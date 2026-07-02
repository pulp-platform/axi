// Copyright (c) 2024 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Authors:
// - Tim Fischer <fischeti@iis.ee.ethz.ch>

// Description: AXI4+ATOP to APB4 bridge
//
// Bridges one AXI4+ATOP slave port onto one or more APB4 slaves, supporting data-width downsizing
// (`AxiDataWidth` -> `ApbDataWidth`) and address truncation (`AxiAddrWidth` -> `ApbAddrWidth`). It
// composes an `axi_to_detailed_mem` front-end with an inline APB master:
//
//   1. `axi_atop_filter`      : reject atomic transactions with a slave error (APB has no atomics).
//   2. `axi_to_detailed_mem`  : split AXI bursts into single-word memory requests and downsize the
//                               data width via banking: `NumBanks = AxiDataWidth / ApbDataWidth`,
//                               so each bank is exactly `ApbDataWidth` wide.
//   3. inline APB master FSM  : serialize the active `NumBanks` bank requests onto the single APB
//                               bus, selecting the next active lane with an `lzc` (so inactive /
//                               dropped lanes cost no cycles), decode on the full `AxiAddrWidth`
//                               address and truncate `paddr` to `ApbAddrWidth`, running the standard
//                               SETUP/ACCESS handshake.
//
// Behaviour notes:
//   - Only `INCR` bursts are supported (`axi_to_detailed_mem` restriction).
//   - A wide access is serialized into one APB transfer per active bank, selected via `lzc`.
//     Zero-strobe write lanes are dropped by `axi_to_detailed_mem` (`HideStrb`) and never reach the
//     bus. For reads, *all* banks are read (even lanes outside a narrow beat's byte range), so avoid
//     mapping read-sensitive registers into unaddressed lanes.
//   - Address-decode misses are reported as `RESP_SLVERR` (not `RESP_DECERR`; `axi_to_detailed_mem`
//     has no decode-error path) and exclusive accesses complete as `RESP_OKAY` (no `EXOKAY`).

`include "axi/typedef.svh"
`include "axi/assign.svh"
`include "common_cells/registers.svh"

module axi_to_apb #(
  /// Number of connected APB slaves.
  parameter int unsigned NoApbSlaves     = 32'd1,
  /// Number of APB address-decode rules.
  parameter int unsigned NoRules         = 32'd1,
  /// AXI4 address width. Decoding uses the full width; `paddr` is truncated to `ApbAddrWidth`.
  parameter int unsigned AxiAddrWidth    = 32'd0,
  /// AXI4 data width. Must be an integer power-of-two multiple of `ApbDataWidth`.
  parameter int unsigned AxiDataWidth    = 32'd0,
  /// AXI4 ID width.
  parameter int unsigned AxiIdWidth      = 32'd0,
  /// AXI4 user width.
  parameter int unsigned AxiUserWidth    = 32'd0,
  /// Maximum number of outstanding writes tracked by the `axi_atop_filter`.
  parameter int unsigned AxiMaxWriteTxns = 32'd1,
  /// Response buffer depth of the internal `axi_to_detailed_mem`.
  parameter int unsigned BufDepth        = 32'd1,
  /// Output FIFO depth of the internal `axi_to_detailed_mem`.
  parameter int unsigned OutFifoDepth    = 32'd1,
  /// APB4 address width. Must be `<= AxiAddrWidth`; the upper AXI address bits are discarded.
  parameter int unsigned ApbAddrWidth    = 32'd0,
  /// APB4 data width. Must be a multiple of 8 and `<= 32` (`ApbDataWidth == 8` is supported).
  parameter int unsigned ApbDataWidth    = 32'd0,
  /// AXI4+ATOP request struct, see `axi/typedef.svh`.
  parameter type         axi_req_t       = logic,
  /// AXI4+ATOP response struct, see `axi/typedef.svh`.
  parameter type         axi_resp_t      = logic,
  /// APB4 request struct.
  parameter type         apb_req_t       = logic,
  /// APB4 response struct.
  parameter type         apb_resp_t      = logic,
  /// Address-decode rule struct from `common_cells` (`addr_decode`).
  parameter type         rule_t          = logic
) (
  input  logic                        clk_i,       // Clock
  input  logic                        rst_ni,      // Asynchronous reset active low
  input  logic                        test_i,      // Testmode enable (unused)
  // AXI4+ATOP slave port
  input  axi_req_t                    axi_req_i,
  output axi_resp_t                   axi_resp_o,
  // APB master port
  output apb_req_t  [NoApbSlaves-1:0] apb_req_o,
  input  apb_resp_t [NoApbSlaves-1:0] apb_resp_i,
  // APB slave address map
  input  rule_t     [NoRules-1:0]     addr_map_i
);

  localparam int unsigned NumBanks     = AxiDataWidth / ApbDataWidth;
  localparam int unsigned SelIdxWidth  = (NoApbSlaves > 32'd1) ? $clog2(NoApbSlaves) : 32'd1;
  localparam int unsigned BankIdxWidth = (NumBanks     > 32'd1) ? $clog2(NumBanks)    : 32'd1;

  typedef logic [AxiAddrWidth-1:0]   axi_addr_t;
  typedef logic [ApbAddrWidth-1:0]   apb_addr_t;
  typedef logic [ApbDataWidth-1:0]   apb_data_t;
  typedef logic [ApbDataWidth/8-1:0] apb_strb_t;
  typedef logic [SelIdxWidth-1:0]    sel_idx_t;

  typedef enum logic {
    Setup  = 1'b0, // APB idle / setup phase
    Access = 1'b1  // APB access phase
  } apb_state_e;

  // 1. Reject atomics with a slave error (APB has no atomic support).
  axi_req_t  filtered_req;
  axi_resp_t filtered_resp;

  axi_atop_filter #(
    .AxiIdWidth      ( AxiIdWidth      ),
    .AxiMaxWriteTxns ( AxiMaxWriteTxns ),
    .axi_req_t       ( axi_req_t       ),
    .axi_resp_t      ( axi_resp_t      )
  ) i_axi_atop_filter (
    .clk_i,
    .rst_ni,
    .slv_req_i  ( axi_req_i     ),
    .slv_resp_o ( axi_resp_o    ),
    .mst_req_o  ( filtered_req  ),
    .mst_resp_i ( filtered_resp )
  );

  // 2. AXI bursts -> single-word memory stream, with data-width downsize via banking.
  logic           [NumBanks-1:0] mem_req, mem_gnt;
  axi_addr_t      [NumBanks-1:0] mem_addr;
  apb_data_t      [NumBanks-1:0] mem_wdata;
  apb_strb_t      [NumBanks-1:0] mem_strb;
  logic           [NumBanks-1:0] mem_we;
  axi_pkg::prot_t [NumBanks-1:0] mem_prot;
  logic           [NumBanks-1:0] mem_rvalid;
  apb_data_t      [NumBanks-1:0] mem_rdata;
  logic           [NumBanks-1:0] mem_err;
  logic           [NumBanks-1:0] mem_exokay;

  axi_to_detailed_mem #(
    .axi_req_t    ( axi_req_t    ),
    .axi_resp_t   ( axi_resp_t   ),
    .AddrWidth    ( AxiAddrWidth ),
    .DataWidth    ( AxiDataWidth ),
    .IdWidth      ( AxiIdWidth   ),
    .UserWidth    ( AxiUserWidth ),
    .NumBanks     ( NumBanks     ),
    .BufDepth     ( BufDepth     ),
    .HideStrb     ( 1'b1         ), // drop zero-strobe write lanes so they issue no APB access
    .OutFifoDepth ( OutFifoDepth )
  ) i_axi_to_detailed_mem (
    .clk_i,
    .rst_ni,
    .busy_o       ( /* unused */  ),
    .axi_req_i    ( filtered_req  ),
    .axi_resp_o   ( filtered_resp ),
    .mem_req_o    ( mem_req       ),
    .mem_gnt_i    ( mem_gnt       ),
    .mem_addr_o   ( mem_addr      ),
    .mem_wdata_o  ( mem_wdata     ),
    .mem_strb_o   ( mem_strb      ),
    .mem_atop_o   ( /* unused */  ),
    .mem_lock_o   ( /* unused */  ),
    .mem_we_o     ( mem_we        ),
    .mem_id_o     ( /* unused */  ),
    .mem_user_o   ( /* unused */  ),
    .mem_cache_o  ( /* unused */  ),
    .mem_prot_o   ( mem_prot      ),
    .mem_qos_o    ( /* unused */  ),
    .mem_region_o ( /* unused */  ),
    .mem_rvalid_i ( mem_rvalid    ),
    .mem_rdata_i  ( mem_rdata     ),
    .mem_err_i    ( mem_err       ),
    .mem_exokay_i ( mem_exokay    )
  );

  // 3. Inline APB master: serialize the active bank requests onto the single APB bus.
  apb_state_e              apb_state_q, apb_state_d;
  logic [BankIdxWidth-1:0] bank_sel;
  logic                    no_req;

  // Select the lowest-index lane that still has a pending request. Lanes with no request -
  // including zero-strobe write lanes dropped by `axi_to_detailed_mem` (`HideStrb`) - are skipped
  // for free (no wasted cycles). The selected lane's request stays asserted until we grant it, so
  // `bank_sel` is stable across the SETUP and ACCESS phases of a transfer.
  lzc #(
    .WIDTH ( NumBanks ),
    .MODE  ( 1'b0     ) // count trailing zeros -> lowest set bit
  ) i_bank_sel (
    .in_i    ( mem_req  ),
    .cnt_o   ( bank_sel ),
    .empty_o ( no_req   )
  );

  // Address decode on the selected lane's (full-width) address.
  logic     apb_dec_valid;
  sel_idx_t apb_sel_idx;
  addr_decode #(
    .NoIndices ( NoApbSlaves ),
    .NoRules   ( NoRules     ),
    .addr_t    ( axi_addr_t  ),
    .rule_t    ( rule_t      )
  ) i_apb_decode (
    .addr_i           ( mem_addr[bank_sel] ),
    .addr_map_i       ( addr_map_i         ),
    .idx_o            ( apb_sel_idx        ),
    .dec_valid_o      ( apb_dec_valid      ),
    .dec_error_o      ( /* unused */       ),
    .en_default_idx_i ( 1'b0               ),
    .default_idx_i    ( '0                 )
  );

  always_comb begin
    // Default assignments.
    apb_state_d = apb_state_q;
    apb_req_o   = '0;
    mem_gnt     = '0;
    mem_rvalid  = '0;
    mem_rdata   = '0;
    mem_err     = '0;
    mem_exokay  = '0;

    unique case (apb_state_q)
      Setup: begin
        if (!no_req) begin
          if (apb_dec_valid) begin
            // SETUP phase: assert psel, keep penable low.
            apb_req_o[apb_sel_idx] = '{
              paddr:   apb_addr_t'(mem_addr[bank_sel]),
              pprot:   mem_prot[bank_sel],
              psel:    1'b1,
              penable: 1'b0,
              pwrite:  mem_we[bank_sel],
              pwdata:  mem_wdata[bank_sel],
              pstrb:   mem_strb[bank_sel]
            };
            apb_state_d = Access;
          end else begin
            // Decode miss: no APB request, answer this lane with a slave error and move on.
            mem_gnt[bank_sel]    = 1'b1;
            mem_rvalid[bank_sel] = 1'b1;
            mem_err[bank_sel]    = 1'b1;
          end
        end
      end
      Access: begin
        // ACCESS phase: assert psel and penable until the slave is ready.
        apb_req_o[apb_sel_idx] = '{
          paddr:   apb_addr_t'(mem_addr[bank_sel]),
          pprot:   mem_prot[bank_sel],
          psel:    1'b1,
          penable: 1'b1,
          pwrite:  mem_we[bank_sel],
          pwdata:  mem_wdata[bank_sel],
          pstrb:   mem_strb[bank_sel]
        };
        if (apb_resp_i[apb_sel_idx].pready) begin
          mem_gnt[bank_sel]    = 1'b1;
          mem_rvalid[bank_sel] = 1'b1;
          mem_rdata[bank_sel]  = apb_resp_i[apb_sel_idx].prdata;
          mem_err[bank_sel]    = apb_resp_i[apb_sel_idx].pslverr;
          mem_exokay[bank_sel] = 1'b0; // APB has no exclusive access
          apb_state_d          = Setup;
        end
      end
      default: /* do nothing */ ;
    endcase
  end

  `FFARN(apb_state_q, apb_state_d, Setup, clk_i, rst_ni)

  // parameter check
  // pragma translate_off
  `ifndef VERILATOR
  initial begin : check_params
    apb_data_le: assert (ApbDataWidth <= AxiDataWidth) else
      $fatal(1, $sformatf("ApbDataWidth has to be <= AxiDataWidth"));
    apb_addr_le: assert (ApbAddrWidth <= AxiAddrWidth) else
      $fatal(1, $sformatf("ApbAddrWidth has to be <= AxiAddrWidth"));
    apb_data_div: assert (AxiDataWidth % ApbDataWidth == 0) else
      $fatal(1, $sformatf("AxiDataWidth has to be an integer multiple of ApbDataWidth"));
  end
  `endif
  // pragma translate_on
endmodule

module axi_to_apb_intf #(
  /// Number of connected APB slaves.
  parameter int unsigned NoApbSlaves     = 32'd1,
  /// Number of APB address-decode rules.
  parameter int unsigned NoRules         = 32'd1,
  /// AXI4 address width. Decoding uses the full width; `paddr` is truncated to `ApbAddrWidth`.
  parameter int unsigned AxiAddrWidth    = 32'd0,
  /// AXI4 data width. Must be an integer power-of-two multiple of `ApbDataWidth`.
  parameter int unsigned AxiDataWidth    = 32'd0,
  /// AXI4 ID width.
  parameter int unsigned AxiIdWidth      = 32'd0,
  /// AXI4 user width.
  parameter int unsigned AxiUserWidth    = 32'd0,
  /// Maximum number of outstanding writes tracked by the `axi_atop_filter`.
  parameter int unsigned AxiMaxWriteTxns = 32'd1,
  /// Response buffer depth of the internal `axi_to_detailed_mem`.
  parameter int unsigned BufDepth        = 32'd1,
  /// Output FIFO depth of the internal `axi_to_detailed_mem`.
  parameter int unsigned OutFifoDepth    = 32'd1,
  /// APB4 address width. Must be `<= AxiAddrWidth`; the upper AXI address bits are discarded.
  parameter int unsigned ApbAddrWidth    = 32'd0,
  /// APB4 data width. Must be a multiple of 8 and `<= 32` (`ApbDataWidth == 8` is supported).
  parameter int unsigned ApbDataWidth    = 32'd0,
  /// Address-decode rule struct from `common_cells` (`addr_decode`).
  parameter type         rule_t          = logic,
  // DEPENDENT PARAMETERS, DO NOT OVERWRITE!
  parameter type         apb_addr_t      = logic [ApbAddrWidth-1:0],
  parameter type         apb_data_t      = logic [ApbDataWidth-1:0],
  parameter type         apb_strb_t      = logic [ApbDataWidth/8-1:0],
  parameter type         sel_t           = logic [NoApbSlaves-1:0]
) (
  input  logic                    clk_i,       // Clock
  input  logic                    rst_ni,      // Asynchronous reset active low
  input  logic                    test_i,      // Testmode enable
  // AXI4+ATOP slave port
  AXI_BUS.Slave                   slv,
  // APB master port
  output apb_addr_t               paddr_o,
  output logic  [2:0]             pprot_o,
  output sel_t                    pselx_o,
  output logic                    penable_o,
  output logic                    pwrite_o,
  output apb_data_t               pwdata_o,
  output apb_strb_t               pstrb_o,
  input  logic  [NoApbSlaves-1:0] pready_i,
  input  apb_data_t [NoApbSlaves-1:0] prdata_i,
  input         [NoApbSlaves-1:0] pslverr_i,
  // APB slave address map
  input  rule_t [NoRules-1:0]     addr_map_i
);
  localparam int unsigned SelIdxWidth = NoApbSlaves > 1 ? $clog2(NoApbSlaves) : 1;

  typedef logic [AxiAddrWidth-1:0]   axi_addr_t;
  typedef logic [AxiDataWidth-1:0]   axi_data_t;
  typedef logic [AxiIdWidth-1:0]     axi_id_t;
  typedef logic [AxiDataWidth/8-1:0] axi_strb_t;
  typedef logic [AxiUserWidth-1:0]   axi_user_t;

  typedef struct packed {
    apb_addr_t      paddr;
    axi_pkg::prot_t pprot;
    logic           psel;
    logic           penable;
    logic           pwrite;
    apb_data_t      pwdata;
    apb_strb_t      pstrb;
  } apb_req_t;

  typedef struct packed {
    logic      pready;
    apb_data_t prdata;
    logic      pslverr;
  } apb_resp_t;

  `AXI_TYPEDEF_AW_CHAN_T(aw_chan_t, axi_addr_t, axi_id_t, axi_user_t)
  `AXI_TYPEDEF_W_CHAN_T(w_chan_t, axi_data_t, axi_strb_t, axi_user_t)
  `AXI_TYPEDEF_B_CHAN_T(b_chan_t, axi_id_t, axi_user_t)
  `AXI_TYPEDEF_AR_CHAN_T(ar_chan_t, axi_addr_t, axi_id_t, axi_user_t)
  `AXI_TYPEDEF_R_CHAN_T(r_chan_t, axi_data_t, axi_id_t, axi_user_t)
  `AXI_TYPEDEF_REQ_T(axi_req_t, aw_chan_t, w_chan_t, ar_chan_t)
  `AXI_TYPEDEF_RESP_T(axi_resp_t, b_chan_t, r_chan_t)

  axi_req_t                     axi_req;
  axi_resp_t                    axi_resp;
  apb_req_t   [NoApbSlaves-1:0] apb_req;
  apb_resp_t  [NoApbSlaves-1:0] apb_resp;
  logic       [SelIdxWidth-1:0] apb_sel;

  `AXI_ASSIGN_TO_REQ(axi_req, slv)
  `AXI_ASSIGN_FROM_RESP(slv, axi_resp)

  onehot_to_bin #(
    .ONEHOT_WIDTH ( NoApbSlaves )
  ) i_onehot_to_bin (
    .onehot ( pselx_o ),
    .bin    ( apb_sel )
  );

  assign paddr_o   = apb_req[apb_sel].paddr;
  assign pprot_o   = apb_req[apb_sel].pprot;
  assign penable_o = apb_req[apb_sel].penable;
  assign pwrite_o  = apb_req[apb_sel].pwrite;
  assign pwdata_o  = apb_req[apb_sel].pwdata;
  assign pstrb_o   = apb_req[apb_sel].pstrb;
  for (genvar i = 0; i < NoApbSlaves; i++) begin : gen_apb_resp_assign
    assign pselx_o[i]          = apb_req[i].psel;
    assign apb_resp[i].pready  = pready_i[i];
    assign apb_resp[i].prdata  = prdata_i[i];
    assign apb_resp[i].pslverr = pslverr_i[i];
  end

  axi_to_apb #(
    .NoApbSlaves     ( NoApbSlaves     ),
    .NoRules         ( NoRules         ),
    .AxiAddrWidth    ( AxiAddrWidth    ),
    .AxiDataWidth    ( AxiDataWidth    ),
    .AxiIdWidth      ( AxiIdWidth      ),
    .AxiUserWidth    ( AxiUserWidth    ),
    .AxiMaxWriteTxns ( AxiMaxWriteTxns ),
    .BufDepth        ( BufDepth        ),
    .OutFifoDepth    ( OutFifoDepth    ),
    .ApbAddrWidth    ( ApbAddrWidth    ),
    .ApbDataWidth    ( ApbDataWidth    ),
    .axi_req_t       ( axi_req_t       ),
    .axi_resp_t      ( axi_resp_t      ),
    .apb_req_t       ( apb_req_t       ),
    .apb_resp_t      ( apb_resp_t      ),
    .rule_t          ( rule_t          )
  ) i_axi_to_apb (
    .clk_i,
    .rst_ni,
    .test_i,
    .axi_req_i  ( axi_req  ),
    .axi_resp_o ( axi_resp ),
    .apb_req_o  ( apb_req  ),
    .apb_resp_i ( apb_resp ),
    .addr_map_i
  );
endmodule
