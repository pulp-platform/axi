// Copyright (c) 2020 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Author: Wolfgang Roenninger <wroennin@ethz.ch>

`include "axi/typedef.svh"
`include "common_cells/registers.svh"
/// AXI4-Lite Registers with option to make individual registers read-only.
/// This module exposes a number of registers on an AXI4-Lite bus modeled with structs.
/// It responds to accesses outside the instantiated registers with a slave error.
/// Some of the registers can be configured to be read-only.
module axi_lite_regs #(
  /// Number of registers which are mapped to the AXI channel. Each register has a size of
  /// `RegDataWidth` bit and is is aligned to the AXI4-Lite bus data width (AxiDataWidth).
  /// Ech register has an index `reg_index` associated with it, range `0` to `NumAxiRegs-1`
  parameter int unsigned           NumAxiRegs   = 32'd0,
  /// Address width of `axi_req_i.aw.addr` and `axi_req_i.ar.addr`, is used to generate internal
  /// address map.
  parameter int unsigned           AxiAddrWidth = 32'd0,
  /// Data width of the AXI4-Lite bus. Register address map is generated with this value.
  parameter int unsigned           AxiDataWidth = 32'd0,
  /// Privileged accesses only. The slave only executes AXI4-Lite transactions if the `AxProt[0]`
  /// bit in the `AW` or `AR` vector is set, otherwise ignores writes and answers with
  /// `axi_pkg::RESP_SLVERR` to transactions.
  parameter bit                    PrivProtOnly = 1'b0,
  /// Secure accesses only. The slave only executes AXI4-Lite transactions if the `AxProt[1]` bit
  /// in the `AW` or `AR` vector is set, otherwise ignores writes and answers with
  /// `axi_pkg::RESP_SLVERR` to transactions.
  parameter bit                    SecuProtOnly = 1'b0,
  /// The data width of the registers, this value has to be less or equal to `AxiDataWidth`.
  /// If it is less, the register gets zero extended for reads and higher bits on writes are
  /// ignored.
  parameter int unsigned           RegDataWidth = 32'd0,
  /// This flag can specify a AXI read-only register at the given register index of the array.
  /// This flag only applies for AXI4-Lite write transactions. Transactions targeting an `reg_index`
  /// where `ReadOnly[reg_index] == 1'b1` will always respond with `axi_pkg::RESP_SLVERR` and
  /// not perform the write.
  parameter logic [NumAxiRegs-1:0] AxiReadOnly = {NumAxiRegs{1'b0}},
  /// Reset value for the whole register array.
  /// 2D-array with `NumAxiRegs` entries which each have size of `RegDataWidth`-bit.
  parameter logic [NumAxiRegs-1:0][RegDataWidth-1:0] RegRstVal = {NumAxiRegs{{RegDataWidth{1'b0}}}},
  /// AXI4-Lite request struct. See macro definition in `include/typedef.svh`
  parameter type                        req_lite_t   = logic,
  /// AXI4-Lite response struct. See macro definition in `include/typedef.svh`
  parameter type                        resp_lite_t  = logic,
  /// DEPENDENT PARAMETER, DO NOT OVERRIDE! Address type of the AXI4-Lite channel.
  parameter type axi_addr_t = logic[AxiAddrWidth-1:0],
  /// DEPENDENT PARAMETER, DO NOT OVERRIDE! Data type of an individual register.
  parameter type reg_data_t = logic[RegDataWidth-1:0],
  /// DEPENDENT PARAMETER, DO NOT OVERRIDE! Width of `reg_index`.
  parameter int unsigned IdxWidth = (NumAxiRegs > 32'd1) ? $clog2(NumAxiRegs) : 32'd1,
  /// DEPENDENT PARAMETER, DO NOT OVERRIDE! Type of `reg_index`.
  parameter type reg_idx_t  = logic [IdxWidth-1:0]
) (
  /// Clock input signal (1-bit).
  input  logic                       clk_i,
  /// Asynchronous active low reset signal (1-bit).
  input  logic                       rst_ni,
  /// AXI4-Lite slave port request struct, bundles all AXI4-Lite signals from the master.
  /// This module will perform the write transaction when `axi_req_i.aw_valid` and
  /// `axi_req_i.w_valid` are both asserted.
  input  req_lite_t                  axi_req_i,
  /// AXI4-Lite slave port response struct, bundles all AXI4-Lite signals to the master.
  output resp_lite_t                 axi_resp_o,
  /// Base address of this module, from here the registers `0` are mapped, starting with index `0`.
  /// The base address of each individual register can be calculated with:
  /// `reg_address` = `axi_base_addr_i` + `reg_index` * `AxiDataWidth/8`
  input  axi_addr_t                  axi_base_addr_i,
  /// The `reg_index` of the register array that is currently updated by a write transaction from
  /// the AXI4-Lite channel.
  output reg_idx_t                   axi_wr_idx_o,
  /// Indicates that the AXI4-Lite channel performs a write onto the register at `axi_wr_idx_o`
  /// (Active high).
  /// The new value is available in the next cycle at `reg_q_o[axi_wr_idx_o]`.
  /// This signal will be only active if the AXI4-Lite write transaction has the B response
  /// `axi_pkg::RESP_OAKY`.
  output logic                       axi_wr_active_o,
  /// The `reg_index` of the register array that is currently accessed by a read transaction from
  /// the AXI4-Lite channel.
  output reg_idx_t                   axi_rd_idx_o,
  /// Indicates that the AXI4-Lite channel performs a read onto the register at `axi_rd_idx_o`.
  /// (Active high)
  /// The read out value is `reg_q_o[axi_rd_idx_o]`, zero extended/truncated to `AxiDataWidth`.
  /// This signal will only be active if the AXI4-Lite read transaction has the R response
  /// `axi_pkg::RESP_OKAY`.
  output logic                       axi_rd_active_o,
  /// Load value for each register. When the signal `reg_load_i[reg_index] == 1'b1`, the value
  /// `reg_d_i[reg_index]` is latched and available in the next cycle at `reg_q_i[reg_iindex]`.
  /// The parameter `ReadOnly` has no influence on the load capability of a register array entry.
  /// (Array size: `NumAxiRegs` * RegDataWidth-bit)
  input  reg_data_t [NumAxiRegs-1:0] reg_d_i,
  /// Load enable for each register.
  /// The bit index of this signal is the index of the corresponding register array entry.
  /// When asserted (`reg_load_i[reg_index] == 1'b1`) the value of `reg_d_i[reg_index]` is latched
  /// and available on `reg_q_o[reg_index]` in the next cycle.
  /// When an AXI4-Lite write transaction is active onto the same register index
  /// (`aw_valid && aw_ready && w_valid && w_ready`) where a load is active
  /// (`reg_load_i[reg_index] == 1'b1`) in the same cycle, the AXI4-Lite write transaction will
  /// stall until the load signal is `reg_load_i[reg_index]==1'b0` and then perform the write!
  /// This only applies for writable register array entries (`ReadOnly[reg_index] == 1'b0`), as
  /// read-only entries alway reply with `axi_pkg::RESP_SLVERR` for write transactions.
  input  logic      [NumAxiRegs-1:0] reg_load_i,
  /// The current value of the register. For constant propagation, leave the corresponding
  /// `reg_load_i[reg_index] == 1'b0` and `ReadOnly[reg_index] == 1'b1`.
  /// (Array size: `NumAxiRegs` * RegDataWidth-bit)
  output reg_data_t [NumAxiRegs-1:0] reg_q_o
);
  // definition and generation of the address rule
  typedef struct packed {
    int unsigned idx;
    axi_addr_t   start_addr;
    axi_addr_t   end_addr;
  } axi_rule_t;
  axi_rule_t    [NumAxiRegs-1:0] addr_map;
  for (genvar i = 0; i < NumAxiRegs; i++) begin : gen_addr_map
    assign addr_map[i] = axi_rule_t'{
      idx:        i,
      start_addr: axi_base_addr_i +  i   * (AxiDataWidth / 8),
      end_addr:   axi_base_addr_i + (i+1)* (AxiDataWidth / 8)
    };
  end

  // Channel definitions for spill register
  typedef logic [AxiDataWidth-1:0] axi_data_t;
  `AXI_LITE_TYPEDEF_B_CHAN_T(b_chan_lite_t)
  `AXI_LITE_TYPEDEF_R_CHAN_T(r_chan_lite_t, axi_data_t)

  // Register array declarations
  reg_data_t [NumAxiRegs-1:0] reg_q,      reg_d;
  logic      [NumAxiRegs-1:0] reg_update;

  // Write logic
  reg_idx_t     aw_idx;
  logic         aw_dec_valid;
  b_chan_lite_t b_chan;
  logic         b_valid,      b_ready;
  logic         aw_prot_ok;

  assign aw_prot_ok   = (PrivProtOnly ? axi_req_i.aw.prot[0] : 1'b1) &
                        (SecuProtOnly ? axi_req_i.aw.prot[1] : 1'b1);
  assign axi_wr_idx_o = aw_idx;
  always_comb begin
    // default assignments
    reg_d               = reg_q;
    reg_update          = '0;
    // Channel handshake
    axi_resp_o.aw_ready = 1'b0;
    axi_resp_o.w_ready  = 1'b0;
    // Response
    b_chan              = b_chan_lite_t'{resp: axi_pkg::RESP_SLVERR, default: '0};
    b_valid             = 1'b0;
    // write active flag
    axi_wr_active_o     = 1'b0;

    // Control
    // Handle all non AXI register loads.
    for (int unsigned i = 0; i < NumAxiRegs; i++) begin
      if (reg_load_i[i]) begin
        reg_d[i]      = reg_d_i[i];
        reg_update[i] = 1'b1;
      end
    end

    // Handle load from AXI write.
    // `b_ready` is allowed to be a condition as it comes from a spill register.
    if (axi_req_i.aw_valid && axi_req_i.w_valid && b_ready) begin
      // The write can be performed when these conditions are true:
      // - AW decode is valid.
      // - `axi_req_i.aw.prot` has the right value.
      // - AW decode index points to a non read-only register.
      if (aw_dec_valid && aw_prot_ok && !AxiReadOnly[aw_idx]) begin
        b_chan.resp = axi_pkg::RESP_OKAY;
        // Stall the write transaction until there is no load active onto register at `aw_idx`.
        if (!reg_load_i[aw_idx]) begin
          for (int unsigned i = 0; i < RegDataWidth; i++) begin
            if (axi_req_i.w.strb[i/8]) begin
              reg_d[aw_idx][i] = axi_req_i.w.data[i];
            end
          end
          reg_update[aw_idx]  = 1'b1;
          axi_wr_active_o     = 1'b1;
          b_valid             = 1'b1;
          axi_resp_o.aw_ready = 1'b1;
          axi_resp_o.w_ready  = 1'b1;
        end
      end else begin
        // Send default B error response on each not allowed write transaction.
        b_valid             = 1'b1;
        axi_resp_o.aw_ready = 1'b1;
        axi_resp_o.w_ready  = 1'b1;
      end
    end
  end

  // Read logic
  reg_idx_t     ar_idx;
  logic         ar_dec_valid;
  r_chan_lite_t r_chan;
  logic         r_valid,      r_ready;
  logic         ar_prot_ok;
  assign ar_prot_ok = (PrivProtOnly ? axi_req_i.ar.prot[0] : 1'b1) &
                      (SecuProtOnly ? axi_req_i.ar.prot[1] : 1'b1);
  assign r_chan = r_chan_lite_t'{
    data: (ar_dec_valid && ar_prot_ok) ? axi_data_t'(reg_q_o[ar_idx]) : axi_data_t'(32'hBA5E1E55),
    resp: (ar_dec_valid && ar_prot_ok) ? axi_pkg::RESP_OKAY           : axi_pkg::RESP_SLVERR,
    default : '0
  };
  assign r_valid             = axi_req_i.ar_valid; // to spill register
  assign axi_resp_o.ar_ready = r_ready;            // from spill register
  // Read active flags
  assign axi_rd_idx_o        = ar_idx;
  assign axi_rd_active_o     = (r_chan.resp == axi_pkg::RESP_OKAY) & r_valid & r_ready;

  // Register array output, even read only register can be loaded
  for (genvar i = 0; i < NumAxiRegs; i++) begin : gen_rw_regs
    `FFLARN(reg_q[i], reg_d[i], reg_update[i], RegRstVal[i], clk_i, rst_ni)
    assign reg_q_o[i] = reg_q[i];
  end

  addr_decode #(
    .NoIndices ( NumAxiRegs ),
    .NoRules   ( NumAxiRegs ),
    .addr_t    ( axi_addr_t ),
    .rule_t    ( axi_rule_t )
  ) i_aw_decode (
    .addr_i           ( axi_req_i.aw.addr ),
    .addr_map_i       ( addr_map          ),
    .idx_o            ( aw_idx            ),
    .dec_valid_o      ( aw_dec_valid      ),
    .dec_error_o      ( /*not used*/      ),
    .en_default_idx_i ( '0                ),
    .default_idx_i    ( '0                )
  );

  addr_decode #(
    .NoIndices ( NumAxiRegs ),
    .NoRules   ( NumAxiRegs ),
    .addr_t    ( axi_addr_t ),
    .rule_t    ( axi_rule_t )
  ) i_ar_decode (
    .addr_i           ( axi_req_i.ar.addr ),
    .addr_map_i       ( addr_map          ),
    .idx_o            ( ar_idx            ),
    .dec_valid_o      ( ar_dec_valid      ),
    .dec_error_o      ( /*not used*/      ),
    .en_default_idx_i ( '0                ),
    .default_idx_i    ( '0                )
  );

  // Add a cycle delay on AXI response, cut all comb paths between slave port inputs and outputs.
  spill_register #(
    .T      ( b_chan_lite_t ),
    .Bypass ( 1'b0          )
  ) i_b_spill_register (
    .clk_i,
    .rst_ni,
    .valid_i ( b_valid ),
    .ready_o ( b_ready ),
    .data_i  ( b_chan  ),
    .valid_o ( axi_resp_o.b_valid ),
    .ready_i ( axi_req_i.b_ready  ),
    .data_o  ( axi_resp_o.b       )
  );

  // Add a cycle delay on AXI response, cut all comb paths between slave port inputs and outputs.
  spill_register #(
    .T      ( r_chan_lite_t ),
    .Bypass ( 1'b0          )
  ) i_r_spill_register (
    .clk_i,
    .rst_ni,
    .valid_i ( r_valid ),
    .ready_o ( r_ready ),
    .data_i  ( r_chan  ),
    .valid_o ( axi_resp_o.r_valid ),
    .ready_i ( axi_req_i.r_ready  ),
    .data_o  ( axi_resp_o.r       )
  );

  // Validate parameters.
  // pragma translate_off
  `ifndef VERILATOR
    initial begin: p_assertions
      assert (NumAxiRegs > 32'd0)
          else $fatal(1, "The number of registers must be at least 1!");
      assert (AxiAddrWidth > 32'd2)
          else $fatal(1, "ApbAddrWidth is not wide enough, has to be at least 3 bit wide!");
      assert ($bits(axi_req_i.aw.addr) == AxiAddrWidth)
          else $fatal(1, "AddrWidth does not match req_i.aw.addr!");
      assert ($bits(axi_req_i.ar.addr) == AxiAddrWidth)
          else $fatal(1, "AddrWidth does not match req_i.ar.addr!");
      assert (AxiDataWidth == $bits(axi_req_i.w.data))
          else $fatal(1, "AxiDataWidth has to be: AxiDataWidth == $bits(axi_req_i.w.data)!");
      assert (AxiDataWidth == $bits(axi_resp_o.r.data))
          else $fatal(1, "AxiDataWidth has to be: AxiDataWidth == $bits(axi_resp_o.r.data)!");
      assert (RegDataWidth > 32'd0)
          else $fatal(1, "RegDataWidth has to be: RegDataWidth > 0!");
      assert (RegDataWidth <= AxiDataWidth)
          else $fatal(1, "RegDataWidth has to be: RegDataWidth <= AxiDataWidth!");
      assert (NumAxiRegs == $bits(ReadOnly))
          else $fatal(1, "Each register needs a `ReadOnly` flag!");
    end
    default disable iff (~rst_ni);
    for (genvar i = 0; i < NumAxiRegs; i++) begin
      assert property (@(posedge clk_i) (reg_d_i[i] === reg_q_o[i])) else
          $fatal(1, "Read-only register at index: %0h")
    end
  `endif
  // pragma translate_on
endmodule

`include "axi/assign.svh"
/// AXI4-Lite Registers with option to make individual registers read-only.
/// This module is an interface wrapper for `axi_lite_regs`. The parameters have the same
/// function as the ones in `axi_lite_regs`, however are defined in `ALL_CAPS`.
module axi_lite_regs_intf #(
  /// See `axi_lite_reg`: `NumAxiRegs`.
  parameter int unsigned                                 NUM_AXI_REGS   = 32'd0,
  /// See `axi_lite_reg`: `AxiAddrWidth`.
  parameter int unsigned                                 AXI_ADDR_WIDTH = 32'd0,
  /// See `axi_lite_reg`: `AxiDataWidth`.
  parameter int unsigned                                 AXI_DATA_WIDTH = 32'd0,
  /// See `axi_lite_reg`: `PrivProtOnly`.
  parameter bit                                          PRIV_PROT_ONLY = 1'd0,
  /// See `axi_lite_reg`: `SecuProtOnly`.
  parameter bit                                          SECU_PROT_ONLY = 1'd0,
  /// See `axi_lite_reg`: `RegDataWidth`.
  parameter int unsigned                                 REG_DATA_WIDTH = 32'd0,
  /// See `axi_lite_reg`: `AxiReadOnly`.
  parameter logic [NUM_AXI_REGS-1:0]                     AXI_READ_ONLY  = {NUM_AXI_REGS{1'b0}},
  /// See `axi_lite_reg`: `RegRstVal`
  parameter logic [NUM_AXI_REGS-1:0][REG_DATA_WIDTH-1:0] REG_RST_VAL    =
      {NUM_AXI_REGS{{REG_DATA_WIDTH{1'b0}}}},
  /// DEPENDENT PARAMETER, DO NOT OVERRIDE! See `axi_lite_reg`: `axi_addr_t`.
  parameter type axi_addr_t        = logic[AXI_ADDR_WIDTH-1:0],
  /// DEPENDENT PARAMETER, DO NOT OVERRIDE! See `axi_lite_reg`: `reg_data_t`.
  parameter type reg_data_t        = logic[REG_DATA_WIDTH-1:0],
  /// DEPENDENT PARAMETER, DO NOT OVERRIDE! See `axi_lite_reg`: `IdxWidth`.
  parameter int unsigned IDX_WIDTH = (NUM_AXI_REGS > 32'd1) ? $clog2(NUM_AXI_REGS) : 32'd1,
  /// DEPENDENT PARAMETER, DO NOT OVERRIDE! See `axi_lite_reg`: `reg_idx_t`.
  parameter type reg_idx_t         = logic [IDX_WIDTH-1:0]
) (
  /// Clock input signal (1-bit).
  input  logic                         clk_i,
  /// Asynchronous active low reset signal (1-bit).
  input  logic                         rst_ni,
  /// AXI4-Lite slave port interface.
  AXI_LITE.Slave                       slv,
  /// See `axi_lite_reg`: `axi_base_addr_i`.
  input  axi_addr_t                    axi_base_addr_i,
  /// See `axi_lite_reg`: `axi_wr_idx_o`.
  input  reg_idx_t                     axi_wr_idx_o,
  /// See `axi_lite_reg`: `axi_wr_active_o`.
  input  logic                         axi_wr_active_o,
  /// See `axi_lite_reg`: `axi_rd_idx_o`.
  input  reg_idx_t                     axi_rd_idx_o,
  /// See `axi_lite_reg`: `axi_rd_active_o`.
  input  logic                         axi_rd_active_o,
  /// See `axi_lite_reg`: `reg_d_i`.
  input  reg_data_t [NUM_AXI_REGS-1:0] reg_d_i,
  /// See `axi_lite_reg`: `reg_load_i`.
  input  logic      [NUM_AXI_REGS-1:0] reg_load_i,
  /// See `axi_lite_reg`: `reg_q_o`.
  output reg_data_t [NUM_AXI_REGS-1:0] reg_q_o
);
  typedef logic [AXI_ADDR_WIDTH-1:0]   addr_t;
  typedef logic [AXI_DATA_WIDTH-1:0]   data_t;
  typedef logic [AXI_DATA_WIDTH/8-1:0] strb_t;
  `AXI_LITE_TYPEDEF_AW_CHAN_T(aw_chan_lite_t, addr_t)
  `AXI_LITE_TYPEDEF_W_CHAN_T(w_chan_lite_t, data_t, strb_t)
  `AXI_LITE_TYPEDEF_B_CHAN_T(b_chan_lite_t)
  `AXI_LITE_TYPEDEF_AR_CHAN_T(ar_chan_lite_t, addr_t)
  `AXI_LITE_TYPEDEF_R_CHAN_T(r_chan_lite_t, data_t)
  `AXI_LITE_TYPEDEF_REQ_T(req_lite_t, aw_chan_lite_t, w_chan_lite_t, ar_chan_lite_t)
  `AXI_LITE_TYPEDEF_RESP_T(resp_lite_t, b_chan_lite_t, r_chan_lite_t)

  req_lite_t  axi_lite_req;
  resp_lite_t axi_lite_resp;

  `AXI_LITE_ASSIGN_TO_REQ(axi_lite_req, slv)
  `AXI_LITE_ASSIGN_FROM_RESP(slv, axi_lite_resp)

  axi_lite_regs #(
    .NumAxiRegs   ( NUM_AXI_REGS   ),
    .AxiAddrWidth ( AXI_ADDR_WIDTH ),
    .AxiDataWidth ( AXI_DATA_WIDTH ),
    .PrivProtOnly ( PRIV_PROT_ONLY ),
    .SecuProtOnly ( SECU_PROT_ONLY ),
    .RegDataWidth ( REG_DATA_WIDTH ),
    .AxiReadOnly  ( AXI_READ_ONLY  ),
    .RegRstVal    ( REG_RST_VAL    ),
    .req_lite_t   ( req_lite_t     ),
    .resp_lite_t  ( resp_lite_t    )
  ) i_axi_lite_regs (
    .clk_i,                         // Clock
    .rst_ni,                        // Asynchronous reset active low
    .axi_req_i   ( axi_lite_req  ), // AXI4-Lite request struct
    .axi_resp_o  ( axi_lite_resp ), // AXI4-Lite response struct
    .axi_base_addr_i,                   // Base address of the registers
    .axi_wr_idx_o,                  // AXI write index
    .axi_wr_active_o,                // AXI write active
    .axi_rd_idx_o,                  // AXI read index
    .axi_rd_active_o,               // AXI read active
    .reg_d_i,                       // Register load values
    .reg_load_i,                    // Register load enable
    .reg_q_o                        // Register state
  );
  // Validate parameters.
  // pragma translate_off
  `ifndef VERILATOR
    initial begin: p_assertions
      assert (AXI_ADDR_WIDTH == $bits(slv.aw_addr))
          else $fatal(1, "AXI_ADDR_WIDTH does not match slv interface!");
      assert (AXI_DATA_WIDTH == $bits(slv.w_data))
          else $fatal(1, "AXI_DATA_WIDTH does not match slv interface!");
    end
  `endif
  // pragma translate_on
endmodule
