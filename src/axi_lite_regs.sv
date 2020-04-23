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
  /// This flag can specify a read-only register at the given register index of the array.
  /// When in the array the corresponding bit is set, the `reg_init_i` signal at given index can be
  /// read out. Writes are ignored on flag set.
  parameter logic [NumAxiRegs-1:0] ReadOnly     = {NumAxiRegs{1'b0}},
  /// AXI4-Lite request struct. See macro definition in `include/typedef.svh`
  parameter type                   req_lite_t   = logic,
  /// AXI4-Lite response struct. See macro definition in `include/typedef.svh`
  parameter type                   resp_lite_t  = logic,
  /// DEPENDENT PARAMETER, DO NOT OVERRIDE! Address type of the AXI4-Lite channel.
  parameter type axi_addr_t = logic[AxiAddrWidth-1:0],
  /// DEPENDENT PARAMETER, DO NOT OVERRIDE! Data type of an individual register.
  parameter type reg_data_t = logic[RegDataWidth-1:0]
) (
  /// Clock input signal (1-bit).
  input  logic                       clk_i,
  /// Asynchronous active low reset signal (1-bit).
  input  logic                       rst_ni,
  /// AXI4-Lite slave port request struct, bundles all AXI4-Lite signals from the master.
  input  req_lite_t                  axi_req_i,
  /// AXI4-Lite slave port response struct, bundles all AXI4-Lite signals to the master.
  output resp_lite_t                 axi_resp_o,
  /// Base address of this module, from here the registers `0` are mapped, starting with index `0`.
  /// The base address of each individual register can be calculated with:
  /// `reg_address` = `base_addr_i` + `reg_index` * `AxiDataWidth/8`
  input  axi_addr_t                  base_addr_i,
  /// Initialization value for each register, when the register index is configured as
  /// `ReadOnly[reg_index] == 1'b1` this value is passed through directly to the AXI4-Lite bus.
  /// (Array size: `NumAxiRegs` * RegDataWidth-bit)
  input  reg_data_t [NumAxiRegs-1:0] reg_init_i,
  /// The current value of the register. If the register at the array index is read only, the
  /// `reg_init_i` value is passed through to the respective index.
  /// (Array size: `NumAxiRegs` * RegDataWidth-bit)
  output reg_data_t [NumAxiRegs-1:0] reg_q_o
);
  // definition and generation of the address rule and register indices
  localparam int unsigned IdxWidth = (NumAxiRegs > 32'd1) ? $clog2(NumAxiRegs) : 32'd1;
  typedef struct packed {
    int unsigned idx;
    axi_addr_t   start_addr;
    axi_addr_t   end_addr;
  } axi_rule_t;
  typedef logic [IdxWidth-1:0]   reg_idx_t;
  axi_rule_t    [NumAxiRegs-1:0] addr_map;
  for (genvar i = 0; i < NumAxiRegs; i++) begin : gen_addr_map
    assign addr_map[i] = '{
      idx:        i,
      start_addr: base_addr_i +  i   * (AxiDataWidth / 8),
      end_addr:   base_addr_i + (i+1)* (AxiDataWidth / 8)
    };
  end

  // Channel definitions for spill register
  typedef logic [AxiDataWidth-1:0] axi_data_t;
  `AXI_LITE_TYPEDEF_B_CHAN_T(b_chan_lite_t)
  `AXI_LITE_TYPEDEF_R_CHAN_T(r_chan_lite_t, axi_data_t)

  // Register declarations
  reg_data_t [NumAxiRegs-1:0] reg_q,      reg_d;
  logic      [NumAxiRegs-1:0] reg_update;

  // Write logic
  reg_idx_t     aw_idx;
  logic         aw_dec_valid;
  b_chan_lite_t b_chan;
  logic         b_valid,      b_ready;
  logic         aw_prot_ok;

  assign aw_prot_ok = (PrivProtOnly ? axi_req_i.aw.prot[0] : 1'b1) &
                      (SecuProtOnly ? axi_req_i.aw.prot[1] : 1'b1);
  always_comb begin
    // default assignments
    reg_d               = reg_q;
    reg_update          = '0;
    // Channel handshake
    axi_resp_o.aw_ready = 1'b0;
    axi_resp_o.w_ready  = 1'b0;
    // Response
    b_chan              = '0;
    b_valid             = 1'b0;
    // Control
    if (axi_req_i.aw_valid && axi_req_i.w_valid) begin
      if (aw_dec_valid && aw_prot_ok && !ReadOnly[aw_idx]) begin
        b_chan.resp = axi_pkg::RESP_OKAY;
        for (int unsigned i = 0; i < RegDataWidth; i++) begin
          if (axi_req_i.w.strb[i/8]) begin
            reg_d[aw_idx][i] = axi_req_i.w.data[i];
          end
        end
        reg_update[aw_idx] = 1'b1;
      end else begin
        b_chan.resp = axi_pkg::RESP_SLVERR;
      end
      // send response if channel is ready, if stalled and write is ok, register gets
      // written multiple times with the same data
      b_valid = 1'b1;
      axi_resp_o.aw_ready = b_ready; // comes from spill register
      axi_resp_o.w_ready  = b_ready; // comes from spill register
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
  assign r_chan = '{
    data: (ar_dec_valid && ar_prot_ok) ?
              ( ReadOnly[ar_idx] ?
                  axi_data_t'(reg_init_i[ar_idx]) :
                  axi_data_t'(reg_q[ar_idx])
              ) :
              axi_data_t'(32'hDEADBEEF),
    resp: (ar_dec_valid && ar_prot_ok) ?
              axi_pkg::RESP_OKAY :
              axi_pkg::RESP_SLVERR,
    default : '0
  };
  assign r_valid             = axi_req_i.ar_valid; // to spill register
  assign axi_resp_o.ar_ready = r_ready;            // from spill register

  for (genvar i = 0; i < NumAxiRegs; i++) begin : gen_rw_regs
    assign reg_q_o[i] = ReadOnly[i] ? reg_init_i[i] : reg_q[i];
  end
  `FFLARN(reg_q, reg_d, reg_update, reg_init_i, clk_i, rst_ni)

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
  `endif
  // pragma translate_on
endmodule

`include "axi/assign.svh"
/// AXI4-Lite Registers with option to make individual registers read-only.
/// This module is an interface wrapper for `axi_lite_regs`. The parameters have the same
/// function as the ones in `axi_lite_regs`, however are defined in `ALL_CAPS`.
module axi_lite_regs_intf #(
  /// See `axi_lite_reg`: `NumAxiRegs`.
  parameter int unsigned NUM_AXI_REGS      = 32'd0,
  /// See `axi_lite_reg`: `AxiAddrWidth`.
  parameter int unsigned AXI_ADDR_WIDTH    = 32'd0,
  /// See `axi_lite_reg`: `AxiDataWidth`.
  parameter int unsigned AXI_DATA_WIDTH    = 32'd0,
  /// See `axi_lite_reg`: `PrivProtOnly`.
  parameter bit          PRIV_PROT_ONLY    = 1'd0,
  /// See `axi_lite_reg`: `SecuProtOnly`.
  parameter bit          SECU_PROT_ONLY    = 1'd0,
  /// See `axi_lite_reg`: `RegDataWidth`.
  parameter int unsigned REG_DATA_WIDTH    = 32'd0,
  /// See `axi_lite_reg`: `ReadOnly`.
  parameter int unsigned READ_ONLY         = {NUM_AXI_REGS{1'b0}},
  /// DEPENDENT PARAMETER, DO NOT OVERRIDE! See `axi_lite_reg`: `axi_addr_t`.
  parameter type axi_addr_t = logic[AXI_ADDR_WIDTH-1:0],
  /// DEPENDENT PARAMETER, DO NOT OVERRIDE! See `axi_lite_reg`: `reg_data_t`.
  parameter type reg_data_t = logic[REG_DATA_WIDTH-1:0]
) (
  /// Clock input signal (1-bit).
  input  logic                         clk_i,
  /// Asynchronous active low reset signal (1-bit).
  input  logic                         rst_ni,
  /// AXI4-Lite slave port interface.
  AXI_LITE.Slave                       slv,
  /// See `axi_lite_reg`: `base_addr_i`.
  input  axi_addr_t                    base_addr_i,
  /// See `axi_lite_reg`: `reg_init_i`.
  input  reg_data_t [NUM_AXI_REGS-1:0] reg_init_i,
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
    .ReadOnly     ( READ_ONLY      ),
    .req_lite_t   ( req_lite_t     ),
    .resp_lite_t  ( resp_lite_t    )
  ) i_axi_lite_regs (
    .clk_i,                         // Clock
    .rst_ni,                        // Asynchronous reset active low
    .axi_req_i   ( axi_lite_req  ), // AXI4-Lite request struct
    .axi_resp_o  ( axi_lite_resp ), // AXI4-Lite response struct
    .base_addr_i,                   // Base address of the registers
    .reg_init_i,                    // Register
    .reg_q_o
  );
  // Validate parameters.
  // pragma translate_off
  `ifndef VERILATOR
    initial begin: p_assertions
      assert (AXI_ADDR_WIDTH == $bits(slv.aw_addr))
          else $fatal(1, "APB_ADDR_WIDTH does not match slv interface!");
      assert (AXI_DATA_WIDTH == $bits(slv.w_data))
          else $fatal(1, "APB_DATA_WIDTH does not match slv interface!");
    end
  `endif
  // pragma translate_on
endmodule
