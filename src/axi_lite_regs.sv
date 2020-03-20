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

// APB Read-Write Registers
// Description: This module exposes a number of registers on an AXI4-Lite interface.
//              It responds to not mapped accesses with a slave error.
//              Some of the registers can be configured to be read only.
// Parameters:
// - `NumAxiRegs`:      Number of registers.
// - `AxiAddrWidth`:    Address width of `axi_req_i.aw.addr` and `axi_req_i.ar.addr`, is used to
//                      generate internal address map.
// - `AxiDataWidth`:    The data width of the AXI4-Lite bus. Register address map is generated with
//                      this value.
// - `RegDataWidth`:    The data width of the registers, this value has to be less or equal to
//                      `AxiDataWidth`. If it is less, the register gets zero extended for reads and
//                      higher bits on writes get ignored.
// - `PrivProtOnly`:    Privileged accesses only. The slave only executes AXI4-Lite transactions if
//                      the `AxProt[0]` bit in the `AW` or `AR` vector is set, otherwise
//                      ignores writes and answers with `axi_pkg::RESP_SLVERR` to transactions.
// - `SecuProtOnly`:    Secure accesses only. The slave only executes AXI4-Lite transactions if
//                      the `AxProt[1]` bit in the `AW` or `AR` vector is set, otherwise
//                      ignores writes and answers with `axi_pkg::RESP_SLVERR` to transactions.
// - `ReadOnly`:        This flag can specify a read only register at the given register index of
//                      the array. When in the array the corresponding bit is set, the `reg_init_i`
//                      signal at given index can be read out. Writes are ignored on flag set.
// - `axi_lite_req_t`:  APB4 request struct. See macro definition in `include/typedef.svh`
// - `axi_lite_resp_t`: APB4 response struct. See macro definition in `include/typedef.svh`
//
// Ports:
//
// - `clk_i`:        Clock input signal (1-bit).
// - `rst_ni`:       Asynchronous active low reset signal (1-bit).
// - `axi_req_i`:    AXI4-Lite request struct, bundles all AXI4-Lite signals from the master.
// - `axi_resp_o`:   AXI4-Lite response struct, bundles all AXI4-Lite signals to the master.
// - `base_addr_i`:  Base address of this module, from here the registers `0` are mapped, starting
//                   with index `0`. All subsequent register with higher indices have their bases
//                   mapped with TODO reg_index * `AddrOffset` from this value (ApbAddrWidth-bit).
// - `reg_init_i:    Initialization value for each register, when the register index is configured
//                   as `ReadOnly[reg_index] == 1'b1` this value is passed through directly to
//                   the APB4 bus (Array size `NumAxiRegs` * RegDataWidth-bit).
// - `reg_q_o:       The current value of the register. If the register at the array index is
//                   read only, the `reg_init_i` value is passed through to the respective index
//                   (Array size `NumAxiRegs` * RegDataWidth-bit).
//
// This file also features the module `axi_lite_regs_intf`. The difference is that instead of the
// request and response structs it uses an `AXI_LITE.Salve` interface. The parameters have the same
// function, however are defined in `ALL_CAPS`.

`include "axi/typedef.svh"
`include "common_cells/registers.svh"

module axi_lite_regs #(
  parameter int unsigned           NumAxiRegs   = 32'd0,
  parameter int unsigned           AxiAddrWidth = 32'd0,
  parameter int unsigned           AxiDataWidth = 32'd0,
  parameter bit                    PrivProtOnly = 1'b0,
  parameter bit                    SecuProtOnly = 1'b0,
  parameter int unsigned           RegDataWidth = 32'd0,
  parameter logic [NumAxiRegs-1:0] ReadOnly     = {NumAxiRegs{1'b0}},
  parameter type                   req_lite_t   = logic,
  parameter type                   resp_lite_t  = logic,
  // DEPENDENT PARAMETERS, DO NOT OVERRIDE!
  parameter type axi_addr_t = logic[AxiAddrWidth-1:0],
  parameter type reg_data_t = logic[RegDataWidth-1:0]
) (
  input  logic                       clk_i,       // Clock
  input  logic                       rst_ni,      // Asynchronous reset active low
  // AXI4-Lite slave port
  input  req_lite_t                  axi_req_i,   // AXI4-Lite request struct
  output resp_lite_t                 axi_resp_o,  // AXI4-Lite response struct
  input  axi_addr_t                  base_addr_i, // Base address of the registers
  // Register interface
  input  reg_data_t [NumAxiRegs-1:0] reg_init_i,  // Register initialization
  output reg_data_t [NumAxiRegs-1:0] reg_q_o      // Register state
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

  // output spill register
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

module axi_lite_regs_intf #(
  parameter int unsigned NUM_AXI_REGS      = 32'd0,
  parameter int unsigned AXI_ADDR_WIDTH    = 32'd0,
  parameter int unsigned AXI_DATA_WIDTH    = 32'd0,
  parameter bit          PRIV_PROT_ONLY    = 1'd0,
  parameter bit          SECU_PROT_ONLY    = 1'd0,
  parameter int unsigned REG_DATA_WIDTH    = 32'd0,
  parameter int unsigned READ_ONLY         = {NUM_AXI_REGS{1'b0}},
  // DEPENDENT PARAMETERS, DO NOT OVERRIDE!
  parameter type axi_addr_t = logic[AXI_ADDR_WIDTH-1:0],
  parameter type reg_data_t = logic[REG_DATA_WIDTH-1:0]
) (
  input  logic                         clk_i,       // Clock
  input  logic                         rst_ni,      // Asynchronous reset active low
  AXI_LITE.Slave                       slv,         // AXI4-Lite slave interface
  input  axi_addr_t                    base_addr_i, // Base address of the registers
  // Register interface
  input  reg_data_t [NUM_AXI_REGS-1:0] reg_init_i,  // Register initialization
  output reg_data_t [NUM_AXI_REGS-1:0] reg_q_o      // Register state
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