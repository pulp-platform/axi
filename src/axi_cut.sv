// Copyright (c) 2014-2018 ETH Zurich, University of Bologna
//
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
// - Wolfgang Roenninger <wroennin@iis.ee.ethz.ch>
// - Fabian Schuiki <fschuiki@iis.ee.ethz.ch>
// - Andreas Kurth <akurth@iis.ee.ethz.ch>

/// An AXI4 cut.
///
/// Breaks all combinatorial paths between its input and output.
module axi_cut #(
  // bypass enable
  parameter bit  Bypass    = 1'b0,
  // AXI channel structs
  parameter type aw_chan_t = logic,
  parameter type  w_chan_t = logic,
  parameter type  b_chan_t = logic,
  parameter type ar_chan_t = logic,
  parameter type  r_chan_t = logic,
  // AXI request & response structs
  parameter type axi_req_t = logic,
  parameter type axi_rsp_t = logic
) (
  input logic      clk_i,
  input logic      rst_ni,
  // subordinate port
  input  axi_req_t sbr_port_req_i,
  output axi_rsp_t sbr_port_rsp_o,
  // manager port
  output axi_req_t mgr_port_req_o,
  input  axi_rsp_t mgr_port_rsp_i
);

  // a spill register for each channel
  spill_register #(
    .T       ( aw_chan_t ),
    .Bypass  ( Bypass    )
  ) i_reg_aw (
    .clk_i   ( clk_i              ),
    .rst_ni  ( rst_ni             ),
    .valid_i ( sbr_port_req_i.aw_valid ),
    .ready_o ( sbr_port_rsp_o.aw_ready ),
    .data_i  ( sbr_port_req_i.aw       ),
    .valid_o ( mgr_port_req_o.aw_valid ),
    .ready_i ( mgr_port_rsp_i.aw_ready ),
    .data_o  ( mgr_port_req_o.aw       )
  );

  spill_register #(
    .T       ( w_chan_t ),
    .Bypass  ( Bypass   )
  ) i_reg_w  (
    .clk_i   ( clk_i             ),
    .rst_ni  ( rst_ni            ),
    .valid_i ( sbr_port_req_i.w_valid ),
    .ready_o ( sbr_port_rsp_o.w_ready ),
    .data_i  ( sbr_port_req_i.w       ),
    .valid_o ( mgr_port_req_o.w_valid ),
    .ready_i ( mgr_port_rsp_i.w_ready ),
    .data_o  ( mgr_port_req_o.w       )
  );

  spill_register #(
    .T       ( b_chan_t ),
    .Bypass  ( Bypass   )
  ) i_reg_b  (
    .clk_i   ( clk_i             ),
    .rst_ni  ( rst_ni            ),
    .valid_i ( mgr_port_rsp_i.b_valid ),
    .ready_o ( mgr_port_req_o.b_ready ),
    .data_i  ( mgr_port_rsp_i.b       ),
    .valid_o ( sbr_port_rsp_o.b_valid ),
    .ready_i ( sbr_port_req_i.b_ready ),
    .data_o  ( sbr_port_rsp_o.b       )
  );

  spill_register #(
    .T       ( ar_chan_t ),
    .Bypass  ( Bypass    )
  ) i_reg_ar (
    .clk_i   ( clk_i              ),
    .rst_ni  ( rst_ni             ),
    .valid_i ( sbr_port_req_i.ar_valid ),
    .ready_o ( sbr_port_rsp_o.ar_ready ),
    .data_i  ( sbr_port_req_i.ar       ),
    .valid_o ( mgr_port_req_o.ar_valid ),
    .ready_i ( mgr_port_rsp_i.ar_ready ),
    .data_o  ( mgr_port_req_o.ar       )
  );

  spill_register #(
    .T       ( r_chan_t ),
    .Bypass  ( Bypass   )
  ) i_reg_r  (
    .clk_i   ( clk_i             ),
    .rst_ni  ( rst_ni            ),
    .valid_i ( mgr_port_rsp_i.r_valid ),
    .ready_o ( mgr_port_req_o.r_ready ),
    .data_i  ( mgr_port_rsp_i.r       ),
    .valid_o ( sbr_port_rsp_o.r_valid ),
    .ready_i ( sbr_port_req_i.r_ready ),
    .data_o  ( sbr_port_rsp_o.r       )
  );
endmodule

`include "axi/assign.svh"
`include "axi/typedef.svh"

// interface wrapper
module axi_cut_intf #(
  // Bypass eneable
  parameter bit          BYPASS     = 1'b0,
  // The address width.
  parameter int unsigned ADDR_WIDTH = 0,
  // The data width.
  parameter int unsigned DATA_WIDTH = 0,
  // The ID width.
  parameter int unsigned ID_WIDTH   = 0,
  // The user data width.
  parameter int unsigned USER_WIDTH = 0
) (
  input logic     clk_i  ,
  input logic     rst_ni ,
  AXI_BUS.Subordinate   in     ,
  AXI_BUS.Manager  out
);

  typedef logic [ID_WIDTH-1:0]     id_t;
  typedef logic [ADDR_WIDTH-1:0]   addr_t;
  typedef logic [DATA_WIDTH-1:0]   data_t;
  typedef logic [DATA_WIDTH/8-1:0] strb_t;
  typedef logic [USER_WIDTH-1:0]   user_t;

  `AXI_TYPEDEF_AW_CHAN_T(aw_chan_t, addr_t, id_t, user_t)
  `AXI_TYPEDEF_W_CHAN_T(w_chan_t, data_t, strb_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T(b_chan_t, id_t, user_t)
  `AXI_TYPEDEF_AR_CHAN_T(ar_chan_t, addr_t, id_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(r_chan_t, data_t, id_t, user_t)
  `AXI_TYPEDEF_REQ_T(axi_req_t, aw_chan_t, w_chan_t, ar_chan_t)
  `AXI_TYPEDEF_RSP_T(axi_rsp_t, b_chan_t, r_chan_t)

  axi_req_t sbr_req, mgr_req;
  axi_rsp_t sbr_rsp, mgr_rsp;

  `AXI_ASSIGN_TO_REQ(sbr_req, in)
  `AXI_ASSIGN_FROM_RSP(in, sbr_rsp)

  `AXI_ASSIGN_FROM_REQ(out, mgr_req)
  `AXI_ASSIGN_TO_RSP(mgr_rsp, out)

  axi_cut #(
    .Bypass     (    BYPASS ),
    .aw_chan_t  ( aw_chan_t ),
    .w_chan_t   (  w_chan_t ),
    .b_chan_t   (  b_chan_t ),
    .ar_chan_t  ( ar_chan_t ),
    .r_chan_t   (  r_chan_t ),
    .axi_req_t  ( axi_req_t ),
    .axi_rsp_t  ( axi_rsp_t )
  ) i_axi_cut (
    .clk_i,
    .rst_ni,
    .sbr_port_req_i ( sbr_req ),
    .sbr_port_rsp_o ( sbr_rsp ),
    .mgr_port_req_o ( mgr_req ),
    .mgr_port_rsp_i ( mgr_rsp )
  );

  // Check the invariants.
  // pragma translate_off
  `ifndef VERILATOR
  initial begin
    assert (ADDR_WIDTH > 0) else $fatal(1, "Wrong addr width parameter");
    assert (DATA_WIDTH > 0) else $fatal(1, "Wrong data width parameter");
    assert (ID_WIDTH   > 0) else $fatal(1, "Wrong id   width parameter");
    assert (USER_WIDTH > 0) else $fatal(1, "Wrong user width parameter");
    assert (in.AXI_ADDR_WIDTH  == ADDR_WIDTH) else $fatal(1, "Wrong interface definition");
    assert (in.AXI_DATA_WIDTH  == DATA_WIDTH) else $fatal(1, "Wrong interface definition");
    assert (in.AXI_ID_WIDTH    == ID_WIDTH)   else $fatal(1, "Wrong interface definition");
    assert (in.AXI_USER_WIDTH  == USER_WIDTH) else $fatal(1, "Wrong interface definition");
    assert (out.AXI_ADDR_WIDTH == ADDR_WIDTH) else $fatal(1, "Wrong interface definition");
    assert (out.AXI_DATA_WIDTH == DATA_WIDTH) else $fatal(1, "Wrong interface definition");
    assert (out.AXI_ID_WIDTH   == ID_WIDTH)   else $fatal(1, "Wrong interface definition");
    assert (out.AXI_USER_WIDTH == USER_WIDTH) else $fatal(1, "Wrong interface definition");
  end
  `endif
  // pragma translate_on
endmodule

module axi_lite_cut_intf #(
  // bypass enable
  parameter bit          BYPASS     = 1'b0,
  /// The address width.
  parameter int unsigned ADDR_WIDTH = 0,
  /// The data width.
  parameter int unsigned DATA_WIDTH = 0
) (
  input logic     clk_i  ,
  input logic     rst_ni ,
  AXI_LITE.Subordinate  in     ,
  AXI_LITE.Manager out
);

  typedef logic [ADDR_WIDTH-1:0]   addr_t;
  typedef logic [DATA_WIDTH-1:0]   data_t;
  typedef logic [DATA_WIDTH/8-1:0] strb_t;

  `AXI_LITE_TYPEDEF_AW_CHAN_T(aw_chan_t, addr_t)
  `AXI_LITE_TYPEDEF_W_CHAN_T(w_chan_t, data_t, strb_t)
  `AXI_LITE_TYPEDEF_B_CHAN_T(b_chan_t)
  `AXI_LITE_TYPEDEF_AR_CHAN_T(ar_chan_t, addr_t)
  `AXI_LITE_TYPEDEF_R_CHAN_T(r_chan_t, data_t)
  `AXI_LITE_TYPEDEF_REQ_T(axi_lite_req_t, aw_chan_t, w_chan_t, ar_chan_t)
  `AXI_LITE_TYPEDEF_RSP_T(axi_lite_rsp_t, b_chan_t, r_chan_t)

  axi_lite_req_t  sbr_req, mgr_req;
  axi_lite_rsp_t  sbr_rsp, mgr_rsp;

  `AXI_LITE_ASSIGN_TO_REQ(sbr_req, in)
  `AXI_LITE_ASSIGN_FROM_RSP(in, sbr_rsp)

  `AXI_LITE_ASSIGN_FROM_REQ(out, mgr_req)
  `AXI_LITE_ASSIGN_TO_RSP(mgr_rsp, out)

  axi_cut #(
    .Bypass     (         BYPASS ),
    .aw_chan_t  (      aw_chan_t ),
    .w_chan_t   (       w_chan_t ),
    .b_chan_t   (       b_chan_t ),
    .ar_chan_t  (      ar_chan_t ),
    .r_chan_t   (       r_chan_t ),
    .axi_req_t  ( axi_lite_req_t ),
    .axi_rsp_t  ( axi_lite_rsp_t )
  ) i_axi_cut (
    .clk_i,
    .rst_ni,
    .sbr_port_req_i ( sbr_req ),
    .sbr_port_rsp_o ( sbr_rsp ),
    .mgr_port_req_o ( mgr_req ),
    .mgr_port_rsp_i ( mgr_rsp )
  );

  // Check the invariants.
  // pragma translate_off
  `ifndef VERILATOR
  initial begin
    assert (ADDR_WIDTH > 0) else $fatal(1, "Wrong addr width parameter");
    assert (DATA_WIDTH > 0) else $fatal(1, "Wrong data width parameter");
    assert (in.AXI_ADDR_WIDTH == ADDR_WIDTH)  else $fatal(1, "Wrong interface definition");
    assert (in.AXI_DATA_WIDTH == DATA_WIDTH)  else $fatal(1, "Wrong interface definition");
    assert (out.AXI_ADDR_WIDTH == ADDR_WIDTH) else $fatal(1, "Wrong interface definition");
    assert (out.AXI_DATA_WIDTH == DATA_WIDTH) else $fatal(1, "Wrong interface definition");
  end
  `endif
  // pragma translate_on
endmodule
