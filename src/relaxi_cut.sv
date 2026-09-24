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
module relaxi_cut #(
  // bypass enable
  parameter bit  Bypass     = 1'b0,
  parameter bit  BypassAw   = Bypass,
  parameter bit  BypassW    = Bypass,
  parameter bit  BypassB    = Bypass,
  parameter bit  BypassAr   = Bypass,
  parameter bit  BypassR    = Bypass,
  // AXI channel structs
  parameter type  aw_chan_t = logic,
  parameter type   w_chan_t = logic,
  parameter type   b_chan_t = logic,
  parameter type  ar_chan_t = logic,
  parameter type   r_chan_t = logic,
  // AXI request & response structs
  parameter type  axi_req_t = logic,
  parameter type axi_resp_t = logic
) (
  input logic       clk_i,
  input logic       rst_ni,
  // salve port
  input  axi_req_t  slv_req_i,
  output axi_resp_t slv_resp_o,
  // master port
  output axi_req_t  mst_req_o,
  input  axi_resp_t mst_resp_i,
  output logic [1:0] fault_o
);

  // Handshake intermediates: Questa (vsim-3015) treats struct-field references
  // in port connections as 1-bit scalars even when the field is logic [2:0].
  logic [2:0] aw_valid_slv, aw_ready_slv, aw_valid_mst, aw_ready_mst;
  logic [2:0]  w_valid_slv,  w_ready_slv,  w_valid_mst,  w_ready_mst;
  logic [2:0]  b_valid_mst,  b_ready_mst,  b_valid_slv,  b_ready_slv;
  logic [2:0] ar_valid_slv, ar_ready_slv, ar_valid_mst, ar_ready_mst;
  logic [2:0]  r_valid_mst,  r_ready_mst,  r_valid_slv,  r_ready_slv;
  logic [4:0] cut_faults;   // AW, W, B, AR, R spill faults (all corrected-class)

  assign aw_valid_slv        = slv_req_i.aw_valid;
  assign aw_ready_mst        = mst_resp_i.aw_ready;
  assign slv_resp_o.aw_ready = aw_ready_slv;
  assign mst_req_o.aw_valid  = aw_valid_mst;

  assign w_valid_slv        = slv_req_i.w_valid;
  assign w_ready_mst        = mst_resp_i.w_ready;
  assign slv_resp_o.w_ready = w_ready_slv;
  assign mst_req_o.w_valid  = w_valid_mst;

  assign b_valid_mst        = mst_resp_i.b_valid;
  assign b_ready_slv        = slv_req_i.b_ready;
  assign mst_req_o.b_ready  = b_ready_mst;
  assign slv_resp_o.b_valid = b_valid_slv;

  assign ar_valid_slv        = slv_req_i.ar_valid;
  assign ar_ready_mst        = mst_resp_i.ar_ready;
  assign slv_resp_o.ar_ready = ar_ready_slv;
  assign mst_req_o.ar_valid  = ar_valid_mst;

  assign r_valid_mst        = mst_resp_i.r_valid;
  assign r_ready_slv        = slv_req_i.r_ready;
  assign mst_req_o.r_ready  = r_ready_mst;
  assign slv_resp_o.r_valid = r_valid_slv;

  // a spill register for each channel
  rel_spill_register #(
    .T            ( aw_chan_t ),
    .Bypass       ( BypassAw  ),
    .TmrHandshake ( 1'b1      ),
    .DataCorrector( 1'b0      )
  ) i_reg_aw (
    .clk_i,
    .rst_ni,
    .valid_i          ( aw_valid_slv ),
    .ready_o          ( aw_ready_slv ),
    .data_i           ( slv_req_i.aw ),
    .valid_o          ( aw_valid_mst ),
    .ready_i          ( aw_ready_mst ),
    .data_o           ( mst_req_o.aw ),
    .fault_o          ( cut_faults[0]),
    .data_corrector_o (              ),
    .data_corrected_i ( '0           )
  );

  rel_spill_register #(
    .T            ( w_chan_t ),
    .Bypass       ( BypassW  ),
    .TmrHandshake ( 1'b1     ),
    .DataCorrector( 1'b0     )
  ) i_reg_w (
    .clk_i,
    .rst_ni,
    .valid_i          ( w_valid_slv   ),
    .ready_o          ( w_ready_slv   ),
    .data_i           ( slv_req_i.w   ),
    .valid_o          ( w_valid_mst   ),
    .ready_i          ( w_ready_mst   ),
    .data_o           ( mst_req_o.w   ),
    .fault_o          ( cut_faults[1] ),
    .data_corrector_o (               ),
    .data_corrected_i ( '0            )
  );

  rel_spill_register #(
    .T            ( b_chan_t ),
    .Bypass       ( BypassB  ),
    .TmrHandshake ( 1'b1     ),
    .DataCorrector( 1'b0     )
  ) i_reg_b (
    .clk_i,
    .rst_ni,
    .valid_i          ( b_valid_mst  ),
    .ready_o          ( b_ready_mst  ),
    .data_i           ( mst_resp_i.b ),
    .valid_o          ( b_valid_slv  ),
    .ready_i          ( b_ready_slv  ),
    .data_o           ( slv_resp_o.b ),
    .fault_o          ( cut_faults[2]),
    .data_corrector_o (              ),
    .data_corrected_i ( '0           )
  );

  rel_spill_register #(
    .T            ( ar_chan_t ),
    .Bypass       ( BypassAr  ),
    .TmrHandshake ( 1'b1      ),
    .DataCorrector( 1'b0      )
  ) i_reg_ar (
    .clk_i,
    .rst_ni,
    .valid_i          ( ar_valid_slv ),
    .ready_o          ( ar_ready_slv ),
    .data_i           ( slv_req_i.ar ),
    .valid_o          ( ar_valid_mst ),
    .ready_i          ( ar_ready_mst ),
    .data_o           ( mst_req_o.ar ),
    .fault_o          ( cut_faults[3]),
    .data_corrector_o (              ),
    .data_corrected_i ( '0           )
  );

  rel_spill_register #(
    .T            ( r_chan_t ),
    .Bypass       ( BypassR  ),
    .TmrHandshake ( 1'b1     ),
    .DataCorrector( 1'b0     )
  ) i_reg_r (
    .clk_i,
    .rst_ni,
    .valid_i          ( r_valid_mst  ),
    .ready_o          ( r_ready_mst  ),
    .data_i           ( mst_resp_i.r ),
    .valid_o          ( r_valid_slv  ),
    .ready_i          ( r_ready_slv  ),
    .data_o           ( slv_resp_o.r ),
    .fault_o          ( cut_faults[4]),
    .data_corrector_o (              ),
    .data_corrected_i ( '0           )
  );

  // Spill-register faults are all TMR/corrected-class -> corrected bit only
  assign fault_o[0] = |cut_faults;
  assign fault_o[1] = 1'b0;

endmodule

`include "axi/assign.svh"
`include "axi/typedef.svh"

// interface wrapper
module axi_cut_intf #(
  // Bypass eneable
  parameter bit          BYPASS     = 1'b0,
  parameter bit          BYPASS_AW  = BYPASS,
  parameter bit          BYPASS_W   = BYPASS,
  parameter bit          BYPASS_B   = BYPASS,
  parameter bit          BYPASS_AR  = BYPASS,
  parameter bit          BYPASS_R   = BYPASS,
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
  AXI_BUS.Slave   in     ,
  AXI_BUS.Master  out
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
  `AXI_TYPEDEF_RESP_T(axi_resp_t, b_chan_t, r_chan_t)

  axi_req_t  slv_req,  mst_req;
  axi_resp_t slv_resp, mst_resp;

  `AXI_ASSIGN_TO_REQ(slv_req, in)
  `AXI_ASSIGN_FROM_RESP(in, slv_resp)

  `AXI_ASSIGN_FROM_REQ(out, mst_req)
  `AXI_ASSIGN_TO_RESP(mst_resp, out)

  relaxi_cut #(
    .Bypass     (     BYPASS ),
    .BypassAw   (  BYPASS_AW ),
    .BypassW    (   BYPASS_W ),
    .BypassB    (   BYPASS_B ),
    .BypassAr   (  BYPASS_AR ),
    .BypassR    (   BYPASS_R ),
    .aw_chan_t  (  aw_chan_t ),
    .w_chan_t   (   w_chan_t ),
    .b_chan_t   (   b_chan_t ),
    .ar_chan_t  (  ar_chan_t ),
    .r_chan_t   (   r_chan_t ),
    .axi_req_t  (  axi_req_t ),
    .axi_resp_t ( axi_resp_t )
  ) i_axi_cut (
    .clk_i,
    .rst_ni,
    .slv_req_i  ( slv_req  ),
    .slv_resp_o ( slv_resp ),
    .mst_req_o  ( mst_req  ),
    .mst_resp_i ( mst_resp )
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
  parameter bit          BYPASS_AW  = BYPASS,
  parameter bit          BYPASS_W   = BYPASS,
  parameter bit          BYPASS_B   = BYPASS,
  parameter bit          BYPASS_AR  = BYPASS,
  parameter bit          BYPASS_R   = BYPASS,
  /// The address width.
  parameter int unsigned ADDR_WIDTH = 0,
  /// The data width.
  parameter int unsigned DATA_WIDTH = 0
) (
  input logic     clk_i  ,
  input logic     rst_ni ,
  AXI_LITE.Slave  in     ,
  AXI_LITE.Master out
);

  typedef logic [ADDR_WIDTH-1:0]   addr_t;
  typedef logic [DATA_WIDTH-1:0]   data_t;
  typedef logic [DATA_WIDTH/8-1:0] strb_t;

  `AXI_LITE_TYPEDEF_AW_CHAN_T(aw_chan_t, addr_t)
  `AXI_LITE_TYPEDEF_W_CHAN_T(w_chan_t, data_t, strb_t)
  `AXI_LITE_TYPEDEF_B_CHAN_T(b_chan_t)
  `AXI_LITE_TYPEDEF_AR_CHAN_T(ar_chan_t, addr_t)
  `AXI_LITE_TYPEDEF_R_CHAN_T(r_chan_t, data_t)
  `AXI_LITE_TYPEDEF_REQ_T(axi_req_t, aw_chan_t, w_chan_t, ar_chan_t)
  `AXI_LITE_TYPEDEF_RESP_T(axi_resp_t, b_chan_t, r_chan_t)

  axi_req_t   slv_req,  mst_req;
  axi_resp_t  slv_resp, mst_resp;

  `AXI_LITE_ASSIGN_TO_REQ(slv_req, in)
  `AXI_LITE_ASSIGN_FROM_RESP(in, slv_resp)

  `AXI_LITE_ASSIGN_FROM_REQ(out, mst_req)
  `AXI_LITE_ASSIGN_TO_RESP(mst_resp, out)

  relaxi_cut #(
    .Bypass     (     BYPASS ),
    .BypassAw   (  BYPASS_AW ),
    .BypassW    (   BYPASS_W ),
    .BypassB    (   BYPASS_B ),
    .BypassAr   (  BYPASS_AR ),
    .BypassR    (   BYPASS_R ),
    .aw_chan_t  (  aw_chan_t ),
    .w_chan_t   (   w_chan_t ),
    .b_chan_t   (   b_chan_t ),
    .ar_chan_t  (  ar_chan_t ),
    .r_chan_t   (   r_chan_t ),
    .axi_req_t  (  axi_req_t ),
    .axi_resp_t ( axi_resp_t )
  ) i_axi_cut (
    .clk_i,
    .rst_ni,
    .slv_req_i  ( slv_req  ),
    .slv_resp_o ( slv_resp ),
    .mst_req_o  ( mst_req  ),
    .mst_resp_i ( mst_resp )
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
