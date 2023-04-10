// Copyright (c) 2014-2019 ETH Zurich, University of Bologna
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
// - Andreas Kurth <akurth@iis.ee.ethz.ch>
// - Fabian Schuiki <fschuiki@iis.ee.ethz.ch>
// - Stefan Mach <smach@iis.ee.ethz.ch>

// Multiple AXI4 cuts.
//
// These can be used to relax timing pressure on very long AXI busses.
module axi_multicut #(
  parameter int unsigned NumCuts = 32'd1, // Number of cuts.
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
  input  logic     clk_i,   // Clock
  input  logic     rst_ni,  // Asynchronous reset active low
  // subordinate port
  input  axi_req_t sbr_req_i,
  output axi_rsp_t sbr_rsp_o,
  // manager port
  output axi_req_t mgr_req_o,
  input  axi_rsp_t mgr_rsp_i
);

  if (NumCuts == '0) begin : gen_no_cut
    // degenerate case, connect input to output
    assign mgr_req_o = sbr_req_i;
    assign sbr_rsp_o = mgr_rsp_i;
  end else begin : gen_axi_cut
    // instantiate all needed cuts
    axi_req_t [NumCuts:0] cut_req;
    axi_rsp_t [NumCuts:0] cut_rsp;

    // connect subordinate to the lowest index
    assign cut_req[0] = sbr_req_i;
    assign sbr_rsp_o  = cut_rsp[0];

    // AXI cuts
    for (genvar i = 0; i < NumCuts; i++) begin : gen_axi_cuts
      axi_cut #(
        .Bypass    (      1'b0 ),
        .aw_chan_t ( aw_chan_t ),
        .w_chan_t  (  w_chan_t ),
        .b_chan_t  (  b_chan_t ),
        .ar_chan_t ( ar_chan_t ),
        .r_chan_t  (  r_chan_t ),
        .axi_req_t ( axi_req_t ),
        .axi_rsp_t ( axi_rsp_t )
      ) i_cut (
        .clk_i,
        .rst_ni,
        .sbr_req_i ( cut_req[i]   ),
        .sbr_rsp_o ( cut_rsp[i]   ),
        .mgr_req_o ( cut_req[i+1] ),
        .mgr_rsp_i ( cut_rsp[i+1] )
      );
    end

    // connect manager to the highest index
    assign mgr_req_o        = cut_req[NumCuts];
    assign cut_rsp[NumCuts] = mgr_rsp_i;
  end

  // Check the invariants
  // pragma translate_off
  `ifndef VERILATOR
  initial begin
    assert(NumCuts >= 0);
  end
  `endif
  // pragma translate_on
endmodule

`include "axi/assign.svh"
`include "axi/typedef.svh"

// interface wrapper
module axi_multicut_intf #(
  parameter int unsigned ADDR_WIDTH = 0, // The address width.
  parameter int unsigned DATA_WIDTH = 0, // The data width.
  parameter int unsigned ID_WIDTH   = 0, // The ID width.
  parameter int unsigned USER_WIDTH = 0, // The user data width.
  parameter int unsigned NUM_CUTS   = 0  // The number of cuts.
) (
  input logic    clk_i,
  input logic    rst_ni,
  AXI_BUS.Subordinate  in,
  AXI_BUS.Manager out
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

  axi_req_t sbr_req,  mgr_req;
  axi_rsp_t sbr_rsp, mgr_rsp;

  `AXI_ASSIGN_TO_REQ(sbr_req, in)
  `AXI_ASSIGN_FROM_RSP(in, sbr_rsp)

  `AXI_ASSIGN_FROM_REQ(out, mgr_req)
  `AXI_ASSIGN_TO_RSP(mgr_rsp, out)

  axi_multicut #(
    .NumCuts   (  NUM_CUTS ),
    .aw_chan_t ( aw_chan_t ),
    .w_chan_t  (  w_chan_t ),
    .b_chan_t  (  b_chan_t ),
    .ar_chan_t ( ar_chan_t ),
    .r_chan_t  (  r_chan_t ),
    .axi_req_t ( axi_req_t ),
    .axi_rsp_t ( axi_rsp_t )
  ) i_axi_multicut (
    .clk_i,
    .rst_ni,
    .sbr_req_i ( sbr_req ),
    .sbr_rsp_o ( sbr_rsp ),
    .mgr_req_o ( mgr_req ),
    .mgr_rsp_i ( mgr_rsp )
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

module axi_lite_multicut_intf #(
  // The address width.
  parameter int unsigned ADDR_WIDTH = 0,
  // The data width.
  parameter int unsigned DATA_WIDTH = 0,
  // The number of cuts.
  parameter int unsigned NUM_CUTS   = 0
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
  `AXI_LITE_TYPEDEF_REQ_T(axi_req_t, aw_chan_t, w_chan_t, ar_chan_t)
  `AXI_LITE_TYPEDEF_RSP_T(axi_rsp_t, b_chan_t, r_chan_t)

  axi_req_t sbr_req,  mgr_req;
  axi_rsp_t sbr_rsp, mgr_rsp;

  `AXI_LITE_ASSIGN_TO_REQ(sbr_req, in)
  `AXI_LITE_ASSIGN_FROM_RSP(in, sbr_rsp)

  `AXI_LITE_ASSIGN_FROM_REQ(out, mgr_req)
  `AXI_LITE_ASSIGN_TO_RSP(mgr_rsp, out)

  axi_multicut #(
    .NumCuts   (  NUM_CUTS ),
    .aw_chan_t ( aw_chan_t ),
    .w_chan_t  (  w_chan_t ),
    .b_chan_t  (  b_chan_t ),
    .ar_chan_t ( ar_chan_t ),
    .r_chan_t  (  r_chan_t ),
    .axi_req_t ( axi_req_t ),
    .axi_rsp_t ( axi_rsp_t )
  ) i_axi_multicut (
    .clk_i,
    .rst_ni,
    .sbr_req_i ( sbr_req ),
    .sbr_rsp_o ( sbr_rsp ),
    .mgr_req_o ( mgr_req ),
    .mgr_rsp_i ( mgr_rsp )
  );

  // Check the invariants.
  // pragma translate_off
  `ifndef VERILATOR
  initial begin
    assert (ADDR_WIDTH > 0) else $fatal(1, "Wrong addr width parameter");
    assert (DATA_WIDTH > 0) else $fatal(1, "Wrong data width parameter");
    assert (in.AXI_ADDR_WIDTH == ADDR_WIDTH) else $fatal(1, "Wrong interface definition");
    assert (in.AXI_DATA_WIDTH == DATA_WIDTH) else $fatal(1, "Wrong interface definition");
    assert (out.AXI_ADDR_WIDTH == ADDR_WIDTH) else $fatal(1, "Wrong interface definition");
    assert (out.AXI_DATA_WIDTH == DATA_WIDTH) else $fatal(1, "Wrong interface definition");
  end
  `endif
  // pragma translate_on
endmodule
