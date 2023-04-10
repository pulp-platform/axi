// Copyright (c) 2014-2022 ETH Zurich, University of Bologna
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
// - Noah Huetter <huettern@ethz.ch>
// - Florian Zaruba <zarubaf@iis.ee.ethz.ch>
// - Fabian Schuiki <fschuiki@iis.ee.ethz.ch>

// AXI4 Fifo
//
// Can be used to buffer transactions

module axi_fifo #(
    parameter int unsigned Depth       = 32'd1,  // Number of FiFo slots.
    parameter bit          FallThrough = 1'b0,  // fifos are in fall-through mode
    // AXI channel structs
    parameter type         aw_chan_t   = logic,
    parameter type         w_chan_t    = logic,
    parameter type         b_chan_t    = logic,
    parameter type         ar_chan_t   = logic,
    parameter type         r_chan_t    = logic,
    // AXI request & response structs
    parameter type         axi_req_t   = logic,
    parameter type         axi_rsp_t   = logic
) (
    input  logic     clk_i,  // Clock
    input  logic     rst_ni,  // Asynchronous reset active low
    input  logic     test_i,
    // subordinate port
    input  axi_req_t sbr_req_i,
    output axi_rsp_t sbr_rsp_o,
    // manager port
    output axi_req_t mgr_req_o,
    input  axi_rsp_t mgr_rsp_i
);

  if (Depth == '0) begin : gen_no_fifo
    // degenerate case, connect input to output
    assign mgr_req_o = sbr_req_i;
    assign sbr_rsp_o = mgr_rsp_i;
  end else begin : gen_axi_fifo
    logic aw_fifo_empty, ar_fifo_empty, w_fifo_empty, r_fifo_empty, b_fifo_empty;
    logic aw_fifo_full, ar_fifo_full, w_fifo_full, r_fifo_full, b_fifo_full;

    assign mgr_req_o.aw_valid = ~aw_fifo_empty;
    assign mgr_req_o.ar_valid = ~ar_fifo_empty;
    assign mgr_req_o.w_valid  = ~w_fifo_empty;
    assign sbr_rsp_o.r_valid  = ~r_fifo_empty;
    assign sbr_rsp_o.b_valid  = ~b_fifo_empty;

    assign sbr_rsp_o.aw_ready = ~aw_fifo_full;
    assign sbr_rsp_o.ar_ready = ~ar_fifo_full;
    assign sbr_rsp_o.w_ready  = ~w_fifo_full;
    assign mgr_req_o.r_ready  = ~r_fifo_full;
    assign mgr_req_o.b_ready  = ~b_fifo_full;

    // A FiFo for each channel
    fifo_v3 #(
        .dtype(aw_chan_t),
        .DEPTH(Depth),
        .FALL_THROUGH(FallThrough)
    ) i_aw_fifo (
        .clk_i,
        .rst_ni,
        .flush_i   (1'b0),
        .testmode_i(test_i),
        .full_o    (aw_fifo_full),
        .empty_o   (aw_fifo_empty),
        .usage_o   (),
        .data_i    (sbr_req_i.aw),
        .push_i    (sbr_req_i.aw_valid && sbr_rsp_o.aw_ready),
        .data_o    (mgr_req_o.aw),
        .pop_i     (mgr_req_o.aw_valid && mgr_rsp_i.aw_ready)
    );
    fifo_v3 #(
        .dtype(ar_chan_t),
        .DEPTH(Depth),
        .FALL_THROUGH(FallThrough)
    ) i_ar_fifo (
        .clk_i,
        .rst_ni,
        .flush_i   (1'b0),
        .testmode_i(test_i),
        .full_o    (ar_fifo_full),
        .empty_o   (ar_fifo_empty),
        .usage_o   (),
        .data_i    (sbr_req_i.ar),
        .push_i    (sbr_req_i.ar_valid && sbr_rsp_o.ar_ready),
        .data_o    (mgr_req_o.ar),
        .pop_i     (mgr_req_o.ar_valid && mgr_rsp_i.ar_ready)
    );
    fifo_v3 #(
        .dtype(w_chan_t),
        .DEPTH(Depth),
        .FALL_THROUGH(FallThrough)
    ) i_w_fifo (
        .clk_i,
        .rst_ni,
        .flush_i   (1'b0),
        .testmode_i(test_i),
        .full_o    (w_fifo_full),
        .empty_o   (w_fifo_empty),
        .usage_o   (),
        .data_i    (sbr_req_i.w),
        .push_i    (sbr_req_i.w_valid && sbr_rsp_o.w_ready),
        .data_o    (mgr_req_o.w),
        .pop_i     (mgr_req_o.w_valid && mgr_rsp_i.w_ready)
    );
    fifo_v3 #(
        .dtype(r_chan_t),
        .DEPTH(Depth),
        .FALL_THROUGH(FallThrough)
    ) i_r_fifo (
        .clk_i,
        .rst_ni,
        .flush_i   (1'b0),
        .testmode_i(test_i),
        .full_o    (r_fifo_full),
        .empty_o   (r_fifo_empty),
        .usage_o   (),
        .data_i    (mgr_rsp_i.r),
        .push_i    (mgr_rsp_i.r_valid && mgr_req_o.r_ready),
        .data_o    (sbr_rsp_o.r),
        .pop_i     (sbr_rsp_o.r_valid && sbr_req_i.r_ready)
    );
    fifo_v3 #(
        .dtype(b_chan_t),
        .DEPTH(Depth),
        .FALL_THROUGH(FallThrough)
    ) i_b_fifo (
        .clk_i,
        .rst_ni,
        .flush_i   (1'b0),
        .testmode_i(test_i),
        .full_o    (b_fifo_full),
        .empty_o   (b_fifo_empty),
        .usage_o   (),
        .data_i    (mgr_rsp_i.b),
        .push_i    (mgr_rsp_i.b_valid && mgr_req_o.b_ready),
        .data_o    (sbr_rsp_o.b),
        .pop_i     (sbr_rsp_o.b_valid && sbr_req_i.b_ready)
    );
  end

  // Check the invariants
  // pragma translate_off
`ifndef VERILATOR
  initial begin
    assert (Depth >= 0);
  end
`endif
  // pragma translate_on
endmodule

`include "axi/assign.svh"
`include "axi/typedef.svh"

// interface wrapper
module axi_fifo_intf #(
    parameter int unsigned ADDR_WIDTH = 0,  // The address width.
    parameter int unsigned DATA_WIDTH = 0,  // The data width.
    parameter int unsigned ID_WIDTH = 0,  // The ID width.
    parameter int unsigned USER_WIDTH = 0,  // The user data width.
    parameter int unsigned DEPTH = 0,  // The number of FiFo slots.
    parameter int unsigned FALL_THROUGH = 0  // FiFo in fall-through mode
) (
    input logic    clk_i,
    input logic    rst_ni,
    input logic    test_i,
    AXI_BUS.Subordinate  sbr,
    AXI_BUS.Manager mgr
);

  typedef logic [ID_WIDTH-1:0] id_t;
  typedef logic [ADDR_WIDTH-1:0] addr_t;
  typedef logic [DATA_WIDTH-1:0] data_t;
  typedef logic [DATA_WIDTH/8-1:0] strb_t;
  typedef logic [USER_WIDTH-1:0] user_t;

  `AXI_TYPEDEF_AW_CHAN_T(aw_chan_t, addr_t, id_t, user_t)
  `AXI_TYPEDEF_W_CHAN_T(w_chan_t, data_t, strb_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T(b_chan_t, id_t, user_t)
  `AXI_TYPEDEF_AR_CHAN_T(ar_chan_t, addr_t, id_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(r_chan_t, data_t, id_t, user_t)
  `AXI_TYPEDEF_REQ_T(axi_req_t, aw_chan_t, w_chan_t, ar_chan_t)
  `AXI_TYPEDEF_RSP_T(axi_rsp_t, b_chan_t, r_chan_t)

  axi_req_t sbr_req, mgr_req;
  axi_rsp_t sbr_rsp, mgr_rsp;

  `AXI_ASSIGN_TO_REQ(sbr_req, sbr)
  `AXI_ASSIGN_FROM_RSP(sbr, sbr_rsp)

  `AXI_ASSIGN_FROM_REQ(mgr, mgr_req)
  `AXI_ASSIGN_TO_RSP(mgr_rsp, mgr)

  axi_fifo #(
      .Depth      (DEPTH),
      .FallThrough(FALL_THROUGH),
      .aw_chan_t  (aw_chan_t),
      .w_chan_t   (w_chan_t),
      .b_chan_t   (b_chan_t),
      .ar_chan_t  (ar_chan_t),
      .r_chan_t   (r_chan_t),
      .axi_req_t  (axi_req_t),
      .axi_rsp_t (axi_rsp_t)
  ) i_axi_fifo (
      .clk_i,
      .rst_ni,
      .test_i,
      .sbr_req_i (sbr_req),
      .sbr_rsp_o(sbr_rsp),
      .mgr_req_o (mgr_req),
      .mgr_rsp_i(mgr_rsp)
  );

  // Check the invariants.
  // pragma translate_off
`ifndef VERILATOR
  initial begin
    assert (ADDR_WIDTH > 0)
    else $fatal(1, "Wrong addr width parameter");
    assert (DATA_WIDTH > 0)
    else $fatal(1, "Wrong data width parameter");
    assert (ID_WIDTH > 0)
    else $fatal(1, "Wrong id   width parameter");
    assert (USER_WIDTH > 0)
    else $fatal(1, "Wrong user width parameter");
    assert (sbr.AXI_ADDR_WIDTH == ADDR_WIDTH)
    else $fatal(1, "Wrong interface definition");
    assert (sbr.AXI_DATA_WIDTH == DATA_WIDTH)
    else $fatal(1, "Wrong interface definition");
    assert (sbr.AXI_ID_WIDTH == ID_WIDTH)
    else $fatal(1, "Wrong interface definition");
    assert (sbr.AXI_USER_WIDTH == USER_WIDTH)
    else $fatal(1, "Wrong interface definition");
    assert (mgr.AXI_ADDR_WIDTH == ADDR_WIDTH)
    else $fatal(1, "Wrong interface definition");
    assert (mgr.AXI_DATA_WIDTH == DATA_WIDTH)
    else $fatal(1, "Wrong interface definition");
    assert (mgr.AXI_ID_WIDTH == ID_WIDTH)
    else $fatal(1, "Wrong interface definition");
    assert (mgr.AXI_USER_WIDTH == USER_WIDTH)
    else $fatal(1, "Wrong interface definition");
  end
`endif
  // pragma translate_on
endmodule
