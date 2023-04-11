// Copyright 2018 ETH Zurich and University of Bologna.
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
// - Florian Zaruba <zarubaf@iis.ee.ethz.ch>
// - Andreas Kurth <akurth@iis.ee.ethz.ch>

/// Synthesizable module that (randomly) delays AXI channels.
module axi_delayer #(
  // AXI channel types
  parameter type aw_chan_t = logic,
  parameter type  w_chan_t = logic,
  parameter type  b_chan_t = logic,
  parameter type ar_chan_t = logic,
  parameter type  r_chan_t = logic,
  // AXI request & response types
  parameter type axi_req_t = logic,
  parameter type axi_rsp_t = logic,
  // delay parameters
  parameter bit          StallRandomInput  = 0,
  parameter bit          StallRandomOutput = 0,
  parameter int unsigned FixedDelayInput   = 1,
  parameter int unsigned FixedDelayOutput  = 1
) (
  input  logic     clk_i,      // Clock
  input  logic     rst_ni,     // Asynchronous reset active low
  // subordinate port
  input  axi_req_t sbr_port_req_i,
  output axi_rsp_t sbr_port_rsp_o,
  // manager port
  output axi_req_t mgr_port_req_o,
  input  axi_rsp_t mgr_port_rsp_i
);
  // AW
  stream_delay #(
    .StallRandom ( StallRandomInput ),
    .FixedDelay  ( FixedDelayInput  ),
    .payload_t   ( aw_chan_t        )
  ) i_stream_delay_aw (
    .clk_i,
    .rst_ni,
    .payload_i ( sbr_port_req_i.aw       ),
    .ready_o   ( sbr_port_rsp_o.aw_ready ),
    .valid_i   ( sbr_port_req_i.aw_valid ),
    .payload_o ( mgr_port_req_o.aw       ),
    .ready_i   ( mgr_port_rsp_i.aw_ready ),
    .valid_o   ( mgr_port_req_o.aw_valid )
  );

  // AR
  stream_delay #(
    .StallRandom ( StallRandomInput ),
    .FixedDelay  ( FixedDelayInput  ),
    .payload_t   ( ar_chan_t        )
  ) i_stream_delay_ar (
    .clk_i,
    .rst_ni,
    .payload_i ( sbr_port_req_i.ar       ),
    .ready_o   ( sbr_port_rsp_o.ar_ready ),
    .valid_i   ( sbr_port_req_i.ar_valid ),
    .payload_o ( mgr_port_req_o.ar       ),
    .ready_i   ( mgr_port_rsp_i.ar_ready ),
    .valid_o   ( mgr_port_req_o.ar_valid )
  );

  // W
  stream_delay #(
    .StallRandom ( StallRandomInput ),
    .FixedDelay  ( FixedDelayInput  ),
    .payload_t   ( w_chan_t         )
  ) i_stream_delay_w (
    .clk_i,
    .rst_ni,
    .payload_i ( sbr_port_req_i.w       ),
    .ready_o   ( sbr_port_rsp_o.w_ready ),
    .valid_i   ( sbr_port_req_i.w_valid ),
    .payload_o ( mgr_port_req_o.w       ),
    .ready_i   ( mgr_port_rsp_i.w_ready ),
    .valid_o   ( mgr_port_req_o.w_valid )
  );

  // B
  stream_delay #(
    .StallRandom ( StallRandomOutput ),
    .FixedDelay  ( FixedDelayOutput  ),
    .payload_t   ( b_chan_t          )
  ) i_stream_delay_b (
    .clk_i,
    .rst_ni,
    .payload_i ( mgr_port_rsp_i.b       ),
    .ready_o   ( mgr_port_req_o.b_ready ),
    .valid_i   ( mgr_port_rsp_i.b_valid ),
    .payload_o ( sbr_port_rsp_o.b       ),
    .ready_i   ( sbr_port_req_i.b_ready ),
    .valid_o   ( sbr_port_rsp_o.b_valid )
  );

  // R
   stream_delay #(
    .StallRandom ( StallRandomOutput ),
    .FixedDelay  ( FixedDelayOutput  ),
    .payload_t   ( r_chan_t          )
  ) i_stream_delay_r (
    .clk_i,
    .rst_ni,
    .payload_i ( mgr_port_rsp_i.r       ),
    .ready_o   ( mgr_port_req_o.r_ready ),
    .valid_i   ( mgr_port_rsp_i.r_valid ),
    .payload_o ( sbr_port_rsp_o.r       ),
    .ready_i   ( sbr_port_req_i.r_ready ),
    .valid_o   ( sbr_port_rsp_o.r_valid )
  );
endmodule

`include "axi/typedef.svh"
`include "axi/assign.svh"

// interface wrapper
module axi_delayer_intf #(
  // Synopsys DC requires a default value for parameters.
  parameter int unsigned AXI_ID_WIDTH        = 0,
  parameter int unsigned AXI_ADDR_WIDTH      = 0,
  parameter int unsigned AXI_DATA_WIDTH      = 0,
  parameter int unsigned AXI_USER_WIDTH      = 0,
  parameter bit          STALL_RANDOM_INPUT  = 0,
  parameter bit          STALL_RANDOM_OUTPUT = 0,
  parameter int unsigned FIXED_DELAY_INPUT   = 1,
  parameter int unsigned FIXED_DELAY_OUTPUT  = 1
) (
  input  logic    clk_i,
  input  logic    rst_ni,
  AXI_BUS.Subordinate   sbr,
  AXI_BUS.Manager  mgr
);

  typedef logic [AXI_ID_WIDTH-1:0]     id_t;
  typedef logic [AXI_ADDR_WIDTH-1:0]   addr_t;
  typedef logic [AXI_DATA_WIDTH-1:0]   data_t;
  typedef logic [AXI_DATA_WIDTH/8-1:0] strb_t;
  typedef logic [AXI_USER_WIDTH-1:0]   user_t;

  `AXI_TYPEDEF_AW_CHAN_T(aw_chan_t, addr_t, id_t, user_t)
  `AXI_TYPEDEF_W_CHAN_T(w_chan_t, data_t, strb_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T(b_chan_t, id_t, user_t)
  `AXI_TYPEDEF_AR_CHAN_T(ar_chan_t, addr_t, id_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(r_chan_t, data_t, id_t, user_t)
  `AXI_TYPEDEF_REQ_T(axi_req_t, aw_chan_t, w_chan_t, ar_chan_t)
  `AXI_TYPEDEF_RSP_T(axi_rsp_t, b_chan_t, r_chan_t)

  axi_req_t sbr_req,  mgr_req;
  axi_rsp_t sbr_rsp, mgr_rsp;

  `AXI_ASSIGN_TO_REQ(sbr_req, sbr)
  `AXI_ASSIGN_FROM_RSP(sbr, sbr_rsp)

  `AXI_ASSIGN_FROM_REQ(mgr, mgr_req)
  `AXI_ASSIGN_TO_RSP(mgr_rsp, mgr)

  axi_delayer #(
    .aw_chan_t         (           aw_chan_t ),
    .w_chan_t          (            w_chan_t ),
    .b_chan_t          (            b_chan_t ),
    .ar_chan_t         (           ar_chan_t ),
    .r_chan_t          (            r_chan_t ),
    .axi_req_t         (           axi_req_t ),
    .axi_rsp_t         (           axi_rsp_t ),
    .StallRandomInput  ( STALL_RANDOM_INPUT  ),
    .StallRandomOutput ( STALL_RANDOM_OUTPUT ),
    .FixedDelayInput   ( FIXED_DELAY_INPUT   ),
    .FixedDelayOutput  ( FIXED_DELAY_OUTPUT  )
  ) i_axi_delayer (
    .clk_i,   // Clock
    .rst_ni,  // Asynchronous reset active low
    .sbr_port_req_i ( sbr_req ),
    .sbr_port_rsp_o ( sbr_rsp ),
    .mgr_port_req_o ( mgr_req ),
    .mgr_port_rsp_i ( mgr_rsp )
  );

// pragma translate_off
`ifndef VERILATOR
  initial begin: p_assertions
    assert (AXI_ID_WIDTH >= 1) else $fatal(1, "AXI ID width must be at least 1!");
    assert (AXI_ADDR_WIDTH >= 1) else $fatal(1, "AXI ADDR width must be at least 1!");
    assert (AXI_DATA_WIDTH >= 1) else $fatal(1, "AXI DATA width must be at least 1!");
    assert (AXI_USER_WIDTH >= 1) else $fatal(1, "AXI USER width must be at least 1!");
  end
`endif
// pragma translate_on
endmodule
