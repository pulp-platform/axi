// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Author: Florian Zaruba, zarubaf@iis.ee.ethz.ch
// Description: Synthesiseable module which (randomly) delays AXI channels

module axi_delayer #(
  // AXI channel types
  parameter type aw_chan_t = logic,
  parameter type  w_chan_t = logic,
  parameter type  b_chan_t = logic,
  parameter type ar_chan_t = logic,
  parameter type  r_chan_t = logic,
  // AXI request & response types
  parameter type     req_t = logic,
  parameter type    resp_t = logic,
  // delay parameters
  parameter bit          StallRandomInput  = 0,
  parameter bit          StallRandomOutput = 0,
  parameter int unsigned FixedDelayInput   = 1,
  parameter int unsigned FixedDelayOutput  = 1
) (
  input  logic  clk_i,      // Clock
  input  logic  rst_ni,     // Asynchronous reset active low
  // slave port
  input  req_t  slv_req_i,
  output resp_t slv_resp_o,
  // master port
  output req_t  mst_req_o,
  input  resp_t mst_resp_i
);
  // AW
  stream_delay #(
    .StallRandom ( StallRandomInput ),
    .FixedDelay  ( FixedDelayInput  ),
    .payload_t   ( aw_chan_t        )
  ) i_stream_delay_aw (
    .clk_i,
    .rst_ni,
    .payload_i ( slv_req_i.aw        ),
    .ready_o   ( slv_resp_o.aw_ready ),
    .valid_i   ( slv_req_i.aw_valid  ),
    .payload_o ( mst_req_o.aw        ),
    .ready_i   ( mst_resp_i.aw_ready ),
    .valid_o   ( mst_req_o.aw_valid  )
  );

  // AR
  stream_delay #(
    .StallRandom ( StallRandomInput ),
    .FixedDelay  ( FixedDelayInput  ),
    .payload_t   ( ar_chan_t        )
  ) i_stream_delay_ar (
    .clk_i,
    .rst_ni,
    .payload_i ( slv_req_i.ar        ),
    .ready_o   ( slv_resp_o.ar_ready ),
    .valid_i   ( slv_req_i.ar_valid  ),
    .payload_o ( mst_req_o.ar        ),
    .ready_i   ( mst_resp_i.ar_ready ),
    .valid_o   ( mst_req_o.ar_valid  )
  );

  // W
  stream_delay #(
    .StallRandom ( StallRandomInput ),
    .FixedDelay  ( FixedDelayInput  ),
    .payload_t   ( w_chan_t         )
  ) i_stream_delay_w (
    .clk_i,
    .rst_ni,
    .payload_i ( slv_req_i.w        ),
    .ready_o   ( slv_resp_o.w_ready ),
    .valid_i   ( slv_req_i.w_valid  ),
    .payload_o ( mst_req_o.w        ),
    .ready_i   ( mst_resp_i.w_ready ),
    .valid_o   ( mst_req_o.w_valid  )
  );

  // B
  stream_delay #(
    .StallRandom ( StallRandomOutput ),
    .FixedDelay  ( FixedDelayOutput  ),
    .payload_t   ( b_chan_t          )
  ) i_stream_delay_b (
    .clk_i,
    .rst_ni,
    .payload_i ( mst_resp_i.b       ),
    .ready_o   ( mst_req_o.b_ready  ),
    .valid_i   ( mst_resp_i.b_valid ),
    .payload_o ( slv_resp_o.b       ),
    .ready_i   ( slv_req_i.b_ready  ),
    .valid_o   ( slv_resp_o.b_valid )
  );

  // R
   stream_delay #(
    .StallRandom ( StallRandomOutput ),
    .FixedDelay  ( FixedDelayOutput  ),
    .payload_t   ( r_chan_t          )
  ) i_stream_delay_r (
    .clk_i,
    .rst_ni,
    .payload_i ( mst_resp_i.r       ),
    .ready_o   ( mst_req_o.r_ready  ),
    .valid_i   ( mst_resp_i.r_valid ),
    .payload_o ( slv_resp_o.r       ),
    .ready_i   ( slv_req_i.r_ready  ),
    .valid_o   ( slv_resp_o.r_valid )
  );
endmodule

`include "axi/typedef.svh"

// unwrapped structs
module axi_delayer_wrap #(
  parameter type aw_t = logic,
  parameter type  w_t = logic,
  parameter type  b_t = logic,
  parameter type ar_t = logic,
  parameter type  r_t = logic,
  parameter bit          StallRandomInput  = 0,
  parameter bit          StallRandomOutput = 0,
  parameter int unsigned FixedDelayInput   = 1,
  parameter int unsigned FixedDelayOutput  = 1
) (
  input  logic clk_i,   // Clock
  input  logic rst_ni,  // Asynchronous reset active low
  // input side
  input  logic aw_valid_i,
  input  aw_t  aw_chan_i,
  output logic aw_ready_o,

  input  logic w_valid_i,
  input  w_t   w_chan_i,
  output logic w_ready_o,

  output logic b_valid_o,
  output b_t   b_chan_o,
  input  logic b_ready_i,

  input  logic ar_valid_i,
  input  ar_t  ar_chan_i,
  output logic ar_ready_o,

  output logic r_valid_o,
  output r_t   r_chan_o,
  input  logic r_ready_i,

  // output side
  output logic aw_valid_o,
  output aw_t  aw_chan_o,
  input  logic aw_ready_i,

  output logic w_valid_o,
  output w_t   w_chan_o,
  input  logic w_ready_i,

  input  logic b_valid_i,
  input  b_t   b_chan_i,
  output logic b_ready_o,

  output logic ar_valid_o,
  output ar_t  ar_chan_o,
  input  logic ar_ready_i,

  input  logic r_valid_i,
  input  r_t   r_chan_i,
  output logic r_ready_o
);

  `AXI_TYPEDEF_REQ_T  (  req_t, aw_t, w_t, ar_t)
  `AXI_TYPEDEF_RESP_T ( resp_t,  b_t, r_t)

  req_t  slv_req,  mst_req;
  resp_t slv_resp, mst_resp;

  // assign the slave port to the request and responses
  // AW
  assign slv_req.aw_valid  = aw_valid_i        ;
  assign slv_req.aw        = aw_chan_i         ;
  assign aw_ready_o        = slv_resp.aw_ready ;
  //  W
  assign slv_req.w_valid   = w_valid_i         ;
  assign slv_req.w         = w_chan_i          ;
  assign w_ready_o         = slv_resp.w_ready  ;
  //  B
  assign b_valid_o         = slv_resp.b_valid  ;
  assign b_chan_o          = slv_resp.b        ;
  assign slv_req.b_ready   = b_ready_i         ;
  // AR
  assign slv_req.ar_valid  = ar_valid_i        ;
  assign slv_req.ar        = ar_chan_i         ;
  assign ar_ready_o        = slv_resp.ar_ready ;
  //  R
  assign r_valid_o         = slv_resp.r_valid  ;
  assign r_chan_o          = slv_resp.r        ;
  assign slv_req.r_ready   = r_ready_i         ;
  // assign the master port to the request and responses
  assign aw_valid_o        = mst_req.aw_valid  ;
  assign aw_chan_o         = mst_req.aw        ;
  assign mst_resp.aw_ready = aw_ready_i        ;

  assign w_valid_o         = mst_req.w_valid   ;
  assign w_chan_o          = mst_req.w         ;
  assign mst_resp.w_ready  = w_ready_i         ;

  assign mst_resp.b_valid  = b_valid_i         ;
  assign mst_resp.b        = b_chan_i          ;
  assign b_ready_o         = mst_req.b_ready   ;

  assign ar_valid_o        = mst_req.ar_valid  ;
  assign ar_chan_o         = mst_req.ar        ;
  assign mst_resp.ar_ready = ar_ready_i        ;

  assign mst_resp.r_valid  = r_valid_i         ;
  assign mst_resp.r        = r_chan_i          ;
  assign r_ready_o         = mst_req.r_ready   ;

  axi_delayer #(
    .aw_chan_t         (   aw_t ),
    .w_chan_t          (    w_t ),
    .b_chan_t          (    b_t ),
    .ar_chan_t         (   ar_t ),
    .r_chan_t          (    r_t ),
    .req_t             (  req_t ),
    .resp_t            ( resp_t ),
    .StallRandomOutput ( StallRandomOutput ),
    .StallRandomInput  ( StallRandomInput  ),
    .FixedDelayInput   ( FixedDelayInput   ),
    .FixedDelayOutput  ( FixedDelayOutput  )
  ) i_axi_delayer (
    .clk_i,   // Clock
    .rst_ni,  // Asynchronous reset active low
    .slv_req_i  ( slv_req  ),
    .slv_resp_o ( slv_resp ),
    .mst_req_o  ( mst_req  ),
    .mst_resp_i ( mst_resp )
  );
endmodule

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
  AXI_BUS.Slave   slv,
  AXI_BUS.Master  mst
);

  typedef logic [AXI_ID_WIDTH-1:0]     id_t;
  typedef logic [AXI_ADDR_WIDTH-1:0]   addr_t;
  typedef logic [AXI_DATA_WIDTH-1:0]   data_t;
  typedef logic [AXI_DATA_WIDTH/8-1:0] strb_t;
  typedef logic [AXI_USER_WIDTH-1:0]   user_t;

  `AXI_TYPEDEF_AW_CHAN_T ( aw_chan_t, addr_t, id_t,         user_t)
  `AXI_TYPEDEF_W_CHAN_T  (  w_chan_t, data_t,       strb_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T  (  b_chan_t,         id_t,         user_t)
  `AXI_TYPEDEF_AR_CHAN_T ( ar_chan_t, addr_t, id_t,         user_t)
  `AXI_TYPEDEF_R_CHAN_T  (  r_chan_t, data_t, id_t,         user_t)
  `AXI_TYPEDEF_REQ_T     (     req_t, aw_chan_t, w_chan_t, ar_chan_t)
  `AXI_TYPEDEF_RESP_T    (    resp_t,  b_chan_t, r_chan_t)

  req_t  slv_req,  mst_req;
  resp_t slv_resp, mst_resp;

  `AXI_ASSIGN_TO_REQ    ( slv_req,  slv      )
  `AXI_ASSIGN_FROM_RESP ( slv,      slv_resp )

  `AXI_ASSIGN_FROM_REQ  ( mst     , mst_req  )
  `AXI_ASSIGN_TO_RESP   ( mst_resp, mst      )

  axi_delayer #(
    .aw_chan_t         (           aw_chan_t ),
    .w_chan_t          (            w_chan_t ),
    .b_chan_t          (            b_chan_t ),
    .ar_chan_t         (           ar_chan_t ),
    .r_chan_t          (            r_chan_t ),
    .req_t             (               req_t ),
    .resp_t            (              resp_t ),
    .StallRandomInput  ( STALL_RANDOM_INPUT  ),
    .StallRandomOutput ( STALL_RANDOM_OUTPUT ),
    .FixedDelayInput   ( FIXED_DELAY_INPUT   ),
    .FixedDelayOutput  ( FIXED_DELAY_OUTPUT  )
  ) i_axi_delayer (
    .clk_i,   // Clock
    .rst_ni,  // Asynchronous reset active low
    .slv_req_i  ( slv_req  ),
    .slv_resp_o ( slv_resp ),
    .mst_req_o  ( mst_req  ),
    .mst_resp_i ( mst_resp )
  );
endmodule
