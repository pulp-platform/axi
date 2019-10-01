// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// AXI ATOP Filter: This module filters atomic operations (ATOPs), i.e., write transactions that
// have a non-zero `aw_atop` value, from its `slv` to its `mst` port. This module guarantees that:
//
// 1) `aw_atop` is always zero on the `mst` port;
//
// 2) write transactions with non-zero `aw_atop` on the `slv` port are handled in conformance with
//    the AXI standard by replying to such write transactions with the proper B and R responses. The
//    response code on atomic operations that reach this module is always SLVERR
//    (implementation-specific, not defined in the AXI standard).
//
// This module is intended to be placed between masters that may issue ATOPs and slaves that do not
// support ATOPs. That way, this module ensures that the AXI protocol remains in a defined state on
// systems with mixed ATOP capabilities.
//
// Interface note:
// The AXI standard specifies that there may be no ordering requirements between different atomic
// bursts (i.e., a burst started by an AW with ATOP other than 0) and none between atomic bursts and
// non-atomic bursts [E2.1.4]. That is, an atomic burst may never have the same ID as any other
// write or read burst that is ongoing at the same time.
// Note: This is a wrapper that

`include "axi/assign.svh"
`include "axi/typedef.svh"

module axi_atop_filter_wrap #(
  parameter int unsigned AXI_ID_WIDTH   = 0, // Synopsys DC requires a default value for parameters.
  parameter int unsigned AXI_ADDR_WIDTH = 0,
  parameter int unsigned AXI_DATA_WIDTH = 0,
  parameter int unsigned AXI_USER_WIDTH = 0,
  // Maximum number of AXI write bursts outstanding at the same time
  parameter int unsigned AXI_MAX_WRITE_TXNS = 0
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
  `AXI_TYPEDEF_AW_CHAN_T ( aw_chan_t, addr_t, id_t,         user_t);
  `AXI_TYPEDEF_W_CHAN_T  (  w_chan_t, data_t,       strb_t, user_t);
  `AXI_TYPEDEF_B_CHAN_T  (  b_chan_t,         id_t,         user_t);
  `AXI_TYPEDEF_AR_CHAN_T ( ar_chan_t, addr_t, id_t,         user_t);
  `AXI_TYPEDEF_R_CHAN_T  (  r_chan_t, data_t, id_t,         user_t);
  `AXI_TYPEDEF_REQ_T     (     req_t, aw_chan_t, w_chan_t, ar_chan_t);
  `AXI_TYPEDEF_RESP_T    (    resp_t,  b_chan_t, r_chan_t) ;

  req_t  slv_req,  mst_req;
  resp_t slv_resp, mst_resp;

  `AXI_ASSIGN_TO_REQ    ( slv_req,  slv      );
  `AXI_ASSIGN_FROM_RESP ( slv,      slv_resp );

  `AXI_ASSIGN_FROM_REQ  ( mst     , mst_req  );
  `AXI_ASSIGN_TO_RESP   ( mst_resp, mst      );

  axi_atop_filter #(
    .AXI_ID_WIDTH       (AXI_ID_WIDTH       ),
  // Maximum number of AXI write bursts outstanding at the same time
    .AXI_MAX_WRITE_TXNS (AXI_MAX_WRITE_TXNS ),
  // AXI request & response type
    .req_t  ( req_t  ),
    .resp_t ( resp_t )
  ) i_axi_atop_filter (
    .clk_i      ( clk_i    ),
    .rst_ni     ( rst_ni   ),
    .slv_req_i  ( slv_req  ),
    .slv_resp_o ( slv_resp ),
    .mst_req_o  ( mst_req  ),
    .mst_resp_i ( mst_resp )
  );
endmodule
