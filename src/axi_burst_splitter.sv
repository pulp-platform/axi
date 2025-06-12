// Copyright (c) 2020 ETH Zurich, University of Bologna
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

`include "axi/typedef.svh"

/// Split AXI4 bursts into single-beat transactions.
///
/// ## Limitations
///
/// - This module does not support wrapping ([`axi_pkg::BURST_WRAP`](package.axi_pkg)) bursts and
///   responds to such bursts with slave error(s).
/// - This module does not support atomic operations (ATOPs) and responds to ATOPs with a slave
///   error.  Place an [`axi_atop_filter`](module.axi_atop_filter) before this module if upstream
///   modules can generate ATOPs.
module axi_burst_splitter #(
  // Maximum number of AXI read bursts outstanding at the same time
  parameter int unsigned MaxReadTxns  = 32'd0,
  // Maximum number of AXI write bursts outstanding at the same time
  parameter int unsigned MaxWriteTxns = 32'd0,
  // Internal ID queue can work in two bandwidth modes: see id_queue.sv for details
  parameter bit          FullBW       = 0,
  // AXI Bus Types
  parameter int unsigned AddrWidth    = 32'd0,
  parameter int unsigned DataWidth    = 32'd0,
  parameter int unsigned IdWidth      = 32'd0,
  parameter int unsigned UserWidth    = 32'd0,
  parameter type         axi_req_t    = logic,
  parameter type         axi_resp_t   = logic
) (
  input  logic  clk_i,
  input  logic  rst_ni,

  // Input / Slave Port
  input  axi_req_t  slv_req_i,
  output axi_resp_t slv_resp_o,

  // Output / Master Port
  output axi_req_t  mst_req_o,
  input  axi_resp_t mst_resp_i
);

  typedef logic [AddrWidth-1:0]   addr_t;
  typedef logic [DataWidth-1:0]   data_t;
  typedef logic [DataWidth/8-1:0] strb_t;
  typedef logic [IdWidth-1:0]     id_t;
  typedef logic [UserWidth-1:0]   user_t;

  `AXI_TYPEDEF_AW_CHAN_T(axi_aw_chan_t, addr_t, id_t, user_t)
  `AXI_TYPEDEF_W_CHAN_T (axi_w_chan_t, data_t, strb_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T (axi_b_chan_t, id_t, user_t)
  `AXI_TYPEDEF_AR_CHAN_T(axi_ar_chan_t, addr_t, id_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T (axi_r_chan_t, data_t, id_t, user_t)

  axi_burst_splitter_gran #(
    .MaxReadTxns   ( MaxReadTxns   ),
    .MaxWriteTxns  ( MaxWriteTxns  ),
    .CutPath       ( 1'b0          ),
    .DisableChecks ( 1'b0          ),
    .FullBW        ( FullBW        ),
    .AddrWidth     ( AddrWidth     ),
    .DataWidth     ( DataWidth     ),
    .IdWidth       ( IdWidth       ),
    .UserWidth     ( UserWidth     ),
    .axi_req_t     ( axi_req_t     ),
    .axi_resp_t    ( axi_resp_t    ),
    .axi_aw_chan_t ( axi_aw_chan_t ),
    .axi_w_chan_t  ( axi_w_chan_t  ),
    .axi_b_chan_t  ( axi_b_chan_t  ),
    .axi_ar_chan_t ( axi_ar_chan_t ),
    .axi_r_chan_t  ( axi_r_chan_t  )
  ) i_axi_burst_splitter_gran (
    .clk_i,
    .rst_ni,
    .len_limit_i ( 8'h00 ),
    .slv_req_i,
    .slv_resp_o,
    .mst_req_o,
    .mst_resp_i
  );

endmodule
