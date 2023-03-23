// Copyright (c) 2023 ETH Zurich, University of Bologna
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
// - Thomas Benz <tbenz@iis.ee.ethz.ch>

`include "common_cells/registers.svh"

module axi_write_buffer #(
  parameter int unsigned NumOutstanding = 32'd0,
  parameter int unsigned WBufferDepth   = 32'd0,
  parameter int unsigned IdxWWidth      = cf_math_pkg::idx_width(WBufferDepth),
  parameter int unsigned IdxAwWidth     = cf_math_pkg::idx_width(NumOutstanding),
  parameter type         aw_chan_t      = logic,
  parameter type         w_chan_t       = logic,
  parameter type         axi_req_t      = logic,
  parameter type         axi_resp_t     = logic,
  // Dependent parameter, do **not** overwite!
  parameter type         idx_w_t        = logic [IdxWWidth-1:0],
  parameter type         idx_aw_t       = logic [IdxAwWidth-1:0]
)(
  input logic clk_i,
  input logic rst_ni,

  // Input / Slave Port
  input  axi_req_t  slv_req_i,
  output axi_resp_t slv_resp_o,

  // Output / Master Port
  output axi_req_t  mst_req_o,
  input  axi_resp_t mst_resp_i,

  // status
  output idx_w_t    num_w_stored_o,
  output idx_aw_t   num_aw_stored_o
);

  logic ingress_w_last;
  logic egress_w_last;

  logic egress_w_ready;
  logic egress_w_valid;

  logic egress_aw_ready;
  logic egress_aw_valid;

  logic mgmt_ready_w, mgmt_ready_aw;
  logic mgmt_valid_w, mgmt_valid_aw;

  // counter for amount of lasts in queue
  idx_w_t  num_lasts_d, num_lasts_q;


  // --------------------------------------------------
  // Bypass
  // --------------------------------------------------
  // bypass the B, AR, R channels
  assign mst_req_o.ar        = slv_req_i.ar;
  assign mst_req_o.ar_valid  = slv_req_i.ar_valid;
  assign slv_resp_o.ar_ready = mst_resp_i.ar_ready;

  assign slv_resp_o.r        = mst_resp_i.r;
  assign slv_resp_o.r_valid  = mst_resp_i.r_valid;
  assign mst_req_o.r_ready   = slv_req_i.r_ready;

  assign slv_resp_o.b        = mst_resp_i.b;
  assign slv_resp_o.b_valid  = mst_resp_i.b_valid;
  assign mst_req_o.b_ready   = slv_req_i.b_ready;


  // --------------------------------------------------
  // handle AW channel
  // --------------------------------------------------
  // buffer AW
  stream_fifo #(
    .DEPTH      ( NumOutstanding ),
    .T          ( aw_chan_t      )
  ) i_stream_fifo_aw (
    .clk_i,
    .rst_ni,
    .flush_i    ( 1'b0                ),
    .testmode_i ( 1'b0                ),
    .usage_o    ( num_aw_stored_o     ),
    .data_i     ( slv_req_i.aw        ),
    .valid_i    ( slv_req_i.aw_valid  ),
    .ready_o    ( slv_resp_o.aw_ready ),
    .data_o     ( mst_req_o.aw        ),
    .valid_o    ( egress_aw_valid     ),
    .ready_i    ( egress_aw_ready     )
  );


  // use a stream join to ensure handshaking is correct
  stream_join #(
    .N_INP       ( 32'd2  )
  ) i_stream_join_aw (
    .inp_valid_i ( {mgmt_valid_aw, egress_aw_valid} ),
    .inp_ready_o ( {mgmt_ready_aw, egress_aw_ready} ),
    .oup_valid_o ( mst_req_o.aw_valid               ),
    .oup_ready_i ( mst_resp_i.aw_ready              )
  );

  assign mgmt_valid_aw = ingress_w_last;


  // --------------------------------------------------
  // handle W channel
  // --------------------------------------------------
  // buffer W
  stream_fifo #(
    .DEPTH      ( WBufferDepth ),
    .T          ( w_chan_t     ),
    .ADDR_DEPTH ( IdxWWidth    )
  ) i_stream_fifo_w (
    .clk_i,
    .rst_ni,
    .flush_i    ( 1'b0               ),
    .testmode_i ( 1'b0               ),
    .usage_o    ( num_w_stored_o     ),
    .data_i     ( slv_req_i.w        ),
    .valid_i    ( slv_req_i.w_valid  ),
    .ready_o    ( slv_resp_o.w_ready ),
    .data_o     ( mst_req_o.w        ),
    .valid_o    ( egress_w_valid     ),
    .ready_i    ( egress_w_ready     )
  );

  // last signals
  assign ingress_w_last = slv_req_i.w.last & slv_req_i.w_valid & slv_resp_o.w_ready;
  assign egress_w_last  = mst_req_o.w.last & egress_w_valid & egress_w_ready;

  // number of buffered lasts
  always_comb begin : proc_num_lasts_counter
    // default
    num_lasts_d = num_lasts_q;

    // if one enters the queue: increment counter
    if (ingress_w_last) begin
      num_lasts_d = num_lasts_q + 1;
    end

    // if one leaves: decrease counter
    if (egress_w_last) begin
      num_lasts_d = num_lasts_q - 1;
    end
  end

  // as long as there is credit -> drain
  assign mgmt_valid_w = num_lasts_q > 0;

  // use a stream join to ensure handshaking is correct
  stream_join #(
    .N_INP       ( 32'd2  )
  ) i_stream_join_w (
    .inp_valid_i ( {mgmt_valid_w, egress_w_valid} ),
    .inp_ready_o ( {mgmt_ready_w, egress_w_ready} ),
    .oup_valid_o ( mst_req_o.w_valid              ),
    .oup_ready_i ( mst_resp_i.w_ready             )
  );


  // --------------------------------------------------
  // state
  // --------------------------------------------------
  `FFARN(num_lasts_q, num_lasts_d, '0, clk_i, rst_ni)

endmodule
