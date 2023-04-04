/* Copyright 2021 ETH Zurich and University of Bologna.
 * Copyright and related rights are licensed under the Solderpad Hardware
 * License, Version 0.51 (the “License”); you may not use this file except in
 * compliance with the License.  You may obtain a copy of the License at
 * http: //solderpad.org/licenses/SHL-0.51. Unless required by applicable law
 * or agreed to in writing, software, hardware and materials distributed under
 * this License is distributed on an “AS IS” BASIS, WITHOUT WARRANTIES OR
 * CONDITIONS OF ANY KIND, either express or implied. See the License for the
 * specific language governing permissions and limitations under the License.
 *
 * Author: Michael Rogenmoser <michaero@iis.ee.ethz.ch>
 * Date:   15.02.2022
 *
 */

/// Only allows passing of AW if corresponding W is valid.
/// Only allows passing of W if corresponding AW is valid or sent.

`include "axi/assign.svh"
`include "common_cells/registers.svh"

module axi_aw_w_sync #(
  parameter type axi_req_t  = logic,
  parameter type axi_resp_t = logic
) (
  input  logic      clk_i,
  input  logic      rst_ni,

  input  axi_req_t  slv_req_i,
  output axi_resp_t slv_resp_o,

  output axi_req_t  mst_req_o,
  input  axi_resp_t mst_resp_i
);

  `AXI_ASSIGN_AR_STRUCT(mst_req_o.ar, slv_req_i.ar)
  assign mst_req_o.ar_valid = slv_req_i.ar_valid;
  assign slv_resp_o.ar_ready = mst_resp_i.ar_ready;
  `AXI_ASSIGN_R_STRUCT(slv_resp_o.r, mst_resp_i.r)
  assign slv_resp_o.r_valid = mst_resp_i.r_valid;
  assign mst_req_o.r_ready = slv_req_i.r_ready;
  `AXI_ASSIGN_B_STRUCT(slv_resp_o.b, mst_resp_i.b)
  assign slv_resp_o.b_valid = mst_resp_i.b_valid;
  assign mst_req_o.b_ready = slv_req_i.b_ready;

  `AXI_ASSIGN_AW_STRUCT(mst_req_o.aw, slv_req_i.aw)
  `AXI_ASSIGN_W_STRUCT(mst_req_o.w, slv_req_i.w)

  logic aw_valid, w_valid;
  logic w_completed_d, w_completed_q;
  `FF(w_completed_q, w_completed_d, 1'b1)


  // AW is valid when previous write completed and current AW and W are valid
  assign aw_valid = w_completed_q && slv_req_i.aw_valid && slv_req_i.w_valid;

  // W is valid when corresponding AW is valid or sent
  assign w_valid = slv_req_i.w_valid && (!w_completed_q || (aw_valid && mst_resp_i.aw_ready)); // This is probably pretty bad for timing

  always_comb begin
    w_completed_d = w_completed_q;
    // reset w_completed to 0 when a new AW request happens
    if (aw_valid && mst_resp_i.aw_ready) begin
      w_completed_d = 1'b0;
    end
    // assign w_completed to w_last when W handshake is done and W is ongoing
    if (slv_req_i.w_valid && slv_resp_o.w_ready) begin
      w_completed_d = slv_req_i.w.last;
    end
  end

  assign mst_req_o.w_valid = w_valid;
  assign slv_resp_o.w_ready = w_valid && mst_resp_i.w_ready;
  assign mst_req_o.aw_valid = aw_valid;
  assign slv_resp_o.aw_ready = aw_valid && mst_resp_i.aw_ready;
  
endmodule

`include "axi/typedef.svh"

module axi_aw_w_sync_intf #(
  parameter int unsigned AXI_ADDR_WIDTH = 0,
  parameter int unsigned AXI_DATA_WIDTH = 0,
  parameter int unsigned AXI_ID_WIDTH   = 0,
  parameter int unsigned AXI_USER_WIDTH = 0
) (
  input logic    clk_i,
  input logic    rst_ni,
  AXI_BUS.Slave  in,
  AXI_BUS.Master out
);

  typedef logic [    AXI_ID_WIDTH-1:0] id_t;
  typedef logic [  AXI_ADDR_WIDTH-1:0] addr_t;
  typedef logic [  AXI_DATA_WIDTH-1:0] data_t;
  typedef logic [AXI_DATA_WIDTH/8-1:0] strb_t;
  typedef logic [  AXI_USER_WIDTH-1:0] user_t;

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

  axi_aw_w_sync #(
    .axi_req_t  ( axi_req_t  ),
    .axi_resp_t ( axi_resp_t )
  ) i_axi_aw_w_sync (
    .clk_i,
    .rst_ni,
    .slv_req_i  ( slv_req  ),
    .slv_resp_o ( slv_resp ),
    .mst_req_o  ( mst_req  ),
    .mst_resp_i ( mst_resp )
  );
  
endmodule