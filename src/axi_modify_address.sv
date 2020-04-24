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
// Fabian Schuiki <fschuiki@iis.ee.ethz.ch>
// Andreas Kurth  <akurth@iis.ee.ethz.ch>


// A connector that allows addresses of AXI requests to be changed.
module axi_modify_address #(
  parameter type  slv_req_t = logic, // request type slave port
  parameter type mst_addr_t = logic, // address type of master port
  parameter type  mst_req_t = logic, // request type master port
  parameter type     resp_t = logic  // response type of both ports
) (
  // slave port
  input  slv_req_t  slv_req_i,
  output resp_t     slv_resp_o,
  // master port
  output mst_req_t  mst_req_o,
  input  resp_t     mst_resp_i,
  input  mst_addr_t mst_aw_addr_i,
  input  mst_addr_t mst_ar_addr_i
);

  assign mst_req_o = '{
    aw: '{
      id:     slv_req_i.aw.id,
      addr:   mst_aw_addr_i,
      len:    slv_req_i.aw.len,
      size:   slv_req_i.aw.size,
      burst:  slv_req_i.aw.burst,
      lock:   slv_req_i.aw.lock,
      cache:  slv_req_i.aw.cache,
      prot:   slv_req_i.aw.prot,
      qos:    slv_req_i.aw.qos,
      region: slv_req_i.aw.region,
      atop:   slv_req_i.aw.atop,
      user:   slv_req_i.aw.user,
      default: '0
    },
    aw_valid: slv_req_i.aw_valid,
    w:        slv_req_i.w,
    w_valid:  slv_req_i.w_valid,
    b_ready:  slv_req_i.b_ready,
    ar: '{
      id:     slv_req_i.ar.id,
      addr:   mst_ar_addr_i,
      len:    slv_req_i.ar.len,
      size:   slv_req_i.ar.size,
      burst:  slv_req_i.ar.burst,
      lock:   slv_req_i.ar.lock,
      cache:  slv_req_i.ar.cache,
      prot:   slv_req_i.ar.prot,
      qos:    slv_req_i.ar.qos,
      region: slv_req_i.ar.region,
      user:   slv_req_i.ar.user,
      default: '0
    },
    ar_valid: slv_req_i.ar_valid,
    r_ready:  slv_req_i.r_ready,
    default: '0
  };

  assign slv_resp_o = mst_resp_i;
endmodule

`include "axi/typedef.svh"
`include "axi/assign.svh"

// interface wrapper
module axi_modify_address_intf #(
  parameter int unsigned AXI_SLV_PORT_ADDR_WIDTH = 0,
  parameter int unsigned AXI_MST_PORT_ADDR_WIDTH = AXI_SLV_PORT_ADDR_WIDTH,
  parameter int unsigned AXI_DATA_WIDTH = 0,
  parameter int unsigned AXI_ID_WIDTH = 0,
  parameter int unsigned AXI_USER_WIDTH = 0
) (
  AXI_BUS.Slave   slv,
  AXI_BUS.Master  mst,
  input  logic [AXI_MST_PORT_ADDR_WIDTH-1:0] mst_aw_addr_i,
  input  logic [AXI_MST_PORT_ADDR_WIDTH-1:0] mst_ar_addr_i
);

  typedef logic [AXI_ID_WIDTH-1:0]            id_t;
  typedef logic [AXI_SLV_PORT_ADDR_WIDTH-1:0] slv_addr_t;
  typedef logic [AXI_MST_PORT_ADDR_WIDTH-1:0] mst_addr_t;
  typedef logic [AXI_DATA_WIDTH-1:0]          data_t;
  typedef logic [AXI_DATA_WIDTH/8-1:0]        strb_t;
  typedef logic [AXI_USER_WIDTH-1:0]          user_t;

  `AXI_TYPEDEF_AW_CHAN_T(slv_aw_chan_t, slv_addr_t, id_t, user_t)
  `AXI_TYPEDEF_AW_CHAN_T(mst_aw_chan_t, mst_addr_t, id_t, user_t)
  `AXI_TYPEDEF_W_CHAN_T(w_chan_t, data_t, strb_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T(b_chan_t, id_t, user_t)
  `AXI_TYPEDEF_AR_CHAN_T(slv_ar_chan_t, slv_addr_t, id_t, user_t)
  `AXI_TYPEDEF_AR_CHAN_T(mst_ar_chan_t, mst_addr_t, id_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(r_chan_t, data_t, id_t, user_t)
  `AXI_TYPEDEF_REQ_T(slv_req_t, slv_aw_chan_t, w_chan_t, slv_ar_chan_t)
  `AXI_TYPEDEF_REQ_T(mst_req_t, mst_aw_chan_t, w_chan_t, mst_ar_chan_t)
  `AXI_TYPEDEF_RESP_T(resp_t, b_chan_t, r_chan_t)

  slv_req_t  slv_req;
  mst_req_t  mst_req;
  resp_t     slv_resp, mst_resp;

  `AXI_ASSIGN_TO_REQ(slv_req, slv)
  `AXI_ASSIGN_FROM_RESP(slv, slv_resp)

  `AXI_ASSIGN_FROM_REQ(mst, mst_req)
  `AXI_ASSIGN_TO_RESP(mst_resp, mst)

  axi_modify_address #(
    .slv_req_t  ( slv_req_t  ), // request type slave port
    .mst_addr_t ( mst_addr_t ), // address type of master port
    .mst_req_t  ( mst_req_t  ), // request type master port
    .resp_t     ( resp_t     )  // response type of both ports
  ) i_axi_modify_address (
  // slave port
    .slv_req_i     ( slv_req  ),
    .slv_resp_o    ( slv_resp ),
  // master port
    .mst_req_o     ( mst_req  ),
    .mst_resp_i    ( mst_resp ),
    .mst_aw_addr_i,
    .mst_ar_addr_i
  );

// pragma translate_off
`ifndef VERILATOR
  initial begin
    assert(AXI_SLV_PORT_ADDR_WIDTH > 0);
    assert(AXI_MST_PORT_ADDR_WIDTH > 0);
    assert(AXI_DATA_WIDTH > 0);
    assert(AXI_ID_WIDTH > 0);
  end
`endif
// pragma translate_on
endmodule
