// Copyright (c) 2019 ETH Zurich, University of Bologna
//
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

`include "axi/assign.svh"
`include "axi/typedef.svh"

// Purely combinatorial bypass for AXI modules.  Change the bypass enable (`bypass_i`) only when
// no transactions are in flight!
module axi_bypass_wrap #(
  parameter int unsigned ADDR_WIDTH = 0,
  parameter int unsigned DATA_WIDTH = 0,
  parameter int unsigned ID_WIDTH = 0,
  parameter int unsigned USER_WIDTH = 0
) (
  AXI_BUS.Slave   slv,
  AXI_BUS.Master  module_mst,
  AXI_BUS.Slave   module_slv,
  AXI_BUS.Master  mst,

  input  logic    bypass_i
);

  typedef logic [ADDR_WIDTH-1:0] addr_t;
  typedef logic [DATA_WIDTH-1:0] data_t;
  typedef logic [ID_WIDTH-1:0] id_t;
  typedef logic [DATA_WIDTH/8-1:0] strb_t;
  typedef logic [USER_WIDTH-1:0] user_t;
  `AXI_TYPEDEF_AW_CHAN_T(aw_chan_t, addr_t, id_t, user_t);
  `AXI_TYPEDEF_W_CHAN_T(w_chan_t, data_t, strb_t, user_t);
  `AXI_TYPEDEF_B_CHAN_T(b_chan_t, id_t, user_t);
  `AXI_TYPEDEF_AR_CHAN_T(ar_chan_t, addr_t, id_t, user_t);
  `AXI_TYPEDEF_R_CHAN_T(r_chan_t, data_t, id_t, user_t);
  `AXI_TYPEDEF_REQ_T(req_t, aw_chan_t, w_chan_t, ar_chan_t);
  `AXI_TYPEDEF_RESP_T(resp_t, b_chan_t, r_chan_t);

  req_t  slv_req,  module_mst_req,  module_slv_req,  mst_req;
  resp_t slv_resp, module_mst_resp, module_slv_resp, mst_resp;

  `AXI_ASSIGN_TO_REQ(slv_req, slv);
  `AXI_ASSIGN_FROM_RESP(slv, slv_resp);

  `AXI_ASSIGN_FROM_REQ(module_mst, module_mst_req);
  `AXI_ASSIGN_TO_RESP(module_mst_resp, module_mst);

  `AXI_ASSIGN_TO_REQ(module_slv_req, module_slv);
  `AXI_ASSIGN_FROM_RESP(module_slv, module_slv_resp);

  `AXI_ASSIGN_FROM_REQ(mst, mst_req);
  `AXI_ASSIGN_TO_RESP(mst_resp, mst);

  axi_bypass #(
    .req_t  (req_t),
    .resp_t (resp_t)
  ) i_wrapped (
    .slv_req,
    .slv_resp,
    .module_mst_req,
    .module_mst_resp,
    .module_slv_req,
    .module_slv_resp,
    .mst_req,
    .mst_resp,
    .bypass_i
  );

endmodule
