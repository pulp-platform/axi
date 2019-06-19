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

// Purely combinatorial bypass for AXI modules.  Change the bypass enable (`bypass_i`) only when
// no transactions are in flight!
module axi_bypass #(
  parameter type req_t = logic,
  parameter type resp_t = logic
) (
  input  req_t    slv_req,
  output resp_t   slv_resp,

  output req_t    module_mst_req,
  input  resp_t   module_mst_resp,

  input  req_t    module_slv_req,
  output resp_t   module_slv_resp,

  output req_t    mst_req,
  input  resp_t   mst_resp,

  input  logic    bypass_i
);

  req_t  internal_req;
  resp_t internal_resp;

  axi_demux #(
    .req_t  (req_t),
    .resp_t (resp_t),
    .NrMst  (2)
  ) i_demux (
    .slv_req  (slv_req),
    .slv_resp (slv_resp),
    .mst_req  ({internal_req,  module_mst_req}),
    .mst_resp ({internal_resp, module_mst_resp}),
    .sel_i    (bypass_i)
  );

  axi_mux #(
    .req_t  (req_t),
    .resp_t (resp_t),
    .NrSlv  (2)
  ) i_mux (
    .slv_req  ({internal_req,  module_slv_req}),
    .slv_resp ({internal_resp, module_slv_resp}),
    .mst_req  (mst_req),
    .mst_resp (mst_resp),
    .sel_i    (bypass_i)
  );

endmodule
