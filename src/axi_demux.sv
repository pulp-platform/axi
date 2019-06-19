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

// Purely combinatorial demultiplexer for AXI channels.  Change the select input (`sel_i`) only when
// there are no transactions in-flight!
module axi_demux #(
  parameter type req_t = logic,
  parameter type resp_t = logic,
  parameter int unsigned NrMst = 0,
  localparam int unsigned SelWidth = $clog2(NrMst)
) (
  input  req_t                slv_req,
  output resp_t               slv_resp,
  output req_t  [NrMst-1:0]   mst_req,
  input  resp_t [NrMst-1:0]   mst_resp,
  input  logic [SelWidth-1:0] sel_i
);

  for (genvar i = 0; i < NrMst; i++) begin : gen_demux_mst_req
    always_comb begin
      if (i == sel_i) begin
        mst_req[i] = slv_req;
      end else begin
        mst_req[i].aw_valid = 1'b0;
        mst_req[i].w_valid = 1'b0;
        mst_req[i].b_ready = 1'b0;
        mst_req[i].ar_valid = 1'b0;
        mst_req[i].r_ready = 1'b0;
      end
    end
  end

  assign slv_resp = mst_resp[sel_i];

endmodule
