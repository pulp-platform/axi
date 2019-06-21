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

// Purely combinatorial multiplexer for AXI channels.  Change the select input (`sel_i`) only when
// there are no transactions in-flight!
module axi_mux #(
  parameter type req_t = logic,
  parameter type resp_t = logic,
  parameter int unsigned NrSlv = 0,
  localparam int unsigned SelWidth = $clog2(NrSlv)
) (
  input  req_t  [NrSlv-1:0]   slv_req,
  output resp_t [NrSlv-1:0]   slv_resp,
  output req_t                mst_req,
  input  resp_t               mst_resp,
  input  logic [SelWidth-1:0] sel_i
);

  for (genvar i = 0; i < NrSlv; i++) begin : gen_demux_slv_resp
    always_comb begin
      if (i == sel_i) begin
        slv_resp[i] = mst_resp;
      end else begin
        slv_resp[i] = 'x;
        slv_resp[i].aw_ready = 1'b0;
        slv_resp[i].ar_ready = 1'b0;
        slv_resp[i].w_ready = 1'b0;
        slv_resp[i].b_valid = 1'b0;
        slv_resp[i].r_valid = 1'b0;
      end
    end
  end

  assign mst_req = slv_req[sel_i];

endmodule
