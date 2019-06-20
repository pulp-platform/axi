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

// Simple AXI Address Width Converter that truncates addresses when converting down or extends
// addresses by a configurable offset when converting up.
module axi_address_width_converter #(
  parameter type slv_req_t = logic,
  parameter type mst_req_t = logic,
  parameter type resp_t = logic,
  // Address offset when extending
  parameter longint unsigned AddrOffset = 0
) (
  input  slv_req_t  slv_req,
  output resp_t     slv_resp,

  output mst_req_t  mst_req,
  input  resp_t     mst_resp
);

  localparam int unsigned AW_SLV = $bits(slv_req.aw.addr);
  localparam int unsigned AW_MST = $bits(mst_req.aw.addr);

  // Feed response channels through.
  assign slv_resp = mst_resp;

  if (AW_SLV > AW_MST) begin : gen_truncate
    always_comb begin
      mst_req = slv_req;
      mst_req.aw.addr = slv_req.aw.addr[AW_MST-1:0];
      mst_req.ar.addr = slv_req.ar.addr[AW_MST-1:0];
    end

  end else if (AW_SLV < AW_MST) begin : gen_extend
    always_comb begin
      mst_req = slv_req;
      mst_req.aw.addr[AW_SLV-1:0] = slv_req.aw.addr;
      mst_req.ar.addr[AW_SLV-1:0] = slv_req.ar.addr;
      mst_req.aw.addr[AW_MST-1:AW_SLV] = AddrOffset[AW_MST-AW_SLV-1:0];
      mst_req.ar.addr[AW_MST-1:AW_SLV] = AddrOffset[AW_MST-AW_SLV-1:0];
    end

  end else begin : gen_feedthrough
    assign mst_req = slv_req;
  end

  // Assumptions and assertions
  `ifndef VERILATOR
  // pragma translate_off
  // Parameters
  initial begin
    assert ($bits(slv_req.aw.addr) == $bits(slv_req.ar.addr))
      else $fatal(1, "Width of AR and AW on slave interface does not match!");
    assert ($bits(mst_req.aw.addr) == $bits(mst_req.ar.addr))
      else $fatal(1, "Width of AR and AW on master interface does not match!");
  end
  // pragma translate_on
  `endif

endmodule
