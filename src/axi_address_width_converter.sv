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

// Simple AXI Address Width Converter:  When converting down, it first adds the signed offset input
// to the address and then truncates the upper bits.  When converting up, it first zero-extends the
// address and then adds the signed offset input.  Even when not converting address width, it adds
// the signed offset input.
module axi_address_width_converter #(
  parameter type slv_req_t = logic,
  parameter type mst_req_t = logic,
  parameter type resp_t = logic,
  parameter int unsigned OffsetWidth = 0, // must be set to the wider address width + 1
  localparam type offset_t = logic signed [OffsetWidth-1:0]
) (
  input  slv_req_t  slv_req,
  output resp_t     slv_resp,

  output mst_req_t  mst_req,
  input  resp_t     mst_resp,

  input  offset_t   offset_i
);

  localparam int unsigned AwSlv = $bits(slv_req.aw.addr);
  localparam int unsigned AwMst = $bits(mst_req.aw.addr);

  if (AwSlv > AwMst) begin : gen_downsize
    slv_req_t imed_req;
    // Add offset.
    axi_address_width_converter #(
      .slv_req_t    (slv_req_t),
      .mst_req_t    (slv_req_t),
      .resp_t       (resp_t),
      .OffsetWidth  (OffsetWidth)
    ) i_offset (
      .slv_req,
      .slv_resp,
      .mst_req  (imed_req),
      .mst_resp,
      .offset_i
    );
    // Truncate addresses.
    always_comb begin
      `AXI_SET_REQ(mst_req, imed_req);
      mst_req.aw.addr = imed_req.aw.addr[AwMst-1:0];
      mst_req.ar.addr = imed_req.ar.addr[AwMst-1:0];
    end

  end else if (AwSlv < AwMst) begin : gen_upsize
    mst_req_t imed_req;
    // Zero-extend addresses.
    always_comb begin
      `AXI_SET_REQ(imed_req, slv_req);
      imed_req.aw.addr[AwSlv-1:0] = slv_req.aw.addr;
      imed_req.ar.addr[AwSlv-1:0] = slv_req.ar.addr;
      imed_req.aw.addr[AwMst-1:AwSlv] = '0;
      imed_req.ar.addr[AwMst-1:AwSlv] = '0;
    end
    // Add offset.
    axi_address_width_converter #(
      .slv_req_t    (mst_req_t),
      .mst_req_t    (mst_req_t),
      .resp_t       (resp_t),
      .OffsetWidth  (OffsetWidth)
    ) i_offset (
      .slv_req  (imed_req),
      .slv_resp,
      .mst_req,
      .mst_resp,
      .offset_i
    );

  end else begin : gen_offset
    // Feed response channel through.
    assign slv_resp = mst_resp;

    // Add offset to request addresses.
    offset_t aw_addr, ar_addr;
    assign aw_addr = signed'({1'b0, slv_req.aw.addr}) + offset_i;
    assign ar_addr = signed'({1'b0, slv_req.ar.addr}) + offset_i;
    always_comb begin
      `AXI_SET_REQ(mst_req, slv_req);
      mst_req.aw.addr = unsigned'(aw_addr[AwMst-1:0]);
      mst_req.ar.addr = unsigned'(ar_addr[AwMst-1:0]);
    end
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
    assert (OffsetWidth == (AwMst + 1) || OffsetWidth == (AwSlv + 1))
      else $fatal(1, "Offset width must exceed the wider address by one, even if not using offsets!");
  end
  // pragma translate_on
  `endif

endmodule
