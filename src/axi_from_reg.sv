// Copyright 2024 ETH Zurich and University of Bologna.
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
// - Paul Scheffler <paulsc@iis.ee.ethz.ch>

/// A simple Regbus to AXI4 adapter. Blocks until response (B/R) is received.
/// Data width must match in both types! Address is truncated or zero-extended.
/// Sends requests with ID 0 and user signals 0.
module axi_from_reg #(
  /// Datawidth of both incoming Regbus and outgoing AXI4.
  parameter int unsigned DataWidth = 0,
  /// Cache signal assigned to Ax requests.
  parameter axi_pkg::cache_t AxiCache = axi_pkg::CACHE_MODIFIABLE,
  /// Incoming Regbus request type.
  parameter type reg_req_t = logic,
  /// Incoming Regbus response type.
  parameter type reg_rsp_t = logic,
  /// Outgoing AXI4 request type.
  parameter type axi_req_t = logic,
  /// Incoming AXI4 response type.
  parameter type axi_rsp_t = logic
) (
  input  logic     clk_i,
  input  logic     rst_ni,
  input  reg_req_t reg_req_i,
  output reg_rsp_t reg_rsp_o,
  output axi_req_t axi_req_o,
  input  axi_rsp_t axi_rsp_i
);
  `include "common_cells/registers.svh"

  // Set request pending flags on handshakes to block further requests until response.
  // Clear request pending flags (with in-cycle precedence over set!) on response.
  logic ar_pending_q, aw_pending_q, w_pending_q;

  `FFLARNC(ar_pending_q, axi_rsp_i.ar_ready, axi_req_o.ar_valid, axi_rsp_i.r_valid, 1'b0, clk_i, rst_ni)
  `FFLARNC(aw_pending_q, axi_rsp_i.aw_ready, axi_req_o.aw_valid, axi_rsp_i.b_valid, 1'b0, clk_i, rst_ni)
  `FFLARNC(w_pending_q,  axi_rsp_i.w_ready,  axi_req_o.w_valid,  axi_rsp_i.b_valid, 1'b0, clk_i, rst_ni)

  // AR: Forward locked-in read requests
  assign axi_req_o.ar = '{
    addr:   reg_req_i.addr,
    size:   $clog2(DataWidth/8),
    burst:  axi_pkg::BURST_INCR,
    cache:  AxiCache,
    default: '0
  };

  assign axi_req_o.r_ready  = reg_req_i.valid & ~reg_req_i.write;
  assign axi_req_o.ar_valid = axi_req_o.r_ready & ~ar_pending_q;

  // AW: Forward locked-in write requests
  assign axi_req_o.aw = '{
    addr:   reg_req_i.addr,
    size:   $clog2(DataWidth/8),
    burst:  axi_pkg::BURST_INCR,
    cache:  AxiCache,
    default: '0
  };

  assign axi_req_o.b_ready  = reg_req_i.valid & reg_req_i.write;
  assign axi_req_o.aw_valid = axi_req_o.b_ready & ~aw_pending_q;

  // W: lock control flow to AW requests
  assign axi_req_o.w = '{
    data:   reg_req_i.wdata,
    strb:   reg_req_i.wstrb,
    last:   1'b1,
    default:  '0
  };

  assign axi_req_o.w_valid = axi_req_o.b_ready & ~w_pending_q;

  // Regbus response
  assign reg_rsp_o = '{
    rdata:  axi_rsp_i.r.data,
    error:  (reg_req_i.write ? axi_rsp_i.b.resp : axi_rsp_i.r.resp) == axi_pkg::RESP_OKAY,
    ready:  axi_rsp_i.r_valid | axi_rsp_i.b_valid
  };

endmodule
