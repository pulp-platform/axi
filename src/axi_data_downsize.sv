// Copyright 2019 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// File          : axi_data_downsize.sv
// Author        : Matheus Cavalcante <matheusd@iis.ee.ethz.ch>
// Created       : 31.01.2019
//
// Copyright (C) 2019 ETH Zurich, University of Bologna
// All rights reserved.
//
// Description:
// AXI Data_downsize Conversion.
// Connects a wide master to a narrower slave.

import axi_pkg::*;

module axi_data_downsize #(
  parameter int unsigned MASTER_DATA_WIDTH = 64,
  parameter int unsigned SLAVE_DATA_WIDTH  = 64
) (
  input logic clk_i,
  input logic rst_ni,
  AXI_BUS.in  in,
  AXI_BUS.out out
);

`ifndef SYNTHESIS
  initial begin
    assert(MASTER_DATA_WIDTH > SLAVE_DATA_WIDTH);
  end
`endif

  localparam int unsigned MUL_FACTOR = SLAVE_DATA_WIDTH / MASTER_DATA_WIDTH;

  // --------------
  // READ
  // --------------

  enum logic { R_IDLE, R_MERGE }         r_state_d, r_state_q;
  struct packed {
    logic [$clog2(MUL_FACTOR)-1:0]       cnt;
  } r_req_d, r_req_q;

  always_comb begin
    // Maintain state
    r_state_d     = r_state_q;
    r_req_d       = r_req_q;

    // AXI assignments
    out.ar_id     = in.ar_id;
    out.ar_addr   = in.ar_addr;
    out.ar_len    = in.ar_len;
    out.ar_size   = in.ar_size;
    out.ar_burst  = in.ar_burst;
    out.ar_lock   = in.ar_lock;
    out.ar_cache  = in.ar_cache;
    out.ar_prot   = in.ar_prot;
    out.ar_qos    = in.ar_qos;
    out.ar_region = in.ar_region;
    out.ar_user   = in.ar_user;
    out.ar_valid  = in.ar_valid;
    in.ar_ready   = out.ar_ready;

    in.r_id       = '0;
    in.r_data     = '0;
    in.r_resp     = '0;
    in.r_last     = '0;
    in.r_user     = '0;
    in.r_valid    = '0;
    out.r_ready   = '0;

    // Read
    case (r_state_q)
      R_IDLE: begin
        // New read request
        if (in.ar_valid) begin
        end
      end // case: R_IDLE
    endcase // case (r_state_q)
  end

  // --------------
  // WRITE
  // --------------

  enum logic { W_IDLE, W_SERIALIZATION }   w_state_d, w_state_q;
  struct packed {
    logic [$clog2(MUL_FACTOR)-1:0]         cnt;
  } w_req_d, w_req_q;

  always_comb begin
    // Maintain state
    w_state_d     = w_state_q;
    w_req_d       = w_req_q;

    // AXI assignments
    out.aw_id     = in.aw_id;
    out.aw_addr   = in.aw_addr;
    out.aw_len    = in.aw_len;
    out.aw_size   = in.aw_size;
    out.aw_burst  = in.aw_burst;
    out.aw_lock   = in.aw_lock;
    out.aw_cache  = in.aw_cache;
    out.aw_prot   = in.aw_prot;
    out.aw_qos    = in.aw_qos;
    out.aw_region = in.aw_region;
    out.aw_user   = in.aw_user;
    out.aw_valid  = in.aw_valid;
    in.aw_ready   = out.aw_ready;

    out.w_data    = '0;
    out.w_strb    = '0;
    out.w_last    = '0;
    out.w_user    = '0;
    out.w_valid   = '0;
    in.w_ready    = '0;

    in.b_id       = '0;
    in.b_resp     = '0;
    in.b_user     = '0;
    in.b_valid    = '0;
    out.b_ready   = '0;

    // Write
    case (w_state_q)
      W_IDLE: begin
        // New write request
        if (in.aw_valid) begin
        end
      end
    endcase // case (w_state_q)
  end

  // --------------
  // REGISTER
  // --------------

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (~rst_ni) begin
      r_state_q <= R_IDLE;
      r_req_q   <= '0;

      w_state_q <= W_IDLE;
      w_req_q   <= '0;
    end else begin
      r_state_q <= r_state_d;
      r_req_q   <= r_req_d;

      w_state_q <= w_state_d;
      w_req_q   <= w_req_d;
    end
  end

endmodule // axi_data_downsize
