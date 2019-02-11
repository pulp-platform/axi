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
// AXI Data Downsize Conversion.
// Connects a wide master to a narrower slave.

import axi_pkg::*;

module axi_data_downsize #(
  parameter int unsigned MST_DATA_WIDTH = 64,
  parameter int unsigned SLV_DATA_WIDTH = 64
) (
  input logic clk_i,
  input logic rst_ni,
  AXI_BUS.in  in,
  AXI_BUS.out out
);

`ifndef SYNTHESIS
  initial begin
    assert(MST_DATA_WIDTH > SLV_DATA_WIDTH);
  end
`endif

  localparam int unsigned MUL_FACTOR = SLV_DATA_WIDTH / MST_DATA_WIDTH;
  typedef logic [$clog2(MUL_FACTOR):0] mfactor_t;

  typedef logic [MST_DATA_WIDTH-1:0]   mst_data_t;
  typedef logic [MST_DATA_WIDTH/8-1:0] mst_strb_t;
  typedef logic [SLV_DATA_WIDTH-1:0]   slv_data_t;
  typedef logic [SLV_DATA_WIDTH/8-1:0] slv_strb_t;

  // --------------
  // READ
  // --------------

  enum logic [1:0] { R_IDLE,
                   R_SINGLE,
                   R_BURST } r_state_d, r_state_q;

  struct packed {
    addr_t    addr;
    len_t     len;
    size_t    size;
    burst_t   burst;

    mfactor_t cnt;
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

    in.r_id       = out.r_id;
    in.r_data     = '0;
    in.r_resp     = out.r_resp;
    in.r_last     = '0;
    in.r_user     = out.r_user;
    in.r_valid    = '0;
    out.r_ready   = '0;

    // Read
    case (r_state_q)
      R_SINGLE: begin
        in.r_data[ 8*r_req_q.addr[$clog2(MST_DATA_WIDTH/8)-1:0] +: SLV_DATA_WIDTH ] = out.r_data;
        in.r_last                                                                   = out.r_last;
        in.r_valid                                                                  = out.r_valid;
        out.r_ready                                                                 = in.r_ready;

        // End of transaction
        if (in.r_ready)
          r_state_d = R_IDLE;
      end
    endcase // case (r_state_q)

    // Might start new transaction whenever r_state_d == R_IDLE
    if (r_state_d == R_IDLE) begin
      // New write request
      if (in.ar_valid) begin
        if (in.ar_burst == BURST_INCR && |(in.ar_cache & CACHE_MODIFIABLE))
          r_state_d = R_BURST;
        else
          r_state_d = R_SINGLE;

        // Save beat
        r_req_d.addr  = in.ar_addr;
        r_req_d.len   = in.ar_len;
        r_req_d.size  = in.ar_size;
        r_req_d.burst = in.ar_burst;
      end // if (in.ar_valid)
    end // if (r_state_d == R_IDLE)
  end

  // --------------
  // WRITE
  // --------------

  enum logic [1:0] { W_IDLE,
                   W_SINGLE,
                   W_BURST } w_state_d, w_state_q;

  struct packed {
    addr_t    addr;
    len_t     len;
    size_t    size;
    burst_t   burst;

    mfactor_t cnt;
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
    out.w_user    = in.w_user;
    out.w_valid   = '0;
    in.w_ready    = '0;

    in.b_id       = out.b_id;
    in.b_resp     = out.b_resp;
    in.b_user     = out.b_user;
    in.b_valid    = out.b_valid;
    out.b_ready   = in.b_ready;

    // Write
    case (w_state_q)
      W_SINGLE: begin
        out.w_data  = in.w_data[ 8*w_req_q.addr[$clog2(MST_DATA_WIDTH/8)-1:0] +: SLV_DATA_WIDTH ];
        out.w_strb  = in.w_strb[   w_req_q.addr[$clog2(MST_DATA_WIDTH/8)-1:0] +: SLV_DATA_WIDTH/8];
        out.w_last  = in.w_last;
        out.w_valid = in.w_valid;
        in.w_ready  = out.w_ready;

        // End of transaction
        if (in.w_ready)
          w_state_d = W_IDLE;
      end
    endcase // case (w_state_q)

    // Might start new transaction whenever w_state_d == W_IDLE
    if (w_state_d == W_IDLE) begin
      // New write request
      if (in.aw_valid) begin
        if (in.aw_burst == BURST_INCR && |(in.aw_cache & CACHE_MODIFIABLE))
          w_state_d = W_BURST;
        else
          w_state_d = W_SINGLE;

        // Save beat
        w_req_d.addr  = in.aw_addr;
        w_req_d.len   = in.aw_len;
        w_req_d.size  = in.aw_size;
        w_req_d.burst = in.aw_burst;
      end // if (in.aw_valid)
    end // if (w_state_d == W_IDLE)
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
