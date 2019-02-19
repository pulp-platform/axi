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
// File          : axi_data_upsize.sv
// Author        : Matheus Cavalcante <matheusd@iis.ee.ethz.ch>
// Created       : 31.01.2019
//
// Copyright (C) 2019 ETH Zurich, University of Bologna
// All rights reserved.
//
// Description:
// AXI Data Upsize Conversion.
// Connects a narrow master to a wider slave.

import axi_pkg::*;

module axi_data_upsize #(
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
    assert(MST_DATA_WIDTH < SLV_DATA_WIDTH);
  end
`endif

  // --------------
  // DEFINITIONS
  // --------------

  localparam int unsigned MUL_FACTOR = $clog2(SLV_DATA_WIDTH / MST_DATA_WIDTH);
  typedef logic [MUL_FACTOR:0]         mfactor_t;

  typedef logic [MST_DATA_WIDTH-1:0]     mst_data_t;
  typedef logic [MST_DATA_WIDTH/8-1:0]   mst_strb_t;
  typedef mst_data_t [2**MUL_FACTOR-1:0] slv_data_t;
  typedef mst_strb_t [2**MUL_FACTOR-1:0] slv_strb_t;

  function automatic addr_t align_addr(addr_t addr);
    addr_t retval                        = addr;
    retval[$clog2(SLV_DATA_WIDTH/8)-1:0] = '0;
    return retval;
  endfunction // align_addr


  // --------------
  // READ
  // --------------

  enum logic [1:0] { R_IDLE,
                   R_READ,
                   R_SERIALIZE } r_state_d, r_state_q;

  struct packed {
    id_t     ar_id;
    addr_t   ar_addr;
    len_t    ar_len;
    size_t   ar_size;
    burst_t  ar_burst;
    logic    ar_lock;
    cache_t  ar_cache;
    prot_t   ar_prot;
    qos_t    ar_qos;
    region_t ar_region;
    user_t   ar_user;
    logic    ar_valid;

    logic    serialize;
  } r_req_d, r_req_q;

  always_comb begin
    // Maintain state
    r_state_d     = r_state_q;
    r_req_d       = r_req_q;

    // AR Channel
    out.ar_id     = r_req_q.ar_id;
    out.ar_addr   = r_req_q.ar_addr;
    out.ar_len    = r_req_q.serialize ? (r_req_q.ar_len >> MUL_FACTOR) : 0; // Un-serializable beats are split into individual requests
    out.ar_size   = r_req_q.ar_size;
    out.ar_burst  = r_req_q.ar_burst;
    out.ar_lock   = r_req_q.ar_lock;
    out.ar_cache  = r_req_q.ar_cache;
    out.ar_prot   = r_req_q.ar_prot;
    out.ar_qos    = r_req_q.ar_qos;
    out.ar_region = r_req_q.ar_region;
    out.ar_user   = r_req_q.ar_user;
    out.ar_valid  = r_req_q.ar_valid;
    in.ar_ready   = '0;

    in.r_id       = out.r_id;
    in.r_data     = '0;
    in.r_resp     = out.r_resp;
    in.r_last     = '0;
    in.r_user     = '0; // Due to data serialization/merging, no user data is forwarded
    in.r_valid    = '0;
    out.r_ready   = '0;

    // FSM
    case (r_state_q)
      R_READ: begin

      end

      R_SERIALIZE: begin

      end
    endcase // case (r_state_q)

    // Can start new request whenever r_state_d is IDLE
    if (r_state_d == R_IDLE)
      // New write request
      if (in.ar_valid) begin
        r_state_d         = R_READ;

        // Save beat
        r_req_d.ar_addr   = in.ar_addr;
        r_req_d.ar_len    = in.ar_len;
        r_req_d.ar_size   = in.ar_size;
        r_req_d.ar_burst  = in.ar_burst;
        r_req_d.ar_lock   = in.ar_lock;
        r_req_d.ar_cache  = in.ar_cache;
        r_req_d.ar_prot   = in.ar_prot;
        r_req_d.ar_qos    = in.ar_qos;
        r_req_d.ar_region = in.ar_region;
        r_req_d.ar_user   = in.ar_user;
        r_req_d.ar_valid  = in.ar_valid;

        // Can we serialize the slave responses?
        if (in.ar_burst == BURST_INCR && |(in.ar_cache & CACHE_MODIFIABLE))
          r_req_d.serialize = (in.ar_size == $clog2(MST_DATA_WIDTH/8)); // No support for narrow bursts
        else
          r_req_d.serialize = 1'b0;

        // Acknowledge this request
        // NOTE: Acknowledgment regardless of an answer
        // on the slave side?
        in.ar_ready         = 1'b1;
      end // if (in.ar_valid)
  end

  // --------------
  // WRITE
  // --------------

  enum logic [1:0] { W_IDLE,
                   W_MERGE,
                   W_WRITE } w_state_d, w_state_q;

  struct packed {
    id_t       aw_id;
    addr_t     aw_addr;
    len_t      aw_len;
    size_t     aw_size;
    burst_t    aw_burst;
    logic      aw_lock;
    cache_t    aw_cache;
    prot_t     aw_prot;
    qos_t      aw_qos;
    region_t   aw_region;
    user_t     aw_user;
    logic      aw_valid;

    slv_data_t w_data;
    slv_strb_t w_strb;

    logic      merging;
  } w_req_d, w_req_q;

  always_comb begin
    // Maintain state
    w_state_d     = w_state_q;
    w_req_d       = w_req_q;

    // AW Channel
    out.aw_id     = w_req_q.aw_id;
    out.aw_addr   = w_req_q.aw_addr;
    out.aw_len    = w_req_q.merging ? (w_req_q.aw_len >> MUL_FACTOR) : 0; // Un-mergeable burts are split into individual beats
    out.aw_size   = w_req_q.aw_size;
    out.aw_burst  = w_req_q.aw_burst;
    out.aw_lock   = w_req_q.aw_lock;
    out.aw_cache  = w_req_q.aw_cache;
    out.aw_prot   = w_req_q.aw_prot;
    out.aw_qos    = w_req_q.aw_qos;
    out.aw_region = w_req_q.aw_region;
    out.aw_user   = w_req_q.aw_user;
    out.aw_valid  = w_req_q.aw_valid;
    in.aw_ready   = '0;

    // W Channel
    out.w_data    = w_req_q.w_data;
    out.w_strb    = w_req_q.w_strb;
    out.w_last    = '0;
    out.w_user    = '0; // Due to data serialization/merging, no user data is forwarded
    out.w_valid   = '0;
    in.w_ready    = '0;

    // B Channel
    // No latency
    in.b_id       = out.b_id;
    in.b_resp     = out.b_resp;
    in.b_user     = out.b_user;
    in.b_valid    = out.b_valid;
    out.b_ready   = in.b_ready;

    // Issue write beat
    if (w_state_q == W_WRITE) begin
      out.w_valid = 1'b1;

      // Send w_last if finished merging or at the end of every beat
      out.w_last  = (w_req_q.aw_len == '1) || !w_req_q.merging;

      if (out.w_ready) begin
        w_req_d.w_data = '0;
        w_req_d.w_strb = '0;
        w_state_d      = (w_req_q.aw_len == '1) ? W_IDLE : W_MERGE;
      end
    end // if (w_state_q == W_WRITE)

    // Can accept data whenever w_state_d is MERGE
    if (w_state_d == W_MERGE) begin
      // Got a grant on the AW channel
      if (out.aw_ready)
        w_req_d.aw_valid = 1'b0;

      // Ready for more data
      in.w_ready = 1'b1;

      if (in.w_valid) begin
        // Lane steering
        automatic integer lane = w_req_q.aw_addr[$clog2(SLV_DATA_WIDTH/8)-1:$clog2(MST_DATA_WIDTH/8)];
        w_req_d.w_data[lane]   = in.w_data;
        w_req_d.w_strb[lane]   = in.w_strb;

        w_req_d.aw_len         = w_req_q.aw_len - 1;
        w_req_d.aw_addr        = w_req_q.aw_addr + (1 << w_req_q.aw_size);
      end

      if (w_req_q.merging) begin
        if ((align_addr(w_req_d.aw_addr) != align_addr(w_req_q.aw_addr)) // Filled up one word
          || w_req_d.aw_len == '1)                                       // Burst finished
          w_state_d = W_WRITE;
      end else begin
        w_state_d = W_WRITE;

        // If not finished with this burst, trigger another request on AW
        if (in.w_valid && (w_req_d.aw_len != '1))
          w_req_d.aw_valid = 1'b1;
      end
    end

    // Can start new request whenever w_state_d is IDLE
    if (w_state_d == W_IDLE)
      // New write request
      if (in.aw_valid) begin
        w_state_d         = W_MERGE;

        // Save beat
        w_req_d.aw_addr   = in.aw_addr;
        w_req_d.aw_len    = in.aw_len;
        w_req_d.aw_size   = in.aw_size;
        w_req_d.aw_burst  = in.aw_burst;
        w_req_d.aw_lock   = in.aw_lock;
        w_req_d.aw_cache  = in.aw_cache;
        w_req_d.aw_prot   = in.aw_prot;
        w_req_d.aw_qos    = in.aw_qos;
        w_req_d.aw_region = in.aw_region;
        w_req_d.aw_user   = in.aw_user;
        w_req_d.aw_valid  = in.aw_valid;

        // Can we merge the master requests?
        if (in.aw_burst == BURST_INCR && |(in.aw_cache & CACHE_MODIFIABLE))
          w_req_d.merging = (in.aw_size == $clog2(MST_DATA_WIDTH/8)); // No support for narrow bursts
        else
          w_req_d.merging = 1'b0;

        // Acknowledge this request
        // NOTE: Acknowledgment regardless of an answer
        // on the slave side?
        in.aw_ready       = 1'b1;
      end // if (in.aw_valid)
  end

  // --------------
  // REGISTERS
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

endmodule // axi_data_upsize
