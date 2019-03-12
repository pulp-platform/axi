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
// Connects a wide master to a narrower slave.

import axi_pkg::*;

module axi_data_upsize #(
  parameter int unsigned MI_DATA_WIDTH = 64,
  parameter int unsigned SI_DATA_WIDTH = 64
) (
  input logic clk_i,
  input logic rst_ni,
  AXI_BUS.in  in,
  AXI_BUS.out out
);

`ifndef SYNTHESIS
  initial begin
    assert(SI_DATA_WIDTH < MI_DATA_WIDTH);
  end
`endif

  // --------------
  // DEFINITIONS
  // --------------

  localparam addr_t MI_BYTES = MI_DATA_WIDTH/8;
  localparam addr_t MI_BYTE_MASK = MI_BYTES - 1;
  typedef logic [MI_DATA_WIDTH-1:0] mi_data_t;
  typedef logic [MI_BYTES-1:0]      mi_strb_t;

  localparam addr_t SI_BYTES = SI_DATA_WIDTH/8;
  localparam addr_t SI_BYTE_MASK = SI_BYTES - 1;
  typedef logic [SI_DATA_WIDTH-1:0] si_data_t;
  typedef logic [SI_BYTES-1:0]      si_strb_t;

  function automatic addr_t align_addr(addr_t unaligned_addr);
    return unaligned_addr & ~MI_BYTE_MASK;
  endfunction // align_addr

  // --------------
  // READ
  // --------------

  enum logic [1:0] { R_IDLE,
                     R_PASSTHROUGH,
                     R_INCR_UPSIZE } r_state_d, r_state_q;

  struct packed {
    struct packed {
      id_t     id;
      addr_t   addr;
      len_t    len;
      size_t   size;
      burst_t  burst;
      logic    lock;
      cache_t  cache;
      prot_t   prot;
      qos_t    qos;
      region_t region;
      user_t   user;
      logic    valid;
    } ar;

    struct packed {
      id_t      id;
      mi_data_t data;
      resp_t    resp;
      logic     last;
      logic     valid;
    } r;

    size_t      size;
    len_t       len;
  } r_req_d, r_req_q;

  always_comb begin
    // Maintain state
    r_state_d     = r_state_q;
    r_req_d       = r_req_q;

    // AR Channel
    out.ar_id     = r_req_q.ar.id;
    out.ar_addr   = r_req_q.ar.addr;
    out.ar_len    = r_req_q.ar.len;
    out.ar_size   = r_req_q.ar.size;
    out.ar_burst  = r_req_q.ar.burst;
    out.ar_lock   = r_req_q.ar.lock;
    out.ar_cache  = r_req_q.ar.cache;
    out.ar_prot   = r_req_q.ar.prot;
    out.ar_qos    = r_req_q.ar.qos;
    out.ar_region = r_req_q.ar.region;
    out.ar_user   = r_req_q.ar.user;
    out.ar_valid  = r_req_q.ar.valid;
    in.ar_ready   = '0;

    // R Channel
    in.r_id       = r_req_q.r.id;
    in.r_data     = '0;
    in.r_resp     = r_req_q.r.resp;
    in.r_last     = '0;
    in.r_user     = '0; // Due do data serialization/merging, no user data is forwarded
    in.r_valid    = '0;
    out.r_ready   = '0;

    // Got a grant on the AR channel
    if (out.ar_valid & out.ar_ready)
      r_req_d.ar.valid = 1'b0;

    case (r_state_q)
      R_IDLE: begin
        // Reset channels
        r_req_d.ar = '0;
        r_req_d.r  = '0;
      end

      R_PASSTHROUGH, R_INCR_UPSIZE: begin
        if (r_req_q.r.valid) begin
          automatic addr_t mi_offset = r_req_q.ar.addr[$clog2(MI_BYTES)-1:0];
          automatic addr_t si_offset = r_req_q.ar.addr[$clog2(SI_BYTES)-1:0];
          automatic addr_t size_mask = (1 << r_req_q.size) - 1;

          // Valid output
          in.r_valid                 = 1'b1;
          in.r_last                  = r_req_q.r.last & (r_req_q.len == 0);

          // Serialization
          for (int b = 0; b < MI_BYTES; b++)
            if ((b >= mi_offset) &&
                (b - mi_offset < (1 << r_req_q.size)) &&
                (b + si_offset - mi_offset < SI_BYTES)) begin
              in.r_data[8 * (b + si_offset - mi_offset) +: 8] = r_req_q.r.data[8 * b +: 8];
            end

          // Acknowledgement
          if (in.r_ready) begin
            r_req_d.len     = r_req_q.len - 1;

            case (r_state_q)
              R_PASSTHROUGH: begin
                r_req_d.ar.addr = (r_req_q.ar.addr & ~size_mask) + (1 << r_req_q.size);
                r_req_d.r.valid = 1'b0;
              end

              R_INCR_UPSIZE: begin
                r_req_d.ar.addr = (r_req_q.ar.addr & ~size_mask) + (1 << r_req_q.size);

                if (r_req_q.len == 0 || (align_addr(r_req_d.ar.addr) != align_addr(r_req_q.ar.addr)))
                  r_req_d.r.valid = 1'b0;
              end
            endcase // case (r_state_q)

            if (r_req_q.len == 0) begin
              r_req_d.r.valid = 1'b0;
              r_state_d       = R_IDLE;
            end
          end // if (in.r_ready)
        end // if (r_req_q.r.valid)

        // If we are waiting for a word, ready
        // whenever downstream answers
        if (!r_req_q.r.valid)
          out.r_ready = out.r_valid;
        // Else, ready if the upstream interface is ready
        else
          out.r_ready = ~r_req_d.r.valid & out.r_valid;

        // Accept a new word
        if (out.r_ready & out.r_valid) begin
          r_req_d.r.id    = out.r_id;
          r_req_d.r.data  = out.r_data;
          r_req_d.r.resp  = out.r_resp;
          r_req_d.r.last  = out.r_last;
          r_req_d.r.valid = 1'b1;
        end
      end // case: R_PASSTHROUGH
    endcase // case (r_state_q)

    // Can start new request whenever r_state_d is IDLE
    if (r_state_d == R_IDLE) begin
      // New read request
      if (in.ar_valid) begin
        // Save beat
        r_req_d.ar.id     = in.ar_id;
        r_req_d.ar.addr   = in.ar_addr;
        r_req_d.ar.size   = in.ar_size;
        r_req_d.ar.burst  = in.ar_burst;
        r_req_d.ar.len    = in.ar_len;
        r_req_d.ar.lock   = in.ar_lock;
        r_req_d.ar.cache  = in.ar_cache;
        r_req_d.ar.prot   = in.ar_prot;
        r_req_d.ar.qos    = in.ar_qos;
        r_req_d.ar.region = in.ar_region;
        r_req_d.ar.user   = in.ar_user;
        r_req_d.ar.valid  = 1'b1;
        r_req_d.len       = in.ar_len;
        r_req_d.size      = in.ar_size;

        if (|(in.ar_cache & CACHE_MODIFIABLE)) begin
          case (in.ar_burst)
            BURST_INCR: begin
              // Evaluate output burst length
              automatic addr_t size_mask  = (1 << in.ar_size) - 1;

              automatic addr_t addr_start = align_addr(in.ar_addr);
              automatic addr_t addr_end   = align_addr((in.ar_addr & ~size_mask) + (in.ar_len << in.ar_size));

              r_req_d.ar.len              = (addr_end - addr_start) >> $clog2(MI_BYTES);
              r_req_d.ar.size             = $clog2(MI_BYTES);
              r_state_d                   = R_INCR_UPSIZE;
            end // case: BURST_INCR

            default:
              r_state_d = R_PASSTHROUGH;
          endcase // case (in.ar_burst)
        end else begin
          // Do nothing
          r_state_d = R_PASSTHROUGH;
        end

        // Acknowledge this request
        // NOTE: Acknowledgment regardless of an answer
        // on the slave side?
        in.ar_ready = 1'b1;
      end // if (in.ar_valid)
    end // if (r_state_d == R_IDLE)
  end

  // --------------
  // WRITE
  // --------------

  enum logic [1:0] { W_IDLE,
                     W_PASSTHROUGH,
                     W_INCR_UPSIZE } w_state_d, w_state_q;

  struct packed {
    struct packed {
      id_t     id;
      addr_t   addr;
      len_t    len;
      size_t   size;
      burst_t  burst;
      logic    lock;
      cache_t  cache;
      prot_t   prot;
      qos_t    qos;
      region_t region;
      atop_t   atop;
      user_t   user;
      logic    valid;
    } aw;

    struct packed {
      mi_data_t data;
      mi_strb_t strb;
      logic     last;
      logic     valid;
    } w;

    size_t      size;
    len_t       len;
  } w_req_d, w_req_q;

  always_comb begin
    // Maintain state
    w_state_d     = w_state_q;
    w_req_d       = w_req_q;

    // AW Channel
    out.aw_id     = w_req_q.aw.id;
    out.aw_addr   = w_req_q.aw.addr;
    out.aw_len    = w_req_q.aw.len;
    out.aw_size   = w_req_q.aw.size;
    out.aw_burst  = w_req_q.aw.burst;
    out.aw_lock   = w_req_q.aw.lock;
    out.aw_cache  = w_req_q.aw.cache;
    out.aw_prot   = w_req_q.aw.prot;
    out.aw_qos    = w_req_q.aw.qos;
    out.aw_region = w_req_q.aw.region;
    out.aw_atop   = w_req_q.aw.atop;
    out.aw_user   = w_req_q.aw.user;
    out.aw_valid  = w_req_q.aw.valid;
    in.aw_ready   = '0;

    // W Channel
    out.w_data    = w_req_q.w.data;
    out.w_strb    = w_req_q.w.strb;
    out.w_last    = w_req_q.w.last;
    out.w_user    = '0; // Due to data serialization/merging, no user data is forwarded
    out.w_valid   = w_req_q.w.valid;
    in.w_ready    = '0;

    // B Channel
    // No latency
    in.b_id       = out.b_id;
    in.b_resp     = out.b_resp;
    in.b_user     = out.b_user;
    in.b_valid    = out.b_valid;
    out.b_ready   = in.b_ready;

    // Got a grant on the AW channel
    if (out.aw_valid & out.aw_ready)
      w_req_d.aw.valid = 1'b0;

    // Got a grant on the W channel
    if (out.w_valid & out.w_ready)
      w_req_d.w = '0;

    case (w_state_q)
      W_IDLE: begin
        // Reset channels
        w_req_d.aw = '0;
        w_req_d.w  = '0;
      end

      W_PASSTHROUGH, W_INCR_UPSIZE: begin
        // If the downstream interface is idle,
        // ready whenever a new word arrives
        if (!out.w_valid)
          in.w_ready = in.w_valid;
        // Else, ready if the upstream interface is ready
        else
          in.w_ready = in.w_valid & out.w_ready;

        if (in.w_ready) begin
          automatic addr_t mi_offset = w_req_q.aw.addr[$clog2(MI_BYTES)-1:0];
          automatic addr_t si_offset = w_req_q.aw.addr[$clog2(SI_BYTES)-1:0];
          automatic addr_t size_mask = (1 << w_req_q.size) - 1;

          // Lane steering
          for (int b = 0; b < MI_BYTES; b++)
            if ((b >= mi_offset) &&
                (b - mi_offset < (1 << w_req_q.size)) &&
                (b + si_offset - mi_offset < SI_BYTES)) begin
              w_req_d.w.data[8 * b +: 8] = in.w_data[8 * (b + si_offset - mi_offset) +: 8];
              w_req_d.w.strb[b]          = in.w_strb[b + si_offset - mi_offset];
            end

          w_req_d.len     = w_req_q.len - 1;

          case (w_state_q)
            W_PASSTHROUGH: begin
              w_req_d.aw.addr = (w_req_q.aw.addr & ~size_mask) + (1 << w_req_q.size);

              // Forward data as soon as we can
              w_req_d.w.valid = 1'b1;
            end

            W_INCR_UPSIZE: begin
              w_req_d.aw.addr = (w_req_q.aw.addr & ~size_mask) + (1 << w_req_q.size);

              // Forward when the burst is finished, or when a word was filled up
              if (w_req_q.len == 0 || (align_addr(w_req_d.aw.addr) != align_addr(w_req_q.aw.addr)))
                w_req_d.w.valid = 1'b1;
            end
          endcase // case (w_state_q)

          if (w_req_q.len == 0) begin
            w_req_d.w.last = 1'b1;
            w_state_d      = W_IDLE;
          end
        end
      end
    endcase // case (w_state_q)

    // Can start new request whenever w_state_d is IDLE
    if (w_state_d == W_IDLE) begin
      // New write request
      if (in.aw_valid) begin
        // Save beat
        w_req_d.aw.id     = in.aw_id;
        w_req_d.aw.addr   = in.aw_addr;
        w_req_d.aw.size   = in.aw_size;
        w_req_d.aw.burst  = in.aw_burst;
        w_req_d.aw.len    = in.aw_len;
        w_req_d.aw.lock   = in.aw_lock;
        w_req_d.aw.cache  = in.aw_cache;
        w_req_d.aw.prot   = in.aw_prot;
        w_req_d.aw.qos    = in.aw_qos;
        w_req_d.aw.region = in.aw_region;
        w_req_d.aw.atop   = in.aw_atop;
        w_req_d.aw.user   = in.aw_user;
        w_req_d.aw.valid  = 1'b1;
        w_req_d.len       = in.aw_len;
        w_req_d.size      = in.aw_size;

        if (|(in.aw_cache & CACHE_MODIFIABLE)) begin
          case (in.aw_burst)
            BURST_INCR: begin
              // Evaluate output burst length
              automatic addr_t size_mask  = (1 << in.aw_size) - 1;

              automatic addr_t addr_start = align_addr(in.aw_addr);
              automatic addr_t addr_end   = align_addr((in.aw_addr & ~size_mask) + (in.aw_len << in.aw_size));

              w_req_d.aw.len              = (addr_end - addr_start) >> $clog2(MI_BYTES);
              w_req_d.aw.size             = $clog2(MI_BYTES);
              w_state_d                   = W_INCR_UPSIZE;
            end // case: BURST_INCR

            default:
              w_state_d = W_PASSTHROUGH;
          endcase // case (in.aw_burst)
        end else begin
          // Do nothing
          w_state_d = W_PASSTHROUGH;
        end

        // Acknowledge this request
        // NOTE: Acknowledgment regardless of an answer
        // on the slave side?
        in.aw_ready = 1'b1;
      end // if (in.aw_valid)
    end // if (w_state_d == W_IDLE)
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
