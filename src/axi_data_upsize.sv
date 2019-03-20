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
  parameter int unsigned ADDR_WIDTH = 64,
  parameter int unsigned SI_DATA_WIDTH = 64,
  parameter int unsigned MI_DATA_WIDTH = 64,
  parameter int unsigned ID_WIDTH = 4,
  parameter int unsigned USER_WIDTH = 1,
  // Dependent parameters, do not change!
  parameter type addr_t = logic[ADDR_WIDTH-1:0],
  parameter type id_t = logic[ID_WIDTH-1:0],
  parameter type user_t = logic[USER_WIDTH-1:0]
) (
  input logic                        clk_i,
  input logic                        rst_ni,

  // SLAVE INTERFACE

  input id_t                         in_aw_id,
  input addr_t                       in_aw_addr,
  input len_t                        in_aw_len,
  input size_t                       in_aw_size,
  input burst_t                      in_aw_burst,
  input logic                        in_aw_lock,
  input cache_t                      in_aw_cache,
  input prot_t                       in_aw_prot,
  input qos_t                        in_aw_qos,
  input region_t                     in_aw_region,
  input atop_t                       in_aw_atop,
  input user_t                       in_aw_user,
  input logic                        in_aw_valid,
  output logic                       in_aw_ready,

  input logic [SI_DATA_WIDTH-1:0]    in_w_data,
  input logic [SI_DATA_WIDTH/8-1:0]  in_w_strb,
  input logic                        in_w_last,
  input user_t                       in_w_user,
  input logic                        in_w_valid,
  output logic                       in_w_ready,

  output id_t                        in_b_id,
  output resp_t                      in_b_resp,
  output user_t                      in_b_user,
  output logic                       in_b_valid,
  input logic                        in_b_ready,

  input id_t                         in_ar_id,
  input addr_t                       in_ar_addr,
  input len_t                        in_ar_len,
  input size_t                       in_ar_size,
  input burst_t                      in_ar_burst,
  input logic                        in_ar_lock,
  input cache_t                      in_ar_cache,
  input prot_t                       in_ar_prot,
  input qos_t                        in_ar_qos,
  input region_t                     in_ar_region,
  input user_t                       in_ar_user,
  input logic                        in_ar_valid,
  output logic                       in_ar_ready,

  output id_t                        in_r_id,
  output logic [SI_DATA_WIDTH-1:0]   in_r_data,
  output resp_t                      in_r_resp,
  output logic                       in_r_last,
  output user_t                      in_r_user,
  output logic                       in_r_valid,
  input logic                        in_r_ready,

  // MASTER INTERFACE

  output id_t                        out_aw_id,
  output addr_t                      out_aw_addr,
  output len_t                       out_aw_len,
  output size_t                      out_aw_size,
  output burst_t                     out_aw_burst,
  output logic                       out_aw_lock,
  output cache_t                     out_aw_cache,
  output prot_t                      out_aw_prot,
  output qos_t                       out_aw_qos,
  output region_t                    out_aw_region,
  output atop_t                      out_aw_atop,
  output user_t                      out_aw_user,
  output logic                       out_aw_valid,
  input logic                        out_aw_ready,

  output logic [MI_DATA_WIDTH-1:0]   out_w_data,
  output logic [MI_DATA_WIDTH/8-1:0] out_w_strb,
  output logic                       out_w_last,
  output user_t                      out_w_user,
  output logic                       out_w_valid,
  input logic                        out_w_ready,

  input id_t                         out_b_id,
  input resp_t                       out_b_resp,
  input user_t                       out_b_user,
  input logic                        out_b_valid,
  output logic                       out_b_ready,

  output id_t                        out_ar_id,
  output addr_t                      out_ar_addr,
  output len_t                       out_ar_len,
  output size_t                      out_ar_size,
  output burst_t                     out_ar_burst,
  output logic                       out_ar_lock,
  output cache_t                     out_ar_cache,
  output prot_t                      out_ar_prot,
  output qos_t                       out_ar_qos,
  output region_t                    out_ar_region,
  output user_t                      out_ar_user,
  output logic                       out_ar_valid,
  input logic                        out_ar_ready,

  input id_t                         out_r_id,
  input logic [MI_DATA_WIDTH-1:0]    out_r_data,
  input resp_t                       out_r_resp,
  input logic                        out_r_last,
  input user_t                       out_r_user,
  input logic                        out_r_valid,
  output logic                       out_r_ready
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

  typedef struct packed {
    id_t        id;
    addr_t      addr;
    len_t       len;
    size_t      size;
    burst_t     burst;
    logic       lock;
    cache_t     cache;
    prot_t      prot;
    qos_t       qos;
    region_t    region;
    atop_t      atop;   // Only defined on the AW channel.
    user_t      user;
    logic       valid;
    logic       ready;
  } channel_ax_t;

  typedef struct packed {
    mi_data_t   data;
    mi_strb_t   strb;
    logic       last;
    user_t      user;
    logic       valid;
    logic       ready;
  } mi_channel_w_t;

  typedef struct packed {
    si_data_t   data;
    si_strb_t   strb;
    logic       last;
    user_t      user;
    logic       valid;
    logic       ready;
  } si_channel_w_t;

  typedef struct packed {
    id_t        id;
    mi_data_t   data;
    resp_t      resp;
    logic       last;
    user_t      user;
    logic       valid;
    logic       ready;
  } mi_channel_r_t;

  typedef struct packed {
    id_t        id;
    si_data_t   data;
    resp_t      resp;
    logic       last;
    user_t      user;
    logic       valid;
    logic       ready;
  } si_channel_r_t;

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
    channel_ax_t    ar;
    mi_channel_r_t  r;

    len_t           len;
    size_t          size;
  } r_req_d, r_req_q;

  always_comb begin
    // Maintain state
    r_state_d     = r_state_q;
    r_req_d       = r_req_q;

    // AR Channel
    out_ar_id     = r_req_q.ar.id;
    out_ar_addr   = r_req_q.ar.addr;
    out_ar_len    = r_req_q.ar.len;
    out_ar_size   = r_req_q.ar.size;
    out_ar_burst  = r_req_q.ar.burst;
    out_ar_lock   = r_req_q.ar.lock;
    out_ar_cache  = r_req_q.ar.cache;
    out_ar_prot   = r_req_q.ar.prot;
    out_ar_qos    = r_req_q.ar.qos;
    out_ar_region = r_req_q.ar.region;
    out_ar_user   = r_req_q.ar.user;
    out_ar_valid  = r_req_q.ar.valid;
    in_ar_ready   = '0;

    // R Channel
    in_r_id       = r_req_q.r.id;
    in_r_data     = '0;
    in_r_resp     = r_req_q.r.resp;
    in_r_last     = '0;
    in_r_user     = '0; // Due do data serialization/merging, no user data is forwarded
    in_r_valid    = '0;
    out_r_ready   = '0;

    // Got a grant on the AR channel
    if (out_ar_valid && out_ar_ready)
      r_req_d.ar.valid = 1'b0;

    case (r_state_q)
      R_PASSTHROUGH, R_INCR_UPSIZE: begin
        // Request was accepted
        if (!r_req_q.ar.valid) begin
          if (r_req_q.r.valid) begin
            automatic addr_t mi_offset = r_req_q.ar.addr[$clog2(MI_BYTES)-1:0];
            automatic addr_t si_offset = r_req_q.ar.addr[$clog2(SI_BYTES)-1:0];

            // Valid output
            in_r_valid                 = 1'b1;
            in_r_last                  = r_req_q.r.last && (r_req_q.len == 0);

            // Serialization
            for (int b = 0; b < MI_BYTES; b++)
              if ((b >= mi_offset) &&
                        (b - mi_offset < (1 << r_req_q.size)) &&
                        (b + si_offset - mi_offset < SI_BYTES)) begin
                in_r_data[8 * (b + si_offset - mi_offset) +: 8] = r_req_q.r.data[8 * b +: 8];
              end

            // Acknowledgement
            if (in_r_ready) begin
              automatic addr_t size_mask = (1 << r_req_q.size) - 1;

              r_req_d.len                = r_req_q.len - 1;
              r_req_d.ar.addr            = (r_req_q.ar.addr & ~size_mask) + (1 << r_req_q.size);

              case (r_state_q)
                R_PASSTHROUGH:
                  r_req_d.r.valid = 1'b0;

                R_INCR_UPSIZE:
                  if (r_req_q.len == 0 || (align_addr(r_req_d.ar.addr) != align_addr(r_req_q.ar.addr)))
                    r_req_d.r.valid = 1'b0;
              endcase // case (r_state_q)

              if (r_req_q.len == 0)
                r_state_d = R_IDLE;
            end // if (in_r_ready)
          end // if (r_req_q.r.valid)

          // We consumed a whole word
          if (!r_req_d.r.valid) begin
            out_r_ready = 1'b1;

            // Accept a new word
            if (out_r_valid) begin
              r_req_d.r.id    = out_r_id;
              r_req_d.r.data  = out_r_data;
              r_req_d.r.resp  = out_r_resp;
              r_req_d.r.last  = out_r_last;
              r_req_d.r.valid = 1'b1;
            end
          end // if (r_req_d.r.valid)
        end // if (!r_req_d.ar.valid)
      end // case: R_PASSTHROUGH, R_INCR_UPSIZE
    endcase // case (r_state_q)

    // Can start a new request as soon as r_state_d is R_IDLE
    if (r_state_d == R_IDLE) begin
      // Reset channels
      r_req_d.ar  = '0;
      r_req_d.r   = '0;

      // Ready
      in_ar_ready = 1'b1;

      // New read request
      if (in_ar_valid) begin
        // Default state
        r_state_d         = R_PASSTHROUGH;

        // Save beat
        r_req_d.ar.id     = in_ar_id;
        r_req_d.ar.addr   = in_ar_addr;
        r_req_d.ar.size   = in_ar_size;
        r_req_d.ar.burst  = in_ar_burst;
        r_req_d.ar.len    = in_ar_len;
        r_req_d.ar.lock   = in_ar_lock;
        r_req_d.ar.cache  = in_ar_cache;
        r_req_d.ar.prot   = in_ar_prot;
        r_req_d.ar.qos    = in_ar_qos;
        r_req_d.ar.region = in_ar_region;
        r_req_d.ar.user   = in_ar_user;
        r_req_d.ar.valid  = 1'b1;

        r_req_d.len       = in_ar_len;
        r_req_d.size      = in_ar_size;

        if (|(in_ar_cache & CACHE_MODIFIABLE))
          case (in_ar_burst)
            BURST_INCR: begin
              // Evaluate output burst length
              automatic addr_t size_mask  = (1 << in_ar_size) - 1;

              automatic addr_t addr_start = align_addr(in_ar_addr);
              automatic addr_t addr_end   = align_addr((in_ar_addr & ~size_mask) + (in_ar_len << in_ar_size));

              r_req_d.ar.len              = (addr_end - addr_start) >> $clog2(MI_BYTES);
              r_req_d.ar.size             = $clog2(MI_BYTES);
              r_state_d                   = R_INCR_UPSIZE;
            end // case: BURST_INCR
          endcase // case (in_ar_burst)
      end // if (in_ar_valid)
    end
  end

  // --------------
  // WRITE
  // --------------

  enum logic [1:0] { W_IDLE,
                     W_PASSTHROUGH,
                     W_INCR_UPSIZE } w_state_d, w_state_q;

  struct packed {
    channel_ax_t    aw;
    mi_channel_w_t  w;

    len_t           len;
    size_t          size;
  } w_req_d, w_req_q;

  always_comb begin
    // Maintain state
    w_state_d     = w_state_q;
    w_req_d       = w_req_q;

    // AW Channel
    out_aw_id     = w_req_q.aw.id;
    out_aw_addr   = w_req_q.aw.addr;
    out_aw_len    = w_req_q.aw.len;
    out_aw_size   = w_req_q.aw.size;
    out_aw_burst  = w_req_q.aw.burst;
    out_aw_lock   = w_req_q.aw.lock;
    out_aw_cache  = w_req_q.aw.cache;
    out_aw_prot   = w_req_q.aw.prot;
    out_aw_qos    = w_req_q.aw.qos;
    out_aw_region = w_req_q.aw.region;
    out_aw_atop   = w_req_q.aw.atop;
    out_aw_user   = w_req_q.aw.user;
    out_aw_valid  = w_req_q.aw.valid;
    in_aw_ready   = '0;

    // W Channel
    out_w_data    = w_req_q.w.data;
    out_w_strb    = w_req_q.w.strb;
    out_w_last    = w_req_q.w.last;
    out_w_user    = '0; // Due to data serialization/merging, no user data is forwarded
    out_w_valid   = w_req_q.w.valid;
    in_w_ready    = '0;

    // B Channel
    // No latency
    in_b_id       = out_b_id;
    in_b_resp     = out_b_resp;
    in_b_user     = out_b_user;
    in_b_valid    = out_b_valid;
    out_b_ready   = in_b_ready;

    // Got a grant on the AW channel
    if (out_aw_valid && out_aw_ready)
      w_req_d.aw.valid = 1'b0;

    case (w_state_q)
      W_PASSTHROUGH, W_INCR_UPSIZE: begin
        // Got a grant on the W channel
        if (out_w_valid && out_w_ready)
          w_req_d.w = '0;

        // Request was accepted
        if (!w_req_q.aw.valid) begin
          // Ready if downstream interface is idle, or if it is ready
          in_w_ready  = ~out_w_valid || out_w_ready;

          if (in_w_valid && in_w_ready) begin
            automatic addr_t mi_offset = w_req_q.aw.addr[$clog2(MI_BYTES)-1:0];
            automatic addr_t si_offset = w_req_q.aw.addr[$clog2(SI_BYTES)-1:0];
            automatic addr_t size_mask = (1 << w_req_q.size) - 1;

            // Lane steering
            for (int b = 0; b < MI_BYTES; b++)
              if ((b >= mi_offset) &&
                        (b - mi_offset < (1 << w_req_q.size)) &&
                        (b + si_offset - mi_offset < SI_BYTES)) begin
                w_req_d.w.data[8 * b +: 8] = in_w_data[8 * (b + si_offset - mi_offset) +: 8];
                w_req_d.w.strb[b]          = in_w_strb[b + si_offset - mi_offset];
              end

            w_req_d.len     = w_req_q.len - 1;
            w_req_d.aw.addr = (w_req_q.aw.addr & ~size_mask) + (1 << w_req_q.size);
            w_req_d.w.last  = (w_req_q.len == 0);

            case (w_state_q)
              W_PASSTHROUGH:
                // Forward data as soon as we can
                w_req_d.w.valid = 1'b1;

              W_INCR_UPSIZE:
                // Forward when the burst is finished, or when a word was filled up
                if (w_req_q.len == 0 || (align_addr(w_req_d.aw.addr) != align_addr(w_req_q.aw.addr)))
                  w_req_d.w.valid = 1'b1;
            endcase // case (w_state_q)
          end // if (in_w_valid && in_w_ready)
        end // if (!w_req_d.aw.valid)

        if (out_w_valid && out_w_ready)
          if (w_req_q.len == '1)
            w_state_d = W_IDLE;
      end
    endcase // case (w_state_q)

    // Can start a new request as soon as w_state_d is W_IDLE
    if (w_state_d == W_IDLE) begin
      // Reset channels
      w_req_d.aw  = '0;
      w_req_d.w   = '0;

      // Ready
      in_aw_ready = 1'b1;

      // New write request
      if (in_aw_valid & in_aw_ready) begin
        // Default state
        w_state_d         = W_PASSTHROUGH;

        // Save beat
        w_req_d.aw.id     = in_aw_id;
        w_req_d.aw.addr   = in_aw_addr;
        w_req_d.aw.size   = in_aw_size;
        w_req_d.aw.burst  = in_aw_burst;
        w_req_d.aw.len    = in_aw_len;
        w_req_d.aw.lock   = in_aw_lock;
        w_req_d.aw.cache  = in_aw_cache;
        w_req_d.aw.prot   = in_aw_prot;
        w_req_d.aw.qos    = in_aw_qos;
        w_req_d.aw.region = in_aw_region;
        w_req_d.aw.atop   = in_aw_atop;
        w_req_d.aw.user   = in_aw_user;
        w_req_d.aw.valid  = 1'b1;

        w_req_d.len       = in_aw_len;
        w_req_d.size      = in_aw_size;

        if (|(in_aw_cache & CACHE_MODIFIABLE))
          case (in_aw_burst)
            BURST_INCR: begin
              // Evaluate output burst length
              automatic addr_t size_mask  = (1 << in_aw_size) - 1;

              automatic addr_t addr_start = align_addr(in_aw_addr);
              automatic addr_t addr_end   = align_addr((in_aw_addr & ~size_mask) + (in_aw_len << in_aw_size));

              w_req_d.aw.len              = (addr_end - addr_start) >> $clog2(MI_BYTES);
              w_req_d.aw.size             = $clog2(MI_BYTES);
              w_state_d                   = W_INCR_UPSIZE;
            end // case: BURST_INCR
          endcase // case (in_aw_burst)
      end // if (in_aw_valid)
    end
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
