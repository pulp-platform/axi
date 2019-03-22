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
// Author: Matheus Cavalcante <matheusd@iis.ee.ethz.ch>
//
// Description:
// AXI Data Downsize Conversion.
// Connects a narrow master to a wider slave.

import axi_pkg::*;

module axi_data_downsize #(
  parameter int unsigned ADDR_WIDTH = 64,
  parameter int unsigned SI_DATA_WIDTH = 64,
  parameter int unsigned MI_DATA_WIDTH = 64,
  parameter int unsigned ID_WIDTH = 4,
  parameter int unsigned USER_WIDTH = 1,
  parameter int unsigned NR_OUTSTANDING = 1,
  // Dependent parameters, do not change!
  parameter type addr_t = logic[ADDR_WIDTH-1:0],
  parameter type si_data_t = logic[SI_DATA_WIDTH-1:0],
  parameter type si_strb_t = logic[SI_DATA_WIDTH/8-1:0],
  parameter type mi_data_t = logic[MI_DATA_WIDTH-1:0],
  parameter type mi_strb_t = logic[MI_DATA_WIDTH/8-1:0],
  parameter type id_t = logic[ID_WIDTH-1:0],
  parameter type user_t = logic[USER_WIDTH-1:0]
) (
  input  logic      clk_i,
  input  logic      rst_ni,

  // SLAVE INTERFACE

  input  id_t       in_aw_id,
  input  addr_t     in_aw_addr,
  input  len_t      in_aw_len,
  input  size_t     in_aw_size,
  input  burst_t    in_aw_burst,
  input  logic      in_aw_lock,
  input  cache_t    in_aw_cache,
  input  prot_t     in_aw_prot,
  input  qos_t      in_aw_qos,
  input  region_t   in_aw_region,
  input  atop_t     in_aw_atop,
  input  user_t     in_aw_user,
  input  logic      in_aw_valid,
  output logic      in_aw_ready,

  input  si_data_t  in_w_data,
  input  si_strb_t  in_w_strb,
  input  logic      in_w_last,
  input  user_t     in_w_user,
  input  logic      in_w_valid,
  output logic      in_w_ready,

  output id_t       in_b_id,
  output resp_t     in_b_resp,
  output user_t     in_b_user,
  output logic      in_b_valid,
  input  logic      in_b_ready,

  input  id_t       in_ar_id,
  input  addr_t     in_ar_addr,
  input  len_t      in_ar_len,
  input  size_t     in_ar_size,
  input  burst_t    in_ar_burst,
  input  logic      in_ar_lock,
  input  cache_t    in_ar_cache,
  input  prot_t     in_ar_prot,
  input  qos_t      in_ar_qos,
  input  region_t   in_ar_region,
  input  user_t     in_ar_user,
  input  logic      in_ar_valid,
  output logic      in_ar_ready,

  output id_t       in_r_id,
  output si_data_t  in_r_data,
  output resp_t     in_r_resp,
  output logic      in_r_last,
  output user_t     in_r_user,
  output logic      in_r_valid,
  input  logic      in_r_ready,

  // MASTER INTERFACE

  output id_t       out_aw_id,
  output addr_t     out_aw_addr,
  output len_t      out_aw_len,
  output size_t     out_aw_size,
  output burst_t    out_aw_burst,
  output logic      out_aw_lock,
  output cache_t    out_aw_cache,
  output prot_t     out_aw_prot,
  output qos_t      out_aw_qos,
  output region_t   out_aw_region,
  output atop_t     out_aw_atop,
  output user_t     out_aw_user,
  output logic      out_aw_valid,
  input  logic      out_aw_ready,

  output mi_data_t  out_w_data,
  output mi_strb_t  out_w_strb,
  output logic      out_w_last,
  output user_t     out_w_user,
  output logic      out_w_valid,
  input  logic      out_w_ready,

  input  id_t       out_b_id,
  input  resp_t     out_b_resp,
  input  user_t     out_b_user,
  input  logic      out_b_valid,
  output logic      out_b_ready,

  output id_t       out_ar_id,
  output addr_t     out_ar_addr,
  output len_t      out_ar_len,
  output size_t     out_ar_size,
  output burst_t    out_ar_burst,
  output logic      out_ar_lock,
  output cache_t    out_ar_cache,
  output prot_t     out_ar_prot,
  output qos_t      out_ar_qos,
  output region_t   out_ar_region,
  output user_t     out_ar_user,
  output logic      out_ar_valid,
  input  logic      out_ar_ready,

  input  id_t       out_r_id,
  input  mi_data_t  out_r_data,
  input  resp_t     out_r_resp,
  input  logic      out_r_last,
  input  user_t     out_r_user,
  input  logic      out_r_valid,
  output logic      out_r_ready
);

`ifndef SYNTHESIS
  initial begin
    assert(SI_DATA_WIDTH > MI_DATA_WIDTH);
  end
`endif

  // --------------
  // DEFINITIONS
  // --------------

  localparam addr_t MI_BYTES = MI_DATA_WIDTH/8;
  localparam addr_t MI_BYTE_MASK = MI_BYTES - 1;

  localparam addr_t SI_BYTES = SI_DATA_WIDTH/8;
  localparam addr_t SI_BYTE_MASK = SI_BYTES - 1;

  // Type for indexing which FSM handles each outstanding transaction
  typedef logic [$clog2(NR_OUTSTANDING)-1:0] tr_id_t;

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
  } channel_ax_t;

  typedef struct packed {
    mi_data_t   data;
    mi_strb_t   strb;
    logic       last;
    user_t      user;
    logic       valid;
  } mi_channel_w_t;

  typedef struct packed {
    si_data_t   data;
    si_strb_t   strb;
    logic       last;
    user_t      user;
    logic       valid;
  } si_channel_w_t;

  typedef struct packed {
    id_t        id;
    mi_data_t   data;
    resp_t      resp;
    logic       last;
    user_t      user;
    logic       valid;
  } mi_channel_r_t;

  typedef struct packed {
    id_t        id;
    si_data_t   data;
    resp_t      resp;
    logic       last;
    user_t      user;
    logic       valid;
  } si_channel_r_t;

  function automatic addr_t align_addr(addr_t unaligned_addr, size_t size);
    return unaligned_addr & ~((1 << size) - 1);
  endfunction // align_addr

  // Length of burst after downsizing
  typedef logic [$clog2(SI_BYTES/MI_BYTES)+7:0] full_len_t;

  // --------------
  // MULTIPLEXER
  // --------------

  channel_ax_t   [NR_OUTSTANDING-1:0]         ar_in;
  logic [NR_OUTSTANDING-1:0]                  ar_ready_in;

  mi_channel_r_t [NR_OUTSTANDING-1:0]         r_out;
  logic [NR_OUTSTANDING-1:0]                  r_ready_out;

  si_channel_r_t [NR_OUTSTANDING-1:0]         r_in;
  logic [NR_OUTSTANDING-1:0]                  r_ready_in;
  tr_id_t                                     r_in_idx;
  logic [NR_OUTSTANDING-1:0]                  r_in_req;

generate
  if (NR_OUTSTANDING >= 2) begin
    rrarbiter #(
      .NUM_REQ ( NR_OUTSTANDING )
    ) i_rrarbiter_r_in (
      .clk_i,
      .rst_ni,
      .flush_i ( 1'b0           ),
      .en_i    ( |r_in_req      ),
      .req_i   ( r_in_req       ),
      .ack_o   ( /* unused   */ ),
      .vld_o   ( /* unused   */ ),
      .idx_o   ( r_in_idx       )
    );
  end else begin // if (NR_OUTSTANDING >= 2)
    assign r_in_idx = 1'b0;
  end // else: !if(NR_OUTSTANDING >= 2)
endgenerate

  channel_ax_t   [NR_OUTSTANDING-1:0]         ar_out;
  logic [NR_OUTSTANDING-1:0]                  ar_ready_out;
  tr_id_t                                     ar_out_idx;
  logic [NR_OUTSTANDING-1:0]                  ar_out_req;

generate
  if (NR_OUTSTANDING >= 2) begin
    rrarbiter #(
      .NUM_REQ ( NR_OUTSTANDING )
    ) i_rrarbiter_ar_out (
      .clk_i,
      .rst_ni,
      .flush_i ( 1'b0           ),
      .en_i    ( |ar_out_req    ),
      .req_i   ( ar_out_req     ),
      .ack_o   ( /* unused   */ ),
      .vld_o   ( /* unused   */ ),
      .idx_o   ( ar_out_idx     )
    );
  end else begin // if (NR_OUTSTANDING >= 2)
    assign ar_out_idx = 1'b0;
  end // else: !if(NR_OUTSTANDING >= 2)
endgenerate

  always_comb begin: mux
    // Default values
    ar_in        = '0;
    r_out        = '0;

    in_ar_ready  = 1'b0;
    r_ready_in   = '0;
    ar_ready_out = '0;
    out_r_ready  = 1'b0;

    // REQUEST SIGNALS
    for (int tr = 0; tr < NR_OUTSTANDING; tr++) begin
      r_in_req[tr]   = r_in[tr].valid;
      ar_out_req[tr] = ar_out[tr].valid;
    end

    // INPUT SIGNALS
    for (int tr = 0; tr < NR_OUTSTANDING; tr++) begin
      ar_in[tr].id     = in_ar_id;
      ar_in[tr].addr   = in_ar_addr;
      ar_in[tr].len    = in_ar_len;
      ar_in[tr].size   = in_ar_size;
      ar_in[tr].burst  = in_ar_burst;
      ar_in[tr].lock   = in_ar_lock;
      ar_in[tr].cache  = in_ar_cache;
      ar_in[tr].prot   = in_ar_prot;
      ar_in[tr].qos    = in_ar_qos;
      ar_in[tr].region = in_ar_region;
      ar_in[tr].user   = in_ar_user;
      ar_in[tr].valid  = in_ar_valid && (in_ar_id % NR_OUTSTANDING == tr);
      if (in_ar_id % NR_OUTSTANDING == tr)
        in_ar_ready   = ar_ready_in[tr];

      r_out[tr].id    = out_r_id;
      r_out[tr].data  = out_r_data;
      r_out[tr].resp  = out_r_resp;
      r_out[tr].last  = out_r_last;
      r_out[tr].user  = out_r_user;
      r_out[tr].valid = out_r_valid && (out_r_id % NR_OUTSTANDING == tr);
      if (out_r_id % NR_OUTSTANDING == tr)
        out_r_ready = r_ready_out[tr];
    end

    // OUTPUT SIGNALS
    out_ar_id                = ar_out[ar_out_idx].id;
    out_ar_addr              = ar_out[ar_out_idx].addr;
    out_ar_len               = ar_out[ar_out_idx].len;
    out_ar_size              = ar_out[ar_out_idx].size;
    out_ar_burst             = ar_out[ar_out_idx].burst;
    out_ar_lock              = ar_out[ar_out_idx].lock;
    out_ar_cache             = ar_out[ar_out_idx].cache;
    out_ar_prot              = ar_out[ar_out_idx].prot;
    out_ar_qos               = ar_out[ar_out_idx].qos;
    out_ar_region            = ar_out[ar_out_idx].region;
    out_ar_user              = ar_out[ar_out_idx].user;
    out_ar_valid             = ar_out[ar_out_idx].valid;
    ar_ready_out[ar_out_idx] = out_ar_ready;

    in_r_id                  = r_in[r_in_idx].id;
    in_r_data                = r_in[r_in_idx].data;
    in_r_resp                = r_in[r_in_idx].resp;
    in_r_last                = r_in[r_in_idx].last;
    in_r_user                = r_in[r_in_idx].user;
    in_r_valid               = r_in[r_in_idx].valid;
    r_ready_in[r_in_idx]     = in_r_ready;
  end

  // --------------
  // READ
  // --------------

  // There is an identical FSM for each possible outstanding transaction
  generate
    for (genvar tr = 0; tr < NR_OUTSTANDING; tr++) begin: req_fsm

      enum logic [1:0] { R_IDLE,
                         R_PASSTHROUGH,
                         R_INCR_DOWNSIZE,
                         R_SPLIT_INCR_DOWNSIZE } r_state_d, r_state_q;

      struct packed {
        channel_ax_t   ar;
        si_channel_r_t r;

        full_len_t     len;
        size_t         size;
      } r_req_d, r_req_q;

      always_comb begin
        // Maintain state
        r_state_d     = r_state_q;
        r_req_d       = r_req_q;

        // AR Channel
        ar_out[tr].id     = r_req_q.ar.id;
        ar_out[tr].addr   = r_req_q.ar.addr;
        ar_out[tr].len    = r_req_q.ar.len;
        ar_out[tr].size   = r_req_q.ar.size;
        ar_out[tr].burst  = r_req_q.ar.burst;
        ar_out[tr].lock   = r_req_q.ar.lock;
        ar_out[tr].cache  = r_req_q.ar.cache;
        ar_out[tr].prot   = r_req_q.ar.prot;
        ar_out[tr].qos    = r_req_q.ar.qos;
        ar_out[tr].region = r_req_q.ar.region;
        ar_out[tr].user   = r_req_q.ar.user;
        ar_out[tr].valid  = r_req_q.ar.valid;
        ar_ready_in[tr]   = 1'b0;

        // R Channel
        r_in[tr].id       = r_req_q.r.id;
        r_in[tr].data     = r_req_q.r.data;
        r_in[tr].resp     = r_req_q.r.resp;
        r_in[tr].last     = r_req_q.r.last;
        r_in[tr].user     = r_req_q.r.user;
        r_in[tr].valid    = r_req_q.r.valid;
        r_ready_out[tr]   = 1'b0;

        // Got a grant on the AR channel
        if (ar_out[tr].valid && ar_ready_out[tr])
          r_req_d.ar.valid = 1'b0;

        case (r_state_q)
          R_PASSTHROUGH, R_INCR_DOWNSIZE, R_SPLIT_INCR_DOWNSIZE: begin
            // Got a grant on the R channel
            if (r_in[tr].valid && r_ready_in[tr])
              r_req_d.r = '0;

            // Request was accepted
            if (!r_req_q.ar.valid) begin
              // Ready to accept more data
              if (!r_in[tr].valid || (r_in[tr].valid && r_ready_in[tr])) begin
                r_ready_out[tr] = 1'b1;

                if (r_out[tr].valid) begin
                  automatic addr_t mi_offset = r_req_q.ar.addr[$clog2(MI_BYTES)-1:0];
                  automatic addr_t si_offset = r_req_q.ar.addr[$clog2(SI_BYTES)-1:0];
                  automatic addr_t size_mask = (1 << r_req_q.ar.size) - 1;

                  // Lane steering
                  for (int b = 0; b < SI_BYTES; b++)
                    if ((b >= si_offset) &&
                        (b - si_offset < (1 << r_req_q.size)) &&
                        (b + mi_offset - si_offset < MI_BYTES)) begin
                      r_req_d.r.data[8 * b +: 8] = r_out[tr].data[8 * (b + mi_offset - si_offset) +: 8];
                    end

                  r_req_d.len     = r_req_q.len - 1;
                  r_req_d.ar.len  = r_req_q.ar.len - 1;
                  r_req_d.ar.addr = (r_req_q.ar.addr & ~size_mask) + (1 << r_req_q.ar.size);
                  r_req_d.r.last  = (r_req_q.len == 0);
                  r_req_d.r.id    = r_out[tr].id;

                  // Forward user data
                  if (r_state_q == R_PASSTHROUGH)
                    r_req_d.r.user = r_out[tr].user;

                  case (r_state_q)
                    R_PASSTHROUGH:
                      // Forward data as soon as we can
                      r_req_d.r.valid = 1'b1;

                    R_INCR_DOWNSIZE, R_SPLIT_INCR_DOWNSIZE:
                      // Forward when the burst is finished, or when a word was filled up
                      if (r_req_q.len == 0 || (align_addr(r_req_d.ar.addr, r_req_q.size) != align_addr(r_req_q.ar.addr, r_req_q.size)))
                        r_req_d.r.valid = 1'b1;
                  endcase // case (r_state_q)

                  // Trigger another burst request, if needed
                  if (r_state_q == R_SPLIT_INCR_DOWNSIZE)
                    // Finished current burst, but whole transaction hasn't finished
                    if (r_req_q.ar.len == '0 && r_req_q.len != '0) begin
                      r_req_d.ar.valid = 1'b1;
                      r_req_d.ar.len   = (r_req_d.len <= 255) ? r_req_d.len : 255;
                    end
                end // if (r_out[tr].valid)
              end // if (!r_in[tr].valid || (r_in[tr].valid && r_ready_in[tr]))
            end // if (!r_req_d.ar.valid)

            if (r_in[tr].valid && r_ready_in[tr])
              if (r_req_q.len == '1)
                r_state_d = R_IDLE;
          end // case: R_PASSTHROUGH, R_INCR_DOWNSIZE, R_SPLIT_INCR_DOWNSIZE
        endcase // case (r_state_q)

        // Can start a new request as soon as r_state_d is R_IDLE
        if (r_state_d == R_IDLE) begin
          // Reset channels
          r_req_d.ar  = '0;
          r_req_d.r   = '0;

          // Ready
          ar_ready_in[tr] = 1'b1;

          // New write request
          if (ar_in[tr].valid) begin
            // Default state
            r_state_d         = R_PASSTHROUGH;

            // Save beat
            r_req_d.ar.id     = ar_in[tr].id;
            r_req_d.ar.addr   = ar_in[tr].addr;
            r_req_d.ar.size   = ar_in[tr].size;
            r_req_d.ar.burst  = ar_in[tr].burst;
            r_req_d.ar.len    = ar_in[tr].len;
            r_req_d.ar.lock   = ar_in[tr].lock;
            r_req_d.ar.cache  = ar_in[tr].cache;
            r_req_d.ar.prot   = ar_in[tr].prot;
            r_req_d.ar.qos    = ar_in[tr].qos;
            r_req_d.ar.region = ar_in[tr].region;
            r_req_d.ar.user   = ar_in[tr].user;
            r_req_d.ar.valid  = 1'b1;

            r_req_d.len       = ar_in[tr].len;
            r_req_d.size      = ar_in[tr].size;

            if (|(ar_in[tr].cache & CACHE_MODIFIABLE))
              case (ar_in[tr].burst)
                BURST_INCR: begin
                  // Evaluate downsize ratio
                  automatic addr_t size_mask  = (1 << ar_in[tr].size) - 1;
                  automatic addr_t conv_ratio = ((1 << ar_in[tr].size) + MI_BYTES - 1) / MI_BYTES;

                  // Evaluate output burst length
                  automatic addr_t align_adj  = (ar_in[tr].addr & size_mask & ~MI_BYTE_MASK) / MI_BYTES;
                  r_req_d.len                 = (ar_in[tr].len + 1) * conv_ratio - align_adj - 1;

                  if (conv_ratio != 1) begin
                    r_req_d.ar.size   = $clog2(MI_BYTES);

                    if (r_req_d.len <= 255) begin
                      r_state_d      = R_INCR_DOWNSIZE;
                      r_req_d.ar.len = r_req_d.len;
                    end else begin
                      r_state_d      = R_SPLIT_INCR_DOWNSIZE;
                      r_req_d.ar.len = 255 - align_adj;
                    end
                  end // if (conv_ratio != 1)
                end // case: BURST_INCR
              endcase // case (ar_in[tr].burst)
          end // if (ar_in[tr].valid)
        end
      end

      // --------------
      // REGISTERS
      // --------------

      always_ff @(posedge clk_i or negedge rst_ni) begin
        if (~rst_ni) begin
          r_state_q <= R_IDLE;
          r_req_q   <= '0;
        end else begin
          r_state_q <= r_state_d;
          r_req_q   <= r_req_d;
        end
      end

    end // block: req_fsm
  endgenerate

  // --------------
  // WRITE
  // --------------

  enum logic [1:0] { W_IDLE,
                     W_PASSTHROUGH,
                     W_INCR_DOWNSIZE,
                     W_SPLIT_INCR_DOWNSIZE } w_state_d, w_state_q;

  struct packed {
    channel_ax_t    aw;
    si_channel_w_t  w;

    full_len_t      len;
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
    out_w_data    = '0;
    out_w_strb    = '0;
    out_w_last    = '0;
    out_w_user    = '0;
    out_w_valid   = '0;
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
      W_PASSTHROUGH, W_INCR_DOWNSIZE, W_SPLIT_INCR_DOWNSIZE: begin
        // Request was accepted
        if (!w_req_q.aw.valid) begin
          if (w_req_q.w.valid) begin
            automatic addr_t mi_offset = w_req_q.aw.addr[$clog2(MI_BYTES)-1:0];
            automatic addr_t si_offset = w_req_q.aw.addr[$clog2(SI_BYTES)-1:0];

            // Valid output
            out_w_valid                = 1'b1;
            out_w_last                 = w_req_q.w.last && (w_req_q.len == 0);

            // Forward user data
            if (w_state_q == W_PASSTHROUGH)
              out_w_user = w_req_q.w.user;

            // Serialization
            for (int b = 0; b < SI_BYTES; b++)
              if ((b >= si_offset) &&
                  (b - si_offset < (1 << w_req_q.aw.size)) &&
                  (b + mi_offset - si_offset < MI_BYTES)) begin
                out_w_data[8 * (b + mi_offset - si_offset) +: 8] = w_req_q.w.data[8 * b +: 8];
                out_w_strb[b + mi_offset - si_offset]            = w_req_q.w.strb[b];
              end
          end // if (w_req_q.w.valid)

          // Acknowledgement
          if (out_w_ready && out_w_valid) begin
            automatic addr_t size_mask = (1 << w_req_q.aw.size) - 1;

            w_req_d.len                = w_req_q.len - 1;
            w_req_d.aw.len             = w_req_q.aw.len - 1;
            w_req_d.aw.addr            = (w_req_q.aw.addr & ~size_mask) + (1 << w_req_q.aw.size);

            case (w_state_q)
              W_PASSTHROUGH:
                w_req_d.w.valid = 1'b0;

              W_INCR_DOWNSIZE, W_SPLIT_INCR_DOWNSIZE:
                if (w_req_q.len == 0 || (align_addr(w_req_d.aw.addr, w_req_q.size) != align_addr(w_req_q.aw.addr, w_req_q.size)))
                  w_req_d.w.valid = 1'b0;
            endcase // case (w_state_q)

            // Trigger another burst request, if needed
            if (w_state_q == W_SPLIT_INCR_DOWNSIZE)
              // Finished current burst, but whole transaction hasn't finished
              if (w_req_q.aw.len == '0 && w_req_q.len != '0) begin
                w_req_d.aw.valid  = 1'b1;
                w_req_d.aw.len    = (w_req_d.len <= 255) ? w_req_d.len : 255;
              end

            if (w_req_q.len == 0)
              w_state_d = W_IDLE;
          end // if (out_w_ready && out_w_valid)

          // Ready if we consumed a whole word
          in_w_ready = ~w_req_d.w.valid;

          // Accept a new word
          if (in_w_valid && in_w_ready) begin
            w_req_d.w.data  = in_w_data;
            w_req_d.w.strb  = in_w_strb;
            w_req_d.w.user  = in_w_user;
            w_req_d.w.last  = in_w_last;
            w_req_d.w.valid = 1'b1;
          end
        end // if (!w_req_d.aw.valid)
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
      if (in_aw_valid && in_aw_ready) begin
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

        // Do nothing
        if (|(in_aw_cache & CACHE_MODIFIABLE))
          case (in_aw_burst)
            BURST_INCR: begin
              // Evaluate downsize ratio
              automatic addr_t size_mask  = (1 << in_aw_size) - 1;
              automatic addr_t conv_ratio = ((1 << in_aw_size) + MI_BYTES - 1) / MI_BYTES;

              // Evaluate output burst length
              automatic addr_t align_adj  = (in_aw_addr & size_mask & ~MI_BYTE_MASK) / MI_BYTES;
              w_req_d.len                 = (in_aw_len + 1) * conv_ratio - align_adj - 1;

              if (conv_ratio != 1) begin
                w_req_d.aw.size   = $clog2(MI_BYTES);

                if (w_req_d.len <= 255) begin
                  w_state_d      = W_INCR_DOWNSIZE;
                  w_req_d.aw.len = w_req_d.len;
                end else begin
                  w_state_d      = W_SPLIT_INCR_DOWNSIZE;
                  w_req_d.aw.len = 255 - align_adj;
                end
              end // if (conv_ratio != 1)
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
      w_state_q <= W_IDLE;
      w_req_q   <= '0;
    end else begin
      w_state_q <= w_state_d;
      w_req_q   <= w_req_d;
    end
  end

endmodule // axi_data_downsize
