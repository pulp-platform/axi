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

  input  id_t       slv_aw_id,
  input  addr_t     slv_aw_addr,
  input  len_t      slv_aw_len,
  input  size_t     slv_aw_size,
  input  burst_t    slv_aw_burst,
  input  logic      slv_aw_lock,
  input  cache_t    slv_aw_cache,
  input  prot_t     slv_aw_prot,
  input  qos_t      slv_aw_qos,
  input  region_t   slv_aw_region,
  input  atop_t     slv_aw_atop,
  input  user_t     slv_aw_user,
  input  logic      slv_aw_valid,
  output logic      slv_aw_ready,

  input  si_data_t  slv_w_data,
  input  si_strb_t  slv_w_strb,
  input  logic      slv_w_last,
  input  user_t     slv_w_user,
  input  logic      slv_w_valid,
  output logic      slv_w_ready,

  output id_t       slv_b_id,
  output resp_t     slv_b_resp,
  output user_t     slv_b_user,
  output logic      slv_b_valid,
  input  logic      slv_b_ready,

  input  id_t       slv_ar_id,
  input  addr_t     slv_ar_addr,
  input  len_t      slv_ar_len,
  input  size_t     slv_ar_size,
  input  burst_t    slv_ar_burst,
  input  logic      slv_ar_lock,
  input  cache_t    slv_ar_cache,
  input  prot_t     slv_ar_prot,
  input  qos_t      slv_ar_qos,
  input  region_t   slv_ar_region,
  input  user_t     slv_ar_user,
  input  logic      slv_ar_valid,
  output logic      slv_ar_ready,

  output id_t       slv_r_id,
  output si_data_t  slv_r_data,
  output resp_t     slv_r_resp,
  output logic      slv_r_last,
  output user_t     slv_r_user,
  output logic      slv_r_valid,
  input  logic      slv_r_ready,

  // MASTER INTERFACE

  output id_t       mst_aw_id,
  output addr_t     mst_aw_addr,
  output len_t      mst_aw_len,
  output size_t     mst_aw_size,
  output burst_t    mst_aw_burst,
  output logic      mst_aw_lock,
  output cache_t    mst_aw_cache,
  output prot_t     mst_aw_prot,
  output qos_t      mst_aw_qos,
  output region_t   mst_aw_region,
  output atop_t     mst_aw_atop,
  output user_t     mst_aw_user,
  output logic      mst_aw_valid,
  input  logic      mst_aw_ready,

  output mi_data_t  mst_w_data,
  output mi_strb_t  mst_w_strb,
  output logic      mst_w_last,
  output user_t     mst_w_user,
  output logic      mst_w_valid,
  input  logic      mst_w_ready,

  input  id_t       mst_b_id,
  input  resp_t     mst_b_resp,
  input  user_t     mst_b_user,
  input  logic      mst_b_valid,
  output logic      mst_b_ready,

  output id_t       mst_ar_id,
  output addr_t     mst_ar_addr,
  output len_t      mst_ar_len,
  output size_t     mst_ar_size,
  output burst_t    mst_ar_burst,
  output logic      mst_ar_lock,
  output cache_t    mst_ar_cache,
  output prot_t     mst_ar_prot,
  output qos_t      mst_ar_qos,
  output region_t   mst_ar_region,
  output user_t     mst_ar_user,
  output logic      mst_ar_valid,
  input  logic      mst_ar_ready,

  input  id_t       mst_r_id,
  input  mi_data_t  mst_r_data,
  input  resp_t     mst_r_resp,
  input  logic      mst_r_last,
  input  user_t     mst_r_user,
  input  logic      mst_r_valid,
  output logic      mst_r_ready
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

  logic [NR_OUTSTANDING-1:0]               int_slv_ar_ready;
  assign slv_ar_ready = int_slv_ar_ready[slv_ar_id % NR_OUTSTANDING];

  logic [NR_OUTSTANDING-1:0]               int_mst_r_ready;
  assign mst_r_ready = int_mst_r_ready[mst_r_id % NR_OUTSTANDING];

  si_channel_r_t [NR_OUTSTANDING-1:0]      int_slv_r;
  logic [NR_OUTSTANDING-1:0]               int_slv_r_ready;
  logic [NR_OUTSTANDING-1:0]               int_slv_r_req;
  logic                                    int_slv_r_en_d, int_slv_r_en_q;
  tr_id_t                                  int_slv_r_idx;

  generate
    if (NR_OUTSTANDING >= 2) begin
      rrarbiter #(
        .NUM_REQ ( NR_OUTSTANDING ),
        .LOCK_IN ( 1'b1           )
      ) i_rrarbiter_r_slv (
        .clk_i,
        .rst_ni,
        .flush_i ( 1'b0           ),
        .en_i    ( int_slv_r_en_q ),
        .req_i   ( int_slv_r_req  ),
        .ack_o   ( /* unused   */ ),
        .vld_o   ( /* unused   */ ),
        .idx_o   ( int_slv_r_idx  )
      );
    end else begin // if (NR_OUTSTANDING >= 2)
      assign int_slv_r_idx = 1'b0;
    end // else: !if(NR_OUTSTANDING >= 2)
  endgenerate

  channel_ax_t [NR_OUTSTANDING-1:0]        int_mst_ar;
  logic [NR_OUTSTANDING-1:0]               int_mst_ar_ready;
  logic [NR_OUTSTANDING-1:0]               int_mst_ar_req;
  logic                                    int_mst_ar_en_d, int_mst_ar_en_q;
  tr_id_t                                  int_mst_ar_idx;

  generate
    if (NR_OUTSTANDING >= 2) begin
      rrarbiter #(
        .NUM_REQ ( NR_OUTSTANDING ),
        .LOCK_IN ( 1'b1           )
      ) i_rrarbiter_ar_mst (
        .clk_i,
        .rst_ni,
        .flush_i ( 1'b0            ),
        .en_i    ( int_mst_ar_en_q ),
        .req_i   ( int_mst_ar_req  ),
        .ack_o   ( /* unused    */ ),
        .vld_o   ( /* unused    */ ),
        .idx_o   ( int_mst_ar_idx  )
      );
    end else begin // if (NR_OUTSTANDING >= 2)
      assign int_mst_ar_idx = 1'b0;
    end // else: !if(NR_OUTSTANDING >= 2)
  endgenerate

  /* This multiplexes the requests from all the FSMs handling different
   * outstanding transactions into a single channel */

  always_comb begin: mux
    // Default values
    int_slv_r_ready  = '0;
    int_mst_ar_ready = '0;

    // OUTPUT SIGNALS
    mst_ar_id                        = int_mst_ar[int_mst_ar_idx].id;
    mst_ar_addr                      = int_mst_ar[int_mst_ar_idx].addr;
    mst_ar_len                       = int_mst_ar[int_mst_ar_idx].len;
    mst_ar_size                      = int_mst_ar[int_mst_ar_idx].size;
    mst_ar_burst                     = int_mst_ar[int_mst_ar_idx].burst;
    mst_ar_lock                      = int_mst_ar[int_mst_ar_idx].lock;
    mst_ar_cache                     = int_mst_ar[int_mst_ar_idx].cache;
    mst_ar_prot                      = int_mst_ar[int_mst_ar_idx].prot;
    mst_ar_qos                       = int_mst_ar[int_mst_ar_idx].qos;
    mst_ar_region                    = int_mst_ar[int_mst_ar_idx].region;
    mst_ar_user                      = int_mst_ar[int_mst_ar_idx].user;
    mst_ar_valid                     = int_mst_ar[int_mst_ar_idx].valid;
    int_mst_ar_ready[int_mst_ar_idx] = mst_ar_ready;

    slv_r_id                         = int_slv_r[int_slv_r_idx].id;
    slv_r_data                       = int_slv_r[int_slv_r_idx].data;
    slv_r_resp                       = int_slv_r[int_slv_r_idx].resp;
    slv_r_last                       = int_slv_r[int_slv_r_idx].last;
    slv_r_user                       = int_slv_r[int_slv_r_idx].user;
    slv_r_valid                      = int_slv_r[int_slv_r_idx].valid;
    int_slv_r_ready[int_slv_r_idx]   = slv_r_ready;

    // REQUEST SIGNALS
    for (int tr = 0; tr < NR_OUTSTANDING; tr++) begin
      int_slv_r_req[tr]  = int_slv_r[tr].valid;
      int_mst_ar_req[tr] = int_mst_ar[tr].valid;
    end

    // Disable arbitration if request wasn't acknowledged
    int_slv_r_en_d  = !(slv_r_valid && !slv_r_ready);
    int_mst_ar_en_d = !(mst_ar_valid && !mst_ar_ready);
  end // block: mux

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (~rst_ni) begin
      int_slv_r_en_q  <= 1'b0;
      int_mst_ar_en_q <= 1'b0;
    end else begin
      int_slv_r_en_q  <= int_slv_r_en_d;
      int_mst_ar_en_q <= int_mst_ar_en_d;
    end
  end

  // --------------
  // READ
  // --------------

  // There is an identical FSM for each possible outstanding transaction
  typedef enum logic [1:0] { R_IDLE,
                             R_PASSTHROUGH,
                             R_INCR_DOWNSIZE,
                             R_SPLIT_INCR_DOWNSIZE } r_state_t;

  generate
    for (genvar tr = 0; tr < NR_OUTSTANDING; tr++) begin: req_fsm

      r_state_t r_state_d, r_state_q;

      struct packed {
        channel_ax_t   ar;
        si_channel_r_t r;

        full_len_t     len;
        size_t         size;
      } r_req_d, r_req_q;

      always_comb begin
        // Maintain state
        r_state_d             = r_state_q;
        r_req_d               = r_req_q;

        // AR Channel
        int_mst_ar[tr]        = '0;
        int_mst_ar[tr].id     = r_req_q.ar.id;
        int_mst_ar[tr].addr   = r_req_q.ar.addr;
        int_mst_ar[tr].len    = r_req_q.ar.len;
        int_mst_ar[tr].size   = r_req_q.ar.size;
        int_mst_ar[tr].burst  = r_req_q.ar.burst;
        int_mst_ar[tr].lock   = r_req_q.ar.lock;
        int_mst_ar[tr].cache  = r_req_q.ar.cache;
        int_mst_ar[tr].prot   = r_req_q.ar.prot;
        int_mst_ar[tr].qos    = r_req_q.ar.qos;
        int_mst_ar[tr].region = r_req_q.ar.region;
        int_mst_ar[tr].user   = r_req_q.ar.user;
        int_mst_ar[tr].valid  = r_req_q.ar.valid;
        int_slv_ar_ready[tr]  = 1'b0;

        // R Channel
        int_slv_r[tr].id      = r_req_q.r.id;
        int_slv_r[tr].data    = r_req_q.r.data;
        int_slv_r[tr].resp    = r_req_q.r.resp;
        int_slv_r[tr].last    = r_req_q.r.last;
        int_slv_r[tr].user    = r_req_q.r.user;
        int_slv_r[tr].valid   = r_req_q.r.valid;
        int_mst_r_ready[tr]   = 1'b0;

        // Got a grant on the AR channel
        if (int_mst_ar[tr].valid && int_mst_ar_ready[tr])
          r_req_d.ar.valid = 1'b0;

        case (r_state_q)
          R_PASSTHROUGH, R_INCR_DOWNSIZE, R_SPLIT_INCR_DOWNSIZE: begin
            // Got a grant on the R channel
            if (int_slv_r[tr].valid && int_slv_r_ready[tr])
              r_req_d.r = '0;

            // Request was accepted
            if (!r_req_q.ar.valid) begin
              // Ready to accept more data
              if (!int_slv_r[tr].valid || (int_slv_r[tr].valid && int_slv_r_ready[tr])) begin
                int_mst_r_ready[tr] = 1'b1;

                if (mst_r_valid && (mst_r_id % NR_OUTSTANDING == tr)) begin
                  automatic addr_t mi_offset = r_req_q.ar.addr[$clog2(MI_BYTES)-1:0];
                  automatic addr_t si_offset = r_req_q.ar.addr[$clog2(SI_BYTES)-1:0];
                  automatic addr_t size_mask = (1 << r_req_q.ar.size) - 1;

                  // Lane steering
                  for (int b = 0; b < SI_BYTES; b++)
                    if ((b >= si_offset) &&
                        (b - si_offset < (1 << r_req_q.size)) &&
                        (b + mi_offset - si_offset < MI_BYTES)) begin
                      r_req_d.r.data[8 * b +: 8] = mst_r_data[8 * (b + mi_offset - si_offset) +: 8];
                    end

                  r_req_d.len     = r_req_q.len - 1;
                  r_req_d.ar.len  = r_req_q.ar.len - 1;
                  r_req_d.ar.addr = (r_req_q.ar.addr & ~size_mask) + (1 << r_req_q.ar.size);
                  r_req_d.r.last  = (r_req_q.len == 0);
                  r_req_d.r.id    = mst_r_id;

                  // Forward user data
                  if (r_state_q == R_PASSTHROUGH)
                    r_req_d.r.user = mst_r_user;

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
                end // if (mst_r_valid && (mst_r_id % NR_OUTSTANDING == tr))
              end // if (!int_slv_r[tr].valid || (int_slv_r[tr].valid && int_slv_r_ready[tr]))
            end // if (!r_req_d.ar.valid)

            if (int_slv_r[tr].valid && int_slv_r_ready[tr])
              if (r_req_q.len == '1)
                r_state_d = R_IDLE;
          end // case: R_PASSTHROUGH, R_INCR_DOWNSIZE, R_SPLIT_INCR_DOWNSIZE
        endcase // case (r_state_q)

        // Can start a new request as soon as r_state_d is R_IDLE
        if (r_state_d == R_IDLE) begin
          // Reset channels
          r_req_d.ar          = '0;
          r_req_d.r           = '0;

          // Ready
          int_slv_ar_ready[tr] = 1'b1;

          // New write request
          if (slv_ar_valid && (slv_ar_id % NR_OUTSTANDING == tr)) begin
            // Default state
            r_state_d         = R_PASSTHROUGH;

            // Save beat
            r_req_d.ar.id     = slv_ar_id;
            r_req_d.ar.addr   = slv_ar_addr;
            r_req_d.ar.size   = slv_ar_size;
            r_req_d.ar.burst  = slv_ar_burst;
            r_req_d.ar.len    = slv_ar_len;
            r_req_d.ar.lock   = slv_ar_lock;
            r_req_d.ar.cache  = slv_ar_cache;
            r_req_d.ar.prot   = slv_ar_prot;
            r_req_d.ar.qos    = slv_ar_qos;
            r_req_d.ar.region = slv_ar_region;
            r_req_d.ar.user   = slv_ar_user;
            r_req_d.ar.valid  = 1'b1;

            r_req_d.len       = slv_ar_len;
            r_req_d.size      = slv_ar_size;

            if (|(slv_ar_cache & CACHE_MODIFIABLE))
              case (slv_ar_burst)
                BURST_INCR: begin
                  // Evaluate downsize ratio
                  automatic addr_t size_mask  = (1 << slv_ar_size) - 1;
                  automatic addr_t conv_ratio = ((1 << slv_ar_size) + MI_BYTES - 1) / MI_BYTES;

                  // Evaluate output burst length
                  automatic addr_t align_adj  = (slv_ar_addr & size_mask & ~MI_BYTE_MASK) / MI_BYTES;
                  r_req_d.len                 = (slv_ar_len + 1) * conv_ratio - align_adj - 1;

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
              endcase // case (slv_ar_burst)
          end // if (slv_ar_valid && (slv_ar_id % NR_OUTSTANDING == tr))
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

    full_len_t      len;
    size_t          size;
  } w_req_d, w_req_q;

  always_comb begin
    // Maintain state
    w_state_d     = w_state_q;
    w_req_d       = w_req_q;

    // AW Channel
    mst_aw_id     = w_req_q.aw.id;
    mst_aw_addr   = w_req_q.aw.addr;
    mst_aw_len    = w_req_q.aw.len;
    mst_aw_size   = w_req_q.aw.size;
    mst_aw_burst  = w_req_q.aw.burst;
    mst_aw_lock   = w_req_q.aw.lock;
    mst_aw_cache  = w_req_q.aw.cache;
    mst_aw_prot   = w_req_q.aw.prot;
    mst_aw_qos    = w_req_q.aw.qos;
    mst_aw_region = w_req_q.aw.region;
    mst_aw_atop   = w_req_q.aw.atop;
    mst_aw_user   = w_req_q.aw.user;
    mst_aw_valid  = w_req_q.aw.valid;
    slv_aw_ready  = '0;

    // W Channel
    mst_w_data    = '0;
    mst_w_strb    = '0;
    mst_w_last    = '0;
    mst_w_user    = '0;
    mst_w_valid   = '0;
    slv_w_ready   = '0;

    // B Channel
    // No latency
    slv_b_id      = mst_b_id;
    slv_b_resp    = mst_b_resp;
    slv_b_user    = mst_b_user;
    slv_b_valid   = mst_b_valid;
    mst_b_ready   = slv_b_ready;

    // Got a grant on the AW channel
    if (mst_aw_valid && mst_aw_ready)
      w_req_d.aw.valid = 1'b0;

    case (w_state_q)
      W_PASSTHROUGH, W_INCR_DOWNSIZE, W_SPLIT_INCR_DOWNSIZE: begin
        // Request was accepted
        if (!w_req_q.aw.valid) begin
          if (slv_w_valid) begin
            automatic addr_t mi_offset = w_req_q.aw.addr[$clog2(MI_BYTES)-1:0];
            automatic addr_t si_offset = w_req_q.aw.addr[$clog2(SI_BYTES)-1:0];

            // Valid output
            mst_w_valid                = 1'b1;
            mst_w_last                 = slv_w_last && (w_req_q.len == 0);

            // Forward user data
            if (w_state_q == W_PASSTHROUGH)
              mst_w_user = slv_w_user;

            // Serialization
            for (int b = 0; b < SI_BYTES; b++)
              if ((b >= si_offset) &&
                  (b - si_offset < (1 << w_req_q.aw.size)) &&
                  (b + mi_offset - si_offset < MI_BYTES)) begin
                mst_w_data[8 * (b + mi_offset - si_offset) +: 8] = slv_w_data[8 * b +: 8];
                mst_w_strb[b + mi_offset - si_offset]            = slv_w_strb[b];
              end
          end // if (slv_w_valid)

          // Acknowledgement
          if (mst_w_ready && mst_w_valid) begin
            automatic addr_t size_mask = (1 << w_req_q.aw.size) - 1;

            w_req_d.len                = w_req_q.len - 1;
            w_req_d.aw.len             = w_req_q.aw.len - 1;
            w_req_d.aw.addr            = (w_req_q.aw.addr & ~size_mask) + (1 << w_req_q.aw.size);

            case (w_state_q)
              W_PASSTHROUGH:
                slv_w_ready = 1'b1;

              W_INCR_DOWNSIZE, W_SPLIT_INCR_DOWNSIZE:
                if (w_req_q.len == 0 || (align_addr(w_req_d.aw.addr, w_req_q.size) != align_addr(w_req_q.aw.addr, w_req_q.size)))
                  slv_w_ready = 1'b1;
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
          end // if (mst_w_ready && mst_w_valid)
        end // if (!w_req_d.aw.valid)
      end
    endcase // case (w_state_q)

    // Can start a new request as soon as w_state_d is W_IDLE
    if (w_state_d == W_IDLE) begin
      // Reset channels
      w_req_d.aw   = '0;

      // Ready
      slv_aw_ready = 1'b1;

      // New write request
      if (slv_aw_valid && slv_aw_ready) begin
        // Default state
        w_state_d         = W_PASSTHROUGH;

        // Save beat
        w_req_d.aw.id     = slv_aw_id;
        w_req_d.aw.addr   = slv_aw_addr;
        w_req_d.aw.size   = slv_aw_size;
        w_req_d.aw.burst  = slv_aw_burst;
        w_req_d.aw.len    = slv_aw_len;
        w_req_d.aw.lock   = slv_aw_lock;
        w_req_d.aw.cache  = slv_aw_cache;
        w_req_d.aw.prot   = slv_aw_prot;
        w_req_d.aw.qos    = slv_aw_qos;
        w_req_d.aw.region = slv_aw_region;
        w_req_d.aw.atop   = slv_aw_atop;
        w_req_d.aw.user   = slv_aw_user;
        w_req_d.aw.valid  = 1'b1;

        w_req_d.len       = slv_aw_len;
        w_req_d.size      = slv_aw_size;

        // Do nothing
        if (|(slv_aw_cache & CACHE_MODIFIABLE))
          case (slv_aw_burst)
            BURST_INCR: begin
              // Evaluate downsize ratio
              automatic addr_t size_mask  = (1 << slv_aw_size) - 1;
              automatic addr_t conv_ratio = ((1 << slv_aw_size) + MI_BYTES - 1) / MI_BYTES;

              // Evaluate output burst length
              automatic addr_t align_adj  = (slv_aw_addr & size_mask & ~MI_BYTE_MASK) / MI_BYTES;
              w_req_d.len                 = (slv_aw_len + 1) * conv_ratio - align_adj - 1;

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
          endcase // case (slv_aw_burst)
      end // if (slv_aw_valid)
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
