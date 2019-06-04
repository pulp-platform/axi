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
  parameter int  ADDR_WIDTH     = 64             ,
  parameter int  SI_DATA_WIDTH  = 64             ,
  parameter int  MI_DATA_WIDTH  = 64             ,
  parameter int  ID_WIDTH       = 4              ,
  parameter int  USER_WIDTH     = 1              ,
  parameter int  NR_OUTSTANDING = 1              ,
  // Dependent parameters, do not change!
  parameter      MI_BYTES       = MI_DATA_WIDTH/8,
  parameter      MI_BYTE_MASK   = MI_BYTES - 1   ,
  parameter      SI_BYTES       = SI_DATA_WIDTH/8,
  parameter      SI_BYTE_MASK   = SI_BYTES - 1   ,
  parameter type addr_t         = logic            [   ADDR_WIDTH-1:0],
  parameter type si_data_t      = logic            [SI_DATA_WIDTH-1:0],
  parameter type si_strb_t      = logic            [     SI_BYTES-1:0],
  parameter type mi_data_t      = logic            [MI_DATA_WIDTH-1:0],
  parameter type mi_strb_t      = logic            [     MI_BYTES-1:0],
  parameter type id_t           = logic            [     ID_WIDTH-1:0],
  parameter type user_t         = logic            [   USER_WIDTH-1:0]
) (
  input  logic     clk_i        ,
  input  logic     rst_ni       ,
  // SLAVE INTERFACE
  input  id_t      slv_aw_id    ,
  input  addr_t    slv_aw_addr  ,
  input  len_t     slv_aw_len   ,
  input  size_t    slv_aw_size  ,
  input  burst_t   slv_aw_burst ,
  input  logic     slv_aw_lock  ,
  input  cache_t   slv_aw_cache ,
  input  prot_t    slv_aw_prot  ,
  input  qos_t     slv_aw_qos   ,
  input  region_t  slv_aw_region,
  input  atop_t    slv_aw_atop  ,
  input  user_t    slv_aw_user  ,
  input  logic     slv_aw_valid ,
  output logic     slv_aw_ready ,
  input  si_data_t slv_w_data   ,
  input  si_strb_t slv_w_strb   ,
  input  logic     slv_w_last   ,
  input  user_t    slv_w_user   ,
  input  logic     slv_w_valid  ,
  output logic     slv_w_ready  ,
  output id_t      slv_b_id     ,
  output resp_t    slv_b_resp   ,
  output user_t    slv_b_user   ,
  output logic     slv_b_valid  ,
  input  logic     slv_b_ready  ,
  input  id_t      slv_ar_id    ,
  input  addr_t    slv_ar_addr  ,
  input  len_t     slv_ar_len   ,
  input  size_t    slv_ar_size  ,
  input  burst_t   slv_ar_burst ,
  input  logic     slv_ar_lock  ,
  input  cache_t   slv_ar_cache ,
  input  prot_t    slv_ar_prot  ,
  input  qos_t     slv_ar_qos   ,
  input  region_t  slv_ar_region,
  input  user_t    slv_ar_user  ,
  input  logic     slv_ar_valid ,
  output logic     slv_ar_ready ,
  output id_t      slv_r_id     ,
  output si_data_t slv_r_data   ,
  output resp_t    slv_r_resp   ,
  output logic     slv_r_last   ,
  output user_t    slv_r_user   ,
  output logic     slv_r_valid  ,
  input  logic     slv_r_ready  ,
  // MASTER INTERFACE
  output id_t      mst_aw_id    ,
  output addr_t    mst_aw_addr  ,
  output len_t     mst_aw_len   ,
  output size_t    mst_aw_size  ,
  output burst_t   mst_aw_burst ,
  output logic     mst_aw_lock  ,
  output cache_t   mst_aw_cache ,
  output prot_t    mst_aw_prot  ,
  output qos_t     mst_aw_qos   ,
  output region_t  mst_aw_region,
  output atop_t    mst_aw_atop  ,
  output user_t    mst_aw_user  ,
  output logic     mst_aw_valid ,
  input  logic     mst_aw_ready ,
  output mi_data_t mst_w_data   ,
  output mi_strb_t mst_w_strb   ,
  output logic     mst_w_last   ,
  output user_t    mst_w_user   ,
  output logic     mst_w_valid  ,
  input  logic     mst_w_ready  ,
  input  id_t      mst_b_id     ,
  input  resp_t    mst_b_resp   ,
  input  user_t    mst_b_user   ,
  input  logic     mst_b_valid  ,
  output logic     mst_b_ready  ,
  output id_t      mst_ar_id    ,
  output addr_t    mst_ar_addr  ,
  output len_t     mst_ar_len   ,
  output size_t    mst_ar_size  ,
  output burst_t   mst_ar_burst ,
  output logic     mst_ar_lock  ,
  output cache_t   mst_ar_cache ,
  output prot_t    mst_ar_prot  ,
  output qos_t     mst_ar_qos   ,
  output region_t  mst_ar_region,
  output user_t    mst_ar_user  ,
  output logic     mst_ar_valid ,
  input  logic     mst_ar_ready ,
  input  id_t      mst_r_id     ,
  input  mi_data_t mst_r_data   ,
  input  resp_t    mst_r_resp   ,
  input  logic     mst_r_last   ,
  input  user_t    mst_r_user   ,
  input  logic     mst_r_valid  ,
  output logic     mst_r_ready
);

  // --------------
  // DEFINITIONS
  // --------------

  // Type for indexing which FSM handles each outstanding transaction
  typedef logic [$clog2(NR_OUTSTANDING)-1:0] tr_id_t;

  typedef struct packed {
    id_t     id    ;
    addr_t   addr  ;
    len_t    len   ;
    size_t   size  ;
    burst_t  burst ;
    logic    lock  ;
    cache_t  cache ;
    prot_t   prot  ;
    qos_t    qos   ;
    region_t region;
    atop_t   atop  ; // Only defined on the AW channel.
    user_t   user  ;
    logic    valid ;
  } channel_ax_t;

  typedef struct packed {
    mi_data_t data ;
    mi_strb_t strb ;
    logic     last ;
    user_t    user ;
    logic     valid;
  } mi_channel_w_t;

  typedef struct packed {
    si_data_t data ;
    si_strb_t strb ;
    logic     last ;
    user_t    user ;
    logic     valid;
  } si_channel_w_t;

  typedef struct packed {
    id_t      id   ;
    mi_data_t data ;
    resp_t    resp ;
    logic     last ;
    user_t    user ;
    logic     valid;
  } mi_channel_r_t;

  typedef struct packed {
    id_t      id   ;
    si_data_t data ;
    resp_t    resp ;
    logic     last ;
    user_t    user ;
    logic     valid;
  } si_channel_r_t;

  function automatic addr_t align_addr(addr_t unaligned_addr, size_t size);
    return unaligned_addr & ~((1 << size) - 1);
  endfunction // align_addr

  // Length of burst after downsizing
  typedef logic [$clog2(SI_BYTES/MI_BYTES)+7:0] full_len_t;

  // --------------
  // MULTIPLEXER
  // --------------

  si_channel_r_t [NR_OUTSTANDING-1:0] int_slv_r      ;
  logic          [NR_OUTSTANDING-1:0] int_slv_r_valid;
  logic          [NR_OUTSTANDING-1:0] int_slv_r_ready;
  si_channel_r_t                      arb_slv_r      ;

  rr_arb_tree #(
    .NumIn    (NR_OUTSTANDING),
    .DataType (si_channel_r_t),
    .AxiVldRdy(1'b1          ),
    .LockIn   (1'b1          )
  ) i_arbiter_slv_r (
    .clk_i                   ,
    .rst_ni                  ,
    .flush_i(1'b0           ),
    .rr_i   (/* unused */   ),
    .req_i  (int_slv_r_valid),
    .gnt_o  (int_slv_r_ready),
    .data_i (int_slv_r      ),
    .gnt_i  (slv_r_ready    ),
    .req_o  (slv_r_valid    ),
    .data_o (arb_slv_r      ),
    .idx_o  (/* unused */   )
  );

  channel_ax_t [NR_OUTSTANDING-1:0] int_mst_ar      ;
  logic        [NR_OUTSTANDING-1:0] int_mst_ar_valid;
  logic        [NR_OUTSTANDING-1:0] int_mst_ar_ready;
  channel_ax_t                      arb_mst_ar      ;

  rr_arb_tree #(
    .NumIn    (NR_OUTSTANDING),
    .DataType (channel_ax_t  ),
    .AxiVldRdy(1'b1          ),
    .LockIn   (1'b1          )
  ) i_arbiter_mst_ar (
    .clk_i                    ,
    .rst_ni                   ,
    .flush_i(1'b0            ),
    .rr_i   (/* unused */    ),
    .req_i  (int_mst_ar_valid),
    .gnt_o  (int_mst_ar_ready),
    .data_i (int_mst_ar      ),
    .gnt_i  (mst_ar_ready    ),
    .req_o  (mst_ar_valid    ),
    .data_o (arb_mst_ar      ),
    .idx_o  (/* unused */    )
  );

  always_comb begin
    // OUTPUT SIGNALS
    mst_ar_id     = arb_mst_ar.id;
    mst_ar_addr   = arb_mst_ar.addr;
    mst_ar_len    = arb_mst_ar.len;
    mst_ar_size   = arb_mst_ar.size;
    mst_ar_burst  = arb_mst_ar.burst;
    mst_ar_lock   = arb_mst_ar.lock;
    mst_ar_cache  = arb_mst_ar.cache;
    mst_ar_prot   = arb_mst_ar.prot;
    mst_ar_qos    = arb_mst_ar.qos;
    mst_ar_region = arb_mst_ar.region;
    mst_ar_user   = arb_mst_ar.user;

    slv_r_id      = arb_slv_r.id;
    slv_r_data    = arb_slv_r.data;
    slv_r_resp    = arb_slv_r.resp;
    slv_r_last    = arb_slv_r.last;
    slv_r_user    = arb_slv_r.user;

    // REQUEST SIGNALS
    for (int tr = 0; tr < NR_OUTSTANDING; tr++) begin
      int_slv_r_valid[tr]  = int_slv_r[tr].valid;
      int_mst_ar_valid[tr] = int_mst_ar[tr].valid;
    end
  end // block: mux

  // --------------
  // READ
  // --------------

  // There is an identical FSM for each possible outstanding transaction
  enum logic [1:0] { R_IDLE, R_PASSTHROUGH, R_INCR_DOWNSIZE, R_SPLIT_INCR_DOWNSIZE } [NR_OUTSTANDING-1:0] r_state_d, r_state_q;

  // Decides which FSM is idle

  logic [NR_OUTSTANDING-1:0] idle_read_fsm;
  tr_id_t                    idx_read_fsm ;
  logic                      full_read_fsm;

  for (genvar tr = 0; tr < NR_OUTSTANDING; tr++)
    assign idle_read_fsm[tr] = (r_state_q[tr] == R_IDLE);

  lzc #(.WIDTH(NR_OUTSTANDING)) i_read_lzc (
    .in_i   (idle_read_fsm),
    .cnt_o  (idx_read_fsm ),
    .empty_o(full_read_fsm)
  );

  // This ID queue is used to resolve with FSM is handling
  // each outstanding read transaction

  logic [NR_OUTSTANDING-1:0] idqueue_push ;
  logic [NR_OUTSTANDING-1:0] idqueue_pop  ;
  tr_id_t                    idqueue_id   ;
  logic                      idqueue_valid;

  id_queue #(
    .ID_WIDTH(ID_WIDTH      ),
    .CAPACITY(NR_OUTSTANDING),
    .data_t  (tr_id_t       )
  ) i_read_id_queue (
    .clk_i                          ,
    .rst_ni                         ,

    .inp_id_i        (slv_ar_id    ),
    .inp_data_i      (idx_read_fsm ),
    .inp_req_i       (|idqueue_push),
    .inp_gnt_o       (/* unused  */),

    .oup_id_i        (mst_r_id     ),
    .oup_pop_i       (|idqueue_pop ),
    .oup_req_i       (1'b1         ),
    .oup_data_o      (idqueue_id   ),
    .oup_data_valid_o(idqueue_valid),
    .oup_gnt_o       (/* unused  */),

    // Unused
    .exists_data_i   ('0           ),
    .exists_mask_i   ('0           ),
    .exists_req_i    ('0           ),
    .exists_o        (/* unused  */),
    .exists_gnt_o    (/* unused  */)
  );

  struct packed {
    channel_ax_t   ar  ;
    si_channel_r_t r   ;
    full_len_t     len ;
    size_t         size;
  } [NR_OUTSTANDING-1:0] r_req_d, r_req_q;

  always_comb begin
    idqueue_push = '0;
    idqueue_pop  = '0;
    mst_r_ready  = 1'b0;
    slv_ar_ready = 1'b0;

    for (int tr = 0; tr < NR_OUTSTANDING; tr++) begin
      // Maintain state
      r_state_d[tr]         = r_state_q[tr];
      r_req_d[tr]           = r_req_q[tr];

      // AR Channel
      int_mst_ar[tr]        = '0;
      int_mst_ar[tr].id     = r_req_q[tr].ar.id;
      int_mst_ar[tr].addr   = r_req_q[tr].ar.addr;
      int_mst_ar[tr].len    = r_req_q[tr].ar.len;
      int_mst_ar[tr].size   = r_req_q[tr].ar.size;
      int_mst_ar[tr].burst  = r_req_q[tr].ar.burst;
      int_mst_ar[tr].lock   = r_req_q[tr].ar.lock;
      int_mst_ar[tr].cache  = r_req_q[tr].ar.cache;
      int_mst_ar[tr].prot   = r_req_q[tr].ar.prot;
      int_mst_ar[tr].qos    = r_req_q[tr].ar.qos;
      int_mst_ar[tr].region = r_req_q[tr].ar.region;
      int_mst_ar[tr].user   = r_req_q[tr].ar.user;
      int_mst_ar[tr].valid  = r_req_q[tr].ar.valid;

      // R Channel
      int_slv_r[tr].id      = r_req_q[tr].r.id;
      int_slv_r[tr].data    = r_req_q[tr].r.data;
      int_slv_r[tr].resp    = r_req_q[tr].r.resp;
      int_slv_r[tr].last    = r_req_q[tr].r.last;
      int_slv_r[tr].user    = r_req_q[tr].r.user;
      int_slv_r[tr].valid   = r_req_q[tr].r.valid;

      // Got a grant on the AR channel
      if (int_mst_ar[tr].valid && int_mst_ar_ready[tr])
        r_req_d[tr].ar.valid = 1'b0;

      case (r_state_q[tr])
        R_IDLE : begin
          // Reset channels
          r_req_d[tr].ar = '0;
          r_req_d[tr].r  = '0;

          // Ready
          slv_ar_ready = 1'b1;

          // New write request
          if (slv_ar_valid && (idx_read_fsm == tr)) begin
            // Push to ID queue
            idqueue_push[tr] = 1'b1;

            // Default state
            r_state_d[tr] = R_PASSTHROUGH;

            // Save beat
            r_req_d[tr].ar.id     = slv_ar_id;
            r_req_d[tr].ar.addr   = slv_ar_addr;
            r_req_d[tr].ar.size   = slv_ar_size;
            r_req_d[tr].ar.burst  = slv_ar_burst;
            r_req_d[tr].ar.len    = slv_ar_len;
            r_req_d[tr].ar.lock   = slv_ar_lock;
            r_req_d[tr].ar.cache  = slv_ar_cache;
            r_req_d[tr].ar.prot   = slv_ar_prot;
            r_req_d[tr].ar.qos    = slv_ar_qos;
            r_req_d[tr].ar.region = slv_ar_region;
            r_req_d[tr].ar.user   = slv_ar_user;
            r_req_d[tr].ar.valid  = 1'b1;

            r_req_d[tr].len       = slv_ar_len;
            r_req_d[tr].size      = slv_ar_size;

            if (|(slv_ar_cache & CACHE_MODIFIABLE))
              case (slv_ar_burst)
                BURST_INCR : begin
                  // Evaluate downsize ratio
                  automatic addr_t size_mask  = (1 << slv_ar_size) - 1;
                  automatic addr_t conv_ratio = ((1 << slv_ar_size) + MI_BYTES - 1) / MI_BYTES;

                  // Evaluate output burst length
                  automatic addr_t align_adj  = (slv_ar_addr & size_mask & ~MI_BYTE_MASK) / MI_BYTES;
                  r_req_d[tr].len             = (slv_ar_len + 1) * conv_ratio - align_adj - 1;

                  if (conv_ratio != 1) begin
                    r_req_d[tr].ar.size   = $clog2(MI_BYTES);

                    if (r_req_d[tr].len <= 255) begin
                      r_state_d[tr] = R_INCR_DOWNSIZE;
                      r_req_d[tr].ar.len = r_req_d[tr].len;
                    end else begin
                      r_state_d[tr] = R_SPLIT_INCR_DOWNSIZE;
                      r_req_d[tr].ar.len = 255 - align_adj;
                    end
                  end // if (conv_ratio != 1)
                end // case: BURST_INCR
              endcase // case (slv_ar_burst)
          end // if (slv_ar_valid && (idx_read_fsm == tr))
        end

        R_PASSTHROUGH, R_INCR_DOWNSIZE, R_SPLIT_INCR_DOWNSIZE: begin
          // Got a grant on the R channel
          if (int_slv_r[tr].valid && int_slv_r_ready[tr])
            r_req_d[tr].r = '0;

          // Request was accepted
          if (!r_req_q[tr].ar.valid)
            // Our turn
            if ((idqueue_id == tr) && idqueue_valid)
              // Ready to accept more data
              if (!int_slv_r[tr].valid || (int_slv_r[tr].valid && int_slv_r_ready[tr])) begin
                mst_r_ready = 1'b1;

                if (mst_r_valid) begin
                  automatic addr_t mi_offset = r_req_q[tr].ar.addr[$clog2(MI_BYTES)-1:0];
                  automatic addr_t si_offset = r_req_q[tr].ar.addr[$clog2(SI_BYTES)-1:0];
                  automatic addr_t size_mask = (1 << r_req_q[tr].ar.size) - 1;

                  // Lane steering
                  for (int b = 0; b < SI_BYTES; b++)
                    if ((b >= si_offset) &&
                      (b - si_offset < (1 << r_req_q[tr].size)) &&
                      (b + mi_offset - si_offset < MI_BYTES)) begin
                      r_req_d[tr].r.data[8*b+:8] = mst_r_data[8 * (b + mi_offset - si_offset) +: 8];
                    end

                  r_req_d[tr].len     = r_req_q[tr].len - 1;
                  r_req_d[tr].ar.len  = r_req_q[tr].ar.len - 1;
                  r_req_d[tr].ar.addr = (r_req_q[tr].ar.addr & ~size_mask) + (1 << r_req_q[tr].ar.size);
                  r_req_d[tr].r.last  = (r_req_q[tr].len == 0);
                  r_req_d[tr].r.id    = mst_r_id;
                  r_req_d[tr].r.user  = mst_r_user;

                  if (r_req_q[tr].len == 0)
                    idqueue_pop[tr] = 1'b1;

                  case (r_state_q[tr])
                    R_PASSTHROUGH :
                      // Forward data as soon as we can
                      r_req_d[tr].r.valid = 1'b1;

                    R_INCR_DOWNSIZE, R_SPLIT_INCR_DOWNSIZE:
                      // Forward when the burst is finished, or when a word was filled up
                      if (r_req_q[tr].len == 0 || (align_addr(r_req_d[tr].ar.addr, r_req_q[tr].size) != align_addr(r_req_q[tr].ar.addr, r_req_q[tr].size)))
                        r_req_d[tr].r.valid = 1'b1;
                  endcase // case (r_state_q[tr])

                  // Trigger another burst request, if needed
                  if (r_state_q[tr] == R_SPLIT_INCR_DOWNSIZE)
                    // Finished current burst, but whole transaction hasn't finished
                    if (r_req_q[tr].ar.len == '0 && r_req_q[tr].len != '0) begin
                      r_req_d[tr].ar.valid = 1'b1;
                      r_req_d[tr].ar.len   = (r_req_d[tr].len <= 255) ? r_req_d[tr].len : 255;
                    end
                end // if ((idqueue_id == tr) && idqueue_valid)
              end // if (!int_slv_r[tr].valid || (int_slv_r[tr].valid && int_slv_r_ready[tr]))

          if (int_slv_r[tr].valid && int_slv_r_ready[tr])
            if (r_req_q[tr].len == '1)
              r_state_d[tr] = R_IDLE;
        end // case: R_PASSTHROUGH, R_INCR_DOWNSIZE, R_SPLIT_INCR_DOWNSIZE
      endcase // case (r_state_q[tr])
    end // for (unsigned int tr = 0; tr < NR_OUTSTANDING; tr++)
  end // always_comb

  // --------------
  // WRITE
  // --------------

  enum logic [1:0] { W_IDLE, W_PASSTHROUGH, W_INCR_DOWNSIZE, W_SPLIT_INCR_DOWNSIZE } w_state_d, w_state_q;

  struct packed {
    channel_ax_t aw  ;
    full_len_t   len ;
    size_t       size;
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
        if (!w_req_q.aw.valid)
          if (slv_w_valid) begin
            automatic addr_t mi_offset = w_req_q.aw.addr[$clog2(MI_BYTES)-1:0];
            automatic addr_t si_offset = w_req_q.aw.addr[$clog2(SI_BYTES)-1:0];

            // Valid output
            mst_w_valid                = 1'b1;
            mst_w_last                 = slv_w_last && (w_req_q.len == 0);
            mst_w_user                 = slv_w_user;

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
      end // if (slv_aw_valid && slv_aw_ready)
    end
  end

  // --------------
  // REGISTERS
  // --------------

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (~rst_ni) begin
      r_state_q <= {NR_OUTSTANDING{R_IDLE}};
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

  // --------------
  // ASSERTIONS
  // --------------

  // Validate parameters.
  // pragma translate_off
  `ifndef VERILATOR
    initial begin: validate_params
      assert(SI_DATA_WIDTH > MI_DATA_WIDTH)
        else $fatal("Data downsizer not being used for downsizing.");

      assert (2**ID_WIDTH >= NR_OUTSTANDING)
        else $fatal("The outstanding transactions could not be indexed with the given ID bits!");
    end
  `endif
  // pragma translate_on

endmodule // axi_data_downsize
