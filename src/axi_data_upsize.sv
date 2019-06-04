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
// AXI Data Upsize Conversion.
// Connects a wide master to a narrower slave.

import axi_pkg::*;

module axi_data_upsize #(
  parameter int  ADDR_WIDTH     = 64                       ,
  parameter int  SI_DATA_WIDTH  = 64                       ,
  parameter int  MI_DATA_WIDTH  = 64                       ,
  parameter int  ID_WIDTH       = 4                        ,
  parameter int  USER_WIDTH     = 1                        ,
  parameter int  NR_OUTSTANDING = 1                        ,
  // Dependent parameters, do not change!
  parameter      MI_BYTES       = MI_DATA_WIDTH/8          ,
  parameter      MI_BYTE_MASK   = MI_BYTES - 1             ,
  parameter      SI_BYTES       = SI_DATA_WIDTH/8          ,
  parameter      SI_BYTE_MASK   = SI_BYTES - 1             ,
  parameter type addr_t         = logic [   ADDR_WIDTH-1:0],
  parameter type si_data_t      = logic [SI_DATA_WIDTH-1:0],
  parameter type si_strb_t      = logic [     SI_BYTES-1:0],
  parameter type mi_data_t      = logic [MI_DATA_WIDTH-1:0],
  parameter type mi_strb_t      = logic [     MI_BYTES-1:0],
  parameter type id_t           = logic [     ID_WIDTH-1:0],
  parameter type user_t         = logic [   USER_WIDTH-1:0]
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

  function automatic addr_t align_addr(addr_t unaligned_addr);
    return unaligned_addr & ~MI_BYTE_MASK;
  endfunction // align_addr

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
    .AxiVldRdy(1'b1          )
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

  enum logic [1:0] { R_IDLE, R_PASSTHROUGH, R_INCR_UPSIZE } [NR_OUTSTANDING-1:0] r_state_d, r_state_q;

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
    channel_ax_t ar  ;
    len_t        len ;
    size_t       size;
  } [NR_OUTSTANDING-1:0] r_req_d, r_req_q;

  always_comb begin
    idqueue_push = '0;
    idqueue_pop  = '0;
    mst_r_ready  = 1'b0;
    slv_ar_ready = 1'b0;

    for (int tr = 0; tr < NR_OUTSTANDING; tr++) begin
      // Maintain state
      r_state_d[tr] = r_state_q[tr];
      r_req_d[tr]   = r_req_q[tr];

      // AR Channel
      int_mst_ar[tr] = '0;
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
      int_mst_ar[tr].atop   = '0;
      int_mst_ar[tr].user   = r_req_q[tr].ar.user;
      int_mst_ar[tr].valid  = r_req_q[tr].ar.valid;

      // R Channel
      // No latency
      int_slv_r[tr].id      = mst_r_id;
      int_slv_r[tr].data    = '0;
      int_slv_r[tr].resp    = mst_r_resp;
      int_slv_r[tr].last    = '0;
      int_slv_r[tr].user    = mst_r_user;
      int_slv_r[tr].valid   = '0;

      // Got a grant on the AR channel
      if (int_mst_ar[tr].valid && int_mst_ar_ready[tr])
        r_req_d[tr].ar.valid = 1'b0;

      case (r_state_q[tr])
        R_IDLE : begin
          // Reset channels
          r_req_d[tr].ar = '0;

          // Ready
          slv_ar_ready = 1'b1;

          // New read request
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
                  // Evaluate output burst length
                  automatic addr_t size_mask  = (1 << slv_ar_size) - 1;

                  automatic addr_t addr_start = align_addr(slv_ar_addr);
                  automatic addr_t addr_end   = align_addr((slv_ar_addr & ~size_mask) + (slv_ar_len << slv_ar_size));

                  r_req_d[tr].ar.len          = (addr_end - addr_start) >> $clog2(MI_BYTES);
                  r_req_d[tr].ar.size         = $clog2(MI_BYTES);
                  r_state_d[tr] = R_INCR_UPSIZE;
                end // case: BURST_INCR
              endcase // case (slv_ar_burst)
          end // if (slv_ar_valid && (idx_read_fsm == tr))
        end // case: R_IDLE

        R_PASSTHROUGH, R_INCR_UPSIZE:
          // Request was accepted
          if (!r_req_q[tr].ar.valid)
            if (mst_r_valid && (idqueue_id == tr) && idqueue_valid) begin
              automatic addr_t mi_offset = r_req_q[tr].ar.addr[$clog2(MI_BYTES)-1:0];
              automatic addr_t si_offset = r_req_q[tr].ar.addr[$clog2(SI_BYTES)-1:0];

              // Valid output
              int_slv_r[tr].valid        = 1'b1;
              int_slv_r[tr].last         = mst_r_last && (r_req_q[tr].len == 0);

              // Serialization
              for (int b = 0; b < MI_BYTES; b++)
                if ((b >= mi_offset) &&
                  (b - mi_offset < (1 << r_req_q[tr].size)) &&
                  (b + si_offset - mi_offset < SI_BYTES)) begin
                  int_slv_r[tr].data[8*(b+si_offset-mi_offset)+:8] = mst_r_data[8 * b +: 8];
                end

              // Acknowledgement
              if (int_slv_r_ready[tr]) begin
                automatic addr_t size_mask = (1 << r_req_q[tr].size) - 1;

                r_req_d[tr].len            = r_req_q[tr].len - 1;
                r_req_d[tr].ar.addr        = (r_req_q[tr].ar.addr & ~size_mask) + (1 << r_req_q[tr].size);

                case (r_state_q[tr])
                  R_PASSTHROUGH :
                    mst_r_ready = 1'b1;

                  R_INCR_UPSIZE :
                    if (r_req_q[tr].len == 0 || (align_addr(r_req_d[tr].ar.addr) != align_addr(r_req_q[tr].ar.addr)))
                      mst_r_ready = 1'b1;
                endcase // case (r_state_q[tr])

                if (r_req_q[tr].len == '0) begin
                  r_state_d[tr]   = R_IDLE;
                  idqueue_pop[tr] = 1'b1;
                end
              end // if (int_slv_r[tr].ready)
            end // if (mst_r_valid && (idqueue_id == tr) && idqueue_valid)
      endcase // case (r_state_q[tr])
    end // for (int tr = 0; tr < NR_OUTSTANDING; tr++)
  end // always_comb

  // --------------
  // WRITE
  // --------------

  enum logic [1:0] { W_IDLE, W_PASSTHROUGH, W_INCR_UPSIZE } w_state_d, w_state_q;

  struct packed {
    channel_ax_t   aw  ;
    mi_channel_w_t w   ;
    len_t          len ;
    size_t         size;
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
    mst_w_data    = w_req_q.w.data;
    mst_w_strb    = w_req_q.w.strb;
    mst_w_last    = w_req_q.w.last;
    mst_w_user    = w_req_q.w.user;
    mst_w_valid   = w_req_q.w.valid;
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
      W_PASSTHROUGH, W_INCR_UPSIZE: begin
        // Got a grant on the W channel
        if (mst_w_valid && mst_w_ready)
          w_req_d.w = '0;

        // Request was accepted
        if (!w_req_q.aw.valid) begin
          // Ready if downstream interface is idle, or if it is ready
          slv_w_ready  = ~mst_w_valid || mst_w_ready;

          if (slv_w_valid && slv_w_ready) begin
            automatic addr_t mi_offset = w_req_q.aw.addr[$clog2(MI_BYTES)-1:0];
            automatic addr_t si_offset = w_req_q.aw.addr[$clog2(SI_BYTES)-1:0];
            automatic addr_t size_mask = (1 << w_req_q.size) - 1;

            // Lane steering
            for (int b = 0; b < MI_BYTES; b++)
              if ((b >= mi_offset) &&
                (b - mi_offset < (1 << w_req_q.size)) &&
                (b + si_offset - mi_offset < SI_BYTES)) begin
                w_req_d.w.data[8 * b +: 8] = slv_w_data[8 * (b + si_offset - mi_offset) +: 8];
                w_req_d.w.strb[b]          = slv_w_strb[b + si_offset - mi_offset];
              end

            w_req_d.len     = w_req_q.len - 1;
            w_req_d.aw.addr = (w_req_q.aw.addr & ~size_mask) + (1 << w_req_q.size);
            w_req_d.w.last  = (w_req_q.len == 0);
            w_req_d.w.user  = mst_w_user;

            case (w_state_q)
              W_PASSTHROUGH:
                // Forward data as soon as we can
                w_req_d.w.valid = 1'b1;

              W_INCR_UPSIZE:
                // Forward when the burst is finished, or when a word was filled up
                if (w_req_q.len == 0 || (align_addr(w_req_d.aw.addr) != align_addr(w_req_q.aw.addr)))
                  w_req_d.w.valid = 1'b1;
            endcase // case (w_state_q)
          end // if (slv_w_valid && slv_w_ready)
        end // if (!w_req_d.aw.valid)

        if (mst_w_valid && mst_w_ready)
          if (w_req_q.len == '1) begin
            slv_w_ready = 1'b0;
            w_state_d  = W_IDLE;
          end
      end
    endcase // case (w_state_q)

    // Can start a new request as soon as w_state_d is W_IDLE
    if (w_state_d == W_IDLE) begin
      // Reset channels
      w_req_d.aw  = '0;
      w_req_d.w   = '0;

      // Ready
      slv_aw_ready = 1'b1;

      // New write request
      if (slv_aw_valid & slv_aw_ready) begin
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

        if (|(slv_aw_cache & CACHE_MODIFIABLE))
          case (slv_aw_burst)
            BURST_INCR: begin
              // Evaluate output burst length
              automatic addr_t size_mask  = (1 << slv_aw_size) - 1;

              automatic addr_t addr_start = align_addr(slv_aw_addr);
              automatic addr_t addr_end   = align_addr((slv_aw_addr & ~size_mask) + (slv_aw_len << slv_aw_size));

              w_req_d.aw.len              = (addr_end - addr_start) >> $clog2(MI_BYTES);
              w_req_d.aw.size             = $clog2(MI_BYTES);
              w_state_d                   = W_INCR_UPSIZE;
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
      assert(SI_DATA_WIDTH < MI_DATA_WIDTH)
        else $fatal("Data upsizer not being used for upsizing.");

      assert (2**ID_WIDTH >= NR_OUTSTANDING)
        else $fatal("The outstanding transactions could not be indexed with the given ID bits!");
    end
  `endif
  // pragma translate_on

endmodule // axi_data_upsize
