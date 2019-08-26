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
  localparam TR_ID_WIDTH = NR_OUTSTANDING > 1 ? $clog2(NR_OUTSTANDING) : 1;
  typedef logic [TR_ID_WIDTH-1:0] tr_id_t;

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
  // ARBITERS
  // --------------

  // R

  si_channel_r_t [NR_OUTSTANDING-1:0] slv_r_outstanding      ;
  logic          [NR_OUTSTANDING-1:0] slv_r_valid_outstanding;
  logic          [NR_OUTSTANDING-1:0] slv_r_ready_outstanding;
  si_channel_r_t                      arbiter_slv_r          ;

  assign slv_r_id   = arbiter_slv_r.id;
  assign slv_r_data = arbiter_slv_r.data;
  assign slv_r_resp = arbiter_slv_r.resp;
  assign slv_r_last = arbiter_slv_r.last;
  assign slv_r_user = arbiter_slv_r.user;

  rr_arb_tree #(
    .NumIn    (NR_OUTSTANDING),
    .DataType (si_channel_r_t),
    .AxiVldRdy(1'b1          )
  ) i_arbiter_slv_r (
    .clk_i                           ,
    .rst_ni                          ,
    .flush_i(1'b0                   ),
    .rr_i   (/* unused */           ),
    .req_i  (slv_r_valid_outstanding),
    .gnt_o  (slv_r_ready_outstanding),
    .data_i (slv_r_outstanding      ),
    .gnt_i  (slv_r_ready            ),
    .req_o  (slv_r_valid            ),
    .data_o (arbiter_slv_r          ),
    .idx_o  (/* unused */           )
  );

  logic [NR_OUTSTANDING-1:0] mst_r_ready_outstanding;
  assign mst_r_ready = |mst_r_ready_outstanding;

  // AR
  // Multiplex AR slave between AR and AW for the injection of atomic operations with an R response.
  logic inject_aw_into_ar_req,  inject_aw_into_ar_gnt,
        int_slv_ar_req,         int_slv_ar_gnt;
  logic [NR_OUTSTANDING-1:0] int_slv_ar_gnt_outstanding;
  assign int_slv_ar_gnt = |int_slv_ar_gnt_outstanding;
  channel_ax_t slv_ar, slv_aw, int_slv_ar;
  assign slv_ar = '{
    id:     slv_ar_id,
    addr:   slv_ar_addr,
    len:    slv_ar_len,
    size:   slv_ar_size,
    burst:  slv_ar_burst,
    lock:   slv_ar_lock,
    cache:  slv_ar_cache,
    prot:   slv_ar_prot,
    qos:    slv_ar_qos,
    region: slv_ar_region,
    atop:   '0,
    user:   slv_ar_user,
    valid:  slv_ar_valid
  };
  assign slv_aw = '{
    id:     slv_aw_id,
    addr:   slv_aw_addr,
    len:    slv_aw_len,
    size:   slv_aw_size,
    burst:  slv_aw_burst,
    lock:   slv_aw_lock,
    cache:  slv_aw_cache,
    prot:   slv_aw_prot,
    qos:    slv_aw_qos,
    region: slv_aw_region,
    atop:   slv_aw_atop,
    user:   slv_aw_user,
    valid:  slv_aw_valid
  };
  rr_arb_tree #(
    .NumIn      (2),
    .DataWidth  ($bits(int_slv_ar)),
    .ExtPrio    (1'b0),
    .AxiVldRdy  (1'b1),
    .LockIn     (1'b0)
  ) i_int_slv_ar_arb (
    .clk_i,
    .rst_ni,
    .flush_i  (1'b0),
    .rr_i     ('0),
    .req_i    ({inject_aw_into_ar_req,  slv_ar_valid}),
    .gnt_o    ({inject_aw_into_ar_gnt,  slv_ar_ready}),
    .data_i   ({slv_aw,                 slv_ar}),
    .req_o    (int_slv_ar_req),
    .gnt_i    (int_slv_ar_gnt),
    .data_o   (int_slv_ar),
    .idx_o    ()
  );

  channel_ax_t [NR_OUTSTANDING-1:0] mst_ar_outstanding      ;
  logic        [NR_OUTSTANDING-1:0] mst_ar_valid_outstanding;
  logic        [NR_OUTSTANDING-1:0] mst_ar_ready_outstanding;
  channel_ax_t                      arbiter_mst_ar          ;

  assign mst_ar_id     = arbiter_mst_ar.id;
  assign mst_ar_addr   = arbiter_mst_ar.addr;
  assign mst_ar_len    = arbiter_mst_ar.len;
  assign mst_ar_size   = arbiter_mst_ar.size;
  assign mst_ar_burst  = arbiter_mst_ar.burst;
  assign mst_ar_lock   = arbiter_mst_ar.lock;
  assign mst_ar_cache  = arbiter_mst_ar.cache;
  assign mst_ar_prot   = arbiter_mst_ar.prot;
  assign mst_ar_qos    = arbiter_mst_ar.qos;
  assign mst_ar_region = arbiter_mst_ar.region;
  assign mst_ar_user   = arbiter_mst_ar.user;

  rr_arb_tree #(
    .NumIn    (NR_OUTSTANDING),
    .DataType (channel_ax_t  ),
    .AxiVldRdy(1'b1          ),
    .LockIn   (1'b1          )
  ) i_arbiter_mst_ar (
    .clk_i                            ,
    .rst_ni                           ,
    .flush_i(1'b0                    ),
    .rr_i   (/* unused */            ),
    .req_i  (mst_ar_valid_outstanding),
    .gnt_o  (mst_ar_ready_outstanding),
    .data_i (mst_ar_outstanding      ),
    .gnt_i  (mst_ar_ready            ),
    .req_o  (mst_ar_valid            ),
    .data_o (arbiter_mst_ar          ),
    .idx_o  (/* unused */            )
  );

  logic [NR_OUTSTANDING-1:0] slv_ar_ready_outstanding;
  assign int_slv_ar_ready = |slv_ar_ready_outstanding;

  // UNPACK REQUEST SIGNALS

  generate
    for (genvar t = 0; t < NR_OUTSTANDING; t++) begin: gen_outstanding_request_signals
      assign slv_r_valid_outstanding[t]  = slv_r_outstanding[t].valid;
      assign mst_ar_valid_outstanding[t] = mst_ar_outstanding[t].valid;
    end
  endgenerate

  // --------------
  // READ
  // --------------

  typedef enum logic [1:0] {
    R_IDLE, R_PASSTHROUGH, R_INCR_UPSIZE
  } r_state_t;

  logic [NR_OUTSTANDING-1:0] idle_read_upsizer;
  tr_id_t                    idx_idle_upsizer ;

  lzc #(.WIDTH(NR_OUTSTANDING)) i_read_lzc (
    .in_i   (idle_read_upsizer),
    .cnt_o  (idx_idle_upsizer ),
    .empty_o(                 )
  );

  // This ID queue is used to resolve which FSM is handling
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
    .clk_i                             ,
    .rst_ni                            ,

    .inp_id_i        (int_slv_ar.id   ),
    .inp_data_i      (idx_idle_upsizer),
    .inp_req_i       (|idqueue_push   ),
    .inp_gnt_o       (/* unused  */   ),

    .oup_id_i        (mst_r_id        ),
    .oup_pop_i       (|idqueue_pop    ),
    .oup_req_i       (1'b1            ),
    .oup_data_o      (idqueue_id      ),
    .oup_data_valid_o(idqueue_valid   ),
    .oup_gnt_o       (/* unused  */   ),

    // Unused
    .exists_data_i   ('0              ),
    .exists_mask_i   ('0              ),
    .exists_req_i    ('0              ),
    .exists_o        (/* unused  */   ),
    .exists_gnt_o    (/* unused  */   )
  );

  generate
    for (genvar t = 0; t < NR_OUTSTANDING; t++) begin: gen_read_upsizer
      r_state_t r_state_d, r_state_q;
      assign idle_read_upsizer[t] = (r_state_q == R_IDLE);

      struct packed {
        channel_ax_t ar  ;
        len_t        len ;
        size_t       size;
      } r_req_d, r_req_q;

      always_comb begin
        // Maintain state
        r_state_d = r_state_q;
        r_req_d   = r_req_q;

        // AR Channel
        mst_ar_outstanding[t] = '{
          id      : r_req_q.ar.id,
          addr    : r_req_q.ar.addr,
          len     : r_req_q.ar.len,
          size    : r_req_q.ar.size,
          burst   : r_req_q.ar.burst,
          lock    : r_req_q.ar.lock,
          cache   : r_req_q.ar.cache,
          prot    : r_req_q.ar.prot,
          qos     : r_req_q.ar.qos,
          region  : r_req_q.ar.prot,
          user    : r_req_q.ar.user,
          valid   : r_req_q.ar.valid,
          default : '0
        };

        // R Channel
        // No latency
        slv_r_outstanding[t] = '{
          id      : mst_r_id,
          resp    : mst_r_resp,
          user    : mst_r_user,
          default : '0
        };

        idqueue_push[t] = 1'b0;
        idqueue_pop[t]  = 1'b0;

        int_slv_ar_gnt_outstanding[t] = 1'b0;

        mst_r_ready_outstanding[t]  = 1'b0;
        slv_ar_ready_outstanding[t] = 1'b0;

        // Got a grant on the AR channel
        if (mst_ar_valid_outstanding[t] && mst_ar_ready_outstanding[t])
          r_req_d.ar.valid = 1'b0;

        case (r_state_q)
          R_IDLE : begin
            // Reset channels
            r_req_d.ar = '0;

            // Ready
            slv_ar_ready_outstanding[t] = 1'b1;

            // New read request
            if (int_slv_ar_req && (idx_idle_upsizer == t)) begin
              int_slv_ar_gnt_outstanding[t] = 1'b1;
              // Push to ID queue
              idqueue_push[t] = 1'b1;

              // Default state
              r_state_d = R_PASSTHROUGH;

              // Save beat
              r_req_d.ar = '{
                id      : int_slv_ar.id,
                addr    : int_slv_ar.addr,
                size    : int_slv_ar.size,
                burst   : int_slv_ar.burst,
                len     : int_slv_ar.len,
                lock    : int_slv_ar.lock,
                cache   : int_slv_ar.cache,
                prot    : int_slv_ar.prot,
                qos     : int_slv_ar.qos,
                region  : int_slv_ar.region,
                user    : int_slv_ar.user,
                valid   : &(~int_slv_ar.atop), // Injected "AR"s from AW are not valid.
                default : '0
              };
              r_req_d.len  = int_slv_ar.len;
              r_req_d.size = int_slv_ar.size;

              if (|(int_slv_ar.cache & CACHE_MODIFIABLE))
                case (int_slv_ar.burst)
                  BURST_INCR : begin
                    // Evaluate output burst length
                    automatic addr_t size_mask  = (1 << int_slv_ar.size) - 1;

                    automatic addr_t addr_start = align_addr(int_slv_ar.addr);
                    automatic addr_t addr_end   = align_addr((int_slv_ar.addr & ~size_mask) + (int_slv_ar.len << int_slv_ar.size));

                    r_req_d.ar.len  = (addr_end - addr_start) >> $clog2(MI_BYTES);
                    r_req_d.ar.size = $clog2(MI_BYTES);
                    r_state_d       = R_INCR_UPSIZE;
                  end // case: BURST_INCR
                endcase // case (int_slv_ar.burst)
            end // if (int_slv_ar_req && (idx_read_fsm == t))
          end // case: R_IDLE

          R_PASSTHROUGH, R_INCR_UPSIZE:
            // Request was accepted
            if (!r_req_q.ar.valid)
              if (mst_r_valid && (idqueue_id == t) && idqueue_valid) begin
                automatic addr_t mi_offset = r_req_q.ar.addr[$clog2(MI_BYTES)-1:0];
                automatic addr_t si_offset = r_req_q.ar.addr[$clog2(SI_BYTES)-1:0];

                // Valid output
                slv_r_outstanding[t].valid = 1'b1;
                slv_r_outstanding[t].last  = mst_r_last && (r_req_q.len == 0);

                // Serialization
                for (int b = 0; b < MI_BYTES; b++)
                  if ((b >= mi_offset) &&
                    (b - mi_offset < (1 << r_req_q.size)) &&
                    (b + si_offset - mi_offset < SI_BYTES)) begin
                    slv_r_outstanding[t].data[8*(b + si_offset - mi_offset) +: 8] = mst_r_data[8 * b +: 8];
                  end

                // Acknowledgement
                if (slv_r_ready_outstanding[t]) begin
                  automatic addr_t size_mask = (1 << r_req_q.size) - 1;

                  r_req_d.len     = r_req_q.len - 1;
                  r_req_d.ar.addr = (r_req_q.ar.addr & ~size_mask) + (1 << r_req_q.size);

                  case (r_state_q)
                    R_PASSTHROUGH :
                      mst_r_ready_outstanding[t] = 1'b1;

                    R_INCR_UPSIZE :
                      if (r_req_q.len == 0 || (align_addr(r_req_d.ar.addr) != align_addr(r_req_q.ar.addr)))
                        mst_r_ready_outstanding[t] = 1'b1;
                  endcase // r_state_q

                  if (r_req_q.len == '0) begin
                    r_state_d      = R_IDLE;
                    idqueue_pop[t] = 1'b1;
                  end // if (r_req_q.len == '0)
                end // if (slv_r_ready_outstanding[t])
              end // if (mst_r_valid && (idqueue_id == t) && idqueue_valid)
        endcase // r_state_q
      end // always_comb

      always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
          r_state_q <= R_IDLE;
          r_req_q   <= '0;
        end else begin
          r_state_q <= r_state_d;
          r_req_q   <= r_req_d;
        end
      end
    end
  endgenerate

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
    inject_aw_into_ar_req = 1'b0;

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

      if (slv_aw_valid && slv_aw_atop[5]) begin // ATOP with an R response
        inject_aw_into_ar_req = 1'b1;
        slv_aw_ready = inject_aw_into_ar_gnt;
      end else begin                            // Regular AW
        slv_aw_ready = 1'b1;
      end

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

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      w_state_q <= W_IDLE;
      w_req_q   <= '0;
    end else begin
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
