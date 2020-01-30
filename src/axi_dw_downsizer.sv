// Copyright 2020 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Author: Matheus Cavalcante <matheusd@iis.ee.ethz.ch>

// Description:
// Data width downsize conversion.
// Connects a narrow master to a wider slave.

`include "axi/typedef.svh"

import axi_pkg::*;

module axi_dw_downsizer #(
    parameter int AxiAddrWidth    = 64,
    parameter int AxiMstDataWidth = 64,
    parameter int AxiSlvDataWidth = 64,
    parameter int AxiMaxTrans     = 1 ,
    parameter int AxiIdWidth      = 4 ,
    parameter int AxiUserWidth    = 1 ,

    // Dependent parameters, do not change!
    parameter AxiMstStrbWidth = AxiMstDataWidth/8          ,
    parameter AxiSlvStrbWidth = AxiSlvDataWidth/8          ,
    parameter type addr_t     = logic [AxiAddrWidth-1:0]   ,
    parameter type slv_data_t = logic [AxiSlvDataWidth-1:0],
    parameter type slv_strb_t = logic [AxiSlvStrbWidth-1:0],
    parameter type mst_data_t = logic [AxiMstDataWidth-1:0],
    parameter type mst_strb_t = logic [AxiMstStrbWidth-1:0],
    parameter type id_t       = logic [AxiIdWidth-1:0]     ,
    parameter type user_t     = logic [AxiUserWidth-1:0]
  ) (
    input  logic      clk_i,
    input  logic      rst_ni,
    // Slave interfae
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
    input  slv_data_t slv_w_data,
    input  slv_strb_t slv_w_strb,
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
    output slv_data_t slv_r_data,
    output resp_t     slv_r_resp,
    output logic      slv_r_last,
    output user_t     slv_r_user,
    output logic      slv_r_valid,
    input  logic      slv_r_ready,
    // Master interface
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
    output mst_data_t mst_w_data,
    output mst_strb_t mst_w_strb,
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
    input  mst_data_t mst_r_data,
    input  resp_t     mst_r_resp,
    input  logic      mst_r_last,
    input  user_t     mst_r_user,
    input  logic      mst_r_valid,
    output logic      mst_r_ready
  );

  /*****************
   *  DEFINITIONS  *
   *****************/

  localparam MstByteMask = AxiMstStrbWidth - 1;

  // Type used to index which adapter is handling each outstanding transaction.
  localparam TranIdWidth = AxiMaxTrans > 1 ? $clog2(AxiMaxTrans) : 1;
  typedef logic [TranIdWidth-1:0] tran_id_t;

  // AXI channel types
  `AXI_TYPEDEF_AW_CHAN_T(ax_chan_t, addr_t, id_t, user_t)            ;
  `AXI_TYPEDEF_W_CHAN_T(mst_w_chan_t, mst_data_t, mst_strb_t, user_t);
  `AXI_TYPEDEF_W_CHAN_T(slv_w_chan_t, slv_data_t, slv_strb_t, user_t);
  `AXI_TYPEDEF_R_CHAN_T(mst_r_chan_t, mst_data_t, mst_strb_t, user_t);
  `AXI_TYPEDEF_R_CHAN_T(slv_r_chan_t, slv_data_t, slv_strb_t, user_t);

  // Length of burst after downsizing
  typedef logic [$clog2(AxiSlvStrbWidth/AxiMstStrbWidth) + 7:0] burst_len_t;

  /**************
   *  ARBITERS  *
   **************/

  // R

  slv_r_chan_t [AxiMaxTrans-1:0] slv_r_tran;
  logic        [AxiMaxTrans-1:0] slv_r_valid_tran;
  logic        [AxiMaxTrans-1:0] slv_r_ready_tran;
  slv_r_chan_t                   arbiter_slv_r;

  assign slv_r_id   = arbiter_slv_r.id  ;
  assign slv_r_data = arbiter_slv_r.data;
  assign slv_r_resp = arbiter_slv_r.resp;
  assign slv_r_last = arbiter_slv_r.last;
  assign slv_r_user = arbiter_slv_r.user;

  rr_arb_tree #(
    .NumIn    (AxiMaxTrans  ),
    .DataType (slv_r_chan_t ),
    .AxiVldRdy(1'b1         ),
    .ExtPrio  (1'b0         ),
    .LockIn   (1'b1         )
  ) i_slv_r_arb (
    .clk_i  (clk_i           ),
    .rst_ni (rst_ni          ),
    .flush_i(1'b0            ),
    .rr_i   ('0              ),
    .req_i  (slv_r_valid_tran),
    .gnt_o  (slv_r_ready_tran),
    .data_i (slv_r_tran      ),
    .gnt_i  (slv_r_ready     ),
    .req_o  (slv_r_valid     ),
    .data_o (arbiter_slv_r   ),
    .idx_o  (/* Unused */    )
  );

  logic [AxiMaxTrans-1:0] mst_r_ready_tran;
  assign mst_r_ready = |mst_r_ready_tran;

  // AR

  ax_chan_t                   slv_ar;
  ax_chan_t                   slv_aw;
  ax_chan_t                   arb_slv_ar;
  logic                       arb_slv_ar_req;
  logic                       arb_slv_ar_gnt;
  logic     [AxiMaxTrans-1:0] arb_slv_ar_gnt_tran;
  // Multiplex AR slave between AR and AW for the injection of atomic operations with an R response.
  logic                       inject_aw_into_ar_req;
  logic                       inject_aw_into_ar_gnt;

  assign arb_slv_ar_gnt = |arb_slv_ar_gnt_tran;
  assign slv_ar         = '{
    id    : slv_ar_id    ,
    addr  : slv_ar_addr  ,
    len   : slv_ar_len   ,
    size  : slv_ar_size  ,
    burst : slv_ar_burst ,
    lock  : slv_ar_lock  ,
    cache : slv_ar_cache ,
    prot  : slv_ar_prot  ,
    qos   : slv_ar_qos   ,
    region: slv_ar_region,
    atop  : '0           ,
    user  : slv_ar_user
  };
  assign slv_aw = '{
    id    : slv_aw_id    ,
    addr  : slv_aw_addr  ,
    len   : slv_aw_len   ,
    size  : slv_aw_size  ,
    burst : slv_aw_burst ,
    lock  : slv_aw_lock  ,
    cache : slv_aw_cache ,
    prot  : slv_aw_prot  ,
    qos   : slv_aw_qos   ,
    region: slv_aw_region,
    atop  : slv_aw_atop  ,
    user  : slv_aw_user
  };

  rr_arb_tree #(
    .NumIn     (2               ),
    .DataWidth ($bits(ax_chan_t)),
    .ExtPrio   (1'b0            ),
    .AxiVldRdy (1'b1            ),
    .LockIn    (1'b0            )
  ) i_slv_ar_arb (
    .clk_i   (clk_i                                ),
    .rst_ni  (rst_ni                               ),
    .flush_i (1'b0                                 ),
    .rr_i    ('0                                   ),
    .req_i   ({inject_aw_into_ar_req, slv_ar_valid}),
    .gnt_o   ({inject_aw_into_ar_gnt, slv_ar_ready}),
    .data_i  ({slv_aw, slv_ar}                     ),
    .req_o   (arb_slv_ar_req                       ),
    .gnt_i   (arb_slv_ar_gnt                       ),
    .data_o  (arb_slv_ar                           ),
    .idx_o   (/* Unused */                         )
  );

  ax_chan_t [AxiMaxTrans-1:0] mst_ar_tran;
  logic     [AxiMaxTrans-1:0] mst_ar_valid_tran;
  logic     [AxiMaxTrans-1:0] mst_ar_ready_tran;
  ax_chan_t                   arb_mst_ar;

  assign mst_ar_id     = arb_mst_ar.id    ;
  assign mst_ar_addr   = arb_mst_ar.addr  ;
  assign mst_ar_len    = arb_mst_ar.len   ;
  assign mst_ar_size   = arb_mst_ar.size  ;
  assign mst_ar_burst  = arb_mst_ar.burst ;
  assign mst_ar_lock   = arb_mst_ar.lock  ;
  assign mst_ar_cache  = arb_mst_ar.cache ;
  assign mst_ar_prot   = arb_mst_ar.prot  ;
  assign mst_ar_qos    = arb_mst_ar.qos   ;
  assign mst_ar_region = arb_mst_ar.region;
  assign mst_ar_user   = arb_mst_ar.user  ;

  rr_arb_tree #(
    .NumIn    (AxiMaxTrans ),
    .DataType (ax_chan_t   ),
    .AxiVldRdy(1'b1        ),
    .ExtPrio  (1'b0        ),
    .LockIn   (1'b1        )
  ) i_mst_ar_arb (
    .clk_i  (clk_i            ),
    .rst_ni (rst_ni           ),
    .flush_i(1'b0             ),
    .rr_i   ('0               ),
    .req_i  (mst_ar_valid_tran),
    .gnt_o  (mst_ar_ready_tran),
    .data_i (mst_ar_tran      ),
    .gnt_i  (mst_ar_ready     ),
    .req_o  (mst_ar_valid     ),
    .data_o (arb_mst_ar       ),
    .idx_o  (/* Unused */     )
  );

  /**********
   *  READ  *
   **********/

  typedef enum logic [1:0] {
    R_IDLE         ,
    R_PASSTHROUGH  ,
    R_INCR_DOWNSIZE,
    R_SPLIT_INCR_DOWNSIZE
  } r_state_t;

  // Decide which downsizer will handle the incoming AXI transaction
  logic     [AxiMaxTrans-1:0] idle_read_downsizer;
  tran_id_t                   idx_idle_downsizer ;

  if (AxiMaxTrans > 1) begin: gen_read_lzc
    lzc #(
      .WIDTH(AxiMaxTrans)
    ) i_read_lzc (
      .in_i   (idle_read_downsizer),
      .cnt_o  (idx_idle_downsizer ),
      .empty_o(/* Unused */       )
    );
  end else begin: gen_no_read_lzc
    assign idx_idle_downsizer = 1'b0;
  end

  // This ID queue is used to resolve which downsizer is handling
  // each outstanding read transaction.

  logic     [AxiMaxTrans-1:0] idqueue_push;
  logic     [AxiMaxTrans-1:0] idqueue_pop;
  tran_id_t                   idqueue_id;
  logic                       idqueue_valid;

  id_queue #(
    .ID_WIDTH(AxiIdWidth ),
    .CAPACITY(AxiMaxTrans),
    .data_t  (tran_id_t  )
  ) i_read_id_queue (
    .clk_i           (clk_i             ),
    .rst_ni          (rst_ni            ),
    .inp_id_i        (arb_slv_ar.id     ),
    .inp_data_i      (idx_idle_downsizer),
    .inp_req_i       (|idqueue_push     ),
    .inp_gnt_o       (/* Unused  */     ),
    .oup_id_i        (mst_r_id          ),
    .oup_pop_i       (|idqueue_pop      ),
    .oup_req_i       (1'b1              ),
    .oup_data_o      (idqueue_id        ),
    .oup_data_valid_o(idqueue_valid     ),
    .oup_gnt_o       (/* Unused  */     ),
    .exists_data_i   ('0                ),
    .exists_mask_i   ('0                ),
    .exists_req_i    ('0                ),
    .exists_o        (/* Unused  */     ),
    .exists_gnt_o    (/* Unused  */     )
  );

  for (genvar t = 0; t < AxiMaxTrans; t++) begin: gen_read_downsizer
    r_state_t r_state_d;
    r_state_t r_state_q;

    // Are we idle?
    assign idle_read_downsizer[t] = (r_state_q == R_IDLE);

    struct packed {
      ax_chan_t ar  ;
      logic ar_valid;

      slv_r_chan_t r;
      logic r_valid ;

      burst_len_t len;
      size_t size    ;
    } r_req_d, r_req_q;

    always_comb begin
      // Maintain state
      r_state_d = r_state_q;
      r_req_d   = r_req_q  ;

      // AR Channel
      mst_ar_tran[t]        = '0              ;
      mst_ar_tran[t].id     = r_req_q.ar.id   ;
      mst_ar_tran[t].addr   = r_req_q.ar.addr ;
      mst_ar_tran[t].len    = r_req_q.ar.len  ;
      mst_ar_tran[t].size   = r_req_q.ar.size ;
      mst_ar_tran[t].burst  = r_req_q.ar.burst;
      mst_ar_tran[t].lock   = r_req_q.ar.lock ;
      mst_ar_tran[t].cache  = r_req_q.ar.cache;
      mst_ar_tran[t].prot   = r_req_q.ar.prot ;
      mst_ar_tran[t].qos    = r_req_q.ar.qos  ;
      mst_ar_tran[t].region = r_req_q.ar.prot ;
      mst_ar_tran[t].user   = r_req_q.ar.user ;
      mst_ar_valid_tran[t]  = r_req_q.ar_valid;

      // R Channel
      slv_r_tran[t].id    = r_req_q.r.id   ;
      slv_r_tran[t].data  = r_req_q.r.data ;
      slv_r_tran[t].resp  = r_req_q.r.resp ;
      slv_r_tran[t].last  = r_req_q.r.last ;
      slv_r_tran[t].user  = r_req_q.r.user ;
      slv_r_valid_tran[t] = r_req_q.r_valid;

      idqueue_push[t] = '0;
      idqueue_pop[t]  = '0;

      arb_slv_ar_gnt_tran[t] = 1'b0;

      mst_r_ready_tran[t] = 1'b0;

      // Got a grant on the AR channel
      if (mst_ar_valid_tran[t] & mst_ar_ready_tran[t])
        r_req_d.ar_valid = 1'b0;

      case (r_state_q)
        R_IDLE : begin
          // Reset channels
          r_req_d.ar = '0;
          r_req_d.r  = '0;

          // New write request
          if (arb_slv_ar_req && (idx_idle_downsizer == t)) begin
            arb_slv_ar_gnt_tran[t] = 1'b1;
            // Push to ID queue
            idqueue_push[t]        = 1'b1;

            // Default state
            r_state_d = R_PASSTHROUGH;

            // Save beat
            r_req_d.ar        = '0                 ;
            r_req_d.ar.id     = arb_slv_ar.id      ;
            r_req_d.ar.addr   = arb_slv_ar.addr    ;
            r_req_d.ar.size   = arb_slv_ar.size    ;
            r_req_d.ar.burst  = arb_slv_ar.burst   ;
            r_req_d.ar.len    = arb_slv_ar.len     ;
            r_req_d.ar.lock   = arb_slv_ar.lock    ;
            r_req_d.ar.cache  = arb_slv_ar.cache   ;
            r_req_d.ar.prot   = arb_slv_ar.prot    ;
            r_req_d.ar.qos    = arb_slv_ar.qos     ;
            r_req_d.ar.region = arb_slv_ar.region  ;
            r_req_d.ar.user   = arb_slv_ar.user    ;
            r_req_d.ar_valid  = &(~arb_slv_ar.atop); // Injected "AR"s from AW are not valid.
            r_req_d.len       = arb_slv_ar.len     ;
            r_req_d.size      = arb_slv_ar.size    ;

            if (|(arb_slv_ar.cache & CACHE_MODIFIABLE))
              case (arb_slv_ar.burst)
                BURST_INCR : begin
                  // Evaluate downsize ratio
                  automatic addr_t size_mask  = (1 << arb_slv_ar.size) - 1                                      ;
                  automatic addr_t conv_ratio = ((1 << arb_slv_ar.size) + AxiMstStrbWidth - 1) / AxiMstStrbWidth;

                  // Evaluate output burst length
                  automatic addr_t align_adj = (arb_slv_ar.addr & size_mask & ~MstByteMask) / AxiMstStrbWidth;
                  r_req_d.len                = (arb_slv_ar.len + 1) * conv_ratio - align_adj - 1             ;

                  if (conv_ratio != 1) begin
                    r_req_d.ar.size = $clog2(AxiMstStrbWidth);

                    if (r_req_d.len <= 255) begin
                      r_state_d      = R_INCR_DOWNSIZE;
                      r_req_d.ar.len = r_req_d.len    ;
                    end else begin
                      r_state_d      = R_SPLIT_INCR_DOWNSIZE;
                      r_req_d.ar.len = 255 - align_adj      ;
                    end
                  end
                end
              endcase
          end
        end

        R_PASSTHROUGH, R_INCR_DOWNSIZE, R_SPLIT_INCR_DOWNSIZE: begin
          // Got a grant on the R channel
          if (slv_r_valid_tran[t] && slv_r_ready_tran[t])
            r_req_d.r = '0;

          // Request was accepted
          if (!r_req_q.ar_valid)
            // Our turn
            if ((idqueue_id == t) && idqueue_valid)
              // Ready to accept more data
              if (!slv_r_valid_tran[t] || (slv_r_valid_tran[t] && slv_r_ready_tran[t])) begin
                mst_r_ready_tran[t] = 1'b1;

                if (mst_r_valid) begin
                  automatic addr_t mst_offset = r_req_q.ar.addr[(AxiMstStrbWidth == 1 ? 1 : $clog2(AxiMstStrbWidth)) - 1:0];
                  automatic addr_t slv_offset = r_req_q.ar.addr[(AxiSlvStrbWidth == 1 ? 1 : $clog2(AxiSlvStrbWidth)) - 1:0];
                  automatic addr_t size_mask  = (1 << r_req_q.ar.size) - 1                                                 ;

                  // Lane steering
                  for (int b = 0; b < AxiSlvStrbWidth; b++) begin
                    if ((b >= slv_offset) &&
                        (b - slv_offset < (1 << r_req_q.size)) &&
                        (b + mst_offset - slv_offset < AxiMstStrbWidth)) begin
                      r_req_d.r.data[8*b+:8] = mst_r_data[8 * (b + mst_offset - slv_offset) +: 8];
                    end
                  end

                  r_req_d.len     = r_req_q.len - 1                                        ;
                  r_req_d.ar.len  = r_req_q.ar.len - 1                                     ;
                  r_req_d.ar.addr = (r_req_q.ar.addr & ~size_mask) + (1 << r_req_q.ar.size);
                  r_req_d.r.last  = (r_req_q.len == 0)                                     ;
                  r_req_d.r.id    = mst_r_id                                               ;
                  r_req_d.r.user  = mst_r_user                                             ;

                  if (r_req_q.len == 0)
                    idqueue_pop[t] = 1'b1;

                  case (r_state_q)
                    R_PASSTHROUGH :
                      // Forward data as soon as we can
                      r_req_d.r_valid = 1'b1;

                    R_INCR_DOWNSIZE, R_SPLIT_INCR_DOWNSIZE:
                      // Forward when the burst is finished, or after filling up a word
                      if (r_req_q.len == 0 || (aligned_addr(r_req_d.ar.addr, r_req_q.size) != aligned_addr(r_req_q.ar.addr, r_req_q.size)))
                        r_req_d.r_valid = 1'b1;
                  endcase

                  // Trigger another burst request, if needed
                  if (r_state_q == R_SPLIT_INCR_DOWNSIZE)
                    // Finished current burst, but whole transaction hasn't finished
                    if (r_req_q.ar.len == '0 && r_req_q.len != '0) begin
                      r_req_d.ar_valid = 1'b1;
                      r_req_d.ar.len   = (r_req_d.len <= 255) ? r_req_d.len : 255;
                    end
                end
              end

          if (slv_r_valid_tran[t] && slv_r_ready_tran[t])
            if (r_req_q.len == '1)
              r_state_d = R_IDLE;
        end
      endcase
    end

    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        r_state_q <= R_IDLE;
        r_req_q   <= '0    ;
      end else begin
        r_state_q <= r_state_d;
        r_req_q   <= r_req_d  ;
      end
    end
  end : gen_read_downsizer

  /***********
   *  WRITE  *
   ***********/

  enum logic [1:0] {
    W_IDLE         ,
    W_PASSTHROUGH  ,
    W_INCR_DOWNSIZE,
    W_SPLIT_INCR_DOWNSIZE
  } w_state_d, w_state_q;

  struct packed {
    ax_chan_t aw  ;
    logic aw_valid;

    burst_len_t len;
    size_t size    ;
  } w_req_d, w_req_q;

  always_comb begin
    inject_aw_into_ar_req = 1'b0;

    // Maintain state
    w_state_d = w_state_q;
    w_req_d   = w_req_q  ;

    // AW Channel
    mst_aw_id     = w_req_q.aw.id    ;
    mst_aw_addr   = w_req_q.aw.addr  ;
    mst_aw_len    = w_req_q.aw.len   ;
    mst_aw_size   = w_req_q.aw.size  ;
    mst_aw_burst  = w_req_q.aw.burst ;
    mst_aw_lock   = w_req_q.aw.lock  ;
    mst_aw_cache  = w_req_q.aw.cache ;
    mst_aw_prot   = w_req_q.aw.prot  ;
    mst_aw_qos    = w_req_q.aw.qos   ;
    mst_aw_region = w_req_q.aw.region;
    mst_aw_atop   = w_req_q.aw.atop  ;
    mst_aw_user   = w_req_q.aw.user  ;
    mst_aw_valid  = w_req_q.aw_valid ;
    slv_aw_ready  = '0               ;

    // W Channel
    mst_w_data  = '0;
    mst_w_strb  = '0;
    mst_w_last  = '0;
    mst_w_user  = '0;
    mst_w_valid = '0;
    slv_w_ready = '0;

    // B Channel
    // No latency
    slv_b_id    = mst_b_id   ;
    slv_b_resp  = mst_b_resp ;
    slv_b_user  = mst_b_user ;
    slv_b_valid = mst_b_valid;
    mst_b_ready = slv_b_ready;

    // Got a grant on the AW channel
    if (mst_aw_valid & mst_aw_ready)
      w_req_d.aw_valid = 1'b0;

    case (w_state_q)
      W_PASSTHROUGH, W_INCR_DOWNSIZE, W_SPLIT_INCR_DOWNSIZE: begin
        // Request was accepted
        if (!w_req_q.aw_valid)
          if (slv_w_valid) begin
            automatic addr_t mst_offset = w_req_q.aw.addr[(AxiMstStrbWidth == 1 ? 1 : $clog2(AxiMstStrbWidth)) - 1:0];
            automatic addr_t slv_offset = w_req_q.aw.addr[(AxiSlvStrbWidth == 1 ? 1 : $clog2(AxiSlvStrbWidth)) - 1:0];

            // Valid output
            mst_w_valid = 1'b1                            ;
            mst_w_last  = slv_w_last && (w_req_q.len == 0);
            mst_w_user  = slv_w_user                      ;

            // Serialization
            for (int b = 0; b < AxiSlvStrbWidth; b++)
              if ((b >= slv_offset) &&
                  (b - slv_offset < (1 << w_req_q.aw.size)) &&
                  (b + mst_offset - slv_offset < AxiMstStrbWidth)) begin
                mst_w_data[8 * (b + mst_offset - slv_offset) +: 8] = slv_w_data[8 * b +: 8];
                mst_w_strb[b + mst_offset - slv_offset]            = slv_w_strb[b]         ;
              end
          end

        // Acknowledgment
        if (mst_w_ready && mst_w_valid) begin
          automatic addr_t size_mask = (1 << w_req_q.aw.size) - 1;

          w_req_d.len     = w_req_q.len - 1                                        ;
          w_req_d.aw.len  = w_req_q.aw.len - 1                                     ;
          w_req_d.aw.addr = (w_req_q.aw.addr & ~size_mask) + (1 << w_req_q.aw.size);

          case (w_state_q)
            W_PASSTHROUGH:
              slv_w_ready = 1'b1;

            W_INCR_DOWNSIZE, W_SPLIT_INCR_DOWNSIZE:
              if (w_req_q.len == 0 || (aligned_addr(w_req_d.aw.addr, w_req_q.size) != aligned_addr(w_req_q.aw.addr, w_req_q.size)))
                slv_w_ready = 1'b1;
          endcase

          // Trigger another burst request, if needed
          if (w_state_q == W_SPLIT_INCR_DOWNSIZE)
            // Finished current burst, but whole transaction hasn't finished
            if (w_req_q.aw.len == '0 && w_req_q.len != '0) begin
              w_req_d.aw_valid = 1'b1;
              w_req_d.aw.len   = (w_req_d.len <= 255) ? w_req_d.len : 255;
            end

          if (w_req_q.len == 0)
            w_state_d = W_IDLE;
        end
      end
    endcase

    // Can start a new request as soon as w_state_d is W_IDLE
    if (w_state_d == W_IDLE) begin
      // Reset channels
      w_req_d.aw = '0;

      if (slv_aw_valid && slv_aw_atop[5]) begin // ATOP with an R response
        inject_aw_into_ar_req = 1'b1                 ;
        slv_aw_ready          = inject_aw_into_ar_gnt;
      end else begin // Regular AW
        slv_aw_ready = 1'b1;
      end

      // New write request
      if (slv_aw_valid && slv_aw_ready) begin
        // Default state
        w_state_d = W_PASSTHROUGH;

        // Save beat
        w_req_d.aw.id     = slv_aw_id    ;
        w_req_d.aw.addr   = slv_aw_addr  ;
        w_req_d.aw.size   = slv_aw_size  ;
        w_req_d.aw.burst  = slv_aw_burst ;
        w_req_d.aw.len    = slv_aw_len   ;
        w_req_d.aw.lock   = slv_aw_lock  ;
        w_req_d.aw.cache  = slv_aw_cache ;
        w_req_d.aw.prot   = slv_aw_prot  ;
        w_req_d.aw.qos    = slv_aw_qos   ;
        w_req_d.aw.region = slv_aw_region;
        w_req_d.aw.atop   = slv_aw_atop  ;
        w_req_d.aw.user   = slv_aw_user  ;
        w_req_d.aw_valid  = 1'b1         ;

        w_req_d.len  = slv_aw_len ;
        w_req_d.size = slv_aw_size;

        // Do nothing
        if (|(slv_aw_cache & CACHE_MODIFIABLE))
          case (slv_aw_burst)
            BURST_INCR: begin
              // Evaluate downsize ratio
              automatic addr_t size_mask  = (1 << slv_aw_size) - 1                                      ;
              automatic addr_t conv_ratio = ((1 << slv_aw_size) + AxiMstStrbWidth - 1) / AxiMstStrbWidth;

              // Evaluate output burst length
              automatic addr_t align_adj = (slv_aw_addr & size_mask & ~MstByteMask) / AxiMstStrbWidth;
              w_req_d.len                = (slv_aw_len + 1) * conv_ratio - align_adj - 1             ;

              if (conv_ratio != 1) begin
                w_req_d.aw.size = $clog2(AxiMstStrbWidth);

                if (w_req_d.len <= 255) begin
                  w_state_d      = W_INCR_DOWNSIZE;
                  w_req_d.aw.len = w_req_d.len    ;
                end else begin
                  w_state_d      = W_SPLIT_INCR_DOWNSIZE;
                  w_req_d.aw.len = 255 - align_adj      ;
                end
              end
            end
          endcase
      end
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      w_state_q <= W_IDLE;
      w_req_q   <= '0    ;
    end else begin
      w_state_q <= w_state_d;
      w_req_q   <= w_req_d  ;
    end
  end

  /****************
   *  ASSERTIONS  *
   ****************/

  // Validate parameters.
  `ifndef VERILATOR
  `ifndef SYNTHESIS
  initial begin: validate_params
    assert(AxiSlvDataWidth > AxiMstDataWidth)
    else $fatal(1, "Data downsizer not being used for downsizing.");

    assert (2**AxiIdWidth >= AxiMaxTrans)
    else $fatal(1, "The outstanding transactions could not be indexed with the given ID bits!");
  end : validate_params
  `endif
  `endif

endmodule : axi_dw_downsizer
