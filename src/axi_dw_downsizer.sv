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

module axi_dw_downsizer #(
    parameter int unsigned AxiMaxReads = 1    , // Number of outstanding reads
    parameter type aw_chan_t           = logic, // AW Channel Type
    parameter type mst_w_chan_t        = logic, //  W Channel Type for mst port
    parameter type slv_w_chan_t        = logic, //  W Channel Type for slv port
    parameter type b_chan_t            = logic, //  B Channel Type
    parameter type ar_chan_t           = logic, // AR Channel Type
    parameter type mst_r_chan_t        = logic, //  R Channel Type for mst port
    parameter type slv_r_chan_t        = logic  //  R Channel Type for slv port
  ) (
    input  logic        clk_i,
    input  logic        rst_ni,
    // Slave interface
    input  aw_chan_t    slv_aw_i,
    input  logic        slv_aw_valid_i,
    output logic        slv_aw_ready_o,
    input  slv_w_chan_t slv_w_i,
    input  logic        slv_w_valid_i,
    output logic        slv_w_ready_o,
    output b_chan_t     slv_b_o,
    output logic        slv_b_valid_o,
    input  logic        slv_b_ready_i,
    input  ar_chan_t    slv_ar_i,
    input  logic        slv_ar_valid_i,
    output logic        slv_ar_ready_o,
    output slv_r_chan_t slv_r_o,
    output logic        slv_r_valid_o,
    input  logic        slv_r_ready_i,
    // Master interface
    output aw_chan_t    mst_aw_o,
    output logic        mst_aw_valid_o,
    input  logic        mst_aw_ready_i,
    output mst_w_chan_t mst_w_o,
    output logic        mst_w_valid_o,
    input  logic        mst_w_ready_i,
    input  b_chan_t     mst_b_i,
    input  logic        mst_b_valid_i,
    output logic        mst_b_ready_o,
    output ar_chan_t    mst_ar_o,
    output logic        mst_ar_valid_o,
    input  logic        mst_ar_ready_i,
    input  mst_r_chan_t mst_r_i,
    input  logic        mst_r_valid_i,
    output logic        mst_r_ready_o
  );

  import axi_pkg::*;

  `include "axi/typedef.svh"

  /*****************
   *  DEFINITIONS  *
   *****************/

  // Type used to index which adapter is handling each outstanding transaction.
  localparam TranIdWidth = AxiMaxReads > 1 ? $clog2(AxiMaxReads) : 1;
  typedef logic [TranIdWidth-1:0] tran_id_t;

  // Data width
  localparam AxiMstDataWidth = $bits(mst_r_i.data);
  localparam AxiSlvDataWidth = $bits(slv_r_o.data);

  localparam AxiMstStrbWidth = AxiMstDataWidth / 8;
  localparam AxiSlvStrbWidth = AxiSlvDataWidth / 8;

  localparam MstByteMask = AxiMstStrbWidth - 1;

  // Address width
  localparam AxiAddrWidth = $bits(slv_ar_i.addr);
  typedef logic [AxiAddrWidth-1:0] addr_t;

  // ID width
  localparam AxiIdWidth = $bits(slv_ar_i.id);

  // Length of burst after downsizing
  typedef logic [$clog2(AxiSlvStrbWidth/AxiMstStrbWidth) + 7:0] burst_len_t;

  /**************
   *  ARBITERS  *
   **************/

  // R

  slv_r_chan_t [AxiMaxReads-1:0] slv_r_tran;
  logic        [AxiMaxReads-1:0] slv_r_valid_tran;
  logic        [AxiMaxReads-1:0] slv_r_ready_tran;

  rr_arb_tree #(
    .NumIn    (AxiMaxReads ),
    .DataType (slv_r_chan_t),
    .AxiVldRdy(1'b1        ),
    .ExtPrio  (1'b0        ),
    .LockIn   (1'b1        )
  ) i_slv_r_arb (
    .clk_i  (clk_i           ),
    .rst_ni (rst_ni          ),
    .flush_i(1'b0            ),
    .rr_i   ('0              ),
    .req_i  (slv_r_valid_tran),
    .gnt_o  (slv_r_ready_tran),
    .data_i (slv_r_tran      ),
    .gnt_i  (slv_r_ready_i   ),
    .req_o  (slv_r_valid_o   ),
    .data_o (slv_r_o         ),
    .idx_o  (/* Unused */    )
  );

  logic [AxiMaxReads-1:0] mst_r_ready_tran;
  assign mst_r_ready_o = |mst_r_ready_tran;

  // AR

  logic [AxiIdWidth-1:0]  arb_slv_ar_id;
  logic                   arb_slv_ar_req;
  logic                   arb_slv_ar_gnt;
  logic [AxiMaxReads-1:0] arb_slv_ar_gnt_tran;
  // Multiplex AR slave between AR and AW for the injection of atomic operations with an R response.
  logic                   inject_aw_into_ar;
  logic                   inject_aw_into_ar_req;
  logic                   inject_aw_into_ar_gnt;

  assign arb_slv_ar_gnt = |arb_slv_ar_gnt_tran;

  rr_arb_tree #(
    .NumIn     (2         ),
    .DataWidth (AxiIdWidth),
    .ExtPrio   (1'b0      ),
    .AxiVldRdy (1'b1      ),
    .LockIn    (1'b0      )
  ) i_slv_ar_arb (
    .clk_i   (clk_i                                  ),
    .rst_ni  (rst_ni                                 ),
    .flush_i (1'b0                                   ),
    .rr_i    ('0                                     ),
    .req_i   ({inject_aw_into_ar_req, slv_ar_valid_i}),
    .gnt_o   ({inject_aw_into_ar_gnt, slv_ar_ready_o}),
    .data_i  ({slv_aw_i.id, slv_ar_i.id}             ),
    .req_o   (arb_slv_ar_req                         ),
    .gnt_i   (arb_slv_ar_gnt                         ),
    .data_o  (arb_slv_ar_id                          ),
    .idx_o   (inject_aw_into_ar                      )
  );

  ar_chan_t [AxiMaxReads-1:0] mst_ar_tran;
  logic     [AxiMaxReads-1:0] mst_ar_valid_tran;
  logic     [AxiMaxReads-1:0] mst_ar_ready_tran;

  rr_arb_tree #(
    .NumIn    (AxiMaxReads),
    .DataType (ar_chan_t  ),
    .AxiVldRdy(1'b1       ),
    .ExtPrio  (1'b0       ),
    .LockIn   (1'b1       )
  ) i_mst_ar_arb (
    .clk_i  (clk_i            ),
    .rst_ni (rst_ni           ),
    .flush_i(1'b0             ),
    .rr_i   ('0               ),
    .req_i  (mst_ar_valid_tran),
    .gnt_o  (mst_ar_ready_tran),
    .data_i (mst_ar_tran      ),
    .gnt_i  (mst_ar_ready_i   ),
    .req_o  (mst_ar_valid_o   ),
    .data_o (mst_ar_o         ),
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
  logic     [AxiMaxReads-1:0] idle_read_downsizer;
  tran_id_t                   idx_idle_downsizer ;

  if (AxiMaxReads > 1) begin: gen_read_lzc
    lzc #(
      .WIDTH(AxiMaxReads)
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

  logic     [AxiMaxReads-1:0] idqueue_push;
  logic     [AxiMaxReads-1:0] idqueue_pop;
  tran_id_t                   idqueue_id;
  logic                       idqueue_valid;

  id_queue #(
    .ID_WIDTH(AxiIdWidth ),
    .CAPACITY(AxiMaxReads),
    .data_t  (tran_id_t  )
  ) i_read_id_queue (
    .clk_i           (clk_i             ),
    .rst_ni          (rst_ni            ),
    .inp_id_i        (arb_slv_ar_id     ),
    .inp_data_i      (idx_idle_downsizer),
    .inp_req_i       (|idqueue_push     ),
    .inp_gnt_o       (/* Unused  */     ),
    .oup_id_i        (mst_r_i.id        ),
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

  for (genvar t = 0; t < AxiMaxReads; t++) begin: gen_read_downsizer
    r_state_t r_state_d;
    r_state_t r_state_q;

    // Are we idle?
    assign idle_read_downsizer[t] = (r_state_q == R_IDLE);

    struct packed {
      ar_chan_t ar  ;
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
      mst_ar_tran[t]       = r_req_q.ar      ;
      mst_ar_valid_tran[t] = r_req_q.ar_valid;

      // R Channel
      slv_r_tran[t]       = r_req_q.r      ;
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
            r_req_d.ar       = slv_ar_i     ;
            r_req_d.ar_valid = 1'b1         ;
            r_req_d.len      = slv_ar_i.len ;
            r_req_d.size     = slv_ar_i.size;
            if (inject_aw_into_ar) begin
              r_req_d.ar.id     = slv_aw_i.id    ;
              r_req_d.ar.addr   = slv_aw_i.addr  ;
              r_req_d.ar.size   = slv_aw_i.size  ;
              r_req_d.ar.burst  = slv_aw_i.burst ;
              r_req_d.ar.len    = slv_aw_i.len   ;
              r_req_d.ar.lock   = slv_aw_i.lock  ;
              r_req_d.ar.cache  = slv_aw_i.cache ;
              r_req_d.ar.prot   = slv_aw_i.prot  ;
              r_req_d.ar.qos    = slv_aw_i.qos   ;
              r_req_d.ar.region = slv_aw_i.region;
              r_req_d.ar.user   = slv_aw_i.user  ;
              r_req_d.ar_valid  = 1'b0           ; // Injected "AR"s from AW are not valid.
              r_req_d.len       = slv_aw_i.len   ;
              r_req_d.size      = slv_aw_i.size  ;
            end

            if (|(r_req_d.ar.cache & CACHE_MODIFIABLE))
              case (r_req_d.ar.burst)
                BURST_INCR : begin
                  // Evaluate downsize ratio
                  automatic addr_t size_mask  = (1 << r_req_d.ar.size) - 1                                      ;
                  automatic addr_t conv_ratio = ((1 << r_req_d.ar.size) + AxiMstStrbWidth - 1) / AxiMstStrbWidth;

                  // Evaluate output burst length
                  automatic addr_t align_adj = (r_req_d.ar.addr & size_mask & ~MstByteMask) / AxiMstStrbWidth;
                  r_req_d.len                = (r_req_d.ar.len + 1) * conv_ratio - align_adj - 1             ;

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

                if (mst_r_valid_i) begin
                  automatic addr_t mst_offset = r_req_q.ar.addr[(AxiMstStrbWidth == 1 ? 1 : $clog2(AxiMstStrbWidth)) - 1:0];
                  automatic addr_t slv_offset = r_req_q.ar.addr[(AxiSlvStrbWidth == 1 ? 1 : $clog2(AxiSlvStrbWidth)) - 1:0];
                  automatic addr_t size_mask  = (1 << r_req_q.ar.size) - 1                                                 ;

                  // Lane steering
                  for (int b = 0; b < AxiSlvStrbWidth; b++) begin
                    if ((b >= slv_offset) &&
                        (b - slv_offset < (1 << r_req_q.size)) &&
                        (b + mst_offset - slv_offset < AxiMstStrbWidth)) begin
                      r_req_d.r.data[8*b+:8] = mst_r_i.data[8 * (b + mst_offset - slv_offset) +: 8];
                    end
                  end

                  r_req_d.len     = r_req_q.len - 1                                        ;
                  r_req_d.ar.len  = r_req_q.ar.len - 1                                     ;
                  r_req_d.ar.addr = (r_req_q.ar.addr & ~size_mask) + (1 << r_req_q.ar.size);
                  r_req_d.r.last  = (r_req_q.len == 0)                                     ;
                  r_req_d.r.id    = mst_r_i.id                                             ;
                  r_req_d.r.user  = mst_r_i.user                                           ;

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
    aw_chan_t aw  ;
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
    mst_aw_o       = w_req_q.aw      ;
    mst_aw_valid_o = w_req_q.aw_valid;
    slv_aw_ready_o = '0              ;

    // W Channel
    mst_w_o       = '0;
    mst_w_valid_o = '0;
    slv_w_ready_o = '0;

    // B Channel
    // No latency
    slv_b_o       = mst_b_i      ;
    slv_b_valid_o = mst_b_valid_i;
    mst_b_ready_o = slv_b_ready_i;

    // Got a grant on the AW channel
    if (mst_aw_valid_o & mst_aw_ready_i)
      w_req_d.aw_valid = 1'b0;

    case (w_state_q)
      W_PASSTHROUGH, W_INCR_DOWNSIZE, W_SPLIT_INCR_DOWNSIZE: begin
        // Request was accepted
        if (!w_req_q.aw_valid)
          if (slv_w_valid_i) begin
            automatic addr_t mst_offset = w_req_q.aw.addr[(AxiMstStrbWidth == 1 ? 1 : $clog2(AxiMstStrbWidth)) - 1:0];
            automatic addr_t slv_offset = w_req_q.aw.addr[(AxiSlvStrbWidth == 1 ? 1 : $clog2(AxiSlvStrbWidth)) - 1:0];

            // Valid output
            mst_w_valid_o = 1'b1                              ;
            mst_w_o.last  = slv_w_i.last && (w_req_q.len == 0);
            mst_w_o.user  = slv_w_i.user                      ;

            // Serialization
            for (int b = 0; b < AxiSlvStrbWidth; b++)
              if ((b >= slv_offset) &&
                  (b - slv_offset < (1 << w_req_q.aw.size)) &&
                  (b + mst_offset - slv_offset < AxiMstStrbWidth)) begin
                mst_w_o.data[8 * (b + mst_offset - slv_offset) +: 8] = slv_w_i.data[8 * b +: 8];
                mst_w_o.strb[b + mst_offset - slv_offset]            = slv_w_i.strb[b]         ;
              end
          end

        // Acknowledgment
        if (mst_w_ready_i && mst_w_valid_o) begin
          automatic addr_t size_mask = (1 << w_req_q.aw.size) - 1;

          w_req_d.len     = w_req_q.len - 1                                        ;
          w_req_d.aw.len  = w_req_q.aw.len - 1                                     ;
          w_req_d.aw.addr = (w_req_q.aw.addr & ~size_mask) + (1 << w_req_q.aw.size);

          case (w_state_q)
            W_PASSTHROUGH:
              slv_w_ready_o = 1'b1;

            W_INCR_DOWNSIZE, W_SPLIT_INCR_DOWNSIZE:
              if (w_req_q.len == 0 || (aligned_addr(w_req_d.aw.addr, w_req_q.size) != aligned_addr(w_req_q.aw.addr, w_req_q.size)))
                slv_w_ready_o = 1'b1;
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

      if (slv_aw_valid_i && slv_aw_i.atop[5]) begin // ATOP with an R response
        inject_aw_into_ar_req = 1'b1                 ;
        slv_aw_ready_o        = inject_aw_into_ar_gnt;
      end else begin // Regular AW
        slv_aw_ready_o = 1'b1;
      end

      // New write request
      if (slv_aw_valid_i && slv_aw_ready_o) begin
        // Default state
        w_state_d = W_PASSTHROUGH;

        // Save beat
        w_req_d.aw       = slv_aw_i     ;
        w_req_d.aw_valid = 1'b1         ;
        w_req_d.len      = slv_aw_i.len ;
        w_req_d.size     = slv_aw_i.size;

        // Do nothing
        if (|(slv_aw_i.cache & CACHE_MODIFIABLE))
          case (slv_aw_i.burst)
            BURST_INCR: begin
              // Evaluate downsize ratio
              automatic addr_t size_mask  = (1 << slv_aw_i.size) - 1                                      ;
              automatic addr_t conv_ratio = ((1 << slv_aw_i.size) + AxiMstStrbWidth - 1) / AxiMstStrbWidth;

              // Evaluate output burst length
              automatic addr_t align_adj = (slv_aw_i.addr & size_mask & ~MstByteMask) / AxiMstStrbWidth;
              w_req_d.len                = (slv_aw_i.len + 1) * conv_ratio - align_adj - 1             ;

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

endmodule : axi_dw_downsizer
