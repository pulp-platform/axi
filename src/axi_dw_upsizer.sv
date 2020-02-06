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
// Data width upsize conversion.
// Connects a wide master to a narrower slave.

`include "axi/typedef.svh"

module axi_dw_upsizer #(
    parameter int unsigned AxiMaxTrans = 1    , // Number of outstanding reads
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

  /*****************
   *  DEFINITIONS  *
   *****************/

  // Type used to index which adapter is handling each outstanding transaction.
  localparam TranIdWidth = AxiMaxTrans > 1 ? $clog2(AxiMaxTrans) : 1;
  typedef logic [TranIdWidth-1:0] tran_id_t;

  // Data width
  localparam AxiMstDataWidth = $bits(mst_r_i.data);
  localparam AxiSlvDataWidth = $bits(slv_r_o.data);

  localparam AxiMstStrbWidth = AxiMstDataWidth / 8;
  localparam AxiSlvStrbWidth = AxiSlvDataWidth / 8;

  // Address width
  localparam AxiAddrWidth = $bits(slv_ar_i.addr);
  typedef logic [AxiAddrWidth-1:0] addr_t;

  // ID width
  localparam AxiIdWidth = $bits(slv_ar_i.id);

  /**************
   *  ARBITERS  *
   **************/

  // R

  slv_r_chan_t [AxiMaxTrans-1:0] slv_r_tran;
  logic        [AxiMaxTrans-1:0] slv_r_valid_tran;
  logic        [AxiMaxTrans-1:0] slv_r_ready_tran;

  rr_arb_tree #(
    .NumIn    (AxiMaxTrans ),
    .DataType (slv_r_chan_t),
    .ExtPrio  (1'b0        ),
    .AxiVldRdy(1'b1        )
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
    .idx_o  (/* unused */    )
  );

  logic [AxiMaxTrans-1:0] mst_r_ready_tran;
  assign mst_r_ready_o = |mst_r_ready_tran;

  // AR

  logic [AxiIdWidth-1:0]  arb_slv_ar_id;
  logic                   arb_slv_ar_req;
  logic                   arb_slv_ar_gnt;
  logic [AxiMaxTrans-1:0] arb_slv_ar_gnt_tran;
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
    .clk_i  (clk_i                                  ),
    .rst_ni (rst_ni                                 ),
    .flush_i(1'b0                                   ),
    .rr_i   ('0                                     ),
    .req_i  ({inject_aw_into_ar_req, slv_ar_valid_i}),
    .gnt_o  ({inject_aw_into_ar_gnt, slv_ar_ready_o}),
    .data_i ({slv_aw_i.id, slv_ar_i.id}             ),
    .req_o  (arb_slv_ar_req                         ),
    .gnt_i  (arb_slv_ar_gnt                         ),
    .data_o (arb_slv_ar_id                          ),
    .idx_o  (inject_aw_into_ar                      )
  );

  ar_chan_t [AxiMaxTrans-1:0] mst_ar_tran;
  logic     [AxiMaxTrans-1:0] mst_ar_valid_tran;
  logic     [AxiMaxTrans-1:0] mst_ar_ready_tran;

  rr_arb_tree #(
    .NumIn    (AxiMaxTrans),
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
    R_IDLE       ,
    R_PASSTHROUGH,
    R_INCR_UPSIZE
  } r_state_t;

  // Decide which upsizer will handle the incoming AXI transaction
  logic     [AxiMaxTrans-1:0] idle_read_upsizer;
  tran_id_t                   idx_idle_upsizer ;

  if (AxiMaxTrans > 1) begin: gen_read_lzc
    lzc #(
      .WIDTH(AxiMaxTrans)
    ) i_read_lzc (
      .in_i   (idle_read_upsizer),
      .cnt_o  (idx_idle_upsizer ),
      .empty_o(/* Unused */     )
    );
  end else begin: gen_no_read_lzc
    assign idx_idle_upsizer = 1'b0;
  end

  // This ID queue is used to resolve which upsizer is handling
  // each outstanding read transaction

  logic     [AxiMaxTrans-1:0] idqueue_push;
  logic     [AxiMaxTrans-1:0] idqueue_pop;
  tran_id_t                   idqueue_id;
  logic                       idqueue_valid;

  id_queue #(
    .ID_WIDTH(AxiIdWidth ),
    .CAPACITY(AxiMaxTrans),
    .data_t  (tran_id_t  )
  ) i_read_id_queue (
    .clk_i           (clk_i           ),
    .rst_ni          (rst_ni          ),
    .inp_id_i        (arb_slv_ar_id   ),
    .inp_data_i      (idx_idle_upsizer),
    .inp_req_i       (|idqueue_push   ),
    .inp_gnt_o       (/* Unused  */   ),
    .oup_id_i        (mst_r_i.id      ),
    .oup_pop_i       (|idqueue_pop    ),
    .oup_req_i       (1'b1            ),
    .oup_data_o      (idqueue_id      ),
    .oup_data_valid_o(idqueue_valid   ),
    .oup_gnt_o       (/* Unused  */   ),
    .exists_data_i   ('0              ),
    .exists_mask_i   ('0              ),
    .exists_req_i    ('0              ),
    .exists_o        (/* Unused  */   ),
    .exists_gnt_o    (/* Unused  */   )
  );

  for (genvar t = 0; t < AxiMaxTrans; t++) begin: gen_read_upsizer
    r_state_t r_state_d;
    r_state_t r_state_q;

    // Are we idle?
    assign idle_read_upsizer[t] = (r_state_q == R_IDLE);

    struct packed {
      ar_chan_t ar  ;
      logic ar_valid;

      len_t len  ;
      size_t size;
    } r_req_d, r_req_q;

    always_comb begin
      // Maintain state
      r_state_d = r_state_q;
      r_req_d   = r_req_q  ;

      // AR Channel
      mst_ar_tran[t]       = r_req_q.ar      ;
      mst_ar_valid_tran[t] = r_req_q.ar_valid;

      // R Channel
      // No latency
      slv_r_tran[t]      = '0          ;
      slv_r_tran[t].id   = mst_r_i.id  ;
      slv_r_tran[t].resp = mst_r_i.resp;
      slv_r_tran[t].user = mst_r_i.user;

      idqueue_push[t] = 1'b0;
      idqueue_pop[t]  = 1'b0;

      arb_slv_ar_gnt_tran[t] = 1'b0;

      mst_r_ready_tran[t] = 1'b0;
      slv_r_valid_tran[t] = 1'b0;

      // Got a grant on the AR channel
      if (mst_ar_valid_tran[t] && mst_ar_ready_tran[t])
        r_req_d.ar_valid = 1'b0;

      case (r_state_q)
        R_IDLE : begin
          // Reset channels
          r_req_d.ar = '0;

          // New read request
          if (arb_slv_ar_req && (idx_idle_upsizer == t)) begin
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
                  // Evaluate output burst length
                  automatic addr_t size_mask = (1 << r_req_d.ar.size) - 1;

                  automatic addr_t addr_start = aligned_addr(r_req_d.ar.addr, $clog2(AxiMstStrbWidth))                                                     ;
                  automatic addr_t addr_end   = aligned_addr((r_req_d.ar.addr & ~size_mask) + (r_req_d.ar.len << r_req_d.ar.size), $clog2(AxiMstStrbWidth));

                  r_req_d.ar.len  = (addr_end - addr_start) >> $clog2(AxiMstStrbWidth);
                  r_req_d.ar.size = $clog2(AxiMstStrbWidth)                           ;
                  r_state_d       = R_INCR_UPSIZE                                     ;
                end
              endcase
          end
        end

        R_PASSTHROUGH, R_INCR_UPSIZE:
          // Request was accepted
          if (!r_req_q.ar_valid)
            if (mst_r_valid_i && (idqueue_id == t) && idqueue_valid) begin
              automatic addr_t mst_offset = r_req_q.ar.addr[(AxiMstStrbWidth == 1 ? 1 : $clog2(AxiMstStrbWidth)) - 1:0];
              automatic addr_t slv_offset = r_req_q.ar.addr[(AxiSlvStrbWidth == 1 ? 1 : $clog2(AxiSlvStrbWidth)) - 1:0];

              // Valid output
              slv_r_valid_tran[t] = 1'b1                              ;
              slv_r_tran[t].last  = mst_r_i.last && (r_req_q.len == 0);

              // Serialization
              for (int b = 0; b < AxiMstStrbWidth; b++)
                if ((b >= mst_offset) &&
                    (b - mst_offset < (1 << r_req_q.size)) &&
                    (b + slv_offset - mst_offset < AxiSlvStrbWidth)) begin
                  slv_r_tran[t].data[8*(b + slv_offset - mst_offset) +: 8] = mst_r_i.data[8 * b +: 8];
                end

              // Acknowledgment
              if (slv_r_ready_tran[t]) begin
                automatic addr_t size_mask = (1 << r_req_q.size) - 1;

                r_req_d.len     = r_req_q.len - 1                                     ;
                r_req_d.ar.addr = (r_req_q.ar.addr & ~size_mask) + (1 << r_req_q.size);

                case (r_state_q)
                  R_PASSTHROUGH :
                    mst_r_ready_tran[t] = 1'b1;

                  R_INCR_UPSIZE :
                    if (r_req_q.len == 0 || (aligned_addr(r_req_d.ar.addr, $clog2(AxiMstStrbWidth)) != aligned_addr(r_req_q.ar.addr, $clog2(AxiMstStrbWidth))))
                      mst_r_ready_tran[t] = 1'b1;
                endcase

                if (r_req_q.len == '0) begin
                  r_state_d      = R_IDLE;
                  idqueue_pop[t] = 1'b1  ;
                end
              end
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
  end : gen_read_upsizer

  /***********
   *  WRITE  *
   ***********/

  enum logic [1:0] {
    W_IDLE       ,
    W_PASSTHROUGH,
    W_INCR_UPSIZE
  } w_state_d, w_state_q;

  struct packed {
    aw_chan_t aw  ;
    logic aw_valid;

    mst_w_chan_t w;
    logic w_valid ;

    len_t len  ;
    size_t size;
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
    mst_w_o       = w_req_q.w      ;
    mst_w_valid_o = w_req_q.w_valid;
    slv_w_ready_o = '0             ;

    // B Channel
    // No latency
    slv_b_o       = mst_b_i      ;
    slv_b_valid_o = mst_b_valid_i;
    mst_b_ready_o = slv_b_ready_i;

    // Got a grant on the AW channel
    if (mst_aw_valid_o && mst_aw_ready_i)
      w_req_d.aw_valid = 1'b0;

    case (w_state_q)
      W_PASSTHROUGH, W_INCR_UPSIZE: begin
        // Got a grant on the W channel
        if (mst_w_valid_o && mst_w_ready_i)
          w_req_d.w = '0;

        // Request was accepted
        if (!w_req_q.aw_valid) begin
          // Ready if downstream interface is idle, or if it is ready
          slv_w_ready_o = ~mst_w_valid_o || mst_w_ready_i;

          if (slv_w_valid_i && slv_w_ready_o) begin
            automatic addr_t mst_offset = w_req_q.aw.addr[(AxiMstStrbWidth == 1 ? 1 : $clog2(AxiMstStrbWidth)) - 1:0];
            automatic addr_t slv_offset = w_req_q.aw.addr[(AxiSlvStrbWidth == 1 ? 1 : $clog2(AxiSlvStrbWidth)) - 1:0];
            automatic addr_t size_mask  = (1 << w_req_q.size) - 1                                                    ;

            // Lane steering
            for (int b = 0; b < AxiMstStrbWidth; b++)
              if ((b >= mst_offset) &&
                  (b - mst_offset < (1 << w_req_q.size)) &&
                  (b + slv_offset - mst_offset < AxiSlvStrbWidth)) begin
                w_req_d.w.data[8 * b +: 8] = slv_w_i.data[8 * (b + slv_offset - mst_offset) +: 8];
                w_req_d.w.strb[b]          = slv_w_i.strb[b + slv_offset - mst_offset]           ;
              end

            w_req_d.len     = w_req_q.len - 1                                     ;
            w_req_d.aw.addr = (w_req_q.aw.addr & ~size_mask) + (1 << w_req_q.size);
            w_req_d.w.last  = (w_req_q.len == 0)                                  ;
            w_req_d.w.user  = slv_w_i.user                                        ;

            case (w_state_q)
              W_PASSTHROUGH:
                // Forward data as soon as we can
                w_req_d.w_valid = 1'b1;

              W_INCR_UPSIZE:
                // Forward when the burst is finished, or after filling up a word
                if (w_req_q.len == 0 || (aligned_addr(w_req_d.aw.addr, $clog2(AxiMstStrbWidth) != aligned_addr(w_req_q.aw.addr, $clog2(AxiMstStrbWidth)))))
                  w_req_d.w_valid = 1'b1;
            endcase
          end
        end

        if (mst_w_valid_o && mst_w_ready_i)
          if (w_req_q.len == '1) begin
            slv_w_ready_o = 1'b0  ;
            w_state_d     = W_IDLE;
          end
      end
    endcase

    // Can start a new request as soon as w_state_d is W_IDLE
    if (w_state_d == W_IDLE) begin
      // Reset channels
      w_req_d.aw = '0;
      w_req_d.w  = '0;

      if (slv_aw_valid_i && slv_aw_i.atop[5]) begin // ATOP with an R response
        inject_aw_into_ar_req = 1'b1                 ;
        slv_aw_ready_o        = inject_aw_into_ar_gnt;
      end else begin // Regular AW
        slv_aw_ready_o = 1'b1;
      end

      // New write request
      if (slv_aw_valid_i & slv_aw_ready_o) begin
        // Default state
        w_state_d = W_PASSTHROUGH;

        // Save beat
        w_req_d.aw       = slv_aw_i;
        w_req_d.aw_valid = 1'b1    ;

        w_req_d.len  = slv_aw_i.len ;
        w_req_d.size = slv_aw_i.size;

        if (|(slv_aw_i.cache & CACHE_MODIFIABLE))
          case (slv_aw_i.burst)
            BURST_INCR: begin
              // Evaluate output burst length
              automatic addr_t size_mask = (1 << slv_aw_i.size) - 1;

              automatic addr_t addr_start = aligned_addr(slv_aw_i.addr, $clog2(AxiMstStrbWidth))                                                 ;
              automatic addr_t addr_end   = aligned_addr((slv_aw_i.addr & ~size_mask) + (slv_aw_i.len << slv_aw_i.size), $clog2(AxiMstStrbWidth));

              w_req_d.aw.len  = (addr_end - addr_start) >> $clog2(AxiMstStrbWidth);
              w_req_d.aw.size = $clog2(AxiMstStrbWidth)                           ;
              w_state_d       = W_INCR_UPSIZE                                     ;
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
  `ifndef SYNTHESIS
  `ifndef VERILATOR
  if (2**AxiIdWidth < AxiMaxTrans)
    $fatal(1, "Cannot index all requested outstanding reads with the given ID bits!");
  `endif
  `endif

endmodule : axi_dw_upsizer
