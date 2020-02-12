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

module axi_dw_upsizer #(
    parameter int unsigned AxiMaxReads = 1    , // Number of outstanding reads
    parameter type aw_chan_t           = logic, // AW Channel Type
    parameter type mst_w_chan_t        = logic, //  W Channel Type for mst port
    parameter type slv_w_chan_t        = logic, //  W Channel Type for slv port
    parameter type b_chan_t            = logic, //  B Channel Type
    parameter type ar_chan_t           = logic, // AR Channel Type
    parameter type mst_r_chan_t        = logic, //  R Channel Type for mst port
    parameter type slv_r_chan_t        = logic, //  R Channel Type for slv port
    parameter type axi_mst_req_t       = logic, // AXI Request Type for mst ports
    parameter type axi_mst_resp_t      = logic, // AXI Response Type for mst ports
    parameter type axi_slv_req_t       = logic, // AXI Request Type for mst ports
    parameter type axi_slv_resp_t      = logic  // AXI Response Type for mst ports
  ) (
    input  logic          clk_i,
    input  logic          rst_ni,
    // Slave interface
    input  axi_slv_req_t  slv_req_i,
    output axi_slv_resp_t slv_resp_o,
    // Master interface
    output axi_mst_req_t  mst_req_o,
    input  axi_mst_resp_t mst_resp_i
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
  localparam AxiMstDataWidth = $bits(mst_resp_i.r.data);
  localparam AxiSlvDataWidth = $bits(slv_resp_o.r.data);

  localparam AxiMstStrbWidth = AxiMstDataWidth / 8;
  localparam AxiSlvStrbWidth = AxiSlvDataWidth / 8;

  // Address width
  localparam AxiAddrWidth = $bits(slv_req_i.ar.addr);
  typedef logic [AxiAddrWidth-1:0] addr_t;

  // ID width
  localparam AxiIdWidth = $bits(slv_req_i.ar.id);

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
    .ExtPrio  (1'b0        ),
    .AxiVldRdy(1'b1        )
  ) i_slv_r_arb (
    .clk_i  (clk_i             ),
    .rst_ni (rst_ni            ),
    .flush_i(1'b0              ),
    .rr_i   ('0                ),
    .req_i  (slv_r_valid_tran  ),
    .gnt_o  (slv_r_ready_tran  ),
    .data_i (slv_r_tran        ),
    .gnt_i  (slv_req_i.r_ready ),
    .req_o  (slv_resp_o.r_valid),
    .data_o (slv_resp_o.r      ),
    .idx_o  (/* unused */      )
  );

  logic [AxiMaxReads-1:0] mst_r_ready_tran;
  assign mst_req_o.r_ready = |mst_r_ready_tran;

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
    .clk_i  (clk_i                                       ),
    .rst_ni (rst_ni                                      ),
    .flush_i(1'b0                                        ),
    .rr_i   ('0                                          ),
    .req_i  ({inject_aw_into_ar_req, slv_req_i.ar_valid} ),
    .gnt_o  ({inject_aw_into_ar_gnt, slv_resp_o.ar_ready}),
    .data_i ({slv_req_i.aw.id, slv_req_i.ar.id}          ),
    .req_o  (arb_slv_ar_req                              ),
    .gnt_i  (arb_slv_ar_gnt                              ),
    .data_o (arb_slv_ar_id                               ),
    .idx_o  (inject_aw_into_ar                           )
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
    .clk_i  (clk_i              ),
    .rst_ni (rst_ni             ),
    .flush_i(1'b0               ),
    .rr_i   ('0                 ),
    .req_i  (mst_ar_valid_tran  ),
    .gnt_o  (mst_ar_ready_tran  ),
    .data_i (mst_ar_tran        ),
    .gnt_i  (mst_resp_i.ar_ready),
    .req_o  (mst_req_o.ar_valid ),
    .data_o (mst_req_o.ar       ),
    .idx_o  (/* Unused */       )
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
  logic     [AxiMaxReads-1:0] idle_read_upsizer;
  tran_id_t                   idx_idle_upsizer ;

  if (AxiMaxReads > 1) begin: gen_read_lzc
    lzc #(
      .WIDTH(AxiMaxReads)
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

  logic     [AxiMaxReads-1:0] idqueue_push;
  logic     [AxiMaxReads-1:0] idqueue_pop;
  tran_id_t                   idqueue_id;
  logic                       idqueue_valid;

  id_queue #(
    .ID_WIDTH(AxiIdWidth ),
    .CAPACITY(AxiMaxReads),
    .data_t  (tran_id_t  )
  ) i_read_id_queue (
    .clk_i           (clk_i           ),
    .rst_ni          (rst_ni          ),
    .inp_id_i        (arb_slv_ar_id   ),
    .inp_data_i      (idx_idle_upsizer),
    .inp_req_i       (|idqueue_push   ),
    .inp_gnt_o       (/* Unused  */   ),
    .oup_id_i        (mst_resp_i.r.id ),
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

  for (genvar t = 0; t < AxiMaxReads; t++) begin: gen_read_upsizer
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
      slv_r_tran[t]      = '0               ;
      slv_r_tran[t].id   = mst_resp_i.r.id  ;
      slv_r_tran[t].resp = mst_resp_i.r.resp;
      slv_r_tran[t].user = mst_resp_i.r.user;

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
            r_req_d.ar       = slv_req_i.ar     ;
            r_req_d.ar_valid = 1'b1             ;
            r_req_d.len      = slv_req_i.ar.len ;
            r_req_d.size     = slv_req_i.ar.size;
            if (inject_aw_into_ar) begin
              r_req_d.ar.id     = slv_req_i.aw.id    ;
              r_req_d.ar.addr   = slv_req_i.aw.addr  ;
              r_req_d.ar.size   = slv_req_i.aw.size  ;
              r_req_d.ar.burst  = slv_req_i.aw.burst ;
              r_req_d.ar.len    = slv_req_i.aw.len   ;
              r_req_d.ar.lock   = slv_req_i.aw.lock  ;
              r_req_d.ar.cache  = slv_req_i.aw.cache ;
              r_req_d.ar.prot   = slv_req_i.aw.prot  ;
              r_req_d.ar.qos    = slv_req_i.aw.qos   ;
              r_req_d.ar.region = slv_req_i.aw.region;
              r_req_d.ar.user   = slv_req_i.aw.user  ;
              r_req_d.ar_valid  = 1'b0               ; // Injected "AR"s from AW are not valid.
              r_req_d.len       = slv_req_i.aw.len   ;
              r_req_d.size      = slv_req_i.aw.size  ;
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
            if (mst_resp_i.r_valid && (idqueue_id == t) && idqueue_valid) begin
              automatic addr_t mst_offset = r_req_q.ar.addr[(AxiMstStrbWidth == 1 ? 1 : $clog2(AxiMstStrbWidth)) - 1:0];
              automatic addr_t slv_offset = r_req_q.ar.addr[(AxiSlvStrbWidth == 1 ? 1 : $clog2(AxiSlvStrbWidth)) - 1:0];

              // Valid output
              slv_r_valid_tran[t] = 1'b1                                   ;
              slv_r_tran[t].last  = mst_resp_i.r.last && (r_req_q.len == 0);

              // Serialization
              for (int b = 0; b < AxiMstStrbWidth; b++)
                if ((b >= mst_offset) &&
                    (b - mst_offset < (1 << r_req_q.size)) &&
                    (b + slv_offset - mst_offset < AxiSlvStrbWidth)) begin
                  slv_r_tran[t].data[8*(b + slv_offset - mst_offset) +: 8] = mst_resp_i.r.data[8 * b +: 8];
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
    mst_req_o.aw        = w_req_q.aw      ;
    mst_req_o.aw_valid  = w_req_q.aw_valid;
    slv_resp_o.aw_ready = '0              ;

    // W Channel
    mst_req_o.w        = w_req_q.w      ;
    mst_req_o.w_valid  = w_req_q.w_valid;
    slv_resp_o.w_ready = '0             ;

    // B Channel
    // No latency
    slv_resp_o.b       = mst_resp_i.b      ;
    slv_resp_o.b_valid = mst_resp_i.b_valid;
    mst_req_o.b_ready  = slv_req_i.b_ready ;

    // Got a grant on the AW channel
    if (mst_req_o.aw_valid && mst_resp_i.aw_ready)
      w_req_d.aw_valid = 1'b0;

    case (w_state_q)
      W_PASSTHROUGH, W_INCR_UPSIZE: begin
        // Got a grant on the W channel
        if (mst_req_o.w_valid && mst_resp_i.w_ready)
          w_req_d.w = '0;

        // Request was accepted
        if (!w_req_q.aw_valid) begin
          // Ready if downstream interface is idle, or if it is ready
          slv_resp_o.w_ready = ~mst_req_o.w_valid || mst_resp_i.w_ready;

          if (slv_req_i.w_valid && slv_resp_o.w_ready) begin
            automatic addr_t mst_offset = w_req_q.aw.addr[(AxiMstStrbWidth == 1 ? 1 : $clog2(AxiMstStrbWidth)) - 1:0];
            automatic addr_t slv_offset = w_req_q.aw.addr[(AxiSlvStrbWidth == 1 ? 1 : $clog2(AxiSlvStrbWidth)) - 1:0];
            automatic addr_t size_mask  = (1 << w_req_q.size) - 1                                                    ;

            // Lane steering
            for (int b = 0; b < AxiMstStrbWidth; b++)
              if ((b >= mst_offset) &&
                  (b - mst_offset < (1 << w_req_q.size)) &&
                  (b + slv_offset - mst_offset < AxiSlvStrbWidth)) begin
                w_req_d.w.data[8 * b +: 8] = slv_req_i.w.data[8 * (b + slv_offset - mst_offset) +: 8];
                w_req_d.w.strb[b]          = slv_req_i.w.strb[b + slv_offset - mst_offset]           ;
              end

            w_req_d.len     = w_req_q.len - 1                                     ;
            w_req_d.aw.addr = (w_req_q.aw.addr & ~size_mask) + (1 << w_req_q.size);
            w_req_d.w.last  = (w_req_q.len == 0)                                  ;
            w_req_d.w.user  = slv_req_i.w.user                                    ;

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

        if (mst_req_o.w_valid && mst_resp_i.w_ready)
          if (w_req_q.len == '1) begin
            slv_resp_o.w_ready = 1'b0  ;
            w_state_d          = W_IDLE;
          end
      end
    endcase

    // Can start a new request as soon as w_state_d is W_IDLE
    if (w_state_d == W_IDLE) begin
      // Reset channels
      w_req_d.aw = '0;
      w_req_d.w  = '0;

      if (slv_req_i.aw_valid && slv_req_i.aw.atop[5]) begin // ATOP with an R response
        inject_aw_into_ar_req = 1'b1                 ;
        slv_resp_o.aw_ready   = inject_aw_into_ar_gnt;
      end else begin // Regular AW
        slv_resp_o.aw_ready = 1'b1;
      end

      // New write request
      if (slv_req_i.aw_valid & slv_resp_o.aw_ready) begin
        // Default state
        w_state_d = W_PASSTHROUGH;

        // Save beat
        w_req_d.aw       = slv_req_i.aw;
        w_req_d.aw_valid = 1'b1        ;

        w_req_d.len  = slv_req_i.aw.len ;
        w_req_d.size = slv_req_i.aw.size;

        if (|(slv_req_i.aw.cache & CACHE_MODIFIABLE))
          case (slv_req_i.aw.burst)
            BURST_INCR: begin
              // Evaluate output burst length
              automatic addr_t size_mask = (1 << slv_req_i.aw.size) - 1;

              automatic addr_t addr_start = aligned_addr(slv_req_i.aw.addr, $clog2(AxiMstStrbWidth))                                                         ;
              automatic addr_t addr_end   = aligned_addr((slv_req_i.aw.addr & ~size_mask) + (slv_req_i.aw.len << slv_req_i.aw.size), $clog2(AxiMstStrbWidth));

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

endmodule : axi_dw_upsizer
