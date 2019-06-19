// Copyright (c) 2019 ETH Zurich, University of Bologna
//
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

`include "axi/assign.svh"

module axi_burst_splitter #(
  // Maximum number of AXI read bursts outstanding at the same time
  parameter int unsigned MAX_READ_TXNS = 0,
  // AXI Bus Parameters
  parameter type addr_t = logic,
  parameter type id_t = logic,
  parameter type user_t = logic
) (
  input  logic clk_i,
  input  logic rst_ni,

  AXI_BUS.Slave   slv,
  AXI_BUS.Master  mst
);

  // AW Channel
  typedef struct packed {
    id_t              id;
    addr_t            addr;
    axi_pkg::len_t    len;
    axi_pkg::size_t   size;
    axi_pkg::burst_t  burst;
    logic             lock;
    axi_pkg::cache_t  cache;
    axi_pkg::prot_t   prot;
    axi_pkg::qos_t    qos;
    axi_pkg::region_t region;
    axi_pkg::atop_t   atop;
    user_t            user;
  } aw_chan_t;
  aw_chan_t aw_d, aw_q, slv_aw, mst_aw;

  `AXI_ASSIGN_TO_AW(slv_aw, slv);
  `AXI_ASSIGN_FROM_AW(mst, mst_aw);

  enum logic {AwIdle, AwBusy} aw_state_d, aw_state_q;
  always_comb begin
    aw_d = aw_q;
    aw_state_d = aw_state_q;
    mst.aw_valid = 1'b0;
    mst_aw = 'x;
    slv.aw_ready = 1'b0;

    case (aw_state_q)
      AwIdle: begin
        if (slv.aw_valid) begin
          if (slv.aw_len == '0) begin // No splitting required -> feed through.
            mst_aw = slv_aw;
            mst.aw_valid = 1'b1;
            // Acknowledge upstream as soon as downstream is ready.
            slv.aw_ready = mst.aw_ready;
          end else begin
            // Store AW and acknowledge upstream.
            aw_d = slv_aw;
            slv.aw_ready = 1'b1;
            // Try to feed first burst through.
            mst_aw = aw_d;
            mst_aw.len = '0;
            mst.aw_valid = 1'b1;
            if (mst.aw_ready) begin
              // Reduce number of bursts still to be sent by one.
              aw_d.len--;
              if (aw_d.burst == axi_pkg::BURST_INCR) begin
                aw_d.addr += (1 << aw_d.size);
              end
            end
            aw_state_d = AwBusy;
          end
        end
      end
      AwBusy: begin
        // Send next burst from split.
        mst_aw = aw_q;
        mst_aw.len = '0;
        mst.aw_valid = 1'b1;
        if (mst.aw_ready) begin
          if (aw_q.len == '0) begin
            // If this was the last burst, go back to idle.
            aw_state_d = AwIdle;
          end else begin
            // Otherwise, continue with the next burst.
            aw_d.len--;
            if (aw_q.burst == axi_pkg::BURST_INCR) begin
              aw_d.addr += (1 << aw_q.size);
            end
          end
        end
      end
      default: aw_state_d = AwIdle;
    endcase
  end

  // Feed W channel through, except `last`, which is always set.
  assign mst.w_data   = slv.w_data;
  assign mst.w_strb   = slv.w_strb;
  assign mst.w_last   = 1'b1;
  assign mst.w_user   = slv.w_user;
  assign mst.w_valid  = slv.w_valid;
  assign slv.w_ready  = mst.w_ready;

  // Feed B channel through.
  `AXI_ASSIGN_B(slv, mst);

  // AR Channel: Store burst lengths in counters, which are associated to AXI IDs through ID queues
  // (to allow reordering of responses w.r.t. requests).
  typedef struct packed {
    id_t              id;
    addr_t            addr;
    axi_pkg::len_t    len;
    axi_pkg::size_t   size;
    axi_pkg::burst_t  burst;
    logic             lock;
    axi_pkg::cache_t  cache;
    axi_pkg::prot_t   prot;
    axi_pkg::qos_t    qos;
    axi_pkg::region_t region;
    user_t            user;
  } ar_chan_t;
  ar_chan_t ar_d, ar_q, slv_ar, mst_ar;

  `AXI_ASSIGN_TO_AR(slv_ar, slv);
  `AXI_ASSIGN_FROM_AR(mst, mst_ar);

  typedef logic [$clog2(MAX_READ_TXNS)-1:0] r_cnt_idx_t;
  logic [MAX_READ_TXNS-1:0]       r_cnt_dec, r_cnt_free, r_cnt_set;
  logic [8:0]                     r_cnt_inp;
  logic [MAX_READ_TXNS-1:0][8:0]  r_cnt_oup;
  r_cnt_idx_t                     r_cnt_free_idx, r_cnt_r_idx;
  for (genvar i = 0; i < MAX_READ_TXNS; i++) begin : gen_r_cnt
    counter #(
      .WIDTH (9)
    ) i_cnt (
      .clk_i,
      .rst_ni,
      .clear_i    (1'b0),
      .en_i       (r_cnt_dec[i]),
      .load_i     (r_cnt_set[i]),
      .down_i     (1'b1),
      .d_i        (r_cnt_inp),
      .q_o        (r_cnt_oup[i]),
      .overflow_o ()
    );
    assign r_cnt_free[i] = (r_cnt_oup[i] == '0);
  end
  assign r_cnt_inp = slv.ar_len + 1;
  lzc #(
    .WIDTH (MAX_READ_TXNS),
    .MODE  (1'b0) // start counting at index 0
  ) i_r_cnt_lzc (
    .in_i     (r_cnt_free),
    .cnt_o    (r_cnt_free_idx),
    .empty_o  ()
  );

  logic r_cnt_idq_inp_req, r_cnt_idq_inp_gnt,
        r_cnt_idq_oup_req, r_cnt_idq_oup_gnt, r_cnt_idq_oup_valid, r_cnt_idq_pop;
  id_queue #(
    .ID_WIDTH ($bits(id_t)),
    .CAPACITY (MAX_READ_TXNS),
    .data_t   (r_cnt_idx_t)
  ) i_r_cnt_idq (
    .clk_i,
    .rst_ni,
    .inp_id_i         (slv.ar_id),
    .inp_data_i       (r_cnt_free_idx),
    .inp_req_i        (r_cnt_idq_inp_req),
    .inp_gnt_o        (r_cnt_idq_inp_gnt),
    .exists_data_i    ('0),
    .exists_mask_i    ('0),
    .exists_req_i     (1'b0),
    .exists_o         (),
    .exists_gnt_o     (),
    .oup_id_i         (mst.r_id),
    .oup_pop_i        (r_cnt_idq_pop),
    .oup_req_i        (r_cnt_idq_oup_req),
    .oup_data_o       (r_cnt_r_idx),
    .oup_data_valid_o (r_cnt_idq_oup_valid),
    .oup_gnt_o        (r_cnt_idq_oup_gnt)
  );

  enum logic {ArIdle, ArBusy} ar_state_d, ar_state_q;
  always_comb begin
    r_cnt_idq_inp_req = 1'b0;
    r_cnt_set = '0;
    ar_d = ar_q;
    ar_state_d = ar_state_q;
    mst.ar_valid = 1'b0;
    mst_ar = 'x;
    slv.ar_ready = 1'b0;
    case (ar_state_q)
      ArIdle: begin
        if (slv.ar_valid && |(r_cnt_free) && r_cnt_idq_inp_gnt) begin
          if (slv.ar_len == '0) begin // No splitting required -> feed through.
            mst_ar = slv_ar;
            mst.ar_valid = 1'b1;
            // As soon as downstream is ready, allocate a counter and acknowledge upstream.
            if (mst.ar_ready) begin
              r_cnt_set[r_cnt_free_idx] = 1'b1;
              r_cnt_idq_inp_req = 1'b1;
              slv.ar_ready = 1'b1;
            end
          end else begin // Splitting required.
            // Store AR, allocate a counter, and acknowledge upstream.
            ar_d = slv_ar;
            r_cnt_set[r_cnt_free_idx] = 1'b1;
            r_cnt_idq_inp_req = 1'b1;
            slv.ar_ready = 1'b1;
            // Try to feed first burst through.
            mst_ar = ar_d;
            mst_ar.len = '0;
            mst.ar_valid = 1'b1;
            if (mst.ar_ready) begin
              // Reduce number of bursts still to be sent by one and increment address.
              ar_d.len--;
              if (ar_d.burst == axi_pkg::BURST_INCR) begin
                ar_d.addr += (1 << ar_d.size);
              end
            end
            ar_state_d = ArBusy;
          end
        end
      end
      ArBusy: begin
        // Sent next burst from split.
        mst_ar = ar_q;
        mst_ar.len = '0;
        mst.ar_valid = 1'b1;
        if (mst.ar_ready) begin
          if (ar_q.len == '0) begin
            // If this was the last burst, go back to idle.
            ar_state_d = ArIdle;
          end else begin
            // Otherwise, continue with the next burst.
            ar_d.len--;
            if (ar_q.burst == axi_pkg::BURST_INCR) begin
              ar_d.addr += (1 << ar_q.size);
            end
          end
        end
      end
      default: ar_state_d = ArIdle;
    endcase
  end

  // R Channel: Reconstruct `last`, feed rest through.
  logic r_last_d, r_last_q;
  enum logic {RFeedthrough, RWait} r_state_d, r_state_q;
  assign slv.r_id   = mst.r_id;
  assign slv.r_data = mst.r_data;
  assign slv.r_resp = mst.r_resp;
  assign slv.r_user = mst.r_user;
  always_comb begin
    mst.r_ready = 1'b0;
    r_cnt_dec = '0;
    r_cnt_idq_oup_req = 1'b0;
    r_cnt_idq_pop = 1'b0;
    r_last_d = r_last_q;
    r_state_d = r_state_q;
    slv.r_last = 1'b0;
    slv.r_valid = 1'b0;

    case (r_state_q)
      RFeedthrough: begin
        // If downstream has an R beat ..
        if (mst.r_valid) begin
          // .. and the ID queue can give us the index of the counter ..
          r_cnt_idq_oup_req = 1'b1;
          if (r_cnt_idq_oup_gnt) begin
            r_last_d = (r_cnt_oup[r_cnt_r_idx] == 9'd1);
            // .. if this is the last beat of the burst, ..
            if (r_last_d) begin
              slv.r_last = 1'b1;
              // pop the counter index from the ID queue.
              r_cnt_idq_pop = 1'b1;
            end
            // Decrement the counter.
            r_cnt_dec[r_cnt_r_idx] = 1'b1;
            // Try to forward the beat upstream.
            slv.r_valid = 1'b1;
            if (slv.r_ready) begin
              // Acknowledge downstream.
              mst.r_ready = 1'b1;
            end else begin
              // Wait for upstream to become ready.
              r_state_d = RWait;
            end
          end
        end
      end
      RWait: begin
        slv.r_last = r_last_q;
        slv.r_valid = mst.r_valid;
        if (mst.r_valid && slv.r_ready) begin
          mst.r_ready = 1'b1;
          r_state_d = RFeedthrough;
        end
      end
      default: r_state_d = RFeedthrough;
    endcase
  end

  // Flip-Flops
  always_ff @(posedge clk_i, negedge rst_ni) begin
    if (!rst_ni) begin
      ar_q        <= '0;
      aw_q        <= '0;
      ar_state_q  <= ArIdle;
      aw_state_q  <= AwIdle;
      r_last_q    <= 1'b0;
      r_state_q   <= RFeedthrough;
    end else begin
      ar_q        <= ar_d;
      aw_q        <= aw_d;
      ar_state_q  <= ar_state_d;
      aw_state_q  <= aw_state_d;
      r_last_q    <= r_last_d;
      r_state_q   <= r_state_d;
    end
  end

  // Assumptions and assertions
  `ifndef VERILATOR
  // pragma translate_off
  default disable iff (!rst_ni);
  // Inputs
  assume property (@(posedge clk_i) slv.aw_valid |-> slv.aw_burst != axi_pkg::BURST_WRAP)
    else $fatal(1, "Wrapping burst on AW received, which this module does not support!");
  assume property (@(posedge clk_i) slv.ar_valid |-> slv.ar_burst != axi_pkg::BURST_WRAP)
    else $fatal(1, "Wrapping burst on AR received, which this module does not support!");
  assume property (@(posedge clk_i) slv.aw_valid && slv.aw_ready |->
      |(slv.aw_cache & axi_pkg::CACHE_MODIFIABLE) || slv.aw_len > 15)
    else $warning("Splitting a non-modifiable AW burst with 16 beats or less, which violates the AXI spec.");
  assume property (@(posedge clk_i) slv.ar_valid && slv.ar_ready |->
      |(slv.ar_cache & axi_pkg::CACHE_MODIFIABLE) || slv.ar_len > 15)
    else $warning("Splitting a non-modifiable AR burst with 16 beats or less, which violates the AXI spec.");
  // Internals
  assume property (@(posedge clk_i) r_cnt_idq_oup_gnt |-> r_cnt_idq_oup_valid)
    else $error("Invalid output at R ID queue!");
  // Outputs
  assert property (@(posedge clk_i) mst.aw_valid |-> mst.aw_len == '0)
    else $fatal(1, "AW burst longer than a single beat emitted!");
  assert property (@(posedge clk_i) mst.ar_valid |-> mst.ar_len == '0)
    else $fatal(1, "AR burst longer than a single beat emitted!");
  // pragma translate_on
  `endif

  // TODO: Add FORCE parameter to split non-modifiable bursts with 16 beats or less only when that
  // parameter is set, to have a standard-compliant alternative?

endmodule
