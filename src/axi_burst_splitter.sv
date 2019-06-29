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
`include "axi/typedef.svh"

module axi_burst_splitter #(
  // Maximum number of AXI read bursts outstanding at the same time
  parameter int unsigned MAX_READ_TXNS = 0,
  // Maximum number of AXI write bursts outstanding at the same time
  parameter int unsigned MAX_WRITE_TXNS = 0,
  // AXI Bus Types
  parameter int unsigned AW = 0,
  parameter int unsigned DW = 0,
  parameter int unsigned IW = 0,
  parameter int unsigned UW = 0,
  parameter type req_t = logic,
  parameter type resp_t = logic
) (
  input  logic  clk_i,
  input  logic  rst_ni,

  // Input / Slave Port
  input  req_t  req_i,
  output resp_t resp_o,

  // Output / Master Port
  output req_t  req_o,
  input  resp_t resp_i
);

  typedef logic [IW-1:0] id_t;
  `AXI_TYPEDEF_AW_CHAN_T(aw_chan_t, logic[AW-1:0], id_t, logic[UW-1:0]);
  `AXI_TYPEDEF_AR_CHAN_T(ar_chan_t, logic[AW-1:0], id_t, logic[UW-1:0]);

  // --------------------------------------------------
  // AW Channel
  // --------------------------------------------------
  logic           w_cnt_dec, w_cnt_req, w_cnt_gnt, w_cnt_err;
  axi_pkg::len_t  w_cnt_len;
  axi_burst_splitter_ax_chan #(
    .chan_t   (aw_chan_t),
    .IW       (IW),
    .MAX_TXNS (MAX_WRITE_TXNS)
  ) i_aw_chan (
    .clk_i,
    .rst_ni,
    .ax_i           (req_i.aw),
    .ax_valid_i     (req_i.aw_valid),
    .ax_ready_o     (resp_o.aw_ready),
    .ax_o           (req_o.aw),
    .ax_valid_o     (req_o.aw_valid),
    .ax_ready_i     (resp_i.aw_ready),
    .cnt_id_i       (resp_i.b.id),
    .cnt_len_o      (w_cnt_len),
    .cnt_set_err_i  (resp_i.b.resp[1]),
    .cnt_err_o      (w_cnt_err),
    .cnt_dec_i      (w_cnt_dec),
    .cnt_req_i      (w_cnt_req),
    .cnt_gnt_o      (w_cnt_gnt)
  );

  // --------------------------------------------------
  // W Channel
  // --------------------------------------------------
  // Feed through, except `last`, which is always set.
  always_comb begin
    req_o.w = req_i.w;
    req_o.w.last = 1'b1;
    resp_o.w_ready = resp_i.w_ready;
    req_o.w_valid = req_i.w_valid;
  end

  // --------------------------------------------------
  // B Channel
  // --------------------------------------------------
  // Feed only last B response of a burst through.
  enum logic {BReady, BWait} b_state_d, b_state_q;
  logic b_err_d, b_err_q;
  always_comb begin
    req_o.b_ready = 1'b0;
    resp_o.b = '0;
    resp_o.b_valid = 1'b0;
    w_cnt_dec = 1'b0;
    w_cnt_req = 1'b0;
    b_err_d = b_err_q;
    b_state_d = b_state_q;

    case (b_state_q)
      BReady: begin
        if (resp_i.b_valid) begin
          w_cnt_req = 1'b1;
          if (w_cnt_gnt) begin
            if (w_cnt_len == 8'd0) begin
              resp_o.b = resp_i.b;
              resp_o.b.resp[1] = w_cnt_err;
              resp_o.b_valid = 1'b1;
              w_cnt_dec = 1'b1;
              if (req_i.b_ready) begin
                req_o.b_ready = 1'b1;
              end else begin
                b_state_d = BWait;
                b_err_d = w_cnt_err;
              end
            end else begin
              req_o.b_ready = 1'b1;
              w_cnt_dec = 1'b1;
            end
          end
        end
      end
      BWait: begin
        resp_o.b = resp_i.b;
        resp_o.b.resp[1] = b_err_q;
        resp_o.b_valid = 1'b1;
        if (resp_i.b_valid && req_i.b_ready) begin
          req_o.b_ready = 1'b1;
          b_state_d = BReady;
        end
      end
      default: b_state_d = BReady;
    endcase
  end

  // --------------------------------------------------
  // AR Channel
  // --------------------------------------------------
  // See description of `ax_chan` module.
  logic           r_cnt_dec, r_cnt_req, r_cnt_gnt;
  axi_pkg::len_t  r_cnt_len;
  axi_burst_splitter_ax_chan #(
    .chan_t   (ar_chan_t),
    .IW       (IW),
    .MAX_TXNS (MAX_READ_TXNS)
  ) i_ar_chan (
    .clk_i,
    .rst_ni,
    .ax_i           (req_i.ar),
    .ax_valid_i     (req_i.ar_valid),
    .ax_ready_o     (resp_o.ar_ready),
    .ax_o           (req_o.ar),
    .ax_valid_o     (req_o.ar_valid),
    .ax_ready_i     (resp_i.ar_ready),
    .cnt_id_i       (resp_i.r.id),
    .cnt_len_o      (r_cnt_len),
    .cnt_set_err_i  (1'b0),
    .cnt_err_o      (),
    .cnt_dec_i      (r_cnt_dec),
    .cnt_req_i      (r_cnt_req),
    .cnt_gnt_o      (r_cnt_gnt)
  );

  // --------------------------------------------------
  // R Channel
  // --------------------------------------------------
  // Reconstruct `last`, feed rest through.
  logic r_last_d, r_last_q;
  enum logic {RFeedthrough, RWait} r_state_d, r_state_q;
  always_comb begin
    r_cnt_dec = 1'b0;
    r_cnt_req = 1'b0;
    r_last_d = r_last_q;
    r_state_d = r_state_q;
    req_o.r_ready = 1'b0;
    resp_o.r = resp_i.r;
    resp_o.r.last = 1'b0;
    resp_o.r_valid = 1'b0;

    case (r_state_q)
      RFeedthrough: begin
        // If downstream has an R beat and the R counters can give us the remaining length of
        // that burst, ...
        if (resp_i.r_valid) begin
          r_cnt_req = 1'b1;
          if (r_cnt_gnt) begin
            r_last_d = (r_cnt_len == 8'd0);
            resp_o.r.last = r_last_d;
            // Decrement the counter.
            r_cnt_dec = 1'b1;
            // Try to forward the beat upstream.
            resp_o.r_valid = 1'b1;
            if (req_i.r_ready) begin
              // Acknowledge downstream.
              req_o.r_ready = 1'b1;
            end else begin
              // Wait for upstream to become ready.
              r_state_d = RWait;
            end
          end
        end
      end
      RWait: begin
        resp_o.r.last = r_last_q;
        resp_o.r_valid = resp_i.r_valid;
        if (resp_i.r_valid && req_i.r_ready) begin
          req_o.r_ready = 1'b1;
          r_state_d = RFeedthrough;
        end
      end
      default: r_state_d = RFeedthrough;
    endcase
  end

  // --------------------------------------------------
  // Flip-Flops
  // --------------------------------------------------
  always_ff @(posedge clk_i, negedge rst_ni) begin
    if (!rst_ni) begin
      b_err_q     <= 1'b0;
      b_state_q   <= BReady;
      r_last_q    <= 1'b0;
      r_state_q   <= RFeedthrough;
    end else begin
      b_err_q     <= b_err_d;
      b_state_q   <= b_state_d;
      r_last_q    <= r_last_d;
      r_state_q   <= r_state_d;
    end
  end

  // --------------------------------------------------
  // Assumptions and assertions
  // --------------------------------------------------
  `ifndef VERILATOR
  // pragma translate_off
  default disable iff (!rst_ni);
  // Inputs
  assume property (@(posedge clk_i) req_i.aw_valid |-> req_i.aw.burst != axi_pkg::BURST_WRAP)
    else $fatal(1, "Wrapping burst on AW received, which this module does not support!");
  assume property (@(posedge clk_i) req_i.ar_valid |-> req_i.ar.burst != axi_pkg::BURST_WRAP)
    else $fatal(1, "Wrapping burst on AR received, which this module does not support!");
  assume property (@(posedge clk_i) req_i.aw_valid && resp_o.aw_ready |->
      |(req_i.aw.cache & axi_pkg::CACHE_MODIFIABLE) || req_i.aw.len > 15)
    else $warning("Splitting a non-modifiable AW burst with 16 beats or less, which violates the AXI spec.");
  assume property (@(posedge clk_i) req_i.ar_valid && resp_o.ar_ready |->
      |(req_i.ar.cache & axi_pkg::CACHE_MODIFIABLE) || req_i.ar.len > 15)
    else $warning("Splitting a non-modifiable AR burst with 16 beats or less, which violates the AXI spec.");
  // Outputs
  assert property (@(posedge clk_i) req_o.aw_valid |-> req_o.aw.len == '0)
    else $fatal(1, "AW burst longer than a single beat emitted!");
  assert property (@(posedge clk_i) req_o.ar_valid |-> req_o.ar.len == '0)
    else $fatal(1, "AR burst longer than a single beat emitted!");
  // pragma translate_on
  `endif

  // TODO: Add FORCE parameter to split non-modifiable bursts with 16 beats or less only when that
  // parameter is set, to have a standard-compliant alternative?

endmodule

// Store burst lengths in counters, which are associated to AXI IDs through ID queues (to allow
// reordering of responses w.r.t. requests).
module axi_burst_splitter_ax_chan #(
  parameter type chan_t = logic,
  parameter int unsigned IW = 0,
  parameter int unsigned MAX_TXNS = 0,
  localparam type id_t = logic[IW-1:0]
) (
  input  logic          clk_i,
  input  logic          rst_ni,

  input  chan_t         ax_i,
  input  logic          ax_valid_i,
  output logic          ax_ready_o,
  output chan_t         ax_o,
  output logic          ax_valid_o,
  input  logic          ax_ready_i,

  input  id_t           cnt_id_i,
  output axi_pkg::len_t cnt_len_o,
  input  logic          cnt_set_err_i,
  output logic          cnt_err_o,
  input  logic          cnt_dec_i,
  input  logic          cnt_req_i,
  output logic          cnt_gnt_o
);

  logic cnt_alloc_req, cnt_alloc_gnt;
  axi_burst_splitter_counters #(
    .MAX_TXNS (MAX_TXNS),
    .id_t     (id_t)
  ) i_cntrs (
    .clk_i,
    .rst_ni,
    .alloc_id_i     (ax_i.id),
    .alloc_len_i    (ax_i.len),
    .alloc_req_i    (cnt_alloc_req),
    .alloc_gnt_o    (cnt_alloc_gnt),
    .read_id_i      (cnt_id_i),
    .read_len_o     (cnt_len_o),
    .read_set_err_i (cnt_set_err_i),
    .read_err_o     (cnt_err_o),
    .read_dec_i     (cnt_dec_i),
    .read_req_i     (cnt_req_i),
    .read_gnt_o     (cnt_gnt_o)
  );

  chan_t ax_d, ax_q;

  enum logic {Idle, Busy} state_d, state_q;
  always_comb begin
    cnt_alloc_req = 1'b0;
    ax_d = ax_q;
    state_d = state_q;
    ax_o = '0;
    ax_valid_o = 1'b0;
    ax_ready_o = 1'b0;
    case (state_q)
      Idle: begin
        if (ax_valid_i && cnt_alloc_gnt) begin
          if (ax_i.len == '0) begin // No splitting required -> feed through.
            ax_o = ax_i;
            ax_valid_o = 1'b1;
            // As soon as downstream is ready, allocate a counter and acknowledge upstream.
            if (ax_ready_i) begin
              cnt_alloc_req = 1'b1;
              ax_ready_o = 1'b1;
            end
          end else begin // Splitting required.
            // Store Ax, allocate a counter, and acknowledge upstream.
            ax_d = ax_i;
            cnt_alloc_req = 1'b1;
            ax_ready_o = 1'b1;
            // Try to feed first burst through.
            ax_o = ax_d;
            ax_o.len = '0;
            ax_valid_o = 1'b1;
            if (ax_ready_i) begin
              // Reduce number of bursts still to be sent by one and increment address.
              ax_d.len--;
              if (ax_d.burst == axi_pkg::BURST_INCR) begin
                ax_d.addr += (1 << ax_d.size);
              end
            end
            state_d = Busy;
          end
        end
      end
      Busy: begin
        // Sent next burst from split.
        ax_o = ax_q;
        ax_o.len = '0;
        ax_valid_o = 1'b1;
        if (ax_ready_i) begin
          if (ax_q.len == '0) begin
            // If this was the last burst, go back to idle.
            state_d = Idle;
          end else begin
            // Otherwise, continue with the next burst.
            ax_d.len--;
            if (ax_q.burst == axi_pkg::BURST_INCR) begin
              ax_d.addr += (1 << ax_q.size);
            end
          end
        end
      end
      default: state_d = Idle;
    endcase
  end

  always_ff @(posedge clk_i, negedge rst_ni) begin
    if (!rst_ni) begin
      ax_q    <= '0;
      state_q <= Idle;
    end else begin
      ax_q    <= ax_d;
      state_q <= state_d;
    end
  end

endmodule

module axi_burst_splitter_counters #(
  parameter int unsigned MAX_TXNS = 0,
  parameter type id_t
) (
  input  logic          clk_i,
  input  logic          rst_ni,

  input  id_t           alloc_id_i,
  input  axi_pkg::len_t alloc_len_i,
  input  logic          alloc_req_i,
  output logic          alloc_gnt_o,

  input  id_t           read_id_i,
  output axi_pkg::len_t read_len_o,
  input  logic          read_set_err_i,
  output logic          read_err_o,
  input  logic          read_dec_i,
  input  logic          read_req_i,
  output logic          read_gnt_o
);

  typedef logic [$clog2(MAX_TXNS)-1:0] cnt_idx_t;
  typedef logic [$bits(axi_pkg::len_t):0] cnt_t;
  logic [MAX_TXNS-1:0]  cnt_dec, cnt_free, cnt_set, err_d, err_q;
  cnt_t                 cnt_inp;
  cnt_t [MAX_TXNS-1:0]  cnt_oup;
  cnt_idx_t             cnt_free_idx, cnt_r_idx;
  for (genvar i = 0; i < MAX_TXNS; i++) begin : gen_cnt
    counter #(
      .WIDTH ($bits(cnt_t))
    ) i_cnt (
      .clk_i,
      .rst_ni,
      .clear_i    (1'b0),
      .en_i       (cnt_dec[i]),
      .load_i     (cnt_set[i]),
      .down_i     (1'b1),
      .d_i        (cnt_inp),
      .q_o        (cnt_oup[i]),
      .overflow_o ()
    );
    assign cnt_free[i] = (cnt_oup[i] == '0);
  end
  assign cnt_inp = {1'b0, alloc_len_i} + 1;

  lzc #(
    .WIDTH  (MAX_TXNS),
    .MODE   (1'b0)  // start counting at index 0
  ) i_lzc (
    .in_i     (cnt_free),
    .cnt_o    (cnt_free_idx),
    .empty_o  ()
  );

  logic idq_inp_req, idq_inp_gnt,
        idq_oup_gnt, idq_oup_valid, idq_oup_pop;
  id_queue #(
    .ID_WIDTH ($bits(id_t)),
    .CAPACITY (MAX_TXNS),
    .data_t   (cnt_idx_t)
  ) i_idq (
    .clk_i,
    .rst_ni,
    .inp_id_i         (alloc_id_i),
    .inp_data_i       (cnt_free_idx),
    .inp_req_i        (idq_inp_req),
    .inp_gnt_o        (idq_inp_gnt),
    .exists_data_i    ('0),
    .exists_mask_i    ('0),
    .exists_req_i     (1'b0),
    .exists_o         (/* keep open */),
    .exists_gnt_o     (/* keep open */),
    .oup_id_i         (read_id_i),
    .oup_pop_i        (idq_oup_pop),
    .oup_req_i        (read_req_i),
    .oup_data_o       (cnt_r_idx),
    .oup_data_valid_o (idq_oup_valid),
    .oup_gnt_o        (idq_oup_gnt)
  );
  assign idq_inp_req = alloc_req_i & alloc_gnt_o;
  assign alloc_gnt_o = idq_inp_gnt & |(cnt_free);
  assign read_gnt_o = idq_oup_gnt & idq_oup_valid;
  logic [8:0] read_len;
  assign read_len = cnt_oup[cnt_r_idx] - 1;
  assign read_len_o = read_len[7:0];

  assign idq_oup_pop = read_req_i & read_gnt_o & read_dec_i & (read_len_o == 8'd0);
  always_comb begin
    cnt_dec = '0;
    cnt_dec[cnt_r_idx] = read_req_i & read_gnt_o & read_dec_i;
  end
  always_comb begin
    cnt_set = '0;
    cnt_set[cnt_free_idx] = alloc_req_i & alloc_gnt_o;
  end
  always_comb begin
    err_d = err_q;
    read_err_o = err_q[cnt_r_idx];
    if (read_req_i && read_gnt_o && read_set_err_i) begin
      err_d[cnt_r_idx] = 1'b1;
      read_err_o = 1'b1;
    end
    if (alloc_req_i && alloc_gnt_o) begin
      err_d[cnt_free_idx] = 1'b0;
    end
  end

  always_ff @(posedge clk_i, negedge rst_ni) begin
    if (!rst_ni) begin
      err_q <= '0;
    end else begin
      err_q <= err_d;
    end
  end

  `ifndef VERILATOR
  // pragma translate_off
  assume property (@(posedge clk_i) idq_oup_gnt |-> idq_oup_valid)
    else $warning("Invalid output at ID queue, read not granted!");
  // pragma translate_on
  `endif

endmodule
