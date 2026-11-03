// Copyright (c) 2026 Kuan-Yu Liu
//
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Authors:
// - Kuan-Yu Liu <cat930112@gmail.com>

// Testbench for axi_burst_unwrap.
//
// Regression test for https://github.com/pulp-platform/axi/issues/448:
// a downstream slave is allowed to wait for WVALID before asserting AWREADY
// (AXI IHI0022, A3.3.1), but axi_burst_unwrap used to allocate its W-channel
// counters only once the downstream AW handshake completed, so it never
// asserted WVALID -> deadlock.  This testbench models such a slave and checks
// that writes still complete, plus functional checks for INCR and (split)
// WRAP bursts, W-channel backpressure stability, and the read path.

`include "axi/typedef.svh"

module tb_axi_burst_unwrap #(
  // AXI parameters
  parameter int unsigned TbAddrWidth = 32'd32,
  parameter int unsigned TbDataWidth = 32'd32,
  parameter int unsigned TbIdWidth   = 32'd2,
  parameter int unsigned TbUserWidth = 32'd1,
  // TB parameters
  parameter int unsigned TbTimeout   = 32'd1000
);

  localparam time CyclTime = 10ns;

  typedef logic [TbAddrWidth-1:0]   addr_t;
  typedef logic [TbDataWidth-1:0]   data_t;
  typedef logic [TbIdWidth-1:0]     id_t;
  typedef logic [TbDataWidth/8-1:0] strb_t;
  typedef logic [TbUserWidth-1:0]   user_t;

  `AXI_TYPEDEF_AW_CHAN_T(aw_chan_t, addr_t, id_t, user_t)
  `AXI_TYPEDEF_W_CHAN_T(w_chan_t, data_t, strb_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T(b_chan_t, id_t, user_t)
  `AXI_TYPEDEF_AR_CHAN_T(ar_chan_t, addr_t, id_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(r_chan_t, data_t, id_t, user_t)
  `AXI_TYPEDEF_REQ_T(axi_req_t, aw_chan_t, w_chan_t, ar_chan_t)
  `AXI_TYPEDEF_RESP_T(axi_resp_t, b_chan_t, r_chan_t)

  typedef struct packed {
    data_t data;
    strb_t strb;
    logic  last;
  } w_beat_t;

  typedef struct packed {
    data_t data;
    id_t   id;
    logic  last;
  } r_beat_t;

  // -------------------------------------------------------------------------
  // Clock, reset, DUT
  // -------------------------------------------------------------------------
  logic clk, rst_n;

  axi_req_t  slv_req;   // TB master -> DUT
  axi_resp_t slv_resp;
  axi_req_t  mst_req;   // DUT -> TB slave
  axi_resp_t mst_resp;

  axi_burst_unwrap #(
    .MaxReadTxns  ( 32'd4       ),
    .MaxWriteTxns ( 32'd4       ),
    .AddrWidth    ( TbAddrWidth ),
    .DataWidth    ( TbDataWidth ),
    .IdWidth      ( TbIdWidth   ),
    .UserWidth    ( TbUserWidth ),
    .axi_req_t    ( axi_req_t   ),
    .axi_resp_t   ( axi_resp_t  )
  ) i_dut (
    .clk_i      ( clk      ),
    .rst_ni     ( rst_n    ),
    .slv_req_i  ( slv_req  ),
    .slv_resp_o ( slv_resp ),
    .mst_req_o  ( mst_req  ),
    .mst_resp_i ( mst_resp )
  );

  initial begin
    clk = 1'b0;
    forever #(CyclTime/2) clk = ~clk;
  end

  // -------------------------------------------------------------------------
  // TB configuration and bookkeeping
  // -------------------------------------------------------------------------
  // Issue #448 slave model: assert AWREADY only while WVALID is observed.
  bit          cfg_aw_waits_for_wvalid;
  // WREADY backpressure: 0 = always ready, N = ready one cycle in N+1.
  int unsigned cfg_wready_stall;
  // In wvalid-first mode: 0 = AWREADY asserted combinationally while WVALID is
  // observed; N > 0 = AWREADY asserted only once WVALID has been observed
  // (sticky) for N cycles, so the AW stays stalled long after its W beats
  // went through.
  int unsigned cfg_awready_hold;
  // Withhold all B responses while set (keeps the DUT's B counters occupied).
  bit          cfg_b_hold;

  int unsigned err_cnt;

  // Logs of what the downstream slave observed / the upstream master received.
  aw_chan_t    ds_aw_log[$];
  ar_chan_t    ds_ar_log[$];
  w_beat_t     ds_w_log[$];
  b_chan_t     us_b_log[$];
  r_beat_t     us_r_log[$];

  // -------------------------------------------------------------------------
  // Upstream master: queue-driven drivers
  // -------------------------------------------------------------------------
  aw_chan_t us_aw_queue[$];
  w_beat_t  us_w_queue[$];
  ar_chan_t us_ar_queue[$];

  aw_chan_t us_aw;
  logic     us_aw_valid;
  w_chan_t  us_w;
  logic     us_w_valid;
  ar_chan_t us_ar;
  logic     us_ar_valid;

  assign slv_req = '{
    aw:       us_aw,
    aw_valid: us_aw_valid,
    w:        us_w,
    w_valid:  us_w_valid,
    b_ready:  1'b1,
    ar:       us_ar,
    ar_valid: us_ar_valid,
    r_ready:  1'b1
  };

  always @(posedge clk or negedge rst_n) begin : proc_us_aw_driver
    if (!rst_n) begin
      us_aw       <= '0;
      us_aw_valid <= 1'b0;
    end else if (!us_aw_valid || slv_resp.aw_ready) begin
      if (us_aw_queue.size() > 0) begin
        automatic aw_chan_t beat = us_aw_queue.pop_front();
        us_aw       <= beat;
        us_aw_valid <= 1'b1;
      end else begin
        us_aw_valid <= 1'b0;
      end
    end
  end

  always @(posedge clk or negedge rst_n) begin : proc_us_w_driver
    if (!rst_n) begin
      us_w       <= '0;
      us_w_valid <= 1'b0;
    end else if (!us_w_valid || slv_resp.w_ready) begin
      if (us_w_queue.size() > 0) begin
        automatic w_beat_t beat = us_w_queue.pop_front();
        us_w       <= '{data: beat.data, strb: beat.strb, last: beat.last, user: '0};
        us_w_valid <= 1'b1;
      end else begin
        us_w_valid <= 1'b0;
      end
    end
  end

  always @(posedge clk or negedge rst_n) begin : proc_us_ar_driver
    if (!rst_n) begin
      us_ar       <= '0;
      us_ar_valid <= 1'b0;
    end else if (!us_ar_valid || slv_resp.ar_ready) begin
      if (us_ar_queue.size() > 0) begin
        automatic ar_chan_t beat = us_ar_queue.pop_front();
        us_ar       <= beat;
        us_ar_valid <= 1'b1;
      end else begin
        us_ar_valid <= 1'b0;
      end
    end
  end

  // Upstream response logging.
  always @(posedge clk) begin : proc_us_resp_log
    if (rst_n) begin
      if (slv_resp.b_valid && slv_req.b_ready) begin
        us_b_log.push_back(slv_resp.b);
      end
      if (slv_resp.r_valid && slv_req.r_ready) begin
        us_r_log.push_back('{data: slv_resp.r.data, id: slv_resp.r.id, last: slv_resp.r.last});
      end
    end
  end

  // -------------------------------------------------------------------------
  // Downstream slave model
  // -------------------------------------------------------------------------
  logic    ds_aw_ready, ds_w_ready;
  b_chan_t ds_b;
  logic    ds_b_valid;
  r_chan_t ds_r;
  logic    ds_r_valid;

  assign mst_resp = '{
    aw_ready: ds_aw_ready,
    ar_ready: 1'b1,
    w_ready:  ds_w_ready,
    b_valid:  ds_b_valid,
    b:        ds_b,
    r_valid:  ds_r_valid,
    r:        ds_r
  };

  // AWREADY: the issue #448 slave waits until it observes WVALID before it
  // asserts AWREADY.  This is legal for a destination (AXI IHI0022 A3.3.1).
  // With cfg_awready_hold > 0, AWREADY is additionally held off for that many
  // cycles after WVALID was first observed (sticky per pending AW), so the AW
  // handshake completes long after the W beats went through.
  logic        ds_wv_seen;
  int unsigned ds_wv_hold_cnt;
  always @(posedge clk or negedge rst_n) begin : proc_ds_awready_hold
    if (!rst_n) begin
      ds_wv_seen     <= 1'b0;
      ds_wv_hold_cnt <= 0;
    end else if (mst_req.aw_valid && ds_aw_ready) begin
      ds_wv_seen     <= 1'b0;
      ds_wv_hold_cnt <= 0;
    end else begin
      if (mst_req.w_valid) begin
        ds_wv_seen <= 1'b1;
      end
      if (ds_wv_seen) begin
        ds_wv_hold_cnt <= ds_wv_hold_cnt + 1;
      end
    end
  end
  assign ds_aw_ready = !cfg_aw_waits_for_wvalid ? 1'b1 :
                       ((cfg_awready_hold == 0) ? mst_req.w_valid :
                        (ds_wv_seen && (ds_wv_hold_cnt >= cfg_awready_hold)));

  // WREADY backpressure pattern.
  int unsigned ds_stall_cnt;
  always @(posedge clk or negedge rst_n) begin : proc_ds_wready
    if (!rst_n) begin
      ds_stall_cnt <= 0;
    end else begin
      ds_stall_cnt <= (ds_stall_cnt >= cfg_wready_stall) ? 0 : ds_stall_cnt + 1;
    end
  end
  assign ds_w_ready = (ds_stall_cnt >= cfg_wready_stall);

  // Track accepted AWs / completed W bursts; respond with B once a burst has
  // both its AW and all its W beats (W data may arrive before the AW with the
  // issue #448 slave).
  id_t         ds_b_id_queue[$];
  int unsigned ds_wlast_cnt;
  int unsigned ds_b_launched;

  always @(posedge clk or negedge rst_n) begin : proc_ds_slave
    if (!rst_n) begin
      ds_b         <= '0;
      ds_b_valid   <= 1'b0;
      ds_wlast_cnt <= 0;
    end else begin
      // Observe AW handshakes.
      if (mst_req.aw_valid && mst_resp.aw_ready) begin
        ds_aw_log.push_back(mst_req.aw);
        ds_b_id_queue.push_back(mst_req.aw.id);
      end
      // Observe W handshakes.
      if (mst_req.w_valid && mst_resp.w_ready) begin
        ds_w_log.push_back('{data: mst_req.w.data, strb: mst_req.w.strb, last: mst_req.w.last});
        if (mst_req.w.last) begin
          ds_wlast_cnt <= ds_wlast_cnt + 1;
        end
      end
      // B channel: one response per completed downstream burst, in order.
      if (!ds_b_valid || mst_req.b_ready) begin
        if ((ds_b_id_queue.size() > ds_b_launched) && (ds_wlast_cnt > ds_b_launched)
            && !cfg_b_hold) begin
          ds_b          <= '{id: ds_b_id_queue[ds_b_launched], resp: axi_pkg::RESP_OKAY, user: '0};
          ds_b_valid    <= 1'b1;
          ds_b_launched <= ds_b_launched + 1;
        end else begin
          ds_b_valid <= 1'b0;
        end
      end
    end
  end

  // R channel: on each accepted AR, return one beat per address with
  // data = beat address (makes data checking trivial).
  r_beat_t ds_r_queue[$];

  always @(posedge clk or negedge rst_n) begin : proc_ds_read
    if (!rst_n) begin
      ds_r       <= '0;
      ds_r_valid <= 1'b0;
    end else begin
      if (mst_req.ar_valid && mst_resp.ar_ready) begin
        ds_ar_log.push_back(mst_req.ar);
        for (int unsigned i = 0; i <= mst_req.ar.len; i++) begin
          automatic addr_t beat_addr = mst_req.ar.addr + addr_t'(i << mst_req.ar.size);
          ds_r_queue.push_back('{data: data_t'(beat_addr), id: mst_req.ar.id,
                                 last: (i == mst_req.ar.len)});
        end
      end
      if (!ds_r_valid || mst_req.r_ready) begin
        if (ds_r_queue.size() > 0) begin
          automatic r_beat_t beat = ds_r_queue.pop_front();
          ds_r       <= '{id: beat.id, data: beat.data, resp: axi_pkg::RESP_OKAY,
                          last: beat.last, user: '0};
          ds_r_valid <= 1'b1;
        end else begin
          ds_r_valid <= 1'b0;
        end
      end
    end
  end

  // -------------------------------------------------------------------------
  // Protocol stability checks on the downstream AW and W channels:
  // while VALID is high and READY is low, VALID must stay high and the
  // payload must remain stable.
  // -------------------------------------------------------------------------
  aw_chan_t chk_aw_q;
  w_chan_t  chk_w_q;
  logic     chk_aw_valid_q, chk_aw_ready_q, chk_w_valid_q, chk_w_ready_q;

  always @(posedge clk or negedge rst_n) begin : proc_stability_check
    if (!rst_n) begin
      chk_aw_valid_q <= 1'b0;
      chk_aw_ready_q <= 1'b0;
      chk_w_valid_q  <= 1'b0;
      chk_w_ready_q  <= 1'b0;
      chk_aw_q       <= '0;
      chk_w_q        <= '0;
    end else begin
      if (chk_aw_valid_q && !chk_aw_ready_q) begin
        if (!mst_req.aw_valid) begin
          $display("ERROR Stability: AWVALID retracted without AWREADY");
          err_cnt++;
        end else if (mst_req.aw !== chk_aw_q) begin
          $display("ERROR Stability: AW payload changed while stalled");
          err_cnt++;
        end
      end
      if (chk_w_valid_q && !chk_w_ready_q) begin
        if (!mst_req.w_valid) begin
          $display("ERROR Stability: WVALID retracted without WREADY");
          err_cnt++;
        end else if (mst_req.w !== chk_w_q) begin
          $display("ERROR Stability: W payload changed while stalled");
          err_cnt++;
        end
      end
      chk_aw_valid_q <= mst_req.aw_valid;
      chk_aw_ready_q <= mst_resp.aw_ready;
      chk_w_valid_q  <= mst_req.w_valid;
      chk_w_ready_q  <= mst_resp.w_ready;
      chk_aw_q       <= mst_req.aw;
      chk_w_q        <= mst_req.w;
    end
  end

  // -------------------------------------------------------------------------
  // Test helpers
  // -------------------------------------------------------------------------
  task automatic do_reset();
    // Assert and deassert reset on the inactive clock edge, so the release
    // never races the clocked processes at a posedge (event-driven
    // simulators would otherwise schedule the two nondeterministically).
    @(negedge clk);
    rst_n = 1'b0;
    cfg_aw_waits_for_wvalid = 1'b0;
    cfg_wready_stall        = 0;
    cfg_awready_hold        = 0;
    cfg_b_hold              = 1'b0;
    us_aw_queue.delete();
    us_w_queue.delete();
    us_ar_queue.delete();
    ds_r_queue.delete();
    ds_b_id_queue.delete();
    ds_aw_log.delete();
    ds_ar_log.delete();
    ds_w_log.delete();
    us_b_log.delete();
    us_r_log.delete();
    ds_b_launched = 0;
    repeat (5) @(posedge clk);
    @(negedge clk);
    rst_n = 1'b1;
    @(posedge clk);
  endtask

  task automatic push_write(input addr_t addr, input axi_pkg::len_t len,
                            input axi_pkg::burst_t burst, input id_t id,
                            input axi_pkg::size_t size, input data_t data_base);
    // Cache must be modifiable: axi_burst_unwrap only splits modifiable WRAP
    // bursts (non-modifiable ones are routed to the error slave).
    us_aw_queue.push_back('{id: id, addr: addr, len: len, size: size, burst: burst,
                            cache: axi_pkg::CACHE_MODIFIABLE, default: '0});
    for (int unsigned i = 0; i <= len; i++) begin
      us_w_queue.push_back('{data: data_base + data_t'(i), strb: '1,
                             last: (i == len)});
    end
  endtask

  task automatic push_read(input addr_t addr, input axi_pkg::len_t len,
                           input axi_pkg::burst_t burst, input id_t id,
                           input axi_pkg::size_t size);
    us_ar_queue.push_back('{id: id, addr: addr, len: len, size: size, burst: burst,
                            cache: axi_pkg::CACHE_MODIFIABLE, default: '0});
  endtask

  // Wait until `cnt` B responses were received upstream; a timeout is the
  // deadlock symptom of issue #448.
  task automatic wait_b_count(input string tag, input int unsigned cnt);
    int unsigned n = 0;
    while ((us_b_log.size() < cnt) && (n < TbTimeout)) begin
      @(posedge clk);
      n++;
    end
    if (us_b_log.size() < cnt) begin
      $display("ERROR [%s] TIMEOUT: no B response after %0d cycles -- write deadlock (issue #448): ds.aw_valid=%b ds.aw_ready=%b ds.w_valid=%b ds.w_ready=%b",
             tag, TbTimeout, mst_req.aw_valid, mst_resp.aw_ready,
             mst_req.w_valid, mst_resp.w_ready);
      err_cnt++;
    end
  endtask

  task automatic wait_r_count(input string tag, input int unsigned cnt);
    int unsigned n = 0;
    while ((us_r_log.size() < cnt) && (n < TbTimeout)) begin
      @(posedge clk);
      n++;
    end
    if (us_r_log.size() < cnt) begin
      $display("ERROR [%s] TIMEOUT: got %0d/%0d R beats after %0d cycles",
             tag, us_r_log.size(), cnt, TbTimeout);
      err_cnt++;
    end
  endtask

  task automatic wait_ds_aw_count(input string tag, input int unsigned cnt);
    int unsigned n = 0;
    while ((ds_aw_log.size() < cnt) && (n < TbTimeout)) begin
      @(posedge clk);
      n++;
    end
    if (ds_aw_log.size() < cnt) begin
      $display("ERROR [%s] TIMEOUT: only %0d/%0d downstream AWs after %0d cycles",
               tag, ds_aw_log.size(), cnt, TbTimeout);
      err_cnt++;
    end
  endtask

  task automatic check_ds_aw(input string tag, input int unsigned idx,
                             input addr_t addr, input axi_pkg::len_t len,
                             input axi_pkg::burst_t burst);
    if (idx >= ds_aw_log.size()) begin
      $display("ERROR [%s] expected downstream AW[%0d], but only %0d AWs seen",
             tag, idx, ds_aw_log.size());
      err_cnt++;
    end else if ((ds_aw_log[idx].addr !== addr) || (ds_aw_log[idx].len !== len)
        || (ds_aw_log[idx].burst !== burst)) begin
      $display("ERROR [%s] downstream AW[%0d] mismatch: got addr=0x%08x len=%0d burst=%0d, exp addr=0x%08x len=%0d burst=%0d",
             tag, idx, ds_aw_log[idx].addr, ds_aw_log[idx].len, ds_aw_log[idx].burst,
             addr, len, burst);
      err_cnt++;
    end
  endtask

  task automatic check_ds_ar(input string tag, input int unsigned idx,
                             input addr_t addr, input axi_pkg::len_t len,
                             input axi_pkg::burst_t burst);
    if (idx >= ds_ar_log.size()) begin
      $display("ERROR [%s] expected downstream AR[%0d], but only %0d ARs seen",
             tag, idx, ds_ar_log.size());
      err_cnt++;
    end else if ((ds_ar_log[idx].addr !== addr) || (ds_ar_log[idx].len !== len)
        || (ds_ar_log[idx].burst !== burst)) begin
      $display("ERROR [%s] downstream AR[%0d] mismatch: got addr=0x%08x len=%0d burst=%0d, exp addr=0x%08x len=%0d burst=%0d",
             tag, idx, ds_ar_log[idx].addr, ds_ar_log[idx].len, ds_ar_log[idx].burst,
             addr, len, burst);
      err_cnt++;
    end
  endtask

  task automatic check_ds_w(input string tag, input int unsigned idx,
                            input data_t data, input logic last);
    if (idx >= ds_w_log.size()) begin
      $display("ERROR [%s] expected downstream W[%0d], but only %0d W beats seen",
             tag, idx, ds_w_log.size());
      err_cnt++;
    end else if ((ds_w_log[idx].data !== data) || (ds_w_log[idx].last !== last)) begin
      $display("ERROR [%s] downstream W[%0d] mismatch: got data=0x%08x last=%b, exp data=0x%08x last=%b",
             tag, idx, ds_w_log[idx].data, ds_w_log[idx].last, data, last);
      err_cnt++;
    end
  endtask

  task automatic check_us_r(input string tag, input int unsigned idx,
                            input data_t data, input logic last);
    if (idx >= us_r_log.size()) begin
      $display("ERROR [%s] expected upstream R[%0d], but only %0d R beats seen",
             tag, idx, us_r_log.size());
      err_cnt++;
    end else if ((us_r_log[idx].data !== data) || (us_r_log[idx].last !== last)) begin
      $display("ERROR [%s] upstream R[%0d] mismatch: got data=0x%08x last=%b, exp data=0x%08x last=%b",
             tag, idx, us_r_log[idx].data, us_r_log[idx].last, data, last);
      err_cnt++;
    end
  endtask

  task automatic check_count(input string tag, input string what,
                             input int unsigned got, input int unsigned exp);
    if (got !== exp) begin
      $display("ERROR [%s] %s count mismatch: got %0d, exp %0d", tag, what, got, exp);
      err_cnt++;
    end
  endtask

  // All upstream B responses must be OKAY (an SLVERR here would mean the
  // transaction was routed to the internal error slave instead).
  task automatic check_us_b(input string tag, input int unsigned idx, input id_t id);
    if (idx >= us_b_log.size()) begin
      $display("ERROR [%s] expected upstream B[%0d], but only %0d Bs seen",
               tag, idx, us_b_log.size());
      err_cnt++;
    end else if ((us_b_log[idx].resp !== axi_pkg::RESP_OKAY)
        || (us_b_log[idx].id !== id)) begin
      $display("ERROR [%s] upstream B[%0d] mismatch: got id=%0d resp=%0d, exp id=%0d resp=OKAY",
               tag, idx, us_b_log[idx].id, us_b_log[idx].resp, id);
      err_cnt++;
    end
  endtask

  // -------------------------------------------------------------------------
  // Test program
  // -------------------------------------------------------------------------
  initial begin : proc_tests
    err_cnt                 = 0;
    cfg_aw_waits_for_wvalid = 1'b0;
    cfg_wready_stall        = 0;
    rst_n                   = 1'b0;

    // T1: plain INCR burst, well-behaved slave (baseline).
    do_reset();
    $display("T1: INCR len=3, normal slave");
    push_write(32'h0000_0040, 8'd3, axi_pkg::BURST_INCR, 2'd0, 3'd2, 32'h1000_0000);
    wait_b_count("T1", 1);
    check_count("T1", "downstream AW", ds_aw_log.size(), 1);
    check_ds_aw("T1", 0, 32'h0000_0040, 8'd3, axi_pkg::BURST_INCR);
    check_count("T1", "downstream W", ds_w_log.size(), 4);
    for (int unsigned i = 0; i < 4; i++) begin
      check_ds_w("T1", i, 32'h1000_0000 + i, (i == 3));
    end
    check_count("T1", "upstream B", us_b_log.size(), 1);
    check_us_b("T1", 0, 2'd0);

    // T2: WRAP burst 4x4B @ 0x0C -> split into (0x0C, len 0) + (0x00, len 2).
    do_reset();
    $display("T2: WRAP len=3 @ 0x0C, normal slave (split)");
    push_write(32'h0000_000C, 8'd3, axi_pkg::BURST_WRAP, 2'd1, 3'd2, 32'h2000_0000);
    wait_b_count("T2", 1);
    check_count("T2", "downstream AW", ds_aw_log.size(), 2);
    check_ds_aw("T2", 0, 32'h0000_000C, 8'd0, axi_pkg::BURST_INCR);
    check_ds_aw("T2", 1, 32'h0000_0000, 8'd2, axi_pkg::BURST_INCR);
    check_count("T2", "downstream W", ds_w_log.size(), 4);
    check_ds_w("T2", 0, 32'h2000_0000, 1'b1);  // end of first downstream burst
    check_ds_w("T2", 1, 32'h2000_0001, 1'b0);
    check_ds_w("T2", 2, 32'h2000_0002, 1'b0);
    check_ds_w("T2", 3, 32'h2000_0003, 1'b1);  // end of second downstream burst
    check_count("T2", "upstream B", us_b_log.size(), 1);  // two downstream Bs merged
    check_us_b("T2", 0, 2'd1);

    // T3: WRAP burst aligned to its wrap boundary -> plain feedthrough as INCR.
    do_reset();
    $display("T3: WRAP len=3 @ 0x00, normal slave (feedthrough)");
    push_write(32'h0000_0000, 8'd3, axi_pkg::BURST_WRAP, 2'd2, 3'd2, 32'h3000_0000);
    wait_b_count("T3", 1);
    check_count("T3", "downstream AW", ds_aw_log.size(), 1);
    check_ds_aw("T3", 0, 32'h0000_0000, 8'd3, axi_pkg::BURST_INCR);
    check_count("T3", "downstream W", ds_w_log.size(), 4);
    for (int unsigned i = 0; i < 4; i++) begin
      check_ds_w("T3", i, 32'h3000_0000 + i, (i == 3));
    end
    check_count("T3", "upstream B", us_b_log.size(), 1);
    check_us_b("T3", 0, 2'd2);

    // T4: regression for issue #448, INCR: the slave asserts AWREADY only
    // once it observes WVALID.  Without the fix this deadlocks.
    do_reset();
    cfg_aw_waits_for_wvalid = 1'b1;
    $display("T4: INCR len=3, slave waits for WVALID before AWREADY (issue #448)");
    push_write(32'h0000_0080, 8'd3, axi_pkg::BURST_INCR, 2'd0, 3'd2, 32'h4000_0000);
    wait_b_count("T4", 1);
    check_count("T4", "downstream AW", ds_aw_log.size(), 1);
    check_ds_aw("T4", 0, 32'h0000_0080, 8'd3, axi_pkg::BURST_INCR);
    check_count("T4", "downstream W", ds_w_log.size(), 4);
    for (int unsigned i = 0; i < 4; i++) begin
      check_ds_w("T4", i, 32'h4000_0000 + i, (i == 3));
    end
    check_count("T4", "upstream B", us_b_log.size(), 1);
    check_us_b("T4", 0, 2'd0);

    // T5: regression for issue #448, split WRAP burst.
    do_reset();
    cfg_aw_waits_for_wvalid = 1'b1;
    $display("T5: WRAP len=3 @ 0x0C, slave waits for WVALID before AWREADY (issue #448)");
    push_write(32'h0000_000C, 8'd3, axi_pkg::BURST_WRAP, 2'd1, 3'd2, 32'h5000_0000);
    wait_b_count("T5", 1);
    check_count("T5", "downstream AW", ds_aw_log.size(), 2);
    check_ds_aw("T5", 0, 32'h0000_000C, 8'd0, axi_pkg::BURST_INCR);
    check_ds_aw("T5", 1, 32'h0000_0000, 8'd2, axi_pkg::BURST_INCR);
    check_count("T5", "downstream W", ds_w_log.size(), 4);
    check_ds_w("T5", 0, 32'h5000_0000, 1'b1);
    check_ds_w("T5", 1, 32'h5000_0001, 1'b0);
    check_ds_w("T5", 2, 32'h5000_0002, 1'b0);
    check_ds_w("T5", 3, 32'h5000_0003, 1'b1);
    check_count("T5", "upstream B", us_b_log.size(), 1);
    check_us_b("T5", 0, 2'd1);

    // T6: WREADY backpressure; the stability checker verifies that WVALID and
    // the W payload stay stable while stalled.
    do_reset();
    cfg_wready_stall = 3;
    $display("T6: WRAP len=3 @ 0x0C with WREADY backpressure (1 ready cycle in 4)");
    push_write(32'h0000_000C, 8'd3, axi_pkg::BURST_WRAP, 2'd3, 3'd2, 32'h6000_0000);
    wait_b_count("T6", 1);
    check_count("T6", "downstream AW", ds_aw_log.size(), 2);
    check_count("T6", "downstream W", ds_w_log.size(), 4);
    check_ds_w("T6", 0, 32'h6000_0000, 1'b1);
    check_ds_w("T6", 1, 32'h6000_0001, 1'b0);
    check_ds_w("T6", 2, 32'h6000_0002, 1'b0);
    check_ds_w("T6", 3, 32'h6000_0003, 1'b1);
    check_count("T6", "upstream B", us_b_log.size(), 1);
    check_us_b("T6", 0, 2'd3);

    // T7: WRAP read @ 0x0C: split ARs downstream, upstream RLAST only on the
    // final beat, data in wrap order.
    do_reset();
    $display("T7: WRAP read len=3 @ 0x0C");
    push_read(32'h0000_000C, 8'd3, axi_pkg::BURST_WRAP, 2'd1, 3'd2);
    wait_r_count("T7", 4);
    check_count("T7", "downstream AR", ds_ar_log.size(), 2);
    check_count("T7", "upstream R", us_r_log.size(), 4);
    check_ds_ar("T7", 0, 32'h0000_000C, 8'd0, axi_pkg::BURST_INCR);
    check_ds_ar("T7", 1, 32'h0000_0000, 8'd2, axi_pkg::BURST_INCR);
    check_us_r("T7", 0, 32'h0000_000C, 1'b0);
    check_us_r("T7", 1, 32'h0000_0000, 1'b0);
    check_us_r("T7", 2, 32'h0000_0004, 1'b0);
    check_us_r("T7", 3, 32'h0000_0008, 1'b1);

    // T8: several back-to-back writes (counter reuse), mixed INCR/WRAP.
    do_reset();
    $display("T8: back-to-back INCR / WRAP / INCR writes");
    push_write(32'h0000_0100, 8'd1, axi_pkg::BURST_INCR, 2'd0, 3'd2, 32'h7000_0000);
    push_write(32'h0000_001C, 8'd3, axi_pkg::BURST_WRAP, 2'd1, 3'd2, 32'h7100_0000);
    push_write(32'h0000_0200, 8'd0, axi_pkg::BURST_INCR, 2'd2, 3'd2, 32'h7200_0000);
    wait_b_count("T8", 3);
    check_count("T8", "downstream AW", ds_aw_log.size(), 4);
    check_ds_aw("T8", 0, 32'h0000_0100, 8'd1, axi_pkg::BURST_INCR);
    check_ds_aw("T8", 1, 32'h0000_001C, 8'd0, axi_pkg::BURST_INCR);
    check_ds_aw("T8", 2, 32'h0000_0010, 8'd2, axi_pkg::BURST_INCR);
    check_ds_aw("T8", 3, 32'h0000_0200, 8'd0, axi_pkg::BURST_INCR);
    check_count("T8", "downstream W", ds_w_log.size(), 7);
    check_ds_w("T8", 0, 32'h7000_0000, 1'b0);
    check_ds_w("T8", 1, 32'h7000_0001, 1'b1);
    check_ds_w("T8", 2, 32'h7100_0000, 1'b1);
    check_ds_w("T8", 3, 32'h7100_0001, 1'b0);
    check_ds_w("T8", 4, 32'h7100_0002, 1'b0);
    check_ds_w("T8", 5, 32'h7100_0003, 1'b1);
    check_ds_w("T8", 6, 32'h7200_0000, 1'b1);
    check_count("T8", "upstream B", us_b_log.size(), 3);
    check_us_b("T8", 0, 2'd0);
    check_us_b("T8", 1, 2'd1);
    check_us_b("T8", 2, 2'd2);

    // T9: B-counter exhaustion + long AW backpressure (fix hardening).  The
    // slave withholds all B responses, so each write keeps one B counter
    // occupied (MaxWriteTxns = 4).  The 4th AW occupies the last counter
    // while its AWREADY is held off until long after its W beats went
    // through: `&cnt_alloc_gnt` is then low with the AW still presented,
    // which must neither retract AWVALID (stability checker) nor allocate
    // twice (one-shot flag; a double allocation would corrupt WLAST or the
    // B count below).  A 5th write must not get a downstream AW until a
    // counter frees up.
    do_reset();
    cfg_aw_waits_for_wvalid = 1'b1;
    cfg_awready_hold        = 12;
    cfg_b_hold              = 1'b1;
    $display("T9: B-counter exhaustion + delayed AWREADY (one-shot allocation)");
    for (int unsigned i = 0; i < 5; i++) begin
      push_write(32'h0000_0300 + 32'h40 * i, 8'd1, axi_pkg::BURST_INCR, id_t'(i),
                 3'd2, 32'h8000_0000 + 32'h100 * i);
    end
    wait_ds_aw_count("T9", 4);
    // All four B counters are now occupied (no B responses yet): the 5th AW
    // must stay back until a counter frees up.
    repeat (30) @(posedge clk);
    check_count("T9", "downstream AW while counters exhausted", ds_aw_log.size(), 4);
    check_count("T9", "upstream B while withheld", us_b_log.size(), 0);
    // Release the B responses: everything must complete.
    cfg_b_hold = 1'b0;
    wait_b_count("T9", 5);
    check_count("T9", "downstream AW", ds_aw_log.size(), 5);
    check_count("T9", "downstream W", ds_w_log.size(), 10);
    for (int unsigned i = 0; i < 5; i++) begin
      check_us_b("T9", i, id_t'(i));
      check_ds_aw("T9", i, 32'h0000_0300 + 32'h40 * i, 8'd1, axi_pkg::BURST_INCR);
      check_ds_w("T9", 2 * i,     32'h8000_0000 + 32'h100 * i, 1'b0);
      check_ds_w("T9", 2 * i + 1, 32'h8000_0000 + 32'h100 * i + 1, 1'b1);
    end

    // Summary.
    if (err_cnt == 0) begin
      $display("All tests passed.");
    end else begin
      $fatal(1, "TESTS FAILED: %0d error(s).", err_cnt);
    end
    $finish;
  end

  // Global watchdog in case the test program itself hangs.
  initial begin : proc_watchdog
    repeat (100 * TbTimeout) @(posedge clk);
    $fatal(1, "GLOBAL WATCHDOG TIMEOUT -- aborting.");
  end

`ifdef TB_AXI_BURST_UNWRAP_DUMP
  initial begin : proc_dump
    $dumpfile("tb_axi_burst_unwrap.vcd");
    $dumpvars(0, tb_axi_burst_unwrap);
  end
`endif

endmodule
