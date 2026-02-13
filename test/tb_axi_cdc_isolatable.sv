// Copyright 2019-2020 ETH Zurich and University of Bologna.
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
// - Andreas Kurth <akurth@iis.ee.ethz.ch>
// - Wolfgang Roenninger <wroennin@iis.ee.ethz.ch>
// - Luca Rufer <luca@mosaic-soc.ch>

`include "axi/typedef.svh"
`include "axi/assign.svh"

module tb_axi_cdc_isolatable #(
  // AXI Parameters
  parameter int unsigned AXI_AW = 32,
  parameter int unsigned AXI_DW = 64,
  parameter int unsigned AXI_IW = 4,
  parameter int unsigned AXI_UW = 2,
  parameter int unsigned AXI_MAX_READ_TXNS = 10,
  parameter int unsigned AXI_MAX_WRITE_TXNS = 12,
  // TB Parameters
  parameter time TCLK_UPSTREAM = 10ns,
  parameter time TA_UPSTREAM = TCLK_UPSTREAM * 1/4,
  parameter time TT_UPSTREAM = TCLK_UPSTREAM * 3/4,
  parameter time TCLK_DOWNSTREAM = 3ns,
  parameter time TA_DOWNSTREAM = TCLK_DOWNSTREAM * 1/4,
  parameter time TT_DOWNSTREAM = TCLK_DOWNSTREAM * 3/4,
  parameter int unsigned REQ_MIN_WAIT_CYCLES = 0,
  parameter int unsigned REQ_MAX_WAIT_CYCLES = 10,
  parameter int unsigned RESP_MIN_WAIT_CYCLES = 0,
  parameter int unsigned RESP_MAX_WAIT_CYCLES = REQ_MAX_WAIT_CYCLES/2,
  parameter int unsigned N_TXNS = 100,
  parameter int unsigned N_UPSTREAM_RSTS = 10,
  parameter int unsigned ISOLATE_MIN_WAIT_CYCLES = 0,
  parameter int unsigned ISOLATE_MAX_WAIT_CYCLES = 500
);

  localparam int unsigned N_RD_TXNS = N_TXNS / 2;
  localparam int unsigned N_WR_TXNS = N_TXNS / 2;

  // Clocks and Resets

  logic upstream_clk,
        upstream_rst_n,
        upstream_rst_gen_n,
        upstream_test_rst_n;

  clk_rst_gen #(
    .ClkPeriod    (TCLK_UPSTREAM),
    .RstClkCycles (5)
  ) i_clk_rst_gen_upstream (
    .clk_o  (upstream_clk),
    .rst_no (upstream_rst_gen_n)
  );

  assign upstream_rst_n = upstream_rst_gen_n & upstream_test_rst_n;

  logic downstream_clk,
        downstream_rst_n,
        downstream_rst_gen_n,
        downstream_test_rst_n;

  clk_rst_gen #(
    .ClkPeriod    (TCLK_DOWNSTREAM),
    .RstClkCycles (5)
  ) i_clk_rst_gen_downstream (
    .clk_o  (downstream_clk),
    .rst_no (downstream_rst_gen_n)
  );

  assign downstream_rst_n = downstream_rst_gen_n & downstream_test_rst_n;

  // AXI Interfaces

  AXI_BUS_DV #(
    .AXI_ADDR_WIDTH (AXI_AW),
    .AXI_DATA_WIDTH (AXI_DW),
    .AXI_ID_WIDTH   (AXI_IW),
    .AXI_USER_WIDTH (AXI_UW)
  ) upstream_dv (
    .clk_i  (upstream_clk)
  );

  AXI_BUS #(
    .AXI_ADDR_WIDTH (AXI_AW),
    .AXI_DATA_WIDTH (AXI_DW),
    .AXI_ID_WIDTH   (AXI_IW),
    .AXI_USER_WIDTH (AXI_UW)
  ) upstream ();

  `AXI_ASSIGN(upstream, upstream_dv)

  AXI_BUS_DV #(
    .AXI_ADDR_WIDTH (AXI_AW),
    .AXI_DATA_WIDTH (AXI_DW),
    .AXI_ID_WIDTH   (AXI_IW),
    .AXI_USER_WIDTH (AXI_UW)
  ) downstream_dv (
    .clk_i  (downstream_clk)
  );

  AXI_BUS #(
    .AXI_ADDR_WIDTH (AXI_AW),
    .AXI_DATA_WIDTH (AXI_DW),
    .AXI_ID_WIDTH   (AXI_IW),
    .AXI_USER_WIDTH (AXI_UW)
  ) downstream ();

  `AXI_ASSIGN(downstream_dv, downstream)

  // AXI Channel Structs

  typedef logic [AXI_AW-1:0]    addr_t;
  typedef logic [AXI_DW-1:0]    data_t;
  typedef logic [AXI_IW-1:0]    id_t;
  typedef logic [AXI_DW/8-1:0]  strb_t;
  typedef logic [AXI_UW-1:0]    user_t;

  `AXI_TYPEDEF_AW_CHAN_T(aw_chan_t, addr_t, id_t, user_t)
  `AXI_TYPEDEF_W_CHAN_T(w_chan_t, data_t, strb_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T(b_chan_t, id_t, user_t)
  `AXI_TYPEDEF_AR_CHAN_T(ar_chan_t, addr_t, id_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(r_chan_t, data_t, id_t, user_t)

  // Source Isolation signals
  logic src_isolate, src_isolated;

  // Dest Isolation signals
  logic dst_isolate, dst_isolated;

  axi_cdc_isolatable_intf #(
    .AXI_ADDR_WIDTH        (AXI_AW),
    .AXI_DATA_WIDTH        (AXI_DW),
    .AXI_ID_WIDTH          (AXI_IW),
    .AXI_USER_WIDTH        (AXI_UW),
    .ATOP_SUPPORT          (1'b1),
    .LOG_DEPTH             (2),
    .SYNC_STAGES           (2),
    .TERMINATE_TRANSACTION (0)
  ) dut (
    .src_clk_i      (upstream_clk),
    .src_rst_ni     (upstream_rst_n),
    .src_isolate_i  (src_isolate),
    .src_isolated_o (src_isolated),
    .src            (upstream),
    .dst_clk_i      (downstream_clk),
    .dst_rst_ni     (downstream_rst_n),
    .dst_isolate_i  (dst_isolate),
    .dst_isolated_o (dst_isolated),
    .dst            (downstream)
  );

  semaphore reset_lock;
  initial reset_lock = new(1);

  initial begin
    src_isolate <= 1'b0;
    downstream_test_rst_n <= 1'b1;
    wait (upstream_rst_n);

    forever begin
      automatic int rand_success;
      automatic int unsigned cycles;
      automatic bit reset_downstream;
      rand_success = std::randomize(cycles) with {
        cycles >= ISOLATE_MIN_WAIT_CYCLES;
        cycles <= ISOLATE_MAX_WAIT_CYCLES;
      };
      assert (rand_success) else $error("Failed to randomize wait cycles!");
      reset_downstream = $random;

      repeat (cycles) @(posedge upstream_clk);

      reset_lock.get();

      // src_isolate
      #(TA_UPSTREAM);
      src_isolate <= 1'b1;
      #(TT_UPSTREAM - TA_UPSTREAM);
      wait (src_isolated);

      // Optional downstream reset
      if (reset_downstream) begin
        @(posedge downstream_clk);
        #(TA_DOWNSTREAM);
        downstream_test_rst_n <= 1'b0;

        repeat (5) @(posedge downstream_clk);
        #(TA_DOWNSTREAM);
        downstream_test_rst_n <= 1'b1;
      end

      // Release Isolation
      @(posedge upstream_clk);
      #(TA_UPSTREAM);
      src_isolate <= 1'b0;
      #(TT_UPSTREAM - TA_UPSTREAM);
      wait (!src_isolated);

      reset_lock.put();
    end
  end

  typedef axi_test::axi_rand_master #(
    .AW                   (AXI_AW),
    .DW                   (AXI_DW),
    .IW                   (AXI_IW),
    .UW                   (AXI_UW),
    .TA                   (TA_UPSTREAM),
    .TT                   (TT_UPSTREAM),
    .MAX_READ_TXNS        (AXI_MAX_READ_TXNS),
    .MAX_WRITE_TXNS       (AXI_MAX_WRITE_TXNS),
    .AX_MIN_WAIT_CYCLES   (REQ_MIN_WAIT_CYCLES),
    .AX_MAX_WAIT_CYCLES   (REQ_MAX_WAIT_CYCLES),
    .W_MIN_WAIT_CYCLES    (REQ_MIN_WAIT_CYCLES),
    .W_MAX_WAIT_CYCLES    (REQ_MAX_WAIT_CYCLES),
    .RESP_MIN_WAIT_CYCLES (RESP_MIN_WAIT_CYCLES),
    .RESP_MAX_WAIT_CYCLES (RESP_MAX_WAIT_CYCLES),
    .AXI_MAX_BURST_LEN    (16)
  ) axi_master_t;
  axi_master_t axi_master = new(upstream_dv);

  initial begin
    dst_isolate <= 1'b0;
    upstream_test_rst_n <= 1'b1;
    wait (upstream_rst_n);

    axi_master.run(N_RD_TXNS, N_WR_TXNS);

    for (int unsigned i = 0; i < N_UPSTREAM_RSTS - 1; i++) begin
      automatic bit reset_upstream;
      automatic bit release_dst_iso_before_reset;
      reset_upstream = $random;
      release_dst_iso_before_reset = $random;

      reset_lock.get();

      // Isolate
      @(posedge downstream_clk);
      #(TA_DOWNSTREAM);
      dst_isolate <= 1'b1;
      #(TT_DOWNSTREAM - TA_DOWNSTREAM);
      wait (dst_isolated);

      // Optional isolate release before reset
      if (release_dst_iso_before_reset) begin
        @(posedge downstream_clk);
        #(TA_DOWNSTREAM);
        dst_isolate <= 1'b0;
        #(TT_DOWNSTREAM - TA_DOWNSTREAM);
        wait (!dst_isolated);
      end

      // Optional upstream reset
      if (reset_upstream) begin
        @(posedge upstream_clk);
        #(TA_UPSTREAM);
        upstream_test_rst_n <= 1'b0;

        repeat (5) @(posedge upstream_clk);
        #(TA_UPSTREAM);
        upstream_test_rst_n <= 1'b1;
      end

      // Optional isolate release after reset
      if (!release_dst_iso_before_reset) begin
        @(posedge downstream_clk);
        #(TA_DOWNSTREAM);
        dst_isolate <= 1'b0;
        #(TT_DOWNSTREAM - TA_DOWNSTREAM);
        wait (!dst_isolated);
      end

      reset_lock.put();

      axi_master.run(N_RD_TXNS, N_WR_TXNS);
    end
  end

  typedef axi_test::axi_rand_slave #(
    .AW                   (AXI_AW),
    .DW                   (AXI_DW),
    .IW                   (AXI_IW),
    .UW                   (AXI_UW),
    .TA                   (TA_DOWNSTREAM),
    .TT                   (TT_DOWNSTREAM),
    .AX_MIN_WAIT_CYCLES   (RESP_MIN_WAIT_CYCLES),
    .AX_MAX_WAIT_CYCLES   (RESP_MAX_WAIT_CYCLES),
    .R_MIN_WAIT_CYCLES    (RESP_MIN_WAIT_CYCLES),
    .R_MAX_WAIT_CYCLES    (RESP_MAX_WAIT_CYCLES),
    .RESP_MIN_WAIT_CYCLES (RESP_MIN_WAIT_CYCLES),
    .RESP_MAX_WAIT_CYCLES (RESP_MAX_WAIT_CYCLES)
  ) axi_slave_t;
  axi_slave_t axi_slave = new(downstream_dv);

  initial begin
    wait (downstream_rst_n);
    axi_slave.run();
  end

  ar_chan_t   mst_ar, slv_ar, ar_queue[$];
  aw_chan_t   mst_aw, slv_aw, aw_queue[$];
  b_chan_t    mst_b,  slv_b,  b_queue[$];
  r_chan_t    mst_r,  slv_r,  r_queue[$];
  w_chan_t    mst_w,  slv_w,  w_queue[$];

  `AXI_ASSIGN_TO_AR(mst_ar, upstream)
  `AXI_ASSIGN_TO_AR(slv_ar, downstream)
  `AXI_ASSIGN_TO_AW(mst_aw, upstream)
  `AXI_ASSIGN_TO_AW(slv_aw, downstream)
  `AXI_ASSIGN_TO_B(mst_b, upstream)
  `AXI_ASSIGN_TO_B(slv_b, downstream)
  `AXI_ASSIGN_TO_R(mst_r, upstream)
  `AXI_ASSIGN_TO_R(slv_r, downstream)
  `AXI_ASSIGN_TO_W(mst_w, upstream)
  `AXI_ASSIGN_TO_W(slv_w, downstream)

  logic mst_done = 1'b0;
  // Monitor and check upstream
  initial begin
    automatic b_chan_t exp_b;
    automatic r_chan_t exp_r;
    automatic int unsigned rd_cnt = 0, wr_cnt = 0;
    forever begin
      @(posedge upstream_clk);
      #(TT_UPSTREAM);
      if (upstream.aw_valid && upstream.aw_ready) begin
        aw_queue.push_back(mst_aw);
      end
      if (upstream.w_valid && upstream.w_ready) begin
        w_queue.push_back(mst_w);
      end
      if (upstream.b_valid && upstream.b_ready) begin
        exp_b = b_queue.pop_front();
        assert (mst_b == exp_b);
        wr_cnt++;
      end
      if (upstream.ar_valid && upstream.ar_ready) begin
        ar_queue.push_back(mst_ar);
      end
      if (upstream.r_valid && upstream.r_ready) begin
        exp_r = r_queue.pop_front();
        assert (mst_r == exp_r);
        if (upstream.r_last) begin
          rd_cnt++;
        end
      end
      if (rd_cnt == N_UPSTREAM_RSTS * N_RD_TXNS && wr_cnt == N_UPSTREAM_RSTS * N_WR_TXNS) begin
        mst_done = 1'b1;
      end
    end
  end

  // Monitor and check downstream
  initial begin
    automatic ar_chan_t exp_ar;
    automatic aw_chan_t exp_aw;
    automatic w_chan_t  exp_w;
    forever begin
      @(posedge downstream_clk);
      #(TT_DOWNSTREAM);
      if (downstream.aw_valid && downstream.aw_ready) begin
        exp_aw = aw_queue.pop_front();
        assert (slv_aw == exp_aw);
      end
      if (downstream.w_valid && downstream.w_ready) begin
        exp_w = w_queue.pop_front();
        assert (slv_w == exp_w);
      end
      if (downstream.b_valid && downstream.b_ready) begin
        b_queue.push_back(slv_b);
      end
      if (downstream.ar_valid && downstream.ar_ready) begin
        exp_ar = ar_queue.pop_front();
        assert (slv_ar == exp_ar);
      end
      if (downstream.r_valid && downstream.r_ready) begin
        r_queue.push_back(slv_r);
      end
    end
  end

  // Terminate simulation after all transactions have completed.
  initial begin
   wait (mst_done);
   #(10*TCLK_UPSTREAM);
   $finish();
  end

endmodule
