// Copyright (c) 2020 ETH Zurich and University of Bologna
// SPDX-License-Identifier: SHL-0.51
//
// Authors:
// - Andreas Kurth <akurth@iis.ee.ethz.ch>

`include "axi/assign.svh"
`include "axi/typedef.svh"

/// Testbench for `axi_sim_mem`
module tb_axi_sim_mem #(
  // TB Parameters
  parameter time TbTclk = 10ns,
  // Module Parameters
  parameter int unsigned TbAddrWidth = 32'd64,
  parameter int unsigned TbDataWidth = 32'd128,
  parameter int unsigned TbIdWidth = 32'd6,
  parameter int unsigned TbUserWidth = 32'd2,
  parameter bit TbWarnUninitialized = 1'b0,
  parameter time TbApplDelay = 2ns,
  parameter time TbAcqDelay = 8ns
);

  logic clk,
        rst_n;
  clk_rst_gen #(
    .ClkPeriod    (TbTclk),
    .RstClkCycles (5)
  ) i_clk_rst_gen (
    .clk_o  (clk),
    .rst_no (rst_n)
  );

  localparam int unsigned StrbWidth = TbDataWidth / 8;
  typedef logic [TbAddrWidth-1:0] addr_t;
  typedef logic [TbDataWidth-1:0] data_t;
  typedef logic [TbIdWidth-1:0]   id_t;
  typedef logic [StrbWidth-1:0] strb_t;
  typedef logic [TbUserWidth-1:0] user_t;
  `AXI_TYPEDEF_AW_CHAN_T(aw_t, addr_t, id_t, user_t)
  `AXI_TYPEDEF_W_CHAN_T(w_t, data_t, strb_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T(b_t, id_t, user_t)
  `AXI_TYPEDEF_AR_CHAN_T(ar_t, addr_t, id_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(r_t, data_t, id_t, user_t)
  `AXI_TYPEDEF_REQ_T(axi_req_t, aw_t, w_t, ar_t)
  `AXI_TYPEDEF_RESP_T(axi_rsp_t, b_t, r_t)

  axi_req_t req;
  axi_rsp_t rsp;
  axi_sim_mem #(
    .AddrWidth          (TbAddrWidth),
    .DataWidth          (TbDataWidth),
    .IdWidth            (TbIdWidth),
    .UserWidth          (TbUserWidth),
    .axi_req_t          (axi_req_t),
    .axi_rsp_t          (axi_rsp_t),
    .WarnUninitialized  (TbWarnUninitialized),
    .ApplDelay          (TbApplDelay),
    .AcqDelay           (TbAcqDelay)
  ) i_sim_mem (
    .clk_i      (clk),
    .rst_ni     (rst_n),
    .axi_req_i  (req),
    .axi_rsp_o  (rsp)
  );

  AXI_BUS_DV #(
    .AXI_ADDR_WIDTH (TbAddrWidth),
    .AXI_DATA_WIDTH (TbDataWidth),
    .AXI_ID_WIDTH   (TbIdWidth),
    .AXI_USER_WIDTH (TbUserWidth)
  ) axi_dv (clk);
  `AXI_ASSIGN_TO_REQ(req, axi_dv)
  `AXI_ASSIGN_FROM_RESP(axi_dv, rsp)
  typedef axi_test::axi_driver #(
    .AW(TbAddrWidth), .DW(TbDataWidth), .IW(TbIdWidth), .UW(TbUserWidth),
    .TA(1ns), .TT(6ns)
  ) drv_t;
  drv_t drv = new(axi_dv);

  // Simply read and write a random memory region.
  initial begin
    automatic logic rand_success;
    automatic data_t exp_data[$];
    automatic drv_t::ax_beat_t aw_beat = new, ar_beat = new;
    automatic drv_t::w_beat_t w_beat = new;
    automatic drv_t::b_beat_t b_beat;
    automatic drv_t::r_beat_t r_beat;
    drv.reset_master();
    wait (rst_n);
    // AW
    rand_success = aw_beat.randomize(); assert(rand_success);
    aw_beat.ax_addr >>= $clog2(StrbWidth); // align address with data width
    aw_beat.ax_addr <<= $clog2(StrbWidth);
    aw_beat.ax_len = $urandom();
    aw_beat.ax_size = $clog2(StrbWidth);
    aw_beat.ax_burst = axi_pkg::BURST_INCR;
    drv.send_aw(aw_beat);
    // W beats
    for (int unsigned i = 0; i <= aw_beat.ax_len; i++) begin
      rand_success = w_beat.randomize(); assert(rand_success);
      w_beat.w_strb = '1;
      if (i == aw_beat.ax_len) begin
        w_beat.w_last = 1'b1;
      end
      drv.send_w(w_beat);
      exp_data.push_back(w_beat.w_data);
    end
    // B
    drv.recv_b(b_beat);
    assert(b_beat.b_resp == axi_pkg::RESP_OKAY);
    // AR
    ar_beat.ax_addr = aw_beat.ax_addr;
    ar_beat.ax_len = aw_beat.ax_len;
    ar_beat.ax_size = aw_beat.ax_size;
    ar_beat.ax_burst = aw_beat.ax_burst;
    drv.send_ar(ar_beat);
    // R beats
    for (int unsigned i = 0; i <= ar_beat.ax_len; i++) begin
      automatic data_t exp = exp_data.pop_front();
      drv.recv_r(r_beat);
      assert(r_beat.r_data == exp) else
        $error("Received 0x%h != expected 0x%h!", r_beat.r_data, exp);
    end
    // Done.
    #(TbTclk);
    $finish();
  end

endmodule
