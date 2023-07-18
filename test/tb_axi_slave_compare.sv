// Copyright (c) 2020 ETH Zurich and University of Bologna
// SPDX-License-Identifier: SHL-0.51
//
// Authors:
// - Andreas Kurth <akurth@iis.ee.ethz.ch>
// - Thomas Benz <tbenz@iis.ee.ethz.ch>
// - Michael Rogenmoser <michaero@iis.ee.ethz.ch>

`include "axi/assign.svh"
`include "axi/typedef.svh"

/// Testbench for `axi_slave_compare`
module tb_axi_slave_compare #(
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

  AXI_BUS #(
    .AXI_ADDR_WIDTH (TbAddrWidth),
    .AXI_DATA_WIDTH (TbDataWidth),
    .AXI_ID_WIDTH   (TbIdWidth),
    .AXI_USER_WIDTH (TbUserWidth)
  ) axi ();

  AXI_BUS_DV #(
    .AXI_ADDR_WIDTH (TbAddrWidth),
    .AXI_DATA_WIDTH (TbDataWidth),
    .AXI_ID_WIDTH   (TbIdWidth),
    .AXI_USER_WIDTH (TbUserWidth)
  ) axi_dv (clk);
  typedef axi_test::axi_driver #(
    .AW(TbAddrWidth), .DW(TbDataWidth), .IW(TbIdWidth), .UW(TbUserWidth),
    .TA(1ns), .TT(6ns)
  ) drv_t;
  drv_t drv = new(axi_dv);

  `AXI_ASSIGN (axi, axi_dv)

  `AXI_TYPEDEF_ALL(axi, addr_t, id_t, data_t, strb_t, user_t)

  axi_req_t   axi_req, axi_req_a_out, axi_req_b_out, axi_req_b_dly;
  axi_resp_t  axi_rsp, axi_rsp_a_out, axi_rsp_b_out, axi_rsp_b_dly;

  `AXI_ASSIGN_TO_REQ(axi_req, axi)
  `AXI_ASSIGN_FROM_RESP(axi, axi_rsp)

  axi_slave_compare #(
    .AxiIdWidth     ( TbIdWidth       ),
    .FifoDepth      ( 32'd16          ),
    .axi_aw_chan_t  ( axi_aw_chan_t   ),
    .axi_w_chan_t   ( axi_w_chan_t    ),
    .axi_b_chan_t   ( axi_b_chan_t    ),
    .axi_ar_chan_t  ( axi_ar_chan_t   ),
    .axi_r_chan_t   ( axi_r_chan_t    ),
    .axi_req_t      ( axi_req_t       ),
    .axi_rsp_t      ( axi_resp_t      )
  ) i_axi_bus_compare (
    .clk_i          ( clk           ),
    .rst_ni         ( rst_n         ),
    .testmode_i     ( 1'b0          ),
    .axi_mst_req_i  ( axi_req       ),
    .axi_mst_rsp_o  ( axi_rsp       ),
    .axi_ref_req_o  ( axi_req_a_out ),
    .axi_ref_rsp_i  ( axi_rsp_a_out ),
    .axi_test_req_o ( axi_req_b_out ),
    .axi_test_rsp_i ( axi_rsp_b_out ),
    .aw_mismatch_o  ( ),
    .w_mismatch_o   ( ),
    .b_mismatch_o   ( ),
    .ar_mismatch_o  ( ),
    .r_mismatch_o   ( ),
    .mismatch_o     ( ),
    .busy_o         ( )
  );

  axi_sim_mem #(
    .AddrWidth(TbAddrWidth),
    .DataWidth(TbDataWidth),
    .IdWidth  (TbIdWidth),
    .UserWidth(TbUserWidth),
    .axi_req_t(axi_req_t),
    .axi_rsp_t(axi_resp_t),
    .ApplDelay(TbApplDelay),
    .AcqDelay (TbAcqDelay)
  ) i_axi_sim_mem_a (
    .clk_i             ( clk           ),
    .rst_ni            ( rst_n         ),
    .axi_req_i         ( axi_req_a_out ),
    .axi_rsp_o         ( axi_rsp_a_out ),
    .mon_w_valid_o     ( ),
    .mon_w_addr_o      ( ),
    .mon_w_data_o      ( ),
    .mon_w_id_o        ( ),
    .mon_w_user_o      ( ),
    .mon_w_beat_count_o( ),
    .mon_w_last_o      ( ),
    .mon_r_valid_o     ( ),
    .mon_r_addr_o      ( ),
    .mon_r_data_o      ( ),
    .mon_r_id_o        ( ),
    .mon_r_user_o      ( ),
    .mon_r_beat_count_o( ),
    .mon_r_last_o      ( )
  );

  axi_multicut #(
    .NoCuts    (8),
    .aw_chan_t (axi_aw_chan_t),
    .w_chan_t  (axi_w_chan_t),
    .b_chan_t  (axi_b_chan_t),
    .ar_chan_t (axi_ar_chan_t),
    .r_chan_t  (axi_r_chan_t),
    .axi_req_t (axi_req_t),
    .axi_resp_t(axi_resp_t)
  ) i_axi_multicut (
    .clk_i      ( clk           ),
    .rst_ni     ( rst_n         ),
    .slv_req_i  ( axi_req_b_out ),
    .slv_resp_o ( axi_rsp_b_out ),
    .mst_req_o  ( axi_req_b_dly ),
    .mst_resp_i ( axi_rsp_b_dly )
  );

  axi_sim_mem #(
    .AddrWidth(TbAddrWidth),
    .DataWidth(TbDataWidth),
    .IdWidth  (TbIdWidth),
    .UserWidth(TbUserWidth),
    .axi_req_t(axi_req_t),
    .axi_rsp_t(axi_resp_t),
    .ApplDelay(TbApplDelay),
    .AcqDelay (TbAcqDelay)
  ) i_axi_sim_mem_b (
    .clk_i             ( clk            ),
    .rst_ni            ( rst_n          ),
    .axi_req_i         ( axi_req_b_dly  ),
    .axi_rsp_o         ( axi_rsp_b_dly  ),
    .mon_w_valid_o     ( ),
    .mon_w_addr_o      ( ),
    .mon_w_data_o      ( ),
    .mon_w_id_o        ( ),
    .mon_w_user_o      ( ),
    .mon_w_beat_count_o( ),
    .mon_w_last_o      ( ),
    .mon_r_valid_o     ( ),
    .mon_r_addr_o      ( ),
    .mon_r_data_o      ( ),
    .mon_r_id_o        ( ),
    .mon_r_user_o      ( ),
    .mon_r_beat_count_o( ),
    .mon_r_last_o      ( )
  );


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
`ifdef XSIM
    // std::randomize(aw_beat) may behave differently to aw_beat.randomize() wrt. limited ranges
    // Keeping alternate implementation for XSIM only
    rand_success = std::randomize(aw_beat); assert (rand_success);
`else
    rand_success = aw_beat.randomize(); assert (rand_success);
`endif
    aw_beat.ax_addr >>= $clog2(StrbWidth); // align address with data width
    aw_beat.ax_addr <<= $clog2(StrbWidth);
    aw_beat.ax_len = $urandom();
    aw_beat.ax_size = $clog2(StrbWidth);
    aw_beat.ax_burst = axi_pkg::BURST_INCR;
    drv.send_aw(aw_beat);
    // W beats
    for (int unsigned i = 0; i <= aw_beat.ax_len; i++) begin
`ifdef XSIM
      // std::randomize(w_beat) may behave differently to w_beat.randomize() wrt. limited ranges
      // Keeping alternate implementation for XSIM only
      rand_success = std::randomize(w_beat); assert (rand_success);
`else
      rand_success = w_beat.randomize(); assert (rand_success);
`endif
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
