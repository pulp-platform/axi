// Copyright 2020 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Author: Andreas Kurth <akurth@iis.ee.ethz.ch>

`include "axi/assign.svh"
`include "axi/typedef.svh"

/// Testbench for `axi_modify_address`
module tb_axi_modify_address #(
  // DUT Parameters
  parameter int unsigned AXI_SLV_PORT_ADDR_WIDTH = 32,
  parameter int unsigned AXI_MST_PORT_ADDR_WIDTH = 48,
  parameter int unsigned AXI_DATA_WIDTH = 64,
  parameter int unsigned AXI_ID_WIDTH = 3,
  parameter int unsigned AXI_USER_WIDTH = 2,
  // TB Parameters
  parameter time TCLK = 10ns,
  parameter time TA = TCLK * 1/4,
  parameter time TT = TCLK * 3/4,
  parameter int unsigned REQ_MIN_WAIT_CYCLES = 0,
  parameter int unsigned REQ_MAX_WAIT_CYCLES = 10,
  parameter int unsigned RESP_MIN_WAIT_CYCLES = 0,
  parameter int unsigned RESP_MAX_WAIT_CYCLES = REQ_MAX_WAIT_CYCLES/2,
  parameter int unsigned N_TXNS = 1000
);

  timeunit 1ns;
  timeprecision 10ps;

  localparam int unsigned N_RD_TXNS = N_TXNS / 2;
  localparam int unsigned N_WR_TXNS = N_TXNS / 2;

  // Clock and Reset
  logic clk,
        rst_n;
  clk_rst_gen #(
    .CLK_PERIOD     (TCLK),
    .RST_CLK_CYCLES (5)
  ) i_clk_rst_gen (
    .clk_o  (clk),
    .rst_no (rst_n)
  );

  // AXI Interfaces
  AXI_BUS_DV #(
    .AXI_ADDR_WIDTH (AXI_SLV_PORT_ADDR_WIDTH),
    .AXI_DATA_WIDTH (AXI_DATA_WIDTH),
    .AXI_ID_WIDTH   (AXI_ID_WIDTH),
    .AXI_USER_WIDTH (AXI_USER_WIDTH)
  ) upstream_dv (
    .clk_i  (clk)
  );
  AXI_BUS #(
    .AXI_ADDR_WIDTH (AXI_SLV_PORT_ADDR_WIDTH),
    .AXI_DATA_WIDTH (AXI_DATA_WIDTH),
    .AXI_ID_WIDTH   (AXI_ID_WIDTH),
    .AXI_USER_WIDTH (AXI_USER_WIDTH)
  ) upstream ();
  `AXI_ASSIGN(upstream, upstream_dv)
  AXI_BUS_DV #(
    .AXI_ADDR_WIDTH (AXI_MST_PORT_ADDR_WIDTH),
    .AXI_DATA_WIDTH (AXI_DATA_WIDTH),
    .AXI_ID_WIDTH   (AXI_ID_WIDTH),
    .AXI_USER_WIDTH (AXI_USER_WIDTH)
  ) downstream_dv (
    .clk_i  (clk)
  );
  AXI_BUS #(
    .AXI_ADDR_WIDTH (AXI_MST_PORT_ADDR_WIDTH),
    .AXI_DATA_WIDTH (AXI_DATA_WIDTH),
    .AXI_ID_WIDTH   (AXI_ID_WIDTH),
    .AXI_USER_WIDTH (AXI_USER_WIDTH)
  ) downstream ();
  `AXI_ASSIGN(downstream_dv, downstream)

  // Types
  typedef logic [AXI_MST_PORT_ADDR_WIDTH-1:0]   addr_t;
  typedef logic [AXI_DATA_WIDTH-1:0]            data_t;
  typedef logic [AXI_ID_WIDTH-1:0]              id_t;
  typedef logic [AXI_MST_PORT_ADDR_WIDTH-13:0]  page_t;
  typedef logic [AXI_DATA_WIDTH/8-1:0]          strb_t;
  typedef logic [AXI_USER_WIDTH-1:0]            user_t;
  `AXI_TYPEDEF_AW_CHAN_T(aw_t, addr_t, id_t, user_t)
  `AXI_TYPEDEF_W_CHAN_T(w_t, data_t, strb_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T(b_t, id_t, user_t)
  `AXI_TYPEDEF_AR_CHAN_T(ar_t, addr_t, id_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(r_t, data_t, id_t, user_t)

  // DUT
  addr_t  mst_aw_addr,
          mst_ar_addr;
  axi_modify_address_intf #(
    .AXI_SLV_PORT_ADDR_WIDTH  (AXI_SLV_PORT_ADDR_WIDTH),
    .AXI_MST_PORT_ADDR_WIDTH  (AXI_MST_PORT_ADDR_WIDTH),
    .AXI_DATA_WIDTH           (AXI_DATA_WIDTH),
    .AXI_ID_WIDTH             (AXI_ID_WIDTH),
    .AXI_USER_WIDTH           (AXI_USER_WIDTH)
  ) i_dut (
    .slv            (upstream),
    .mst_aw_addr_i  (mst_aw_addr),
    .mst_ar_addr_i  (mst_ar_addr),
    .mst            (downstream)
  );

  // Test harness master
  typedef axi_test::axi_rand_master #(
    .AW                   (AXI_SLV_PORT_ADDR_WIDTH),
    .DW                   (AXI_DATA_WIDTH),
    .IW                   (AXI_ID_WIDTH),
    .UW                   (AXI_USER_WIDTH),
    .TA                   (TA),
    .TT                   (TT),
    .MAX_READ_TXNS        (N_TXNS),
    .MAX_WRITE_TXNS       (N_TXNS),
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
    wait (rst_n);
    axi_master.run(N_RD_TXNS, N_WR_TXNS);
    #(10*TCLK);
    $finish();
  end

  // Test harness slave
  typedef axi_test::axi_rand_slave #(
    .AW                   (AXI_MST_PORT_ADDR_WIDTH),
    .DW                   (AXI_DATA_WIDTH),
    .IW                   (AXI_ID_WIDTH),
    .UW                   (AXI_USER_WIDTH),
    .TA                   (TA),
    .TT                   (TT),
    .AX_MIN_WAIT_CYCLES   (RESP_MIN_WAIT_CYCLES),
    .AX_MAX_WAIT_CYCLES   (RESP_MAX_WAIT_CYCLES),
    .R_MIN_WAIT_CYCLES    (RESP_MIN_WAIT_CYCLES),
    .R_MAX_WAIT_CYCLES    (RESP_MAX_WAIT_CYCLES),
    .RESP_MIN_WAIT_CYCLES (RESP_MIN_WAIT_CYCLES),
    .RESP_MAX_WAIT_CYCLES (RESP_MAX_WAIT_CYCLES)
  ) axi_slave_t;
  axi_slave_t axi_slave = new(downstream_dv);
  initial begin
    wait (rst_n);
    axi_slave.run();
  end

  // Assign offset within page from upstream.
  assign mst_aw_addr[11:0] = upstream.aw_addr[11:0];
  assign mst_ar_addr[11:0] = upstream.ar_addr[11:0];

  // Randomize page number.
  page_t  mst_aw_page,
          mst_ar_page;
  assign mst_aw_addr[AXI_MST_PORT_ADDR_WIDTH-1:12] = mst_aw_page;
  assign mst_ar_addr[AXI_MST_PORT_ADDR_WIDTH-1:12] = mst_ar_page;
  initial begin
    logic rand_success;
    mst_aw_page = '0;
    mst_ar_page = '0;
    wait (rst_n);
    forever begin
      @(posedge clk);
      #TA;
      if (!(upstream.aw_valid && !upstream.aw_ready)) begin
        rand_success = std::randomize(mst_aw_page);
        assert(rand_success);
      end
      if (!(upstream.ar_valid && !upstream.ar_ready)) begin
        rand_success = std::randomize(mst_ar_page);
        assert(rand_success);
      end
    end
  end

  // Signals for expected and actual responses
  aw_t  aw_exp, aw_act;
  w_t   w_exp,  w_act;
  b_t   b_exp,  b_act;
  ar_t  ar_exp, ar_act;
  r_t   r_exp,  r_act;

  // Compute expected responses.
  always_comb begin
    `AXI_SET_TO_AW(aw_exp, upstream)
    aw_exp.addr = mst_aw_addr;
    `AXI_SET_TO_AR(ar_exp, upstream)
    ar_exp.addr = mst_ar_addr;
  end
  `AXI_ASSIGN_TO_W(w_exp, upstream)
  `AXI_ASSIGN_TO_B(b_exp, downstream)
  `AXI_ASSIGN_TO_R(r_exp, downstream)

  // Determine actual responses.
  `AXI_ASSIGN_TO_AW(aw_act, downstream)
  `AXI_ASSIGN_TO_W(w_act, downstream)
  `AXI_ASSIGN_TO_B(b_act, upstream)
  `AXI_ASSIGN_TO_AR(ar_act, downstream)
  `AXI_ASSIGN_TO_R(r_act, upstream)

  // Assert that actual responses match expected responses.
  default disable iff (~rst_n);
  aw: assert property(@(posedge clk)
    downstream.aw_valid |-> aw_act == aw_exp
  ) else $error("AW %p != %p!", aw_act, aw_exp);
  w: assert property(@(posedge clk)
    downstream.w_valid |-> w_act == w_exp
  ) else $error("W %p != %p!", w_act, w_exp);
  b: assert property(@(posedge clk)
    upstream.b_valid |-> b_act == b_exp
  ) else $error("B %p != %p!", b_act, b_exp);
  ar: assert property(@(posedge clk)
    downstream.ar_valid |-> ar_act == ar_exp
  ) else $error("AR %p != %p!", ar_act, ar_exp);
  r: assert property(@(posedge clk)
    upstream.r_valid |-> r_act == r_exp
  ) else $error("R %p != %p!", r_act, r_exp);

endmodule
