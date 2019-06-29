// Copyright 2019 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Testbench for axi_burst_splitter

`include "axi/assign.svh"
`include "axi/typedef.svh"

module tb_axi_burst_splitter #(
  // AXI Parameters
  parameter int unsigned ADDR_WIDTH = 32,
  parameter int unsigned DATA_WIDTH = 64,
  parameter int unsigned ID_WIDTH = 4,
  parameter int unsigned USER_WIDTH = 2,
  parameter int unsigned MAX_READ_TXNS = 10,
  parameter int unsigned MAX_WRITE_TXNS = 10,
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

  typedef logic [ADDR_WIDTH-1:0]    addr_t;
  typedef logic [DATA_WIDTH-1:0]    data_t;
  typedef logic [ID_WIDTH-1:0]      id_t;
  typedef logic [DATA_WIDTH/8-1:0]  strb_t;
  typedef logic [USER_WIDTH-1:0]    user_t;
  `AXI_TYPEDEF_AW_CHAN_T(aw_chan_t, addr_t, id_t, user_t);
  `AXI_TYPEDEF_W_CHAN_T(w_chan_t, data_t, strb_t, user_t);
  `AXI_TYPEDEF_B_CHAN_T(b_chan_t, id_t, user_t);
  `AXI_TYPEDEF_AR_CHAN_T(ar_chan_t, addr_t, id_t, user_t);
  `AXI_TYPEDEF_R_CHAN_T(r_chan_t, data_t, id_t, user_t);
  `AXI_TYPEDEF_REQ_T(req_t, aw_chan_t, w_chan_t, ar_chan_t);
  `AXI_TYPEDEF_RESP_T(resp_t, b_chan_t, r_chan_t);

  logic clk,
        rst_n;

  clk_rst_gen #(
    .CLK_PERIOD     (TCLK),
    .RST_CLK_CYCLES (5)
  ) i_clk_rst_gen (
    .clk_o  (clk),
    .rst_no (rst_n)
  );

  AXI_BUS_DV #(
    .AXI_ADDR_WIDTH (ADDR_WIDTH),
    .AXI_DATA_WIDTH (DATA_WIDTH),
    .AXI_ID_WIDTH   (ID_WIDTH),
    .AXI_USER_WIDTH (USER_WIDTH)
  ) upstream_dv (
    .clk_i  (clk)
  );
  req_t   upstream_req;
  resp_t  upstream_resp;
  `AXI_ASSIGN_TO_REQ(upstream_req, upstream_dv);
  `AXI_ASSIGN_FROM_RESP(upstream_dv, upstream_resp);

  AXI_BUS_DV #(
    .AXI_ADDR_WIDTH (ADDR_WIDTH),
    .AXI_DATA_WIDTH (DATA_WIDTH),
    .AXI_ID_WIDTH   (ID_WIDTH),
    .AXI_USER_WIDTH (USER_WIDTH)
  ) downstream_dv (
    .clk_i  (clk)
  );
  req_t   downstream_req;
  resp_t  downstream_resp;
  `AXI_ASSIGN_FROM_REQ(downstream_dv, downstream_req);
  `AXI_ASSIGN_TO_RESP(downstream_resp, downstream_dv);

  axi_burst_splitter #(
    .MAX_READ_TXNS  (MAX_READ_TXNS),
    .AW             (ADDR_WIDTH),
    .DW             (DATA_WIDTH),
    .IW             (ID_WIDTH),
    .UW             (USER_WIDTH),
    .req_t          (req_t),
    .resp_t         (resp_t)
  ) dut (
    .clk_i  (clk),
    .rst_ni (rst_n),
    .req_i  (upstream_req),
    .resp_o (upstream_resp),
    .req_o  (downstream_req),
    .resp_i (downstream_resp)
  );

  // AXI Master
  logic mst_done = 1'b0;
  axi_test::rand_axi_master #(
    .AW(ADDR_WIDTH), .DW(DATA_WIDTH), .IW(ID_WIDTH), .UW(USER_WIDTH),
    .TA(TA), .TT(TT),
    .MAX_READ_TXNS        (MAX_READ_TXNS),
    .MAX_WRITE_TXNS       (MAX_WRITE_TXNS),
    .AX_MIN_WAIT_CYCLES   (REQ_MIN_WAIT_CYCLES),
    .AX_MAX_WAIT_CYCLES   (REQ_MAX_WAIT_CYCLES),
    .W_MIN_WAIT_CYCLES    (REQ_MIN_WAIT_CYCLES),
    .W_MAX_WAIT_CYCLES    (REQ_MAX_WAIT_CYCLES),
    .RESP_MIN_WAIT_CYCLES (RESP_MIN_WAIT_CYCLES),
    .RESP_MAX_WAIT_CYCLES (RESP_MAX_WAIT_CYCLES),
    .AXI_MAX_BURST_LEN    (17),
    .AXI_ATOPS            (1'b0)
  ) axi_master = new(upstream_dv);
  initial begin
    axi_master.reset();
    wait(rst_n);
    axi_master.run(N_TXNS, N_TXNS, {ADDR_WIDTH{1'b0}}, {ADDR_WIDTH{1'b1}});
    mst_done = 1'b1;
  end

  initial begin
    wait (mst_done);
    $finish();
  end

  // AXI Slave
  axi_test::rand_axi_slave #(
    .AW(ADDR_WIDTH), .DW(DATA_WIDTH), .IW(ID_WIDTH), .UW(USER_WIDTH),
    .TA(TA), .TT(TT),
    .AX_MIN_WAIT_CYCLES   (RESP_MIN_WAIT_CYCLES),
    .AX_MAX_WAIT_CYCLES   (RESP_MAX_WAIT_CYCLES),
    .R_MIN_WAIT_CYCLES    (RESP_MIN_WAIT_CYCLES),
    .R_MAX_WAIT_CYCLES    (RESP_MAX_WAIT_CYCLES),
    .RESP_MIN_WAIT_CYCLES (RESP_MIN_WAIT_CYCLES),
    .RESP_MAX_WAIT_CYCLES (RESP_MAX_WAIT_CYCLES)
  ) axi_slave = new(downstream_dv);
  initial begin
    axi_slave.reset();
    wait (rst_n);
    axi_slave.run();
  end

  // TODO: Monitoring and checking.

endmodule
