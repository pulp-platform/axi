// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Fabian Schuiki <fschuiki@iis.ee.ethz.ch>

import axi_pkg::*;

/// A synthesis test bench which instantiates various adapter variants.
module synth_bench (
  input logic clk_i,
  input logic rst_ni
);

  localparam int AXI_ADDR_WIDTH[6] = {32, 64, 1, 2, 42, 129};
  localparam int AXI_ID_USER_WIDTH[3] = {0, 1, 8};
  localparam int NUM_SLAVE_MASTER[3] = {1, 2, 4};

  // AXI_DATA_WIDTH = {8, 16, 32, 64, 128, 256, 512, 1024}
  for (genvar i = 0; i < 8; i++) begin
    localparam DW = (2**i) * 8;
    synth_slice #(.AW(32), .DW(DW), .IW(8), .UW(8)) s(.*);
  end

  // AXI_ADDR_WIDTH
  for (genvar i = 0; i < 6; i++) begin
    localparam int AW = AXI_ADDR_WIDTH[i];
    synth_slice #(.AW(AW), .DW(32), .IW(8), .UW(8)) s(.*);
  end

  // AXI_ID_WIDTH and AXI_USER_WIDTH
  for (genvar i = 0; i < 3; i++) begin
    localparam int IUW = AXI_ID_USER_WIDTH[i];
    synth_slice #(.AW(32), .DW(32), .IW(IUW), .UW(IUW)) s(.*);
  end

  // Crossbar
  for (genvar i = 0; i < 3; i++) begin : xbar_master
    localparam int NM = NUM_SLAVE_MASTER[i];
    for (genvar j = 0; j < 3; j++) begin : xbar_slave
      localparam int NS = NUM_SLAVE_MASTER[j];
      axi_lite_xbar_slice #(.NUM_MASTER(NM), .NUM_SLAVE(NS)) i_xbar (.*);
    end
  end

  // ATOP Filter
  for (genvar iID = 1; iID <= 8; iID++) begin
    localparam int IW = iID;
    for (genvar iTxn = 1; iTxn <= 12; iTxn++) begin
      localparam int WT = iTxn;
      synth_axi_atop_filter #(
        .AXI_ADDR_WIDTH     (64),
        .AXI_DATA_WIDTH     (64),
        .AXI_ID_WIDTH       (IW),
        .AXI_USER_WIDTH     (4),
        .AXI_MAX_WRITE_TXNS (WT)
      ) i_filter (.*);
    end
  end

  // Performance Monitor
  synth_axi_perf_mon #(
    // Number of monitored AXI interfaces
    .N_MON          (2),
    // AXI parameters
    .AW             (64),
    .IW             (4),
    // Capabilities of all interface monitors
    .CAP_HS         (1'b1),
    .CAP_FL_TXN     (1'b1),
    .CAP_FL_DAT     (1'b0),
    .CAP_TX_DAT     (1'b0),
    .CAP_STALL      (1'b1),
    .CAP_RT         (1'b0),
    .CAP_EXCL       (1'b1),
    .CAP_ATOP       (1'b1),
    // Counter widths for all interface monitors
    .CW_CLK         (56),
    .CW_HS_CMD      (32),
    .CW_HS_DAT      (32),
    .CW_FL_TXN_ACC  (63),
    .CW_FL_TXN_MAX  (10),
    .CW_STALL_CMD   (56),
    .CW_STALL_DAT   (56),
    .CW_STALL_MAX   (16),
    .CW_EXCL        (10),
    .CW_ATOP        (14)
  ) i_perf_mon ();

endmodule


module synth_slice #(
  parameter int AW = -1,
  parameter int DW = -1,
  parameter int IW = -1,
  parameter int UW = -1
)(
  input logic clk_i,
  input logic rst_ni
);

  AXI_BUS #(
    .AXI_ADDR_WIDTH(AW),
    .AXI_DATA_WIDTH(DW),
    .AXI_ID_WIDTH(IW),
    .AXI_USER_WIDTH(UW)
  ) a_full(), b_full();

  AXI_LITE #(
    .AXI_ADDR_WIDTH(AW),
    .AXI_DATA_WIDTH(DW)
  ) a_lite(), b_lite();

  axi_to_axi_lite a (
    .clk_i      (clk_i),
    .rst_ni     (rst_ni),
    .testmode_i (1'b0),
    .in         (a_full.in),
    .out        (a_lite.out)
  );
  axi_lite_to_axi b (
    .in   (b_lite.in),
    .out  (b_full.out)
  );

endmodule


module axi_lite_xbar_slice #(
  parameter int NUM_MASTER = -1,
  parameter int NUM_SLAVE = -1
)(
  input logic clk_i,
  input logic rst_ni
);

  AXI_LITE #(
    .AXI_ADDR_WIDTH(32),
    .AXI_DATA_WIDTH(32)
  ) xbar_master [0:NUM_MASTER-1]();

  AXI_LITE #(
    .AXI_ADDR_WIDTH(32),
    .AXI_DATA_WIDTH(32)
  ) xbar_slave [0:NUM_SLAVE-1]();

  AXI_ROUTING_RULES #(
    .AXI_ADDR_WIDTH(32),
    .NUM_SLAVE(NUM_SLAVE),
    .NUM_RULES(1)
  ) xbar_routing();

  for (genvar i = 0; i < NUM_SLAVE; i++) begin
    assign xbar_routing.rules[i] = {{ 32'hfffff000, 32'h00010000 * i }};
  end

  axi_lite_xbar #(
    .ADDR_WIDTH(32),
    .DATA_WIDTH(32),
    .NUM_MASTER(NUM_MASTER),
    .NUM_SLAVE(NUM_SLAVE),
    .NUM_RULES(1)
  ) xbar (
    .clk_i  ( clk_i              ),
    .rst_ni ( rst_ni             ),
    .master ( xbar_master.in     ),
    .slave  ( xbar_slave.out     ),
    .rules  ( xbar_routing.xbar  )
  );

endmodule


module synth_axi_atop_filter #(
  parameter int unsigned AXI_ADDR_WIDTH = 0,
  parameter int unsigned AXI_DATA_WIDTH = 0,
  parameter int unsigned AXI_ID_WIDTH = 0,
  parameter int unsigned AXI_USER_WIDTH = 0,
  parameter int unsigned AXI_MAX_WRITE_TXNS = 0
) (
  input logic clk_i,
  input logic rst_ni
);

  AXI_BUS #(
    .AXI_ADDR_WIDTH (AXI_ADDR_WIDTH),
    .AXI_DATA_WIDTH (AXI_DATA_WIDTH),
    .AXI_ID_WIDTH   (AXI_ID_WIDTH),
    .AXI_USER_WIDTH (AXI_USER_WIDTH)
  ) upstream ();

  AXI_BUS #(
    .AXI_ADDR_WIDTH (AXI_ADDR_WIDTH),
    .AXI_DATA_WIDTH (AXI_DATA_WIDTH),
    .AXI_ID_WIDTH   (AXI_ID_WIDTH),
    .AXI_USER_WIDTH (AXI_USER_WIDTH)
  ) downstream ();

  axi_atop_filter #(
    .AXI_ID_WIDTH       (AXI_ID_WIDTH),
    .AXI_MAX_WRITE_TXNS (AXI_MAX_WRITE_TXNS)
  ) dut (
    .clk_i  (clk_i),
    .rst_ni (rst_ni),
    .slv    (upstream),
    .mst    (downstream)
  );

endmodule

module synth_axi_perf_mon #(
  // Number of monitored AXI interfaces
  parameter int unsigned  N_MON         = 0,
  // AXI parameters
  parameter int unsigned  AW            = 0,
  parameter int unsigned  IW            = 0,
  // Capabilities of all interface monitors
  parameter bit           CAP_HS        = 1'b0,
  parameter bit           CAP_FL_TXN    = 1'b0,
  parameter bit           CAP_FL_DAT    = 1'b0,
  parameter bit           CAP_TX_DAT    = 1'b0,
  parameter bit           CAP_STALL     = 1'b0,
  parameter bit           CAP_RT        = 1'b0,
  parameter bit           CAP_EXCL      = 1'b0,
  parameter bit           CAP_ATOP      = 1'b0,
  // Counter widths for all interface monitors
  parameter int unsigned  CW_CLK        = 0,
  parameter int unsigned  CW_HS_CMD     = 0,
  parameter int unsigned  CW_HS_DAT     = 0,
  parameter int unsigned  CW_FL_TXN_ACC = 0,
  parameter int unsigned  CW_FL_TXN_MAX = 0,
  parameter int unsigned  CW_FL_DAT_ACC = 0,
  parameter int unsigned  CW_FL_DAT_MAX = 0,
  parameter int unsigned  CW_TX_DAT     = 0,
  parameter int unsigned  CW_STALL_CMD  = 0,
  parameter int unsigned  CW_STALL_DAT  = 0,
  parameter int unsigned  CW_STALL_MAX  = 0,
  parameter int unsigned  CW_RT_ACC     = 0,
  parameter int unsigned  CW_RT_MAX     = 0,
  parameter int unsigned  CW_EXCL       = 0,
  parameter int unsigned  CW_ATOP       = 0,
  // Dependent parameters, do not override.
  parameter type id_t = logic [IW-1:0]
);
  // APB Readout and Control Interface
  logic        pclk_i;
  logic        preset_ni;
  logic [31:0] paddr_i;
  logic  [2:0] pprot_i;
  logic        psel_i;
  logic        penable_i;
  logic        pwrite_i;
  logic [31:0] pwdata_i;
  logic  [3:0] pstrb_i;
  logic        pready_o;
  logic [31:0] prdata_o;
  logic        pslverr_o;

  // Monitored AXI Interfaces
  logic  [N_MON-1:0] clk_axi_i;
  logic  [N_MON-1:0] rst_axi_ni;
  id_t   [N_MON-1:0] ar_id_i;
  len_t  [N_MON-1:0] ar_len_i;
  size_t [N_MON-1:0] ar_size_i;
  logic  [N_MON-1:0] ar_lock_i;
  logic  [N_MON-1:0] ar_valid_i;
  logic  [N_MON-1:0] ar_ready_i;
  id_t   [N_MON-1:0] aw_id_i;
  len_t  [N_MON-1:0] aw_len_i;
  size_t [N_MON-1:0] aw_size_i;
  logic  [N_MON-1:0] aw_lock_i;
  atop_t [N_MON-1:0] aw_atop_i;
  logic  [N_MON-1:0] aw_valid_i;
  logic  [N_MON-1:0] aw_ready_i;
  id_t   [N_MON-1:0] r_id_i;
  logic  [N_MON-1:0] r_last_i;
  logic  [N_MON-1:0] r_valid_i;
  logic  [N_MON-1:0] r_ready_i;
  logic  [N_MON-1:0] w_last_i;
  logic  [N_MON-1:0] w_valid_i;
  logic  [N_MON-1:0] w_ready_i;
  id_t   [N_MON-1:0] b_id_i;
  resp_t [N_MON-1:0] b_resp_i;
  logic  [N_MON-1:0] b_valid_i;
  logic  [N_MON-1:0] b_ready_i;

  axi_perf_mon #(
    .N_MON          (N_MON),
    .IW             (IW),
    .CAP_HS         (CAP_HS),
    .CAP_FL_TXN     (CAP_FL_TXN),
    .CAP_FL_DAT     (CAP_FL_DAT),
    .CAP_TX_DAT     (CAP_TX_DAT),
    .CAP_STALL      (CAP_STALL),
    .CAP_RT         (CAP_RT),
    .CAP_EXCL       (CAP_EXCL),
    .CAP_ATOP       (CAP_ATOP),
    .CW_CLK         (CW_CLK),
    .CW_HS_CMD      (CW_HS_CMD),
    .CW_HS_DAT      (CW_HS_DAT),
    .CW_FL_TXN_ACC  (CW_FL_TXN_ACC),
    .CW_FL_TXN_MAX  (CW_FL_TXN_MAX),
    .CW_FL_DAT_ACC  (CW_FL_DAT_ACC),
    .CW_FL_DAT_MAX  (CW_FL_DAT_MAX),
    .CW_TX_DAT      (CW_TX_DAT),
    .CW_STALL_CMD   (CW_STALL_CMD),
    .CW_STALL_DAT   (CW_STALL_DAT),
    .CW_STALL_MAX   (CW_STALL_MAX),
    .CW_RT_ACC      (CW_RT_ACC),
    .CW_RT_MAX      (CW_RT_MAX),
    .CW_EXCL        (CW_EXCL),
    .CW_ATOP        (CW_ATOP)
  ) dut (
    .pclk_i,
    .preset_ni,
    .paddr_i,
    .pprot_i,
    .psel_i,
    .penable_i,
    .pwrite_i,
    .pwdata_i,
    .pstrb_i,
    .pready_o,
    .prdata_o,
    .pslverr_o,
    .clk_axi_i,
    .rst_axi_ni,
    .ar_id_i,
    .ar_len_i,
    .ar_size_i,
    .ar_lock_i,
    .ar_valid_i,
    .ar_ready_i,
    .aw_id_i,
    .aw_len_i,
    .aw_size_i,
    .aw_lock_i,
    .aw_atop_i,
    .aw_valid_i,
    .aw_ready_i,
    .r_id_i,
    .r_last_i,
    .r_valid_i,
    .r_ready_i,
    .w_last_i,
    .w_valid_i,
    .w_ready_i,
    .b_id_i,
    .b_resp_i,
    .b_valid_i,
    .b_ready_i
  );

endmodule
