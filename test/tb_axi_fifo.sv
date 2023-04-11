// Copyright (c) 2019 ETH Zurich and University of Bologna.
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
// - Noah Huetter <huettern@ethz.ch>

`include "axi/typedef.svh"
`include "axi/assign.svh"

module tb_axi_fifo #(
    parameter int unsigned Depth = 16,
    parameter int unsigned FallThrough = 0,
    parameter int unsigned NumWrites = 200,  // How many writes per manager
    parameter int unsigned NumReads = 200  // How many reads per manager
);
  // Random Manager Atomics
  localparam int unsigned MaxAW = 30;
  localparam int unsigned MaxAR = 30;
  localparam bit EnAtop = 1'b1;
  // timing parameters
  localparam time CyclTime = 10ns;
  localparam time ApplTime = 2ns;
  localparam time TestTime = 8ns;
  // AXI configuration
  localparam int unsigned IdWidth = 4;
  localparam int unsigned AddrWidth = 32;  // Address Width
  localparam int unsigned DataWidth = 64;  // Data Width
  localparam int unsigned UserWidth = 5;
  // Sim print config, how many transactions
  localparam int unsigned PrintTnx = 100;

  typedef axi_test::axi_rand_manager#(
      // AXI interface parameters
      .AW            (AddrWidth),
      .DW            (DataWidth),
      .IW            (IdWidth),
      .UW            (UserWidth),
      // Stimuli application and test time
      .TA            (ApplTime),
      .TT            (TestTime),
      // Maximum number of read and write transactions in flight
      .MAX_READ_TXNS (MaxAR),
      .MAX_WRITE_TXNS(MaxAW),
      .AXI_ATOPS     (EnAtop)
  ) axi_rand_manager_t;
  typedef axi_test::axi_rand_subordinate#(
      // AXI interface parameters
      .AW(AddrWidth),
      .DW(DataWidth),
      .IW(IdWidth),
      .UW(UserWidth),
      // Stimuli application and test time
      .TA(ApplTime),
      .TT(TestTime)
  ) axi_rand_subordinate_t;

  // -------------
  // DUT signals
  // -------------
  logic clk;
  logic rst_n;
  logic end_of_sim;

  // interfaces
  AXI_BUS #(
      .AXI_ADDR_WIDTH(AddrWidth),
      .AXI_DATA_WIDTH(DataWidth),
      .AXI_ID_WIDTH  (IdWidth),
      .AXI_USER_WIDTH(UserWidth)
  )
      manager (), subordinate ();
  AXI_BUS_DV #(
      .AXI_ADDR_WIDTH(AddrWidth),
      .AXI_DATA_WIDTH(DataWidth),
      .AXI_ID_WIDTH  (IdWidth),
      .AXI_USER_WIDTH(UserWidth)
  )
      manager_dv (clk), subordinate_dv (clk);

  `AXI_ASSIGN(manager, manager_dv)
  `AXI_ASSIGN(subordinate_dv, subordinate)

  //-----------------------------------
  // Clock generator
  //-----------------------------------
  clk_rst_gen #(
      .ClkPeriod   (CyclTime),
      .RstClkCycles(5)
  ) i_clk_gen (
      .clk_o (clk),
      .rst_no(rst_n)
  );

  //-----------------------------------
  // DUT
  //-----------------------------------
  axi_fifo_intf #(
      .DEPTH       (Depth),  // number of FiFo slots
      .FALL_THROUGH(FallThrough),  // FiFos in fall through mode
      .ID_WIDTH    (IdWidth),  // AXI ID width
      .ADDR_WIDTH  (AddrWidth),  // AXI address width
      .DATA_WIDTH  (DataWidth),  // AXI data width
      .USER_WIDTH  (UserWidth)  // AXI user width
  ) i_dut (
      .clk_i (clk),  // clock
      .rst_ni(rst_n),  // asynchronous reset active low
      .test_i(1'b0),
      .sbr   (manager),  // subordinate port
      .mgr   (subordinate)  // manager port
  );

  initial begin : proc_axi_manager
    automatic axi_rand_manager_t axi_rand_manager = new(manager_dv);
    end_of_sim <= 1'b0;
    axi_rand_manager.add_memory_region(32'h0000_0000, 32'h1000_0000, axi_pkg::DEVICE_NONBUFFERABLE);
    axi_rand_manager.add_memory_region(32'h2000_0000, 32'h3000_0000, axi_pkg::WTHRU_NOALLOCATE);
    axi_rand_manager.add_memory_region(32'h4000_0000, 32'h5000_0000, axi_pkg::WBACK_RWALLOCATE);
    axi_rand_manager.reset();
    @(posedge rst_n);
    axi_rand_manager.run(NumReads, NumWrites);
    end_of_sim <= 1'b1;
    repeat (10000) @(posedge clk);
    $stop();
  end

  initial begin : proc_axi_subordinate
    automatic axi_rand_subordinate_t axi_rand_subordinate = new(subordinate_dv);
    axi_rand_subordinate.reset();
    @(posedge rst_n);
    axi_rand_subordinate.run();
  end

  initial begin : proc_sim_progress
    automatic int unsigned aw = 0;
    automatic int unsigned ar = 0;
    automatic bit          aw_printed = 1'b0;
    automatic bit          ar_printed = 1'b0;

    @(posedge rst_n);

    forever begin
      @(posedge clk);
      #TestTime;
      if (manager.aw_valid && manager.aw_ready) begin
        aw++;
      end
      if (manager.ar_valid && manager.ar_ready) begin
        ar++;
      end

      if ((aw % PrintTnx == 0) && !aw_printed) begin
        $display("%t> Transmit AW %d of %d.", $time(), aw, NumWrites);
        aw_printed = 1'b1;
      end
      if ((ar % PrintTnx == 0) && !ar_printed) begin
        $display("%t> Transmit AR %d of %d.", $time(), ar, NumReads);
        ar_printed = 1'b1;
      end

      if (aw % PrintTnx == 1) begin
        aw_printed = 1'b0;
      end
      if (ar % PrintTnx == 1) begin
        ar_printed = 1'b0;
      end

      if (end_of_sim) begin
        $info("All transactions completed.");
        break;
      end
    end
  end


  default disable iff (!rst_n); aw_unstable :
  assert property (@(posedge clk) (subordinate.aw_valid && !subordinate.aw_ready) |=> $stable(subordinate.aw_addr))
  else $fatal(1, "AW is unstable.");
  w_unstable :
  assert property (@(posedge clk) (subordinate.w_valid && !subordinate.w_ready) |=> $stable(subordinate.w_data))
  else $fatal(1, "W is unstable.");
  b_unstable :
  assert property (@(posedge clk) (manager.b_valid && !manager.b_ready) |=> $stable(manager.b_resp))
  else $fatal(1, "B is unstable.");
  ar_unstable :
  assert property (@(posedge clk) (subordinate.ar_valid && !subordinate.ar_ready) |=> $stable(subordinate.ar_addr))
  else $fatal(1, "AR is unstable.");
  r_unstable :
  assert property (@(posedge clk) (manager.r_valid && !manager.r_ready) |=> $stable(manager.r_data))
  else $fatal(1, "R is unstable.");


endmodule
