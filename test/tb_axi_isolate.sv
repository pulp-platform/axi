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
// - Wolfgang Roenninger <wroennin@iis.ee.ethz.ch>
// - Andreas Kurth <akurth@iis.ee.ethz.ch>

`include "axi/typedef.svh"
`include "axi/assign.svh"

module tb_axi_isolate #(
    parameter int unsigned NoWrites = 50000,  // How many writes per master
    parameter int unsigned NoReads  = 30000   // How many reads per master
  );
  // Random master no Transactions
  localparam int unsigned NoPendingDut = 16;
  // Random Master Atomics
  localparam int unsigned MaxAW      = 32'd30;
  localparam int unsigned MaxAR      = 32'd30;
  localparam bit          EnAtop     = 1'b1;
  // timing parameters
  localparam time CyclTime = 10ns;
  localparam time ApplTime =  2ns;
  localparam time TestTime =  8ns;
  // AXI configuration
  localparam int unsigned AxiIdWidth   =  4;
  localparam int unsigned AxiAddrWidth =  32;    // Axi Address Width
  localparam int unsigned AxiDataWidth =  64;    // Axi Data Width
  localparam int unsigned AxiUserWidth =  5;
  // Sim print config, how many transactions
  localparam int unsigned PrintTnx = 1000;


  typedef axi_test::axi_rand_master #(
    // AXI interface parameters
    .AW ( AxiAddrWidth ),
    .DW ( AxiDataWidth ),
    .IW ( AxiIdWidth   ),
    .UW ( AxiUserWidth ),
    // Stimuli application and test time
    .TA ( ApplTime ),
    .TT ( TestTime ),
    // Maximum number of read and write transactions in flight
    .MAX_READ_TXNS  ( MaxAR  ),
    .MAX_WRITE_TXNS ( MaxAW  ),
    .AXI_ATOPS      ( EnAtop )
  ) axi_rand_master_t;
  typedef axi_test::axi_rand_slave #(
    // AXI interface parameters
    .AW ( AxiAddrWidth ),
    .DW ( AxiDataWidth ),
    .IW ( AxiIdWidth   ),
    .UW ( AxiUserWidth ),
    // Stimuli application and test time
    .TA ( ApplTime ),
    .TT ( TestTime )
  ) axi_rand_slave_t;

  // -------------
  // DUT signals
  // -------------
  logic clk;
  logic rst_n;
  logic end_of_sim;
  // DUT signals
  logic isolate, isolated;

  // interfaces
  AXI_BUS #(
    .AXI_ADDR_WIDTH ( AxiAddrWidth ),
    .AXI_DATA_WIDTH ( AxiDataWidth ),
    .AXI_ID_WIDTH   ( AxiIdWidth   ),
    .AXI_USER_WIDTH ( AxiUserWidth )
  ) master ();
  AXI_BUS_DV #(
    .AXI_ADDR_WIDTH ( AxiAddrWidth ),
    .AXI_DATA_WIDTH ( AxiDataWidth ),
    .AXI_ID_WIDTH   ( AxiIdWidth   ),
    .AXI_USER_WIDTH ( AxiUserWidth )
  ) master_dv (clk);
  AXI_BUS #(
    .AXI_ADDR_WIDTH ( AxiAddrWidth ),
    .AXI_DATA_WIDTH ( AxiDataWidth ),
    .AXI_ID_WIDTH   ( AxiIdWidth   ),
    .AXI_USER_WIDTH ( AxiUserWidth )
  ) slave ();
  AXI_BUS_DV #(
    .AXI_ADDR_WIDTH ( AxiAddrWidth ),
    .AXI_DATA_WIDTH ( AxiDataWidth ),
    .AXI_ID_WIDTH   ( AxiIdWidth   ),
    .AXI_USER_WIDTH ( AxiUserWidth )
  ) slave_dv (clk);

  `AXI_ASSIGN           ( master,  master_dv )
  `AXI_ASSIGN           ( slave_dv, slave    )

  //-----------------------------------
  // Clock generator
  //-----------------------------------
  clk_rst_gen #(
    .ClkPeriod    ( CyclTime ),
    .RstClkCycles ( 5        )
  ) i_clk_gen (
    .clk_o (clk),
    .rst_no(rst_n)
  );

  //-----------------------------------
  // DUT
  //-----------------------------------
  axi_isolate_intf #(
    .NUM_PENDING    ( NoPendingDut ), // number of pending requests
    .AXI_ID_WIDTH   ( AxiIdWidth   ), // AXI ID width
    .AXI_ADDR_WIDTH ( AxiAddrWidth ), // AXI address width
    .AXI_DATA_WIDTH ( AxiDataWidth ), // AXI data width
    .AXI_USER_WIDTH ( AxiUserWidth )  // AXI user width
  ) i_dut (
    .clk_i      ( clk      ), // clock
    .rst_ni     ( rst_n    ), // asynchronous reset active low
    .slv        ( master   ), // slave port
    .mst        ( slave    ), // master port
    .isolate_i  ( isolate  ), // isolate master port from slave port
    .isolated_o ( isolated )  // master port is isolated from slave port
  );

  initial begin : proc_axi_master
    automatic axi_rand_master_t axi_rand_master = new(master_dv);
    end_of_sim <= 1'b0;
    axi_rand_master.add_memory_region(32'h0000_0000, 32'h1000_0000, axi_pkg::DEVICE_NONBUFFERABLE);
    axi_rand_master.add_memory_region(32'h2000_0000, 32'h3000_0000, axi_pkg::WTHRU_NOALLOCATE);
    axi_rand_master.add_memory_region(32'h4000_0000, 32'h5000_0000, axi_pkg::WBACK_RWALLOCATE);
    axi_rand_master.reset();
    @(posedge rst_n);
    axi_rand_master.run(NoReads, NoWrites);
    end_of_sim <= 1'b1;
    repeat (10000) @(posedge clk);
    $stop();
  end

  initial begin : proc_axi_slave
    automatic axi_rand_slave_t  axi_rand_slave  = new(slave_dv);
    axi_rand_slave.reset();
    @(posedge rst_n);
    axi_rand_slave.run();
  end

  initial begin : proc_sim_ctl
    forever begin
      isolate <= 1'b0;
      repeat ($urandom_range(100000,1)) @(posedge clk);
      isolate <= 1'b1;
      repeat ($urandom_range(100000,1)) @(posedge clk);
    end
  end

  initial begin : proc_sim_progress
    automatic int unsigned aw         = 0;
    automatic int unsigned ar         = 0;
    automatic bit          aw_printed = 1'b0;
    automatic bit          ar_printed = 1'b0;

    @(posedge rst_n);

    forever begin
      @(posedge clk);
      #TestTime;
      if (master.aw_valid && master.aw_ready) begin
        aw++;
      end
      if (master.ar_valid && master.ar_ready) begin
        ar++;
      end

      if ((aw % PrintTnx == 0) && ! aw_printed) begin
        $display("%t> Transmit AW %d of %d.", $time(), aw, NoWrites);
        aw_printed = 1'b1;
      end
      if ((ar % PrintTnx == 0) && !ar_printed) begin
        $display("%t> Transmit AR %d of %d.", $time(), ar, NoReads);
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


  default disable iff (!rst_n);
  aw_unstable: assert property (@(posedge clk)
      (slave.aw_valid && !slave.aw_ready) |=> $stable(slave.aw_addr)) else
      $fatal(1, "AW is unstable.");
  w_unstable:  assert property (@(posedge clk)
      (slave.w_valid  && !slave.w_ready)  |=> $stable(slave.w_data)) else
      $fatal(1, "W is unstable.");
  b_unstable:  assert property (@(posedge clk)
      (master.b_valid && !master.b_ready) |=> $stable(master.b_resp)) else
      $fatal(1, "B is unstable.");
  ar_unstable: assert property (@(posedge clk)
      (slave.ar_valid && !slave.ar_ready) |=> $stable(slave.ar_addr)) else
      $fatal(1, "AR is unstable.");
  r_unstable:  assert property (@(posedge clk)
      (master.r_valid && !master.r_ready) |=> $stable(master.r_data)) else
      $fatal(1, "R is unstable.");


endmodule
