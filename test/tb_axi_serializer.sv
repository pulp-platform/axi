// Copyright (c) 2019 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Author: Wolfgang Roenninger <wroennin@ethz.ch>

`include "axi/typedef.svh"
`include "axi/assign.svh"

module tb_axi_serializer #(
    parameter int unsigned NoWrites = 5000,  // How many writes per master
    parameter int unsigned NoReads  = 3000   // How many reads per master
  );
  // Random master no Transactions
  localparam int unsigned NoPendingDut = 4;
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
  localparam int unsigned PrintTnx = 500;


  typedef axi_test::rand_axi_master #(
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
  ) rand_axi_master_t;
  typedef axi_test::rand_axi_slave #(
    // AXI interface parameters
    .AW ( AxiAddrWidth ),
    .DW ( AxiDataWidth ),
    .IW ( AxiIdWidth   ),
    .UW ( AxiUserWidth ),
    // Stimuli application and test time
    .TA ( ApplTime ),
    .TT ( TestTime )
  ) rand_axi_slave_t;

  // -------------
  // DUT signals
  // -------------
  logic clk;
  logic rst_n;
  logic end_of_sim;

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
    .CLK_PERIOD    ( CyclTime ),
    .RST_CLK_CYCLES( 5        )
  ) i_clk_gen (
    .clk_o (clk),
    .rst_no(rst_n)
  );

  //-----------------------------------
  // DUT
  //-----------------------------------
  axi_serializer_intf #(
    .MAX_READ_TXNS  ( NoPendingDut ),
    .MAX_WRITE_TXNS ( NoPendingDut ),
    .AXI_ID_WIDTH   ( AxiIdWidth   ), // AXI ID width
    .AXI_ADDR_WIDTH ( AxiAddrWidth ), // AXI address width
    .AXI_DATA_WIDTH ( AxiDataWidth ), // AXI data width
    .AXI_USER_WIDTH ( AxiUserWidth )  // AXI user width
  ) i_dut (
    .clk_i      ( clk      ), // clock
    .rst_ni     ( rst_n    ), // asynchronous reset active low
    .slv        ( master   ), // slave port
    .mst        ( slave    )  // master port
  );

  initial begin : proc_axi_master
    automatic rand_axi_master_t rand_axi_master = new(master_dv);
    end_of_sim <= 1'b0;
    rand_axi_master.add_memory_region(32'h0000_0000, 32'h1000_0000, axi_pkg::DEVICE_NONBUFFERABLE);
    rand_axi_master.add_memory_region(32'h2000_0000, 32'h3000_0000, axi_pkg::WTHRU_NOALLOCATE);
    rand_axi_master.add_memory_region(32'h4000_0000, 32'h5000_0000, axi_pkg::WBACK_RWALLOCATE);
    rand_axi_master.reset();
    @(posedge rst_n);
    rand_axi_master.run(NoReads, NoWrites);
    end_of_sim <= 1'b1;
    repeat (100) @(posedge clk);
    $stop();
  end

  initial begin : proc_axi_slave
    automatic rand_axi_slave_t  rand_axi_slave  = new(slave_dv);
    rand_axi_slave.reset();
    @(posedge rst_n);
    rand_axi_slave.run();
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
endmodule
