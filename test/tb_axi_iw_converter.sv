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
// Author: Florian Zaruba <zarubaf@iis.ee.ethz.ch>
//         Wolfgang Roennigner <wroennin@iis.ee.ethz.ch>

`include "axi/assign.svh"

module tb_axi_iw_converter #(
  /// AXI4+ATOP ID width upstream, connected to the slave port of the DUT
  parameter int unsigned AxiIdWidthUpstream   = 32'd6,
  /// AXI4+ATOP ID width downstream, connected to the master port of the DUT
  parameter int unsigned AxiIdWidthDownstream = 32'd4,
  /// Size of the remap table
  parameter int unsigned RemapTableSize       = 32'd8,
  /// Number of Read Transactions
  parameter int unsigned NumReadTxns          = 32'd1000,
  /// Number of Write Transactions
  parameter int unsigned NumWriteTxns         = 32'd2000,
  /// Enable Atomics
  parameter bit          EnAtop               = 1'b1
);
  // AXI4+ATOP channel parameter
  parameter int unsigned AxiAddrWidth = 32'd32;
  parameter int unsigned AxiDataWidth = 32'd32;
  parameter int unsigned AxiUserWidth = 32'd4;

  // TB timing parameter
  localparam time CyclTime = 10ns;
  localparam time ApplTime = 2ns;
  localparam time TestTime = 8ns;

  // Driver definitions
  typedef axi_test::rand_axi_master #(
    // AXI interface parameters
    .AW ( AxiAddrWidth       ),
    .DW ( AxiDataWidth       ),
    .IW ( AxiIdWidthUpstream ),
    .UW ( AxiUserWidth       ),
    // Stimuli application and test time
    .TA ( ApplTime           ),
    .TT ( TestTime           ),
    // Maximum number of read and write transactions in flight
    .MAX_READ_TXNS  ( 20     ),
    .MAX_WRITE_TXNS ( 20     ),
    .AXI_ATOPS      ( EnAtop )
  ) rand_axi_master_t;
  typedef axi_test::rand_axi_slave #(
    // AXI interface parameters
    .AW ( AxiAddrWidth         ),
    .DW ( AxiDataWidth         ),
    .IW ( AxiIdWidthDownstream ),
    .UW ( AxiUserWidth         ),
    // Stimuli application and test time
    .TA ( ApplTime         ),
    .TT ( TestTime         )
  ) rand_axi_slave_t;

  // TB signals
  logic clk, rst_n, sim_done;

  //-----------------------------------
  // Clock generator
  //-----------------------------------
  clk_rst_gen #(
    .CLK_PERIOD     ( CyclTime ),
    .RST_CLK_CYCLES ( 5        )
  ) i_clk_gen (
    .clk_o  ( clk   ),
    .rst_no ( rst_n )
  );

  AXI_BUS_DV #(
    .AXI_ADDR_WIDTH ( AxiAddrWidth       ),
    .AXI_DATA_WIDTH ( AxiDataWidth       ),
    .AXI_ID_WIDTH   ( AxiIdWidthUpstream ),
    .AXI_USER_WIDTH ( AxiUserWidth       )
  ) axi_upstream_dv (clk);

  AXI_BUS #(
    .AXI_ADDR_WIDTH ( AxiAddrWidth       ),
    .AXI_DATA_WIDTH ( AxiDataWidth       ),
    .AXI_ID_WIDTH   ( AxiIdWidthUpstream ),
    .AXI_USER_WIDTH ( AxiUserWidth       )
  ) axi_upstream();

  `AXI_ASSIGN(axi_upstream, axi_upstream_dv);

  AXI_BUS_DV #(
    .AXI_ADDR_WIDTH (  AxiAddrWidth         ),
    .AXI_DATA_WIDTH (  AxiDataWidth         ),
    .AXI_ID_WIDTH   (  AxiIdWidthDownstream ),
    .AXI_USER_WIDTH (  AxiUserWidth         )
  ) axi_downstream_dv (clk);

  AXI_BUS #(
    .AXI_ADDR_WIDTH ( AxiAddrWidth         ),
    .AXI_DATA_WIDTH ( AxiDataWidth         ),
    .AXI_ID_WIDTH   ( AxiIdWidthDownstream ),
    .AXI_USER_WIDTH ( AxiUserWidth         )
  ) axi_downstream();

  `AXI_ASSIGN(axi_downstream_dv, axi_downstream);

  initial begin : proc_rand_master
    automatic rand_axi_master_t axi_master = new(axi_upstream_dv);
    sim_done = 1'b0;
    @(posedge rst_n);
    axi_master.reset();
    axi_master.add_memory_region('0, '1, axi_pkg::DEVICE_NONBUFFERABLE);
    repeat (5) @(posedge clk);
    axi_master.run(NumReadTxns, NumWriteTxns);

    sim_done = 1'b1;
  end

  initial begin : proc_rand_slave
    automatic rand_axi_slave_t axi_slave = new(axi_downstream_dv);
    @(posedge rst_n);
    axi_slave.reset();
    axi_slave.run();
  end

  initial begin : proc_sim_stop
    @(posedge rst_n);
    wait(|sim_done);
    repeat (10) @(posedge clk);
    $info("Simulation stopped.");
    $stop();
  end


  axi_iw_converter_intf #(
    .REMAP_TABLE_SIZE ( RemapTableSize       ),
    .AXI_ID_WIDTH_SLV ( AxiIdWidthUpstream   ),
    .AXI_ID_WIDTH_MST ( AxiIdWidthDownstream ),
    .AXI_ADDR_WIDTH   ( AxiAddrWidth         ),
    .AXI_DATA_WIDTH   ( AxiDataWidth         ),
    .AXI_USER_WIDTH   ( AxiUserWidth         )
  ) i_axi_iw_converter_dut (
    .clk_i  ( clk            ),
    .rst_ni ( rst_n          ),
    .slv    ( axi_upstream   ),
    .mst    ( axi_downstream )
  );
// vsim -voptargs=+acc work.tb_axi_id_remap
endmodule
