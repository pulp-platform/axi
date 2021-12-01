// Copyright 2018-2020 ETH Zurich and University of Bologna.
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
//         Andreas Kurth <akurth@iis.ee.ethz.ch>

`include "axi/assign.svh"

module tb_axi_iw_converter #(
  // DUT Parameters
  parameter int unsigned TbAxiSlvPortIdWidth = 32'd0,
  parameter int unsigned TbAxiMstPortIdWidth = 32'd0,
  parameter int unsigned TbAxiSlvPortMaxUniqIds = 32'd0,
  parameter int unsigned TbAxiSlvPortMaxTxnsPerId = 32'd0,
  parameter int unsigned TbAxiSlvPortMaxTxns = 32'd0,
  parameter int unsigned TbAxiMstPortMaxUniqIds = 32'd0,
  parameter int unsigned TbAxiMstPortMaxTxnsPerId = 32'd0,
  parameter int unsigned TbAxiAddrWidth = 32'd32,
  parameter int unsigned TbAxiDataWidth = 32'd32,
  parameter int unsigned TbAxiUserWidth = 32'd4,
  // TB Parameters
  parameter int unsigned TbNumReadTxns = 32'd100,
  parameter int unsigned TbNumWriteTxns = 32'd200,
  parameter bit          TbEnAtop = 1'b1,
  parameter bit          TbEnExcl = 1'b0
);
  // AXI4+ATOP channel parameter

  // TB timing parameter
  localparam time CyclTime = 10ns;
  localparam time ApplTime = 2ns;
  localparam time TestTime = 8ns;

  // Driver definitions
  typedef axi_test::axi_rand_master #(
    // AXI interface parameters
    .AW ( TbAxiAddrWidth       ),
    .DW ( TbAxiDataWidth       ),
    .IW ( TbAxiSlvPortIdWidth  ),
    .UW ( TbAxiUserWidth       ),
    // Stimuli application and test time
    .TA ( ApplTime           ),
    .TT ( TestTime           ),
    // Maximum number of read and write transactions in flight
    .MAX_READ_TXNS  ( 20     ),
    .MAX_WRITE_TXNS ( 20     ),
    .AXI_EXCLS      ( TbEnExcl ),
    .AXI_ATOPS      ( TbEnAtop )
  ) rand_axi_master_t;
  typedef axi_test::axi_rand_slave #(
    // AXI interface parameters
    .AW ( TbAxiAddrWidth      ),
    .DW ( TbAxiDataWidth      ),
    .IW ( TbAxiMstPortIdWidth ),
    .UW ( TbAxiUserWidth      ),
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
    .ClkPeriod    ( CyclTime ),
    .RstClkCycles ( 5        )
  ) i_clk_gen (
    .clk_o  ( clk   ),
    .rst_no ( rst_n )
  );

  AXI_BUS_DV #(
    .AXI_ADDR_WIDTH ( TbAxiAddrWidth       ),
    .AXI_DATA_WIDTH ( TbAxiDataWidth       ),
    .AXI_ID_WIDTH   ( TbAxiSlvPortIdWidth  ),
    .AXI_USER_WIDTH ( TbAxiUserWidth       )
  ) axi_upstream_dv (clk);

  AXI_BUS #(
    .AXI_ADDR_WIDTH ( TbAxiAddrWidth       ),
    .AXI_DATA_WIDTH ( TbAxiDataWidth       ),
    .AXI_ID_WIDTH   ( TbAxiSlvPortIdWidth  ),
    .AXI_USER_WIDTH ( TbAxiUserWidth       )
  ) axi_upstream();

  `AXI_ASSIGN(axi_upstream, axi_upstream_dv);

  AXI_BUS_DV #(
    .AXI_ADDR_WIDTH ( TbAxiAddrWidth      ),
    .AXI_DATA_WIDTH ( TbAxiDataWidth      ),
    .AXI_ID_WIDTH   ( TbAxiMstPortIdWidth ),
    .AXI_USER_WIDTH ( TbAxiUserWidth      )
  ) axi_downstream_dv (clk);

  AXI_BUS #(
    .AXI_ADDR_WIDTH ( TbAxiAddrWidth      ),
    .AXI_DATA_WIDTH ( TbAxiDataWidth      ),
    .AXI_ID_WIDTH   ( TbAxiMstPortIdWidth ),
    .AXI_USER_WIDTH ( TbAxiUserWidth      )
  ) axi_downstream();

  `AXI_ASSIGN(axi_downstream_dv, axi_downstream);

  initial begin : proc_rand_master
    automatic rand_axi_master_t axi_master = new(axi_upstream_dv);
    sim_done = 1'b0;
    @(posedge rst_n);
    axi_master.reset();
    axi_master.add_memory_region('0, '1, axi_pkg::DEVICE_NONBUFFERABLE);
    repeat (5) @(posedge clk);
    axi_master.run(TbNumReadTxns, TbNumWriteTxns);

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
    $finish();
  end

  axi_iw_converter_intf #(
    .AXI_SLV_PORT_ID_WIDTH        ( TbAxiSlvPortIdWidth       ),
    .AXI_MST_PORT_ID_WIDTH        ( TbAxiMstPortIdWidth       ),
    .AXI_SLV_PORT_MAX_UNIQ_IDS    ( TbAxiSlvPortMaxUniqIds    ),
    .AXI_SLV_PORT_MAX_TXNS_PER_ID ( TbAxiSlvPortMaxTxnsPerId  ),
    .AXI_SLV_PORT_MAX_TXNS        ( TbAxiSlvPortMaxTxns       ),
    .AXI_MST_PORT_MAX_UNIQ_IDS    ( TbAxiMstPortMaxUniqIds    ),
    .AXI_MST_PORT_MAX_TXNS_PER_ID ( TbAxiMstPortMaxTxnsPerId  ),
    .AXI_ADDR_WIDTH               ( TbAxiAddrWidth            ),
    .AXI_DATA_WIDTH               ( TbAxiDataWidth            ),
    .AXI_USER_WIDTH               ( TbAxiUserWidth            )
  ) i_dut (
    .clk_i  ( clk            ),
    .rst_ni ( rst_n          ),
    .slv    ( axi_upstream   ),
    .mst    ( axi_downstream )
  );

endmodule
