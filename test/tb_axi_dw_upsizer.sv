// Copyright 2020 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// File          : tb_axi_dw_upsize.sv
// Author        : Matheus Cavalcante <matheusd@iis.ee.ethz.ch>
// Created       : 09.02.2019

// Copyright (C) 2020 ETH Zurich, University of Bologna
// All rights reserved.

module tb_axi_dw_upsizer #(
    // AXI Parameters
    parameter int unsigned AxiAddrWidth        = 64  ,
    parameter int unsigned AxiIdWidth          = 4   ,
    parameter int unsigned AxiSlvPortDataWidth = 32  ,
    parameter int unsigned AxiMstPortDataWidth = 64  ,
    parameter int unsigned AxiUserWidth        = 8   ,
    // TB Parameters
    parameter time CyclTime                    = 10ns,
    parameter time ApplTime                    = 2ns ,
    parameter time TestTime                    = 8ns
  );

  /****************
   *  PARAMETERS  *
   ****************/

  `include "axi/assign.svh"
  `include "axi/typedef.svh"

  /*********************
   *  CLOCK GENERATOR  *
   *********************/

  logic clk;
  logic rst_n;
  logic eos;

  clk_rst_gen #(
    .CLK_PERIOD    (CyclTime),
    .RST_CLK_CYCLES(5       )
  ) i_clk_rst_gen (
    .clk_o (clk  ),
    .rst_no(rst_n)
  );

  /*********
   *  AXI  *
   *********/

  // Master port

  AXI_BUS_DV #(
    .AXI_ADDR_WIDTH(AxiAddrWidth       ),
    .AXI_DATA_WIDTH(AxiSlvPortDataWidth),
    .AXI_ID_WIDTH  (AxiIdWidth         ),
    .AXI_USER_WIDTH(AxiUserWidth       )
  ) master_dv (
    .clk_i(clk)
  );

  AXI_BUS #(
    .AXI_ADDR_WIDTH(AxiAddrWidth       ),
    .AXI_DATA_WIDTH(AxiSlvPortDataWidth),
    .AXI_ID_WIDTH  (AxiIdWidth         ),
    .AXI_USER_WIDTH(AxiUserWidth       )
  ) master ();

  `AXI_ASSIGN(master, master_dv)

  axi_test::rand_axi_master #(
    .AW       (AxiAddrWidth       ),
    .DW       (AxiSlvPortDataWidth),
    .IW       (AxiIdWidth         ),
    .UW       (AxiUserWidth       ),
    .TA       (ApplTime           ),
    .TT       (TestTime           ),
    .AXI_ATOPS(1'b1               )
  ) master_drv = new (master_dv);

  // Slave port

  AXI_BUS_DV #(
    .AXI_ADDR_WIDTH(AxiAddrWidth       ),
    .AXI_DATA_WIDTH(AxiMstPortDataWidth),
    .AXI_ID_WIDTH  (AxiIdWidth         ),
    .AXI_USER_WIDTH(AxiUserWidth       )
  ) slave_dv (
    .clk_i(clk)
  );

  AXI_BUS #(
    .AXI_ADDR_WIDTH(AxiAddrWidth       ),
    .AXI_DATA_WIDTH(AxiMstPortDataWidth),
    .AXI_ID_WIDTH  (AxiIdWidth         ),
    .AXI_USER_WIDTH(AxiUserWidth       )
  ) slave ();

  axi_test::rand_axi_slave #(
    .AW(AxiAddrWidth       ),
    .DW(AxiMstPortDataWidth),
    .IW(AxiIdWidth         ),
    .UW(AxiUserWidth       ),
    .TA(ApplTime           ),
    .TT(TestTime           )
  ) slave_drv = new (slave_dv);

  `AXI_ASSIGN(slave_dv, slave)

  /*********
   *  DUT  *
   *********/

  axi_dw_converter_intf #(
    .AXI_MAX_READS          (4                  ),
    .AXI_ADDR_WIDTH         (AxiAddrWidth       ),
    .AXI_ID_WIDTH           (AxiIdWidth         ),
    .AXI_SLV_PORT_DATA_WIDTH(AxiSlvPortDataWidth),
    .AXI_MST_PORT_DATA_WIDTH(AxiMstPortDataWidth),
    .AXI_USER_WIDTH         (AxiUserWidth       )
  ) i_dw_converter (
    .clk_i (clk   ),
    .rst_ni(rst_n ),
    .slv   (master),
    .mst   (slave )
  );

  /*************
   *  DRIVERS  *
   *************/

  initial begin
    eos = 1'b0;

    // Configuration
    slave_drv.reset()                                                                                  ;
    master_drv.reset()                                                                                 ;
    master_drv.add_memory_region({AxiAddrWidth{1'b0}}, {AxiAddrWidth{1'b1}}, axi_pkg::WTHRU_NOALLOCATE);

    fork
      // Act as a sink
      slave_drv.run()         ;
      master_drv.run(200, 200);
    join_any

    // Done
    #(10*CyclTime);
    eos = 1'b1;
  end

  /*************
   *  MONITOR  *
   *************/

  initial begin : proc_monitor
    static tb_axi_dw_pkg::axi_dw_upsizer_monitor #(
      .AxiAddrWidth       (AxiAddrWidth       ),
      .AxiMstPortDataWidth(AxiMstPortDataWidth),
      .AxiSlvPortDataWidth(AxiSlvPortDataWidth),
      .AxiIdWidth         (AxiIdWidth         ),
      .AxiUserWidth       (AxiUserWidth       ),
      .TimeTest           (TestTime           )
    ) monitor = new (master_dv, slave_dv);
    fork
      monitor.run();
      forever begin
        #TestTime;
        if(eos) begin
          monitor.print_result();
          $stop()               ;
        end
        @(posedge clk);
      end
    join
  end

// vsim -voptargs=+acc work.tb_axi_dw_upsizer
endmodule : tb_axi_dw_upsizer
