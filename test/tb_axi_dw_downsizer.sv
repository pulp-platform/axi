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
// Authors:
// - Matheus Cavalcante <matheusd@iis.ee.ethz.ch>
// - Andreas Kurth <akurth@iis.ee.ethz.ch>

`include "axi/assign.svh"

module tb_axi_dw_downsizer #(
    // AXI Parameters
    parameter int unsigned TbAxiAddrWidth        = 64  ,
    parameter int unsigned TbAxiIdWidth          = 4   ,
    parameter int unsigned TbAxiSlvPortDataWidth = 64  ,
    parameter int unsigned TbAxiMstPortDataWidth = 32  ,
    parameter int unsigned TbAxiUserWidth        = 8   ,
    parameter int unsigned TbInitialBStallCycles = 0,
    parameter int unsigned TbInitialRStallCycles = 0,
    // TB Parameters
    parameter time TbCyclTime                    = 10ns,
    parameter time TbApplTime                    = 2ns ,
    parameter time TbTestTime                    = 8ns
  );

  /*********************
   *  CLOCK GENERATOR  *
   *********************/

  logic clk;
  logic rst_n;
  logic eos;

  int unsigned b_stall;
  int unsigned r_stall;

  clk_rst_gen #(
    .ClkPeriod    (TbCyclTime),
    .RstClkCycles (5       )
  ) i_clk_rst_gen (
    .clk_o (clk  ),
    .rst_no(rst_n)
  );

  /*********
   *  AXI  *
   *********/

  // Master port

  AXI_BUS_DV #(
    .AXI_ADDR_WIDTH(TbAxiAddrWidth       ),
    .AXI_DATA_WIDTH(TbAxiSlvPortDataWidth),
    .AXI_ID_WIDTH  (TbAxiIdWidth         ),
    .AXI_USER_WIDTH(TbAxiUserWidth       )
  ) master_dv (
    .clk_i(clk)
  );

  AXI_BUS #(
    .AXI_ADDR_WIDTH(TbAxiAddrWidth       ),
    .AXI_DATA_WIDTH(TbAxiSlvPortDataWidth),
    .AXI_ID_WIDTH  (TbAxiIdWidth         ),
    .AXI_USER_WIDTH(TbAxiUserWidth       )
  ) master ();

  `AXI_ASSIGN_AW(master, master_dv)
  `AXI_ASSIGN_W(master, master_dv)
  `AXI_ASSIGN_AR(master, master_dv)
  assign master_dv.b_id    =                       master.b_id;
  assign master_dv.b_resp  =                       master.b_resp;
  assign master_dv.b_user  =                       master.b_user;
  assign master_dv.b_valid = b_stall != 0 ? 1'b0 : master.b_valid;
  assign master.b_ready    = b_stall != 0 ? 1'b0 : master_dv.b_ready;
  assign master_dv.r_id    =                       master.r_id;
  assign master_dv.r_data  =                       master.r_data;
  assign master_dv.r_resp  =                       master.r_resp;
  assign master_dv.r_last  =                       master.r_last;
  assign master_dv.r_user  =                       master.r_user;
  assign master_dv.r_valid = r_stall != 0 ? 1'b0 : master.r_valid;
  assign master.r_ready    = r_stall != 0 ? 1'b0 : master_dv.r_ready;

  always_ff @(posedge clk or negedge rst_n) begin : proc_
    if(~rst_n) begin
      b_stall <= TbInitialBStallCycles;
      r_stall <= TbInitialRStallCycles;
    end else begin
      b_stall <= b_stall == 0 ? 0 : b_stall-1;
      r_stall <= r_stall == 0 ? 0 : r_stall-1;
    end
  end

  axi_test::axi_rand_master #(
    .AW             (TbAxiAddrWidth       ),
    .DW             (TbAxiSlvPortDataWidth),
    .IW             (TbAxiIdWidth         ),
    .UW             (TbAxiUserWidth       ),
    .TA             (TbApplTime           ),
    .TT             (TbTestTime           ),
    .MAX_READ_TXNS  (8                  ),
    .MAX_WRITE_TXNS (8                  ),
    .AXI_BURST_FIXED(1'b0               ),
    .AXI_ATOPS      (1'b1               )
  ) master_drv = new (master_dv);

  // Slave port

  AXI_BUS_DV #(
    .AXI_ADDR_WIDTH(TbAxiAddrWidth       ),
    .AXI_DATA_WIDTH(TbAxiMstPortDataWidth),
    .AXI_ID_WIDTH  (TbAxiIdWidth         ),
    .AXI_USER_WIDTH(TbAxiUserWidth       )
  ) slave_dv (
    .clk_i(clk)
  );

  AXI_BUS #(
    .AXI_ADDR_WIDTH(TbAxiAddrWidth       ),
    .AXI_DATA_WIDTH(TbAxiMstPortDataWidth),
    .AXI_ID_WIDTH  (TbAxiIdWidth         ),
    .AXI_USER_WIDTH(TbAxiUserWidth       )
  ) slave ();

  axi_test::axi_rand_slave #(
    .AW(TbAxiAddrWidth       ),
    .DW(TbAxiMstPortDataWidth),
    .IW(TbAxiIdWidth         ),
    .UW(TbAxiUserWidth       ),
    .TA(TbApplTime           ),
    .TT(TbTestTime           )
  ) slave_drv = new (slave_dv);

  `AXI_ASSIGN(slave_dv, slave)

  /*********
   *  DUT  *
   *********/

  axi_dw_converter_intf #(
    .AXI_MAX_READS          (4                    ),
    .AXI_ADDR_WIDTH         (TbAxiAddrWidth       ),
    .AXI_ID_WIDTH           (TbAxiIdWidth         ),
    .AXI_SLV_PORT_DATA_WIDTH(TbAxiSlvPortDataWidth),
    .AXI_MST_PORT_DATA_WIDTH(TbAxiMstPortDataWidth),
    .AXI_USER_WIDTH         (TbAxiUserWidth       )
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
    master_drv.add_memory_region({TbAxiAddrWidth{1'b0}}, {TbAxiAddrWidth{1'b1}}, axi_pkg::WTHRU_NOALLOCATE);

    // Wait for the reset before sending requests
    @(posedge rst_n);

    fork
      // Act as a sink
      slave_drv.run()         ;
      master_drv.run(200, 200);
    join_any

    // Done
    repeat (10) @(posedge clk);
    eos = 1'b1;
  end

  /*************
   *  MONITOR  *
   *************/

  initial begin : proc_monitor
    static tb_axi_dw_pkg::axi_dw_downsizer_monitor #(
      .AxiAddrWidth       (TbAxiAddrWidth       ),
      .AxiMstPortDataWidth(TbAxiMstPortDataWidth),
      .AxiSlvPortDataWidth(TbAxiSlvPortDataWidth),
      .AxiIdWidth         (TbAxiIdWidth         ),
      .AxiUserWidth       (TbAxiUserWidth       ),
      .TimeTest           (TbTestTime           )
    ) monitor = new (master_dv, slave_dv);
    fork
      monitor.run();
      forever begin
        #TbTestTime;
        if(eos) begin
          monitor.print_result();
          $stop()               ;
        end
        @(posedge clk);
      end
    join
  end

// vsim -voptargs=+acc work.tb_axi_dw_downsizer
endmodule : tb_axi_dw_downsizer
