// Copyright 2020 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// File          : tb_axi_dw_upsizer.sv
// Author        : Matheus Cavalcante <matheusd@iis.ee.ethz.ch>
// Created       : 09.02.2019

// Copyright (C) 2020 ETH Zurich, University of Bologna
// All rights reserved.

`include "axi/assign.svh"

module tb_axi_dw_upsizer;

  parameter AW   = 64;
  parameter IW   = 4;
  parameter DW   = 32;
  parameter UW   = 8;
  parameter MULT = 8;

  localparam tCK = 1ns;

  logic clk  = 0;
  logic rst  = 1;
  logic done = 0;

  AXI_BUS_DV #(
    .AXI_ADDR_WIDTH (AW),
    .AXI_DATA_WIDTH (DW),
    .AXI_ID_WIDTH   (IW),
    .AXI_USER_WIDTH (UW)
  ) axi_master_dv (clk);

  AXI_BUS #(
    .AXI_ADDR_WIDTH (AW),
    .AXI_DATA_WIDTH (DW),
    .AXI_ID_WIDTH   (IW),
    .AXI_USER_WIDTH (UW)
  ) axi_master();

  axi_test::rand_axi_master #(
    .AW             (AW   ),
    .DW             (DW   ),
    .IW             (IW   ),
    .UW             (UW   ),
    .MAX_READ_TXNS  (8    ),
    .MAX_WRITE_TXNS (8    ),
    .TA             (200ps),
    .TT             (700ps)
  ) axi_master_drv = new (axi_master_dv);

  AXI_BUS_DV #(
    .AXI_ADDR_WIDTH (AW       ),
    .AXI_DATA_WIDTH (MULT * DW),
    .AXI_ID_WIDTH   (IW       ),
    .AXI_USER_WIDTH (UW       )
  ) axi_slave_dv ( clk );

  AXI_BUS #(
    .AXI_ADDR_WIDTH (AW       ),
    .AXI_DATA_WIDTH (MULT * DW),
    .AXI_ID_WIDTH   (IW       ),
    .AXI_USER_WIDTH (UW       )
  ) axi_slave ();

  axi_test::rand_axi_slave #(
    .AW (AW       ),
    .DW (MULT * DW),
    .IW (IW       ),
    .UW (UW       ),
    .TA (200ps    ),
    .TT (700ps    )
  ) axi_slave_drv = new ( axi_slave_dv );

  `AXI_ASSIGN(axi_master, axi_master_dv);
  `AXI_ASSIGN(axi_slave_dv, axi_slave)  ;

  axi_dw_converter #(
    .AxiMstDataWidth(MULT*DW),
    .AxiSlvDataWidth(DW     ),
    .AxiIdWidth     (IW     ),
    .AxiUserWidth   (UW     ),
    .AxiMaxTrans    (4      )
  ) i_dw_converter (
    .clk_i  (clk       ),
    .rst_ni (rst       ),
    .slv    (axi_master),
    .mst    (axi_slave )
  );

  initial begin
    #tCK;
    rst <= 0;
    #tCK;
    rst <= 1;
    #tCK;
    while (!done) begin
      clk <= 1;
      #(tCK/2);
      clk <= 0;
      #(tCK/2);
    end
  end

  initial begin
    axi_master_drv.reset()                                                             ;
    axi_master_drv.add_memory_region({AW{1'b0}}, {AW{1'b1}}, axi_pkg::WTHRU_NOALLOCATE);
    axi_master_drv.run(50, 50)                                                         ;
    done = 1;
  end

  initial begin
    axi_slave_drv.reset();
    axi_slave_drv.run()  ;
  end

// vsim -voptargs=+acc work.tb_axi_dw_upsizer
endmodule : tb_axi_dw_upsizer
