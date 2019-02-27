// Copyright 2019 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// File          : axi_data_downsize.sv
// Author        : Matheus Cavalcante <matheusd@iis.ee.ethz.ch>
// Created       : 31.01.2019
//
// Copyright (C) 2019 ETH Zurich, University of Bologna
// All rights reserved.
//
// Description:
// AXI Data Downsize Conversion.
// Connects a wide master to a narrower slave.

import axi_pkg::*;

module axi_data_downsize #(
  parameter int unsigned MI_DATA_WIDTH = 64,
  parameter int unsigned SI_DATA_WIDTH = 64
) (
  input logic clk_i,
  input logic rst_ni,
  AXI_BUS.in  in,
  AXI_BUS.out out
);

`ifndef SYNTHESIS
  initial begin
    assert(SI_DATA_WIDTH > MI_DATA_WIDTH);
  end
`endif

  // --------------
  // DEFINITIONS
  // --------------

  localparam addr_t MI_BYTES = MI_DATA_WIDTH/8;
  localparam addr_t MI_BYTE_MASK = MI_BYTES - 1;
  typedef logic [MI_DATA_WIDTH-1:0] mi_data_t;
  typedef logic [MI_BYTES-1:0]      mi_strb_t;

  localparam addr_t SI_BYTES = SI_DATA_WIDTH/8;
  localparam addr_t SI_BYTE_MASK = SI_BYTES - 1;
  typedef logic [SI_DATA_WIDTH-1:0] si_data_t;
  typedef logic [SI_BYTES-1:0]      si_strb_t;

  function automatic addr_t align_addr(addr_t addr);
    return addr & ~MI_BYTE_MASK;
  endfunction // align_addr

endmodule // axi_data_downsize
