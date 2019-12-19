// Copyright (c) 2019 ETH Zurich, University of Bologna
//
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
//
// File:   axi_llc_desc_fifo.sv
// Author: Wolfgang Roenninger <wroennin@student.ethz.ch>
// Date:   28.05.2019
//
// Description: is a FIFO for the LLC descriptors, has handshakeing in AXI style

module axi_llc_desc_fifo #(
  parameter type         desc_t    = logic,
  parameter int unsigned Depth     = 8,
  // DO NOT OVERWRITE THIS PARAMETER
  parameter int unsigned AddrDepth = (Depth > 1) ? $clog2(Depth) : 1
) (
  input  logic                 clk_i,  // Clock
  input  logic                 rst_ni, // Asynchronous reset active low
  input  logic                 test_i, // test mode
  // descriptor input
  input  desc_t                desc_i,
  input  logic                 desc_valid_i,
  output logic                 desc_ready_o,
  // descriptor output
  output desc_t                desc_o,
  output logic                 desc_valid_o,
  input  logic                 desc_ready_i,
  // ussage output
  output logic [AddrDepth-1:0] fifo_ussage_o
);

  // signals
  logic push, pop;
  logic full, empty;
  // Handshaking input
  assign desc_ready_o = ~full;
  assign push         = desc_valid_i & ~full;
  // Handshaking output
  assign desc_valid_o = ~empty;
  assign pop          = desc_ready_i & ~empty;

  fifo_v3 #(
    .FALL_THROUGH ( 1'b1   ),
    .DEPTH        ( Depth  ),
    .dtype        ( desc_t )
  ) i_fifo (
    .clk_i        ( clk_i         ),
    .rst_ni       ( rst_ni        ),
    .flush_i      ( '0            ),
    .testmode_i   ( test_i        ),
    .full_o       ( full          ),
    .empty_o      ( empty         ),
    .usage_o      ( fifo_ussage_o ),
    .data_i       ( desc_i        ),
    .push_i       ( push          ),
    .data_o       ( desc_o        ),
    .pop_i        ( pop           )
  );
endmodule
