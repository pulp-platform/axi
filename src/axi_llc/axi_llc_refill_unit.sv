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
// File:   axi_llc_refill_unit.sv
// Author: Wolfgang Roenninger <wroennin@student.ethz.ch>
// Date:   28.05.2019
//
// Description: houses the components for the refill operation
//              Is Ar/R Axi Master and refills lines to the different cache ways
//              Descripors enter, go to the ar master, then to a fifo, then to r master, then leave
//

module axi_llc_refill_unit #(
  parameter axi_llc_pkg::llc_cfg_t     Cfg       = -1,
  parameter axi_llc_pkg::llc_axi_cfg_t AxiCfg    = -1,
  parameter type                       desc_t    = logic,
  parameter type                       way_inp_t = logic,
  parameter type                       ar_chan_t = logic,
  parameter type                       r_chan_t  = logic
) (
  input  logic clk_i,  // Clock
  input  logic rst_ni, // Asynchronous reset active low
  input  logic test_i, // set during test
  // descriptor input
  input  desc_t    desc_i,
  input  logic     desc_valid_i,
  output logic     desc_ready_o,
  // descriptor output
  output desc_t              desc_o,
  output logic     desc_valid_o,
  input  logic     desc_ready_i,
  // to the ways
  output way_inp_t way_inp_o,
  output logic     way_inp_valid_o,
  input  logic     way_inp_ready_i,
  // AR channel master
  output ar_chan_t ar_chan_mst_o,
  output logic     ar_chan_valid_o,
  input  logic     ar_chan_ready_i,
  // R channel master
  input  r_chan_t  r_chan_mst_i,
  input  logic     r_chan_valid_i,
  output logic     r_chan_ready_o
);

  // descriptor signals between ar master and fifo
  desc_t desc_ar;
  logic  desc_ar_valid;
  logic  desc_ar_ready;
  // descriptor signals between fifo and r master
  desc_t desc_r;
  logic  desc_r_valid;
  logic  desc_r_ready;

  axi_llc_ax_master #(
    .Cfg        ( Cfg                    ),
    .AxiCfg     ( AxiCfg                 ),
    .desc_t     ( desc_t                 ),
    .ax_chan_t  ( ar_chan_t              ),
    .cache_unit ( axi_llc_pkg::RefilUnit )
  ) i_ar_master (
    .clk_i           ( clk_i           ),
    .rst_ni          ( rst_ni          ),
    // Descriptor in
    .desc_i          ( desc_i          ),
    .desc_valid_i    ( desc_valid_i    ),
    .desc_ready_o    ( desc_ready_o    ),
    // to fifo
    .desc_o          ( desc_ar         ),
    .desc_valid_o    ( desc_ar_valid   ),
    .desc_ready_i    ( desc_ar_ready   ),
    // AR channel master
    .ax_chan_mst_o   ( ar_chan_mst_o   ),
    .ax_chan_valid_o ( ar_chan_valid_o ),
    .ax_chan_ready_i ( ar_chan_ready_i )
  );

  axi_llc_desc_fifo #(
    .desc_t ( desc_t                       ),
    .Depth  ( axi_llc_pkg::RefillFifoDepth )
  ) i_no_refills_fifo (
    .clk_i          ( clk_i         ),
    .rst_ni         ( rst_ni        ),
    .test_i         ( test_i        ),
    // from ar master
    .desc_i         ( desc_ar       ),
    .desc_valid_i   ( desc_ar_valid ),
    .desc_ready_o   ( desc_ar_ready ),
    // to r master
    .desc_o         ( desc_r        ),
    .desc_valid_o   ( desc_r_valid  ),
    .desc_ready_i   ( desc_r_ready  ),
    // fill pionter
    .fifo_ussage_o  ( /*not used*/  )
  );

  axi_llc_r_master #(
    .Cfg       ( Cfg       ),
    .AxiCfg    ( AxiCfg    ),
    .desc_t    ( desc_t    ),
    .way_inp_t ( way_inp_t ),
    .r_chan_t  ( r_chan_t  )
  ) i_r_master (
    .clk_i          ( clk_i           ),
    .rst_ni         ( rst_ni          ),
    // from fifo
    .desc_i         ( desc_r          ),
    .desc_valid_i   ( desc_r_valid    ),
    .desc_ready_o   ( desc_r_ready    ),
    // Descriptor out
    .desc_o         ( desc_o          ),
    .desc_valid_o   ( desc_valid_o    ),
    .desc_ready_i   ( desc_ready_i    ),
    // R channel master
    .r_chan_mst_i   ( r_chan_mst_i    ),
    .r_chan_valid_i ( r_chan_valid_i  ),
    .r_chan_ready_o ( r_chan_ready_o  ),
    // to data way
    .way_inp_o      ( way_inp_o       ),
    .way_inp_valid_o( way_inp_valid_o ),
    .way_inp_ready_i( way_inp_ready_i )
  );
endmodule
