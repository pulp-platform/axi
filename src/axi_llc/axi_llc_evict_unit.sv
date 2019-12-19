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
// File:   axi_llc_evict_unit.sv
// Author: Wolfgang Roenninger <wroennin@student.ethz.ch>
// Date:   29.05.2019
//
// Description: houses the components for the evict operation
//              Is AW/W/B AXI Master and evicts lines from the different ways
//              Descripors enter, go to the AW master, then to W master, then leave through a FIFO
//              The port `flush_desc_recv_o` notifies the config module that a flush descriptor
//              ended its journey through the eviction pipeline.

module axi_llc_evict_unit #(
  parameter axi_llc_pkg::llc_cfg_t     Cfg       = -1,
  parameter axi_llc_pkg::llc_axi_cfg_t AxiCfg    = -1,
  parameter type                       desc_t    = logic,
  parameter type                       way_inp_t = logic,
  parameter type                       way_oup_t = logic,
  parameter type                       aw_chan_t = logic,
  parameter type                       w_chan_t  = logic,
  parameter type                       b_chan_t  = logic
) (
  input clk_i,    // Clock
  input rst_ni,   // Asynchronous reset active low
  input test_i,   // Test mode activate
  // descriptor input
  input  desc_t    desc_i,
  input  logic     desc_valid_i,
  output logic     desc_ready_o,
  // descriptor output
  output desc_t    desc_o,
  output logic     desc_valid_o,
  input  logic     desc_ready_i,
  // to the ways
  output way_inp_t way_inp_o,
  output logic     way_inp_valid_o,
  input  logic     way_inp_ready_i,
  // from the ways
  input  way_oup_t way_out_i,
  input  logic     way_out_valid_i,
  output logic     way_out_ready_o,
  // AW channel master
  output aw_chan_t aw_chan_mst_o,
  output logic     aw_chan_valid_o,
  input  logic     aw_chan_ready_i,
  // W channel master
  output w_chan_t  w_chan_mst_o,
  output logic     w_chan_valid_o,
  input  logic     w_chan_ready_i,
  // B channel master
  input  b_chan_t  b_chan_mst_i,
  input  logic     b_chan_valid_i,
  output logic     b_chan_ready_o,
  // to cfg
  output logic     flush_desc_recv_o
);

  // descriptor signals between AW master and eviction FIFO
  desc_t desc_aw;
  logic  desc_aw_valid;
  logic  desc_aw_ready;
  // descriptor signals between eviction FIFO and W master
  desc_t desc_w;
  logic  desc_w_valid;
  logic  desc_w_ready;
  // descriptor signals between W master and miss buffer FIFO
  desc_t desc_b;
  logic  desc_b_valid;
  logic  desc_b_ready;

  axi_llc_ax_master #(
    .Cfg             ( Cfg                    ),
    .AxiCfg          ( AxiCfg                 ),
    .desc_t          ( desc_t                 ),
    .ax_chan_t       ( aw_chan_t              ),
    .cache_unit      ( axi_llc_pkg::EvictUnit )
  ) i_aw_master (
    .clk_i           ( clk_i           ),
    .rst_ni          ( rst_ni          ),
    // Descriptor in
    .desc_i          ( desc_i          ),
    .desc_valid_i    ( desc_valid_i    ),
    .desc_ready_o    ( desc_ready_o    ),
    // to fifo
    .desc_o          ( desc_aw         ),
    .desc_valid_o    ( desc_aw_valid   ),
    .desc_ready_i    ( desc_aw_ready   ),
    // AR channel master
    .ax_chan_mst_o   ( aw_chan_mst_o   ),
    .ax_chan_valid_o ( aw_chan_valid_o ),
    .ax_chan_ready_i ( aw_chan_ready_i )
  );

  // FIFO between AW master and W mastrer, this many evictions transactions can be in flight
  axi_llc_desc_fifo #(
    .desc_t        ( desc_t                      ),
    .Depth         ( axi_llc_pkg::EvictFifoDepth )
  ) i_no_evictions_fifo (
    .clk_i         ( clk_i          ),
    .rst_ni        ( rst_ni         ),
    .test_i        ( test_i         ),
    // from AW master
    .desc_i        ( desc_aw        ),
    .desc_valid_i  ( desc_aw_valid  ),
    .desc_ready_o  ( desc_aw_ready  ),
    // to W master
    .desc_o        ( desc_w         ),
    .desc_valid_o  ( desc_w_valid   ),
    .desc_ready_i  ( desc_w_ready   ),
    // fill flag
    .fifo_ussage_o ( /*not used*/   )
  );

  axi_llc_w_master #(
    .Cfg             ( Cfg       ),
    .AxiCfg          ( AxiCfg    ),
    .desc_t          ( desc_t    ),
    .way_inp_t       ( way_inp_t ),
    .way_oup_t       ( way_oup_t ),
    .w_chan_t        ( w_chan_t  ),
    .b_chan_t        ( b_chan_t  )
  ) i_w_master (
    .clk_i           ( clk_i           ),
    .rst_ni          ( rst_ni          ),
    .test_i          ( test_i          ),
    // from in flight FIFO
    .desc_i          ( desc_w          ),
    .desc_valid_i    ( desc_w_valid    ),
    .desc_ready_o    ( desc_w_ready    ),
    // to miss buffer FIFO
    .desc_o          ( desc_b          ),
    .desc_valid_o    ( desc_b_valid    ),
    .desc_ready_i    ( desc_b_ready    ),
    // W channel master
    .w_chan_mst_o    ( w_chan_mst_o    ),
    .w_chan_valid_o  ( w_chan_valid_o  ),
    .w_chan_ready_i  ( w_chan_ready_i  ),
    // B channel master
    .b_chan_mst_i    ( b_chan_mst_i    ),
    .b_chan_valid_i  ( b_chan_valid_i  ),
    .b_chan_ready_o  ( b_chan_ready_o  ),
    // to data way
    .way_inp_o       ( way_inp_o       ),
    .way_inp_valid_o ( way_inp_valid_o ),
    .way_inp_ready_i ( way_inp_ready_i ),
    // from data way
    .way_out_i       ( way_out_i       ),
    .way_out_valid_i ( way_out_valid_i ),
    .way_out_ready_o ( way_out_ready_o ),
    // to cfg
    .flush_desc_recv_o(flush_desc_recv_o)
  );

  axi_llc_desc_fifo #(
    .desc_t        ( desc_t                       ),
    .Depth         ( axi_llc_pkg::MissBufferDepth )
  ) i_miss_buffer_fifo (
    .clk_i         ( clk_i          ),
    .rst_ni        ( rst_ni         ),
    .test_i        ( test_i         ),
    // from W master
    .desc_i        ( desc_b         ),
    .desc_valid_i  ( desc_b_valid   ),
    .desc_ready_o  ( desc_b_ready   ),
    // to output
    .desc_o        ( desc_o         ),
    .desc_valid_o  ( desc_valid_o   ),
    .desc_ready_i  ( desc_ready_i   ),
    // fill flag
    .fifo_ussage_o ( /*not used*/   )
  );
endmodule
