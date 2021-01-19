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
// Author: Wolfgang Roenninger <wroennin@iis.ee.ethz.ch>
// Date:   29.05.2019

/// Houses the components for the eviction operation.
/// Is AW/W/B AXI Master and evicts lines from the different ways
/// Descriptors enter, go to the AW master, then to W master, then leave through a FIFO
/// The port `flush_desc_recv_o` notifies the configuration module that a flush descriptor
/// ended its journey through the eviction pipeline.
module axi_llc_evict_unit #(
  /// Static LLC configuration parameters.
  parameter axi_llc_pkg::llc_cfg_t Cfg = axi_llc_pkg::llc_cfg_t'{default: '0},
  /// Static LLC AXI configuration parameters.
  parameter axi_llc_pkg::llc_axi_cfg_t AxiCfg = axi_llc_pkg::llc_axi_cfg_t'{default: '0},
  /// LLC descriptor type definition.
  parameter type desc_t = logic,
  /// LLC way input request payload type.
  parameter type way_inp_t = logic,
  /// LLC way output response payload type.
  parameter type way_oup_t = logic,
  /// AXI master port AW channel type.
  parameter type aw_chan_t = logic,
  /// AXI master port W channel type.
  parameter type w_chan_t = logic,
  /// AXI master port B channel type.
  parameter type b_chan_t = logic
) (
  /// Clock, positive edge triggered.
  input logic clk_i,
  /// Asynchronous reset, active low.
  input logic rst_ni,
  /// Test mode enable, active high.
  input logic test_i,
  /// Descriptor payload input. This descriptor comes from the hit_miss detection unit.
  input desc_t desc_i,
  /// Input descriptor is valid.
  input logic desc_valid_i,
  /// Module is ready to accept a descriptor.
  output logic desc_ready_o,
  /// Descriptor payload output. This descriptor finished the eviction pipeline and goes
  /// to the refill pipeline.
  output desc_t desc_o,
  /// Output descriptor is valid.
  output logic desc_valid_o,
  /// Downstream is ready to accept the output descriptor.
  input logic desc_ready_i,
  /// Eviction request to the data ways. This comes from the W channel unit and will issue
  /// reads for cache lines that are evicted/written back.
  output way_inp_t way_inp_o,
  /// Data storage way request is valid.
  output logic way_inp_valid_o,
  /// Way is ready to accept the request.
  input logic way_inp_ready_i,
  /// Response payload from the ways. This is the read data from the storage macros which is
  /// written back through the master port.
  input way_oup_t way_out_i,
  /// Data way has a valid response.
  input logic way_out_valid_i,
  /// Unit is ready to accept the response from the ways.
  output logic way_out_ready_o,
  /// AW master channel payload.
  output aw_chan_t aw_chan_mst_o,
  /// AW beat is valid.
  output logic aw_chan_valid_o,
  /// AW beat is ready.
  input logic aw_chan_ready_i,
  /// W master channel payload.
  output w_chan_t w_chan_mst_o,
  /// W beat is valid.
  output logic w_chan_valid_o,
  /// W beat is ready.
  input logic w_chan_ready_i,
  /// B master channel payload.
  input b_chan_t b_chan_mst_i,
  /// B beat is valid.
  input logic b_chan_valid_i,
  /// B beat is ready.
  output logic b_chan_ready_o,
  /// A flush descriptor finished/destroyed in the eviction pipeline.
  output logic flush_desc_recv_o
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

  // FIFO between AW master and W master, this many evictions transactions can be in flight
  stream_fifo #(
    .FALL_THROUGH ( 1'b1                        ),
    .DEPTH        ( axi_llc_pkg::EvictFifoDepth ),
    .T            ( desc_t                      )
  ) i_stream_fifo_evict (
    .clk_i,
    .rst_ni,
    .flush_i    ( 1'b0          ),
    .testmode_i ( test_i        ),
    .usage_o    ( /*not used*/  ),
    .data_i     ( desc_aw       ),
    .valid_i    ( desc_aw_valid ),
    .ready_o    ( desc_aw_ready ),
    .data_o     ( desc_w        ),
    .valid_o    ( desc_w_valid  ),
    .ready_i    ( desc_w_ready  )
  );

  axi_llc_w_master #(
    .Cfg       ( Cfg       ),
    .AxiCfg    ( AxiCfg    ),
    .desc_t    ( desc_t    ),
    .way_inp_t ( way_inp_t ),
    .way_oup_t ( way_oup_t ),
    .w_chan_t  ( w_chan_t  ),
    .b_chan_t  ( b_chan_t  )
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

  stream_fifo #(
    .FALL_THROUGH ( 1'b1                         ),
    .DEPTH        ( axi_llc_pkg::MissBufferDepth ),
    .T            ( desc_t                       )
  ) i_stream_fifo_miss_buffer (
    .clk_i,
    .rst_ni,
    .flush_i    ( 1'b0         ),
    .testmode_i ( test_i       ),
    .usage_o    ( /*not used*/ ),
    .data_i     (desc_b        ),
    .valid_i    (desc_b_valid  ),
    .ready_o    (desc_b_ready  ),
    .data_o     (desc_o        ),
    .valid_o    (desc_valid_o  ),
    .ready_i    (desc_ready_i  )
  );
endmodule
