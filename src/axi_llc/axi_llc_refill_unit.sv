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
// Author: Wolfgang Roenninger <wroennin@iis.ee.ethz.ch>
// Date:   28.05.2019

/// Houses the components for the refill operation.
/// Is Ar/R Axi Master and refills lines to the different cache ways.
/// Descripors enter, go to the ar master, then to a fifo, then to r master, then leave.
module axi_llc_refill_unit #(
  /// Static LLC configuration parameters.
  parameter axi_llc_pkg::llc_cfg_t Cfg = axi_llc_pkg::llc_cfg_t'{default: '0},
  /// Static LLC AXI configuration parameters.
  parameter axi_llc_pkg::llc_axi_cfg_t AxiCfg = axi_llc_pkg::llc_axi_cfg_t'{default: '0},
  /// LLC descriptor type definition.
  parameter type desc_t = logic,
  /// LLC way input request payload type.
  parameter type way_inp_t = logic,
  /// AXI master port AR channel type.
  parameter type ar_chan_t = logic,
  /// AXI master port R channel type.
  parameter type r_chan_t = logic
) (
  /// Clock, positive edge triggered.
  input logic clk_i,
  /// Asynchronous reset, active low.
  input logic rst_ni,
  /// Testmode enable, active high.
  input logic test_i,
  /// Descriptor payload input. Comes from the eviction pipeline.
  input desc_t desc_i,
  /// Input descriptor is vaild.
  input logic desc_valid_i,
  /// Module is ready to accept a descriptor.
  output logic desc_ready_o,
  /// Output descriptor payload. This descriptor finished the refill pipeline and can be
  /// transferred to either the read or the write unit.
  output desc_t desc_o,
  /// Output descriptor is valid.
  output logic desc_valid_o,
  /// Downstream is ready to accept the output descriptor.
  input logic desc_ready_i,
  /// Request payload to the data storage ways. These will be writes as it is a refill.
  output way_inp_t way_inp_o,
  /// Request to the data storage ways is valid.
  output logic way_inp_valid_o,
  /// Data storage way is ready to accept the request.
  input logic way_inp_ready_i,
  /// AR master channel payload.
  output ar_chan_t ar_chan_mst_o,
  /// AR beat is valid.
  output logic ar_chan_valid_o,
  /// AR beat is ready.
  input logic ar_chan_ready_i,
  /// R master channel payload.
  input r_chan_t r_chan_mst_i,
  /// R beat is valid.
  input logic r_chan_valid_i,
  /// R beat is ready.
  output logic r_chan_ready_o
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

  stream_fifo #(
    .FALL_THROUGH ( 1'b1                         ),
    .DEPTH        ( axi_llc_pkg::RefillFifoDepth ),
    .T            ( desc_t                       )
  ) i_stream_fifo_refill (
    .clk_i,
    .rst_ni,
    .flush_i   ( 1'b0          ),
    .testmode_i( test_i        ),
    .usage_o   ( /*not used*/  ),
    .data_i    ( desc_ar       ),
    .valid_i   ( desc_ar_valid ),
    .ready_o   ( desc_ar_ready ),
    .data_o    ( desc_r        ),
    .valid_o   ( desc_r_valid  ),
    .ready_i   ( desc_r_ready  )
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
