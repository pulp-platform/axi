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
// File:   axi_llc_data_way.sv
// Author: Wolfgang Roenninger <wroennin@iis.ee.ethz.ch>
// Date:   20.05.2019

/// Implements one Way/Set of the cache and controls the memory macro where the
/// cached data is stored in. From the `way_inp` struct it determines what action
/// should be performed on the macro. The module answers with read output and the
/// enum of the module, which made the read request. The module is able to stall
/// if the read is not consumed the cycle it is made.
`include "common_cells/registers.svh"
module axi_llc_data_way #(
  /// Static AXI LLC configuration
  parameter axi_llc_pkg::llc_cfg_t   Cfg        = -1,
  /// The input struct has to be defined as follows (is done in `axi_llc_top`):
  /// typedef struct packed {
  ///   axi_axi_llc_pkg::cache_unit_e     cache_unit;   // which unit does the access
  ///   logic [Cfg.SetAssociativity -1:0] way_ind;      // to which way the access goes
  ///   logic [Cfg.IndexLength      -1:0] line_addr;    // cache line address
  ///   logic [Cfg.BlockOffsetLength-1:0] blk_offset;   // block offset
  ///   logic                             we;           // write enable
  ///   axi_data_t                        data;         // write data to the macro
  ///   axi_strb_t                        strb;         // write enable (AXI strb)
  /// } way_inp_t;
  parameter type                     way_inp_t  = logic,
  /// The output struct has to be defined as follows (is done in `axi_llc_top`):
  /// typedef struct packed {
  ///   axi_axi_llc_pkg::cache_unit_e cache_unit;   // which unit had the access
  ///   axi_data_t                    data;         // read data from the macro
  /// } way_oup_t;
  parameter type                     way_oup_t  = logic
) (
  /// Clock, positive edge triggered
  input  logic     clk_i,
  /// Asynchronous reset active low
  input  logic     rst_ni,
  /// Testmode enable
  input  logic     test_i,
  /// Data way request input
  input  way_inp_t inp_i,
  /// Request is valid
  input  logic     inp_valid_i,
  /// Module is ready to handle a request
  output logic     inp_ready_o,
  /// Output is read data, has routing information, which unit made an access.
  output way_oup_t out_o,
  /// Output is valid.
  output logic     out_valid_o,
  /// Downstream is ready for output.
  input  logic     out_ready_i
);

  // The number of lines of each data SRAM macro
  localparam int unsigned SRamAddrWidth = Cfg.IndexLength + Cfg.BlockOffsetLength;

  // SRAM control signals
  logic [SRamAddrWidth-1:0] addr;    // true macro address
  logic                     ram_req; // request to the macro

  // flip-flops to know when the output data is valid on a read request
  logic                     outp_valid_d, outp_valid_q;
  axi_llc_pkg::cache_unit_e cache_unit_d, cache_unit_q;
  logic                     load_unit,    load_valid;

  // concatenate the line address (index) and block offset to get the true address
  assign addr = {inp_i.line_addr, inp_i.blk_offset};

  //----------------------------------------------------------
  // Control
  //----------------------------------------------------------
  assign out_o.cache_unit = cache_unit_q; // for the data demux in the module `axi_llc_ways`
  assign out_valid_o      = outp_valid_q;

  // control of the data way, handles the handshaking and macro signals
  always_comb begin
    // default assignments
    cache_unit_d = cache_unit_q;
    load_unit    = 1'b0;
    outp_valid_d = outp_valid_q;
    load_valid   = 1'b0;
    ram_req      = 1'b0;
    // module handshakes for the input
    inp_ready_o  = 1'b0;
    if (outp_valid_q) begin
      // valid output from the SRAM, wait for handshake
      if (out_ready_i) begin
        // we update `outp_valid_d` anyway
        load_valid = 1'b1;
        // what value gets written depends on if there is another sram request
        if (inp_valid_i) begin
          // we can handle the new input
          inp_ready_o  = 1'b1;
          cache_unit_d = inp_i.cache_unit;
          load_unit    = 1'b1;
          outp_valid_d = ~inp_i.we;
          ram_req      = 1'b1;
        end else begin
          outp_valid_d = 1'b0;
        end
      end
    end else begin
      // we are able to handle a request to the sram
      inp_ready_o = 1'b1;
      if (inp_valid_i) begin
        // load the registers and request to the sram
        cache_unit_d = inp_i.cache_unit;
        load_unit    = 1'b1;
        outp_valid_d = ~inp_i.we;
        load_valid   = 1'b1;
        ram_req      = 1'b1;
      end
    end
  end

  tc_sram #(
    .NumWords   ( Cfg.NoLines * Cfg.NoBlocks ),
    .DataWidth  ( Cfg.BlockSize              ),
    .ByteWidth  ( 32'd8                      ),
    .NumPorts   ( 32'd1                      ),
    .Latency    ( 32'd1                      ),
    .SimInit    ( "none"                     ),
    .PrintSimCfg( 1'b1                       )
  ) i_data_sram (
    .clk_i,
    .rst_ni,
    .req_i   ( ram_req    ),
    .we_i    ( inp_i.we   ),
    .addr_i  ( addr       ),
    .wdata_i ( inp_i.data ),
    .be_i    ( inp_i.strb ),
    .rdata_o ( out_o.data )
  );

  // Flip Flops to hold the read request meta information
  `FFLARN(outp_valid_q, outp_valid_d, load_valid, '0, clk_i, rst_ni)
  `FFLARN(cache_unit_q, cache_unit_d, load_unit, axi_llc_pkg::EvictUnit, clk_i, rst_ni)
endmodule
