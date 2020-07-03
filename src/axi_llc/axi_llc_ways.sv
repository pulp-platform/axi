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
// File:   axi_llc_ways.sv
// Author: Wolfgang Roenninger <wroennin@iis.ee.ethz.ch>
// Date:   31.05.2019

/// Holds the interconnect and the generates the different Ways for the llc
/// Inputs:  The four way_inp_t from the units, structs are defined in `axi_llc_top`.
///   The struct needs a field called `way_ind` for switching.
/// Outputs: The responses to the two units that want a read response from the macros.
///
/// There are two FIFO's parallel to the ways, they hold the output switching decision for
/// read outputs. These are necessary, if one of the read request unit stalls, there could be
/// multiple read responses waiting in different ways. The output multiplexer has to know
/// in which ordering the requests were made.
module axi_llc_ways #(
  /// Static LLC configuration parameter struct.
  parameter axi_llc_pkg::llc_cfg_t Cfg = axi_llc_pkg::llc_cfg_t'{default: '0},
  /// Data way request payload type definition.
  parameter type way_inp_t = logic,
  /// Data way response payload type definition.
  parameter type way_oup_t = logic
) (
  /// Clock, positive edge triggered.
  input logic clk_i,
  /// Asynchronous reset, active low.
  input logic rst_ni,
  /// Testmode enable, active high.
  input logic test_i,
  /// Way request payloads inputs. One array index for each unit which can make request to the
  /// data storage macros.
  input way_inp_t [3:0] way_inp_i,
  /// Way request is valid.
  input logic [3:0] way_inp_valid_i,
  /// Data way is ready for the request.
  output logic [3:0] way_inp_ready_o,
  /// Way response payload to the evict unit.
  output way_oup_t evict_way_out_o,
  /// Response to the evict unit is valid.
  output logic evict_way_out_valid_o,
  /// Evict unit is ready for the response.
  input logic evict_way_out_ready_i,
  /// Way response payload to the read unit.
  output way_oup_t read_way_out_o,
  /// Response to the read unit is valid.
  output logic read_way_out_valid_o,
  /// Read unit is ready for the response.
  input logic read_way_out_ready_i
);
  localparam int unsigned SelIdxWidth = cf_math_pkg::idx_width(Cfg.SetAssociativity);
  typedef logic [SelIdxWidth-1:0]          way_sel_t; // Binary representation of the way selection
  typedef logic [Cfg.SetAssociativity-1:0] way_ind_t; // way indicator for switching decision

  // input signal handshaking can be disconnected if the read output FIFO is full
  logic [3:0] inp_valid, inp_ready;

  // input to the ways
  way_inp_t [Cfg.SetAssociativity-1:0]  way_inp;
  logic     [Cfg.SetAssociativity-1:0]  way_inp_valid;
  logic     [Cfg.SetAssociativity-1:0]  way_inp_ready;

  // output from the ways
  way_oup_t [Cfg.SetAssociativity-1:0]  way_out;
  logic     [Cfg.SetAssociativity-1:0]  way_out_valid;
  logic     [Cfg.SetAssociativity-1:0]  way_out_ready;

  // binary number which selects the right way to send the request to
  way_sel_t [3:0] way_sel;

  // FIFO signals, these are here so that read responses can not get reordered!
  way_ind_t e_switch,       r_switch;
  logic     e_switch_full,  r_switch_full;
  logic     e_switch_empty, r_switch_empty;
  logic     e_switch_push,  r_switch_push;
  logic     e_switch_pop,   r_switch_pop;

  // Connect the right input handshaking dependent on FIFO fullness where it is required.
  // All are written here explicit, so that unit can be extended in the future to
  // also have a read response (e.g. ATOP support in write unit).
  // Evict unit (watch the FIFO)
  assign inp_valid[axi_llc_pkg::EvictUnit]       =
      ~e_switch_full & way_inp_valid_i[axi_llc_pkg::EvictUnit];
  assign way_inp_ready_o[axi_llc_pkg::EvictUnit] =
      ~e_switch_full & inp_ready[axi_llc_pkg::EvictUnit];
  // Refill Unit
  assign inp_valid[axi_llc_pkg::RefilUnit]       = way_inp_valid_i[axi_llc_pkg::RefilUnit];
  assign way_inp_ready_o[axi_llc_pkg::RefilUnit] = inp_ready[axi_llc_pkg::RefilUnit];
  // Write unit
  assign inp_valid[axi_llc_pkg::WChanUnit]       = way_inp_valid_i[axi_llc_pkg::WChanUnit];
  assign way_inp_ready_o[axi_llc_pkg::WChanUnit] = inp_ready[axi_llc_pkg::WChanUnit];
  // Read unit (watch the FIFO)
  assign inp_valid[axi_llc_pkg::RChanUnit]       =
      ~r_switch_full & way_inp_valid_i[axi_llc_pkg::RChanUnit];
  assign way_inp_ready_o[axi_llc_pkg::RChanUnit] =
      ~r_switch_full & inp_ready[axi_llc_pkg::RChanUnit];

  // Selection signal of each unit to the ways.
  for (genvar i = 0; unsigned'(i) < 32'd4; i++) begin : gen_connect_demux
    onehot_to_bin #(
      .ONEHOT_WIDTH ( Cfg.SetAssociativity )
    ) i_onehot_to_bin (
      .onehot ( way_inp_i[i].way_ind ),
      .bin    ( way_sel[i]           )
    );
  end

  stream_xbar #(
    .NumInp      ( 32'd4                ),
    .NumOut      ( Cfg.SetAssociativity ),
    .payload_t   ( way_inp_t            ),
    .OutSpillReg ( 1'b0                 ),
    .ExtPrio     ( 1'b0                 ),
    .AxiVldRdy   ( 1'b1                 ),
    .LockIn      ( 1'b1                 )
  ) i_stream_xbar (
    .clk_i,
    .rst_ni,
    .flush_i ( '0              ),
    .rr_i    ( '0              ),
    .data_i  ( way_inp_i       ),
    .sel_i   ( way_sel         ),
    .valid_i ( inp_valid       ),
    .ready_o ( inp_ready       ),
    .data_o  ( way_inp         ),
    .idx_o   ( /*not used*/    ),
    .valid_o ( way_inp_valid   ),
    .ready_i ( way_inp_ready   )
  );

  // once for each way
  for (genvar j = 0; unsigned'(j) < Cfg.SetAssociativity; j++) begin : gen_data_ways
    axi_llc_data_way #(
      .Cfg       ( Cfg       ),
      .way_inp_t ( way_inp_t ),
      .way_oup_t ( way_oup_t )
    ) i_data_way (
      .clk_i,
      .rst_ni,
      .test_i,
      .inp_i      ( way_inp[j]       ),
      .inp_valid_i( way_inp_valid[j] ),
      .inp_ready_o( way_inp_ready[j] ),
      .out_o      ( way_out[j]       ),
      .out_valid_o( way_out_valid[j] ),
      .out_ready_i( way_out_ready[j] )
    );
  end

  // output to the evict and read unit gets controlled by a FIFO each
  // not looking onto the request flag, because this two unit only can make read requests
  assign r_switch_push =
      way_inp_valid_i[axi_llc_pkg::RChanUnit] & way_inp_ready_o[axi_llc_pkg::RChanUnit];
  assign e_switch_push =
      way_inp_valid_i[axi_llc_pkg::EvictUnit] & way_inp_ready_o[axi_llc_pkg::EvictUnit];

  fifo_v3 #(
    .FALL_THROUGH ( 1'b0                 ),  // SRAM has on cycle latency anyway
    .DEPTH        ( Cfg.SetAssociativity ),  // each way could have a read response request
    .dtype        ( way_ind_t            )
  ) i_r_switch_fifo (
    .clk_i,                                                     // Clock
    .rst_ni,                                                    // Asynchronous reset active low
    .flush_i    ( '0                                        ),  // flush the queue
    .testmode_i ( test_i                                    ),  // test_mode
    .full_o     ( r_switch_full                             ),  // queue is full
    .empty_o    ( r_switch_empty                            ),  // queue is empty
    .usage_o    (                                           ),  // fill pointer
    .data_i     ( way_inp_i[axi_llc_pkg::RChanUnit].way_ind ),  // data to push into the queue
    .push_i     ( r_switch_push                             ),  // data is valid
    .data_o     ( r_switch                                  ),  // output data
    .pop_i      ( r_switch_pop                              )   // pop head from queue
  );
  fifo_v3 #(
    .FALL_THROUGH ( 1'b0                 ), // SRAM has one cycle latency anyway
    .DEPTH        ( Cfg.SetAssociativity ), // each way could have a read response request
    .dtype        ( way_ind_t            )
  ) i_e_switch_fifo (
    .clk_i,                                                     // Clock
    .rst_ni,                                                    // Asynchronous reset active low
    .flush_i    ( '0                                        ),  // flush the queue
    .testmode_i ( test_i                                    ),  // test_mode
    .full_o     ( e_switch_full                             ),  // queue is full
    .empty_o    ( e_switch_empty                            ),  // queue is empty
    .usage_o    (                                           ),  // fill pointer
    .data_i     ( way_inp_i[axi_llc_pkg::EvictUnit].way_ind ),  // data to push into the queue
    .push_i     ( e_switch_push                             ),  // data is valid
    .data_o     ( e_switch                                  ),  // output data
    .pop_i      ( e_switch_pop                              )   // pop head from queue
  );

  // output to evict and read unit, listen to the output of the switch FIFOs
  always_comb begin
    // default assignments
    evict_way_out_o       = '0;
    evict_way_out_valid_o = '0;
    e_switch_pop          = 1'b0;
    read_way_out_o        = '0;
    read_way_out_valid_o  = '0;
    r_switch_pop          = 1'b0;
    way_out_ready         = '0;
    for (int unsigned m = 0; m < Cfg.SetAssociativity; m++) begin
      // evict unit wants a read output
      if (e_switch[m] && !e_switch_empty) begin
        // the correct output is ready
        if (way_out_valid[m] && (way_out[m].cache_unit == axi_llc_pkg::EvictUnit)) begin
          evict_way_out_o       = way_out[m];
          evict_way_out_valid_o = 1'b1;
          // evict unit eats the response
          if (evict_way_out_ready_i) begin
            way_out_ready[m] = 1'b1;
            e_switch_pop     = 1'b1;
          end
        end
      end
      // read unit wants a read output
      if (r_switch[m] && !r_switch_empty) begin
        // the correct output is ready
        if (way_out_valid[m] && (way_out[m].cache_unit == axi_llc_pkg::RChanUnit)) begin
          read_way_out_o       = way_out[m];
          read_way_out_valid_o = 1'b1;
          // evict unit eats the response
          if (read_way_out_ready_i) begin
            way_out_ready[m] = 1'b1;
            r_switch_pop     = 1'b1;
          end
        end
      end
    end
  end
endmodule
