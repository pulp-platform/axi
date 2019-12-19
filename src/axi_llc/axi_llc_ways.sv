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
// Author: Wolfgang Roenninger <wroennin@student.ethz.ch>
// Date:   31.05.2019
//
// Description: Holds the interconnect and the generates the different Ways for the llc
// Inputs     : The four way_inp_t from the units, structs are defined in `axi_llc_top`.
//              The struct needs a field called `way_ind` for switching.
// Outputs    : The responses to the two units that want a read response from the macros.
//
// There are two FIFO's parallel to the ways, they hold the output switching decision for
// read outputs. These are necessary, if one of the read request unit stalls, there could be
// multiple read responses waiting in different ways. The output multiplexer has to know
// in which ordering the requests were made.

module axi_llc_ways #(
  parameter axi_llc_pkg::llc_cfg_t    Cfg = -1,
  parameter type                way_inp_t = logic,
  parameter type                way_oup_t = logic
) (
  input  logic           clk_i,  // Clock
  input  logic           rst_ni, // Asynchronous reset active low
  input  logic           test_i, // Test Mode Enable
  // Way inputs
  input  way_inp_t [3:0] way_inp_i,
  input  logic     [3:0] way_inp_valid_i,
  output logic     [3:0] way_inp_ready_o,
  // Way outputs
  output way_oup_t       evict_way_out_o,
  output logic           evict_way_out_valid_o,
  input  logic           evict_way_out_ready_i,
  output way_oup_t       read_way_out_o,
  output logic           read_way_out_valid_o,
  input  logic           read_way_out_ready_i
);

  typedef logic [Cfg.SetAssociativity-1:0] way_ind_t; // way indicator for switching decision

  // input signal handshaking can be disconnected if the read output FIFO is full
  logic [3:0] inp_valid, inp_ready;

  // crossbar signals, these arrays have to be explicit
  logic [3:0][Cfg.SetAssociativity-1:0] to_way_valid;
  logic [Cfg.SetAssociativity-1:0][3:0] t_to_way_valid;
  logic [3:0][Cfg.SetAssociativity-1:0] to_way_ready;
  logic [Cfg.SetAssociativity-1:0][3:0] t_to_way_ready;

  // input to the ways
  way_inp_t [Cfg.SetAssociativity-1:0]  way_inp;
  logic     [Cfg.SetAssociativity-1:0]  way_inp_valid;
  logic     [Cfg.SetAssociativity-1:0]  way_inp_ready;

  // output from the ways
  way_oup_t [Cfg.SetAssociativity-1:0]  way_out;
  logic     [Cfg.SetAssociativity-1:0]  way_out_valid;
  logic     [Cfg.SetAssociativity-1:0]  way_out_ready;

  // binary number which selects the right way to send the request to
  logic [3:0][$clog2(Cfg.SetAssociativity)-1:0] demux_bin;

  // FIFO signals, these are here so that read responses can not get reordered!
  way_ind_t e_switch,       r_switch;
  logic     e_switch_full,  r_switch_full;
  logic     e_switch_empty, r_switch_empty;
  logic     e_switch_push,  r_switch_push;
  logic     e_switch_pop,   r_switch_pop;

  // connect the right inputs dependent on FIFO fullness where it is required
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

  // demultiplexer for each unit to the ways
  for (genvar i = 0; i < 4; i++) begin : gen_connect_demux
    onehot_to_bin #(
      .ONEHOT_WIDTH ( Cfg.SetAssociativity )
    ) i_demux_onehot (
      .onehot ( way_inp_i[i].way_ind ),
      .bin    ( demux_bin[i]         )
    );

    stream_demux #(
      .N_OUP        ( Cfg.SetAssociativity )
    ) i_unit_demux (
      .inp_valid_i  ( inp_valid[i]    ),
      .inp_ready_o  ( inp_ready[i]    ),
      .oup_sel_i    ( demux_bin[i]    ),
      .oup_valid_o  ( to_way_valid[i] ),
      .oup_ready_i  ( to_way_ready[i] )
    );
    for (genvar j = 0; j < Cfg.SetAssociativity; j++) begin : gen_connect_cross
      assign t_to_way_valid[j][i] = to_way_valid[i][j];
      assign to_way_ready[i][j]   = t_to_way_ready[j][i];
    end
  end

  // once for each way
  for (genvar j = 0; j < Cfg.SetAssociativity; j++) begin : gen_data_ways
    // connect both units to the RAM
    rr_arb_tree #(
      .NumIn    ( 4          ),
      .DataType ( way_inp_t  ),
      .AxiVldRdy( 1'b1       )
    ) i_req_mux (
      .clk_i    ( clk_i             ),
      .rst_ni   ( rst_ni            ),
      .flush_i  ( 1'b0              ),
      .rr_i     ( '0                ),
      .data_i   ( way_inp_i         ),
      .req_i    ( t_to_way_valid[j] ), // equals valid
      .gnt_o    ( t_to_way_ready[j] ), // equals ready
      .data_o   ( way_inp      [j]  ),
      .req_o    ( way_inp_valid[j]  ),
      .gnt_i    ( way_inp_ready[j]  ),
      .idx_o    (                   )
    );

    axi_llc_data_way #(
      .Cfg       ( Cfg       ),
      .way_inp_t ( way_inp_t ),
      .way_oup_t ( way_oup_t )
    ) i_data_way (
      .clk_i      ( clk_i            ),
      .rst_ni     ( rst_ni           ),
      .test_i     ( test_i           ),
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
    .clk_i        ( clk_i                                     ),  // Clock
    .rst_ni       ( rst_ni                                    ),  // Asynchronous reset active low
    .flush_i      ( '0                                        ),  // flush the queue
    .testmode_i   ( test_i                                    ),  // test_mode
    .full_o       ( r_switch_full                             ),  // queue is full
    .empty_o      ( r_switch_empty                            ),  // queue is empty
    .usage_o      (                                           ),  // fill pointer
    .data_i       ( way_inp_i[axi_llc_pkg::RChanUnit].way_ind ),  // data to push into the queue
    .push_i       ( r_switch_push                             ),  // data is valid
    .data_o       ( r_switch                                  ),  // output data
    .pop_i        ( r_switch_pop                              )   // pop head from queue
  );
  fifo_v3 #(
    .FALL_THROUGH ( 1'b0                 ), // SRAM has one cycle latency anyway
    .DEPTH        ( Cfg.SetAssociativity ), // each way could have a read response request
    .dtype        ( way_ind_t            )
  ) i_e_switch_fifo (
    .clk_i        ( clk_i                                     ),  // Clock
    .rst_ni       ( rst_ni                                    ),  // Asynchronous reset active low
    .flush_i      ( '0                                        ),  // flush the queue
    .testmode_i   ( test_i                                    ),  // test_mode
    .full_o       ( e_switch_full                             ),  // queue is full
    .empty_o      ( e_switch_empty                            ),  // queue is empty
    .usage_o      (                                           ),  // fill pointer
    .data_i       ( way_inp_i[axi_llc_pkg::EvictUnit].way_ind ),  // data to push into the queue
    .push_i       ( e_switch_push                             ),  // data is valid
    .data_o       ( e_switch                                  ),  // output data
    .pop_i        ( e_switch_pop                              )   // pop head from queue
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
