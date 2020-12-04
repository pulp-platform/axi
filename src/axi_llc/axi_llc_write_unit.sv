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
// File:   axi_llc_write_unit.sv
// Author: Wolfgang Roenninger <wroennin@iis.ee.ethz.ch>
// Date:   21.05.2019

/// This module takes a descriptor as input and sends appropriate W channel beats to the data
/// storage.
/// When the last descriptor of a burst is finished writing onto the macros it sends the appropriate
/// B response onto the B channel of the slave port.
/// For this the unit has a small FIFO, writes can only done if there is space in the FIFO.
/// When a write descriptor is finished, the bloom filter in the hit_miss_unit gets notified and the
/// line unlocked.
/// This unit can only perform writes when `w_unlock_gnt_i`
/// is asserted.
module axi_llc_write_unit #(
  /// Static LLC configuration parameter struct.
  parameter axi_llc_pkg::llc_cfg_t Cfg = axi_llc_pkg::llc_cfg_t'{default: '0},
  /// Static LLC AXI configuration parameters.
  parameter axi_llc_pkg::llc_axi_cfg_t AxiCfg = axi_llc_pkg::llc_axi_cfg_t'{default: '0},
  /// LLC descriptor type definition.
  parameter type desc_t = logic,
  /// Data way request payload type definition.
  parameter type way_inp_t = logic,
  /// Lock struct definition. This is for the bloom filter to signal, that the line is unlocked.
  parameter type lock_t = logic,
  /// AXI slave port W channel struct definition.
  parameter type w_chan_t = logic,
  /// AXI slave port B channel struct definition.
  parameter type b_chan_t = logic
) (
  /// Clock, positive edge triggered.
  input logic clk_i,
  /// Asynchronous reset, active low.
  input logic rst_ni,
  /// Testmode enable, active high.
  input logic test_i,
  /// Write descriptor payload input.
  input desc_t desc_i,
  /// An input descriptor is valid.
  input logic desc_valid_i,
  /// Unit is ready for accepting an input descriptor.
  output logic desc_ready_o,
  /// AXI slave port W channel payload input.
  input w_chan_t w_chan_slv_i,
  /// AXI W beat is valid.
  input logic w_chan_valid_i,
  /// AXI W beat is ready.
  output logic w_chan_ready_o,
  /// AXI slave port B channel payload output.
  output b_chan_t b_chan_slv_o,
  /// AXI B beat is valid.
  output logic b_chan_valid_o,
  /// AXI B Beat is ready.
  input logic b_chan_ready_i,
  /// Request payload to the data ways.
  output way_inp_t way_inp_o,
  /// Data way request is valid.
  output logic way_inp_valid_o,
  /// Data way is ready for a request.
  input logic way_inp_ready_i,
  /// Unlock signal payload for the line locking mechanism.
  output lock_t w_unlock_o,
  /// Unlock request.
  /// NOT AXI compliant!
  output logic w_unlock_req_o,
  /// Unlock request can be granted.
  /// NOT AXI compliant! Has to be `1'b1` so that the unit is active!
  input logic w_unlock_gnt_i
);
  `include "common_cells/registers.svh"
  typedef logic [AxiCfg.AddrWidthFull-1:0] addr_t;
  // flip flops
  desc_t         desc_d,      desc_q;
  logic          busy_d,      busy_q;
  logic          load_desc,   load_busy;

  // W channel FIFO signals
  w_chan_t       w_chan;
  logic          w_valid, w_ready;

  // B spill register signals
  b_chan_t       b_chan;
  logic          b_valid, b_ready;

  // W channel pipeline FIFO
  // This FIFO buffers W beats as long as the corresponding AW
  // vector goes through the pipeline for lookup etc.
  stream_fifo #(
    .FALL_THROUGH ( 1'b0                          ),
    .DEPTH        ( axi_llc_pkg::WChanBufferDepth ),
    .T            ( w_chan_t                      )
  ) i_w_stream_fifo (
    .clk_i,
    .rst_ni,
    .flush_i    ( 1'b0           ),
    .testmode_i ( test_i         ),
    .usage_o    ( /*not used*/   ),
    .data_i     ( w_chan_slv_i   ),
    .valid_i    ( w_chan_valid_i ),
    .ready_o    ( w_chan_ready_o ),
    .data_o     ( w_chan         ),
    .valid_o    ( w_valid        ),
    .ready_i    ( w_ready        )
  );

  // way_inp assignments
  assign way_inp_o = '{
    cache_unit: axi_llc_pkg::WChanUnit,
    way_ind:    desc_q.way_ind,
    line_addr:  desc_q.a_x_addr[(Cfg.ByteOffsetLength + Cfg.BlockOffsetLength) +: Cfg.IndexLength],
    blk_offset: desc_q.a_x_addr[ Cfg.ByteOffsetLength +: Cfg.BlockOffsetLength],
    we:         1'b1,
    data:       w_chan.data,
    strb:       w_chan.strb
  };

  // assignment of the write unlock fields, which are not set with the control below
  assign w_unlock_o = '{
    index:   desc_q.a_x_addr[(Cfg.ByteOffsetLength + Cfg.BlockOffsetLength) +: Cfg.IndexLength],
    way_ind: desc_q.way_ind
  };

  // unit control
  always_comb begin
    desc_d           = desc_q;
    load_desc        = 1'b0;
    busy_d           = busy_q;
    load_busy        = 1'b0;
    // handshaking signals
    desc_ready_o     = 1'b0;
    w_ready          = 1'b0;
    way_inp_valid_o  = 1'b0;
    // unlock signal
    w_unlock_req_o   = 1'b0;
    // b response FIFO push signal
    b_valid          = 1'b0;
    // control
    if (busy_q) begin
      // only do something if the B response could be send
      // allowed to listen for b ready as it comes from a spill register
      if (b_ready && w_unlock_gnt_i) begin

        // check if there is no internal error, this block has to be before the next one
        // as the W beat handshaking gets set here
        if (desc_q.x_resp != axi_pkg::RESP_SLVERR) begin
          // connect the handshaking
          way_inp_valid_o = w_valid;
          w_ready         = way_inp_ready_i;
        end else begin
          // Error, eat the W beats and continue
          w_ready         = 1'b1;
        end

        // when a transfer occurs, look at the length field or update the descriptor
        if (w_valid && w_ready) begin
          if (desc_q.a_x_len == '0) begin
            // should a B be sent?
            if (desc_q.x_last) begin
              b_valid = 1'b1;
            end
            busy_d         = 1'b0;
            load_busy      = 1'b1;
            w_unlock_req_o = 1'b1;
            load_new_desc(); // a new descriptor can be loaded if there is one
          end else begin
            // update the descriptor, when not
            load_desc      = 1'b1;
            desc_d.a_x_len = desc_q.a_x_len - axi_pkg::len_t'(1);
            // update the address when necessary
            if (desc_q.a_x_burst != axi_pkg::BURST_FIXED) begin
              desc_d.a_x_addr = axi_pkg::aligned_addr(desc_q.a_x_addr +
                                    axi_pkg::num_bytes(desc_q.a_x_size), desc_q.a_x_size);
            end
          end
        end

      end
    end else begin
      // not busy, can load a new descriptor
      load_new_desc();
    end
  end

  // this function loads a new descriptor and sends the first read request to the data storage
  function void load_new_desc ();
    desc_ready_o = 1'b1;
    // we have a new descriptor, send the read request to the macros and initialize the counters
    if (desc_valid_i) begin
      desc_d    = desc_i;
      load_desc = 1'b1;
      busy_d    = 1'b1;
      load_busy = 1'b1;
    end
  endfunction : load_new_desc

  // assign of the B channel FIFO input
  assign b_chan = '{
    id:      desc_q.a_x_id,
    resp:    desc_q.x_resp,
    default: '0
  };

  // Spill register so that the B response is one cycle after W last.
  spill_register #(
    .T      ( b_chan_t ),
    .Bypass ( 1'b0     )
  ) i_spill_register_b (
    .clk_i,
    .rst_ni,
    .valid_i ( b_valid        ),
    .ready_o ( b_ready        ),
    .data_i  ( b_chan         ),
    .valid_o ( b_chan_valid_o ),
    .ready_i ( b_chan_ready_i ),
    .data_o  ( b_chan_slv_o   )
  );

  `FFLARN(desc_q, desc_d, load_desc, '0, clk_i, rst_ni)
  `FFLARN(busy_q, busy_d, load_busy, '0, clk_i, rst_ni)
endmodule
