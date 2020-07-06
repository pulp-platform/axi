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
// File:   axi_llc_w_master.sv
// Author: Wolfgang Roenninger <wroennin@iis.ee.ethz.ch>
// Date:   29.05.2019

/// This unit handles the generation of w beats on the master channel if there is a cache line
/// to evict. It has a register that holds the descriptor. All operations occur, when a valid
/// descriptor is in the unit. The unit has two status flags `busy_q` and `send_q`. These
/// define the state in which the unit is currently at.
///
/// State machine:
/// case {busy_q, send_q}
/// 2'b00: IDLE:  The unit can take in a new descriptor.
/// 2'b01: SEND:  The unit sends the descriptor to the next unit. If the descriptor is from a
///               flush, it gets destroyed and the flush control gets notified.
/// 2'b10: EVICT: The unit generates requests to the macros and sends W beats on the AXI.
///               The response data of the macros can get buffered in the FIFO.
/// 2'b11: RESP:  The unit waits for the B response
///
/// On Descriptor load the evict flag of it gets checked. When it is set, initialize two counters.
/// `i_block_offset_counter`is responsible for generating the block offset of the request towards
/// the SRAM macros. This counter gets on descriptor load initialized to '0 and counts up.
/// It has the same width as the block offset, this means if the counter overflows through counting
/// up all required requests to the macros where made for this line eviction.
/// `i_w_to_send_counter` counts down and corresponds to the AX length signal. if it reaches zero
/// It indicates the last transfer of this write and the last flag gets set.
module axi_llc_w_master #(
  /// Static LLC parameter configuration.
  parameter axi_llc_pkg::llc_cfg_t Cfg = axi_llc_pkg::llc_cfg_t'{default: '0},
  /// Give the exact AXI parameters in struct form. This is passed down from
  /// [`axi_llc_top`](module.axi_llc_top).
  ///
  /// Required struct definition in: `axi_llc_pkg`.
  parameter axi_llc_pkg::llc_axi_cfg_t AxiCfg = axi_llc_pkg::llc_axi_cfg_t'{default: '0},
  /// LLC descriptor type definition.
  parameter type desc_t = logic,
  /// Data way request payload definition.
  parameter type way_inp_t = logic,
  /// Data way response payload definition.
  parameter type way_oup_t = logic,
  /// AXI W channel payload type definition.
  parameter type w_chan_t = logic,
  /// AXI B channel payload type definition.
  parameter type b_chan_t = logic
) (
  /// Clock, positive edge triggered.
  input logic clk_i,
  /// Asynchronous reset, active low.
  input logic rst_ni,
  /// Testmode enable, active high.
  input logic test_i,
  /// Input descriptor payload.
  input desc_t desc_i,
  /// Input descriptor is valid.
  input logic desc_valid_i,
  /// Unit is ready for a new descriptor.
  output logic desc_ready_o,
  /// Output descriptor payload.
  output desc_t desc_o,
  /// Output descriptor is valid.
  output logic desc_valid_o,
  /// The next unit is ready to accept the output descriptor.
  input logic desc_ready_i,
  /// AXI W master channel payload.
  output w_chan_t w_chan_mst_o,
  /// AXI W master channel is valid.
  output logic w_chan_valid_o,
  /// AXI W master channel is ready.
  input logic w_chan_ready_i,
  /// AXI B master channel payload.
  input b_chan_t b_chan_mst_i,
  /// AXI B master channel is valid.
  input logic b_chan_valid_i,
  /// AXI B master channel is ready.
  output logic b_chan_ready_o,
  /// Data way request payload.
  output way_inp_t way_inp_o,
  /// Data way request is valid.
  output logic way_inp_valid_o,
  /// Data way is ready for a request.
  input logic way_inp_ready_i,
  /// Data way response payload.
  input way_oup_t way_out_i,
  /// Data way response is valid.
  input logic way_out_valid_i,
  /// Unit is ready for data way response.
  output logic way_out_ready_o,
  /// Flag for the configuration module that a flush descriptor was destroyed here.
  output logic flush_desc_recv_o
);
  `include "common_cells/registers.svh"
  // typedefs
  typedef logic [Cfg.BlockOffsetLength-1:0] offset_t;
  typedef logic [AxiCfg.DataWidthFull-1:0]  data_t;
  // flipflops
  desc_t         desc_d,       desc_q;               // flipflops to hold descriptor
  logic          busy_d,       busy_q;               // busy flag
  logic          send_d,       send_q;               // b_beat was received
  logic          load_desc,    load_busy, load_send; // flipflop load signals
  // internal signals to manage register and counter
  offset_t       block_offset;  // output of the counter, determines the block offset of eviction
  logic          load_cnt;      // load the counters
  logic          en_cnt_req;    // count down how many requests have to be issued to the SRAM
  logic          stop_req_gen;  // stop the generation of new requests to the SRAM
  logic          en_cnt_w_chan; // count down how many beats remain for the W channel
  offset_t       curr_w_len;    // output from w channel counter, tell us when to set the last flag
  // FIFO control signals
  logic          fifo_full;     // the FIFO is full
  logic          fifo_push;     // push data into the FIFO
  logic          fifo_empty;    // the FIFO is empty -> no valid on channel
  logic          fifo_pop;      // pop data from FIFO if it gets transferred
  data_t         fifo_data;     // gets assigned to the w channel

  // W channel output (data directly from FIFO / last from control)
  assign w_chan_valid_o = ~fifo_empty;
  // push control of the FIFO and handshake to the data way
  assign fifo_push       = ~fifo_full & way_out_valid_i;
  assign way_out_ready_o = ~fifo_full;
  // w_data transfer occurs in this cycle -> pop the FIFO content
  assign fifo_pop = w_chan_ready_i & ~fifo_empty;

  // way_inp assignments
  always_comb begin : proc_way_inp
    // initialize the input to '0, then change the required fields
    way_inp_o = '0;
    way_inp_o.cache_unit = axi_llc_pkg::EvictUnit;
    way_inp_o.way_ind    = desc_q.way_ind;
    way_inp_o.line_addr  = desc_q.a_x_addr[(Cfg.ByteOffsetLength + Cfg.BlockOffsetLength) +:
                               Cfg.IndexLength]; // does not depend on the counting address
    way_inp_o.blk_offset = block_offset;
    // these comments are just for reasoning why the fields are not set
    // way_inp_o.we           = 1'b0; // only read data out from the way
    // way_inp_o.data         = '0;   // this is the eviction unit, we do not have write data
    // way_inp_o.strb         = '0;   // not write any data
  end

  always_comb begin : proc_w_chan_outp
    // init the channel to completely 0, assign then the rest
    w_chan_mst_o      = '0;
    // w channel output used signals (all assignments to the w channel are in this block)
    w_chan_mst_o.data = fifo_data;
    w_chan_mst_o.strb = '1;
    w_chan_mst_o.last = (curr_w_len == '0) ? 1'b1 : 1'b0;
  end

  // descriptor output
  assign desc_o = desc_q;

  // control
  always_comb begin : proc_control
    // default flip flop assignments
    desc_d            = desc_q;
    load_desc         = 1'b0;
    busy_d            = busy_q;
    load_busy         = 1'b0;
    send_d            = send_q;
    load_send         = 1'b0;
    // counter signals to manage the send status of an eviction
    load_cnt          = 1'b0;
    en_cnt_req        = 1'b0; // counts how many read requests remain to go to the ram
    en_cnt_w_chan     = 1'b0; // counts how many w beats remain to send on the w channel
    // handshaking signals
    desc_ready_o      = 1'b0;
    way_inp_valid_o   = 1'b0;
    b_chan_ready_o    = 1'b0;
    desc_valid_o      = 1'b0;
    // flush descriptor output to cfg
    flush_desc_recv_o = 1'b0;

    // do different things depending on the state of the two flipflops `busy_q` and `send_q`
    unique case ({busy_q, send_q})
      2'b00 : begin // unit is idle, it can load a new descriptor
        load_new_desc();
      end
      2'b01 : begin // unit wants to send the descriptor further, load a new one when possible
        if (desc_q.flush) begin
          // destroy the flush descriptor and go to idle state
          flush_desc_recv_o = 1'b1;
          send_d            = 1'b0;
          load_send         = 1'b1;
          load_new_desc();
        end else begin
          desc_valid_o = 1'b1;
          if (desc_ready_i) begin
            // go to idle and load a potential new descriptor
            send_d    = 1'b0;
            load_send = 1'b1;
            load_new_desc();
          end
        end
      end
      2'b10 : begin // conduct the requests towards the macros
        if (!stop_req_gen) begin
          way_inp_valid_o = 1'b1;
          // request handshake occurs, update the block offset counter
          if (way_inp_ready_i) begin
            en_cnt_req = 1'b1;
          end
        end
        // look for transfers on the w channel, pop from the FIFO indicates a transfer
        if (fifo_pop) begin
          en_cnt_w_chan = 1'b1;
          // on popping of the last w beat, try to receive the b response
          if(w_chan_mst_o.last) begin
            b_chan_ready_o = 1'b1;
            // depending if the b occurs this cycle go the the next states
            send_d    = 1'b1;
            load_send = 1'b1;
            if (b_chan_valid_i) begin
              // b response received, go to sending further the descriptor
              busy_d    = 1'b0;
              load_busy = 1'b1;
            end
          end
        end
      end
      2'b11 : begin // wait for receiving of the b response, prevent deadlock
        b_chan_ready_o = 1'b1;
        if (b_chan_valid_i) begin
          busy_d = 1'b0;
          load_busy = 1'b1;
        end
      end
      default: /*do nothing*/ ;
    endcase
  end

  // this function loads a descriptor into the unit
  function void load_new_desc();
    desc_ready_o = 1'b1;
    // transfer new descriptor in
    if (desc_valid_i) begin
      desc_d    = desc_i;
      load_desc = 1'b1;
      if (desc_i.evict) begin
        // prepare the unit for evicting
        busy_d    = 1'b1;
        load_busy = 1'b1;
        // load the block offset
        load_cnt  = 1'b1; // load the counters with the values
      end else begin
        // send the descriptor along
        send_d    = 1'b1;
        load_send = 1'b1;
      end
    end
  endfunction : load_new_desc

  fifo_v3 #(
    .FALL_THROUGH ( 1'b1          ),  // FIFO is in fall-through mode
    .DEPTH        ( Cfg.NumBlocks ),  // can store a whole cache line
    .dtype        ( data_t        )
  ) i_r_data_fifo (
    .clk_i        ( clk_i             ),  // Clock
    .rst_ni       ( rst_ni            ),  // Asynchronous reset active low
    .flush_i      ( '0                ),  // flush the queue
    .testmode_i   ( test_i            ),  // test_mode to bypass clock gating
    // status flags
    .full_o       ( fifo_full         ),  // queue is full
    .empty_o      ( fifo_empty        ),  // queue is empty
    .usage_o      ( /*not used*/      ),  // fill pointer
    // as long as the queue is not full we can push new data
    .data_i       ( way_out_i.data    ),  // data to push into the queue
    .push_i       ( fifo_push         ),  // data is valid and can be pushed to the queue
    // as long as the queue is not empty we can pop new elements
    .data_o       ( fifo_data         ),  // output data
    .pop_i        ( fifo_pop          )   // pop head from queue
  );

  // Cast such that synthesis does not complain about size miss match
  counter #(
    .WIDTH        ( Cfg.BlockOffsetLength ) // maximum AXI x_len signal width
  ) i_block_offset_counter (
    .clk_i        ( clk_i        ),
    .rst_ni       ( rst_ni       ),
    .clear_i      ( 1'b0         ), // counter do not get cleared
    .en_i         ( en_cnt_req   ),
    .load_i       ( load_cnt     ),
    .down_i       ( 1'b0         ),
    .d_i          ( '0           ), // we evict always the whole line, start @ block 0
    .q_o          ( block_offset ), // the block offset sent towards the macros
    .overflow_o   ( stop_req_gen )
  );

  counter #(
    .WIDTH        ( Cfg.BlockOffsetLength ) // maximum AXI len_t signal width
  ) i_w_to_send_counter (
    .clk_i        ( clk_i         ),
    .rst_ni       ( rst_ni        ),
    .clear_i      ( 1'b0          ), // counter do not get cleared
    .en_i         ( en_cnt_w_chan ),
    .load_i       ( load_cnt      ),
    .down_i       ( 1'b1          ), // count towards 0
    .d_i          ( '1            ), // we evict always the whole line, start at len = Blocks
    .q_o          ( curr_w_len    ),
    .overflow_o   ( /*not used*/  )
  );

  // Flip-flop with load-enable and asynchronous active-low reset
  `FFLARN(desc_q, desc_d, load_desc, '0, clk_i, rst_ni) // descriptor
  `FFLARN(busy_q, busy_d, load_busy, '0, clk_i, rst_ni) // unit busy flag
  `FFLARN(send_q, send_d, load_send, '0, clk_i, rst_ni) // send descriptor along

  // pragma translate_off
  `ifndef VERILATOR
  `ifndef VCS
  `ifndef SYNTHESIS
  read_fifo_error: assert property(
    @(posedge clk_i) disable iff (~rst_ni) (!busy_q |-> fifo_empty)) else
      $fatal(1, "Write Unit is not busy even fifo is not empty.");
  initial begin : check_params
    block_offset_constraint: assume ($bits(axi_pkg::len_t) >= Cfg.BlockOffsetLength) else
      $fatal(1, "The BlockOffsetLength is at maximum the width of the AXI len_t signal.");
  end
  `endif
  `endif
  `endif
  // pragma translate_on
endmodule
