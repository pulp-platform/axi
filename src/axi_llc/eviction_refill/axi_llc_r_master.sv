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
// File:   axi_llc_r_master.sv
// Author: Wolfgang Roenninger <wroennin@ethz.ch>
// Date:   27.05.2019
//
// This unit waits for refill R bursts on the AXI master port to put them towards the
// data storage. It uses a void function to encapsulate the loading of a new descriptor
// in its control always comb block.

// register macros
`include "common_cells/registers.svh"

module axi_llc_r_master #(
  parameter axi_llc_pkg::llc_cfg_t     Cfg       = -1,
  parameter axi_llc_pkg::llc_axi_cfg_t AxiCfg    = -1,
  parameter type                       desc_t    = logic,
  parameter type                       way_inp_t = logic,
  parameter type                       r_chan_t  = logic
) (
  input  logic clk_i,  // Clock
  input  logic rst_ni, // Asynchronous reset active low
  // descriptor input
  input  desc_t    desc_i,
  input  logic     desc_valid_i,
  output logic     desc_ready_o,
  // descriptor output
  output desc_t    desc_o,
  output logic     desc_valid_o,
  input  logic     desc_ready_i,
  // R channel
  input  r_chan_t  r_chan_mst_i,
  input  logic     r_chan_valid_i,
  output logic     r_chan_ready_o,
  // signal to the ways (is a write)
  output way_inp_t way_inp_o,
  output logic     way_inp_valid_o,
  input  logic     way_inp_ready_i
);

  typedef logic [Cfg.BlockOffsetLength-1:0] offset_t;

  // flipflops for state
  desc_t   desc_d,       desc_q;               // descriptor flipflop
  logic    busy_d,       busy_q;               // unit busy flag
  logic    send_d,       send_q;               // send descriptor along flag
  logic    load_desc,    load_busy, load_send; // load flipflop signals
  // offset counter signals
  offset_t block_offset;
  logic    en_cnt,       load_cnt;

  // output assignment
  assign desc_o = desc_q;

  // way_inp assignments
  assign way_inp_o.cache_unit   = axi_llc_pkg::RefilUnit;
  assign way_inp_o.way_ind      = desc_q.way_ind;
  assign way_inp_o.line_addr    = desc_q.a_x_addr[(Cfg.ByteOffsetLength+Cfg.BlockOffsetLength) +:
                                      Cfg.IndexLength];
  assign way_inp_o.blk_offset   = block_offset;
  assign way_inp_o.we           = 1'b1;
  assign way_inp_o.data         = r_chan_mst_i.data;
  assign way_inp_o.strb         = '1; // all bytes have to be written to the macros

  // unit control
  always_comb begin
    // default assignments registers
    desc_d    = desc_q;
    load_desc = 1'b0;
    busy_d    = busy_q;
    load_busy = 1'b0;
    send_d    = send_q;
    load_send = 1'b0;
    // handshaking signals
    desc_ready_o    = 1'b0;
    r_chan_ready_o  = 1'b0;
    way_inp_valid_o = 1'b0;
    desc_valid_o    = 1'b0;
    // offset counter enable and load
    en_cnt   = 1'b0;
    load_cnt = 1'b0;

    // do different things depending on the state of the two flipflops `busy_q` and `send_q`
    case ({busy_q, send_q})
      2'b00 : begin // idle, be ready to get a new descriptor
        load_new_desc();
      end
      2'b01 : begin // send the descriptor further
        desc_valid_o = 1'b1;
        // transaction
        if (desc_ready_i) begin
          // update to idle state, gets overridden by the task if necessary
          send_d    = 1'b0;
          load_send = 1'b1;
          load_new_desc();
        end
      end
      2'b10 : begin // the unit puts for R beats towards the ways
        // connect the r channel handshaking
        way_inp_valid_o = r_chan_valid_i;
        r_chan_ready_o  = way_inp_ready_i;
        // transfer occurs
        if (r_chan_valid_i && way_inp_ready_i) begin
          if (r_chan_mst_i.last == 1'b1) begin
            // the last refill transfer send descriptor further and potentially load a new one
            desc_valid_o = 1'b1;
            // transaction
            // update to idle state, gets overridden by the task if necessary
            busy_d    = 1'b0;
            load_busy = 1'b1;
            if (desc_ready_i) begin
              load_new_desc();
            end else begin
              // go to send state on no transaction
              send_d    = 1'b1;
              load_send = 1'b1;
            end
          end else begin
            // more R beats are coming, update the offset counter
            en_cnt = 1'b1;
          end
        end
      end
      default : begin // go to idle, so that it is not stuck in a strange state
        busy_d    = 1'b0;
        load_busy = 1'b1;
        send_d    = 1'b0;
        load_send = 1'b1;
      end
    endcase
  end

  // this function sets the input descriptor handshaking and loads a new descriptor
  // sets both the busy and send flipflop depending on the input refill flag
  // intended for use only in the always_comb block above
  // the function can here be used, as the sensitivity list is inferred automatically
  function void load_new_desc();
    desc_ready_o = 1'b1;
    // new descriptor at the input
    if (desc_valid_i) begin
      desc_d    = desc_i;
      load_desc = 1'b1;
      if (desc_i.refill) begin
        // prepare for refill r beats from the AXI channel, load the offset counter
        busy_d    = 1'b1;
        load_busy = 1'b1;
        // load in the line address as we are refilling one line at a time
        load_cnt  = 1'b1;
      end else begin
        // load the new descriptor to send further in next cycle
        send_d    = 1'b1;
        load_send = 1'b1;
      end
    end
  endfunction : load_new_desc

  // counter to count up the block offset, as the refill will always be all blocks
  counter #(
    .WIDTH        ( Cfg.BlockOffsetLength ) // maximum AXI x_len signal width
  ) i_block_offset_counter (
    .clk_i        ( clk_i        ),
    .rst_ni       ( rst_ni       ),
    .clear_i      ( 1'b0         ), // counter do not get cleared
    .en_i         ( en_cnt       ),
    .load_i       ( load_cnt     ),
    .down_i       ( 1'b0         ),
    .d_i          ( '0           ), // we evict always the whole line, start @ block 0
    .q_o          ( block_offset ), // the block offset sent towards the macros
    .overflow_o   ( /*not used*/ )  // listen on the last signal for when to stop counting
  );

  // Flip Flops
  `FFLARN(desc_q, desc_d, load_desc, '0, clk_i, rst_ni) // descriptor
  `FFLARN(busy_q, busy_d, load_busy, '0, clk_i, rst_ni) // unit busy flag
  `FFLARN(send_q, send_d, load_send, '0, clk_i, rst_ni) // send descriptor along
endmodule
