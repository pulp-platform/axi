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
// File:   axi_llc_read_unit.sv
// Author: Wolfgang Roenninger <wroennin@student.ethz.ch>
// Date:   24.05.2019
//
// Description: This module takes a descriptor as input and sends
//              appropriate R channel beats from the data storage
//              It issues read requests to the data SRAM way specified in the descriptor
//              There is a FIFO, which stores the R channel meta information, when the
//              read request is made to the data SRAM, all other fields of the R beat get also
//              described into this R metadata FIFO. When the read data response arrives, the
//              complete R beat gets assembled and put into the R channel output FIFO.

// register macros
`include "common_cells/registers.svh"

module axi_llc_read_unit #(
  parameter axi_llc_pkg::llc_cfg_t     Cfg       = -1,
  parameter axi_llc_pkg::llc_axi_cfg_t AxiCfg    = -1,
  parameter type                       desc_t    = logic,
  parameter type                       way_inp_t = logic,
  parameter type                       way_oup_t = logic,
  parameter type                       lock_t    = logic,
  parameter type                       r_chan_t  = logic
) (
  input  logic     clk_i,  // Clock
  input  logic     rst_ni, // Active low reset
  input  logic     test_i, // Testmode
  // descriptor input
  input  desc_t    desc_i,
  input  logic     desc_valid_i,
  output logic     desc_ready_o,
  // R channel output
  output r_chan_t  r_chan_slv_o,
  output logic     r_chan_valid_o,
  input  logic     r_chan_ready_i,
  // signals to the ways
  output way_inp_t way_inp_o,
  output logic     way_inp_valid_o,
  input  logic     way_inp_ready_i,
  // signals from the ways
  input  way_oup_t way_out_i,
  input  logic     way_out_valid_i,
  output logic     way_out_ready_o,
  // unlock signal
  output lock_t    r_unlock_o,
  output logic     r_unlock_req_o, // NOT AXI compliant!
  input  logic     r_unlock_gnt_i  // NOT AXI compliant!
);
  typedef logic [AxiCfg.SlvPortIdWidth-1:0] id_t;
  typedef logic [AxiCfg.DataWidthFull-1:0]  data_t;
  // this struct saves the r channel meta information before it goes to the R FIFO
  typedef struct packed {
    id_t            id;
    axi_pkg::resp_t resp;
    logic           last;
  } r_meta_t;

  // flipflops
  desc_t          desc_d,    desc_q;  // flipflop to hold descriptor
  logic           load_desc;
  logic           busy_d,    busy_q;  // status if descriptor occupies unit
  logic           load_busy;
  // R FIFO control signals
  r_chan_t        r_fifo_inp;      // the assembled R beat to put on the channel
  logic           r_fifo_push;     // push a read response from way into FIFO
  logic           r_fifo_full;     // the R FIFO is full
  logic           r_fifo_empty;    // to signal valid status to axi and control
  logic           r_fifo_pop;      // is set to high if a data transfer occurs
  // R channel metadate FIFO
  r_meta_t        meta_fifo_inp;
  logic           meta_fifo_full;
  logic           meta_fifo_push;
  r_meta_t        meta_fifo_outp;
  logic           meta_fifo_empty;
  logic           meta_fifo_pop;

  // way_inp assignments
  assign way_inp_o = '{
    cache_unit: axi_llc_pkg::RChanUnit,
    way_ind:    desc_q.way_ind,
    line_addr:  desc_q.a_x_addr[(Cfg.ByteOffsetLength + Cfg.BlockOffsetLength)+:Cfg.IndexLength],
    blk_offset: desc_q.a_x_addr[ Cfg.ByteOffsetLength +: Cfg.BlockOffsetLength],
    default: '0
  }; // other fields not needed, `we` is `1'b0.

  //always_comb begin
  //  way_inp_o = '0;
  //  way_inp_o.cache_unit   = axi_llc_pkg::RChanUnit;
  //  way_inp_o.way_ind      = desc_q.way_ind;
  //  way_inp_o.line_addr    =
  //      desc_q.a_x_addr[(Cfg.ByteOffsetLength + Cfg.BlockOffsetLength)+:Cfg.IndexLength];
  //  way_inp_o.blk_offset   =
  //      desc_q.a_x_addr[ Cfg.ByteOffsetLength                         +:Cfg.BlockOffsetLength];
  //  // these comments are just for reasoning, why the fields are not set
  //  // way_inp_o.we           = 1'b0;
  //  // way_inp_o.data         = '0; // this is the read unit, we do not have write data
  //  // way_inp_o.strb         = '0;
  //end

  // unlock assignment
  assign r_unlock_o = '{
    index:   desc_q.a_x_addr[(Cfg.ByteOffsetLength + Cfg.BlockOffsetLength)+:Cfg.IndexLength],
    way_ind: desc_q.way_ind
  };
//  assign r_unlock_o.index   =
//      desc_q.a_x_addr[(Cfg.ByteOffsetLength + Cfg.BlockOffsetLength)+:Cfg.IndexLength];
//  assign r_unlock_o.way_ind = desc_q.way_ind;

  // control
  always_comb begin
    // default assignments
    desc_d    = desc_q;
    load_desc = 1'b0;
    busy_d    = busy_q;
    load_busy = 1'b0;
    // handshaking signals
    way_inp_valid_o = 1'b0;
    desc_ready_o    = 1'b0;
    // unlock signal
    r_unlock_req_o = 1'b0;

    // control
    if (busy_q) begin
      // we are busy and have a descriptor inside (listen to meta FIFO)
      if (!meta_fifo_full && r_unlock_gnt_i) begin
        // send requests towards the macros
        way_inp_valid_o = 1'b1;
        if (way_inp_ready_i) begin
          //transaction
          if (desc_q.a_x_len == '0) begin
            // all read requests where made, go to IDLE and load potential new descriptor
            busy_d    = 1'b0;
            load_busy = 1'b1;
            // unlock the line, line is free when the bloom filter is updated in the next cycle
            r_unlock_req_o = 1'b1;
            load_new_desc();
          end else begin
            // more read requests have to be made, update the address and update the length
            if (desc_q.a_x_burst != axi_pkg::BURST_FIXED) begin
              // update the address
              desc_d.a_x_addr = desc_q.a_x_addr + 2**desc_q.a_x_size;
            end
            desc_d.a_x_len  = desc_q.a_x_len - axi_pkg::len_t'(1);
            load_desc       = 1'b1;
          end
        end
      end
    end else begin
      // be ready to load a new descriptor, when not busy
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

  // Metadata FIFO
  assign meta_fifo_inp = '{
    id:   desc_q.a_x_id,                           // propagate ID
    resp: desc_q.x_resp,                           // propagate response
    last: (desc_q.x_last & (desc_q.a_x_len == '0)) // set the last flag only on the last request
  };
  // push pop control of the metadata FIFO
  assign meta_fifo_push = way_inp_valid_o & way_inp_ready_i; // push when request to SRAM is made
  assign meta_fifo_pop  = r_fifo_push;                       // pop when R beat goes to output FIFO

  // push data into the R FIFO
  assign r_fifo_push     =  way_out_valid_i & way_out_ready_o;
  assign way_out_ready_o = ~r_fifo_full     & ~meta_fifo_empty;

  // The FIFO is directly connected to the R channel, this means its handshaking is the pop control
  assign r_chan_valid_o  = ~r_fifo_empty;
  assign r_fifo_pop      =  r_chan_ready_i & ~r_fifo_empty;

  // R FIFO data assignment
  assign r_fifo_inp = r_chan_t'{
    id:   meta_fifo_outp.id,
    // Add data from the SRAM only if the response is ok.
    data: (meta_fifo_outp.resp inside {axi_pkg::RESP_OKAY}) ?
              way_out_i.data : data_t'(axi_llc_pkg::AxiLlcVersion),
    resp: meta_fifo_outp.resp,
    last: meta_fifo_outp.last,
    default: '0
  };

  fifo_v3 #(
    .FALL_THROUGH ( 1'b0     ),  // FIFO not in fall-through mode as SRAM has one cycle latency
    .DEPTH        ( 3        ),  // two places for stalling
    .dtype        ( r_meta_t )
  ) i_r_meta_fifo (
    .clk_i        ( clk_i           ),  // Clock
    .rst_ni       ( rst_ni          ),  // Asynchronous reset active low
    .flush_i      ( '0              ),  // flush the queue
    .testmode_i   ( test_i          ),  // test_mode to bypass clock gating
    .full_o       ( meta_fifo_full  ),  // queue is full
    .empty_o      ( meta_fifo_empty ),  // queue is empty
    .usage_o      (                 ),  // fill pointer
    .data_i       ( meta_fifo_inp   ),  // data to push into the queue
    .push_i       ( meta_fifo_push  ),  // push on requests to the SRAM
    .data_o       ( meta_fifo_outp  ),  // output data
    .pop_i        ( meta_fifo_pop   )   // pop when data is pushed to R FIFO
  );
  fifo_v3 #(
    .FALL_THROUGH ( 1'b1         ),  // FIFO is in fall-through mode, for read response latency
    .DEPTH        ( Cfg.NoBlocks ),  // can store a whole cache line, when the request size is max
    .dtype        ( r_chan_t     )
  ) i_r_fifo (
    .clk_i        ( clk_i        ),  // Clock
    .rst_ni       ( rst_ni       ),  // Asynchronous reset active low
    .flush_i      ( '0           ),  // flush the queue
    .testmode_i   ( test_i       ),  // test_mode to bypass clock gating
    .full_o       ( r_fifo_full  ),  // queue is full
    .empty_o      ( r_fifo_empty ),  // queue is empty
    .usage_o      (              ),  // fill pointer
    .data_i       ( r_fifo_inp   ),  // data to push into the queue
    .push_i       ( r_fifo_push  ),  // data is valid and can be pushed to the queue
    .data_o       ( r_chan_slv_o ),  // output data
    .pop_i        ( r_fifo_pop   )   // pop head from queue
);

  // Flip Flops
  `FFLARN(desc_q, desc_d, load_desc, '0, clk_i, rst_ni)
  `FFLARN(busy_q, busy_d, load_busy, '0, clk_i, rst_ni)
endmodule
