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
// File:   llc_merge_unit.sv
// Author: Wolfgang Roenninger <wroennin@student.ethz.ch>
// Date:   12.06.2019
//
// Description: This module merges the descriptor streams form the bypass and the eviction/refill
//              pipeline. It distributes the descriptors to the read and write unit.
//              It also notifies the counter unit in the hit_miss that a descriptor left the
//              eviction/refill pipeline.
//              The struct cnt_t has to be defined as follows (done in `axi_llc_top`):
//              typedef struct packed {
//                 axi_slv_id_t id;     // Axi ID of the count operation
//                 logic        rw;     // 0: read, 1: write
//                 logic        valid;  // valid, equals enable
//               } cnt_t;

module axi_llc_merge_unit #(
  parameter axi_llc_pkg::llc_cfg_t    Cfg = -1,
  parameter type                   desc_t = logic,
  parameter type                    cnt_t = logic
) (
  input  logic  clk_i,   // Clock
  input  logic  rst_ni,  // Asynchronous reset active low
  // input from bypass
  input  desc_t bypass_desc_i,
  input  logic  bypass_valid_i,
  output logic  bypass_ready_o,
  // input from eviction / refill pipeline
  input  desc_t refill_desc_i,
  input  logic  refill_valid_i,
  output logic  refill_ready_o,
  // output to read unit
  output desc_t read_desc_o,
  output logic  read_valid_o,
  input  logic  read_ready_i,
  // output to write unit
  output desc_t write_desc_o,
  output logic  write_valid_o,
  input  logic  write_ready_i,
  // output to the miss counters in the hit miss unit
  output cnt_t  cnt_down_o // a descriptor leaves the evict refill pipeline
);

  // signal definitions
  logic  [1:0] bypass_valid, bypass_ready;
  logic  [1:0] refill_valid, refill_ready;
  logic  [1:0] w_tree_valid, w_tree_ready;
  logic  [1:0] r_tree_valid, r_tree_ready;
  desc_t [1:0] tree_desc;

  // count down output towards the miss counters
  // enable cnt_down_o if there is a transfer from the pipeline
  assign cnt_down_o.id    = refill_desc_i.a_x_id;
  assign cnt_down_o.rw    = refill_desc_i.rw;
  assign cnt_down_o.valid = refill_valid_i & refill_ready_o;

  // valid ready signal demux
  stream_demux #(
    .N_OUP    (2)
  ) i_bypass_demux (
    .inp_valid_i (   bypass_valid_i ),
    .inp_ready_o (   bypass_ready_o ),
    .oup_sel_i   ( bypass_desc_i.rw ),
    .oup_valid_o (     bypass_valid ),
    .oup_ready_i (     bypass_ready )
  );

  stream_demux #(
    .N_OUP    (2)
  ) i_pipeline_demux (
    .inp_valid_i (   refill_valid_i ),
    .inp_ready_o (   refill_ready_o ),
    .oup_sel_i   ( refill_desc_i.rw ),
    .oup_valid_o (     refill_valid ),
    .oup_ready_i (     refill_ready )
  );

  // descriptor distribution
  assign tree_desc[1] = bypass_desc_i;
  assign tree_desc[0] = refill_desc_i;

  // butterfly of the valid signals
  assign w_tree_valid[1] = bypass_valid[1];
  assign w_tree_valid[0] = refill_valid[1];
  assign r_tree_valid[1] = bypass_valid[0];
  assign r_tree_valid[0] = refill_valid[0];
  // butterfly of the ready signals
  assign bypass_ready[1] = w_tree_ready[1];
  assign bypass_ready[0] = r_tree_ready[1];
  assign refill_ready[1] = w_tree_ready[0];
  assign refill_ready[0] = r_tree_ready[0];

  rr_arb_tree #(
    .NumIn     (          2 ),
    .DataType  (  desc_t ),
    .AxiVldRdy (       1'b1 )
  ) i_write_arb_tree (
    .clk_i  (         clk_i ),
    .rst_ni (        rst_ni ),
    .flush_i(            '0 ),
    .rr_i   (            '0 ),
    .req_i  (  w_tree_valid ),
    .gnt_o  (  w_tree_ready ),
    .data_i (     tree_desc ),
    .gnt_i  ( write_ready_i ),
    .req_o  ( write_valid_o ),
    .data_o (  write_desc_o ),
    .idx_o  ()
  );

  rr_arb_tree #(
    .NumIn    (          2 ),
    .DataType (  desc_t ),
    .AxiVldRdy(       1'b1 )
  ) i_read_arb_tree (
    .clk_i  (        clk_i ),
    .rst_ni (       rst_ni ),
    .flush_i(           '0 ),
    .rr_i   (           '0 ),
    .req_i  ( r_tree_valid ),
    .gnt_o  ( r_tree_ready ),
    .data_i (    tree_desc ),
    .gnt_i  ( read_ready_i ),
    .req_o  ( read_valid_o ),
    .data_o (  read_desc_o ),
    .idx_o  ()
  );
endmodule
