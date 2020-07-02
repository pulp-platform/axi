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
// File:   tag_pattern_gen.sv
// Author: Wolfgang Roenninger <wroennin@iis.ee.ethz.ch>
// Date:   11.06.2019

/// This is the Tag generation for the LLC.
/// Initialize the tag storage to a known value of all 0 using a march X
/// BIST algorithm.
//
//              tag_t is shown, however fields do not mater as they are written with either '0 or '1
//              typedef struct packed {
//                logic                     val; // tag valid flag
//                logic                     dit; // tag dirty flag
//                logic [Cfg.TagLength-1:0] tag; // tag itself
//              } pattern_t;
module axi_llc_tag_pattern_gen #(
  /// Stattic LLC configuration struct.
  parameter axi_llc_pkg::llc_cfg_t Cfg = axi_llc_pkg::llc_cfg_t'{default: '0},
  /// Pattern type for generation.
  parameter type pattern_t = logic,
  /// Way indicator type. Each way is checked indiviually. Bit position id the index of the way.
  parameter type way_ind_t = logic,
  /// Cache line index type (macro address).
  parameter type index_t   = logic
) (
  /// Clock, positive edge triggered.
  input  logic     clk_i,
  /// Asynchronous reset, active low.
  input  logic     rst_ni,
  /// Valid request to start BIST.
  input  logic     valid_i,
  /// Module is ready to start BIST.
  output logic     ready_o,
  /// Pattern address for SRAM.
  output index_t   index_o,
  /// Output pattern.
  output pattern_t pattern_o,
  /// Request signal for the tag sram.
  output logic     req_o,
  /// Write enable for tag sram.
  output logic     we_o,
  /// Individual BIST comparison results.
  input  way_ind_t bist_res_i,
  /// `bist_res_i` is valid.
  input  logic     bist_res_valid_i,
  /// Aggregated output of bist.
  output way_ind_t bist_res_o,
  /// End of computation.
  output logic     eoc_o
);
  `include "common_cells/registers.svh"
  // Define the width of the pattern for assignment of bits.
  localparam int unsigned PatternWidth = unsigned'($bits(pattern_t));

  // unit status
  logic         busy_d, busy_q, switch_busy;
  // BIST state implements March X
  typedef enum logic [3:0] {
    WZEROUP, RZEROUP, WONEUP, RONEDOWN, WZERODOWN, RZERODOWN, BISTEND
  } bist_e;
  bist_e                           bist_d,      bist_q;
  logic                            update_bist;
  // counter signals (control)
  logic                            clear_cnt,   en_cnt, load_cnt, down_cnt, overflow_cnt;
  logic [Cfg.IndexLength-1:0]      data_cnt;
  // bist result flipflop and
  logic [Cfg.SetAssociativity-1:0] bist_res_d,  bist_res_q;
  logic                            error_bist;

  // assign the bist error flag
  assign error_bist = bist_res_valid_i & ~(&bist_res_i);
  // bist output assignment
  assign bist_res_o = bist_res_q;

  always_comb begin
    // default assignments
    busy_d      = busy_q;
    switch_busy = 1'b0;
    bist_d      = bist_q;
    update_bist = 1'b0;
    ready_o     = 1'b0;
    req_o       = 1'b0;
    we_o        = 1'b0;
    eoc_o       = 1'b0;
    // counter signals
    clear_cnt   = 1'b0;
    en_cnt      = 1'b0;
    load_cnt    = 1'b0; // will be used for BIST
    data_cnt    = '0;
    down_cnt    = 1'b0; // will be used for BIST
    // pattern to write (for now all zeros)
    pattern_o   = pattern_t'{default: '0};
    // bist result
    bist_res_d  = bist_res_q;

    // count and react according to BIST status
    if (busy_q) begin
      case (bist_q)
        // write all zeros counting up
        WZEROUP   : begin
          if (overflow_cnt) begin
            clear_cnt   = 1'b1;
            bist_d      = RZEROUP;
            update_bist = 1'b1;
          end else begin
            req_o  = 1'b1;
            we_o   = 1'b1;
            en_cnt = 1'b1;
          end
        end
        // read out all zeros counting up
        RZEROUP   : begin
          if (overflow_cnt) begin
            clear_cnt   = 1'b1;
            bist_d      = WONEUP;
            update_bist = 1'b1;
          end else begin
            req_o  = 1'b1;
            en_cnt = 1'b1;
          end
          // do checking of the bist result gets only saved, if one of the bist_res_i is zero
          bist_res_d = bist_res_q & bist_res_i;
        end
        // write all ones counting up
        WONEUP    : begin
          if (overflow_cnt) begin
            load_cnt    = 1'b1;
            data_cnt    = '1;
            bist_d      = RONEDOWN;
            update_bist = 1'b1;
          end else begin
            req_o     = 1'b1;
            we_o      = 1'b1;
            pattern_o = {PatternWidth{1'b1}};
            en_cnt    = 1'b1;
          end
        end
        // read out all ones counting down
        RONEDOWN  : begin
          if (overflow_cnt) begin
            load_cnt    = 1'b1;
            data_cnt    = '1;
            bist_d      = WZERODOWN;
            update_bist = 1'b1;
          end else begin
            req_o     = 1'b1;
            pattern_o = {PatternWidth{1'b1}};
            en_cnt    = 1'b1;
            down_cnt  = 1'b1;
          end
        end
        // write all zeros counting down
        WZERODOWN : begin
          if (overflow_cnt) begin
            load_cnt    = 1'b1;
            data_cnt    = '1;
            bist_d      = RZERODOWN;
            update_bist = 1'b1;
          end else begin
            req_o    = 1'b1;
            we_o     = 1'b1;
            en_cnt   = 1'b1;
            down_cnt = 1'b1;
          end
        end
        // read all zeros counting down
        RZERODOWN : begin
          if (overflow_cnt) begin
            clear_cnt   = 1'b1;
            bist_d      = BISTEND;
            update_bist = 1'b1;
          end else begin
            req_o         = 1'b1;
            en_cnt        = 1'b1;
            down_cnt      = 1'b1;
          end
        end
        BISTEND   : begin
          bist_d      = WZEROUP;
          update_bist = 1'b1;
          eoc_o       = 1'b1;
          busy_d      = 1'b0;
          switch_busy = 1'b1;
        end
        default : ; // not possible to come here
      endcase

    // we are ready to get a new request
    end else begin
      ready_o     = 1'b1;
      // start operation
      if (valid_i) begin
        // start bist
        busy_d      = 1'b1;
        switch_busy = 1'b1;
        clear_cnt   = 1'b1;
      end
    end
  end

  counter #(
    .WIDTH     ( Cfg.IndexLength )
  ) i_index_cnt (
    .clk_i     (        clk_i ),
    .rst_ni    (       rst_ni ),
    .clear_i   (    clear_cnt ),
    .en_i      (       en_cnt ),
    .load_i    (     load_cnt ),
    .down_i    (     down_cnt ),
    .d_i       (     data_cnt ),
    .q_o       (      index_o ),
    .overflow_o( overflow_cnt )
  );

  // Flip Flops
  `FFLARN(busy_q,     busy_d,     switch_busy,      '0, clk_i, rst_ni)
  `FFLARN(bist_q,     bist_d,     update_bist, WZEROUP, clk_i, rst_ni)
  `FFLARN(bist_res_q, bist_res_d, error_bist,       '0, clk_i, rst_ni)
endmodule
