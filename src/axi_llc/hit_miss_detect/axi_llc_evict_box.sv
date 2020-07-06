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
// File:   axi_llc_evict_box.sv
// Author: Wolfgang Roenninger <wroennin@iis.ee.ethz.ch>
// Date:   06.06.2019

/// Determines from the valid and spm lock signals, on which way the eviction
/// operation should be performed on, also tells us if we should write back the
/// data located at the old tag to the memory. It uses a counter which
/// advances every clock cycle for pseudo randomness as eviction strategy.
module axi_llc_evict_box #(
  /// Static configuration parameters of the LLC.
  parameter axi_llc_pkg::llc_cfg_t Cfg = axi_llc_pkg::llc_cfg_t'{default: '0},
  /// Way indicator type. This segnal has the width equal to the set-associativity.
  parameter type way_ind_t = logic
) (
  /// Clock, positive edge triggered.
  input  logic clk_i,
  /// Asynchronous reset, active low.
  input  logic rst_ni,
  /// Request to the eviction unit, has to be high so that valid is eventually set.
  input  logic req_i,
  /// All valid tags as input. This indicates if there are still free ways for putting in data.
  input  way_ind_t tag_valid_i,
  /// All dirty flags as input. This indicates us if we have to write back the data.
  input  way_ind_t tag_dirty_i,
  /// All SPM configured ways. So that the output indicator does not point to a SPM way.
  input  way_ind_t spm_lock_i,
  /// Way indicator for action to be performed. Is a onehot signal.
  output way_ind_t way_ind_o,
  /// Evict the line.
  output logic evict_o,
  /// Output is valid. This signal will eventually go to high if `req_i` is 1.
  output logic valid_o
);
  `include "common_cells/registers.svh"
  // Mask which tells us which way have something in them (valid or spm)
  way_ind_t occupied;
  logic     en_cnt;                     // enables the counter for 'randomness'
  way_ind_t onehot_ind_q, onehot_ind_d; // counter output converted to onehot

  assign occupied = tag_valid_i | spm_lock_i;
  // hold the output (stop the counter) if we have a request and we have valid output
  assign en_cnt   = ~(req_i && valid_o);

  // determine on which way the operation should go
  always_comb begin
    // default assignments
    way_ind_o = '0;   // output silence
    valid_o   = 1'b0; // output is valid
    evict_o   = 1'b0; // we have to evict the old tag, because it is dirty

    // differentiate between all occupied or some ways still empty
    // we only have to evict something, if
    // all ways full, evict something
    if (req_i) begin
      // all ways have something in them, evict a not spm way
      if (occupied == '1) begin
        if ((spm_lock_i & onehot_ind_q) == '0) begin
          way_ind_o = onehot_ind_q;
          valid_o   = 1'b1;
          // check if we have to evict the old tag, it is dirty
          if ((tag_dirty_i & onehot_ind_q) != '0) begin
            evict_o = 1'b1;
          end
        end
      // we have ways to fill, pick a random one
      end else begin
        if ((occupied & onehot_ind_q) == '0) begin
          way_ind_o = onehot_ind_q;
          valid_o   = 1'b1;
        end
      end
    end
  end

  // Shift register to generate 'randomness' the counter is enabled as long as `valid_o` is not set.
  if (Cfg.SetAssociativity > 32'd1) begin : gen_counter
    // A shift register where a 1 runs around
    for (genvar i = 0; unsigned'(i) < Cfg.SetAssociativity; i++) begin : gen_shift
      if (unsigned'(i) == 32'd0) begin : gen_first
        `FFLARN(onehot_ind_q[i], onehot_ind_d[i], en_cnt, 1'b1, clk_i, rst_ni)
        assign onehot_ind_d[Cfg.SetAssociativity-1] = onehot_ind_q[i];
      end else begin : gen_others
        `FFLARN(onehot_ind_q[i], onehot_ind_d[i], en_cnt, 1'b0, clk_i, rst_ni)
        assign onehot_ind_d[i-1] = onehot_ind_q[i];
      end
    end
  end else begin : gen_no_counter
    assign onehot_ind_q = 1'b1;
  end

  // check if the output really is onehot
  // pragma translate_off
  `ifndef VERILATOR
  check_onehot: assert property ( @(posedge clk_i) disable iff (~rst_ni) $onehot0(way_ind_o)) else
      $fatal(1, "More than two bit set in the one-hot signal");
  `endif
  // pragma translate_on
endmodule
