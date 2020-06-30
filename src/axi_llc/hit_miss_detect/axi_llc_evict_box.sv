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
// Author: Wolfgang Roenninger <wroennin@student.ethz.ch>
// Date:   06.06.2019
//
// Description: Determines from the valid and spm lock signals, on which way the eviction
//              operation should be performed on, also tells us if we should write back the
//              data located at the old tag to the memory. It uses a counter which
//              advances every clock cycle for pseudo randomness as eviction strategy.

module axi_llc_evict_box #(
  parameter axi_llc_pkg::llc_cfg_t Cfg = -1
) (
  input  logic clk_i,                                  // Clock
  input  logic rst_ni,                                 // Asynchronous reset active low
  input  logic                            req_i,       // request an output
  input  logic [Cfg.SetAssociativity-1:0] tag_valid_i, // all valid tags as input -> free pace
  input  logic [Cfg.SetAssociativity-1:0] tag_dirty_i, // all dirty tags as input -> eviction?
  input  logic [Cfg.SetAssociativity-1:0] spm_lock_i,  // is the way configured for SPM

  output logic [Cfg.SetAssociativity-1:0] way_ind_o,   // way indicator for action to be performed
  output logic                            evict_o,     // evict the line
  output logic                            valid_o      // output is valid
);

  // Mask which tells us which way have something in them (valid or spm)
  logic [Cfg.SetAssociativity-1:0]          occupied;
  logic                                     en_cnt;     // enables the counter for 'randomness'
  logic [$clog2(Cfg.SetAssociativity)-1:0]  bin_ind;    // output from the counter
  logic [Cfg.SetAssociativity-1:0]          onehot_ind; // counter output converted to onehot

  assign occupied = tag_valid_i | spm_lock_i;
  // hold the output (stop the counter) if we have a request and we have valid output
  assign en_cnt   = ~(req_i && valid_o);

  // determine on which way the operation should go
  always_comb begin
    // default assignments
    way_ind_o = '0;   // output silence
    valid_o   = 1'b0; // ouput is valid
    evict_o   = 1'b0; // we have to evict the old tag, because it is dirty

    // differentiate between all occupoed or some ways still empty
    // we only have to evict something, if
    // all ways full, evict something
    if (req_i) begin
      // all ways have something in them, evict a not spm way
      if (occupied == '1) begin
        if ((spm_lock_i & onehot_ind) == '0) begin
          way_ind_o = onehot_ind;
          valid_o   = 1'b1;
          // check if we have to evict the old tag, it is dirty
          if ((tag_dirty_i & onehot_ind) != '0) begin
            evict_o = 1'b1;
          end
        end
      //we have ways to fill, pick a random one
      end else begin
        if ((occupied & onehot_ind) == '0) begin
          way_ind_o = onehot_ind;
          valid_o   = 1'b1;
        end
      end
    end
  end

  // counter to generate 'randomness'
  // we do not care about the overflow, because we want to wrap around
  counter #(
    .WIDTH ( $clog2(Cfg.SetAssociativity) )
  ) i_way_counter (
    .clk_i      (   clk_i ),
    .rst_ni     (  rst_ni ),
    .clear_i    (    1'b0 ),
    .en_i       (  en_cnt ),
    .load_i     (    1'b0 ),
    .down_i     (    1'b0 ),
    .d_i        (      '0 ),
    .q_o        ( bin_ind ),
    .overflow_o (         )
  );

  // convert counter output to onehot
  always_comb begin
    onehot_ind = '0;
    for (int unsigned i = 0; i < Cfg.SetAssociativity; i++) begin
      if (bin_ind == i) begin
        onehot_ind[i] = 1'b1;
      end
    end
  end

  // check if the output really is onehot
  // pragma translate_off
  `ifndef VERILATOR
  `ifndef VCS
  `ifndef SYNTHESIS
  check_onehot: assert property ( @(posedge clk_i) disable iff (~rst_ni) $onehot0(way_ind_o)) else
      $fatal(1, "More than two bit set in the one-hot signal");
  check_all_spm:    assert property ( @(posedge clk_i) disable iff (~rst_ni)
                                 ((spm_lock_i == '1) |-> (req_i == 1'b0))) else
      $fatal(1, "Should not have a request, if all ways are spm!");
  `endif
  `endif
  `endif
  // pragma translate_on
endmodule
