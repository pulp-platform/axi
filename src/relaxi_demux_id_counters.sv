// Copyright 2026 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Author: Chaoqun Liang <chaoqun.liang@unibo.it>

`include "common_cells/registers.svh"

module relaxi_demux_id_counters #(
  // the lower bits of the AXI ID that should be considered, results in 2**AXI_ID_BITS counters
  parameter int unsigned AxiIdBits         = 2,
  parameter int unsigned CounterWidth      = 4,
  parameter type         mst_port_select_t = logic
) (
  input  logic                    clk_i,   // Clock
  input  logic                    rst_ni,  // Asynchronous reset active low
  // lookup
  input  logic   [2:0][AxiIdBits-1:0]  lookup_axi_id_i,
  output mst_port_select_t  [2:0] lookup_mst_select_o,
  output logic              [2:0] lookup_mst_select_occupied_o,
  // push
  output logic              [2:0] full_o,
  input  logic   [2:0][AxiIdBits-1:0]  push_axi_id_i,
  input  mst_port_select_t  [2:0] push_mst_select_i,
  input  logic   [2:0]            push_i,
  // inject ATOPs in AR channel
  input  logic   [2:0][AxiIdBits-1:0]  inject_axi_id_i,
  input  logic   [2:0]            inject_i,
  // pop
  input  logic   [2:0][AxiIdBits-1:0]  pop_axi_id_i,
  input  logic   [2:0]            pop_i,
  // outstanding transactions
  output logic                    any_outstanding_trx_o,
  // fault detection
  output logic                    fault_o
);

  localparam int unsigned NoCounters = 2**AxiIdBits;
  typedef logic [CounterWidth-1:0] cnt_t;

  // registers, each gets loaded when push_en[i]
  // TMR registers for mst_select: 3 replicas x NoCounters entries
  mst_port_select_t [2:0][NoCounters-1:0] mst_select_q;
  mst_port_select_t [2:0][NoCounters-1:0] mst_select_voted;

  // per-replica counter status: [replica][counter_id]
  logic [2:0][NoCounters-1:0] occupied;
  logic [2:0][NoCounters-1:0] cnt_full;

  // per-counter fault signals from rel_delta_counter
  logic [NoCounters-1:0] cnt_fault;
  logic [NoCounters-1:0] sel_fault;
  logic [NoCounters-1:0] ovf_fault;
  // control signals
  logic [2:0][NoCounters-1:0] push_en, inject_en, pop_en;

  //-----------------------------------
  // Push and Pop
  //-----------------------------------
  for (genvar i = 0; i < 3; i++) begin : gen_enables
    assign push_en[i]   = push_i[i]   ? (1 << push_axi_id_i[i])   : '0;
    assign inject_en[i] = inject_i[i] ? (1 << inject_axi_id_i[i]) : '0;
    assign pop_en[i]    = pop_i[i]    ? (1 << pop_axi_id_i[i])    : '0;
  end

  //-----------------------------------
  // Lookup
  //-----------------------------------
  for (genvar i = 0; i < 3; i++) begin : gen_lookup_out
    assign lookup_mst_select_o[i]          = mst_select_voted[i][lookup_axi_id_i[i]];
    assign lookup_mst_select_occupied_o[i] = occupied[i][lookup_axi_id_i[i]];
  end

  //------------------------------------------------------------------
  // Full output
  //------------------------------------------------------------------
  for (genvar i = 0; i < 3; i++) begin : gen_full
    assign full_o[i] = |cnt_full[i];
  end

  //-----------------------------------
  // Status
  //-----------------------------------
  logic [2:0] any_outstanding;
  logic outstand_fault;

  for (genvar r = 0; r < 3; r++) begin : gen_outstanding
    assign any_outstanding[r] = |occupied[r];
  end

  TMR_voter_fail i_any_outstanding_vote (
    .a_i              ( any_outstanding[0] ),
    .b_i              ( any_outstanding[1] ),
    .c_i              ( any_outstanding[2] ),
    .majority_o       ( any_outstanding_trx_o  ),
    .fault_detected_o ( outstand_fault         )
  );

  assign fault_o = outstand_fault | |cnt_fault | |ovf_fault | |sel_fault;

  // counters
  for (genvar i = 0; i < NoCounters; i++) begin : gen_counters
    logic [2:0]                   cnt_en;
    logic [2:0]                   cnt_down;
    cnt_t [2:0]                   cnt_delta;
    logic                         ovf_flt;

    for (genvar r = 0; r < 3; r++) begin : gen_cnt_delta_tmr
      always_comb begin
        unique case ({push_en[r][i], inject_en[r][i], pop_en[r][i]})
          3'b110  : cnt_delta[r] = cnt_t'(2); // push+inject = +2
          default : cnt_delta[r] = cnt_t'(1); // any single op = 1
        endcase
      end
    end

    for (genvar r = 0; r < 3; r++) begin : gen_cnt_ctrl
      always_comb begin
        unique case ({push_en[r][i], inject_en[r][i], pop_en[r][i]})
          3'b001  : begin cnt_en[r] = 1'b1; cnt_down[r] = 1'b1; end // pop only
          3'b010  : begin cnt_en[r] = 1'b1; cnt_down[r] = 1'b0; end // inject only
          3'b100  : begin cnt_en[r] = 1'b1; cnt_down[r] = 1'b0; end // push only
          3'b110  : begin cnt_en[r] = 1'b1; cnt_down[r] = 1'b0; end // push+inject
          3'b111  : begin cnt_en[r] = 1'b1; cnt_down[r] = 1'b0; end // push+inject+pop
          default : begin cnt_en[r] = 1'b0; cnt_down[r] = 1'b0; end // no-op
        endcase
      end
    end

    logic [2:0][CounterWidth-1:0] in_flight;
    logic [2:0]                   overflow;

    rel_delta_counter #(
      .WIDTH           ( CounterWidth ),
      .STICKY_OVERFLOW ( 1'b0         ),
      .TmrStatus       ( 1'b1         )
    ) i_in_flight_cnt (
      .clk_i      ( clk_i       ),
      .rst_ni     ( rst_ni      ),
      .clear_i    ( 3'b000      ),
      .en_i       ( cnt_en      ),
      .load_i     ( 3'b000      ),
      .down_i     ( cnt_down    ), // prim fault, at both primitive input and output
      .delta_i    ( cnt_delta   ),
      .d_i        ( '0          ),
      .q_o        ( in_flight   ),
      .overflow_o ( overflow    ),
      .fault_o    ( cnt_fault[i] )
    );

    // Per-replica occupied and cnt_full
    for (genvar j = 0; j < 3; j++) begin : gen_replica_status
      assign occupied[j][i] = |in_flight[j];
      assign cnt_full[j][i] = overflow[j] | (&in_flight[j]);
    end

    logic             [2:0] sel_fault_slot;

    for (genvar r = 0; r < 3; r++) begin : gen_mst_select_tmr
      bitwise_TMR_voter_fail #(
        .DataWidth ( $bits(mst_port_select_t) )
      ) i_sel_vote (
        .a_i              ( mst_select_q[r][i]       ),
        .b_i              ( mst_select_q[(r+1)%3][i] ),
        .c_i              ( mst_select_q[(r+2)%3][i] ),
        .majority_o       ( mst_select_voted[r][i]   ),
        .fault_detected_o ( sel_fault_slot[r]        )
      );

      always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni)            mst_select_q[r][i] <= '0;
        else if (push_en[r][i]) mst_select_q[r][i] <= push_mst_select_i[r];
        else                    mst_select_q[r][i] <= mst_select_voted[r][i];
      end
    end

    assign sel_fault[i] = |sel_fault_slot;

    logic ovf_voted;
    TMR_voter_fail i_overflow_vote_rep (
      .a_i              ( overflow[0] ),
      .b_i              ( overflow[1] ),
      .c_i              ( overflow[2] ),
      .majority_o       ( ovf_voted   ),   // majority not needed here
      .fault_detected_o ( ovf_flt     )
    );
    assign ovf_fault[i] = ovf_flt;

// Then the assertion (gated, consistency-aware), reusing the real voted overflow:
// pragma translate_off
`ifndef FAULTSIM
`ifndef VERILATOR
`ifndef XSIM
    // pop_en replica consistency (TMR invariant)
    pop_en_consistent: assert property(@(posedge clk_i) disable iff (~rst_ni)
      (pop_en[0][i] == pop_en[1][i]) && (pop_en[1][i] == pop_en[2][i])) else
      $fatal(1, "id_counter %0d: pop_en replicas diverged (TMR inconsistency).", i);

    // underflow check on the voted overflow (not a separate sim-only voter)
    cnt_underflow: assert property(@(posedge clk_i) disable iff (~rst_ni)
      (pop_en[0][i] |=> !ovf_voted)) else
      $fatal(1, "id_counter %0d underflowed (likely faulty AXI response).", i);
`endif
`endif
`endif
// pragma translate_on
  end
endmodule
