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

`include "common_cells/assertions.svh"
`include "common_cells/registers.svh"
`include "axi/assign.svh"

`ifdef QUESTA
// Derive `TARGET_VSIM`, which is used for tool-specific workarounds in this file, from `QUESTA`,
// which is automatically set in Questa.
`define TARGET_VSIM
`endif

/// Demultiplex one AXI4+ATOP slave port to multiple AXI4+ATOP master ports.
///
/// The AW and AR slave channels each have a `select` input to determine to which master port the
/// current request is sent.  The `select` can, for example, be driven by an address decoding module
/// to map address ranges to different AXI slaves.
///
/// ## Design overview
///
/// ![Block diagram](module.axi_demux.png "Block diagram")
///
/// Beats on the W channel are routed by demultiplexer according to the selection for the
/// corresponding AW beat.  This relies on the AXI property that W bursts must be sent in the same
/// order as AW beats and beats from different W bursts may not be interleaved.
///
/// Beats on the B and R channel are multiplexed from the master ports to the slave port with
/// a round-robin arbitration tree.
module relaxi_demux_simple #(
  parameter int unsigned AxiIdWidth     = 32'd0,
  parameter bit          AtopSupport    = 1'b1,
  parameter type         axi_req_t      = logic,
  parameter type         axi_resp_t     = logic,
  parameter int unsigned NoMstPorts     = 32'd0,
  parameter int unsigned MaxTrans       = 32'd8,
  parameter int unsigned AxiLookBits    = 32'd3,
  parameter bit          UniqueIds      = 1'b0,
  // Dependent parameters, DO NOT OVERRIDE!
  parameter int unsigned SelectWidth    = (NoMstPorts > 32'd1) ? $clog2(NoMstPorts) : 32'd1,
  parameter type         select_t       = logic [SelectWidth-1:0]
) (
  input  logic                          clk_i,
  input  logic                          rst_ni,
  input  logic                          test_i,
  // Slave Port
  input  axi_req_t                      slv_req_i,
  input  select_t     [2:0]             slv_aw_select_i,
  input  select_t     [2:0]             slv_ar_select_i,
  output axi_resp_t                     slv_resp_o,
  // Master Ports
  output axi_req_t    [NoMstPorts-1:0]  mst_reqs_o,
  input  axi_resp_t   [NoMstPorts-1:0]  mst_resps_i,

  input  logic [2:0][AxiIdWidth-1:0]    slv_aw_id_corr_i,
  input  logic [2:0][AxiIdWidth-1:0]    slv_ar_id_corr_i,

  output logic [1:0]                    fault_o
);

  localparam int unsigned IdCounterWidth = cf_math_pkg::idx_width(MaxTrans);
  typedef logic [IdCounterWidth-1:0] id_cnt_t;

  logic [2:0][AxiLookBits-1:0] b_pop_id;
  logic [2:0][cf_math_pkg::idx_width(NoMstPorts)-1:0] b_idx;

  logic [2:0][AxiLookBits-1:0] r_pop_id;
  logic [2:0][cf_math_pkg::idx_width(NoMstPorts)-1:0] r_idx;

  localparam int unsigned IdxW = cf_math_pkg::idx_width(NoMstPorts);

  logic            b_idx_oor,        r_idx_oor;
  logic b_valid_fault, r_valid_fault;

  localparam int unsigned BChanBits = $bits(mst_resps_i[0].b);
  localparam int unsigned RChanBits = $bits(mst_resps_i[0].r);

  logic [2:0][IdxW-1:0]      b_idx_g, r_idx_g;
  logic [2:0][BChanBits-1:0] b_payload_raw;
  logic [2:0][RChanBits-1:0] r_payload_raw;
  logic [BChanBits-1:0]      b_payload, b_payload_faults;
  logic [RChanBits-1:0]      r_payload, r_payload_faults;

  logic [2:0] b_oor_raw, r_oor_raw;
  for (genvar i = 0; i < 3; i++) begin : gen_idx_clamp
    assign b_oor_raw[i] = (b_idx[i] >= NoMstPorts);
    assign r_oor_raw[i] = (r_idx[i] >= NoMstPorts);
    assign b_idx_g[i]   = b_oor_raw[i] ? '0 : b_idx[i];
    assign r_idx_g[i]   = r_oor_raw[i] ? '0 : r_idx[i];
  end

  localparam int unsigned NumFaults = 12;// Update if more faults are added
  logic [NumFaults-1:0] faults;          // corrected-class only
  logic [1:0]           pop_id_fault;    // [0] corrected, [1] uncorrectable

  assign fault_o[0] = |faults | pop_id_fault[0];
  assign fault_o[1] = pop_id_fault[1] | b_idx_oor | r_idx_oor;

  logic [2:0][AxiLookBits-1:0] aw_lookup_id, ar_lookup_id;
  for (genvar i = 0; i < 3; i++) begin : gen_lookup_slice
    assign aw_lookup_id[i] = slv_aw_id_corr_i[i][0+:AxiLookBits];
    assign ar_lookup_id[i] = slv_ar_id_corr_i[i][0+:AxiLookBits];
  end

  // pass through if only one master port
  if (NoMstPorts == 32'h1) begin : gen_no_demux
    `AXI_ASSIGN_REQ_STRUCT(mst_reqs_o[0], slv_req_i)
    `AXI_ASSIGN_RESP_STRUCT(slv_resp_o, mst_resps_i[0])
    assign faults = '0;
    assign pop_id_fault = 2'b00;
    assign b_idx_oor   = 1'b0;
    assign r_idx_oor   = 1'b0;
  end else begin : gen_demux

    //--------------------------------------
    //--------------------------------------
    // Signal Declarations
    //--------------------------------------
    //--------------------------------------

    //--------------------------------------
    // Write Transaction
    //--------------------------------------

    // Register which locks the AW valid signal
    logic  [2:0]              lock_aw_valid_d, lock_aw_valid_q, lock_aw_valid_next, load_aw_lock;
    logic  [2:0]              aw_valid, aw_ready;
    logic  [2:0][1:0]         alt_lock_aw_valid;

    // AW ID counter
    select_t  [2:0]                lookup_aw_select;
    logic     [2:0]                aw_select_occupied, aw_id_cnt_full;
    // Upon an ATOP load, inject IDs from the AW into the AR channel
    logic     [2:0]                atop_inject;

    // W select counter: stores the decision to which master W beats should go
    select_t   [2:0]               w_select,           w_select_q, w_select_next;
    select_t   [2:0][1:0]          alt_w_select;
    logic      [2:0]               w_select_valid;
    id_cnt_t   [2:0]               w_open;
    logic      [2:0]               w_cnt_up,           w_cnt_down;

    // B channles input into the arbitration
    logic    [NoMstPorts-1:0][2:0] mst_b_valids,       mst_b_readies;
    // Flat intermediates: avoid Questa optimizer crash on multi-dim packed connections

    //--------------------------------------
    // Read Transaction
    //--------------------------------------
    // 3 replcias x 2 alternatives
    logic     [2:0][1:0]          alt_lock_ar_valid;
    // AR ID counter
    select_t  [2:0]               lookup_ar_select;
    logic     [2:0]               ar_select_occupied, ar_id_cnt_full;
    logic     [2:0]               ar_push;

    // Register which locks the AR valid signal
    logic     [2:0]              lock_ar_valid_d, lock_ar_valid_q, load_ar_lock, lock_ar_valid_next;
    logic     [2:0]              ar_valid,        ar_ready;

    logic     [NoMstPorts-1:0][2:0] mst_r_valids, mst_r_readies;

    // Intermediates: avoid LHS bit-select into struct fields (Questa vopt-13198).
    logic [2:0] slv_aw_valid_d, slv_aw_ready_d;
    logic [2:0] slv_ar_valid_d, slv_ar_ready_d;
    logic [2:0] slv_w_ready_d;
    logic [2:0] slv_b_valid_d;
    logic [2:0] slv_r_valid_d;
    logic [NoMstPorts-1:0][2:0] mst_aw_ready_d, mst_ar_ready_d;
    logic [NoMstPorts-1:0][2:0] mst_aw_valid_d;
    logic [NoMstPorts-1:0][2:0] mst_b_ready_d;
    logic [NoMstPorts-1:0][2:0] mst_b_valid_d, mst_r_valid_d;

    logic [2:0] lock_aw_faults, w_sel_faults, lock_ar_faults;
    logic       aw_idcnt_fault, ar_idcnt_fault, b_arb_fault, r_arb_fault;
    logic       open_w_fault;

    assign faults[0] = |lock_aw_faults;   // AW lock voters (3 replicas)
    assign faults[1] = |w_sel_faults;     // W-select voters (3 replicas)
    assign faults[2] = |lock_ar_faults;   // AR lock voters (3 replicas)
    assign faults[3] = aw_idcnt_fault;    // AW id counter
    assign faults[4] = ar_idcnt_fault;    // AR id counter
    assign faults[5] = b_arb_fault;       // B response arbiter
    assign faults[6] = r_arb_fault;       // R response arbiter
    assign faults[7] = open_w_fault;      // the rel_counter

    assign slv_aw_valid_d      = slv_req_i.aw_valid;
    assign slv_resp_o.aw_ready = slv_aw_ready_d;
    assign slv_ar_valid_d      = slv_req_i.ar_valid;
    assign slv_resp_o.ar_ready = slv_ar_ready_d;
    assign slv_resp_o.w_ready  = slv_w_ready_d;
    assign slv_resp_o.b_valid  = slv_b_valid_d;
    assign slv_resp_o.r_valid  = slv_r_valid_d;

    logic [2:0] slv_b_ready_d, slv_r_ready_d;
    assign slv_b_ready_d = slv_req_i.b_ready;
    assign slv_r_ready_d = slv_req_i.r_ready;

    logic [2:0] b_pop, r_pop;
    assign b_pop = slv_b_valid_d & slv_b_ready_d;

    logic [2:0] b_oor_gated, r_oor_gated;
    logic       b_oor_div,   r_oor_div;

    for (genvar i = 0; i < 3; i++) begin : gen_oor_gate
      assign b_oor_gated[i] = slv_b_valid_d[i] & b_oor_raw[i];
      assign r_oor_gated[i] = slv_r_valid_d[i] & r_oor_raw[i];
    end

    TMR_voter_fail #(.VoterType(1)) i_b_oor_vote (
      .a_i              ( b_oor_gated[0] ),
      .b_i              ( b_oor_gated[1] ),
      .c_i              ( b_oor_gated[2] ),
      .majority_o       ( b_idx_oor      ),
      .fault_detected_o ( b_oor_div      )
    );

    TMR_voter_fail #(.VoterType(1)) i_r_oor_vote (
      .a_i              ( r_oor_gated[0] ),
      .b_i              ( r_oor_gated[1] ),
      .c_i              ( r_oor_gated[2] ),
      .majority_o       ( r_idx_oor      ),
      .fault_detected_o ( r_oor_div      )
    );

    assign faults[10] = b_oor_div;
    assign faults[11] = r_oor_div;

    logic [2:0] b_pf_gated, r_pf_gated;
    for (genvar i = 0; i < 3; i++) begin : gen_pf_gate
      assign b_pf_gated[i] = slv_b_valid_d[i] & (|b_payload_faults);
      assign r_pf_gated[i] = slv_r_valid_d[i] & (|r_payload_faults);
    end

    TMR_voter_fail #(.VoterType(1)) i_b_pf_vote (
      .a_i(b_pf_gated[0]), .b_i(b_pf_gated[1]), .c_i(b_pf_gated[2]),
      .majority_o(faults[8]), .fault_detected_o()
    );

    TMR_voter_fail #(.VoterType(1)) i_r_pf_vote (
      .a_i(r_pf_gated[0]), .b_i(r_pf_gated[1]), .c_i(r_pf_gated[2]),
      .majority_o(faults[9]), .fault_detected_o()
    );

    logic [2:0] r_last;
    for (genvar i = 0; i < 3; i++) begin : gen_r_last
      assign r_last[i] = slv_r_valid_d[i] ? mst_resps_i[r_idx_g[i]].r.last[i] : 1'b0;
    end
    assign r_pop = slv_r_valid_d & slv_r_ready_d & r_last;

    for (genvar j = 0; j < NoMstPorts; j++) begin : gen_mst_hs_if
      assign mst_aw_ready_d[j] = mst_resps_i[j].aw_ready;
      assign mst_ar_ready_d[j] = mst_resps_i[j].ar_ready;
      assign mst_b_valid_d[j]  = mst_resps_i[j].b_valid;
      assign mst_r_valid_d[j]  = mst_resps_i[j].r_valid;
    end

    //--------------------------------------
    // Channel Control
    //--------------------------------------
    //--------------------------------------

    //--------------------------------------
    // AW Channel
    //--------------------------------------
    for (genvar i = 0; i < 3; i++) begin : gen_aw_ctrl
      // each replica uses its own raw inputs
      // Control of the AW handshake
      always_comb begin
        // AXI Handshakes
        slv_aw_ready_d[i] = 1'b0;
        aw_valid[i]     = 1'b0;
        // `lock_aw_valid`, used to be protocol conform as it is not allowed to deassert
        // a valid if there was no corresponding ready. As this process has to be able to inject
        // an AXI ID into the counter of the AR channel on an ATOP, there could be a case where
        // this process waits on `aw_ready` but in the mean time on the AR channel the counter gets
        // full.
        lock_aw_valid_d[i] = lock_aw_valid_q[i];
        load_aw_lock[i]    = 1'b0;
        // AW ID counter and W FIFO
        w_cnt_up[i]        = 1'b0;
        // ATOP injection into ar counter
        atop_inject[i]     = 1'b0;
        // we had an arbitration decision, the valid is locked, wait for the transaction
        if (lock_aw_valid_q[i]) begin
          aw_valid[i] = 1'b1;
          // transaction
          if (aw_ready[i]) begin
            slv_aw_ready_d[i] = 1'b1;
            lock_aw_valid_d[i] = 1'b0;
            load_aw_lock[i]    = 1'b1;
            // inject the ATOP if necessary
            atop_inject[i]     = slv_req_i.aw.atop[axi_pkg::ATOP_R_RESP] & AtopSupport;
          end
        end else begin
          // an AW can be handles if 'o_aw_id_counter' and 'i_coutner_open_w' are not full. An ATOP that
          // requires an R resposne can be handled if 'i_ar_id_counter' is not full (this
          // only applies if ATOPs are supported at all)
          if (!aw_id_cnt_full[i] && (w_open[i] != {IdCounterWidth{1'b1}}) &&
             (!(ar_id_cnt_full[i] && slv_req_i.aw.atop[axi_pkg::ATOP_R_RESP]) ||
             !AtopSupport)) begin
            if (slv_aw_valid_d[i] &&
                  ((w_open[i] == '0) || (w_select[i] == slv_aw_select_i[i])) &&
                  (!aw_select_occupied[i] || (slv_aw_select_i[i] == lookup_aw_select[i]))) begin
              // connect the handshake
              aw_valid[i] = 1'b1;
              w_cnt_up[i] = 1'b1;
              // on AW transaction
              if (aw_ready[i]) begin
                slv_aw_ready_d[i] = 1'b1;
                atop_inject[i]        = slv_req_i.aw.atop[axi_pkg::ATOP_R_RESP] & AtopSupport;
              // no AW transaction this cycle, lock the decision
              end else begin
                lock_aw_valid_d[i] = 1'b1;
                load_aw_lock[i]    = 1'b1;
              end
            end
          end
        end
      end
    end

    for (genvar i = 0; i < 3; i++) begin : gen_lock_aw_alt
      for (genvar j = 0; j < 2; j++) begin
        assign alt_lock_aw_valid[i][j] = lock_aw_valid_next[(i+j+1) % 3];
      end
    end

    for (genvar i = 0; i < 3; i++) begin : gen_lock_aw
      TMR_voter_fail #(.VoterType(1)) i_lock_aw_voted (
        .a_i              ( lock_aw_valid_next[i]    ),
        .b_i              ( alt_lock_aw_valid[i][0]  ),
        .c_i              ( alt_lock_aw_valid[i][1]  ),
        .majority_o       ( lock_aw_valid_q[i]       ),
        .fault_detected_o ( lock_aw_faults[i]        )
      );

      always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni)              lock_aw_valid_next[i] <= 1'b0;
        else if (load_aw_lock[i]) lock_aw_valid_next[i] <= lock_aw_valid_d[i];
        else                      lock_aw_valid_next[i] <= lock_aw_valid_q[i];
      end
    end

    if (UniqueIds) begin : gen_unique_ids_aw
      // If the `UniqueIds` parameter is set, each write transaction has an ID that is unique among
      // all in-flight write transactions, or all write transactions with a given ID target the same
      // master port as all write transactions with the same ID, or both.  This means that the
      // signals that are driven by the ID counters if this parameter is not set can instead be
      // derived from existing signals.  The ID counters can therefore be omitted.
      for (genvar i = 0; i < 3; i++) begin : gen_unique_ids_aw
        assign lookup_aw_select[i] = slv_aw_select_i[i];
        assign aw_select_occupied[i] = 1'b0;
        assign aw_id_cnt_full[i] = 1'b0;
      end
      assign aw_idcnt_fault = 1'b0;
    end else begin : gen_aw_id_counter
      relaxi_demux_id_counters #(
        .AxiIdBits         ( AxiLookBits    ),
        .CounterWidth      ( IdCounterWidth ),
        .mst_port_select_t ( select_t       )
      ) i_aw_id_counter (
        .clk_i                        ( clk_i                          ),
        .rst_ni                       ( rst_ni                         ),
        .lookup_axi_id_i              ( aw_lookup_id                   ),
        .lookup_mst_select_o          ( lookup_aw_select               ),
        .lookup_mst_select_occupied_o ( aw_select_occupied             ),
        .full_o                       ( aw_id_cnt_full                 ),
        .inject_axi_id_i              ( '0                             ),
        .inject_i                     ( 3'b000                         ),
        .push_axi_id_i                ( aw_lookup_id                   ),
        .push_mst_select_i            ( slv_aw_select_i                ),
        .push_i                       ( w_cnt_up                       ),
        .pop_axi_id_i                 ( b_pop_id                       ),
        .pop_i                        ( b_pop                          ),
        .any_outstanding_trx_o        ( ),
        .fault_o                      ( aw_idcnt_fault )
      );
      // pop from ID counter on outward transaction
    end

    // This counter steers the demultiplexer of the W channel.
    // `w_select` determines, which handshaking is connected.
    // AWs are only forwarded, if the counter is empty, or `w_select_q` is the same as
    // `slv_aw_select_i`.
    rel_counter #(
      .WIDTH           ( IdCounterWidth ),
      .STICKY_OVERFLOW ( 1'b0           ),
      .TmrStatus       ( 1'b1           )
    ) i_counter_open_w (
      .clk_i,
      .rst_ni,
      .clear_i    ( 3'b000                ),
      .en_i       ( w_cnt_up ^ w_cnt_down ),
      .load_i     ( 3'b000                ),
      .down_i     ( w_cnt_down            ),
      .d_i        ( '0                    ),
      .q_o        ( w_open                ),
      .overflow_o ( /*not used*/          ),
      .fault_o    ( open_w_fault          )
    );

    for (genvar i = 0; i < 3; i++) begin : gen_w_sel_alt
      for (genvar j = 0; j < 2; j++) begin
        assign alt_w_select[i][j] = w_select_next[(i+j+1) % 3];
      end
    end

    for (genvar i = 0; i < 3; i++) begin : gen_w_sel_tmr
      bitwise_TMR_voter_fail #(.DataWidth(SelectWidth)) i_w_sel_vote (
        .a_i              ( w_select_next[i]   ),
        .b_i              ( alt_w_select[i][0] ),
        .c_i              ( alt_w_select[i][1] ),
        .majority_o       ( w_select_q[i]      ),
        .fault_detected_o ( w_sel_faults[i]    )
      );

      always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni)          w_select_next[i] <= select_t'(0);
        else if (w_cnt_up[i]) w_select_next[i] <= slv_aw_select_i[i];
        else                  w_select_next[i] <= w_select_q[i];
      end
    end

    for (genvar i = 0; i < 3; i++) begin : gen_w_select
      assign w_select[i]       = (|w_open[i]) ? w_select_q[i] : slv_aw_select_i[i];
      assign w_select_valid[i] = w_cnt_up[i] | (|w_open[i]);
    end

    //--------------------------------------
    //  W Channel
    //--------------------------------------

    //--------------------------------------
    //  B Channel
    //--------------------------------------

    // Arbitration of the different B responses
    rel_rr_arb_tree #(
      .NumIn    ( NoMstPorts ),
      .DataType ( logic      ),
      .AxiVldRdy( 1'b1       ),
      .LockIn   ( 1'b1       ),
      .TmrStatus( 1'b1       )
    ) i_b_mux (
      .clk_i   ( clk_i           ),
      .rst_ni  ( rst_ni          ),
      .flush_i ( 1'b0            ),
      .rr_i    ( '0              ),
      .req_i   ( mst_b_valids    ),
      .gnt_o   ( mst_b_readies   ),
      .data_i  ( '0              ),
      .gnt_i   ( slv_b_ready_d   ),
      .req_o   ( slv_b_valid_d   ),
      .data_o  (                 ),
      .idx_o   ( b_idx           ),
      .fault_o ( b_arb_fault     )
    );

    for (genvar i = 0; i < 3; i++) begin : gen_b_mux_rep
      always_comb begin
        b_payload_raw[i] = '0;
        for (int unsigned j = 0; j < NoMstPorts; j++)
          if (b_idx_g[i] == IdxW'(j)) b_payload_raw[i] = mst_resps_i[j].b;
      end
    end

    //--------------------------------------\
    //  AR Channel
    //--------------------------------------

    // control of the AR handshake
    for (genvar i = 0; i < 3; i++) begin : gen_ar_ctrl
      always_comb begin
        // AXI Handshakes
        slv_ar_ready_d[i]    = 1'b0;
        ar_valid[i]        = 1'b0;
        // `lock_ar_valid`: Used to be protocol conform as it is not allowed to deassert `ar_valid`
        // if there was no corresponding `ar_ready`. There is the possibility that an injection
        // of a R response from an `atop` from the AW channel can change the occupied flag of the
        // `i_ar_id_counter`, even if it was previously empty. This FF prevents the deassertion.
        lock_ar_valid_d[i] = lock_ar_valid_q[i];
        load_ar_lock[i]    = 1'b0;
        // AR id counter
        ar_push[i]         = 1'b0;
        // The process had an arbitration decision in a previous cycle, the valid is locked,
        // wait for the AR transaction.
        if (lock_ar_valid_q[i]) begin
          ar_valid[i] = 1'b1;
          // transaction
          if (ar_ready[i]) begin
            slv_ar_ready_d[i]    = 1'b1;
            ar_push[i]         = 1'b1;
            lock_ar_valid_d[i] = 1'b0;
            load_ar_lock[i]    = 1'b1;
          end
        end else begin
          // The process can start handling AR transaction if `i_ar_id_counter` has space.
          if (!ar_id_cnt_full[i]) begin
            // There is a valid AR, so look the ID up.
            if (slv_ar_valid_d[i] && (!ar_select_occupied[i] ||
              (slv_ar_select_i[i] == lookup_ar_select[i]))) begin
              // connect the AR handshake
              ar_valid[i]     = 1'b1;
              // on transaction
              if (ar_ready[i]) begin
                slv_ar_ready_d[i] = 1'b1;
                ar_push[i]      = 1'b1;
              // no transaction this cycle, lock the valid decision!
              end else begin
                lock_ar_valid_d[i] = 1'b1;
                load_ar_lock[i]    = 1'b1;
              end
            end
          end
        end
      end
    end

    for (genvar i = 0; i < 3; i++) begin : gen_lock_ar_alt
      for (genvar j = 0; j < 2; j++) begin
        assign alt_lock_ar_valid[i][j] = lock_ar_valid_next[(i+j+1) % 3];
      end
    end

    for (genvar i = 0; i < 3; i++) begin : gen_lock_ar
      TMR_voter_fail #(.VoterType(1)) i_lock_ar_voted (
        .a_i              ( lock_ar_valid_next[i]   ),
        .b_i              ( alt_lock_ar_valid[i][0] ),
        .c_i              ( alt_lock_ar_valid[i][1] ),
        .majority_o       ( lock_ar_valid_q[i]      ),
        .fault_detected_o ( lock_ar_faults[i]       )
      );

      always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni)              lock_ar_valid_next[i] <= 1'b0;
        else if (load_ar_lock[i]) lock_ar_valid_next[i] <= lock_ar_valid_d[i];
        else                      lock_ar_valid_next[i] <= lock_ar_valid_q[i];
      end
    end

    if (UniqueIds) begin : gen_unique_ids_ar
      // If the `UniqueIds` parameter is set, each read transaction has an ID that is unique among
      // all in-flight read transactions, or all read transactions with a given ID target the same
      // master port as all read transactions with the same ID, or both.  This means that the
      // signals that are driven by the ID counters if this parameter is not set can instead be
      // derived from existing signals.  The ID counters can therefore be omitted.
      for (genvar i = 0; i < 3; i++) begin : gen_unique_ids_ar
        assign lookup_ar_select[i] = slv_ar_select_i[i];
        assign ar_select_occupied[i] = 1'b0;
        assign ar_id_cnt_full[i] = 1'b0;
      end
      assign ar_idcnt_fault = 1'b0;
    end else begin : gen_ar_id_counter
      relaxi_demux_id_counters #(
        .AxiIdBits         ( AxiLookBits    ),
        .CounterWidth      ( IdCounterWidth ),
        .mst_port_select_t ( select_t       )
      ) i_ar_id_counter (
        .clk_i                        ( clk_i                                       ),
        .rst_ni                       ( rst_ni                                      ),
        .lookup_axi_id_i              ( ar_lookup_id                                ),
        .lookup_mst_select_o          ( lookup_ar_select                            ),
        .lookup_mst_select_occupied_o ( ar_select_occupied                          ),
        .full_o                       ( ar_id_cnt_full                              ),
        .inject_axi_id_i              ( aw_lookup_id                                ),
        .inject_i                     ( atop_inject                                 ),
        .push_axi_id_i                ( ar_lookup_id                                ),
        .push_mst_select_i            ( slv_ar_select_i                             ),
        .push_i                       ( ar_push                                     ),
        .pop_axi_id_i                 ( r_pop_id                                    ),
        .pop_i                        ( r_pop                                       ),
        .any_outstanding_trx_o        ( ),
        .fault_o                      ( ar_idcnt_fault                              )
      );
    end

    //--------------------------------------
    //  R Channel
    //--------------------------------------

    // Arbitration of the different r responses
    rel_rr_arb_tree #(
      .NumIn    ( NoMstPorts ),
      .DataType ( logic      ),
      .AxiVldRdy( 1'b1       ),
      .LockIn   ( 1'b1       ),
      .TmrStatus( 1'b1       )
    ) i_r_mux (
      .clk_i  ( clk_i           ),
      .rst_ni ( rst_ni          ),
      .flush_i( 1'b0            ),
      .rr_i   ( '0              ),
      .req_i  ( mst_r_valids   ),
      .gnt_o  ( mst_r_readies  ),
      .data_i ( '0              ),
      .gnt_i  ( slv_r_ready_d   ),
      .req_o  ( slv_r_valid_d   ),
      .data_o (                 ),
      .idx_o  ( r_idx           ),
      .fault_o( r_arb_fault     )
    );

    for (genvar i = 0; i < 3; i++) begin : gen_r_mux_rep
      always_comb begin
        r_payload_raw[i] = '0;
        for (int unsigned j = 0; j < NoMstPorts; j++)
          if (r_idx_g[i] == IdxW'(j)) r_payload_raw[i] = mst_resps_i[j].r;
      end
    end

    for (genvar b = 0; b < BChanBits; b++) begin : gen_b_payload_vote
      TMR_voter_fail #(.VoterType(1)) i_b_vote (
        .a_i              ( b_payload_raw[0][b] ),
        .b_i              ( b_payload_raw[1][b] ),
        .c_i              ( b_payload_raw[2][b] ),
        .majority_o       ( b_payload[b]        ),
        .fault_detected_o ( b_payload_faults[b] )
      );
    end

    for (genvar b = 0; b < RChanBits; b++) begin : gen_r_payload_vote
      TMR_voter_fail #(.VoterType(1)) i_r_vote (
        .a_i              ( r_payload_raw[0][b] ),
        .b_i              ( r_payload_raw[1][b] ),
        .c_i              ( r_payload_raw[2][b] ),
        .majority_o       ( r_payload[b]        ),
        .fault_detected_o ( r_payload_faults[b] )
      );
    end

    assign slv_resp_o.b = b_payload;
    assign slv_resp_o.r = r_payload;

    //--------------------------------------
    // Pop-Path ID Decoders
    //--------------------------------------
    logic [2:0][AxiIdWidth-1:0] b_id_corr, r_id_corr;
    logic [2:0][1:0]            b_id_fault, r_id_fault;

    for (genvar i = 0; i < 3; i++) begin : gen_b_pop_dec
      relaxi_id_dec #(.IdWidth(AxiIdWidth)) i_b_dec (
        .id_i    ( mst_resps_i[b_idx_g[i]].b.id     ),
        .id_ecc_i( mst_resps_i[b_idx_g[i]].b.id_ecc ),
        .id_o    ( b_id_corr[i]                     ),
        .err_o   ( b_id_fault[i]                    )
      );
    end

    always_comb begin
      b_pop_id = '0;
      for (int i = 0; i < 3; i++) begin
        if (slv_b_valid_d[i]) begin
          // use the decoded ID instead of raw mst_resps_i
          b_pop_id[i] = b_id_corr[i][0+:AxiLookBits];
        end
      end
    end

    always_comb begin
      pop_id_fault = 2'b00;
      for (int i = 0; i < 3; i++) begin
        if (b_pop[i]) pop_id_fault |= b_id_fault[i];
        if (r_pop[i]) pop_id_fault |= r_id_fault[i];
      end
    end

    for (genvar i = 0; i < 3; i++) begin : gen_r_pop_dec
      relaxi_id_dec #(.IdWidth(AxiIdWidth)) i_r_dec (
        .id_i    ( mst_resps_i[r_idx_g[i]].r.id     ),
        .id_ecc_i( mst_resps_i[r_idx_g[i]].r.id_ecc ),
        .id_o    ( r_id_corr[i]                     ),
        .err_o   ( r_id_fault[i]                    )
      );
    end

    always_comb begin
      r_pop_id = '0;
      for (int i = 0; i < 3; i++) begin
        if (slv_r_valid_d[i]) begin
          // use the decoded ID instead of raw mst_resps_i
          r_pop_id[i] = r_id_corr[i][0+:AxiLookBits];
        end
      end
    end

    for (genvar i = 0; i < 3; i ++ ) begin: gen_ax_readies
      assign ar_ready[i] = ar_valid[i] & mst_ar_ready_d[slv_ar_select_i[i]][i];
      assign aw_ready[i] = aw_valid[i] & mst_aw_ready_d[slv_aw_select_i[i]][i];
    end

    // process that defines the individual demuxes and assignments for the arbitration
    // as mst_reqs_o has to be drivem from the same always comb block!
    always_comb begin
      // Default everything to zero once, before the per-replica loop.
      // Moving this inside the loop would erase replica i-1 work on each iteration.
      mst_reqs_o = '0;
      for (int i = 0; i < 3; i++) begin
        slv_w_ready_d[i] = 1'b0;
        w_cnt_down[i]    = 1'b0;

        for (int unsigned j = 0; j < NoMstPorts; j++) begin
          // AW channel
          mst_reqs_o[j].aw     = slv_req_i.aw;
          mst_aw_valid_d[j][i] = 1'b0;
          if (aw_valid[i] && (slv_aw_select_i[i] == select_t'(j))) begin
            mst_aw_valid_d[j][i] = 1'b1;
          end

          // W channel — use per-replica [i] index so port-1 comparison works
          mst_reqs_o[j].w = slv_req_i.w;
          if (w_select_valid[i] && (w_select[i] == select_t'(j))) begin
            mst_reqs_o[j].w_valid[i] = slv_req_i.w_valid[i];
            slv_w_ready_d[i]         = mst_resps_i[j].w_ready[i];
            w_cnt_down[i]            = slv_req_i.w_valid[i] & mst_resps_i[j].w_ready[i]
                                       & slv_req_i.w.last[i];
          end

          // B channel
          mst_b_ready_d[j][i] = mst_b_readies[j][i];

          // AR channel — use per-replica [i] index so port-1 comparison works
          mst_reqs_o[j].ar = slv_req_i.ar;
          if (ar_valid[i] && (slv_ar_select_i[i] == select_t'(j))) begin
            mst_reqs_o[j].ar_valid[i] = 1'b1;
          end

          // R channel
          mst_reqs_o[j].r_ready[i] = mst_r_readies[j][i];
        end
      end
      for (int unsigned j = 0; j < NoMstPorts; j++) begin
        mst_reqs_o[j].aw_valid = mst_aw_valid_d[j];
        mst_reqs_o[j].b_ready  = mst_b_ready_d[j];
      end
    end

    // unpack the response B and R channels for the arbitration
    for (genvar i = 0; i < 3; i++) begin : gen_b_channels
      for (genvar j = 0; j < NoMstPorts; j++) begin
        assign mst_b_valids[j][i] = mst_b_valid_d[j][i];
        assign mst_r_valids[j][i] = mst_r_valid_d[j][i];
      end
    end

// Validate parameters.
// pragma translate_off
`ifndef FAULTSIM
`ifndef VERILATOR
`ifndef XSIM
  // AW select: replicas must agree (TMR invariant) and be legal
  aw_select_consistent: assert property(@(posedge clk_i) disable iff (!rst_ni)
    (aw_valid[0] |-> (slv_aw_select_i[0] == slv_aw_select_i[1]) &&
                     (slv_aw_select_i[1] == slv_aw_select_i[2]))) else
    $fatal(1, "AW select replicas diverged (TMR inconsistency).");

  aw_select_legal: assert property(@(posedge clk_i) disable iff (!rst_ni)
    (aw_valid[0] |-> slv_aw_select_i[0] < NoMstPorts)) else
    $fatal(1, "AW select out of range: %0d (NoMstPorts=%0d).",
           slv_aw_select_i[0], NoMstPorts);

  // AR select: same
  ar_select_consistent: assert property(@(posedge clk_i) disable iff (!rst_ni)
    (ar_valid[0] |-> (slv_ar_select_i[0] == slv_ar_select_i[1]) &&
                     (slv_ar_select_i[1] == slv_ar_select_i[2]))) else
    $fatal(1, "AR select replicas diverged (TMR inconsistency).");

  ar_select_legal: assert property(@(posedge clk_i) disable iff (!rst_ni)
    (ar_valid[0] |-> slv_ar_select_i[0] < NoMstPorts)) else
    $fatal(1, "AR select out of range: %0d (NoMstPorts=%0d).",
           slv_ar_select_i[0], NoMstPorts);

  b_idx_consistent: assert property(@(posedge clk_i) disable iff (!rst_ni)
    ((|slv_b_valid_d) |-> (b_idx[0] == b_idx[1]) && (b_idx[1] == b_idx[2])));

  b_idx_legal: assert property(@(posedge clk_i) disable iff (!rst_ni)
    ((|slv_b_valid_d) |-> (b_idx[0] < NoMstPorts) &&
                          (b_idx[1] < NoMstPorts) &&
                          (b_idx[2] < NoMstPorts)));
`endif
`endif
`endif
// pragma translate_on
  end // gen_demux
endmodule
