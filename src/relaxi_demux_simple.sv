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

  output logic                          fault_o
);

  localparam int unsigned IdCounterWidth = cf_math_pkg::idx_width(MaxTrans);
  typedef logic [IdCounterWidth-1:0] id_cnt_t;
  
  localparam intunsigned NumFaults = 8;// Update if more faults are added
  logic [NumFaults-1:0] faults;
  assign fault_o = |faults;

  // pass through if only one master port
  if (NoMstPorts == 32'h1) begin : gen_no_demux
    `AXI_ASSIGN_REQ_STRUCT(mst_reqs_o[0], slv_req_i)
    `AXI_ASSIGN_RESP_STRUCT(slv_resp_o, mst_resps_i[0])
    assign faults = '0;
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
    select_t   [2:0]               w_select,           w_select_q;
    select_t   [2:0][1:0]          alt_w_select;
    logic      [2:0]               w_select_valid;
    id_cnt_t   [2:0]               w_open;
    logic      [2:0]               w_cnt_up,           w_cnt_down;

    // B channles input into the arbitration
    logic    [2:0][NoMstPorts-1:0] mst_b_valids,       mst_b_readies;

    //--------------------------------------
    // Read Transaction
    //--------------------------------------

    // AR ID counter
    select_t  [2:0]               lookup_ar_select;
    logic     [2:0]               ar_select_occupied, ar_id_cnt_full;
    logic     [2:0]               ar_push;

    // Register which locks the AR valid signal
    logic     [2:0]              lock_ar_valid_d,    lock_ar_valid_q, load_ar_lock;
    logic     [2:0]              ar_valid,           ar_ready;

    logic     [2:0][NoMstPorts-1:0] mst_r_valids, mst_r_readies;

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
        slv_resp_o.aw_ready[i] = 1'b0;
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
            slv_resp_o.aw_ready[i] = 1'b1;
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
            if (slv_req_i.aw_valid[i] &&
                  ((w_open[i] == '0) || (w_select[i] == slv_aw_select_i[i])) &&
                  (!aw_select_occupied[i] || (slv_aw_select_i[i] == lookup_aw_select[i]))) begin
              // connect the handshake
              aw_valid[i] = 1'b1;
              w_cnt_up[i] = 1'b1;
              // on AW transaction
              if (aw_ready[i]) begin
                slv_resp_o.aw_ready[i] = 1'b1;
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
        .fault_detected_o (                          )  // fault to-do
      );

      `FFLARN(lock_aw_valid_next[i], lock_aw_valid_d[i], load_aw_lock[i], '0, clk_i, rst_ni)
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
    end else begin : gen_aw_id_counter
      relaxi_demux_id_counters #(
        .AxiIdBits         ( AxiLookBits    ),
        .CounterWidth      ( IdCounterWidth ),
        .mst_port_select_t ( select_t       )
      ) i_aw_id_counter (
        .clk_i                        ( clk_i                          ),
        .rst_ni                       ( rst_ni                         ),
        .lookup_axi_id_i              ( slv_req_i.aw.id[0+:AxiLookBits] ),
        .lookup_mst_select_o          ( lookup_aw_select               ),
        .lookup_mst_select_occupied_o ( aw_select_occupied             ),
        .full_o                       ( aw_id_cnt_full                 ),
        .inject_axi_id_i              ( '0                             ),
        .inject_i                     ( 3'b000                         ),
        .push_axi_id_i                ( slv_req_i.aw.id[0+:AxiLookBits] ),
        .push_mst_select_i            ( slv_aw_select_i                ),
        .push_i                       ( w_cnt_up                       ),
        .pop_axi_id_i                 ( slv_resp_o.b.id[0+:AxiLookBits]  ),
        .pop_i                        ( slv_resp_o.b_valid & slv_req_i.b_ready      ),
        .any_outstanding_trx_o        ( )
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
      .overflow_o ( /*not used*/          )
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
        .fault_detected_o (                    )
      );
      `FFLARN(w_select_next[i], slv_aw_select_i[i], w_cnt_up[i], select_t'(0), clk_i, rst_ni)
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
    logic [cf_math_pkg::idx_width(NoMstPorts)-1:0][2:0] b_idx;
   
    // Arbitration of the different B responses
    rel_rr_arb_tree #(
      .NumIn    ( NoMstPorts ),
      .DataType ( logic      ),
      .AxiVldRdy( 1'b1       ),
      .LockIn   ( 1'b1       ),
      .TmrStatus( 1'b1       )
    ) i_b_mux (
      .clk_i  ( clk_i         ),
      .rst_ni ( rst_ni        ),
      .flush_i( 1'b0          ),
      .rr_i   ( '0            ),
      .req_i  ( mst_b_valids  ),
      .gnt_o  ( mst_b_readies ),
      .data_i ( '0   ),
      .gnt_i  ( slv_req_i.b_ready  ),
      .req_o  ( slv_resp_o.b_valid ),
      .data_o (        ),
      .idx_o  ( b_idx              )
    );

    always_comb begin
      for (int i = 0; i < 3; i++) begin
        if (slv_resp_o.b_valid[i]) begin
          `AXI_SET_B_STRUCT(slv_resp_o.b, mst_resps_i[b_idx[i]].b)
        end else begin
          slv_resp_o.b = '0;
        end
      end
    end

    //--------------------------------------\
    //  AR Channel
    //--------------------------------------

    // control of the AR handshake
    for (genvar i = 0; i < 3; i++) begin : gen_ar_ctrl
      always_comb begin
        // AXI Handshakes
        slv_resp_o.ar_ready[i]    = 1'b0;
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
            slv_resp_o.ar_ready[i]    = 1'b1;
            ar_push[i]         = 1'b1;
            lock_ar_valid_d[i] = 1'b0;
            load_ar_lock[i]    = 1'b1;
          end
        end else begin
          // The process can start handling AR transaction if `i_ar_id_counter` has space.
          if (!ar_id_cnt_full[i]) begin
            // There is a valid AR, so look the ID up.
            if (slv_req_i.ar_valid && (!ar_select_occupied[i] ||
              (slv_ar_select_i[i] == lookup_ar_select[i]))) begin
              // connect the AR handshake
              ar_valid[i]     = 1'b1;
              // on transaction
              if (ar_ready[i]) begin
                slv_resp_o.ar_ready[i] = 1'b1;
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
        .fault_detected_o (                         )
      );
      `FFLARN(lock_ar_valid_next[i], lock_ar_valid_d[i], load_ar_lock[i], '0, clk_i, rst_ni)
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
    end else begin : gen_ar_id_counter
      relaxi_demux_id_counters #(
        .AxiIdBits         ( AxiLookBits    ),
        .CounterWidth      ( IdCounterWidth ),
        .mst_port_select_t ( select_t       )
      ) i_ar_id_counter (
        .clk_i                        ( clk_i                                       ),
        .rst_ni                       ( rst_ni                                      ),
        .lookup_axi_id_i              ( slv_req_i.ar.id[0+:AxiLookBits]             ),
        .lookup_mst_select_o          ( lookup_ar_select                            ),
        .lookup_mst_select_occupied_o ( ar_select_occupied                          ),
        .full_o                       ( ar_id_cnt_full                              ),
        .inject_axi_id_i              ( slv_req_i.aw.id[0+:AxiLookBits]             ),
        .inject_i                     ( atop_inject                                 ),
        .push_axi_id_i                ( slv_req_i.ar.id[0+:AxiLookBits]             ),
        .push_mst_select_i            ( slv_ar_select_i                             ),
        .push_i                       ( ar_push                                     ),
        .pop_axi_id_i                 ( slv_resp_o.r.id[0+:AxiLookBits]               ),
        .pop_i                        ( slv_resp_o.r_valid & slv_req_i.r_ready & slv_resp_o.r.last ),
        .any_outstanding_trx_o        ( )
      );
    end

    //--------------------------------------
    //  R Channel
    //--------------------------------------

    logic [cf_math_pkg::idx_width(NoMstPorts)-1:0][2:0] r_idx;

    // Arbitration of the different r responses
    rr_arb_tree #(
      .NumIn    ( NoMstPorts ),
      .DataType ( logic   ),
      .AxiVldRdy( 1'b1       ),
      .LockIn   ( 1'b1       )
    ) i_r_mux (
      .clk_i  ( clk_i         ),
      .rst_ni ( rst_ni        ),
      .flush_i( 1'b0          ),
      .rr_i   ( '0            ),
      .req_i  ( mst_r_valids  ),
      .gnt_o  ( mst_r_readies ),
      .data_i ( '0            ),
      .gnt_i  ( slv_req_i.r_ready   ),
      .req_o  ( slv_resp_o.r_valid   ),
      .data_o (),
      .idx_o  ( r_idx              )
    );

    always_comb begin
      for (int i = 0; i < 3; i++) begin
        if (slv_resp_o.r_valid[i]) begin
          `AXI_SET_R_STRUCT(slv_resp_o.r, mst_resps_i[r_idx[i]].r)
        end else begin
          slv_resp_o.r = '0;
        end
      end
    end
    
    for (genvar i = 0; i < 3; i ++ ) begin: gen_ax_readies
      assign ar_ready[i] = ar_valid[i] & mst_resps_i[slv_ar_select_i[i]].ar_ready[i];
      assign aw_ready[i] = aw_valid[i] & mst_resps_i[slv_aw_select_i[i]].aw_ready[i];
    end
    
    // process that defines the individual demuxes and assignments for the arbitration
    // as mst_reqs_o has to be drivem from the same always comb block!
    always_comb begin
      for (int i = 0; i < 3; i++) begin
        // default assignments
        mst_reqs_o  = '0; // out of the loop? to save area? 
        slv_resp_o.w_ready[i] = 1'b0;
        w_cnt_down[i]  = 1'b0;

        for (int unsigned j = 0; j < NoMstPorts; j++) begin
          // AW channel
          mst_reqs_o[j].aw       = slv_req_i.aw;
          mst_reqs_o[j].aw_valid[j] = 1'b0;
          if (aw_valid[i] && (slv_aw_select_i[j] == j)) begin
            mst_reqs_o[j].aw_valid[i] = 1'b1;
          end

          //  W channel
          mst_reqs_o[j].w       = slv_req_i.w;
          mst_reqs_o[j].w_valid = 1'b0;
          if (w_select_valid && (w_select == j)) begin
            mst_reqs_o[j].w_valid = slv_req_i.w_valid;
            slv_resp_o.w_ready           = mst_resps_i[j].w_ready;
            w_cnt_down            = slv_req_i.w_valid & mst_resps_i[j].w_ready & slv_req_i.w.last;
          end

          //  B channel
          mst_reqs_o[j].b_ready[i] = mst_b_readies[j];

          // AR channel
          mst_reqs_o[j].ar       = slv_req_i.ar;
          mst_reqs_o[j].ar_valid = 1'b0;
          if (ar_valid && (slv_ar_select_i == j)) begin
            mst_reqs_o[j].ar_valid = 1'b1;
          end

          //  R channel
          mst_reqs_o[j].r_ready = mst_r_readies[j];
        end
      end
    end

    // unpack the response B and R channels for the arbitration
    for (genvar i = 0; i < 3; i++) begin : gen_b_channels
      for (genvar j = 0; j < NoMstPorts; j++) begin
        assign mst_b_valids[j]       = mst_resps_i[j].b_valid[i];
        assign mst_r_valids[j]       = mst_resps_i[j].r_valid[i];
      end
    end

// Validate parameters.
// pragma translate_off
`ifndef VERILATOR
    initial begin: validate_params
      no_mst_ports: assume (NoMstPorts > 0) else
        $fatal(1, "The Number of slaves (NoMstPorts) has to be at least 1");
      AXI_ID_BITS:  assume (AxiIdWidth >= AxiLookBits) else
        $fatal(1, "AxiIdBits has to be equal or smaller than AxiIdWidth.");
    end
`ifndef XSIM
    default disable iff (!rst_ni);
    aw_select: assume property( @(posedge clk_i) (slv_req_i.aw_valid |->
                                                 (slv_aw_select_i < NoMstPorts))) else
      $fatal(1, "slv_aw_select_i is %d: AW has selected a slave that is not defined.\
                 NoMstPorts: %d", slv_aw_select_i, NoMstPorts);
    ar_select: assume property( @(posedge clk_i) (slv_req_i.ar_valid |->
                                                 (slv_ar_select_i < NoMstPorts))) else
      $fatal(1, "slv_ar_select_i is %d: AR has selected a slave that is not defined.\
                 NoMstPorts: %d", slv_ar_select_i, NoMstPorts);
    aw_valid_stable: assert property( @(posedge clk_i) (aw_valid && !aw_ready) |=> aw_valid) else
      $fatal(1, "aw_valid was deasserted, when aw_ready = 0 in last cycle.");
    ar_valid_stable: assert property( @(posedge clk_i)
                               (ar_valid && !ar_ready) |=> ar_valid) else
      $fatal(1, "ar_valid was deasserted, when ar_ready = 0 in last cycle.");
    slv_aw_chan_stable: assert property( @(posedge clk_i) (aw_valid && !aw_ready)
                               |=> $stable(slv_req_i.aw)) else
      $fatal(1, "slv_aw_chan unstable with valid set.");
    slv_aw_select_stable: assert property( @(posedge clk_i) (aw_valid && !aw_ready)
                               |=> $stable(slv_aw_select_i)) else
      $fatal(1, "slv_aw_select_i unstable with valid set.");
    slv_ar_chan_stable: assert property( @(posedge clk_i) (ar_valid && !ar_ready)
                               |=> $stable(slv_req_i.ar)) else
      $fatal(1, "slv_ar_chan unstable with valid set.");
    slv_ar_select_stable: assert property( @(posedge clk_i) (ar_valid && !ar_ready)
                               |=> $stable(slv_ar_select_i)) else
      $fatal(1, "slv_ar_select_i unstable with valid set.");
    internal_ar_select: assert property( @(posedge clk_i)
        (ar_valid |-> slv_ar_select_i < NoMstPorts))
      else $fatal(1, "slv_ar_select_i illegal while ar_valid.");
    internal_aw_select: assert property( @(posedge clk_i)
        (aw_valid |-> slv_aw_select_i < NoMstPorts))
      else $fatal(1, "slv_aw_select_i illegal while aw_valid.");
    w_underflow: assert property( @(posedge clk_i)
        ((w_open == '0) && (w_cnt_up ^ w_cnt_down) |-> !w_cnt_down)) else
        $fatal(1, "W counter underflowed!");
    `ASSUME(NoAtopAllowed, !AtopSupport && slv_req_i.aw_valid |-> slv_req_i.aw.atop == '0)
`endif
`endif
// pragma translate_on
  end // gen_demux
endmodule