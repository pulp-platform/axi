// Copyright (c) 2022 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Authors:
// - Luca Colagrande <colluca@iis.ee.ethz.ch>
// Based on:
// - axi_demux.sv

`include "common_cells/assertions.svh"
`include "common_cells/registers.svh"

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
module axi_mcast_demux #(
  parameter int unsigned AxiIdWidth     = 32'd0,
  parameter bit          AtopSupport    = 1'b1,
  parameter type         aw_addr_t      = logic,
  parameter type         aw_chan_t      = logic,
  parameter type         w_chan_t       = logic,
  parameter type         b_chan_t       = logic,
  parameter type         ar_chan_t      = logic,
  parameter type         r_chan_t       = logic,
  parameter type         axi_req_t      = logic,
  parameter type         axi_resp_t     = logic,
  parameter int unsigned NoMstPorts     = 32'd0,
  parameter int unsigned MaxTrans       = 32'd8,
  parameter int unsigned AxiLookBits    = 32'd3,
  parameter bit          UniqueIds      = 1'b0,
  parameter bit          SpillAw        = 1'b1,
  parameter bit          SpillW         = 1'b0,
  parameter bit          SpillB         = 1'b0,
  parameter bit          SpillAr        = 1'b1,
  parameter bit          SpillR         = 1'b0,
  parameter type         rule_t         = logic,
  parameter int unsigned NoAddrRules    = 32'd0,
  parameter int unsigned NoMulticastRules = 32'd0,
  parameter int unsigned NoMulticastPorts = 32'd0,
  // Dependent parameters, DO NOT OVERRIDE!
  parameter int unsigned DecodeIdxWidth = ((NoMstPorts - 1) > 32'd1) ? $clog2(NoMstPorts - 1) : 32'd1,
  parameter int unsigned IdxSelectWidth = (NoMstPorts > 32'd1) ? $clog2(NoMstPorts) : 32'd1,
  parameter type         decode_idx_t   = logic [DecodeIdxWidth-1:0],
  parameter type         idx_select_t   = logic [IdxSelectWidth-1:0],
  parameter type         mask_select_t  = logic [NoMstPorts-1:0]
) (
  input  logic                       clk_i,
  input  logic                       rst_ni,
  input  logic                       test_i,
  input  rule_t    [NoAddrRules-1:0] addr_map_i,
  input  logic                       en_default_mst_port_i,
  input  decode_idx_t                default_mst_port_i,
  // Slave Port
  input  axi_req_t                   slv_req_i,
  input  idx_select_t                slv_ar_select_i,
  output axi_resp_t                  slv_resp_o,
  // Master Ports
  output axi_req_t  [NoMstPorts-1:0] mst_reqs_o,
  input  axi_resp_t [NoMstPorts-1:0] mst_resps_i,
  output logic      [NoMstPorts-1:0] mst_is_mcast_o,
  output logic      [NoMstPorts-1:0] mst_aw_commit_o
);

  localparam int unsigned IdCounterWidth = cf_math_pkg::idx_width(MaxTrans);
  typedef logic [IdCounterWidth-1:0] id_cnt_t;

  typedef struct packed {
    int unsigned idx;
    aw_addr_t addr;
    aw_addr_t mask;
  } mask_rule_t;

  // pass through if only one master port
  if (NoMstPorts == 32'h1) begin : gen_no_demux
    spill_register #(
      .T       ( aw_chan_t  ),
      .Bypass  ( ~SpillAw   )
    ) i_aw_spill_reg (
      .clk_i   ( clk_i                    ),
      .rst_ni  ( rst_ni                   ),
      .valid_i ( slv_req_i.aw_valid       ),
      .ready_o ( slv_resp_o.aw_ready      ),
      .data_i  ( slv_req_i.aw             ),
      .valid_o ( mst_reqs_o[0].aw_valid   ),
      .ready_i ( mst_resps_i[0].aw_ready  ),
      .data_o  ( mst_reqs_o[0].aw         )
    );
    spill_register #(
      .T       ( w_chan_t  ),
      .Bypass  ( ~SpillW   )
    ) i_w_spill_reg (
      .clk_i   ( clk_i                   ),
      .rst_ni  ( rst_ni                  ),
      .valid_i ( slv_req_i.w_valid       ),
      .ready_o ( slv_resp_o.w_ready      ),
      .data_i  ( slv_req_i.w             ),
      .valid_o ( mst_reqs_o[0].w_valid   ),
      .ready_i ( mst_resps_i[0].w_ready  ),
      .data_o  ( mst_reqs_o[0].w         )
    );
    spill_register #(
      .T       ( b_chan_t ),
      .Bypass  ( ~SpillB      )
    ) i_b_spill_reg (
      .clk_i   ( clk_i                  ),
      .rst_ni  ( rst_ni                 ),
      .valid_i ( mst_resps_i[0].b_valid ),
      .ready_o ( mst_reqs_o[0].b_ready  ),
      .data_i  ( mst_resps_i[0].b       ),
      .valid_o ( slv_resp_o.b_valid     ),
      .ready_i ( slv_req_i.b_ready      ),
      .data_o  ( slv_resp_o.b           )
    );
    spill_register #(
      .T       ( ar_chan_t  ),
      .Bypass  ( ~SpillAr   )
    ) i_ar_spill_reg (
      .clk_i   ( clk_i                    ),
      .rst_ni  ( rst_ni                   ),
      .valid_i ( slv_req_i.ar_valid       ),
      .ready_o ( slv_resp_o.ar_ready      ),
      .data_i  ( slv_req_i.ar             ),
      .valid_o ( mst_reqs_o[0].ar_valid   ),
      .ready_i ( mst_resps_i[0].ar_ready  ),
      .data_o  ( mst_reqs_o[0].ar         )
    );
    spill_register #(
      .T       ( r_chan_t ),
      .Bypass  ( ~SpillR      )
    ) i_r_spill_reg (
      .clk_i   ( clk_i                  ),
      .rst_ni  ( rst_ni                 ),
      .valid_i ( mst_resps_i[0].r_valid ),
      .ready_o ( mst_reqs_o[0].r_ready  ),
      .data_i  ( mst_resps_i[0].r       ),
      .valid_o ( slv_resp_o.r_valid     ),
      .ready_i ( slv_req_i.r_ready      ),
      .data_o  ( slv_resp_o.r           )
    );

  // other non degenerate cases
  end else begin : gen_demux

    //--------------------------------------
    //--------------------------------------
    // Signal Declarations
    //--------------------------------------
    //--------------------------------------

    //--------------------------------------
    // Write Transaction
    //--------------------------------------
    // comes from spill register at input
    aw_chan_t                  slv_aw_chan;
    logic                      slv_aw_valid;
    logic                      slv_aw_ready;

    // AW address decoder
    mask_rule_t [NoMulticastRules-1:0] multicast_rules;
    decode_idx_t                       dec_aw_idx;
    logic                              dec_aw_idx_valid, dec_aw_idx_error;
    logic       [NoMulticastPorts-1:0] dec_aw_select_partial;
    aw_addr_t   [NoMulticastPorts-1:0] dec_aw_addr, dec_aw_mask;
    logic                              dec_aw_select_error;
    logic       [NoMstPorts-2:0]       dec_aw_select;
    aw_addr_t   [NoMstPorts-1:0]       slv_aw_addr, slv_aw_mask;
    mask_select_t                      slv_aw_select_mask;
    idx_select_t                       slv_aw_select;

    // AW channel to slave ports
    logic [NoMstPorts-1:0]    mst_aw_valids, mst_aw_readies;

    // AW ID counter
    idx_select_t              lookup_aw_select;
    logic                     aw_select_occupied, aw_id_cnt_full;
    logic                     aw_any_outstanding_unicast_trx;
    logic                     aw_any_outstanding_trx;
    // Upon an ATOP load, inject IDs from the AW into the AR channel
    logic                     atop_inject;
    // Multicast logic
    logic                     aw_is_multicast;
    logic                     outstanding_multicast;
    logic                     multicast_stall;
    mask_select_t             multicast_select_q, multicast_select_d;
    logic                     multicast_select_load;
    logic [$clog2(NoMstPorts)+1-1:0] aw_select_popcount;
    logic                     accept_aw;
    logic                     mcast_aw_hs_in_progress;

    // W select counter: stores the decision to which masters W beats should go
    mask_select_t             w_select,           w_select_q;
    logic                     w_select_valid;
    id_cnt_t                  w_open;
    logic                     w_cnt_up,           w_cnt_down;

    // Register which locks the AW valid signal
    logic                     lock_aw_valid_d,    lock_aw_valid_q, load_aw_lock;
    logic                     aw_valid,           aw_ready;

    // W channel from spill reg
    w_chan_t                  slv_w_chan;
    logic                     slv_w_valid,        slv_w_ready;

    // W channel to slave ports
    logic [NoMstPorts-1:0]    mst_w_valids,       mst_w_readies;

    // B channels input into the arbitration (unicast transactions)
    // or join module (multicast transactions)
    b_chan_t [NoMstPorts-1:0] mst_b_chans;
    axi_pkg::resp_t [NoMstPorts-1:0] mst_b_resps;
    idx_select_t              mst_b_valids_tzc;
    logic    [NoMstPorts-1:0] mst_b_valids,       mst_b_readies;
    logic    [NoMstPorts-1:0] mst_b_readies_arb,  mst_b_readies_join;

    // B channel to spill register
    b_chan_t                  slv_b_chan;
    logic                     slv_b_valid,        slv_b_ready;
    b_chan_t                  slv_b_chan_arb,     slv_b_chan_join;
    logic                     slv_b_valid_arb,    slv_b_valid_join;

    //--------------------------------------
    // Read Transaction
    //--------------------------------------
    // comes from spill register at input
    logic                     slv_ar_valid, ar_valid_chan, ar_valid_sel;
    logic                     slv_ar_ready, slv_ar_ready_chan, slv_ar_ready_sel;

    // AR ID counter
    idx_select_t              lookup_ar_select;
    logic                     ar_select_occupied, ar_id_cnt_full;
    logic                     ar_push;

    // Register which locks the AR valid signel
    logic                     lock_ar_valid_d,    lock_ar_valid_q, load_ar_lock;
    logic                     ar_valid,           ar_ready;

    // R channles input into the arbitration
    r_chan_t [NoMstPorts-1:0] mst_r_chans;
    logic    [NoMstPorts-1:0] mst_r_valids, mst_r_readies;

    // R channel to spill register
    r_chan_t                  slv_r_chan;
    logic                     slv_r_valid,        slv_r_ready;

    //--------------------------------------
    //--------------------------------------
    // Channel Control
    //--------------------------------------
    //--------------------------------------

    //--------------------------------------
    // AW Channel
    //--------------------------------------
    // spill register at the channel input
    spill_register #(
      .T       ( aw_chan_t          ),
      .Bypass  ( ~SpillAw           ) // because module param indicates if we want a spill reg
    ) i_aw_channel_spill_reg (
      .clk_i   ( clk_i              ),
      .rst_ni  ( rst_ni             ),
      .valid_i ( slv_req_i.aw_valid ),
      .ready_o ( slv_resp_o.aw_ready ),
      .data_i  ( slv_req_i.aw       ),
      .valid_o ( slv_aw_valid       ),
      .ready_i ( slv_aw_ready       ),
      .data_o  ( slv_aw_chan        )
    );

    if (NoMulticastRules != NoAddrRules) begin : g_aw_idx_decode
      // Compare request against {start_addr, end_addr} rules
      addr_decode #(
        .NoIndices(NoMstPorts - 1),
        .NoRules  (NoAddrRules - NoMulticastRules),
        .addr_t   (aw_addr_t),
        .rule_t   (rule_t)
      ) i_axi_aw_idx_decode (
        .addr_i          (slv_aw_chan.addr),
        .addr_map_i      (addr_map_i[NoAddrRules-1:NoMulticastRules]),
        .idx_o           (dec_aw_idx),
        .dec_valid_o     (dec_aw_idx_valid),
        .dec_error_o     (dec_aw_idx_error),
        .en_default_idx_i(en_default_mst_port_i),
        .default_idx_i   (default_mst_port_i)
      );
    end else begin
      assign dec_aw_idx_valid = '0;
      assign dec_aw_idx = '0;
    end

    // Convert multicast rules to mask (NAPOT) form
    // - mask =  {'0, {log2(end_addr - start_addr){1'b1}}}
    // - addr = start_addr / (end_addr - start_addr)
    // More info in `multiaddr_decode` module
    // TODO colluca: add checks on conversion feasibility
    for (genvar i = 0; i < NoMulticastRules; i++) begin : g_multicast_rules
      assign multicast_rules[i].idx = addr_map_i[i].idx;
      assign multicast_rules[i].mask = addr_map_i[i].end_addr - addr_map_i[i].start_addr - 1;
      assign multicast_rules[i].addr = addr_map_i[i].start_addr;
    end

    // Compare request against {addr, mask} rules
    multiaddr_decode #(
      .NoIndices(NoMulticastPorts),
      .NoRules(NoMulticastRules),
      .addr_t (aw_addr_t),
      .rule_t (mask_rule_t)
    ) i_axi_aw_mask_decode (
      .addr_map_i (multicast_rules),
      .addr_i     (slv_aw_chan.addr),
      .mask_i     (slv_aw_chan.user.mcast),
      .select_o   (dec_aw_select_partial),
      .addr_o     (dec_aw_addr),
      .mask_o     (dec_aw_mask),
      .dec_valid_o(),
      .dec_error_o(dec_aw_select_error)
    );

    // Combine output from the two address decoders
    // Note: assumes the slaves targeted by multicast lie at the lower indices
    assign dec_aw_select = (dec_aw_idx_valid << dec_aw_idx) | dec_aw_select_partial;

    assign slv_aw_select_mask = (dec_aw_idx_error && dec_aw_select_error) ?
        {1'b1, {(NoMstPorts-1){1'b0}}} : {1'b0, dec_aw_select};
    assign slv_aw_addr = {'0, {(NoMstPorts-NoMulticastPorts){slv_aw_chan.addr}}, dec_aw_addr};
    assign slv_aw_mask = {'0, dec_aw_mask};

    // Control of the AW handshake
    always_comb begin
      // AXI Handshakes
      slv_aw_ready = 1'b0;
      aw_valid     = 1'b0;
      // `lock_aw_valid`, used to be protocol conform as it is not allowed to deassert
      // a valid if there was no corresponding ready. As this process has to be able to inject
      // an AXI ID into the counter of the AR channel on an ATOP, there could be a case where
      // this process waits on `aw_ready` but in the mean time on the AR channel the counter gets
      // full.
      lock_aw_valid_d = lock_aw_valid_q;
      load_aw_lock    = 1'b0;
      // AW ID counter and W FIFO
      w_cnt_up        = 1'b0;
      // ATOP injection into ar counter
      atop_inject     = 1'b0;
      // we had an arbitration decision, the valid is locked, wait for the transaction
      if (lock_aw_valid_q) begin
        aw_valid = 1'b1;
        // transaction
        if (aw_ready) begin
          slv_aw_ready    = 1'b1;
          lock_aw_valid_d = 1'b0;
          load_aw_lock    = 1'b1;
          // inject the ATOP if necessary
          atop_inject     = slv_aw_chan.atop[axi_pkg::ATOP_R_RESP] & AtopSupport;
        end
      end else begin
        // An AW can be handled if `i_aw_id_counter` and `i_counter_open_w` are not full.  An ATOP that
        // requires an R response can be handled if additionally `i_ar_id_counter` is not full (this
        // only applies if ATOPs are supported at all).
        if (!aw_id_cnt_full && (w_open != {IdCounterWidth{1'b1}}) &&
            (!(ar_id_cnt_full && slv_aw_chan.atop[axi_pkg::ATOP_R_RESP]) ||
             !AtopSupport)) begin
          // There is a valid AW vector make the id lookup and go further, if it passes.
          // Also stall if previous transmitted AWs still have active W's in flight.
          // This prevents deadlocking of the W channel. The counters are there for the
          // Handling of the B responses.
          if (slv_aw_valid &&
                ((w_open == '0) || (w_select == slv_aw_select_mask)) &&
                (!aw_select_occupied || (slv_aw_select == lookup_aw_select)) &&
                !multicast_stall) begin
            // connect the handshake
            aw_valid     = 1'b1;
            // push arbitration to the W FIFO regardless, do not wait for the AW transaction
            w_cnt_up     = 1'b1;
            // on AW transaction
            if (aw_ready) begin
              slv_aw_ready = 1'b1;
              atop_inject  = slv_aw_chan.atop[axi_pkg::ATOP_R_RESP] & AtopSupport;
            // no AW transaction this cycle, lock the decision
            end else begin
              lock_aw_valid_d = 1'b1;
              load_aw_lock    = 1'b1;
            end
          end
        end
      end
    end

    // lock the valid signal, as the selection gets pushed into the W FIFO on first assertion,
    // prevent further pushing
    `FFLARN(lock_aw_valid_q, lock_aw_valid_d, load_aw_lock, '0, clk_i, rst_ni)

    /// Multicast logic

    // Convert AW select mask to select index since the indices
    // are smaller than the masks and thus cheaper to store in
    // the ID counters. We anyways don't use the ID counters on
    // multicast transactions...

    onehot_to_bin #(
      .ONEHOT_WIDTH(NoMstPorts)
    ) i_onehot_to_bin  (
        .onehot(slv_aw_select_mask & {NoMstPorts{!aw_is_multicast}}),
        .bin   (slv_aw_select)
    );

    // Popcount to identify multicast requests
    popcount #(NoMstPorts) i_aw_select_popcount (
        .data_i    (slv_aw_select_mask),
        .popcount_o(aw_select_popcount)
    );

    // While there can be multiple outstanding write transactions, i.e. 
    // multiple AWs can be accepted before the corresponding Bs are returned,
    // in the case of multicast transactions this would require the need
    // for additional (possibly expensive) hardware.
    // The reason is that multicast transactions require merging multiple B
    // responses arriving on different master ports. To know which master ports
    // need to be merged we need to register the select signal of the
    // write transaction. And if we allow multiple outstanding transactions
    // we need to register the select signal of each, and we need a big
    // associative (by ID) table for this. And actually this still allows
    // deadlocks to occur, e.g. if two multicast transactions A and B are partially
    // reordered, i.e. some masters respond to A first and some to B.
    // If we restrict the outstanding transactions to a single ID then ordering is
    // guaranteed, but we anyways need a FIFO to store the selects.
    // So for the moment we disallow multiple outstanding transactions in presence
    // of a multicast. This means stall an AW request if:
    // - there is an outstanding multicast transaction or
    // - if the request is a multicast, until there are no more outstanding transactions
    assign aw_is_multicast        = aw_select_popcount > 1;
    assign outstanding_multicast  = |multicast_select_q;
    assign aw_any_outstanding_trx = aw_any_outstanding_unicast_trx || outstanding_multicast;
    assign multicast_stall        = outstanding_multicast || (aw_is_multicast && aw_any_outstanding_trx);
    // We can send this signal to all slaves since we will only have one outstanding aw
    assign mst_is_mcast_o = {NoMstPorts{aw_is_multicast}};

    // Keep track of which B responses need to be returned to complete the multicast
    `FFLARN(multicast_select_q, multicast_select_d, multicast_select_load, '0, clk_i, rst_ni)

    // Logic to update multicast_select_q. Loads the register upon the AW handshake
    // of a multicast transaction. Successively clears it upon the "joined" B handshake
    always_comb begin
      multicast_select_d = multicast_select_q;
      multicast_select_load = 1'b0;

      unique if (aw_is_multicast && aw_valid && aw_ready) begin
        multicast_select_d    = slv_aw_select_mask;
        multicast_select_load = 1'b1;
      end else if (outstanding_multicast && slv_b_valid && slv_b_ready) begin
        multicast_select_d    = '0;
        multicast_select_load = 1'b1;
      end else begin
        multicast_select_d = multicast_select_q;
        multicast_select_load = 1'b0;
      end
    end

    // Multicast AW transaction handshake state
    typedef enum logic {MCastAwHandshakeIdle, MCastAwHandshakeInProgress} mcast_aw_hs_state_e;
    mcast_aw_hs_state_e mcast_aw_hs_state_q, mcast_aw_hs_state_d;

    // Update of the multicast AW handshake state
    always_comb begin
      mcast_aw_hs_state_d = mcast_aw_hs_state_q;
      unique case (mcast_aw_hs_state_q)
        // Waiting for all selected master ports to be ready
        MCastAwHandshakeIdle:
          if (accept_aw && aw_is_multicast) begin
            mcast_aw_hs_state_d = MCastAwHandshakeInProgress;
          end
        // Commit is asserted and handshake takes place in the current cycle.
        // In the next cycle we are again idle
        MCastAwHandshakeInProgress:
          mcast_aw_hs_state_d = MCastAwHandshakeIdle;
      endcase
    end

    assign mcast_aw_hs_in_progress = mcast_aw_hs_state_q == MCastAwHandshakeInProgress;

    `FFARN(mcast_aw_hs_state_q, mcast_aw_hs_state_d, MCastAwHandshakeIdle, clk_i, rst_ni)

    // When a multicast occurs, the upstream valid signals need to
    // be forwarded to multiple master ports.
    // Proper stream forking is necessary to avoid protocol violations.
    // We must also require that downstream handshakes occur
    // simultaneously on all addressed master ports, otherwise deadlocks
    // may occur. To achieve this we modify the ready-valid protocol by adding
    // a third signal, called commit, which is asserted only when we have all
    // downstream handshakes. This signal notifies the slaves that the
    // handshake can now actually take place.
    // Using commit, instead of valid, to this end ensures that we don't have
    // any combinational loops.
    assign mst_aw_valids = {NoMstPorts{aw_valid}} & slv_aw_select_mask;
    assign accept_aw = &((mst_aw_valids & mst_aw_readies) | ~slv_aw_select_mask);
    assign aw_ready = aw_is_multicast ? mcast_aw_hs_in_progress : accept_aw;
    assign mst_aw_commit_o = {NoMstPorts{mcast_aw_hs_in_progress}} & slv_aw_select_mask;

    if (UniqueIds) begin : gen_unique_ids_aw
      // If the `UniqueIds` parameter is set, each write transaction has an ID that is unique among
      // all in-flight write transactions, or all write transactions with a given ID target the same
      // master port as all write transactions with the same ID, or both.  This means that the
      // signals that are driven by the ID counters if this parameter is not set can instead be
      // derived from existing signals.  The ID counters can therefore be omitted.
      assign lookup_aw_select = slv_aw_select;
      assign aw_select_occupied = 1'b0;

      // We still need a (single) counter to keep track of any outstanding transactions
      axi_mcast_demux_id_counters #(
        .AxiIdBits         ( 0              ),
        .CounterWidth      ( IdCounterWidth ),
        .mst_port_select_t ( idx_select_t   )
      ) i_aw_id_counter (
        .clk_i                        ( clk_i                          ),
        .rst_ni                       ( rst_ni                         ),
        .lookup_axi_id_i              ( '0                             ),
        .lookup_mst_select_o          ( /* Not used */                 ),
        .lookup_mst_select_occupied_o ( /* Not used */                 ),
        .full_o                       ( aw_id_cnt_full                 ),
        .inject_axi_id_i              ( '0                             ),
        .inject_i                     ( 1'b0                           ),
        .push_axi_id_i                ( '0                             ),
        .push_mst_select_i            ( '0                             ),
        .push_i                       ( w_cnt_up && !aw_is_multicast   ),
        .pop_axi_id_i                 ( '0                             ),
        .pop_i                        ( slv_b_valid & slv_b_ready & ~outstanding_multicast ),
        .any_outstanding_trx_o        ( aw_any_outstanding_unicast_trx )
      );

    end else begin : gen_aw_id_counter

      axi_mcast_demux_id_counters #(
        .AxiIdBits         ( AxiLookBits    ),
        .CounterWidth      ( IdCounterWidth ),
        .mst_port_select_t ( idx_select_t   )
      ) i_aw_id_counter (
        .clk_i                        ( clk_i                          ),
        .rst_ni                       ( rst_ni                         ),
        .lookup_axi_id_i              ( slv_aw_chan.id[0+:AxiLookBits] ),
        .lookup_mst_select_o          ( lookup_aw_select               ),
        .lookup_mst_select_occupied_o ( aw_select_occupied             ),
        .full_o                       ( aw_id_cnt_full                 ),
        .inject_axi_id_i              ( '0                             ),
        .inject_i                     ( 1'b0                           ),
        .push_axi_id_i                ( slv_aw_chan.id[0+:AxiLookBits] ),
        .push_mst_select_i            ( slv_aw_select                  ),
        .push_i                       ( w_cnt_up && !aw_is_multicast   ),
        .pop_axi_id_i                 ( slv_b_chan.id[0+:AxiLookBits]  ),
        .pop_i                        ( slv_b_valid & slv_b_ready & ~outstanding_multicast ),
        .any_outstanding_trx_o        ( aw_any_outstanding_unicast_trx )
      );
      // pop from ID counter on outward transaction
    end

    // This counter steers the demultiplexer of the W channel.
    // `w_select` determines, which handshaking is connected.
    // AWs are only forwarded, if the counter is empty, or `w_select_q` is the same as
    // `slv_aw_select`.
    counter #(
      .WIDTH           ( IdCounterWidth ),
      .STICKY_OVERFLOW ( 1'b0           )
    ) i_counter_open_w (
      .clk_i,
      .rst_ni,
      .clear_i    ( 1'b0                  ),
      .en_i       ( w_cnt_up ^ w_cnt_down ),
      .load_i     ( 1'b0                  ),
      .down_i     ( w_cnt_down            ),
      .d_i        ( '0                    ),
      .q_o        ( w_open                ),
      .overflow_o ( /*not used*/          )
    );

    `FFLARN(w_select_q, slv_aw_select_mask, w_cnt_up, mask_select_t'(0), clk_i, rst_ni)
    assign w_select       = (|w_open) ? w_select_q : slv_aw_select_mask;
    assign w_select_valid = w_cnt_up | (|w_open);
    assign w_cnt_down     = slv_w_valid & slv_w_ready & slv_w_chan.last;

    //--------------------------------------
    //  W Channel
    //--------------------------------------
    spill_register #(
      .T       ( w_chan_t ),
      .Bypass  ( ~SpillW  )
    ) i_w_spill_reg(
      .clk_i   ( clk_i              ),
      .rst_ni  ( rst_ni             ),
      .valid_i ( slv_req_i.w_valid  ),
      .ready_o ( slv_resp_o.w_ready ),
      .data_i  ( slv_req_i.w        ),
      .valid_o ( slv_w_valid        ),
      .ready_i ( slv_w_ready        ),
      .data_o  ( slv_w_chan         )
    );

    // When a multicast occurs, the upstream valid signals need to
    // be forwarded to multiple master ports.
    // Proper stream forking is necessary to avoid protocol violations
    stream_fork_dynamic #(
      .N_OUP(NoMstPorts)
    ) i_w_stream_fork_dynamic (
      .clk_i      (clk_i),
      .rst_ni     (rst_ni),
      .valid_i    (slv_w_valid),
      .ready_o    (slv_w_ready),
      .sel_i      (w_select),
      .sel_valid_i(w_select_valid),
      .sel_ready_o(),
      .valid_o    (mst_w_valids),
      .ready_i    (mst_w_readies)
    );

    //--------------------------------------
    //  B Channel
    //--------------------------------------
    // optional spill register
    spill_register #(
      .T       ( b_chan_t ),
      .Bypass  ( ~SpillB  )
    ) i_b_spill_reg (
      .clk_i   ( clk_i              ),
      .rst_ni  ( rst_ni             ),
      .valid_i ( slv_b_valid        ),
      .ready_o ( slv_b_ready        ),
      .data_i  ( slv_b_chan         ),
      .valid_o ( slv_resp_o.b_valid ),
      .ready_i ( slv_req_i.b_ready  ),
      .data_o  ( slv_resp_o.b       )
    );

    // Arbitration of the different B responses
    rr_arb_tree #(
      .NumIn    ( NoMstPorts ),
      .DataType ( b_chan_t   ),
      .AxiVldRdy( 1'b1       ),
      .LockIn   ( 1'b1       )
    ) i_b_mux (
      .clk_i  ( clk_i         ),
      .rst_ni ( rst_ni        ),
      .flush_i( 1'b0          ),
      .rr_i   ( '0            ),
      .req_i  ( mst_b_valids & {NoMstPorts{!outstanding_multicast}} ),
      .gnt_o  ( mst_b_readies_arb ),
      .data_i ( mst_b_chans   ),
      .gnt_i  ( slv_b_ready   ),
      .req_o  ( slv_b_valid_arb ),
      .data_o ( slv_b_chan_arb ),
      .idx_o  (               )
    );

    // Streams must be joined instead of arbitrated when multicast
    stream_join_dynamic #(NoMstPorts) i_b_stream_join (
      .inp_valid_i(mst_b_valids & {NoMstPorts{outstanding_multicast}}),
      .inp_ready_o(mst_b_readies_join),
      .sel_i      (multicast_select_q),
      .oup_valid_o(slv_b_valid_join),
      .oup_ready_i(slv_b_ready)
    );
    for (genvar i=0; i<NoMstPorts; i++) begin : g_mst_b_resps
      assign mst_b_resps[i] = multicast_select_q[i] ? mst_b_chans[i].resp : axi_pkg::RESP_OKAY;
    end
    // All fields of B other than RESP can be taken from any slave (need not be merged).
    // We use a priority encoder to take them from the first addressed slave.
    lzc #(
      .WIDTH ( NoMstPorts ),
      .MODE  ( 1'b0       ) // Trailing zero mode
    ) i_mst_b_valids_tzc (
      .in_i    ( mst_b_valids & {NoMstPorts{outstanding_multicast}} ),
      .cnt_o   ( mst_b_valids_tzc                                   ),
      .empty_o ( /* Not used */                                     )
    );
    always_comb begin
      slv_b_chan_join = mst_b_chans[mst_b_valids_tzc];
      // If a response to a multicast transaction from any slave is different
      // from OKAY, we return SLVERR. Note: we assume multicast transactions
      // cannot be exclusive requests, i.e. the EX_OKAY response is not allowed.
      slv_b_chan_join.resp = |mst_b_resps ? axi_pkg::RESP_SLVERR : axi_pkg::RESP_OKAY;
    end

    // Mux output of arbiter and stream_join_dynamic modules
    assign mst_b_readies = mst_b_readies_arb | mst_b_readies_join;
    assign slv_b_valid   = slv_b_valid_arb | slv_b_valid_join;
    assign slv_b_chan    = outstanding_multicast ? slv_b_chan_join : slv_b_chan_arb;

    //--------------------------------------
    //  AR Channel
    //--------------------------------------
    ar_chan_t slv_ar_chan;
    idx_select_t slv_ar_select;
    spill_register #(
      .T       ( ar_chan_t          ),
      .Bypass  ( ~SpillAr           )
    ) i_ar_chan_spill_reg (
      .clk_i   ( clk_i              ),
      .rst_ni  ( rst_ni             ),
      .valid_i ( slv_req_i.ar_valid ),
      .ready_o ( slv_ar_ready_chan  ),
      .data_i  ( slv_req_i.ar       ),
      .valid_o ( ar_valid_chan      ),
      .ready_i ( slv_ar_ready       ),
      .data_o  ( slv_ar_chan        )
    );
    spill_register #(
      .T       ( idx_select_t       ),
      .Bypass  ( ~SpillAr           )
    ) i_ar_sel_spill_reg (
      .clk_i   ( clk_i              ),
      .rst_ni  ( rst_ni             ),
      .valid_i ( slv_req_i.ar_valid ),
      .ready_o ( slv_ar_ready_sel   ),
      .data_i  ( slv_ar_select_i    ),
      .valid_o ( ar_valid_sel       ),
      .ready_i ( slv_ar_ready       ),
      .data_o  ( slv_ar_select      )
    );
    assign slv_resp_o.ar_ready = slv_ar_ready_chan & slv_ar_ready_sel;
    assign slv_ar_valid = ar_valid_chan & ar_valid_sel;

    // control of the AR handshake
    always_comb begin
      // AXI Handshakes
      slv_ar_ready    = 1'b0;
      ar_valid        = 1'b0;
      // `lock_ar_valid`: Used to be protocol conform as it is not allowed to deassert `ar_valid`
      // if there was no corresponding `ar_ready`. There is the possibility that an injection
      // of a R response from an `atop` from the AW channel can change the occupied flag of the
      // `i_ar_id_counter`, even if it was previously empty. This FF prevents the deassertion.
      lock_ar_valid_d = lock_ar_valid_q;
      load_ar_lock    = 1'b0;
      // AR id counter
      ar_push         = 1'b0;
      // The process had an arbitration decision in a previous cycle, the valid is locked,
      // wait for the AR transaction.
      if (lock_ar_valid_q) begin
        ar_valid = 1'b1;
        // transaction
        if (ar_ready) begin
          slv_ar_ready    = 1'b1;
          ar_push         = 1'b1;
          lock_ar_valid_d = 1'b0;
          load_ar_lock    = 1'b1;
        end
      end else begin
        // The process can start handling AR transaction if `i_ar_id_counter` has space.
        if (!ar_id_cnt_full) begin
          // There is a valid AR, so look the ID up.
          if (slv_ar_valid && (!ar_select_occupied ||
             (slv_ar_select == lookup_ar_select))) begin
            // connect the AR handshake
            ar_valid     = 1'b1;
            // on transaction
            if (ar_ready) begin
              slv_ar_ready = 1'b1;
              ar_push      = 1'b1;
            // no transaction this cycle, lock the valid decision!
            end else begin
              lock_ar_valid_d = 1'b1;
              load_ar_lock    = 1'b1;
            end
          end
        end
      end
    end

    // this ff is needed so that ar does not get de-asserted if an atop gets injected
    `FFLARN(lock_ar_valid_q, lock_ar_valid_d, load_ar_lock, '0, clk_i, rst_ni)

    if (UniqueIds) begin : gen_unique_ids_ar
      // If the `UniqueIds` parameter is set, each read transaction has an ID that is unique among
      // all in-flight read transactions, or all read transactions with a given ID target the same
      // master port as all read transactions with the same ID, or both.  This means that the
      // signals that are driven by the ID counters if this parameter is not set can instead be
      // derived from existing signals.  The ID counters can therefore be omitted.
      assign lookup_ar_select = slv_ar_select;
      assign ar_select_occupied = 1'b0;
      assign ar_id_cnt_full = 1'b0;
    end else begin : gen_ar_id_counter
      axi_demux_id_counters #(
        .AxiIdBits         ( AxiLookBits    ),
        .CounterWidth      ( IdCounterWidth ),
        .mst_port_select_t ( idx_select_t   )
      ) i_ar_id_counter (
        .clk_i                        ( clk_i                                       ),
        .rst_ni                       ( rst_ni                                      ),
        .lookup_axi_id_i              ( slv_ar_chan.id[0+:AxiLookBits]              ),
        .lookup_mst_select_o          ( lookup_ar_select                            ),
        .lookup_mst_select_occupied_o ( ar_select_occupied                          ),
        .full_o                       ( ar_id_cnt_full                              ),
        .inject_axi_id_i              ( slv_aw_chan.id[0+:AxiLookBits]              ),
        .inject_i                     ( atop_inject                                 ),
        .push_axi_id_i                ( slv_ar_chan.id[0+:AxiLookBits]              ),
        .push_mst_select_i            ( slv_ar_select                               ),
        .push_i                       ( ar_push                                     ),
        .pop_axi_id_i                 ( slv_r_chan.id[0+:AxiLookBits]               ),
        .pop_i                        ( slv_r_valid & slv_r_ready & slv_r_chan.last )
      );
    end

    //--------------------------------------
    //  R Channel
    //--------------------------------------
    // optional spill register
    spill_register #(
      .T       ( r_chan_t ),
      .Bypass  ( ~SpillR  )
    ) i_r_spill_reg (
      .clk_i   ( clk_i              ),
      .rst_ni  ( rst_ni             ),
      .valid_i ( slv_r_valid        ),
      .ready_o ( slv_r_ready        ),
      .data_i  ( slv_r_chan         ),
      .valid_o ( slv_resp_o.r_valid ),
      .ready_i ( slv_req_i.r_ready  ),
      .data_o  ( slv_resp_o.r       )
    );

    // Arbitration of the different r responses
    rr_arb_tree #(
      .NumIn    ( NoMstPorts ),
      .DataType ( r_chan_t   ),
      .AxiVldRdy( 1'b1       ),
      .LockIn   ( 1'b1       )
    ) i_r_mux (
      .clk_i  ( clk_i         ),
      .rst_ni ( rst_ni        ),
      .flush_i( 1'b0          ),
      .rr_i   ( '0            ),
      .req_i  ( mst_r_valids  ),
      .gnt_o  ( mst_r_readies ),
      .data_i ( mst_r_chans   ),
      .gnt_i  ( slv_r_ready   ),
      .req_o  ( slv_r_valid   ),
      .data_o ( slv_r_chan    ),
      .idx_o  (               )
    );

    assign ar_ready = ar_valid & mst_resps_i[slv_ar_select].ar_ready;

    // process that defines the individual demuxes and assignments for the arbitration
    // as mst_reqs_o has to be driven from the same always comb block!
    always_comb begin
      // default assignments
      mst_reqs_o  = '0;

      for (int unsigned i = 0; i < NoMstPorts; i++) begin
        // AW channel
        mst_reqs_o[i].aw            = slv_aw_chan;
        mst_reqs_o[i].aw.addr       = slv_aw_addr[i];
        mst_reqs_o[i].aw.user.mcast = slv_aw_mask[i];
        mst_reqs_o[i].aw_valid      = mst_aw_valids[i];

        //  W channel
        mst_reqs_o[i].w       = slv_w_chan;
        mst_reqs_o[i].w_valid = mst_w_valids[i];

        //  B channel
        mst_reqs_o[i].b_ready = mst_b_readies[i];

        // AR channel
        mst_reqs_o[i].ar       = slv_ar_chan;
        mst_reqs_o[i].ar_valid = 1'b0;
        if (ar_valid && (slv_ar_select == i)) begin
          mst_reqs_o[i].ar_valid = 1'b1;
        end

        //  R channel
        mst_reqs_o[i].r_ready = mst_r_readies[i];
      end
    end
    // unpack the response AW, W, R and B channels for the arbitration/muxes
    for (genvar i = 0; i < NoMstPorts; i++) begin : gen_b_channels
      assign mst_b_chans[i]        = mst_resps_i[i].b;
      assign mst_b_valids[i]       = mst_resps_i[i].b_valid;
      assign mst_r_chans[i]        = mst_resps_i[i].r;
      assign mst_r_valids[i]       = mst_resps_i[i].r_valid;
      assign mst_w_readies[i]      = mst_resps_i[i].w_ready;
      assign mst_aw_readies[i]     = mst_resps_i[i].aw_ready;
    end


// Validate parameters.
// pragma translate_off
`ifndef VERILATOR
`ifndef XSIM
    initial begin: validate_params
      no_mst_ports: assume (NoMstPorts > 0) else
        $fatal(1, "The Number of slaves (NoMstPorts) has to be at least 1");
      AXI_ID_BITS:  assume (AxiIdWidth >= AxiLookBits) else
        $fatal(1, "AxiIdBits has to be equal or smaller than AxiIdWidth.");
      aw_addr_bits: assume ($bits(slv_aw_addr[0]) == $bits(slv_req_i.aw.addr)) else
        $fatal(1, "aw_addr_t must be the type of slv_req_i.aw.addr");
    end
    default disable iff (!rst_ni);
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
                               |=> $stable(slv_aw_chan)) else
      $fatal(1, "slv_aw_chan unstable with valid set.");
    slv_aw_select_stable: assert property( @(posedge clk_i) (aw_valid && !aw_ready)
                               |=> $stable(slv_aw_select)) else
      $fatal(1, "slv_aw_select unstable with valid set.");
    slv_ar_chan_stable: assert property( @(posedge clk_i) (ar_valid && !ar_ready)
                               |=> $stable(slv_ar_chan)) else
      $fatal(1, "slv_ar_chan unstable with valid set.");
    slv_ar_select_stable: assert property( @(posedge clk_i) (ar_valid && !ar_ready)
                               |=> $stable(slv_ar_select)) else
      $fatal(1, "slv_ar_select unstable with valid set.");
    internal_ar_select: assert property( @(posedge clk_i)
        (ar_valid |-> slv_ar_select < NoMstPorts))
      else $fatal(1, "slv_ar_select illegal while ar_valid.");
    w_underflow: assert property( @(posedge clk_i)
        ((w_open == '0) && (w_cnt_up ^ w_cnt_down) |-> !w_cnt_down)) else
        $fatal(1, "W counter underflowed!");
    `ASSUME(NoAtopAllowed, !AtopSupport && slv_req_i.aw_valid |-> slv_req_i.aw.atop == '0)
`endif
`endif
// pragma translate_on
  end
endmodule

module axi_mcast_demux_id_counters #(
  // the lower bits of the AXI ID that should be considered, results in 2**AXI_ID_BITS counters
  parameter int unsigned AxiIdBits         = 2,
  parameter int unsigned CounterWidth      = 4,
  parameter type         mst_port_select_t = logic
) (
  input                        clk_i,   // Clock
  input                        rst_ni,  // Asynchronous reset active low
  // lookup
  input  logic [AxiIdBits-1:0] lookup_axi_id_i,
  output mst_port_select_t     lookup_mst_select_o,
  output logic                 lookup_mst_select_occupied_o,
  // push
  output logic                 full_o,
  input  logic [AxiIdBits-1:0] push_axi_id_i,
  input  mst_port_select_t     push_mst_select_i,
  input  logic                 push_i,
  // inject ATOPs in AR channel
  input  logic [AxiIdBits-1:0] inject_axi_id_i,
  input  logic                 inject_i,
  // pop
  input  logic [AxiIdBits-1:0] pop_axi_id_i,
  input  logic                 pop_i,
  // outstanding transactions
  output logic                 any_outstanding_trx_o
);
  localparam int unsigned NoCounters = 2**AxiIdBits;
  typedef logic [CounterWidth-1:0] cnt_t;

  // registers, each gets loaded when push_en[i]
  mst_port_select_t [NoCounters-1:0] mst_select_q;

  // counter signals
  logic [NoCounters-1:0] push_en, inject_en, pop_en, occupied, cnt_full;

  //-----------------------------------
  // Lookup
  //-----------------------------------
  assign lookup_mst_select_o          = mst_select_q[lookup_axi_id_i];
  assign lookup_mst_select_occupied_o = occupied[lookup_axi_id_i];
  //-----------------------------------
  // Push and Pop
  //-----------------------------------
  assign push_en   = (push_i)   ? (1 << push_axi_id_i)   : '0;
  assign inject_en = (inject_i) ? (1 << inject_axi_id_i) : '0;
  assign pop_en    = (pop_i)    ? (1 << pop_axi_id_i)    : '0;
  assign full_o    = |cnt_full;
  //-----------------------------------
  // Status
  //-----------------------------------
  assign any_outstanding_trx_o = |occupied;

  // counters
  for (genvar i = 0; i < NoCounters; i++) begin : gen_counters
    logic cnt_en, cnt_down, overflow;
    cnt_t cnt_delta, in_flight;
    always_comb begin
      unique case ({push_en[i], inject_en[i], pop_en[i]})
        3'b001  : begin // pop_i = -1
          cnt_en    = 1'b1;
          cnt_down  = 1'b1;
          cnt_delta = cnt_t'(1);
        end
        3'b010  : begin // inject_i = +1
          cnt_en    = 1'b1;
          cnt_down  = 1'b0;
          cnt_delta = cnt_t'(1);
        end
     // 3'b011, inject_i & pop_i = 0 --> use default
        3'b100  : begin // push_i = +1
          cnt_en    = 1'b1;
          cnt_down  = 1'b0;
          cnt_delta = cnt_t'(1);
        end
     // 3'b101, push_i & pop_i = 0 --> use default
        3'b110  : begin // push_i & inject_i = +2
          cnt_en    = 1'b1;
          cnt_down  = 1'b0;
          cnt_delta = cnt_t'(2);
        end
        3'b111  : begin // push_i & inject_i & pop_i = +1
          cnt_en    = 1'b1;
          cnt_down  = 1'b0;
          cnt_delta = cnt_t'(1);
        end
        default : begin // do nothing to the counters
          cnt_en    = 1'b0;
          cnt_down  = 1'b0;
          cnt_delta = cnt_t'(0);
        end
      endcase
    end

    delta_counter #(
      .WIDTH           ( CounterWidth ),
      .STICKY_OVERFLOW ( 1'b0         )
    ) i_in_flight_cnt (
      .clk_i      ( clk_i     ),
      .rst_ni     ( rst_ni    ),
      .clear_i    ( 1'b0      ),
      .en_i       ( cnt_en    ),
      .load_i     ( 1'b0      ),
      .down_i     ( cnt_down  ),
      .delta_i    ( cnt_delta ),
      .d_i        ( '0        ),
      .q_o        ( in_flight ),
      .overflow_o ( overflow  )
    );
    assign occupied[i] = |in_flight;
    assign cnt_full[i] = overflow | (&in_flight);

    // holds the selection signal for this id
    `FFLARN(mst_select_q[i], push_mst_select_i, push_en[i], '0, clk_i, rst_ni)

// pragma translate_off
`ifndef VERILATOR
`ifndef XSIM
    // Validate parameters.
    cnt_underflow: assert property(
      @(posedge clk_i) disable iff (~rst_ni) (pop_en[i] |=> !overflow)) else
        $fatal(1, "axi_demux_id_counters > Counter: %0d underflowed.\
                   The reason is probably a faulty AXI response.", i);
`endif
`endif
// pragma translate_on
  end
endmodule

// interface wrapper
`include "axi/assign.svh"
`include "axi/typedef.svh"
module axi_mcast_demux_intf #(
  parameter int unsigned AXI_ID_WIDTH     = 32'd0, // Synopsys DC requires default value for params
  parameter bit          ATOP_SUPPORT     = 1'b1,
  parameter int unsigned AXI_ADDR_WIDTH   = 32'd0,
  parameter int unsigned AXI_DATA_WIDTH   = 32'd0,
  parameter int unsigned AXI_USER_WIDTH   = 32'd0,
  parameter int unsigned NO_MST_PORTS     = 32'd3,
  parameter int unsigned MAX_TRANS        = 32'd8,
  parameter int unsigned AXI_LOOK_BITS    = 32'd3,
  parameter bit          UNIQUE_IDS       = 1'b0,
  parameter bit          SPILL_AW         = 1'b1,
  parameter bit          SPILL_W          = 1'b0,
  parameter bit          SPILL_B          = 1'b0,
  parameter bit          SPILL_AR         = 1'b1,
  parameter bit          SPILL_R          = 1'b0,
  parameter type         rule_t           = logic,
  // Dependent parameters, DO NOT OVERRIDE!
  parameter int unsigned SELECT_WIDTH   = (NO_MST_PORTS > 32'd1) ? $clog2(NO_MST_PORTS) : 32'd1,
  parameter type         idx_select_t   = logic [SELECT_WIDTH-1:0],
  parameter type         addr_t         = logic [AXI_ADDR_WIDTH-1:0]
) (
  input  logic    clk_i,                 // Clock
  input  logic    rst_ni,                // Asynchronous reset active low
  input  logic    test_i,                // Testmode enable
  input  rule_t [NO_MST_PORTS-2:0] addr_map_i,
  input  idx_select_t  slv_ar_select_i,  // has to be stable, when ar_valid
  AXI_BUS.Slave   slv,                   // slave port
  AXI_BUS.Master  mst [NO_MST_PORTS-1:0] // master ports
);

  typedef logic [AXI_ID_WIDTH-1:0]       id_t;
  typedef logic [AXI_DATA_WIDTH-1:0]   data_t;
  typedef logic [AXI_DATA_WIDTH/8-1:0] strb_t;
  typedef logic [AXI_USER_WIDTH-1:0]   user_t;
  `AXI_TYPEDEF_AW_CHAN_T(aw_chan_t, addr_t, id_t, user_t)
  `AXI_TYPEDEF_W_CHAN_T(w_chan_t, data_t, strb_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T(b_chan_t, id_t, user_t)
  `AXI_TYPEDEF_AR_CHAN_T(ar_chan_t, addr_t, id_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(r_chan_t, data_t, id_t, user_t)
  `AXI_TYPEDEF_REQ_T(axi_req_t, aw_chan_t, w_chan_t, ar_chan_t)
  `AXI_TYPEDEF_RESP_T(axi_resp_t, b_chan_t, r_chan_t)

  axi_req_t                     slv_req;
  axi_resp_t                    slv_resp;
  axi_req_t  [NO_MST_PORTS-1:0] mst_req;
  axi_resp_t [NO_MST_PORTS-1:0] mst_resp;

  `AXI_ASSIGN_TO_REQ(slv_req, slv)
  `AXI_ASSIGN_FROM_RESP(slv, slv_resp)

  for (genvar i = 0; i < NO_MST_PORTS; i++) begin : gen_assign_mst_ports
    `AXI_ASSIGN_FROM_REQ(mst[i], mst_req[i])
    `AXI_ASSIGN_TO_RESP(mst_resp[i], mst[i])
  end

  axi_mcast_demux #(
    .AxiIdWidth     ( AXI_ID_WIDTH  ), // ID Width
    .AtopSupport    ( ATOP_SUPPORT  ),
    .aw_addr_t      (     addr_t    ), // AW Address Type
    .aw_chan_t      (  aw_chan_t    ), // AW Channel Type
    .w_chan_t       (   w_chan_t    ), //  W Channel Type
    .b_chan_t       (   b_chan_t    ), //  B Channel Type
    .ar_chan_t      (  ar_chan_t    ), // AR Channel Type
    .r_chan_t       (   r_chan_t    ), //  R Channel Type
    .axi_req_t      (  axi_req_t    ),
    .axi_resp_t     ( axi_resp_t    ),
    .NoMstPorts     ( NO_MST_PORTS  ),
    .MaxTrans       ( MAX_TRANS     ),
    .AxiLookBits    ( AXI_LOOK_BITS ),
    .UniqueIds      ( UNIQUE_IDS    ),
    .SpillAw        ( SPILL_AW      ),
    .SpillW         ( SPILL_W       ),
    .SpillB         ( SPILL_B       ),
    .SpillAr        ( SPILL_AR      ),
    .SpillR         ( SPILL_R       ),
    .rule_t         ( rule_t        )
  ) i_axi_demux (
    .clk_i,   // Clock
    .rst_ni,  // Asynchronous reset active low
    .test_i,  // Testmode enable
    .addr_map_i      ( addr_map_i      ),
    // slave port
    .slv_req_i       ( slv_req         ),
    .slv_ar_select_i ( slv_ar_select_i ),
    .slv_resp_o      ( slv_resp        ),
    // master port
    .mst_reqs_o      ( mst_req         ),
    .mst_resps_i     ( mst_resp        )
  );
endmodule
