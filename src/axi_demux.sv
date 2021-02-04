// Copyright (c) 2019 ETH Zurich and University of Bologna.
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
// - Wolfgang Roenninger <wroennin@iis.ee.ethz.ch>
// - Andreas Kurth <akurth@iis.ee.ethz.ch>

`include "axi/typedef.svh"
`include "common_cells/registers.svh"

/// Demultiplex an AXI4 + ATOPs bus from one slave port to multiple master ports.
///
///
/// # Design Overview
///
/// The demultiplexer has one *slave port* and a configurable number of *master ports*.
/// A block diagram is shown below:
///
/// ![Block diagram of the AXI demultiplexer](axi_demux.png
/// "Block diagram of the AXI demultiplexer")
///
/// The AW and AR channels each have a *select* input, to determine the master port to which they
/// are sent.  The select can, for example, be driven by an (external) address decoder to map
/// address ranges to different AXI slaves.
///
/// Beats on the W channel are routed by demultiplexer according to the selection for the
/// corresponding AW beat.  This relies on the AXI property that W bursts must be sent in the same
/// order as AW beats and beats from different W bursts may not be interleaved.
///
/// Beats on the B and R channel are multiplexed from the master ports to the slave port with a
/// round-robin arbitration tree.
///
///
/// # Pipelining and Latency
///
/// The `SpillXX` parameters allow to insert spill register before each channel of the
/// demultiplexer.  Spill registers cut all combinatorial paths of a channel (i.e., both payload and
/// handshake).  Thus, they add one cycle of latency per channel but do not impair throughput.
///
/// If all `SpillXX` and `FallThrough` are disabled, all paths through this multiplexer are
/// combinatorial (i.e., have zero sequential latency).
///
///
/// # Ordering and Stalls
///
/// When the demultiplexer receives two transactions with the same ID and direction (i.e., both read
/// or both write) but targeting two different master ports, it will not accept the second
/// transaction until the first has completed.  During this time, the demultiplexer stalls the AR or
/// AW channel, respectively.  To determine whether two transactions have the same ID, the
/// `IdWidthUsed` least-significant bits are compared.  That parameter can be set to the full
/// `IdWidth` to avoid false ID conflicts, or it can be set to a lower value to reduce area and
/// delay at the cost of more false conflicts.
///
/// The reason for this behavior are AXI ordering constraints, see the [documentation of the
/// crossbar](module.axi_xbar.md) for details.
///
///
/// ## Implementation
///
/// `2 * 2^AxiLookBits` counters track the number of [in-flight](doc#in-flight) transactions.
/// That is, for each ID in the (potentially) reduced set of IDs of `IdWidthUsed` bits, there is one
/// counter for write transactions and one for read transactions.  Each counter can count up to (and
/// including) `MaxTxns`, and there is a register that holds the index of the master port to which a
/// counter is assigned (see [`axi_demux_id_counters`](module.axi_demux_id_counters)).
///
/// When the demultiplexer gets an AW or an AR, it indexes the counters with the AXI ID.  If the
/// indexed counter has a value greater than zero and its master port index register is not equal to
/// the index to which the AW or AR is to be sent, a transaction with the same direction and ID is
/// already in flight to another master port.  The demultiplexer then stalls the AW or AR.  In all
/// other cases, the demultiplexer forwards the AW or AR, increments the value of the indexed
/// counter, and sets the master port index of the counter.  A counter is decremented upon a
/// handshake a B respectively last R beat at a slave port.
///
/// W beats are routed to the master port defined by the value of `slv_aw_select_i` for the
/// corresponding AW.  As the order of the W bursts is given by the order of the AWs, the select
/// signals are stored in a FIFO queue.  This FIFO is pushed upon a handshake on the AW slave
/// channel and popped upon a handshake of the last W beat of a burst on a W master channel.
///
///
/// # Atomic Transactions
///
/// The demultiplexer also supports AXI atomic transactions (initiated by an AW with `atop` field
/// not equal to zero).  A part of AXI atomic transactions, namely atomic loads, require a response
/// on the B *and* the R channel.
///
/// ## Implementation
///
/// Atomic loads introduce a dependency between the read and write channels that otherwise does not
/// exist in AXI.  In this demultiplexer, the ID counters of the read channel must be aware of R
/// beats without a corresponding AR.  Otherwise, they would underflow upon atomic loads.  To
/// prevent this, the AW channel of the demultiplexer can "inject" the ID of an atomic load to the
/// ID counter of the AR channel.  This is possible because atomic transactions must have an ID that
/// is unique with respect to *all* other transactions (i.e., reads *and* writes) currently in
/// flight.
///
/// As only a part of the AXI ID is compared to determine whether two transactions have the same ID
/// (see section *Ordering and Stalls*), atomic loads can lead to additional false conflict stalls
/// on the read channel.  However, atomic transactions are short bursts and thus usually complete
/// relatively fast, so this should not reduce throughput under non-degenerate conditions.
///
module axi_demux #(
  /// The number of AXI master ports of the module.
  /// (In other words, how many AXI slave modules can be attached).
  parameter int unsigned NumMstPorts = 32'd0,
  /// AXI ID width of all ports.
  parameter int unsigned IdWidth = 32'd0,
  /// The number of slave port ID bits (starting at the least significant) the crossbar uses to
  /// determine the uniqueness of an AXI ID (see section *Ordering and Stalls* above).
  ///
  /// This value *must* follow `IdWidth >= IdWidthUsed && IdWidthUsed > 0`.
  ///
  /// Setting this to small values leads to less area, however on an increased stalling rate
  /// due to ID collisions.
  parameter int unsigned IdWidthUsed = 32'd0,
  /// AXI4+ATOP address field width.
  parameter int unsigned AddrWidth = 32'd0,
  /// AXI4+ATOP data field width.
  parameter int unsigned DataWidth = 32'd0,
  /// AXI4+ATOP user field width.
  parameter int unsigned UserWidth = 32'd0,
  /// Maximum number of open transactions that can be [in flight](doc/#in-flight) at the same time.
  parameter int unsigned MaxTxns = 32'd0,
  /// The internal FIFO from the AW channel to the W channel is in FallThrough mode.
  parameter bit FallThrough = 1'b0,
  /// Ass a spill register on the `AW` channel of the slave port.
  parameter bit SpillAw = 1'b1,
  /// Ass a spill register on the `W` channel of the slave port.
  parameter bit SpillW = 1'b0,
  /// Ass a spill register on the `B` channel of the slave port.
  parameter bit SpillB = 1'b0,
  /// Ass a spill register on the `AR` channel of the slave port.
  parameter bit SpillAr = 1'b1,
  /// Ass a spill register on the `R` channel of the slave port.
  parameter bit SpillR = 1'b0,
  /// AXI4+ATOP request struct type for a single port.
  parameter type axi_req_t = logic,
  /// AXI4+ATOP response struct type for a single port.
  parameter type axi_rsp_t = logic,
  /// Dependent parameter, do **not** override!
  /// Width of the selection signal specifying a master port.
  parameter int unsigned SelectWidth = cf_math_pkg::idx_width(NumMstPorts),
  /// Dependent parameter, do **not** override!
  /// Selection signal data type.
  parameter type select_t = logic [SelectWidth-1:0]
) (
  /// Clock, rising edge triggered.
  ///
  /// All other signals (except `rst_ni`) are synchronous to this signal.
  input  logic clk_i,
  /// Asynchronous reset, active low.
  input  logic rst_ni,
  /// Testmode enable, active high.
  input  logic test_i,
  /// AXI4+ATOP requests to the slave port.
  input  axi_req_t slv_port_req_i,
  /// Selection signal to which master port a write transaction should be routed.
  ///
  /// This signal has to be viewed as part of an `AW` beat. It has to be stable as long as
  /// `slv_port_req_i.aw_valid` is `1`.
  input  select_t  slv_port_aw_select_i,
  /// Selection signal to which master port a read transaction should be routed.
  ///
  /// This signal has to be viewed as part of an `AR` beat. It has to be stable as long as
  /// `slv_port_req_i.ar_valid` is `1`.
  input  select_t  slv_port_ar_select_i,
  /// AXI4+ATOP responses of the slave port.
  output axi_rsp_t slv_port_rsp_o,
  /// AXI4+ATOP requests of the master ports.
  output axi_req_t [NumMstPorts-1:0] mst_ports_req_o,
  /// AXI4+ATOP responses to the master ports.
  input  axi_rsp_t [NumMstPorts-1:0] mst_ports_rsp_i
);

  // Internal type definitions for the AXI4+ATOP channels.
  localparam int unsigned StrbWidth = DataWidth / 32'd8;
  typedef logic [IdWidth   -1:0] axi_id_t;
  typedef logic [AddrWidth -1:0] axi_addr_t;
  typedef logic [DataWidth -1:0] axi_data_t;
  typedef logic [StrbWidth -1:0] axi_strb_t;
  typedef logic [UserWidth -1:0] axi_user_t;

  `AXI_TYPEDEF_AW_CHAN_T(axi_aw_t, axi_addr_t, axi_id_t, axi_user_t)
  `AXI_TYPEDEF_W_CHAN_T(axi_w_t, axi_data_t, axi_strb_t, axi_user_t)
  `AXI_TYPEDEF_B_CHAN_T(axi_b_t, axi_id_t, axi_user_t)
  `AXI_TYPEDEF_AR_CHAN_T(axi_ar_t, axi_addr_t, axi_id_t, axi_user_t)
  `AXI_TYPEDEF_R_CHAN_T(axi_r_t, axi_data_t, axi_id_t, axi_user_t)

  // Type definition for the transaction counters.
  localparam int unsigned IdCounterWidth = cf_math_pkg::idx_width(MaxTxns);

  //--------------------------------------
  // Typedefs for the FIFOs / Queues
  //--------------------------------------
  typedef struct packed {
    axi_aw_t aw_chan;
    select_t aw_select;
  } aw_select_t;
  typedef struct packed {
    axi_ar_t ar_chan;
    select_t ar_select;
  } ar_select_t;

  // pass through if only one master port
  if (NumMstPorts == 32'h1) begin : gen_no_demux
    assign mst_ports_req_o[0] = slv_port_req_i;
    assign slv_port_rsp_o     = mst_ports_rsp_i[0];
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
    aw_select_t               slv_aw_chan_select;
    logic                     slv_aw_valid,       slv_aw_ready;

    // AW ID counter
    select_t                  lookup_aw_select;
    logic                     aw_select_occupied, aw_id_cnt_full;
    logic                     aw_push;
    // Upon an ATOP load, inject IDs from the AW into the AR channel
    logic                     atop_inject;

    // W FIFO: stores the decision to which master W beats should go
    logic                     w_fifo_pop;
    logic                     w_fifo_full,        w_fifo_empty;
    select_t                  w_select;

    // Register which locks the AW valid signal
    logic                     lock_aw_valid_d,    lock_aw_valid_q, load_aw_lock;
    logic                     aw_valid,           aw_ready;

    // W channel from spill reg
    axi_w_t                   slv_w_chan;
    logic                     slv_w_valid,        slv_w_ready;

    // B channels input into the arbitration
    axi_b_t [NumMstPorts-1:0] mst_b_chans;
    logic   [NumMstPorts-1:0] mst_b_valids,       mst_b_readies;

    // B channel to spill register
    axi_b_t                   slv_b_chan;
    logic                     slv_b_valid,        slv_b_ready;

    //--------------------------------------
    // Read Transaction
    //--------------------------------------
    // comes from spill register at input
    ar_select_t               slv_ar_chan_select;
    logic                     slv_ar_valid,       slv_ar_ready;

    // AR ID counter
    select_t                  lookup_ar_select;
    logic                     ar_select_occupied, ar_id_cnt_full;
    logic                     ar_push;

    // Register which locks the AR valid signal
    logic                     lock_ar_valid_d,    lock_ar_valid_q, load_ar_lock;
    logic                     ar_valid,           ar_ready;

    // R channels input into the arbitration
    axi_r_t [NumMstPorts-1:0] mst_r_chans;
    logic   [NumMstPorts-1:0] mst_r_valids, mst_r_readies;

    // R channel to spill register
    axi_r_t                   slv_r_chan;
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
    aw_select_t slv_aw_chan_select_in;
    assign      slv_aw_chan_select_in.aw_chan   = slv_port_req_i.aw;
    assign      slv_aw_chan_select_in.aw_select = slv_port_aw_select_i;

    spill_register #(
      .T       ( aw_select_t ),
      .Bypass  ( ~SpillAw    ) // because module param indicates if we want a spill reg
    ) i_aw_spill_reg (
      .clk_i,
      .rst_ni,
      .valid_i ( slv_port_req_i.aw_valid ),
      .ready_o ( slv_port_rsp_o.aw_ready ),
      .data_i  ( slv_aw_chan_select_in   ),
      .valid_o ( slv_aw_valid            ),
      .ready_i ( slv_aw_ready            ),
      .data_o  ( slv_aw_chan_select      )
    );

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
      aw_push      = 1'b0;
      // ATOP injection into ar counter
      atop_inject  = 1'b0;
      // we had an arbitration decision, the valid is locked, wait for the transaction
      if (lock_aw_valid_q) begin
        aw_valid = 1'b1;
        // transaction
        if (aw_ready) begin
          slv_aw_ready    = 1'b1;
          lock_aw_valid_d = 1'b0;
          load_aw_lock    = 1'b1;
          // inject the ATOP if necessary
          atop_inject     = slv_aw_chan_select.aw_chan.atop[axi_pkg::ATOP_R_RESP];
        end
      end else begin
        // Process can start handling a transaction if its `i_aw_id_counter` and `w_fifo` have
        // space in them. Further check if we could inject something on the AR channel.
        if (!aw_id_cnt_full && !w_fifo_full && !ar_id_cnt_full) begin
          // there is a valid AW vector make the id lookup and go further, if it passes
          if (slv_aw_valid && (!aw_select_occupied ||
             (slv_aw_chan_select.aw_select == lookup_aw_select))) begin
            // connect the handshake
            aw_valid     = 1'b1;
            // push arbitration to the W FIFO regardless, do not wait for the AW transaction
            aw_push      = 1'b1;
            // on AW transaction
            if (aw_ready) begin
              slv_aw_ready = 1'b1;
              atop_inject  = slv_aw_chan_select.aw_chan.atop[axi_pkg::ATOP_R_RESP];
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

    axi_demux_id_counters #(
      .AxiIdBits         ( IdWidthUsed    ),
      .CounterWidth      ( IdCounterWidth ),
      .mst_port_select_t ( select_t       )
    ) i_aw_id_counter (
      .clk_i                        ( clk_i                                         ),
      .rst_ni                       ( rst_ni                                        ),
      .lookup_axi_id_i              ( slv_aw_chan_select.aw_chan.id[0+:IdWidthUsed] ),
      .lookup_mst_select_o          ( lookup_aw_select                              ),
      .lookup_mst_select_occupied_o ( aw_select_occupied                            ),
      .full_o                       ( aw_id_cnt_full                                ),
      .inject_axi_id_i              ( '0                                            ),
      .inject_i                     ( 1'b0                                          ),
      .push_axi_id_i                ( slv_aw_chan_select.aw_chan.id[0+:IdWidthUsed] ),
      .push_mst_select_i            ( slv_aw_chan_select.aw_select                  ),
      .push_i                       ( aw_push                                       ),
      .pop_axi_id_i                 ( slv_b_chan.id[0+:IdWidthUsed]                 ),
      .pop_i                        ( slv_b_valid & slv_b_ready                     )
    );
    // pop from ID counter on outward transaction

    // FIFO to save W selection
    fifo_v3 #(
      .FALL_THROUGH ( FallThrough ),
      .DEPTH        ( MaxTxns     ),
      .dtype        ( select_t    )
    ) i_w_fifo (
      .clk_i     ( clk_i                        ),
      .rst_ni    ( rst_ni                       ),
      .flush_i   ( 1'b0                         ),
      .testmode_i( test_i                       ),
      .full_o    ( w_fifo_full                  ),
      .empty_o   ( w_fifo_empty                 ),
      .usage_o   (                              ),
      .data_i    ( slv_aw_chan_select.aw_select ),
      .push_i    ( aw_push                      ), // controlled from proc_aw_chan
      .data_o    ( w_select                     ), // where the w beat should go
      .pop_i     ( w_fifo_pop                   )  // controlled from proc_w_chan
    );

    //--------------------------------------
    //  W Channel
    //--------------------------------------
    spill_register #(
      .T       ( axi_w_t ),
      .Bypass  ( ~SpillW )
    ) i_w_spill_reg(
      .clk_i,
      .rst_ni,
      .valid_i ( slv_port_req_i.w_valid ),
      .ready_o ( slv_port_rsp_o.w_ready ),
      .data_i  ( slv_port_req_i.w       ),
      .valid_o ( slv_w_valid            ),
      .ready_i ( slv_w_ready            ),
      .data_o  ( slv_w_chan             )
    );

    //--------------------------------------
    //  B Channel
    //--------------------------------------
    // optional spill register
    spill_register #(
      .T       ( axi_b_t ),
      .Bypass  ( ~SpillB )
    ) i_b_spill_reg (
      .clk_i,
      .rst_ni,
      .valid_i ( slv_b_valid            ),
      .ready_o ( slv_b_ready            ),
      .data_i  ( slv_b_chan             ),
      .valid_o ( slv_port_rsp_o.b_valid ),
      .ready_i ( slv_port_req_i.b_ready ),
      .data_o  ( slv_port_rsp_o.b       )
    );

    // Arbitration of the different B responses
    rr_arb_tree #(
      .NumIn    ( NumMstPorts ),
      .DataType ( axi_b_t     ),
      .AxiVldRdy( 1'b1        ),
      .LockIn   ( 1'b1        )
    ) i_b_mux (
      .clk_i,
      .rst_ni,
      .flush_i( 1'b0          ),
      .rr_i   ( '0            ),
      .req_i  ( mst_b_valids  ),
      .gnt_o  ( mst_b_readies ),
      .data_i ( mst_b_chans   ),
      .gnt_i  ( slv_b_ready   ),
      .req_o  ( slv_b_valid   ),
      .data_o ( slv_b_chan    ),
      .idx_o  ( /*not used*/  )
    );

    //--------------------------------------
    //  AR Channel
    //--------------------------------------
    ar_select_t slv_ar_chan_select_in;
    assign      slv_ar_chan_select_in.ar_chan   = slv_port_req_i.ar;
    assign      slv_ar_chan_select_in.ar_select = slv_port_ar_select_i;
    spill_register #(
      .T       ( ar_select_t ),
      .Bypass  ( ~SpillAr    )
    ) i_ar_spill_reg (
      .clk_i,
      .rst_ni,
      .valid_i ( slv_port_req_i.ar_valid ),
      .ready_o ( slv_port_rsp_o.ar_ready ),
      .data_i  ( slv_ar_chan_select_in   ),
      .valid_o ( slv_ar_valid            ),
      .ready_i ( slv_ar_ready            ),
      .data_o  ( slv_ar_chan_select      )
    );

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
             (slv_ar_chan_select.ar_select == lookup_ar_select))) begin
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

    axi_demux_id_counters #(
      .AxiIdBits         ( IdWidthUsed    ),
      .CounterWidth      ( IdCounterWidth ),
      .mst_port_select_t ( select_t       )
    ) i_ar_id_counter (
      .clk_i,
      .rst_ni,
      .lookup_axi_id_i              ( slv_ar_chan_select.ar_chan.id[0+:IdWidthUsed] ),
      .lookup_mst_select_o          ( lookup_ar_select                              ),
      .lookup_mst_select_occupied_o ( ar_select_occupied                            ),
      .full_o                       ( ar_id_cnt_full                                ),
      .inject_axi_id_i              ( slv_aw_chan_select.aw_chan.id[0+:IdWidthUsed] ),
      .inject_i                     ( atop_inject                                   ),
      .push_axi_id_i                ( slv_ar_chan_select.ar_chan.id[0+:IdWidthUsed] ),
      .push_mst_select_i            ( slv_ar_chan_select.ar_select                  ),
      .push_i                       ( ar_push                                       ),
      .pop_axi_id_i                 ( slv_r_chan.id[0+:IdWidthUsed]                 ),
      .pop_i                        ( slv_r_valid & slv_r_ready & slv_r_chan.last   )
    );

    //--------------------------------------
    //  R Channel
    //--------------------------------------
    // optional spill register
    spill_register #(
      .T       ( axi_r_t ),
      .Bypass  ( ~SpillR )
    ) i_r_spill_reg (
      .clk_i,
      .rst_ni,
      .valid_i ( slv_r_valid            ),
      .ready_o ( slv_r_ready            ),
      .data_i  ( slv_r_chan             ),
      .valid_o ( slv_port_rsp_o.r_valid ),
      .ready_i ( slv_port_req_i.r_ready ),
      .data_o  ( slv_port_rsp_o.r       )
    );

    // Arbitration of the different r responses
    rr_arb_tree #(
      .NumIn     ( NumMstPorts ),
      .DataType  ( axi_r_t     ),
      .AxiVldRdy ( 1'b1        ),
      .LockIn    ( 1'b1        )
    ) i_r_mux (
      .clk_i,
      .rst_ni,
      .flush_i( 1'b0          ),
      .rr_i   ( '0            ),
      .req_i  ( mst_r_valids  ),
      .gnt_o  ( mst_r_readies ),
      .data_i ( mst_r_chans   ),
      .gnt_i  ( slv_r_ready   ),
      .req_o  ( slv_r_valid   ),
      .data_o ( slv_r_chan    ),
      .idx_o  ( /*not used*/  )
    );

   assign ar_ready = ar_valid & mst_ports_rsp_i[slv_ar_chan_select.ar_select].ar_ready;
   assign aw_ready = aw_valid & mst_ports_rsp_i[slv_aw_chan_select.aw_select].aw_ready;

    // process that defines the individual demuxes and assignments for the arbitration
    // as `mst_ports_req_o` has to be driven from the same always comb block!
    always_comb begin
      // default assignments
      mst_ports_req_o = '0;
      slv_w_ready     = 1'b0;
      w_fifo_pop      = 1'b0;

      for (int unsigned i = 0; i < NumMstPorts; i++) begin
        // AW channel
        mst_ports_req_o[i].aw       = slv_aw_chan_select.aw_chan;
        mst_ports_req_o[i].aw_valid = 1'b0;
        if (aw_valid && (slv_aw_chan_select.aw_select == i)) begin
          mst_ports_req_o[i].aw_valid = 1'b1;
        end

        //  W channel
        mst_ports_req_o[i].w       = slv_w_chan;
        mst_ports_req_o[i].w_valid = 1'b0;
        if (!w_fifo_empty && (w_select == i)) begin
          mst_ports_req_o[i].w_valid = slv_w_valid;
          slv_w_ready = mst_ports_rsp_i[i].w_ready;
          w_fifo_pop  = mst_ports_rsp_i[i].w_ready & slv_w_valid & slv_w_chan.last;
        end

        //  B channel
        mst_ports_req_o[i].b_ready  = mst_b_readies[i];

        // AR channel
        mst_ports_req_o[i].ar       = slv_ar_chan_select.ar_chan;
        mst_ports_req_o[i].ar_valid = 1'b0;
        if (ar_valid && (slv_ar_chan_select.ar_select == i)) begin
          mst_ports_req_o[i].ar_valid = 1'b1;
        end

        //  R channel
        mst_ports_req_o[i].r_ready = mst_r_readies[i];
      end
    end
    // unpack the response B and R channels for the arbitration
    for (genvar i = 0; unsigned'(i) < NumMstPorts; i++) begin : gen_b_channels
      assign mst_b_chans[i]        = mst_ports_rsp_i[i].b;
      assign mst_b_valids[i]       = mst_ports_rsp_i[i].b_valid;
      assign mst_r_chans[i]        = mst_ports_rsp_i[i].r;
      assign mst_r_valids[i]       = mst_ports_rsp_i[i].r_valid;
    end


// Validate parameters.
// pragma translate_off
`ifndef VERILATOR
`ifndef XSIM
    initial begin: validate_params
      no_mst_ports: assume (NumMstPorts > 0) else
        $fatal(1, "The Number of slaves (NumMstPorts) has to be at least 1");
      AXI_ID_BITS:  assume (IdWidth >= IdWidthUsed) else
        $fatal(1, "IdWidthUsed has to be equal or smaller than IdWidth.");
    end
    default disable iff (!rst_ni);
    aw_select: assume property( @(posedge clk_i) (slv_port_req_i.aw_valid |->
                                                 (slv_port_aw_select_i < NumMstPorts))) else
      $fatal(1, "slv_port_aw_select_i is %d: AW has selected a master port that is not defined.\
                 NumMstPorts: %d", slv_port_aw_select_i, NumMstPorts);
    ar_select: assume property( @(posedge clk_i) (slv_port_req_i.ar_valid |->
                                                 (slv_port_ar_select_i < NumMstPorts))) else
      $fatal(1, "slv_port_ar_select_i is %d: AR has selected a master port that is not defined.\
                 NoMstPorts: %d", slv_port_ar_select_i, NumMstPorts);
    aw_valid_stable: assert property( @(posedge clk_i) (aw_valid && !aw_ready) |=> aw_valid) else
      $fatal(1, "aw_valid was deasserted, when aw_ready = 0 in last cycle.");
    ar_valid_stable: assert property( @(posedge clk_i)
                               (ar_valid && !ar_ready) |=> ar_valid) else
      $fatal(1, "ar_valid was deasserted, when ar_ready = 0 in last cycle.");
    aw_stable: assert property( @(posedge clk_i) (aw_valid && !aw_ready)
                               |=> $stable(slv_aw_chan_select)) else
      $fatal(1, "slv_aw_chan_select unstable with valid set.");
    ar_stable: assert property( @(posedge clk_i) (ar_valid && !ar_ready)
                               |=> $stable(slv_ar_chan_select)) else
      $fatal(1, "slv_aw_chan_select unstable with valid set.");
    internal_ar_select: assert property( @(posedge clk_i)
        (ar_valid |-> slv_ar_chan_select.ar_select < NumMstPorts))
      else $fatal(1, "slv_ar_chan_select.ar_select illegal while ar_valid.");
    internal_aw_select: assert property( @(posedge clk_i)
        (aw_valid |-> slv_aw_chan_select.aw_select < NumMstPorts))
      else $fatal(1, "slv_aw_chan_select.aw_select illegal while aw_valid.");
`endif
`endif
// pragma translate_on
  end
endmodule

/// Internal ID counter module of `axi_demux`.
///
///
/// There needs to be kept track of which IDs are currently in-flight at a given master port of the
/// module so that the AXI ordering requirements are not violated.
module axi_demux_id_counters #(
  /// The lower bits of the AXI ID that should be considered, results in 2**AXI_ID_BITS counters.
  parameter int unsigned AxiIdBits = 32'd0,
  /// The width of each instantiated counter. This equates to the maximum number of transactions
  /// which can be in flight of a given ID.
  parameter int unsigned CounterWidth = 32'd0,
  /// The type of the selection signal to indicate on which master port the ID is transmitted.
  parameter type mst_port_select_t = logic
) (
  /// Clock, rising edge triggered.
  ///
  /// All other signals (except `rst_ni`) are synchronous to this signal.
  input  logic clk_i,
  /// Asynchronous reset, active low.
  input  logic rst_ni,
  /// The new ID that should be looked up for if it is already in-flight.
  input  logic [AxiIdBits-1:0] lookup_axi_id_i,
  /// The master port where the looked up transaction is currently in-flight if
  /// `lookup_mst_select_occupied_o` is `1`.
  output mst_port_select_t     lookup_mst_select_o,
  /// When `1`, the looked up ID is currently in-flight on master port indicated by
  /// `lookup_mst_select_o`.
  output logic                 lookup_mst_select_occupied_o,
  /// The counter selected by `push_axi_id_i` is currently full.
  output logic                 full_o,
  /// The ID that selects the counter.
  input  logic [AxiIdBits-1:0] push_axi_id_i,
  /// Specify the master port where the ID is transmitted.
  input  mst_port_select_t     push_mst_select_i,
  /// Increment the counter.
  input  logic                 push_i,
  /// Inject the ATOP id in AR channel.
  /// This port should only be used on the AR channel, tie to `0` in AW channel.
  input  logic [AxiIdBits-1:0] inject_axi_id_i,
  /// Push the ID, this increments the counter selected by `inject_axi_id_i` by an additional `+1`.
  input  logic                 inject_i,
  /// The ID of the counter that should be decremented on transaction completion.
  input  logic [AxiIdBits-1:0] pop_axi_id_i,
  /// Decrement the counter selected with `pop_axi_id_i`.
  input  logic                 pop_i
);
  localparam int unsigned NumCounters = 2**AxiIdBits;
  typedef logic [CounterWidth-1:0] cnt_t;

  // registers, each gets loaded when push_en[i]
  mst_port_select_t [NumCounters-1:0] mst_select_q;

  // counter signals
  logic [NumCounters-1:0] push_en, inject_en, pop_en, occupied, cnt_full;

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
  // counters
  for (genvar i = 0; unsigned'(i) < NumCounters; i++) begin : gen_counters
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

`include "axi/assign.svh"

/// Interface wrapper for `axi_demux`.
///
/// Ports and parameters are analog to `axi_demux`, see [`axi_demux` documentation](module.axi_demux).
/// The AXI4+ATOP master ports are structured here as interfaces.
///
/// The indexing of the master port interface array is big-endian.
module axi_demux_intf #(
  parameter int unsigned NumMstPorts = 32'd0,
  parameter int unsigned IdWidth     = 32'd0,
  parameter int unsigned IdWidthUsed = 32'd0,
  parameter int unsigned AddrWidth   = 32'd0,
  parameter int unsigned DataWidth   = 32'd0,
  parameter int unsigned UserWidth   = 32'd0,
  parameter int unsigned MaxTxns     = 32'd0,
  parameter bit          FallThrough = 1'b0,
  parameter bit          SpillAw     = 1'b1,
  parameter bit          SpillW      = 1'b0,
  parameter bit          SpillB      = 1'b0,
  parameter bit          SpillAr     = 1'b1,
  parameter bit          SpillR      = 1'b0,
  /// Dependent parameter, do **not** override!
  parameter int unsigned SelectWidth = cf_math_pkg::idx_width(NumMstPorts),
  /// Dependent parameter, do **not** override!
  parameter type select_t = logic [SelectWidth-1:0]
) (
  input  logic    clk_i,
  input  logic    rst_ni,
  input  logic    test_i,
  /// Slave port interface.
  AXI_BUS.Slave   slv_port,
  input  select_t slv_port_aw_select_i,
  input  select_t slv_port_ar_select_i,
  /// Unpacked, big-endian (upto) array of master port interfaces.
  AXI_BUS.Master  mst_ports[NumMstPorts]
);
  // Internal type definitions for the AXI4+ATOP channels.
  localparam int unsigned StrbWidth = DataWidth / 32'd8;
  typedef logic [IdWidth   -1:0] axi_id_t;
  typedef logic [AddrWidth -1:0] axi_addr_t;
  typedef logic [DataWidth -1:0] axi_data_t;
  typedef logic [StrbWidth -1:0] axi_strb_t;
  typedef logic [UserWidth -1:0] axi_user_t;

  `AXI_TYPEDEF_AW_CHAN_T(axi_aw_t, axi_addr_t, axi_id_t, axi_user_t)
  `AXI_TYPEDEF_W_CHAN_T(axi_w_t, axi_data_t, axi_strb_t, axi_user_t)
  `AXI_TYPEDEF_B_CHAN_T(axi_b_t, axi_id_t, axi_user_t)
  `AXI_TYPEDEF_AR_CHAN_T(axi_ar_t, axi_addr_t, axi_id_t, axi_user_t)
  `AXI_TYPEDEF_R_CHAN_T(axi_r_t, axi_data_t, axi_id_t, axi_user_t)

  `AXI_TYPEDEF_REQ_T(axi_req_t, axi_aw_t, axi_w_t, axi_ar_t)
  `AXI_TYPEDEF_RESP_T(axi_rsp_t, axi_b_t, axi_r_t)

  axi_req_t                   slv_req;
  axi_rsp_t                   slv_rsp;
  axi_req_t [NumMstPorts-1:0] mst_reqs;
  axi_rsp_t [NumMstPorts-1:0] mst_rsps;

  `AXI_ASSIGN_TO_REQ(slv_req, slv_port)
  `AXI_ASSIGN_FROM_RESP(slv_port, slv_rsp)

  for (genvar i = 0; unsigned'(i) < NumMstPorts; i++) begin : gen_assign_mst_ports
    `AXI_ASSIGN_FROM_REQ(mst_ports[i], mst_reqs[i])
    `AXI_ASSIGN_TO_RESP(mst_rsps[i], mst_ports[i])
  end

  axi_demux #(
    .NumMstPorts ( NumMstPorts ),
    .IdWidth     ( IdWidth     ),
    .IdWidthUsed ( IdWidthUsed ),
    .AddrWidth   ( AddrWidth   ),
    .DataWidth   ( DataWidth   ),
    .UserWidth   ( UserWidth   ),
    .MaxTxns     ( MaxTxns     ),
    .FallThrough ( FallThrough ),
    .SpillAw     ( SpillAw     ),
    .SpillW      ( SpillW      ),
    .SpillB      ( SpillB      ),
    .SpillAr     ( SpillAr     ),
    .SpillR      ( SpillR      ),
    .axi_req_t   ( axi_req_t   ),
    .axi_rsp_t   ( axi_rsp_t   )
  ) i_axi_demux (
    .clk_i,
    .rst_ni,
    .test_i,
    .slv_port_req_i       ( slv_req  ),
    .slv_port_aw_select_i,
    .slv_port_ar_select_i,
    .slv_port_rsp_o       ( slv_rsp  ),
    .mst_ports_req_o      ( mst_reqs ),
    .mst_ports_rsp_i      ( mst_rsps )
  );
endmodule
