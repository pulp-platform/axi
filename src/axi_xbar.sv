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
// - Florian Zaruba <zarubaf@iis.ee.ethz.ch>

`include "axi/typedef.svh"

/// Fully-connected crossbar that implements AXI4 plus atomic operations (ATOPs) from AXI5 (E1.1).
///
///
/// # Design Overview
///
/// `axi_xbar` is a fully-connected crossbar, which means that each master module that is connected
/// to a *slave port* for of the crossbar has direct wires to all slave modules that are connected
/// to the *master ports* of the crossbar.
/// A block-diagram of the crossbar is shown below:
///
/// ![Block-diagram showing the design of the full AXI4 Crossbar.](docs/axi_xbar.png
/// "Block-diagram showing the design of the full AXI4 Crossbar.")
///
/// The crossbar has a configurable number of slave and master ports.
///
/// The ID width of the master ports is **wider** than that of the slave ports.  The additional ID
/// bits are used by the internal multiplexers to route responses.  The ID width of the master ports
/// must be `AxiIdWidthSlvPorts + $clog_2(NoSlvPorts)`.
///
///
/// # Address Map
///
/// One address map is shared by all master ports.  The *address map* contains an arbitrary number
/// of rules (but at least one).  Each *rule* maps one address range to one master port.  Multiple
/// rules can map to the same master port.  The address ranges of two rules may overlap: in case two
/// address ranges overlap, the rule at the higher (more significant) position in the address map
/// prevails.
///
/// Each address range includes the start address but does **not** include the end address.
/// That is, an address *matches* an address range if and only if
/// ```
/// addr >= start_addr && addr < end_addr
/// ```
/// The start address must be less than or equal to the end address.
///
/// The address map can be defined and changed at run time (it is an input signal to the crossbar).
/// However, the address map must not be changed while any AW or AR channel of any slave port is
/// valid.
///
/// [`addr_decode`](https://github.com/pulp-platform/common_cells/blob/master/src/addr_decode.sv)
/// module is used for decoding the address map.
///
///
/// # Decode Errors and Default Slave Port
///
/// Each slave port has its own internal *decode error slave* module.  If the address of a
/// transaction does not match any rule, the transaction is routed to that decode error slave
/// module.  That module absorbs each transaction and responds with a decode error (with the proper
/// number of beats).  The data of each read response beat is `32'hBADCAB1E` (zero-extended or
/// truncated to match the data width).
///
/// Each slave port can have a default master port.  If the default master port is enabled for a
/// slave port, any address on that slave port that does not match any rule is routed to the default
/// master port instead of the decode error slave.  The default master port can be enabled and
/// changed at run time (it is an input signal to the crossbar), and the same restrictions as for
/// the address map apply.
///
///
/// # Ordering and Stalls
///
/// When one slave port receives two transactions with the same ID and direction (i.e., both read or
/// both write) but targeting two different master ports, it will not accept the second transaction
/// until the first has completed.  During this time, the crossbar stalls the AR or AW channel of
/// that slave port.  To determine whether two transactions have the same ID, the
/// `AxiIdUsedSlvPorts` least-significant bits are compared.  That parameter can be set to the full
/// `AxiIdWidthSlvPorts` to avoid false ID conflicts, or it can be set to a lower value to reduce
/// area and delay at the cost of more false conflicts.
///
/// The reason for this ordering constraint is that AXI transactions with the same ID and direction
/// must remain ordered.  If this crossbar would forward both transactions described above, the
/// second master port could get a response before the first one, and the crossbar would have to
/// reorder the responses before returning them on the master port.  However, for efficiency
/// reasons, this crossbar does not have reorder buffers.
///
///
/// # Verification Methodology
///
/// This module has been verified with a directed random verification testbench, described and
/// implemented in [`tb_axi_xbar`](module.tb_axi_xbar) and
/// [`tb_axi_xbar_pkg`](package.tb_axi_xbar_pkg).
///
///
/// # Design Rationale for No Pipelining Inside Crossbar
///
/// Inserting spill registers between [`axi_demux`](module.axi_demux) and
/// [`axi_mux`](module.axi_mux) seems attractive to further reduce the length of combinatorial paths
/// in the crossbar.  However, this can lead to deadlocks in the W channel where two different
/// [`axi_mux`](module.axi_mux) at the master ports would circular wait on two different
/// [`axi_demux`](module.axi_demux).  In fact, spill registers between the switching modules causes
/// all four deadlock criteria to be met.  Recall that the criteria are:
///
/// 1. Mutual Exclusion
/// 2. Hold and Wait
/// 3. No Preemption
/// 4. Circular Wait
///
/// The first criterion is given by the nature of a multiplexer on the W channel: all W beats have
/// to arrive in the same order as the AW beats regardless of the ID at the slave module.  Thus, the
/// different master ports of the multiplexer exclude each other because the order is given by the
/// arbitration tree of the AW channel.
///
/// The second and third criterion are inherent to the AXI protocol:  For (2), the valid signal has
/// to be held high until the ready signal goes high.  For (3), AXI does not allow interleaving of
/// W beats and requires W bursts to be in the same order as AW beats.
///
/// The fourth criterion is thus the only one that can be broken to prevent deadlocks.  However,
/// inserting a spill register between a master port of the [`axi_demux`](module.axi_demux) and a
/// slave port of the [`axi_mux`](module.axi_mux) can lead to a circular dependency inside the
/// W FIFOs.  This comes from the particular way the round robin arbiter from the AW channel in the
/// multiplexer defines its priorities.  It is constructed in a way by giving each of its slave
/// ports an increasing priority and then comparing pairwise down till a winner is chosen.  When the
/// winner gets transferred, the priority state is advanced by one position, preventing starvation.
///
/// The problem can be shown with an example.  Assume an arbitration tree with 10 inputs.  Two
/// requests want to be served in the same clock cycle.  The one with the higher priority wins and
/// the priority state advances.  In the next cycle again the same two inputs have a request
/// waiting.  Again it is possible that the same port as last time wins as the priority shifted only
/// one position further.  This can lead in conjunction with the other arbitration trees in the
/// other muxes of the crossbar to the circular dependencies inside the FIFOs.  Removing the spill
/// register between the demultiplexer and multiplexer forces the switching decision into the
/// W FIFOs in the same clock cycle.  This leads to a strict ordering of the switching decision,
/// thus preventing the circular wait.
///
module axi_xbar #(
  /// The number of AXI slave ports of the crossbar.
  /// (In other words, how many AXI master modules can be attached).
  parameter int unsigned NumSlvPorts = 32'd0,
  /// The number of AXI master ports of the crossbar.
  /// (In other words, how many AXI slave modules can be attached).
  parameter int unsigned NumMstPorts = 32'd0,
  /// AXI ID width of the slave ports.
  ///
  /// This parameter also determines the corresponding value for `MstPortIdWidth` .
  /// Routing of responses is done by extending the ID by the index of the slave port witch accepted
  /// the transaction.  See [`axi_mux`](module.axi_mux) for details.
  parameter int unsigned SlvPortIdWidth = 32'd0,
  /// The number of slave port ID bits (starting at the least significant) the crossbar uses to
  /// determine the uniqueness of an AXI ID (see section *Ordering and Stalls* above).
  ///
  /// This value *must* follow `SlvPortIdWidth >= SlvPortIdWidthUsed && SlvPortIdWidthUsed > 0`.
  ///
  /// Setting this to small values leads to less area, however on an increased stalling rate
  /// due to ID collisions.
  parameter int unsigned SlvPortIdWidthUsed = 32'd0,
  /// AXI4+ATOP address field width.
  parameter int unsigned AddrWidth = 32'd0,
  /// AXI4+ATOP data field width.
  parameter int unsigned DataWidth = 32'd0,
  /// AXI4+ATOP user field width.
  parameter int unsigned UserWidth = 32'd0,
  /// Maximum number of open transactions each slave port of the crossbar can have
  /// [in flight](doc/#in-flight) at the same time.
  parameter int unsigned SlvPortMaxTxns = 32'd0,
  /// Maximum number of open transactions each master port the crossbar can have
  /// [in flight](../doc#in-flight) per ID at the same time.
  parameter int unsigned MstPortMaxTxns = 32'd0,
  /// Routing decisions on the AW channel fall through to the W channel.  Enabling this allows the
  /// crossbar to accept a W beat in the same cycle as the corresponding AW beat, but it increases
  /// the combinatorial path of the W channel with logic from the AW channel.
  ///
  /// Setting this to `0` prevents logic on the AW channel from extending into the W channel.
  ///
  /// 0: No fallthrough
  /// 1: Fallthrough
  parameter bit FallThrough = 32'd1,
  /// The `LatencyMode` parameter allows to insert spill registers after each channel
  /// (AW, W, B, AR, and R) of each master port (i.e., each [`axi_mux`](module.axi_mux)) and before
  /// each channel of each slave port (i.e., each [`axi_demux`](module.axi_demux)).
  /// Spill registers cut combinatorial paths, so this parameter reduces the length of combinatorial
  /// paths through the crossbar.
  ///
  /// Some common configurations are given in the [`xbar_latency_e` `enum`](package.axi_pkg).
  /// The recommended configuration (`axi_pkg::CUT_ALL_AX`) is to have a latency of 2 on the AW and
  /// AR channels because these channels have the most combinatorial logic on them.
  /// Additionally, `FallThrough` should be set to `0` to prevent logic on the AW channel from
  /// extending combinatorial paths on the W channel.  However, it is possible to run the crossbar
  /// in a fully combinatorial configuration by setting `LatencyMode` to `NO_LATENCY` and
  /// `FallThrough` to `1`.
  ///
  /// If two crossbars are connected in both directions, meaning both have one of their master ports
  /// connected to a slave port of the other, the `LatencyMode` of both crossbars must be set to
  /// either `CUT_SLV_PORTS`, `CUT_MST_PORTS`, or `CUT_ALL_PORTS`.  Any other latency mode will lead
  /// to timing loops on the uncut channels between the two crossbars.  The latency mode of the two
  /// crossbars does not have to be identical.
  parameter axi_pkg::xbar_latency_e LatencyMode = axi_pkg::CUT_ALL_AX,
  /// The number of address rules defined for routing of the transactions.
  /// Each master port can have multiple rules, should have however at least one or be the
  /// *default master port* of at least one slave port.
  /// If a transaction can not be routed the xbar will answer with an `axi_pkg::RESP_DECERR`.
  parameter int unsigned NumAddrRules = 32'd0,
  /// Enable atomic operations support.
  parameter bit EnableAtops = 1'b1,
  /// AXI4+ATOP request struct type for a single slave port.
  parameter type slv_port_axi_req_t = logic,
  /// AXI4+ATOP response struct type for a single slave port.
  parameter type slv_port_axi_rsp_t = logic,
  /// AXI4+ATOP request struct type for a single master port.
  parameter type mst_port_axi_req_t = logic,
  /// AXI4+ATOP response struct type for a single master port.
  parameter type mst_port_axi_rsp_t = logic,
  /// Address rule type for the address decoders from `common_cells:addr_decode`.
  ///
  /// Example types are provided in [`axi_pkg`](package.axi_pkg).
  ///
  /// Required struct fields:
  ///
  /// ```systemverilog
  /// typedef struct packed {
  ///   int unsigned idx;
  ///   axi_addr_t   start_addr;
  ///   axi_addr_t   end_addr;
  /// } rule_t;
  /// ```
  parameter type rule_t = axi_pkg::xbar_rule_64_t,
  /// Dependent parameter, do **not** override!
  /// Width of the index specifying a master port.
  parameter int unsigned DefaultMstPortIdxWidth = cf_math_pkg::idx_width(NumMstPorts),
  /// Dependent parameter, do **not** override!
  /// Type of index for a default master port.
  parameter type default_mst_port_idx_t = logic [DefaultMstPortIdxWidth-1:0]
) (
  /// Clock, rising edge triggered.
  ///
  /// All other signals (except `rst_ni`) are synchronous to this signal.
  input  logic clk_i,
  /// Asynchronous reset, active low.
  input  logic rst_ni,
  /// Testmode enable, active high.
  input  logic test_i,
  /// AXI4+ATOP requests to the slave ports.
  input  slv_port_axi_req_t [NumSlvPorts-1:0] slv_ports_req_i,
  /// AXI4+ATOP responses of the slave ports.
  output slv_port_axi_rsp_t [NumSlvPorts-1:0] slv_ports_rsp_o,
  /// AXI4+ATOP requests of the master ports.
  output mst_port_axi_req_t [NumMstPorts-1:0] mst_ports_req_o,
  /// AXI4+ATOP responses to the master ports.
  input  mst_port_axi_rsp_t [NumMstPorts-1:0] mst_ports_rsp_i,
  /// Address map array input for the crossbar. This map is global for the whole module.
  /// It is used for routing the transactions to the respective master ports.
  /// Each master port can have multiple different rules.
  input  rule_t [NumAddrRules-1:0] addr_map_i,
  /// Enables a default master port for each slave port. When this is enabled unmapped
  /// transactions get issued at the master port given by `default_mst_port_i`.
  /// Each bit index corresponds to the index of a master port and is ordered little-endian (downto).
  ///
  /// When not used, tie to `'0`.
  input  logic [NumSlvPorts-1:0] en_default_mst_port_i,
  /// For each slave port the default index where the transaction should be routed, if
  /// for this slave port the default index functionality is enabled by setting the
  /// bit `en_default_mst_ports_i[slave_port_idx]` to `1'b1`.
  ///
  /// When not used, tie to `'0`.
  input  default_mst_port_idx_t [NumSlvPorts-1:0] default_mst_ports_i
);

  // Internal type definitions for the AXI4+ATOP channels.
  localparam int unsigned MstPortIdWidth = SlvPortIdWidth + unsigned'($clog2(NumSlvPorts));
  localparam int unsigned StrbWidth      = DataWidth / 32'd8;
  typedef logic [SlvPortIdWidth -1:0] slv_port_axi_id_t;
  typedef logic [MstPortIdWidth -1:0] mst_port_axi_id_t;
  typedef logic [AddrWidth      -1:0] axi_addr_t;
  typedef logic [DataWidth      -1:0] axi_data_t;
  typedef logic [StrbWidth      -1:0] axi_strb_t;
  typedef logic [UserWidth      -1:0] axi_user_t;

  `AXI_TYPEDEF_AW_CHAN_T(slv_port_axi_aw_t, axi_addr_t, slv_port_axi_id_t, axi_user_t)
  `AXI_TYPEDEF_AW_CHAN_T(mst_port_axi_aw_t, axi_addr_t, mst_port_axi_id_t, axi_user_t)
  `AXI_TYPEDEF_W_CHAN_T(axi_w_t, axi_data_t, axi_strb_t, axi_user_t)
  `AXI_TYPEDEF_B_CHAN_T(slv_port_axi_b_t, slv_port_axi_id_t, axi_user_t)
  `AXI_TYPEDEF_B_CHAN_T(mst_port_axi_b_t, mst_port_axi_id_t, axi_user_t)
  `AXI_TYPEDEF_AR_CHAN_T(slv_port_axi_ar_t, axi_addr_t, slv_port_axi_id_t, axi_user_t)
  `AXI_TYPEDEF_AR_CHAN_T(mst_port_axi_ar_t, axi_addr_t, mst_port_axi_id_t, axi_user_t)
  `AXI_TYPEDEF_R_CHAN_T(slv_port_axi_r_t, axi_data_t, slv_port_axi_id_t, axi_user_t)
  `AXI_TYPEDEF_R_CHAN_T(mst_port_axi_r_t, axi_data_t, mst_port_axi_id_t, axi_user_t)

  // Account for the decoding error slave in the `axi_demux` select width.
  // The `axi_demux` on a slave port always has one more master port that the number of master ports
  // of the `axi_xbar`.
  localparam int unsigned InternalSelectIdxWidth = cf_math_pkg::idx_width(NumMstPorts + 32'd1);
  typedef logic [InternalSelectIdxWidth-1:0] internal_select_idx_t;

  // signals from the axi_demuxes, one index more for decode error
  slv_port_axi_req_t [NumSlvPorts-1:0][NumMstPorts:0] slv_reqs;
  slv_port_axi_rsp_t [NumSlvPorts-1:0][NumMstPorts:0] slv_rsps;

  // signals into the axi_muxes, are of type slave as the multiplexer extends the ID
  slv_port_axi_req_t [NumMstPorts-1:0][NumSlvPorts-1:0] mst_reqs;
  slv_port_axi_rsp_t [NumMstPorts-1:0][NumSlvPorts-1:0] mst_rsps;

  for (genvar i = 0; unsigned'(i) < NumSlvPorts; i++) begin : gen_slv_port_demux
    default_mst_port_idx_t dec_aw,        dec_ar;
    internal_select_idx_t  slv_aw_select, slv_ar_select;
    logic                  dec_aw_valid,  dec_aw_error;
    logic                  dec_ar_valid,  dec_ar_error;

    addr_decode #(
      .NoIndices  ( NumMstPorts  ),
      .NoRules    ( NumAddrRules ),
      .addr_t     ( axi_addr_t   ),
      .rule_t     ( rule_t       )
    ) i_axi_aw_decode (
      .addr_i           ( slv_ports_req_i[i].aw.addr ),
      .addr_map_i       ( addr_map_i                 ),
      .idx_o            ( dec_aw                     ),
      .dec_valid_o      ( dec_aw_valid               ),
      .dec_error_o      ( dec_aw_error               ),
      .en_default_idx_i ( en_default_mst_port_i[i]   ),
      .default_idx_i    ( default_mst_ports_i[i]     )
    );

    addr_decode #(
      .NoIndices  ( NumMstPorts  ),
      .NoRules    ( NumAddrRules ),
      .addr_t     ( axi_addr_t   ),
      .rule_t     ( rule_t       )
    ) i_axi_ar_decode (
      .addr_i           ( slv_ports_req_i[i].ar.addr ),
      .addr_map_i       ( addr_map_i                 ),
      .idx_o            ( dec_ar                     ),
      .dec_valid_o      ( dec_ar_valid               ),
      .dec_error_o      ( dec_ar_error               ),
      .en_default_idx_i ( en_default_mst_port_i[i]   ),
      .default_idx_i    ( default_mst_ports_i[i]     )
    );

    assign slv_aw_select = (dec_aw_error) ?
        internal_select_idx_t'(NumMstPorts) : internal_select_idx_t'(dec_aw);
    assign slv_ar_select = (dec_ar_error) ?
        internal_select_idx_t'(NumMstPorts) : internal_select_idx_t'(dec_ar);

    // make sure that the default slave does not get changed, if there is an unserved Ax
    // pragma translate_off
    `ifndef VERILATOR
    `ifndef XSIM
    default disable iff (~rst_ni);
    default_aw_mst_port_en: assert property(
      @(posedge clk_i) (slv_ports_req_i[i].aw_valid && !slv_ports_rsp_o[i].aw_ready)
          |=> $stable(en_default_mst_port_i[i]))
        else $fatal (1, $sformatf("It is not allowed to change the default mst port\
                                   enable, when there is an unserved Aw beat. Slave Port: %0d", i));
    default_aw_mst_port: assert property(
      @(posedge clk_i) (slv_ports_req_i[i].aw_valid && !slv_ports_rsp_o[i].aw_ready)
          |=> $stable(default_mst_ports_i[i]))
        else $fatal (1, $sformatf("It is not allowed to change the default mst port\
                                   when there is an unserved Aw beat. Slave Port: %0d", i));
    default_ar_mst_port_en: assert property(
      @(posedge clk_i) (slv_ports_req_i[i].ar_valid && !slv_ports_rsp_o[i].ar_ready)
          |=> $stable(en_default_mst_port_i[i]))
        else $fatal (1, $sformatf("It is not allowed to change the enable, when\
                                   there is an unserved Ar beat. Slave Port: %0d", i));
    default_ar_mst_port: assert property(
      @(posedge clk_i) (slv_ports_req_i[i].ar_valid && !slv_ports_rsp_o[i].ar_ready)
          |=> $stable(default_mst_ports_i[i]))
        else $fatal (1, $sformatf("It is not allowed to change the default mst port\
                                   when there is an unserved Ar beat. Slave Port: %0d", i));
    `endif
    `endif
    // pragma translate_on
    axi_demux #(
      .AxiIdWidth     ( SlvPortIdWidth      ),  // ID Width
      .aw_chan_t      ( slv_port_axi_aw_t   ),  // AW Channel Type
      .w_chan_t       ( axi_w_t             ),  //  W Channel Type
      .b_chan_t       ( slv_port_axi_b_t    ),  //  B Channel Type
      .ar_chan_t      ( slv_port_axi_ar_t   ),  // AR Channel Type
      .r_chan_t       ( slv_port_axi_r_t    ),  //  R Channel Type
      .req_t          ( slv_port_axi_req_t  ),
      .resp_t         ( slv_port_axi_rsp_t  ),
      .NoMstPorts     ( NumMstPorts + 32'd1 ),
      .MaxTrans       ( SlvPortMaxTxns      ),
      .AxiLookBits    ( SlvPortIdWidthUsed  ),
      .FallThrough    ( FallThrough         ),
      .SpillAw        ( LatencyMode[9]      ),
      .SpillW         ( LatencyMode[8]      ),
      .SpillB         ( LatencyMode[7]      ),
      .SpillAr        ( LatencyMode[6]      ),
      .SpillR         ( LatencyMode[5]      )
    ) i_axi_demux (
      .clk_i,   // Clock
      .rst_ni,  // Asynchronous reset active low
      .test_i,  // Testmode enable
      .slv_req_i       ( slv_ports_req_i[i] ),
      .slv_aw_select_i ( slv_aw_select      ),
      .slv_ar_select_i ( slv_ar_select      ),
      .slv_resp_o      ( slv_ports_rsp_o[i] ),
      .mst_reqs_o      ( slv_reqs[i]        ),
      .mst_resps_i     ( slv_rsps[i]        )
    );

    axi_err_slv #(
      .AxiIdWidth  ( SlvPortIdWidth       ),
      .req_t       ( slv_port_axi_req_t   ),
      .resp_t      ( slv_port_axi_rsp_t   ),
      .Resp        ( axi_pkg::RESP_DECERR ),
      .ATOPs       ( EnableAtops          ),
      .MaxTrans    ( 32'd4                )   // Transactions terminate at this slave, so minimize
                                              // resource consumption by accepting only a few
                                              // transactions at a time.
    ) i_axi_err_slv (
      .clk_i,   // Clock
      .rst_ni,  // Asynchronous reset active low
      .test_i,  // Testmode enable
      // slave port
      .slv_req_i  ( slv_reqs[i][NumMstPorts] ),
      .slv_resp_o ( slv_rsps[i][NumMstPorts] )
    );
  end

  // cross all channels
  for (genvar i = 0; unsigned'(i) < NumSlvPorts; i++) begin : gen_xbar_slv_cross
    for (genvar j = 0; unsigned'(j) < NumMstPorts; j++) begin : gen_xbar_mst_cross
      assign mst_reqs[j][i] = slv_reqs[i][j];
      assign slv_rsps[i][j] = mst_rsps[j][i];
    end
  end

  for (genvar i = 0; unsigned'(i) < NumMstPorts; i++) begin : gen_mst_port_mux
    axi_mux #(
      .SlvAxiIDWidth ( SlvPortIdWidth      ), // ID width of the slave ports
      .slv_aw_chan_t ( slv_port_axi_aw_t   ), // AW Channel Type, slave ports
      .mst_aw_chan_t ( mst_port_axi_aw_t   ), // AW Channel Type, master port
      .w_chan_t      ( axi_w_t             ), //  W Channel Type, all ports
      .slv_b_chan_t  ( slv_port_axi_b_t    ), //  B Channel Type, slave ports
      .mst_b_chan_t  ( mst_port_axi_b_t    ), //  B Channel Type, master port
      .slv_ar_chan_t ( slv_port_axi_ar_t   ), // AR Channel Type, slave ports
      .mst_ar_chan_t ( mst_port_axi_ar_t   ), // AR Channel Type, master port
      .slv_r_chan_t  ( slv_port_axi_r_t    ), //  R Channel Type, slave ports
      .mst_r_chan_t  ( mst_port_axi_r_t    ), //  R Channel Type, master port
      .slv_req_t     ( slv_port_axi_req_t  ),
      .slv_resp_t    ( slv_port_axi_rsp_t  ),
      .mst_req_t     ( mst_port_axi_req_t  ),
      .mst_resp_t    ( mst_port_axi_rsp_t  ),
      .NoSlvPorts    ( NumSlvPorts         ), // Number of Masters for the module
      .MaxWTrans     ( MstPortMaxTxns      ),
      .FallThrough   ( FallThrough         ),
      .SpillAw       ( LatencyMode[4]      ),
      .SpillW        ( LatencyMode[3]      ),
      .SpillB        ( LatencyMode[2]      ),
      .SpillAr       ( LatencyMode[1]      ),
      .SpillR        ( LatencyMode[0]      )
    ) i_axi_mux (
      .clk_i,   // Clock
      .rst_ni,  // Asynchronous reset active low
      .test_i,  // Test Mode enable
      .slv_reqs_i  ( mst_reqs[i]        ),
      .slv_resps_o ( mst_rsps[i]        ),
      .mst_req_o   ( mst_ports_req_o[i] ),
      .mst_resp_i  ( mst_ports_rsp_i[i] )
    );
  end

  // pragma translate_off
  `ifndef VERILATOR
  `ifndef XSIM
  initial begin : check_params
    id_slv_req_ports: assert ($bits(slv_ports_req_i[0].aw.id) == SlvPortIdWidth) else
      $fatal(1, $sformatf("slv_ports_req_i.aw.id and SlvPortIdWidth not equal."));
    id_slv_rsp_ports: assert ($bits(slv_ports_rsp_o[0].r.id) == SlvPortIdWidth) else
      $fatal(1, $sformatf("slv_ports_rsp_o.r.id and SlvPortIdWidth not equal."));
  end
  `endif
  `endif
  // pragma translate_on
endmodule

`include "axi/assign.svh"

/// This is the interface wrapper for `axi_xbar`. Ports and parameters are analog to `axi_xbar`,
/// see [`axi_xbar` documentation](module.axi_xbar).
/// The AXI4+ATOP master and slave ports are structured here as interfaces.
///
/// The indexing of the master and slave port interface arrays is big-endian.
module axi_xbar_intf #(
  parameter int unsigned            NumSlvPorts        = 32'd0,
  parameter int unsigned            NumMstPorts        = 32'd0,
  parameter int unsigned            SlvPortIdWidth     = 32'd0,
  parameter int unsigned            SlvPortIdWidthUsed = 32'd0,
  parameter int unsigned            AddrWidth          = 32'd0,
  parameter int unsigned            DataWidth          = 32'd0,
  parameter int unsigned            UserWidth          = 32'd0,
  parameter int unsigned            SlvPortMaxTxns     = 32'd0,
  parameter int unsigned            MstPortMaxTxns     = 32'd0,
  parameter bit                     FallThrough        = 32'd1,
  parameter axi_pkg::xbar_latency_e LatencyMode        = axi_pkg::CUT_ALL_AX,
  parameter int unsigned            NumAddrRules       = 32'd0,
  parameter bit                     EnableAtops        = 1'b1,
  parameter type rule_t = axi_pkg::xbar_rule_64_t,
  /// Dependent parameter, do **not** override!
  parameter int unsigned DefaultMstPortIdxWidth = cf_math_pkg::idx_width(NumMstPorts),
  /// Dependent parameter, do **not**parameter override!
  parameter type default_mst_port_idx_t = logic [DefaultMstPortIdxWidth-1:0]
) (
  input logic                                     clk_i,
  input logic                                     rst_ni,
  input logic                                     test_i,
  /// Unpacked, big-endian (upto) array of slave port interfaces.
  AXI_BUS.Slave                                   slv_ports[NumSlvPorts],
  /// Unpacked, big-endian (upto) array of master port interfaces.
  AXI_BUS.Master                                  mst_ports[NumMstPorts],
  input rule_t                 [NumAddrRules-1:0] addr_map_i,
  input logic                  [NumSlvPorts -1:0] en_default_mst_port_i,
  input default_mst_port_idx_t [NumSlvPorts -1:0] default_mst_ports_i
);

  // Internal type definitions for the AXI4+ATOP channels.
  localparam int unsigned MstPortIdWidth = SlvPortIdWidth + unsigned'($clog2(NumSlvPorts));
  localparam int unsigned StrbWidth      = DataWidth / 32'd8;
  typedef logic [SlvPortIdWidth -1:0] slv_port_axi_id_t;
  typedef logic [MstPortIdWidth -1:0] mst_port_axi_id_t;
  typedef logic [AddrWidth      -1:0] axi_addr_t;
  typedef logic [DataWidth      -1:0] axi_data_t;
  typedef logic [StrbWidth      -1:0] axi_strb_t;
  typedef logic [UserWidth      -1:0] axi_user_t;

  `AXI_TYPEDEF_AW_CHAN_T(slv_port_axi_aw_t, axi_addr_t, slv_port_axi_id_t, axi_user_t)
  `AXI_TYPEDEF_AW_CHAN_T(mst_port_axi_aw_t, axi_addr_t, mst_port_axi_id_t, axi_user_t)
  `AXI_TYPEDEF_W_CHAN_T(axi_w_t, axi_data_t, axi_strb_t, axi_user_t)
  `AXI_TYPEDEF_B_CHAN_T(slv_port_axi_b_t, slv_port_axi_id_t, axi_user_t)
  `AXI_TYPEDEF_B_CHAN_T(mst_port_axi_b_t, mst_port_axi_id_t, axi_user_t)
  `AXI_TYPEDEF_AR_CHAN_T(slv_port_axi_ar_t, axi_addr_t, slv_port_axi_id_t, axi_user_t)
  `AXI_TYPEDEF_AR_CHAN_T(mst_port_axi_ar_t, axi_addr_t, mst_port_axi_id_t, axi_user_t)
  `AXI_TYPEDEF_R_CHAN_T(slv_port_axi_r_t, axi_data_t, slv_port_axi_id_t, axi_user_t)
  `AXI_TYPEDEF_R_CHAN_T(mst_port_axi_r_t, axi_data_t, mst_port_axi_id_t, axi_user_t)

  `AXI_TYPEDEF_REQ_T(slv_port_axi_req_t, slv_port_axi_aw_t, axi_w_t, slv_port_axi_ar_t)
  `AXI_TYPEDEF_REQ_T(mst_port_axi_req_t, mst_port_axi_aw_t, axi_w_t, mst_port_axi_ar_t)
  `AXI_TYPEDEF_RESP_T(slv_port_axi_rsp_t, slv_port_axi_b_t, slv_port_axi_r_t)
  `AXI_TYPEDEF_RESP_T(mst_port_axi_rsp_t, mst_port_axi_b_t, mst_port_axi_r_t)

  slv_port_axi_req_t [NumSlvPorts-1:0] slv_reqs;
  slv_port_axi_rsp_t [NumSlvPorts-1:0] slv_rsps;
  mst_port_axi_req_t [NumMstPorts-1:0] mst_reqs;
  mst_port_axi_rsp_t [NumMstPorts-1:0] mst_rsps;

  for (genvar i = 0; unsigned'(i) < NumSlvPorts; i++) begin : gen_assign_slv
    `AXI_ASSIGN_TO_REQ(slv_reqs[i], slv_ports[i])
    `AXI_ASSIGN_FROM_RESP(slv_ports[i], slv_rsps[i])
  end

  for (genvar i = 0; unsigned'(i) < NumMstPorts; i++) begin : gen_assign_mst
    `AXI_ASSIGN_FROM_REQ(mst_ports[i], mst_reqs[i])
    `AXI_ASSIGN_TO_RESP(mst_rsps[i], mst_ports[i])
  end

  axi_xbar #(
    .NumSlvPorts        ( NumSlvPorts        ),
    .NumMstPorts        ( NumMstPorts        ),
    .SlvPortIdWidth     ( SlvPortIdWidth     ),
    .SlvPortIdWidthUsed ( SlvPortIdWidthUsed ),
    .AddrWidth          ( AddrWidth          ),
    .DataWidth          ( DataWidth          ),
    .UserWidth          ( UserWidth          ),
    .SlvPortMaxTxns     ( SlvPortMaxTxns     ),
    .MstPortMaxTxns     ( MstPortMaxTxns     ),
    .FallThrough        ( FallThrough        ),
    .LatencyMode        ( LatencyMode        ),
    .NumAddrRules       ( NumAddrRules       ),
    .EnableAtops        ( EnableAtops        ),
    .slv_port_axi_req_t ( slv_port_axi_req_t ),
    .slv_port_axi_rsp_t ( slv_port_axi_rsp_t ),
    .mst_port_axi_req_t ( mst_port_axi_req_t ),
    .mst_port_axi_rsp_t ( mst_port_axi_rsp_t ),
    .rule_t             ( rule_t             )
  ) i_xbar (
    .clk_i,
    .rst_ni,
    .test_i,
    .slv_ports_req_i ( slv_reqs ),
    .slv_ports_rsp_o ( slv_rsps ),
    .mst_ports_req_o ( mst_reqs ),
    .mst_ports_rsp_i ( mst_rsps ),
    .addr_map_i,
    .en_default_mst_port_i,
    .default_mst_ports_i
  );
endmodule
