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

// axi_xbar: Fully-connected AXI4+ATOP crossbar with an arbitrary number of slave and master ports.
// See `doc/axi_xbar.md` for the documentation, including the definition of parameters and ports.
module axi_xbar #(
  /// Number of slave ports of the crossbar.
  /// This many master modules are connected to it.
  parameter int unsigned NumSlvPorts = 32'd0,
  /// Number of master ports of the crossbar.
  /// This many slave modules are connected to it.
  parameter int unsigned NumMstPorts = 32'd0,
  /// AXI ID width of the slave ports. The ID width of the master ports is determined
  /// Automatically. See `axi_mux` for details.
  parameter int unsigned SlvPortIdWidth = 32'd0,
  /// The used ID portion to determine if a different salve is used for the same ID.
  /// See `axi_demux` for details.
  parameter int unsigned SlvPortIdWidthUsed = 32'd0,
  /// AXI4+ATOP address field width.
  parameter int unsigned AddrWidth = 32'd0,
  /// AXI4+ATOP data field width.
  parameter int unsigned DataWidth = 32'd0,
  /// AXI4+ATOP user field width.
  parameter int unsigned UserWidth = 32'd0,
  /// Maximum number of open transactions each master connected to the crossbar can have in
  /// flight at the same time.
  parameter int unsigned SlvPortMaxTxns = 32'd0,
  /// Maximum number of open transactions each slave connected to the crossbar can have in
  /// flight at the same time.
  parameter int unsigned MstPortMaxTxns = 32'd0,
  /// Determine if the internal FIFOs of the crossbar are instantiated in fallthrough mode.
  /// 0: No fallthrough
  /// 1: Fallthrough
  parameter bit FallThrough = 32'd1,
  /// The Latency mode of the xbar. This determines if the channels on the ports have
  /// a spill register instantiated.
  /// Example configurations are provided with the enum `xbar_latency_e`.
  parameter axi_pkg::xbar_latency_e LatencyMode = axi_pkg::CUT_ALL_AX,
  /// The number of address rules defined for routing of the transactions.
  /// Each master port can have multiple rules, should have however at least one.
  /// If a transaction can not be routed the xbar will answer with an `axi_pkg::RESP_DECERR`.
  parameter int unsigned NumAddrRules = 32'd0,
  /// Enable atomic operations support.
  parameter bit EnableAtops = 1'b1,
    //   /// AXI4+ATOP AW channel struct type for the slave ports.
    //   parameter type slv_aw_chan_t = logic,
    //   /// AXI4+ATOP AW channel struct type for the master ports.
    //   parameter type mst_aw_chan_t = logic,
    //   /// AXI4+ATOP W channel struct type for all ports.
    //   parameter type w_chan_t = logic,
    //   /// AXI4+ATOP B channel struct type for the slave ports.
    //   parameter type slv_b_chan_t = logic,
    //   /// AXI4+ATOP B channel struct type for the master ports.
    //   parameter type mst_b_chan_t = logic,
    //   /// AXI4+ATOP AR channel struct type for the slave ports.
    //   parameter type slv_ar_chan_t = logic,
    //   /// AXI4+ATOP AR channel struct type for the master ports.
    //   parameter type mst_ar_chan_t = logic,
    //   /// AXI4+ATOP R channel struct type for the slave ports.
    //   parameter type slv_r_chan_t = logic,
    //   /// AXI4+ATOP R channel struct type for the master ports.
    //   parameter type mst_r_chan_t = logic,
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
  /// Example types are provided in `axi_pkg`.
  ///
  /// Required struct fields:
  ///
  /// typedef struct packed {
  ///   int unsigned idx;
  ///   axi_addr_t   start_addr;
  ///   axi_addr_t   end_addr;
  /// } rule_t;
  parameter type rule_t = axi_pkg::xbar_rule_64_t,
  /// Dependent parameter, do **not** override!
  /// Width of the index specifying a master port.
  parameter int unsigned DefaultMstPortIdxWidth = cf_math_pkg::idx_width(NumMstPorts),
  /// Dependent parameter, do **not**parameter override!
  /// Type of index for a default master port.
  parameter type default_mst_port_idx_t = logic [DefaultMstPortIdxWidth-1:0]
) (
  /// Clock, positive edge triggered.
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
  ///
  /// When not used, tie to `'0`.
  input  logic [NumSlvPorts-1:0] en_default_mst_port_i,
  /// For each slave port the default index where the transaction should be routed, if
  /// for this slave port the default index functionality is enabled by setting the
  /// bit `en_default_mst_ports_i[slave_port_idx]` to `'1`.
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

/// This is the interface wrapper for `axi_xbar`. Ports and parameters are analog to `axxi_xbar`.
/// The AXI4+ATOP master and slave ports are structured here as interfaces.
/// Indexing of the interface is big-endian. This module does the little-endian indexing
/// for the port structs.
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
  AXI_BUS.Slave                                   slv_ports[NumSlvPorts],
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
