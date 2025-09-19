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

/// axi_xbar: Fully-connected AXI4+ATOP crossbar with an arbitrary number of slave and master ports.
/// See `doc/axi_xbar.md` for the documentation, including the definition of parameters and ports.
module axi_mcast_xbar_unmuxed
import cf_math_pkg::idx_width;
#(
  /// Configuration struct for the crossbar see `axi_pkg` for fields and definitions.
  parameter axi_pkg::xbar_cfg_t Cfg                                   = '0,
  /// Enable atomic operations support.
  parameter bit  ATOPs                                                = 1'b1,
  /// Connectivity matrix
  parameter bit [Cfg.NoSlvPorts-1:0][Cfg.NoMstPorts-1:0] Connectivity = '1,
  /// Connectivity matrix for multicast transactions
  parameter bit [Cfg.NoSlvPorts-1:0][Cfg.NoMstPorts-1:0] MulticastConnectivity = '1,
  /// AXI4+ATOP AW channel struct type for the slave ports.
  parameter type aw_chan_t                                            = logic,
  /// AXI4+ATOP W channel struct type for all ports.
  parameter type w_chan_t                                             = logic,
  /// AXI4+ATOP B channel struct type for the slave ports.
  parameter type b_chan_t                                             = logic,
  /// AXI4+ATOP AR channel struct type for the slave ports.
  parameter type ar_chan_t                                            = logic,
  /// AXI4+ATOP R channel struct type for the slave ports.
  parameter type r_chan_t                                             = logic,
  /// AXI4+ATOP request struct type for the slave ports.
  parameter type req_t                                                = logic,
  /// AXI4+ATOP response struct type for the slave ports.
  parameter type resp_t                                               = logic,
  /// Address rule type for the address decoders from `common_cells:addr_decode`.
  /// Example types are provided in `axi_pkg`.
  /// Required struct fields:
  /// ```
  /// typedef struct packed {
  ///   int unsigned idx;
  ///   axi_addr_t   start_addr;
  ///   axi_addr_t   end_addr;
  /// } rule_t;
  /// ```
  parameter type rule_t                                               = axi_pkg::xbar_rule_64_t
) (
  /// Clock, positive edge triggered.
  input  logic                                                          clk_i,
  /// Asynchronous reset, active low.
  input  logic                                                          rst_ni,
  /// Testmode enable, active high.
  input  logic                                                          test_i,
  /// AXI4+ATOP requests to the slave ports.
  input  req_t  [Cfg.NoSlvPorts-1:0]                                    slv_ports_req_i,
  /// AXI4+ATOP responses of the slave ports.
  output resp_t [Cfg.NoSlvPorts-1:0]                                    slv_ports_resp_o,
  /// AXI4+ATOP requests of the master ports.
  output req_t  [Cfg.NoMstPorts-1:0][Cfg.NoSlvPorts-1:0]                mst_ports_req_o,
  /// AXI4+ATOP responses to the master ports.
  input  resp_t [Cfg.NoMstPorts-1:0][Cfg.NoSlvPorts-1:0]                mst_ports_resp_i,
  /// Additional multicast signals to the master ports.
  output logic  [Cfg.NoMstPorts-1:0][Cfg.NoSlvPorts-1:0]                mst_is_mcast_o,
  output logic  [Cfg.NoMstPorts-1:0][Cfg.NoSlvPorts-1:0]                mst_aw_commit_o,
  /// Address map array input for the crossbar. This map is global for the whole module.
  /// It is used for routing the transactions to the respective master ports.
  /// Each master port can have multiple different rules.
  input  rule_t     [Cfg.NoAddrRules-1:0]                               addr_map_i,
  /// Enable default master port.
  input  logic      [Cfg.NoSlvPorts-1:0]                                en_default_mst_port_i,
  /// Enables a default master port for each slave port. When this is enabled unmapped
  /// transactions get issued at the master port given by `default_mst_port_i`.
  /// When not used, tie to `'0`.
  input  rule_t     [Cfg.NoSlvPorts-1:0]                                default_mst_port_i
);

  // Address type for individual address signals
  typedef logic [Cfg.AxiAddrWidth-1:0] addr_t;
  // to account for the decoding error slave
  localparam int unsigned MstPortsIdxWidthOne =
      (Cfg.NoMstPorts == 32'd1) ? 32'd1 : unsigned'($clog2(Cfg.NoMstPorts + 1));
  localparam int unsigned MstPortsIdxWidth =
      (Cfg.NoMstPorts == 32'd1) ? 32'd1 : unsigned'($clog2(Cfg.NoMstPorts));
  typedef logic [MstPortsIdxWidthOne-1:0]           mst_port_idx_t;
  typedef logic [MstPortsIdxWidth-1:0]              mst_port_idx_m1_t;

  // signals from the axi_demuxes, one index more for decode error
  req_t  [Cfg.NoSlvPorts-1:0][Cfg.NoMstPorts:0]  slv_reqs;
  resp_t [Cfg.NoSlvPorts-1:0][Cfg.NoMstPorts:0]  slv_resps;

  logic  [Cfg.NoSlvPorts-1:0][Cfg.NoMstPorts:0]  slv_is_mcast;
  logic  [Cfg.NoSlvPorts-1:0][Cfg.NoMstPorts:0]  slv_aw_commit;

  // workaround for issue #133 (problem with vsim 10.6c)
  localparam int unsigned cfg_NoMstPorts = Cfg.NoMstPorts;

  for (genvar i = 0; i < Cfg.NoSlvPorts; i++) begin : gen_slv_port_demux
    mst_port_idx_m1_t           dec_ar_select;
    logic                       dec_ar_valid,  dec_ar_error;
    mst_port_idx_t              slv_ar_select;

    addr_decode #(
      .NoIndices  ( Cfg.NoMstPorts  ),
      .addr_t     ( addr_t          ),
      .NoRules    ( Cfg.NoAddrRules ),
      .rule_t     ( rule_t          )
    ) i_axi_ar_decode (
      .addr_i           ( slv_ports_req_i[i].ar.addr                    ),
      .addr_map_i       ( addr_map_i                                    ),
      .idx_o            ( dec_ar_select                                 ),
      .dec_valid_o      ( dec_ar_valid                                  ),
      .dec_error_o      ( dec_ar_error                                  ),
      .en_default_idx_i ( en_default_mst_port_i[i]                      ),
      .default_idx_i    ( mst_port_idx_m1_t'(default_mst_port_i[i].idx) )
    );
    assign slv_ar_select = (dec_ar_error) ?
        mst_port_idx_t'(Cfg.NoMstPorts) : mst_port_idx_t'(dec_ar_select);

    // make sure that the default slave does not get changed, if there is an unserved Ax
    // pragma translate_off
    `ifndef VERILATOR
    `ifndef XSIM
    default disable iff (~rst_ni);
    default_aw_mst_port_en: assert property(
      @(posedge clk_i) (slv_ports_req_i[i].aw_valid && !slv_ports_resp_o[i].aw_ready)
          |=> $stable(en_default_mst_port_i[i]))
        else $fatal (1, $sformatf("It is not allowed to change the default mst port\
                                   enable, when there is an unserved Aw beat. Slave Port: %0d", i));
    default_aw_mst_port: assert property(
      @(posedge clk_i) (slv_ports_req_i[i].aw_valid && !slv_ports_resp_o[i].aw_ready)
          |=> $stable(default_mst_port_i[i]))
        else $fatal (1, $sformatf("It is not allowed to change the default mst port\
                                   when there is an unserved Aw beat. Slave Port: %0d", i));
    default_ar_mst_port_en: assert property(
      @(posedge clk_i) (slv_ports_req_i[i].ar_valid && !slv_ports_resp_o[i].ar_ready)
          |=> $stable(en_default_mst_port_i[i]))
        else $fatal (1, $sformatf("It is not allowed to change the enable, when\
                                   there is an unserved Ar beat. Slave Port: %0d", i));
    default_ar_mst_port: assert property(
      @(posedge clk_i) (slv_ports_req_i[i].ar_valid && !slv_ports_resp_o[i].ar_ready)
          |=> $stable(default_mst_port_i[i]))
        else $fatal (1, $sformatf("It is not allowed to change the default mst port\
                                   when there is an unserved Ar beat. Slave Port: %0d", i));
    `endif
    `endif
    // pragma translate_on

    axi_mcast_demux #(
      .AxiIdWidth            ( Cfg.AxiIdWidthSlvPorts   ),  // ID Width
      .AtopSupport           ( ATOPs                    ),
      .aw_addr_t             ( addr_t                   ),  // AW Address Type
      .aw_chan_t             ( aw_chan_t                ),  // AW Channel Type
      .w_chan_t              ( w_chan_t                 ),  //  W Channel Type
      .b_chan_t              ( b_chan_t                 ),  //  B Channel Type
      .ar_chan_t             ( ar_chan_t                ),  // AR Channel Type
      .r_chan_t              ( r_chan_t                 ),  //  R Channel Type
      .axi_req_t             ( req_t                    ),
      .axi_resp_t            ( resp_t                   ),
      .NoMstPorts            ( Cfg.NoMstPorts + 1       ),
      .MaxTrans              ( Cfg.MaxMstTrans          ),
      .AxiLookBits           ( Cfg.AxiIdUsedSlvPorts    ),
      .UniqueIds             ( Cfg.UniqueIds            ),
      .SpillAw               ( Cfg.LatencyMode[9]       ),
      .SpillW                ( Cfg.LatencyMode[8]       ),
      .SpillB                ( Cfg.LatencyMode[7]       ),
      .SpillAr               ( Cfg.LatencyMode[6]       ),
      .SpillR                ( Cfg.LatencyMode[5]       ),
      .Connectivity          ( Connectivity[i]          ),
      .MulticastConnectivity ( MulticastConnectivity[i] ),
      .rule_t                ( rule_t                   ),
      .NoAddrRules           ( Cfg.NoAddrRules          ),
      .NoMulticastRules      ( Cfg.NoMulticastRules     ),
      .NoMulticastPorts      ( Cfg.NoMulticastPorts     )
    ) i_axi_demux (
      .clk_i,   // Clock
      .rst_ni,  // Asynchronous reset active low
      .test_i,  // Testmode enable
      .addr_map_i            ( addr_map_i               ),
      .en_default_mst_port_i ( en_default_mst_port_i[i] ),
      .default_mst_port_i    ( default_mst_port_i[i]    ),
      .slv_req_i             ( slv_ports_req_i[i]       ),
      .slv_ar_select_i       ( slv_ar_select            ),
      .slv_resp_o            ( slv_ports_resp_o[i]      ),
      .mst_reqs_o            ( slv_reqs[i]              ),
      .mst_resps_i           ( slv_resps[i]             ),
      .mst_is_mcast_o        ( slv_is_mcast[i]          ),
      .mst_aw_commit_o       ( slv_aw_commit[i]         )
    );

    axi_err_slv #(
      .AxiIdWidth  ( Cfg.AxiIdWidthSlvPorts ),
      .axi_req_t   ( req_t                  ),
      .axi_resp_t  ( resp_t                 ),
      .Resp        ( axi_pkg::RESP_DECERR   ),
      .ATOPs       ( ATOPs                  ),
      .MaxTrans    ( 4                      )   // Transactions terminate at this slave, so minimize
                                                // resource consumption by accepting only a few
                                                // transactions at a time.
    ) i_axi_err_slv (
      .clk_i,   // Clock
      .rst_ni,  // Asynchronous reset active low
      .test_i,  // Testmode enable
      // slave port
      .slv_req_i  ( slv_reqs[i][Cfg.NoMstPorts]   ),
      .slv_resp_o ( slv_resps[i][cfg_NoMstPorts]  )
    );
  end

  // cross all channels
  for (genvar i = 0; i < Cfg.NoSlvPorts; i++) begin : gen_xbar_slv_cross
    for (genvar j = 0; j < Cfg.NoMstPorts; j++) begin : gen_xbar_mst_cross
      if (Connectivity[i][j]) begin : gen_connection

        assign mst_is_mcast_o[j][i] = slv_is_mcast[i][j];
        assign mst_aw_commit_o[j][i] = slv_aw_commit[i][j];

        axi_multicut #(
          .NoCuts     ( Cfg.PipelineStages ),
          .aw_chan_t  ( aw_chan_t          ),
          .w_chan_t   ( w_chan_t           ),
          .b_chan_t   ( b_chan_t           ),
          .ar_chan_t  ( ar_chan_t          ),
          .r_chan_t   ( r_chan_t           ),
          .axi_req_t  ( req_t              ),
          .axi_resp_t ( resp_t             )
        ) i_axi_multicut_xbar_pipeline (
          .clk_i,
          .rst_ni,
          .slv_req_i  ( slv_reqs[i][j]         ),
          .slv_resp_o ( slv_resps[i][j]        ),
          .mst_req_o  ( mst_ports_req_o[j][i]  ),
          .mst_resp_i ( mst_ports_resp_i[j][i] )
        );

      end else begin : gen_no_connection

        assign mst_is_mcast_o[j][i] = 1'b0;
        assign mst_aw_commit_o[j][i] = 1'b0;

        assign mst_ports_req_o[j][i] = '0;
        axi_err_slv #(
          .AxiIdWidth ( Cfg.AxiIdWidthSlvPorts  ),
          .axi_req_t  ( req_t                   ),
          .axi_resp_t ( resp_t                  ),
          .Resp       ( axi_pkg::RESP_DECERR    ),
          .ATOPs      ( ATOPs                   ),
          .MaxTrans   ( 1                       )
        ) i_axi_err_slv (
          .clk_i,
          .rst_ni,
          .test_i,
          .slv_req_i  ( slv_reqs[i][j]  ),
          .slv_resp_o ( slv_resps[i][j] )
        );
      end
    end
  end

  // pragma translate_off
  `ifndef VERILATOR
  `ifndef XSIM
  initial begin : check_params
    id_slv_req_ports: assert ($bits(slv_ports_req_i[0].aw.id ) == Cfg.AxiIdWidthSlvPorts) else
      $fatal(1, $sformatf("Slv_req and aw_chan id width not equal."));
    id_slv_resp_ports: assert ($bits(slv_ports_resp_o[0].r.id) == Cfg.AxiIdWidthSlvPorts) else
      $fatal(1, $sformatf("Slv_req and aw_chan id width not equal."));
    addr_slv_req_ports: assert ($bits(slv_ports_req_i[0].aw.addr) == Cfg.AxiAddrWidth) else
      $fatal(1, $sformatf("Slv_req and aw_addr width not equal."));
    addr_mst_req_ports: assert ($bits(mst_ports_req_o[0][0].aw.addr) == Cfg.AxiAddrWidth) else
      $fatal(1, $sformatf("Mst_req and aw_addr width not equal."));
    no_cuts_if_mcast: assert (!Cfg.EnableMulticast || (Cfg.PipelineStages == 0)) else
      $fatal(1, $sformatf("Multicast XBAR currently does not support pipeline stages."));
  end
  `endif
  `endif
  // pragma translate_on
endmodule

`ifndef VCS
// As of now, VCS does not support multi-dimensional array of interfaces.
`include "axi/assign.svh"
`include "axi/typedef.svh"

module axi_mcast_xbar_unmuxed_intf
import cf_math_pkg::idx_width;
#(
  parameter int unsigned AXI_USER_WIDTH =  0,
  parameter axi_pkg::xbar_cfg_t Cfg     = '0,
  parameter bit ATOPS                   = 1'b1,
  parameter bit [Cfg.NoSlvPorts-1:0][Cfg.NoMstPorts-1:0] CONNECTIVITY = '1,
  parameter bit [Cfg.NoSlvPorts-1:0][Cfg.NoMstPorts-1:0] MULTICAST_CONNECTIVITY = '1,
  parameter type rule_t                 = axi_pkg::xbar_rule_64_t
) (
  input  logic                                                      clk_i,
  input  logic                                                      rst_ni,
  input  logic                                                      test_i,
  AXI_BUS.Slave                                                     slv_ports [Cfg.NoSlvPorts-1:0],
  AXI_BUS.Master                                                    mst_ports [Cfg.NoMstPorts-1:0][Cfg.NoSlvPorts-1:0],
  input  rule_t [Cfg.NoAddrRules-1:0]                               addr_map_i,
  input  logic  [Cfg.NoSlvPorts-1:0]                                en_default_mst_port_i,
  input  logic  [Cfg.NoSlvPorts-1:0][idx_width(Cfg.NoMstPorts)-1:0] default_mst_port_i
);

  typedef logic [Cfg.AxiIdWidthSlvPorts -1:0] id_t;
  typedef logic [Cfg.AxiAddrWidth       -1:0] addr_t;
  typedef logic [Cfg.AxiDataWidth       -1:0] data_t;
  typedef logic [Cfg.AxiDataWidth/8     -1:0] strb_t;
  typedef logic [AXI_USER_WIDTH         -1:0] user_t;

  `AXI_TYPEDEF_AW_CHAN_T(aw_chan_t, addr_t, id_t, user_t)
  `AXI_TYPEDEF_W_CHAN_T(w_chan_t, data_t, strb_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T(b_chan_t, id_t, user_t)
  `AXI_TYPEDEF_AR_CHAN_T(ar_chan_t, addr_t, id_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(r_chan_t, data_t, id_t, user_t)
  `AXI_TYPEDEF_REQ_T(req_t, aw_chan_t, w_chan_t, ar_chan_t)
  `AXI_TYPEDEF_RESP_T(resp_t, b_chan_t, r_chan_t)

  req_t   [Cfg.NoMstPorts-1:0][Cfg.NoSlvPorts-1:0] mst_reqs;
  resp_t  [Cfg.NoMstPorts-1:0][Cfg.NoSlvPorts-1:0] mst_resps;
  req_t   [Cfg.NoSlvPorts-1:0]                     slv_reqs;
  resp_t  [Cfg.NoSlvPorts-1:0]                     slv_resps;

  for (genvar i = 0; i < Cfg.NoMstPorts; i++) begin : gen_assign_mst
    for (genvar j = 0; j < Cfg.NoSlvPorts; j++) begin : gen_assign_mst_inner
      `AXI_ASSIGN_FROM_REQ(mst_ports[i][j], mst_reqs[i][j])
      `AXI_ASSIGN_TO_RESP(mst_resps[i][j], mst_ports[i][j])
    end
  end

  for (genvar i = 0; i < Cfg.NoSlvPorts; i++) begin : gen_assign_slv
    `AXI_ASSIGN_TO_REQ(slv_reqs[i], slv_ports[i])
    `AXI_ASSIGN_FROM_RESP(slv_ports[i], slv_resps[i])
  end

  axi_mcast_xbar_unmuxed #(
    .Cfg          ( Cfg          ),
    .ATOPs        ( ATOPS        ),
    .Connectivity ( CONNECTIVITY ),
    .MulticastConnectivity ( MULTICAST_CONNECTIVITY ),
    .aw_chan_t    ( aw_chan_t    ),
    .w_chan_t     ( w_chan_t     ),
    .b_chan_t     ( b_chan_t     ),
    .ar_chan_t    ( ar_chan_t    ),
    .r_chan_t     ( r_chan_t     ),
    .req_t        ( req_t        ),
    .resp_t       ( resp_t       ),
    .rule_t       ( rule_t       )
  ) i_xbar (
    .clk_i,
    .rst_ni,
    .test_i,
    .slv_ports_req_i  (slv_reqs ),
    .slv_ports_resp_o (slv_resps),
    .mst_ports_req_o  (mst_reqs ),
    .mst_ports_resp_i (mst_resps),
    .addr_map_i,
    .en_default_mst_port_i,
    .default_mst_port_i
  );

endmodule

`endif
