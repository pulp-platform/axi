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

/// axi_xbar: Fully-connected AXI4+ATOP crossbar with an arbitrary number of subordinate and manager ports.
/// See `doc/axi_xbar.md` for the documentation, including the definition of parameters and ports.
module axi_xbar
import cf_math_pkg::idx_width;
#(
  /// Configuration struct for the crossbar see `axi_pkg` for fields and definitions.
  parameter axi_pkg::xbar_cfg_t Cfg                                     = '0,
  /// Enable atomic operations support.
  parameter bit  ATOPs                                                  = 1'b1,
  /// Connectivity matrix
  parameter bit [Cfg.NumSbrPorts-1:0][Cfg.NumMgrPorts-1:0] Connectivity = '1,
  /// AXI4+ATOP AW channel struct type for the subordinate ports.
  parameter type sbr_aw_chan_t                                          = logic,
  /// AXI4+ATOP AW channel struct type for the manager ports.
  parameter type mgr_aw_chan_t                                          = logic,
  /// AXI4+ATOP W channel struct type for all ports.
  parameter type w_chan_t                                               = logic,
  /// AXI4+ATOP B channel struct type for the subordinate ports.
  parameter type sbr_b_chan_t                                           = logic,
  /// AXI4+ATOP B channel struct type for the manager ports.
  parameter type mgr_b_chan_t                                           = logic,
  /// AXI4+ATOP AR channel struct type for the subordinate ports.
  parameter type sbr_ar_chan_t                                          = logic,
  /// AXI4+ATOP AR channel struct type for the manager ports.
  parameter type mgr_ar_chan_t                                          = logic,
  /// AXI4+ATOP R channel struct type for the subordinate ports.
  parameter type sbr_r_chan_t                                           = logic,
  /// AXI4+ATOP R channel struct type for the manager ports.
  parameter type mgr_r_chan_t                                           = logic,
  /// AXI4+ATOP request struct type for the subordinate ports.
  parameter type sbr_port_axi_req_t                                     = logic,
  /// AXI4+ATOP response struct type for the subordinate ports.
  parameter type sbr_port_axi_rsp_t                                     = logic,
  /// AXI4+ATOP request struct type for the manager ports.
  parameter type mgr_port_axi_req_t                                     = logic,
  /// AXI4+ATOP response struct type for the manager ports
  parameter type mgr_port_axi_rsp_t                                     = logic,
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
  parameter type rule_t                                                 = axi_pkg::xbar_rule_64_t
`ifdef VCS
  , localparam int unsigned MgrPortsIdxWidth =
      (Cfg.NumMgrPorts == 32'd1) ? 32'd1 : unsigned'($clog2(Cfg.NumMgrPorts))
`endif
) (
  /// Clock, positive edge triggered.
  input  logic                                                            clk_i,
  /// Asynchronous reset, active low.
  input  logic                                                            rst_ni,
  /// Testmode enable, active high.
  input  logic                                                            test_i,
  /// AXI4+ATOP requests to the subordinate ports.
  input  sbr_port_axi_req_t [Cfg.NumSbrPorts-1:0]                                 sbr_ports_req_i,
  /// AXI4+ATOP responses of the subordinate ports.
  output sbr_port_axi_rsp_t [Cfg.NumSbrPorts-1:0]                                 sbr_ports_rsp_o,
  /// AXI4+ATOP requests of the manager ports.
  output mgr_port_axi_req_t [Cfg.NumMgrPorts-1:0]                                 mgr_ports_req_o,
  /// AXI4+ATOP responses to the manager ports.
  input  mgr_port_axi_rsp_t [Cfg.NumMgrPorts-1:0]                                 mgr_ports_rsp_i,
  /// Address map array input for the crossbar. This map is global for the whole module.
  /// It is used for routing the transactions to the respective manager ports.
  /// Each manager port can have multiple different rules.
  input  rule_t     [Cfg.NumAddrRules-1:0]                                addr_map_i,
  /// Enable default manager port.
  input  logic      [Cfg.NumSbrPorts-1:0]                                 en_default_mgr_port_i,
`ifdef VCS
  /// Enables a default manager port for each subordinate port. When this is enabled unmapped
  /// transactions get issued at the manager port given by `default_mgr_port_i`.
  /// When not used, tie to `'0`.
  input  logic      [Cfg.NumSbrPorts-1:0][MgrPortsIdxWidth-1:0]           default_mgr_port_i
`else
  /// Enables a default manager port for each subordinate port. When this is enabled unmapped
  /// transactions get issued at the manager port given by `default_mgr_port_i`.
  /// When not used, tie to `'0`.
  input  logic      [Cfg.NumSbrPorts-1:0][idx_width(Cfg.NumMgrPorts)-1:0] default_mgr_port_i
`endif
);

  // Address tpye for inidvidual address signals
  typedef logic [Cfg.AddrWidth-1:0] addr_t;
  // to account for the decoding error subordinate
`ifdef VCS
  localparam int unsigned MgrPortsIdxWidthOne =
      (Cfg.NumMgrPorts == 32'd1) ? 32'd1 : unsigned'($clog2(Cfg.NumMgrPorts + 1));
  typedef logic [MgrPortsIdxWidthOne-1:0]           mgr_port_idx_t;
`else
  typedef logic [idx_width(Cfg.NumMgrPorts + 1)-1:0] mgr_port_idx_t;
`endif

  // signals from the axi_demuxes, one index more for decode error
  sbr_port_axi_req_t [Cfg.NumSbrPorts-1:0][Cfg.NumMgrPorts:0]  sbr_reqs;
  sbr_port_axi_rsp_t [Cfg.NumSbrPorts-1:0][Cfg.NumMgrPorts:0]  sbr_rsps;

  // workaround for issue #133 (problem with vsim 10.6c)
  localparam int unsigned cfg_NumMgrPorts = Cfg.NumMgrPorts;

  // signals into the axi_muxes, are of type subordinate as the multiplexer extends the ID
  sbr_port_axi_req_t [Cfg.NumMgrPorts-1:0][Cfg.NumSbrPorts-1:0] mgr_reqs;
  sbr_port_axi_rsp_t [Cfg.NumMgrPorts-1:0][Cfg.NumSbrPorts-1:0] mgr_rsps;

  for (genvar i = 0; i < Cfg.NumSbrPorts; i++) begin : gen_sbr_port_demux
`ifdef VCS
    logic [MgrPortsIdxWidth-1:0]          dec_aw,        dec_ar;
`else
    logic [idx_width(Cfg.NumMgrPorts)-1:0] dec_aw,        dec_ar;
`endif
    mgr_port_idx_t                        sbr_aw_select, sbr_ar_select;
    logic                                 dec_aw_valid,  dec_aw_error;
    logic                                 dec_ar_valid,  dec_ar_error;

    addr_decode #(
      .NoIndices  ( Cfg.NumMgrPorts  ),
      .NoRules    ( Cfg.NumAddrRules ),
      .addr_t     ( addr_t           ),
      .rule_t     ( rule_t           )
    ) i_axi_aw_decode (
      .addr_i           ( sbr_ports_req_i[i].aw.addr ),
      .addr_map_i       ( addr_map_i                 ),
      .idx_o            ( dec_aw                     ),
      .dec_valid_o      ( dec_aw_valid               ),
      .dec_error_o      ( dec_aw_error               ),
      .en_default_idx_i ( en_default_mgr_port_i[i]   ),
      .default_idx_i    ( default_mgr_port_i[i]      )
    );

    addr_decode #(
      .NoIndices  ( Cfg.NumMgrPorts  ),
      .addr_t     ( addr_t           ),
      .NoRules    ( Cfg.NumAddrRules ),
      .rule_t     ( rule_t           )
    ) i_axi_ar_decode (
      .addr_i           ( sbr_ports_req_i[i].ar.addr ),
      .addr_map_i       ( addr_map_i                 ),
      .idx_o            ( dec_ar                     ),
      .dec_valid_o      ( dec_ar_valid               ),
      .dec_error_o      ( dec_ar_error               ),
      .en_default_idx_i ( en_default_mgr_port_i[i]   ),
      .default_idx_i    ( default_mgr_port_i[i]      )
    );

    assign sbr_aw_select = (dec_aw_error) ?
        mgr_port_idx_t'(Cfg.NumMgrPorts) : mgr_port_idx_t'(dec_aw);
    assign sbr_ar_select = (dec_ar_error) ?
        mgr_port_idx_t'(Cfg.NumMgrPorts) : mgr_port_idx_t'(dec_ar);

    // make sure that the default subordinate does not get changed, if there is an unserved Ax
    // pragma translate_off
    `ifndef VERILATOR
    `ifndef XSIM
    default disable iff (~rst_ni);
    default_aw_mgr_port_en: assert property(
      @(posedge clk_i) (sbr_ports_req_i[i].aw_valid && !sbr_ports_rsp_o[i].aw_ready)
          |=> $stable(en_default_mgr_port_i[i]))
        else $fatal (1, $sformatf("It is not allowed to change the default mgr port\
                                   enable, when there is an unserved Aw beat. Subordinate Port: %0d", i));
    default_aw_mgr_port: assert property(
      @(posedge clk_i) (sbr_ports_req_i[i].aw_valid && !sbr_ports_rsp_o[i].aw_ready)
          |=> $stable(default_mgr_port_i[i]))
        else $fatal (1, $sformatf("It is not allowed to change the default mgr port\
                                   when there is an unserved Aw beat. Subordinate Port: %0d", i));
    default_ar_mgr_port_en: assert property(
      @(posedge clk_i) (sbr_ports_req_i[i].ar_valid && !sbr_ports_rsp_o[i].ar_ready)
          |=> $stable(en_default_mgr_port_i[i]))
        else $fatal (1, $sformatf("It is not allowed to change the enable, when\
                                   there is an unserved Ar beat. Subordinate Port: %0d", i));
    default_ar_mgr_port: assert property(
      @(posedge clk_i) (sbr_ports_req_i[i].ar_valid && !sbr_ports_rsp_o[i].ar_ready)
          |=> $stable(default_mgr_port_i[i]))
        else $fatal (1, $sformatf("It is not allowed to change the default mgr port\
                                   when there is an unserved Ar beat. Subordinate Port: %0d", i));
    `endif
    `endif
    // pragma translate_on
    axi_demux #(
      .IdWidth        ( Cfg.IdWidthSbrPorts ),  // ID Width
      .AtopSupport    ( ATOPs               ),
      .aw_chan_t      ( sbr_aw_chan_t       ),  // AW Channel Type
      .w_chan_t       ( w_chan_t            ),  //  W Channel Type
      .b_chan_t       ( sbr_b_chan_t        ),  //  B Channel Type
      .ar_chan_t      ( sbr_ar_chan_t       ),  // AR Channel Type
      .r_chan_t       ( sbr_r_chan_t        ),  //  R Channel Type
      .axi_req_t      ( sbr_port_axi_req_t  ),
      .axi_rsp_t      ( sbr_port_axi_rsp_t  ),
      .NumMgrPorts    ( Cfg.NumMgrPorts + 1 ),
      .MaxTrans       ( Cfg.MaxMgrTrans     ),
      .LookBits       ( Cfg.IdUsedSbrPorts  ),
      .UniqueIds      ( Cfg.UniqueIds       ),
      .SpillAw        ( Cfg.LatencyMode[9]  ),
      .SpillW         ( Cfg.LatencyMode[8]  ),
      .SpillB         ( Cfg.LatencyMode[7]  ),
      .SpillAr        ( Cfg.LatencyMode[6]  ),
      .SpillR         ( Cfg.LatencyMode[5]  )
    ) i_axi_demux (
      .clk_i,   // Clock
      .rst_ni,  // Asynchronous reset active low
      .test_i,  // Testmode enable
      .sbr_req_i       ( sbr_ports_req_i[i] ),
      .sbr_aw_select_i ( sbr_aw_select      ),
      .sbr_ar_select_i ( sbr_ar_select      ),
      .sbr_rsp_o       ( sbr_ports_rsp_o[i] ),
      .mgr_reqs_o      ( sbr_reqs[i]        ),
      .mgr_rsps_i      ( sbr_rsps[i]        )
    );

    axi_err_sbr #(
      .IdWidth     ( Cfg.IdWidthSbrPorts  ),
      .axi_req_t   ( sbr_port_axi_req_t   ),
      .axi_rsp_t   ( sbr_port_axi_rsp_t   ),
      .Resp        ( axi_pkg::RESP_DECERR ),
      .ATOPs       ( ATOPs                ),
      .MaxTrans    ( 4                    )   // Transactions terminate at this subordinate, so minimize
                                                // resource consumption by accepting only a few
                                                // transactions at a time.
    ) i_axi_err_sbr (
      .clk_i,   // Clock
      .rst_ni,  // Asynchronous reset active low
      .test_i,  // Testmode enable
      // subordinate port
      .sbr_req_i ( sbr_reqs[i][Cfg.NumMgrPorts]  ),
      .sbr_rsp_o ( sbr_rsps[i][cfg_NumMgrPorts]  )
    );
  end

  // cross all channels
  for (genvar i = 0; i < Cfg.NumSbrPorts; i++) begin : gen_xbar_sbr_cross
    for (genvar j = 0; j < Cfg.NumMgrPorts; j++) begin : gen_xbar_mgr_cross
      if (Connectivity[i][j]) begin : gen_connection
        axi_multicut #(
          .NumCuts    ( Cfg.PipelineStages ),
          .aw_chan_t  ( sbr_aw_chan_t      ),
          .w_chan_t   ( w_chan_t           ),
          .b_chan_t   ( sbr_b_chan_t       ),
          .ar_chan_t  ( sbr_ar_chan_t      ),
          .r_chan_t   ( sbr_r_chan_t       ),
          .axi_req_t  ( sbr_port_axi_req_t ),
          .axi_rsp_t  ( sbr_port_axi_rsp_t )
        ) i_axi_multicut_xbar_pipeline (
          .clk_i,
          .rst_ni,
          .sbr_req_i ( sbr_reqs[i][j] ),
          .sbr_rsp_o ( sbr_rsps[i][j] ),
          .mgr_req_o ( mgr_reqs[j][i] ),
          .mgr_rsp_i ( mgr_rsps[j][i] )
        );

      end else begin : gen_no_connection
        assign mgr_reqs[j][i] = '0;
        axi_err_sbr #(
          .IdWidth    ( Cfg.IdWidthSbrPorts  ),
          .axi_req_t  ( sbr_port_axi_req_t   ),
          .axi_rsp_t  ( sbr_port_axi_rsp_t   ),
          .Resp       ( axi_pkg::RESP_DECERR ),
          .ATOPs      ( ATOPs                ),
          .MaxTrans   ( 1                    )
        ) i_axi_err_sbr (
          .clk_i,
          .rst_ni,
          .test_i,
          .sbr_req_i ( sbr_reqs[i][j] ),
          .sbr_rsp_o ( sbr_rsps[i][j] )
        );
      end
    end
  end

  for (genvar i = 0; i < Cfg.NumMgrPorts; i++) begin : gen_mgr_port_mux
    axi_mux #(
      .SbrIDWidth         ( Cfg.IdWidthSbrPorts ), // ID width of the subordinate ports
      .sbr_aw_chan_t      ( sbr_aw_chan_t       ), // AW Channel Type, subordinate ports
      .mgr_aw_chan_t      ( mgr_aw_chan_t       ), // AW Channel Type, manager port
      .w_chan_t           ( w_chan_t            ), //  W Channel Type, all ports
      .sbr_b_chan_t       ( sbr_b_chan_t        ), //  B Channel Type, subordinate ports
      .mgr_b_chan_t       ( mgr_b_chan_t        ), //  B Channel Type, manager port
      .sbr_ar_chan_t      ( sbr_ar_chan_t       ), // AR Channel Type, subordinate ports
      .mgr_ar_chan_t      ( mgr_ar_chan_t       ), // AR Channel Type, manager port
      .sbr_r_chan_t       ( sbr_r_chan_t        ), //  R Channel Type, subordinate ports
      .mgr_r_chan_t       ( mgr_r_chan_t        ), //  R Channel Type, manager port
      .sbr_port_axi_req_t ( sbr_port_axi_req_t  ),
      .sbr_port_axi_rsp_t ( sbr_port_axi_rsp_t  ),
      .mgr_port_axi_req_t ( mgr_port_axi_req_t  ),
      .mgr_port_axi_rsp_t ( mgr_port_axi_rsp_t  ),
      .NumSbrPorts        ( Cfg.NumSbrPorts     ), // Number of Managers for the module
      .MaxWTrans          ( Cfg.MaxSbrTrans     ),
      .FallThrough        ( Cfg.FallThrough     ),
      .SpillAw            ( Cfg.LatencyMode[4]  ),
      .SpillW             ( Cfg.LatencyMode[3]  ),
      .SpillB             ( Cfg.LatencyMode[2]  ),
      .SpillAr            ( Cfg.LatencyMode[1]  ),
      .SpillR             ( Cfg.LatencyMode[0]  )
    ) i_axi_mux (
      .clk_i,   // Clock
      .rst_ni,  // Asynchronous reset active low
      .test_i,  // Test Mode enable
      .sbr_reqs_i ( mgr_reqs[i]        ),
      .sbr_rsps_o ( mgr_rsps[i]        ),
      .mgr_req_o  ( mgr_ports_req_o[i] ),
      .mgr_rsp_i  ( mgr_ports_rsp_i[i] )
    );
  end

  // pragma translate_off
  `ifndef VERILATOR
  `ifndef XSIM
  initial begin : check_params
    id_sbr_req_ports: assert ($bits(sbr_ports_req_i[0].aw.id ) == Cfg.IdWidthSbrPorts) else
      $fatal(1, $sformatf("Sbr_req and aw_chan id width not equal."));
    id_sbr_rsp_ports: assert ($bits(sbr_ports_rsp_o[0].r.id) == Cfg.IdWidthSbrPorts) else
      $fatal(1, $sformatf("Sbr_req and aw_chan id width not equal."));
  end
  `endif
  `endif
  // pragma translate_on
endmodule

`include "axi/assign.svh"
`include "axi/typedef.svh"

module axi_xbar_intf
import cf_math_pkg::idx_width;
#(
  parameter int unsigned AXI_USER_WIDTH =  0,
  parameter axi_pkg::xbar_cfg_t Cfg     = '0,
  parameter bit ATOPS                   = 1'b1,
  parameter bit [Cfg.NumSbrPorts-1:0][Cfg.NumMgrPorts-1:0] CONNECTIVITY = '1,
  parameter type rule_t                 = axi_pkg::xbar_rule_64_t
`ifdef VCS
  , localparam int unsigned MgrPortsIdxWidth =
        (Cfg.NumMgrPorts == 32'd1) ? 32'd1 : unsigned'($clog2(Cfg.NumMgrPorts))
`endif
) (
  input  logic                                                      clk_i,
  input  logic                                                      rst_ni,
  input  logic                                                      test_i,
  AXI_BUS.Subordinate                                                     sbr_ports [Cfg.NumSbrPorts-1:0],
  AXI_BUS.Manager                                                    mgr_ports [Cfg.NumMgrPorts-1:0],
  input  rule_t [Cfg.NumAddrRules-1:0]                               addr_map_i,
  input  logic  [Cfg.NumSbrPorts-1:0]                                en_default_mgr_port_i,
`ifdef VCS
  input  logic  [Cfg.NumSbrPorts-1:0][MgrPortsIdxWidth-1:0]          default_mgr_port_i
`else
  input  logic  [Cfg.NumSbrPorts-1:0][idx_width(Cfg.NumMgrPorts)-1:0] default_mgr_port_i
`endif
);

  localparam int unsigned IdWidthMgrPorts = Cfg.IdWidthSbrPorts + $clog2(Cfg.NumSbrPorts);

  typedef logic [IdWidthMgrPorts     -1:0] id_mgr_t;
  typedef logic [Cfg.IdWidthSbrPorts -1:0] id_sbr_t;
  typedef logic [Cfg.AddrWidth       -1:0] addr_t;
  typedef logic [Cfg.DataWidth       -1:0] data_t;
  typedef logic [Cfg.DataWidth/8     -1:0] strb_t;
  typedef logic [AXI_USER_WIDTH      -1:0] user_t;

  `AXI_TYPEDEF_AW_CHAN_T(mgr_aw_chan_t, addr_t, id_mgr_t, user_t)
  `AXI_TYPEDEF_AW_CHAN_T(sbr_aw_chan_t, addr_t, id_sbr_t, user_t)
  `AXI_TYPEDEF_W_CHAN_T(w_chan_t, data_t, strb_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T(mgr_b_chan_t, id_mgr_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T(sbr_b_chan_t, id_sbr_t, user_t)
  `AXI_TYPEDEF_AR_CHAN_T(mgr_ar_chan_t, addr_t, id_mgr_t, user_t)
  `AXI_TYPEDEF_AR_CHAN_T(sbr_ar_chan_t, addr_t, id_sbr_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(mgr_r_chan_t, data_t, id_mgr_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(sbr_r_chan_t, data_t, id_sbr_t, user_t)
  `AXI_TYPEDEF_REQ_T(mgr_port_axi_req_t, mgr_aw_chan_t, w_chan_t, mgr_ar_chan_t)
  `AXI_TYPEDEF_REQ_T(sbr_port_axi_req_t, sbr_aw_chan_t, w_chan_t, sbr_ar_chan_t)
  `AXI_TYPEDEF_RSP_T(mgr_port_axi_rsp_t, mgr_b_chan_t, mgr_r_chan_t)
  `AXI_TYPEDEF_RSP_T(sbr_port_axi_rsp_t, sbr_b_chan_t, sbr_r_chan_t)

  mgr_port_axi_req_t  [Cfg.NumMgrPorts-1:0]  mgr_reqs;
  mgr_port_axi_rsp_t  [Cfg.NumMgrPorts-1:0]  mgr_rsps;
  sbr_port_axi_req_t  [Cfg.NumSbrPorts-1:0]  sbr_reqs;
  sbr_port_axi_rsp_t  [Cfg.NumSbrPorts-1:0]  sbr_rsps;

  for (genvar i = 0; i < Cfg.NumMgrPorts; i++) begin : gen_assign_mgr
    `AXI_ASSIGN_FROM_REQ(mgr_ports[i], mgr_reqs[i])
    `AXI_ASSIGN_TO_RSP(mgr_rsps[i], mgr_ports[i])
  end

  for (genvar i = 0; i < Cfg.NumSbrPorts; i++) begin : gen_assign_sbr
    `AXI_ASSIGN_TO_REQ(sbr_reqs[i], sbr_ports[i])
    `AXI_ASSIGN_FROM_RSP(sbr_ports[i], sbr_rsps[i])
  end

  axi_xbar #(
    .Cfg  (Cfg),
    .ATOPs              ( ATOPS              ),
    .Connectivity       ( CONNECTIVITY       ),
    .sbr_aw_chan_t      ( sbr_aw_chan_t      ),
    .mgr_aw_chan_t      ( mgr_aw_chan_t      ),
    .w_chan_t           ( w_chan_t           ),
    .sbr_b_chan_t       ( sbr_b_chan_t       ),
    .mgr_b_chan_t       ( mgr_b_chan_t       ),
    .sbr_ar_chan_t      ( sbr_ar_chan_t      ),
    .mgr_ar_chan_t      ( mgr_ar_chan_t      ),
    .sbr_r_chan_t       ( sbr_r_chan_t       ),
    .mgr_r_chan_t       ( mgr_r_chan_t       ),
    .sbr_port_axi_req_t ( sbr_port_axi_req_t ),
    .sbr_port_axi_rsp_t ( sbr_port_axi_rsp_t ),
    .mgr_port_axi_req_t ( mgr_port_axi_req_t ),
    .mgr_port_axi_rsp_t ( mgr_port_axi_rsp_t ),
    .rule_t             ( rule_t             )
  ) i_xbar (
    .clk_i,
    .rst_ni,
    .test_i,
    .sbr_ports_req_i (sbr_reqs),
    .sbr_ports_rsp_o (sbr_rsps),
    .mgr_ports_req_o (mgr_reqs),
    .mgr_ports_rsp_i (mgr_rsps),
    .addr_map_i,
    .en_default_mgr_port_i,
    .default_mgr_port_i
  );

endmodule
