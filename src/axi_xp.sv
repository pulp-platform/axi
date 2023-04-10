// Copyright (c) 2020 ETH Zurich, University of Bologna
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
// Authors:
// - Tim Fischer <fischeti@iis.ee.ethz.ch>
// - Andreas Kurth <akurth@iis.ee.ethz.ch>
// - Vikram Jain <jvikram@iis.ee.ethz.ch>

`include "axi/typedef.svh"

/// AXI Crosspoint (XP) with homomorphous subordinate and manager ports.
module axi_xp #(
  // Atomic operations settings
  parameter bit  ATOPs = 1'b1,
  // xbar configuration
  parameter axi_pkg::xbar_cfg_t Cfg = '0,
  /// Number of subordinate ports.
  parameter int unsigned NumSbrPorts = 32'd0,
  /// Number of manager ports.
  parameter int unsigned NumMgrPorts = 32'd0,
  /// Connectivity from a subordinate port to the manager ports.  A `1'b1` in `Connectivity[i][j]` means
  /// that subordinate port `i` is connected to manager port `j`.  By default, all subordinate ports are
  /// connected to all manager ports.
  parameter bit [NumSbrPorts-1:0][NumMgrPorts-1:0] Connectivity = '1,
  /// Address width of all ports.
  parameter int unsigned AddrWidth = 32'd0,
  /// Data width of all ports.
  parameter int unsigned DataWidth = 32'd0,
  /// ID width of all ports.
  parameter int unsigned IdWidth = 32'd0,
  /// User signal width of all ports.
  parameter int unsigned UserWidth = 32'd0,
  /// Maximum number of different IDs that can be in flight at each subordinate port.  Reads and writes
  /// are counted separately (except for ATOPs, which count as both read and write).
  ///
  /// It is legal for upstream to have transactions with more unique IDs than the maximum given by
  /// this parameter in flight, but a transaction exceeding the maximum will be stalled until all
  /// transactions of another ID complete.
  parameter int unsigned SbrPortMaxUniqIds = 32'd0,
  /// Maximum number of in-flight transactions with the same ID at the subordinate port.
  ///
  /// This parameter is only relevant if `SbrPortMaxUniqIds <= 2**MgrPortIdWidth`.  In that
  /// case, this parameter is passed to [`axi_id_remap` as `MaxTxnsPerId`
  /// parameter](module.axi_id_remap#parameter.MaxTxnsPerId).
  parameter int unsigned SbrPortMaxTxnsPerId = 32'd0,
  /// Maximum number of in-flight transactions at the subordinate port.  Reads and writes are counted
  /// separately (except for ATOPs, which count as both read and write).
  ///
  /// This parameter is only relevant if `SbrPortMaxUniqIds > 2**MgrPortIdWidth`.  In that
  /// case, this parameter is passed to
  /// [`axi_id_serialize`](module.axi_id_serialize#parameter.SbrPortMaxTxns).
  parameter int unsigned SbrPortMaxTxns = 32'd0,
  /// Maximum number of different IDs that can be in flight at the manager port.  Reads and writes
  /// are counted separately (except for ATOPs, which count as both read and write).
  ///
  /// This parameter is only relevant if `SbrPortMaxUniqIds > 2**MgrPortIdWidth`.  In that
  /// case, this parameter is passed to
  /// [`axi_id_serialize`](module.axi_id_serialize#parameter.MgrPortMaxUniqIds).
  parameter int unsigned MgrPortMaxUniqIds = 32'd0,
  /// Maximum number of in-flight transactions with the same ID at the manager port.
  ///
  /// This parameter is only relevant if `SbrPortMaxUniqIds > 2**MgrPortIdWidth`.  In that
  /// case, this parameter is passed to
  /// [`axi_id_serialize`](module.axi_id_serialize#parameter.MgrPortMaxTxnsPerId).
  parameter int unsigned MgrPortMaxTxnsPerId = 32'd0,
  /// Number of rules in the address map.
  parameter int unsigned NumAddrRules = 32'd0,
  /// Request struct type of the AXI4+ATOP
  parameter type axi_req_t = logic,
  /// Response struct type of the AXI4+ATOP
  parameter type axi_rsp_t = logic,
  /// Rule type (see documentation of `axi_xbar` for details).
  parameter type rule_t = axi_pkg::xbar_rule_64_t
) (
  /// Rising-edge clock of all ports
  input  logic                         clk_i,
  /// Asynchronous reset, active low
  input  logic                         rst_ni,
  /// Test mode enable
  input  logic                         test_en_i,
  /// Subordinate ports request
  input  axi_req_t [NumSbrPorts-1:0]   sbr_req_i,
  /// Subordinate ports response
  output axi_rsp_t [NumSbrPorts-1:0]   sbr_rsp_o,
  /// Manager ports request
  output axi_req_t [NumMgrPorts-1:0]   mgr_req_o,
  /// Manager ports response
  input  axi_rsp_t [NumMgrPorts-1:0]   mgr_rsp_i,
  /// Address map for transferring transactions from subordinate to manager ports
  input  rule_t    [NumAddrRules-1:0]  addr_map_i
);

  // The manager port of the Xbar has a different ID width than the subordinate ports.
  parameter int unsigned XbarIdWidth = IdWidth + $clog2(NumSbrPorts);
  typedef logic [AddrWidth-1:0]    addr_t;
  typedef logic [DataWidth-1:0]    data_t;
  typedef logic [IdWidth-1:0]      id_t;
  typedef logic [XbarIdWidth-1:0]  xbar_id_t;
  typedef logic [DataWidth/8-1:0]  strb_t;
  typedef logic [UserWidth-1:0]    user_t;


  `AXI_TYPEDEF_ALL(xp, addr_t, id_t, data_t, strb_t, user_t)
  `AXI_TYPEDEF_ALL(xbar, addr_t, xbar_id_t, data_t, strb_t, user_t)

  xbar_req_t [NumMgrPorts-1:0] xbar_req;
  xbar_rsp_t [NumMgrPorts-1:0] xbar_rsp;

  axi_xbar #(
    .Cfg            ( Cfg             ),
    .ATOPs          ( ATOPs           ),
    .Connectivity   ( Connectivity    ),
    .sbr_aw_chan_t  ( xp_aw_chan_t    ),
    .mgr_aw_chan_t  ( xbar_aw_chan_t  ),
    .w_chan_t       ( xp_w_chan_t     ),
    .sbr_b_chan_t   ( xp_b_chan_t     ),
    .mgr_b_chan_t   ( xbar_b_chan_t   ),
    .sbr_ar_chan_t  ( xp_ar_chan_t    ),
    .mgr_ar_chan_t  ( xbar_ar_chan_t  ),
    .sbr_r_chan_t   ( xp_r_chan_t     ),
    .mgr_r_chan_t   ( xbar_r_chan_t   ),
    .sbr_req_t      ( axi_req_t       ),
    .sbr_rsp_t      ( axi_rsp_t       ),
    .mgr_req_t      ( xbar_req_t      ),
    .mgr_rsp_t      ( xbar_rsp_t      ),
    .rule_t         ( rule_t          )
  ) i_xbar (
    .clk_i,
    .rst_ni,
    .test_i                 ( test_en_i                               ),
    .sbr_ports_req_i        ( sbr_req_i                               ),
    .sbr_ports_rsp_o        ( sbr_rsp_o                               ),
    .mgr_ports_req_o        ( xbar_req                                ),
    .mgr_ports_rsp_i        ( xbar_rsp                                ),
    .addr_map_i,
    .en_default_mgr_port_i  ( '0                                      ),
    .default_mgr_port_i     ( '0                                      )
  );

  for (genvar i = 0; i < NumMgrPorts; i++) begin : gen_remap
    axi_id_remap #(
      .SbrPortIdWidth    ( XbarIdWidth         ),
      .SbrPortMaxUniqIds ( SbrPortMaxUniqIds   ),
      .MaxTxnsPerId      ( SbrPortMaxTxnsPerId ),
      .MgrPortIdWidth    ( IdWidth             ),
      .sbr_req_t         ( xbar_req_t          ),
      .sbr_rsp_t         ( xbar_rsp_t          ),
      .mgr_req_t         ( axi_req_t           ),
      .mgr_rsp_t         ( axi_rsp_t           )
    ) i_axi_id_remap (
      .clk_i,
      .rst_ni,
      .sbr_req_i ( xbar_req[i]  ),
      .sbr_rsp_o ( xbar_rsp[i]  ),
      .mgr_req_o ( mgr_req_o[i] ),
      .mgr_rsp_i ( mgr_rsp_i[i] )
    );
  end

endmodule

`include "axi/assign.svh"
`include "axi/typedef.svh"

module axi_xp_intf
import cf_math_pkg::idx_width;
#(
  parameter bit  ATOPs = 1'b1,
  parameter axi_pkg::xbar_cfg_t Cfg = '0,
  parameter int unsigned NumSbrPorts = 32'd0,
  parameter int unsigned NumMgrPorts = 32'd0,
  parameter bit [NumSbrPorts-1:0][NumMgrPorts-1:0] Connectivity = '1,
  parameter int unsigned AddrWidth = 32'd0,
  parameter int unsigned DataWidth = 32'd0,
  parameter int unsigned IdWidth = 32'd0,
  parameter int unsigned UserWidth = 32'd0,
  parameter int unsigned SbrPortMaxUniqIds = 32'd0,
  parameter int unsigned SbrPortMaxTxnsPerId = 32'd0,
  parameter int unsigned SbrPortMaxTxns = 32'd0,
  parameter int unsigned MgrPortMaxUniqIds = 32'd0,
  parameter int unsigned MgrPortMaxTxnsPerId = 32'd0,
  parameter int unsigned NumAddrRules = 32'd0,
  parameter type rule_t = axi_pkg::xbar_rule_64_t
) (
  input  logic                       clk_i,
  input  logic                       rst_ni,
  input  logic                       test_en_i,
  AXI_BUS.Subordinate                      sbr_ports [NumSbrPorts-1:0],
  AXI_BUS.Manager                     mgr_ports [NumMgrPorts-1:0],
  input  rule_t  [NumAddrRules-1:0]  addr_map_i
);

  // localparam int unsigned IdWidthMgrPorts = IdWidth + $clog2(NumSbrPorts);

  typedef logic [IdWidth         -1:0] id_t;
  typedef logic [AddrWidth       -1:0] addr_t;
  typedef logic [DataWidth       -1:0] data_t;
  typedef logic [DataWidth/8     -1:0] strb_t;
  typedef logic [UserWidth       -1:0] user_t;

  `AXI_TYPEDEF_ALL(axi, addr_t, id_t, data_t, strb_t, user_t)

  axi_req_t  [NumMgrPorts-1:0]  mgr_reqs;
  axi_rsp_t  [NumMgrPorts-1:0]  mgr_rsps;
  axi_req_t  [NumSbrPorts-1:0]  sbr_reqs;
  axi_rsp_t  [NumSbrPorts-1:0]  sbr_rsps;

  for (genvar i = 0; i < NumMgrPorts; i++) begin : gen_assign_mgr
    `AXI_ASSIGN_FROM_REQ(mgr_ports[i], mgr_reqs[i])
    `AXI_ASSIGN_TO_RSP(mgr_rsps[i], mgr_ports[i])
  end

  for (genvar i = 0; i < NumSbrPorts; i++) begin : gen_assign_sbr
    `AXI_ASSIGN_TO_REQ(sbr_reqs[i], sbr_ports[i])
    `AXI_ASSIGN_FROM_RSP(sbr_ports[i], sbr_rsps[i])
  end

  axi_xp #(
    .ATOPs                ( ATOPs               ),
    .Cfg                  ( Cfg                 ),
    .NumSbrPorts          ( NumSbrPorts         ),
    .NumMgrPorts          ( NumMgrPorts         ),
    .Connectivity         ( Connectivity        ),
    .AddrWidth            ( AddrWidth           ),
    .DataWidth            ( DataWidth           ),
    .IdWidth              ( IdWidth             ),
    .UserWidth            ( UserWidth           ),
    .SbrPortMaxUniqIds    ( SbrPortMaxUniqIds   ),
    .SbrPortMaxTxnsPerId  ( SbrPortMaxTxnsPerId ),
    .SbrPortMaxTxns       ( SbrPortMaxTxns      ),
    .MgrPortMaxUniqIds    ( MgrPortMaxUniqIds   ),
    .MgrPortMaxTxnsPerId  ( MgrPortMaxTxnsPerId ),
    .NumAddrRules         ( NumAddrRules        ),
    .axi_req_t            ( axi_req_t           ),
    .axi_rsp_t            ( axi_rsp_t           ),
    .rule_t               ( rule_t              )
  ) i_xp (
    .clk_i,
    .rst_ni,
    .test_en_i,
    .sbr_req_i (sbr_reqs),
    .sbr_rsp_o (sbr_rsps),
    .mgr_req_o (mgr_reqs),
    .mgr_rsp_i (mgr_rsps),
    .addr_map_i
  );

endmodule
