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
// - Andreas Kurth <akurth@iis.ee.ethz.ch>
// - Vikram Jain <jvikram@iis.ee.ethz.ch>

`include "axi/typedef.svh"

/// AXI Crosspoint (XP) with homomorphous slave and master ports.
module axi_xp #(
  // Atomic operations settings
  parameter bit  ATOPs = 1'b1,
  /// Number of slave ports.
  parameter int unsigned NumSlvPorts = 32'd0,
  /// Number of master ports.
  parameter int unsigned NumMstPorts = 32'd0,
  /// Connectivity from a slave port to the master ports.  A `1'b1` in `Connectivity[i][j]` means
  /// that slave port `i` is connected to master port `j`.  By default, all slave ports are
  /// connected to all master ports.
  parameter bit [NumSlvPorts-1:0][NumMstPorts-1:0] Connectivity = '1,
  /// Address width of all ports.
  parameter int unsigned AxiAddrWidth = 32'd0,
  /// Data width of all ports.
  parameter int unsigned AxiDataWidth = 32'd0,
  /// ID width of all ports.
  parameter int unsigned AxiIdWidth = 32'd0,
  /// User signal width of all ports.
  parameter int unsigned AxiUserWidth = 32'd0,
  /// Maximum number of different IDs that can be in flight at each slave port.  Reads and writes
  /// are counted separately (except for ATOPs, which count as both read and write).
  ///
  /// It is legal for upstream to have transactions with more unique IDs than the maximum given by
  /// this parameter in flight, but a transaction exceeding the maximum will be stalled until all
  /// transactions of another ID complete.
  parameter int unsigned AxiSlvPortMaxUniqIds = 32'd0,
  /// Maximum number of in-flight transactions with the same ID at the slave port.
  ///
  /// This parameter is only relevant if `AxiSlvPortMaxUniqIds <= 2**AxiMstPortIdWidth`.  In that
  /// case, this parameter is passed to [`axi_id_remap` as `AxiMaxTxnsPerId`
  /// parameter](module.axi_id_remap#parameter.AxiMaxTxnsPerId).
  parameter int unsigned AxiSlvPortMaxTxnsPerId = 32'd0,
  /// Maximum number of in-flight transactions at the slave port.  Reads and writes are counted
  /// separately (except for ATOPs, which count as both read and write).
  ///
  /// This parameter is only relevant if `AxiSlvPortMaxUniqIds > 2**AxiMstPortIdWidth`.  In that
  /// case, this parameter is passed to
  /// [`axi_id_serialize`](module.axi_id_serialize#parameter.AxiSlvPortMaxTxns).
  parameter int unsigned AxiSlvPortMaxTxns = 32'd0,
  /// Maximum number of different IDs that can be in flight at the master port.  Reads and writes
  /// are counted separately (except for ATOPs, which count as both read and write).
  ///
  /// This parameter is only relevant if `AxiSlvPortMaxUniqIds > 2**AxiMstPortIdWidth`.  In that
  /// case, this parameter is passed to
  /// [`axi_id_serialize`](module.axi_id_serialize#parameter.AxiMstPortMaxUniqIds).
  parameter int unsigned AxiMstPortMaxUniqIds = 32'd0,
  /// Maximum number of in-flight transactions with the same ID at the master port.
  ///
  /// This parameter is only relevant if `AxiSlvPortMaxUniqIds > 2**AxiMstPortIdWidth`.  In that
  /// case, this parameter is passed to
  /// [`axi_id_serialize`](module.axi_id_serialize#parameter.AxiMstPortMaxTxnsPerId).
  parameter int unsigned AxiMstPortMaxTxnsPerId = 32'd0,
  /// Number of rules in the address map.
  parameter int unsigned NumAddrRules = 32'd0,
  /// Request struct type of the AXI4+ATOP slave port
  parameter type slv_req_t = logic,
  /// Response struct type of the AXI4+ATOP slave port
  parameter type slv_resp_t = logic,
  /// Request struct type of the AXI4+ATOP master port
  parameter type mst_req_t = logic,
  /// Response struct type of the AXI4+ATOP master port
  parameter type mst_resp_t = logic,
  /// Rule type (see documentation of `axi_xbar` for details).
  parameter type rule_t = axi_pkg::xbar_rule_64_t
) (
  /// Rising-edge clock of all ports
  input  logic                          clk_i,
  /// Asynchronous reset, active low
  input  logic                          rst_ni,
  /// Test mode enable
  input  logic                          test_en_i,
  /// Slave ports request
  input  slv_req_t  [NumSlvPorts-1:0]   slv_req_i,
  /// Slave ports response
  output slv_resp_t [NumSlvPorts-1:0]   slv_resp_o,
  /// Master ports request
  output mst_req_t  [NumMstPorts-1:0]   mst_req_o,
  /// Master ports response
  input  mst_resp_t [NumMstPorts-1:0]   mst_resp_i,
  /// Address map for transferring transactions from slave to master ports
  input  rule_t     [NumAddrRules-1:0]  addr_map_i
);

  parameter int unsigned AxiXbarIdWidth = AxiIdWidth + $clog2(NumSlvPorts);
  typedef logic [AxiAddrWidth-1:0]    addr_t;
  typedef logic [AxiDataWidth-1:0]    data_t;
  typedef logic [AxiIdWidth-1:0]      id_t;
  typedef logic [AxiXbarIdWidth-1:0]  xbar_id_t;
  typedef logic [AxiDataWidth/8-1:0]  strb_t;
  typedef logic [AxiUserWidth-1:0]    user_t;

  `AXI_TYPEDEF_AW_CHAN_T(aw_t, addr_t, id_t, user_t)
  `AXI_TYPEDEF_AW_CHAN_T(xbar_aw_t, addr_t, xbar_id_t, user_t)
  `AXI_TYPEDEF_W_CHAN_T(w_t, data_t, strb_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T(b_t, id_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T(xbar_b_t, xbar_id_t, user_t)
  `AXI_TYPEDEF_AR_CHAN_T(ar_t, addr_t, id_t, user_t)
  `AXI_TYPEDEF_AR_CHAN_T(xbar_ar_t, addr_t, xbar_id_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(r_t, data_t, id_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(xbar_r_t, data_t, xbar_id_t, user_t)
  `AXI_TYPEDEF_REQ_T(req_t, aw_t, w_t, ar_t)
  `AXI_TYPEDEF_REQ_T(xbar_req_t, xbar_aw_t, w_t, xbar_ar_t)
  `AXI_TYPEDEF_RESP_T(resp_t, b_t, r_t)
  `AXI_TYPEDEF_RESP_T(xbar_resp_t, xbar_b_t, xbar_r_t)

  xbar_req_t  [NumMstPorts-1:0] xbar_req;
  xbar_resp_t [NumMstPorts-1:0] xbar_resp;

  localparam axi_pkg::xbar_cfg_t xbar_cfg = '{
    NoSlvPorts:         NumSlvPorts,
    NoMstPorts:         NumMstPorts,
    MaxMstTrans:        AxiMaxTxnsPerId,
    MaxSlvTrans:        AxiSlvPortMaxWriteTxns,
    FallThrough:        1'b0,
    LatencyMode:        axi_pkg::CUT_ALL_PORTS,
    AxiIdWidthSlvPorts: AxiIdWidth,
    AxiIdUsedSlvPorts:  AxiIdWidth,
    AxiAddrWidth:       AxiAddrWidth,
    AxiDataWidth:       AxiDataWidth,
    NoAddrRules:        NumAddrRules
  };

  axi_xbar #(
    .Cfg            ( xbar_cfg      ),
    .ATOPs          ( ATOPs         ),
    .Connectivity   ( Connectivity  ),
    .slv_aw_chan_t  ( aw_t          ),
    .mst_aw_chan_t  ( xbar_aw_t     ),
    .w_chan_t       ( w_t           ),
    .slv_b_chan_t   ( b_t           ),
    .mst_b_chan_t   ( xbar_b_t      ),
    .slv_ar_chan_t  ( ar_t          ),
    .mst_ar_chan_t  ( xbar_ar_t     ),
    .slv_r_chan_t   ( r_t           ),
    .mst_r_chan_t   ( xbar_r_t      ),
    .slv_req_t      ( req_t         ),
    .slv_resp_t     ( resp_t        ),
    .mst_req_t      ( xbar_req_t    ),
    .mst_resp_t     ( xbar_resp_t   ),
    .rule_t         ( rule_t        )
  ) i_xbar (
    .clk_i,
    .rst_ni,
    .test_i                 ( test_en_i                               ),
    .slv_ports_req_i        ( slv_req_i                               ),
    .slv_ports_resp_o       ( slv_resp_o                              ),
    .mst_ports_req_o        ( xbar_req                                ),
    .mst_ports_resp_i       ( xbar_resp                               ),
    .addr_map_i,
    .en_default_mst_port_i  ( {NumSlvPorts{1'b0}}                     ),
    .default_mst_port_i     ( {NumSlvPorts{{$clog2(NumMstPorts){1'b0}}}} )
  );

  for (genvar i = 0; i < NumMstPorts; i++) begin : gen_remap
    axi_id_remap #(
      .AxiSlvPortIdWidth    ( AxiXbarIdWidth        ),
      .AxiSlvPortMaxUniqIds ( AxiSlvPortMaxUniqIds  ),
      .AxiMaxTxnsPerId      ( AxiMaxTxnsPerId       ),
      .AxiMstPortIdWidth    ( AxiIdWidth            ),
      .slv_req_t            ( xbar_req_t            ),
      .slv_resp_t           ( xbar_resp_t           ),
      .mst_req_t            ( req_t                 ),
      .mst_resp_t           ( resp_t                )
    ) i_axi_id_remap (
      .clk_i,
      .rst_ni,
      .slv_req_i  ( xbar_req[i]   ),
      .slv_resp_o ( xbar_resp[i]  ),
      .mst_req_o  ( mst_req_o[i]  ),
      .mst_resp_i ( mst_resp_i[i] )
    );
  end

endmodule
