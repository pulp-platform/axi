// Copyright (c) 2014-2018 ETH Zurich, University of Bologna
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
// - Wolfgang Roenninger <wroennin@iis.ee.ethz.ch>
// - Fabian Schuiki <fschuiki@iis.ee.ethz.ch>

/// Modify addresses on an AXI4 bus
module axi_modify_address #(
  /// Request type of the subordinate port
  parameter type  sbr_port_axi_req_t = logic,
  /// Address type of the manager port
  parameter type mgr_addr_t = logic,
  /// Request type of the manager port
  parameter type  mgr_port_axi_req_t = logic,
  /// Response type of subordinate and manager port
  parameter type axi_rsp_t = logic
) (
  /// Subordinate port request
  input  sbr_port_axi_req_t  sbr_port_req_i,
  /// Subordinate port response
  output axi_rsp_t sbr_port_rsp_o,
  /// AW address on manager port; must remain stable while an AW handshake is pending.
  input  mgr_addr_t mgr_aw_addr_i,
  /// AR address on manager port; must remain stable while an AR handshake is pending.
  input  mgr_addr_t mgr_ar_addr_i,
  /// Manager port request
  output mgr_port_axi_req_t  mgr_port_req_o,
  /// Manager port response
  input  axi_rsp_t mgr_port_rsp_i
);

  assign mgr_port_req_o = '{
    aw: '{
      id:     sbr_port_req_i.aw.id,
      addr:   mgr_aw_addr_i,
      len:    sbr_port_req_i.aw.len,
      size:   sbr_port_req_i.aw.size,
      burst:  sbr_port_req_i.aw.burst,
      lock:   sbr_port_req_i.aw.lock,
      cache:  sbr_port_req_i.aw.cache,
      prot:   sbr_port_req_i.aw.prot,
      qos:    sbr_port_req_i.aw.qos,
      region: sbr_port_req_i.aw.region,
      atop:   sbr_port_req_i.aw.atop,
      user:   sbr_port_req_i.aw.user,
      default: '0
    },
    aw_valid: sbr_port_req_i.aw_valid,
    w:        sbr_port_req_i.w,
    w_valid:  sbr_port_req_i.w_valid,
    b_ready:  sbr_port_req_i.b_ready,
    ar: '{
      id:     sbr_port_req_i.ar.id,
      addr:   mgr_ar_addr_i,
      len:    sbr_port_req_i.ar.len,
      size:   sbr_port_req_i.ar.size,
      burst:  sbr_port_req_i.ar.burst,
      lock:   sbr_port_req_i.ar.lock,
      cache:  sbr_port_req_i.ar.cache,
      prot:   sbr_port_req_i.ar.prot,
      qos:    sbr_port_req_i.ar.qos,
      region: sbr_port_req_i.ar.region,
      user:   sbr_port_req_i.ar.user,
      default: '0
    },
    ar_valid: sbr_port_req_i.ar_valid,
    r_ready:  sbr_port_req_i.r_ready,
    default: '0
  };

  assign sbr_port_rsp_o = mgr_port_rsp_i;
endmodule


`include "axi/typedef.svh"
`include "axi/assign.svh"

/// Interface variant of [`axi_modify_address`](module.axi_modify_address)
module axi_modify_address_intf #(
  /// Address width of subordinate port
  parameter int unsigned AXI_SBR_PORT_ADDR_WIDTH = 0,
  /// Address width of manager port
  parameter int unsigned AXI_MGR_PORT_ADDR_WIDTH = AXI_SBR_PORT_ADDR_WIDTH,
  /// Data width of subordinate and manager port
  parameter int unsigned AXI_DATA_WIDTH = 0,
  /// ID width of subordinate and manager port
  parameter int unsigned AXI_ID_WIDTH = 0,
  /// User signal width of subordinate and manager port
  parameter int unsigned AXI_USER_WIDTH = 0,
  /// Derived (=DO NOT OVERRIDE) type of manager port addresses
  type mgr_addr_t = logic [AXI_MGR_PORT_ADDR_WIDTH-1:0]
) (
  /// Subordinate port
  AXI_BUS.Subordinate     sbr,
  /// AW address on manager port; must remain stable while an AW handshake is pending.
  input  mgr_addr_t mgr_aw_addr_i,
  /// AR address on manager port; must remain stable while an AR handshake is pending.
  input  mgr_addr_t mgr_ar_addr_i,
  /// Manager port
  AXI_BUS.Manager    mgr
);

  typedef logic [AXI_ID_WIDTH-1:0]            id_t;
  typedef logic [AXI_SBR_PORT_ADDR_WIDTH-1:0] sbr_addr_t;
  typedef logic [AXI_DATA_WIDTH-1:0]          data_t;
  typedef logic [AXI_DATA_WIDTH/8-1:0]        strb_t;
  typedef logic [AXI_USER_WIDTH-1:0]          user_t;

  `AXI_TYPEDEF_AW_CHAN_T(sbr_aw_chan_t, sbr_addr_t, id_t, user_t)
  `AXI_TYPEDEF_AW_CHAN_T(mgr_aw_chan_t, mgr_addr_t, id_t, user_t)
  `AXI_TYPEDEF_W_CHAN_T(w_chan_t, data_t, strb_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T(b_chan_t, id_t, user_t)
  `AXI_TYPEDEF_AR_CHAN_T(sbr_ar_chan_t, sbr_addr_t, id_t, user_t)
  `AXI_TYPEDEF_AR_CHAN_T(mgr_ar_chan_t, mgr_addr_t, id_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(r_chan_t, data_t, id_t, user_t)
  `AXI_TYPEDEF_REQ_T(sbr_port_axi_req_t, sbr_aw_chan_t, w_chan_t, sbr_ar_chan_t)
  `AXI_TYPEDEF_REQ_T(mgr_port_axi_req_t, mgr_aw_chan_t, w_chan_t, mgr_ar_chan_t)
  `AXI_TYPEDEF_RSP_T(axi_rsp_t, b_chan_t, r_chan_t)

  sbr_port_axi_req_t  sbr_req;
  mgr_port_axi_req_t  mgr_req;
  axi_rsp_t           sbr_rsp, mgr_rsp;

  `AXI_ASSIGN_TO_REQ(sbr_req, sbr)
  `AXI_ASSIGN_FROM_RSP(sbr, sbr_rsp)

  `AXI_ASSIGN_FROM_REQ(mgr, mgr_req)
  `AXI_ASSIGN_TO_RSP(mgr_rsp, mgr)

  axi_modify_address #(
    .sbr_port_axi_req_t ( sbr_port_axi_req_t ),
    .mgr_addr_t         ( mgr_addr_t         ),
    .mgr_port_axi_req_t ( mgr_port_axi_req_t ),
    .axi_rsp_t          ( axi_rsp_t          )
  ) i_axi_modify_address (
    .sbr_port_req_i    ( sbr_req ),
    .sbr_port_rsp_o    ( sbr_rsp ),
    .mgr_port_req_o    ( mgr_req ),
    .mgr_port_rsp_i    ( mgr_rsp ),
    .mgr_aw_addr_i,
    .mgr_ar_addr_i
  );

// pragma translate_off
`ifndef VERILATOR
  initial begin
    assert(AXI_SBR_PORT_ADDR_WIDTH > 0);
    assert(AXI_MGR_PORT_ADDR_WIDTH > 0);
    assert(AXI_DATA_WIDTH > 0);
    assert(AXI_ID_WIDTH > 0);
  end
`endif
// pragma translate_on
endmodule
