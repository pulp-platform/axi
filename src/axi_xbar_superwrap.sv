// Copyright (c) 2024 ETH Zurich and University of Bologna.
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
// - Nils Wistoff <nwistoff@iis.ee.ethz.ch>

module axi_xbar_superwrap
import cf_math_pkg::idx_width;
import autocc_axi_xbar_pkg::*;
#(
  parameter ASSERT_INPUTS = 0
) (
  /// Clock, positive edge triggered.
  input logic                                                     clk_i,
  /// Asynchronous reset, active low.  
  input logic                                                     rst_ni,
  /// Testmode enable, active high.
  input logic                                                     test_i,
  /// AXI4+ATOP requests to the slave ports.  
  input                                                           slv_req_t [Cfg.NoSlvPorts-1:0] slv_ports_req_i_2,
  input                                                           slv_req_t [Cfg.NoSlvPorts-1:0] slv_ports_req_i,
  /// AXI4+ATOP responses of the slave ports.  
  output                                                          slv_resp_t [Cfg.NoSlvPorts-1:0] slv_ports_resp_o_2,
  output                                                          slv_resp_t [Cfg.NoSlvPorts-1:0] slv_ports_resp_o,
  /// AXI4+ATOP requests of the master ports.  
  output                                                          mst_req_t [Cfg.NoMstPorts-1:0] mst_ports_req_o_2,
  output                                                          mst_req_t [Cfg.NoMstPorts-1:0] mst_ports_req_o,
  /// AXI4+ATOP responses to the master ports.  
  input                                                           mst_resp_t [Cfg.NoMstPorts-1:0] mst_ports_resp_i_2,
  input                                                           mst_resp_t [Cfg.NoMstPorts-1:0] mst_ports_resp_i,
  /// Address map array input for the crossbar. This map is global for the whole module.
  /// It is used for routing the transactions to the respective master ports.
  /// Each master port can have multiple different rules.
  input                                                           rule_t [Cfg.NoAddrRules-1:0] addr_map_i,
  /// Enable default master port.
  input logic [Cfg.NoSlvPorts-1:0]                                en_default_mst_port_i,
`ifdef VCS
  /// Enables a default master port for each slave port. When this is enabled unmapped
  /// transactions get issued at the master port given by `default_mst_port_i`.
  /// When not used, tie to `'0`.  
  input logic [Cfg.NoSlvPorts-1:0][MstPortsIdxWidth-1:0]          default_mst_port_i
`else
  /// Enables a default master port for each slave port. When this is enabled unmapped
  /// transactions get issued at the master port given by `default_mst_port_i`.
  /// When not used, tie to `'0`.  
  input logic [Cfg.NoSlvPorts-1:0][idx_width(Cfg.NoMstPorts)-1:0] default_mst_port_i
`endif
  );


  // =========
  // Testbench
  // =========

  axi_xbar_wrap #(
    .Cfg(Cfg),
    .ATOPs(ATOPs),
    .Connectivity(Connectivity),
    .slv_aw_chan_t(slv_aw_chan_t),
    .mst_aw_chan_t(mst_aw_chan_t),
    .w_chan_t(slv_w_chan_t),
    .slv_b_chan_t(slv_b_chan_t),
    .mst_b_chan_t(mst_b_chan_t),
    .slv_ar_chan_t(slv_ar_chan_t),
    .mst_ar_chan_t(mst_ar_chan_t),
    .slv_r_chan_t(slv_r_chan_t),
    .mst_r_chan_t(mst_r_chan_t),
    .slv_req_t(slv_req_t),
    .slv_resp_t(slv_resp_t),
    .mst_req_t(mst_req_t),
    .mst_resp_t(mst_resp_t),
    .rule_t(rule_t)
  ) i_axi_xbar_wrap (
    .clk_i(clk_i),
    .rst_ni(rst_ni),
    .test_i(test_i),
    .slv_ports_req_i_2(slv_ports_req_i_2),
    .slv_ports_req_i(slv_ports_req_i),
    .slv_ports_resp_o_2(slv_ports_resp_o_2),
    .slv_ports_resp_o(slv_ports_resp_o),
    .mst_ports_req_o_2(mst_ports_req_o_2),
    .mst_ports_req_o(mst_ports_req_o),
    .mst_ports_resp_i_2(mst_ports_resp_i_2),
    .mst_ports_resp_i(mst_ports_resp_i),
    .addr_map_i(addr_map_i),
    .en_default_mst_port_i(en_default_mst_port_i),
    .default_mst_port_i(default_mst_port_i)
);

endmodule
