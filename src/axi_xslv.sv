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

module axi_xslv
import cf_math_pkg::idx_width;
#(
  parameter                                              axi_pkg::xbar_cfg_t Cfg = '0,
  parameter bit                                          ATOPs = 1'b1,
  parameter bit [Cfg.NoSlvPorts-1:0][Cfg.NoMstPorts-1:0] Connectivity = '1,
  parameter type                                         slv_aw_chan_t = logic,
  parameter type                                         mst_aw_chan_t = logic,
  parameter type                                         w_chan_t = logic,
  parameter type                                         slv_b_chan_t = logic,
  parameter type                                         mst_b_chan_t = logic,
  parameter type                                         slv_ar_chan_t = logic,
  parameter type                                         mst_ar_chan_t = logic,
  parameter type                                         slv_r_chan_t = logic,
  parameter type                                         mst_r_chan_t = logic,
  parameter type                                         slv_req_t = logic,
  parameter type                                         slv_resp_t = logic,
  parameter type                                         mst_req_t = logic,
  parameter type                                         mst_resp_t = logic,
  parameter type                                         rule_t = axi_pkg::xbar_rule_64_t
) (
  /// Clock, positive edge triggered.
  input logic                                                     clk_i,
  /// Asynchronous reset, active low.  
  input logic                                                     rst_ni,
  /// Testmode enable, active high.
  input logic                                                     test_i,
  /*AUTOSVA
  slv_port_r_req_0: slv_port_r_req_0 --IN> slv_port_r_resp_0
  slv_port_r_req_0_val = slv_ports_req_i[0].ar_valid
  slv_port_r_req_0_rdy = slv_ports_resp_o[0].ar_ready
  slv_port_r_req_0_transid = slv_ports_req_i[0].ar.id
  slv_port_r_resp_0_val = slv_ports_resp_o[0].r_valid
  slv_port_r_resp_0_rdy = slv_ports_req_i[0].r_ready
  slv_port_r_resp_0_transid = slv_ports_resp_o[0].r.id
  slv_port_r_req_1: slv_port_r_req_1 --IN> slv_port_r_resp_1
  slv_port_r_req_1_val = slv_ports_req_i[1].ar_valid
  slv_port_r_req_1_rdy = slv_ports_resp_o[1].ar_ready
  slv_port_r_req_1_transid = slv_ports_req_i[1].ar.id
  slv_port_r_resp_1_val = slv_ports_resp_o[1].r_valid
  slv_port_r_resp_1_rdy = slv_ports_req_i[1].r_ready
  slv_port_r_resp_1_transid = slv_ports_resp_o[1].r.id
  slv_port_w_req_0: slv_port_w_req_0 --IN> slv_port_w_resp_0
  slv_port_w_req_0_val = slv_ports_req_i[0].aw_valid
  slv_port_w_req_0_rdy = slv_ports_resp_o[0].aw_ready
  slv_port_w_req_0_transid = slv_ports_req_i[0].aw.id
  slv_port_w_resp_0_val = slv_ports_resp_o[0].b_valid
  slv_port_w_resp_0_rdy = slv_ports_req_i[0].b_ready
  slv_port_w_resp_0_transid = slv_ports_resp_o[0].b.id
  slv_port_w_req_1: slv_port_w_req_1 --IN> slv_port_w_resp_1
  slv_port_w_req_1_val = slv_ports_req_i[1].aw_valid
  slv_port_w_req_1_rdy = slv_ports_resp_o[1].aw_ready
  slv_port_w_req_1_transid = slv_ports_req_i[1].aw.id
  slv_port_w_resp_1_val = slv_ports_resp_o[1].b_valid
  slv_port_w_resp_1_rdy = slv_ports_req_i[1].b_ready
  slv_port_w_resp_1_transid = slv_ports_resp_o[1].b.id
  */
  /// AXI4+ATOP requests to the slave ports.  
  input                                                           slv_req_t [Cfg.NoSlvPorts-1:0] slv_ports_req_i,
  /// AXI4+ATOP responses of the slave ports.  
  output                                                          slv_resp_t [Cfg.NoSlvPorts-1:0] slv_ports_resp_o,
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

  mst_req_t [Cfg.NoMstPorts-1:0] mst_ports_req;
  mst_resp_t [Cfg.NoMstPorts-1:0] mst_ports_resp;

  axi_xbar #(
    .Cfg(Cfg),
    .ATOPs(ATOPs),
    .Connectivity(Connectivity),
    .slv_aw_chan_t(slv_aw_chan_t),
    .mst_aw_chan_t(mst_aw_chan_t),
    .w_chan_t(w_chan_t),
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
  ) i_axi_xbar (
    .clk_i(clk_i),
    .rst_ni(rst_ni),
    .test_i(test_i),
    .slv_ports_req_i(slv_ports_req_i),
    .slv_ports_resp_o(slv_ports_resp_o),
    .mst_ports_req_o(mst_ports_req),
    .mst_ports_resp_i(mst_ports_resp),
    .addr_map_i(addr_map_i),
    .en_default_mst_port_i(en_default_mst_port_i),
    .default_mst_port_i(default_mst_port_i)
  );

  for (genvar i = 0; i < Cfg.NoSlvPorts; i++) begin : gen_zero_mems
    axi_zero_mem #(
      .axi_req_t(mst_req_t),
      .axi_resp_t(mst_resp_t),
      .AddrWidth($bits(mst_ports_req[0].ar.addr)),
      .DataWidth($bits(mst_ports_req[0].w.data)),
      .IdWidth($bits(mst_ports_req[0].ar.id)),
      .NumBanks(1),
      .BufDepth(1)
    ) i_axi_zero_mem (
      .clk_i,
      .rst_ni,
      .busy_o(),
      .axi_req_i(mst_ports_req[i]),
      .axi_resp_o(mst_ports_resp[i])
    );
  end

endmodule
