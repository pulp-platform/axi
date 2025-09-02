// Copyright (c) 2025 ETH Zurich and University of Bologna.
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

`include "common_cells/registers.svh"

/// axi_xbar_clearable: An AXI crossbar that can be cleared gracefully.
module axi_xbar_clearable
import cf_math_pkg::idx_width;
#(
  /// Configuration struct for the crossbar see `axi_pkg` for fields and definitions.
  parameter axi_pkg::xbar_cfg_t Cfg                                   = '0,
  /// Enable atomic operations support.
  parameter bit  ATOPs                                                = 1'b1,
  /// Connectivity matrix
  parameter bit [Cfg.NoSlvPorts-1:0][Cfg.NoMstPorts-1:0] Connectivity = '1,
  /// AXI4+ATOP AW channel struct type for the slave ports.
  parameter type slv_aw_chan_t                                        = logic,
  /// AXI4+ATOP AW channel struct type for the master ports.
  parameter type mst_aw_chan_t                                        = logic,
  /// AXI4+ATOP W channel struct type for all ports.
  parameter type w_chan_t                                             = logic,
  /// AXI4+ATOP B channel struct type for the slave ports.
  parameter type slv_b_chan_t                                         = logic,
  /// AXI4+ATOP B channel struct type for the master ports.
  parameter type mst_b_chan_t                                         = logic,
  /// AXI4+ATOP AR channel struct type for the slave ports.  
  parameter type slv_ar_chan_t                                        = logic,
  /// AXI4+ATOP AR channel struct type for the master ports.
  parameter type mst_ar_chan_t                                        = logic,
  /// AXI4+ATOP R channel struct type for the slave ports.  
  parameter type slv_r_chan_t                                         = logic,
  /// AXI4+ATOP R channel struct type for the master ports.
  parameter type mst_r_chan_t                                         = logic,
  /// AXI4+ATOP request struct type for the slave ports.
  parameter type slv_req_t                                            = logic,
  /// AXI4+ATOP response struct type for the slave ports.
  parameter type slv_resp_t                                           = logic,
  /// AXI4+ATOP request struct type for the master ports.
  parameter type mst_req_t                                            = logic,
  /// AXI4+ATOP response struct type for the master ports
  parameter type mst_resp_t                                           = logic,
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
  parameter type rule_t                                               = axi_pkg::xbar_rule_64_t,
`ifdef VCS
  localparam int unsigned MstPortsIdxWidth =
      (Cfg.NoMstPorts == 32'd1) ? 32'd1 : unsigned'($clog2(Cfg.NoMstPorts))
`endif
  parameter int unsigned NumPending = 32'd16
) (
  /// Clock, positive edge triggered.
  input  logic                                                          clk_i,
  /// Asynchronous reset, active low.  
  input  logic                                                          rst_ni,
  /// Testmode enable, active high.
  input  logic                                                          test_i,
  /// Clear gracefully
  input  logic                                                          clr_i,
  output logic                                                          clr_ack_o,
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
  input  slv_req_t  [Cfg.NoSlvPorts-1:0]                                slv_ports_req_i,
  /// AXI4+ATOP responses of the slave ports.  
  output slv_resp_t [Cfg.NoSlvPorts-1:0]                                slv_ports_resp_o,
  /*AUTOSVA
  mst_port_r_req_0: mst_port_r_req_0 --OUT> mst_port_r_resp_0
  mst_port_r_req_0_val = mst_ports_req_o[0].ar_valid
  mst_port_r_req_0_rdy = mst_ports_resp_i[0].ar_ready
  [1:0] mst_port_r_req_0_transid = mst_ports_req_o[0].ar.id
  mst_port_r_resp_0_val = mst_ports_resp_i[0].r_valid
  mst_port_r_resp_0_rdy = mst_ports_req_o[0].r_ready
  [1:0] mst_port_r_resp_0_transid = mst_ports_resp_i[0].r.id
  mst_port_r_req_1: mst_port_r_req_1 --OUT> mst_port_r_resp_1
  mst_port_r_req_1_val = mst_ports_req_o[1].ar_valid
  mst_port_r_req_1_rdy = mst_ports_resp_i[1].ar_ready
  [1:0] mst_port_r_req_1_transid = mst_ports_req_o[1].ar.id
  mst_port_r_resp_1_val = mst_ports_resp_i[1].r_valid
  mst_port_r_resp_1_rdy = mst_ports_req_o[1].r_ready
  [1:0] mst_port_r_resp_1_transid = mst_ports_resp_i[1].r.id
  mst_port_w_req_0: mst_port_w_req_0 --OUT> mst_port_w_resp_0
  mst_port_w_req_0_val = mst_ports_req_o[0].aw_valid
  mst_port_w_req_0_rdy = mst_ports_resp_i[0].aw_ready
  [1:0] mst_port_w_req_0_transid = mst_ports_req_o[0].aw.id
  mst_port_w_resp_0_val = mst_ports_resp_i[0].b_valid
  mst_port_w_resp_0_rdy = mst_ports_req_o[0].b_ready
  [1:0] mst_port_w_resp_0_transid = mst_ports_resp_i[0].b.id
  mst_port_w_req_1: mst_port_w_req_1 --OUT> mst_port_w_resp_1
  mst_port_w_req_1_val = mst_ports_req_o[1].aw_valid
  mst_port_w_req_1_rdy = mst_ports_resp_i[1].aw_ready
  [1:0] mst_port_w_req_1_transid = mst_ports_req_o[1].aw.id
  mst_port_w_resp_1_val = mst_ports_resp_i[1].b_valid
  mst_port_w_resp_1_rdy = mst_ports_req_o[1].b_ready
  [1:0] mst_port_w_resp_1_transid = mst_ports_resp_i[1].b.id
  */
  /// AXI4+ATOP requests of the master ports.  
  output mst_req_t  [Cfg.NoMstPorts-1:0]                                mst_ports_req_o,
  /// AXI4+ATOP responses to the master ports.  
  input  mst_resp_t [Cfg.NoMstPorts-1:0]                                mst_ports_resp_i,
  /// Address map array input for the crossbar. This map is global for the whole module.
  /// It is used for routing the transactions to the respective master ports.
  /// Each master port can have multiple different rules.
  input  rule_t     [Cfg.NoAddrRules-1:0]                               addr_map_i,
  /// Enable default master port.
  input  logic      [Cfg.NoSlvPorts-1:0]                                en_default_mst_port_i,
`ifdef VCS
  /// Enables a default master port for each slave port. When this is enabled unmapped
  /// transactions get issued at the master port given by `default_mst_port_i`.
  /// When not used, tie to `'0`.  
  input  logic      [Cfg.NoSlvPorts-1:0][MstPortsIdxWidth-1:0]          default_mst_port_i
`else
  /// Enables a default master port for each slave port. When this is enabled unmapped
  /// transactions get issued at the master port given by `default_mst_port_i`.
  /// When not used, tie to `'0`.  
  input  logic      [Cfg.NoSlvPorts-1:0][idx_width(Cfg.NoMstPorts)-1:0] default_mst_port_i
`endif
);

  logic                      isolate;
  logic [Cfg.NoSlvPorts-1:0] isolated;
  logic                      isolating_d, isolating_q;

  assign isolate = clr_i | isolating_q;
  assign clr_ack_o = &isolated;
  assign isolating_d = isolate & !clr_ack_o;

  `FF(isolating_q, isolating_d, 1'b0, clk_i, rst_ni)

  slv_req_t  [Cfg.NoSlvPorts-1:0] slv_reqs_isolated;
  slv_resp_t [Cfg.NoSlvPorts-1:0] slv_resps_isolated;

  for (genvar i = 0; i < Cfg.NoSlvPorts; i++) begin : gen_slv_port_isolate
    axi_isolate #(
      .NumPending (NumPending),
      .TerminateTransaction (1'b0),
      .AtopSupport (ATOPs),
      .AxiAddrWidth (Cfg.AxiAddrWidth),
      .AxiDataWidth (Cfg.AxiDataWidth),
      .AxiIdWidth (Cfg.AxiIdWidthSlvPorts),
      .AxiUserWidth (32'd1),
      .axi_req_t (slv_req_t),
      .axi_resp_t (slv_resp_t)
    ) i_axi_isolate (
      .clk_i (clk_i),
      .rst_ni (rst_ni),
      .slv_req_i (slv_ports_req_i[i]),
      .slv_resp_o (slv_ports_resp_o[i]),
      .mst_req_o (slv_reqs_isolated[i]),
      .mst_resp_i (slv_resps_isolated[i]),
      .isolate_i (isolate),
      .isolated_o (isolated[i])
    );
  end

  axi_xbar #(
    .Cfg  (Cfg),
    .ATOPs          ( ATOPs         ),
    .Connectivity   ( Connectivity  ),
    .slv_aw_chan_t  ( slv_aw_chan_t ),
    .mst_aw_chan_t  ( mst_aw_chan_t ),
    .w_chan_t       ( w_chan_t      ),
    .slv_b_chan_t   ( slv_b_chan_t  ),
    .mst_b_chan_t   ( mst_b_chan_t  ),
    .slv_ar_chan_t  ( slv_ar_chan_t ),
    .mst_ar_chan_t  ( mst_ar_chan_t ),
    .slv_r_chan_t   ( slv_r_chan_t  ),
    .mst_r_chan_t   ( mst_r_chan_t  ),
    .slv_req_t      ( slv_req_t     ),
    .slv_resp_t     ( slv_resp_t    ),
    .mst_req_t      ( mst_req_t     ),
    .mst_resp_t     ( mst_resp_t    ),
    .rule_t         ( rule_t        )
  ) i_xbar (
    .clk_i,
    .rst_ni (rst_ni & !clr_ack_o),
    .test_i,
    .slv_ports_req_i  (slv_reqs_isolated ),
    .slv_ports_resp_o (slv_resps_isolated ),
    .mst_ports_req_o,
    .mst_ports_resp_i,
    .addr_map_i,
    .en_default_mst_port_i,
    .default_mst_port_i
  );

endmodule
