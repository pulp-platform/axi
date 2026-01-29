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
module axi_xbar_unmuxed
import cc_pkg::idx_width;
#(
  /// Configuration struct for the crossbar see `axi_pkg` for fields and definitions.
  parameter axi_pkg::xbar_cfg_t Cfg                                   = '0,
  /// Enable atomic operations support.
  parameter bit  ATOPs                                                = 1'b1,
  /// Connectivity matrix
  parameter bit [Cfg.NoSlvPorts-1:0][Cfg.NoMstPorts-1:0] Connectivity = '1,
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
  parameter type rule_t                                               = axi_pkg::xbar_rule_64_t,
  localparam int unsigned MstPortsIdxWidth =
      (Cfg.NoMstPorts == 32'd1) ? 32'd1 : unsigned'($clog2(Cfg.NoMstPorts))
) (
  /// Clock, positive edge triggered.
  input  logic                                                          clk_i,
  /// Asynchronous reset, active low.
  input  logic                                                          rst_ni,
  /// AXI4+ATOP requests to the slave ports.
  input  req_t  [Cfg.NoSlvPorts-1:0]                                    slv_ports_req_i,
  /// AXI4+ATOP responses of the slave ports.
  output resp_t [Cfg.NoSlvPorts-1:0]                                    slv_ports_resp_o,
  /// AXI4+ATOP requests of the master ports.
  output req_t  [Cfg.NoMstPorts-1:0][Cfg.NoSlvPorts-1:0]                mst_ports_req_o,
  /// AXI4+ATOP responses to the master ports.
  input  resp_t [Cfg.NoMstPorts-1:0][Cfg.NoSlvPorts-1:0]                mst_ports_resp_i,
  /// Address map array input for the crossbar. This map is global for the whole module.
  /// It is used for routing the transactions to the respective master ports.
  /// Each master port can have multiple different rules.
  input  rule_t [Cfg.NoAddrRules-1:0]                                   addr_map_i,
  /// Enable default master port.
  input  logic  [Cfg.NoSlvPorts-1:0]                                    en_default_mst_port_i,
  /// Enables a default master port for each slave port. When this is enabled unmapped
  /// transactions get issued at the master port given by `default_mst_port_i`.
  /// When not used, tie to `'0`.
  input  logic  [Cfg.NoSlvPorts-1:0][MstPortsIdxWidth-1:0]              default_mst_port_i
);

  rule_t [Cfg.NoSlvPorts-1:0] default_rules;
  for (genvar i = 0; i < Cfg.NoSlvPorts; i++) begin : gen_default_rules
    assign default_rules[i] = '{
      idx:        default_mst_port_i[i],
      start_addr: '0,
      end_addr:   '0
    };
  end

  axi_mcast_xbar_unmuxed #(
    .Cfg                  (Cfg),
    .ATOPs                (ATOPs),
    .Connectivity         (Connectivity),
    .aw_chan_t            (aw_chan_t),
    .w_chan_t             (w_chan_t),
    .b_chan_t             (b_chan_t),
    .ar_chan_t            (ar_chan_t),
    .r_chan_t             (r_chan_t),
    .req_t                (req_t),
    .resp_t               (resp_t),
    .rule_t               (rule_t)
  ) i_axi_mcast_xbar_unmuxed (
    .clk_i                (clk_i),
    .rst_ni               (rst_ni),
    .test_i               (test_i),
    .slv_ports_req_i      (slv_ports_req_i),
    .slv_ports_resp_o     (slv_ports_resp_o),
    .mst_ports_req_o      (mst_ports_req_o),
    .mst_ports_resp_i     (mst_ports_resp_i),
    .addr_map_i           (addr_map_i),
    .en_default_mst_port_i(en_default_mst_port_i),
    .default_mst_port_i   (default_rules)
  );

endmodule
