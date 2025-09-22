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
// - Michael Rogenmoser <michaero@iis.ee.ethz.ch>
// - Thomas Benz <tbenz@iis.ee.ethz.ch>
// - Andreas Kurth <akurth@iis.ee.ethz.ch>

`include "common_cells/assertions.svh"
`include "common_cells/registers.svh"
`include "axi/assign.svh"

`ifdef QUESTA
// Derive `TARGET_VSIM`, which is used for tool-specific workarounds in this file, from `QUESTA`,
// which is automatically set in Questa.
`define TARGET_VSIM
`endif

/// Demultiplex one AXI4+ATOP slave port to multiple AXI4+ATOP master ports.
///
/// The AW and AR slave channels each have a `select` input to determine to which master port the
/// current request is sent.  The `select` can, for example, be driven by an address decoding module
/// to map address ranges to different AXI slaves.
///
/// ## Design overview
///
/// ![Block diagram](module.axi_demux.png "Block diagram")
///
/// Beats on the W channel are routed by demultiplexer according to the selection for the
/// corresponding AW beat.  This relies on the AXI property that W bursts must be sent in the same
/// order as AW beats and beats from different W bursts may not be interleaved.
///
/// Beats on the B and R channel are multiplexed from the master ports to the slave port with
/// a round-robin arbitration tree.
module axi_demux_simple #(
  parameter int unsigned AxiIdWidth     = 32'd0,
  parameter bit          AtopSupport    = 1'b1,
  parameter type         axi_req_t      = logic,
  parameter type         axi_resp_t     = logic,
  parameter int unsigned NoMstPorts     = 32'd0,
  parameter int unsigned MaxTrans       = 32'd8,
  parameter int unsigned AxiLookBits    = 32'd3,
  parameter bit          UniqueIds      = 1'b0,
  // Dependent parameters, DO NOT OVERRIDE!
  parameter int unsigned SelectWidth    = (NoMstPorts > 32'd1) ? $clog2(NoMstPorts) : 32'd1,
  parameter type         select_t       = logic [SelectWidth-1:0]
) (
  input  logic                          clk_i,
  input  logic                          rst_ni,
  input  logic                          test_i,
  // Slave Port
  input  axi_req_t                      slv_req_i,
  input  select_t                       slv_aw_select_i,
  input  select_t                       slv_ar_select_i,
  output axi_resp_t                     slv_resp_o,
  // Master Ports
  output axi_req_t    [NoMstPorts-1:0]  mst_reqs_o,
  input  axi_resp_t   [NoMstPorts-1:0]  mst_resps_i
);

  logic [NoMstPorts-1:0] aw_select_mask;

  assign aw_select_mask = 1'b1 << slv_aw_select_i;

  axi_mcast_demux_simple #(
    .AxiIdWidth           (AxiIdWidth),
    .AtopSupport          (AtopSupport),
    .axi_req_t            (axi_req_t),
    .axi_resp_t           (axi_resp_t),
    .NoMstPorts           (NoMstPorts),
    .MaxTrans             (MaxTrans),
    .AxiLookBits          (AxiLookBits),
    .UniqueIds            (UniqueIds),
    .NoMulticastPorts     (0),
    .MaxMcastTrans        (1)
  ) i_axi_mcast_demux_simple (
    .clk_i                (clk_i),
    .rst_ni               (rst_ni),
    .test_i               (test_i),
    .slv_req_i            (slv_req_i),
    .slv_aw_select_i      (aw_select_mask),
    .slv_aw_addr_i        ('0),
    .slv_aw_mask_i        ('0),
    .slv_ar_select_i      (slv_ar_select_i),
    .slv_resp_o           (slv_resp_o),
    .mst_reqs_o           (mst_reqs_o),
    .mst_resps_i          (mst_resps_i),
    .mst_is_mcast_o       (),
    .mst_aw_commit_o      ()
  );

endmodule
