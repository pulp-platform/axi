// Copyright (c) 2019 ETH Zurich, University of Bologna
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
// - Wolfgang Roenninger <wroennin@iis.ee.ethz.ch>
// - Andreas Kurth <akurth@iis.ee.ethz.ch>

// AXI Multiplexer: This module multiplexes the AXI4 slave ports down to one master port.
// The AXI IDs from the slave ports get extended with the respective slave port index.
// The extension width can be calculated with `$clog2(NoSlvPorts)`. This means the AXI
// ID for the master port has to be this `$clog2(NoSlvPorts)` wider than the ID for the
// slave ports.
// Responses are switched based on these bits. For example, with 4 slave ports
// a response with ID `6'b100110` will be forwarded to slave port 2 (`2'b10`).

// register macros
`include "common_cells/assertions.svh"
`include "common_cells/registers.svh"

module axi_mux #(
  // AXI parameter and channel types
  parameter int unsigned SlvAxiIDWidth = 32'd0, // AXI ID width, slave ports
  parameter type         slv_aw_chan_t = logic, // AW Channel Type, slave ports
  parameter type         mst_aw_chan_t = logic, // AW Channel Type, master port
  parameter type         w_chan_t      = logic, //  W Channel Type, all ports
  parameter type         slv_b_chan_t  = logic, //  B Channel Type, slave ports
  parameter type         mst_b_chan_t  = logic, //  B Channel Type, master port
  parameter type         slv_ar_chan_t = logic, // AR Channel Type, slave ports
  parameter type         mst_ar_chan_t = logic, // AR Channel Type, master port
  parameter type         slv_r_chan_t  = logic, //  R Channel Type, slave ports
  parameter type         mst_r_chan_t  = logic, //  R Channel Type, master port
  parameter type         slv_req_t     = logic, // Slave port request type
  parameter type         slv_resp_t    = logic, // Slave port response type
  parameter type         mst_req_t     = logic, // Master ports request type
  parameter type         mst_resp_t    = logic, // Master ports response type
  parameter int unsigned NoSlvPorts    = 32'd0, // Number of slave ports
  // Maximum number of outstanding transactions per write
  parameter int unsigned MaxWTrans     = 32'd8,
  // If enabled, this multiplexer is purely combinatorial
  parameter bit          FallThrough   = 1'b0,
  // add spill register on write master ports, adds a cycle latency on write channels
  parameter bit          SpillAw       = 1'b1,
  parameter bit          SpillW        = 1'b0,
  parameter bit          SpillB        = 1'b0,
  // add spill register on read master ports, adds a cycle latency on read channels
  parameter bit          SpillAr       = 1'b1,
  parameter bit          SpillR        = 1'b0
) (
  input  logic                       clk_i,    // Clock
  input  logic                       rst_ni,   // Asynchronous reset active low
  input  logic                       test_i,   // Test Mode enable
  // slave ports (AXI inputs), connect master modules here
  input  slv_req_t  [NoSlvPorts-1:0] slv_reqs_i,
  output slv_resp_t [NoSlvPorts-1:0] slv_resps_o,
  // master port (AXI outputs), connect slave modules here
  output mst_req_t                   mst_req_o,
  input  mst_resp_t                  mst_resp_i
);

  axi_mcast_mux #(
    .SlvAxiIDWidth(SlvAxiIDWidth),
    .slv_aw_chan_t(slv_aw_chan_t),
    .mst_aw_chan_t(mst_aw_chan_t),
    .w_chan_t     (w_chan_t),
    .slv_b_chan_t (slv_b_chan_t),
    .mst_b_chan_t (mst_b_chan_t),
    .slv_ar_chan_t(slv_ar_chan_t),
    .mst_ar_chan_t(mst_ar_chan_t),
    .slv_r_chan_t (slv_r_chan_t),
    .mst_r_chan_t (mst_r_chan_t),
    .slv_req_t    (slv_req_t),
    .slv_resp_t   (slv_resp_t),
    .mst_req_t    (mst_req_t),
    .mst_resp_t   (mst_resp_t),
    .NoSlvPorts   (NoSlvPorts),
    .MaxWTrans    (MaxWTrans),
    .FallThrough  (FallThrough),
    .SpillAw      (SpillAw),
    .SpillW       (SpillW),
    .SpillB       (SpillB),
    .SpillAr      (SpillAr),
    .SpillR       (SpillR)
  ) i_axi_mcast_mux (
    .clk_i          (clk_i),
    .rst_ni         (rst_ni),
    .test_i         (test_i),
    .slv_is_mcast_i ('0),
    .slv_aw_commit_i('0),
    .slv_reqs_i     (slv_reqs_i),
    .slv_resps_o    (slv_resps_o),
    .mst_req_o      (mst_req_o),
    .mst_resp_i     (mst_resp_i)
  );

endmodule

// interface wrap
`include "axi/assign.svh"
`include "axi/typedef.svh"
module axi_mux_intf #(
  parameter int unsigned SLV_AXI_ID_WIDTH = 32'd0, // Synopsys DC requires default value for params
  parameter int unsigned MST_AXI_ID_WIDTH = 32'd0,
  parameter int unsigned AXI_ADDR_WIDTH   = 32'd0,
  parameter int unsigned AXI_DATA_WIDTH   = 32'd0,
  parameter int unsigned AXI_USER_WIDTH   = 32'd0,
  parameter int unsigned NO_SLV_PORTS     = 32'd0, // Number of slave ports
  // Maximum number of outstanding transactions per write
  parameter int unsigned MAX_W_TRANS      = 32'd8,
  // if enabled, this multiplexer is purely combinatorial
  parameter bit          FALL_THROUGH     = 1'b0,
  // add spill register on write master ports, adds a cycle latency on write channels
  parameter bit          SPILL_AW         = 1'b1,
  parameter bit          SPILL_W          = 1'b0,
  parameter bit          SPILL_B          = 1'b0,
  // add spill register on read master ports, adds a cycle latency on read channels
  parameter bit          SPILL_AR         = 1'b1,
  parameter bit          SPILL_R          = 1'b0
) (
  input  logic   clk_i,                  // Clock
  input  logic   rst_ni,                 // Asynchronous reset active low
  input  logic   test_i,                 // Testmode enable
  AXI_BUS.Slave  slv [NO_SLV_PORTS-1:0], // slave ports
  AXI_BUS.Master mst                     // master port
);

  typedef logic [SLV_AXI_ID_WIDTH-1:0] slv_id_t;
  typedef logic [MST_AXI_ID_WIDTH-1:0] mst_id_t;
  typedef logic [AXI_ADDR_WIDTH -1:0]  addr_t;
  typedef logic [AXI_DATA_WIDTH-1:0]   data_t;
  typedef logic [AXI_DATA_WIDTH/8-1:0] strb_t;
  typedef logic [AXI_USER_WIDTH-1:0]   user_t;
  // channels typedef
  `AXI_TYPEDEF_AW_CHAN_T(slv_aw_chan_t, addr_t, slv_id_t, user_t)
  `AXI_TYPEDEF_AW_CHAN_T(mst_aw_chan_t, addr_t, mst_id_t, user_t)

  `AXI_TYPEDEF_W_CHAN_T(w_chan_t, data_t, strb_t, user_t)

  `AXI_TYPEDEF_B_CHAN_T(slv_b_chan_t, slv_id_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T(mst_b_chan_t, mst_id_t, user_t)

  `AXI_TYPEDEF_AR_CHAN_T(slv_ar_chan_t, addr_t, slv_id_t, user_t)
  `AXI_TYPEDEF_AR_CHAN_T(mst_ar_chan_t, addr_t, mst_id_t, user_t)

  `AXI_TYPEDEF_R_CHAN_T(slv_r_chan_t, data_t, slv_id_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(mst_r_chan_t, data_t, mst_id_t, user_t)

  `AXI_TYPEDEF_REQ_T(slv_req_t, slv_aw_chan_t, w_chan_t, slv_ar_chan_t)
  `AXI_TYPEDEF_RESP_T(slv_resp_t, slv_b_chan_t, slv_r_chan_t)

  `AXI_TYPEDEF_REQ_T(mst_req_t, mst_aw_chan_t, w_chan_t, mst_ar_chan_t)
  `AXI_TYPEDEF_RESP_T(mst_resp_t, mst_b_chan_t, mst_r_chan_t)

  slv_req_t  [NO_SLV_PORTS-1:0] slv_reqs;
  slv_resp_t [NO_SLV_PORTS-1:0] slv_resps;
  mst_req_t                     mst_req;
  mst_resp_t                    mst_resp;

  for (genvar i = 0; i < NO_SLV_PORTS; i++) begin : gen_assign_slv_ports
    `AXI_ASSIGN_TO_REQ(slv_reqs[i], slv[i])
    `AXI_ASSIGN_FROM_RESP(slv[i], slv_resps[i])
  end

  `AXI_ASSIGN_FROM_REQ(mst, mst_req)
  `AXI_ASSIGN_TO_RESP(mst_resp, mst)

  axi_mux #(
    .SlvAxiIDWidth ( SLV_AXI_ID_WIDTH ),
    .slv_aw_chan_t ( slv_aw_chan_t    ), // AW Channel Type, slave ports
    .mst_aw_chan_t ( mst_aw_chan_t    ), // AW Channel Type, master port
    .w_chan_t      ( w_chan_t         ), //  W Channel Type, all ports
    .slv_b_chan_t  ( slv_b_chan_t     ), //  B Channel Type, slave ports
    .mst_b_chan_t  ( mst_b_chan_t     ), //  B Channel Type, master port
    .slv_ar_chan_t ( slv_ar_chan_t    ), // AR Channel Type, slave ports
    .mst_ar_chan_t ( mst_ar_chan_t    ), // AR Channel Type, master port
    .slv_r_chan_t  ( slv_r_chan_t     ), //  R Channel Type, slave ports
    .mst_r_chan_t  ( mst_r_chan_t     ), //  R Channel Type, master port
    .slv_req_t     ( slv_req_t        ),
    .slv_resp_t    ( slv_resp_t       ),
    .mst_req_t     ( mst_req_t        ),
    .mst_resp_t    ( mst_resp_t       ),
    .NoSlvPorts    ( NO_SLV_PORTS     ), // Number of slave ports
    .MaxWTrans     ( MAX_W_TRANS      ),
    .FallThrough   ( FALL_THROUGH     ),
    .SpillAw       ( SPILL_AW         ),
    .SpillW        ( SPILL_W          ),
    .SpillB        ( SPILL_B          ),
    .SpillAr       ( SPILL_AR         ),
    .SpillR        ( SPILL_R          )
  ) i_axi_mux (
    .clk_i       ( clk_i     ), // Clock
    .rst_ni      ( rst_ni    ), // Asynchronous reset active low
    .test_i      ( test_i    ), // Test Mode enable
    .slv_reqs_i  ( slv_reqs  ),
    .slv_resps_o ( slv_resps ),
    .mst_req_o   ( mst_req   ),
    .mst_resp_i  ( mst_resp  )
  );
endmodule
