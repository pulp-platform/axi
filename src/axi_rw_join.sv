// Copyright (c) 2022 ETH Zurich, University of Bologna
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
// - Tobias Senti <tsenti@ethz.ch>

`include "axi/assign.svh"
`include "common_cells/assertions.svh"

/// Joins a read and a write subordinate into one single read / write manager
///
/// Connects the ar and r channel of the read subordinate to the read / write manager
/// and the aw, w and b channel of the write subordinate to the read / write manager
module axi_rw_join #(
  parameter type axi_req_t = logic,
  parameter type axi_rsp_t = logic
) (
  input  logic     clk_i,
  input  logic     rst_ni,
  // Read Subordinate
  input  axi_req_t sbr_read_req_i,
  output axi_rsp_t sbr_read_rsp_o,

  // Write Subordinate
  input  axi_req_t sbr_write_req_i,
  output axi_rsp_t sbr_write_rsp_o,

  // Read / Write Manager
  output axi_req_t mgr_req_o,
  input  axi_rsp_t mgr_rsp_i
);

  //--------------------------------------
  // Read channel data
  //--------------------------------------

  // Assign Read Structs
  `AXI_ASSIGN_AR_STRUCT ( mgr_req_o.ar      , sbr_read_req_i.ar  )
  `AXI_ASSIGN_R_STRUCT  ( sbr_read_rsp_o.r  , mgr_rsp_i.r        )

  // Read B channel data
  assign sbr_read_rsp_o.b         = '0;


  //--------------------------------------
  // Read channel handshakes
  //--------------------------------------

  // Read AR channel handshake
  assign mgr_req_o.ar_valid       = sbr_read_req_i.ar_valid;
  assign sbr_read_rsp_o.ar_ready  = mgr_rsp_i.ar_ready;

  // Read R channel handshake
  assign sbr_read_rsp_o.r_valid   = mgr_rsp_i.r_valid;
  assign mgr_req_o.r_ready        = sbr_read_req_i.r_ready;

  // Read AW, W and B handshake
  assign sbr_read_rsp_o.aw_ready  = 1'b0;
  assign sbr_read_rsp_o.w_ready   = 1'b0;
  assign sbr_read_rsp_o.b_valid   = 1'b0;

  // check for AW and W never to be valid
  `ASSERT_NEVER(sbr_read_req_aw_valid, sbr_read_req_i.aw_valid, clk_i, !rst_ni)
  `ASSERT_NEVER(sbr_read_req_w_valid,  sbr_read_req_i.w_valid,  clk_i, !rst_ni)

  //--------------------------------------
  // Write channel data
  //--------------------------------------

  // Assign Write Structs
  `AXI_ASSIGN_AW_STRUCT ( mgr_req_o.aw      , sbr_write_req_i.aw )
  `AXI_ASSIGN_W_STRUCT  ( mgr_req_o.w       , sbr_write_req_i.w  )
  `AXI_ASSIGN_B_STRUCT  ( sbr_write_rsp_o.b , mgr_rsp_i.b        )

  // Write R channel data
  assign sbr_write_rsp_o.r        = '0;


  //--------------------------------------
  // Write channel handshakes
  //--------------------------------------

  // Write AR and R channel handshake
  assign sbr_write_rsp_o.ar_ready = 1'b0;
  assign sbr_write_rsp_o.r_valid  = 1'b0;

  // check for AR to never be valid
  `ASSERT_NEVER(sbr_write_req_ar_valid, sbr_write_req_i.ar_valid, clk_i, !rst_ni)

  // Write AW channel handshake
  assign mgr_req_o.aw_valid       = sbr_write_req_i.aw_valid;
  assign sbr_write_rsp_o.aw_ready = mgr_rsp_i.aw_ready;

  // Write W channel handshake
  assign mgr_req_o.w_valid        = sbr_write_req_i.w_valid;
  assign sbr_write_rsp_o.w_ready  = mgr_rsp_i.w_ready;

  // Write B channel handshake
  assign sbr_write_rsp_o.b_valid  = mgr_rsp_i.b_valid;
  assign mgr_req_o.b_ready        = sbr_write_req_i.b_ready;

endmodule : axi_rw_join
