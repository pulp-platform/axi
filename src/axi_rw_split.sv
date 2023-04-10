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

/// Splits a single read / write subordinate into one read and one write manager
///
/// Connects the ar and r channel of the read / write subordinate to the read manager
/// and the aw, w and b channel of the read / write subordinate to the write manager
module axi_rw_split #(
  parameter type axi_req_t = logic,
  parameter type axi_rsp_t = logic
) (
  input  logic      clk_i,
  input  logic      rst_ni,
  // Read / Write Subordinate
  input  axi_req_t sbr_req_i,
  output axi_rsp_t sbr_rsp_o,

  // Read Manager
  output axi_req_t mgr_read_req_o,
  input  axi_rsp_t mgr_read_rsp_i,

  // Write Manager
  output axi_req_t mgr_write_req_o,
  input  axi_rsp_t mgr_write_rsp_i
);

  //--------------------------------------
  // Read channel data
  //--------------------------------------

  // Assign Read channel structs
  `AXI_ASSIGN_AR_STRUCT ( mgr_read_req_o.ar  , sbr_req_i.ar      )
  `AXI_ASSIGN_R_STRUCT  ( sbr_rsp_o.r        , mgr_read_rsp_i.r  )

  // Read AW and W channel data
  assign mgr_read_req_o.aw        = '0;
  assign mgr_read_req_o.w         = '0;


  //--------------------------------------
  // Read channel handshakes
  //--------------------------------------

  // Read AR channel handshake
  assign mgr_read_req_o.ar_valid  = sbr_req_i.ar_valid;
  assign sbr_rsp_o.ar_ready       = mgr_read_rsp_i.ar_ready;

  // Read R channel handshake
  assign sbr_rsp_o.r_valid        = mgr_read_rsp_i.r_valid;
  assign mgr_read_req_o.r_ready   = sbr_req_i.r_ready;

  // Read AW, W and B handshake
  assign mgr_read_req_o.aw_valid  = 1'b0;
  assign mgr_read_req_o.w_valid   = 1'b0;
  assign mgr_read_req_o.b_ready   = 1'b0;

  // check for B never to be valid
  `ASSERT_NEVER(mgr_read_rsp_b_valid, mgr_read_rsp_i.b_valid, clk_i, !rst_ni)


  //--------------------------------------
  // Write channel data
  //--------------------------------------

  // Assign Write channel structs
  `AXI_ASSIGN_AW_STRUCT ( mgr_write_req_o.aw , sbr_req_i.aw      )
  `AXI_ASSIGN_W_STRUCT  ( mgr_write_req_o.w  , sbr_req_i.w       )
  `AXI_ASSIGN_B_STRUCT  ( sbr_rsp_o.b        , mgr_write_rsp_i.b )

  // Write AR channel data
  assign mgr_write_req_o.ar       = '0;


  //--------------------------------------
  // Write channel handshakes
  //--------------------------------------

  // Write AR and R channel handshake
  assign mgr_write_req_o.ar_valid = 1'b0;
  assign mgr_write_req_o.r_ready  = 1'b0;

  // check for R never to be valid
  `ASSERT_NEVER(mgr_read_rsp_r_valid, mgr_read_rsp_i.r_valid, clk_i, !rst_ni)

  // Write AW channel handshake
  assign mgr_write_req_o.aw_valid = sbr_req_i.aw_valid;
  assign sbr_rsp_o.aw_ready       = mgr_write_rsp_i.aw_ready;

  // Write W channel handshake
  assign mgr_write_req_o.w_valid  = sbr_req_i.w_valid;
  assign sbr_rsp_o.w_ready        = mgr_write_rsp_i.w_ready;

  // Write B channel handshake
  assign sbr_rsp_o.b_valid        = mgr_write_rsp_i.b_valid;
  assign mgr_write_req_o.b_ready  = sbr_req_i.b_ready;

endmodule : axi_rw_split
