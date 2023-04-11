// Copyright (c) 2014-2020 ETH Zurich, University of Bologna
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
// - Fabian Schuiki <fschuiki@iis.ee.ethz.ch>

/// An AXI4+ATOP to AXI4-Lite converter with atomic transaction and burst support.
module axi_to_axi_lite #(
  parameter int unsigned AddrWidth      = 32'd0,
  parameter int unsigned DataWidth      = 32'd0,
  parameter int unsigned IdWidth        = 32'd0,
  parameter int unsigned UserWidth      = 32'd0,
  parameter int unsigned MaxWriteTxns   = 32'd0,
  parameter int unsigned MaxReadTxns    = 32'd0,
  parameter bit          FallThrough    = 1'b1,  // FIFOs in Fall through mode in ID reflect
  parameter type         axi_req_t      = logic,
  parameter type         axi_rsp_t      = logic,
  parameter type         axi_lite_req_t = logic,
  parameter type         axi_lite_rsp_t = logic
) (
  input  logic          clk_i,    // Clock
  input  logic          rst_ni,   // Asynchronous reset active low
  input  logic          test_i,   // Testmode enable
  // subordinate port full AXI4+ATOP
  input  axi_req_t      sbr_port_req_i,
  output axi_rsp_t      sbr_port_rsp_o,
  // manager port AXI4-Lite
  output axi_lite_req_t mgr_port_req_o,
  input  axi_lite_rsp_t mgr_port_rsp_i
);
  // full bus declarations
  axi_req_t filtered_req, splitted_req;
  axi_rsp_t filtered_rsp, splitted_rsp;

  // atomics adapter so that atomics can be resolved
  axi_atop_filter #(
    .IdWidth      ( IdWidth      ),
    .MaxWriteTxns ( MaxWriteTxns ),
    .axi_req_t    ( axi_req_t    ),
    .axi_rsp_t    ( axi_rsp_t    )
  ) i_axi_atop_filter(
    .clk_i     ( clk_i        ),
    .rst_ni    ( rst_ni       ),
    .sbr_port_req_i ( sbr_port_req_i    ),
    .sbr_port_rsp_o ( sbr_port_rsp_o    ),
    .mgr_port_req_o ( filtered_req ),
    .mgr_port_rsp_i ( filtered_rsp )
  );

  // burst splitter so that the id reflect module has no burst accessing it
  axi_burst_splitter #(
    .MaxReadTxns  ( MaxReadTxns  ),
    .MaxWriteTxns ( MaxWriteTxns ),
    .AddrWidth    ( AddrWidth    ),
    .DataWidth    ( DataWidth    ),
    .IdWidth      ( IdWidth      ),
    .UserWidth    ( UserWidth    ),
    .axi_req_t    ( axi_req_t    ),
    .axi_rsp_t    ( axi_rsp_t    )
  ) i_axi_burst_splitter (
    .clk_i     ( clk_i        ),
    .rst_ni    ( rst_ni       ),
    .sbr_port_req_i ( filtered_req ),
    .sbr_port_rsp_o ( filtered_rsp ),
    .mgr_port_req_o ( splitted_req ),
    .mgr_port_rsp_i ( splitted_rsp )
  );

  // ID reflect module handles the conversion from the full AXI to AXI lite on the wireing
  axi_to_axi_lite_id_reflect #(
    .IdWidth        ( IdWidth        ),
    .MaxWriteTxns   ( MaxWriteTxns   ),
    .MaxReadTxns    ( MaxReadTxns    ),
    .FallThrough    ( FallThrough    ),
    .axi_req_t      ( axi_req_t      ),
    .axi_rsp_t      ( axi_rsp_t      ),
    .axi_lite_req_t ( axi_lite_req_t ),
    .axi_lite_rsp_t ( axi_lite_rsp_t )
  ) i_axi_to_axi_lite_id_reflect (
    .clk_i     ( clk_i        ),
    .rst_ni    ( rst_ni       ),
    .test_i    ( test_i       ),
    .sbr_port_req_i ( splitted_req ),
    .sbr_port_rsp_o ( splitted_rsp ),
    .mgr_port_req_o ( mgr_port_req_o    ),
    .mgr_port_rsp_i ( mgr_port_rsp_i    )
  );

  // Assertions, check params
  // pragma translate_off
  `ifndef VERILATOR
  initial begin
    assume (IdWidth   > 0) else $fatal(1, "AXI ID width has to be > 0");
    assume (AddrWidth > 0) else $fatal(1, "AXI address width has to be > 0");
    assume (DataWidth > 0) else $fatal(1, "AXI data width has to be > 0");
  end
  `endif
  // pragma translate_on
endmodule

// Description: This module does the translation of the full AXI4+ATOP to AXI4-Lite signals.
//              It reflects the ID of the incoming transaction and crops all signals not used
//              in AXI4-Lite. It requires that incoming AXI4+ATOP transactions have a
//              `axi_pkg::len_t` of `'0` and an `axi_pkg::atop_t` of `'0`.

module axi_to_axi_lite_id_reflect #(
  parameter int unsigned IdWidth        = 32'd0,
  parameter int unsigned MaxWriteTxns   = 32'd0,
  parameter int unsigned MaxReadTxns    = 32'd0,
  parameter bit          FallThrough    = 1'b1,  // FIFOs in fall through mode
  parameter type         axi_req_t      = logic,
  parameter type         axi_rsp_t      = logic,
  parameter type         axi_lite_req_t = logic,
  parameter type         axi_lite_rsp_t = logic
) (
  input  logic          clk_i,    // Clock
  input  logic          rst_ni,   // Asynchronous reset active low
  input  logic          test_i,   // Testmode enable
  // subordinate port full AXI
  input  axi_req_t      sbr_port_req_i,
  output axi_rsp_t      sbr_port_rsp_o,
  // manager port AXI LITE
  output axi_lite_req_t mgr_port_req_o,
  input  axi_lite_rsp_t mgr_port_rsp_i
);
  typedef logic [IdWidth-1:0] id_t;

  // FIFO status and control signals
  logic aw_full, aw_empty, aw_push, aw_pop, ar_full, ar_empty, ar_push, ar_pop;
  id_t  aw_reflect_id, ar_reflect_id;

  assign sbr_port_rsp_o = '{
    aw_ready: mgr_port_rsp_i.aw_ready & ~aw_full,
    w_ready:  mgr_port_rsp_i.w_ready,
    b: '{
      id:       aw_reflect_id,
      resp:     mgr_port_rsp_i.b.resp,
      default:  '0
    },
    b_valid:  mgr_port_rsp_i.b_valid  & ~aw_empty,
    ar_ready: mgr_port_rsp_i.ar_ready & ~ar_full,
    r: '{
      id:       ar_reflect_id,
      data:     mgr_port_rsp_i.r.data,
      resp:     mgr_port_rsp_i.r.resp,
      last:     1'b1,
      default:  '0
    },
    r_valid: mgr_port_rsp_i.r_valid & ~ar_empty,
    default: '0
  };

  // Write ID reflection
  assign aw_push = mgr_port_req_o.aw_valid & sbr_port_rsp_o.aw_ready;
  assign aw_pop  = sbr_port_rsp_o.b_valid & mgr_port_req_o.b_ready;
  fifo_v3 #(
    .FALL_THROUGH ( FallThrough  ),
    .DEPTH        ( MaxWriteTxns ),
    .dtype        ( id_t         )
  ) i_aw_id_fifo (
    .clk_i     ( clk_i           ),
    .rst_ni    ( rst_ni          ),
    .flush_i   ( 1'b0            ),
    .testmode_i( test_i          ),
    .full_o    ( aw_full         ),
    .empty_o   ( aw_empty        ),
    .usage_o   ( /*not used*/    ),
    .data_i    ( sbr_port_req_i.aw.id ),
    .push_i    ( aw_push         ),
    .data_o    ( aw_reflect_id   ),
    .pop_i     ( aw_pop          )
  );

  // Read ID reflection
  assign ar_push = mgr_port_req_o.ar_valid & sbr_port_rsp_o.ar_ready;
  assign ar_pop  = sbr_port_rsp_o.r_valid & mgr_port_req_o.r_ready;
  fifo_v3 #(
    .FALL_THROUGH ( FallThrough ),
    .DEPTH        ( MaxReadTxns ),
    .dtype        ( id_t        )
  ) i_ar_id_fifo (
    .clk_i     ( clk_i           ),
    .rst_ni    ( rst_ni          ),
    .flush_i   ( 1'b0            ),
    .testmode_i( test_i          ),
    .full_o    ( ar_full         ),
    .empty_o   ( ar_empty        ),
    .usage_o   ( /*not used*/    ),
    .data_i    ( sbr_port_req_i.ar.id ),
    .push_i    ( ar_push         ),
    .data_o    ( ar_reflect_id   ),
    .pop_i     ( ar_pop          )
  );

  assign mgr_port_req_o = '{
    aw: '{
      addr: sbr_port_req_i.aw.addr,
      prot: sbr_port_req_i.aw.prot
    },
    aw_valid: sbr_port_req_i.aw_valid & ~aw_full,
    w: '{
      data: sbr_port_req_i.w.data,
      strb: sbr_port_req_i.w.strb
    },
    w_valid:  sbr_port_req_i.w_valid,
    b_ready:  sbr_port_req_i.b_ready & ~aw_empty,
    ar: '{
      addr: sbr_port_req_i.ar.addr,
      prot: sbr_port_req_i.ar.prot
    },
    ar_valid: sbr_port_req_i.ar_valid & ~ar_full,
    r_ready:  sbr_port_req_i.r_ready  & ~ar_empty,
    default:  '0
  };

  // Assertions
  // pragma translate_off
  `ifndef VERILATOR
  aw_atop: assume property( @(posedge clk_i) disable iff (~rst_ni)
                        sbr_port_req_i.aw_valid |-> (sbr_port_req_i.aw.atop == '0)) else
    $fatal(1, "Module does not support atomics. Value observed: %0b", sbr_port_req_i.aw.atop);
  aw_axi_len: assume property( @(posedge clk_i) disable iff (~rst_ni)
                        sbr_port_req_i.aw_valid |-> (sbr_port_req_i.aw.len == '0)) else
    $fatal(1, "AW request length has to be zero. Value observed: %0b", sbr_port_req_i.aw.len);
  w_axi_last: assume property( @(posedge clk_i) disable iff (~rst_ni)
                        sbr_port_req_i.w_valid |-> (sbr_port_req_i.w.last == 1'b1)) else
    $fatal(1, "W last signal has to be one. Value observed: %0b", sbr_port_req_i.w.last);
  ar_axi_len: assume property( @(posedge clk_i) disable iff (~rst_ni)
                        sbr_port_req_i.ar_valid |-> (sbr_port_req_i.ar.len == '0)) else
    $fatal(1, "AR request length has to be zero. Value observed: %0b", sbr_port_req_i.ar.len);
  `endif
  // pragma translate_on
endmodule

// interface wrapper
`include "axi/assign.svh"
`include "axi/typedef.svh"
module axi_to_axi_lite_intf #(
  /// AXI bus parameters
  parameter int unsigned AXI_ADDR_WIDTH     = 32'd0,
  parameter int unsigned AXI_DATA_WIDTH     = 32'd0,
  parameter int unsigned AXI_ID_WIDTH       = 32'd0,
  parameter int unsigned AXI_USER_WIDTH     = 32'd0,
  /// Maximum number of outstanding writes.
  parameter int unsigned AXI_MAX_WRITE_TXNS = 32'd1,
  /// Maximum number of outstanding reads.
  parameter int unsigned AXI_MAX_READ_TXNS  = 32'd1,
  parameter bit          FALL_THROUGH       = 1'b1
) (
  input logic     clk_i,
  input logic     rst_ni,
  input logic     testmode_i,
  AXI_BUS.Subordinate   sbr,
  AXI_LITE.Manager mgr
);
  typedef logic [AXI_ADDR_WIDTH-1:0]   addr_t;
  typedef logic [AXI_DATA_WIDTH-1:0]   data_t;
  typedef logic [AXI_ID_WIDTH-1:0]       id_t;
  typedef logic [AXI_DATA_WIDTH/8-1:0] strb_t;
  typedef logic [AXI_USER_WIDTH-1:0]   user_t;
  // full channels typedefs
  `AXI_TYPEDEF_AW_CHAN_T(full_aw_chan_t, addr_t, id_t, user_t)
  `AXI_TYPEDEF_W_CHAN_T(full_w_chan_t, data_t, strb_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T(full_b_chan_t, id_t, user_t)
  `AXI_TYPEDEF_AR_CHAN_T(full_ar_chan_t, addr_t, id_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(full_r_chan_t, data_t, id_t, user_t)
  `AXI_TYPEDEF_REQ_T(axi_req_t, full_aw_chan_t, full_w_chan_t, full_ar_chan_t)
  `AXI_TYPEDEF_RSP_T(axi_rsp_t, full_b_chan_t, full_r_chan_t)
  // LITE channels typedef
  `AXI_LITE_TYPEDEF_AW_CHAN_T(lite_aw_chan_t, addr_t)
  `AXI_LITE_TYPEDEF_W_CHAN_T(lite_w_chan_t, data_t, strb_t)
  `AXI_LITE_TYPEDEF_B_CHAN_T(lite_b_chan_t)
  `AXI_LITE_TYPEDEF_AR_CHAN_T(lite_ar_chan_t, addr_t)
  `AXI_LITE_TYPEDEF_R_CHAN_T (lite_r_chan_t, data_t)
  `AXI_LITE_TYPEDEF_REQ_T(axi_lite_req_t, lite_aw_chan_t, lite_w_chan_t, lite_ar_chan_t)
  `AXI_LITE_TYPEDEF_RSP_T(axi_lite_rsp_t, lite_b_chan_t, lite_r_chan_t)

  axi_req_t full_req;
  axi_rsp_t full_rsp;
  axi_lite_req_t lite_req;
  axi_lite_rsp_t lite_rsp;

  `AXI_ASSIGN_TO_REQ(full_req, sbr)
  `AXI_ASSIGN_FROM_RSP(sbr, full_rsp)

  `AXI_LITE_ASSIGN_FROM_REQ(mgr, lite_req)
  `AXI_LITE_ASSIGN_TO_RSP(lite_rsp, mgr)

  axi_to_axi_lite #(
    .AddrWidth      ( AXI_ADDR_WIDTH     ),
    .DataWidth      ( AXI_DATA_WIDTH     ),
    .IdWidth        ( AXI_ID_WIDTH       ),
    .UserWidth      ( AXI_USER_WIDTH     ),
    .MaxWriteTxns   ( AXI_MAX_WRITE_TXNS ),
    .MaxReadTxns    ( AXI_MAX_READ_TXNS  ),
    .FallThrough    ( FALL_THROUGH       ),  // FIFOs in Fall through mode in ID reflect
    .axi_req_t      ( axi_req_t          ),
    .axi_rsp_t      ( axi_rsp_t          ),
    .axi_lite_req_t ( axi_lite_req_t     ),
    .axi_lite_rsp_t ( axi_lite_rsp_t     )
  ) i_axi_to_axi_lite (
    .clk_i     ( clk_i      ),
    .rst_ni    ( rst_ni     ),
    .test_i    ( testmode_i ),
    // subordinate port full AXI4+ATOP
    .sbr_port_req_i ( full_req   ),
    .sbr_port_rsp_o ( full_rsp   ),
    // manager port AXI4-Lite
    .mgr_port_req_o ( lite_req   ),
    .mgr_port_rsp_i ( lite_rsp   )
  );
endmodule
