// Copyright (c) 2019-2020 ETH Zurich, University of Bologna
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
// - Manuel Eggimann <meggiman@iis.ee.ethz.ch>
// - Andreas Kurth <akurth@iis.ee.ethz.ch>
// - Fabian Schuiki <fschuiki@iis.ee.ethz.ch>
// - Florian Zaruba <zarubaf@iis.ee.ethz.ch>
// - Wolfgang Roenninger <wroennin@iis.ee.ethz.ch>
// - Luca Valente <luca.valente2@unibo.it>

`include "axi/assign.svh"

// A clock domain crossing on an AXI interface with support for one-sided clearing/reset.
// 
// For each of the five AXI channels, this module instantiates a CDC FIFO, whose push and pop
// ports are in separate clock domains.  IMPORTANT: For each AXI channel, you MUST properly
// constrain three paths through the FIFO; see the header of `cdc_fifo_gray_clearable`
// for instructions.
//
// Clearability Feature:
// In contrast to the regular axi_cdc module, this module allows the user to
// initiate one-sided asynchronous resets or synchronous clears. With the
// regular axi_cdc, this would result in spurious transactions apearing which
// inevitebly would result in the AXI bus to lock up. This module on the other
// hand leverages the common_cells' cdc_rst_ctrl IP that initiates reset sequence
// in lock-step and synchronizes it into the other side of the CDC IP.
//
// Usage:
// In normal operation, the axi_cdc_clearable behaves like a normal axi_cdc IP
// and does not differ in latency or bandwidth. If you initiate a synchronous
// reset on one side of the CDC (via the src/dst_clear_i signal), the module will
// first isolate the AXI channel waiting for all outstanding transactions to
// terminate first. It then initiates and synchronizes the reset sequence in lock
// step with the other side of the clock domain. Finally, once both sides of the
// CDC have been reset, the axi_cdc_clearable module becomes operational again
// and will deisolate its input.
//
// Parameters:
//
// ClearOnAsyncReset: By default, both the synchronous clear input as
//   well as the asynchronous reset will trigger a reset sequence. The async reset
//   triggering can be optionally disabled with the CLEAR_ON_ASYNC_REST
//   parameter. This might be useful if you only ever use the async resets simultaneously during
//   power up of both domains and want to have the CDC operational immediately
//   without an initial reset sequence first.
// NumPendingTransaction: The clearable CDC contains an axi_isolate instance
//   that ensures graceful isolation of the AXI channel before clearing the CDC.
//   This parameter controls the maximum number of in-flight transactions this
//   module can track (the only implication of making this parameter larger is a
//   wider transaction counter).

// Interface Behavior:

// Initiate a reset procedure by either asserting the src/dst_clear_i signal for
// at least one clock cylce or (if enabled) by asserting either sides async
// reset. As soon as the src/dst_isolate_req_o signal is asserted, the CDC
// initiates the isolation phase and will isolate the AXI port from the outside
// world (either by waiting for in-flight transactions to be terminated or by
// forcefully revoking the transaction).  The src/dst_force_isolate_i signal can be used to bypass
// the axi isolate step and thus forcefully terminate all outstanding
// transactions. This will cause the bus to no longer be AXI compliant since
// valid signals of the AXI channels will be revoked. However, in case you want
// to reset a faulty AXI IP this might be exactly the behavior desired. The
// src/dst_isolated_o signal indicates the successful isolation of the AXI channel. The signal is synchronous to the
// respective clock domain and indicate that it is now safe to reset either side
// of the CDC. The CDC will remain in this state until the src/dst_isolate_ack_i
// signal is asserted by the outside logic. This signal can be used to keep the
// CDC in isolation state until we are ready to actually complete the reset
// sequence.


// How to Use This Module For One-Sided Clock Domain Resetting:
// 
// Assume the following scenario: We have three clock domains a,b and c. Each
// clock domain communicates with all other clock domains via a clearable AXI
// CDCs (the master/slave role is not important for this example). So we have
// cdc instances i_a2b, i_a2c and i_b2c.
// 
// Integration: Connect each side of the CDC to their respective clock domains
// and AXI ports.
// 
// Usage: Now we want to reset clock domain A: 
// 1. Initiate a SYNCHRONOUS clear on i_a2b and i_a2c
// 2. Wait for both CDCs to assert their src/dst_isolated_o signal on A's side
// of the clock domain
// 3. Reset clock domain A (e.g. by using the asynchronous reset) BUT DO NOT
// RESET THE CDCs.
// 4. After reset, assert the src/dst_isolate_req_ack_i signal of i_a2b and
// i_a2c until src/dst_isolate_req_o of A's side of both CDCs is deasserted.
// 5. Resume normal operation.

// When you want to gracefully reset either side of the channel FIRST initiate a
// SYNCHRONOUS clear sequence on either side of the CDC (it does not matter
// which one you choose). As soon as the src/dst_isolated_o signal is asserted,
// you can safely reset one of the clock domains (assuming there are no
// other CDC crossings to be cleared)
// 
// 
// For more details on the internal working principles of the reset sequencer
// check the source code documentation of the common_cells/cdc_reset_ctrl
// module.


module axi_cdc_clearable 
  import cdc_reset_ctrlr_pkg::clear_seq_phase_e;
#(
  parameter type aw_chan_t            = logic, // AW Channel Type
  parameter type w_chan_t             = logic, //  W Channel Type
  parameter type b_chan_t             = logic, //  B Channel Type
  parameter type ar_chan_t            = logic, // AR Channel Type
  parameter type r_chan_t             = logic, //  R Channel Type
  parameter type axi_req_t            = logic, // encapsulates request channels
  parameter type axi_resp_t           = logic, // encapsulates request channels
  /// Depth of the FIFO crossing the clock domain, given as 2**LOG_DEPTH.
  parameter int unsigned  LogDepth    = 1,
  // Parameters specific to clearability feature
  parameter ClearOnAsyncReset         = 1'b1,
  /// The maximum number of outstanding transactions the axi_isolate module
  /// within this IP can track (just implies a wider transaction counter).
  parameter NumPendingTransaction     = 16,
  /// Address width of all AXI4+ATOP ports
  parameter int unsigned AxiAddrWidth = 32'd0,
  /// Data width of all AXI4+ATOP ports
  parameter int unsigned AxiDataWidth = 32'd0,
  /// ID width of all AXI4+ATOP ports
  parameter int unsigned AxiIdWidth   = 32'd0,
  /// User signal width of all AXI4+ATOP ports
  parameter int unsigned AxiUserWidth = 32'd0
) (
  // slave side - clocked by `src_clk_i`
  input  logic      src_clk_i,
  input  logic      src_rst_ni,
  input  logic      src_clear_i,
  input  logic      src_force_isolate_i, 
  output logic      src_isolated_o,
  output logic      src_isolate_req_o,
  input  logic      src_isolate_ack_i,
  input  axi_req_t  src_req_i,
  output axi_resp_t src_resp_o,
  // master side - clocked by `dst_clk_i`
  input  logic      dst_clk_i,
  input  logic      dst_rst_ni,
  input  logic      dst_clear_i,
  input  logic      dst_force_isolate_i,
  output logic      dst_isolated_o,
  output logic      dst_isolate_req_o,
  input  logic      dst_isolate_ack_i,
  output axi_req_t  dst_req_o,
  input  axi_resp_t dst_resp_i
);

  aw_chan_t [2**LogDepth-1:0] async_data_aw_data;
  w_chan_t  [2**LogDepth-1:0] async_data_w_data;
  b_chan_t  [2**LogDepth-1:0] async_data_b_data;
  ar_chan_t [2**LogDepth-1:0] async_data_ar_data;
  r_chan_t  [2**LogDepth-1:0] async_data_r_data;
  logic          [LogDepth:0] async_data_aw_wptr, async_data_aw_rptr,
                              async_data_w_wptr,  async_data_w_rptr,
                              async_data_b_wptr,  async_data_b_rptr,
                              async_data_ar_wptr, async_data_ar_rptr,
                              async_data_r_wptr,  async_data_r_rptr;

  logic                       async_src2dst_clr_seq_next_phase;
  logic                       async_src2dst_clr_seq_req;
  logic                       async_src2dst_clr_seq_ack;
  logic                       async_dst2src_clr_seq_next_phase;
  logic                       async_dst2src_clr_seq_req;
  logic                       async_dst2src_clr_seq_ack;

  axi_cdc_clearable_src #(
    .aw_chan_t             ( aw_chan_t               ),
    .w_chan_t              ( w_chan_t                ),
    .b_chan_t              ( b_chan_t                ),
    .ar_chan_t             ( ar_chan_t               ),
    .r_chan_t              ( r_chan_t                ),
    .axi_req_t             ( axi_req_t               ),
    .axi_resp_t            ( axi_resp_t              ),
    .LogDepth              ( LogDepth                ),
    .ClearOnAsyncReset     ( ClearOnAsyncReset       ),
    .NumPendingTransaction ( NumPendingTransaction   ),
    .AxiAddrWidth          ( AxiAddrWidth            ),
    .AxiDataWidth          ( AxiDataWidth            ),
    .AxiIdWidth            ( AxiIdWidth              ),
    .AxiUserWidth          ( AxiUserWidth            )
  ) i_axi_cdc_src (
                .src_clk_i,
                .src_rst_ni,
                .src_req_i,
                .src_resp_o,
                .src_clear_i,
                .src_force_isolate_i,
                .src_isolated_o,
                .src_isolate_req_o,
                .src_isolate_ack_i,
    (* async *) .async_data_master_aw_data_o  ( async_data_aw_data  ),
    (* async *) .async_data_master_aw_wptr_o  ( async_data_aw_wptr  ),
    (* async *) .async_data_master_aw_rptr_i  ( async_data_aw_rptr  ),
    (* async *) .async_data_master_w_data_o   ( async_data_w_data   ),
    (* async *) .async_data_master_w_wptr_o   ( async_data_w_wptr   ),
    (* async *) .async_data_master_w_rptr_i   ( async_data_w_rptr   ),
    (* async *) .async_data_master_b_data_i   ( async_data_b_data   ),
    (* async *) .async_data_master_b_wptr_i   ( async_data_b_wptr   ),
    (* async *) .async_data_master_b_rptr_o   ( async_data_b_rptr   ),
    (* async *) .async_data_master_ar_data_o  ( async_data_ar_data  ),
    (* async *) .async_data_master_ar_wptr_o  ( async_data_ar_wptr  ),
    (* async *) .async_data_master_ar_rptr_i  ( async_data_ar_rptr  ),
    (* async *) .async_data_master_r_data_i   ( async_data_r_data   ),
    (* async *) .async_data_master_r_wptr_i   ( async_data_r_wptr   ),
    (* async *) .async_data_master_r_rptr_o   ( async_data_r_rptr   ),
    (* async *) .async_clr_seq_next_phase_o,
    (* async *) .async_clr_seq_req_o,
    (* async *) .async_clr_seq_ack_i,
    (* async *) .async_clr_seq_next_phase_i,
    (* async *) .async_clr_seq_req_i,
    (* async *) .async_clr_seq_ack_o
  );

  axi_cdc_clearable_dst #(
    .aw_chan_t  ( aw_chan_t   ),
    .w_chan_t   ( w_chan_t    ),
    .b_chan_t   ( b_chan_t    ),
    .ar_chan_t  ( ar_chan_t   ),
    .r_chan_t   ( r_chan_t    ),
    .axi_req_t  ( axi_req_t   ),
    .axi_resp_t ( axi_resp_t  ),
    .LogDepth   ( LogDepth    ),
    .ClearOnAsyncReset     ( ClearOnAsyncReset       ),
    .NumPendingTransaction ( NumPendingTransaction   ),
    .AxiAddrWidth          ( AxiAddrWidth            ),
    .AxiDataWidth          ( AxiDataWidth            ),
    .AxiIdWidth            ( AxiIdWidth              ),
    .AxiUserWidth          ( AxiUserWidth            )
  ) i_axi_cdc_dst (
                .dst_clk_i,
                .dst_rst_ni,
                .dst_req_o,
                .dst_resp_i,
                .dst_clear_i,
                .dst_force_isolate_i,
                .dst_isolated_o,
                .dst_isolate_req_o,
                .dst_isolate_ack_i,
    (* async *) .async_data_slave_aw_wptr_i ( async_data_aw_wptr  ),
    (* async *) .async_data_slave_aw_rptr_o ( async_data_aw_rptr  ),
    (* async *) .async_data_slave_aw_data_i ( async_data_aw_data  ),
    (* async *) .async_data_slave_w_wptr_i  ( async_data_w_wptr   ),
    (* async *) .async_data_slave_w_rptr_o  ( async_data_w_rptr   ),
    (* async *) .async_data_slave_w_data_i  ( async_data_w_data   ),
    (* async *) .async_data_slave_b_wptr_o  ( async_data_b_wptr   ),
    (* async *) .async_data_slave_b_rptr_i  ( async_data_b_rptr   ),
    (* async *) .async_data_slave_b_data_o  ( async_data_b_data   ),
    (* async *) .async_data_slave_ar_wptr_i ( async_data_ar_wptr  ),
    (* async *) .async_data_slave_ar_rptr_o ( async_data_ar_rptr  ),
    (* async *) .async_data_slave_ar_data_i ( async_data_ar_data  ),
    (* async *) .async_data_slave_r_wptr_o  ( async_data_r_wptr   ),
    (* async *) .async_data_slave_r_rptr_i  ( async_data_r_rptr   ),
    (* async *) .async_data_slave_r_data_o  ( async_data_r_data   ),
    (* async *) .async_clr_seq_next_phase_o,
    (* async *) .async_clr_seq_req_o,
    (* async *) .async_clr_seq_ack_i,
    (* async *) .async_clr_seq_next_phase_i,
    (* async *) .async_clr_seq_req_i,
    (* async *) .async_clr_seq_ack_o
);

endmodule

`include "axi/assign.svh"
`include "axi/typedef.svh"

// interface wrapper
module axi_cdc_intf
  import cdc_reset_ctrlr_pkg::clear_seq_phase_e;
#(
  parameter int unsigned AXI_ID_WIDTH   = 0,
  parameter int unsigned AXI_ADDR_WIDTH = 0,
  parameter int unsigned AXI_DATA_WIDTH = 0,
  parameter int unsigned AXI_USER_WIDTH = 0,
  /// Depth of the FIFO crossing the clock domain, given as 2**LOG_DEPTH.
  parameter int unsigned LOG_DEPTH      = 1,
  /// Parameters specific to clearbility feature
  PARAMETER CLEAR_ON_ASYNC_RESET        = 1'b1,
  /// The maximum number of outstanding transactions the axi_isolate module
  /// within this IP can track (just implies a wider transaction counter).
  parameter NUM_PENDING_TRANSACTION     = 16
) (
   // slave side - clocked by `src_clk_i`
  input  logic      src_clk_i,
  input  logic      src_rst_ni,
  input  logic      src_clear_i,
  input  logic      src_force_isolate_i, 
  output logic      src_isolated_o,
  output logic      src_isolate_req_o,
  input  logic      src_isolate_ack_i,
  AXI_BUS.Slave     src,
  // master side - clocked by `dst_clk_i`
  input  logic      dst_clk_i,
  input  logic      dst_rst_ni,
  input  logic      dst_clear_i,
  input  logic      dst_force_isolate_i, 
  output logic      dst_isolated_o,
  output logic      dst_isolate_req_o,
  input  logic      dst_isolate_ack_i,
  AXI_BUS.Master    dst
);

  typedef logic [AXI_ID_WIDTH-1:0]     id_t;
  typedef logic [AXI_ADDR_WIDTH-1:0]   addr_t;
  typedef logic [AXI_DATA_WIDTH-1:0]   data_t;
  typedef logic [AXI_DATA_WIDTH/8-1:0] strb_t;
  typedef logic [AXI_USER_WIDTH-1:0]   user_t;
  `AXI_TYPEDEF_AW_CHAN_T(aw_chan_t, addr_t, id_t, user_t)
  `AXI_TYPEDEF_W_CHAN_T(w_chan_t, data_t, strb_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T(b_chan_t, id_t, user_t)
  `AXI_TYPEDEF_AR_CHAN_T(ar_chan_t, addr_t, id_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(r_chan_t, data_t, id_t, user_t)
  `AXI_TYPEDEF_REQ_T(req_t, aw_chan_t, w_chan_t, ar_chan_t)
  `AXI_TYPEDEF_RESP_T(resp_t, b_chan_t, r_chan_t)

  req_t  src_req,  dst_req;
  resp_t src_resp, dst_resp;

  `AXI_ASSIGN_TO_REQ(src_req, src)
  `AXI_ASSIGN_FROM_RESP(src, src_resp)

  `AXI_ASSIGN_FROM_REQ(dst, dst_req)
  `AXI_ASSIGN_TO_RESP(dst_resp, dst)

  axi_cdc_clearable #(
    .aw_chan_t  ( aw_chan_t ),
    .w_chan_t   ( w_chan_t  ),
    .b_chan_t   ( b_chan_t  ),
    .ar_chan_t  ( ar_chan_t ),
    .r_chan_t   ( r_chan_t  ),
    .axi_req_t  ( req_t     ),
    .axi_resp_t ( resp_t    ),
    .LogDepth   ( LOG_DEPTH ),
    .ClearOnAsyncReset     ( CLEAR_ON_ASYNC_RESET    ),
    .NumPendingTransaction ( NUM_PENDING_TRANSACTION ),
    .AxiAddrWidth          ( AXI_ADDR_WIDTH          ),
    .AxiDataWidth          ( AXI_DATA_WIDTH          ),
    .AxiIdWidth            ( AXI_ID_WIDTH            ),
    .AxiUserWidth          ( AXI_USER_WIDTH          )
  ) i_axi_cdc (
    .src_clk_i,
    .src_rst_ni,
    .src_clear_i,
    .src_force_isolate_i,
    .src_isolated_o,
    .src_isolate_req_o,
    .src_isolate_ack_i,
    .src_req_i  ( src_req  ),
    .src_resp_o ( src_resp ),
    .dst_clk_i,
    .dst_rst_ni,
    .dst_clear_i,
    .dst_force_isolate_i,
    .dst_isolated_o,
    .dst_isolate_req_o,
    .dst_isolate_ack_i,
    .dst_req_o  ( dst_req  ),
    .dst_resp_i ( dst_resp )
  );

endmodule

module axi_lite_cdc_intf
  import cdc_reset_ctrlr_pkg::clear_seq_phase_e;
#(
  parameter int unsigned AXI_ADDR_WIDTH = 0,
  parameter int unsigned AXI_DATA_WIDTH = 0,
  /// Depth of the FIFO crossing the clock domain, given as 2**LOG_DEPTH.
  parameter int unsigned LOG_DEPTH = 1,
  /// Parameters specific to clearbility feature
  PARAMETER CLEAR_ON_ASYNC_RESET        = 1'b1,
  /// The maximum number of outstanding transactions the axi_isolate module
  /// within this IP can track (just implies a wider transaction counter).
  parameter NUM_PENDING_TRANSACTION     = 16
) (
   // slave side - clocked by `src_clk_i`
  input  logic      src_clk_i,
  input  logic      src_rst_ni,
  input  logic      src_clear_i,
  input  logic      src_force_isolate_i,
  output logic      src_isolated_o,
  output logic      src_isolate_req_o,
  input  logic      src_isolate_ack_i,
  AXI_LITE.Slave    src,
  input  logic      dst_clk_i,
  input  logic      dst_rst_ni,
  input  logic      ds_clear_i,
  input  logic      dst_force_isolate_i,
  output logic      dst_isolated_o,
  output logic      dst_isolate_req_o,
  input  logic      dst_isolate_ack_i,
  AXI_LITE.Master   dst
);

  typedef logic [AXI_ADDR_WIDTH-1:0]   addr_t;
  typedef logic [AXI_DATA_WIDTH-1:0]   data_t;
  typedef logic [AXI_DATA_WIDTH/8-1:0] strb_t;
  `AXI_LITE_TYPEDEF_AW_CHAN_T(aw_chan_t, addr_t)
  `AXI_LITE_TYPEDEF_W_CHAN_T(w_chan_t, data_t, strb_t)
  `AXI_LITE_TYPEDEF_B_CHAN_T(b_chan_t)
  `AXI_LITE_TYPEDEF_AR_CHAN_T(ar_chan_t, addr_t)
  `AXI_LITE_TYPEDEF_R_CHAN_T(r_chan_t, data_t)
  `AXI_LITE_TYPEDEF_REQ_T(req_t, aw_chan_t, w_chan_t, ar_chan_t)
  `AXI_LITE_TYPEDEF_RESP_T(resp_t, b_chan_t, r_chan_t)

  req_t  src_req,  dst_req;
  resp_t src_resp, dst_resp;

  `AXI_LITE_ASSIGN_TO_REQ(src_req, src)
  `AXI_LITE_ASSIGN_FROM_RESP(src, src_resp)

  `AXI_LITE_ASSIGN_FROM_REQ(dst, dst_req)
  `AXI_LITE_ASSIGN_TO_RESP(dst_resp, dst)

  axi_cdc_clearable #(
    .aw_chan_t  ( aw_chan_t ),
    .w_chan_t   ( w_chan_t  ),
    .b_chan_t   ( b_chan_t  ),
    .ar_chan_t  ( ar_chan_t ),
    .r_chan_t   ( r_chan_t  ),
    .axi_req_t  ( req_t     ),
    .axi_resp_t ( resp_t    ),
    .LogDepth   ( LOG_DEPTH )
  ) i_axi_cdc (
    .src_clk_i,
    .src_rst_ni,
    .src_clear_i,
    .src_force_isolate_i,
    .src_isolated_o,
    .src_isolate_req_o,
    .src_isolate_ack_i,
    .src_req_i  ( src_req  ),
    .src_resp_o ( src_resp ),
    .dst_clk_i,
    .dst_rst_ni,
    .dst_clear_i,
    .dst_force_isolate_i,
    .dst_isolated_o,
    .dst_isolate_req_o,
    .dst_isolate_ack_i,
    .dst_req_o  ( dst_req  ),
    .dst_resp_i ( dst_resp )
  );

endmodule
