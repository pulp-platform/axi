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
// - Andreas Kurth <akurth@iis.ee.ethz.ch>
// - Luca Valente <luca.valente@unibo.it>
// - Wolfgang Roenninger <wroennin@iis.ee.ethz.ch>
// - Luca Rufer <luca@mosaic-soc.ch>

`include "axi/assign.svh"

/// An isolatable clock domain crossing on an AXI interface. This isolatable variant of the AXI CDC
/// allows one-sided power-down or reset without having to reset the other side of the CDC.
///
/// The module consists of an AXI isolate on the src side and a clearable CDC. When powering down or
/// resetting the dst side, the src side must first assert the `src_isolate_i` signal and wait until
/// the `src_isolated_o` signal is asserted. Assertion of the `src_isolated_o` signal indicates that
/// the AXI interface was isolated with all outstanding transactions completed and the CDC FIFO
/// pointers were cleared.
/// The `src_isolate_i` signal must remain asserted during the power-down and/or reset of the dst
/// side and may only be retracted after the reset on the dst side was completed.
/// After de-asserting the `src_isolate_i` signal, the user shall way for de-assertion of the
/// `src_isolated_o` signal before sending new AXI requests to ensure the AXI interface is no longer
/// isolated.
/// `src_isolate_i` and `src_isolated_o` form a 4-phase handshake signal, which may not be violated.
///
/// When powering down or resetting the src side, the dst side must first assert the `dst_isolate_i`
/// signal and wait until the `dst_isolated_o` signal is asserted. Assertion of the `dst_isolated_o`
/// signal indicates that all outstanding AXI transactions were completed and the CDC FIFO pointers
/// were cleared.
/// The `dst_isolate_i` signal is required to remain asserted until the power-down or the reset
/// of the src side unless the user can guarantee that no new AXI requests are issued.
/// After de-asserting the `dst_isolate_i` signal, the de-assertion of `dst_isolated_o` indicates
/// that the AXI interface on the src side is no longer isolated.
/// `dst_isolate_i` and `dst_isolated_o` form a 4-phase handshake signal, which may not be violated.
///
/// For each of the five AXI channels, this module instantiates a clearable CDC FIFO, whose push and
/// pop ports are in separate clock domains.  IMPORTANT: For each AXI channel, you MUST properly
/// constrain three paths through the FIFO; see the header of `cdc_fifo_gray_clearable` for
/// instructions.
module axi_cdc_isolatable
  import axi_pkg::*;
#(
  /// Address width of all AXI4+ATOP ports
  parameter int signed   AxiAddrWidth         = 32'd0,
  /// Data width of all AXI4+ATOP ports
  parameter int signed   AxiDataWidth         = 32'd0,
  /// ID width of all AXI4+ATOP ports
  parameter int signed   AxiIdWidth           = 32'd0,
  /// User signal width of all AXI4+ATOP ports
  parameter int signed   AxiUserWidth         = 32'd0,
  /// Support atomic operations (ATOPs)
  parameter bit          AtopSupport          = 1'b1,
  /// Request struct type of all AXI4+ATOP ports
  parameter type         axi_req_t            = logic,
  /// Response struct type of all AXI4+ATOP ports
  parameter type         axi_resp_t           = logic,
  /// Depth of the FIFO crossing the clock domain, given as 2**LOG_DEPTH.
  parameter int unsigned LogDepth             = 1,
  /// Number of synchronization registers to insert on the async pointers
  parameter int unsigned SyncStages           = 3,
  /// Gracefully terminate all incoming transactions in case of isolation by returning proper error
  /// responses.
  parameter bit          TerminateTransaction = 1'b0
) (
  // slave side - clocked by `src_clk_i`
  input  logic      src_clk_i,
  input  logic      src_rst_ni,
  input  logic      src_isolate_i,
  output logic      src_isolated_o,
  input  axi_req_t  src_req_i,
  output axi_resp_t src_resp_o,
  // master side - clocked by `dst_clk_i`
  input  logic      dst_clk_i,
  input  logic      dst_rst_ni,
  input  logic      dst_isolate_i,
  output logic      dst_isolated_o,
  output axi_req_t  dst_req_o,
  input  axi_resp_t dst_resp_i
);

  typedef logic [AxiIdWidth-1:0] id_t;
  typedef logic [AxiAddrWidth-1:0] addr_t;
  typedef logic [AxiDataWidth-1:0] data_t;
  typedef logic [AxiDataWidth/8-1:0] strb_t;
  typedef logic [AxiUserWidth-1:0] user_t;

  `AXI_TYPEDEF_AW_CHAN_T(aw_chan_t, addr_t, id_t, user_t)
  `AXI_TYPEDEF_W_CHAN_T(w_chan_t, data_t, strb_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T(b_chan_t, id_t, user_t)
  `AXI_TYPEDEF_AR_CHAN_T(ar_chan_t, addr_t, id_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(r_chan_t, data_t, id_t, user_t)

  //---------
  // Isolate
  //---------

  logic axi_src_isolate;
  logic axi_src_isolated;

  logic cdc_src_isolate, dst_isolate_sync;

  axi_req_t  src_req_iso;
  axi_resp_t src_resp_iso;

  // Isolation is triggered from the input signal or by request of the CDC
  assign axi_src_isolate = src_isolate_i | cdc_src_isolate | dst_isolate_sync;

  axi_isolate #(
    .NumPending          (2 ** LogDepth),
    .TerminateTransaction(TerminateTransaction),
    .AtopSupport         (AtopSupport),
    .AxiAddrWidth        (AxiAddrWidth),
    .AxiDataWidth        (AxiDataWidth),
    .AxiIdWidth          (AxiIdWidth),
    .AxiUserWidth        (AxiUserWidth),
    .axi_req_t           (axi_req_t),
    .axi_resp_t          (axi_resp_t)
  ) i_src_iso (
    .clk_i     (src_clk_i),
    .rst_ni    (src_rst_ni),
    .slv_req_i (src_req_i),
    .slv_resp_o(src_resp_o),
    .mst_req_o (src_req_iso),
    .mst_resp_i(src_resp_iso),
    .isolate_i (axi_src_isolate),
    .isolated_o(axi_src_isolated)
  );

  //--------------------------------
  // CDC Clear and Reset Controller
  //--------------------------------

  logic src_clear, dst_clear;

  logic src_clear_req, src_clear_ack_q;
  logic dst_clear_req, dst_clear_ack_q;
  logic dst_isolate_req, dst_isolate_ack_q;

  // Synchronize the clear and reset signaling in both directions
  cdc_reset_ctrlr #(
    .SYNC_STAGES         (SyncStages - 1),
    .CLEAR_ON_ASYNC_RESET(1'b0)
  ) i_cdc_reset_ctrlr (
    .a_clk_i        (src_clk_i),
    .a_rst_ni       (src_rst_ni),
    .a_clear_i      (src_clear),
    .a_clear_o      (src_clear_req),
    .a_clear_ack_i  (src_clear_ack_q),
    .a_isolate_o    (cdc_src_isolate),
    .a_isolate_ack_i(axi_src_isolated),
    .b_clk_i        (dst_clk_i),
    .b_rst_ni       (dst_rst_ni),
    .b_clear_i      (dst_clear),
    .b_clear_o      (dst_clear_req),
    .b_clear_ack_i  (dst_clear_ack_q),
    .b_isolate_o    (dst_isolate_req),
    .b_isolate_ack_i(dst_isolate_ack_q)
  );

  // The CDC can be cleared in one cycle
  always_ff @(posedge src_clk_i, negedge src_rst_ni) begin
    if (!src_rst_ni) begin
      src_clear_ack_q <= 1'b0;
    end else begin
      src_clear_ack_q <= src_clear_req;
    end
  end

  always_ff @(posedge dst_clk_i, negedge dst_rst_ni) begin
    if (!dst_rst_ni) begin
      dst_clear_ack_q <= 1'b0;
    end else begin
      dst_clear_ack_q <= dst_clear_req;
    end
  end

  // Isolation is controlled on the src side, dst side is irrelevant
  always_ff @(posedge dst_clk_i, negedge dst_rst_ni) begin
    if (!dst_rst_ni) begin
      dst_isolate_ack_q <= 1'b0;
    end else begin
      dst_isolate_ack_q <= dst_isolate_req;
    end
  end

  //--------------------------------
  // Isolate / Clear handshakes
  //--------------------------------

  logic src_isolate_in_q;
  logic src_isolated_d, src_isolated_q;

  logic dst_isolate_in_q;
  logic dst_isolated_d, dst_isolated_q;

  logic src_isolated_sync_n;

  // Initiate the CDC clear on the rising edge of the isolate inputs
  assign src_clear = src_isolate_i && !src_isolate_in_q;
  assign dst_clear = dst_isolate_i && !dst_isolate_in_q;

  always_comb begin
    src_isolated_d = src_isolated_q;

    if (src_isolate_i) begin
      // Isolation (+ CDC clear) complete when iso isolated and CDC clear complete
      if (axi_src_isolated && !cdc_src_isolate) begin
        src_isolated_d = 1'b1;
      end
    end else begin
      // Isolation revoked when no isolation and no CDC clear ongoing
      if (!axi_src_isolated && !cdc_src_isolate) begin
        src_isolated_d = 1'b0;
      end
    end
  end

  assign src_isolated_o = src_isolated_q;

  always_comb begin
    dst_isolated_d = dst_isolated_q;

    if (dst_isolate_i) begin
      // Dst isolation complete when crc reset controller has finished (falling edge of dst isolate)
      if (dst_isolate_ack_q && !dst_isolate_req) begin
        dst_isolated_d = 1'b1;
      end
    end else begin
      // Dst isolation released once iso on the source side is no longer isolating
      if (src_isolated_sync_n) begin
        dst_isolated_d = 1'b0;
      end
    end
  end

  assign dst_isolated_o = dst_isolated_q;

  always_ff @(posedge src_clk_i, negedge src_rst_ni) begin
    if (!src_rst_ni) begin
      src_isolate_in_q <= 1'b0;
      src_isolated_q   <= 1'b0;
    end else begin
      src_isolate_in_q <= src_isolate_i;
      src_isolated_q   <= src_isolated_d;
    end
  end

  always_ff @(posedge dst_clk_i, negedge dst_rst_ni) begin
    if (!dst_rst_ni) begin
      dst_isolate_in_q <= 1'b0;
      dst_isolated_q   <= 1'b0;
    end else begin
      dst_isolate_in_q <= dst_isolate_i;
      dst_isolated_q   <= dst_isolated_d;
    end
  end

  //--------------------------------
  // Destination clear synchronizer
  //--------------------------------

  sync #(
    .STAGES(SyncStages)
  ) i_dst_isolate_sync (
    .clk_i   (src_clk_i),
    .rst_ni  (src_rst_ni),
    .serial_i(dst_isolate_i),
    .serial_o(dst_isolate_sync)
  );

  sync #(
    .STAGES(SyncStages)
  ) i_dst_isolated_sync (
    .clk_i   (dst_clk_i),
    .rst_ni  (dst_rst_ni),
    .serial_i(!axi_src_isolated),
    .serial_o(src_isolated_sync_n)
  );

  //-----
  // CDC
  //-----

  aw_chan_t [2**LogDepth-1:0] async_data_aw_data;
  w_chan_t  [2**LogDepth-1:0] async_data_w_data;
  b_chan_t  [2**LogDepth-1:0] async_data_b_data;
  ar_chan_t [2**LogDepth-1:0] async_data_ar_data;
  r_chan_t  [2**LogDepth-1:0] async_data_r_data;
  logic [LogDepth:0]
      async_data_aw_wptr,
      async_data_aw_rptr,
      async_data_w_wptr,
      async_data_w_rptr,
      async_data_b_wptr,
      async_data_b_rptr,
      async_data_ar_wptr,
      async_data_ar_rptr,
      async_data_r_wptr,
      async_data_r_rptr;

  axi_cdc_src_clearable #(
    .aw_chan_t (aw_chan_t),
    .w_chan_t  (w_chan_t),
    .b_chan_t  (b_chan_t),
    .ar_chan_t (ar_chan_t),
    .r_chan_t  (r_chan_t),
    .axi_req_t (axi_req_t),
    .axi_resp_t(axi_resp_t),
    .LogDepth  (LogDepth),
    .SyncStages(SyncStages)
  ) i_axi_cdc_src (
    .src_clk_i,
    .src_rst_ni,
                .src_clear_i                (src_clear_req),
                .src_req_i                  (src_req_iso),
                .src_resp_o                 (src_resp_iso),
    (* async *) .async_data_master_aw_data_o(async_data_aw_data),
    (* async *) .async_data_master_aw_wptr_o(async_data_aw_wptr),
    (* async *) .async_data_master_aw_rptr_i(async_data_aw_rptr),
    (* async *) .async_data_master_w_data_o (async_data_w_data),
    (* async *) .async_data_master_w_wptr_o (async_data_w_wptr),
    (* async *) .async_data_master_w_rptr_i (async_data_w_rptr),
    (* async *) .async_data_master_b_data_i (async_data_b_data),
    (* async *) .async_data_master_b_wptr_i (async_data_b_wptr),
    (* async *) .async_data_master_b_rptr_o (async_data_b_rptr),
    (* async *) .async_data_master_ar_data_o(async_data_ar_data),
    (* async *) .async_data_master_ar_wptr_o(async_data_ar_wptr),
    (* async *) .async_data_master_ar_rptr_i(async_data_ar_rptr),
    (* async *) .async_data_master_r_data_i (async_data_r_data),
    (* async *) .async_data_master_r_wptr_i (async_data_r_wptr),
    (* async *) .async_data_master_r_rptr_o (async_data_r_rptr)
  );

  axi_cdc_dst_clearable #(
    .aw_chan_t (aw_chan_t),
    .w_chan_t  (w_chan_t),
    .b_chan_t  (b_chan_t),
    .ar_chan_t (ar_chan_t),
    .r_chan_t  (r_chan_t),
    .axi_req_t (axi_req_t),
    .axi_resp_t(axi_resp_t),
    .LogDepth  (LogDepth),
    .SyncStages(SyncStages)
  ) i_axi_cdc_dst (
    .dst_clk_i,
    .dst_rst_ni,
                .dst_clear_i               (dst_clear_req),
    .dst_req_o,
    .dst_resp_i,
    (* async *) .async_data_slave_aw_wptr_i(async_data_aw_wptr),
    (* async *) .async_data_slave_aw_rptr_o(async_data_aw_rptr),
    (* async *) .async_data_slave_aw_data_i(async_data_aw_data),
    (* async *) .async_data_slave_w_wptr_i (async_data_w_wptr),
    (* async *) .async_data_slave_w_rptr_o (async_data_w_rptr),
    (* async *) .async_data_slave_w_data_i (async_data_w_data),
    (* async *) .async_data_slave_b_wptr_o (async_data_b_wptr),
    (* async *) .async_data_slave_b_rptr_i (async_data_b_rptr),
    (* async *) .async_data_slave_b_data_o (async_data_b_data),
    (* async *) .async_data_slave_ar_wptr_i(async_data_ar_wptr),
    (* async *) .async_data_slave_ar_rptr_o(async_data_ar_rptr),
    (* async *) .async_data_slave_ar_data_i(async_data_ar_data),
    (* async *) .async_data_slave_r_wptr_o (async_data_r_wptr),
    (* async *) .async_data_slave_r_rptr_i (async_data_r_rptr),
    (* async *) .async_data_slave_r_data_o (async_data_r_data)
  );

  // pragma translate_off
`ifndef SYNTHESIS
  assert property (@(posedge src_clk_i)
                   disable iff (~src_rst_ni) (src_isolate_i && !src_isolated_o) |=> src_isolate_i)
  else $error(1, "src isolate signal was de-asserted before isolation was complete!");
  assert property (@(posedge src_clk_i)
                   disable iff (~src_rst_ni) (!src_isolate_i && src_isolated_o) |=> !src_isolate_i)
  else $error(1, "src isolate signal was asserted before previous isolation was complete!");
  assert property (@(posedge dst_clk_i)
                   disable iff (~dst_rst_ni) (dst_isolate_i && !dst_isolated_o) |=> dst_isolate_i)
  else $error(1, "dst isolate signal was de-asserted before isolation was complete!");
  assert property (@(posedge dst_clk_i)
                   disable iff (~dst_rst_ni) (!dst_isolate_i && dst_isolated_o) |=> !dst_isolate_i)
  else $error(1, "dst isolate signal was asserted before previous isolation was complete!");
`endif
  // pragma translate_on

endmodule

`include "axi/assign.svh"
`include "axi/typedef.svh"

// interface wrapper
module axi_cdc_isolatable_intf #(
  parameter int unsigned AXI_ID_WIDTH          = 0,
  parameter int unsigned AXI_ADDR_WIDTH        = 0,
  parameter int unsigned AXI_DATA_WIDTH        = 0,
  parameter int unsigned AXI_USER_WIDTH        = 0,
  parameter bit          ATOP_SUPPORT          = 1'b1,
  /// Depth of the FIFO crossing the clock domain, given as 2**LOG_DEPTH.
  parameter int unsigned LOG_DEPTH             = 1,
  /// Number of synchronization registers to insert on the async pointers
  parameter int unsigned SYNC_STAGES           = 2,
  /// Gracefully terminate all incoming transactions in case of isolation by returning proper error
  /// responses.
  parameter bit          TERMINATE_TRANSACTION = 1'b0
) (
  // slave side - clocked by `src_clk_i`
  input  logic          src_clk_i,
  input  logic          src_rst_ni,
  input  logic          src_isolate_i,
  output logic          src_isolated_o,
         AXI_BUS.Slave  src,
  // master side - clocked by `dst_clk_i`
  input  logic          dst_clk_i,
  input  logic          dst_rst_ni,
  input  logic          dst_isolate_i,
  output logic          dst_isolated_o,
         AXI_BUS.Master dst
);

  typedef logic [AXI_ID_WIDTH-1:0] id_t;
  typedef logic [AXI_ADDR_WIDTH-1:0] addr_t;
  typedef logic [AXI_DATA_WIDTH-1:0] data_t;
  typedef logic [AXI_DATA_WIDTH/8-1:0] strb_t;
  typedef logic [AXI_USER_WIDTH-1:0] user_t;
  `AXI_TYPEDEF_AW_CHAN_T(aw_chan_t, addr_t, id_t, user_t)
  `AXI_TYPEDEF_W_CHAN_T(w_chan_t, data_t, strb_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T(b_chan_t, id_t, user_t)
  `AXI_TYPEDEF_AR_CHAN_T(ar_chan_t, addr_t, id_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(r_chan_t, data_t, id_t, user_t)
  `AXI_TYPEDEF_REQ_T(req_t, aw_chan_t, w_chan_t, ar_chan_t)
  `AXI_TYPEDEF_RESP_T(resp_t, b_chan_t, r_chan_t)

  req_t src_req, dst_req;
  resp_t src_resp, dst_resp;

  `AXI_ASSIGN_TO_REQ(src_req, src)
  `AXI_ASSIGN_FROM_RESP(src, src_resp)

  `AXI_ASSIGN_FROM_REQ(dst, dst_req)
  `AXI_ASSIGN_TO_RESP(dst_resp, dst)

  axi_cdc_isolatable #(
    .AxiAddrWidth        (AXI_ADDR_WIDTH),
    .AxiDataWidth        (AXI_DATA_WIDTH),
    .AxiIdWidth          (AXI_ID_WIDTH),
    .AxiUserWidth        (AXI_USER_WIDTH),
    .AtopSupport         (ATOP_SUPPORT),
    .axi_req_t           (req_t),
    .axi_resp_t          (resp_t),
    .LogDepth            (LOG_DEPTH),
    .SyncStages          (SYNC_STAGES),
    .TerminateTransaction(TERMINATE_TRANSACTION)
  ) i_axi_cdc (
    .src_clk_i,
    .src_rst_ni,
    .src_isolate_i,
    .src_isolated_o,
    .src_req_i (src_req),
    .src_resp_o(src_resp),
    .dst_clk_i,
    .dst_rst_ni,
    .dst_isolate_i,
    .dst_isolated_o,
    .dst_req_o (dst_req),
    .dst_resp_i(dst_resp)
  );

endmodule

module axi_lite_cdc_isolatable_intf #(
  parameter int unsigned AXI_ADDR_WIDTH        = 0,
  parameter int unsigned AXI_DATA_WIDTH        = 0,
  /// Depth of the FIFO crossing the clock domain, given as 2**LOG_DEPTH.
  parameter int unsigned LOG_DEPTH             = 1,
  /// Number of synchronization registers to insert on the async pointers
  parameter int unsigned SYNC_STAGES           = 2,
  /// Gracefully terminate all incoming transactions in case of isolation by returning proper error
  /// responses.
  parameter bit          TERMINATE_TRANSACTION = 1'b0
) (
  // slave side - clocked by `src_clk_i`
  input  logic           src_clk_i,
  input  logic           src_rst_ni,
  input  logic           src_isolate_i,
  output logic           src_isolated_o,
         AXI_LITE.Slave  src,
  // master side - clocked by `dst_clk_i`
  input  logic           dst_clk_i,
  input  logic           dst_rst_ni,
  input  logic           dst_isolate_i,
  output logic           dst_isolated_o,
         AXI_LITE.Master dst
);

  typedef logic [AXI_ADDR_WIDTH-1:0] addr_t;
  typedef logic [AXI_DATA_WIDTH-1:0] data_t;
  typedef logic [AXI_DATA_WIDTH/8-1:0] strb_t;
  `AXI_LITE_TYPEDEF_AW_CHAN_T(aw_chan_t, addr_t)
  `AXI_LITE_TYPEDEF_W_CHAN_T(w_chan_t, data_t, strb_t)
  `AXI_LITE_TYPEDEF_B_CHAN_T(b_chan_t)
  `AXI_LITE_TYPEDEF_AR_CHAN_T(ar_chan_t, addr_t)
  `AXI_LITE_TYPEDEF_R_CHAN_T(r_chan_t, data_t)
  `AXI_LITE_TYPEDEF_REQ_T(req_t, aw_chan_t, w_chan_t, ar_chan_t)
  `AXI_LITE_TYPEDEF_RESP_T(resp_t, b_chan_t, r_chan_t)

  req_t src_req, dst_req;
  resp_t src_resp, dst_resp;

  `AXI_LITE_ASSIGN_TO_REQ(src_req, src)
  `AXI_LITE_ASSIGN_FROM_RESP(src, src_resp)

  `AXI_LITE_ASSIGN_FROM_REQ(dst, dst_req)
  `AXI_LITE_ASSIGN_TO_RESP(dst_resp, dst)

  axi_cdc_isolatable #(
    .AxiAddrWidth        (AXI_ADDR_WIDTH),
    .AxiDataWidth        (AXI_DATA_WIDTH),
    .AtopSupport         (1'b0),
    .axi_req_t           (req_t),
    .axi_resp_t          (resp_t),
    .LogDepth            (LOG_DEPTH),
    .SyncStages          (SYNC_STAGES),
    .TerminateTransaction(TERMINATE_TRANSACTION)
  ) i_axi_cdc (
    .src_clk_i,
    .src_rst_ni,
    .src_isolate_i,
    .src_isolated_o,
    .src_req_i (src_req),
    .src_resp_o(src_resp),
    .dst_clk_i,
    .dst_rst_ni,
    .dst_isolate_i,
    .dst_isolated_o,
    .dst_req_o (dst_req),
    .dst_resp_i(dst_resp)
  );

endmodule
