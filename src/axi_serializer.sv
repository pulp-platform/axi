// Copyright (c) 2020 ETH Zurich and University of Bologna.
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

`include "common_cells/registers.svh"

/// Serialize all AXI transactions to a single ID (zero).
///
/// This module contains one queue with subordinate port IDs for the read direction and one for the write
/// direction.  These queues are used to reconstruct the ID of responses at the subordinate port.  The
/// depth of each queue is defined by `MaxReadTxns` and `MaxWriteTxns`, respectively.
module axi_serializer #(
  /// Maximum number of in flight read transactions.
  parameter int unsigned MaxReadTxns  = 32'd0,
  /// Maximum number of in flight write transactions.
  parameter int unsigned MaxWriteTxns = 32'd0,
  /// AXI4+ATOP ID width.
  parameter int unsigned IdWidth      = 32'd0,
  /// AXI4+ATOP request struct definition.
  parameter type         axi_req_t    = logic,
  /// AXI4+ATOP response struct definition.
  parameter type         axi_rsp_t    = logic
) (
  /// Clock
  input  logic     clk_i,
  /// Asynchronous reset, active low
  input  logic     rst_ni,
  /// Subordinate port request
  input  axi_req_t sbr_port_req_i,
  /// Subordinate port response
  output axi_rsp_t sbr_port_rsp_o,
  /// Manager port request
  output axi_req_t mgr_port_req_o,
  /// Manager port response
  input  axi_rsp_t mgr_port_rsp_i
);

  typedef logic [IdWidth-1:0] id_t;
  typedef enum logic [1:0] {
    AtopIdle    = 2'b00,
    AtopDrain   = 2'b01,
    AtopExecute = 2'b10
  } state_e;

  logic   rd_fifo_full, rd_fifo_empty, rd_fifo_push, rd_fifo_pop,
          wr_fifo_full, wr_fifo_empty, wr_fifo_push, wr_fifo_pop;
  id_t    b_id,
          r_id,         ar_id;
  state_e state_q,      state_d;

  always_comb begin
    // Default assignments
    state_d      = state_q;
    rd_fifo_push = 1'b0;
    wr_fifo_push = 1'b0;

    // Default, connect the channels
    mgr_port_req_o = sbr_port_req_i;
    sbr_port_rsp_o = mgr_port_rsp_i;

    // Serialize transactions -> tie downstream IDs to zero.
    mgr_port_req_o.aw.id = '0;
    mgr_port_req_o.ar.id = '0;

    // Reflect upstream ID in response.
    ar_id          = sbr_port_req_i.ar.id;
    sbr_port_rsp_o.b.id = b_id;
    sbr_port_rsp_o.r.id = r_id;

    // Default, cut the AW/AR handshaking
    mgr_port_req_o.ar_valid = 1'b0;
    sbr_port_rsp_o.ar_ready = 1'b0;
    mgr_port_req_o.aw_valid = 1'b0;
    sbr_port_rsp_o.aw_ready = 1'b0;

    unique case (state_q)
      AtopIdle, AtopExecute: begin

        // Wait until the ATOP response(s) have been sent back upstream.
        if (state_q == AtopExecute) begin
          if ((wr_fifo_empty && rd_fifo_empty) || (wr_fifo_pop && rd_fifo_pop) ||
              (wr_fifo_empty && rd_fifo_pop)   || (wr_fifo_pop && rd_fifo_empty)) begin
            state_d = AtopIdle;
          end
        end

        // This part lets new Transactions through, if no ATOP is underway or the last ATOP
        // response has been transmitted.
        if ((state_q == AtopIdle) || (state_d == AtopIdle)) begin
          // Gate AR handshake with ready output of Read FIFO.
          mgr_port_req_o.ar_valid = sbr_port_req_i.ar_valid & ~rd_fifo_full;
          sbr_port_rsp_o.ar_ready = mgr_port_rsp_i.ar_ready & ~rd_fifo_full;
          rd_fifo_push       = mgr_port_req_o.ar_valid & mgr_port_rsp_i.ar_ready;
          if (sbr_port_req_i.aw_valid) begin
            if (sbr_port_req_i.aw.atop[5:4] == axi_pkg::ATOP_NONE) begin
              // Normal operation
              // Gate AW handshake with ready output of Write FIFO.
              mgr_port_req_o.aw_valid = ~wr_fifo_full;
              sbr_port_rsp_o.aw_ready = mgr_port_rsp_i.aw_ready & ~wr_fifo_full;
              wr_fifo_push       = mgr_port_req_o.aw_valid  & mgr_port_rsp_i.aw_ready;
            end else begin
              // Atomic Operation received, go to drain state, when both channels are ready
              // Wait for finished or no AR beat
              if (!mgr_port_req_o.ar_valid || (mgr_port_req_o.ar_valid && mgr_port_rsp_i.ar_ready)) begin
                state_d = AtopDrain;
              end
            end
          end
        end
      end
      AtopDrain: begin
        // Send the ATOP AW when the last open transaction terminates
        if (wr_fifo_empty && rd_fifo_empty) begin
          mgr_port_req_o.aw_valid = 1'b1;
          sbr_port_rsp_o.aw_ready = mgr_port_rsp_i.aw_ready;
          wr_fifo_push       = mgr_port_rsp_i.aw_ready;
          if (sbr_port_req_i.aw.atop[axi_pkg::ATOP_R_RESP]) begin
            // Overwrite the read ID with the one from AW
            ar_id        = sbr_port_req_i.aw.id;
            rd_fifo_push = mgr_port_rsp_i.aw_ready;
          end
          if (mgr_port_rsp_i.aw_ready) begin
            state_d = AtopExecute;
          end
        end
      end
      default : /* do nothing */;
    endcase

    // Gate B handshake with empty flag output of Write FIFO.
    sbr_port_rsp_o.b_valid = mgr_port_rsp_i.b_valid & ~wr_fifo_empty;
    mgr_port_req_o.b_ready = sbr_port_req_i.b_ready & ~wr_fifo_empty;

    // Gate R handshake with empty flag output of Read FIFO.
    sbr_port_rsp_o.r_valid = mgr_port_rsp_i.r_valid & ~rd_fifo_empty;
    mgr_port_req_o.r_ready = sbr_port_req_i.r_ready & ~rd_fifo_empty;
  end

  fifo_v3 #(
    .FALL_THROUGH ( 1'b0        ), // No fall-through as response has to come a cycle later anyway
    .DEPTH        ( MaxReadTxns ),
    .dtype        ( id_t        )
  ) i_rd_id_fifo (
    .clk_i,
    .rst_ni,
    .flush_i    ( 1'b0          ),
    .testmode_i ( 1'b0          ),
    .data_i     ( ar_id         ),
    .push_i     ( rd_fifo_push  ),
    .full_o     ( rd_fifo_full  ),
    .data_o     ( r_id          ),
    .empty_o    ( rd_fifo_empty ),
    .pop_i      ( rd_fifo_pop   ),
    .usage_o    ( /*not used*/  )
  );
  // Assign as this condition is needed in FSM
  assign rd_fifo_pop = sbr_port_rsp_o.r_valid & sbr_port_req_i.r_ready & sbr_port_rsp_o.r.last;

  fifo_v3 #(
    .FALL_THROUGH ( 1'b0         ),
    .DEPTH        ( MaxWriteTxns ),
    .dtype        ( id_t         )
  ) i_wr_id_fifo (
    .clk_i,
    .rst_ni,
    .flush_i    ( 1'b0            ),
    .testmode_i ( 1'b0            ),
    .data_i     ( sbr_port_req_i.aw.id ),
    .push_i     ( wr_fifo_push    ),
    .full_o     ( wr_fifo_full    ),
    .data_o     ( b_id            ),
    .empty_o    ( wr_fifo_empty   ),
    .pop_i      ( wr_fifo_pop     ),
    .usage_o    ( /*not used*/    )
  );
  // Assign as this condition is needed in FSM
  assign wr_fifo_pop = sbr_port_rsp_o.b_valid & sbr_port_req_i.b_ready;

  `FFARN(state_q, state_d, AtopIdle, clk_i, rst_ni)

// pragma translate_off
`ifndef VERILATOR
  initial begin: p_assertions
    assert (IdWidth    >= 1) else $fatal(1, "AXI ID width must be at least 1!");
    assert (MaxReadTxns   >= 1)
      else $fatal(1, "Maximum number of read transactions must be >= 1!");
    assert (MaxWriteTxns  >= 1)
      else $fatal(1, "Maximum number of write transactions must be >= 1!");
  end
  default disable iff (~rst_ni);
  aw_lost : assert property( @(posedge clk_i)
      (sbr_port_req_i.aw_valid & sbr_port_rsp_o.aw_ready |-> mgr_port_req_o.aw_valid & mgr_port_rsp_i.aw_ready))
    else $error("AW beat lost.");
  w_lost  : assert property( @(posedge clk_i)
      (sbr_port_req_i.w_valid & sbr_port_rsp_o.w_ready |-> mgr_port_req_o.w_valid & mgr_port_rsp_i.w_ready))
    else $error("W beat lost.");
  b_lost  : assert property( @(posedge clk_i)
      (mgr_port_rsp_i.b_valid & mgr_port_req_o.b_ready |-> sbr_port_rsp_o.b_valid & sbr_port_req_i.b_ready))
    else $error("B beat lost.");
  ar_lost : assert property( @(posedge clk_i)
      (sbr_port_req_i.ar_valid & sbr_port_rsp_o.ar_ready |-> mgr_port_req_o.ar_valid & mgr_port_rsp_i.ar_ready))
    else $error("AR beat lost.");
  r_lost :  assert property( @(posedge clk_i)
      (mgr_port_rsp_i.r_valid & mgr_port_req_o.r_ready |-> sbr_port_rsp_o.r_valid & sbr_port_req_i.r_ready))
    else $error("R beat lost.");
`endif
// pragma translate_on
endmodule

`include "axi/typedef.svh"
`include "axi/assign.svh"
/// Serialize all AXI transactions to a single ID (zero), interface version.
module axi_serializer_intf #(
  /// AXI4+ATOP ID width.
  parameter int unsigned AXI_ID_WIDTH   = 32'd0,
  /// AXI4+ATOP address width.
  parameter int unsigned AXI_ADDR_WIDTH = 32'd0,
  /// AXI4+ATOP data width.
  parameter int unsigned AXI_DATA_WIDTH = 32'd0,
  /// AXI4+ATOP user width.
  parameter int unsigned AXI_USER_WIDTH = 32'd0,
  /// Maximum number of in flight read transactions.
  parameter int unsigned MAX_READ_TXNS  = 32'd0,
  /// Maximum number of in flight write transactions.
  parameter int unsigned MAX_WRITE_TXNS = 32'd0
) (
  /// Clock
  input  logic    clk_i,
  /// Asynchronous reset, active low
  input  logic    rst_ni,
  /// AXI4+ATOP Subordinate modport
  AXI_BUS.Subordinate   sbr,
  /// AXI4+ATOP Manager modport
  AXI_BUS.Manager  mgr
);

  typedef logic [AXI_ID_WIDTH    -1:0] id_t;
  typedef logic [AXI_ADDR_WIDTH  -1:0] addr_t;
  typedef logic [AXI_DATA_WIDTH  -1:0] data_t;
  typedef logic [AXI_DATA_WIDTH/8-1:0] strb_t;
  typedef logic [AXI_USER_WIDTH  -1:0] user_t;
  `AXI_TYPEDEF_AW_CHAN_T(aw_chan_t, addr_t, id_t, user_t)
  `AXI_TYPEDEF_W_CHAN_T(w_chan_t, data_t, strb_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T(b_chan_t, id_t, user_t)
  `AXI_TYPEDEF_AR_CHAN_T(ar_chan_t, addr_t, id_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(r_chan_t, data_t, id_t, user_t)
  `AXI_TYPEDEF_REQ_T(axi_req_t, aw_chan_t, w_chan_t, ar_chan_t)
  `AXI_TYPEDEF_RSP_T(axi_rsp_t, b_chan_t, r_chan_t)
  axi_req_t sbr_req,  mgr_req;
  axi_rsp_t sbr_rsp, mgr_rsp;
  `AXI_ASSIGN_TO_REQ(sbr_req, sbr)
  `AXI_ASSIGN_FROM_RSP(sbr, sbr_rsp)
  `AXI_ASSIGN_FROM_REQ(mgr, mgr_req)
  `AXI_ASSIGN_TO_RSP(mgr_rsp, mgr)

  axi_serializer #(
    .MaxReadTxns  ( MAX_READ_TXNS  ),
    .MaxWriteTxns ( MAX_WRITE_TXNS ),
    .IdWidth      ( AXI_ID_WIDTH   ),
    .axi_req_t    ( axi_req_t      ),
    .axi_rsp_t    ( axi_rsp_t      )
  ) i_axi_serializer (
    .clk_i,
    .rst_ni,
    .sbr_port_req_i ( sbr_req ),
    .sbr_port_rsp_o ( sbr_rsp ),
    .mgr_port_req_o ( mgr_req ),
    .mgr_port_rsp_i ( mgr_rsp )
  );

// pragma translate_off
`ifndef VERILATOR
  initial begin: p_assertions
    assert (AXI_ADDR_WIDTH  >= 1) else $fatal(1, "AXI address width must be at least 1!");
    assert (AXI_DATA_WIDTH  >= 1) else $fatal(1, "AXI data width must be at least 1!");
    assert (AXI_ID_WIDTH    >= 1) else $fatal(1, "AXI ID width must be at least 1!");
    assert (AXI_USER_WIDTH  >= 1) else $fatal(1, "AXI user width must be at least 1!");
    assert (MAX_READ_TXNS   >= 1)
      else $fatal(1, "Maximum number of read transactions must be >= 1!");
    assert (MAX_WRITE_TXNS  >= 1)
      else $fatal(1, "Maximum number of write transactions must be >= 1!");
  end
`endif
// pragma translate_on
endmodule
