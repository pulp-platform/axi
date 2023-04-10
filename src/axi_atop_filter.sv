// Copyright 2018 ETH Zurich and University of Bologna.
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
// - Wolfgang Roenninger <wroennin@iis.ee.ethz.ch>

/// Filter atomic operations (ATOPs) in a protocol-compliant manner.
///
/// This module filters atomic operations (ATOPs), i.e., write transactions that have a non-zero
/// `aw_atop` value, from its `sbr` to its `mgr` port. This module guarantees that:
///
/// 1) `aw_atop` is always zero on the `mgr` port;
///
/// 2) write transactions with non-zero `aw_atop` on the `sbr` port are handled in conformance with
///    the AXI standard by replying to such write transactions with the proper B and R responses.
///    The response code on atomic operations that reach this module is always SLVERR
///    (implementation-specific, not defined in the AXI standard).
///
/// ## Intended usage
/// This module is intended to be placed between managers that may issue ATOPs and subordinates that do not
/// support ATOPs. That way, this module ensures that the AXI protocol remains in a defined state on
/// systems with mixed ATOP capabilities.
///
/// ## Specification reminder
/// The AXI standard specifies that there may be no ordering requirements between different atomic
/// bursts (i.e., a burst started by an AW with ATOP other than 0) and none between atomic bursts
/// and non-atomic bursts [E2.1.4]. That is, **an atomic burst may never have the same ID as any
/// other write or read burst that is in-flight at the same time**.
module axi_atop_filter #(
  /// AXI ID width
  parameter int unsigned IdWidth = 0,
  /// Maximum number of in-flight AXI write transactions
  parameter int unsigned MaxWriteTxns = 0,
  /// AXI request type
  parameter type axi_req_t = logic,
  /// AXI response type
  parameter type axi_rsp_t = logic
) (
  /// Rising-edge clock of both ports
  input  logic     clk_i,
  /// Asynchronous reset, active low
  input  logic     rst_ni,
  /// Subordinate port request
  input  axi_req_t sbr_req_i,
  /// Subordinate port response
  output axi_rsp_t sbr_rsp_o,
  /// Manager port request
  output axi_req_t mgr_req_o,
  /// Manager port response
  input  axi_rsp_t mgr_rsp_i
);

  // Minimum counter width is 2 to detect underflows.
  localparam int unsigned COUNTER_WIDTH = (MaxWriteTxns == 1) ? 2 : $clog2(MaxWriteTxns+1);
  typedef struct packed {
    logic                     underflow;
    logic [COUNTER_WIDTH-1:0] cnt;
  } cnt_t;
  cnt_t   w_cnt_d, w_cnt_q;

  typedef enum logic [2:0] {
    W_FEEDTHROUGH, BLOCK_AW, ABSORB_W, HOLD_B, INJECT_B, WAIT_R
  } w_state_e;
  w_state_e   w_state_d, w_state_q;

  typedef enum logic [1:0] { R_FEEDTHROUGH, INJECT_R, R_HOLD } r_state_e;
  r_state_e   r_state_d, r_state_q;

  typedef logic [IdWidth-1:0] id_t;
  id_t  id_d, id_q;

  typedef logic [7:0] len_t;
  len_t   r_beats_d,  r_beats_q;

  typedef struct packed {
    len_t len;
  } r_resp_cmd_t;
  r_resp_cmd_t  r_resp_cmd_push, r_resp_cmd_pop;

  logic aw_without_complete_w_downstream,
        complete_w_without_aw_downstream,
        r_resp_cmd_push_valid,  r_resp_cmd_push_ready,
        r_resp_cmd_pop_valid,   r_resp_cmd_pop_ready;

  // An AW without a complete W burst is in-flight downstream if the W counter is > 0 and not
  // underflowed.
  assign aw_without_complete_w_downstream = !w_cnt_q.underflow && (w_cnt_q.cnt > 0);
  // A complete W burst without AW is in-flight downstream if the W counter is -1.
  assign complete_w_without_aw_downstream = w_cnt_q.underflow && &(w_cnt_q.cnt);

  // Manage AW, W, and B channels.
  always_comb begin
    // Defaults:
    // Disable AW and W handshakes.
    mgr_req_o.aw_valid = 1'b0;
    sbr_rsp_o.aw_ready = 1'b0;
    mgr_req_o.w_valid  = 1'b0;
    sbr_rsp_o.w_ready  = 1'b0;
    // Feed write responses through.
    mgr_req_o.b_ready  = sbr_req_i.b_ready;
    sbr_rsp_o.b_valid  = mgr_rsp_i.b_valid;
    sbr_rsp_o.b        = mgr_rsp_i.b;
    // Keep ID stored for B and R response.
    id_d = id_q;
    // Do not push R response commands.
    r_resp_cmd_push_valid = 1'b0;
    // Keep the current state.
    w_state_d = w_state_q;

    unique case (w_state_q)
      W_FEEDTHROUGH: begin
        // Feed AW channel through if the maximum number of outstanding bursts is not reached.
        if (complete_w_without_aw_downstream || (w_cnt_q.cnt < MaxWriteTxns)) begin
          mgr_req_o.aw_valid = sbr_req_i.aw_valid;
          sbr_rsp_o.aw_ready = mgr_rsp_i.aw_ready;
        end
        // Feed W channel through if ..
        if (aw_without_complete_w_downstream // .. downstream is missing W bursts ..
            // .. or a new non-ATOP AW is being applied and there is not already a complete W burst
            // downstream (to prevent underflows of w_cnt).
            || ((sbr_req_i.aw_valid && sbr_req_i.aw.atop[5:4] == axi_pkg::ATOP_NONE)
                && !complete_w_without_aw_downstream)
        ) begin
          mgr_req_o.w_valid = sbr_req_i.w_valid;
          sbr_rsp_o.w_ready = mgr_rsp_i.w_ready;
        end
        // Filter out AWs that are atomic operations.
        if (sbr_req_i.aw_valid && sbr_req_i.aw.atop[5:4] != axi_pkg::ATOP_NONE) begin
          mgr_req_o.aw_valid = 1'b0; // Do not let AW pass to manager port.
          sbr_rsp_o.aw_ready = 1'b1; // Absorb AW on subordinate port.
          id_d = sbr_req_i.aw.id; // Store ID for B response.
          // Some atomic operations require a response on the R channel.
          if (sbr_req_i.aw.atop[axi_pkg::ATOP_R_RESP]) begin
            // Push R response command.  We do not have to wait for the ready of the register
            // because we know it is ready: we are its only manager and will wait for the register to
            // be emptied before going back to the `W_FEEDTHROUGH` state.
            r_resp_cmd_push_valid = 1'b1;
          end
          // If downstream is missing W beats, block the AW channel and let the W bursts complete.
          if (aw_without_complete_w_downstream) begin
            w_state_d = BLOCK_AW;
          // If downstream is not missing W beats, absorb the W beats for this atomic AW.
          end else begin
            mgr_req_o.w_valid  = 1'b0; // Do not let W beats pass to manager port.
            sbr_rsp_o.w_ready = 1'b1; // Absorb W beats on subordinate port.
            if (sbr_req_i.w_valid && sbr_req_i.w.last) begin
              // If the W beat is valid and the last, proceed by injecting the B response.
              // However, if there is a non-handshaked B on our response port, we must let that
              // complete first.
              if (sbr_rsp_o.b_valid && !sbr_req_i.b_ready) begin
                w_state_d = HOLD_B;
              end else begin
                w_state_d = INJECT_B;
              end
            end else begin
              // Otherwise continue with absorbing W beats.
              w_state_d = ABSORB_W;
            end
          end
        end
      end

      BLOCK_AW: begin
        // Feed W channel through to let outstanding bursts complete.
        if (aw_without_complete_w_downstream) begin
          mgr_req_o.w_valid = sbr_req_i.w_valid;
          sbr_rsp_o.w_ready = mgr_rsp_i.w_ready;
        end else begin
          // If there are no more outstanding W bursts, start absorbing the next W burst.
          sbr_rsp_o.w_ready = 1'b1;
          if (sbr_req_i.w_valid && sbr_req_i.w.last) begin
            // If the W beat is valid and the last, proceed by injecting the B response.
            if (sbr_rsp_o.b_valid && !sbr_req_i.b_ready) begin
              w_state_d = HOLD_B;
            end else begin
              w_state_d = INJECT_B;
            end
          end else begin
            // Otherwise continue with absorbing W beats.
            w_state_d = ABSORB_W;
          end
        end
      end

      ABSORB_W: begin
        // Absorb all W beats of the current burst.
        sbr_rsp_o.w_ready = 1'b1;
        if (sbr_req_i.w_valid && sbr_req_i.w.last) begin
          if (sbr_rsp_o.b_valid && !sbr_req_i.b_ready) begin
            w_state_d = HOLD_B;
          end else begin
            w_state_d = INJECT_B;
          end
        end
      end

      HOLD_B: begin
        // Proceed with injection of B response upon handshake.
        if (sbr_rsp_o.b_valid && sbr_req_i.b_ready) begin
          w_state_d = INJECT_B;
        end
      end

      INJECT_B: begin
        // Pause forwarding of B response.
        mgr_req_o.b_ready = 1'b0;
        // Inject error response instead.  Since the B channel has an ID and the atomic burst we are
        // replying to is guaranteed to be the only burst with this ID in flight, we do not have to
        // observe any ordering and can immediately inject on the B channel.
        sbr_rsp_o.b = '0;
        sbr_rsp_o.b.id = id_q;
        sbr_rsp_o.b.resp = axi_pkg::RESP_SLVERR;
        sbr_rsp_o.b_valid = 1'b1;
        if (sbr_req_i.b_ready) begin
          // If not all beats of the R response have been injected, wait for them. Otherwise, return
          // to `W_FEEDTHROUGH`.
          if (r_resp_cmd_pop_valid && !r_resp_cmd_pop_ready) begin
            w_state_d = WAIT_R;
          end else begin
            w_state_d = W_FEEDTHROUGH;
          end
        end
      end

      WAIT_R: begin
        // Wait with returning to `W_FEEDTHROUGH` until all beats of the R response have been
        // injected.
        if (!r_resp_cmd_pop_valid) begin
          w_state_d = W_FEEDTHROUGH;
        end
      end

      default: w_state_d = W_FEEDTHROUGH;
    endcase
  end
  // Connect signals on AW and W channel that are not managed by the control FSM from subordinate port to
  // manager port.
  // Feed-through of the AW and W vectors, make sure that downstream aw.atop is always zero
  always_comb begin
    // overwrite the atop signal
    mgr_req_o.aw      = sbr_req_i.aw;
    mgr_req_o.aw.atop = '0;
  end
  assign mgr_req_o.w = sbr_req_i.w;

  // Manage R channel.
  always_comb begin
    // Defaults:
    // Feed read responses through.
    sbr_rsp_o.r       = mgr_rsp_i.r;
    sbr_rsp_o.r_valid = mgr_rsp_i.r_valid;
    mgr_req_o.r_ready = sbr_req_i.r_ready;
    // Do not pop R response command.
    r_resp_cmd_pop_ready = 1'b0;
    // Keep the current value of the beats counter.
    r_beats_d = r_beats_q;
    // Keep the current state.
    r_state_d = r_state_q;

    unique case (r_state_q)
      R_FEEDTHROUGH: begin
        if (mgr_rsp_i.r_valid && !sbr_req_i.r_ready) begin
          r_state_d = R_HOLD;
        end else if (r_resp_cmd_pop_valid) begin
          // Upon a command to inject an R response, immediately proceed with doing so because there
          // are no ordering requirements with other bursts that may be ongoing on the R channel at
          // this moment.
          r_beats_d = r_resp_cmd_pop.len;
          r_state_d = INJECT_R;
        end
      end

      INJECT_R: begin
        mgr_req_o.r_ready = 1'b0;
        sbr_rsp_o.r       = '0;
        sbr_rsp_o.r.id    = id_q;
        sbr_rsp_o.r.resp  = axi_pkg::RESP_SLVERR;
        sbr_rsp_o.r.last  = (r_beats_q == '0);
        sbr_rsp_o.r_valid = 1'b1;
        if (sbr_req_i.r_ready) begin
          if (sbr_rsp_o.r.last) begin
            r_resp_cmd_pop_ready = 1'b1;
            r_state_d = R_FEEDTHROUGH;
          end else begin
            r_beats_d -= 1;
          end
        end
      end

      R_HOLD: begin
        if (mgr_rsp_i.r_valid && sbr_req_i.r_ready) begin
          r_state_d = R_FEEDTHROUGH;
        end
      end

      default: r_state_d = R_FEEDTHROUGH;
    endcase
  end
  // Feed all signals on AR through.
  assign mgr_req_o.ar       = sbr_req_i.ar;
  assign mgr_req_o.ar_valid = sbr_req_i.ar_valid;
  assign sbr_rsp_o.ar_ready = mgr_rsp_i.ar_ready;

  // Keep track of outstanding downstream write bursts and responses.
  always_comb begin
    w_cnt_d = w_cnt_q;
    if (mgr_req_o.aw_valid && mgr_rsp_i.aw_ready) begin
      w_cnt_d.cnt += 1;
    end
    if (mgr_req_o.w_valid && mgr_rsp_i.w_ready && mgr_req_o.w.last) begin
      w_cnt_d.cnt -= 1;
    end
    if (w_cnt_q.underflow && (w_cnt_d.cnt == '0)) begin
      w_cnt_d.underflow = 1'b0;
    end else if (w_cnt_q.cnt == '0 && &(w_cnt_d.cnt)) begin
      w_cnt_d.underflow = 1'b1;
    end
  end

  always_ff @(posedge clk_i, negedge rst_ni) begin
    if (!rst_ni) begin
      id_q <= '0;
      r_beats_q <= '0;
      r_state_q <= R_FEEDTHROUGH;
      w_cnt_q <= '{default: '0};
      w_state_q <= W_FEEDTHROUGH;
    end else begin
      id_q <= id_d;
      r_beats_q <= r_beats_d;
      r_state_q <= r_state_d;
      w_cnt_q <= w_cnt_d;
      w_state_q <= w_state_d;
    end
  end

  stream_register #(
    .T(r_resp_cmd_t)
  ) r_resp_cmd (
    .clk_i      (clk_i),
    .rst_ni     (rst_ni),
    .clr_i      (1'b0),
    .testmode_i (1'b0),
    .valid_i    (r_resp_cmd_push_valid),
    .ready_o    (r_resp_cmd_push_ready),
    .data_i     (r_resp_cmd_push),
    .valid_o    (r_resp_cmd_pop_valid),
    .ready_i    (r_resp_cmd_pop_ready),
    .data_o     (r_resp_cmd_pop)
  );
  assign r_resp_cmd_push.len = sbr_req_i.aw.len;

// pragma translate_off
`ifndef VERILATOR
  initial begin: p_assertions
    assert (IdWidth >= 1) else $fatal(1, "AXI ID width must be at least 1!");
    assert (MaxWriteTxns >= 1)
      else $fatal(1, "Maximum number of outstanding write transactions must be at least 1!");
  end
`endif
// pragma translate_on
endmodule

`include "axi/assign.svh"
`include "axi/typedef.svh"

/// Interface variant of [`axi_atop_filter`](module.axi_atop_filter).
module axi_atop_filter_intf #(
  /// AXI ID width
  parameter int unsigned AXI_ID_WIDTH   = 0,
  /// AXI address width
  parameter int unsigned AXI_ADDR_WIDTH = 0,
  /// AXI data width
  parameter int unsigned AXI_DATA_WIDTH = 0,
  /// AXI user signal width
  parameter int unsigned AXI_USER_WIDTH = 0,
  /// Maximum number of in-flight AXI write transactions
  parameter int unsigned AXI_MAX_WRITE_TXNS = 0
) (
  /// Rising-edge clock of both ports
  input  logic    clk_i,
  /// Asynchronous reset, active low
  input  logic    rst_ni,
  /// Subordinate interface port
  AXI_BUS.Subordinate   sbr,
  /// Manager interface port
  AXI_BUS.Manager  mgr
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
  `AXI_TYPEDEF_REQ_T(axi_req_t, aw_chan_t, w_chan_t, ar_chan_t)
  `AXI_TYPEDEF_RSP_T(axi_rsp_t, b_chan_t, r_chan_t)

  axi_req_t  sbr_req,  mgr_req;
  axi_rsp_t sbr_rsp, mgr_rsp;

  `AXI_ASSIGN_TO_REQ(sbr_req, sbr)
  `AXI_ASSIGN_FROM_RSP(sbr, sbr_rsp)

  `AXI_ASSIGN_FROM_REQ(mgr, mgr_req)
  `AXI_ASSIGN_TO_RSP(mgr_rsp, mgr)

  axi_atop_filter #(
    .IdWidth      ( AXI_ID_WIDTH       ),
  // Maximum number of AXI write bursts outstanding at the same time
    .MaxWriteTxns ( AXI_MAX_WRITE_TXNS ),
  // AXI request & response type
    .axi_req_t    ( axi_req_t          ),
    .axi_rsp_t    ( axi_rsp_t          )
  ) i_axi_atop_filter (
    .clk_i,
    .rst_ni,
    .sbr_req_i ( sbr_req ),
    .sbr_rsp_o ( sbr_rsp ),
    .mgr_req_o ( mgr_req ),
    .mgr_rsp_i ( mgr_rsp )
  );
// pragma translate_off
`ifndef VERILATOR
  initial begin: p_assertions
    assert (AXI_ADDR_WIDTH >= 1) else $fatal(1, "AXI ADDR width must be at least 1!");
    assert (AXI_DATA_WIDTH >= 1) else $fatal(1, "AXI DATA width must be at least 1!");
    assert (AXI_USER_WIDTH >= 1) else $fatal(1, "AXI USER width must be at least 1!");
  end
`endif
// pragma translate_on
endmodule
