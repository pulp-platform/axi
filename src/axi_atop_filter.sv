// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// AXI ATOP Filter: This module filters atomic operations (ATOPs), i.e., write transactions that
// have a non-zero `aw_atop` value, from its `slv` to its `mst` port. This module guarantees that:
//
// 1) `aw_atop` is always zero on the `mst` port mst_req_o;
//
// 2) write transactions with non-zero `aw_atop` on the `slv` port are handled in conformance with
//    the AXI standard by replying to such write transactions with the proper B and R responses. The
//    response code on atomic operations that reach this module is always SLVERR
//    (implementation-specific, not defined in the AXI standard).
//
// This module is intended to be placed between masters that may issue ATOPs and slaves that do not
// support ATOPs. That way, this module ensures that the AXI protocol remains in a defined state on
// systems with mixed ATOP capabilities.
//
// Interface note:
// The AXI standard specifies that there may be no ordering requirements between different atomic
// bursts (i.e., a burst started by an AW with ATOP other than 0) and none between atomic bursts and
// non-atomic bursts [E2.1.4]. That is, an atomic burst may never have the same ID as any other
// write or read burst that is ongoing at the same time.

module axi_atop_filter #(
  parameter int unsigned AXI_ID_WIDTH = 0,  // Synopsys DC requires a default value for parameters.
  // Maximum number of AXI write bursts outstanding at the same time
  parameter int unsigned AXI_MAX_WRITE_TXNS = 0,
  // AXI request & response type
  parameter type req_t  = logic,
  parameter type resp_t = logic
) (
  input  logic    clk_i,
  input  logic    rst_ni,
  // slave port
  input  req_t  slv_req_i,
  output resp_t slv_resp_o,
  // master port
  output req_t  mst_req_o,
  input  resp_t mst_resp_i
);

  typedef logic [$clog2(AXI_MAX_WRITE_TXNS+1)-1:0] cnt_t;
  cnt_t   w_cnt_d, w_cnt_q;

  typedef enum logic [2:0] { W_FEEDTHROUGH, BLOCK_AW, ABSORB_W, INJECT_B, WAIT_R } w_state_t;
  w_state_t   w_state_d, w_state_q;

  typedef enum logic { R_FEEDTHROUGH, INJECT_R } r_state_t;
  r_state_t   r_state_d, r_state_q;

  typedef logic [AXI_ID_WIDTH-1:0] id_t;
  id_t  id_d, id_q;

  typedef logic [7:0] len_t;
  len_t   r_beats_d,  r_beats_q;

  typedef struct packed {
    len_t len;
  } r_resp_cmd_t;
  r_resp_cmd_t  r_resp_cmd_push, r_resp_cmd_pop;

  logic r_resp_cmd_push_valid,  r_resp_cmd_push_ready,
        r_resp_cmd_pop_valid,   r_resp_cmd_pop_ready;

  // During simulation with questa the following error was encountered:
  // > unhandled IDL type ../../src/vlog/vsymtab.c(5443) <net_type>.
  // > Please contact Questa support at http://supportnet.mentor.com
  // It has something to do with directly assigning an input port to an
  // output port in an always comb block.
  // (eg: `mst_req_o.aw = slv_req_i.aw;`)
  // Adding these assignments fixed the problem.
  req_t  slv_req,  mst_req;
  resp_t slv_resp, mst_resp;
  assign slv_req    = slv_req_i;
  assign slv_resp_o = slv_resp;
  assign mst_req_o  = mst_req;
  assign mst_resp   = mst_resp_i;


  // Manage AW, W, and B channels.
  always_comb begin
    // Defaults:
    mst_req.aw      = slv_req.aw;
    mst_req.aw.atop = '0;
    mst_req.w       = slv_req.w;

    // Disable AW and W handshakes.
    mst_req.aw_valid  = 1'b0;
    slv_resp.aw_ready = 1'b0;
    mst_req.w_valid   = 1'b0;
    slv_resp.w_ready  = 1'b0;
    // Feed write responses through.
    mst_req.b_ready   = slv_req.b_ready;
    slv_resp.b_valid  = mst_resp.b_valid;
    slv_resp.b        = mst_resp.b;
    // Keep ID stored for B and R response.
    id_d = id_q;
    // Do not push R response commands.
    r_resp_cmd_push_valid = 1'b0;
    // Keep the current state.
    w_state_d = w_state_q;

    unique case (w_state_q)
      W_FEEDTHROUGH: begin
        // Feed AW channel through if the maximum number of outstanding bursts is not reached.
        if (w_cnt_q < AXI_MAX_WRITE_TXNS) begin
          mst_req.aw_valid  = slv_req.aw_valid;   //
          slv_resp.aw_ready = mst_resp.aw_ready;  //
        end
        // Feed W channel through if at least one AW request is outstanding.  This does not allow
        // W beats before the corresponding AW because we need to know the `atop` of an AW to decide
        // what to do with the W beats.
        if (w_cnt_q > 0) begin
          mst_req.w_valid  = slv_req.w_valid;
          slv_resp.w_ready = mst_resp.w_ready;
        end
        // Filter out AWs that are atomic operations.
        if (slv_req.aw_valid && slv_req.aw.atop[5:4] != axi_pkg::ATOP_NONE) begin
          mst_req.aw_valid  = 1'b0; // Do not let AW pass to master port.
          slv_resp.aw_ready = 1'b1; // Absorb AW on slave port.
          id_d = slv_req.aw.id; // Store ID for B response.
          // All atomic operations except atomic stores require a response on the R channel.
          if (slv_req.aw.atop[5:4] != axi_pkg::ATOP_ATOMICSTORE) begin
            // Push R response command.  We do not have to wait for the ready of the register
            // because we know it is ready: we are its only master and will wait for the register to
            // be emptied before going back to the `W_FEEDTHROUGH` state.
            r_resp_cmd_push_valid = 1'b1;
          end
          // If there are outstanding W bursts, block the AW channel and let the W bursts complete.
          if (w_cnt_q > 0) begin
            w_state_d = BLOCK_AW;
          // If there are no outstanding W bursts, absorb the W beats for this atomic AW.
          end else begin
            mst_req.w_valid  = 1'b0; // Do not let W beats pass to master port.
            slv_resp.w_ready = 1'b1; // Absorb W beats on slave port.
            if (slv_req.w_valid && slv_req.w.last) begin
              // If the W beat is valid and the last, proceed by injecting the B response.
              w_state_d = INJECT_B;
            end else begin
              // Otherwise continue with absorbing W beats.
              w_state_d = ABSORB_W;
            end
          end
        end
      end

      BLOCK_AW: begin
        // Feed W channel through to let outstanding bursts complete.
        if (w_cnt_q > 0) begin
          mst_req.w_valid  = slv_req.w_valid;
          slv_resp.w_ready = mst_resp.w_ready;
        end else begin
          // If there are no more outstanding W bursts, start absorbing the next W burst.
          slv_resp.w_ready   = 1'b1;
          if (slv_req.w_valid && slv_req.w.last) begin
            // If the W beat is valid and the last, proceed by injecting the B response.
            w_state_d = INJECT_B;
          end else begin
            // Otherwise continue with absorbing W beats.
            w_state_d = ABSORB_W;
          end
        end
      end

      ABSORB_W: begin
        // Absorb all W beats of the current burst.
        slv_resp.w_ready = 1'b1;
        if (slv_req.w_valid && slv_req.w.last) begin
          w_state_d = INJECT_B;
        end
      end

      INJECT_B: begin
        // Pause forwarding of B response.
        mst_req.b_ready = 1'b0;
        // Inject error response instead.  Since the B channel has an ID and the atomic burst we are
        // replying to is guaranteed to be the only burst with this ID in flight, we do not have to
        // observe any ordering and can immediately inject on the B channel.
        slv_resp.b = '0;
        slv_resp.b.id = id_q;
        slv_resp.b.resp = axi_pkg::RESP_SLVERR;
        slv_resp.b_valid = 1'b1;
        if (slv_req.b_ready) begin
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

  // Manage R channel.
  always_comb begin
    // Defaults:
    // Feed all signals on AR through.
    mst_req.ar        = slv_req.ar;
    mst_req.ar_valid  = slv_req.ar_valid;
    slv_resp.ar_ready = mst_resp.ar_ready;
    // Feed read responses through.
    slv_resp.r       = mst_resp.r;
    slv_resp.r_valid = mst_resp.r_valid;
    mst_req.r_ready  = slv_req.r_ready;
    // Do not pop R response command.
    r_resp_cmd_pop_ready = 1'b0;
    // Keep the current value of the beats counter.
    r_beats_d = r_beats_q;
    // Keep the current state.
    r_state_d = r_state_q;

    unique case (r_state_q)
      R_FEEDTHROUGH: begin
        if (r_resp_cmd_pop_valid) begin
          // Upon a command to inject an R response, immediately proceed with doing so because there
          // are no ordering requirements with other bursts that may be ongoing on the R channel at
          // this moment.
          r_beats_d = r_resp_cmd_pop.len;
          r_state_d = INJECT_R;
        end
      end

      INJECT_R: begin
        mst_req.r_ready  = 1'b0;
        slv_resp.r       = '0;
        slv_resp.r.id    = id_q;
        slv_resp.r.resp  = axi_pkg::RESP_SLVERR;
        slv_resp.r.last  = (r_beats_q == '0);
        slv_resp.r_valid = 1'b1;
        if (slv_req.r_ready) begin
          if (slv_resp.r.last) begin
            r_resp_cmd_pop_ready = 1'b1;
            r_state_d = R_FEEDTHROUGH;
          end else begin
            r_beats_d -= 1;
          end
        end
      end

      default: begin
        r_state_d = R_FEEDTHROUGH;
      end
    endcase
  end

  // Keep track of outstanding downstream write bursts and responses.
  always_comb begin
    w_cnt_d = w_cnt_q;
    if (mst_req.aw_valid && mst_resp.aw_ready) begin
      w_cnt_d += 1;
    end
    if (mst_req.w_valid && mst_resp.w_ready && mst_req.w.last) begin
      w_cnt_d -= 1;
    end
  end

  always_ff @(posedge clk_i, negedge rst_ni) begin
    if (!rst_ni) begin
      id_q <= '0;
      r_beats_q <= '0;
      r_state_q <= R_FEEDTHROUGH;
      w_cnt_q <= '0;
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
  assign r_resp_cmd_push.len = slv_req.aw.len;

// pragma translate_off
`ifndef VERILATOR
  initial begin: p_assertions
    assert (AXI_ID_WIDTH >= 1) else $fatal("AXI ID width must be at least 1!");
    assert (AXI_MAX_WRITE_TXNS >= 1)
      else $fatal("Maximum number of outstanding write transactions must be at least 1!");
  end
`endif
// pragma translate_on
endmodule

`include "axi/assign.svh"
`include "axi/typedef.svh"

// interface wrapper
module axi_atop_filter_wrap #(
  parameter int unsigned AXI_ID_WIDTH   = 0, // Synopsys DC requires a default value for parameters.
  parameter int unsigned AXI_ADDR_WIDTH = 0,
  parameter int unsigned AXI_DATA_WIDTH = 0,
  parameter int unsigned AXI_USER_WIDTH = 0,
  // Maximum number of AXI write bursts outstanding at the same time
  parameter int unsigned AXI_MAX_WRITE_TXNS = 0
) (
  input  logic    clk_i,
  input  logic    rst_ni,
  AXI_BUS.Slave   slv,
  AXI_BUS.Master  mst
);

  typedef logic [AXI_ID_WIDTH-1:0]     id_t;
  typedef logic [AXI_ADDR_WIDTH-1:0]   addr_t;
  typedef logic [AXI_DATA_WIDTH-1:0]   data_t;
  typedef logic [AXI_DATA_WIDTH/8-1:0] strb_t;
  typedef logic [AXI_USER_WIDTH-1:0]   user_t;
  `AXI_TYPEDEF_AW_CHAN_T ( aw_chan_t, addr_t, id_t,         user_t);
  `AXI_TYPEDEF_W_CHAN_T  (  w_chan_t, data_t,       strb_t, user_t);
  `AXI_TYPEDEF_B_CHAN_T  (  b_chan_t,         id_t,         user_t);
  `AXI_TYPEDEF_AR_CHAN_T ( ar_chan_t, addr_t, id_t,         user_t);
  `AXI_TYPEDEF_R_CHAN_T  (  r_chan_t, data_t, id_t,         user_t);
  `AXI_TYPEDEF_REQ_T     (     req_t, aw_chan_t, w_chan_t, ar_chan_t);
  `AXI_TYPEDEF_RESP_T    (    resp_t,  b_chan_t, r_chan_t) ;

  req_t  slv_req,  mst_req;
  resp_t slv_resp, mst_resp;

  `AXI_ASSIGN_TO_REQ    ( slv_req,  slv      );
  `AXI_ASSIGN_FROM_RESP ( slv,      slv_resp );

  `AXI_ASSIGN_FROM_REQ  ( mst     , mst_req  );
  `AXI_ASSIGN_TO_RESP   ( mst_resp, mst      );

  axi_atop_filter #(
    .AXI_ID_WIDTH       (AXI_ID_WIDTH       ),
  // Maximum number of AXI write bursts outstanding at the same time
    .AXI_MAX_WRITE_TXNS (AXI_MAX_WRITE_TXNS ),
  // AXI request & response type
    .req_t  ( req_t  ),
    .resp_t ( resp_t )
  ) i_axi_atop_filter (
    .clk_i      ( clk_i    ),
    .rst_ni     ( rst_ni   ),
    .slv_req_i  ( slv_req  ),
    .slv_resp_o ( slv_resp ),
    .mst_req_o  ( mst_req  ),
    .mst_resp_i ( mst_resp )
  );
endmodule
