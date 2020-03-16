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

// Author: Fabian Schuiki <fschuiki@iis.ethz.ch>
//         Florian Zaruba <zarubaf@iis.ethz.ch>
//         Wolfgang Roenninger <wroennin@ethz.ch>

// Description: This module can isolate the AXI4+ATOPs bus on the master port from the slave port.
//              When the isolation is not active the two ports are directly connected.
//              This unit counts how many open transactions are currently in flight
//              on the read and write channels. It further is capable of tracking the amount of
//              open atomic transactions with read responses.
//              The isolation interface has the two signals `isolate_i` and `isolated_o`.
//              When `isolate_i` is asserted, all open transactions get terminated.
//              When no longer transactions are in flight the output `isolated_o` gets asserted.
//              As long as `isolated_o` is asserted all output signals in `mst_req_o` are silenced
//              to `'0`. When isolated, new transactions initiated on the slave port are
//              stalled until the isolation is terminated by deasserting `isolate_i`.

`include "common_cells/registers.svh"

module axi_isolate #(
  parameter int unsigned NoPending = 32'd16, // Number of pending requests per channel
  parameter type         req_t     = logic,  // AXI request struct definition
  parameter type         resp_t    = logic   // AXI response struct definition
) (
  input  logic  clk_i,      // clock
  input  logic  rst_ni,     // reset
  input  req_t  slv_req_i,  // slave port request struct
  output resp_t slv_resp_o, // slave port response struct
  output req_t  mst_req_o,  // master port request struct
  input  resp_t mst_resp_i, // master port response struct
  input  logic  isolate_i,  // isolate master port from slave port
  output logic  isolated_o  // master port is isolated from slave port
);
  // plus 1 in clog for accouning no open transaction, plus one bit for atomic injection
  localparam int unsigned CounterWidth = $clog2(NoPending + 32'd1) + 32'd1;
  typedef logic [CounterWidth-1:0] cnt_t;

  enum logic [1:0] {
    NORMAL,
    HOLD,
    DRAIN,
    ISOLATE
  } state_aw_d, state_aw_q, state_ar_d, state_ar_q;
  logic update_aw_state, update_ar_state;

  cnt_t pending_aw_d,    pending_aw_q;
  logic update_aw_cnt;

  // W channel unlocks over a FIFO
  logic w_push, w_full, w_empty;

  cnt_t pending_ar_d,    pending_ar_q;
  logic update_ar_cnt;

  `FFLARN(pending_aw_q,pending_aw_d, update_aw_cnt, '0, clk_i, rst_ni)
  `FFLARN(pending_ar_q, pending_ar_d, update_ar_cnt, '0, clk_i, rst_ni)
  `FFLARN(state_aw_q, state_aw_d, update_aw_state, ISOLATE, clk_i, rst_ni)
  `FFLARN(state_ar_q, state_ar_d, update_ar_state, ISOLATE, clk_i, rst_ni)

  // Update counters.
  always_comb begin
    pending_aw_d  = pending_aw_q;
    update_aw_cnt = 1'b0;
    w_push        = 1'b0;
    pending_ar_d  = pending_ar_q;
    update_ar_cnt = 1'b0;

    if (mst_req_o.aw_valid && (state_aw_q == NORMAL)) begin
      pending_aw_d++;
      update_aw_cnt = 1'b1;
      w_push        = 1'b1;
      if (mst_req_o.aw.atop[axi_pkg::ATOP_R_RESP]) begin
        pending_ar_d++; // handle atomic with read response by injecting a count in AR
        update_ar_cnt = 1'b1;
      end
    end
    if (mst_req_o.ar_valid && (state_ar_q == NORMAL)) begin
      pending_ar_d++;
      update_ar_cnt = 1'b1;
    end
    if (mst_resp_i.b_valid  && mst_req_o.b_ready) begin
      pending_aw_d--;
      update_aw_cnt = 1'b1;
    end
    if (mst_resp_i.r_valid  && mst_req_o.r_ready && mst_resp_i.r.last) begin
      pending_ar_d--;
      update_ar_cnt = 1'b1;
    end
  end

  // Perform isolation.
  always_comb begin
    // Default assignments
    state_aw_d      = state_aw_q;
    update_aw_state = 1'b0;
    state_ar_d      = state_ar_q;
    update_ar_state = 1'b0;
    // Connect channel per default
    mst_req_o       = slv_req_i;
    slv_resp_o      = mst_resp_i;

    /////////////////////////////////////////////////////////////
    // Write transaction
    /////////////////////////////////////////////////////////////
    case (state_aw_q)
      NORMAL:  begin // NORMAL operation
        // Cut valid handshake if a counter capacity is reached.
        // It has to check AR counter in case of for atomics. Counters are wide enough
        // to account for injected count in the read response counter
        if (pending_aw_q >= cnt_t'(NoPending) || pending_ar_q >= cnt_t'(2*NoPending) || w_full) begin
          mst_req_o.aw_valid  = 1'b0;
          slv_resp_o.aw_ready = 1'b0;
          if (isolate_i) begin
            state_aw_d      = DRAIN;
            update_aw_state = 1'b1;
          end
        end else begin
          // here the AW handshake is connected normally
          if (slv_req_i.aw_valid && !mst_resp_i.aw_ready) begin
            state_aw_d      = HOLD;
            update_aw_state = 1'b1;
          end else begin
            if (isolate_i) begin
              state_aw_d      = DRAIN;
              update_aw_state = 1'b1;
            end
          end
        end
      end
      HOLD: begin // Hold the valid signal on 1'b1 if there was no transfer
        mst_req_o.aw_valid = 1'b1;
        // aw_ready normal connected
        if (mst_resp_i.aw_ready) begin
          update_aw_state = 1'b1;
          state_aw_d      = isolate_i ? DRAIN : NORMAL;
        end
      end
      DRAIN: begin // cut the AW channel until counter is zero
        mst_req_o.aw        = '0;
        mst_req_o.aw_valid  = 1'b0;
        slv_resp_o.aw_ready = 1'b0;
        if (pending_aw_q == '0) begin
          state_aw_d      = ISOLATE;
          update_aw_state = 1'b1;
        end
      end
      ISOLATE: begin // Cut the signals to the outputs
        mst_req_o.aw        = '0;
        mst_req_o.aw_valid  = 1'b0;
        slv_resp_o.aw_ready = 1'b0;
        slv_resp_o.b        = '0;
        slv_resp_o.b_valid  = 1'b0;
        mst_req_o.b_ready   = 1'b0;
        if (!isolate_i) begin
          state_aw_d      = NORMAL;
          update_aw_state = 1'b1;
        end
      end
    endcase

    // W channel is cloded as long as nothing is in the unlock FIFO.
    if (w_empty) begin
      mst_req_o.w         = '0;
      mst_req_o.w_valid   = 1'b0;
      slv_resp_o.w_ready  = 1'b0;
    end

    /////////////////////////////////////////////////////////////
    // Read transaction
    /////////////////////////////////////////////////////////////
    case (state_ar_q)
      NORMAL: begin
        // cut handshake if counter capacity is reached
        if (pending_ar_q >= NoPending) begin
          mst_req_o.ar_valid  = 1'b0;
          slv_resp_o.ar_ready = 1'b0;
          if (isolate_i) begin
            state_ar_d      = DRAIN;
            update_ar_state = 1'b1;
          end
        end else begin
          // here the AR handshake is connected normally
          if (slv_req_i.ar_valid && !mst_resp_i.ar_ready) begin
            state_ar_d      = HOLD;
            update_ar_state = 1'b1;
          end else begin
            if (isolate_i) begin
              state_ar_d      = DRAIN;
              update_ar_state = 1'b1;
            end
          end
        end
      end
      HOLD: begin // Hold the valid signal on 1'b1 if there was no transfer
        mst_req_o.ar_valid = 1'b1;
        // ar_ready normal connected
        if (mst_resp_i.ar_ready) begin
          update_ar_state = 1'b1;
          state_ar_d      = isolate_i ? DRAIN : NORMAL;
        end
      end
      DRAIN: begin
        mst_req_o.ar        = '0;
        mst_req_o.ar_valid  = 1'b0;
        slv_resp_o.ar_ready = 1'b0;
        if (pending_ar_q == '0) begin
          state_ar_d      = ISOLATE;
          update_ar_state = 1'b1;
        end
      end
      ISOLATE: begin
        mst_req_o.ar        = '0;
        mst_req_o.ar_valid  = 1'b0;
        slv_resp_o.ar_ready = 1'b0;
        slv_resp_o.r        = '0;
        slv_resp_o.r_valid  = 1'b0;
        mst_req_o.r_ready   = 1'b0;
        if (!isolate_i) begin
          state_ar_d      = NORMAL;
          update_ar_state = 1'b1;
        end
      end
    endcase
  end

  // This FIFO holds over the push and pop signals the unlock state for the W channel
  fifo_v3 #(
    .FALL_THROUGH ( 1'b1      ),
    .DATA_WIDTH   ( 32'd1     ),
    .DEPTH        ( NoPending )
  ) i_w_fifo (
    .clk_i     ( clk_i                                                     ),
    .rst_ni    ( rst_ni                                                    ),
    .flush_i   ( 1'b0                                                      ),
    .testmode_i( 1'b0                                                      ),
    .full_o    ( w_full                                                    ),
    .empty_o   ( w_empty                                                   ),
    .usage_o   ( /*not used*/                                              ),
    .data_i    ( 1'd0                                                      ),
    .push_i    ( w_push                                                    ),
    .data_o    ( /*not used*/                                              ),
    .pop_i     ( mst_req_o.w_valid & mst_resp_i.w_ready & mst_req_o.w.last )
  );

  // the isolated output signal
  assign isolated_o = (state_aw_q == ISOLATE && state_ar_q == ISOLATE);

// pragma translate_off
`ifndef VERILATOR
  initial begin
    assume (NoPending > 0) else $fatal(1, "At least one pending transaction required.");
  end
  default disable iff (!rst_ni);
  aw_overflow: assert property (@(posedge clk_i)
      (pending_aw_q == '1) |=> (pending_aw_q != '0)) else
      $fatal(1, "pending_aw_q overflowed");
  ar_overflow: assert property (@(posedge clk_i)
      (pending_ar_q == '1) |=> (pending_ar_q != '0)) else
      $fatal(1, "pending_ar_q overflowed");
  aw_underflow: assert property (@(posedge clk_i)
      (pending_aw_q == '0) |=> (pending_aw_q != '1)) else
      $fatal(1, "pending_aw_q underflowed");
  ar_underflow: assert property (@(posedge clk_i)
      (pending_ar_q == '0) |=> (pending_ar_q != '1)) else
      $fatal(1, "pending_ar_q underflowed");
`endif
// pragma translate_on
endmodule

`include "axi/typedef.svh"
`include "axi/assign.svh"

module axi_isolate_intf #(
  parameter int unsigned NoPending    = 32'd16, // number of pending requests
  parameter int unsigned AxiIdWidth   = 32'd0,  // AXI ID width
  parameter int unsigned AxiAddrWidth = 32'd0,  // AXI address width
  parameter int unsigned AxiDataWidth = 32'd0,  // AXI data width
  parameter int unsigned AxiUserWidth = 32'd0   // AXI user width
) (
  input  logic   clk_i,      // clock
  input  logic   rst_ni,     // asynchronous reset active low
  AXI_BUS.Slave  slv,        // slave port
  AXI_BUS.Master mst,        // master port
  input  logic   isolate_i,  // isolate master port from slave port
  output logic   isolated_o  // master port is isolated from slave port
);
  typedef logic [AxiIdWidth-1:0]     id_t;
  typedef logic [AxiAddrWidth-1:0]   addr_t;
  typedef logic [AxiDataWidth-1:0]   data_t;
  typedef logic [AxiDataWidth/8-1:0] strb_t;
  typedef logic [AxiUserWidth-1:0]   user_t;

  `AXI_TYPEDEF_AW_CHAN_T(aw_chan_t, addr_t, id_t, user_t)
  `AXI_TYPEDEF_W_CHAN_T(w_chan_t, data_t, strb_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T(b_chan_t, id_t, user_t)

  `AXI_TYPEDEF_AR_CHAN_T(ar_chan_t, addr_t, id_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(r_chan_t, data_t, id_t, user_t)

  `AXI_TYPEDEF_REQ_T(req_t, aw_chan_t, w_chan_t, ar_chan_t)
  `AXI_TYPEDEF_RESP_T(resp_t, b_chan_t, r_chan_t)

  req_t  slv_req,  mst_req;
  resp_t slv_resp, mst_resp;

  `AXI_ASSIGN_TO_REQ(slv_req, slv)
  `AXI_ASSIGN_FROM_RESP(slv, slv_resp)

  `AXI_ASSIGN_FROM_REQ(mst, mst_req)
  `AXI_ASSIGN_TO_RESP(mst_resp, mst)

  axi_isolate #(
    .NoPending ( NoPending ), // Number of pending requests per channel
    .req_t     ( req_t     ), // AXI request struct definition
    .resp_t    ( resp_t    )  // AXI response struct definition
  ) i_axi_isolate (
    .clk_i,                   // clock
    .rst_ni,                  // reset
    .slv_req_i  ( slv_req  ), // slave port request struct
    .slv_resp_o ( slv_resp ), // slave port response struct
    .mst_req_o  ( mst_req  ), // master port request struct
    .mst_resp_i ( mst_resp ), // master port response struct
    .isolate_i,               // isolate master port from slave port
    .isolated_o               // master port is isolated from slave port
  );

  // pragma translate_off
  `ifndef VERILATOR
  initial begin
    assume (AxiIdWidth   > 0) else $fatal(1, "AxiIdWidth   has to be > 0.");
    assume (AxiAddrWidth > 0) else $fatal(1, "AxiAddrWidth has to be > 0.");
    assume (AxiDataWidth > 0) else $fatal(1, "AxiDataWidth has to be > 0.");
    assume (AxiUserWidth > 0) else $fatal(1, "AxiUserWidth has to be > 0.");
  end
  `endif
  // pragma translate_on
endmodule

