// Copyright 2021 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51
//
// Authors: Nils Wistoff <nwistoff@iis.ee.ethz.ch>
// Description:
// Listens to AXI4 AW channel and issue single cacheline invalidations.
// All other channels are passed through.

module axi_inval_filter #(
    // Maximum number of AXI write bursts outstanding at the same time
    parameter int  unsigned MaxTxns     = 32'd0,
    // AXI Bus Types
    parameter int  unsigned AddrWidth   = 32'd0,
    parameter int  unsigned L1LineWidth = 32'd0,
    parameter type          aw_chan_t   = logic,
    parameter type          req_t       = logic,
    parameter type          resp_t      = logic
  ) (
    input logic clk_i,
    input logic rst_ni,
    input logic en_i,

    // Input / Slave Port
    input  req_t  slv_req_i,
    output resp_t slv_resp_o,

    // Output / Master Port
    output req_t  mst_req_o,
    input  resp_t mst_resp_i,

    // Output / Cache invalidation requests
    output logic [AddrWidth-1:0] inval_addr_o,
    output logic                 inval_valid_o,
    input  logic                 inval_ready_i
  );

  import cf_math_pkg::idx_width;

  // Includes
  `include "axi/typedef.svh"
  `include "common_cells/registers.svh"

  // AW FIFO
  logic     aw_fifo_full, aw_fifo_empty;
  logic     aw_fifo_push, aw_fifo_pop;
  aw_chan_t aw_fifo_data;

  assign aw_fifo_push = en_i & slv_req_i.aw_valid & slv_resp_o.aw_ready;

  // Invalidation requests
  logic [AddrWidth-1:0] inval_offset_d, inval_offset_q;

  assign inval_addr_o  = aw_fifo_data.addr + inval_offset_q;
  assign inval_valid_o = ~aw_fifo_empty;

  //////////////////
  // AXI Handling //
  //////////////////

  always_comb begin : axi
    // Default: Feed through
    mst_req_o  = slv_req_i;
    slv_resp_o = mst_resp_i;

    // Do not accept new AWs if FIFO is full
    if (aw_fifo_full) begin
      slv_resp_o.aw_ready = 1'b0;
      mst_req_o.aw_valid  = 1'b0;
    end
  end

  ///////////////////////
  // Invalidation FSM  //
  ///////////////////////

  enum logic { Idle, Invalidating } state_d, state_q;

  always_comb begin : inval_fsm
    // Default assignments
    state_d        = state_q;
    aw_fifo_pop    = 1'b0;
    inval_offset_d = inval_offset_q;

    unique case (state_q)
      // Ready for the next invalidation
      Idle: begin
        // We have a new AW
        if (!aw_fifo_empty) begin
          // Wait for the L1 to accept a new invalidation request
          if (inval_ready_i) begin
            // Continue if we are not done yet
            // If the addr is misaligned wrt the cache line, we should invalidate one line more
            if ((L1LineWidth - aw_fifo_data.addr[idx_width(L1LineWidth)-1:0]) < ((aw_fifo_data.len + 1) << aw_fifo_data.size)) begin
              state_d        = Invalidating;
              inval_offset_d = L1LineWidth - aw_fifo_data.addr[idx_width(L1LineWidth)-1:0];
            end else begin
              aw_fifo_pop = 1'b1;
            end
          end
        end
      end

      // Issue incrementing invalidation requests
      Invalidating: begin
        // Wait for the L1 to accept a new invalidation request
        if (inval_ready_i) begin
          inval_offset_d = inval_offset_q + L1LineWidth;
          // Are we done?
          if (inval_offset_d >= ((aw_fifo_data.len + 1) << aw_fifo_data.size)) begin
            state_d        = Idle;
            inval_offset_d = '0;
            aw_fifo_pop    = 1'b1;
          end
        end
      end
    endcase
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      state_q        <= Idle;
      inval_offset_q <= '0;
    end else begin
      state_q        <= state_d;
      inval_offset_q <= inval_offset_d;
    end
  end

  fifo_v3 #(
    .FALL_THROUGH ( 1'b1      ),
    .DEPTH        ( MaxTxns   ),
    .dtype        ( aw_chan_t )
  ) i_aw_fifo (
    .clk_i      ( clk_i         ),
    .rst_ni     ( rst_ni        ),
    .flush_i    ( 1'b0          ),
    .testmode_i ( 1'b0          ),
    .full_o     ( aw_fifo_full  ),
    .empty_o    ( aw_fifo_empty ),
    .usage_o    (               ),
    .data_i     ( slv_req_i.aw  ),
    .push_i     ( aw_fifo_push  ),
    .data_o     ( aw_fifo_data  ),
    .pop_i      ( aw_fifo_pop   )
  );

endmodule : axi_inval_filter
