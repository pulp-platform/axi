// Copyright (c) 2018 ETH Zurich, University of Bologna
// All rights reserved.
//
// This code is under development and not yet released to the public.
// Until it is released, the code is under the copyright of ETH Zurich and
// the University of Bologna, and may contain confidential and/or unpublished
// work. Any reuse/redistribution is strictly forbidden without written
// permission from ETH Zurich.
//
// Bug fixes and contributions will eventually be released under the
// SolderPad open hardware license in the context of the PULP platform
// (http://www.pulp-platform.org), under the copyright of ETH Zurich and the
// University of Bologna.
//
// Fabian Schuiki <fschuiki@iis.ee.ethz.ch>

import axi_pkg::*;


/// An AXI4-Lite slice.
///
/// Breaks all combinatorial paths between its input and output.
module axi_lite_slice #(
  /// The address width.
  parameter int ADDR_WIDTH = -1,
  /// The data width.
  parameter int DATA_WIDTH = -1
)(
  input logic            clk_i  ,
  input logic            rst_ni ,
  AXI_LITE.in            in     ,
  AXI_LITE.out           out
);

  // Check the invariants.
  `ifndef SYNTHESIS
  initial begin
    assert(ADDR_WIDTH >= 0);
    assert(DATA_WIDTH >= 0);
    assert(in.AXI_ADDR_WIDTH == ADDR_WIDTH);
    assert(in.AXI_DATA_WIDTH == DATA_WIDTH);
    assert(out.AXI_ADDR_WIDTH == ADDR_WIDTH);
    assert(out.AXI_DATA_WIDTH == DATA_WIDTH);
  end
  `endif

  // Create spill registers to buffer each channel.
  typedef struct packed {
    logic [ADDR_WIDTH-1:0] addr;
  } channel_ax_t;

  typedef struct packed {
    logic [DATA_WIDTH-1:0] data;
    logic [DATA_WIDTH/8-1:0] strb;
  } channel_w_t;

  typedef struct packed {
    resp_t resp;
  } channel_b_t;

  typedef struct packed {
    logic [DATA_WIDTH-1:0] data;
    resp_t resp;
  } channel_r_t;

  channel_ax_t aw_in, aw_out;
  assign aw_in.addr = in.aw_addr;
  assign out.aw_addr = aw_out.addr;
  axi_spill_register #(channel_ax_t) i_reg_aw (
    .clk_i   ( clk_i        ),
    .rst_ni  ( rst_ni       ),
    .valid_i ( in.aw_valid  ),
    .ready_o ( in.aw_ready  ),
    .data_i  ( aw_in        ),
    .valid_o ( out.aw_valid ),
    .ready_i ( out.aw_ready ),
    .data_o  ( aw_out       )
  );

  channel_w_t w_in, w_out;
  assign w_in.data = in.w_data;
  assign w_in.strb = in.w_strb;
  assign out.w_data = w_out.data;
  assign out.w_strb = w_out.strb;
  axi_spill_register #(channel_w_t) i_reg_w (
    .clk_i   ( clk_i       ),
    .rst_ni  ( rst_ni      ),
    .valid_i ( in.w_valid  ),
    .ready_o ( in.w_ready  ),
    .data_i  ( w_in        ),
    .valid_o ( out.w_valid ),
    .ready_i ( out.w_ready ),
    .data_o  ( w_out       )
  );

  channel_b_t b_in, b_out;
  assign b_out.resp = out.b_resp;
  assign in.b_resp = b_in.resp;
  axi_spill_register #(channel_b_t) i_reg_b (
    .clk_i   ( clk_i       ),
    .rst_ni  ( rst_ni      ),
    .valid_i ( out.b_valid ),
    .ready_o ( out.b_ready ),
    .data_i  ( b_out       ),
    .valid_o ( in.b_valid  ),
    .ready_i ( in.b_ready  ),
    .data_o  ( b_in        )
  );

  channel_ax_t ar_in, ar_out;
  assign ar_in.addr = in.ar_addr;
  assign out.ar_addr = ar_out.addr;
  axi_spill_register #(channel_ax_t) i_reg_ar (
    .clk_i   ( clk_i        ),
    .rst_ni  ( rst_ni       ),
    .valid_i ( in.ar_valid  ),
    .ready_o ( in.ar_ready  ),
    .data_i  ( ar_in        ),
    .valid_o ( out.ar_valid ),
    .ready_i ( out.ar_ready ),
    .data_o  ( ar_out       )
  );

  channel_r_t r_in, r_out;
  assign r_out.data = out.r_data;
  assign r_out.resp = out.r_resp;
  assign in.r_data = r_in.data;
  assign in.r_resp = r_in.resp;
  axi_spill_register #(channel_r_t) i_reg_r (
    .clk_i   ( clk_i       ),
    .rst_ni  ( rst_ni      ),
    .valid_i ( out.r_valid ),
    .ready_o ( out.r_ready ),
    .data_i  ( r_out       ),
    .valid_o ( in.r_valid  ),
    .ready_i ( in.r_ready  ),
    .data_o  ( r_in        )
  );

endmodule
