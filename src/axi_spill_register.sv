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


/// A register with handshakes that completely cuts any combinational paths
/// between the input and output.
module axi_spill_register #(
  /// The payload type.
  parameter type T = logic
)(
  input  logic clk_i   ,
  input  logic rst_ni  ,
  input  logic valid_i ,
  output logic ready_o ,
  input  T     data_i  ,
  output logic valid_o ,
  input  logic ready_i ,
  output T     data_o
);

  // Create the data and fullness registers.
  T data_slice_q, data_spill_q;
  logic slice_full_q, spill_full_q;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni)
      data_slice_q <= '0;
    else if (valid_i && ~spill_full_q)
      data_slice_q <= data_i;
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni)
      slice_full_q <= 0;
    else if (~spill_full_q)
      slice_full_q <= valid_i;
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni)
      data_spill_q <= '0;
    else if (~ready_i && slice_full_q)
      data_spill_q <= data_slice_q;
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni)
      spill_full_q <= 0;
    else if (~ready_i || spill_full_q)
      spill_full_q <= ~ready_i && slice_full_q;
  end

  // The unit is able to accept input as long as the spill register is empty.
  assign ready_o = ~spill_full_q;

  // The unit provides output as long as one of the registers is filled.
  assign valid_o = slice_full_q | spill_full_q;

  // We empty the spill register before the slice register.
  assign data_o = spill_full_q ? data_spill_q : data_slice_q;

endmodule
