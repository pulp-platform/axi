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


/// Multiple AXI4-Lite cuts.
///
/// These can be used to relax timing pressure on very long AXI-Lite busses.
module axi_lite_multicut #(
  /// The address width.
  parameter int ADDR_WIDTH = -1,
  /// The data width.
  parameter int DATA_WIDTH = -1,
  // The number of cuts. Must be >= 0.
  parameter int NUM_CUTS = 0
)(
  input logic  clk_i  ,
  input logic  rst_ni ,
  AXI_LITE.in  in     ,
  AXI_LITE.out out
);

  // Check the invariants.
  `ifndef SYNTHESIS
  initial begin
    assert(NUM_CUTS >= 0);
  end
  `endif

  // Handle the special case of no cuts.
  if (NUM_CUTS == 0) begin : g_cuts
    axi_lite_join i_join (
      .in  ( in  ),
      .out ( out )
    );
  end

  // Handle the special case of one cut.
  else if (NUM_CUTS == 1) begin : g_cuts
    axi_lite_cut #(
      .ADDR_WIDTH ( ADDR_WIDTH ),
      .DATA_WIDTH ( DATA_WIDTH )
    ) i_cut (
      .clk_i  ( clk_i  ),
      .rst_ni ( rst_ni ),
      .in     ( in     ),
      .out    ( out    )
    );
  end

  // Handle the cases of two or more cuts.
  else begin : g_cuts
    AXI_LITE #(
      .AXI_ADDR_WIDTH ( ADDR_WIDTH ),
      .AXI_DATA_WIDTH ( DATA_WIDTH )
    ) s_cut[NUM_CUTS-1](clk_i);

    axi_lite_cut #(
      .ADDR_WIDTH ( ADDR_WIDTH ),
      .DATA_WIDTH ( DATA_WIDTH )
    ) i_first (
      .clk_i  ( clk_i        ),
      .rst_ni ( rst_ni       ),
      .in     ( in           ),
      .out    ( s_cut[0].out )
    );

    for (genvar i = 1; i < NUM_CUTS-1; i++) begin
      axi_lite_cut #(
        .ADDR_WIDTH ( ADDR_WIDTH ),
        .DATA_WIDTH ( DATA_WIDTH )
      ) i_middle (
        .clk_i  ( clk_i         ),
        .rst_ni ( rst_ni        ),
        .in     ( s_cut[i-1].in ),
        .out    ( s_cut[i].out  )
      );
    end

    axi_lite_cut #(
      .ADDR_WIDTH ( ADDR_WIDTH ),
      .DATA_WIDTH ( DATA_WIDTH )
    ) i_last (
      .clk_i  ( clk_i                ),
      .rst_ni ( rst_ni               ),
      .in     ( s_cut[NUM_CUTS-2].in ),
      .out    ( out                  )
    );
  end

endmodule
