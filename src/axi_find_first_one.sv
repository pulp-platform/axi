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


/// A leading zero counter.
module axi_find_first_one #(
  /// The width of the number.
  parameter int WIDTH = -1
)(
  input  logic [WIDTH-1:0]         in_i,
  output logic [$clog2(WIDTH)-1:0] first_one_o,
  output logic                     no_ones_o
);

  localparam int NUM_LEVELS = $clog2(WIDTH);

  `ifndef SYNTHESIS
  initial begin
    assert(WIDTH >= 0);
  end
  `endif

  logic [WIDTH-1:0][NUM_LEVELS-1:0]          index_lut;
  logic [2**NUM_LEVELS-1:0]                  sel_nodes;
  logic [2**NUM_LEVELS-1:0][NUM_LEVELS-1:0]  index_nodes;

  generate
    for (genvar j = 0; j < WIDTH; j++) begin
      assign index_lut[j] = j;
    end
  endgenerate

  generate
    for (genvar level = 0; level < NUM_LEVELS; level++) begin

      if (level < NUM_LEVELS-1) begin
        for (genvar l = 0; l < 2**level; l++) begin
          assign sel_nodes[2**level-1+l]   = sel_nodes[2**(level+1)-1+l*2] | sel_nodes[2**(level+1)-1+l*2+1];
          assign index_nodes[2**level-1+l] = (sel_nodes[2**(level+1)-1+l*2] == 1'b1) ?
            index_nodes[2**(level+1)-1+l*2] : index_nodes[2**(level+1)-1+l*2+1];
        end
      end

      if (level == NUM_LEVELS-1) begin
        for (genvar k = 0; k < 2**level; k++) begin
          // if two successive indices are still in the vector...
          if (k * 2 < WIDTH) begin
            assign sel_nodes[2**level-1+k]   = in_i[k*2] | in_i[k*2+1];
            assign index_nodes[2**level-1+k] = (in_i[k*2] == 1'b1) ? index_lut[k*2] : index_lut[k*2+1];
          end
          // if only the first index is still in the vector...
          if (k * 2 == WIDTH) begin
            assign sel_nodes[2**level-1+k]   = in_i[k*2];
            assign index_nodes[2**level-1+k] = index_lut[k*2];
          end
          // if index is out of range
          if (k * 2 > WIDTH) begin
            assign sel_nodes[2**level-1+k]   = 1'b0;
            assign index_nodes[2**level-1+k] = '0;
          end
        end
      end
    end
  endgenerate

  assign first_one_o = NUM_LEVELS > 0 ? index_nodes[0] : '0;
  assign no_ones_o   = NUM_LEVELS > 0 ? ~sel_nodes[0]  : '1;

endmodule
