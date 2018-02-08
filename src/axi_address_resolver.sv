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

/// An address resolver.
///
/// Matches an address against a routing table and produces the index of the
/// matching slave.
module axi_address_resolver #(
  /// The address width.
  parameter int ADDR_WIDTH = -1,
  /// The number of slaves.
  parameter int NUM_SLAVE = -1,
  /// The number of rules.
  parameter int NUM_RULES = -1
)(
  AXI_ROUTING_RULES.xbar               rules       ,
  input  logic [ADDR_WIDTH-1:0]        addr_i      ,
  output logic [$clog2(NUM_SLAVE)-1:0] match_idx_o ,
  output logic                         match_ok_o
);

  logic [NUM_SLAVE-1:0][NUM_RULES-1:0] matched_rules;
  logic [NUM_SLAVE-1:0]                matched_slaves;

  for (genvar i = 0; i < NUM_SLAVE; i++) begin : g_slave
    // Match each of the rules.
    for (genvar j = 0; j < NUM_RULES; j++) begin : g_rule
      logic [ADDR_WIDTH-1:0] base, mask;
      assign base = rules.rules[i][j].base;
      assign mask = rules.rules[i][j].mask;
      assign matched_rules[i][j] = (mask != '0 && (addr_i & mask) == (base & mask));
    end

    // Check which slaves matched.
    assign matched_slaves[i] = |matched_rules[i];
  end

  // // If anything matched the address, output ok.
  assign match_ok_o = |matched_slaves;

  // Determine the index of the slave that matched.
  axi_find_first_one #(.WIDTH(NUM_SLAVE)) i_lzc (
    .in_i        ( matched_slaves ),
    .first_one_o ( match_idx_o    ),
    .no_ones_o   (                )
  );

  // Ensure that we have a one-hot match. If we don't, this implies that the
  // rules in the routing table are not mututally exclusive.
  `ifndef SYNTHESIS
  always @(matched_rules, matched_slaves) begin
    assert($onehot0(matched_rules));
    assert($onehot0(matched_slaves));
  end
  `endif

endmodule
