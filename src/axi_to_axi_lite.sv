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

/// An AXI4 to AXI4-Lite adapter.
///
/// Two internal FIFOs are used to perform ID reflection. The length of these
/// FIFOs determines the maximum number of outstanding transactions on the read
/// and write channels that the adapter can handle.
///
/// Burst accesses will result in an error.
module axi_to_axi_lite #(
  /// Maximum number of outstanding reads.
  parameter int NUM_PENDING_R = 1,
  /// Maximum number of outstanding writes.
  parameter int NUM_PENDING_W = 1
)(
  input logic clk_i,
  input logic rst_ni,
  AXI_BUS.Slave slave,
  AXI_LITE.Master master
);

  `ifndef SYNTHESIS
  initial begin
    assert(NUM_PENDING_R > 0);
    assert(NUM_PENDING_W > 0);
    assert(slave.AXI_ADDR_WIDTH == master.AXI_ADDR_WIDTH);
    assert(slave.AXI_DATA_WIDTH == master.AXI_DATA_WIDTH);
  end
  `endif

endmodule
