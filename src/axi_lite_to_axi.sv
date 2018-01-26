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

/// An AXI4-Lite to AXI4 adapter.
module axi_lite_to_axi (
  AXI_LITE.Slave slave,
  AXI_BUS.Master master
);

  `ifndef SYNTHESIS
  initial begin
    assert(slave.AXI_ADDR_WIDTH == master.AXI_ADDR_WIDTH);
    assert(slave.AXI_DATA_WIDTH == master.AXI_DATA_WIDTH);
  end
  `endif

  assign master.aw_id     = '0;
  assign master.aw_addr   = slave.aw_addr;
  assign master.aw_len    = '0;
  assign master.aw_size   = $unsigned($clog2($bits(master.w_data)/8));
  assign master.aw_burst  = axi_pkg::BURST_FIXED;
  assign master.aw_lock   = '0;
  assign master.aw_cache  = '0; // non-modifiable and non-bufferable mandated by std
  assign master.aw_prot   = '0;
  assign master.aw_qos    = '0;
  assign master.aw_region = '0;
  assign master.aw_user   = '0;
  assign master.aw_valid  = slave.aw_valid;
  assign slave.aw_ready   = master.aw_ready;

  assign master.w_data    = slave.w_data;
  assign master.w_strb    = slave.w_strb;
  assign master.w_last    = '1;
  assign master.w_user    = '0;
  assign master.w_valid   = slave.w_valid;
  assign slave.w_ready    = master.w_ready;

  assign slave.b_resp     = master.b_resp;
  assign slave.b_valid    = master.b_valid;
  assign master.b_ready   = slave.b_ready;

  assign master.ar_id     = '0;
  assign master.ar_addr   = slave.ar_addr;
  assign master.ar_len    = '0;
  assign master.ar_size   = $unsigned($clog2($bits(master.r_data)/8));
  assign master.ar_burst  = axi_pkg::BURST_FIXED;
  assign master.ar_lock   = '0;
  assign master.ar_cache  = '0; // non-modifiable and non-bufferable mandated by std
  assign master.ar_prot   = '0;
  assign master.ar_qos    = '0;
  assign master.ar_region = '0;
  assign master.ar_user   = '0;
  assign master.ar_valid  = slave.ar_valid;
  assign slave.ar_ready   = master.ar_ready;

  assign slave.r_data     = master.r_data;
  assign slave.r_resp     = master.r_resp;
  assign slave.r_valid    = master.r_valid;
  assign master.r_ready   = slave.r_ready;

endmodule
