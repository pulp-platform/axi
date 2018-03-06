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


/// A connector that joins two AXI-Lite interfaces.
module axi_lite_join (
  AXI_LITE.in  in,
  AXI_LITE.out out
);

  assign out.aw_addr   = in.aw_addr;
  assign out.aw_valid  = in.aw_valid;
  assign out.w_data    = in.w_data;
  assign out.w_strb    = in.w_strb;
  assign out.w_valid   = in.w_valid;
  assign out.b_ready   = in.b_ready;
  assign out.ar_addr   = in.ar_addr;
  assign out.ar_valid  = in.ar_valid;
  assign out.r_ready   = in.r_ready;

  assign in.aw_ready = out.aw_ready;
  assign in.w_ready  = out.w_ready;
  assign in.b_resp   = out.b_resp;
  assign in.b_valid  = out.b_valid;
  assign in.ar_ready = out.ar_ready;
  assign in.r_data   = out.r_data;
  assign in.r_resp   = out.r_resp;
  assign in.r_valid  = out.r_valid;

endmodule
