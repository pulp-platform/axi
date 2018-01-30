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
/// Burst accesses are not yet supported and DO NOT produce an error.
module axi_to_axi_lite #(
  /// Maximum number of outstanding reads.
  parameter int NUM_PENDING_RD = 1,
  /// Maximum number of outstanding writes.
  parameter int NUM_PENDING_WR = 1
)(
  input logic clk_i,
  input logic rst_ni,
  AXI_BUS.Slave slave,
  AXI_LITE.Master master
);

  `ifndef SYNTHESIS
  initial begin
    assert(NUM_PENDING_RD > 0);
    assert(NUM_PENDING_WR > 0);
    assert(slave.AXI_ADDR_WIDTH == master.AXI_ADDR_WIDTH);
    assert(slave.AXI_DATA_WIDTH == master.AXI_DATA_WIDTH);
  end
  `endif

  // Round the maximum number of pending transactions up to the next power of
  // two. This is required by the implementation of the FIFO.
  localparam int DEPTH_FIFO_RD = 2**$clog2(NUM_PENDING_RD);
  localparam int DEPTH_FIFO_WR = 2**$clog2(NUM_PENDING_WR);

  // The transaction information that will be stored locally.
  typedef struct packed {
    logic [$bits(slave.r_id)-1:0] id;
    logic [$bits(slave.r_user)-1:0] user;
  } meta_rd_t;

  typedef struct packed {
    logic [$bits(slave.b_id)-1:0] id;
    logic [$bits(slave.b_user)-1:0] user;
  } meta_wr_t;

  // HACK: Rather than passing a meta_rd_t and meta_wr_t into the FIFO's data_o
  //       port, we destructure it into the constituent fields. If we don't do
  //       this, Synopsys DC 2016.03 throws an "Internal Error" on "meta_rd.id".
  logic [$bits(slave.r_id)-1:0] meta_rd_id;
  logic [$bits(slave.r_user)-1:0] meta_rd_user;
  logic [$bits(slave.b_id)-1:0] meta_wr_id;
  logic [$bits(slave.b_user)-1:0] meta_wr_user;

  // The two FIFOs which hold the transaction information.
  logic rd_full;
  logic wr_full;
  meta_rd_t meta_rd;
  meta_wr_t meta_wr;

  axi_fifo #(.dtype(meta_rd_t), .DEPTH(DEPTH_FIFO_RD)) i_fifo_rd (
    .clk_i   ( clk_i                                        ),
    .rst_ni  ( rst_ni                                       ),
    .flush_i ( '0                                           ),
    .full_o  ( rd_full                                      ),
    .empty_o (                                              ),
    .single_element_o (                                     ),
    // For every transaction on the AR channel we push the ID and USER metadata
    // into the queue.
    .data_i  ( {slave.ar_id, slave.ar_user}                 ),
    .push_i  ( slave.ar_ready & slave.ar_valid              ),
    // After the last response on the R channel we pop the metadata off the
    // queue.
    .data_o  ( {meta_rd_id, meta_rd_user}                   ),
    // .data_o  ( meta_rd                                      ),
    .pop_i   ( slave.r_valid & slave.r_ready & slave.r_last )
  );

  axi_fifo #(.dtype(meta_wr_t), .DEPTH(DEPTH_FIFO_WR)) i_fifo_wr (
    .clk_i   ( clk_i                           ),
    .rst_ni  ( rst_ni                          ),
    .flush_i ( '0                              ),
    .full_o  ( wr_full                         ),
    .empty_o (                                              ),
    .single_element_o (                                     ),
    // For every transaction on the AW channel we push the ID and USER metadata
    // into the queue.
    .data_i  ( {slave.aw_id, slave.aw_user}    ),
    .push_i  ( slave.aw_ready & slave.aw_valid ),
    // After the response on the B channel we pop the metadata off the queue.
    .data_o  ( {meta_wr_id, meta_wr_user}                   ),
    // .data_o  ( meta_wr                                      ),
    .pop_i   ( slave.b_valid & slave.b_ready   )
  );

  // Accept transactions on the AW and AR channels if the corresponding FIFO is
  // not full.
  assign slave.aw_ready  = ~wr_full & master.aw_ready;
  assign slave.ar_ready  = ~rd_full & master.ar_ready;
  assign master.aw_addr  = slave.aw_addr;
  assign master.ar_addr  = slave.ar_addr;
  assign master.aw_valid = slave.aw_valid;
  assign master.ar_valid = slave.ar_valid;

  assign master.w_data  = slave.w_data;
  assign master.w_strb  = slave.w_strb;
  assign master.w_valid = slave.w_valid;
  assign slave.w_ready  = master.w_ready;

  // Inject the metadata again on the B and R return paths.
  assign slave.b_id     = meta_wr_id;
  assign slave.b_resp   = master.b_resp;
  assign slave.b_user   = meta_wr_user;
  assign slave.b_valid  = master.b_valid;
  assign master.b_ready = slave.b_ready;

  assign slave.r_id     = meta_rd_id;
  assign slave.r_data   = master.r_data;
  assign slave.r_resp   = master.r_resp;
  assign slave.r_last   = '1;
  assign slave.r_user   = meta_rd_user;
  assign slave.r_valid  = master.r_valid;
  assign master.r_ready = slave.r_ready;

endmodule
