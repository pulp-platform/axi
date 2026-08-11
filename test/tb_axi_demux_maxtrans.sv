// Copyright (c) 2026 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Directed regression for pulp-platform/axi issue #249:
// `axi_demux` must accept `MaxTrans` outstanding same-ID transactions, but its
// ID counters are sized with `idx_width(MaxTrans)` bits, which can only count
// to `MaxTrans - 1` when `MaxTrans` is a power of two.  The demux therefore
// reports "full" one transaction early.
//
// Method: issue back-to-back same-ID reads into a demux whose selected master
// port accepts every AR but never returns R beats, so the in-flight count can
// only grow.  The number of accepted AR handshakes before `ar_ready`
// deasserts is exactly the counter limit.  Expected: `MaxTrans`.

`include "axi/typedef.svh"

module tb_axi_demux_maxtrans #(
  /// Configured maximum in-flight transactions of the demux (pow2 triggers #249).
  parameter int unsigned TbMaxTrans = 32'd8,
  /// Number of read requests the driver offers (must exceed TbMaxTrans).
  parameter int unsigned TbNumTxns  = 32'd12
);

  localparam int unsigned TbIdWidth   = 32'd5;
  localparam int unsigned TbAddrWidth = 32'd32;
  localparam int unsigned TbDataWidth = 32'd64;
  localparam int unsigned TbUserWidth = 32'd1;
  localparam int unsigned TbNoMstPorts = 32'd2;

  localparam time CyclTime = 10ns;

  typedef logic [TbIdWidth-1:0]     id_t;
  typedef logic [TbAddrWidth-1:0]   addr_t;
  typedef logic [TbDataWidth-1:0]   data_t;
  typedef logic [TbDataWidth/8-1:0] strb_t;
  typedef logic [TbUserWidth-1:0]   user_t;

  `AXI_TYPEDEF_AW_CHAN_T(aw_chan_t, addr_t, id_t, user_t)
  `AXI_TYPEDEF_W_CHAN_T(w_chan_t, data_t, strb_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T(b_chan_t, id_t, user_t)
  `AXI_TYPEDEF_AR_CHAN_T(ar_chan_t, addr_t, id_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(r_chan_t, data_t, id_t, user_t)
  `AXI_TYPEDEF_REQ_T(axi_req_t, aw_chan_t, w_chan_t, ar_chan_t)
  `AXI_TYPEDEF_RESP_T(axi_resp_t, b_chan_t, r_chan_t)

  logic clk, rst_n;

  clk_rst_gen #(
    .ClkPeriod    ( CyclTime ),
    .RstClkCycles ( 5        )
  ) i_clk_gen (
    .clk_o  ( clk   ),
    .rst_no ( rst_n )
  );

  axi_req_t                     slv_req;
  axi_resp_t                    slv_resp;
  axi_req_t  [TbNoMstPorts-1:0] mst_reqs;
  axi_resp_t [TbNoMstPorts-1:0] mst_resps;

  logic drive_ar;

  // Constant same-ID read request, always offered while `drive_ar` is set.
  always_comb begin
    slv_req             = '0;
    slv_req.ar.id       = id_t'(5);
    slv_req.ar.addr     = addr_t'(32'h0000_0100);
    slv_req.ar.len      = 8'd0;
    slv_req.ar.size     = 3'd3;
    slv_req.ar.burst    = axi_pkg::BURST_INCR;
    slv_req.ar_valid    = drive_ar;
    slv_req.r_ready     = 1'b1;
    slv_req.b_ready     = 1'b1;
  end

  // Master port 0: accept every AR, never return an R beat, so the demux's
  // in-flight counter can only increase.  Port 1 is idle.
  always_comb begin
    mst_resps           = '{default: '0};
    mst_resps[0].ar_ready = 1'b1;
  end

  axi_demux_simple #(
    .AxiIdWidth  ( TbIdWidth    ),
    .AtopSupport ( 1'b1         ),
    .axi_req_t   ( axi_req_t    ),
    .axi_resp_t  ( axi_resp_t   ),
    .NoMstPorts  ( TbNoMstPorts ),
    .MaxTrans    ( TbMaxTrans   ),
    .AxiLookBits ( 32'd3        ),
    .UniqueIds   ( 1'b0         )
  ) i_dut (
    .clk_i           ( clk       ),
    .rst_ni          ( rst_n     ),
    .slv_req_i       ( slv_req   ),
    .slv_aw_select_i ( 1'b0      ),
    .slv_ar_select_i ( 1'b0      ),
    .slv_resp_o      ( slv_resp  ),
    .mst_reqs_o      ( mst_reqs  ),
    .mst_resps_i     ( mst_resps )
  );

  int unsigned accepted;

  always @(posedge clk) begin
    if (!rst_n) begin
      accepted <= 0;
    end else if (slv_req.ar_valid && slv_resp.ar_ready) begin
      accepted <= accepted + 1;
    end
  end

  initial begin : proc_dump
    if ($test$plusargs("dump")) begin
      $dumpfile("tb_axi_demux_maxtrans.vcd");
      $dumpvars(0, tb_axi_demux_maxtrans);
    end
  end

  initial begin
    drive_ar = 1'b0;
    @(posedge rst_n);
    @(posedge clk);
    drive_ar <= 1'b1;
    // Offer requests long enough for any accepted beat to be counted; the
    // stall point is reached after a handful of cycles.
    repeat (TbNumTxns + 50) @(posedge clk);
    drive_ar <= 1'b0;
    @(posedge clk);
    $display("==================================================================");
    $display("MaxTrans configured: %0d", TbMaxTrans);
    $display("Same-ID reads accepted before stall: %0d", accepted);
    if (accepted < TbMaxTrans) begin
      $display("BUG (issue #249): demux is full at %0d, one below MaxTrans.", accepted);
    end else if (accepted == TbMaxTrans) begin
      $display("OK: accepted count matches configured MaxTrans.");
    end else begin
      $display("NOTE: accepted %0d > MaxTrans %0d (non-pow2 counter slack).",
               accepted, TbMaxTrans);
    end
    $display("==================================================================");
    $finish;
  end

endmodule
