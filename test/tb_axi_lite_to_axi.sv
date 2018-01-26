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

module tb_axi_lite_to_axi;

  parameter AW = 32;
  parameter DW = 32;
  parameter IW = 8;
  parameter UW = 8;

  localparam tCK = 1ns;

  logic clk = 0;
  logic rst = 1;
  logic done = 0;

  AXI_LITE #(
    .AXI_ADDR_WIDTH(AW),
    .AXI_DATA_WIDTH(DW)
  ) axi_lite(clk);

  AXI_BUS #(
    .AXI_ADDR_WIDTH(AW),
    .AXI_DATA_WIDTH(DW),
    .AXI_ID_WIDTH(IW),
    .AXI_USER_WIDTH(UW)
  ) axi(clk);

  axi_lite_to_axi i_dut (
    .slave  ( axi_lite ),
    .master ( axi      )
  );

  axi_test::axi_lite_driver #(.AW(AW), .DW(DW)) axi_lite_drv = new(axi_lite);
  axi_test::axi_driver #(.AW(AW), .DW(DW), .IW(IW), .UW(UW)) axi_drv = new(axi);

  initial begin
    #tCK;
    rst <= 0;
    #tCK;
    rst <= 1;
    #tCK;
    while (!done) begin
      clk <= 1;
      #(tCK/2);
      clk <= 0;
      #(tCK/2);
    end
  end

  initial begin
    automatic axi_pkg::resp_t resp;
    axi_lite_drv.reset_master();
    @(posedge clk);
    axi_lite_drv.send_aw('hdeadbeef);
    axi_lite_drv.send_w('hdeadbeef, '1);
    axi_lite_drv.recv_b(resp);
    $info("AXI-Lite B: resp %h", resp);
    repeat (4) @(posedge clk);
    done = 1;
  end

  initial begin
    automatic axi_test::axi_ax_beat #(.AW(AW), .IW(IW), .UW(UW)) ax_beat;
    automatic axi_test::axi_w_beat #(.DW(DW), .UW(UW)) w_beat;
    automatic axi_test::axi_b_beat #(.IW(IW), .UW(UW)) b_beat = new;
    axi_drv.reset_slave();
    @(posedge clk);
    axi_drv.recv_aw(ax_beat);
    $info("AXI AW: addr %h", ax_beat.ax_addr);
    axi_drv.recv_w(w_beat);
    $info("AXI W: data %h, strb %h", w_beat.w_data, w_beat.w_strb);
    axi_drv.send_b(b_beat);
  end

endmodule
