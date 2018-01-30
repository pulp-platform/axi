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

module tb_axi_to_axi_lite;

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

  axi_to_axi_lite i_dut (
    .clk_i  ( clk      ),
    .rst_ni ( rst      ),
    .slave  ( axi      ),
    .master ( axi_lite )
  );

  typedef axi_test::axi_lite_driver #(.AW(AW), .DW(DW)) axi_lite_drv_t;
  typedef axi_test::axi_driver #(.AW(AW), .DW(DW), .IW(IW), .UW(UW)) axi_drv_t;
  axi_lite_drv_t axi_lite_drv = new(axi_lite);
  axi_drv_t axi_drv = new(axi);

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
    automatic axi_drv_t::ax_beat_t ax = new;
    automatic axi_drv_t::w_beat_t w = new;
    automatic axi_drv_t::b_beat_t b = new;
    automatic axi_drv_t::r_beat_t r = new;
    axi_drv.reset_master();
    @(posedge clk);

    ax.randomize();
    w.randomize();
    axi_drv.send_aw(ax);
    axi_drv.send_w(w);
    axi_drv.recv_b(b);

    ax.randomize();
    axi_drv.send_ar(ax);
    axi_drv.recv_r(r);

    repeat (4) @(posedge clk);
    done = 1;
  end

  initial begin
    automatic logic [AW-1:0] addr;
    automatic logic [DW-1:0] data;
    automatic logic [DW/8-1:0] strb;

    axi_lite_drv.reset_slave();
    @(posedge clk);

    axi_lite_drv.recv_aw(addr);
    axi_lite_drv.recv_w(data, strb);
    axi_lite_drv.send_b(axi_pkg::RESP_OKAY);

    axi_lite_drv.recv_ar(addr);
    axi_lite_drv.send_r('0, axi_pkg::RESP_OKAY);
  end

endmodule
