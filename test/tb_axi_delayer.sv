// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Authors:
// - Andreas Kurth <akurth@iis.ee.ethz.ch>
// - Florian Zaruba <zarubaf@iis.ee.ethz.ch>

`include "axi/assign.svh"

module tb_axi_delayer;

  parameter AW = 32;
  parameter DW = 32;
  parameter IW = 8;
  parameter UW = 8;
  parameter TS = 4;

  localparam tCK = 1ns;

  logic clk = 0;
  logic rst = 1;
  logic done = 0;

  AXI_BUS_DV #(
    .AXI_ADDR_WIDTH(AW),
    .AXI_DATA_WIDTH(DW),
    .AXI_ID_WIDTH(IW),
    .AXI_USER_WIDTH(UW)
  ) axi_slave_dv(clk), axi_master_dv(clk);
  AXI_BUS #(
    .AXI_ADDR_WIDTH(AW),
    .AXI_DATA_WIDTH(DW),
    .AXI_ID_WIDTH(IW),
    .AXI_USER_WIDTH(UW)
  ) axi_slave(), axi_master();
  `AXI_ASSIGN(axi_slave_dv, axi_slave)
  `AXI_ASSIGN(axi_master, axi_master_dv)

  axi_delayer_intf #(
    .AXI_ADDR_WIDTH     ( AW ),
    .AXI_DATA_WIDTH     ( DW ),
    .AXI_ID_WIDTH       ( IW ),
    .AXI_USER_WIDTH     ( UW ),
    .FIXED_DELAY_INPUT  ( 0  ),
    .STALL_RANDOM_INPUT ( 1  )
  ) i_axi_delayer (
    .clk_i      ( clk         ),
    .rst_ni     ( rst         ),
    .slv        ( axi_master  ),
    .mst        ( axi_slave   )
  );

  axi_test::axi_driver #(.AW(AW), .DW(DW), .IW(IW), .UW(UW), .TA(200ps), .TT(700ps)) axi_slave_drv = new(axi_slave_dv);
  axi_test::axi_driver #(.AW(AW), .DW(DW), .IW(IW), .UW(UW), .TA(200ps), .TT(700ps)) axi_master_drv = new(axi_master_dv);

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
    automatic axi_test::axi_ax_beat #(.AW(AW), .IW(IW), .UW(UW)) ax_beat = new;
    automatic axi_test::axi_w_beat #(.DW(DW), .UW(UW)) w_beat = new;
    automatic axi_test::axi_b_beat  #(.IW(IW), .UW(UW)) b_beat;
    automatic logic rand_success;
    axi_master_drv.reset_master();
    @(posedge clk);
    repeat (200) begin
        @(posedge clk);
`ifdef XILINX_SIMULATOR
        // std::randomize(ax_beat) may behave differently to ax_beat.randomize() wrt. limited ranges
        // Keeping alternate implementation for XSIM only
        rand_success = std::randomize(ax_beat); assert(rand_success);
`else
        rand_success = ax_beat.randomize(); assert(rand_success);
`endif
        axi_master_drv.send_aw(ax_beat);
        w_beat.w_data = 'hcafebabe;
        axi_master_drv.send_w(w_beat);
    end

    repeat (200) axi_master_drv.recv_b(b_beat);

    done = 1;
  end

  initial begin
    automatic axi_test::axi_ax_beat #(.AW(AW), .IW(IW), .UW(UW)) ax_beat;
    automatic axi_test::axi_w_beat #(.DW(DW), .UW(UW)) w_beat;
    automatic axi_test::axi_b_beat #(.IW(IW), .UW(UW)) b_beat = new;
    automatic int b_id_queue[$];
    axi_slave_drv.reset_slave();
    @(posedge clk);
    repeat (200) begin
        axi_slave_drv.recv_aw(ax_beat);
        $info("AXI AW: addr %h", ax_beat.ax_addr);
        axi_slave_drv.recv_w(w_beat);
        $info("AXI W: data %h, strb %h", w_beat.w_data, w_beat.w_strb);
        b_id_queue.push_back(ax_beat.ax_id);
    end
    while (b_id_queue.size() != 0) begin
      b_beat.b_id = b_id_queue.pop_front();
      axi_slave_drv.send_b(b_beat);
    end
  end
// vsim -voptargs=+acc work.tb_axi_delayer
endmodule
