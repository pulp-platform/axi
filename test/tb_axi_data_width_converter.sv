// Copyright 2019 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// File          : test_axi_data_width_converter.sv
// Author        : Matheus Cavalcante <matheusd@student.ethz.ch>
// Created       : 09.02.2019
//
// Copyright (C) 2019 ETH Zurich, University of Bologna
// All rights reserved.

`include "axi/assign.svh"

module tb_axi_data_width_converter;

  parameter AW  = 32;
  parameter IW  = 8;
  parameter DW  = 32;
  parameter UW  = 8;
  parameter IWO = 4;
  parameter TS  = 4;
  parameter MULT = 8;

  localparam tCK = 1ns;

  logic clk  = 0;
  logic rst  = 1;
  logic done = 0;

  AXI_BUS_DV #(
    .AXI_ADDR_WIDTH ( AW ),
    .AXI_DATA_WIDTH ( MULT * DW ),
    .AXI_ID_WIDTH ( IW ),
    .AXI_USER_WIDTH ( UW )
  ) axi_master_dv ( clk );

  AXI_BUS #(
    .AXI_ADDR_WIDTH ( AW ),
    .AXI_DATA_WIDTH ( MULT * DW ),
    .AXI_ID_WIDTH ( IW ),
    .AXI_USER_WIDTH ( UW )
  ) axi_master();

  axi_test::axi_driver #(
    .AW ( AW ),
    .DW ( MULT * DW ),
    .IW ( IW ),
    .UW ( UW ),
    .TA ( 200ps ),
    .TT ( 700ps )) axi_master_drv = new ( axi_master_dv );

  AXI_BUS_DV #(
    .AXI_ADDR_WIDTH ( AW ),
    .AXI_DATA_WIDTH ( DW ),
    .AXI_ID_WIDTH ( IWO ),
    .AXI_USER_WIDTH ( UW )
    ) axi_slave_dv ( clk );

  AXI_BUS #(
    .AXI_ADDR_WIDTH ( AW ),
    .AXI_DATA_WIDTH ( DW ),
    .AXI_ID_WIDTH ( IWO ),
    .AXI_USER_WIDTH ( UW )
    ) axi_slave ();

  axi_test::axi_driver #(
    .AW ( AW ),
    .DW ( DW ),
    .IW ( IWO ),
    .UW ( UW ),
    .TA ( 200ps ),
    .TT ( 700ps )) axi_slave_drv = new ( axi_slave_dv );

  `AXI_ASSIGN(axi_master, axi_master_dv);
  `AXI_ASSIGN(axi_slave_dv, axi_slave);

  axi_data_width_converter #(
    .MI_DATA_WIDTH ( DW ),
    .SI_DATA_WIDTH ( MULT * DW )
  ) dwc_1 (
    .clk_i ( clk ),
    .rst_ni ( rst ),
    .in ( axi_master ),
    .out ( axi_slave ));

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
  end // initial begin

  initial begin
    axi_master_drv.reset_master();

    @(posedge clk);

    fork
      // AR and R channels
      repeat (200) begin
        automatic axi_test::axi_ax_beat #( .AW ( AW ), .IW ( IW ), .UW ( UW )) ax_beat      = new;
        automatic axi_test::axi_r_beat #( .DW ( MULT * DW ), .IW ( IW ), .UW ( UW )) r_beat = new;

        @(posedge clk);
        void'(randomize(ax_beat));
        ax_beat.ax_burst = axi_pkg::BURST_INCR;
        ax_beat.ax_cache = axi_pkg::CACHE_MODIFIABLE;
        ax_beat.ax_len   = $urandom();

        ax_beat.ax_size  = $urandom();
        if (ax_beat.ax_size > $clog2(DW/8))
          ax_beat.ax_size = $clog2(DW/8);

        axi_master_drv.send_ar(ax_beat);

        for (int beat = 0; beat <= ax_beat.ax_len; beat++) begin
          axi_master_drv.recv_r(r_beat);
          $info("AXI R: data %h", r_beat.r_data);
        end
      end

      // AW and W channels
      repeat (200) begin
        automatic axi_test::axi_ax_beat #( .AW ( AW ), .IW ( IW ), .UW ( UW )) ax_beat = new;
        automatic axi_test::axi_w_beat #( .DW ( MULT * DW ), .UW ( UW )) w_beat        = new;

        @(posedge clk);
        void'(randomize(ax_beat));
        ax_beat.ax_burst = axi_pkg::BURST_INCR;
        ax_beat.ax_cache = axi_pkg::CACHE_MODIFIABLE;
        ax_beat.ax_size  = $urandom();

        ax_beat.ax_len   = $urandom();
        if (ax_beat.ax_size > $clog2(DW/8))
          ax_beat.ax_size = $clog2(DW/8);

        axi_master_drv.send_aw(ax_beat);

        w_beat.w_data  = {MULT{32'hcafebabe}};
        w_beat.w_strb  = '1;
        for (int beat = 0; beat <= ax_beat.ax_len; beat++) begin
          if (beat == ax_beat.ax_len)
            w_beat.w_last = 1'b1;
          axi_master_drv.send_w(w_beat);
        end
      end

      // B channel
      repeat (200) begin
        automatic axi_test::axi_b_beat #( .IW ( IW ), .UW ( UW )) b_beat = new;
        axi_master_drv.recv_b(b_beat);
      end
    join

    done = 1;
  end

  initial begin
    automatic int b_id_queue[$];
    axi_slave_drv.reset_slave();

    @(posedge clk);

    fork
      // AR and R channels
      repeat (200) begin
        automatic axi_test::axi_ax_beat #( .AW ( AW ), .IW ( IWO ), .UW ( UW )) ax_beat    = new;
        automatic axi_test::axi_r_beat #( .DW ( DW ), .IW ( IWO), .UW( UW )) r_beat = new;

        axi_slave_drv.recv_ar(ax_beat);
        $info("AXI AR: addr %h", ax_beat.ax_addr);

        r_beat.r_data = 32'hdeadcafe;
        for (int beat = 0; beat <= ax_beat.ax_len; beat++) begin
          if (beat == ax_beat.ax_len)
            r_beat.r_last = 1'b1;
          axi_slave_drv.send_r(r_beat);
        end
      end

      // AW and W channels
      repeat (200) begin
        automatic axi_test::axi_ax_beat #( .AW ( AW ), .IW ( IWO ), .UW ( UW )) ax_beat = new;
        automatic axi_test::axi_w_beat #( .DW ( DW ), .UW( UW )) w_beat          = new;

        axi_slave_drv.recv_aw(ax_beat);
        $info("AXI AW: addr %h", ax_beat.ax_addr);

        for (int beat = 0; beat <= ax_beat.ax_len; beat++) begin
          axi_slave_drv.recv_w(w_beat);
          $info("AXI W: data %h, strb %h", w_beat.w_data, w_beat.w_strb);
        end

        b_id_queue.push_back(ax_beat.ax_id);
      end
    join

    // B channel
    while (b_id_queue.size() != 0) begin
      automatic axi_test::axi_b_beat #( .IW ( IWO ), .UW ( UW )) b_beat = new;

      b_beat.b_id = b_id_queue.pop_front();
      axi_slave_drv.send_b(b_beat);
    end
  end

  // vsim -voptargs=+acc work.tb_axi_data_width_converter
endmodule // tb_axi_data_width_converter
