// Copyright (c) 2014-2018 ETH Zurich, University of Bologna
//
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Fabian Schuiki <fschuiki@iis.ee.ethz.ch>
// Andreas Kurth  <akurth@iis.ee.ethz.ch>
//
// This file defines the interfaces we support.


/// A set of testbench utilities for AXI interfaces.
package axi_test;

  import axi_pkg::*;

  /// A driver for AXI4-Lite interface.
  class axi_lite_driver #(
    parameter int  AW = 32  ,
    parameter int  DW = 32  ,
    parameter time TA = 0ns , // stimuli application time
    parameter time TT = 0ns   // stimuli test time
  );
    virtual AXI_LITE_DV #(
      .AXI_ADDR_WIDTH(AW),
      .AXI_DATA_WIDTH(DW)
    ) axi;

    function new(
      virtual AXI_LITE_DV #(
        .AXI_ADDR_WIDTH(AW),
        .AXI_DATA_WIDTH(DW)
      ) axi
    );
      this.axi = axi;
    endfunction

    function void reset_master();
      axi.aw_addr  <= '0;
      axi.aw_valid <= '0;
      axi.w_valid  <= '0;
      axi.w_data   <= '0;
      axi.w_strb   <= '0;
      axi.b_ready  <= '0;
      axi.ar_valid <= '0;
      axi.ar_addr  <= '0;
      axi.r_ready  <= '0;
    endfunction

    function void reset_slave();
      axi.aw_ready <= '0;
      axi.w_ready  <= '0;
      axi.b_resp   <= '0;
      axi.b_valid  <= '0;
      axi.ar_ready <= '0;
      axi.r_data   <= '0;
      axi.r_resp   <= '0;
      axi.r_valid  <= '0;
    endfunction

    task cycle_start;
      #TT;
    endtask

    task cycle_end;
      @(posedge axi.clk_i);
    endtask

    /// Issue a beat on the AW channel.
    task send_aw (
      input logic [AW-1:0] addr
    );
      axi.aw_addr  <= #TA addr;
      axi.aw_valid <= #TA 1;
      cycle_start();
      while (axi.aw_ready != 1) begin cycle_end(); cycle_start(); end
      cycle_end();
      axi.aw_addr  <= #TA '0;
      axi.aw_valid <= #TA 0;
    endtask

    /// Issue a beat on the W channel.
    task send_w (
      input logic [DW-1:0] data,
      input logic [DW/8-1:0] strb
    );
      axi.w_data  <= #TA data;
      axi.w_strb  <= #TA strb;
      axi.w_valid <= #TA 1;
      cycle_start();
      while (axi.w_ready != 1) begin cycle_end(); cycle_start(); end
      cycle_end();
      axi.w_data  <= #TA '0;
      axi.w_strb  <= #TA '0;
      axi.w_valid <= #TA 0;
    endtask

    /// Issue a beat on the B channel.
    task send_b (
      input axi_pkg::resp_t resp
    );
      axi.b_resp  <= #TA resp;
      axi.b_valid <= #TA 1;
      cycle_start();
      while (axi.b_ready != 1) begin cycle_end(); cycle_start(); end
      cycle_end();
      axi.b_resp  <= #TA '0;
      axi.b_valid <= #TA 0;
    endtask

    /// Issue a beat on the AR channel.
    task send_ar (
      input logic [AW-1:0] addr
    );
      axi.ar_addr  <= #TA addr;
      axi.ar_valid <= #TA 1;
      cycle_start();
      while (axi.ar_ready != 1) begin cycle_end(); cycle_start(); end
      cycle_end();
      axi.ar_addr  <= #TA '0;
      axi.ar_valid <= #TA 0;
    endtask

    /// Issue a beat on the R channel.
    task send_r (
      input logic [DW-1:0] data,
      input axi_pkg::resp_t resp
    );
      axi.r_data  <= #TA data;
      axi.r_resp  <= #TA resp;
      axi.r_valid <= #TA 1;
      cycle_start();
      while (axi.r_ready != 1) begin cycle_end(); cycle_start(); end
      cycle_end();
      axi.r_data  <= #TA '0;
      axi.r_resp  <= #TA '0;
      axi.r_valid <= #TA 0;
    endtask

    /// Wait for a beat on the AW channel.
    task recv_aw (
      output [AW-1:0] addr
    );
      axi.aw_ready <= #TA 1;
      cycle_start();
      while (axi.aw_valid != 1) begin cycle_end(); cycle_start(); end
      addr = axi.aw_addr;
      cycle_end();
      axi.aw_ready <= #TA 0;
    endtask

    /// Wait for a beat on the W channel.
    task recv_w (
      output [DW-1:0] data,
      output [DW/8-1:0] strb
    );
      axi.w_ready <= #TA 1;
      cycle_start();
      while (axi.w_valid != 1) begin cycle_end(); cycle_start(); end
      data = axi.w_data;
      strb = axi.w_strb;
      cycle_end();
      axi.w_ready <= #TA 0;
    endtask

    /// Wait for a beat on the B channel.
    task recv_b (
      output axi_pkg::resp_t resp
    );
      axi.b_ready <= #TA 1;
      cycle_start();
      while (axi.b_valid != 1) begin cycle_end(); cycle_start(); end
      resp = axi.b_resp;
      cycle_end();
      axi.b_ready <= #TA 0;
    endtask

    /// Wait for a beat on the AR channel.
    task recv_ar (
      output [AW-1:0] addr
    );
      axi.ar_ready <= #TA 1;
      cycle_start();
      while (axi.ar_valid != 1) begin cycle_end(); cycle_start(); end
      addr = axi.ar_addr;
      cycle_end();
      axi.ar_ready <= #TA 0;
    endtask

    /// Wait for a beat on the R channel.
    task recv_r (
      output [DW-1:0] data,
      output axi_pkg::resp_t resp
    );
      axi.r_ready <= #TA 1;
      cycle_start();
      while (axi.r_valid != 1) begin cycle_end(); cycle_start(); end
      data = axi.r_data;
      resp = axi.r_resp;
      cycle_end();
      axi.r_ready <= #TA 0;
    endtask

  endclass


  /// The data transferred on a beat on the AW/AR channels.
  class axi_ax_beat #(
    parameter AW,
    parameter IW,
    parameter UW
  );
    rand logic [IW-1:0] ax_id     = '0;
    rand logic [AW-1:0] ax_addr   = '0;
    logic [7:0]         ax_len    = '0;
    logic [2:0]         ax_size   = '0;
    logic [1:0]         ax_burst  = '0;
    logic               ax_lock   = '0;
    logic [3:0]         ax_cache  = '0;
    logic [2:0]         ax_prot   = '0;
    logic [3:0]         ax_qos    = '0;
    logic [3:0]         ax_region = '0;
    logic [5:0]         ax_atop   = '0; // Only defined on the AW channel.
    rand logic [UW-1:0] ax_user   = '0;
  endclass

  /// The data transferred on a beat on the W channel.
  class axi_w_beat #(
    parameter DW,
    parameter UW
  );
    rand logic [DW-1:0]   w_data = '0;
    rand logic [DW/8-1:0] w_strb = '0;
    logic                 w_last = '0;
    rand logic [UW-1:0]   w_user = '0;
  endclass

  /// The data transferred on a beat on the B channel.
  class axi_b_beat #(
    parameter IW,
    parameter UW
  );
    rand logic [IW-1:0] b_id   = '0;
    axi_pkg::resp_t     b_resp = '0;
    rand logic [UW-1:0] b_user = '0;
  endclass

  /// The data transferred on a beat on the R channel.
  class axi_r_beat #(
    parameter DW,
    parameter IW,
    parameter UW
  );
    rand logic [IW-1:0] r_id   = '0;
    rand logic [DW-1:0] r_data = '0;
    axi_pkg::resp_t     r_resp = '0;
    logic               r_last = '0;
    rand logic [UW-1:0] r_user = '0;
  endclass


  /// A driver for AXI4 interface.
  class axi_driver #(
    parameter int  AW       ,
    parameter int  DW       ,
    parameter int  IW       ,
    parameter int  UW       ,
    parameter time TA = 0ns , // stimuli application time
    parameter time TT = 0ns   // stimuli test time
  );
    virtual AXI_BUS_DV #(
      .AXI_ADDR_WIDTH(AW),
      .AXI_DATA_WIDTH(DW),
      .AXI_ID_WIDTH(IW),
      .AXI_USER_WIDTH(UW)
    ) axi;

    typedef axi_ax_beat #(.AW(AW), .IW(IW), .UW(UW)) ax_beat_t;
    typedef axi_w_beat  #(.DW(DW), .UW(UW))          w_beat_t;
    typedef axi_b_beat  #(.IW(IW), .UW(UW))          b_beat_t;
    typedef axi_r_beat  #(.DW(DW), .IW(IW), .UW(UW)) r_beat_t;

    function new(
      virtual AXI_BUS_DV #(
        .AXI_ADDR_WIDTH(AW),
        .AXI_DATA_WIDTH(DW),
        .AXI_ID_WIDTH(IW),
        .AXI_USER_WIDTH(UW)
      ) axi
    );
      this.axi = axi;
    endfunction

    function void reset_master();
      axi.aw_id     <= '0;
      axi.aw_addr   <= '0;
      axi.aw_len    <= '0;
      axi.aw_size   <= '0;
      axi.aw_burst  <= '0;
      axi.aw_lock   <= '0;
      axi.aw_cache  <= '0;
      axi.aw_prot   <= '0;
      axi.aw_qos    <= '0;
      axi.aw_region <= '0;
      axi.aw_atop   <= '0;
      axi.aw_user   <= '0;
      axi.aw_valid  <= '0;
      axi.w_data    <= '0;
      axi.w_strb    <= '0;
      axi.w_last    <= '0;
      axi.w_user    <= '0;
      axi.w_valid   <= '0;
      axi.b_ready   <= '0;
      axi.ar_id     <= '0;
      axi.ar_addr   <= '0;
      axi.ar_len    <= '0;
      axi.ar_size   <= '0;
      axi.ar_burst  <= '0;
      axi.ar_lock   <= '0;
      axi.ar_cache  <= '0;
      axi.ar_prot   <= '0;
      axi.ar_qos    <= '0;
      axi.ar_region <= '0;
      axi.ar_user   <= '0;
      axi.ar_valid  <= '0;
      axi.r_ready   <= '0;
    endfunction

    function void reset_slave();
      axi.aw_ready  <= '0;
      axi.w_ready   <= '0;
      axi.b_id      <= '0;
      axi.b_resp    <= '0;
      axi.b_user    <= '0;
      axi.b_valid   <= '0;
      axi.ar_ready  <= '0;
      axi.r_id      <= '0;
      axi.r_data    <= '0;
      axi.r_resp    <= '0;
      axi.r_last    <= '0;
      axi.r_user    <= '0;
      axi.r_valid   <= '0;
    endfunction

    task cycle_start;
      #TT;
    endtask

    task cycle_end;
      @(posedge axi.clk_i);
    endtask

    /// Issue a beat on the AW channel.
    task send_aw (
      input ax_beat_t beat
    );
      axi.aw_id     <= #TA beat.ax_id;
      axi.aw_addr   <= #TA beat.ax_addr;
      axi.aw_len    <= #TA beat.ax_len;
      axi.aw_size   <= #TA beat.ax_size;
      axi.aw_burst  <= #TA beat.ax_burst;
      axi.aw_lock   <= #TA beat.ax_lock;
      axi.aw_cache  <= #TA beat.ax_cache;
      axi.aw_prot   <= #TA beat.ax_prot;
      axi.aw_qos    <= #TA beat.ax_qos;
      axi.aw_region <= #TA beat.ax_region;
      axi.aw_atop   <= #TA beat.ax_atop;
      axi.aw_user   <= #TA beat.ax_user;
      axi.aw_valid  <= #TA 1;
      cycle_start();
      while (axi.aw_ready != 1) begin cycle_end(); cycle_start(); end
      cycle_end();
      axi.aw_id     <= #TA '0;
      axi.aw_addr   <= #TA '0;
      axi.aw_len    <= #TA '0;
      axi.aw_size   <= #TA '0;
      axi.aw_burst  <= #TA '0;
      axi.aw_lock   <= #TA '0;
      axi.aw_cache  <= #TA '0;
      axi.aw_prot   <= #TA '0;
      axi.aw_qos    <= #TA '0;
      axi.aw_region <= #TA '0;
      axi.aw_atop   <= #TA '0;
      axi.aw_user   <= #TA '0;
      axi.aw_valid  <= #TA 0;
    endtask

    /// Issue a beat on the W channel.
    task send_w (
      input w_beat_t beat
    );
      axi.w_data  <= #TA beat.w_data;
      axi.w_strb  <= #TA beat.w_strb;
      axi.w_last  <= #TA beat.w_last;
      axi.w_user  <= #TA beat.w_user;
      axi.w_valid <= #TA 1;
      cycle_start();
      while (axi.w_ready != 1) begin cycle_end(); cycle_start(); end
      cycle_end();
      axi.w_data  <= #TA '0;
      axi.w_strb  <= #TA '0;
      axi.w_last  <= #TA '0;
      axi.w_user  <= #TA '0;
      axi.w_valid <= #TA 0;
    endtask

    /// Issue a beat on the B channel.
    task send_b (
      input b_beat_t beat
    );
      axi.b_id    <= #TA beat.b_id;
      axi.b_resp  <= #TA beat.b_resp;
      axi.b_user  <= #TA beat.b_user;
      axi.b_valid <= #TA 1;
      cycle_start();
      while (axi.b_ready != 1) begin cycle_end(); cycle_start(); end
      cycle_end();
      axi.b_id    <= #TA '0;
      axi.b_resp  <= #TA '0;
      axi.b_user  <= #TA '0;
      axi.b_valid <= #TA 0;
    endtask

    /// Issue a beat on the AR channel.
    task send_ar (
      input ax_beat_t beat
    );
      axi.ar_id     <= #TA beat.ax_id;
      axi.ar_addr   <= #TA beat.ax_addr;
      axi.ar_len    <= #TA beat.ax_len;
      axi.ar_size   <= #TA beat.ax_size;
      axi.ar_burst  <= #TA beat.ax_burst;
      axi.ar_lock   <= #TA beat.ax_lock;
      axi.ar_cache  <= #TA beat.ax_cache;
      axi.ar_prot   <= #TA beat.ax_prot;
      axi.ar_qos    <= #TA beat.ax_qos;
      axi.ar_region <= #TA beat.ax_region;
      axi.ar_user   <= #TA beat.ax_user;
      axi.ar_valid  <= #TA 1;
      cycle_start();
      while (axi.ar_ready != 1) begin cycle_end(); cycle_start(); end
      cycle_end();
      axi.ar_id     <= #TA '0;
      axi.ar_addr   <= #TA '0;
      axi.ar_len    <= #TA '0;
      axi.ar_size   <= #TA '0;
      axi.ar_burst  <= #TA '0;
      axi.ar_lock   <= #TA '0;
      axi.ar_cache  <= #TA '0;
      axi.ar_prot   <= #TA '0;
      axi.ar_qos    <= #TA '0;
      axi.ar_region <= #TA '0;
      axi.ar_user   <= #TA '0;
      axi.ar_valid  <= #TA 0;
    endtask

    /// Issue a beat on the R channel.
    task send_r (
      input r_beat_t beat
    );
      axi.r_id    <= #TA beat.r_id;
      axi.r_data  <= #TA beat.r_data;
      axi.r_resp  <= #TA beat.r_resp;
      axi.r_last  <= #TA beat.r_last;
      axi.r_user  <= #TA beat.r_user;
      axi.r_valid <= #TA 1;
      cycle_start();
      while (axi.r_ready != 1) begin cycle_end(); cycle_start(); end
      cycle_end();
      axi.r_id    <= #TA '0;
      axi.r_data  <= #TA '0;
      axi.r_resp  <= #TA '0;
      axi.r_last  <= #TA '0;
      axi.r_user  <= #TA '0;
      axi.r_valid <= #TA 0;
    endtask

    /// Wait for a beat on the AW channel.
    task recv_aw (
      output ax_beat_t beat
    );
      axi.aw_ready <= #TA 1;
      cycle_start();
      while (axi.aw_valid != 1) begin cycle_end(); cycle_start(); end
      beat = new;
      beat.ax_id     = axi.aw_id;
      beat.ax_addr   = axi.aw_addr;
      beat.ax_len    = axi.aw_len;
      beat.ax_size   = axi.aw_size;
      beat.ax_burst  = axi.aw_burst;
      beat.ax_lock   = axi.aw_lock;
      beat.ax_cache  = axi.aw_cache;
      beat.ax_prot   = axi.aw_prot;
      beat.ax_qos    = axi.aw_qos;
      beat.ax_region = axi.aw_region;
      beat.ax_atop   = axi.aw_atop;
      beat.ax_user   = axi.aw_user;
      cycle_end();
      axi.aw_ready <= #TA 0;
    endtask

    /// Wait for a beat on the W channel.
    task recv_w (
      output w_beat_t beat
    );
      axi.w_ready <= #TA 1;
      cycle_start();
      while (axi.w_valid != 1) begin cycle_end(); cycle_start(); end
      beat = new;
      beat.w_data = axi.w_data;
      beat.w_strb = axi.w_strb;
      beat.w_last = axi.w_last;
      beat.w_user = axi.w_user;
      cycle_end();
      axi.w_ready <= #TA 0;
    endtask

    /// Wait for a beat on the B channel.
    task recv_b (
      output b_beat_t beat
    );
      axi.b_ready <= #TA 1;
      cycle_start();
      while (axi.b_valid != 1) begin cycle_end(); cycle_start(); end
      beat = new;
      beat.b_id   = axi.b_id;
      beat.b_resp = axi.b_resp;
      beat.b_user = axi.b_user;
      cycle_end();
      axi.b_ready <= #TA 0;
    endtask

    /// Wait for a beat on the AR channel.
    task recv_ar (
      output ax_beat_t beat
    );
      axi.ar_ready  <= #TA 1;
      cycle_start();
      while (axi.ar_valid != 1) begin cycle_end(); cycle_start(); end
      beat = new;
      beat.ax_id     = axi.ar_id;
      beat.ax_addr   = axi.ar_addr;
      beat.ax_len    = axi.ar_len;
      beat.ax_size   = axi.ar_size;
      beat.ax_burst  = axi.ar_burst;
      beat.ax_lock   = axi.ar_lock;
      beat.ax_cache  = axi.ar_cache;
      beat.ax_prot   = axi.ar_prot;
      beat.ax_qos    = axi.ar_qos;
      beat.ax_region = axi.ar_region;
      beat.ax_atop   = 'X;  // Not defined on the AR channel.
      beat.ax_user   = axi.ar_user;
      cycle_end();
      axi.ar_ready  <= #TA 0;
    endtask

    /// Wait for a beat on the R channel.
    task recv_r (
      output r_beat_t beat
    );
      axi.r_ready <= #TA 1;
      cycle_start();
      while (axi.r_valid != 1) begin cycle_end(); cycle_start(); end
      beat = new;
      beat.r_id   = axi.r_id;
      beat.r_data = axi.r_data;
      beat.r_resp = axi.r_resp;
      beat.r_last = axi.r_last;
      beat.r_user = axi.r_user;
      cycle_end();
      axi.r_ready <= #TA 0;
    endtask

  endclass

  class rand_axi_slave #(
    // AXI interface parameters
    parameter int   AW,
    parameter int   DW,
    parameter int   IW,
    parameter int   UW,
    // Stimuli application and test time
    parameter time  TA,
    parameter time  TT,
    // Upper and lower bounds on wait cycles on Ax, W, and resp (R and B) channels
    parameter int   AX_MIN_WAIT_CYCLES = 0,
    parameter int   AX_MAX_WAIT_CYCLES = 100,
    parameter int   R_MIN_WAIT_CYCLES = 0,
    parameter int   R_MAX_WAIT_CYCLES = 5,
    parameter int   RESP_MIN_WAIT_CYCLES = 0,
    parameter int   RESP_MAX_WAIT_CYCLES = 20
  );
    typedef axi_test::axi_driver #(
      .AW(AW), .DW(DW), .IW(IW), .UW(UW), .TA(TA), .TT(TT)
    ) axi_driver_t;
    typedef rand_id_queue_pkg::rand_id_queue #(
      .data_t   (axi_driver_t::ax_beat_t),
      .ID_WIDTH (IW)
    ) rand_ax_beat_queue_t;
    typedef axi_driver_t::ax_beat_t ax_beat_t;
    typedef axi_driver_t::b_beat_t b_beat_t;
    typedef axi_driver_t::r_beat_t r_beat_t;
    typedef axi_driver_t::w_beat_t w_beat_t;

    axi_driver_t          drv;
    rand_ax_beat_queue_t  ar_queue,
                          b_queue;
    ax_beat_t             aw_queue[$];

    function new(
      virtual AXI_BUS_DV #(
        .AXI_ADDR_WIDTH(AW),
        .AXI_DATA_WIDTH(DW),
        .AXI_ID_WIDTH(IW),
        .AXI_USER_WIDTH(UW)
      ) axi
    );
      this.drv = new(axi);
      this.ar_queue = new;
      this.b_queue = new;
    endfunction

    function void reset();
      drv.reset_slave();
    endfunction

    // TODO: The `rand_wait` task exists in `rand_verif_pkg`, but that task cannot be called with
    // `this.drv.axi.clk_i` as `clk` argument.  What is the syntax getting an assignable reference?
    task automatic rand_wait(input int unsigned min, max);
      int unsigned rand_success, cycles;
      rand_success = std::randomize(cycles) with {
        cycles >= min;
        cycles <= max;
      };
      assert (rand_success) else $error("Failed to randomize wait cycles!");
      repeat (cycles) @(posedge this.drv.axi.clk_i);
    endtask

    task recv_ars();
      forever begin
        automatic ax_beat_t ar_beat;
        rand_wait(AX_MIN_WAIT_CYCLES, AX_MAX_WAIT_CYCLES);
        drv.recv_ar(ar_beat);
        ar_queue.push(ar_beat.ax_id, ar_beat);
      end
    endtask

    task send_rs();
      forever begin
        automatic logic rand_success;
        automatic ax_beat_t ar_beat;
        automatic r_beat_t r_beat = new;
        wait (!ar_queue.empty());
        ar_beat = ar_queue.peek();
        rand_success = std::randomize(r_beat); assert(rand_success);
        r_beat.r_id = ar_beat.ax_id;
        if (ar_beat.ax_lock)
          r_beat.r_resp[0]= $random();
        rand_wait(R_MIN_WAIT_CYCLES, R_MAX_WAIT_CYCLES);
        if (ar_beat.ax_len == '0) begin
          r_beat.r_last = 1'b1;
          void'(ar_queue.pop_id(ar_beat.ax_id));
        end else begin
          ar_beat.ax_len--;
          ar_queue.set(ar_beat.ax_id, ar_beat);
        end
        drv.send_r(r_beat);
      end
    endtask

    task recv_aws();
      forever begin
        automatic ax_beat_t aw_beat;
        rand_wait(AX_MIN_WAIT_CYCLES, AX_MAX_WAIT_CYCLES);
        drv.recv_aw(aw_beat);
        aw_queue.push_back(aw_beat);
        // Atomic{Load,Swap,Compare}s require an R response.
        if (aw_beat.ax_atop[5]) begin
          ar_queue.push(aw_beat.ax_id, aw_beat);
        end
      end
    endtask

    task recv_ws();
      forever begin
        automatic ax_beat_t aw_beat;
        forever begin
          automatic w_beat_t w_beat;
          rand_wait(RESP_MIN_WAIT_CYCLES, RESP_MAX_WAIT_CYCLES);
          drv.recv_w(w_beat);
          if (w_beat.w_last)
            break;
        end
        wait (aw_queue.size() > 0);
        aw_beat = aw_queue.pop_front();
        b_queue.push(aw_beat.ax_id, aw_beat);
      end
    endtask

    task send_bs();
      forever begin
        automatic ax_beat_t aw_beat;
        automatic b_beat_t b_beat = new;
        automatic logic rand_success;
        wait (!b_queue.empty());
        aw_beat = b_queue.pop();
        rand_success = std::randomize(b_beat); assert(rand_success);
        b_beat.b_id = aw_beat.ax_id;
        if (aw_beat.ax_lock) begin
          b_beat.b_resp[0]= $random();
        end
        rand_wait(RESP_MIN_WAIT_CYCLES, RESP_MAX_WAIT_CYCLES);
        drv.send_b(b_beat);
      end
    endtask

    task run();
      fork
        recv_ars();
        send_rs();
        recv_aws();
        recv_ws();
        send_bs();
      join
    endtask

  endclass

endpackage
