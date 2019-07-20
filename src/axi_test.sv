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
//
// This file defines the interfaces we support.

import axi_pkg::*;

/// A set of testbench utilities for AXI interfaces.
package axi_test;

  /// A driver for AXI4-Lite interface.
  class axi_lite_driver #(
    parameter int  AW       ,
    parameter int  DW       ,
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

  class rand_axi_master #(
    // AXI interface parameters
    parameter int   AW,
    parameter int   DW,
    parameter int   IW,
    parameter int   UW,
    // Stimuli application and test time
    parameter time  TA,
    parameter time  TT,
    // Maximum number of read and write transactions in flight
    parameter int   MAX_READ_TXNS,
    parameter int   MAX_WRITE_TXNS,
    // Upper and lower bounds on wait cycles on Ax, W, and resp (R and B) channels
    parameter int   AX_MIN_WAIT_CYCLES = 0,
    parameter int   AX_MAX_WAIT_CYCLES = 100,
    parameter int   W_MIN_WAIT_CYCLES = 0,
    parameter int   W_MAX_WAIT_CYCLES = 5,
    parameter int   RESP_MIN_WAIT_CYCLES = 0,
    parameter int   RESP_MAX_WAIT_CYCLES = 20,
    // AXI feature usage
    parameter int   AXI_MAX_BURST_LEN = 0, // maximum number of beats in burst; 0 = AXI max (256)
    parameter int   TRAFFIC_SHAPING = 0,
    parameter bit   AXI_EXCLS = 1'b0,
    parameter bit   AXI_ATOPS = 1'b0,
    // Dependent parameters, do not override.
    parameter int   AXI_STRB_WIDTH = DW/8,
    parameter int   N_AXI_IDS = 2**IW
  );
    typedef axi_test::axi_driver #(
      .AW(AW), .DW(DW), .IW(IW), .UW(UW), .TA(TA), .TT(TT)
    ) axi_driver_t;
    typedef logic [AW-1:0]      addr_t;
    typedef axi_pkg::burst_t    burst_t;
    typedef axi_pkg::cache_t    cache_t;
    typedef logic [DW-1:0]      data_t;
    typedef logic [IW-1:0]      id_t;
    typedef axi_pkg::len_t      len_t;
    typedef axi_pkg::size_t     size_t;
    typedef logic [UW-1:0]      user_t;
    typedef axi_pkg::mem_type_t mem_type_t;

    typedef axi_driver_t::ax_beat_t ax_beat_t;
    typedef axi_driver_t::b_beat_t  b_beat_t;
    typedef axi_driver_t::r_beat_t  r_beat_t;
    typedef axi_driver_t::w_beat_t  w_beat_t;

    static addr_t PFN_MASK = '{11: 1'b0, 10: 1'b0, 9: 1'b0, 8: 1'b0, 7: 1'b0, 6: 1'b0, 5: 1'b0,
        4: 1'b0, 3: 1'b0, 2: 1'b0, 1: 1'b0, 0: 1'b0, default: '1};

    axi_driver_t drv;

    int unsigned          r_flight_cnt[N_AXI_IDS-1:0],
                          w_flight_cnt[N_AXI_IDS-1:0],
                          tot_r_flight_cnt,
                          tot_w_flight_cnt;
    logic [N_AXI_IDS-1:0] atop_resp_b,
                          atop_resp_r;

    len_t                 max_len;

    semaphore cnt_sem;

    ax_beat_t aw_queue[$],
              excl_queue[$];

    typedef struct packed {
      addr_t     addr_begin;
      addr_t     addr_end;
      mem_type_t mem_type;
    } mem_region_t;
    mem_region_t mem_map[$];

    struct packed {
      int unsigned len  ;
      int unsigned cprob;
    } traffic_shape[$];
    int unsigned max_cprob;

    function new(
      virtual AXI_BUS_DV #(
        .AXI_ADDR_WIDTH(AW),
        .AXI_DATA_WIDTH(DW),
        .AXI_ID_WIDTH(IW),
        .AXI_USER_WIDTH(UW)
      ) axi
    );
      if (AXI_MAX_BURST_LEN <= 0 || AXI_MAX_BURST_LEN > 256) begin
        this.max_len = 255;
      end else begin
        this.max_len = AXI_MAX_BURST_LEN - 1;
      end
      this.drv = new(axi);
      this.cnt_sem = new(1);
      this.reset();
    endfunction

    function void reset();
      drv.reset_master();
      r_flight_cnt = '{default: 0};
      w_flight_cnt = '{default: 0};
      tot_r_flight_cnt = 0;
      tot_w_flight_cnt = 0;
      atop_resp_b = '0;
      atop_resp_r = '0;
    endfunction

    function void add_memory_region(input addr_t addr_begin, input addr_t addr_end, input mem_type_t mem_type);
      mem_map.push_back({addr_begin, addr_end, mem_type});
    endfunction

    function void add_traffic_shaping(input int unsigned len, input int unsigned freq);
      if (traffic_shape.size() == 0)
        traffic_shape.push_back({len, freq});
      else
        traffic_shape.push_back({len, traffic_shape[$].cprob + freq});

      max_cprob = traffic_shape[$].cprob;
    endfunction : add_traffic_shaping

    function ax_beat_t new_rand_burst(input logic is_read);
      automatic logic rand_success;
      automatic ax_beat_t ax_beat = new;
      automatic addr_t addr;
      automatic burst_t burst;
      automatic cache_t cache;
      automatic id_t id;
      automatic len_t len;
      automatic size_t size;
      automatic int unsigned mem_region_idx;
      automatic mem_region_t mem_region;
      automatic int cprob;

      // Randomly pick a memory region
      rand_success = std::randomize(mem_region_idx) with {
        mem_region_idx < mem_map.size();
      }; assert(rand_success);
      mem_region = mem_map[mem_region_idx];
      // Randomly pick FIXED or INCR burst.  WRAP is currently not supported.
      rand_success = std::randomize(burst) with {
        burst <= axi_pkg::BURST_INCR;
      }; assert(rand_success);
      ax_beat.ax_burst = burst;
      // Determine memory type.
      ax_beat.ax_cache = is_read ? axi_pkg::get_arcache(mem_region.mem_type) : axi_pkg::get_awcache(mem_region.mem_type);
      // Randomize beat size.
      if (TRAFFIC_SHAPING) begin
        rand_success = std::randomize(cprob) with {
          cprob >= 0; cprob < max_cprob;
        }; assert(rand_success);

        for (int i = 0; i < traffic_shape.size(); i++)
          if (traffic_shape[i].cprob > cprob) begin
            len = traffic_shape[i].len;
            break;
          end

        // Randomize address.  Make sure that the burst does not cross a 4KiB boundary.
        forever begin
          // The largest size possible
          size = $clog2(len);
          if (2**size > AXI_STRB_WIDTH)
            size = $clog2(AXI_STRB_WIDTH);

          ax_beat.ax_size = size;
          ax_beat.ax_len = ((len + (1'b1 << size) - 1) >> size) - 1;

          rand_success = std::randomize(addr) with {
            addr >= mem_region.addr_begin;
            addr <= mem_region.addr_end;
            addr + len <= mem_region.addr_end;
          }; assert(rand_success);

          if (ax_beat.ax_burst == axi_pkg::BURST_FIXED) begin
            if (((addr + 2**ax_beat.ax_size) & PFN_MASK) == (addr & PFN_MASK)) begin
              break;
            end
          end else begin // BURST_INCR
            if (((addr + 2**ax_beat.ax_size * (ax_beat.ax_len + 1)) & PFN_MASK) == (addr & PFN_MASK)) begin
              break;
            end
          end
        end
      end else begin
        // Randomize address.  Make sure that the burst does not cross a 4KiB boundary.
        forever begin
          // Randomize burst length.
          rand_success = std::randomize(len) with {
            len <= this.max_len;
          }; assert(rand_success);
          rand_success = std::randomize(size) with {
            2**size <= AXI_STRB_WIDTH;
          }; assert(rand_success);
          ax_beat.ax_size = size;
          ax_beat.ax_len = len;

          // Randomize address
          rand_success = std::randomize(addr) with {
            addr >= mem_region.addr_begin;
            addr <= mem_region.addr_end;
            addr + ((len + 1) << size) <= mem_region.addr_end;
          }; assert(rand_success);

          if (ax_beat.ax_burst == axi_pkg::BURST_FIXED) begin
            if (((addr + 2**ax_beat.ax_size) & PFN_MASK) == (addr & PFN_MASK)) begin
              break;
            end
          end else begin // BURST_INCR
            if (((addr + 2**ax_beat.ax_size * (ax_beat.ax_len + 1)) & PFN_MASK) == (addr & PFN_MASK)) begin
              break;
            end
          end
        end
      end

      ax_beat.ax_addr = addr;
      forever begin
        rand_success = std::randomize(id); assert(rand_success);
        if (r_flight_cnt[id] == 0 && w_flight_cnt[id] == 0) begin
          break;
        end
      end
      ax_beat.ax_id = id;
      return ax_beat;
    endfunction

    task rand_atop_burst(inout ax_beat_t beat);
      automatic logic rand_success;
      automatic id_t id;
      beat.ax_atop[5:4] = $random();
      if (beat.ax_atop[5:4] != 2'b00) begin // ATOP
        // Determine `ax_atop`.
        if (beat.ax_atop[5:4] == axi_pkg::ATOP_ATOMICSTORE ||
            beat.ax_atop[5:4] == axi_pkg::ATOP_ATOMICLOAD) begin
          beat.ax_atop[5:4] = axi_pkg::ATOP_ATOMICLOAD; // (Do not support stores)
          // Endianness
          beat.ax_atop[3] = $random();
          // Atomic operation
          beat.ax_atop[2:0] = $random();
        end else begin // Atomic{Swap,Compare}
          beat.ax_atop[3:1] = '0;
          //beat.ax_atop[0] = $random(); (Do not support compares)
        end
        // Determine `ax_size` and `ax_len`.
        if (2**beat.ax_size < AXI_STRB_WIDTH) begin
          // Transaction does *not* occupy full data bus, so we must send just one beat. [E2.1.3]
          beat.ax_len = '0;
        end else begin
          automatic int unsigned bytes;
          if (beat.ax_atop == axi_pkg::ATOP_ATOMICCMP) begin
            // Total data transferred in burst can be 2, 4, 8, 16, or 32 B.
            automatic int unsigned log_bytes;
            rand_success = std::randomize(log_bytes) with {
              log_bytes > 0; 2**log_bytes >= AXI_STRB_WIDTH; 2**log_bytes <= 32;
            }; assert(rand_success);
            bytes = 2**log_bytes;
          end else begin
            // Total data transferred in burst can be 1, 2, 4, or 8 B.
            if (AXI_STRB_WIDTH >= 8) begin
              bytes = AXI_STRB_WIDTH;
            end else begin
              automatic int unsigned log_bytes;
              rand_success = std::randomize(log_bytes); assert(rand_success);
              log_bytes = log_bytes % (4 - $clog2(AXI_STRB_WIDTH)) - $clog2(AXI_STRB_WIDTH);
              bytes = 2**log_bytes;
            end
          end
          beat.ax_len = bytes / AXI_STRB_WIDTH - 1;
        end
        // Determine `ax_addr`.
        if (beat.ax_atop == axi_pkg::ATOP_ATOMICCMP) begin
          // The address must be aligned to half the outbound data size. [E2-337]
          beat.ax_addr = beat.ax_addr & ~((1'b1<<beat.ax_size) - 1);
        end else begin
          // The address must be aligned to the data size. [E2-337]
          beat.ax_addr = beat.ax_addr & ~((1'b1<<(beat.ax_size+1)) - 1);
        end
        // Determine `ax_burst`.
        if (beat.ax_atop == axi_pkg::ATOP_ATOMICCMP) begin
          // If the address is aligned to the total size of outgoing data, the burst type must be
          // INCR. Otherwise, it must be WRAP. [E2-338]
          beat.ax_burst = (beat.ax_addr % ((beat.ax_len+1) * 2**beat.ax_size) == 0) ?
              axi_pkg::BURST_INCR : axi_pkg::BURST_WRAP;
        end else begin
          // Only INCR allowed.
          beat.ax_burst = axi_pkg::BURST_INCR;
        end
        // Determine `ax_id`, which must not be the same as that of any other in-flight AXI
        // transaction.
        forever begin
          cnt_sem.get();
          rand_success = std::randomize(id); assert(rand_success);
          if (r_flight_cnt[id] == 0 && w_flight_cnt[id] == 0 && !atop_resp_b[id] &&
              !atop_resp_r[id]) begin
            break;
          end else begin
            // The random ID does not meet the requirements, so try another ID in the next cycle.
            cnt_sem.put();
            rand_wait(1, 1);
          end
        end
        atop_resp_b[id] = 1'b1;
        if (beat.ax_atop[5] == 1'b1) begin
          atop_resp_r[id] = 1'b1;
        end
      end else begin
        // Determine `ax_id`, which must not be the same as that of any in-flight ATOP.
        forever begin
          cnt_sem.get();
          rand_success = std::randomize(id); assert(rand_success);
          if (!atop_resp_b[id] && !atop_resp_r[id]) begin
            break;
          end else begin
            // The random ID does not meet the requirements, so try another ID in the next cycle.
            cnt_sem.put();
            rand_wait(1, 1);
          end
        end
      end
      beat.ax_id = id;
      w_flight_cnt[id]++;
      cnt_sem.put();
    endtask

    function void rand_excl_ar(inout ax_beat_t ar_beat);
      ar_beat.ax_lock = $random();
      if (ar_beat.ax_lock) begin
        automatic logic rand_success;
        automatic int unsigned n_bytes;
        automatic size_t size;
        automatic addr_t addr_mask;
        // In an exclusive burst, the number of bytes to be transferred must be a power of 2, i.e.,
        // 1, 2, 4, 8, 16, 32, 64, or 128 bytes, and the burst length must not exceed 16 transfers.
        static int unsigned ul = (AXI_STRB_WIDTH < 8) ? 4 + $clog2(AXI_STRB_WIDTH) : 7;
        rand_success = std::randomize(n_bytes) with {
          n_bytes >= 1;
          n_bytes <= ul;
        }; assert(rand_success);
        n_bytes = 2**n_bytes;
        rand_success = std::randomize(size) with {
          size >= 0;
          2**size <= n_bytes;
          2**size <= AXI_STRB_WIDTH;
          n_bytes / 2**size <= 16;
        }; assert(rand_success);
        ar_beat.ax_size = size;
        ar_beat.ax_len = n_bytes / 2**size;
        // The address must be aligned to the total number of bytes in the burst.
        ar_beat.ax_addr = ar_beat.ax_addr & ~(n_bytes-1);
      end
    endfunction

    // TODO: The `rand_wait` task exists in `rand_verif_pkg`, but that task cannot be called with
    // `this.drv.axi.clk_i` as `clk` argument. What is the syntax for getting an assignable
    // reference?
    task automatic rand_wait(input int unsigned min, max);
      int unsigned rand_success, cycles;
      rand_success = std::randomize(cycles) with {
        cycles >= min;
        cycles <= max;
      };
      assert (rand_success) else $error("Failed to randomize wait cycles!");
      repeat (cycles) @(posedge this.drv.axi.clk_i);
    endtask

    task send_ars(input int n_reads);
      automatic logic rand_success;
      repeat (n_reads) begin
        automatic id_t id;
        automatic ax_beat_t ar_beat = new_rand_burst(1'b1);
        while (tot_r_flight_cnt >= MAX_READ_TXNS) begin
          rand_wait(1, 1);
        end
        if (AXI_EXCLS) begin
          rand_excl_ar(ar_beat);
        end
        if (AXI_ATOPS) begin
          // The ID must not be the same as that of any in-flight ATOP.
          forever begin
            cnt_sem.get();
            rand_success = std::randomize(id); assert(rand_success);
            if (!atop_resp_b[id] && !atop_resp_r[id]) begin
              break;
            end else begin
              // The random ID does not meet the requirements, so try another ID in the next cycle.
              cnt_sem.put();
              rand_wait(1, 1);
            end
          end
          ar_beat.ax_id = id;
        end else begin
          cnt_sem.get();
        end
        r_flight_cnt[ar_beat.ax_id]++;
        tot_r_flight_cnt++;
        cnt_sem.put();
        rand_wait(AX_MIN_WAIT_CYCLES, AX_MAX_WAIT_CYCLES);
        drv.send_ar(ar_beat);
        if (ar_beat.ax_lock) excl_queue.push_back(ar_beat);
      end
    endtask

    task recv_rs(ref logic ar_done, aw_done);
      while (!(ar_done && tot_r_flight_cnt == 0 &&
          (!AXI_ATOPS || (AXI_ATOPS && aw_done && atop_resp_r == '0))
      )) begin
        automatic r_beat_t r_beat;
        rand_wait(RESP_MIN_WAIT_CYCLES, RESP_MAX_WAIT_CYCLES);
        drv.recv_r(r_beat);
        if (r_beat.r_last) begin
          cnt_sem.get();
          if (atop_resp_r[r_beat.r_id]) begin
            atop_resp_r[r_beat.r_id] = 1'b0;
          end else begin
            r_flight_cnt[r_beat.r_id]--;
            tot_r_flight_cnt--;
          end
          cnt_sem.put();
        end
      end
    endtask

    task send_aws(input int n_writes);
      automatic logic rand_success;
      repeat (n_writes) begin
        automatic bit excl = 1'b0;
        automatic ax_beat_t aw_beat;
        if (AXI_EXCLS && excl_queue.size() > 0) excl = $random();
        if (excl) begin
          aw_beat = excl_queue.pop_front();
        end else begin
          aw_beat = new_rand_burst(1'b0);
        end
        while (tot_w_flight_cnt >= MAX_WRITE_TXNS) begin
          rand_wait(1, 1);
        end
        if (AXI_ATOPS) begin
          if (excl) begin
            // Make sure the exclusive transfer does not have the same ID as an in-flight ATOP.
            forever begin
              cnt_sem.get();
              if (!atop_resp_b[aw_beat.ax_id] && !atop_resp_r[aw_beat.ax_id]) break;
              cnt_sem.put();
              rand_wait(1, 1);
            end
            w_flight_cnt[aw_beat.ax_id]++;
            cnt_sem.put();
          end else begin
            rand_atop_burst(aw_beat);
          end
        end else begin
          cnt_sem.get();
          w_flight_cnt[aw_beat.ax_id]++;
          cnt_sem.put();
        end
        tot_w_flight_cnt++;
        aw_queue.push_back(aw_beat);
        rand_wait(AX_MIN_WAIT_CYCLES, AX_MAX_WAIT_CYCLES);
        drv.send_aw(aw_beat);
      end
    endtask

    task send_ws(ref logic aw_done);
      while (!(aw_done && aw_queue.size() == 0)) begin
        automatic ax_beat_t aw_beat;
        automatic addr_t addr;
        static logic rand_success;
        wait (aw_queue.size() > 0);
        aw_beat = aw_queue.pop_front();
        addr = aw_beat.ax_addr;
        for (int unsigned i = 0; i < aw_beat.ax_len + 1; i++) begin
          automatic w_beat_t w_beat = new;
          automatic int unsigned begin_byte, end_byte, n_bytes;
          automatic logic [AXI_STRB_WIDTH-1:0] rand_strb, strb_mask;
          rand_success = std::randomize(w_beat); assert (rand_success);
          // Determine strobe.
          w_beat.w_strb = '0;
          n_bytes = 2**aw_beat.ax_size;
          begin_byte = addr % AXI_STRB_WIDTH;
          end_byte = ((begin_byte + n_bytes) >> aw_beat.ax_size) << aw_beat.ax_size;
          strb_mask = '0;
          for (int unsigned b = begin_byte; b < end_byte; b++)
            strb_mask[b] = 1'b1;
          rand_success = std::randomize(rand_strb); assert (rand_success);
          w_beat.w_strb |= (rand_strb & strb_mask);
          // Determine last.
          w_beat.w_last = (i == aw_beat.ax_len);
          rand_wait(W_MIN_WAIT_CYCLES, W_MAX_WAIT_CYCLES);
          drv.send_w(w_beat);
          if (aw_beat.ax_burst == axi_pkg::BURST_INCR)
            addr += n_bytes;
        end
      end
    endtask

    task recv_bs(ref logic aw_done);
      while (!(aw_done && tot_w_flight_cnt == 0)) begin
        automatic b_beat_t b_beat;
        rand_wait(RESP_MIN_WAIT_CYCLES, RESP_MAX_WAIT_CYCLES);
        drv.recv_b(b_beat);
        cnt_sem.get();
        if (atop_resp_b[b_beat.b_id]) begin
          atop_resp_b[b_beat.b_id] = 1'b0;
        end
        w_flight_cnt[b_beat.b_id]--;
        tot_w_flight_cnt--;
        cnt_sem.put();
      end
    endtask

    // Issue n_reads random read and n_writes random write transactions to an address range.
    task run(input int n_reads, input int n_writes);
      static logic  ar_done = 1'b0,
                    aw_done = 1'b0;
      fork
        begin
          send_ars(n_reads);
          ar_done = 1'b1;
        end
        recv_rs(ar_done, aw_done);
        begin
          send_aws(n_writes);
          aw_done = 1'b1;
        end
        send_ws(aw_done);
        recv_bs(aw_done);
      join
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
