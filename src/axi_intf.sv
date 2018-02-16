// Copyright (c) 2014-2018 ETH Zurich, University of Bologna
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
//
// This file defines the interfaces we support.

import axi_pkg::*;


/// An AXI4 interface.
interface AXI_BUS #(
  parameter AXI_ADDR_WIDTH = -1,
  parameter AXI_DATA_WIDTH = -1,
  parameter AXI_ID_WIDTH   = -1,
  parameter AXI_USER_WIDTH = -1
)(
  input logic clk_i
);

  localparam AXI_STRB_WIDTH = AXI_DATA_WIDTH / 8;

  typedef logic [AXI_ID_WIDTH-1:0]   id_t;
  typedef logic [AXI_ADDR_WIDTH-1:0] addr_t;
  typedef logic [AXI_DATA_WIDTH-1:0] data_t;
  typedef logic [AXI_STRB_WIDTH-1:0] strb_t;
  typedef logic [AXI_USER_WIDTH-1:0] user_t;

  id_t        aw_id;
  addr_t      aw_addr;
  logic [7:0] aw_len;
  logic [2:0] aw_size;
  burst_t     aw_burst;
  logic       aw_lock;
  cache_t     aw_cache;
  prot_t      aw_prot;
  qos_t       aw_qos;
  region_t    aw_region;
  user_t      aw_user;
  logic       aw_valid;
  logic       aw_ready;

  data_t      w_data;
  strb_t      w_strb;
  logic       w_last;
  user_t      w_user;
  logic       w_valid;
  logic       w_ready;

  id_t        b_id;
  resp_t      b_resp;
  user_t      b_user;
  logic       b_valid;
  logic       b_ready;

  id_t        ar_id;
  addr_t      ar_addr;
  logic [7:0] ar_len;
  logic [2:0] ar_size;
  burst_t     ar_burst;
  logic       ar_lock;
  cache_t     ar_cache;
  prot_t      ar_prot;
  qos_t       ar_qos;
  region_t    ar_region;
  user_t      ar_user;
  logic       ar_valid;
  logic       ar_ready;

  id_t        r_id;
  data_t      r_data;
  resp_t      r_resp;
  logic       r_last;
  user_t      r_user;
  logic       r_valid;
  logic       r_ready;

  modport Master (
    output aw_id, aw_addr, aw_len, aw_size, aw_burst, aw_lock, aw_cache, aw_prot, aw_qos, aw_region, aw_user, aw_valid, input aw_ready,
    output w_data, w_strb, w_last, w_user, w_valid, input w_ready,
    input b_id, b_resp, b_user, b_valid, output b_ready,
    output ar_id, ar_addr, ar_len, ar_size, ar_burst, ar_lock, ar_cache, ar_prot, ar_qos, ar_region, ar_user, ar_valid, input ar_ready,
    input r_id, r_data, r_resp, r_last, r_user, r_valid, output r_ready
  );

  modport Slave (
    input aw_id, aw_addr, aw_len, aw_size, aw_burst, aw_lock, aw_cache, aw_prot, aw_qos, aw_region, aw_user, aw_valid, output aw_ready,
    input w_data, w_strb, w_last, w_user, w_valid, output w_ready,
    output b_id, b_resp, b_user, b_valid, input b_ready,
    input ar_id, ar_addr, ar_len, ar_size, ar_burst, ar_lock, ar_cache, ar_prot, ar_qos, ar_region, ar_user, ar_valid, output ar_ready,
    output r_id, r_data, r_resp, r_last, r_user, r_valid, input r_ready
  );

  /// The interface as an output (issuing requests, initiator, master).
  modport out (
    output aw_id, aw_addr, aw_len, aw_size, aw_burst, aw_lock, aw_cache, aw_prot, aw_qos, aw_region, aw_user, aw_valid, input aw_ready,
    output w_data, w_strb, w_last, w_user, w_valid, input w_ready,
    input b_id, b_resp, b_user, b_valid, output b_ready,
    output ar_id, ar_addr, ar_len, ar_size, ar_burst, ar_lock, ar_cache, ar_prot, ar_qos, ar_region, ar_user, ar_valid, input ar_ready,
    input r_id, r_data, r_resp, r_last, r_user, r_valid, output r_ready
  );

  /// The interface as an input (accepting requests, target, slave).
  modport in (
    input aw_id, aw_addr, aw_len, aw_size, aw_burst, aw_lock, aw_cache, aw_prot, aw_qos, aw_region, aw_user, aw_valid, output aw_ready,
    input w_data, w_strb, w_last, w_user, w_valid, output w_ready,
    output b_id, b_resp, b_user, b_valid, input b_ready,
    input ar_id, ar_addr, ar_len, ar_size, ar_burst, ar_lock, ar_cache, ar_prot, ar_qos, ar_region, ar_user, ar_valid, output ar_ready,
    output r_id, r_data, r_resp, r_last, r_user, r_valid, input r_ready
  );

endinterface


/// An asynchronous AXI4 interface.
interface AXI_BUS_ASYNC
#(
  parameter AXI_ADDR_WIDTH = -1,
  parameter AXI_DATA_WIDTH = -1,
  parameter AXI_ID_WIDTH   = -1,
  parameter AXI_USER_WIDTH = -1,
  parameter BUFFER_WIDTH   = -1
);

  localparam AXI_STRB_WIDTH = AXI_DATA_WIDTH / 8;


  logic [AXI_ID_WIDTH-1:0]    aw_id;
  logic [AXI_ADDR_WIDTH-1:0]  aw_addr;
  logic [7:0]                 aw_len;
  logic [2:0]                 aw_size;
  logic [1:0]                 aw_burst;
  logic                       aw_lock;
  logic [3:0]                 aw_cache;
  logic [2:0]                 aw_prot;
  logic [3:0]                 aw_qos;
  logic [3:0]                 aw_region;
  logic [AXI_USER_WIDTH-1:0]  aw_user;
  logic [BUFFER_WIDTH-1:0]    aw_writetoken;
  logic [BUFFER_WIDTH-1:0]    aw_readpointer;

  logic [AXI_DATA_WIDTH-1:0]  w_data;
  logic [AXI_STRB_WIDTH-1:0]  w_strb;
  logic                       w_last;
  logic [AXI_USER_WIDTH-1:0]  w_user;
  logic [BUFFER_WIDTH-1:0]    w_writetoken;
  logic [BUFFER_WIDTH-1:0]    w_readpointer;

  logic [AXI_ID_WIDTH-1:0]    b_id;
  logic [1:0]                 b_resp;
  logic [AXI_USER_WIDTH-1:0]  b_user;
  logic [BUFFER_WIDTH-1:0]    b_writetoken;
  logic [BUFFER_WIDTH-1:0]    b_readpointer;

  logic [AXI_ID_WIDTH-1:0]    ar_id;
  logic [AXI_ADDR_WIDTH-1:0]  ar_addr;
  logic [7:0]                 ar_len;
  logic [2:0]                 ar_size;
  logic [1:0]                 ar_burst;
  logic                       ar_lock;
  logic [3:0]                 ar_cache;
  logic [2:0]                 ar_prot;
  logic [3:0]                 ar_qos;
  logic [3:0]                 ar_region;
  logic [AXI_USER_WIDTH-1:0]  ar_user;
  logic [BUFFER_WIDTH-1:0]    ar_writetoken;
  logic [BUFFER_WIDTH-1:0]    ar_readpointer;

  logic [AXI_ID_WIDTH-1:0]    r_id;
  logic [AXI_DATA_WIDTH-1:0]  r_data;
  logic [1:0]                 r_resp;
  logic                       r_last;
  logic [AXI_USER_WIDTH-1:0]  r_user;
  logic [BUFFER_WIDTH-1:0]    r_writetoken;
  logic [BUFFER_WIDTH-1:0]    r_readpointer;

  modport Master (
    output aw_id, aw_addr, aw_len, aw_size, aw_burst, aw_lock, aw_cache, aw_prot, aw_qos, aw_region, aw_user, aw_writetoken, input aw_readpointer,
    output w_data, w_strb, w_last, w_user, w_writetoken, input w_readpointer,
    input b_id, b_resp, b_user, b_writetoken, output b_readpointer,
    output ar_id, ar_addr, ar_len, ar_size, ar_burst, ar_lock, ar_cache, ar_prot, ar_qos, ar_region, ar_user, ar_writetoken, input ar_readpointer,
    input r_id, r_data, r_resp, r_last, r_user, r_writetoken, output r_readpointer
  );

  modport Slave (
    input aw_id, aw_addr, aw_len, aw_size, aw_burst, aw_lock, aw_cache, aw_prot, aw_qos, aw_region, aw_user, aw_writetoken, output aw_readpointer,
    input w_data, w_strb, w_last, w_user, w_writetoken, output w_readpointer,
    output b_id, b_resp, b_user, b_writetoken, input b_readpointer,
    input ar_id, ar_addr, ar_len, ar_size, ar_burst, ar_lock, ar_cache, ar_prot, ar_qos, ar_region, ar_user, ar_writetoken, output ar_readpointer,
    output r_id, r_data, r_resp, r_last, r_user, r_writetoken, input r_readpointer
  );

endinterface


/// An AXI4-Lite interface.
interface AXI_LITE #(
  parameter AXI_ADDR_WIDTH = -1,
  parameter AXI_DATA_WIDTH = -1
)(
  input logic clk_i
);

  localparam AXI_STRB_WIDTH = AXI_DATA_WIDTH / 8;

  typedef logic [AXI_ADDR_WIDTH-1:0] addr_t;
  typedef logic [AXI_DATA_WIDTH-1:0] data_t;
  typedef logic [AXI_STRB_WIDTH-1:0] strb_t;

  // AW channel
  addr_t aw_addr;
  logic  aw_valid;
  logic  aw_ready;

  data_t w_data;
  strb_t w_strb;
  logic  w_valid;
  logic  w_ready;

  resp_t b_resp;
  logic  b_valid;
  logic  b_ready;

  addr_t ar_addr;
  logic  ar_valid;
  logic  ar_ready;

  data_t r_data;
  resp_t r_resp;
  logic  r_valid;
  logic  r_ready;

  modport Master (
    output aw_addr, aw_valid, input aw_ready,
    output w_data, w_strb, w_valid, input w_ready,
    input b_resp, b_valid, output b_ready,
    output ar_addr, ar_valid, input ar_ready,
    input r_data, r_resp, r_valid, output r_ready
  );

  modport Slave (
    input aw_addr, aw_valid, output aw_ready,
    input w_data, w_strb, w_valid, output w_ready,
    output b_resp, b_valid, input b_ready,
    input ar_addr, ar_valid, output ar_ready,
    output r_data, r_resp, r_valid, input r_ready
  );

  /// The interface as an output (issuing requests, initiator, master).
  modport out (
    output aw_addr, aw_valid, input aw_ready,
    output w_data, w_strb, w_valid, input w_ready,
    input b_resp, b_valid, output b_ready,
    output ar_addr, ar_valid, input ar_ready,
    input r_data, r_resp, r_valid, output r_ready
  );

  /// The interface as an input (accepting requests, target, slave).
  modport in (
    input aw_addr, aw_valid, output aw_ready,
    input w_data, w_strb, w_valid, output w_ready,
    output b_resp, b_valid, input b_ready,
    input ar_addr, ar_valid, output ar_ready,
    output r_data, r_resp, r_valid, input r_ready
  );

endinterface


`ifndef SYNTHESIS
package axi_test;

  class axi_lite_driver #(
    parameter int AW,
    parameter int DW,
    parameter time TA = 0ns, // stimuli application time
    parameter time TT = 0ns  // stimuli test time
  );
    virtual AXI_LITE #(
      .AXI_ADDR_WIDTH(AW),
      .AXI_DATA_WIDTH(DW)
    ) axi;

    function new(
      virtual AXI_LITE #(
        .AXI_ADDR_WIDTH(AW),
        .AXI_DATA_WIDTH(DW)
      ) axi
    );
      this.axi = axi;
    endfunction

    task reset_master;
      axi.aw_addr  <= 0;
      axi.aw_valid <= 0;
      axi.w_valid  <= 0;
      axi.w_data   <= 0;
      axi.w_strb   <= 0;
      axi.b_ready  <= 0;
      axi.ar_valid <= 0;
      axi.ar_addr  <= 0;
      axi.r_ready  <= 0;
    endtask

    task reset_slave;
      axi.aw_ready <= 0;
      axi.w_ready  <= 0;
      axi.b_resp   <= 0;
      axi.b_valid  <= 0;
      axi.ar_ready <= 0;
      axi.r_data   <= 0;
      axi.r_resp   <= 0;
      axi.r_valid  <= 0;
    endtask

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


  class axi_driver #(
    parameter AW,
    parameter DW,
    parameter IW,
    parameter UW
  );
    virtual AXI_BUS #(
      .AXI_ADDR_WIDTH(AW),
      .AXI_DATA_WIDTH(DW),
      .AXI_ID_WIDTH(IW),
      .AXI_USER_WIDTH(UW)
    ) axi;

    typedef axi_ax_beat #(.AW(AW), .IW(IW), .UW(UW)) ax_beat_t;
    typedef axi_w_beat #(.DW(DW), .UW(UW))            w_beat_t;
    typedef axi_b_beat #(.IW(IW), .UW(UW))            b_beat_t;
    typedef axi_r_beat #(.DW(DW), .IW(IW), .UW(UW))   r_beat_t;

    function new(
      virtual AXI_BUS #(
        .AXI_ADDR_WIDTH(AW),
        .AXI_DATA_WIDTH(DW),
        .AXI_ID_WIDTH(IW),
        .AXI_USER_WIDTH(UW)
      ) axi
    );
      this.axi = axi;
    endfunction

    task reset_master;
      axi.aw_valid <= 0;
      axi.w_valid  <= 0;
      axi.b_ready  <= 0;
      axi.ar_valid <= 0;
      axi.r_ready  <= 0;
    endtask

    task reset_slave;
      axi.aw_ready <= 0;
      axi.w_ready  <= 0;
      axi.b_valid  <= 0;
      axi.ar_ready <= 0;
      axi.r_valid  <= 0;
    endtask

    /// Issue a beat on the AW channel.
    task send_aw (
      input ax_beat_t beat
    );
      axi.aw_id     <= beat.ax_id;
      axi.aw_addr   <= beat.ax_addr;
      axi.aw_len    <= beat.ax_len;
      axi.aw_size   <= beat.ax_size;
      axi.aw_burst  <= beat.ax_burst;
      axi.aw_lock   <= beat.ax_lock;
      axi.aw_cache  <= beat.ax_cache;
      axi.aw_prot   <= beat.ax_prot;
      axi.aw_qos    <= beat.ax_qos;
      axi.aw_region <= beat.ax_region;
      axi.aw_user   <= beat.ax_user;
      axi.aw_valid  <= 1;
      @(posedge axi.clk_i);
      while (axi.aw_ready != 1) @(posedge axi.clk_i);
      axi.aw_id     <= 'x;
      axi.aw_addr   <= 'x;
      axi.aw_len    <= 'x;
      axi.aw_size   <= 'x;
      axi.aw_burst  <= 'x;
      axi.aw_lock   <= 'x;
      axi.aw_cache  <= 'x;
      axi.aw_prot   <= 'x;
      axi.aw_qos    <= 'x;
      axi.aw_region <= 'x;
      axi.aw_user   <= 'x;
      axi.aw_valid  <= 0;
    endtask

    /// Issue a beat on the W channel.
    task send_w (
      input w_beat_t beat
    );
      axi.w_data  <= beat.w_data;
      axi.w_strb  <= beat.w_strb;
      axi.w_last  <= beat.w_last;
      axi.w_user  <= beat.w_user;
      axi.w_valid <= 1;
      @(posedge axi.clk_i);
      while (axi.w_ready != 1) @(posedge axi.clk_i);
      axi.w_data  <= 'x;
      axi.w_strb  <= 'x;
      axi.w_last  <= 'x;
      axi.w_user  <= 'x;
      axi.w_valid <= 0;
    endtask

    /// Issue a beat on the B channel.
    task send_b (
      input b_beat_t beat
    );
      axi.b_id    <= beat.b_id;
      axi.b_resp  <= beat.b_resp;
      axi.b_user  <= beat.b_user;
      axi.b_valid <= 1;
      @(posedge axi.clk_i);
      while (axi.b_ready != 1) @(posedge axi.clk_i);
      axi.b_id    <= 'x;
      axi.b_resp  <= 'x;
      axi.b_user  <= 'x;
      axi.b_valid <= 0;
    endtask

    /// Issue a beat on the AR channel.
    task send_ar (
      input ax_beat_t beat
    );
      axi.ar_id     <= beat.ax_id;
      axi.ar_addr   <= beat.ax_addr;
      axi.ar_len    <= beat.ax_len;
      axi.ar_size   <= beat.ax_size;
      axi.ar_burst  <= beat.ax_burst;
      axi.ar_lock   <= beat.ax_lock;
      axi.ar_cache  <= beat.ax_cache;
      axi.ar_prot   <= beat.ax_prot;
      axi.ar_qos    <= beat.ax_qos;
      axi.ar_region <= beat.ax_region;
      axi.ar_user   <= beat.ax_user;
      axi.ar_valid  <= 1;
      @(posedge axi.clk_i);
      while (axi.ar_ready != 1) @(posedge axi.clk_i);
      axi.ar_id     <= 'x;
      axi.ar_addr   <= 'x;
      axi.ar_len    <= 'x;
      axi.ar_size   <= 'x;
      axi.ar_burst  <= 'x;
      axi.ar_lock   <= 'x;
      axi.ar_cache  <= 'x;
      axi.ar_prot   <= 'x;
      axi.ar_qos    <= 'x;
      axi.ar_region <= 'x;
      axi.ar_user   <= 'x;
      axi.ar_valid  <= 0;
    endtask

    /// Issue a beat on the R channel.
    task send_r (
      input r_beat_t beat
    );
      axi.r_id    <= beat.r_id;
      axi.r_data  <= beat.r_data;
      axi.r_resp  <= beat.r_resp;
      axi.r_last  <= beat.r_last;
      axi.r_user  <= beat.r_user;
      axi.r_valid <= 1;
      @(posedge axi.clk_i);
      while (axi.r_ready != 1) @(posedge axi.clk_i);
      axi.r_id    <= 'x;
      axi.r_data  <= 'x;
      axi.r_resp  <= 'x;
      axi.r_last  <= 'x;
      axi.r_user  <= 'x;
      axi.r_valid <= 0;
    endtask

    /// Wait for a beat on the AW channel.
    task recv_aw (
      output ax_beat_t beat
    );
      axi.aw_ready <= 1;
      @(posedge axi.clk_i);
      while (axi.aw_valid != 1) @(posedge axi.clk_i);
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
      beat.ax_user   = axi.aw_user;
      axi.aw_ready <= 0;
    endtask

    /// Wait for a beat on the W channel.
    task recv_w (
      output w_beat_t beat
    );
      axi.w_ready <= 1;
      @(posedge axi.clk_i);
      while (axi.w_valid != 1) @(posedge axi.clk_i);
      beat = new;
      beat.w_data = axi.w_data;
      beat.w_strb = axi.w_strb;
      beat.w_last = axi.w_last;
      beat.w_user = axi.w_user;
      axi.w_ready <= 0;
    endtask

    /// Wait for a beat on the B channel.
    task recv_b (
      output b_beat_t beat
    );
      axi.b_ready <= 1;
      @(posedge axi.clk_i);
      while (axi.b_valid != 1) @(posedge axi.clk_i);
      beat = new;
      beat.b_id   = axi.b_id;
      beat.b_resp = axi.b_resp;
      beat.b_user = axi.b_user;
      axi.b_ready <= 0;
    endtask

    /// Wait for a beat on the AR channel.
    task recv_ar (
      output ax_beat_t beat
    );
      axi.ar_ready  <= 1;
      @(posedge axi.clk_i);
      while (axi.ar_valid != 1) @(posedge axi.clk_i);
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
      beat.ax_user   = axi.ar_user;
      axi.ar_ready  <= 0;
    endtask

    /// Wait for a beat on the R channel.
    task recv_r (
      output r_beat_t beat
    );
      axi.r_ready <= 1;
      @(posedge axi.clk_i);
      while (axi.r_valid != 1) @(posedge axi.clk_i);
      beat = new;
      beat.r_id   = axi.r_id;
      beat.r_data = axi.r_data;
      beat.r_resp = axi.r_resp;
      beat.r_last = axi.r_last;
      beat.r_user = axi.r_user;
      axi.r_ready <= 0;
    endtask

  endclass

endpackage
`endif


/// An AXI routing table.
///
/// For each slave, multiple rules can be defined. Each rule consists of an
/// address mask and a base. Addresses are masked and then compared against the
/// base to decide where transfers need to go.
interface AXI_ROUTING_RULES #(
  /// The address width.
  parameter int AXI_ADDR_WIDTH = -1,
  /// The number of slaves in the routing table.
  parameter int NUM_SLAVE  = -1,
  /// The number of rules in the routing table.
  parameter int NUM_RULES  = -1
);

  struct packed {
    logic enabled;
    logic [AXI_ADDR_WIDTH-1:0] mask;
    logic [AXI_ADDR_WIDTH-1:0] base;
  } [NUM_RULES-1:0] rules [NUM_SLAVE];

  modport xbar(input rules);
  modport cfg(output rules);

endinterface


/// An AXI arbitration interface.
interface AXI_ARBITRATION #(
  /// The number of requestors.
  parameter int NUM_REQ = -1
);

  // Incoming requests.
  logic [NUM_REQ-1:0] in_req;
  logic [NUM_REQ-1:0] in_ack;

  // Outgoing request.
  logic out_req;
  logic out_ack;
  logic [$clog2(NUM_REQ)-1:0] out_sel;

  // The arbiter side of the interface.
  modport arb(input  in_req, out_ack, output out_req, out_sel, in_ack);

  // The requestor side of the interface.
  modport req(output in_req, out_ack, input  out_req, out_sel, in_ack);

endinterface
