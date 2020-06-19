// Copyright (c) 2019 ETH Zurich, University of Bologna
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
// File:   tb_axi_llc.sv
// Author: Wolfgang Roenninger <wroennin@student.ethz.ch>
// Date:   03.05.2019
//
// Description: Testbench for the block AXI last level cache.
//              The LLC has a monitor class which acts as the golden model.
//              Requests get generated with the help of `rand_axi_master`.
//


`include "axi/typedef.svh"
`include "axi/assign.svh"

module tb_axi_llc #(
  parameter bit SimSpm   = 1'b0, // simulate SPM access
  parameter bit SimCache = 1'b1
);
  localparam axi_llc_pkg::llc_axi_cfg_t AxiCfg = '{
    SlvPortIdWidth:    llc_axi::IdWidthSlave,
    AddrWidthFull:     llc_axi::AddrWidth,
    DataWidthFull:     llc_axi::DataWidth,
    LitePortAddrWidth: llc_axi::AddrWidth,
    LitePortDataWidth: llc_axi::DataWidthLite
  };

  // -------------
  // MUT signals
  // -------------
  logic clk;
  // DUT signals
  logic rst_n;
  logic test;

  // Master Axi from Cpu
  llc_axi::req_slv_t  axi_llc_req;
  llc_axi::resp_slv_t axi_llc_resp;

  // Salve Axi from memory
  llc_axi::req_mst_t      axi_mem_req;
  llc_axi::resp_mst_t     axi_mem_resp;

  // Config Lite signals
  llc_axi::req_lite_t     axi_lite_conf_req;
  llc_axi::resp_lite_t    axi_lite_conf_resp;

  // Events output
  axi_llc_pkg::events_t axi_llc_events;

  // ---------------------
  // Testbench signals
  // ---------------------
  logic end_of_sim, print_counters, enable_counters; // if counters are printed, they are reset.

  // -------------
  // Clock generator
  // -------------
  clk_rst_gen #(
    .CLK_PERIOD    (tb_axi_llc_pkg::clockPeriod),
    .RST_CLK_CYCLES(tb_axi_llc_pkg::rstCycles)
  ) i_clk_gen (
    .clk_o (clk),
    .rst_no(rst_n)
  );

  // application bus
  AXI_BUS_DV #(
    .AXI_ADDR_WIDTH ( llc_axi::AddrWidth     ),
    .AXI_DATA_WIDTH ( llc_axi::DataWidth     ),
    .AXI_ID_WIDTH   ( llc_axi::IdWidthSlave  ),
    .AXI_USER_WIDTH ( 1                      )
  ) master_dv(.clk_i(clk));

  // config Lite bus
  AXI_LITE_DV #(
    .AXI_ADDR_WIDTH ( llc_axi::AddrWidth     ),
    .AXI_DATA_WIDTH ( llc_axi::DataWidthLite )
  ) axi_lite_dv(.clk_i(clk));

  // bus to main mem
  AXI_BUS_DV #(
    .AXI_ADDR_WIDTH ( llc_axi::AddrWidth     ),
    .AXI_DATA_WIDTH ( llc_axi::DataWidth     ),
    .AXI_ID_WIDTH   ( llc_axi::IdWidthMaster ),
    .AXI_USER_WIDTH ( 1                      )
  ) axi_memory_dv(.clk_i(clk));

  // MONITOR INTERFACE
  AXI_MONITOR_INTF monitor_intf (
    .clk_i   ( clk          ),
    .rst_ni  ( rst_n        ),
    .req_slv ( axi_llc_req  ),
    .resp_slv( axi_llc_resp ),
    .end_sim ( 1'b0         )
  );

  AXI_BUS_DV #(
    .AXI_ADDR_WIDTH ( llc_axi::AddrWidth    ),
    .AXI_DATA_WIDTH ( llc_axi::DataWidth    ),
    .AXI_ID_WIDTH   ( llc_axi::IdWidthSlave ),
    .AXI_USER_WIDTH ( 1                     )
  ) scoreboard_dv(.clk_i(clk));

  // -------------
  // Testbench
  // -------------
  program test_llc;
    // ----------------
    // do the application of signals here
    // ----------------
    initial begin : stimulus
      // specify the initial values
      automatic axi_pkg::resp_t                    resp;
      automatic logic [llc_axi::DataWidthLite-1:0] data;

      // Master Axi 4 Driver
      axi_test::rand_axi_master #(
      // AXI interface parameters
      .AW ( llc_axi::AddrWidth     ),
      .DW ( llc_axi::DataWidth     ),
      .IW ( llc_axi::IdWidthSlave  ),
      .UW ( 1                      ),
      // Stimuli application and test time
      .TA ( tb_axi_llc_pkg::appliSkew                               ),
      .TT ( tb_axi_llc_pkg::clockPeriod - tb_axi_llc_pkg::aquisSkew ),
      // Maximum number of read and write transactions in flight
      .MAX_READ_TXNS       ( 5          ),
      .MAX_WRITE_TXNS      ( 5          ),
      .AX_MIN_WAIT_CYCLES  ( 0          ),
      .AX_MAX_WAIT_CYCLES  ( 50         ),
      .W_MIN_WAIT_CYCLES   ( 0          ),
      .W_MAX_WAIT_CYCLES   ( 0          ),
      .RESP_MIN_WAIT_CYCLES( 0          ),
      .RESP_MAX_WAIT_CYCLES( 0          )
      ) rand_axi_master;

      // Config Axi Lite Driver
      axi_test::axi_lite_driver #(
      .AW ( llc_axi::AddrWidth     ),
      .DW ( llc_axi::DataWidthLite ),
      .TA ( tb_axi_llc_pkg::appliSkew                               ),
      .TT ( tb_axi_llc_pkg::clockPeriod - tb_axi_llc_pkg::aquisSkew )
      ) axi_lite_drv;

      tb_axi_llc_pkg::axi_llc_monitor #(
        .AW( llc_axi::AddrWidth     ),
        .DW( llc_axi::DataWidth     ),
        .IW( llc_axi::IdWidthMaster ),
        .UW( 1                      ),
        .TA( tb_axi_llc_pkg::appliSkew  ),
        .TT( tb_axi_llc_pkg::clockPeriod - tb_axi_llc_pkg::aquisSkew )
      ) axi_monitor;

      axi_test::axi_scoreboard #(
        .IW( llc_axi::IdWidthSlave ),
        .AW( llc_axi::AddrWidth    ),
        .DW( llc_axi::DataWidth    ),
        .UW( 1                     ),
        .TT( tb_axi_llc_pkg::clockPeriod - tb_axi_llc_pkg::aquisSkew )
      ) axi_scoreboard;


      rand_axi_master = new(  master_dv     );
      axi_lite_drv    = new(  axi_lite_dv   );
      axi_monitor     = new(  "Monitor",
                              64'h1000_0000,
                              64'h0008_0800,
                              monitor_intf,
                              axi_memory_dv );
      axi_scoreboard  = new(  scoreboard_dv );



      fork
      axi_monitor.monitor_channel();
      begin
        axi_scoreboard.reset();
        axi_scoreboard.monitor();
        @(posedge rst_n);
        axi_scoreboard.enable_all_checks();
      end
      begin
        rand_axi_master.reset();
        axi_lite_drv.reset_master();
        // counter signals
        print_counters  = 1'b0;
        enable_counters = 1'b0;

        //axi_monitor.reset();
        @(posedge rst_n);
        //rand_axi_master.send_aws(5, 64'h1000, 64'h10F0);
        //rand_axi_master.run(0, 1000, 64'h1000_0000, 64'h2DCD_6500);

        print_test_info("Testing LITE Configuration");

        repeat (10) @(posedge clk);
        print_test_info("Read Cfg @ 64'h0001_0000");
        axi_lite_drv.send_ar(64'h0001_0000, axi_pkg::prot_t'(1'b0));
        axi_lite_drv.recv_r(data, resp);
        $info("AXI-LITE conf data: %h", data);
        $info("Response was      : %h", resp);

        repeat (10) @(posedge clk);
        print_test_info("Read Cfg @ 64'h0002_0000: Expect Error");
        axi_lite_drv.send_ar(64'h0002_0000, axi_pkg::prot_t'(1'b0));
        axi_lite_drv.recv_r(data, resp);
        $info("AXI-LITE conf data: %h", data);
        $info("Response was      : %h", resp);

        repeat (10) @(posedge clk);
        print_test_info("Write Cfg @ 64'h0001_0000 with 32'hDEAD_BEEF");
        fork
          axi_lite_drv.send_aw(64'h0001_0000, axi_pkg::prot_t'(1'b0));
          axi_lite_drv.send_w(32'hDEAD_BEEF, '1);
        join
        axi_lite_drv.recv_b(resp);
        $info("AXI-Lite B: resp %h", resp);

        repeat (10) @(posedge clk);
        print_test_info("Read Cfg @ 64'h0001_0000: Expect 32'hDEAD_BEEF");
        axi_lite_drv.send_ar(64'h0001_0000, axi_pkg::prot_t'(1'b0));
        axi_lite_drv.recv_r(data, resp);
        $info("AXI-LITE conf data: %h", data);
        $info("Response was      : %h", resp);

        repeat (10) @(posedge clk);
        print_test_info("Write Cfg @ 64'h0001_0000 with 32'h0000_000F");
        fork
          axi_lite_drv.send_aw(64'h0001_0000, axi_pkg::prot_t'(1'b0));
          axi_lite_drv.send_w(32'h0000_000F, '1);
        join
        axi_lite_drv.recv_b(resp);
        $info("AXI-Lite B: resp %h", resp);

        repeat (10) @(posedge clk);
        print_test_info("Read Cfg @ 64'h0001_0000: Expect 32'h0000_000F");
        axi_lite_drv.send_ar(64'h0001_0000, axi_pkg::prot_t'(1'b0));
        axi_lite_drv.recv_r(data, resp);
        $info("AXI-LITE conf data: %h", data);
        $info("Response was      : %h", resp);

        repeat (10) @(posedge clk);
        print_test_info("Read Cfg @ 64'h0001_0008: Expect 32'h0000_0000 FLUSH REG");
        axi_lite_drv.send_ar(64'h0001_0008, axi_pkg::prot_t'(1'b0));
        axi_lite_drv.recv_r(data, resp);
        $info("AXI-LITE conf data: %h", data);
        $info("Response was      : %h", resp);

//        repeat (10) @(posedge clk);
//        print_test_info("Read Cfg @ 64'h0001_0010: Expect FLUSHED REGISTER");
//        axi_lite_drv.send_ar(64'h0001_0010, axi_pkg::prot_t'(1'b0));
//        axi_lite_drv.recv_r(data, resp);
//        $info("AXI-LITE conf data: %h", data);
//        $info("Response was      : %h", resp);
//
//        repeat (10) @(posedge clk);
//        print_test_info("Read Cfg @ 64'h0001_020: Expect BIST RESULT");
//        axi_lite_drv.send_ar(64'h0001_0020, axi_pkg::prot_t'(1'b0));
//        axi_lite_drv.recv_r(data, resp);
//        $info("AXI-LITE conf data: %h", data);
//        $info("Response was      : %h", resp);

        repeat (10) @(posedge clk);
        print_test_info("Write Cfg @ 64'h0001_0008 with 32'h0000_0001, enable perf counter");
        fork
          axi_lite_drv.send_aw(64'h0001_0010, axi_pkg::prot_t'(1'b0));
          axi_lite_drv.send_w(32'h0000_0001, '1);
        join
        axi_lite_drv.recv_b(resp);
        $info("AXI-Lite B: resp %h", resp);

        //rand_axi_master.add_memory_region(64'h1004_0000, 64'h1007_FFFF,
                                         // axi_pkg::DEVICE_BUFFERABLE);
        //print_test_info("Test 10 wites on not spm configured, expect errors!");
        //rand_axi_master.run(0, 10);
        //repeat (1000) @(posedge clk);

        if (SimCache) begin
          rand_axi_master.add_memory_region(64'h2000_0000, 64'h2010_0000,
                                            axi_pkg::WBACK_RWALLOCATE);
          print_test_info("1000 reads and 2000 writes on cache region.");
          @(posedge clk);
          #tb_axi_llc_pkg::appliSkew;
            enable_counters = 1'b1;
          @(posedge clk);


          rand_axi_master.run(1000, 2000);
          @(posedge clk);
          #tb_axi_llc_pkg::appliSkew;
            enable_counters = 1'b0;
            print_counters  = 1'b1;
          @(posedge clk);
          #tb_axi_llc_pkg::appliSkew;
            print_counters  = 1'b0;
          @(posedge clk);



          repeat (1000) @(posedge clk);

          print_test_info("Flushing the cache and reversing the SPM definition");
          repeat (10) @(posedge clk);
          @(posedge clk);
          #tb_axi_llc_pkg::appliSkew;
            enable_counters = 1'b1;
          @(posedge clk);

          fork
            axi_lite_drv.send_aw(64'h0001_0000, axi_pkg::prot_t'(1'b0));
            axi_lite_drv.send_w(32'h0000_00F0, '1);
          join
          axi_lite_drv.recv_b(resp);
          $info("AXI-Lite B: resp %h", resp);
          repeat (100000) @(posedge clk);
          @(posedge clk);
          #tb_axi_llc_pkg::appliSkew;
            enable_counters = 1'b0;
            print_counters  = 1'b1;
          @(posedge clk);
          #tb_axi_llc_pkg::appliSkew;
            print_counters  = 1'b0;
          @(posedge clk);


          print_test_info("1000 reads and 2000 writes on cache region.");
          @(posedge clk);
          #tb_axi_llc_pkg::appliSkew;
            enable_counters = 1'b1;
          @(posedge clk)rand_axi_master.run(1000, 2000);
          @(posedge clk);
          #tb_axi_llc_pkg::appliSkew;
            enable_counters = 1'b0;
            print_counters  = 1'b1;
          @(posedge clk);
          #tb_axi_llc_pkg::appliSkew;
            print_counters  = 1'b0;
          @(posedge clk);repeat (1000) @(posedge clk);

        end else if (SimSpm) begin
          repeat (10) @(posedge clk);
          print_test_info("Write Cfg @ 64'h0001_0000 with 32'h0000_00FF");
          fork
            axi_lite_drv.send_aw(64'h0001_0000, axi_pkg::prot_t'(1'b0));
            axi_lite_drv.send_w(32'h0000_00FF, '1);
          join
          axi_lite_drv.recv_b(resp);
          $info("AXI-Lite B: resp %h", resp);

          repeat (2000) @(posedge clk);
          rand_axi_master.add_memory_region(64'h1000_0000, 64'h1003_FFFF,
                                            axi_pkg::DEVICE_BUFFERABLE);
          print_test_info("Test 1000 writes and 1000 reads on spm region.");
          rand_axi_master.run(1000, 1000);
          repeat (1000) @(posedge clk);
        end




        print_test_info("Reading out perf counters.");
        // stop the counters
        fork
          axi_lite_drv.send_aw(64'h0001_0010, axi_pkg::prot_t'(1'b0));
          axi_lite_drv.send_w(32'h0000_0000, '1);
        join
        axi_lite_drv.recv_b(resp);
        axi_lite_drv.send_ar(64'h0001_0010, axi_pkg::prot_t'(1'b0));
        axi_lite_drv.recv_r(data, resp);
        $display("No Cycles: %h", data);
        axi_lite_drv.send_ar(64'h0001_0018, axi_pkg::prot_t'(1'b0));
        axi_lite_drv.recv_r(data, resp);
        $display("No Descs:  %h", data);
        axi_lite_drv.send_ar(64'h0001_0020, axi_pkg::prot_t'(1'b0));
        axi_lite_drv.recv_r(data, resp);
        $display("No Hits:   %h", data);
        axi_lite_drv.send_ar(64'h0001_0028, axi_pkg::prot_t'(1'b0));
        axi_lite_drv.recv_r(data, resp);
        $display("No Misses: %h", data);
        print_test_info("Clearing counters.");
        fork
          axi_lite_drv.send_aw(64'h0001_0010, axi_pkg::prot_t'(1'b0));
          axi_lite_drv.send_w(32'h0000_0002, '1);
        join
        axi_lite_drv.recv_b(resp);
        fork
          axi_lite_drv.send_aw(64'h0001_0010, axi_pkg::prot_t'(1'b0));
          axi_lite_drv.send_w(32'h0000_0000, '1);
        join
        axi_lite_drv.recv_b(resp);



        repeat (10) @(posedge clk);
        print_test_info("Write Cfg @ 64'h0001_0008 with 32'h0000_0004 should Flush way 2");
        fork
          axi_lite_drv.send_aw(64'h0001_0008, axi_pkg::prot_t'(1'b0));
          axi_lite_drv.send_w(32'h0000_0004, '1);
        join
        axi_lite_drv.recv_b(resp);
        $info("AXI-Lite B: resp %h", resp);


        repeat (100000) @(posedge clk);

        print_test_info("Write Cfg @ 64'h0001_0008 with 32'hFFFF_FFFF should Flush the rest");
        fork
          axi_lite_drv.send_aw(64'h0001_0008, axi_pkg::prot_t'(1'b0));
          axi_lite_drv.send_w(32'hFFFF_FFFF, '1);
        join
        axi_lite_drv.recv_b(resp);
        $info("AXI-Lite B: resp %h", resp);

        repeat (400000) @(posedge clk);

        if ( axi_monitor.progress.totErrCnt == 0 ) begin
          $display(">>> ----------------------------------------------------------------------" );
          $display(">>> PASSED %0d VECTORS", axi_monitor.progress.totAcqCnt);
          $display(">>> ----------------------------------------------------------------------\n");
        end else begin
          $display(">>> ----------------------------------------------------------------------\n");
          $display(">>> FAILED %0d OF %0d VECTORS\n", axi_monitor.progress.totErrCnt, axi_monitor.progress.totAcqCnt);
          $display(">>> ----------------------------------------------------------------------\n");
        end
        $stop();
      end
      join
    end

    task print_test_info(input string text);
      automatic string disp_str;
      disp_str = {">>> ", text};
      $display(">>> ----------------------------------------------------------------------" );
      $info(disp_str);
      $display(">>> ----------------------------------------------------------------------" );
    endtask : print_test_info

    initial begin : test_tb_params
      if ((SimSpm || SimCache) == 1'b0) begin
        $fatal(1, "No Simulation chosen in tb params.");
      end
    end

  endprogram

  ////////////////////////////////////////////////////////
  // Performance counters                               //
  ////////////////////////////////////////////////////////
  localparam int unsigned NumCounters = 32'd52;
  initial begin : proc_counters
    automatic longint unsigned count [0:NumCounters-1];
    automatic longint unsigned cycle_count = 0;
    for (int unsigned i = 0; i < NumCounters; i++) begin
      count[i] = 0;
    end

    @(posedge rst_n);
    forever begin
      // Wait for the test time
      @(posedge clk);
      #(tb_axi_llc_pkg::clockPeriod - tb_axi_llc_pkg::aquisSkew);
      cycle_count++;

      if (enable_counters) begin
        if (axi_llc_events.aw_slv_transfer.active) begin
          count[0] = count[0] + axi_llc_events.aw_slv_transfer.num_bytes;
          count[1] = count[1] + 64'd1;
        end
        if (axi_llc_events.ar_slv_transfer.active) begin
          count[2] = count[2] + axi_llc_events.ar_slv_transfer.num_bytes;
          count[3] = count[3] + 64'd1;
        end
        if (axi_llc_events.aw_bypass_transfer.active) begin
          count[4] = count[4] + axi_llc_events.aw_bypass_transfer.num_bytes;
          count[5] = count[5] + 64'd1;
        end
        if (axi_llc_events.ar_bypass_transfer.active) begin
          count[6] = count[6] + axi_llc_events.ar_bypass_transfer.num_bytes;
          count[7] = count[7] + 64'd1;
        end
        if (axi_llc_events.aw_mst_transfer.active) begin
          count[8] = count[8] + axi_llc_events.aw_mst_transfer.num_bytes;
          count[9] = count[9] + 64'd1;
        end
        if (axi_llc_events.ar_mst_transfer.active) begin
          count[10] = count[10] + axi_llc_events.ar_mst_transfer.num_bytes;
          count[11] = count[11] + 64'd1;
        end
        if (axi_llc_events.aw_desc_spm.active) begin
          count[12] = count[12] + axi_llc_events.aw_desc_spm.num_bytes;
          count[13] = count[13] + 64'd1;
        end
        if (axi_llc_events.ar_desc_spm.active) begin
          count[14] = count[14] + axi_llc_events.ar_desc_spm.num_bytes;
          count[15] = count[15] + 64'd1;
        end
        if (axi_llc_events.aw_desc_cache.active) begin
          count[16] = count[16] + axi_llc_events.aw_desc_cache.num_bytes;
          count[17] = count[17] + 64'd1;
        end
        if (axi_llc_events.ar_desc_cache.active) begin
          count[18] = count[18] + axi_llc_events.ar_desc_cache.num_bytes;
          count[19] = count[19] + 64'd1;
        end
        if (axi_llc_events.config_desc.active) begin
          count[20] = count[20] + axi_llc_events.config_desc.num_bytes;
          count[21] = count[21] + 64'd1;
        end
        if (axi_llc_events.hit_write_spm.active) begin
          count[22] = count[22] + axi_llc_events.hit_write_spm.num_bytes;
          count[23] = count[23] + 64'd1;
        end
        if (axi_llc_events.hit_read_spm.active) begin
          count[24] = count[24] + axi_llc_events.hit_read_spm.num_bytes;
          count[25] = count[25] + 64'd1;
        end
        if (axi_llc_events.miss_write_spm.active) begin
          count[26] = count[26] + axi_llc_events.miss_write_spm.num_bytes;
          count[27] = count[27] + 64'd1;
        end
        if (axi_llc_events.miss_read_spm.active) begin
          count[28] = count[28] + axi_llc_events.miss_read_spm.num_bytes;
          count[29] = count[29] + 64'd1;
        end
        if (axi_llc_events.hit_write_cache.active) begin
          count[30] = count[30] + axi_llc_events.hit_write_cache.num_bytes;
          count[31] = count[31] + 64'd1;
        end
        if (axi_llc_events.hit_read_cache.active) begin
          count[32] = count[32] + axi_llc_events.hit_read_cache.num_bytes;
          count[33] = count[33] + 64'd1;
        end
        if (axi_llc_events.miss_write_cache.active) begin
          count[34] = count[34] + axi_llc_events.miss_write_cache.num_bytes;
          count[35] = count[35] + 64'd1;
        end
        if (axi_llc_events.miss_read_cache.active) begin
          count[36] = count[36] + axi_llc_events.miss_read_cache.num_bytes;
          count[37] = count[37] + 64'd1;
        end
        if (axi_llc_events.refill_write.active) begin
          count[38] = count[38] + axi_llc_events.refill_write.num_bytes;
          count[39] = count[39] + 64'd1;
        end
        if (axi_llc_events.refill_read.active) begin
          count[40] = count[40] + axi_llc_events.refill_read.num_bytes;
          count[41] = count[41] + 64'd1;
        end
        if (axi_llc_events.evict_write.active) begin
          count[42] = count[42] + axi_llc_events.evict_write.num_bytes;
          count[43] = count[43] + 64'd1;
        end
        if (axi_llc_events.evict_read.active) begin
          count[44] = count[44] + axi_llc_events.evict_read.num_bytes;
          count[45] = count[45] + 64'd1;
        end
        if (axi_llc_events.evict_flush.active) begin
          count[46] = count[46] + axi_llc_events.evict_flush.num_bytes;
          count[47] = count[47] + 64'd1;
        end
        if (axi_llc_events.evict_unit_req) begin
          count[48] = count[48] + 64'd1;
        end
        if (axi_llc_events.refill_unit_req) begin
          count[49] = count[49] + 64'd1;
        end
        if (axi_llc_events.w_chan_unit_req) begin
          count[50] = count[50] + 64'd1;
        end
        if (axi_llc_events.r_chan_unit_req) begin
          count[51] = count[51] + 64'd1;
        end
      end

      if (print_counters) begin
        $display("##################################################################");
        $display("LLC: Performance");
        $display("Max Bandwidth of one channel: %f MiB/sec", (real'(llc_axi::DataWidth) / real'(8)) * (real'(1000000000) /  real'(tb_axi_llc_pkg::clockPeriod)) / 1024 / 1024);
        $display("##################################################################");
        $display("Bandwidths:");
        $display("aw_slv_transfer:    %f MiB/sec", real'(count[0] ) / real'(cycle_count) / real'(tb_axi_llc_pkg::clockPeriod) * real'(1000000000) / 1024 / 1024);
        $display("ar_slv_transfer:    %f MiB/sec", real'(count[2] ) / real'(cycle_count) / real'(tb_axi_llc_pkg::clockPeriod) * real'(1000000000) / 1024 / 1024);
        $display("aw_bypass_transfer: %f MiB/sec", real'(count[4] ) / real'(cycle_count) / real'(tb_axi_llc_pkg::clockPeriod) * real'(1000000000) / 1024 / 1024);
        $display("ar_bypass_transfer: %f MiB/sec", real'(count[6] ) / real'(cycle_count) / real'(tb_axi_llc_pkg::clockPeriod) * real'(1000000000) / 1024 / 1024);
        $display("aw_mst_transfer:    %f MiB/sec", real'(count[8] ) / real'(cycle_count) / real'(tb_axi_llc_pkg::clockPeriod) * real'(1000000000) / 1024 / 1024);
        $display("ar_mst_transfer:    %f MiB/sec", real'(count[10]) / real'(cycle_count) / real'(tb_axi_llc_pkg::clockPeriod) * real'(1000000000) / 1024 / 1024);
        $display("aw_desc_spm:        %f MiB/sec", real'(count[12]) / real'(cycle_count) / real'(tb_axi_llc_pkg::clockPeriod) * real'(1000000000) / 1024 / 1024);
        $display("ar_desc_spm:        %f MiB/sec", real'(count[14]) / real'(cycle_count) / real'(tb_axi_llc_pkg::clockPeriod) * real'(1000000000) / 1024 / 1024);
        $display("aw_desc_cache:      %f MiB/sec", real'(count[16]) / real'(cycle_count) / real'(tb_axi_llc_pkg::clockPeriod) * real'(1000000000) / 1024 / 1024);
        $display("ar_desc_cache:      %f MiB/sec", real'(count[18]) / real'(cycle_count) / real'(tb_axi_llc_pkg::clockPeriod) * real'(1000000000) / 1024 / 1024);
        $display("config_desc:        %f MiB/sec", real'(count[20]) / real'(cycle_count) / real'(tb_axi_llc_pkg::clockPeriod) * real'(1000000000) / 1024 / 1024);
        $display("hit_write_spm:      %f MiB/sec", real'(count[22]) / real'(cycle_count) / real'(tb_axi_llc_pkg::clockPeriod) * real'(1000000000) / 1024 / 1024);
        $display("hit_read_spm:       %f MiB/sec", real'(count[24]) / real'(cycle_count) / real'(tb_axi_llc_pkg::clockPeriod) * real'(1000000000) / 1024 / 1024);
        $display("miss_write_spm:     %f MiB/sec", real'(count[26]) / real'(cycle_count) / real'(tb_axi_llc_pkg::clockPeriod) * real'(1000000000) / 1024 / 1024);
        $display("miss_read_spm:      %f MiB/sec", real'(count[28]) / real'(cycle_count) / real'(tb_axi_llc_pkg::clockPeriod) * real'(1000000000) / 1024 / 1024);
        $display("hit_write_cache:    %f MiB/sec", real'(count[30]) / real'(cycle_count) / real'(tb_axi_llc_pkg::clockPeriod) * real'(1000000000) / 1024 / 1024);
        $display("hit_read_cache:     %f MiB/sec", real'(count[32]) / real'(cycle_count) / real'(tb_axi_llc_pkg::clockPeriod) * real'(1000000000) / 1024 / 1024);
        $display("miss_write_cache:   %f MiB/sec", real'(count[34]) / real'(cycle_count) / real'(tb_axi_llc_pkg::clockPeriod) * real'(1000000000) / 1024 / 1024);
        $display("miss_read_cache:    %f MiB/sec", real'(count[36]) / real'(cycle_count) / real'(tb_axi_llc_pkg::clockPeriod) * real'(1000000000) / 1024 / 1024);
        $display("refill_write:       %f MiB/sec", real'(count[38]) / real'(cycle_count) / real'(tb_axi_llc_pkg::clockPeriod) * real'(1000000000) / 1024 / 1024);
        $display("refill_read:        %f MiB/sec", real'(count[40]) / real'(cycle_count) / real'(tb_axi_llc_pkg::clockPeriod) * real'(1000000000) / 1024 / 1024);
        $display("evict_write:        %f MiB/sec", real'(count[42]) / real'(cycle_count) / real'(tb_axi_llc_pkg::clockPeriod) * real'(1000000000) / 1024 / 1024);
        $display("evict_read:         %f MiB/sec", real'(count[44]) / real'(cycle_count) / real'(tb_axi_llc_pkg::clockPeriod) * real'(1000000000) / 1024 / 1024);
        $display("evict_flush:        %f MiB/sec", real'(count[46]) / real'(cycle_count) / real'(tb_axi_llc_pkg::clockPeriod) * real'(1000000000) / 1024 / 1024);
        $display("##################################################################");
        $display("Utilization:");
        $display("aw_slv_transfer:    %f", real'(count[1] ) / real'(cycle_count));
        $display("ar_slv_transfer:    %f", real'(count[3] ) / real'(cycle_count));
        $display("aw_bypass_transfer: %f", real'(count[5] ) / real'(cycle_count));
        $display("ar_bypass_transfer: %f", real'(count[7] ) / real'(cycle_count));
        $display("aw_mst_transfer:    %f", real'(count[9] ) / real'(cycle_count));
        $display("ar_mst_transfer:    %f", real'(count[11]) / real'(cycle_count));
        $display("aw_desc_spm:        %f", real'(count[13]) / real'(cycle_count));
        $display("ar_desc_spm:        %f", real'(count[15]) / real'(cycle_count));
        $display("aw_desc_cache:      %f", real'(count[17]) / real'(cycle_count));
        $display("ar_desc_cache:      %f", real'(count[19]) / real'(cycle_count));
        $display("config_desc:        %f", real'(count[21]) / real'(cycle_count));
        $display("hit_write_spm:      %f", real'(count[23]) / real'(cycle_count));
        $display("hit_read_spm:       %f", real'(count[25]) / real'(cycle_count));
        $display("miss_write_spm:     %f", real'(count[27]) / real'(cycle_count));
        $display("miss_read_spm:      %f", real'(count[29]) / real'(cycle_count));
        $display("hit_write_cache:    %f", real'(count[31]) / real'(cycle_count));
        $display("hit_read_cache:     %f", real'(count[33]) / real'(cycle_count));
        $display("miss_write_cache:   %f", real'(count[35]) / real'(cycle_count));
        $display("miss_read_cache:    %f", real'(count[37]) / real'(cycle_count));
        $display("refill_write:       %f", real'(count[39]) / real'(cycle_count));
        $display("refill_read:        %f", real'(count[41]) / real'(cycle_count));
        $display("evict_write:        %f", real'(count[43]) / real'(cycle_count));
        $display("evict_read:         %f", real'(count[45]) / real'(cycle_count));
        $display("evict_flush:        %f", real'(count[47]) / real'(cycle_count));
        $display("evict_unit_req:     %f", real'(count[48]) / real'(cycle_count));
        $display("refill_unit_req:    %f", real'(count[49]) / real'(cycle_count));
        $display("w_chan_unit_req:    %f", real'(count[50]) / real'(cycle_count));
        $display("r_chan_unit_req:    %f", real'(count[51]) / real'(cycle_count));
        $display("##################################################################");
        // After printing, reset the counters.
        cycle_count = 0;
        for (int unsigned i = 0; i < NumCounters; i++) begin
          count[i] = 0;
        end
      end // print counters
    end // forever begin
  end : proc_counters

  // -------------------------------
  // AXI
  // -------------------------------
  AXI_BUS #(
    .AXI_ADDR_WIDTH ( llc_axi::AddrWidth     ),
    .AXI_DATA_WIDTH ( llc_axi::DataWidth     ),
    .AXI_ID_WIDTH   ( llc_axi::IdWidthSlave  ),
    .AXI_USER_WIDTH ( 1                      )
  ) master();

  AXI_LITE #(
    .AXI_ADDR_WIDTH ( llc_axi::AddrWidth     ),
    .AXI_DATA_WIDTH ( llc_axi::DataWidthLite )
    ) axi_lite();

  AXI_BUS #(
    .AXI_ADDR_WIDTH ( llc_axi::AddrWidth     ),
    .AXI_DATA_WIDTH ( llc_axi::DataWidth     ),
    .AXI_ID_WIDTH   ( llc_axi::IdWidthMaster ),
    .AXI_USER_WIDTH ( 1                      )
  ) axi_memory();

  `AXI_ASSIGN(master, master_dv)
  `AXI_LITE_ASSIGN(axi_lite, axi_lite_dv)
  `AXI_ASSIGN(axi_memory_dv, axi_memory)

  `AXI_ASSIGN_TO_REQ    ( axi_llc_req,  master       )
  `AXI_ASSIGN_FROM_RESP ( master,       axi_llc_resp )

  `AXI_ASSIGN_FROM_REQ  ( axi_memory,   axi_mem_req  )
  `AXI_ASSIGN_TO_RESP   ( axi_mem_resp, axi_memory   )

  `AXI_LITE_ASSIGN_TO_REQ    ( axi_lite_conf_req, axi_lite           )
  `AXI_LITE_ASSIGN_FROM_RESP ( axi_lite,          axi_lite_conf_resp )

  `AXI_ASSIGN_MONITOR(scoreboard_dv, master)

  // -------------------------------
  // Instance DUT
  // -------------------------------

  axi_llc_top #(
    .AxiCfg         ( AxiCfg                  ),
    .SetAssociativity( 32'd8                  ),
    .NoLines         ( 32'd1024               ),
    .NoBlocks        ( 32'd8                  ),
    .slv_aw_chan_t  ( llc_axi::aw_chan_slv_t  ),
    .mst_aw_chan_t  ( llc_axi::aw_chan_mst_t  ),
    .w_chan_t       ( llc_axi::w_chan_t       ),
    .slv_b_chan_t   ( llc_axi::b_chan_slv_t   ),
    .mst_b_chan_t   ( llc_axi::b_chan_mst_t   ),
    .slv_ar_chan_t  ( llc_axi::ar_chan_slv_t  ),
    .mst_ar_chan_t  ( llc_axi::ar_chan_mst_t  ),
    .slv_r_chan_t   ( llc_axi::r_chan_slv_t   ),
    .mst_r_chan_t   ( llc_axi::r_chan_mst_t   ),
    .slv_req_t      ( llc_axi::req_slv_t      ),
    .slv_resp_t     ( llc_axi::resp_slv_t     ),
    .mst_req_t      ( llc_axi::req_mst_t      ),
    .mst_resp_t     ( llc_axi::resp_mst_t     ),
    .lite_req_t     ( llc_axi::req_lite_t     ),
    .lite_resp_t    ( llc_axi::resp_lite_t    )
  ) dut (
    .clk_i       ( clk          ),  // Clock
  // input clk_en, // Clock Enable
    .rst_ni      ( rst_n        ),  // Asynchronous reset active low
    .test_i      ( 1'b0         ),

  // AXI Slave Port ( from CPU side )
    .slv_req_i   ( axi_llc_req  ),
    .slv_resp_o  ( axi_llc_resp ),
  // AXI Master Port ( to memory )
    .mst_req_o   ( axi_mem_req  ),
    .mst_resp_i  ( axi_mem_resp ),

  // AXI Slafe Port ( Config )
    .conf_req_i  ( axi_lite_conf_req  ),
    .conf_resp_o ( axi_lite_conf_resp ),
  // address mapping
    .ram_start_addr_i ( 64'h2000_0000  ),
    .ram_end_addr_i   ( 64'h2010_0000  ),
    .spm_start_addr_i ( 64'h1000_0000  ),
    .axi_llc_events_o ( axi_llc_events )
  );
endmodule
