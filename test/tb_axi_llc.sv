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
// File:   tb_aw_splitter.sv
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

  // ---------------------
  // Testbench signals
  // ---------------------
  logic end_of_sim;

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

      rand_axi_master = new(  master_dv     );
      axi_lite_drv    = new(  axi_lite_dv   );
      axi_monitor     = new(  "Monitor",
                              64'h1000_0000,
                              64'h0008_0800,
                              monitor_intf,
                              axi_memory_dv );

      fork
      axi_monitor.monitor_channel();
      begin
        rand_axi_master.reset();
        axi_lite_drv.reset_master();
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
          rand_axi_master.run(1000, 2000);
          repeat (1000) @(posedge clk);

          print_test_info("Flushing the cache and reversing the SPM definition");
          repeat (10) @(posedge clk);
          fork
            axi_lite_drv.send_aw(64'h0001_0000, axi_pkg::prot_t'(1'b0));
            axi_lite_drv.send_w(32'h0000_00F0, '1);
          join
          axi_lite_drv.recv_b(resp);
          $info("AXI-Lite B: resp %h", resp);
          repeat (100000) @(posedge clk);

          print_test_info("1000 reads and 2000 writes on cache region.");
          rand_axi_master.run(1000, 2000);
          repeat (1000) @(posedge clk);

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
    .ram_start_addr_i ( 64'h2000_0000 ),
    .ram_end_addr_i   ( 64'h2010_0000 ),
    .spm_start_addr_i ( 64'h1000_0000 )
  );
endmodule
