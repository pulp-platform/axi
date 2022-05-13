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
// Authors:
// - Wolfgang Roenninger <wroennin@iis.ee.ethz.ch>

/// Testbench for the module `axi_llc_top`.
module tb_axi_llc #(
  /// Set Associativity of the LLC
  parameter int unsigned TbSetAssociativity = 32'd8,
  /// Number of cache lines of the LLC
  parameter int unsigned TbNumLines         = 32'd256,
  /// Number of Blocks per cache line
  parameter int unsigned TbNumBlocks        = 32'd8,
  /// ID width of the Full AXI slave port, master port has ID `AxiIdWidthFull + 32'd1`
  parameter int unsigned TbAxiIdWidthFull   = 32'd6,
  /// Address width of the full AXI bus
  parameter int unsigned TbAxiAddrWidthFull = 32'd32,
  /// Data width of the full AXI bus
  parameter int unsigned TbAxiDataWidthFull = 32'd128,
  /// Address width of the AXI configureation port
  parameter int unsigned TbAxiAddrWidthLite = 32'd32,
  /// Data width of the AXI configuration port
  parameter int unsigned TbAxiDataWidthLite = 32'd32,
  /// Number of random write transactions in a testblock.
  parameter int unsigned TbNumWrites        = 32'd1100,
  /// Number of random read transactions in a testblock.
  parameter int unsigned TbNumReads         = 32'd1500,
  /// Cycle time for the TB clock generator
  parameter time         TbCyclTime         = 10ns,
  /// Application time to the DUT
  parameter time         TbApplTime         = 2ns,
  /// Test time of the DUT
  parameter time         TbTestTime         = 8ns
);
  /////////////////////////////
  // Axi channel definitions //
  /////////////////////////////
  `include "axi/typedef.svh"
  `include "axi/assign.svh"

  localparam int unsigned TbAxiStrbWidthFull = TbAxiDataWidthFull / 32'd8;
  localparam int unsigned TbAxiUserWidthFull = 32'd1;

  typedef logic [TbAxiIdWidthFull-1:0]     axi_slv_id_t;
  typedef logic [TbAxiIdWidthFull:0]       axi_mst_id_t;
  typedef logic [TbAxiAddrWidthFull-1:0]   axi_addr_t;
  typedef logic [TbAxiDataWidthFull-1:0]   axi_data_t;
  typedef logic [TbAxiStrbWidthFull-1:0]   axi_strb_t;
  typedef logic [TbAxiUserWidthFull-1:0]   axi_user_t;

  `AXI_TYPEDEF_AW_CHAN_T(axi_slv_aw_t, axi_addr_t, axi_slv_id_t, axi_user_t)
  `AXI_TYPEDEF_AW_CHAN_T(axi_mst_aw_t, axi_addr_t, axi_mst_id_t, axi_user_t)
  `AXI_TYPEDEF_W_CHAN_T(axi_w_t, axi_data_t, axi_strb_t, axi_user_t)
  `AXI_TYPEDEF_B_CHAN_T(axi_slv_b_t, axi_slv_id_t, axi_user_t)
  `AXI_TYPEDEF_B_CHAN_T(axi_mst_b_t, axi_mst_id_t, axi_user_t)
  `AXI_TYPEDEF_AR_CHAN_T(axi_slv_ar_t, axi_addr_t, axi_slv_id_t, axi_user_t)
  `AXI_TYPEDEF_AR_CHAN_T(axi_mst_ar_t, axi_addr_t, axi_mst_id_t, axi_user_t)
  `AXI_TYPEDEF_R_CHAN_T(axi_slv_r_t, axi_data_t, axi_slv_id_t, axi_user_t)
  `AXI_TYPEDEF_R_CHAN_T(axi_mst_r_t, axi_data_t, axi_mst_id_t, axi_user_t)

  `AXI_TYPEDEF_REQ_T(axi_slv_req_t, axi_slv_aw_t, axi_w_t, axi_slv_ar_t)
  `AXI_TYPEDEF_RESP_T(axi_slv_resp_t, axi_slv_b_t, axi_slv_r_t)
  `AXI_TYPEDEF_REQ_T(axi_mst_req_t, axi_mst_aw_t, axi_w_t, axi_mst_ar_t)
  `AXI_TYPEDEF_RESP_T(axi_mst_resp_t, axi_mst_b_t, axi_mst_r_t)

  localparam int unsigned TbAxiStrbWidthLite = TbAxiDataWidthLite / 32'd8;

  typedef logic [TbAxiAddrWidthLite-1:0] axi_lite_addr_t;
  typedef logic [TbAxiDataWidthLite-1:0] axi_lite_data_t;
  typedef logic [TbAxiStrbWidthLite-1:0] axi_lite_strb_t;

  `AXI_LITE_TYPEDEF_AW_CHAN_T(aw_lite_t, axi_lite_addr_t)
  `AXI_LITE_TYPEDEF_W_CHAN_T(w_lite_t, axi_lite_data_t, axi_lite_strb_t)
  `AXI_LITE_TYPEDEF_B_CHAN_T(b_lite_t)
  `AXI_LITE_TYPEDEF_AR_CHAN_T(ar_lite_t, axi_lite_addr_t)
  `AXI_LITE_TYPEDEF_R_CHAN_T(r_lite_t, axi_lite_data_t)

  `AXI_LITE_TYPEDEF_REQ_T(req_lite_t, aw_lite_t, w_lite_t, ar_lite_t)
  `AXI_LITE_TYPEDEF_RESP_T(resp_lite_t, b_lite_t, r_lite_t)

  typedef logic [7:0] byte_t;

  // rule definitions
  typedef struct packed {
    int unsigned idx;
    axi_addr_t   start_addr;
    axi_addr_t   end_addr;
  } rule_full_t;

  // Config register addresses
  typedef enum logic [7:0] {
    CfgSpm    = axi_lite_addr_t'(8'h00),
    CfgFlush  = axi_lite_addr_t'(8'h08),
    Flushed   = axi_lite_addr_t'(8'h10),
    BistOut   = axi_lite_addr_t'(8'h18),
    SetAsso   = axi_lite_addr_t'(8'h20),
    NumLines  = axi_lite_addr_t'(8'h28),
    NumBlocks = axi_lite_addr_t'(8'h30),
    Version   = axi_lite_addr_t'(8'h38)
  } llc_cfg_addr_e;

  ////////////////////////////////
  // Stimuli generator typedefs //
  ////////////////////////////////
  typedef axi_test::axi_rand_master #(
    .AW                   ( TbAxiAddrWidthFull ),
    .DW                   ( TbAxiDataWidthFull ),
    .IW                   ( TbAxiIdWidthFull   ),
    .UW                   ( TbAxiUserWidthFull ),
    .TA                   ( TbApplTime         ),
    .TT                   ( TbTestTime         ),
    .MAX_READ_TXNS        ( 5                  ),
    .MAX_WRITE_TXNS       ( 5                  ),
    .AX_MIN_WAIT_CYCLES   ( 0                  ),
    .AX_MAX_WAIT_CYCLES   ( 50                 ),
    .W_MIN_WAIT_CYCLES    ( 0                  ),
    .W_MAX_WAIT_CYCLES    ( 0                  ),
    .RESP_MIN_WAIT_CYCLES ( 0                  ),
    .RESP_MAX_WAIT_CYCLES ( 0                  ),
    .AXI_BURST_FIXED      ( 1'b0               ),
    .AXI_BURST_INCR       ( 1'b1               ),
    .AXI_BURST_WRAP       ( 1'b0               )
  ) axi_rand_master_t;

  typedef axi_test::axi_rand_slave #(
    .AW                   ( TbAxiAddrWidthFull        ),
    .DW                   ( TbAxiDataWidthFull        ),
    .IW                   ( TbAxiIdWidthFull + 32'd1  ),
    .UW                   ( TbAxiUserWidthFull        ),
    .TA                   ( TbApplTime                ),
    .TT                   ( TbTestTime                ),
    .AX_MIN_WAIT_CYCLES   ( 0                         ),
    .AX_MAX_WAIT_CYCLES   ( 50                        ),
    .R_MIN_WAIT_CYCLES    ( 10                        ),
    .R_MAX_WAIT_CYCLES    ( 20                        ),
    .RESP_MIN_WAIT_CYCLES ( 10                        ),
    .RESP_MAX_WAIT_CYCLES ( 20                        ),
    .MAPPED               ( 1'b1                      )
  ) axi_rand_slave_t;

  typedef axi_test::axi_lite_rand_master #(
    .AW ( TbAxiAddrWidthLite ),
    .DW ( TbAxiDataWidthLite ),
    .TA ( TbApplTime         ),
    .TT ( TbTestTime         )
  ) axi_lite_rand_master_t;

  typedef axi_test::axi_scoreboard #(
    .IW( TbAxiIdWidthFull   ),
    .AW( TbAxiAddrWidthFull ),
    .DW( TbAxiDataWidthFull ),
    .UW( TbAxiUserWidthFull ),
    .TT( TbTestTime         )
  ) axi_scoreboard_cpu_t;

  typedef axi_test::axi_scoreboard #(
    .IW( TbAxiIdWidthFull + 32'd1  ),
    .AW( TbAxiAddrWidthFull        ),
    .DW( TbAxiDataWidthFull        ),
    .UW( TbAxiUserWidthFull        ),
    .TT( TbTestTime                )
  ) axi_scoreboard_mem_t;

  ////////////////////
  // Address Ranges //
  ////////////////////
  localparam axi_addr_t SpmRegionStart     = axi_addr_t'(0);
  localparam axi_addr_t SpmRegionLength    =
      axi_addr_t'(TbSetAssociativity * TbNumLines * TbNumBlocks * TbAxiDataWidthFull / 32'd8);
  localparam axi_addr_t CachedRegionStart  = axi_addr_t'(32'h8000_0000);
  localparam axi_addr_t CachedRegionLength = axi_addr_t'(2*SpmRegionLength);

  /////////////////
  // Dut signals //
  /////////////////
  logic clk, rst_n, test;
  axi_llc_pkg::events_t llc_events;
  // AXI channels
  axi_slv_req_t  axi_cpu_req;
  axi_slv_resp_t axi_cpu_res;
  axi_mst_req_t  axi_mem_req;
  axi_mst_resp_t axi_mem_res;
  req_lite_t     axi_cfg_req;
  resp_lite_t    axi_cfg_res;
  // Tb signals
  logic enable_counters, print_counters, enable_progress;

  ///////////////////////
  // AXI DV interfaces //
  ///////////////////////
  AXI_BUS_DV #(
    .AXI_ADDR_WIDTH ( TbAxiAddrWidthFull ),
    .AXI_DATA_WIDTH ( TbAxiDataWidthFull ),
    .AXI_ID_WIDTH   ( TbAxiIdWidthFull   ),
    .AXI_USER_WIDTH ( TbAxiUserWidthFull )
  ) axi_cpu_intf_dv (
    .clk_i ( clk )
  );

    AXI_BUS_DV #(
    .AXI_ADDR_WIDTH ( TbAxiAddrWidthFull ),
    .AXI_DATA_WIDTH ( TbAxiDataWidthFull ),
    .AXI_ID_WIDTH   ( TbAxiIdWidthFull   ),
    .AXI_USER_WIDTH ( TbAxiUserWidthFull )
  ) score_cpu_intf_dv (
    .clk_i ( clk )
  );

  AXI_BUS_DV #(
    .AXI_ADDR_WIDTH ( TbAxiAddrWidthFull       ),
    .AXI_DATA_WIDTH ( TbAxiDataWidthFull       ),
    .AXI_ID_WIDTH   ( TbAxiIdWidthFull + 32'd1 ),
    .AXI_USER_WIDTH ( TbAxiUserWidthFull       )
  ) axi_mem_intf_dv (
    .clk_i ( clk )
  );

    AXI_BUS_DV #(
    .AXI_ADDR_WIDTH ( TbAxiAddrWidthFull       ),
    .AXI_DATA_WIDTH ( TbAxiDataWidthFull       ),
    .AXI_ID_WIDTH   ( TbAxiIdWidthFull + 32'd1 ),
    .AXI_USER_WIDTH ( TbAxiUserWidthFull       )
  ) score_mem_intf_dv (
    .clk_i ( clk )
  );

  AXI_LITE_DV #(
    .AXI_ADDR_WIDTH ( TbAxiAddrWidthLite ),
    .AXI_DATA_WIDTH ( TbAxiDataWidthLite )
  ) axi_cfg_intf_dv (
    .clk_i ( clk )
  );

  `AXI_ASSIGN_TO_REQ(axi_cpu_req, axi_cpu_intf_dv)
  `AXI_ASSIGN_FROM_RESP(axi_cpu_intf_dv, axi_cpu_res)

  `AXI_ASSIGN_FROM_REQ(axi_mem_intf_dv, axi_mem_req)
  `AXI_ASSIGN_TO_RESP(axi_mem_res, axi_mem_intf_dv)

  `AXI_ASSIGN_MONITOR(score_cpu_intf_dv, axi_cpu_intf_dv)
  `AXI_ASSIGN_MONITOR(score_mem_intf_dv, axi_mem_intf_dv)

  `AXI_LITE_ASSIGN_TO_REQ(axi_cfg_req, axi_cfg_intf_dv)
  `AXI_LITE_ASSIGN_FROM_RESP(axi_cfg_intf_dv, axi_cfg_res)

  /////////////////////////
  // Clock and Reset gen //
  /////////////////////////
  clk_rst_gen #(
    .ClkPeriod     ( TbCyclTime ),
    .RstClkCycles  ( 32'd5    )
  ) i_clk_rst_gen (
    .clk_o  ( clk   ),
    .rst_no ( rst_n )
  );
  assign test = 1'b0;

  ////////////////////////////////////////
  // Scoreboards and simulation control //
  ////////////////////////////////////////
  //axi_rand_master_t axi_master;
  //axi_rand_slave_t  axi_slave;


  initial begin : proc_sim_crtl
    automatic axi_scoreboard_cpu_t   cpu_scoreboard  = new( score_cpu_intf_dv             );
    automatic axi_scoreboard_mem_t   mem_scoreboard  = new( score_mem_intf_dv             );
    automatic axi_rand_master_t      axi_master      = new( axi_cpu_intf_dv               );
    automatic axi_lite_rand_master_t axi_lite_master = new( axi_cfg_intf_dv , "CfgMaster" );
    // Variables for the LITE config thingy.
    automatic axi_lite_addr_t lite_addr  = axi_lite_addr_t'(0);
    automatic axi_pkg::prot_t lite_prot  = axi_pkg::prot_t'(0);
    automatic axi_lite_data_t lite_rdata = axi_lite_data_t'(0);
    automatic axi_lite_data_t lite_wdata = axi_lite_data_t'(0);
    automatic axi_lite_strb_t lite_wstrb = axi_lite_strb_t'(0);
    automatic axi_pkg::resp_t lite_resp  = axi_pkg::RESP_OKAY;

    // Reset the AXI drivers and scoreboards
    cpu_scoreboard.reset();
    mem_scoreboard.reset();
    axi_master.reset();
    axi_lite_master.reset();
    enable_counters = 1'b0;
    print_counters  = 1'b0;
    enable_progress = 1'b0;

    // Set some mem regions for rand axi master
    axi_master.add_memory_region(CachedRegionStart, CachedRegionStart + 2*CachedRegionLength,
                                 axi_pkg::WBACK_RWALLOCATE);
    axi_master.add_memory_region(SpmRegionStart, SpmRegionStart + SpmRegionLength,
                                 axi_pkg::NORMAL_NONCACHEABLE_BUFFERABLE);

    cpu_scoreboard.enable_all_checks();
    mem_scoreboard.enable_all_checks();

    @(posedge rst_n);
    cpu_scoreboard.monitor();
    mem_scoreboard.monitor();
    enable_counters = 1'b1;
    enable_progress = 1'b1;

    $info("Read all Cfg registers.");
    axi_lite_master.read(CfgSpm,    lite_prot, lite_rdata, lite_resp);
    axi_lite_master.read(CfgFlush,  lite_prot, lite_rdata, lite_resp);
    axi_lite_master.read(Flushed,   lite_prot, lite_rdata, lite_resp);
    axi_lite_master.read(BistOut,   lite_prot, lite_rdata, lite_resp);
    axi_lite_master.read(SetAsso,   lite_prot, lite_rdata, lite_resp);
    axi_lite_master.read(NumLines,  lite_prot, lite_rdata, lite_resp);
    axi_lite_master.read(NumBlocks, lite_prot, lite_rdata, lite_resp);
    axi_lite_master.read(Version,   lite_prot, lite_rdata, lite_resp);

    $info("Random read and write");
    axi_master.run(TbNumReads, TbNumWrites);
    flush_all(axi_lite_master);
    compare_mems(cpu_scoreboard, mem_scoreboard);
    clear_spm_cpu(cpu_scoreboard);

    $info("Enable lower half SPM");
    lite_addr  = CfgSpm;
    lite_wdata = axi_lite_data_t'({((TbSetAssociativity == 32'd1) ? 32'd1 : (TbSetAssociativity/2)){1'b1}});
    lite_wstrb = axi_lite_strb_t'({TbAxiStrbWidthLite{1'b1}});
    axi_lite_master.write(lite_addr, lite_prot, lite_wdata, lite_wstrb, lite_resp);
    axi_master.run(TbNumReads, TbNumWrites);
    flush_all(axi_lite_master);
    compare_mems(cpu_scoreboard, mem_scoreboard);
    clear_spm_cpu(cpu_scoreboard);

    $info("All SPM");
    lite_addr  = CfgSpm;
    lite_wdata = axi_lite_data_t'({TbSetAssociativity{1'b1}});
    lite_wstrb = axi_lite_strb_t'({TbAxiStrbWidthLite{1'b1}});
    axi_lite_master.write(lite_addr, lite_prot, lite_wdata, lite_wstrb, lite_resp);
    axi_master.run(TbNumReads, TbNumWrites);
    flush_all(axi_lite_master);
    compare_mems(cpu_scoreboard, mem_scoreboard);
    clear_spm_cpu(cpu_scoreboard);

    $info("Random read and write");
    lite_addr  = CfgSpm;
    lite_wdata = axi_lite_data_t'({TbSetAssociativity{1'b0}});
    lite_wstrb = axi_lite_strb_t'({TbAxiStrbWidthLite{1'b1}});
    axi_lite_master.write(lite_addr, lite_prot, lite_wdata, lite_wstrb, lite_resp);
    axi_master.run(TbNumReads, TbNumWrites);

    print_perf_couters();

    flush_all(axi_lite_master);
    compare_mems(cpu_scoreboard, mem_scoreboard);
    clear_spm_cpu(cpu_scoreboard);


    $display("Tests ended!");
    $stop();
  end

  initial begin : proc_sim_mem
    automatic axi_rand_slave_t axi_slave = new( axi_mem_intf_dv );
    axi_slave.reset();
    @(posedge rst_n);
    axi_slave.run();
  end

  task compare_mems(axi_scoreboard_cpu_t cpu_scoreboard, axi_scoreboard_mem_t mem_scoreboard);
    automatic byte_t     cpu_byte, mem_byte;
    automatic axi_addr_t compare_addr = CachedRegionStart;
    while (compare_addr < (CachedRegionStart + 2*CachedRegionLength)) begin
      cpu_scoreboard.get_byte(compare_addr, cpu_byte);
      mem_scoreboard.get_byte(compare_addr, mem_byte);
      // As the whole cache line is written back there are some bytes which are only present
      // in the scoreboard of the memory and X in the CPU memory.
      if (cpu_byte !== 8'hxx) begin
        assert (cpu_byte === mem_byte) /*$display("Pass addr: %h", compare_addr);*/ else
          $error("At addr: %h differeing memory values are encoutered! \n CPU: %h \n MEM: %h",
              compare_addr, cpu_byte, mem_byte);
      end
      compare_addr++;
    end
  endtask : compare_mems

  task clear_spm_cpu(axi_scoreboard_cpu_t cpu_scoreboard);
    cpu_scoreboard.clear_range(SpmRegionStart, SpmRegionStart + SpmRegionLength);
  endtask : clear_spm_cpu

  task flush_all(axi_lite_rand_master_t axi_lite_master);
    automatic axi_pkg::resp_t l_resp;
    automatic axi_lite_data_t data = {TbSetAssociativity{1'b1}};
    $info("Flushing the cache!");
    axi_lite_master.write(CfgFlush, axi_pkg::prot_t'(0), data,
        axi_lite_strb_t'({TbAxiStrbWidthLite{1'b1}}), l_resp);
    // poll on the flush config untill it is cleared
    while (|data) begin
      axi_lite_master.read(CfgFlush, axi_pkg::prot_t'(0), data, l_resp);
      repeat (5000) @(posedge clk);
    end
    $info("Finished flushing the cache!");
  endtask : flush_all

  task print_perf_couters();
    @(negedge clk);
    print_counters = 1'b1;
    @(negedge clk);
    print_counters = 1'b0;
  endtask : print_perf_couters


  ///////////////////////
  // Design under test //
  ///////////////////////
  axi_llc_top #(
    .SetAssociativity ( TbSetAssociativity ),
    .NumLines         ( TbNumLines         ),
    .NumBlocks        ( TbNumBlocks        ),
    .AxiIdWidth       ( TbAxiIdWidthFull   ),
    .AxiAddrWidth     ( TbAxiAddrWidthFull ),
    .AxiDataWidth     ( TbAxiDataWidthFull ),
    .AxiUserWidth     ( TbAxiUserWidthFull ),
    .AxiLiteAddrWidth ( TbAxiAddrWidthLite ),
    .AxiLiteDataWidth ( TbAxiDataWidthLite ),
    .slv_req_t        ( axi_slv_req_t      ),
    .slv_resp_t       ( axi_slv_resp_t     ),
    .mst_req_t        ( axi_mst_req_t      ),
    .mst_resp_t       ( axi_mst_resp_t     ),
    .lite_req_t       ( req_lite_t         ),
    .lite_resp_t      ( resp_lite_t        ),
    .rule_full_t      ( rule_full_t        )
  ) i_axi_llc_dut (
    .clk_i               ( clk                                    ),
    .rst_ni              ( rst_n                                  ),
    .test_i              ( test                                   ),
    .slv_req_i           ( axi_cpu_req                            ),
    .slv_resp_o          ( axi_cpu_res                            ),
    .mst_req_o           ( axi_mem_req                            ),
    .mst_resp_i          ( axi_mem_res                            ),
    .conf_req_i          ( axi_cfg_req                            ),
    .conf_resp_o         ( axi_cfg_res                            ),
    .cached_start_addr_i ( CachedRegionStart                      ),
    .cached_end_addr_i   ( CachedRegionStart + CachedRegionLength ),
    .spm_start_addr_i    ( SpmRegionStart                         ),
    .axi_llc_events_o    ( llc_events                             )
  );

  ////////////////////////////
  // `Perf Counter` process //
  ////////////////////////////
  localparam int unsigned NumCounters = 32'd52;
  localparam int unsigned PrintCycles = 32'd100;
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
      #(TbTestTime);
      cycle_count++;

      if (enable_counters) begin
        if (llc_events.aw_slv_transfer.active) begin
          count[0] = count[0] + llc_events.aw_slv_transfer.num_bytes;
          count[1] = count[1] + 64'd1;
          if ((count[1]%PrintCycles == 0) && enable_progress) begin
            $display("%0t> AW transaction: %d", $time(), count[1]);
          end
        end
        if (llc_events.ar_slv_transfer.active) begin
          count[2] = count[2] + llc_events.ar_slv_transfer.num_bytes;
          count[3] = count[3] + 64'd1;
          if ((count[3]%PrintCycles == 0) && enable_progress) begin
            $display("%0t> AR transaction: %d", $time(), count[3]);
          end
        end
        if (llc_events.aw_bypass_transfer.active) begin
          count[4] = count[4] + llc_events.aw_bypass_transfer.num_bytes;
          count[5] = count[5] + 64'd1;
        end
        if (llc_events.ar_bypass_transfer.active) begin
          count[6] = count[6] + llc_events.ar_bypass_transfer.num_bytes;
          count[7] = count[7] + 64'd1;
        end
        if (llc_events.aw_mst_transfer.active) begin
          count[8] = count[8] + llc_events.aw_mst_transfer.num_bytes;
          count[9] = count[9] + 64'd1;
        end
        if (llc_events.ar_mst_transfer.active) begin
          count[10] = count[10] + llc_events.ar_mst_transfer.num_bytes;
          count[11] = count[11] + 64'd1;
        end
        if (llc_events.aw_desc_spm.active) begin
          count[12] = count[12] + llc_events.aw_desc_spm.num_bytes;
          count[13] = count[13] + 64'd1;
        end
        if (llc_events.ar_desc_spm.active) begin
          count[14] = count[14] + llc_events.ar_desc_spm.num_bytes;
          count[15] = count[15] + 64'd1;
        end
        if (llc_events.aw_desc_cache.active) begin
          count[16] = count[16] + llc_events.aw_desc_cache.num_bytes;
          count[17] = count[17] + 64'd1;
        end
        if (llc_events.ar_desc_cache.active) begin
          count[18] = count[18] + llc_events.ar_desc_cache.num_bytes;
          count[19] = count[19] + 64'd1;
        end
        if (llc_events.config_desc.active) begin
          count[20] = count[20] + llc_events.config_desc.num_bytes;
          count[21] = count[21] + 64'd1;
        end
        if (llc_events.hit_write_spm.active) begin
          count[22] = count[22] + llc_events.hit_write_spm.num_bytes;
          count[23] = count[23] + 64'd1;
        end
        if (llc_events.hit_read_spm.active) begin
          count[24] = count[24] + llc_events.hit_read_spm.num_bytes;
          count[25] = count[25] + 64'd1;
        end
        if (llc_events.miss_write_spm.active) begin
          count[26] = count[26] + llc_events.miss_write_spm.num_bytes;
          count[27] = count[27] + 64'd1;
        end
        if (llc_events.miss_read_spm.active) begin
          count[28] = count[28] + llc_events.miss_read_spm.num_bytes;
          count[29] = count[29] + 64'd1;
        end
        if (llc_events.hit_write_cache.active) begin
          count[30] = count[30] + llc_events.hit_write_cache.num_bytes;
          count[31] = count[31] + 64'd1;
        end
        if (llc_events.hit_read_cache.active) begin
          count[32] = count[32] + llc_events.hit_read_cache.num_bytes;
          count[33] = count[33] + 64'd1;
        end
        if (llc_events.miss_write_cache.active) begin
          count[34] = count[34] + llc_events.miss_write_cache.num_bytes;
          count[35] = count[35] + 64'd1;
        end
        if (llc_events.miss_read_cache.active) begin
          count[36] = count[36] + llc_events.miss_read_cache.num_bytes;
          count[37] = count[37] + 64'd1;
        end
        if (llc_events.refill_write.active) begin
          count[38] = count[38] + llc_events.refill_write.num_bytes;
          count[39] = count[39] + 64'd1;
        end
        if (llc_events.refill_read.active) begin
          count[40] = count[40] + llc_events.refill_read.num_bytes;
          count[41] = count[41] + 64'd1;
        end
        if (llc_events.evict_write.active) begin
          count[42] = count[42] + llc_events.evict_write.num_bytes;
          count[43] = count[43] + 64'd1;
        end
        if (llc_events.evict_read.active) begin
          count[44] = count[44] + llc_events.evict_read.num_bytes;
          count[45] = count[45] + 64'd1;
        end
        if (llc_events.evict_flush.active) begin
          count[46] = count[46] + llc_events.evict_flush.num_bytes;
          count[47] = count[47] + 64'd1;
        end
        if (llc_events.evict_unit_req) begin
          count[48] = count[48] + 64'd1;
        end
        if (llc_events.refill_unit_req) begin
          count[49] = count[49] + 64'd1;
        end
        if (llc_events.w_chan_unit_req) begin
          count[50] = count[50] + 64'd1;
        end
        if (llc_events.r_chan_unit_req) begin
          count[51] = count[51] + 64'd1;
        end
      end

      if (print_counters) begin
        $display("##################################################################");
        $display("LLC: Performance");
        $display("Max Bandwidth of one AXI channel: %f MiB/sec", (real'(TbAxiDataWidthFull)
            / real'(8)) * (real'(1000000000) /  real'(TbCyclTime)) / 1024 / 1024);
        $display("##################################################################");
        $display("Bandwidths:");
        $display("aw_slv_transfer:    %f MiB/sec", real'(count[0] ) / real'(cycle_count)
            / real'(TbCyclTime) * real'(1000000000) / 1024 / 1024);
        $display("ar_slv_transfer:    %f MiB/sec", real'(count[2] ) / real'(cycle_count)
            / real'(TbCyclTime) * real'(1000000000) / 1024 / 1024);
        $display("aw_bypass_transfer: %f MiB/sec", real'(count[4] ) / real'(cycle_count)
            / real'(TbCyclTime) * real'(1000000000) / 1024 / 1024);
        $display("ar_bypass_transfer: %f MiB/sec", real'(count[6] ) / real'(cycle_count)
            / real'(TbCyclTime) * real'(1000000000) / 1024 / 1024);
        $display("aw_mst_transfer:    %f MiB/sec", real'(count[8] ) / real'(cycle_count)
            / real'(TbCyclTime) * real'(1000000000) / 1024 / 1024);
        $display("ar_mst_transfer:    %f MiB/sec", real'(count[10]) / real'(cycle_count)
            / real'(TbCyclTime) * real'(1000000000) / 1024 / 1024);
        $display("aw_desc_spm:        %f MiB/sec", real'(count[12]) / real'(cycle_count)
            / real'(TbCyclTime) * real'(1000000000) / 1024 / 1024);
        $display("ar_desc_spm:        %f MiB/sec", real'(count[14]) / real'(cycle_count)
            / real'(TbCyclTime) * real'(1000000000) / 1024 / 1024);
        $display("aw_desc_cache:      %f MiB/sec", real'(count[16]) / real'(cycle_count)
            / real'(TbCyclTime) * real'(1000000000) / 1024 / 1024);
        $display("ar_desc_cache:      %f MiB/sec", real'(count[18]) / real'(cycle_count)
            / real'(TbCyclTime) * real'(1000000000) / 1024 / 1024);
        $display("config_desc:        %f MiB/sec", real'(count[20]) / real'(cycle_count)
            / real'(TbCyclTime) * real'(1000000000) / 1024 / 1024);
        $display("hit_write_spm:      %f MiB/sec", real'(count[22]) / real'(cycle_count)
            / real'(TbCyclTime) * real'(1000000000) / 1024 / 1024);
        $display("hit_read_spm:       %f MiB/sec", real'(count[24]) / real'(cycle_count)
            / real'(TbCyclTime) * real'(1000000000) / 1024 / 1024);
        $display("miss_write_spm:     %f MiB/sec", real'(count[26]) / real'(cycle_count)
            / real'(TbCyclTime) * real'(1000000000) / 1024 / 1024);
        $display("miss_read_spm:      %f MiB/sec", real'(count[28]) / real'(cycle_count)
            / real'(TbCyclTime) * real'(1000000000) / 1024 / 1024);
        $display("hit_write_cache:    %f MiB/sec", real'(count[30]) / real'(cycle_count)
            / real'(TbCyclTime) * real'(1000000000) / 1024 / 1024);
        $display("hit_read_cache:     %f MiB/sec", real'(count[32]) / real'(cycle_count)
            / real'(TbCyclTime) * real'(1000000000) / 1024 / 1024);
        $display("miss_write_cache:   %f MiB/sec", real'(count[34]) / real'(cycle_count)
            / real'(TbCyclTime) * real'(1000000000) / 1024 / 1024);
        $display("miss_read_cache:    %f MiB/sec", real'(count[36]) / real'(cycle_count)
            / real'(TbCyclTime) * real'(1000000000) / 1024 / 1024);
        $display("refill_write:       %f MiB/sec", real'(count[38]) / real'(cycle_count)
            / real'(TbCyclTime) * real'(1000000000) / 1024 / 1024);
        $display("refill_read:        %f MiB/sec", real'(count[40]) / real'(cycle_count)
            / real'(TbCyclTime) * real'(1000000000) / 1024 / 1024);
        $display("evict_write:        %f MiB/sec", real'(count[42]) / real'(cycle_count)
            / real'(TbCyclTime) * real'(1000000000) / 1024 / 1024);
        $display("evict_read:         %f MiB/sec", real'(count[44]) / real'(cycle_count)
            / real'(TbCyclTime) * real'(1000000000) / 1024 / 1024);
        $display("evict_flush:        %f MiB/sec", real'(count[46]) / real'(cycle_count)
            / real'(TbCyclTime) * real'(1000000000) / 1024 / 1024);
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
endmodule
