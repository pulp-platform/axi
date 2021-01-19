// Copyright 2020 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Authors:
// - Wolfgang Roenninger <wroennin@iis.ee.ethz.ch>

`include "axi/typedef.svh"
`include "axi/assign.svh"
`include "common_cells/registers.svh"

/// Testbench for axi_to_mem_banked. Monitors the performance for random accesses.
module tb_axi_to_mem_banked #(
  /// Data Width of the AXI4+ATOP channels.
  parameter int unsigned TbAxiDataWidth = 32'd256,
  /// Number of words of an individual memory bank.
  /// Determines the address width of the request output.
  parameter int unsigned TbNumWords     = 32'd8192,
  /// Number of connected memory banks.
  parameter int unsigned TbNumBanks     = 32'd8,
  /// Data width of an individual memory bank.
  parameter int unsigned TbMemDataWidth = 32'd64,
  /// Latancy in cycles of a memory bank.
  parameter int unsigned TbMemLatency   = 32'd2,
  /// Number of writes performed by the testbench.
  parameter int unsigned TbNumWrites    = 32'd10000,
  /// Number of writes performed by the testbench.
  parameter int unsigned TbNumReads     = 32'd10000
);
  // test bench params
  localparam time CyclTime = 10ns;
  localparam time ApplTime = 2ns;
  localparam time TestTime = 8ns;

  // localparam and typedefs for AXI4+ATOP
  localparam int unsigned AxiIdWidth   = 32'd6;
  localparam int unsigned AxiAddrWidth = 32'd64;
  localparam int unsigned AxiStrbWidth = TbAxiDataWidth / 8;
  localparam int unsigned AxiUserWidth = 32'd4;

  typedef logic [AxiAddrWidth-1:0] axi_addr_t;

  // AXI test defines
  typedef axi_test::axi_rand_master #(
    // AXI interface parameters
    .AW ( AxiAddrWidth ),
    .DW ( TbAxiDataWidth ),
    .IW ( AxiIdWidth   ),
    .UW ( AxiUserWidth ),
    // Stimuli application and test time
    .TA ( ApplTime     ),
    .TT ( TestTime     ),
    // Maximum number of read and write transactions in flight
    .MAX_READ_TXNS        (   20 ),
    .MAX_WRITE_TXNS       (   20 ),
    // Upper and lower bounds on wait cycles on Ax, W, and resp (R and B) channels
    .AX_MIN_WAIT_CYCLES   (    0 ),
    .AX_MAX_WAIT_CYCLES   (    0 ),
    .W_MIN_WAIT_CYCLES    (    0 ),
    .W_MAX_WAIT_CYCLES    (    0 ),
    .RESP_MIN_WAIT_CYCLES (    0 ),
    .RESP_MAX_WAIT_CYCLES (    0 ),
    // AXI feature usage
    .AXI_MAX_BURST_LEN    (    0 ), // maximum number of beats in burst; 0 = AXI max (256)
    .TRAFFIC_SHAPING      (    0 ),
    .AXI_EXCLS            ( 1'b0 ),
    .AXI_ATOPS            ( 1'b0 ),
    .AXI_BURST_FIXED      ( 1'b0 ),
    .AXI_BURST_INCR       ( 1'b1 ),
    .AXI_BURST_WRAP       ( 1'b0 )
  ) axi_rand_master_t;

  // memory defines
  localparam int unsigned MemAddrWidth = $clog2(TbNumWords);

  localparam int unsigned MemBufDepth  = 1;
  // addresses
  localparam axi_addr_t StartAddr = axi_addr_t'(64'h0);
  localparam axi_addr_t EndAddr   = axi_addr_t'(StartAddr + 32'd2 * TbNumWords * TbAxiDataWidth/32'd8);

  typedef logic [MemAddrWidth-1:0]     mem_addr_t;
  typedef logic [5:0]                  mem_atop_t;
  typedef logic [TbMemDataWidth-1:0]   mem_data_t;
  typedef logic [TbMemDataWidth/8-1:0] mem_strb_t;

  // sim signals
  logic end_of_sim;

  // dut signals
  logic clk, rst_n, one_dut_active;

  logic      [1:0]            dut_busy;
  logic      [TbNumBanks-1:0] mem_req;
  logic      [TbNumBanks-1:0] mem_gnt;
  mem_addr_t [TbNumBanks-1:0] mem_addr;
  mem_data_t [TbNumBanks-1:0] mem_wdata;
  mem_strb_t [TbNumBanks-1:0] mem_strb;
  logic      [TbNumBanks-1:0] mem_we;
  mem_atop_t [TbNumBanks-1:0] mem_atop;
  logic      [TbNumBanks-1:0] mem_rvalid;
  mem_data_t [TbNumBanks-1:0] mem_rdata;

  assign one_dut_active = |dut_busy;

  AXI_BUS_DV #(
    .AXI_ADDR_WIDTH ( AxiAddrWidth   ),
    .AXI_DATA_WIDTH ( TbAxiDataWidth ),
    .AXI_ID_WIDTH   ( AxiIdWidth     ),
    .AXI_USER_WIDTH ( AxiUserWidth   )
  ) mem_axi_dv (clk);

  AXI_BUS #(
    .AXI_ADDR_WIDTH ( AxiAddrWidth   ),
    .AXI_DATA_WIDTH ( TbAxiDataWidth ),
    .AXI_ID_WIDTH   ( AxiIdWidth     ),
    .AXI_USER_WIDTH ( AxiUserWidth   )
  ) mem_axi ();
  `AXI_ASSIGN(mem_axi, mem_axi_dv)

  // stimuli generation
  initial begin : proc_axi_master
    static axi_rand_master_t axi_rand_master = new ( mem_axi_dv );
    end_of_sim <= 1'b0;
    axi_rand_master.add_memory_region(StartAddr, EndAddr, axi_pkg::DEVICE_NONBUFFERABLE);
    axi_rand_master.reset();
    @(posedge rst_n);
    @(posedge clk);
    @(posedge clk);

    axi_rand_master.run(TbNumReads, TbNumWrites);
    end_of_sim <= 1'b1;
  end

  // memory banks
  for (genvar i = 0; i < TbNumBanks; i++) begin : gen_tc_sram
    tc_sram #(
      .NumWords    ( TbNumWords   ),
      .DataWidth   ( TbMemDataWidth ),
      .ByteWidth   ( 32'd8        ),
      .NumPorts    ( 32'd1        ),
      .Latency     ( TbMemLatency   ),
      .SimInit     ( "none"       ),
      .PrintSimCfg ( 1'b1         )
    ) i_tc_sram_bank (
      .clk_i   ( clk          ),
      .rst_ni  ( rst_n        ),
      .req_i   ( mem_req[i]   ),
      .we_i    ( mem_we[i]    ),
      .addr_i  ( mem_addr[i]  ),
      .wdata_i ( mem_wdata[i] ),
      .be_i    ( mem_strb[i]  ),
      .rdata_o ( mem_rdata[i] )
    );
    // always be ready
    assign mem_gnt[i] = 1'b1;
    // generate mem_rvalid signal
    if (TbMemLatency == 0) begin : gen_no_mem__lat
      assign mem_rvalid[i] = mem_req[i];
    end else begin : gen_mem_lat
      logic [TbMemLatency-1:0] mem_lat_q, mem_lat_d;
      `FFARN(mem_lat_q, mem_lat_d, '0, clk, rst_n)
      assign mem_lat_d[TbMemLatency-1] = mem_req[i];
      if (TbMemLatency > 1) begin
        for (genvar lat_i = 0; lat_i < TbMemLatency - 1; lat_i++) begin
          assign mem_lat_d[lat_i] = mem_lat_q[lat_i+1];
        end
      end
      assign mem_rvalid[i] = mem_lat_q[0];
    end
  end

  // Clock generator
  clk_rst_gen #(
    .CLK_PERIOD     ( CyclTime ),
    .RST_CLK_CYCLES ( 5        )
  ) i_clk_rst_gen (
    .clk_o  ( clk   ),
    .rst_no ( rst_n )
  );

  // Design under test
  axi_to_mem_banked_intf #(
    .AXI_ID_WIDTH   ( AxiIdWidth   ),
    .AXI_ADDR_WIDTH ( AxiAddrWidth ),
    .AXI_DATA_WIDTH ( TbAxiDataWidth ),
    .AXI_USER_WIDTH ( AxiUserWidth ),
    .MEM_NUM_BANKS  ( TbNumBanks     ),
    .MEM_ADDR_WIDTH ( MemAddrWidth ),
    .MEM_DATA_WIDTH ( TbMemDataWidth ),
    .MEM_LATENCY    ( TbMemLatency   )
  ) i_axi_to_mem_banked_dut (
    .clk_i             ( clk       ),
    .rst_ni            ( rst_n     ),
    .test_i            ( 1'b0      ),
    .axi_to_mem_busy_o ( dut_busy  ),
    .slv               ( mem_axi   ),
    .mem_req_o         ( mem_req   ),
    .mem_gnt_i         ( mem_gnt   ),
    .mem_add_o         ( mem_addr  ), // byte address
    .mem_wdata_o       ( mem_wdata ), // write data
    .mem_be_o          ( mem_strb  ), // byte-wise strobe
    .mem_atop_o        ( mem_atop  ), // atomic operation
    .mem_we_o          ( mem_we    ), // write enable
    .mem_rdata_i       ( mem_rdata )  // read data
  );

  // monitoring
  logic aw_beat, aw_stall, w_beat, b_beat, ar_beat, ar_stall, r_beat;
  assign aw_beat  = mem_axi.aw_valid & mem_axi.aw_ready;
  assign aw_stall = mem_axi.aw_valid & !mem_axi.aw_ready;
  assign  w_beat  = mem_axi.w_valid  & mem_axi.w_ready;
  assign  b_beat  = mem_axi.b_valid  & mem_axi.b_ready;
  assign ar_beat  = mem_axi.ar_valid & mem_axi.ar_ready;
  assign ar_stall = mem_axi.ar_valid & !mem_axi.ar_ready;
  assign  r_beat  = mem_axi.r_valid  & mem_axi.r_ready;

  int unsigned aw_open;
  int unsigned ar_open;

  initial begin : proc_monitor
    automatic bit aw_new = 1;
    automatic bit w_new  = 1;
    automatic bit b_new  = 1;
    automatic bit ar_new = 1;
    automatic bit r_new  = 1;


    automatic longint      wc_cnt     = 0;
    automatic longint      rc_cnt     = 0;
    automatic longint      w_cnt      = 0;
    automatic longint      r_cnt      = 0;

    automatic longint      busy_cnt;
    automatic longint      dut_busy_cnt [TbNumBanks];
    automatic real         bank_busy_percent;
    automatic real         axi_busy_percent;
    automatic real         tmp;

    aw_open           = 0;
    ar_open           = 0;
    bank_busy_percent = 0;
    axi_busy_percent  = 0;
    for (int i = 0; i < TbNumBanks; i++) begin
      dut_busy_cnt[i] = 0;
    end
    $display("###############################################################################");
    $display("Sim Parameter:");
    $display("###############################################################################");
    $display("TbAxiDataWidth: %0d", TbAxiDataWidth);
    $display("TbMemDataWidth: %0d", TbMemDataWidth);
    $display("TbNumBanks:     %0d", TbNumBanks);
    $display("TbMemLatency:   %0d", TbMemLatency);
    $display("###############################################################################");

    @(posedge rst_n);
    forever begin
      @(posedge clk);

      #TestTime;
      // determine the first valid of an AW transaction
      if (mem_axi.aw_valid) begin
        if (aw_new) begin
          aw_open++;
          if (!mem_axi.aw_ready) begin
            aw_new = 0;
          end
        end else begin
          if (mem_axi.aw_ready) begin
            aw_new = 1;
          end
        end
      end

      // determine the first valid of an AR transaction
      if (mem_axi.ar_valid) begin
        if (ar_new) begin
          ar_open++;
          if (!mem_axi.ar_ready) begin
            ar_new = 0;
          end
        end else begin
          if (mem_axi.ar_ready) begin
            ar_new = 1;
          end
        end
      end

      if (b_beat) begin
        aw_open--;
      end
      if (r_beat && mem_axi.r_last) begin
        ar_open--;
      end

      if (aw_open > 0) begin
        wc_cnt++;
      end
      if (ar_open > 0) begin
        rc_cnt++;
      end

      if (w_beat) begin
        w_cnt++;
      end
      if (r_beat) begin
        r_cnt++;
      end

      if ((aw_open > 0) || (ar_open > 0)) begin
        busy_cnt++;
      end

      for (int unsigned i = 0; i < TbNumBanks; i++) begin
        if (mem_req[i]) begin
          dut_busy_cnt[i]++;
        end
      end


      if (end_of_sim) begin
        @(posedge clk);
        $display("###############################################################################");
        $display("Statistics:");
        $display("###############################################################################");
        $display("Writes:");
        $display("Cycles Open write tnx: %0d", wc_cnt);
        $display("Write beat count:      %0d", w_cnt);
        $display("Write utilization:     %0f", real'(w_cnt) / real'(wc_cnt) * 100);
        axi_busy_percent += real'(w_cnt) / real'(wc_cnt) * 100;
                $display("###############################################################################");
        $display("Reads:");
        $display("Cycles Open read tnx:  %0d", rc_cnt);
        $display("Read beat count:       %0d", r_cnt);
        $display("Read utilization:      %0f", real'(r_cnt) / real'(rc_cnt) * 100);
        axi_busy_percent += real'(r_cnt) / real'(rc_cnt) * 100;
        $display("###############################################################################");
        for (int unsigned i = 0; i < TbNumBanks; i++) begin
          bank_busy_percent += real'(dut_busy_cnt[i]) / real'(busy_cnt) * 100;
          $display("Bank %0d utilization: %0f", i, real'(dut_busy_cnt[i]) / real'(busy_cnt) * 100);
          tmp = dut_busy_cnt[i];
          $display("Bank %0d requests: %0f", i, tmp);
          tmp = busy_cnt;
          $display("Bank %0d busy cycles: %0f", i, tmp);
        end
        $display("Sum bank utilization:      %0f", bank_busy_percent);
        $display("Sum axi utilization:       %0f", axi_busy_percent);
        $display("###############################################################################");
        $stop();
      end
    end
  end

  initial begin : proc_sim_progress
    longint unsigned       ActAwTnx;
    longint unsigned       ActArTnx;
    automatic int unsigned PrintInterv = 100;

    ActAwTnx = 0;
    ActArTnx = 0;
    $display("Start Addr: %0h", StartAddr);
    $display("End   addr: %0h", EndAddr);

    @(posedge rst_n);
    forever begin
      @(posedge clk);
      #TestTime;

      if (aw_beat) begin
        if (ActAwTnx % PrintInterv == 0) begin
          $display("%t > AW Transaction %d of %d ", $time(), ActAwTnx, TbNumWrites);
        end
        ActAwTnx++;
      end
      if (ar_beat) begin
        if (ActArTnx % PrintInterv == 0) begin
          $display("%t > AR Transaction %d of %d ", $time(), ActArTnx, TbNumReads);
        end
        ActArTnx++;
      end

      if (end_of_sim) begin
        break;
      end
    end
  end

  AXI_BUS_DV #(
    .AXI_ADDR_WIDTH ( AxiAddrWidth ),
    .AXI_DATA_WIDTH ( TbAxiDataWidth ),
    .AXI_ID_WIDTH   ( AxiIdWidth   ),
    .AXI_USER_WIDTH ( AxiUserWidth )
  ) monitor_dv (clk);

  `AXI_ASSIGN_MONITOR(monitor_dv, mem_axi)

  typedef axi_test::axi_scoreboard #(
    .IW ( AxiIdWidth   ),
    .AW ( AxiAddrWidth ),
    .DW ( TbAxiDataWidth ),
    .UW ( AxiUserWidth ),
    .TT ( TestTime     )
  ) axi_scoreboard_t;
  axi_scoreboard_t axi_scoreboard = new(monitor_dv);
  initial begin : proc_scoreboard
    axi_scoreboard.enable_all_checks();
    @(posedge rst_n);
    axi_scoreboard.monitor();
    wait (end_of_sim);
  end

endmodule
