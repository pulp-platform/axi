// Copyright (c) 2019 ETH Zurich and University of Bologna.
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
// - Andreas Kurth <akurth@iis.ee.ethz.ch>

// Description: Simple test for showing address wrapping behavior of the function
// `axi_pkg::beat_addr`

`include "axi/assign.svh"
/// Test bench for address generation
module tb_axi_addr_test #(
  /// Number of calculated AX transfers
  int unsigned NumTests = 32'd10000,
  /// Print each calculated address
  bit          PrintDbg = 1'b0
);

  localparam int unsigned IdWidth   = 32'd1;
  localparam int unsigned AddrWidth = 32'd16;
  localparam int unsigned DataWidth = 32'd1024;
  localparam int unsigned UserWidth = 32'd1;

  // Sim print config, how many transactions
  localparam int unsigned PrintTnx  = 1000;
  localparam int unsigned NumReads  = 0;
  localparam int unsigned NumWrites = NumTests;


  typedef logic [AddrWidth:0] addr_t;

  /// The data transferred on a beat on the AW/AR channels.
  class ax_transfer;
    rand addr_t           addr  = '0;
    rand axi_pkg::len_t   len   = '0;
    rand axi_pkg::size_t  size  = '0;
    rand axi_pkg::burst_t burst = '0;
  endclass

  // Random manager no Transactions
  localparam int unsigned NumPendingDut = 16;

  // timing parameters
  localparam time CyclTime = 10ns;
  localparam time ApplTime =  2ns;
  localparam time TestTime =  8ns;

  typedef axi_test::axi_rand_manager #(
    // AXI interface parameters
    .AW ( AddrWidth ),
    .DW ( DataWidth ),
    .IW ( IdWidth   ),
    .UW ( UserWidth ),
    // Stimuli application and test time
    .TA ( ApplTime ),
    .TT ( TestTime ),
    // Enable burst types
    .AXI_BURST_FIXED ( 1'b1 ),
    .AXI_BURST_INCR  ( 1'b1 ),
    .AXI_BURST_WRAP  ( 1'b1 )
  ) axi_rand_manager_t;
  typedef axi_test::axi_rand_subordinate #(
    // AXI interface parameters
    .AW ( AddrWidth ),
    .DW ( DataWidth ),
    .IW ( IdWidth   ),
    .UW ( UserWidth ),
    // Stimuli application and test time
    .TA ( ApplTime ),
    .TT ( TestTime )
  ) axi_rand_subordinate_t;
  // -------------
  // DUT signals
  // -------------
  logic clk;
  logic rst_n;
  logic end_of_sim;

  AXI_BUS_DV #(
    .AXI_ADDR_WIDTH ( AddrWidth ),
    .AXI_DATA_WIDTH ( DataWidth ),
    .AXI_ID_WIDTH   ( IdWidth   ),
    .AXI_USER_WIDTH ( UserWidth )
  ) manager_dv (clk);
  AXI_BUS_DV #(
    .AXI_ADDR_WIDTH ( AddrWidth ),
    .AXI_DATA_WIDTH ( DataWidth ),
    .AXI_ID_WIDTH   ( IdWidth   ),
    .AXI_USER_WIDTH ( UserWidth )
  ) subordinate_dv (clk);

  `AXI_ASSIGN(subordinate_dv, manager_dv)

  //-----------------------------------
  // Clock generator
  //-----------------------------------
  clk_rst_gen #(
    .ClkPeriod   ( CyclTime ),
    .RstClkCycles( 5        )
  ) i_clk_gen (
    .clk_o (clk),
    .rst_no(rst_n)
  );

  initial begin : proc_axi_manager
    automatic axi_rand_manager_t axi_rand_manager = new(manager_dv);
    end_of_sim <= 1'b0;
    axi_rand_manager.add_memory_region(16'h0000, 16'hFFFF, axi_pkg::DEVICE_NONBUFFERABLE);
    axi_rand_manager.add_memory_region(16'h0000, 16'hFFFF, axi_pkg::WTHRU_NOALLOCATE);
    axi_rand_manager.add_memory_region(16'h0000, 16'hFFFF, axi_pkg::WBACK_RWALLOCATE);
    axi_rand_manager.reset();
    @(posedge rst_n);
    axi_rand_manager.run(0, NumTests);
    end_of_sim <= 1'b1;
    repeat (10000) @(posedge clk);
    $stop();
  end

  initial begin : proc_axi_subordinate
    automatic axi_rand_subordinate_t  axi_rand_subordinate  = new(subordinate_dv);
    axi_rand_subordinate.reset();
    @(posedge rst_n);
    axi_rand_subordinate.run();
  end

  initial begin : proc_sim_progress
    automatic int unsigned aw         = 0;
    automatic int unsigned ar         = 0;
    automatic bit          aw_printed = 1'b0;
    automatic bit          ar_printed = 1'b0;

    @(posedge rst_n);

    forever begin
      @(posedge clk);
      #TestTime;
      if (manager_dv.aw_valid && manager_dv.aw_ready) begin
        aw++;
      end
      if (manager_dv.ar_valid && manager_dv.ar_ready) begin
        ar++;
      end

      if ((aw % PrintTnx == 0) && ! aw_printed) begin
        $display("%t> Transmit AW %d of %d.", $time(), aw, NumWrites);
        aw_printed = 1'b1;
      end
      if ((ar % PrintTnx == 0) && !ar_printed) begin
        $display("%t> Transmit AR %d of %d.", $time(), ar, NumReads);
        ar_printed = 1'b1;
      end

      if (aw % PrintTnx == 1) begin
        aw_printed = 1'b0;
      end
      if (ar % PrintTnx == 1) begin
        ar_printed = 1'b0;
      end

      if (end_of_sim) begin
        $info("All transactions completed.");
        break;
      end
    end
  end

  // Test Address queue
  ax_transfer ax_queue[$];
  addr_t      gold_addr[$];

  initial begin : generate_tests
    automatic logic       rand_success;
    automatic ax_transfer ax_beat;

    forever begin
      @(posedge clk);
      #TestTime;
      if (manager_dv.aw_valid && manager_dv.aw_ready) begin
        ax_beat = new;
        ax_beat.addr  = manager_dv.aw_addr;
        ax_beat.len   = manager_dv.aw_len;
        ax_beat.size  = manager_dv.aw_size;
        ax_beat.burst = manager_dv.aw_burst;

        ax_queue.push_back(ax_beat);
      end
    end
  end

  initial begin : proc_test
    automatic ax_transfer ax_beat;
    automatic addr_t      test_addr, exp_addr;
    for (int unsigned i = 0; i < NumTests; i++) begin
      wait (ax_queue.size());
      // get current transfer
      ax_beat = ax_queue.pop_front();
      if (PrintDbg) begin
        print_ax(ax_beat);
      end
      // golden model derived from pseudocode from A-52
      data_transfer(ax_beat.addr, (2**ax_beat.size), (ax_beat.len+1), ax_beat.burst);
      // test the calculated addresses
      for (int unsigned i = 0; i <= ax_beat.len; i++) begin
        test_addr = axi_pkg::beat_addr(ax_beat.addr, ax_beat.size, ax_beat.len, ax_beat.burst, i);
        exp_addr  = gold_addr.pop_front();
        if (PrintDbg) begin
          print_addr(test_addr, i);
        end
        assert (test_addr == exp_addr) else
          begin
            print_ax(ax_beat);
            print_addr(test_addr, i);
            $error("Expected ADDR: %0h was ADDR: %0h", exp_addr, test_addr);
          end
      end
    end
  end

  // golden model derived from pseudocode from A-52
  function automatic void data_transfer(addr_t start_addr, int unsigned num_bytes,
      int unsigned burst_length, axi_pkg::burst_t mode);
    // define boundaries wider than the address, to finf wrapp of addr space
    localparam int unsigned large_addr = $bits(addr_t);
    typedef logic [large_addr:0] laddr_t;

    laddr_t      addr;
    laddr_t      aligned_addr;
    bit          aligned;
    int unsigned dtsize;
    laddr_t      lower_wrap_boundary;
    laddr_t      upper_wrap_boundary;
    assume (mode inside {axi_pkg::BURST_FIXED, axi_pkg::BURST_INCR, axi_pkg::BURST_WRAP});
    addr         = laddr_t'(start_addr);
    aligned_addr = laddr_t'((addr / num_bytes) * num_bytes);
    aligned      = (aligned_addr == addr);
    dtsize       = num_bytes * burst_length;

    if (mode == axi_pkg::BURST_WRAP) begin
      lower_wrap_boundary = laddr_t'((addr / dtsize) * dtsize);
      upper_wrap_boundary = lower_wrap_boundary + dtsize;
    end

    for (int unsigned n = 1; n <= burst_length; n++) begin
      gold_addr.push_back(addr_t'(addr));
      // increment address if necessary
      if (mode != axi_pkg::BURST_FIXED) begin
        if (aligned) begin
          addr += num_bytes;
        end else begin
          addr    = aligned_addr + num_bytes;
          aligned = 1'b1;
        end
        if (mode == axi_pkg::BURST_WRAP && (addr >= upper_wrap_boundary)) begin
          addr = lower_wrap_boundary;
        end
      end
    end
  endfunction : data_transfer

  function automatic void print_ax (ax_transfer ax);
    $display("####################################################################",);
    $display("AX transfer with:");
    case (ax.burst)
      axi_pkg::BURST_FIXED: $display("TYPE: BURST_FIXED");
      axi_pkg::BURST_INCR:  $display("TYPE: BURST_INCR");
      axi_pkg::BURST_WRAP:  $display("TYPE: BURST_WRAP");
      default : $error("TYPE: NOT_DEFINED");
    endcase
    $display("ADDR: %0h", ax.addr);
    $display("SIZE: %0h", ax.size);
    $display("LEN:  %0h", ax.len);
  endfunction : print_ax

  function automatic void print_addr(addr_t addr, int unsigned i_addr);
    $display("i_beat: %0h ADDR: %0h", i_addr, addr);
  endfunction : print_addr

endmodule
