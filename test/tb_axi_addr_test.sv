// Copyright (c) 2019 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Author: Wolfgang Roenninger <wroennin@ethz.ch>

// Description: Simple test for showing address wrapping behavior of the function
// `axi_pkg::beat_addr`

`include "axi/typedef.svh"
/// Test bench for address generation
module tb_axi_addr_test #(
  /// Number of calculated AX transfers
  int unsigned NumTests = 32'd100,
  /// Print each calculated address
  bit          PrintDbg = 1'b0
);

  typedef logic [15:0] addr_t;

  /// The data transferred on a beat on the AW/AR channels.
  class ax_transfer;
    rand addr_t           addr  = '0;
    rand axi_pkg::len_t   len   = '0;
    rand axi_pkg::size_t  size  = '0;
    rand axi_pkg::burst_t burst = '0;
  endclass


  // Test Address queue
  ax_transfer ax_queue[$];
  addr_t      gold_addr[$];

  initial begin : generate_tests
    automatic logic       rand_success;
    automatic ax_transfer ax_beat;

    for (int unsigned i = 0; i < NumTests; i++) begin
      ax_beat = new;
      rand_success = std::randomize(ax_beat) with {
        solve ax_beat.burst before ax_beat.addr, ax_beat.len, ax_beat.size;
        // Randomize one of three burst types
        ax_beat.burst inside {axi_pkg::BURST_FIXED, axi_pkg::BURST_INCR, axi_pkg::BURST_WRAP};
        // Fix lengths if burst type is wrap
        ax_beat.burst == axi_pkg::BURST_WRAP ->
            ax_beat.len inside {axi_pkg::len_t'(1), axi_pkg::len_t'(3),
                                axi_pkg::len_t'(7), axi_pkg::len_t'(15)};
        // Do not cross a 4 KiB boundary with a burst
        //ax_beat.burst == axi_pkg::BURST_INCR ->
        //    ((ax_beat.addr >> 12) << 12) >= ax_beat.addr + 2**ax_beat.size * (ax_beat.len + 1);

      }; assert(rand_success);
      ax_queue.push_back(ax_beat);
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
