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

module tb_axi_addr_test;

  typedef logic [16:0] addr_t;

  localparam int unsigned NumAddr = 32'd4;
  localparam addr_t [NumAddr-1:0] TestAddr = '{
    16'h0000,
    16'h0008,
    16'h1000,
    16'h003B
  };
  localparam axi_pkg::len_t [3:0] TestLen = '{
    8'b1,
    8'b11,
    8'b111,
    8'b1111
  };

  initial begin : proc_print_examples
    automatic addr_t           addr;
    automatic axi_pkg::burst_t burst = axi_pkg::BURST_WRAP;
    automatic axi_pkg::len_t   len;
    automatic axi_pkg::size_t  size  = 3'b011;

    $display("Bust Type is BURST_WRAP:");
    for (int unsigned i_addr = 0; i_addr < NumAddr; i_addr++) begin
      addr = TestAddr[i_addr];
      for (int unsigned i_len = 0; i_len < 4; i_len++) begin
        len = TestLen[i_len];
        $display("####################################################################",);
        $display("Wrap Boundary lower:  %h", addr_t'(axi_pkg::wrap_boundary(addr, size, len)));
        $display("Wrap Boundary higher: %h", addr_t'(axi_pkg::wrap_boundary(addr, size, len) + (axi_pkg::num_bytes(size) * (len + 1))));
        for (axi_pkg::len_t i_beat = 0; i_beat <= len; i_beat++) begin

          $display("Burst: %h Addr0: %h Beats: %0d Size: %h i_Beat: %0h Calc Addr: %h",
              burst,
              addr,
              len + 1,
              size,
              i_beat,
              addr_t'(axi_pkg::beat_addr(addr, size, len, burst, i_beat))
          );
        end
      end
    end
  end
endmodule
