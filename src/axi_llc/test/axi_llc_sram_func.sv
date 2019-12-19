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
// File:   axi_sram_llc_func.sv
// Author: Wolfgang Roenninger <wroennin@student.ethz.ch>
// Date:   03.11.2019
//
// Description: Behavioral sram module for the AXI LLC

module axi_llc_sram #(
  parameter int unsigned DATA_WIDTH = 0,   // [bit]
  parameter int unsigned N_WORDS    = 0,
  // Dependent parameters, do not override!
  parameter int unsigned N_BYTES = cf_math_pkg::ceil_div(DATA_WIDTH, 8),
  parameter type addr_t = logic[$clog2(N_WORDS)-1:0],
  parameter type data_t = logic[DATA_WIDTH-1:0],
  parameter type strb_t = logic[N_BYTES-1:0]
) (
  input  logic  clk_i,
  input  logic  rst_ni,
  input  logic  test_i,
  input  logic  req_i,
  input  logic  we_i,
  input  addr_t addr_i,
  input  data_t wdata_i,
  input  strb_t be_i,
  output data_t rdata_o
);

  data_t mem [N_WORDS-1:0];
  addr_t raddr_q;

  always_ff @(posedge clk_i) begin : proc_sram
    if (req_i) begin
      raddr_q <= addr_i;
      if (we_i) begin
        for (int unsigned i = 0; i < N_BYTES; i++) begin
          if (be_i[i]) begin
            mem[addr_i][i*8+:8] <= wdata_i[i*8+:8];
          end
        end
      end
    end
  end

  assign rdata_o = mem[raddr_q];

  initial begin : proc_tell_size
    $display($sformatf("Instantiated axi_llc_sram: N_WORDS: %d addr_t: %d data_t: %d strb_t: %d",
                        N_WORDS, $bits(addr_t), $bits(data_t), $bits(strb_t)));
  end
endmodule
