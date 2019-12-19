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
// File:   chan_splitter.sv
// Author: Wolfgang Roenninger <wroennin@student.ethz.ch>
// Date:   02.05.2019
//
// Description: Takes an axi4 AW vector and converts it to one or multiple
//              Chache line descriptors.

// register macros
`include "common_cells/registers.svh"

module axi_llc_chan_splitter #(
  parameter axi_llc_pkg::llc_cfg_t     Cfg    = -1,    // static LLC configuration
  parameter axi_llc_pkg::llc_axi_cfg_t AxiCfg = -1,    // AXI configuration
  parameter type                       chan_t = logic, // AW or AR channel type
  parameter bit                        Write  = 1'b1,  // Write:1 Read:0
  parameter type                       desc_t = logic, // cache descriptor (def in `axi_llc_top`)
  parameter type                       rule_t = axi_pkg::xbar_rule_64_t
) (
  input clk_i,                   // Clock
  input rst_ni,                  // Asynchronous reset active low
  // AXI AW channel Slave Port (from CPU side)
  input  chan_t ax_chan_slv_i,
  input  logic  ax_chan_valid_i,
  output logic  ax_chan_ready_o,
  // chache line descriptor
  output desc_t desc_o,
  output logic  desc_valid_o,
  input  logic  desc_ready_i,
  // output busy status, for flushing
  output logic  unit_busy_o,
  // addr map input,
  input  rule_t ram_rule_i,      // only `start_addr`, `end_addr` get used
  input  rule_t spm_rule_i       // only `start_addr` gets used
);
  // Registers
  chan_t chan_d,    chan_q;      // to store channel information
  logic  busy_d,    busy_q;      // to store if spitter is ready for next descriptor or not
  logic  load_chan, load_busy;   // register enable

  chan_t curr_chan;
  chan_t next_chan;

  always_comb begin : proc_control_cut
    // default assignments
    curr_chan       = ax_chan_slv_i;
    chan_d          = chan_q;
    load_chan       = 1'b0;
    busy_d          = busy_q;
    load_busy       = 1'b0;
    // handshakes
    ax_chan_ready_o = 1'b0;
    desc_valid_o    = 1'b0;
    // status flag
    unit_busy_o     = 1'b0;

    // control
    if (busy_q) begin
      unit_busy_o  = 1'b1;
      curr_chan    = chan_q;
      desc_valid_o = 1'b1;
      // handshake downstream
      if (desc_ready_i) begin
        // do something different, if it is the last descriptor or not
        // it is the last descriptor
        if (desc_o.x_last) begin
          ax_chan_ready_o = 1'b1;
          // handshake new ax vector
          if (ax_chan_valid_i) begin
            chan_d    = ax_chan_slv_i;
            load_chan = 1'b1;
          // no new vector, go not busy
          end else begin
            busy_d    = 1'b0;
            load_busy = 1'b1;
          end
        // not the last one, save the next chan
        end else begin
          chan_d = next_chan;
          load_chan = 1'b1;
        end
      end

    // we are ready to take in a new vector, if we do not get stalled of flushing
    end else begin
      ax_chan_ready_o = 1'b1;
      // handshake the new vector
      if (ax_chan_valid_i) begin
        unit_busy_o  = 1'b1;
        desc_valid_o = 1'b1;
        // what happens, if the descriptor handshakes out
        // downstream is ready
        if (desc_ready_i) begin
          // if it is not the last descriptor, save the next_chan and get busy
          if (!desc_o.x_last) begin
            chan_d    = next_chan;
            load_chan = 1'b1;
            busy_d    = 1'b1;
            load_busy = 1'b1;
          end
        // downstream not ready, save vector in register and get busy
        end else begin
          chan_d    = ax_chan_slv_i;
          load_chan = 1'b1;
          busy_d    = 1'b1;
          load_busy = 1'b1;
        end
      end
    end
  end

  // this module determines how many data beats of the AX request map onto a cache line
  axi_llc_burst_cutter #(
    .Cfg        ( Cfg      ),
    .AxiCfg     ( AxiCfg   ),
    .chan_t     ( chan_t   ),
    .Write      ( Write    ),
    .desc_t     ( desc_t   ),
    .rule_t     ( rule_t   )
  ) i_burst_cutter (
    .clk_i      ( clk_i       ),
    .rst_ni     ( rst_ni      ),
    .curr_chan_i( curr_chan   ),
    .next_chan_o( next_chan   ),
    .desc_o     ( desc_o      ),
    .ram_rule_i ( ram_rule_i  ),
    .spm_rule_i ( spm_rule_i  )
  );

  // Flip Flops
  `FFLARN(busy_q, busy_d, load_busy, '0, clk_i, rst_ni)
  `FFLARN(chan_q, chan_d, load_chan, '0, clk_i, rst_ni)
endmodule
