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
// Author: Wolfgang Roenninger <wroennin@iis.ee.ethz.ch>
// Date:   02.05.2019

/// This is the AX slave module of `axi_llc`. It accepts AXI4 AX vectors and converts them to
/// LLC descriptors. Each descriptor has all information of the burst considering a single cache
/// line.
module axi_llc_chan_splitter #(
  /// Static configuration parameters of the LLC.
  parameter axi_llc_pkg::llc_cfg_t Cfg = axi_llc_pkg::llc_cfg_t'{default: '0},
  /// Give the exact AXI parameters in struct form. This is passed down from
  /// [`axi_llc_top`](module.axi_llc_top).
  ///
  /// Required struct definition in: `axi_llc_pkg`.
  parameter axi_llc_pkg::llc_axi_cfg_t AxiCfg = axi_llc_pkg::llc_axi_cfg_t'{default: '0},
  /// AXI4 AX channel type. This can either be the AW or AR channel.
  parameter type chan_t = logic,
  /// This defines if the unit is on the AW or the AR channel.
  /// AW: 1
  /// AR: 0
  parameter bit Write = 1'b1,
  /// AXI LLC descriptor type definition.
  parameter type desc_t = logic,
  /// Address rule type definitions for the AXI slave port.
  parameter type rule_t = axi_pkg::xbar_rule_64_t
) (
  /// Clock, positive edge triggered.
  input logic clk_i,
  /// Asynchronous reset, active low.
  input logic rst_ni,
  /// AXI AX slave channel payload.
  input chan_t ax_chan_slv_i,
  /// AXI AX slave channel is valid.
  input logic ax_chan_valid_i,
  /// AXI AX slave channel is ready.
  output logic ax_chan_ready_o,
  /// Generated output descriptor payload.
  output desc_t desc_o,
  /// Descriptor is valid.
  output logic desc_valid_o,
  /// Downstream unit is ready for a descriptor.
  input logic desc_ready_i,
  /// Busy flag of the unit. This signals that an AX vector is actively generating descriptors.
  /// This is used for flushing to prevent flush descriptors interfering with normal operation.
  output logic unit_busy_o,
  /// Cached region address map input.
  /// `start_addr` and `end_addr` are used.
  input rule_t cached_rule_i,
  /// SPM mapping rule input.
  /// This is used in the address decoder for finding out the exact way where the access is
  /// matching.
  /// Only `start_addr` is used.
  input rule_t spm_rule_i
);
  `include "common_cells/registers.svh"
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
    .Cfg    ( Cfg      ),
    .AxiCfg ( AxiCfg   ),
    .chan_t ( chan_t   ),
    .Write  ( Write    ),
    .desc_t ( desc_t   ),
    .rule_t ( rule_t   )
  ) i_burst_cutter (
    .clk_i,
    .rst_ni,
    .curr_chan_i   ( curr_chan     ),
    .next_chan_o   ( next_chan     ),
    .desc_o        ( desc_o        ),
    .cached_rule_i ( cached_rule_i ),
    .spm_rule_i    ( spm_rule_i    )
  );

  // Flip Flops
  `FFLARN(busy_q, busy_d, load_busy, '0, clk_i, rst_ni)
  `FFLARN(chan_q, chan_d, load_chan, '0, clk_i, rst_ni)
endmodule
