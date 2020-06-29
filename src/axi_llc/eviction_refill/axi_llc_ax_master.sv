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
// File:   axi_llc_ax_master.sv
// Author: Wolfgang Roenninger <wroennin@ethz.ch>
// Date:   27.05.2019
//
// This module acts as the AX master for either the eviction or the refill unit.
// When this unit gets a descripor it looks at the corresponding flag. If it is set,
// the AX register gets loaded with the ricght burst. The Sending of the AX vector is
// independednt of the further transmission of the descriptor, however the unit will
// wait with loading the next descriptor as long as the AX is not sent.
//
// `cache_unit = axi_llc_pkg::EvictUnit`:
//        The unit is configured for eviction and has to be connected to the AW master channel.
//        It looks, if the evict flag is set in the descriptor.
// `cache_unit = axi_llc_pkg::REFILUnit`:
//        The unit is configures for refill and has to be connected to the AR master channel.
//        It looks, if the refill flag is set in the descriptor.

// register macros
`include "common_cells/registers.svh"

module axi_llc_ax_master #(
  parameter axi_llc_pkg::llc_cfg_t     Cfg        = -1,
  parameter axi_llc_pkg::llc_axi_cfg_t AxiCfg     = -1,
  parameter type                       desc_t     = logic,
  parameter type                       ax_chan_t  = logic,
  parameter axi_llc_pkg::cache_unit_e  cache_unit = axi_llc_pkg::EvictUnit
) (
  input  logic     clk_i,  // Clock
  input  logic     rst_ni, // Asynchronous reset active low
  // descriptor input
  input  desc_t    desc_i,
  input  logic     desc_valid_i,
  output logic     desc_ready_o,
  // descriptor output
  output desc_t    desc_o,
  output logic     desc_valid_o,
  input  logic     desc_ready_i,
  // Axi AR master channel
  output ax_chan_t ax_chan_mst_o,
  output logic     ax_chan_valid_o,
  input  logic     ax_chan_ready_i
);
  // The master port ID is one bit wider than the slave port one, see `axi_mux`
  typedef logic [AxiCfg.SlvPortIdWidth:0]  id_mst_t;
  typedef logic [AxiCfg.AddrWidthFull-1:0] addr_t;

  // register for holding the descriptor and ax vector
  desc_t    desc_d,       desc_q;
  logic     desc_valid_d, desc_valid_q;
  logic     load_desc,    load_desc_valid;

  ax_chan_t chan_d,       chan_q;
  logic     chan_valid_d, chan_valid_q;
  logic     load_chan,    load_chan_valid;

  logic  desc_flag;  // is either the refill, or the eviction flag depending on cache_unit
  // control signals
  addr_t evict_addr, refill_addr;

  // descriptor and channel output assignment
  assign desc_o          = desc_q;
  assign desc_valid_o    = desc_valid_q;
  assign ax_chan_mst_o   = chan_q;
  assign ax_chan_valid_o = chan_valid_q;

  // descriptor ready signal
  assign desc_ready_o = ~desc_valid_q & ~chan_valid_q;

  // assignment of the addresses, either refill or eviction, calculate address index for request
  localparam int AddrOffset = Cfg.BlockOffsetLength + Cfg.ByteOffsetLength;
  assign evict_addr  =
      {desc_i.evict_tag, desc_i.a_x_addr[AddrOffset+:Cfg.IndexLength], {AddrOffset{1'b0}}};
  assign refill_addr =
      {desc_i.a_x_addr[AddrOffset+:(Cfg.TagLength + Cfg.IndexLength)], {AddrOffset{1'b0}}};

  always_comb begin : proc_desc_control
    // default assignments
    desc_d          = desc_q;
    desc_valid_d    = desc_valid_q;
    load_desc       = 1'b0;
    load_desc_valid = 1'b0;
    // when the desc is valid, send it along
    if (desc_valid_q) begin
      // change state, if the descriptor leaves the module
      if (desc_ready_i) begin
        desc_valid_d    = 1'b0;
        load_desc_valid = 1'b1;
      end
    end else begin
      // here load a new descriptor, if it is ready -> chan is also not busy
      if (desc_valid_i && desc_ready_o) begin
        desc_d          = desc_i;
        load_desc       = 1'b1;
        desc_valid_d    = 1'b1;
        load_desc_valid = 1'b1;
      end
    end
  end

  // determine the flag if the unit has to send an ax vector with the next descriptor
  assign desc_flag = (cache_unit == axi_llc_pkg::EvictUnit) ? desc_i.evict : desc_i.refill;

  always_comb begin : proc_chan_control
    // default assignments
    chan_d          = '0;
    load_chan       = 1'b0;
    chan_valid_d    = chan_valid_q;
    load_chan_valid = 1'b0;
    // assign the right channel values to the flip flop
    chan_d.id    = id_mst_t'(axi_llc_pkg::AxReqId);
    if (cache_unit == axi_llc_pkg::EvictUnit) begin
      chan_d.addr = evict_addr;
    end else begin
      chan_d.addr = refill_addr;
    end
    chan_d.len    = Cfg.NumBlocks - 1;         // This unit always makes request for the whole line
    chan_d.size   = $clog2(Cfg.BlockSize / 8); // and all blocks
    chan_d.burst  = axi_pkg::BURST_INCR;
    chan_d.lock   = desc_i.a_x_lock;
    chan_d.cache  = desc_i.a_x_cache;
    chan_d.prot   = desc_i.a_x_prot;
    // send the vector over the channel
    if (chan_valid_q) begin
      // transaction happens, go back to free
      if (ax_chan_ready_i) begin
        chan_valid_d    = 1'b0;
        load_chan_valid = 1'b1;
      end
    end else begin
      // only enable the channel if the flag is set
      if (desc_valid_i && desc_ready_o && desc_flag) begin
        load_chan       = 1'b1;
        chan_valid_d    = 1'b1;
        load_chan_valid = 1'b1;
      end
    end
  end

  // Flip Flops
  `FFLARN(desc_q,       desc_d,       load_desc,       '0, clk_i, rst_ni)
  `FFLARN(desc_valid_q, desc_valid_d, load_desc_valid, '0, clk_i, rst_ni)
  `FFLARN(chan_q,       chan_d,       load_chan,       '0, clk_i, rst_ni)
  `FFLARN(chan_valid_q, chan_valid_d, load_chan_valid, '0, clk_i, rst_ni)

  // these assumptions check if the module has valid parameters
  // pragma translate_off
  `ifndef VERILATOR
  `ifndef VCS
  `ifndef SYNTHESIS
  initial begin : proc_check_params
    unit_check: assume ((cache_unit == axi_llc_pkg::EvictUnit) ||
                        (cache_unit == axi_llc_pkg::RefilUnit)) else
      $fatal(1, "Wrong cache_unit parameter.");
  end
  `endif
  `endif
  `endif
  // pragma translate_on
endmodule
