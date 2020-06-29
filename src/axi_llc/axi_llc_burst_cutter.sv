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
// File:   axi_llc_burst_cutter.sv
// Author: Wolfgang Roenninger <wroennin@iis.ee.ethz.ch>
// Date:   02.05.2019


/// This module takes as input an Axi4 AW or AR channel struct
/// It computes the current descriptor for the LLC, which maps part of the burst
/// onto a cache line
/// It computes the remaining channel struct, all remaining parts of the burst
/// which map onto other cache lines
/// This module further caclulates the exact data way where an spm access will go to.
module axi_llc_burst_cutter #(
  /// LLC configuration struct, with static parameters.
  parameter axi_llc_pkg::llc_cfg_t     Cfg    = axi_llc_pkg::llc_cfg_t'{default: '0},
  /// AXI channel configuration struct.
  parameter axi_llc_pkg::llc_axi_cfg_t AxiCfg = axi_llc_pkg::llc_axi_cfg_t'{default: '0},
  /// AXI AW or AR channel struct definition.
  parameter type                       chan_t = logic,
  /// The type of channel, how the write bit in the descriptor should be set.
  /// `0`: AR channel is connected, descriptors do read accesses.
  /// `1`: AW channel is connected, descriptors do write accesses.
  parameter bit                        Write  = 1'b0,
  /// LLC descriptor type defeintion.
  parameter type                       desc_t = logic,
  /// Type of the address rule struct used for SPM access streeri
  parameter type                       rule_t = axi_pkg::xbar_rule_64_t
) (
  /// Clock, positive edge triggered.
 	input  logic  clk_i,
  /// Asynchronous reset, active low.
 	input  logic  rst_ni,
  /// The current AW or AR channel. This is the whole AXI transaction.
  /// It is split into a descriptor and a next channel, which is a smaller transfer if it accesses
  /// another cache line.
  input  chan_t curr_chan_i,
  /// The Ax transaction where the part accessed on the current cache line has been removed.
  output chan_t next_chan_o,
  /// Output descriptor for the current line.
  output desc_t desc_o,
  /// Address rule for mapping the cached address region.
  /// `start_addr` and `end_addr` are used.
  input  rule_t cached_rule_i,
  /// Address rule for mapping the SPM mapped region.
  /// Here only the `satrt_addr` field is used. Internal builds an address decoding map
  /// one for each cache way.
  input  rule_t spm_rule_i
  );

  // typedefs for casting
  typedef logic [AxiCfg.AddrWidthFull-1:0] addr_t; // address type
  typedef logic [Cfg.SetAssociativity-1:0] indi_t; // way indicator type

  // line offset is the index where we are interested in, or where the line index starts
  localparam int unsigned LineOffset = Cfg.ByteOffsetLength + Cfg.BlockOffsetLength;

  addr_t         this_line_address; // address of this line (tag included)
  addr_t         next_line_address; // address of the next line (tag included)
  addr_t         bytes_on_line;     // how many bytes are on this cache line
  axi_pkg::len_t beats_on_line;     // how many beats are on this cache line
  // addr decode signals
  logic          rule_valid;
  logic [$clog2(Cfg.SetAssociativity+32'd1)-1:0] rule_index; // so that width matches decoder port

  // generate the addr map for the decoder, ram has rule 0 and each way has one for its spm region
  rule_t [Cfg.SetAssociativity:0] addr_map;
  always_comb begin : proc_assign_addr_map
    addr_t tmp_addr;                  // this counts up for the spm regions, one for each way
    tmp_addr = spm_rule_i.start_addr; // init tmp_addr
    addr_map = '0;
    // assign the ram range
    addr_map[0].start_addr = cached_rule_i.start_addr;
    addr_map[0].end_addr   = cached_rule_i.end_addr;
    // assign the spm regions
    for (int unsigned i = 1; i <= Cfg.SetAssociativity; i++) begin
      addr_map[i].idx = i;
      addr_map[i].start_addr   = tmp_addr;
      addr_map[i].end_addr     = tmp_addr + (Cfg.BlockSize / 8) * Cfg.NoBlocks * Cfg.NoLines;
      tmp_addr                 = tmp_addr + (Cfg.BlockSize / 8) * Cfg.NoBlocks * Cfg.NoLines;
    end
  end

  always_comb begin : proc_cutter
    // Make sure the outputs are defined to a default.
    next_chan_o         = curr_chan_i;
    desc_o              = desc_t'{
      a_x_id:    curr_chan_i.id,
      a_x_addr:  curr_chan_i.addr,
      a_x_size:  curr_chan_i.size,
      a_x_burst: curr_chan_i.burst,
      a_x_lock:  curr_chan_i.lock,
      a_x_prot:  curr_chan_i.prot,
      a_x_cache: curr_chan_i.cache,
      x_resp:    axi_pkg::RESP_OKAY,
      rw:        Write,
      default: '0
    };

    // calculate the line address (tag included)
    this_line_address   = addr_t'(curr_chan_i.addr[LineOffset+:(AxiCfg.AddrWidthFull-LineOffset)]
                             << LineOffset);
    // calculate the next line address (tag included)
    next_line_address   = this_line_address + (addr_t'(1) << LineOffset);
    // how many bytes are on the line from curr addr to the end
    bytes_on_line       = next_line_address - curr_chan_i.addr;
    // how many transaction beats map onto the current line
    beats_on_line       = axi_pkg::len_t'((bytes_on_line - 1) >> curr_chan_i.size) + 1;

    // Are we making an SPM access?
    if (rule_valid) begin
      if (rule_index != '0) begin
        desc_o.spm     = 1'b1;
        desc_o.way_ind = indi_t'(1 << (rule_index - 1));
      end
    end else begin
      // make it an spm access on decerror go always onto way 0
      desc_o.spm     = 1'b1;
      desc_o.way_ind = indi_t'(1 << 0);
      desc_o.x_resp  = axi_pkg::RESP_SLVERR;
    end

    // Do we have beats left on the next line?
    if(((beats_on_line - 1) < curr_chan_i.len) &&
        !(curr_chan_i.burst == axi_pkg::BURST_FIXED)) begin
      // in this case we have at least one beat on the next cache line.
      next_chan_o.addr  = next_line_address;
      next_chan_o.len   = curr_chan_i.len - beats_on_line;
      desc_o.a_x_len    = beats_on_line - 1;
      desc_o.x_last     = 1'b0;
    end else begin // all remaining beats are on the current cacheline.
      next_chan_o.addr  = addr_t'(0);
      next_chan_o.len   = axi_pkg::len_t'(0);
      desc_o.a_x_len    = curr_chan_i.len;
      desc_o.x_last     = 1'b1;
    end
  end

  addr_decode #(
    .NoIndices ( Cfg.SetAssociativity + 32'd1 ),
    .NoRules   ( Cfg.SetAssociativity + 32'd1 ),
    .addr_t    ( addr_t                       ),
    .rule_t    ( rule_t                       )
  ) i_burst_cutter_decode (
    .addr_i           ( curr_chan_i.addr ),
    .addr_map_i       ( addr_map         ),
    .idx_o            ( rule_index       ),
    .dec_valid_o      ( rule_valid       ),
    .dec_error_o      ( /*not used*/     ), // implicit used in rule_valid
    .en_default_idx_i ( 1'b0             ),
    .default_idx_i    ( '0               )
  );

  // pragma translate_off
  `ifndef VERILATOR
  `ifndef VCS
  `ifndef SYNTHESIS
  address_rollover: assert property( @(posedge clk_i) disable iff (~rst_ni)
                        (next_line_address > this_line_address)) else
    $fatal(1, $sformatf("burst_cutter > We habe an Global Address rollover in burst_cutter.\n \
                         this_line_address: %s\nnext_line_address: %s",
                         this_line_address, next_line_address));
  line_address: assert property( @(posedge clk_i) disable iff (~rst_ni)
                        ((next_line_address >= curr_chan_i.addr))) else
    $fatal(1, $sformatf("burst_cutter > nWe habe an problem with the current burst address and \
                         the next line address.\nthis_line_address: %s\ncurr_addr_i: %s",
                         this_line_address, curr_chan_i.addr));
  `endif
  `endif
  `endif
  // pragma translate_on
endmodule
