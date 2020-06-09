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
// File:   llc_pkg.sv
// Author: Wolfgang Roenninger <wroennin@student.ethz.ch>
// Date:   30.04.2019
//
/// Contains the configuration and internal messages structs of the `axi_llc`.
/// Parameter contained in this package are for fine grain configuration of the modules.
/// They can be changed to adapt the cache to a specific design for optimal performance.
package axi_llc_pkg;
  /// AxiCfgStruct to be set externally as part of the [`axi_llc_top`](module.axi_llc_top)
  /// parameter configuration.
  ///
  /// Example configuration:
  ///
  /// localparam axi_llc_pkg::llc_axi_cfg_t AxiLlcAxiCfg = axi_llc_pkg::llc_axi_cfg_t'{
  ///   SlvPortIdWidth:    32'd6,
  ///   AddrWidthFull:     32'd64,
  ///   DataWidthFull:     32'd64,
  ///   LitePortAddrWidth: 32'd32,
  ///   LitePortDataWidth: 32'd32
  /// };
  typedef struct packed {
    /// AXI4+ATOP ID width of the slave port, CPU side, in bits
    int unsigned SlvPortIdWidth;
    /// AXI4+ATOP address width of the ports for accessing the LLC, in bits
    int unsigned AddrWidthFull;
    /// AXI4+ATOP data width of the ports for accessing the LLC, in bits
    int unsigned DataWidthFull;
    /// AXI4+ATOP address width of the config AXI LITE port, in bits
    int unsigned LitePortAddrWidth;
    /// AXI4+ATOP Data width of the config AXI LITE port Has to be 32 bit
    int unsigned LitePortDataWidth;
  } llc_axi_cfg_t;

  /// Cache configuration, used internally as localparam in the LLC submodules.
  /// Automatically set in (module.axi_llc_top).
  typedef struct packed {
    /// Set-associativity of the cache
    int unsigned SetAssociativity;
    /// Number of cache lines per way
    int unsigned NoLines;
    /// Number of blocks (words) in a cache line
    int unsigned NoBlocks;
    /// Size of a block (word) in bit.
    int unsigned BlockSize;
    /// Length of the address tag
    int unsigned TagLength;
    /// Length of the index ( line address )
    int unsigned IndexLength;
    /// Length of the block offset
    int unsigned BlockOffsetLength;
    /// Length of the byte offset
    int unsigned ByteOffsetLength;
    /// SPM address length
    int unsigned SPMLength;
  } llc_cfg_t;

  /// Maximum concurrent AXI transactions on both ports
  parameter int unsigned MaxTrans = 32'd10;

  /// Request Id for refill operations (is constant so that no read interleaving is happening)
  /// Casted/extended to the required ID width in `ax_master`.
  parameter logic [3:0] AxReqId = 4'b1001;

  /// Tag storage request enumeration definition
  typedef enum logic [1:0] {
    /// Run BIST/INIT
    BIST   = 2'b00,
    /// Flush the requested position (output tells if to evict)
    FLUSH  = 2'b01,
    /// Lookup, Performs Hit detection
    LOOKUP = 2'b10,
    /// Store, Writes a tag at the position set with `way_ind_i`
    STORE  = 2'b11
  } tag_req_e;

  // Configuration of the counting bloom filter in `lock_box_bloom` located in `hit_miss`.
  // Change these parameters if you want to optimize the false positive rate.
  /// Number of different hashes used in (`module.lock_box_bloom`).
  parameter int unsigned BloomKHashes     = 32'd3;
  /// Width of the calculated hash function.
  ///
  /// Restriction has to be wider than TODO.
  parameter int unsigned BloomHashWidth   = 32'd6;
  /// Number of hash rounds of the counting bloom filter.
  parameter int unsigned BloomHashRounds  = 32'd1;
  /// Width of the buckets of the counting bloom filter.
  parameter int unsigned BloomBucketWidth = 32'd3;
  parameter cb_filter_pkg::cb_seed_t [BloomKHashes-1:0] BloomSeeds = '{
    cb_filter_pkg::cb_seed_t'{PermuteSeed: 32'd299034753, XorSeed: 32'd4094834  },
    cb_filter_pkg::cb_seed_t'{PermuteSeed: 32'd19921030,  XorSeed: 32'd995713   },
    cb_filter_pkg::cb_seed_t'{PermuteSeed: 32'd294388,    XorSeed: 32'd65146511 }
  };

  /// Number of simultaneous eviction transactions.
  parameter int unsigned EvictFifoDepth   = 32'd4;
  /// Number of descriptors between eviction and refill.
  parameter int unsigned MissBufferDepth  = 32'd2;
  /// Number of simultaneous refill transactions.
  parameter int unsigned RefillFifoDepth  = 32'd4;

  /// Miss counter determine how many descriptors of a given ID can go into the miss pipeline before
  /// the module stalls.
  parameter int unsigned MissCntWidth     = 32'd5;
  /// Writes are counted separately. Writes have to be in order, only one counter.
  parameter int unsigned MissCntMaxWWidth = 32'd7;
  /// This number tells us how many bits of the slave port AXI ID are used for pointing on a counter
  /// * Translates in 2**`UseIdBits` counters inferred.
  /// * Set this parameter to the slave port AXI ID width if you want one counter for each AXI ID.
  parameter int unsigned UseIdBits        = 32'd4;

  /// Width of the performance counters in (module.axi_llc_config)
  parameter int unsigned PerfWidth = 32'd42;

  /// Indicates which unit does an operation onto a cache line data storage element
  typedef enum logic [1:0] {
    /// Eviction Unit
    EvictUnit = 2'b00,
    /// Refill Unit
    RefilUnit = 2'b01,
    /// Write Unit
    WChanUnit = 2'b10,
    /// Read UNit
    RChanUnit = 2'b11
  } cache_unit_e;
endpackage
