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
// Description: Contains the configuration and internal messages structs of the LLC.
//              Parameter contained in this package are for fine grain configuration of the module.
//              They can be changed to adapt the cache to a specific design for optimal performance.
//

package axi_llc_pkg;
  // AxiCfgStruct to be set externally as part of the `axi_llc_top` parameter configuration
  typedef struct packed {
    int unsigned SlvPortIdWidth;    // AXI ID width of the slave port, CPU side
    int unsigned AddrWidthFull;     // Address width of the full AXI 4 ports
    int unsigned DataWidthFull;     // Data width of the full AXI 4 ports
    int unsigned LitePortAddrWidth; // Addr width of the config AXI LITE port
    int unsigned LitePortDataWidth; // Data width of the config AXI LITE port Has to be 32 bit
  } llc_axi_cfg_t;

  // Cache configuration, used internally in the LLC
  typedef struct packed {
    int unsigned SetAssociativity;               // Set Associativity of the cache
    int unsigned NoLines;                        // Number of cache lines per way
    int unsigned NoBlocks;                       // Number of Blocks (Words) in a cache line
    int unsigned BlockSize;                      // Size of a Block (Word) in bit.
    int unsigned TagLength;                      // Length of the Address Tag
    int unsigned IndexLength;                    // Length of the Index ( Line Address )
    int unsigned BlockOffsetLength;              // Length of the Block Offset
    int unsigned ByteOffsetLength;               // Length of the Byte Offset
    int unsigned SPMLength;                      // SPM Address Length
  } llc_cfg_t;

  // config definitions
  // number of cfg registers of length llc_axi::DataWidthLite
  localparam int unsigned nbCfgRegs        = 4;
  // Config reg definition , move to llc config?
  typedef struct packed {
    logic [32-1:0] bist_out; // read only
    logic [32-1:0] flushed;  // read only
    logic [32-1:0] flush;    // read and write
    logic [32-1:0] spm_cfg;  // read and write
  } llc_cfg_reg_t;

  // Maximum concurrent AXI transactions on both ports
  localparam int unsigned MaxTrans = 32'd10;

  // Request Id for refill operations (is constant so that no read interleaving is happening)
  // Cast to rigth Id width happens in `ax_master`.
  localparam logic [3:0] AxReqId = 4'b1001;

  // Tag storage request mode
  typedef enum logic [1:0] {
    BIST,   // 0 Run BIST/INIT
    FLUSH,  // 1 Flush the requested position (output tells if to evict)
    LOOKUP, // 2 Lookup, Performs Hit detection
    STORE   // 3 Store, Writes a tag at the position set with way_ind_i
  } tag_req_e;

  // Configuration of the counting bloom filter in `lock_box_bloom` located in `hit_miss`.
  // Change these parameters if you want to optimize the false positive rate.
  localparam int unsigned BloomKHashes     = 3;
  localparam int unsigned BloomHashWidth   = 6;
  localparam int unsigned BloomHashRounds  = 1;
  localparam int unsigned BloomBucketWidth = 3;
  localparam cb_filter_pkg::cb_seed_t [BloomKHashes-1:0] BloomSeeds = '{
    '{PermuteSeed: 32'd299034753, XorSeed: 32'd4094834  },
    '{PermuteSeed: 32'd19921030,  XorSeed: 32'd995713   },
    '{PermuteSeed: 32'd294388,    XorSeed: 32'd65146511 }
  };

  // The FIFO depths in the miss pipeline of the LLC, determines the number of simultanous
  // in flight cache line eviction or refill requests on the master port of the cache
  localparam int unsigned EvictFifoDepth   = 4; // Number of simultanous evictions
  localparam int unsigned MissBufferDepth  = 2; // Number of descriptors between eviction and refill
  localparam int unsigned RefillFifoDepth  = 4; // Number of simultanous refills

  // The Width of the counters to prevent reordering
  // This number determines how many descriptors of a given ID can go into the miss pipeline before
  localparam int unsigned MissCntWidth     = 5; // normal counters
  localparam int unsigned MissCntMaxWWidth = 7; // write counter
  // This number tells us how many bits of the slave port AXI ID are used for pointing on a counter
  // translates in 2**`UseIdBits` counters innferred
  // set this parameter to the slave port AXI ID width if you want one counter for each AXI ID
  localparam int unsigned UseIdBits        = 4;

  // Width of the performance counters
  localparam int unsigned PerfWidth = 32'd42;

  // this enum is for indicating a way which unit does an operation onto a cache line
  typedef enum logic [1:0] {
    EvictUnit = 2'b00, // 0
    RefilUnit = 2'b01, // 1
    WChanUnit = 2'b10, // 2
    RChanUnit = 2'b11  // 3
  } cache_unit_e;
endpackage
