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
// File:   axi_llc_top.sv
// Author: Wolfgang Roenninger <wroennin@student.ethz.ch>
// Date:   30.04.2019

/// Contains the top_level of the axi_llc with structs as AXI connections.
/// The standard configuration is a cache size of 512KByte with a set-associativity
/// of 8, and line length of 8 blocks, one block equals the AXI data width of the
/// master port. Each set, also called way, can be configured to be directly
/// accessible as scratch pad memory. This can be done by setting the corresponding
/// register over the AXI LITE port.
///
///              AXI ports: The FULL AXI ports, have different ID widths. The master ports ID is
///                         one bit wider than the slave port. The reason is the `axi_mux` which
///                         controls the AXI bypass.
///

/// # AXI4+ATOP Last Level Cache (LLC)
///
/// This is the top-level module of `axi_llc`.
///
/// ## Overview
///
/// Features:
/// * Write-back last level cache.
/// * Multiple outstanding transactions, priority for cache hits.
/// * Hot configurable scratch-pad memory.
///   * Individual cache sets can be configured to be direct addressable scratch pad while
///     cache is in operation.
///   * Contend of set is flushed back to memory.
/// * Bypass for non-cached memory accesses. (Bypass active when all sets are configured as SPM.)
/// * User configurable cache flush: See [`axi_llc_config`](module.axi_llc_config)
/// * Performance counters: See [`axi_llc_config`](module.axi_llc_config)
///
/// ![Block-diagram he Top Level of the LLC.](axi_llc_top.svg "Block-diagram of the Top Level of the LLC.")
///
  /// The module has three main parameters. They determine the overall size and shape of the LLC.
  /// All are of the type `int unsigned`.
  ///
  /// * `SetAssociativity`: The set-associativity of the LLC. This parameter determines how many ways/sets will be instantiated. The minimum value is 1. The maximum value depends on the data width of the AXI LITE configuration port and should either be 32 or 64 to stay inside the protocol specification. The reason is that the SPM configuration register matches in width the data width of the LITE configuration port.
  /// * `NoLines`: Specifies the number of lines in each way. This value has to be higher than two. The reason is that in the address at least one bit has to be mapped onto a cache-line index. This is a limitation of the *system verilog* language, which requires at least one bit wide fields inside of a struct. Further this value has to be a power of 2. This has to do with the requirement that the address mapping from the address onto the cache-line index has to be continuous.
  /// * `NumBlocks`: Specifies the number of blocks inside a cache line. A block is defined to have the data width of the master port. Currently this also matches the data with of the slave port. The same value limitation as with the *NoLines* parameter applies. Fixing the minimum value to 2 and the overall value to be a power of 2.
  ///
  ///
  /// There exists an additional top level parameter which is compromised of a struct defining the AXI parameters of the different ports. The definition can be found in `axi_llc_pkg`. Following table defines the fields of this struct which are all of type `int unsigned`.
  ///
  ///
  /// | Name        | Function |
  /// |:------------------ |:------------------------------------------------------ |
  /// | `SlvPortIdWidth`    | AXI ID width of the slave port, facing the CPU side. |
  /// | `AddrWidthFull`     | AXI address width of both the slave and master port. |
  /// | `DataWidthFull`     | AXI data width of both the slave and the master port. |
  /// | `LitePortAddrWidth` | AXI address width of the configuration LITE port. |
  /// | `LitePortDataWidth` | AXI data width of the configuration LITE port. Has to be ether 32 or 64 bit to adhere to the AXI4 specification. Further limits the maximum set-associativity of the cache. |
  ///
///
/// It is required to provide the detailed AXI4+ATOP and AXI4-Lite structs as parameters.
/// The structs follow the naming scheme *port*\_*xx*\_chan_t. Where *port* stands for the
/// respective port and have the values *slv*, *mst* and *lite*. In addition the respective request
/// and response structs have to be given. The address rule struct from the
/// `common_cells/addr_decode` has to be specified for the AXI4+ATOP and AXI4-Lite ports as they are
/// used internally to provide address mapping for the AXI transfers onto the different SPM and
/// cache regions.
///
/// The overall size in bytes of the LLC in byte can be calculated with:
///
/// ![Equation axi_llc size](axi_llc_size_equ.gif "Equation axi_llc size")
///
/// ## Operation principle
///
/// The AXI4 protocol issues its transfers in a bursted fashion. The architecture of the LLC uses
/// most of the control information provided by the protocol to implement the cache control in a
/// decentralized way. For this it uses a data-flow driven control scheme.
///
/// The premise is that an AXI transfer gets translated into a number of descriptors which then flow
/// through a pipeline. Each descriptor maps the specific operation onto a cache line and basically
/// translates long bursts onto shorter ones which exactly map onto a single cache line.
/// For example when an AXI4+ATOP burst wants to write on three cache-lines, the control beat gets
/// translated into three descriptors which then flow through the pipeline.
///
/// Example of a write transfer when it accesses the cache:
/// * AW beat is valid on the slave port of the LLC.
/// * AW address gets decoded in the configuration module.
/// * AW enters the split unit and first descriptor enters the spill register.
/// * Request gets issued to the tag-storage (compromised of one SRAM block per set of the cache).
/// * Hit or miss and exact cacheline location (set) is determined. The dirty flag is set.
///   Cache line is locked for other following descriptors. Lock is taken away when descriptor
///   is finished with operation on this cache line.
/// * On hit:
///   * Descriptor goes directly to the write unit, takes hit bypass.
///   * Allows hits to overtake misses, if the AXI ID is different.
/// * On miss:
///   * Descriptor goes to the eviction/refill pipeline.
///   * If the cache-line is dirty it gets evicted by issuing a write request on the AXI4+ATOP
///     master port.
///   * Cache line is refilled from main memory.
///   * Descriptor is transferred into the write unit.
///  * Write unit sends the W beats from the CPU towards the data storage.
///  * Write unit issues a B beat back to the CPU, when the last W beat of the AXI4+ATOP
///    transfer is sent to the LLC data storage.
///
/// Reads are analogous to writes and use the same pipeline.
///
/// The hit bypass allows AXI4+ATOP transaction hitting onto the cache to overtake ones that are in
/// the miss pipeline.
/// Example: This has the advantage that a short write transaction from a CPU can overtake a long
///          read transactions (DMA). The feature requires that the AXI4+ATOP IDs of the transfers
///          are different.
///
/// Following table shows the internal struct which is used to define a
/// [cache descriptor](type llc_desc_t).
/// Part of the descriptor uses directly types defined in `axi_pkg`.
/// The other fields get defined when instantiating the design.
///
/// | Name        | Type               | Function |
/// |:----------- |:------------------ |:----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
/// | `a_x_id`    | `axi_slv_id_t`     | The AXI4+ATOP ID of the burst entering through the slave port of the design. It has the same width as the slave port AXI ID.                                                                                                                                                                                |
/// | `a_x_addr`  | `axi_addr_t`       | The address of the descriptor. Aligned to the corresponding cache block.                                                                                                                                                                                                                                    |
/// | `a_x_len`   | `axi_pkg::len_t`   | AXI4+ATOP burst length field. Corresponds to the number of beats which map onto the cache line accessed by this descriptor. Gets set in the splitting unit which does the mapping onto the cache line.                                                                                                      |
/// | `a_x_size`  | `axi_pkg::size_t`  | AXI4+ATOP size field. This is important for the write and read unit to find the exact block and byte offset. Used for calculating the block location in the data storage.                                                                                                                                   |
/// | `a_x_burst` | `axi_pkg::burst_t` | AXI4+ATOP burst type. This is important for the splitter unit as well as the read and write unit. It determines the descriptor field `a_x_addr`.                                                                                                                                                            |
/// | `a_x_lock`  | `logic`            | AXI4+ATOP lock signal. Passed further in the miss pipeline when the line gets evicted or refilled.                                                                                                                                                                                                          |
/// | `a_x_cache` | `axi_pkg::cache_t` | AXI4+ATOP cache signal. The cache only supports write back mode.                                                                                                                                                                                                                                            |
/// | `a_x_prot`  | `axi_pkg::prot_t`  | AXI4+ATOP protection signal. Passed further in the miss pipeline.                                                                                                                                                                                                                                           |
/// | `x_resp`    | `axi_pkg::resp_t`  | AXI4+ATOP response signal. This tells if we try to make un-allowed accesses onto address regions which are not mapped to either SPM nor cache. When this signal gets set somewhere in the pipeline, all following modules will pass the descriptor along and absorb the corresponding beats from the ports. |
/// | `x_last`    | `logic`            | AXI4+ATOP last flag. Defines if the read or write unit send back the response.                                                                                                                                                                                                                              |
/// | `spm`       | `logic`            | This field signals that the descriptor is of type SPM. It will not make a lookup in the hit/miss detection and utilize the hit bypass if applicable.                                                                                                                                                        |
/// | `rw`        | `logic`            | This field determines if the descriptor makes a write access `1'b1` or read access `1'b0`.                                                                                                                                                                                                                  |
/// | `way_ind`   | `logic`            | The way indicator. Is a vector of width equal of the set-associativity. Decodes the index of the cache set where the descriptor should make an access.                                                                                                                                                      |
/// | `evict`     | `logic`            | The eviction flag. The descriptor missed and the line at the position was determined dirty by the detection. The evict unit will write back the dirty cache-line to the main memory.                                                                                                                        |
/// | `evict_tag` | `logic`            | The eviction tag. As the field `a_x_addr` has the new tag in it, it is used to send back the right address to the main memory during eviction.                                                                                                                                                              |
/// | `refill`    | `logic`            | The refill flag. The descriptor will trigger a read transaction to the main memory, refilling the cache-line.                                                                                                                                                                                               |
/// | `flush`     | `logic`            | The flush flag. This only gets set when a way should be flushed. It gets only set by descriptors coming from the configuration module.                                                                                                                                                                      |
module axi_llc_top #(
  /// The set-associativity of the LLC.
  ///
  /// This parameter determines how many ways/sets will be instantiated.
  ///
  /// Restrictions:
  /// * Minimum value: `32'd1`
  /// * Maximum value: `32'd63`
  /// The maximum value depends on the AXI-Lite register mapping of `axi_llc_config`.
  parameter int unsigned    SetAssociativity   = 32'd8,
  /// Number of cache lines per way.
  ///
  /// Restrictions:
  /// * Minimum value: `32'd2`
  /// * Has to be a power of two.
  ///
  /// Note on restrictions:
  /// The reason is that in the address, at least one bit has to be mapped onto a cache-line index.
  /// This is a limitation of the *system verilog* language, which requires at least one bit wide
  /// fields inside of a struct. Further this value has to be a power of 2. This has to do with the
  /// requirement that the address mapping from the address onto the cache-line index has to be
  /// continuous.
  parameter int unsigned    NoLines            = 32'd1024,
  /// Number of blocks (words) in a cache line.
  ///
  /// The width of a block is the same as the data width of the AXI4+ATOP ports. Defined with
  /// parameter `AxiCfg.DataWidthFull` in bits.
  ///
  /// Restrictions:
  /// * Minimum value: 32'd2
  /// * Has to be a power of two.
  ///
  /// Note on restrictions:
  /// The same restriction as of parameter `NoLines` applies.
  parameter int unsigned    NumBlocks           = 32'd8,
  /// Give the exact AXI parameters in struct form.
  ///
  /// Required struct definition in: `axi_llc_pkg`.
  parameter axi_llc_pkg::llc_axi_cfg_t  AxiCfg = '0,
  /// AW Channel Type slave  port
  parameter type slv_aw_chan_t  = logic,
  /// AW Channel Type master port
  parameter type mst_aw_chan_t  = logic,
  ///  W Channel Type both   ports
  parameter type w_chan_t       = logic,
  ///  B Channel Type slave  port
  parameter type slv_b_chan_t   = logic,
  ///  B Channel Type master port
  parameter type mst_b_chan_t   = logic,
  /// AR Channel Type slave  port
  parameter type slv_ar_chan_t  = logic,
  /// AR Channel Type master port
  parameter type mst_ar_chan_t  = logic,
  ///  R Channel Type slave  port
  parameter type slv_r_chan_t   = logic,
  ///  R Channel Type master port
  parameter type mst_r_chan_t   = logic,
  /// requests  slave  port
  parameter type slv_req_t      = logic,
  /// responses slave  port
  parameter type slv_resp_t     = logic,
  /// requests  master port
  parameter type mst_req_t      = logic,
  /// responses master port
  parameter type mst_resp_t     = logic,
  /// request  lite port
  parameter type lite_req_t     = logic,
  /// response lite port
  parameter type lite_resp_t    = logic,
  /// Full AXI Port address decoding rule
  parameter type rule_full_t    = axi_pkg::xbar_rule_64_t
) (
  /// Rising-edge clock of all ports.
  input  logic                                 clk_i,
  /// Asynchronous reset, active low
  input  logic                                 rst_ni,
  /// Test mode activate, active high, TODO: remove?
  input  logic                                 test_i,
  /// AXI4+ATOP slave port request, CPU side
  input  slv_req_t                             slv_req_i,
  /// AXI4+ATOP slave port response, CPU side
  output slv_resp_t                            slv_resp_o,
  /// AXI4+ATOP master port request, memory side
  output mst_req_t                             mst_req_o,
  /// AXI4+ATOP master port response, memory side
  input  mst_resp_t                            mst_resp_i,
  /// AXI4-Lite slave port request, configuration
  input  lite_req_t                            conf_req_i,
  /// AXI4-Lite slave port response, configuration
  output lite_resp_t                           conf_resp_o,
  /// Start of address region mapped to cache
  input  logic [AxiCfg.AddrWidthFull-1:0]      cached_start_addr_i,
  /// End of address region mapped to cache
  input  logic [AxiCfg.AddrWidthFull-1:0]      cached_end_addr_i,
  /// SPM start address
  ///
  /// The end address is automatically caclulated by the configuration of the LLC.
  /// `spm_end_addr` = `spm_start_addr_i` +
  ///     `SetAssociativity` * `NoLines` * `NumBlocks` * (`AxiCfg.DataWidthFull/8`)
  input  logic [AxiCfg.AddrWidthFull-1:0]      spm_start_addr_i,
  /// Events output, for tracked events see `axi_llc_pkg`.
  ///
  /// Ehen not used, leave open.
  output axi_llc_pkg::events_t                 axi_llc_events_o
);
  typedef logic [ AxiCfg.SlvPortIdWidth  -1:0] axi_slv_id_t;
  typedef logic [ AxiCfg.AddrWidthFull   -1:0] axi_addr_t;
  typedef logic [ AxiCfg.DataWidthFull   -1:0] axi_data_t;
  typedef logic [(AxiCfg.DataWidthFull/8)-1:0] axi_strb_t;

  // configuration struct that has all the cache parameters included for the submodules
  localparam axi_llc_pkg::llc_cfg_t Cfg = axi_llc_pkg::llc_cfg_t'{
    SetAssociativity  : SetAssociativity,
    NoLines           : NoLines,
    NumBlocks         : NumBlocks,
    BlockSize         : AxiCfg.DataWidthFull,
    TagLength         : AxiCfg.AddrWidthFull - $clog2(NoLines) -
                        $clog2(NumBlocks)    - $clog2(AxiCfg.DataWidthFull/8),
    IndexLength       : $clog2(NoLines),
    BlockOffsetLength : $clog2(NumBlocks),
    ByteOffsetLength  : $clog2(AxiCfg.DataWidthFull/8),
    SPMLength         : SetAssociativity * NoLines * NumBlocks * (AxiCfg.DataWidthFull/8)
  };

  // definition of the descriptor struct that gets sent around in the llc
  // (necessary here, because we can not have variable length structs in a package...)
  typedef struct packed {
    // AXI4+ATOP specific descriptor signals
    axi_slv_id_t                      a_x_id;   // AXI ID from slave port
    axi_addr_t                        a_x_addr; // memory address
    axi_pkg::len_t                    a_x_len;  // AXI burst length
    axi_pkg::size_t                   a_x_size; // AXI burst size
    axi_pkg::burst_t                  a_x_burst;// AXI burst type
    logic                             a_x_lock; // AXI lock signal
    axi_pkg::cache_t                  a_x_cache;// AXI cache signal
    axi_pkg::prot_t                   a_x_prot; // AXI protection signal
    axi_pkg::resp_t                   x_resp;   // AXI response signal, for error propagation
    logic                             x_last;   // Last descriptor of a burst
    // Cache specific descriptor signals
    logic                             spm;      // this descriptor targets a SPM region in the cache
    logic                             rw;       // this descriptor is a read:0 or write:1 access
    logic [Cfg.SetAssociativity-1:0]  way_ind;  // way we have to perform an operation on
    logic                             evict;    // evict what is standing in the line
    logic [Cfg.TagLength -1:0]        evict_tag;// tag for evicting a line
    logic                             refill;   // refill the cache line
    logic                             flush;    // flush this line, comes from config
  } llc_desc_t;

  // definition of the structs that are between the units and the ways
  typedef struct packed {
    axi_llc_pkg::cache_unit_e         cache_unit;   // which unit does the access
    logic [Cfg.SetAssociativity -1:0] way_ind;      // to which way the access goes
    logic [Cfg.IndexLength      -1:0] line_addr;    // cache line address
    logic [Cfg.BlockOffsetLength-1:0] blk_offset;   // block offset
    logic                             we;           // write enable
    axi_data_t                        data;         // input data
    axi_strb_t                        strb;         // write enable (equals AXI strb)
  } way_inp_t;

  typedef struct packed {
    axi_llc_pkg::cache_unit_e         cache_unit;   // which unit had the access
    axi_data_t                        data;         // read data from the way
  } way_oup_t;

  // definitions of the miss counting struct
  typedef struct packed {
    axi_slv_id_t                      id;           // AXI id of the count operation
    logic                             rw;           // 0:read, 1:write
    logic                             valid;        // valid, equals enable
  } cnt_t;

  // definition of the lock signals
  typedef struct packed {
    logic [Cfg.IndexLength-1:0]      index;         // index of lock (cache-line)
    logic [Cfg.SetAssociativity-1:0] way_ind;       // way which is locked
  } lock_t;

  // slave requests, that go into the bypass `axi_demux` from the config module
  // `index` for the axi_mux and axi_demux: bypass: 1, llc: 0
  logic slv_aw_bypass, slv_ar_bypass;

  // bypass channels and llc connection to the axi_demux and axi_mux
  slv_req_t     to_demux_req,  bypass_req,   to_llc_req,   from_llc_req;
  slv_resp_t    to_demux_resp, bypass_resp,  to_llc_resp,  from_llc_resp;

  // signals between channel splitters and rw_arb_tree
  llc_desc_t [2:0]      ax_desc;
  logic      [2:0]      ax_desc_valid;
  logic      [2:0]      ax_desc_ready;

  // descriptor from rw_arb_tree to spill register to cut longest path (hit miss detect)
  llc_desc_t            rw_desc;
  logic                 rw_desc_valid,     rw_desc_ready;

  // descriptor from spill register to hit miss detect
  llc_desc_t            spill_desc;
  logic                 spill_valid,       spill_ready;

  // descriptor from the hit_miss_unit
  llc_desc_t            desc;
  logic                 hit_valid,         hit_ready;
  logic                 miss_valid,        miss_ready;

  // descriptor from the evict_unit to the refill_unit
  llc_desc_t            evict_desc;
  logic                 evict_desc_valid,  evict_desc_ready;

  // descriptor from the refill_unit to the merge_unit
  llc_desc_t            refill_desc;
  logic                 refill_desc_valid, refill_desc_ready;

  // descriptor from the merge_unit to the write_unit
  llc_desc_t            write_desc;
  logic                 write_desc_valid,  write_desc_ready;

  // descriptor from the merge_unit to the read_unit
  llc_desc_t            read_desc;
  logic                 read_desc_valid,   read_desc_ready;

  // signals from the unit to the data_ways
  way_inp_t [3:0]       to_way;
  logic     [3:0]       to_way_valid;
  logic     [3:0]       to_way_ready;

  // read signals from the data SRAMs
  way_oup_t             evict_way_out,       read_way_out;
  logic                 evict_way_out_valid, read_way_out_valid;
  logic                 evict_way_out_ready, read_way_out_ready;

  // count down signal from the merge_unit to the hit miss unit
  cnt_t                 cnt_down;

  // unlock signals from the read / write unit towards the hit miss unit
  // req signal depends on gnt signal!
  lock_t                r_unlock,     w_unlock;
  logic                 r_unlock_req, w_unlock_req; // Not AXI valid / ready dependency
  logic                 r_unlock_gnt, w_unlock_gnt; // Not AXI valid / ready dependency

  // global SPM lock signal
  logic [Cfg.SetAssociativity-1:0] spm_lock;
  logic [Cfg.SetAssociativity-1:0] flushed;

  // BIST from tag_store
  logic [Cfg.SetAssociativity-1:0] bist_res;
  logic                            bist_valid;

  // global flush signals
  logic llc_isolate, llc_isolated, aw_unit_busy, ar_unit_busy, flush_recv;

  // define address rules from the address ports, propagate it throughout the design
  rule_full_t cached_addr_rule;
  assign cached_addr_rule = rule_full_t'{
    start_addr: cached_start_addr_i,
    end_addr:   cached_end_addr_i,
    default:    '0
  };
  rule_full_t spm_addr_rule;
  assign spm_addr_rule = rule_full_t'{
    start_addr: spm_start_addr_i,
    end_addr:   spm_start_addr_i + axi_addr_t'(Cfg.SPMLength),
    default:    '0
  };

  // configuration, also has control over bypass logic and flush
  axi_llc_config #(
    .Cfg            ( Cfg              ),
    .AxiCfg         ( AxiCfg           ),
    .desc_t         ( llc_desc_t       ),
    .lite_req_t     ( lite_req_t       ),
    .lite_resp_t    ( lite_resp_t      ),
    .rule_full_t    ( rule_full_t      )
  ) i_llc_config (
    .clk_i             ( clk_i                                  ),
    .rst_ni            ( rst_ni                                 ),
    .conf_req_i        ( conf_req_i                             ),
    .conf_resp_o       ( conf_resp_o                            ),
    .spm_lock_o        ( spm_lock                               ),
    .flushed_o         ( flushed                                ),
    .desc_o            ( ax_desc[axi_llc_pkg::ConfigUnit]       ),
    .desc_valid_o      ( ax_desc_valid[axi_llc_pkg::ConfigUnit] ),
    .desc_ready_i      ( ax_desc_ready[axi_llc_pkg::ConfigUnit] ),
    // AXI address input from slave port for controlling bypass
    .slv_aw_addr_i     ( slv_req_i.aw.addr                      ),
    .slv_ar_addr_i     ( slv_req_i.ar.addr                      ),
    .mst_aw_bypass_o   ( slv_aw_bypass                          ),
    .mst_ar_bypass_o   ( slv_ar_bypass                          ),
    // flush control signals to prevent new data in ax_cutter loading
    .llc_isolate_o     ( llc_isolate                            ),
    .llc_isolated_i    ( llc_isolated                           ),
    .aw_unit_busy_i    ( aw_unit_busy                           ),
    .ar_unit_busy_i    ( ar_unit_busy                           ),
    .flush_desc_recv_i ( flush_recv                             ),
    // BIST input
    .bist_res_i        ( bist_res                               ),
    .bist_valid_i      ( bist_valid                             ),
    // address rules for bypass selection
    .axi_cached_rule_i ( cached_addr_rule                       ),
    .axi_spm_rule_i    ( spm_addr_rule                          )
  );

  // Isolation module before demux to easy flushing,
  // AXI requests get stalled while flush is active
  axi_isolate #(
    .NumPending ( axi_llc_pkg::MaxTrans ),
    .req_t      ( slv_req_t             ),
    .resp_t     ( slv_resp_t            )
  ) i_axi_isolate_flush (
    .clk_i,
    .rst_ni,
    .slv_req_i,  // Slave port request
    .slv_resp_o, // Slave port response
    .mst_req_o  ( to_demux_req  ),
    .mst_resp_i ( to_demux_resp ),
    .isolate_i  ( llc_isolate   ),
    .isolated_o ( llc_isolated  )
  );

  axi_demux #(
    .AxiIdWidth     ( AxiCfg.SlvPortIdWidth  ),
    .aw_chan_t      ( slv_aw_chan_t          ),
    .w_chan_t       ( w_chan_t               ),
    .b_chan_t       ( slv_b_chan_t           ),
    .ar_chan_t      ( slv_ar_chan_t          ),
    .r_chan_t       ( slv_r_chan_t           ),
    .req_t          ( slv_req_t              ),
    .resp_t         ( slv_resp_t             ),
    .NoMstPorts     ( 32'd2                  ),
    .MaxTrans       ( axi_llc_pkg::MaxTrans  ),
    .AxiLookBits    ( axi_llc_pkg::UseIdBits ),
    .FallThrough    ( 1'b0                   ),
    .SpillAw        ( 1'b0                   ),
    .SpillW         ( 1'b0                   ),
    .SpillB         ( 1'b0                   ),
    .SpillAr        ( 1'b0                   ),
    .SpillR         ( 1'b0                   )
  ) i_axi_bypass_demux (
    .clk_i           ( clk_i                    ),
    .rst_ni          ( rst_ni                   ),
    .test_i          ( test_i                   ),
    .slv_req_i       ( to_demux_req             ),
    .slv_aw_select_i ( slv_aw_bypass            ),
    .slv_ar_select_i ( slv_ar_bypass            ),
    .slv_resp_o      ( to_demux_resp            ),
    .mst_reqs_o      ({bypass_req,  to_llc_req }),
    .mst_resps_i     ({bypass_resp, to_llc_resp})
  );

  // AW channel burst splitter
  axi_llc_chan_splitter #(
    .Cfg    ( Cfg           ),
    .AxiCfg ( AxiCfg        ),
    .chan_t ( slv_aw_chan_t ),
    .Write  ( 1'b1          ),
    .desc_t ( llc_desc_t    ),
    .rule_t ( rule_full_t   )
  ) i_aw_splitter    (
    .clk_i           ( clk_i                                  ),
    .rst_ni          ( rst_ni                                 ),
    .ax_chan_slv_i   ( to_llc_req.aw                          ),
    .ax_chan_valid_i ( to_llc_req.aw_valid                    ),
    .ax_chan_ready_o ( to_llc_resp.aw_ready                   ),
    .desc_o          ( ax_desc[axi_llc_pkg::AwChanUnit]       ),
    .desc_valid_o    ( ax_desc_valid[axi_llc_pkg::AwChanUnit] ),
    .desc_ready_i    ( ax_desc_ready[axi_llc_pkg::AwChanUnit] ),
    .unit_busy_o     ( aw_unit_busy                           ),
    .cached_rule_i   ( cached_addr_rule                       ),
    .spm_rule_i      ( spm_addr_rule                          )
  );


  // RW channel burst splitter
  axi_llc_chan_splitter #(
    .Cfg    ( Cfg           ),
    .AxiCfg ( AxiCfg        ),
    .chan_t ( slv_ar_chan_t ),
    .Write  ( 1'b0          ),
    .desc_t ( llc_desc_t    ),
    .rule_t ( rule_full_t   )
  ) i_ar_splitter    (
    .clk_i           ( clk_i                                  ),
    .rst_ni          ( rst_ni                                 ),
    .ax_chan_slv_i   ( to_llc_req.ar                          ),
    .ax_chan_valid_i ( to_llc_req.ar_valid                    ),
    .ax_chan_ready_o ( to_llc_resp.ar_ready                   ),
    .desc_o          ( ax_desc[axi_llc_pkg::ArChanUnit]       ),
    .desc_valid_o    ( ax_desc_valid[axi_llc_pkg::ArChanUnit] ),
    .desc_ready_i    ( ax_desc_ready[axi_llc_pkg::ArChanUnit] ),
    .unit_busy_o     ( ar_unit_busy                           ),
    .cached_rule_i   ( cached_addr_rule                       ),
    .spm_rule_i      ( spm_addr_rule                          )
  );

  // arbitration tree which funnels the flush, read and write descriptors together
  rr_arb_tree #(
    .NumIn    ( 32'd3      ),
    .DataType ( llc_desc_t ),
    .AxiVldRdy( 1'b1       ),
    .LockIn   ( 1'b1       )
  ) i_rw_arb_tree (
    .clk_i  ( clk_i         ),
    .rst_ni ( rst_ni        ),
    .flush_i( '0            ),
    .rr_i   ( '0            ),
    .req_i  ( ax_desc_valid ),
    .gnt_o  ( ax_desc_ready ),
    .data_i ( ax_desc       ),
    .gnt_i  ( rw_desc_ready ),
    .req_o  ( rw_desc_valid ),
    .data_o ( rw_desc       ),
    .idx_o  ()
  );

  spill_register #(
    .T       ( llc_desc_t )
  ) i_rw_spill (
    .clk_i   ( clk_i         ),
    .rst_ni  ( rst_ni        ),
    .valid_i ( rw_desc_valid ),
    .ready_o ( rw_desc_ready ),
    .data_i  ( rw_desc       ),
    .valid_o ( spill_valid   ),
    .ready_i ( spill_ready   ),
    .data_o  ( spill_desc    )
  );

  axi_llc_hit_miss #(
    .Cfg      ( Cfg       ),
    .AxiCfg   ( AxiCfg    ),
    .desc_t   ( llc_desc_t),
    .lock_t   ( lock_t    ),
    .cnt_t    ( cnt_t     )
  ) i_hit_miss_unit (
    .clk_i,
    .rst_ni,
    .test_i,
    .desc_i         ( spill_desc     ),
    .valid_i        ( spill_valid    ),
    .ready_o        ( spill_ready    ),
    .desc_o         ( desc           ),
    .miss_valid_o   ( miss_valid     ),
    .miss_ready_i   ( hit_miss_ready ),
    .hit_valid_o    ( hit_valid      ),
    .hit_ready_i    ( hit_miss_ready ),
    .spm_lock_i     ( spm_lock       ),
    .flushed_i      ( flushed        ),
    .w_unlock_i     ( w_unlock       ),
    .w_unlock_req_i ( w_unlock_req   ),
    .w_unlock_gnt_o ( w_unlock_gnt   ),
    .r_unlock_i     ( r_unlock       ),
    .r_unlock_req_i ( r_unlock_req   ),
    .r_unlock_gnt_o ( r_unlock_gnt   ),
    .cnt_down_i     ( cnt_down       ),
    .bist_res_o     ( bist_res       ),
    .bist_valid_o   ( bist_valid     )
  );

  // This spill register is to ease timing constraints.
  typedef struct packed {
    llc_desc_t desc;
    logic      miss;
  } hit_miss_desc_t;

  hit_miss_desc_t hit_miss_desc, hit_miss_desc_spill;
  // Pack the decision together.
  assign hit_miss_desc = hit_miss_desc_t'{
    llc_desc_t: desc,
    miss:       miss_valid
  };

  // This spill register is to cut the longest path.
  spill_register #(
    .T      ( hit_miss_desc_t             ),
    .Bypass ( !axi_llc_pkg::SpillHitMiss  )
  ) i_spill_register_hit_miss (
    .clk_i,
    .rst_ni,
    .valid_i ( hit_valid | miss_valid ),
    .ready_o ( hit_miss_ready         ),
    .data_i  ( hit_miss_desc          ),
    .valid_o ( hit_miss_spill_valid   ),
    .ready_i ( hit_miss_spill_ready   ),
    .data_o  ( hit_miss_spill_desc    )
  );
  assign hit_miss_spill_ready = hit_miss_spill_desc.miss ? miss_ready : hit_ready;


  axi_llc_evict_unit #(
    .Cfg       ( Cfg           ),
    .AxiCfg    ( AxiCfg        ),
    .desc_t    ( llc_desc_t    ),
    .way_inp_t ( way_inp_t     ),
    .way_oup_t ( way_oup_t     ),
    .aw_chan_t ( slv_aw_chan_t ),
    .w_chan_t  ( w_chan_t      ),
    .b_chan_t  ( slv_b_chan_t  )
  ) i_evict_unit (
    .clk_i             ( clk_i                                           ),
    .rst_ni            ( rst_ni                                          ),
    .test_i            ( test_i                                          ),
    .desc_i            ( hit_miss_spill_desc.desc                        ),
    .desc_valid_i      ( hit_miss_spill_desc.miss & hit_miss_spill_valid ),
    .desc_ready_o      ( miss_ready                                      ),
    .desc_o            ( evict_desc                                      ),
    .desc_valid_o      ( evict_desc_valid                                ),
    .desc_ready_i      ( evict_desc_ready                                ),
    .way_inp_o         ( to_way[axi_llc_pkg::EvictUnit]                  ),
    .way_inp_valid_o   ( to_way_valid[axi_llc_pkg::EvictUnit]            ),
    .way_inp_ready_i   ( to_way_ready[axi_llc_pkg::EvictUnit]            ),
    .way_out_i         ( evict_way_out                                   ),
    .way_out_valid_i   ( evict_way_out_valid                             ),
    .way_out_ready_o   ( evict_way_out_ready                             ),
    .aw_chan_mst_o     ( from_llc_req.aw                                 ),
    .aw_chan_valid_o   ( from_llc_req.aw_valid                           ),
    .aw_chan_ready_i   ( from_llc_resp.aw_ready                          ),
    .w_chan_mst_o      ( from_llc_req.w                                  ),
    .w_chan_valid_o    ( from_llc_req.w_valid                            ),
    .w_chan_ready_i    ( from_llc_resp.w_ready                           ),
    .b_chan_mst_i      ( from_llc_resp.b                                 ),
    .b_chan_valid_i    ( from_llc_resp.b_valid                           ),
    .b_chan_ready_o    ( from_llc_req.b_ready                            ),
    .flush_desc_recv_o ( flush_recv                                      )
  );

  // plug in refill unit for test
  axi_llc_refill_unit #(
    .Cfg       ( Cfg           ),
    .AxiCfg    ( AxiCfg        ),
    .desc_t    ( llc_desc_t    ),
    .way_inp_t ( way_inp_t     ),
    .ar_chan_t ( slv_ar_chan_t ),
    .r_chan_t  ( slv_r_chan_t  )
  ) i_refill_unit (
    .clk_i           ( clk_i                                ),
    .rst_ni          ( rst_ni                               ),
    .test_i          ( test_i                               ),
    .desc_i          ( evict_desc                           ),
    .desc_valid_i    ( evict_desc_valid                     ),
    .desc_ready_o    ( evict_desc_ready                     ),
    .desc_o          ( refill_desc                          ),
    .desc_valid_o    ( refill_desc_valid                    ),
    .desc_ready_i    ( refill_desc_ready                    ),
    .way_inp_o       ( to_way[axi_llc_pkg::RefilUnit]       ),
    .way_inp_valid_o ( to_way_valid[axi_llc_pkg::RefilUnit] ),
    .way_inp_ready_i ( to_way_ready[axi_llc_pkg::RefilUnit] ),
    .ar_chan_mst_o   ( from_llc_req.ar                      ),
    .ar_chan_valid_o ( from_llc_req.ar_valid                ),
    .ar_chan_ready_i ( from_llc_resp.ar_ready               ),
    .r_chan_mst_i    ( from_llc_resp.r                      ),
    .r_chan_valid_i  ( from_llc_resp.r_valid                ),
    .r_chan_ready_o  ( from_llc_req.r_ready                 )
  );

  // merge unit
  axi_llc_merge_unit #(
    .Cfg    ( Cfg        ),
    .desc_t ( llc_desc_t ),
    .cnt_t  ( cnt_t      )
  ) i_merge_unit (
    .clk_i,
    .rst_ni,
    .bypass_desc_i ( hit_miss_spill_desc.desc                         ),
    .bypass_valid_i( ~hit_miss_spill_desc.miss & hit_miss_spill_valid ),
    .bypass_ready_o( hit_ready                                        ),
    .refill_desc_i ( refill_desc                                      ),
    .refill_valid_i( refill_desc_valid                                ),
    .refill_ready_o( refill_desc_ready                                ),
    .read_desc_o   ( read_desc                                        ),
    .read_valid_o  ( read_desc_valid                                  ),
    .read_ready_i  ( read_desc_ready                                  ),
    .write_desc_o  ( write_desc                                       ),
    .write_valid_o ( write_desc_valid                                 ),
    .write_ready_i ( write_desc_ready                                 ),
    .cnt_down_o    ( cnt_down                                         )
  );

  // write unit
  axi_llc_write_unit #(
    .Cfg       ( Cfg          ),
    .AxiCfg    ( AxiCfg       ),
    .desc_t    ( llc_desc_t   ),
    .way_inp_t ( way_inp_t    ),
    .lock_t    ( lock_t       ),
    .w_chan_t  ( w_chan_t     ),
    .b_chan_t  ( slv_b_chan_t )
  ) i_write_unit  (
    .clk_i           ( clk_i                                ),
    .rst_ni          ( rst_ni                               ),
    .test_i          ( test_i                               ),
    .desc_i          ( write_desc                           ),
    .desc_valid_i    ( write_desc_valid                     ),
    .desc_ready_o    ( write_desc_ready                     ),
    .w_chan_slv_i    ( to_llc_req.w                         ),
    .w_chan_valid_i  ( to_llc_req.w_valid                   ),
    .w_chan_ready_o  ( to_llc_resp.w_ready                  ),
    .b_chan_slv_o    ( to_llc_resp.b                        ),
    .b_chan_valid_o  ( to_llc_resp.b_valid                  ),
    .b_chan_ready_i  ( to_llc_req.b_ready                   ),
    .way_inp_o       ( to_way[axi_llc_pkg::WChanUnit]       ),
    .way_inp_valid_o ( to_way_valid[axi_llc_pkg::WChanUnit] ),
    .way_inp_ready_i ( to_way_ready[axi_llc_pkg::WChanUnit] ),
    .w_unlock_o      ( w_unlock                             ),
    .w_unlock_req_o  ( w_unlock_req                         ),
    .w_unlock_gnt_i  ( w_unlock_gnt                         )
  );

  // read unit
  axi_llc_read_unit #(
    .Cfg       ( Cfg          ),
    .AxiCfg    ( AxiCfg       ),
    .desc_t    ( llc_desc_t   ),
    .way_inp_t ( way_inp_t    ),
    .way_oup_t ( way_oup_t    ),
    .lock_t    ( lock_t       ),
    .r_chan_t  ( slv_r_chan_t )
  ) i_read_unit (
    .clk_i           ( clk_i                                ),
    .rst_ni          ( rst_ni                               ),
    .test_i          ( test_i                               ),
    .desc_i          ( read_desc                            ),
    .desc_valid_i    ( read_desc_valid                      ),
    .desc_ready_o    ( read_desc_ready                      ),
    .r_chan_slv_o    ( to_llc_resp.r                        ),
    .r_chan_valid_o  ( to_llc_resp.r_valid                  ),
    .r_chan_ready_i  ( to_llc_req.r_ready                   ),
    .way_inp_o       ( to_way[axi_llc_pkg::RChanUnit]       ),
    .way_inp_valid_o ( to_way_valid[axi_llc_pkg::RChanUnit] ),
    .way_inp_ready_i ( to_way_ready[axi_llc_pkg::RChanUnit] ),
    .way_out_i       ( read_way_out                         ),
    .way_out_valid_i ( read_way_out_valid                   ),
    .way_out_ready_o ( read_way_out_ready                   ),
    .r_unlock_o      ( r_unlock                             ),
    .r_unlock_req_o  ( r_unlock_req                         ),
    .r_unlock_gnt_i  ( r_unlock_gnt                         )
  );

  // data storage
  axi_llc_ways #(
    .Cfg       ( Cfg       ),
    .way_inp_t ( way_inp_t ),
    .way_oup_t ( way_oup_t )
  ) i_llc_ways (
    .clk_i                ( clk_i               ),
    .rst_ni               ( rst_ni              ),
    .test_i               ( test_i              ),
    .way_inp_i            ( to_way              ),
    .way_inp_valid_i      ( to_way_valid        ),
    .way_inp_ready_o      ( to_way_ready        ),
    .evict_way_out_o      ( evict_way_out       ),
    .evict_way_out_valid_o( evict_way_out_valid ),
    .evict_way_out_ready_i( evict_way_out_ready ),
    .read_way_out_o       ( read_way_out        ),
    .read_way_out_valid_o ( read_way_out_valid  ),
    .read_way_out_ready_i ( read_way_out_ready  )
  );

  // this unit widens the AXI ID by one!
  axi_mux #(
    .SlvAxiIDWidth ( AxiCfg.SlvPortIdWidth     ),
    .slv_aw_chan_t ( slv_aw_chan_t             ),
    .mst_aw_chan_t ( mst_aw_chan_t             ),
    .w_chan_t      ( w_chan_t                  ),
    .slv_b_chan_t  ( slv_b_chan_t              ),
    .mst_b_chan_t  ( mst_b_chan_t              ),
    .slv_ar_chan_t ( slv_ar_chan_t             ),
    .mst_ar_chan_t ( mst_ar_chan_t             ),
    .slv_r_chan_t  ( slv_r_chan_t              ),
    .mst_r_chan_t  ( mst_r_chan_t              ),
    .slv_req_t     ( slv_req_t                 ),
    .slv_resp_t    ( slv_resp_t                ),
    .mst_req_t     ( mst_req_t                 ),
    .mst_resp_t    ( mst_resp_t                ),
    .NoSlvPorts    ( 32'd2                     ),
    .MaxWTrans     ( axi_llc_pkg::MaxTrans     ),
    .FallThrough   ( 1'b0                      ), // No registers
    .SpillAw       ( 1'b0                      ), // No registers
    .SpillW        ( 1'b0                      ), // No registers
    .SpillB        ( 1'b0                      ), // No registers
    .SpillAr       ( 1'b0                      ), // No registers
    .SpillR        ( 1'b0                      )  // No registers
  ) i_axi_bypass_mux (
    .clk_i       ( clk_i                      ),
    .rst_ni      ( rst_ni                     ),
    .test_i      ( test_i                     ),
    .slv_reqs_i  ({bypass_req,  from_llc_req }),
    .slv_resps_o ({bypass_resp, from_llc_resp}),
    .mst_req_o   ( mst_req_o                  ),
    .mst_resp_i  ( mst_resp_i                 )
  );

  // Events output track successfull handshakes at different `axi_llc` units.
  // Function definition see `axi_llc_pkg`.
  assign axi_llc_events_o = axi_llc_pkg::events_t'{
    aw_slv_transfer:    axi_llc_pkg::event_num_bytes(
        to_llc_req.aw.len,
        to_llc_req.aw.size,
        to_llc_req.aw_valid,
        to_llc_resp.aw_ready),
    ar_slv_transfer:    axi_llc_pkg::event_num_bytes(
        to_llc_req.ar.len,
        to_llc_req.ar.size,
        to_llc_req.ar_valid,
        to_llc_resp.ar_ready),
    aw_bypass_transfer: axi_llc_pkg::event_num_bytes(
        bypass_req.aw.len,
        bypass_req.aw.size,
        bypass_req.aw_valid,
        bypass_resp.aw_ready),
    ar_bypass_transfer: axi_llc_pkg::event_num_bytes(
        bypass_req.ar.len,
        bypass_req.ar.size,
        bypass_req.ar_valid,
        bypass_resp.ar_ready),
    aw_mst_transfer:    axi_llc_pkg::event_num_bytes(
        from_llc_req.aw.len,
        from_llc_req.aw.size,
        from_llc_req.aw_valid,
        from_llc_resp.aw_ready),
    ar_mst_transfer:    axi_llc_pkg::event_num_bytes(
        from_llc_req.ar.len,
        from_llc_req.ar.size,
        from_llc_req.ar_valid,
        from_llc_resp.ar_ready),
    aw_desc_spm:        axi_llc_pkg::event_num_bytes(
        ax_desc[axi_llc_pkg::AwChanUnit].a_x_len,
        ax_desc[axi_llc_pkg::AwChanUnit].a_x_size,
        ax_desc_valid[axi_llc_pkg::AwChanUnit] & ax_desc[axi_llc_pkg::AwChanUnit].spm,
        ax_desc_ready[axi_llc_pkg::AwChanUnit]),
    ar_desc_spm:        axi_llc_pkg::event_num_bytes(
        ax_desc[axi_llc_pkg::ArChanUnit].a_x_len,
        ax_desc[axi_llc_pkg::ArChanUnit].a_x_size,
        ax_desc_valid[axi_llc_pkg::ArChanUnit] & ax_desc[axi_llc_pkg::ArChanUnit].spm,
        ax_desc_ready[axi_llc_pkg::ArChanUnit]),
    aw_desc_cache:      axi_llc_pkg::event_num_bytes(
        ax_desc[axi_llc_pkg::AwChanUnit].a_x_len,
        ax_desc[axi_llc_pkg::AwChanUnit].a_x_size,
        ax_desc_valid[axi_llc_pkg::AwChanUnit] & ~ax_desc[axi_llc_pkg::AwChanUnit].spm,
        ax_desc_ready[axi_llc_pkg::AwChanUnit]),
    ar_desc_cache:      axi_llc_pkg::event_num_bytes(
        ax_desc[axi_llc_pkg::ArChanUnit].a_x_len,
        ax_desc[axi_llc_pkg::ArChanUnit].a_x_size,
        ax_desc_valid[axi_llc_pkg::ArChanUnit] & ~ax_desc[axi_llc_pkg::ArChanUnit].spm,
        ax_desc_ready[axi_llc_pkg::ArChanUnit]),
    config_desc:        axi_llc_pkg::event_num_bytes(
        ax_desc[axi_llc_pkg::ConfigUnit].a_x_len,
        ax_desc[axi_llc_pkg::ConfigUnit].a_x_size,
        ax_desc_valid[axi_llc_pkg::ConfigUnit],
        ax_desc_ready[axi_llc_pkg::ConfigUnit]),
    hit_write_spm:      axi_llc_pkg::event_num_bytes(
        desc.a_x_len,
        desc.a_x_size,
        hit_valid & desc.rw & desc.spm & ~desc.flush,
        hit_ready),
    hit_read_spm:       axi_llc_pkg::event_num_bytes(
        desc.a_x_len,
        desc.a_x_size,
        hit_valid & ~desc.rw & desc.spm & ~desc.flush,
        hit_ready),
    miss_write_spm:     axi_llc_pkg::event_num_bytes(
        desc.a_x_len,
        desc.a_x_size,
        miss_valid & desc.rw & desc.spm & ~desc.flush,
        miss_ready),
    miss_read_spm:      axi_llc_pkg::event_num_bytes(
        desc.a_x_len,
        desc.a_x_size,
        miss_valid & ~desc.rw & desc.spm & ~desc.flush,
        miss_ready),
    hit_write_cache:    axi_llc_pkg::event_num_bytes(
        desc.a_x_len,
        desc.a_x_size,
        hit_valid & desc.rw & ~desc.spm & ~desc.flush,
        hit_ready),
    hit_read_cache:     axi_llc_pkg::event_num_bytes(
        desc.a_x_len,
        desc.a_x_size,
        hit_valid & ~desc.rw & ~desc.spm & ~desc.flush,
        hit_ready),
    miss_write_cache:   axi_llc_pkg::event_num_bytes(
        desc.a_x_len,
        desc.a_x_size,
        miss_valid & desc.rw & ~desc.spm & ~desc.flush,
        miss_ready),
    miss_read_cache:    axi_llc_pkg::event_num_bytes(
        desc.a_x_len,
        desc.a_x_size,
        miss_valid & ~desc.rw & ~desc.spm & ~desc.flush,
        miss_ready),
    refill_write:       axi_llc_pkg::event_num_bytes(
        evict_desc.a_x_len,
        evict_desc.a_x_size,
        evict_desc_valid & evict_desc.rw & ~evict_desc.spm & ~evict_desc.flush & evict_desc.refill,
        evict_desc_ready),
    refill_read:        axi_llc_pkg::event_num_bytes(
        evict_desc.a_x_len,
        evict_desc.a_x_size,
        evict_desc_valid & ~evict_desc.rw & ~evict_desc.spm & ~evict_desc.flush & evict_desc.refill,
        evict_desc_ready),
    evict_write:        axi_llc_pkg::event_num_bytes(
        desc.a_x_len,
        desc.a_x_size,
        miss_valid & desc.rw & ~desc.spm & ~desc.flush & desc.evict,
        miss_ready),
    evict_read:         axi_llc_pkg::event_num_bytes(
        desc.a_x_len,
        desc.a_x_size,
        miss_valid & ~desc.rw & ~desc.spm & ~desc.flush & desc.evict,
        miss_ready),
    evict_flush:        axi_llc_pkg::event_num_bytes(
        desc.a_x_len,
        desc.a_x_size,
        miss_valid & ~desc.spm & desc.flush & desc.evict,
        miss_ready),
    evict_unit_req:     to_way_valid[axi_llc_pkg::EvictUnit] & to_way_ready[axi_llc_pkg::EvictUnit],
    refill_unit_req:    to_way_valid[axi_llc_pkg::RefilUnit] & to_way_ready[axi_llc_pkg::RefilUnit],
    w_chan_unit_req:    to_way_valid[axi_llc_pkg::WChanUnit] & to_way_ready[axi_llc_pkg::WChanUnit],
    r_chan_unit_req:    to_way_valid[axi_llc_pkg::RChanUnit] & to_way_ready[axi_llc_pkg::RChanUnit],
    default: '0
  };

// pragma translate_off
`ifndef VERILATOR
  initial begin : proc_assert_axi_params
    // check the structs against the Cfg
    slv_aw_id    : assume ($bits(slv_req_i.aw.id) == AxiCfg.SlvPortIdWidth) else
      $fatal(1, $sformatf("llc> AXI Slave port, AW ID width not equal to AxiCfg"));
    slv_aw_addr  : assume ($bits(slv_req_i.aw.addr) == AxiCfg.AddrWidthFull) else
      $fatal(1, $sformatf("llc> AXI Slave port, AW ADDR width not equal to AxiCfg"));
    slv_ar_id    : assume ($bits(slv_req_i.ar.id) == AxiCfg.SlvPortIdWidth) else
      $fatal(1, $sformatf("llc> AXI Slave port, AW ID width not equal to AxiCfg"));
    slv_ar_addr  : assume ($bits(slv_req_i.ar.addr) == AxiCfg.AddrWidthFull) else
      $fatal(1, $sformatf("llc> AXI Slave port, AW ADDR width not equal to AxiCfg"));
    slv_w_data   : assume ($bits(slv_req_i.w.data) == AxiCfg.DataWidthFull) else
      $fatal(1, $sformatf("llc> AXI Slave port, W DATA width not equal to AxiCfg"));
    slv_r_data   : assume ($bits(slv_resp_o.r.data) == AxiCfg.DataWidthFull) else
      $fatal(1, $sformatf("llc> AXI Slave port, R DATA width not equal to AxiCfg"));
    // compare the types against the structs
    slv_req_aw   : assume ($bits(slv_aw_chan_t) == $bits(slv_req_i.aw)) else
      $fatal(1, $sformatf("llc> AXI Slave port, slv_aw_chan_t and slv_req_i.aw not equal"));
    slv_req_w    : assume ($bits(w_chan_t) == $bits(slv_req_i.w)) else
      $fatal(1, $sformatf("llc> AXI Slave port, w_chan_t and slv_req_i.w not equal"));
    slv_req_b    : assume ($bits(slv_b_chan_t) == $bits(slv_resp_o.b)) else
      $fatal(1, $sformatf("llc> AXI Slave port, slv_b_chan_t and slv_resp_o.b not equal"));
    slv_req_ar   : assume ($bits(slv_ar_chan_t) == $bits(slv_req_i.ar)) else
      $fatal(1, $sformatf("llc> AXI Slave port, slv_ar_chan_t and slv_req_i.ar not equal"));
    slv_req_r    : assume ($bits(slv_r_chan_t) == $bits(slv_resp_o.r)) else
      $fatal(1, $sformatf("llc> AXI Slave port, slv_r_chan_t and slv_resp_o.r not equal"));
    // check the structs against the Cfg
    mst_aw_id    : assume ($bits(mst_req_o.aw.id) == AxiCfg.SlvPortIdWidth + 1) else
      $fatal(1, $sformatf("llc> AXI Master port, AW ID not equal to AxiCfg.SlvPortIdWidth + 1"));
    mst_aw_addr  : assume ($bits(mst_req_o.aw.addr) == AxiCfg.AddrWidthFull) else
      $fatal(1, $sformatf("llc> AXI Master port, AW ADDR width not equal to AxiCfg"));
    mst_ar_id    : assume ($bits(mst_req_o.ar.id) == AxiCfg.SlvPortIdWidth + 1) else
      $fatal(1, $sformatf("llc> AXI Master port, AW ID not equal to AxiCfg.SlvPortIdWidth + 1"));
    mst_ar_addr  : assume ($bits(mst_req_o.ar.addr) == AxiCfg.AddrWidthFull) else
      $fatal(1, $sformatf("llc> AXI Master port, AW ADDR width not equal to AxiCfg"));
    mst_w_data   : assume ($bits(mst_req_o.w.data) == AxiCfg.DataWidthFull) else
      $fatal(1, $sformatf("llc> AXI Master port, W DATA width not equal to AxiCfg"));
    mst_r_data   : assume ($bits(mst_resp_i.r.data) == AxiCfg.DataWidthFull) else
      $fatal(1, $sformatf("llc> AXI Master port, R DATA width not equal to AxiCfg"));
    // compare the types against the structs
    mst_req_aw   : assume ($bits(mst_aw_chan_t) == $bits(mst_req_o.aw)) else
      $fatal(1, $sformatf("llc> AXI Master port, mst_aw_chan_t and mst_req_o.aw not equal"));
    mst_req_w    : assume ($bits(w_chan_t) == $bits(mst_req_o.w)) else
      $fatal(1, $sformatf("llc> AXI Master port, w_chan_t and mst_req_o.w not equal"));
    mst_req_b    : assume ($bits(mst_b_chan_t) == $bits(mst_resp_i.b)) else
      $fatal(1, $sformatf("llc> AXI Master port, mst_b_chan_t and mst_resp_i.b not equal"));
    mst_req_ar   : assume ($bits(mst_ar_chan_t) == $bits(mst_req_o.ar)) else
      $fatal(1, $sformatf("llc> AXI Master port, mst_ar_chan_t and mst_req_i.ar not equal"));
    mst_req_r    : assume ($bits(mst_r_chan_t) == $bits(mst_resp_i.r)) else
      $fatal(1, $sformatf("llc> AXI Slave port, slv_r_chan_t and mst_resp_i.r not equal"));
    // check the config lite port against the cfg
    lite_aw_addr : assume ($bits(conf_req_i.aw.addr) == AxiCfg.LitePortAddrWidth ) else
      $fatal(1, $sformatf("llc> Cfg Lite port, AW ADDR width not equal to AxiCfg"));
    lite_ar_addr : assume ($bits(conf_req_i.ar.addr) == AxiCfg.LitePortAddrWidth ) else
      $fatal(1, $sformatf("llc> Cfg Lite port, AR ADDR width not equal to AxiCfg"));
    lite_data    : assume ((AxiCfg.LitePortDataWidth == 32)||(AxiCfg.LitePortDataWidth == 64)) else
      $fatal(1, $sformatf("llc> Axi 4 LITE spec defines a DATA width of 32 or 64 bits!"));
    lite_w_data  : assume ($bits(conf_req_i.w.data) == AxiCfg.LitePortDataWidth) else
      $fatal(1, $sformatf("llc> Cfg Lite port, W DATA width not equal to AxiCfg"));
    lite_r_data  : assume ($bits(conf_resp_o.r.data) == AxiCfg.LitePortDataWidth) else
      $fatal(1, $sformatf("llc> Cfg Lite port, R DATA width not equal to AxiCfg"));
  end
`endif
// pragma translate_on

endmodule
