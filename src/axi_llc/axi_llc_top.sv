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
//
// Description: Contains the top_level of the axi_llc with structs as AXI connections.
//              The standard configuration is a cache size of 512KByte with a set-associativity
//              of 8, and line length of 8 blocks, one block equals the AXI data width of the
//              master port. Each set, also called way, can be configured to be directly
//              accessible as scratch pad memory. This can be done by setting the corresponding
//              register over the AXI LITE port.
//
//              AXI ports: The FULL AXI ports, have different ID widths. The master ports ID is
//                         one bit wider than the slave port. The reason is the `axi_mux` which
//                         controls the AXI bypass.
//

module axi_llc_top #(
  parameter int unsigned    SetAssociativity   = 8,    // set associativity of the cache
  parameter int unsigned    NoLines            = 1024, // number of cache lines per Way
  parameter int unsigned    NoBlocks           = 8,    // number of Blocks (Words) in a cache line
  // Give the exact AXI parameters, definition in `axi_llc_pkg`
  parameter axi_llc_pkg::llc_axi_cfg_t  AxiCfg = '0,
  // AXI channel types
  parameter type slv_aw_chan_t  = logic, // AW Channel Type slave  port
  parameter type mst_aw_chan_t  = logic, // AW Channel Type master port
  parameter type w_chan_t       = logic, //  W Channel Type both   ports
  parameter type slv_b_chan_t   = logic, //  B Channel Type slave  port
  parameter type mst_b_chan_t   = logic, //  B Channel Type master port
  parameter type slv_ar_chan_t  = logic, // AR Channel Type slave  port
  parameter type mst_ar_chan_t  = logic, // AR Channel Type master port
  parameter type slv_r_chan_t   = logic, //  R Channel Type slave  port
  parameter type mst_r_chan_t   = logic, //  R Channel Type master port
  parameter type slv_req_t      = logic, // requests  slave  port
  parameter type slv_resp_t     = logic, // responses slave  port
  parameter type mst_req_t      = logic, // requests  master port
  parameter type mst_resp_t     = logic, // responses master port
  parameter type lite_aw_chan_t = logic, // AXI Lite AW channel
  parameter type lite_w_chan_t  = logic, // AXI Lite W channel
  parameter type lite_b_chan_t  = logic, // AXI Lite B channel
  parameter type lite_ar_chan_t = logic, // AXI Lite AR channel
  parameter type lite_r_chan_t  = logic, // AXI Lite R channel
  parameter type lite_req_t     = logic, // request  lite port
  parameter type lite_resp_t    = logic, // response lite port
  parameter type rule_full_t    = axi_pkg::xbar_rule_64_t, // Full AXI Port address decoding rule
  parameter type rule_lite_t    = axi_pkg::xbar_rule_64_t  // LITE AXI Port address decoding rule
) (
  input  logic                                 clk_i,  // Clock
  input  logic                                 rst_ni, // Asynchronous reset active low
  input  logic                                 test_i, // Test mode activate
  // Slave Bus Port from CPU side
  input  slv_req_t                             slv_req_i,
  output slv_resp_t                            slv_resp_o,
  // Master Bus Port to Memory
  output mst_req_t                             mst_req_o,
  input  mst_resp_t                            mst_resp_i,
  // LITE Slave Bus Port from CPU side (Config)
  input  lite_req_t                            conf_req_i,
  output lite_resp_t                           conf_resp_o,
  // Address Map the rest gets calculated internally
  input  logic [AxiCfg.AddrWidthFull-1:0]      ram_start_addr_i,
  input  logic [AxiCfg.AddrWidthFull-1:0]      ram_end_addr_i,
  input  logic [AxiCfg.AddrWidthFull-1:0]      spm_start_addr_i,
  input  logic [AxiCfg.LitePortAddrWidth-1:0]  cfg_start_addr_i
);
  typedef logic [ AxiCfg.SlvPortIdWidth  -1:0] axi_slv_id_t;
  typedef logic [ AxiCfg.AddrWidthFull   -1:0] axi_addr_t;
  typedef logic [ AxiCfg.DataWidthFull   -1:0] axi_data_t;
  typedef logic [(AxiCfg.DataWidthFull/8)-1:0] axi_strb_t;


  // configuration struct that has all the cache parameters included for the submodules
  localparam axi_llc_pkg::llc_cfg_t Cfg = '{
    SetAssociativity  : SetAssociativity,
    NoLines           : NoLines,
    NoBlocks          : NoBlocks,
    BlockSize         : AxiCfg.DataWidthFull,
    TagLength         : AxiCfg.AddrWidthFull - $clog2(NoLines) -
                        $clog2(NoBlocks)     - $clog2(AxiCfg.DataWidthFull/8),
    IndexLength       : $clog2(NoLines),
    BlockOffsetLength : $clog2(NoBlocks),
    ByteOffsetLength  : $clog2(AxiCfg.DataWidthFull/8),
    SPMLength         : SetAssociativity * NoLines * NoBlocks * (AxiCfg.DataWidthFull/8)
  };

  // definition of the descriptor struct that gets sent around in the llc
  // (necessary here, because we can not have variable length structs in a package...)
  typedef struct packed {
    // Axi4 specific descriptor signals
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

  // slave requests, that go into the bypass `axi_demux`
  slv_aw_chan_t slv_aw;
  logic         slv_aw_valid, slv_aw_ready, slv_aw_bypass;
  slv_ar_chan_t slv_ar;
  logic         slv_ar_valid, slv_ar_ready, slv_ar_bypass;

  // bypass channels
  // `index` for the axi_mux and axi_demux: bypass: 1, llc: 0
  slv_aw_chan_t bypass_aw;
  logic         bypass_aw_valid, bypass_aw_ready;
  w_chan_t      bypass_w;
  logic         bypass_w_valid,  bypass_w_ready;
  slv_b_chan_t  bypass_b;
  logic         bypass_b_valid,  bypass_b_ready;
  slv_ar_chan_t bypass_ar;
  logic         bypass_ar_valid, bypass_ar_ready;
  slv_r_chan_t  bypass_r;
  logic         bypass_r_valid,  bypass_r_ready;
  // llc channels, master and slave
  slv_aw_chan_t to_llc_aw,                        from_llc_aw;
  logic         to_llc_aw_valid, to_llc_aw_ready, from_llc_aw_valid, from_llc_aw_ready;
  w_chan_t      to_llc_w,                         from_llc_w;
  logic         to_llc_w_valid,  to_llc_w_ready,  from_llc_w_valid,  from_llc_w_ready;
  slv_b_chan_t  to_llc_b,                         from_llc_b;
  logic         to_llc_b_valid,  to_llc_b_ready,  from_llc_b_valid,  from_llc_b_ready;
  slv_ar_chan_t to_llc_ar,                        from_llc_ar;
  logic         to_llc_ar_valid, to_llc_ar_ready, from_llc_ar_valid, from_llc_ar_ready;
  slv_r_chan_t  to_llc_r,                         from_llc_r;
  logic         to_llc_r_valid,  to_llc_r_ready,  from_llc_r_valid,  from_llc_r_ready;

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
  way_inp_t[3:0]        to_way;
  logic    [3:0]        to_way_valid;
  logic    [3:0]        to_way_ready;

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
  logic aw_unit_busy, ar_unit_busy, flush_recv;


  // define address rules from the address ports, propagate it throughout the design
  rule_full_t ram_addr_rule;
  assign ram_addr_rule = '{
    start_addr: ram_start_addr_i,
    end_addr:   ram_end_addr_i,
    default:    '0
  };
  rule_full_t spm_addr_rule;
  assign spm_addr_rule = '{
    start_addr: spm_start_addr_i,
    end_addr:   spm_start_addr_i + axi_addr_t'(Cfg.SPMLength),
    default:    '0
  };

  // configuration, also has control over bypass logic, AW and AR channels from the
  // slave port pass through here, W, B and R channel directly go to the bypass `axi_demux`
  axi_llc_config #(
    .Cfg            ( Cfg              ),
    .AxiCfg         ( AxiCfg           ),
    .desc_t         ( llc_desc_t       ),
    .aw_chan_t      ( slv_aw_chan_t    ),
    .ar_chan_t      ( slv_ar_chan_t    ),
    .lite_aw_chan_t ( lite_aw_chan_t   ),
    .lite_w_chan_t  ( lite_w_chan_t    ),
    .lite_b_chan_t  ( lite_b_chan_t    ),
    .lite_ar_chan_t ( lite_ar_chan_t   ),
    .lite_r_chan_t  ( lite_r_chan_t    ),
    .lite_req_t     ( lite_req_t       ),
    .lite_resp_t    ( lite_resp_t      ),
    .rule_full_t    ( rule_full_t      ),
    .rule_lite_t    ( rule_lite_t      )
  ) i_llc_config (
    .clk_i          ( clk_i            ),
    .rst_ni         ( rst_ni           ),
    .conf_req_i     ( conf_req_i       ),
    .conf_resp_o    ( conf_resp_o      ),
    .spm_lock_o     ( spm_lock         ),
    .flushed_o      ( flushed          ),
    .desc_o         ( ax_desc[2]       ),
    .desc_valid_o   ( ax_desc_valid[2] ),
    .desc_ready_i   ( ax_desc_ready[2] ),
    // slave port for controlling bypass (only AW and AR, rest gets handled per assign outside)
    .slv_aw_chan_i  ( slv_req_i.aw        ),
    .slv_aw_valid_i ( slv_req_i.aw_valid  ),
    .slv_aw_ready_o ( slv_resp_o.aw_ready ),
    .slv_ar_chan_i  ( slv_req_i.ar        ),
    .slv_ar_valid_i ( slv_req_i.ar_valid  ),
    .slv_ar_ready_o ( slv_resp_o.ar_ready ),
    // master port for bypass control
    .mst_aw_chan_o     ( slv_aw            ),
    .mst_aw_bypass_o   ( slv_aw_bypass     ),
    .mst_aw_valid_o    ( slv_aw_valid      ),
    .mst_aw_ready_i    ( slv_aw_ready      ),
    .mst_ar_chan_o     ( slv_ar            ),
    .mst_ar_bypass_o   ( slv_ar_bypass     ),
    .mst_ar_valid_o    ( slv_ar_valid      ),
    .mst_ar_ready_i    ( slv_ar_ready      ),
    // flush control signals to prevent new data in ax_cutter loading
    .aw_unit_busy_i    ( aw_unit_busy     ),
    .ar_unit_busy_i    ( ar_unit_busy     ),
    .flush_desc_recv_i ( flush_recv       ),
    // performance register inputs
    .hit_valid_i       ( hit_valid        ),
    .hit_ready_i       ( hit_ready        ),
    .miss_valid_i      ( miss_valid       ),
    .miss_ready_i      ( miss_ready       ),
    .evict_flag_i      ( desc.evict       ),
    .refil_flag_i      ( desc.refill      ),
    .flush_flag_i      ( desc.flush       ),
    // BIST input
    .bist_res_i        ( bist_res         ),
    .bist_valid_i      ( bist_valid       ),
    // address rules for bypass selection
    .axi_ram_rule_i    ( ram_addr_rule    ),
    .axi_spm_rule_i    ( spm_addr_rule    ),
    .cfg_start_addr_i  ( cfg_start_addr_i )
  );

  // only the AW and AR channel go through the CFG module
  // AXI demux for bypassing the cache
  axi_demux #(
    .AxiIdWidth     ( AxiCfg.SlvPortIdWidth  ),
    .aw_chan_t      ( slv_aw_chan_t          ),
    .w_chan_t       ( w_chan_t               ),
    .b_chan_t       ( slv_b_chan_t           ),
    .ar_chan_t      ( slv_ar_chan_t          ),
    .r_chan_t       ( slv_r_chan_t           ),
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
    .clk_i            ( clk_i              ),
    .rst_ni           ( rst_ni             ),
    .test_i           ( test_i             ),
    .slv_aw_chan_i    ( slv_aw             ),
    .slv_aw_select_i  ( slv_aw_bypass      ),
    .slv_aw_valid_i   ( slv_aw_valid       ),
    .slv_aw_ready_o   ( slv_aw_ready       ),
    .slv_w_chan_i     ( slv_req_i.w        ),
    .slv_w_valid_i    ( slv_req_i.w_valid  ),
    .slv_w_ready_o    ( slv_resp_o.w_ready ),
    .slv_b_chan_o     ( slv_resp_o.b       ),
    .slv_b_valid_o    ( slv_resp_o.b_valid ),
    .slv_b_ready_i    ( slv_req_i.b_ready  ),
    .slv_ar_chan_i    ( slv_ar             ),
    .slv_ar_select_i  ( slv_ar_bypass      ),
    .slv_ar_valid_i   ( slv_ar_valid       ),
    .slv_ar_ready_o   ( slv_ar_ready       ),
    .slv_r_chan_o     ( slv_resp_o.r       ),
    .slv_r_valid_o    ( slv_resp_o.r_valid ),
    .slv_r_ready_i    ( slv_req_i.r_ready  ),

    .mst_aw_chans_o   ({ bypass_aw,       to_llc_aw       }),
    .mst_aw_valids_o  ({ bypass_aw_valid, to_llc_aw_valid }),
    .mst_aw_readies_i ({ bypass_aw_ready, to_llc_aw_ready }),
    .mst_w_chans_o    ({ bypass_w,        to_llc_w        }),
    .mst_w_valids_o   ({ bypass_w_valid,  to_llc_w_valid  }),
    .mst_w_readies_i  ({ bypass_w_ready,  to_llc_w_ready  }),
    .mst_b_chans_i    ({ bypass_b,        to_llc_b        }),
    .mst_b_valids_i   ({ bypass_b_valid,  to_llc_b_valid  }),
    .mst_b_readies_o  ({ bypass_b_ready,  to_llc_b_ready  }),
    .mst_ar_chans_o   ({ bypass_ar,       to_llc_ar       }),
    .mst_ar_valids_o  ({ bypass_ar_valid, to_llc_ar_valid }),
    .mst_ar_readies_i ({ bypass_ar_ready, to_llc_ar_ready }),
    .mst_r_chans_i    ({ bypass_r,        to_llc_r        }),
    .mst_r_valids_i   ({ bypass_r_valid,  to_llc_r_valid  }),
    .mst_r_readies_o  ({ bypass_r_ready,  to_llc_r_ready  })
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
    .clk_i           ( clk_i            ),
    .rst_ni          ( rst_ni           ),
    .ax_chan_slv_i   ( to_llc_aw        ),
    .ax_chan_valid_i ( to_llc_aw_valid  ),
    .ax_chan_ready_o ( to_llc_aw_ready  ),
    .desc_o          ( ax_desc[1]       ),
    .desc_valid_o    ( ax_desc_valid[1] ),
    .desc_ready_i    ( ax_desc_ready[1] ),
    .unit_busy_o     ( aw_unit_busy     ),
    .ram_rule_i      ( ram_addr_rule    ),
    .spm_rule_i      ( spm_addr_rule    )
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
    .clk_i           ( clk_i            ),
    .rst_ni          ( rst_ni           ),
    .ax_chan_slv_i   ( to_llc_ar        ),
    .ax_chan_valid_i ( to_llc_ar_valid  ),
    .ax_chan_ready_o ( to_llc_ar_ready  ),
    .desc_o          ( ax_desc[0]       ),
    .desc_valid_o    ( ax_desc_valid[0] ),
    .desc_ready_i    ( ax_desc_ready[0] ),
    .unit_busy_o     ( ar_unit_busy     ),
    .ram_rule_i      ( ram_addr_rule    ),
    .spm_rule_i      ( spm_addr_rule    )
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
    .clk_i          ( clk_i        ),
    .rst_ni         ( rst_ni       ),
    .test_i         ( test_i       ),
    .desc_i         ( spill_desc   ),
    .valid_i        ( spill_valid  ),
    .ready_o        ( spill_ready  ),
    .desc_o         ( desc         ),
    .miss_valid_o   ( miss_valid   ),
    .miss_ready_i   ( miss_ready   ),
    .hit_valid_o    ( hit_valid    ),
    .hit_ready_i    ( hit_ready    ),
    .spm_lock_i     ( spm_lock     ),
    .flushed_i      ( flushed      ),
    .w_unlock_i     ( w_unlock     ),
    .w_unlock_req_i ( w_unlock_req ),
    .w_unlock_gnt_o ( w_unlock_gnt ),
    .r_unlock_i     ( r_unlock     ),
    .r_unlock_req_i ( r_unlock_req ),
    .r_unlock_gnt_o ( r_unlock_gnt ),
    .cnt_down_i     ( cnt_down     ),
    .bist_res_o     ( bist_res     ),
    .bist_valid_o   ( bist_valid   )
  );

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
    .clk_i             ( clk_i                                 ),
    .rst_ni            ( rst_ni                                ),
    .test_i            ( test_i                                ),
    .desc_i            ( desc                                  ),
    .desc_valid_i      ( miss_valid                            ),
    .desc_ready_o      ( miss_ready                            ),
    .desc_o            ( evict_desc                            ),
    .desc_valid_o      ( evict_desc_valid                      ),
    .desc_ready_i      ( evict_desc_ready                      ),
    .way_inp_o         ( to_way       [axi_llc_pkg::EvictUnit] ),
    .way_inp_valid_o   ( to_way_valid [axi_llc_pkg::EvictUnit] ),
    .way_inp_ready_i   ( to_way_ready [axi_llc_pkg::EvictUnit] ),
    .way_out_i         ( evict_way_out                         ),
    .way_out_valid_i   ( evict_way_out_valid                   ),
    .way_out_ready_o   ( evict_way_out_ready                   ),
    .aw_chan_mst_o     ( from_llc_aw                           ),
    .aw_chan_valid_o   ( from_llc_aw_valid                     ),
    .aw_chan_ready_i   ( from_llc_aw_ready                     ),
    .w_chan_mst_o      ( from_llc_w                            ),
    .w_chan_valid_o    ( from_llc_w_valid                      ),
    .w_chan_ready_i    ( from_llc_w_ready                      ),
    .b_chan_mst_i      ( from_llc_b                            ),
    .b_chan_valid_i    ( from_llc_b_valid                      ),
    .b_chan_ready_o    ( from_llc_b_ready                      ),
    .flush_desc_recv_o ( flush_recv                            )
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
    .clk_i           ( clk_i                                  ),
    .rst_ni          ( rst_ni                                 ),
    .test_i          ( test_i                                 ),
    .desc_i          ( evict_desc                             ),
    .desc_valid_i    ( evict_desc_valid                       ),
    .desc_ready_o    ( evict_desc_ready                       ),
    .desc_o          ( refill_desc                            ),
    .desc_valid_o    ( refill_desc_valid                      ),
    .desc_ready_i    ( refill_desc_ready                      ),
    .way_inp_o       ( to_way       [axi_llc_pkg::RefilUnit]  ),
    .way_inp_valid_o ( to_way_valid [axi_llc_pkg::RefilUnit]  ),
    .way_inp_ready_i ( to_way_ready [axi_llc_pkg::RefilUnit]  ),
    .ar_chan_mst_o   ( from_llc_ar                            ),
    .ar_chan_valid_o ( from_llc_ar_valid                      ),
    .ar_chan_ready_i ( from_llc_ar_ready                      ),
    .r_chan_mst_i    ( from_llc_r                             ),
    .r_chan_valid_i  ( from_llc_r_valid                       ),
    .r_chan_ready_o  ( from_llc_r_ready                       )
  );

  // merge unit
  axi_llc_merge_unit #(
    .Cfg    ( Cfg        ),
    .desc_t ( llc_desc_t ),
    .cnt_t  ( cnt_t      )
  ) i_merge_unit (
    .clk_i         (clk_i),
    .rst_ni        (rst_ni),
    .bypass_desc_i ( desc              ),
    .bypass_valid_i( hit_valid         ),
    .bypass_ready_o( hit_ready         ),
    .refill_desc_i ( refill_desc       ),
    .refill_valid_i( refill_desc_valid ),
    .refill_ready_o( refill_desc_ready ),
    .read_desc_o   ( read_desc         ),
    .read_valid_o  ( read_desc_valid   ),
    .read_ready_i  ( read_desc_ready   ),
    .write_desc_o  ( write_desc        ),
    .write_valid_o ( write_desc_valid  ),
    .write_ready_i ( write_desc_ready  ),
    .cnt_down_o    ( cnt_down          )
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
    .clk_i           ( clk_i                                 ),
    .rst_ni          ( rst_ni                                ),
    .test_i          ( test_i                                ),
    .desc_i          ( write_desc                            ),
    .desc_valid_i    ( write_desc_valid                      ),
    .desc_ready_o    ( write_desc_ready                      ),
    .w_chan_slv_i    ( to_llc_w                              ),
    .w_chan_valid_i  ( to_llc_w_valid                        ),
    .w_chan_ready_o  ( to_llc_w_ready                        ),
    .b_chan_slv_o    ( to_llc_b                              ),
    .b_chan_valid_o  ( to_llc_b_valid                        ),
    .b_chan_ready_i  ( to_llc_b_ready                        ),
    .way_inp_o       ( to_way       [axi_llc_pkg::WChanUnit] ),
    .way_inp_valid_o ( to_way_valid [axi_llc_pkg::WChanUnit] ),
    .way_inp_ready_i ( to_way_ready [axi_llc_pkg::WChanUnit] ),
    .w_unlock_o      ( w_unlock                              ),
    .w_unlock_req_o  ( w_unlock_req                          ),
    .w_unlock_gnt_i  ( w_unlock_gnt                          )
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
    .r_chan_slv_o    ( to_llc_r                             ),
    .r_chan_valid_o  ( to_llc_r_valid                       ),
    .r_chan_ready_i  ( to_llc_r_ready                       ),
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
    .MstAxiIDWidth ( AxiCfg.SlvPortIdWidth + 1 ), // fixed as there are two inputs only
    .slv_aw_chan_t ( slv_aw_chan_t             ),
    .mst_aw_chan_t ( mst_aw_chan_t             ),
    .w_chan_t      ( w_chan_t                  ),
    .slv_b_chan_t  ( slv_b_chan_t              ),
    .mst_b_chan_t  ( mst_b_chan_t              ),
    .slv_ar_chan_t ( slv_ar_chan_t             ),
    .mst_ar_chan_t ( mst_ar_chan_t             ),
    .slv_r_chan_t  ( slv_r_chan_t              ),
    .mst_r_chan_t  ( mst_r_chan_t              ),
    .NoSlvPorts    ( 32'd2                     ),
    .MaxWTrans     ( axi_llc_pkg::MaxTrans     ),
    .FallThrough   ( 1'b0                      ), // No registers
    .SpillAw       ( 1'b0                      ), // No registers
    .SpillW        ( 1'b0                      ), // No registers
    .SpillB        ( 1'b0                      ), // No registers
    .SpillAr       ( 1'b0                      ), // No registers
    .SpillR        ( 1'b0                      )  // No registers
  ) i_axi_bypass_mux (
    .clk_i           ( clk_i                                ),
    .rst_ni          ( rst_ni                               ),
    .test_i          ( test_i                               ),
    .slv_aw_chans_i  ({ bypass_aw,       from_llc_aw       }),
    .slv_aw_valids_i ({ bypass_aw_valid, from_llc_aw_valid }),
    .slv_aw_readies_o({ bypass_aw_ready, from_llc_aw_ready }),
    .slv_w_chans_i   ({ bypass_w,        from_llc_w        }),
    .slv_w_valids_i  ({ bypass_w_valid,  from_llc_w_valid  }),
    .slv_w_readies_o ({ bypass_w_ready,  from_llc_w_ready  }),
    .slv_b_chans_o   ({ bypass_b,        from_llc_b        }),
    .slv_b_valids_o  ({ bypass_b_valid,  from_llc_b_valid  }),
    .slv_b_readies_i ({ bypass_b_ready,  from_llc_b_ready  }),
    .slv_ar_chans_i  ({ bypass_ar,       from_llc_ar       }),
    .slv_ar_valids_i ({ bypass_ar_valid, from_llc_ar_valid }),
    .slv_ar_readies_o({ bypass_ar_ready, from_llc_ar_ready }),
    .slv_r_chans_o   ({ bypass_r,        from_llc_r        }),
    .slv_r_valids_o  ({ bypass_r_valid,  from_llc_r_valid  }),
    .slv_r_readies_i ({ bypass_r_ready,  from_llc_r_ready  }),
    .mst_aw_chan_o   ( mst_req_o.aw                         ),
    .mst_aw_valid_o  ( mst_req_o.aw_valid                   ),
    .mst_aw_ready_i  ( mst_resp_i.aw_ready                  ),
    .mst_w_chan_o    ( mst_req_o.w                          ),
    .mst_w_valid_o   ( mst_req_o.w_valid                    ),
    .mst_w_ready_i   ( mst_resp_i.w_ready                   ),
    .mst_b_chan_i    ( mst_resp_i.b                         ),
    .mst_b_valid_i   ( mst_resp_i.b_valid                   ),
    .mst_b_ready_o   ( mst_req_o.b_ready                    ),
    .mst_ar_chan_o   ( mst_req_o.ar                         ),
    .mst_ar_valid_o  ( mst_req_o.ar_valid                   ),
    .mst_ar_ready_i  ( mst_resp_i.ar_ready                  ),
    .mst_r_chan_i    ( mst_resp_i.r                         ),
    .mst_r_valid_i   ( mst_resp_i.r_valid                   ),
    .mst_r_ready_o   ( mst_req_o.r_ready                    )
  );

  // pragma translate_off
  `ifndef VERILATOR
  `ifndef VCS
  `ifndef SYNTHESIS
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
  `endif
  `endif
  // pragma translate_on

endmodule
