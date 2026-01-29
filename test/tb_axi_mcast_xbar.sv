// Copyright (c) 2019 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Authors:
// - Wolfgang Roenninger <wroennin@ethz.ch>
// - Florian Zaruba <zarubaf@iis.ee.ethz.ch>
// - Andreas Kurth <akurth@iis.ee.ethz.ch>
// - Luca Colagrande <colluca@iis.ee.ethz.ch>

// Directed Random Verification Testbench for `axi_xbar`:  The crossbar is instantiated with
// a number of random axi master and slave modules.  Each random master executes a fixed number of
// writes and reads over the whole addess map.  All masters simultaneously issue transactions
// through the crossbar, thereby saturating it.  A monitor, which snoops the transactions of each
// master and slave port and models the crossbar with a network of FIFOs, checks whether each
// transaction follows the expected route.

`include "axi/typedef.svh"
`include "axi/assign.svh"

/// Testbench for the module `axi_mcast_xbar`.
module tb_axi_mcast_xbar #(
  /// Number of AXI masters connected to the xbar. (Number of slave ports)
  parameter int unsigned TbNumMasters        = 32'd6,
  /// Number of AXI slaves connected to the xbar which can be targeted by multicast
  /// transactions. (Number of multicast-enabled master ports)
  parameter int unsigned TbNumMcastSlaves    = 32'd8,
  /// Number of write transactions per master.
  parameter int unsigned TbNumWrites         = 32'd200,
  /// Number of read transactions per master.
  parameter int unsigned TbNumReads          = 32'd200,
  /// AXI4+ATOP ID width of the masters connected to the slave ports of the DUT.
  /// The ID width of the slaves is calculated depending on the xbar configuration.
  parameter int unsigned TbAxiIdWidthMasters = 32'd5,
  /// The used ID width of the DUT.
  /// Has to be `TbAxiIdWidthMasters >= TbAxiIdUsed`.
  parameter int unsigned TbAxiIdUsed         = 32'd3,
  /// Data width of the AXI channels.
  parameter int unsigned TbAxiDataWidth      = 32'd64,
  /// Pipeline stages in the xbar itself (between demux and mux).
  parameter int unsigned TbPipeline          = 32'd1,
  /// Enable ATOP generation
  parameter bit          TbEnAtop            = 1'b1,
  /// Enable exclusive accesses
  parameter bit TbEnExcl                     = 1'b0,   
  /// Restrict to only unique IDs         
  parameter bit TbUniqueIds                  = 1'b0
);

  // TB timing parameters
  localparam time CyclTime = 10ns;
  localparam time ApplTime =  2ns;
  localparam time TestTime =  8ns;

  // AXI configuration which is automatically derived.
  localparam int unsigned TbAxiIdWidthSlaves =  TbAxiIdWidthMasters + $clog2(TbNumMasters);
  localparam int unsigned TbAxiAddrWidth     =  32'd32;
  localparam int unsigned TbAxiStrbWidth     =  TbAxiDataWidth / 8;
  localparam int unsigned TbAxiUserWidth     =  TbAxiAddrWidth;
  // In the bench can change this variables which are set here freely,
  localparam TbNumSlaves = TbNumMcastSlaves + 1;
  localparam axi_pkg::xbar_cfg_t xbar_cfg = '{
    NoSlvPorts:         TbNumMasters,
    NoMstPorts:         TbNumSlaves,
    MaxMstTrans:        10,
    MaxSlvTrans:        6,
    FallThrough:        1'b0,
    LatencyMode:        axi_pkg::CUT_ALL_PORTS,
    PipelineStages:     TbPipeline,
    AxiIdWidthSlvPorts: TbAxiIdWidthMasters,
    AxiIdUsedSlvPorts:  TbAxiIdUsed,
    UniqueIds:          TbUniqueIds,
    AxiAddrWidth:       TbAxiAddrWidth,
    AxiDataWidth:       TbAxiDataWidth,
    NoAddrRules:        TbNumMcastSlaves * 2 + 1,
    NoMulticastRules:   TbNumMcastSlaves * 2,
    NoMulticastPorts:   TbNumMcastSlaves
  };
  typedef logic [TbAxiIdWidthMasters-1:0] id_mst_t;
  typedef logic [TbAxiIdWidthSlaves-1:0]  id_slv_t;
  typedef logic [TbAxiAddrWidth-1:0]      addr_t;
  typedef struct packed {
    int unsigned idx;
    addr_t start_addr;
    addr_t end_addr;
  } rule_t;
  typedef logic [TbAxiDataWidth-1:0]      data_t;
  typedef logic [TbAxiStrbWidth-1:0]      strb_t;
  typedef logic [TbAxiUserWidth-1:0]      user_t;
  // For collectives, AW channel should contain collective mask in USER field
  typedef struct packed {
    addr_t collective_mask;
  } aw_user_t;

  `AXI_TYPEDEF_AW_CHAN_T(aw_chan_mst_t, addr_t, id_mst_t, aw_user_t)
  `AXI_TYPEDEF_AW_CHAN_T(aw_chan_slv_t, addr_t, id_slv_t, aw_user_t)
  `AXI_TYPEDEF_W_CHAN_T(w_chan_t, data_t, strb_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T(b_chan_mst_t, id_mst_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T(b_chan_slv_t, id_slv_t, user_t)

  `AXI_TYPEDEF_AR_CHAN_T(ar_chan_mst_t, addr_t, id_mst_t, user_t)
  `AXI_TYPEDEF_AR_CHAN_T(ar_chan_slv_t, addr_t, id_slv_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(r_chan_mst_t, data_t, id_mst_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(r_chan_slv_t, data_t, id_slv_t, user_t)

  `AXI_TYPEDEF_REQ_T(mst_req_t, aw_chan_mst_t, w_chan_t, ar_chan_mst_t)
  `AXI_TYPEDEF_RESP_T(mst_resp_t, b_chan_mst_t, r_chan_mst_t)
  `AXI_TYPEDEF_REQ_T(slv_req_t, aw_chan_slv_t, w_chan_t, ar_chan_slv_t)
  `AXI_TYPEDEF_RESP_T(slv_resp_t, b_chan_slv_t, r_chan_slv_t)

  // Each slave has its own address range:
  localparam rule_t [xbar_cfg.NoAddrRules-1:0] AddrMap = {
    rule_t'{
      idx:        TbNumMcastSlaves,
      start_addr: 32'h7000_0000,
      end_addr:   32'h7008_0000
    },
    addr_map_gen(32'h1000_0000, 32'h10_0000),
    addr_map_gen(32'h0b00_0000, 32'h1_0000)
  };

  function rule_t [xbar_cfg.NoMulticastPorts-1:0] addr_map_gen (addr_t base, addr_t offset);
    for (int unsigned i = 0; i < xbar_cfg.NoMulticastPorts; i++) begin
      addr_map_gen[i] = rule_t'{
        idx:        unsigned'(i),
        start_addr: base + offset * i,
        end_addr:   base + offset * (i + 1),
        default:    '0
      };
    end
  endfunction

  typedef axi_test::axi_rand_master #(
    // AXI interface parameters
    .AW ( TbAxiAddrWidth          ),
    .DW ( TbAxiDataWidth          ),
    .IW ( TbAxiIdWidthMasters     ),
    .UW ( TbAxiUserWidth          ),
    // Stimuli application and test time
    .TA ( ApplTime                ),
    .TT ( TestTime                ),
    // Maximum number of read and write transactions in flight
    .MAX_READ_TXNS  ( 20          ),
    .MAX_WRITE_TXNS ( 20          ),
    .AXI_EXCLS      ( TbEnExcl    ),
    .AXI_ATOPS      ( TbEnAtop    ),
    .UNIQUE_IDS     ( TbUniqueIds ),
    .ENABLE_MULTICAST ( 1         )
  ) axi_rand_master_t;
  typedef axi_test::axi_rand_slave #(
    // AXI interface parameters
    .AW ( TbAxiAddrWidth     ),
    .DW ( TbAxiDataWidth     ),
    .IW ( TbAxiIdWidthSlaves ),
    .UW ( TbAxiUserWidth     ),
    // Stimuli application and test time
    .TA ( ApplTime           ),
    .TT ( TestTime           )
  ) axi_rand_slave_t;

  // -------------
  // DUT signals
  // -------------
  logic clk;
  // DUT signals
  logic rst_n;
  logic [TbNumMasters-1:0] end_of_sim;

  // master structs
  mst_req_t  [TbNumMasters-1:0] masters_req;
  mst_resp_t [TbNumMasters-1:0] masters_resp;

  // slave structs
  slv_req_t  [TbNumSlaves-1:0]  slaves_req;
  slv_resp_t [TbNumSlaves-1:0]  slaves_resp;

  // -------------------------------
  // AXI Interfaces
  // -------------------------------
  AXI_BUS #(
    .AXI_ADDR_WIDTH ( TbAxiAddrWidth      ),
    .AXI_DATA_WIDTH ( TbAxiDataWidth      ),
    .AXI_ID_WIDTH   ( TbAxiIdWidthMasters ),
    .AXI_USER_WIDTH ( TbAxiUserWidth      )
  ) master [TbNumMasters-1:0] ();
  AXI_BUS_DV #(
    .AXI_ADDR_WIDTH ( TbAxiAddrWidth      ),
    .AXI_DATA_WIDTH ( TbAxiDataWidth      ),
    .AXI_ID_WIDTH   ( TbAxiIdWidthMasters ),
    .AXI_USER_WIDTH ( TbAxiUserWidth      )
  ) master_dv [TbNumMasters-1:0] (clk);
  AXI_BUS_DV #(
    .AXI_ADDR_WIDTH ( TbAxiAddrWidth      ),
    .AXI_DATA_WIDTH ( TbAxiDataWidth      ),
    .AXI_ID_WIDTH   ( TbAxiIdWidthMasters ),
    .AXI_USER_WIDTH ( TbAxiUserWidth      )
  ) master_monitor_dv [TbNumMasters-1:0] (clk);
  for (genvar i = 0; i < TbNumMasters; i++) begin : gen_conn_dv_masters
    `AXI_ASSIGN (master[i], master_dv[i])
    `AXI_ASSIGN_TO_REQ(masters_req[i], master[i])
    `AXI_ASSIGN_TO_RESP(masters_resp[i], master[i])
  end

  AXI_BUS #(
    .AXI_ADDR_WIDTH ( TbAxiAddrWidth     ),
    .AXI_DATA_WIDTH ( TbAxiDataWidth     ),
    .AXI_ID_WIDTH   ( TbAxiIdWidthSlaves ),
    .AXI_USER_WIDTH ( TbAxiUserWidth     )
  ) slave [TbNumSlaves-1:0] ();
  AXI_BUS_DV #(
    .AXI_ADDR_WIDTH ( TbAxiAddrWidth     ),
    .AXI_DATA_WIDTH ( TbAxiDataWidth     ),
    .AXI_ID_WIDTH   ( TbAxiIdWidthSlaves ),
    .AXI_USER_WIDTH ( TbAxiUserWidth     )
  ) slave_dv [TbNumSlaves-1:0](clk);
  AXI_BUS_DV #(
    .AXI_ADDR_WIDTH ( TbAxiAddrWidth     ),
    .AXI_DATA_WIDTH ( TbAxiDataWidth     ),
    .AXI_ID_WIDTH   ( TbAxiIdWidthSlaves ),
    .AXI_USER_WIDTH ( TbAxiUserWidth     )
  ) slave_monitor_dv [TbNumSlaves-1:0](clk);
  for (genvar i = 0; i < TbNumSlaves; i++) begin : gen_conn_dv_slaves
    `AXI_ASSIGN(slave_dv[i], slave[i])
    `AXI_ASSIGN_TO_REQ(slaves_req[i], slave[i])
    `AXI_ASSIGN_TO_RESP(slaves_resp[i], slave[i])
  end
  // -------------------------------
  // AXI Rand Masters and Slaves
  // -------------------------------
  // Masters control simulation run time
  axi_rand_master_t axi_rand_master [TbNumMasters];
  for (genvar i = 0; i < TbNumMasters; i++) begin : gen_rand_master
    initial begin
      axi_rand_master[i] = new( master_dv[i] );
      end_of_sim[i] <= 1'b0;
      axi_rand_master[i].add_memory_region(AddrMap[0].start_addr,
                                      AddrMap[xbar_cfg.NoMulticastPorts-1].end_addr,
                                      axi_pkg::DEVICE_NONBUFFERABLE);
      axi_rand_master[i].add_memory_region(AddrMap[xbar_cfg.NoMulticastPorts].start_addr,
                                      AddrMap[xbar_cfg.NoMulticastRules-1].end_addr,
                                      axi_pkg::DEVICE_NONBUFFERABLE);
      axi_rand_master[i].add_memory_region(AddrMap[xbar_cfg.NoMulticastRules].start_addr,
                                      AddrMap[xbar_cfg.NoAddrRules-1].end_addr,
                                      axi_pkg::DEVICE_NONBUFFERABLE);
      axi_rand_master[i].set_multicast_probability(50);
      axi_rand_master[i].reset();
      @(posedge rst_n);
      axi_rand_master[i].run(TbNumReads, TbNumWrites);
      end_of_sim[i] <= 1'b1;
    end
  end

  axi_rand_slave_t axi_rand_slave [TbNumSlaves];
  for (genvar i = 0; i < TbNumSlaves; i++) begin : gen_rand_slave
    initial begin
      axi_rand_slave[i] = new( slave_dv[i] );
      axi_rand_slave[i].reset();
      @(posedge rst_n);
      axi_rand_slave[i].run();
    end
  end

  initial begin : proc_monitor
    static tb_axi_xbar_pkg::axi_xbar_monitor #(
      .AxiAddrWidth      ( TbAxiAddrWidth       ),
      .AxiDataWidth      ( TbAxiDataWidth       ),
      .AxiIdWidthMasters ( TbAxiIdWidthMasters  ),
      .AxiIdWidthSlaves  ( TbAxiIdWidthSlaves   ),
      .AxiUserWidth      ( TbAxiUserWidth       ),
      .NoMasters         ( TbNumMasters         ),
      .NoSlaves          ( TbNumSlaves          ),
      .NoAddrRules       ( xbar_cfg.NoAddrRules ),
      .NoMulticastRules  ( xbar_cfg.NoMulticastRules ),
      .rule_t            ( rule_t               ),
      .AddrMap           ( AddrMap              ),
      .TimeTest          ( TestTime             )
    ) monitor = new( master_monitor_dv, slave_monitor_dv );
    fork
      monitor.run();
      do begin
        #TestTime;
        if(end_of_sim == '1) begin
          monitor.print_result();
          $stop();
        end
        @(posedge clk);
      end while (1'b1);
    join
  end

  //-----------------------------------
  // Clock generator
  //-----------------------------------
    clk_rst_gen #(
    .ClkPeriod    ( CyclTime ),
    .RstClkCycles ( 5        )
  ) i_clk_gen (
    .clk_o (clk),
    .rst_no(rst_n)
  );

  //-----------------------------------
  // DUT
  //-----------------------------------

  axi_mcast_xbar_intf #(
    .AXI_USER_WIDTH ( TbAxiUserWidth ),
    .Cfg            ( xbar_cfg       ),
    .aw_user_t      ( aw_user_t      ),
    .rule_t         ( rule_t         )
  ) i_xbar_dut (
    .clk_i                  ( clk     ),
    .rst_ni                 ( rst_n   ),
    .test_i                 ( 1'b0    ),
    .slv_ports              ( master  ),
    .mst_ports              ( slave   ),
    .addr_map_i             ( AddrMap ),
    .en_default_mst_port_i  ( '0      ),
    .default_mst_port_i     ( '0      )
  );

  // logger for master modules
  for (genvar i = 0; i < TbNumMasters; i++) begin : gen_master_logger
    axi_chan_logger #(
      .TestTime  ( TestTime      ), // Time after clock, where sampling happens
      .LoggerName( $sformatf("axi_logger_master_%0d", i)),
      .aw_chan_t ( aw_chan_mst_t ), // axi AW type
      .w_chan_t  (  w_chan_t     ), // axi  W type
      .b_chan_t  (  b_chan_mst_t ), // axi  B type
      .ar_chan_t ( ar_chan_mst_t ), // axi AR type
      .r_chan_t  (  r_chan_mst_t ), // axi  R type
      .ENABLE_MULTICAST(1)
    ) i_mst_channel_logger (
      .clk_i      ( clk         ),    // Clock
      .rst_ni     ( rst_n       ),    // Asynchronous reset active low, when `1'b0` no sampling
      .end_sim_i  ( &end_of_sim ),
      // AW channel
      .aw_chan_i  ( masters_req[i].aw        ),
      .aw_valid_i ( masters_req[i].aw_valid  ),
      .aw_ready_i ( masters_resp[i].aw_ready ),
      //  W channel
      .w_chan_i   ( masters_req[i].w         ),
      .w_valid_i  ( masters_req[i].w_valid   ),
      .w_ready_i  ( masters_resp[i].w_ready  ),
      //  B channel
      .b_chan_i   ( masters_resp[i].b        ),
      .b_valid_i  ( masters_resp[i].b_valid  ),
      .b_ready_i  ( masters_req[i].b_ready   ),
      // AR channel
      .ar_chan_i  ( masters_req[i].ar        ),
      .ar_valid_i ( masters_req[i].ar_valid  ),
      .ar_ready_i ( masters_resp[i].ar_ready ),
      //  R channel
      .r_chan_i   ( masters_resp[i].r        ),
      .r_valid_i  ( masters_resp[i].r_valid  ),
      .r_ready_i  ( masters_req[i].r_ready   )
    );
  end
  // logger for slave modules
  for (genvar i = 0; i < TbNumSlaves; i++) begin : gen_slave_logger
    axi_chan_logger #(
      .TestTime  ( TestTime      ), // Time after clock, where sampling happens
      .LoggerName( $sformatf("axi_logger_slave_%0d",i)),
      .aw_chan_t ( aw_chan_slv_t ), // axi AW type
      .w_chan_t  (  w_chan_t     ), // axi  W type
      .b_chan_t  (  b_chan_slv_t ), // axi  B type
      .ar_chan_t ( ar_chan_slv_t ), // axi AR type
      .r_chan_t  (  r_chan_slv_t )  // axi  R type
    ) i_slv_channel_logger (
      .clk_i      ( clk         ),    // Clock
      .rst_ni     ( rst_n       ),    // Asynchronous reset active low, when `1'b0` no sampling
      .end_sim_i  ( &end_of_sim ),
      // AW channel
      .aw_chan_i  ( slaves_req[i].aw        ),
      .aw_valid_i ( slaves_req[i].aw_valid  ),
      .aw_ready_i ( slaves_resp[i].aw_ready ),
      //  W channel
      .w_chan_i   ( slaves_req[i].w         ),
      .w_valid_i  ( slaves_req[i].w_valid   ),
      .w_ready_i  ( slaves_resp[i].w_ready  ),
      //  B channel
      .b_chan_i   ( slaves_resp[i].b        ),
      .b_valid_i  ( slaves_resp[i].b_valid  ),
      .b_ready_i  ( slaves_req[i].b_ready   ),
      // AR channel
      .ar_chan_i  ( slaves_req[i].ar        ),
      .ar_valid_i ( slaves_req[i].ar_valid  ),
      .ar_ready_i ( slaves_resp[i].ar_ready ),
      //  R channel
      .r_chan_i   ( slaves_resp[i].r        ),
      .r_valid_i  ( slaves_resp[i].r_valid  ),
      .r_ready_i  ( slaves_req[i].r_ready   )
    );
  end


  for (genvar i = 0; i < TbNumMasters; i++) begin : gen_connect_master_monitor
    assign master_monitor_dv[i].aw_id     = master[i].aw_id    ;
    assign master_monitor_dv[i].aw_addr   = master[i].aw_addr  ;
    assign master_monitor_dv[i].aw_len    = master[i].aw_len   ;
    assign master_monitor_dv[i].aw_size   = master[i].aw_size  ;
    assign master_monitor_dv[i].aw_burst  = master[i].aw_burst ;
    assign master_monitor_dv[i].aw_lock   = master[i].aw_lock  ;
    assign master_monitor_dv[i].aw_cache  = master[i].aw_cache ;
    assign master_monitor_dv[i].aw_prot   = master[i].aw_prot  ;
    assign master_monitor_dv[i].aw_qos    = master[i].aw_qos   ;
    assign master_monitor_dv[i].aw_region = master[i].aw_region;
    assign master_monitor_dv[i].aw_atop   = master[i].aw_atop  ;
    assign master_monitor_dv[i].aw_user   = master[i].aw_user  ;
    assign master_monitor_dv[i].aw_valid  = master[i].aw_valid ;
    assign master_monitor_dv[i].aw_ready  = master[i].aw_ready ;
    assign master_monitor_dv[i].w_data    = master[i].w_data   ;
    assign master_monitor_dv[i].w_strb    = master[i].w_strb   ;
    assign master_monitor_dv[i].w_last    = master[i].w_last   ;
    assign master_monitor_dv[i].w_user    = master[i].w_user   ;
    assign master_monitor_dv[i].w_valid   = master[i].w_valid  ;
    assign master_monitor_dv[i].w_ready   = master[i].w_ready  ;
    assign master_monitor_dv[i].b_id      = master[i].b_id     ;
    assign master_monitor_dv[i].b_resp    = master[i].b_resp   ;
    assign master_monitor_dv[i].b_user    = master[i].b_user   ;
    assign master_monitor_dv[i].b_valid   = master[i].b_valid  ;
    assign master_monitor_dv[i].b_ready   = master[i].b_ready  ;
    assign master_monitor_dv[i].ar_id     = master[i].ar_id    ;
    assign master_monitor_dv[i].ar_addr   = master[i].ar_addr  ;
    assign master_monitor_dv[i].ar_len    = master[i].ar_len   ;
    assign master_monitor_dv[i].ar_size   = master[i].ar_size  ;
    assign master_monitor_dv[i].ar_burst  = master[i].ar_burst ;
    assign master_monitor_dv[i].ar_lock   = master[i].ar_lock  ;
    assign master_monitor_dv[i].ar_cache  = master[i].ar_cache ;
    assign master_monitor_dv[i].ar_prot   = master[i].ar_prot  ;
    assign master_monitor_dv[i].ar_qos    = master[i].ar_qos   ;
    assign master_monitor_dv[i].ar_region = master[i].ar_region;
    assign master_monitor_dv[i].ar_user   = master[i].ar_user  ;
    assign master_monitor_dv[i].ar_valid  = master[i].ar_valid ;
    assign master_monitor_dv[i].ar_ready  = master[i].ar_ready ;
    assign master_monitor_dv[i].r_id      = master[i].r_id     ;
    assign master_monitor_dv[i].r_data    = master[i].r_data   ;
    assign master_monitor_dv[i].r_resp    = master[i].r_resp   ;
    assign master_monitor_dv[i].r_last    = master[i].r_last   ;
    assign master_monitor_dv[i].r_user    = master[i].r_user   ;
    assign master_monitor_dv[i].r_valid   = master[i].r_valid  ;
    assign master_monitor_dv[i].r_ready   = master[i].r_ready  ;
  end
  for (genvar i = 0; i < TbNumSlaves; i++) begin : gen_connect_slave_monitor
    assign slave_monitor_dv[i].aw_id     = slave[i].aw_id    ;
    assign slave_monitor_dv[i].aw_addr   = slave[i].aw_addr  ;
    assign slave_monitor_dv[i].aw_len    = slave[i].aw_len   ;
    assign slave_monitor_dv[i].aw_size   = slave[i].aw_size  ;
    assign slave_monitor_dv[i].aw_burst  = slave[i].aw_burst ;
    assign slave_monitor_dv[i].aw_lock   = slave[i].aw_lock  ;
    assign slave_monitor_dv[i].aw_cache  = slave[i].aw_cache ;
    assign slave_monitor_dv[i].aw_prot   = slave[i].aw_prot  ;
    assign slave_monitor_dv[i].aw_qos    = slave[i].aw_qos   ;
    assign slave_monitor_dv[i].aw_region = slave[i].aw_region;
    assign slave_monitor_dv[i].aw_atop   = slave[i].aw_atop  ;
    assign slave_monitor_dv[i].aw_user   = slave[i].aw_user  ;
    assign slave_monitor_dv[i].aw_valid  = slave[i].aw_valid ;
    assign slave_monitor_dv[i].aw_ready  = slave[i].aw_ready ;
    assign slave_monitor_dv[i].w_data    = slave[i].w_data   ;
    assign slave_monitor_dv[i].w_strb    = slave[i].w_strb   ;
    assign slave_monitor_dv[i].w_last    = slave[i].w_last   ;
    assign slave_monitor_dv[i].w_user    = slave[i].w_user   ;
    assign slave_monitor_dv[i].w_valid   = slave[i].w_valid  ;
    assign slave_monitor_dv[i].w_ready   = slave[i].w_ready  ;
    assign slave_monitor_dv[i].b_id      = slave[i].b_id     ;
    assign slave_monitor_dv[i].b_resp    = slave[i].b_resp   ;
    assign slave_monitor_dv[i].b_user    = slave[i].b_user   ;
    assign slave_monitor_dv[i].b_valid   = slave[i].b_valid  ;
    assign slave_monitor_dv[i].b_ready   = slave[i].b_ready  ;
    assign slave_monitor_dv[i].ar_id     = slave[i].ar_id    ;
    assign slave_monitor_dv[i].ar_addr   = slave[i].ar_addr  ;
    assign slave_monitor_dv[i].ar_len    = slave[i].ar_len   ;
    assign slave_monitor_dv[i].ar_size   = slave[i].ar_size  ;
    assign slave_monitor_dv[i].ar_burst  = slave[i].ar_burst ;
    assign slave_monitor_dv[i].ar_lock   = slave[i].ar_lock  ;
    assign slave_monitor_dv[i].ar_cache  = slave[i].ar_cache ;
    assign slave_monitor_dv[i].ar_prot   = slave[i].ar_prot  ;
    assign slave_monitor_dv[i].ar_qos    = slave[i].ar_qos   ;
    assign slave_monitor_dv[i].ar_region = slave[i].ar_region;
    assign slave_monitor_dv[i].ar_user   = slave[i].ar_user  ;
    assign slave_monitor_dv[i].ar_valid  = slave[i].ar_valid ;
    assign slave_monitor_dv[i].ar_ready  = slave[i].ar_ready ;
    assign slave_monitor_dv[i].r_id      = slave[i].r_id     ;
    assign slave_monitor_dv[i].r_data    = slave[i].r_data   ;
    assign slave_monitor_dv[i].r_resp    = slave[i].r_resp   ;
    assign slave_monitor_dv[i].r_last    = slave[i].r_last   ;
    assign slave_monitor_dv[i].r_user    = slave[i].r_user   ;
    assign slave_monitor_dv[i].r_valid   = slave[i].r_valid  ;
    assign slave_monitor_dv[i].r_ready   = slave[i].r_ready  ;
  end
endmodule
