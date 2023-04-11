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

// Directed Random Verification Testbench for `axi_xbar`:  The crossbar is instantiated with
// a number of random axi manager and subordinate modules.  Each random manager executes a fixed number of
// writes and reads over the whole addess map.  All managers simultaneously issue transactions
// through the crossbar, thereby saturating it.  A monitor, which snoops the transactions of each
// manager and subordinate port and models the crossbar with a network of FIFOs, checks whether each
// transaction follows the expected route.

`include "axi/typedef.svh"
`include "axi/assign.svh"

/// Testbench for the module `axi_xbar`.
module tb_axi_xbar #(
  /// Number of AXI managers connected to the xbar. (Number of subordinate ports)
  parameter int unsigned TbNumManagers     = 32'd6,
  /// Number of AXI subordinates connected to the xbar. (Number of manager ports)
  parameter int unsigned TbNumSubordinates      = 32'd8,
  /// Number of write transactions per manager.
  parameter int unsigned TbNumWrites      = 32'd200,
  /// Number of read transactions per manager.
  parameter int unsigned TbNumReads       = 32'd200,
  /// AXI4+ATOP ID width of the managers connected to the subordinate ports of the DUT.
  /// The ID width of the subordinates is calculated depending on the xbar configuration.
  parameter int unsigned TbIdWidthManagers = 32'd5,
  /// The used ID width of the DUT.
  /// Has to be `TbIdWidthManagers >= TbIdUsed`.
  parameter int unsigned TbIdUsed         = 32'd3,
  /// Data width of the AXI channels.
  parameter int unsigned TbDataWidth      = 32'd64,
  /// Pipeline stages in the xbar itself (between demux and mux).
  parameter int unsigned TbPipeline       = 32'd1,
  /// Enable ATOP generation
  parameter bit          TbEnAtop         = 1'b1,
  /// Enable exclusive accesses
  parameter bit TbEnExcl                  = 1'b0,   
  /// Restrict to only unique IDs         
  parameter bit TbUniqueIds               = 1'b0       

);

  // TB timing parameters
  localparam time CyclTime = 10ns;
  localparam time ApplTime =  2ns;
  localparam time TestTime =  8ns;

  // AXI configuration which is automatically derived.
  localparam int unsigned TbIdWidthSubordinates =  TbIdWidthManagers + $clog2(TbNumManagers);
  localparam int unsigned TbAddrWidth     =  32'd32;
  localparam int unsigned TbStrbWidth     =  TbDataWidth / 8;
  localparam int unsigned TbUserWidth     =  5;
  // In the bench can change this variables which are set here freely,
  localparam axi_pkg::xbar_cfg_t xbar_cfg = '{
    NumSbrPorts:     TbNumManagers,
    NumMgrPorts:     TbNumSubordinates,
    MaxMgrTrans:     10,
    MaxSbrTrans:     6,
    FallThrough:     1'b0,
    LatencyMode:     axi_pkg::CUT_ALL_AX,
    PipelineStages:  TbPipeline,
    IdWidthSbrPorts: TbIdWidthManagers,
    IdUsedSbrPorts:  TbIdUsed,
    UniqueIds:       TbUniqueIds,
    AddrWidth:       TbAddrWidth,
    DataWidth:       TbDataWidth,
    NumAddrRules:    TbNumSubordinates
  };
  typedef logic [TbIdWidthManagers-1:0] id_mgr_t;
  typedef logic [TbIdWidthSubordinates-1:0]  id_sbr_t;
  typedef logic [TbAddrWidth-1:0]      addr_t;
  typedef axi_pkg::xbar_rule_32_t      rule_t; // Has to be the same width as axi addr
  typedef logic [TbDataWidth-1:0]      data_t;
  typedef logic [TbStrbWidth-1:0]      strb_t;
  typedef logic [TbUserWidth-1:0]      user_t;

  `AXI_TYPEDEF_AW_CHAN_T(aw_chan_mgr_t, addr_t, id_mgr_t, user_t)
  `AXI_TYPEDEF_AW_CHAN_T(aw_chan_sbr_t, addr_t, id_sbr_t, user_t)
  `AXI_TYPEDEF_W_CHAN_T(w_chan_t, data_t, strb_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T(b_chan_mgr_t, id_mgr_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T(b_chan_sbr_t, id_sbr_t, user_t)

  `AXI_TYPEDEF_AR_CHAN_T(ar_chan_mgr_t, addr_t, id_mgr_t, user_t)
  `AXI_TYPEDEF_AR_CHAN_T(ar_chan_sbr_t, addr_t, id_sbr_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(r_chan_mgr_t, data_t, id_mgr_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(r_chan_sbr_t, data_t, id_sbr_t, user_t)

  `AXI_TYPEDEF_REQ_T(mgr_req_t, aw_chan_mgr_t, w_chan_t, ar_chan_mgr_t)
  `AXI_TYPEDEF_RSP_T(mgr_rsp_t, b_chan_mgr_t, r_chan_mgr_t)
  `AXI_TYPEDEF_REQ_T(sbr_req_t, aw_chan_sbr_t, w_chan_t, ar_chan_sbr_t)
  `AXI_TYPEDEF_RSP_T(sbr_rsp_t, b_chan_sbr_t, r_chan_sbr_t)

  // Each subordinate has its own address range:
  localparam rule_t [xbar_cfg.NumAddrRules-1:0] AddrMap = addr_map_gen();

  function rule_t [xbar_cfg.NumAddrRules-1:0] addr_map_gen ();
    for (int unsigned i = 0; i < xbar_cfg.NumAddrRules; i++) begin
      addr_map_gen[i] = rule_t'{
        idx:        unsigned'(i),
        start_addr:  i    * 32'h0000_2000,
        end_addr:   (i+1) * 32'h0000_2000,
        default:    '0
      };
    end
  endfunction

  typedef axi_test::axi_rand_manager #(
    // AXI interface parameters
    .AW ( TbAddrWidth          ),
    .DW ( TbDataWidth          ),
    .IW ( TbIdWidthManagers     ),
    .UW ( TbUserWidth          ),
    // Stimuli application and test time
    .TA ( ApplTime                ),
    .TT ( TestTime                ),
    // Maximum number of read and write transactions in flight
    .MAX_READ_TXNS  ( 20          ),
    .MAX_WRITE_TXNS ( 20          ),
    .AXI_EXCLS      ( TbEnExcl    ),
    .AXI_ATOPS      ( TbEnAtop    ),
    .UNIQUE_IDS     ( TbUniqueIds )
  ) axi_rand_manager_t;
  typedef axi_test::axi_rand_subordinate #(
    // AXI interface parameters
    .AW ( TbAddrWidth     ),
    .DW ( TbDataWidth     ),
    .IW ( TbIdWidthSubordinates ),
    .UW ( TbUserWidth     ),
    // Stimuli application and test time
    .TA ( ApplTime           ),
    .TT ( TestTime           )
  ) axi_rand_subordinate_t;

  // -------------
  // DUT signals
  // -------------
  logic clk;
  // DUT signals
  logic rst_n;
  logic [TbNumManagers-1:0] end_of_sim;

  // manager structs
  mgr_req_t [TbNumManagers-1:0] managers_req;
  mgr_rsp_t [TbNumManagers-1:0] managers_rsp;

  // subordinate structs
  sbr_req_t [TbNumSubordinates-1:0]  subordinates_req;
  sbr_rsp_t [TbNumSubordinates-1:0]  subordinates_rsp;

  // -------------------------------
  // AXI Interfaces
  // -------------------------------
  AXI_BUS #(
    .AXI_ADDR_WIDTH ( TbAddrWidth      ),
    .AXI_DATA_WIDTH ( TbDataWidth      ),
    .AXI_ID_WIDTH   ( TbIdWidthManagers ),
    .AXI_USER_WIDTH ( TbUserWidth      )
  ) manager [TbNumManagers-1:0] ();
  AXI_BUS_DV #(
    .AXI_ADDR_WIDTH ( TbAddrWidth      ),
    .AXI_DATA_WIDTH ( TbDataWidth      ),
    .AXI_ID_WIDTH   ( TbIdWidthManagers ),
    .AXI_USER_WIDTH ( TbUserWidth      )
  ) manager_dv [TbNumManagers-1:0] (clk);
  AXI_BUS_DV #(
    .AXI_ADDR_WIDTH ( TbAddrWidth      ),
    .AXI_DATA_WIDTH ( TbDataWidth      ),
    .AXI_ID_WIDTH   ( TbIdWidthManagers ),
    .AXI_USER_WIDTH ( TbUserWidth      )
  ) manager_monitor_dv [TbNumManagers-1:0] (clk);
  for (genvar i = 0; i < TbNumManagers; i++) begin : gen_conn_dv_managers
    `AXI_ASSIGN (manager[i], manager_dv[i])
    `AXI_ASSIGN_TO_REQ(managers_req[i], manager[i])
    `AXI_ASSIGN_TO_RSP(managers_rsp[i], manager[i])
  end

  AXI_BUS #(
    .AXI_ADDR_WIDTH ( TbAddrWidth     ),
    .AXI_DATA_WIDTH ( TbDataWidth     ),
    .AXI_ID_WIDTH   ( TbIdWidthSubordinates ),
    .AXI_USER_WIDTH ( TbUserWidth     )
  ) subordinate [TbNumSubordinates-1:0] ();
  AXI_BUS_DV #(
    .AXI_ADDR_WIDTH ( TbAddrWidth     ),
    .AXI_DATA_WIDTH ( TbDataWidth     ),
    .AXI_ID_WIDTH   ( TbIdWidthSubordinates ),
    .AXI_USER_WIDTH ( TbUserWidth     )
  ) subordinate_dv [TbNumSubordinates-1:0](clk);
  AXI_BUS_DV #(
    .AXI_ADDR_WIDTH ( TbAddrWidth     ),
    .AXI_DATA_WIDTH ( TbDataWidth     ),
    .AXI_ID_WIDTH   ( TbIdWidthSubordinates ),
    .AXI_USER_WIDTH ( TbUserWidth     )
  ) subordinate_monitor_dv [TbNumSubordinates-1:0](clk);
  for (genvar i = 0; i < TbNumSubordinates; i++) begin : gen_conn_dv_subordinates
    `AXI_ASSIGN(subordinate_dv[i], subordinate[i])
    `AXI_ASSIGN_TO_REQ(subordinates_req[i], subordinate[i])
    `AXI_ASSIGN_TO_RSP(subordinates_rsp[i], subordinate[i])
  end
  // -------------------------------
  // AXI Rand Managers and Subordinates
  // -------------------------------
  // Managers control simulation run time
  axi_rand_manager_t axi_rand_manager [TbNumManagers];
  for (genvar i = 0; i < TbNumManagers; i++) begin : gen_rand_manager
    initial begin
      axi_rand_manager[i] = new( manager_dv[i] );
      end_of_sim[i] <= 1'b0;
      axi_rand_manager[i].add_memory_region(AddrMap[0].start_addr,
                                      AddrMap[xbar_cfg.NumAddrRules-1].end_addr,
                                      axi_pkg::DEVICE_NONBUFFERABLE);
      axi_rand_manager[i].reset();
      @(posedge rst_n);
      axi_rand_manager[i].run(TbNumReads, TbNumWrites);
      end_of_sim[i] <= 1'b1;
    end
  end

  axi_rand_subordinate_t axi_rand_subordinate [TbNumSubordinates];
  for (genvar i = 0; i < TbNumSubordinates; i++) begin : gen_rand_subordinate
    initial begin
      axi_rand_subordinate[i] = new( subordinate_dv[i] );
      axi_rand_subordinate[i].reset();
      @(posedge rst_n);
      axi_rand_subordinate[i].run();
    end
  end

  initial begin : proc_monitor
    static tb_axi_xbar_pkg::axi_xbar_monitor #(
      .AddrWidth      ( TbAddrWidth           ),
      .DataWidth      ( TbDataWidth           ),
      .IdWidthManagers ( TbIdWidthManagers      ),
      .IdWidthSubordinates  ( TbIdWidthSubordinates       ),
      .UserWidth      ( TbUserWidth           ),
      .NumManagers     ( TbNumManagers          ),
      .NumSubordinates      ( TbNumSubordinates           ),
      .NumAddrRules   ( xbar_cfg.NumAddrRules ),
      .rule_t         ( rule_t                ),
      .AddrMap        ( AddrMap               ),
      .TimeTest       ( TestTime              )
    ) monitor = new( manager_monitor_dv, subordinate_monitor_dv );
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
  axi_xbar_intf #(
    .AXI_USER_WIDTH ( TbUserWidth  ),
    .Cfg            ( xbar_cfg     ),
    .rule_t         ( rule_t       )
  ) i_xbar_dut (
    .clk_i                  ( clk     ),
    .rst_ni                 ( rst_n   ),
    .test_i                 ( 1'b0    ),
    .sbr_ports              ( manager  ),
    .mgr_ports              ( subordinate   ),
    .addr_map_i             ( AddrMap ),
    .en_default_mgr_port_i  ( '0      ),
    .default_mgr_port_i     ( '0      )
  );

  // logger for manager modules
  for (genvar i = 0; i < TbNumManagers; i++) begin : gen_manager_logger
    axi_chan_logger #(
      .TestTime  ( TestTime      ), // Time after clock, where sampling happens
      .LoggerName( $sformatf("axi_logger_manager_%0d", i)),
      .aw_chan_t ( aw_chan_mgr_t ), // axi AW type
      .w_chan_t  (  w_chan_t     ), // axi  W type
      .b_chan_t  (  b_chan_mgr_t ), // axi  B type
      .ar_chan_t ( ar_chan_mgr_t ), // axi AR type
      .r_chan_t  (  r_chan_mgr_t )  // axi  R type
    ) i_mgr_channel_logger (
      .clk_i      ( clk         ),    // Clock
      .rst_ni     ( rst_n       ),    // Asynchronous reset active low, when `1'b0` no sampling
      .end_sim_i  ( &end_of_sim ),
      // AW channel
      .aw_chan_i  ( managers_req[i].aw       ),
      .aw_valid_i ( managers_req[i].aw_valid ),
      .aw_ready_i ( managers_rsp[i].aw_ready ),
      //  W channel
      .w_chan_i   ( managers_req[i].w        ),
      .w_valid_i  ( managers_req[i].w_valid  ),
      .w_ready_i  ( managers_rsp[i].w_ready  ),
      //  B channel
      .b_chan_i   ( managers_rsp[i].b        ),
      .b_valid_i  ( managers_rsp[i].b_valid  ),
      .b_ready_i  ( managers_req[i].b_ready  ),
      // AR channel
      .ar_chan_i  ( managers_req[i].ar       ),
      .ar_valid_i ( managers_req[i].ar_valid ),
      .ar_ready_i ( managers_rsp[i].ar_ready ),
      //  R channel
      .r_chan_i   ( managers_rsp[i].r        ),
      .r_valid_i  ( managers_rsp[i].r_valid  ),
      .r_ready_i  ( managers_req[i].r_ready  )
    );
  end
  // logger for subordinate modules
  for (genvar i = 0; i < TbNumSubordinates; i++) begin : gen_subordinate_logger
    axi_chan_logger #(
      .TestTime  ( TestTime      ), // Time after clock, where sampling happens
      .LoggerName( $sformatf("axi_logger_subordinate_%0d",i)),
      .aw_chan_t ( aw_chan_sbr_t ), // axi AW type
      .w_chan_t  (  w_chan_t     ), // axi  W type
      .b_chan_t  (  b_chan_sbr_t ), // axi  B type
      .ar_chan_t ( ar_chan_sbr_t ), // axi AR type
      .r_chan_t  (  r_chan_sbr_t )  // axi  R type
    ) i_sbr_channel_logger (
      .clk_i      ( clk         ),    // Clock
      .rst_ni     ( rst_n       ),    // Asynchronous reset active low, when `1'b0` no sampling
      .end_sim_i  ( &end_of_sim ),
      // AW channel
      .aw_chan_i  ( subordinates_req[i].aw       ),
      .aw_valid_i ( subordinates_req[i].aw_valid ),
      .aw_ready_i ( subordinates_rsp[i].aw_ready ),
      //  W channel
      .w_chan_i   ( subordinates_req[i].w        ),
      .w_valid_i  ( subordinates_req[i].w_valid  ),
      .w_ready_i  ( subordinates_rsp[i].w_ready  ),
      //  B channel
      .b_chan_i   ( subordinates_rsp[i].b        ),
      .b_valid_i  ( subordinates_rsp[i].b_valid  ),
      .b_ready_i  ( subordinates_req[i].b_ready  ),
      // AR channel
      .ar_chan_i  ( subordinates_req[i].ar       ),
      .ar_valid_i ( subordinates_req[i].ar_valid ),
      .ar_ready_i ( subordinates_rsp[i].ar_ready ),
      //  R channel
      .r_chan_i   ( subordinates_rsp[i].r        ),
      .r_valid_i  ( subordinates_rsp[i].r_valid  ),
      .r_ready_i  ( subordinates_req[i].r_ready  )
    );
  end


  for (genvar i = 0; i < TbNumManagers; i++) begin : gen_connect_manager_monitor
    assign manager_monitor_dv[i].aw_id     = manager[i].aw_id    ;
    assign manager_monitor_dv[i].aw_addr   = manager[i].aw_addr  ;
    assign manager_monitor_dv[i].aw_len    = manager[i].aw_len   ;
    assign manager_monitor_dv[i].aw_size   = manager[i].aw_size  ;
    assign manager_monitor_dv[i].aw_burst  = manager[i].aw_burst ;
    assign manager_monitor_dv[i].aw_lock   = manager[i].aw_lock  ;
    assign manager_monitor_dv[i].aw_cache  = manager[i].aw_cache ;
    assign manager_monitor_dv[i].aw_prot   = manager[i].aw_prot  ;
    assign manager_monitor_dv[i].aw_qos    = manager[i].aw_qos   ;
    assign manager_monitor_dv[i].aw_region = manager[i].aw_region;
    assign manager_monitor_dv[i].aw_atop   = manager[i].aw_atop  ;
    assign manager_monitor_dv[i].aw_user   = manager[i].aw_user  ;
    assign manager_monitor_dv[i].aw_valid  = manager[i].aw_valid ;
    assign manager_monitor_dv[i].aw_ready  = manager[i].aw_ready ;
    assign manager_monitor_dv[i].w_data    = manager[i].w_data   ;
    assign manager_monitor_dv[i].w_strb    = manager[i].w_strb   ;
    assign manager_monitor_dv[i].w_last    = manager[i].w_last   ;
    assign manager_monitor_dv[i].w_user    = manager[i].w_user   ;
    assign manager_monitor_dv[i].w_valid   = manager[i].w_valid  ;
    assign manager_monitor_dv[i].w_ready   = manager[i].w_ready  ;
    assign manager_monitor_dv[i].b_id      = manager[i].b_id     ;
    assign manager_monitor_dv[i].b_resp    = manager[i].b_resp   ;
    assign manager_monitor_dv[i].b_user    = manager[i].b_user   ;
    assign manager_monitor_dv[i].b_valid   = manager[i].b_valid  ;
    assign manager_monitor_dv[i].b_ready   = manager[i].b_ready  ;
    assign manager_monitor_dv[i].ar_id     = manager[i].ar_id    ;
    assign manager_monitor_dv[i].ar_addr   = manager[i].ar_addr  ;
    assign manager_monitor_dv[i].ar_len    = manager[i].ar_len   ;
    assign manager_monitor_dv[i].ar_size   = manager[i].ar_size  ;
    assign manager_monitor_dv[i].ar_burst  = manager[i].ar_burst ;
    assign manager_monitor_dv[i].ar_lock   = manager[i].ar_lock  ;
    assign manager_monitor_dv[i].ar_cache  = manager[i].ar_cache ;
    assign manager_monitor_dv[i].ar_prot   = manager[i].ar_prot  ;
    assign manager_monitor_dv[i].ar_qos    = manager[i].ar_qos   ;
    assign manager_monitor_dv[i].ar_region = manager[i].ar_region;
    assign manager_monitor_dv[i].ar_user   = manager[i].ar_user  ;
    assign manager_monitor_dv[i].ar_valid  = manager[i].ar_valid ;
    assign manager_monitor_dv[i].ar_ready  = manager[i].ar_ready ;
    assign manager_monitor_dv[i].r_id      = manager[i].r_id     ;
    assign manager_monitor_dv[i].r_data    = manager[i].r_data   ;
    assign manager_monitor_dv[i].r_resp    = manager[i].r_resp   ;
    assign manager_monitor_dv[i].r_last    = manager[i].r_last   ;
    assign manager_monitor_dv[i].r_user    = manager[i].r_user   ;
    assign manager_monitor_dv[i].r_valid   = manager[i].r_valid  ;
    assign manager_monitor_dv[i].r_ready   = manager[i].r_ready  ;
  end
  for (genvar i = 0; i < TbNumSubordinates; i++) begin : gen_connect_subordinate_monitor
    assign subordinate_monitor_dv[i].aw_id     = subordinate[i].aw_id    ;
    assign subordinate_monitor_dv[i].aw_addr   = subordinate[i].aw_addr  ;
    assign subordinate_monitor_dv[i].aw_len    = subordinate[i].aw_len   ;
    assign subordinate_monitor_dv[i].aw_size   = subordinate[i].aw_size  ;
    assign subordinate_monitor_dv[i].aw_burst  = subordinate[i].aw_burst ;
    assign subordinate_monitor_dv[i].aw_lock   = subordinate[i].aw_lock  ;
    assign subordinate_monitor_dv[i].aw_cache  = subordinate[i].aw_cache ;
    assign subordinate_monitor_dv[i].aw_prot   = subordinate[i].aw_prot  ;
    assign subordinate_monitor_dv[i].aw_qos    = subordinate[i].aw_qos   ;
    assign subordinate_monitor_dv[i].aw_region = subordinate[i].aw_region;
    assign subordinate_monitor_dv[i].aw_atop   = subordinate[i].aw_atop  ;
    assign subordinate_monitor_dv[i].aw_user   = subordinate[i].aw_user  ;
    assign subordinate_monitor_dv[i].aw_valid  = subordinate[i].aw_valid ;
    assign subordinate_monitor_dv[i].aw_ready  = subordinate[i].aw_ready ;
    assign subordinate_monitor_dv[i].w_data    = subordinate[i].w_data   ;
    assign subordinate_monitor_dv[i].w_strb    = subordinate[i].w_strb   ;
    assign subordinate_monitor_dv[i].w_last    = subordinate[i].w_last   ;
    assign subordinate_monitor_dv[i].w_user    = subordinate[i].w_user   ;
    assign subordinate_monitor_dv[i].w_valid   = subordinate[i].w_valid  ;
    assign subordinate_monitor_dv[i].w_ready   = subordinate[i].w_ready  ;
    assign subordinate_monitor_dv[i].b_id      = subordinate[i].b_id     ;
    assign subordinate_monitor_dv[i].b_resp    = subordinate[i].b_resp   ;
    assign subordinate_monitor_dv[i].b_user    = subordinate[i].b_user   ;
    assign subordinate_monitor_dv[i].b_valid   = subordinate[i].b_valid  ;
    assign subordinate_monitor_dv[i].b_ready   = subordinate[i].b_ready  ;
    assign subordinate_monitor_dv[i].ar_id     = subordinate[i].ar_id    ;
    assign subordinate_monitor_dv[i].ar_addr   = subordinate[i].ar_addr  ;
    assign subordinate_monitor_dv[i].ar_len    = subordinate[i].ar_len   ;
    assign subordinate_monitor_dv[i].ar_size   = subordinate[i].ar_size  ;
    assign subordinate_monitor_dv[i].ar_burst  = subordinate[i].ar_burst ;
    assign subordinate_monitor_dv[i].ar_lock   = subordinate[i].ar_lock  ;
    assign subordinate_monitor_dv[i].ar_cache  = subordinate[i].ar_cache ;
    assign subordinate_monitor_dv[i].ar_prot   = subordinate[i].ar_prot  ;
    assign subordinate_monitor_dv[i].ar_qos    = subordinate[i].ar_qos   ;
    assign subordinate_monitor_dv[i].ar_region = subordinate[i].ar_region;
    assign subordinate_monitor_dv[i].ar_user   = subordinate[i].ar_user  ;
    assign subordinate_monitor_dv[i].ar_valid  = subordinate[i].ar_valid ;
    assign subordinate_monitor_dv[i].ar_ready  = subordinate[i].ar_ready ;
    assign subordinate_monitor_dv[i].r_id      = subordinate[i].r_id     ;
    assign subordinate_monitor_dv[i].r_data    = subordinate[i].r_data   ;
    assign subordinate_monitor_dv[i].r_resp    = subordinate[i].r_resp   ;
    assign subordinate_monitor_dv[i].r_last    = subordinate[i].r_last   ;
    assign subordinate_monitor_dv[i].r_user    = subordinate[i].r_user   ;
    assign subordinate_monitor_dv[i].r_valid   = subordinate[i].r_valid  ;
    assign subordinate_monitor_dv[i].r_ready   = subordinate[i].r_ready  ;
  end
endmodule
