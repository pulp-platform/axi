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
// - Florian Zaruba <zarubaf@iis.ee.ethz.ch>
// - Andreas Kurth <akurth@iis.ee.ethz.ch>
// - Vikram Jain <jvikram@iis.ee.ethz.ch>

// Directed Random Verification Testbench for `axi_xp`:  The crosspoint is instantiated with
// a configurable number of random axi master and slave modules.  Each random master executes a 
// fixed number of writes and reads over the whole addess map.  All masters simultaneously issue
// transactions through the crosspoint, thereby saturating it.  A monitor, which snoops the 
// transactions of each master and slave port and models the crosspoint with a network of FIFOs, 
// checks whether each transaction follows the expected route.

`include "axi/typedef.svh"
`include "axi/assign.svh"

module tb_axi_xp #(
  // Testbench parameters
  parameter bit TbEnAtop = 1'b1,            // enable atomic operations (ATOPs)
  parameter bit TbEnExcl = 1'b0,            // enable exclusive accesses
  parameter bit TbUniqueIds = 1'b0,         // restrict to only unique IDs
  parameter int unsigned TbNumMst = 32'd4,  // how many AXI masters there are
  parameter int unsigned TbNumSlv = 32'd4   // how many AXI slaves there are
);
  // Random master no Transactions
  localparam int unsigned NoWrites = 80;   // How many writes per master
  localparam int unsigned NoReads  = 80;   // How many reads per master
  // timing parameters
  localparam time CyclTime = 10ns;
  localparam time ApplTime =  2ns;
  localparam time TestTime =  8ns;

  // DUT parameters
  localparam bit  ATOPs = TbEnAtop;
  localparam int unsigned NoSlvPorts = TbNumSlv;
  localparam int unsigned NoMstPorts = TbNumMst;
  localparam bit [NoSlvPorts-1:0][NoMstPorts-1:0] Connectivity = '1;
  localparam int unsigned AxiSlvPortMaxUniqIds = 32'd16;
  localparam int unsigned AxiSlvPortMaxTxnsPerId = 32'd128;
  localparam int unsigned AxiSlvPortMaxTxns = 32'd31;
  localparam int unsigned AxiMstPortMaxUniqIds = 32'd2;
  localparam int unsigned AxiMstPortMaxTxnsPerId = 32'd7;
  localparam int unsigned NoAddrRules = 32'd8;

  // axi configuration
  localparam int unsigned AxiIdWidthMasters =  4;
  localparam int unsigned AxiIdUsed         =  3; // Has to be <= AxiIdWidthMasters
  localparam int unsigned AxiIdWidthSlaves  =  AxiIdWidthMasters + $clog2(TbNumMst);
  localparam int unsigned AxiAddrWidth      =  32;    // Axi Address Width
  localparam int unsigned AxiDataWidth      =  64;    // Axi Data Width
  localparam int unsigned AxiStrbWidth      =  AxiDataWidth / 8;
  localparam int unsigned AxiUserWidth      =  5;
  localparam int unsigned AxiIdWidth        =  AxiIdWidthMasters;
  // in the bench can change this variables which are set here freely
  localparam axi_pkg::xbar_cfg_t xbar_cfg = '{
    NoSlvPorts:         TbNumSlv,
    NoMstPorts:         TbNumMst,
    MaxMstTrans:        AxiSlvPortMaxTxns,
    MaxSlvTrans:        AxiSlvPortMaxTxnsPerId,
    FallThrough:        1'b0,
    LatencyMode:        axi_pkg::CUT_ALL_AX,
    AxiIdWidthSlvPorts: AxiIdWidthMasters,
    AxiIdUsedSlvPorts:  AxiIdUsed,
    UniqueIds:          TbUniqueIds,
    AxiAddrWidth:       AxiAddrWidth,
    AxiDataWidth:       AxiDataWidth,
    NoAddrRules:        8
  };
  typedef logic [AxiIdWidthMasters-1:0] id_mst_t;
  typedef logic [AxiIdWidthSlaves-1:0]  id_slv_t;
  typedef logic [AxiAddrWidth-1:0]      addr_t;
  typedef axi_pkg::xbar_rule_32_t       rule_t; // Has to be the same width as axi addr
  typedef logic [AxiDataWidth-1:0]      data_t;
  typedef logic [AxiStrbWidth-1:0]      strb_t;
  typedef logic [AxiUserWidth-1:0]      user_t;

  `AXI_TYPEDEF_AW_CHAN_T(aw_chan_mst_t, addr_t, id_mst_t, user_t)
  `AXI_TYPEDEF_AW_CHAN_T(aw_chan_slv_t, addr_t, id_slv_t, user_t)
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

  localparam rule_t [xbar_cfg.NoAddrRules-1:0] AddrMap = '{
    '{idx: 32'd7 % TbNumSlv, start_addr: 32'h0001_0000, end_addr: 32'h0001_1000},
    '{idx: 32'd6 % TbNumSlv, start_addr: 32'h0000_9000, end_addr: 32'h0001_0000},
    '{idx: 32'd5 % TbNumSlv, start_addr: 32'h0000_8000, end_addr: 32'h0000_9000},
    '{idx: 32'd4 % TbNumSlv, start_addr: 32'h0000_7000, end_addr: 32'h0000_8000},
    '{idx: 32'd3 % TbNumSlv, start_addr: 32'h0000_6300, end_addr: 32'h0000_7000},
    '{idx: 32'd2 % TbNumSlv, start_addr: 32'h0000_4000, end_addr: 32'h0000_6300},
    '{idx: 32'd1 % TbNumSlv, start_addr: 32'h0000_3000, end_addr: 32'h0000_4000},
    '{idx: 32'd0 % TbNumSlv, start_addr: 32'h0000_0000, end_addr: 32'h0000_3000}
  };

  typedef axi_test::axi_rand_master #(
    // AXI interface parameters
    .AW ( AxiAddrWidth       ),
    .DW ( AxiDataWidth       ),
    .IW ( AxiIdWidthMasters  ),
    .UW ( AxiUserWidth       ),
    // Stimuli application and test time
    .TA ( ApplTime           ),
    .TT ( TestTime           ),
    // Maximum number of read and write transactions in flight
    .MAX_READ_TXNS  ( 20     ),
    .MAX_WRITE_TXNS ( 20     ),
    .AXI_EXCLS      ( TbEnExcl ),
    .AXI_ATOPS      ( TbEnAtop ),
    .UNIQUE_IDS     ( TbUniqueIds )
  ) axi_rand_master_t;
  typedef axi_test::axi_rand_slave #(
    // AXI interface parameters
    .AW ( AxiAddrWidth     ),
    .DW ( AxiDataWidth     ),
    .IW ( AxiIdWidthSlaves ),
    .UW ( AxiUserWidth     ),
    // Stimuli application and test time
    .TA ( ApplTime         ),
    .TT ( TestTime         )
  ) axi_rand_slave_t;

  // -------------
  // DUT signals
  // -------------
  logic clk;
  // DUT signals
  logic rst_n;
  logic [TbNumMst-1:0] end_of_sim;

  // master structs
  mst_req_t  [TbNumMst-1:0] masters_req;
  mst_resp_t [TbNumMst-1:0] masters_resp;

  // slave structs
  slv_req_t  [TbNumSlv-1:0] slaves_req;
  slv_resp_t [TbNumSlv-1:0] slaves_resp;

  // -------------------------------
  // AXI Interfaces
  // -------------------------------
  AXI_BUS #(
    .AXI_ADDR_WIDTH ( AxiAddrWidth      ),
    .AXI_DATA_WIDTH ( AxiDataWidth      ),
    .AXI_ID_WIDTH   ( AxiIdWidthMasters ),
    .AXI_USER_WIDTH ( AxiUserWidth      )
  ) master [TbNumMst-1:0] ();
  AXI_BUS_DV #(
    .AXI_ADDR_WIDTH ( AxiAddrWidth      ),
    .AXI_DATA_WIDTH ( AxiDataWidth      ),
    .AXI_ID_WIDTH   ( AxiIdWidthMasters ),
    .AXI_USER_WIDTH ( AxiUserWidth      )
  ) master_dv [TbNumMst-1:0] (clk);
  AXI_BUS_DV #(
    .AXI_ADDR_WIDTH ( AxiAddrWidth      ),
    .AXI_DATA_WIDTH ( AxiDataWidth      ),
    .AXI_ID_WIDTH   ( AxiIdWidthMasters ),
    .AXI_USER_WIDTH ( AxiUserWidth      )
  ) master_monitor_dv [TbNumMst-1:0] (clk);
  for (genvar i = 0; i < TbNumMst; i++) begin : gen_conn_dv_masters
    `AXI_ASSIGN (master[i], master_dv[i])
    `AXI_ASSIGN_TO_REQ(masters_req[i], master[i])
    `AXI_ASSIGN_TO_RESP(masters_resp[i], master[i])
  end

  AXI_BUS #(
    .AXI_ADDR_WIDTH ( AxiAddrWidth     ),
    .AXI_DATA_WIDTH ( AxiDataWidth     ),
    .AXI_ID_WIDTH   ( AxiIdWidthSlaves ),
    .AXI_USER_WIDTH ( AxiUserWidth     )
  ) slave [TbNumSlv-1:0] ();
  AXI_BUS_DV #(
    .AXI_ADDR_WIDTH ( AxiAddrWidth     ),
    .AXI_DATA_WIDTH ( AxiDataWidth     ),
    .AXI_ID_WIDTH   ( AxiIdWidthSlaves ),
    .AXI_USER_WIDTH ( AxiUserWidth     )
  ) slave_dv [TbNumSlv-1:0](clk);
  AXI_BUS_DV #(
    .AXI_ADDR_WIDTH ( AxiAddrWidth     ),
    .AXI_DATA_WIDTH ( AxiDataWidth     ),
    .AXI_ID_WIDTH   ( AxiIdWidthSlaves ),
    .AXI_USER_WIDTH ( AxiUserWidth     )
  ) slave_monitor_dv [TbNumSlv-1:0](clk);
  for (genvar i = 0; i < TbNumSlv; i++) begin : gen_conn_dv_slaves
    `AXI_ASSIGN(slave_dv[i], slave[i])
    `AXI_ASSIGN_TO_REQ(slaves_req[i], slave[i])
    `AXI_ASSIGN_TO_RESP(slaves_resp[i], slave[i])
  end
  // -------------------------------
  // AXI Rand Masters and Slaves
  // -------------------------------
  // Masters control simulation run time
  axi_rand_master_t axi_rand_master [TbNumMst];
  for (genvar i = 0; i < TbNumMst; i++) begin : gen_rand_master
    initial begin
      axi_rand_master[i] = new( master_dv[i] );
      end_of_sim[i] <= 1'b0;
      axi_rand_master[i].add_memory_region(AddrMap[0].start_addr,
                                      AddrMap[xbar_cfg.NoAddrRules-1].end_addr,
                                      axi_pkg::DEVICE_NONBUFFERABLE);
      axi_rand_master[i].reset();
      @(posedge rst_n);
      axi_rand_master[i].run(NoReads, NoWrites);
      end_of_sim[i] <= 1'b1;
    end
  end

  axi_rand_slave_t axi_rand_slave [TbNumSlv];
  for (genvar i = 0; i < TbNumSlv; i++) begin : gen_rand_slave
    initial begin
      axi_rand_slave[i] = new( slave_dv[i] );
      axi_rand_slave[i].reset();
      @(posedge rst_n);
      axi_rand_slave[i].run();
    end
  end

  initial begin : proc_monitor
    static tb_axi_xp_pkg::axi_xp_monitor #(
      .AxiAddrWidth      ( AxiAddrWidth         ),
      .AxiDataWidth      ( AxiDataWidth         ),
      .AxiIdWidthMasters ( AxiIdWidthMasters    ),
      .AxiIdWidthSlaves  ( AxiIdWidthSlaves     ),
      .AxiUserWidth      ( AxiUserWidth         ),
      .NoMasters         ( TbNumMst            ),
      .NoSlaves          ( TbNumSlv             ),
      .NoAddrRules       ( xbar_cfg.NoAddrRules ),
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
  axi_xp_intf #(
    .ATOPs                   ( ATOPs         ),
    .Cfg                     ( xbar_cfg      ),
    .NoSlvPorts              ( xbar_cfg.NoSlvPorts    ),
    .NoMstPorts              ( xbar_cfg.NoMstPorts    ),
    .Connectivity            ( Connectivity  ),
    .AxiAddrWidth            ( AxiAddrWidth  ),
    .AxiDataWidth            ( AxiDataWidth  ),
    .AxiIdWidth              ( AxiIdWidth    ),
    .AxiUserWidth            ( AxiUserWidth  ),
    .AxiSlvPortMaxUniqIds    ( AxiSlvPortMaxUniqIds   ),
    .AxiSlvPortMaxTxnsPerId  ( AxiSlvPortMaxTxnsPerId ),
    .AxiSlvPortMaxTxns       ( AxiSlvPortMaxTxns      ),
    .AxiMstPortMaxUniqIds    ( AxiMstPortMaxUniqIds   ),
    .AxiMstPortMaxTxnsPerId  ( AxiMstPortMaxTxnsPerId ),
    .NoAddrRules             ( xbar_cfg.NoAddrRules   ),
    .rule_t                  ( rule_t                 )
  ) i_xp_dut (
    .clk_i                  ( clk     ),
    .rst_ni                 ( rst_n   ),
    .test_en_i              ( 1'b0    ),
    .slv_ports              ( master  ),
    .mst_ports              ( slave   ),
    .addr_map_i             ( AddrMap )
  );

  // logger for master modules
  for (genvar i = 0; i < TbNumMst; i++) begin : gen_master_logger
    axi_chan_logger #(
      .TestTime  ( TestTime      ), // Time after clock, where sampling happens
      .LoggerName( $sformatf("axi_logger_master_%0d", i)),
      .aw_chan_t ( aw_chan_mst_t ), // axi AW type
      .w_chan_t  (  w_chan_t     ), // axi  W type
      .b_chan_t  (  b_chan_mst_t ), // axi  B type
      .ar_chan_t ( ar_chan_mst_t ), // axi AR type
      .r_chan_t  (  r_chan_mst_t )  // axi  R type
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
  for (genvar i = 0; i < TbNumSlv; i++) begin : gen_slave_logger
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


  for (genvar i = 0; i < TbNumMst; i++) begin : gen_connect_master_monitor
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
  for (genvar i = 0; i < TbNumSlv; i++) begin : gen_connect_slave_monitor
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
