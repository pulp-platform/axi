`include "axi/typedef.svh"
`include "axi/assign.svh"
`ifndef TARGET_NETLIST_SIM
  `define XBAR i_xbar_dut
`else
  `define XBAR i_xbar_dut.i_dut
`endif

module tb_axi_xbar_zoix #(
  /// Number of AXI masters connected to the xbar. (Number of slave ports)
  parameter int unsigned TbNumMasters        = 32'd10,//32'd10,
  /// Number of AXI slaves connected to the xbar. (Number of master ports)
  parameter int unsigned TbNumSlaves         = 32'd10,//32'd10,
  /// Number of write transactions per master.
  parameter int unsigned TbNumWrites         = 32'd20,//32'd200,
  /// Number of read transactions per master.
  parameter int unsigned TbNumReads          = 32'd20,//32'd200,
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
  parameter bit          TbEnAtop            = 1'b0,
  /// Enable exclusive accesses
  parameter bit          TbEnExcl            = 1'b0,
  /// Restrict to only unique IDs
  parameter bit          TbUniqueIds         = 1'b0
);

  // TB timing parameters
  localparam time CyclTime = 10ns;
  localparam time ApplTime =  2ns;
  localparam time TestTime =  8ns;

  // AXI configuration which is automatically derived.
  localparam int unsigned TbAxiIdWidthSlaves = TbAxiIdWidthMasters + $clog2(TbNumMasters);
  localparam int unsigned TbAxiAddrWidth     = 32'd32;
  localparam int unsigned TbAxiStrbWidth     = TbAxiDataWidth / 8;
  localparam int unsigned TbAxiUserWidth     = 5;

  localparam axi_pkg::xbar_cfg_t xbar_cfg = '{
    NoSlvPorts:         TbNumMasters,
    NoMstPorts:         TbNumSlaves,
    MaxMstTrans:        10,
    MaxSlvTrans:        6,
    FallThrough:        1'b0,
    LatencyMode:        axi_pkg::CUT_ALL_AX,
    PipelineStages:     TbPipeline,
    AxiIdWidthSlvPorts: TbAxiIdWidthMasters,
    AxiIdUsedSlvPorts:  TbAxiIdUsed,
    UniqueIds:          TbUniqueIds,
    AxiAddrWidth:       TbAxiAddrWidth,
    AxiDataWidth:       TbAxiDataWidth,
    NoAddrRules:        TbNumSlaves
  };

  typedef logic [TbAxiIdWidthMasters-1:0] id_mst_t;
  typedef logic [TbAxiIdWidthSlaves-1:0]  id_slv_t;
  typedef logic [TbAxiIdWidthSlaves-1:0]  id_mst_rel_t;    // relAXI manager side, zero-extended
  typedef logic [TbAxiAddrWidth-1:0]      addr_t;
  typedef axi_pkg::xbar_rule_32_t         rule_t;
  typedef logic [TbAxiDataWidth-1:0]      data_t;
  typedef logic [TbAxiStrbWidth-1:0]      strb_t;
  typedef logic [TbAxiUserWidth-1:0]      user_t;

  // Plain AXI typedefs, used for flat signals and Z01X strobes
  `AXI_TYPEDEF_AW_CHAN_T(aw_chan_mst_plain_t, addr_t, id_mst_t, user_t)
  `AXI_TYPEDEF_AW_CHAN_T(aw_chan_slv_plain_t, addr_t, id_slv_t, user_t)
  `AXI_TYPEDEF_W_CHAN_T(w_chan_plain_t, data_t, strb_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T(b_chan_mst_plain_t, id_mst_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T(b_chan_slv_plain_t, id_slv_t, user_t)
  `AXI_TYPEDEF_AR_CHAN_T(ar_chan_mst_plain_t, addr_t, id_mst_t, user_t)
  `AXI_TYPEDEF_AR_CHAN_T(ar_chan_slv_plain_t, addr_t, id_slv_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(r_chan_mst_plain_t, data_t, id_mst_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(r_chan_slv_plain_t, data_t, id_slv_t, user_t)
  `AXI_TYPEDEF_REQ_T(mst_req_plain_t, aw_chan_mst_plain_t, w_chan_plain_t, ar_chan_mst_plain_t)
  `AXI_TYPEDEF_RESP_T(mst_resp_plain_t, b_chan_mst_plain_t, r_chan_mst_plain_t)
  `AXI_TYPEDEF_REQ_T(slv_req_plain_t, aw_chan_slv_plain_t, w_chan_plain_t, ar_chan_slv_plain_t)
  `AXI_TYPEDEF_RESP_T(slv_resp_plain_t, b_chan_slv_plain_t, r_chan_slv_plain_t)

  // Relaxi typedefs, used for DUT ports
  `RELAXI_TYPEDEF_AW_CHAN_T(aw_chan_mst_t, addr_t, id_mst_rel_t, user_t)
  `RELAXI_TYPEDEF_AW_CHAN_T(aw_chan_slv_t, addr_t, id_slv_t, user_t)
  `RELAXI_TYPEDEF_W_CHAN_T(w_chan_t, data_t, strb_t, user_t)
  `RELAXI_TYPEDEF_B_CHAN_T(b_chan_mst_t, id_mst_rel_t, user_t)
  `RELAXI_TYPEDEF_B_CHAN_T(b_chan_slv_t, id_slv_t, user_t)
  `RELAXI_TYPEDEF_AR_CHAN_T(ar_chan_mst_t, addr_t, id_mst_rel_t, user_t)
  `RELAXI_TYPEDEF_AR_CHAN_T(ar_chan_slv_t, addr_t, id_slv_t, user_t)
  `RELAXI_TYPEDEF_R_CHAN_T(r_chan_mst_t, data_t, id_mst_rel_t, user_t)
  `RELAXI_TYPEDEF_R_CHAN_T(r_chan_slv_t, data_t, id_slv_t, user_t)
  `RELAXI_TYPEDEF_REQ_T(mst_req_t, aw_chan_mst_t, w_chan_t, ar_chan_mst_t)
  `RELAXI_TYPEDEF_RESP_T(mst_resp_t, b_chan_mst_t, r_chan_mst_t)
  `RELAXI_TYPEDEF_REQ_T(slv_req_t, aw_chan_slv_t, w_chan_t, ar_chan_slv_t)
  `RELAXI_TYPEDEF_RESP_T(slv_resp_t, b_chan_slv_t, r_chan_slv_t)

  // Address map
  localparam rule_t [xbar_cfg.NoAddrRules-1:0] AddrMap = addr_map_gen();

  function rule_t [xbar_cfg.NoAddrRules-1:0] addr_map_gen();
    for (int unsigned i = 0; i < xbar_cfg.NoAddrRules; i++) begin
      addr_map_gen[i] = rule_t'{
        idx:        unsigned'(i),
        start_addr:  i    * 32'h0000_2000,
        end_addr:   (i+1) * 32'h0000_2000,
        default:    '0
      };
    end
  endfunction

  typedef axi_test::axi_rand_master #(
    .AW             ( TbAxiAddrWidth      ),
    .DW             ( TbAxiDataWidth      ),
    .IW             ( TbAxiIdWidthMasters ),
    .UW             ( TbAxiUserWidth      ),
    .TA             ( ApplTime            ),
    .TT             ( TestTime            ),
    .MAX_READ_TXNS  ( 20                  ),
    .MAX_WRITE_TXNS ( 20                  ),
    .AXI_EXCLS      ( TbEnExcl            ),
    .AXI_ATOPS      ( TbEnAtop            ),
    .UNIQUE_IDS     ( TbUniqueIds         )
  ) axi_rand_master_t;

  typedef axi_test::axi_rand_slave #(
    .AW ( TbAxiAddrWidth     ),
    .DW ( TbAxiDataWidth     ),
    .IW ( TbAxiIdWidthSlaves ),
    .UW ( TbAxiUserWidth     ),
    .TA ( ApplTime           ),
    .TT ( TestTime           )
  ) axi_rand_slave_t;

  // -----------------------------------------------------------
  // DUT signals
  // -----------------------------------------------------------
  logic clk;
  logic rst_n;
  logic [TbNumMasters-1:0] end_of_sim;
  logic [1:0] xbar_fault;

  // Relaxi structs ? DUT ports
  mst_req_t  [TbNumMasters-1:0] masters_req;
  mst_resp_t [TbNumMasters-1:0] masters_resp;
  slv_req_t  [TbNumSlaves-1:0]  slaves_req;
  slv_resp_t [TbNumSlaves-1:0]  slaves_resp;

  // Plain AXI structs ? for flat signals and Z01X strobes
  // Tapped from master[i]/slave[i] interfaces (decoded side)
  mst_req_plain_t  [TbNumMasters-1:0] masters_req_plain;
  mst_resp_plain_t [TbNumMasters-1:0] masters_resp_plain;
  slv_req_plain_t  [TbNumSlaves-1:0]  slaves_req_plain;
  slv_resp_plain_t [TbNumSlaves-1:0]  slaves_resp_plain;

  // -----------------------------------------------------------
  // AXI Interfaces (plain AXI ? between rand masters/slaves and encoder/decoder)
  // -----------------------------------------------------------
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

  // --- ADDED FOR MONITOR LOGGING ---
  AXI_BUS_DV #(
    .AXI_ADDR_WIDTH ( TbAxiAddrWidth      ),
    .AXI_DATA_WIDTH ( TbAxiDataWidth      ),
    .AXI_ID_WIDTH   ( TbAxiIdWidthMasters ),
    .AXI_USER_WIDTH ( TbAxiUserWidth      )
  ) master_monitor_dv [TbNumMasters-1:0] (clk);

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
  ) slave_dv [TbNumSlaves-1:0] (clk);

  // --- ADDED FOR MONITOR LOGGING ---
  AXI_BUS_DV #(
    .AXI_ADDR_WIDTH ( TbAxiAddrWidth     ),
    .AXI_DATA_WIDTH ( TbAxiDataWidth     ),
    .AXI_ID_WIDTH   ( TbAxiIdWidthSlaves ),
    .AXI_USER_WIDTH ( TbAxiUserWidth     )
  ) slave_monitor_dv [TbNumSlaves-1:0](clk);

  logic [TbNumMasters-1:0][1:0] enc_fault;
  logic [TbNumSlaves-1:0][1:0]  dec_fault;
  logic corrected_fault;
  logic uncorrectable_fault;
  // -----------------------------------------------------------
  // Master side: rand_master ? master_dv ? master ? encoder ? relaxi DUT
  // -----------------------------------------------------------
  for (genvar i = 0; i < TbNumMasters; i++) begin : gen_conn_dv_masters
    `AXI_ASSIGN(master[i], master_dv[i])

    relaxi_encoder #(
      .AxiAddrWidth ( TbAxiAddrWidth      ),
      .AxiDataWidth ( TbAxiDataWidth      ),
      .AxiIdWidth   ( TbAxiIdWidthMasters ),
      .RelIdWidth   ( TbAxiIdWidthSlaves  ),
      .AxiUserWidth ( TbAxiUserWidth      )
    ) i_master_enc (
      .aw_valid_i  ( master[i].aw_valid  ),
      .aw_id_i     ( master[i].aw_id     ),
      .aw_addr_i   ( master[i].aw_addr   ),
      .aw_len_i    ( master[i].aw_len    ),
      .aw_size_i   ( master[i].aw_size   ),
      .aw_burst_i  ( master[i].aw_burst  ),
      .aw_lock_i   ( master[i].aw_lock   ),
      .aw_cache_i  ( master[i].aw_cache  ),
      .aw_prot_i   ( master[i].aw_prot   ),
      .aw_qos_i    ( master[i].aw_qos    ),
      .aw_region_i ( master[i].aw_region ),
      .aw_atop_i   ( master[i].aw_atop   ),
      .aw_user_i   ( master[i].aw_user   ),
      .aw_ready_o  ( master[i].aw_ready  ),

      .w_valid_i   ( master[i].w_valid   ),
      .w_data_i    ( master[i].w_data    ),
      .w_strb_i    ( master[i].w_strb    ),
      .w_last_i    ( master[i].w_last    ),
      .w_user_i    ( master[i].w_user    ),
      .w_ready_o   ( master[i].w_ready   ),

      .b_valid_o   ( master[i].b_valid   ),
      .b_id_o      ( master[i].b_id      ),
      .b_resp_o    ( master[i].b_resp    ),
      .b_user_o    ( master[i].b_user    ),
      .b_ready_i   ( master[i].b_ready   ),

      .ar_valid_i  ( master[i].ar_valid  ),
      .ar_id_i     ( master[i].ar_id     ),
      .ar_addr_i   ( master[i].ar_addr   ),
      .ar_len_i    ( master[i].ar_len    ),
      .ar_size_i   ( master[i].ar_size   ),
      .ar_burst_i  ( master[i].ar_burst  ),
      .ar_lock_i   ( master[i].ar_lock   ),
      .ar_cache_i  ( master[i].ar_cache  ),
      .ar_prot_i   ( master[i].ar_prot   ),
      .ar_qos_i    ( master[i].ar_qos    ),
      .ar_region_i ( master[i].ar_region ),
      .ar_user_i   ( master[i].ar_user   ),
      .ar_ready_o  ( master[i].ar_ready  ),

      .r_valid_o   ( master[i].r_valid   ),
      .r_id_o      ( master[i].r_id      ),
      .r_data_o    ( master[i].r_data    ),
      .r_resp_o    ( master[i].r_resp    ),
      .r_last_o    ( master[i].r_last    ),
      .r_user_o    ( master[i].r_user    ),
      .r_ready_i   ( master[i].r_ready   ),

      .rel_aw_valid_o     ( masters_req[i].aw_valid         ),
      .rel_aw_id_o        ( masters_req[i].aw.id            ),
      .rel_aw_id_ecc_o    ( masters_req[i].aw.id_ecc        ),
      .rel_aw_addr_o      ( masters_req[i].aw.addr          ),
      .rel_aw_len_o       ( masters_req[i].aw.len           ),
      .rel_aw_size_o      ( masters_req[i].aw.size          ),
      .rel_aw_burst_o     ( masters_req[i].aw.burst         ),
      .rel_aw_lock_o      ( masters_req[i].aw.lock          ),
      .rel_aw_cache_o     ( masters_req[i].aw.cache         ),
      .rel_aw_prot_o      ( masters_req[i].aw.prot          ),
      .rel_aw_qos_o       ( masters_req[i].aw.qos           ),
      .rel_aw_region_o    ( masters_req[i].aw.region        ),
      .rel_aw_atop_o      ( masters_req[i].aw.atop          ),
      .rel_aw_user_o      ( masters_req[i].aw.user          ),
      .rel_aw_other_ecc_o ( masters_req[i].aw.aw_other_ecc ),
      .rel_aw_ready_i     ( masters_resp[i].aw_ready        ),

      .rel_w_valid_o      ( masters_req[i].w_valid          ),
      .rel_w_data_o       ( masters_req[i].w.data           ),
      .rel_w_strb_o       ( masters_req[i].w.strb           ),
      .rel_w_last_o       ( masters_req[i].w.last           ),
      .rel_w_user_o       ( masters_req[i].w.user           ),
      .rel_w_other_ecc_o  ( masters_req[i].w.w_other_ecc   ),
      .rel_w_ready_i      ( masters_resp[i].w_ready         ),

      .rel_b_valid_i      ( masters_resp[i].b_valid         ),
      .rel_b_id_i         ( masters_resp[i].b.id            ),
      .rel_b_id_ecc_i     ( masters_resp[i].b.id_ecc        ),
      .rel_b_resp_i       ( masters_resp[i].b.resp          ),
      .rel_b_user_i       ( masters_resp[i].b.user          ),
      .rel_b_ecc_i        ( masters_resp[i].b.b_ecc         ),
      .rel_b_ready_o      ( masters_req[i].b_ready          ),

      .rel_ar_valid_o     ( masters_req[i].ar_valid         ),
      .rel_ar_id_o        ( masters_req[i].ar.id            ),
      .rel_ar_id_ecc_o    ( masters_req[i].ar.id_ecc        ),
      .rel_ar_addr_o      ( masters_req[i].ar.addr          ),
      .rel_ar_len_o       ( masters_req[i].ar.len           ),
      .rel_ar_size_o      ( masters_req[i].ar.size          ),
      .rel_ar_burst_o     ( masters_req[i].ar.burst         ),
      .rel_ar_lock_o      ( masters_req[i].ar.lock          ),
      .rel_ar_cache_o     ( masters_req[i].ar.cache         ),
      .rel_ar_prot_o      ( masters_req[i].ar.prot          ),
      .rel_ar_qos_o       ( masters_req[i].ar.qos           ),
      .rel_ar_region_o    ( masters_req[i].ar.region        ),
      .rel_ar_user_o      ( masters_req[i].ar.user          ),
      .rel_ar_other_ecc_o ( masters_req[i].ar.ar_other_ecc ),
      .rel_ar_ready_i     ( masters_resp[i].ar_ready        ),

      .rel_r_valid_i      ( masters_resp[i].r_valid         ),
      .rel_r_id_i         ( masters_resp[i].r.id            ),
      .rel_r_id_ecc_i     ( masters_resp[i].r.id_ecc        ),
      .rel_r_data_i       ( masters_resp[i].r.data          ),
      .rel_r_resp_i       ( masters_resp[i].r.resp          ),
      .rel_r_last_i       ( masters_resp[i].r.last          ),
      .rel_r_user_i       ( masters_resp[i].r.user          ),
      .rel_r_other_ecc_i  ( masters_resp[i].r.r_other_ecc   ),
      .rel_r_ready_o      ( masters_req[i].r_ready          ),

      .fault_o            ( enc_fault[i]                    )
    );

    // Tap plain AXI signals for flat structs and Z01X strobes
    `AXI_ASSIGN_TO_REQ(masters_req_plain[i], master[i])
    `AXI_ASSIGN_TO_RESP(masters_resp_plain[i], master[i])
  end

  // -----------------------------------------------------------
  // Slave side: relaxi DUT ? decoder ? slave ? slave_dv ? rand_slave
  // -----------------------------------------------------------
  for (genvar i = 0; i < TbNumSlaves; i++) begin : gen_conn_dv_slaves
    relaxi_decoder #(
      .AxiAddrWidth ( TbAxiAddrWidth     ),
      .AxiDataWidth ( TbAxiDataWidth     ),
      .AxiIdWidth   ( TbAxiIdWidthSlaves ),
      .RelIdWidth   ( TbAxiIdWidthSlaves  ),
      .AxiUserWidth ( TbAxiUserWidth     )
    ) i_slave_dec (
      .rel_aw_valid_i     ( slaves_req[i].aw_valid         ),
      .rel_aw_id_i        ( slaves_req[i].aw.id            ),
      .rel_aw_addr_i      ( slaves_req[i].aw.addr          ),
      .rel_aw_len_i       ( slaves_req[i].aw.len           ),
      .rel_aw_size_i      ( slaves_req[i].aw.size          ),
      .rel_aw_burst_i     ( slaves_req[i].aw.burst         ),
      .rel_aw_lock_i      ( slaves_req[i].aw.lock          ),
      .rel_aw_cache_i     ( slaves_req[i].aw.cache         ),
      .rel_aw_prot_i      ( slaves_req[i].aw.prot          ),
      .rel_aw_qos_i       ( slaves_req[i].aw.qos           ),
      .rel_aw_region_i    ( slaves_req[i].aw.region        ),
      .rel_aw_atop_i      ( slaves_req[i].aw.atop          ),
      .rel_aw_user_i      ( slaves_req[i].aw.user          ),
      .rel_aw_other_ecc_i ( slaves_req[i].aw.aw_other_ecc  ),
      .rel_aw_ready_o     ( slaves_resp[i].aw_ready        ),

      .rel_w_valid_i      ( slaves_req[i].w_valid          ),
      .rel_w_data_i       ( slaves_req[i].w.data           ),
      .rel_w_strb_i       ( slaves_req[i].w.strb           ),
      .rel_w_last_i       ( slaves_req[i].w.last           ),
      .rel_w_user_i       ( slaves_req[i].w.user           ),
      .rel_w_other_ecc_i  ( slaves_req[i].w.w_other_ecc   ),
      .rel_w_ready_o      ( slaves_resp[i].w_ready         ),

      .rel_b_valid_o      ( slaves_resp[i].b_valid         ),
      .rel_b_id_o         ( slaves_resp[i].b.id            ),
      .rel_b_resp_o       ( slaves_resp[i].b.resp          ),
      .rel_b_user_o       ( slaves_resp[i].b.user          ),
      .rel_b_ecc_o        ( slaves_resp[i].b.b_ecc         ),
      .rel_b_ready_i      ( slaves_req[i].b_ready          ),

      .rel_ar_valid_i     ( slaves_req[i].ar_valid         ),
      .rel_ar_id_i        ( slaves_req[i].ar.id            ),
      .rel_ar_addr_i      ( slaves_req[i].ar.addr          ),
      .rel_ar_len_i       ( slaves_req[i].ar.len           ),
      .rel_ar_size_i      ( slaves_req[i].ar.size          ),
      .rel_ar_burst_i     ( slaves_req[i].ar.burst         ),
      .rel_ar_lock_i      ( slaves_req[i].ar.lock          ),
      .rel_ar_cache_i     ( slaves_req[i].ar.cache         ),
      .rel_ar_prot_i      ( slaves_req[i].ar.prot          ),
      .rel_ar_qos_i       ( slaves_req[i].ar.qos           ),
      .rel_ar_region_i    ( slaves_req[i].ar.region        ),
      .rel_ar_user_i      ( slaves_req[i].ar.user          ),
      .rel_ar_other_ecc_i ( slaves_req[i].ar.ar_other_ecc ),
      .rel_ar_ready_o     ( slaves_resp[i].ar_ready        ),

      .rel_r_valid_o      ( slaves_resp[i].r_valid         ),
      .rel_r_id_o         ( slaves_resp[i].r.id            ),
      .rel_r_data_o       ( slaves_resp[i].r.data          ),
      .rel_r_resp_o       ( slaves_resp[i].r.resp          ),
      .rel_r_last_o       ( slaves_resp[i].r.last          ),
      .rel_r_user_o       ( slaves_resp[i].r.user          ),
      .rel_r_other_ecc_o  ( slaves_resp[i].r.r_other_ecc   ),
      .rel_r_ready_i      ( slaves_req[i].r_ready          ),

      .rel_aw_id_ecc_i    ( slaves_req[i].aw.id_ecc ),
      .rel_ar_id_ecc_i    ( slaves_req[i].ar.id_ecc ),
      .rel_b_id_ecc_o     ( slaves_resp[i].b.id_ecc ),
      .rel_r_id_ecc_o     ( slaves_resp[i].r.id_ecc ),

      .aw_valid_o  ( slave[i].aw_valid  ),
      .aw_id_o     ( slave[i].aw_id     ),
      .aw_addr_o   ( slave[i].aw_addr   ),
      .aw_len_o    ( slave[i].aw_len    ),
      .aw_size_o   ( slave[i].aw_size   ),
      .aw_burst_o  ( slave[i].aw_burst  ),
      .aw_lock_o   ( slave[i].aw_lock   ),
      .aw_cache_o  ( slave[i].aw_cache  ),
      .aw_prot_o   ( slave[i].aw_prot   ),
      .aw_qos_o    ( slave[i].aw_qos    ),
      .aw_region_o ( slave[i].aw_region ),
      .aw_atop_o   ( slave[i].aw_atop   ),
      .aw_user_o   ( slave[i].aw_user   ),
      .aw_ready_i  ( slave[i].aw_ready  ),

      .w_valid_o   ( slave[i].w_valid   ),
      .w_data_o    ( slave[i].w_data    ),
      .w_strb_o    ( slave[i].w_strb    ),
      .w_last_o    ( slave[i].w_last    ),
      .w_user_o    ( slave[i].w_user    ),
      .w_ready_i   ( slave[i].w_ready   ),

      .b_valid_i   ( slave[i].b_valid   ),
      .b_id_i      ( slave[i].b_id      ),
      .b_resp_i    ( slave[i].b_resp    ),
      .b_user_i    ( slave[i].b_user    ),
      .b_ready_o   ( slave[i].b_ready   ),

      .ar_valid_o  ( slave[i].ar_valid  ),
      .ar_id_o     ( slave[i].ar_id     ),
      .ar_addr_o   ( slave[i].ar_addr   ),
      .ar_len_o    ( slave[i].ar_len    ),
      .ar_size_o   ( slave[i].ar_size   ),
      .ar_burst_o  ( slave[i].ar_burst  ),
      .ar_lock_o   ( slave[i].ar_lock   ),
      .ar_cache_o  ( slave[i].ar_cache  ),
      .ar_prot_o   ( slave[i].ar_prot   ),
      .ar_qos_o    ( slave[i].ar_qos    ),
      .ar_region_o ( slave[i].ar_region ),
      .ar_user_o   ( slave[i].ar_user   ),
      .ar_ready_i  ( slave[i].ar_ready  ),

      .r_valid_i   ( slave[i].r_valid   ),
      .r_id_i      ( slave[i].r_id      ),
      .r_data_i    ( slave[i].r_data    ),
      .r_resp_i    ( slave[i].r_resp    ),
      .r_last_i    ( slave[i].r_last    ),
      .r_user_i    ( slave[i].r_user    ),
      .r_ready_o   ( slave[i].r_ready   ),



      .fault_o     ( dec_fault[i]        )
    );

    `AXI_ASSIGN(slave_dv[i], slave[i])

    // Tap plain AXI signals for flat structs and Z01X strobes
    `AXI_ASSIGN_TO_REQ(slaves_req_plain[i], slave[i])
    `AXI_ASSIGN_TO_RESP(slaves_resp_plain[i], slave[i])
  end

  // --- ADDED FOR MONITOR LOGGING ---
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

  // --- ADDED FOR MONITOR LOGGING ---
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

  // -----------------------------------------------------------
  // AXI Rand Masters and Slaves
  // -----------------------------------------------------------

  axi_rand_master_t axi_rand_master [TbNumMasters];
  for (genvar i = 0; i < TbNumMasters; i++) begin : gen_rand_master
    initial begin
      axi_rand_master[i] = new(master_dv[i]);
      end_of_sim[i] <= 1'b0;
      axi_rand_master[i].add_memory_region(
        AddrMap[0].start_addr,
        AddrMap[xbar_cfg.NoAddrRules-1].end_addr,
        axi_pkg::DEVICE_NONBUFFERABLE
      );
      axi_rand_master[i].reset();
      @(posedge rst_n);
      repeat(100) @(posedge clk); // wait 100 cycles after reset
      axi_rand_master[i].run(TbNumReads, TbNumWrites);
      end_of_sim[i] <= 1'b1;
    end
  end

  axi_rand_slave_t axi_rand_slave [TbNumSlaves];
  for (genvar i = 0; i < TbNumSlaves; i++) begin : gen_rand_slave
    initial begin
      axi_rand_slave[i] = new(slave_dv[i]);
      axi_rand_slave[i].reset();
      @(posedge rst_n);
      repeat(100) @(posedge clk); // wait for X to resolve
      axi_rand_slave[i].run();
    end
  end

  initial $display("[WIDTH] id_mst_rel=%0d aw_mst=%0d aw_slv=%0d",
                 $bits(id_mst_rel_t), $bits(aw_chan_mst_t), $bits(aw_chan_slv_t));

  initial $display("[WIDTH2] slv_req=%0d slv_resp=%0d mst_req=%0d mst_resp=%0d",
                 $bits(slv_req_t), $bits(slv_resp_t), $bits(mst_req_t), $bits(mst_resp_t));

  // --- MONITOR: module-scope handle so the strobe can observe its verdict
  tb_axi_xbar_pkg::axi_xbar_monitor #(
    .AxiAddrWidth      ( TbAxiAddrWidth       ),
    .AxiDataWidth      ( TbAxiDataWidth       ),
    .AxiIdWidthMasters ( TbAxiIdWidthMasters  ),
    .AxiIdWidthSlaves  ( TbAxiIdWidthSlaves   ),
    .AxiUserWidth      ( TbAxiUserWidth       ),
    .NoMasters         ( TbNumMasters         ),
    .NoSlaves          ( TbNumSlaves          ),
    .NoAddrRules       ( xbar_cfg.NoAddrRules ),
    .rule_t            ( rule_t               ),
    .AddrMap           ( AddrMap              ),
    .TimeTest          ( TestTime             )
  ) monitor;

  logic monitor_route_error;
  logic monitor_content_error;

  initial begin : proc_monitor
    monitor               = new( master_monitor_dv, slave_monitor_dv );
    monitor_route_error   = 1'b0;
    monitor_content_error = 1'b0;
    fork
      monitor.run();
      forever begin
        #TestTime;
        // These are correctly sticky: once the monitor asserts an error,
        // the global flag holds it at 1'b1 for the rest of the simulation.
        if (monitor.route_error)   monitor_route_error   = 1'b1;
        if (monitor.content_error) monitor_content_error = 1'b1;
        @(posedge clk);
      end
      do begin
        #TestTime;
        if (end_of_sim == '1) begin
          monitor.print_result();
          $finish();
        end
        @(posedge clk);
      end while (1'b1);
    join
  end

  // ECC/FAULT HEALTH: covers boundary codec (enc/dec) AND the whole xbar fabric
  //`ifndef FAULTSIM
    longint unsigned enc_corr_cnt, enc_unc_cnt, dec_corr_cnt, dec_unc_cnt;
    longint unsigned xbar_corr_cnt, xbar_unc_cnt;

    initial begin
      enc_corr_cnt = 0; enc_unc_cnt = 0; dec_corr_cnt = 0; dec_unc_cnt = 0;
      xbar_corr_cnt = 0; xbar_unc_cnt = 0;
      @(posedge rst_n);
      forever @(posedge clk) begin
        #(TestTime);
        for (int i = 0; i < TbNumMasters; i++) begin
          if (enc_fault[i][0]) enc_corr_cnt++;
          if (enc_fault[i][1]) enc_unc_cnt++;
        end
        for (int i = 0; i < TbNumSlaves; i++) begin
          if (dec_fault[i][0]) dec_corr_cnt++;
          if (dec_fault[i][1]) dec_unc_cnt++;
        end
        if (xbar_fault[0]) xbar_corr_cnt++;
        if (xbar_fault[1]) xbar_unc_cnt++;
      end
    end

    // X-CHECK: any undriven fault slot anywhere in the tree shows up as X here.
    // This is the strongest completeness test for the threading.
    always @(posedge clk) begin
      #(TestTime);
      if (rst_n === 1'b1) begin
        if (^xbar_fault === 1'bx)
          $fatal(1, "[FAULT-THREAD] xbar_fault is X at %0t -- an undriven fault slot exists in the xbar tree!", $time);
        for (int i = 0; i < TbNumMasters; i++)
          if (^enc_fault[i] === 1'bx)
            $fatal(1, "[FAULT-THREAD] enc_fault[%0d] is X at %0t", i, $time);
        for (int i = 0; i < TbNumSlaves; i++)
          if (^dec_fault[i] === 1'bx)
            $fatal(1, "[FAULT-THREAD] dec_fault[%0d] is X at %0t", i, $time);
      end
    end

    final begin
      $display("[ECC-HEALTH] enc corr=%0d unc=%0d | dec corr=%0d unc=%0d | xbar corr=%0d unc=%0d",
               enc_corr_cnt, enc_unc_cnt, dec_corr_cnt, dec_unc_cnt,
               xbar_corr_cnt, xbar_unc_cnt);
      if (enc_corr_cnt || enc_unc_cnt || dec_corr_cnt || dec_unc_cnt ||
          xbar_corr_cnt || xbar_unc_cnt)
        $display("[ECC-HEALTH] *** NONZERO IN GOLDEN -- protection is firing without injected faults ***");
    end
  //`endif

  `ifndef FAULTSIM
  // logger for master modules (Linked to _plain structs)
  for (genvar i = 0; i < TbNumMasters; i++) begin : gen_master_logger
    axi_chan_logger #(
      .TestTime  ( TestTime      ),
      .LoggerName( $sformatf("axi_logger_master_%0d", i)),
      .aw_chan_t ( aw_chan_mst_plain_t ),
      .w_chan_t  (  w_chan_plain_t     ),
      .b_chan_t  (  b_chan_mst_plain_t ),
      .ar_chan_t ( ar_chan_mst_plain_t ),
      .r_chan_t  (  r_chan_mst_plain_t )
    ) i_mst_channel_logger (
      .clk_i      ( clk         ),
      .rst_ni     ( rst_n       ),
      .end_sim_i  ( &end_of_sim ),
      .aw_chan_i  ( masters_req_plain[i].aw        ),
      .aw_valid_i ( masters_req_plain[i].aw_valid  ),
      .aw_ready_i ( masters_resp_plain[i].aw_ready ),
      .w_chan_i   ( masters_req_plain[i].w         ),
      .w_valid_i  ( masters_req_plain[i].w_valid   ),
      .w_ready_i  ( masters_resp_plain[i].w_ready  ),
      .b_chan_i   ( masters_resp_plain[i].b        ),
      .b_valid_i  ( masters_resp_plain[i].b_valid  ),
      .b_ready_i  ( masters_req_plain[i].b_ready   ),
      .ar_chan_i  ( masters_req_plain[i].ar        ),
      .ar_valid_i ( masters_req_plain[i].ar_valid  ),
      .ar_ready_i ( masters_resp_plain[i].ar_ready ),
      .r_chan_i   ( masters_resp_plain[i].r        ),
      .r_valid_i  ( masters_resp_plain[i].r_valid  ),
      .r_ready_i  ( masters_req_plain[i].r_ready   )
    );
  end
  `endif

  // --- ADDED FOR CHANNEL LOGGING ---
  // logger for slave modules (Linked to _plain structs)
  `ifndef FAULTSIM
  for (genvar i = 0; i < TbNumSlaves; i++) begin : gen_slave_logger
    axi_chan_logger #(
      .TestTime  ( TestTime      ),
      .LoggerName( $sformatf("axi_logger_slave_%0d",i)),
      .aw_chan_t ( aw_chan_slv_plain_t ),
      .w_chan_t  (  w_chan_plain_t     ),
      .b_chan_t  (  b_chan_slv_plain_t ),
      .ar_chan_t ( ar_chan_slv_plain_t ),
      .r_chan_t  (  r_chan_slv_plain_t )
    ) i_slv_channel_logger (
      .clk_i      ( clk         ),
      .rst_ni     ( rst_n       ),
      .end_sim_i  ( &end_of_sim ),
      .aw_chan_i  ( slaves_req_plain[i].aw        ),
      .aw_valid_i ( slaves_req_plain[i].aw_valid  ),
      .aw_ready_i ( slaves_resp_plain[i].aw_ready ),
      .w_chan_i   ( slaves_req_plain[i].w         ),
      .w_valid_i  ( slaves_req_plain[i].w_valid   ),
      .w_ready_i  ( slaves_resp_plain[i].w_ready  ),
      .b_chan_i   ( slaves_resp_plain[i].b        ),
      .b_valid_i  ( slaves_resp_plain[i].b_valid  ),
      .b_ready_i  ( slaves_req_plain[i].b_ready   ),
      .ar_chan_i  ( slaves_req_plain[i].ar        ),
      .ar_valid_i ( slaves_req_plain[i].ar_valid  ),
      .ar_ready_i ( slaves_resp_plain[i].ar_ready ),
      .r_chan_i   ( slaves_resp_plain[i].r        ),
      .r_valid_i  ( slaves_resp_plain[i].r_valid  ),
      .r_ready_i  ( slaves_req_plain[i].r_ready   )
    );
  end
  `endif
  // -----------------------------------------------------------
  // Simulation termination (Updated to let proc_monitor handle $stop)
  // -----------------------------------------------------------

  initial begin
    wait (&end_of_sim);
    $display("[END OF SIM] end_of_sim at cycle %0d, time %0t", $time/10, $time);
    repeat (1000) @(posedge clk);
    $finish();  // add this
  end

  initial begin
    #(10ns * 2_000_000); // 5M cycles watchdog
    $display("[POST-SYNTH] WATCHDOG timeout");
    $finish();
  end

  // -----------------------------------------------------------
  // Clock generator
  // -----------------------------------------------------------
  clk_rst_gen #(
    .ClkPeriod    ( CyclTime ),
    .RstClkCycles ( 200        ) //5
  ) i_clk_gen (
    .clk_o  (clk),
    .rst_no (rst_n)
  );

  // -----------------------------------------------------------
  // DUT
  // -----------------------------------------------------------

  relaxi_xbar_synth i_xbar_dut (
    .clk_i                 ( clk          ),
    .rst_ni                ( rst_n        ),
    .slv_req_i             ( masters_req  ),
    .slv_resp_o            ( masters_resp ),
    .mst_req_o             ( slaves_req   ),
    .mst_resp_i            ( slaves_resp  ),
    .addr_map_i            ( AddrMap      ),
    .en_default_mst_port_i ( '0           ),
    .default_mst_port_i    ( '0           ),
    .fault_o               ( xbar_fault             )
  );

  /*
  relaxi_xbar #(
    .Cfg           ( xbar_cfg       ),
    .ATOPs         ( TbEnAtop       ),
    .slv_aw_chan_t ( aw_chan_mst_t  ),
    .mst_aw_chan_t ( aw_chan_slv_t  ),
    .w_chan_t      ( w_chan_t       ),
    .slv_b_chan_t  ( b_chan_mst_t   ),
    .mst_b_chan_t  ( b_chan_slv_t   ),
    .slv_ar_chan_t ( ar_chan_mst_t  ),
    .mst_ar_chan_t ( ar_chan_slv_t  ),
    .slv_r_chan_t  ( r_chan_mst_t   ),
    .mst_r_chan_t  ( r_chan_slv_t   ),
    .slv_req_t     ( mst_req_t     ),
    .slv_resp_t    ( mst_resp_t    ),
    .mst_req_t     ( slv_req_t     ),
    .mst_resp_t    ( slv_resp_t    ),
    .rule_t        ( rule_t        )
  ) i_xbar_dut (
    .clk_i                 ( clk          ),
    .rst_ni                ( rst_n        ),
    .test_i                ( 1'b0         ),
    .slv_ports_req_i       ( masters_req  ),
    .slv_ports_resp_o      ( masters_resp ),
    .mst_ports_req_o       ( slaves_req   ),
    .mst_ports_resp_i      ( slaves_resp  ),
    .addr_map_i            ( AddrMap      ),
    .en_default_mst_port_i ( '0           ),
    .default_mst_port_i    ( '0           ),
    .fault_o               ( xbar_fault   )
  );
  */

  always_comb begin
    corrected_fault     = xbar_fault[0];
    uncorrectable_fault = xbar_fault[1];
    for (int i = 0; i < TbNumMasters; i++) begin
      corrected_fault     |= enc_fault[i][0];
      uncorrectable_fault |= enc_fault[i][1];
    end
    for (int i = 0; i < TbNumSlaves; i++) begin
      corrected_fault     |= dec_fault[i][0];
      uncorrectable_fault |= dec_fault[i][1];
    end
  end

  // -----------------------------------------------------------
  // Flat signals for $fs_compare ? tapped from plain AXI side
  // masters_resp_plain: what masters see back (decoded responses)
  // slaves_req_plain:   what slaves see (decoded requests)
  // -----------------------------------------------------------
  localparam int unsigned MstRespBits = $bits(mst_resp_plain_t);
  localparam int unsigned SlvReqBits  = $bits(slv_req_plain_t);

  logic [TbNumMasters-1:0][MstRespBits-1:0] masters_resp_flat;
  logic [TbNumSlaves-1:0][SlvReqBits-1:0]   slaves_req_flat;

  for (genvar i = 0; i < TbNumMasters; i++) begin : gen_masters_resp_flat
    assign masters_resp_flat[i] = masters_resp_plain[i];
  end
  for (genvar i = 0; i < TbNumSlaves; i++) begin : gen_slaves_req_flat
    assign slaves_req_flat[i] = slaves_req_plain[i];
  end

  // -----------------------------------------------------------
  // interface_error: misrouting checker
  // Uses decoded plain AXI addresses from slave[i] - correct width,
  // no ECC bits mixed in
  // -----------------------------------------------------------
  logic interface_error;
  logic [TbNumSlaves-1:0] mst_port_aw_error;
  logic [TbNumSlaves-1:0] mst_port_ar_error;

  always_comb begin
    for (int unsigned i = 0; i < TbNumSlaves; i++) begin
      automatic logic aw_addr_ok;
      automatic logic ar_addr_ok;
      // AW channel misrouting check
      aw_addr_ok = 1'b0;
      if (slaves_req_plain[i].aw_valid) begin
        for (int unsigned r = 0; r < xbar_cfg.NoAddrRules; r++) begin
          if (AddrMap[r].idx == i &&
              slaves_req_plain[i].aw.addr >= AddrMap[r].start_addr &&
              slaves_req_plain[i].aw.addr <  AddrMap[r].end_addr) begin
            aw_addr_ok = 1'b1;
          end
        end
        mst_port_aw_error[i] = ~aw_addr_ok;
      end else begin
        mst_port_aw_error[i] = 1'b0;
      end

      // AR channel misrouting check
      ar_addr_ok = 1'b0;
      if (slaves_req_plain[i].ar_valid) begin
        for (int unsigned r = 0; r < xbar_cfg.NoAddrRules; r++) begin
          if (AddrMap[r].idx == i &&
              slaves_req_plain[i].ar.addr >= AddrMap[r].start_addr &&
              slaves_req_plain[i].ar.addr <  AddrMap[r].end_addr) begin
            ar_addr_ok = 1'b1;
          end
        end
        mst_port_ar_error[i] = ~ar_addr_ok;
      end else begin
        mst_port_ar_error[i] = 1'b0;
      end
    end
  end

  assign interface_error = |mst_port_aw_error | |mst_port_ar_error;

  // Sticky version for the strobe: the combinational signal is only high while
  // a misrouted AW/AR is on the bus, so a single-cycle event could fall between
  // strobe sampling points.
  logic interface_error_sticky;
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n)               interface_error_sticky <= 1'b0;
    else if (interface_error) interface_error_sticky <= 1'b1;
  end

  // ============================================================================
  // ID-ROUTING CHECKER  (genvar-tapped, X-safe for fault injection)
  // ============================================================================
  localparam int unsigned IdSpace = (1 << TbAxiIdWidthMasters);
  localparam int unsigned OutCntW = 8;

  // Flat taps of the per-master interface signals (constant index via genvar)
  logic [TbNumMasters-1:0]                          m_aw_hs, m_ar_hs, m_b_hs, m_r_hs;
  logic [TbNumMasters-1:0]                          m_aw_hs_x, m_ar_hs_x, m_b_hs_x, m_r_hs_x;
  logic [TbNumMasters-1:0][TbAxiIdWidthMasters-1:0] m_aw_id, m_ar_id, m_b_id, m_r_id;
  logic [TbNumMasters-1:0][1:0]                     m_b_resp, m_r_resp;

  for (genvar gi = 0; gi < TbNumMasters; gi++) begin : gen_id_route_taps
    // X-safe handshake decode: an X on valid/ready must not silently read as 0
    assign m_aw_hs_x[gi] = $isunknown(master[gi].aw_valid & master[gi].aw_ready);
    assign m_ar_hs_x[gi] = $isunknown(master[gi].ar_valid & master[gi].ar_ready);
    assign m_b_hs_x [gi] = $isunknown(master[gi].b_valid  & master[gi].b_ready);
    assign m_r_hs_x [gi] = $isunknown(master[gi].r_valid  & master[gi].r_ready
                                                          & master[gi].r_last);

    assign m_aw_hs[gi] = m_aw_hs_x[gi] ? 1'b0 : (master[gi].aw_valid & master[gi].aw_ready);
    assign m_ar_hs[gi] = m_ar_hs_x[gi] ? 1'b0 : (master[gi].ar_valid & master[gi].ar_ready);
    assign m_b_hs [gi] = m_b_hs_x [gi] ? 1'b0 : (master[gi].b_valid  & master[gi].b_ready);
    assign m_r_hs [gi] = m_r_hs_x [gi] ? 1'b0 : (master[gi].r_valid  & master[gi].r_ready
                                                                     & master[gi].r_last);

    assign m_aw_id[gi] = master[gi].aw_id;
    assign m_ar_id[gi] = master[gi].ar_id;
    assign m_b_id [gi] = master[gi].b_id;
    assign m_r_id [gi] = master[gi].r_id;
    assign m_b_resp[gi] = master[gi].b_resp;
    assign m_r_resp[gi] = master[gi].r_resp;
  end

  // Outstanding-transaction scoreboard: [manager][id] -> count
  logic [OutCntW-1:0] aw_outstanding [TbNumMasters][IdSpace];
  logic [OutCntW-1:0] ar_outstanding [TbNumMasters][IdSpace];

  logic [TbNumMasters-1:0] b_misroute;
  logic [TbNumMasters-1:0] r_misroute;
  logic [TbNumMasters-1:0] aw_id_x;        // address-phase ID corruption (write)
  logic [TbNumMasters-1:0] ar_id_x;        // address-phase ID corruption (read)
  logic [TbNumMasters-1:0] hs_x;           // handshake went X
  logic                    id_route_error;
  logic                    addr_id_error;

  // Debug capture of the offending beat
  logic [TbAxiIdWidthMasters-1:0] b_bad_id [TbNumMasters];
  logic [TbAxiIdWidthMasters-1:0] r_bad_id [TbNumMasters];
  int unsigned                    sb_collisions;

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      for (int m = 0; m < TbNumMasters; m++) begin
        for (int k = 0; k < IdSpace; k++) begin
          aw_outstanding[m][k] <= '0;
          ar_outstanding[m][k] <= '0;
        end
        b_bad_id[m] <= '0;
        r_bad_id[m] <= '0;
      end
      b_misroute    <= '0;
      r_misroute    <= '0;
      aw_id_x       <= '0;
      ar_id_x       <= '0;
      hs_x          <= '0;
      sb_collisions <= 0;
    end else begin
      automatic int unsigned cycle_collisions = 0;

      b_misroute <= '0;
      r_misroute <= '0;
      aw_id_x    <= '0;
      ar_id_x    <= '0;
      hs_x       <= '0;

      for (int m = 0; m < TbNumMasters; m++) begin
        automatic logic aw_inc, ar_inc, b_dec, r_dec;
        aw_inc = 1'b0;  ar_inc = 1'b0;
        b_dec  = 1'b0;  r_dec  = 1'b0;

        // ---- handshake X (fault made valid/ready unknown) ----
        if (m_aw_hs_x[m] | m_ar_hs_x[m] | m_b_hs_x[m] | m_r_hs_x[m])
          hs_x[m] <= 1'b1;

        // ---- AW issue ----
        if (m_aw_hs[m]) begin
          if ($isunknown(m_aw_id[m])) begin
            aw_id_x[m] <= 1'b1;                    // address phase, NOT a B misroute
            $display("[%0t] AW ID X mgr=%0d", $time, m);
          end else begin
            aw_inc = 1'b1;
          end
        end

        // ---- AR issue ----
        if (m_ar_hs[m]) begin
          if ($isunknown(m_ar_id[m])) begin
            ar_id_x[m] <= 1'b1;
            $display("[%0t] AR ID X mgr=%0d", $time, m);
          end else begin
            ar_inc = 1'b1;
          end
        end

        // ---- B receive ----
        if (m_b_hs[m]) begin
          if ($isunknown(m_b_id[m])) begin
            b_misroute[m] <= 1'b1;
            $display("[%0t] B MISROUTE (X id) mgr=%0d", $time, m);
          end else if ((aw_outstanding[m][m_b_id[m]] == '0) &&
                       !(aw_inc && (m_aw_id[m] == m_b_id[m]))) begin
            b_misroute[m] <= 1'b1;
            b_bad_id[m]   <= m_b_id[m];
            $display("[%0t] B MISROUTE mgr=%0d b_id=0x%0h resp=%0d",
                     $time, m, m_b_id[m], m_b_resp[m]);
            for (int mm = 0; mm < TbNumMasters; mm++)
              if (aw_outstanding[mm][m_b_id[m]] != '0)
                $display("           owner mgr=%0d cnt=%0d",
                         mm, aw_outstanding[mm][m_b_id[m]]);
          end else begin
            b_dec = 1'b1;
          end
        end

        // ---- R receive (last beat) ----
        if (m_r_hs[m]) begin
          if ($isunknown(m_r_id[m])) begin
            r_misroute[m] <= 1'b1;
            $display("[%0t] R MISROUTE (X id) mgr=%0d", $time, m);
          end else if ((ar_outstanding[m][m_r_id[m]] == '0) &&
                       !(ar_inc && (m_ar_id[m] == m_r_id[m]))) begin
            r_misroute[m] <= 1'b1;
            r_bad_id[m]   <= m_r_id[m];
            $display("[%0t] R MISROUTE mgr=%0d r_id=0x%0h resp=%0d",
                     $time, m, m_r_id[m], m_r_resp[m]);
            for (int mm = 0; mm < TbNumMasters; mm++)
              if (ar_outstanding[mm][m_r_id[m]] != '0)
                $display("           owner mgr=%0d cnt=%0d",
                         mm, ar_outstanding[mm][m_r_id[m]]);
          end else begin
            r_dec = 1'b1;
          end
        end

        // ---- apply net delta: write path ----
        if (aw_inc && b_dec && (m_aw_id[m] == m_b_id[m])) begin
          cycle_collisions++;                      // net zero, leave counter alone
        end else begin
          if (aw_inc) aw_outstanding[m][m_aw_id[m]] <= aw_outstanding[m][m_aw_id[m]] + 1'b1;
          if (b_dec)  aw_outstanding[m][m_b_id[m]]  <= aw_outstanding[m][m_b_id[m]]  - 1'b1;
        end

        // ---- apply net delta: read path ----
        if (ar_inc && r_dec && (m_ar_id[m] == m_r_id[m])) begin
          cycle_collisions++;
        end else begin
          if (ar_inc) ar_outstanding[m][m_ar_id[m]] <= ar_outstanding[m][m_ar_id[m]] + 1'b1;
          if (r_dec)  ar_outstanding[m][m_r_id[m]]  <= ar_outstanding[m][m_r_id[m]]  - 1'b1;
        end
      end

      if (cycle_collisions > 0)
        sb_collisions <= sb_collisions + cycle_collisions;
    end
  end

  assign id_route_error = (|b_misroute) | (|r_misroute);
  assign addr_id_error  = (|aw_id_x)    | (|ar_id_x);

  logic id_route_error_sticky, addr_id_error_sticky, hs_x_sticky;
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      id_route_error_sticky <= 1'b0;
      addr_id_error_sticky  <= 1'b0;
      hs_x_sticky           <= 1'b0;
    end else begin
      if (id_route_error) id_route_error_sticky <= 1'b1;
      if (addr_id_error)  addr_id_error_sticky  <= 1'b1;
      if (|hs_x)          hs_x_sticky           <= 1'b1;
    end
  end

  logic [TbNumSlaves-1:0] mux_lock_div;
  for (genvar m = 0; m < TbNumSlaves; m++) begin : gen_mux_div
    logic [2:0] lk;
    //assign lk = `XBAR.gen_mst_port_mux[m].i_axi_mux.gen_mux.lock_aw_valid_next;
    `ifndef TARGET_NETLIST_SIM
        assign lk = `XBAR.gen_mst_port_mux[m].i_axi_mux.gen_mux.lock_aw_valid_next;
    `else
        assign lk = '0;
    `endif
    assign mux_lock_div[m] = (^lk === 1'bx) ? 1'b0
                           : ~((lk[0] == lk[1]) && (lk[1] == lk[2]));
  end

  logic [TbNumMasters-1:0] demux_lock_aw_div, demux_lock_ar_div, demux_wsel_div;
  for (genvar s = 0; s < TbNumMasters; s++) begin : gen_demux_div
    logic [2:0] la_, lr_;
    // assign la_ = `XBAR.i_xbar_unmuxed.gen_slv_port_demux[s].i_axi_demux
    //                .i_demux_simple.gen_demux.lock_aw_valid_next;
    // assign lr_ = `XBAR.i_xbar_unmuxed.gen_slv_port_demux[s].i_axi_demux
    //                .i_demux_simple.gen_demux.lock_ar_valid_next;

    `ifndef TARGET_NETLIST_SIM
        assign la_ = `XBAR.i_xbar_unmuxed.gen_slv_port_demux[s].i_axi_demux
                      .i_demux_simple.gen_demux.lock_aw_valid_next;
        assign lr_ = `XBAR.i_xbar_unmuxed.gen_slv_port_demux[s].i_axi_demux
                      .i_demux_simple.gen_demux.lock_ar_valid_next;
    `else
        assign la_ = '0;
        assign lr_ = '0;
    `endif
    assign demux_lock_aw_div[s] = (^la_ === 1'bx) ? 1'b0
                                : ~((la_[0] == la_[1]) && (la_[1] == la_[2]));
    assign demux_lock_ar_div[s] = (^lr_ === 1'bx) ? 1'b0
                                : ~((lr_[0] == lr_[1]) && (lr_[1] == lr_[2]));
  end

  logic [TbNumMasters-1:0] errslv_busy_div;
  for (genvar s = 0; s < TbNumMasters; s++) begin : gen_errslv_div
    logic [2:0] rb;
    //assign rb = `XBAR.i_xbar_unmuxed.gen_slv_port_demux[s].i_axi_err_slv.r_busy_q;
    `ifndef TARGET_NETLIST_SIM
      assign rb = `XBAR.i_xbar_unmuxed.gen_slv_port_demux[s].i_axi_err_slv.r_busy_q;
  `else
      assign rb = '0;
  `endif
    assign errslv_busy_div[s] = (^rb === 1'bx) ? 1'b0
                              : ~((rb[0] == rb[1]) && (rb[1] == rb[2]));
  end

  // relaxi_demux_simple: W-select register. FFLARN with w_cnt_up as enable,
  // voted on read, so a divergent replica persists until the next push.
  localparam int unsigned DemuxSelW = $clog2(TbNumSlaves + 1);
  for (genvar s = 0; s < TbNumMasters; s++) begin : gen_demux_wsel_div
    logic [2:0][DemuxSelW-1:0] ws;
    //assign ws = `XBAR.i_xbar_unmuxed.gen_slv_port_demux[s].i_axi_demux
    //              .i_demux_simple.gen_demux.w_select_next;

    `ifndef TARGET_NETLIST_SIM
        assign ws = `XBAR.i_xbar_unmuxed.gen_slv_port_demux[s].i_axi_demux
                      .i_demux_simple.gen_demux.w_select_next;
    `else
        assign ws = '0;
    `endif
    assign demux_wsel_div[s] = (^ws === 1'bx) ? 1'b0
                             : ~((ws[0] == ws[1]) && (ws[1] == ws[2]));
  end

  // relaxi_demux_id_counters: per-ID destination registers. FFLARN with
  // push_en as enable, read directly with no voter, so a divergent replica
  // persists until that ID is pushed again.
  logic [TbNumMasters-1:0] demux_awcnt_div, demux_arcnt_div;
  for (genvar s = 0; s < TbNumMasters; s++) begin : gen_demux_cnt_div
    logic [2:0][(2**TbAxiIdUsed)-1:0][DemuxSelW-1:0] aw_sel, ar_sel;
    logic aw_d, ar_d;

    // assign aw_sel = `XBAR.i_xbar_unmuxed.gen_slv_port_demux[s].i_axi_demux
    //               .i_demux_simple.gen_demux.gen_aw_id_counter
    //               .i_aw_id_counter.mst_select_q;
    // assign ar_sel = `XBAR.i_xbar_unmuxed.gen_slv_port_demux[s].i_axi_demux
    //               .i_demux_simple.gen_demux.gen_ar_id_counter
    //               .i_ar_id_counter.mst_select_q;
    `ifndef TARGET_NETLIST_SIM
        assign aw_sel = `XBAR.i_xbar_unmuxed.gen_slv_port_demux[s].i_axi_demux
                          .i_demux_simple.gen_demux.gen_aw_id_counter.i_aw_id_counter.mst_select_q;
        assign ar_sel = `XBAR.i_xbar_unmuxed.gen_slv_port_demux[s].i_axi_demux
                          .i_demux_simple.gen_demux.gen_ar_id_counter.i_ar_id_counter.mst_select_q;
    `else
        assign aw_sel = '0;
        assign ar_sel = '0;
    `endif

    always_comb begin
      aw_d = 1'b0;
      ar_d = 1'b0;
      for (int c = 0; c < (2**TbAxiIdUsed); c++) begin
        if (^aw_sel[0][c] !== 1'bx && ^aw_sel[1][c] !== 1'bx && ^aw_sel[2][c] !== 1'bx)
          aw_d |= ~((aw_sel[0][c] == aw_sel[1][c]) && (aw_sel[1][c] == aw_sel[2][c]));
        if (^ar_sel[0][c] !== 1'bx && ^ar_sel[1][c] !== 1'bx && ^ar_sel[2][c] !== 1'bx)
          ar_d |= ~((ar_sel[0][c] == ar_sel[1][c]) && (ar_sel[1][c] == ar_sel[2][c]));
      end
    end

    assign demux_awcnt_div[s] = aw_d;
    assign demux_arcnt_div[s] = ar_d;
  end

  logic tmr_diverged;
  assign tmr_diverged = |mux_lock_div | |demux_lock_aw_div
                      | |demux_lock_ar_div | |errslv_busy_div
                      | |demux_wsel_div
                      | |demux_awcnt_div | |demux_arcnt_div;

  final begin
    automatic int unsigned leftover = 0;
    for (int m = 0; m < TbNumMasters; m++)
      for (int k = 0; k < IdSpace; k++) begin
        if (aw_outstanding[m][k] != 0) begin
          leftover++;
          $display("[SB] AW leak mgr=%0d id=0x%0h cnt=%0d", m, k, aw_outstanding[m][k]);
        end
        if (ar_outstanding[m][k] != 0) begin
          leftover++;
          $display("[SB] AR leak mgr=%0d id=0x%0h cnt=%0d", m, k, ar_outstanding[m][k]);
        end
      end
    $display("[SB] collisions=%0d leftover=%0d bmis=%b rmis=%b awx=%b arx=%b hsx=%b",
             sb_collisions, leftover, b_misroute, r_misroute, aw_id_x, ar_id_x, hs_x);
    $display("[TMR-DIV] mux=%b dmxaw=%b dmxar=%b busy=%b wsel=%b awcnt=%b arcnt=%b",
                 mux_lock_div, demux_lock_aw_div, demux_lock_ar_div,
                 errslv_busy_div, demux_wsel_div, demux_awcnt_div, demux_arcnt_div);

  end
  // -----------------------------------------------------------
  // Z01X strobe
  // -----------------------------------------------------------
  `ifdef FAULTSIM
  `include "strobe_relaxi_xbar.sv"
  `endif

endmodule
