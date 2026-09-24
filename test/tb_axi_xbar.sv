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
// a number of random axi master and slave modules.  Each random master executes a fixed number of
// writes and reads over the whole addess map.  All masters simultaneously issue transactions
// through the crossbar, thereby saturating it.  A monitor, which snoops the transactions of each
// master and slave port and models the crossbar with a network of FIFOs, checks whether each
// transaction follows the expected route.

`include "axi/typedef.svh"
`include "axi/assign.svh"

/// Testbench for the module `axi_xbar`.
module tb_axi_xbar #(
  /// Number of AXI masters connected to the xbar. (Number of slave ports)
  parameter int unsigned TbNumMasters        = 32'd6,
  /// Number of AXI slaves connected to the xbar. (Number of master ports)
  parameter int unsigned TbNumSlaves         = 32'd8,
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
  localparam int unsigned TbAxiUserWidth     =  5;
  // In the bench can change this variables which are set here freely,
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
  typedef logic [TbAxiAddrWidth-1:0]      addr_t;
  typedef axi_pkg::xbar_rule_32_t         rule_t; // Has to be the same width as axi addr
  typedef logic [TbAxiDataWidth-1:0]      data_t;
  typedef logic [TbAxiStrbWidth-1:0]      strb_t;
  typedef logic [TbAxiUserWidth-1:0]      user_t;

  `RELAXI_TYPEDEF_AW_CHAN_T(aw_chan_mst_t, addr_t, id_mst_t, user_t)
  `RELAXI_TYPEDEF_AW_CHAN_T(aw_chan_slv_t, addr_t, id_slv_t, user_t)
  `RELAXI_TYPEDEF_W_CHAN_T(w_chan_t, data_t, strb_t, user_t)
  `RELAXI_TYPEDEF_B_CHAN_T(b_chan_mst_t, id_mst_t, user_t)
  `RELAXI_TYPEDEF_B_CHAN_T(b_chan_slv_t, id_slv_t, user_t)

  `RELAXI_TYPEDEF_AR_CHAN_T(ar_chan_mst_t, addr_t, id_mst_t, user_t)
  `RELAXI_TYPEDEF_AR_CHAN_T(ar_chan_slv_t, addr_t, id_slv_t, user_t)
  `RELAXI_TYPEDEF_R_CHAN_T(r_chan_mst_t, data_t, id_mst_t, user_t)
  `RELAXI_TYPEDEF_R_CHAN_T(r_chan_slv_t, data_t, id_slv_t, user_t)

  `RELAXI_TYPEDEF_REQ_T(mst_req_t, aw_chan_mst_t, w_chan_t, ar_chan_mst_t)
  `RELAXI_TYPEDEF_RESP_T(mst_resp_t, b_chan_mst_t, r_chan_mst_t)
  `RELAXI_TYPEDEF_REQ_T(slv_req_t, aw_chan_slv_t, w_chan_t, ar_chan_slv_t)
  `RELAXI_TYPEDEF_RESP_T(slv_resp_t, b_chan_slv_t, r_chan_slv_t)

  // Each slave has its own address range:
  localparam rule_t [xbar_cfg.NoAddrRules-1:0] AddrMap = addr_map_gen();

  function rule_t [xbar_cfg.NoAddrRules-1:0] addr_map_gen ();
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
    .UNIQUE_IDS     ( TbUniqueIds )
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
    // AXI_BUS_DV (driven by axi_rand_master) ↔ AXI_BUS (bidirectional)
    `AXI_ASSIGN (master[i], master_dv[i])
    // Encoder: plain AXI master[i] → relaxi masters_req/resp for DUT
    relaxi_encoder #(
      .AxiAddrWidth ( TbAxiAddrWidth      ),
      .AxiDataWidth ( TbAxiDataWidth      ),
      .AxiIdWidth   ( TbAxiIdWidthMasters ),
      .AxiUserWidth ( TbAxiUserWidth      )
    ) i_master_enc (
      // Plain AXI request — from master[i] interface
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
      .aw_ready_o  ( master[i].aw_ready  ),   // ← voted, drives back to master
 
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
 
      // Relaxi request → DUT slave ports (masters_req)
      .rel_aw_valid_o     ( masters_req[i].aw_valid         ),
      .rel_aw_id_o        ( masters_req[i].aw.id            ),
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
      .rel_b_resp_i       ( masters_resp[i].b.resp          ),
      .rel_b_user_i       ( masters_resp[i].b.user          ),
      .rel_b_ecc_i        ( masters_resp[i].b.b_ecc         ),
      .rel_b_ready_o      ( masters_req[i].b_ready          ),
 
      .rel_ar_valid_o     ( masters_req[i].ar_valid         ),
      .rel_ar_id_o        ( masters_req[i].ar.id            ),
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
      .rel_r_data_i       ( masters_resp[i].r.data          ),
      .rel_r_resp_i       ( masters_resp[i].r.resp          ),
      .rel_r_last_i       ( masters_resp[i].r.last          ),
      .rel_r_user_i       ( masters_resp[i].r.user          ),
      .rel_r_other_ecc_i  ( masters_resp[i].r.r_other_ecc  ),
      .rel_r_ready_o      ( masters_req[i].r_ready          ),
 
      .fault_o            (                                  )  // TODO: connect to fault monitor
    );
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
    // Decoder: relaxi slaves_req/resp from DUT → plain AXI slave[i]
    relaxi_decoder #(
      .AxiAddrWidth ( TbAxiAddrWidth     ),
      .AxiDataWidth ( TbAxiDataWidth     ),
      .AxiIdWidth   ( TbAxiIdWidthSlaves ),
      .AxiUserWidth ( TbAxiUserWidth     )
    ) i_slave_dec (
      // Relaxi request ← DUT master ports (slaves_req)
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
      .rel_aw_other_ecc_i ( slaves_req[i].aw.aw_other_ecc ),
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
      .rel_r_other_ecc_o  ( slaves_resp[i].r.r_other_ecc  ),
      .rel_r_ready_i      ( slaves_req[i].r_ready          ),
 
      // Plain AXI → slave[i] interface (driven to axi_rand_slave)
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
      .aw_ready_i  ( slave[i].aw_ready  ),  // ← driven by axi_rand_slave
 
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
 
      .fault_o     (                    )   // TODO: connect to fault monitor
    );
    // AXI_BUS ↔ AXI_BUS_DV (driven by axi_rand_slave)
    `AXI_ASSIGN (slave_dv[i], slave[i])
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
                                      AddrMap[xbar_cfg.NoAddrRules-1].end_addr,
                                      axi_pkg::DEVICE_NONBUFFERABLE);
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
  relaxi_xbar #(
  .Cfg            ( xbar_cfg        ),
  .ATOPs          ( TbEnAtop        ),
  .slv_aw_chan_t  ( aw_chan_mst_t   ),  // slave port = master-side ID width
  .mst_aw_chan_t  ( aw_chan_slv_t   ),  // master port = slave-side ID width (widened)
  .w_chan_t       ( w_chan_t        ),
  .slv_b_chan_t   ( b_chan_mst_t    ),
  .mst_b_chan_t   ( b_chan_slv_t    ),
  .slv_ar_chan_t  ( ar_chan_mst_t   ),
  .mst_ar_chan_t  ( ar_chan_slv_t   ),
  .slv_r_chan_t   ( r_chan_mst_t    ),
  .mst_r_chan_t   ( r_chan_slv_t    ),
  .slv_req_t      ( mst_req_t      ),
  .slv_resp_t     ( mst_resp_t     ),
  .mst_req_t      ( slv_req_t      ),
  .mst_resp_t     ( slv_resp_t     ),
  .rule_t         ( rule_t         )
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
  .fault_o               (              )
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
      .r_chan_t  (  r_chan_mst_t )  // axi  R type
    ) i_mst_channel_logger (
      .clk_i      ( clk         ),    // Clock
      .rst_ni     ( rst_n       ),    // Asynchronous reset active low, when `1'b0` no sampling
      .end_sim_i  ( &end_of_sim ),
      // AW channel
      .aw_chan_i  ( masters_req[i].aw        ),
      .aw_valid_i ( masters_req[i].aw_valid[0]  ),
      .aw_ready_i ( masters_resp[i].aw_ready[0] ),
      //  W channel
      .w_chan_i   ( masters_req[i].w            ),
      .w_valid_i  ( masters_req[i].w_valid[0]   ),
      .w_ready_i  ( masters_resp[i].w_ready[0]  ),
      //  B channel
      .b_chan_i   ( masters_resp[i].b           ),
      .b_valid_i  ( masters_resp[i].b_valid[0]  ),
      .b_ready_i  ( masters_req[i].b_ready[0]   ),
      // AR channel
      .ar_chan_i  ( masters_req[i].ar           ),
      .ar_valid_i ( masters_req[i].ar_valid[0]  ),
      .ar_ready_i ( masters_resp[i].ar_ready[0] ),
      //  R channel
      .r_chan_i   ( masters_resp[i].r           ),
      .r_valid_i  ( masters_resp[i].r_valid[0]  ),
      .r_ready_i  ( masters_req[i].r_ready[0]   )
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
      .aw_valid_i ( slaves_req[i].aw_valid[0]  ),
      .aw_ready_i ( slaves_resp[i].aw_ready[0] ),
      //  W channel
      .w_chan_i   ( slaves_req[i].w            ),
      .w_valid_i  ( slaves_req[i].w_valid[0]   ),
      .w_ready_i  ( slaves_resp[i].w_ready[0]  ),
      //  B channel
      .b_chan_i   ( slaves_resp[i].b           ),
      .b_valid_i  ( slaves_resp[i].b_valid[0]  ),
      .b_ready_i  ( slaves_req[i].b_ready[0]   ),
      // AR channel
      .ar_chan_i  ( slaves_req[i].ar           ),
      .ar_valid_i ( slaves_req[i].ar_valid[0]  ),
      .ar_ready_i ( slaves_resp[i].ar_ready[0] ),
      //  R channel
      .r_chan_i   ( slaves_resp[i].r           ),
      .r_valid_i  ( slaves_resp[i].r_valid[0]  ),
      .r_ready_i  ( slaves_req[i].r_ready[0]   )
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
