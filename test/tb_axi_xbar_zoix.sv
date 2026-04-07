// Copyright 2026 ETH Zurich and University of Bologna.
// Proprietary, not for release

`include "axi/typedef.svh"
`include "axi/assign.svh"

module tb_axi_xbar_zoix #(
  /// Number of AXI masters connected to the xbar. (Number of slave ports)
  parameter int unsigned TbNumMasters        = 32'd10,
  /// Number of AXI slaves connected to the xbar. (Number of master ports)
  parameter int unsigned TbNumSlaves         = 32'd10,
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
      axi_rand_master[i].add_memory_region(
        AddrMap[0].start_addr,
        AddrMap[xbar_cfg.NoAddrRules-1].end_addr,
        axi_pkg::DEVICE_NONBUFFERABLE
      );
      axi_rand_master[i].reset();
      @(posedge rst_n);
      axi_rand_master[i].run(TbNumReads, TbNumWrites);
      end_of_sim[i] <= 1'b1;
    end
  end

  initial begin
    wait (&end_of_sim);
    $display("[ZOIX] end_of_sim at cycle %0d, time %0t",
             $time/10, $time);
    repeat (1000) @(posedge clk);
    $finish();
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
  
  // -----------------------------------------------------------
  // Simulation termination
  // -----------------------------------------------------------
  initial begin
    wait (&end_of_sim);
    repeat (1000) @(posedge clk);
    $display("[%0t] All masters done.", $time);
    $finish();
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
    .AXI_USER_WIDTH ( TbAxiUserWidth  ),
    .Cfg            ( xbar_cfg        ),
    .rule_t         ( rule_t          )
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
  
  // -----------------------------------------------------------
  // Flat signals for $fs_compare
  // masters_resp is what managers see back (slv port responses)
  // slaves_req is what subordinates see (mst port requests)
  // -----------------------------------------------------------
  localparam int unsigned MstRespBits = $bits(mst_resp_t);
  localparam int unsigned SlvReqBits  = $bits(slv_req_t);

  logic [TbNumMasters-1:0][MstRespBits-1:0] masters_resp_flat;
  logic [TbNumSlaves-1:0][SlvReqBits-1:0]   slaves_req_flat;

  for (genvar i = 0; i < TbNumMasters; i++) begin : gen_masters_resp_flat
    assign masters_resp_flat[i] = masters_resp[i];
  end
  for (genvar i = 0; i < TbNumSlaves; i++) begin : gen_slaves_req_flat
    assign slaves_req_flat[i] = slaves_req[i];
  end
  
  // -----------------------------------------------------------
  // interface_error:
  // Fires when a transaction appears on a mst port (slave side)
  // but the address does not belong to that port's mapped range.
  // Catches misrouting: address decoded to wrong port.
  // Checked on AW (writes) and AR (reads) separately.
  // -----------------------------------------------------------
  logic interface_error;
  logic [TbNumSlaves-1:0] mst_port_aw_error;
  logic [TbNumSlaves-1:0] mst_port_ar_error;

  always_comb begin
    for (int unsigned i = 0; i < TbNumSlaves; i++) begin
      // AW channel misrouting check
      if (slaves_req[i].aw_valid) begin
        logic aw_addr_ok;
        aw_addr_ok = 1'b0;
        for (int unsigned r = 0; r < xbar_cfg.NoAddrRules; r++) begin
          if (AddrMap[r].idx == i &&
              slaves_req[i].aw.addr >= AddrMap[r].start_addr &&
              slaves_req[i].aw.addr <  AddrMap[r].end_addr) begin
            aw_addr_ok = 1'b1;
          end
        end
        mst_port_aw_error[i] = ~aw_addr_ok;
      end else begin
        mst_port_aw_error[i] = 1'b0;
      end

      // AR channel misrouting check
      if (slaves_req[i].ar_valid) begin
        logic ar_addr_ok;
        ar_addr_ok = 1'b0;
        for (int unsigned r = 0; r < xbar_cfg.NoAddrRules; r++) begin
          if (AddrMap[r].idx == i &&
              slaves_req[i].ar.addr >= AddrMap[r].start_addr &&
              slaves_req[i].ar.addr <  AddrMap[r].end_addr) begin
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
  
  // -----------------------------------------------------------
  // Z01X strobe
  // -----------------------------------------------------------
  `ifdef TARGET_ZOIX
  `include "strobe_axi_xbar.sv"
  `endif

endmodule
