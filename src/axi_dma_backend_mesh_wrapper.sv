// Copyright (c) 2019 ETH Zurich, University of Bologna
// All rights reserved.
//
// This code is under development and not yet released to the public.
// Until it is released, the code is under the copyright of ETH Zurich and
// the University of Bologna, and may contain confidential and/or unpublished
// work. Any reuse/redistribution is strictly forbidden without written
// permission from ETH Zurich.
//
// Thomas Benz <tbenz@ethz.ch>

// fixture for the AXi DMA backend
// the fixture instantiates the DMA backend, a golden model of the backend , and tasks controlling
// both.

`timescale 1ns/1ns

`include "axi/assign.svh"
`include "axi/typedef.svh"

module axi_dma_backend_mesh_wrapper #(
  parameter bit ATOPs = 1'b0,
  parameter int unsigned NoSlvPorts_1 = 32'd2,
  parameter int unsigned NoMstPorts_1 = 32'd2,  
  parameter int unsigned NoSlvPorts_0 = 32'd1,
  parameter int unsigned NoMstPorts_0 = 32'd1,
  parameter bit [NoSlvPorts_1-1:0][NoMstPorts_1-1:0] Connectivity_1 = '1,
  parameter bit [NoSlvPorts_0-1:0][NoMstPorts_0-1:0] Connectivity_0 = '1,
  parameter int unsigned AxiAddrWidth = 32'd64,
  parameter int unsigned AxiDataWidth = 32'd512,
  parameter int unsigned AxiIdWidth = 32'd6,
  parameter int unsigned AxiUserWidth = 32'd1,
  parameter int unsigned AxiStrbWidth = (AxiDataWidth/8),
  parameter int unsigned AxiSlvPortMaxUniqIds = 32'd16,
  parameter int unsigned AxiSlvPortMaxTxnsPerId = 32'd128,
  parameter int unsigned AxiSlvPortMaxTxns = 32'd31,
  parameter int unsigned AxiMstPortMaxUniqIds = 32'd4,
  parameter int unsigned AxiMstPortMaxTxnsPerId = 32'd7,
  parameter int unsigned NoAddrRules_1 = 32'd2,
  parameter int unsigned NoAddrRules_0 = 32'd1
) (
  input  logic                          clk_i,
  input  logic                          rst_ni,
  input  logic                          test_en_i,
  AXI_BUS.Slave                         dma [NoMstPorts_1-1:0],
  AXI_BUS.Master                        mem_0 [NoSlvPorts_0-1:0],
  AXI_BUS.Master                        mem_1 [NoSlvPorts_0-1:0]
);

    //--------------------------------------
    // Parameters
    //--------------------------------------

    typedef axi_pkg::xbar_rule_64_t       rule_t; // Has to be the same width as axi addr

    // in the bench can change this variables which are set here freely
    localparam axi_pkg::xbar_cfg_t xbar_cfg_2 = '{
      NoSlvPorts:         NoMstPorts_1,
      NoMstPorts:         NoSlvPorts_1,
      MaxMstTrans:        AxiSlvPortMaxTxns,
      MaxSlvTrans:        AxiSlvPortMaxTxnsPerId,
      FallThrough:        1'b0,
      LatencyMode:        axi_pkg::CUT_ALL_AX,
      AxiIdWidthSlvPorts: AxiIdWidth,
      AxiIdUsedSlvPorts:  (AxiIdWidth-1),
      UniqueIds:          1'b0,
      AxiAddrWidth:       AxiAddrWidth,
      AxiDataWidth:       AxiDataWidth,
      NoAddrRules:        NoAddrRules_1
    };

    localparam axi_pkg::xbar_cfg_t xbar_cfg_1 = '{
      NoSlvPorts:         NoMstPorts_1,
      NoMstPorts:         NoSlvPorts_1,
      MaxMstTrans:        AxiSlvPortMaxTxns,
      MaxSlvTrans:        AxiSlvPortMaxTxnsPerId,
      FallThrough:        1'b0,
      LatencyMode:        axi_pkg::CUT_ALL_AX,
      AxiIdWidthSlvPorts: AxiIdWidth,
      AxiIdUsedSlvPorts:  (AxiIdWidth-1),
      UniqueIds:          1'b0,
      AxiAddrWidth:       AxiAddrWidth,
      AxiDataWidth:       AxiDataWidth,
      NoAddrRules:        NoAddrRules_1
    };

    localparam axi_pkg::xbar_cfg_t xbar_cfg_0 = '{
      NoSlvPorts:         NoMstPorts_0,
      NoMstPorts:         NoSlvPorts_0,
      MaxMstTrans:        AxiSlvPortMaxTxns,
      MaxSlvTrans:        AxiSlvPortMaxTxnsPerId,
      FallThrough:        1'b0,
      LatencyMode:        axi_pkg::CUT_ALL_AX,
      AxiIdWidthSlvPorts: AxiIdWidth,
      AxiIdUsedSlvPorts:  (AxiIdWidth-1),
      UniqueIds:          1'b0,
      AxiAddrWidth:       AxiAddrWidth,
      AxiDataWidth:       AxiDataWidth,
      NoAddrRules:        NoAddrRules_0
    };

    localparam rule_t [xbar_cfg_2.NoAddrRules-1:0] AddrMap_xp2 = '{
      '{idx: 32'd1 % NoSlvPorts_1, start_addr: {AxiAddrWidth{1'b0}}, end_addr: {1'b0, {(AxiAddrWidth-1){1'b1}}}},
      '{idx: 32'd0 % NoSlvPorts_1, start_addr: {1'b0, {(AxiAddrWidth-1){1'b1}}}, end_addr: {(AxiAddrWidth){1'b1}}}
      //'{idx: 32'd0 % NoSlvPorts, start_addr: {AddrWidth{1'b0}}, end_addr: {(AddrWidth){1'b1}}}
    };

    localparam rule_t [xbar_cfg_1.NoAddrRules-1:0] AddrMap_xp1 = '{
      '{idx: 32'd1 % NoSlvPorts_1, start_addr: {1'b0, {(AxiAddrWidth-1){1'b1}}}, end_addr: {(AxiAddrWidth){1'b1}}},
      '{idx: 32'd0 % NoSlvPorts_1, start_addr: {AxiAddrWidth{1'b0}}, end_addr: {1'b0, {(AxiAddrWidth-1){1'b1}}}}
      //'{idx: 32'd0 % NoSlvPorts, start_addr: {AddrWidth{1'b0}}, end_addr: {(AddrWidth){1'b1}}}
    };

    localparam rule_t [xbar_cfg_0.NoAddrRules-1:0] AddrMap_xp0 = '{
      '{idx: 32'd0 % NoSlvPorts_0, start_addr: {AxiAddrWidth{1'b0}}, end_addr: {(AxiAddrWidth){1'b1}}}
    };

    /// Address Type
    typedef logic [  AxiAddrWidth-1:0] addr_t;
    /// Data Type
    typedef logic [  AxiDataWidth-1:0] data_t;
    /// Strobe Type
    typedef logic [  AxiStrbWidth-1:0] strb_t;
    /// AXI ID Type
    typedef logic [  AxiIdWidth-1:0] axi_id_t;
    /// AXI USER Type
    typedef logic [  AxiUserWidth-1:0] user_t;

    // master AXI bus --> DMA
    `AXI_TYPEDEF_AW_CHAN_T(aw_chan_dma_t, addr_t, axi_id_t, user_t)
    `AXI_TYPEDEF_W_CHAN_T(w_chan_t, data_t, strb_t, user_t)
    `AXI_TYPEDEF_B_CHAN_T(b_chan_dma_t, axi_id_t, user_t)

    `AXI_TYPEDEF_AR_CHAN_T(ar_chan_dma_t, addr_t, axi_id_t, user_t)
    `AXI_TYPEDEF_R_CHAN_T(r_chan_dma_t, data_t, axi_id_t, user_t)

    `AXI_TYPEDEF_REQ_T(dma_req_t, aw_chan_dma_t, w_chan_t, ar_chan_dma_t)
    `AXI_TYPEDEF_RESP_T(dma_resp_t, b_chan_dma_t, r_chan_dma_t)

    // slave AXI bus --> mem
    `AXI_TYPEDEF_AW_CHAN_T(aw_chan_mem_t, addr_t, axi_id_t, user_t)
    `AXI_TYPEDEF_B_CHAN_T(b_chan_mem_t, axi_id_t, user_t)

    `AXI_TYPEDEF_AR_CHAN_T(ar_chan_mem_t, addr_t, axi_id_t, user_t)
    `AXI_TYPEDEF_R_CHAN_T(r_chan_mem_t, data_t, axi_id_t, user_t)

    `AXI_TYPEDEF_REQ_T(mem_req_t, aw_chan_mem_t, w_chan_t, ar_chan_mem_t)
    `AXI_TYPEDEF_RESP_T(mem_resp_t, b_chan_mem_t, r_chan_mem_t)

    //--------------------------------------
    // DUT Axi busses
    //--------------------------------------

    // AXI_BUS #(
    //     .AXI_ADDR_WIDTH  ( AxiAddrWidth   ),
    //     .AXI_DATA_WIDTH  ( AxiDataWidth   ),
    //     .AXI_ID_WIDTH    ( AxiIdWidth     ),
    //     .AXI_USER_WIDTH  ( 1           )
    // ) dma [NoMstPorts_1-1:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AxiAddrWidth   ),
        .AXI_DATA_WIDTH  ( AxiDataWidth   ),
        .AXI_ID_WIDTH    ( AxiIdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp0_slv [NoSlvPorts_1-1:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AxiAddrWidth   ),
        .AXI_DATA_WIDTH  ( AxiDataWidth   ),
        .AXI_ID_WIDTH    ( AxiIdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp0_slv_0 [NoSlvPorts_0-1:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AxiAddrWidth   ),
        .AXI_DATA_WIDTH  ( AxiDataWidth   ),
        .AXI_ID_WIDTH    ( AxiIdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp0_slv_1 [NoSlvPorts_0-1:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AxiAddrWidth   ),
        .AXI_DATA_WIDTH  ( AxiDataWidth   ),
        .AXI_ID_WIDTH    ( AxiIdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp1_slv [NoSlvPorts_0-1:0] ();

    `AXI_ASSIGN (xp0_slv_0[0], xp0_slv[0])
    `AXI_ASSIGN (xp0_slv_1[0], xp0_slv[1])

    // AXI_BUS #(
    //     .AXI_ADDR_WIDTH  ( AxiAddrWidth   ),
    //     .AXI_DATA_WIDTH  ( AxiDataWidth   ),
    //     .AXI_ID_WIDTH    ( AxiIdWidth     ),
    //     .AXI_USER_WIDTH  ( 1           )
    // ) mem_0 [NoSlvPorts_0-1:0] ();

    // AXI_BUS #(
    //     .AXI_ADDR_WIDTH  ( AxiAddrWidth   ),
    //     .AXI_DATA_WIDTH  ( AxiDataWidth   ),
    //     .AXI_ID_WIDTH    ( AxiIdWidth     ),
    //     .AXI_USER_WIDTH  ( 1           )
    // ) mem_1 [NoSlvPorts_0-1:0] ();

    //-----------------------------------
    // DUT
    //-----------------------------------
    axi_xp_intf #(
      .ATOPs                   ( ATOPs         ),
      .Cfg                     ( xbar_cfg_0      ),
      .NoSlvPorts              ( xbar_cfg_0.NoSlvPorts    ),
      .NoMstPorts              ( xbar_cfg_0.NoMstPorts    ),
      .Connectivity            ( Connectivity_1  ),
      .AxiAddrWidth            ( AxiAddrWidth  ),
      .AxiDataWidth            ( AxiDataWidth  ),
      .AxiIdWidth              ( AxiIdWidth    ),
      .AxiUserWidth            ( AxiUserWidth  ),
      .AxiSlvPortMaxUniqIds    ( AxiSlvPortMaxUniqIds   ),
      .AxiSlvPortMaxTxnsPerId  ( AxiSlvPortMaxTxnsPerId ),
      .AxiSlvPortMaxTxns       ( AxiSlvPortMaxTxns      ),
      .AxiMstPortMaxUniqIds    ( AxiMstPortMaxUniqIds   ),
      .AxiMstPortMaxTxnsPerId  ( AxiMstPortMaxTxnsPerId ),
      .NoAddrRules             ( xbar_cfg_0.NoAddrRules   ),
      .rule_t                  ( rule_t                 )
    ) i_xp_dut_3 (
      .clk_i                  ( clk_i          ),
      .rst_ni                 ( rst_ni        ),
      .test_en_i              ( 1'b0         ),
      .slv_ports              ( xp1_slv      ),
      .mst_ports              ( mem_0        ),
      .addr_map_i             ( AddrMap_xp0  )
    );

    axi_xp_intf #(
      .ATOPs                   ( ATOPs         ),
      .Cfg                     ( xbar_cfg_0      ),
      .NoSlvPorts              ( xbar_cfg_0.NoSlvPorts    ),
      .NoMstPorts              ( xbar_cfg_0.NoMstPorts    ),
      .Connectivity            ( Connectivity_0  ),
      .AxiAddrWidth            ( AxiAddrWidth  ),
      .AxiDataWidth            ( AxiDataWidth  ),
      .AxiIdWidth              ( AxiIdWidth    ),
      .AxiUserWidth            ( AxiUserWidth  ),
      .AxiSlvPortMaxUniqIds    ( AxiSlvPortMaxUniqIds   ),
      .AxiSlvPortMaxTxnsPerId  ( AxiSlvPortMaxTxnsPerId ),
      .AxiSlvPortMaxTxns       ( AxiSlvPortMaxTxns      ),
      .AxiMstPortMaxUniqIds    ( AxiMstPortMaxUniqIds   ),
      .AxiMstPortMaxTxnsPerId  ( AxiMstPortMaxTxnsPerId ),
      .NoAddrRules             ( xbar_cfg_0.NoAddrRules   ),
      .rule_t                  ( rule_t                 )
    ) i_xp_dut_2 (
      .clk_i                  ( clk_i          ),
      .rst_ni                 ( rst_ni        ),
      .test_en_i              ( 1'b0         ),
      .slv_ports              ( xp0_slv_1      ),
      .mst_ports              ( mem_1          ),
      .addr_map_i             ( AddrMap_xp0  )
    );

    axi_xp_intf #(
      .ATOPs                   ( ATOPs         ),
      .Cfg                     ( xbar_cfg_0      ),
      .NoSlvPorts              ( xbar_cfg_0.NoSlvPorts    ),
      .NoMstPorts              ( xbar_cfg_0.NoMstPorts    ),
      .Connectivity            ( Connectivity_0  ),
      .AxiAddrWidth            ( AxiAddrWidth  ),
      .AxiDataWidth            ( AxiDataWidth  ),
      .AxiIdWidth              ( AxiIdWidth    ),
      .AxiUserWidth            ( AxiUserWidth  ),
      .AxiSlvPortMaxUniqIds    ( AxiSlvPortMaxUniqIds   ),
      .AxiSlvPortMaxTxnsPerId  ( AxiSlvPortMaxTxnsPerId ),
      .AxiSlvPortMaxTxns       ( AxiSlvPortMaxTxns      ),
      .AxiMstPortMaxUniqIds    ( AxiMstPortMaxUniqIds   ),
      .AxiMstPortMaxTxnsPerId  ( AxiMstPortMaxTxnsPerId ),
      .NoAddrRules             ( xbar_cfg_0.NoAddrRules   ),
      .rule_t                  ( rule_t                 )
    ) i_xp_dut_1 (
      .clk_i                  ( clk_i          ),
      .rst_ni                 ( rst_ni        ),
      .test_en_i              ( 1'b0         ),
      .slv_ports              ( xp0_slv_0    ),
      .mst_ports              ( xp1_slv      ),
      .addr_map_i             ( AddrMap_xp0  )
    );

    axi_xp_intf #(
      .ATOPs                   ( ATOPs         ),
      .Cfg                     ( xbar_cfg_1      ),
      .NoSlvPorts              ( xbar_cfg_1.NoSlvPorts    ),
      .NoMstPorts              ( xbar_cfg_1.NoMstPorts    ),
      .Connectivity            ( Connectivity_1  ),
      .AxiAddrWidth            ( AxiAddrWidth  ),
      .AxiDataWidth            ( AxiDataWidth  ),
      .AxiIdWidth              ( AxiIdWidth    ),
      .AxiUserWidth            ( AxiUserWidth  ),
      .AxiSlvPortMaxUniqIds    ( AxiSlvPortMaxUniqIds   ),
      .AxiSlvPortMaxTxnsPerId  ( AxiSlvPortMaxTxnsPerId ),
      .AxiSlvPortMaxTxns       ( AxiSlvPortMaxTxns      ),
      .AxiMstPortMaxUniqIds    ( AxiMstPortMaxUniqIds   ),
      .AxiMstPortMaxTxnsPerId  ( AxiMstPortMaxTxnsPerId ),
      .NoAddrRules             ( xbar_cfg_1.NoAddrRules   ),
      .rule_t                  ( rule_t                 )
    ) i_xp_dut_0 (
      .clk_i                  ( clk_i          ),
      .rst_ni                 ( rst_ni        ),
      .test_en_i              ( 1'b0         ),
      .slv_ports              ( dma          ),
      .mst_ports              ( xp0_slv      ),
      .addr_map_i             ( AddrMap_xp1  )
    );

endmodule : axi_dma_backend_mesh_wrapper
