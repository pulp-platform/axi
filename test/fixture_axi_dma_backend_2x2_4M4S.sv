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
module fixture_axi_dma_backend();

    // `include "../axi/include/axi/assign.svh"
    `define MEM_DEBUG 1
    `include "axi/assign.svh"
    `include "axi/typedef.svh"

    //--------------------------------------
    // Parameters
    //--------------------------------------
    localparam TA          = 0.2ns;  // must be nonzero to avoid Snitch load fifo double pop glitch
    localparam TT          = 0.8ns;
    localparam HalfPeriod  = 50ns;
    localparam Reset       = 75ns;

    localparam DataWidth   = 512;
    localparam AddrWidth   = 32;
    localparam StrbWidth   = DataWidth / 8;
    localparam IdWidth     = 6;
    localparam UserWidth   = 1;

    // DUT parameters
    localparam bit  ATOPs = 0;
    localparam int unsigned NoMst = 4;
    localparam int unsigned NoSlv = 4;
    localparam int unsigned NoSlvPorts_1 = 3;
    localparam int unsigned NoMstPorts_1 = 3;
    localparam int unsigned NoSlvPorts_0 = 3;
    localparam int unsigned NoMstPorts_0 = 3;
    localparam bit [NoSlvPorts_1-1:0][NoMstPorts_1-1:0] Connectivity_1 = '1;
    localparam bit [NoSlvPorts_0-1:0][NoMstPorts_0-1:0] Connectivity_0 = '1;
    localparam int unsigned AxiSlvPortMaxUniqIds = 32'd16;
    localparam int unsigned AxiSlvPortMaxTxnsPerId = 32'd128;
    localparam int unsigned AxiSlvPortMaxTxns = 32'd31;
    localparam int unsigned AxiMstPortMaxUniqIds = 32'd4;
    localparam int unsigned AxiMstPortMaxTxnsPerId = 32'd7;
    localparam int unsigned NoAddrRules_1 = 32'd3;
    localparam int unsigned NoAddrRules_0 = 32'd3;

    typedef axi_pkg::xbar_rule_32_t       rule_t; // Has to be the same width as axi addr

    // axi configuration
    localparam int unsigned AxiIdWidthMasters =  IdWidth;
    localparam int unsigned AxiIdUsed         =  IdWidth-1; // Has to be <= AxiIdWidthMasters
    localparam int unsigned AxiIdWidthSlaves  =  AxiIdWidthMasters + $clog2(NoMstPorts_1);
    localparam int unsigned AxiAddrWidth      =  AddrWidth;    // Axi Address Width
    localparam int unsigned AxiDataWidth      =  DataWidth;    // Axi Data Width
    localparam int unsigned AxiStrbWidth      =  StrbWidth;
    localparam int unsigned AxiUserWidth      =  UserWidth;
    localparam int unsigned AxiIdWidth        =  IdWidth;
    // in the bench can change this variables which are set here freely
    localparam axi_pkg::xbar_cfg_t xbar_cfg_2 = '{
      NoSlvPorts:         NoMstPorts_1,
      NoMstPorts:         NoSlvPorts_1,
      MaxMstTrans:        AxiSlvPortMaxTxns,
      MaxSlvTrans:        AxiSlvPortMaxTxnsPerId,
      FallThrough:        1'b0,
      LatencyMode:        axi_pkg::CUT_ALL_PORTS,
      AxiIdWidthSlvPorts: AxiIdWidthMasters,
      AxiIdUsedSlvPorts:  AxiIdUsed,
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
      LatencyMode:        axi_pkg::CUT_ALL_PORTS,
      AxiIdWidthSlvPorts: AxiIdWidthMasters,
      AxiIdUsedSlvPorts:  AxiIdUsed,
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
      LatencyMode:        axi_pkg::CUT_ALL_PORTS,
      AxiIdWidthSlvPorts: AxiIdWidthMasters,
      AxiIdUsedSlvPorts:  AxiIdUsed,
      UniqueIds:          1'b0,
      AxiAddrWidth:       AxiAddrWidth,
      AxiDataWidth:       AxiDataWidth,
      NoAddrRules:        NoAddrRules_0
    };

    //localparam rule_t [xbar_cfg_2.NoAddrRules-1:0] AddrMap_xp2 = '{
    //  '{idx: 32'd1 % NoSlvPorts_1, start_addr: {AddrWidth{1'b0}}, end_addr: {1'b0, {(AddrWidth-1){1'b1}}}},
    //  '{idx: 32'd0 % NoSlvPorts_1, start_addr: {1'b0, {(AddrWidth-1){1'b1}}}, end_addr: {(AddrWidth){1'b1}}}
      //'{idx: 32'd0 % NoSlvPorts, start_addr: {AddrWidth{1'b0}}, end_addr: {(AddrWidth){1'b1}}}
    //};

    localparam rule_t [xbar_cfg_1.NoAddrRules-1:0] AddrMap_xp0 = '{
      '{idx: 32'd2 % NoSlvPorts_1, start_addr: {32'h0fffffff}, end_addr: {32'hffffffff}},
      '{idx: 32'd1 % NoSlvPorts_1, start_addr: {32'h0000ffff}, end_addr: {32'h0fffffff}},
      '{idx: 32'd0 % NoSlvPorts_1, start_addr: {32'b0}, end_addr: {32'h0000ffff}}
      //'{idx: 32'd0 % NoSlvPorts, start_addr: {AddrWidth{1'b0}}, end_addr: {(AddrWidth){1'b1}}}
    };

    localparam rule_t [xbar_cfg_1.NoAddrRules-1:0] AddrMap_xp1 = '{
      '{idx: 32'd2 % NoSlvPorts_1, start_addr: {32'b0}, end_addr: {32'h0000ffff}},
      '{idx: 32'd1 % NoSlvPorts_1, start_addr: {32'h0000ffff}, end_addr: {32'h0fffffff}},
      '{idx: 32'd0 % NoSlvPorts_1, start_addr: {32'h0fffffff}, end_addr: {32'hffffffff}}
      //'{idx: 32'd0 % NoSlvPorts, start_addr: {AddrWidth{1'b0}}, end_addr: {(AddrWidth){1'b1}}}
    };

    localparam rule_t [xbar_cfg_1.NoAddrRules-1:0] AddrMap_xp2 = '{
      '{idx: 32'd2 % NoSlvPorts_1, start_addr: {32'b0}, end_addr: {32'h0000ffff}},
      '{idx: 32'd1 % NoSlvPorts_1, start_addr: {32'h0fffffff}, end_addr: {32'hffffffff}},
      '{idx: 32'd0 % NoSlvPorts_1, start_addr: {32'h0000ffff}, end_addr: {32'h0fffffff}}
      //'{idx: 32'd0 % NoSlvPorts, start_addr: {AddrWidth{1'b0}}, end_addr: {(AddrWidth){1'b1}}}
    };

    //localparam rule_t [xbar_cfg_0.NoAddrRules-1:0] AddrMap_xp0 = '{
    //  '{idx: 32'd0 % NoSlvPorts_0, start_addr: {AddrWidth{1'b0}}, end_addr: {(AddrWidth){1'b1}}}
    //};

    typedef union packed {
        logic [StrbWidth-1:0][7:0] bytes;
        logic [DataWidth-1:0]      data;
    } block_t;

    /// Address Type
    typedef logic [  AddrWidth-1:0] addr_t;
    /// Data Type
    typedef logic [  DataWidth-1:0] data_t;
    /// Strobe Type
    typedef logic [  StrbWidth-1:0] strb_t;
    /// AXI ID Type
    typedef logic [    IdWidth-1:0] axi_id_t;
    /// AXI USER Type
    typedef logic [  UserWidth-1:0] user_t;
    /// 1D burst request
    typedef struct packed {
        axi_id_t            id;
        addr_t              src, dst, num_bytes;
        axi_pkg::cache_t    cache_src, cache_dst;
        axi_pkg::burst_t    burst_src, burst_dst;
        logic               decouple_rw;
        logic               deburst;
        logic               serialize;
    } burst_req_t;

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
    // Clock and Reset
    //--------------------------------------
    logic clk;
    initial begin
        forever begin
            clk = 0;
            #HalfPeriod;
            clk = 1;
            #HalfPeriod;
        end
    end

    logic rst_n;
    initial begin
        rst_n = 0;
        #Reset;
        rst_n = 1;
    end

    task wait_for_reset;
       @(posedge rst_n);
       @(posedge clk);
    endtask

    //--------------------------------------
    // DUT Axi busses
    //--------------------------------------

    dma_req_t  [NoMst-1:0] axi_dma_req;
    dma_resp_t [NoMst-1:0] axi_dma_res;

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) dma [NoMst-1:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) dma_sync [NoMst-1:0] ();

    AXI_BUS_DV #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) dma_dv [NoMst-1:0] (clk);

    for (genvar i = 0; i < NoMst; i++) begin : gen_conn_dv_masters
      //`AXI_ASSIGN (dma_dv[i], dma[i])
      `AXI_ASSIGN_FROM_REQ(dma[i], axi_dma_req[i])
      `AXI_ASSIGN_TO_RESP(axi_dma_res[i], dma[i])
    end

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp0_mst [NoMstPorts_1-1:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp0_mst_0 [0:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp0_mst_1 [0:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp0_mst_2 [0:0] ();

    `AXI_ASSIGN (mem_0[0], xp0_mst[0])
    `AXI_ASSIGN (xp0_mst_1[0], xp0_mst[1])
    `AXI_ASSIGN (xp0_mst_2[0], xp0_mst[2])

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp0_slv [NoSlvPorts_1-1:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp0_slv_0 [0:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp0_slv_1 [0:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp0_slv_2 [0:0] ();

    `AXI_ASSIGN (xp0_slv[0], dma_sync[0])
    `AXI_ASSIGN (xp0_slv[1], xp0_slv_1[0])
    `AXI_ASSIGN (xp0_slv[2], xp0_slv_2[0])

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp1_mst [NoMstPorts_1-1:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp1_mst_0 [0:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp1_mst_1 [0:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp1_mst_2 [0:0] ();

    `AXI_ASSIGN (mem_0[1], xp1_mst[0])
    `AXI_ASSIGN (xp1_mst_1[0], xp1_mst[1])
    `AXI_ASSIGN (xp1_mst_2[0], xp1_mst[2])

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp1_slv [NoSlvPorts_1-1:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp1_slv_0 [0:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp1_slv_1 [0:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp1_slv_2 [0:0] ();

    `AXI_ASSIGN (xp1_slv[0], dma_sync[1])
    `AXI_ASSIGN (xp1_slv[1], xp1_slv_1[0])
    `AXI_ASSIGN (xp1_slv[2], xp1_slv_2[0])

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp2_mst [NoMstPorts_1-1:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp2_mst_0 [0:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp2_mst_1 [0:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp2_mst_2 [0:0] ();

    `AXI_ASSIGN (mem_0[2], xp2_mst[0])
    `AXI_ASSIGN (xp2_mst_1[0], xp2_mst[1])
    `AXI_ASSIGN (xp2_mst_2[0], xp2_mst[2])

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp2_slv [NoSlvPorts_1-1:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp2_slv_0 [0:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp2_slv_1 [0:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp2_slv_2 [0:0] ();

    `AXI_ASSIGN (xp2_slv[0], dma_sync[2])
    `AXI_ASSIGN (xp2_slv[1], xp2_slv_1[0])
    `AXI_ASSIGN (xp2_slv[2], xp2_slv_2[0])

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp3_mst [NoMstPorts_1-1:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp3_mst_0 [0:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp3_mst_1 [0:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp3_mst_2 [0:0] ();

    `AXI_ASSIGN (mem_0[3], xp3_mst[0])
    `AXI_ASSIGN (xp3_mst_1[0], xp3_mst[1])
    `AXI_ASSIGN (xp3_mst_2[0], xp3_mst[2])

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp3_slv [NoSlvPorts_1-1:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp3_slv_0 [0:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp3_slv_1 [0:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp3_slv_2 [0:0] ();

    `AXI_ASSIGN (xp3_slv[0], dma_sync[3])
    `AXI_ASSIGN (xp3_slv[1], xp3_slv_1[0])
    `AXI_ASSIGN (xp3_slv[2], xp3_slv_2[0])

    // XP0 <--> XP1

    `AXI_ASSIGN (xp1_slv_1[0], xp0_mst_1[0])
    `AXI_ASSIGN (xp0_slv_1[0], xp1_mst_1[0])

    // XP0 <--> XP2

    `AXI_ASSIGN (xp2_slv_2[0], xp0_mst_2[0])
    `AXI_ASSIGN (xp0_slv_2[0], xp2_mst_2[0])

    // XP1 <--> XP3

    `AXI_ASSIGN (xp1_slv_2[0], xp3_mst_2[0])
    `AXI_ASSIGN (xp3_slv_2[0], xp1_mst_2[0])

    // XP2 <--> XP3

    `AXI_ASSIGN (xp2_slv_1[0], xp3_mst_1[0])
    `AXI_ASSIGN (xp3_slv_1[0], xp2_mst_1[0])

    AXI_BUS_DV #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) mem_dv [NoSlv-1:0] (clk);

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) mem_0 [NoSlv-1:0] ();

    `AXI_ASSIGN (mem_dv[0], mem_0[0])
    `AXI_ASSIGN (mem_dv[1], mem_0[1])
    `AXI_ASSIGN (mem_dv[2], mem_0[2])
    `AXI_ASSIGN (mem_dv[3], mem_0[3])

    //`AXI_ASSIGN (mem_dv[1], mem_1[0])

    typedef axi_test::axi_driver #(
      .AW(AddrWidth), .DW(DataWidth), .IW(IdWidth), .UW(UserWidth),
      .TA(0.1*2*HalfPeriod), .TT(0.9*2*HalfPeriod)
    ) driver_dma_t;

    typedef axi_test::axi_driver #(
      .AW(AddrWidth), .DW(DataWidth), .IW(IdWidth), .UW(UserWidth),
      .TA(0.1*2*HalfPeriod), .TT(0.9*2*HalfPeriod)
    ) driver_dma1_t;

    typedef axi_test::axi_driver #(
      .AW(AddrWidth), .DW(DataWidth), .IW(IdWidth), .UW(UserWidth),
      .TA(0.1*2*HalfPeriod), .TT(0.9*2*HalfPeriod)
    ) driver_dma2_t;

    typedef axi_test::axi_driver #(
      .AW(AddrWidth), .DW(DataWidth), .IW(IdWidth), .UW(UserWidth),
      .TA(0.1*2*HalfPeriod), .TT(0.9*2*HalfPeriod)
    ) driver_dma3_t;

    driver_dma_t driver_dma = new(mem_dv[0]);
    driver_dma1_t driver_dma1 = new(mem_dv[1]);
    driver_dma2_t driver_dma2 = new(mem_dv[2]);
    driver_dma3_t driver_dma3 = new(mem_dv[3]);

    axi_sim_mem_intf #(
      .AXI_ADDR_WIDTH      (AddrWidth),
      .AXI_DATA_WIDTH      (DataWidth),
      .AXI_ID_WIDTH        (IdWidth),
      .AXI_USER_WIDTH      (UserWidth),
      .WARN_UNINITIALIZED  (1'b0),
      .APPL_DELAY          (2ns),
      .ACQ_DELAY           (8ns)
    ) i_sim_mem0 (
      .clk_i   (clk),
      .rst_ni  (rst_n),
      .axi_slv (mem_dv[0])
    );

    axi_sim_mem_intf #(
      .AXI_ADDR_WIDTH      (AddrWidth),
      .AXI_DATA_WIDTH      (DataWidth),
      .AXI_ID_WIDTH        (IdWidth),
      .AXI_USER_WIDTH      (UserWidth),
      .WARN_UNINITIALIZED  (1'b0),
      .APPL_DELAY          (2ns), 
      .ACQ_DELAY           (8ns)
    ) i_sim_mem1 (
      .clk_i   (clk),
      .rst_ni  (rst_n),
      .axi_slv (mem_dv[1])
    );

    axi_sim_mem_intf #(
      .AXI_ADDR_WIDTH      (AddrWidth),
      .AXI_DATA_WIDTH      (DataWidth),
      .AXI_ID_WIDTH        (IdWidth),
      .AXI_USER_WIDTH      (UserWidth),
      .WARN_UNINITIALIZED  (1'b0),
      .APPL_DELAY          (2ns),
      .ACQ_DELAY           (8ns)
    ) i_sim_mem2 (
      .clk_i   (clk),
      .rst_ni  (rst_n),
      .axi_slv (mem_dv[2])
    );

    axi_sim_mem_intf #(
      .AXI_ADDR_WIDTH      (AddrWidth),
      .AXI_DATA_WIDTH      (DataWidth),
      .AXI_ID_WIDTH        (IdWidth),
      .AXI_USER_WIDTH      (UserWidth),
      .WARN_UNINITIALIZED  (1'b0),
      .APPL_DELAY          (2ns), 
      .ACQ_DELAY           (8ns)
    ) i_sim_mem3 (
      .clk_i   (clk),
      .rst_ni  (rst_n),
      .axi_slv (mem_dv[3])
    );

    // initial begin
    //   $readmemh("sim_mem0.mem", i_sim_mem0.mem);
    //   $readmemh("sim_mem1.mem", i_sim_mem1.mem);
    // end

    //--------------------------------------
    // DUT AXI Memory System
    //--------------------------------------
    // lfsr
    logic [784:0] lfsr_dut_q, lfsr_dut_d;

    // transaction id
    logic [  7:0] transaction_id = 0;

    // Memory
    block_t dma_memory [bit [AddrWidth-$clog2($bits(block_t))-1:0]];
    block_t dma_memory1 [bit [AddrWidth-$clog2($bits(block_t))-1:0]];

    //--------------------------------------
    // DMA instantiation
    //--------------------------------------
    burst_req_t burst0_req;
    burst_req_t burst1_req;
    logic burst0_req_valid;
    logic burst1_req_valid;
    logic burst0_req_ready;
    logic burst1_req_ready;
    logic backend_idle_0;
    logic backend_idle_1;
    burst_req_t burst2_req;
    burst_req_t burst3_req;
    logic burst2_req_valid;
    logic burst3_req_valid;
    logic burst2_req_ready;
    logic burst3_req_ready;
    logic backend_idle_2;
    logic backend_idle_3;

    axi_dma_backend #(
        .DataWidth           ( DataWidth           ),
        .AddrWidth           ( AddrWidth           ),
        .IdWidth             ( IdWidth             ),
        .DmaIdWidth          ( 32                  ),
        .AxReqFifoDepth      ( 3                   ),
        .TransFifoDepth      ( 2                   ),
        .BufferDepth         ( 3                   ),
        .axi_req_t           ( dma_req_t           ),
        .axi_res_t           ( dma_resp_t          ),
        .burst_req_t         ( burst_req_t         ),
        .DmaTracing          ( 1                   )
    ) i_dut_axi_backend_0 (
        .clk_i              ( clk              ),
        .rst_ni             ( rst_n            ),
        .axi_dma_req_o      ( axi_dma_req[0]   ),
        .axi_dma_res_i      ( axi_dma_res[0]   ),
        .burst_req_i        ( burst0_req        ),
        .valid_i            ( burst0_req_valid  ),
        .ready_o            ( burst0_req_ready   ),
        .backend_idle_o     ( backend_idle_0     ),
        .trans_complete_o   ( ),
        .dma_id_i           ( 32'h00000000       )
    );

    axi_aw_w_sync_intf #(
        .AXI_ADDR_WIDTH ( AddrWidth ),
        .AXI_DATA_WIDTH ( DataWidth ),
        .AXI_ID_WIDTH   ( IdWidth   ),
        .AXI_USER_WIDTH ( UserWidth )
    ) i_aw_w_sync_intf_0 (
        .clk_i  ( clk            ),
        .rst_ni ( rst_n          ),
        .in     ( dma[0]         ),
        .out    ( dma_sync[0]    )
    );

    axi_dma_backend #(
        .DataWidth           ( DataWidth           ),
        .AddrWidth           ( AddrWidth           ),
        .IdWidth             ( IdWidth             ),
        .DmaIdWidth          ( 32                  ),
        .AxReqFifoDepth      ( 3                   ),
        .TransFifoDepth      ( 2                   ),
        .BufferDepth         ( 3                   ),
        .axi_req_t           ( dma_req_t           ),
        .axi_res_t           ( dma_resp_t          ),
        .burst_req_t         ( burst_req_t         ),
        .DmaTracing          ( 1                   )
    ) i_dut_axi_backend_1 (
        .clk_i              ( clk              ),
        .rst_ni             ( rst_n            ),
        .axi_dma_req_o      ( axi_dma_req[1]   ),
        .axi_dma_res_i      ( axi_dma_res[1]   ),
        .burst_req_i        ( burst1_req        ),
        .valid_i            ( burst1_req_valid  ),
        .ready_o            ( burst1_req_ready  ),
        .backend_idle_o     ( backend_idle_1     ),
        .trans_complete_o   ( ),
        .dma_id_i           ( 32'h00000001       )
    );

    axi_aw_w_sync_intf #(
        .AXI_ADDR_WIDTH ( AddrWidth ),
        .AXI_DATA_WIDTH ( DataWidth ),
        .AXI_ID_WIDTH   ( IdWidth   ),
        .AXI_USER_WIDTH ( UserWidth )
    ) i_aw_w_sync_intf_1 (
        .clk_i  ( clk            ),
        .rst_ni ( rst_n          ),
        .in     ( dma[1]         ),
        .out    ( dma_sync[1]    )
    );

    axi_dma_backend #(
        .DataWidth           ( DataWidth           ),
        .AddrWidth           ( AddrWidth           ),
        .IdWidth             ( IdWidth             ),
        .DmaIdWidth          ( 32                  ),
        .AxReqFifoDepth      ( 3                   ),
        .TransFifoDepth      ( 2                   ),
        .BufferDepth         ( 3                   ),
        .axi_req_t           ( dma_req_t           ),
        .axi_res_t           ( dma_resp_t          ),
        .burst_req_t         ( burst_req_t         ),
        .DmaTracing          ( 1                   )
    ) i_dut_axi_backend_2 (
        .clk_i              ( clk              ),
        .rst_ni             ( rst_n            ),
        .axi_dma_req_o      ( axi_dma_req[2]   ),
        .axi_dma_res_i      ( axi_dma_res[2]   ),
        .burst_req_i        ( burst2_req        ),
        .valid_i            ( burst2_req_valid  ),
        .ready_o            ( burst2_req_ready   ),
        .backend_idle_o     ( backend_idle_2     ),
        .trans_complete_o   ( ),
        .dma_id_i           ( 32'h00000002       )
    );

    axi_aw_w_sync_intf #(
        .AXI_ADDR_WIDTH ( AddrWidth ),
        .AXI_DATA_WIDTH ( DataWidth ),
        .AXI_ID_WIDTH   ( IdWidth   ),
        .AXI_USER_WIDTH ( UserWidth )
    ) i_aw_w_sync_intf_2 (
        .clk_i  ( clk            ),
        .rst_ni ( rst_n          ),
        .in     ( dma[2]         ),
        .out    ( dma_sync[2]    )
    );

    axi_dma_backend #(
        .DataWidth           ( DataWidth           ),
        .AddrWidth           ( AddrWidth           ),
        .IdWidth             ( IdWidth             ),
        .DmaIdWidth          ( 32                  ),
        .AxReqFifoDepth      ( 3                   ),
        .TransFifoDepth      ( 2                   ),
        .BufferDepth         ( 3                   ),
        .axi_req_t           ( dma_req_t           ),
        .axi_res_t           ( dma_resp_t          ),
        .burst_req_t         ( burst_req_t         ),
        .DmaTracing          ( 1                   )
    ) i_dut_axi_backend_3 (
        .clk_i              ( clk              ),
        .rst_ni             ( rst_n            ),
        .axi_dma_req_o      ( axi_dma_req[3]   ),
        .axi_dma_res_i      ( axi_dma_res[3]   ),
        .burst_req_i        ( burst3_req        ),
        .valid_i            ( burst3_req_valid  ),
        .ready_o            ( burst3_req_ready  ),
        .backend_idle_o     ( backend_idle_3     ),
        .trans_complete_o   ( ),
        .dma_id_i           ( 32'h00000003       )
    );

    axi_aw_w_sync_intf #(
        .AXI_ADDR_WIDTH ( AddrWidth ),
        .AXI_DATA_WIDTH ( DataWidth ),
        .AXI_ID_WIDTH   ( IdWidth   ),
        .AXI_USER_WIDTH ( UserWidth )
    ) i_aw_w_sync_intf_3 (
        .clk_i  ( clk            ),
        .rst_ni ( rst_n          ),
        .in     ( dma[3]         ),
        .out    ( dma_sync[3]    )
    );

    //-----------------------------------
    // DUT
    //-----------------------------------
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
    ) i_xp_dut_3 (
      .clk_i                  ( clk          ),
      .rst_ni                 ( rst_n        ),
      .test_en_i              ( 1'b0         ),
      .slv_ports              ( xp3_slv      ),
      .mst_ports              ( xp3_mst      ),
      .addr_map_i             ( AddrMap_xp2  )
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
    ) i_xp_dut_2 (
      .clk_i                  ( clk          ),
      .rst_ni                 ( rst_n        ),
      .test_en_i              ( 1'b0         ),
      .slv_ports              ( xp2_slv      ),
      .mst_ports              ( xp2_mst      ),
      .addr_map_i             ( AddrMap_xp1  )
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
    ) i_xp_dut_1 (
      .clk_i                  ( clk          ),
      .rst_ni                 ( rst_n        ),
      .test_en_i              ( 1'b0         ),
      .slv_ports              ( xp1_slv      ),
      .mst_ports              ( xp1_mst      ),
      .addr_map_i             ( AddrMap_xp1  )
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
      .clk_i                  ( clk          ),
      .rst_ni                 ( rst_n        ),
      .test_en_i              ( 1'b0         ),
      .slv_ports              ( xp0_slv      ),
      .mst_ports              ( xp0_mst      ),
      .addr_map_i             ( AddrMap_xp0  )
    );
    //--------------------------------------
    // DMA DUT tasks
    //--------------------------------------

    task oned_dut_launch_3 (
        input logic [   IdWidth-1:0] transf_id_i,
        input logic [ AddrWidth-1:0] src_addr_i,  dst_addr_i,  num_bytes_i,
        input logic [           1:0] src_burst_i, dst_burst_i,
        input logic [           3:0] src_cache_i, dst_cache_i,
        input logic                  decouple_rw_i,
        input logic                  serialize_i,
        input logic                  deburst_i
    );
        burst3_req_valid        <= 1'b0;
        burst3_req              <=  '0;
        @(posedge clk);
        while (burst3_req_ready !== 1) @(posedge clk);
        // write data
        burst3_req.id           <= transf_id_i;
        burst3_req.src          <= src_addr_i;
        burst3_req.dst          <= dst_addr_i;
        burst3_req.num_bytes    <= num_bytes_i;
        burst3_req.cache_src    <= src_cache_i;
        burst3_req.cache_dst    <= dst_cache_i;
        burst3_req.burst_src    <= src_burst_i;
        burst3_req.burst_dst    <= dst_burst_i;
        burst3_req.decouple_rw  <= decouple_rw_i;
        burst3_req.deburst      <= deburst_i;
        burst3_req.serialize    <= serialize_i;
        burst3_req_valid        <= 1'b1;
        // wait and set to 0
        @(posedge clk);
        burst3_req_valid        <= 1'b0;
        burst3_req              <=  '0;
    endtask

    task oned_dut_launch_2 (
        input logic [   IdWidth-1:0] transf_id_i,
        input logic [ AddrWidth-1:0] src_addr_i,  dst_addr_i,  num_bytes_i,
        input logic [           1:0] src_burst_i, dst_burst_i,
        input logic [           3:0] src_cache_i, dst_cache_i,
        input logic                  decouple_rw_i,
        input logic                  serialize_i,
        input logic                  deburst_i
    );
        burst2_req_valid        <= 1'b0;
        burst2_req              <=  '0;
        @(posedge clk);
        while (burst2_req_ready !== 1) @(posedge clk);
        // write data
        burst2_req.id           <= transf_id_i;
        burst2_req.src          <= src_addr_i;
        burst2_req.dst          <= dst_addr_i;
        burst2_req.num_bytes    <= num_bytes_i;
        burst2_req.cache_src    <= src_cache_i;
        burst2_req.cache_dst    <= dst_cache_i;
        burst2_req.burst_src    <= src_burst_i;
        burst2_req.burst_dst    <= dst_burst_i;
        burst2_req.decouple_rw  <= decouple_rw_i;
        burst2_req.deburst      <= deburst_i;
        burst2_req.serialize    <= serialize_i;
        burst2_req_valid        <= 1'b1;
        // wait and set to 0
        @(posedge clk);
        burst2_req_valid        <= 1'b0;
        burst2_req              <=  '0;
    endtask

    task oned_dut_launch_1 (
        input logic [   IdWidth-1:0] transf_id_i,
        input logic [ AddrWidth-1:0] src_addr_i,  dst_addr_i,  num_bytes_i,
        input logic [           1:0] src_burst_i, dst_burst_i,
        input logic [           3:0] src_cache_i, dst_cache_i,
        input logic                  decouple_rw_i,
        input logic                  serialize_i,
        input logic                  deburst_i
    );
        burst1_req_valid        <= 1'b0;
        burst1_req              <=  '0;
        @(posedge clk);
        while (burst1_req_ready !== 1) @(posedge clk);
        // write data
        burst1_req.id           <= transf_id_i;
        burst1_req.src          <= src_addr_i;
        burst1_req.dst          <= dst_addr_i;
        burst1_req.num_bytes    <= num_bytes_i;
        burst1_req.cache_src    <= src_cache_i;
        burst1_req.cache_dst    <= dst_cache_i;
        burst1_req.burst_src    <= src_burst_i;
        burst1_req.burst_dst    <= dst_burst_i;
        burst1_req.decouple_rw  <= decouple_rw_i;
        burst1_req.deburst      <= deburst_i;
        burst1_req.serialize    <= serialize_i;
        burst1_req_valid        <= 1'b1;
        // wait and set to 0
        @(posedge clk);
        burst1_req_valid        <= 1'b0;
        burst1_req              <=  '0;
    endtask

    task oned_dut_launch_0 (
        input logic [   IdWidth-1:0] transf_id_i,
        input logic [ AddrWidth-1:0] src_addr_i,  dst_addr_i,  num_bytes_i,
        input logic [           1:0] src_burst_i, dst_burst_i,
        input logic [           3:0] src_cache_i, dst_cache_i,
        input logic                  decouple_rw_i,
        input logic                  serialize_i,
        input logic                  deburst_i
    );
        burst0_req_valid        <= 1'b0;
        burst0_req              <=  '0;
        @(posedge clk);
        while (burst0_req_ready !== 1) @(posedge clk);
        // write data
        burst0_req.id           <= transf_id_i;
        burst0_req.src          <= src_addr_i;
        burst0_req.dst          <= dst_addr_i;
        burst0_req.num_bytes    <= num_bytes_i;
        burst0_req.cache_src    <= src_cache_i;
        burst0_req.cache_dst    <= dst_cache_i;
        burst0_req.burst_src    <= src_burst_i;
        burst0_req.burst_dst    <= dst_burst_i;
        burst0_req.decouple_rw  <= decouple_rw_i;
        burst0_req.deburst      <= deburst_i;
        burst0_req.serialize    <= serialize_i;
        burst0_req_valid        <= 1'b1;
        // wait and set to 0
        @(posedge clk);
        burst0_req_valid        <= 1'b0;
        burst0_req              <=  '0;
    endtask

    task oned_reset ();
        burst0_req_valid        <= 1'b0;
        burst0_req              <=  '0;
        burst1_req_valid        <= 1'b0;
        burst1_req              <=  '0;
        burst2_req_valid        <= 1'b0;
        burst2_req              <=  '0;
        burst3_req_valid        <= 1'b0;
        burst3_req              <=  '0;
    endtask

    task wait_for_dut_completion ();
        repeat(10) @(posedge clk);
        while (backend_idle_0 === 0) @(posedge clk);
        while (backend_idle_1 === 0) @(posedge clk);
        while (backend_idle_2 === 0) @(posedge clk);
        while (backend_idle_3 === 0) @(posedge clk);
        repeat(50) @(posedge clk);
    endtask

    task clear_dut_memory ();
        dma_memory.delete();
        dma_memory1.delete();
    endtask

    task reset_dut_lfsr ();
        lfsr_dut_q <= 'hc0a232c162b2bab5b960668030f4efce27940bd0de965f0b8d4315f15b79704195e4e0a6b495fc269f65ae17e10e9ca98510fc143327a292b418597f9dd175fc91c3d61be287d5462a23e00fa7ae906ae9eb339ab5225021356138cd46b6e5a73540c5591116b6b5e08d2c0e54eaf0d5143b33b2186b6cf841c076a98c412a63981f0e323dce93481ed1c37e4f1d7553b6c2fba1a3af6c3ad88b15ad58812ba07d1753917ac4e6ab1e8c4f67a47b4b0f48a34f42a52c546e979f4e4968e80a732a0a5e7a51146cf08482f349f94336752b765c0b1d70803d883d5058d127264335213da4163c62f65a4e65501b90fa5f177675c0747cfca328e131bfb3f7bcc5c27680c7bf86491f4ed3d36c25531edfa74b1e32fafe426958ae356eb8ef0fd818eaca4227a667b7c934ebfa282ab6bfc6db89b927c91a41e63a9554dced774f30268d0725a1a565368703b9f81d5c027ba196ef8b803a51c639c7ead834e1d6bc537d33800fe5eb12f1ed67758f1dfe85ffdbae56e8ef27f2ecedcee75b8dbb5f5f1a629ba3b755;
    endtask

    //--------------------------------------
    // Osmium Model
    //--------------------------------------
    // Memory
    block_t osmium_memory [bit [AddrWidth-$clog2($bits(block_t))-1:0]];
    // lfsr
    logic [784:0] lfsr_osmium_q,lfsr_osmium_d;

    task oned_osmium_launch (
        input logic [   IdWidth-1:0] transf_id_i,
        input logic [ AddrWidth-1:0] src_addr_i,  dst_addr_i,  num_bytes_i,
        input logic [           1:0] src_burst_i, dst_burst_i,
        input logic [           3:0] src_cache_i, dst_cache_i,
        input logic                  decouple_rw_i,
        input logic                  deburst_i,
        input logic                  serialize_i
    );
        logic [AddrWidth-1:0] read_addr,   write_addr;
        logic [AddrWidth-1:0] read_word,   write_word;
        logic [$clog2(AddrWidth):0] read_offset, write_offset;
        // perform the transfer
        for(int i = 0; i < num_bytes_i; i = i + 1) begin
            read_addr     = src_addr_i + i;
            write_addr    = dst_addr_i + i;
            read_word     = src_burst_i == 2'b00 ? src_addr_i >> $clog2(AddrWidth) : read_addr  >> $clog2(AddrWidth);
            write_word    = dst_burst_i == 2'b00 ? dst_addr_i >> $clog2(AddrWidth) : write_addr >> $clog2(AddrWidth);
            read_offset   = read_addr [$clog2(AddrWidth)-1:0];
            write_offset  = write_addr[$clog2(AddrWidth)-1:0];

            // do the read
            if (!osmium_memory.exists(read_word) === 1) begin
                osmium_memory[read_word].data = lfsr_osmium_q[784:273];
                //shift 513x
                repeat(513) begin
                    // next state
                    for (int i = 1; i < 785; i = i +1) lfsr_osmium_d[i-1] = lfsr_osmium_q[i];
                    lfsr_osmium_d[784] = lfsr_osmium_q[0];
                    lfsr_osmium_d[692] = lfsr_osmium_q[0] ^ lfsr_osmium_q[693];
                    lfsr_osmium_q      = lfsr_osmium_d;
                end
            end
            // do the write
            osmium_memory[write_word].bytes[write_offset] = osmium_memory[read_word].bytes[read_offset];
            // $display("W: %d - %d    R: %d - %d", write_word, write_offset, read_word, read_offset);
        end

    endtask

    task clear_osmium_memory ();
        osmium_memory.delete();
    endtask

    task reset_osmium_lfsr ();
        lfsr_osmium_q = 'hc0a232c162b2bab5b960668030f4efce27940bd0de965f0b8d4315f15b79704195e4e0a6b495fc269f65ae17e10e9ca98510fc143327a292b418597f9dd175fc91c3d61be287d5462a23e00fa7ae906ae9eb339ab5225021356138cd46b6e5a73540c5591116b6b5e08d2c0e54eaf0d5143b33b2186b6cf841c076a98c412a63981f0e323dce93481ed1c37e4f1d7553b6c2fba1a3af6c3ad88b15ad58812ba07d1753917ac4e6ab1e8c4f67a47b4b0f48a34f42a52c546e979f4e4968e80a732a0a5e7a51146cf08482f349f94336752b765c0b1d70803d883d5058d127264335213da4163c62f65a4e65501b90fa5f177675c0747cfca328e131bfb3f7bcc5c27680c7bf86491f4ed3d36c25531edfa74b1e32fafe426958ae356eb8ef0fd818eaca4227a667b7c934ebfa282ab6bfc6db89b927c91a41e63a9554dced774f30268d0725a1a565368703b9f81d5c027ba196ef8b803a51c639c7ead834e1d6bc537d33800fe5eb12f1ed67758f1dfe85ffdbae56e8ef27f2ecedcee75b8dbb5f5f1a629ba3b755;
    endtask

    //--------------------------------------
    // Compare Memory content
    //--------------------------------------
    task compare_memories ();

        // go through osmium memory and compare contents
        foreach(osmium_memory[i]) begin
            if (osmium_memory[i] !== dma_memory[i]) $fatal("Memory mismatch @ %x\nexpect: %x\ngot   :%x\n", i << $clog2(AddrWidth), osmium_memory[i], dma_memory[i]);
        end
        // go through dma memory and compare contents
        foreach(dma_memory[i]) begin
            if (osmium_memory[i] !== dma_memory[i]) $fatal("Memory mismatch @ %x\nexpect: %x\ngot   :%x\n", i << $clog2(AddrWidth), osmium_memory[i], dma_memory[i]);
        end

        // it worked :P
        $display(" - :D");

    endtask

    //--------------------------------------
    // Master tasks
    //--------------------------------------

    task clear_memory ();
        clear_dut_memory();
        clear_osmium_memory();
    endtask

    task reset_lfsr ();
        reset_dut_lfsr();
        reset_osmium_lfsr();
    endtask

    task oned_launch_3 (
        input logic [   IdWidth-1:0] transf_id_i,
        input logic [ AddrWidth-1:0] src_addr_i,  dst_addr_i,  num_bytes_i,
        input logic                  decouple_rw_i,
        input logic                  deburst_i,
        input logic                  serialize_i,
        input logic                  wait_for_completion_i
    );
        // keep a log file
        int my_file;
        my_file = $fopen("dma3_transfers.txt", "a+");
        $write("ID: %d  SRC: 0x%x  DST: 0x%x  LEN: %d  DECOUPLE: %1b DEBURST: %1b SERIALIZE: %1b\n", transf_id_i, src_addr_i, dst_addr_i, num_bytes_i, decouple_rw_i, deburst_i, serialize_i );
        $fwrite (my_file, "ID: %d  SRC: 0x%x  DST: 0x%x  LEN: %d  DECOUPLE: %1b DEBURST: %1b SERIALIZE: %1b\n", transf_id_i, src_addr_i, dst_addr_i, num_bytes_i, decouple_rw_i, deburst_i, serialize_i );
        $fclose(my_file);

        // cache and burst is ignored
        oned_dut_launch_3(transf_id_i, src_addr_i, dst_addr_i, num_bytes_i, 2'b01, 2'b01, 4'h0, 4'h0, decouple_rw_i, deburst_i, serialize_i);
        // wait if requested
        if (wait_for_completion_i)
            wait_for_dut_completion();
        // run model
        //oned_osmium_launch(transf_id_i, src_addr_i, dst_addr_i, num_bytes_i, 2'b01, 2'b01, 4'h0, 4'h0, decouple_rw_i, deburst_i, serialize_i);
    endtask

    task oned_launch_2 (
        input logic [   IdWidth-1:0] transf_id_i,
        input logic [ AddrWidth-1:0] src_addr_i,  dst_addr_i,  num_bytes_i,
        input logic                  decouple_rw_i,
        input logic                  deburst_i,
        input logic                  serialize_i,
        input logic                  wait_for_completion_i
    );
        // keep a log file
        int my_file;
        my_file = $fopen("dma2_transfers.txt", "a+");
        $write("ID: %d  SRC: 0x%x  DST: 0x%x  LEN: %d  DECOUPLE: %1b DEBURST: %1b SERIALIZE: %1b\n", transf_id_i, src_addr_i, dst_addr_i, num_bytes_i, decouple_rw_i, deburst_i, serialize_i );
        $fwrite (my_file, "ID: %d  SRC: 0x%x  DST: 0x%x  LEN: %d  DECOUPLE: %1b DEBURST: %1b SERIALIZE: %1b\n", transf_id_i, src_addr_i, dst_addr_i, num_bytes_i, decouple_rw_i, deburst_i, serialize_i );
        $fclose(my_file);

        // cache and burst is ignored
        oned_dut_launch_2(transf_id_i, src_addr_i, dst_addr_i, num_bytes_i, 2'b01, 2'b01, 4'h0, 4'h0, decouple_rw_i, deburst_i, serialize_i);
        // wait if requested
        if (wait_for_completion_i)
            wait_for_dut_completion();
        // run model
        //oned_osmium_launch(transf_id_i, src_addr_i, dst_addr_i, num_bytes_i, 2'b01, 2'b01, 4'h0, 4'h0, decouple_rw_i, deburst_i, serialize_i);
    endtask

    task oned_launch_1 (
        input logic [   IdWidth-1:0] transf_id_i,
        input logic [ AddrWidth-1:0] src_addr_i,  dst_addr_i,  num_bytes_i,
        input logic                  decouple_rw_i,
        input logic                  deburst_i,
        input logic                  serialize_i,
        input logic                  wait_for_completion_i
    );
        // keep a log file
        int my_file;
        my_file = $fopen("dma1_transfers.txt", "a+");
        $write("ID: %d  SRC: 0x%x  DST: 0x%x  LEN: %d  DECOUPLE: %1b DEBURST: %1b SERIALIZE: %1b\n", transf_id_i, src_addr_i, dst_addr_i, num_bytes_i, decouple_rw_i, deburst_i, serialize_i );
        $fwrite (my_file, "ID: %d  SRC: 0x%x  DST: 0x%x  LEN: %d  DECOUPLE: %1b DEBURST: %1b SERIALIZE: %1b\n", transf_id_i, src_addr_i, dst_addr_i, num_bytes_i, decouple_rw_i, deburst_i, serialize_i );
        $fclose(my_file);

        // cache and burst is ignored
        oned_dut_launch_1(transf_id_i, src_addr_i, dst_addr_i, num_bytes_i, 2'b01, 2'b01, 4'h0, 4'h0, decouple_rw_i, deburst_i, serialize_i);
        // wait if requested
        if (wait_for_completion_i)
            wait_for_dut_completion();
        // run model
        //oned_osmium_launch(transf_id_i, src_addr_i, dst_addr_i, num_bytes_i, 2'b01, 2'b01, 4'h0, 4'h0, decouple_rw_i, deburst_i, serialize_i);
    endtask

    task oned_launch_0 (
        input logic [   IdWidth-1:0] transf_id_i,
        input logic [ AddrWidth-1:0] src_addr_i,  dst_addr_i,  num_bytes_i,
        input logic                  decouple_rw_i,
        input logic                  deburst_i,
        input logic                  serialize_i,
        input logic                  wait_for_completion_i
    );
        // keep a log file
        int my_file;
        my_file = $fopen("dma0_transfers.txt", "a+");
        $write("ID: %d  SRC: 0x%x  DST: 0x%x  LEN: %d  DECOUPLE: %1b DEBURST: %1b SERIALIZE: %1b\n", transf_id_i, src_addr_i, dst_addr_i, num_bytes_i, decouple_rw_i, deburst_i, serialize_i );
        $fwrite (my_file, "ID: %d  SRC: 0x%x  DST: 0x%x  LEN: %d  DECOUPLE: %1b DEBURST: %1b SERIALIZE: %1b\n", transf_id_i, src_addr_i, dst_addr_i, num_bytes_i, decouple_rw_i, deburst_i, serialize_i );
        $fclose(my_file);

        // cache and burst is ignored
        oned_dut_launch_0(transf_id_i, src_addr_i, dst_addr_i, num_bytes_i, 2'b01, 2'b01, 4'h0, 4'h0, decouple_rw_i, deburst_i, serialize_i);
        // wait if requested
        if (wait_for_completion_i)
            wait_for_dut_completion();
        // run model
        //oned_osmium_launch(transf_id_i, src_addr_i, dst_addr_i, num_bytes_i, 2'b01, 2'b01, 4'h0, 4'h0, decouple_rw_i, deburst_i, serialize_i);
    endtask

    task reset ();
        int my_file;
        oned_reset();
        wait_for_reset();
        // clear trace file
        my_file = $fopen("dma_transfers.txt", "w");
        $fwrite(my_file, "Transfers launched:\n");
        $fclose(my_file);
    endtask

    task oned_random_launch(
        input  logic [15:0] max_len,
        input  logic [31:0] src_add,
        input  logic [31:0] dst_add,
        input  logic [15:0] master_id,
        input  logic [15:0] size,
        input  logic        wait_for_completion
    );

        logic [   IdWidth-1:0] transf_id_0;
        logic [ AddrWidth-1:0] src_addr_0,  dst_addr_0,  num_bytes_0;
        logic [   IdWidth-1:0] transf_id_1;
        logic [ AddrWidth-1:0] src_addr_1,  dst_addr_1,  num_bytes_1;
        logic [   IdWidth-1:0] transf_id_2;
        logic [ AddrWidth-1:0] src_addr_2,  dst_addr_2,  num_bytes_2;
        logic [   IdWidth-1:0] transf_id_3;
        logic [ AddrWidth-1:0] src_addr_3,  dst_addr_3,  num_bytes_3;
        logic                  decouple_rw;
        logic                  deburst;
        logic                  serialize;

        decouple_rw       = 0;//$urandom();
        deburst           = 0;//$urandom();
        serialize         = 0;//$urandom();

        if (master_id == 0) begin
            transf_id_0         = 0;//$urandom();
            // transf_id         = transaction_id;
            //src_addr_0[AddrWidth-1:(AddrWidth/2)]   = $urandom();
            //src_addr_0[(AddrWidth/2)-1: 0]   = $urandom();
            //dst_addr_0[AddrWidth-1:(AddrWidth/2)]   = $urandom();
            //dst_addr_0[(AddrWidth/2)-1: 0]   = $urandom();
            num_bytes_0         = 0;
            num_bytes_0[15: 0]  = size;
            src_addr_0 = src_add;
            dst_addr_0 = dst_add;

            oned_launch_0(transf_id_0, src_addr_0, dst_addr_0, num_bytes_0, decouple_rw, deburst, serialize, wait_for_completion);

        end else if (master_id == 1) begin
            transf_id_1         = 1;//$urandom();
            // transf_id         = transaction_id;
            //src_addr_1[AddrWidth-1:(AddrWidth/2)]   = $urandom();
            //src_addr_1[(AddrWidth/2)-1: 0]   = $urandom();
            //dst_addr_1[AddrWidth-1:(AddrWidth/2)]   = $urandom();
            //dst_addr_1[(AddrWidth/2)-1: 0]   = $urandom();
            num_bytes_1         = 0;
            num_bytes_1[15: 0]  = size;
            src_addr_1 = src_add;
            dst_addr_1 = dst_add;

            oned_launch_1(transf_id_1, src_addr_1, dst_addr_1, num_bytes_1, decouple_rw, deburst, serialize, wait_for_completion);

        end else if (master_id == 2) begin
            transf_id_2         = 2;//$urandom();
            // transf_id         = transaction_id;
            //src_addr_1[AddrWidth-1:(AddrWidth/2)]   = $urandom();
            //src_addr_1[(AddrWidth/2)-1: 0]   = $urandom();
            //dst_addr_1[AddrWidth-1:(AddrWidth/2)]   = $urandom();
            //dst_addr_1[(AddrWidth/2)-1: 0]   = $urandom();
            num_bytes_2         = 0;
            num_bytes_2[15: 0]  = size;
            src_addr_2 = src_add;
            dst_addr_2 = dst_add;

            oned_launch_2(transf_id_2, src_addr_2, dst_addr_2, num_bytes_2, decouple_rw, deburst, serialize, wait_for_completion);

        end else if (master_id == 3) begin
            transf_id_3         = 3;//$urandom();
            // transf_id         = transaction_id;
            //src_addr_1[AddrWidth-1:(AddrWidth/2)]   = $urandom();
            //src_addr_1[(AddrWidth/2)-1: 0]   = $urandom();
            //dst_addr_1[AddrWidth-1:(AddrWidth/2)]   = $urandom();
            //dst_addr_1[(AddrWidth/2)-1: 0]   = $urandom();
            num_bytes_3         = 0;
            num_bytes_3[15: 0]  = size;
            src_addr_3 = src_add;
            dst_addr_3 = dst_add;

            oned_launch_3(transf_id_3, src_addr_3, dst_addr_3, num_bytes_3, decouple_rw, deburst, serialize, wait_for_completion);

        end

        // transaction_id    = transaction_id + 1;
        

    endtask

endmodule : fixture_axi_dma_backend
