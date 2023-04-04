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
    `define MASTERS_16
    `define MEM_DEBUG 1
    `include "axi/assign.svh"
    `include "axi/typedef.svh"

    //--------------------------------------
    // Parameters
    //--------------------------------------
    localparam TA          = 0.2ns;  // must be nonzero to avoid Snitch load fifo double pop glitch
    localparam TT          = 0.8ns;
    localparam HalfPeriod  = 5ns;
    localparam Reset       = 7.5ns;

    localparam DataWidth   = 32;
    localparam AddrWidth   = 32;
    localparam StrbWidth   = DataWidth / 8;
    localparam IdWidth     = 6;
    localparam UserWidth   = 1;

    // DUT parameters
    localparam bit  ATOPs = 0;
    localparam int unsigned NoMst = 16;
    localparam int unsigned NoSlv = 16;
    localparam int unsigned NoSlvPorts_2 = 5;
    localparam int unsigned NoMstPorts_2 = 5;
    localparam int unsigned NoSlvPorts_1 = 4;
    localparam int unsigned NoMstPorts_1 = 4;
    localparam int unsigned NoSlvPorts_0 = 3;
    localparam int unsigned NoMstPorts_0 = 3;
    localparam bit [NoSlvPorts_2-1:0][NoMstPorts_2-1:0] Connectivity_2 = {5'h1f,5'h1f,5'h1f,5'h1f,5'h1f};
    localparam bit [NoSlvPorts_1-1:0][NoMstPorts_1-1:0] Connectivity_1 = {4'hf,4'hf,4'hf,4'hf};
    localparam bit [NoSlvPorts_0-1:0][NoMstPorts_0-1:0] Connectivity_0 = '1;//{3'h6,3'h6,3'h6};
    localparam int unsigned AxiSlvPortMaxUniqIds = 32'd16;
    localparam int unsigned AxiSlvPortMaxTxnsPerId = 32'd128;
    localparam int unsigned AxiSlvPortMaxTxns = 32'd31;
    localparam int unsigned AxiMstPortMaxUniqIds = 32'd16;
    localparam int unsigned AxiMstPortMaxTxnsPerId = 32'd128;
    localparam int unsigned NoAddrRules_2 = 32'd5;
    localparam int unsigned NoAddrRules_1 = 32'd4;
    localparam int unsigned NoAddrRules_0 = 32'd3;

    typedef axi_pkg::xbar_rule_32_t       rule_t; // Has to be the same width as axi addr

    // axi configuration
    localparam int unsigned AxiIdWidthMasters =  IdWidth;
    localparam int unsigned AxiIdUsed         =  IdWidth-1; // Has to be <= AxiIdWidthMasters
    localparam int unsigned AxiIdWidthSlaves  =  AxiIdWidthMasters + $clog2(NoMstPorts_2);
    localparam int unsigned AxiAddrWidth      =  AddrWidth;    // Axi Address Width
    localparam int unsigned AxiDataWidth      =  DataWidth;    // Axi Data Width
    localparam int unsigned AxiStrbWidth      =  StrbWidth;
    localparam int unsigned AxiUserWidth      =  UserWidth;
    localparam int unsigned AxiIdWidth        =  IdWidth;

    // in the bench can change this variables which are set here freely
    localparam axi_pkg::xbar_cfg_t xbar_cfg_2 = '{
      NoSlvPorts:         NoMstPorts_2,
      NoMstPorts:         NoSlvPorts_2,
      MaxMstTrans:        AxiSlvPortMaxTxns,
      MaxSlvTrans:        AxiSlvPortMaxTxnsPerId,
      FallThrough:        1'b0,
      LatencyMode:        axi_pkg::CUT_ALL_PORTS,
      AxiIdWidthSlvPorts: AxiIdWidthMasters,
      AxiIdUsedSlvPorts:  AxiIdUsed,
      UniqueIds:          1'b0,
      AxiAddrWidth:       AxiAddrWidth,
      AxiDataWidth:       AxiDataWidth,
      NoAddrRules:        NoAddrRules_2
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

    // //////////////////////////////// All global accesses start //////////////////////////////////////

    // localparam rule_t [xbar_cfg_0.NoAddrRules-1:0] AddrMap_xp0 = '{
    //   '{idx: 32'd2 % NoSlvPorts_0, start_addr: {32'h0fffffff}, end_addr: {32'hffffffff}},
    //   '{idx: 32'd1 % NoSlvPorts_0, start_addr: {32'h000fffff}, end_addr: {32'h0fffffff}},
    //   '{idx: 32'd0 % NoSlvPorts_0, start_addr: {32'b0}, end_addr: {32'h000fffff}}
    //   //'{idx: 32'd0 % NoSlvPorts, start_addr: {AddrWidth{1'b0}}, end_addr: {(AddrWidth){1'b1}}}
    // };

    // localparam rule_t [xbar_cfg_1.NoAddrRules-1:0] AddrMap_xp1 = '{
    //   '{idx: 32'd3 % NoSlvPorts_1, start_addr: {32'h000000ff}, end_addr: {32'h0000ffff}},
    //   '{idx: 32'd2 % NoSlvPorts_1, start_addr: {32'h0000ffff}, end_addr: {32'h0fffffff}},
    //   '{idx: 32'd1 % NoSlvPorts_1, start_addr: {32'h0fffffff}, end_addr: {32'hffffffff}},
    //   '{idx: 32'd0 % NoSlvPorts_1, start_addr: {32'h00000000}, end_addr: {32'h000000ff}}
    //   //'{idx: 32'd0 % NoSlvPorts, start_addr: {AddrWidth{1'b0}}, end_addr: {(AddrWidth){1'b1}}}
    // };

    // // localparam rule_t [xbar_cfg_2.NoAddrRules-1:0] AddrMap_xp2 = '{
    // //   '{idx: 32'd4 % NoSlvPorts_2, start_addr: {32'b0}, end_addr: {32'h00000fff}},
    // //   '{idx: 32'd3 % NoSlvPorts_2, start_addr: {32'h00000fff}, end_addr: {32'h000fffff}},
    // //   '{idx: 32'd2 % NoSlvPorts_2, start_addr: {32'h000fffff}, end_addr: {32'h00ffffff}},
    // //   '{idx: 32'd1 % NoSlvPorts_2, start_addr: {32'h00ffffff}, end_addr: {32'h0fffffff}},
    // //   '{idx: 32'd0 % NoSlvPorts_2, start_addr: {32'h0fffffff}, end_addr: {32'hffffffff}}
    // //   //'{idx: 32'd0 % NoSlvPorts, start_addr: {AddrWidth{1'b0}}, end_addr: {(AddrWidth){1'b1}}}
    // // };

    // localparam rule_t [xbar_cfg_2.NoAddrRules-1:0] AddrMap_xp2_1 = '{
    //   '{idx: 32'd4 % NoSlvPorts_2, start_addr: {32'h00000000}, end_addr: {32'h000000ff}},
    //   '{idx: 32'd3 % NoSlvPorts_2, start_addr: {32'h000fffff}, end_addr: {32'hffffffff}},
    //   '{idx: 32'd2 % NoSlvPorts_2, start_addr: {32'h000000ff}, end_addr: {32'h00000fff}},
    //   '{idx: 32'd1 % NoSlvPorts_2, start_addr: {32'h00000fff}, end_addr: {32'h0000ffff}},
    //   '{idx: 32'd0 % NoSlvPorts_2, start_addr: {32'h0000ffff}, end_addr: {32'h000fffff}}
    //   //'{idx: 32'd0 % NoSlvPorts, start_addr: {AddrWidth{1'b0}}, end_addr: {(AddrWidth){1'b1}}}
    // };

    // localparam rule_t [xbar_cfg_2.NoAddrRules-1:0] AddrMap_xp2_2 = '{
    //   '{idx: 32'd4 % NoSlvPorts_2, start_addr: {32'h00000000}, end_addr: {32'h000000ff}},
    //   '{idx: 32'd3 % NoSlvPorts_2, start_addr: {32'h000000ff}, end_addr: {32'h00000fff}},
    //   '{idx: 32'd2 % NoSlvPorts_2, start_addr: {32'h00000fff}, end_addr: {32'h0000ffff}},
    //   '{idx: 32'd1 % NoSlvPorts_2, start_addr: {32'h0000ffff}, end_addr: {32'h000fffff}},
    //   '{idx: 32'd0 % NoSlvPorts_2, start_addr: {32'h000fffff}, end_addr: {32'hffffffff}}
    //   //'{idx: 32'd0 % NoSlvPorts, start_addr: {AddrWidth{1'b0}}, end_addr: {(AddrWidth){1'b1}}}
    // };

    // localparam rule_t [xbar_cfg_2.NoAddrRules-1:0] AddrMap_xp2_3 = '{
    //   '{idx: 32'd4 % NoSlvPorts_2, start_addr: {32'h000fffff}, end_addr: {32'hffffffff}},
    //   '{idx: 32'd3 % NoSlvPorts_2, start_addr: {32'h00000000}, end_addr: {32'h000000ff}},
    //   '{idx: 32'd2 % NoSlvPorts_2, start_addr: {32'h000000ff}, end_addr: {32'h00000fff}},
    //   '{idx: 32'd1 % NoSlvPorts_2, start_addr: {32'h00000fff}, end_addr: {32'h0000ffff}},
    //   '{idx: 32'd0 % NoSlvPorts_2, start_addr: {32'h0000ffff}, end_addr: {32'h000fffff}}
    //   //'{idx: 32'd0 % NoSlvPorts, start_addr: {AddrWidth{1'b0}}, end_addr: {(AddrWidth){1'b1}}}
    // };

    // //////////////////////////////// All global accesses end //////////////////////////////////////

    // //////////////////////////////// All local accesses start //////////////////////////////////////

    // localparam rule_t [xbar_cfg_0.NoAddrRules-1:0] AddrMap_xp0 = '{
    //   '{idx: 32'd2 % NoSlvPorts_0, start_addr: {32'h00000000}, end_addr: {32'h00000001}},
    //   '{idx: 32'd1 % NoSlvPorts_0, start_addr: {32'h00000001}, end_addr: {32'h00000002}},
    //   '{idx: 32'd0 % NoSlvPorts_0, start_addr: {32'h00000002}, end_addr: {32'hffffffff}}
    //   //'{idx: 32'd0 % NoSlvPorts, start_addr: {AddrWidth{1'b0}}, end_addr: {(AddrWidth){1'b1}}}
    // };

    // localparam rule_t [xbar_cfg_1.NoAddrRules-1:0] AddrMap_xp1 = '{
    //   '{idx: 32'd3 % NoSlvPorts_1, start_addr: {32'h00000000}, end_addr: {32'h000000ff}},
    //   '{idx: 32'd2 % NoSlvPorts_1, start_addr: {32'h000000ff}, end_addr: {32'h00000fff}},
    //   '{idx: 32'd1 % NoSlvPorts_1, start_addr: {32'h00000fff}, end_addr: {32'h0000ffff}},
    //   '{idx: 32'd0 % NoSlvPorts_1, start_addr: {32'h0000ffff}, end_addr: {32'hffffffff}}
    //   //'{idx: 32'd0 % NoSlvPorts, start_addr: {AddrWidth{1'b0}}, end_addr: {(AddrWidth){1'b1}}}
    // };

    // // localparam rule_t [xbar_cfg_2.NoAddrRules-1:0] AddrMap_xp2 = '{
    // //   '{idx: 32'd4 % NoSlvPorts_2, start_addr: {32'b0}, end_addr: {32'h00000fff}},
    // //   '{idx: 32'd3 % NoSlvPorts_2, start_addr: {32'h00000fff}, end_addr: {32'h000fffff}},
    // //   '{idx: 32'd2 % NoSlvPorts_2, start_addr: {32'h000fffff}, end_addr: {32'h00ffffff}},
    // //   '{idx: 32'd1 % NoSlvPorts_2, start_addr: {32'h00ffffff}, end_addr: {32'h0fffffff}},
    // //   '{idx: 32'd0 % NoSlvPorts_2, start_addr: {32'h0fffffff}, end_addr: {32'hffffffff}}
    // //   //'{idx: 32'd0 % NoSlvPorts, start_addr: {AddrWidth{1'b0}}, end_addr: {(AddrWidth){1'b1}}}
    // // };

    // localparam rule_t [xbar_cfg_2.NoAddrRules-1:0] AddrMap_xp2_1 = '{
    //   '{idx: 32'd4 % NoSlvPorts_2, start_addr: {32'h00000000}, end_addr: {32'h0000000f}},
    //   '{idx: 32'd3 % NoSlvPorts_2, start_addr: {32'h00000fff}, end_addr: {32'h0000ffff}},
    //   '{idx: 32'd2 % NoSlvPorts_2, start_addr: {32'h0000000f}, end_addr: {32'h000000ff}},
    //   '{idx: 32'd1 % NoSlvPorts_2, start_addr: {32'h000000ff}, end_addr: {32'h00000fff}},
    //   '{idx: 32'd0 % NoSlvPorts_2, start_addr: {32'h0000ffff}, end_addr: {32'hffffffff}}
    //   //'{idx: 32'd0 % NoSlvPorts, start_addr: {AddrWidth{1'b0}}, end_addr: {(AddrWidth){1'b1}}}
    // };

    // localparam rule_t [xbar_cfg_2.NoAddrRules-1:0] AddrMap_xp2_2 = '{
    //   '{idx: 32'd4 % NoSlvPorts_2, start_addr: {32'h00000000}, end_addr: {32'h0000000f}},
    //   '{idx: 32'd3 % NoSlvPorts_2, start_addr: {32'h0000000f}, end_addr: {32'h000000ff}},
    //   '{idx: 32'd2 % NoSlvPorts_2, start_addr: {32'h000000ff}, end_addr: {32'h00000fff}},
    //   '{idx: 32'd1 % NoSlvPorts_2, start_addr: {32'h00000fff}, end_addr: {32'h0000ffff}},
    //   '{idx: 32'd0 % NoSlvPorts_2, start_addr: {32'h0000ffff}, end_addr: {32'hffffffff}}
    //   //'{idx: 32'd0 % NoSlvPorts, start_addr: {AddrWidth{1'b0}}, end_addr: {(AddrWidth){1'b1}}}
    // };

    // localparam rule_t [xbar_cfg_2.NoAddrRules-1:0] AddrMap_xp2_3 = '{
    //   '{idx: 32'd4 % NoSlvPorts_2, start_addr: {32'h00000fff}, end_addr: {32'h0000ffff}},
    //   '{idx: 32'd3 % NoSlvPorts_2, start_addr: {32'h00000000}, end_addr: {32'h0000000f}},
    //   '{idx: 32'd2 % NoSlvPorts_2, start_addr: {32'h0000000f}, end_addr: {32'h000000ff}},
    //   '{idx: 32'd1 % NoSlvPorts_2, start_addr: {32'h000000ff}, end_addr: {32'h00000fff}},
    //   '{idx: 32'd0 % NoSlvPorts_2, start_addr: {32'h0000ffff}, end_addr: {32'hffffffff}}
    //   //'{idx: 32'd0 % NoSlvPorts, start_addr: {AddrWidth{1'b0}}, end_addr: {(AddrWidth){1'b1}}}
    // };

    // //////////////////////////////// All local accesses end //////////////////////////////////////

    // //////////////////////////////// Mixed accesses (max 2 hop) start //////////////////////////////////////

    // localparam rule_t [xbar_cfg_0.NoAddrRules-1:0] AddrMap_xp0 = '{
    //   '{idx: 32'd2 % NoSlvPorts_0, start_addr: {32'h0fffffff}, end_addr: {32'hffffffff}},
    //   '{idx: 32'd1 % NoSlvPorts_0, start_addr: {32'h0000ffff}, end_addr: {32'h0fffffff}},
    //   '{idx: 32'd0 % NoSlvPorts_0, start_addr: {32'b0}, end_addr: {32'h0000ffff}}
    //   //'{idx: 32'd0 % NoSlvPorts, start_addr: {AddrWidth{1'b0}}, end_addr: {(AddrWidth){1'b1}}}
    // };

    // localparam rule_t [xbar_cfg_1.NoAddrRules-1:0] AddrMap_xp1 = '{
    //   '{idx: 32'd3 % NoSlvPorts_1, start_addr: {32'h000000ff}, end_addr: {32'h0000ffff}},
    //   '{idx: 32'd2 % NoSlvPorts_1, start_addr: {32'h0000ffff}, end_addr: {32'h0fffffff}},
    //   '{idx: 32'd1 % NoSlvPorts_1, start_addr: {32'h0fffffff}, end_addr: {32'hffffffff}},
    //   '{idx: 32'd0 % NoSlvPorts_1, start_addr: {32'h00000000}, end_addr: {32'h000000ff}}
    //   //'{idx: 32'd0 % NoSlvPorts, start_addr: {AddrWidth{1'b0}}, end_addr: {(AddrWidth){1'b1}}}
    // };

    // // localparam rule_t [xbar_cfg_2.NoAddrRules-1:0] AddrMap_xp2 = '{
    // //   '{idx: 32'd4 % NoSlvPorts_2, start_addr: {32'b0}, end_addr: {32'h00000fff}},
    // //   '{idx: 32'd3 % NoSlvPorts_2, start_addr: {32'h00000fff}, end_addr: {32'h000fffff}},
    // //   '{idx: 32'd2 % NoSlvPorts_2, start_addr: {32'h000fffff}, end_addr: {32'h00ffffff}},
    // //   '{idx: 32'd1 % NoSlvPorts_2, start_addr: {32'h00ffffff}, end_addr: {32'h0fffffff}},
    // //   '{idx: 32'd0 % NoSlvPorts_2, start_addr: {32'h0fffffff}, end_addr: {32'hffffffff}}
    // //   //'{idx: 32'd0 % NoSlvPorts, start_addr: {AddrWidth{1'b0}}, end_addr: {(AddrWidth){1'b1}}}
    // // };

    // localparam rule_t [xbar_cfg_2.NoAddrRules-1:0] AddrMap_xp2_1 = '{
    //   '{idx: 32'd4 % NoSlvPorts_2, start_addr: {32'h00000000}, end_addr: {32'h0000000f}},
    //   '{idx: 32'd3 % NoSlvPorts_2, start_addr: {32'h00000fff}, end_addr: {32'h0000ffff}},
    //   '{idx: 32'd2 % NoSlvPorts_2, start_addr: {32'h0000000f}, end_addr: {32'h000000ff}},
    //   '{idx: 32'd1 % NoSlvPorts_2, start_addr: {32'h000000ff}, end_addr: {32'h00000fff}},
    //   '{idx: 32'd0 % NoSlvPorts_2, start_addr: {32'h0000ffff}, end_addr: {32'hffffffff}}
    //   //'{idx: 32'd0 % NoSlvPorts, start_addr: {AddrWidth{1'b0}}, end_addr: {(AddrWidth){1'b1}}}
    // };

    // localparam rule_t [xbar_cfg_2.NoAddrRules-1:0] AddrMap_xp2_2 = '{
    //   '{idx: 32'd4 % NoSlvPorts_2, start_addr: {32'h00000000}, end_addr: {32'h0000000f}},
    //   '{idx: 32'd3 % NoSlvPorts_2, start_addr: {32'h0000000f}, end_addr: {32'h000000ff}},
    //   '{idx: 32'd2 % NoSlvPorts_2, start_addr: {32'h000000ff}, end_addr: {32'h00000fff}},
    //   '{idx: 32'd1 % NoSlvPorts_2, start_addr: {32'h00000fff}, end_addr: {32'h0000ffff}},
    //   '{idx: 32'd0 % NoSlvPorts_2, start_addr: {32'h0000ffff}, end_addr: {32'hffffffff}}
    //   //'{idx: 32'd0 % NoSlvPorts, start_addr: {AddrWidth{1'b0}}, end_addr: {(AddrWidth){1'b1}}}
    // };

    // localparam rule_t [xbar_cfg_2.NoAddrRules-1:0] AddrMap_xp2_3 = '{
    //   '{idx: 32'd4 % NoSlvPorts_2, start_addr: {32'h00000fff}, end_addr: {32'h0000ffff}},
    //   '{idx: 32'd3 % NoSlvPorts_2, start_addr: {32'h00000000}, end_addr: {32'h0000000f}},
    //   '{idx: 32'd2 % NoSlvPorts_2, start_addr: {32'h0000000f}, end_addr: {32'h000000ff}},
    //   '{idx: 32'd1 % NoSlvPorts_2, start_addr: {32'h000000ff}, end_addr: {32'h00000fff}},
    //   '{idx: 32'd0 % NoSlvPorts_2, start_addr: {32'h0000ffff}, end_addr: {32'hffffffff}}
    //   //'{idx: 32'd0 % NoSlvPorts, start_addr: {AddrWidth{1'b0}}, end_addr: {(AddrWidth){1'b1}}}
    // };

    // //////////////////////////////// Mixed accesses (max 2 hop) end //////////////////////////////////////

    // //////////////////////////////// Mixed accesses (max 1 hop) start //////////////////////////////////////

    // localparam rule_t [xbar_cfg_0.NoAddrRules-1:0] AddrMap_xp0 = '{
    //   '{idx: 32'd2 % NoSlvPorts_0, start_addr: {32'h0fffffff}, end_addr: {32'hffffffff}},
    //   '{idx: 32'd1 % NoSlvPorts_0, start_addr: {32'h00000fff}, end_addr: {32'h0fffffff}},
    //   '{idx: 32'd0 % NoSlvPorts_0, start_addr: {32'h00000000}, end_addr: {32'h00000fff}}
    //   //'{idx: 32'd0 % NoSlvPorts, start_addr: {AddrWidth{1'b0}}, end_addr: {(AddrWidth){1'b1}}}
    // };

    // localparam rule_t [xbar_cfg_1.NoAddrRules-1:0] AddrMap_xp1 = '{
    //   '{idx: 32'd3 % NoSlvPorts_1, start_addr: {32'h0000000f}, end_addr: {32'h000000ff}},
    //   '{idx: 32'd2 % NoSlvPorts_1, start_addr: {32'h000000ff}, end_addr: {32'h00000fff}},
    //   '{idx: 32'd1 % NoSlvPorts_1, start_addr: {32'h00000000}, end_addr: {32'h0000000f}},
    //   '{idx: 32'd0 % NoSlvPorts_1, start_addr: {32'h00000fff}, end_addr: {32'hffffffff}}
    //   //'{idx: 32'd0 % NoSlvPorts, start_addr: {AddrWidth{1'b0}}, end_addr: {(AddrWidth){1'b1}}}
    // };

    // // localparam rule_t [xbar_cfg_2.NoAddrRules-1:0] AddrMap_xp2 = '{
    // //   '{idx: 32'd4 % NoSlvPorts_2, start_addr: {32'b0}, end_addr: {32'h00000fff}},
    // //   '{idx: 32'd3 % NoSlvPorts_2, start_addr: {32'h00000fff}, end_addr: {32'h000fffff}},
    // //   '{idx: 32'd2 % NoSlvPorts_2, start_addr: {32'h000fffff}, end_addr: {32'h00ffffff}},
    // //   '{idx: 32'd1 % NoSlvPorts_2, start_addr: {32'h00ffffff}, end_addr: {32'h0fffffff}},
    // //   '{idx: 32'd0 % NoSlvPorts_2, start_addr: {32'h0fffffff}, end_addr: {32'hffffffff}}
    // //   //'{idx: 32'd0 % NoSlvPorts, start_addr: {AddrWidth{1'b0}}, end_addr: {(AddrWidth){1'b1}}}
    // // };

    // localparam rule_t [xbar_cfg_2.NoAddrRules-1:0] AddrMap_xp2_1 = '{
    //   '{idx: 32'd4 % NoSlvPorts_2, start_addr: {32'h00000000}, end_addr: {32'h0000000f}},
    //   '{idx: 32'd3 % NoSlvPorts_2, start_addr: {32'h0000000f}, end_addr: {32'h000000ff}},
    //   '{idx: 32'd2 % NoSlvPorts_2, start_addr: {32'h00000fff}, end_addr: {32'h0000ffff}},
    //   '{idx: 32'd1 % NoSlvPorts_2, start_addr: {32'h0000ffff}, end_addr: {32'hffffffff}},
    //   '{idx: 32'd0 % NoSlvPorts_2, start_addr: {32'h000000ff}, end_addr: {32'h00000fff}}
    //   //'{idx: 32'd0 % NoSlvPorts, start_addr: {AddrWidth{1'b0}}, end_addr: {(AddrWidth){1'b1}}}
    // };

    // localparam rule_t [xbar_cfg_2.NoAddrRules-1:0] AddrMap_xp2_2 = '{
    //   '{idx: 32'd4 % NoSlvPorts_2, start_addr: {32'h00000000}, end_addr: {32'h0000000f}},
    //   '{idx: 32'd3 % NoSlvPorts_2, start_addr: {32'h0000000f}, end_addr: {32'h000000ff}},
    //   '{idx: 32'd2 % NoSlvPorts_2, start_addr: {32'h000000ff}, end_addr: {32'h00000fff}},
    //   '{idx: 32'd1 % NoSlvPorts_2, start_addr: {32'h0000ffff}, end_addr: {32'hffffffff}},
    //   '{idx: 32'd0 % NoSlvPorts_2, start_addr: {32'h00000fff}, end_addr: {32'h0000ffff}}
    //   //'{idx: 32'd0 % NoSlvPorts, start_addr: {AddrWidth{1'b0}}, end_addr: {(AddrWidth){1'b1}}}
    // };

    // localparam rule_t [xbar_cfg_2.NoAddrRules-1:0] AddrMap_xp2_3 = '{
    //   '{idx: 32'd4 % NoSlvPorts_2, start_addr: {32'h00000fff}, end_addr: {32'h0000ffff}},
    //   '{idx: 32'd3 % NoSlvPorts_2, start_addr: {32'h00000000}, end_addr: {32'h0000000f}},
    //   '{idx: 32'd2 % NoSlvPorts_2, start_addr: {32'h0000000f}, end_addr: {32'h000000ff}},
    //   '{idx: 32'd1 % NoSlvPorts_2, start_addr: {32'h0000ffff}, end_addr: {32'hffffffff}},
    //   '{idx: 32'd0 % NoSlvPorts_2, start_addr: {32'h000000ff}, end_addr: {32'h00000fff}}
    //   //'{idx: 32'd0 % NoSlvPorts, start_addr: {AddrWidth{1'b0}}, end_addr: {(AddrWidth){1'b1}}}
    // };

    // //////////////////////////////// Mixed accesses (max 1 hop) end //////////////////////////////////////

    //////////////////////////////// Uniform random start //////////////////////////////////////

    ////// row 1

    localparam rule_t [xbar_cfg_0.NoAddrRules-1:0] AddrMap_xp0 = '{
      '{idx: 32'd2 % NoSlvPorts_0, start_addr: {32'h00000000}, end_addr: {32'hc0000000}},
      '{idx: 32'd1 % NoSlvPorts_0, start_addr: {32'hd0000000}, end_addr: {32'hffffffff}},
      '{idx: 32'd0 % NoSlvPorts_0, start_addr: {32'hc0000000}, end_addr: {32'hd0000000}}
      //'{idx: 32'd0 % NoSlvPorts, start_addr: {AddrWidth{1'b0}}, end_addr: {(AddrWidth){1'b1}}}
    };

    localparam rule_t [xbar_cfg_1.NoAddrRules-1:0] AddrMap_xp1 = '{
      '{idx: 32'd3 % NoSlvPorts_1, start_addr: {32'he0000000}, end_addr: {32'hffffffff}},
      '{idx: 32'd2 % NoSlvPorts_1, start_addr: {32'h00000000}, end_addr: {32'hc0000000}},
      '{idx: 32'd1 % NoSlvPorts_1, start_addr: {32'hc0000000}, end_addr: {32'hd0000000}},
      '{idx: 32'd0 % NoSlvPorts_1, start_addr: {32'hd0000000}, end_addr: {32'he0000000}}
      //'{idx: 32'd0 % NoSlvPorts, start_addr: {AddrWidth{1'b0}}, end_addr: {(AddrWidth){1'b1}}}
    };

    localparam rule_t [xbar_cfg_1.NoAddrRules-1:0] AddrMap_xp2 = '{
      '{idx: 32'd3 % NoSlvPorts_1, start_addr: {32'hc0000000}, end_addr: {32'he0000000}},
      '{idx: 32'd2 % NoSlvPorts_1, start_addr: {32'h00000000}, end_addr: {32'hc0000000}},
      '{idx: 32'd1 % NoSlvPorts_1, start_addr: {32'hf0000000}, end_addr: {32'hffffffff}},
      '{idx: 32'd0 % NoSlvPorts_1, start_addr: {32'he0000000}, end_addr: {32'hf0000000}}
      //'{idx: 32'd0 % NoSlvPorts, start_addr: {AddrWidth{1'b0}}, end_addr: {(AddrWidth){1'b1}}}
    };

    localparam rule_t [xbar_cfg_0.NoAddrRules-1:0] AddrMap_xp3 = '{
      '{idx: 32'd2 % NoSlvPorts_0, start_addr: {32'h00000000}, end_addr: {32'hc0000000}},
      '{idx: 32'd1 % NoSlvPorts_0, start_addr: {32'hc0000000}, end_addr: {32'hf0000000}},
      '{idx: 32'd0 % NoSlvPorts_0, start_addr: {32'hf0000000}, end_addr: {32'hffffffff}}
      //'{idx: 32'd0 % NoSlvPorts, start_addr: {AddrWidth{1'b0}}, end_addr: {(AddrWidth){1'b1}}}
    };

    ////// row 2

    localparam rule_t [xbar_cfg_1.NoAddrRules-1:0] AddrMap_xp4 = '{
      '{idx: 32'd3 % NoSlvPorts_1, start_addr: {32'h00000000}, end_addr: {32'h80000000}},
      '{idx: 32'd2 % NoSlvPorts_1, start_addr: {32'hc0000000}, end_addr: {32'hffffffff}},
      '{idx: 32'd1 % NoSlvPorts_1, start_addr: {32'h90000000}, end_addr: {32'hc0000000}},
      '{idx: 32'd0 % NoSlvPorts_1, start_addr: {32'h80000000}, end_addr: {32'h90000000}}
      //'{idx: 32'd0 % NoSlvPorts, start_addr: {AddrWidth{1'b0}}, end_addr: {(AddrWidth){1'b1}}}
    };

    localparam rule_t [xbar_cfg_2.NoAddrRules-1:0] AddrMap_xp5 = '{
      '{idx: 32'd4 % NoSlvPorts_2, start_addr: {32'h00000000}, end_addr: {32'h80000000}},
      '{idx: 32'd3 % NoSlvPorts_2, start_addr: {32'ha0000000}, end_addr: {32'hc0000000}},
      '{idx: 32'd2 % NoSlvPorts_2, start_addr: {32'hc0000000}, end_addr: {32'hffffffff}},
      '{idx: 32'd1 % NoSlvPorts_2, start_addr: {32'h80000000}, end_addr: {32'h90000000}},
      '{idx: 32'd0 % NoSlvPorts_2, start_addr: {32'h90000000}, end_addr: {32'ha0000000}}
      //'{idx: 32'd0 % NoSlvPorts, start_addr: {AddrWidth{1'b0}}, end_addr: {(AddrWidth){1'b1}}}
    };

    localparam rule_t [xbar_cfg_2.NoAddrRules-1:0] AddrMap_xp6 = '{
      '{idx: 32'd4 % NoSlvPorts_2, start_addr: {32'h00000000}, end_addr: {32'h80000000}},
      '{idx: 32'd3 % NoSlvPorts_2, start_addr: {32'h80000000}, end_addr: {32'ha0000000}},
      '{idx: 32'd2 % NoSlvPorts_2, start_addr: {32'hc0000000}, end_addr: {32'hffffffff}},
      '{idx: 32'd1 % NoSlvPorts_2, start_addr: {32'hb0000000}, end_addr: {32'hc0000000}},
      '{idx: 32'd0 % NoSlvPorts_2, start_addr: {32'ha0000000}, end_addr: {32'hb0000000}}
      //'{idx: 32'd0 % NoSlvPorts, start_addr: {AddrWidth{1'b0}}, end_addr: {(AddrWidth){1'b1}}}
    };

    localparam rule_t [xbar_cfg_1.NoAddrRules-1:0] AddrMap_xp7 = '{
      '{idx: 32'd3 % NoSlvPorts_1, start_addr: {32'h00000000}, end_addr: {32'h80000000}},
      '{idx: 32'd2 % NoSlvPorts_1, start_addr: {32'hc0000000}, end_addr: {32'hffffffff}},
      '{idx: 32'd1 % NoSlvPorts_1, start_addr: {32'h80000000}, end_addr: {32'hb0000000}},
      '{idx: 32'd0 % NoSlvPorts_1, start_addr: {32'hb0000000}, end_addr: {32'hc0000000}}
      //'{idx: 32'd0 % NoSlvPorts, start_addr: {AddrWidth{1'b0}}, end_addr: {(AddrWidth){1'b1}}}
    };

    ////// row 3

    localparam rule_t [xbar_cfg_1.NoAddrRules-1:0] AddrMap_xp8 = '{
      '{idx: 32'd3 % NoSlvPorts_1, start_addr: {32'h80000000}, end_addr: {32'hffffffff}},
      '{idx: 32'd2 % NoSlvPorts_1, start_addr: {32'h00000000}, end_addr: {32'h40000000}},
      '{idx: 32'd1 % NoSlvPorts_1, start_addr: {32'h50000000}, end_addr: {32'h80000000}},
      '{idx: 32'd0 % NoSlvPorts_1, start_addr: {32'h40000000}, end_addr: {32'h50000000}}
      //'{idx: 32'd0 % NoSlvPorts, start_addr: {AddrWidth{1'b0}}, end_addr: {(AddrWidth){1'b1}}}
    };

    localparam rule_t [xbar_cfg_2.NoAddrRules-1:0] AddrMap_xp9 = '{
      '{idx: 32'd4 % NoSlvPorts_2, start_addr: {32'h80000000}, end_addr: {32'hffffffff}},
      '{idx: 32'd3 % NoSlvPorts_2, start_addr: {32'h60000000}, end_addr: {32'h80000000}},
      '{idx: 32'd2 % NoSlvPorts_2, start_addr: {32'h00000000}, end_addr: {32'h40000000}},
      '{idx: 32'd1 % NoSlvPorts_2, start_addr: {32'h40000000}, end_addr: {32'h50000000}},
      '{idx: 32'd0 % NoSlvPorts_2, start_addr: {32'h50000000}, end_addr: {32'h60000000}}
      //'{idx: 32'd0 % NoSlvPorts, start_addr: {AddrWidth{1'b0}}, end_addr: {(AddrWidth){1'b1}}}
    };

    localparam rule_t [xbar_cfg_2.NoAddrRules-1:0] AddrMap_xp10 = '{
      '{idx: 32'd4 % NoSlvPorts_2, start_addr: {32'h80000000}, end_addr: {32'hffffffff}},
      '{idx: 32'd3 % NoSlvPorts_2, start_addr: {32'h40000000}, end_addr: {32'h60000000}},
      '{idx: 32'd2 % NoSlvPorts_2, start_addr: {32'h00000000}, end_addr: {32'h40000000}},
      '{idx: 32'd1 % NoSlvPorts_2, start_addr: {32'h70000000}, end_addr: {32'h80000000}},
      '{idx: 32'd0 % NoSlvPorts_2, start_addr: {32'h60000000}, end_addr: {32'h70000000}}
      //'{idx: 32'd0 % NoSlvPorts, start_addr: {AddrWidth{1'b0}}, end_addr: {(AddrWidth){1'b1}}}
    };

    localparam rule_t [xbar_cfg_1.NoAddrRules-1:0] AddrMap_xp11 = '{
      '{idx: 32'd3 % NoSlvPorts_1, start_addr: {32'h80000000}, end_addr: {32'hffffffff}},
      '{idx: 32'd2 % NoSlvPorts_1, start_addr: {32'h00000000}, end_addr: {32'h40000000}},
      '{idx: 32'd1 % NoSlvPorts_1, start_addr: {32'h40000000}, end_addr: {32'h70000000}},
      '{idx: 32'd0 % NoSlvPorts_1, start_addr: {32'h70000000}, end_addr: {32'h80000000}}
      //'{idx: 32'd0 % NoSlvPorts, start_addr: {AddrWidth{1'b0}}, end_addr: {(AddrWidth){1'b1}}}
    };

    ////// row 4

    localparam rule_t [xbar_cfg_0.NoAddrRules-1:0] AddrMap_xp12 = '{
      '{idx: 32'd2 % NoSlvPorts_0, start_addr: {32'h40000000}, end_addr: {32'hffffffff}},
      '{idx: 32'd1 % NoSlvPorts_0, start_addr: {32'h10000000}, end_addr: {32'h40000000}},
      '{idx: 32'd0 % NoSlvPorts_0, start_addr: {32'h00000000}, end_addr: {32'h10000000}}
      //'{idx: 32'd0 % NoSlvPorts, start_addr: {AddrWidth{1'b0}}, end_addr: {(AddrWidth){1'b1}}}
    };

    localparam rule_t [xbar_cfg_1.NoAddrRules-1:0] AddrMap_xp13 = '{
      '{idx: 32'd3 % NoSlvPorts_1, start_addr: {32'h20000000}, end_addr: {32'h40000000}},
      '{idx: 32'd2 % NoSlvPorts_1, start_addr: {32'h40000000}, end_addr: {32'hffffffff}},
      '{idx: 32'd1 % NoSlvPorts_1, start_addr: {32'h00000000}, end_addr: {32'h10000000}},
      '{idx: 32'd0 % NoSlvPorts_1, start_addr: {32'h10000000}, end_addr: {32'h20000000}}
      //'{idx: 32'd0 % NoSlvPorts, start_addr: {AddrWidth{1'b0}}, end_addr: {(AddrWidth){1'b1}}}
    };

    localparam rule_t [xbar_cfg_1.NoAddrRules-1:0] AddrMap_xp14 = '{
      '{idx: 32'd3 % NoSlvPorts_1, start_addr: {32'h00000000}, end_addr: {32'h20000000}},
      '{idx: 32'd2 % NoSlvPorts_1, start_addr: {32'h40000000}, end_addr: {32'hffffffff}},
      '{idx: 32'd1 % NoSlvPorts_1, start_addr: {32'h30000000}, end_addr: {32'h40000000}},
      '{idx: 32'd0 % NoSlvPorts_1, start_addr: {32'h20000000}, end_addr: {32'h30000000}}
      //'{idx: 32'd0 % NoSlvPorts, start_addr: {AddrWidth{1'b0}}, end_addr: {(AddrWidth){1'b1}}}
    };

    localparam rule_t [xbar_cfg_0.NoAddrRules-1:0] AddrMap_xp15 = '{
      '{idx: 32'd2 % NoSlvPorts_0, start_addr: {32'h40000000}, end_addr: {32'hffffffff}},
      '{idx: 32'd1 % NoSlvPorts_0, start_addr: {32'h00000000}, end_addr: {32'h30000000}},
      '{idx: 32'd0 % NoSlvPorts_0, start_addr: {32'h30000000}, end_addr: {32'h40000000}}
      //'{idx: 32'd0 % NoSlvPorts, start_addr: {AddrWidth{1'b0}}, end_addr: {(AddrWidth){1'b1}}}
    };

    //////////////////////////////// Uniform random end //////////////////////////////////////

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

    ////////////////////////////////////////// Row 1 /////////////////////////////////////////

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp0_mst [NoMstPorts_0-1:0] ();

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
    ) xp0_slv [NoSlvPorts_0-1:0] ();

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

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp1_mst_3 [0:0] ();

    `AXI_ASSIGN (mem_0[1], xp1_mst[0])
    `AXI_ASSIGN (xp1_mst_1[0], xp1_mst[1])
    `AXI_ASSIGN (xp1_mst_2[0], xp1_mst[2])
    `AXI_ASSIGN (xp1_mst_3[0], xp1_mst[3])

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

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp1_slv_3 [0:0] ();

    `AXI_ASSIGN (xp1_slv[0], dma_sync[1])
    `AXI_ASSIGN (xp1_slv[1], xp1_slv_1[0])
    `AXI_ASSIGN (xp1_slv[2], xp1_slv_2[0])
    `AXI_ASSIGN (xp1_slv[3], xp1_slv_3[0])

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

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp2_mst_3 [0:0] ();

    `AXI_ASSIGN (mem_0[2], xp2_mst[0])
    `AXI_ASSIGN (xp2_mst_1[0], xp2_mst[1])
    `AXI_ASSIGN (xp2_mst_2[0], xp2_mst[2])
    `AXI_ASSIGN (xp2_mst_3[0], xp2_mst[3])

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

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp2_slv_3 [0:0] ();

    `AXI_ASSIGN (xp2_slv[0], dma_sync[2])
    `AXI_ASSIGN (xp2_slv[1], xp2_slv_1[0])
    `AXI_ASSIGN (xp2_slv[2], xp2_slv_2[0])
    `AXI_ASSIGN (xp2_slv[3], xp2_slv_3[0])

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp3_mst [NoMstPorts_0-1:0] ();

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
    ) xp3_slv [NoSlvPorts_0-1:0] ();

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

    /////////////////////////////////////////// Row 2 ////////////////////////////////////////////////

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp4_mst [NoMstPorts_1-1:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp4_mst_0 [0:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp4_mst_1 [0:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp4_mst_2 [0:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp4_mst_3 [0:0] ();

    `AXI_ASSIGN (mem_0[4], xp4_mst[0])
    `AXI_ASSIGN (xp4_mst_1[0], xp4_mst[1])
    `AXI_ASSIGN (xp4_mst_2[0], xp4_mst[2])
    `AXI_ASSIGN (xp4_mst_3[0], xp4_mst[3])

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp4_slv [NoSlvPorts_1-1:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp4_slv_0 [0:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp4_slv_1 [0:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp4_slv_2 [0:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp4_slv_3 [0:0] ();

    `AXI_ASSIGN (xp4_slv[0], dma_sync[4])
    `AXI_ASSIGN (xp4_slv[1], xp4_slv_1[0])
    `AXI_ASSIGN (xp4_slv[2], xp4_slv_2[0])
    `AXI_ASSIGN (xp4_slv[3], xp4_slv_3[0])

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp5_mst [NoMstPorts_2-1:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp5_mst_0 [0:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp5_mst_1 [0:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp5_mst_2 [0:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp5_mst_3 [0:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp5_mst_4 [0:0] ();

    `AXI_ASSIGN (mem_0[5], xp5_mst[0])
    `AXI_ASSIGN (xp5_mst_1[0], xp5_mst[1])
    `AXI_ASSIGN (xp5_mst_2[0], xp5_mst[2])
    `AXI_ASSIGN (xp5_mst_3[0], xp5_mst[3])
    `AXI_ASSIGN (xp5_mst_4[0], xp5_mst[4])

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp5_slv [NoSlvPorts_2-1:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp5_slv_0 [0:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp5_slv_1 [0:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp5_slv_2 [0:0] ();    

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp5_slv_3 [0:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp5_slv_4 [0:0] ();

    `AXI_ASSIGN (xp5_slv[0], dma_sync[5])
    `AXI_ASSIGN (xp5_slv[1], xp5_slv_1[0])
    `AXI_ASSIGN (xp5_slv[2], xp5_slv_2[0])
    `AXI_ASSIGN (xp5_slv[3], xp5_slv_3[0])
    `AXI_ASSIGN (xp5_slv[4], xp5_slv_4[0])

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp6_mst [NoMstPorts_2-1:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp6_mst_0 [0:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp6_mst_1 [0:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp6_mst_2 [0:0] ();    

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp6_mst_3 [0:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp6_mst_4 [0:0] ();

    `AXI_ASSIGN (mem_0[6], xp6_mst[0])
    `AXI_ASSIGN (xp6_mst_1[0], xp6_mst[1])
    `AXI_ASSIGN (xp6_mst_2[0], xp6_mst[2])
    `AXI_ASSIGN (xp6_mst_3[0], xp6_mst[3])
    `AXI_ASSIGN (xp6_mst_4[0], xp6_mst[4])

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp6_slv [NoSlvPorts_2-1:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp6_slv_0 [0:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp6_slv_1 [0:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp6_slv_2 [0:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp6_slv_3 [0:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp6_slv_4 [0:0] ();

    `AXI_ASSIGN (xp6_slv[0], dma_sync[6])
    `AXI_ASSIGN (xp6_slv[1], xp6_slv_1[0])
    `AXI_ASSIGN (xp6_slv[2], xp6_slv_2[0])
    `AXI_ASSIGN (xp6_slv[3], xp6_slv_3[0])
    `AXI_ASSIGN (xp6_slv[4], xp6_slv_4[0])

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp7_mst [NoMstPorts_1-1:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp7_mst_0 [0:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp7_mst_1 [0:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp7_mst_2 [0:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp7_mst_3 [0:0] ();

    `AXI_ASSIGN (mem_0[7], xp7_mst[0])
    `AXI_ASSIGN (xp7_mst_1[0], xp7_mst[1])
    `AXI_ASSIGN (xp7_mst_2[0], xp7_mst[2])
    `AXI_ASSIGN (xp7_mst_3[0], xp7_mst[3])

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp7_slv [NoSlvPorts_1-1:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp7_slv_0 [0:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp7_slv_1 [0:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp7_slv_2 [0:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp7_slv_3 [0:0] ();

    `AXI_ASSIGN (xp7_slv[0], dma_sync[7])
    `AXI_ASSIGN (xp7_slv[1], xp7_slv_1[0])
    `AXI_ASSIGN (xp7_slv[2], xp7_slv_2[0])
    `AXI_ASSIGN (xp7_slv[3], xp7_slv_3[0])

    /////////////////////////////////////////// Row 3 ////////////////////////////////////////////////

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp8_mst [NoMstPorts_1-1:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp8_mst_0 [0:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp8_mst_1 [0:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp8_mst_2 [0:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp8_mst_3 [0:0] ();

    `AXI_ASSIGN (mem_0[8], xp8_mst[0])
    `AXI_ASSIGN (xp8_mst_1[0], xp8_mst[1])
    `AXI_ASSIGN (xp8_mst_2[0], xp8_mst[2])
    `AXI_ASSIGN (xp8_mst_3[0], xp8_mst[3])

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp8_slv [NoSlvPorts_1-1:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp8_slv_0 [0:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp8_slv_1 [0:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp8_slv_2 [0:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp8_slv_3 [0:0] ();

    `AXI_ASSIGN (xp8_slv[0], dma_sync[8])
    `AXI_ASSIGN (xp8_slv[1], xp8_slv_1[0])
    `AXI_ASSIGN (xp8_slv[2], xp8_slv_2[0])
    `AXI_ASSIGN (xp8_slv[3], xp8_slv_3[0])

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp9_mst [NoMstPorts_2-1:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp9_mst_0 [0:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp9_mst_1 [0:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp9_mst_2 [0:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp9_mst_3 [0:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp9_mst_4 [0:0] ();

    `AXI_ASSIGN (mem_0[9], xp9_mst[0])
    `AXI_ASSIGN (xp9_mst_1[0], xp9_mst[1])
    `AXI_ASSIGN (xp9_mst_2[0], xp9_mst[2])
    `AXI_ASSIGN (xp9_mst_3[0], xp9_mst[3])
    `AXI_ASSIGN (xp9_mst_4[0], xp9_mst[4])

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp9_slv [NoSlvPorts_2-1:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp9_slv_0 [0:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp9_slv_1 [0:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp9_slv_2 [0:0] ();    

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp9_slv_3 [0:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp9_slv_4 [0:0] ();

    `AXI_ASSIGN (xp9_slv[0], dma_sync[9])
    `AXI_ASSIGN (xp9_slv[1], xp9_slv_1[0])
    `AXI_ASSIGN (xp9_slv[2], xp9_slv_2[0])
    `AXI_ASSIGN (xp9_slv[3], xp9_slv_3[0])
    `AXI_ASSIGN (xp9_slv[4], xp9_slv_4[0])

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp10_mst [NoMstPorts_2-1:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp10_mst_0 [0:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp10_mst_1 [0:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp10_mst_2 [0:0] ();    

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp10_mst_3 [0:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp10_mst_4 [0:0] ();

    `AXI_ASSIGN (mem_0[10], xp10_mst[0])
    `AXI_ASSIGN (xp10_mst_1[0], xp10_mst[1])
    `AXI_ASSIGN (xp10_mst_2[0], xp10_mst[2])
    `AXI_ASSIGN (xp10_mst_3[0], xp10_mst[3])
    `AXI_ASSIGN (xp10_mst_4[0], xp10_mst[4])

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp10_slv [NoSlvPorts_2-1:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp10_slv_0 [0:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp10_slv_1 [0:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp10_slv_2 [0:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp10_slv_3 [0:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp10_slv_4 [0:0] ();

    `AXI_ASSIGN (xp10_slv[0], dma_sync[10])
    `AXI_ASSIGN (xp10_slv[1], xp10_slv_1[0])
    `AXI_ASSIGN (xp10_slv[2], xp10_slv_2[0])
    `AXI_ASSIGN (xp10_slv[3], xp10_slv_3[0])
    `AXI_ASSIGN (xp10_slv[4], xp10_slv_4[0])

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp11_mst [NoMstPorts_1-1:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp11_mst_0 [0:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp11_mst_1 [0:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp11_mst_2 [0:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp11_mst_3 [0:0] ();

    `AXI_ASSIGN (mem_0[11], xp11_mst[0])
    `AXI_ASSIGN (xp11_mst_1[0], xp11_mst[1])
    `AXI_ASSIGN (xp11_mst_2[0], xp11_mst[2])
    `AXI_ASSIGN (xp11_mst_3[0], xp11_mst[3])

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp11_slv [NoSlvPorts_1-1:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp11_slv_0 [0:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp11_slv_1 [0:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp11_slv_2 [0:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp11_slv_3 [0:0] ();

    `AXI_ASSIGN (xp11_slv[0], dma_sync[11])
    `AXI_ASSIGN (xp11_slv[1], xp11_slv_1[0])
    `AXI_ASSIGN (xp11_slv[2], xp11_slv_2[0])
    `AXI_ASSIGN (xp11_slv[3], xp11_slv_3[0])

    ////////////////////////////////////////////// Row 4 ///////////////////////////////////////////

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp12_mst [NoMstPorts_0-1:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp12_mst_0 [0:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp12_mst_1 [0:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp12_mst_2 [0:0] ();

    `AXI_ASSIGN (mem_0[12], xp12_mst[0])
    `AXI_ASSIGN (xp12_mst_1[0], xp12_mst[1])
    `AXI_ASSIGN (xp12_mst_2[0], xp12_mst[2])

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp12_slv [NoSlvPorts_0-1:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp12_slv_0 [0:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp12_slv_1 [0:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp12_slv_2 [0:0] ();

    `AXI_ASSIGN (xp12_slv[0], dma_sync[12])
    `AXI_ASSIGN (xp12_slv[1], xp12_slv_1[0])
    `AXI_ASSIGN (xp12_slv[2], xp12_slv_2[0])

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp13_mst [NoMstPorts_1-1:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp13_mst_0 [0:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp13_mst_1 [0:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp13_mst_2 [0:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp13_mst_3 [0:0] ();

    `AXI_ASSIGN (mem_0[13], xp13_mst[0])
    `AXI_ASSIGN (xp13_mst_1[0], xp13_mst[1])
    `AXI_ASSIGN (xp13_mst_2[0], xp13_mst[2])
    `AXI_ASSIGN (xp13_mst_3[0], xp13_mst[3])

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp13_slv [NoSlvPorts_1-1:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp13_slv_0 [0:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp13_slv_1 [0:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp13_slv_2 [0:0] ();    

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp13_slv_3 [0:0] ();

    `AXI_ASSIGN (xp13_slv[0], dma_sync[13])
    `AXI_ASSIGN (xp13_slv[1], xp13_slv_1[0])
    `AXI_ASSIGN (xp13_slv[2], xp13_slv_2[0])
    `AXI_ASSIGN (xp13_slv[3], xp13_slv_3[0])

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp14_mst [NoMstPorts_1-1:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp14_mst_0 [0:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp14_mst_1 [0:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp14_mst_2 [0:0] ();    

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp14_mst_3 [0:0] ();

    `AXI_ASSIGN (mem_0[14], xp14_mst[0])
    `AXI_ASSIGN (xp14_mst_1[0], xp14_mst[1])
    `AXI_ASSIGN (xp14_mst_2[0], xp14_mst[2])
    `AXI_ASSIGN (xp14_mst_3[0], xp14_mst[3])

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp14_slv [NoSlvPorts_1-1:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp14_slv_0 [0:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp14_slv_1 [0:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp14_slv_2 [0:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp14_slv_3 [0:0] ();

    `AXI_ASSIGN (xp14_slv[0], dma_sync[14])
    `AXI_ASSIGN (xp14_slv[1], xp14_slv_1[0])
    `AXI_ASSIGN (xp14_slv[2], xp14_slv_2[0])
    `AXI_ASSIGN (xp14_slv[3], xp14_slv_3[0])

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp15_mst [NoMstPorts_0-1:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp15_mst_0 [0:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp15_mst_1 [0:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp15_mst_2 [0:0] ();

    `AXI_ASSIGN (mem_0[15], xp15_mst[0])
    `AXI_ASSIGN (xp15_mst_1[0], xp15_mst[1])
    `AXI_ASSIGN (xp15_mst_2[0], xp15_mst[2])

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp15_slv [NoSlvPorts_0-1:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp15_slv_0 [0:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp15_slv_1 [0:0] ();

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) xp15_slv_2 [0:0] ();

    `AXI_ASSIGN (xp15_slv[0], dma_sync[15])
    `AXI_ASSIGN (xp15_slv[1], xp15_slv_1[0])
    `AXI_ASSIGN (xp15_slv[2], xp15_slv_2[0])

    // XP0 <--> XP1

    `AXI_ASSIGN (xp1_slv_1[0], xp0_mst_1[0])
    `AXI_ASSIGN (xp0_slv_1[0], xp1_mst_1[0])

    // XP0 <--> XP4

    `AXI_ASSIGN (xp4_slv_2[0], xp0_mst_2[0])
    `AXI_ASSIGN (xp0_slv_2[0], xp4_mst_2[0])

    // XP1 <--> XP2

    `AXI_ASSIGN (xp2_slv_3[0], xp1_mst_3[0])
    `AXI_ASSIGN (xp1_slv_3[0], xp2_mst_3[0])

    // XP1 <--> XP5

    `AXI_ASSIGN (xp5_slv_2[0], xp1_mst_2[0])
    `AXI_ASSIGN (xp1_slv_2[0], xp5_mst_2[0])

    // XP2 <--> XP3

    `AXI_ASSIGN (xp2_slv_1[0], xp3_mst_1[0])
    `AXI_ASSIGN (xp3_slv_1[0], xp2_mst_1[0])

    // XP2 <--> XP6

    `AXI_ASSIGN (xp6_slv_2[0], xp2_mst_2[0])
    `AXI_ASSIGN (xp2_slv_2[0], xp6_mst_2[0])

    // XP3 <--> XP7

    `AXI_ASSIGN (xp7_slv_2[0], xp3_mst_2[0])
    `AXI_ASSIGN (xp3_slv_2[0], xp7_mst_2[0])

    // XP4 <--> XP5

    `AXI_ASSIGN (xp5_slv_1[0], xp4_mst_1[0])
    `AXI_ASSIGN (xp4_slv_1[0], xp5_mst_1[0])

    // XP4 <--> XP8

    `AXI_ASSIGN (xp8_slv_3[0], xp4_mst_3[0])
    `AXI_ASSIGN (xp4_slv_3[0], xp8_mst_3[0])

    // XP5 <--> XP6

    `AXI_ASSIGN (xp6_slv_3[0], xp5_mst_3[0])
    `AXI_ASSIGN (xp5_slv_3[0], xp6_mst_3[0])

    // XP5 <--> XP9

    `AXI_ASSIGN (xp9_slv_4[0], xp5_mst_4[0])
    `AXI_ASSIGN (xp5_slv_4[0], xp9_mst_4[0])

    // XP6 <--> XP7

    `AXI_ASSIGN (xp7_slv_1[0], xp6_mst_1[0])
    `AXI_ASSIGN (xp6_slv_1[0], xp7_mst_1[0])

    // XP6 <--> XP10

    `AXI_ASSIGN (xp10_slv_4[0], xp6_mst_4[0])
    `AXI_ASSIGN (xp6_slv_4[0], xp10_mst_4[0])

    // XP7 <--> XP11

    `AXI_ASSIGN (xp11_slv_3[0], xp7_mst_3[0])
    `AXI_ASSIGN (xp7_slv_3[0], xp11_mst_3[0])

    // XP8 <--> XP9

    `AXI_ASSIGN (xp9_slv_1[0], xp8_mst_1[0])
    `AXI_ASSIGN (xp8_slv_1[0], xp9_mst_1[0])

    // XP8 <--> XP12

    `AXI_ASSIGN (xp12_slv_2[0], xp8_mst_2[0])
    `AXI_ASSIGN (xp8_slv_2[0], xp12_mst_2[0])

    // XP9 <--> XP10

    `AXI_ASSIGN (xp10_slv_3[0], xp9_mst_3[0])
    `AXI_ASSIGN (xp9_slv_3[0], xp10_mst_3[0])

    // XP9 <--> XP13

    `AXI_ASSIGN (xp13_slv_2[0], xp9_mst_2[0])
    `AXI_ASSIGN (xp9_slv_2[0], xp13_mst_2[0])

    // XP10 <--> XP11

    `AXI_ASSIGN (xp11_slv_1[0], xp10_mst_1[0])
    `AXI_ASSIGN (xp10_slv_1[0], xp11_mst_1[0])

    // XP10 <--> XP14

    `AXI_ASSIGN (xp14_slv_2[0], xp10_mst_2[0])
    `AXI_ASSIGN (xp10_slv_2[0], xp14_mst_2[0])

    // XP11 <--> XP15

    `AXI_ASSIGN (xp15_slv_2[0], xp11_mst_2[0])
    `AXI_ASSIGN (xp11_slv_2[0], xp15_mst_2[0])

    // XP12 <--> XP13

    `AXI_ASSIGN (xp13_slv_1[0], xp12_mst_1[0])
    `AXI_ASSIGN (xp12_slv_1[0], xp13_mst_1[0])

    // XP13 <--> XP14

    `AXI_ASSIGN (xp14_slv_3[0], xp13_mst_3[0])
    `AXI_ASSIGN (xp13_slv_3[0], xp14_mst_3[0])

    // XP14 <--> XP15

    `AXI_ASSIGN (xp15_slv_1[0], xp14_mst_1[0])
    `AXI_ASSIGN (xp14_slv_1[0], xp15_mst_1[0])

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
    `AXI_ASSIGN (mem_dv[4], mem_0[4])
    `AXI_ASSIGN (mem_dv[5], mem_0[5])
    `AXI_ASSIGN (mem_dv[6], mem_0[6])
    `AXI_ASSIGN (mem_dv[7], mem_0[7])
    `AXI_ASSIGN (mem_dv[8], mem_0[8])
    `AXI_ASSIGN (mem_dv[9], mem_0[9])
    `AXI_ASSIGN (mem_dv[10], mem_0[10])
    `AXI_ASSIGN (mem_dv[11], mem_0[11])
    `AXI_ASSIGN (mem_dv[12], mem_0[12])
    `AXI_ASSIGN (mem_dv[13], mem_0[13])
    `AXI_ASSIGN (mem_dv[14], mem_0[14])
    `AXI_ASSIGN (mem_dv[15], mem_0[15])

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

    typedef axi_test::axi_driver #(
      .AW(AddrWidth), .DW(DataWidth), .IW(IdWidth), .UW(UserWidth),
      .TA(0.1*2*HalfPeriod), .TT(0.9*2*HalfPeriod)
    ) driver_dma4_t;

    typedef axi_test::axi_driver #(
      .AW(AddrWidth), .DW(DataWidth), .IW(IdWidth), .UW(UserWidth),
      .TA(0.1*2*HalfPeriod), .TT(0.9*2*HalfPeriod)
    ) driver_dma5_t;

    typedef axi_test::axi_driver #(
      .AW(AddrWidth), .DW(DataWidth), .IW(IdWidth), .UW(UserWidth),
      .TA(0.1*2*HalfPeriod), .TT(0.9*2*HalfPeriod)
    ) driver_dma6_t;

    typedef axi_test::axi_driver #(
      .AW(AddrWidth), .DW(DataWidth), .IW(IdWidth), .UW(UserWidth),
      .TA(0.1*2*HalfPeriod), .TT(0.9*2*HalfPeriod)
    ) driver_dma7_t;

    typedef axi_test::axi_driver #(
      .AW(AddrWidth), .DW(DataWidth), .IW(IdWidth), .UW(UserWidth),
      .TA(0.1*2*HalfPeriod), .TT(0.9*2*HalfPeriod)
    ) driver_dma8_t;

    typedef axi_test::axi_driver #(
      .AW(AddrWidth), .DW(DataWidth), .IW(IdWidth), .UW(UserWidth),
      .TA(0.1*2*HalfPeriod), .TT(0.9*2*HalfPeriod)
    ) driver_dma9_t;

    typedef axi_test::axi_driver #(
      .AW(AddrWidth), .DW(DataWidth), .IW(IdWidth), .UW(UserWidth),
      .TA(0.1*2*HalfPeriod), .TT(0.9*2*HalfPeriod)
    ) driver_dma10_t;

    typedef axi_test::axi_driver #(
      .AW(AddrWidth), .DW(DataWidth), .IW(IdWidth), .UW(UserWidth),
      .TA(0.1*2*HalfPeriod), .TT(0.9*2*HalfPeriod)
    ) driver_dma11_t;

    typedef axi_test::axi_driver #(
      .AW(AddrWidth), .DW(DataWidth), .IW(IdWidth), .UW(UserWidth),
      .TA(0.1*2*HalfPeriod), .TT(0.9*2*HalfPeriod)
    ) driver_dma12_t;

    typedef axi_test::axi_driver #(
      .AW(AddrWidth), .DW(DataWidth), .IW(IdWidth), .UW(UserWidth),
      .TA(0.1*2*HalfPeriod), .TT(0.9*2*HalfPeriod)
    ) driver_dma13_t;

    typedef axi_test::axi_driver #(
      .AW(AddrWidth), .DW(DataWidth), .IW(IdWidth), .UW(UserWidth),
      .TA(0.1*2*HalfPeriod), .TT(0.9*2*HalfPeriod)
    ) driver_dma14_t;

    typedef axi_test::axi_driver #(
      .AW(AddrWidth), .DW(DataWidth), .IW(IdWidth), .UW(UserWidth),
      .TA(0.1*2*HalfPeriod), .TT(0.9*2*HalfPeriod)
    ) driver_dma15_t;

    driver_dma_t driver_dma = new(mem_dv[0]);
    driver_dma1_t driver_dma1 = new(mem_dv[1]);
    driver_dma2_t driver_dma2 = new(mem_dv[2]);
    driver_dma3_t driver_dma3 = new(mem_dv[3]);
    driver_dma4_t driver_dma4 = new(mem_dv[4]);
    driver_dma5_t driver_dma5 = new(mem_dv[5]);
    driver_dma6_t driver_dma6 = new(mem_dv[6]);
    driver_dma7_t driver_dma7 = new(mem_dv[7]);
    driver_dma8_t driver_dma8 = new(mem_dv[8]);
    driver_dma9_t driver_dma9 = new(mem_dv[9]);
    driver_dma10_t driver_dma10 = new(mem_dv[10]);
    driver_dma11_t driver_dma11 = new(mem_dv[11]);
    driver_dma12_t driver_dma12 = new(mem_dv[12]);
    driver_dma13_t driver_dma13 = new(mem_dv[13]);
    driver_dma14_t driver_dma14 = new(mem_dv[14]);
    driver_dma15_t driver_dma15 = new(mem_dv[15]);

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

    axi_sim_mem_intf #(
      .AXI_ADDR_WIDTH      (AddrWidth),
      .AXI_DATA_WIDTH      (DataWidth),
      .AXI_ID_WIDTH        (IdWidth),
      .AXI_USER_WIDTH      (UserWidth),
      .WARN_UNINITIALIZED  (1'b0),
      .APPL_DELAY          (2ns),
      .ACQ_DELAY           (8ns)
    ) i_sim_mem4 (
      .clk_i   (clk),
      .rst_ni  (rst_n),
      .axi_slv (mem_dv[4])
    );

    axi_sim_mem_intf #(
      .AXI_ADDR_WIDTH      (AddrWidth),
      .AXI_DATA_WIDTH      (DataWidth),
      .AXI_ID_WIDTH        (IdWidth),
      .AXI_USER_WIDTH      (UserWidth),
      .WARN_UNINITIALIZED  (1'b0),
      .APPL_DELAY          (2ns), 
      .ACQ_DELAY           (8ns)
    ) i_sim_mem5 (
      .clk_i   (clk),
      .rst_ni  (rst_n),
      .axi_slv (mem_dv[5])
    );

    axi_sim_mem_intf #(
      .AXI_ADDR_WIDTH      (AddrWidth),
      .AXI_DATA_WIDTH      (DataWidth),
      .AXI_ID_WIDTH        (IdWidth),
      .AXI_USER_WIDTH      (UserWidth),
      .WARN_UNINITIALIZED  (1'b0),
      .APPL_DELAY          (2ns),
      .ACQ_DELAY           (8ns)
    ) i_sim_mem6 (
      .clk_i   (clk),
      .rst_ni  (rst_n),
      .axi_slv (mem_dv[6])
    );

    axi_sim_mem_intf #(
      .AXI_ADDR_WIDTH      (AddrWidth),
      .AXI_DATA_WIDTH      (DataWidth),
      .AXI_ID_WIDTH        (IdWidth),
      .AXI_USER_WIDTH      (UserWidth),
      .WARN_UNINITIALIZED  (1'b0),
      .APPL_DELAY          (2ns), 
      .ACQ_DELAY           (8ns)
    ) i_sim_mem7 (
      .clk_i   (clk),
      .rst_ni  (rst_n),
      .axi_slv (mem_dv[7])
    );

    axi_sim_mem_intf #(
      .AXI_ADDR_WIDTH      (AddrWidth),
      .AXI_DATA_WIDTH      (DataWidth),
      .AXI_ID_WIDTH        (IdWidth),
      .AXI_USER_WIDTH      (UserWidth),
      .WARN_UNINITIALIZED  (1'b0),
      .APPL_DELAY          (2ns),
      .ACQ_DELAY           (8ns)
    ) i_sim_mem8 (
      .clk_i   (clk),
      .rst_ni  (rst_n),
      .axi_slv (mem_dv[8])
    );

    axi_sim_mem_intf #(
      .AXI_ADDR_WIDTH      (AddrWidth),
      .AXI_DATA_WIDTH      (DataWidth),
      .AXI_ID_WIDTH        (IdWidth),
      .AXI_USER_WIDTH      (UserWidth),
      .WARN_UNINITIALIZED  (1'b0),
      .APPL_DELAY          (2ns), 
      .ACQ_DELAY           (8ns)
    ) i_sim_mem9 (
      .clk_i   (clk),
      .rst_ni  (rst_n),
      .axi_slv (mem_dv[9])
    );

    axi_sim_mem_intf #(
      .AXI_ADDR_WIDTH      (AddrWidth),
      .AXI_DATA_WIDTH      (DataWidth),
      .AXI_ID_WIDTH        (IdWidth),
      .AXI_USER_WIDTH      (UserWidth),
      .WARN_UNINITIALIZED  (1'b0),
      .APPL_DELAY          (2ns),
      .ACQ_DELAY           (8ns)
    ) i_sim_mem10 (
      .clk_i   (clk),
      .rst_ni  (rst_n),
      .axi_slv (mem_dv[10])
    );

    axi_sim_mem_intf #(
      .AXI_ADDR_WIDTH      (AddrWidth),
      .AXI_DATA_WIDTH      (DataWidth),
      .AXI_ID_WIDTH        (IdWidth),
      .AXI_USER_WIDTH      (UserWidth),
      .WARN_UNINITIALIZED  (1'b0),
      .APPL_DELAY          (2ns), 
      .ACQ_DELAY           (8ns)
    ) i_sim_mem11 (
      .clk_i   (clk),
      .rst_ni  (rst_n),
      .axi_slv (mem_dv[11])
    );

    axi_sim_mem_intf #(
      .AXI_ADDR_WIDTH      (AddrWidth),
      .AXI_DATA_WIDTH      (DataWidth),
      .AXI_ID_WIDTH        (IdWidth),
      .AXI_USER_WIDTH      (UserWidth),
      .WARN_UNINITIALIZED  (1'b0),
      .APPL_DELAY          (2ns),
      .ACQ_DELAY           (8ns)
    ) i_sim_mem12 (
      .clk_i   (clk),
      .rst_ni  (rst_n),
      .axi_slv (mem_dv[12])
    );

    axi_sim_mem_intf #(
      .AXI_ADDR_WIDTH      (AddrWidth),
      .AXI_DATA_WIDTH      (DataWidth),
      .AXI_ID_WIDTH        (IdWidth),
      .AXI_USER_WIDTH      (UserWidth),
      .WARN_UNINITIALIZED  (1'b0),
      .APPL_DELAY          (2ns), 
      .ACQ_DELAY           (8ns)
    ) i_sim_mem13 (
      .clk_i   (clk),
      .rst_ni  (rst_n),
      .axi_slv (mem_dv[13])
    );

    axi_sim_mem_intf #(
      .AXI_ADDR_WIDTH      (AddrWidth),
      .AXI_DATA_WIDTH      (DataWidth),
      .AXI_ID_WIDTH        (IdWidth),
      .AXI_USER_WIDTH      (UserWidth),
      .WARN_UNINITIALIZED  (1'b0),
      .APPL_DELAY          (2ns),
      .ACQ_DELAY           (8ns)
    ) i_sim_mem14 (
      .clk_i   (clk),
      .rst_ni  (rst_n),
      .axi_slv (mem_dv[14])
    );

    axi_sim_mem_intf #(
      .AXI_ADDR_WIDTH      (AddrWidth),
      .AXI_DATA_WIDTH      (DataWidth),
      .AXI_ID_WIDTH        (IdWidth),
      .AXI_USER_WIDTH      (UserWidth),
      .WARN_UNINITIALIZED  (1'b0),
      .APPL_DELAY          (2ns), 
      .ACQ_DELAY           (8ns)
    ) i_sim_mem15 (
      .clk_i   (clk),
      .rst_ni  (rst_n),
      .axi_slv (mem_dv[15])
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
    burst_req_t burst4_req;
    burst_req_t burst5_req;
    logic burst4_req_valid;
    logic burst5_req_valid;
    logic burst4_req_ready;
    logic burst5_req_ready;
    logic backend_idle_4;
    logic backend_idle_5;
    burst_req_t burst6_req;
    burst_req_t burst7_req;
    logic burst6_req_valid;
    logic burst7_req_valid;
    logic burst6_req_ready;
    logic burst7_req_ready;
    logic backend_idle_6;
    logic backend_idle_7;

    burst_req_t burst8_req;
    burst_req_t burst9_req;
    logic burst8_req_valid;
    logic burst9_req_valid;
    logic burst8_req_ready;
    logic burst9_req_ready;
    logic backend_idle_8;
    logic backend_idle_9;
    burst_req_t burst10_req;
    burst_req_t burst11_req;
    logic burst10_req_valid;
    logic burst11_req_valid;
    logic burst10_req_ready;
    logic burst11_req_ready;
    logic backend_idle_10;
    logic backend_idle_11;
    burst_req_t burst12_req;
    burst_req_t burst13_req;
    logic burst12_req_valid;
    logic burst13_req_valid;
    logic burst12_req_ready;
    logic burst13_req_ready;
    logic backend_idle_12;
    logic backend_idle_13;
    burst_req_t burst14_req;
    burst_req_t burst15_req;
    logic burst14_req_valid;
    logic burst15_req_valid;
    logic burst14_req_ready;
    logic burst15_req_ready;
    logic backend_idle_14;
    logic backend_idle_15;

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
    ) i_dut_axi_backend_4 (
        .clk_i              ( clk              ),
        .rst_ni             ( rst_n            ),
        .axi_dma_req_o      ( axi_dma_req[4]   ),
        .axi_dma_res_i      ( axi_dma_res[4]   ),
        .burst_req_i        ( burst4_req        ),
        .valid_i            ( burst4_req_valid  ),
        .ready_o            ( burst4_req_ready   ),
        .backend_idle_o     ( backend_idle_4     ),
        .trans_complete_o   ( ),
        .dma_id_i           ( 32'h00000004       )
    );

    axi_aw_w_sync_intf #(
        .AXI_ADDR_WIDTH ( AddrWidth ),
        .AXI_DATA_WIDTH ( DataWidth ),
        .AXI_ID_WIDTH   ( IdWidth   ),
        .AXI_USER_WIDTH ( UserWidth )
    ) i_aw_w_sync_intf_4 (
        .clk_i  ( clk            ),
        .rst_ni ( rst_n          ),
        .in     ( dma[4]         ),
        .out    ( dma_sync[4]    )
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
    ) i_dut_axi_backend_5 (
        .clk_i              ( clk              ),
        .rst_ni             ( rst_n            ),
        .axi_dma_req_o      ( axi_dma_req[5]   ),
        .axi_dma_res_i      ( axi_dma_res[5]   ),
        .burst_req_i        ( burst5_req        ),
        .valid_i            ( burst5_req_valid  ),
        .ready_o            ( burst5_req_ready  ),
        .backend_idle_o     ( backend_idle_5     ),
        .trans_complete_o   ( ),
        .dma_id_i           ( 32'h00000005       )
    );

    axi_aw_w_sync_intf #(
        .AXI_ADDR_WIDTH ( AddrWidth ),
        .AXI_DATA_WIDTH ( DataWidth ),
        .AXI_ID_WIDTH   ( IdWidth   ),
        .AXI_USER_WIDTH ( UserWidth )
    ) i_aw_w_sync_intf_5 (
        .clk_i  ( clk            ),
        .rst_ni ( rst_n          ),
        .in     ( dma[5]         ),
        .out    ( dma_sync[5]    )
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
    ) i_dut_axi_backend_6 (
        .clk_i              ( clk              ),
        .rst_ni             ( rst_n            ),
        .axi_dma_req_o      ( axi_dma_req[6]   ),
        .axi_dma_res_i      ( axi_dma_res[6]   ),
        .burst_req_i        ( burst6_req        ),
        .valid_i            ( burst6_req_valid  ),
        .ready_o            ( burst6_req_ready   ),
        .backend_idle_o     ( backend_idle_6     ),
        .trans_complete_o   ( ),
        .dma_id_i           ( 32'h00000006       )
    );

    axi_aw_w_sync_intf #(
        .AXI_ADDR_WIDTH ( AddrWidth ),
        .AXI_DATA_WIDTH ( DataWidth ),
        .AXI_ID_WIDTH   ( IdWidth   ),
        .AXI_USER_WIDTH ( UserWidth )
    ) i_aw_w_sync_intf_6 (
        .clk_i  ( clk            ),
        .rst_ni ( rst_n          ),
        .in     ( dma[6]         ),
        .out    ( dma_sync[6]    )
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
    ) i_dut_axi_backend_7 (
        .clk_i              ( clk              ),
        .rst_ni             ( rst_n            ),
        .axi_dma_req_o      ( axi_dma_req[7]   ),
        .axi_dma_res_i      ( axi_dma_res[7]   ),
        .burst_req_i        ( burst7_req        ),
        .valid_i            ( burst7_req_valid  ),
        .ready_o            ( burst7_req_ready  ),
        .backend_idle_o     ( backend_idle_7     ),
        .trans_complete_o   ( ),
        .dma_id_i           ( 32'h00000007       )
    );

    axi_aw_w_sync_intf #(
        .AXI_ADDR_WIDTH ( AddrWidth ),
        .AXI_DATA_WIDTH ( DataWidth ),
        .AXI_ID_WIDTH   ( IdWidth   ),
        .AXI_USER_WIDTH ( UserWidth )
    ) i_aw_w_sync_intf_7 (
        .clk_i  ( clk            ),
        .rst_ni ( rst_n          ),
        .in     ( dma[7]         ),
        .out    ( dma_sync[7]    )
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
    ) i_dut_axi_backend_8 (
        .clk_i              ( clk              ),
        .rst_ni             ( rst_n            ),
        .axi_dma_req_o      ( axi_dma_req[8]   ),
        .axi_dma_res_i      ( axi_dma_res[8]   ),
        .burst_req_i        ( burst8_req        ),
        .valid_i            ( burst8_req_valid  ),
        .ready_o            ( burst8_req_ready   ),
        .backend_idle_o     ( backend_idle_8     ),
        .trans_complete_o   ( ),
        .dma_id_i           ( 32'h00000008       )
    );

    axi_aw_w_sync_intf #(
        .AXI_ADDR_WIDTH ( AddrWidth ),
        .AXI_DATA_WIDTH ( DataWidth ),
        .AXI_ID_WIDTH   ( IdWidth   ),
        .AXI_USER_WIDTH ( UserWidth )
    ) i_aw_w_sync_intf_8 (
        .clk_i  ( clk            ),
        .rst_ni ( rst_n          ),
        .in     ( dma[8]         ),
        .out    ( dma_sync[8]    )
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
    ) i_dut_axi_backend_9 (
        .clk_i              ( clk              ),
        .rst_ni             ( rst_n            ),
        .axi_dma_req_o      ( axi_dma_req[9]   ),
        .axi_dma_res_i      ( axi_dma_res[9]   ),
        .burst_req_i        ( burst9_req        ),
        .valid_i            ( burst9_req_valid  ),
        .ready_o            ( burst9_req_ready  ),
        .backend_idle_o     ( backend_idle_9     ),
        .trans_complete_o   ( ),
        .dma_id_i           ( 32'h00000009       )
    );

    axi_aw_w_sync_intf #(
        .AXI_ADDR_WIDTH ( AddrWidth ),
        .AXI_DATA_WIDTH ( DataWidth ),
        .AXI_ID_WIDTH   ( IdWidth   ),
        .AXI_USER_WIDTH ( UserWidth )
    ) i_aw_w_sync_intf_9 (
        .clk_i  ( clk            ),
        .rst_ni ( rst_n          ),
        .in     ( dma[9]         ),
        .out    ( dma_sync[9]    )
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
    ) i_dut_axi_backend_10 (
        .clk_i              ( clk              ),
        .rst_ni             ( rst_n            ),
        .axi_dma_req_o      ( axi_dma_req[10]   ),
        .axi_dma_res_i      ( axi_dma_res[10]   ),
        .burst_req_i        ( burst10_req        ),
        .valid_i            ( burst10_req_valid  ),
        .ready_o            ( burst10_req_ready   ),
        .backend_idle_o     ( backend_idle_10     ),
        .trans_complete_o   ( ),
        .dma_id_i           ( 32'h0000000a       )
    );

    axi_aw_w_sync_intf #(
        .AXI_ADDR_WIDTH ( AddrWidth ),
        .AXI_DATA_WIDTH ( DataWidth ),
        .AXI_ID_WIDTH   ( IdWidth   ),
        .AXI_USER_WIDTH ( UserWidth )
    ) i_aw_w_sync_intf_10 (
        .clk_i  ( clk            ),
        .rst_ni ( rst_n          ),
        .in     ( dma[10]         ),
        .out    ( dma_sync[10]    )
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
    ) i_dut_axi_backend_11 (
        .clk_i              ( clk              ),
        .rst_ni             ( rst_n            ),
        .axi_dma_req_o      ( axi_dma_req[11]   ),
        .axi_dma_res_i      ( axi_dma_res[11]   ),
        .burst_req_i        ( burst11_req        ),
        .valid_i            ( burst11_req_valid  ),
        .ready_o            ( burst11_req_ready  ),
        .backend_idle_o     ( backend_idle_11     ),
        .trans_complete_o   ( ),
        .dma_id_i           ( 32'h0000000b       )
    );

    axi_aw_w_sync_intf #(
        .AXI_ADDR_WIDTH ( AddrWidth ),
        .AXI_DATA_WIDTH ( DataWidth ),
        .AXI_ID_WIDTH   ( IdWidth   ),
        .AXI_USER_WIDTH ( UserWidth )
    ) i_aw_w_sync_intf_11 (
        .clk_i  ( clk            ),
        .rst_ni ( rst_n          ),
        .in     ( dma[11]         ),
        .out    ( dma_sync[11]    )
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
    ) i_dut_axi_backend_12 (
        .clk_i              ( clk              ),
        .rst_ni             ( rst_n            ),
        .axi_dma_req_o      ( axi_dma_req[12]   ),
        .axi_dma_res_i      ( axi_dma_res[12]   ),
        .burst_req_i        ( burst12_req        ),
        .valid_i            ( burst12_req_valid  ),
        .ready_o            ( burst12_req_ready   ),
        .backend_idle_o     ( backend_idle_12     ),
        .trans_complete_o   ( ),
        .dma_id_i           ( 32'h0000000c       )
    );

    axi_aw_w_sync_intf #(
        .AXI_ADDR_WIDTH ( AddrWidth ),
        .AXI_DATA_WIDTH ( DataWidth ),
        .AXI_ID_WIDTH   ( IdWidth   ),
        .AXI_USER_WIDTH ( UserWidth )
    ) i_aw_w_sync_intf_12 (
        .clk_i  ( clk            ),
        .rst_ni ( rst_n          ),
        .in     ( dma[12]         ),
        .out    ( dma_sync[12]    )
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
    ) i_dut_axi_backend_13 (
        .clk_i              ( clk              ),
        .rst_ni             ( rst_n            ),
        .axi_dma_req_o      ( axi_dma_req[13]   ),
        .axi_dma_res_i      ( axi_dma_res[13]   ),
        .burst_req_i        ( burst13_req        ),
        .valid_i            ( burst13_req_valid  ),
        .ready_o            ( burst13_req_ready  ),
        .backend_idle_o     ( backend_idle_13     ),
        .trans_complete_o   ( ),
        .dma_id_i           ( 32'h0000000d       )
    );

    axi_aw_w_sync_intf #(
        .AXI_ADDR_WIDTH ( AddrWidth ),
        .AXI_DATA_WIDTH ( DataWidth ),
        .AXI_ID_WIDTH   ( IdWidth   ),
        .AXI_USER_WIDTH ( UserWidth )
    ) i_aw_w_sync_intf_13 (
        .clk_i  ( clk            ),
        .rst_ni ( rst_n          ),
        .in     ( dma[13]         ),
        .out    ( dma_sync[13]    )
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
    ) i_dut_axi_backend_14 (
        .clk_i              ( clk              ),
        .rst_ni             ( rst_n            ),
        .axi_dma_req_o      ( axi_dma_req[14]   ),
        .axi_dma_res_i      ( axi_dma_res[14]   ),
        .burst_req_i        ( burst14_req        ),
        .valid_i            ( burst14_req_valid  ),
        .ready_o            ( burst14_req_ready   ),
        .backend_idle_o     ( backend_idle_14     ),
        .trans_complete_o   ( ),
        .dma_id_i           ( 32'h0000000e       )
    );

    axi_aw_w_sync_intf #(
        .AXI_ADDR_WIDTH ( AddrWidth ),
        .AXI_DATA_WIDTH ( DataWidth ),
        .AXI_ID_WIDTH   ( IdWidth   ),
        .AXI_USER_WIDTH ( UserWidth )
    ) i_aw_w_sync_intf_14 (
        .clk_i  ( clk            ),
        .rst_ni ( rst_n          ),
        .in     ( dma[14]         ),
        .out    ( dma_sync[14]    )
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
    ) i_dut_axi_backend_15 (
        .clk_i              ( clk              ),
        .rst_ni             ( rst_n            ),
        .axi_dma_req_o      ( axi_dma_req[15]   ),
        .axi_dma_res_i      ( axi_dma_res[15]   ),
        .burst_req_i        ( burst15_req        ),
        .valid_i            ( burst15_req_valid  ),
        .ready_o            ( burst15_req_ready  ),
        .backend_idle_o     ( backend_idle_15     ),
        .trans_complete_o   ( ),
        .dma_id_i           ( 32'h0000000f       )
    );

    axi_aw_w_sync_intf #(
        .AXI_ADDR_WIDTH ( AddrWidth ),
        .AXI_DATA_WIDTH ( DataWidth ),
        .AXI_ID_WIDTH   ( IdWidth   ),
        .AXI_USER_WIDTH ( UserWidth )
    ) i_aw_w_sync_intf_15 (
        .clk_i  ( clk            ),
        .rst_ni ( rst_n          ),
        .in     ( dma[15]         ),
        .out    ( dma_sync[15]    )
    );

    //-----------------------------------
    // DUT
    //-----------------------------------

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
    ) i_xp_dut_15 (
      .clk_i                  ( clk          ),
      .rst_ni                 ( rst_n        ),
      .test_en_i              ( 1'b0         ),
      .slv_ports              ( xp15_slv      ),
      .mst_ports              ( xp15_mst      ),
      .addr_map_i             ( AddrMap_xp15  )
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
    ) i_xp_dut_14 (
      .clk_i                  ( clk          ),
      .rst_ni                 ( rst_n        ),
      .test_en_i              ( 1'b0         ),
      .slv_ports              ( xp14_slv      ),
      .mst_ports              ( xp14_mst      ),
      .addr_map_i             ( AddrMap_xp14  )
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
    ) i_xp_dut_13 (
      .clk_i                  ( clk          ),
      .rst_ni                 ( rst_n        ),
      .test_en_i              ( 1'b0         ),
      .slv_ports              ( xp13_slv      ),
      .mst_ports              ( xp13_mst      ),
      .addr_map_i             ( AddrMap_xp13  )
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
    ) i_xp_dut_12 (
      .clk_i                  ( clk          ),
      .rst_ni                 ( rst_n        ),
      .test_en_i              ( 1'b0         ),
      .slv_ports              ( xp12_slv      ),
      .mst_ports              ( xp12_mst      ),
      .addr_map_i             ( AddrMap_xp12  )
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
    ) i_xp_dut_11 (
      .clk_i                  ( clk          ),
      .rst_ni                 ( rst_n        ),
      .test_en_i              ( 1'b0         ),
      .slv_ports              ( xp11_slv      ),
      .mst_ports              ( xp11_mst      ),
      .addr_map_i             ( AddrMap_xp11  )
    );

    axi_xp_intf #(
      .ATOPs                   ( ATOPs         ),
      .Cfg                     ( xbar_cfg_2      ),
      .NoSlvPorts              ( xbar_cfg_2.NoSlvPorts    ),
      .NoMstPorts              ( xbar_cfg_2.NoMstPorts    ),
      .Connectivity            ( Connectivity_2  ),
      .AxiAddrWidth            ( AxiAddrWidth  ),
      .AxiDataWidth            ( AxiDataWidth  ),
      .AxiIdWidth              ( AxiIdWidth    ),
      .AxiUserWidth            ( AxiUserWidth  ),
      .AxiSlvPortMaxUniqIds    ( AxiSlvPortMaxUniqIds   ),
      .AxiSlvPortMaxTxnsPerId  ( AxiSlvPortMaxTxnsPerId ),
      .AxiSlvPortMaxTxns       ( AxiSlvPortMaxTxns      ),
      .AxiMstPortMaxUniqIds    ( AxiMstPortMaxUniqIds   ),
      .AxiMstPortMaxTxnsPerId  ( AxiMstPortMaxTxnsPerId ),
      .NoAddrRules             ( xbar_cfg_2.NoAddrRules   ),
      .rule_t                  ( rule_t                 )
    ) i_xp_dut_10 (
      .clk_i                  ( clk          ),
      .rst_ni                 ( rst_n        ),
      .test_en_i              ( 1'b0         ),
      .slv_ports              ( xp10_slv      ),
      .mst_ports              ( xp10_mst      ),
      .addr_map_i             ( AddrMap_xp10  )
    );

    axi_xp_intf #(
      .ATOPs                   ( ATOPs         ),
      .Cfg                     ( xbar_cfg_2      ),
      .NoSlvPorts              ( xbar_cfg_2.NoSlvPorts    ),
      .NoMstPorts              ( xbar_cfg_2.NoMstPorts    ),
      .Connectivity            ( Connectivity_2  ),
      .AxiAddrWidth            ( AxiAddrWidth  ),
      .AxiDataWidth            ( AxiDataWidth  ),
      .AxiIdWidth              ( AxiIdWidth    ),
      .AxiUserWidth            ( AxiUserWidth  ),
      .AxiSlvPortMaxUniqIds    ( AxiSlvPortMaxUniqIds   ),
      .AxiSlvPortMaxTxnsPerId  ( AxiSlvPortMaxTxnsPerId ),
      .AxiSlvPortMaxTxns       ( AxiSlvPortMaxTxns      ),
      .AxiMstPortMaxUniqIds    ( AxiMstPortMaxUniqIds   ),
      .AxiMstPortMaxTxnsPerId  ( AxiMstPortMaxTxnsPerId ),
      .NoAddrRules             ( xbar_cfg_2.NoAddrRules   ),
      .rule_t                  ( rule_t                 )
    ) i_xp_dut_9 (
      .clk_i                  ( clk          ),
      .rst_ni                 ( rst_n        ),
      .test_en_i              ( 1'b0         ),
      .slv_ports              ( xp9_slv      ),
      .mst_ports              ( xp9_mst      ),
      .addr_map_i             ( AddrMap_xp9  )
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
    ) i_xp_dut_8 (
      .clk_i                  ( clk          ),
      .rst_ni                 ( rst_n        ),
      .test_en_i              ( 1'b0         ),
      .slv_ports              ( xp8_slv      ),
      .mst_ports              ( xp8_mst      ),
      .addr_map_i             ( AddrMap_xp8  )
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
    ) i_xp_dut_7 (
      .clk_i                  ( clk          ),
      .rst_ni                 ( rst_n        ),
      .test_en_i              ( 1'b0         ),
      .slv_ports              ( xp7_slv      ),
      .mst_ports              ( xp7_mst      ),
      .addr_map_i             ( AddrMap_xp7  )
    );

    axi_xp_intf #(
      .ATOPs                   ( ATOPs         ),
      .Cfg                     ( xbar_cfg_2      ),
      .NoSlvPorts              ( xbar_cfg_2.NoSlvPorts    ),
      .NoMstPorts              ( xbar_cfg_2.NoMstPorts    ),
      .Connectivity            ( Connectivity_2  ),
      .AxiAddrWidth            ( AxiAddrWidth  ),
      .AxiDataWidth            ( AxiDataWidth  ),
      .AxiIdWidth              ( AxiIdWidth    ),
      .AxiUserWidth            ( AxiUserWidth  ),
      .AxiSlvPortMaxUniqIds    ( AxiSlvPortMaxUniqIds   ),
      .AxiSlvPortMaxTxnsPerId  ( AxiSlvPortMaxTxnsPerId ),
      .AxiSlvPortMaxTxns       ( AxiSlvPortMaxTxns      ),
      .AxiMstPortMaxUniqIds    ( AxiMstPortMaxUniqIds   ),
      .AxiMstPortMaxTxnsPerId  ( AxiMstPortMaxTxnsPerId ),
      .NoAddrRules             ( xbar_cfg_2.NoAddrRules   ),
      .rule_t                  ( rule_t                 )
    ) i_xp_dut_6 (
      .clk_i                  ( clk          ),
      .rst_ni                 ( rst_n        ),
      .test_en_i              ( 1'b0         ),
      .slv_ports              ( xp6_slv      ),
      .mst_ports              ( xp6_mst      ),
      .addr_map_i             ( AddrMap_xp6  )
    );

    axi_xp_intf #(
      .ATOPs                   ( ATOPs         ),
      .Cfg                     ( xbar_cfg_2      ),
      .NoSlvPorts              ( xbar_cfg_2.NoSlvPorts    ),
      .NoMstPorts              ( xbar_cfg_2.NoMstPorts    ),
      .Connectivity            ( Connectivity_2  ),
      .AxiAddrWidth            ( AxiAddrWidth  ),
      .AxiDataWidth            ( AxiDataWidth  ),
      .AxiIdWidth              ( AxiIdWidth    ),
      .AxiUserWidth            ( AxiUserWidth  ),
      .AxiSlvPortMaxUniqIds    ( AxiSlvPortMaxUniqIds   ),
      .AxiSlvPortMaxTxnsPerId  ( AxiSlvPortMaxTxnsPerId ),
      .AxiSlvPortMaxTxns       ( AxiSlvPortMaxTxns      ),
      .AxiMstPortMaxUniqIds    ( AxiMstPortMaxUniqIds   ),
      .AxiMstPortMaxTxnsPerId  ( AxiMstPortMaxTxnsPerId ),
      .NoAddrRules             ( xbar_cfg_2.NoAddrRules   ),
      .rule_t                  ( rule_t                 )
    ) i_xp_dut_5 (
      .clk_i                  ( clk          ),
      .rst_ni                 ( rst_n        ),
      .test_en_i              ( 1'b0         ),
      .slv_ports              ( xp5_slv      ),
      .mst_ports              ( xp5_mst      ),
      .addr_map_i             ( AddrMap_xp5  )
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
    ) i_xp_dut_4 (
      .clk_i                  ( clk          ),
      .rst_ni                 ( rst_n        ),
      .test_en_i              ( 1'b0         ),
      .slv_ports              ( xp4_slv      ),
      .mst_ports              ( xp4_mst      ),
      .addr_map_i             ( AddrMap_xp4  )
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
    ) i_xp_dut_3 (
      .clk_i                  ( clk          ),
      .rst_ni                 ( rst_n        ),
      .test_en_i              ( 1'b0         ),
      .slv_ports              ( xp3_slv      ),
      .mst_ports              ( xp3_mst      ),
      .addr_map_i             ( AddrMap_xp3  )
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

    task oned_dut_launch_15 (
        input logic [   IdWidth-1:0] transf_id_i,
        input logic [ AddrWidth-1:0] src_addr_i,  dst_addr_i,  num_bytes_i,
        input logic [           1:0] src_burst_i, dst_burst_i,
        input logic [           3:0] src_cache_i, dst_cache_i,
        input logic                  decouple_rw_i,
        input logic                  serialize_i,
        input logic                  deburst_i
    );
        burst15_req_valid        <= 1'b0;
        burst15_req              <=  '0;
        @(posedge clk);
        while (burst15_req_ready !== 1) @(posedge clk);
        // write data
        burst15_req.id           <= transf_id_i;
        burst15_req.src          <= src_addr_i;
        burst15_req.dst          <= dst_addr_i;
        burst15_req.num_bytes    <= num_bytes_i;
        burst15_req.cache_src    <= src_cache_i;
        burst15_req.cache_dst    <= dst_cache_i;
        burst15_req.burst_src    <= src_burst_i;
        burst15_req.burst_dst    <= dst_burst_i;
        burst15_req.decouple_rw  <= decouple_rw_i;
        burst15_req.deburst      <= deburst_i;
        burst15_req.serialize    <= serialize_i;
        burst15_req_valid        <= 1'b1;
        // wait and set to 0
        @(posedge clk);
        burst15_req_valid        <= 1'b0;
        burst15_req              <=  '0;
    endtask

    task oned_dut_launch_14 (
        input logic [   IdWidth-1:0] transf_id_i,
        input logic [ AddrWidth-1:0] src_addr_i,  dst_addr_i,  num_bytes_i,
        input logic [           1:0] src_burst_i, dst_burst_i,
        input logic [           3:0] src_cache_i, dst_cache_i,
        input logic                  decouple_rw_i,
        input logic                  serialize_i,
        input logic                  deburst_i
    );
        burst14_req_valid        <= 1'b0;
        burst14_req              <=  '0;
        @(posedge clk);
        while (burst14_req_ready !== 1) @(posedge clk);
        // write data
        burst14_req.id           <= transf_id_i;
        burst14_req.src          <= src_addr_i;
        burst14_req.dst          <= dst_addr_i;
        burst14_req.num_bytes    <= num_bytes_i;
        burst14_req.cache_src    <= src_cache_i;
        burst14_req.cache_dst    <= dst_cache_i;
        burst14_req.burst_src    <= src_burst_i;
        burst14_req.burst_dst    <= dst_burst_i;
        burst14_req.decouple_rw  <= decouple_rw_i;
        burst14_req.deburst      <= deburst_i;
        burst14_req.serialize    <= serialize_i;
        burst14_req_valid        <= 1'b1;
        // wait and set to 0
        @(posedge clk);
        burst14_req_valid        <= 1'b0;
        burst14_req              <=  '0;
    endtask

    task oned_dut_launch_13 (
        input logic [   IdWidth-1:0] transf_id_i,
        input logic [ AddrWidth-1:0] src_addr_i,  dst_addr_i,  num_bytes_i,
        input logic [           1:0] src_burst_i, dst_burst_i,
        input logic [           3:0] src_cache_i, dst_cache_i,
        input logic                  decouple_rw_i,
        input logic                  serialize_i,
        input logic                  deburst_i
    );
        burst13_req_valid        <= 1'b0;
        burst13_req              <=  '0;
        @(posedge clk);
        while (burst13_req_ready !== 1) @(posedge clk);
        // write data
        burst13_req.id           <= transf_id_i;
        burst13_req.src          <= src_addr_i;
        burst13_req.dst          <= dst_addr_i;
        burst13_req.num_bytes    <= num_bytes_i;
        burst13_req.cache_src    <= src_cache_i;
        burst13_req.cache_dst    <= dst_cache_i;
        burst13_req.burst_src    <= src_burst_i;
        burst13_req.burst_dst    <= dst_burst_i;
        burst13_req.decouple_rw  <= decouple_rw_i;
        burst13_req.deburst      <= deburst_i;
        burst13_req.serialize    <= serialize_i;
        burst13_req_valid        <= 1'b1;
        // wait and set to 0
        @(posedge clk);
        burst13_req_valid        <= 1'b0;
        burst13_req              <=  '0;
    endtask

    task oned_dut_launch_12 (
        input logic [   IdWidth-1:0] transf_id_i,
        input logic [ AddrWidth-1:0] src_addr_i,  dst_addr_i,  num_bytes_i,
        input logic [           1:0] src_burst_i, dst_burst_i,
        input logic [           3:0] src_cache_i, dst_cache_i,
        input logic                  decouple_rw_i,
        input logic                  serialize_i,
        input logic                  deburst_i
    );
        burst12_req_valid        <= 1'b0;
        burst12_req              <=  '0;
        @(posedge clk);
        while (burst12_req_ready !== 1) @(posedge clk);
        // write data
        burst12_req.id           <= transf_id_i;
        burst12_req.src          <= src_addr_i;
        burst12_req.dst          <= dst_addr_i;
        burst12_req.num_bytes    <= num_bytes_i;
        burst12_req.cache_src    <= src_cache_i;
        burst12_req.cache_dst    <= dst_cache_i;
        burst12_req.burst_src    <= src_burst_i;
        burst12_req.burst_dst    <= dst_burst_i;
        burst12_req.decouple_rw  <= decouple_rw_i;
        burst12_req.deburst      <= deburst_i;
        burst12_req.serialize    <= serialize_i;
        burst12_req_valid        <= 1'b1;
        // wait and set to 0
        @(posedge clk);
        burst12_req_valid        <= 1'b0;
        burst12_req              <=  '0;
    endtask

    task oned_dut_launch_11 (
        input logic [   IdWidth-1:0] transf_id_i,
        input logic [ AddrWidth-1:0] src_addr_i,  dst_addr_i,  num_bytes_i,
        input logic [           1:0] src_burst_i, dst_burst_i,
        input logic [           3:0] src_cache_i, dst_cache_i,
        input logic                  decouple_rw_i,
        input logic                  serialize_i,
        input logic                  deburst_i
    );
        burst11_req_valid        <= 1'b0;
        burst11_req              <=  '0;
        @(posedge clk);
        while (burst11_req_ready !== 1) @(posedge clk);
        // write data
        burst11_req.id           <= transf_id_i;
        burst11_req.src          <= src_addr_i;
        burst11_req.dst          <= dst_addr_i;
        burst11_req.num_bytes    <= num_bytes_i;
        burst11_req.cache_src    <= src_cache_i;
        burst11_req.cache_dst    <= dst_cache_i;
        burst11_req.burst_src    <= src_burst_i;
        burst11_req.burst_dst    <= dst_burst_i;
        burst11_req.decouple_rw  <= decouple_rw_i;
        burst11_req.deburst      <= deburst_i;
        burst11_req.serialize    <= serialize_i;
        burst11_req_valid        <= 1'b1;
        // wait and set to 0
        @(posedge clk);
        burst11_req_valid        <= 1'b0;
        burst11_req              <=  '0;
    endtask

    task oned_dut_launch_10 (
        input logic [   IdWidth-1:0] transf_id_i,
        input logic [ AddrWidth-1:0] src_addr_i,  dst_addr_i,  num_bytes_i,
        input logic [           1:0] src_burst_i, dst_burst_i,
        input logic [           3:0] src_cache_i, dst_cache_i,
        input logic                  decouple_rw_i,
        input logic                  serialize_i,
        input logic                  deburst_i
    );
        burst10_req_valid        <= 1'b0;
        burst10_req              <=  '0;
        @(posedge clk);
        while (burst10_req_ready !== 1) @(posedge clk);
        // write data
        burst10_req.id           <= transf_id_i;
        burst10_req.src          <= src_addr_i;
        burst10_req.dst          <= dst_addr_i;
        burst10_req.num_bytes    <= num_bytes_i;
        burst10_req.cache_src    <= src_cache_i;
        burst10_req.cache_dst    <= dst_cache_i;
        burst10_req.burst_src    <= src_burst_i;
        burst10_req.burst_dst    <= dst_burst_i;
        burst10_req.decouple_rw  <= decouple_rw_i;
        burst10_req.deburst      <= deburst_i;
        burst10_req.serialize    <= serialize_i;
        burst10_req_valid        <= 1'b1;
        // wait and set to 0
        @(posedge clk);
        burst10_req_valid        <= 1'b0;
        burst10_req              <=  '0;
    endtask

    task oned_dut_launch_9 (
        input logic [   IdWidth-1:0] transf_id_i,
        input logic [ AddrWidth-1:0] src_addr_i,  dst_addr_i,  num_bytes_i,
        input logic [           1:0] src_burst_i, dst_burst_i,
        input logic [           3:0] src_cache_i, dst_cache_i,
        input logic                  decouple_rw_i,
        input logic                  serialize_i,
        input logic                  deburst_i
    );
        burst9_req_valid        <= 1'b0;
        burst9_req              <=  '0;
        @(posedge clk);
        while (burst9_req_ready !== 1) @(posedge clk);
        // write data
        burst9_req.id           <= transf_id_i;
        burst9_req.src          <= src_addr_i;
        burst9_req.dst          <= dst_addr_i;
        burst9_req.num_bytes    <= num_bytes_i;
        burst9_req.cache_src    <= src_cache_i;
        burst9_req.cache_dst    <= dst_cache_i;
        burst9_req.burst_src    <= src_burst_i;
        burst9_req.burst_dst    <= dst_burst_i;
        burst9_req.decouple_rw  <= decouple_rw_i;
        burst9_req.deburst      <= deburst_i;
        burst9_req.serialize    <= serialize_i;
        burst9_req_valid        <= 1'b1;
        // wait and set to 0
        @(posedge clk);
        burst9_req_valid        <= 1'b0;
        burst9_req              <=  '0;
    endtask

    task oned_dut_launch_8 (
        input logic [   IdWidth-1:0] transf_id_i,
        input logic [ AddrWidth-1:0] src_addr_i,  dst_addr_i,  num_bytes_i,
        input logic [           1:0] src_burst_i, dst_burst_i,
        input logic [           3:0] src_cache_i, dst_cache_i,
        input logic                  decouple_rw_i,
        input logic                  serialize_i,
        input logic                  deburst_i
    );
        burst8_req_valid        <= 1'b0;
        burst8_req              <=  '0;
        @(posedge clk);
        while (burst8_req_ready !== 1) @(posedge clk);
        // write data
        burst8_req.id           <= transf_id_i;
        burst8_req.src          <= src_addr_i;
        burst8_req.dst          <= dst_addr_i;
        burst8_req.num_bytes    <= num_bytes_i;
        burst8_req.cache_src    <= src_cache_i;
        burst8_req.cache_dst    <= dst_cache_i;
        burst8_req.burst_src    <= src_burst_i;
        burst8_req.burst_dst    <= dst_burst_i;
        burst8_req.decouple_rw  <= decouple_rw_i;
        burst8_req.deburst      <= deburst_i;
        burst8_req.serialize    <= serialize_i;
        burst8_req_valid        <= 1'b1;
        // wait and set to 0
        @(posedge clk);
        burst8_req_valid        <= 1'b0;
        burst8_req              <=  '0;
    endtask

    task oned_dut_launch_7 (
        input logic [   IdWidth-1:0] transf_id_i,
        input logic [ AddrWidth-1:0] src_addr_i,  dst_addr_i,  num_bytes_i,
        input logic [           1:0] src_burst_i, dst_burst_i,
        input logic [           3:0] src_cache_i, dst_cache_i,
        input logic                  decouple_rw_i,
        input logic                  serialize_i,
        input logic                  deburst_i
    );
        burst7_req_valid        <= 1'b0;
        burst7_req              <=  '0;
        @(posedge clk);
        while (burst7_req_ready !== 1) @(posedge clk);
        // write data
        burst7_req.id           <= transf_id_i;
        burst7_req.src          <= src_addr_i;
        burst7_req.dst          <= dst_addr_i;
        burst7_req.num_bytes    <= num_bytes_i;
        burst7_req.cache_src    <= src_cache_i;
        burst7_req.cache_dst    <= dst_cache_i;
        burst7_req.burst_src    <= src_burst_i;
        burst7_req.burst_dst    <= dst_burst_i;
        burst7_req.decouple_rw  <= decouple_rw_i;
        burst7_req.deburst      <= deburst_i;
        burst7_req.serialize    <= serialize_i;
        burst7_req_valid        <= 1'b1;
        // wait and set to 0
        @(posedge clk);
        burst7_req_valid        <= 1'b0;
        burst7_req              <=  '0;
    endtask

    task oned_dut_launch_6 (
        input logic [   IdWidth-1:0] transf_id_i,
        input logic [ AddrWidth-1:0] src_addr_i,  dst_addr_i,  num_bytes_i,
        input logic [           1:0] src_burst_i, dst_burst_i,
        input logic [           3:0] src_cache_i, dst_cache_i,
        input logic                  decouple_rw_i,
        input logic                  serialize_i,
        input logic                  deburst_i
    );
        burst6_req_valid        <= 1'b0;
        burst6_req              <=  '0;
        @(posedge clk);
        while (burst6_req_ready !== 1) @(posedge clk);
        // write data
        burst6_req.id           <= transf_id_i;
        burst6_req.src          <= src_addr_i;
        burst6_req.dst          <= dst_addr_i;
        burst6_req.num_bytes    <= num_bytes_i;
        burst6_req.cache_src    <= src_cache_i;
        burst6_req.cache_dst    <= dst_cache_i;
        burst6_req.burst_src    <= src_burst_i;
        burst6_req.burst_dst    <= dst_burst_i;
        burst6_req.decouple_rw  <= decouple_rw_i;
        burst6_req.deburst      <= deburst_i;
        burst6_req.serialize    <= serialize_i;
        burst6_req_valid        <= 1'b1;
        // wait and set to 0
        @(posedge clk);
        burst6_req_valid        <= 1'b0;
        burst6_req              <=  '0;
    endtask

    task oned_dut_launch_5 (
        input logic [   IdWidth-1:0] transf_id_i,
        input logic [ AddrWidth-1:0] src_addr_i,  dst_addr_i,  num_bytes_i,
        input logic [           1:0] src_burst_i, dst_burst_i,
        input logic [           3:0] src_cache_i, dst_cache_i,
        input logic                  decouple_rw_i,
        input logic                  serialize_i,
        input logic                  deburst_i
    );
        burst5_req_valid        <= 1'b0;
        burst5_req              <=  '0;
        @(posedge clk);
        while (burst5_req_ready !== 1) @(posedge clk);
        // write data
        burst5_req.id           <= transf_id_i;
        burst5_req.src          <= src_addr_i;
        burst5_req.dst          <= dst_addr_i;
        burst5_req.num_bytes    <= num_bytes_i;
        burst5_req.cache_src    <= src_cache_i;
        burst5_req.cache_dst    <= dst_cache_i;
        burst5_req.burst_src    <= src_burst_i;
        burst5_req.burst_dst    <= dst_burst_i;
        burst5_req.decouple_rw  <= decouple_rw_i;
        burst5_req.deburst      <= deburst_i;
        burst5_req.serialize    <= serialize_i;
        burst5_req_valid        <= 1'b1;
        // wait and set to 0
        @(posedge clk);
        burst5_req_valid        <= 1'b0;
        burst5_req              <=  '0;
    endtask

    task oned_dut_launch_4 (
        input logic [   IdWidth-1:0] transf_id_i,
        input logic [ AddrWidth-1:0] src_addr_i,  dst_addr_i,  num_bytes_i,
        input logic [           1:0] src_burst_i, dst_burst_i,
        input logic [           3:0] src_cache_i, dst_cache_i,
        input logic                  decouple_rw_i,
        input logic                  serialize_i,
        input logic                  deburst_i
    );
        burst4_req_valid        <= 1'b0;
        burst4_req              <=  '0;
        @(posedge clk);
        while (burst4_req_ready !== 1) @(posedge clk);
        // write data
        burst4_req.id           <= transf_id_i;
        burst4_req.src          <= src_addr_i;
        burst4_req.dst          <= dst_addr_i;
        burst4_req.num_bytes    <= num_bytes_i;
        burst4_req.cache_src    <= src_cache_i;
        burst4_req.cache_dst    <= dst_cache_i;
        burst4_req.burst_src    <= src_burst_i;
        burst4_req.burst_dst    <= dst_burst_i;
        burst4_req.decouple_rw  <= decouple_rw_i;
        burst4_req.deburst      <= deburst_i;
        burst4_req.serialize    <= serialize_i;
        burst4_req_valid        <= 1'b1;
        // wait and set to 0
        @(posedge clk);
        burst4_req_valid        <= 1'b0;
        burst4_req              <=  '0;
    endtask

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
        burst4_req_valid        <= 1'b0;
        burst4_req              <=  '0;
        burst5_req_valid        <= 1'b0;
        burst5_req              <=  '0;
        burst6_req_valid        <= 1'b0;
        burst6_req              <=  '0;
        burst7_req_valid        <= 1'b0;
        burst7_req              <=  '0;
        burst8_req_valid        <= 1'b0;
        burst8_req              <=  '0;
        burst9_req_valid        <= 1'b0;
        burst9_req              <=  '0;
        burst10_req_valid        <= 1'b0;
        burst10_req              <=  '0;
        burst11_req_valid        <= 1'b0;
        burst11_req              <=  '0;
        burst12_req_valid        <= 1'b0;
        burst12_req              <=  '0;
        burst13_req_valid        <= 1'b0;
        burst13_req              <=  '0;
        burst14_req_valid        <= 1'b0;
        burst14_req              <=  '0;
        burst15_req_valid        <= 1'b0;
        burst15_req              <=  '0;
    endtask

    task wait_for_dut_completion ();
        repeat(10) @(posedge clk);
        while (backend_idle_0 === 0) @(posedge clk);
        while (backend_idle_1 === 0) @(posedge clk);
        while (backend_idle_2 === 0) @(posedge clk);
        while (backend_idle_3 === 0) @(posedge clk);
        while (backend_idle_4 === 0) @(posedge clk);
        while (backend_idle_5 === 0) @(posedge clk);
        while (backend_idle_6 === 0) @(posedge clk);
        while (backend_idle_7 === 0) @(posedge clk);
        while (backend_idle_8 === 0) @(posedge clk);
        while (backend_idle_9 === 0) @(posedge clk);
        while (backend_idle_10 === 0) @(posedge clk);
        while (backend_idle_11 === 0) @(posedge clk);
        while (backend_idle_12 === 0) @(posedge clk);
        while (backend_idle_13 === 0) @(posedge clk);
        while (backend_idle_14 === 0) @(posedge clk);
        while (backend_idle_15 === 0) @(posedge clk);
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

    task oned_launch_15 (
        input logic [   IdWidth-1:0] transf_id_i,
        input logic [ AddrWidth-1:0] src_addr_i,  dst_addr_i,  num_bytes_i,
        input logic                  decouple_rw_i,
        input logic                  deburst_i,
        input logic                  serialize_i,
        input logic                  wait_for_completion_i
    );
        // keep a log file
        int my_file;
        my_file = $fopen("dma15_transfers.txt", "a+");
        $write("ID: %d  SRC: 0x%x  DST: 0x%x  LEN: %d  DECOUPLE: %1b DEBURST: %1b SERIALIZE: %1b\n", transf_id_i, src_addr_i, dst_addr_i, num_bytes_i, decouple_rw_i, deburst_i, serialize_i );
        $fwrite (my_file, "ID: %d  SRC: 0x%x  DST: 0x%x  LEN: %d  DECOUPLE: %1b DEBURST: %1b SERIALIZE: %1b\n", transf_id_i, src_addr_i, dst_addr_i, num_bytes_i, decouple_rw_i, deburst_i, serialize_i );
        $fclose(my_file);

        // cache and burst is ignored
        oned_dut_launch_15(transf_id_i, src_addr_i, dst_addr_i, num_bytes_i, 2'b01, 2'b01, 4'h0, 4'h0, decouple_rw_i, deburst_i, serialize_i);
        // wait if requested
        if (wait_for_completion_i)
            wait_for_dut_completion();
        // run model
        //oned_osmium_launch(transf_id_i, src_addr_i, dst_addr_i, num_bytes_i, 2'b01, 2'b01, 4'h0, 4'h0, decouple_rw_i, deburst_i, serialize_i);
    endtask

    task oned_launch_14 (
        input logic [   IdWidth-1:0] transf_id_i,
        input logic [ AddrWidth-1:0] src_addr_i,  dst_addr_i,  num_bytes_i,
        input logic                  decouple_rw_i,
        input logic                  deburst_i,
        input logic                  serialize_i,
        input logic                  wait_for_completion_i
    );
        // keep a log file
        int my_file;
        my_file = $fopen("dma14_transfers.txt", "a+");
        $write("ID: %d  SRC: 0x%x  DST: 0x%x  LEN: %d  DECOUPLE: %1b DEBURST: %1b SERIALIZE: %1b\n", transf_id_i, src_addr_i, dst_addr_i, num_bytes_i, decouple_rw_i, deburst_i, serialize_i );
        $fwrite (my_file, "ID: %d  SRC: 0x%x  DST: 0x%x  LEN: %d  DECOUPLE: %1b DEBURST: %1b SERIALIZE: %1b\n", transf_id_i, src_addr_i, dst_addr_i, num_bytes_i, decouple_rw_i, deburst_i, serialize_i );
        $fclose(my_file);

        // cache and burst is ignored
        oned_dut_launch_14(transf_id_i, src_addr_i, dst_addr_i, num_bytes_i, 2'b01, 2'b01, 4'h0, 4'h0, decouple_rw_i, deburst_i, serialize_i);
        // wait if requested
        if (wait_for_completion_i)
            wait_for_dut_completion();
        // run model
        //oned_osmium_launch(transf_id_i, src_addr_i, dst_addr_i, num_bytes_i, 2'b01, 2'b01, 4'h0, 4'h0, decouple_rw_i, deburst_i, serialize_i);
    endtask

    task oned_launch_13 (
        input logic [   IdWidth-1:0] transf_id_i,
        input logic [ AddrWidth-1:0] src_addr_i,  dst_addr_i,  num_bytes_i,
        input logic                  decouple_rw_i,
        input logic                  deburst_i,
        input logic                  serialize_i,
        input logic                  wait_for_completion_i
    );
        // keep a log file
        int my_file;
        my_file = $fopen("dma13_transfers.txt", "a+");
        $write("ID: %d  SRC: 0x%x  DST: 0x%x  LEN: %d  DECOUPLE: %1b DEBURST: %1b SERIALIZE: %1b\n", transf_id_i, src_addr_i, dst_addr_i, num_bytes_i, decouple_rw_i, deburst_i, serialize_i );
        $fwrite (my_file, "ID: %d  SRC: 0x%x  DST: 0x%x  LEN: %d  DECOUPLE: %1b DEBURST: %1b SERIALIZE: %1b\n", transf_id_i, src_addr_i, dst_addr_i, num_bytes_i, decouple_rw_i, deburst_i, serialize_i );
        $fclose(my_file);

        // cache and burst is ignored
        oned_dut_launch_13(transf_id_i, src_addr_i, dst_addr_i, num_bytes_i, 2'b01, 2'b01, 4'h0, 4'h0, decouple_rw_i, deburst_i, serialize_i);
        // wait if requested
        if (wait_for_completion_i)
            wait_for_dut_completion();
        // run model
        //oned_osmium_launch(transf_id_i, src_addr_i, dst_addr_i, num_bytes_i, 2'b01, 2'b01, 4'h0, 4'h0, decouple_rw_i, deburst_i, serialize_i);
    endtask

    task oned_launch_12 (
        input logic [   IdWidth-1:0] transf_id_i,
        input logic [ AddrWidth-1:0] src_addr_i,  dst_addr_i,  num_bytes_i,
        input logic                  decouple_rw_i,
        input logic                  deburst_i,
        input logic                  serialize_i,
        input logic                  wait_for_completion_i
    );
        // keep a log file
        int my_file;
        my_file = $fopen("dma12_transfers.txt", "a+");
        $write("ID: %d  SRC: 0x%x  DST: 0x%x  LEN: %d  DECOUPLE: %1b DEBURST: %1b SERIALIZE: %1b\n", transf_id_i, src_addr_i, dst_addr_i, num_bytes_i, decouple_rw_i, deburst_i, serialize_i );
        $fwrite (my_file, "ID: %d  SRC: 0x%x  DST: 0x%x  LEN: %d  DECOUPLE: %1b DEBURST: %1b SERIALIZE: %1b\n", transf_id_i, src_addr_i, dst_addr_i, num_bytes_i, decouple_rw_i, deburst_i, serialize_i );
        $fclose(my_file);

        // cache and burst is ignored
        oned_dut_launch_12(transf_id_i, src_addr_i, dst_addr_i, num_bytes_i, 2'b01, 2'b01, 4'h0, 4'h0, decouple_rw_i, deburst_i, serialize_i);
        // wait if requested
        if (wait_for_completion_i)
            wait_for_dut_completion();
        // run model
        //oned_osmium_launch(transf_id_i, src_addr_i, dst_addr_i, num_bytes_i, 2'b01, 2'b01, 4'h0, 4'h0, decouple_rw_i, deburst_i, serialize_i);
    endtask

    task oned_launch_11 (
        input logic [   IdWidth-1:0] transf_id_i,
        input logic [ AddrWidth-1:0] src_addr_i,  dst_addr_i,  num_bytes_i,
        input logic                  decouple_rw_i,
        input logic                  deburst_i,
        input logic                  serialize_i,
        input logic                  wait_for_completion_i
    );
        // keep a log file
        int my_file;
        my_file = $fopen("dma11_transfers.txt", "a+");
        $write("ID: %d  SRC: 0x%x  DST: 0x%x  LEN: %d  DECOUPLE: %1b DEBURST: %1b SERIALIZE: %1b\n", transf_id_i, src_addr_i, dst_addr_i, num_bytes_i, decouple_rw_i, deburst_i, serialize_i );
        $fwrite (my_file, "ID: %d  SRC: 0x%x  DST: 0x%x  LEN: %d  DECOUPLE: %1b DEBURST: %1b SERIALIZE: %1b\n", transf_id_i, src_addr_i, dst_addr_i, num_bytes_i, decouple_rw_i, deburst_i, serialize_i );
        $fclose(my_file);

        // cache and burst is ignored
        oned_dut_launch_11(transf_id_i, src_addr_i, dst_addr_i, num_bytes_i, 2'b01, 2'b01, 4'h0, 4'h0, decouple_rw_i, deburst_i, serialize_i);
        // wait if requested
        if (wait_for_completion_i)
            wait_for_dut_completion();
        // run model
        //oned_osmium_launch(transf_id_i, src_addr_i, dst_addr_i, num_bytes_i, 2'b01, 2'b01, 4'h0, 4'h0, decouple_rw_i, deburst_i, serialize_i);
    endtask

    task oned_launch_10 (
        input logic [   IdWidth-1:0] transf_id_i,
        input logic [ AddrWidth-1:0] src_addr_i,  dst_addr_i,  num_bytes_i,
        input logic                  decouple_rw_i,
        input logic                  deburst_i,
        input logic                  serialize_i,
        input logic                  wait_for_completion_i
    );
        // keep a log file
        int my_file;
        my_file = $fopen("dma10_transfers.txt", "a+");
        $write("ID: %d  SRC: 0x%x  DST: 0x%x  LEN: %d  DECOUPLE: %1b DEBURST: %1b SERIALIZE: %1b\n", transf_id_i, src_addr_i, dst_addr_i, num_bytes_i, decouple_rw_i, deburst_i, serialize_i );
        $fwrite (my_file, "ID: %d  SRC: 0x%x  DST: 0x%x  LEN: %d  DECOUPLE: %1b DEBURST: %1b SERIALIZE: %1b\n", transf_id_i, src_addr_i, dst_addr_i, num_bytes_i, decouple_rw_i, deburst_i, serialize_i );
        $fclose(my_file);

        // cache and burst is ignored
        oned_dut_launch_10(transf_id_i, src_addr_i, dst_addr_i, num_bytes_i, 2'b01, 2'b01, 4'h0, 4'h0, decouple_rw_i, deburst_i, serialize_i);
        // wait if requested
        if (wait_for_completion_i)
            wait_for_dut_completion();
        // run model
        //oned_osmium_launch(transf_id_i, src_addr_i, dst_addr_i, num_bytes_i, 2'b01, 2'b01, 4'h0, 4'h0, decouple_rw_i, deburst_i, serialize_i);
    endtask

    task oned_launch_9 (
        input logic [   IdWidth-1:0] transf_id_i,
        input logic [ AddrWidth-1:0] src_addr_i,  dst_addr_i,  num_bytes_i,
        input logic                  decouple_rw_i,
        input logic                  deburst_i,
        input logic                  serialize_i,
        input logic                  wait_for_completion_i
    );
        // keep a log file
        int my_file;
        my_file = $fopen("dma9_transfers.txt", "a+");
        $write("ID: %d  SRC: 0x%x  DST: 0x%x  LEN: %d  DECOUPLE: %1b DEBURST: %1b SERIALIZE: %1b\n", transf_id_i, src_addr_i, dst_addr_i, num_bytes_i, decouple_rw_i, deburst_i, serialize_i );
        $fwrite (my_file, "ID: %d  SRC: 0x%x  DST: 0x%x  LEN: %d  DECOUPLE: %1b DEBURST: %1b SERIALIZE: %1b\n", transf_id_i, src_addr_i, dst_addr_i, num_bytes_i, decouple_rw_i, deburst_i, serialize_i );
        $fclose(my_file);

        // cache and burst is ignored
        oned_dut_launch_9(transf_id_i, src_addr_i, dst_addr_i, num_bytes_i, 2'b01, 2'b01, 4'h0, 4'h0, decouple_rw_i, deburst_i, serialize_i);
        // wait if requested
        if (wait_for_completion_i)
            wait_for_dut_completion();
        // run model
        //oned_osmium_launch(transf_id_i, src_addr_i, dst_addr_i, num_bytes_i, 2'b01, 2'b01, 4'h0, 4'h0, decouple_rw_i, deburst_i, serialize_i);
    endtask

    task oned_launch_8 (
        input logic [   IdWidth-1:0] transf_id_i,
        input logic [ AddrWidth-1:0] src_addr_i,  dst_addr_i,  num_bytes_i,
        input logic                  decouple_rw_i,
        input logic                  deburst_i,
        input logic                  serialize_i,
        input logic                  wait_for_completion_i
    );
        // keep a log file
        int my_file;
        my_file = $fopen("dma8_transfers.txt", "a+");
        $write("ID: %d  SRC: 0x%x  DST: 0x%x  LEN: %d  DECOUPLE: %1b DEBURST: %1b SERIALIZE: %1b\n", transf_id_i, src_addr_i, dst_addr_i, num_bytes_i, decouple_rw_i, deburst_i, serialize_i );
        $fwrite (my_file, "ID: %d  SRC: 0x%x  DST: 0x%x  LEN: %d  DECOUPLE: %1b DEBURST: %1b SERIALIZE: %1b\n", transf_id_i, src_addr_i, dst_addr_i, num_bytes_i, decouple_rw_i, deburst_i, serialize_i );
        $fclose(my_file);

        // cache and burst is ignored
        oned_dut_launch_8(transf_id_i, src_addr_i, dst_addr_i, num_bytes_i, 2'b01, 2'b01, 4'h0, 4'h0, decouple_rw_i, deburst_i, serialize_i);
        // wait if requested
        if (wait_for_completion_i)
            wait_for_dut_completion();
        // run model
        //oned_osmium_launch(transf_id_i, src_addr_i, dst_addr_i, num_bytes_i, 2'b01, 2'b01, 4'h0, 4'h0, decouple_rw_i, deburst_i, serialize_i);
    endtask

    task oned_launch_7 (
        input logic [   IdWidth-1:0] transf_id_i,
        input logic [ AddrWidth-1:0] src_addr_i,  dst_addr_i,  num_bytes_i,
        input logic                  decouple_rw_i,
        input logic                  deburst_i,
        input logic                  serialize_i,
        input logic                  wait_for_completion_i
    );
        // keep a log file
        int my_file;
        my_file = $fopen("dma7_transfers.txt", "a+");
        $write("ID: %d  SRC: 0x%x  DST: 0x%x  LEN: %d  DECOUPLE: %1b DEBURST: %1b SERIALIZE: %1b\n", transf_id_i, src_addr_i, dst_addr_i, num_bytes_i, decouple_rw_i, deburst_i, serialize_i );
        $fwrite (my_file, "ID: %d  SRC: 0x%x  DST: 0x%x  LEN: %d  DECOUPLE: %1b DEBURST: %1b SERIALIZE: %1b\n", transf_id_i, src_addr_i, dst_addr_i, num_bytes_i, decouple_rw_i, deburst_i, serialize_i );
        $fclose(my_file);

        // cache and burst is ignored
        oned_dut_launch_7(transf_id_i, src_addr_i, dst_addr_i, num_bytes_i, 2'b01, 2'b01, 4'h0, 4'h0, decouple_rw_i, deburst_i, serialize_i);
        // wait if requested
        if (wait_for_completion_i)
            wait_for_dut_completion();
        // run model
        //oned_osmium_launch(transf_id_i, src_addr_i, dst_addr_i, num_bytes_i, 2'b01, 2'b01, 4'h0, 4'h0, decouple_rw_i, deburst_i, serialize_i);
    endtask

    task oned_launch_6 (
        input logic [   IdWidth-1:0] transf_id_i,
        input logic [ AddrWidth-1:0] src_addr_i,  dst_addr_i,  num_bytes_i,
        input logic                  decouple_rw_i,
        input logic                  deburst_i,
        input logic                  serialize_i,
        input logic                  wait_for_completion_i
    );
        // keep a log file
        int my_file;
        my_file = $fopen("dma6_transfers.txt", "a+");
        $write("ID: %d  SRC: 0x%x  DST: 0x%x  LEN: %d  DECOUPLE: %1b DEBURST: %1b SERIALIZE: %1b\n", transf_id_i, src_addr_i, dst_addr_i, num_bytes_i, decouple_rw_i, deburst_i, serialize_i );
        $fwrite (my_file, "ID: %d  SRC: 0x%x  DST: 0x%x  LEN: %d  DECOUPLE: %1b DEBURST: %1b SERIALIZE: %1b\n", transf_id_i, src_addr_i, dst_addr_i, num_bytes_i, decouple_rw_i, deburst_i, serialize_i );
        $fclose(my_file);

        // cache and burst is ignored
        oned_dut_launch_6(transf_id_i, src_addr_i, dst_addr_i, num_bytes_i, 2'b01, 2'b01, 4'h0, 4'h0, decouple_rw_i, deburst_i, serialize_i);
        // wait if requested
        if (wait_for_completion_i)
            wait_for_dut_completion();
        // run model
        //oned_osmium_launch(transf_id_i, src_addr_i, dst_addr_i, num_bytes_i, 2'b01, 2'b01, 4'h0, 4'h0, decouple_rw_i, deburst_i, serialize_i);
    endtask

    task oned_launch_5 (
        input logic [   IdWidth-1:0] transf_id_i,
        input logic [ AddrWidth-1:0] src_addr_i,  dst_addr_i,  num_bytes_i,
        input logic                  decouple_rw_i,
        input logic                  deburst_i,
        input logic                  serialize_i,
        input logic                  wait_for_completion_i
    );
        // keep a log file
        int my_file;
        my_file = $fopen("dma5_transfers.txt", "a+");
        $write("ID: %d  SRC: 0x%x  DST: 0x%x  LEN: %d  DECOUPLE: %1b DEBURST: %1b SERIALIZE: %1b\n", transf_id_i, src_addr_i, dst_addr_i, num_bytes_i, decouple_rw_i, deburst_i, serialize_i );
        $fwrite (my_file, "ID: %d  SRC: 0x%x  DST: 0x%x  LEN: %d  DECOUPLE: %1b DEBURST: %1b SERIALIZE: %1b\n", transf_id_i, src_addr_i, dst_addr_i, num_bytes_i, decouple_rw_i, deburst_i, serialize_i );
        $fclose(my_file);

        // cache and burst is ignored
        oned_dut_launch_5(transf_id_i, src_addr_i, dst_addr_i, num_bytes_i, 2'b01, 2'b01, 4'h0, 4'h0, decouple_rw_i, deburst_i, serialize_i);
        // wait if requested
        if (wait_for_completion_i)
            wait_for_dut_completion();
        // run model
        //oned_osmium_launch(transf_id_i, src_addr_i, dst_addr_i, num_bytes_i, 2'b01, 2'b01, 4'h0, 4'h0, decouple_rw_i, deburst_i, serialize_i);
    endtask

    task oned_launch_4 (
        input logic [   IdWidth-1:0] transf_id_i,
        input logic [ AddrWidth-1:0] src_addr_i,  dst_addr_i,  num_bytes_i,
        input logic                  decouple_rw_i,
        input logic                  deburst_i,
        input logic                  serialize_i,
        input logic                  wait_for_completion_i
    );
        // keep a log file
        int my_file;
        my_file = $fopen("dma4_transfers.txt", "a+");
        $write("ID: %d  SRC: 0x%x  DST: 0x%x  LEN: %d  DECOUPLE: %1b DEBURST: %1b SERIALIZE: %1b\n", transf_id_i, src_addr_i, dst_addr_i, num_bytes_i, decouple_rw_i, deburst_i, serialize_i );
        $fwrite (my_file, "ID: %d  SRC: 0x%x  DST: 0x%x  LEN: %d  DECOUPLE: %1b DEBURST: %1b SERIALIZE: %1b\n", transf_id_i, src_addr_i, dst_addr_i, num_bytes_i, decouple_rw_i, deburst_i, serialize_i );
        $fclose(my_file);

        // cache and burst is ignored
        oned_dut_launch_4(transf_id_i, src_addr_i, dst_addr_i, num_bytes_i, 2'b01, 2'b01, 4'h0, 4'h0, decouple_rw_i, deburst_i, serialize_i);
        // wait if requested
        if (wait_for_completion_i)
            wait_for_dut_completion();
        // run model
        //oned_osmium_launch(transf_id_i, src_addr_i, dst_addr_i, num_bytes_i, 2'b01, 2'b01, 4'h0, 4'h0, decouple_rw_i, deburst_i, serialize_i);
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
        input  logic [31:0] max_len,
        // input  logic [31:0] src_add,
        // input  logic [31:0] dst_add,
        input  logic [15:0] master_id,
        // input  logic [15:0] size,
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
        logic [   IdWidth-1:0] transf_id_4;
        logic [ AddrWidth-1:0] src_addr_4,  dst_addr_4,  num_bytes_4;
        logic [   IdWidth-1:0] transf_id_5;
        logic [ AddrWidth-1:0] src_addr_5,  dst_addr_5,  num_bytes_5;
        logic [   IdWidth-1:0] transf_id_6;
        logic [ AddrWidth-1:0] src_addr_6,  dst_addr_6,  num_bytes_6;
        logic [   IdWidth-1:0] transf_id_7;
        logic [ AddrWidth-1:0] src_addr_7,  dst_addr_7,  num_bytes_7;
        logic [   IdWidth-1:0] transf_id_8;
        logic [ AddrWidth-1:0] src_addr_8,  dst_addr_8,  num_bytes_8;
        logic [   IdWidth-1:0] transf_id_9;
        logic [ AddrWidth-1:0] src_addr_9,  dst_addr_9,  num_bytes_9;
        logic [   IdWidth-1:0] transf_id_10;
        logic [ AddrWidth-1:0] src_addr_10,  dst_addr_10,  num_bytes_10;
        logic [   IdWidth-1:0] transf_id_11;
        logic [ AddrWidth-1:0] src_addr_11,  dst_addr_11,  num_bytes_11;
        logic [   IdWidth-1:0] transf_id_12;
        logic [ AddrWidth-1:0] src_addr_12,  dst_addr_12,  num_bytes_12;
        logic [   IdWidth-1:0] transf_id_13;
        logic [ AddrWidth-1:0] src_addr_13,  dst_addr_13,  num_bytes_13;
        logic [   IdWidth-1:0] transf_id_14;
        logic [ AddrWidth-1:0] src_addr_14,  dst_addr_14,  num_bytes_14;
        logic [   IdWidth-1:0] transf_id_15;
        logic [ AddrWidth-1:0] src_addr_15,  dst_addr_15,  num_bytes_15;
        logic                  decouple_rw;
        logic                  deburst;
        logic                  serialize;

        decouple_rw       = 0;//$urandom();
        deburst           = 0;//$urandom();
        serialize         = 0;//$urandom();

        if (master_id == 0) begin
            transf_id_0         = 0;//$urandom();
            // transf_id         = transaction_id;
            src_addr_0[AddrWidth-1:(AddrWidth/2)]   = $urandom();
            src_addr_0[(AddrWidth/2)-1: 0]   = $urandom();
            dst_addr_0[AddrWidth-1:(AddrWidth/2)]   = $urandom();
            dst_addr_0[(AddrWidth/2)-1: 0]   = $urandom();
            if (src_addr_0[31:28] == 0) begin
                src_addr_0[31:28] = ~(src_addr_0[31:28]);
            end
            if (dst_addr_0[31:28] == 0) begin
                dst_addr_0[31:28] = ~(dst_addr_0[31:28]);
            end            
            //src_addr_0   = $urandom();
            //dst_addr_0   = $urandom();
            //num_bytes_0         = 0;
            num_bytes_0  = $urandom_range(max_len, 1);

            oned_launch_0(transf_id_0, src_addr_0, dst_addr_0, num_bytes_0, decouple_rw, deburst, serialize, wait_for_completion);

        end else if (master_id == 1) begin
            transf_id_1         = 1;//$urandom();
            // transf_id         = transaction_id;
            src_addr_1[AddrWidth-1:(AddrWidth/2)]   = $urandom();
            src_addr_1[(AddrWidth/2)-1: 0]   = $urandom();
            dst_addr_1[AddrWidth-1:(AddrWidth/2)]   = $urandom();
            dst_addr_1[(AddrWidth/2)-1: 0]   = $urandom();
            if (src_addr_1[31:28] == 1) begin
                src_addr_1[31:28] = ~(src_addr_1[31:28]);
            end
            if (dst_addr_1[31:28] == 1) begin
                dst_addr_1[31:28] = ~(dst_addr_1[31:28]);
            end 
            //src_addr_1   = $urandom();
            //dst_addr_1   = $urandom();
            //num_bytes_1         = 0;
            num_bytes_1  = $urandom_range(max_len, 1);

            oned_launch_1(transf_id_1, src_addr_1, dst_addr_1, num_bytes_1, decouple_rw, deburst, serialize, wait_for_completion);

        end else if (master_id == 2) begin
            transf_id_2         = 2;//$urandom();
            //transf_id         = transaction_id;
            src_addr_2[AddrWidth-1:(AddrWidth/2)]   = $urandom();
            src_addr_2[(AddrWidth/2)-1: 0]   = $urandom();
            dst_addr_2[AddrWidth-1:(AddrWidth/2)]   = $urandom();
            dst_addr_2[(AddrWidth/2)-1: 0]   = $urandom();
            if (src_addr_2[31:28] == 2) begin
                src_addr_2[31:28] = ~(src_addr_2[31:28]);
            end
            if (dst_addr_2[31:28] == 2) begin
                dst_addr_2[31:28] = ~(dst_addr_2[31:28]);
            end 
            //src_addr_2   = $urandom();
            //dst_addr_2   = $urandom();
            //num_bytes_2         = 0;
            num_bytes_2  = $urandom_range(max_len, 1);

            oned_launch_2(transf_id_2, src_addr_2, dst_addr_2, num_bytes_2, decouple_rw, deburst, serialize, wait_for_completion);

        end else if (master_id == 3) begin
            transf_id_3         = 3;//$urandom();
            // transf_id         = transaction_id;
            src_addr_3[AddrWidth-1:(AddrWidth/2)]   = $urandom();
            src_addr_3[(AddrWidth/2)-1: 0]   = $urandom();
            dst_addr_3[AddrWidth-1:(AddrWidth/2)]   = $urandom();
            dst_addr_3[(AddrWidth/2)-1: 0]   = $urandom();
            if (src_addr_3[31:28] == 3) begin
                src_addr_3[31:28] = ~(src_addr_3[31:28]);
            end
            if (dst_addr_3[31:28] == 3) begin
                dst_addr_3[31:28] = ~(dst_addr_3[31:28]);
            end 
            //src_addr_3   = $urandom();
            //dst_addr_3   = $urandom();
            //num_bytes_3         = 0;
            num_bytes_3  = $urandom_range(max_len, 1);

            oned_launch_3(transf_id_3, src_addr_3, dst_addr_3, num_bytes_3, decouple_rw, deburst, serialize, wait_for_completion);

        end else if (master_id == 4) begin
            transf_id_4         = 4;//$urandom();
            // transf_id         = transaction_id;
            src_addr_4[AddrWidth-1:(AddrWidth/2)]   = $urandom();
            src_addr_4[(AddrWidth/2)-1: 0]   = $urandom();
            dst_addr_4[AddrWidth-1:(AddrWidth/2)]   = $urandom();
            dst_addr_4[(AddrWidth/2)-1: 0]   = $urandom();
            if (src_addr_4[31:28] == 4) begin
                src_addr_4[31:28] = ~(src_addr_4[31:28]);
            end
            if (dst_addr_4[31:28] == 4) begin
                dst_addr_4[31:28] = ~(dst_addr_4[31:28]);
            end 
            //src_addr_4   = $urandom();
            //dst_addr_4   = $urandom();
            //num_bytes_4         = 0;
            num_bytes_4  = $urandom_range(max_len, 1);

            oned_launch_4(transf_id_4, src_addr_4, dst_addr_4, num_bytes_4, decouple_rw, deburst, serialize, wait_for_completion);

        end else if (master_id == 5) begin
            transf_id_5         = 5;//$urandom();
            // transf_id         = transaction_id;
            src_addr_5[AddrWidth-1:(AddrWidth/2)]   = $urandom();
            src_addr_5[(AddrWidth/2)-1: 0]   = $urandom();
            dst_addr_5[AddrWidth-1:(AddrWidth/2)]   = $urandom();
            dst_addr_5[(AddrWidth/2)-1: 0]   = $urandom();
            if (src_addr_5[31:28] == 5) begin
                src_addr_5[31:28] = ~(src_addr_5[31:28]);
            end
            if (dst_addr_5[31:28] == 5) begin
                dst_addr_5[31:28] = ~(dst_addr_5[31:28]);
            end 
            //src_addr_5   = $urandom();
            //dst_addr_5   = $urandom();
            //num_bytes_5         = 0;
            num_bytes_5  = $urandom_range(max_len, 1);

            oned_launch_5(transf_id_5, src_addr_5, dst_addr_5, num_bytes_5, decouple_rw, deburst, serialize, wait_for_completion);

        end else if (master_id == 6) begin
            transf_id_6         = 6;//$urandom();
            // transf_id         = transaction_id;
            src_addr_6[AddrWidth-1:(AddrWidth/2)]   = $urandom();
            src_addr_6[(AddrWidth/2)-1: 0]   = $urandom();
            dst_addr_6[AddrWidth-1:(AddrWidth/2)]   = $urandom();
            dst_addr_6[(AddrWidth/2)-1: 0]   = $urandom();
            if (src_addr_6[31:28] == 6) begin
                src_addr_6[31:28] = ~(src_addr_6[31:28]);
            end
            if (dst_addr_6[31:28] == 6) begin
                dst_addr_6[31:28] = ~(dst_addr_6[31:28]);
            end 
            //src_addr_6  = $urandom();
            //dst_addr_6   = $urandom();
            //num_bytes_6         = 0;
            num_bytes_6  = $urandom_range(max_len, 1);

            oned_launch_6(transf_id_6, src_addr_6, dst_addr_6, num_bytes_6, decouple_rw, deburst, serialize, wait_for_completion);

        end else if (master_id == 7) begin
            transf_id_7         = 7;//$urandom();
            // transf_id         = transaction_id;
            //src_addr_7[AddrWidth-1:AddrWidth-2]   = 1'b1;
            src_addr_7[AddrWidth-1:(AddrWidth/2)]   = $urandom();
            src_addr_7[(AddrWidth/2)-1: 0]   = $urandom();
            dst_addr_7[AddrWidth-1:(AddrWidth/2)]   = $urandom();
            dst_addr_7[(AddrWidth/2)-1: 0]   = $urandom();
            if (src_addr_7[31:28] == 7) begin
                src_addr_7[31:28] = ~(src_addr_7[31:28]);
            end
            if (dst_addr_7[31:28] == 7) begin
                dst_addr_7[31:28] = ~(dst_addr_7[31:28]);
            end 
            //src_addr_7   = $urandom();
            //dst_addr_7   = $urandom();
            //num_bytes_7         = 0;
            num_bytes_7  = $urandom_range(max_len, 1);

            oned_launch_7(transf_id_7, src_addr_7, dst_addr_7, num_bytes_7, decouple_rw, deburst, serialize, wait_for_completion);

        end else if (master_id == 8) begin
            transf_id_8         = 8;//$urandom();
            // transf_id         = transaction_id;
            src_addr_8[AddrWidth-1:(AddrWidth/2)]   = $urandom();
            src_addr_8[(AddrWidth/2)-1: 0]   = $urandom();
            dst_addr_8[AddrWidth-1:(AddrWidth/2)]   = $urandom();
            dst_addr_8[(AddrWidth/2)-1: 0]   = $urandom();
            if (src_addr_8[31:28] == 8) begin
                src_addr_8[31:28] = ~(src_addr_8[31:28]);
            end
            if (dst_addr_8[31:28] == 8) begin
                dst_addr_8[31:28] = ~(dst_addr_8[31:28]);
            end 
            //src_addr_8   = $urandom();
            //dst_addr_8   = $urandom();
            //num_bytes_8         = 0;
            num_bytes_8  = $urandom_range(max_len, 1);

            oned_launch_8(transf_id_8, src_addr_8, dst_addr_8, num_bytes_8, decouple_rw, deburst, serialize, wait_for_completion);

        end else if (master_id == 9) begin
            transf_id_9         = 9;//$urandom();
            // transf_id         = transaction_id;
            src_addr_9[AddrWidth-1:(AddrWidth/2)]   = $urandom();
            src_addr_9[(AddrWidth/2)-1: 0]   = $urandom();
            dst_addr_9[AddrWidth-1:(AddrWidth/2)]   = $urandom();
            dst_addr_9[(AddrWidth/2)-1: 0]   = $urandom();
            if (src_addr_9[31:28] == 9) begin
                src_addr_9[31:28] = ~(src_addr_9[31:28]);
            end
            if (dst_addr_9[31:28] == 9) begin
                dst_addr_9[31:28] = ~(dst_addr_9[31:28]);
            end 
            //src_addr_9   = $urandom();
            //dst_addr_9   = $urandom();
            //num_bytes_9         = 0;
            num_bytes_9  = $urandom_range(max_len, 1);

            oned_launch_9(transf_id_9, src_addr_9, dst_addr_9, num_bytes_9, decouple_rw, deburst, serialize, wait_for_completion);

        end else if (master_id == 10) begin
            transf_id_10         = 10;//$urandom();
            // transf_id         = transaction_id;
            src_addr_10[AddrWidth-1:(AddrWidth/2)]   = $urandom();
            src_addr_10[(AddrWidth/2)-1: 0]   = $urandom();
            dst_addr_10[AddrWidth-1:(AddrWidth/2)]   = $urandom();
            dst_addr_10[(AddrWidth/2)-1: 0]   = $urandom();
            if (src_addr_10[31:28] == 10) begin
                src_addr_10[31:28] = ~(src_addr_10[31:28]);
            end
            if (dst_addr_10[31:28] == 10) begin
                dst_addr_10[31:28] = ~(dst_addr_10[31:28]);
            end 
            // src_addr_10   = $urandom();
            // dst_addr_10   = $urandom();
            //num_bytes_10         = 0;
            num_bytes_10  = $urandom_range(max_len, 1);

            oned_launch_10(transf_id_10, src_addr_10, dst_addr_10, num_bytes_10, decouple_rw, deburst, serialize, wait_for_completion);

        end else if (master_id == 11) begin
            transf_id_11         = 11;//$urandom();
            // transf_id         = transaction_id;
            //src_addr_11[AddrWidth-1:AddrWidth-2]   = 1'b1;
            src_addr_11[AddrWidth-1:(AddrWidth/2)]   = $urandom();
            src_addr_11[(AddrWidth/2)-1: 0]   = $urandom();
            dst_addr_11[AddrWidth-1:(AddrWidth/2)]   = $urandom();
            dst_addr_11[(AddrWidth/2)-1: 0]   = $urandom();
            if (src_addr_11[31:28] == 11) begin
                src_addr_11[31:28] = ~(src_addr_11[31:28]);
            end
            if (dst_addr_11[31:28] == 11) begin
                dst_addr_11[31:28] = ~(dst_addr_11[31:28]);
            end 
            //src_addr_11   = $urandom();
            //dst_addr_11   = $urandom();
            //num_bytes_11         = 0;
            num_bytes_11  = $urandom_range(max_len, 1);

            oned_launch_11(transf_id_11, src_addr_11, dst_addr_11, num_bytes_11, decouple_rw, deburst, serialize, wait_for_completion);

        end else if (master_id == 12) begin
            transf_id_12         = 12;//$urandom();
            // transf_id         = transaction_id;
            src_addr_12[AddrWidth-1:(AddrWidth/2)]   = $urandom();
            src_addr_12[(AddrWidth/2)-1: 0]   = $urandom();
            dst_addr_12[AddrWidth-1:(AddrWidth/2)]   = $urandom();
            dst_addr_12[(AddrWidth/2)-1: 0]   = $urandom();
            if (src_addr_12[31:28] == 12) begin
                src_addr_12[31:28] = ~(src_addr_12[31:28]);
            end
            if (dst_addr_12[31:28] == 12) begin
                dst_addr_12[31:28] = ~(dst_addr_12[31:28]);
            end 
            //src_addr_12   = $urandom();
            //dst_addr_12   = $urandom();
            //num_bytes_12         = 0;
            num_bytes_12  = $urandom_range(max_len, 1);

            oned_launch_12(transf_id_12, src_addr_12, dst_addr_12, num_bytes_12, decouple_rw, deburst, serialize, wait_for_completion);

        end else if (master_id == 13) begin
            transf_id_13         = 13;//$urandom();
            // transf_id         = transaction_id;
            src_addr_13[AddrWidth-1:(AddrWidth/2)]   = $urandom();
            src_addr_13[(AddrWidth/2)-1: 0]   = $urandom();
            dst_addr_13[AddrWidth-1:(AddrWidth/2)]   = $urandom();
            dst_addr_13[(AddrWidth/2)-1: 0]   = $urandom();
            if (src_addr_13[31:28] == 13) begin
                src_addr_13[31:28] = ~(src_addr_13[31:28]);
            end
            if (dst_addr_13[31:28] == 13) begin
                dst_addr_13[31:28] = ~(dst_addr_13[31:28]);
            end 
            //src_addr_13   = $urandom();
            //dst_addr_13   = $urandom();
            //num_bytes_13         = 0;
            num_bytes_13  = $urandom_range(max_len, 1);

            oned_launch_13(transf_id_13, src_addr_13, dst_addr_13, num_bytes_13, decouple_rw, deburst, serialize, wait_for_completion);

        end else if (master_id == 14) begin
            transf_id_14         = 14;//$urandom();
            // transf_id         = transaction_id;
            src_addr_14[AddrWidth-1:(AddrWidth/2)]   = $urandom();
            src_addr_14[(AddrWidth/2)-1: 0]   = $urandom();
            dst_addr_14[AddrWidth-1:(AddrWidth/2)]   = $urandom();
            dst_addr_14[(AddrWidth/2)-1: 0]   = $urandom();
            if (src_addr_14[31:28] == 14) begin
                src_addr_14[31:28] = ~(src_addr_14[31:28]);
            end
            if (dst_addr_14[31:28] == 14) begin
                dst_addr_14[31:28] = ~(dst_addr_14[31:28]);
            end 
            //src_addr_14   = $urandom();
            //dst_addr_14   = $urandom();
            //num_bytes_14         = 0;
            num_bytes_14  = $urandom_range(max_len, 1);

            oned_launch_14(transf_id_14, src_addr_14, dst_addr_14, num_bytes_14, decouple_rw, deburst, serialize, wait_for_completion);

        end else if (master_id == 15) begin
            transf_id_15         = 15;//$urandom();
            // transf_id         = transaction_id;
            //src_addr_15[AddrWidth-1:AddrWidth-2]   = 1'b1;
            src_addr_15[AddrWidth-1:(AddrWidth/2)]   = $urandom();
            src_addr_15[(AddrWidth/2)-1: 0]   = $urandom();
            dst_addr_15[AddrWidth-1:(AddrWidth/2)]   = $urandom();
            dst_addr_15[(AddrWidth/2)-1: 0]   = $urandom();
            if (src_addr_15[31:28] == 15) begin
                src_addr_15[31:28] = ~(src_addr_15[31:28]);
            end
            if (dst_addr_15[31:28] == 15) begin
                dst_addr_15[31:28] = ~(dst_addr_15[31:28]);
            end 
            //src_addr_15   = $urandom();
            //dst_addr_15   = $urandom();
            //num_bytes_15         = 0;
            num_bytes_15  = $urandom_range(max_len, 1);

            oned_launch_15(transf_id_15, src_addr_15, dst_addr_15, num_bytes_15, decouple_rw, deburst, serialize, wait_for_completion);

        end

        // transaction_id    = transaction_id + 1;
        

    endtask

endmodule : fixture_axi_dma_backend
