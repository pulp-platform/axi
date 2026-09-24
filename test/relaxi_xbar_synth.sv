// Copyright 2026 ETH Zurich and University of Bologna.
// Proprietary, not for release.
//
// Synthesis bench for relaxi_xbar matching fault injection campaign parameters.
// TB-aligned: 10x10, AxiIdWidth=5, AxiIdUsed=3, Data=64, Addr=32, User=5
// LatencyMode=CUT_ALL_AX, PipelineStages=1, ATOPs=0
// Copyright 2026 ETH Zurich and University of Bolivia.
// Proprietary, not for release.
//
// Synthesis bench for relaxi_xbar matching fault injection campaign parameters.
// TB-aligned: 10x10, AxiIdWidth=5, AxiIdUsed=3, Data=64, Addr=32, User=5
// LatencyMode=CUT_ALL_AX, PipelineStages=1, ATOPs=0
//
// All AXI ports exposed as flat logic so DC preserves the full datapath
// and does not insert SYNOPSYS_UNCONNECTED on internal signals.

// Copyright 2026 ETH Zurich and University of Bologna.
// Proprietary, not for release.
//
// Synthesis bench for relaxi_xbar matching fault injection campaign parameters.
// TB-aligned: 10x10, AxiIdWidth=5, AxiIdUsed=3, Data=64, Addr=32, User=5
// LatencyMode=CUT_ALL_AX, PipelineStages=1, ATOPs=0
// Copyright 2026 ETH Zurich and University of Bolivia.
// Proprietary, not for release.
//
// Synthesis bench for relaxi_xbar matching fault injection campaign parameters.
// TB-aligned: 10x10, AxiIdWidth=5, AxiIdUsed=3, Data=64, Addr=32, User=5
// LatencyMode=CUT_ALL_AX, PipelineStages=1, ATOPs=0
//
// All AXI ports exposed as flat logic so DC preserves the full datapath
// and does not insert SYNOPSYS_UNCONNECTED on internal signals.
`include "axi/typedef.svh"

module relaxi_xbar_synth
  import axi_pkg::*;
#(
  parameter int unsigned NoSlvPorts         = 32'd10,
  parameter int unsigned NoMstPorts         = 32'd10,
  parameter int unsigned AxiIdWidthSlvPorts = 32'd5,
  parameter int unsigned AxiIdUsedSlvPorts  = 32'd3,
  parameter int unsigned AxiAddrWidth       = 32'd32,
  parameter int unsigned AxiDataWidth       = 32'd64,
  parameter int unsigned AxiUserWidth       = 32'd5,
  parameter int unsigned NoAddrRules        = NoMstPorts,
  parameter int unsigned AxiIdWidthMstPorts = AxiIdWidthSlvPorts + $clog2(NoSlvPorts)
) (
  input  logic clk_i,
  input  logic rst_ni,

  input  logic [3029:0] slv_req_i,
  output logic [1419:0] slv_resp_o,
  output logic [3029:0] mst_req_o,
  input  logic [1419:0] mst_resp_i,
  input  logic  [959:0] addr_map_i,
  input  logic    [9:0] en_default_mst_port_i,
  input  logic   [39:0] default_mst_port_i,
  output logic    [1:0] fault_o
);

  localparam axi_pkg::xbar_cfg_t XbarCfg = '{
    NoSlvPorts:         NoSlvPorts,
    NoMstPorts:         NoMstPorts,
    MaxMstTrans:        32'd10,
    MaxSlvTrans:        32'd6,
    FallThrough:        1'b0,
    LatencyMode:        axi_pkg::CUT_ALL_AX,
    PipelineStages:     32'd1,
    AxiIdWidthSlvPorts: AxiIdWidthSlvPorts,
    AxiIdUsedSlvPorts:  AxiIdUsedSlvPorts,
    UniqueIds:          1'b0,
    AxiAddrWidth:       AxiAddrWidth,
    AxiDataWidth:       AxiDataWidth,
    NoAddrRules:        NoAddrRules,
    default:            '0
  };

  typedef logic [AxiIdWidthMstPorts-1:0] slv_id_t;
  typedef logic [AxiIdWidthMstPorts-1:0] mst_id_t;
  typedef logic [AxiAddrWidth-1:0]       addr_t;
  typedef logic [AxiDataWidth-1:0]       data_t;
  typedef logic [AxiDataWidth/8-1:0]     strb_t;
  typedef logic [AxiUserWidth-1:0]       user_t;

  `RELAXI_TYPEDEF_AW_CHAN_T(slv_aw_chan_t, addr_t, slv_id_t, user_t)
  `RELAXI_TYPEDEF_AW_CHAN_T(mst_aw_chan_t, addr_t, mst_id_t, user_t)
  `RELAXI_TYPEDEF_W_CHAN_T (w_chan_t,      data_t, strb_t,   user_t)
  `RELAXI_TYPEDEF_B_CHAN_T (slv_b_chan_t,  slv_id_t,         user_t)
  `RELAXI_TYPEDEF_B_CHAN_T (mst_b_chan_t,  mst_id_t,         user_t)
  `RELAXI_TYPEDEF_AR_CHAN_T(slv_ar_chan_t, addr_t, slv_id_t, user_t)
  `RELAXI_TYPEDEF_AR_CHAN_T(mst_ar_chan_t, addr_t, mst_id_t, user_t)
  `RELAXI_TYPEDEF_R_CHAN_T (slv_r_chan_t,  data_t, slv_id_t, user_t)
  `RELAXI_TYPEDEF_R_CHAN_T (mst_r_chan_t,  data_t, mst_id_t, user_t)
  `RELAXI_TYPEDEF_REQ_T   (slv_req_t,     slv_aw_chan_t, w_chan_t, slv_ar_chan_t)
  `RELAXI_TYPEDEF_RESP_T  (slv_resp_t,    slv_b_chan_t,  slv_r_chan_t)
  `RELAXI_TYPEDEF_REQ_T   (mst_req_t,     mst_aw_chan_t, w_chan_t, mst_ar_chan_t)
  `RELAXI_TYPEDEF_RESP_T  (mst_resp_t,    mst_b_chan_t,  mst_r_chan_t)

  // Cast flat ports to typed structs
  slv_req_t  [NoSlvPorts-1:0]               slv_req;
  slv_resp_t [NoSlvPorts-1:0]               slv_resp;
  mst_req_t  [NoMstPorts-1:0]               mst_req;
  mst_resp_t [NoMstPorts-1:0]               mst_resp;
  axi_pkg::xbar_rule_32_t [NoAddrRules-1:0] addr_map;

  assign slv_req    = slv_req_i;
  assign slv_resp_o = slv_resp;
  assign mst_req_o  = mst_req;
  assign mst_resp   = mst_resp_i;
  assign addr_map   = addr_map_i;

  relaxi_xbar #(
    .Cfg           ( XbarCfg                  ),
    .ATOPs         ( 1'b0                     ),
    .Connectivity  ( '1                       ),
    .slv_aw_chan_t ( slv_aw_chan_t            ),
    .mst_aw_chan_t ( mst_aw_chan_t            ),
    .w_chan_t      ( w_chan_t                 ),
    .slv_b_chan_t  ( slv_b_chan_t             ),
    .mst_b_chan_t  ( mst_b_chan_t             ),
    .slv_ar_chan_t ( slv_ar_chan_t            ),
    .mst_ar_chan_t ( mst_ar_chan_t            ),
    .slv_r_chan_t  ( slv_r_chan_t             ),
    .mst_r_chan_t  ( mst_r_chan_t             ),
    .slv_req_t     ( slv_req_t               ),
    .slv_resp_t    ( slv_resp_t              ),
    .mst_req_t     ( mst_req_t               ),
    .mst_resp_t    ( mst_resp_t              ),
    .rule_t        ( axi_pkg::xbar_rule_32_t )
  ) i_dut (
    .clk_i,
    .rst_ni,
    .test_i                ( 1'b0                  ),
    .slv_ports_req_i       ( slv_req               ),
    .slv_ports_resp_o      ( slv_resp              ),
    .mst_ports_req_o       ( mst_req               ),
    .mst_ports_resp_i      ( mst_resp              ),
    .addr_map_i            ( addr_map              ),
    .en_default_mst_port_i ( en_default_mst_port_i ),
    .default_mst_port_i    ( default_mst_port_i    ),
    .fault_o               ( fault_o               )
  );

// pragma translate_off
  initial begin
    $display("[WRAP] slv_req=%0d slv_resp=%0d mst_req=%0d mst_resp=%0d addr_map=%0d",
             $bits(slv_req), $bits(slv_resp), $bits(mst_req), $bits(mst_resp), $bits(addr_map));
    if ($bits(slv_req)  != $bits(slv_req_i))  $fatal(1, "slv_req %0d vs %0d",  $bits(slv_req),  $bits(slv_req_i));
    if ($bits(slv_resp) != $bits(slv_resp_o)) $fatal(1, "slv_resp %0d vs %0d", $bits(slv_resp), $bits(slv_resp_o));
    if ($bits(mst_req)  != $bits(mst_req_o))  $fatal(1, "mst_req %0d vs %0d",  $bits(mst_req),  $bits(mst_req_o));
    if ($bits(mst_resp) != $bits(mst_resp_i)) $fatal(1, "mst_resp %0d vs %0d", $bits(mst_resp), $bits(mst_resp_i));
  end
// pragma translate_on

endmodule
