// Copyright 2026 ETH Zurich and University of Bologna.
// Proprietary, not for release.
//
// Synthesis bench for axi_xbar matching fault injection campaign parameters:
//   NoSlvPorts = 6, NoMstPorts = 8, AxiIdWidthSlvPorts = 5
//   AxiAddrWidth = 32, AxiDataWidth = 64
//   LatencyMode = CUT_ALL_PORTS, PipelineStages = 1
`include "axi/typedef.svh"

module axi_xbar_synth 
  import axi_pkg::*;
#(
  parameter int unsigned NoSlvPorts         = 32'd10,
  parameter int unsigned NoMstPorts         = 32'd10,
  parameter int unsigned AxiIdWidthSlvPorts = 32'd5,
  parameter int unsigned AxiAddrWidth       = 32'd32,
  parameter int unsigned AxiDataWidth       = 32'd64,
  parameter int unsigned AxiUserWidth       = 32'd1,
  // derived
  parameter int unsigned AxiIdWidthMstPorts = AxiIdWidthSlvPorts + $clog2(NoSlvPorts),
  parameter int unsigned NoAddrRules        = NoMstPorts,
  // req/rsp widths using axi_pkg functions
  parameter int unsigned SlvReqWidth = req_width(AxiAddrWidth, AxiDataWidth,
                                         AxiIdWidthSlvPorts, AxiUserWidth,
                                         AxiUserWidth, AxiUserWidth),
  parameter int unsigned SlvRspWidth = rsp_width(AxiDataWidth,
                                         AxiIdWidthSlvPorts,
                                         AxiUserWidth, AxiUserWidth),
  parameter int unsigned MstReqWidth = req_width(AxiAddrWidth, AxiDataWidth,
                                         AxiIdWidthMstPorts, AxiUserWidth,
                                         AxiUserWidth, AxiUserWidth),
  parameter int unsigned MstRspWidth = rsp_width(AxiDataWidth,
                                         AxiIdWidthMstPorts,
                                         AxiUserWidth, AxiUserWidth)
) (
  input  logic clk_i,
  input  logic rst_ni,

  input  logic [NoSlvPorts-1:0][SlvReqWidth-1:0] slv_req_i,
  output logic [NoSlvPorts-1:0][SlvRspWidth-1:0] slv_resp_o,
  output logic [NoMstPorts-1:0][MstReqWidth-1:0] mst_req_o,
  input  logic [NoMstPorts-1:0][MstRspWidth-1:0] mst_resp_i,

  input  axi_pkg::xbar_rule_32_t [NoAddrRules-1:0] addr_map_i
);

  localparam axi_pkg::xbar_cfg_t XbarCfg = '{
    NoSlvPorts:         NoSlvPorts,
    NoMstPorts:         NoMstPorts,
    MaxMstTrans:        32'd10,
    MaxSlvTrans:        32'd6,
    FallThrough:        1'b0,
    LatencyMode:        axi_pkg::CUT_ALL_PORTS,
    PipelineStages:     32'd1,
    AxiIdWidthSlvPorts: AxiIdWidthSlvPorts,
    AxiIdUsedSlvPorts:  AxiIdWidthSlvPorts,
    UniqueIds:          1'b0,
    AxiAddrWidth:       AxiAddrWidth,
    AxiDataWidth:       AxiDataWidth,
    NoAddrRules:        NoAddrRules,
    default:            '0
  };

  // Internal typed signals
  typedef logic [AxiIdWidthSlvPorts-1:0] slv_id_t;
  typedef logic [AxiIdWidthMstPorts-1:0] mst_id_t;
  typedef logic [AxiAddrWidth-1:0]       addr_t;
  typedef logic [AxiDataWidth-1:0]       data_t;
  typedef logic [AxiDataWidth/8-1:0]     strb_t;
  typedef logic [AxiUserWidth-1:0]       user_t;

  `AXI_TYPEDEF_AW_CHAN_T(slv_aw_chan_t, addr_t, slv_id_t, user_t)
  `AXI_TYPEDEF_W_CHAN_T (w_chan_t,      data_t, strb_t,   user_t)
  `AXI_TYPEDEF_B_CHAN_T (slv_b_chan_t,  slv_id_t,         user_t)
  `AXI_TYPEDEF_AR_CHAN_T(slv_ar_chan_t, addr_t, slv_id_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T (slv_r_chan_t,  data_t, slv_id_t, user_t)
  `AXI_TYPEDEF_REQ_T    (slv_req_t,    slv_aw_chan_t, w_chan_t, slv_ar_chan_t)
  `AXI_TYPEDEF_RESP_T   (slv_resp_t,   slv_b_chan_t,  slv_r_chan_t)

  `AXI_TYPEDEF_AW_CHAN_T(mst_aw_chan_t, addr_t, mst_id_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T (mst_b_chan_t,  mst_id_t,         user_t)
  `AXI_TYPEDEF_AR_CHAN_T(mst_ar_chan_t, addr_t, mst_id_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T (mst_r_chan_t,  data_t, mst_id_t, user_t)
  `AXI_TYPEDEF_REQ_T    (mst_req_t,    mst_aw_chan_t, w_chan_t, mst_ar_chan_t)
  `AXI_TYPEDEF_RESP_T   (mst_resp_t,   mst_b_chan_t,  mst_r_chan_t)

  // Cast flat ports to typed structs
  slv_req_t  [NoSlvPorts-1:0] slv_req;
  slv_resp_t [NoSlvPorts-1:0] slv_resp;
  mst_req_t  [NoMstPorts-1:0] mst_req;
  mst_resp_t [NoMstPorts-1:0] mst_resp;

  assign slv_req  = slv_req_i;
  assign slv_resp_o = slv_resp;
  assign mst_req_o  = mst_req;
  assign mst_resp = mst_resp_i;

  axi_xbar #(
    .Cfg           ( XbarCfg        ),
    .ATOPs         ( 1'b1           ),
    .Connectivity  ( '1             ),
    .slv_aw_chan_t ( slv_aw_chan_t  ),
    .mst_aw_chan_t ( mst_aw_chan_t  ),
    .w_chan_t      ( w_chan_t       ),
    .slv_b_chan_t  ( slv_b_chan_t   ),
    .mst_b_chan_t  ( mst_b_chan_t   ),
    .slv_ar_chan_t ( slv_ar_chan_t  ),
    .mst_ar_chan_t ( mst_ar_chan_t  ),
    .slv_r_chan_t  ( slv_r_chan_t   ),
    .mst_r_chan_t  ( mst_r_chan_t   ),
    .slv_req_t     ( slv_req_t      ),
    .slv_resp_t    ( slv_resp_t     ),
    .mst_req_t     ( mst_req_t      ),
    .mst_resp_t    ( mst_resp_t     ),
    .rule_t        ( axi_pkg::xbar_rule_32_t )
  ) i_dut (
    .clk_i,
    .rst_ni,
    .test_i                ( 1'b0                ),
    .slv_ports_req_i       ( slv_req             ),
    .slv_ports_resp_o      ( slv_resp            ),
    .mst_ports_req_o       ( mst_req             ),
    .mst_ports_resp_i      ( mst_resp            ),
    .addr_map_i            ( addr_map_i          ),
    .en_default_mst_port_i ( '0                  ),
    .default_mst_port_i    ( '0                  )
  );

endmodule