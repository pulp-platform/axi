`timescale 1ns/1ns

`include "axi/assign.svh"
`include "axi/typedef.svh"

module axi_dma_backend_wrapper #(
  parameter bit ATOPs = 1'b0,
  parameter int unsigned NoSlvPorts = 32'd1,
  parameter int unsigned NoMstPorts = 32'd1,
  parameter bit [NoSlvPorts-1:0][NoMstPorts-1:0] Connectivity = '1,
  parameter int unsigned AxiAddrWidth = 32'd64,
  parameter int unsigned AxiDataWidth = 32'd512,
  parameter int unsigned AxiIdWidth = 32'd6,
  parameter int unsigned AxiUserWidth = 32'd1,
  parameter int unsigned AxiSlvPortMaxUniqIds = 32'd16,
  parameter int unsigned AxiSlvPortMaxTxnsPerId = 32'd128,
  parameter int unsigned AxiSlvPortMaxTxns = 32'd31,
  parameter int unsigned AxiMstPortMaxUniqIds = 32'd4,
  parameter int unsigned AxiMstPortMaxTxnsPerId = 32'd7,
  parameter int unsigned NoAddrRules = 32'd1
) (
  input  logic                          clk_i,
  input  logic                          rst_ni,
  input  logic                          test_en_i,
  AXI_BUS.Slave                         slv_ports [NoSlvPorts-1:0],
  AXI_BUS.Master                        mst_ports [NoMstPorts-1:0]
);

  typedef axi_pkg::xbar_rule_64_t       rule_t; // Has to be the same width as axi addr

  typedef logic [AxiIdWidth         -1:0] id_mst_t;
  typedef logic [AxiIdWidth         -1:0] id_slv_t;
  typedef logic [AxiAddrWidth       -1:0] addr_t;
  typedef logic [AxiDataWidth       -1:0] data_t;
  typedef logic [AxiDataWidth/8     -1:0] strb_t;
  typedef logic [AxiUserWidth       -1:0] user_t;

  localparam axi_pkg::xbar_cfg_t Cfg = '{
    NoSlvPorts:         NoMstPorts,
    NoMstPorts:         NoSlvPorts,
    MaxMstTrans:        AxiSlvPortMaxTxns,
    MaxSlvTrans:        AxiSlvPortMaxTxnsPerId,
    FallThrough:        1'b0,
    LatencyMode:        axi_pkg::CUT_ALL_AX,
    AxiIdWidthSlvPorts: AxiIdWidth,
    AxiIdUsedSlvPorts:  (AxiIdWidth-1),
    UniqueIds:          1'b0,
    AxiAddrWidth:       AxiAddrWidth,
    AxiDataWidth:       AxiDataWidth,
    NoAddrRules:        NoAddrRules
  };

  localparam rule_t [Cfg.NoAddrRules-1:0] AddrMap = '{
    '{idx: 32'd0 % NoSlvPorts, start_addr: {AxiAddrWidth{1'b0}}, end_addr: {(AxiAddrWidth){1'b1}}}
  };


  `AXI_TYPEDEF_AW_CHAN_T(mst_aw_chan_t, addr_t, id_mst_t, user_t)
  `AXI_TYPEDEF_AW_CHAN_T(slv_aw_chan_t, addr_t, id_slv_t, user_t)
  `AXI_TYPEDEF_W_CHAN_T(w_chan_t, data_t, strb_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T(mst_b_chan_t, id_mst_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T(slv_b_chan_t, id_slv_t, user_t)
  `AXI_TYPEDEF_AR_CHAN_T(mst_ar_chan_t, addr_t, id_mst_t, user_t)
  `AXI_TYPEDEF_AR_CHAN_T(slv_ar_chan_t, addr_t, id_slv_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(mst_r_chan_t, data_t, id_mst_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(slv_r_chan_t, data_t, id_slv_t, user_t)
  `AXI_TYPEDEF_REQ_T(mst_req_t, mst_aw_chan_t, w_chan_t, mst_ar_chan_t)
  `AXI_TYPEDEF_REQ_T(slv_req_t, slv_aw_chan_t, w_chan_t, slv_ar_chan_t)
  `AXI_TYPEDEF_RESP_T(mst_resp_t, mst_b_chan_t, mst_r_chan_t)
  `AXI_TYPEDEF_RESP_T(slv_resp_t, slv_b_chan_t, slv_r_chan_t)

  mst_req_t   [NoMstPorts-1:0]  mst_reqs;
  mst_resp_t  [NoMstPorts-1:0]  mst_resps;
  slv_req_t   [NoSlvPorts-1:0]  slv_reqs;
  slv_resp_t  [NoSlvPorts-1:0]  slv_resps;

  for (genvar i = 0; i < NoMstPorts; i++) begin : gen_assign_mst
    `AXI_ASSIGN_FROM_REQ(mst_ports[i], mst_reqs[i])
    `AXI_ASSIGN_TO_RESP(mst_resps[i], mst_ports[i])
  end

  for (genvar i = 0; i < NoSlvPorts; i++) begin : gen_assign_slv
    `AXI_ASSIGN_TO_REQ(slv_reqs[i], slv_ports[i])
    `AXI_ASSIGN_FROM_RESP(slv_ports[i], slv_resps[i])
  end

  axi_xp #(
    .ATOPs                   ( ATOPs         ),
    .Cfg                     ( Cfg           ),
    .NoSlvPorts              ( Cfg.NoSlvPorts),
    .NoMstPorts              ( Cfg.NoMstPorts),
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
    .NoAddrRules             ( NoAddrRules            ),
    .slv_aw_chan_t  ( slv_aw_chan_t ),
    .mst_aw_chan_t  ( mst_aw_chan_t ),
    .w_chan_t       ( w_chan_t      ),
    .slv_b_chan_t   ( slv_b_chan_t  ),
    .mst_b_chan_t   ( mst_b_chan_t  ),
    .slv_ar_chan_t  ( slv_ar_chan_t ),
    .mst_ar_chan_t  ( mst_ar_chan_t ),
    .slv_r_chan_t   ( slv_r_chan_t  ),
    .mst_r_chan_t   ( mst_r_chan_t  ),
    .slv_req_t      ( slv_req_t     ),
    .slv_resp_t     ( slv_resp_t    ),
    .mst_req_t      ( mst_req_t     ),
    .mst_resp_t     ( mst_resp_t    ),
    .rule_t         ( rule_t        )
  ) i_xp (
    .clk_i,
    .rst_ni,
    .test_en_i,
    .slv_req_i  (slv_reqs ),
    .slv_resp_o (slv_resps),
    .mst_req_o  (mst_reqs ),
    .mst_resp_i (mst_resps),
    .addr_map_i (AddrMap  )
  );

endmodule