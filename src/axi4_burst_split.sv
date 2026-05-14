// Copyright (c) 2026 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

`include "axi/typedef.svh"

/// AXI4 burst splitter with AXI4-Lite configurable granularity limit.
///
/// This module combines [`axi_burst_splitter_gran`](module.axi_burst_splitter_gran) with an
/// [`axi_lite_regs`](module.axi_lite_regs) instance. Software can program the splitter length
/// limit (`len_limit_i`) via AXI4-Lite register offset 0.
module axi4_burst_split #(
  parameter int unsigned MaxReadTxns      = 32'd2,
  parameter int unsigned MaxWriteTxns     = 32'd2,
  parameter bit          FullBW           = 1'b0,
  parameter bit          CutPath          = 1'b0,
  parameter bit          DisableChecks    = 1'b0,
  parameter int unsigned AddrWidth        = 32'd32,
  parameter int unsigned DataWidth        = 32'd64,
  parameter int unsigned IdWidth          = 32'd4,
  parameter int unsigned UserWidth        = 32'd1,
  parameter int unsigned CfgAddrWidth     = 32'd12,
  parameter int unsigned CfgDataWidth     = 32'd32,
  parameter logic [7:0]  LenLimitResetVal = 8'd15
) (
  input  logic clk_i,
  input  logic rst_ni,

  input  logic                 test_i,

  input  logic [CfgAddrWidth-1:0] cfg_aw_addr_i,
  input  logic [2:0]              cfg_aw_prot_i,
  input  logic                    cfg_aw_valid_i,
  output logic                    cfg_aw_ready_o,
  input  logic [CfgDataWidth-1:0] cfg_w_data_i,
  input  logic [CfgDataWidth/8-1:0] cfg_w_strb_i,
  input  logic                    cfg_w_valid_i,
  output logic                    cfg_w_ready_o,
  output logic [1:0]              cfg_b_resp_o,
  output logic                    cfg_b_valid_o,
  input  logic                    cfg_b_ready_i,
  input  logic [CfgAddrWidth-1:0] cfg_ar_addr_i,
  input  logic [2:0]              cfg_ar_prot_i,
  input  logic                    cfg_ar_valid_i,
  output logic                    cfg_ar_ready_o,
  output logic [CfgDataWidth-1:0] cfg_r_data_o,
  output logic [1:0]              cfg_r_resp_o,
  output logic                    cfg_r_valid_o,
  input  logic                    cfg_r_ready_i,

  input  logic [IdWidth-1:0]      slv_aw_id_i,
  input  logic [AddrWidth-1:0]    slv_aw_addr_i,
  input  logic [7:0]              slv_aw_len_i,
  input  logic [2:0]              slv_aw_size_i,
  input  logic [1:0]              slv_aw_burst_i,
  input  logic                    slv_aw_lock_i,
  input  logic [3:0]              slv_aw_cache_i,
  input  logic [2:0]              slv_aw_prot_i,
  input  logic [3:0]              slv_aw_qos_i,
  input  logic [3:0]              slv_aw_region_i,
  input  logic [UserWidth-1:0]    slv_aw_user_i,
  input  logic                    slv_aw_valid_i,
  output logic                    slv_aw_ready_o,
  input  logic [DataWidth-1:0]    slv_w_data_i,
  input  logic [DataWidth/8-1:0]  slv_w_strb_i,
  input  logic                    slv_w_last_i,
  input  logic [UserWidth-1:0]    slv_w_user_i,
  input  logic                    slv_w_valid_i,
  output logic                    slv_w_ready_o,
  output logic [IdWidth-1:0]      slv_b_id_o,
  output logic [1:0]              slv_b_resp_o,
  output logic [UserWidth-1:0]    slv_b_user_o,
  output logic                    slv_b_valid_o,
  input  logic                    slv_b_ready_i,
  input  logic [IdWidth-1:0]      slv_ar_id_i,
  input  logic [AddrWidth-1:0]    slv_ar_addr_i,
  input  logic [7:0]              slv_ar_len_i,
  input  logic [2:0]              slv_ar_size_i,
  input  logic [1:0]              slv_ar_burst_i,
  input  logic                    slv_ar_lock_i,
  input  logic [3:0]              slv_ar_cache_i,
  input  logic [2:0]              slv_ar_prot_i,
  input  logic [3:0]              slv_ar_qos_i,
  input  logic [3:0]              slv_ar_region_i,
  input  logic [UserWidth-1:0]    slv_ar_user_i,
  input  logic                    slv_ar_valid_i,
  output logic                    slv_ar_ready_o,
  output logic [IdWidth-1:0]      slv_r_id_o,
  output logic [DataWidth-1:0]    slv_r_data_o,
  output logic [1:0]              slv_r_resp_o,
  output logic                    slv_r_last_o,
  output logic [UserWidth-1:0]    slv_r_user_o,
  output logic                    slv_r_valid_o,
  input  logic                    slv_r_ready_i,

  output logic [IdWidth-1:0]      mst_aw_id_o,
  output logic [AddrWidth-1:0]    mst_aw_addr_o,
  output logic [7:0]              mst_aw_len_o,
  output logic [2:0]              mst_aw_size_o,
  output logic [1:0]              mst_aw_burst_o,
  output logic                    mst_aw_lock_o,
  output logic [3:0]              mst_aw_cache_o,
  output logic [2:0]              mst_aw_prot_o,
  output logic [3:0]              mst_aw_qos_o,
  output logic [3:0]              mst_aw_region_o,
  output logic [UserWidth-1:0]    mst_aw_user_o,
  output logic                    mst_aw_valid_o,
  input  logic                    mst_aw_ready_i,
  output logic [DataWidth-1:0]    mst_w_data_o,
  output logic [DataWidth/8-1:0]  mst_w_strb_o,
  output logic                    mst_w_last_o,
  output logic [UserWidth-1:0]    mst_w_user_o,
  output logic                    mst_w_valid_o,
  input  logic                    mst_w_ready_i,
  input  logic [IdWidth-1:0]      mst_b_id_i,
  input  logic [1:0]              mst_b_resp_i,
  input  logic [UserWidth-1:0]    mst_b_user_i,
  input  logic                    mst_b_valid_i,
  output logic                    mst_b_ready_o,
  output logic [IdWidth-1:0]      mst_ar_id_o,
  output logic [AddrWidth-1:0]    mst_ar_addr_o,
  output logic [7:0]              mst_ar_len_o,
  output logic [2:0]              mst_ar_size_o,
  output logic [1:0]              mst_ar_burst_o,
  output logic                    mst_ar_lock_o,
  output logic [3:0]              mst_ar_cache_o,
  output logic [2:0]              mst_ar_prot_o,
  output logic [3:0]              mst_ar_qos_o,
  output logic [3:0]              mst_ar_region_o,
  output logic [UserWidth-1:0]    mst_ar_user_o,
  output logic                    mst_ar_valid_o,
  input  logic                    mst_ar_ready_i,
  input  logic [IdWidth-1:0]      mst_r_id_i,
  input  logic [DataWidth-1:0]    mst_r_data_i,
  input  logic [1:0]              mst_r_resp_i,
  input  logic                    mst_r_last_i,
  input  logic [UserWidth-1:0]    mst_r_user_i,
  input  logic                    mst_r_valid_i,
  output logic                    mst_r_ready_o
);
  typedef logic [AddrWidth-1:0] addr_t;
  typedef logic [DataWidth-1:0] data_t;
  typedef logic [IdWidth-1:0] id_t;
  typedef logic [UserWidth-1:0] user_t;
  typedef logic [CfgAddrWidth-1:0] cfg_addr_t;
  typedef logic [CfgDataWidth-1:0] cfg_data_t;

  `AXI_TYPEDEF_AW_CHAN_T(aw_chan_t, addr_t, id_t, user_t)
  `AXI_TYPEDEF_W_CHAN_T(w_chan_t, data_t, data_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T(b_chan_t, id_t, user_t)
  `AXI_TYPEDEF_AR_CHAN_T(ar_chan_t, addr_t, id_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(r_chan_t, data_t, id_t, user_t)
  `AXI_TYPEDEF_REQ_T(axi_req_t, aw_chan_t, w_chan_t, ar_chan_t)
  `AXI_TYPEDEF_RESP_T(axi_resp_t, b_chan_t, r_chan_t)

  `AXI_LITE_TYPEDEF_AW_CHAN_T(cfg_aw_chan_t, cfg_addr_t)
  `AXI_LITE_TYPEDEF_W_CHAN_T(cfg_w_chan_t, cfg_data_t, logic [CfgDataWidth/8-1:0])
  `AXI_LITE_TYPEDEF_B_CHAN_T(cfg_b_chan_t)
  `AXI_LITE_TYPEDEF_AR_CHAN_T(cfg_ar_chan_t, cfg_addr_t)
  `AXI_LITE_TYPEDEF_R_CHAN_T(cfg_r_chan_t, cfg_data_t)
  `AXI_LITE_TYPEDEF_REQ_T(cfg_req_t, cfg_aw_chan_t, cfg_w_chan_t, cfg_ar_chan_t)
  `AXI_LITE_TYPEDEF_RESP_T(cfg_resp_t, cfg_b_chan_t, cfg_r_chan_t)

  axi_req_t slv_req, mst_req;
  axi_resp_t slv_resp, mst_resp;
  cfg_req_t cfg_req;
  cfg_resp_t cfg_resp;

  logic [7:0] reg_q [0:3];
  logic [7:0] reg_d [0:3];
  logic [3:0] reg_load;

  assign reg_d = '{default:8'h00};
  assign reg_load = '0;

  assign cfg_req.aw.addr  = cfg_aw_addr_i;
  assign cfg_req.aw.prot  = cfg_aw_prot_i;
  assign cfg_req.aw_valid = cfg_aw_valid_i;
  assign cfg_req.w.data   = cfg_w_data_i;
  assign cfg_req.w.strb   = cfg_w_strb_i;
  assign cfg_req.w_valid  = cfg_w_valid_i;
  assign cfg_req.b_ready  = cfg_b_ready_i;
  assign cfg_req.ar.addr  = cfg_ar_addr_i;
  assign cfg_req.ar.prot  = cfg_ar_prot_i;
  assign cfg_req.ar_valid = cfg_ar_valid_i;
  assign cfg_req.r_ready  = cfg_r_ready_i;

  assign cfg_aw_ready_o = cfg_resp.aw_ready;
  assign cfg_w_ready_o  = cfg_resp.w_ready;
  assign cfg_b_resp_o   = cfg_resp.b.resp;
  assign cfg_b_valid_o  = cfg_resp.b_valid;
  assign cfg_ar_ready_o = cfg_resp.ar_ready;
  assign cfg_r_data_o   = cfg_resp.r.data;
  assign cfg_r_resp_o   = cfg_resp.r.resp;
  assign cfg_r_valid_o  = cfg_resp.r_valid;

  axi_lite_regs #(
    .RegNumBytes  ( 32'd4        ),
    .AxiAddrWidth ( CfgAddrWidth ),
    .AxiDataWidth ( CfgDataWidth ),
    .byte_t       ( logic [7:0]  ),
    .RegRstVal    ( '{0: LenLimitResetVal, default: 8'h00} ),
    .req_lite_t   ( cfg_req_t    ),
    .resp_lite_t  ( cfg_resp_t   )
  ) i_axi_lite_regs (
    .clk_i,
    .rst_ni,
    .axi_req_i    ( cfg_req  ),
    .axi_resp_o   ( cfg_resp ),
    .wr_active_o  (          ),
    .rd_active_o  (          ),
    .reg_d_i      ( reg_d    ),
    .reg_load_i   ( reg_load ),
    .reg_q_o      ( reg_q    )
  );

  assign slv_req.aw = '{
    id: slv_aw_id_i, addr: slv_aw_addr_i, len: slv_aw_len_i, size: slv_aw_size_i,
    burst: slv_aw_burst_i, lock: slv_aw_lock_i, cache: slv_aw_cache_i, prot: slv_aw_prot_i,
    qos: slv_aw_qos_i, region: slv_aw_region_i, atop: '0, user: slv_aw_user_i};
  assign slv_req.aw_valid = slv_aw_valid_i;
  assign slv_req.w = '{data: slv_w_data_i, strb: slv_w_strb_i, last: slv_w_last_i, user: slv_w_user_i};
  assign slv_req.w_valid = slv_w_valid_i;
  assign slv_req.b_ready = slv_b_ready_i;
  assign slv_req.ar = '{
    id: slv_ar_id_i, addr: slv_ar_addr_i, len: slv_ar_len_i, size: slv_ar_size_i,
    burst: slv_ar_burst_i, lock: slv_ar_lock_i, cache: slv_ar_cache_i, prot: slv_ar_prot_i,
    qos: slv_ar_qos_i, region: slv_ar_region_i, user: slv_ar_user_i};
  assign slv_req.ar_valid = slv_ar_valid_i;
  assign slv_req.r_ready = slv_r_ready_i;

  assign slv_aw_ready_o = slv_resp.aw_ready;
  assign slv_w_ready_o  = slv_resp.w_ready;
  assign slv_b_id_o     = slv_resp.b.id;
  assign slv_b_resp_o   = slv_resp.b.resp;
  assign slv_b_user_o   = slv_resp.b.user;
  assign slv_b_valid_o  = slv_resp.b_valid;
  assign slv_ar_ready_o = slv_resp.ar_ready;
  assign slv_r_id_o     = slv_resp.r.id;
  assign slv_r_data_o   = slv_resp.r.data;
  assign slv_r_resp_o   = slv_resp.r.resp;
  assign slv_r_last_o   = slv_resp.r.last;
  assign slv_r_user_o   = slv_resp.r.user;
  assign slv_r_valid_o  = slv_resp.r_valid;

  assign mst_aw_id_o     = mst_req.aw.id;
  assign mst_aw_addr_o   = mst_req.aw.addr;
  assign mst_aw_len_o    = mst_req.aw.len;
  assign mst_aw_size_o   = mst_req.aw.size;
  assign mst_aw_burst_o  = mst_req.aw.burst;
  assign mst_aw_lock_o   = mst_req.aw.lock;
  assign mst_aw_cache_o  = mst_req.aw.cache;
  assign mst_aw_prot_o   = mst_req.aw.prot;
  assign mst_aw_qos_o    = mst_req.aw.qos;
  assign mst_aw_region_o = mst_req.aw.region;
  assign mst_aw_user_o   = mst_req.aw.user;
  assign mst_aw_valid_o  = mst_req.aw_valid;

  assign mst_w_data_o    = mst_req.w.data;
  assign mst_w_strb_o    = mst_req.w.strb;
  assign mst_w_last_o    = mst_req.w.last;
  assign mst_w_user_o    = mst_req.w.user;
  assign mst_w_valid_o   = mst_req.w_valid;

  assign mst_b_ready_o   = mst_req.b_ready;

  assign mst_ar_id_o     = mst_req.ar.id;
  assign mst_ar_addr_o   = mst_req.ar.addr;
  assign mst_ar_len_o    = mst_req.ar.len;
  assign mst_ar_size_o   = mst_req.ar.size;
  assign mst_ar_burst_o  = mst_req.ar.burst;
  assign mst_ar_lock_o   = mst_req.ar.lock;
  assign mst_ar_cache_o  = mst_req.ar.cache;
  assign mst_ar_prot_o   = mst_req.ar.prot;
  assign mst_ar_qos_o    = mst_req.ar.qos;
  assign mst_ar_region_o = mst_req.ar.region;
  assign mst_ar_user_o   = mst_req.ar.user;
  assign mst_ar_valid_o  = mst_req.ar_valid;

  assign mst_r_ready_o   = mst_req.r_ready;

  assign mst_resp.aw_ready = mst_aw_ready_i;
  assign mst_resp.w_ready  = mst_w_ready_i;
  assign mst_resp.b.id     = mst_b_id_i;
  assign mst_resp.b.resp   = mst_b_resp_i;
  assign mst_resp.b.user   = mst_b_user_i;
  assign mst_resp.b_valid  = mst_b_valid_i;
  assign mst_resp.ar_ready = mst_ar_ready_i;
  assign mst_resp.r.id     = mst_r_id_i;
  assign mst_resp.r.data   = mst_r_data_i;
  assign mst_resp.r.resp   = mst_r_resp_i;
  assign mst_resp.r.last   = mst_r_last_i;
  assign mst_resp.r.user   = mst_r_user_i;
  assign mst_resp.r_valid  = mst_r_valid_i;

  axi_burst_splitter_gran #(
    .MaxReadTxns   ( MaxReadTxns   ),
    .MaxWriteTxns  ( MaxWriteTxns  ),
    .FullBW        ( FullBW        ),
    .CutPath       ( CutPath       ),
    .DisableChecks ( DisableChecks ),
    .AddrWidth     ( AddrWidth     ),
    .DataWidth     ( DataWidth     ),
    .IdWidth       ( IdWidth       ),
    .UserWidth     ( UserWidth     ),
    .axi_req_t     ( axi_req_t     ),
    .axi_resp_t    ( axi_resp_t    ),
    .axi_aw_chan_t ( aw_chan_t     ),
    .axi_w_chan_t  ( w_chan_t      ),
    .axi_b_chan_t  ( b_chan_t      ),
    .axi_ar_chan_t ( ar_chan_t     ),
    .axi_r_chan_t  ( r_chan_t      )
  ) i_axi_burst_splitter_gran (
    .clk_i,
    .rst_ni,
    .len_limit_i ( reg_q[0] ),
    .slv_req_i   ( slv_req ),
    .slv_resp_o  ( slv_resp ),
    .mst_req_o   ( mst_req ),
    .mst_resp_i  ( mst_resp )
  );

endmodule
