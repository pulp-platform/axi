// Lint elaboration top for slang-server.
// Instantiates all parameterized AXI modules with concrete types so that
// slang can resolve struct member accesses (e.g. req.aw_valid) without
// falling back to the `logic` default.
//
// Design rules:
//   - All inputs are shared ports (one per type variant) -> slang sees unknown
//     values and won't constant-fold through them.
//   - Every module instance has its own dedicated output signal(s) exposed as
//     ports -> no multiply-driven wires, no unused-signal warnings.
`include "axi/typedef.svh"

// ---------------------------------------------------------------------------
// Concrete type package
// ---------------------------------------------------------------------------
package axi_lint_pkg;
  // --- full-AXI parameters -------------------------------------------------
  localparam int unsigned AW        = 32;
  localparam int unsigned DW        = 64;
  localparam int unsigned SW        = DW / 8;
  localparam int unsigned IW        = 8;   // standard / id-remap slave IW
  localparam int unsigned IW_NARROW = 4;   // xbar/mux slave IW, id-remap master IW
  localparam int unsigned IW_XMST   = 6;   // xbar/mux master IW (IW_NARROW + log2(4))
  localparam int unsigned UW        = 1;
  // --- AXI-Lite parameters -------------------------------------------------
  localparam int unsigned LITE_DW   = 32;
  localparam int unsigned LITE_SW   = LITE_DW / 8;
  localparam int unsigned LITE_MST_DW = 16;
  localparam int unsigned LITE_MST_SW = LITE_MST_DW / 8;
  // --- DW-converter parameters ---------------------------------------------
  localparam int unsigned DW_MST    = 32;
  localparam int unsigned SW_MST    = DW_MST / 8;
  // --- Xbar/mux parameters -------------------------------------------------
  localparam int unsigned XBAR_NO_SLV   = 4;
  localparam int unsigned XBAR_NO_MST   = 2;
  localparam int unsigned XBAR_NO_RULES = 2;

  // Base scalars
  typedef logic [AW-1:0]        addr_t;
  typedef logic [DW-1:0]        data_t;
  typedef logic [SW-1:0]        strb_t;
  typedef logic [IW-1:0]        id_t;
  typedef logic [IW_NARROW-1:0] id_narrow_t;
  typedef logic [IW_XMST-1:0]   id_xmst_t;
  typedef logic [UW-1:0]        user_t;

  // Standard full-AXI structs (IW = 8)
  `AXI_TYPEDEF_ALL(axi, addr_t, id_t, data_t, strb_t, user_t)

  // Narrow-ID structs (xbar/mux slave-side, id-remap master-side)
  `AXI_TYPEDEF_ALL_CT(axi_narrow,
    axi_narrow_req_t, axi_narrow_resp_t,
    addr_t, id_narrow_t, data_t, strb_t, user_t)

  // Extended-ID structs (xbar/mux master-side)
  `AXI_TYPEDEF_ALL_CT(axi_xmst,
    axi_xmst_req_t, axi_xmst_resp_t,
    addr_t, id_xmst_t, data_t, strb_t, user_t)

  // DW-downsized master structs (W/R channels with narrower data)
  typedef logic [DW_MST-1:0] dw_mst_data_t;
  typedef logic [SW_MST-1:0] dw_mst_strb_t;
  `AXI_TYPEDEF_W_CHAN_T(axi_dw_mst_w_t,    dw_mst_data_t, dw_mst_strb_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(axi_dw_mst_r_t,    dw_mst_data_t, id_t,          user_t)
  `AXI_TYPEDEF_REQ_T(axi_dw_mst_req_t,     axi_aw_chan_t,  axi_dw_mst_w_t, axi_ar_chan_t)
  `AXI_TYPEDEF_RESP_T(axi_dw_mst_resp_t,   axi_b_chan_t,   axi_dw_mst_r_t)

  // AXI-Lite structs
  typedef logic [AW-1:0]          lite_addr_t;
  typedef logic [LITE_DW-1:0]     lite_data_t;
  typedef logic [LITE_SW-1:0]     lite_strb_t;
  typedef logic [LITE_MST_DW-1:0] lite_mst_data_t;
  typedef logic [LITE_MST_SW-1:0] lite_mst_strb_t;
  `AXI_LITE_TYPEDEF_ALL(axi_lite, lite_addr_t, lite_data_t, lite_strb_t)
  `AXI_LITE_TYPEDEF_ALL_CT(axi_lite_mst,
    axi_lite_mst_req_t, axi_lite_mst_resp_t,
    lite_addr_t, lite_mst_data_t, lite_mst_strb_t)

  // APB structs (for axi_lite_to_apb) -- field names must match axi_lite_to_apb.sv
  typedef struct packed {
    lite_addr_t     paddr;
    axi_pkg::prot_t pprot;
    logic           psel;
    logic           penable;
    logic           pwrite;
    lite_data_t     pwdata;
    lite_strb_t     pstrb;
  } apb_req_t;
  typedef struct packed {
    logic       pready;
    lite_data_t prdata;
    logic       pslverr;
  } apb_resp_t;

  // Address-decode rule type
  typedef struct packed {
    int unsigned idx;
    addr_t       start_addr;
    addr_t       end_addr;
  } rule_t;

  // Xbar configuration
  localparam axi_pkg::xbar_cfg_t XbarCfg = '{
    NoSlvPorts:         XBAR_NO_SLV,
    NoMstPorts:         XBAR_NO_MST,
    MaxMstTrans:        4,
    MaxSlvTrans:        4,
    FallThrough:        1'b0,
    LatencyMode:        axi_pkg::CUT_ALL_AX,
    PipelineStages:     0,
    AxiIdWidthSlvPorts: IW_NARROW,
    AxiIdUsedSlvPorts:  IW_NARROW,
    UniqueIds:          1'b0,
    AxiAddrWidth:       AW,
    AxiDataWidth:       DW,
    NoAddrRules:        XBAR_NO_RULES
  };

endpackage

// ---------------------------------------------------------------------------
// Lint top module
// ---------------------------------------------------------------------------
module axi_lint_top
  import axi_lint_pkg::*;
  import axi_pkg::*;
(
  // ------------------------------------------------------------------
  // Shared inputs (one per type variant)
  // ------------------------------------------------------------------
  input  logic clk_i,
  input  logic rst_ni,

  // Standard full-AXI
  input  axi_req_t                           req_i,
  input  axi_resp_t                          resp_i,

  // Narrow-ID (xbar/mux slave-side, id-remap master-side)
  input  axi_narrow_req_t                    narrow_req_i,
  input  axi_narrow_resp_t                   narrow_resp_i,

  // Extended-ID (xbar/mux master-side)
  input  axi_xmst_resp_t                     xmst_resp_i,

  // DW-downsized
  input  axi_dw_mst_resp_t                   dw_mst_resp_i,

  // Mux slave array (4 slave ports)
  input  axi_narrow_req_t  [XBAR_NO_SLV-1:0] mux_slv_req_i,
  input  axi_narrow_resp_t [XBAR_NO_SLV-1:0] mux_slv_resp_i,

  // Xbar slave array
  input  axi_narrow_req_t  [XBAR_NO_SLV-1:0] xbar_slv_req_i,
  input  axi_narrow_resp_t [XBAR_NO_SLV-1:0] xbar_slv_resp_i,

  // AXI-Lite
  input  axi_lite_req_t                      lite_req_i,
  input  axi_lite_resp_t                     lite_resp_i,
  input  axi_lite_mst_resp_t                 lite_mst_resp_i,
  input  axi_lite_req_t  [XBAR_NO_SLV-1:0]  lite_slv_req_i,
  input  axi_lite_resp_t [XBAR_NO_SLV-1:0]  lite_slv_resp_i,
  input  apb_resp_t      [0:0]               apb_resp_i,
  input  rule_t          [XBAR_NO_RULES-1:0] addr_map_i,

  // ------------------------------------------------------------------
  // Per-instance outputs
  // ------------------------------------------------------------------
  output axi_req_t  cut_req_o,        output axi_resp_t cut_resp_o,
  output axi_req_t  multicut_req_o,   output axi_resp_t multicut_resp_o,
  output axi_req_t  delayer_req_o,    output axi_resp_t delayer_resp_o,
  output axi_req_t  fifo_req_o,       output axi_resp_t fifo_resp_o,
  output axi_req_t  fifo_dyn_req_o,   output axi_resp_t fifo_dyn_resp_o,
  output axi_req_t  isolate_req_o,    output axi_resp_t isolate_resp_o,
  output axi_resp_t err_slv_resp_o,
  output axi_req_t  serializer_req_o, output axi_resp_t serializer_resp_o,
  output axi_req_t  atop_req_o,       output axi_resp_t atop_resp_o,
  output axi_req_t  bsplit_req_o,     output axi_resp_t bsplit_resp_o,
  output axi_req_t  throttle_req_o,   output axi_resp_t throttle_resp_o,
  output axi_req_t  cdc_req_o,        output axi_resp_t cdc_resp_o,
  output axi_req_t  from_mem_req_o,

  // Burst splitter gran / unwrap
  output axi_req_t  bsplit_gran_req_o,   output axi_resp_t bsplit_gran_resp_o,
  output axi_req_t  bwrap_req_o,         output axi_resp_t bwrap_resp_o,

  // CDC src/dst standalone
  output axi_resp_t cdc_src_resp_o,
  output axi_req_t  cdc_dst_req_o,

  // rw_join / rw_split
  output axi_req_t  rw_join_req_o,
  output axi_resp_t rw_split_resp_o,
  output axi_req_t  rw_split_rd_req_o,
  output axi_req_t  rw_split_wr_req_o,

  // Demux
  output axi_req_t  [1:0] demux_req_o,
  output axi_req_t  [1:0] demux_simple_req_o,

  // Mux
  output axi_xmst_req_t   mux_req_o,
  output axi_narrow_resp_t [XBAR_NO_SLV-1:0] mux_resp_o,

  // Xbar
  output axi_xmst_req_t   [XBAR_NO_MST-1:0] xbar_mst_req_o,
  output axi_narrow_resp_t [XBAR_NO_SLV-1:0] xbar_slv_resp_o,
  output axi_xmst_req_t   [XBAR_NO_MST-1:0] ixbar_mst_req_o,
  output axi_narrow_resp_t [XBAR_NO_SLV-1:0] ixbar_slv_resp_o,
  output axi_narrow_req_t  [XBAR_NO_SLV-1:0] xbar_unmuxed_req_o,
  output axi_narrow_resp_t [XBAR_NO_SLV-1:0] xbar_unmuxed_resp_o,

  // ID-remapping
  output axi_narrow_req_t  id_remap_req_o,   output axi_narrow_resp_t id_remap_resp_o,
  output axi_narrow_req_t  id_ser_req_o,     output axi_narrow_resp_t id_ser_resp_o,
  output axi_narrow_req_t  iw_conv_req_o,    output axi_narrow_resp_t iw_conv_resp_o,

  // id_prepend
  output axi_req_t         id_prep_req_o,   output axi_resp_t id_prep_resp_o,
  output axi_narrow_resp_t id_prep_slv_resp_o,

  // modify_address
  output axi_req_t  mod_addr_req_o,   output axi_resp_t mod_addr_resp_o,

  // DW converter
  output axi_dw_mst_req_t  dw_down_req_o,  output axi_resp_t        dw_down_resp_o,
  output axi_req_t          dw_up_req_o,   output axi_dw_mst_resp_t  dw_up_resp_o,
  output axi_req_t          dw_conv_req_o,

  // AXI <-> AXI-Lite converters
  output axi_lite_req_t  to_lite_req_o,    output axi_resp_t       to_lite_resp_o,
  output axi_req_t        from_lite_req_o, output axi_lite_resp_t  from_lite_resp_o,

  // Inval filter
  output axi_req_t  inval_req_o,   output axi_resp_t inval_resp_o,

  // Compare / checker
  output axi_req_t  bus_cmp_req_o,  output axi_resp_t bus_cmp_resp_o,
  output axi_req_t  slv_cmp_rd_req_o, output axi_req_t slv_cmp_wr_req_o,

  // Memory adapters
  output axi_resp_t to_mem_resp_o,
  output axi_resp_t to_dmem_resp_o,
  output axi_resp_t to_banked_resp_o,
  output axi_resp_t to_interleaved_resp_o,
  output axi_resp_t to_split_resp_o,
  output axi_resp_t zero_mem_resp_o,

  // LFSR
  output axi_resp_t      lfsr_rsp_o,
  output axi_lite_resp_t lite_lfsr_rsp_o,

  // AXI-Lite
  output axi_lite_req_t   lite_mux_req_o,
  output axi_lite_resp_t  [1:0] lite_demux_resp_o,
  output axi_lite_req_t   [XBAR_NO_MST-1:0] lite_xbar_req_o,
  output axi_lite_resp_t  [XBAR_NO_SLV-1:0] lite_xbar_slv_resp_o,
  output axi_lite_req_t   lite_from_mem_req_o,
  output axi_lite_mst_req_t lite_dw_req_o, output axi_lite_resp_t lite_dw_slv_resp_o,
  output apb_req_t [0:0]  apb_req_o,       output axi_lite_resp_t apb_lite_resp_o,

  // AXI-Lite misc
  output axi_lite_resp_t [1:0] lite_mailbox_resp_o,
  output axi_lite_resp_t       lite_regs_resp_o,

  // Crosspoint
  output axi_narrow_req_t  [1:0] xp_mst_req_o,
  output axi_narrow_resp_t [1:0] xp_slv_resp_o
);

  // -------------------------------------------------------------------------
  // Simple passthrough / cut modules
  // -------------------------------------------------------------------------
  axi_cut #(
    .aw_chan_t(axi_aw_chan_t), .w_chan_t(axi_w_chan_t),
    .b_chan_t(axi_b_chan_t),   .ar_chan_t(axi_ar_chan_t), .r_chan_t(axi_r_chan_t),
    .axi_req_t(axi_req_t), .axi_resp_t(axi_resp_t)
  ) i_cut (.clk_i, .rst_ni,
           .slv_req_i(req_i),         .slv_resp_o(cut_resp_o),
           .mst_req_o(cut_req_o),     .mst_resp_i(resp_i));

  axi_multicut #(
    .aw_chan_t(axi_aw_chan_t), .w_chan_t(axi_w_chan_t),
    .b_chan_t(axi_b_chan_t),   .ar_chan_t(axi_ar_chan_t), .r_chan_t(axi_r_chan_t),
    .axi_req_t(axi_req_t), .axi_resp_t(axi_resp_t)
  ) i_multicut (.clk_i, .rst_ni,
                .slv_req_i(req_i),           .slv_resp_o(multicut_resp_o),
                .mst_req_o(multicut_req_o),  .mst_resp_i(resp_i));

  axi_delayer #(
    .aw_chan_t(axi_aw_chan_t), .w_chan_t(axi_w_chan_t),
    .b_chan_t(axi_b_chan_t),   .ar_chan_t(axi_ar_chan_t), .r_chan_t(axi_r_chan_t),
    .axi_req_t(axi_req_t), .axi_resp_t(axi_resp_t)
  ) i_delayer (.clk_i, .rst_ni,
               .slv_req_i(req_i),          .slv_resp_o(delayer_resp_o),
               .mst_req_o(delayer_req_o),  .mst_resp_i(resp_i));

  axi_fifo #(
    .aw_chan_t(axi_aw_chan_t), .w_chan_t(axi_w_chan_t),
    .b_chan_t(axi_b_chan_t),   .ar_chan_t(axi_ar_chan_t), .r_chan_t(axi_r_chan_t),
    .axi_req_t(axi_req_t), .axi_resp_t(axi_resp_t)
  ) i_fifo (.clk_i, .rst_ni, .test_i('0),
            .slv_req_i(req_i),       .slv_resp_o(fifo_resp_o),
            .mst_req_o(fifo_req_o),  .mst_resp_i(resp_i));

  axi_fifo_delay_dyn #(
    .aw_chan_t(axi_aw_chan_t), .w_chan_t(axi_w_chan_t),
    .b_chan_t(axi_b_chan_t),   .ar_chan_t(axi_ar_chan_t), .r_chan_t(axi_r_chan_t),
    .axi_req_t(axi_req_t), .axi_resp_t(axi_resp_t)
  ) i_fifo_dyn (.clk_i, .rst_ni,
                .aw_delay_i('0), .w_delay_i('0), .b_delay_i('0),
                .ar_delay_i('0), .r_delay_i('0),
                .slv_req_i(req_i),           .slv_resp_o(fifo_dyn_resp_o),
                .mst_req_o(fifo_dyn_req_o),  .mst_resp_i(resp_i));

  axi_isolate #(
    .axi_req_t(axi_req_t), .axi_resp_t(axi_resp_t)
  ) i_isolate (.clk_i, .rst_ni, .clr_i('0),
               .slv_req_i(req_i),          .slv_resp_o(isolate_resp_o),
               .mst_req_o(isolate_req_o),  .mst_resp_i(resp_i),
               .isolate_i('0), .isolated_o());

  axi_err_slv #(
    .axi_req_t(axi_req_t), .axi_resp_t(axi_resp_t)
  ) i_err_slv (.clk_i, .rst_ni, .test_i('0), .clr_i('0),
               .slv_req_i(req_i), .slv_resp_o(err_slv_resp_o));

  axi_serializer #(
    .axi_req_t(axi_req_t), .axi_resp_t(axi_resp_t)
  ) i_serializer (.clk_i, .rst_ni,
                  .slv_req_i(req_i),              .slv_resp_o(serializer_resp_o),
                  .mst_req_o(serializer_req_o),   .mst_resp_i(resp_i));

  axi_atop_filter #(
    .axi_req_t(axi_req_t), .axi_resp_t(axi_resp_t)
  ) i_atop (.clk_i, .rst_ni, .clr_i('0),
            .slv_req_i(req_i),      .slv_resp_o(atop_resp_o),
            .mst_req_o(atop_req_o), .mst_resp_i(resp_i));

  axi_burst_splitter #(
    .MaxReadTxns(32'd1), .MaxWriteTxns(32'd1),
    .AddrWidth(AW), .DataWidth(DW), .IdWidth(IW), .UserWidth(UW),
    .axi_req_t(axi_req_t), .axi_resp_t(axi_resp_t)
  ) i_burst_split (.clk_i, .rst_ni, .clr_i('0),
                   .slv_req_i(req_i),         .slv_resp_o(bsplit_resp_o),
                   .mst_req_o(bsplit_req_o),  .mst_resp_i(resp_i));

  axi_burst_splitter_gran #(
    .MaxReadTxns(32'd1), .MaxWriteTxns(32'd1),
    .AddrWidth(AW), .DataWidth(DW), .IdWidth(IW), .UserWidth(UW),
    .axi_req_t(axi_req_t), .axi_resp_t(axi_resp_t),
    .axi_aw_chan_t(axi_aw_chan_t), .axi_w_chan_t(axi_w_chan_t),
    .axi_b_chan_t(axi_b_chan_t),   .axi_ar_chan_t(axi_ar_chan_t),
    .axi_r_chan_t(axi_r_chan_t)
  ) i_burst_split_gran (.clk_i, .rst_ni, .clr_i('0), .len_limit_i('1),
                         .slv_req_i(req_i),               .slv_resp_o(bsplit_gran_resp_o),
                         .mst_req_o(bsplit_gran_req_o),   .mst_resp_i(resp_i));

  axi_burst_unwrap #(
    .AddrWidth(AW), .DataWidth(DW), .IdWidth(IW), .UserWidth(UW),
    .axi_req_t(axi_req_t), .axi_resp_t(axi_resp_t)
  ) i_burst_unwrap (.clk_i, .rst_ni, .clr_i('0),
                    .slv_req_i(req_i),         .slv_resp_o(bwrap_resp_o),
                    .mst_req_o(bwrap_req_o),   .mst_resp_i(resp_i));

  axi_throttle #(
    .axi_req_t(axi_req_t), .axi_rsp_t(axi_resp_t)
  ) i_throttle (.clk_i, .rst_ni,
                .req_i,            .rsp_o(throttle_resp_o),
                .req_o(throttle_req_o), .rsp_i(resp_i),
                .w_credit_i('1), .r_credit_i('1));

  // -------------------------------------------------------------------------
  // CDC (wrapper and standalone halves)
  // -------------------------------------------------------------------------
  axi_cdc #(
    .aw_chan_t(axi_aw_chan_t), .w_chan_t(axi_w_chan_t),
    .b_chan_t(axi_b_chan_t),   .ar_chan_t(axi_ar_chan_t), .r_chan_t(axi_r_chan_t),
    .axi_req_t(axi_req_t), .axi_resp_t(axi_resp_t)
  ) i_cdc (.src_clk_i(clk_i), .src_rst_ni(rst_ni),
           .src_req_i(req_i),        .src_resp_o(cdc_resp_o),
           .dst_clk_i(clk_i), .dst_rst_ni(rst_ni),
           .dst_req_o(cdc_req_o),    .dst_resp_i(resp_i));

  // Intermediate wires for cdc_src <-> cdc_dst (LogDepth=1 -> 2**1=2 entries)
  axi_aw_chan_t [1:0] cdc_async_aw_data;
  logic         [1:0] cdc_async_aw_wptr, cdc_async_aw_rptr;
  axi_w_chan_t  [1:0] cdc_async_w_data;
  logic         [1:0] cdc_async_w_wptr,  cdc_async_w_rptr;
  axi_b_chan_t  [1:0] cdc_async_b_data;
  logic         [1:0] cdc_async_b_wptr,  cdc_async_b_rptr;
  axi_ar_chan_t [1:0] cdc_async_ar_data;
  logic         [1:0] cdc_async_ar_wptr, cdc_async_ar_rptr;
  axi_r_chan_t  [1:0] cdc_async_r_data;
  logic         [1:0] cdc_async_r_wptr,  cdc_async_r_rptr;

  axi_cdc_src #(
    .aw_chan_t(axi_aw_chan_t), .w_chan_t(axi_w_chan_t),
    .b_chan_t(axi_b_chan_t),   .ar_chan_t(axi_ar_chan_t), .r_chan_t(axi_r_chan_t),
    .axi_req_t(axi_req_t), .axi_resp_t(axi_resp_t)
  ) i_cdc_src (
    .src_clk_i(clk_i), .src_rst_ni(rst_ni),
    .src_req_i(req_i),          .src_resp_o(cdc_src_resp_o),
    .async_data_master_aw_data_o(cdc_async_aw_data),
    .async_data_master_aw_wptr_o(cdc_async_aw_wptr),
    .async_data_master_aw_rptr_i(cdc_async_aw_rptr),
    .async_data_master_w_data_o(cdc_async_w_data),
    .async_data_master_w_wptr_o(cdc_async_w_wptr),
    .async_data_master_w_rptr_i(cdc_async_w_rptr),
    .async_data_master_b_data_i(cdc_async_b_data),
    .async_data_master_b_wptr_i(cdc_async_b_wptr),
    .async_data_master_b_rptr_o(cdc_async_b_rptr),
    .async_data_master_ar_data_o(cdc_async_ar_data),
    .async_data_master_ar_wptr_o(cdc_async_ar_wptr),
    .async_data_master_ar_rptr_i(cdc_async_ar_rptr),
    .async_data_master_r_data_i(cdc_async_r_data),
    .async_data_master_r_wptr_i(cdc_async_r_wptr),
    .async_data_master_r_rptr_o(cdc_async_r_rptr));

  axi_cdc_dst #(
    .aw_chan_t(axi_aw_chan_t), .w_chan_t(axi_w_chan_t),
    .b_chan_t(axi_b_chan_t),   .ar_chan_t(axi_ar_chan_t), .r_chan_t(axi_r_chan_t),
    .axi_req_t(axi_req_t), .axi_resp_t(axi_resp_t)
  ) i_cdc_dst (
    .dst_clk_i(clk_i), .dst_rst_ni(rst_ni),
    .dst_req_o(cdc_dst_req_o),   .dst_resp_i(resp_i),
    .async_data_slave_aw_data_i(cdc_async_aw_data),
    .async_data_slave_aw_wptr_i(cdc_async_aw_wptr),
    .async_data_slave_aw_rptr_o(cdc_async_aw_rptr),
    .async_data_slave_w_data_i(cdc_async_w_data),
    .async_data_slave_w_wptr_i(cdc_async_w_wptr),
    .async_data_slave_w_rptr_o(cdc_async_w_rptr),
    .async_data_slave_b_data_o(cdc_async_b_data),
    .async_data_slave_b_wptr_o(cdc_async_b_wptr),
    .async_data_slave_b_rptr_i(cdc_async_b_rptr),
    .async_data_slave_ar_data_i(cdc_async_ar_data),
    .async_data_slave_ar_wptr_i(cdc_async_ar_wptr),
    .async_data_slave_ar_rptr_o(cdc_async_ar_rptr),
    .async_data_slave_r_data_o(cdc_async_r_data),
    .async_data_slave_r_wptr_o(cdc_async_r_wptr),
    .async_data_slave_r_rptr_i(cdc_async_r_rptr));

  // -------------------------------------------------------------------------
  // Read/write split & join
  // -------------------------------------------------------------------------
  axi_rw_join #(
    .axi_req_t(axi_req_t), .axi_resp_t(axi_resp_t)
  ) i_rw_join (.clk_i, .rst_ni,
               .slv_read_req_i(req_i),   .slv_read_resp_o(),
               .slv_write_req_i(req_i),  .slv_write_resp_o(rw_split_resp_o),
               .mst_req_o(rw_join_req_o), .mst_resp_i(resp_i));

  axi_rw_split #(
    .axi_req_t(axi_req_t), .axi_resp_t(axi_resp_t)
  ) i_rw_split (.clk_i, .rst_ni,
                .slv_req_i(req_i),            .slv_resp_o(),
                .mst_read_req_o(rw_split_rd_req_o),  .mst_read_resp_i(resp_i),
                .mst_write_req_o(rw_split_wr_req_o), .mst_write_resp_i(resp_i));

  // -------------------------------------------------------------------------
  // Demux
  // -------------------------------------------------------------------------
  axi_demux #(
    .AxiIdWidth(IW), .NoMstPorts(2),
    .aw_chan_t(axi_aw_chan_t), .w_chan_t(axi_w_chan_t),
    .b_chan_t(axi_b_chan_t),   .ar_chan_t(axi_ar_chan_t), .r_chan_t(axi_r_chan_t),
    .axi_req_t(axi_req_t), .axi_resp_t(axi_resp_t)
  ) i_demux (.clk_i, .rst_ni, .test_i('0),
             .slv_req_i(req_i), .slv_aw_select_i('0), .slv_ar_select_i('0),
             .slv_resp_o(),
             .mst_reqs_o(demux_req_o), .mst_resps_i({resp_i, resp_i}));

  axi_demux_simple #(
    .AxiIdWidth(IW), .NoMstPorts(2),
    .axi_req_t(axi_req_t), .axi_resp_t(axi_resp_t)
  ) i_demux_simple (.clk_i, .rst_ni, .test_i('0), .clr_i('0),
                    .slv_req_i(req_i), .slv_aw_select_i('0), .slv_ar_select_i('0),
                    .slv_resp_o(),
                    .mst_reqs_o(demux_simple_req_o), .mst_resps_i({resp_i, resp_i}));

  // -------------------------------------------------------------------------
  // Mux (narrow slv -> extended mst)
  // -------------------------------------------------------------------------
  axi_mux #(
    .SlvAxiIDWidth(IW_NARROW), .NoSlvPorts(XBAR_NO_SLV),
    .slv_aw_chan_t(axi_narrow_aw_chan_t), .mst_aw_chan_t(axi_xmst_aw_chan_t),
    .w_chan_t(axi_w_chan_t),
    .slv_b_chan_t(axi_narrow_b_chan_t),   .mst_b_chan_t(axi_xmst_b_chan_t),
    .slv_ar_chan_t(axi_narrow_ar_chan_t), .mst_ar_chan_t(axi_xmst_ar_chan_t),
    .slv_r_chan_t(axi_narrow_r_chan_t),   .mst_r_chan_t(axi_xmst_r_chan_t),
    .slv_req_t(axi_narrow_req_t), .slv_resp_t(axi_narrow_resp_t),
    .mst_req_t(axi_xmst_req_t),   .mst_resp_t(axi_xmst_resp_t)
  ) i_mux (.clk_i, .rst_ni, .test_i('0),
           .slv_reqs_i(mux_slv_req_i), .slv_resps_o(mux_resp_o),
           .mst_req_o(mux_req_o),      .mst_resp_i(xmst_resp_i));

  // -------------------------------------------------------------------------
  // Xbar
  // -------------------------------------------------------------------------
  axi_xbar #(
    .Cfg(XbarCfg),
    .slv_aw_chan_t(axi_narrow_aw_chan_t), .mst_aw_chan_t(axi_xmst_aw_chan_t),
    .w_chan_t(axi_w_chan_t),
    .slv_b_chan_t(axi_narrow_b_chan_t),   .mst_b_chan_t(axi_xmst_b_chan_t),
    .slv_ar_chan_t(axi_narrow_ar_chan_t), .mst_ar_chan_t(axi_xmst_ar_chan_t),
    .slv_r_chan_t(axi_narrow_r_chan_t),   .mst_r_chan_t(axi_xmst_r_chan_t),
    .slv_req_t(axi_narrow_req_t), .slv_resp_t(axi_narrow_resp_t),
    .mst_req_t(axi_xmst_req_t),   .mst_resp_t(axi_xmst_resp_t),
    .rule_t(rule_t)
  ) i_xbar (.clk_i, .rst_ni, .test_i('0),
            .slv_ports_req_i(xbar_slv_req_i),   .slv_ports_resp_o(xbar_slv_resp_o),
            .mst_ports_req_o(xbar_mst_req_o),   .mst_ports_resp_i({xmst_resp_i, xmst_resp_i}),
            .addr_map_i, .en_default_mst_port_i('0), .default_mst_port_i('0));

  axi_interleaved_xbar #(
    .Cfg(XbarCfg),
    .slv_aw_chan_t(axi_narrow_aw_chan_t), .mst_aw_chan_t(axi_xmst_aw_chan_t),
    .w_chan_t(axi_w_chan_t),
    .slv_b_chan_t(axi_narrow_b_chan_t),   .mst_b_chan_t(axi_xmst_b_chan_t),
    .slv_ar_chan_t(axi_narrow_ar_chan_t), .mst_ar_chan_t(axi_xmst_ar_chan_t),
    .slv_r_chan_t(axi_narrow_r_chan_t),   .mst_r_chan_t(axi_xmst_r_chan_t),
    .slv_req_t(axi_narrow_req_t), .slv_resp_t(axi_narrow_resp_t),
    .mst_req_t(axi_xmst_req_t),   .mst_resp_t(axi_xmst_resp_t),
    .rule_t(rule_t)
  ) i_ixbar (.clk_i, .rst_ni, .test_i('0),
             .slv_ports_req_i(xbar_slv_req_i),   .slv_ports_resp_o(ixbar_slv_resp_o),
             .mst_ports_req_o(ixbar_mst_req_o),  .mst_ports_resp_i({xmst_resp_i, xmst_resp_i}),
             .addr_map_i, .interleaved_mode_ena_i('0),
             .en_default_mst_port_i('0), .default_mst_port_i('0));

  axi_xbar_unmuxed #(
    .Cfg(XbarCfg),
    .aw_chan_t(axi_narrow_aw_chan_t), .w_chan_t(axi_w_chan_t),
    .b_chan_t(axi_narrow_b_chan_t),   .ar_chan_t(axi_narrow_ar_chan_t),
    .r_chan_t(axi_narrow_r_chan_t),
    .req_t(axi_narrow_req_t), .resp_t(axi_narrow_resp_t),
    .rule_t(rule_t)
  ) i_xbar_unmuxed (.clk_i, .rst_ni, .test_i('0),
                    .slv_ports_req_i(xbar_slv_req_i),    .slv_ports_resp_o(xbar_unmuxed_resp_o),
                    .mst_ports_req_o(xbar_unmuxed_req_o), .mst_ports_resp_i(xbar_slv_resp_i),
                    .addr_map_i, .en_default_mst_port_i('0), .default_mst_port_i('0));

  // -------------------------------------------------------------------------
  // ID-remapping / converting
  // -------------------------------------------------------------------------
  axi_id_remap #(
    .AxiSlvPortIdWidth(IW), .AxiSlvPortMaxUniqIds(4), .AxiMaxTxnsPerId(2),
    .AxiMstPortIdWidth(IW_NARROW),
    .slv_req_t(axi_req_t), .slv_resp_t(axi_resp_t),
    .mst_req_t(axi_narrow_req_t), .mst_resp_t(axi_narrow_resp_t)
  ) i_id_remap (.clk_i, .rst_ni, .clr_i('0),
                .slv_req_i(req_i),            .slv_resp_o(id_remap_resp_o),
                .mst_req_o(id_remap_req_o),   .mst_resp_i(narrow_resp_i));

  axi_id_serialize #(
    .AxiSlvPortIdWidth(IW), .AxiSlvPortMaxTxns(4),
    .AxiMstPortIdWidth(IW_NARROW), .AxiMstPortMaxUniqIds(4), .AxiMstPortMaxTxnsPerId(2),
    .slv_req_t(axi_req_t), .slv_resp_t(axi_resp_t),
    .mst_req_t(axi_narrow_req_t), .mst_resp_t(axi_narrow_resp_t)
  ) i_id_ser (.clk_i, .rst_ni,
              .slv_req_i(req_i),         .slv_resp_o(id_ser_resp_o),
              .mst_req_o(id_ser_req_o),  .mst_resp_i(narrow_resp_i));

  axi_iw_converter #(
    .AxiSlvPortIdWidth(IW), .AxiMstPortIdWidth(IW_NARROW),
    .AxiSlvPortMaxUniqIds(4), .AxiSlvPortMaxTxnsPerId(2), .AxiMstPortMaxUniqIds(4),
    .slv_req_t(axi_req_t), .slv_resp_t(axi_resp_t),
    .mst_req_t(axi_narrow_req_t), .mst_resp_t(axi_narrow_resp_t)
  ) i_iw_conv (.clk_i, .rst_ni,
               .slv_req_i(req_i),          .slv_resp_o(iw_conv_resp_o),
               .mst_req_o(iw_conv_req_o),  .mst_resp_i(narrow_resp_i));

  axi_id_prepend #(
    .AxiIdWidthSlvPort(IW_NARROW), .AxiIdWidthMstPort(IW),
    .slv_aw_chan_t(axi_narrow_aw_chan_t), .slv_w_chan_t(axi_w_chan_t),
    .slv_b_chan_t(axi_narrow_b_chan_t),   .slv_ar_chan_t(axi_narrow_ar_chan_t),
    .slv_r_chan_t(axi_narrow_r_chan_t),
    .mst_aw_chan_t(axi_aw_chan_t), .mst_w_chan_t(axi_w_chan_t),
    .mst_b_chan_t(axi_b_chan_t),   .mst_ar_chan_t(axi_ar_chan_t),
    .mst_r_chan_t(axi_r_chan_t)
  ) i_id_prep (
    .pre_id_i('0),
    .slv_aw_chans_i(narrow_req_i.aw),      .slv_aw_valids_i(narrow_req_i.aw_valid),
    .slv_aw_readies_o(id_prep_slv_resp_o.aw_ready),
    .slv_w_chans_i(narrow_req_i.w),        .slv_w_valids_i(narrow_req_i.w_valid),
    .slv_w_readies_o(id_prep_slv_resp_o.w_ready),
    .slv_b_chans_o(id_prep_slv_resp_o.b),  .slv_b_valids_o(id_prep_slv_resp_o.b_valid),
    .slv_b_readies_i(narrow_req_i.b_ready),
    .slv_ar_chans_i(narrow_req_i.ar),      .slv_ar_valids_i(narrow_req_i.ar_valid),
    .slv_ar_readies_o(id_prep_slv_resp_o.ar_ready),
    .slv_r_chans_o(id_prep_slv_resp_o.r),  .slv_r_valids_o(id_prep_slv_resp_o.r_valid),
    .slv_r_readies_i(narrow_req_i.r_ready),
    .mst_aw_chans_o(id_prep_req_o.aw),     .mst_aw_valids_o(id_prep_req_o.aw_valid),
    .mst_aw_readies_i(id_prep_resp_o.aw_ready),
    .mst_w_chans_o(id_prep_req_o.w),       .mst_w_valids_o(id_prep_req_o.w_valid),
    .mst_w_readies_i(id_prep_resp_o.w_ready),
    .mst_b_chans_i(id_prep_resp_o.b),      .mst_b_valids_i(id_prep_resp_o.b_valid),
    .mst_b_readies_o(id_prep_req_o.b_ready),
    .mst_ar_chans_o(id_prep_req_o.ar),     .mst_ar_valids_o(id_prep_req_o.ar_valid),
    .mst_ar_readies_i(id_prep_resp_o.ar_ready),
    .mst_r_chans_i(id_prep_resp_o.r),      .mst_r_valids_i(id_prep_resp_o.r_valid),
    .mst_r_readies_o(id_prep_req_o.r_ready));

  axi_modify_address #(
    .slv_req_t(axi_req_t), .mst_addr_t(addr_t),
    .mst_req_t(axi_req_t), .axi_resp_t(axi_resp_t)
  ) i_mod_addr (.slv_req_i(req_i),              .slv_resp_o(mod_addr_resp_o),
                .mst_aw_addr_i('0), .mst_ar_addr_i('0),
                .mst_req_o(mod_addr_req_o),     .mst_resp_i(resp_i));

  // -------------------------------------------------------------------------
  // DW converter (slave=64-bit, master=32-bit)
  // -------------------------------------------------------------------------
  axi_dw_downsizer #(
    .AxiMaxReads(4), .AxiSlvPortDataWidth(DW), .AxiMstPortDataWidth(DW_MST),
    .AxiAddrWidth(AW), .AxiIdWidth(IW),
    .aw_chan_t(axi_aw_chan_t), .mst_w_chan_t(axi_dw_mst_w_t), .slv_w_chan_t(axi_w_chan_t),
    .b_chan_t(axi_b_chan_t),   .ar_chan_t(axi_ar_chan_t),
    .mst_r_chan_t(axi_dw_mst_r_t), .slv_r_chan_t(axi_r_chan_t),
    .axi_mst_req_t(axi_dw_mst_req_t), .axi_mst_resp_t(axi_dw_mst_resp_t),
    .axi_slv_req_t(axi_req_t),        .axi_slv_resp_t(axi_resp_t)
  ) i_dw_down (.clk_i, .rst_ni, .clr_i('0),
               .slv_req_i(req_i),            .slv_resp_o(dw_down_resp_o),
               .mst_req_o(dw_down_req_o),    .mst_resp_i(dw_mst_resp_i));

  axi_dw_upsizer #(
    .AxiMaxReads(4), .AxiSlvPortDataWidth(DW_MST), .AxiMstPortDataWidth(DW),
    .AxiAddrWidth(AW), .AxiIdWidth(IW),
    .aw_chan_t(axi_aw_chan_t), .mst_w_chan_t(axi_w_chan_t), .slv_w_chan_t(axi_dw_mst_w_t),
    .b_chan_t(axi_b_chan_t),   .ar_chan_t(axi_ar_chan_t),
    .mst_r_chan_t(axi_r_chan_t), .slv_r_chan_t(axi_dw_mst_r_t),
    .axi_mst_req_t(axi_req_t),         .axi_mst_resp_t(axi_resp_t),
    .axi_slv_req_t(axi_dw_mst_req_t),  .axi_slv_resp_t(axi_dw_mst_resp_t)
  ) i_dw_up (.clk_i, .rst_ni, .clr_i('0),
             .slv_req_i('0),           .slv_resp_o(dw_up_resp_o),
             .mst_req_o(dw_up_req_o),  .mst_resp_i(resp_i));

  axi_dw_converter #(
    .AxiMaxReads(4), .AxiSlvPortDataWidth(DW_MST), .AxiMstPortDataWidth(DW),
    .AxiAddrWidth(AW), .AxiIdWidth(IW),
    .aw_chan_t(axi_aw_chan_t), .mst_w_chan_t(axi_w_chan_t), .slv_w_chan_t(axi_dw_mst_w_t),
    .b_chan_t(axi_b_chan_t),   .ar_chan_t(axi_ar_chan_t),
    .mst_r_chan_t(axi_r_chan_t), .slv_r_chan_t(axi_dw_mst_r_t),
    .axi_mst_req_t(axi_req_t),         .axi_mst_resp_t(axi_resp_t),
    .axi_slv_req_t(axi_dw_mst_req_t),  .axi_slv_resp_t(axi_dw_mst_resp_t)
  ) i_dw_conv (.clk_i, .rst_ni,
               .slv_req_i('0),              .slv_resp_o(),
               .mst_req_o(dw_conv_req_o),   .mst_resp_i(resp_i));

  // -------------------------------------------------------------------------
  // AXI <-> AXI-Lite converters
  // -------------------------------------------------------------------------
  axi_to_axi_lite #(
    .AxiAddrWidth(AW), .AxiDataWidth(DW), .AxiIdWidth(IW), .AxiUserWidth(UW),
    .AxiMaxWriteTxns(4), .AxiMaxReadTxns(4),
    .full_req_t(axi_req_t), .full_resp_t(axi_resp_t),
    .lite_req_t(axi_lite_req_t), .lite_resp_t(axi_lite_resp_t)
  ) i_to_lite (.clk_i, .rst_ni, .test_i('0),
               .slv_req_i(req_i),           .slv_resp_o(to_lite_resp_o),
               .mst_req_o(to_lite_req_o),   .mst_resp_i(lite_resp_i));

  axi_lite_to_axi #(
    .AxiDataWidth(LITE_DW),
    .req_lite_t(axi_lite_req_t), .resp_lite_t(axi_lite_resp_t),
    .axi_req_t(axi_req_t), .axi_resp_t(axi_resp_t)
  ) i_from_lite (.slv_req_lite_i(lite_req_i),      .slv_resp_lite_o(from_lite_resp_o),
                 .slv_aw_cache_i('0), .slv_ar_cache_i('0),
                 .mst_req_o(from_lite_req_o),       .mst_resp_i(resp_i));

  // -------------------------------------------------------------------------
  // Misc full-AXI
  // -------------------------------------------------------------------------
  axi_inval_filter #(
    .MaxTxns(4), .AddrWidth(AW), .L1LineWidth(64),
    .aw_chan_t(axi_aw_chan_t), .req_t(axi_req_t), .resp_t(axi_resp_t)
  ) i_inval (.clk_i, .rst_ni, .clr_i('0), .en_i('1),
             .slv_req_i(req_i),        .slv_resp_o(inval_resp_o),
             .mst_req_o(inval_req_o),  .mst_resp_i(resp_i),
             .inval_addr_o(), .inval_valid_o(), .inval_ready_i('1));

  axi_bus_compare #(
    .AxiIdWidth(IW), .DataWidth(DW),
    .axi_aw_chan_t(axi_aw_chan_t), .axi_w_chan_t(axi_w_chan_t),
    .axi_b_chan_t(axi_b_chan_t),   .axi_ar_chan_t(axi_ar_chan_t), .axi_r_chan_t(axi_r_chan_t),
    .axi_req_t(axi_req_t), .axi_rsp_t(axi_resp_t)
  ) i_bus_cmp (.clk_i, .rst_ni, .clr_i('0), .testmode_i('0),
               .axi_a_req_i(req_i),          .axi_a_rsp_o(bus_cmp_resp_o),
               .axi_a_req_o(bus_cmp_req_o),  .axi_a_rsp_i(resp_i),
               .axi_b_req_i(req_i),          .axi_b_rsp_o(),
               .axi_b_req_o(),               .axi_b_rsp_i(resp_i),
               .aw_mismatch_o(), .w_mismatch_o(), .b_mismatch_o(),
               .ar_mismatch_o(), .r_mismatch_o(), .mismatch_o(), .busy_o());

  axi_slave_compare #(
    .AxiIdWidth(IW), .DataWidth(DW),
    .axi_aw_chan_t(axi_aw_chan_t), .axi_w_chan_t(axi_w_chan_t),
    .axi_b_chan_t(axi_b_chan_t),   .axi_ar_chan_t(axi_ar_chan_t), .axi_r_chan_t(axi_r_chan_t),
    .axi_req_t(axi_req_t), .axi_rsp_t(axi_resp_t)
  ) i_slv_cmp (.clk_i, .rst_ni, .testmode_i('0),
               .axi_mst_req_i(req_i),              .axi_mst_rsp_o(),
               .axi_ref_req_o(slv_cmp_rd_req_o),   .axi_ref_rsp_i(resp_i),
               .axi_test_req_o(slv_cmp_wr_req_o),  .axi_test_rsp_i(resp_i),
               .aw_mismatch_o(), .w_mismatch_o(), .b_mismatch_o(),
               .ar_mismatch_o(), .r_mismatch_o(), .mismatch_o(), .busy_o());

  // -------------------------------------------------------------------------
  // Memory adapters
  // -------------------------------------------------------------------------
  axi_from_mem #(
    .MemAddrWidth(AW), .AxiAddrWidth(AW), .DataWidth(DW), .MaxRequests(4),
    .axi_req_t(axi_req_t), .axi_rsp_t(axi_resp_t)
  ) i_from_mem (.clk_i, .rst_ni,
                .mem_req_i('0), .mem_addr_i('0), .mem_we_i('0),
                .mem_wdata_i('0), .mem_be_i('0),
                .mem_gnt_o(), .mem_rsp_valid_o(), .mem_rsp_rdata_o(), .mem_rsp_error_o(),
                .slv_aw_cache_i('0), .slv_ar_cache_i('0),
                .axi_req_o(from_mem_req_o), .axi_rsp_i(resp_i));

  axi_to_mem #(
    .axi_req_t(axi_req_t), .axi_resp_t(axi_resp_t),
    .AddrWidth(AW), .DataWidth(DW), .IdWidth(IW), .NumBanks(1), .BufDepth(4)
  ) i_to_mem (.clk_i, .rst_ni,
              .busy_o(),
              .axi_req_i(req_i), .axi_resp_o(to_mem_resp_o),
              .mem_req_o(), .mem_gnt_i('1), .mem_addr_o(), .mem_wdata_o(),
              .mem_strb_o(), .mem_atop_o(), .mem_we_o(),
              .mem_rvalid_i('0), .mem_rdata_i('0));

  axi_to_detailed_mem #(
    .axi_req_t(axi_req_t), .axi_resp_t(axi_resp_t),
    .AddrWidth(AW), .DataWidth(DW), .IdWidth(IW), .UserWidth(UW),
    .NumBanks(1), .BufDepth(4)
  ) i_to_dmem (.clk_i, .rst_ni,
               .busy_o(),
               .axi_req_i(req_i), .axi_resp_o(to_dmem_resp_o),
               .mem_req_o(), .mem_gnt_i('1), .mem_addr_o(), .mem_wdata_o(),
               .mem_strb_o(), .mem_atop_o(), .mem_lock_o(), .mem_we_o(),
               .mem_id_o(), .mem_user_o(), .mem_cache_o(), .mem_prot_o(),
               .mem_qos_o(), .mem_region_o(),
               .mem_rvalid_i('0), .mem_rdata_i('0), .mem_err_i('0), .mem_exokay_i('0));

  axi_to_mem_banked #(
    .AxiIdWidth(IW), .AxiAddrWidth(AW), .AxiDataWidth(DW),
    .axi_aw_chan_t(axi_aw_chan_t), .axi_w_chan_t(axi_w_chan_t),
    .axi_b_chan_t(axi_b_chan_t),   .axi_ar_chan_t(axi_ar_chan_t),
    .axi_r_chan_t(axi_r_chan_t),
    .axi_req_t(axi_req_t), .axi_resp_t(axi_resp_t),
    .MemNumBanks(1), .MemAddrWidth(AW - $clog2(DW/8) - 1), .MemDataWidth(DW)
  ) i_to_banked (.clk_i, .rst_ni, .test_i('0),
                 .axi_req_i(req_i), .axi_resp_o(to_banked_resp_o),
                 .mem_req_o(), .mem_gnt_i('1), .mem_add_o(), .mem_we_o(),
                 .mem_wdata_o(), .mem_be_o(), .mem_atop_o(),
                 .mem_rdata_i('0), .axi_to_mem_busy_o());

  axi_to_mem_interleaved #(
    .axi_req_t(axi_req_t), .axi_resp_t(axi_resp_t),
    .AddrWidth(AW), .DataWidth(DW), .IdWidth(IW), .NumBanks(1), .BufDepth(4)
  ) i_to_interleaved (.clk_i, .rst_ni, .test_i('0),
                       .busy_o(),
                       .axi_req_i(req_i), .axi_resp_o(to_interleaved_resp_o),
                       .mem_req_o(), .mem_gnt_i('1), .mem_addr_o(), .mem_wdata_o(),
                       .mem_strb_o(), .mem_atop_o(), .mem_we_o(),
                       .mem_rvalid_i('0), .mem_rdata_i('0));

  axi_to_mem_split #(
    .axi_req_t(axi_req_t), .axi_resp_t(axi_resp_t),
    .AddrWidth(AW), .AxiDataWidth(DW), .IdWidth(IW),
    .MemDataWidth(DW), .NumMemPorts(2), .BufDepth(4)
  ) i_to_split (.clk_i, .rst_ni, .test_i('0),
                .busy_o(),
                .axi_req_i(req_i), .axi_resp_o(to_split_resp_o),
                .mem_req_o(), .mem_gnt_i('1), .mem_addr_o(), .mem_wdata_o(),
                .mem_strb_o(), .mem_atop_o(), .mem_we_o(),
                .mem_rvalid_i('0), .mem_rdata_i('0));

  axi_zero_mem #(
    .axi_req_t(axi_req_t), .axi_resp_t(axi_resp_t),
    .AddrWidth(AW), .DataWidth(DW), .IdWidth(IW), .NumBanks(1), .BufDepth(4)
  ) i_zero_mem (.clk_i, .rst_ni,
                .busy_o(),
                .axi_req_i(req_i), .axi_resp_o(zero_mem_resp_o));

  // -------------------------------------------------------------------------
  // LFSR
  // -------------------------------------------------------------------------
  axi_lfsr #(
    .DataWidth(DW), .AddrWidth(AW), .IdWidth(IW), .UserWidth(UW),
    .axi_req_t(axi_req_t), .axi_rsp_t(axi_resp_t)
  ) i_lfsr (.clk_i, .rst_ni, .testmode_i('0),
            .req_i, .rsp_o(lfsr_rsp_o),
            .w_ser_data_i('0), .w_ser_data_o(), .w_ser_en_i('0),
            .r_ser_data_i('0), .r_ser_data_o(), .r_ser_en_i('0));

  axi_lite_lfsr #(
    .DataWidth(LITE_DW),
    .axi_lite_req_t(axi_lite_req_t), .axi_lite_rsp_t(axi_lite_resp_t)
  ) i_lite_lfsr (.clk_i, .rst_ni, .testmode_i('0),
                 .req_i(lite_req_i), .rsp_o(lite_lfsr_rsp_o),
                 .w_ser_data_i('0), .w_ser_data_o(), .w_ser_en_i('0),
                 .r_ser_data_i('0), .r_ser_data_o(), .r_ser_en_i('0));

  // -------------------------------------------------------------------------
  // AXI-Lite
  // -------------------------------------------------------------------------
  axi_lite_mux #(
    .aw_chan_t(axi_lite_aw_chan_t), .w_chan_t(axi_lite_w_chan_t),
    .b_chan_t(axi_lite_b_chan_t),   .ar_chan_t(axi_lite_ar_chan_t), .r_chan_t(axi_lite_r_chan_t),
    .axi_req_t(axi_lite_req_t), .axi_resp_t(axi_lite_resp_t),
    .NoSlvPorts(XBAR_NO_SLV), .MaxTrans(4)
  ) i_lite_mux (.clk_i, .rst_ni, .test_i('0),
                .slv_reqs_i(lite_slv_req_i), .slv_resps_o(),
                .mst_req_o(lite_mux_req_o),  .mst_resp_i(lite_resp_i));

  axi_lite_demux #(
    .aw_chan_t(axi_lite_aw_chan_t), .w_chan_t(axi_lite_w_chan_t),
    .b_chan_t(axi_lite_b_chan_t),   .ar_chan_t(axi_lite_ar_chan_t), .r_chan_t(axi_lite_r_chan_t),
    .axi_req_t(axi_lite_req_t), .axi_resp_t(axi_lite_resp_t),
    .NoMstPorts(2)
  ) i_lite_demux (.clk_i, .rst_ni, .test_i('0), .clr_i('0),
                  .slv_req_i(lite_req_i), .slv_aw_select_i('0), .slv_ar_select_i('0),
                  .slv_resp_o(),
                  .mst_reqs_o(), .mst_resps_i({lite_demux_resp_o[1], lite_demux_resp_o[0]}));

  axi_lite_xbar #(
    .Cfg(XbarCfg),
    .aw_chan_t(axi_lite_aw_chan_t), .w_chan_t(axi_lite_w_chan_t),
    .b_chan_t(axi_lite_b_chan_t),   .ar_chan_t(axi_lite_ar_chan_t), .r_chan_t(axi_lite_r_chan_t),
    .axi_req_t(axi_lite_req_t), .axi_resp_t(axi_lite_resp_t),
    .rule_t(rule_t)
  ) i_lite_xbar (.clk_i, .rst_ni, .test_i('0),
                 .slv_ports_req_i(lite_slv_req_i),   .slv_ports_resp_o(lite_xbar_slv_resp_o),
                 .mst_ports_req_o(lite_xbar_req_o),  .mst_ports_resp_i({lite_resp_i, lite_resp_i}),
                 .addr_map_i, .en_default_mst_port_i('0), .default_mst_port_i('0));

  axi_lite_from_mem #(
    .MemAddrWidth(AW), .AxiAddrWidth(AW), .DataWidth(LITE_DW), .MaxRequests(4),
    .axi_req_t(axi_lite_req_t), .axi_rsp_t(axi_lite_resp_t)
  ) i_lite_from_mem (.clk_i, .rst_ni,
                     .mem_req_i('0), .mem_addr_i('0), .mem_we_i('0),
                     .mem_wdata_i('0), .mem_be_i('0),
                     .mem_gnt_o(), .mem_rsp_valid_o(), .mem_rsp_rdata_o(), .mem_rsp_error_o(),
                     .axi_req_o(lite_from_mem_req_o), .axi_rsp_i(lite_resp_i));

  axi_lite_dw_converter #(
    .AxiAddrWidth(AW), .AxiSlvPortDataWidth(LITE_DW), .AxiMstPortDataWidth(LITE_MST_DW),
    .axi_lite_aw_t(axi_lite_aw_chan_t),
    .axi_lite_slv_w_t(axi_lite_w_chan_t), .axi_lite_mst_w_t(axi_lite_mst_w_chan_t),
    .axi_lite_b_t(axi_lite_b_chan_t),     .axi_lite_ar_t(axi_lite_ar_chan_t),
    .axi_lite_slv_r_t(axi_lite_r_chan_t), .axi_lite_mst_r_t(axi_lite_mst_r_chan_t),
    .axi_lite_slv_req_t(axi_lite_req_t),  .axi_lite_slv_res_t(axi_lite_resp_t),
    .axi_lite_mst_req_t(axi_lite_mst_req_t), .axi_lite_mst_res_t(axi_lite_mst_resp_t)
  ) i_lite_dw (.clk_i, .rst_ni,
               .slv_req_i(lite_req_i),         .slv_res_o(lite_dw_slv_resp_o),
               .mst_req_o(lite_dw_req_o),       .mst_res_i(lite_mst_resp_i));

  axi_lite_to_apb #(
    .NoApbSlaves(1), .NoRules(1), .AddrWidth(AW), .DataWidth(LITE_DW),
    .axi_lite_req_t(axi_lite_req_t), .axi_lite_resp_t(axi_lite_resp_t),
    .apb_req_t(apb_req_t), .apb_resp_t(apb_resp_t),
    .rule_t(rule_t)
  ) i_lite_to_apb (.clk_i, .rst_ni,
                   .axi_lite_req_i(lite_req_i),    .axi_lite_resp_o(apb_lite_resp_o),
                   .apb_req_o,                     .apb_resp_i,
                   .addr_map_i(addr_map_i[0:0]));

  // -------------------------------------------------------------------------
  // AXI-Lite mailbox and registers
  // -------------------------------------------------------------------------
  axi_lite_mailbox #(
    .MailboxDepth(4), .AxiAddrWidth(AW), .AxiDataWidth(LITE_DW),
    .req_lite_t(axi_lite_req_t), .resp_lite_t(axi_lite_resp_t)
  ) i_lite_mailbox (.clk_i, .rst_ni, .test_i('0),
                    .slv_reqs_i(lite_slv_req_i[1:0]),
                    .slv_resps_o(lite_mailbox_resp_o),
                    .irq_o(), .base_addr_i('0));

  axi_lite_regs #(
    .RegNumBytes(4), .AxiAddrWidth(AW), .AxiDataWidth(LITE_DW),
    .req_lite_t(axi_lite_req_t), .resp_lite_t(axi_lite_resp_t)
  ) i_lite_regs (.clk_i, .rst_ni,
                 .axi_req_i(lite_req_i), .axi_resp_o(lite_regs_resp_o),
                 .wr_active_o(), .rd_active_o(),
                 .reg_d_i('0), .reg_load_i('0), .reg_q_o());

  // -------------------------------------------------------------------------
  // Crosspoint (axi_xp): 2 slave + 2 master ports, homomorphous narrow type
  // -------------------------------------------------------------------------
  localparam axi_pkg::xbar_cfg_t XpCfg = '{
    NoSlvPorts:         2,
    NoMstPorts:         2,
    MaxMstTrans:        4,
    MaxSlvTrans:        4,
    FallThrough:        1'b0,
    LatencyMode:        axi_pkg::CUT_ALL_AX,
    PipelineStages:     0,
    AxiIdWidthSlvPorts: IW_NARROW,
    AxiIdUsedSlvPorts:  IW_NARROW,
    UniqueIds:          1'b0,
    AxiAddrWidth:       AW,
    AxiDataWidth:       DW,
    NoAddrRules:        XBAR_NO_RULES
  };

  axi_xp #(
    .Cfg(XpCfg),
    .NumSlvPorts(2), .NumMstPorts(2), .NumAddrRules(XBAR_NO_RULES),
    .AxiAddrWidth(AW), .AxiDataWidth(DW), .AxiIdWidth(IW_NARROW), .AxiUserWidth(UW),
    .AxiSlvPortMaxUniqIds(4), .AxiSlvPortMaxTxnsPerId(2), .AxiSlvPortMaxTxns(8),
    .AxiMstPortMaxUniqIds(4), .AxiMstPortMaxTxnsPerId(2),
    .axi_req_t(axi_narrow_req_t), .axi_resp_t(axi_narrow_resp_t),
    .rule_t(rule_t)
  ) i_xp (.clk_i, .rst_ni, .test_en_i('0),
           .slv_req_i(xbar_slv_req_i[1:0]),  .slv_resp_o(xp_slv_resp_o),
           .mst_req_o(xp_mst_req_o),          .mst_resp_i({narrow_resp_i, narrow_resp_i}),
           .addr_map_i);

endmodule
