// Copyright (c) 2019-2020 ETH Zurich, University of Bologna
//
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
// - Luca Valente <luca.valente@unibo.it>
// - Andreas Kurth <akurth@iis.ee.ethz.ch>

`include "axi/assign.svh"
`include "axi/typedef.svh"

/// Source-clock-domain half of the AXI CDC crossing.
///
/// For each of the five AXI channels, this module instantiates the source or destination half of
/// a CDC FIFO.  IMPORTANT: For each AXI channel, you MUST properly constrain three paths through
/// the FIFO; see the header of `cdc_fifo_gray` for instructions.
module axi_cdc_src #(
  /// Depth of the FIFO crossing the clock domain, given as 2**LOG_DEPTH.
  parameter int unsigned LogDepth = 1,
  parameter type aw_chan_t = logic,
  parameter type w_chan_t = logic,
  parameter type b_chan_t = logic,
  parameter type ar_chan_t = logic,
  parameter type r_chan_t = logic,
  parameter type axi_req_t = logic,
  parameter type axi_rsp_t = logic
) (
  // synchronous subordinate port - clocked by `src_clk_i`
  input  logic                        src_clk_i,
  input  logic                        src_rst_ni,
  input  axi_req_t                    src_req_i,
  output axi_rsp_t                    src_rsp_o,
  // asynchronous manager port
  output aw_chan_t  [2**LogDepth-1:0] async_data_manager_aw_data_o,
  output logic           [LogDepth:0] async_data_manager_aw_wptr_o,
  input  logic           [LogDepth:0] async_data_manager_aw_rptr_i,
  output w_chan_t   [2**LogDepth-1:0] async_data_manager_w_data_o,
  output logic           [LogDepth:0] async_data_manager_w_wptr_o,
  input  logic           [LogDepth:0] async_data_manager_w_rptr_i,
  input  b_chan_t   [2**LogDepth-1:0] async_data_manager_b_data_i,
  input  logic           [LogDepth:0] async_data_manager_b_wptr_i,
  output logic           [LogDepth:0] async_data_manager_b_rptr_o,
  output ar_chan_t  [2**LogDepth-1:0] async_data_manager_ar_data_o,
  output logic           [LogDepth:0] async_data_manager_ar_wptr_o,
  input  logic           [LogDepth:0] async_data_manager_ar_rptr_i,
  input  r_chan_t   [2**LogDepth-1:0] async_data_manager_r_data_i,
  input  logic           [LogDepth:0] async_data_manager_r_wptr_i,
  output logic           [LogDepth:0] async_data_manager_r_rptr_o
);

  cdc_fifo_gray_src #(
    // Workaround for a bug in Questa (see comment in `axi_cdc_dst` for details).
`ifdef QUESTA
    .T         ( logic [$bits(aw_chan_t)-1:0] ),
`else
    .T         ( aw_chan_t                    ),
`endif
    .LOG_DEPTH ( LogDepth                     )
  ) i_cdc_fifo_gray_src_aw (
    .src_clk_i,
    .src_rst_ni,
    .src_data_i   ( src_req_i.aw                ),
    .src_valid_i  ( src_req_i.aw_valid          ),
    .src_ready_o  ( src_rsp_o.aw_ready          ),
    .async_data_o ( async_data_manager_aw_data_o ),
    .async_wptr_o ( async_data_manager_aw_wptr_o ),
    .async_rptr_i ( async_data_manager_aw_rptr_i )
  );

  cdc_fifo_gray_src #(
`ifdef QUESTA
    .T         ( logic [$bits(w_chan_t)-1:0]  ),
`else
    .T         ( w_chan_t                     ),
`endif
    .LOG_DEPTH ( LogDepth                     )
  ) i_cdc_fifo_gray_src_w (
    .src_clk_i,
    .src_rst_ni,
    .src_data_i   ( src_req_i.w                 ),
    .src_valid_i  ( src_req_i.w_valid           ),
    .src_ready_o  ( src_rsp_o.w_ready           ),
    .async_data_o ( async_data_manager_w_data_o  ),
    .async_wptr_o ( async_data_manager_w_wptr_o  ),
    .async_rptr_i ( async_data_manager_w_rptr_i  )
  );

  cdc_fifo_gray_dst #(
`ifdef QUESTA
    .T         ( logic [$bits(b_chan_t)-1:0]  ),
`else
    .T         ( b_chan_t                     ),
`endif
    .LOG_DEPTH ( LogDepth                     )
  ) i_cdc_fifo_gray_dst_b (
    .dst_clk_i    ( src_clk_i                   ),
    .dst_rst_ni   ( src_rst_ni                  ),
    .dst_data_o   ( src_rsp_o.b                 ),
    .dst_valid_o  ( src_rsp_o.b_valid           ),
    .dst_ready_i  ( src_req_i.b_ready           ),
    .async_data_i ( async_data_manager_b_data_i  ),
    .async_wptr_i ( async_data_manager_b_wptr_i  ),
    .async_rptr_o ( async_data_manager_b_rptr_o  )
  );

  cdc_fifo_gray_src #(
`ifdef QUESTA
    .T         ( logic [$bits(ar_chan_t)-1:0] ),
`else
    .T         ( ar_chan_t                    ),
`endif
    .LOG_DEPTH ( LogDepth                     )
  ) i_cdc_fifo_gray_src_ar (
    .src_clk_i,
    .src_rst_ni,
    .src_data_i   ( src_req_i.ar                ),
    .src_valid_i  ( src_req_i.ar_valid          ),
    .src_ready_o  ( src_rsp_o.ar_ready          ),
    .async_data_o ( async_data_manager_ar_data_o ),
    .async_wptr_o ( async_data_manager_ar_wptr_o ),
    .async_rptr_i ( async_data_manager_ar_rptr_i )
  );

  cdc_fifo_gray_dst #(
`ifdef QUESTA
    .T         ( logic [$bits(r_chan_t)-1:0]  ),
`else
    .T         ( r_chan_t                     ),
`endif
    .LOG_DEPTH ( LogDepth                     )
  ) i_cdc_fifo_gray_dst_r (
    .dst_clk_i    ( src_clk_i                   ),
    .dst_rst_ni   ( src_rst_ni                  ),
    .dst_data_o   ( src_rsp_o.r                 ),
    .dst_valid_o  ( src_rsp_o.r_valid           ),
    .dst_ready_i  ( src_req_i.r_ready           ),
    .async_data_i ( async_data_manager_r_data_i  ),
    .async_wptr_i ( async_data_manager_r_wptr_i  ),
    .async_rptr_o ( async_data_manager_r_rptr_o  )
  );

endmodule


module axi_cdc_src_intf #(
  parameter int unsigned AXI_ID_WIDTH = 0,
  parameter int unsigned AXI_ADDR_WIDTH = 0,
  parameter int unsigned AXI_DATA_WIDTH = 0,
  parameter int unsigned AXI_USER_WIDTH = 0,
  /// Depth of the FIFO crossing the clock domain, given as 2**LOG_DEPTH.
  parameter int unsigned LOG_DEPTH = 1
) (
  // synchronous subordinate port - clocked by `src_clk_i`
  input  logic                src_clk_i,
  input  logic                src_rst_ni,
  AXI_BUS.Subordinate               src,
  // asynchronous manager port
  AXI_BUS_ASYNC_GRAY.Manager   dst
);

  typedef logic [AXI_ID_WIDTH-1:0]     id_t;
  typedef logic [AXI_ADDR_WIDTH-1:0]   addr_t;
  typedef logic [AXI_DATA_WIDTH-1:0]   data_t;
  typedef logic [AXI_DATA_WIDTH/8-1:0] strb_t;
  typedef logic [AXI_USER_WIDTH-1:0]   user_t;
  `AXI_TYPEDEF_AW_CHAN_T(aw_chan_t, addr_t, id_t, user_t)
  `AXI_TYPEDEF_W_CHAN_T(w_chan_t, data_t, strb_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T(b_chan_t, id_t, user_t)
  `AXI_TYPEDEF_AR_CHAN_T(ar_chan_t, addr_t, id_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(r_chan_t, data_t, id_t, user_t)
  `AXI_TYPEDEF_REQ_T(axi_req_t, aw_chan_t, w_chan_t, ar_chan_t)
  `AXI_TYPEDEF_RSP_T(axi_rsp_t, b_chan_t, r_chan_t)

  axi_req_t src_req;
  axi_rsp_t src_rsp;

  `AXI_ASSIGN_TO_REQ(src_req, src)
  `AXI_ASSIGN_FROM_RSP(src, src_rsp)

  axi_cdc_src #(
    .aw_chan_t  ( aw_chan_t ),
    .w_chan_t   ( w_chan_t  ),
    .b_chan_t   ( b_chan_t  ),
    .ar_chan_t  ( ar_chan_t ),
    .r_chan_t   ( r_chan_t  ),
    .axi_req_t  ( axi_req_t ),
    .axi_rsp_t  ( axi_rsp_t ),
    .LogDepth   ( LOG_DEPTH )
  ) i_axi_cdc_src (
    .src_clk_i,
    .src_rst_ni,
    .src_req_i                    ( src_req     ),
    .src_rsp_o                    ( src_rsp     ),
    .async_data_manager_aw_data_o  ( dst.aw_data ),
    .async_data_manager_aw_wptr_o  ( dst.aw_wptr ),
    .async_data_manager_aw_rptr_i  ( dst.aw_rptr ),
    .async_data_manager_w_data_o   ( dst.w_data  ),
    .async_data_manager_w_wptr_o   ( dst.w_wptr  ),
    .async_data_manager_w_rptr_i   ( dst.w_rptr  ),
    .async_data_manager_b_data_i   ( dst.b_data  ),
    .async_data_manager_b_wptr_i   ( dst.b_wptr  ),
    .async_data_manager_b_rptr_o   ( dst.b_rptr  ),
    .async_data_manager_ar_data_o  ( dst.ar_data ),
    .async_data_manager_ar_wptr_o  ( dst.ar_wptr ),
    .async_data_manager_ar_rptr_i  ( dst.ar_rptr ),
    .async_data_manager_r_data_i   ( dst.r_data  ),
    .async_data_manager_r_wptr_i   ( dst.r_wptr  ),
    .async_data_manager_r_rptr_o   ( dst.r_rptr  )
  );

endmodule


module axi_lite_cdc_src_intf #(
  parameter int unsigned AXI_ADDR_WIDTH = 0,
  parameter int unsigned AXI_DATA_WIDTH = 0,
  /// Depth of the FIFO crossing the clock domain, given as 2**LOG_DEPTH.
  parameter int unsigned LOG_DEPTH = 1
) (
  // synchronous subordinate port - clocked by `src_clk_i`
  input  logic                src_clk_i,
  input  logic                src_rst_ni,
  AXI_BUS.Subordinate               src,
  // asynchronous manager port
  AXI_LITE_ASYNC_GRAY.Manager  dst
);

  typedef logic [AXI_ADDR_WIDTH-1:0]   addr_t;
  typedef logic [AXI_DATA_WIDTH-1:0]   data_t;
  typedef logic [AXI_DATA_WIDTH/8-1:0] strb_t;
  `AXI_LITE_TYPEDEF_AW_CHAN_T(aw_chan_t, addr_t)
  `AXI_LITE_TYPEDEF_W_CHAN_T(w_chan_t, data_t, strb_t)
  `AXI_LITE_TYPEDEF_B_CHAN_T(b_chan_t)
  `AXI_LITE_TYPEDEF_AR_CHAN_T(ar_chan_t, addr_t)
  `AXI_LITE_TYPEDEF_R_CHAN_T(r_chan_t, data_t)
  `AXI_LITE_TYPEDEF_REQ_T(axi_lite_req_t, aw_chan_t, w_chan_t, ar_chan_t)
  `AXI_LITE_TYPEDEF_RSP_T(axi_lite_rsp_t, b_chan_t, r_chan_t)

  axi_lite_req_t src_req;
  axi_lite_rsp_t src_rsp;

  `AXI_LITE_ASSIGN_TO_REQ(src_req, src)
  `AXI_LITE_ASSIGN_FROM_RSP(src, src_rsp)

  axi_cdc_src #(
    .aw_chan_t  ( aw_chan_t      ),
    .w_chan_t   ( w_chan_t       ),
    .b_chan_t   ( b_chan_t       ),
    .ar_chan_t  ( ar_chan_t      ),
    .r_chan_t   ( r_chan_t       ),
    .axi_req_t  ( axi_lite_req_t ),
    .axi_rsp_t  ( axi_lite_rsp_t ),
    .LogDepth   ( LOG_DEPTH      )
  ) i_axi_cdc_src (
    .src_clk_i,
    .src_rst_ni,
    .src_req_i                    ( src_req     ),
    .src_rsp_o                    ( src_rsp     ),
    .async_data_manager_aw_data_o  ( dst.aw_data ),
    .async_data_manager_aw_wptr_o  ( dst.aw_wptr ),
    .async_data_manager_aw_rptr_i  ( dst.aw_rptr ),
    .async_data_manager_w_data_o   ( dst.w_data  ),
    .async_data_manager_w_wptr_o   ( dst.w_wptr  ),
    .async_data_manager_w_rptr_i   ( dst.w_rptr  ),
    .async_data_manager_b_data_i   ( dst.b_data  ),
    .async_data_manager_b_wptr_i   ( dst.b_wptr  ),
    .async_data_manager_b_rptr_o   ( dst.b_rptr  ),
    .async_data_manager_ar_data_o  ( dst.ar_data ),
    .async_data_manager_ar_wptr_o  ( dst.ar_wptr ),
    .async_data_manager_ar_rptr_i  ( dst.ar_rptr ),
    .async_data_manager_r_data_i   ( dst.r_data  ),
    .async_data_manager_r_wptr_i   ( dst.r_wptr  ),
    .async_data_manager_r_rptr_o   ( dst.r_rptr  )
  );

endmodule
