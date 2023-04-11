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
// - Andreas Kurth <akurth@iis.ee.ethz.ch>
// - Luca Valente <luca.valente@unibo.it>
// - Wolfgang Roenninger <wroennin@iis.ee.ethz.ch>

`include "axi/assign.svh"

/// A clock domain crossing on an AXI interface.
///
/// For each of the five AXI channels, this module instantiates a CDC FIFO, whose push and pop
/// ports are in separate clock domains.  IMPORTANT: For each AXI channel, you MUST properly
/// constrain three paths through the FIFO; see the header of `cdc_fifo_gray` for instructions.
module axi_cdc #(
  parameter type aw_chan_t = logic, // AW Channel Type
  parameter type w_chan_t  = logic, //  W Channel Type
  parameter type b_chan_t  = logic, //  B Channel Type
  parameter type ar_chan_t = logic, // AR Channel Type
  parameter type r_chan_t  = logic, //  R Channel Type
  parameter type axi_req_t = logic, // encapsulates request channels
  parameter type axi_rsp_t = logic, // encapsulates request channels
  /// Depth of the FIFO crossing the clock domain, given as 2**LOG_DEPTH.
  parameter int unsigned  LogDepth  = 1
) (
  // subordinate side - clocked by `src_clk_i`
  input  logic     src_clk_i,
  input  logic     src_rst_ni,
  input  axi_req_t src_req_i,
  output axi_rsp_t src_rsp_o,
  // manager side - clocked by `dst_clk_i`
  input  logic     dst_clk_i,
  input  logic     dst_rst_ni,
  output axi_req_t dst_req_o,
  input  axi_rsp_t dst_rsp_i
);

  aw_chan_t [2**LogDepth-1:0] async_data_aw_data;
  w_chan_t  [2**LogDepth-1:0] async_data_w_data;
  b_chan_t  [2**LogDepth-1:0] async_data_b_data;
  ar_chan_t [2**LogDepth-1:0] async_data_ar_data;
  r_chan_t  [2**LogDepth-1:0] async_data_r_data;
  logic          [LogDepth:0] async_data_aw_wptr, async_data_aw_rptr,
                              async_data_w_wptr,  async_data_w_rptr,
                              async_data_b_wptr,  async_data_b_rptr,
                              async_data_ar_wptr, async_data_ar_rptr,
                              async_data_r_wptr,  async_data_r_rptr;

  axi_cdc_src #(
    .aw_chan_t  ( aw_chan_t   ),
    .w_chan_t   ( w_chan_t    ),
    .b_chan_t   ( b_chan_t    ),
    .ar_chan_t  ( ar_chan_t   ),
    .r_chan_t   ( r_chan_t    ),
    .axi_req_t  ( axi_req_t   ),
    .axi_rsp_t  ( axi_rsp_t   ),
    .LogDepth   ( LogDepth    )
  ) i_axi_cdc_src (
                .src_clk_i,
                .src_rst_ni,
                .src_req_i,
                .src_rsp_o,
    (* async *) .async_data_manager_aw_data_o  ( async_data_aw_data  ),
    (* async *) .async_data_manager_aw_wptr_o  ( async_data_aw_wptr  ),
    (* async *) .async_data_manager_aw_rptr_i  ( async_data_aw_rptr  ),
    (* async *) .async_data_manager_w_data_o   ( async_data_w_data   ),
    (* async *) .async_data_manager_w_wptr_o   ( async_data_w_wptr   ),
    (* async *) .async_data_manager_w_rptr_i   ( async_data_w_rptr   ),
    (* async *) .async_data_manager_b_data_i   ( async_data_b_data   ),
    (* async *) .async_data_manager_b_wptr_i   ( async_data_b_wptr   ),
    (* async *) .async_data_manager_b_rptr_o   ( async_data_b_rptr   ),
    (* async *) .async_data_manager_ar_data_o  ( async_data_ar_data  ),
    (* async *) .async_data_manager_ar_wptr_o  ( async_data_ar_wptr  ),
    (* async *) .async_data_manager_ar_rptr_i  ( async_data_ar_rptr  ),
    (* async *) .async_data_manager_r_data_i   ( async_data_r_data   ),
    (* async *) .async_data_manager_r_wptr_i   ( async_data_r_wptr   ),
    (* async *) .async_data_manager_r_rptr_o   ( async_data_r_rptr   )
  );

  axi_cdc_dst #(
    .aw_chan_t  ( aw_chan_t   ),
    .w_chan_t   ( w_chan_t    ),
    .b_chan_t   ( b_chan_t    ),
    .ar_chan_t  ( ar_chan_t   ),
    .r_chan_t   ( r_chan_t    ),
    .axi_req_t  ( axi_req_t   ),
    .axi_rsp_t  ( axi_rsp_t   ),
    .LogDepth   ( LogDepth    )
  ) i_axi_cdc_dst (
                .dst_clk_i,
                .dst_rst_ni,
                .dst_req_o,
                .dst_rsp_i,
    (* async *) .async_data_subordinate_aw_wptr_i ( async_data_aw_wptr  ),
    (* async *) .async_data_subordinate_aw_rptr_o ( async_data_aw_rptr  ),
    (* async *) .async_data_subordinate_aw_data_i ( async_data_aw_data  ),
    (* async *) .async_data_subordinate_w_wptr_i  ( async_data_w_wptr   ),
    (* async *) .async_data_subordinate_w_rptr_o  ( async_data_w_rptr   ),
    (* async *) .async_data_subordinate_w_data_i  ( async_data_w_data   ),
    (* async *) .async_data_subordinate_b_wptr_o  ( async_data_b_wptr   ),
    (* async *) .async_data_subordinate_b_rptr_i  ( async_data_b_rptr   ),
    (* async *) .async_data_subordinate_b_data_o  ( async_data_b_data   ),
    (* async *) .async_data_subordinate_ar_wptr_i ( async_data_ar_wptr  ),
    (* async *) .async_data_subordinate_ar_rptr_o ( async_data_ar_rptr  ),
    (* async *) .async_data_subordinate_ar_data_i ( async_data_ar_data  ),
    (* async *) .async_data_subordinate_r_wptr_o  ( async_data_r_wptr   ),
    (* async *) .async_data_subordinate_r_rptr_i  ( async_data_r_rptr   ),
    (* async *) .async_data_subordinate_r_data_o  ( async_data_r_data   )
);

endmodule

`include "axi/assign.svh"
`include "axi/typedef.svh"

// interface wrapper
module axi_cdc_intf #(
  parameter int unsigned AXI_ID_WIDTH   = 0,
  parameter int unsigned AXI_ADDR_WIDTH = 0,
  parameter int unsigned AXI_DATA_WIDTH = 0,
  parameter int unsigned AXI_USER_WIDTH = 0,
  /// Depth of the FIFO crossing the clock domain, given as 2**LOG_DEPTH.
  parameter int unsigned LOG_DEPTH = 1
) (
   // subordinate side - clocked by `src_clk_i`
  input  logic      src_clk_i,
  input  logic      src_rst_ni,
  AXI_BUS.Subordinate     src,
  // manager side - clocked by `dst_clk_i`
  input  logic      dst_clk_i,
  input  logic      dst_rst_ni,
  AXI_BUS.Manager    dst
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

  axi_req_t src_req,  dst_req;
  axi_rsp_t src_rsp, dst_rsp;

  `AXI_ASSIGN_TO_REQ(src_req, src)
  `AXI_ASSIGN_FROM_RSP(src, src_rsp)

  `AXI_ASSIGN_FROM_REQ(dst, dst_req)
  `AXI_ASSIGN_TO_RSP(dst_rsp, dst)

  axi_cdc #(
    .aw_chan_t  ( aw_chan_t ),
    .w_chan_t   ( w_chan_t  ),
    .b_chan_t   ( b_chan_t  ),
    .ar_chan_t  ( ar_chan_t ),
    .r_chan_t   ( r_chan_t  ),
    .axi_req_t  ( axi_req_t ),
    .axi_rsp_t  ( axi_rsp_t ),
    .LogDepth   ( LOG_DEPTH )
  ) i_axi_cdc (
    .src_clk_i,
    .src_rst_ni,
    .src_req_i  ( src_req ),
    .src_rsp_o  ( src_rsp ),
    .dst_clk_i,
    .dst_rst_ni,
    .dst_req_o  ( dst_req ),
    .dst_rsp_i  ( dst_rsp )
  );

endmodule

module axi_lite_cdc_intf #(
  parameter int unsigned AXI_ADDR_WIDTH = 0,
  parameter int unsigned AXI_DATA_WIDTH = 0,
  /// Depth of the FIFO crossing the clock domain, given as 2**LOG_DEPTH.
  parameter int unsigned LOG_DEPTH = 1
) (
   // subordinate side - clocked by `src_clk_i`
  input  logic      src_clk_i,
  input  logic      src_rst_ni,
  AXI_LITE.Subordinate    src,
  // manager side - clocked by `dst_clk_i`
  input  logic      dst_clk_i,
  input  logic      dst_rst_ni,
  AXI_LITE.Manager   dst
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

  axi_lite_req_t src_req,  dst_req;
  axi_lite_rsp_t src_rsp, dst_rsp;

  `AXI_LITE_ASSIGN_TO_REQ(src_req, src)
  `AXI_LITE_ASSIGN_FROM_RSP(src, src_rsp)

  `AXI_LITE_ASSIGN_FROM_REQ(dst, dst_req)
  `AXI_LITE_ASSIGN_TO_RSP(dst_rsp, dst)

  axi_cdc #(
    .aw_chan_t  ( aw_chan_t      ),
    .w_chan_t   ( w_chan_t       ),
    .b_chan_t   ( b_chan_t       ),
    .ar_chan_t  ( ar_chan_t      ),
    .r_chan_t   ( r_chan_t       ),
    .axi_req_t  ( axi_lite_req_t ),
    .axi_rsp_t  ( axi_lite_rsp_t ),
    .LogDepth   ( LOG_DEPTH      )
  ) i_axi_cdc (
    .src_clk_i,
    .src_rst_ni,
    .src_req_i  ( src_req ),
    .src_rsp_o  ( src_rsp ),
    .dst_clk_i,
    .dst_rst_ni,
    .dst_req_o  ( dst_req ),
    .dst_rsp_i  ( dst_rsp )
  );

endmodule
