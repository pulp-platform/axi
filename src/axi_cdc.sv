// Copyright (c) 2019 ETH Zurich, University of Bologna
//
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

`include "axi/assign.svh"
import axi_pkg::*;

/// A clock domain crossing on an AXI interface.
///
/// For each of the five AXI channels, this module instantiates a CDC FIFO, whose push and pop
/// ports are in separate clock domains.  IMPORTANT: For each AXI channel, you MUST properly
/// constrain three paths through the FIFO; see the header of `cdc_fifo_gray` for instructions.
module axi_cdc #(
  parameter int unsigned  AW = 0,
  parameter int unsigned  DW = 0,
  parameter int unsigned  IW = 0,
  parameter int unsigned  UW = 0,
  /// Depth of the FIFO crossing the clock domain, given as 2**LOG_DEPTH.
  parameter int unsigned  LOG_DEPTH = 0
) (
  input  logic    clk_slv_i,
  input  logic    rst_slv_ni,
  AXI_BUS.Slave   slv,
  input  logic    clk_mst_i,
  input  logic    rst_mst_ni,
  AXI_BUS.Master  mst
);

  typedef logic [AW-1:0]    addr_t;
  typedef logic [DW-1:0]    data_t;
  typedef logic [IW-1:0]    id_t;
  typedef logic [DW/8-1:0]  strb_t;
  typedef logic [UW-1:0]    user_t;

  // AW Channel

  typedef struct packed {
    id_t     id;
    addr_t   addr;
    len_t    len;
    size_t   size;
    burst_t  burst;
    logic    lock;
    cache_t  cache;
    prot_t   prot;
    qos_t    qos;
    region_t region;
    atop_t   atop;
    user_t   user;
  } aw_chan_t;
  aw_chan_t slv_aw, mst_aw;

  `AXI_ASSIGN_TO_AW(slv_aw, slv);
  `AXI_ASSIGN_FROM_AW(mst, mst_aw);

  cdc_fifo_gray #(
    .T          (aw_chan_t),
    .LOG_DEPTH  (LOG_DEPTH)
  ) i_aw_cdc (
    .src_rst_ni   (rst_slv_ni),
    .src_clk_i    (clk_slv_i),
    .src_data_i   (slv_aw),
    .src_valid_i  (slv.aw_valid),
    .src_ready_o  (slv.aw_ready),

    .dst_rst_ni   (rst_mst_ni),
    .dst_clk_i    (clk_mst_i),
    .dst_data_o   (mst_aw),
    .dst_valid_o  (mst.aw_valid),
    .dst_ready_i  (mst.aw_ready)
  );

  // W Channel

  typedef struct packed {
    data_t data;
    strb_t strb;
    user_t user;
    logic  last;
  } w_chan_t;
  w_chan_t slv_w, mst_w;

  `AXI_ASSIGN_TO_W(slv_w, slv);
  `AXI_ASSIGN_FROM_W(mst, mst_w);

  cdc_fifo_gray #(
    .T          (w_chan_t),
    .LOG_DEPTH  (LOG_DEPTH)
  ) i_w_cdc (
    .src_rst_ni   (rst_slv_ni),
    .src_clk_i    (clk_slv_i),
    .src_data_i   (slv_w),
    .src_valid_i  (slv.w_valid),
    .src_ready_o  (slv.w_ready),

    .dst_rst_ni   (rst_mst_ni),
    .dst_clk_i    (clk_mst_i),
    .dst_data_o   (mst_w),
    .dst_valid_o  (mst.w_valid),
    .dst_ready_i  (mst.w_ready)
  );

  // B Channel

  typedef struct packed {
    id_t   id;
    resp_t resp;
    user_t user;
  } b_chan_t;
  b_chan_t slv_b, mst_b;

  `AXI_ASSIGN_TO_B(mst_b, mst);
  `AXI_ASSIGN_FROM_B(slv, slv_b);

  cdc_fifo_gray #(
    .T          (b_chan_t),
    .LOG_DEPTH  (LOG_DEPTH)
  ) i_b_cdc (
    .src_rst_ni   (rst_mst_ni),
    .src_clk_i    (clk_mst_i),
    .src_data_i   (mst_b),
    .src_valid_i  (mst.b_valid),
    .src_ready_o  (mst.b_ready),

    .dst_rst_ni   (rst_slv_ni),
    .dst_clk_i    (clk_slv_i),
    .dst_data_o   (slv_b),
    .dst_valid_o  (slv.b_valid),
    .dst_ready_i  (slv.b_ready)
  );

  // AR Channel

  typedef struct packed {
    id_t     id;
    addr_t   addr;
    len_t    len;
    size_t   size;
    burst_t  burst;
    logic    lock;
    cache_t  cache;
    prot_t   prot;
    qos_t    qos;
    region_t region;
    user_t   user;
  } ar_chan_t;
  ar_chan_t mst_ar, slv_ar;

  `AXI_ASSIGN_TO_AR(slv_ar, slv);
  `AXI_ASSIGN_FROM_AR(mst, mst_ar);

  cdc_fifo_gray #(
    .T          (ar_chan_t),
    .LOG_DEPTH  (LOG_DEPTH)
  ) i_ar_cdc (
    .src_rst_ni   (rst_slv_ni),
    .src_clk_i    (clk_slv_i),
    .src_data_i   (slv_ar),
    .src_valid_i  (slv.ar_valid),
    .src_ready_o  (slv.ar_ready),

    .dst_rst_ni   (rst_mst_ni),
    .dst_clk_i    (clk_mst_i),
    .dst_data_o   (mst_ar),
    .dst_valid_o  (mst.ar_valid),
    .dst_ready_i  (mst.ar_ready)
  );

  // R Channel

  typedef struct packed {
    id_t   id;
    data_t data;
    resp_t resp;
    user_t user;
    logic  last;
  } r_chan_t;
  r_chan_t mst_r, slv_r;

  `AXI_ASSIGN_TO_R(mst_r, mst);
  `AXI_ASSIGN_FROM_R(slv, slv_r);

  cdc_fifo_gray #(
    .T          (r_chan_t),
    .LOG_DEPTH  (LOG_DEPTH)
  ) i_r_cdc (
    .src_rst_ni   (rst_mst_ni),
    .src_clk_i    (clk_mst_i),
    .src_data_i   (mst_r),
    .src_valid_i  (mst.r_valid),
    .src_ready_o  (mst.r_ready),

    .dst_rst_ni   (rst_slv_ni),
    .dst_clk_i    (clk_slv_i),
    .dst_data_o   (slv_r),
    .dst_valid_o  (slv.r_valid),
    .dst_ready_i  (slv.r_ready)
  );

// pragma translate_off
`ifndef VERILATOR
  initial begin: p_assertions
    assert (AW > 0) else $fatal("AXI address width must be at least 1!");
    assert (DW > 0) else $fatal("AXI data width must be at least 1!");
    assert (IW > 0) else $fatal("AXI ID width must be at least 1!");
  end
`endif
// pragma translate_on

endmodule
