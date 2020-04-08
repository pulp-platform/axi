// Copyright (c) 2020 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Author: Andreas Kurth <akurth@iis.ee.ethz.ch>

`include "axi/assign.svh"

/// Serialize all AXI transactions to a single ID (zero).
module axi_serializer #(
  parameter int unsigned MaxReadTxns = 0,
  parameter int unsigned MaxWriteTxns = 0,
  parameter int unsigned AxiIdWidth = 0,
  parameter type req_t = logic,
  parameter type resp_t = logic
) (
  input  logic  clk_i,
  input  logic  rst_ni,
  input  req_t  slv_req_i,
  output resp_t slv_resp_o,
  output req_t  mst_req_o,
  input  resp_t mst_resp_i
);

  // TODO for upstreaming: Add support for ATOPs.

  typedef logic [AxiIdWidth-1:0] id_t;

  logic rd_fifo_ready,  rd_fifo_valid,
        wr_fifo_ready,  wr_fifo_valid;
  id_t  b_id,
        r_id;

  always_comb begin
    mst_req_o   = slv_req_i;
    slv_resp_o  = mst_resp_i;

    // Serialize transactions -> tie downstream IDs to zero.
    mst_req_o.aw.id = '0;
    mst_req_o.ar.id = '0;

    // Reflect upstream ID in response.
    slv_resp_o.b.id = b_id;
    slv_resp_o.r.id = r_id;

    // Gate AW handshake with ready output of Write FIFO.
    mst_req_o.aw_valid = slv_req_i.aw_valid & wr_fifo_ready;
    slv_resp_o.aw_ready = mst_resp_i.aw_ready & wr_fifo_ready;

    // Gate B handshake with valid output of Write FIFO.
    slv_resp_o.b_valid = mst_resp_i.b_valid & wr_fifo_valid;
    mst_req_o.b_ready = slv_req_i.b_ready & wr_fifo_valid;

    // Gate AR handshake with ready output of Read FIFO.
    mst_req_o.ar_valid = slv_req_i.ar_valid & rd_fifo_ready;
    slv_resp_o.ar_ready = mst_resp_i.ar_ready & rd_fifo_ready;

    // Gate R handshake with valid output of Read FIFO.
    slv_resp_o.r_valid = mst_resp_i.r_valid & rd_fifo_valid;
    mst_req_o.r_ready = slv_req_i.r_ready & rd_fifo_valid;
  end

  stream_fifo #(
    .FALL_THROUGH (1'b1),
    .DEPTH        (MaxReadTxns),
    .T            (id_t)
  ) i_rd_id_fifo (
    .clk_i,
    .rst_ni,
    .flush_i    (1'b0),
    .testmode_i (1'b0),
    .data_i     (slv_req_i.ar.id),
    .valid_i    (slv_req_i.ar_valid & slv_resp_o.ar_ready),
    .ready_o    (rd_fifo_ready),
    .data_o     (r_id),
    .valid_o    (rd_fifo_valid),
    .ready_i    (slv_resp_o.r_valid & slv_req_i.r_ready & slv_resp_o.r.last),
    .usage_o    (/* unused */)
  );

  stream_fifo #(
    .FALL_THROUGH (1'b1),
    .DEPTH        (MaxWriteTxns),
    .T            (id_t)
  ) i_wr_id_fifo (
    .clk_i,
    .rst_ni,
    .flush_i    (1'b0),
    .testmode_i (1'b0),
    .data_i     (slv_req_i.aw.id),
    .valid_i    (slv_req_i.aw_valid & slv_resp_o.aw_ready),
    .ready_o    (wr_fifo_ready),
    .data_o     (b_id),
    .valid_o    (wr_fifo_valid),
    .ready_i    (slv_resp_o.b_valid & slv_req_i.b_ready),
    .usage_o    (/* unused */)
  );

endmodule

`include "axi/typedef.svh"

module axi_serializer_intf #(
  parameter int unsigned AXI_ADDR_WIDTH = 0,
  parameter int unsigned AXI_DATA_WIDTH = 0,
  parameter int unsigned AXI_ID_WIDTH = 0,
  parameter int unsigned AXI_USER_WIDTH = 0,
  parameter int unsigned MAX_READ_TXNS = 0,
  parameter int unsigned MAX_WRITE_TXNS = 0
) (
  input  logic    clk_i,
  input  logic    rst_ni,
  AXI_BUS.Slave   slv,
  AXI_BUS.Master  mst
);

  typedef logic [AXI_ADDR_WIDTH  -1:0] addr_t;
  typedef logic [AXI_DATA_WIDTH  -1:0] data_t;
  typedef logic [AXI_DATA_WIDTH/8-1:0] strb_t;
  typedef logic [AXI_ID_WIDTH    -1:0] id_t;
  typedef logic [AXI_USER_WIDTH  -1:0] user_t;
  `AXI_TYPEDEF_AW_CHAN_T(aw_chan_t, addr_t, id_t, user_t)
  `AXI_TYPEDEF_W_CHAN_T(w_chan_t, data_t, strb_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T(b_chan_t, id_t, user_t)
  `AXI_TYPEDEF_AR_CHAN_T(ar_chan_t, addr_t, id_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(r_chan_t, data_t, id_t, user_t)
  `AXI_TYPEDEF_REQ_T(req_t, aw_chan_t, w_chan_t, ar_chan_t)
  `AXI_TYPEDEF_RESP_T(resp_t, b_chan_t, r_chan_t)
  req_t  slv_req,  mst_req;
  resp_t slv_resp, mst_resp;
  `AXI_ASSIGN_TO_REQ(slv_req, slv)
  `AXI_ASSIGN_FROM_RESP(slv, slv_resp)
  `AXI_ASSIGN_FROM_REQ(mst, mst_req)
  `AXI_ASSIGN_TO_RESP(mst_resp, mst)

  axi_serializer #(
    .MaxReadTxns  (MAX_READ_TXNS),
    .MaxWriteTxns (MAX_WRITE_TXNS),
    .AxiIdWidth   (AXI_ID_WIDTH),
    .req_t        (req_t),
    .resp_t       (resp_t)
  ) i_axi_serializer (
    .clk_i,
    .rst_ni,
    .slv_req_i  (slv_req),
    .slv_resp_o (slv_resp),
    .mst_req_o  (mst_req),
    .mst_resp_i (mst_resp)
  );

// pragma translate_off
`ifndef VERILATOR
  initial begin: p_assertions
    assert (AXI_ADDR_WIDTH  >= 1) else $fatal(1, "AXI address width must be at least 1!");
    assert (AXI_DATA_WIDTH  >= 1) else $fatal(1, "AXI data width must be at least 1!");
    assert (AXI_ID_WIDTH    >= 1) else $fatal(1, "AXI ID   width must be at least 1!");
    assert (AXI_USER_WIDTH  >= 1) else $fatal(1, "AXI user width must be at least 1!");
    assert (MAX_READ_TXNS   >= 1)
      else $fatal(1, "Maximum number of read transactions must be >= 1!");
    assert (MAX_WRITE_TXNS  >= 1)
      else $fatal(1, "Maximum number of write transactions must be >= 1!");
  end
`endif
// pragma translate_on

endmodule
