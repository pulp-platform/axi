// Copyright (c) 2014-2018 ETH Zurich, University of Bologna
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
// Fabian Schuiki <fschuiki@iis.ee.ethz.ch>
// Andreas Kurth  <akurth@iis.ee.ethz.ch>

/// An AXI4 to AXI4-Lite adapter.
///
/// Two internal FIFOs are used to perform ID reflection. The length of these
/// FIFOs determines the maximum number of outstanding transactions on the read
/// and write channels that the adapter can handle.
///
/// Burst accesses are not yet supported and DO NOT produce an error.
module axi_to_axi_lite #(
  parameter int unsigned AxiIdWidth = 0,
  parameter int unsigned AxiUserWidth = 0,
  parameter int unsigned UserWidth = 0,
  // Maximum number of outstanding reads.
  parameter int unsigned NumPendingRd = 0,
  // Maximum number of outstanding writes.
  parameter int unsigned NumPendingWr = 0,
  // AXI structs
  parameter type       req_t = logic,
  parameter type      resp_t = logic,
  // AXI-Lite structs
  parameter type  req_lite_t = logic,
  parameter type resp_lite_t = logic
) (
  input  logic        clk_i,
  input  logic        rst_ni,
  input  logic        testmode_i,
  // Slave AXI port
  input  req_t        slv_req_i,
  output resp_t       slv_resp_o,
  // Master AXI-Lite port
  output req_lite_t   mst_req_o,
  input  resp_lite_t  mst_resp_i
);

  typedef logic   [AxiIdWidth-1:0]   id_t;
  typedef logic [AxiUserWidth-1:0] user_t;

  // The transaction information that will be stored locally.
  typedef struct packed {
    id_t    id;
    user_t  user;
  } meta_t;

  // HACK: Rather than passing a meta_rd_t and meta_wr_t into the FIFO's data_o
  //       port, we destructure it into the constituent fields. If we don't do
  //       this, Synopsys DC 2016.03 throws an "Internal Error" on "meta_rd.id".
  id_t    meta_rd_id,
          meta_wr_id;
  user_t  meta_rd_user,
          meta_wr_user;

  // The two FIFOs which hold the transaction information.
  logic   rd_full,
          wr_full;
  meta_t  meta_rd,
          meta_wr;

  fifo #(.dtype(meta_t), .DEPTH(NumPendingRd)) i_fifo_rd (
    .clk_i       ( clk_i      ),
    .rst_ni      ( rst_ni     ),
    .testmode_i  ( testmode_i ),
    .flush_i     ( '0         ),
    .full_o      ( rd_full    ),
    .empty_o     (            ),
    .threshold_o (            ),
    // For every transaction on the AR channel we push the ID and USER metadata
    // into the queue.
    .data_i  ( {slv_req_i.ar.id, slv_req_i.ar.user}     ),
    .push_i  ( slv_resp_o.ar_ready & slv_req_i.ar_valid ),
    // After the last response on the R channel we pop the metadata off the
    // queue.
    .data_o  ( {meta_rd_id, meta_rd_user}                                 ),
    .pop_i   ( slv_resp_o.r_valid & slv_req_i.r_ready & slv_resp_o.r.last )
  );

  fifo #(.dtype(meta_t), .DEPTH(NumPendingWr)) i_fifo_wr (
    .clk_i        ( clk_i      ),
    .rst_ni       ( rst_ni     ),
    .testmode_i   ( testmode_i ),
    .flush_i      ( '0         ),
    .full_o       ( wr_full    ),
    .empty_o      (            ),
    .threshold_o  (            ),
    // For every transaction on the AW channel we push the ID and USER metadata
    // into the queue.
    .data_i  ( {slv_req_i.aw.id, slv_req_i.aw.user}     ),
    .push_i  ( slv_resp_o.aw_ready & slv_req_i.aw_valid ),
    // After the response on the B channel we pop the metadata off the queue.
    .data_o  ( {meta_wr_id, meta_wr_user}               ),
    .pop_i   ( slv_resp_o.b_valid & slv_req_i.b_ready   )
  );

  // Accept transactions on the AW and AR channels if the corresponding FIFO is
  // not full.
  assign mst_req_o.aw = '{
    addr:     slv_req_i.aw.addr,
    prot:     slv_req_i.aw.prot,
    default:  '0
  };
  assign mst_req_o.aw_valid = ~wr_full & slv_req_i.aw_valid;
  assign slv_resp_o.aw_ready = ~wr_full & mst_resp_i.aw_ready;
  assign mst_req_o.ar = '{
    addr:     slv_req_i.ar.addr,
    prot:     slv_req_i.ar.prot,
    default:  '0
  };
  assign mst_req_o.ar_valid = ~rd_full & slv_req_i.ar_valid;
  assign slv_resp_o.ar_ready = ~rd_full & mst_resp_i.ar_ready;

  assign mst_req_o.w = '{
    data:     slv_req_i.w.data,
    strb:     slv_req_i.w.strb,
    default:  '0
  };
  assign mst_req_o.w_valid = slv_req_i.w_valid;
  assign slv_resp_o.w_ready = mst_resp_i.w_ready;

  // Inject the metadata again on the B and R return paths.
  assign slv_resp_o.b = '{
    id:       meta_wr_id,
    resp:     mst_resp_i.b.resp,
    user:     meta_wr_user,
    default:  '0
  };
  assign slv_resp_o.b_valid = mst_resp_i.b_valid;
  assign mst_req_o.b_ready = slv_req_i.b_ready;
  assign slv_resp_o.r = '{
    id:       meta_rd_id,
    data:     mst_resp_i.r.data,
    resp:     mst_resp_i.r.resp,
    last:     1'b1,
    user:     meta_rd_user,
    default:  '0
  };
  assign slv_resp_o.r_valid = mst_resp_i.r_valid;
  assign mst_req_o.r_ready = slv_req_i.r_ready;

// pragma translate_off
`ifndef VERILATOR
  initial begin
    assert(NumPendingRd > 0) else $fatal(1, "Number of pending reads must be greater than 0!");
    assert(NumPendingWr > 0) else $fatal(1, "Number of pending writes must be greater than 0!");
  end
`endif
// pragma translate_on

endmodule

`include "axi/assign.svh"
`include "axi/typedef.svh"

module axi_to_axi_lite_intf #(
  parameter int unsigned AXI_ADDR_WIDTH = 0,
  parameter int unsigned AXI_DATA_WIDTH = 0,
  parameter int unsigned AXI_ID_WIDTH = 0,
  parameter int unsigned AXI_USER_WIDTH = 0,
  parameter int unsigned NUM_PENDING_RD = 0,
  parameter int unsigned NUM_PENDING_WR = 0
) (
  input  logic    clk_i,
  input  logic    rst_ni,
  input  logic    testmode_i,
  AXI_BUS.Slave   in,
  AXI_LITE.Master out
);

  typedef logic [AXI_ADDR_WIDTH-1:0]   addr_t;
  typedef logic [AXI_DATA_WIDTH-1:0]   data_t;
  typedef logic [AXI_ID_WIDTH-1:0]     id_t;
  typedef logic [AXI_DATA_WIDTH/8-1:0] strb_t;
  typedef logic [AXI_USER_WIDTH-1:0]   user_t;

  `AXI_TYPEDEF_AW_CHAN_T      (aw_t,        addr_t, id_t,         user_t)
  `AXI_TYPEDEF_W_CHAN_T       (w_t,         data_t,       strb_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T       (b_t,         id_t,         user_t)
  `AXI_TYPEDEF_AR_CHAN_T      (ar_t,        addr_t, id_t,         user_t)
  `AXI_TYPEDEF_R_CHAN_T       (r_t,         data_t, id_t,         user_t)
  `AXI_TYPEDEF_REQ_T          (req_t,       aw_t, w_t, ar_t)
  `AXI_TYPEDEF_RESP_T         (resp_t,      b_t, r_t)
  `AXI_LITE_TYPEDEF_AW_CHAN_T (lite_aw_t,   addr_t)
  `AXI_LITE_TYPEDEF_W_CHAN_T  (lite_w_t,    data_t, strb_t)
  `AXI_LITE_TYPEDEF_B_CHAN_T  (lite_b_t)
  `AXI_LITE_TYPEDEF_AR_CHAN_T (lite_ar_t,   addr_t)
  `AXI_LITE_TYPEDEF_R_CHAN_T  (lite_r_t,    data_t)
  `AXI_LITE_TYPEDEF_REQ_T     (lite_req_t,  lite_aw_t, lite_w_t, lite_ar_t)
  `AXI_LITE_TYPEDEF_RESP_T    (lite_resp_t, lite_b_t, lite_r_t)

  req_t       slv_req;
  lite_req_t  mst_req;
  resp_t      slv_resp;
  lite_resp_t mst_resp;

  `AXI_ASSIGN_TO_REQ        ( slv_req , in       )
  `AXI_ASSIGN_FROM_RESP     ( in      , slv_resp )

  `AXI_LITE_ASSIGN_FROM_REQ ( out     , mst_req  )
  `AXI_LITE_ASSIGN_TO_RESP  ( mst_resp, out      )

  axi_to_axi_lite #(
    .AxiIdWidth   (AXI_ID_WIDTH),
    .AxiUserWidth (AXI_USER_WIDTH),
    .NumPendingRd (NUM_PENDING_RD),
    .NumPendingWr (NUM_PENDING_WR),
    .req_t        (req_t),
    .resp_t       (resp_t),
    .req_lite_t   (lite_req_t),
    .resp_lite_t  (lite_resp_t)
  ) i_axi_to_axi_lite (
    .clk_i,
    .rst_ni,
    .testmode_i,
    .slv_req_i    ( slv_req  ),
    .slv_resp_o   ( slv_resp ),
    .mst_req_o    ( mst_req  ),
    .mst_resp_i   ( mst_resp )
  );

// pragma translate_off
`ifndef VERILATOR
  initial begin: p_assertions
    assert (AXI_ADDR_WIDTH >= 1) else $fatal(1, "AXI ADDR width must be at least 1!");
    assert (AXI_DATA_WIDTH >= 1) else $fatal(1, "AXI DATA width must be at least 1!");
    assert (AXI_ID_WIDTH   >= 1) else $fatal(1, "AXI ID width must be at least 1!");
    assert (AXI_USER_WIDTH >= 1) else $fatal(1, "AXI USER width must be at least 1!");
  end
`endif
// pragma translate_on

endmodule
