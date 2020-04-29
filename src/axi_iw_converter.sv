// Copyright (c) 2014-2019 ETH Zurich, University of Bologna
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
// Andreas Kurth <akurth@iis.ee.ethz.ch>
// Florian Zaruba <zarubaf@iis.ee.ethz.ch>
// Wolfgang Roenninger <wroennin@iis.ee.ethz.ch>

/// Change the AXI ID width.
///
/// This module instantiates a remapper if the outgoing ID is smaller than the incoming ID.
/// Feeds through the channel if the ID widths are the same and extends it with zeros, if
/// the outgoing ID is larger than the incoming ID.
module axi_iw_converter #(
  /// Size of the remap table when downconverting the ID size.
  /// This number of ID's get generated at the master port.
  /// Maximum value is RemapTableSize <= 2**`AxiIdWidthMst` as then one table exists for
  /// every possible master port ID. The mapping is one to one.
  parameter int unsigned RemapTableSize = 32'd0,
  /// AXI4+ATOP address width of both ports
  parameter int unsigned AxiAddrWidth   = 32'd0,
  /// AXI4+ATOP data width of both ports
  parameter int unsigned AxiDataWidth   = 32'd0,
  /// AXI4+ATOP user width of both ports
  parameter int unsigned AxiUserWidth   = 32'd0,
  /// AXI4+ATOP ID width of the slave port
  parameter int unsigned AxiIdWidthSlv  = 32'd0,
  /// AXI4+ATOP AW channel struct type of the slave port
  parameter type         slv_aw_chan_t  = logic,
  /// AXI4+ATOP W channel struct type of the slave port
  parameter type         slv_w_chan_t   = logic,
  /// AXI4+ATOP B channel struct type of the slave port
  parameter type         slv_b_chan_t   = logic,
  /// AXI4+ATOP AR channel struct type of the slave port
  parameter type         slv_ar_chan_t  = logic,
  /// AXI4+ATOP R channel struct type of the slave port
  parameter type         slv_r_chan_t   = logic,
  /// AXI4+ATOP request struct type of the slave port
  parameter type         slv_req_t      = logic,
  /// AXI4+ATOP response struct type of the slave port
  parameter type         slv_resp_t     = logic,
  /// AXI4+ATOP ID width of the master port
  parameter int unsigned AxiIdWidthMst  = 32'd0,
  /// AXI4+ATOP AW channel struct type of the master port
  parameter type         mst_aw_chan_t  = logic,
  /// AXI4+ATOP W channel struct type of the master port
  parameter type         mst_w_chan_t   = logic,
  /// AXI4+ATOP B channel struct type of the master port
  parameter type         mst_b_chan_t   = logic,
  /// AXI4+ATOP AR channel struct type of the master port
  parameter type         mst_ar_chan_t  = logic,
  /// AXI4+ATOP R channel struct type of the master port
  parameter type         mst_r_chan_t   = logic,
  /// AXI4+ATOP request struct type of the master port
  parameter type         mst_req_t      = logic,
  /// AXI4+ATOP response struct type of the master port
  parameter type         mst_resp_t     = logic
) (
  /// Clock Input
  input  logic      clk_i,
  /// Asynchronous reset active low
  input  logic      rst_ni,
  /// Slave port request
  input  slv_req_t  slv_req_i,
  /// Slave port response
  output slv_resp_t slv_resp_o,
  /// Master port request
  output mst_req_t  mst_req_o,
  /// Master port response
  input  mst_resp_t mst_resp_i
);

  localparam int unsigned MaxMstIds = 2**AxiIdWidthMst;

  if ((AxiIdWidthSlv > AxiIdWidthMst) && (RemapTableSize <= MaxMstIds)) begin : gen_id_downsize_table
    axi_id_remap #(
      .TableSize          ( RemapTableSize ),
      .AxiSlvPortIdWidth  ( AxiIdWidthSlv  ),
      .AxiMstPortIdWidth  ( AxiIdWidthMst  ),
      .slv_req_t          ( slv_req_t      ),
      .slv_resp_t         ( slv_resp_t     ),
      .mst_req_t          ( mst_req_t      ),
      .mst_resp_t         ( mst_resp_t     )
    ) i_remap (
      .clk_i,
      .rst_ni,
      .slv_req_i  ( slv_req_i  ),
      .slv_resp_o ( slv_resp_o ),
      .mst_req_o  ( mst_req_o  ),
      .mst_resp_i ( mst_resp_i )
    );
  end else if (AxiIdWidthSlv > AxiIdWidthMst) begin : gen_id_downsize_serializer
    localparam int unsigned MaxTrans = cf_math_pkg::ceil_div(RemapTableSize, MaxMstIds);
    axi_iw_downsizer #(
      .NumIds        ( MaxMstIds     ),
      .MaxTrans      ( MaxTrans      ),
      .AxiAddrWidth  ( AxiAddrWidth  ),
      .AxiDataWidth  ( AxiDataWidth  ),
      .AxiUserWidth  ( AxiUserWidth  ),
      .AxiIdWidthSlv ( AxiIdWidthSlv ),
      .slv_aw_chan_t ( slv_aw_chan_t ),
      .slv_w_chan_t  ( slv_w_chan_t  ),
      .slv_b_chan_t  ( slv_b_chan_t  ),
      .slv_ar_chan_t ( slv_ar_chan_t ),
      .slv_r_chan_t  ( slv_r_chan_t  ),
      .slv_req_t     ( slv_req_t     ),
      .slv_resp_t    ( slv_resp_t    ),
      .AxiIdWidthMst ( AxiIdWidthMst ),
      .mst_aw_chan_t ( mst_aw_chan_t ),
      .mst_w_chan_t  ( mst_w_chan_t  ),
      .mst_b_chan_t  ( mst_b_chan_t  ),
      .mst_ar_chan_t ( mst_ar_chan_t ),
      .mst_r_chan_t  ( mst_r_chan_t  ),
      .mst_req_t     ( mst_req_t     ),
      .mst_resp_t    ( mst_resp_t    )
    ) i_axi_iw_downsizer (
      .clk_i,
      .rst_ni,
      .slv_req_i  ( slv_req_i  ),
      .slv_resp_o ( slv_resp_o ),
      .mst_req_o  ( mst_req_o  ),
      .mst_resp_i ( mst_resp_i )
    );
  end else if (AxiIdWidthSlv < AxiIdWidthMst) begin : gen_id_upsize
    axi_id_prepend #(
      .NoBus             ( 32'd1         ),
      .AxiIdWidthSlvPort ( AxiIdWidthSlv ),
      .AxiIdWidthMstPort ( AxiIdWidthMst ),
      .slv_aw_chan_t     ( slv_aw_chan_t ),
      .slv_w_chan_t      ( slv_w_chan_t  ),
      .slv_b_chan_t      ( slv_b_chan_t  ),
      .slv_ar_chan_t     ( slv_ar_chan_t ),
      .slv_r_chan_t      ( slv_r_chan_t  ),
      .mst_aw_chan_t     ( mst_aw_chan_t ),
      .mst_w_chan_t      ( mst_w_chan_t  ),
      .mst_b_chan_t      ( mst_b_chan_t  ),
      .mst_ar_chan_t     ( mst_ar_chan_t ),
      .mst_r_chan_t      ( mst_r_chan_t  )
    ) i_axi_id_prepend (
      .pre_id_i         ( '0                  ),
      .slv_aw_chans_i   ( slv_req_i.aw        ),
      .slv_aw_valids_i  ( slv_req_i.aw_valid  ),
      .slv_aw_readies_o ( slv_resp_o.aw_ready ),
      .slv_w_chans_i    ( slv_req_i.w         ),
      .slv_w_valids_i   ( slv_req_i.w_valid   ),
      .slv_w_readies_o  ( slv_resp_o.w_ready  ),
      .slv_b_chans_o    ( slv_resp_o.b        ),
      .slv_b_valids_o   ( slv_resp_o.b_valid  ),
      .slv_b_readies_i  ( slv_req_i.b_ready   ),
      .slv_ar_chans_i   ( slv_req_i.ar        ),
      .slv_ar_valids_i  ( slv_req_i.ar_valid  ),
      .slv_ar_readies_o ( slv_resp_o.ar_ready ),
      .slv_r_chans_o    ( slv_resp_o.r        ),
      .slv_r_valids_o   ( slv_resp_o.r_valid  ),
      .slv_r_readies_i  ( slv_req_i.r_ready   ),
      .mst_aw_chans_o   ( mst_req_o.aw        ),
      .mst_aw_valids_o  ( mst_req_o.aw_valid  ),
      .mst_aw_readies_i ( mst_resp_i.aw_ready ),
      .mst_w_chans_o    ( mst_req_o.w         ),
      .mst_w_valids_o   ( mst_req_o.w_valid   ),
      .mst_w_readies_i  ( mst_resp_i.w_ready  ),
      .mst_b_chans_i    ( mst_resp_i.b        ),
      .mst_b_valids_i   ( mst_resp_i.b_valid  ),
      .mst_b_readies_o  ( mst_req_o.b_ready   ),
      .mst_ar_chans_o   ( mst_req_o.ar        ),
      .mst_ar_valids_o  ( mst_req_o.ar_valid  ),
      .mst_ar_readies_i ( mst_resp_i.ar_ready ),
      .mst_r_chans_i    ( mst_resp_i.r        ),
      .mst_r_valids_i   ( mst_resp_i.r_valid  ),
      .mst_r_readies_o  ( mst_req_o.r_ready   )
    );
  end else begin : gen_id_passthrough
    assign mst_req_o  = slv_req_i;
    assign slv_resp_o = mst_resp_i;
  end
  // pragma translate_off
  `ifndef VERILATOR
  initial begin : p_assert
    assert(AxiAddrWidth > 32'd0)
      else $fatal(1, "Parameter AxiAddrWidth has to be larger than 0!");
    assert(AxiDataWidth > 32'd0)
      else $fatal(1, "Parameter AxiDataWidth has to be larger than 0!");
    assert(AxiUserWidth > 32'd0)
      else $fatal(1, "Parameter AxiUserWidth has to be larger than 0!");
    assert(AxiIdWidthSlv > 32'd0)
      else $fatal(1, "Parameter AxiIdWidthSlv has to be larger than 0!");
    assert(AxiIdWidthMst > 32'd0)
      else $fatal(1, "Parameter AxiIdWidthMst has to be larger than 0!");
    assert($bits(slv_req_i.aw.addr) == $bits(mst_req_o.aw.addr))
      else $fatal(1, "AXI AW address widths are not equal!");
    assert($bits(slv_req_i.w.data) == $bits(mst_req_o.w.data))
      else $fatal(1, "AXI W data widths are not equal!");
    assert($bits(slv_req_i.ar.addr) == $bits(mst_req_o.ar.addr))
      else $fatal(1, "AXI AR address widths are not equal!");
    assert($bits(slv_resp_o.r.data) == $bits(mst_resp_i.r.data))
      else $fatal(1, "AXI R data widths are not equal!");
  end
  `endif
  // pragma translate_on
endmodule

`include "axi/typedef.svh"
`include "axi/assign.svh"
module axi_iw_converter_intf #(
  ///
  parameter int unsigned REMAP_TABLE_SIZE = 32'd0,
  /// AXI4+ATOP ID width of the slave port
  parameter int unsigned AXI_ID_WIDTH_SLV = 32'd0,
  /// AXI4+ATOP ID width of the master port
  parameter int unsigned AXI_ID_WIDTH_MST = 32'd0,
  /// AXI4+ATOP address width of both ports
  parameter int unsigned AXI_ADDR_WIDTH   = 32'd0,
  /// AXI4+ATOP data width of both ports
  parameter int unsigned AXI_DATA_WIDTH   = 32'd0,
  /// AXI4+ATOP user width of both ports
  parameter int unsigned AXI_USER_WIDTH   = 32'd0
) (
  /// Clock Input
  input  logic   clk_i,
  /// Asynchronous reset active low
  input  logic   rst_ni,
  /// Slave port
  AXI_BUS.Slave  slv,
  /// Master port
  AXI_BUS.Master mst
);
  typedef logic [AXI_ID_WIDTH_SLV-1:0] slv_id_t;
  typedef logic [AXI_ID_WIDTH_MST-1:0] mst_id_t;
  typedef logic [AXI_ADDR_WIDTH-1:0]   axi_addr_t;
  typedef logic [AXI_DATA_WIDTH-1:0]   axi_data_t;
  typedef logic [AXI_DATA_WIDTH/8-1:0] axi_strb_t;
  typedef logic [AXI_USER_WIDTH-1:0]   axi_user_t;

  `AXI_TYPEDEF_AW_CHAN_T(slv_aw_chan_t, axi_addr_t, slv_id_t, axi_user_t)
  `AXI_TYPEDEF_W_CHAN_T(slv_w_chan_t, axi_data_t, axi_strb_t, axi_user_t)
  `AXI_TYPEDEF_B_CHAN_T(slv_b_chan_t, slv_id_t, axi_user_t)
  `AXI_TYPEDEF_AR_CHAN_T(slv_ar_chan_t, axi_addr_t, slv_id_t, axi_user_t)
  `AXI_TYPEDEF_R_CHAN_T(slv_r_chan_t, axi_data_t, slv_id_t, axi_user_t)
  `AXI_TYPEDEF_REQ_T(slv_req_t, slv_aw_chan_t, slv_w_chan_t, slv_ar_chan_t)
  `AXI_TYPEDEF_RESP_T(slv_resp_t, slv_b_chan_t, slv_r_chan_t)

  `AXI_TYPEDEF_AW_CHAN_T(mst_aw_chan_t, axi_addr_t, mst_id_t, axi_user_t)
  `AXI_TYPEDEF_W_CHAN_T(mst_w_chan_t, axi_data_t, axi_strb_t, axi_user_t)
  `AXI_TYPEDEF_B_CHAN_T(mst_b_chan_t, mst_id_t, axi_user_t)
  `AXI_TYPEDEF_AR_CHAN_T(mst_ar_chan_t, axi_addr_t, mst_id_t, axi_user_t)
  `AXI_TYPEDEF_R_CHAN_T(mst_r_chan_t, axi_data_t, mst_id_t, axi_user_t)
  `AXI_TYPEDEF_REQ_T(mst_req_t, mst_aw_chan_t, mst_w_chan_t, mst_ar_chan_t)
  `AXI_TYPEDEF_RESP_T(mst_resp_t, mst_b_chan_t, mst_r_chan_t)

  slv_req_t  slv_req;
  slv_resp_t slv_resp;
  mst_req_t  mst_req;
  mst_resp_t mst_resp;

  `AXI_ASSIGN_TO_REQ(slv_req, slv)
  `AXI_ASSIGN_FROM_RESP(slv, slv_resp)
  `AXI_ASSIGN_FROM_REQ(mst, mst_req)
  `AXI_ASSIGN_TO_RESP(mst_resp, mst)

  axi_iw_converter #(
    .RemapTableSize ( REMAP_TABLE_SIZE ),
    .AxiAddrWidth   ( AXI_ADDR_WIDTH   ),
    .AxiDataWidth   ( AXI_DATA_WIDTH   ),
    .AxiUserWidth   ( AXI_USER_WIDTH   ),
    .AxiIdWidthSlv  ( AXI_ID_WIDTH_SLV ),
    .slv_aw_chan_t  ( slv_aw_chan_t    ),
    .slv_w_chan_t   ( slv_w_chan_t     ),
    .slv_b_chan_t   ( slv_b_chan_t     ),
    .slv_ar_chan_t  ( slv_ar_chan_t    ),
    .slv_r_chan_t   ( slv_r_chan_t     ),
    .slv_req_t      ( slv_req_t        ),
    .slv_resp_t     ( slv_resp_t       ),
    .AxiIdWidthMst  ( AXI_ID_WIDTH_MST ),
    .mst_aw_chan_t  ( mst_aw_chan_t    ),
    .mst_w_chan_t   ( mst_w_chan_t     ),
    .mst_b_chan_t   ( mst_b_chan_t     ),
    .mst_ar_chan_t  ( mst_ar_chan_t    ),
    .mst_r_chan_t   ( mst_r_chan_t     ),
    .mst_req_t      ( mst_req_t        ),
    .mst_resp_t     ( mst_resp_t       )
  ) i_axi_iw_converter (
    .clk_i,
    .rst_ni,
    .slv_req_i  ( slv_req  ),
    .slv_resp_o ( slv_resp ),
    .mst_req_o  ( mst_req  ),
    .mst_resp_i ( mst_resp )
  );
  // pragma translate_off
  `ifndef VERILATOR
    initial begin
      assert (slv.AXI_ID_WIDTH   == AXI_ID_WIDTH_SLV);
      assert (slv.AXI_ADDR_WIDTH == AXI_ADDR_WIDTH);
      assert (slv.AXI_DATA_WIDTH == AXI_DATA_WIDTH);
      assert (slv.AXI_USER_WIDTH == AXI_USER_WIDTH);
      assert (mst.AXI_ID_WIDTH   == AXI_ID_WIDTH_MST);
      assert (mst.AXI_ADDR_WIDTH == AXI_ADDR_WIDTH);
      assert (mst.AXI_DATA_WIDTH == AXI_DATA_WIDTH);
      assert (mst.AXI_USER_WIDTH == AXI_USER_WIDTH);
    end
  `endif
  // pragma translate_on
endmodule
