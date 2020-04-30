// Copyright (c) 2014-2020 ETH Zurich, University of Bologna
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

/// Convert between two AXI ID widths.
///
/// Any combination of slave and master port ID width is valid.  When the master port ID width is
/// larger than or equal to the slave port ID width, slave port IDs are simply prepended with zeros
/// to the width of master port IDs.  For *reducing* the ID width, i.e., when the master port ID
/// width is smaller than the slave port ID width, there are two options.
///
/// ## Options for reducing the ID width
///
/// The two options for reducing ID widths differ in the maximum number of transactions that can be
/// in flight at the slave port of this module, given in the `AxiMaxUniqSlvPortIds` parameter.
///
/// ### Fewer unique slave port IDs than master port IDs
///
/// If `AxiMaxUniqSlvPortIds <= 2**AxiMstPortIdWidth`, there are fewer unique slave port IDs than
/// master port IDs.  Therefore, IDs that are different at the slave port of this module can remain
/// different at the reduced-ID-width master port and thus remain *independently reorderable*.
/// Since the IDs are master port are nonetheless shorter than at the slave port, they need to be
/// *remapped*.  An instance of [`axi_id_remap`](module.axi_id_remap) handles this case.
///
/// ### More unique slave port IDs than master port IDs
///
/// If `AxiMaxUniqSlvPortIds > 2**AxiMstPortIdWidth`, there are more unique slave port IDs than
/// master port IDs.  Therefore, some IDs that are different at the slave port need to be assigned
/// to the same master port ID and thus become ordered with respect to each other.  An instance of
/// [`axi_id_serializer`](module.axi_id_serializer) handles this case.
module axi_iw_converter #(
  /// Size of the remap table when downconverting the ID size.
  /// This number of ID's get generated at the master port.
  /// Maximum value is RemapTableSize <= 2**`AxiMstPortIdWidth` as then one table exists for
  /// every possible master port ID. The mapping is one to one.
  parameter int unsigned RemapTableSize = 32'd0,
  /// ID width of the AXI4+ATOP slave port
  parameter int unsigned AxiSlvPortIdWidth = 32'd0,
  /// ID width of the AXI4+ATOP master port
  parameter int unsigned AxiMstPortIdWidth = 32'd0,
  /// Address width of both AXI4+ATOP ports
  parameter int unsigned AxiAddrWidth = 32'd0,
  /// Data width of both AXI4+ATOP ports
  parameter int unsigned AxiDataWidth = 32'd0,
  /// User signal width of both AXI4+ATOP ports
  parameter int unsigned AxiUserWidth = 32'd0,
  /// Request struct type of the AXI4+ATOP slave port
  parameter type slv_req_t = logic,
  /// Response struct type of the AXI4+ATOP slave port
  parameter type slv_resp_t = logic,
  /// Request struct type of the AXI4+ATOP master port
  parameter type mst_req_t = logic,
  /// Response struct type of the AXI4+ATOP master port
  parameter type mst_resp_t = logic
) (
  /// Rising-edge clock of both ports
  input  logic      clk_i,
  /// Asynchronous reset, active low
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

  localparam int unsigned MaxMstIds = 2**AxiMstPortIdWidth;
  typedef logic [AxiAddrWidth-1:0]      addr_t;
  typedef logic [AxiDataWidth-1:0]      data_t;
  typedef logic [AxiIdWidthSlvPort-1:0] slv_id_t;
  typedef logic [AxiIdWidthMstPort-1:0] mst_id_t;
  typedef logic [AxiDataWidth/8-1:0]    strb_t;
  `AXI_TYPEDEF_AW_CHAN_T(slv_aw_t, addr_t, slv_id_t, user_t)
  `AXI_TYPEDEF_AW_CHAN_T(mst_aw_t, addr_t, mst_id_t, user_t)
  `AXI_TYPEDEF_W_CHAN_T(w_t, data_t, strb_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T(slv_b_t, slv_id_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T(mst_b_t, mst_id_t, user_t)
  `AXI_TYPEDEF_AR_CHAN_T(slv_ar_t, addr_t, slv_id_t, user_t)
  `AXI_TYPEDEF_AR_CHAN_T(mst_ar_t, addr_t, mst_id_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(slv_r_t, data_t, slv_id_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(mst_r_t, data_t, mst_id_t, user_t)

  if ((AxiSlvPortIdWidth > AxiMstPortIdWidth) && (RemapTableSize <= MaxMstIds)) begin : gen_id_downsize_table
    axi_id_remap #(
      .AxiSlvPortIdWidth    ( AxiSlvPortIdWidth ),
      .AxiMstPortIdWidth    ( AxiMstPortIdWidth ),
      .AxiMaxUniqSlvPortIds ( RemapTableSize    ),
      .AxiMaxTxnsPerId      ( RemapTableSize    ),
      .slv_req_t            ( slv_req_t         ),
      .slv_resp_t           ( slv_resp_t        ),
      .mst_req_t            ( mst_req_t         ),
      .mst_resp_t           ( mst_resp_t        )
    ) i_remap (
      .clk_i,
      .rst_ni,
      .slv_req_i  ( slv_req_i  ),
      .slv_resp_o ( slv_resp_o ),
      .mst_req_o  ( mst_req_o  ),
      .mst_resp_i ( mst_resp_i )
    );
  end else if (AxiSlvPortIdWidth > AxiMstPortIdWidth) begin : gen_id_downsize_serializer
    localparam int unsigned MaxTrans = cf_math_pkg::ceil_div(RemapTableSize, MaxMstIds);
    axi_iw_downsizer #(
      .NumIds        ( MaxMstIds          ),
      .MaxTrans      ( MaxTrans           ),
      .AxiAddrWidth  ( AxiAddrWidth       ),
      .AxiDataWidth  ( AxiDataWidth       ),
      .AxiUserWidth  ( AxiUserWidth       ),
      .AxiIdWidthSlv ( AxiSlvPortIdWidth  ),
      .slv_aw_chan_t ( slv_aw_t           ),
      .slv_w_chan_t  ( w_t                ),
      .slv_b_chan_t  ( slv_b_t            ),
      .slv_ar_chan_t ( slv_ar_t           ),
      .slv_r_chan_t  ( slv_r_t            ),
      .slv_req_t     ( slv_req_t          ),
      .slv_resp_t    ( slv_resp_t         ),
      .AxiIdWidthMst ( AxiMstPortIdWidth  ),
      .mst_aw_chan_t ( mst_aw_t           ),
      .mst_w_chan_t  ( w_t                ),
      .mst_b_chan_t  ( mst_b_t            ),
      .mst_ar_chan_t ( mst_ar_t           ),
      .mst_r_chan_t  ( mst_r_t            ),
      .mst_req_t     ( mst_req_t          ),
      .mst_resp_t    ( mst_resp_t         )
    ) i_axi_iw_downsizer (
      .clk_i,
      .rst_ni,
      .slv_req_i  ( slv_req_i  ),
      .slv_resp_o ( slv_resp_o ),
      .mst_req_o  ( mst_req_o  ),
      .mst_resp_i ( mst_resp_i )
    );
  end else if (AxiSlvPortIdWidth < AxiMstPortIdWidth) begin : gen_id_upsize
    axi_id_prepend #(
      .NoBus             ( 32'd1              ),
      .AxiIdWidthSlvPort ( AxiSlvPortIdWidth  ),
      .AxiIdWidthMstPort ( AxiMstPortIdWidth  ),
      .slv_aw_chan_t     ( slv_aw_t           ),
      .slv_w_chan_t      ( w_t                ),
      .slv_b_chan_t      ( slv_b_t            ),
      .slv_ar_chan_t     ( slv_ar_t           ),
      .slv_r_chan_t      ( slv_r_t            ),
      .mst_aw_chan_t     ( mst_aw_t           ),
      .mst_w_chan_t      ( w_t                ),
      .mst_b_chan_t      ( mst_b_t            ),
      .mst_ar_chan_t     ( mst_ar_t           ),
      .mst_r_chan_t      ( mst_r_t            )
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
    assert(AxiSlvPortIdWidth > 32'd0)
      else $fatal(1, "Parameter AxiSlvPortIdWidth has to be larger than 0!");
    assert(AxiMstPortIdWidth > 32'd0)
      else $fatal(1, "Parameter AxiMstPortIdWidth has to be larger than 0!");
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
/// Interface variant of [`axi_iw_converter`](module.axi_iw_converter).
///
/// See the documentation of the main module for the definition of ports and parameters.
module axi_iw_converter_intf #(
  parameter int unsigned REMAP_TABLE_SIZE = 32'd0,
  parameter int unsigned AXI_SLV_PORT_ID_WIDTH = 32'd0,
  parameter int unsigned AXI_MST_PORT_ID_WIDTH = 32'd0,
  parameter int unsigned AXI_ADDR_WIDTH = 32'd0,
  parameter int unsigned AXI_DATA_WIDTH = 32'd0,
  parameter int unsigned AXI_USER_WIDTH = 32'd0
) (
  input  logic   clk_i,
  input  logic   rst_ni,
  AXI_BUS.Slave  slv,
  AXI_BUS.Master mst
);
  typedef logic [AXI_SLV_PORT_ID_WIDTH-1:0] slv_id_t;
  typedef logic [AXI_MST_PORT_ID_WIDTH-1:0] mst_id_t;
  typedef logic [AXI_ADDR_WIDTH-1:0]        axi_addr_t;
  typedef logic [AXI_DATA_WIDTH-1:0]        axi_data_t;
  typedef logic [AXI_DATA_WIDTH/8-1:0]      axi_strb_t;
  typedef logic [AXI_USER_WIDTH-1:0]        axi_user_t;

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
    .RemapTableSize     ( REMAP_TABLE_SIZE      ),
    .AxiAddrWidth       ( AXI_ADDR_WIDTH        ),
    .AxiDataWidth       ( AXI_DATA_WIDTH        ),
    .AxiUserWidth       ( AXI_USER_WIDTH        ),
    .AxiSlvPortIdWidth  ( AXI_SLV_PORT_ID_WIDTH ),
    .slv_req_t          ( slv_req_t             ),
    .slv_resp_t         ( slv_resp_t            ),
    .AxiMstPortIdWidth  ( AXI_MST_PORT_ID_WIDTH ),
    .mst_req_t          ( mst_req_t             ),
    .mst_resp_t         ( mst_resp_t            )
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
      assert (slv.AXI_ID_WIDTH   == AXI_SLV_PORT_ID_WIDTH);
      assert (slv.AXI_ADDR_WIDTH == AXI_ADDR_WIDTH);
      assert (slv.AXI_DATA_WIDTH == AXI_DATA_WIDTH);
      assert (slv.AXI_USER_WIDTH == AXI_USER_WIDTH);
      assert (mst.AXI_ID_WIDTH   == AXI_MST_PORT_ID_WIDTH);
      assert (mst.AXI_ADDR_WIDTH == AXI_ADDR_WIDTH);
      assert (mst.AXI_DATA_WIDTH == AXI_DATA_WIDTH);
      assert (mst.AXI_USER_WIDTH == AXI_USER_WIDTH);
    end
  `endif
  // pragma translate_on
endmodule
