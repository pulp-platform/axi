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
// Authors:
// - Andreas Kurth <akurth@iis.ee.ethz.ch>
// - Wolfgang Roenninger <wroennin@iis.ee.ethz.ch>

`include "axi/typedef.svh"

/// Convert between any two AXI ID widths.
///
/// Any combination of slave and master port ID width is valid.  When the master port ID width is
/// larger than or equal to the slave port ID width, slave port IDs are simply prepended with zeros
/// to the width of master port IDs.  For *reducing* the ID width, i.e., when the master port ID
/// width is smaller than the slave port ID width, there are two options.
///
/// ## Options for reducing the ID width
///
/// The two options for reducing ID widths differ in the maximum number of different IDs that can be
/// in flight at the slave port of this module, given in the `SlvPortMaxUniqIds` parameter.
///
/// ### Fewer unique slave port IDs than master port IDs
///
/// If `SlvPortMaxUniqIds <= 2**MstPortIdWidth`, there are fewer unique slave port IDs than
/// master port IDs.  Therefore, IDs that are different at the slave port of this module can remain
/// different at the reduced-ID-width master port and thus remain *independently reorderable*.
/// Since the IDs are master port are nonetheless shorter than at the slave port, they need to be
/// *remapped*.  An instance of [`axi_id_remap`](module.axi_id_remap) handles this case.
///
/// ### More unique slave port IDs than master port IDs
///
/// If `SlvPortMaxUniqIds > 2**MstPortIdWidth`, there are more unique slave port IDs than
/// master port IDs.  Therefore, some IDs that are different at the slave port need to be assigned
/// to the same master port ID and thus become ordered with respect to each other.  An instance of
/// [`axi_id_serialize`](module.axi_id_serialize) handles this case.
module axi_iw_converter #(
  /// ID width of the AXI4+ATOP slave port
  parameter int unsigned SlvPortIdWidth = 32'd0,
  /// ID width of the AXI4+ATOP master port
  parameter int unsigned MstPortIdWidth = 32'd0,
  /// Maximum number of different IDs that can be in flight at the slave port.  Reads and writes are
  /// counted separately (except for ATOPs, which count as both read and write).
  ///
  /// It is legal for upstream to have transactions with more unique IDs than the maximum given by
  /// this parameter in flight, but a transaction exceeding the maximum will be stalled until all
  /// transactions of another ID complete.
  parameter int unsigned SlvPortMaxUniqIds = 32'd0,
  /// Maximum number of in-flight transactions with the same ID at the slave port.
  ///
  /// This parameter is only relevant if `SlvPortMaxUniqIds <= 2**MstPortIdWidth`.  In that
  /// case, this parameter is passed to [`axi_id_remap` as `MaxTxnsPerId`
  /// parameter](module.axi_id_remap#parameter.MaxTxnsPerId).
  parameter int unsigned SlvPortMaxTxnsPerId = 32'd0,
  /// Maximum number of in-flight transactions at the slave port.  Reads and writes are counted
  /// separately (except for ATOPs, which count as both read and write).
  ///
  /// This parameter is only relevant if `SlvPortMaxUniqIds > 2**MstPortIdWidth`.  In that
  /// case, this parameter is passed to
  /// [`axi_id_serialize`](module.axi_id_serialize#parameter.SlvPortMaxTxns).
  parameter int unsigned SlvPortMaxTxns = 32'd0,
  /// Maximum number of different IDs that can be in flight at the master port.  Reads and writes
  /// are counted separately (except for ATOPs, which count as both read and write).
  ///
  /// This parameter is only relevant if `SlvPortMaxUniqIds > 2**MstPortIdWidth`.  In that
  /// case, this parameter is passed to
  /// [`axi_id_serialize`](module.axi_id_serialize#parameter.MstPortMaxUniqIds).
  parameter int unsigned MstPortMaxUniqIds = 32'd0,
  /// Maximum number of in-flight transactions with the same ID at the master port.
  ///
  /// This parameter is only relevant if `SlvPortMaxUniqIds > 2**MstPortIdWidth`.  In that
  /// case, this parameter is passed to
  /// [`axi_id_serialize`](module.axi_id_serialize#parameter.MstPortMaxTxnsPerId).
  parameter int unsigned MstPortMaxTxnsPerId = 32'd0,
  /// Address width of both AXI4+ATOP ports
  parameter int unsigned AddrWidth = 32'd0,
  /// Data width of both AXI4+ATOP ports
  parameter int unsigned DataWidth = 32'd0,
  /// User signal width of both AXI4+ATOP ports
  parameter int unsigned UserWidth = 32'd0,
  /// Request struct type of the AXI4+ATOP slave port
  parameter type slv_port_axi_req_t = logic,
  /// Response struct type of the AXI4+ATOP slave port
  parameter type slv_port_axi_rsp_t = logic,
  /// Request struct type of the AXI4+ATOP master port
  parameter type mst_port_axi_req_t = logic,
  /// Response struct type of the AXI4+ATOP master port
  parameter type mst_port_axi_rsp_t = logic
) (
  /// Rising-edge clock of both ports
  input  logic              clk_i,
  /// Asynchronous reset, active low
  input  logic              rst_ni,
  /// Slave port request
  input  slv_port_axi_req_t slv_req_i,
  /// Slave port response
  output slv_port_axi_rsp_t slv_rsp_o,
  /// Master port request
  output mst_port_axi_req_t mst_req_o,
  /// Master port response
  input  mst_port_axi_rsp_t mst_rsp_i
);

  typedef logic [AddrWidth-1:0]      addr_t;
  typedef logic [DataWidth-1:0]      data_t;
  typedef logic [SlvPortIdWidth-1:0] slv_id_t;
  typedef logic [MstPortIdWidth-1:0] mst_id_t;
  typedef logic [DataWidth/8-1:0]    strb_t;
  typedef logic [UserWidth-1:0]      user_t;
  `AXI_TYPEDEF_AW_CHAN_T(slv_aw_t, addr_t, slv_id_t, user_t)
  `AXI_TYPEDEF_AW_CHAN_T(mst_aw_t, addr_t, mst_id_t, user_t)
  `AXI_TYPEDEF_W_CHAN_T(w_t, data_t, strb_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T(slv_b_t, slv_id_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T(mst_b_t, mst_id_t, user_t)
  `AXI_TYPEDEF_AR_CHAN_T(slv_ar_t, addr_t, slv_id_t, user_t)
  `AXI_TYPEDEF_AR_CHAN_T(mst_ar_t, addr_t, mst_id_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(slv_r_t, data_t, slv_id_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(mst_r_t, data_t, mst_id_t, user_t)

  if (MstPortIdWidth < SlvPortIdWidth) begin : gen_downsize
    if (SlvPortMaxUniqIds <= 2**MstPortIdWidth) begin : gen_remap
      axi_id_remap #(
        .SlvPortIdWidth     ( SlvPortIdWidth       ),
        .MstPortIdWidth     ( MstPortIdWidth       ),
        .SlvPortMaxUniqIds  ( SlvPortMaxUniqIds    ),
        .MaxTxnsPerId       ( SlvPortMaxTxnsPerId  ),
        .slv_port_axi_req_t ( slv_port_axi_req_t   ),
        .slv_port_axi_rsp_t ( slv_port_axi_rsp_t   ),
        .mst_port_axi_req_t ( mst_port_axi_req_t   ),
        .mst_port_axi_rsp_t ( mst_port_axi_rsp_t   )
      ) i_axi_id_remap (
        .clk_i,
        .rst_ni,
        .slv_req_i ( slv_req_i ),
        .slv_rsp_o ( slv_rsp_o ),
        .mst_req_o ( mst_req_o ),
        .mst_rsp_i ( mst_rsp_i )
      );
    end else begin : gen_serialize
      axi_id_serialize #(
        .SlvPortIdWidth      ( SlvPortIdWidth       ),
        .SlvPortMaxTxns      ( SlvPortMaxTxns       ),
        .MstPortIdWidth      ( MstPortIdWidth       ),
        .MstPortMaxUniqIds   ( MstPortMaxUniqIds    ),
        .MstPortMaxTxnsPerId ( MstPortMaxTxnsPerId  ),
        .AddrWidth           ( AddrWidth            ),
        .DataWidth           ( DataWidth            ),
        .UserWidth           ( UserWidth            ),
        .slv_port_axi_req_t  ( slv_port_axi_req_t   ),
        .slv_port_axi_rsp_t  ( slv_port_axi_rsp_t   ),
        .mst_port_axi_req_t  ( mst_port_axi_req_t   ),
        .mst_port_axi_rsp_t  ( mst_port_axi_rsp_t   )
      ) i_axi_id_serialize (
        .clk_i,
        .rst_ni,
        .slv_req_i ( slv_req_i ),
        .slv_rsp_o ( slv_rsp_o ),
        .mst_req_o ( mst_req_o ),
        .mst_rsp_i ( mst_rsp_i )
      );
      end
  end else if (MstPortIdWidth > SlvPortIdWidth) begin : gen_upsize
    axi_id_prepend #(
      .NoBus          ( 32'd1           ),
      .IdWidthSlvPort ( SlvPortIdWidth  ),
      .IdWidthMstPort ( MstPortIdWidth  ),
      .slv_aw_chan_t  ( slv_aw_t        ),
      .slv_w_chan_t   ( w_t             ),
      .slv_b_chan_t   ( slv_b_t         ),
      .slv_ar_chan_t  ( slv_ar_t        ),
      .slv_r_chan_t   ( slv_r_t         ),
      .mst_aw_chan_t  ( mst_aw_t        ),
      .mst_w_chan_t   ( w_t             ),
      .mst_b_chan_t   ( mst_b_t         ),
      .mst_ar_chan_t  ( mst_ar_t        ),
      .mst_r_chan_t   ( mst_r_t         )
    ) i_axi_id_prepend (
      .pre_id_i         ( '0                 ),
      .slv_aw_chans_i   ( slv_req_i.aw       ),
      .slv_aw_valids_i  ( slv_req_i.aw_valid ),
      .slv_aw_readies_o ( slv_rsp_o.aw_ready ),
      .slv_w_chans_i    ( slv_req_i.w        ),
      .slv_w_valids_i   ( slv_req_i.w_valid  ),
      .slv_w_readies_o  ( slv_rsp_o.w_ready  ),
      .slv_b_chans_o    ( slv_rsp_o.b        ),
      .slv_b_valids_o   ( slv_rsp_o.b_valid  ),
      .slv_b_readies_i  ( slv_req_i.b_ready  ),
      .slv_ar_chans_i   ( slv_req_i.ar       ),
      .slv_ar_valids_i  ( slv_req_i.ar_valid ),
      .slv_ar_readies_o ( slv_rsp_o.ar_ready ),
      .slv_r_chans_o    ( slv_rsp_o.r        ),
      .slv_r_valids_o   ( slv_rsp_o.r_valid  ),
      .slv_r_readies_i  ( slv_req_i.r_ready  ),
      .mst_aw_chans_o   ( mst_req_o.aw       ),
      .mst_aw_valids_o  ( mst_req_o.aw_valid ),
      .mst_aw_readies_i ( mst_rsp_i.aw_ready ),
      .mst_w_chans_o    ( mst_req_o.w        ),
      .mst_w_valids_o   ( mst_req_o.w_valid  ),
      .mst_w_readies_i  ( mst_rsp_i.w_ready  ),
      .mst_b_chans_i    ( mst_rsp_i.b        ),
      .mst_b_valids_i   ( mst_rsp_i.b_valid  ),
      .mst_b_readies_o  ( mst_req_o.b_ready  ),
      .mst_ar_chans_o   ( mst_req_o.ar       ),
      .mst_ar_valids_o  ( mst_req_o.ar_valid ),
      .mst_ar_readies_i ( mst_rsp_i.ar_ready ),
      .mst_r_chans_i    ( mst_rsp_i.r        ),
      .mst_r_valids_i   ( mst_rsp_i.r_valid  ),
      .mst_r_readies_o  ( mst_req_o.r_ready  )
    );
  end else begin : gen_passthrough
    assign mst_req_o = slv_req_i;
    assign slv_rsp_o = mst_rsp_i;
  end

  // pragma translate_off
  `ifndef VERILATOR
  initial begin : p_assert
    assert(AddrWidth > 32'd0)
      else $fatal(1, "Parameter AddrWidth has to be larger than 0!");
    assert(DataWidth > 32'd0)
      else $fatal(1, "Parameter DataWidth has to be larger than 0!");
    assert(UserWidth > 32'd0)
      else $fatal(1, "Parameter UserWidth has to be larger than 0!");
    assert(SlvPortIdWidth > 32'd0)
      else $fatal(1, "Parameter SlvPortIdWidth has to be larger than 0!");
    assert(MstPortIdWidth > 32'd0)
      else $fatal(1, "Parameter MstPortIdWidth has to be larger than 0!");
    if (SlvPortMaxUniqIds <= 2**MstPortIdWidth) begin
      assert(SlvPortMaxTxnsPerId > 32'd0)
        else $fatal(1, "Parameter SlvPortMaxTxnsPerId has to be larger than 0!");
    end else begin
      assert(MstPortMaxUniqIds > 32'd0)
        else $fatal(1, "Parameter MstPortMaxUniqIds has to be larger than 0!");
      assert(MstPortMaxTxnsPerId > 32'd0)
        else $fatal(1, "Parameter MstPortMaxTxnsPerId has to be larger than 0!");
    end
    assert($bits(slv_req_i.aw.addr) == $bits(mst_req_o.aw.addr))
      else $fatal(1, "AXI AW address widths are not equal!");
    assert($bits(slv_req_i.w.data) == $bits(mst_req_o.w.data))
      else $fatal(1, "AXI W data widths are not equal!");
    assert($bits(slv_req_i.ar.addr) == $bits(mst_req_o.ar.addr))
      else $fatal(1, "AXI AR address widths are not equal!");
    assert($bits(slv_rsp_o.r.data) == $bits(mst_rsp_i.r.data))
      else $fatal(1, "AXI R data widths are not equal!");
  end
  `endif
  // pragma translate_on
endmodule


`include "axi/assign.svh"

/// Interface variant of [`axi_iw_converter`](module.axi_iw_converter).
///
/// See the documentation of the main module for the definition of ports and parameters.
module axi_iw_converter_intf #(
  parameter int unsigned AXI_SLV_PORT_ID_WIDTH = 32'd0,
  parameter int unsigned AXI_MST_PORT_ID_WIDTH = 32'd0,
  parameter int unsigned AXI_SLV_PORT_MAX_UNIQ_IDS = 32'd0,
  parameter int unsigned AXI_SLV_PORT_MAX_TXNS_PER_ID = 32'd0,
  parameter int unsigned AXI_SLV_PORT_MAX_TXNS = 32'd0,
  parameter int unsigned AXI_MST_PORT_MAX_UNIQ_IDS = 32'd0,
  parameter int unsigned AXI_MST_PORT_MAX_TXNS_PER_ID = 32'd0,
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
  `AXI_TYPEDEF_REQ_T(slv_port_axi_req_t, slv_aw_chan_t, slv_w_chan_t, slv_ar_chan_t)
  `AXI_TYPEDEF_RSP_T(slv_port_axi_rsp_t, slv_b_chan_t, slv_r_chan_t)

  `AXI_TYPEDEF_AW_CHAN_T(mst_aw_chan_t, axi_addr_t, mst_id_t, axi_user_t)
  `AXI_TYPEDEF_W_CHAN_T(mst_w_chan_t, axi_data_t, axi_strb_t, axi_user_t)
  `AXI_TYPEDEF_B_CHAN_T(mst_b_chan_t, mst_id_t, axi_user_t)
  `AXI_TYPEDEF_AR_CHAN_T(mst_ar_chan_t, axi_addr_t, mst_id_t, axi_user_t)
  `AXI_TYPEDEF_R_CHAN_T(mst_r_chan_t, axi_data_t, mst_id_t, axi_user_t)
  `AXI_TYPEDEF_REQ_T(mst_port_axi_req_t, mst_aw_chan_t, mst_w_chan_t, mst_ar_chan_t)
  `AXI_TYPEDEF_RSP_T(mst_port_axi_rsp_t, mst_b_chan_t, mst_r_chan_t)

  slv_port_axi_req_t slv_req;
  slv_port_axi_rsp_t slv_rsp;
  mst_port_axi_req_t mst_req;
  mst_port_axi_rsp_t mst_rsp;

  `AXI_ASSIGN_TO_REQ(slv_req, slv)
  `AXI_ASSIGN_FROM_RSP(slv, slv_rsp)
  `AXI_ASSIGN_FROM_REQ(mst, mst_req)
  `AXI_ASSIGN_TO_RSP(mst_rsp, mst)

  axi_iw_converter #(
    .SlvPortIdWidth      ( AXI_SLV_PORT_ID_WIDTH         ),
    .MstPortIdWidth      ( AXI_MST_PORT_ID_WIDTH         ),
    .SlvPortMaxUniqIds   ( AXI_SLV_PORT_MAX_UNIQ_IDS     ),
    .SlvPortMaxTxnsPerId ( AXI_SLV_PORT_MAX_TXNS_PER_ID  ),
    .SlvPortMaxTxns      ( AXI_SLV_PORT_MAX_TXNS         ),
    .MstPortMaxUniqIds   ( AXI_MST_PORT_MAX_UNIQ_IDS     ),
    .MstPortMaxTxnsPerId ( AXI_MST_PORT_MAX_TXNS_PER_ID  ),
    .AddrWidth           ( AXI_ADDR_WIDTH                ),
    .DataWidth           ( AXI_DATA_WIDTH                ),
    .UserWidth           ( AXI_USER_WIDTH                ),
    .slv_port_axi_req_t  ( slv_port_axi_req_t            ),
    .slv_port_axi_rsp_t  ( slv_port_axi_rsp_t            ),
    .mst_port_axi_req_t  ( mst_port_axi_req_t            ),
    .mst_port_axi_rsp_t  ( mst_port_axi_rsp_t            )
  ) i_axi_iw_converter (
    .clk_i,
    .rst_ni,
    .slv_req_i ( slv_req ),
    .slv_rsp_o ( slv_rsp ),
    .mst_req_o ( mst_req ),
    .mst_rsp_i ( mst_rsp )
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
