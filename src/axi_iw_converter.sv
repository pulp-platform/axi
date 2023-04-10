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
/// Any combination of subordinate and manager port ID width is valid.  When the manager port ID width is
/// larger than or equal to the subordinate port ID width, subordinate port IDs are simply prepended with zeros
/// to the width of manager port IDs.  For *reducing* the ID width, i.e., when the manager port ID
/// width is smaller than the subordinate port ID width, there are two options.
///
/// ## Options for reducing the ID width
///
/// The two options for reducing ID widths differ in the maximum number of different IDs that can be
/// in flight at the subordinate port of this module, given in the `SbrPortMaxUniqIds` parameter.
///
/// ### Fewer unique subordinate port IDs than manager port IDs
///
/// If `SbrPortMaxUniqIds <= 2**MgrPortIdWidth`, there are fewer unique subordinate port IDs than
/// manager port IDs.  Therefore, IDs that are different at the subordinate port of this module can remain
/// different at the reduced-ID-width manager port and thus remain *independently reorderable*.
/// Since the IDs are manager port are nonetheless shorter than at the subordinate port, they need to be
/// *remapped*.  An instance of [`axi_id_remap`](module.axi_id_remap) handles this case.
///
/// ### More unique subordinate port IDs than manager port IDs
///
/// If `SbrPortMaxUniqIds > 2**MgrPortIdWidth`, there are more unique subordinate port IDs than
/// manager port IDs.  Therefore, some IDs that are different at the subordinate port need to be assigned
/// to the same manager port ID and thus become ordered with respect to each other.  An instance of
/// [`axi_id_serialize`](module.axi_id_serialize) handles this case.
module axi_iw_converter #(
  /// ID width of the AXI4+ATOP subordinate port
  parameter int unsigned SbrPortIdWidth = 32'd0,
  /// ID width of the AXI4+ATOP manager port
  parameter int unsigned MgrPortIdWidth = 32'd0,
  /// Maximum number of different IDs that can be in flight at the subordinate port.  Reads and writes are
  /// counted separately (except for ATOPs, which count as both read and write).
  ///
  /// It is legal for upstream to have transactions with more unique IDs than the maximum given by
  /// this parameter in flight, but a transaction exceeding the maximum will be stalled until all
  /// transactions of another ID complete.
  parameter int unsigned SbrPortMaxUniqIds = 32'd0,
  /// Maximum number of in-flight transactions with the same ID at the subordinate port.
  ///
  /// This parameter is only relevant if `SbrPortMaxUniqIds <= 2**MgrPortIdWidth`.  In that
  /// case, this parameter is passed to [`axi_id_remap` as `MaxTxnsPerId`
  /// parameter](module.axi_id_remap#parameter.MaxTxnsPerId).
  parameter int unsigned SbrPortMaxTxnsPerId = 32'd0,
  /// Maximum number of in-flight transactions at the subordinate port.  Reads and writes are counted
  /// separately (except for ATOPs, which count as both read and write).
  ///
  /// This parameter is only relevant if `SbrPortMaxUniqIds > 2**MgrPortIdWidth`.  In that
  /// case, this parameter is passed to
  /// [`axi_id_serialize`](module.axi_id_serialize#parameter.SbrPortMaxTxns).
  parameter int unsigned SbrPortMaxTxns = 32'd0,
  /// Maximum number of different IDs that can be in flight at the manager port.  Reads and writes
  /// are counted separately (except for ATOPs, which count as both read and write).
  ///
  /// This parameter is only relevant if `SbrPortMaxUniqIds > 2**MgrPortIdWidth`.  In that
  /// case, this parameter is passed to
  /// [`axi_id_serialize`](module.axi_id_serialize#parameter.MgrPortMaxUniqIds).
  parameter int unsigned MgrPortMaxUniqIds = 32'd0,
  /// Maximum number of in-flight transactions with the same ID at the manager port.
  ///
  /// This parameter is only relevant if `SbrPortMaxUniqIds > 2**MgrPortIdWidth`.  In that
  /// case, this parameter is passed to
  /// [`axi_id_serialize`](module.axi_id_serialize#parameter.MgrPortMaxTxnsPerId).
  parameter int unsigned MgrPortMaxTxnsPerId = 32'd0,
  /// Address width of both AXI4+ATOP ports
  parameter int unsigned AddrWidth = 32'd0,
  /// Data width of both AXI4+ATOP ports
  parameter int unsigned DataWidth = 32'd0,
  /// User signal width of both AXI4+ATOP ports
  parameter int unsigned UserWidth = 32'd0,
  /// Request struct type of the AXI4+ATOP subordinate port
  parameter type sbr_port_axi_req_t = logic,
  /// Response struct type of the AXI4+ATOP subordinate port
  parameter type sbr_port_axi_rsp_t = logic,
  /// Request struct type of the AXI4+ATOP manager port
  parameter type mgr_port_axi_req_t = logic,
  /// Response struct type of the AXI4+ATOP manager port
  parameter type mgr_port_axi_rsp_t = logic
) (
  /// Rising-edge clock of both ports
  input  logic              clk_i,
  /// Asynchronous reset, active low
  input  logic              rst_ni,
  /// Subordinate port request
  input  sbr_port_axi_req_t sbr_req_i,
  /// Subordinate port response
  output sbr_port_axi_rsp_t sbr_rsp_o,
  /// Manager port request
  output mgr_port_axi_req_t mgr_req_o,
  /// Manager port response
  input  mgr_port_axi_rsp_t mgr_rsp_i
);

  typedef logic [AddrWidth-1:0]      addr_t;
  typedef logic [DataWidth-1:0]      data_t;
  typedef logic [SbrPortIdWidth-1:0] sbr_id_t;
  typedef logic [MgrPortIdWidth-1:0] mgr_id_t;
  typedef logic [DataWidth/8-1:0]    strb_t;
  typedef logic [UserWidth-1:0]      user_t;
  `AXI_TYPEDEF_AW_CHAN_T(sbr_aw_t, addr_t, sbr_id_t, user_t)
  `AXI_TYPEDEF_AW_CHAN_T(mgr_aw_t, addr_t, mgr_id_t, user_t)
  `AXI_TYPEDEF_W_CHAN_T(w_t, data_t, strb_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T(sbr_b_t, sbr_id_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T(mgr_b_t, mgr_id_t, user_t)
  `AXI_TYPEDEF_AR_CHAN_T(sbr_ar_t, addr_t, sbr_id_t, user_t)
  `AXI_TYPEDEF_AR_CHAN_T(mgr_ar_t, addr_t, mgr_id_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(sbr_r_t, data_t, sbr_id_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(mgr_r_t, data_t, mgr_id_t, user_t)

  if (MgrPortIdWidth < SbrPortIdWidth) begin : gen_downsize
    if (SbrPortMaxUniqIds <= 2**MgrPortIdWidth) begin : gen_remap
      axi_id_remap #(
        .SbrPortIdWidth     ( SbrPortIdWidth       ),
        .MgrPortIdWidth     ( MgrPortIdWidth       ),
        .SbrPortMaxUniqIds  ( SbrPortMaxUniqIds    ),
        .MaxTxnsPerId       ( SbrPortMaxTxnsPerId  ),
        .sbr_port_axi_req_t ( sbr_port_axi_req_t   ),
        .sbr_port_axi_rsp_t ( sbr_port_axi_rsp_t   ),
        .mgr_port_axi_req_t ( mgr_port_axi_req_t   ),
        .mgr_port_axi_rsp_t ( mgr_port_axi_rsp_t   )
      ) i_axi_id_remap (
        .clk_i,
        .rst_ni,
        .sbr_req_i ( sbr_req_i ),
        .sbr_rsp_o ( sbr_rsp_o ),
        .mgr_req_o ( mgr_req_o ),
        .mgr_rsp_i ( mgr_rsp_i )
      );
    end else begin : gen_serialize
      axi_id_serialize #(
        .SbrPortIdWidth      ( SbrPortIdWidth       ),
        .SbrPortMaxTxns      ( SbrPortMaxTxns       ),
        .MgrPortIdWidth      ( MgrPortIdWidth       ),
        .MgrPortMaxUniqIds   ( MgrPortMaxUniqIds    ),
        .MgrPortMaxTxnsPerId ( MgrPortMaxTxnsPerId  ),
        .AddrWidth           ( AddrWidth            ),
        .DataWidth           ( DataWidth            ),
        .UserWidth           ( UserWidth            ),
        .sbr_port_axi_req_t  ( sbr_port_axi_req_t   ),
        .sbr_port_axi_rsp_t  ( sbr_port_axi_rsp_t   ),
        .mgr_port_axi_req_t  ( mgr_port_axi_req_t   ),
        .mgr_port_axi_rsp_t  ( mgr_port_axi_rsp_t   )
      ) i_axi_id_serialize (
        .clk_i,
        .rst_ni,
        .sbr_req_i ( sbr_req_i ),
        .sbr_rsp_o ( sbr_rsp_o ),
        .mgr_req_o ( mgr_req_o ),
        .mgr_rsp_i ( mgr_rsp_i )
      );
      end
  end else if (MgrPortIdWidth > SbrPortIdWidth) begin : gen_upsize
    axi_id_prepend #(
      .NumBus         ( 32'd1           ),
      .IdWidthSbrPort ( SbrPortIdWidth  ),
      .IdWidthMgrPort ( MgrPortIdWidth  ),
      .sbr_aw_chan_t  ( sbr_aw_t        ),
      .sbr_w_chan_t   ( w_t             ),
      .sbr_b_chan_t   ( sbr_b_t         ),
      .sbr_ar_chan_t  ( sbr_ar_t        ),
      .sbr_r_chan_t   ( sbr_r_t         ),
      .mgr_aw_chan_t  ( mgr_aw_t        ),
      .mgr_w_chan_t   ( w_t             ),
      .mgr_b_chan_t   ( mgr_b_t         ),
      .mgr_ar_chan_t  ( mgr_ar_t        ),
      .mgr_r_chan_t   ( mgr_r_t         )
    ) i_axi_id_prepend (
      .pre_id_i         ( '0                 ),
      .sbr_aw_chans_i   ( sbr_req_i.aw       ),
      .sbr_aw_valids_i  ( sbr_req_i.aw_valid ),
      .sbr_aw_readies_o ( sbr_rsp_o.aw_ready ),
      .sbr_w_chans_i    ( sbr_req_i.w        ),
      .sbr_w_valids_i   ( sbr_req_i.w_valid  ),
      .sbr_w_readies_o  ( sbr_rsp_o.w_ready  ),
      .sbr_b_chans_o    ( sbr_rsp_o.b        ),
      .sbr_b_valids_o   ( sbr_rsp_o.b_valid  ),
      .sbr_b_readies_i  ( sbr_req_i.b_ready  ),
      .sbr_ar_chans_i   ( sbr_req_i.ar       ),
      .sbr_ar_valids_i  ( sbr_req_i.ar_valid ),
      .sbr_ar_readies_o ( sbr_rsp_o.ar_ready ),
      .sbr_r_chans_o    ( sbr_rsp_o.r        ),
      .sbr_r_valids_o   ( sbr_rsp_o.r_valid  ),
      .sbr_r_readies_i  ( sbr_req_i.r_ready  ),
      .mgr_aw_chans_o   ( mgr_req_o.aw       ),
      .mgr_aw_valids_o  ( mgr_req_o.aw_valid ),
      .mgr_aw_readies_i ( mgr_rsp_i.aw_ready ),
      .mgr_w_chans_o    ( mgr_req_o.w        ),
      .mgr_w_valids_o   ( mgr_req_o.w_valid  ),
      .mgr_w_readies_i  ( mgr_rsp_i.w_ready  ),
      .mgr_b_chans_i    ( mgr_rsp_i.b        ),
      .mgr_b_valids_i   ( mgr_rsp_i.b_valid  ),
      .mgr_b_readies_o  ( mgr_req_o.b_ready  ),
      .mgr_ar_chans_o   ( mgr_req_o.ar       ),
      .mgr_ar_valids_o  ( mgr_req_o.ar_valid ),
      .mgr_ar_readies_i ( mgr_rsp_i.ar_ready ),
      .mgr_r_chans_i    ( mgr_rsp_i.r        ),
      .mgr_r_valids_i   ( mgr_rsp_i.r_valid  ),
      .mgr_r_readies_o  ( mgr_req_o.r_ready  )
    );
  end else begin : gen_passthrough
    assign mgr_req_o = sbr_req_i;
    assign sbr_rsp_o = mgr_rsp_i;
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
    assert(SbrPortIdWidth > 32'd0)
      else $fatal(1, "Parameter SbrPortIdWidth has to be larger than 0!");
    assert(MgrPortIdWidth > 32'd0)
      else $fatal(1, "Parameter MgrPortIdWidth has to be larger than 0!");
    if (SbrPortMaxUniqIds <= 2**MgrPortIdWidth) begin
      assert(SbrPortMaxTxnsPerId > 32'd0)
        else $fatal(1, "Parameter SbrPortMaxTxnsPerId has to be larger than 0!");
    end else begin
      assert(MgrPortMaxUniqIds > 32'd0)
        else $fatal(1, "Parameter MgrPortMaxUniqIds has to be larger than 0!");
      assert(MgrPortMaxTxnsPerId > 32'd0)
        else $fatal(1, "Parameter MgrPortMaxTxnsPerId has to be larger than 0!");
    end
    assert($bits(sbr_req_i.aw.addr) == $bits(mgr_req_o.aw.addr))
      else $fatal(1, "AXI AW address widths are not equal!");
    assert($bits(sbr_req_i.w.data) == $bits(mgr_req_o.w.data))
      else $fatal(1, "AXI W data widths are not equal!");
    assert($bits(sbr_req_i.ar.addr) == $bits(mgr_req_o.ar.addr))
      else $fatal(1, "AXI AR address widths are not equal!");
    assert($bits(sbr_rsp_o.r.data) == $bits(mgr_rsp_i.r.data))
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
  parameter int unsigned AXI_SBR_PORT_ID_WIDTH = 32'd0,
  parameter int unsigned AXI_MGR_PORT_ID_WIDTH = 32'd0,
  parameter int unsigned AXI_SBR_PORT_MAX_UNIQ_IDS = 32'd0,
  parameter int unsigned AXI_SBR_PORT_MAX_TXNS_PER_ID = 32'd0,
  parameter int unsigned AXI_SBR_PORT_MAX_TXNS = 32'd0,
  parameter int unsigned AXI_MGR_PORT_MAX_UNIQ_IDS = 32'd0,
  parameter int unsigned AXI_MGR_PORT_MAX_TXNS_PER_ID = 32'd0,
  parameter int unsigned AXI_ADDR_WIDTH = 32'd0,
  parameter int unsigned AXI_DATA_WIDTH = 32'd0,
  parameter int unsigned AXI_USER_WIDTH = 32'd0
) (
  input  logic   clk_i,
  input  logic   rst_ni,
  AXI_BUS.Subordinate  sbr,
  AXI_BUS.Manager mgr
);
  typedef logic [AXI_SBR_PORT_ID_WIDTH-1:0] sbr_id_t;
  typedef logic [AXI_MGR_PORT_ID_WIDTH-1:0] mgr_id_t;
  typedef logic [AXI_ADDR_WIDTH-1:0]        axi_addr_t;
  typedef logic [AXI_DATA_WIDTH-1:0]        axi_data_t;
  typedef logic [AXI_DATA_WIDTH/8-1:0]      axi_strb_t;
  typedef logic [AXI_USER_WIDTH-1:0]        axi_user_t;

  `AXI_TYPEDEF_AW_CHAN_T(sbr_aw_chan_t, axi_addr_t, sbr_id_t, axi_user_t)
  `AXI_TYPEDEF_W_CHAN_T(sbr_w_chan_t, axi_data_t, axi_strb_t, axi_user_t)
  `AXI_TYPEDEF_B_CHAN_T(sbr_b_chan_t, sbr_id_t, axi_user_t)
  `AXI_TYPEDEF_AR_CHAN_T(sbr_ar_chan_t, axi_addr_t, sbr_id_t, axi_user_t)
  `AXI_TYPEDEF_R_CHAN_T(sbr_r_chan_t, axi_data_t, sbr_id_t, axi_user_t)
  `AXI_TYPEDEF_REQ_T(sbr_port_axi_req_t, sbr_aw_chan_t, sbr_w_chan_t, sbr_ar_chan_t)
  `AXI_TYPEDEF_RSP_T(sbr_port_axi_rsp_t, sbr_b_chan_t, sbr_r_chan_t)

  `AXI_TYPEDEF_AW_CHAN_T(mgr_aw_chan_t, axi_addr_t, mgr_id_t, axi_user_t)
  `AXI_TYPEDEF_W_CHAN_T(mgr_w_chan_t, axi_data_t, axi_strb_t, axi_user_t)
  `AXI_TYPEDEF_B_CHAN_T(mgr_b_chan_t, mgr_id_t, axi_user_t)
  `AXI_TYPEDEF_AR_CHAN_T(mgr_ar_chan_t, axi_addr_t, mgr_id_t, axi_user_t)
  `AXI_TYPEDEF_R_CHAN_T(mgr_r_chan_t, axi_data_t, mgr_id_t, axi_user_t)
  `AXI_TYPEDEF_REQ_T(mgr_port_axi_req_t, mgr_aw_chan_t, mgr_w_chan_t, mgr_ar_chan_t)
  `AXI_TYPEDEF_RSP_T(mgr_port_axi_rsp_t, mgr_b_chan_t, mgr_r_chan_t)

  sbr_port_axi_req_t sbr_req;
  sbr_port_axi_rsp_t sbr_rsp;
  mgr_port_axi_req_t mgr_req;
  mgr_port_axi_rsp_t mgr_rsp;

  `AXI_ASSIGN_TO_REQ(sbr_req, sbr)
  `AXI_ASSIGN_FROM_RSP(sbr, sbr_rsp)
  `AXI_ASSIGN_FROM_REQ(mgr, mgr_req)
  `AXI_ASSIGN_TO_RSP(mgr_rsp, mgr)

  axi_iw_converter #(
    .SbrPortIdWidth      ( AXI_SBR_PORT_ID_WIDTH         ),
    .MgrPortIdWidth      ( AXI_MGR_PORT_ID_WIDTH         ),
    .SbrPortMaxUniqIds   ( AXI_SBR_PORT_MAX_UNIQ_IDS     ),
    .SbrPortMaxTxnsPerId ( AXI_SBR_PORT_MAX_TXNS_PER_ID  ),
    .SbrPortMaxTxns      ( AXI_SBR_PORT_MAX_TXNS         ),
    .MgrPortMaxUniqIds   ( AXI_MGR_PORT_MAX_UNIQ_IDS     ),
    .MgrPortMaxTxnsPerId ( AXI_MGR_PORT_MAX_TXNS_PER_ID  ),
    .AddrWidth           ( AXI_ADDR_WIDTH                ),
    .DataWidth           ( AXI_DATA_WIDTH                ),
    .UserWidth           ( AXI_USER_WIDTH                ),
    .sbr_port_axi_req_t  ( sbr_port_axi_req_t            ),
    .sbr_port_axi_rsp_t  ( sbr_port_axi_rsp_t            ),
    .mgr_port_axi_req_t  ( mgr_port_axi_req_t            ),
    .mgr_port_axi_rsp_t  ( mgr_port_axi_rsp_t            )
  ) i_axi_iw_converter (
    .clk_i,
    .rst_ni,
    .sbr_req_i ( sbr_req ),
    .sbr_rsp_o ( sbr_rsp ),
    .mgr_req_o ( mgr_req ),
    .mgr_rsp_i ( mgr_rsp )
  );
  // pragma translate_off
  `ifndef VERILATOR
    initial begin
      assert (sbr.AXI_ID_WIDTH   == AXI_SBR_PORT_ID_WIDTH);
      assert (sbr.AXI_ADDR_WIDTH == AXI_ADDR_WIDTH);
      assert (sbr.AXI_DATA_WIDTH == AXI_DATA_WIDTH);
      assert (sbr.AXI_USER_WIDTH == AXI_USER_WIDTH);
      assert (mgr.AXI_ID_WIDTH   == AXI_MGR_PORT_ID_WIDTH);
      assert (mgr.AXI_ADDR_WIDTH == AXI_ADDR_WIDTH);
      assert (mgr.AXI_DATA_WIDTH == AXI_DATA_WIDTH);
      assert (mgr.AXI_USER_WIDTH == AXI_USER_WIDTH);
    end
  `endif
  // pragma translate_on
endmodule
