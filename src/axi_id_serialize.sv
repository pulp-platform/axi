// Copyright (c) 2020 ETH Zurich, University of Bologna
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

`include "axi/assign.svh"
`include "axi/typedef.svh"

/// Reduce AXI IDs by serializing transactions when necessary.
///
/// This module is designed to remap a wide ID space to an arbitrarily narrow ID space.  If
/// necessary, this module maps two different IDs at its subordinate port to the same ID at its manager
/// port, thereby constraining the order of those transactions and in this sense *serializing* them.
/// If the independence of IDs needs to be retained at the cost of a wider ID space at the manager
/// port, use [`axi_id_remap`](module.axi_id_remap) instead.
///
/// This module contains one [`axi_serializer`](module.axi_serializer) per manager port ID (given by
/// the `MgrPortMaxUniqIds parameter`).
module axi_id_serialize #(
  /// ID width of the AXI4+ATOP subordinate port
  parameter int unsigned SbrPortIdWidth = 32'd0,
  /// Maximum number of transactions that can be in flight at the subordinate port.  Reads and writes are
  /// counted separately (except for ATOPs, which count as both read and write).
  parameter int unsigned SbrPortMaxTxns = 32'd0,
  /// ID width of the AXI4+ATOP manager port
  parameter int unsigned MgrPortIdWidth = 32'd0,
  /// Maximum number of different IDs that can be in flight at the manager port.  Reads and writes
  /// are counted separately (except for ATOPs, which count as both read and write).
  ///
  /// The maximum value of this parameter is `2**MgrPortIdWidth`.
  parameter int unsigned MgrPortMaxUniqIds = 32'd0,
  /// Maximum number of in-flight transactions with the same ID at the manager port.
  parameter int unsigned MgrPortMaxTxnsPerId = 32'd0,
  /// Address width of both AXI4+ATOP ports
  parameter int unsigned AddrWidth = 32'd0,
  /// Data width of both AXI4+ATOP ports
  parameter int unsigned DataWidth = 32'd0,
  /// User width of both AXI4+ATOP ports
  parameter int unsigned UserWidth = 32'd0,
  /// Enable support for AXI4+ATOP atomics
  parameter bit          AtopSupport = 1'b1,
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
  input  sbr_port_axi_req_t sbr_port_req_i,
  /// Subordinate port response
  output sbr_port_axi_rsp_t sbr_port_rsp_o,
  /// Manager port request
  output mgr_port_axi_req_t mgr_port_req_o,
  /// Manager port response
  input  mgr_port_axi_rsp_t mgr_port_rsp_i
);

  /// Number of bits of the subordinate port ID that determine the mapping to the manager port ID
  localparam int unsigned SelectWidth = cf_math_pkg::idx_width(MgrPortMaxUniqIds);
  /// Slice of subordinate port IDs that determines the manager port ID
  typedef logic [SelectWidth-1:0] select_t;

  /// ID width after the multiplexer
  localparam int unsigned MuxIdWidth = (MgrPortMaxUniqIds > 32'd1) ? SelectWidth + 32'd1 : 32'd1;

  /// ID after serializer (i.e., with a constant value of zero)
  typedef logic [0:0]                ser_id_t;
  /// ID after the multiplexer
  typedef logic [MuxIdWidth-1:0]     mux_id_t;
  /// ID at the subordinate port
  typedef logic [SbrPortIdWidth-1:0] sbr_id_t;
  /// ID at the manager port
  typedef logic [MgrPortIdWidth-1:0] mgr_id_t;
  /// Address in any AXI channel
  typedef logic [AddrWidth-1:0]      addr_t;
  /// Data in any AXI channel
  typedef logic [DataWidth-1:0]      data_t;
  /// Strobe in any AXI channel
  typedef logic [DataWidth/8-1:0]    strb_t;
  /// User signal in any AXI channel
  typedef logic [UserWidth-1:0]      user_t;

  /// W channel at any interface
  `AXI_TYPEDEF_W_CHAN_T(w_t, data_t, strb_t, user_t)

  /// AW channel at subordinate port
  `AXI_TYPEDEF_AW_CHAN_T(sbr_aw_t, addr_t, sbr_id_t, user_t)
  /// B channel at subordinate port
  `AXI_TYPEDEF_B_CHAN_T(sbr_b_t, sbr_id_t, user_t)
  /// AR channel at subordinate port
  `AXI_TYPEDEF_AR_CHAN_T(sbr_ar_t, addr_t, sbr_id_t, user_t)
  /// R channel at subordinate port
  `AXI_TYPEDEF_R_CHAN_T(sbr_r_t, data_t, sbr_id_t, user_t)

  /// AW channel after serializer
  `AXI_TYPEDEF_AW_CHAN_T(ser_aw_t, addr_t, ser_id_t, user_t)
  /// B channel after serializer
  `AXI_TYPEDEF_B_CHAN_T(ser_b_t, ser_id_t, user_t)
  /// AR channel after serializer
  `AXI_TYPEDEF_AR_CHAN_T(ser_ar_t, addr_t, ser_id_t, user_t)
  /// R channel after serializer
  `AXI_TYPEDEF_R_CHAN_T(ser_r_t, data_t, ser_id_t, user_t)
  /// AXI Requests from serializer
  `AXI_TYPEDEF_REQ_T(ser_req_t, ser_aw_t, w_t, ser_ar_t)
  /// AXI responses to serializer
  `AXI_TYPEDEF_RSP_T(ser_rsp_t, ser_b_t, ser_r_t)

  /// AW channel after the multiplexer
  `AXI_TYPEDEF_AW_CHAN_T(mux_aw_t, addr_t, mux_id_t, user_t)
  /// B channel after the multiplexer
  `AXI_TYPEDEF_B_CHAN_T(mux_b_t, mux_id_t, user_t)
  /// AR channel after the multiplexer
  `AXI_TYPEDEF_AR_CHAN_T(mux_ar_t, addr_t, mux_id_t, user_t)
  /// R channel after the multiplexer
  `AXI_TYPEDEF_R_CHAN_T(mux_r_t, data_t, mux_id_t, user_t)
  /// AXI requests from the multiplexer
  `AXI_TYPEDEF_REQ_T(mux_req_t, mux_aw_t, w_t, mux_ar_t)
  /// AXI responses to the multiplexer
  `AXI_TYPEDEF_RSP_T(mux_rsp_t, mux_b_t, mux_r_t)

  /// AW channel at manager port
  `AXI_TYPEDEF_AW_CHAN_T(mgr_aw_t, addr_t, mgr_id_t, user_t)
  /// B channel at manager port
  `AXI_TYPEDEF_B_CHAN_T(mgr_b_t, mgr_id_t, user_t)
  /// AR channel at manager port
  `AXI_TYPEDEF_AR_CHAN_T(mgr_ar_t, addr_t, mgr_id_t, user_t)
  /// R channel at manager port
  `AXI_TYPEDEF_R_CHAN_T(mgr_r_t, data_t, mgr_id_t, user_t)

  select_t sbr_aw_select, sbr_ar_select;
  assign sbr_aw_select = select_t'(sbr_port_req_i.aw.id % MgrPortMaxUniqIds); // TODO: customizable base
  assign sbr_ar_select = select_t'(sbr_port_req_i.ar.id % MgrPortMaxUniqIds);

  sbr_port_axi_req_t [MgrPortMaxUniqIds-1:0] to_serializer_reqs;
  sbr_port_axi_rsp_t [MgrPortMaxUniqIds-1:0] to_serializer_rsps;

  axi_demux #(
    .IdWidth     ( SbrPortIdWidth     ),
    .aw_chan_t   ( sbr_aw_t           ),
    .w_chan_t    ( w_t                ),
    .b_chan_t    ( sbr_b_t            ),
    .ar_chan_t   ( sbr_ar_t           ),
    .r_chan_t    ( sbr_r_t            ),
    .axi_req_t   ( sbr_port_axi_req_t ),
    .axi_rsp_t   ( sbr_port_axi_rsp_t ),
    .NumMgrPorts ( MgrPortMaxUniqIds  ),
    .MaxTrans    ( SbrPortMaxTxns     ),
    .LookBits    ( SbrPortIdWidth     ),
    .AtopSupport ( AtopSupport        ),
    .SpillAw     ( 1'b1               ),
    .SpillW      ( 1'b0               ),
    .SpillB      ( 1'b0               ),
    .SpillAr     ( 1'b1               ),
    .SpillR      ( 1'b0               )
  ) i_axi_demux (
    .clk_i,
    .rst_ni,
    .test_i          ( 1'b0               ),
    .sbr_port_req_i       ( sbr_port_req_i          ),
    .sbr_aw_select_i ( sbr_aw_select      ),
    .sbr_ar_select_i ( sbr_ar_select      ),
    .sbr_port_rsp_o       ( sbr_port_rsp_o          ),
    .mgr_ports_req_o      ( to_serializer_reqs ),
    .mgr_ports_rsp_i      ( to_serializer_rsps )
  );

  sbr_port_axi_req_t [MgrPortMaxUniqIds-1:0] tmp_serializer_reqs;
  sbr_port_axi_rsp_t [MgrPortMaxUniqIds-1:0] tmp_serializer_rsps;
  ser_req_t [MgrPortMaxUniqIds-1:0] from_serializer_reqs;
  ser_rsp_t [MgrPortMaxUniqIds-1:0] from_serializer_rsps;

  for (genvar i = 0; i < MgrPortMaxUniqIds; i++) begin : gen_serializers
    axi_serializer #(
      .MaxReadTxns  ( MgrPortMaxTxnsPerId  ),
      .MaxWriteTxns ( MgrPortMaxTxnsPerId  ),
      .IdWidth      ( SbrPortIdWidth       ),
      .axi_req_t    ( sbr_port_axi_req_t   ),
      .axi_rsp_t    ( sbr_port_axi_rsp_t   )
    ) i_axi_serializer (
      .clk_i,
      .rst_ni,
      .sbr_port_req_i ( to_serializer_reqs[i]  ),
      .sbr_port_rsp_o ( to_serializer_rsps[i]  ),
      .mgr_port_req_o ( tmp_serializer_reqs[i] ),
      .mgr_port_rsp_i ( tmp_serializer_rsps[i] )
    );
    always_comb begin
      `AXI_SET_REQ_STRUCT(from_serializer_reqs[i], tmp_serializer_reqs[i])
      // Truncate to ID width 1 as all requests have ID '0.
      from_serializer_reqs[i].aw.id = tmp_serializer_reqs[i].aw.id[0];
      from_serializer_reqs[i].ar.id = tmp_serializer_reqs[i].ar.id[0];
      `AXI_SET_RSP_STRUCT(tmp_serializer_rsps[i], from_serializer_rsps[i])
      // Zero-extend response IDs.
      tmp_serializer_rsps[i].b.id = {{SbrPortIdWidth-1{1'b0}}, from_serializer_rsps[i].b.id};
      tmp_serializer_rsps[i].r.id = {{SbrPortIdWidth-1{1'b0}}, from_serializer_rsps[i].r.id};
    end
  end

  mux_req_t axi_mux_req;
  mux_rsp_t axi_mux_rsp;

  axi_mux #(
    .SbrIDWidth         ( 32'd1               ),
    .sbr_aw_chan_t      ( ser_aw_t            ),
    .mgr_aw_chan_t      ( mux_aw_t            ),
    .w_chan_t           ( w_t                 ),
    .sbr_b_chan_t       ( ser_b_t             ),
    .mgr_b_chan_t       ( mux_b_t             ),
    .sbr_ar_chan_t      ( ser_ar_t            ),
    .mgr_ar_chan_t      ( mux_ar_t            ),
    .sbr_r_chan_t       ( ser_r_t             ),
    .mgr_r_chan_t       ( mux_r_t             ),
    .sbr_port_axi_req_t ( ser_req_t           ),
    .sbr_port_axi_rsp_t ( ser_rsp_t           ),
    .mgr_port_axi_req_t ( mux_req_t           ),
    .mgr_port_axi_rsp_t ( mux_rsp_t           ),
    .NumSbrPorts        ( MgrPortMaxUniqIds   ),
    .MaxWTrans          ( MgrPortMaxTxnsPerId ),
    .FallThrough        ( 1'b0                ),
    .SpillAw            ( 1'b1                ),
    .SpillW             ( 1'b0                ),
    .SpillB             ( 1'b0                ),
    .SpillAr            ( 1'b1                ),
    .SpillR             ( 1'b0                )
  ) i_axi_mux (
    .clk_i,
    .rst_ni,
    .test_i     ( 1'b0                  ),
    .sbr_ports_req_i ( from_serializer_reqs  ),
    .sbr_ports_rsp_o ( from_serializer_rsps  ),
    .mgr_port_req_o  ( axi_mux_req           ),
    .mgr_port_rsp_i  ( axi_mux_rsp           )
  );

  // Shift the ID one down if needed, as mux prepends IDs
  if (MuxIdWidth > 32'd1) begin : gen_id_shift
    always_comb begin
      `AXI_SET_REQ_STRUCT(mgr_port_req_o, axi_mux_req)
      mgr_port_req_o.aw.id = mgr_id_t'(axi_mux_req.aw.id >> 32'd1);
      mgr_port_req_o.ar.id = mgr_id_t'(axi_mux_req.ar.id >> 32'd1);
      `AXI_SET_RSP_STRUCT(axi_mux_rsp, mgr_port_rsp_i)
      axi_mux_rsp.b.id = mux_id_t'(mgr_port_rsp_i.b.id << 32'd1);
      axi_mux_rsp.r.id = mux_id_t'(mgr_port_rsp_i.r.id << 32'd1);
    end
  end else begin : gen_no_id_shift
    axi_id_prepend #(
      .NumBus         ( 32'd1           ),
      .IdWidthSbrPort ( MuxIdWidth      ),
      .IdWidthMgrPort ( MgrPortIdWidth  ),
      .sbr_aw_chan_t  ( mux_aw_t        ),
      .sbr_w_chan_t   ( w_t             ),
      .sbr_b_chan_t   ( mux_b_t         ),
      .sbr_ar_chan_t  ( mux_ar_t        ),
      .sbr_r_chan_t   ( mux_r_t         ),
      .mgr_aw_chan_t  ( mgr_aw_t        ),
      .mgr_w_chan_t   ( w_t             ),
      .mgr_b_chan_t   ( mgr_b_t         ),
      .mgr_ar_chan_t  ( mgr_ar_t        ),
      .mgr_r_chan_t   ( mgr_r_t         )
    ) i_axi_id_prepend (
      .pre_id_i         ( '0                   ),
      .sbr_aw_chans_i   ( axi_mux_req.aw       ),
      .sbr_aw_valids_i  ( axi_mux_req.aw_valid ),
      .sbr_aw_readies_o ( axi_mux_rsp.aw_ready ),
      .sbr_w_chans_i    ( axi_mux_req.w        ),
      .sbr_w_valids_i   ( axi_mux_req.w_valid  ),
      .sbr_w_readies_o  ( axi_mux_rsp.w_ready  ),
      .sbr_b_chans_o    ( axi_mux_rsp.b        ),
      .sbr_b_valids_o   ( axi_mux_rsp.b_valid  ),
      .sbr_b_readies_i  ( axi_mux_req.b_ready  ),
      .sbr_ar_chans_i   ( axi_mux_req.ar       ),
      .sbr_ar_valids_i  ( axi_mux_req.ar_valid ),
      .sbr_ar_readies_o ( axi_mux_rsp.ar_ready ),
      .sbr_r_chans_o    ( axi_mux_rsp.r        ),
      .sbr_r_valids_o   ( axi_mux_rsp.r_valid  ),
      .sbr_r_readies_i  ( axi_mux_req.r_ready  ),
      .mgr_aw_chans_o   ( mgr_port_req_o.aw         ),
      .mgr_aw_valids_o  ( mgr_port_req_o.aw_valid   ),
      .mgr_aw_readies_i ( mgr_port_rsp_i.aw_ready   ),
      .mgr_w_chans_o    ( mgr_port_req_o.w          ),
      .mgr_w_valids_o   ( mgr_port_req_o.w_valid    ),
      .mgr_w_readies_i  ( mgr_port_rsp_i.w_ready    ),
      .mgr_b_chans_i    ( mgr_port_rsp_i.b          ),
      .mgr_b_valids_i   ( mgr_port_rsp_i.b_valid    ),
      .mgr_b_readies_o  ( mgr_port_req_o.b_ready    ),
      .mgr_ar_chans_o   ( mgr_port_req_o.ar         ),
      .mgr_ar_valids_o  ( mgr_port_req_o.ar_valid   ),
      .mgr_ar_readies_i ( mgr_port_rsp_i.ar_ready   ),
      .mgr_r_chans_i    ( mgr_port_rsp_i.r          ),
      .mgr_r_valids_i   ( mgr_port_rsp_i.r_valid    ),
      .mgr_r_readies_o  ( mgr_port_req_o.r_ready    )
    );
  end

  // pragma translate_off
  `ifndef VERILATOR
  initial begin : p_assert
    assert(MgrPortMaxUniqIds > 32'd0)
      else $fatal(1, "MgrPortMaxUniqIds has to be > 0.");
    assert(2**(MgrPortIdWidth) >= MgrPortMaxUniqIds)
      else $fatal(1, "Not enought Id width on MGR port to map all ID's.");
    assert(SbrPortIdWidth > 32'd0)
      else $fatal(1, "Parameter SbrPortIdWidth has to be larger than 0!");
    assert(MgrPortIdWidth)
      else $fatal(1, "Parameter MgrPortIdWidth has to be larger than 0!");
    assert(MgrPortIdWidth <= SbrPortIdWidth)
      else $fatal(1, "Downsize implies that MgrPortIdWidth <= SbrPortIdWidth!");
    assert($bits(sbr_port_req_i.aw.addr) == $bits(mgr_port_req_o.aw.addr))
      else $fatal(1, "AXI AW address widths are not equal!");
    assert($bits(sbr_port_req_i.w.data) == $bits(mgr_port_req_o.w.data))
      else $fatal(1, "AXI W data widths are not equal!");
    assert($bits(sbr_port_req_i.ar.addr) == $bits(mgr_port_req_o.ar.addr))
      else $fatal(1, "AXI AR address widths are not equal!");
    assert($bits(sbr_port_rsp_o.r.data) == $bits(mgr_port_rsp_i.r.data))
      else $fatal(1, "AXI R data widths are not equal!");
  end
  `endif
  // pragma translate_on
endmodule


/// Interface variant of [`axi_id_serialize`](module.axi_id_serialize).
///
/// See the documentation of the main module for the definition of ports and parameters.
module axi_id_serialize_intf #(
  parameter int unsigned AXI_SBR_PORT_ID_WIDTH = 32'd0,
  parameter int unsigned AXI_SBR_PORT_MAX_TXNS = 32'd0,
  parameter int unsigned AXI_MGR_PORT_ID_WIDTH = 32'd0,
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
  typedef logic [AXI_ADDR_WIDTH-1:0]        addr_t;
  typedef logic [AXI_DATA_WIDTH-1:0]        data_t;
  typedef logic [AXI_DATA_WIDTH/8-1:0]      strb_t;
  typedef logic [AXI_USER_WIDTH-1:0]        user_t;

  `AXI_TYPEDEF_AW_CHAN_T(sbr_aw_t, addr_t, sbr_id_t, user_t)
  `AXI_TYPEDEF_W_CHAN_T(w_t, data_t, strb_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T(sbr_b_t, sbr_id_t, user_t)
  `AXI_TYPEDEF_AR_CHAN_T(sbr_ar_t, addr_t, sbr_id_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(sbr_r_t, data_t, sbr_id_t, user_t)
  `AXI_TYPEDEF_REQ_T(sbr_port_axi_req_t, sbr_aw_t, w_t, sbr_ar_t)
  `AXI_TYPEDEF_RSP_T(sbr_port_axi_rsp_t, sbr_b_t, sbr_r_t)

  `AXI_TYPEDEF_AW_CHAN_T(mgr_aw_t, addr_t, mgr_id_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T(mgr_b_t, mgr_id_t, user_t)
  `AXI_TYPEDEF_AR_CHAN_T(mgr_ar_t, addr_t, mgr_id_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(mgr_r_t, data_t, mgr_id_t, user_t)
  `AXI_TYPEDEF_REQ_T(mgr_port_axi_req_t, mgr_aw_t, w_t, mgr_ar_t)
  `AXI_TYPEDEF_RSP_T(mgr_port_axi_rsp_t, mgr_b_t, mgr_r_t)

  sbr_port_axi_req_t sbr_req;
  sbr_port_axi_rsp_t sbr_rsp;
  mgr_port_axi_req_t mgr_req;
  mgr_port_axi_rsp_t mgr_rsp;

  `AXI_ASSIGN_TO_REQ(sbr_req, sbr)
  `AXI_ASSIGN_FROM_RSP(sbr, sbr_rsp)
  `AXI_ASSIGN_FROM_REQ(mgr, mgr_req)
  `AXI_ASSIGN_TO_RSP(mgr_rsp, mgr)

  axi_id_serialize #(
    .SbrPortIdWidth      ( AXI_SBR_PORT_ID_WIDTH         ),
    .SbrPortMaxTxns      ( AXI_SBR_PORT_MAX_TXNS         ),
    .MgrPortIdWidth      ( AXI_MGR_PORT_ID_WIDTH         ),
    .MgrPortMaxUniqIds   ( AXI_MGR_PORT_MAX_UNIQ_IDS     ),
    .MgrPortMaxTxnsPerId ( AXI_MGR_PORT_MAX_TXNS_PER_ID  ),
    .AddrWidth           ( AXI_ADDR_WIDTH                ),
    .DataWidth           ( AXI_DATA_WIDTH                ),
    .UserWidth           ( AXI_USER_WIDTH                ),
    .sbr_port_axi_req_t  ( sbr_port_axi_req_t            ),
    .sbr_port_axi_rsp_t  ( sbr_port_axi_rsp_t            ),
    .mgr_port_axi_req_t  ( mgr_port_axi_req_t            ),
    .mgr_port_axi_rsp_t  ( mgr_port_axi_rsp_t            )
  ) i_axi_id_serialize (
    .clk_i,
    .rst_ni,
    .sbr_port_req_i ( sbr_req ),
    .sbr_port_rsp_o ( sbr_rsp ),
    .mgr_port_req_o ( mgr_req ),
    .mgr_port_rsp_i ( mgr_rsp )
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
