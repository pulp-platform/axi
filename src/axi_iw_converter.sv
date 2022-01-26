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
/// in flight at the slave port of this module, given in the `AxiSlvPortMaxUniqIds` parameter.
///
/// ### Fewer unique slave port IDs than master port IDs
///
/// If `AxiSlvPortMaxUniqIds <= 2**AxiMstPortIdWidth`, there are fewer unique slave port IDs than
/// master port IDs.  Therefore, IDs that are different at the slave port of this module can remain
/// different at the reduced-ID-width master port and thus remain *independently reorderable*.
/// Since the IDs are master port are nonetheless shorter than at the slave port, they need to be
/// *remapped*.  An instance of [`axi_id_remap`](module.axi_id_remap) handles this case.
///
/// ### More unique slave port IDs than master port IDs
///
/// If `AxiSlvPortMaxUniqIds > 2**AxiMstPortIdWidth`, there are more unique slave port IDs than
/// master port IDs.  Therefore, some IDs that are different at the slave port need to be assigned
/// to the same master port ID and thus become ordered with respect to each other.  An instance of
/// [`axi_id_serialize`](module.axi_id_serialize) handles this case.
module axi_iw_converter #(
  /// ID width of the AXI4+ATOP slave port
  parameter int unsigned AxiSlvPortIdWidth = 32'd0,
  /// ID width of the AXI4+ATOP master port
  parameter int unsigned AxiMstPortIdWidth = 32'd0,
  /// Maximum number of different IDs that can be in flight at the slave port.  Reads and writes are
  /// counted separately (except for ATOPs, which count as both read and write).
  ///
  /// It is legal for upstream to have transactions with more unique IDs than the maximum given by
  /// this parameter in flight, but a transaction exceeding the maximum will be stalled until all
  /// transactions of another ID complete.
  parameter int unsigned AxiSlvPortMaxUniqIds = 32'd0,
  /// Maximum number of in-flight transactions with the same ID at the slave port.
  ///
  /// This parameter is only relevant if `AxiSlvPortMaxUniqIds <= 2**AxiMstPortIdWidth`.  In that
  /// case, this parameter is passed to [`axi_id_remap` as `AxiMaxTxnsPerId`
  /// parameter](module.axi_id_remap#parameter.AxiMaxTxnsPerId).
  parameter int unsigned AxiSlvPortMaxTxnsPerId = 32'd0,
  /// Maximum number of in-flight transactions at the slave port.  Reads and writes are counted
  /// separately (except for ATOPs, which count as both read and write).
  ///
  /// This parameter is only relevant if `AxiSlvPortMaxUniqIds > 2**AxiMstPortIdWidth`.  In that
  /// case, this parameter is passed to
  /// [`axi_id_serialize`](module.axi_id_serialize#parameter.AxiSlvPortMaxTxns).
  parameter int unsigned AxiSlvPortMaxTxns = 32'd0,
  /// Maximum number of different IDs that can be in flight at the master port.  Reads and writes
  /// are counted separately (except for ATOPs, which count as both read and write).
  ///
  /// This parameter is only relevant if `AxiSlvPortMaxUniqIds > 2**AxiMstPortIdWidth`.  In that
  /// case, this parameter is passed to
  /// [`axi_id_serialize`](module.axi_id_serialize#parameter.AxiMstPortMaxUniqIds).
  parameter int unsigned AxiMstPortMaxUniqIds = 32'd0,
  /// Maximum number of in-flight transactions with the same ID at the master port.
  ///
  /// This parameter is only relevant if `AxiSlvPortMaxUniqIds > 2**AxiMstPortIdWidth`.  In that
  /// case, this parameter is passed to
  /// [`axi_id_serialize`](module.axi_id_serialize#parameter.AxiMstPortMaxTxnsPerId).
  parameter int unsigned AxiMstPortMaxTxnsPerId = 32'd0,
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

  typedef logic [AxiAddrWidth-1:0]      addr_t;
  typedef logic [AxiDataWidth-1:0]      data_t;
  typedef logic [AxiSlvPortIdWidth-1:0] slv_id_t;
  typedef logic [AxiMstPortIdWidth-1:0] mst_id_t;
  typedef logic [AxiDataWidth/8-1:0]    strb_t;
  typedef logic [AxiUserWidth-1:0]      user_t;
  `AXI_TYPEDEF_AW_CHAN_T(slv_aw_t, addr_t, slv_id_t, user_t)
  `AXI_TYPEDEF_AW_CHAN_T(mst_aw_t, addr_t, mst_id_t, user_t)
  `AXI_TYPEDEF_W_CHAN_T(w_t, data_t, strb_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T(slv_b_t, slv_id_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T(mst_b_t, mst_id_t, user_t)
  `AXI_TYPEDEF_AR_CHAN_T(slv_ar_t, addr_t, slv_id_t, user_t)
  `AXI_TYPEDEF_AR_CHAN_T(mst_ar_t, addr_t, mst_id_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(slv_r_t, data_t, slv_id_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(mst_r_t, data_t, mst_id_t, user_t)

  if (AxiMstPortIdWidth < AxiSlvPortIdWidth) begin : gen_downsize
    if (AxiSlvPortMaxUniqIds <= 2**AxiMstPortIdWidth) begin : gen_remap
      axi_id_remap #(
        .AxiSlvPortIdWidth    ( AxiSlvPortIdWidth       ),
        .AxiMstPortIdWidth    ( AxiMstPortIdWidth       ),
        .AxiSlvPortMaxUniqIds ( AxiSlvPortMaxUniqIds    ),
        .AxiMaxTxnsPerId      ( AxiSlvPortMaxTxnsPerId  ),
        .slv_req_t            ( slv_req_t               ),
        .slv_resp_t           ( slv_resp_t              ),
        .mst_req_t            ( mst_req_t               ),
        .mst_resp_t           ( mst_resp_t              )
      ) i_axi_id_remap (
        .clk_i,
        .rst_ni,
        .slv_req_i  ( slv_req_i  ),
        .slv_resp_o ( slv_resp_o ),
        .mst_req_o  ( mst_req_o  ),
        .mst_resp_i ( mst_resp_i )
      );
    end else begin : gen_serialize
      axi_id_serialize #(
        .AxiSlvPortIdWidth      ( AxiSlvPortIdWidth       ),
        .AxiSlvPortMaxTxns      ( AxiSlvPortMaxTxns       ),
        .AxiMstPortIdWidth      ( AxiMstPortIdWidth       ),
        .AxiMstPortMaxUniqIds   ( AxiMstPortMaxUniqIds    ),
        .AxiMstPortMaxTxnsPerId ( AxiMstPortMaxTxnsPerId  ),
        .AxiAddrWidth           ( AxiAddrWidth            ),
        .AxiDataWidth           ( AxiDataWidth            ),
        .AxiUserWidth           ( AxiUserWidth            ),
        .slv_req_t              ( slv_req_t               ),
        .slv_resp_t             ( slv_resp_t              ),
        .mst_req_t              ( mst_req_t               ),
        .mst_resp_t             ( mst_resp_t              )
      ) i_axi_id_serialize (
        .clk_i,
        .rst_ni,
        .slv_req_i  ( slv_req_i  ),
        .slv_resp_o ( slv_resp_o ),
        .mst_req_o  ( mst_req_o  ),
        .mst_resp_i ( mst_resp_i )
      );
      end
  end else if (AxiMstPortIdWidth > AxiSlvPortIdWidth) begin : gen_upsize
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
  end else begin : gen_passthrough
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
    if (AxiSlvPortMaxUniqIds <= 2**AxiMstPortIdWidth) begin
      assert(AxiSlvPortMaxTxnsPerId > 32'd0)
        else $fatal(1, "Parameter AxiSlvPortMaxTxnsPerId has to be larger than 0!");
    end else begin
      assert(AxiMstPortMaxUniqIds > 32'd0)
        else $fatal(1, "Parameter AxiMstPortMaxUniqIds has to be larger than 0!");
      assert(AxiMstPortMaxTxnsPerId > 32'd0)
        else $fatal(1, "Parameter AxiMstPortMaxTxnsPerId has to be larger than 0!");
    end
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
    .AxiSlvPortIdWidth      ( AXI_SLV_PORT_ID_WIDTH         ),
    .AxiMstPortIdWidth      ( AXI_MST_PORT_ID_WIDTH         ),
    .AxiSlvPortMaxUniqIds   ( AXI_SLV_PORT_MAX_UNIQ_IDS     ),
    .AxiSlvPortMaxTxnsPerId ( AXI_SLV_PORT_MAX_TXNS_PER_ID  ),
    .AxiSlvPortMaxTxns      ( AXI_SLV_PORT_MAX_TXNS         ),
    .AxiMstPortMaxUniqIds   ( AXI_MST_PORT_MAX_UNIQ_IDS     ),
    .AxiMstPortMaxTxnsPerId ( AXI_MST_PORT_MAX_TXNS_PER_ID  ),
    .AxiAddrWidth           ( AXI_ADDR_WIDTH                ),
    .AxiDataWidth           ( AXI_DATA_WIDTH                ),
    .AxiUserWidth           ( AXI_USER_WIDTH                ),
    .slv_req_t              ( slv_req_t                     ),
    .slv_resp_t             ( slv_resp_t                    ),
    .mst_req_t              ( mst_req_t                     ),
    .mst_resp_t             ( mst_resp_t                    )
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

/// Flat ports variant of [`axi_iw_converter`](module.axi_iw_converter).
///
/// See the documentation of the main module for the definition of ports and parameters.
module axi_iw_converter_flat #(
  parameter int unsigned AXI_SLV_PORT_ID_WIDTH = 32'd0,
  parameter int unsigned AXI_MST_PORT_ID_WIDTH = 32'd0,
  parameter int unsigned AXI_SLV_PORT_MAX_UNIQ_IDS = 32'd0,
  parameter int unsigned AXI_SLV_PORT_MAX_TXNS_PER_ID = 32'd0,
  parameter int unsigned AXI_SLV_PORT_MAX_TXNS = 32'd0,
  parameter int unsigned AXI_MST_PORT_MAX_UNIQ_IDS = 32'd0,
  parameter int unsigned AXI_MST_PORT_MAX_TXNS_PER_ID = 32'd0,
  parameter int unsigned AXI_ADDR_WIDTH = 32'd0,
  parameter int unsigned AXI_DATA_WIDTH = 32'd0,
  parameter int unsigned AXI_USER_WIDTH = 32'd0,
  /// Dependent parameter, DO NOT OVERRIDE!
  parameter type addr_t = logic [AXI_ADDR_WIDTH-1:0],
  /// Dependent parameter, DO NOT OVERRIDE!
  parameter type data_t = logic [AXI_DATA_WIDTH-1:0],
  /// Dependent parameter, DO NOT OVERRIDE!
  parameter type slv_port_id_t = logic [AXI_SLV_PORT_ID_WIDTH-1:0],
  /// Dependent parameter, DO NOT OVERRIDE!
  parameter type mst_port_id_t = logic [AXI_MST_PORT_ID_WIDTH-1:0],
  /// Dependent parameter, DO NOT OVERRIDE!
  parameter type strb_t = logic [AXI_DATA_WIDTH/8-1:0],
  /// Dependent parameter, DO NOT OVERRIDE!
  parameter type user_t = logic [AXI_USER_WIDTH-1:0]
) (
  input  logic              clk_i,
  input  logic              rst_ni,

  input  slv_port_id_t      slv_aw_id_i,
  input  addr_t             slv_aw_addr_i,
  input  axi_pkg::len_t     slv_aw_len_i,
  input  axi_pkg::size_t    slv_aw_size_i,
  input  axi_pkg::burst_t   slv_aw_burst_i,
  input  logic              slv_aw_lock_i,
  input  axi_pkg::cache_t   slv_aw_cache_i,
  input  axi_pkg::prot_t    slv_aw_prot_i,
  input  axi_pkg::qos_t     slv_aw_qos_i,
  input  axi_pkg::region_t  slv_aw_region_i,
  input  axi_pkg::atop_t    slv_aw_atop_i,
  input  user_t             slv_aw_user_i,
  input  logic              slv_aw_valid_i,
  output logic              slv_aw_ready_o,
  input  data_t             slv_w_data_i,
  input  strb_t             slv_w_strb_i,
  input  logic              slv_w_last_i,
  input  user_t             slv_w_user_i,
  input  logic              slv_w_valid_i,
  output logic              slv_w_ready_o,
  output slv_port_id_t      slv_b_id_o,
  output axi_pkg::resp_t    slv_b_resp_o,
  output user_t             slv_b_user_o,
  output logic              slv_b_valid_o,
  input  logic              slv_b_ready_i,
  input  slv_port_id_t      slv_ar_id_i,
  input  addr_t             slv_ar_addr_i,
  input  axi_pkg::len_t     slv_ar_len_i,
  input  axi_pkg::size_t    slv_ar_size_i,
  input  axi_pkg::burst_t   slv_ar_burst_i,
  input  logic              slv_ar_lock_i,
  input  axi_pkg::cache_t   slv_ar_cache_i,
  input  axi_pkg::prot_t    slv_ar_prot_i,
  input  axi_pkg::qos_t     slv_ar_qos_i,
  input  axi_pkg::region_t  slv_ar_region_i,
  input  user_t             slv_ar_user_i,
  input  logic              slv_ar_valid_i,
  output logic              slv_ar_ready_o,
  output slv_port_id_t      slv_r_id_o,
  output data_t             slv_r_data_o,
  output axi_pkg::resp_t    slv_r_resp_o,
  output logic              slv_r_last_o,
  output user_t             slv_r_user_o,
  output logic              slv_r_valid_o,
  input  logic              slv_r_ready_i,

  output mst_port_id_t      mst_aw_id_o,
  output addr_t             mst_aw_addr_o,
  output axi_pkg::len_t     mst_aw_len_o,
  output axi_pkg::size_t    mst_aw_size_o,
  output axi_pkg::burst_t   mst_aw_burst_o,
  output logic              mst_aw_lock_o,
  output axi_pkg::cache_t   mst_aw_cache_o,
  output axi_pkg::prot_t    mst_aw_prot_o,
  output axi_pkg::qos_t     mst_aw_qos_o,
  output axi_pkg::region_t  mst_aw_region_o,
  output axi_pkg::atop_t    mst_aw_atop_o,
  output user_t             mst_aw_user_o,
  output logic              mst_aw_valid_o,
  input  logic              mst_aw_ready_i,
  output data_t             mst_w_data_o,
  output strb_t             mst_w_strb_o,
  output logic              mst_w_last_o,
  output user_t             mst_w_user_o,
  output logic              mst_w_valid_o,
  input  logic              mst_w_ready_i,
  input  mst_port_id_t      mst_b_id_i,
  input  axi_pkg::resp_t    mst_b_resp_i,
  input  user_t             mst_b_user_i,
  input  logic              mst_b_valid_i,
  output logic              mst_b_ready_o,
  output mst_port_id_t      mst_ar_id_o,
  output addr_t             mst_ar_addr_o,
  output axi_pkg::len_t     mst_ar_len_o,
  output axi_pkg::size_t    mst_ar_size_o,
  output axi_pkg::burst_t   mst_ar_burst_o,
  output logic              mst_ar_lock_o,
  output axi_pkg::cache_t   mst_ar_cache_o,
  output axi_pkg::prot_t    mst_ar_prot_o,
  output axi_pkg::qos_t     mst_ar_qos_o,
  output axi_pkg::region_t  mst_ar_region_o,
  output user_t             mst_ar_user_o,
  output logic              mst_ar_valid_o,
  input  logic              mst_ar_ready_i,
  input  mst_port_id_t      mst_r_id_i,
  input  data_t             mst_r_data_i,
  input  axi_pkg::resp_t    mst_r_resp_i,
  input  logic              mst_r_last_i,
  input  user_t             mst_r_user_i,
  input  logic              mst_r_valid_i,
  output logic              mst_r_ready_o
);

  AXI_BUS #(
    .AXI_ADDR_WIDTH (AXI_ADDR_WIDTH),
    .AXI_DATA_WIDTH (AXI_DATA_WIDTH),
    .AXI_ID_WIDTH   (AXI_SLV_PORT_ID_WIDTH),
    .AXI_USER_WIDTH (AXI_USER_WIDTH)
  ) slv ();
  assign slv.aw_id = slv_aw_id_i;
  assign slv.aw_addr = slv_aw_addr_i;
  assign slv.aw_len = slv_aw_len_i;
  assign slv.aw_size = slv_aw_size_i;
  assign slv.aw_burst = slv_aw_burst_i;
  assign slv.aw_lock = slv_aw_lock_i;
  assign slv.aw_cache = slv_aw_cache_i;
  assign slv.aw_prot = slv_aw_prot_i;
  assign slv.aw_qos = slv_aw_qos_i;
  assign slv.aw_region = slv_aw_region_i;
  assign slv.aw_atop = slv_aw_atop_i;
  assign slv.aw_user = slv_aw_user_i;
  assign slv.aw_valid = slv_aw_valid_i;
  assign slv_aw_ready_o = slv.aw_ready;
  assign slv.w_data = slv_w_data_i;
  assign slv.w_strb = slv_w_strb_i;
  assign slv.w_last = slv_w_last_i;
  assign slv.w_user = slv_w_user_i;
  assign slv.w_valid = slv_w_valid_i;
  assign slv_w_ready_o = slv.w_ready;
  assign slv_b_id_o = slv.b_id;
  assign slv_b_resp_o = slv.b_resp;
  assign slv_b_user_o = slv.b_user;
  assign slv_b_valid_o = slv.b_valid;
  assign slv.b_ready = slv_b_ready_i;
  assign slv.ar_id = slv_ar_id_i;
  assign slv.ar_addr = slv_ar_addr_i;
  assign slv.ar_len = slv_ar_len_i;
  assign slv.ar_size = slv_ar_size_i;
  assign slv.ar_burst = slv_ar_burst_i;
  assign slv.ar_lock = slv_ar_lock_i;
  assign slv.ar_cache = slv_ar_cache_i;
  assign slv.ar_prot = slv_ar_prot_i;
  assign slv.ar_qos = slv_ar_qos_i;
  assign slv.ar_region = slv_ar_region_i;
  assign slv.ar_user = slv_ar_user_i;
  assign slv.ar_valid = slv_ar_valid_i;
  assign slv_ar_ready_o = slv.ar_ready;
  assign slv_r_id_o = slv.r_id;
  assign slv_r_data_o = slv.r_data;
  assign slv_r_resp_o = slv.r_resp;
  assign slv_r_last_o = slv.r_last;
  assign slv_r_user_o = slv.r_user;
  assign slv_r_valid_o = slv.r_valid;
  assign slv.r_ready = slv_r_ready_i;

  AXI_BUS #(
    .AXI_ADDR_WIDTH (AXI_ADDR_WIDTH),
    .AXI_DATA_WIDTH (AXI_DATA_WIDTH),
    .AXI_ID_WIDTH   (AXI_MST_PORT_ID_WIDTH),
    .AXI_USER_WIDTH (AXI_USER_WIDTH)
  ) mst ();
  assign mst_aw_id_o = mst.aw_id;
  assign mst_aw_addr_o = mst.aw_addr;
  assign mst_aw_len_o = mst.aw_len;
  assign mst_aw_size_o = mst.aw_size;
  assign mst_aw_burst_o = mst.aw_burst;
  assign mst_aw_lock_o = mst.aw_lock;
  assign mst_aw_cache_o = mst.aw_cache;
  assign mst_aw_prot_o = mst.aw_prot;
  assign mst_aw_qos_o = mst.aw_qos;
  assign mst_aw_region_o = mst.aw_region;
  assign mst_aw_atop_o = mst.aw_atop;
  assign mst_aw_user_o = mst.aw_user;
  assign mst_aw_valid_o = mst.aw_valid;
  assign mst.aw_ready = mst_aw_ready_i;
  assign mst_w_data_o = mst.w_data;
  assign mst_w_strb_o = mst.w_strb;
  assign mst_w_last_o = mst.w_last;
  assign mst_w_user_o = mst.w_user;
  assign mst_w_valid_o = mst.w_valid;
  assign mst.w_ready = mst_w_ready_i;
  assign mst.b_id = mst_b_id_i;
  assign mst.b_resp = mst_b_resp_i;
  assign mst.b_user = mst_b_user_i;
  assign mst.b_valid = mst_b_valid_i;
  assign mst_b_ready_o = mst.b_ready;
  assign mst_ar_id_o = mst.ar_id;
  assign mst_ar_addr_o = mst.ar_addr;
  assign mst_ar_len_o = mst.ar_len;
  assign mst_ar_size_o = mst.ar_size;
  assign mst_ar_burst_o = mst.ar_burst;
  assign mst_ar_lock_o = mst.ar_lock;
  assign mst_ar_cache_o = mst.ar_cache;
  assign mst_ar_prot_o = mst.ar_prot;
  assign mst_ar_qos_o = mst.ar_qos;
  assign mst_ar_region_o = mst.ar_region;
  assign mst_ar_user_o = mst.ar_user;
  assign mst_ar_valid_o = mst.ar_valid;
  assign mst.ar_ready = mst_ar_ready_i;
  assign mst.r_id = mst_r_id_i;
  assign mst.r_data = mst_r_data_i;
  assign mst.r_resp = mst_r_resp_i;
  assign mst.r_last = mst_r_last_i;
  assign mst.r_user = mst_r_user_i;
  assign mst.r_valid = mst_r_valid_i;
  assign mst_r_ready_o = mst.r_ready;

  axi_iw_converter_intf #(
    .AXI_SLV_PORT_ID_WIDTH        (AXI_SLV_PORT_ID_WIDTH),
    .AXI_MST_PORT_ID_WIDTH        (AXI_MST_PORT_ID_WIDTH),
    .AXI_SLV_PORT_MAX_UNIQ_IDS    (AXI_SLV_PORT_MAX_UNIQ_IDS),
    .AXI_SLV_PORT_MAX_TXNS_PER_ID (AXI_SLV_PORT_MAX_TXNS_PER_ID),
    .AXI_SLV_PORT_MAX_TXNS        (AXI_SLV_PORT_MAX_TXNS),
    .AXI_MST_PORT_MAX_UNIQ_IDS    (AXI_MST_PORT_MAX_UNIQ_IDS),
    .AXI_MST_PORT_MAX_TXNS_PER_ID (AXI_MST_PORT_MAX_TXNS_PER_ID),
    .AXI_ADDR_WIDTH               (AXI_ADDR_WIDTH),
    .AXI_DATA_WIDTH               (AXI_DATA_WIDTH),
    .AXI_USER_WIDTH               (AXI_USER_WIDTH)
  ) i_resize (
    .clk_i,
    .rst_ni,
    .slv  (slv),
    .mst  (mst)
  );

endmodule
