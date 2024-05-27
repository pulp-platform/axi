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
// - Paul Scheffler <paulsc@iis.ee.ethz.ch>
// - Michael Rogenmoser <michaero@iis.ee.ethz.ch>

`include "axi/assign.svh"
`include "axi/typedef.svh"

/// Reduce AXI IDs by serializing transactions when necessary.
///
/// This module is designed to remap a wide ID space to an arbitrarily narrow ID space.  If
/// necessary, this module maps two different IDs at its slave port to the same ID at its master
/// port, thereby constraining the order of those transactions and in this sense *serializing* them.
/// If the independence of IDs needs to be retained at the cost of a wider ID space at the master
/// port, use [`axi_id_remap`](module.axi_id_remap) instead.
///
/// This module contains one [`axi_serializer`](module.axi_serializer) per master port ID (given by
/// the `AxiMstPortMaxUniqIds parameter`).
module axi_id_serialize #(
  /// ID width of the AXI4+ATOP slave port
  parameter int unsigned AxiSlvPortIdWidth = 32'd0,
  /// ID width of the AXI4+ATOP master port
  parameter int unsigned AxiMstPortIdWidth = 32'd0,
  /// Maximum number of different IDs that can be in flight at the master port.  Reads and writes
  /// are counted separately (except for ATOPs, which count as both read and write).
  ///
  /// The maximum value of this parameter is `2**AxiMstPortIdWidth`.
  parameter int unsigned AxiMstPortMaxUniqIds = 32'd0,
  /// Maximum number of in-flight transactions with the same ID at the master port.
  parameter int unsigned AxiMstPortMaxTxnsPerId = 32'd0,
  /// Address width of both AXI4+ATOP ports
  parameter int unsigned AxiAddrWidth = 32'd0,
  /// User width of both AXI4+ATOP ports
  parameter int unsigned AxiUserWidth = 32'd0,
  /// Request struct type of the AXI4+ATOP slave port
  parameter type slv_req_t = logic,
  /// Response struct type of the AXI4+ATOP slave port
  parameter type slv_resp_t = logic,
  /// Request struct type of the AXI4+ATOP master port
  parameter type mst_req_t = logic,
  /// Response struct type of the AXI4+ATOP master port
  parameter type mst_resp_t = logic,
  /// A custom offset (modulo `AxiMstPortMaxUniqIds`, ignored for input IDs remapped through
  /// `IdMap`) for the assigned output IDs.
  parameter int unsigned MstIdBaseOffset = 32'd0,
  /// Explicit input-output ID map. If an input ID `id` does not appear in this mapping (default),
  /// it is simply mapped to the output ID `id % AxiMstPortMaxUniqIds`. If `id` appears in more
  /// than one entry, it is matched to the *last* matching entry's output ID.
  /// Number of Entries in the explicit ID map (default: None)
  parameter int unsigned IdMapNumEntries = 32'd0,
  /// Explicit ID map; index [0] in each entry is the input ID to match, index [1] the output ID.
  parameter int unsigned IdMap [IdMapNumEntries-1:0][0:1] = '{default: {32'b0, 32'b0}},
  /// Spill AR and AW
  parameter bit          SpillAx = 1'b1,
  // unused parameters, no longer needed, left for backwards-compatibility
  parameter int unsigned AxiSlvPortMaxTxns = 32'd0, // unused
  parameter int unsigned AxiDataWidth = 32'd0,
  parameter bit          AtopSupport  = 1'b1
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

  /// Number of bits of the slave port ID that determine the mapping to the master port ID
  localparam int unsigned SelectWidth = cf_math_pkg::idx_width(AxiMstPortMaxUniqIds);
  /// Slice of slave port IDs that determines the master port ID
  typedef logic [SelectWidth-1:0] select_t;

  /// ID at the master port
  typedef logic [AxiMstPortIdWidth-1:0] mst_id_t;
   /// Address in any AXI channel
  typedef logic [AxiAddrWidth-1:0]      addr_t;
  /// User signal in any AXI channel
  typedef logic [AxiUserWidth-1:0]      user_t;

  /// AW channel at master port
  `AXI_TYPEDEF_AW_CHAN_T(mst_aw_t, addr_t, mst_id_t, user_t)
  /// AR channel at master port
  `AXI_TYPEDEF_AR_CHAN_T(mst_ar_t, addr_t, mst_id_t, user_t)

  /// Type for slave ID map
  typedef mst_id_t [2**AxiSlvPortIdWidth-1:0] slv_id_map_t;

  /// Resolve target output ID for each possible input ID as a parameter
  function automatic slv_id_map_t map_slv_ids();
    slv_id_map_t ret = '0;
    // Populate output with default mapping, including `MstIdBaseOffset`
    for (int unsigned i = 0; i < 2**AxiSlvPortIdWidth; ++i)
      ret[i] = (i + MstIdBaseOffset) % AxiMstPortMaxUniqIds;
    // For each explicitly mapped input ID, set the desired output ID
    for (int unsigned i = 0; i < IdMapNumEntries; ++i)
      ret[IdMap[i][0]] = IdMap[i][1];
    return ret;
  endfunction

  /// Input-to-output ID map used
  localparam slv_id_map_t SlvIdMap = map_slv_ids();

  select_t slv_aw_select, slv_ar_select, slv_b_select, slv_r_select;
  assign slv_aw_select = select_t'(SlvIdMap[slv_req_i.aw.id]);
  assign slv_ar_select = select_t'(SlvIdMap[slv_req_i.ar.id]);

  slv_req_t  [AxiMstPortMaxUniqIds-1:0] to_serializer_reqs;
  slv_resp_t [AxiMstPortMaxUniqIds-1:0] to_serializer_resps;

  logic [AxiMstPortMaxUniqIds-1:0] to_serializer_resps_b_valid,
                                   to_serializer_resps_r_valid;

  onehot_to_bin #(
    .ONEHOT_WIDTH( AxiMstPortMaxUniqIds )
  ) i_slv_b_select (
    .onehot(to_serializer_resps_b_valid),
    .bin   (slv_b_select)
  );

  onehot_to_bin #(
    .ONEHOT_WIDTH( AxiMstPortMaxUniqIds )
  ) i_slv_r_select (
    .onehot(to_serializer_resps_r_valid),
    .bin   (slv_r_select)
  );

  for (genvar i = 0; i < AxiMstPortMaxUniqIds; i++) begin
    assign to_serializer_resps_b_valid[i] = to_serializer_resps[i].b_valid;
    assign to_serializer_resps_r_valid[i] = to_serializer_resps[i].r_valid;
  end

  // Due to static ID mapping, ID consistency checking is not needed.
  always_comb begin
    // AW, W, AR
    for (int unsigned i = 0; i < AxiMstPortMaxUniqIds; i++) begin
      to_serializer_reqs[i] = slv_req_i; // .aw, .w, .ar
      to_serializer_reqs[i].aw_valid = '0;
      to_serializer_reqs[i].w_valid = '0;
      to_serializer_reqs[i].ar_valid = '0;
    end
    to_serializer_reqs[slv_aw_select].aw_valid = slv_req_i.aw_valid;
    slv_resp_o.aw_ready = to_serializer_resps[slv_aw_select].aw_ready;

    slv_resp_o.w_ready = mst_resp_i.w_ready;

    to_serializer_reqs[slv_ar_select].ar_valid = slv_req_i.ar_valid;
    slv_resp_o.ar_ready = to_serializer_resps[slv_ar_select].ar_ready;

    // B, R (these are passed through or both gated inside the serializer)
    slv_resp_o.b_valid = |to_serializer_resps_b_valid;
    slv_resp_o.b = to_serializer_resps[slv_b_select].b;
    slv_resp_o.r_valid = |to_serializer_resps_r_valid;
    slv_resp_o.r = to_serializer_resps[slv_r_select].r;
    for (int unsigned i = 0; i < AxiMstPortMaxUniqIds; i++) begin
      to_serializer_reqs[i].b_ready = slv_req_i.b_ready;
      to_serializer_reqs[i].r_ready = slv_req_i.r_ready;
    end
  end

  slv_req_t  [AxiMstPortMaxUniqIds-1:0] tmp_serializer_reqs;
  slv_resp_t [AxiMstPortMaxUniqIds-1:0] tmp_serializer_resps;
  mst_req_t  [AxiMstPortMaxUniqIds-1:0] from_serializer_reqs;
  mst_resp_t [AxiMstPortMaxUniqIds-1:0] from_serializer_resps;

  for (genvar i = 0; i < AxiMstPortMaxUniqIds; i++) begin : gen_serializers
    // serializer takes care to ensure unique IDs for ATOPs
    axi_serializer #(
      .MaxReadTxns  ( AxiMstPortMaxTxnsPerId  ),
      .MaxWriteTxns ( AxiMstPortMaxTxnsPerId  ),
      .AxiIdWidth   ( AxiSlvPortIdWidth       ),
      .axi_req_t    ( slv_req_t               ),
      .axi_resp_t   ( slv_resp_t              )
    ) i_axi_serializer (
      .clk_i,
      .rst_ni,
      .slv_req_i  ( to_serializer_reqs[i]   ),
      .slv_resp_o ( to_serializer_resps[i]  ),
      .mst_req_o  ( tmp_serializer_reqs[i]  ),
      .mst_resp_i ( tmp_serializer_resps[i] )
    );
    always_comb begin
      `AXI_SET_REQ_STRUCT(from_serializer_reqs[i], tmp_serializer_reqs[i])
      from_serializer_reqs[i].aw.id = i;
      from_serializer_reqs[i].ar.id = i;
      `AXI_SET_RESP_STRUCT(tmp_serializer_resps[i], from_serializer_resps[i])
      // Zero-extend response IDs.
      tmp_serializer_resps[i].b.id = '0;
      tmp_serializer_resps[i].r.id = '0;
    end
  end

  logic [AxiMstPortMaxUniqIds-1:0] from_serializer_reqs_aw_valid,
                                   from_serializer_reqs_ar_valid,
                                   from_serializer_reqs_b_ready,
                                   from_serializer_reqs_r_ready;

  select_t mst_aw_select, mst_ar_select;

  onehot_to_bin #(
    .ONEHOT_WIDTH( AxiMstPortMaxUniqIds )
  ) i_mst_aw_select (
    .onehot(from_serializer_reqs_aw_valid),
    .bin   (mst_aw_select)
  );

  onehot_to_bin #(
    .ONEHOT_WIDTH( AxiMstPortMaxUniqIds )
  ) i_mst_ar_select (
    .onehot(from_serializer_reqs_ar_valid),
    .bin   (mst_ar_select)
  );

  for (genvar i = 0; i < AxiMstPortMaxUniqIds; i++) begin
    assign from_serializer_reqs_aw_valid[i] = from_serializer_reqs[i].aw_valid;
    assign from_serializer_reqs_ar_valid[i] = from_serializer_reqs[i].ar_valid;
  end

  mst_req_t mst_req;
  logic mst_aw_ready, mst_ar_ready;

  always_comb begin
    mst_req.aw_valid = |from_serializer_reqs_aw_valid;
    mst_req.aw = from_serializer_reqs[mst_aw_select].aw;
    mst_req.w_valid = slv_req_i.w_valid;
    mst_req.w = slv_req_i.w;
    mst_req.ar_valid = |from_serializer_reqs_ar_valid;
    mst_req.ar = from_serializer_reqs[mst_ar_select].ar;
    for (int unsigned i = 0; i < AxiMstPortMaxUniqIds; i++) begin
      from_serializer_resps[i].aw_ready = mst_aw_ready;
      from_serializer_resps[i].ar_ready = mst_ar_ready;
    end

    for (int unsigned i = 0; i < AxiMstPortMaxUniqIds; i++) begin
      from_serializer_reqs_b_ready[i] = from_serializer_reqs[i].b_ready;
      from_serializer_reqs_r_ready[i] = from_serializer_reqs[i].r_ready;
      from_serializer_resps[i].b_valid = '0;
      from_serializer_resps[i].r_valid = '0;
      from_serializer_resps[i].b = mst_resp_i.b;
      from_serializer_resps[i].r = mst_resp_i.r;
    end
    from_serializer_resps[mst_resp_i.b.id].b_valid = mst_resp_i.b_valid;
    mst_req.b_ready = from_serializer_reqs[mst_resp_i.b.id].b_ready;
    from_serializer_resps[mst_resp_i.r.id].r_valid = mst_resp_i.r_valid;
    mst_req.r_ready = from_serializer_reqs[mst_resp_i.r.id].r_ready;
  end

  spill_register #(
    .T     ( mst_aw_t ),
    .Bypass( ~SpillAx )
  ) i_aw_spill_reg (
    .clk_i,
    .rst_ni,
    .valid_i( mst_req.aw_valid ),
    .ready_o( mst_aw_ready ),
    .data_i ( mst_req.aw),
    .valid_o( mst_req_o.aw_valid ),
    .ready_i( mst_resp_i.aw_ready ),
    .data_o ( mst_req_o.aw )
  );

  spill_register #(
    .T     ( mst_ar_t ),
    .Bypass( ~SpillAx )
  ) i_ar_spill_reg (
    .clk_i,
    .rst_ni,
    .valid_i( mst_req.ar_valid ),
    .ready_o( mst_ar_ready ),
    .data_i ( mst_req.ar ),
    .valid_o( mst_req_o.ar_valid ),
    .ready_i( mst_resp_i.ar_ready ),
    .data_o ( mst_req_o.ar )
  );

  `AXI_ASSIGN_W_STRUCT(mst_req_o.w, mst_req.w)
  assign mst_req_o.w_valid = mst_req.w_valid;
  assign mst_req_o.b_ready = mst_req.b_ready;
  assign mst_req_o.r_ready = mst_req.r_ready;

  // pragma translate_off
  `ifndef VERILATOR
  initial begin : p_assert
    assert(AxiMstPortMaxUniqIds > 32'd0)
      else $fatal(1, "AxiMstPortMaxUniqIds has to be > 0.");
    assert(2**(AxiMstPortIdWidth) >= AxiMstPortMaxUniqIds)
      else $fatal(1, "Not enought Id width on MST port to map all ID's.");
    assert(AxiSlvPortIdWidth > 32'd0)
      else $fatal(1, "Parameter AxiSlvPortIdWidth has to be larger than 0!");
    assert(AxiMstPortIdWidth)
      else $fatal(1, "Parameter AxiMstPortIdWidth has to be larger than 0!");
    assert(AxiMstPortIdWidth <= AxiSlvPortIdWidth)
      else $fatal(1, "Downsize implies that AxiMstPortIdWidth <= AxiSlvPortIdWidth!");
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


/// Interface variant of [`axi_id_serialize`](module.axi_id_serialize).
///
/// See the documentation of the main module for the definition of ports and parameters.
module axi_id_serialize_intf #(
  parameter int unsigned AXI_SLV_PORT_ID_WIDTH = 32'd0,
  parameter int unsigned AXI_SLV_PORT_MAX_TXNS = 32'd0,
  parameter int unsigned AXI_MST_PORT_ID_WIDTH = 32'd0,
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
  typedef logic [AXI_ADDR_WIDTH-1:0]        addr_t;
  typedef logic [AXI_DATA_WIDTH-1:0]        data_t;
  typedef logic [AXI_DATA_WIDTH/8-1:0]      strb_t;
  typedef logic [AXI_USER_WIDTH-1:0]        user_t;

  `AXI_TYPEDEF_AW_CHAN_T(slv_aw_t, addr_t, slv_id_t, user_t)
  `AXI_TYPEDEF_W_CHAN_T(w_t, data_t, strb_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T(slv_b_t, slv_id_t, user_t)
  `AXI_TYPEDEF_AR_CHAN_T(slv_ar_t, addr_t, slv_id_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(slv_r_t, data_t, slv_id_t, user_t)
  `AXI_TYPEDEF_REQ_T(slv_req_t, slv_aw_t, w_t, slv_ar_t)
  `AXI_TYPEDEF_RESP_T(slv_resp_t, slv_b_t, slv_r_t)

  `AXI_TYPEDEF_AW_CHAN_T(mst_aw_t, addr_t, mst_id_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T(mst_b_t, mst_id_t, user_t)
  `AXI_TYPEDEF_AR_CHAN_T(mst_ar_t, addr_t, mst_id_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(mst_r_t, data_t, mst_id_t, user_t)
  `AXI_TYPEDEF_REQ_T(mst_req_t, mst_aw_t, w_t, mst_ar_t)
  `AXI_TYPEDEF_RESP_T(mst_resp_t, mst_b_t, mst_r_t)

  slv_req_t  slv_req;
  slv_resp_t slv_resp;
  mst_req_t  mst_req;
  mst_resp_t mst_resp;

  `AXI_ASSIGN_TO_REQ(slv_req, slv)
  `AXI_ASSIGN_FROM_RESP(slv, slv_resp)
  `AXI_ASSIGN_FROM_REQ(mst, mst_req)
  `AXI_ASSIGN_TO_RESP(mst_resp, mst)

  axi_id_serialize #(
    .AxiSlvPortIdWidth      ( AXI_SLV_PORT_ID_WIDTH         ),
    .AxiSlvPortMaxTxns      ( AXI_SLV_PORT_MAX_TXNS         ),
    .AxiMstPortIdWidth      ( AXI_MST_PORT_ID_WIDTH         ),
    .AxiMstPortMaxUniqIds   ( AXI_MST_PORT_MAX_UNIQ_IDS     ),
    .AxiMstPortMaxTxnsPerId ( AXI_MST_PORT_MAX_TXNS_PER_ID  ),
    .AxiAddrWidth           ( AXI_ADDR_WIDTH                ),
    .AxiDataWidth           ( AXI_DATA_WIDTH                ),
    .AxiUserWidth           ( AXI_USER_WIDTH                ),
    .slv_req_t              ( slv_req_t                     ),
    .slv_resp_t             ( slv_resp_t                    ),
    .mst_req_t              ( mst_req_t                     ),
    .mst_resp_t             ( mst_resp_t                    )
  ) i_axi_id_serialize (
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
