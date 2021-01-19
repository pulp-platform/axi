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
// - Wolfgang Roenninger <wroennin@iis.ee.ethz.ch>

/// Downsize the AXI ID width.
`include "axi/typedef.svh"
module axi_iw_downsizer #(
  /// Number of IDs that should be active on the master port side.
  /// E.G.: If chosen as 32'd3 ther will be the IDs: `0`, `1`, `2`.
  /// This has to satisfy: `$clog2(NumIds) <= AxiIdWidthMst`
  parameter int unsigned NumIds         = 32'd0,
  /// Maximum number of transactions in flight
  parameter int unsigned MaxTrans       = 32'd0,
  /// AXI4+ATOP address width
  parameter int unsigned AxiAddrWidth   = 32'd0,
  /// AXI4+ATOP data width
  parameter int unsigned AxiDataWidth   = 32'd0,
  /// AXI4+ATOP user width
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
  // Width of the SLV ID that matters for routing
  localparam int unsigned SelectWidth = (NumIds > 32'd1) ? $clog2(NumIds)      : 32'd1;
  localparam int unsigned MuxIdWidth  = (NumIds > 32'd1) ? SelectWidth + 32'd1 : 32'd1;
  typedef logic [SelectWidth-1:0] select_t;

  typedef logic [0:0]                axi_id_one_t;
  typedef logic [MuxIdWidth-1:0]     axi_id_mux_t;
  typedef logic [AxiIdWidthMst-1:0]  axi_id_mst_t;
  typedef logic [AxiAddrWidth-1:0]   axi_addr_t;
  typedef logic [AxiDataWidth-1:0]   axi_data_t;
  typedef logic [AxiDataWidth/8-1:0] axi_strb_t;
  typedef logic [AxiUserWidth-1:0]   axi_user_t;

  `AXI_TYPEDEF_AW_CHAN_T(one_aw_chan_t, axi_addr_t, axi_id_one_t, axi_user_t)
  `AXI_TYPEDEF_W_CHAN_T(one_w_chan_t, axi_data_t, axi_strb_t, axi_user_t)
  `AXI_TYPEDEF_B_CHAN_T(one_b_chan_t, axi_id_one_t, axi_user_t)
  `AXI_TYPEDEF_AR_CHAN_T(one_ar_chan_t, axi_addr_t, axi_id_one_t, axi_user_t)
  `AXI_TYPEDEF_R_CHAN_T(one_r_chan_t, axi_data_t, axi_id_one_t, axi_user_t)
  `AXI_TYPEDEF_REQ_T(one_req_t, one_aw_chan_t, one_w_chan_t, one_ar_chan_t)
  `AXI_TYPEDEF_RESP_T(one_resp_t, one_b_chan_t, one_r_chan_t)

  `AXI_TYPEDEF_AW_CHAN_T(mux_aw_chan_t, axi_addr_t, axi_id_mux_t, axi_user_t)
  `AXI_TYPEDEF_W_CHAN_T(mux_w_chan_t, axi_data_t, axi_strb_t, axi_user_t)
  `AXI_TYPEDEF_B_CHAN_T(mux_b_chan_t, axi_id_mux_t, axi_user_t)
  `AXI_TYPEDEF_AR_CHAN_T(mux_ar_chan_t, axi_addr_t, axi_id_mux_t, axi_user_t)
  `AXI_TYPEDEF_R_CHAN_T(mux_r_chan_t, axi_data_t, axi_id_mux_t, axi_user_t)
  `AXI_TYPEDEF_REQ_T(mux_req_t, mux_aw_chan_t, mux_w_chan_t, mux_ar_chan_t)
  `AXI_TYPEDEF_RESP_T(mux_resp_t, mux_b_chan_t, mux_r_chan_t)

  select_t slv_aw_select, slv_ar_select;
  assign slv_aw_select = select_t'(slv_req_i.aw.id % NumIds);
  assign slv_ar_select = select_t'(slv_req_i.ar.id % NumIds);

  slv_req_t  [NumIds-1:0] to_serializer_reqs;
  slv_resp_t [NumIds-1:0] to_serializer_resps;

  axi_demux #(
    .AxiIdWidth  ( AxiIdWidthSlv  ),
    .aw_chan_t   ( slv_aw_chan_t  ),
    .w_chan_t    ( slv_w_chan_t   ),
    .b_chan_t    ( slv_b_chan_t   ),
    .ar_chan_t   ( slv_ar_chan_t  ),
    .r_chan_t    ( slv_r_chan_t   ),
    .req_t       ( slv_req_t      ),
    .resp_t      ( slv_resp_t     ),
    .NoMstPorts  ( NumIds         ),
    .MaxTrans    ( MaxTrans       ),
    .AxiLookBits ( AxiIdWidthSlv  ),
    .FallThrough ( 1'b1           ),
    .SpillAw     ( 1'b1           ),
    .SpillW      ( 1'b0           ),
    .SpillB      ( 1'b0           ),
    .SpillAr     ( 1'b1           ),
    .SpillR      ( 1'b0           )
  ) i_axi_demux(
    .clk_i,
    .rst_ni,
    .test_i          ( 1'b0                ),
    .slv_req_i       ( slv_req_i           ),
    .slv_aw_select_i ( slv_aw_select       ),
    .slv_ar_select_i ( slv_ar_select       ),
    .slv_resp_o      ( slv_resp_o          ),
    .mst_reqs_o      ( to_serializer_reqs  ),
    .mst_resps_i     ( to_serializer_resps )
  );

  one_req_t  [NumIds-1:0] from_serializer_reqs;
  one_resp_t [NumIds-1:0] from_serializer_resps;

  for (genvar i = 0; i < NumIds; i++) begin : gen_serializer

    slv_req_t  serializer_req;
    slv_resp_t serializer_resp;

    axi_serializer #(
      .MaxReadTxns  ( MaxTrans      ),
      .MaxWriteTxns ( MaxTrans      ),
      .AxiIdWidth   ( AxiIdWidthSlv ),
      .req_t        ( slv_req_t     ),
      .resp_t       ( slv_resp_t    )
    ) i_axi_serializer (
      .clk_i,
      .rst_ni,
      .slv_req_i  ( to_serializer_reqs[i]  ),
      .slv_resp_o ( to_serializer_resps[i] ),
      .mst_req_o  ( serializer_req         ),
      .mst_resp_i ( serializer_resp        )
    );
    // Truncate to ID width 1 as all requests have ID '0.
    assign from_serializer_reqs[i] = '{
      aw: '{
        id:     serializer_req.aw.id[0],
        addr:   serializer_req.aw.addr,
        len:    serializer_req.aw.len,
        size:   serializer_req.aw.size,
        burst:  serializer_req.aw.burst,
        lock:   serializer_req.aw.lock,
        cache:  serializer_req.aw.cache,
        prot:   serializer_req.aw.prot,
        qos:    serializer_req.aw.qos,
        region: serializer_req.aw.region,
        atop:   serializer_req.aw.atop,
        user:   serializer_req.aw.user
      },
      aw_valid: serializer_req.aw_valid,
      w:        serializer_req.w,
      w_valid:  serializer_req.w_valid,
      b_ready:  serializer_req.b_ready,
      ar: '{
        id:     serializer_req.ar.id[0],
        addr:   serializer_req.ar.addr,
        len:    serializer_req.ar.len,
        size:   serializer_req.ar.size,
        burst:  serializer_req.ar.burst,
        lock:   serializer_req.ar.lock,
        cache:  serializer_req.ar.cache,
        prot:   serializer_req.ar.prot,
        qos:    serializer_req.ar.qos,
        region: serializer_req.ar.region,
        user:   serializer_req.ar.user
      },
      ar_valid: serializer_req.ar_valid,
      r_ready:  serializer_req.r_ready
    };
    assign serializer_resp = '{
      aw_ready: from_serializer_resps[i].aw_ready,
      w_ready:  from_serializer_resps[i].w_ready,
      b: '{
        id:   from_serializer_resps[i].b.id,
        resp: from_serializer_resps[i].b.resp,
        user: from_serializer_resps[i].b.user,
        default: '0
      },
      b_valid:  from_serializer_resps[i].b_valid,
      ar_ready: from_serializer_resps[i].ar_ready,
      r: '{
        id:   from_serializer_resps[i].r.id,
        data: from_serializer_resps[i].r.data,
        resp: from_serializer_resps[i].r.resp,
        last: from_serializer_resps[i].r.last,
        user: from_serializer_resps[i].r.user,
        default: '0
      },
      r_valid:  from_serializer_resps[i].r_valid,
      default: '0
    };
  end

  mux_req_t  axi_mux_req;
  mux_resp_t axi_mux_resp;

  axi_mux #(
    .SlvAxiIDWidth ( 32'd1         ),
    .slv_aw_chan_t ( one_aw_chan_t ),
    .mst_aw_chan_t ( mux_aw_chan_t ),
    .w_chan_t      ( one_w_chan_t  ),
    .slv_b_chan_t  ( one_b_chan_t  ),
    .mst_b_chan_t  ( mux_b_chan_t  ),
    .slv_ar_chan_t ( one_ar_chan_t ),
    .mst_ar_chan_t ( mux_ar_chan_t ),
    .slv_r_chan_t  ( one_r_chan_t  ),
    .mst_r_chan_t  ( mux_r_chan_t  ),
    .slv_req_t     ( one_req_t     ),
    .slv_resp_t    ( one_resp_t    ),
    .mst_req_t     ( mux_req_t     ),
    .mst_resp_t    ( mux_resp_t    ),
    .NoSlvPorts    ( NumIds        ),
    .MaxWTrans     ( MaxTrans      ),
    .FallThrough   ( 1'b0          ),
    .SpillAw       ( 1'b1          ),
    .SpillW        ( 1'b0          ),
    .SpillB        ( 1'b0          ),
    .SpillAr       ( 1'b1          ),
    .SpillR        ( 1'b0          )
  ) i_axi_mux (
    .clk_i,
    .rst_ni,
    .test_i      ( 1'b0        ),
    .slv_reqs_i  ( from_serializer_reqs  ),
    .slv_resps_o ( from_serializer_resps ),
    .mst_req_o   ( axi_mux_req           ),
    .mst_resp_i  ( axi_mux_resp          )
  );

  // Shift the ID one down if needed, as mux prepends ID's
  if (MuxIdWidth > 32'd1) begin : gen_id_shift
    assign mst_req_o = '{
      aw: '{
        id:     axi_id_mst_t'(axi_mux_req.aw.id >> 32'd1),
        addr:   axi_mux_req.aw.addr,
        len:    axi_mux_req.aw.len,
        size:   axi_mux_req.aw.size,
        burst:  axi_mux_req.aw.burst,
        lock:   axi_mux_req.aw.lock,
        cache:  axi_mux_req.aw.cache,
        prot:   axi_mux_req.aw.prot,
        qos:    axi_mux_req.aw.qos,
        region: axi_mux_req.aw.region,
        atop:   axi_mux_req.aw.atop,
        user:   axi_mux_req.aw.user
      },
      aw_valid: axi_mux_req.aw_valid,
      w:        axi_mux_req.w,
      w_valid:  axi_mux_req.w_valid,
      b_ready:  axi_mux_req.b_ready,
      ar: '{
        id:     axi_id_mst_t'(axi_mux_req.ar.id >> 32'd1),
        addr:   axi_mux_req.ar.addr,
        len:    axi_mux_req.ar.len,
        size:   axi_mux_req.ar.size,
        burst:  axi_mux_req.ar.burst,
        lock:   axi_mux_req.ar.lock,
        cache:  axi_mux_req.ar.cache,
        prot:   axi_mux_req.ar.prot,
        qos:    axi_mux_req.ar.qos,
        region: axi_mux_req.ar.region,
        user:   axi_mux_req.ar.user
      },
      ar_valid: axi_mux_req.ar_valid,
      r_ready:  axi_mux_req.r_ready,
      default:  '0
    };
    assign axi_mux_resp = '{
      aw_ready: mst_resp_i.aw_ready,
      w_ready:  mst_resp_i.w_ready,
      b: '{
        id:   axi_id_mux_t'(mst_resp_i.b.id << 32'd1),
        resp: mst_resp_i.b.resp,
        user: mst_resp_i.b.user,
        default: '0
      },
      b_valid:  mst_resp_i.b_valid,
      ar_ready: mst_resp_i.ar_ready,
      r: '{
        id:   axi_id_mux_t'(mst_resp_i.r.id << 32'd1),
        data: mst_resp_i.r.data,
        resp: mst_resp_i.r.resp,
        last: mst_resp_i.r.last,
        user: mst_resp_i.r.user,
        default: '0
      },
      r_valid:  mst_resp_i.r_valid,
      default: '0
    };
  end else begin : gen_no_id_shift
    axi_id_prepend #(
      .NoBus             ( 32'd1         ),
      .AxiIdWidthSlvPort ( MuxIdWidth    ),
      .AxiIdWidthMstPort ( AxiIdWidthMst ),
      .slv_aw_chan_t     ( mux_aw_chan_t ),
      .slv_w_chan_t      ( mux_w_chan_t  ),
      .slv_b_chan_t      ( mux_b_chan_t  ),
      .slv_ar_chan_t     ( mux_ar_chan_t ),
      .slv_r_chan_t      ( mux_r_chan_t  ),
      .mst_aw_chan_t     ( mst_aw_chan_t ),
      .mst_w_chan_t      ( mst_w_chan_t  ),
      .mst_b_chan_t      ( mst_b_chan_t  ),
      .mst_ar_chan_t     ( mst_ar_chan_t ),
      .mst_r_chan_t      ( mst_r_chan_t  )
    ) i_axi_id_prepend (
      .pre_id_i         ( '0                    ),
      .slv_aw_chans_i   ( axi_mux_req.aw        ),
      .slv_aw_valids_i  ( axi_mux_req.aw_valid  ),
      .slv_aw_readies_o ( axi_mux_resp.aw_ready ),
      .slv_w_chans_i    ( axi_mux_req.w         ),
      .slv_w_valids_i   ( axi_mux_req.w_valid   ),
      .slv_w_readies_o  ( axi_mux_resp.w_ready  ),
      .slv_b_chans_o    ( axi_mux_resp.b        ),
      .slv_b_valids_o   ( axi_mux_resp.b_valid  ),
      .slv_b_readies_i  ( axi_mux_req.b_ready   ),
      .slv_ar_chans_i   ( axi_mux_req.ar        ),
      .slv_ar_valids_i  ( axi_mux_req.ar_valid  ),
      .slv_ar_readies_o ( axi_mux_resp.ar_ready ),
      .slv_r_chans_o    ( axi_mux_resp.r        ),
      .slv_r_valids_o   ( axi_mux_resp.r_valid  ),
      .slv_r_readies_i  ( axi_mux_req.r_ready   ),
      .mst_aw_chans_o   ( mst_req_o.aw          ),
      .mst_aw_valids_o  ( mst_req_o.aw_valid    ),
      .mst_aw_readies_i ( mst_resp_i.aw_ready   ),
      .mst_w_chans_o    ( mst_req_o.w           ),
      .mst_w_valids_o   ( mst_req_o.w_valid     ),
      .mst_w_readies_i  ( mst_resp_i.w_ready    ),
      .mst_b_chans_i    ( mst_resp_i.b          ),
      .mst_b_valids_i   ( mst_resp_i.b_valid    ),
      .mst_b_readies_o  ( mst_req_o.b_ready     ),
      .mst_ar_chans_o   ( mst_req_o.ar          ),
      .mst_ar_valids_o  ( mst_req_o.ar_valid    ),
      .mst_ar_readies_i ( mst_resp_i.ar_ready   ),
      .mst_r_chans_i    ( mst_resp_i.r          ),
      .mst_r_valids_i   ( mst_resp_i.r_valid    ),
      .mst_r_readies_o  ( mst_req_o.r_ready     )
    );
  end

  // pragma translate_off
  `ifndef VERILATOR
  initial begin : p_assert
    assert(NumIds > 32'd0)
      else $fatal(1, "NumIds has to be > 0.");
    assert(2**(AxiIdWidthMst) >= NumIds)
      else $fatal(1, "Not enought Id width on MST port to map all ID's.");
    assert(AxiIdWidthSlv > 32'd0)
      else $fatal(1, "Parameter AxiIdWidthSlv has to be larger than 0!");
    assert(AxiIdWidthMst > 32'd0)
      else $fatal(1, "Parameter AxiIdWidthMst has to be larger than 0!");
    assert(AxiIdWidthMst <= AxiIdWidthSlv)
      else $fatal(1, "Downsize implies that AxiIdWidthMst <= AxiIdWidthSlv!");
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
module axi_iw_downsizer_intf #(
  /// Number of IDs that should be active on the master port side.
  /// E.G.: If chosen as 32'd3 ther will be the IDs: `0`, `1`, `2`.
  /// This has to satisfy: `$clog2(NumIds) <= AxiIdWidthMst`
  parameter int unsigned NUM_IDS          = 32'd0,
  /// Maximum number of transactions in flight
  parameter int unsigned MAX_TRANS        = 32'd0,
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

  axi_iw_downsizer #(
    .NumIds         ( NUM_IDS          ),
    .MaxTrans       ( MAX_TRANS        ),
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
  ) i_axi_iw_downsizer (
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
