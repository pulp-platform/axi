// Copyright (c) 2026 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

`include "axi/typedef.svh"

/// Flat-port wrapper for packaging [`axi_burst_splitter_gran`](module.axi_burst_splitter_gran) as
/// an AMD custom IP.
///
/// AMD Vivado IP Packager expects AXI4 interfaces to be exposed as individual scalar/vector ports
/// rather than SystemVerilog structs.  This wrapper exposes one AXI4 slave interface (`S_AXI`) and
/// one AXI4 master interface (`M_AXI`) with Vivado interface metadata and adapts them to the
/// request/response structs used by `axi_burst_splitter_gran` internally.
module axi_burst_splitter_gran_wrapper #(
  /// Maximum number of AXI read bursts outstanding at the same time.
  parameter int unsigned MAX_READ_TXNS   = 32'd2,
  /// Maximum number of AXI write bursts outstanding at the same time.
  parameter int unsigned MAX_WRITE_TXNS  = 32'd2,
  /// Internal ID queue bandwidth mode.
  parameter bit          FULL_BW         = 1'b0,
  /// Number of cuts through the internal multicut.
  parameter bit          CUT_PATH        = 1'b0,
  /// Disable checks and bypass unsupported transfers instead of returning an error.
  parameter bit          DISABLE_CHECKS  = 1'b0,
  /// AXI address width.
  parameter int unsigned AXI_ADDR_WIDTH  = 32'd32,
  /// AXI data width.
  parameter int unsigned AXI_DATA_WIDTH  = 32'd32,
  /// AXI ID width.
  parameter int unsigned AXI_ID_WIDTH    = 32'd1,
  /// AXI user signal width.
  parameter int unsigned AXI_USER_WIDTH  = 32'd1,
  parameter int unsigned LenWidth.       = 32'd8
) (
  (* X_INTERFACE_INFO = "xilinx.com:signal:clock:1.0 ACLK CLK" *)
  (* X_INTERFACE_PARAMETER = "ASSOCIATED_BUSIF S_AXI:M_AXI, ASSOCIATED_RESET aresetn" *)
  input  logic                              aclk,
  (* X_INTERFACE_INFO = "xilinx.com:signal:reset:1.0 ARESETN RST" *)
  (* X_INTERFACE_PARAMETER = "POLARITY ACTIVE_LOW" *)
  input  logic                              aresetn,

  /// Maximum burst length emitted by this splitter, encoded as AXI `AxLEN` (`0` means one beat).
  input  logic [LenWidth-1:0]      len_limit_i,

  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI AWID" *)
  input  logic [AXI_ID_WIDTH-1:0]           s_axi_awid,
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI AWADDR" *)
  input  logic [AXI_ADDR_WIDTH-1:0]         s_axi_awaddr,
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI AWLEN" *)
  input  logic [7:0]                        s_axi_awlen,
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI AWSIZE" *)
  input  logic [2:0]                        s_axi_awsize,
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI AWBURST" *)
  input  logic [1:0]                        s_axi_awburst,
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI AWLOCK" *)
  input  logic                              s_axi_awlock,
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI AWCACHE" *)
  input  logic [3:0]                        s_axi_awcache,
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI AWPROT" *)
  input  logic [2:0]                        s_axi_awprot,
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI AWQOS" *)
  input  logic [3:0]                        s_axi_awqos,
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI AWREGION" *)
  input  logic [3:0]                        s_axi_awregion,
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI AWUSER" *)
  input  logic [AXI_USER_WIDTH-1:0]         s_axi_awuser,
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI AWVALID" *)
  input  logic                              s_axi_awvalid,
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI AWREADY" *)
  output logic                              s_axi_awready,

  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI WDATA" *)
  input  logic [AXI_DATA_WIDTH-1:0]         s_axi_wdata,
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI WSTRB" *)
  input  logic [AXI_DATA_WIDTH/8-1:0]       s_axi_wstrb,
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI WLAST" *)
  input  logic                              s_axi_wlast,
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI WUSER" *)
  input  logic [AXI_USER_WIDTH-1:0]         s_axi_wuser,
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI WVALID" *)
  input  logic                              s_axi_wvalid,
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI WREADY" *)
  output logic                              s_axi_wready,

  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI BID" *)
  output logic [AXI_ID_WIDTH-1:0]           s_axi_bid,
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI BRESP" *)
  output logic [1:0]                        s_axi_bresp,
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI BUSER" *)
  output logic [AXI_USER_WIDTH-1:0]         s_axi_buser,
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI BVALID" *)
  output logic                              s_axi_bvalid,
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI BREADY" *)
  input  logic                              s_axi_bready,

  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI ARID" *)
  input  logic [AXI_ID_WIDTH-1:0]           s_axi_arid,
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI ARADDR" *)
  input  logic [AXI_ADDR_WIDTH-1:0]         s_axi_araddr,
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI ARLEN" *)
  input  logic [7:0]                        s_axi_arlen,
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI ARSIZE" *)
  input  logic [2:0]                        s_axi_arsize,
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI ARBURST" *)
  input  logic [1:0]                        s_axi_arburst,
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI ARLOCK" *)
  input  logic                              s_axi_arlock,
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI ARCACHE" *)
  input  logic [3:0]                        s_axi_arcache,
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI ARPROT" *)
  input  logic [2:0]                        s_axi_arprot,
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI ARQOS" *)
  input  logic [3:0]                        s_axi_arqos,
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI ARREGION" *)
  input  logic [3:0]                        s_axi_arregion,
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI ARUSER" *)
  input  logic [AXI_USER_WIDTH-1:0]         s_axi_aruser,
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI ARVALID" *)
  input  logic                              s_axi_arvalid,
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI ARREADY" *)
  output logic                              s_axi_arready,

  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI RID" *)
  output logic [AXI_ID_WIDTH-1:0]           s_axi_rid,
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI RDATA" *)
  output logic [AXI_DATA_WIDTH-1:0]         s_axi_rdata,
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI RRESP" *)
  output logic [1:0]                        s_axi_rresp,
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI RLAST" *)
  output logic                              s_axi_rlast,
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI RUSER" *)
  output logic [AXI_USER_WIDTH-1:0]         s_axi_ruser,
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI RVALID" *)
  output logic                              s_axi_rvalid,
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI RREADY" *)
  input  logic                              s_axi_rready,

  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI AWID" *)
  output logic [AXI_ID_WIDTH-1:0]           m_axi_awid,
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI AWADDR" *)
  output logic [AXI_ADDR_WIDTH-1:0]         m_axi_awaddr,
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI AWLEN" *)
  output logic [7:0]                        m_axi_awlen,
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI AWSIZE" *)
  output logic [2:0]                        m_axi_awsize,
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI AWBURST" *)
  output logic [1:0]                        m_axi_awburst,
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI AWLOCK" *)
  output logic                              m_axi_awlock,
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI AWCACHE" *)
  output logic [3:0]                        m_axi_awcache,
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI AWPROT" *)
  output logic [2:0]                        m_axi_awprot,
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI AWQOS" *)
  output logic [3:0]                        m_axi_awqos,
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI AWREGION" *)
  output logic [3:0]                        m_axi_awregion,
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI AWUSER" *)
  output logic [AXI_USER_WIDTH-1:0]         m_axi_awuser,
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI AWVALID" *)
  output logic                              m_axi_awvalid,
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI AWREADY" *)
  input  logic                              m_axi_awready,

  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI WDATA" *)
  output logic [AXI_DATA_WIDTH-1:0]         m_axi_wdata,
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI WSTRB" *)
  output logic [AXI_DATA_WIDTH/8-1:0]       m_axi_wstrb,
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI WLAST" *)
  output logic                              m_axi_wlast,
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI WUSER" *)
  output logic [AXI_USER_WIDTH-1:0]         m_axi_wuser,
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI WVALID" *)
  output logic                              m_axi_wvalid,
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI WREADY" *)
  input  logic                              m_axi_wready,

  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI BID" *)
  input  logic [AXI_ID_WIDTH-1:0]           m_axi_bid,
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI BRESP" *)
  input  logic [1:0]                        m_axi_bresp,
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI BUSER" *)
  input  logic [AXI_USER_WIDTH-1:0]         m_axi_buser,
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI BVALID" *)
  input  logic                              m_axi_bvalid,
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI BREADY" *)
  output logic                              m_axi_bready,

  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI ARID" *)
  output logic [AXI_ID_WIDTH-1:0]           m_axi_arid,
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI ARADDR" *)
  output logic [AXI_ADDR_WIDTH-1:0]         m_axi_araddr,
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI ARLEN" *)
  output logic [7:0]                        m_axi_arlen,
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI ARSIZE" *)
  output logic [2:0]                        m_axi_arsize,
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI ARBURST" *)
  output logic [1:0]                        m_axi_arburst,
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI ARLOCK" *)
  output logic                              m_axi_arlock,
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI ARCACHE" *)
  output logic [3:0]                        m_axi_arcache,
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI ARPROT" *)
  output logic [2:0]                        m_axi_arprot,
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI ARQOS" *)
  output logic [3:0]                        m_axi_arqos,
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI ARREGION" *)
  output logic [3:0]                        m_axi_arregion,
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI ARUSER" *)
  output logic [AXI_USER_WIDTH-1:0]         m_axi_aruser,
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI ARVALID" *)
  output logic                              m_axi_arvalid,
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI ARREADY" *)
  input  logic                              m_axi_arready,

  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI RID" *)
  input  logic [AXI_ID_WIDTH-1:0]           m_axi_rid,
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI RDATA" *)
  input  logic [AXI_DATA_WIDTH-1:0]         m_axi_rdata,
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI RRESP" *)
  input  logic [1:0]                        m_axi_rresp,
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI RLAST" *)
  input  logic                              m_axi_rlast,
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI RUSER" *)
  input  logic [AXI_USER_WIDTH-1:0]         m_axi_ruser,
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI RVALID" *)
  input  logic                              m_axi_rvalid,
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI RREADY" *)
  output logic                              m_axi_rready
);

  localparam int unsigned AXI_STRB_WIDTH = AXI_DATA_WIDTH / 32'd8;

  typedef logic [AXI_ADDR_WIDTH-1:0] addr_t;
  typedef logic [AXI_DATA_WIDTH-1:0] data_t;
  typedef logic [AXI_STRB_WIDTH-1:0] strb_t;
  typedef logic [AXI_ID_WIDTH-1:0]   id_t;
  typedef logic [AXI_USER_WIDTH-1:0] user_t;

  `AXI_TYPEDEF_AW_CHAN_T(axi_aw_chan_t, addr_t, id_t, user_t)
  `AXI_TYPEDEF_W_CHAN_T(axi_w_chan_t, data_t, strb_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T(axi_b_chan_t, id_t, user_t)
  `AXI_TYPEDEF_AR_CHAN_T(axi_ar_chan_t, addr_t, id_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(axi_r_chan_t, data_t, id_t, user_t)
  `AXI_TYPEDEF_REQ_T(axi_req_t, axi_aw_chan_t, axi_w_chan_t, axi_ar_chan_t)
  `AXI_TYPEDEF_RESP_T(axi_resp_t, axi_b_chan_t, axi_r_chan_t)

  axi_req_t  slv_req;
  axi_resp_t slv_resp;
  axi_req_t  mst_req;
  axi_resp_t mst_resp;

  assign slv_req.aw = axi_aw_chan_t'{
    id:     s_axi_awid,
    addr:   s_axi_awaddr,
    len:    s_axi_awlen,
    size:   s_axi_awsize,
    burst:  s_axi_awburst,
    lock:   s_axi_awlock,
    cache:  s_axi_awcache,
    prot:   s_axi_awprot,
    qos:    s_axi_awqos,
    region: s_axi_awregion,
    atop:   '0,
    user:   s_axi_awuser
  };
  assign slv_req.aw_valid = s_axi_awvalid;
  assign s_axi_awready    = slv_resp.aw_ready;

  assign slv_req.w = axi_w_chan_t'{
    data: s_axi_wdata,
    strb: s_axi_wstrb,
    last: s_axi_wlast,
    user: s_axi_wuser
  };
  assign slv_req.w_valid = s_axi_wvalid;
  assign s_axi_wready    = slv_resp.w_ready;

  assign s_axi_bid     = slv_resp.b.id;
  assign s_axi_bresp   = slv_resp.b.resp;
  assign s_axi_buser   = slv_resp.b.user;
  assign s_axi_bvalid  = slv_resp.b_valid;
  assign slv_req.b_ready = s_axi_bready;

  assign slv_req.ar = axi_ar_chan_t'{
    id:     s_axi_arid,
    addr:   s_axi_araddr,
    len:    s_axi_arlen,
    size:   s_axi_arsize,
    burst:  s_axi_arburst,
    lock:   s_axi_arlock,
    cache:  s_axi_arcache,
    prot:   s_axi_arprot,
    qos:    s_axi_arqos,
    region: s_axi_arregion,
    user:   s_axi_aruser
  };
  assign slv_req.ar_valid = s_axi_arvalid;
  assign s_axi_arready    = slv_resp.ar_ready;

  assign s_axi_rid     = slv_resp.r.id;
  assign s_axi_rdata   = slv_resp.r.data;
  assign s_axi_rresp   = slv_resp.r.resp;
  assign s_axi_rlast   = slv_resp.r.last;
  assign s_axi_ruser   = slv_resp.r.user;
  assign s_axi_rvalid  = slv_resp.r_valid;
  assign slv_req.r_ready = s_axi_rready;

  assign m_axi_awid     = mst_req.aw.id;
  assign m_axi_awaddr   = mst_req.aw.addr;
  assign m_axi_awlen    = mst_req.aw.len;
  assign m_axi_awsize   = mst_req.aw.size;
  assign m_axi_awburst  = mst_req.aw.burst;
  assign m_axi_awlock   = mst_req.aw.lock;
  assign m_axi_awcache  = mst_req.aw.cache;
  assign m_axi_awprot   = mst_req.aw.prot;
  assign m_axi_awqos    = mst_req.aw.qos;
  assign m_axi_awregion = mst_req.aw.region;
  assign m_axi_awuser   = mst_req.aw.user;
  assign m_axi_awvalid  = mst_req.aw_valid;
  assign mst_resp.aw_ready = m_axi_awready;

  assign m_axi_wdata    = mst_req.w.data;
  assign m_axi_wstrb    = mst_req.w.strb;
  assign m_axi_wlast    = mst_req.w.last;
  assign m_axi_wuser    = mst_req.w.user;
  assign m_axi_wvalid   = mst_req.w_valid;
  assign mst_resp.w_ready = m_axi_wready;

  assign mst_resp.b = axi_b_chan_t'{
    id:   m_axi_bid,
    resp: m_axi_bresp,
    user: m_axi_buser
  };
  assign mst_resp.b_valid = m_axi_bvalid;
  assign m_axi_bready     = mst_req.b_ready;

  assign m_axi_arid     = mst_req.ar.id;
  assign m_axi_araddr   = mst_req.ar.addr;
  assign m_axi_arlen    = mst_req.ar.len;
  assign m_axi_arsize   = mst_req.ar.size;
  assign m_axi_arburst  = mst_req.ar.burst;
  assign m_axi_arlock   = mst_req.ar.lock;
  assign m_axi_arcache  = mst_req.ar.cache;
  assign m_axi_arprot   = mst_req.ar.prot;
  assign m_axi_arqos    = mst_req.ar.qos;
  assign m_axi_arregion = mst_req.ar.region;
  assign m_axi_aruser   = mst_req.ar.user;
  assign m_axi_arvalid  = mst_req.ar_valid;
  assign mst_resp.ar_ready = m_axi_arready;

  assign mst_resp.r = axi_r_chan_t'{
    id:   m_axi_rid,
    data: m_axi_rdata,
    resp: m_axi_rresp,
    last: m_axi_rlast,
    user: m_axi_ruser
  };
  assign mst_resp.r_valid = m_axi_rvalid;
  assign m_axi_rready     = mst_req.r_ready;

  axi_burst_splitter_gran #(
    .MaxReadTxns   ( MAX_READ_TXNS  ),
    .MaxWriteTxns  ( MAX_WRITE_TXNS ),
    .FullBW        ( FULL_BW        ),
    .CutPath       ( CUT_PATH       ),
    .DisableChecks ( DISABLE_CHECKS ),
    .AddrWidth     ( AXI_ADDR_WIDTH ),
    .DataWidth     ( AXI_DATA_WIDTH ),
    .IdWidth       ( AXI_ID_WIDTH   ),
    .UserWidth     ( AXI_USER_WIDTH ),
    .axi_req_t     ( axi_req_t      ),
    .axi_resp_t    ( axi_resp_t     ),
    .axi_aw_chan_t ( axi_aw_chan_t  ),
    .axi_w_chan_t  ( axi_w_chan_t   ),
    .axi_b_chan_t  ( axi_b_chan_t   ),
    .axi_ar_chan_t ( axi_ar_chan_t  ),
    .axi_r_chan_t  ( axi_r_chan_t   )
  ) i_axi_burst_splitter_gran (
    .clk_i       ( aclk        ),
    .rst_ni      ( aresetn     ),
    .len_limit_i ( len_limit_i ),
    .slv_req_i   ( slv_req     ),
    .slv_resp_o  ( slv_resp    ),
    .mst_req_o   ( mst_req     ),
    .mst_resp_i  ( mst_resp    )
  );

  // Validate parameters.
  // pragma translate_off
  `ifndef VERILATOR
    initial begin: p_assertions
      assert (MAX_READ_TXNS > 32'd0) else
          $fatal(1, "MAX_READ_TXNS must be at least 1!");
      assert (MAX_WRITE_TXNS > 32'd0) else
          $fatal(1, "MAX_WRITE_TXNS must be at least 1!");
      assert (AXI_DATA_WIDTH % 32'd8 == 32'd0) else
          $fatal(1, "AXI_DATA_WIDTH must be a multiple of 8!");
      assert (AXI_ID_WIDTH > 32'd0) else
          $fatal(1, "AXI_ID_WIDTH must be at least 1 for flat IP ports!");
      assert (AXI_USER_WIDTH > 32'd0) else
          $fatal(1, "AXI_USER_WIDTH must be at least 1 for flat IP ports!");
    end
  `endif
  // pragma translate_on
endmodule
