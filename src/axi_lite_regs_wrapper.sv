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

/// Flat-port wrapper for packaging [`axi_lite_regs`](module.axi_lite_regs) as an AMD custom IP.
///
/// AMD Vivado IP Packager expects AXI4-Lite interfaces to be exposed as individual scalar/vector
/// ports rather than SystemVerilog structs or interfaces.  This wrapper keeps the AXI4-Lite bus and
/// register sideband signals flat, adds Vivado interface metadata, and adapts the ports to the
/// request/response structs used by `axi_lite_regs` internally.
module axi_lite_regs_wrapper #(
  /// The size of the register field in bytes.
  parameter int unsigned REG_NUM_BYTES  = 32'd32,
  /// Address width of the AXI4-Lite slave port.
  parameter int unsigned AXI_ADDR_WIDTH = 32'd32,
  /// Data width of the AXI4-Lite slave port.
  parameter int unsigned AXI_DATA_WIDTH = 32'd32,
  /// Only allow privileged accesses on the AXI4-Lite slave port.
  parameter bit          PRIV_PROT_ONLY = 1'b0,
  /// Only allow secure accesses on the AXI4-Lite slave port.
  parameter bit          SECU_PROT_ONLY = 1'b0,
  /// Define individual bytes as read-only from the AXI4-Lite slave port.
  parameter logic [REG_NUM_BYTES-1:0] AXI_READ_ONLY = {REG_NUM_BYTES{1'b0}},
  /// Reset value for the register array, byte 0 in bits [7:0].
  parameter logic [REG_NUM_BYTES*8-1:0] REG_RST_VAL = {REG_NUM_BYTES{8'h00}}
) (
  (* X_INTERFACE_INFO = "xilinx.com:signal:clock:1.0 S_AXI_ACLK CLK" *)
  (* X_INTERFACE_PARAMETER = "ASSOCIATED_BUSIF S_AXI, ASSOCIATED_RESET s_axi_aresetn" *)
  input  logic                             s_axi_aclk,
  (* X_INTERFACE_INFO = "xilinx.com:signal:reset:1.0 S_AXI_ARESETN RST" *)
  (* X_INTERFACE_PARAMETER = "POLARITY ACTIVE_LOW" *)
  input  logic                             s_axi_aresetn,

  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI AWADDR" *)
  input  logic [AXI_ADDR_WIDTH-1:0]        s_axi_awaddr,
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI AWPROT" *)
  input  logic [2:0]                       s_axi_awprot,
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI AWVALID" *)
  input  logic                             s_axi_awvalid,
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI AWREADY" *)
  output logic                             s_axi_awready,

  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI WDATA" *)
  input  logic [AXI_DATA_WIDTH-1:0]        s_axi_wdata,
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI WSTRB" *)
  input  logic [AXI_DATA_WIDTH/8-1:0]      s_axi_wstrb,
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI WVALID" *)
  input  logic                             s_axi_wvalid,
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI WREADY" *)
  output logic                             s_axi_wready,

  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI BRESP" *)
  output logic [1:0]                       s_axi_bresp,
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI BVALID" *)
  output logic                             s_axi_bvalid,
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI BREADY" *)
  input  logic                             s_axi_bready,

  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI ARADDR" *)
  input  logic [AXI_ADDR_WIDTH-1:0]        s_axi_araddr,
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI ARPROT" *)
  input  logic [2:0]                       s_axi_arprot,
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI ARVALID" *)
  input  logic                             s_axi_arvalid,
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI ARREADY" *)
  output logic                             s_axi_arready,

  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI RDATA" *)
  output logic [AXI_DATA_WIDTH-1:0]        s_axi_rdata,
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI RRESP" *)
  output logic [1:0]                       s_axi_rresp,
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI RVALID" *)
  output logic                             s_axi_rvalid,
  (* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI RREADY" *)
  input  logic                             s_axi_rready,

  /// Signals that a byte is being written from the AXI4-Lite port in the current clock cycle.
  output logic [REG_NUM_BYTES-1:0]         wr_active_o,
  /// Signals that a byte is being read from the AXI4-Lite port in the current clock cycle.
  output logic [REG_NUM_BYTES-1:0]         rd_active_o,
  /// Flattened input value of each byte, byte 0 in bits [7:0].
  input  logic [REG_NUM_BYTES*8-1:0]       reg_d_i,
  /// Load enable of each byte.
  input  logic [REG_NUM_BYTES-1:0]         reg_load_i,
  /// Flattened registered value of each byte, byte 0 in bits [7:0].
  output logic [REG_NUM_BYTES*8-1:0]       reg_q_o
);

  localparam int unsigned AXI_STRB_WIDTH = AXI_DATA_WIDTH / 32'd8;

  typedef logic [7:0]                         byte_t;
  typedef byte_t [REG_NUM_BYTES-1:0]          byte_array_t;
  typedef logic [AXI_ADDR_WIDTH-1:0]          addr_t;
  typedef logic [AXI_DATA_WIDTH-1:0]          data_t;
  typedef logic [AXI_STRB_WIDTH-1:0]          strb_t;

  function automatic byte_array_t unpack_bytes(input logic [REG_NUM_BYTES*8-1:0] flat_i);
    for (int unsigned i = 0; i < REG_NUM_BYTES; i++) begin
      unpack_bytes[i] = flat_i[8*i+:8];
    end
  endfunction

  localparam byte_array_t REG_RST_VAL_UNPACKED = unpack_bytes(REG_RST_VAL);

  `AXI_LITE_TYPEDEF_AW_CHAN_T(aw_chan_lite_t, addr_t)
  `AXI_LITE_TYPEDEF_W_CHAN_T(w_chan_lite_t, data_t, strb_t)
  `AXI_LITE_TYPEDEF_B_CHAN_T(b_chan_lite_t)
  `AXI_LITE_TYPEDEF_AR_CHAN_T(ar_chan_lite_t, addr_t)
  `AXI_LITE_TYPEDEF_R_CHAN_T(r_chan_lite_t, data_t)
  `AXI_LITE_TYPEDEF_REQ_T(req_lite_t, aw_chan_lite_t, w_chan_lite_t, ar_chan_lite_t)
  `AXI_LITE_TYPEDEF_RESP_T(resp_lite_t, b_chan_lite_t, r_chan_lite_t)

  req_lite_t    axi_req;
  resp_lite_t   axi_resp;
  byte_array_t  reg_d;
  byte_array_t  reg_q;

  assign axi_req.aw.addr  = s_axi_awaddr;
  assign axi_req.aw.prot  = s_axi_awprot;
  assign axi_req.aw_valid = s_axi_awvalid;
  assign s_axi_awready    = axi_resp.aw_ready;

  assign axi_req.w.data   = s_axi_wdata;
  assign axi_req.w.strb   = s_axi_wstrb;
  assign axi_req.w_valid  = s_axi_wvalid;
  assign s_axi_wready     = axi_resp.w_ready;

  assign s_axi_bresp      = axi_resp.b.resp;
  assign s_axi_bvalid     = axi_resp.b_valid;
  assign axi_req.b_ready  = s_axi_bready;

  assign axi_req.ar.addr  = s_axi_araddr;
  assign axi_req.ar.prot  = s_axi_arprot;
  assign axi_req.ar_valid = s_axi_arvalid;
  assign s_axi_arready    = axi_resp.ar_ready;

  assign s_axi_rdata      = axi_resp.r.data;
  assign s_axi_rresp      = axi_resp.r.resp;
  assign s_axi_rvalid     = axi_resp.r_valid;
  assign axi_req.r_ready  = s_axi_rready;

  for (genvar i = 0; i < REG_NUM_BYTES; i++) begin : gen_reg_flatten
    assign reg_d[i]          = reg_d_i[8*i+:8];
    assign reg_q_o[8*i+:8]   = reg_q[i];
  end

  axi_lite_regs #(
    .RegNumBytes  ( REG_NUM_BYTES          ),
    .AxiAddrWidth ( AXI_ADDR_WIDTH         ),
    .AxiDataWidth ( AXI_DATA_WIDTH         ),
    .PrivProtOnly ( PRIV_PROT_ONLY         ),
    .SecuProtOnly ( SECU_PROT_ONLY         ),
    .AxiReadOnly  ( AXI_READ_ONLY          ),
    .RegRstVal    ( REG_RST_VAL_UNPACKED   ),
    .req_lite_t   ( req_lite_t             ),
    .resp_lite_t  ( resp_lite_t            )
  ) i_axi_lite_regs (
    .clk_i       ( s_axi_aclk    ),
    .rst_ni      ( s_axi_aresetn ),
    .axi_req_i   ( axi_req       ),
    .axi_resp_o  ( axi_resp      ),
    .wr_active_o ( wr_active_o   ),
    .rd_active_o ( rd_active_o   ),
    .reg_d_i     ( reg_d         ),
    .reg_load_i  ( reg_load_i    ),
    .reg_q_o     ( reg_q         )
  );

  // Validate parameters.
  // pragma translate_off
  `ifndef VERILATOR
    initial begin: p_assertions
      assert (REG_NUM_BYTES > 32'd0) else
          $fatal(1, "REG_NUM_BYTES must be at least 1!");
      assert (AXI_DATA_WIDTH % 32'd8 == 32'd0) else
          $fatal(1, "AXI_DATA_WIDTH must be a multiple of 8!");
      assert (AXI_STRB_WIDTH > 32'd0) else
          $fatal(1, "AXI_DATA_WIDTH must provide at least one byte lane!");
    end
  `endif
  // pragma translate_on
endmodule
