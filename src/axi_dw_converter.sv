// Copyright 2020 ETH Zurich and University of Bologna.
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
// - Matheus Cavalcante <matheusd@iis.ee.ethz.ch>

// NOTE: The upsizer does not support WRAP bursts, and will answer with SLVERR
// upon receiving a burst of such type. In addition to that, the downsizer also
// does not support FIXED bursts with incoming axlen != 0.

module axi_dw_converter #(
    parameter int unsigned MaxReads         = 1    , // Number of outstanding reads
    parameter int unsigned SbrPortDataWidth = 8    , // Data width of the sbr port
    parameter int unsigned MgrPortDataWidth = 8    , // Data width of the mgr port
    parameter int unsigned AddrWidth        = 1    , // Address width
    parameter int unsigned IdWidth          = 1    , // ID width
    parameter type aw_chan_t                = logic, // AW Channel Type
    parameter type mgr_w_chan_t             = logic, //  W Channel Type for the mgr port
    parameter type sbr_w_chan_t             = logic, //  W Channel Type for the sbr port
    parameter type b_chan_t                 = logic, //  B Channel Type
    parameter type ar_chan_t                = logic, // AR Channel Type
    parameter type mgr_r_chan_t             = logic, //  R Channel Type for the mgr port
    parameter type sbr_r_chan_t             = logic, //  R Channel Type for the sbr port
    parameter type mgr_port_axi_req_t       = logic, // AXI Request Type for mgr ports
    parameter type mgr_port_axi_rsp_t       = logic, // AXI Response Type for mgr ports
    parameter type sbr_port_axi_req_t       = logic, // AXI Request Type for sbr ports
    parameter type sbr_port_axi_rsp_t       = logic  // AXI Response Type for sbr ports
  ) (
    input  logic              clk_i,
    input  logic              rst_ni,
    // Subordinate interface
    input  sbr_port_axi_req_t sbr_port_req_i,
    output sbr_port_axi_rsp_t sbr_port_rsp_o,
    // Manager interface
    output mgr_port_axi_req_t mgr_port_req_o,
    input  mgr_port_axi_rsp_t mgr_port_rsp_i
  );

  if (MgrPortDataWidth == SbrPortDataWidth) begin: gen_no_dw_conversion
    assign mgr_port_req_o = sbr_port_req_i ;
    assign sbr_port_rsp_o = mgr_port_rsp_i;
  end : gen_no_dw_conversion

  if (MgrPortDataWidth > SbrPortDataWidth) begin: gen_dw_upsize
    axi_dw_upsizer #(
      .MaxReads           (MaxReads        ),
      .SbrPortDataWidth   (SbrPortDataWidth),
      .MgrPortDataWidth   (MgrPortDataWidth),
      .AddrWidth          (AddrWidth       ),
      .IdWidth            (IdWidth         ),
      .aw_chan_t          (aw_chan_t          ),
      .mgr_w_chan_t       (mgr_w_chan_t       ),
      .sbr_w_chan_t       (sbr_w_chan_t       ),
      .b_chan_t           (b_chan_t           ),
      .ar_chan_t          (ar_chan_t          ),
      .mgr_r_chan_t       (mgr_r_chan_t       ),
      .sbr_r_chan_t       (sbr_r_chan_t       ),
      .mgr_port_axi_req_t (mgr_port_axi_req_t ),
      .mgr_port_axi_rsp_t (mgr_port_axi_rsp_t ),
      .sbr_port_axi_req_t (sbr_port_axi_req_t ),
      .sbr_port_axi_rsp_t (sbr_port_axi_rsp_t )
    ) i_axi_dw_upsizer (
      .clk_i     (clk_i    ),
      .rst_ni    (rst_ni   ),
      // Subordinate interface
      .sbr_port_req_i (sbr_port_req_i),
      .sbr_port_rsp_o (sbr_port_rsp_o),
      // Manager interface
      .mgr_port_req_o (mgr_port_req_o),
      .mgr_port_rsp_i (mgr_port_rsp_i)
    );
  end : gen_dw_upsize

  if (MgrPortDataWidth < SbrPortDataWidth) begin: gen_dw_downsize
    axi_dw_downsizer #(
      .MaxReads           (MaxReads        ),
      .SbrPortDataWidth   (SbrPortDataWidth),
      .MgrPortDataWidth   (MgrPortDataWidth),
      .AddrWidth          (AddrWidth       ),
      .IdWidth            (IdWidth         ),
      .aw_chan_t          (aw_chan_t          ),
      .mgr_w_chan_t       (mgr_w_chan_t       ),
      .sbr_w_chan_t       (sbr_w_chan_t       ),
      .b_chan_t           (b_chan_t           ),
      .ar_chan_t          (ar_chan_t          ),
      .mgr_r_chan_t       (mgr_r_chan_t       ),
      .sbr_r_chan_t       (sbr_r_chan_t       ),
      .mgr_port_axi_req_t (mgr_port_axi_req_t ),
      .mgr_port_axi_rsp_t (mgr_port_axi_rsp_t ),
      .sbr_port_axi_req_t (sbr_port_axi_req_t ),
      .sbr_port_axi_rsp_t (sbr_port_axi_rsp_t )
    ) i_axi_dw_downsizer (
      .clk_i     (clk_i    ),
      .rst_ni    (rst_ni   ),
      // Subordinate interface
      .sbr_port_req_i (sbr_port_req_i),
      .sbr_port_rsp_o (sbr_port_rsp_o),
      // Manager interface
      .mgr_port_req_o (mgr_port_req_o),
      .mgr_port_rsp_i (mgr_port_rsp_i)
    );
  end : gen_dw_downsize

endmodule : axi_dw_converter

// Interface wrapper

`include "axi/assign.svh"
`include "axi/typedef.svh"

module axi_dw_converter_intf #(
    parameter int unsigned AXI_ID_WIDTH            = 1,
    parameter int unsigned AXI_ADDR_WIDTH          = 1,
    parameter int unsigned AXI_SBR_PORT_DATA_WIDTH = 8,
    parameter int unsigned AXI_MGR_PORT_DATA_WIDTH = 8,
    parameter int unsigned AXI_USER_WIDTH          = 0,
    parameter int unsigned AXI_MAX_READS           = 8
  ) (
    input          logic clk_i,
    input          logic rst_ni,
    AXI_BUS.Subordinate        sbr,
    AXI_BUS.Manager       mgr
  );

  typedef logic [AXI_ID_WIDTH-1:0] id_t                   ;
  typedef logic [AXI_ADDR_WIDTH-1:0] addr_t               ;
  typedef logic [AXI_MGR_PORT_DATA_WIDTH-1:0] mgr_data_t  ;
  typedef logic [AXI_MGR_PORT_DATA_WIDTH/8-1:0] mgr_strb_t;
  typedef logic [AXI_SBR_PORT_DATA_WIDTH-1:0] sbr_data_t  ;
  typedef logic [AXI_SBR_PORT_DATA_WIDTH/8-1:0] sbr_strb_t;
  typedef logic [AXI_USER_WIDTH-1:0] user_t               ;
  `AXI_TYPEDEF_AW_CHAN_T(aw_chan_t, addr_t, id_t, user_t)
  `AXI_TYPEDEF_W_CHAN_T(mgr_w_chan_t, mgr_data_t, mgr_strb_t, user_t)
  `AXI_TYPEDEF_W_CHAN_T(sbr_w_chan_t, sbr_data_t, sbr_strb_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T(b_chan_t, id_t, user_t)
  `AXI_TYPEDEF_AR_CHAN_T(ar_chan_t, addr_t, id_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(mgr_r_chan_t, mgr_data_t, id_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(sbr_r_chan_t, sbr_data_t, id_t, user_t)
  `AXI_TYPEDEF_REQ_T(mgr_port_axi_req_t, aw_chan_t, mgr_w_chan_t, ar_chan_t)
  `AXI_TYPEDEF_RSP_T(mgr_port_axi_rsp_t, b_chan_t, mgr_r_chan_t)
  `AXI_TYPEDEF_REQ_T(sbr_port_axi_req_t, aw_chan_t, sbr_w_chan_t, ar_chan_t)
  `AXI_TYPEDEF_RSP_T(sbr_port_axi_rsp_t, b_chan_t, sbr_r_chan_t)

  sbr_port_axi_req_t sbr_req;
  sbr_port_axi_rsp_t sbr_rsp;
  mgr_port_axi_req_t mgr_req;
  mgr_port_axi_rsp_t mgr_rsp;

  `AXI_ASSIGN_TO_REQ(sbr_req, sbr)
  `AXI_ASSIGN_FROM_RSP(sbr, sbr_rsp)

  `AXI_ASSIGN_FROM_REQ(mgr, mgr_req)
  `AXI_ASSIGN_TO_RSP(mgr_rsp, mgr)

  axi_dw_converter #(
    .MaxReads           ( AXI_MAX_READS           ),
    .SbrPortDataWidth   ( AXI_SBR_PORT_DATA_WIDTH ),
    .MgrPortDataWidth   ( AXI_MGR_PORT_DATA_WIDTH ),
    .AddrWidth          ( AXI_ADDR_WIDTH          ),
    .IdWidth            ( AXI_ID_WIDTH            ),
    .aw_chan_t          ( aw_chan_t               ),
    .mgr_w_chan_t       ( mgr_w_chan_t            ),
    .sbr_w_chan_t       ( sbr_w_chan_t            ),
    .b_chan_t           ( b_chan_t                ),
    .ar_chan_t          ( ar_chan_t               ),
    .mgr_r_chan_t       ( mgr_r_chan_t            ),
    .sbr_r_chan_t       ( sbr_r_chan_t            ),
    .mgr_port_axi_req_t ( mgr_port_axi_req_t               ),
    .mgr_port_axi_rsp_t ( mgr_port_axi_rsp_t               ),
    .sbr_port_axi_req_t ( sbr_port_axi_req_t               ),
    .sbr_port_axi_rsp_t ( sbr_port_axi_rsp_t               )
  ) i_axi_dw_converter (
    .clk_i      ( clk_i    ),
    .rst_ni     ( rst_ni   ),
    // subordinate port
    .sbr_port_req_i  ( sbr_req  ),
    .sbr_port_rsp_o ( sbr_rsp ),
    // manager port
    .mgr_port_req_o  ( mgr_req  ),
    .mgr_port_rsp_i ( mgr_rsp )
  );

endmodule : axi_dw_converter_intf
