// Copyright 2020 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Author: Matheus Cavalcante <matheusd@iis.ee.ethz.ch>

// NOTE: The upsizer/downsizer do not support WRAP and FIXED bursts, and
// will answer with SLVERR upon receiving a burst of such types.

module axi_dw_converter #(
    parameter int unsigned AxiMaxReads     = 1    , // Number of outstanding reads
    parameter int unsigned AxiMstDataWidth = 8    , // Master data width
    parameter int unsigned AxiSlvDataWidth = 8    , // Slave data width
    parameter int unsigned AxiAddrWidth    = 1    , // Address width
    parameter int unsigned AxiIdWidth      = 1    , // ID width
    parameter type aw_chan_t               = logic, // AW Channel Type
    parameter type mst_w_chan_t            = logic, //  W Channel Type for the mst port
    parameter type slv_w_chan_t            = logic, //  W Channel Type for the slv port
    parameter type b_chan_t                = logic, //  B Channel Type
    parameter type ar_chan_t               = logic, // AR Channel Type
    parameter type mst_r_chan_t            = logic, //  R Channel Type for the mst port
    parameter type slv_r_chan_t            = logic, //  R Channel Type for the slv port
    parameter type axi_mst_req_t           = logic, // AXI Request Type for mst ports
    parameter type axi_mst_resp_t          = logic, // AXI Response Type for mst ports
    parameter type axi_slv_req_t           = logic, // AXI Request Type for mst ports
    parameter type axi_slv_resp_t          = logic  // AXI Response Type for mst ports
  ) (
    input  logic          clk_i,
    input  logic          rst_ni,
    // Slave interface
    input  axi_slv_req_t  slv_req_i,
    output axi_slv_resp_t slv_resp_o,
    // Master interface
    output axi_mst_req_t  mst_req_o,
    input  axi_mst_resp_t mst_resp_i
  );

  if (AxiSlvDataWidth == AxiMstDataWidth) begin: gen_no_dw_conversion
    assign mst_req_o  = slv_req_i ;
    assign slv_resp_o = mst_resp_i;
  end : gen_no_dw_conversion

  if (AxiSlvDataWidth < AxiMstDataWidth) begin: gen_dw_upsize
    axi_dw_upsizer #(
      .AxiMaxReads    (AxiMaxReads    ),
      .AxiMstDataWidth(AxiMstDataWidth),
      .AxiSlvDataWidth(AxiSlvDataWidth),
      .AxiAddrWidth   (AxiAddrWidth   ),
      .AxiIdWidth     (AxiIdWidth     ),
      .aw_chan_t      (aw_chan_t      ),
      .mst_w_chan_t   (mst_w_chan_t   ),
      .slv_w_chan_t   (slv_w_chan_t   ),
      .b_chan_t       (b_chan_t       ),
      .ar_chan_t      (ar_chan_t      ),
      .mst_r_chan_t   (mst_r_chan_t   ),
      .slv_r_chan_t   (slv_r_chan_t   ),
      .axi_mst_req_t  (axi_mst_req_t  ),
      .axi_mst_resp_t (axi_mst_resp_t ),
      .axi_slv_req_t  (axi_slv_req_t  ),
      .axi_slv_resp_t (axi_slv_resp_t )
    ) i_axi_dw_upsizer (
      .clk_i     (clk_i     ),
      .rst_ni    (rst_ni    ),
      // Slave interface
      .slv_req_i (slv_req_i ),
      .slv_resp_o(slv_resp_o),
      // Master interface
      .mst_req_o (mst_req_o ),
      .mst_resp_i(mst_resp_i)
    );
  end : gen_dw_upsize

  if (AxiSlvDataWidth > AxiMstDataWidth) begin: gen_dw_downsize
    axi_dw_downsizer #(
      .AxiMaxReads    (AxiMaxReads    ),
      .AxiMstDataWidth(AxiMstDataWidth),
      .AxiSlvDataWidth(AxiSlvDataWidth),
      .AxiAddrWidth   (AxiAddrWidth   ),
      .AxiIdWidth     (AxiIdWidth     ),
      .aw_chan_t      (aw_chan_t      ),
      .mst_w_chan_t   (mst_w_chan_t   ),
      .slv_w_chan_t   (slv_w_chan_t   ),
      .b_chan_t       (b_chan_t       ),
      .ar_chan_t      (ar_chan_t      ),
      .mst_r_chan_t   (mst_r_chan_t   ),
      .slv_r_chan_t   (slv_r_chan_t   ),
      .axi_mst_req_t  (axi_mst_req_t  ),
      .axi_mst_resp_t (axi_mst_resp_t ),
      .axi_slv_req_t  (axi_slv_req_t  ),
      .axi_slv_resp_t (axi_slv_resp_t )
    ) i_axi_dw_downsizer (
      .clk_i     (clk_i     ),
      .rst_ni    (rst_ni    ),
      // Slave interface
      .slv_req_i (slv_req_i ),
      .slv_resp_o(slv_resp_o),
      // Master interface
      .mst_req_o (mst_req_o ),
      .mst_resp_i(mst_resp_i)
    );
  end : gen_dw_downsize

endmodule : axi_dw_converter
