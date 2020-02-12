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

module axi_dw_converter #(
    parameter int unsigned AxiMaxReads = 1    , // Number of outstanding reads
    parameter type aw_chan_t           = logic, // AW Channel Type
    parameter type mst_w_chan_t        = logic, //  W Channel Type for mst port
    parameter type slv_w_chan_t        = logic, //  W Channel Type for slv port
    parameter type b_chan_t            = logic, //  B Channel Type
    parameter type ar_chan_t           = logic, // AR Channel Type
    parameter type mst_r_chan_t        = logic, //  R Channel Type for mst port
    parameter type slv_r_chan_t        = logic  //  R Channel Type for slv port
  ) (
    input  logic        clk_i,
    input  logic        rst_ni,
    // Slave interface
    input  aw_chan_t    slv_aw_i,
    input  logic        slv_aw_valid_i,
    output logic        slv_aw_ready_o,
    input  slv_w_chan_t slv_w_i,
    input  logic        slv_w_valid_i,
    output logic        slv_w_ready_o,
    output b_chan_t     slv_b_o,
    output logic        slv_b_valid_o,
    input  logic        slv_b_ready_i,
    input  ar_chan_t    slv_ar_i,
    input  logic        slv_ar_valid_i,
    output logic        slv_ar_ready_o,
    output slv_r_chan_t slv_r_o,
    output logic        slv_r_valid_o,
    input  logic        slv_r_ready_i,
    // Master interface
    output aw_chan_t    mst_aw_o,
    output logic        mst_aw_valid_o,
    input  logic        mst_aw_ready_i,
    output mst_w_chan_t mst_w_o,
    output logic        mst_w_valid_o,
    input  logic        mst_w_ready_i,
    input  b_chan_t     mst_b_i,
    input  logic        mst_b_valid_i,
    output logic        mst_b_ready_o,
    output ar_chan_t    mst_ar_o,
    output logic        mst_ar_valid_o,
    input  logic        mst_ar_ready_i,
    input  mst_r_chan_t mst_r_i,
    input  logic        mst_r_valid_i,
    output logic        mst_r_ready_o
  );

  if ($bits(slv_r_o.data) == $bits(mst_r_i.data)) begin: gen_no_dw_conversion
    assign mst_aw_o       = slv_aw_i      ;
    assign mst_aw_valid_o = slv_aw_i      ;
    assign slv_aw_ready_o = mst_aw_ready_i;
    assign mst_w_o        = slv_w_i       ;
    assign mst_w_valid_o  = slv_w_i       ;
    assign slv_w_ready_o  = mst_w_ready_i ;
    assign slv_b_o        = mst_b_i       ;
    assign slv_b_valid_o  = mst_b_valid_i ;
    assign mst_b_ready_o  = slv_b_ready_i ;
    assign mst_ar_o       = slv_ar_i      ;
    assign mst_ar_valid_o = slv_ar_i      ;
    assign slv_ar_ready_o = mst_ar_ready_i;
    assign slv_r_o        = mst_r_i       ;
    assign slv_r_valid_o  = mst_r_valid_i ;
    assign mst_r_ready_o  = slv_r_ready_i ;
  end : gen_no_dw_conversion

  if ($bits(slv_r_o.data) < $bits(mst_r_i.data)) begin: gen_dw_upsize
    axi_dw_upsizer #(
      .AxiMaxReads (AxiMaxReads ),
      .aw_chan_t   (aw_chan_t   ),
      .mst_w_chan_t(mst_w_chan_t),
      .slv_w_chan_t(slv_w_chan_t),
      .b_chan_t    (b_chan_t    ),
      .ar_chan_t   (ar_chan_t   ),
      .mst_r_chan_t(mst_r_chan_t),
      .slv_r_chan_t(slv_r_chan_t)
    ) i_axi_dw_upsizer (
      .clk_i         (clk_i         ),
      .rst_ni        (rst_ni        ),
      // Slave interface
      .slv_aw_i      (slv_aw_i      ),
      .slv_aw_valid_i(slv_aw_valid_i),
      .slv_aw_ready_o(slv_aw_ready_o),
      .slv_w_i       (slv_w_i       ),
      .slv_w_valid_i (slv_w_valid_i ),
      .slv_w_ready_o (slv_w_ready_o ),
      .slv_b_o       (slv_b_o       ),
      .slv_b_valid_o (slv_b_valid_o ),
      .slv_b_ready_i (slv_b_ready_i ),
      .slv_ar_i      (slv_ar_i      ),
      .slv_ar_valid_i(slv_ar_valid_i),
      .slv_ar_ready_o(slv_ar_ready_o),
      .slv_r_o       (slv_r_o       ),
      .slv_r_valid_o (slv_r_valid_o ),
      .slv_r_ready_i (slv_r_ready_i ),
      // Master interface
      .mst_aw_o      (mst_aw_o      ),
      .mst_aw_valid_o(mst_aw_valid_o),
      .mst_aw_ready_i(mst_aw_ready_i),
      .mst_w_o       (mst_w_o       ),
      .mst_w_valid_o (mst_w_valid_o ),
      .mst_w_ready_i (mst_w_ready_i ),
      .mst_b_i       (mst_b_i       ),
      .mst_b_valid_i (mst_b_valid_i ),
      .mst_b_ready_o (mst_b_ready_o ),
      .mst_ar_o      (mst_ar_o      ),
      .mst_ar_valid_o(mst_ar_valid_o),
      .mst_ar_ready_i(mst_ar_ready_i),
      .mst_r_i       (mst_r_i       ),
      .mst_r_valid_i (mst_r_valid_i ),
      .mst_r_ready_o (mst_r_ready_o )
    );
  end : gen_dw_upsize

  if ($bits(slv_r_o.data) > $bits(mst_r_i.data)) begin: gen_dw_downsize
    axi_dw_downsizer #(
      .AxiMaxReads (AxiMaxReads ),
      .aw_chan_t   (aw_chan_t   ),
      .mst_w_chan_t(mst_w_chan_t),
      .slv_w_chan_t(slv_w_chan_t),
      .b_chan_t    (b_chan_t    ),
      .ar_chan_t   (ar_chan_t   ),
      .mst_r_chan_t(mst_r_chan_t),
      .slv_r_chan_t(slv_r_chan_t)
    ) i_axi_dw_downsizer (
      .clk_i         (clk_i         ),
      .rst_ni        (rst_ni        ),
      // Slave interface
      .slv_aw_i      (slv_aw_i      ),
      .slv_aw_valid_i(slv_aw_valid_i),
      .slv_aw_ready_o(slv_aw_ready_o),
      .slv_w_i       (slv_w_i       ),
      .slv_w_valid_i (slv_w_valid_i ),
      .slv_w_ready_o (slv_w_ready_o ),
      .slv_b_o       (slv_b_o       ),
      .slv_b_valid_o (slv_b_valid_o ),
      .slv_b_ready_i (slv_b_ready_i ),
      .slv_ar_i      (slv_ar_i      ),
      .slv_ar_valid_i(slv_ar_valid_i),
      .slv_ar_ready_o(slv_ar_ready_o),
      .slv_r_o       (slv_r_o       ),
      .slv_r_valid_o (slv_r_valid_o ),
      .slv_r_ready_i (slv_r_ready_i ),
      // Master interface
      .mst_aw_o      (mst_aw_o      ),
      .mst_aw_valid_o(mst_aw_valid_o),
      .mst_aw_ready_i(mst_aw_ready_i),
      .mst_w_o       (mst_w_o       ),
      .mst_w_valid_o (mst_w_valid_o ),
      .mst_w_ready_i (mst_w_ready_i ),
      .mst_b_i       (mst_b_i       ),
      .mst_b_valid_i (mst_b_valid_i ),
      .mst_b_ready_o (mst_b_ready_o ),
      .mst_ar_o      (mst_ar_o      ),
      .mst_ar_valid_o(mst_ar_valid_o),
      .mst_ar_ready_i(mst_ar_ready_i),
      .mst_r_i       (mst_r_i       ),
      .mst_r_valid_i (mst_r_valid_i ),
      .mst_r_ready_o (mst_r_ready_o )
    );
  end : gen_dw_downsize

endmodule : axi_dw_converter
