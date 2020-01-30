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

import axi_pkg::*;

module axi_dw_converter #(
    parameter int AxiAddrWidth    = 64,
    parameter int AxiMstDataWidth = 64,
    parameter int AxiSlvDataWidth = 64,
    parameter int AxiMaxTrans     = 1 ,
    parameter int AxiIdWidth      = 4 ,
    parameter int AxiUserWidth    = 1
  )(
    input logic clk_i,
    input logic rst_ni,

    AXI_BUS.Slave  slv,
    AXI_BUS.Master mst
  );

  `ifndef SYNTHESIS
  initial begin
    assert(slv.AXI_ADDR_WIDTH == mst.AXI_ADDR_WIDTH && slv.AXI_ADDR_WIDTH == AxiAddrWidth) ;
    assert(slv.AXI_DATA_WIDTH == AxiSlvDataWidth) ;
    assert(mst.AXI_DATA_WIDTH == AxiMstDataWidth) ;
    assert(slv.AXI_ID_WIDTH == mst.AXI_ID_WIDTH && slv.AXI_ID_WIDTH == AxiIdWidth) ;
    assert(slv.AXI_USER_WIDTH == mst.AXI_USER_WIDTH && slv.AXI_USER_WIDTH == AxiUserWidth);

    if (AxiSlvDataWidth != AxiMstDataWidth)
      assert property (@(posedge clk_i) disable iff (~rst_ni) slv.aw_valid |-> slv.aw_atop[5] == 1'b0)
      else $fatal(1, "This module does not yet support atomic transactions with an R resp!");
  end
  `endif

  if (AxiSlvDataWidth == AxiMstDataWidth) begin: gen_no_dw_conversion
    axi_join_intf i_axi_join (
      .in (slv),
      .out(mst)
    );
  end

  if (AxiSlvDataWidth < AxiMstDataWidth) begin: gen_dw_upsize
    axi_dw_upsizer #(
      .AxiAddrWidth   (AxiAddrWidth    ),
      .AxiMstDataWidth(AxiMstDataWidth ),
      .AxiSlvDataWidth(AxiSlvDataWidth ),
      .AxiMaxTrans    (AxiMaxTrans     ),
      .AxiIdWidth     (AxiIdWidth      ),
      .AxiUserWidth   (AxiUserWidth    )
    ) i_axi_data_upsize (
      .clk_i        (clk_i        ),
      .rst_ni       (rst_ni       ),
      .slv_aw_id    (slv.aw_id    ),
      .slv_aw_addr  (slv.aw_addr  ),
      .slv_aw_len   (slv.aw_len   ),
      .slv_aw_size  (slv.aw_size  ),
      .slv_aw_burst (slv.aw_burst ),
      .slv_aw_lock  (slv.aw_lock  ),
      .slv_aw_cache (slv.aw_cache ),
      .slv_aw_prot  (slv.aw_prot  ),
      .slv_aw_qos   (slv.aw_qos   ),
      .slv_aw_region(slv.aw_region),
      .slv_aw_atop  (slv.aw_atop  ),
      .slv_aw_user  (slv.aw_user  ),
      .slv_aw_valid (slv.aw_valid ),
      .slv_aw_ready (slv.aw_ready ),
      .slv_w_data   (slv.w_data   ),
      .slv_w_strb   (slv.w_strb   ),
      .slv_w_last   (slv.w_last   ),
      .slv_w_user   (slv.w_user   ),
      .slv_w_valid  (slv.w_valid  ),
      .slv_w_ready  (slv.w_ready  ),
      .slv_b_id     (slv.b_id     ),
      .slv_b_resp   (slv.b_resp   ),
      .slv_b_user   (slv.b_user   ),
      .slv_b_valid  (slv.b_valid  ),
      .slv_b_ready  (slv.b_ready  ),
      .slv_ar_id    (slv.ar_id    ),
      .slv_ar_addr  (slv.ar_addr  ),
      .slv_ar_len   (slv.ar_len   ),
      .slv_ar_size  (slv.ar_size  ),
      .slv_ar_burst (slv.ar_burst ),
      .slv_ar_lock  (slv.ar_lock  ),
      .slv_ar_cache (slv.ar_cache ),
      .slv_ar_prot  (slv.ar_prot  ),
      .slv_ar_qos   (slv.ar_qos   ),
      .slv_ar_region(slv.ar_region),
      .slv_ar_user  (slv.ar_user  ),
      .slv_ar_valid (slv.ar_valid ),
      .slv_ar_ready (slv.ar_ready ),
      .slv_r_id     (slv.r_id     ),
      .slv_r_data   (slv.r_data   ),
      .slv_r_resp   (slv.r_resp   ),
      .slv_r_last   (slv.r_last   ),
      .slv_r_user   (slv.r_user   ),
      .slv_r_valid  (slv.r_valid  ),
      .slv_r_ready  (slv.r_ready  ),
      .mst_aw_id    (mst.aw_id    ),
      .mst_aw_addr  (mst.aw_addr  ),
      .mst_aw_len   (mst.aw_len   ),
      .mst_aw_size  (mst.aw_size  ),
      .mst_aw_burst (mst.aw_burst ),
      .mst_aw_lock  (mst.aw_lock  ),
      .mst_aw_cache (mst.aw_cache ),
      .mst_aw_prot  (mst.aw_prot  ),
      .mst_aw_qos   (mst.aw_qos   ),
      .mst_aw_region(mst.aw_region),
      .mst_aw_atop  (mst.aw_atop  ),
      .mst_aw_user  (mst.aw_user  ),
      .mst_aw_valid (mst.aw_valid ),
      .mst_aw_ready (mst.aw_ready ),
      .mst_w_data   (mst.w_data   ),
      .mst_w_strb   (mst.w_strb   ),
      .mst_w_last   (mst.w_last   ),
      .mst_w_user   (mst.w_user   ),
      .mst_w_valid  (mst.w_valid  ),
      .mst_w_ready  (mst.w_ready  ),
      .mst_b_id     (mst.b_id     ),
      .mst_b_resp   (mst.b_resp   ),
      .mst_b_user   (mst.b_user   ),
      .mst_b_valid  (mst.b_valid  ),
      .mst_b_ready  (mst.b_ready  ),
      .mst_ar_id    (mst.ar_id    ),
      .mst_ar_addr  (mst.ar_addr  ),
      .mst_ar_len   (mst.ar_len   ),
      .mst_ar_size  (mst.ar_size  ),
      .mst_ar_burst (mst.ar_burst ),
      .mst_ar_lock  (mst.ar_lock  ),
      .mst_ar_cache (mst.ar_cache ),
      .mst_ar_prot  (mst.ar_prot  ),
      .mst_ar_qos   (mst.ar_qos   ),
      .mst_ar_region(mst.ar_region),
      .mst_ar_user  (mst.ar_user  ),
      .mst_ar_valid (mst.ar_valid ),
      .mst_ar_ready (mst.ar_ready ),
      .mst_r_id     (mst.r_id     ),
      .mst_r_data   (mst.r_data   ),
      .mst_r_resp   (mst.r_resp   ),
      .mst_r_last   (mst.r_last   ),
      .mst_r_user   (mst.r_user   ),
      .mst_r_valid  (mst.r_valid  ),
      .mst_r_ready  (mst.r_ready  )
    );
  end

  if (AxiSlvDataWidth > AxiMstDataWidth) begin: gen_dw_downsize
    axi_dw_downsizer #(
      .AxiAddrWidth   (AxiAddrWidth    ),
      .AxiMstDataWidth(AxiMstDataWidth ),
      .AxiSlvDataWidth(AxiSlvDataWidth ),
      .AxiMaxTrans    (AxiMaxTrans     ),
      .AxiIdWidth     (AxiIdWidth      ),
      .AxiUserWidth   (AxiUserWidth    )
    ) i_axi_data_downsize (
      .clk_i        (clk_i        ),
      .rst_ni       (rst_ni       ),
      .slv_aw_id    (slv.aw_id    ),
      .slv_aw_addr  (slv.aw_addr  ),
      .slv_aw_len   (slv.aw_len   ),
      .slv_aw_size  (slv.aw_size  ),
      .slv_aw_burst (slv.aw_burst ),
      .slv_aw_lock  (slv.aw_lock  ),
      .slv_aw_cache (slv.aw_cache ),
      .slv_aw_prot  (slv.aw_prot  ),
      .slv_aw_qos   (slv.aw_qos   ),
      .slv_aw_region(slv.aw_region),
      .slv_aw_atop  (slv.aw_atop  ),
      .slv_aw_user  (slv.aw_user  ),
      .slv_aw_valid (slv.aw_valid ),
      .slv_aw_ready (slv.aw_ready ),
      .slv_w_data   (slv.w_data   ),
      .slv_w_strb   (slv.w_strb   ),
      .slv_w_last   (slv.w_last   ),
      .slv_w_user   (slv.w_user   ),
      .slv_w_valid  (slv.w_valid  ),
      .slv_w_ready  (slv.w_ready  ),
      .slv_b_id     (slv.b_id     ),
      .slv_b_resp   (slv.b_resp   ),
      .slv_b_user   (slv.b_user   ),
      .slv_b_valid  (slv.b_valid  ),
      .slv_b_ready  (slv.b_ready  ),
      .slv_ar_id    (slv.ar_id    ),
      .slv_ar_addr  (slv.ar_addr  ),
      .slv_ar_len   (slv.ar_len   ),
      .slv_ar_size  (slv.ar_size  ),
      .slv_ar_burst (slv.ar_burst ),
      .slv_ar_lock  (slv.ar_lock  ),
      .slv_ar_cache (slv.ar_cache ),
      .slv_ar_prot  (slv.ar_prot  ),
      .slv_ar_qos   (slv.ar_qos   ),
      .slv_ar_region(slv.ar_region),
      .slv_ar_user  (slv.ar_user  ),
      .slv_ar_valid (slv.ar_valid ),
      .slv_ar_ready (slv.ar_ready ),
      .slv_r_id     (slv.r_id     ),
      .slv_r_data   (slv.r_data   ),
      .slv_r_resp   (slv.r_resp   ),
      .slv_r_last   (slv.r_last   ),
      .slv_r_user   (slv.r_user   ),
      .slv_r_valid  (slv.r_valid  ),
      .slv_r_ready  (slv.r_ready  ),
      .mst_aw_id    (mst.aw_id    ),
      .mst_aw_addr  (mst.aw_addr  ),
      .mst_aw_len   (mst.aw_len   ),
      .mst_aw_size  (mst.aw_size  ),
      .mst_aw_burst (mst.aw_burst ),
      .mst_aw_lock  (mst.aw_lock  ),
      .mst_aw_cache (mst.aw_cache ),
      .mst_aw_prot  (mst.aw_prot  ),
      .mst_aw_qos   (mst.aw_qos   ),
      .mst_aw_region(mst.aw_region),
      .mst_aw_atop  (mst.aw_atop  ),
      .mst_aw_user  (mst.aw_user  ),
      .mst_aw_valid (mst.aw_valid ),
      .mst_aw_ready (mst.aw_ready ),
      .mst_w_data   (mst.w_data   ),
      .mst_w_strb   (mst.w_strb   ),
      .mst_w_last   (mst.w_last   ),
      .mst_w_user   (mst.w_user   ),
      .mst_w_valid  (mst.w_valid  ),
      .mst_w_ready  (mst.w_ready  ),
      .mst_b_id     (mst.b_id     ),
      .mst_b_resp   (mst.b_resp   ),
      .mst_b_user   (mst.b_user   ),
      .mst_b_valid  (mst.b_valid  ),
      .mst_b_ready  (mst.b_ready  ),
      .mst_ar_id    (mst.ar_id    ),
      .mst_ar_addr  (mst.ar_addr  ),
      .mst_ar_len   (mst.ar_len   ),
      .mst_ar_size  (mst.ar_size  ),
      .mst_ar_burst (mst.ar_burst ),
      .mst_ar_lock  (mst.ar_lock  ),
      .mst_ar_cache (mst.ar_cache ),
      .mst_ar_prot  (mst.ar_prot  ),
      .mst_ar_qos   (mst.ar_qos   ),
      .mst_ar_region(mst.ar_region),
      .mst_ar_user  (mst.ar_user  ),
      .mst_ar_valid (mst.ar_valid ),
      .mst_ar_ready (mst.ar_ready ),
      .mst_r_id     (mst.r_id     ),
      .mst_r_data   (mst.r_data   ),
      .mst_r_resp   (mst.r_resp   ),
      .mst_r_last   (mst.r_last   ),
      .mst_r_user   (mst.r_user   ),
      .mst_r_valid  (mst.r_valid  ),
      .mst_r_ready  (mst.r_ready  )
    );
  end

endmodule : axi_dw_converter
