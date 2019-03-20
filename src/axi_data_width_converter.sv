// Copyright 2019 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// File          : axi_data_width_converter.sv
// Author        : Matheus Cavalcante <matheusd@iis.ee.ethz.ch>
// Created       : 31.01.2019
//
// Copyright (C) 2019 ETH Zurich, University of Bologna
// All rights reserved.

import axi_pkg::*;

module axi_data_width_converter #(
  parameter int unsigned SI_DATA_WIDTH = 64,
  parameter int unsigned MI_DATA_WIDTH = 64,
  parameter int unsigned ID_WIDTH = 4,
  parameter int unsigned USER_WIDTH = 1
) (
  input logic clk_i,
  input logic rst_ni,
  AXI_BUS.in  in,
  AXI_BUS.out out
);

`ifndef SYNTHESIS
  initial begin
    assert(in.AXI_ADDR_WIDTH  == out.AXI_ADDR_WIDTH);
    assert(in.AXI_DATA_WIDTH  == SI_DATA_WIDTH);
    assert(out.AXI_DATA_WIDTH == MI_DATA_WIDTH);
    assert(in.AXI_ID_WIDTH    == out.AXI_ID_WIDTH   && in.AXI_ID_WIDTH   == ID_WIDTH);
    assert(in.AXI_USER_WIDTH  == out.AXI_USER_WIDTH && in.AXI_USER_WIDTH == USER_WIDTH);
  end
`endif

  generate
    if (SI_DATA_WIDTH == MI_DATA_WIDTH) begin: NO_WIDTH_CONVERSION
    axi_join i_axi_join (
      .in,
      .out
    );
    end

    if (SI_DATA_WIDTH < MI_DATA_WIDTH) begin: UPSIZE
    axi_data_upsize #(
      .SI_DATA_WIDTH ( SI_DATA_WIDTH ),
      .MI_DATA_WIDTH ( MI_DATA_WIDTH ),
      .ID_WIDTH ( ID_WIDTH ),
      .USER_WIDTH ( USER_WIDTH )
    ) i_axi_data_upsize (
      .clk_i,
      .rst_ni,

      .in_aw_id ( in.aw_id ),
      .in_aw_addr ( in.aw_addr ),
      .in_aw_len ( in.aw_len ),
      .in_aw_size ( in.aw_size ),
      .in_aw_burst ( in.aw_burst ),
      .in_aw_lock ( in.aw_lock ),
      .in_aw_cache ( in.aw_cache ),
      .in_aw_prot ( in.aw_prot ),
      .in_aw_qos ( in.aw_qos ),
      .in_aw_region ( in.aw_region ),
      .in_aw_atop ( in.aw_atop ),
      .in_aw_user ( in.aw_user ),
      .in_aw_valid ( in.aw_valid ),
      .in_aw_ready ( in.aw_ready ),

      .in_w_data ( in.w_data ),
      .in_w_strb ( in.w_strb ),
      .in_w_last ( in.w_last ),
      .in_w_user ( in.w_user ),
      .in_w_valid ( in.w_valid ),
      .in_w_ready ( in.w_ready ),

      .in_b_id ( in.b_id ),
      .in_b_resp ( in.b_resp ),
      .in_b_user ( in.b_user ),
      .in_b_valid ( in.b_valid ),
      .in_b_ready ( in.b_ready ),

      .in_ar_id ( in.ar_id ),
      .in_ar_addr ( in.ar_addr ),
      .in_ar_len ( in.ar_len ),
      .in_ar_size ( in.ar_size ),
      .in_ar_burst ( in.ar_burst ),
      .in_ar_lock ( in.ar_lock ),
      .in_ar_cache ( in.ar_cache ),
      .in_ar_prot ( in.ar_prot ),
      .in_ar_qos ( in.ar_qos ),
      .in_ar_region ( in.ar_region ),
      .in_ar_user ( in.ar_user ),
      .in_ar_valid ( in.ar_valid ),
      .in_ar_ready ( in.ar_ready ),

      .in_r_id ( in.r_id ),
      .in_r_data ( in.r_data ),
      .in_r_resp ( in.r_resp ),
      .in_r_last ( in.r_last ),
      .in_r_user ( in.r_user ),
      .in_r_valid ( in.r_valid ),
      .in_r_ready ( in.r_ready ),

      .out_aw_id ( out.aw_id ),
      .out_aw_addr ( out.aw_addr ),
      .out_aw_len ( out.aw_len ),
      .out_aw_size ( out.aw_size ),
      .out_aw_burst ( out.aw_burst ),
      .out_aw_lock ( out.aw_lock ),
      .out_aw_cache ( out.aw_cache ),
      .out_aw_prot ( out.aw_prot ),
      .out_aw_qos ( out.aw_qos ),
      .out_aw_region ( out.aw_region ),
      .out_aw_atop ( out.aw_atop ),
      .out_aw_user ( out.aw_user ),
      .out_aw_valid ( out.aw_valid ),
      .out_aw_ready ( out.aw_ready ),

      .out_w_data ( out.w_data ),
      .out_w_strb ( out.w_strb ),
      .out_w_last ( out.w_last ),
      .out_w_user ( out.w_user ),
      .out_w_valid ( out.w_valid ),
      .out_w_ready ( out.w_ready ),

      .out_b_id ( out.b_id ),
      .out_b_resp ( out.b_resp ),
      .out_b_user ( out.b_user ),
      .out_b_valid ( out.b_valid ),
      .out_b_ready ( out.b_ready ),

      .out_ar_id ( out.ar_id ),
      .out_ar_addr ( out.ar_addr ),
      .out_ar_len ( out.ar_len ),
      .out_ar_size ( out.ar_size ),
      .out_ar_burst ( out.ar_burst ),
      .out_ar_lock ( out.ar_lock ),
      .out_ar_cache ( out.ar_cache ),
      .out_ar_prot ( out.ar_prot ),
      .out_ar_qos ( out.ar_qos ),
      .out_ar_region ( out.ar_region ),
      .out_ar_user ( out.ar_user ),
      .out_ar_valid ( out.ar_valid ),
      .out_ar_ready ( out.ar_ready ),

      .out_r_id ( out.r_id ),
      .out_r_data ( out.r_data ),
      .out_r_resp ( out.r_resp ),
      .out_r_last ( out.r_last ),
      .out_r_user ( out.r_user ),
      .out_r_valid ( out.r_valid ),
      .out_r_ready ( out.r_ready ));
    end

    if (SI_DATA_WIDTH > MI_DATA_WIDTH) begin: DOWNSIZE
    axi_data_downsize #(
      .SI_DATA_WIDTH ( SI_DATA_WIDTH ),
      .MI_DATA_WIDTH ( MI_DATA_WIDTH ),
      .ID_WIDTH ( ID_WIDTH ),
      .USER_WIDTH ( USER_WIDTH )
    ) i_axi_data_downsize (
      .clk_i,
      .rst_ni,

      .in_aw_id ( in.aw_id ),
      .in_aw_addr ( in.aw_addr ),
      .in_aw_len ( in.aw_len ),
      .in_aw_size ( in.aw_size ),
      .in_aw_burst ( in.aw_burst ),
      .in_aw_lock ( in.aw_lock ),
      .in_aw_cache ( in.aw_cache ),
      .in_aw_prot ( in.aw_prot ),
      .in_aw_qos ( in.aw_qos ),
      .in_aw_region ( in.aw_region ),
      .in_aw_atop ( in.aw_atop ),
      .in_aw_user ( in.aw_user ),
      .in_aw_valid ( in.aw_valid ),
      .in_aw_ready ( in.aw_ready ),

      .in_w_data ( in.w_data ),
      .in_w_strb ( in.w_strb ),
      .in_w_last ( in.w_last ),
      .in_w_user ( in.w_user ),
      .in_w_valid ( in.w_valid ),
      .in_w_ready ( in.w_ready ),

      .in_b_id ( in.b_id ),
      .in_b_resp ( in.b_resp ),
      .in_b_user ( in.b_user ),
      .in_b_valid ( in.b_valid ),
      .in_b_ready ( in.b_ready ),

      .in_ar_id ( in.ar_id ),
      .in_ar_addr ( in.ar_addr ),
      .in_ar_len ( in.ar_len ),
      .in_ar_size ( in.ar_size ),
      .in_ar_burst ( in.ar_burst ),
      .in_ar_lock ( in.ar_lock ),
      .in_ar_cache ( in.ar_cache ),
      .in_ar_prot ( in.ar_prot ),
      .in_ar_qos ( in.ar_qos ),
      .in_ar_region ( in.ar_region ),
      .in_ar_user ( in.ar_user ),
      .in_ar_valid ( in.ar_valid ),
      .in_ar_ready ( in.ar_ready ),

      .in_r_id ( in.r_id ),
      .in_r_data ( in.r_data ),
      .in_r_resp ( in.r_resp ),
      .in_r_last ( in.r_last ),
      .in_r_user ( in.r_user ),
      .in_r_valid ( in.r_valid ),
      .in_r_ready ( in.r_ready ),

      .out_aw_id ( out.aw_id ),
      .out_aw_addr ( out.aw_addr ),
      .out_aw_len ( out.aw_len ),
      .out_aw_size ( out.aw_size ),
      .out_aw_burst ( out.aw_burst ),
      .out_aw_lock ( out.aw_lock ),
      .out_aw_cache ( out.aw_cache ),
      .out_aw_prot ( out.aw_prot ),
      .out_aw_qos ( out.aw_qos ),
      .out_aw_region ( out.aw_region ),
      .out_aw_atop ( out.aw_atop ),
      .out_aw_user ( out.aw_user ),
      .out_aw_valid ( out.aw_valid ),
      .out_aw_ready ( out.aw_ready ),

      .out_w_data ( out.w_data ),
      .out_w_strb ( out.w_strb ),
      .out_w_last ( out.w_last ),
      .out_w_user ( out.w_user ),
      .out_w_valid ( out.w_valid ),
      .out_w_ready ( out.w_ready ),

      .out_b_id ( out.b_id ),
      .out_b_resp ( out.b_resp ),
      .out_b_user ( out.b_user ),
      .out_b_valid ( out.b_valid ),
      .out_b_ready ( out.b_ready ),

      .out_ar_id ( out.ar_id ),
      .out_ar_addr ( out.ar_addr ),
      .out_ar_len ( out.ar_len ),
      .out_ar_size ( out.ar_size ),
      .out_ar_burst ( out.ar_burst ),
      .out_ar_lock ( out.ar_lock ),
      .out_ar_cache ( out.ar_cache ),
      .out_ar_prot ( out.ar_prot ),
      .out_ar_qos ( out.ar_qos ),
      .out_ar_region ( out.ar_region ),
      .out_ar_user ( out.ar_user ),
      .out_ar_valid ( out.ar_valid ),
      .out_ar_ready ( out.ar_ready ),

      .out_r_id ( out.r_id ),
      .out_r_data ( out.r_data ),
      .out_r_resp ( out.r_resp ),
      .out_r_last ( out.r_last ),
      .out_r_user ( out.r_user ),
      .out_r_valid ( out.r_valid ),
      .out_r_ready ( out.r_ready ));
    end
  endgenerate

endmodule // axi_data_width_converter
