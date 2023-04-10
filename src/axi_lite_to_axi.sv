// Copyright (c) 2014-2018 ETH Zurich, University of Bologna
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
// - Fabian Schuiki <fschuiki@iis.ee.ethz.ch>
// - Wolfgang Roenninger <wroennin@iis.ee.ethz.ch>
// - Andreas Kurth <akurth@iis.ee.ethz.ch>

/// An AXI4-Lite to AXI4 adapter.
module axi_lite_to_axi #(
  parameter int unsigned DataWidth = 32'd0,
  // LITE AXI structs
  parameter type axi_lite_req_t = logic,
  parameter type axi_lite_rsp_t = logic,
  // FULL AXI structs
  parameter type      axi_req_t = logic,
  parameter type      axi_rsp_t = logic
) (
  // Subordinate AXI LITE port
  input  axi_lite_req_t   sbr_req_lite_i,
  output axi_lite_rsp_t   sbr_rsp_lite_o,
  input  axi_pkg::cache_t sbr_aw_cache_i,
  input  axi_pkg::cache_t sbr_ar_cache_i,
  // Manager AXI port
  output axi_req_t        mgr_req_o,
  input  axi_rsp_t        mgr_rsp_i
);
  localparam int unsigned Size = axi_pkg::size_t'($unsigned($clog2(DataWidth/8)));

  // request assign
  assign mgr_req_o = '{
    aw: '{
      addr:  sbr_req_lite_i.aw.addr,
      prot:  sbr_req_lite_i.aw.prot,
      size:  Size,
      burst: axi_pkg::BURST_FIXED,
      cache: sbr_aw_cache_i,
      default: '0
    },
    aw_valid: sbr_req_lite_i.aw_valid,
    w: '{
      data: sbr_req_lite_i.w.data,
      strb: sbr_req_lite_i.w.strb,
      last: 1'b1,
      default: '0
    },
    w_valid: sbr_req_lite_i.w_valid,
    b_ready: sbr_req_lite_i.b_ready,
    ar: '{
      addr:  sbr_req_lite_i.ar.addr,
      prot:  sbr_req_lite_i.ar.prot,
      size:  Size,
      burst: axi_pkg::BURST_FIXED,
      cache: sbr_ar_cache_i,
      default: '0
    },
    ar_valid: sbr_req_lite_i.ar_valid,
    r_ready:  sbr_req_lite_i.r_ready,
    default:   '0
  };
  // response assign
  assign sbr_rsp_lite_o = '{
    aw_ready: mgr_rsp_i.aw_ready,
    w_ready:  mgr_rsp_i.w_ready,
    b: '{
      resp: mgr_rsp_i.b.resp,
      default: '0
    },
    b_valid:  mgr_rsp_i.b_valid,
    ar_ready: mgr_rsp_i.ar_ready,
    r: '{
      data: mgr_rsp_i.r.data,
      resp: mgr_rsp_i.r.resp,
      default: '0
    },
    r_valid: mgr_rsp_i.r_valid,
    default: '0
  };

  // pragma translate_off
  `ifndef VERILATOR
  initial begin
    assert (DataWidth > 0) else $fatal(1, "Data width must be non-zero!");
  end
  `endif
  // pragma translate_on
endmodule

module axi_lite_to_axi_intf #(
  parameter int unsigned AXI_DATA_WIDTH = 32'd0
) (
  AXI_LITE.Subordinate  in,
  input axi_pkg::cache_t sbr_aw_cache_i,
  input axi_pkg::cache_t sbr_ar_cache_i,
  AXI_BUS.Manager  out
);
  localparam int unsigned Size = axi_pkg::size_t'($unsigned($clog2(AXI_DATA_WIDTH/8)));

// pragma translate_off
  initial begin
    assert(in.AXI_ADDR_WIDTH == out.AXI_ADDR_WIDTH);
    assert(in.AXI_DATA_WIDTH == out.AXI_DATA_WIDTH);
    assert(AXI_DATA_WIDTH    == out.AXI_DATA_WIDTH);
  end
// pragma translate_on

  assign out.aw_id     = '0;
  assign out.aw_addr   = in.aw_addr;
  assign out.aw_len    = '0;
  assign out.aw_size   = Size;
  assign out.aw_burst  = axi_pkg::BURST_FIXED;
  assign out.aw_lock   = '0;
  assign out.aw_cache  = sbr_aw_cache_i;
  assign out.aw_prot   = '0;
  assign out.aw_qos    = '0;
  assign out.aw_region = '0;
  assign out.aw_atop   = '0;
  assign out.aw_user   = '0;
  assign out.aw_valid  = in.aw_valid;
  assign in.aw_ready   = out.aw_ready;

  assign out.w_data    = in.w_data;
  assign out.w_strb    = in.w_strb;
  assign out.w_last    = '1;
  assign out.w_user    = '0;
  assign out.w_valid   = in.w_valid;
  assign in.w_ready    = out.w_ready;

  assign in.b_resp     = out.b_resp;
  assign in.b_valid    = out.b_valid;
  assign out.b_ready   = in.b_ready;

  assign out.ar_id     = '0;
  assign out.ar_addr   = in.ar_addr;
  assign out.ar_len    = '0;
  assign out.ar_size   = Size;
  assign out.ar_burst  = axi_pkg::BURST_FIXED;
  assign out.ar_lock   = '0;
  assign out.ar_cache  = sbr_ar_cache_i;
  assign out.ar_prot   = '0;
  assign out.ar_qos    = '0;
  assign out.ar_region = '0;
  assign out.ar_user   = '0;
  assign out.ar_valid  = in.ar_valid;
  assign in.ar_ready   = out.ar_ready;

  assign in.r_data     = out.r_data;
  assign in.r_resp     = out.r_resp;
  assign in.r_valid    = out.r_valid;
  assign out.r_ready   = in.r_ready;

endmodule
