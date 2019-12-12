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

// Macros to assign AXI Interfaces

`ifndef AXI_ASSIGN_SVH_
`define AXI_ASSIGN_SVH_

////////////////////////////////////////////////////////////////////////////////////////////////////
// Assigning one AXI4+ATOP interface to another, as if you would do `assign slv = mst;`
//
// The channel assignments `AXI_ASSIGN_XX(dst, src)` assign all payload and the valid signal of the
// `XX` channel from the `src` to the `dst` interface and they assign the ready signal from the
// `src` to the `dst` interface.
// The interface assignment `AXI_ASSIGN(dst, src)` assigns all channels including handshakes as if
// `src` was the master of `dst`.
//
// Usage Example:
// `AXI_ASSIGN(slv, mst);
// `AXI_ASSIGN_AW(dst, src);
// `AXI_ASSIGN_R(dst, src);
`define AXI_ASSIGN_AW(dst, src)           \
  assign dst.aw_id      = src.aw_id;      \
  assign dst.aw_addr    = src.aw_addr;    \
  assign dst.aw_len     = src.aw_len;     \
  assign dst.aw_size    = src.aw_size;    \
  assign dst.aw_burst   = src.aw_burst;   \
  assign dst.aw_lock    = src.aw_lock;    \
  assign dst.aw_cache   = src.aw_cache;   \
  assign dst.aw_prot    = src.aw_prot;    \
  assign dst.aw_qos     = src.aw_qos;     \
  assign dst.aw_region  = src.aw_region;  \
  assign dst.aw_atop    = src.aw_atop;    \
  assign dst.aw_user    = src.aw_user;    \
  assign dst.aw_valid   = src.aw_valid;   \
  assign src.aw_ready   = dst.aw_ready;
`define AXI_ASSIGN_W(dst, src)        \
  assign dst.w_data   = src.w_data;   \
  assign dst.w_strb   = src.w_strb;   \
  assign dst.w_last   = src.w_last;   \
  assign dst.w_user   = src.w_user;   \
  assign dst.w_valid  = src.w_valid;  \
  assign src.w_ready  = dst.w_ready;
`define AXI_ASSIGN_B(dst, src)        \
  assign dst.b_id     = src.b_id;     \
  assign dst.b_resp   = src.b_resp;   \
  assign dst.b_user   = src.b_user;   \
  assign dst.b_valid  = src.b_valid;  \
  assign src.b_ready  = dst.b_ready;
`define AXI_ASSIGN_AR(dst, src)           \
  assign dst.ar_id      = src.ar_id;      \
  assign dst.ar_addr    = src.ar_addr;    \
  assign dst.ar_len     = src.ar_len;     \
  assign dst.ar_size    = src.ar_size;    \
  assign dst.ar_burst   = src.ar_burst;   \
  assign dst.ar_lock    = src.ar_lock;    \
  assign dst.ar_cache   = src.ar_cache;   \
  assign dst.ar_prot    = src.ar_prot;    \
  assign dst.ar_qos     = src.ar_qos;     \
  assign dst.ar_region  = src.ar_region;  \
  assign dst.ar_user    = src.ar_user;    \
  assign dst.ar_valid   = src.ar_valid;   \
  assign src.ar_ready   = dst.ar_ready;
`define AXI_ASSIGN_R(dst, src)        \
  assign dst.r_id     = src.r_id;     \
  assign dst.r_data   = src.r_data;   \
  assign dst.r_resp   = src.r_resp;   \
  assign dst.r_last   = src.r_last;   \
  assign dst.r_user   = src.r_user;   \
  assign dst.r_valid  = src.r_valid;  \
  assign src.r_ready  = dst.r_ready;
`define AXI_ASSIGN(slv, mst)  \
  `AXI_ASSIGN_AW(slv, mst)    \
  `AXI_ASSIGN_W(slv, mst)     \
  `AXI_ASSIGN_B(mst, slv)     \
  `AXI_ASSIGN_AR(slv, mst)    \
  `AXI_ASSIGN_R(mst, slv)
////////////////////////////////////////////////////////////////////////////////////////////////////

// Assign an AXI4-Lite master interface to a slave interface, as in `assign slv = mst;`.
`define AXI_LITE_ASSIGN(slv, mst)     \
  assign slv.aw_addr  = mst.aw_addr;  \
  assign slv.aw_valid = mst.aw_valid; \
  assign mst.aw_ready = slv.aw_ready; \
                                      \
  assign slv.w_data   = mst.w_data;   \
  assign slv.w_strb   = mst.w_strb;   \
  assign slv.w_valid  = mst.w_valid;  \
  assign mst.w_ready  = slv.w_ready;  \
                                      \
  assign mst.b_resp   = slv.b_resp;   \
  assign mst.b_valid  = slv.b_valid;  \
  assign slv.b_ready  = mst.b_ready;  \
                                      \
  assign slv.ar_addr  = mst.ar_addr;  \
  assign slv.ar_valid = mst.ar_valid; \
  assign mst.ar_ready = slv.ar_ready; \
                                      \
  assign mst.r_data   = slv.r_data;   \
  assign mst.r_resp   = slv.r_resp;   \
  assign mst.r_valid  = slv.r_valid;  \
  assign slv.r_ready  = mst.r_ready;

`endif
