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

`ifndef AXI_ASSIGN_SVH_
`define AXI_ASSIGN_SVH_

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

// Assign an AXI4 master interface to a slave interface, as in `assign slv = mst;`.
`define AXI_ASSIGN(slv, mst)  \
  `AXI_ASSIGN_AW(slv, mst)    \
  `AXI_ASSIGN_W(slv, mst)     \
  `AXI_ASSIGN_B(mst, slv)     \
  `AXI_ASSIGN_AR(slv, mst)    \
  `AXI_ASSIGN_R(mst, slv)

`define AXI_ASSIGN_TO_AW(aw_struct, axi_if) \
  assign aw_struct = '{                     \
    id:     axi_if.aw_id,                   \
    addr:   axi_if.aw_addr,                 \
    len:    axi_if.aw_len,                  \
    size:   axi_if.aw_size,                 \
    burst:  axi_if.aw_burst,                \
    lock:   axi_if.aw_lock,                 \
    cache:  axi_if.aw_cache,                \
    prot:   axi_if.aw_prot,                 \
    qos:    axi_if.aw_qos,                  \
    region: axi_if.aw_region,               \
    atop:   axi_if.aw_atop,                 \
    user:   axi_if.aw_user                  \
  };

`define AXI_ASSIGN_FROM_AW(axi_if, aw_struct) \
  assign axi_if.aw_id     = aw_struct.id;     \
  assign axi_if.aw_addr   = aw_struct.addr;   \
  assign axi_if.aw_len    = aw_struct.len;    \
  assign axi_if.aw_size   = aw_struct.size;   \
  assign axi_if.aw_burst  = aw_struct.burst;  \
  assign axi_if.aw_lock   = aw_struct.lock;   \
  assign axi_if.aw_cache  = aw_struct.cache;  \
  assign axi_if.aw_prot   = aw_struct.prot;   \
  assign axi_if.aw_qos    = aw_struct.qos;    \
  assign axi_if.aw_region = aw_struct.region; \
  assign axi_if.aw_atop   = aw_struct.atop;   \
  assign axi_if.aw_user   = aw_struct.user;

`define AXI_ASSIGN_TO_W(w_struct, axi_if) \
  assign w_struct = '{                    \
    data: axi_if.w_data,                  \
    strb: axi_if.w_strb,                  \
    last: axi_if.w_last,                  \
    user: axi_if.w_user                   \
  };

`define AXI_ASSIGN_FROM_W(axi_if, w_struct) \
  assign axi_if.w_data  = w_struct.data;    \
  assign axi_if.w_strb  = w_struct.strb;    \
  assign axi_if.w_last  = w_struct.last;    \
  assign axi_if.w_user  = w_struct.user;

`define AXI_ASSIGN_TO_B(b_struct, axi_if) \
  assign b_struct = '{                    \
    id:   axi_if.b_id,                    \
    resp: axi_if.b_resp,                  \
    user: axi_if.b_user                   \
  };

`define AXI_ASSIGN_FROM_B(axi_if, b_struct) \
  assign axi_if.b_id    = b_struct.id;      \
  assign axi_if.b_resp  = b_struct.resp;    \
  assign axi_if.b_user  = b_struct.user;

`define AXI_ASSIGN_TO_AR(ar_struct, axi_if) \
  assign ar_struct = '{                     \
    id:     axi_if.ar_id,                   \
    addr:   axi_if.ar_addr,                 \
    len:    axi_if.ar_len,                  \
    size:   axi_if.ar_size,                 \
    burst:  axi_if.ar_burst,                \
    lock:   axi_if.ar_lock,                 \
    cache:  axi_if.ar_cache,                \
    prot:   axi_if.ar_prot,                 \
    qos:    axi_if.ar_qos,                  \
    region: axi_if.ar_region,               \
    user:   axi_if.ar_user                  \
  };

`define AXI_ASSIGN_FROM_AR(axi_if, ar_struct) \
  assign axi_if.ar_id     = ar_struct.id;     \
  assign axi_if.ar_addr   = ar_struct.addr;   \
  assign axi_if.ar_len    = ar_struct.len;    \
  assign axi_if.ar_size   = ar_struct.size;   \
  assign axi_if.ar_burst  = ar_struct.burst;  \
  assign axi_if.ar_lock   = ar_struct.lock;   \
  assign axi_if.ar_cache  = ar_struct.cache;  \
  assign axi_if.ar_prot   = ar_struct.prot;   \
  assign axi_if.ar_qos    = ar_struct.qos;    \
  assign axi_if.ar_region = ar_struct.region; \
  assign axi_if.ar_user   = ar_struct.user;

`define AXI_ASSIGN_TO_R(r_struct, axi_if) \
  assign r_struct = '{                    \
    id:   axi_if.r_id,                    \
    data: axi_if.r_data,                  \
    resp: axi_if.r_resp,                  \
    last: axi_if.r_last,                  \
    user: axi_if.r_user                   \
  };

`define AXI_ASSIGN_FROM_R(axi_if, r_struct) \
  assign axi_if.r_id    = r_struct.id;      \
  assign axi_if.r_data  = r_struct.data;    \
  assign axi_if.r_resp  = r_struct.resp;    \
  assign axi_if.r_last  = r_struct.last;    \
  assign axi_if.r_user  = r_struct.user;

`define AXI_ASSIGN_TO_REQ(req_struct, axi_if)   \
  `AXI_ASSIGN_TO_AW(req_struct.aw, axi_if);     \
  assign req_struct.aw_valid = axi_if.aw_valid; \
  `AXI_ASSIGN_TO_W(req_struct.w, axi_if);       \
  assign req_struct.w_valid = axi_if.w_valid;   \
  assign req_struct.b_ready = axi_if.b_ready;   \
  `AXI_ASSIGN_TO_AR(req_struct.ar, axi_if);     \
  assign req_struct.ar_valid = axi_if.ar_valid; \
  assign req_struct.r_ready = axi_if.r_ready;

`define AXI_ASSIGN_FROM_REQ(axi_if, req_struct) \
  `AXI_ASSIGN_FROM_AW(axi_if, req_struct.aw)    \
  assign axi_if.aw_valid = req_struct.aw_valid; \
  `AXI_ASSIGN_FROM_W(axi_if, req_struct.w);     \
  assign axi_if.w_valid = req_struct.w_valid;   \
  assign axi_if.b_ready = req_struct.b_ready;   \
  `AXI_ASSIGN_FROM_AR(axi_if, req_struct.ar);   \
  assign axi_if.ar_valid = req_struct.ar_valid; \
  assign axi_if.r_ready = req_struct.r_ready;

`define AXI_ASSIGN_FROM_RESP(axi_if, resp_struct) \
  assign axi_if.aw_ready = resp_struct.aw_ready;  \
  assign axi_if.ar_ready = resp_struct.ar_ready;  \
  assign axi_if.w_ready = resp_struct.w_ready;    \
  assign axi_if.b_valid = resp_struct.b_valid;    \
  `AXI_ASSIGN_FROM_B(axi_if, resp_struct.b);      \
  assign axi_if.r_valid = resp_struct.r_valid;    \
  `AXI_ASSIGN_FROM_R(axi_if, resp_struct.r);

`define AXI_ASSIGN_TO_RESP(resp_struct, axi_if)   \
  assign resp_struct.aw_ready = axi_if.aw_ready;  \
  assign resp_struct.ar_ready = axi_if.ar_ready;  \
  assign resp_struct.w_ready = axi_if.w_ready;    \
  assign resp_struct.b_valid = axi_if.b_valid;    \
  `AXI_ASSIGN_TO_B(resp_struct.b, axi_if);        \
  assign resp_struct.r_valid = axi_if.r_valid;    \
  `AXI_ASSIGN_TO_R(resp_struct.r, axi_if);

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
