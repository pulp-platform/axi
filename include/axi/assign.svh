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

// Assign an AXI4 master interface to a slave interface, as in `assign slv = mst;`.
`define AXI_ASSIGN(slv, mst)              \
  assign slv.aw_id      = mst.aw_id;      \
  assign slv.aw_addr    = mst.aw_addr;    \
  assign slv.aw_len     = mst.aw_len;     \
  assign slv.aw_size    = mst.aw_size;    \
  assign slv.aw_burst   = mst.aw_burst;   \
  assign slv.aw_lock    = mst.aw_lock;    \
  assign slv.aw_cache   = mst.aw_cache;   \
  assign slv.aw_prot    = mst.aw_prot;    \
  assign slv.aw_qos     = mst.aw_qos;     \
  assign slv.aw_region  = mst.aw_region;  \
  assign slv.aw_atop    = mst.aw_atop;    \
  assign slv.aw_user    = mst.aw_user;    \
  assign slv.aw_valid   = mst.aw_valid;   \
  assign mst.aw_ready   = slv.aw_ready;   \
                                          \
  assign slv.w_data     = mst.w_data;     \
  assign slv.w_strb     = mst.w_strb;     \
  assign slv.w_last     = mst.w_last;     \
  assign slv.w_user     = mst.w_user;     \
  assign slv.w_valid    = mst.w_valid;    \
  assign mst.w_ready    = slv.w_ready;    \
                                          \
  assign mst.b_id       = slv.b_id;       \
  assign mst.b_resp     = slv.b_resp;     \
  assign mst.b_user     = slv.b_user;     \
  assign mst.b_valid    = slv.b_valid;    \
  assign slv.b_ready    = mst.b_ready;    \
                                          \
  assign slv.ar_id      = mst.ar_id;      \
  assign slv.ar_addr    = mst.ar_addr;    \
  assign slv.ar_len     = mst.ar_len;     \
  assign slv.ar_size    = mst.ar_size;    \
  assign slv.ar_burst   = mst.ar_burst;   \
  assign slv.ar_lock    = mst.ar_lock;    \
  assign slv.ar_cache   = mst.ar_cache;   \
  assign slv.ar_prot    = mst.ar_prot;    \
  assign slv.ar_qos     = mst.ar_qos;     \
  assign slv.ar_region  = mst.ar_region;  \
  assign slv.ar_user    = mst.ar_user;    \
  assign slv.ar_valid   = mst.ar_valid;   \
  assign mst.ar_ready   = slv.ar_ready;   \
                                          \
  assign mst.r_id       = slv.r_id;       \
  assign mst.r_data     = slv.r_data;     \
  assign mst.r_resp     = slv.r_resp;     \
  assign mst.r_last     = slv.r_last;     \
  assign mst.r_user     = slv.r_user;     \
  assign mst.r_valid    = slv.r_valid;    \
  assign slv.r_ready    = mst.r_ready;

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
