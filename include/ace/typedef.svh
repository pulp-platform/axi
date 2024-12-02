// Copyright (c) 2019 ETH Zurich, University of Bologna
// Copyright (c) 2022 PlanV GmbH
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

// Macros to define ACE Channel and Request/Response Structs

`ifndef ACE_TYPEDEF_SVH_
`define ACE_TYPEDEF_SVH_

`include "axi/typedef.svh"

////////////////////////////////////////////////////////////////////////////////////////////////////
// AXI4+ATOP Channel and Request/Response Structs (with snoop support)
//
// Usage Example:
// `ACE_TYPEDEF_AW_CHAN_T(axi_aw_t, axi_addr_t, axi_id_t, axi_user_t)
// `ACE_TYPEDEF_AR_CHAN_T(axi_ar_t, axi_addr_t, axi_id_t, axi_user_t)
// `ACE_TYPEDEF_R_CHAN_T(axi_r_t, axi_data_t, axi_id_t, axi_user_t)
// `ACE_TYPEDEF_REQ_T(axi_req_t, axi_aw_t, axi_w_t, axi_ar_t)
// `ACE_TYPEDEF_RESP_T(axi_resp_t, axi_b_t, axi_r_t)
`define ACE_TYPEDEF_AW_CHAN_T(aw_chan_t, addr_t, id_t, user_t)  \
  typedef struct packed {                                       \
    id_t                id;                                       \
    addr_t              addr;                                     \
    axi_pkg::len_t      len;                                      \
    axi_pkg::size_t     size;                                     \
    axi_pkg::burst_t    burst;                                    \
    logic               lock;                                     \
    axi_pkg::cache_t    cache;                                    \
    axi_pkg::prot_t     prot;                                     \
    axi_pkg::qos_t      qos;                                      \
    axi_pkg::region_t   region;                                   \
    axi_pkg::atop_t     atop;                                     \
    user_t              user;                                     \
    ace_pkg::awsnoop_t  snoop;                                  \
    ace_pkg::axbar_t      bar;                                      \
    ace_pkg::axdomain_t   domain;                                   \
    ace_pkg::awunique_t awunique;                                 \
  } aw_chan_t;
`define ACE_TYPEDEF_AR_CHAN_T(ar_chan_t, addr_t, id_t, user_t)  \
  typedef struct packed {                                         \
    id_t                id;                                       \
    addr_t              addr;                                     \
    axi_pkg::len_t      len;                                      \
    axi_pkg::size_t     size;                                     \
    axi_pkg::burst_t    burst;                                    \
    logic               lock;                                     \
    axi_pkg::cache_t    cache;                                    \
    axi_pkg::prot_t     prot;                                     \
    axi_pkg::qos_t      qos;                                      \
    axi_pkg::region_t   region;                                   \
    user_t              user;                                     \
    ace_pkg::arsnoop_t  snoop;                                  \
    ace_pkg::axbar_t      bar;                                      \
    ace_pkg::axdomain_t   domain;                                   \
  } ar_chan_t;
`define ACE_TYPEDEF_R_CHAN_T(r_chan_t, data_t, id_t, user_t)  \
  typedef struct packed {                                        \
    id_t              id;                                       \
    data_t            data;                                     \
    ace_pkg::rresp_t  resp;                                    \
    logic             last;                                     \
    user_t            user;                                     \
  } r_chan_t;
`define ACE_TYPEDEF_REQ_T(req_t, aw_chan_t, w_chan_t, ar_chan_t)  \
  typedef struct packed {                                         \
    aw_chan_t aw;                                             \
    logic     aw_valid;                                           \
    w_chan_t  w;                                                  \
    logic     w_valid;                                            \
    logic     b_ready;                                            \
    ar_chan_t ar;                                             \
    logic     ar_valid;                                           \
    logic     r_ready;                                            \
    logic     wack;                                               \
    logic     rack;                                               \
  } req_t;
`define ACE_TYPEDEF_RESP_T(resp_t, b_chan_t, r_chan_t)  \
  typedef struct packed {                               \
    logic     aw_ready;                                 \
    logic     ar_ready;                                 \
    logic     w_ready;                                  \
    logic     b_valid;                                  \
    b_chan_t  b;                                        \
    logic     r_valid;                                  \
    r_chan_t  r;                                        \
  } resp_t;
////////////////////////////////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////////////////////////////////
// All AXI4+ATOP Channels and Request/Response Structs in One Macro (with snoop support)
//
// This can be used whenever the user is not interested in "precise" control of the naming of the
// individual channels.
//
// Usage Example:
// `AXI_TYPEDEF_ALL(axi, addr_t, id_t, data_t, strb_t, user_t)
//
// This defines `axi_req_t` and `axi_resp_t` request/response structs as well as `axi_aw_chan_t`,
// `axi_w_chan_t`, `axi_b_chan_t`, `axi_ar_chan_t`, and `axi_r_chan_t` channel structs.
`define ACE_TYPEDEF_ALL(__name, __addr_t, __id_t, __data_t, __strb_t, __user_t)                 \
  `ACE_TYPEDEF_AW_CHAN_T(__name``_aw_chan_t, __addr_t, __id_t, __user_t)                    \
  `AXI_TYPEDEF_W_CHAN_T(__name``_w_chan_t, __data_t, __strb_t, __user_t)                        \
  `AXI_TYPEDEF_B_CHAN_T(__name``_b_chan_t, __id_t, __user_t)                                    \
  `ACE_TYPEDEF_AR_CHAN_T(__name``_ar_chan_t, __addr_t, __id_t, __user_t)                    \
  `ACE_TYPEDEF_R_CHAN_T(__name``_r_chan_t, __data_t, __id_t, __user_t)                      \
  `ACE_TYPEDEF_REQ_T(__name``_req_t, __name``_aw_chan_t, __name``_w_chan_t, __name``_ar_chan_t) \
  `ACE_TYPEDEF_RESP_T(__name``_resp_t, __name``_b_chan_t, __name``_r_chan_t)
////////////////////////////////////////////////////////////////////////////////////////////////////
// Usage Example:
// `SNOOP_TYPEDEF_AC_CHAN_T(snoop_ac_t, snoop_addr_t)
// 'SNOOP_TYPEDEF_CD_CHAN_T(snoop_cd_t, snoop_data_t)
// `SNOOP_TYPEDEF_REQ_T(snoop_req_t, snoop_ac_t)
// `SNOOP_TYPEDEF_RESP_T(snoop_resp_t, snoop_cd_t, snoop_cr_t)
`define SNOOP_TYPEDEF_AC_CHAN_T(ac_chan_t, addr_t)              \
  typedef struct packed {                                       \
    addr_t                addr;                                 \
    ace_pkg::acsnoop_t  snoop;                              \
    ace_pkg::acprot_t   prot;                               \
  } ac_chan_t;
`define SNOOP_TYPEDEF_CD_CHAN_T(cd_chan_t, data_t)              \
  typedef struct packed {                                       \
    data_t                data;                                 \
    logic                 last;                                 \
  } cd_chan_t;
`define SNOOP_TYPEDEF_CR_CHAN_T(cr_chan_t)                      \
   typedef ace_pkg::crresp_t     cr_chan_t;
`define SNOOP_TYPEDEF_REQ_T(req_t, ac_chan_t)      \
  typedef struct packed {                                       \
    logic     ac_valid;                                         \
    logic     cd_ready;                                         \
    ac_chan_t ac;                                               \
    logic     cr_ready;                                         \
  } req_t;
`define SNOOP_TYPEDEF_RESP_T(resp_t, cd_chan_t, cr_chan_t)      \
  typedef struct packed {                                       \
    logic     ac_ready;                                         \
    logic     cd_valid;                                         \
    cd_chan_t cd;                                               \
    logic     cr_valid;                                         \
    cr_chan_t cr_resp;                                          \
  } resp_t;
////////////////////////////////////////////////////////////////////////////////////////////////////

// Usage Example:
// `SNOOP_TYPEDEF_ALL(snoop, addr_t, data_t)
//
// This defines `snoop_req_t` and `snoop_resp_t` request/response structs as well as `snoop_ac_chan_t`,
// `snoop_cd_chan_t` and `snoop_cr_chan_t` channel structs.
  `define SNOOP_TYPEDEF_ALL(__name, __addr_t, __data_t)               \
  `SNOOP_TYPEDEF_AC_CHAN_T(__name``_aw_chan_t, __addr_t)              \
  `SNOOP_TYPEDEF_CR_CHAN_T(__name``_cr_chan_t)                        \
  `SNOOP_TYPEDEF_CD_CHAN_T(__name``_cd_chan_t, __data_t)              \
  `SNOOP_TYPEDEF_REQ_T(__name``_req_t, __name``_ac_chan_t)            \
  `SNOOP_TYPEDEF_RESP_T(__name``_resp_t, __name``_cd_chan_t, __name``_cr_chan_t)
////////////////////////////////////////////////////////////////////////////////////////////////////

`endif
