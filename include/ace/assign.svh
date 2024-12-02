// Copyright (c) 2014-2018 ETH Zurich, University of Bologna
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

// Macros to assign ACE Interfaces and Structs

`ifndef ACE_ASSIGN_SVH_
`define ACE_ASSIGN_SVH_

`include "axi/assign.svh"

////////////////////////////////////////////////////////////////////////////////////////////////////
// Internal implementation for assigning one ACE struct or interface to another struct or interface.
// The path to the signals on each side is defined by the `__sep*` arguments.  The `__opt_as`
// argument allows to use this standalone (with `__opt_as = assign`) or in assignments inside
// processes (with `__opt_as` void).
`define __ACE_TO_AW(__opt_as, __lhs, __lhs_sep, __rhs, __rhs_sep)   \
  __opt_as __lhs``__lhs_sep``id     = __rhs``__rhs_sep``id;         \
  __opt_as __lhs``__lhs_sep``addr   = __rhs``__rhs_sep``addr;       \
  __opt_as __lhs``__lhs_sep``len    = __rhs``__rhs_sep``len;        \
  __opt_as __lhs``__lhs_sep``size   = __rhs``__rhs_sep``size;       \
  __opt_as __lhs``__lhs_sep``burst  = __rhs``__rhs_sep``burst;      \
  __opt_as __lhs``__lhs_sep``lock   = __rhs``__rhs_sep``lock;       \
  __opt_as __lhs``__lhs_sep``cache  = __rhs``__rhs_sep``cache;      \
  __opt_as __lhs``__lhs_sep``prot   = __rhs``__rhs_sep``prot;       \
  __opt_as __lhs``__lhs_sep``qos    = __rhs``__rhs_sep``qos;        \
  __opt_as __lhs``__lhs_sep``region = __rhs``__rhs_sep``region;     \
  __opt_as __lhs``__lhs_sep``atop   = __rhs``__rhs_sep``atop;       \
  __opt_as __lhs``__lhs_sep``user   = __rhs``__rhs_sep``user;       \
  __opt_as __lhs``__lhs_sep``snoop   = __rhs``__rhs_sep``snoop; \
  __opt_as __lhs``__lhs_sep``bar   = __rhs``__rhs_sep``bar;         \
  __opt_as __lhs``__lhs_sep``domain   = __rhs``__rhs_sep``domain;   \
  __opt_as __lhs``__lhs_sep``awunique   = __rhs``__rhs_sep``awunique;


`define __ACE_TO_AR(__opt_as, __lhs, __lhs_sep, __rhs, __rhs_sep)   \
  __opt_as __lhs``__lhs_sep``id     = __rhs``__rhs_sep``id;         \
  __opt_as __lhs``__lhs_sep``addr   = __rhs``__rhs_sep``addr;       \
  __opt_as __lhs``__lhs_sep``len    = __rhs``__rhs_sep``len;        \
  __opt_as __lhs``__lhs_sep``size   = __rhs``__rhs_sep``size;       \
  __opt_as __lhs``__lhs_sep``burst  = __rhs``__rhs_sep``burst;      \
  __opt_as __lhs``__lhs_sep``lock   = __rhs``__rhs_sep``lock;       \
  __opt_as __lhs``__lhs_sep``cache  = __rhs``__rhs_sep``cache;      \
  __opt_as __lhs``__lhs_sep``prot   = __rhs``__rhs_sep``prot;       \
  __opt_as __lhs``__lhs_sep``qos    = __rhs``__rhs_sep``qos;        \
  __opt_as __lhs``__lhs_sep``region = __rhs``__rhs_sep``region;     \
  __opt_as __lhs``__lhs_sep``user   = __rhs``__rhs_sep``user;       \
  __opt_as __lhs``__lhs_sep``snoop = __rhs``__rhs_sep``snoop;   \
  __opt_as __lhs``__lhs_sep``bar = __rhs``__rhs_sep``bar;           \
  __opt_as __lhs``__lhs_sep``domain = __rhs``__rhs_sep``domain;
`define __ACE_TO_R(__opt_as, __lhs, __lhs_sep, __rhs, __rhs_sep)    \
  __opt_as __lhs``__lhs_sep``id     = __rhs``__rhs_sep``id;         \
  __opt_as __lhs``__lhs_sep``data   = __rhs``__rhs_sep``data;       \
  __opt_as __lhs``__lhs_sep``resp   = __rhs``__rhs_sep``resp;       \
  __opt_as __lhs``__lhs_sep``last   = __rhs``__rhs_sep``last;       \
  __opt_as __lhs``__lhs_sep``user   = __rhs``__rhs_sep``user;
`define __ACE_TO_REQ(__opt_as, __lhs, __lhs_sep, __rhs, __rhs_sep)  \
  `__ACE_TO_AW(__opt_as, __lhs.aw, __lhs_sep, __rhs.aw, __rhs_sep)  \
  __opt_as __lhs.aw_valid = __rhs.aw_valid;                         \
  `__AXI_TO_W(__opt_as, __lhs.w, __lhs_sep, __rhs.w, __rhs_sep)     \
  __opt_as __lhs.w_valid = __rhs.w_valid;                           \
  __opt_as __lhs.b_ready = __rhs.b_ready;                           \
  `__ACE_TO_AR(__opt_as, __lhs.ar, __lhs_sep, __rhs.ar, __rhs_sep)  \
  __opt_as __lhs.ar_valid = __rhs.ar_valid;                         \
  __opt_as __lhs.r_ready = __rhs.r_ready;                           \
  __opt_as __lhs.wack = __rhs.wack;                                 \
  __opt_as __lhs.rack = __rhs.rack;
`define __ACE_TO_RESP(__opt_as, __lhs, __lhs_sep, __rhs, __rhs_sep) \
  __opt_as __lhs.aw_ready = __rhs.aw_ready;                         \
  __opt_as __lhs.ar_ready = __rhs.ar_ready;                         \
  __opt_as __lhs.w_ready = __rhs.w_ready;                           \
  __opt_as __lhs.b_valid = __rhs.b_valid;                           \
  `__AXI_TO_B(__opt_as, __lhs.b, __lhs_sep, __rhs.b, __rhs_sep)     \
  __opt_as __lhs.r_valid = __rhs.r_valid;                           \
  `__ACE_TO_R(__opt_as, __lhs.r, __lhs_sep, __rhs.r, __rhs_sep)
////////////////////////////////////////////////////////////////////////////////////////////////////


////////////////////////////////////////////////////////////////////////////////////////////////////
// Assigning one AXI4+ATOP interface to another, as if you would do `assign slv = mst;`
//
// The channel assignments `ACE_ASSIGN_XX(dst, src)` assign all payload and the valid signal of the
// `XX` channel from the `src` to the `dst` interface and they assign the ready signal from the
// `src` to the `dst` interface.
// The interface assignment `AXI_ASSIGN(dst, src)` assigns all channels including handshakes as if
// `src` was the master of `dst`.
//
// Usage Example:
// `ACE_ASSIGN(slv, mst)
// `ACE_ASSIGN_AW(dst, src)
// `ACE_ASSIGN_R(dst, src)
`define ACE_ASSIGN_AW(dst, src)               \
  `__ACE_TO_AW(assign, dst.aw, _, src.aw, _)  \
  assign dst.aw_valid = src.aw_valid;         \
  assign src.aw_ready = dst.aw_ready;

`define ACE_ASSIGN_AR(dst, src)               \
  `__ACE_TO_AR(assign, dst.ar, _, src.ar, _)  \
  assign dst.ar_valid = src.ar_valid;         \
  assign src.ar_ready = dst.ar_ready;
`define ACE_ASSIGN_R(dst, src)                \
  `__ACE_TO_R(assign, dst.r, _, src.r, _)     \
  assign dst.r_valid  = src.r_valid;          \
  assign src.r_ready  = dst.r_ready;
`define ACE_ASSIGN(slv, mst)  \
  `ACE_ASSIGN_AW(slv, mst)    \
  `AXI_ASSIGN_W(slv, mst)     \
  `AXI_ASSIGN_B(mst, slv)     \
  `ACE_ASSIGN_AR(slv, mst)    \
  `ACE_ASSIGN_R(mst, slv)     \
  assign slv.wack = mst.wack; \
  assign slv.rack = mst.rack;

////////////////////////////////////////////////////////////////////////////////////////////////////


////////////////////////////////////////////////////////////////////////////////////////////////////
// Assigning a AXI4+ATOP interface to a monitor modport, as if you would do `assign mon = axi_if;`
//
// The channel assignment `ACE_ASSIGN_MONITOR(mon_dv, axi_if)` assigns all signals from `axi_if`
// to the `mon_dv` interface.
//
// Usage Example:
// `ACE_ASSIGN_MONITOR(mon_dv, axi_if)
`define ACE_ASSIGN_MONITOR(mon_dv, axi_if)          \
  `__ACE_TO_AW(assign, mon_dv.aw, _, axi_if.aw, _)  \
  assign mon_dv.aw_valid  = axi_if.aw_valid;        \
  assign mon_dv.aw_ready  = axi_if.aw_ready;        \
  `__AXI_TO_W(assign, mon_dv.w, _, axi_if.w, _)     \
  assign mon_dv.w_valid   = axi_if.w_valid;         \
  assign mon_dv.w_ready   = axi_if.w_ready;         \
  `__AXI_TO_B(assign, mon_dv.b, _, axi_if.b, _)     \
  assign mon_dv.b_valid   = axi_if.b_valid;         \
  assign mon_dv.b_ready   = axi_if.b_ready;         \
  `__ACE_TO_AR(assign, mon_dv.ar, _, axi_if.ar, _)  \
  assign mon_dv.ar_valid  = axi_if.ar_valid;        \
  assign mon_dv.ar_ready  = axi_if.ar_ready;        \
  `__ACE_TO_R(assign, mon_dv.r, _, axi_if.r, _)     \
  assign mon_dv.r_valid   = axi_if.r_valid;         \
  assign mon_dv.r_ready   = axi_if.r_ready;         \
  assign mon_dv.wack   = axi_if.wack;               \
  assign mon_dv.rack   = axi_if.rack;
////////////////////////////////////////////////////////////////////////////////////////////////////


////////////////////////////////////////////////////////////////////////////////////////////////////
// Setting an interface from channel or request/response structs inside a process.
//
// The channel macros `ACE_SET_FROM_XX(axi_if, xx_struct)` set the payload signals of the `axi_if`
// interface from the signals in `xx_struct`.  They do not set the handshake signals.
// The request macro `ACE_SET_FROM_REQ(axi_if, req_struct)` sets all request channels (AW, W, AR)
// and the request-side handshake signals (AW, W, and AR valid and B and R ready) of the `axi_if`
// interface from the signals in `req_struct`.
// The response macro `ACE_SET_FROM_RESP(axi_if, resp_struct)` sets both response channels (B and R)
// and the response-side handshake signals (B and R valid and AW, W, and AR ready) of the `axi_if`
// interface from the signals in `resp_struct`.
//
// Usage Example:
// always_comb begin
//   `ACE_SET_FROM_REQ(my_if, my_req_struct)
// end
`define ACE_SET_FROM_AW(axi_if, aw_struct)      `__ACE_TO_AW(, axi_if.aw, _, aw_struct, .)
`define ACE_SET_FROM_AR(axi_if, ar_struct)      `__ACE_TO_AR(, axi_if.ar, _, ar_struct, .)
`define ACE_SET_FROM_R(axi_if, r_struct)        `__ACE_TO_R(, axi_if.r, _, r_struct, .)
`define ACE_SET_FROM_REQ(axi_if, req_struct)    `__ACE_TO_REQ(, axi_if, _, req_struct, .)
`define ACE_SET_FROM_RESP(axi_if, resp_struct)  `__ACE_TO_RESP(, axi_if, _, resp_struct, .)
////////////////////////////////////////////////////////////////////////////////////////////////////


////////////////////////////////////////////////////////////////////////////////////////////////////
// Assigning an interface from channel or request/response structs outside a process.
//
// The channel macros `ACE_ASSIGN_FROM_XX(axi_if, xx_struct)` assign the payload signals of the
// `axi_if` interface from the signals in `xx_struct`.  They do not assign the handshake signals.
// The request macro `ACE_ASSIGN_FROM_REQ(axi_if, req_struct)` assigns all request channels (AW, W,
// AR) and the request-side handshake signals (AW, W, and AR valid and B and R ready) of the
// `axi_if` interface from the signals in `req_struct`.
// The response macro `ACE_ASSIGN_FROM_RESP(axi_if, resp_struct)` assigns both response channels (B
// and R) and the response-side handshake signals (B and R valid and AW, W, and AR ready) of the
// `axi_if` interface from the signals in `resp_struct`.
//
// Usage Example:
// `ACE_ASSIGN_FROM_REQ(my_if, my_req_struct)
`define ACE_ASSIGN_FROM_AW(axi_if, aw_struct)     `__ACE_TO_AW(assign, axi_if.aw, _, aw_struct, .)
`define ACE_ASSIGN_FROM_AR(axi_if, ar_struct)     `__ACE_TO_AR(assign, axi_if.ar, _, ar_struct, .)
`define ACE_ASSIGN_FROM_R(axi_if, r_struct)       `__ACE_TO_R(assign, axi_if.r, _, r_struct, .)
`define ACE_ASSIGN_FROM_REQ(axi_if, req_struct)   `__ACE_TO_REQ(assign, axi_if, _, req_struct, .)
`define ACE_ASSIGN_FROM_RESP(axi_if, resp_struct) `__ACE_TO_RESP(assign, axi_if, _, resp_struct, .)
////////////////////////////////////////////////////////////////////////////////////////////////////


////////////////////////////////////////////////////////////////////////////////////////////////////
// Setting channel or request/response structs from an interface inside a process.
//
// The channel macros `ACE_SET_TO_XX(xx_struct, axi_if)` set the signals of `xx_struct` to the
// payload signals of that channel in the `axi_if` interface.  They do not set the handshake
// signals.
// The request macro `ACE_SET_TO_REQ(axi_if, req_struct)` sets all signals of `req_struct` (i.e.,
// request channel (AW, W, AR) payload and request-side handshake signals (AW, W, and AR valid and
// B and R ready)) to the signals in the `axi_if` interface.
// The response macro `ACE_SET_TO_RESP(axi_if, resp_struct)` sets all signals of `resp_struct`
// (i.e., response channel (B and R) payload and response-side handshake signals (B and R valid and
// AW, W, and AR ready)) to the signals in the `axi_if` interface.
//
// Usage Example:
// always_comb begin
//   `ACE_SET_TO_REQ(my_req_struct, my_if)
// end
`define ACE_SET_TO_AW(aw_struct, axi_if)     `__ACE_TO_AW(, aw_struct, ., axi_if.aw, _)
`define ACE_SET_TO_AR(ar_struct, axi_if)     `__ACE_TO_AR(, ar_struct, ., axi_if.ar, _)
`define ACE_SET_TO_R(r_struct, axi_if)       `__ACE_TO_R(, r_struct, ., axi_if.r, _)
`define ACE_SET_TO_REQ(req_struct, axi_if)   `__ACE_TO_REQ(, req_struct, ., axi_if, _)
`define ACE_SET_TO_RESP(resp_struct, axi_if) `__ACE_TO_RESP(, resp_struct, ., axi_if, _)
////////////////////////////////////////////////////////////////////////////////////////////////////


////////////////////////////////////////////////////////////////////////////////////////////////////
// Assigning channel or request/response structs from an interface outside a process.
//
// The channel macros `ACE_ASSIGN_TO_XX(xx_struct, axi_if)` assign the signals of `xx_struct` to the
// payload signals of that channel in the `axi_if` interface.  They do not assign the handshake
// signals.
// The request macro `ACE_ASSIGN_TO_REQ(axi_if, req_struct)` assigns all signals of `req_struct`
// (i.e., request channel (AW, W, AR) payload and request-side handshake signals (AW, W, and AR
// valid and B and R ready)) to the signals in the `axi_if` interface.
// The response macro `ACE_ASSIGN_TO_RESP(axi_if, resp_struct)` assigns all signals of `resp_struct`
// (i.e., response channel (B and R) payload and response-side handshake signals (B and R valid and
// AW, W, and AR ready)) to the signals in the `axi_if` interface.
//
// Usage Example:
// `ACE_ASSIGN_TO_REQ(my_req_struct, my_if)
`define ACE_ASSIGN_TO_AW(aw_struct, axi_if)     `__ACE_TO_AW(assign, aw_struct, ., axi_if.aw, _)
`define ACE_ASSIGN_TO_AR(ar_struct, axi_if)     `__ACE_TO_AR(assign, ar_struct, ., axi_if.ar, _)
`define ACE_ASSIGN_TO_R(r_struct, axi_if)       `__ACE_TO_R(assign, r_struct, ., axi_if.r, _)
`define ACE_ASSIGN_TO_REQ(req_struct, axi_if)   `__ACE_TO_REQ(assign, req_struct, ., axi_if, _)
`define ACE_ASSIGN_TO_RESP(resp_struct, axi_if) `__ACE_TO_RESP(assign, resp_struct, ., axi_if, _)
////////////////////////////////////////////////////////////////////////////////////////////////////


////////////////////////////////////////////////////////////////////////////////////////////////////
// Setting channel or request/response structs from another struct inside a process.
//
// The channel macros `ACE_SET_XX_STRUCT(lhs, rhs)` set the fields of the `lhs` channel struct to
// the fields of the `rhs` channel struct.  They do not set the handshake signals, which are not
// part of channel structs.
// The request macro `ACE_SET_REQ_STRUCT(lhs, rhs)` sets all fields of the `lhs` request struct to
// the fields of the `rhs` request struct.  This includes all request channel (AW, W, AR) payload
// and request-side handshake signals (AW, W, and AR valid and B and R ready).
// The response macro `ACE_SET_RESP_STRUCT(lhs, rhs)` sets all fields of the `lhs` response struct
// to the fields of the `rhs` response struct.  This includes all response channel (B and R) payload
// and response-side handshake signals (B and R valid and AW, W, and R ready).
//
// Usage Example:
// always_comb begin
//   `AXI_SET_S_REQ_STRUCT(my_req_struct, another_req_struct)
// end
`define ACE_SET_AW_STRUCT(lhs, rhs)     `__ACE_TO_AW(, lhs, ., rhs, .)
`define ACE_SET_AR_STRUCT(lhs, rhs)     `__ACE_TO_AR(, lhs, ., rhs, .)
`define ACE_SET_R_STRUCT(lhs, rhs)       `__ACE_TO_R(, lhs, ., rhs, .)
`define ACE_SET_REQ_STRUCT(lhs, rhs)   `__ACE_TO_REQ(, lhs, ., rhs, .)
`define ACE_SET_RESP_STRUCT(lhs, rhs) `__ACE_TO_RESP(, lhs, ., rhs, .)
////////////////////////////////////////////////////////////////////////////////////////////////////


////////////////////////////////////////////////////////////////////////////////////////////////////
// Assigning channel or request/response structs from another struct outside a process.
//
// The channel macros `ACE_ASSIGN_XX_STRUCT(lhs, rhs)` assign the fields of the `lhs` channel struct
// to the fields of the `rhs` channel struct.  They do not assign the handshake signals, which are
// not part of the channel structs.
// The request macro `ACE_ASSIGN_REQ_STRUCT(lhs, rhs)` assigns all fields of the `lhs` request
// struct to the fields of the `rhs` request struct.  This includes all request channel (AW, W, AR)
// payload and request-side handshake signals (AW, W, and AR valid and B and R ready).
// The response macro `ACE_ASSIGN_RESP_STRUCT(lhs, rhs)` assigns all fields of the `lhs` response
// struct to the fields of the `rhs` response struct.  This includes all response channel (B and R)
// payload and response-side handshake signals (B and R valid and AW, W, and R ready).
//
// Usage Example:
// `ACE_ASSIGN_REQ_STRUCT(my_req_struct, another_req_struct)
`define ACE_ASSIGN_AW_STRUCT(lhs, rhs)     `__ACE_TO_AW(assign, lhs, ., rhs, .)
`define ACE_ASSIGN_AR_STRUCT(lhs, rhs)     `__ACE_TO_AR(assign, lhs, ., rhs, .)
`define ACE_ASSIGN_R_STRUCT(lhs, rhs)       `__ACE_TO_R(assign, lhs, ., rhs, .)
`define ACE_ASSIGN_REQ_STRUCT(lhs, rhs)   `__ACE_TO_REQ(assign, lhs, ., rhs, .)
`define ACE_ASSIGN_RESP_STRUCT(lhs, rhs) `__ACE_TO_RESP(assign, lhs, ., rhs, .)
////////////////////////////////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////////////////////////////////
// Internal implementation for assigning one SNOOP struct or interface to another struct or interface.
// The path to the signals on each side is defined by the `__sep*` arguments.  The `__opt_as`
// argument allows to use this standalone (with `__opt_as = assign`) or in assignments inside
// processes (with `__opt_as` void).
`define __SNOOP_TO_AC(__opt_as, __lhs, __lhs_sep, __rhs, __rhs_sep)       \
  __opt_as __lhs``__lhs_sep``addr      = __rhs``__rhs_sep``addr;          \
  __opt_as __lhs``__lhs_sep``snoop   = __rhs``__rhs_sep``snoop;       \
  __opt_as __lhs``__lhs_sep``prot    = __rhs``__rhs_sep``prot;
`define __SNOOP_TO_CD(__opt_as, __lhs, __lhs_sep, __rhs, __rhs_sep)       \
  __opt_as __lhs``__lhs_sep``data   = __rhs``__rhs_sep``data;             \
  __opt_as __lhs``__lhs_sep``last   = __rhs``__rhs_sep``last;
`define __SNOOP_TO_CR(__opt_as, __lhs, __lhs_sep, __rhs, __rhs_sep)       \
  __opt_as __lhs``__lhs_sep``resp   = __rhs``__rhs_sep``resp;
`define __SNOOP_TO_REQ(__opt_as, __lhs, __lhs_sep, __rhs, __rhs_sep)      \
  `__SNOOP_TO_AC(__opt_as, __lhs.ac, __lhs_sep, __rhs.ac, __rhs_sep)      \
  __opt_as __lhs.ac_valid = __rhs.ac_valid;                               \
  __opt_as __lhs.cd_ready = __rhs.cd_ready;                               \
  __opt_as __lhs.cr_ready = __rhs.cr_ready;
`define __SNOOP_TO_RESP(__opt_as, __lhs, __lhs_sep, __rhs, __rhs_sep)     \
  __opt_as __lhs.ac_ready = __rhs.ac_ready;                               \
  __opt_as __lhs.cd_valid = __rhs.cd_valid;                               \
  `__SNOOP_TO_CD(__opt_as, __lhs.cd, __lhs_sep, __rhs.cd, __rhs_sep)      \
  __opt_as __lhs.cr_valid = __rhs.cr_valid;                               \
  __opt_as __lhs.cr_resp = __rhs.cr_resp;
////////////////////////////////////////////////////////////////////////////////////////////////////


////////////////////////////////////////////////////////////////////////////////////////////////////
// Assigning one SNOOP+ATOP interface to another, as if you would do `assign slv = mst;`
//
// The channel assignments `SNOOP_ASSIGN_XX(dst, src)` assign all payload and the valid signal of the
// `XX` channel from the `src` to the `dst` interface and they assign the ready signal from the
// `src` to the `dst` interface.
// The interface assignment `SNOOP_ASSIGN(dst, src)` assigns all channels including handshakes as if
// `src` was the master of `dst`.
//
// Usage Example:
// `SNOOP_ASSIGN(slv, mst)
// `SNOOP_ASSIGN_AC(dst, src)
// `SNOOP_ASSIGN_Cd(dst, src)
`define SNOOP_ASSIGN_AC(dst, src)               \
  `__SNOOP_TO_AC(assign, dst.ac, _, src.ac, _)  \
  assign dst.ac_valid = src.ac_valid;         \
  assign src.ac_ready = dst.ac_ready;
`define SNOOP_ASSIGN_CD(dst, src)                \
  `__SNOOP_TO_CD(assign, dst.cd, _, src.cd, _)     \
  assign dst.cd_valid  = src.cd_valid;          \
  assign src.cd_ready  = dst.cd_ready;
`define SNOOP_ASSIGN_CR(dst, src)                \
  `__SNOOP_TO_CR(assign, dst.cr, _, src.cr, _)     \
  assign dst.cr_valid  = src.cr_valid;          \
  assign src.cr_ready  = dst.cr_ready;
`define SNOOP_ASSIGN(slv, mst)  \
  `SNOOP_ASSIGN_AC(slv, mst)    \
  `SNOOP_ASSIGN_CD(mst, slv)    \
  `SNOOP_ASSIGN_CR(mst, slv)
////////////////////////////////////////////////////////////////////////////////////////////////////
// The channel assignment `SNOOP_ASSIGN_MONITOR(mon_dv, snoop_if)` assigns all signals from `snoop_if`
// to the `mon_dv` interface.
//
// Usage Example:
// `SNOOP_ASSIGN_MONITOR(mon_dv, snoop_if)
`define SNOOP_ASSIGN_MONITOR(mon_dv, snoop_if)          \
  `__SNOOP_TO_AC(assign, mon_dv.ac, _, snoop_if.ac, _)  \
  assign mon_dv.ac_valid  = snoop_if.ac_valid;        \
  assign mon_dv.ac_ready  = snoop_if.ac_ready;        \
  `__SNOOP_TO_CD(assign, mon_dv.cd, _, snoop_if.cd, _)     \
  assign mon_dv.cd_valid   = snoop_if.cd_valid;         \
  assign mon_dv.cd_ready   = snoop_if.cd_ready;         \
  `__SNOOP_TO_CR(assign, mon_dv.cr, _, snoop_if.cr, _)     \
  assign mon_dv.cr_ready   = snoop_if.cr_ready;         \
  assign mon_dv.cr_valid   = snoop_if.cr_valid;

////////////////////////////////////////////////////////////////////////////////////////////////////
// Setting an interface from channel or request/response structs inside a process.
//
// The channel macros `SNOOP_SET_FROM_XX(snoop_if, xx_struct)` set the payload signals of the `snoop_if`
// interface from the signals in `xx_struct`.  They do not set the handshake signals.
// The request macro `SNOOP_SET_FROM_REQ(snoop_if, req_struct)` sets all request channels (AC)
// and the request-side handshake signals (AC valid, CD and CR ready) of the `snoop_if`
// interface from the signals in `req_struct`.
// The response macro `SNOOP_SET_FROM_RESP(snoop_if, resp_struct)` sets both response channels (CD and CR)
// and the response-side handshake signals (CD and CR valid, AC ready) of the `snoop_if`
// interface from the signals in `resp_struct`.
//
// Usage Example:
// always_comb begin
//   `SNOOP_SET_FROM_REQ(my_if, my_req_struct)
// end
`define SNOOP_SET_FROM_AC(snoop_if, ac_struct)      `__SNOOP_TO_AC(, snoop_if.ac, _, ac_struct, .)
`define SNOOP_SET_FROM_CD(snoop_if, cd_struct)      `__SNOOP_TO_CD(, snoop_if.cd, _, cd_struct, .)
`define SNOOP_SET_FROM_CR(snoop_if, cr_struct)        `__SNOOP_TO_CR(, snoop_if.cr, _, cr_struct, .)
`define SNOOP_SET_FROM_REQ(snoop_if, req_struct)    `__SNOOP_TO_REQ(, snoop_if, _, req_struct, .)
`define SNOOP_SET_FROM_RESP(snoop_if, resp_struct)  `__SNOOP_TO_RESP(, snoop_if, _, resp_struct, .)
////////////////////////////////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////////////////////////////////
// Assigning an interface from channel or request/response structs outside a process.
//
// The channel macros `SNOOP_ASSIGN_FROM_XX(snoop_if, xx_struct)` assign the payload signals of the
// `snoop_if` interface from the signals in `xx_struct`.  They do not assign the handshake signals.
// The request macro `SNOOP_ASSIGN_FROM_REQ(snoop_if, req_struct)` assigns all request channels (AC)
// and the request-side handshake signals (AC valid and CD and CR ready) of the `snoop_if` interface
// from the signals in `req_struct`.The response macro `SNOOP_ASSIGN_FROM_RESP(snoop_if, resp_struct)`
// assigns both response channels (CD and CR) and the response-side handshake signals (CD and CR valid
// and AC ready) of the `snoop_if` interface from the signals in `resp_struct`.
//
// Usage Example:
// `SNOOP_ASSIGN_FROM_REQ(my_if, my_req_struct)
`define SNOOP_ASSIGN_FROM_AC(snoop_if, ac_struct)     `__SNOOP_TO_AC(assign, snoop_if.ac, _, ac_struct, .)
`define SNOOP_ASSIGN_FROM_CD(snoop_if, cd_struct)     `__SNOOP_TO_CD(assign, snoop_if.cd, _, cd_struct, .)
`define SNOOP_ASSIGN_FROM_CR(snoop_if, cr_struct)       `__SNOOP_TO_CR(assign, snoop_if.cr, _, cr_struct, .)
`define SNOOP_ASSIGN_FROM_REQ(snoop_if, req_struct)   `__SNOOP_TO_REQ(assign, snoop_if, _, req_struct, .)
`define SNOOP_ASSIGN_FROM_RESP(snoop_if, resp_struct) `__SNOOP_TO_RESP(assign, snoop_if, _, resp_struct, .)
////////////////////////////////////////////////////////////////////////////////////////////////////


////////////////////////////////////////////////////////////////////////////////////////////////////
// Setting channel or request/response structs from an interface inside a process.
//
// The channel macros `SNOOP_SET_TO_XX(xx_struct, snoop_if)` set the signals of `xx_struct` to the
// payload signals of that channel in the `snoop_if` interface.  They do not set the handshake
// signals.
// The request macro `SNOOP_SET_TO_REQ(snoop_if, req_struct)` sets all signals of `req_struct` (i.e.,
// request channel (AC) payload and request-side handshake signals (AC valid and
// CD and CR ready)) to the signals in the `snoop_if` interface.
// The response macro `SNOOP_SET_TO_RESP(snoop_if, resp_struct)` sets all signals of `resp_struct`
// (i.e., response channel (CD and CR) payload and response-side handshake signals (CD and CR valid and
// AC ready)) to the signals in the `snoop_if` interface.
//
// Usage Example:
// always_comb begin
//   `SNOOP_SET_TO_REQ(my_req_struct, my_if)
// end
`define SNOOP_SET_TO_AC(ac_struct, snoop_if)     `__SNOOP_TO_AC(, ac_struct, ., snoop_if.ac, _)
`define SNOOP_SET_TO_CD(cd_struct, snoop_if)     `__SNOOP_TO_CD(, cd_struct, ., snoop_if.cd, _)
`define SNOOP_SET_TO_CR(cr_struct, snoop_if)       `__SNOOP_TO_CR(, cr_struct, ., snoop_if.cr, _)
`define SNOOP_SET_TO_REQ(req_struct, snoop_if)   `__SNOOP_TO_REQ(, req_struct, ., snoop_if, _)
`define SNOOP_SET_TO_RESP(resp_struct, snoop_if) `__SNOOP_TO_RESP(, resp_struct, ., snoop_if, _)
////////////////////////////////////////////////////////////////////////////////////////////////////


////////////////////////////////////////////////////////////////////////////////////////////////////
// Assigning channel or request/response structs from an interface outside a process.
//
// The channel macros `SNOOP_ASSIGN_TO_XX(xx_struct, snoop_if)` assign the signals of `xx_struct` to the
// payload signals of that channel in the `snoop_if` interface.  They do not assign the handshake
// signals.
// The request macro `SNOOP_ASSIGN_TO_REQ(snoop_if, req_struct)` assigns all signals of `req_struct`
// (i.e., request channel (AC) payload and request-side handshake signals (AC valid and CD and CR ready))
// to the signals in the `snoop_if` interface.
// The response macro `SNOOP_ASSIGN_TO_RESP(snoop_if, resp_struct)` assigns all signals of `resp_struct`
// (i.e., response channel (CD and CR) payload and response-side handshake signals (CD and CR valid and
// AC ready)) to the signals in the `snoop_if` interface.
//
// Usage Example:
// `SNOOP_ASSIGN_TO_REQ(my_req_struct, my_if)
`define SNOOP_ASSIGN_TO_AC(aw_struct, snoop_if)     `__SNOOP_TO_AC(assign, aw_struct, ., snoop_if.aw, _)
`define SNOOP_ASSIGN_TO_CD(ar_struct, snoop_if)     `__SNOOP_TO_CD(assign, ar_struct, ., snoop_if.ar, _)
`define SNOOP_ASSIGN_TO_CR(r_struct, snoop_if)       `__SNOOP_TO_CR(assign, r_struct, ., snoop_if.r, _)
`define SNOOP_ASSIGN_TO_REQ(req_struct, snoop_if)   `__SNOOP_TO_REQ(assign, req_struct, ., snoop_if, _)
`define SNOOP_ASSIGN_TO_RESP(resp_struct, snoop_if) `__SNOOP_TO_RESP(assign, resp_struct, ., snoop_if, _)
////////////////////////////////////////////////////////////////////////////////////////////////////


////////////////////////////////////////////////////////////////////////////////////////////////////
// Setting channel or request/response structs from another struct inside a process.
//
// The channel macros `SNOOP_SET_XX_STRUCT(lhs, rhs)` set the fields of the `lhs` channel struct to
// the fields of the `rhs` channel struct.  They do not set the handshake signals, which are not
// part of channel structs.
// The request macro `SNOOP_SET_REQ_STRUCT(lhs, rhs)` sets all fields of the `lhs` request struct to
// the fields of the `rhs` request struct.  This includes all request channel (AC) payload
// and request-side handshake signals (AC valid and CD and CR ready).
// The response macro `SNOOP_SET_RESP_STRUCT(lhs, rhs)` sets all fields of the `lhs` response struct
// to the fields of the `rhs` response struct.  This includes all response channel (CD and CR) payload
// and response-side handshake signals (CD and CR valid and AC ready).
//
// Usage Example:
// always_comb begin
//   `SNOOP_SET_S_REQ_STRUCT(my_req_struct, another_req_struct)
// end
`define SNOOP_SET_AC_STRUCT(lhs, rhs)     `__SNOOP_TO_AC(, lhs, ., rhs, .)
`define SNOOP_SET_CD_STRUCT(lhs, rhs)     `__SNOOP_TO_CD(, lhs, ., rhs, .)
`define SNOOP_SET_CR_STRUCT(lhs, rhs)       `__SNOOP_TO_CR(, lhs, ., rhs, .)
`define SNOOP_SET_REQ_STRUCT(lhs, rhs)   `__SNOOP_TO_REQ(, lhs, ., rhs, .)
`define SNOOP_SET_RESP_STRUCT(lhs, rhs) `__SNOOP_TO_RESP(, lhs, ., rhs, .)
////////////////////////////////////////////////////////////////////////////////////////////////////


////////////////////////////////////////////////////////////////////////////////////////////////////
// Assigning channel or request/response structs from another struct outside a process.
//
// The channel macros `SNOOP_ASSIGN_XX_STRUCT(lhs, rhs)` assign the fields of the `lhs` channel struct
// to the fields of the `rhs` channel struct.  They do not assign the handshake signals, which are
// not part of the channel structs.
// The request macro `SNOOP_ASSIGN_REQ_STRUCT(lhs, rhs)` assigns all fields of the `lhs` request
// struct to the fields of the `rhs` request struct.  This includes all request channel (AW, W, AR)
// payload and request-side handshake signals (AC valid and CD and CR ready).
// The response macro `SNOOP_ASSIGN_RESP_STRUCT(lhs, rhs)` assigns all fields of the `lhs` response
// struct to the fields of the `rhs` response struct.  This includes all response channel (CD and CR)
// payload and response-side handshake signals (CD and CR valid and AC ready).
//
// Usage Example:
// `SNOOP_ASSIGN_REQ_STRUCT(my_req_struct, another_req_struct)
`define SNOOP_ASSIGN_AC_STRUCT(lhs, rhs)     `__SNOOP_TO_AC(assign, lhs, ., rhs, .)
`define SNOOP_ASSIGN_CD_STRUCT(lhs, rhs)     `__SNOOP_TO_CD(assign, lhs, ., rhs, .)
`define SNOOP_ASSIGN_CR_STRUCT(lhs, rhs)       `__SNOOP_TO_CR(assign, lhs, ., rhs, .)
`define SNOOP_ASSIGN_REQ_STRUCT(lhs, rhs)   `__SNOOP_TO_REQ(assign, lhs, ., rhs, .)
`define SNOOP_ASSIGN_RESP_STRUCT(lhs, rhs) `__SNOOP_TO_RESP(assign, lhs, ., rhs, .)
////////////////////////////////////////////////////////////////////////////////////////////////////


`endif
