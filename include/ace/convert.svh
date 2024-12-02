`include "axi/assign.svh"

`ifndef ACE_CONVERT_SVH_
`define ACE_CONVERT_SVH_

`define __ACE_TO_AXI_R(__opt_as, __lhs, __lhs_sep, __rhs, __rhs_sep)     \
    __opt_as __lhs``__lhs_sep``id     = __rhs``__rhs_sep``id;            \
    __opt_as __lhs``__lhs_sep``data   = __rhs``__rhs_sep``data;          \
    __opt_as __lhs``__lhs_sep``resp   = __rhs``__rhs_sep``resp[1:0];     \
    __opt_as __lhs``__lhs_sep``last   = __rhs``__rhs_sep``last;          \
    __opt_as __lhs``__lhs_sep``user   = __rhs``__rhs_sep``user;
`define __AXI_TO_ACE_AW(__opt_as, __lhs, __lhs_sep, __rhs, __rhs_sep) \
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
    __opt_as __lhs``__lhs_sep``snoop  = '0;                           \
    __opt_as __lhs``__lhs_sep``bar    = '0;                           \
    __opt_as __lhs``__lhs_sep``domain = '0;                           \
    __opt_as __lhs``__lhs_sep``awunique = '0;
`define __AXI_TO_ACE_AR(__opt_as, __lhs, __lhs_sep, __rhs, __rhs_sep) \
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
    __opt_as __lhs``__lhs_sep``snoop  = '0;                           \
    __opt_as __lhs``__lhs_sep``bar    = '0;                           \
    __opt_as __lhs``__lhs_sep``domain = '0;
`define __AXI_TO_ACE_R(__opt_as, __lhs, __lhs_sep, __rhs, __rhs_sep)     \
    __opt_as __lhs``__lhs_sep``id     = __rhs``__rhs_sep``id;            \
    __opt_as __lhs``__lhs_sep``data   = __rhs``__rhs_sep``data;          \
    __opt_as __lhs``__lhs_sep``resp   = {2'b00, __rhs``__rhs_sep``resp}; \
    __opt_as __lhs``__lhs_sep``last   = __rhs``__rhs_sep``last;          \
    __opt_as __lhs``__lhs_sep``user   = __rhs``__rhs_sep``user;

`define ACE_TO_AXI_ASSIGN_R_STRUCT(dst, src) \
    `__ACE_TO_AXI_R(assign, dst, ., src, .)

`define AXI_TO_ACE_ASSIGN_AW_STRUCT(dst, src) \
    `__AXI_TO_ACE_AW(assign, dst, ., src, .)

`define AXI_TO_ACE_ASSIGN_AR_STRUCT(dst, src) \
    `__AXI_TO_ACE_AR(assign, dst, ., src, .)

`define AXI_TO_ACE_ASSIGN_R_STRUCT(dst, src) \
    `__AXI_TO_ACE_R(assign, dst, ., src, .)


`define ACE_TO_AXI_ASSIGN_REQ(dst, src)   \
    `AXI_ASSIGN_AW_STRUCT(dst.aw, src.aw) \
    `AXI_ASSIGN_AR_STRUCT(dst.ar, src.ar) \
    `AXI_ASSIGN_W_STRUCT(dst.w, src.w)    \
    assign dst.aw_valid = src.aw_valid;   \
    assign dst.ar_valid = src.ar_valid;   \
    assign dst.w_valid  = src.w_valid;    \
    assign dst.b_ready  = src.b_ready;    \
    assign dst.r_ready  = src.r_ready;

`define ACE_TO_AXI_ASSIGN_RESP(dst, src)      \
    `ACE_TO_AXI_ASSIGN_R_STRUCT(dst.r, src.r) \
    `AXI_ASSIGN_B_STRUCT(dst.b, src.b)        \
    assign dst.aw_ready = src.aw_ready;       \
    assign dst.ar_ready = src.ar_ready;       \
    assign dst.w_ready  = src.w_ready;        \
    assign dst.b_valid  = src.b_valid;        \
    assign dst.r_valid  = src.r_valid;

`define AXI_TO_ACE_ASSIGN_REQ(dst, src)          \
    `AXI_TO_ACE_ASSIGN_AW_STRUCT(dst.aw, src.aw) \
    `AXI_TO_ACE_ASSIGN_AR_STRUCT(dst.ar, src.ar) \
    `AXI_ASSIGN_W_STRUCT(dst.w, src.w)           \
    assign dst.aw_valid = src.aw_valid;          \
    assign dst.ar_valid = src.ar_valid;          \
    assign dst.w_valid  = src.w_valid;           \
    assign dst.b_ready  = src.b_ready;           \
    assign dst.r_ready  = src.r_ready;


`define AXI_TO_ACE_ASSIGN_RESP(dst, src)      \
    `AXI_TO_ACE_ASSIGN_R_STRUCT(dst.r, src.r) \
    `AXI_ASSIGN_B_STRUCT(dst.b, src.b)        \
    assign dst.aw_ready = src.aw_ready;       \
    assign dst.ar_ready = src.ar_ready;       \
    assign dst.w_ready  = src.w_ready;        \
    assign dst.b_valid  = src.b_valid;        \
    assign dst.r_valid  = src.r_valid;


`endif // ACE_CONVERT_SVH_
