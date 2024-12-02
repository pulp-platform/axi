`ifndef ACE_DOMAIN_SVH_
`define ACE_DOMAIN_SVH_

  //////////////////
  // Domain types //
  //////////////////

    `define DOMAIN_MASK_T(width)\
        logic [width-1:0]
    `define DOMAIN_SET_T           \
        struct packed {    \
          domain_mask_t initiator; \
          domain_mask_t inner;     \
          domain_mask_t outer;     \
        }
    `define DOMAIN_TYPEDEF_MASK_T(width) \
        typedef logic [width-1:0] domain_mask_t;
    `define DOMAIN_TYPEDEF_SET_T \
        typedef  struct packed {    \
          domain_mask_t initiator; \
          domain_mask_t inner;     \
          domain_mask_t outer;     \
        } domain_set_t;
    `define DOMAIN_TYPEDEF_ALL(width) \
        `DOMAIN_TYPEDEF_MASK_T(width) \
        `DOMAIN_TYPEDEF_SET_T

`endif // ACE_DOMAIN_SVH_
