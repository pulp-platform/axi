// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51
//
// Chaoqun Liang <chaoqun.liang@unibo.it>

// ============================================================
// relaxi_encoder
//   Master-side boundary: plain AXI in → relaxi out
//   Request path : broadcast handshakes [2:0], encode ECC
//   Response path: vote handshakes [2:0]→1, decode/correct ECC
// ============================================================
module relaxi_encoder #(
  parameter int unsigned AxiAddrWidth  = 0,
  parameter int unsigned AxiDataWidth  = 0,
  parameter int unsigned AxiIdWidth    = 0,
  parameter int unsigned RelIdWidth    = AxiIdWidth,   // relAXI side, >= AxiIdWidth
  parameter int unsigned AxiUserWidth  = 0,
  // DO NOT OVERRIDE
  parameter int unsigned AxiStrbWidth  = AxiDataWidth / 8
) (
  // Plain AXI — from/to master
  input  logic                          aw_valid_i,
  input  logic [AxiIdWidth-1:0]         aw_id_i,
  input  logic [AxiAddrWidth-1:0]       aw_addr_i,
  input  axi_pkg::len_t                 aw_len_i,
  input  axi_pkg::size_t                aw_size_i,
  input  axi_pkg::burst_t               aw_burst_i,
  input  logic                          aw_lock_i,
  input  axi_pkg::cache_t               aw_cache_i,
  input  axi_pkg::prot_t                aw_prot_i,
  input  axi_pkg::qos_t                 aw_qos_i,
  input  axi_pkg::region_t              aw_region_i,
  input  axi_pkg::atop_t                aw_atop_i,
  input  logic [AxiUserWidth-1:0]       aw_user_i,
  output logic                          aw_ready_o,

  input  logic                          w_valid_i,
  input  logic [AxiDataWidth-1:0]       w_data_i,
  input  logic [AxiStrbWidth-1:0]       w_strb_i,
  input  logic                          w_last_i,
  input  logic [AxiUserWidth-1:0]       w_user_i,
  output logic                          w_ready_o,

  output logic                          b_valid_o,
  output logic [AxiIdWidth-1:0]         b_id_o,
  output axi_pkg::resp_t                b_resp_o,
  output logic [AxiUserWidth-1:0]       b_user_o,
  input  logic                          b_ready_i,

  input  logic                          ar_valid_i,
  input  logic [AxiIdWidth-1:0]         ar_id_i,
  input  logic [AxiAddrWidth-1:0]       ar_addr_i,
  input  axi_pkg::len_t                 ar_len_i,
  input  axi_pkg::size_t                ar_size_i,
  input  axi_pkg::burst_t               ar_burst_i,
  input  logic                          ar_lock_i,
  input  axi_pkg::cache_t               ar_cache_i,
  input  axi_pkg::prot_t                ar_prot_i,
  input  axi_pkg::qos_t                 ar_qos_i,
  input  axi_pkg::region_t              ar_region_i,
  input  logic [AxiUserWidth-1:0]       ar_user_i,
  output logic                          ar_ready_o,

  output logic                          r_valid_o,
  output logic [AxiIdWidth-1:0]         r_id_o,
  output logic [AxiDataWidth-1:0]       r_data_o,
  output axi_pkg::resp_t                r_resp_o,
  output logic                          r_last_o,
  output logic [AxiUserWidth-1:0]       r_user_o,
  input  logic                          r_ready_i,

  // relaxi — into/from xbar
  output logic [2:0]                    rel_aw_valid_o,
  output logic [RelIdWidth-1:0]                          rel_aw_id_o,
  output logic [hsiao_ecc_pkg::min_ecc(RelIdWidth)-1:0]  rel_aw_id_ecc_o,
  output logic [AxiAddrWidth
                +hsiao_ecc_pkg::min_ecc(AxiAddrWidth)-1:0] rel_aw_addr_o,
  output axi_pkg::len_t                 rel_aw_len_o,
  output axi_pkg::size_t                rel_aw_size_o,
  output axi_pkg::burst_t               rel_aw_burst_o,
  output logic                          rel_aw_lock_o,
  output axi_pkg::cache_t               rel_aw_cache_o,
  output axi_pkg::prot_t                rel_aw_prot_o,
  output axi_pkg::qos_t                 rel_aw_qos_o,
  output axi_pkg::region_t              rel_aw_region_o,
  output axi_pkg::atop_t                rel_aw_atop_o,
  output logic [AxiUserWidth-1:0]       rel_aw_user_o,
  output logic [hsiao_ecc_pkg::min_ecc(
    $bits(axi_pkg::len_t) + $bits(axi_pkg::size_t) +
    $bits(axi_pkg::burst_t) + 1 + $bits(axi_pkg::cache_t) +
    $bits(axi_pkg::prot_t) + $bits(axi_pkg::qos_t) +
    $bits(axi_pkg::region_t) + $bits(axi_pkg::atop_t) +
    AxiUserWidth)-1:0]                  rel_aw_other_ecc_o,
  input  logic [2:0]                    rel_aw_ready_i,

  output logic [2:0]                    rel_w_valid_o,
  output logic [AxiDataWidth
                +hsiao_ecc_pkg::min_ecc(AxiDataWidth)-1:0] rel_w_data_o,
  output logic [AxiStrbWidth-1:0]       rel_w_strb_o,
  output logic [2:0]                    rel_w_last_o,
  output logic [AxiUserWidth-1:0]       rel_w_user_o,
  output logic [hsiao_ecc_pkg::min_ecc(
    AxiStrbWidth + AxiUserWidth)-1:0]   rel_w_other_ecc_o,
  input  logic [2:0]                    rel_w_ready_i,

  input  logic [2:0]                    rel_b_valid_i,

  input logic [RelIdWidth-1:0]                          rel_b_id_i,
  input logic [hsiao_ecc_pkg::min_ecc(RelIdWidth)-1:0]  rel_b_id_ecc_i,

  input  axi_pkg::resp_t                rel_b_resp_i,
  input  logic [AxiUserWidth-1:0]       rel_b_user_i,
  input  logic [hsiao_ecc_pkg::min_ecc(
    $bits(axi_pkg::resp_t) +
    AxiUserWidth)-1:0]                  rel_b_ecc_i,
  output logic [2:0]                    rel_b_ready_o,

  output logic [2:0]                    rel_ar_valid_o,

  output logic [RelIdWidth-1:0]                          rel_ar_id_o,
  output logic [hsiao_ecc_pkg::min_ecc(RelIdWidth)-1:0]  rel_ar_id_ecc_o,

  output logic [AxiAddrWidth
                +hsiao_ecc_pkg::min_ecc(AxiAddrWidth)-1:0] rel_ar_addr_o,
  output axi_pkg::len_t                 rel_ar_len_o,
  output axi_pkg::size_t                rel_ar_size_o,
  output axi_pkg::burst_t               rel_ar_burst_o,
  output logic                          rel_ar_lock_o,
  output axi_pkg::cache_t               rel_ar_cache_o,
  output axi_pkg::prot_t                rel_ar_prot_o,
  output axi_pkg::qos_t                 rel_ar_qos_o,
  output axi_pkg::region_t              rel_ar_region_o,
  output logic [AxiUserWidth-1:0]       rel_ar_user_o,
  output logic [hsiao_ecc_pkg::min_ecc(
    $bits(axi_pkg::len_t) + $bits(axi_pkg::size_t) +
    $bits(axi_pkg::burst_t) + 1 + $bits(axi_pkg::cache_t) +
    $bits(axi_pkg::prot_t) + $bits(axi_pkg::qos_t) +
    $bits(axi_pkg::region_t) + AxiUserWidth)-1:0] rel_ar_other_ecc_o,
  input  logic [2:0]                    rel_ar_ready_i,

  input  logic [2:0]                    rel_r_valid_i,

  input logic [RelIdWidth-1:0]                          rel_r_id_i,
  input logic [hsiao_ecc_pkg::min_ecc(RelIdWidth)-1:0]  rel_r_id_ecc_i,

  input  logic [AxiDataWidth
                +hsiao_ecc_pkg::min_ecc(AxiDataWidth)-1:0] rel_r_data_i,
  input  axi_pkg::resp_t                rel_r_resp_i,
  input  logic [2:0]                    rel_r_last_i,
  input  logic [AxiUserWidth-1:0]       rel_r_user_i,
  input  logic [hsiao_ecc_pkg::min_ecc(
    $bits(axi_pkg::resp_t) +
    AxiUserWidth)-1:0]                  rel_r_other_ecc_i,
  output logic [2:0]                    rel_r_ready_o,

  // fault[0] = correctable, fault[1] = uncorrectable
  output logic [1:0]                    fault_o
);

  // -----------------------------------------------------------
  // Local parameters
  // -----------------------------------------------------------
  localparam int unsigned AwOtherWidth =
    $bits(axi_pkg::len_t) + $bits(axi_pkg::size_t) +
    $bits(axi_pkg::burst_t) + 1 + $bits(axi_pkg::cache_t) +
    $bits(axi_pkg::prot_t) + $bits(axi_pkg::qos_t) +
    $bits(axi_pkg::region_t) + $bits(axi_pkg::atop_t) + AxiUserWidth;
  localparam int unsigned AwOtherEccWidth = hsiao_ecc_pkg::min_ecc(AwOtherWidth);

  localparam int unsigned ArOtherWidth =
    $bits(axi_pkg::len_t) + $bits(axi_pkg::size_t) +
    $bits(axi_pkg::burst_t) + 1 + $bits(axi_pkg::cache_t) +
    $bits(axi_pkg::prot_t) + $bits(axi_pkg::qos_t) +
    $bits(axi_pkg::region_t) + AxiUserWidth;                            // NO AxiIdWidth
  localparam int unsigned ArOtherEccWidth = hsiao_ecc_pkg::min_ecc(ArOtherWidth);

  localparam int unsigned BWidth    = $bits(axi_pkg::resp_t) + AxiUserWidth;   // NO AxiIdWidth
  localparam int unsigned BEccWidth = hsiao_ecc_pkg::min_ecc(BWidth);

  localparam int unsigned ROtherWidth    = $bits(axi_pkg::resp_t) + AxiUserWidth; // NO AxiIdWidth
  localparam int unsigned ROtherEccWidth = hsiao_ecc_pkg::min_ecc(ROtherWidth);

  localparam int unsigned WOtherWidth    = AxiStrbWidth + AxiUserWidth;
  localparam int unsigned WOtherEccWidth = hsiao_ecc_pkg::min_ecc(WOtherWidth);

  localparam int unsigned IdPad = RelIdWidth - AxiIdWidth;
  // -----------------------------------------------------------
  // REQUEST PATH: broadcast handshakes, encode ECC
  // -----------------------------------------------------------

  // Handshakes — broadcast 1→3
  assign rel_aw_valid_o = {3{aw_valid_i}};
  assign rel_w_valid_o  = {3{w_valid_i}};
  assign rel_b_ready_o  = {3{b_ready_i}};
  assign rel_ar_valid_o = {3{ar_valid_i}};
  assign rel_r_ready_o  = {3{r_ready_i}};

  // W last — broadcast 1→3 (TMR field)
  assign rel_w_last_o = {3{w_last_i}};

  // AW channel: pass plain fields through, encode addr and other_ecc
  assign rel_aw_len_o    = aw_len_i;
  assign rel_aw_size_o   = aw_size_i;
  assign rel_aw_burst_o  = aw_burst_i;
  assign rel_aw_lock_o   = aw_lock_i;
  assign rel_aw_cache_o  = aw_cache_i;
  assign rel_aw_prot_o   = aw_prot_i;
  assign rel_aw_qos_o    = aw_qos_i;
  assign rel_aw_region_o = aw_region_i;
  assign rel_aw_atop_o   = aw_atop_i;
  assign rel_aw_user_o   = aw_user_i;

  hsiao_ecc_enc #(
    .DataWidth(AxiAddrWidth)
  ) i_aw_addr_enc (
    .in  (aw_addr_i),
    .out (rel_aw_addr_o)
  );

  relaxi_id_enc #(
    .IdWidth(RelIdWidth)
  ) i_aw_id_enc (
    .id_i({{IdPad{1'b0}}, aw_id_i}),
    .id_o(rel_aw_id_o),
    .id_ecc_o(rel_aw_id_ecc_o)
  );

  relaxi_aw_other_enc #(
    .UserWidth(AxiUserWidth)
  ) i_aw_other_enc (
    .len_i(aw_len_i),
    .size_i(aw_size_i),
    .burst_i(aw_burst_i),
    .lock_i(aw_lock_i),
    .cache_i(aw_cache_i),
    .prot_i(aw_prot_i),
    .qos_i(aw_qos_i),
    .region_i(aw_region_i),
    .atop_i(aw_atop_i),
    .user_i(aw_user_i),
    .ecc_o(rel_aw_other_ecc_o)
  );

  // W channel
  assign rel_w_strb_o = w_strb_i;
  assign rel_w_user_o = w_user_i;

  hsiao_ecc_enc #(
    .DataWidth(AxiDataWidth)
  ) i_w_data_enc (
    .in  (w_data_i),
    .out (rel_w_data_o)
  );

  logic [WOtherWidth + WOtherEccWidth-1:0] w_other_enc;
  hsiao_ecc_enc #(
    .DataWidth(WOtherWidth)
  ) i_w_other_enc (
    .in  ({w_strb_i, w_user_i}),
    .out (w_other_enc)
  );

  assign rel_w_other_ecc_o = w_other_enc[WOtherWidth +: WOtherEccWidth];

  // AR channel
  assign rel_ar_len_o    = ar_len_i;
  assign rel_ar_size_o   = ar_size_i;
  assign rel_ar_burst_o  = ar_burst_i;
  assign rel_ar_lock_o   = ar_lock_i;
  assign rel_ar_cache_o  = ar_cache_i;
  assign rel_ar_prot_o   = ar_prot_i;
  assign rel_ar_qos_o    = ar_qos_i;
  assign rel_ar_region_o = ar_region_i;
  assign rel_ar_user_o   = ar_user_i;

  hsiao_ecc_enc #(
    .DataWidth(AxiAddrWidth)
  ) i_ar_addr_enc (
    .in  (ar_addr_i),
    .out (rel_ar_addr_o)
  );

  relaxi_id_enc #(
    .IdWidth(RelIdWidth)
  ) i_ar_id_enc (
    .id_i({{IdPad{1'b0}}, ar_id_i}),
    .id_o(rel_ar_id_o),
    .id_ecc_o(rel_ar_id_ecc_o)
  );

  relaxi_ar_other_enc #(
    .UserWidth(AxiUserWidth)
  ) i_ar_other_enc (
    .len_i(ar_len_i),
    .size_i(ar_size_i),
    .burst_i(ar_burst_i),
    .lock_i(ar_lock_i),
    .cache_i(ar_cache_i),
    .prot_i(ar_prot_i),
    .qos_i(ar_qos_i),
    .region_i(ar_region_i),
    .user_i(ar_user_i),
    .ecc_o(rel_ar_other_ecc_o)
  );

  // -----------------------------------------------------------
  // RESPONSE PATH: vote handshakes, decode/correct ECC
  // -----------------------------------------------------------
  logic voter_aw_ready_fault, voter_w_ready_fault, voter_b_valid_fault;
  logic voter_ar_ready_fault, voter_r_valid_fault, voter_r_last_fault;

  TMR_voter_fail #(
    .VoterType ( 0 ) // Classical_MV
  ) i_aw_ready_vote (
    .a_i(rel_aw_ready_i[0]),
    .b_i(rel_aw_ready_i[1]),
    .c_i(rel_aw_ready_i[2]),
    .majority_o(aw_ready_o),
    .fault_detected_o(voter_aw_ready_fault)
  );

  TMR_voter_fail #(
    .VoterType ( 0 ) // Classical_MV
  ) i_w_ready_vote (
    .a_i(rel_w_ready_i[0]),
    .b_i(rel_w_ready_i[1]),
    .c_i(rel_w_ready_i[2]),
    .majority_o(w_ready_o),
    .fault_detected_o(voter_w_ready_fault)
  );

  TMR_voter_fail #(
    .VoterType ( 0 ) // Classical_MV
  ) i_b_valid_vote (
    .a_i(rel_b_valid_i[0]),
    .b_i(rel_b_valid_i[1]),
    .c_i(rel_b_valid_i[2]),
    .majority_o(b_valid_o),
    .fault_detected_o(voter_b_valid_fault)
  );

  TMR_voter_fail #(
    .VoterType ( 0 ) // Classical_MV
  ) i_ar_ready_vote (
    .a_i(rel_ar_ready_i[0]),
    .b_i(rel_ar_ready_i[1]),
    .c_i(rel_ar_ready_i[2]),
    .majority_o(ar_ready_o),
    .fault_detected_o(voter_ar_ready_fault)
  );

  TMR_voter_fail #(
    .VoterType ( 0 ) // Classical_MV
  ) i_r_valid_vote (
    .a_i(rel_r_valid_i[0]), .b_i(rel_r_valid_i[1]), .c_i(rel_r_valid_i[2]),
    .majority_o(r_valid_o), .fault_detected_o(voter_r_valid_fault)
  );

  TMR_voter_fail #(
    .VoterType ( 0 ) // Classical_MV
  ) i_r_last_vote (
    .a_i(rel_r_last_i[0]),
    .b_i(rel_r_last_i[1]),
    .c_i(rel_r_last_i[2]),
    .majority_o(r_last_o),
    .fault_detected_o(voter_r_last_fault)
  );

  logic [1:0] b_id_fault;
  logic [RelIdWidth-1:0] b_id_wide;
  logic                  b_id_hi_err;

  relaxi_id_dec #(
    .IdWidth(RelIdWidth)
  ) i_b_id_dec (
    .id_i(rel_b_id_i),
    .id_ecc_i(rel_b_id_ecc_i),
    .id_o(b_id_wide),
    .err_o(b_id_fault)
  );
  assign b_id_o = b_id_wide[AxiIdWidth-1:0];
  assign b_id_hi_err = |b_id_wide[RelIdWidth-1:AxiIdWidth];

  logic [1:0] b_fault;
  relaxi_resp_other_dec #(
    .UserWidth(AxiUserWidth)
  ) i_b_other_dec (
    .resp_i(rel_b_resp_i),
    .user_i(rel_b_user_i),
    .ecc_i(rel_b_ecc_i),
    .resp_o(b_resp_o),
    .user_o(b_user_o),
    .err_o(b_fault)
  );

  logic [1:0] r_id_fault;
  logic [RelIdWidth-1:0] r_id_wide;
  logic                  r_id_hi_err;
  relaxi_id_dec #(
    .IdWidth(RelIdWidth)
  ) i_r_id_dec (
    .id_i(rel_r_id_i),
    .id_ecc_i(rel_r_id_ecc_i),
    .id_o(r_id_wide),
    .err_o(r_id_fault)
  );
  assign r_id_o = r_id_wide[AxiIdWidth-1:0];
  assign r_id_hi_err = |r_id_wide[RelIdWidth-1:AxiIdWidth];

  logic [1:0] r_other_fault;
  relaxi_resp_other_dec #(
    .UserWidth(AxiUserWidth)
  ) i_r_other_dec (
    .resp_i(rel_r_resp_i),
    .user_i(rel_r_user_i),
    .ecc_i(rel_r_other_ecc_i),
    .resp_o(r_resp_o),
    .user_o(r_user_o),
    .err_o(r_other_fault)
  );

  // R channel — decode r_data
  logic [1:0] r_data_fault;
  hsiao_ecc_dec #(
    .DataWidth(AxiDataWidth)
  ) i_r_data_dec (
    .in     (rel_r_data_i),
    .out    (r_data_o),
    .syndrome_o (),
    .err_o      (r_data_fault)
  );


  // Aggregate faults — gate on valid to avoid spurious errors on idle channels
  assign fault_o[0] = (rel_b_valid_i[0] & b_fault[0])        |
                      (rel_r_valid_i[0] & r_data_fault[0])    |
                      (rel_r_valid_i[0] & r_other_fault[0])   |
                      (rel_b_valid_i[0] & b_id_fault[0])      |
                      (rel_r_valid_i[0] & r_id_fault[0])      |
                      voter_aw_ready_fault | voter_w_ready_fault |
                      voter_b_valid_fault  | voter_ar_ready_fault |
                      voter_r_valid_fault  | voter_r_last_fault;

  assign fault_o[1] = (rel_b_valid_i[0] & b_fault[1])       |
                      (rel_r_valid_i[0] & r_data_fault[1])   |
                      (rel_r_valid_i[0] & r_other_fault[1])  |
                      (rel_b_valid_i[0] & b_id_fault[1])     |
                      (rel_r_valid_i[0] & r_id_fault[1])     |
                      (rel_b_valid_i[0] & b_id_hi_err)       |
                      (rel_r_valid_i[0] & r_id_hi_err);

endmodule
