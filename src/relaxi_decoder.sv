// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51
//
// Chaoqun Liang <chaoqun.liang@unibo.it>

// ============================================================
// relaxi_decoder
//   Slave-side boundary: relaxi in → plain AXI out
//   Request path : vote handshakes [2:0]→1, decode/correct ECC
//   Response path: broadcast handshakes 1→[2:0], encode ECC
// ============================================================
module relaxi_decoder #(
  parameter int unsigned AxiAddrWidth  = 0,
  parameter int unsigned AxiDataWidth  = 0,
  parameter int unsigned AxiIdWidth    = 0,
  parameter int unsigned RelIdWidth    = 0,
  parameter int unsigned AxiUserWidth  = 0,
  // DO NOT OVERRIDE
  parameter int unsigned AxiStrbWidth  = AxiDataWidth / 8
) (
  // relaxi — from xbar
  input  logic [2:0]                    rel_aw_valid_i,
  // request inputs (from fabric): id PLAIN + separate id_ecc
  input  logic [RelIdWidth-1:0]                          rel_aw_id_i,
  input  logic [hsiao_ecc_pkg::min_ecc(RelIdWidth)-1:0]  rel_aw_id_ecc_i,

  input  logic [AxiAddrWidth
                +hsiao_ecc_pkg::min_ecc(AxiAddrWidth)-1:0] rel_aw_addr_i,
  input  axi_pkg::len_t                 rel_aw_len_i,
  input  axi_pkg::size_t                rel_aw_size_i,
  input  axi_pkg::burst_t               rel_aw_burst_i,
  input  logic                          rel_aw_lock_i,
  input  axi_pkg::cache_t               rel_aw_cache_i,
  input  axi_pkg::prot_t                rel_aw_prot_i,
  input  axi_pkg::qos_t                 rel_aw_qos_i,
  input  axi_pkg::region_t              rel_aw_region_i,
  input  axi_pkg::atop_t                rel_aw_atop_i,
  input  logic [AxiUserWidth-1:0]       rel_aw_user_i,
  input  logic [hsiao_ecc_pkg::min_ecc(
    $bits(axi_pkg::len_t) + $bits(axi_pkg::size_t) +
    $bits(axi_pkg::burst_t) + 1 + $bits(axi_pkg::cache_t) +
    $bits(axi_pkg::prot_t) + $bits(axi_pkg::qos_t) +
    $bits(axi_pkg::region_t) + $bits(axi_pkg::atop_t) +
    AxiUserWidth)-1:0]                  rel_aw_other_ecc_i,
  output logic [2:0]                    rel_aw_ready_o,

  input  logic [2:0]                    rel_w_valid_i,
  input  logic [AxiDataWidth
                +hsiao_ecc_pkg::min_ecc(AxiDataWidth)-1:0] rel_w_data_i,
  input  logic [AxiStrbWidth-1:0]       rel_w_strb_i,
  input  logic [2:0]                    rel_w_last_i,
  input  logic [AxiUserWidth-1:0]       rel_w_user_i,
  input  logic [hsiao_ecc_pkg::min_ecc(
    AxiStrbWidth + AxiUserWidth)-1:0]   rel_w_other_ecc_i,
  output logic [2:0]                    rel_w_ready_o,

  output logic [2:0]                    rel_b_valid_o,
  // response outputs (to fabric): id PLAIN + separate id_ecc
  output logic [RelIdWidth-1:0]                          rel_b_id_o,
  output logic [hsiao_ecc_pkg::min_ecc(RelIdWidth)-1:0]  rel_b_id_ecc_o,
  output axi_pkg::resp_t                rel_b_resp_o,
  output logic [AxiUserWidth-1:0]       rel_b_user_o,
  output logic [hsiao_ecc_pkg::min_ecc(
    $bits(axi_pkg::resp_t) +
    AxiUserWidth)-1:0]                  rel_b_ecc_o,
  input  logic [2:0]                    rel_b_ready_i,

  input  logic [2:0]                    rel_ar_valid_i,
  input  logic [RelIdWidth-1:0]                          rel_ar_id_i,
  input  logic [hsiao_ecc_pkg::min_ecc(RelIdWidth)-1:0]  rel_ar_id_ecc_i,
  input  logic [AxiAddrWidth
                +hsiao_ecc_pkg::min_ecc(AxiAddrWidth)-1:0] rel_ar_addr_i,
  input  axi_pkg::len_t                 rel_ar_len_i,
  input  axi_pkg::size_t                rel_ar_size_i,
  input  axi_pkg::burst_t               rel_ar_burst_i,
  input  logic                          rel_ar_lock_i,
  input  axi_pkg::cache_t               rel_ar_cache_i,
  input  axi_pkg::prot_t                rel_ar_prot_i,
  input  axi_pkg::qos_t                 rel_ar_qos_i,
  input  axi_pkg::region_t              rel_ar_region_i,
  input  logic [AxiUserWidth-1:0]       rel_ar_user_i,
  input  logic [hsiao_ecc_pkg::min_ecc(
    $bits(axi_pkg::len_t) + $bits(axi_pkg::size_t) +
    $bits(axi_pkg::burst_t) + 1 + $bits(axi_pkg::cache_t) +
    $bits(axi_pkg::prot_t) + $bits(axi_pkg::qos_t) +
    $bits(axi_pkg::region_t) + AxiUserWidth)-1:0] rel_ar_other_ecc_i,
  output logic [2:0]                    rel_ar_ready_o,
  output logic [RelIdWidth-1:0]                          rel_r_id_o,
  output logic [hsiao_ecc_pkg::min_ecc(RelIdWidth)-1:0]  rel_r_id_ecc_o,
  output logic [2:0]                    rel_r_valid_o,

  output logic [AxiDataWidth
                +hsiao_ecc_pkg::min_ecc(AxiDataWidth)-1:0] rel_r_data_o,
  output axi_pkg::resp_t                rel_r_resp_o,
  output logic [2:0]                    rel_r_last_o,
  output logic [AxiUserWidth-1:0]       rel_r_user_o,
  output logic [hsiao_ecc_pkg::min_ecc(
    $bits(axi_pkg::resp_t) +
    AxiUserWidth)-1:0]                  rel_r_other_ecc_o,
  input  logic [2:0]                    rel_r_ready_i,

  // Plain AXI — to/from slave
  output logic                          aw_valid_o,
  output logic [AxiIdWidth-1:0]         aw_id_o,
  output logic [AxiAddrWidth-1:0]       aw_addr_o,
  output axi_pkg::len_t                 aw_len_o,
  output axi_pkg::size_t                aw_size_o,
  output axi_pkg::burst_t               aw_burst_o,
  output logic                          aw_lock_o,
  output axi_pkg::cache_t               aw_cache_o,
  output axi_pkg::prot_t                aw_prot_o,
  output axi_pkg::qos_t                 aw_qos_o,
  output axi_pkg::region_t              aw_region_o,
  output axi_pkg::atop_t                aw_atop_o,
  output logic [AxiUserWidth-1:0]       aw_user_o,
  input  logic                          aw_ready_i,

  output logic                          w_valid_o,
  output logic [AxiDataWidth-1:0]       w_data_o,
  output logic [AxiStrbWidth-1:0]       w_strb_o,
  output logic                          w_last_o,
  output logic [AxiUserWidth-1:0]       w_user_o,
  input  logic                          w_ready_i,

  input  logic                          b_valid_i,
  input  logic [AxiIdWidth-1:0]         b_id_i,
  input  axi_pkg::resp_t                b_resp_i,
  input  logic [AxiUserWidth-1:0]       b_user_i,
  output logic                          b_ready_o,

  output logic                          ar_valid_o,
  output logic [AxiIdWidth-1:0]         ar_id_o,
  output logic [AxiAddrWidth-1:0]       ar_addr_o,
  output axi_pkg::len_t                 ar_len_o,
  output axi_pkg::size_t                ar_size_o,
  output axi_pkg::burst_t               ar_burst_o,
  output logic                          ar_lock_o,
  output axi_pkg::cache_t               ar_cache_o,
  output axi_pkg::prot_t                ar_prot_o,
  output axi_pkg::qos_t                 ar_qos_o,
  output axi_pkg::region_t              ar_region_o,
  output logic [AxiUserWidth-1:0]       ar_user_o,
  input  logic                          ar_ready_i,

  input  logic                          r_valid_i,
  input  logic [AxiIdWidth-1:0]         r_id_i,
  input  logic [AxiDataWidth-1:0]       r_data_i,
  input  axi_pkg::resp_t                r_resp_i,
  input  logic                          r_last_i,
  input  logic [AxiUserWidth-1:0]       r_user_i,
  output logic                          r_ready_o,

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
    $bits(axi_pkg::region_t) + AxiUserWidth;
  localparam int unsigned ArOtherEccWidth = hsiao_ecc_pkg::min_ecc(ArOtherWidth);

  localparam int unsigned WOtherWidth    = AxiStrbWidth + AxiUserWidth;
  localparam int unsigned WOtherEccWidth = hsiao_ecc_pkg::min_ecc(WOtherWidth);

  localparam int unsigned BWidth    = $bits(axi_pkg::resp_t) + AxiUserWidth;
  localparam int unsigned BEccWidth = hsiao_ecc_pkg::min_ecc(BWidth);

  localparam int unsigned ROtherWidth    = $bits(axi_pkg::resp_t) + AxiUserWidth;
  localparam int unsigned ROtherEccWidth = hsiao_ecc_pkg::min_ecc(ROtherWidth);

  localparam int unsigned IdPad = RelIdWidth - AxiIdWidth;
  // -----------------------------------------------------------
  // REQUEST PATH: vote handshakes, decode/correct ECC → plain AXI
  // -----------------------------------------------------------
  logic voter_aw_valid_fault, voter_w_valid_fault, voter_b_ready_fault;
  logic voter_ar_valid_fault, voter_r_ready_fault, voter_w_last_fault;

  TMR_voter_fail #(
    .VoterType ( 0 ) // Classical_MV
  ) i_aw_valid_vote (
    .a_i(rel_aw_valid_i[0]), .b_i(rel_aw_valid_i[1]), .c_i(rel_aw_valid_i[2]),
    .majority_o(aw_valid_o), .fault_detected_o(voter_aw_valid_fault)
  );
  TMR_voter_fail #(
    .VoterType ( 0 ) // Classical_MV
  ) i_w_valid_vote (
    .a_i(rel_w_valid_i[0]), .b_i(rel_w_valid_i[1]), .c_i(rel_w_valid_i[2]),
    .majority_o(w_valid_o), .fault_detected_o(voter_w_valid_fault)
  );
  TMR_voter_fail #(
    .VoterType ( 0 ) // Classical_MV
  ) i_b_ready_vote (
    .a_i(rel_b_ready_i[0]), .b_i(rel_b_ready_i[1]), .c_i(rel_b_ready_i[2]),
    .majority_o(b_ready_o), .fault_detected_o(voter_b_ready_fault)
  );
  TMR_voter_fail #(
    .VoterType ( 0 ) // Classical_MV
  ) i_ar_valid_vote (
    .a_i(rel_ar_valid_i[0]), .b_i(rel_ar_valid_i[1]), .c_i(rel_ar_valid_i[2]),
    .majority_o(ar_valid_o), .fault_detected_o(voter_ar_valid_fault)
  );
  TMR_voter_fail #(
    .VoterType ( 0 ) // Classical_MV
  ) i_r_ready_vote (
    .a_i(rel_r_ready_i[0]), .b_i(rel_r_ready_i[1]), .c_i(rel_r_ready_i[2]),
    .majority_o(r_ready_o), .fault_detected_o(voter_r_ready_fault)
  );
  // W last — TMR field
  TMR_voter_fail #(
    .VoterType ( 0 ) // Classical_MV
  ) i_w_last_vote (
    .a_i(rel_w_last_i[0]), .b_i(rel_w_last_i[1]), .c_i(rel_w_last_i[2]),
    .majority_o(w_last_o), .fault_detected_o(voter_w_last_fault)
  );

  // AW: decode addr, decode other_ecc → corrected fields
  logic [1:0] aw_addr_fault, aw_other_fault;

  hsiao_ecc_dec #(.DataWidth(AxiAddrWidth)) i_aw_addr_dec (
    .in     (rel_aw_addr_i),
    .out    (aw_addr_o),
    .syndrome_o (),
    .err_o      (aw_addr_fault)
  );

  // AW: id own codeword + other group (no id)
  logic [1:0] aw_id_fault;
  logic [RelIdWidth-1:0] aw_id_wide;
  logic                  aw_id_hi_err;

  relaxi_id_dec #(
    .IdWidth(RelIdWidth)
  ) i_aw_id_dec (
    .id_i(rel_aw_id_i),
    .id_ecc_i(rel_aw_id_ecc_i),
    .id_o(aw_id_wide),
    .err_o(aw_id_fault)
  );
  assign aw_id_o = aw_id_wide[AxiIdWidth-1:0];

  if (RelIdWidth > AxiIdWidth) begin : gen_aw_id_hi_err
    assign aw_id_hi_err = |aw_id_wide[RelIdWidth-1:AxiIdWidth];
  end else begin : gen_aw_id_hi_err_tie
    assign aw_id_hi_err = 1'b0;
  end

  relaxi_aw_other_dec #(.UserWidth(AxiUserWidth)) i_aw_other_dec (
    .len_i(rel_aw_len_i), .size_i(rel_aw_size_i), .burst_i(rel_aw_burst_i),
    .lock_i(rel_aw_lock_i), .cache_i(rel_aw_cache_i), .prot_i(rel_aw_prot_i),
    .qos_i(rel_aw_qos_i), .region_i(rel_aw_region_i), .atop_i(rel_aw_atop_i),
    .user_i(rel_aw_user_i), .ecc_i(rel_aw_other_ecc_i),
    .len_o(aw_len_o), .size_o(aw_size_o), .burst_o(aw_burst_o),
    .lock_o(aw_lock_o), .cache_o(aw_cache_o), .prot_o(aw_prot_o),
    .qos_o(aw_qos_o), .region_o(aw_region_o), .atop_o(aw_atop_o),
    .user_o(aw_user_o), .err_o(aw_other_fault));

  // W: decode data, decode other_ecc → corrected {strb, user}
  logic [1:0] w_data_fault, w_other_fault;

  hsiao_ecc_dec #(.DataWidth(AxiDataWidth)) i_w_data_dec (
    .in     (rel_w_data_i),
    .out    (w_data_o),
    .syndrome_o (),
    .err_o      (w_data_fault)
  );

  hsiao_ecc_dec #(.DataWidth(WOtherWidth)) i_w_other_dec (
    .in     ({rel_w_other_ecc_i, rel_w_strb_i, rel_w_user_i}),
    .out    ({w_strb_o, w_user_o}),
    .syndrome_o (),
    .err_o      (w_other_fault)
  );

  // AR: decode addr, decode other_ecc
  logic [1:0] ar_addr_fault, ar_other_fault;

  hsiao_ecc_dec #(.DataWidth(AxiAddrWidth)) i_ar_addr_dec (
    .in     (rel_ar_addr_i),
    .out    (ar_addr_o),
    .syndrome_o (),
    .err_o      (ar_addr_fault)
  );

  logic [1:0] ar_id_fault;
  logic [RelIdWidth-1:0] ar_id_wide;
  logic                  ar_id_hi_err;

  relaxi_id_dec #(
    .IdWidth(RelIdWidth)
  ) i_ar_id_dec (
    .id_i(rel_ar_id_i),
    .id_ecc_i(rel_ar_id_ecc_i),
    .id_o(ar_id_wide),
    .err_o(ar_id_fault)
  );
  assign ar_id_o = ar_id_wide[AxiIdWidth-1:0];
  if (RelIdWidth > AxiIdWidth) begin : gen_ar_id_hi_err
    assign ar_id_hi_err = |ar_id_wide[RelIdWidth-1:AxiIdWidth];
  end else begin : gen_ar_id_hi_err_tie
    assign ar_id_hi_err = 1'b0;
  end

  relaxi_ar_other_dec #(.UserWidth(AxiUserWidth)) i_ar_other_dec (
    .len_i(rel_ar_len_i), .size_i(rel_ar_size_i), .burst_i(rel_ar_burst_i),
    .lock_i(rel_ar_lock_i), .cache_i(rel_ar_cache_i), .prot_i(rel_ar_prot_i),
    .qos_i(rel_ar_qos_i), .region_i(rel_ar_region_i),
    .user_i(rel_ar_user_i), .ecc_i(rel_ar_other_ecc_i),
    .len_o(ar_len_o), .size_o(ar_size_o), .burst_o(ar_burst_o),
    .lock_o(ar_lock_o), .cache_o(ar_cache_o), .prot_o(ar_prot_o),
    .qos_o(ar_qos_o), .region_o(ar_region_o),
    .user_o(ar_user_o), .err_o(ar_other_fault));

  // -----------------------------------------------------------
  // RESPONSE PATH: broadcast handshakes, encode ECC → relaxi
  // -----------------------------------------------------------

  // Handshakes — broadcast 1→3
  assign rel_aw_ready_o = {3{aw_ready_i}};
  assign rel_w_ready_o  = {3{w_ready_i}};
  assign rel_b_valid_o  = {3{b_valid_i}};
  assign rel_ar_ready_o = {3{ar_ready_i}};
  assign rel_r_valid_o  = {3{r_valid_i}};

  // R last — broadcast 1→3 (TMR field)
  assign rel_r_last_o = {3{r_last_i}};

  // B: id own codeword + resp/user group

  relaxi_id_enc #(
    .IdWidth(RelIdWidth)
  ) i_b_id_enc (
    .id_i({{IdPad{1'b0}}, b_id_i}),
    .id_o(rel_b_id_o),
    .id_ecc_o(rel_b_id_ecc_o)
  );

  relaxi_resp_other_enc #(.UserWidth(AxiUserWidth)) i_b_other_enc (
    .resp_i(b_resp_i), .user_i(b_user_i), .ecc_o(rel_b_ecc_o));

  assign rel_b_resp_o = b_resp_i;
  assign rel_b_user_o = b_user_i;

  hsiao_ecc_enc #(.DataWidth(AxiDataWidth)) i_r_data_enc (
    .in  (r_data_i),
    .out (rel_r_data_o)
  );

  relaxi_id_enc #(
    .IdWidth(RelIdWidth)
  ) i_r_id_enc (
    .id_i({{IdPad{1'b0}}, r_id_i}),
    .id_o(rel_r_id_o),
    .id_ecc_o(rel_r_id_ecc_o)
  );

  relaxi_resp_other_enc #(.UserWidth(AxiUserWidth)) i_r_other_enc (
    .resp_i(r_resp_i), .user_i(r_user_i), .ecc_o(rel_r_other_ecc_o));
  assign rel_r_resp_o = r_resp_i;
  assign rel_r_user_o = r_user_i;

  // -----------------------------------------------------------
  // Fault aggregation — gate on valid to suppress idle channel errors
  // -----------------------------------------------------------
  assign fault_o[0] = (rel_aw_valid_i[0] & (aw_addr_fault[0]|aw_other_fault[0]|aw_id_fault[0])) |
                      (rel_w_valid_i[0]  & (w_data_fault[0] |w_other_fault[0]))                 |
                      (rel_ar_valid_i[0] & (ar_addr_fault[0]|ar_other_fault[0]|ar_id_fault[0])) |
                      voter_aw_valid_fault | voter_w_valid_fault | voter_b_ready_fault |
                      voter_ar_valid_fault | voter_r_ready_fault | voter_w_last_fault;

  assign fault_o[1] = (rel_aw_valid_i[0] & (aw_addr_fault[1]|aw_other_fault[1]|aw_id_fault[1]|aw_id_hi_err)) |
                      (rel_w_valid_i[0]  & (w_data_fault[1] |w_other_fault[1]))                              |
                      (rel_ar_valid_i[0] & (ar_addr_fault[1]|ar_other_fault[1]|ar_id_fault[1]|ar_id_hi_err));
endmodule
