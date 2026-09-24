// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Chaoqun Liang <chaoqun.liang@unibo.it>

module relaxi_ar_other_decoder #(
  /// Configuration of the bus
  parameter axi_pkg::cfg_t Cfg           = axi_pkg::AxiDefaultConfig,

  parameter type               a_optional_t  = logic,
  parameter int unsigned       OtherEccWidth = axi_pkg::axi_a_other_ecc_width(Cfg)
) (
  input  logic                       we_i,
  input  logic [Cfg.DataWidth/8-1:0] be_i,
  input  logic [Cfg.IdWidth    -1:0] aid_i,
  input  a_optional_t                a_optional_i,
  input  logic [  OtherEccWidth-1:0] other_ecc_i,

  output logic                       we_o,
  output logic [Cfg.DataWidth/8-1:0] be_o,
  output logic [Cfg.IdWidth    -1:0] aid_o,
  output a_optional_t                a_optional_o,

  output logic [1:0]                 fault_o
);

  hsiao_ecc_dec #(
    .DataWidth (axi_pkg::axi_a_other_width(Cfg))
  ) i_a_remaining_dec (
    .in        ( {other_ecc_i,
                  we_i,
                  be_i,
                  aid_i,
                  a_optional_i} ),
    .out       ( {we_o,
                  be_o,
                  aid_o,
                  a_optional_o} ),
    .syndrome_o(),
    .err_o     (fault_o)
  );

endmodule