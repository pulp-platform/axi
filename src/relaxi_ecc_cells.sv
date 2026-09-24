// relAXI ECC group codec cells. Field membership lives ONLY here.
// id is a separate codeword; *_other groups never contain id.

(* no_ungroup *)
(* no_boundary_optimization *)
module relaxi_id_enc #(
  parameter int unsigned IdWidth  = 0,
  parameter int unsigned EccWidth = hsiao_ecc_pkg::min_ecc(IdWidth)
) (
  input  logic [IdWidth-1:0]  id_i,
  output logic [IdWidth-1:0]  id_o,
  output logic [EccWidth-1:0] id_ecc_o
);
  logic [IdWidth+EccWidth-1:0] enc;
  hsiao_ecc_enc #(.DataWidth(IdWidth)) i_enc (.in(id_i), .out(enc));
  assign id_o     = id_i;
  assign id_ecc_o = enc[IdWidth +: EccWidth];
endmodule

(* no_ungroup *)
(* no_boundary_optimization *)
module relaxi_id_dec #(
  parameter int unsigned IdWidth  = 0,
  parameter int unsigned EccWidth = hsiao_ecc_pkg::min_ecc(IdWidth)
) (
  input  logic [IdWidth-1:0]  id_i,
  input  logic [EccWidth-1:0] id_ecc_i,
  output logic [IdWidth-1:0]  id_o,
  output logic [1:0]          err_o
);
  hsiao_ecc_dec #(.DataWidth(IdWidth)) i_dec (
    .in({id_ecc_i, id_i}), .out(id_o), .syndrome_o(), .err_o(err_o)
  );
endmodule

// ---- AW group: len,size,burst,lock,cache,prot,qos,region,atop,user ----
module relaxi_aw_other_enc #(
  parameter int unsigned UserWidth = 0,
  parameter int unsigned W = $bits(axi_pkg::len_t)+$bits(axi_pkg::size_t)+
      $bits(axi_pkg::burst_t)+1+$bits(axi_pkg::cache_t)+$bits(axi_pkg::prot_t)+
      $bits(axi_pkg::qos_t)+$bits(axi_pkg::region_t)+$bits(axi_pkg::atop_t)+UserWidth,
  parameter int unsigned E = hsiao_ecc_pkg::min_ecc(W)
) (
  input  axi_pkg::len_t len_i, input axi_pkg::size_t size_i,
  input  axi_pkg::burst_t burst_i, input logic lock_i,
  input  axi_pkg::cache_t cache_i, input axi_pkg::prot_t prot_i,
  input  axi_pkg::qos_t qos_i, input axi_pkg::region_t region_i,
  input  axi_pkg::atop_t atop_i, input logic [UserWidth-1:0] user_i,
  output logic [E-1:0] ecc_o
);
  logic [W+E-1:0] enc;
  hsiao_ecc_enc #(.DataWidth(W)) i_enc (
    .in({len_i,size_i,burst_i,lock_i,cache_i,prot_i,qos_i,region_i,atop_i,user_i}),
    .out(enc));
  assign ecc_o = enc[W +: E];
endmodule

module relaxi_aw_other_dec #(
  parameter int unsigned UserWidth = 0,
  parameter int unsigned W = $bits(axi_pkg::len_t)+$bits(axi_pkg::size_t)+
      $bits(axi_pkg::burst_t)+1+$bits(axi_pkg::cache_t)+$bits(axi_pkg::prot_t)+
      $bits(axi_pkg::qos_t)+$bits(axi_pkg::region_t)+$bits(axi_pkg::atop_t)+UserWidth,
  parameter int unsigned E = hsiao_ecc_pkg::min_ecc(W)
) (
  input  axi_pkg::len_t len_i, input axi_pkg::size_t size_i,
  input  axi_pkg::burst_t burst_i, input logic lock_i,
  input  axi_pkg::cache_t cache_i, input axi_pkg::prot_t prot_i,
  input  axi_pkg::qos_t qos_i, input axi_pkg::region_t region_i,
  input  axi_pkg::atop_t atop_i, input logic [UserWidth-1:0] user_i,
  input  logic [E-1:0] ecc_i,
  output axi_pkg::len_t len_o, output axi_pkg::size_t size_o,
  output axi_pkg::burst_t burst_o, output logic lock_o,
  output axi_pkg::cache_t cache_o, output axi_pkg::prot_t prot_o,
  output axi_pkg::qos_t qos_o, output axi_pkg::region_t region_o,
  output axi_pkg::atop_t atop_o, output logic [UserWidth-1:0] user_o,
  output logic [1:0] err_o
);
  hsiao_ecc_dec #(.DataWidth(W)) i_dec (
    .in({ecc_i,len_i,size_i,burst_i,lock_i,cache_i,prot_i,qos_i,region_i,atop_i,user_i}),
    .out({len_o,size_o,burst_o,lock_o,cache_o,prot_o,qos_o,region_o,atop_o,user_o}),
    .syndrome_o(), .err_o(err_o));
endmodule

// ---- AR group: same as AW WITHOUT atop ----
module relaxi_ar_other_enc #(
  parameter int unsigned UserWidth = 0,
  parameter int unsigned W = $bits(axi_pkg::len_t)+$bits(axi_pkg::size_t)+
      $bits(axi_pkg::burst_t)+1+$bits(axi_pkg::cache_t)+$bits(axi_pkg::prot_t)+
      $bits(axi_pkg::qos_t)+$bits(axi_pkg::region_t)+UserWidth,
  parameter int unsigned E = hsiao_ecc_pkg::min_ecc(W)
) (
  input  axi_pkg::len_t len_i, input axi_pkg::size_t size_i,
  input  axi_pkg::burst_t burst_i, input logic lock_i,
  input  axi_pkg::cache_t cache_i, input axi_pkg::prot_t prot_i,
  input  axi_pkg::qos_t qos_i, input axi_pkg::region_t region_i,
  input  logic [UserWidth-1:0] user_i,
  output logic [E-1:0] ecc_o
);
  logic [W+E-1:0] enc;
  hsiao_ecc_enc #(.DataWidth(W)) i_enc (
    .in({len_i,size_i,burst_i,lock_i,cache_i,prot_i,qos_i,region_i,user_i}),
    .out(enc));
  assign ecc_o = enc[W +: E];
endmodule

module relaxi_ar_other_dec #(
  parameter int unsigned UserWidth = 0,
  parameter int unsigned W = $bits(axi_pkg::len_t)+$bits(axi_pkg::size_t)+
      $bits(axi_pkg::burst_t)+1+$bits(axi_pkg::cache_t)+$bits(axi_pkg::prot_t)+
      $bits(axi_pkg::qos_t)+$bits(axi_pkg::region_t)+UserWidth,
  parameter int unsigned E = hsiao_ecc_pkg::min_ecc(W)
) (
  input  axi_pkg::len_t len_i, input axi_pkg::size_t size_i,
  input  axi_pkg::burst_t burst_i, input logic lock_i,
  input  axi_pkg::cache_t cache_i, input axi_pkg::prot_t prot_i,
  input  axi_pkg::qos_t qos_i, input axi_pkg::region_t region_i,
  input  logic [UserWidth-1:0] user_i,
  input  logic [E-1:0] ecc_i,
  output axi_pkg::len_t len_o, output axi_pkg::size_t size_o,
  output axi_pkg::burst_t burst_o, output logic lock_o,
  output axi_pkg::cache_t cache_o, output axi_pkg::prot_t prot_o,
  output axi_pkg::qos_t qos_o, output axi_pkg::region_t region_o,
  output logic [UserWidth-1:0] user_o,
  output logic [1:0] err_o
);
  hsiao_ecc_dec #(.DataWidth(W)) i_dec (
    .in({ecc_i,len_i,size_i,burst_i,lock_i,cache_i,prot_i,qos_i,region_i,user_i}),
    .out({len_o,size_o,burst_o,lock_o,cache_o,prot_o,qos_o,region_o,user_o}),
    .syndrome_o(), .err_o(err_o));
endmodule

// ---- B / R group: {resp, user} ----
module relaxi_resp_other_enc #(
  parameter int unsigned UserWidth = 0,
  parameter int unsigned W = $bits(axi_pkg::resp_t)+UserWidth,
  parameter int unsigned E = hsiao_ecc_pkg::min_ecc(W)
) (
  input  axi_pkg::resp_t resp_i, input logic [UserWidth-1:0] user_i,
  output logic [E-1:0] ecc_o
);
  logic [W+E-1:0] enc;
  hsiao_ecc_enc #(.DataWidth(W)) i_enc (.in({resp_i,user_i}), .out(enc));
  assign ecc_o = enc[W +: E];
endmodule

module relaxi_resp_other_dec #(
  parameter int unsigned UserWidth = 0,
  parameter int unsigned W = $bits(axi_pkg::resp_t)+UserWidth,
  parameter int unsigned E = hsiao_ecc_pkg::min_ecc(W)
) (
  input  axi_pkg::resp_t resp_i, input logic [UserWidth-1:0] user_i,
  input  logic [E-1:0] ecc_i,
  output axi_pkg::resp_t resp_o, output logic [UserWidth-1:0] user_o,
  output logic [1:0] err_o
);
  hsiao_ecc_dec #(.DataWidth(W)) i_dec (
    .in({ecc_i,resp_i,user_i}), .out({resp_o,user_o}),
    .syndrome_o(), .err_o(err_o));
endmodule
