// Constant-XOR ID index shift. Adds or removes a port index from an ID
// codeword without decoding. Hsiao codes are linear, so XORing a constant
// into the ID field and its precomputed parity into the ECC field yields a
// valid codeword for the modified ID. XOR is self-inverse, so the same
// instance parameters serve both the add and remove directions.
module relaxi_id_shift #(
  parameter int unsigned SlvIdWidth = 5,
  parameter int unsigned MstIdWidth = 9,
  // DEPENDENT, DO NOT OVERRIDE
  parameter int unsigned PreIdWidth = MstIdWidth - SlvIdWidth,
  parameter int unsigned Ecc        = hsiao_ecc_pkg::min_ecc(MstIdWidth)
) (
  input  logic [PreIdWidth-1:0] pre_id_i,
  input  logic [MstIdWidth-1:0] id_i,
  input  logic [Ecc-1:0]        ecc_i,
  output logic [MstIdWidth-1:0] id_o,
  output logic [Ecc-1:0]        ecc_o,
  output logic                  idx_err_o
);

  logic [MstIdWidth-1:0] id_const;
  logic [Ecc-1:0]        ecc_const;

  assign id_const = {pre_id_i, {SlvIdWidth{1'b0}}};

  relaxi_id_enc #(.IdWidth(MstIdWidth)) i_const_enc (
    .id_i     ( id_const  ),
    .id_o     (           ),
    .id_ecc_o ( ecc_const )
  );

  assign id_o      = id_i  ^ id_const;
  assign ecc_o     = ecc_i ^ ecc_const;
  assign idx_err_o = |id_o[MstIdWidth-1 -: PreIdWidth];

endmodule
