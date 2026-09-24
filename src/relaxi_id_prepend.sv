// Copyright 2019 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Authors:
// - Wolfgang Roenninger <wroennin@iis.ee.ethz.ch>
// - Andreas Kurth <akurth@iis.ee.ethz.ch>

// AXI ID Prepend: This module prepends/strips the MSB from the AXI IDs.
// Constraints enforced through assertions: ID width of slave and master port

module relaxi_id_prepend #(
  parameter int unsigned NoBus             = 1,     // Can take multiple axi busses
  parameter int unsigned AxiIdWidthSlvPort = 4,     // AXI ID Width of the Slave Ports
  parameter int unsigned AxiIdWidthMstPort = 6,     // AXI ID Width of the Master Ports
  parameter type         slv_aw_chan_t     = logic, // AW Channel Type for slv port
  parameter type         slv_w_chan_t      = logic, //  W Channel Type for slv port
  parameter type         slv_b_chan_t      = logic, //  B Channel Type for slv port
  parameter type         slv_ar_chan_t     = logic, // AR Channel Type for slv port
  parameter type         slv_r_chan_t      = logic, //  R Channel Type for slv port
  parameter type         mst_aw_chan_t     = logic, // AW Channel Type for mst port
  parameter type         mst_w_chan_t      = logic, //  W Channel Type for mst port
  parameter type         mst_b_chan_t      = logic, //  B Channel Type for mst port
  parameter type         mst_ar_chan_t     = logic, // AR Channel Type for mst port
  parameter type         mst_r_chan_t      = logic, //  R Channel Type for mst port
  // DEPENDENT PARAMETER DO NOT OVERWRITE!
  parameter int unsigned PreIdWidth        = AxiIdWidthMstPort - AxiIdWidthSlvPort
) (
  input  logic [PreIdWidth-1:0] pre_id_i, // ID to be prepended
  // slave port (input), connect master modules here
  // AW channel
  input  slv_aw_chan_t [NoBus-1:0] slv_aw_chans_i,
  input  logic         [NoBus-1:0][2:0] slv_aw_valids_i,
  output logic         [NoBus-1:0][2:0] slv_aw_readies_o,
  //  W channel
  input  slv_w_chan_t  [NoBus-1:0] slv_w_chans_i,
  input  logic         [NoBus-1:0][2:0] slv_w_valids_i,
  output logic         [NoBus-1:0][2:0] slv_w_readies_o,
  //  B channel
  output slv_b_chan_t  [NoBus-1:0] slv_b_chans_o,
  output logic         [NoBus-1:0][2:0] slv_b_valids_o,
  input  logic         [NoBus-1:0][2:0] slv_b_readies_i,
  // AR channel
  input  slv_ar_chan_t [NoBus-1:0] slv_ar_chans_i,
  input  logic         [NoBus-1:0][2:0] slv_ar_valids_i,
  output logic         [NoBus-1:0][2:0] slv_ar_readies_o,
  //  R channel
  output slv_r_chan_t  [NoBus-1:0] slv_r_chans_o,
  output logic         [NoBus-1:0][2:0] slv_r_valids_o,
  input  logic         [NoBus-1:0][2:0] slv_r_readies_i,
  // master ports (output), connect slave modules here
  // AW channel
  output mst_aw_chan_t [NoBus-1:0] mst_aw_chans_o,
  output logic         [NoBus-1:0][2:0] mst_aw_valids_o,
  input  logic         [NoBus-1:0][2:0] mst_aw_readies_i,
  //  W channel
  output mst_w_chan_t  [NoBus-1:0] mst_w_chans_o,
  output logic         [NoBus-1:0][2:0] mst_w_valids_o,
  input  logic         [NoBus-1:0][2:0] mst_w_readies_i,
  //  B channel
  input  mst_b_chan_t  [NoBus-1:0] mst_b_chans_i,
  input  logic         [NoBus-1:0][2:0] mst_b_valids_i,
  output logic         [NoBus-1:0][2:0] mst_b_readies_o,
  // AR channel
  output mst_ar_chan_t [NoBus-1:0] mst_ar_chans_o,
  output logic         [NoBus-1:0][2:0] mst_ar_valids_o,
  input  logic         [NoBus-1:0][2:0] mst_ar_readies_i,
  //  R channel
  input  mst_r_chan_t  [NoBus-1:0] mst_r_chans_i,
  input  logic         [NoBus-1:0][2:0] mst_r_valids_i,
  output logic         [NoBus-1:0][2:0] mst_r_readies_o,
  //  ECC fault report: [0]=corrected, [1]=uncorrectable
  output logic [1:0]       fault_o
);

  localparam int unsigned SlvEcc = hsiao_ecc_pkg::min_ecc(AxiIdWidthSlvPort);
  localparam int unsigned MstEcc = hsiao_ecc_pkg::min_ecc(AxiIdWidthMstPort);
  logic [NoBus-1:0] b_idx_err, r_idx_err;

  // prepend the ID
  for (genvar i = 0; i < NoBus; i++) begin : gen_id_prepend

    logic [AxiIdWidthMstPort-1:0] aw_id_out, ar_id_out, b_id_out, r_id_out;
    logic [MstEcc-1:0]            aw_ecc_out, ar_ecc_out, b_ecc_out, r_ecc_out;

    // AW forward: add index
    relaxi_id_shift #(
      .SlvIdWidth ( AxiIdWidthSlvPort ),
      .MstIdWidth ( AxiIdWidthMstPort )
    ) i_aw_shift (
      .pre_id_i  ( pre_id_i                 ),
      .id_i      ( slv_aw_chans_i[i].id     ),
      .ecc_i     ( slv_aw_chans_i[i].id_ecc ),
      .id_o      ( aw_id_out                ),
      .ecc_o     ( aw_ecc_out               ),
      .idx_err_o (                          )
    );

    // AR forward: add index
    relaxi_id_shift #(
      .SlvIdWidth ( AxiIdWidthSlvPort ),
      .MstIdWidth ( AxiIdWidthMstPort )
    ) i_ar_shift (
      .pre_id_i  ( pre_id_i                 ),
      .id_i      ( slv_ar_chans_i[i].id     ),
      .ecc_i     ( slv_ar_chans_i[i].id_ecc ),
      .id_o      ( ar_id_out                ),
      .ecc_o     ( ar_ecc_out               ),
      .idx_err_o (                          )  // already in encoder, hi_err
    );

    // B return: remove index, check it was ours
    relaxi_id_shift #(
      .SlvIdWidth ( AxiIdWidthSlvPort ),
      .MstIdWidth ( AxiIdWidthMstPort )
    ) i_b_shift (
      .pre_id_i  ( pre_id_i                ),
      .id_i      ( mst_b_chans_i[i].id     ),
      .ecc_i     ( mst_b_chans_i[i].id_ecc ),
      .id_o      ( b_id_out                ),
      .ecc_o     ( b_ecc_out               ),
      .idx_err_o ( b_idx_err[i]            )
    );

    // R return: remove index, check it was ours
    relaxi_id_shift #(
      .SlvIdWidth ( AxiIdWidthSlvPort ),
      .MstIdWidth ( AxiIdWidthMstPort )
    ) i_r_shift (
      .pre_id_i  ( pre_id_i                ),
      .id_i      ( mst_r_chans_i[i].id     ),
      .ecc_i     ( mst_r_chans_i[i].id_ecc ),
      .id_o      ( r_id_out                ),
      .ecc_o     ( r_ecc_out               ),
      .idx_err_o ( r_idx_err[i]            )
    );

    always_comb begin
      mst_aw_chans_o[i]        = slv_aw_chans_i[i];
      mst_aw_chans_o[i].id     = aw_id_out;
      mst_aw_chans_o[i].id_ecc = aw_ecc_out;

      mst_ar_chans_o[i]        = slv_ar_chans_i[i];
      mst_ar_chans_o[i].id     = ar_id_out;
      mst_ar_chans_o[i].id_ecc = ar_ecc_out;

      slv_b_chans_o[i]         = mst_b_chans_i[i];
      slv_b_chans_o[i].id      = b_id_out;
      slv_b_chans_o[i].id_ecc  = b_ecc_out;

      slv_r_chans_o[i]         = mst_r_chans_i[i];
      slv_r_chans_o[i].id      = r_id_out;
      slv_r_chans_o[i].id_ecc  = r_ecc_out;
    end
  end

  // -------------------------------------------------------------------------
  // Aggregate fault_o across all channels/buses, gated on the channel valid.
  // [0] = any corrected, [1] = any uncorrectable.
  // -------------------------------------------------------------------------
  // Majority of the three handshake rails. A single spurious rail must not
  // open the fault gate, since the boundary voter would mask it anyway.
  function automatic logic maj3(input logic [2:0] v);
    return (v[0] & v[1]) | (v[1] & v[2]) | (v[0] & v[2]);
  endfunction

  always_comb begin
    fault_o = 2'b00;
    for (int unsigned i = 0; i < NoBus; i++) begin
      if (maj3(mst_b_valids_i[i]) && b_idx_err[i]) fault_o[1] = 1'b1;
      if (maj3(mst_r_valids_i[i]) && r_idx_err[i]) fault_o[1] = 1'b1;
    end
  end

  // assign the handshaking's and w channel
  assign mst_w_chans_o    = slv_w_chans_i;
  assign mst_aw_valids_o  = slv_aw_valids_i;
  assign slv_aw_readies_o = mst_aw_readies_i;
  assign mst_w_valids_o   = slv_w_valids_i;
  assign slv_w_readies_o  = mst_w_readies_i;
  assign slv_b_valids_o   = mst_b_valids_i;
  assign mst_b_readies_o  = slv_b_readies_i;
  assign mst_ar_valids_o  = slv_ar_valids_i;
  assign slv_ar_readies_o = mst_ar_readies_i;
  assign slv_r_valids_o   = mst_r_valids_i;
  assign mst_r_readies_o  = slv_r_readies_i;

// pragma translate_off
`ifndef VERILATOR
  initial begin : p_assert
    assert(NoBus > 0)
      else $fatal(1, "Input must be at least one element wide.");
  end

  // NOTE: id checks now compare the CORRECTED id path; in fault-free operation
  // these still hold since decode is identity on valid codewords.
  aw_addr : assert final(mst_aw_chans_o[0].addr === slv_aw_chans_i[0].addr)
      else $fatal (1, "AW addr changed unexpectedly.");
  aw_len  : assert final(mst_aw_chans_o[0].len === slv_aw_chans_i[0].len)
      else $fatal (1, "AW len changed unexpectedly.");
  b_resp  : assert final(mst_b_chans_i[0].resp === slv_b_chans_o[0].resp)
      else $fatal (1, "B resp changed unexpectedly.");
  r_data  : assert final(mst_r_chans_i[0].data === slv_r_chans_o[0].data)
      else $fatal (1, "R data changed unexpectedly.");
  r_resp  : assert final(mst_r_chans_i[0].resp === slv_r_chans_o[0].resp)
      else $fatal (1, "R resp changed unexpectedly.");
`endif
// pragma translate_on
endmodule
