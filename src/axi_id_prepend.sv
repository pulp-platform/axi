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
// Constraints enforced through assertions: ID width of subordinate and manager port

module axi_id_prepend #(
  parameter int unsigned NumBus         = 1,     // Can take multiple axi busses
  parameter int unsigned IdWidthSbrPort = 4,     // AXI ID Width of the Subordinate Ports
  parameter int unsigned IdWidthMgrPort = 6,     // AXI ID Width of the Manager Ports
  parameter type         sbr_aw_chan_t  = logic, // AW Channel Type for sbr port
  parameter type         sbr_w_chan_t   = logic, //  W Channel Type for sbr port
  parameter type         sbr_b_chan_t   = logic, //  B Channel Type for sbr port
  parameter type         sbr_ar_chan_t  = logic, // AR Channel Type for sbr port
  parameter type         sbr_r_chan_t   = logic, //  R Channel Type for sbr port
  parameter type         mgr_aw_chan_t  = logic, // AW Channel Type for mgr port
  parameter type         mgr_w_chan_t   = logic, //  W Channel Type for mgr port
  parameter type         mgr_b_chan_t   = logic, //  B Channel Type for mgr port
  parameter type         mgr_ar_chan_t  = logic, // AR Channel Type for mgr port
  parameter type         mgr_r_chan_t   = logic, //  R Channel Type for mgr port
  // DEPENDENT PARAMETER DO NOT OVERWRITE!
  parameter int unsigned PreIdWidth     = IdWidthMgrPort - IdWidthSbrPort
) (
  input  logic [PreIdWidth-1:0] pre_id_i, // ID to be prepended
  // subordinate port (input), connect manager modules here
  // AW channel
  input  sbr_aw_chan_t [NumBus-1:0] sbr_aw_chans_i,
  input  logic         [NumBus-1:0] sbr_aw_valids_i,
  output logic         [NumBus-1:0] sbr_aw_readies_o,
  //  W channel
  input  sbr_w_chan_t  [NumBus-1:0] sbr_w_chans_i,
  input  logic         [NumBus-1:0] sbr_w_valids_i,
  output logic         [NumBus-1:0] sbr_w_readies_o,
  //  B channel
  output sbr_b_chan_t  [NumBus-1:0] sbr_b_chans_o,
  output logic         [NumBus-1:0] sbr_b_valids_o,
  input  logic         [NumBus-1:0] sbr_b_readies_i,
  // AR channel
  input  sbr_ar_chan_t [NumBus-1:0] sbr_ar_chans_i,
  input  logic         [NumBus-1:0] sbr_ar_valids_i,
  output logic         [NumBus-1:0] sbr_ar_readies_o,
  //  R channel
  output sbr_r_chan_t  [NumBus-1:0] sbr_r_chans_o,
  output logic         [NumBus-1:0] sbr_r_valids_o,
  input  logic         [NumBus-1:0] sbr_r_readies_i,
  // manager ports (output), connect subordinate modules here
  // AW channel
  output mgr_aw_chan_t [NumBus-1:0] mgr_aw_chans_o,
  output logic         [NumBus-1:0] mgr_aw_valids_o,
  input  logic         [NumBus-1:0] mgr_aw_readies_i,
  //  W channel
  output mgr_w_chan_t  [NumBus-1:0] mgr_w_chans_o,
  output logic         [NumBus-1:0] mgr_w_valids_o,
  input  logic         [NumBus-1:0] mgr_w_readies_i,
  //  B channel
  input  mgr_b_chan_t  [NumBus-1:0] mgr_b_chans_i,
  input  logic         [NumBus-1:0] mgr_b_valids_i,
  output logic         [NumBus-1:0] mgr_b_readies_o,
  // AR channel
  output mgr_ar_chan_t [NumBus-1:0] mgr_ar_chans_o,
  output logic         [NumBus-1:0] mgr_ar_valids_o,
  input  logic         [NumBus-1:0] mgr_ar_readies_i,
  //  R channel
  input  mgr_r_chan_t  [NumBus-1:0] mgr_r_chans_i,
  input  logic         [NumBus-1:0] mgr_r_valids_i,
  output logic         [NumBus-1:0] mgr_r_readies_o
);

  // prepend the ID
  for (genvar i = 0; i < NumBus; i++) begin : gen_id_prepend
    if (PreIdWidth == 0) begin : gen_no_prepend
      assign mgr_aw_chans_o[i] = sbr_aw_chans_i[i];
      assign mgr_ar_chans_o[i] = sbr_ar_chans_i[i];
    end else begin : gen_prepend
      always_comb begin
        mgr_aw_chans_o[i] = sbr_aw_chans_i[i];
        mgr_ar_chans_o[i] = sbr_ar_chans_i[i];
        mgr_aw_chans_o[i].id = {pre_id_i, sbr_aw_chans_i[i].id[IdWidthSbrPort-1:0]};
        mgr_ar_chans_o[i].id = {pre_id_i, sbr_ar_chans_i[i].id[IdWidthSbrPort-1:0]};
      end
    end
    // The ID is in the highest bits of the struct, so an assignment from a channel with a wide ID
    // to a channel with a shorter ID correctly cuts the prepended ID.
    assign sbr_b_chans_o[i] = mgr_b_chans_i[i];
    assign sbr_r_chans_o[i] = mgr_r_chans_i[i];
  end

  // assign the handshaking's and w channel
  assign mgr_w_chans_o    = sbr_w_chans_i;
  assign mgr_aw_valids_o  = sbr_aw_valids_i;
  assign sbr_aw_readies_o = mgr_aw_readies_i;
  assign mgr_w_valids_o   = sbr_w_valids_i;
  assign sbr_w_readies_o  = mgr_w_readies_i;
  assign sbr_b_valids_o   = mgr_b_valids_i;
  assign mgr_b_readies_o  = sbr_b_readies_i;
  assign mgr_ar_valids_o  = sbr_ar_valids_i;
  assign sbr_ar_readies_o = mgr_ar_readies_i;
  assign sbr_r_valids_o   = mgr_r_valids_i;
  assign mgr_r_readies_o  = sbr_r_readies_i;

// pragma translate_off
`ifndef VERILATOR
  initial begin : p_assert
    assert(NumBus > 0)
      else $fatal(1, "Input must be at least one element wide.");
    assert(PreIdWidth == ($bits(mgr_aw_chans_o[0].id) - $bits(sbr_aw_chans_i[0].id)))
      else $fatal(1, "Prepend ID Width must be: $bits(mgr_aw_chans_o.id)-$bits(sbr_aw_chans_i.id)");
    assert ($bits(mgr_aw_chans_o[0].id) > $bits(sbr_aw_chans_i[0].id))
      else $fatal(1, "The manager AXI port has to have a wider ID than the subordinate port.");
  end

  aw_id   : assert final(
      mgr_aw_chans_o[0].id[$bits(sbr_aw_chans_i[0].id)-1:0] === sbr_aw_chans_i[0].id)
        else $fatal (1, "Something with the AW channel ID prepending went wrong.");
  aw_addr : assert final(mgr_aw_chans_o[0].addr === sbr_aw_chans_i[0].addr)
      else $fatal (1, "Something with the AW channel ID prepending went wrong.");
  aw_len  : assert final(mgr_aw_chans_o[0].len === sbr_aw_chans_i[0].len)
      else $fatal (1, "Something with the AW channel ID prepending went wrong.");
  aw_size : assert final(mgr_aw_chans_o[0].size === sbr_aw_chans_i[0].size)
      else $fatal (1, "Something with the AW channel ID prepending went wrong.");
  aw_qos  : assert final(mgr_aw_chans_o[0].qos === sbr_aw_chans_i[0].qos)
      else $fatal (1, "Something with the AW channel ID prepending went wrong.");

  b_id    : assert final(
      mgr_b_chans_i[0].id[$bits(sbr_b_chans_o[0].id)-1:0] === sbr_b_chans_o[0].id)
        else $fatal (1, "Something with the B channel ID stripping went wrong.");
  b_resp  : assert final(mgr_b_chans_i[0].resp === sbr_b_chans_o[0].resp)
      else $fatal (1, "Something with the B channel ID stripping went wrong.");

  ar_id   : assert final(
      mgr_ar_chans_o[0].id[$bits(sbr_ar_chans_i[0].id)-1:0] === sbr_ar_chans_i[0].id)
        else $fatal (1, "Something with the AR channel ID prepending went wrong.");
  ar_addr : assert final(mgr_ar_chans_o[0].addr === sbr_ar_chans_i[0].addr)
      else $fatal (1, "Something with the AR channel ID prepending went wrong.");
  ar_len  : assert final(mgr_ar_chans_o[0].len === sbr_ar_chans_i[0].len)
      else $fatal (1, "Something with the AR channel ID prepending went wrong.");
  ar_size : assert final(mgr_ar_chans_o[0].size === sbr_ar_chans_i[0].size)
      else $fatal (1, "Something with the AR channel ID prepending went wrong.");
  ar_qos  : assert final(mgr_ar_chans_o[0].qos === sbr_ar_chans_i[0].qos)
      else $fatal (1, "Something with the AR channel ID prepending went wrong.");

  r_id    : assert final(mgr_r_chans_i[0].id[$bits(sbr_r_chans_o[0].id)-1:0] === sbr_r_chans_o[0].id)
      else $fatal (1, "Something with the R channel ID stripping went wrong.");
  r_data  : assert final(mgr_r_chans_i[0].data === sbr_r_chans_o[0].data)
      else $fatal (1, "Something with the R channel ID stripping went wrong.");
  r_resp  : assert final(mgr_r_chans_i[0].resp === sbr_r_chans_o[0].resp)
      else $fatal (1, "Something with the R channel ID stripping went wrong.");
`endif
// pragma translate_on
endmodule
