// Copyright 2019 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Author: Wolfgang Roenninger <wroennin@ethz.ch>

// AXI ADDR DECODE: Address decoder for the axi_full_xbar
// Maps the input address combinational to a master port index.
// The Address Map `addr_map_i` is a paced array of xbar_rules.
// Two examples are given in `axi_pkg` for an address width of 32 and 64 bit.
// The rule on the MSB position in the array wins if there is an overlap
// with the ranges.

// `en_default_mst_port_i`: This option allows for a not mapped address to be decoded
// onto a default master port index. If enabled `dec_error_o` is always `1'b0`.

// Assertions: The module checks every time there is a change in the address mapping
// if the resulting map is valid. Fatals when `start_addr` is higher than `end_addr`
// and on a mapping for a master port index that is not allowed from the parameter.
// Issues warnings if it finds overlapping address regions.

module axi_addr_decode #(
  parameter int unsigned NoMstPorts = 1,                       // Number MST in rules
  parameter int unsigned NoRules    = 1,                       // Total Number of rules
  parameter type         addr_t     = logic,                   // AXI address type
  parameter type         rule_t     = axi_pkg::xbar_rule_64_t, // rule type
  // DEPENDENT PARAMETERS DO NOT OVERWRITE!
  parameter type         mst_port_idx_t = logic [$clog2(NoMstPorts)-1:0] // master port index type
) (
  input  addr_t               addr_i,         // Address to decode
  input  rule_t [NoRules-1:0] addr_map_i,     // The address map: rule with the highest index wins
  output mst_port_idx_t       mst_port_idx_o, // output id of the slv
  output logic                dec_valid_o,    // decode is valid
  output logic                dec_error_o,    // decode is not valid
  // Default slave enable
  input  logic                en_default_mst_port_i, // enable default salve port
  input  mst_port_idx_t       default_mst_port_idx_i // Id of default slave
);

  logic [NoRules-1:0] matched_rules; // purely for addr map debugging

  always_comb begin : proc_addr_decode
    // default assignments
    matched_rules  = '0;
    dec_valid_o    = 1'b0;
    dec_error_o    = (en_default_mst_port_i) ? 1'b0 : 1'b1;
    mst_port_idx_o = (en_default_mst_port_i) ? default_mst_port_idx_i : '0;

    // match the rules
    for (int unsigned i = 0; i < NoRules; i++) begin
      if ((addr_i >= addr_map_i[i].start_addr) && (addr_i < addr_map_i[i].end_addr)) begin
        matched_rules[i] = 1'b1;
        dec_valid_o      = 1'b1;
        dec_error_o      = 1'b0;
        mst_port_idx_o   = mst_port_idx_t'(addr_map_i[i].mst_port_idx);
      end
    end
  end

  // Assumptions and assertions
  `ifndef VERILATOR
  // pragma translate_off
  initial begin : proc_check_parameters
    assume ($bits(addr_i) == $bits(addr_map_i[0].start_addr)) else
      $warning($sformatf("axi_addr_decode> input address has %d bits and address map has %d bits.",
        $bits(addr_i), $bits(addr_map_i[0].start_addr)));
    assume (NoRules > 0) else
      $fatal(1, $sformatf("axi_addr_decode> at least one rule needed"));
  end

  assert final ($onehot0(matched_rules)) else
    $warning("axi_addr_decode> More than one bit set in the one-hot signal, matched_rules");

  for (genvar i = 0; i < NoRules; i++) begin : gen_assert_0
    for (genvar j = 0; j < NoRules; j++) begin : gen_assert_1
      if((i != j) && (i < j)) begin : gen_check
        // These assumptions check the validity of the address map.
        // The assumptions gets generated for each distinct pair of rules.
        // Each assumption is present two times, as they rely on one rules being
        // effectively ordered. Only one of the rules with the same function is
        // active at a time for a given pair.
        // check_start:        Enforces a smaller start than end address.
        // check_mst_port_idx: Enforces a valid master port index in the rule.
        // check_overlap:      Warns if there are overlapping address regions.
        // check_same_addr:    Warns the not cached overlaps from check_overlap.
        check_start_0 : assume final (addr_map_i[i].start_addr <= addr_map_i[i].end_addr) else
          $fatal(1, $sformatf("This rule has a higher start than end address!!!\n\
              Violating rule %d.\n\
              Rule> mst_port_idx: %h START: %h END: %h\n\
              axi_addr_decode>  #####################################################",
              i ,addr_map_i[i].mst_port_idx, addr_map_i[i].start_addr, addr_map_i[i].end_addr));
        check_start_1 : assume final (addr_map_i[j].start_addr <= addr_map_i[j].end_addr) else
          $fatal(1, $sformatf("This rule has a higher start than end address!!!\n\
              Violating rule %d.\n\
              Rule> mst_port_idx: %h START: %h END: %h\n\
              axi_addr_decode>  #####################################################",
              i ,addr_map_i[j].mst_port_idx, addr_map_i[j].start_addr, addr_map_i[j].end_addr));
        // check the SLV ids
        check_mst_port_idx_0 : assume final (addr_map_i[i].mst_port_idx < NoMstPorts) else
          $fatal(1, $sformatf("This rule has a slave id that is not allowed!!!\n\
              Violating rule %d.\n\
              Rule> mst_port_idx: %h START: %h END: %h\n\
              Rule> MAX_ID: %h\n\
              axi_addr_decode>  #####################################################",
              i, addr_map_i[i].mst_port_idx, addr_map_i[i].start_addr, addr_map_i[i].end_addr,
              (NoMstPorts-1)));
        check_mst_port_idx_1 : assume final (addr_map_i[j].mst_port_idx < NoMstPorts) else
          $fatal(1, $sformatf("This rule has a slave id that is not allowed!!!\n\
              Violating rule %d.\n\
              Rule> mst_port_idx: %h START: %h END: %h\n\
              Rule> MAX_ID: %h\n\
              axi_addr_decode>  #####################################################",
              j, addr_map_i[j].mst_port_idx, addr_map_i[j].start_addr, addr_map_i[j].end_addr,
              (NoMstPorts-1)));
        // overlap check
        check_overlap_0 : assume final ((addr_map_i[i].start_addr >= addr_map_i[j].start_addr) ||
                                        (addr_map_i[i].end_addr <= addr_map_i[j].start_addr)) else
          $warning($sformatf("Overlapping address region found!!!\n\
              Rule %d: SLV ID: %h START: %h END: %h\n\
              Rule %d: SLV ID: %h START: %h END: %h\n\
              axi_addr_decode>  #####################################################",
              i, addr_map_i[i].mst_port_idx, addr_map_i[i].start_addr, addr_map_i[i].end_addr,
              j, addr_map_i[j].mst_port_idx, addr_map_i[j].start_addr, addr_map_i[j].end_addr));
        check_overlap_1 : assume final ((addr_map_i[j].start_addr >= addr_map_i[i].start_addr) ||
                                        (addr_map_i[j].end_addr <= addr_map_i[i].start_addr)) else
          $warning($sformatf("Overlapping address region found!!!\n\
              Rule %d: ID: %h START: %h END: %h\n\
              Rule %d: ID: %h START: %h END: %h\n\
              axi_addr_decode>  #####################################################",
              i, addr_map_i[i].mst_port_idx, addr_map_i[i].start_addr, addr_map_i[i].end_addr,
              j, addr_map_i[j].mst_port_idx, addr_map_i[j].start_addr, addr_map_i[j].end_addr));
        check_same_addr : assume final (addr_map_i[i].start_addr != addr_map_i[j].start_addr) else
          $warning($sformatf("Overlapping address region found!!!\n\
              Rule %d: ID: %h START: %h END: %h\n\
              Rule %d: ID: %h START: %h END: %h\n\
              axi_addr_decode>  #####################################################",
              i, addr_map_i[i].mst_port_idx, addr_map_i[i].start_addr, addr_map_i[i].end_addr,
              j, addr_map_i[j].mst_port_idx, addr_map_i[j].start_addr, addr_map_i[j].end_addr));
      end
    end
  end
  // pragma translate_on
  `endif
endmodule
