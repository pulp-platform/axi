// Copyright (c) 2019 ETH Zurich, University of Bologna
//
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// File:   tag_store.sv
// Author: Wolfgang Roenninger <wroennin@student.ethz.ch>
// Date:   06.06.2019
//
// Description: This is the Tag storage for the LLC
//              There are four types of requests which can be made onto this unit.
//              BIST:   The pattern gets written or read to all macros, BIST resulte gets activated
//              FLUSH:  Perform a way trageted eviction
//              LOOKUP: Perform a tag lookup in all non SPM ways, hit/eviction gets set if needed
//              STORE:  Store the given tag plus flags in a given way
//

// register macros
`include "common_cells/registers.svh"

module axi_llc_tag_store #(
  parameter axi_llc_pkg::llc_cfg_t Cfg = -1
) (
  input  logic clk_i,   // Clock
  input  logic rst_ni,  // Asynchronous reset active low
  input  logic test_i,  // to enable during testing (activates sram bypass)
  // inputs
  // Which ways are disabled for STORE requests, because they are beeing used as SPM
  input  logic [Cfg.SetAssociativity-1:0] spm_lock_i,
  // LOOKUP have to be the inverse of the flushed signal, as during flushing
  // other mem accesses on ways that are actively flushing could be valid
  input  logic [Cfg.SetAssociativity-1:0] flushed_i,
  // -------------------------------------------------
  // request
  // control
  input  logic                            valid_i,      // valid request to the tag storage
  output logic                            ready_o,      // tag storage is ready for a request
  input  axi_llc_pkg::tag_req_e           req_mode_i,   // what mode the request has
  // In which way should the request be operated on
  input  logic [Cfg.SetAssociativity-1:0] way_ind_i,
  // Is the Cache index of the lookup/write, equals Line Address
  input  logic [Cfg.IndexLength-1:0]      index_i,
  // Indicates in the SRAM that the Tag inside is dirty (on write requests to the cache)
  input  logic                            tag_dit_i,
  // Tag for which the lookup or the write should be done
  input  logic [Cfg.TagLength-1:0]        tag_i,
  // --------------------------------------------------
  // outputs
  output logic [Cfg.SetAssociativity-1:0] way_ind_o,    // cache operation has to be on this way
  output logic                            hit_o,        // request has a cache hit
  output logic                            evict_o,      // line has dirty data in it -> evict
  output logic [Cfg.TagLength-1:0]        tag_o,        // tag for eviction
  output logic                            dit_o,        // eviction tag has the dirty field set
  output logic                            valid_o,      // output of the detection is valid
  input  logic                            ready_i,      // handshake
  // --------------------------------------------------
  // BIST output
  output logic [Cfg.SetAssociativity-1:0] bist_res_o,   // BIST output
  output logic                            bist_valid_o  // BIST output is valid
);

  // typedef, because we use in this module many signals with the width of SetAssiciativity
  typedef logic [Cfg.SetAssociativity-1:0] indi_t;  // stands for indicator
  typedef logic [Cfg.IndexLength-1:0]      index_t; // index type (equals the address for sram)

  // typedef to have consistent tag data (that what gets written into the sram)
  localparam TagDataLen = Cfg.TagLength + 2;
  typedef struct packed {
    logic                     val;
    logic                     dit;
    logic [Cfg.TagLength-1:0] tag;
  } tag_t;

  // signals horizontally over the inputs to the tag srams
  tag_t   tag; // here we aggregate the inputs in for easyer handeling

  // signals to/from the pattern generator
  logic   gen_valid,   gen_ready;
  index_t index_gen;
  tag_t   pattern_gen;
  logic   req_gen,     we_gen;
  logic   eoc_gen;

  // signals around the sram blocks
  // read data tag is defined inside generate block further down
  indi_t  we_ram   ; // write enable this ram
  indi_t  req_ram  ; // request this sram
  index_t index_ram; // address to the sram
  tag_t   tag_w_ram; // write data to the sram

  // Flip Flops parallel to the Tag SRAM
  logic   load;
  indi_t  way_ind_d,  way_ind_q;
  index_t index_d,    index_q;
  tag_t   tag_d,      tag_q;

  // signals horizontally along the outputs of the srams
  indi_t  tag_val; // output sram tag valid
  indi_t  tag_dit; // output sram tag dirty
  indi_t  tag_equ; // signal that tag_q and the one from the sram are equal
  // hit indicator
  indi_t  hit;
  logic   hit_red;

  //signals from the evict_box
  logic   evict_req;
  indi_t  evict_way_ind;
  logic   evict_flag;
  logic   evict_valid;

  // unit status
  logic                  busy_d,     busy_q, load_busy;
  axi_llc_pkg::tag_req_e req_mode_d, req_mode_q;

  // BIST result
  indi_t bist_res;
  logic  bist_valid;

  // signal for tag output mux
  tag_t [Cfg.SetAssociativity-1:0] tag_out;

  // gathering of the tag inputs to the struct
  // only when we perform a tag store operation, then the tag gets valid
  assign tag.val = (req_mode_i == axi_llc_pkg::STORE) ? 1'b1 : 1'b0;
  assign tag.dit = tag_dit_i;
  assign tag.tag = tag_i;

  assign hit_red = |hit;

  always_comb begin : proc_control
    //default assignments
    busy_d     = busy_q;
    load_busy  = 1'b0;
    req_mode_d = req_mode_q;
    way_ind_d  = way_ind_q;
    index_d    = index_q;
    tag_d      = tag_q;
    load       = 1'b0;  // load the registers parallel to the tag srams
    ready_o    = 1'b0;
    gen_valid  = 1'b0;
    // request to the srams
    req_ram    = '0;
    we_ram     = '0;
    index_ram  = '0;
    tag_w_ram  = '0;
    // requests to the evict box
    evict_req  = 1'b0;
    // unit outputs other than tag
    valid_o    = 1'b0;
    way_ind_o  = '0;
    hit_o      = '0;
    evict_o    = '0;
    // bist signals
    bist_valid = 1'b0;

    // we have an operation to do on the tag storages
    if (busy_q) begin
      case (req_mode_q)
        // BIST / init is running
        axi_llc_pkg::BIST : begin
          index_ram  = index_gen;
          req_ram    = req_gen ? way_ind_q : '0;
          we_ram     = we_gen  ? way_ind_q : '0;
          tag_w_ram  = pattern_gen;
          // also load the register parallel to the macros, for comparison
          load       = 1'b1;
          tag_d      = pattern_gen;
          // repurpose index register [0] for bist_valid flag, when the comparison of BIST is valid
          index_d[0] = ~we_gen & req_gen;
          bist_valid = index_q[0];
          // if finished, go to idle
          if (eoc_gen) begin
            busy_d    = 1'b0;
            load_busy = 1'b1;
          end
        end
        // we had a flush request to a position, check dirty and act accordingly
        axi_llc_pkg::FLUSH : begin
          // Regardless if the flushed tag is dirty or not, we have valid output
          // tag mux gets set with way_ind_o
          way_ind_o = way_ind_q;
          evict_o   = |(way_ind_q & tag_val & tag_dit);
          valid_o   = 1'b1;
          // if the output gets eaten, store all 0's back into the sram and unit to not busy
          if (ready_i) begin
            busy_d    = 1'b0;
            load_busy = 1'b1;
            index_ram = index_q;
            req_ram   = way_ind_q;
            we_ram    = way_ind_q;
          end
        end
        // Had a normal lookup, Hit detection
        axi_llc_pkg::LOOKUP : begin
          // set the signals for the hit generation
          evict_req = (hit_red) ? 1'b0 : 1'b1;
          // output generation
          way_ind_o = (hit_red) ? hit  : evict_way_ind;
          hit_o     = (hit_red);
          evict_o   = (hit_red) ? 1'b0 : evict_flag;
          valid_o   = (hit_red) ? 1'b1 : evict_valid;
          // output gets eaten, decide what to do next
          if (valid_o & ready_i) begin
            // check what would be the next request, default go to not busy
            busy_d    = 1'b0;
            load_busy = 1'b1;
            if (valid_i) begin
              // only be fast if there is a lookup or store next
              case (req_mode_i)
                axi_llc_pkg::LOOKUP : begin
                  // stay busy, as the result of the next lookup is availanle next cycle
                  busy_d     = 1'b1;
                  ready_o    = 1'b1;
                  req_mode_d = req_mode_i;
                  way_ind_d  = ~flushed_i;
                  index_d    = index_i;
                  tag_d      = tag;
                  load       = 1'b1;
                  req_ram    = ~flushed_i;
                  index_ram  = index_i;
                end
                axi_llc_pkg::STORE : begin
                  ready_o    = 1'b1;
                  req_mode_d = req_mode_i;
                  load       = 1'b1;
                  index_ram  = index_i;
                  req_ram    = way_ind_i;
                  we_ram     = way_ind_i;
                  tag_w_ram  = tag;
                end
                default : /* go back to idle, do nothing, we can be slow for Flush and BIST */;
              endcase
            end
          end
        end
        default : begin
          // should never be triggered, this would mean a STORE operation went into busy
          busy_d    = 1'b0;
          load_busy = 1'b1;
        end
      endcase

    // we do not have any request so we are ready when we have a request
    end else begin
      // request is valid
      if (valid_i) begin
        load       = 1'b1;
        req_mode_d = req_mode_i;
        case (req_mode_i)
          // Initialization / BIST
          axi_llc_pkg::BIST : begin
            // start this mode, if pattern gen is also ready
            gen_valid = 1'b1;
            if (gen_ready) begin
              ready_o   = 1'b1;
              busy_d    = 1'b1;
              load_busy = 1'b1;
              way_ind_d = way_ind_i;
            end
          end
          // Flush this Position
          axi_llc_pkg::FLUSH : begin
            ready_o   = 1'b1;
            busy_d    = 1'b1;
            load_busy = 1'b1;
            way_ind_d = way_ind_i;
            index_d   = index_i;
            req_ram   = way_ind_i;
            index_ram = index_i;
          end
          // Lookup, next cycle Hit detection
          axi_llc_pkg::LOOKUP : begin
            ready_o   = 1'b1;
            busy_d    = 1'b1;
            load_busy = 1'b1;
            way_ind_d = ~flushed_i;
            index_d   = index_i;
            tag_d     = tag;
            req_ram   = ~flushed_i;
            index_ram = index_i;
          end
          // Store the tag
          axi_llc_pkg::STORE : begin
            // we do not need to switch to busy, because there will be no output
            ready_o   = 1'b1;
            req_ram   = way_ind_i;
            we_ram    = way_ind_i;
            index_ram = index_i;
            tag_w_ram = tag;
          end
          default : /* default */;
        endcase
      end
    end
  end // proc_control

  // tag output multiplexer
  always_comb begin : proc_tag_out_mux
    tag_o = '0;
    dit_o = 1'b0;
    for (int unsigned i = 0; i < Cfg.SetAssociativity; i++) begin
      if (way_ind_o[i]) begin
        tag_o = tag_out[i].tag;
        dit_o = tag_out[i].dit;
      end
    end
  end // proc_tag_out_mux

  // generate for each Way once
  for (genvar i = 0; unsigned'(i) < Cfg.SetAssociativity; i++) begin : proc_tag
    tag_t tag_r_ram;    // read data from the sram
    tag_t tag_compared; // comparison result of tags

    axi_llc_sram #(
      .DATA_WIDTH (  TagDataLen ),
      .N_WORDS    ( Cfg.NoLines )
    ) i_tag_store (
      .clk_i   (      clk_i ),
      .rst_ni  (     rst_ni ),
      .test_i  (     test_i ),
      .req_i   ( req_ram[i] ),
      .we_i    (  we_ram[i] ),
      .addr_i  (  index_ram ),
      .wdata_i (  tag_w_ram ),
      .be_i    (         '1 ),
      .rdata_o (  tag_r_ram )
    );

    // comparator (XNOR)
    assign tag_compared = tag_q ~^ tag_r_ram;
    assign tag_equ[i]   = &tag_compared.tag; // valid if the stored tag equals the one looked up
    assign tag_val[i]   = tag_r_ram.val;     // indicates where valid values are in the line
    assign tag_dit[i]   = tag_r_ram.dit;     // indicates which tags are dirty

    // hit detection
    assign hit[i]       = way_ind_q[i]     & tag_val[i]       & tag_equ[i];
    // BIST also add the two bits of valid and dirty
    assign bist_res[i]  = tag_compared.val & tag_compared.dit & tag_equ[i];
    // assignment to wide output signal that goes to the tag output mux
    assign tag_out[i]   = tag_r_ram;
  end

  axi_llc_tag_pattern_gen #(
    .Cfg          (      Cfg ),
    .pattern_type (     tag_t)
  ) i_tag_pattern_gen (
    .clk_i            (       clk_i ),
    .rst_ni           (      rst_ni ),
    .valid_i          (   gen_valid ),
    .ready_o          (   gen_ready ),
    .index_o          (   index_gen ),
    .pattern_o        ( pattern_gen ),
    .req_o            (     req_gen ),
    .we_o             (      we_gen ),
    .bist_res_i       (    bist_res ),
    .bist_res_valid_i (  bist_valid ),
    .bist_res_o       (  bist_res_o ),
    .eoc_o            (     eoc_gen )
  );
  assign bist_valid_o = (req_mode_q == axi_llc_pkg::BIST) & eoc_gen;

  axi_llc_evict_box #(
    .Cfg         ( Cfg )
  ) i_evict_box (
    .clk_i       (            clk_i ),
    .rst_ni      (           rst_ni ),
    .req_i       (        evict_req ),
    .tag_valid_i (          tag_val ),
    .tag_dirty_i (          tag_dit ),
    .spm_lock_i  (       spm_lock_i ),
    .way_ind_o   (    evict_way_ind ),
    .evict_o     (       evict_flag ),
    .valid_o     (      evict_valid )
  );

  // Flip Flops
  `FFLARN(busy_q,     busy_d,     load_busy,            '0, clk_i, rst_ni)
  `FFLARN(req_mode_q, req_mode_d,      load, axi_llc_pkg::BIST, clk_i, rst_ni)
  `FFLARN(way_ind_q,  way_ind_d,       load,            '0, clk_i, rst_ni)
  `FFLARN(index_q,    index_d,         load,            '0, clk_i, rst_ni)
  `FFLARN(tag_q,      tag_d,           load,            '0, clk_i, rst_ni)

  // assertions
  // pragma translate_off
  `ifndef VERILATOR
  `ifndef VCS
  `ifndef SYNTHESIS
  onehot_hit:  assert property ( @(posedge clk_i) disable iff (!rst_ni)
      (req_mode_q != axi_llc_pkg::BIST) |-> $onehot0(hit)) else
      $fatal(1, "[hit_ind] More than two bit set in the one-hot signal, multiple hits!");
  onehot_ind:  assert property ( @(posedge clk_i) disable iff (!rst_ni)
      (req_mode_q != axi_llc_pkg::BIST) |-> $onehot0(way_ind_o)) else
      $fatal(1, "[way_ind_o] More than two bit set in the one-hot signal, multiple hits!");
  // trigger warning if output valid gets deasserted without ready
  check_valid: assert property ( @(posedge clk_i) disable iff (!rst_ni)
      (valid_o && !ready_i) |=> valid_o) else
      $warning("Valid was deasserted, even when no ready was set.");
  `endif
  `endif
  `endif
  // pragma translate_on
endmodule
