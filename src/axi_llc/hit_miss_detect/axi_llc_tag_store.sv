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

/// This is the Tag storage for the LLC
/// There are four types of requests which can be made onto this unit.
/// `axi_llc_pkg::Bist`:
///   The pattern gets written or read to all macros, BIST resulte gets activated
/// `axi_llc_pkg::Flush`:
///   Perform a way trageted eviction, the tag is written in with all zero.
/// `axi_llc_pkg::Lookup`:
///   Perform a tag lookup in all non SPM ways, hit/eviction gets set if needed.
///   Writes the tag into the macro if needed.
`include "common_cells/registers.svh"
module axi_llc_tag_store #(
  /// Static LLC configuration struct
  parameter axi_llc_pkg::llc_cfg_t Cfg = axi_llc_pkg::llc_cfg_t'{default: '0},
  /// Way indicator type
  /// EG: typedef logic [Cfg.SetAssociativity-1:0] way_ind_t;
  parameter type way_ind_t = logic,
  /// Type of the request payload made to the tag storage
  parameter type store_req_t = logic,
  /// Type of the response payload expected from the tag storage
  parameter type store_res_t = logic
) (
  /// Clock, positive edge triggered
  input  logic       clk_i,
  /// Asynchronous reset, active low
  input  logic       rst_ni,
  /// Testmode enable
  input  logic       test_i,
  /// SPM lock signal input.
  ///
  /// For each way there is one signal. When high the way is configured as SPM. They are disabled
  /// for store requests.
  input  way_ind_t   spm_lock_i,
  /// Flushed indicator from `axi_llc_config`.
  ///
  /// This indicates that a way is flushed. No LOOKUP operations are performed on flushed ways.
  input  way_ind_t   flushed_i,
  /// Tag storage request payload.
  input  store_req_t req_i,
  /// Request to the tag storage is valid.
  input  logic       valid_i,
  /// Tag storage is ready for an request.
  output logic       ready_o,
  /// Tag storage response payload
  output store_res_t res_o,
  /// Tag stoarage response is valid.
  output logic       valid_o,
  /// Hit miss unit is ready to accept response.
  input  logic       ready_i,
  /// BIST result output. If one of these bits is high, when `bist_valid_o` is `1`. The
  /// corresponding tag storage SRAM macro failed the test.
  output way_ind_t   bist_res_o,
  /// BIST output is valid.
  output logic       bist_valid_o
);

  // typedef, because we use in this module many signals with the width of SetAssiciativity
  typedef logic [Cfg.IndexLength-1:0] index_t; // index type (equals the address for sram)
  typedef logic [Cfg.TagLength-1:0]   tag_t;

  // typedef to have consistent tag data (that what gets written into the sram)
  localparam int unsigned TagDataLen = Cfg.TagLength + 32'd2;
  /// Packed struct for the data stored in the memory macros.
  typedef struct packed {
    /// The tag stored is valid.
    logic val;
    /// The tag stored is dirty.
    logic dit;
    /// The stored tag itself.
    tag_t tag;
  } tag_data_t;

  // Binary indicator of the output way selected.
  localparam int unsigned BinIndicatorWidth = cf_math_pkg::idx_width(Cfg.SetAssociativity);
  typedef logic [BinIndicatorWidth-1:0] bin_ind_t;

  // The module can be busy or not.
  logic       busy_q,      busy_d,       switch_busy;

  // Save the request in state
  store_req_t req_q;
  logic       load_req;

  // Macro signals
  // Request for the macros
  way_ind_t   ram_req;
  // Write enable for the macros, active high. (Also functions as byte enable as there is one byte).
  way_ind_t   ram_we;
  // Index is the address.
  index_t     ram_index;
  // Write data for the macros.
  tag_data_t  ram_wdata;
  // Read data is valid
  way_ind_t   ram_rvalid,  ram_rvalid_q, ram_rvalid_d;
  logic       lock_rvalid;
  // Hit indication signals
  way_ind_t   hit, tag_val, tag_dit,     tag_equ;
  tag_data_t  [Cfg.SetAssociativity-1:0] stored_tag;
  // Binary representation of the selected output indicator
  bin_ind_t   bin_ind;
  // The pattern generation unit signals
  logic       gen_valid,   gen_ready;
  index_t     gen_index;
  tag_data_t  gen_pattern, bist_pattern;
  logic       gen_req,     gen_we;
  way_ind_t   bist_res;
  logic       bist_valid,  gen_eoc;
  // Evict box signals
  logic       evict_req,   evict_valid;

  // macro control
  always_comb begin : proc_macro_ctrl
    // default assignments
    // FFs
    switch_busy  = 1'b0;
    ready_o      = 1'b0;
    load_req     = 1'b0;
    valid_o      = 1'b0;
    ram_req      = way_ind_t'(0);
    ram_we       = way_ind_t'(0);
    ram_index    = way_ind_t'(0);
    ram_wdata    = tag_data_t'{default: '0};
    // Evict box
    evict_req    = 1'b0;
    // generation request
    gen_valid    = 1'b0;

    if (busy_q) begin
      // We are busy so there are active operations going on, we are not ready.
      unique case (req_q.mode)
          axi_llc_pkg::Bist: begin
            // During BIST connect the request to the tag pattern generator.
            ram_req    = {Cfg.SetAssociativity{gen_req}};
            ram_we     = {Cfg.SetAssociativity{gen_we}};
            ram_index  = gen_index;
            ram_wdata  = gen_pattern;
            bist_valid = |ram_rvalid;
            // If BIST finished, go to idle.
            if (gen_eoc) begin
              switch_busy = 1'b1;
            end
          end
          axi_llc_pkg::Lookup: begin
            // Wait for valid macro output
            if ((|ram_rvalid) | (|ram_rvalid_q)) begin
              // We are valid on hit.
              if (|hit) begin
                valid_o = 1'b1;
              end else begin
                evict_req = 1'b1;
                valid_o   = evict_valid;
              end
            end

            // Do we have to write back something?
            if (valid_o && ready_i) begin
              if (res_o.hit) begin
                // This is a hit
                if (req_q.dirty && !tag_dit[bin_ind]) begin
                  // Do we have to store a dirty as the hit was not dirty until now?
                  ram_req   = res_o.indicator;
                  ram_we    = res_o.indicator;
                  ram_index = req_q.index;
                  ram_wdata = tag_data_t'{
                                val: 1'b1,
                                dit: 1'b1,
                                tag: req_q.tag
                              };
                  switch_busy = 1'b1;
                end else begin
                  // Noting to write back, do we have a new LOOKUP request?
                  if (valid_i && (req_i.mode == axi_llc_pkg::Lookup)) begin
                    ready_o = 1'b1;
                    // Do the lookup on the requested macros
                    ram_req     = req_i.indicator;
                    ram_index   = req_i.index;
                    load_req    = 1'b1;
                  end else begin
                    // Go back to IDLE if no Lookup
                    switch_busy = 1'b1;
                  end
                end
              end else begin
                // This is a miss!
                // Write back the new tag, it was a miss.
                ram_req   = res_o.indicator;
                ram_we    = res_o.indicator;
                ram_index = req_q.index;
                ram_wdata = tag_data_t'{
                              val: 1'b1,
                              dit: req_q.dirty,
                              tag: req_q.tag
                            };
                // Go back to idle.
                switch_busy = 1'b1;
              end
            end
          end
          axi_llc_pkg::Flush: begin
            if ((|ram_rvalid) | (|ram_rvalid_q)) begin
              // We are valid on hit.
              if (|hit) begin
                valid_o = 1'b1;
              end else begin
                evict_req = 1'b1;
                valid_o   = evict_valid;
              end
            end

            // Write back all zeros to the storage if the output is acknowledged.
            if (valid_o && ready_i) begin
              ram_req     = req_q.indicator;
              ram_we      = req_q.indicator;
              ram_index   = req_q.index;
              ram_wdata   = tag_data_t'{default: '0};
              switch_busy = 1'b1;
            end
          end
        default : /* default */;
      endcase
    end else begin
      // we are not busy, so we are ready to get a new request.
      ready_o = 1'b1;

      if (valid_i) begin
        // There is a request to the tag store.
        switch_busy = 1'b1;
        load_req    = 1'b1;

        // Make the requests to the tag macros.
        unique case (req_i.mode)
          axi_llc_pkg::Bist: begin
            gen_valid   = 1'b1;
            ready_o     = gen_ready;
            // Only switch the state, if the request is valid
            switch_busy = gen_ready;
          end
          axi_llc_pkg::Lookup, axi_llc_pkg::Flush: begin
            // Do the lookup on the requested macros
            ram_req     = req_i.indicator;
            ram_index   = req_i.index;
            load_req    = 1'b1;
            switch_busy = 1'b1;
          end
          default : /* do nothing */;
        endcase
      end
    end
  end

  `FFLARN(req_q, req_i, load_req, store_req_t'{default: '0}, clk_i, rst_ni)
  `FFLARN(busy_q, busy_d, switch_busy, 1'b0, clk_i, rst_ni)
  assign busy_d = ~busy_q;
  `FFLARN(ram_rvalid_q, ram_rvalid_d, lock_rvalid, way_ind_t'(0), clk_i, rst_ni)
  assign ram_rvalid_d = (valid_o & ready_i) ? way_ind_t'(0) : ram_rvalid;
  assign lock_rvalid  = (valid_o & ready_i) | (|ram_rvalid);

  // generate for each Way one tag storage macro
  for (genvar i = 0; unsigned'(i) < Cfg.SetAssociativity; i++) begin : gen_tag_macros
    tag_data_t ram_rdata;    // read data from the sram
    tag_data_t ram_compared; // comparison result of tags

    tc_sram #(
      .NumWords    ( Cfg.NumLines                 ),
      .DataWidth   ( TagDataLen                   ),
      .ByteWidth   ( TagDataLen                   ),
      .NumPorts    ( 32'd1                        ),
      .Latency     ( axi_llc_pkg::TagMacroLatency ),
      .SimInit     ( "none"                       ),
      .PrintSimCfg ( 1'b1                         )
    ) i_tag_store (
      .clk_i,
      .rst_ni,
      .req_i   ( ram_req[i] ),
      .we_i    ( ram_we[i]  ),
      .addr_i  ( ram_index  ),
      .wdata_i ( ram_wdata  ),
      .be_i    ( ram_we[i]  ),
      .rdata_o ( ram_rdata  )
    );

    // shift register for a validtoken for read data, this pulses once for each read request
    shift_reg #(
      .dtype ( logic                        ),
      .Depth ( axi_llc_pkg::TagMacroLatency )
    ) i_shift_reg_rvalid (
      .clk_i,
      .rst_ni,
      .d_i    ( ram_req[i] & ~ram_we[i] ),
      .d_o    ( ram_rvalid[i]           )
    );

    // comparator (XNOR)
    assign ram_compared = tag_data_t'{
          val: bist_pattern.val,
          dit: bist_pattern.dit,
          tag: (req_q.mode == axi_llc_pkg::Bist) ? bist_pattern.tag : req_q.tag
        } ~^ ram_rdata;
    assign tag_equ[i] = &ram_compared.tag; // valid if the stored tag equals the one looked up
    assign tag_val[i] = ram_rdata.val;     // indicates where valid values are in the line
    assign tag_dit[i] = ram_rdata.dit;     // indicates which tags are dirty

    // hit detection
    assign hit[i]        = req_q.indicator[i] & tag_val[i] & tag_equ[i];
    // BIST also add the two bits of valid and dirty
    assign bist_res[i]   = ram_compared.val & ram_compared.dit & tag_equ[i];
    // assignment to wide output signal that goes to the tag output mux
    assign stored_tag[i] = ram_rdata;
  end

  axi_llc_tag_pattern_gen #(
    .Cfg       ( Cfg        ),
    .pattern_t ( tag_data_t ),
    .way_ind_t ( way_ind_t  ),
    .index_t   ( index_t    )
  ) i_tag_pattern_gen (
    .clk_i,
    .rst_ni,
    .valid_i          ( gen_valid   ),
    .ready_o          ( gen_ready   ),
    .index_o          ( gen_index   ),
    .pattern_o        ( gen_pattern ),
    .req_o            ( gen_req     ),
    .we_o             ( gen_we      ),
    .bist_res_i       ( bist_res    ),
    .bist_res_valid_i ( bist_valid  ),
    .bist_res_o       ( bist_res_o  ),
    .eoc_o            ( gen_eoc     )
  );
  assign bist_valid_o = (req_q.mode == axi_llc_pkg::BIST) & gen_eoc;

  // This shift register holds the pattern for comparison of the bist.
  shift_reg #(
    .dtype ( tag_data_t                   ),
    .Depth ( axi_llc_pkg::TagMacroLatency )
  ) i_shift_reg_bist (
    .clk_i,
    .rst_ni,
    .d_i    ( gen_pattern  ),
    .d_o    ( bist_pattern )
  );

  way_ind_t evict_way_ind;

  axi_llc_evict_box #(
    .Cfg ( Cfg )
  ) i_evict_box (
    .clk_i,
    .rst_ni,
    .req_i       ( evict_req     ),
    .tag_valid_i ( tag_val       ),
    .tag_dirty_i ( tag_dit       ),
    .spm_lock_i  ( spm_lock_i    ),
    .way_ind_o   ( evict_way_ind ),
    .evict_o     ( evict_flag    ),
    .valid_o     ( evict_valid   )
  );

  onehot_to_bin #(
    .ONEHOT_WIDTH ( Cfg.SetAssociativity )
  ) i_onehot_to_bin (
    .onehot ( res_o.indicator ),
    .bin    ( bin_ind         )
  );

  // Silence output when not in a mode where it is required.
  always_comb begin
    // Default assignment
    res_o = store_res_t'{default: '0};
    if (busy_q) begin
      unique case (req_q.mode)
        axi_llc_pkg::Lookup: begin
          res_o = store_res_t'{
            indicator: (|hit) ? hit       : evict_way_ind,
            hit:       (|hit) ? 1'b1      : 1'b0,
            evict:     (|hit) ? 1'b0      : evict_flag,
            evict_tag: (|hit) ? tag_t'(0) : stored_tag[bin_ind].tag,
            default:   '0
          };
        end
        axi_llc_pkg::Flush: begin
          res_o = store_res_t'{
            indicator: req_q.indicator,
            hit:       1'b0,
            evict:     stored_tag[bin_ind].val & stored_tag[bin_ind].dit,
            evict_tag: stored_tag[bin_ind].tag,
            default:   '0
          };
        end
        default : /* not used */;
      endcase
    end
  end

  // Assertions
  // pragma translate_off
  `ifndef VERILATOR
  onehot_hit:  assert property ( @(posedge clk_i) disable iff (!rst_ni)
      (req_q.mode inside {axi_llc_pkg::Lookup, axi_llc_pkg::Flush}) |-> $onehot0(hit)) else
      $fatal(1, "[hit_ind] More than two bit set in the one-hot signal, multiple hits!");
  onehot_ind:  assert property ( @(posedge clk_i) disable iff (!rst_ni)
      (req_q.mode inside {axi_llc_pkg::Lookup, axi_llc_pkg::Flush}) |-> $onehot0(res_o.indicator)) else
      $fatal(1, "[way_ind_o] More than two bit set in the one-hot signal, multiple hits!");
  // trigger warning if output valid gets deasserted without ready
  check_valid: assert property ( @(posedge clk_i) disable iff (!rst_ni)
      (valid_o && !ready_i) |=> valid_o) else
      $warning("Valid was deasserted, even when no ready was set.");
  `endif
  // pragma translate_on
endmodule
