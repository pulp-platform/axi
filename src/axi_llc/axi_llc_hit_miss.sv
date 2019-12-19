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
// File:   read_unit.sv
// Author: Wolfgang Roenninger <wroennin@student.ethz.ch>
// Date:   11.06.2019
//
// Description: This module houses the hit miss detection logic and the tag storage.
//              When a descriptor gets loaded into the unit the respective tag operation happens
//              depending on the input descriptor.
//              The unit starts uninitialized and starts in the first cycle after each reset
//              the tag pattern generator to perform a march X BIST onto the macros.
//              After the BIST is finished, the macros are initialyzed to all zero.
//              During initialisation no descriptors can enter the unit.
//
//              This unit keeps track of which cache lines are currently in use by descriptors
//              downstream with the help od a bloom filter. If there is a new descriptor, which
//              will access a cache line currently in use, it wil be stalled untill the line is
//              unlocked. This is to prevent data corruption.
//
//              There is an array of counter which keep track which IDs of descriptors
//              are currently in the miss pipeline. All subsequent hits which normally would go
//              through the bypass will get sent also towards the miss pipeline. However their
//              eviction and refill fields will not be set. This is to clear the unit from
//              descriptors, so that new ones from other IDs can use the hit bypass.
//
//              // definition of the lock signals
//              typedef struct packed {
//                logic [Cfg.IndexLength-1:0]      index;        // index of lock (cacheline)
//                logic [Cfg.SetAssociativity-1:0] way_ind;      // way which is locked
//              } lock_t;
//
//              // definitions of the miss counting struct
//              typedef struct packed {
//                axi_slv_id_t                     id;           // Axi id of the count operation
//                logic                            rw;           // 0:read, 1:write
//                logic                            valid;        // valid, equals enable
//              } cnt_t;
//

// register macros
`include "common_cells/registers.svh"

module axi_llc_hit_miss #(
  parameter axi_llc_pkg::llc_cfg_t     Cfg    = -1,
  parameter axi_llc_pkg::llc_axi_cfg_t AxiCfg = -1,
  parameter type                       desc_t = logic,
  parameter type                       lock_t = logic,
  parameter type                       cnt_t  = logic
) (
  input  logic  clk_i,    // Clock
  input  logic  rst_ni,   // Asynchronous reset active low
  input  logic  test_i,   // Test Signal for Test mode
  // Descriptor Input
  input  desc_t desc_i,
  input  logic  valid_i,
  output logic  ready_o,
  // Descriptor Output
  output desc_t desc_o,
  output logic  miss_valid_o,
  input  logic  miss_ready_i,
  output logic  hit_valid_o,
  input  logic  hit_ready_i,
  // Configuration input
  input  logic [Cfg.SetAssociativity-1:0] spm_lock_i,
  input  logic [Cfg.SetAssociativity-1:0] flushed_i,
  // unlock inputs from the units
  input  lock_t w_unlock_i,
  input  logic  w_unlock_req_i,
  output logic  w_unlock_gnt_o,
  input  lock_t r_unlock_i,
  input  logic  r_unlock_req_i,
  output logic  r_unlock_gnt_o,
  // counter inputs to count down
  input  cnt_t  cnt_down_i,
  // bist aoutput
  output logic [Cfg.SetAssociativity-1:0] bist_res_o,
  output logic                            bist_valid_o
);
  localparam int unsigned IndexBase = Cfg.ByteOffsetLength + Cfg.BlockOffsetLength;
  localparam int unsigned TagBase   = Cfg.ByteOffsetLength + Cfg.BlockOffsetLength +
                                      Cfg.IndexLength;

  // Signals to/from the tag store
  logic                            req_valid;
  logic                            req_ready;
  axi_llc_pkg::tag_req_e           req_mode;
  // Request towards the tag store
  logic [Cfg.SetAssociativity-1:0] req_ind;
  logic                            req_we;
  logic [Cfg.IndexLength-1:0]      req_index;
  logic                            req_tag_dit;
  logic [Cfg.TagLength-1:0]        req_tag;
  // response from the tag storage
  logic [Cfg.SetAssociativity-1:0] out_ind;
  logic                            out_hit;
  logic                            out_evict;
  logic [Cfg.TagLength-1:0]        out_tag;
  logic                            out_dirty;
  logic                            out_valid;
  logic                            out_ready;
  // lock signal
  lock_t lock;
  logic  lock_req, locked;
  // up counting signal
  cnt_t  cnt_up;
  logic  cnt_stall;
  logic  to_miss;

  // Flipflops
  logic  busy_d,    busy_q, load_busy; // we have a valid descriptor in the unit
  logic  init_d,    init_q, load_init; // is the tag storage initialized?
  desc_t desc_d,    desc_q;            // descriptor residing in unit
  logic  load_desc;

  // control
  always_comb begin
    // default assignments
    init_d    = init_q;
    load_init = 1'b0;
    busy_d    = busy_q;
    load_busy = 1'b0;
    desc_d    = desc_q;
    // output
    desc_o    = desc_q; // some fields get combinatorically overwritten from the tag lookup
    load_desc = 1'b0;
    // unit handshaking
    ready_o      = 1'b0;
    miss_valid_o = 1'b0;
    hit_valid_o  = 1'b0;
    // inputs to the tag store
    req_valid    = 1'b0;
    req_mode     = axi_llc_pkg::BIST;
    req_ind      = '0;
    req_we       = '0;
    req_index    = '0;
    //req_tag_val  = 1'b0; not used
    req_tag_dit  = 1'b0;
    req_tag      = '0;
    out_ready    = 1'b0;

    // we are initialized, can operate on input descriptors
    if (init_q) begin

      // we have a valid descriptor in the unit and made the request to the tag store
      if (busy_q) begin
        if (desc_q.spm) begin
          /////////////////////////////////////////////////////////
          // SPM descriptor in unit
          /////////////////////////////////////////////////////////
          // check if the spm access would go onto a way configured as cache, if yes error
          if (|(desc_q.way_ind & (~spm_lock_i))) begin
            desc_o.x_resp = axi_pkg::RESP_SLVERR;
          end

          // only do something if we are not stalled or locked
          if (!(locked | cnt_stall)) begin
            // check if we have to go to hit or bypass
            if (!to_miss) begin
              hit_valid_o = 1'b1;
              // transfer
              if (hit_ready_i) begin
                busy_d    = 1'b0;
                load_busy = 1'b1;
              end
            end else begin
              miss_valid_o = 1'b1;
              // transfer
              if (miss_ready_i) begin
                busy_d    = 1'b0;
                load_busy = 1'b1;
              end
            end
          end

        end else begin
          ////////////////////////////////////////////////////////////////
          // NORMAL or FLUSH descriptor in unit, made req to tag_store
          ////////////////////////////////////////////////////////////////
          if (out_valid) begin
            if (desc_q.flush) begin
              // we have to send further, update desc_o
              desc_o.evict     = out_evict;
              desc_o.evict_tag = out_tag;
              // check that the line is not locked!
              if (!locked) begin
                miss_valid_o     = 1'b1;
                // transfer of flush descriptor to miss unit
                if (miss_ready_i) begin
                  out_ready = 1'b1;
                  busy_d    = 1'b0;
                  load_busy = 1'b1;
                end
              end
            end else begin
              /////////////////////////////////////////////////////////////
              // NORMAL lookup - differentiate between hit / miss
              /////////////////////////////////////////////////////////////
              // set out descriptor
              desc_o.way_ind   = out_ind;
              desc_o.evict     = out_evict;
              desc_o.evict_tag = out_tag;
              desc_o.refill    = out_hit ? 1'b0 : 1'b1;
              // determine if it has to go to the bypass or not if we are not stalled
              if (!(locked || cnt_stall)) begin
                hit_valid_o  = ~to_miss &  out_hit;
                miss_valid_o =  to_miss | ~out_hit;
                // check for a transfer, do not update hit_valid or miss_valid from this point on!
                if ((hit_valid_o && hit_ready_i) || (miss_valid_o && miss_ready_i)) begin
                  out_ready = 1'b1;
                  // do we have to make a store reqest to the tag store?
                  // - if there was a miss
                  // - if we have a write hit, but previously was not dirty
                  if (!out_hit || (out_hit && desc_q.rw && !out_dirty)) begin
                    req_valid   = 1'b1;
                    req_mode    = axi_llc_pkg::STORE;
                    req_ind     = out_ind;
                    req_index   = desc_q.a_x_addr[IndexBase+:Cfg.IndexLength];
                    req_tag_dit = desc_q.rw;
                    req_tag     = desc_q.a_x_addr[TagBase+:Cfg.TagLength];;
                    // should check on readyness of the tag_store, but should be ok?
                    // because we have made a lookup request in the previous cycle, and
                    // then the tag store should be ready anyways
                    busy_d      = 1'b0;
                    load_busy   = 1'b1;
                  // otherwise snoop, if there is another request to be made
                  end else begin
                    // we signal that we are ready only, if there is a valid input descriptor
                    if (valid_i) begin
                      // snoop at the descriptors spm, we do not have to make a lookup if it is spm
                      if (desc_i.spm) begin
                        // load directly, if it is spm
                        ready_o   = 1'b1;
                        desc_d    = desc_i;
                        load_desc = 1'b1;
                      end else begin
                        // make the request to the tag store
                        req_valid = 1'b1;
                        req_mode  = desc_i.flush ? axi_llc_pkg::FLUSH : axi_llc_pkg::LOOKUP;
                        req_ind   = desc_i.flush ? desc_i.way_ind     : '0;
                        req_index = desc_i.a_x_addr[IndexBase+:Cfg.IndexLength];
                        req_tag   = desc_i.flush ? '0 : desc_i.a_x_addr[TagBase+:Cfg.TagLength];
                        // transfer
                        if (req_ready) begin
                          ready_o   = 1'b1;
                          desc_d    = desc_i;
                          load_desc = 1'b1;
                        end else begin
                          // to idle, because unit not ready
                          busy_d    = 1'b0;
                          load_busy = 1'b1;
                        end
                      end
                    end else begin
                      // no new descriptor to idle
                      busy_d    = 1'b0;
                      load_busy = 1'b1;
                    end
                  end
                end
              end
            end
          end
        end

      //////////////////////////////////////////////////////////////////////////////
      // we do not have a descriptor in our unit (not busy)
      //////////////////////////////////////////////////////////////////////////////
      end else begin
        // we signal that we are ready only, if there is a valid input descriptor
        if (valid_i) begin
          // snoop at the descriptors spm, we do not have to make a lookup if it is spm
          if (desc_i.spm) begin
            // load directly, if it is spm
            ready_o   = 1'b1;
            busy_d    = 1'b1;
            load_busy = 1'b1;
            desc_d    = desc_i;
            load_desc = 1'b1;
          end else begin
            // make the request to the tag store
            req_valid = 1'b1;
            req_mode  = desc_i.flush ? axi_llc_pkg::FLUSH : axi_llc_pkg::LOOKUP;
            req_ind   = desc_i.flush ? desc_i.way_ind     : '0;
            req_index = desc_i.a_x_addr[IndexBase+:Cfg.IndexLength];
            req_tag   = desc_i.flush ? '0 : desc_i.a_x_addr[TagBase+:Cfg.TagLength];
            // transfer
            if (req_ready) begin
              ready_o   = 1'b1;
              busy_d    = 1'b1;
              load_busy = 1'b1;
              desc_d    = desc_i;
              load_desc = 1'b1;
            end
          end
        end // we had a new descriptor for loading
      end

    ///////////////////////////////////////////////////////////////////////////////
    // we come out of a reset, initialize the tag sram makros
    ///////////////////////////////////////////////////////////////////////////////
    end else begin
      // first cycle after reset start initialization of the sram makros
      req_valid = 1'b1;
      req_mode  = axi_llc_pkg::BIST;
      req_ind   = '1;
      if (req_ready) begin
        init_d    = 1'b1;
        load_init = 1'b1;
      end
    end
  end

  axi_llc_tag_store #(
    .Cfg (Cfg)
  ) i_tag_store (
    .clk_i        (        clk_i ),
    .rst_ni       (       rst_ni ),
    .test_i       (       test_i ),
    .spm_lock_i   (   spm_lock_i ),
    .flushed_i    (    flushed_i ),
    .valid_i      (    req_valid ),
    .ready_o      (    req_ready ),
    .req_mode_i   (     req_mode ),
    .way_ind_i    (      req_ind ),
    .index_i      (    req_index ),
    .tag_dit_i    (  req_tag_dit ),
    .tag_i        (      req_tag ),
    .way_ind_o    (      out_ind ),
    .hit_o        (      out_hit ),
    .evict_o      (    out_evict ),
    .tag_o        (      out_tag ),
    .dit_o        (    out_dirty ),
    .valid_o      (    out_valid ),
    .ready_i      (    out_ready ),
    .bist_res_o   (   bist_res_o ),
    .bist_valid_o ( bist_valid_o )
  );

  // inputs to the miss counter unit
  assign cnt_up.id    = desc_o.a_x_id;
  assign cnt_up.rw    = desc_o.rw;
  // count up if a transfer happens on the miss pipeline
  assign cnt_up.valid = ~desc_o.flush & miss_valid_o & miss_ready_i;

  axi_llc_miss_counters #(
    .Cfg     ( Cfg    ),
    .AxiCfg  ( AxiCfg ),
    .cnt_t   ( cnt_t  )
  ) i_miss_counters (
    .clk_i      (      clk_i ),
    .rst_ni     (     rst_ni ),
    .cnt_up_i   (     cnt_up ),
    .cnt_down_i ( cnt_down_i ),
    .to_miss_o  (    to_miss ),
    .stall_o    (  cnt_stall )
  );

  // inputs to the lock box
  assign lock = '{
    index:   desc_o.a_x_addr[(Cfg.ByteOffsetLength + Cfg.BlockOffsetLength)+:Cfg.IndexLength],
    way_ind: desc_o.way_ind
  };
  // Lock it if a transfer happens on ether channel and no flush!
  assign lock_req = ~desc_o.flush & ((miss_valid_o & miss_ready_i) | (hit_valid_o & hit_ready_i));

  axi_llc_lock_box_bloom #(
    .Cfg       ( Cfg    ),
    .lock_t    ( lock_t )
  ) i_lock_box_bloom (
    .clk_i          ( clk_i      ),  // Clock
    .rst_ni         ( rst_ni     ),  // Asynchronous reset active low
    .test_i         ( test_i     ),
    .lock_i         ( lock       ),
    .lock_req_i     ( lock_req   ),
    .locked_o       ( locked     ),
    .w_unlock_i,
    .w_unlock_req_i,
    .w_unlock_gnt_o,
    .r_unlock_i,
    .r_unlock_req_i,
    .r_unlock_gnt_o
  );

  // registers
  `FFLARN(busy_q, busy_d, load_busy, '0, clk_i, rst_ni)
  `FFLARN(init_q, init_d, load_init, '0, clk_i, rst_ni)
  `FFLARN(desc_q, desc_d, load_desc, '0, clk_i, rst_ni)

  // pragma translate_off
  `ifndef VERILATOR
  `ifndef VCS
  `ifndef SYNTHESIS
  valid_o : assert property(
    @(posedge clk_i) disable iff (!rst_ni) !(miss_valid_o & hit_valid_o))
    else $fatal (1, "Duplicated descriptors, both valid outs are active.");

  detect_way_onehot : assert property(
    @(posedge clk_i) disable iff (!rst_ni) $onehot0(desc_o.way_ind))
    else $fatal(1, "[hit_miss.desc_o.way_ind] More than two bit set in the one-hot signal!");
  `endif
  `endif
  `endif
endmodule
