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
// File:   axi_llc_hit_miss.sv
// Author: Wolfgang Roenninger <wroennin@iis.ee.ethz.ch>
// Date:   11.06.2019

/// This module houses the hit miss detection logic and the tag storage.
/// When a descriptor gets loaded into the unit the respective tag operation happens
/// depending on the input descriptor.
/// The unit starts uninitialized and starts in the first cycle after each reset
/// the tag pattern generator to perform a march X BIST onto the macros.
/// After the BIST is finished, the macros are initialyzed to all zero.
/// During initialisation no descriptors can enter the unit.
///
/// This unit keeps track of which cache lines are currently in use by descriptors
/// downstream with the help od a bloom filter. If there is a new descriptor, which
/// will access a cache line currently in use, it wil be stalled untill the line is
/// unlocked. This is to prevent data corruption.
///
/// There is an array of counter which keep track which IDs of descriptors
/// are currently in the miss pipeline. All subsequent hits which normally would go
/// through the bypass will get sent also towards the miss pipeline. However their
/// eviction and refill fields will not be set. This is to clear the unit from
/// descriptors, so that new ones from other IDs can use the hit bypass.
module axi_llc_hit_miss #(
  /// Stattic LLC configuration struct.
  parameter axi_llc_pkg::llc_cfg_t     Cfg       = axi_llc_pkg::llc_cfg_t'{default: '0},
  /// AXI parameter configuration
  parameter axi_llc_pkg::llc_axi_cfg_t AxiCfg    = axi_llc_pkg::llc_axi_cfg_t'{default: '0},
  /// LLC descriptor type
  parameter type                       desc_t    = logic,
  /// Lock struct definition. The lock signal indicate that a cache line is unlocked.
  ///
  ///  typedef struct packed {
  ///    logic [Cfg.IndexLength-1:0]      index;        // index of lock (cacheline)
  ///    logic [Cfg.SetAssociativity-1:0] way_ind;      // way which is locked
  ///  } lock_t;
  parameter type                       lock_t    = logic,
  /// Expected type definition definition of the miss counting struct
  ///
  /// typedef struct packed {
  ///   axi_slv_id_t id;    // Axi id of the count operation
  ///   logic        rw;    // 0:read, 1:write
  ///   logic        valid; // valid, equals enable
  /// } cnt_t;
  parameter type                       cnt_t     = logic,
  /// Way indicator, is a onehot signal with width: `Cfg.SetAssociativity`.
  parameter type                       way_ind_t = logic
) (
  /// Clock, positive edge triggered.
  input  logic     clk_i,
  /// Asynchronous reset, active low.
  input  logic     rst_ni,
  /// Testmode enable, active high.
  input  logic     test_i,
  /// Input descriptor payload.
  input  desc_t    desc_i,
  /// Input descriptor is valid.
  input  logic     valid_i,
  /// Module is ready to accept a new input descriptor.
  output logic     ready_o,
  /// Descriptor Output TODO
  output desc_t    desc_o,
  output logic     miss_valid_o,
  input  logic     miss_ready_i,
  output logic     hit_valid_o,
  input  logic     hit_ready_i,
  // Configuration input
  input  way_ind_t spm_lock_i,
  input  way_ind_t flushed_i,
  // unlock inputs from the units
  input  lock_t    w_unlock_i,
  input  logic     w_unlock_req_i,
  output logic     w_unlock_gnt_o,
  input  lock_t    r_unlock_i,
  input  logic     r_unlock_req_i,
  output logic     r_unlock_gnt_o,
  // counter inputs to count down
  input  cnt_t     cnt_down_i,
  // bist aoutput
  output way_ind_t bist_res_o,
  output logic     bist_valid_o
);
  `include "common_cells/registers.svh"
  localparam int unsigned IndexBase = Cfg.ByteOffsetLength + Cfg.BlockOffsetLength;
  localparam int unsigned TagBase   = Cfg.ByteOffsetLength + Cfg.BlockOffsetLength +
                                      Cfg.IndexLength;
  // Type definitions for the requests and responses to/from the tag storage
      // typedef logic [Cfg.SetAssociativity-1:0] way_ind_t;
  typedef logic [Cfg.IndexLength-1:0]      index_t;
  typedef logic [Cfg.TagLength-1:0]        tag_t;

  /// Request struct to the tag storage.
  typedef struct packed {
    /// The request mode. What operation the tag storage should perform with the request.
    axi_llc_pkg::tag_mode_e mode;
    /// The indicatior encodes with a hot signal, to which ways the request should be made.
    way_ind_t               indicator;
    /// The index points to the cache line, for which the request is made.
    index_t                 index;
    /// The tag for which the request to the tag storage is made.
    tag_t                   tag;
    /// The tag is dirty, comes from a write.
    logic                   dirty;
  } store_req_t;

  /// The response will only come out of the tag storage, id a lookup request was made.
  typedef struct packed {
    /// The descriptor has to operate on this way
    way_ind_t indicator;
    /// The request has hit on a cache line.
    logic     hit;
    /// The tag currently stored is dirty.
    /// The tag storage wants to evict the current line stored at this position.
    logic     evict;
    /// The tag which is evicted.
    tag_t     evict_tag;
  } store_res_t;

  // Signals to/from the tag store
  store_req_t store_req;
  logic       store_req_valid;
  logic       store_req_ready;

  store_res_t store_res;
  logic       store_res_valid;
  logic       store_res_ready;
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
    store_req       = store_req_t'{mode: axi_llc_pkg::Bist, default: '0};
    store_req_valid = 1'b0;

    store_res_ready = 1'b0;

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
          // wait for the response
          ////////////////////////////////////////////////////////////////
          if (store_res_valid) begin
            if (desc_q.flush) begin
              // We have to send further, update desc_o
              desc_o.evict     = store_res.evict;
              desc_o.evict_tag = store_res.evict_tag;
              // check that the line is not locked!
              if (!locked) begin
                miss_valid_o     = 1'b1;
                // transfer of flush descriptor to miss unit
                if (miss_ready_i) begin
                  store_res_ready = 1'b1;
                  busy_d          = 1'b0;
                  load_busy       = 1'b1;
                end
              end
            end else begin
              /////////////////////////////////////////////////////////////
              // NORMAL lookup - differentiate between hit / miss
              /////////////////////////////////////////////////////////////
              // set out descriptor
              desc_o.way_ind   = store_res.indicator;
              desc_o.evict     = store_res.evict;
              desc_o.evict_tag = store_res.evict_tag;
              desc_o.refill    = store_res.hit ? 1'b0 : 1'b1;
              // determine if it has to go to the bypass or not if we are not stalled
              if (!(locked || cnt_stall)) begin
                hit_valid_o  = ~to_miss &  store_res.hit;
                miss_valid_o =  to_miss | ~store_res.hit;
                // check for a transfer, do not update hit_valid or miss_valid from this point on!
                if ((hit_valid_o && hit_ready_i) || (miss_valid_o && miss_ready_i)) begin
                  store_res_ready = 1'b1;
                  // New tag is written with the lookup or flush if it was necessary and the storage
                  // will go to ready, if it can take a new request.
                  // Does the module have a new descriptor at its input and we can take it?
                  if (valid_i) begin
                    // snoop at the descriptors spm, we do not have to make a lookup if it is spm
                    if (desc_i.spm) begin
                      // load directly, if it is spm
                      ready_o   = 1'b1;
                      desc_d    = desc_i;
                      load_desc = 1'b1;
                    end else begin
                      // make the request to the tag store,
                      store_req = store_req_t'{
                        mode:      desc_i.flush ? axi_llc_pkg::Flush : axi_llc_pkg::Lookup,
                        indicator: desc_i.flush ? desc_i.way_ind     : ~flushed_i,
                        index:     desc_i.a_x_addr[IndexBase+:Cfg.IndexLength],
                        tag:       desc_i.flush ? tag_t'(0)          : desc_i.a_x_addr[TagBase+:Cfg.TagLength],
                        dirty:     desc_i.rw,
                        default:   '0
                      };
                      store_req_valid = 1'b1;
                      // transfer
                      if (store_req_ready) begin
                        ready_o   = 1'b1;
                        desc_d    = desc_i;
                        load_desc = 1'b1;
                      end else begin
                        // go to idle and do nothing
                        busy_d    = 1'b0;
                        load_busy = 1'b1;
                      end
                    end
                  end else begin
                    // Go to IDLE otherwise
                    busy_d    = 1'b0;
                    load_busy = 1'b1;
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
            // make the request to the tag store,
            store_req = store_req_t'{
              mode:      desc_i.flush ? axi_llc_pkg::Flush : axi_llc_pkg::Lookup,
              indicator: desc_i.flush ? desc_i.way_ind     : ~flushed_i,
              index:     desc_i.a_x_addr[IndexBase+:Cfg.IndexLength],
              tag:       desc_i.flush ? tag_t'(0)          : desc_i.a_x_addr[TagBase+:Cfg.TagLength],
              dirty:     desc_i.rw,
              default:   '0
            };
            store_req_valid = 1'b1;
            // transfer
            if (store_req_ready) begin
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
      store_req = store_req_t'{
        mode:      axi_llc_pkg::Bist,
        indicator: {Cfg.SetAssociativity{1'b1}},
        default:   '0
      };
      store_req_valid = 1'b1;
      if (store_req_ready) begin
        init_d    = 1'b1;
        load_init = 1'b1;
      end
    end
  end

  axi_llc_tag_store #(
    .Cfg         ( Cfg         ),
    .way_ind_t   ( way_ind_t   ),
    .store_req_t ( store_req_t ),
    .store_res_t ( store_res_t )
  ) i_tag_store (
    .clk_i,
    .rst_ni,
    .test_i,
    .spm_lock_i   ( spm_lock_i      ),
    .flushed_i    ( flushed_i       ),
    .req_i        ( store_req       ),
    .valid_i      ( store_req_valid ),
    .ready_o      ( store_req_ready ),
    .res_o        ( store_res       ),
    .valid_o      ( store_res_valid ),
    .ready_i      ( store_res_ready ),
    .bist_res_o   ( bist_res_o      ),
    .bist_valid_o ( bist_valid_o    )
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
    valid_o : assert property(
      @(posedge clk_i) disable iff (!rst_ni) !(miss_valid_o & hit_valid_o))
      else $fatal (1, "Duplicated descriptors, both valid outs are active.");

    detect_way_onehot : assert property(
      @(posedge clk_i) disable iff (!rst_ni) $onehot0(desc_o.way_ind))
      else $fatal(1, "[hit_miss.desc_o.way_ind] More than two bit set in the one-hot signal!");
  `endif
endmodule
