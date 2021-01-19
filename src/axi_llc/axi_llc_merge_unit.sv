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
// File:   llc_merge_unit.sv
// Author: Wolfgang Roenninger <wroennin@iis.ee.ethz.ch>
// Date:   12.06.2019

/// This module merges the descriptor streams form the bypass and the eviction/refill
/// pipeline. It distributes the descriptors to the read and write unit.
/// It also notifies the counter unit in the hit_miss that a descriptor left the
/// eviction/refill pipeline.
module axi_llc_merge_unit #(
  /// Static LLC configuration struct.
  parameter axi_llc_pkg::llc_cfg_t Cfg = axi_llc_pkg::llc_cfg_t'{default: '0},
  /// LLC descriptor type definition.
  parameter type desc_t = logic,
  /// Counter struct, is used in the miss counters for  ensuring the right ordering of
  /// the descriptors.
  ///
  /// The struct `cnt_t` has to be defined as follows (done in `axi_llc_top`):
  /// typedef struct packed {
  ///    axi_slv_id_t id;     // AXI ID of the count operation
  ///    logic        rw;     // 0: read, 1: write
  ///    logic        valid;  // valid, equals enable
  ///  } cnt_t;
  parameter type cnt_t = logic
) (
  /// Clock, positive edge triggered.
  input logic clk_i,
  /// Asynchronous reset, active low.
  input logic rst_ni,
  /// Input descriptor payload from the hit bypass.
  input desc_t bypass_desc_i,
  /// Hit bypass descriptor is valid.
  input logic bypass_valid_i,
  /// We are ready to accept a descriptor from the hit bypass.
  output logic bypass_ready_o,
  /// Input descriptor payload from the eviction / refill pipeline.
  input desc_t refill_desc_i,
  /// Miss pipeline descriptor is valid.
  input logic refill_valid_i,
  /// We are ready to accept a descriptor from the miss pipeline.
  output logic refill_ready_o,
  /// Output descriptor payload to the read unit.
  output desc_t read_desc_o,
  /// Read descriptor is valid.
  output logic read_valid_o,
  /// Read unit is ready to accept a descriptor
  input logic read_ready_i,
  /// Write descriptor payload to the write unit.
  output desc_t write_desc_o,
  /// Write descriptor is valid.
  output logic write_valid_o,
  /// Write unit is ready to accept a descriptor.
  input logic write_ready_i,
  /// Output to the miss counters in the hit miss unit.
  /// When valid a descriptor leaves the miss pipeline.
  output cnt_t cnt_down_o
);

  // count down output towards the miss counters
  // enable cnt_down_o if there is a transfer from the pipeline
  assign cnt_down_o.id    = refill_desc_i.a_x_id;
  assign cnt_down_o.rw    = refill_desc_i.rw;
  assign cnt_down_o.valid = refill_valid_i & refill_ready_o;

  // The rw field is write = 1, read = 0.
  stream_xbar #(
    .NumInp     ( 32'd2  ),
    .NumOut     ( 32'd2  ),
    .payload_t  ( desc_t ),
    .OutSpillReg( 1'b0   ),
    .ExtPrio    ( 1'b0   ),
    .AxiVldRdy  ( 1'b1   ),
    .LockIn     ( 1'b1   )
  ) i_stream_xbar (
    .clk_i,
    .rst_ni,
    .flush_i ( '0                                 ),
    .rr_i    ( '0                                 ),
    .data_i  ({bypass_desc_i,    refill_desc_i   }),
    .sel_i   ({bypass_desc_i.rw, refill_desc_i.rw}),
    .valid_i ({bypass_valid_i,   refill_valid_i  }),
    .ready_o ({bypass_ready_o,   refill_ready_o  }),
    .data_o  ({write_desc_o,     read_desc_o     }),
    .idx_o   ( /*not used*/                       ),
    .valid_o ({write_valid_o,    read_valid_o    }),
    .ready_i ({write_ready_i,    read_ready_i    })
  );
endmodule
