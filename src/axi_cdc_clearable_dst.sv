// Copyright (c) 2019-2020 ETH Zurich, University of Bologna
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
// Authors:
// - Manuel Eggimann <meggimann@iis.ee.ethz.ch>
// - Andreas Kurth <akurth@iis.ee.ethz.ch>
// - Fabian Schuiki <fschuiki@iis.ee.ethz.ch>
// - Florian Zaruba <zarubaf@iis.ee.ethz.ch>
// - Luca Valente <luca.valente2@unibo.it>

`include "axi/assign.svh"
`include "axi/typedef.svh"

/// Destination-clock-domain half of the AXI CDC crossing.
///
/// For each of the five AXI channels, this module instantiates the source or destination half of
/// a CDC FIFO.  IMPORTANT: For each AXI channel, you MUST properly constrain three paths through
/// the FIFO; see the header of `cdc_fifo_gray` for instructions.
///
/// See the documentation in axi_cdc_clearable for more information about the
/// differences between the clearable and the non-clearable version of the CDC.
module axi_cdc_clearable_dst
  import cdc_reset_ctrlr_pkg::clear_seq_phase_e;
 #(
  /// Depth of the FIFO crossing the clock domain, given as 2**LOG_DEPTH.
  parameter int unsigned LogDepth = 1,
  parameter type aw_chan_t = logic,
  parameter type w_chan_t = logic,
  parameter type b_chan_t = logic,
  parameter type ar_chan_t = logic,
  parameter type r_chan_t = logic,
  parameter type axi_req_t = logic,
  parameter type axi_resp_t = logic,
  // Parameters specific to clearability feature
  parameter ClearOnAsyncReset = 1'b1,
  /// The maximum number of outstanding transactions the axi_isolate module
  /// within this IP can track (just implies a wider transaction counter).
  parameter NumPendingTransaction = 16,
  /// Address width of all AXI4+ATOP ports
  parameter int unsigned AxiAddrWidth = 32'd0,
  /// Data width of all AXI4+ATOP ports
  parameter int unsigned AxiDataWidth = 32'd0,
  /// ID width of all AXI4+ATOP ports
  parameter int unsigned AxiIdWidth = 32'd0,
  /// User signal width of all AXI4+ATOP ports
  parameter int unsigned AxiUserWidth = 32'd0
) (
  // synchronous master port - clocked by `dst_clk_i`
  input  logic                        dst_clk_i,
  /// Initiate asynchronous reset and (if ClearOnAsyncReset is enabled) initiate
  /// CDC reset sequence
  input  logic                        dst_rst_ni,
  /// Synchronously clear destination side of CDC and initiate  CDC reset sequence
  input  logic                        dst_clear_i,
  /// Synchronously clear destination side of CDC and initiate  CDC reset sequence
  /// but do not wait for graceful termination of outstanding AXI transactions.
  input  logic                        dst_force_isolate_i,
  output logic                        dst_isolated_o,
  output logic                        dst_isolate_req_o,
  input  logic                        dst_isolate_ack_i,
  output axi_req_t                    dst_req_o,
  input  axi_resp_t                   dst_resp_i,
  // asynchronous slave port
  input  aw_chan_t  [2**LogDepth-1:0] async_data_slave_aw_data_i,
  input  logic           [LogDepth:0] async_data_slave_aw_wptr_i,
  output logic           [LogDepth:0] async_data_slave_aw_rptr_o,
  input  w_chan_t   [2**LogDepth-1:0] async_data_slave_w_data_i,
  input  logic           [LogDepth:0] async_data_slave_w_wptr_i,
  output logic           [LogDepth:0] async_data_slave_w_rptr_o,
  output b_chan_t   [2**LogDepth-1:0] async_data_slave_b_data_o,
  output logic           [LogDepth:0] async_data_slave_b_wptr_o,
  input  logic           [LogDepth:0] async_data_slave_b_rptr_i,
  input  ar_chan_t  [2**LogDepth-1:0] async_data_slave_ar_data_i,
  input  logic           [LogDepth:0] async_data_slave_ar_wptr_i,
  output logic           [LogDepth:0] async_data_slave_ar_rptr_o,
  output r_chan_t   [2**LogDepth-1:0] async_data_slave_r_data_o,
  output logic           [LogDepth:0] async_data_slave_r_wptr_o,
  input  logic           [LogDepth:0] async_data_slave_r_rptr_i,
  // asynchronous clear sequence synchronization port
  output clear_seq_phase_e   async_clr_seq_next_phase_o,
  output logic               async_clr_seq_req_o,
  input logic                async_clr_seq_ack_i,
  input clear_seq_phase_e    async_clr_seq_next_phase_i,
  input logic                async_clr_seq_req_i,
  output logic               async_clr_seq_ack_o
);


  logic                      s_isolate_req;
  logic                      s_axi_isolated;
  logic                      s_isolate_ack_q;
  logic                      s_clear_req;
  logic                      s_clear_ack_q;

   // Reset sequencer
  cdc_reset_ctrlr_half #(
    .CLEAR_ON_ASYNC_RESET(ClearOnAsyncReset)
  ) i_cdc_reset_ctrlr_half (
    .clk_i         ( dst_clk_i       ),
    .rst_ni        ( dst_rst_ni      ),
    .clear_i       ( dst_clear_i     ),
    .isolate_o     ( s_isolate_req   ),
    .isolate_ack_i ( s_isolate_ack_q ),
    .clear_o       ( s_clear_req     ),
    .clear_ack_i   ( s_clear_ack_q   )
  )

  // Delay clear ack by one cycle. That's how long it takes the clearable
  // cdc_fifos to clear. The isolate ack signal is either generated by the AXI
  // isolate module or overriden by the force clear signal.
  always_ff @(posedge dst_clk_i, negedge dst_rst_ni) begin
    if (!dst_rst_ni) begin
      s_clear_ack_q   <= 1'b0;
      s_isolate_ack_q <= 1'b0;
    end else begin
      s_clear_ack_q   <= s_clear_req;
      s_isolate_ack_q <= s_isolate_req & dst_isolate_ack_i & (dst_force_isolate_i | s_axi_isolated | s_isolate_ack_q);
    end
  end

  assign dst_isolate_req_o = s_isolate_req;
  
  // AXI Isolate Module
  // This module isolates the AXI CDC channel in a graceful manner, waiting for
  // outstanding transactions to finish first.
  axi_req_t s_isolateable_axi_req;
  axi_resp_t s_isolateable_axi_resp;

  axi_isolate #(
    .NumPending           ( NumPendingTransaction ),
    .TerminateTransaction ( 1'b0                  ),
    .AtopSupport          ( 1'b1                  ),
    .AxiAddrWidth         ( AxiAddrWidth          ),
    .AxiDataWidth         ( AxiDataWidth          ),
    .AxiIdWidth           ( AxiIdWidth            ),
    .AxiUserWidth         ( AxiUserWidth          )
  ) i_axi_isolate (
    .clk_i      ( dst_clk_i              ),
    .rst_ni     ( dst_rst_ni             ),
    .slv_req_i  ( s_isolateable_axi_req  ),
    .slv_resp_o ( s_isolateable_axi_resp ),
    .mst_req_o  ( dst_req_o              ),
    .mst_resp_i ( dst_resp_i             ),
    .isolate_i  ( s_isolate_req          ),
    .isolated_o ( s_axi_isolated         )
  );

  assign dst_isolated_o = s_axi_isolated;
  assign 

  cdc_fifo_gray_dst_clearable #(
`ifdef QUESTA
    // Workaround for a bug in Questa: Pass flat logic vector instead of struct to type parameter.
    .T          ( logic [$bits(aw_chan_t)-1:0]  ),
`else
    // Other tools, such as VCS, have problems with type parameters constructed through `$bits()`.
    .T          ( aw_chan_t                     ),
`endif
    .LOG_DEPTH  ( LogDepth                      )
  ) i_cdc_fifo_gray_dst_aw (
    .async_data_i ( async_data_slave_aw_data_i      ),
    .async_wptr_i ( async_data_slave_aw_wptr_i      ),
    .async_rptr_o ( async_data_slave_aw_rptr_o      ),
    .dst_clk_i,
    .dst_rst_ni,
    .dst_clear_i  ( s_clear_req                     ),
    .dst_data_o   ( s_isolateable_axi_req.aw        ),
    .dst_valid_o  ( s_isolateable_axi_req.aw_valid  ),
    .dst_ready_i  ( s_isolateable_axi_resp.aw_ready )
  );

  cdc_fifo_gray_dst_clearable #(
`ifdef QUESTA
    .T          ( logic [$bits(w_chan_t)-1:0] ),
`else
    .T          ( w_chan_t                    ),
`endif
    .LOG_DEPTH  ( LogDepth                    )
  ) i_cdc_fifo_gray_dst_w (
    .async_data_i ( async_data_slave_w_data_i      ),
    .async_wptr_i ( async_data_slave_w_wptr_i      ),
    .async_rptr_o ( async_data_slave_w_rptr_o      ),
    .dst_clk_i,
    .dst_rst_ni,
    .dst_clear_i  ( s_clear_req                    ),
    .dst_data_o   ( s_isolateable_axi_req.w        ),
    .dst_valid_o  ( s_isolateable_axi_req.w_valid  ),
    .dst_ready_i  ( s_isolateable_axi_resp.w_ready )
  );

  cdc_fifo_gray_src_clearable #(
`ifdef QUESTA
    .T          ( logic [$bits(b_chan_t)-1:0] ),
`else
    .T          ( b_chan_t                    ),
`endif
    .LOG_DEPTH  ( LogDepth                    )
  ) i_cdc_fifo_gray_src_b (
    .src_clk_i    ( dst_clk_i                      ),
    .src_rst_ni   ( dst_rst_ni                     ),
    .src_clear_i  ( s_clear_req                    ),
    .src_data_i   ( s_isolateable_axi_resp.b       ),
    .src_valid_i  ( s_isolateable_axi_resp.b_valid ),
    .src_ready_o  ( s_isolateable_axi_req.b_ready  ),
    .async_data_o ( async_data_slave_b_data_o      ),
    .async_wptr_o ( async_data_slave_b_wptr_o      ),
    .async_rptr_i ( async_data_slave_b_rptr_i      )
  );

  cdc_fifo_gray_dst_clearable #(
`ifdef QUESTA
    .T          ( logic [$bits(ar_chan_t)-1:0]  ),
`else
    .T          ( ar_chan_t                     ),
`endif
    .LOG_DEPTH  ( LogDepth                      )
  ) i_cdc_fifo_gray_dst_ar (
    .dst_clk_i,
    .dst_rst_ni,
    .dst_clear_i  ( s_clear_req                     ),
    .dst_data_o   ( s_isolateable_axi_req.ar        ),
    .dst_valid_o  ( s_isolateable_axi_req.ar_valid  ),
    .dst_ready_i  ( s_isolateable_axi_resp.ar_ready ),
    .async_data_i ( async_data_slave_ar_data_i      ),
    .async_wptr_i ( async_data_slave_ar_wptr_i      ),
    .async_rptr_o ( async_data_slave_ar_rptr_o      )
  );

  cdc_fifo_gray_src_clearable #(
`ifdef QUESTA
    .T          ( logic [$bits(r_chan_t)-1:0] ),
`else
    .T          ( r_chan_t                    ),
`endif
    .LOG_DEPTH  ( LogDepth                    )
  ) i_cdc_fifo_gray_src_r (
    .src_clk_i    ( dst_clk_i                      ),
    .src_rst_ni   ( dst_rst_ni                     ),
    .src_clear_i  ( s_clear_req                    ),
    .src_data_i   ( s_isolateable_axi_resp.r       ),
    .src_valid_i  ( s_isolateable_axi_resp.r_valid ),
    .src_ready_o  ( s_isolateable_axi_req.r_ready  ),
    .async_data_o ( async_data_slave_r_data_o      ),
    .async_wptr_o ( async_data_slave_r_wptr_o      ),
    .async_rptr_i ( async_data_slave_r_rptr_i      )
  );

endmodule


module axi_cdc_dst_intf 
  import cdc_reset_ctrlr_pkg::clear_seq_phase_e;
#(
  parameter int unsigned AXI_ID_WIDTH = 0,
  parameter int unsigned AXI_ADDR_WIDTH = 0,
  parameter int unsigned AXI_DATA_WIDTH = 0,
  parameter int unsigned AXI_USER_WIDTH = 0,
  /// Depth of the FIFO crossing the clock domain, given as 2**LOG_DEPTH.
  parameter int unsigned LOG_DEPTH = 1,
  /// Depth of the FIFO crossing the clock domain, given as 2**LOG_DEPTH.
  parameter int unsigned LOG_DEPTH = 1,
  /// Parameters specific to clearbility feature
  PARAMETER CLEAR_ON_ASYNC_RESET = 1'b1,
  /// The maximum number of outstanding transactions the axi_isolate module
  /// within this IP can track (just implies a wider transaction counter).
  parameter NUM_PENDING_TRANSACTION = 16
) (
  // synchronous master port - clocked by `dst_clk_i`
  input  logic              dst_clk_i,
  input  logic              dst_rst_ni,
  input  logic              dst_clear_i,
  /// Synchronously clear source side of CDC and initiate  CDC reset sequence
  /// but do not wait for graceful termination of outstanding AXI transactions.
  input  logic              dst_force_isolate_i,
  output logic              dst_isolated_o,
  output logic              dst_isolate_req_o,
  input  logic              dst_isolate_ack_i,
  AXI_BUS.Master            dst,
  // asynchronous slave port
  AXI_BUS_ASYNC_GRAY.Slave  src,
  // asynchronous clear sequence synchronization port
  output clear_seq_phase_e   async_clr_seq_next_phase_o,
  output logic               async_clr_seq_req_o,
  input logic                async_clr_seq_ack_i,
  input clear_seq_phase_e    async_clr_seq_next_phase_i,
  input logic                async_clr_seq_req_i,
  output logic               async_clr_seq_ack_o
);

  typedef logic [AXI_ID_WIDTH-1:0]     id_t;
  typedef logic [AXI_ADDR_WIDTH-1:0]   addr_t;
  typedef logic [AXI_DATA_WIDTH-1:0]   data_t;
  typedef logic [AXI_DATA_WIDTH/8-1:0] strb_t;
  typedef logic [AXI_USER_WIDTH-1:0]   user_t;
  `AXI_TYPEDEF_AW_CHAN_T(aw_chan_t, addr_t, id_t, user_t)
  `AXI_TYPEDEF_W_CHAN_T(w_chan_t, data_t, strb_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T(b_chan_t, id_t, user_t)
  `AXI_TYPEDEF_AR_CHAN_T(ar_chan_t, addr_t, id_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(r_chan_t, data_t, id_t, user_t)
  `AXI_TYPEDEF_REQ_T(req_t, aw_chan_t, w_chan_t, ar_chan_t)
  `AXI_TYPEDEF_RESP_T(resp_t, b_chan_t, r_chan_t)

  req_t  dst_req;
  resp_t dst_resp;

  axi_cdc_clearable_dst #(
    .aw_chan_t  ( aw_chan_t ),
    .w_chan_t   ( w_chan_t  ),
    .b_chan_t   ( b_chan_t  ),
    .ar_chan_t  ( ar_chan_t ),
    .r_chan_t   ( r_chan_t  ),
    .axi_req_t  ( req_t     ),
    .axi_resp_t ( resp_t    ),
    .LogDepth   ( LOG_DEPTH ),
    .ClearOnAsyncReset     ( CLEAR_ON_ASYNC_RESET    ),
    .NumPendingTransaction ( NUM_PENDING_TRANSACTION ),
    .AxiAddrWidth          ( AXI_ADDR_WIDTH          ),
    .AxiDataWidth          ( AXI_DATA_WIDTH          ),
    .AxiIdWidth            ( AXI_ID_WIDTH            ),
    .AxiUserWidth          ( AXI_USER_WIDTH          )
  ) i_axi_cdc_dst (
    .dst_clk_i,
    .dst_rst_ni,
    .dst_clear_i,
    .dst_force_isolate_i,
    .dst_isolated_o,
    .dst_isolate_req_o,
    .dst_isolate_ack_i,
    .dst_req_o                  ( dst_req     ),
    .dst_resp_i                 ( dst_resp    )
    .async_data_slave_aw_data_i ( src.aw_data ),
    .async_data_slave_aw_wptr_i ( src.aw_wptr ),
    .async_data_slave_aw_rptr_o ( src.aw_rptr ),
    .async_data_slave_w_data_i  ( src.w_data  ),
    .async_data_slave_w_wptr_i  ( src.w_wptr  ),
    .async_data_slave_w_rptr_o  ( src.w_rptr  ),
    .async_data_slave_b_data_o  ( src.b_data  ),
    .async_data_slave_b_wptr_o  ( src.b_wptr  ),
    .async_data_slave_b_rptr_i  ( src.b_rptr  ),
    .async_data_slave_ar_data_i ( src.ar_data ),
    .async_data_slave_ar_wptr_i ( src.ar_wptr ),
    .async_data_slave_ar_rptr_o ( src.ar_rptr ),
    .async_data_slave_r_data_o  ( src.r_data  ),
    .async_data_slave_r_wptr_o  ( src.r_wptr  ),
    .async_data_slave_r_rptr_i  ( src.r_rptr  ),
    .async_clr_seq_next_phase_o,
    .async_clr_seq_req_o,
    .async_clr_seq_ack_i,
    .async_clr_seq_next_phase_i,
    .async_clr_seq_req_i,
    .async_clr_seq_ack_o
  );

  `AXI_ASSIGN_FROM_REQ(dst, dst_req)
  `AXI_ASSIGN_TO_RESP(dst_resp, dst)

endmodule


module axi_lite_cdc_dst_intf
  import cdc_reset_ctrlr_pkg::clear_seq_phase_e;
#(
  parameter int unsigned AXI_ADDR_WIDTH = 0,
  parameter int unsigned AXI_DATA_WIDTH = 0,
  /// Depth of the FIFO crossing the clock domain, given as 2**LOG_DEPTH.
  parameter int unsigned LOG_DEPTH = 1,
  /// Parameters specific to clearbility feature
  PARAMETER CLEAR_ON_ASYNC_RESET = 1'b1,
  /// The maximum number of outstanding transactions the axi_isolate module
  /// within this IP can track (just implies a wider transaction counter).
  parameter NUM_PENDING_TRANSACTION = 16
) (
  // synchronous master port - clocked by `dst_clk_i`
  input  logic                dst_clk_i,
  input  logic                dst_rst_ni,
  AXI_LITE.Master             dst
  input  logic                dst_clear_i,
  /// Synchronously clear source side of CDC and initiate  CDC reset sequence
  /// but do not wait for graceful termination of outstanding AXI transactions.
  input  logic                dst_force_isolate_i,
  output logic                dst_isolated_o,
  output logic                dst_isolate_req_o,
  input  logic                dst_isolate_ack_i,
  // asynchronous slave port
  AXI_LITE_ASYNC_GRAY.Slave   src,
  // asynchronous clear sequence synchronization port
  output clear_seq_phase_e    async_clr_seq_next_phase_o,
  output logic                async_clr_seq_req_o,
  input logic                 async_clr_seq_ack_i,
  input clear_seq_phase_e     async_clr_seq_next_phase_i,
  input logic                 async_clr_seq_req_i,
  output logic                async_clr_seq_ack_o
);

  typedef logic [AXI_ADDR_WIDTH-1:0]   addr_t;
  typedef logic [AXI_DATA_WIDTH-1:0]   data_t;
  typedef logic [AXI_DATA_WIDTH/8-1:0] strb_t;
  `AXI_LITE_TYPEDEF_AW_CHAN_T(aw_chan_t, addr_t)
  `AXI_LITE_TYPEDEF_W_CHAN_T(w_chan_t, data_t, strb_t)
  `AXI_LITE_TYPEDEF_B_CHAN_T(b_chan_t)
  `AXI_LITE_TYPEDEF_AR_CHAN_T(ar_chan_t, addr_t)
  `AXI_LITE_TYPEDEF_R_CHAN_T(r_chan_t, data_t)
  `AXI_LITE_TYPEDEF_REQ_T(req_t, aw_chan_t, w_chan_t, ar_chan_t)
  `AXI_LITE_TYPEDEF_RESP_T(resp_t, b_chan_t, r_chan_t)

  req_t   dst_req;
  resp_t  dst_resp;

  axi_cdc_clearable_dst #(
    .aw_chan_t  ( aw_chan_t ),
    .w_chan_t   ( w_chan_t  ),
    .b_chan_t   ( b_chan_t  ),
    .ar_chan_t  ( ar_chan_t ),
    .r_chan_t   ( r_chan_t  ),
    .axi_req_t  ( req_t     ),
    .axi_resp_t ( resp_t    ),
    .LogDepth   ( LOG_DEPTH ),
    .ClearOnAsyncReset     ( CLEAR_ON_ASYNC_RESET    ),
    .NumPendingTransaction ( NUM_PENDING_TRANSACTION ),
    .AxiAddrWidth          ( AXI_ADDR_WIDTH          ),
    .AxiDataWidth          ( AXI_DATA_WIDTH          ),
    .AxiIdWidth            ( AXI_ID_WIDTH            ),
    .AxiUserWidth          ( AXI_USER_WIDTH          )
  ) i_axi_cdc_dst (
    .dst_clk_i,
    .dst_rst_ni,
    .dst_clear_i,
    .dst_force_isolate_i,
    .dst_isolated_o,
    .dst_isolate_req_o,
    .dst_isolate_ack_i,
    .dst_req_o                  ( dst_req     ),
    .dst_resp_i                 ( dst_resp    ),
    .async_data_slave_aw_data_i ( src.aw_data ),
    .async_data_slave_aw_wptr_i ( src.aw_wptr ),
    .async_data_slave_aw_rptr_o ( src.aw_rptr ),
    .async_data_slave_w_data_i  ( src.w_data  ),
    .async_data_slave_w_wptr_i  ( src.w_wptr  ),
    .async_data_slave_w_rptr_o  ( src.w_rptr  ),
    .async_data_slave_b_data_o  ( src.b_data  ),
    .async_data_slave_b_wptr_o  ( src.b_wptr  ),
    .async_data_slave_b_rptr_i  ( src.b_rptr  ),
    .async_data_slave_ar_data_i ( src.ar_data ),
    .async_data_slave_ar_wptr_i ( src.ar_wptr ),
    .async_data_slave_ar_rptr_o ( src.ar_rptr ),
    .async_data_slave_r_data_o  ( src.r_data  ),
    .async_data_slave_r_wptr_o  ( src.r_wptr  ),
    .async_data_slave_r_rptr_i  ( src.r_rptr  ),
    .async_clr_seq_next_phase_o,
    .async_clr_seq_req_o,
    .async_clr_seq_ack_i,
    .async_clr_seq_next_phase_i,
    .async_clr_seq_req_i,
    .async_clr_seq_ack_o
  );

  `AXI_LITE_ASSIGN_FROM_REQ(dst, dst_req)
  `AXI_LITE_ASSIGN_TO_RESP(dst_resp, dst)

endmodule
