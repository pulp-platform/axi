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

// Autor: Wolfgang Roenninger <wroennin@ethz.ch>

// AXI MUX: This module muxes multiple AXI4 mst ports down to one slv port.
// It only complies to the Axi standard, if the unique mst port inedx is present
// in the MSB's of the axi id. The Response switching happens on these bits.
// EG: 4 SLV ports: Response of AXI transaction with ID: `6'b100110 will be forwarded
//     to MST port `2'b10`.
module axi_mux #(
  parameter int unsigned NO_SLV_PORTS = 1,     // Number of slave ports
  parameter int unsigned AXI_ID_WIDTH = 1,     // Id Width of the axi going througth
  parameter type         aw_chan_t    = logic, // AW Channel Type
  parameter type         w_chan_t     = logic, //  W Channel Type
  parameter type         b_chan_t     = logic, //  B Channel Type
  parameter type         ar_chan_t    = logic, // AR Channel Type
  parameter type         r_chan_t     = logic, //  R Channel Type
  // Maximum number of outstanding transactions per write
  parameter int unsigned MAX_W_TRANS  = 8,
  // When enabled theoretical one cycle transaction, but long logic paths
  parameter bit          FALL_THROUGH = 1'b0,
  // add spill register on aw mst port, adds a cycle latency on aw channel
  parameter bit          SPILL_AW     = 1'b1,
  parameter bit          SPILL_W      = 1'b0,
  parameter bit          SPILL_B      = 1'b0,
  // add spill register on ar mst port, adds a cycle latency on ar channel
  parameter bit          SPILL_AR     = 1'b1,
  parameter bit          SPILL_R      = 1'b0
) (
  input  logic clk_i,    // Clock
  input  logic rst_ni,   // Asynchronous reset active low
  input  logic test_i,   // Test Mode enable
  // slave ports (Axi inputs), connect master modules here
  // AW channel
  input  aw_chan_t [NO_SLV_PORTS-1:0] slv_aw_chans_i,
  input  logic     [NO_SLV_PORTS-1:0] slv_aw_valids_i,
  output logic     [NO_SLV_PORTS-1:0] slv_aw_readies_o,
  //  W channel
  input  w_chan_t  [NO_SLV_PORTS-1:0] slv_w_chans_i,
  input  logic     [NO_SLV_PORTS-1:0] slv_w_valids_i,
  output logic     [NO_SLV_PORTS-1:0] slv_w_readies_o,
  //  B channel
  output b_chan_t  [NO_SLV_PORTS-1:0] slv_b_chans_o,
  output logic     [NO_SLV_PORTS-1:0] slv_b_valids_o,
  input  logic     [NO_SLV_PORTS-1:0] slv_b_readies_i,
  // AR channel
  input  ar_chan_t [NO_SLV_PORTS-1:0] slv_ar_chans_i,
  input  logic     [NO_SLV_PORTS-1:0] slv_ar_valids_i,
  output logic     [NO_SLV_PORTS-1:0] slv_ar_readies_o,
  //  R channel
  output r_chan_t  [NO_SLV_PORTS-1:0] slv_r_chans_o,
  output logic     [NO_SLV_PORTS-1:0] slv_r_valids_o,
  input  logic     [NO_SLV_PORTS-1:0] slv_r_readies_i,
  // master port (Axi outputs), connect slave modules here
  // AW channel
  output aw_chan_t                    mst_aw_chan_o,
  output logic                        mst_aw_valid_o,
  input  logic                        mst_aw_ready_i,
  //  W channel
  output w_chan_t                     mst_w_chan_o,
  output logic                        mst_w_valid_o,
  input  logic                        mst_w_ready_i,
  //  B channel
  input  b_chan_t                     mst_b_chan_i,
  input  logic                        mst_b_valid_i,
  output logic                        mst_b_ready_o,
  // AR channel
  output ar_chan_t                    mst_ar_chan_o,
  output logic                        mst_ar_valid_o,
  input  logic                        mst_ar_ready_i,
  //  R channel
  input  r_chan_t                     mst_r_chan_i,
  input  logic                        mst_r_valid_i,
  output logic                        mst_r_ready_o
);

  // typedef for the w_fifo
  localparam int unsigned MST_IDX_BITS = $clog2(NO_SLV_PORTS);
  // these are for finding the right bit of the return id for the switching
  localparam int unsigned MST_IDX      = AXI_ID_WIDTH - MST_IDX_BITS;

  typedef logic [MST_IDX_BITS-1:0] switch_id_t;

  // aw channel
  aw_chan_t   mst_aw_chan;
  logic       mst_aw_valid, mst_aw_ready;

  // AW mst handshake internal, so that we are able to stall, if w_fifo is full
  logic       aw_valid,     aw_ready;

  // fifo signals, the fifo holds the last switching decision of the AW channel
  switch_id_t switch_aw_id;
  logic       w_fifo_full,  w_fifo_empty;
  logic       w_fifo_push,  w_fifo_pop;
  switch_id_t w_fifo_data;

  // w channel spill reg
  w_chan_t    mst_w_chan;
  logic       mst_w_valid,  mst_w_ready;

  // master id in the b_id
  switch_id_t switch_b_id;

  // b channel spill reg
  b_chan_t    mst_b_chan;
  logic       mst_b_valid,  mst_b_ready;

  // ar channel for when spill is eneabled
  ar_chan_t   mst_ar_chan;
  logic       ar_valid,     ar_ready;

  // master id in the r_id
  switch_id_t switch_r_id;

  // r channel spill reg
  r_chan_t    mst_r_chan;
  logic       mst_r_valid,  mst_r_ready;

  //--------------------------------------
  // AW Channel
  //--------------------------------------
  rr_arb_tree #(
    .NumIn    ( NO_SLV_PORTS ),
    .DataType ( aw_chan_t  ),
    .AxiVldRdy( 1'b1       ),
    .LockIn   ( 1'b1       )
  ) i_aw_arbiter (
    .clk_i  ( clk_i            ),
    .rst_ni ( rst_ni           ),
    .flush_i( 1'b0             ),
    .rr_i   ( '0               ),
    .req_i  ( slv_aw_valids_i  ),
    .gnt_o  ( slv_aw_readies_o ),
    .data_i ( slv_aw_chans_i   ),
    .gnt_i  ( aw_ready         ),
    .req_o  ( aw_valid         ),
    .data_o ( mst_aw_chan      ),
    .idx_o  (                  )
  );
  always_comb begin : proc_aw_chan
    // default assignments
    w_fifo_push    = 1'b0;
    mst_aw_valid   = 1'b0;
    aw_ready       = 1'b0;
    // control
    if(!w_fifo_full) begin
      // connect the handshake
      mst_aw_valid = aw_valid;
      aw_ready     = mst_aw_ready;
      // on AW transaction
      if(aw_valid && mst_aw_ready) begin
        w_fifo_push = 1'b1;
      end
    end
  end
  assign switch_aw_id = mst_aw_chan.id[MST_IDX+:MST_IDX_BITS];
  fifo_v3 #(
    .FALL_THROUGH ( FALL_THROUGH ),
    .DEPTH        ( MAX_W_TRANS   ),
    .dtype        ( switch_id_t )
  ) i_w_fifo (
    .clk_i     ( clk_i        ),
    .rst_ni    ( rst_ni       ),
    .flush_i   ( 1'b0         ),
    .testmode_i( test_i       ),
    .full_o    ( w_fifo_full  ),
    .empty_o   ( w_fifo_empty ),
    .usage_o   (              ),
    .data_i    ( switch_aw_id ),
    .push_i    ( w_fifo_push  ),
    .data_o    ( w_fifo_data  ),
    .pop_i     ( w_fifo_pop   )
  );
  if (SPILL_AW) begin : gen_spill_aw
    spill_register #(
      .T       ( aw_chan_t      )
    ) i_aw_spill_reg (
      .clk_i   ( clk_i          ),
      .rst_ni  ( rst_ni         ),
      .valid_i ( mst_aw_valid   ),
      .ready_o ( mst_aw_ready   ),
      .data_i  ( mst_aw_chan    ),
      .valid_o ( mst_aw_valid_o ),
      .ready_i ( mst_aw_ready_i ),
      .data_o  ( mst_aw_chan_o  )
    );
  end else begin : gen_no_spill_aw
    assign mst_aw_chan_o  = mst_aw_chan;
    assign mst_aw_valid_o = mst_aw_valid;
    assign mst_aw_ready   = mst_aw_ready_i;
  end

  //--------------------------------------
  // W Channel
  //--------------------------------------
  // mux
  assign mst_w_chan = slv_w_chans_i[w_fifo_data];
  always_comb begin : proc_w_chan
    // default assignments
    mst_w_valid   = 1'b0;
    slv_w_readies = '0;
    w_fifo_pop    = 1'b0;
    // control
    if(!w_fifo_empty) begin
      // connect the handshake
      mst_w_valid                  = slv_w_valids_i[w_fifo_data];
      slv_w_readies_o[w_fifo_data] = mst_w_ready;
      // pop fifo on a last transaction
      if(slv_w_valids_i[w_fifo_data] && mst_w_ready && mst_w_chan.last) begin
        w_fifo_pop = 1'b1;
      end
    end
  end
  if (SPILL_W) begin : gen_spill_w
    spill_register #(
      .T       ( w_chan_t      )
    ) i_w_spill_reg (
      .clk_i   ( clk_i         ),
      .rst_ni  ( rst_ni        ),
      .valid_i ( mst_w_valid   ),
      .ready_o ( mst_w_ready   ),
      .data_i  ( mst_w_chan    ),
      .valid_o ( mst_w_valid_o ),
      .ready_i ( mst_w_ready_i ),
      .data_o  ( mst_w_chan_o  )
    );
  end else begin : gen_no_spill_w
    assign mst_w_chan_o  = mst_w_chan;
    assign mst_w_valid_o = mst_w_valid;
    assign mst_w_ready   = mst_w_ready_i;
  end

  //--------------------------------------
  // B Channel
  //--------------------------------------
  always_comb begin : proc_b_chan
    for (int unsigned i = 0; i < NO_SLV_PORTS; i++) begin
      slv_b_chans_o[i] = mst_b_chan;
    end
    switch_b_id                 = mst_b_chan.id[MST_IDX+:MST_IDX_BITS];
    slv_b_valids_o              = '0;
    slv_b_valids_o[switch_b_id] = mst_b_valid;
    mst_b_ready                 = slv_b_readies_i[switch_b_id];
  end
  if (SPILL_B) begin : gen_spill_b
    spill_register #(
      .T       ( b_chan_t      )
    ) i_b_spill_reg (
      .clk_i   ( clk_i         ),
      .rst_ni  ( rst_ni        ),
      .valid_i ( mst_b_valid_i ),
      .ready_o ( mst_b_ready_o ),
      .data_i  ( mst_b_chan_i  ),
      .valid_o ( mst_b_valid   ),
      .ready_i ( mst_b_ready   ),
      .data_o  ( mst_b_chan    )
    );
  end else begin : gen_no_spill_b
    assign mst_b_chan    = mst_b_chan_i;
    assign mst_b_valid   = mst_b_valid_i;
    assign mst_b_ready_o = mst_r_ready;
  end

  //--------------------------------------
  // AR Channel
  //--------------------------------------
  rr_arb_tree #(
    .NumIn    ( NO_SLV_PORTS ),
    .DataType ( ar_chan_t  ),
    .AxiVldRdy( 1'b1       ),
    .LockIn   ( 1'b1       )
  ) i_ar_arbiter (
    .clk_i  ( clk_i            ),
    .rst_ni ( rst_ni           ),
    .flush_i( 1'b0             ),
    .rr_i   ( '0               ),
    .req_i  ( slv_ar_valids_i  ),
    .gnt_o  ( slv_ar_readies_o ),
    .data_i ( slv_ar_chans_i   ),
    .gnt_i  ( ar_ready         ),
    .req_o  ( ar_valid         ),
    .data_o ( mst_ar_chan      ),
    .idx_o  (                  )
  );
  if (SPILL_AR) begin : gen_spill_ar
    spill_register #(
      .T(ar_chan_t)
    ) i_ar_spill_reg (
      .clk_i   ( clk_i          ),
      .rst_ni  ( rst_ni         ),
      .valid_i ( ar_valid       ),
      .ready_o ( ar_ready       ),
      .data_i  ( mst_ar_chan    ),
      .valid_o ( mst_ar_valid_o ),
      .ready_i ( mst_ar_ready_i ),
      .data_o  ( mst_ar_chan_o  )
    );
  end else begin : gen_no_spill_ar
    assign mst_ar_chan_o  = mst_ar_chan;
    assign mst_ar_valid_o = ar_valid;
    assign ar_ready       = mst_ar_ready_i;
  end

  //--------------------------------------
  // R Channel
  //--------------------------------------
  always_comb begin : proc_r_chan
    for (int unsigned i = 0; i < NO_SLV_PORTS; i++) begin
      slv_r_chans_o[i] = mst_r_chan;
    end
    switch_r_id                 = mst_r_chan.id[MST_IDX+:MST_IDX_BITS];
    slv_r_valids_o              = '0;
    slv_r_valids_o[switch_r_id] = mst_r_valid;
    mst_r_ready                 = slv_r_readies_i[switch_r_id];
  end
  if (SPILL_R) begin : gen_spill_r
    spill_register #(
      .T       ( r_chan_t      )
    ) i_r_spill_reg (
      .clk_i   ( clk_i         ),
      .rst_ni  ( rst_ni        ),
      .valid_i ( mst_r_valid_i ),
      .ready_o ( mst_r_ready_o ),
      .data_i  ( mst_r_chan_i  ),
      .valid_o ( mst_r_valid   ),
      .ready_i ( mst_r_ready   ),
      .data_o  ( mst_r_chan    )
    );
  end else begin : gen_no_spill_b
    assign mst_r_chan    = mst_r_chan_i;
    assign mst_r_valid   = mst_r_valid_i;
    assign mst_r_ready_o = mst_r_ready;
  end
endmodule
