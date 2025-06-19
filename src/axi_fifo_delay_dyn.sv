// Copyright 2025 ETH Zurich and University of Bologna.
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
// - Enrico Zelioli <ezelioli@iis.ee.ethz.ch>

`include "common_cells/registers.svh"
`include "axi/typedef.svh"
`include "axi/assign.svh"

/// Delay and buffer an AXI bus
module axi_fifo_delay_dyn #(
  // AXI channel types
  parameter type  aw_chan_t = logic,
  parameter type   w_chan_t = logic,
  parameter type   b_chan_t = logic,
  parameter type  ar_chan_t = logic,
  parameter type   r_chan_t = logic,
  // AXI request & response types
  parameter type  axi_req_t = logic,
  parameter type axi_resp_t = logic,
  // delay parameters
  parameter int unsigned DepthAR  = 4,    // Power of two
  parameter int unsigned DepthAW  = 4,    // Power of two
  parameter int unsigned DepthR   = 4,    // Power of two
  parameter int unsigned DepthW   = 4,    // Power of two
  parameter int unsigned DepthB   = 4,     // Power of two
  parameter int unsigned MaxDelay = 1024,
  // DO NOT EDIT, derived parameters
  localparam int unsigned DelayWidth = $clog2(MaxDelay) + 1
) (
  input  logic                  clk_i,      // Clock
  input  logic                  rst_ni,     // Asynchronous reset active low
  input  logic [DelayWidth-1:0] aw_delay_i,
  input  logic [DelayWidth-1:0] w_delay_i,
  input  logic [DelayWidth-1:0] b_delay_i,
  input  logic [DelayWidth-1:0] ar_delay_i,
  input  logic [DelayWidth-1:0] r_delay_i,
  // slave port
  input  axi_req_t              slv_req_i,
  output axi_resp_t             slv_resp_o,
  // master port
  output axi_req_t              mst_req_o,
  input  axi_resp_t             mst_resp_i
);

  if (DepthAR > 0) begin
    stream_fifo_delay_dyn #(
      .payload_t ( ar_chan_t ),
      .MaxDelay  ( MaxDelay  ),
      .Depth     ( DepthAR   )
    ) i_ar_fifo_delay (
      .clk_i     ( clk_i               ),
      .rst_ni    ( rst_ni              ),
      .delay_i   ( ar_delay_i          ),
      .payload_i ( slv_req_i.ar        ),
      .ready_o   ( slv_resp_o.ar_ready ),
      .valid_i   ( slv_req_i.ar_valid  ),
      .payload_o ( mst_req_o.ar        ),
      .ready_i   ( mst_resp_i.ar_ready ),
      .valid_o   ( mst_req_o.ar_valid  )
    );
  end else begin
    // AR channel pass-through
    assign mst_req_o.ar        = slv_req_i.ar;
    assign mst_req_o.ar_valid  = slv_req_i.ar_valid;
    assign slv_resp_o.ar_ready = mst_resp_i.ar_ready;
  end

  if (DepthAW > 0) begin
    stream_fifo_delay_dyn #(
      .payload_t ( aw_chan_t ),
      .MaxDelay  ( MaxDelay  ),
      .Depth     ( DepthAW   )
    ) i_aw_fifo_delay (
      .clk_i     ( clk_i               ),
      .rst_ni    ( rst_ni              ),
      .delay_i   ( aw_delay_i          ),
      .payload_i ( slv_req_i.aw        ),
      .ready_o   ( slv_resp_o.aw_ready ),
      .valid_i   ( slv_req_i.aw_valid  ),
      .payload_o ( mst_req_o.aw        ),
      .ready_i   ( mst_resp_i.aw_ready ),
      .valid_o   ( mst_req_o.aw_valid  )
    );
  end else begin
    // AW channel pass-through
    assign mst_req_o.aw        = slv_req_i.aw;
    assign mst_req_o.aw_valid  = slv_req_i.aw_valid;
    assign slv_resp_o.aw_ready = mst_resp_i.aw_ready;
  end

  if (DepthR > 0) begin
    stream_fifo_delay_dyn #(
      .payload_t ( r_chan_t ),
      .MaxDelay  ( MaxDelay ),
      .Depth     ( DepthR   )
    ) i_r_fifo_delay (
      .clk_i     ( clk_i              ),
      .rst_ni    ( rst_ni             ),
      .delay_i   ( r_delay_i          ),
      .payload_i ( mst_resp_i.r       ),
      .ready_o   ( mst_req_o.r_ready  ),
      .valid_i   ( mst_resp_i.r_valid ),
      .payload_o ( slv_resp_o.r       ),
      .ready_i   ( slv_req_i.r_ready  ),
      .valid_o   ( slv_resp_o.r_valid )
    );
  end else begin
    // R channel pass-through
    assign mst_req_o.r_ready  = slv_req_i.r_ready;
    assign slv_resp_o.r_valid = mst_resp_i.r_valid;
    assign slv_resp_o.r       = mst_resp_i.r;
  end

  if (DepthW > 0) begin
    stream_fifo_delay_dyn #(
      .payload_t ( w_chan_t ),
      .MaxDelay  ( MaxDelay ),
      .Depth     ( DepthW   )
    ) i_w_fifo_delay (
      .clk_i     ( clk_i              ),
      .rst_ni    ( rst_ni             ),
      .delay_i   ( w_delay_i          ),
      .payload_i ( slv_req_i.w        ),
      .ready_o   ( slv_resp_o.w_ready ),
      .valid_i   ( slv_req_i.w_valid  ),
      .payload_o ( mst_req_o.w        ),
      .ready_i   ( mst_resp_i.w_ready ),
      .valid_o   ( mst_req_o.w_valid  )
    );
  end else begin
    // W channel pass-through
    assign mst_req_o.w         = slv_req_i.w;
    assign mst_req_o.w_valid   = slv_req_i.w_valid;
    assign slv_resp_o.w_ready  = mst_resp_i.w_ready;
  end

  if (DepthB > 0) begin
    stream_fifo_delay_dyn #(
      .payload_t ( b_chan_t ),
      .MaxDelay  ( MaxDelay ),
      .Depth     ( DepthB   )
    ) i_b_fifo_delay (
      .clk_i     ( clk_i              ),
      .rst_ni    ( rst_ni             ),
      .delay_i   ( b_delay_i          ),
      .payload_i ( mst_resp_i.b       ),
      .ready_o   ( mst_req_o.b_ready  ),
      .valid_i   ( mst_resp_i.b_valid ),
      .payload_o ( slv_resp_o.b       ),
      .ready_i   ( slv_req_i.b_ready  ),
      .valid_o   ( slv_resp_o.b_valid )
    );
  end else begin
    // B channel pass-through
    assign mst_req_o.b_ready   = slv_req_i.b_ready;
    assign slv_resp_o.b        = mst_resp_i.b;
    assign slv_resp_o.b_valid  = mst_resp_i.b_valid;
  end

endmodule



/// Delay and buffer an AXI bus interface wrapper
module axi_fifo_delay_dyn_intf #(
  // Synopsys DC requires a default value for parameters.
  parameter int unsigned AXI_ID_WIDTH        = 0,
  parameter int unsigned AXI_ADDR_WIDTH      = 0,
  parameter int unsigned AXI_DATA_WIDTH      = 0,
  parameter int unsigned AXI_USER_WIDTH      = 0,
  parameter int unsigned DEPTH_AR            = 4, // Power of two
  parameter int unsigned DEPTH_AW            = 4, // Power of two
  parameter int unsigned DEPTH_R             = 4, // Power of two
  parameter int unsigned DEPTH_W             = 4, // Power of two
  parameter int unsigned DEPTH_B             = 4, // Power of two
  parameter int unsigned MAX_DELAY           = 0,
  // DO NOT EDIT, derived parameters
  parameter int unsigned DELAY_WIDTH         = $clog2(MAX_DELAY) + 1
) (
  input  logic                 clk_i,
  input  logic                 rst_ni,
  input  logic [MAX_DELAY-1:0] aw_delay_i,
  input  logic [MAX_DELAY-1:0] w_delay_i,
  input  logic [MAX_DELAY-1:0] b_delay_i,
  input  logic [MAX_DELAY-1:0] ar_delay_i,
  input  logic [MAX_DELAY-1:0] r_delay_i,
  AXI_BUS.Slave                slv,
  AXI_BUS.Master               mst
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
  `AXI_TYPEDEF_REQ_T(axi_req_t, aw_chan_t, w_chan_t, ar_chan_t)
  `AXI_TYPEDEF_RESP_T(axi_resp_t, b_chan_t, r_chan_t)

  axi_req_t  slv_req,  mst_req;
  axi_resp_t slv_resp, mst_resp;

  `AXI_ASSIGN_TO_REQ(slv_req, slv)
  `AXI_ASSIGN_FROM_RESP(slv, slv_resp)

  `AXI_ASSIGN_FROM_REQ(mst, mst_req)
  `AXI_ASSIGN_TO_RESP(mst_resp, mst)

  axi_fifo_delay_dyn #(
    .aw_chan_t  (  aw_chan_t ),
    .w_chan_t   (   w_chan_t ),
    .b_chan_t   (   b_chan_t ),
    .ar_chan_t  (  ar_chan_t ),
    .r_chan_t   (   r_chan_t ),
    .axi_req_t  (  axi_req_t ),
    .axi_resp_t ( axi_resp_t ),
    .DepthAR    (   DEPTH_AR ),
    .DepthAW    (   DEPTH_AW ),
    .DepthR     (    DEPTH_R ),
    .DepthW     (    DEPTH_W ),
    .DepthB     (    DEPTH_B ),
    .MaxDelay   (  MAX_DELAY )
  ) i_axi_fifo_delay_dyn (
    .clk_i,   // Clock
    .rst_ni,  // Asynchronous reset active low
    .aw_delay_i ( aw_delay_i ),
    .w_delay_i  ( w_delay_i  ),
    .b_delay_i  ( b_delay_i  ),
    .ar_delay_i ( ar_delay_i ),
    .r_delay_i  ( r_delay_i  ),
    .slv_req_i  ( slv_req    ),
    .slv_resp_o ( slv_resp   ),
    .mst_req_o  ( mst_req    ),
    .mst_resp_i ( mst_resp   )
  );

// pragma translate_off
`ifndef VERILATOR
  initial begin: p_assertions
    assert (AXI_ID_WIDTH >= 1) else $fatal(1, "AXI ID width must be at least 1!");
    assert (AXI_ADDR_WIDTH >= 1) else $fatal(1, "AXI ADDR width must be at least 1!");
    assert (AXI_DATA_WIDTH >= 1) else $fatal(1, "AXI DATA width must be at least 1!");
    assert (AXI_USER_WIDTH >= 1) else $fatal(1, "AXI USER width must be at least 1!");
  end
`endif
// pragma translate_on
endmodule



/// Delay and buffer a stream with AXI-like handshaking
module stream_fifo_delay_dyn #(
  parameter type payload_t           = logic,
  parameter int unsigned MaxDelay    = 1024,
  parameter int unsigned Depth       = 4,      // Power of two
  // DO NOT EDIT, derived parameters
  parameter int unsigned CounterWidth = $clog2(MaxDelay) + 1
)(
  input  logic                    clk_i,
  input  logic                    rst_ni,
  input  logic [CounterWidth-1 : 0]     delay_i,
  input  payload_t                payload_i,
  output logic                    ready_o,
  input  logic                    valid_i,
  output payload_t                payload_o,
  input  logic                    ready_i,
  output logic                    valid_o
);

  `ifdef SYNTHESIS
  `ifndef TARGET_XILINX
  $fatal(1, "Delay unit is not made for synthesis");
  `endif
  `endif

  if (Depth & (Depth - 1) == 0)
    $fatal(1, "Depth must be a power of two");

  localparam int unsigned BookeepingBits = $clog2(Depth) + 1;
  logic [BookeepingBits-1 : 0] dead_count_d, dead_count_q;

  // head_deadline : latest element's deadline
  // tail_deadline : next element's deadline
  logic [CounterWidth-1 : 0] count_val;
  logic [CounterWidth-1 : 0] head_deadline, tail_deadline;
  payload_t head_data;

  logic fifo_dead_full, fifo_dead_empty, fifo_dead_push, fifo_dead_pop;
  logic fifo_data_full, fifo_data_empty, fifo_data_push, fifo_data_pop;

  `FF(dead_count_q, dead_count_d, '0, clk_i, rst_ni);

  always_comb begin
    dead_count_d = dead_count_q;
    if (fifo_dead_pop)
      dead_count_d += 1;
    if (fifo_data_pop)
      dead_count_d -= 1;
  end

  assign tail_deadline = count_val + delay_i + 1;

  assign fifo_data_push = ~fifo_data_full & valid_i;
  assign fifo_dead_push = fifo_data_push;

  assign fifo_dead_pop = (count_val == head_deadline) & ~fifo_dead_empty;
  assign fifo_data_pop = valid_o & ready_i;

  assign valid_o = (dead_count_q > 0);
  assign ready_o = ~fifo_data_full;

  assign payload_o = head_data;

  counter #(
    .WIDTH      ( CounterWidth )
  ) i_counter (
    .clk_i,
    .rst_ni,
    .clear_i    ( 1'b0         ),
    .en_i       ( 1'b1         ),
    .load_i     ( 1'b0         ),
    .down_i     ( 1'b0         ),
    .d_i        ( '0           ),
    .q_o        ( count_val    ),
    .overflow_o (              )
  );

`ifdef TARGET_XILINX
  xpm_fifo_sync #(
    .FIFO_MEMORY_TYPE    ( "auto"           ) , // string; "auto", "block", "distributed", or "ultra";
    .ECC_MODE            ( "no_ecc"         ) , // string; "no_ecc" or "en_ecc";
    .FIFO_WRITE_DEPTH    ( Depth            ) , // positive integer
    .WRITE_DATA_WIDTH    ( $bits(payload_t) ) , // positive integer
    .WR_DATA_COUNT_WIDTH ( $clog2(Depth)+1  ) , // positive integer, not used
    .PROG_FULL_THRESH    ( 10               ) , // positive integer, not used
    .FULL_RESET_VALUE    ( 1                ) , // positive integer; 0 or 1
    .USE_ADV_FEATURES    ( "1F1F"           ) , // string; "0000" to "1F1F";
    .READ_MODE           ( "std"            ) , // string; "std" or "fwft";
    .FIFO_READ_LATENCY   ( 0                ) , // positive integer;
    .READ_DATA_WIDTH     ( $bits(payload_t) ) , // positive integer
    .RD_DATA_COUNT_WIDTH ( $clog2(Depth)+1  ) , // positive integer, not used
    .PROG_EMPTY_THRESH   ( 10               ) , // positive integer, not used
    .DOUT_RESET_VALUE    ( "0"              ) , // string, don't care
    .WAKEUP_TIME         ( 0                ) // positive integer; 0 or 2;
  ) data_fifo (
    .sleep('0),
    .injectsbiterr('0),
    .injectdbiterr('0),
    .wr_clk(clk_i),
    .rst(~rst_ni),
    .wr_en(fifo_data_push),
    .rd_en(fifo_data_pop),
    .full(fifo_data_full),
    .empty(fifo_data_empty),
    .din(payload_i),
    .dout(head_data)
  );
`else
  fifo_v3 #(
    .DATA_WIDTH  ( $bits(payload_t) ),
    .DEPTH       ( Depth            ),
    .FALL_THROUGH( 1'b0             )
  ) data_fifo (
    .clk_i     (clk_i               ),
    .rst_ni    (rst_ni              ),
    .flush_i   (1'b0                ),
    .testmode_i(1'b0                ),
    .data_i    (payload_i           ),
    .push_i    (fifo_data_push      ),
    .full_o    (fifo_data_full      ),
    .data_o    (head_data           ),
    .pop_i     (fifo_data_pop       ),
    .empty_o   (fifo_data_empty     ),
    .usage_o   (/* Unused */        )
  );
`endif

`ifdef TARGET_XILINX
  xpm_fifo_sync #(
    .FIFO_MEMORY_TYPE    ( "auto"          ) , // string; "auto", "block", "distributed", or "ultra";
    .ECC_MODE            ( "no_ecc"        ) , // string; "no_ecc" or "en_ecc";
    .FIFO_WRITE_DEPTH    ( Depth           ) , // positive integer
    .WRITE_DATA_WIDTH    ( CounterWidth    ) , // positive integer
    .WR_DATA_COUNT_WIDTH ( $clog2(Depth)+1 ) , // positive integer, not used
    .PROG_FULL_THRESH    ( 10              ) , // positive integer, not used
    .FULL_RESET_VALUE    ( 1               ) , // positive integer; 0 or 1
    .USE_ADV_FEATURES    ( "1F1F"          ) , // string; "0000" to "1F1F";
    .READ_MODE           ( "std"           ) , // string; "std" or "fwft";
    .FIFO_READ_LATENCY   ( 0               ) , // positive integer;
    .READ_DATA_WIDTH     ( CounterWidth    ) , // positive integer
    .RD_DATA_COUNT_WIDTH ( $clog2(Depth)+1 ) , // positive integer, not used
    .PROG_EMPTY_THRESH   ( 10              ) , // positive integer, not used
    .DOUT_RESET_VALUE    ( "0"             ) , // string, don't care
    .WAKEUP_TIME         ( 0               ) // positive integer; 0 or 2;
  ) deadline_fifo (
    .sleep('0),
    .injectsbiterr('0),
    .injectdbiterr('0),
    .wr_clk(clk_i),
    .rst(~rst_ni),
    .wr_en(fifo_dead_push),
    .rd_en(fifo_dead_pop),
    .full(fifo_dead_full),
    .empty(fifo_dead_empty),
    .din(tail_deadline),
    .dout(head_deadline)
  );
`else
  fifo_v3 #(
    .DATA_WIDTH  ( CounterWidth     ),
    .DEPTH       ( Depth            ),
    .FALL_THROUGH( 1'b0             )
  ) deadline_fifo (
    .clk_i     (clk_i               ),
    .rst_ni    (rst_ni              ),
    .flush_i   (1'b0                ),
    .testmode_i(1'b0                ),
    .data_i    (tail_deadline       ),
    .push_i    (fifo_dead_push      ),
    .full_o    (fifo_dead_full      ),
    .data_o    (head_deadline       ),
    .pop_i     (fifo_dead_pop       ),
    .empty_o   (fifo_dead_empty     ),
    .usage_o   (/* Unused */        )
  );
`endif

endmodule
