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

// AXI DECERR SLV: This module always responds with an AXI decode error for transactions
// which are sent to it. Depends on axi_atop_filter for atomics support.

module axi_decerr_slv #(
  parameter int unsigned AxiIdWidth  = 0,     // AXI ID Width
  parameter type         req_t       = logic, // AXI 4 REQUEST struct, with atop field
  parameter type         resp_t      = logic, // AXI 4 REQUEST struct
  parameter bit          FallThrough = 1'b1, // When enabled: in cycle transaction, long paths
  parameter int unsigned MaxTrans    = 1     // Determines the FiFo depth between the channels
) (
  input  logic  clk_i,   // Clock
  input  logic  rst_ni,  // Asynchronous reset active low
  input  logic  test_i,  // Testmode enable
  // slave port
  input  req_t  slv_req_i,
  output resp_t slv_resp_o
);
  typedef logic [AxiIdWidth-1:0] id_t;
  typedef struct packed {
    id_t           id;
    axi_pkg::len_t len;
  } r_data_t;

  req_t  decerr_req;
  resp_t decerr_resp;

  // w fifo
  logic    w_fifo_full, w_fifo_empty;
  logic    w_fifo_push, w_fifo_pop;
  id_t     w_fifo_data;
  // b fifo
  logic    b_fifo_full, b_fifo_empty;
  logic    b_fifo_push, b_fifo_pop;
  id_t     b_fifo_data;
  // r fifo
  r_data_t r_fifo_inp;
  logic    r_fifo_full, r_fifo_empty;
  logic    r_fifo_push, r_fifo_pop;
  r_data_t r_fifo_data;
  // r counter
  logic    r_cnt_clear, r_cnt_en, r_cnt_load;
  axi_pkg::len_t r_current_beat;
  // r status
  logic    r_busy_n, r_busy_q, r_busy_load;

  //--------------------------------------
  // Atop Filter for atomics support
  //--------------------------------------
  axi_atop_filter #(
    .AXI_ID_WIDTH       ( AxiIdWidth ),
    .AXI_MAX_WRITE_TXNS ( MaxTrans   ),
    .req_t              ( req_t      ),
    .resp_t             ( resp_t     )
  ) i_atop_filter (
    .clk_i      ( clk_i       ),
    .rst_ni     ( rst_ni      ),
    .slv_req_i  ( slv_req_i   ),
    .slv_resp_o ( slv_resp_o  ),
    .mst_req_o  ( decerr_req  ),
    .mst_resp_i ( decerr_resp )
  );

  //--------------------------------------
  // Write Transactions
  //--------------------------------------
  always_comb begin : proc_aw_channel
    // default assignments
    decerr_resp.aw_ready = ~w_fifo_full;
    w_fifo_push          = 1'b0;
    // aw transaction
    if(decerr_req.aw_valid && !w_fifo_full) begin
      w_fifo_push    = 1'b1;
    end
  end

  fifo_v3 #(
    .FALL_THROUGH ( FallThrough ),
    .DEPTH        ( MaxTrans    ),
    .dtype        ( id_t         )
  ) i_w_fifo (
    .clk_i      ( clk_i             ),
    .rst_ni     ( rst_ni            ),
    .flush_i    ( 1'b0              ),
    .testmode_i ( test_i            ),
    .full_o     ( w_fifo_full       ),
    .empty_o    ( w_fifo_empty      ),
    .usage_o    (                   ),
    .data_i     ( decerr_req.aw.id  ),
    .push_i     ( w_fifo_push       ),
    .data_o     ( w_fifo_data       ),
    .pop_i      ( w_fifo_pop        )
  );

  always_comb begin : proc_w_channel
    decerr_resp.w_ready = 1'b0;
    w_fifo_pop          = 1'b0;
    b_fifo_push         = 1'b0;
    if (!w_fifo_empty && !b_fifo_full) begin
      // eat the beats
      decerr_resp.w_ready = 1'b1;
      // on the last w transaction
      if (decerr_req.w_valid && decerr_req.w.last) begin
        w_fifo_pop    = 1'b1;
        b_fifo_push   = 1'b1;
      end
    end
  end

  fifo_v3 #(
    .FALL_THROUGH ( FallThrough  ),
    .DEPTH        ( unsigned'(2) ), // two placed so that w can eat beats if b is not sent
    .dtype        ( id_t         )
  ) i_b_fifo (
    .clk_i      ( clk_i        ),
    .rst_ni     ( rst_ni       ),
    .flush_i    ( 1'b0         ),
    .testmode_i ( test_i       ),
    .full_o     ( b_fifo_full  ),
    .empty_o    ( b_fifo_empty ),
    .usage_o    (              ),
    .data_i     ( w_fifo_data  ),
    .push_i     ( b_fifo_push  ),
    .data_o     ( b_fifo_data  ),
    .pop_i      ( b_fifo_pop   )
  );

  always_comb begin : proc_b_channel
    b_fifo_pop          = 1'b0;
    decerr_resp.b       = '0;
    decerr_resp.b.id    = b_fifo_data;
    decerr_resp.b.resp  = axi_pkg::RESP_DECERR;
    decerr_resp.b_valid = 1'b0;
    if (!b_fifo_empty) begin
      decerr_resp.b_valid = 1'b1;
      // b transaction
      if (decerr_req.b_ready) begin
        b_fifo_pop = 1'b1;
      end
    end
  end

  //--------------------------------------
  // Read Transactions
  //--------------------------------------
  always_comb begin : proc_ar_channel
    decerr_resp.ar_ready = ~r_fifo_full;
    r_fifo_push          = 1'b0;
    // ar transaction
    if (decerr_req.ar_valid && !r_fifo_full) begin
      r_fifo_push = 1'b1;
    end
  end

  assign r_fifo_inp.id  = decerr_req.ar.id;
  assign r_fifo_inp.len = decerr_req.ar.len;

  fifo_v3 #(
    .FALL_THROUGH ( FallThrough ),
    .DEPTH        ( MaxTrans    ),
    .dtype        ( r_data_t    )
  ) i_r_fifo (
    .clk_i     ( clk_i        ),
    .rst_ni    ( rst_ni       ),
    .flush_i   ( 1'b0         ),
    .testmode_i( test_i       ),
    .full_o    ( r_fifo_full  ),
    .empty_o   ( r_fifo_empty ),
    .usage_o   (              ),
    .data_i    ( r_fifo_inp   ),
    .push_i    ( r_fifo_push  ),
    .data_o    ( r_fifo_data  ),
    .pop_i     ( r_fifo_pop   )
  );

  always_comb begin : proc_r_channel
    // default assignments
    r_busy_n    = r_busy_q;
    r_busy_load = 1'b0;
    // r fifo signals
    r_fifo_pop  = 1'b0;
    // r counter signals
    r_cnt_clear = 1'b0;
    r_cnt_en    = 1'b0;
    r_cnt_load  = 1'b0;
    // r_channel
    decerr_resp.r       = '0;
    decerr_resp.r.id    = r_fifo_data.id;
    decerr_resp.r.data  = 32'hBADCAB1E;
    decerr_resp.r.resp  = axi_pkg::RESP_DECERR;
    decerr_resp.r_valid = 1'b0;
    // control
    if (r_busy_q) begin
      decerr_resp.r_valid = 1'b1;
      if (r_current_beat == '0) begin
        decerr_resp.r.last = 1'b1;
      end
      // r transaction
      if (decerr_req.r_ready) begin
        r_cnt_en = 1'b1;
        if (r_current_beat == '0) begin
          r_busy_n    = 1'b0;
          r_busy_load = 1'b1;
          r_cnt_clear = 1'b1;
          r_fifo_pop  = 1'b1;
        end
      end
    end else begin
      // when not busy and fifo not empty, start counter decerr gen
      if (!r_fifo_empty) begin
        r_busy_n    = 1'b1;
        r_busy_load = 1'b1;
        r_cnt_load  = 1'b1;
      end
    end
  end

  always_ff @(posedge clk_i, negedge rst_ni) begin
    if (!rst_ni) begin
      r_busy_q <= '0;
    end else if (r_busy_load) begin
      r_busy_q <= r_busy_n;
    end
  end

  counter #(
    .WIDTH     ($bits(axi_pkg::len_t))
  ) i_r_counter (
    .clk_i     ( clk_i           ),
    .rst_ni    ( rst_ni          ),
    .clear_i   ( r_cnt_clear     ),
    .en_i      ( r_cnt_en        ),
    .load_i    ( r_cnt_load      ),
    .down_i    ( 1'b1            ),
    .d_i       ( r_fifo_data.len ),
    .q_o       ( r_current_beat  ),
    .overflow_o(                 )
  );
endmodule
