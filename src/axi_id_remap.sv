// Copyright (c) 2014-2019 ETH Zurich, University of Bologna
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
// Andreas Kurth <akurth@iis.ee.ethz.ch>
// Florian Zaruba <zarubaf@iis.ee.ethz.ch>
// Wolfgang Roenninger <wroennin@iis.ee.ethz.ch>

/// Remap AXI IDs.
module axi_id_remap #(
  parameter int unsigned ADDR_WIDTH   = 0,
  parameter int unsigned DATA_WIDTH   = 0,
  parameter int unsigned USER_WIDTH   = 0,
  parameter int unsigned ID_WIDTH_IN  = 0,
  parameter int unsigned ID_WIDTH_OUT = 0,
  parameter int unsigned TABLE_SIZE   = 0
) (
  input logic     clk_i,
  input logic     rst_ni,
  AXI_BUS.Slave   in,
  AXI_BUS.Master  out
);

  // Feed all signals that are not ID or flow control of AW and AR through.
  assign out.aw_addr    = in.aw_addr;
  assign out.aw_len     = in.aw_len;
  assign out.aw_size    = in.aw_size;
  assign out.aw_burst   = in.aw_burst;
  assign out.aw_lock    = in.aw_lock;
  assign out.aw_cache   = in.aw_cache;
  assign out.aw_prot    = in.aw_prot;
  assign out.aw_qos     = in.aw_qos;
  assign out.aw_region  = in.aw_region;
  assign out.aw_atop    = in.aw_atop;
  assign out.aw_user    = in.aw_user;

  assign out.ar_addr    = in.ar_addr;
  assign out.ar_len     = in.ar_len;
  assign out.ar_size    = in.ar_size;
  assign out.ar_burst   = in.ar_burst;
  assign out.ar_lock    = in.ar_lock;
  assign out.ar_cache   = in.ar_cache;
  assign out.ar_prot    = in.ar_prot;
  assign out.ar_qos     = in.ar_qos;
  assign out.ar_region  = in.ar_region;
  assign out.ar_user    = in.ar_user;

  assign out.w_data     = in.w_data;
  assign out.w_strb     = in.w_strb;
  assign out.w_last     = in.w_last;
  assign out.w_user     = in.w_user;
  assign out.w_valid    = in.w_valid;
  assign in.w_ready     = out.w_ready;

  assign in.r_data      = out.r_data;
  assign in.r_resp      = out.r_resp;
  assign in.r_last      = out.r_last;
  assign in.r_user      = out.r_user;
  assign in.r_valid     = out.r_valid;
  assign out.r_ready    = in.r_ready;

  assign in.b_resp      = out.b_resp;
  assign in.b_user      = out.b_user;
  assign in.b_valid     = out.b_valid;
  assign out.b_ready    = in.b_ready;

  // Remap tables keep track of in-flight bursts and their input and output IDs.
  typedef logic [TABLE_SIZE-1:0] field_t;
  typedef logic [ID_WIDTH_IN-1:0] id_inp_t;
  localparam int unsigned IDX_WIDTH = $clog2(TABLE_SIZE) > 0 ? $clog2(TABLE_SIZE) : 1;
  typedef logic [IDX_WIDTH-1:0] idx_t;
  field_t   wr_free,          rd_free,          both_free;
  id_inp_t                    rd_push_inp_id;
  idx_t     wr_free_oup_id,   rd_free_oup_id,   both_free_oup_id,
            wr_push_oup_id,   rd_push_oup_id,
            wr_exists_id,     rd_exists_id;
  logic     wr_exists,        rd_exists,
            wr_exists_full,   rd_exists_full,
            wr_full,          rd_full,
            wr_push,          rd_push;

  axi_id_remap_table #(
    .ID_WIDTH_INP ( ID_WIDTH_IN ),
    .MAX_TXNS     ( TABLE_SIZE  )
  ) i_wr_table (
    .clk_i,
    .rst_ni,
    .free_o           (wr_free),
    .free_oup_id_o    (wr_free_oup_id),
    .full_o           (wr_full),
    .push_inp_id_i    (in.aw_id),
    .push_oup_id_i    (wr_push_oup_id),
    .push_i           (wr_push),
    .exists_inp_id_i  (in.aw_id),
    .exists_oup_id_o  (wr_exists_id),
    .exists_full_o    (wr_exists_full),
    .exists_o         (wr_exists),
    .pop_oup_id_i     (out.b_id[IDX_WIDTH-1:0]),
    .pop_inp_id_o     (in.b_id),
    .pop_i            (in.b_valid && in.b_ready)
  );
  axi_id_remap_table #(
    .ID_WIDTH_INP ( ID_WIDTH_IN ),
    .MAX_TXNS     ( TABLE_SIZE  )
  ) i_rd_table (
    .clk_i,
    .rst_ni,
    .free_o           (rd_free),
    .free_oup_id_o    (rd_free_oup_id),
    .full_o           (rd_full),
    .push_inp_id_i    (rd_push_inp_id),
    .push_oup_id_i    (rd_push_oup_id),
    .push_i           (rd_push),
    .exists_inp_id_i  (in.ar_id),
    .exists_oup_id_o  (rd_exists_id),
    .exists_full_o    (rd_exists_full),
    .exists_o         (rd_exists),
    .pop_oup_id_i     (out.r_id[IDX_WIDTH-1:0]),
    .pop_inp_id_o     (in.r_id),
    .pop_i            (in.r_valid && in.r_ready && in.r_last)
  );
  assign both_free = wr_free & rd_free;
  lzc #(
    .WIDTH  (TABLE_SIZE),
    .MODE   (1'b0)
  ) i_lzc (
    .in_i     (both_free),
    .cnt_o    (both_free_oup_id),
    .empty_o  (/* unused */)
  );

  // Zero-extend output IDs if the output IDs is are wider than the IDs from the tables.
  localparam ZERO_WIDTH = ID_WIDTH_OUT - IDX_WIDTH;
  assign out.ar_id = {{ZERO_WIDTH{1'b0}}, rd_push_oup_id};
  assign out.aw_id = {{ZERO_WIDTH{1'b0}}, wr_push_oup_id};

  // Handle requests.
  enum logic [1:0] {Ready, HoldAR, HoldAW, HoldAx} state_d, state_q;
  idx_t ar_id_d, ar_id_q,
        aw_id_d, aw_id_q;
  always_comb begin
    out.aw_valid    = 1'b0;
    in.aw_ready     = 1'b0;
    wr_push         = 1'b0;
    wr_push_oup_id  =   'x;
    out.ar_valid    = 1'b0;
    in.ar_ready     = 1'b0;
    rd_push         = 1'b0;
    rd_push_inp_id  =   'x;
    rd_push_oup_id  =   'x;
    ar_id_d         = ar_id_q;
    aw_id_d         = aw_id_q;
    state_d         = state_q;

    unique case (state_q)
      Ready: begin
        // Reads
        if (in.ar_valid) begin
          // If a burst with the same input ID is already in flight or there are free output IDs:
          if ((rd_exists && !rd_exists_full) || (!rd_exists && !rd_full)) begin
            // Determine the output ID: if another in-flight burst had the same input ID, we must
            // reuse its output ID to maintain ordering; else, we assign the next free ID.
            rd_push_inp_id = in.ar_id;
            rd_push_oup_id = rd_exists ? rd_exists_id : rd_free_oup_id;
            // Forward the AR and push a new entry to the read table.
            out.ar_valid = 1'b1;
            rd_push = 1'b1;
          end
        end

        // Writes
        if (in.aw_valid) begin
          // If this is not an ATOP that gives rise to an R response, we can handle it in isolation
          // on the write direction.
          if (!in.aw_atop[5]) begin
            // If a burst with the same input ID is already in flight or there are free output IDs:
            if ((wr_exists && !wr_exists_full) || (!wr_exists && !wr_full)) begin
              // Determine the output ID: if another in-flight burst had the same input ID, we must
              // reuse its output ID to maintain ordering; else, we assign the next free ID.
              wr_push_oup_id = wr_exists ? wr_exists_id : wr_free_oup_id;
              // Forward the AW and push a new entry to the write table.
              out.aw_valid = 1'b1;
              wr_push = 1'b1;
            end
          // If this is an ATOP that gives rise to an R response, we must remap to an ID that is
          // free on both read and write direction and push also to the read table.
          end else begin
            // Nullify a potential AR at our output.  This is legal in this state.
            out.ar_valid = 1'b0;
            in.ar_ready = 1'b0;
            rd_push = 1'b0;
            if ((|both_free)) begin
              // Use an output ID that is free in both directions.
              wr_push_oup_id = both_free_oup_id;
              rd_push_inp_id = in.aw_id;
              rd_push_oup_id = both_free_oup_id;
              // Forward the AW and push a new entry to both tables.
              out.aw_valid = 1'b1;
              rd_push = 1'b1;
              wr_push = 1'b1;
            end
          end
        end

        // Hold AR, AW, or both if they are valid but not yet ready.
        if (out.ar_valid) begin
          in.ar_ready = out.ar_ready;
          if (!out.ar_ready) begin
            ar_id_d = rd_push_oup_id;
          end
        end
        if (out.aw_valid) begin
          in.aw_ready = out.aw_ready;
          if (!out.aw_ready) begin
            aw_id_d = wr_push_oup_id;
          end
        end
        priority casez ({out.ar_valid, out.ar_ready, out.aw_valid, out.aw_ready})
          4'b1010: state_d = HoldAx;
          4'b10??: state_d = HoldAR;
          4'b??10: state_d = HoldAW;
          default: state_d = Ready;
        endcase
      end

      HoldAR: begin
        // Drive out.ar_id through rd_push_oup_id.
        rd_push_oup_id = ar_id_q;
        out.ar_valid = 1'b1;
        in.ar_ready = out.ar_ready;
        if (out.ar_ready) begin
          state_d = Ready;
        end
      end

      HoldAW: begin
        // Drive out.aw_id through wr_push_oup_id.
        wr_push_oup_id = aw_id_q;
        out.aw_valid = 1'b1;
        in.aw_ready = out.aw_ready;
        if (out.aw_ready) begin
          state_d = Ready;
        end
      end

      HoldAx: begin
        rd_push_oup_id = ar_id_q;
        out.ar_valid = 1'b1;
        in.ar_ready = out.ar_ready;
        wr_push_oup_id = aw_id_q;
        out.aw_valid = 1'b1;
        in.aw_ready = out.aw_ready;
        unique0 case ({out.ar_ready, out.aw_ready})
          2'b01: state_d = HoldAR;
          2'b10: state_d = HoldAW;
          2'b11: state_d = Ready;
        endcase
      end

      default: state_d = Ready;
    endcase
  end

  // Registers
  always_ff @(posedge clk_i, negedge rst_ni) begin
    if (!rst_ni) begin
      ar_id_q <= '0;
      aw_id_q <= '0;
      state_q <= Ready;
    end else begin
      ar_id_q <= ar_id_d;
      aw_id_q <= aw_id_d;
      state_q <= state_d;
    end
  end

  // Assertions
  `ifndef TARGET_SYNTHESIS
    default disable iff (!rst_ni);
    assert property (@(posedge clk_i) in.aw_valid && in.aw_ready |-> out.aw_valid && out.aw_ready);
    assert property (@(posedge clk_i) out.b_valid && out.b_ready |-> in.b_valid && in.b_ready);
    assert property (@(posedge clk_i) in.ar_valid && in.ar_ready |-> out.ar_valid && out.ar_ready);
    assert property (@(posedge clk_i) out.r_valid && out.r_ready |-> in.r_valid && in.r_ready);
    assert property (@(posedge clk_i) in.r_valid |-> in.r_last == out.r_last);
    assert property (@(posedge clk_i)
        out.ar_valid && !out.ar_ready |=> out.ar_valid && $stable(out.ar_id));
    assert property (@(posedge clk_i)
        out.aw_valid && !out.aw_ready |=> out.aw_valid && $stable(out.aw_id));
    initial begin
      assert (ADDR_WIDTH > 0);
      assert (DATA_WIDTH > 0);
      assert (USER_WIDTH >= 0);
      assert (ID_WIDTH_IN > 0);
      assert (ID_WIDTH_OUT > 0);
      assert (ID_WIDTH_OUT < ID_WIDTH_IN);
      assert (TABLE_SIZE > 0);
      assert (ID_WIDTH_OUT >= IDX_WIDTH);
      // TODO: Allow ID_WIDTH_OUT to be smaller than IDX_WIDTH, i.e., to have multiple outstanding
      // transactions (limited by TABLE_SIZE) remapped to a few (extreme case: one) ID.  This is
      // possible because the restriction from unordered input transactions to ordered output
      // transactions is legal.
      assert (in.AXI_ADDR_WIDTH == ADDR_WIDTH);
      assert (in.AXI_DATA_WIDTH == DATA_WIDTH);
      assert (in.AXI_ID_WIDTH == ID_WIDTH_IN);
      assert (in.AXI_USER_WIDTH == USER_WIDTH);
      assert (out.AXI_ADDR_WIDTH == ADDR_WIDTH);
      assert (out.AXI_DATA_WIDTH == DATA_WIDTH);
      assert (out.AXI_ID_WIDTH == ID_WIDTH_OUT);
      assert (out.AXI_USER_WIDTH == USER_WIDTH);
    end
  `endif

endmodule


module axi_id_remap_table #(
  parameter int unsigned ID_WIDTH_INP = 0,
  // Maximum number of AXI read and write bursts outstanding at the same time
  parameter int unsigned MAX_TXNS = 0,
  // Derived Parameters (do NOT change manually!)
  localparam type field_t = logic [MAX_TXNS-1:0],
  localparam type id_inp_t = logic [ID_WIDTH_INP-1:0],
  localparam int unsigned IDX_WIDTH = $clog2(MAX_TXNS) > 0 ? $clog2(MAX_TXNS) : 1,
  localparam type idx_t = logic [IDX_WIDTH-1:0]
) (
  input  logic    clk_i,
  input  logic    rst_ni,

  output field_t  free_o,
  output idx_t    free_oup_id_o,
  output logic    full_o,

  input  id_inp_t push_inp_id_i,
  input  idx_t    push_oup_id_i,
  input  logic    push_i,

  input  id_inp_t exists_inp_id_i,
  output idx_t    exists_oup_id_o,
  output logic    exists_full_o,
  output logic    exists_o,

  input  idx_t    pop_oup_id_i,
  output id_inp_t pop_inp_id_o,
  input  logic    pop_i
);

  localparam int unsigned CNT_WIDTH = $clog2(MAX_TXNS+1);
  typedef logic [CNT_WIDTH-1:0] cnt_t;

  typedef struct packed {
    id_inp_t  inp_id;
    cnt_t     cnt;    // number of in-flight bursts with that ID
  } entry_t;

  // Table indexed by output IDs that contains the corresponding input IDs
  entry_t [MAX_TXNS-1:0] table_d, table_q;

  // Determine lowest free output ID.
  for (genvar i = 0; i < MAX_TXNS; i++) begin : gen_free_o
    assign free_o[i] = table_q[i].cnt == '0;
  end
  lzc #(
    .WIDTH    (MAX_TXNS),
    .MODE     (1'b0)
  ) i_lzc_free (
    .in_i     (free_o),
    .cnt_o    (free_oup_id_o),
    .empty_o  (full_o)
  );

  // Determine the input ID for a given output ID.
  assign pop_inp_id_o = table_q[pop_oup_id_i].inp_id;

  // Determine if given output ID is already used and, if it is, by which input ID.
  field_t match;
  for (genvar i = 0; i < MAX_TXNS; i++) begin : gen_match
    assign match[i] = table_q[i].cnt > 0 && table_q[i].inp_id == exists_inp_id_i;
  end
  logic no_match;
  lzc #(
      .WIDTH    (MAX_TXNS),
      .MODE     (1'b0)
  ) i_lzc_match (
      .in_i     (match),
      .cnt_o    (exists_oup_id_o),
      .empty_o  (no_match)
  );
  assign exists_o = ~no_match;
  assign exists_full_o = table_q[exists_oup_id_o].cnt == MAX_TXNS;

  // Push and pop table entries.
  always_comb begin
    table_d = table_q;
    if (push_i) begin
      table_d[push_oup_id_i].inp_id = push_inp_id_i;
      table_d[push_oup_id_i].cnt += 1;
    end
    if (pop_i) begin
      table_d[pop_oup_id_i].cnt -= 1;
    end
  end

  // Registers
  always_ff @(posedge clk_i, negedge rst_ni) begin
    if (!rst_ni) begin
      table_q <= '0;
    end else begin
      table_q <= table_d;
    end
  end

  // Assertions
  `ifndef TARGET_SYNTHESIS
    default disable iff (!rst_ni);
    assume property (@(posedge clk_i) push_i |->
        table_q[push_oup_id_i].cnt == '0 || table_q[push_oup_id_i].inp_id == push_inp_id_i)
      else $error("Push must be to empty output ID or match existing input ID!");
    assume property (@(posedge clk_i) push_i |-> table_q[push_oup_id_i].cnt < MAX_TXNS)
      else $error("Maximum number of in-flight bursts must not be exceeded!");
    assume property (@(posedge clk_i) pop_i |-> table_q[pop_oup_id_i].cnt > 0)
      else $error("Pop must target output ID with non-zero counter!");
    assume property (@(posedge clk_i) $onehot0(match))
      else $error("Input ID in table must be unique!");
    initial begin
      assert (ID_WIDTH_INP > 0);
      assert (MAX_TXNS > 0);
      assert (IDX_WIDTH >= 1);
    end
  `endif

endmodule
