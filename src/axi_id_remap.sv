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

module axi_id_remap #(
  /// Size of the remap table per channel
  parameter int unsigned TableSize     = 32'd0,
  /// AXI4+ATOP ID width of the slave port
  parameter int unsigned AxiIdWidthSlv = 32'd0,
  /// AXI4+ATOP request struct type of the slave port
  parameter type         slv_req_t     = logic,
  /// AXI4+ATOP response struct type of the slave port
  parameter type         slv_resp_t    = logic,
  /// AXI4+ATOP ID width of the master port
  parameter int unsigned AxiIdWidthMst = 32'd0,
  /// AXI4+ATOP request struct type of the master port
  parameter type         mst_req_t     = logic,
  /// AXI4+ATOP response struct type of the master port
  parameter type         mst_resp_t    = logic
) (
  /// Clock Input
  input  logic      clk_i,
  /// Asynchronous reset active low
  input  logic      rst_ni,
  /// Slave port request
  input  slv_req_t  slv_req_i,
  /// Slave port response
  output slv_resp_t slv_resp_o,
  /// Master port request
  output mst_req_t  mst_req_o,
  /// Master port response
  input  mst_resp_t mst_resp_i
);

  // Feed all signals that are not ID or flow control of AW and AR through.
  assign mst_req_o.aw.addr   = slv_req_i.aw.addr;
  assign mst_req_o.aw.len    = slv_req_i.aw.len;
  assign mst_req_o.aw.size   = slv_req_i.aw.size;
  assign mst_req_o.aw.burst  = slv_req_i.aw.burst;
  assign mst_req_o.aw.lock   = slv_req_i.aw.lock;
  assign mst_req_o.aw.cache  = slv_req_i.aw.cache;
  assign mst_req_o.aw.prot   = slv_req_i.aw.prot;
  assign mst_req_o.aw.qos    = slv_req_i.aw.qos;
  assign mst_req_o.aw.region = slv_req_i.aw.region;
  assign mst_req_o.aw.atop   = slv_req_i.aw.atop;
  assign mst_req_o.aw.user   = slv_req_i.aw.user;

  assign mst_req_o.w         = slv_req_i.w;
  assign mst_req_o.w_valid   = slv_req_i.w_valid;
  assign slv_resp_o.w_ready  = mst_resp_i.w_ready;

  assign slv_resp_o.b.resp   = mst_resp_i.b.resp;
  assign slv_resp_o.b.user   = mst_resp_i.b.user;
  assign slv_resp_o.b_valid  = mst_resp_i.b_valid;
  assign mst_req_o.b_ready   = slv_req_i.b_ready;

  assign mst_req_o.ar.addr   = slv_req_i.ar.addr;
  assign mst_req_o.ar.len    = slv_req_i.ar.len;
  assign mst_req_o.ar.size   = slv_req_i.ar.size;
  assign mst_req_o.ar.burst  = slv_req_i.ar.burst;
  assign mst_req_o.ar.lock   = slv_req_i.ar.lock;
  assign mst_req_o.ar.cache  = slv_req_i.ar.cache;
  assign mst_req_o.ar.prot   = slv_req_i.ar.prot;
  assign mst_req_o.ar.qos    = slv_req_i.ar.qos;
  assign mst_req_o.ar.region = slv_req_i.ar.region;
  assign mst_req_o.ar.user   = slv_req_i.ar.user;

  assign slv_resp_o.r.data   = mst_resp_i.r.data;
  assign slv_resp_o.r.resp   = mst_resp_i.r.resp;
  assign slv_resp_o.r.last   = mst_resp_i.r.last;
  assign slv_resp_o.r.user   = mst_resp_i.r.user;
  assign slv_resp_o.r_valid  = mst_resp_i.r_valid;
  assign mst_req_o.r_ready   = slv_req_i.r_ready;


  // Remap tables keep track of in-flight bursts and their input and output IDs.
  localparam int unsigned IdxWidth = $clog2(TableSize) > 0 ? $clog2(TableSize) : 1;
  typedef logic [TableSize-1:0]     field_t;
  typedef logic [AxiIdWidthSlv-1:0] id_inp_t;
  typedef logic [IdxWidth-1:0]      idx_t;
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
    .IdWidthInp ( AxiIdWidthSlv ),
    .MaxTxns    ( TableSize     )
  ) i_wr_table (
    .clk_i,
    .rst_ni,
    .free_o          ( wr_free                                 ),
    .free_oup_id_o   ( wr_free_oup_id                          ),
    .full_o          ( wr_full                                 ),
    .push_inp_id_i   ( slv_req_i.aw.id                         ),
    .push_oup_id_i   ( wr_push_oup_id                          ),
    .push_i          ( wr_push                                 ),
    .exists_inp_id_i ( slv_req_i.aw.id                         ),
    .exists_oup_id_o ( wr_exists_id                            ),
    .exists_full_o   ( wr_exists_full                          ),
    .exists_o        ( wr_exists                               ),
    .pop_oup_id_i    ( mst_resp_i.b.id[IdxWidth-1:0]           ), // TODO, check!!
    .pop_inp_id_o    ( slv_resp_o.b.id                         ),
    .pop_i           ( slv_resp_o.b_valid && slv_req_i.b_ready )
  );
  axi_id_remap_table #(
    .IdWidthInp ( AxiIdWidthSlv ),
    .MaxTxns    ( TableSize     )
  ) i_rd_table (
    .clk_i,
    .rst_ni,
    .free_o           ( rd_free                                                      ),
    .free_oup_id_o    ( rd_free_oup_id                                               ),
    .full_o           ( rd_full                                                      ),
    .push_inp_id_i    ( rd_push_inp_id                                               ),
    .push_oup_id_i    ( rd_push_oup_id                                               ),
    .push_i           ( rd_push                                                      ),
    .exists_inp_id_i  ( slv_req_i.ar.id                                              ),
    .exists_oup_id_o  ( rd_exists_id                                                 ),
    .exists_full_o    ( rd_exists_full                                               ),
    .exists_o         ( rd_exists                                                    ),
    .pop_oup_id_i     ( mst_resp_i.r.id[IdxWidth-1:0]                                ), // TODO, check!!
    .pop_inp_id_o     ( slv_resp_o.r.id                                              ),
    .pop_i            ( slv_resp_o.r_valid && slv_req_i.r_ready && slv_resp_o.r.last )
  );
  assign both_free = wr_free & rd_free;
  lzc #(
    .WIDTH  ( TableSize ),
    .MODE   ( 1'b0      )
  ) i_lzc (
    .in_i     ( both_free        ),
    .cnt_o    ( both_free_oup_id ),
    .empty_o  ( /* unused */     )
  );

  // Zero-extend output IDs if the output IDs is are wider than the IDs from the tables.
  localparam ZeroWidth = AxiIdWidthMst - IdxWidth;
  assign mst_req_o.ar.id = {{ZeroWidth{1'b0}}, rd_push_oup_id};
  assign mst_req_o.aw.id = {{ZeroWidth{1'b0}}, wr_push_oup_id};

  // Handle requests.
  enum logic [1:0] {Ready, HoldAR, HoldAW, HoldAx} state_d, state_q;
  idx_t ar_id_d, ar_id_q,
        aw_id_d, aw_id_q;
  always_comb begin
    mst_req_o.aw_valid  = 1'b0;
    slv_resp_o.aw_ready = 1'b0;
    wr_push             = 1'b0;
    wr_push_oup_id      =   'x;
    mst_req_o.ar_valid  = 1'b0;
    slv_resp_o.ar_ready = 1'b0;
    rd_push             = 1'b0;
    rd_push_inp_id      =   'x;
    rd_push_oup_id      =   'x;
    ar_id_d             = ar_id_q;
    aw_id_d             = aw_id_q;
    state_d             = state_q;

    unique case (state_q)
      Ready: begin
        // Reads
        if (slv_req_i.ar_valid) begin
          // If a burst with the same input ID is already in flight or there are free output IDs:
          if ((rd_exists && !rd_exists_full) || (!rd_exists && !rd_full)) begin
            // Determine the output ID: if another in-flight burst had the same input ID, we must
            // reuse its output ID to maintain ordering; else, we assign the next free ID.
            rd_push_inp_id     = slv_req_i.ar.id;
            rd_push_oup_id     = rd_exists ? rd_exists_id : rd_free_oup_id;
            // Forward the AR and push a new entry to the read table.
            mst_req_o.ar_valid = 1'b1;
            rd_push            = 1'b1;
          end
        end

        // Writes
        if (slv_req_i.aw_valid) begin
          // If this is not an ATOP that gives rise to an R response, we can handle it in isolation
          // on the write direction.
          if (!slv_req_i.aw.atop[5]) begin
            // If a burst with the same input ID is already in flight or there are free output IDs:
            if ((wr_exists && !wr_exists_full) || (!wr_exists && !wr_full)) begin
              // Determine the output ID: if another in-flight burst had the same input ID, we must
              // reuse its output ID to maintain ordering; else, we assign the next free ID.
              wr_push_oup_id     = wr_exists ? wr_exists_id : wr_free_oup_id;
              // Forward the AW and push a new entry to the write table.
              mst_req_o.aw_valid = 1'b1;
              wr_push            = 1'b1;
            end
          // If this is an ATOP that gives rise to an R response, we must remap to an ID that is
          // free on both read and write direction and push also to the read table.
          end else begin
            // Nullify a potential AR at our output.  This is legal in this state.
            mst_req_o.ar_valid  = 1'b0;
            slv_resp_o.ar_ready = 1'b0;
            rd_push             = 1'b0;
            if ((|both_free)) begin
              // Use an output ID that is free in both directions.
              wr_push_oup_id = both_free_oup_id;
              rd_push_inp_id = slv_req_i.aw.id;
              rd_push_oup_id = both_free_oup_id;
              // Forward the AW and push a new entry to both tables.
              mst_req_o.aw_valid = 1'b1;
              rd_push            = 1'b1;
              wr_push            = 1'b1;
            end
          end
        end

        // Hold AR, AW, or both if they are valid but not yet ready.
        if (mst_req_o.ar_valid) begin
          slv_resp_o.ar_ready = mst_resp_i.ar_ready;
          if (!mst_resp_i.ar_ready) begin
            ar_id_d = rd_push_oup_id;
          end
        end
        if (mst_req_o.aw_valid) begin
          slv_resp_o.aw_ready = mst_resp_i.aw_ready;
          if (!mst_resp_i.aw_ready) begin
            aw_id_d = wr_push_oup_id;
          end
        end
        priority casez ({mst_req_o.ar_valid, mst_resp_i.ar_ready,
                         mst_req_o.aw_valid, mst_resp_i.aw_ready})
          4'b1010: state_d = HoldAx;
          4'b10??: state_d = HoldAR;
          4'b??10: state_d = HoldAW;
          default: state_d = Ready;
        endcase
      end

      HoldAR: begin
        // Drive `mst_req_o.ar.id` through rd_push_oup_id.
        rd_push_oup_id      = ar_id_q;
        mst_req_o.ar_valid  = 1'b1;
        slv_resp_o.ar_ready = mst_resp_i.ar_ready;
        if (mst_resp_i.ar_ready) begin
          state_d = Ready;
        end
      end

      HoldAW: begin
        // Drive mst_req_o.aw.id through wr_push_oup_id.
        wr_push_oup_id      = aw_id_q;
        mst_req_o.aw_valid  = 1'b1;
        slv_resp_o.aw_ready = mst_resp_i.aw_ready;
        if (mst_resp_i.aw_ready) begin
          state_d = Ready;
        end
      end

      HoldAx: begin
        rd_push_oup_id      = ar_id_q;
        mst_req_o.ar_valid  = 1'b1;
        slv_resp_o.ar_ready = mst_resp_i.ar_ready;
        wr_push_oup_id      = aw_id_q;
        mst_req_o.aw_valid  = 1'b1;
        slv_resp_o.aw_ready = mst_resp_i.aw_ready;
        unique0 case ({mst_resp_i.ar_ready, mst_resp_i.aw_ready})
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

  // pragma translate_off
  `ifndef VERILATOR
  initial begin : p_assert
    assert(AxiIdWidthSlv > 32'd0)
      else $fatal(1, "Parameter AxiIdWidthSlv has to be larger than 0!");
    assert(AxiIdWidthMst > 32'd0)
      else $fatal(1, "Parameter AxiIdWidthMst has to be larger than 0!");
    assert($bits(slv_req_i.aw.addr) == $bits(mst_req_o.aw.addr))
      else $fatal(1, "AXI AW address widths are not equal!");
    assert($bits(slv_req_i.w.data) == $bits(mst_req_o.w.data))
      else $fatal(1, "AXI W data widths are not equal!");
    assert($bits(slv_req_i.ar.addr) == $bits(mst_req_o.ar.addr))
      else $fatal(1, "AXI AR address widths are not equal!");
    assert($bits(slv_resp_o.r.data) == $bits(mst_resp_i.r.data))
      else $fatal(1, "AXI R data widths are not equal!");
  end
  `endif
  `ifndef TARGET_SYNTHESIS
    default disable iff (!rst_ni);
    assert property (@(posedge clk_i) slv_req_i.aw_valid && slv_resp_o.aw_ready
        |-> mst_req_o.aw_valid && mst_resp_i.aw_ready);
    assert property (@(posedge clk_i) mst_resp_i.b_valid && mst_req_o.b_ready
        |-> slv_resp_o.b_valid && slv_req_i.b_ready);
    assert property (@(posedge clk_i) slv_req_i.ar_valid && slv_resp_o.ar_ready
        |-> mst_req_o.ar_valid && mst_resp_i.ar_ready);
    assert property (@(posedge clk_i) mst_resp_i.r_valid && mst_req_o.r_ready
        |-> slv_resp_o.r_valid && slv_req_i.r_ready);
    assert property (@(posedge clk_i) slv_resp_o.r_valid
        |-> slv_resp_o.r.last == mst_resp_i.r.last);
    assert property (@(posedge clk_i) mst_req_o.ar_valid && !mst_resp_i.ar_ready
        |=> mst_req_o.ar_valid && $stable(mst_req_o.ar.id));
    assert property (@(posedge clk_i) mst_req_o.aw_valid && !mst_resp_i.aw_ready
        |=> mst_req_o.aw_valid && $stable(mst_req_o.aw.id));
    initial begin
      assert (AxiIdWidthSlv > 0);
      assert (AxiIdWidthMst > 0);
      assert (AxiIdWidthMst < AxiIdWidthSlv);
      assert (TableSize > 0);
      assert (AxiIdWidthMst >= IdxWidth);
      // TODO: Allow AxiIdWidthMst to be smaller than IdxWidth, i.e., to have multiple outstanding
      // transactions (limited by TableSize) remapped to a few (extreme case: one) ID.  This is
      // possible because the restriction from unordered input transactions to ordered output
      // transactions is legal.
      assert ($bits(slv_req_i.aw.id) == AxiIdWidthSlv);
      assert ($bits(slv_resp_o.b.id) == AxiIdWidthSlv);
      assert ($bits(slv_req_i.ar.id) == AxiIdWidthSlv);
      assert ($bits(slv_resp_o.r.id) == AxiIdWidthSlv);
      assert ($bits(mst_req_o.aw.id) == AxiIdWidthMst);
      assert ($bits(mst_resp_i.b.id) == AxiIdWidthMst);
      assert ($bits(mst_req_o.ar.id) == AxiIdWidthMst);
      assert ($bits(mst_resp_i.r.id) == AxiIdWidthMst);
    end
  `endif
  // pragma translate_on
endmodule

/// Implements ID remap tables
module axi_id_remap_table #(
  parameter int unsigned IdWidthInp = 32'd0,
  // Maximum number of AXI read and write bursts outstanding at the same time
  parameter int unsigned MaxTxns    = 32'd0,
  // Derived Parameters (do NOT change manually!)
  localparam type field_t           = logic [MaxTxns-1:0],
  localparam type id_inp_t          = logic [IdWidthInp-1:0],
  localparam int unsigned IdxWidth  = $clog2(MaxTxns) > 0 ? $clog2(MaxTxns) : 1,
  localparam type idx_t             = logic [IdxWidth-1:0]
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

  localparam int unsigned CntWidth = $clog2(MaxTxns+1);
  typedef logic [CntWidth-1:0] cnt_t;

  typedef struct packed {
    id_inp_t  inp_id;
    cnt_t     cnt;    // number of in-flight bursts with that ID
  } entry_t;

  // Table indexed by output IDs that contains the corresponding input IDs
  entry_t [MaxTxns-1:0] table_d, table_q;

  // Determine lowest free output ID.
  for (genvar i = 0; i < MaxTxns; i++) begin : gen_free_o
    assign free_o[i] = table_q[i].cnt == '0;
  end
  lzc #(
    .WIDTH ( MaxTxns ),
    .MODE  ( 1'b0    )
  ) i_lzc_free (
    .in_i    ( free_o        ),
    .cnt_o   ( free_oup_id_o ),
    .empty_o ( full_o        )
  );

  // Determine the input ID for a given output ID.
  assign pop_inp_id_o = table_q[pop_oup_id_i].inp_id;

  // Determine if given output ID is already used and, if it is, by which input ID.
  field_t match;
  for (genvar i = 0; i < MaxTxns; i++) begin : gen_match
    assign match[i] = table_q[i].cnt > 0 && table_q[i].inp_id == exists_inp_id_i;
  end
  logic no_match;
  lzc #(
      .WIDTH ( MaxTxns ),
      .MODE  ( 1'b0    )
  ) i_lzc_match (
      .in_i     ( match           ),
      .cnt_o    ( exists_oup_id_o ),
      .empty_o  ( no_match        )
  );
  assign exists_o      = ~no_match;
  assign exists_full_o = table_q[exists_oup_id_o].cnt == MaxTxns;

  // Push and pop table entries.
  always_comb begin
    table_d = table_q;
    if (push_i) begin
      table_d[push_oup_id_i].inp_id  = push_inp_id_i;
      table_d[push_oup_id_i].cnt    += 1;
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
    assume property (@(posedge clk_i) push_i |-> table_q[push_oup_id_i].cnt < MaxTxns)
      else $error("Maximum number of in-flight bursts must not be exceeded!");
    assume property (@(posedge clk_i) pop_i |-> table_q[pop_oup_id_i].cnt > 0)
      else $error("Pop must target output ID with non-zero counter!");
    assume property (@(posedge clk_i) $onehot0(match))
      else $error("Input ID in table must be unique!");
    initial begin
      assert (IdWidthInp > 0);
      assert (MaxTxns > 0);
      assert (IdxWidth >= 1);
    end
  `endif

endmodule

`include "axi/typedef.svh"
`include "axi/assign.svh"
module axi_id_remap_intf #(
  /// Size of the remap table per channel
  parameter int unsigned TABLE_SIZE       = 32'd0,
  /// ID width of the AXI4+ATOP slave port
  parameter int unsigned AXI_ID_WIDTH_SLV = 32'd0,
  /// ID width of the AXI4+ATOP master port
  parameter int unsigned AXI_ID_WIDTH_MST = 32'd0,
  /// Address width of both AXI4+ATOP ports
  parameter int unsigned AXI_ADDR_WIDTH   = 32'd0,
  /// Data width of both AXI4+ATOP ports
  parameter int unsigned AXI_DATA_WIDTH   = 32'd0,
  /// User width of both AXI4+ATOP ports
  parameter int unsigned AXI_USER_WIDTH   = 32'd0
) (
  input logic     clk_i,
  input logic     rst_ni,
  AXI_BUS.Slave   slv,
  AXI_BUS.Master  mst
);
  typedef logic [AXI_ID_WIDTH_SLV-1:0] slv_id_t;
  typedef logic [AXI_ID_WIDTH_MST-1:0] mst_id_t;
  typedef logic [AXI_ADDR_WIDTH-1:0]   axi_addr_t;
  typedef logic [AXI_DATA_WIDTH-1:0]   axi_data_t;
  typedef logic [AXI_DATA_WIDTH/8-1:0] axi_strb_t;
  typedef logic [AXI_USER_WIDTH-1:0]   axi_user_t;

  `AXI_TYPEDEF_AW_CHAN_T(slv_aw_chan_t, axi_addr_t, slv_id_t, axi_user_t)
  `AXI_TYPEDEF_W_CHAN_T(slv_w_chan_t, axi_data_t, axi_strb_t, axi_user_t)
  `AXI_TYPEDEF_B_CHAN_T(slv_b_chan_t, slv_id_t, axi_user_t)
  `AXI_TYPEDEF_AR_CHAN_T(slv_ar_chan_t, axi_addr_t, slv_id_t, axi_user_t)
  `AXI_TYPEDEF_R_CHAN_T(slv_r_chan_t, axi_data_t, slv_id_t, axi_user_t)
  `AXI_TYPEDEF_REQ_T(slv_req_t, slv_aw_chan_t, slv_w_chan_t, slv_ar_chan_t)
  `AXI_TYPEDEF_RESP_T(slv_resp_t, slv_b_chan_t, slv_r_chan_t)

  `AXI_TYPEDEF_AW_CHAN_T(mst_aw_chan_t, axi_addr_t, mst_id_t, axi_user_t)
  `AXI_TYPEDEF_W_CHAN_T(mst_w_chan_t, axi_data_t, axi_strb_t, axi_user_t)
  `AXI_TYPEDEF_B_CHAN_T(mst_b_chan_t, mst_id_t, axi_user_t)
  `AXI_TYPEDEF_AR_CHAN_T(mst_ar_chan_t, axi_addr_t, mst_id_t, axi_user_t)
  `AXI_TYPEDEF_R_CHAN_T(mst_r_chan_t, axi_data_t, mst_id_t, axi_user_t)
  `AXI_TYPEDEF_REQ_T(mst_req_t, mst_aw_chan_t, mst_w_chan_t, mst_ar_chan_t)
  `AXI_TYPEDEF_RESP_T(mst_resp_t, mst_b_chan_t, mst_r_chan_t)

  slv_req_t  slv_req;
  slv_resp_t slv_resp;
  mst_req_t  mst_req;
  mst_resp_t mst_resp;

  `AXI_ASSIGN_TO_REQ(slv_req, slv)
  `AXI_ASSIGN_FROM_RESP(slv, slv_resp)
  `AXI_ASSIGN_FROM_REQ(mst, mst_req)
  `AXI_ASSIGN_TO_RESP(mst_resp, mst)

  axi_id_remap #(
    .TableSize     ( TABLE_SIZE       ),
    .AxiIdWidthSlv ( AXI_ID_WIDTH_SLV ),
    .slv_req_t     ( slv_req_t        ),
    .slv_resp_t    ( slv_resp_t       ),
    .AxiIdWidthMst ( AXI_ID_WIDTH_MST ),
    .mst_req_t     ( mst_req_t        ),
    .mst_resp_t    ( mst_resp_t       )
  ) i_axi_id_remap (
    .clk_i,
    .rst_ni,
    .slv_req_i  ( slv_req  ),
    .slv_resp_o ( slv_resp ),
    .mst_req_o  ( mst_req  ),
    .mst_resp_i ( mst_resp )
  );
  // pragma translate_off
  `ifndef VERILATOR
    initial begin
      assert (slv.AXI_ID_WIDTH   == AXI_ID_WIDTH_SLV);
      assert (slv.AXI_ADDR_WIDTH == AXI_ADDR_WIDTH);
      assert (slv.AXI_DATA_WIDTH == AXI_DATA_WIDTH);
      assert (slv.AXI_USER_WIDTH == AXI_USER_WIDTH);
      assert (mst.AXI_ID_WIDTH   == AXI_ID_WIDTH_MST);
      assert (mst.AXI_ADDR_WIDTH == AXI_ADDR_WIDTH);
      assert (mst.AXI_DATA_WIDTH == AXI_DATA_WIDTH);
      assert (mst.AXI_USER_WIDTH == AXI_USER_WIDTH);
    end
  `endif
  // pragma translate_on
endmodule
