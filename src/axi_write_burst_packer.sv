// Copyright 2019 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

import axi_pkg::*;

// Buffer AXI write bursts (AW and W channel) and release them as immediately consecutive beats.
// As W bursts cannot be interleaved, this module is designed to maximize the utilization of the
// downstream W channel (connected to the `mst` port of this module) by packing write bursts.
module axi_write_burst_packer #(
  parameter int unsigned ADDR_WIDTH = 0,  // [bit]
  parameter int unsigned DATA_WIDTH = 0,  // [bit]
  parameter int unsigned ID_WIDTH = 0,    // [bit]
  parameter int unsigned USER_WIDTH = 0,  // [bit]
  parameter int unsigned BUF_DEPTH = 0,   // max. number of beats in buffer before burst is started
  // Dependent parameters, do not change!
  localparam type addr_t = logic[ADDR_WIDTH-1:0],
  localparam type data_t = logic[DATA_WIDTH-1:0],
  localparam type strb_t = logic[DATA_WIDTH/8-1:0],
  localparam type id_t = logic[ID_WIDTH-1:0],
  localparam type user_t = logic[USER_WIDTH-1:0]
) (
  input  logic      clk_i,
  input  logic      rst_ni,

  // Slave Ports
  input  id_t       slv_aw_id,
  input  addr_t     slv_aw_addr,
  input  len_t      slv_aw_len,
  input  size_t     slv_aw_size,
  input  burst_t    slv_aw_burst,
  input  logic      slv_aw_lock,
  input  cache_t    slv_aw_cache,
  input  prot_t     slv_aw_prot,
  input  qos_t      slv_aw_qos,
  input  region_t   slv_aw_region,
  input  atop_t     slv_aw_atop,
  input  user_t     slv_aw_user,
  input  logic      slv_aw_valid,
  output logic      slv_aw_ready,
  input  data_t     slv_w_data,
  input  strb_t     slv_w_strb,
  input  logic      slv_w_last,
  input  user_t     slv_w_user,
  input  logic      slv_w_valid,
  output logic      slv_w_ready,
  output id_t       slv_b_id,
  output resp_t     slv_b_resp,
  output user_t     slv_b_user,
  output logic      slv_b_valid,
  input  logic      slv_b_ready,
  input  id_t       slv_ar_id,
  input  addr_t     slv_ar_addr,
  input  len_t      slv_ar_len,
  input  size_t     slv_ar_size,
  input  burst_t    slv_ar_burst,
  input  logic      slv_ar_lock,
  input  cache_t    slv_ar_cache,
  input  prot_t     slv_ar_prot,
  input  qos_t      slv_ar_qos,
  input  region_t   slv_ar_region,
  input  user_t     slv_ar_user,
  input  logic      slv_ar_valid,
  output logic      slv_ar_ready,
  output id_t       slv_r_id,
  output data_t     slv_r_data,
  output resp_t     slv_r_resp,
  output logic      slv_r_last,
  output user_t     slv_r_user,
  output logic      slv_r_valid,
  input  logic      slv_r_ready,

  // Master Ports
  output id_t       mst_aw_id,
  output addr_t     mst_aw_addr,
  output len_t      mst_aw_len,
  output size_t     mst_aw_size,
  output burst_t    mst_aw_burst,
  output logic      mst_aw_lock,
  output cache_t    mst_aw_cache,
  output prot_t     mst_aw_prot,
  output qos_t      mst_aw_qos,
  output region_t   mst_aw_region,
  output atop_t     mst_aw_atop,
  output user_t     mst_aw_user,
  output logic      mst_aw_valid,
  input  logic      mst_aw_ready,
  output data_t     mst_w_data,
  output strb_t     mst_w_strb,
  output logic      mst_w_last,
  output user_t     mst_w_user,
  output logic      mst_w_valid,
  input  logic      mst_w_ready,
  input  id_t       mst_b_id,
  input  resp_t     mst_b_resp,
  input  user_t     mst_b_user,
  input  logic      mst_b_valid,
  output logic      mst_b_ready,
  output id_t       mst_ar_id,
  output addr_t     mst_ar_addr,
  output len_t      mst_ar_len,
  output size_t     mst_ar_size,
  output burst_t    mst_ar_burst,
  output logic      mst_ar_lock,
  output cache_t    mst_ar_cache,
  output prot_t     mst_ar_prot,
  output qos_t      mst_ar_qos,
  output region_t   mst_ar_region,
  output user_t     mst_ar_user,
  output logic      mst_ar_valid,
  input  logic      mst_ar_ready,
  input  id_t       mst_r_id,
  input  data_t     mst_r_data,
  input  resp_t     mst_r_resp,
  input  logic      mst_r_last,
  input  user_t     mst_r_user,
  input  logic      mst_r_valid,
  output logic      mst_r_ready
);

  typedef logic [$clog2(BUF_DEPTH)-1:0] buf_idx_t;
  typedef enum logic [1:0] { Hold, Drain, Single } state_e;

  typedef struct packed {
    id_t      id;
    addr_t    addr;
    len_t     len;
    size_t    size;
    burst_t   burst;
    logic     lock;
    cache_t   cache;
    prot_t    prot;
    qos_t     qos;
    region_t  region;
    atop_t    atop;
    user_t    user;
  } aw_chan_t;

  typedef struct packed {
    data_t  data;
    strb_t  strb;
    user_t  user;
    logic   last;
  } w_chan_t;

  buf_idx_t   aw_pend_d,    aw_pend_q,
              w_compl_d,    w_compl_q;
  state_e     state_d,      state_q;
  logic       aw_pend_inc,  aw_pend_dec, aw_reg_valid,
              w_buf_full,   w_buf_empty;

  // Pack W beats in FIFO.
  fifo_v3 #(
    .FALL_THROUGH (1'b1),
    .DATA_WIDTH   ($bits(w_chan_t)),
    .DEPTH        (BUF_DEPTH),
    .dtype        (w_chan_t)
  ) i_w_buf (
    .clk_i,
    .rst_ni,
    .flush_i    (1'b0),
    .testmode_i (1'b0),
    .full_o     (w_buf_full),
    .empty_o    (w_buf_empty),
    .usage_o    (),
    .data_i     ({slv_w_data, slv_w_strb, slv_w_user, slv_w_last}),
    .push_i     (slv_w_valid & slv_w_ready),
    .data_o     ({mst_w_data, mst_w_strb, mst_w_user, mst_w_last}),
    .pop_i      (mst_w_valid & mst_w_ready)
  );

  // Track number of complete bursts in FIFO.
  always_comb begin
    w_compl_d = w_compl_q;
    if (slv_w_valid && slv_w_ready && slv_w_last) w_compl_d++;
    if (mst_w_valid && mst_w_ready && mst_w_last) w_compl_d--;
  end

  // Control forwarding of W beats and increment pending AW beats.
  always_comb begin
    aw_pend_inc = 1'b0;
    mst_w_valid = 1'b0;
    state_d = state_q;

    unique case (state_q)
      Hold: begin
        // If there is a single-beat burst in the FIFO, send it.
        if (!w_buf_empty && mst_w_last) begin
          aw_pend_inc = 1'b1;
          mst_w_valid = 1'b1;
          if (!mst_w_ready) begin
            state_d = Single;
          end
        // Otherwise, if the FIFO is full or if there is at least one complete multi-beat burst in
        // the FIFO, drain the FIFO.
        end else if (w_buf_full || (!w_buf_empty && w_compl_d > 0)) begin
          mst_w_valid = 1'b1;
          aw_pend_inc = 1'b1;
          state_d = Drain;
        end
      end
      Drain: begin
        // Drain the FIFO until the next `last` beat has been sent.
        mst_w_valid = ~w_buf_empty;
        if (mst_w_valid && mst_w_ready && mst_w_last) begin
          if (w_compl_d == '0) begin
            // The next burst is not complete yet, go back to hold.
            state_d = Hold;
          end else begin
            // There are more complete bursts in the FIFO, continue draining.
            aw_pend_inc = 1'b1;
          end
        end
      end
      Single: begin
        // Finish sending the single beat.
        mst_w_valid = 1'b1;
        if (mst_w_ready) begin
          state_d = Hold;
        end
      end
      default: state_d = Hold;
    endcase
  end

  // Accept new W beats until the FIFO is full.
  assign slv_w_ready = ~w_buf_full;

  // Register AW beat.
  fall_through_register #(
    .T  (aw_chan_t)
  ) i_aw_reg (
    .clk_i,
    .rst_ni,
    .clr_i      (),
    .testmode_i (),
    .valid_i    (slv_aw_valid),
    .ready_o    (slv_aw_ready),
    .data_i     ({slv_aw_id, slv_aw_addr, slv_aw_len, slv_aw_size, slv_aw_burst, slv_aw_lock,
                  slv_aw_cache, slv_aw_prot, slv_aw_qos, slv_aw_region, slv_aw_atop, slv_aw_user}),
    .valid_o    (aw_reg_valid),
    .ready_i    (mst_aw_valid & mst_aw_ready),
    .data_o     ({mst_aw_id, mst_aw_addr, mst_aw_len, mst_aw_size, mst_aw_burst, mst_aw_lock,
                  mst_aw_cache, mst_aw_prot, mst_aw_qos, mst_aw_region, mst_aw_atop, mst_aw_user})
  );

  // Track the number of AW beats that are pending, i.e., that may be sent.
  always_comb begin
    aw_pend_d = aw_pend_q;
    if (aw_pend_inc) aw_pend_d++;
    if (aw_pend_dec) aw_pend_d--;
  end

  // Control forwarding of AW beats.
  assign mst_aw_valid = aw_reg_valid & (aw_pend_q > 0 | (state_q == Hold & state_d == Drain));
  assign aw_pend_dec = mst_aw_valid & mst_aw_ready;

  always_ff @(posedge clk_i, negedge rst_ni) begin
    if (!rst_ni) begin
      aw_pend_q <= '0;
      state_q   <= Hold;
      w_compl_q <= '0;
    end else begin
      aw_pend_q <= aw_pend_d;
      state_q   <= state_d;
      w_compl_q <= w_compl_d;
    end
  end

  // Feed AR, R, and B channels through.
  assign mst_ar_id      = slv_ar_id;
  assign mst_ar_addr    = slv_ar_addr;
  assign mst_ar_len     = slv_ar_len;
  assign mst_ar_size    = slv_ar_size;
  assign mst_ar_burst   = slv_ar_burst;
  assign mst_ar_lock    = slv_ar_lock;
  assign mst_ar_cache   = slv_ar_cache;
  assign mst_ar_prot    = slv_ar_prot;
  assign mst_ar_qos     = slv_ar_qos;
  assign mst_ar_region  = slv_ar_region;
  assign mst_ar_user    = slv_ar_user;
  assign mst_ar_valid   = slv_ar_valid;
  assign slv_ar_ready   = mst_ar_ready;
  assign slv_r_id       = mst_r_id;
  assign slv_r_data     = mst_r_data;
  assign slv_r_resp     = mst_r_resp;
  assign slv_r_last     = mst_r_last;
  assign slv_r_user     = mst_r_user;
  assign slv_r_valid    = mst_r_valid;
  assign mst_r_ready    = slv_r_ready;
  assign slv_b_id       = mst_b_id;
  assign slv_b_resp     = mst_b_resp;
  assign slv_b_user     = mst_b_user;
  assign slv_b_valid    = mst_b_valid;
  assign mst_b_ready    = slv_b_ready;

  // pragma translate_off
  `ifndef VERILATOR
    initial begin: p_assertions
      assert (ADDR_WIDTH > 0) else $fatal("AXI address width must be greater than 0!");
      assert (DATA_WIDTH > 0) else $fatal("AXI data width must be greater than 0!");
      assert (ID_WIDTH > 0) else $fatal("AXI ID width must be greater than 0!");
      assert (BUF_DEPTH >= 1) else $fatal("Buffer depth must be at least 1!");
    end
  `endif
  // pragma translate_on

endmodule

// Interface wrapper around `axi_write_burst_packer`. See the header of that module for the
// parameter and interface definition.
module axi_write_burst_packer_wrap #(

  parameter int unsigned ADDR_WIDTH = 0,
  parameter int unsigned DATA_WIDTH = 0,
  parameter int unsigned ID_WIDTH = 0,
  parameter int unsigned USER_WIDTH = 0,
  parameter int unsigned BUF_DEPTH = 0
) (
  input  logic    clk_i,
  input  logic    rst_ni,

  AXI_BUS.Slave   slv,
  AXI_BUS.Master  mst
);

  axi_write_burst_packer #(
    .ADDR_WIDTH (ADDR_WIDTH),
    .DATA_WIDTH (DATA_WIDTH),
    .ID_WIDTH   (ID_WIDTH),
    .USER_WIDTH (USER_WIDTH),
    .BUF_DEPTH  (BUF_DEPTH)
  ) i_unwrapped (
    .clk_i,
    .rst_ni,

    // Slave Ports
    .slv_aw_id      (slv.aw_id),
    .slv_aw_addr    (slv.aw_addr),
    .slv_aw_len     (slv.aw_len),
    .slv_aw_size    (slv.aw_size),
    .slv_aw_burst   (slv.aw_burst),
    .slv_aw_lock    (slv.aw_lock),
    .slv_aw_cache   (slv.aw_cache),
    .slv_aw_prot    (slv.aw_prot),
    .slv_aw_qos     (slv.aw_qos),
    .slv_aw_region  (slv.aw_region),
    .slv_aw_atop    (slv.aw_atop),
    .slv_aw_user    (slv.aw_user),
    .slv_aw_valid   (slv.aw_valid),
    .slv_aw_ready   (slv.aw_ready),
    .slv_w_data     (slv.w_data),
    .slv_w_strb     (slv.w_strb),
    .slv_w_last     (slv.w_last),
    .slv_w_user     (slv.w_user),
    .slv_w_valid    (slv.w_valid),
    .slv_w_ready    (slv.w_ready),
    .slv_b_id       (slv.b_id),
    .slv_b_resp     (slv.b_resp),
    .slv_b_user     (slv.b_user),
    .slv_b_valid    (slv.b_valid),
    .slv_b_ready    (slv.b_ready),
    .slv_ar_id      (slv.ar_id),
    .slv_ar_addr    (slv.ar_addr),
    .slv_ar_len     (slv.ar_len),
    .slv_ar_size    (slv.ar_size),
    .slv_ar_burst   (slv.ar_burst),
    .slv_ar_lock    (slv.ar_lock),
    .slv_ar_cache   (slv.ar_cache),
    .slv_ar_prot    (slv.ar_prot),
    .slv_ar_qos     (slv.ar_qos),
    .slv_ar_region  (slv.ar_region),
    .slv_ar_user    (slv.ar_user),
    .slv_ar_valid   (slv.ar_valid),
    .slv_ar_ready   (slv.ar_ready),
    .slv_r_id       (slv.r_id),
    .slv_r_data     (slv.r_data),
    .slv_r_resp     (slv.r_resp),
    .slv_r_last     (slv.r_last),
    .slv_r_user     (slv.r_user),
    .slv_r_valid    (slv.r_valid),
    .slv_r_ready    (slv.r_ready),

    // Master Ports
    .mst_aw_id      (mst.aw_id),
    .mst_aw_addr    (mst.aw_addr),
    .mst_aw_len     (mst.aw_len),
    .mst_aw_size    (mst.aw_size),
    .mst_aw_burst   (mst.aw_burst),
    .mst_aw_lock    (mst.aw_lock),
    .mst_aw_cache   (mst.aw_cache),
    .mst_aw_prot    (mst.aw_prot),
    .mst_aw_qos     (mst.aw_qos),
    .mst_aw_region  (mst.aw_region),
    .mst_aw_atop    (mst.aw_atop),
    .mst_aw_user    (mst.aw_user),
    .mst_aw_valid   (mst.aw_valid),
    .mst_aw_ready   (mst.aw_ready),
    .mst_w_data     (mst.w_data),
    .mst_w_strb     (mst.w_strb),
    .mst_w_last     (mst.w_last),
    .mst_w_user     (mst.w_user),
    .mst_w_valid    (mst.w_valid),
    .mst_w_ready    (mst.w_ready),
    .mst_b_id       (mst.b_id),
    .mst_b_resp     (mst.b_resp),
    .mst_b_user     (mst.b_user),
    .mst_b_valid    (mst.b_valid),
    .mst_b_ready    (mst.b_ready),
    .mst_ar_id      (mst.ar_id),
    .mst_ar_addr    (mst.ar_addr),
    .mst_ar_len     (mst.ar_len),
    .mst_ar_size    (mst.ar_size),
    .mst_ar_burst   (mst.ar_burst),
    .mst_ar_lock    (mst.ar_lock),
    .mst_ar_cache   (mst.ar_cache),
    .mst_ar_prot    (mst.ar_prot),
    .mst_ar_qos     (mst.ar_qos),
    .mst_ar_region  (mst.ar_region),
    .mst_ar_user    (mst.ar_user),
    .mst_ar_valid   (mst.ar_valid),
    .mst_ar_ready   (mst.ar_ready),
    .mst_r_id       (mst.r_id),
    .mst_r_data     (mst.r_data),
    .mst_r_resp     (mst.r_resp),
    .mst_r_last     (mst.r_last),
    .mst_r_user     (mst.r_user),
    .mst_r_valid    (mst.r_valid),
    .mst_r_ready    (mst.r_ready)
  );

endmodule
