// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// AXI Performance Monitor
// TODO: Module specification

import axi_pkg::atop_t;
import axi_pkg::len_t;
import axi_pkg::resp_t;
import axi_pkg::size_t;

module axi_perf_mon #(
  // Number of monitored AXI interfaces
  parameter int unsigned  N_MON         = 0,
  // ID width of the monitored AXI interfaces
  parameter int unsigned  IW            = 0,
  // Capabilities of all interface monitors
  parameter bit           CAP_HS        = 1'b0,   // handshakes
  parameter bit           CAP_FL_TXN    = 1'b0,   // transactions in flight
  parameter bit           CAP_FL_DAT    = 1'b0,   // data bytes in flight
  parameter bit           CAP_TX_DAT    = 1'b0,   // data transferred
  parameter bit           CAP_STALL     = 1'b0,   // stalls
  parameter bit           CAP_RT        = 1'b0,   // round trips
  parameter bit           CAP_EXCL      = 1'b0,   // exclusive accesses
  parameter bit           CAP_ATOP      = 1'b0,   // atomic transactions
  // Counter widths for all interface monitors
  parameter int unsigned  CW_CLK        = 0,
  parameter int unsigned  CW_HS_CMD     = 0,
  parameter int unsigned  CW_HS_DAT     = 0,
  parameter int unsigned  CW_FL_TXN_ACC = 0,
  parameter int unsigned  CW_FL_TXN_MAX = 0,
  parameter int unsigned  CW_FL_DAT_ACC = 0,
  parameter int unsigned  CW_FL_DAT_MAX = 0,
  parameter int unsigned  CW_TX_DAT     = 0,
  parameter int unsigned  CW_STALL_CMD  = 0,
  parameter int unsigned  CW_STALL_DAT  = 0,
  parameter int unsigned  CW_STALL_MAX  = 0,
  parameter int unsigned  CW_RT_ACC     = 0,
  parameter int unsigned  CW_RT_MAX     = 0,
  parameter int unsigned  CW_EXCL       = 0,
  parameter int unsigned  CW_ATOP       = 0,
  // Protocol compliance assertions
  parameter bit           ASSERTIONS    = 1'b1,
  // Dependent parameters, do not override.
  parameter type id_t = logic [IW-1:0],
  parameter int unsigned N_IDS = 2**IW
) (
  // APB Readout and Control Interface
  input  logic        pclk_i,
  input  logic        preset_ni,
  input  logic [31:0] paddr_i,
  input  logic  [2:0] pprot_i,
  input  logic        psel_i,
  input  logic        penable_i,
  input  logic        pwrite_i,
  input  logic [31:0] pwdata_i,
  input  logic  [3:0] pstrb_i,
  output logic        pready_o,
  output logic [31:0] prdata_o,
  output logic        pslverr_o,

  // Monitored AXI Interfaces
  input  logic  [N_MON-1:0] clk_axi_i,
  input  logic  [N_MON-1:0] rst_axi_ni,
  input  id_t   [N_MON-1:0] ar_id_i,
  input  len_t  [N_MON-1:0] ar_len_i,
  input  size_t [N_MON-1:0] ar_size_i,
  input  logic  [N_MON-1:0] ar_lock_i,
  input  logic  [N_MON-1:0] ar_valid_i,
  input  logic  [N_MON-1:0] ar_ready_i,
  input  id_t   [N_MON-1:0] aw_id_i,
  input  len_t  [N_MON-1:0] aw_len_i,
  input  size_t [N_MON-1:0] aw_size_i,
  input  logic  [N_MON-1:0] aw_lock_i,
  input  atop_t [N_MON-1:0] aw_atop_i,
  input  logic  [N_MON-1:0] aw_valid_i,
  input  logic  [N_MON-1:0] aw_ready_i,
  input  id_t   [N_MON-1:0] r_id_i,
  input  logic  [N_MON-1:0] r_last_i,
  input  logic  [N_MON-1:0] r_valid_i,
  input  logic  [N_MON-1:0] r_ready_i,
  input  logic  [N_MON-1:0] w_last_i,
  input  logic  [N_MON-1:0] w_valid_i,
  input  logic  [N_MON-1:0] w_ready_i,
  input  id_t   [N_MON-1:0] b_id_i,
  input  resp_t [N_MON-1:0] b_resp_i,
  input  logic  [N_MON-1:0] b_valid_i,
  input  logic  [N_MON-1:0] b_ready_i
);

  localparam int unsigned MAX_N_MON = 8; // Do not change.

  // Internal APB bus
  logic [MAX_N_MON-1:0]       pclk;
  logic [MAX_N_MON-1:0]       preset_n;
  logic [MAX_N_MON-1:0][31:0] paddr;
  logic [MAX_N_MON-1:0] [2:0] pprot;
  logic [MAX_N_MON-1:0]       psel;
  logic [MAX_N_MON-1:0]       penable;
  logic [MAX_N_MON-1:0]       pwrite;
  logic [MAX_N_MON-1:0][31:0] pwdata;
  logic [MAX_N_MON-1:0] [3:0] pstrb;
  logic [MAX_N_MON-1:0]       pready;
  logic [MAX_N_MON-1:0][31:0] prdata;
  logic [MAX_N_MON-1:0]       pslverr;

  for (genvar i = 0; i < N_MON; i++) begin: gen_mon

    // Clock cycle counter
    logic [CW_CLK-1:0]        cnt_clk;
    logic                     cnt_clk_oflw;

    // Count of handshakes on command (AR, AW) channels
    logic [CW_HS_CMD-1:0]     hs_cnt_ar,          hs_cnt_aw;
    logic                     hs_cnt_ar_oflw,     hs_cnt_aw_oflw;

    // Count of handshakes on data (R, W) channels
    logic [CW_HS_DAT-1:0]     hs_cnt_r,           hs_cnt_w;
    logic                     hs_cnt_r_oflw,      hs_cnt_w_oflw;

    // Maximum number of in-flight transactions
    logic [CW_FL_TXN_MAX-1:0] fl_txn_max_r,       fl_txn_max_w;
    logic                     fl_txn_max_r_oflw,  fl_txn_max_w_oflw;

    // Accumulated number of in-flight transactions at each clock cycle
    logic [CW_FL_TXN_ACC-1:0] fl_txn_acc_r,       fl_txn_acc_w;
    logic                     fl_txn_acc_r_oflw,  fl_txn_acc_w_oflw;

    // Current and maximum number of data bytes in flight
    logic [CW_FL_DAT_MAX-1:0] fl_dat_cnt_r,       fl_dat_cnt_w,
                              fl_dat_max_r,       fl_dat_max_w;
    logic                     fl_dat_cnt_r_oflw,  fl_dat_cnt_w_oflw,
                              fl_dat_max_r_oflw,  fl_dat_max_w_oflw;

    // Accumulated number of data bytes in flight at each clock cycle
    logic [CW_FL_DAT_ACC-1:0] fl_dat_acc_r,       fl_dat_acc_w;
    logic                     fl_dat_acc_r_oflw,  fl_dat_acc_w_oflw;

    // Count of data bytes transferred
    logic [CW_TX_DAT-1:0]     tx_dat_cnt_r,       tx_dat_cnt_w;
    logic                     tx_dat_cnt_r_oflw,  tx_dat_cnt_w_oflw;

    // Maximum number of stall cycles
    logic [CW_STALL_MAX-1:0]  stall_max_ar,       stall_max_aw,
                              stall_max_r,        stall_max_w,        stall_max_b;
    logic                     stall_max_ar_oflw,  stall_max_aw_oflw,
                              stall_max_r_oflw,   stall_max_w_oflw,   stall_max_b_oflw;

    // Count of stall cycles on command (AR, AW) channels and on B channel (because #AW HS = #B HS)
    logic [CW_STALL_CMD-1:0]  stall_cnt_ar,       stall_cnt_aw,       stall_cnt_b;
    logic                     stall_cnt_ar_oflw,  stall_cnt_aw_oflw,  stall_cnt_b_oflw;

    // Count of stall cycles on data (R, W) channels
    logic [CW_STALL_DAT-1:0]  stall_cnt_r,        stall_cnt_w;
    logic                     stall_cnt_r_oflw,   stall_cnt_w_oflw;

    // Round trip counters are still to be defined.

    // Count of exclusive ARs, AWs, and Bs
    logic [CW_EXCL-1:0]       excl_cnt_ar,        excl_cnt_aw,        excl_cnt_b;
    logic                     excl_cnt_ar_oflw,   excl_cnt_aw_oflw,   excl_cnt_b_oflw;

    // Count of atomic transactions
    logic [CW_ATOP-1:0]       atop_cnt_st,        atop_cnt_ld,
                              atop_cnt_swp,       atop_cnt_cmp;
    logic                     atop_cnt_st_oflw,   atop_cnt_ld_oflw,
                              atop_cnt_swp_oflw,  atop_cnt_cmp_oflw;

    // Monitor-internal APB bus
    localparam int unsigned N_APB_REGS = 3;
    logic [N_APB_REGS-1:0]        mon_pclk;
    logic [N_APB_REGS-1:0]        mon_preset_n;
    logic [N_APB_REGS-1:0][31:0]  mon_paddr;
    logic [N_APB_REGS-1:0] [2:0]  mon_pprot;
    logic [N_APB_REGS-1:0]        mon_psel;
    logic [N_APB_REGS-1:0]        mon_penable;
    logic [N_APB_REGS-1:0]        mon_pwrite;
    logic [N_APB_REGS-1:0][31:0]  mon_pwdata;
    logic [N_APB_REGS-1:0] [3:0]  mon_pstrb;
    logic [N_APB_REGS-1:0]        mon_pready;
    logic [N_APB_REGS-1:0][31:0]  mon_prdata;
    logic [N_APB_REGS-1:0]        mon_pslverr;

    // Control register
    logic [31:0] ctrl_reg;
    logic clr, en;
    assign en = ctrl_reg[0];
    assign clr = ctrl_reg[1];

    // Capability info register
    logic [31:0] cap_reg;
    assign cap_reg[0] = 1'b1; // monitor exists

    // 32-bit APB output registers
    localparam int unsigned N_OUP_REGS = 128-2;
    logic [N_OUP_REGS-1:0][31:0] oup_reg;

    counter #(.WIDTH(CW_CLK), .LATCH_OVERFLOW(1'b1)) i_cnt_clk (
      .clk_i      (clk_axi_i[i]),
      .rst_ni     (rst_axi_ni[i]),
      .clear_i    (clr),
      .en_i       (en),
      .load_i     (1'b0),
      .down_i     (1'b0),
      .d_i        (),
      .q_o        (cnt_clk),
      .overflow_o (cnt_clk_oflw)
    );
    apm_cnt_to_apb_reg #(.CW(CW_CLK)) i_cnt_clk_reg (
      .cnt_i(cnt_clk), .oflw_i(cnt_clk_oflw), .reg_o(oup_reg[1:0])
    );

    // 1: Handshakes
    if (CAP_HS) begin: gen_hs
      assign cap_reg[1] = 1'b1;
      counter #(.WIDTH(CW_HS_CMD), .LATCH_OVERFLOW(1'b1)) i_hs_cnt_ar (
        .clk_i      (clk_axi_i[i]),
        .rst_ni     (rst_axi_ni[i]),
        .clear_i    (clr),
        .en_i       (en & ar_valid_i[i] & ar_ready_i[i]),
        .load_i     (1'b0),
        .down_i     (1'b0),
        .d_i        (),
        .q_o        (hs_cnt_ar),
        .overflow_o (hs_cnt_ar_oflw)
      );
      counter #(.WIDTH(CW_HS_CMD), .LATCH_OVERFLOW(1'b1)) i_hs_cnt_aw (
        .clk_i      (clk_axi_i[i]),
        .rst_ni     (rst_axi_ni[i]),
        .clear_i    (clr),
        .en_i       (en & aw_valid_i[i] & aw_ready_i[i]),
        .load_i     (1'b0),
        .down_i     (1'b0),
        .d_i        (),
        .q_o        (hs_cnt_aw),
        .overflow_o (hs_cnt_aw_oflw)
      );
      counter #(.WIDTH(CW_HS_DAT), .LATCH_OVERFLOW(1'b1)) i_hs_cnt_r (
        .clk_i      (clk_axi_i[i]),
        .rst_ni     (rst_axi_ni[i]),
        .clear_i    (clr),
        .en_i       (en & r_valid_i[i] & r_ready_i[i]),
        .load_i     (1'b0),
        .down_i     (1'b0),
        .d_i        (),
        .q_o        (hs_cnt_r),
        .overflow_o (hs_cnt_r_oflw)
      );
      counter #(.WIDTH(CW_HS_DAT), .LATCH_OVERFLOW(1'b1)) i_hs_cnt_w (
        .clk_i      (clk_axi_i[i]),
        .rst_ni     (rst_axi_ni[i]),
        .clear_i    (clr),
        .en_i       (en & w_valid_i[i] & w_ready_i[i]),
        .load_i     (1'b0),
        .down_i     (1'b0),
        .d_i        (),
        .q_o        (hs_cnt_w),
        .overflow_o (hs_cnt_w_oflw)
      );
    end else begin: gen_no_hs
      assign cap_reg[1] = 1'b0;
      assign hs_cnt_ar  = 'x;
      assign hs_cnt_aw  = 'x;
      assign hs_cnt_r   = 'x;
      assign hs_cnt_w   = 'x;
      assign hs_cnt_ar_oflw = 1'b0;
      assign hs_cnt_aw_oflw = 1'b0;
      assign hs_cnt_r_oflw  = 1'b0;
      assign hs_cnt_w_oflw  = 1'b0;
    end
    apm_cnt_to_apb_reg #(.CW(CW_HS_CMD)) i_hs_cnt_ar_reg (
      .cnt_i(hs_cnt_ar), .oflw_i(hs_cnt_ar_oflw), .reg_o(oup_reg[3:2])
    );
    apm_cnt_to_apb_reg #(.CW(CW_HS_CMD)) i_hs_cnt_aw_reg (
      .cnt_i(hs_cnt_aw), .oflw_i(hs_cnt_aw_oflw), .reg_o(oup_reg[5:4])
    );
    apm_cnt_to_apb_reg #(.CW(CW_HS_DAT)) i_hs_cnt_r_reg (
      .cnt_i(hs_cnt_r), .oflw_i(hs_cnt_r_oflw), .reg_o(oup_reg[7:6])
    );
    apm_cnt_to_apb_reg #(.CW(CW_HS_DAT)) i_hs_cnt_w_reg (
      .cnt_i(hs_cnt_w), .oflw_i(hs_cnt_w_oflw), .reg_o(oup_reg[9:8])
    );

    // 2: Transactions in flight
    if (CAP_FL_TXN) begin: gen_fl_txn
      // Register for in-flight ATOPs that result in an R response. This bit gets set upon an AW HS
      // for Atomic{Load,Compare,Swap} and cleared upon the corresponding R last HS. If this bit is
      // set on an R last, the counter of reads in flight is not decremented. One bit per ID is
      // sufficient because there can be at most one ATOP in flight per ID at any moment.
      logic [N_IDS-1:0] fl_atop_r_d, fl_atop_r_q;
      // Register for in-flight ATOPs, which all result in a B response. This bit gets set upon an
      // AW HS for any ATOP and cleared upon the corresponding B HS. ATOPs are not counted as
      // in-flight writes. One bit per ID is sufficient because there can be at most one ATOP in
      // flight per ID at any moment.
      logic [N_IDS-1:0] fl_atop_b_d, fl_atop_b_q;

      logic r_inc, r_dec,
            w_inc, w_dec;
      logic [CW_FL_TXN_MAX-1:0] r_cnt,
                                w_cnt;
      logic r_acc_oflw,
            w_acc_oflw;
      assign cap_reg[2] = 1'b1;
      always_comb begin
        r_inc = ar_valid_i[i] & ar_ready_i[i];
        r_dec = r_valid_i[i] & r_ready_i[i] & r_last_i[i] & ~fl_atop_r_q[r_id_i[i]];
        if (r_inc && r_dec) begin
          r_inc = 1'b0;
          r_dec = 1'b0;
        end
      end
      always_comb begin
        fl_atop_b_d = fl_atop_b_q;
        fl_atop_r_d = fl_atop_r_q;
        if (aw_valid_i[i] && aw_ready_i[i] && aw_atop_i[i][5:4] != axi_pkg::ATOP_NONE) begin
          fl_atop_b_d[aw_id_i[i]] = 1'b1;
          if (aw_atop_i[i][5:4] != axi_pkg::ATOP_ATOMICSTORE) begin
            fl_atop_r_d[aw_id_i[i]] = 1'b1;
          end
        end
        if (r_valid_i[i] && r_ready_i[i] && r_last_i[i] && fl_atop_r_q[r_id_i[i]]) begin
          fl_atop_r_d[r_id_i[i]] = 1'b0;
        end
        if (b_valid_i[i] && b_ready_i[i] && fl_atop_b_q[b_id_i[i]]) begin
          fl_atop_b_d[b_id_i[i]] = 1'b0;
        end
      end
      if (ASSERTIONS) begin
        assert property (
          @(posedge clk_axi_i[i]) ar_valid_i[i] && ar_ready_i[i] |-> !fl_atop_b_q[ar_id_i[i]]
        ) else $error(
          "AR with ID 0x%0x illegal due to incomplete ATOP to same ID (B missing)", ar_id_i[i]);
        assert property (
          @(posedge clk_axi_i[i]) ar_valid_i[i] && ar_ready_i[i] |-> !fl_atop_r_q[ar_id_i[i]]
        ) else $error(
          "AR with ID 0x%0x illegal due to incomplete ATOP to same ID (R missing)", ar_id_i[i]);
        assert property (
          @(posedge clk_axi_i[i]) aw_valid_i[i] && aw_ready_i[i] |-> !fl_atop_b_q[aw_id_i[i]]
        ) else $error(
          "AW with ID 0x%0x illegal due to incomplete ATOP to same ID (B missing)", aw_id_i[i]);
        assert property (
          @(posedge clk_axi_i[i]) aw_valid_i[i] && aw_ready_i[i] |-> !fl_atop_r_q[aw_id_i[i]]
        ) else $error(
          "AW with ID 0x%0x illegal due to incomplete ATOP to same ID (R missing)", aw_id_i[i]);
      end
      max_counter #(.WIDTH(CW_FL_TXN_MAX)) i_fl_txn_cnt_r (
        .clk_i          (clk_axi_i[i]),
        .rst_ni         (rst_axi_ni[i]),
        .clear_i        (clr),
        .clear_max_i    (clr),
        .en_i           (en & (r_inc | r_dec)),
        .load_i         (1'b0),
        .down_i         (r_dec),
        .delta_i        ({{CW_FL_TXN_MAX-1{1'b0}}, 1'b1}),
        .d_i            (),
        .q_o            (r_cnt),
        .max_o          (fl_txn_max_r),
        .overflow_o     (fl_txn_max_r_oflw),
        .overflow_max_o ()
      );
      delta_counter #(.WIDTH(CW_FL_TXN_ACC)) i_fl_txn_acc_r (
        .clk_i      (clk_axi_i[i]),
        .rst_ni     (rst_axi_ni[i]),
        .clear_i    (clr),
        .en_i       (en),
        .load_i     (1'b0),
        .down_i     (1'b0),
        .delta_i    ({{CW_FL_TXN_ACC-CW_FL_TXN_MAX{1'b0}}, r_cnt}),
        .d_i        (),
        .q_o        (fl_txn_acc_r),
        .overflow_o (r_acc_oflw)
      );
      assign fl_txn_acc_r_oflw = fl_txn_max_r_oflw | r_acc_oflw;
      always_comb begin
        w_inc = aw_valid_i[i] & aw_ready_i[i] & (aw_atop_i[i][5:4] == axi_pkg::ATOP_NONE);
        w_dec = b_valid_i[i] & b_ready_i[i] & ~fl_atop_b_q[b_id_i[i]];
        if (w_inc && w_dec) begin
          w_inc = 1'b0;
          w_dec = 1'b0;
        end
      end
      max_counter #(.WIDTH(CW_FL_TXN_MAX)) i_fl_txn_cnt_w (
        .clk_i          (clk_axi_i[i]),
        .rst_ni         (rst_axi_ni[i]),
        .clear_i        (clr),
        .clear_max_i    (clr),
        .en_i           (en & (w_inc | w_dec)),
        .load_i         (1'b0),
        .down_i         (w_dec),
        .delta_i        ({{CW_FL_TXN_MAX-1{1'b0}}, 1'b1}),
        .d_i            (),
        .q_o            (w_cnt),
        .max_o          (fl_txn_max_w),
        .overflow_o     (fl_txn_max_w_oflw),
        .overflow_max_o ()
      );
      delta_counter #(.WIDTH(CW_FL_TXN_ACC)) i_fl_txn_acc_w (
        .clk_i      (clk_axi_i[i]),
        .rst_ni     (rst_axi_ni[i]),
        .clear_i    (clr),
        .en_i       (en),
        .load_i     (1'b0),
        .down_i     (1'b0),
        .delta_i    ({{CW_FL_TXN_ACC-CW_FL_TXN_MAX{1'b0}}, w_cnt}),
        .d_i        (),
        .q_o        (fl_txn_acc_w),
        .overflow_o (w_acc_oflw)
      );
      assign fl_txn_acc_w_oflw = fl_txn_max_w_oflw | w_acc_oflw;

      always_ff @(posedge clk_axi_i[i], negedge rst_axi_ni[i]) begin
        if (!rst_axi_ni[i]) begin
          fl_atop_b_q <= '0;
          fl_atop_r_q <= '0;
        end else begin
          fl_atop_b_q <= fl_atop_b_d;
          fl_atop_r_q <= fl_atop_r_d;
        end
      end

    end else begin: gen_no_fl_txn
      assign cap_reg[2] = 1'b0;
      assign fl_txn_acc_r = 'x;
      assign fl_txn_max_r = 'x;
      assign fl_txn_acc_w = 'x;
      assign fl_txn_max_w = 'x;
      assign fl_txn_acc_r_oflw  = 1'b0;
      assign fl_txn_max_r_oflw  = 1'b0;
      assign fl_txn_acc_w_oflw  = 1'b0;
      assign fl_txn_max_w_oflw  = 1'b0;
    end
    apm_cnt_to_apb_reg #(.CW(CW_FL_TXN_ACC)) i_fl_txn_acc_r_reg (
      .cnt_i(fl_txn_acc_r), .oflw_i(fl_txn_acc_r_oflw), .reg_o(oup_reg[11:10])
    );
    apm_cnt_to_apb_reg #(.CW(CW_FL_TXN_MAX)) i_fl_txn_max_r_reg (
      .cnt_i(fl_txn_max_r), .oflw_i(fl_txn_max_r_oflw), .reg_o(oup_reg[13:12])
    );
    apm_cnt_to_apb_reg #(.CW(CW_FL_TXN_ACC)) i_fl_txn_acc_w_reg (
      .cnt_i(fl_txn_acc_w), .oflw_i(fl_txn_acc_w_oflw), .reg_o(oup_reg[15:14])
    );
    apm_cnt_to_apb_reg #(.CW(CW_FL_TXN_MAX)) i_fl_txn_max_w_reg (
      .cnt_i(fl_txn_max_w), .oflw_i(fl_txn_max_w_oflw), .reg_o(oup_reg[17:16])
    );

    // 3: Data bytes in flight
    assign cap_reg[3] = 1'b0;
    assign oup_reg[19:18] = '0;
    assign oup_reg[21:20] = '0;
    assign oup_reg[23:22] = '0;
    assign oup_reg[25:24] = '0;

    // 4: Data transferred
    assign cap_reg[4] = 1'b0;
    assign oup_reg[27:26] = '0;
    assign oup_reg[29:28] = '0;

    // 5: Stalls
    if (CAP_STALL) begin: gen_stall
      assign cap_reg[5] = 1'b1;
      counter #(.WIDTH(CW_STALL_CMD), .LATCH_OVERFLOW(1'b1)) i_stall_cnt_ar (
        .clk_i      (clk_axi_i[i]),
        .rst_ni     (rst_axi_ni[i]),
        .clear_i    (clr),
        .en_i       (en & ar_valid_i[i] & ~ar_ready_i[i]),
        .load_i     (1'b0),
        .down_i     (1'b0),
        .d_i        (),
        .q_o        (stall_cnt_ar),
        .overflow_o (stall_cnt_ar_oflw)
      );
      counter #(.WIDTH(CW_STALL_CMD), .LATCH_OVERFLOW(1'b1)) i_stall_cnt_aw (
        .clk_i      (clk_axi_i[i]),
        .rst_ni     (rst_axi_ni[i]),
        .clear_i    (clr),
        .en_i       (en & aw_valid_i[i] & ~aw_ready_i[i]),
        .load_i     (1'b0),
        .down_i     (1'b0),
        .d_i        (),
        .q_o        (stall_cnt_aw),
        .overflow_o (stall_cnt_aw_oflw)
      );
      counter #(.WIDTH(CW_STALL_CMD), .LATCH_OVERFLOW(1'b1)) i_stall_cnt_b (
        .clk_i      (clk_axi_i[i]),
        .rst_ni     (rst_axi_ni[i]),
        .clear_i    (clr),
        .en_i       (en & b_valid_i[i] & ~b_ready_i[i]),
        .load_i     (1'b0),
        .down_i     (1'b0),
        .d_i        (),
        .q_o        (stall_cnt_b),
        .overflow_o (stall_cnt_b_oflw)
      );
      counter #(.WIDTH(CW_STALL_DAT), .LATCH_OVERFLOW(1'b1)) i_stall_cnt_r (
        .clk_i      (clk_axi_i[i]),
        .rst_ni     (rst_axi_ni[i]),
        .clear_i    (clr),
        .en_i       (en & r_valid_i[i] & ~r_ready_i[i]),
        .load_i     (1'b0),
        .down_i     (1'b0),
        .d_i        (),
        .q_o        (stall_cnt_r),
        .overflow_o (stall_cnt_r_oflw)
      );
      counter #(.WIDTH(CW_STALL_DAT), .LATCH_OVERFLOW(1'b1)) i_stall_cnt_w (
        .clk_i      (clk_axi_i[i]),
        .rst_ni     (rst_axi_ni[i]),
        .clear_i    (clr),
        .en_i       (en & w_valid_i[i] & ~w_ready_i[i]),
        .load_i     (1'b0),
        .down_i     (1'b0),
        .d_i        (),
        .q_o        (stall_cnt_w),
        .overflow_o (stall_cnt_w_oflw)
      );
      max_counter #(.WIDTH(CW_STALL_MAX)) i_stall_max_ar (
        .clk_i          (clk_axi_i[i]),
        .rst_ni         (rst_axi_ni[i]),
        .clear_i        (clr | (ar_valid_i[i] & ar_ready_i[i])),
        .clear_max_i    (clr),
        .en_i           (en & ar_valid_i[i]),
        .load_i         (1'b0),
        .down_i         (1'b0),
        .delta_i        ({{CW_STALL_MAX-1{1'b0}}, 1'b1}),
        .d_i            (),
        .q_o            (),
        .max_o          (stall_max_ar),
        .overflow_o     (),
        .overflow_max_o (stall_max_ar_oflw)
      );
      max_counter #(.WIDTH(CW_STALL_MAX)) i_stall_max_aw (
        .clk_i          (clk_axi_i[i]),
        .rst_ni         (rst_axi_ni[i]),
        .clear_i        (clr | (aw_valid_i[i] & aw_ready_i[i])),
        .clear_max_i    (clr),
        .en_i           (en & aw_valid_i[i]),
        .load_i         (1'b0),
        .down_i         (1'b0),
        .delta_i        ({{CW_STALL_MAX-1{1'b0}}, 1'b1}),
        .d_i            (),
        .q_o            (),
        .max_o          (stall_max_aw),
        .overflow_o     (),
        .overflow_max_o (stall_max_aw_oflw)
      );
      max_counter #(.WIDTH(CW_STALL_MAX)) i_stall_max_r (
        .clk_i          (clk_axi_i[i]),
        .rst_ni         (rst_axi_ni[i]),
        .clear_i        (clr | (r_valid_i[i] & r_ready_i[i])),
        .clear_max_i    (clr),
        .en_i           (en & r_valid_i[i]),
        .load_i         (1'b0),
        .down_i         (1'b0),
        .delta_i        ({{CW_STALL_MAX-1{1'b0}}, 1'b1}),
        .d_i            (),
        .q_o            (),
        .max_o          (stall_max_r),
        .overflow_o     (),
        .overflow_max_o (stall_max_r_oflw)
      );
      max_counter #(.WIDTH(CW_STALL_MAX)) i_stall_max_w (
        .clk_i          (clk_axi_i[i]),
        .rst_ni         (rst_axi_ni[i]),
        .clear_i        (clr | (w_valid_i[i] & w_ready_i[i])),
        .clear_max_i    (clr),
        .en_i           (en & w_valid_i[i]),
        .load_i         (1'b0),
        .down_i         (1'b0),
        .delta_i        ({{CW_STALL_MAX-1{1'b0}}, 1'b1}),
        .d_i            (),
        .q_o            (),
        .max_o          (stall_max_w),
        .overflow_o     (),
        .overflow_max_o (stall_max_w_oflw)
      );
      max_counter #(.WIDTH(CW_STALL_MAX)) i_stall_max_b (
        .clk_i          (clk_axi_i[i]),
        .rst_ni         (rst_axi_ni[i]),
        .clear_i        (clr | (b_valid_i[i] & b_ready_i[i])),
        .clear_max_i    (clr),
        .en_i           (en & b_valid_i[i]),
        .load_i         (1'b0),
        .down_i         (1'b0),
        .delta_i        ({{CW_STALL_MAX-1{1'b0}}, 1'b1}),
        .d_i            (),
        .q_o            (),
        .max_o          (stall_max_b),
        .overflow_o     (),
        .overflow_max_o (stall_max_b_oflw)
      );
    end else begin: gen_no_stall
      assign cap_reg[5] = 1'b0;
      assign stall_cnt_ar = 'x;
      assign stall_cnt_aw = 'x;
      assign stall_cnt_r  = 'x;
      assign stall_cnt_w  = 'x;
      assign stall_cnt_b  = 'x;
      assign stall_max_ar = 'x;
      assign stall_max_aw = 'x;
      assign stall_max_r  = 'x;
      assign stall_max_w  = 'x;
      assign stall_max_b  = 'x;
      assign stall_cnt_ar_oflw  = 1'b0;
      assign stall_cnt_aw_oflw  = 1'b0;
      assign stall_cnt_r_oflw   = 1'b0;
      assign stall_cnt_w_oflw   = 1'b0;
      assign stall_cnt_b_oflw   = 1'b0;
      assign stall_max_ar_oflw  = 1'b0;
      assign stall_max_aw_oflw  = 1'b0;
      assign stall_max_r_oflw   = 1'b0;
      assign stall_max_w_oflw   = 1'b0;
      assign stall_max_b_oflw   = 1'b0;
    end
    apm_cnt_to_apb_reg #(.CW(CW_STALL_CMD)) i_stall_cnt_ar_reg (
      .cnt_i(stall_cnt_ar), .oflw_i(stall_cnt_ar_oflw), .reg_o(oup_reg[31:30])
    );
    apm_cnt_to_apb_reg #(.CW(CW_STALL_MAX)) i_stall_max_ar_reg (
      .cnt_i(stall_max_ar), .oflw_i(stall_max_ar_oflw), .reg_o(oup_reg[33:32])
    );
    apm_cnt_to_apb_reg #(.CW(CW_STALL_CMD)) i_stall_cnt_aw_reg (
      .cnt_i(stall_cnt_aw), .oflw_i(stall_cnt_aw_oflw), .reg_o(oup_reg[35:34])
    );
    apm_cnt_to_apb_reg #(.CW(CW_STALL_MAX)) i_stall_max_aw_reg (
      .cnt_i(stall_max_aw), .oflw_i(stall_max_aw_oflw), .reg_o(oup_reg[37:36])
    );
    apm_cnt_to_apb_reg #(.CW(CW_STALL_DAT)) i_stall_cnt_r_reg (
      .cnt_i(stall_cnt_r), .oflw_i(stall_cnt_r_oflw), .reg_o(oup_reg[39:38])
    );
    apm_cnt_to_apb_reg #(.CW(CW_STALL_MAX)) i_stall_max_r_reg (
      .cnt_i(stall_max_r), .oflw_i(stall_max_r_oflw), .reg_o(oup_reg[41:40])
    );
    apm_cnt_to_apb_reg #(.CW(CW_STALL_DAT)) i_stall_cnt_w_reg (
      .cnt_i(stall_cnt_w), .oflw_i(stall_cnt_w_oflw), .reg_o(oup_reg[43:42])
    );
    apm_cnt_to_apb_reg #(.CW(CW_STALL_MAX)) i_stall_max_w_reg (
      .cnt_i(stall_max_w), .oflw_i(stall_max_w_oflw), .reg_o(oup_reg[45:44])
    );
    apm_cnt_to_apb_reg #(.CW(CW_STALL_CMD)) i_stall_cnt_b_reg (
      .cnt_i(stall_cnt_b), .oflw_i(stall_cnt_b_oflw), .reg_o(oup_reg[47:46])
    );
    apm_cnt_to_apb_reg #(.CW(CW_STALL_MAX)) i_stall_max_b_reg (
      .cnt_i(stall_max_b), .oflw_i(stall_max_b_oflw), .reg_o(oup_reg[49:48])
    );

    // 6: Round trips
    assign cap_reg[6] = 1'b0;
    assign oup_reg[51:50] = '0;
    assign oup_reg[53:52] = '0;
    assign oup_reg[55:54] = '0;
    assign oup_reg[57:56] = '0;
    assign oup_reg[59:58] = '0;
    assign oup_reg[61:60] = '0;

    // 7: Exclusive accesses
    if (CAP_EXCL) begin: gen_excl
      assign cap_reg[7] = 1'b1;
      counter #(.WIDTH(CW_EXCL), .LATCH_OVERFLOW(1'b1)) i_excl_cnt_ar (
        .clk_i      (clk_axi_i[i]),
        .rst_ni     (rst_axi_ni[i]),
        .clear_i    (clr),
        .en_i       (en & ar_valid_i[i] & ar_ready_i[i] & ar_lock_i[i]),
        .load_i     (1'b0),
        .down_i     (1'b0),
        .d_i        (),
        .q_o        (excl_cnt_ar),
        .overflow_o (excl_cnt_ar_oflw)
      );
      counter #(.WIDTH(CW_EXCL), .LATCH_OVERFLOW(1'b1)) i_excl_cnt_aw (
        .clk_i      (clk_axi_i[i]),
        .rst_ni     (rst_axi_ni[i]),
        .clear_i    (clr),
        .en_i       (en & aw_valid_i[i] & aw_ready_i[i] & aw_lock_i[i]),
        .load_i     (1'b0),
        .down_i     (1'b0),
        .d_i        (),
        .q_o        (excl_cnt_aw),
        .overflow_o (excl_cnt_aw_oflw)
      );
      import axi_pkg::RESP_EXOKAY;
      counter #(.WIDTH(CW_EXCL), .LATCH_OVERFLOW(1'b1)) i_excl_cnt_b (
        .clk_i      (clk_axi_i[i]),
        .rst_ni     (rst_axi_ni[i]),
        .clear_i    (clr),
        .en_i       (en & b_valid_i[i] & b_ready_i[i] & (b_resp_i[i] == RESP_EXOKAY)),
        .load_i     (1'b0),
        .down_i     (1'b0),
        .d_i        (),
        .q_o        (excl_cnt_b),
        .overflow_o (excl_cnt_b_oflw)
      );
    end else begin: gen_no_excl
      assign cap_reg[7] = 1'b0;
      assign excl_cnt_ar  = 'x;
      assign excl_cnt_aw  = 'x;
      assign excl_cnt_b   = 'x;
      assign excl_cnt_ar_oflw = 1'b0;
      assign excl_cnt_aw_oflw = 1'b0;
      assign excl_cnt_b_oflw  = 1'b0;
    end
    apm_cnt_to_apb_reg #(.CW(CW_EXCL)) i_excl_cnt_ar_reg (
      .cnt_i(excl_cnt_ar), .oflw_i(excl_cnt_ar_oflw), .reg_o(oup_reg[63:62])
    );
    apm_cnt_to_apb_reg #(.CW(CW_EXCL)) i_excl_cnt_aw_reg (
      .cnt_i(excl_cnt_aw), .oflw_i(excl_cnt_aw_oflw), .reg_o(oup_reg[65:64])
    );
    apm_cnt_to_apb_reg #(.CW(CW_EXCL)) i_excl_cnt_b_reg (
      .cnt_i(excl_cnt_b), .oflw_i(excl_cnt_b_oflw), .reg_o(oup_reg[67:66])
    );

    // 8: Atomic transactions
    if (CAP_ATOP) begin: gen_atop
      import axi_pkg::ATOP_ATOMICSTORE;
      assign cap_reg[8] = 1'b1;
      counter #(.WIDTH(CW_ATOP), .LATCH_OVERFLOW(1'b1)) i_atop_cnt_st (
        .clk_i      (clk_axi_i[i]),
        .rst_ni     (rst_axi_ni[i]),
        .clear_i    (clr),
        .en_i       (en & aw_valid_i[i] & aw_ready_i[i] & (aw_atop_i[i][5:4] == ATOP_ATOMICSTORE)),
        .load_i     (1'b0),
        .down_i     (1'b0),
        .d_i        (),
        .q_o        (atop_cnt_st),
        .overflow_o (atop_cnt_st_oflw)
      );
      import axi_pkg::ATOP_ATOMICLOAD;
      counter #(.WIDTH(CW_ATOP), .LATCH_OVERFLOW(1'b1)) i_atop_cnt_ld (
        .clk_i      (clk_axi_i[i]),
        .rst_ni     (rst_axi_ni[i]),
        .clear_i    (clr),
        .en_i       (en & aw_valid_i[i] & aw_ready_i[i] & (aw_atop_i[i][5:4] == ATOP_ATOMICLOAD)),
        .load_i     (1'b0),
        .down_i     (1'b0),
        .d_i        (),
        .q_o        (atop_cnt_ld),
        .overflow_o (atop_cnt_ld_oflw)
      );
      import axi_pkg::ATOP_ATOMICSWAP;
      counter #(.WIDTH(CW_ATOP), .LATCH_OVERFLOW(1'b1)) i_atop_cnt_swp (
        .clk_i      (clk_axi_i[i]),
        .rst_ni     (rst_axi_ni[i]),
        .clear_i    (clr),
        .en_i       (en & aw_valid_i[i] & aw_ready_i[i] & (aw_atop_i[i] == ATOP_ATOMICSWAP)),
        .load_i     (1'b0),
        .down_i     (1'b0),
        .d_i        (),
        .q_o        (atop_cnt_swp),
        .overflow_o (atop_cnt_swp_oflw)
      );
      import axi_pkg::ATOP_ATOMICCMP;
      counter #(.WIDTH(CW_ATOP), .LATCH_OVERFLOW(1'b1)) i_atop_cnt_cmp (
        .clk_i      (clk_axi_i[i]),
        .rst_ni     (rst_axi_ni[i]),
        .clear_i    (clr),
        .en_i       (en & aw_valid_i[i] & aw_ready_i[i] & (aw_atop_i[i] == ATOP_ATOMICCMP)),
        .load_i     (1'b0),
        .down_i     (1'b0),
        .d_i        (),
        .q_o        (atop_cnt_cmp),
        .overflow_o (atop_cnt_cmp_oflw)
      );
    end else begin: gen_no_atop
      assign cap_reg[8] = 1'b0;
      assign atop_cnt_st  = 'x;
      assign atop_cnt_ld  = 'x;
      assign atop_cnt_swp = 'x;
      assign atop_cnt_cmp = 'x;
      assign atop_cnt_st_oflw   = 1'b0;
      assign atop_cnt_ld_oflw   = 1'b0;
      assign atop_cnt_swp_oflw  = 1'b0;
      assign atop_cnt_cmp_oflw  = 1'b0;
    end
    apm_cnt_to_apb_reg #(.CW(CW_ATOP)) i_atop_cnt_st_reg (
      .cnt_i(atop_cnt_st), .oflw_i(atop_cnt_st_oflw), .reg_o(oup_reg[69:68])
    );
    apm_cnt_to_apb_reg #(.CW(CW_ATOP)) i_atop_cnt_ld_reg (
      .cnt_i(atop_cnt_ld), .oflw_i(atop_cnt_ld_oflw), .reg_o(oup_reg[71:70])
    );
    apm_cnt_to_apb_reg #(.CW(CW_ATOP)) i_atop_cnt_swp_reg (
      .cnt_i(atop_cnt_swp), .oflw_i(atop_cnt_swp_oflw), .reg_o(oup_reg[73:72])
    );
    apm_cnt_to_apb_reg #(.CW(CW_ATOP)) i_atop_cnt_cmp_reg (
      .cnt_i(atop_cnt_cmp), .oflw_i(atop_cnt_cmp_oflw), .reg_o(oup_reg[75:74])
    );

    // Rest: Reserved
    assign cap_reg[31:9] = '0;
    assign oup_reg[N_OUP_REGS-1:76] = 'x;

    apb_bus #(
      .N_SLV      (N_APB_REGS),
      .ADDR_BEGIN ({32'h0000_0008, 32'h0000_0004, 32'h0000_0000}),
      .ADDR_END   ({32'h0000_01FF, 32'h0000_0007, 32'h0000_0003})
    ) i_apb_bus (
      .pclk_i     (pclk[i]),
      .preset_ni  (preset_n[i]),
      .paddr_i    (paddr[i]),
      .pprot_i    (pprot[i]),
      .psel_i     (psel[i]),
      .penable_i  (penable[i]),
      .pwrite_i   (pwrite[i]),
      .pwdata_i   (pwdata[i]),
      .pstrb_i    (pstrb[i]),
      .pready_o   (pready[i]),
      .prdata_o   (prdata[i]),
      .pslverr_o  (pslverr[i]),
      .pclk_o     (mon_pclk),
      .preset_no  (mon_preset_n),
      .paddr_o    (mon_paddr),
      .pprot_o    (mon_pprot),
      .psel_o     (mon_psel),
      .penable_o  (mon_penable),
      .pwrite_o   (mon_pwrite),
      .pwdata_o   (mon_pwdata),
      .pstrb_o    (mon_pstrb),
      .pready_i   (mon_pready),
      .prdata_i   (mon_prdata),
      .pslverr_i  (mon_pslverr)
    );

    apb_ro_regs #(.N_REGS(1)) i_cap_reg (
      .pclk_i     (mon_pclk[0]),
      .preset_ni  (mon_preset_n[0]),
      .paddr_i    (mon_paddr[0]),
      .pprot_i    (mon_pprot[0]),
      .psel_i     (mon_psel[0]),
      .penable_i  (mon_penable[0]),
      .pwrite_i   (mon_pwrite[0]),
      .pwdata_i   (mon_pwdata[0]),
      .pstrb_i    (mon_pstrb[0]),
      .pready_o   (mon_pready[0]),
      .prdata_o   (mon_prdata[0]),
      .pslverr_o  (mon_pslverr[0]),
      .reg_i      (cap_reg)
    );

    apb_rw_regs #(.N_REGS(1)) i_ctrl_reg (
      .pclk_i     (mon_pclk[1]),
      .preset_ni  (mon_preset_n[1]),
      .paddr_i    (mon_paddr[1]),
      .pprot_i    (mon_pprot[1]),
      .psel_i     (mon_psel[1]),
      .penable_i  (mon_penable[1]),
      .pwrite_i   (mon_pwrite[1]),
      .pwdata_i   (mon_pwdata[1]),
      .pstrb_i    (mon_pstrb[1]),
      .pready_o   (mon_pready[1]),
      .prdata_o   (mon_prdata[1]),
      .pslverr_o  (mon_pslverr[1]),
      .init_i     ('0),
      .q_o        (ctrl_reg)
    );

    apb_ro_regs #(.N_REGS(N_OUP_REGS)) i_oup_reg (
      .pclk_i     (mon_pclk[2]),
      .preset_ni  (mon_preset_n[2]),
      .paddr_i    (mon_paddr[2]),
      .pprot_i    (mon_pprot[2]),
      .psel_i     (mon_psel[2]),
      .penable_i  (mon_penable[2]),
      .pwrite_i   (mon_pwrite[2]),
      .pwdata_i   (mon_pwdata[2]),
      .pstrb_i    (mon_pstrb[2]),
      .pready_o   (mon_pready[2]),
      .prdata_o   (mon_prdata[2]),
      .pslverr_o  (mon_pslverr[2]),
      .reg_i      (oup_reg)
    );

  end

  for (genvar i = N_MON; i < MAX_N_MON; i++) begin: gen_no_mon
    logic [31:0] cap_reg;
    assign cap_reg = '0;

    apb_ro_regs #(.N_REGS(1)) i_cap_reg (
      .pclk_i     (pclk[i]),
      .preset_ni  (preset_n[i]),
      .paddr_i    (paddr[i]),
      .pprot_i    (pprot[i]),
      .psel_i     (psel[i]),
      .penable_i  (penable[i]),
      .pwrite_i   (pwrite[i]),
      .pwdata_i   (pwdata[i]),
      .pstrb_i    (pstrb[i]),
      .pready_o   (pready[i]),
      .prdata_o   (prdata[i]),
      .pslverr_o  (pslverr[i]),
      .reg_i      (cap_reg)
    );
  end

  apb_bus #(
    .N_SLV      (MAX_N_MON),
    .ADDR_BEGIN ({32'h0000_0E00, 32'h0000_0C00, 32'h0000_0A00, 32'h0000_0800,
                  32'h0000_0600, 32'h0000_0400, 32'h0000_0200, 32'h0000_0000}),
    .ADDR_END   ({32'h0000_0FFF, 32'h0000_0DFF, 32'h0000_0BFF, 32'h0000_09FF,
                  32'h0000_07FF, 32'h0000_05FF, 32'h0000_03FF, 32'h0000_01FF})
  ) i_apb_bus (
    .pclk_i,
    .preset_ni,
    .paddr_i,
    .pprot_i,
    .psel_i,
    .penable_i,
    .pwrite_i,
    .pwdata_i,
    .pstrb_i,
    .pready_o,
    .prdata_o,
    .pslverr_o,
    .pclk_o     (pclk),
    .preset_no  (preset_n),
    .paddr_o    (paddr),
    .pprot_o    (pprot),
    .psel_o     (psel),
    .penable_o  (penable),
    .pwrite_o   (pwrite),
    .pwdata_o   (pwdata),
    .pstrb_o    (pstrb),
    .pready_i   (pready),
    .prdata_i   (prdata),
    .pslverr_i  (pslverr)
  );

// Validate parameters.
// pragma translate_off
`ifndef VERILATOR
  initial begin: p_assertions
    assert (N_MON >= 1)
      else $fatal(1, "The number of monitored AXI interfaces must be at least 1!");
    assert (N_MON <= MAX_N_MON)
      else $fatal(1, "The number of monitored AXI interfaces can be at most %0d!", MAX_N_MON);
    assert (IW >= 1)
      else $fatal(1, "The ID width of the monitored AXI interfaces must be at least 1");
    assert (CW_CLK >= 1)  else $fatal(1, "The clock cycles counter must be at least 1 bit wide!");
    assert (CW_CLK <= 63) else $fatal(1, "Any counter can be at most 63 bits wide!");
    if (CAP_HS) begin
      assert (CW_HS_CMD >= 1)
        else $fatal(1, "The command handshake counter must be at least 1 bit wide!");
      assert (CW_HS_CMD <= 63) else $fatal(1, "Any counter can be at most 63 bits wide!");
      assert (CW_HS_DAT >= 1)
        else $fatal(1, "The data handshake counter must be at least 1 bit wide!");
      assert (CW_HS_DAT <= 63) else $fatal(1, "Any counter can be at most 63 bits wide!");
    end
    if (CAP_FL_TXN) begin
      assert (CW_FL_TXN_ACC >= 1)
        else $fatal(1, "The accumulate transaction in flight counter must be at least 1 bit wide!");
      assert (CW_FL_TXN_ACC <= 63) else $fatal(1, "Any counter can be at most 63 bits wide!");
      assert (CW_FL_TXN_MAX >= 1)
        else $fatal(1, "The maximum transaction in flight counter must be at least 1 bit wide!");
      assert (CW_FL_TXN_MAX <= 63) else $fatal(1, "Any counter can be at most 63 bits wide!");
      assert (CW_FL_TXN_MAX <= CW_FL_TXN_ACC)
          else $fatal(1, "The accumulate transaction in flight counter must be larger than its maximum counterpart");
    end
    if (CAP_FL_DAT) begin
      assert (CW_FL_DAT_ACC >= 1)
        else $fatal(1, "The accumulate data bytes in flight counter must be at least 1 bit wide!");
      assert (CW_FL_DAT_ACC <= 63) else $fatal(1, "Any counter can be at most 63 bits wide!");
      assert (CW_FL_DAT_MAX >= 1)
        else $fatal(1, "The maximum data bytes in flight counter must be at least 1 bit wide!");
      assert (CW_FL_DAT_MAX <= 63) else $fatal(1, "Any counter can be at most 63 bits wide!");
      assert (CW_FL_DAT_MAX <= CW_FL_DAT_ACC)
          else $fatal(1, "The accumulate data bytes in flight counter must be larger than its maximum counterpart");
    end
    if (CAP_TX_DAT) begin
      assert (CW_TX_DAT >= 1)
        else $fatal(1, "The accumulate data bytes transferred counter must be at least 1 bit wide!");
      assert (CW_TX_DAT <= 63) else $fatal(1, "Any counter can be at most 63 bits wide!");
    end
    if (CAP_STALL) begin
      assert (CW_STALL_CMD >= 1)
        else $fatal(1, "The command stall counter must be at least 1 bit wide!");
      assert (CW_STALL_CMD <= 63) else $fatal(1, "Any counter can be at most 63 bits wide!");
      assert (CW_STALL_DAT >= 1)
        else $fatal(1, "The data stall counter must be at least 1 bit wide!");
      assert (CW_STALL_DAT <= 63) else $fatal(1, "Any counter can be at most 63 bits wide!");
      assert (CW_STALL_MAX >= 1)
        else $fatal(1, "The maximum stall counter must be at least 1 bit wide!");
      assert (CW_STALL_MAX <= 63) else $fatal(1, "Any counter can be at most 63 bits wide!");
    end
    if (CAP_RT) begin
      assert (CW_RT_ACC >= 1)
        else $fatal(1, "The accumulate round trip counter must be at least 1 bit wide!");
      assert (CW_RT_ACC <= 63) else $fatal(1, "Any counter can be at most 63 bits wide!");
      assert (CW_RT_MAX >= 1)
        else $fatal(1, "The maximum round trip counter must be at least 1 bit wide!");
      assert (CW_RT_MAX <= 63) else $fatal(1, "Any counter can be at most 63 bits wide!");
    end
    if (CAP_EXCL) begin
      assert (CW_EXCL >= 1)
        else $fatal(1, "The exclusive access counter must be at least 1 bit wide!");
      assert (CW_EXCL <= 63) else $fatal(1, "Any counter can be at most 63 bits wide!");
    end
    if (CAP_ATOP) begin
      assert (CW_ATOP >= 1)
        else $fatal(1, "The atomic operations counter must be at least 1 bit wide!");
      assert (CW_ATOP <= 63) else $fatal(1, "Any counter can be at most 63 bits wide!");
    end
    assert (!CAP_TX_DAT) else $fatal(1, "The data transferred capability is not implemented yet!");
    assert (!CAP_FL_DAT) else $fatal(1, "The data in flight capability is not implemented yet!");
    assert (!CAP_RT) else $fatal(1, "The round trip capability is not implemented yet!");
  end
`endif
// pragma translate_on

endmodule

module apm_cnt_to_apb_reg #(
  parameter int unsigned CW = 0
) (
  input  logic [CW-1:0] cnt_i,
  input  logic          oflw_i,
  output logic [63:0]   reg_o
);
  assign reg_o[63]    = oflw_i;
  assign reg_o[62:0]  = {{63-CW{1'b0}}, cnt_i};
endmodule
