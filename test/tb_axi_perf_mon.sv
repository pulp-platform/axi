// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

`include "apb/assign.svh"
`include "axi/assign.svh"

`define max(a, b) a > b ? a : b;

module tb_axi_perf_mon #(
  // DUT Parameters
  parameter int unsigned  N_AXI = 2,
  parameter int unsigned  N_READ_TXNS = 1000,
  parameter int unsigned  N_WRITE_TXNS = 900,
  parameter int unsigned  AXI_MAX_READ_TXNS = 100,
  parameter int unsigned  AXI_MAX_WRITE_TXNS = 100,
  // TB Parameters
  parameter time          TCLK = 10ns,
  parameter time          TA = TCLK * 1/4,
  parameter time          TT = TCLK * 3/4,
  parameter int unsigned  REQ_MIN_WAIT_CYCLES = 0,
  parameter int unsigned  REQ_MAX_WAIT_CYCLES = 10,
  parameter int unsigned  RESP_MIN_WAIT_CYCLES = 0,
  parameter int unsigned  RESP_MAX_WAIT_CYCLES = REQ_MAX_WAIT_CYCLES/2
);

  timeunit 1ns;
  timeprecision 10ps;

  localparam int unsigned AW = 64;
  localparam int unsigned DW = 64;
  localparam int unsigned IW = 4;
  localparam int unsigned UW = 2;
  localparam int unsigned AXI_STRB_WIDTH = DW / 8;

  import axi_pkg::atop_t;
  typedef logic [IW-1:0] id_t;
  import axi_pkg::len_t;
  import axi_pkg::resp_t;
  import axi_pkg::size_t;
  import axi_pkg::ATOP_NONE;
  import axi_pkg::ATOP_ATOMICSTORE;
  import axi_pkg::ATOP_ATOMICLOAD;
  import axi_pkg::ATOP_ATOMICSWAP;
  import axi_pkg::ATOP_ATOMICCMP;
  import axi_pkg::RESP_EXOKAY;

  logic clk,
        rst_n;

  clk_rst_gen #(
    .CLK_PERIOD     (TCLK),
    .RST_CLK_CYCLES (5)
  ) i_clk_rst_gen (
    .clk_o  (clk),
    .rst_no (rst_n)
  );

  AXI_BUS_DV #(
    .AXI_ADDR_WIDTH (AW),
    .AXI_DATA_WIDTH (DW),
    .AXI_ID_WIDTH   (IW),
    .AXI_USER_WIDTH (UW)
  ) axi_dv_mst [N_AXI-1:0] (
    .clk_i  (clk)
  );

  AXI_BUS #(
    .AXI_ADDR_WIDTH (AW),
    .AXI_DATA_WIDTH (DW),
    .AXI_ID_WIDTH   (IW),
    .AXI_USER_WIDTH (UW)
  ) axi [N_AXI-1:0] ();

  AXI_BUS_DV #(
    .AXI_ADDR_WIDTH (AW),
    .AXI_DATA_WIDTH (DW),
    .AXI_ID_WIDTH   (IW),
    .AXI_USER_WIDTH (UW)
  ) axi_dv_slv [N_AXI-1:0] (
    .clk_i  (clk)
  );

  APB apb ();
  APB_DV apb_dv (
    .clk_i (clk)
  );
  `APB_ASSIGN(apb, apb_dv);

  for (genvar i = 0; i < N_AXI; i++) begin: gen_axi_assign
    `AXI_ASSIGN(axi[i], axi_dv_mst[i]);
    `AXI_ASSIGN(axi_dv_slv[i], axi[i]);
  end

  logic   [N_AXI-1:0] axi_clk,    axi_rst_n,
                      ar_valid,   ar_ready,   ar_lock,
                      aw_valid,   aw_ready,   aw_lock,
                      r_valid,    r_ready,    r_last,
                      w_valid,    w_ready,    w_last,
                      b_valid,    b_ready;

  atop_t  [N_AXI-1:0] aw_atop;

  id_t    [N_AXI-1:0] ar_id,
                      aw_id,
                      r_id,
                      b_id;

  len_t   [N_AXI-1:0] ar_len,
                      aw_len;

  resp_t  [N_AXI-1:0] b_resp;

  size_t  [N_AXI-1:0] ar_size,
                      aw_size;

  for (genvar i = 0; i < N_AXI; i++) begin: gen_axi_concat
    assign axi_clk[i]    = clk;
    assign axi_rst_n[i]  = rst_n;
    assign ar_id[i]      = axi[i].ar_id;
    assign ar_len[i]     = axi[i].ar_len;
    assign ar_size[i]    = axi[i].ar_size;
    assign ar_lock[i]    = axi[i].ar_lock;
    assign ar_valid[i]   = axi[i].ar_valid;
    assign ar_ready[i]   = axi[i].ar_ready;
    assign aw_id[i]      = axi[i].aw_id;
    assign aw_len[i]     = axi[i].aw_len;
    assign aw_size[i]    = axi[i].aw_size;
    assign aw_lock[i]    = axi[i].aw_lock;
    assign aw_atop[i]    = axi[i].aw_atop;
    assign aw_valid[i]   = axi[i].aw_valid;
    assign aw_ready[i]   = axi[i].aw_ready;
    assign r_id[i]       = axi[i].r_id;
    assign r_last[i]     = axi[i].r_last;
    assign r_valid[i]    = axi[i].r_valid;
    assign r_ready[i]    = axi[i].r_ready;
    assign w_last[i]     = axi[i].w_last;
    assign w_valid[i]    = axi[i].w_valid;
    assign w_ready[i]    = axi[i].w_ready;
    assign b_id[i]       = axi[i].b_id;
    assign b_resp[i]     = axi[i].b_resp;
    assign b_valid[i]    = axi[i].b_valid;
    assign b_ready[i]    = axi[i].b_ready;
  end

  axi_perf_mon #(
    .N_MON          (N_AXI),
    .IW             (IW),
    .CAP_HS         (1'b1),
    .CAP_FL_TXN     (1'b1),
    .CAP_STALL      (1'b1),
    .CAP_EXCL       (1'b1),
    .CAP_ATOP       (1'b1),
    .CW_CLK         (56),
    .CW_HS_CMD      (32),
    .CW_HS_DAT      (32),
    .CW_FL_TXN_ACC  (63),
    .CW_FL_TXN_MAX  (10),
    .CW_STALL_CMD   (56),
    .CW_STALL_DAT   (56),
    .CW_STALL_MAX   (16),
    .CW_EXCL        (10),
    .CW_ATOP        (14)
  ) dut (
    .pclk_i     (clk),
    .preset_ni  (rst_n),
    .paddr_i    (apb.paddr),
    .pprot_i    (apb.pprot),
    .psel_i     (apb.psel),
    .penable_i  (apb.penable),
    .pwrite_i   (apb.pwrite),
    .pwdata_i   (apb.pwdata),
    .pstrb_i    (apb.pstrb),
    .pready_o   (apb.pready),
    .prdata_o   (apb.prdata),
    .pslverr_o  (apb.pslverr),

    .clk_axi_i  (axi_clk),
    .rst_axi_ni (axi_rst_n),
    .ar_id_i    (ar_id),
    .ar_len_i   (ar_len),
    .ar_size_i  (ar_size),
    .ar_lock_i  (ar_lock),
    .ar_valid_i (ar_valid),
    .ar_ready_i (ar_ready),
    .aw_id_i    (aw_id),
    .aw_len_i   (aw_len),
    .aw_size_i  (aw_size),
    .aw_lock_i  (aw_lock),
    .aw_atop_i  (aw_atop),
    .aw_valid_i (aw_valid),
    .aw_ready_i (aw_ready),
    .r_id_i     (r_id),
    .r_last_i   (r_last),
    .r_valid_i  (r_valid),
    .r_ready_i  (r_ready),
    .w_last_i   (w_last),
    .w_valid_i  (w_valid),
    .w_ready_i  (w_ready),
    .b_id_i     (b_id),
    .b_resp_i   (b_resp),
    .b_valid_i  (b_valid),
    .b_ready_i  (b_ready)
  );

  logic mst_done = 1'b0;
  logic init_done = 1'b0;
  logic readout_done = 1'b0;

  // Model expected state
  longint unsigned  hs_cnt_ar = 0,
                    hs_cnt_aw = 0,
                    hs_cnt_r = 0,
                    hs_cnt_w = 0,
                    fl_txn_max_r = 0,
                    fl_txn_max_w = 0,
                    fl_txn_acc_r = 0,
                    fl_txn_acc_w = 0,
                    stall_cnt_ar = 0,
                    stall_cnt_aw = 0,
                    stall_cnt_b = 0,
                    stall_cnt_r = 0,
                    stall_cnt_w = 0,
                    stall_max_ar = 0,
                    stall_max_aw = 0,
                    stall_max_b = 0,
                    stall_max_r = 0,
                    stall_max_w = 0,
                    excl_cnt_ar = 0,
                    excl_cnt_aw = 0,
                    excl_cnt_b = 0,
                    atop_cnt_st = 0,
                    atop_cnt_ld = 0,
                    atop_cnt_swp = 0,
                    atop_cnt_cmp = 0;

  initial begin
    automatic longint unsigned  fl_txn_cnt_r = 0,
                                fl_txn_cnt_w = 0,
                                stall_cur_ar = 0,
                                stall_cur_aw = 0,
                                stall_cur_r = 0,
                                stall_cur_w = 0,
                                stall_cur_b = 0;
    automatic bit [2**IW-1:0]   fl_atop_b = '0,
                                fl_atop_r = '0;
    wait (rst_n);
    wait (init_done);
    forever begin
      #(TT);
      fl_txn_acc_r += fl_txn_cnt_r;
      fl_txn_acc_w += fl_txn_cnt_w;
      // AR
      if (axi[0].ar_valid) begin
        if (axi[0].ar_ready) begin
          hs_cnt_ar++;
          fl_txn_cnt_r++;
          stall_cur_ar = 0;
          if (axi[0].ar_lock) excl_cnt_ar++;
        end else begin
          stall_cnt_ar++;
          stall_cur_ar++;
        end
      end
      // AW
      if (axi[0].aw_valid) begin
        if (axi[0].aw_ready) begin
          hs_cnt_aw++;
          stall_cur_aw = 0;
          if (axi[0].aw_lock) excl_cnt_aw++;
          if (axi[0].aw_atop[5:4] == ATOP_NONE) begin
            fl_txn_cnt_w++;
          end else begin
            fl_atop_b[axi[0].aw_id] = 1'b1;
            if (axi[0].aw_atop[5]) begin
              fl_atop_r[axi[0].aw_id] = 1'b1;
            end
            casex (axi[0].aw_atop)
              {ATOP_ATOMICSTORE, 4'bxxxx}:  atop_cnt_st++;
              {ATOP_ATOMICLOAD,  4'bxxxx}:  atop_cnt_ld++;
              ATOP_ATOMICSWAP:              atop_cnt_swp++;
              ATOP_ATOMICCMP:               atop_cnt_cmp++;
            endcase
          end
        end else begin
          stall_cnt_aw++;
          stall_cur_aw++;
        end
      end
      // R
      if (axi[0].r_valid) begin
        if (axi[0].r_ready) begin
          hs_cnt_r++;
          if (axi[0].r_last) begin
            if (fl_atop_r[axi[0].r_id]) begin
              fl_atop_r[axi[0].r_id] = 1'b0;
            end else begin
              fl_txn_cnt_r--;
            end
          end
          stall_cur_r = 0;
        end else begin
          stall_cnt_r++;
          stall_cur_r++;
        end
      end
      // W
      if (axi[0].w_valid) begin
        if (axi[0].w_ready) begin
          hs_cnt_w++;
          stall_cur_w = 0;
        end else begin
          stall_cnt_w++;
          stall_cur_w++;
        end
      end
      // B
      if (axi[0].b_valid) begin
        if (axi[0].b_ready) begin
          if (fl_atop_b[axi[0].b_id]) begin
            fl_atop_b[axi[0].b_id] = 1'b0;
          end else begin
            fl_txn_cnt_w--;
          end
          stall_cur_b = 0;
          if (axi[0].b_resp == RESP_EXOKAY) excl_cnt_b++;
        end else begin
          stall_cnt_b++;
          stall_cur_b++;
        end
      end
      fl_txn_max_r = `max(fl_txn_max_r, fl_txn_cnt_r);
      fl_txn_max_w = `max(fl_txn_max_w, fl_txn_cnt_w);
      stall_max_ar = `max(stall_max_ar, stall_cur_ar);
      stall_max_aw = `max(stall_max_aw, stall_cur_aw);
      stall_max_r = `max(stall_max_r, stall_cur_r);
      stall_max_w = `max(stall_max_w, stall_cur_w);
      stall_max_b = `max(stall_max_b, stall_cur_b);
      @(posedge clk);
    end
  end

  // APB Master
  apb_test::apb_driver #(.TA(TA), .TT(TT)) apb_master = new(apb_dv);
  task apb_read64(input logic [31:0] addr, output logic [63:0] rdata);
    automatic logic slverr;
    apb_master.read(addr, rdata[31:0], slverr); assert (!slverr);
    apb_master.read(addr + 4, rdata[63:32], slverr); assert (!slverr);
  endtask
  typedef enum logic [2:0] { CMP_EQ, CMP_LEQ, CMP_LT, CMP_GEQ, CMP_GT } cmp_t;
  task apb_check_counter(input logic [31:0] addr, input longint unsigned exp);
    automatic logic [63:0] rdata;
    apb_read64(addr, rdata);
    assert (rdata == exp) else $error("%016x != %016x at address %08x", rdata, exp, addr);
  endtask
  initial begin
    automatic logic slverr;
    automatic logic [31:0] rdata;
    apb_master.reset_master();
    wait (rst_n);
    // Check capabilities and enable monitor 0.
    apb_master.read(32'h0000_0000, rdata, slverr); assert (!slverr);
    assert (rdata[0] && rdata[1] && rdata[2] && rdata[5]);
    apb_master.write(32'h0000_0004, 32'h0000_0001, 4'b1111, slverr); assert (!slverr);
    init_done = 1'b1;
    // Wait for AXI transfers to complete.
    wait (mst_done);
    // Check counter results via APB against modeled counters.
    apb_check_counter(32'h0000_0010, hs_cnt_ar);
    apb_check_counter(32'h0000_0018, hs_cnt_aw);
    apb_check_counter(32'h0000_0020, hs_cnt_r);
    apb_check_counter(32'h0000_0028, hs_cnt_w);
    apb_check_counter(32'h0000_0030, fl_txn_acc_r);
    apb_check_counter(32'h0000_0038, fl_txn_max_r);
    apb_check_counter(32'h0000_0040, fl_txn_acc_w);
    apb_check_counter(32'h0000_0048, fl_txn_max_w);
    apb_check_counter(32'h0000_0080, stall_cnt_ar);
    apb_check_counter(32'h0000_0088, stall_max_ar);
    apb_check_counter(32'h0000_0090, stall_cnt_aw);
    apb_check_counter(32'h0000_0098, stall_max_aw);
    apb_check_counter(32'h0000_00A0, stall_cnt_r);
    apb_check_counter(32'h0000_00A8, stall_max_r);
    apb_check_counter(32'h0000_00B0, stall_cnt_w);
    apb_check_counter(32'h0000_00B8, stall_max_w);
    apb_check_counter(32'h0000_00C0, stall_cnt_b);
    apb_check_counter(32'h0000_00C8, stall_max_b);
    apb_check_counter(32'h0000_0100, excl_cnt_ar);
    apb_check_counter(32'h0000_0108, excl_cnt_aw);
    apb_check_counter(32'h0000_0110, excl_cnt_b);
    apb_check_counter(32'h0000_0118, atop_cnt_st);
    apb_check_counter(32'h0000_0120, atop_cnt_ld);
    apb_check_counter(32'h0000_0128, atop_cnt_swp);
    apb_check_counter(32'h0000_0130, atop_cnt_cmp);
    readout_done = 1'b1;
  end

  // AXI Master
  axi_test::rand_axi_master #(
    .AW(AW), .DW(DW), .IW(IW), .UW(UW), .TA(TA), .TT(TT),
    .MAX_READ_TXNS        (AXI_MAX_READ_TXNS),
    .MAX_WRITE_TXNS       (AXI_MAX_WRITE_TXNS),
    .AX_MIN_WAIT_CYCLES   (REQ_MIN_WAIT_CYCLES),
    .AX_MAX_WAIT_CYCLES   (REQ_MAX_WAIT_CYCLES),
    .W_MIN_WAIT_CYCLES    (REQ_MIN_WAIT_CYCLES),
    .W_MAX_WAIT_CYCLES    (REQ_MAX_WAIT_CYCLES),
    .RESP_MIN_WAIT_CYCLES (RESP_MIN_WAIT_CYCLES),
    .RESP_MAX_WAIT_CYCLES (RESP_MAX_WAIT_CYCLES),
    .AXI_ATOPS            (1'b1),
    .AXI_EXCLS            (1'b1)
  ) axi_master = new(axi_dv_mst[0]);
  initial begin
    static logic [AW-1:0] addr_begin  = '0,
                          addr_end    = '1;
    axi_master.reset();
    wait (rst_n);
    wait (init_done);
    axi_master.run(N_READ_TXNS, N_WRITE_TXNS, addr_begin, addr_end);
    mst_done = 1'b1;
  end

  initial begin
    wait (readout_done);
    $display("TB completed after %0d read and %0d write transactions", N_READ_TXNS, N_WRITE_TXNS);
    $finish();
  end

  // AXI Slave
  axi_test::rand_axi_slave #(
    .AW(AW), .DW(DW), .IW(IW), .UW(UW), .TA(TA), .TT(TT),
    .AX_MIN_WAIT_CYCLES   (RESP_MIN_WAIT_CYCLES),
    .AX_MAX_WAIT_CYCLES   (RESP_MAX_WAIT_CYCLES),
    .R_MIN_WAIT_CYCLES    (RESP_MIN_WAIT_CYCLES),
    .R_MAX_WAIT_CYCLES    (RESP_MAX_WAIT_CYCLES),
    .RESP_MIN_WAIT_CYCLES (RESP_MIN_WAIT_CYCLES),
    .RESP_MAX_WAIT_CYCLES (RESP_MAX_WAIT_CYCLES)
  ) axi_slave = new(axi_dv_slv[0]);
  initial begin
    axi_slave.reset();
    wait (rst_n);
    wait (init_done);
    axi_slave.run();
  end

endmodule
