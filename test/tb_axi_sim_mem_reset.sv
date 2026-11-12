// Copyright (c) 2026 ETH Zurich and University of Bologna
// SPDX-License-Identifier: SHL-0.51

`include "axi/typedef.svh"

module tb_axi_sim_mem_reset;
  logic clk_i = 1'b0;
  logic rst_ni = 1'b0;
  always #5ns clk_i = ~clk_i;

  typedef logic [31:0] addr_t;
  typedef logic [31:0] data_t;
  typedef logic [3:0] id_t;
  typedef logic [3:0] strb_t;
  typedef logic user_t;
  `AXI_TYPEDEF_ALL(axi, addr_t, id_t, data_t, strb_t, user_t)

  axi_req_t [0:0] req;
  axi_resp_t [0:0] rsp;
  logic mon_w_valid, mon_r_valid;
  logic [31:0] mon_w_addr, mon_w_data;
  axi_pkg::len_t mon_w_beat_count;

  axi_sim_mem #(
    .AddrWidth (32),
    .DataWidth (32),
    .IdWidth   (4),
    .UserWidth (1),
    .axi_req_t (axi_req_t),
    .axi_rsp_t (axi_resp_t),
    .ApplDelay (2ns),
    .AcqDelay  (8ns)
  ) dut (
    .clk_i,
    .rst_ni,
    .axi_req_i (req),
    .axi_rsp_o (rsp),
    .mon_w_valid_o (mon_w_valid),
    .mon_w_addr_o (mon_w_addr),
    .mon_w_data_o (mon_w_data),
    .mon_w_beat_count_o (mon_w_beat_count),
    .mon_r_valid_o (mon_r_valid)
  );

  initial begin
    #1us;
    $fatal(1, "axi_sim_mem reset test timed out");
  end

  initial begin
    req = '0;
    dut.mem['h100] = 8'h78;
    dut.mem['h101] = 8'h56;
    dut.mem['h102] = 8'h34;
    dut.mem['h103] = 8'h12;
    #20ns;
    rst_ni = 1'b1;

    // Reset a read response stalled by the master.
    @(negedge clk_i);
    req[0].ar.addr = 'h40;
    req[0].ar.id = 'h3;
    req[0].ar.len = '0;
    req[0].ar.size = 3'd2;
    req[0].ar.burst = axi_pkg::BURST_INCR;
    req[0].ar_valid = 1'b1;
    do begin
      @(posedge clk_i);
      #1ps;
    end while (!rsp[0].ar_ready);
    #9ns;
    req[0].ar_valid = 1'b0;
    wait (rsp[0].r_valid);
    @(posedge clk_i);
    #(2ns);
    #0;
    rst_ni = 1'b0;
    #1ps;
    assert (!rsp[0].r_valid && !rsp[0].ar_ready && !mon_r_valid)
      else $fatal(1, "read state was not cleared by reset");
    req[0].aw.addr = 'h100;
    req[0].aw.id = 'h4;
    req[0].aw.len = '0;
    req[0].aw.size = 3'd2;
    req[0].aw.burst = axi_pkg::BURST_INCR;
    req[0].aw_valid = 1'b1;
    req[0].w.data = 'hdeadbeef;
    req[0].w.strb = '1;
    req[0].w.last = 1'b1;
    req[0].w_valid = 1'b1;
    repeat (3) begin
      @(posedge clk_i);
      #1ps;
      assert (!rsp[0].aw_ready && !rsp[0].w_ready && !rsp[0].ar_ready &&
              !rsp[0].b_valid && !rsp[0].r_valid)
        else $fatal(1, "request was accepted while reset was asserted");
    end
    @(negedge clk_i);
    req[0].aw_valid = 1'b0;
    req[0].w_valid = 1'b0;
    rst_ni = 1'b1;
    repeat (2) @(posedge clk_i);
    #1ps;
    assert (!rsp[0].b_valid && dut.mem['h100] == 8'h78 && dut.mem['h101] == 8'h56 &&
            dut.mem['h102] == 8'h34 && dut.mem['h103] == 8'h12)
      else $fatal(1, "reset-only write leaked past reset");

    // Reset after AW was accepted but before any W beat arrived.
    @(negedge clk_i);
    req[0].aw.addr = 'h80;
    req[0].aw.id = 'h5;
    req[0].aw.len = 1;
    req[0].aw.size = 3'd2;
    req[0].aw.burst = axi_pkg::BURST_INCR;
    req[0].aw_valid = 1'b1;
    do begin
      @(posedge clk_i);
      #1ps;
    end while (!rsp[0].aw_ready);
    #9ns;
    req[0].aw_valid = 1'b0;
    wait (rsp[0].w_ready);
    @(negedge clk_i);
    rst_ni = 1'b0;
    #1ns;
    assert (!rsp[0].w_ready && !rsp[0].b_valid && !mon_w_valid)
      else $fatal(1, "incomplete write state was not cleared by reset");
    repeat (2) @(posedge clk_i);
    @(negedge clk_i);
    rst_ni = 1'b1;
    repeat (2) @(posedge clk_i);
    #1ps;
    assert (!rsp[0].w_ready && !rsp[0].b_valid)
      else $fatal(1, "stale AW state after reset");

    // Reset a completed write response stalled by the master.
    @(negedge clk_i);
    req[0].aw.addr = 'hc0;
    req[0].aw.id = 'h7;
    req[0].aw.len = '0;
    req[0].aw.size = 3'd2;
    req[0].aw.burst = axi_pkg::BURST_INCR;
    req[0].aw_valid = 1'b1;
    do begin
      @(posedge clk_i);
      #1ps;
    end while (!rsp[0].aw_ready);
    #9ns;
    req[0].aw_valid = 1'b0;
    @(negedge clk_i);
    req[0].w.data = 'h12345678;
    req[0].w.strb = '1;
    req[0].w.last = 1'b1;
    req[0].w_valid = 1'b1;
    do begin
      @(posedge clk_i);
      #1ps;
    end while (!rsp[0].w_ready);
    #9ns;
    req[0].w_valid = 1'b0;
    wait (rsp[0].b_valid);
    assert (rsp[0].b.id == 4'h7) else $fatal(1, "wrong B response ID");
    #1ps;
    assert (mon_w_valid && mon_w_addr == 'hc0 && mon_w_data == 32'h12345678 &&
            mon_w_beat_count == 0)
      else $fatal(1, "write monitor did not preserve the captured transaction");
    @(negedge clk_i);
    rst_ni = 1'b0;
    #1ns;
    assert (!rsp[0].b_valid) else $fatal(1, "BVALID was not cleared by reset");
    repeat (2) @(posedge clk_i);
    @(negedge clk_i);
    rst_ni = 1'b1;
    repeat (2) @(posedge clk_i);
    #1ps;
    assert (!rsp[0].b_valid) else $fatal(1, "stale B response after reset");

    // A fresh request must still complete after repeated resets.
    @(negedge clk_i);
    req[0].ar.addr = 'h100;
    req[0].ar.id = 'h9;
    req[0].ar.len = '0;
    req[0].ar.size = 3'd2;
    req[0].ar.burst = axi_pkg::BURST_INCR;
    req[0].ar_valid = 1'b1;
    req[0].r_ready = 1'b1;
    do begin
      @(posedge clk_i);
      #1ps;
    end while (!rsp[0].ar_ready);
    #9ns;
    req[0].ar_valid = 1'b0;
    do begin
      @(posedge clk_i);
      #1ps;
    end while (!rsp[0].r_valid);
    assert (rsp[0].r.id == 4'h9 && rsp[0].r.last && rsp[0].r.data == 32'h12345678)
      else $fatal(1, "reset-only write modified memory");

    @(negedge clk_i);
    req[0].ar.addr = 'hc0;
    req[0].ar.id = 4'ha;
    req[0].ar.len = '0;
    req[0].ar.size = 3'd2;
    req[0].ar.burst = axi_pkg::BURST_INCR;
    req[0].ar_valid = 1'b1;
    do begin
      @(posedge clk_i);
      #1ps;
    end while (!rsp[0].ar_ready);
    #9ns;
    req[0].ar_valid = 1'b0;
    do begin
      @(posedge clk_i);
      #1ps;
    end while (!rsp[0].r_valid);
    assert (rsp[0].r.id == 4'ha && rsp[0].r.last && rsp[0].r.data == 32'h12345678)
      else $fatal(1, "memory contents did not survive reset");

    $display("PASS: axi_sim_mem reset clears outstanding transactions");
    $finish;
  end
endmodule
