// Copyright (c) 2024 ETH Zurich and University of Bologna.
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
// - Tim Fischer <fischeti@iis.ee.ethz.ch>

// Description: Testbench for `axi_to_apb`.
//
// A full-AXI random master drives the DUT, whose APB master ports are attached to four behavioural
// APB slaves with different timing: an ideal (0-wait), a slow (fixed-wait), a random-wait, and an
// error slave. The first three are memory-backed, so `DUT + memory slaves` behaves as an AXI memory
// and an `axi_scoreboard` on the AXI port checks end-to-end data integrity (address mapping, bank
// placement, strobe masking, burst handling). The random master only targets the three memory
// slaves; the error slave and an unmapped address are exercised by a few directed transactions that
// check the error / decode-miss responses. APB-protocol legality is checked with assertions.

`include "axi/typedef.svh"
`include "axi/assign.svh"

module tb_axi_to_apb #(
  // Swept externally over {32, 64} to cover NumBanks = 1 and 2 (with ApbDataWidth = 32).
  parameter int unsigned TbAxiDataWidth = 32'd64
);

  // Timing
  localparam time CyclTime = 10ns;
  localparam time ApplTime =  2ns;
  localparam time TestTime =  8ns;

  // Random master transaction counts
  localparam int unsigned NoWrites = 2000;
  localparam int unsigned NoReads  = 2000;

  // Widths. Keep AxiAddrWidth == ApbAddrWidth so the decode (full AXI address) and the APB memories
  // (truncated `paddr`) stay consistent for the scoreboard, i.e. no truncation aliasing.
  localparam int unsigned AxiAddrWidth = 32'd32;
  localparam int unsigned ApbAddrWidth = 32'd32;
  localparam int unsigned ApbDataWidth = 32'd32;
  localparam int unsigned AxiIdWidth   = 32'd4;
  localparam int unsigned AxiUserWidth = 32'd2;
  localparam int unsigned AxiStrbWidth = TbAxiDataWidth/8;

  localparam int unsigned NoApbSlaves = 32'd4;
  localparam int unsigned NoRules     = NoApbSlaves;

  // APB slave indices / behaviour
  localparam int unsigned IdealSlv  = 0;
  localparam int unsigned SlowSlv   = 1;
  localparam int unsigned RandSlv   = 2;
  localparam int unsigned ErrSlv    = 3;

  typedef axi_pkg::xbar_rule_32_t rule_t; // {idx, start_addr, end_addr}, 32-bit address

  // One 4 KiB page per slave; 4 KiB alignment guarantees a burst never crosses a slave boundary.
  localparam rule_t [NoRules-1:0] AddrMap = '{
    '{idx: 32'd3, start_addr: 32'h0000_3000, end_addr: 32'h0000_4000}, // error
    '{idx: 32'd2, start_addr: 32'h0000_2000, end_addr: 32'h0000_3000}, // random
    '{idx: 32'd1, start_addr: 32'h0000_1000, end_addr: 32'h0000_2000}, // slow
    '{idx: 32'd0, start_addr: 32'h0000_0000, end_addr: 32'h0000_1000}  // ideal
  };
  localparam logic [AxiAddrWidth-1:0] MemLo   = 32'h0000_0000; // ideal+slow+random span
  localparam logic [AxiAddrWidth-1:0] MemHi   = 32'h0000_3000;
  localparam logic [AxiAddrWidth-1:0] ErrAddr = 32'h0000_3040; // inside error slave
  localparam logic [AxiAddrWidth-1:0] DecAddr = 32'h0000_8000; // unmapped

  // APB request/response structs (as expected by `axi_to_apb`)
  typedef logic [ApbAddrWidth-1:0]   apb_addr_t;
  typedef logic [ApbDataWidth-1:0]   apb_data_t;
  typedef logic [ApbDataWidth/8-1:0] apb_strb_t;

  typedef struct packed {
    apb_addr_t      paddr;
    axi_pkg::prot_t pprot;
    logic           psel;
    logic           penable;
    logic           pwrite;
    apb_data_t      pwdata;
    apb_strb_t      pstrb;
  } apb_req_t;

  typedef struct packed {
    logic      pready;
    apb_data_t prdata;
    logic      pslverr;
  } apb_resp_t;

  // Full AXI types
  typedef logic [AxiAddrWidth-1:0]     axi_addr_t;
  typedef logic [TbAxiDataWidth-1:0]   axi_data_t;
  typedef logic [AxiIdWidth-1:0]       axi_id_t;
  typedef logic [AxiStrbWidth-1:0]     axi_strb_t;
  typedef logic [AxiUserWidth-1:0]     axi_user_t;

  `AXI_TYPEDEF_ALL(axi, axi_addr_t, axi_id_t, axi_data_t, axi_strb_t, axi_user_t)

  // -----------------------------------------------------------------------------------------------
  // Clock / reset
  // -----------------------------------------------------------------------------------------------
  logic clk, rst_n;
  logic end_of_sim;

  clk_rst_gen #(
    .ClkPeriod    ( CyclTime ),
    .RstClkCycles ( 5        )
  ) i_clk_gen (
    .clk_o  ( clk   ),
    .rst_no ( rst_n )
  );

  // -----------------------------------------------------------------------------------------------
  // AXI master interface + driver + scoreboard monitor
  // -----------------------------------------------------------------------------------------------
  AXI_BUS_DV #(
    .AXI_ADDR_WIDTH ( AxiAddrWidth   ),
    .AXI_DATA_WIDTH ( TbAxiDataWidth ),
    .AXI_ID_WIDTH   ( AxiIdWidth     ),
    .AXI_USER_WIDTH ( AxiUserWidth   )
  ) master_dv (clk);

  AXI_BUS #(
    .AXI_ADDR_WIDTH ( AxiAddrWidth   ),
    .AXI_DATA_WIDTH ( TbAxiDataWidth ),
    .AXI_ID_WIDTH   ( AxiIdWidth     ),
    .AXI_USER_WIDTH ( AxiUserWidth   )
  ) master ();
  `AXI_ASSIGN(master, master_dv)

  axi_req_t  axi_req;
  axi_resp_t axi_resp;
  `AXI_ASSIGN_TO_REQ(axi_req, master)
  `AXI_ASSIGN_FROM_RESP(master, axi_resp)

  apb_req_t  [NoApbSlaves-1:0] apb_req;
  apb_resp_t [NoApbSlaves-1:0] apb_resp;

  typedef axi_test::axi_rand_master #(
    .AW ( AxiAddrWidth   ), .DW ( TbAxiDataWidth ), .IW ( AxiIdWidth ), .UW ( AxiUserWidth ),
    .TA ( ApplTime       ), .TT ( TestTime       ),
    .MAX_READ_TXNS  ( 4 ), .MAX_WRITE_TXNS ( 4 ),
    .AXI_MAX_BURST_LEN ( 16 ),
    // INCR only (`axi_to_detailed_mem` restriction); no atomics/exclusives.
    .AXI_BURST_FIXED ( 1'b0 ), .AXI_BURST_INCR ( 1'b1 ), .AXI_BURST_WRAP ( 1'b0 ),
    .AXI_ATOPS ( 1'b0 ), .AXI_EXCLS ( 1'b0 ),
    // Master-side backpressure.
    .AX_MIN_WAIT_CYCLES ( 0 ), .AX_MAX_WAIT_CYCLES ( 5 ),
    .W_MIN_WAIT_CYCLES  ( 0 ), .W_MAX_WAIT_CYCLES  ( 3 ),
    .RESP_MIN_WAIT_CYCLES ( 0 ), .RESP_MAX_WAIT_CYCLES ( 8 )
  ) axi_rand_master_t;

  typedef axi_test::axi_driver #(
    .AW ( AxiAddrWidth ), .DW ( TbAxiDataWidth ), .IW ( AxiIdWidth ), .UW ( AxiUserWidth ),
    .TA ( ApplTime ), .TT ( TestTime )
  ) axi_drv_t;

  axi_rand_master_t axi_rand_master = new (master_dv);

  // Directed single-beat write, checks the B response.
  task automatic directed_write(input axi_addr_t addr, input axi_pkg::resp_t exp);
    automatic axi_drv_t::ax_beat_t ax = new;
    automatic axi_drv_t::w_beat_t  w  = new;
    automatic axi_drv_t::b_beat_t  b;
    ax.ax_addr  = addr;
    ax.ax_id    = '0;
    ax.ax_len   = '0;
    ax.ax_size  = axi_pkg::size_t'($clog2(AxiStrbWidth));
    ax.ax_burst = axi_pkg::BURST_INCR;
    w.w_data    = {(TbAxiDataWidth/32){32'hC0FF_EE00}};
    w.w_strb    = '1;
    w.w_last    = 1'b1;
    fork
      axi_rand_master.drv.send_aw(ax);
      axi_rand_master.drv.send_w(w);
    join
    axi_rand_master.drv.recv_b(b);
    assert (b.b_resp == exp) else
      $error("directed_write @%0h: expected B resp %0d, got %0d", addr, exp, b.b_resp);
  endtask

  // Directed single-beat read, checks the R response.
  task automatic directed_read(input axi_addr_t addr, input axi_pkg::resp_t exp);
    automatic axi_drv_t::ax_beat_t ax = new;
    automatic axi_drv_t::r_beat_t  r;
    ax.ax_addr  = addr;
    ax.ax_id    = '0;
    ax.ax_len   = '0;
    ax.ax_size  = axi_pkg::size_t'($clog2(AxiStrbWidth));
    ax.ax_burst = axi_pkg::BURST_INCR;
    axi_rand_master.drv.send_ar(ax);
    axi_rand_master.drv.recv_r(r);
    assert (r.r_resp == exp) else
      $error("directed_read @%0h: expected R resp %0d, got %0d", addr, exp, r.r_resp);
  endtask

  initial begin : proc_stimuli
    end_of_sim <= 1'b0;
    axi_rand_master.reset();
    // Random traffic only hits the three memory slaves.
    axi_rand_master.add_memory_region(MemLo, MemHi, axi_pkg::WTHRU_NOALLOCATE);
    @(posedge rst_n);
    repeat (5) @(posedge clk);

    // Directed error / decode-miss checks (this DUT answers both with SLVERR).
    directed_write(ErrAddr, axi_pkg::RESP_SLVERR); // error slave
    directed_read (ErrAddr, axi_pkg::RESP_SLVERR);
    directed_write(DecAddr, axi_pkg::RESP_SLVERR); // unmapped address
    directed_read (DecAddr, axi_pkg::RESP_SLVERR);

    // Randomized data-integrity + backpressure run.
    axi_rand_master.run(NoReads, NoWrites);

    end_of_sim <= 1'b1;
    repeat (20) @(posedge clk);
    $display("[tb_axi_to_apb] finished (AxiDataWidth=%0d, NumBanks=%0d).",
             TbAxiDataWidth, TbAxiDataWidth/ApbDataWidth);
    $stop();
  end

  // Watchdog: fail instead of hanging on a deadlock.
  initial begin : proc_watchdog
    repeat (32'd5_000_000) @(posedge clk);
    if (!end_of_sim) $fatal(1, "[tb_axi_to_apb] timeout - possible deadlock.");
  end

  // -----------------------------------------------------------------------------------------------
  // Scoreboard (end-to-end data integrity on the AXI side)
  // -----------------------------------------------------------------------------------------------
  AXI_BUS_DV #(
    .AXI_ADDR_WIDTH ( AxiAddrWidth   ),
    .AXI_DATA_WIDTH ( TbAxiDataWidth ),
    .AXI_ID_WIDTH   ( AxiIdWidth     ),
    .AXI_USER_WIDTH ( AxiUserWidth   )
  ) monitor_dv (clk);
  `AXI_ASSIGN_MONITOR(monitor_dv, master)

  typedef axi_test::axi_scoreboard #(
    .IW ( AxiIdWidth     ), .AW ( AxiAddrWidth ), .DW ( TbAxiDataWidth ),
    .UW ( AxiUserWidth   ), .TT ( TestTime     )
  ) axi_scoreboard_t;
  axi_scoreboard_t axi_scoreboard = new(monitor_dv);
  initial begin : proc_scoreboard
    axi_scoreboard.enable_all_checks();
    @(posedge rst_n);
    axi_scoreboard.monitor();
  end

  // -----------------------------------------------------------------------------------------------
  // DUT
  // -----------------------------------------------------------------------------------------------
  axi_to_apb #(
    .NoApbSlaves  ( NoApbSlaves    ),
    .NoRules      ( NoRules        ),
    .AxiAddrWidth ( AxiAddrWidth   ),
    .AxiDataWidth ( TbAxiDataWidth ),
    .AxiIdWidth   ( AxiIdWidth     ),
    .AxiUserWidth ( AxiUserWidth   ),
    .ApbAddrWidth ( ApbAddrWidth   ),
    .ApbDataWidth ( ApbDataWidth   ),
    .axi_req_t    ( axi_req_t      ),
    .axi_resp_t   ( axi_resp_t     ),
    .apb_req_t    ( apb_req_t      ),
    .apb_resp_t   ( apb_resp_t     ),
    .rule_t       ( rule_t         )
  ) i_dut (
    .clk_i      ( clk      ),
    .rst_ni     ( rst_n    ),
    .test_i     ( 1'b0     ),
    .axi_req_i  ( axi_req  ),
    .axi_resp_o ( axi_resp ),
    .apb_req_o  ( apb_req  ),
    .apb_resp_i ( apb_resp ),
    .addr_map_i ( AddrMap  )
  );

  // -----------------------------------------------------------------------------------------------
  // APB slaves: ideal, slow, random (memory-backed) and error.
  // -----------------------------------------------------------------------------------------------
  for (genvar i = 0; i < NoApbSlaves; i++) begin : gen_apb_slv
    localparam bit          IsErr     = (i == ErrSlv);
    localparam bit          IsRand    = (i == RandSlv);
    localparam int unsigned FixedWait = (i == SlowSlv) ? 4 : 0;
    tb_apb_mem_slave #(
      .AddrWidth  ( ApbAddrWidth ),
      .DataWidth  ( ApbDataWidth ),
      .FixedWait  ( FixedWait    ),
      .Random     ( IsRand       ),
      .Error      ( IsErr        ),
      .apb_req_t  ( apb_req_t    ),
      .apb_resp_t ( apb_resp_t   )
    ) i_apb_slv (
      .clk_i      ( clk         ),
      .rst_ni     ( rst_n       ),
      .apb_req_i  ( apb_req[i]  ),
      .apb_resp_o ( apb_resp[i] )
    );
  end

  // -----------------------------------------------------------------------------------------------
  // APB protocol assertions (per slave)
  // -----------------------------------------------------------------------------------------------
  // pragma translate_off
  `ifndef VERILATOR
  default disable iff (!rst_n);
  for (genvar i = 0; i < NoApbSlaves; i++) begin : gen_apb_assertions
    sequence APB_SETUP;  apb_req[i].psel && !apb_req[i].penable; endsequence
    sequence APB_ACCESS; apb_req[i].psel &&  apb_req[i].penable; endsequence
    sequence APB_TRANSFER; APB_SETUP ##1 APB_ACCESS; endsequence

    apb_complete:   assert property ( @(posedge clk) (APB_SETUP |-> APB_TRANSFER));
    apb_penable:    assert property ( @(posedge clk)
        (apb_req[i].penable && apb_req[i].psel && apb_resp[i].pready |=> (!apb_req[i].penable)));
    control_stable: assert property ( @(posedge clk)
        (APB_TRANSFER |-> $stable({apb_req[i].pwrite, apb_req[i].paddr})));
    write_stable:   assert property ( @(posedge clk)
        ((apb_req[i].penable && apb_req[i].pwrite) |-> $stable(apb_req[i].pwdata)));
    strb_stable:    assert property ( @(posedge clk)
        ((apb_req[i].penable && apb_req[i].pwrite) |-> $stable(apb_req[i].pstrb)));
  end
  `endif
  // pragma translate_on

  // -----------------------------------------------------------------------------------------------
  // Light functional coverage: burst length, size, and strobe pattern.
  // -----------------------------------------------------------------------------------------------
  // pragma translate_off
  `ifndef VERILATOR
  covergroup cg_ax @(posedge clk iff (axi_req.aw_valid && axi_resp.aw_ready));
    cp_len:  coverpoint axi_req.aw.len  { bins single = {0}; bins short = {[1:3]}; bins long = {[4:$]}; }
    cp_size: coverpoint axi_req.aw.size;
  endgroup
  covergroup cg_w @(posedge clk iff (axi_req.w_valid && axi_resp.w_ready));
    cp_strb: coverpoint ((axi_req.w.strb == '0) ? 2'd0 : (&axi_req.w.strb) ? 2'd2 : 2'd1) {
      bins zero = {0}; bins partial = {1}; bins full = {2};
    }
  endgroup
  cg_ax i_cg_ax = new;
  cg_w  i_cg_w  = new;
  `endif
  // pragma translate_on

endmodule

// -------------------------------------------------------------------------------------------------
// Behavioural APB slave.
//   - `Error`  : always answers with `pslverr`, stores nothing (0-wait).
//   - `Random` : asserts `pready` on a random cycle during the access phase.
//   - else     : asserts `pready` after `FixedWait` access cycles (0 = ideal).
// Memory-backed (except the error slave): stores `pwdata` under `pstrb`, returns it on reads.
// -------------------------------------------------------------------------------------------------
module tb_apb_mem_slave #(
  parameter int unsigned AddrWidth  = 32,
  parameter int unsigned DataWidth  = 32,
  parameter int unsigned FixedWait  = 0,
  parameter bit          Random     = 1'b0,
  parameter bit          Error      = 1'b0,
  parameter type         apb_req_t  = logic,
  parameter type         apb_resp_t = logic
) (
  input  logic      clk_i,
  input  logic      rst_ni,
  input  apb_req_t  apb_req_i,
  output apb_resp_t apb_resp_o
);
  typedef logic [AddrWidth-1:0] addr_t;
  typedef logic [DataWidth-1:0] data_t;

  data_t       mem [addr_t]; // word-addressed by `paddr`
  logic        in_access;
  logic        pready;
  int unsigned wait_cnt;
  logic        rand_bit;
  data_t       rd_data;

  assign in_access = apb_req_i.psel & apb_req_i.penable;

  // Wait-state counter: counts access cycles until the transfer completes.
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      wait_cnt <= 0;
      rand_bit <= 1'b0;
    end else begin
      rand_bit <= $urandom_range(0, 1);
      wait_cnt <= (in_access && !pready) ? wait_cnt + 1 : 0;
    end
  end

  always_comb begin
    pready = 1'b0;
    if (in_access) begin
      if      (Error)  pready = 1'b1;              // error slave completes immediately
      else if (Random) pready = rand_bit;
      else             pready = (wait_cnt >= FixedWait);
    end
  end

  always_comb begin
    rd_data = '0;
    if (!Error && apb_req_i.psel && mem.exists(apb_req_i.paddr)) rd_data = mem[apb_req_i.paddr];
  end

  assign apb_resp_o.pready  = pready;
  assign apb_resp_o.prdata  = rd_data;
  assign apb_resp_o.pslverr = Error;

  // Commit writes (byte-strobed) on the completing access cycle.
  always_ff @(posedge clk_i) begin
    if (in_access && pready && apb_req_i.pwrite && !Error) begin
      automatic data_t cur = mem.exists(apb_req_i.paddr) ? mem[apb_req_i.paddr] : '0;
      for (int b = 0; b < DataWidth/8; b++) begin
        if (apb_req_i.pstrb[b]) cur[8*b +: 8] = apb_req_i.pwdata[8*b +: 8];
      end
      mem[apb_req_i.paddr] = cur;
    end
  end

endmodule
