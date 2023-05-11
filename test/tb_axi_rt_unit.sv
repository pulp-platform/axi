// Copyright (c) 2019 ETH Zurich and University of Bologna.
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
// - Thomas Benz <tbenz@ethz.ch>
// - Noah Huetter <huettern@ethz.ch>

// vsim -t 1ns -voptargs=+acc tb_axi_rt_unit; log -r /*;

`include "axi/typedef.svh"
`include "axi/assign.svh"

/// Testbench for the AXI RT unit
/// Codename `Mr Poopybutthole`
module tb_axi_rt_unit #(
  /// Number of write transfers
  parameter int unsigned NoWrites      = 32'd100,
  /// Number of read  transfers
  parameter int unsigned NoReads       = 32'd0,
  /// Number of outstanding AW from the master
  parameter int unsigned MaxAW         = 32'd2,
  /// Number of outstanding AR from the master
  parameter int unsigned MaxAR         = 32'd2,
  /// Number of outstanding AW from the burst splitter
  parameter int unsigned SplitterMaxAW = 32'd2,
  /// Number of outstanding AR from the burst splitter
  parameter int unsigned SplitterMaxAR = 32'd2,
  /// Atomic Support
  parameter bit EnAtop                 = 1'b0,
  /// Testbench timing
  parameter time CyclTime              = 10000ps,
  parameter time ApplTime              = 1ps,
  parameter time TestTime              = 9999ps,
  // AXI configuration
  parameter int unsigned AxiIdWidth    = 32'd2,
  parameter int unsigned AxiAddrWidth  = 32'd32,
  parameter int unsigned AxiDataWidth  = 32'd32,
  parameter int unsigned AxiUserWidth  = 32'd1
);

  /// Sim print config, how many transactions
  localparam int unsigned PrintTnx = 32'd100;

  // typedef
  typedef logic [AxiIdWidth-1    :0] id_t;
  typedef logic [AxiAddrWidth-1  :0] addr_t;
  typedef logic [AxiDataWidth-1  :0] data_t;
  typedef logic [AxiDataWidth/8-1:0] strb_t;
  typedef logic [AxiUserWidth-1  :0] user_t;

  `AXI_TYPEDEF_ALL(axi, addr_t, id_t, data_t, strb_t, user_t)

    /// rule type
  typedef struct packed {
    logic [7:0] idx;
    addr_t      start_addr;
    addr_t      end_addr;
  } rt_rule_t;

  /// Number of Address Rules
  localparam int unsigned NumAddrRegions = 32'd3;
  localparam int unsigned NumRules       = 32'd3;

  /// example rule
  localparam rt_rule_t [NumRules-1:0] RtAddrmap = '{
    '{ idx: 8'h00, start_addr: 'h00000000, end_addr: 'h00001000 },
    '{ idx: 8'h01, start_addr: 'h00001000, end_addr: 'h00002000 },
    '{ idx: 8'h02, start_addr: 'h00002000, end_addr: 'h00003000 }
  };

  /// Random AXI slave type
  typedef axi_test::axi_rand_master#(
      .AW                   ( AxiAddrWidth ),
      .DW                   ( AxiDataWidth ),
      .IW                   ( AxiIdWidth   ),
      .UW                   ( AxiUserWidth ),
      .TA                   ( ApplTime     ),
      .TT                   ( TestTime     ),
      .MAX_READ_TXNS        ( MaxAR        ),
      .MAX_WRITE_TXNS       ( MaxAW        ),
      .AX_MIN_WAIT_CYCLES   ( 32'd0        ),
      .AX_MAX_WAIT_CYCLES   ( 32'd0        ),
      .W_MIN_WAIT_CYCLES    ( 32'd0        ),
      .W_MAX_WAIT_CYCLES    ( 32'd0        ),
      .RESP_MIN_WAIT_CYCLES ( 32'd0        ),
      .RESP_MAX_WAIT_CYCLES ( 32'd0        ),
      .SIZE_ALIGN           ( 1'b0         ),
      .AXI_MAX_BURST_LEN    ( 32'd0        ),
      .TRAFFIC_SHAPING      ( 1'b0         ),
      .AXI_EXCLS            ( 1'b0         ),
      .AXI_ATOPS            ( EnAtop       ),
      .AXI_BURST_FIXED      ( 1'b0         ),
      .AXI_BURST_INCR       ( 1'b1         ),
      .AXI_BURST_WRAP       ( 1'b0         ),
      .UNIQUE_IDS           ( 1'b0         )
  ) axi_rand_master_t;

  typedef axi_test::axi_file_master#(
      .AW                   ( AxiAddrWidth ),
      .DW                   ( AxiDataWidth ),
      .IW                   ( AxiIdWidth   ),
      .UW                   ( AxiUserWidth ),
      .TA                   ( ApplTime     ),
      .TT                   ( TestTime     )
  ) axi_file_master_t;

  typedef axi_test::axi_driver #(
    .AW( AxiAddrWidth ),
    .DW( AxiDataWidth ),
    .IW( AxiIdWidth   ),
    .UW( AxiUserWidth ),
    .TA( ApplTime     ),
    .TT( TestTime     )
  ) drv_t;

  /// Random AXI slave type
  typedef axi_test::axi_rand_slave#(
      .AW                   ( AxiAddrWidth ),
      .DW                   ( AxiDataWidth ),
      .IW                   ( AxiIdWidth   ),
      .UW                   ( AxiUserWidth ),
      .TA                   ( ApplTime     ),
      .TT                   ( TestTime     ),
      .AX_MIN_WAIT_CYCLES   ( 32'd0        ),
      .AX_MAX_WAIT_CYCLES   ( 32'd0        ),
      .R_MIN_WAIT_CYCLES    ( 32'd0        ),
      .R_MAX_WAIT_CYCLES    ( 32'd0        ),
      .RESP_MIN_WAIT_CYCLES ( 32'd0        ),
      .RESP_MAX_WAIT_CYCLES ( 32'd0        ),
      .MAPPED               ( 1'b0         )
  ) axi_rand_slave_t;

  // -------------
  // DUT signals
  // -------------
  logic clk;
  logic rst_n;
  logic end_of_sim;

  int   unsigned total_num_reads;
  int   unsigned total_num_writes;

  AXI_BUS #(
    .AXI_ADDR_WIDTH ( AxiAddrWidth ),
    .AXI_DATA_WIDTH ( AxiDataWidth ),
    .AXI_ID_WIDTH   ( AxiIdWidth   ),
    .AXI_USER_WIDTH ( AxiUserWidth )
  ) master (), slave ();

  AXI_BUS_DV #(
      .AXI_ADDR_WIDTH ( AxiAddrWidth ),
      .AXI_DATA_WIDTH ( AxiDataWidth ),
      .AXI_ID_WIDTH   ( AxiIdWidth   ),
      .AXI_USER_WIDTH ( AxiUserWidth )
  ) master_dv (clk), slave_dv (clk);

  `AXI_ASSIGN (master,   master_dv)
  `AXI_ASSIGN (slave_dv, slave)

  axi_req_t  master_req, slave_req;
  axi_resp_t master_rsp, slave_rsp;

  `AXI_ASSIGN_TO_REQ(master_req, master)
  `AXI_ASSIGN_FROM_RESP(master, master_rsp)
  `AXI_ASSIGN_FROM_REQ(slave, slave_req)
  `AXI_ASSIGN_TO_RESP(slave_rsp, slave)




  //-----------------------------------
  // Clock generator
  //-----------------------------------
  clk_rst_gen #(
      .ClkPeriod    ( CyclTime ),
      .RstClkCycles ( 32'd5    )
  ) i_clk_gen (
      .clk_o        ( clk      ),
      .rst_no       ( rst_n    )
  );


  stream_watchdog #(
    .NumCycles ( 1000 )
  ) i_stream_watchdog_aw (
    .clk_i   ( clk                 ),
    .rst_ni  ( rst_n               ),
    .valid_i ( master_req.aw_valid ),
    .ready_i ( master_rsp.aw_ready )
  );


  stream_watchdog #(
    .NumCycles ( 1000 )
  ) i_stream_watchdog_ar (
    .clk_i   ( clk                 ),
    .rst_ni  ( rst_n               ),
    .valid_i ( master_req.ar_valid ),
    .ready_i ( master_rsp.ar_ready )
  );

  // add highlighters
  `AXI_HIGHLIGHT(master, axi_aw_chan_t, axi_w_chan_t, axi_b_chan_t, axi_ar_chan_t, axi_r_chan_t, master_req, master_rsp)
  `AXI_HIGHLIGHT(slave,  axi_aw_chan_t, axi_w_chan_t, axi_b_chan_t, axi_ar_chan_t, axi_r_chan_t, slave_req,  slave_rsp)



  //-----------------------------------
  // DUT
  //-----------------------------------
  axi_rt_unit #(
    .AddrWidth      ( AxiAddrWidth   ),
    .DataWidth      ( AxiDataWidth   ),
    .IdWidth        ( AxiIdWidth     ),
    .UserWidth      ( AxiUserWidth   ),
    .NumPending     ( 32'd16         ),
    .WBufferDepth   ( 32'd512        ),
    .NumAddrRegions ( NumAddrRegions ),
    .NumRules       ( NumRules       ),
    .BudgetWidth    ( 32'd32         ),
    .PeriodWidth    ( 32'd32         ),
    .rt_rule_t      ( rt_rule_t      ),
    .addr_t         ( addr_t         ),
    .aw_chan_t      ( axi_aw_chan_t  ),
    .w_chan_t       ( axi_w_chan_t   ),
    .axi_req_t      ( axi_req_t      ),
    .axi_resp_t     ( axi_resp_t     )
  ) i_axi_rt_unit (
    .clk_i            ( clk            ),
    .rst_ni           ( rst_n          ),
    .slv_req_i        ( master_req     ),
    .slv_resp_o       ( master_rsp     ),
    .mst_req_o        ( slave_req      ),
    .mst_resp_i       ( slave_rsp      ),
    .rt_enable_i      ( 1'b1           ),
    .rt_bypassed_o    ( ),
    .len_limit_i      ( 'd0            ),
    .num_w_pending_o  ( ),
    .num_aw_pending_o ( ),
    .rt_rule_i        ( RtAddrmap      ),
    .w_decode_error_o ( ),
    .r_decode_error_o ( ),
    .imtu_enable_i    ( 1'b1           ),
    .imtu_abort_i     ( 1'b0           ),
    .r_budget_i       ( {32'd1, 32'd1, 32'd1} ),
    .r_budget_left_o  ( ),
    .r_period_i       ( {32'd100, 32'd100, 32'd100} ),
    .r_period_left_o  ( ),
    .w_budget_i       ( {32'd1, 32'd1, 32'd1} ),
    .w_budget_left_o  ( ),
    .w_period_i       ( {32'd100, 32'd100, 32'd100} ),
    .w_period_left_o  ( ),
    .isolate_o        ( ),
    .isolated_o       ( )
  );



  //-----------------------------------
  // TB
  //-----------------------------------

  initial begin : proc_axi_master
    automatic axi_file_master_t axi_file_master = new(master_dv);
    axi_file_master.reset();
    axi_file_master.load_files("../test/stimuli/axi_rt_unit.reads.txt", "../test/stimuli/axi_rt_unit.writes.txt");
    total_num_reads  = axi_file_master.num_reads;
    total_num_writes = axi_file_master.num_writes;
    end_of_sim = 1'b0;
    @(posedge rst_n);
    axi_file_master.run();
    end_of_sim = 1'b1;
    repeat (100) @(posedge clk);
    $stop();
  end

  initial begin : proc_axi_slave
    automatic axi_rand_slave_t axi_rand_slave = new(slave_dv);
    axi_rand_slave.reset();
    @(posedge rst_n);
    axi_rand_slave.run();
  end

  initial begin : proc_sim_progress
    automatic int unsigned aw = 0;
    automatic int unsigned ar = 0;
    automatic bit          aw_printed = 1'b0;
    automatic bit          ar_printed = 1'b0;

    @(posedge rst_n);

    forever begin
      @(posedge clk);
      #TestTime;
      if (master.aw_valid && master.aw_ready) begin
        aw++;
      end
      if (master.ar_valid && master.ar_ready) begin
        ar++;
      end

      if ((aw % PrintTnx == 0) && !aw_printed) begin
        $display("%t> Transmit AW %d of %d.", $time(), aw, total_num_writes);
        aw_printed = 1'b1;
      end
      if ((ar % PrintTnx == 0) && !ar_printed) begin
        $display("%t> Transmit AR %d of %d.", $time(), ar, total_num_reads);
        ar_printed = 1'b1;
      end

      if (aw % PrintTnx == 1) begin
        aw_printed = 1'b0;
      end
      if (ar % PrintTnx == 1) begin
        ar_printed = 1'b0;
      end

      if (end_of_sim) begin
        $info("All transactions completed.");
        break;
      end
    end
  end


  default disable iff (!rst_n); aw_unstable :
  assert property (@(posedge clk) (slave.aw_valid && !slave.aw_ready) |=> $stable(slave.aw_addr))
  else $fatal(1, "AW is unstable.");
  w_unstable :
  assert property (@(posedge clk) (slave.w_valid && !slave.w_ready) |=> $stable(slave.w_data))
  else $fatal(1, "W is unstable.");
  b_unstable :
  assert property (@(posedge clk) (master.b_valid && !master.b_ready) |=> $stable(master.b_resp))
  else $fatal(1, "B is unstable.");
  ar_unstable :
  assert property (@(posedge clk) (slave.ar_valid && !slave.ar_ready) |=> $stable(slave.ar_addr))
  else $fatal(1, "AR is unstable.");
  r_unstable :
  assert property (@(posedge clk) (master.r_valid && !master.r_ready) |=> $stable(master.r_data))
  else $fatal(1, "R is unstable.");

endmodule
