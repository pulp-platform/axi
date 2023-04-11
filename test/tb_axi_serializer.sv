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
// - Wolfgang Roenninger <wroennin@iis.ee.ethz.ch>
// - Andreas Kurth <akurth@iis.ee.ethz.ch>

`include "axi/typedef.svh"
`include "axi/assign.svh"

module tb_axi_serializer #(
    parameter int unsigned NumWrites = 5000,  // How many writes per manager
    parameter int unsigned NumReads  = 3000   // How many reads per manager
  );
  // Random manager no Transactions
  localparam int unsigned NumPendingDut = 4;
  // Random Manager Atomics
  localparam int unsigned MaxAW      = 32'd30;
  localparam int unsigned MaxAR      = 32'd30;
  localparam bit          EnAtop     = 1'b1;
  // timing parameters
  localparam time CyclTime = 10ns;
  localparam time ApplTime =  2ns;
  localparam time TestTime =  8ns;
  // AXI configuration
  localparam int unsigned IdWidth   =  4;
  localparam int unsigned AddrWidth =  32;    // Address Width
  localparam int unsigned DataWidth =  64;    // Data Width
  localparam int unsigned UserWidth =  5;
  // Sim print config, how many transactions
  localparam int unsigned PrintTxn = 500;

  typedef axi_test::axi_rand_manager #(
    // AXI interface parameters
    .AW ( AddrWidth ),
    .DW ( DataWidth ),
    .IW ( IdWidth   ),
    .UW ( UserWidth ),
    // Stimuli application and test time
    .TA ( ApplTime ),
    .TT ( TestTime ),
    // Maximum number of read and write transactions in flight
    .MAX_READ_TXNS  ( MaxAR  ),
    .MAX_WRITE_TXNS ( MaxAW  ),
    .AXI_ATOPS      ( EnAtop )
  ) axi_rand_manager_t;
  typedef axi_test::axi_rand_subordinate #(
    // AXI interface parameters
    .AW ( AddrWidth ),
    .DW ( DataWidth ),
    .IW ( IdWidth   ),
    .UW ( UserWidth ),
    // Stimuli application and test time
    .TA ( ApplTime ),
    .TT ( TestTime )
  ) axi_rand_subordinate_t;

  // -------------
  // DUT signals
  // -------------
  logic clk;
  logic rst_n;
  logic end_of_sim;

  // interfaces
  AXI_BUS #(
    .AXI_ADDR_WIDTH ( AddrWidth ),
    .AXI_DATA_WIDTH ( DataWidth ),
    .AXI_ID_WIDTH   ( IdWidth   ),
    .AXI_USER_WIDTH ( UserWidth )
  ) manager ();
  AXI_BUS_DV #(
    .AXI_ADDR_WIDTH ( AddrWidth ),
    .AXI_DATA_WIDTH ( DataWidth ),
    .AXI_ID_WIDTH   ( IdWidth   ),
    .AXI_USER_WIDTH ( UserWidth )
  ) manager_dv (clk);
  AXI_BUS #(
    .AXI_ADDR_WIDTH ( AddrWidth ),
    .AXI_DATA_WIDTH ( DataWidth ),
    .AXI_ID_WIDTH   ( IdWidth   ),
    .AXI_USER_WIDTH ( UserWidth )
  ) subordinate ();
  AXI_BUS_DV #(
    .AXI_ADDR_WIDTH ( AddrWidth ),
    .AXI_DATA_WIDTH ( DataWidth ),
    .AXI_ID_WIDTH   ( IdWidth   ),
    .AXI_USER_WIDTH ( UserWidth )
  ) subordinate_dv (clk);

  `AXI_ASSIGN(manager, manager_dv)
  `AXI_ASSIGN(subordinate_dv, subordinate)

  //-----------------------------------
  // Clock generator
  //-----------------------------------
  clk_rst_gen #(
    .ClkPeriod    ( CyclTime ),
    .RstClkCycles ( 5        )
  ) i_clk_gen (
    .clk_o (clk),
    .rst_no(rst_n)
  );

  //-----------------------------------
  // DUT
  //-----------------------------------
  axi_serializer_intf #(
    .MAX_READ_TXNS  ( NumPendingDut ),
    .MAX_WRITE_TXNS ( NumPendingDut ),
    .AXI_ID_WIDTH   ( IdWidth      ), // AXI ID width
    .AXI_ADDR_WIDTH ( AddrWidth    ), // AXI address width
    .AXI_DATA_WIDTH ( DataWidth    ), // AXI data width
    .AXI_USER_WIDTH ( UserWidth    )  // AXI user width
  ) i_dut (
    .clk_i      ( clk      ), // clock
    .rst_ni     ( rst_n    ), // asynchronous reset active low
    .sbr        ( manager   ), // subordinate port
    .mgr        ( subordinate    )  // manager port
  );

  initial begin : proc_axi_manager
    automatic axi_rand_manager_t axi_rand_manager = new(manager_dv);
    end_of_sim <= 1'b0;
    axi_rand_manager.add_memory_region(32'h0000_0000, 32'h1000_0000, axi_pkg::DEVICE_NONBUFFERABLE);
    axi_rand_manager.add_memory_region(32'h2000_0000, 32'h3000_0000, axi_pkg::WTHRU_NOALLOCATE);
    axi_rand_manager.add_memory_region(32'h4000_0000, 32'h5000_0000, axi_pkg::WBACK_RWALLOCATE);
    axi_rand_manager.reset();
    @(posedge rst_n);
    axi_rand_manager.run(NumReads, NumWrites);
    end_of_sim <= 1'b1;
    repeat (100) @(posedge clk);
    $stop();
  end

  initial begin : proc_axi_subordinate
    automatic axi_rand_subordinate_t  axi_rand_subordinate  = new(subordinate_dv);
    axi_rand_subordinate.reset();
    @(posedge rst_n);
    axi_rand_subordinate.run();
  end

  // Checker
  typedef logic [IdWidth-1:0]     axi_id_t;
  typedef logic [AddrWidth-1:0]   axi_addr_t;
  typedef logic [DataWidth-1:0]   axi_data_t;
  typedef logic [DataWidth/8-1:0] axi_strb_t;
  typedef logic [UserWidth-1:0]   axi_user_t;
  `AXI_TYPEDEF_AW_CHAN_T(aw_chan_t, axi_addr_t,  axi_id_t,  axi_user_t)
  `AXI_TYPEDEF_W_CHAN_T(w_chan_t,  axi_data_t,  axi_strb_t,  axi_user_t)
  `AXI_TYPEDEF_B_CHAN_T(b_chan_t,  axi_id_t,  axi_user_t)
  `AXI_TYPEDEF_AR_CHAN_T(ar_chan_t,  axi_addr_t,  axi_id_t,  axi_user_t)
  `AXI_TYPEDEF_R_CHAN_T(r_chan_t,  axi_data_t,  axi_id_t,  axi_user_t)
  axi_id_t  aw_queue[$];
  axi_id_t  ar_queue[$];
  aw_chan_t aw_chan[$];
  w_chan_t   w_chan[$];
  b_chan_t   b_chan[$];
  ar_chan_t ar_chan[$];
  r_chan_t   r_chan[$];

  initial begin : proc_checker
    automatic axi_id_t  id_exp; // expected ID
    automatic aw_chan_t aw_exp; // expected AW
    automatic aw_chan_t aw_act; // actual AW
    automatic w_chan_t   w_exp; // expected W
    automatic w_chan_t   w_act; // actual W
    automatic b_chan_t   b_exp; // expected B
    automatic b_chan_t   b_act; // actual B
    automatic ar_chan_t ar_exp; // expected AR
    automatic ar_chan_t ar_act; // actual AR
    automatic r_chan_t   r_exp; // expected R
    automatic r_chan_t   r_act; // actual R
    forever begin
      @(posedge clk);
      #TestTime;
      // All FIFOs get populated if there is something to put in
      if (manager.aw_valid && manager.aw_ready) begin
        `AXI_SET_TO_AW(aw_exp, manager)
        aw_exp.id = '0;
        id_exp    = manager.aw_id;
        aw_chan.push_back(aw_exp);
        aw_queue.push_back(id_exp);
        if (manager.aw_atop[axi_pkg::ATOP_R_RESP]) begin
          ar_queue.push_back(id_exp);
        end
      end
      if (manager.w_valid && manager.w_ready) begin
        `AXI_SET_TO_W(w_exp, manager)
        w_chan.push_back(w_exp);
      end
      if (subordinate.b_valid && subordinate.b_ready) begin
        id_exp = aw_queue.pop_front();
        `AXI_SET_TO_B(b_exp, subordinate)
        b_exp.id = id_exp;
        b_chan.push_back(b_exp);
      end
      if (manager.ar_valid && manager.ar_ready) begin
        `AXI_SET_TO_AR(ar_exp, manager)
        ar_exp.id = '0;
        id_exp    = manager.ar_id;
        ar_chan.push_back(ar_exp);
        ar_queue.push_back(id_exp);
      end
      if (subordinate.r_valid && subordinate.r_ready) begin
        `AXI_SET_TO_R(r_exp, subordinate)
        if (subordinate.r_last) begin
          id_exp = ar_queue.pop_front();
        end else begin
          id_exp = ar_queue[0];
        end
        r_exp.id = id_exp;
        r_chan.push_back(r_exp);
      end
      // Check that all channels match the expected response
      if (subordinate.aw_valid && subordinate.aw_ready) begin
        aw_exp = aw_chan.pop_front();
        `AXI_SET_TO_AW(aw_act, subordinate)
        assert(aw_act == aw_exp) else $error("AW Measured: %h Expected: %h", aw_act, aw_exp);
      end
      if (subordinate.w_valid && subordinate.w_ready) begin
        w_exp = w_chan.pop_front();
        `AXI_SET_TO_W(w_act, subordinate)
        assert(w_act == w_exp) else $error("W Measured: %h Expected: %h", w_act, w_exp);
      end
      if (manager.b_valid && manager.b_ready) begin
        b_exp = b_chan.pop_front();
        `AXI_SET_TO_B(b_act, manager)
        assert(b_act == b_exp) else $error("B Measured: %h Expected: %h", b_act, b_exp);
      end
      if (subordinate.ar_valid && subordinate.ar_ready) begin
        ar_exp = ar_chan.pop_front();
        `AXI_SET_TO_AR(ar_act, subordinate)
        assert(ar_act == ar_exp) else $error("AR Measured: %h Expected: %h", ar_act, ar_exp);
      end
      if (manager.r_valid && manager.r_ready) begin
        r_exp = r_chan.pop_front();
        `AXI_SET_TO_R(r_act, manager)
        assert(r_act == r_exp) else $error("R Measured: %h Expected: %h", r_act, r_exp);
      end
    end
  end

  initial begin : proc_sim_progress
    automatic int unsigned aw         = 0;
    automatic int unsigned ar         = 0;
    automatic bit          aw_printed = 1'b0;
    automatic bit          ar_printed = 1'b0;

    @(posedge rst_n);

    forever begin
      @(posedge clk);
      #TestTime;
      if (manager.aw_valid && manager.aw_ready) begin
        aw++;
      end
      if (manager.ar_valid && manager.ar_ready) begin
        ar++;
      end

      if ((aw % PrintTxn == 0) && ! aw_printed) begin
        $display("%t> Transmit AW %d of %d.", $time(), aw, NumWrites);
        aw_printed = 1'b1;
      end
      if ((ar % PrintTxn == 0) && !ar_printed) begin
        $display("%t> Transmit AR %d of %d.", $time(), ar, NumReads);
        ar_printed = 1'b1;
      end

      if (aw % PrintTxn == 1) begin
        aw_printed = 1'b0;
      end
      if (ar % PrintTxn == 1) begin
        ar_printed = 1'b0;
      end

      if (end_of_sim) begin
        $info("All transactions completed.");
        break;
      end
    end
  end
endmodule
