// Copyright (c) 2019 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Author: Wolfgang Roenninger <wroennin@ethz.ch>

`include "axi/typedef.svh"
`include "axi/assign.svh"

module tb_axi_serializer #(
    parameter int unsigned NoWrites = 5000,  // How many writes per master
    parameter int unsigned NoReads  = 3000   // How many reads per master
  );
  // Random master no Transactions
  localparam int unsigned NoPendingDut = 4;
  // Random Master Atomics
  localparam int unsigned MaxAW      = 32'd30;
  localparam int unsigned MaxAR      = 32'd30;
  localparam bit          EnAtop     = 1'b1;
  // timing parameters
  localparam time CyclTime = 10ns;
  localparam time ApplTime =  2ns;
  localparam time TestTime =  8ns;
  // AXI configuration
  localparam int unsigned AxiIdWidth   =  4;
  localparam int unsigned AxiAddrWidth =  32;    // Axi Address Width
  localparam int unsigned AxiDataWidth =  64;    // Axi Data Width
  localparam int unsigned AxiUserWidth =  5;
  // Sim print config, how many transactions
  localparam int unsigned PrintTxn = 500;

  typedef axi_test::rand_axi_master #(
    // AXI interface parameters
    .AW ( AxiAddrWidth ),
    .DW ( AxiDataWidth ),
    .IW ( AxiIdWidth   ),
    .UW ( AxiUserWidth ),
    // Stimuli application and test time
    .TA ( ApplTime ),
    .TT ( TestTime ),
    // Maximum number of read and write transactions in flight
    .MAX_READ_TXNS  ( MaxAR  ),
    .MAX_WRITE_TXNS ( MaxAW  ),
    .AXI_ATOPS      ( EnAtop )
  ) rand_axi_master_t;
  typedef axi_test::rand_axi_slave #(
    // AXI interface parameters
    .AW ( AxiAddrWidth ),
    .DW ( AxiDataWidth ),
    .IW ( AxiIdWidth   ),
    .UW ( AxiUserWidth ),
    // Stimuli application and test time
    .TA ( ApplTime ),
    .TT ( TestTime )
  ) rand_axi_slave_t;

  // -------------
  // DUT signals
  // -------------
  logic clk;
  logic rst_n;
  logic end_of_sim;

  // interfaces
  AXI_BUS #(
    .AXI_ADDR_WIDTH ( AxiAddrWidth ),
    .AXI_DATA_WIDTH ( AxiDataWidth ),
    .AXI_ID_WIDTH   ( AxiIdWidth   ),
    .AXI_USER_WIDTH ( AxiUserWidth )
  ) master ();
  AXI_BUS_DV #(
    .AXI_ADDR_WIDTH ( AxiAddrWidth ),
    .AXI_DATA_WIDTH ( AxiDataWidth ),
    .AXI_ID_WIDTH   ( AxiIdWidth   ),
    .AXI_USER_WIDTH ( AxiUserWidth )
  ) master_dv (clk);
  AXI_BUS #(
    .AXI_ADDR_WIDTH ( AxiAddrWidth ),
    .AXI_DATA_WIDTH ( AxiDataWidth ),
    .AXI_ID_WIDTH   ( AxiIdWidth   ),
    .AXI_USER_WIDTH ( AxiUserWidth )
  ) slave ();
  AXI_BUS_DV #(
    .AXI_ADDR_WIDTH ( AxiAddrWidth ),
    .AXI_DATA_WIDTH ( AxiDataWidth ),
    .AXI_ID_WIDTH   ( AxiIdWidth   ),
    .AXI_USER_WIDTH ( AxiUserWidth )
  ) slave_dv (clk);

  `AXI_ASSIGN(master, master_dv)
  `AXI_ASSIGN(slave_dv, slave)

  //-----------------------------------
  // Clock generator
  //-----------------------------------
  clk_rst_gen #(
    .CLK_PERIOD    ( CyclTime ),
    .RST_CLK_CYCLES( 5        )
  ) i_clk_gen (
    .clk_o (clk),
    .rst_no(rst_n)
  );

  //-----------------------------------
  // DUT
  //-----------------------------------
  axi_serializer_intf #(
    .MAX_READ_TXNS  ( NoPendingDut ),
    .MAX_WRITE_TXNS ( NoPendingDut ),
    .AXI_ID_WIDTH   ( AxiIdWidth   ), // AXI ID width
    .AXI_ADDR_WIDTH ( AxiAddrWidth ), // AXI address width
    .AXI_DATA_WIDTH ( AxiDataWidth ), // AXI data width
    .AXI_USER_WIDTH ( AxiUserWidth )  // AXI user width
  ) i_dut (
    .clk_i      ( clk      ), // clock
    .rst_ni     ( rst_n    ), // asynchronous reset active low
    .slv        ( master   ), // slave port
    .mst        ( slave    )  // master port
  );

  initial begin : proc_axi_master
    automatic rand_axi_master_t rand_axi_master = new(master_dv);
    end_of_sim <= 1'b0;
    rand_axi_master.add_memory_region(32'h0000_0000, 32'h1000_0000, axi_pkg::DEVICE_NONBUFFERABLE);
    rand_axi_master.add_memory_region(32'h2000_0000, 32'h3000_0000, axi_pkg::WTHRU_NOALLOCATE);
    rand_axi_master.add_memory_region(32'h4000_0000, 32'h5000_0000, axi_pkg::WBACK_RWALLOCATE);
    rand_axi_master.reset();
    @(posedge rst_n);
    rand_axi_master.run(NoReads, NoWrites);
    end_of_sim <= 1'b1;
    repeat (100) @(posedge clk);
    $stop();
  end

  initial begin : proc_axi_slave
    automatic rand_axi_slave_t  rand_axi_slave  = new(slave_dv);
    rand_axi_slave.reset();
    @(posedge rst_n);
    rand_axi_slave.run();
  end

  // Checker
  typedef logic [AxiIdWidth-1:0] axi_id_t;
  typedef logic [AxiIdWidth-1:0] axi_addr_t;
  typedef logic [AxiIdWidth-1:0] axi_data_t;
  typedef logic [AxiIdWidth-1:0] axi_strb_t;
  typedef logic [AxiIdWidth-1:0] axi_user_t;
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
      if (master.aw_valid && master.aw_ready) begin
        `AXI_SET_TO_AW(aw_exp, master)
        aw_exp.id = '0;
        id_exp    = master.aw_id;
        aw_chan.push_back(aw_exp);
        aw_queue.push_back(id_exp);
        if (master.aw_atop[axi_pkg::ATOP_R_RESP]) begin
          ar_queue.push_back(id_exp);
        end
      end
      if (master.w_valid && master.w_ready) begin
        `AXI_SET_TO_W(w_exp, master)
        w_chan.push_back(w_exp);
      end
      if (slave.b_valid && slave.b_ready) begin
        id_exp = aw_queue.pop_front();
        `AXI_SET_TO_B(b_exp, slave)
        b_exp.id = id_exp;
        b_chan.push_back(b_exp);
      end
      if (master.ar_valid && master.ar_ready) begin
        `AXI_SET_TO_AR(ar_exp, master)
        ar_exp.id = '0;
        id_exp    = master.ar_id;
        ar_chan.push_back(ar_exp);
        ar_queue.push_back(id_exp);
      end
      if (slave.r_valid && slave.r_ready) begin
        `AXI_SET_TO_R(r_exp, slave)
        if (slave.r_last) begin
          id_exp = ar_queue.pop_front();
        end else begin
          id_exp = ar_queue[0];
        end
        r_exp.id = id_exp;
        r_chan.push_back(r_exp);
      end
      // Check that all channels match the expected response
      if (slave.aw_valid && slave.aw_ready) begin
        aw_exp = aw_chan.pop_front();
        `AXI_SET_TO_AW(aw_act, slave)
        assert(aw_act == aw_exp) else $error("AW Measured: %h Expected: %h", aw_act, aw_exp);
      end
      if (slave.w_valid && slave.w_ready) begin
        w_exp = w_chan.pop_front();
        `AXI_SET_TO_W(w_act, slave)
        assert(w_act == w_exp) else $error("W Measured: %h Expected: %h", w_act, w_exp);
      end
      if (master.b_valid && master.b_ready) begin
        b_exp = b_chan.pop_front();
        `AXI_SET_TO_B(b_act, master)
        assert(b_act == b_exp) else $error("B Measured: %h Expected: %h", b_act, b_exp);
      end
      if (slave.ar_valid && slave.ar_ready) begin
        ar_exp = ar_chan.pop_front();
        `AXI_SET_TO_AR(ar_act, slave)
        assert(ar_act == ar_exp) else $error("AR Measured: %h Expected: %h", ar_act, ar_exp);
      end
      if (master.r_valid && master.r_ready) begin
        r_exp = r_chan.pop_front();
        `AXI_SET_TO_R(r_act, master)
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
      if (master.aw_valid && master.aw_ready) begin
        aw++;
      end
      if (master.ar_valid && master.ar_ready) begin
        ar++;
      end

      if ((aw % PrintTxn == 0) && ! aw_printed) begin
        $display("%t> Transmit AW %d of %d.", $time(), aw, NoWrites);
        aw_printed = 1'b1;
      end
      if ((ar % PrintTxn == 0) && !ar_printed) begin
        $display("%t> Transmit AR %d of %d.", $time(), ar, NoReads);
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
