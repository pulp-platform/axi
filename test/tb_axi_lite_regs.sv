// Copyright (c) 2020 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Author: Wolfgang Roenninger <wroennin@ethz.ch>

// Directed Random Verification Testbench for `axi_lite_regs`.

`include "axi/assign.svh"

module tb_axi_lite_regs #(
  // register configuration
  parameter int unsigned            RegNumBytes  = 32'd200,
  parameter logic [RegNumBytes-1:0] AxiReadOnly  = {RegNumBytes{1'b0}},
  parameter bit                     PrivProtOnly = 1'b0,
  parameter bit                     SecuProtOnly = 1'b0,
  // AXI configuration
  parameter int unsigned            AxiAddrWidth = 32'd32,    // Axi Address Width
  parameter int unsigned            AxiDataWidth = 32'd32,    // Axi Data Width
  // Random master no Transactions
  parameter int unsigned            NoWrites     = 32'd1000,  // How many writes of master
  parameter int unsigned            NoReads      = 32'd1500   // How many reads of master
);
  localparam int unsigned AxiStrbWidth = AxiDataWidth / 32'd8;
  // timing parameters
  localparam time CyclTime = 10ns;
  localparam time ApplTime =  2ns;
  localparam time TestTime =  8ns;

  typedef logic [7:0]              byte_t;
  typedef logic [AxiAddrWidth-1:0] axi_addr_t;
  typedef logic [AxiDataWidth-1:0] axi_data_t;
  typedef logic [AxiStrbWidth-1:0] axi_strb_t;

  localparam axi_addr_t StartAddr = axi_addr_t'(0);
  localparam axi_addr_t EndAddr   =
      axi_addr_t'(StartAddr + RegNumBytes + RegNumBytes/5);

  typedef axi_test::rand_axi_lite_master #(
    // AXI interface parameters
    .AW ( AxiAddrWidth ),
    .DW ( AxiDataWidth ),
    // Stimuli application and test time
    .TA ( ApplTime  ),
    .TT ( TestTime  ),
    .MIN_ADDR ( StartAddr ),
    .MAX_ADDR ( EndAddr   ),
    .MAX_READ_TXNS  ( 10 ),
    .MAX_WRITE_TXNS ( 10 )
  ) rand_lite_master_t;

  // -------------
  // DUT signals
  // -------------
  logic clk;
  // DUT signals
  logic rst_n;
  logic end_of_sim;
  // Register signals
  byte_t [RegNumBytes-1:0] reg_d,     reg_q;
  logic  [RegNumBytes-1:0] wr_active, rd_active;

  // -------------------------------
  // AXI Interfaces
  // -------------------------------
  AXI_LITE #(
    .AXI_ADDR_WIDTH ( AxiAddrWidth      ),
    .AXI_DATA_WIDTH ( AxiDataWidth      )
  ) master ();
  AXI_LITE_DV #(
    .AXI_ADDR_WIDTH ( AxiAddrWidth      ),
    .AXI_DATA_WIDTH ( AxiDataWidth      )
  ) master_dv (clk);
  `AXI_LITE_ASSIGN(master, master_dv)

  // -------------------------------
  // AXI Rand Masters and Slaves
  // -------------------------------
  // Masters control simulation run time
  initial begin : proc_generate_traffic
    automatic rand_lite_master_t lite_axi_master = new ( master_dv, "Lite Master");
    automatic axi_data_t      data = '0;
    automatic axi_pkg::resp_t resp = '0;
    end_of_sim <= 1'b0;
    lite_axi_master.reset();
    @(posedge rst_n);
    repeat (5) @(posedge clk);
    lite_axi_master.write(axi_addr_t'(32'h0000_0000), axi_data_t'(64'hDEADBEEFDEADBEEF),
        axi_strb_t'(8'hFF), resp);
    lite_axi_master.read(axi_addr_t'(32'h0000_0000), data, resp);
    lite_axi_master.run(NoReads, NoWrites);
    end_of_sim <= 1'b1;
  end

  initial begin : proc_check
    automatic bit init;
    automatic axi_data_t exp_rdata[$];

    for (int unsigned i = 0; i < RegNumBytes; i++) begin
      for (int unsigned j = 0; j < 8; j++) begin
        init = $urandom();
        reg_d [i][j] = init;
      end
    end
    @(posedge rst_n);
//    forever begin
//      @(posedge clk);
//      #(TestTime);
//
//      if (master.ar_valid && master.ar_ready) begin
//        automatic int unsigned ar_idx = (master.ar_addr - StartAddr) >> $clog2(AxiStrbWidth);
//        automatic axi_data_t   r_data = axi_data_t'(0);
//        if (ar_idx < NumAxiRegs) begin
//          r_data = reg_q[ar_idx];
//        end
//        exp_rdata.push_back(r_data);
//      end
//      if (master.r_valid && master.r_ready) begin
//        automatic axi_data_t r_data = exp_rdata.pop_front();
//        if (master.r_resp == axi_pkg::RESP_OKAY) begin
//          assert (master.r_data == r_data) else
//              $error("Unexpected read data: exp: %0h observes %0h", r_data, master.r_data);
//        end
//      end
//    end
  end

  initial begin : proc_stop_sim
    wait (end_of_sim);
    repeat (1000) @(posedge clk);
    $display("Simulation stopped as Master transferred its data.");
    $stop();
  end

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
  axi_lite_regs_intf #(
    .REG_NUM_BYTES  ( RegNumBytes  ),
    .AXI_ADDR_WIDTH ( AxiAddrWidth ),
    .AXI_DATA_WIDTH ( AxiDataWidth ),
    .PRIV_PROT_ONLY ( PrivProtOnly ),
    .SECU_PROT_ONLY ( SecuProtOnly ),
    .AXI_READ_ONLY  ( AxiReadOnly  ),
    .REG_RST_VAL    ( {RegNumBytes{8'h00}})
  ) i_axi_lite_regs (
    .clk_i       ( clk       ),
    .rst_ni      ( rst_n     ),
    .slv         ( master    ),
    .wr_active_o ( wr_active ),
    .rd_active_o ( rd_active ),
    .reg_d_i     ( reg_d     ),
    .reg_load_i  ( '0        ),
    .reg_q_o     ( reg_q     )
  );
endmodule
