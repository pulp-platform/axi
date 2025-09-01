// Copyright 2020 ETH Zurich and University of Bologna.
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
// - Matheus Cavalcante <matheusd@iis.ee.ethz.ch>
// - Andreas Kurth <akurth@iis.ee.ethz.ch>

`include "axi/assign.svh"
`include "axi/typedef.svh"

module tb_axi_burst_unwrap #(
    // AXI Parameters
    parameter int unsigned TbAxiAddrWidth        = 64,
    parameter int unsigned TbAxiIdWidth          = 4,
    parameter int unsigned TbAxiDataWidth        = 64,
    parameter int unsigned TbAxiUserWidth        = 8,
    parameter int unsigned TbInitialBStallCycles = 0,
    parameter int unsigned TbInitialRStallCycles = 0,
    // TB Parameters
    parameter time TbCyclTime                    = 10ns,
    parameter time TbApplTime                    = 2ns,
    parameter time TbTestTime                    = 8ns
  );

  /*********************
   *  CLOCK GENERATOR  *
   *********************/

  logic clk;
  logic rst_n;
  logic eos;

  int unsigned b_stall;
  int unsigned r_stall;

  clk_rst_gen #(
    .ClkPeriod    (TbCyclTime),
    .RstClkCycles (5         )
  ) i_clk_rst_gen (
    .clk_o (clk  ),
    .rst_no(rst_n)
  );

  /*********
   *  AXI  *
   *********/

  typedef logic [TbAxiAddrWidth-1:0]   addr_t;
  typedef logic [TbAxiDataWidth-1:0]   data_t;
  typedef logic [TbAxiIdWidth-1:0]     id_t;
  typedef logic [TbAxiDataWidth/8-1:0] strb_t;
  typedef logic [TbAxiUserWidth-1:0]   user_t;
  `AXI_TYPEDEF_ALL(axi, addr_t, id_t, data_t, strb_t, user_t)

  // Master port

  axi_req_t master_req;
  axi_resp_t master_resp;

  AXI_BUS_DV #(
    .AXI_ADDR_WIDTH(TbAxiAddrWidth),
    .AXI_DATA_WIDTH(TbAxiDataWidth),
    .AXI_ID_WIDTH  (TbAxiIdWidth  ),
    .AXI_USER_WIDTH(TbAxiUserWidth)
  ) master_dv (
    .clk_i(clk)
  );

  AXI_BUS #(
    .AXI_ADDR_WIDTH(TbAxiAddrWidth),
    .AXI_DATA_WIDTH(TbAxiDataWidth),
    .AXI_ID_WIDTH  (TbAxiIdWidth  ),
    .AXI_USER_WIDTH(TbAxiUserWidth)
  ) master ();

  `AXI_ASSIGN_AW(master, master_dv)
  `AXI_ASSIGN_W(master, master_dv)
  `AXI_ASSIGN_AR(master, master_dv)
  assign master_dv.b_id    =                       master.b_id;
  assign master_dv.b_resp  =                       master.b_resp;
  assign master_dv.b_user  =                       master.b_user;
  assign master_dv.b_valid = b_stall != 0 ? 1'b0 : master.b_valid;
  assign master.b_ready    = b_stall != 0 ? 1'b0 : master_dv.b_ready;
  assign master_dv.r_id    =                       master.r_id;
  assign master_dv.r_data  =                       master.r_data;
  assign master_dv.r_resp  =                       master.r_resp;
  assign master_dv.r_last  =                       master.r_last;
  assign master_dv.r_user  =                       master.r_user;
  assign master_dv.r_valid = r_stall != 0 ? 1'b0 : master.r_valid;
  assign master.r_ready    = r_stall != 0 ? 1'b0 : master_dv.r_ready;

  always_ff @(posedge clk or negedge rst_n) begin : proc_
    if(~rst_n) begin
      b_stall <= TbInitialBStallCycles;
      r_stall <= TbInitialRStallCycles;
    end else begin
      b_stall <= b_stall == 0 ? 0 : b_stall-1;
      r_stall <= r_stall == 0 ? 0 : r_stall-1;
    end
  end

  axi_test::axi_rand_master #(
    .AW             (TbAxiAddrWidth),
    .DW             (TbAxiDataWidth),
    .IW             (TbAxiIdWidth  ),
    .UW             (TbAxiUserWidth),
    .TA             (TbApplTime    ),
    .TT             (TbTestTime    ),
    .MAX_READ_TXNS  (8             ),
    .MAX_WRITE_TXNS (8             ),
    .AXI_BURST_FIXED(1'b0          ),
    .AXI_BURST_WRAP (1'b1          ),
    .AXI_ATOPS      (1'b0          )
  ) master_drv = new (master_dv);

  // Slave port

  axi_req_t slave_req;
  axi_resp_t slave_resp;

  AXI_BUS_DV #(
    .AXI_ADDR_WIDTH(TbAxiAddrWidth),
    .AXI_DATA_WIDTH(TbAxiDataWidth),
    .AXI_ID_WIDTH  (TbAxiIdWidth  ),
    .AXI_USER_WIDTH(TbAxiUserWidth)
  ) slave_dv (
    .clk_i(clk)
  );

  AXI_BUS #(
    .AXI_ADDR_WIDTH(TbAxiAddrWidth),
    .AXI_DATA_WIDTH(TbAxiDataWidth),
    .AXI_ID_WIDTH  (TbAxiIdWidth  ),
    .AXI_USER_WIDTH(TbAxiUserWidth)
  ) slave ();

  axi_test::axi_rand_slave #(
    .AW(TbAxiAddrWidth),
    .DW(TbAxiDataWidth),
    .IW(TbAxiIdWidth  ),
    .UW(TbAxiUserWidth),
    .TA(TbApplTime    ),
    .TT(TbTestTime    ),
    .MAPPED( 1'b1     )
  ) slave_drv = new (slave_dv);

  `AXI_ASSIGN(slave_dv, slave)

  `AXI_ASSIGN_TO_REQ(master_req, master)
  `AXI_ASSIGN_FROM_RESP(master, master_resp)
  `AXI_ASSIGN_FROM_REQ(slave, slave_req)
  `AXI_ASSIGN_TO_RESP(slave_resp, slave)

  /*********
   *  DUT  *
   *********/

  axi_burst_unwrap #(
    .MaxReadTxns (8             ),
    .MaxWriteTxns(8             ),
    .AddrWidth   (TbAxiAddrWidth),
    .DataWidth   (TbAxiDataWidth),
    .IdWidth     (TbAxiIdWidth  ),
    .UserWidth   (TbAxiUserWidth),
    .axi_req_t   (axi_req_t     ),
    .axi_resp_t  (axi_resp_t    )
  ) i_burst_unwrap (
    .clk_i (clk),
    .rst_ni(rst_n),
    .slv_req_i(master_req),
    .slv_resp_o(master_resp),
    .mst_req_o(slave_req),
    .mst_resp_i(slave_resp)
  );

  /*************
   *  DRIVERS  *
   *************/

  initial begin
    eos = 1'b0;

    // Configuration
    slave_drv.reset()                                                                                  ;
    master_drv.reset()                                                                                 ;
    master_drv.add_memory_region(addr_t'(64'h0), addr_t'(64'h10), axi_pkg::WTHRU_NOALLOCATE);

    // Wait for the reset before sending requests
    @(posedge rst_n);

    fork
      // Act as a sink
      slave_drv.run()         ;
      master_drv.run(200, 200);
    join_any

    // Done
    repeat (10) @(posedge clk);
    eos = 1'b1;
    $stop();
  end

  /*************
   *  MONITOR  *
   *************/

  typedef axi_test::axi_scoreboard #(
    .IW(TbAxiIdWidth  ),
    .AW(TbAxiAddrWidth),
    .DW(TbAxiDataWidth),
    .UW(TbAxiUserWidth),
    .TT(TbTestTime    )
  ) axi_scoreboard_t;
  axi_scoreboard_t axi_scoreboard = new(master_dv);
  initial begin : proc_scoreboard
    axi_scoreboard.enable_all_checks();
    @(posedge rst_n);
    axi_scoreboard.monitor();
    wait (eos);
  end

// vsim -voptargs=+acc work.tb_axi_dw_downsizer
endmodule : tb_axi_burst_unwrap
