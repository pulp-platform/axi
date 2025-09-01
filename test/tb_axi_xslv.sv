// Copyright 2024 ETH Zurich and University of Bologna.
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
// - Nils Wistoff <nwistoff@iis.ee.ethz.ch>

module tb_axi_xslv;
  import autocc_axi_xbar_pkg::*;

  //-----------------------------------
  // Parameters
  //-----------------------------------
  localparam int NumUniverses = 2;

  // TB timing parameters
  localparam time CyclTime = 10ns;
  localparam time ApplTime =  2ns;
  localparam time TestTime =  8ns;

  logic           spy_mode;

  //-----------------------------------
  // DUT Signals
  //-----------------------------------
  logic                                        clk;
  logic                                        rst_n;
  slv_req_t  [NumUniverses-1:0][NumMasters-1:0] slv_ports_req;
  slv_resp_t [NumUniverses-1:0][NumMasters-1:0] slv_ports_resp;

  localparam rule_t [Cfg.NoAddrRules-1:0] AddrMap = {'{idx: 1, start_addr: 4'h8, end_addr: 4'hf},
                                                     '{idx: 0, start_addr: 4'h0, end_addr: 4'h8}};

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
  axi_xslv_wrap #(
    .Cfg(Cfg),
    .ATOPs(ATOPs),
    .Connectivity(Connectivity),
    .slv_aw_chan_t(slv_aw_chan_t),
    .mst_aw_chan_t(mst_aw_chan_t),
    .w_chan_t(slv_w_chan_t),
    .slv_b_chan_t(slv_b_chan_t),
    .mst_b_chan_t(mst_b_chan_t),
    .slv_ar_chan_t(slv_ar_chan_t),
    .mst_ar_chan_t(mst_ar_chan_t),
    .slv_r_chan_t(slv_r_chan_t),
    .mst_r_chan_t(mst_r_chan_t),
    .slv_req_t(slv_req_t),
    .slv_resp_t(slv_resp_t),
    .mst_req_t(mst_req_t),
    .mst_resp_t(mst_resp_t),
    .rule_t(rule_t)
  ) i_axi_xslv (
    .clk_i(clk),
    .rst_ni(rst_n),
    .test_i('0),
    .slv_ports_req_i_2(slv_ports_req[1]),
    .slv_ports_req_i(slv_ports_req[0]),
    .slv_ports_resp_o_2(slv_ports_resp[1]),
    .slv_ports_resp_o(slv_ports_resp[0]),
    .addr_map_i(AddrMap),
    .en_default_mst_port_i('0),
    .default_mst_port_i('0)
  );

  bind axi_xslv_wrap axi_xslv_prop #(
    .Cfg (Cfg),
    .ATOPs (ATOPs),
    .Connectivity (Connectivity),
    .slv_aw_chan_t (autocc_axi_xbar_pkg::slv_aw_chan_t),
    .mst_aw_chan_t (autocc_axi_xbar_pkg::mst_aw_chan_t),
    .w_chan_t (autocc_axi_xbar_pkg::slv_w_chan_t),
    .slv_b_chan_t (autocc_axi_xbar_pkg::slv_b_chan_t),
    .mst_b_chan_t (autocc_axi_xbar_pkg::mst_b_chan_t),
    .slv_ar_chan_t (autocc_axi_xbar_pkg::slv_ar_chan_t),
    .mst_ar_chan_t (autocc_axi_xbar_pkg::mst_ar_chan_t),
    .slv_r_chan_t (autocc_axi_xbar_pkg::slv_r_chan_t),
    .mst_r_chan_t (autocc_axi_xbar_pkg::mst_r_chan_t),
    .slv_req_t (autocc_axi_xbar_pkg::slv_req_t),
    .slv_resp_t (autocc_axi_xbar_pkg::slv_resp_t),
    .mst_req_t (autocc_axi_xbar_pkg::mst_req_t),
    .mst_resp_t (autocc_axi_xbar_pkg::mst_resp_t),
    .rule_t (autocc_axi_xbar_pkg::rule_t),
    .ASSERT_INPUTS (0)
  ) u_axi_xslv_sva(.*);

  //-----------------------------------
  // Test
  //-----------------------------------
  initial begin
    slv_ports_req               = '0;
    for (int i = 0; i < NumUniverses; i++) begin
      for (int j = 0; j < NumMasters; j++) begin
        slv_ports_req[i][j].r_ready = 1'b1;
        slv_ports_req[i][j].ar.burst = axi_pkg::BURST_INCR;
        slv_ports_req[i][j].aw.burst = axi_pkg::BURST_INCR;
      end
    end
    spy_mode = 1'b0;

    wait(rst_n);
    @(posedge clk);
    #(ApplTime);
    // for (int j = 0; j < NumMasters; j++) begin
      // slv_ports_req[0][j].ar_valid = 1'b1;
    // end
    slv_ports_req[0][0].ar_valid = 1'b1;
    slv_ports_req[1][1].ar_valid = 1'b1;

    @(posedge clk);
    #(ApplTime);
    //for (int j = 0; j < NumMasters; j++) begin
      //slv_ports_req[0][j].ar_valid = 1'b0;
    //end
    slv_ports_req[0][0].ar_valid = 1'b0;
    slv_ports_req[1][1].ar_valid = 1'b0;

    wait(slv_ports_resp[0][0].r_valid && slv_ports_resp[0][0].r.last == 1'b1);
    repeat(6) @(posedge clk);
    #(ApplTime);
    spy_mode = 1'b1;
    for (int i = 0; i < NumUniverses; i++) begin
      for (int j = 0; j < NumMasters; j++) begin
        slv_ports_req[i][j].ar_valid = 1'b1;
      end
    end

    @(posedge clk);
    #(ApplTime);
    for (int i = 0; i < NumUniverses; i++) begin
      for (int j = 0; j < NumMasters; j++) begin
        slv_ports_req[i][j].ar_valid = 1'b0;
      end
    end

    repeat(200) @(posedge clk);
    $finish();
  end

  //-----------------------------------
  // Assertions
  //-----------------------------------
  as_slv_ports_resp: assert property (@(posedge clk) disable iff (!rst_n) spy_mode |-> (slv_ports_resp[0] == slv_ports_resp[1]));

endmodule // tb_axi_xslv
