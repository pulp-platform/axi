// Copyright (c) 2014-2018 ETH Zurich, University of Bologna
// Copyright (c) 2022 PlanV GmbH
//
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.


// Snoop bus interafces
interface SNOOP_BUS #(
  parameter int unsigned SNOOP_ADDR_WIDTH = 0,
  parameter int unsigned SNOOP_DATA_WIDTH = 0
);

  typedef logic [SNOOP_ADDR_WIDTH-1:0] addr_t;
  typedef logic [SNOOP_DATA_WIDTH-1:0] data_t;

  addr_t                ac_addr;
  ace_pkg::acprot_t   ac_prot;
  ace_pkg::acsnoop_t  ac_snoop;
  logic                 ac_valid;
  logic                 ac_ready;

  ace_pkg::crresp_t     cr_resp;
  logic                 cr_valid;
  logic                 cr_ready;

  data_t                cd_data;
  logic                 cd_last;
  logic                 cd_valid;
  logic                 cd_ready;

  modport Master (
    input   ac_addr, ac_prot, ac_snoop, ac_valid, output ac_ready,
    input   cr_ready, output cr_valid, cr_resp,
    input   cd_ready, output cd_data, cd_last, cd_valid
  );

 modport Slave (
    output   ac_addr, ac_prot, ac_snoop, ac_valid, input ac_ready,
    output   cr_ready, input cr_valid, cr_resp,
    output   cd_ready, input cd_data, cd_last, cd_valid
  );


  modport Monitor (
    input    ac_addr, ac_prot, ac_snoop, ac_valid, ac_ready,
             cr_ready, cr_valid, cr_resp,
             cd_ready, cd_data, cd_last, cd_valid
  );

endinterface

/// A clocked SNOOP interface for use in design verification.
interface SNOOP_BUS_DV #(
  parameter int unsigned SNOOP_ADDR_WIDTH = 0,
  parameter int unsigned SNOOP_DATA_WIDTH = 0
)(
  input clk_i
);

  typedef logic [SNOOP_ADDR_WIDTH-1:0] addr_t;
  typedef logic [SNOOP_DATA_WIDTH-1:0] data_t;

  addr_t                ac_addr;
  ace_pkg::acprot_t   ac_prot;
  ace_pkg::acsnoop_t  ac_snoop;
  logic                 ac_valid;
  logic                 ac_ready;

  ace_pkg::crresp_t     cr_resp;
  logic                 cr_valid;
  logic                 cr_ready;

  data_t                cd_data;
  logic                 cd_last;
  logic                 cd_valid;
  logic                 cd_ready;

  modport Master (
    input   ac_addr, ac_prot, ac_snoop, ac_valid, output ac_ready,
    input   cr_ready, output cr_valid, cr_resp,
    input   cd_ready, output cd_data, cd_last, cd_valid
  );

 modport Slave (
    output   ac_addr, ac_prot, ac_snoop, ac_valid, input ac_ready,
    output   cr_ready, input cr_valid, cr_resp,
    output   cd_ready, input cd_data, cd_last, cd_valid
  );


  modport Monitor (
    input    ac_addr, ac_prot, ac_snoop, ac_valid, ac_ready,
             cr_ready, cr_valid, cr_resp,
             cd_ready, cd_data, cd_last, cd_valid
  );

  // pragma translate_off
  `ifndef VERILATOR
  // Single-Channel Assertions: Signals including valid must not change between valid and handshake.
  // AC
  assert property (@(posedge clk_i) (ac_valid && !ac_ready |=> $stable(ac_addr)));
  assert property (@(posedge clk_i) (ac_valid && !ac_ready |=> $stable(ac_snoop)));
  assert property (@(posedge clk_i) (ac_valid && !ac_ready |=> $stable(ac_prot)));
  assert property (@(posedge clk_i) (ac_valid && !ac_ready |=> ac_valid));
  // CR
  assert property (@(posedge clk_i) (cr_valid && !cr_ready |=> $stable(cr_resp)));
  assert property (@(posedge clk_i) (cr_valid && !cr_ready |=> cr_valid));
  // CD
  assert property (@(posedge clk_i) (cd_valid && !cd_ready |=> $stable(cd_data)));
  assert property (@(posedge clk_i) (cd_valid && !cd_ready |=> $stable(cd_last)));
  assert property (@(posedge clk_i) (cd_valid && !cd_ready |=> cd_valid));
  `endif
  // pragma translate_on

endinterface
