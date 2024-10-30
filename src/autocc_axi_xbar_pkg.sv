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
// - Nils Wistoff <nwistoff@iis.ee.ethz.ch>

// Parameter definitions for AutoCC version of AXI Xbar


`include "axi/typedef.svh"

package autocc_axi_xbar_pkg;

  localparam int unsigned NumMasters        = 2;
  localparam int unsigned NumSlaves         = 2;
  localparam int unsigned AxiIdWidthMasters = 1;
  localparam int unsigned AxiDataWidth      = 16;
  localparam int unsigned AxiIdWidthSlaves  = AxiIdWidthMasters + $clog2(NumMasters);
  localparam int unsigned AxiAddrWidth      = 4;
  localparam int unsigned AxiStrbWidth      = AxiDataWidth / 8;
  localparam int unsigned AxiUserWidth      = 1;
  localparam bit          ATOPs             = 1;
  localparam bit [NumMasters-1:0][NumSlaves-1:0] Connectivity = '1;
  localparam int unsigned MstPortsIdxWidth  = $clog2(NumSlaves);

  localparam axi_pkg::xbar_cfg_t Cfg = '{
    NoSlvPorts:         NumMasters,
    NoMstPorts:         NumSlaves,
    MaxMstTrans:        4,
    MaxSlvTrans:        4,
    FallThrough:        1'b0,
    LatencyMode:        axi_pkg::CUT_ALL_AX,
    PipelineStages:     1,
    AxiIdWidthSlvPorts: AxiIdWidthMasters,
    AxiIdUsedSlvPorts:  1,
    UniqueIds:          0,
    AxiAddrWidth:       AxiAddrWidth,
    AxiDataWidth:       AxiDataWidth,
    NoAddrRules:        NumSlaves
  };

  typedef struct packed {
    int unsigned idx;
    logic [AxiAddrWidth-1:0] start_addr;
    logic [AxiAddrWidth-1:0] end_addr;
  } rule_t;

  typedef logic [AxiIdWidthSlaves-1:0]  id_mst_t;
  typedef logic [AxiIdWidthMasters-1:0] id_slv_t;
  typedef logic [AxiAddrWidth-1:0]      addr_t;
  typedef logic [AxiDataWidth-1:0]      data_t;
  typedef logic [AxiStrbWidth-1:0]      strb_t;
  typedef logic [AxiUserWidth-1:0]      user_t;

  `AXI_TYPEDEF_ALL(slv, addr_t, id_slv_t, data_t, strb_t, user_t)
  `AXI_TYPEDEF_ALL(mst, addr_t, id_mst_t, data_t, strb_t, user_t)

  // localparam rule_t [Cfg.NoAddrRules-1:0] AddrMap = {'{idx: 1, start_addr: 4'h8, end_addr: 4'hf},
  //                                                    '{idx: 0, start_addr: 4'h0, end_addr: 4'h8}};

endpackage
