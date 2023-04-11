// Copyright (c) 2020 ETH Zurich and University of Bologna.
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
// - Fabian Schuiki <fschuiki@iis.ee.ethz.ch>
// - Andreas Kurth <akurth@iis.ee.ethz.ch>

// axi_lite_xbar: Fully-connected AXI4-Lite crossbar.
// See `doc/axi_lite_xbar.md` for the documentation,
// including the definition of parameters and ports.

`include "axi/typedef.svh"

module axi_lite_xbar #(
  parameter axi_pkg::xbar_cfg_t Cfg = '0,
  parameter type      aw_chan_t     = logic,
  parameter type       w_chan_t     = logic,
  parameter type       b_chan_t     = logic,
  parameter type      ar_chan_t     = logic,
  parameter type       r_chan_t     = logic,
  parameter type axi_lite_req_t     = logic,
  parameter type axi_lite_rsp_t     = logic,
  parameter type         rule_t     = axi_pkg::xbar_rule_64_t,
  // DEPENDENT PARAMETERS, DO NOT OVERWRITE!
  parameter int unsigned MgrIdxWidth = (Cfg.NumMgrPorts > 32'd1) ? $clog2(Cfg.NumMgrPorts) : 32'd1
) (
  input  logic                                                 clk_i,
  input  logic                                                 rst_ni,
  input  logic                                                 test_i,
  input  axi_lite_req_t [Cfg.NumSbrPorts-1:0]                  sbr_ports_req_i,
  output axi_lite_rsp_t [Cfg.NumSbrPorts-1:0]                  sbr_ports_rsp_o,
  output axi_lite_req_t [Cfg.NumMgrPorts-1:0]                  mgr_ports_req_o,
  input  axi_lite_rsp_t [Cfg.NumMgrPorts-1:0]                  mgr_ports_rsp_i,
  input  rule_t         [Cfg.NumAddrRules-1:0]                 addr_map_i,
  input  logic          [Cfg.NumSbrPorts-1:0]                  en_default_mgr_port_i,
  input  logic          [Cfg.NumSbrPorts-1:0][MgrIdxWidth-1:0] default_mgr_port_i
);

  typedef logic [Cfg.AddrWidth-1:0]   addr_t;
  typedef logic [Cfg.DataWidth-1:0]   data_t;
  typedef logic [Cfg.DataWidth/8-1:0] strb_t;
  // to account for the decoding error subordinate
  typedef logic [$clog2(Cfg.NumMgrPorts + 1)-1:0] mgr_port_idx_t;
  // full AXI typedef for the decode error subordinate, id_t and user_t are logic and will be
  // removed during logic optimization as they are stable
  `AXI_TYPEDEF_AW_CHAN_T(full_aw_chan_t, addr_t, logic, logic)
  `AXI_TYPEDEF_W_CHAN_T(full_w_chan_t, data_t, strb_t, logic)
  `AXI_TYPEDEF_B_CHAN_T(full_b_chan_t, logic, logic)
  `AXI_TYPEDEF_AR_CHAN_T(full_ar_chan_t, addr_t, logic, logic)
  `AXI_TYPEDEF_R_CHAN_T(full_r_chan_t, data_t, logic, logic)
  `AXI_TYPEDEF_REQ_T(full_req_t, full_aw_chan_t, full_w_chan_t, full_ar_chan_t)
  `AXI_TYPEDEF_RSP_T(full_rsp_t, full_b_chan_t, full_r_chan_t)

  // signals from the axi_lite_demuxes, one index more for decode error routing
  axi_lite_req_t [Cfg.NumSbrPorts-1:0][Cfg.NumMgrPorts:0] sbr_reqs;
  axi_lite_rsp_t [Cfg.NumSbrPorts-1:0][Cfg.NumMgrPorts:0] sbr_rsps;

  // signals into the axi_lite_muxes, are of type subordinate as the multiplexer extends the ID
  axi_lite_req_t [Cfg.NumMgrPorts-1:0][Cfg.NumSbrPorts-1:0] mgr_reqs;
  axi_lite_rsp_t [Cfg.NumMgrPorts-1:0][Cfg.NumSbrPorts-1:0] mgr_rsps;

  for (genvar i = 0; i < Cfg.NumSbrPorts; i++) begin : gen_sbr_port_demux
    logic [MgrIdxWidth-1:0] dec_aw,        dec_ar;
    mgr_port_idx_t          sbr_aw_select, sbr_ar_select;
    logic                   dec_aw_error;
    logic                   dec_ar_error;

    full_req_t decerr_req;
    full_rsp_t decerr_rsp;

    addr_decode #(
      .NoIndices  ( Cfg.NumMgrPorts  ),
      .NoRules    ( Cfg.NumAddrRules ),
      .addr_t     ( addr_t           ),
      .rule_t     ( rule_t           )
    ) i_axi_aw_decode (
      .addr_i           ( sbr_ports_req_i[i].aw.addr ),
      .addr_map_i       ( addr_map_i                 ),
      .idx_o            ( dec_aw                     ),
      .dec_valid_o      ( /*not used*/               ),
      .dec_error_o      ( dec_aw_error               ),
      .en_default_idx_i ( en_default_mgr_port_i[i]   ),
      .default_idx_i    ( default_mgr_port_i[i]      )
    );

    addr_decode #(
      .NoIndices  ( Cfg.NumMgrPorts  ),
      .addr_t     ( addr_t           ),
      .NoRules    ( Cfg.NumAddrRules ),
      .rule_t     ( rule_t           )
    ) i_axi_ar_decode (
      .addr_i           ( sbr_ports_req_i[i].ar.addr ),
      .addr_map_i       ( addr_map_i                 ),
      .idx_o            ( dec_ar                     ),
      .dec_valid_o      ( /*not used*/               ),
      .dec_error_o      ( dec_ar_error               ),
      .en_default_idx_i ( en_default_mgr_port_i[i]   ),
      .default_idx_i    ( default_mgr_port_i[i]      )
    );

    assign sbr_aw_select = (dec_aw_error) ?
        mgr_port_idx_t'(Cfg.NumMgrPorts) : mgr_port_idx_t'(dec_aw);
    assign sbr_ar_select = (dec_ar_error) ?
        mgr_port_idx_t'(Cfg.NumMgrPorts) : mgr_port_idx_t'(dec_ar);

    // make sure that the default subordinate does not get changed, if there is an unserved Ax
    // pragma translate_off
    `ifndef VERILATOR
    default disable iff (~rst_ni);
    default_aw_mgr_port_en: assert property(
      @(posedge clk_i) (sbr_ports_req_i[i].aw_valid && !sbr_ports_rsp_o[i].aw_ready)
          |=> $stable(en_default_mgr_port_i[i]))
        else $fatal (1, $sformatf("It is not allowed to change the default mgr port\
                                   enable, when there is an unserved Aw beat. Subordinate Port: %0d", i));
    default_aw_mgr_port: assert property(
      @(posedge clk_i) (sbr_ports_req_i[i].aw_valid && !sbr_ports_rsp_o[i].aw_ready)
          |=> $stable(default_mgr_port_i[i]))
        else $fatal (1, $sformatf("It is not allowed to change the default mgr port\
                                   when there is an unserved Aw beat. Subordinate Port: %0d", i));
    default_ar_mgr_port_en: assert property(
      @(posedge clk_i) (sbr_ports_req_i[i].ar_valid && !sbr_ports_rsp_o[i].ar_ready)
          |=> $stable(en_default_mgr_port_i[i]))
        else $fatal (1, $sformatf("It is not allowed to change the enable, when\
                                   there is an unserved Ar beat. Subordinate Port: %0d", i));
    default_ar_mgr_port: assert property(
      @(posedge clk_i) (sbr_ports_req_i[i].ar_valid && !sbr_ports_rsp_o[i].ar_ready)
          |=> $stable(default_mgr_port_i[i]))
        else $fatal (1, $sformatf("It is not allowed to change the default mgr port\
                                   when there is an unserved Ar beat. Subordinate Port: %0d", i));
    `endif
    // pragma translate_on
    axi_lite_demux #(
      .aw_chan_t      ( aw_chan_t           ),  // AW Channel Type
      .w_chan_t       (  w_chan_t           ),  //  W Channel Type
      .b_chan_t       (  b_chan_t           ),  //  B Channel Type
      .ar_chan_t      ( ar_chan_t           ),  // AR Channel Type
      .r_chan_t       (  r_chan_t           ),  //  R Channel Type
      .axi_lite_req_t ( axi_lite_req_t      ),
      .axi_lite_rsp_t ( axi_lite_rsp_t      ),
      .NumMgrPorts    ( Cfg.NumMgrPorts + 1 ),
      .MaxTrans       ( Cfg.MaxMgrTrans     ),
      .FallThrough    ( Cfg.FallThrough     ),
      .SpillAw        ( Cfg.LatencyMode[9]  ),
      .SpillW         ( Cfg.LatencyMode[8]  ),
      .SpillB         ( Cfg.LatencyMode[7]  ),
      .SpillAr        ( Cfg.LatencyMode[6]  ),
      .SpillR         ( Cfg.LatencyMode[5]  )
    ) i_axi_lite_demux (
      .clk_i,   // Clock
      .rst_ni,  // Asynchronous reset active low
      .test_i,  // Testmode enable
      .sbr_port_req_i       ( sbr_ports_req_i[i] ),
      .sbr_aw_select_i ( sbr_aw_select      ),
      .sbr_ar_select_i ( sbr_ar_select      ),
      .sbr_port_rsp_o       ( sbr_ports_rsp_o[i] ),
      .mgr_ports_req_o      ( sbr_reqs[i]        ),
      .mgr_ports_rsp_i      ( sbr_rsps[i]        )
    );

    // connect the decode error module to the last index of the demux manager port
    // typedef as the decode error subordinate uses full axi
    axi_lite_to_axi #(
      .DataWidth      ( Cfg.DataWidth     ),
      .axi_lite_req_t ( axi_lite_req_t    ),
      .axi_lite_rsp_t ( axi_lite_rsp_t    ),
      .axi_req_t      ( full_req_t        ),
      .axi_rsp_t      ( full_rsp_t        )
    ) i_dec_err_conv (
      .sbr_req_lite_i ( sbr_reqs[i][Cfg.NumMgrPorts] ),
      .sbr_rsp_lite_o ( sbr_rsps[i][Cfg.NumMgrPorts] ),
      .sbr_aw_cache_i ( 4'd0                         ),
      .sbr_ar_cache_i ( 4'd0                         ),
      .mgr_port_req_o      ( decerr_req                   ),
      .mgr_port_rsp_i      ( decerr_rsp                   )
    );

    axi_err_sbr #(
      .IdWidth     ( 32'd1                ), // ID width is one as defined as logic above
      .axi_req_t   ( full_req_t           ), // AXI request struct
      .axi_rsp_t   ( full_rsp_t           ), // AXI response struct
      .Resp        ( axi_pkg::RESP_DECERR ),
      .ATOPs       ( 1'b0                 ), // no ATOPs in AXI4-Lite
      .MaxTrans    ( 1                    )  // Transactions terminate at this subordinate, and AXI4-Lite
                                             // transactions have only a single beat.
    ) i_axi_err_sbr (
      .clk_i     ( clk_i      ),  // Clock
      .rst_ni    ( rst_ni     ),  // Asynchronous reset active low
      .test_i    ( test_i     ),  // Testmode enable
      // subordinate port
      .sbr_port_req_i ( decerr_req ),
      .sbr_port_rsp_o ( decerr_rsp )
    );
  end

  // cross all channels
  for (genvar i = 0; i < Cfg.NumSbrPorts; i++) begin : gen_xbar_sbr_cross
    for (genvar j = 0; j < Cfg.NumMgrPorts; j++) begin : gen_xbar_mgr_cross
      assign mgr_reqs[j][i] = sbr_reqs[i][j];
      assign sbr_rsps[i][j] = mgr_rsps[j][i];
    end
  end

  for (genvar i = 0; i < Cfg.NumMgrPorts; i++) begin : gen_mgr_port_mux
    axi_lite_mux #(
      .aw_chan_t      ( aw_chan_t          ), // AW Channel Type
      .w_chan_t       (  w_chan_t          ), //  W Channel Type
      .b_chan_t       (  b_chan_t          ), //  B Channel Type
      .ar_chan_t      ( ar_chan_t          ), // AR Channel Type
      .r_chan_t       (  r_chan_t          ), //  R Channel Type
      .axi_lite_req_t ( axi_lite_req_t     ),
      .axi_lite_rsp_t ( axi_lite_rsp_t     ),
      .NumSbrPorts    ( Cfg.NumSbrPorts    ), // Number of Managers for the module
      .MaxTrans       ( Cfg.MaxSbrTrans    ),
      .FallThrough    ( Cfg.FallThrough    ),
      .SpillAw        ( Cfg.LatencyMode[4] ),
      .SpillW         ( Cfg.LatencyMode[3] ),
      .SpillB         ( Cfg.LatencyMode[2] ),
      .SpillAr        ( Cfg.LatencyMode[1] ),
      .SpillR         ( Cfg.LatencyMode[0] )
    ) i_axi_lite_mux (
      .clk_i,  // Clock
      .rst_ni, // Asynchronous reset active low
      .test_i, // Test Mode enable
      .sbr_ports_req_i ( mgr_reqs[i]        ),
      .sbr_ports_rsp_o ( mgr_rsps[i]        ),
      .mgr_port_req_o  ( mgr_ports_req_o[i] ),
      .mgr_port_rsp_i  ( mgr_ports_rsp_i[i] )
    );
  end
endmodule

`include "axi/assign.svh"

module axi_lite_xbar_intf #(
  parameter axi_pkg::xbar_cfg_t Cfg = '0,
  parameter type rule_t             = axi_pkg::xbar_rule_64_t
) (
  input  logic                                                     clk_i,
  input  logic                                                     rst_ni,
  input  logic                                                     test_i,
  AXI_LITE.Subordinate                                                   sbr_ports [Cfg.NumSbrPorts-1:0],
  AXI_LITE.Manager                                                  mgr_ports [Cfg.NumMgrPorts-1:0],
  input  rule_t [Cfg.NumAddrRules-1:0]                             addr_map_i,
  input  logic  [Cfg.NumSbrPorts-1:0]                              en_default_mgr_port_i,
  input  logic  [Cfg.NumSbrPorts-1:0][$clog2(Cfg.NumMgrPorts)-1:0] default_mgr_port_i
);

  typedef logic [Cfg.AddrWidth       -1:0] addr_t;
  typedef logic [Cfg.DataWidth       -1:0] data_t;
  typedef logic [Cfg.DataWidth/8     -1:0] strb_t;
  `AXI_LITE_TYPEDEF_AW_CHAN_T(aw_chan_t, addr_t)
  `AXI_LITE_TYPEDEF_W_CHAN_T(w_chan_t, data_t, strb_t)
  `AXI_LITE_TYPEDEF_B_CHAN_T(b_chan_t)
  `AXI_LITE_TYPEDEF_AR_CHAN_T(ar_chan_t, addr_t)
  `AXI_LITE_TYPEDEF_R_CHAN_T(r_chan_t, data_t)
  `AXI_LITE_TYPEDEF_REQ_T(axi_lite_req_t, aw_chan_t, w_chan_t, ar_chan_t)
  `AXI_LITE_TYPEDEF_RSP_T(axi_lite_rsp_t, b_chan_t, r_chan_t)

  axi_lite_req_t  [Cfg.NumMgrPorts-1:0]  mgr_reqs;
  axi_lite_rsp_t  [Cfg.NumMgrPorts-1:0]  mgr_rsps;
  axi_lite_req_t  [Cfg.NumSbrPorts-1:0]  sbr_reqs;
  axi_lite_rsp_t  [Cfg.NumSbrPorts-1:0]  sbr_rsps;

  for (genvar i = 0; i < Cfg.NumMgrPorts; i++) begin : gen_assign_mgr
    `AXI_LITE_ASSIGN_FROM_REQ(mgr_ports[i], mgr_reqs[i])
    `AXI_LITE_ASSIGN_TO_RSP(mgr_rsps[i], mgr_ports[i])
  end

  for (genvar i = 0; i < Cfg.NumSbrPorts; i++) begin : gen_assign_sbr
    `AXI_LITE_ASSIGN_TO_REQ(sbr_reqs[i], sbr_ports[i])
    `AXI_LITE_ASSIGN_FROM_RSP(sbr_ports[i], sbr_rsps[i])
  end

  axi_lite_xbar #(
    .Cfg            ( Cfg            ),
    .aw_chan_t      ( aw_chan_t      ),
    .w_chan_t       ( w_chan_t       ),
    .b_chan_t       ( b_chan_t       ),
    .ar_chan_t      ( ar_chan_t      ),
    .r_chan_t       ( r_chan_t       ),
    .axi_lite_req_t ( axi_lite_req_t ),
    .axi_lite_rsp_t ( axi_lite_rsp_t ),
    .rule_t         ( rule_t         )
  ) i_xbar (
    .clk_i,
    .rst_ni,
    .test_i,
    .sbr_ports_req_i (sbr_reqs),
    .sbr_ports_rsp_o (sbr_rsps),
    .mgr_ports_req_o (mgr_reqs),
    .mgr_ports_rsp_i (mgr_rsps),
    .addr_map_i,
    .en_default_mgr_port_i,
    .default_mgr_port_i
  );

endmodule
