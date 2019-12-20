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

// axi_xbar: Fully-connected AXI4+ATOP crossbar with an arbitrary number of slave and master ports.
// See `doc/axi_xbar.md` for the documentation, including the definition of parameters and ports.
module axi_xbar #(
  parameter axi_pkg::xbar_cfg_t Cfg = '0,
  parameter type slv_aw_chan_t      = logic,
  parameter type mst_aw_chan_t      = logic,
  parameter type w_chan_t           = logic,
  parameter type slv_b_chan_t       = logic,
  parameter type mst_b_chan_t       = logic,
  parameter type slv_ar_chan_t      = logic,
  parameter type mst_ar_chan_t      = logic,
  parameter type slv_r_chan_t       = logic,
  parameter type mst_r_chan_t       = logic,
  parameter type slv_req_t          = logic,
  parameter type slv_resp_t         = logic,
  parameter type mst_req_t          = logic,
  parameter type mst_resp_t         = logic,
  parameter type rule_t             = axi_pkg::xbar_rule_64_t
) (
  input  logic                                                       clk_i,
  input  logic                                                       rst_ni,
  input  logic                                                       test_i,
  input  slv_req_t  [Cfg.NoSlvPorts-1:0]                             slv_ports_req_i,
  output slv_resp_t [Cfg.NoSlvPorts-1:0]                             slv_ports_resp_o,
  output mst_req_t  [Cfg.NoMstPorts-1:0]                             mst_ports_req_o,
  input  mst_resp_t [Cfg.NoMstPorts-1:0]                             mst_ports_resp_i,
  input  rule_t     [Cfg.NoAddrRules-1:0]                            addr_map_i,
  input  logic      [Cfg.NoSlvPorts-1:0]                             en_default_mst_port_i,
  input  logic      [Cfg.NoSlvPorts-1:0][$clog2(Cfg.NoMstPorts)-1:0] default_mst_port_i
);

  typedef logic [Cfg.AxiAddrWidth-1:0]           addr_t;
  // to account for the decoding error slave
  typedef logic [$clog2(Cfg.NoMstPorts + 1)-1:0] mst_port_idx_t;

  // signals from the axi_demuxes, one index more for decode error
  slv_aw_chan_t [Cfg.NoSlvPorts-1:0][Cfg.NoMstPorts:0] slv_aw_chans;
  logic         [Cfg.NoSlvPorts-1:0][Cfg.NoMstPorts:0] slv_aw_valids, slv_aw_readies;
  w_chan_t      [Cfg.NoSlvPorts-1:0][Cfg.NoMstPorts:0] slv_w_chans;
  logic         [Cfg.NoSlvPorts-1:0][Cfg.NoMstPorts:0] slv_w_valids,  slv_w_readies;
  slv_b_chan_t  [Cfg.NoSlvPorts-1:0][Cfg.NoMstPorts:0] slv_b_chans;
  logic         [Cfg.NoSlvPorts-1:0][Cfg.NoMstPorts:0] slv_b_valids,  slv_b_readies;
  slv_ar_chan_t [Cfg.NoSlvPorts-1:0][Cfg.NoMstPorts:0] slv_ar_chans;
  logic         [Cfg.NoSlvPorts-1:0][Cfg.NoMstPorts:0] slv_ar_valids, slv_ar_readies;
  slv_r_chan_t  [Cfg.NoSlvPorts-1:0][Cfg.NoMstPorts:0] slv_r_chans;
  logic         [Cfg.NoSlvPorts-1:0][Cfg.NoMstPorts:0] slv_r_valids,  slv_r_readies;

  // signals into the axi_muxes, are of type slave as the multiplexer extends the ID
  slv_aw_chan_t [Cfg.NoMstPorts-1:0][Cfg.NoSlvPorts-1:0] mst_aw_chans;
  logic         [Cfg.NoMstPorts-1:0][Cfg.NoSlvPorts-1:0] mst_aw_valids, mst_aw_readies;
  w_chan_t      [Cfg.NoMstPorts-1:0][Cfg.NoSlvPorts-1:0] mst_w_chans;
  logic         [Cfg.NoMstPorts-1:0][Cfg.NoSlvPorts-1:0] mst_w_valids,  mst_w_readies;
  slv_b_chan_t  [Cfg.NoMstPorts-1:0][Cfg.NoSlvPorts-1:0] mst_b_chans;
  logic         [Cfg.NoMstPorts-1:0][Cfg.NoSlvPorts-1:0] mst_b_valids,  mst_b_readies;
  slv_ar_chan_t [Cfg.NoMstPorts-1:0][Cfg.NoSlvPorts-1:0] mst_ar_chans;
  logic         [Cfg.NoMstPorts-1:0][Cfg.NoSlvPorts-1:0] mst_ar_valids, mst_ar_readies;
  slv_r_chan_t  [Cfg.NoMstPorts-1:0][Cfg.NoSlvPorts-1:0] mst_r_chans;
  logic         [Cfg.NoMstPorts-1:0][Cfg.NoSlvPorts-1:0] mst_r_valids,  mst_r_readies;

  for (genvar i = 0; i < Cfg.NoSlvPorts; i++) begin : gen_slv_port_demux
    logic [$clog2(Cfg.NoMstPorts)-1:0] dec_aw,        dec_ar;
    mst_port_idx_t                     slv_aw_select, slv_ar_select;
    logic                              dec_aw_valid,  dec_aw_error;
    logic                              dec_ar_valid,  dec_ar_error;

    slv_req_t  decerr_req;
    slv_resp_t decerr_resp;

    addr_decode #(
      .NoIndices  ( Cfg.NoMstPorts  ),
      .NoRules    ( Cfg.NoAddrRules ),
      .addr_t     ( addr_t          ),
      .rule_t     ( rule_t          )
    ) i_axi_aw_decode (
      .addr_i           ( slv_ports_req_i[i].aw.addr ),
      .addr_map_i       ( addr_map_i                 ),
      .idx_o            ( dec_aw                     ),
      .dec_valid_o      ( dec_aw_valid               ),
      .dec_error_o      ( dec_aw_error               ),
      .en_default_idx_i ( en_default_mst_port_i[i]   ),
      .default_idx_i    ( default_mst_port_i[i]      )
    );

    addr_decode #(
      .NoIndices  ( Cfg.NoMstPorts  ),
      .addr_t     ( addr_t          ),
      .NoRules    ( Cfg.NoAddrRules ),
      .rule_t     ( rule_t          )
    ) i_axi_ar_decode (
      .addr_i           ( slv_ports_req_i[i].ar.addr ),
      .addr_map_i       ( addr_map_i                 ),
      .idx_o            ( dec_ar                     ),
      .dec_valid_o      ( dec_ar_valid               ),
      .dec_error_o      ( dec_ar_error               ),
      .en_default_idx_i ( en_default_mst_port_i[i]   ),
      .default_idx_i    ( default_mst_port_i[i]      )
    );

    assign slv_aw_select = (dec_aw_error) ?
        mst_port_idx_t'(Cfg.NoMstPorts) : mst_port_idx_t'(dec_aw);
    assign slv_ar_select = (dec_ar_error) ?
        mst_port_idx_t'(Cfg.NoMstPorts) : mst_port_idx_t'(dec_ar);

    // make sure that the default slave does not get changed, if there is an unserved Ax
    // pragma translate_off
    `ifndef VERILATOR
    default disable iff (~rst_ni);
    default_aw_mst_port_en: assert property(
      @(posedge clk_i) (slv_ports_req_i[i].aw_valid && !slv_ports_resp_o[i].aw_ready)
          |=> $stable(en_default_mst_port_i[i]))
        else $fatal (1, $sformatf("It is not allowed to change the default mst port\
                                   enable, when there is an unserved Aw beat. Slave Port: %0d", i));
    default_aw_mst_port: assert property(
      @(posedge clk_i) (slv_ports_req_i[i].aw_valid && !slv_ports_resp_o[i].aw_ready)
          |=> $stable(default_mst_port_i[i]))
        else $fatal (1, $sformatf("It is not allowed to change the default mst port\
                                   when there is an unserved Aw beat. Slave Port: %0d", i));
    default_ar_mst_port_en: assert property(
      @(posedge clk_i) (slv_ports_req_i[i].ar_valid && !slv_ports_resp_o[i].ar_ready)
          |=> $stable(en_default_mst_port_i[i]))
        else $fatal (1, $sformatf("It is not allowed to change the enable, when\
                                   there is an unserved Ar beat. Slave Port: %0d", i));
    default_ar_mst_port: assert property(
      @(posedge clk_i) (slv_ports_req_i[i].ar_valid && !slv_ports_resp_o[i].ar_ready)
          |=> $stable(default_mst_port_i[i]))
        else $fatal (1, $sformatf("It is not allowed to change the default mst port\
                                   when there is an unserved Ar beat. Slave Port: %0d", i));
    `endif
    // pragma translate_on
    axi_demux #(
      .AxiIdWidth     ( Cfg.AxiIdWidthSlvPorts ),  // ID Width
      .aw_chan_t      ( slv_aw_chan_t          ),  // AW Channel Type
      .w_chan_t       ( w_chan_t               ),  //  W Channel Type
      .b_chan_t       ( slv_b_chan_t           ),  //  B Channel Type
      .ar_chan_t      ( slv_ar_chan_t          ),  // AR Channel Type
      .r_chan_t       ( slv_r_chan_t           ),  //  R Channel Type
      .NoMstPorts     ( Cfg.NoMstPorts + 1     ),
      .MaxTrans       ( Cfg.MaxMstTrans        ),
      .AxiLookBits    ( Cfg.AxiIdUsedSlvPorts  ),
      .FallThrough    ( Cfg.FallThrough        ),
      .SpillAw        ( Cfg.LatencyMode[9]     ),
      .SpillW         ( Cfg.LatencyMode[8]     ),
      .SpillB         ( Cfg.LatencyMode[7]     ),
      .SpillAr        ( Cfg.LatencyMode[6]     ),
      .SpillR         ( Cfg.LatencyMode[5]     )
    ) i_axi_demux (
      .clk_i            ( clk_i                        ),  // Clock
      .rst_ni           ( rst_ni                       ),  // Asynchronous reset active low
      .test_i           ( test_i                       ),  // Testmode enable
      .slv_aw_chan_i    ( slv_ports_req_i[i].aw        ),
      .slv_aw_select_i  ( slv_aw_select                ),
      .slv_aw_valid_i   ( slv_ports_req_i[i].aw_valid  ),
      .slv_aw_ready_o   ( slv_ports_resp_o[i].aw_ready ),
      .slv_w_chan_i     ( slv_ports_req_i[i].w         ),
      .slv_w_valid_i    ( slv_ports_req_i[i].w_valid   ),
      .slv_w_ready_o    ( slv_ports_resp_o[i].w_ready  ),
      .slv_b_chan_o     ( slv_ports_resp_o[i].b        ),
      .slv_b_valid_o    ( slv_ports_resp_o[i].b_valid  ),
      .slv_b_ready_i    ( slv_ports_req_i[i].b_ready   ),
      .slv_ar_chan_i    ( slv_ports_req_i[i].ar        ),
      .slv_ar_select_i  ( slv_ar_select                ),
      .slv_ar_valid_i   ( slv_ports_req_i[i].ar_valid  ),
      .slv_ar_ready_o   ( slv_ports_resp_o[i].ar_ready ),
      .slv_r_chan_o     ( slv_ports_resp_o[i].r        ),
      .slv_r_valid_o    ( slv_ports_resp_o[i].r_valid  ),
      .slv_r_ready_i    ( slv_ports_req_i[i].r_ready   ),
      .mst_aw_chans_o   ( slv_aw_chans[i]              ),
      .mst_aw_valids_o  ( slv_aw_valids[i]             ),
      .mst_aw_readies_i ( slv_aw_readies[i]            ),
      .mst_w_chans_o    ( slv_w_chans[i]               ),
      .mst_w_valids_o   ( slv_w_valids[i]              ),
      .mst_w_readies_i  ( slv_w_readies[i]             ),
      .mst_b_chans_i    ( slv_b_chans[i]               ),
      .mst_b_valids_i   ( slv_b_valids[i]              ),
      .mst_b_readies_o  ( slv_b_readies[i]             ),
      .mst_ar_chans_o   ( slv_ar_chans[i]              ),
      .mst_ar_valids_o  ( slv_ar_valids[i]             ),
      .mst_ar_readies_i ( slv_ar_readies[i]            ),
      .mst_r_chans_i    ( slv_r_chans[i]               ),
      .mst_r_valids_i   ( slv_r_valids[i]              ),
      .mst_r_readies_o  ( slv_r_readies[i]             )
    );

    // connect the decode error module to the last index of the demux master port
    assign decerr_req.aw                     = slv_aw_chans[i][Cfg.NoMstPorts];
    assign decerr_req.aw_valid               = slv_aw_valids[i][Cfg.NoMstPorts];
    assign slv_aw_readies[i][Cfg.NoMstPorts] = decerr_resp.aw_ready;

    assign decerr_req.w                      = slv_w_chans[i][Cfg.NoMstPorts];
    assign decerr_req.w_valid                = slv_w_valids[i][Cfg.NoMstPorts];
    assign slv_w_readies[i][Cfg.NoMstPorts]  = decerr_resp.w_ready;

    assign slv_b_chans[i][Cfg.NoMstPorts]    = decerr_resp.b;
    assign slv_b_valids[i][Cfg.NoMstPorts]   = decerr_resp.b_valid;
    assign decerr_req.b_ready                = slv_b_readies[i][Cfg.NoMstPorts];

    assign decerr_req.ar                     = slv_ar_chans[i][Cfg.NoMstPorts];
    assign decerr_req.ar_valid               = slv_ar_valids[i][Cfg.NoMstPorts];
    assign slv_ar_readies[i][Cfg.NoMstPorts] = decerr_resp.ar_ready;

    assign slv_r_chans[i][Cfg.NoMstPorts]    = decerr_resp.r;
    assign slv_r_valids[i][Cfg.NoMstPorts]   = decerr_resp.r_valid;
    assign decerr_req.r_ready                = slv_r_readies[i][Cfg.NoMstPorts];

    axi_decerr_slv #(
      .AxiIdWidth  ( Cfg.AxiIdWidthSlvPorts      ), // ID width
      .req_t       ( slv_req_t                   ), // AXI request struct
      .resp_t      ( slv_resp_t                  ), // AXI response struct
      .FallThrough ( 1'b0                        ),
      .MaxTrans    ( $clog2(Cfg.MaxMstTrans) + 1 )
    ) i_axi_decerr_slv (
      .clk_i      ( clk_i       ),  // Clock
      .rst_ni     ( rst_ni      ),  // Asynchronous reset active low
      .test_i     ( test_i      ),  // Testmode enable
      // slave port
      .slv_req_i  ( decerr_req  ),
      .slv_resp_o ( decerr_resp )
    );
  end

  // cross all channels
  for (genvar i = 0; i < Cfg.NoSlvPorts; i++) begin : gen_xbar_slv_cross
    for (genvar j = 0; j < Cfg.NoMstPorts; j++) begin : gen_xbar_mst_cross
      // AW Channel
      assign mst_aw_chans[j][i]   = slv_aw_chans[i][j];
      assign mst_aw_valids[j][i]  = slv_aw_valids[i][j];
      assign slv_aw_readies[i][j] = mst_aw_readies[j][i];
      // W Channel
      assign mst_w_chans[j][i]    = slv_w_chans[i][j];
      assign mst_w_valids[j][i]   = slv_w_valids[i][j];
      assign slv_w_readies[i][j]  = mst_w_readies[j][i];
      // B Channel
      assign slv_b_chans[i][j]    = mst_b_chans[j][i];
      assign slv_b_valids[i][j]   = mst_b_valids[j][i];
      assign mst_b_readies[j][i]  = slv_b_readies[i][j];
      // AR Channel
      assign mst_ar_chans[j][i]   = slv_ar_chans[i][j];
      assign mst_ar_valids[j][i]  = slv_ar_valids[i][j];
      assign slv_ar_readies[i][j] = mst_ar_readies[j][i];
      // R Channel
      assign slv_r_chans[i][j]    = mst_r_chans[j][i];
      assign slv_r_valids[i][j]   = mst_r_valids[j][i];
      assign mst_r_readies[j][i]  = slv_r_readies[i][j];
    end
  end

  for (genvar i = 0; i < Cfg.NoMstPorts; i++) begin : gen_mst_port_mux
    axi_mux #(
      .SlvAxiIDWidth ( Cfg.AxiIdWidthSlvPorts ), // ID width of the slave ports
      .slv_aw_chan_t ( slv_aw_chan_t          ), // AW Channel Type, slave ports
      .mst_aw_chan_t ( mst_aw_chan_t          ), // AW Channel Type, master port
      .w_chan_t      ( w_chan_t               ), //  W Channel Type, all ports
      .slv_b_chan_t  ( slv_b_chan_t           ), //  B Channel Type, slave ports
      .mst_b_chan_t  ( mst_b_chan_t           ), //  B Channel Type, master port
      .slv_ar_chan_t ( slv_ar_chan_t          ), // AR Channel Type, slave ports
      .mst_ar_chan_t ( mst_ar_chan_t          ), // AR Channel Type, master port
      .slv_r_chan_t  ( slv_r_chan_t           ), //  R Channel Type, slave ports
      .mst_r_chan_t  ( mst_r_chan_t           ), //  R Channel Type, master port
      .NoSlvPorts    ( Cfg.NoSlvPorts         ), // Number of Masters for the module
      .MaxWTrans     ( Cfg.MaxSlvTrans        ),
      .FallThrough   ( Cfg.FallThrough        ),
      .SpillAw       ( Cfg.LatencyMode[4]     ),
      .SpillW        ( Cfg.LatencyMode[3]     ),
      .SpillB        ( Cfg.LatencyMode[2]     ),
      .SpillAr       ( Cfg.LatencyMode[1]     ),
      .SpillR        ( Cfg.LatencyMode[0]     )
    ) i_axi_mux (
      .clk_i  ( clk_i  ),   // Clock
      .rst_ni ( rst_ni ),   // Asynchronous reset active low
      .test_i ( test_i ),   // Test Mode enable
      .slv_aw_chans_i   ( mst_aw_chans[i]              ),
      .slv_aw_valids_i  ( mst_aw_valids[i]             ),
      .slv_aw_readies_o ( mst_aw_readies[i]            ),
      .slv_w_chans_i    ( mst_w_chans[i]               ),
      .slv_w_valids_i   ( mst_w_valids[i]              ),
      .slv_w_readies_o  ( mst_w_readies[i]             ),
      .slv_b_chans_o    ( mst_b_chans[i]               ),
      .slv_b_valids_o   ( mst_b_valids[i]              ),
      .slv_b_readies_i  ( mst_b_readies[i]             ),
      .slv_ar_chans_i   ( mst_ar_chans[i]              ),
      .slv_ar_valids_i  ( mst_ar_valids[i]             ),
      .slv_ar_readies_o ( mst_ar_readies[i]            ),
      .slv_r_chans_o    ( mst_r_chans[i]               ),
      .slv_r_valids_o   ( mst_r_valids[i]              ),
      .slv_r_readies_i  ( mst_r_readies[i]             ),
      .mst_aw_chan_o    ( mst_ports_req_o[i].aw        ),
      .mst_aw_valid_o   ( mst_ports_req_o[i].aw_valid  ),
      .mst_aw_ready_i   ( mst_ports_resp_i[i].aw_ready ),
      .mst_w_chan_o     ( mst_ports_req_o[i].w         ),
      .mst_w_valid_o    ( mst_ports_req_o[i].w_valid   ),
      .mst_w_ready_i    ( mst_ports_resp_i[i].w_ready  ),
      .mst_b_chan_i     ( mst_ports_resp_i[i].b        ),
      .mst_b_valid_i    ( mst_ports_resp_i[i].b_valid  ),
      .mst_b_ready_o    ( mst_ports_req_o[i].b_ready   ),
      .mst_ar_chan_o    ( mst_ports_req_o[i].ar        ),
      .mst_ar_valid_o   ( mst_ports_req_o[i].ar_valid  ),
      .mst_ar_ready_i   ( mst_ports_resp_i[i].ar_ready ),
      .mst_r_chan_i     ( mst_ports_resp_i[i].r        ),
      .mst_r_valid_i    ( mst_ports_resp_i[i].r_valid  ),
      .mst_r_ready_o    ( mst_ports_req_o[i].r_ready   )
    );
  end

  // pragma translate_off
  `ifndef VERILATOR
  initial begin : check_params
    id_slv_req_ports: assert ($bits(slv_ports_req_i[0].aw.id ) == Cfg.AxiIdWidthSlvPorts) else
      $fatal(1, $sformatf("Slv_req and aw_chan id width not equal."));
    id_slv_resp_ports: assert ($bits(slv_ports_resp_o[0].r.id) == Cfg.AxiIdWidthSlvPorts) else
      $fatal(1, $sformatf("Slv_req and aw_chan id width not equal."));
  end
  `endif
  // pragma translate_on
endmodule
