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

// AXI XBAR: A full AXI 4 crossbar with an arbitrary number of slave and master ports.
// Features:
//  - AXI4 ID ordering compliance
//  - Full Customizable Address Mapping with an opional default master ports per slave port
//  - ATOP support
//
//  Configuration: The configuration structs of the parameters and rules can be found in the axi_pkg
//                 It is neccessary to provide all structs of every axi channel and the request
//                 and response, because it is not possible to reconstruct the fields of sub
//                 structs over multiple hierarchies.
//    Fields:    - NoSlvPorts:         The Number of slave ports created on the xbar. This many
//                                     master modules can be connected to it.
//               - NoMstPorts:         The number of master ports created on the xbar. This many
//                                     slave modules can be connected to it.
//               - MaxMstTrans:        Each master module connected to the crossbar can issue
//                                     in the worst case this many read and write transactions.
//               - MaxSlvTrans:        Each master port of the
//               - FallThrough:
//               - LatencyMode:
//               - AxiIdWidthSlvPorts:
//               - AxiIdUsedSlvPorts:
//               - AxiIdWidthMstPorts:
//               - AxiAddrWidth:
//               - AxiDataWidth:
//               - NoAddrRules:
//

//
//  Behaviour :
//    Ordering:    When there is a transaction on a slave port to a master port with the same AXI ID
//                 than is currently in flight to another master port, the crossbar will stall the
//                 AX vector till the conflicting transaction is finished.
//                 There can be to many stalls, because only the LSB's of the AXI id get checked
//                 for the 'difference' between two axi id's. Determined in Cfg Struct by the
//                 Field .AxiIdUsedSlvPorts, this has to be <= .AxiIdWidthSlvPorts
//    Latency:     The crossbar can be configured for different latencies on the channels.
//                 It does so by introducing spill register in the demuxes and muxes.
//                 In axi_pkg.sv existst the enum xbar_latency_t. In conjenction with the
//                 function get_xbar_lat(), a desired configuration can be chosen.
//
//                 There are further Fifo's between the AW channel and W channel, which 'save'
//                 the switching decision. There should under no cricumstances spill registers
//                 be introduced in the channels between the slave port demuxes and master muxes.
//                 In doing so can lead to a deadlock of the interconnect, as all 4 of the
//                 deadlock properties will be fullfilled. By populating the switching decision
//                 into the fifos in the same cycle, there can be no cyclic dependency and because
//                 of that no deadlock.
//    Address Map: The address map is defined as an packed array of rule structs.
//                 Two rule structs for address widths of 32 and 64 bit are provided in axi_pkg.sv
//                 The address mapping is global in the crossbar and the same for each slave port.
//                 The adderss decoder expects 3 fields in the struct:
//                  - mst_port_idx: index of the master port, has to be < #MST ports of the xbar
//                  - start_addr:   start address of the range the rule describes, is included
//                  - end_addr:     end address of the range the rule describes, is NOT included
//                 There can be an arbitrary number of address rules. There can be multiple
//                 ranges be defined for the same master port. The start address has to be <=
//                 the end address. Simulation will issue warnings if address ranges overlap.
//                 If there are overlaps the rule in the highest array position wins.
//                 The crossbar will answer to a wrong address with a decode error. This can be
//                 disabled by providing a corresponding default master port. Each Salve port
//                 Can has its own unique default master port. Which can be individually enabled.
//                 Be sure to have no pending Ax vector (ax_valid = 1'b1) or the address mapping
//                 on a slave port when changeing the default master port of it.






module axi_xbar #(
  parameter axi_pkg::xbar_cfg_t Cfg = '0, // Fixed Cfg of the xbar
  parameter type slv_aw_chan_t      = logic, // AW Channel Type slave  ports, needs atop field
  parameter type mst_aw_chan_t      = logic, // AW Channel Type master ports, needs atop field
  parameter type w_chan_t           = logic, //  W Channel Type both   ports
  parameter type slv_b_chan_t       = logic, //  B Channel Type slave  ports
  parameter type mst_b_chan_t       = logic, //  B Channel Type master ports
  parameter type slv_ar_chan_t      = logic, // AR Channel Type slave  ports
  parameter type mst_ar_chan_t      = logic, // AR Channel Type master ports
  parameter type slv_r_chan_t       = logic, //  R Channel Type slave  ports
  parameter type mst_r_chan_t       = logic, //  R Channel Type master ports
  parameter type slv_req_t          = logic, // encapsules seperate channels request  slave  ports
  parameter type slv_resp_t         = logic, // encapsules seperate channels response slave  ports
  parameter type mst_req_t          = logic, // encapsules seperate channels request  master ports
  parameter type mst_resp_t         = logic, // encapsules seperate channels response master ports
  parameter type rule_t             = axi_pkg::xbar_rule_64_t    // Axi address decoding rule
) (
  input  logic clk_i,  // Clock
  input  logic rst_ni, // Asynchronous reset active low
  input  logic test_i, // Test mode enable
  // slave ports, connect here the master modules
  input  slv_req_t  [Cfg.NoSlvPorts-1:0]  slv_ports_req_i,
  output slv_resp_t [Cfg.NoSlvPorts-1:0]  slv_ports_resp_o,
  // master ports, connect here the slave modules
  output mst_req_t  [Cfg.NoMstPorts-1:0]  mst_ports_req_o,
  input  mst_resp_t [Cfg.NoMstPorts-1:0]  mst_ports_resp_i,
  // addr map input
  input  rule_t     [Cfg.NoAddrRules-1:0] addr_map_i,
  // default mst port for each slv port, that each connected master can have its own default slave
  // enables the address mapping to a default master port per slave port
  // to disable, set to '0
  input  logic      [Cfg.NoSlvPorts-1:0]                             en_default_mst_port_i,
  // the array of default master ports
  input  logic      [Cfg.NoSlvPorts-1:0][$clog2(Cfg.NoMstPorts)-1:0] default_mst_port_i
);

  typedef logic [Cfg.AxiAddrWidth-1:0]           addr_t;
  typedef logic [$clog2(Cfg.NoSlvPorts)-1:0]     slv_port_idx_t;
  typedef logic [$clog2(Cfg.NoMstPorts + 1)-1:0] mst_port_idx_t; // to account for decerror

  // signals from the axi_demuxes
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

  // signals that get id prepended, the same as the ones above, but without the decerr
  slv_aw_chan_t [Cfg.NoSlvPorts-1:0][Cfg.NoMstPorts-1:0] xbar_aw_chans;
  logic         [Cfg.NoSlvPorts-1:0][Cfg.NoMstPorts-1:0] xbar_aw_valids, xbar_aw_readies;
  w_chan_t      [Cfg.NoSlvPorts-1:0][Cfg.NoMstPorts-1:0] xbar_w_chans;
  logic         [Cfg.NoSlvPorts-1:0][Cfg.NoMstPorts-1:0] xbar_w_valids,  xbar_w_readies;
  slv_b_chan_t  [Cfg.NoSlvPorts-1:0][Cfg.NoMstPorts-1:0] xbar_b_chans;
  logic         [Cfg.NoSlvPorts-1:0][Cfg.NoMstPorts-1:0] xbar_b_valids,  xbar_b_readies;
  slv_ar_chan_t [Cfg.NoSlvPorts-1:0][Cfg.NoMstPorts-1:0] xbar_ar_chans;
  logic         [Cfg.NoSlvPorts-1:0][Cfg.NoMstPorts-1:0] xbar_ar_valids, xbar_ar_readies;
  slv_r_chan_t  [Cfg.NoSlvPorts-1:0][Cfg.NoMstPorts-1:0] xbar_r_chans;
  logic         [Cfg.NoSlvPorts-1:0][Cfg.NoMstPorts-1:0] xbar_r_valids,  xbar_r_readies;

  // signals from the axi_id_prepend
  mst_aw_chan_t [Cfg.NoSlvPorts-1:0][Cfg.NoMstPorts-1:0] aw_chans;
  logic         [Cfg.NoSlvPorts-1:0][Cfg.NoMstPorts-1:0] aw_valids,     aw_readies;
  w_chan_t      [Cfg.NoSlvPorts-1:0][Cfg.NoMstPorts-1:0] w_chans;
  logic         [Cfg.NoSlvPorts-1:0][Cfg.NoMstPorts-1:0] w_valids,      w_readies;
  mst_b_chan_t  [Cfg.NoSlvPorts-1:0][Cfg.NoMstPorts-1:0] b_chans;
  logic         [Cfg.NoSlvPorts-1:0][Cfg.NoMstPorts-1:0] b_valids,      b_readies;
  mst_ar_chan_t [Cfg.NoSlvPorts-1:0][Cfg.NoMstPorts-1:0] ar_chans;
  logic         [Cfg.NoSlvPorts-1:0][Cfg.NoMstPorts-1:0] ar_valids,     ar_readies;
  mst_r_chan_t  [Cfg.NoSlvPorts-1:0][Cfg.NoMstPorts-1:0] r_chans;
  logic         [Cfg.NoSlvPorts-1:0][Cfg.NoMstPorts-1:0] r_valids,      r_readies;

  // signals into the axi_muxes
  mst_aw_chan_t [Cfg.NoMstPorts-1:0][Cfg.NoSlvPorts-1:0] mst_aw_chans;
  logic         [Cfg.NoMstPorts-1:0][Cfg.NoSlvPorts-1:0] mst_aw_valids, mst_aw_readies;
  w_chan_t      [Cfg.NoMstPorts-1:0][Cfg.NoSlvPorts-1:0] mst_w_chans;
  logic         [Cfg.NoMstPorts-1:0][Cfg.NoSlvPorts-1:0] mst_w_valids,  mst_w_readies;
  mst_b_chan_t  [Cfg.NoMstPorts-1:0][Cfg.NoSlvPorts-1:0] mst_b_chans;
  logic         [Cfg.NoMstPorts-1:0][Cfg.NoSlvPorts-1:0] mst_b_valids,  mst_b_readies;
  mst_ar_chan_t [Cfg.NoMstPorts-1:0][Cfg.NoSlvPorts-1:0] mst_ar_chans;
  logic         [Cfg.NoMstPorts-1:0][Cfg.NoSlvPorts-1:0] mst_ar_valids, mst_ar_readies;
  mst_r_chan_t  [Cfg.NoMstPorts-1:0][Cfg.NoSlvPorts-1:0] mst_r_chans;
  logic         [Cfg.NoMstPorts-1:0][Cfg.NoSlvPorts-1:0] mst_r_valids,  mst_r_readies;

  for (genvar i = 0; i < Cfg.NoSlvPorts; i++) begin : proc_gen_slv_port_demux
    logic [$clog2(Cfg.NoMstPorts)-1:0] dec_aw,        dec_ar;
    mst_port_idx_t                      slv_aw_select, slv_ar_select;
    logic                              dec_aw_valid,  dec_aw_error;
    logic                              dec_ar_valid,  dec_ar_error;

    slv_req_t  decerr_req;
    slv_resp_t decerr_resp;

    axi_addr_decode #(
      .NO_MST_PORTS ( Cfg.NoMstPorts  ),
      .addr_t       ( addr_t          ),
      .NO_RULES     ( Cfg.NoAddrRules ),
      .rule_t       ( rule_t          )
    ) i_axi_aw_decode (
      .addr_i                 ( slv_ports_req_i[i].aw.addr ),
      .addr_map_i             ( addr_map_i                 ),
      .mst_port_idx_o         ( dec_aw                     ),
      .dec_valid_o            ( dec_aw_valid               ),
      .dec_error_o            ( dec_aw_error               ),
      .en_default_mst_port_i  ( en_default_mst_port_i[i]   ),
      .default_mst_port_idx_i ( default_mst_port_i[i]      )
    );

    axi_addr_decode #(
      .NO_MST_PORTS ( Cfg.NoMstPorts  ),
      .addr_t       ( addr_t          ),
      .NO_RULES     ( Cfg.NoAddrRules ),
      .rule_t       ( rule_t          )
    ) i_axi_ar_decode (
      .addr_i                 ( slv_ports_req_i[i].ar.addr ),
      .addr_map_i             ( addr_map_i                 ),
      .mst_port_idx_o         ( dec_ar                     ),
      .dec_valid_o            ( dec_ar_valid               ),
      .dec_error_o            ( dec_ar_error               ),
      .en_default_mst_port_i  ( en_default_mst_port_i[i]   ),
      .default_mst_port_idx_i ( default_mst_port_i[i]      )
    );

    assign slv_aw_select = (dec_aw_error) ?
        mst_port_idx_t'(Cfg.NoMstPorts) : mst_port_idx_t'(dec_aw);
    assign slv_ar_select = (dec_ar_error) ?
        mst_port_idx_t'(Cfg.NoMstPorts) : mst_port_idx_t'(dec_ar);

    // make sure that the default slave does not get changed, if there is an unserved Ax
    // pragma translate_off
    `ifndef VERILATOR
    // these assertions could potentally trigger wrong
    default_aw_mst_port_en: assume property(
      @(posedge clk_i)  disable iff (~rst_ni)
        (slv_ports_req_i[i].aw_valid && !slv_ports_resp_o[i].aw_ready)
          |=> en_default_mst_port_i[i] == $past(en_default_mst_port_i[i]))
        else $fatal (1, $sformatf("axi_full_xbar > It is not allowed to change the default mst port\
                                   enable, when there is an unserved Aw beat. Salve Port: %0d", i));
    default_aw_mst_port: assume property(
      @(posedge clk_i) disable iff (~rst_ni)
        (slv_ports_req_i[i].aw_valid && !slv_ports_resp_o[i].aw_ready)
          |=> default_mst_port_i[i] == $past(default_mst_port_i[i]))
        else $fatal (1, $sformatf("axi_full_xbar > It is not allowed to change the default mst port\
                                   when there is an unserved Aw beat. Salve Port: %0d", i));
    default_ar_mst_port_en: assume property(
      @(posedge clk_i) disable iff (~rst_ni)
        (slv_ports_req_i[i].ar_valid && !slv_ports_resp_o[i].ar_ready)
          |=> en_default_mst_port_i[i] == $past(en_default_mst_port_i[i]))
        else $fatal (1, $sformatf("axi_full_xbar > It is not allowed to change the enable, when\
                                   there is an unserved Ar beat. Salve Port: %0d", i));
    default_ar_mst_port: assume property(
      @(posedge clk_i) disable iff (~rst_ni)
        (slv_ports_req_i[i].ar_valid && !slv_ports_resp_o[i].ar_ready)
          |=> default_mst_port_i[i] == $past(default_mst_port_i[i]))
        else $fatal (1, $sformatf("axi_full_xbar > It is not allowed to change the default mst port\
                                   when there is an unserved Ar beat. Salve Port: %0d", i));
    `endif
    // pragma translate_on
    axi_demux #(
      .AXI_ID_WIDTH     ( Cfg.AxiIdWidthSlvPorts ),  // ID Width
      .aw_chan_t        ( slv_aw_chan_t          ),  // AW Channel Type
      .w_chan_t         ( w_chan_t               ),  //  W Channel Type
      .b_chan_t         ( slv_b_chan_t           ),  //  B Channel Type
      .ar_chan_t        ( slv_ar_chan_t          ),  // AR Channel Type
      .r_chan_t         ( slv_r_chan_t           ),  //  R Channel Type
      .NO_MST_PORTS     ( Cfg.NoMstPorts + 1     ),
      .MAX_TRANS        ( Cfg.MaxMstTrans        ),
      .ID_COUNTER_WIDTH ( $clog2(Cfg.MaxMstTrans)),
      .AXI_LOOK_BITS    ( Cfg.AxiIdUsedSlvPorts  ),
      .FALL_THROUGH     ( Cfg.FallThrough        ),
      .SPILL_AW         ( axi_pkg::get_xbarlatmode(Cfg.LatencyMode).DemuxAw ),
      .SPILL_W          ( axi_pkg::get_xbarlatmode(Cfg.LatencyMode).DemuxW  ),
      .SPILL_B          ( axi_pkg::get_xbarlatmode(Cfg.LatencyMode).DemuxB  ),
      .SPILL_AR         ( axi_pkg::get_xbarlatmode(Cfg.LatencyMode).DemuxAr ),
      .SPILL_R          ( axi_pkg::get_xbarlatmode(Cfg.LatencyMode).DemuxR  )
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

    // decode errors
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
      .AXI_ID_WIDTH ( Cfg.AxiIdWidthSlvPorts      ), // ID Width
      .req_t        ( slv_req_t                   ), // AXI 4 REQUEST struct
      .resp_t       ( slv_resp_t                  ), // AXI 4 REQUEST struct
      .FALL_THROUGH ( 1'b0                        ),
      .MAX_TRANS    ( $clog2(Cfg.MaxMstTrans) + 1 )
    ) i_axi_decerr_slv (
      .clk_i      ( clk_i       ),  // Clock
      .rst_ni     ( rst_ni      ),  // Asynchronous reset active low
      .test_i     ( test_i      ),  // Testmode enable
      // slave port
      .slv_req_i  ( decerr_req  ),
      .slv_resp_o ( decerr_resp )
    );

    // assign only the signals that do not go to the decerror to the xbar
    for (genvar j = 0; j < Cfg.NoMstPorts; j++) begin : proc_gen_xbar_assign
      assign xbar_aw_chans[i][j]  = slv_aw_chans[i][j];
      assign xbar_aw_valids[i][j] = slv_aw_valids[i][j];
      assign slv_aw_readies[i][j] = xbar_aw_readies[i][j];

      assign xbar_w_chans[i][j]   = slv_w_chans[i][j];
      assign xbar_w_valids[i][j]  = slv_w_valids[i][j];
      assign slv_w_readies[i][j]  = xbar_w_readies[i][j];

      assign slv_b_chans[i][j]    = xbar_b_chans[i][j] ;
      assign slv_b_valids[i][j]   = xbar_b_valids[i][j];
      assign xbar_b_readies[i][j] = slv_b_readies[i][j];

      assign xbar_ar_chans[i][j]  = slv_ar_chans[i][j];
      assign xbar_ar_valids[i][j] = slv_ar_valids[i][j];
      assign slv_ar_readies[i][j] = xbar_ar_readies[i][j];

      assign slv_r_chans[i][j]    = xbar_r_chans[i][j];
      assign slv_r_valids[i][j]   = xbar_r_valids[i][j];
      assign xbar_r_readies[i][j] = slv_r_readies[i][j];
    end

    axi_id_prepend #(
      .NoBus            ( Cfg.NoMstPorts         ),
      .AxiIdWidthSlvPort( Cfg.AxiIdWidthSlvPorts ),
      .AxiIdWidthMstPort( Cfg.AxiIdWidthMstPorts ),
      .slv_aw_chan_t    ( slv_aw_chan_t          ),
      .slv_w_chan_t     ( w_chan_t               ),
      .slv_b_chan_t     ( slv_b_chan_t           ),
      .slv_ar_chan_t    ( slv_ar_chan_t          ),
      .slv_r_chan_t     ( slv_r_chan_t           ),
      .mst_aw_chan_t    ( mst_aw_chan_t          ),
      .mst_w_chan_t     ( w_chan_t               ),
      .mst_b_chan_t     ( mst_b_chan_t           ),
      .mst_ar_chan_t    ( mst_ar_chan_t          ),
      .mst_r_chan_t     ( mst_r_chan_t           )
    ) i_id_prepend (
      .pre_id_i         ( slv_port_idx_t'(i) ),
      .slv_aw_chans_i   ( xbar_aw_chans[i]   ),
      .slv_aw_valids_i  ( xbar_aw_valids[i]  ),
      .slv_aw_readies_o ( xbar_aw_readies[i] ),
      .slv_w_chans_i    ( xbar_w_chans[i]    ),
      .slv_w_valids_i   ( xbar_w_valids[i]   ),
      .slv_w_readies_o  ( xbar_w_readies[i]  ),
      .slv_b_chans_o    ( xbar_b_chans[i]    ),
      .slv_b_valids_o   ( xbar_b_valids[i]   ),
      .slv_b_readies_i  ( xbar_b_readies[i]  ),
      .slv_ar_chans_i   ( xbar_ar_chans[i]   ),
      .slv_ar_valids_i  ( xbar_ar_valids[i]  ),
      .slv_ar_readies_o ( xbar_ar_readies[i] ),
      .slv_r_chans_o    ( xbar_r_chans[i]    ),
      .slv_r_valids_o   ( xbar_r_valids[i]   ),
      .slv_r_readies_i  ( xbar_r_readies[i]  ),
      .mst_aw_chans_o   ( aw_chans[i]        ),
      .mst_aw_valids_o  ( aw_valids[i]       ),
      .mst_aw_readies_i ( aw_readies[i]      ),
      .mst_w_chans_o    ( w_chans[i]         ),
      .mst_w_valids_o   ( w_valids[i]        ),
      .mst_w_readies_i  ( w_readies[i]       ),
      .mst_b_chans_i    ( b_chans[i]         ),
      .mst_b_valids_i   ( b_valids[i]        ),
      .mst_b_readies_o  ( b_readies[i]       ),
      .mst_ar_chans_o   ( ar_chans[i]        ),
      .mst_ar_valids_o  ( ar_valids[i]       ),
      .mst_ar_readies_i ( ar_readies[i]      ),
      .mst_r_chans_i    ( r_chans[i]         ),
      .mst_r_valids_i   ( r_valids[i]        ),
      .mst_r_readies_o  ( r_readies[i]       )
    );
  end

  for (genvar i = 0; i < Cfg.NoSlvPorts; i++) begin : proc_xbar_slv_ports
    for (genvar j = 0; j <= Cfg.NoMstPorts; j++) begin : proc_xbar_mst_ports
      // AW Channel
      assign mst_aw_chans[j][i]  = aw_chans[i][j];
      assign mst_aw_valids[j][i] = aw_valids[i][j];
      assign aw_readies[i][j]    = mst_aw_readies[j][i];
      // W Channel
      assign mst_w_chans[j][i]   = w_chans[i][j];
      assign mst_w_valids[j][i]  = w_valids[i][j];
      assign w_readies[i][j]     = mst_w_readies[j][i];
      // B Channel
      assign b_chans[i][j]       = mst_b_chans[j][i];
      assign b_valids[i][j]      = mst_b_valids[j][i];
      assign mst_b_readies[j][i] = b_readies[i][j];
      // AR Channel
      assign mst_ar_chans[j][i]  = ar_chans[i][j];
      assign mst_ar_valids[j][i] = ar_valids[i][j];
      assign ar_readies[i][j]    = mst_ar_readies[j][i];
      // R Channel
      assign r_chans[i][j]       = mst_r_chans[j][i];
      assign r_valids[i][j]      = mst_r_valids[j][i];
      assign mst_r_readies[j][i] = r_readies[i][j];
    end
  end

  for (genvar i = 0; i < Cfg.NoMstPorts; i++) begin : proc_gen_mst_port_mux
    axi_mux #(
      .AXI_ID_WIDTH ( Cfg.AxiIdWidthMstPorts ), // Id Width of the axi going througth
      .aw_chan_t    ( mst_aw_chan_t          ), // AW Channel Type
      .w_chan_t     ( w_chan_t               ), //  W Channel Type
      .b_chan_t     ( mst_b_chan_t           ), //  B Channel Type
      .ar_chan_t    ( mst_ar_chan_t          ), // AR Channel Type
      .r_chan_t     ( mst_r_chan_t           ), //  R Channel Type
      .NO_SLV_PORTS ( Cfg.NoSlvPorts         ), // Number of Masters
      .MAX_W_TRANS  ( Cfg.MaxSlvTrans        ),
      .FALL_THROUGH ( Cfg.FallThrough        ),
      .SPILL_AW     ( axi_pkg::get_xbarlatmode(Cfg.LatencyMode).MuxAw ),
      .SPILL_W      ( axi_pkg::get_xbarlatmode(Cfg.LatencyMode).MuxW  ),
      .SPILL_B      ( axi_pkg::get_xbarlatmode(Cfg.LatencyMode).MuxB  ),
      .SPILL_AR     ( axi_pkg::get_xbarlatmode(Cfg.LatencyMode).MuxAr ),
      .SPILL_R      ( axi_pkg::get_xbarlatmode(Cfg.LatencyMode).MuxR  )
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
    id_slv_req_ports: assert ($bits(slv_ports_req_i[0].aw.id ) == $bits(slv_aw_chans[0][0].id)) else
      $fatal(1, $sformatf("axi_full_xbar> Slv_req and aw_chan id width not equal."));
    id_slv_resp_ports: assert ($bits(slv_ports_resp_o[0].r.id) == $bits(slv_r_chans[0][0].id)) else
      $fatal(1, $sformatf("axi_full_xbar> Slv_req and aw_chan id width not equal."));
    id_mst_req_ports: assert ($bits(mst_ports_req_o[0].aw.id) == $bits(mst_aw_chans[0][0].id)) else
      $fatal(1, $sformatf("axi_full_xbar> Slv_req and aw_chan id width not equal."));
    id_mst_resp_ports: assert ($bits(mst_ports_resp_i[0].r.id) == $bits(mst_r_chans[0][0].id)) else
      $fatal(1, $sformatf("axi_full_xbar> Slv_req and aw_chan id width not equal."));
  end
  `endif
  // pragma translate_on
endmodule
