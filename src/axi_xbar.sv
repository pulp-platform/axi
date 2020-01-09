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

// AXI XBAR: A full AXI 4+ATOP crossbar with an arbitrary number of slave and master ports.
// Features:
//  - AXI4 ID ordering compliance
//  - Full Customizable Address Mapping with an optional default master ports per slave port
//  - ATOP support
//
//  Configuration: The configuration structs of the parameters and rules can be found in the axi_pkg
//                 It is necessary to provide all structs of every AXI channel and the request
//                 and response, because it is not possible to reconstruct the fields of sub
//                 structs over multiple hierarchies.
//    Fields:    - NoSlvPorts:         The Number of slave ports created on the xbar. This many
//                                     master modules can be connected to it.
//               - NoMstPorts:         The number of master ports created on the xbar. This many
//                                     slave modules can be connected to it.
//               - MaxMstTrans:        Each master module connected to the crossbar can have at
//                                     most this many read and write transactions in flight.
//               - MaxSlvTrans:        Each master port of the crossbar (to the slave modules)
//                                     supports at most this many transactions in flight per ID.
//               - FallThrough:        The FIFOs that store the switching decision from the
//                                     AW channel to the W channel are in FallThrough mode.
//                                     Can lead to combinational switching, but the longest path in
//                                     synthesis will be longer.
//               - LatencyMode:        A 10-bit vector that encodes the generation of spill
//                                     registers on different points in the crossbar.
//                                     The enum xbar_latency_t found in axi_pkg has some
//                                     common configurations.
//               - AxiIdWidthSlvPorts: The AXI ID width of the slave ports.
//               - AxiIdUsedSlvPorts:  The crossbar uses this many LSBs of the slave port AXI ID
//                                     to determine the uniqueness of an AXI ID. This value
//                                     has to be equal or smaller than the AXI ID width of the
//                                     slave ports.
//               - AxiIdWidthMstPorts: The AXI ID width of the master ports.
//               - AxiAddrWidth:       The AXI address width of the slave ports.
//               - AxiDataWidth:       The AXI data width of the slave ports.
//               - NoAddrRules:        The crossbar has this many address rules.
//
//  Behavior :
//    Ordering:    When there is a transaction on a slave port to a master port with the same AXI ID
//                 as currently in flight to another master port, the crossbar will stall the
//                 AX channel till the conflicting transaction is finished.
//                 There can be the possibility of accidental stalls, because only the LSB's of the
//                 AXI ID get checked for the 'difference' between two AXI id's. Determined in Cfg
//                 struct by the Field `.AxiIdUsedSlvPorts`, this has to be smaller or equal than
//                 `.AxiIdWidthSlvPorts`.
//    Latency:     The crossbar can be configured for different latencies on the channels.
//                 It does so by introducing spill register in the demuxes and muxes.
//                 axi_pkg defines enum xbar_latency_t, which has some configurations
//                 predefined, but any 10-bit vector can be used.
//                 There are further FIFOs between the AW channel and W channel, which 'save'
//                 the switching decision. Under no circumstances may spill registers
//                 be inserted into the channels between the slave port demuxes and master muxes.
//                 Doing so can lead to a deadlock of the interconnect, as all 4 of the
//                 deadlock properties will be fulfilled. By forwarding the switching decision
//                 into the FIFOs in the same cycle, there can be no cyclic dependency, so
//                 no deadlock.
//    Address Map: The address map is defined as a packed array of rule structs.
//                 Two rule structs for address widths of 32 and 64 bit are provided in axi_pkg
//                 The address mapping is global in the crossbar and the same for each slave port.
//                 The address decoder expects 3 fields in the struct:
//                  - `idx`:        index of the master port, has to be < #MST ports of the xbar
//                  - `start_addr`: start address of the range the rule describes, is included
//                  - `end_addr`:   end address of the range the rule describes, is NOT included
//                 There can be an arbitrary number of address rules. There can be multiple
//                 ranges defined for the same master port. The start address has to be <=
//                 the end address. Simulation will issue warnings if address ranges overlap.
//                 If there are overlaps, the rule in the highest array position wins.
//                 The crossbar will answer to a wrong address with a decode error. This can be
//                 disabled by providing a corresponding default master port. Each slave port
//                 can have its own unique default master port, which can be individually enabled.
//                 Be sure to have no pending Ax request (`ax_valid = 1'b1`) when changing the
//                 global address mapping. The same applies when changing a default master port for
//                 the respective slave port.

module axi_xbar #(
  parameter axi_pkg::xbar_cfg_t Cfg = '0, // Fixed Cfg of the xbar
  parameter type slv_aw_chan_t      = logic, // AW Channel Type slave  ports, needs ATOP field
  parameter type mst_aw_chan_t      = logic, // AW Channel Type master ports, needs ATOP field
  parameter type w_chan_t           = logic, //  W Channel Type both   ports
  parameter type slv_b_chan_t       = logic, //  B Channel Type slave  ports
  parameter type mst_b_chan_t       = logic, //  B Channel Type master ports
  parameter type slv_ar_chan_t      = logic, // AR Channel Type slave  ports
  parameter type mst_ar_chan_t      = logic, // AR Channel Type master ports
  parameter type slv_r_chan_t       = logic, //  R Channel Type slave  ports
  parameter type mst_r_chan_t       = logic, //  R Channel Type master ports
  parameter type slv_req_t          = logic, // encapsulates separate channels request  slave  ports
  parameter type slv_resp_t         = logic, // encapsulates separate channels response slave  ports
  parameter type mst_req_t          = logic, // encapsulates separate channels request  master ports
  parameter type mst_resp_t         = logic, // encapsulates separate channels response master ports
  parameter type rule_t             = axi_pkg::xbar_rule_64_t // address decoding rule
) (
  input  logic                                                       clk_i,  // Clock
  // Asynchronous reset active low
  input  logic                                                       rst_ni,
  input  logic                                                       test_i, // Test mode enable
  // slave ports, connect the master modules here
  input  slv_req_t  [Cfg.NoSlvPorts-1:0]                             slv_ports_req_i,
  output slv_resp_t [Cfg.NoSlvPorts-1:0]                             slv_ports_resp_o,
  // master ports, connect the slave modules here
  output mst_req_t  [Cfg.NoMstPorts-1:0]                             mst_ports_req_o,
  input  mst_resp_t [Cfg.NoMstPorts-1:0]                             mst_ports_resp_i,
  // address map
  input  rule_t     [Cfg.NoAddrRules-1:0]                            addr_map_i,
  // default master port for each slave port, set to '0 to disable
  input  logic      [Cfg.NoSlvPorts-1:0]                             en_default_mst_port_i,
  // the array of default master ports
  input  logic      [Cfg.NoSlvPorts-1:0][$clog2(Cfg.NoMstPorts)-1:0] default_mst_port_i
);

  typedef logic [Cfg.AxiAddrWidth-1:0]           addr_t;
  // to account for the decoding error slave
  typedef logic [$clog2(Cfg.NoMstPorts + 1)-1:0] mst_port_idx_t;

  // signals from the axi_demuxes, one index more for decode error
  slv_req_t  [Cfg.NoSlvPorts-1:0][Cfg.NoMstPorts:0]  slv_reqs;
  slv_resp_t [Cfg.NoSlvPorts-1:0][Cfg.NoMstPorts:0]  slv_resps;

  // signals into the axi_muxes, are of type slave as the multiplexer extends the ID
  slv_req_t  [Cfg.NoMstPorts-1:0][Cfg.NoSlvPorts-1:0] mst_reqs;
  slv_resp_t [Cfg.NoMstPorts-1:0][Cfg.NoSlvPorts-1:0] mst_resps;

  for (genvar i = 0; i < Cfg.NoSlvPorts; i++) begin : gen_slv_port_demux
    logic [$clog2(Cfg.NoMstPorts)-1:0] dec_aw,        dec_ar;
    mst_port_idx_t                     slv_aw_select, slv_ar_select;
    logic                              dec_aw_valid,  dec_aw_error;
    logic                              dec_ar_valid,  dec_ar_error;

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
      .req_t          ( slv_req_t              ),
      .resp_t         ( slv_resp_t             ),
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
      .clk_i,   // Clock
      .rst_ni,  // Asynchronous reset active low
      .test_i,  // Testmode enable
      .slv_req_i       ( slv_ports_req_i[i]  ),
      .slv_aw_select_i ( slv_aw_select       ),
      .slv_ar_select_i ( slv_ar_select       ),
      .slv_resp_o      ( slv_ports_resp_o[i] ),
      .mst_reqs_o      ( slv_reqs[i]         ),
      .mst_resps_i     ( slv_resps[i]        )
    );

    axi_decerr_slv #(
      .AxiIdWidth  ( Cfg.AxiIdWidthSlvPorts      ), // ID width
      .req_t       ( slv_req_t                   ), // AXI request struct
      .resp_t      ( slv_resp_t                  ), // AXI response struct
      .FallThrough ( 1'b0                        ),
      .MaxTrans    ( $clog2(Cfg.MaxMstTrans) + 1 )
    ) i_axi_decerr_slv (
      .clk_i,   // Clock
      .rst_ni,  // Asynchronous reset active low
      .test_i,  // Testmode enable
      // slave port
      .slv_req_i  ( slv_reqs[i][Cfg.NoMstPorts]  ),
      .slv_resp_o ( slv_resps[i][Cfg.NoMstPorts] )
    );
  end

  // cross all channels
  for (genvar i = 0; i < Cfg.NoSlvPorts; i++) begin : gen_xbar_slv_cross
    for (genvar j = 0; j < Cfg.NoMstPorts; j++) begin : gen_xbar_mst_cross
      assign mst_reqs[j][i]  = slv_reqs[i][j];
      assign slv_resps[i][j] = mst_resps[j][i];
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
      .slv_req_t     ( slv_req_t              ),
      .slv_resp_t    ( slv_resp_t             ),
      .mst_req_t     ( mst_req_t              ),
      .mst_resp_t    ( mst_resp_t             ),
      .NoSlvPorts    ( Cfg.NoSlvPorts         ), // Number of Masters for the module
      .MaxWTrans     ( Cfg.MaxSlvTrans        ),
      .FallThrough   ( Cfg.FallThrough        ),
      .SpillAw       ( Cfg.LatencyMode[4]     ),
      .SpillW        ( Cfg.LatencyMode[3]     ),
      .SpillB        ( Cfg.LatencyMode[2]     ),
      .SpillAr       ( Cfg.LatencyMode[1]     ),
      .SpillR        ( Cfg.LatencyMode[0]     )
    ) i_axi_mux (
      .clk_i,   // Clock
      .rst_ni,  // Asynchronous reset active low
      .test_i,  // Test Mode enable
      .slv_reqs_i  ( mst_reqs[i]         ),
      .slv_resps_o ( mst_resps[i]        ),
      .mst_req_o   ( mst_ports_req_o[i]  ),
      .mst_resp_i  ( mst_ports_resp_i[i] )
    );
  end

  // pragma translate_off
  `ifndef VERILATOR
  initial begin : check_params
    id_slv_req_ports: assert ($bits(slv_ports_req_i[0].aw.id ) == Cfg.AxiIdWidthSlvPorts) else
      $fatal(1, $sformatf("Slv_req and aw_chan id width not equal."));
    id_slv_resp_ports: assert ($bits(slv_ports_resp_o[0].r.id) == Cfg.AxiIdWidthSlvPorts) else
      $fatal(1, $sformatf("Slv_req and aw_chan id width not equal."));
    id_mst_req_ports: assert ($bits(mst_ports_req_o[0].aw.id) == Cfg.AxiIdWidthMstPorts) else
      $fatal(1, $sformatf("Slv_req and aw_chan id width not equal."));
    id_mst_resp_ports: assert ($bits(mst_ports_resp_i[0].r.id) == Cfg.AxiIdWidthMstPorts) else
      $fatal(1, $sformatf("Slv_req and aw_chan id width not equal."));
  end
  `endif
  // pragma translate_on
endmodule
