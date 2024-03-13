// Copyright 2020 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51
//
// Authors:
// - Wolfgang Roenninger <wroennin@iis.ee.ethz.ch>
// - Andreas Kurth <akurth@iis.ee.ethz.ch>
// - Florian Zaruba <zarubaf@iis.ee.ethz.ch>
// - Thomas Benz <tbenz@iis.ee.ethz.ch>

// axi_interleaved_xbar
module axi_interleaved_xbar
import cf_math_pkg::idx_width;
#(
  parameter axi_pkg::xbar_cfg_t Cfg                                   = '0,
  parameter bit  ATOPs                                                = 1'b1,
  parameter bit [Cfg.NoSlvPorts-1:0][Cfg.NoMstPorts-1:0] Connectivity = '1,
  parameter type slv_aw_chan_t                                        = logic,
  parameter type mst_aw_chan_t                                        = logic,
  parameter type w_chan_t                                             = logic,
  parameter type slv_b_chan_t                                         = logic,
  parameter type mst_b_chan_t                                         = logic,
  parameter type slv_ar_chan_t                                        = logic,
  parameter type mst_ar_chan_t                                        = logic,
  parameter type slv_r_chan_t                                         = logic,
  parameter type mst_r_chan_t                                         = logic,
  parameter type slv_req_t                                            = logic,
  parameter type slv_resp_t                                           = logic,
  parameter type mst_req_t                                            = logic,
  parameter type mst_resp_t                                           = logic,
  parameter type rule_t                                               = axi_pkg::xbar_rule_64_t,
  // don't overwrite
  parameter int unsigned MstPortsIdxWidth =
      (Cfg.NoMstPorts == 32'd1) ? 32'd1 : unsigned'($clog2(Cfg.NoMstPorts))
) (
  input  logic                                                          clk_i,
  input  logic                                                          rst_ni,
  input  logic                                                          test_i,
  input  slv_req_t  [Cfg.NoSlvPorts-1:0]                                slv_ports_req_i,
  output slv_resp_t [Cfg.NoSlvPorts-1:0]                                slv_ports_resp_o,
  output mst_req_t  [Cfg.NoMstPorts-1:0]                                mst_ports_req_o,
  input  mst_resp_t [Cfg.NoMstPorts-1:0]                                mst_ports_resp_i,
  input  rule_t     [Cfg.NoAddrRules-1:0]                               addr_map_i,
  input  logic                                                          interleaved_mode_ena_i,
  input  logic      [Cfg.NoSlvPorts-1:0]                                en_default_mst_port_i,
`ifdef VCS
  input  logic      [Cfg.NoSlvPorts-1:0][MstPortsIdxWidth-1:0]          default_mst_port_i
`else
  input  logic      [Cfg.NoSlvPorts-1:0][idx_width(Cfg.NoMstPorts)-1:0] default_mst_port_i
`endif
);

  typedef logic [Cfg.AxiAddrWidth-1:0]           addr_t;
  // to account for the decoding error slave
`ifdef VCS
  localparam int unsigned MstPortsIdxWidthOne =
      (Cfg.NoMstPorts == 32'd1) ? 32'd1 : unsigned'($clog2(Cfg.NoMstPorts + 1));
  typedef logic [MstPortsIdxWidthOne-1:0]           mst_port_idx_t;
`else
  typedef logic [idx_width(Cfg.NoMstPorts + 1)-1:0] mst_port_idx_t;
`endif

  // signals from the axi_demuxes, one index more for decode error
  slv_req_t  [Cfg.NoSlvPorts-1:0][Cfg.NoMstPorts:0]  slv_reqs;
  slv_resp_t [Cfg.NoSlvPorts-1:0][Cfg.NoMstPorts:0]  slv_resps;

  // workaround for issue #133 (problem with vsim 10.6c)
  localparam int unsigned cfg_NoMstPorts = Cfg.NoMstPorts;

  // signals into the axi_muxes, are of type slave as the multiplexer extends the ID
  slv_req_t  [Cfg.NoMstPorts-1:0][Cfg.NoSlvPorts-1:0] mst_reqs;
  slv_resp_t [Cfg.NoMstPorts-1:0][Cfg.NoSlvPorts-1:0] mst_resps;

  // interleaved address modify
  slv_req_t  [Cfg.NoSlvPorts-1:0]      slv_reqs_mod;

  for (genvar i = 0; i < Cfg.NoSlvPorts; i++) begin : gen_slv_port_demux
`ifdef VCS
    logic [MstPortsIdxWidth-1:0]          dec_aw,        dec_ar;
    logic [MstPortsIdxWidth-1:0]          dec_inter_aw,  dec_inter_ar;
`else
    logic [idx_width(Cfg.NoMstPorts)-1:0] dec_aw,        dec_ar;
    logic [idx_width(Cfg.NoMstPorts)-1:0] dec_inter_aw,  dec_inter_ar;
`endif
    mst_port_idx_t                        slv_aw_select, slv_ar_select;
    logic                                 dec_aw_valid,  dec_aw_error;
    logic                                 dec_ar_valid,  dec_ar_error;

    localparam int unsigned BankSelLow  = 'd16;
    localparam int unsigned BankSelHigh = BankSelLow + MstPortsIdxWidth;

    // interleaved select (4kiB blocks)
    assign dec_inter_aw = slv_ports_req_i[i].aw.addr[BankSelLow +: MstPortsIdxWidth];
    assign dec_inter_ar = slv_ports_req_i[i].ar.addr[BankSelLow +: MstPortsIdxWidth];

    // interleaved address modify
    always_comb begin : proc_modify_addr_interleaved
      slv_reqs_mod[i] = slv_ports_req_i[i];

      // only modify if interleaved mode is active
      if (interleaved_mode_ena_i == 1'b1) begin
        // modify AW address by removing bank bits
        slv_reqs_mod[i].aw.addr = { {(MstPortsIdxWidth){1'b0}},
                                    slv_ports_req_i[i].aw.addr[Cfg.AxiAddrWidth-1:BankSelHigh],
                                    slv_ports_req_i[i].aw.addr[BankSelLow-1:0] };

        // modify AR address by removing bank bits
        slv_reqs_mod[i].ar.addr = { {(MstPortsIdxWidth){1'b0}},
                                    slv_ports_req_i[i].ar.addr[Cfg.AxiAddrWidth-1:BankSelHigh],
                                    slv_ports_req_i[i].ar.addr[BankSelLow-1:0] };
      end
    end

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

    always_comb begin : ax_select
      if (interleaved_mode_ena_i == 1'b1) begin
        slv_aw_select = dec_inter_aw;
        slv_ar_select = dec_inter_ar;
      end else begin
        slv_aw_select = (dec_aw_error) ?
            mst_port_idx_t'(Cfg.NoMstPorts) : mst_port_idx_t'(dec_aw);
        slv_ar_select = (dec_ar_error) ?
            mst_port_idx_t'(Cfg.NoMstPorts) : mst_port_idx_t'(dec_ar);
      end
    end

    // make sure that the default slave does not get changed, if there is an unserved Ax
    // pragma translate_off
    `ifndef VERILATOR
    `ifndef XSIM
    default disable iff (~rst_ni);
    default_aw_mst_port_en: assert property(
      @(posedge clk_i) (slv_ports_req_i[i].aw_valid && !slv_ports_resp_o[i].aw_ready)
          |=> $stable(en_default_mst_port_i[i]))
        else $fatal (1, $sformatf({"It is not allowed to change the default mst port enable,",
                                   "when there is an unserved Aw beat. Slave Port: %0d"}, i));
    default_aw_mst_port: assert property(
      @(posedge clk_i) (slv_ports_req_i[i].aw_valid && !slv_ports_resp_o[i].aw_ready)
          |=> $stable(default_mst_port_i[i]))
        else $fatal (1, $sformatf({"It is not allowed to change the default mst port",
                                   "when there is an unserved Aw beat. Slave Port: %0d"}, i));
    default_ar_mst_port_en: assert property(
      @(posedge clk_i) (slv_ports_req_i[i].ar_valid && !slv_ports_resp_o[i].ar_ready)
          |=> $stable(en_default_mst_port_i[i]))
        else $fatal (1, $sformatf({"It is not allowed to change the enable, when",
                                   "there is an unserved Ar beat. Slave Port: %0d"}, i));
    default_ar_mst_port: assert property(
      @(posedge clk_i) (slv_ports_req_i[i].ar_valid && !slv_ports_resp_o[i].ar_ready)
          |=> $stable(default_mst_port_i[i]))
        else $fatal (1, $sformatf({"It is not allowed to change the default mst port",
                                   "when there is an unserved Ar beat. Slave Port: %0d"}, i));
    `endif
    `endif
    // pragma translate_on
    axi_demux #(
      .AxiIdWidth     ( Cfg.AxiIdWidthSlvPorts ),  // ID Width
      .AtopSupport    ( ATOPs                  ),
      .aw_chan_t      ( slv_aw_chan_t          ),  // AW Channel Type
      .w_chan_t       ( w_chan_t               ),  //  W Channel Type
      .b_chan_t       ( slv_b_chan_t           ),  //  B Channel Type
      .ar_chan_t      ( slv_ar_chan_t          ),  // AR Channel Type
      .r_chan_t       ( slv_r_chan_t           ),  //  R Channel Type
      .axi_req_t      ( slv_req_t              ),
      .axi_resp_t     ( slv_resp_t             ),
      .NoMstPorts     ( Cfg.NoMstPorts + 1     ),
      .MaxTrans       ( Cfg.MaxMstTrans        ),
      .AxiLookBits    ( Cfg.AxiIdUsedSlvPorts  ),
      .UniqueIds      ( Cfg.UniqueIds          ),
      .SpillAw        ( Cfg.LatencyMode[9]     ),
      .SpillW         ( Cfg.LatencyMode[8]     ),
      .SpillB         ( Cfg.LatencyMode[7]     ),
      .SpillAr        ( Cfg.LatencyMode[6]     ),
      .SpillR         ( Cfg.LatencyMode[5]     )
    ) i_axi_demux (
      .clk_i,   // Clock
      .rst_ni,  // Asynchronous reset active low
      .test_i,  // Testmode enable
      .slv_req_i       ( slv_reqs_mod[i]     ),
      .slv_aw_select_i ( slv_aw_select       ),
      .slv_ar_select_i ( slv_ar_select       ),
      .slv_resp_o      ( slv_ports_resp_o[i] ),
      .mst_reqs_o      ( slv_reqs[i]         ),
      .mst_resps_i     ( slv_resps[i]        )
    );

    axi_err_slv #(
      .AxiIdWidth  ( Cfg.AxiIdWidthSlvPorts ),
      .axi_req_t   ( slv_req_t              ),
      .axi_resp_t  ( slv_resp_t             ),
      .Resp        ( axi_pkg::RESP_DECERR   ),
      .ATOPs       ( ATOPs                  ),
      .MaxTrans    ( 4                      )   // Transactions terminate at this slave, so minimize
                                                // resource consumption by accepting only a few
                                                // transactions at a time.
    ) i_axi_err_slv (
      .clk_i,   // Clock
      .rst_ni,  // Asynchronous reset active low
      .test_i,  // Testmode enable
      // slave port
      .slv_req_i  ( slv_reqs[i][Cfg.NoMstPorts]   ),
      .slv_resp_o ( slv_resps[i][cfg_NoMstPorts]  )
    );
  end

  // cross all channels
  for (genvar i = 0; i < Cfg.NoSlvPorts; i++) begin : gen_xbar_slv_cross
    for (genvar j = 0; j < Cfg.NoMstPorts; j++) begin : gen_xbar_mst_cross
      if (Connectivity[i][j]) begin : gen_connection
        assign mst_reqs[j][i]  = slv_reqs[i][j];
        assign slv_resps[i][j] = mst_resps[j][i];

      end else begin : gen_no_connection
        assign mst_reqs[j][i] = '0;
        axi_err_slv #(
          .AxiIdWidth ( Cfg.AxiIdWidthSlvPorts  ),
          .axi_req_t  ( slv_req_t               ),
          .axi_resp_t ( slv_resp_t              ),
          .Resp       ( axi_pkg::RESP_DECERR    ),
          .ATOPs      ( ATOPs                   ),
          .MaxTrans   ( 1                       )
        ) i_axi_err_slv (
          .clk_i,
          .rst_ni,
          .test_i,
          .slv_req_i  ( slv_reqs[i][j]  ),
          .slv_resp_o ( slv_resps[i][j] )
        );
      end
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
  `ifndef XSIM
  initial begin : check_params
    id_slv_req_ports: assert ($bits(slv_ports_req_i[0].aw.id ) == Cfg.AxiIdWidthSlvPorts) else
      $fatal(1, $sformatf("Slv_req and aw_chan id width not equal."));
    id_slv_resp_ports: assert ($bits(slv_ports_resp_o[0].r.id) == Cfg.AxiIdWidthSlvPorts) else
      $fatal(1, $sformatf("Slv_req and aw_chan id width not equal."));
  end
  `endif
  `endif
  // pragma translate_on
endmodule : axi_interleaved_xbar

`include "axi/assign.svh"
`include "axi/typedef.svh"

module axi_interleaved_xbar_intf
import cf_math_pkg::idx_width;
#(
  parameter int unsigned AXI_USER_WIDTH =  0,
  parameter bit ATOPS                   = 1'b1,
  parameter bit [Cfg.NoSlvPorts-1:0][Cfg.NoMstPorts-1:0] CONNECTIVITY = '1,
  parameter axi_pkg::xbar_cfg_t Cfg     = '0,
  parameter type rule_t                 = axi_pkg::xbar_rule_64_t
`ifdef VCS
  , localparam int unsigned MstPortsIdxWidth =
        (Cfg.NoMstPorts == 32'd1) ? 32'd1 : unsigned'($clog2(Cfg.NoMstPorts))
`endif
) (
  input  logic                                                      clk_i,
  input  logic                                                      rst_ni,
  input  logic                                                      test_i,
  AXI_BUS.Slave                                                     slv_ports [Cfg.NoSlvPorts-1:0],
  AXI_BUS.Master                                                    mst_ports [Cfg.NoMstPorts-1:0],
  input  rule_t [Cfg.NoAddrRules-1:0]                               addr_map_i,
  input  logic  [Cfg.NoSlvPorts-1:0]                                en_default_mst_port_i,
  input  logic                                                      interleaved_mode_ena_i,
`ifdef VCS
  input  logic  [Cfg.NoSlvPorts-1:0][MstPortsIdxWidth-1:0]          default_mst_port_i
`else
  input  logic  [Cfg.NoSlvPorts-1:0][idx_width(Cfg.NoMstPorts)-1:0] default_mst_port_i
`endif
);

  localparam int unsigned AxiIdWidthMstPorts = Cfg.AxiIdWidthSlvPorts + $clog2(Cfg.NoSlvPorts);

  typedef logic [AxiIdWidthMstPorts     -1:0] id_mst_t;
  typedef logic [Cfg.AxiIdWidthSlvPorts -1:0] id_slv_t;
  typedef logic [Cfg.AxiAddrWidth       -1:0] addr_t;
  typedef logic [Cfg.AxiDataWidth       -1:0] data_t;
  typedef logic [Cfg.AxiDataWidth/8     -1:0] strb_t;
  typedef logic [AXI_USER_WIDTH         -1:0] user_t;

  `AXI_TYPEDEF_AW_CHAN_T(mst_aw_chan_t, addr_t, id_mst_t, user_t)
  `AXI_TYPEDEF_AW_CHAN_T(slv_aw_chan_t, addr_t, id_slv_t, user_t)
  `AXI_TYPEDEF_W_CHAN_T(w_chan_t, data_t, strb_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T(mst_b_chan_t, id_mst_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T(slv_b_chan_t, id_slv_t, user_t)
  `AXI_TYPEDEF_AR_CHAN_T(mst_ar_chan_t, addr_t, id_mst_t, user_t)
  `AXI_TYPEDEF_AR_CHAN_T(slv_ar_chan_t, addr_t, id_slv_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(mst_r_chan_t, data_t, id_mst_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(slv_r_chan_t, data_t, id_slv_t, user_t)
  `AXI_TYPEDEF_REQ_T(mst_req_t, mst_aw_chan_t, w_chan_t, mst_ar_chan_t)
  `AXI_TYPEDEF_REQ_T(slv_req_t, slv_aw_chan_t, w_chan_t, slv_ar_chan_t)
  `AXI_TYPEDEF_RESP_T(mst_resp_t, mst_b_chan_t, mst_r_chan_t)
  `AXI_TYPEDEF_RESP_T(slv_resp_t, slv_b_chan_t, slv_r_chan_t)

  mst_req_t   [Cfg.NoMstPorts-1:0]  mst_reqs;
  mst_resp_t  [Cfg.NoMstPorts-1:0]  mst_resps;
  slv_req_t   [Cfg.NoSlvPorts-1:0]  slv_reqs;
  slv_resp_t  [Cfg.NoSlvPorts-1:0]  slv_resps;

  for (genvar i = 0; i < Cfg.NoMstPorts; i++) begin : gen_assign_mst
    `AXI_ASSIGN_FROM_REQ(mst_ports[i], mst_reqs[i])
    `AXI_ASSIGN_TO_RESP(mst_resps[i], mst_ports[i])
  end

  for (genvar i = 0; i < Cfg.NoSlvPorts; i++) begin : gen_assign_slv
    `AXI_ASSIGN_TO_REQ(slv_reqs[i], slv_ports[i])
    `AXI_ASSIGN_FROM_RESP(slv_ports[i], slv_resps[i])
  end

  axi_interleaved_xbar #(
    .Cfg  (Cfg),
    .ATOPs          ( ATOPS         ),
    .Connectivity   ( CONNECTIVITY  ),
    .slv_aw_chan_t  ( slv_aw_chan_t ),
    .mst_aw_chan_t  ( mst_aw_chan_t ),
    .w_chan_t       ( w_chan_t      ),
    .slv_b_chan_t   ( slv_b_chan_t  ),
    .mst_b_chan_t   ( mst_b_chan_t  ),
    .slv_ar_chan_t  ( slv_ar_chan_t ),
    .mst_ar_chan_t  ( mst_ar_chan_t ),
    .slv_r_chan_t   ( slv_r_chan_t  ),
    .mst_r_chan_t   ( mst_r_chan_t  ),
    .slv_req_t      ( slv_req_t     ),
    .slv_resp_t     ( slv_resp_t    ),
    .mst_req_t      ( mst_req_t     ),
    .mst_resp_t     ( mst_resp_t    ),
    .rule_t         ( rule_t        )
  ) i_interleaved_xbar (
    .clk_i,
    .rst_ni,
    .test_i,
    .slv_ports_req_i  (slv_reqs ),
    .slv_ports_resp_o (slv_resps),
    .mst_ports_req_o  (mst_reqs ),
    .mst_ports_resp_i (mst_resps),
    .addr_map_i,
    .interleaved_mode_ena_i,
    .en_default_mst_port_i,
    .default_mst_port_i
  );

endmodule : axi_interleaved_xbar_intf
