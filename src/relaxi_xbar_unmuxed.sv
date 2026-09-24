// Copyright (c) 2019 ETH Zurich and University of Bologna.
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
// - Andreas Kurth <akurth@iis.ee.ethz.ch>
// - Florian Zaruba <zarubaf@iis.ee.ethz.ch>

/// axi_xbar: Fully-connected AXI4+ATOP crossbar with an arbitrary number of slave and master ports.
/// See `doc/axi_xbar.md` for the documentation, including the definition of parameters and ports.
module relaxi_xbar_unmuxed
import cf_math_pkg::idx_width;
#(
  /// Configuration struct for the crossbar see `axi_pkg` for fields and definitions.
  parameter axi_pkg::xbar_cfg_t Cfg                                   = '0,
  /// Enable atomic operations support.
  parameter bit  ATOPs                                                = 1'b1,
  /// Connectivity matrix
  parameter bit [Cfg.NoSlvPorts-1:0][Cfg.NoMstPorts-1:0] Connectivity = '1,
  /// AXI4+ATOP AW channel struct type for the slave ports.
  parameter type aw_chan_t                                            = logic,
  /// AXI4+ATOP W channel struct type for all ports.
  parameter type w_chan_t                                             = logic,
  /// AXI4+ATOP B channel struct type for the slave ports.
  parameter type b_chan_t                                             = logic,
  /// AXI4+ATOP AR channel struct type for the slave ports.
  parameter type ar_chan_t                                            = logic,
  /// AXI4+ATOP R channel struct type for the slave ports.
  parameter type r_chan_t                                             = logic,
  /// AXI4+ATOP request struct type for the slave ports.
  parameter type req_t                                                = logic,
  /// AXI4+ATOP response struct type for the slave ports.
  parameter type resp_t                                               = logic,
  /// Address rule type for the address decoders from `common_cells:addr_decode`.
  /// Example types are provided in `axi_pkg`.
  /// Required struct fields:
  /// ```
  /// typedef struct packed {
  ///   int unsigned idx;
  ///   axi_addr_t   start_addr;
  ///   axi_addr_t   end_addr;
  /// } rule_t;
  /// ```
  parameter type rule_t                                               = axi_pkg::xbar_rule_64_t,
  localparam int unsigned MstPortsIdxWidth =
      (Cfg.NoMstPorts == 32'd1) ? 32'd1 : unsigned'($clog2(Cfg.NoMstPorts))
) (
  /// Clock, positive edge triggered.
  input  logic                                                          clk_i,
  /// Asynchronous reset, active low.
  input  logic                                                          rst_ni,
  /// Testmode enable, active high.
  input  logic                                                          test_i,
  /// AXI4+ATOP requests to the slave ports.
  input  req_t  [Cfg.NoSlvPorts-1:0]                                    slv_ports_req_i,
  /// AXI4+ATOP responses of the slave ports.
  output resp_t [Cfg.NoSlvPorts-1:0]                                    slv_ports_resp_o,
  /// AXI4+ATOP requests of the master ports.
  output req_t  [Cfg.NoMstPorts-1:0][Cfg.NoSlvPorts-1:0]                mst_ports_req_o,
  /// AXI4+ATOP responses to the master ports.
  input  resp_t [Cfg.NoMstPorts-1:0][Cfg.NoSlvPorts-1:0]                mst_ports_resp_i,
  /// Address map array input for the crossbar. This map is global for the whole module.
  /// It is used for routing the transactions to the respective master ports.
  /// Each master port can have multiple different rules.
  input  rule_t     [Cfg.NoAddrRules-1:0]                               addr_map_i,
  /// Enable default master port.
  input  logic      [Cfg.NoSlvPorts-1:0]                                en_default_mst_port_i,
  /// Enables a default master port for each slave port. When this is enabled unmapped
  /// transactions get issued at the master port given by `default_mst_port_i`.
  /// When not used, tie to `'0`.
  input  logic      [Cfg.NoSlvPorts-1:0][MstPortsIdxWidth-1:0]          default_mst_port_i,

  output logic [1:0]                                                    fault_o
);

  // fault collectors
  logic [Cfg.NoSlvPorts-1:0][1:0]                   demux_fault;
  logic [Cfg.NoSlvPorts-1:0][1:0]                   errslv_demux_fault;
  logic [Cfg.NoSlvPorts-1:0][Cfg.NoMstPorts-1:0][1:0] cut_fault;
  logic [Cfg.NoSlvPorts-1:0][Cfg.NoMstPorts-1:0][1:0] errslv_conn_fault;

  logic [Cfg.NoSlvPorts-1:0] aw_sel_fault, ar_sel_fault;   // decode-divergence detection
  logic [1:0]                dec_fault_reduced; // Reduce the per-copy address-decode faults (3 TMR copies x slaves x 2 bits)

  localparam int unsigned AxiIdWidthRel = Cfg.AxiIdWidthSlvPorts + $clog2(Cfg.NoSlvPorts);
  // Address tpye for inidvidual address signals
  typedef logic [Cfg.AxiAddrWidth-1:0] addr_t;
  // to account for the decoding error slave
  localparam int unsigned MstPortsIdxWidthOne =
      (Cfg.NoMstPorts == 32'd1) ? 32'd1 : unsigned'($clog2(Cfg.NoMstPorts + 1));
  typedef logic [MstPortsIdxWidthOne-1:0]           mst_port_idx_t;
  // signals from the axi_demuxes, one index more for decode error
  req_t  [Cfg.NoSlvPorts-1:0][Cfg.NoMstPorts:0]  slv_reqs;
  resp_t [Cfg.NoSlvPorts-1:0][Cfg.NoMstPorts:0]  slv_resps;

  // Collect plain AW and AR addresses from all slave ports for the TMR decode logic
  logic [Cfg.NoSlvPorts-1:0][Cfg.AxiAddrWidth-1:0] slv_aw_addrs, slv_ar_addrs;
  for (genvar j = 0; j < Cfg.NoSlvPorts; j++) begin : gen_addr_collect
    assign slv_aw_addrs[j] = slv_ports_req_i[j].aw.addr;
    assign slv_ar_addrs[j] = slv_ports_req_i[j].ar.addr;
  end

  localparam int unsigned cfg_NoMstPorts = Cfg.NoMstPorts;
  mst_port_idx_t [Cfg.NoSlvPorts-1:0][2:0] slv_aw_select;
  mst_port_idx_t [Cfg.NoSlvPorts-1:0][2:0] slv_ar_select;
  // Per-TMR-copy outputs from tmr_part (all slave ports)
  mst_port_idx_t [2:0][Cfg.NoSlvPorts-1:0] tmr_aw_sel, tmr_ar_sel;

  // Transpose: slv_aw_select[slave][tmr] = tmr_aw_sel[tmr][slave]
  for (genvar j = 0; j < Cfg.NoSlvPorts; j++) begin : gen_sel_rearrange
    for (genvar k = 0; k < 3; k++) begin : gen_sel_tmr
      assign slv_aw_select[j][k] = tmr_aw_sel[k][j];
      assign slv_ar_select[j][k] = tmr_ar_sel[k][j];
    end
  end

  // Decode-select fault detection: 3 combinational decoder replicas, carried forward
  // (no vote-to-single, no SPOF; no correction, combinational, no state to scrub).
  // A divergence among replicas is a detected fault, masked downstream at the boundary.
  for (genvar j = 0; j < Cfg.NoSlvPorts; j++) begin : gen_decode_cmp
    assign aw_sel_fault[j] = (tmr_aw_sel[0][j] != tmr_aw_sel[1][j])
                           | (tmr_aw_sel[1][j] != tmr_aw_sel[2][j]);
    assign ar_sel_fault[j] = (tmr_ar_sel[0][j] != tmr_ar_sel[1][j])
                           | (tmr_ar_sel[1][j] != tmr_ar_sel[2][j]);
  end
  assign dec_fault_reduced[0] = (|aw_sel_fault) | (|ar_sel_fault);  // TMR, corrected bit
  assign dec_fault_reduced[1] = 1'b0;                                // never uncorrectable

  for (genvar i = 0; i < 3; i++) begin : gen_tmr_part
    relaxi_xbar_unmuxed_tmr_part #(
      .Cfg         ( Cfg                                    ),
      .rule_t      ( rule_t                                 )
    ) i_tmr_part (
      .aw_addr_i          ( slv_aw_addrs           ),
      .ar_addr_i          ( slv_ar_addrs           ),
      .addr_map_i         ( addr_map_i             ),
      .en_default_idx_i   ( en_default_mst_port_i  ),
      .default_idx_i      ( default_mst_port_i     ),
      .slv_aw_select      ( tmr_aw_sel[i]          ),
      .slv_ar_select      ( tmr_ar_sel[i]          )
    );
  end

  for (genvar i = 0; i < Cfg.NoSlvPorts; i++) begin : gen_slv_port_demux
    // make sure that the default slave does not get changed, if there is an unserved Ax
    // pragma translate_off
    `ifndef VERILATOR
    `ifndef XSIM
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
    `endif
    // pragma translate_on
    relaxi_demux #(
      .AxiIdWidth     ( AxiIdWidthRel          ),  // ID Width
      .AtopSupport    ( ATOPs                  ),
      .aw_chan_t      ( aw_chan_t              ),  // AW Channel Type
      .w_chan_t       ( w_chan_t               ),  //  W Channel Type
      .b_chan_t       ( b_chan_t               ),  //  B Channel Type
      .ar_chan_t      ( ar_chan_t              ),  // AR Channel Type
      .r_chan_t       ( r_chan_t               ),  //  R Channel Type
      .axi_req_t      ( req_t                  ),
      .axi_resp_t     ( resp_t                 ),
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
      .slv_req_i       ( slv_ports_req_i[i]  ),
      .slv_aw_select_i ( slv_aw_select[i]    ),
      .slv_ar_select_i ( slv_ar_select[i]    ),
      .slv_resp_o      ( slv_ports_resp_o[i] ),
      .mst_reqs_o      ( slv_reqs[i]         ),
      .mst_resps_i     ( slv_resps[i]        ),
      .fault_o         ( demux_fault[i]      )
    );

    relaxi_err_slv #(
      .AxiIdWidth  ( AxiIdWidthRel          ),
      .axi_req_t   ( req_t                  ),
      .axi_resp_t  ( resp_t                 ),
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
      .slv_resp_o ( slv_resps[i][cfg_NoMstPorts]  ),
      .fault_o    ( errslv_demux_fault[i]         )
    );
  end

  // cross all channels
  for (genvar i = 0; i < Cfg.NoSlvPorts; i++) begin : gen_xbar_slv_cross
    for (genvar j = 0; j < Cfg.NoMstPorts; j++) begin : gen_xbar_mst_cross
      if (Connectivity[i][j]) begin : gen_connection
        assign errslv_conn_fault[i][j] = 2'b00;
        relaxi_multicut #(
          .NoCuts     ( Cfg.PipelineStages ),
          .aw_chan_t  ( aw_chan_t          ),
          .w_chan_t   ( w_chan_t           ),
          .b_chan_t   ( b_chan_t           ),
          .ar_chan_t  ( ar_chan_t          ),
          .r_chan_t   ( r_chan_t           ),
          .axi_req_t  ( req_t              ),
          .axi_resp_t ( resp_t             )
        ) i_axi_multicut_xbar_pipeline (
          .clk_i,
          .rst_ni,
          .slv_req_i  ( slv_reqs[i][j]         ),
          .slv_resp_o ( slv_resps[i][j]        ),
          .mst_req_o  ( mst_ports_req_o[j][i]  ),
          .mst_resp_i ( mst_ports_resp_i[j][i] ),
          .fault_o    ( cut_fault[i][j]        )
        );

      end else begin : gen_no_connection
        assign mst_ports_req_o[j][i] = '0;
        assign cut_fault[i][j] = 2'b00;              // no cut here
        relaxi_err_slv #(
          .AxiIdWidth ( AxiIdWidthRel           ),
          .axi_req_t  ( req_t                   ),
          .axi_resp_t ( resp_t                  ),
          .Resp       ( axi_pkg::RESP_DECERR    ),
          .ATOPs      ( ATOPs                   ),
          .MaxTrans   ( 1                       )
        ) i_axi_err_slv (
          .clk_i,
          .rst_ni,
          .test_i,
          .slv_req_i  ( slv_reqs[i][j]  ),
          .slv_resp_o ( slv_resps[i][j] ),
          .fault_o    ( errslv_conn_fault[i][j] )
        );
      end
    end
  end

  // Aggregate all sources to fault_o
  always_comb begin
    fault_o = dec_fault_reduced;
    for (int i = 0; i < Cfg.NoSlvPorts; i++) begin
      fault_o |= demux_fault[i];
      fault_o |= errslv_demux_fault[i];
      for (int j = 0; j < Cfg.NoMstPorts; j++) begin
        fault_o |= cut_fault[i][j];
        fault_o |= errslv_conn_fault[i][j];
      end
    end
  end

  // pragma translate_off
  `ifndef VERILATOR
  `ifndef XSIM
  initial begin : check_params
    $display("DEBUG aw.id=%0d AxiIdWidthRel=%0d r.id=%0d",
      $bits(slv_ports_req_i[0].aw.id), AxiIdWidthRel,
      $bits(slv_ports_resp_o[0].r.id));
    id_slv_req_ports: assert ($bits(slv_ports_req_i[0].aw.id ) == AxiIdWidthRel) else
      $fatal(1, $sformatf("Slv_req aw_chan id width mismatch"));
    id_slv_resp_ports: assert ($bits(slv_ports_resp_o[0].r.id) == AxiIdWidthRel) else
      $fatal(1, $sformatf("Slv_resp r_chan id width mismatch"));
  end
  `endif
  `endif
  // pragma translate_on
endmodule

(* no_ungroup *)
(* no_boundary_optimization *)
module relaxi_xbar_unmuxed_tmr_part #(
  parameter axi_pkg::xbar_cfg_t Cfg = '0,
  parameter type rule_t              = axi_pkg::xbar_rule_64_t,
  localparam int unsigned MstPortsIdxWidthOne =
      (Cfg.NoMstPorts == 32'd1) ? 32'd1 : unsigned'($clog2(Cfg.NoMstPorts + 1)),
  localparam int unsigned IdxWidth =
      (Cfg.NoMstPorts > 32'd1) ? unsigned'($clog2(Cfg.NoMstPorts)) : 32'd1,
  localparam type mst_port_idx_t      = logic [MstPortsIdxWidthOne-1:0]
) (
  input  logic [Cfg.NoSlvPorts-1:0][Cfg.AxiAddrWidth-1:0] aw_addr_i,
  input  logic [Cfg.NoSlvPorts-1:0][Cfg.AxiAddrWidth-1:0] ar_addr_i,
  input  rule_t [Cfg.NoAddrRules-1:0]                      addr_map_i,
  input  logic [Cfg.NoSlvPorts-1:0]                        en_default_idx_i,
  input  logic [Cfg.NoSlvPorts-1:0][IdxWidth-1:0]          default_idx_i,
  output mst_port_idx_t [Cfg.NoSlvPorts-1:0]               slv_aw_select,
  output mst_port_idx_t [Cfg.NoSlvPorts-1:0]               slv_ar_select
);

  typedef logic [Cfg.AxiAddrWidth-1:0] addr_t;

  for (genvar i = 0; i < Cfg.NoSlvPorts; i++) begin : gen_slv_port_demux
    logic dec_aw_error, dec_ar_error;
    (* keep *) logic dec_aw_valid, dec_ar_valid;
    logic [IdxWidth-1:0] dec_aw, dec_ar;

    addr_decode #(
      .NoIndices  ( Cfg.NoMstPorts     ),
      .addr_t     ( addr_t             ),
      .NoRules    ( Cfg.NoAddrRules    ),
      .rule_t     ( rule_t             )
    ) i_axi_aw_decode (
      .addr_i           ( aw_addr_i[i]            ),
      .addr_map_i       ( addr_map_i              ),
      .idx_o            ( dec_aw                  ),
      .dec_valid_o      ( dec_aw_valid            ),
      .dec_error_o      ( dec_aw_error            ),
      .en_default_idx_i ( en_default_idx_i[i]     ),
      .default_idx_i    ( default_idx_i[i]        )
    );

    addr_decode #(
      .NoIndices  ( Cfg.NoMstPorts  ),
      .addr_t     ( addr_t          ),
      .NoRules    ( Cfg.NoAddrRules ),
      .rule_t     ( rule_t          )
    ) i_axi_ar_decode (
      .addr_i           ( ar_addr_i[i]            ),
      .addr_map_i       ( addr_map_i              ),
      .idx_o            ( dec_ar                  ),
      .dec_valid_o      ( dec_ar_valid            ),
      .dec_error_o      ( dec_ar_error            ),
      .en_default_idx_i ( en_default_idx_i[i]     ),
      .default_idx_i    ( default_idx_i[i]        )
    );

    assign slv_aw_select[i] = dec_aw_error ?
        mst_port_idx_t'(Cfg.NoMstPorts) : mst_port_idx_t'(dec_aw);
    assign slv_ar_select[i] = dec_ar_error ?
        mst_port_idx_t'(Cfg.NoMstPorts) : mst_port_idx_t'(dec_ar);

  end
endmodule

`ifndef VCS
`ifndef TARGET_GENUS
// As of now, VCS and Genus does not support multi-dimensional array of interfaces.
`include "axi/assign.svh"
`include "axi/typedef.svh"

module axi_xbar_unmuxed_intf
import cf_math_pkg::idx_width;
#(
  parameter int unsigned AXI_USER_WIDTH =  0,
  parameter axi_pkg::xbar_cfg_t Cfg     = '0,
  parameter bit ATOPS                   = 1'b1,
  parameter bit [Cfg.NoSlvPorts-1:0][Cfg.NoMstPorts-1:0] CONNECTIVITY = '1,
  parameter type rule_t                 = axi_pkg::xbar_rule_64_t
) (
  input  logic                                                      clk_i,
  input  logic                                                      rst_ni,
  input  logic                                                      test_i,
  AXI_BUS.Slave                                                     slv_ports [Cfg.NoSlvPorts-1:0],
  AXI_BUS.Master                                                    mst_ports [Cfg.NoMstPorts-1:0][Cfg.NoSlvPorts-1:0],
  input  rule_t [Cfg.NoAddrRules-1:0]                               addr_map_i,
  input  logic  [Cfg.NoSlvPorts-1:0]                                en_default_mst_port_i,
  input  logic  [Cfg.NoSlvPorts-1:0][idx_width(Cfg.NoMstPorts)-1:0] default_mst_port_i
);

  typedef logic [Cfg.AxiIdWidthSlvPorts -1:0] id_t;
  typedef logic [Cfg.AxiAddrWidth       -1:0] addr_t;
  typedef logic [Cfg.AxiDataWidth       -1:0] data_t;
  typedef logic [Cfg.AxiDataWidth/8     -1:0] strb_t;
  typedef logic [AXI_USER_WIDTH         -1:0] user_t;

  `AXI_TYPEDEF_AW_CHAN_T(aw_chan_t, addr_t, id_t, user_t)
  `AXI_TYPEDEF_W_CHAN_T(w_chan_t, data_t, strb_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T(b_chan_t, id_t, user_t)
  `AXI_TYPEDEF_AR_CHAN_T(ar_chan_t, addr_t, id_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(r_chan_t, data_t, id_t, user_t)
  `AXI_TYPEDEF_REQ_T(req_t, aw_chan_t, w_chan_t, ar_chan_t)
  `AXI_TYPEDEF_RESP_T(resp_t, b_chan_t, r_chan_t)

  req_t   [Cfg.NoMstPorts-1:0][Cfg.NoSlvPorts-1:0] mst_reqs;
  resp_t  [Cfg.NoMstPorts-1:0][Cfg.NoSlvPorts-1:0] mst_resps;
  req_t   [Cfg.NoSlvPorts-1:0]                     slv_reqs;
  resp_t  [Cfg.NoSlvPorts-1:0]                     slv_resps;

  for (genvar i = 0; i < Cfg.NoMstPorts; i++) begin : gen_assign_mst
    for (genvar j = 0; j < Cfg.NoSlvPorts; j++) begin : gen_assign_mst_inner
      `AXI_ASSIGN_FROM_REQ(mst_ports[i][j], mst_reqs[i][j])
      `AXI_ASSIGN_TO_RESP(mst_resps[i][j], mst_ports[i][j])
    end
  end

  for (genvar i = 0; i < Cfg.NoSlvPorts; i++) begin : gen_assign_slv
    `AXI_ASSIGN_TO_REQ(slv_reqs[i], slv_ports[i])
    `AXI_ASSIGN_FROM_RESP(slv_ports[i], slv_resps[i])
  end

  axi_xbar_unmuxed #(
    .Cfg          ( Cfg          ),
    .ATOPs        ( ATOPS        ),
    .Connectivity ( CONNECTIVITY ),
    .aw_chan_t    ( aw_chan_t    ),
    .w_chan_t     ( w_chan_t     ),
    .b_chan_t     ( b_chan_t     ),
    .ar_chan_t    ( ar_chan_t    ),
    .r_chan_t     ( r_chan_t     ),
    .req_t        ( req_t        ),
    .resp_t       ( resp_t       ),
    .rule_t       ( rule_t       )
  ) i_xbar (
    .clk_i,
    .rst_ni,
    .test_i,
    .slv_ports_req_i  (slv_reqs ),
    .slv_ports_resp_o (slv_resps),
    .mst_ports_req_o  (mst_reqs ),
    .mst_ports_resp_i (mst_resps),
    .addr_map_i,
    .en_default_mst_port_i,
    .default_mst_port_i
  );

endmodule

`endif
`endif
