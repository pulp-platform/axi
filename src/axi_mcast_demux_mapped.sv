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
// - Michael Rogenmoser <michaero@iis.ee.ethz.ch>
// - Wolfgang Roenninger <wroennin@iis.ee.ethz.ch>
// - Thomas Benz <tbenz@iis.ee.ethz.ch>
// - Andreas Kurth <akurth@iis.ee.ethz.ch>
// - Luca Colagrande <colluca@iis.ee.ethz.ch>

`include "common_cells/assertions.svh"
`include "common_cells/registers.svh"

`ifdef QUESTA
// Derive `TARGET_VSIM`, which is used for tool-specific workarounds in this file, from `QUESTA`,
// which is automatically set in Questa.
`define TARGET_VSIM
`endif

/// Demultiplex one AXI4+ATOP slave port to multiple AXI4+ATOP master ports.
///
/// The module internally decodes Ax requests, determining the master port route based on the
/// address of the request. To this end an address map, and additional inputs required by the
/// address decoding modules, are provided.
///
/// ## Design overview
///
/// ![Block diagram](module.axi_demux.png "Block diagram")
///
/// Beats on the W channel are routed by demultiplexer according to the selection for the
/// corresponding AW beat.  This relies on the AXI property that W bursts must be sent in the same
/// order as AW beats and beats from different W bursts may not be interleaved.
///
/// Beats on the B and R channel are multiplexed from the master ports to the slave port with
/// a round-robin arbitration tree.
module axi_mcast_demux_mapped #(
  parameter int unsigned         AxiIdWidth            = 32'd0,
  parameter int unsigned         AxiAddrWidth          = 32'd0,
  parameter bit                  AtopSupport           = 1'b1,
  parameter type                 aw_chan_t             = logic,
  parameter type                 w_chan_t              = logic,
  parameter type                 b_chan_t              = logic,
  parameter type                 ar_chan_t             = logic,
  parameter type                 r_chan_t              = logic,
  parameter type                 axi_req_t             = logic,
  parameter type                 axi_resp_t            = logic,
  parameter int unsigned         NoMstPorts            = 32'd0,
  parameter int unsigned         MaxTrans              = 32'd8,
  parameter int unsigned         AxiLookBits           = 32'd3,
  parameter bit                  UniqueIds             = 1'b0,
  parameter bit                  SpillAw               = 1'b1,
  parameter bit                  SpillW                = 1'b0,
  parameter bit                  SpillB                = 1'b0,
  parameter bit                  SpillAr               = 1'b1,
  parameter bit                  SpillR                = 1'b0,
  parameter bit [NoMstPorts-1:0] Connectivity          = '1,
  parameter bit [NoMstPorts-1:0] MulticastConnectivity = '1,
  parameter type                 rule_t                = logic,
  parameter int unsigned         NoAddrRules           = 32'd0,
  parameter int unsigned         NoMulticastRules      = 32'd0,
  parameter int unsigned         NoMulticastPorts      = 32'd0,
  parameter int unsigned         MaxMcastTrans         = 32'd7
) (
  input  logic                       clk_i,
  input  logic                       rst_ni,
  input  logic                       test_i,
  // Addressing rules
  input  rule_t    [NoAddrRules-1:0] addr_map_i,
  input  logic                       en_default_mst_port_i,
  input  rule_t                      default_mst_port_i,
  // Slave Port
  input  axi_req_t                   slv_req_i,
  output axi_resp_t                  slv_resp_o,
  // Master Ports
  output axi_req_t  [NoMstPorts-1:0] mst_reqs_o,
  input  axi_resp_t [NoMstPorts-1:0] mst_resps_i,
  output logic      [NoMstPorts-1:0] mst_is_mcast_o,
  output logic      [NoMstPorts-1:0] mst_aw_commit_o
);

  // Account for additional error slave
  localparam int unsigned NoMstPortsExt = NoMstPorts + 1;

  localparam int unsigned IdxSelectWidth = cf_math_pkg::idx_width(NoMstPorts);
  localparam int unsigned IdxSelectWidthExt = cf_math_pkg::idx_width(NoMstPortsExt);
  typedef logic [IdxSelectWidth-1:0] idx_select_t;
  typedef logic [IdxSelectWidthExt-1:0] idx_select_ext_t;

  typedef logic [NoMstPortsExt-1:0] mask_select_t;

  typedef logic [AxiAddrWidth-1:0] addr_t;

  typedef struct packed {
    int unsigned idx;
    addr_t addr;
    addr_t mask;
  } mask_rule_t;

  // ----------------
  // Spill registers
  // ----------------

  axi_req_t slv_req_cut;
  axi_resp_t slv_resp_cut;

  spill_register #(
    .T       ( aw_chan_t  ),
    .Bypass  ( ~SpillAw   )
  ) i_aw_spill_reg (
    .clk_i,
    .rst_ni,
    .valid_i ( slv_req_i.aw_valid    ),
    .ready_o ( slv_resp_o.aw_ready   ),
    .data_i  ( slv_req_i.aw          ),
    .valid_o ( slv_req_cut.aw_valid  ),
    .ready_i ( slv_resp_cut.aw_ready ),
    .data_o  ( slv_req_cut.aw        )
  );
  spill_register #(
    .T       ( w_chan_t  ),
    .Bypass  ( ~SpillW   )
  ) i_w_spill_reg (
    .clk_i,
    .rst_ni,
    .valid_i ( slv_req_i.w_valid    ),
    .ready_o ( slv_resp_o.w_ready   ),
    .data_i  ( slv_req_i.w          ),
    .valid_o ( slv_req_cut.w_valid  ),
    .ready_i ( slv_resp_cut.w_ready ),
    .data_o  ( slv_req_cut.w        )
  );
  spill_register #(
    .T       ( ar_chan_t  ),
    .Bypass  ( ~SpillAr   )
  ) i_ar_spill_reg (
    .clk_i,
    .rst_ni,
    .valid_i ( slv_req_i.ar_valid    ),
    .ready_o ( slv_resp_o.ar_ready   ),
    .data_i  ( slv_req_i.ar          ),
    .valid_o ( slv_req_cut.ar_valid  ),
    .ready_i ( slv_resp_cut.ar_ready ),
    .data_o  ( slv_req_cut.ar        )
  );
  spill_register #(
    .T       ( b_chan_t ),
    .Bypass  ( ~SpillB  )
  ) i_b_spill_reg (
    .clk_i,
    .rst_ni,
    .valid_i ( slv_resp_cut.b_valid ),
    .ready_o ( slv_req_cut.b_ready  ),
    .data_i  ( slv_resp_cut.b       ),
    .valid_o ( slv_resp_o.b_valid   ),
    .ready_i ( slv_req_i.b_ready    ),
    .data_o  ( slv_resp_o.b         )
  );
  spill_register #(
    .T       ( r_chan_t ),
    .Bypass  ( ~SpillR  )
  ) i_r_spill_reg (
    .clk_i,
    .rst_ni,
    .valid_i ( slv_resp_cut.r_valid ),
    .ready_o ( slv_req_cut.r_ready  ),
    .data_i  ( slv_resp_cut.r       ),
    .valid_o ( slv_resp_o.r_valid   ),
    .ready_i ( slv_req_i.r_ready    ),
    .data_o  ( slv_resp_o.r         )
  );

  // -----------------
  // AR address decoding
  // -----------------

  idx_select_t     dec_ar_select_idx;
  logic            dec_ar_error;
  idx_select_ext_t ar_select_idx;

  // Address decoding for unicast requests
  addr_decode #(
    .NoIndices          (NoMstPorts),
    .NoRules            (NoAddrRules),
    .addr_t             (addr_t),
    .rule_t             (rule_t)
  ) i_axi_ar_decode (
    .addr_i             (slv_req_cut.ar.addr),
    .addr_map_i         (addr_map_i),
    .idx_o              (dec_ar_select_idx),
    .dec_valid_o        (),
    .dec_error_o        (dec_ar_error),
    .en_default_idx_i   (en_default_mst_port_i),
    .default_idx_i      (idx_select_t'(default_mst_port_i.idx))
  );

  assign ar_select_idx = dec_ar_error ? NoMstPorts : idx_select_ext_t'(dec_ar_select_idx);

  // -----------------
  // AW address decoding
  // -----------------

  // AW decoder inputs
  mask_rule_t [axi_pkg::iomsb(NoMulticastRules):0] multicast_rules;
  mask_rule_t                                      default_rule;

  // AW unicast decoder outputs
  idx_select_t                       dec_aw_unicast_select_idx;
  logic [NoMstPorts-1:0]             dec_aw_unicast_select_mask;
  logic                              dec_aw_unicast_valid;
  logic                              dec_aw_unicast_error;

  // AW multicast decoder outputs
  logic  [NoMulticastPorts-1:0]      dec_aw_multicast_select_mask;
  addr_t [NoMulticastPorts-1:0]      dec_aw_multicast_addr;
  addr_t [NoMulticastPorts-1:0]      dec_aw_multicast_mask;
  logic                              dec_aw_multicast_valid;
  logic                              dec_aw_multicast_error;

  // Decoding outputs (merged from unicast and multicast paths)
  mask_select_t              dec_aw_select_mask;
  addr_t [NoMstPortsExt-1:0] dec_aw_addr;
  addr_t [NoMstPortsExt-1:0] dec_aw_mask;

  // Address decoding for unicast requests
  addr_decode #(
    .NoIndices          (NoMstPorts),
    .NoRules            (NoAddrRules),
    .addr_t             (addr_t),
    .rule_t             (rule_t)
  ) i_axi_aw_unicast_decode (
    .addr_i             (slv_req_cut.aw.addr),
    .addr_map_i         (addr_map_i),
    .idx_o              (dec_aw_unicast_select_idx),
    .dec_valid_o        (dec_aw_unicast_valid),
    .dec_error_o        (dec_aw_unicast_error),
    .en_default_idx_i   (en_default_mst_port_i),
    .default_idx_i      (idx_select_t'(default_mst_port_i.idx))
  );

  // Generate the output mask from the index
  assign dec_aw_unicast_select_mask = 1'b1 << dec_aw_unicast_select_idx;

  // If the address decoding doesn't produce any match, the request
  // is routed to the error slave, which lies at the highest index.
  mask_select_t select_error_slave;
  assign select_error_slave = 1'b1 << NoMstPorts;

  // Disable multicast only if NoMulticastPorts == 0. In some instances you may want to
  // match the multicast decoder's default port, even if NoMulticastRules == 0.
  if (NoMulticastPorts > 0) begin : gen_multicast

    // Convert multicast rules to mask (NAPOT) form, see https://arxiv.org/pdf/2502.19215
    for (genvar i = 0; i < NoMulticastRules; i++) begin : gen_multicast_rules
      assign multicast_rules[i].idx = addr_map_i[i].idx;
      assign multicast_rules[i].mask = addr_map_i[i].end_addr - addr_map_i[i].start_addr - 1;
      assign multicast_rules[i].addr = addr_map_i[i].start_addr;
    end
    assign default_rule.idx = default_mst_port_i.idx;
    assign default_rule.mask = default_mst_port_i.end_addr - default_mst_port_i.start_addr - 1;
    assign default_rule.addr = default_mst_port_i.start_addr;

    if (NoMulticastRules > 0) begin : gen_multiaddr_decode
      // Address decoding for multicast requests.
      multiaddr_decode #(
        .NoIndices        (NoMulticastPorts),
        .NoRules          (NoMulticastRules),
        .addr_t           (addr_t),
        .rule_t           (mask_rule_t)
      ) i_axi_aw_multicast_decode (
        .addr_map_i       (multicast_rules),
        .addr_i           (slv_req_cut.aw.addr),
        .mask_i           (slv_req_cut.aw.user.collective_mask),
        .select_o         (dec_aw_multicast_select_mask),
        .addr_o           (dec_aw_multicast_addr),
        .mask_o           (dec_aw_multicast_mask),
        .dec_valid_o      (dec_aw_multicast_valid),
        .dec_error_o      (dec_aw_multicast_error),
        .en_default_idx_i (en_default_mst_port_i),
        .default_idx_i    (default_rule)
      );
    end else begin : gen_no_multiaddr_decode
      assign dec_aw_multicast_select_mask = 1'b1 << default_rule.idx;
      assign dec_aw_multicast_addr = slv_req_cut.aw.addr;
      assign dec_aw_multicast_mask = slv_req_cut.aw.user.collective_mask;
      assign dec_aw_multicast_valid = 1'b1;
      assign dec_aw_multicast_error = 1'b0;
    end

    // Mux the multicast and unicast decoding outputs.
    always_comb begin
      dec_aw_select_mask = '0;
      dec_aw_addr = '0;
      dec_aw_mask = '0;

      if (slv_req_cut.aw.user.collective_mask == '0) begin
        dec_aw_addr = {'0, {NoMstPorts{slv_req_cut.aw.addr}}};
        if (dec_aw_unicast_error) begin
          dec_aw_select_mask = select_error_slave;
        end else begin
          dec_aw_select_mask = dec_aw_unicast_select_mask & Connectivity;
        end
      end else begin
        dec_aw_addr = {'0, {(NoMstPorts-NoMulticastPorts){slv_req_cut.aw.addr}}, dec_aw_multicast_addr};
        dec_aw_mask = {'0, dec_aw_multicast_mask};
        if (dec_aw_multicast_error) begin
          dec_aw_select_mask = select_error_slave;
        end else begin
          dec_aw_select_mask = {'0, dec_aw_multicast_select_mask} & MulticastConnectivity;
        end
      end
    end

  end else begin : gen_no_multicast
    assign dec_aw_addr = {'0, {NoMstPorts{slv_req_cut.aw.addr}}};
    assign dec_aw_mask = '0;
    assign dec_aw_select_mask = (dec_aw_unicast_error) ? select_error_slave :
                                (dec_aw_unicast_select_mask & Connectivity);
  end

  // -----------------
  // Demux
  // -----------------

  axi_req_t  errslv_req;
  axi_resp_t errslv_resp;
  logic      errslv_is_mcast;
  logic      errslv_aw_commit;

  axi_mcast_demux_simple #(
    .AxiIdWidth       ( AxiIdWidth       ),
    .AtopSupport      ( AtopSupport      ),
    .axi_req_t        ( axi_req_t        ),
    .axi_resp_t       ( axi_resp_t       ),
    .NoMstPorts       ( NoMstPortsExt    ),
    .MaxTrans         ( MaxTrans         ),
    .AxiLookBits      ( AxiLookBits      ),
    .UniqueIds        ( UniqueIds        ),
    .aw_addr_t        ( addr_t           ),
    .NoMulticastPorts ( NoMulticastPorts ),
    .MaxMcastTrans    ( MaxMcastTrans    )
  ) i_mcast_demux_simple (
    .clk_i,
    .rst_ni,
    .test_i,
    .slv_req_i       ( slv_req_cut                         ),
    .slv_aw_select_i ( dec_aw_select_mask                  ),
    .slv_aw_addr_i   ( dec_aw_addr                         ),
    .slv_aw_mask_i   ( dec_aw_mask                         ),
    .slv_ar_select_i ( ar_select_idx                       ),
    .slv_resp_o      ( slv_resp_cut                        ),
    .mst_reqs_o      ( {errslv_req,       mst_reqs_o}      ),
    .mst_resps_i     ( {errslv_resp,      mst_resps_i}     ),
    .mst_is_mcast_o  ( {errslv_is_mcast,  mst_is_mcast_o}  ),
    .mst_aw_commit_o ( {errslv_aw_commit, mst_aw_commit_o} )
  );

  axi_err_slv #(
    .AxiIdWidth  ( AxiIdWidth           ),
    .axi_req_t   ( axi_req_t            ),
    .axi_resp_t  ( axi_resp_t           ),
    .Resp        ( axi_pkg::RESP_DECERR ),
    .ATOPs       ( AtopSupport          ),
    // Transactions terminate at this slave, so minimize resource consumption by accepting
    // only a few transactions at a time.
    .MaxTrans    ( 4                    )
  ) i_axi_err_slv (
    .clk_i,
    .rst_ni,
    .test_i,
    .slv_req_i  ( errslv_req  ),
    .slv_resp_o ( errslv_resp )
  );

  // -----------------
  // Assertions
  // -----------------

// pragma translate_off
`ifndef VERILATOR
`ifndef XSIM

  // Check that multicast address map rules expressed in interval form can be converted to
  // mask form, see https://arxiv.org/pdf/2502.19215
  for (genvar i = 0; i < NoMulticastRules; i++) begin : gen_multicast_rule_assertion
    addr_t size;
    assign size = addr_map_i[i].end_addr - addr_map_i[i].start_addr;
    `ASSERT(MulticastRuleSize,
      ((size & (size - 1)) == 0), clk_i, !rst_ni,
      $sformatf("Size %0d of rule %0d is not a power of 2", size, i))
    `ASSERT(MulticastRuleAlignment,
      (addr_map_i[i].start_addr % size) == 0, clk_i, !rst_ni,
      $sformatf("Rule %0d, starting at 0x%0x, is not aligned to its size (%0d)",
      i, addr_map_i[i].start_addr, size))
  end
  // Default rule is only converted to mask form if there are any other multicast rules
  if (NoMulticastPorts > 0) begin : gen_multicast_default_rule_assertion
    addr_t size;
    assign size = default_mst_port_i.end_addr - default_mst_port_i.start_addr;
    `ASSERT(DefaultRuleSize,
      !en_default_mst_port_i || ((size & (size - 1)) == 0), clk_i, !rst_ni,
      $sformatf("Size %0d of default rule is not a power of 2", size))
    `ASSERT(DefaultRuleAlignment,
      !en_default_mst_port_i || ((default_mst_port_i.start_addr % size) == 0), clk_i, !rst_ni,
      $sformatf("Default rule, starting at 0x%0x, is not aligned to its size (%0d)",
        default_mst_port_i.start_addr, size))
  end

  // Check that addrmap and default slave do not change while there is an unserved Ax
  `ASSERT(default_mst_port_en_aw_stable,
    (slv_req_cut.aw_valid && !slv_resp_cut.aw_ready) |=> $stable(en_default_mst_port_i),
    clk_i, !rst_ni,
    "It is not allowed to change the default mst port enable when there is an unserved Aw beat.")
  `ASSERT(default_mst_port_aw_stable,
    (slv_req_cut.aw_valid && !slv_resp_cut.aw_ready) |=> $stable(default_mst_port_i),
    clk_i, !rst_ni,
    "It is not allowed to change the default mst port when there is an unserved Aw beat.")
  `ASSERT(addrmap_aw_stable,
    (slv_req_cut.aw_valid && !slv_resp_cut.aw_ready) |=> $stable(addr_map_i),
    clk_i, !rst_ni,
    "It is not allowed to change the address map when there is an unserved Aw beat.")
  `ASSERT(default_mst_port_en_ar_stable,
    (slv_req_cut.ar_valid && !slv_resp_cut.ar_ready) |=> $stable(en_default_mst_port_i),
    clk_i, !rst_ni,
    "It is not allowed to change the default mst port enable when there is an unserved Ar beat.")
  `ASSERT(default_mst_port_ar_stable,
    (slv_req_cut.ar_valid && !slv_resp_cut.ar_ready) |=> $stable(default_mst_port_i),
    clk_i, !rst_ni,
    "It is not allowed to change the default mst port when there is an unserved Ar beat.")
  `ASSERT(addrmap_ar_stable,
    (slv_req_cut.ar_valid && !slv_resp_cut.ar_ready) |=> $stable(addr_map_i),
    clk_i, !rst_ni,
    "It is not allowed to change the address map when there is an unserved Ar beat.")

`endif
`endif
// pragma translate_on

endmodule

// interface wrapper
`include "axi/assign.svh"
`include "axi/typedef.svh"
module axi_mcast_demux_intf #(
  parameter int unsigned AXI_ID_WIDTH     = 32'd0, // Synopsys DC requires default value for params
  parameter bit          ATOP_SUPPORT     = 1'b1,
  parameter int unsigned AXI_ADDR_WIDTH   = 32'd0,
  parameter int unsigned AXI_DATA_WIDTH   = 32'd0,
  parameter int unsigned AXI_USER_WIDTH   = 32'd0,
  parameter int unsigned NO_MST_PORTS     = 32'd3,
  parameter int unsigned MAX_TRANS        = 32'd8,
  parameter int unsigned AXI_LOOK_BITS    = 32'd3,
  parameter bit          UNIQUE_IDS       = 1'b0,
  parameter bit          SPILL_AW         = 1'b1,
  parameter bit          SPILL_W          = 1'b0,
  parameter bit          SPILL_B          = 1'b0,
  parameter bit          SPILL_AR         = 1'b1,
  parameter bit          SPILL_R          = 1'b0,
  parameter type         rule_t           = logic,
  // Dependent parameters, DO NOT OVERRIDE!
  parameter int unsigned SELECT_WIDTH   = (NO_MST_PORTS > 32'd1) ? $clog2(NO_MST_PORTS) : 32'd1,
  parameter type         idx_select_t   = logic [SELECT_WIDTH-1:0] // MST port select type
) (
  input  logic                     clk_i,                  // Clock
  input  logic                     rst_ni,                 // Asynchronous reset active low
  input  logic                     test_i,                 // Testmode enable
  input  rule_t [NO_MST_PORTS-2:0] addr_map_i,
  input  idx_select_t              slv_ar_select_i,        // has to be stable, when ar_valid
  input  logic                     en_default_mst_port_i,
  input  rule_t                    default_mst_port_i,
  AXI_BUS.Slave                    slv,                    // slave port
  AXI_BUS.Master                   mst [NO_MST_PORTS-1:0], // master ports
  output logic [NO_MST_PORTS-1:0]  mst_is_mcast_o,
  output logic [NO_MST_PORTS-1:0]  mst_aw_commit_o
);

  typedef logic [AXI_ID_WIDTH-1:0]       id_t;
  typedef logic [AXI_ADDR_WIDTH-1:0]   addr_t;
  typedef logic [AXI_DATA_WIDTH-1:0]   data_t;
  typedef logic [AXI_DATA_WIDTH/8-1:0] strb_t;
  typedef logic [AXI_USER_WIDTH-1:0]   user_t;
  `AXI_TYPEDEF_AW_CHAN_T(aw_chan_t, addr_t, id_t, user_t)
  `AXI_TYPEDEF_W_CHAN_T(w_chan_t, data_t, strb_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T(b_chan_t, id_t, user_t)
  `AXI_TYPEDEF_AR_CHAN_T(ar_chan_t, addr_t, id_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(r_chan_t, data_t, id_t, user_t)
  `AXI_TYPEDEF_REQ_T(axi_req_t, aw_chan_t, w_chan_t, ar_chan_t)
  `AXI_TYPEDEF_RESP_T(axi_resp_t, b_chan_t, r_chan_t)

  axi_req_t                     slv_req;
  axi_resp_t                    slv_resp;
  axi_req_t  [NO_MST_PORTS-1:0] mst_req;
  axi_resp_t [NO_MST_PORTS-1:0] mst_resp;

  `AXI_ASSIGN_TO_REQ(slv_req, slv)
  `AXI_ASSIGN_FROM_RESP(slv, slv_resp)

  for (genvar i = 0; i < NO_MST_PORTS; i++) begin : gen_assign_mst_ports
    `AXI_ASSIGN_FROM_REQ(mst[i], mst_req[i])
    `AXI_ASSIGN_TO_RESP(mst_resp[i], mst[i])
  end

  axi_mcast_demux #(
    .AxiIdWidth     ( AXI_ID_WIDTH  ), // ID Width
    .AtopSupport    ( ATOP_SUPPORT  ),
    .aw_addr_t      (     addr_t    ), // AW Address Type
    .aw_chan_t      (  aw_chan_t    ), // AW Channel Type
    .w_chan_t       (   w_chan_t    ), //  W Channel Type
    .b_chan_t       (   b_chan_t    ), //  B Channel Type
    .ar_chan_t      (  ar_chan_t    ), // AR Channel Type
    .r_chan_t       (   r_chan_t    ), //  R Channel Type
    .axi_req_t      (  axi_req_t    ),
    .axi_resp_t     ( axi_resp_t    ),
    .NoMstPorts     ( NO_MST_PORTS  ),
    .MaxTrans       ( MAX_TRANS     ),
    .AxiLookBits    ( AXI_LOOK_BITS ),
    .UniqueIds      ( UNIQUE_IDS    ),
    .SpillAw        ( SPILL_AW      ),
    .SpillW         ( SPILL_W       ),
    .SpillB         ( SPILL_B       ),
    .SpillAr        ( SPILL_AR      ),
    .SpillR         ( SPILL_R       ),
    .rule_t         ( rule_t        )
  ) i_axi_demux (
    .clk_i,   // Clock
    .rst_ni,  // Asynchronous reset active low
    .test_i,  // Testmode enable
    .addr_map_i            ( addr_map_i            ),
    .en_default_mst_port_i ( en_default_mst_port_i ),
    .default_mst_port_i    ( default_mst_port_i    ),
    // slave port
    .slv_req_i             ( slv_req               ),
    .slv_ar_select_i       ( slv_ar_select_i       ),
    .slv_resp_o            ( slv_resp              ),
    // master port
    .mst_reqs_o            ( mst_req               ),
    .mst_resps_i           ( mst_resp              ),
    .mst_is_mcast_o        ( mst_is_mcast_o        ),
    .mst_aw_commit_o       ( mst_aw_commit_o       )
  );
endmodule
