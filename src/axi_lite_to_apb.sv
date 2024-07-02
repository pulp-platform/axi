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
// - Andreas Kurth <akurth@iis.ee.ethz.ch>
// - Samuel Riedel <sriedel@iis.ee.ethz.ch>

// Description: AXI4-Lite to APB4 bridge
//
// This module has one AXI4-Lite slave port and is capable of generating
// APB4 requests for multiple APB4 slave modules. The address and data widths
// of AXI4-Lite and APB4 have to be the same for both ports and are enforced over assertions.
// The selection of the APB4 slave is handled by the `addr_decode` module from `common_cells`.
// This module will answer with a `axi_pkg::RESP_DECERR` when a AXI4-Lite AW or AR request
// is not in the address map of the module and `no` APB4 request is made.
//
// The type of the APB4 request is required to look like:
//   typedef struct packed {
//     addr_t paddr;   // same as AXI4-Lite
//     prot_t pprot;   // same as AXI4-Lite, specification is the same
//     logic  psel;    // each APB4 slave has its own single-bit psel
//     logic  penable; // enable signal shows second APB4 cycle
//     logic  pwrite;  // write enable
//     data_t pwdata;  // write data, comes from W channel
//     strb_t pstrb;   // write strb, comes from W channel
//   } apb_req_t;
// For every APB4 slave, the `psel` field is only asserted when the decoded address matches that
// slave.  If `psel` is deasserted, the value of the other fields may be undefined.
//
// The type of the APB4 response is required to look like:
//  typedef struct packed {
//    logic  pready;   // slave signals that it is ready
//    data_t prdata;   // read data, connects to R channel
//    logic  pslverr;  // gets translated into either `axi_pkg::RESP_OK` or `axi_pkg::RESP_SLVERR`
//  } apb_resp_t;
// Each connected `apb_resp`, has to be connected to the corresponding port index. The module
// routes the response depending on the `apb_req.psel` bit and `apb_req.pwrite` either to the
// AXI4Lite B channel for writes and to the R channel for reads.

`include "common_cells/registers.svh"

/* verilator lint_off PINCONNECTEMPTY */
/* verilator lint_off DECLFILENAME */

module axi_lite_to_apb #(
  parameter int unsigned NoApbSlaves      = 32'd1,   // Number of connected APB slaves
  parameter int unsigned NoRules          = 32'd1,   // Number of APB address rules
  parameter int unsigned AddrWidth        = 32'd32,  // Address width
  parameter int unsigned DataWidth        = 32'd32,  // Data width
  parameter bit          PipelineRequest  = 1'b0,    // Pipeline request path
  parameter bit          PipelineResponse = 1'b0,    // Pipeline response path
  parameter type         axi_lite_req_t   = logic,   // AXI4-Lite request struct
  parameter type         axi_lite_resp_t  = logic,   // AXI4-Lite response sruct
  parameter type         apb_req_t        = logic,   // APB4 request struct
  parameter type         apb_resp_t       = logic,   // APB4 response struct
  parameter type         rule_t           = logic    // Address Decoder rule from `common_cells`
) (
  input  logic                             clk_i,            // Clock
  input  logic                             rst_ni,           // Asynchronous reset active low
  // AXI LITE slave port
  input  axi_lite_req_t                    axi_lite_req_i,
  output axi_lite_resp_t                   axi_lite_resp_o,
  // APB master port
  output apb_req_t       [NoApbSlaves-1:0] apb_req_o,
  input  apb_resp_t      [NoApbSlaves-1:0] apb_resp_i,
  // APB Slave Address Map
  input  rule_t          [    NoRules-1:0] addr_map_i
);
  localparam logic RD = 1'b0;  // Encode index of a read request
  localparam logic WR = 1'b1;  // Encode index of a write request
  localparam int unsigned SelIdxWidth = (NoApbSlaves > 32'd1) ? $clog2(NoApbSlaves) : 32'd1;
  typedef logic [AddrWidth-1:0] addr_t;  // AXI4-Lite, APB4 and rule_t addr width
  typedef logic [DataWidth-1:0] data_t;  // AXI4-Lite and APB4 data width
  typedef logic [DataWidth/8-1:0] strb_t;  // AXI4-Lite and APB4 strb width
  typedef logic [SelIdxWidth-1:0] sel_idx_t;  // Selection index from addr_decode

  typedef struct packed {
    addr_t          addr;
    axi_pkg::prot_t prot;   // prot has the exact same bit mapping in AXI4-Lite as In APB v2.0
    data_t          data;
    strb_t          strb;
    logic           write;
  } int_req_t;  // request type generated by the read and write channel, internal
  typedef struct packed {
    data_t          data;  // read data from APB
    axi_pkg::resp_t resp;  // response bit from APB
  } int_resp_t;  // internal
  typedef enum logic {
    Setup  = 1'b0,  // APB in Idle or Setup
    Access = 1'b1   // APB in Access
  } apb_state_e;


  // Signals from AXI4-Lite slave to arbitration tree
  int_req_t [1:0] axi_req;
  logic [1:0] axi_req_valid, axi_req_ready;

  // Signals from response spill registers
  axi_pkg::resp_t axi_bresp;
  logic axi_bresp_valid, axi_bresp_ready;
  int_resp_t axi_rresp;
  logic axi_rresp_valid, axi_rresp_ready;

  // -----------------------------------------------------------------------------------------------
  // AXI4-Lite slave
  // -----------------------------------------------------------------------------------------------
  // read request
  assign axi_req[RD] = '{
      addr: axi_lite_req_i.ar.addr,
      prot: axi_lite_req_i.ar.prot,
      data: '0,
      strb: '0,
      write: RD
    };
  assign axi_req_valid[RD] = axi_lite_req_i.ar_valid;
  // write request
  assign axi_req[WR] = '{
      addr: axi_lite_req_i.aw.addr,
      prot: axi_lite_req_i.aw.prot,
      data: axi_lite_req_i.w.data,
      strb: axi_lite_req_i.w.strb,
      write: WR
    };
  assign axi_req_valid[WR] = axi_lite_req_i.aw_valid & axi_lite_req_i.w_valid;
  assign axi_lite_resp_o = '{
      aw_ready: axi_req_valid[WR] & axi_req_ready[WR],  // if AXI AW & W valid & tree gnt_o[WR]
      w_ready: axi_req_valid[WR] & axi_req_ready[WR],  // if AXI AW & W valid & tree gnt_o[WR]
      b: '{resp: axi_bresp},  // from spill reg
      b_valid: axi_bresp_valid,  // from spill reg
      ar_ready: axi_req_valid[RD] & axi_req_ready[RD],  // if AXI AR valid and tree gnt[RD]
      r: '{data: axi_rresp.data, resp: axi_rresp.resp},  // from spill reg
      r_valid: axi_rresp_valid  // from spill reg
    };
  // -----------------------------------------------------------------------------------------------
  // Arbitration between write and read plus spill register for request and response
  // -----------------------------------------------------------------------------------------------
  int_req_t arb_req, apb_req;
  logic arb_req_valid, arb_req_ready, apb_req_valid, apb_req_ready;
  axi_pkg::resp_t apb_wresp;
  logic apb_wresp_valid, apb_wresp_ready;
  int_resp_t apb_rresp;
  logic apb_rresp_valid, apb_rresp_ready;

  rr_arb_tree #(
    .NumIn    (32'd2),
    .DataType (int_req_t),
    .ExtPrio  (1'b0),
    .AxiVldRdy(1'b1),
    .LockIn   (1'b1)
  ) i_req_arb (
    .clk_i,
    .rst_ni,
    .flush_i('0),
    .rr_i   ('0),
    .req_i  (axi_req_valid),
    .gnt_o  (axi_req_ready),
    .data_i (axi_req),
    .gnt_i  (arb_req_ready),
    .req_o  (arb_req_valid),
    .data_o (arb_req),
    .idx_o  (  /*not used*/)
  );

  if (PipelineRequest) begin : gen_req_spill
    spill_register #(
      .T     (int_req_t),
      .Bypass(1'b0)
    ) i_req_spill (
      .clk_i,
      .rst_ni,
      .valid_i(arb_req_valid),
      .ready_o(arb_req_ready),
      .data_i (arb_req),
      .valid_o(apb_req_valid),
      .ready_i(apb_req_ready),
      .data_o (apb_req)
    );
  end else begin : gen_req_ft_reg
    fall_through_register #(
      .T(int_req_t)
    ) i_req_ft_reg (
      .clk_i,
      .rst_ni,
      .clr_i     (1'b0),
      .testmode_i(1'b0),
      .valid_i   (arb_req_valid),
      .ready_o   (arb_req_ready),
      .data_i    (arb_req),
      .valid_o   (apb_req_valid),
      .ready_i   (apb_req_ready),
      .data_o    (apb_req)
    );
  end

  if (PipelineResponse) begin : gen_resp_spill
    spill_register #(
      .T     (axi_pkg::resp_t),
      .Bypass(1'b0)
    ) i_write_resp_spill (
      .clk_i,
      .rst_ni,
      .valid_i(apb_wresp_valid),
      .ready_o(apb_wresp_ready),
      .data_i (apb_wresp),
      .valid_o(axi_bresp_valid),
      .ready_i(axi_lite_req_i.b_ready),
      .data_o (axi_bresp)
    );
    spill_register #(
      .T     (int_resp_t),
      .Bypass(1'b0)
    ) i_read_resp_spill (
      .clk_i,
      .rst_ni,
      .valid_i(apb_rresp_valid),
      .ready_o(apb_rresp_ready),
      .data_i (apb_rresp),
      .valid_o(axi_rresp_valid),
      .ready_i(axi_lite_req_i.r_ready),
      .data_o (axi_rresp)
    );
  end else begin : gen_resp_ft_reg
    fall_through_register #(
      .T(axi_pkg::resp_t)
    ) i_write_resp_ft_reg (
      .clk_i,
      .rst_ni,
      .clr_i     (1'b0),
      .testmode_i(1'b0),
      .valid_i   (apb_wresp_valid),
      .ready_o   (apb_wresp_ready),
      .data_i    (apb_wresp),
      .valid_o   (axi_bresp_valid),
      .ready_i   (axi_lite_req_i.b_ready),
      .data_o    (axi_bresp)
    );
    fall_through_register #(
      .T(int_resp_t)
    ) i_read_resp_ft_reg (
      .clk_i,
      .rst_ni,
      .clr_i     (1'b0),
      .testmode_i(1'b0),
      .valid_i   (apb_rresp_valid),
      .ready_o   (apb_rresp_ready),
      .data_i    (apb_rresp),
      .valid_o   (axi_rresp_valid),
      .ready_i   (axi_lite_req_i.r_ready),
      .data_o    (axi_rresp)
    );
  end

  // -----------------------------------------------------------------------------------------------
  // APB master FSM
  // -----------------------------------------------------------------------------------------------
  // APB access state machine
  apb_state_e apb_state_q, apb_state_d;
  logic     apb_update;
  // output of address decoder to determine PSELx signal
  logic     apb_dec_valid;
  sel_idx_t apb_sel_idx;
  addr_decode #(
    .NoIndices(NoApbSlaves),
    .NoRules  (NoRules),
    .addr_t   (addr_t),
    .rule_t   (rule_t)
  ) i_apb_decode (
    .addr_i          (apb_req.addr),
    .addr_map_i      (addr_map_i),
    .idx_o           (apb_sel_idx),
    .dec_valid_o     (apb_dec_valid),   // when not valid -> decode error
    .dec_error_o     (  /*not used*/),
    .en_default_idx_i('0),
    .default_idx_i   ('0)
  );

  always_comb begin
    // default assignments
    apb_state_d     = apb_state_q;
    apb_update      = 1'b0;
    apb_req_o       = '0;
    apb_req_ready   = 1'b0;
    // response defaults to the two response spill registers
    apb_wresp       = axi_pkg::RESP_SLVERR;
    apb_wresp_valid = 1'b0;
    apb_rresp       = '{data: data_t'(32'hDEA110C8), resp: axi_pkg::RESP_SLVERR};
    apb_rresp_valid = 1'b0;

    unique case (apb_state_q)
      Setup: begin
        // `Idle` and `Setup` steps
        // can check here for readiness, because the response goes into spill_registers
        if (apb_req_valid && apb_wresp_ready && apb_rresp_ready) begin
          if (apb_dec_valid) begin
            // `Setup` step
            // set the request output
            apb_req_o[apb_sel_idx] = '{
              paddr: apb_req.addr,
              pprot: apb_req.prot,
              psel: 1'b1,
              penable: 1'b0,
              pwrite: apb_req.write,
              pwdata: apb_req.data,
              pstrb: apb_req.strb
            };
            apb_state_d = Access;
            apb_update = 1'b1;
          end else begin
            // decode error, generate error and do not generate APB request, pop it
            apb_req_ready = 1'b1;
            if (apb_req.write) begin
              apb_wresp       = axi_pkg::RESP_DECERR;
              apb_wresp_valid = 1'b1;
            end else begin
              apb_rresp.resp  = axi_pkg::RESP_DECERR;
              apb_rresp_valid = 1'b1;
            end
          end
        end
      end
      Access: begin
        // `Access` step
        apb_req_o[apb_sel_idx] = '{
          paddr: apb_req.addr,
          pprot: apb_req.prot,
          psel: 1'b1,
          penable: 1'b1,
          pwrite: apb_req.write,
          pwdata: apb_req.data,
          pstrb: apb_req.strb
        };
        if (apb_resp_i[apb_sel_idx].pready) begin
          // transfer, pop the request, generate response and update state
          apb_req_ready = 1'b1;
          // we are only in this state if the response spill registers are ready anyway
          if (apb_req.write) begin
            apb_wresp = apb_resp_i[apb_sel_idx].pslverr ? axi_pkg::RESP_SLVERR : axi_pkg::RESP_OKAY;
            apb_wresp_valid = 1'b1;
          end else begin
            apb_rresp.data = apb_resp_i[apb_sel_idx].prdata;
            apb_rresp.resp  = apb_resp_i[apb_sel_idx].pslverr ?
                                  axi_pkg::RESP_SLVERR : axi_pkg::RESP_OKAY;
            apb_rresp_valid = 1'b1;
          end
          apb_state_d = Setup;
          apb_update  = 1'b1;
        end
      end
      default:  /* do nothing */;
    endcase
  end

  `FFLARN(apb_state_q, apb_state_d, apb_update, Setup, clk_i, rst_ni)

  // parameter check
  // pragma translate_off
`ifndef VERILATOR
  initial begin : check_params
    addr_width :
    assert ($bits(axi_lite_req_i.aw.addr) == $bits(apb_req_o[0].paddr))
    else $fatal(1, $sformatf("AXI4-Lite and APB address width not equal"));
    wdata_width :
    assert ($bits(axi_lite_req_i.w.data) == $bits(apb_req_o[0].pwdata))
    else $fatal(1, $sformatf("AXI4-Lite and APB write data width not equal"));
    strb_width :
    assert ($bits(axi_lite_req_i.w.strb) == $bits(apb_req_o[0].pstrb))
    else $fatal(1, $sformatf("AXI4-Lite and APB strobe width not equal"));
    rdata_width :
    assert ($bits(axi_lite_resp_o.r.data) == $bits(apb_resp_i[0].prdata))
    else $fatal(1, $sformatf("AXI4-Lite and APB read data width not equal"));
    sel_width :
    assert ($bits(apb_req_o[0].psel) == 32'd1)
    else $fatal(1, $sformatf("APB psel signal has to have a width of 1'b1"));
  end
`endif
  // pragma translate_on
endmodule

`include "axi/typedef.svh"
`include "axi/assign.svh"

module axi_lite_to_apb_intf #(
  parameter int unsigned NoApbSlaves = 32'd1,  // Number of connected APB slaves
  parameter int unsigned NoRules = 32'd1,  // Number of APB address rules
  parameter int unsigned AddrWidth = 32'd32,  // Address width
  parameter int unsigned DataWidth = 32'd32,  // Data width
  parameter bit PipelineRequest = 1'b0,  // Pipeline request path
  parameter bit PipelineResponse = 1'b0,  // Pipeline response path
  parameter type rule_t = logic,  // Address Decoder rule from `common_cells`
  // DEPENDENT PARAMERETS, DO NOT OVERWRITE!
  parameter type addr_t = logic [AddrWidth-1:0],
  parameter type data_t = logic [DataWidth-1:0],
  parameter type strb_t = logic [DataWidth/8-1:0],
  parameter type sel_t = logic [NoApbSlaves-1:0]
) (
  input  logic                            clk_i,      // Clock
  input  logic                            rst_ni,     // Asynchronous reset active low
  // AXI LITE slave port
         AXI_LITE.Slave                   slv,
  // APB master port
  output addr_t                           paddr_o,
  output logic          [            2:0] pprot_o,
  output sel_t                            pselx_o,
  output logic                            penable_o,
  output logic                            pwrite_o,
  output data_t                           pwdata_o,
  output strb_t                           pstrb_o,
  input  logic          [NoApbSlaves-1:0] pready_i,
  input  data_t         [NoApbSlaves-1:0] prdata_i,
  input                 [NoApbSlaves-1:0] pslverr_i,
  // APB Slave Address Map
  input  rule_t         [    NoRules-1:0] addr_map_i
);
  localparam int unsigned SelIdxWidth = NoApbSlaves > 1 ? $clog2(NoApbSlaves) : 1;

  typedef struct packed {
    addr_t          paddr;    // same as AXI4-Lite
    axi_pkg::prot_t pprot;    // same as AXI4-Lite, specification is the same
    logic           psel;     // onehot, one psel line per connected APB4 slave
    logic           penable;  // enable signal shows second APB4 cycle
    logic           pwrite;   // write enable
    data_t          pwdata;   // write data, comes from W channel
    strb_t          pstrb;    // write strb, comes from W channel
  } apb_req_t;

  typedef struct packed {
    logic  pready;   // slave signals that it is ready
    data_t prdata;   // read data, connects to R channel
    logic  pslverr;  // gets translated into either `axi_pkg::RESP_OK` or `axi_pkg::RESP_SLVERR`
  } apb_resp_t;

  `AXI_LITE_TYPEDEF_AW_CHAN_T(aw_chan_t, addr_t)
  `AXI_LITE_TYPEDEF_W_CHAN_T(w_chan_t, data_t, strb_t)
  `AXI_LITE_TYPEDEF_B_CHAN_T(b_chan_t)
  `AXI_LITE_TYPEDEF_AR_CHAN_T(ar_chan_t, addr_t)
  `AXI_LITE_TYPEDEF_R_CHAN_T(r_chan_t, data_t)
  `AXI_LITE_TYPEDEF_REQ_T(axi_req_t, aw_chan_t, w_chan_t, ar_chan_t)
  `AXI_LITE_TYPEDEF_RESP_T(axi_resp_t, b_chan_t, r_chan_t)

  axi_req_t                    axi_req;
  axi_resp_t                   axi_resp;
  apb_req_t  [NoApbSlaves-1:0] apb_req;
  apb_resp_t [NoApbSlaves-1:0] apb_resp;
  logic      [SelIdxWidth-1:0] apb_sel;

  `AXI_LITE_ASSIGN_TO_REQ(axi_req, slv)
  `AXI_LITE_ASSIGN_FROM_RESP(slv, axi_resp)

  onehot_to_bin #(
    .ONEHOT_WIDTH(NoApbSlaves)
  ) i_onehot_to_bin (
    .onehot(pselx_o),
    .bin   (apb_sel)
  );

  assign paddr_o   = apb_req[apb_sel].paddr;
  assign pprot_o   = apb_req[apb_sel].pprot;
  assign penable_o = apb_req[apb_sel].penable;
  assign pwrite_o  = apb_req[apb_sel].pwrite;
  assign pwdata_o  = apb_req[apb_sel].pwdata;
  assign pstrb_o   = apb_req[apb_sel].pstrb;
  for (genvar i = 0; i < NoApbSlaves; i++) begin : gen_apb_resp_assign
    assign pselx_o[i]          = apb_req[i].psel;
    assign apb_resp[i].pready  = pready_i[i];
    assign apb_resp[i].prdata  = prdata_i[i];
    assign apb_resp[i].pslverr = pslverr_i[i];
  end

  axi_lite_to_apb #(
    .NoApbSlaves     (NoApbSlaves),
    .NoRules         (NoRules),
    .AddrWidth       (AddrWidth),
    .DataWidth       (DataWidth),
    .PipelineRequest (PipelineRequest),
    .PipelineResponse(PipelineResponse),
    .axi_lite_req_t  (axi_req_t),
    .axi_lite_resp_t (axi_resp_t),
    .apb_req_t       (apb_req_t),
    .apb_resp_t      (apb_resp_t),
    .rule_t          (rule_t)
  ) i_axi_lite_to_apb (
    .clk_i,  // Clock
    .rst_ni,  // Asynchronous reset active low
    // AXI LITE slave port
    .axi_lite_req_i (axi_req),
    .axi_lite_resp_o(axi_resp),
    // APB master port
    .apb_req_o      (apb_req),
    .apb_resp_i     (apb_resp),
    // APB Slave Address Map
    .addr_map_i
  );
endmodule
