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

`include "common_cells/registers.svh"

`ifdef QUESTA
// Derive `TARGET_VSIM`, which is used for tool-specific workarounds in this file, from `QUESTA`,
// which is automatically set in Questa.
`define TARGET_VSIM
`endif

// axi_lite_demux: Demultiplex an AXI4-Lite bus from one subordinate port to multiple manager ports.
//                 The selection signal at the AW and AR channel has to follow the same
//                 stability rules as the corresponding AXI4-Lite channel.

module axi_lite_demux #(
  parameter type         aw_chan_t      = logic, // AXI4-Lite AW channel
  parameter type         w_chan_t       = logic, // AXI4-Lite  W channel
  parameter type         b_chan_t       = logic, // AXI4-Lite  B channel
  parameter type         ar_chan_t      = logic, // AXI4-Lite AR channel
  parameter type         r_chan_t       = logic, // AXI4-Lite  R channel
  parameter type         axi_lite_req_t = logic, // AXI4-Lite request struct
  parameter type         axi_lite_rsp_t = logic, // AXI4-Lite response struct
  parameter int unsigned NumMgrPorts    = 32'd0, // Number of instantiated ports
  parameter int unsigned MaxTrans       = 32'd0, // Maximum number of open transactions per channel
  parameter bit          FallThrough    = 1'b0,  // FIFOs are in fall through mode
  parameter bit          SpillAw        = 1'b1,  // insert one cycle latency on subordinate AW
  parameter bit          SpillW         = 1'b0,  // insert one cycle latency on subordinate  W
  parameter bit          SpillB         = 1'b0,  // insert one cycle latency on subordinate  B
  parameter bit          SpillAr        = 1'b1,  // insert one cycle latency on subordinate AR
  parameter bit          SpillR         = 1'b0,  // insert one cycle latency on subordinate  R
  // Dependent parameters, DO NOT OVERRIDE!
  parameter type         select_t       = logic [$clog2(NumMgrPorts)-1:0]
) (
  input  logic                            clk_i,
  input  logic                            rst_ni,
  input  logic                            test_i,
  // subordinate port (AXI4-Lite input), connect manager module here
  input  axi_lite_req_t                   sbr_req_i,
  input  select_t                         sbr_aw_select_i,
  input  select_t                         sbr_ar_select_i,
  output axi_lite_rsp_t                   sbr_rsp_o,
  // manager ports (AXI4-Lite outputs), connect subordinate modules here
  output axi_lite_req_t [NumMgrPorts-1:0] mgr_reqs_o,
  input  axi_lite_rsp_t [NumMgrPorts-1:0] mgr_rsps_i
);

  //--------------------------------------
  // Typedefs for the spill registers
  //--------------------------------------
  typedef struct packed {
    aw_chan_t aw;
    select_t  select;
  } aw_chan_select_t;
  typedef struct packed {
    ar_chan_t ar;
    select_t  select;
  } ar_chan_select_t;

  if (NumMgrPorts == 32'd1) begin : gen_no_demux
    // degenerate case, connect subordinate to manager port
    spill_register #(
      .T       ( aw_chan_t  ),
      .Bypass  ( ~SpillAw   )
    ) i_aw_spill_reg (
      .clk_i   ( clk_i                    ),
      .rst_ni  ( rst_ni                   ),
      .valid_i ( sbr_req_i.aw_valid       ),
      .ready_o ( sbr_rsp_o.aw_ready       ),
      .data_i  ( sbr_req_i.aw             ),
      .valid_o ( mgr_reqs_o[0].aw_valid   ),
      .ready_i ( mgr_rsps_i[0].aw_ready   ),
      .data_o  ( mgr_reqs_o[0].aw         )
    );
    spill_register #(
      .T       ( w_chan_t  ),
      .Bypass  ( ~SpillW   )
    ) i_w_spill_reg (
      .clk_i   ( clk_i                   ),
      .rst_ni  ( rst_ni                  ),
      .valid_i ( sbr_req_i.w_valid       ),
      .ready_o ( sbr_rsp_o.w_ready       ),
      .data_i  ( sbr_req_i.w             ),
      .valid_o ( mgr_reqs_o[0].w_valid   ),
      .ready_i ( mgr_rsps_i[0].w_ready   ),
      .data_o  ( mgr_reqs_o[0].w         )
    );
    spill_register #(
      .T       ( b_chan_t ),
      .Bypass  ( ~SpillB      )
    ) i_b_spill_reg (
      .clk_i   ( clk_i                  ),
      .rst_ni  ( rst_ni                 ),
      .valid_i ( mgr_rsps_i[0].b_valid  ),
      .ready_o ( mgr_reqs_o[0].b_ready  ),
      .data_i  ( mgr_rsps_i[0].b        ),
      .valid_o ( sbr_rsp_o.b_valid      ),
      .ready_i ( sbr_req_i.b_ready      ),
      .data_o  ( sbr_rsp_o.b            )
    );
    spill_register #(
      .T       ( ar_chan_t  ),
      .Bypass  ( ~SpillAr   )
    ) i_ar_spill_reg (
      .clk_i   ( clk_i                    ),
      .rst_ni  ( rst_ni                   ),
      .valid_i ( sbr_req_i.ar_valid       ),
      .ready_o ( sbr_rsp_o.ar_ready       ),
      .data_i  ( sbr_req_i.ar             ),
      .valid_o ( mgr_reqs_o[0].ar_valid   ),
      .ready_i ( mgr_rsps_i[0].ar_ready   ),
      .data_o  ( mgr_reqs_o[0].ar         )
    );
    spill_register #(
      .T       ( r_chan_t ),
      .Bypass  ( ~SpillR      )
    ) i_r_spill_reg (
      .clk_i   ( clk_i                  ),
      .rst_ni  ( rst_ni                 ),
      .valid_i ( mgr_rsps_i[0].r_valid  ),
      .ready_o ( mgr_reqs_o[0].r_ready  ),
      .data_i  ( mgr_rsps_i[0].r        ),
      .valid_o ( sbr_rsp_o.r_valid      ),
      .ready_i ( sbr_req_i.r_ready      ),
      .data_o  ( sbr_rsp_o.r            )
    );

  end else begin : gen_demux
    // normal non degenerate case


    //--------------------------------------
    //--------------------------------------
    // Signal Declarations
    //--------------------------------------
    //--------------------------------------

    //--------------------------------------
    // Write Transaction
    //--------------------------------------
    aw_chan_select_t        sbr_aw_chan;
    logic                   sbr_aw_valid,    sbr_aw_ready;

    logic [NumMgrPorts-1:0] mgr_aw_valids, mgr_aw_readies;

    logic                   lock_aw_valid_d, lock_aw_valid_q, load_aw_lock;

    logic                   w_fifo_push,     w_fifo_pop;
    logic                   w_fifo_full,     w_fifo_empty;

    w_chan_t                sbr_w_chan;
    select_t                w_select;
    logic                   sbr_w_valid,     sbr_w_ready;

    logic                   /*w_pop*/        b_fifo_pop;
    logic                   b_fifo_full,     b_fifo_empty;

    b_chan_t                sbr_b_chan;
    select_t                b_select;
    logic                   sbr_b_valid,     sbr_b_ready;

    //--------------------------------------
    // Read Transaction
    //--------------------------------------
    ar_chan_select_t sbr_ar_chan;
    logic            sbr_ar_valid,    sbr_ar_ready;

    logic            r_fifo_push,     r_fifo_pop;
    logic            r_fifo_full,     r_fifo_empty;

    r_chan_t         sbr_r_chan;
    select_t         r_select;
    logic            sbr_r_valid,     sbr_r_ready;

    //--------------------------------------
    //--------------------------------------
    // Channel control
    //--------------------------------------
    //--------------------------------------

    //--------------------------------------
    // AW Channel
    //--------------------------------------
    `ifdef TARGET_VSIM
    // Workaround for bug in Questa 2020.2 and 2021.1: Flatten the struct into a logic vector before
    // instantiating `spill_register`.
    typedef logic [$bits(aw_chan_select_t)-1:0] aw_chan_select_flat_t;
    `else
    // Other tools, such as VCS, have problems with `$bits()`, so the workaround cannot be used
    // generally.
    typedef aw_chan_select_t aw_chan_select_flat_t;
    `endif
    aw_chan_select_flat_t sbr_aw_chan_select_in_flat,
                          sbr_aw_chan_select_out_flat;
    assign sbr_aw_chan_select_in_flat = {sbr_req_i.aw, sbr_aw_select_i};
    spill_register #(
      .T      ( aw_chan_select_flat_t         ),
      .Bypass ( ~SpillAw                      )
    ) i_aw_spill_reg (
      .clk_i   ( clk_i                        ),
      .rst_ni  ( rst_ni                       ),
      .valid_i ( sbr_req_i.aw_valid           ),
      .ready_o ( sbr_rsp_o.aw_ready           ),
      .data_i  ( sbr_aw_chan_select_in_flat   ),
      .valid_o ( sbr_aw_valid                 ),
      .ready_i ( sbr_aw_ready                 ),
      .data_o  ( sbr_aw_chan_select_out_flat  )
    );
    assign sbr_aw_chan = sbr_aw_chan_select_out_flat;

    // replicate AW channel to the request output
    for (genvar i = 0; i < NumMgrPorts; i++) begin : gen_mgr_aw
      assign mgr_reqs_o[i].aw       = sbr_aw_chan.aw;
      assign mgr_reqs_o[i].aw_valid = mgr_aw_valids[i];
      assign mgr_aw_readies[i]      = mgr_rsps_i[i].aw_ready;
    end

    // AW channel handshake control
    always_comb begin
      // default assignments
      lock_aw_valid_d = lock_aw_valid_q;
      load_aw_lock    = 1'b0;
      // handshake
      sbr_aw_ready    = 1'b0;
      mgr_aw_valids   = '0;
      // W FIFO input control
      w_fifo_push     = 1'b0;
      // control
      if (lock_aw_valid_q) begin
        // AW channel is locked and has valid output, fifo was pushed, as the new request was issued
        mgr_aw_valids[sbr_aw_chan.select] = 1'b1;
        if (mgr_aw_readies[sbr_aw_chan.select]) begin
          // transaction, go back to IDLE
          sbr_aw_ready    = 1'b1;
          lock_aw_valid_d = 1'b0;
          load_aw_lock    = 1'b1;
        end
      end else begin
        if (!w_fifo_full && sbr_aw_valid) begin
          // new transaction, push select in the FIFO and then look if transaction happened
          w_fifo_push                       = 1'b1;
          mgr_aw_valids[sbr_aw_chan.select] = 1'b1; // only set the valid when FIFO is not full
          if (mgr_aw_readies[sbr_aw_chan.select]) begin
            // transaction, notify subordinate port
            sbr_aw_ready = 1'b1;
          end else begin
            // no transaction, lock valid
            lock_aw_valid_d = 1'b1;
            load_aw_lock    = 1'b1;
          end
        end
      end
    end

    // lock the valid signal, as the selection gets pushed into the W FIFO on first assertion,
    // prevent further pushing
    `FFLARN(lock_aw_valid_q, lock_aw_valid_d, load_aw_lock, '0, clk_i, rst_ni)

    fifo_v3 #(
      .FALL_THROUGH( FallThrough ),
      .DEPTH       ( MaxTrans    ),
      .dtype       ( select_t    )
    ) i_w_fifo (
      .clk_i      ( clk_i              ),
      .rst_ni     ( rst_ni             ),
      .flush_i    ( 1'b0               ), // not used, because AXI4-Lite no preemtion rule
      .testmode_i ( test_i             ),
      .full_o     ( w_fifo_full        ),
      .empty_o    ( w_fifo_empty       ),
      .usage_o    ( /*not used*/       ),
      .data_i     ( sbr_aw_chan.select ),
      .push_i     ( w_fifo_push        ),
      .data_o     ( w_select           ),
      .pop_i      ( w_fifo_pop         )
    );

    //--------------------------------------
    // W Channel
    //--------------------------------------
    spill_register #(
      .T      ( w_chan_t ),
      .Bypass ( ~SpillW  )
    ) i_w_spill_reg (
      .clk_i   ( clk_i              ),
      .rst_ni  ( rst_ni             ),
      .valid_i ( sbr_req_i.w_valid  ),
      .ready_o ( sbr_rsp_o.w_ready  ),
      .data_i  ( sbr_req_i.w        ),
      .valid_o ( sbr_w_valid        ),
      .ready_i ( sbr_w_ready        ),
      .data_o  ( sbr_w_chan         )
    );

    // replicate W channel
    for (genvar i = 0; i < NumMgrPorts; i++) begin : gen_mgr_w
      assign mgr_reqs_o[i].w       = sbr_w_chan;
      assign mgr_reqs_o[i].w_valid = ~w_fifo_empty & ~b_fifo_full &
                                       sbr_w_valid & (w_select == select_t'(i));
    end
    assign sbr_w_ready = ~w_fifo_empty & ~b_fifo_full & mgr_rsps_i[w_select].w_ready;
    assign w_fifo_pop  = sbr_w_valid & sbr_w_ready;

    fifo_v3 #(
      .FALL_THROUGH( FallThrough ),
      .DEPTH       ( MaxTrans    ),
      .dtype       ( select_t    )
    ) i_b_fifo (
      .clk_i      ( clk_i        ),
      .rst_ni     ( rst_ni       ),
      .flush_i    ( 1'b0         ), // not used, because AXI4-Lite no preemption
      .testmode_i ( test_i       ),
      .full_o     ( b_fifo_full  ),
      .empty_o    ( b_fifo_empty ),
      .usage_o    ( /*not used*/ ),
      .data_i     ( w_select     ),
      .push_i     ( w_fifo_pop   ), // w beat was transferred, push selection to b channel
      .data_o     ( b_select     ),
      .pop_i      ( b_fifo_pop   )
    );

    //--------------------------------------
    // B Channel
    //--------------------------------------
    spill_register #(
      .T      ( b_chan_t ),
      .Bypass ( ~SpillB  )
    ) i_b_spill_reg (
      .clk_i   ( clk_i              ),
      .rst_ni  ( rst_ni             ),
      .valid_i ( sbr_b_valid        ),
      .ready_o ( sbr_b_ready        ),
      .data_i  ( sbr_b_chan         ),
      .valid_o ( sbr_rsp_o.b_valid  ),
      .ready_i ( sbr_req_i.b_ready  ),
      .data_o  ( sbr_rsp_o.b        )
    );

    // connect the response if the FIFO has valid data in it
    assign sbr_b_chan      = (!b_fifo_empty) ? mgr_rsps_i[b_select].b : '0;
    assign sbr_b_valid     =  ~b_fifo_empty  & mgr_rsps_i[b_select].b_valid;
    for (genvar i = 0; i < NumMgrPorts; i++) begin : gen_mgr_b
      assign mgr_reqs_o[i].b_ready = ~b_fifo_empty & sbr_b_ready & (b_select == select_t'(i));
    end
    assign b_fifo_pop = sbr_b_valid & sbr_b_ready;

    //--------------------------------------
    // AR Channel
    //--------------------------------------
    // Workaround for bug in Questa (see comments on AW channel for details).
    `ifdef TARGET_VSIM
    typedef logic [$bits(ar_chan_select_t)-1:0] ar_chan_select_flat_t;
    `else
    typedef ar_chan_select_t ar_chan_select_flat_t;
    `endif
    ar_chan_select_flat_t sbr_ar_chan_select_in_flat,
                          sbr_ar_chan_select_out_flat;
    assign sbr_ar_chan_select_in_flat = {sbr_req_i.ar, sbr_ar_select_i};
    spill_register #(
      .T      ( ar_chan_select_flat_t         ),
      .Bypass ( ~SpillAr                      )
    ) i_ar_spill_reg (
      .clk_i   ( clk_i                        ),
      .rst_ni  ( rst_ni                       ),
      .valid_i ( sbr_req_i.ar_valid           ),
      .ready_o ( sbr_rsp_o.ar_ready           ),
      .data_i  ( sbr_ar_chan_select_in_flat   ),
      .valid_o ( sbr_ar_valid                 ),
      .ready_i ( sbr_ar_ready                 ),
      .data_o  ( sbr_ar_chan_select_out_flat  )
    );
    assign sbr_ar_chan = sbr_ar_chan_select_out_flat;

    // replicate AR channel
    for (genvar i = 0; i < NumMgrPorts; i++) begin : gen_mgr_ar
      assign mgr_reqs_o[i].ar       = sbr_ar_chan.ar;
      assign mgr_reqs_o[i].ar_valid = ~r_fifo_full & sbr_ar_valid &
                                       (sbr_ar_chan.select == select_t'(i));
    end
    assign sbr_ar_ready = ~r_fifo_full & mgr_rsps_i[sbr_ar_chan.select].ar_ready;
    assign r_fifo_push  = sbr_ar_valid & sbr_ar_ready;

    fifo_v3 #(
      .FALL_THROUGH( FallThrough ),
      .DEPTH       ( MaxTrans    ),
      .dtype       ( select_t    )
    ) i_r_fifo (
      .clk_i      ( clk_i              ),
      .rst_ni     ( rst_ni             ),
      .flush_i    ( 1'b0               ), // not used, because AXI4-Lite no preemption rule
      .testmode_i ( test_i             ),
      .full_o     ( r_fifo_full        ),
      .empty_o    ( r_fifo_empty       ),
      .usage_o    ( /*not used*/       ),
      .data_i     ( sbr_ar_chan.select ),
      .push_i     ( r_fifo_push        ),
      .data_o     ( r_select           ),
      .pop_i      ( r_fifo_pop         )
    );

    //--------------------------------------
    // R Channel
    //--------------------------------------
    spill_register #(
      .T      ( r_chan_t ),
      .Bypass ( ~SpillR  )
    ) i_r_spill_reg (
      .clk_i   ( clk_i              ),
      .rst_ni  ( rst_ni             ),
      .valid_i ( sbr_r_valid        ),
      .ready_o ( sbr_r_ready        ),
      .data_i  ( sbr_r_chan         ),
      .valid_o ( sbr_rsp_o.r_valid  ),
      .ready_i ( sbr_req_i.r_ready  ),
      .data_o  ( sbr_rsp_o.r        )
    );

    // connect the response if the FIFO has valid data in it
    always_comb begin
       sbr_r_chan  = '0;
       sbr_r_valid = '0;
       if (!r_fifo_empty) begin
          sbr_r_chan  = mgr_rsps_i[r_select].r;
          sbr_r_valid = mgr_rsps_i[r_select].r_valid;
       end
    end

    for (genvar i = 0; i < NumMgrPorts; i++) begin : gen_mgr_r
      assign mgr_reqs_o[i].r_ready = ~r_fifo_empty & sbr_r_ready & (r_select == select_t'(i));
    end
    assign r_fifo_pop      = sbr_r_valid & sbr_r_ready;

    // pragma translate_off
    `ifndef VERILATOR
    default disable iff (!rst_ni);
    aw_select: assume property( @(posedge clk_i) (sbr_req_i.aw_valid |->
                                                 (sbr_aw_select_i < NumMgrPorts))) else
      $fatal(1, "sbr_aw_select_i is %d: AW has selected a subordinate that is not defined.\
                 NumMgrPorts: %d", sbr_aw_select_i, NumMgrPorts);
    ar_select: assume property( @(posedge clk_i) (sbr_req_i.ar_valid |->
                                                 (sbr_ar_select_i < NumMgrPorts))) else
      $fatal(1, "sbr_ar_select_i is %d: AR has selected a subordinate that is not defined.\
                 NumMgrPorts: %d", sbr_ar_select_i, NumMgrPorts);
    aw_valid_stable: assert property( @(posedge clk_i) (sbr_aw_valid && !sbr_aw_ready)
                                                       |=> sbr_aw_valid) else
      $fatal(1, "aw_valid was deasserted, when aw_ready = 0 in last cycle.");
    ar_valid_stable: assert property( @(posedge clk_i) (sbr_ar_valid && !sbr_ar_ready)
                                                       |=> sbr_ar_valid) else
      $fatal(1, "ar_valid was deasserted, when ar_ready = 0 in last cycle.");
    aw_stable: assert property( @(posedge clk_i) (sbr_aw_valid && !sbr_aw_ready)
                               |=> $stable(sbr_aw_chan)) else
      $fatal(1, "sbr_aw_chan_select unstable with valid set.");
    ar_stable: assert property( @(posedge clk_i) (sbr_ar_valid && !sbr_ar_ready)
                               |=> $stable(sbr_ar_chan)) else
      $fatal(1, "sbr_aw_chan_select unstable with valid set.");
    `endif
    // pragma translate_on
  end

  // pragma translate_off
  `ifndef VERILATOR
    initial begin: p_assertions
      NumPorts:  assert (NumMgrPorts > 0) else $fatal("Number of manager ports must be at least 1!");
      MaxTnx:    assert (MaxTrans   > 0) else $fatal("Number of transactions must be at least 1!");
    end
  `endif
  // pragma translate_on
endmodule

`include "axi/assign.svh"
`include "axi/typedef.svh"

module axi_lite_demux_intf #(
  parameter int unsigned AddrWidth    = 32'd0,
  parameter int unsigned DataWidth    = 32'd0,
  parameter int unsigned NumMgrPorts  = 32'd0,
  parameter int unsigned MaxTrans     = 32'd0,
  parameter bit          FallThrough  = 1'b0,
  parameter bit          SpillAw      = 1'b1,
  parameter bit          SpillW       = 1'b0,
  parameter bit          SpillB       = 1'b0,
  parameter bit          SpillAr      = 1'b1,
  parameter bit          SpillR       = 1'b0,
  // Dependent parameters, DO NOT OVERRIDE!
  parameter type         select_t     = logic [$clog2(NumMgrPorts)-1:0]
) (
  input  logic     clk_i,               // Clock
  input  logic     rst_ni,              // Asynchronous reset active low
  input  logic     test_i,              // Testmode enable
  input  select_t  sbr_aw_select_i,     // has to be stable, when aw_valid
  input  select_t  sbr_ar_select_i,     // has to be stable, when ar_valid
  AXI_LITE.Subordinate   sbr,                 // subordinate port
  AXI_LITE.Manager  mgr [NumMgrPorts-1:0]// manager ports
);
  typedef logic [AddrWidth-1:0]   addr_t;
  typedef logic [DataWidth-1:0]   data_t;
  typedef logic [DataWidth/8-1:0] strb_t;
  `AXI_LITE_TYPEDEF_AW_CHAN_T(aw_chan_t, addr_t)
  `AXI_LITE_TYPEDEF_W_CHAN_T(w_chan_t, data_t, strb_t)
  `AXI_LITE_TYPEDEF_B_CHAN_T(b_chan_t)
  `AXI_LITE_TYPEDEF_AR_CHAN_T(ar_chan_t, addr_t)
  `AXI_LITE_TYPEDEF_R_CHAN_T(r_chan_t, data_t)
  `AXI_LITE_TYPEDEF_REQ_T(axi_lite_req_t, aw_chan_t, w_chan_t, ar_chan_t)
  `AXI_LITE_TYPEDEF_RSP_T(axi_lite_rsp_t, b_chan_t, r_chan_t)

  axi_lite_req_t                   sbr_req;
  axi_lite_rsp_t                   sbr_rsp;
  axi_lite_req_t [NumMgrPorts-1:0] mgr_reqs;
  axi_lite_rsp_t [NumMgrPorts-1:0] mgr_rsps;

  `AXI_LITE_ASSIGN_TO_REQ(sbr_req, sbr)
  `AXI_LITE_ASSIGN_FROM_RSP(sbr, sbr_rsp)

  for (genvar i = 0; i < NumMgrPorts; i++) begin : gen_assign_mgr_ports
    `AXI_LITE_ASSIGN_FROM_REQ(mgr[i], mgr_reqs[i])
    `AXI_LITE_ASSIGN_TO_RSP(mgr_rsps[i], mgr[i])
  end

  axi_lite_demux #(
    .aw_chan_t      (      aw_chan_t ),
    .w_chan_t       (       w_chan_t ),
    .b_chan_t       (       b_chan_t ),
    .ar_chan_t      (      ar_chan_t ),
    .r_chan_t       (       r_chan_t ),
    .axi_lite_req_t ( axi_lite_req_t ),
    .axi_lite_rsp_t ( axi_lite_rsp_t ),
    .NumMgrPorts    ( NumMgrPorts    ),
    .MaxTrans       ( MaxTrans       ),
    .FallThrough    ( FallThrough    ),
    .SpillAw        ( SpillAw        ),
    .SpillW         ( SpillW         ),
    .SpillB         ( SpillB         ),
    .SpillAr        ( SpillAr        ),
    .SpillR         ( SpillR         )
  ) i_axi_demux (
    .clk_i,
    .rst_ni,
    .test_i,
    // subordinate Port
    .sbr_req_i       ( sbr_req         ),
    .sbr_aw_select_i ( sbr_aw_select_i ), // must be stable while sbr_aw_valid_i
    .sbr_ar_select_i ( sbr_ar_select_i ), // must be stable while sbr_ar_valid_i
    .sbr_rsp_o       ( sbr_rsp         ),
    // mgrer ports
    .mgr_reqs_o      ( mgr_reqs        ),
    .mgr_rsps_i      ( mgr_rsps        )
  );

  // pragma translate_off
  `ifndef VERILATOR
    initial begin: p_assertions
      assert (AddrWidth > 0) else $fatal("AddrWidth Parameter has to be > 0!");
      assert (DataWidth > 0) else $fatal("DataWidth Parameter has to be > 0!");
    end
  `endif
  // pragma translate_on
endmodule
