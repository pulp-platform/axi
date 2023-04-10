// Copyright (c) 2020 ETH Zurich, University of Bologna
//
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

// AXI4-Lite Multiplexer: This module multiplexes the AXI4-Lite subordinate ports down to one manager port.
//                        The multiplexing happens in a round robin fashion, responses get
//                        sent back in order.

// register macros
`include "common_cells/registers.svh"

module axi_lite_mux #(
  // AXI4-Lite parameter and channel types
  parameter type          aw_chan_t  = logic, // AW LITE Channel Type
  parameter type           w_chan_t  = logic, //  W LITE Channel Type
  parameter type           b_chan_t  = logic, //  B LITE Channel Type
  parameter type          ar_chan_t  = logic, // AR LITE Channel Type
  parameter type           r_chan_t  = logic, //  R LITE Channel Type
  parameter type     axi_lite_req_t  = logic, // AXI4-Lite request type
  parameter type     axi_lite_rsp_t  = logic, // AXI4-Lite response type
  parameter int unsigned NumSbrPorts = 32'd0, // Number of subordinate ports
  // Maximum number of outstanding transactions per write or read
  parameter int unsigned MaxTrans    = 32'd0,
  // If enabled, this multiplexer is purely combinatorial
  parameter bit          FallThrough = 1'b0,
  // add spill register on write manager port, adds a cycle latency on write channels
  parameter bit          SpillAw     = 1'b1,
  parameter bit          SpillW      = 1'b0,
  parameter bit          SpillB      = 1'b0,
  // add spill register on read manager port, adds a cycle latency on read channels
  parameter bit          SpillAr     = 1'b1,
  parameter bit          SpillR      = 1'b0
) (
  input  logic                            clk_i,    // Clock
  input  logic                            rst_ni,   // Asynchronous reset active low
  input  logic                            test_i,   // Test Mode enable
  // subordinate ports (AXI4-Lite inputs), connect manager modules here
  input  axi_lite_req_t [NumSbrPorts-1:0] sbr_reqs_i,
  output axi_lite_rsp_t [NumSbrPorts-1:0] sbr_rsps_o,
  // manager port (AXI4-Lite output), connect subordinate module here
  output axi_lite_req_t                   mgr_req_o,
  input  axi_lite_rsp_t                   mgr_rsp_i
);
  // pass through if only one subordinate port
  if (NumSbrPorts == 32'h1) begin : gen_no_mux
    spill_register #(
      .T       ( aw_chan_t  ),
      .Bypass  ( ~SpillAw   )
    ) i_aw_spill_reg (
      .clk_i   ( clk_i                    ),
      .rst_ni  ( rst_ni                   ),
      .valid_i ( sbr_reqs_i[0].aw_valid   ),
      .ready_o ( sbr_rsps_o[0].aw_ready   ),
      .data_i  ( sbr_reqs_i[0].aw         ),
      .valid_o ( mgr_req_o.aw_valid       ),
      .ready_i ( mgr_rsp_i.aw_ready       ),
      .data_o  ( mgr_req_o.aw             )
    );
    spill_register #(
      .T       ( w_chan_t ),
      .Bypass  ( ~SpillW  )
    ) i_w_spill_reg (
      .clk_i   ( clk_i                   ),
      .rst_ni  ( rst_ni                  ),
      .valid_i ( sbr_reqs_i[0].w_valid   ),
      .ready_o ( sbr_rsps_o[0].w_ready   ),
      .data_i  ( sbr_reqs_i[0].w         ),
      .valid_o ( mgr_req_o.w_valid       ),
      .ready_i ( mgr_rsp_i.w_ready       ),
      .data_o  ( mgr_req_o.w             )
    );
    spill_register #(
      .T       ( b_chan_t ),
      .Bypass  ( ~SpillB  )
    ) i_b_spill_reg (
      .clk_i   ( clk_i                 ),
      .rst_ni  ( rst_ni                ),
      .valid_i ( mgr_rsp_i.b_valid     ),
      .ready_o ( mgr_req_o.b_ready     ),
      .data_i  ( mgr_rsp_i.b           ),
      .valid_o ( sbr_rsps_o[0].b_valid ),
      .ready_i ( sbr_reqs_i[0].b_ready ),
      .data_o  ( sbr_rsps_o[0].b       )
    );
    spill_register #(
      .T       ( ar_chan_t ),
      .Bypass  ( ~SpillAr  )
    ) i_ar_spill_reg (
      .clk_i   ( clk_i                    ),
      .rst_ni  ( rst_ni                   ),
      .valid_i ( sbr_reqs_i[0].ar_valid   ),
      .ready_o ( sbr_rsps_o[0].ar_ready   ),
      .data_i  ( sbr_reqs_i[0].ar         ),
      .valid_o ( mgr_req_o.ar_valid       ),
      .ready_i ( mgr_rsp_i.ar_ready       ),
      .data_o  ( mgr_req_o.ar             )
    );
    spill_register #(
      .T       ( r_chan_t ),
      .Bypass  ( ~SpillR  )
    ) i_r_spill_reg (
      .clk_i   ( clk_i                 ),
      .rst_ni  ( rst_ni                ),
      .valid_i ( mgr_rsp_i.r_valid     ),
      .ready_o ( mgr_req_o.r_ready     ),
      .data_i  ( mgr_rsp_i.r           ),
      .valid_o ( sbr_rsps_o[0].r_valid ),
      .ready_i ( sbr_reqs_i[0].r_ready ),
      .data_o  ( sbr_rsps_o[0].r       )
    );

  // other non degenerate cases
  end else begin : gen_mux
    // typedef for the FIFO types
    typedef logic [$clog2(NumSbrPorts)-1:0] select_t;

    // input to the AW arbitration tree, unpacked from request struct
    aw_chan_t [NumSbrPorts-1:0] sbr_aw_chans;
    logic     [NumSbrPorts-1:0] sbr_aw_valids, sbr_aw_readies;

    // AW channel arb tree decision
    select_t  aw_select;
    aw_chan_t mgr_aw_chan;
    logic     mgr_aw_valid, mgr_aw_ready;

    // AW manager handshake internal, so that we are able to stall, if w_fifo is full
    logic     aw_valid,     aw_ready;

    // FF to lock the AW valid signal, when a new arbitration decision is made the decision
    // gets pushed into the W FIFO, when it now stalls prevent subsequent pushing
    // This FF removes AW to W dependency
    logic     lock_aw_valid_d, lock_aw_valid_q;
    logic     load_aw_lock;

    // signals for the FIFO that holds the last switching decision of the AW channel
    logic     w_fifo_full,  w_fifo_empty;
    logic     w_fifo_push,  w_fifo_pop;

    // W channel spill reg
    select_t  w_select;
    w_chan_t  mgr_w_chan;
    logic     mgr_w_valid,  mgr_w_ready;

    // switching decision for the B response back routing
    select_t  b_select;
    // signals for the FIFO that holds the last switching decision of the AW channel
    logic     b_fifo_full,  b_fifo_empty;
    logic     /*w_fifo_pop*/b_fifo_pop;

    // B channel spill reg
    b_chan_t  mgr_b_chan;
    logic     mgr_b_valid,  mgr_b_ready;

    // input to the AR arbitration tree, unpacked from request struct
    ar_chan_t [NumSbrPorts-1:0] sbr_ar_chans;
    logic     [NumSbrPorts-1:0] sbr_ar_valids, sbr_ar_readies;

    // AR channel for when spill is enabled
    select_t  ar_select;
    ar_chan_t mgr_ar_chan;
    logic     mgr_ar_valid, mgr_ar_ready;

    // AR manager handshake internal, so that we are able to stall, if R_fifo is full
    logic     ar_valid,     ar_ready;

    // manager ID in the r_id
    select_t  r_select;

    // signals for the FIFO that holds the last switching decision of the AR channel
    logic     r_fifo_full,  r_fifo_empty;
    logic     r_fifo_push,  r_fifo_pop;

    // R channel spill reg
    r_chan_t  mgr_r_chan;
    logic     mgr_r_valid,  mgr_r_ready;

    //--------------------------------------
    // AW Channel
    //--------------------------------------
    // unpach AW channel from request/response array
    for (genvar i = 0; i < NumSbrPorts; i++) begin : gen_aw_arb_input
      assign sbr_aw_chans[i]         = sbr_reqs_i[i].aw;
      assign sbr_aw_valids[i]        = sbr_reqs_i[i].aw_valid;
      assign sbr_rsps_o[i].aw_ready = sbr_aw_readies[i];
    end
    rr_arb_tree #(
      .NumIn    ( NumSbrPorts ),
      .DataType ( aw_chan_t   ),
      .AxiVldRdy( 1'b1        ),
      .LockIn   ( 1'b1        )
    ) i_aw_arbiter (
      .clk_i  ( clk_i          ),
      .rst_ni ( rst_ni         ),
      .flush_i( 1'b0           ),
      .rr_i   ( '0             ),
      .req_i  ( sbr_aw_valids  ),
      .gnt_o  ( sbr_aw_readies ),
      .data_i ( sbr_aw_chans   ),
      .gnt_i  ( aw_ready       ),
      .req_o  ( aw_valid       ),
      .data_o ( mgr_aw_chan    ),
      .idx_o  ( aw_select      )
    );

    // control of the AW channel
    always_comb begin
      // default assignments
      lock_aw_valid_d = lock_aw_valid_q;
      load_aw_lock    = 1'b0;
      w_fifo_push     = 1'b0;
      mgr_aw_valid    = 1'b0;
      aw_ready        = 1'b0;
      // had a downstream stall, be valid and send the AW along
      if (lock_aw_valid_q) begin
        mgr_aw_valid = 1'b1;
        // transaction
        if (mgr_aw_ready) begin
          aw_ready        = 1'b1;
          lock_aw_valid_d = 1'b0;
          load_aw_lock    = 1'b1;
        end
      end else begin
        if (!w_fifo_full && aw_valid) begin
          mgr_aw_valid = 1'b1;
          w_fifo_push = 1'b1;
          if (mgr_aw_ready) begin
            aw_ready = 1'b1;
          end else begin
            // go to lock if transaction not in this cycle
            lock_aw_valid_d = 1'b1;
            load_aw_lock    = 1'b1;
          end
        end
      end
    end

    `FFLARN(lock_aw_valid_q, lock_aw_valid_d, load_aw_lock, '0, clk_i, rst_ni)

    fifo_v3 #(
      .FALL_THROUGH ( FallThrough ),
      .DEPTH        ( MaxTrans    ),
      .dtype        ( select_t    )
    ) i_w_fifo (
      .clk_i     ( clk_i        ),
      .rst_ni    ( rst_ni       ),
      .flush_i   ( 1'b0         ),
      .testmode_i( test_i       ),
      .full_o    ( w_fifo_full  ),
      .empty_o   ( w_fifo_empty ),
      .usage_o   (              ),
      .data_i    ( aw_select    ),
      .push_i    ( w_fifo_push  ),
      .data_o    ( w_select     ),
      .pop_i     ( w_fifo_pop   )
    );

    spill_register #(
      .T       ( aw_chan_t  ),
      .Bypass  ( ~SpillAw   ) // Param indicated that we want a spill reg
    ) i_aw_spill_reg (
      .clk_i   ( clk_i               ),
      .rst_ni  ( rst_ni              ),
      .valid_i ( mgr_aw_valid        ),
      .ready_o ( mgr_aw_ready        ),
      .data_i  ( mgr_aw_chan         ),
      .valid_o ( mgr_req_o.aw_valid  ),
      .ready_i ( mgr_rsp_i.aw_ready  ),
      .data_o  ( mgr_req_o.aw        )
    );

    //--------------------------------------
    // W Channel
    //--------------------------------------
    // multiplexer
    assign mgr_w_chan      = sbr_reqs_i[w_select].w;
    assign mgr_w_valid     = (!w_fifo_empty && !b_fifo_full) ? sbr_reqs_i[w_select].w_valid  : 1'b0;
    for (genvar i = 0; i < NumSbrPorts; i++) begin : gen_sbr_w_ready
      assign sbr_rsps_o[i].w_ready =  mgr_w_ready & ~w_fifo_empty &
                                      ~b_fifo_full & (w_select == select_t'(i));
    end
    assign w_fifo_pop      = mgr_w_valid & mgr_w_ready;

    fifo_v3 #(
      .FALL_THROUGH ( FallThrough ),
      .DEPTH        ( MaxTrans    ),
      .dtype        ( select_t    )
    ) i_b_fifo (
      .clk_i     ( clk_i        ),
      .rst_ni    ( rst_ni       ),
      .flush_i   ( 1'b0         ),
      .testmode_i( test_i       ),
      .full_o    ( b_fifo_full  ),
      .empty_o   ( b_fifo_empty ),
      .usage_o   (              ),
      .data_i    ( w_select     ),
      .push_i    ( w_fifo_pop   ), // push the selection for the B channel on W transaction
      .data_o    ( b_select     ),
      .pop_i     ( b_fifo_pop   )
    );

    spill_register #(
      .T       ( w_chan_t ),
      .Bypass  ( ~SpillW  )
    ) i_w_spill_reg (
      .clk_i   ( clk_i              ),
      .rst_ni  ( rst_ni             ),
      .valid_i ( mgr_w_valid        ),
      .ready_o ( mgr_w_ready        ),
      .data_i  ( mgr_w_chan         ),
      .valid_o ( mgr_req_o.w_valid  ),
      .ready_i ( mgr_rsp_i.w_ready  ),
      .data_o  ( mgr_req_o.w        )
    );

    //--------------------------------------
    // B Channel
    //--------------------------------------
    // replicate B channels
    for (genvar i = 0; i < NumSbrPorts; i++) begin : gen_sbr_resps_b
      assign sbr_rsps_o[i].b       = mgr_b_chan;
      assign sbr_rsps_o[i].b_valid = mgr_b_valid & ~b_fifo_empty & (b_select == select_t'(i));
    end
    assign mgr_b_ready    = ~b_fifo_empty & sbr_reqs_i[b_select].b_ready;
    assign b_fifo_pop     = mgr_b_valid & mgr_b_ready;

    spill_register #(
      .T       ( b_chan_t ),
      .Bypass  ( ~SpillB  )
    ) i_b_spill_reg (
      .clk_i   ( clk_i             ),
      .rst_ni  ( rst_ni            ),
      .valid_i ( mgr_rsp_i.b_valid ),
      .ready_o ( mgr_req_o.b_ready ),
      .data_i  ( mgr_rsp_i.b       ),
      .valid_o ( mgr_b_valid       ),
      .ready_i ( mgr_b_ready       ),
      .data_o  ( mgr_b_chan        )
    );

    //--------------------------------------
    // AR Channel
    //--------------------------------------
    // unpack AR channel from request/response struct
    for (genvar i = 0; i < NumSbrPorts; i++) begin : gen_ar_arb_input
      assign sbr_ar_chans[i]         = sbr_reqs_i[i].ar;
      assign sbr_ar_valids[i]        = sbr_reqs_i[i].ar_valid;
      assign sbr_rsps_o[i].ar_ready = sbr_ar_readies[i];
    end
    rr_arb_tree #(
      .NumIn    ( NumSbrPorts ),
      .DataType ( ar_chan_t   ),
      .AxiVldRdy( 1'b1        ),
      .LockIn   ( 1'b1        )
    ) i_ar_arbiter (
      .clk_i  ( clk_i          ),
      .rst_ni ( rst_ni         ),
      .flush_i( 1'b0           ),
      .rr_i   ( '0             ),
      .req_i  ( sbr_ar_valids  ),
      .gnt_o  ( sbr_ar_readies ),
      .data_i ( sbr_ar_chans   ),
      .gnt_i  ( ar_ready       ),
      .req_o  ( ar_valid       ),
      .data_o ( mgr_ar_chan    ),
      .idx_o  ( ar_select      )
    );

    // connect the handshake if there is space in the FIFO, no need for valid locking
    // as the R response is only allowed, when AR is transferred
    assign mgr_ar_valid = (!r_fifo_full) ? ar_valid     : 1'b0;
    assign ar_ready     = (!r_fifo_full) ? mgr_ar_ready : 1'b0;
    assign r_fifo_push  = mgr_ar_valid & mgr_ar_ready;

    fifo_v3 #(
      .FALL_THROUGH ( FallThrough ),
      .DEPTH        ( MaxTrans    ),
      .dtype        ( select_t    )
    ) i_r_fifo (
      .clk_i     ( clk_i        ),
      .rst_ni    ( rst_ni       ),
      .flush_i   ( 1'b0         ),
      .testmode_i( test_i       ),
      .full_o    ( r_fifo_full  ),
      .empty_o   ( r_fifo_empty ),
      .usage_o   (              ),
      .data_i    ( ar_select    ),
      .push_i    ( r_fifo_push  ), // push the selection when w transaction happens
      .data_o    ( r_select     ),
      .pop_i     ( r_fifo_pop   )
    );

    spill_register #(
      .T       ( ar_chan_t ),
      .Bypass  ( ~SpillAr  )
    ) i_ar_spill_reg (
      .clk_i   ( clk_i               ),
      .rst_ni  ( rst_ni              ),
      .valid_i ( mgr_ar_valid        ),
      .ready_o ( mgr_ar_ready        ),
      .data_i  ( mgr_ar_chan         ),
      .valid_o ( mgr_req_o.ar_valid  ),
      .ready_i ( mgr_rsp_i.ar_ready  ),
      .data_o  ( mgr_req_o.ar        )
    );

    //--------------------------------------
    // R Channel
    //--------------------------------------
    // replicate R channels
    for (genvar i = 0; i < NumSbrPorts; i++) begin : gen_sbr_rsps_r
      assign sbr_rsps_o[i].r       = mgr_r_chan;
      assign sbr_rsps_o[i].r_valid = mgr_r_valid & ~r_fifo_empty & (r_select == select_t'(i));
    end
    assign mgr_r_ready    = ~r_fifo_empty & sbr_reqs_i[r_select].r_ready;
    assign r_fifo_pop     = mgr_r_valid & mgr_r_ready;

    spill_register #(
      .T       ( r_chan_t ),
      .Bypass  ( ~SpillR  )
    ) i_r_spill_reg (
      .clk_i   ( clk_i             ),
      .rst_ni  ( rst_ni            ),
      .valid_i ( mgr_rsp_i.r_valid ),
      .ready_o ( mgr_req_o.r_ready ),
      .data_i  ( mgr_rsp_i.r       ),
      .valid_o ( mgr_r_valid       ),
      .ready_i ( mgr_r_ready       ),
      .data_o  ( mgr_r_chan        )
    );
  end

  // pragma translate_off
  `ifndef VERILATOR
    initial begin: p_assertions
      NumPorts:  assert (NumSbrPorts > 0) else $fatal("Number of subordinate ports must be at least 1!");
      MaxTnx:    assert (MaxTrans    > 0) else $fatal("Number of transactions must be at least 1!");
    end
  `endif
  // pragma translate_on
endmodule

// interface wrap
`include "axi/assign.svh"
`include "axi/typedef.svh"

module axi_lite_mux_intf #(
  parameter int unsigned AddrWidth     = 32'd0,
  parameter int unsigned DataWidth     = 32'd0,
  parameter int unsigned NumSbrPorts   = 32'd0, // Number of subordinate ports
  // Maximum number of outstanding transactions per write
  parameter int unsigned MaxTrans      = 32'd0,
  // if enabled, this multiplexer is purely combinatorial
  parameter bit          FallThrough   = 1'b0,
  // add spill register on write manager ports, adds a cycle latency on write channels
  parameter bit          SpillAw       = 1'b1,
  parameter bit          SpillW        = 1'b0,
  parameter bit          SpillB        = 1'b0,
  // add spill register on read manager ports, adds a cycle latency on read channels
  parameter bit          SpillAr       = 1'b1,
  parameter bit          SpillR        = 1'b0
) (
  input  logic    clk_i,                // Clock
  input  logic    rst_ni,               // Asynchronous reset active low
  input  logic    test_i,               // Testmode enable
  AXI_LITE.Subordinate  sbr [NumSbrPorts-1:0], // subordinate ports
  AXI_LITE.Manager mgr                   // manager port
);

  typedef logic [AddrWidth-1:0]   addr_t;
  typedef logic [DataWidth-1:0]   data_t;
  typedef logic [DataWidth/8-1:0] strb_t;
  // channels typedef
  `AXI_LITE_TYPEDEF_AW_CHAN_T(aw_chan_t, addr_t)
  `AXI_LITE_TYPEDEF_W_CHAN_T(w_chan_t, data_t, strb_t)
  `AXI_LITE_TYPEDEF_B_CHAN_T(b_chan_t)
  `AXI_LITE_TYPEDEF_AR_CHAN_T(ar_chan_t, addr_t)
  `AXI_LITE_TYPEDEF_R_CHAN_T(r_chan_t, data_t)
  `AXI_LITE_TYPEDEF_REQ_T(axi_lite_req_t, aw_chan_t, w_chan_t, ar_chan_t)
  `AXI_LITE_TYPEDEF_RSP_T(axi_lite_rsp_t, b_chan_t, r_chan_t)

  axi_lite_req_t     [NumSbrPorts-1:0] sbr_reqs;
  axi_lite_rsp_t     [NumSbrPorts-1:0] sbr_rsps;
  axi_lite_req_t                       mgr_req;
  axi_lite_rsp_t                       mgr_rsp;

  for (genvar i = 0; i < NumSbrPorts; i++) begin : gen_assign_sbr_ports
    `AXI_LITE_ASSIGN_TO_REQ(sbr_reqs[i], sbr[i])
    `AXI_LITE_ASSIGN_FROM_RSP(sbr[i], sbr_rsps[i])
  end

  `AXI_LITE_ASSIGN_FROM_REQ(mgr, mgr_req)
  `AXI_LITE_ASSIGN_TO_RSP(mgr_rsp, mgr)

  axi_lite_mux #(
    .aw_chan_t      ( aw_chan_t      ), // AW Channel Type
    .w_chan_t       (  w_chan_t      ), //  W Channel Type
    .b_chan_t       (  b_chan_t      ), //  B Channel Type
    .ar_chan_t      ( ar_chan_t      ), // AR Channel Type
    .r_chan_t       (  r_chan_t      ), //  R Channel Type
    .axi_lite_req_t ( axi_lite_req_t ),
    .axi_lite_rsp_t ( axi_lite_rsp_t ),
    .NumSbrPorts    ( NumSbrPorts    ), // Number of subordinate ports
    .MaxTrans       ( MaxTrans       ),
    .FallThrough    ( FallThrough    ),
    .SpillAw        ( SpillAw        ),
    .SpillW         ( SpillW         ),
    .SpillB         ( SpillB         ),
    .SpillAr        ( SpillAr        ),
    .SpillR         ( SpillR         )
  ) i_axi_mux (
    .clk_i,  // Clock
    .rst_ni, // Asynchronous reset active low
    .test_i, // Test Mode enable
    .sbr_reqs_i ( sbr_reqs ),
    .sbr_rsps_o ( sbr_rsps ),
    .mgr_req_o  ( mgr_req  ),
    .mgr_rsp_i  ( mgr_rsp  )
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
