// Copyright (c) 2019 ETH Zurich, University of Bologna
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

// AXI Multiplexer: This module multiplexes the AXI4 subordinate ports down to one manager port.
// The AXI IDs from the subordinate ports get extended with the respective subordinate port index.
// The extension width can be calculated with `$clog2(NumSbrPorts)`. This means the AXI
// ID for the manager port has to be this `$clog2(NumSbrPorts)` wider than the ID for the
// subordinate ports.
// Responses are switched based on these bits. For example, with 4 subordinate ports
// a response with ID `6'b100110` will be forwarded to subordinate port 2 (`2'b10`).

// register macros
`include "common_cells/assertions.svh"
`include "common_cells/registers.svh"

module axi_mux #(
  // AXI parameter and channel types
  parameter int unsigned SbrIDWidth         = 32'd0, // AXI ID width, subordinate ports
  parameter type         sbr_aw_chan_t      = logic, // AW Channel Type, subordinate ports
  parameter type         mgr_aw_chan_t      = logic, // AW Channel Type, manager port
  parameter type         w_chan_t           = logic, //  W Channel Type, all ports
  parameter type         sbr_b_chan_t       = logic, //  B Channel Type, subordinate ports
  parameter type         mgr_b_chan_t       = logic, //  B Channel Type, manager port
  parameter type         sbr_ar_chan_t      = logic, // AR Channel Type, subordinate ports
  parameter type         mgr_ar_chan_t      = logic, // AR Channel Type, manager port
  parameter type         sbr_r_chan_t       = logic, //  R Channel Type, subordinate ports
  parameter type         mgr_r_chan_t       = logic, //  R Channel Type, manager port
  parameter type         sbr_port_axi_req_t = logic, // Subordinate port request type
  parameter type         sbr_port_axi_rsp_t = logic, // Subordinate port response type
  parameter type         mgr_port_axi_req_t = logic, // Manager ports request type
  parameter type         mgr_port_axi_rsp_t = logic, // Manager ports response type
  parameter int unsigned NumSbrPorts        = 32'd0, // Number of subordinate ports
  // Maximum number of outstanding transactions per write
  parameter int unsigned MaxWTrans          = 32'd8,
  // If enabled, this multiplexer is purely combinatorial
  parameter bit          FallThrough        = 1'b0,
  // add spill register on write manager ports, adds a cycle latency on write channels
  parameter bit          SpillAw            = 1'b1,
  parameter bit          SpillW             = 1'b0,
  parameter bit          SpillB             = 1'b0,
  // add spill register on read manager ports, adds a cycle latency on read channels
  parameter bit          SpillAr            = 1'b1,
  parameter bit          SpillR             = 1'b0
) (
  input  logic                                clk_i,    // Clock
  input  logic                                rst_ni,   // Asynchronous reset active low
  input  logic                                test_i,   // Test Mode enable
  // subordinate ports (AXI inputs), connect manager modules here
  input  sbr_port_axi_req_t [NumSbrPorts-1:0] sbr_ports_req_i,
  output sbr_port_axi_rsp_t [NumSbrPorts-1:0] sbr_ports_rsp_o,
  // manager port (AXI outputs), connect subordinate modules here
  output mgr_port_axi_req_t                   mgr_port_req_o,
  input  mgr_port_axi_rsp_t                   mgr_port_rsp_i
);

  localparam int unsigned MgrIdxBits = $clog2(NumSbrPorts);
  localparam int unsigned MgrIDWidth = SbrIDWidth + MgrIdxBits;

  // pass through if only one subordinate port
  if (NumSbrPorts == 32'h1) begin : gen_no_mux
    spill_register #(
      .T       ( mgr_aw_chan_t ),
      .Bypass  ( ~SpillAw      )
    ) i_aw_spill_reg (
      .clk_i   ( clk_i                    ),
      .rst_ni  ( rst_ni                   ),
      .valid_i ( sbr_ports_req_i[0].aw_valid   ),
      .ready_o ( sbr_ports_rsp_o[0].aw_ready   ),
      .data_i  ( sbr_ports_req_i[0].aw         ),
      .valid_o ( mgr_port_req_o.aw_valid       ),
      .ready_i ( mgr_port_rsp_i.aw_ready       ),
      .data_o  ( mgr_port_req_o.aw             )
    );
    spill_register #(
      .T       ( w_chan_t ),
      .Bypass  ( ~SpillW  )
    ) i_w_spill_reg (
      .clk_i   ( clk_i                   ),
      .rst_ni  ( rst_ni                  ),
      .valid_i ( sbr_ports_req_i[0].w_valid   ),
      .ready_o ( sbr_ports_rsp_o[0].w_ready   ),
      .data_i  ( sbr_ports_req_i[0].w         ),
      .valid_o ( mgr_port_req_o.w_valid       ),
      .ready_i ( mgr_port_rsp_i.w_ready       ),
      .data_o  ( mgr_port_req_o.w             )
    );
    spill_register #(
      .T       ( mgr_b_chan_t ),
      .Bypass  ( ~SpillB      )
    ) i_b_spill_reg (
      .clk_i   ( clk_i                  ),
      .rst_ni  ( rst_ni                 ),
      .valid_i ( mgr_port_rsp_i.b_valid      ),
      .ready_o ( mgr_port_req_o.b_ready      ),
      .data_i  ( mgr_port_rsp_i.b            ),
      .valid_o ( sbr_ports_rsp_o[0].b_valid  ),
      .ready_i ( sbr_ports_req_i[0].b_ready  ),
      .data_o  ( sbr_ports_rsp_o[0].b        )
    );
    spill_register #(
      .T       ( mgr_ar_chan_t ),
      .Bypass  ( ~SpillAr      )
    ) i_ar_spill_reg (
      .clk_i   ( clk_i                    ),
      .rst_ni  ( rst_ni                   ),
      .valid_i ( sbr_ports_req_i[0].ar_valid   ),
      .ready_o ( sbr_ports_rsp_o[0].ar_ready   ),
      .data_i  ( sbr_ports_req_i[0].ar         ),
      .valid_o ( mgr_port_req_o.ar_valid       ),
      .ready_i ( mgr_port_rsp_i.ar_ready       ),
      .data_o  ( mgr_port_req_o.ar             )
    );
    spill_register #(
      .T       ( mgr_r_chan_t ),
      .Bypass  ( ~SpillR      )
    ) i_r_spill_reg (
      .clk_i   ( clk_i                  ),
      .rst_ni  ( rst_ni                 ),
      .valid_i ( mgr_port_rsp_i.r_valid      ),
      .ready_o ( mgr_port_req_o.r_ready      ),
      .data_i  ( mgr_port_rsp_i.r            ),
      .valid_o ( sbr_ports_rsp_o[0].r_valid  ),
      .ready_i ( sbr_ports_req_i[0].r_ready  ),
      .data_o  ( sbr_ports_rsp_o[0].r        )
    );
// Validate parameters.
// pragma translate_off
    `ASSERT_INIT(CorrectIdWidthSbrAw, $bits(sbr_ports_req_i[0].aw.id) == SbrIDWidth)
    `ASSERT_INIT(CorrectIdWidthSbrB, $bits(sbr_ports_rsp_o[0].b.id) == SbrIDWidth)
    `ASSERT_INIT(CorrectIdWidthSbrAr, $bits(sbr_ports_req_i[0].ar.id) == SbrIDWidth)
    `ASSERT_INIT(CorrectIdWidthSbrR, $bits(sbr_ports_rsp_o[0].r.id) == SbrIDWidth)
    `ASSERT_INIT(CorrectIdWidthMgrAw, $bits(mgr_port_req_o.aw.id) == SbrIDWidth)
    `ASSERT_INIT(CorrectIdWidthMgrB, $bits(mgr_port_rsp_i.b.id) == SbrIDWidth)
    `ASSERT_INIT(CorrectIdWidthMgrAr, $bits(mgr_port_req_o.ar.id) == SbrIDWidth)
    `ASSERT_INIT(CorrectIdWidthMgrR, $bits(mgr_port_rsp_i.r.id) == SbrIDWidth)
// pragma translate_on

  // other non degenerate cases
  end else begin : gen_mux

    typedef logic [MgrIdxBits-1:0] switch_id_t;

    // AXI channels between the ID prepend unit and the rest of the multiplexer
    mgr_aw_chan_t [NumSbrPorts-1:0] sbr_aw_chans;
    logic         [NumSbrPorts-1:0] sbr_aw_valids, sbr_aw_readies;
    w_chan_t      [NumSbrPorts-1:0] sbr_w_chans;
    logic         [NumSbrPorts-1:0] sbr_w_valids,  sbr_w_readies;
    mgr_b_chan_t  [NumSbrPorts-1:0] sbr_b_chans;
    logic         [NumSbrPorts-1:0] sbr_b_valids,  sbr_b_readies;
    mgr_ar_chan_t [NumSbrPorts-1:0] sbr_ar_chans;
    logic         [NumSbrPorts-1:0] sbr_ar_valids, sbr_ar_readies;
    mgr_r_chan_t  [NumSbrPorts-1:0] sbr_r_chans;
    logic         [NumSbrPorts-1:0] sbr_r_valids,  sbr_r_readies;

    // These signals are all ID prepended
    // AW channel
    mgr_aw_chan_t   mgr_aw_chan;
    logic           mgr_aw_valid, mgr_aw_ready;

    // AW manager handshake internal, so that we are able to stall, if w_fifo is full
    logic           aw_valid,     aw_ready;

    // FF to lock the AW valid signal, when a new arbitration decision is made the decision
    // gets pushed into the W FIFO, when it now stalls prevent subsequent pushing
    // This FF removes AW to W dependency
    logic           lock_aw_valid_d, lock_aw_valid_q;
    logic           load_aw_lock;

    // signals for the FIFO that holds the last switching decision of the AW channel
    logic           w_fifo_full,  w_fifo_empty;
    logic           w_fifo_push,  w_fifo_pop;
    switch_id_t     w_fifo_data;

    // W channel spill reg
    w_chan_t        mgr_w_chan;
    logic           mgr_w_valid,  mgr_w_ready;

    // manager ID in the b_id
    switch_id_t     switch_b_id;

    // B channel spill reg
    mgr_b_chan_t    mgr_b_chan;
    logic           mgr_b_valid;

    // AR channel for when spill is enabled
    mgr_ar_chan_t   mgr_ar_chan;
    logic           ar_valid,     ar_ready;

    // manager ID in the r_id
    switch_id_t     switch_r_id;

    // R channel spill reg
    mgr_r_chan_t    mgr_r_chan;
    logic           mgr_r_valid;

    //--------------------------------------
    // ID prepend for all subordinate ports
    //--------------------------------------
    for (genvar i = 0; i < NumSbrPorts; i++) begin : gen_id_prepend
      axi_id_prepend #(
        .NumBus         ( 32'd1               ), // one AXI bus per subordinate port
        .IdWidthSbrPort( SbrIDWidth          ),
        .IdWidthMgrPort( MgrIDWidth          ),
        .sbr_aw_chan_t ( sbr_aw_chan_t       ),
        .sbr_w_chan_t  ( w_chan_t            ),
        .sbr_b_chan_t  ( sbr_b_chan_t        ),
        .sbr_ar_chan_t ( sbr_ar_chan_t       ),
        .sbr_r_chan_t  ( sbr_r_chan_t        ),
        .mgr_aw_chan_t ( mgr_aw_chan_t       ),
        .mgr_w_chan_t  ( w_chan_t            ),
        .mgr_b_chan_t  ( mgr_b_chan_t        ),
        .mgr_ar_chan_t ( mgr_ar_chan_t       ),
        .mgr_r_chan_t  ( mgr_r_chan_t        )
      ) i_id_prepend (
        .pre_id_i         ( switch_id_t'(i)        ),
        .sbr_aw_chans_i   ( sbr_ports_req_i[i].aw       ),
        .sbr_aw_valids_i  ( sbr_ports_req_i[i].aw_valid ),
        .sbr_aw_readies_o ( sbr_ports_rsp_o[i].aw_ready ),
        .sbr_w_chans_i    ( sbr_ports_req_i[i].w        ),
        .sbr_w_valids_i   ( sbr_ports_req_i[i].w_valid  ),
        .sbr_w_readies_o  ( sbr_ports_rsp_o[i].w_ready  ),
        .sbr_b_chans_o    ( sbr_ports_rsp_o[i].b        ),
        .sbr_b_valids_o   ( sbr_ports_rsp_o[i].b_valid  ),
        .sbr_b_readies_i  ( sbr_ports_req_i[i].b_ready  ),
        .sbr_ar_chans_i   ( sbr_ports_req_i[i].ar       ),
        .sbr_ar_valids_i  ( sbr_ports_req_i[i].ar_valid ),
        .sbr_ar_readies_o ( sbr_ports_rsp_o[i].ar_ready ),
        .sbr_r_chans_o    ( sbr_ports_rsp_o[i].r        ),
        .sbr_r_valids_o   ( sbr_ports_rsp_o[i].r_valid  ),
        .sbr_r_readies_i  ( sbr_ports_req_i[i].r_ready  ),
        .mgr_aw_chans_o   ( sbr_aw_chans[i]        ),
        .mgr_aw_valids_o  ( sbr_aw_valids[i]       ),
        .mgr_aw_readies_i ( sbr_aw_readies[i]      ),
        .mgr_w_chans_o    ( sbr_w_chans[i]         ),
        .mgr_w_valids_o   ( sbr_w_valids[i]        ),
        .mgr_w_readies_i  ( sbr_w_readies[i]       ),
        .mgr_b_chans_i    ( sbr_b_chans[i]         ),
        .mgr_b_valids_i   ( sbr_b_valids[i]        ),
        .mgr_b_readies_o  ( sbr_b_readies[i]       ),
        .mgr_ar_chans_o   ( sbr_ar_chans[i]        ),
        .mgr_ar_valids_o  ( sbr_ar_valids[i]       ),
        .mgr_ar_readies_i ( sbr_ar_readies[i]      ),
        .mgr_r_chans_i    ( sbr_r_chans[i]         ),
        .mgr_r_valids_i   ( sbr_r_valids[i]        ),
        .mgr_r_readies_o  ( sbr_r_readies[i]       )
      );
    end

    //--------------------------------------
    // AW Channel
    //--------------------------------------
    rr_arb_tree #(
      .NumIn    ( NumSbrPorts   ),
      .DataType ( mgr_aw_chan_t ),
      .AxiVldRdy( 1'b1          ),
      .LockIn   ( 1'b1          )
    ) i_aw_arbiter (
      .clk_i  ( clk_i           ),
      .rst_ni ( rst_ni          ),
      .flush_i( 1'b0            ),
      .rr_i   ( '0              ),
      .req_i  ( sbr_aw_valids   ),
      .gnt_o  ( sbr_aw_readies  ),
      .data_i ( sbr_aw_chans    ),
      .gnt_i  ( aw_ready        ),
      .req_o  ( aw_valid        ),
      .data_o ( mgr_aw_chan     ),
      .idx_o  (                 )
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
      .DEPTH        ( MaxWTrans   ),
      .dtype        ( switch_id_t )
    ) i_w_fifo (
      .clk_i     ( clk_i                                  ),
      .rst_ni    ( rst_ni                                 ),
      .flush_i   ( 1'b0                                   ),
      .testmode_i( test_i                                 ),
      .full_o    ( w_fifo_full                            ),
      .empty_o   ( w_fifo_empty                           ),
      .usage_o   (                                        ),
      .data_i    ( mgr_aw_chan.id[SbrIDWidth+:MgrIdxBits] ),
      .push_i    ( w_fifo_push                            ),
      .data_o    ( w_fifo_data                            ),
      .pop_i     ( w_fifo_pop                             )
    );

    spill_register #(
      .T       ( mgr_aw_chan_t ),
      .Bypass  ( ~SpillAw      ) // Param indicated that we want a spill reg
    ) i_aw_spill_reg (
      .clk_i   ( clk_i               ),
      .rst_ni  ( rst_ni              ),
      .valid_i ( mgr_aw_valid        ),
      .ready_o ( mgr_aw_ready        ),
      .data_i  ( mgr_aw_chan         ),
      .valid_o ( mgr_port_req_o.aw_valid  ),
      .ready_i ( mgr_port_rsp_i.aw_ready ),
      .data_o  ( mgr_port_req_o.aw        )
    );

    //--------------------------------------
    // W Channel
    //--------------------------------------
    // multiplexer
    assign mgr_w_chan = sbr_w_chans[w_fifo_data];
    always_comb begin
      // default assignments
      mgr_w_valid   = 1'b0;
      sbr_w_readies = '0;
      w_fifo_pop    = 1'b0;
      // control
      if (!w_fifo_empty) begin
        // connect the handshake
        mgr_w_valid                = sbr_w_valids[w_fifo_data];
        sbr_w_readies[w_fifo_data] = mgr_w_ready;
        // pop FIFO on a last transaction
        w_fifo_pop = sbr_w_valids[w_fifo_data] & mgr_w_ready & mgr_w_chan.last;
      end
    end

    spill_register #(
      .T       ( w_chan_t ),
      .Bypass  ( ~SpillW  )
    ) i_w_spill_reg (
      .clk_i   ( clk_i              ),
      .rst_ni  ( rst_ni             ),
      .valid_i ( mgr_w_valid        ),
      .ready_o ( mgr_w_ready        ),
      .data_i  ( mgr_w_chan         ),
      .valid_o ( mgr_port_req_o.w_valid  ),
      .ready_i ( mgr_port_rsp_i.w_ready  ),
      .data_o  ( mgr_port_req_o.w        )
    );

    //--------------------------------------
    // B Channel
    //--------------------------------------
    // replicate B channels
    assign sbr_b_chans  = {NumSbrPorts{mgr_b_chan}};
    // control B channel handshake
    assign switch_b_id  = mgr_b_chan.id[SbrIDWidth+:MgrIdxBits];
    assign sbr_b_valids = (mgr_b_valid) ? (1 << switch_b_id) : '0;

    spill_register #(
      .T       ( mgr_b_chan_t ),
      .Bypass  ( ~SpillB      )
    ) i_b_spill_reg (
      .clk_i   ( clk_i                      ),
      .rst_ni  ( rst_ni                     ),
      .valid_i ( mgr_port_rsp_i.b_valid          ),
      .ready_o ( mgr_port_req_o.b_ready          ),
      .data_i  ( mgr_port_rsp_i.b                ),
      .valid_o ( mgr_b_valid                ),
      .ready_i ( sbr_b_readies[switch_b_id] ),
      .data_o  ( mgr_b_chan                 )
    );

    //--------------------------------------
    // AR Channel
    //--------------------------------------
    rr_arb_tree #(
      .NumIn    ( NumSbrPorts   ),
      .DataType ( mgr_ar_chan_t ),
      .AxiVldRdy( 1'b1          ),
      .LockIn   ( 1'b1          )
    ) i_ar_arbiter (
      .clk_i  ( clk_i           ),
      .rst_ni ( rst_ni          ),
      .flush_i( 1'b0            ),
      .rr_i   ( '0              ),
      .req_i  ( sbr_ar_valids   ),
      .gnt_o  ( sbr_ar_readies  ),
      .data_i ( sbr_ar_chans    ),
      .gnt_i  ( ar_ready        ),
      .req_o  ( ar_valid        ),
      .data_o ( mgr_ar_chan     ),
      .idx_o  (                 )
    );

    spill_register #(
      .T       ( mgr_ar_chan_t ),
      .Bypass  ( ~SpillAr      )
    ) i_ar_spill_reg (
      .clk_i   ( clk_i               ),
      .rst_ni  ( rst_ni              ),
      .valid_i ( ar_valid            ),
      .ready_o ( ar_ready            ),
      .data_i  ( mgr_ar_chan         ),
      .valid_o ( mgr_port_req_o.ar_valid  ),
      .ready_i ( mgr_port_rsp_i.ar_ready  ),
      .data_o  ( mgr_port_req_o.ar        )
    );

    //--------------------------------------
    // R Channel
    //--------------------------------------
    // replicate R channels
    assign sbr_r_chans  = {NumSbrPorts{mgr_r_chan}};
    // R channel handshake control
    assign switch_r_id  = mgr_r_chan.id[SbrIDWidth+:MgrIdxBits];
    assign sbr_r_valids = (mgr_r_valid) ? (1 << switch_r_id) : '0;

    spill_register #(
      .T       ( mgr_r_chan_t ),
      .Bypass  ( ~SpillR      )
    ) i_r_spill_reg (
      .clk_i   ( clk_i                      ),
      .rst_ni  ( rst_ni                     ),
      .valid_i ( mgr_port_rsp_i.r_valid          ),
      .ready_o ( mgr_port_req_o.r_ready          ),
      .data_i  ( mgr_port_rsp_i.r                ),
      .valid_o ( mgr_r_valid                ),
      .ready_i ( sbr_r_readies[switch_r_id] ),
      .data_o  ( mgr_r_chan                 )
    );
  end

// pragma translate_off
`ifndef VERILATOR
  initial begin
    assert (SbrIDWidth > 0) else $fatal(1, "AXI ID width of subordinate ports must be non-zero!");
    assert (NumSbrPorts > 0) else $fatal(1, "Number of subordinate ports must be non-zero!");
    assert (MaxWTrans > 0)
      else $fatal(1, "Maximum number of outstanding writes must be non-zero!");
    assert (MgrIDWidth >= SbrIDWidth + $clog2(NumSbrPorts))
      else $fatal(1, "AXI ID width of manager ports must be wide enough to identify subordinate ports!");
    // Assert ID widths (one subordinate is sufficient since they all have the same type).
    assert ($unsigned($bits(sbr_ports_req_i[0].aw.id)) == SbrIDWidth)
      else $fatal(1, "ID width of AW channel of subordinate ports does not match parameter!");
    assert ($unsigned($bits(sbr_ports_req_i[0].ar.id)) == SbrIDWidth)
      else $fatal(1, "ID width of AR channel of subordinate ports does not match parameter!");
    assert ($unsigned($bits(sbr_ports_rsp_o[0].b.id)) == SbrIDWidth)
      else $fatal(1, "ID width of B channel of subordinate ports does not match parameter!");
    assert ($unsigned($bits(sbr_ports_rsp_o[0].r.id)) == SbrIDWidth)
      else $fatal(1, "ID width of R channel of subordinate ports does not match parameter!");
    assert ($unsigned($bits(mgr_port_req_o.aw.id)) == MgrIDWidth)
      else $fatal(1, "ID width of AW channel of manager port is wrong!");
    assert ($unsigned($bits(mgr_port_req_o.ar.id)) == MgrIDWidth)
      else $fatal(1, "ID width of AR channel of manager port is wrong!");
    assert ($unsigned($bits(mgr_port_rsp_i.b.id)) == MgrIDWidth)
      else $fatal(1, "ID width of B channel of manager port is wrong!");
    assert ($unsigned($bits(mgr_port_rsp_i.r.id)) == MgrIDWidth)
      else $fatal(1, "ID width of R channel of manager port is wrong!");
  end
`endif
// pragma translate_on
endmodule

// interface wrap
`include "axi/assign.svh"
`include "axi/typedef.svh"
module axi_mux_intf #(
  parameter int unsigned SBR_AXI_ID_WIDTH = 32'd0, // Synopsys DC requires default value for params
  parameter int unsigned MGR_AXI_ID_WIDTH = 32'd0,
  parameter int unsigned AXI_ADDR_WIDTH   = 32'd0,
  parameter int unsigned AXI_DATA_WIDTH   = 32'd0,
  parameter int unsigned AXI_USER_WIDTH   = 32'd0,
  parameter int unsigned NO_SBR_PORTS     = 32'd0, // Number of subordinate ports
  // Maximum number of outstanding transactions per write
  parameter int unsigned MAX_W_TRANS      = 32'd8,
  // if enabled, this multiplexer is purely combinatorial
  parameter bit          FALL_THROUGH     = 1'b0,
  // add spill register on write manager ports, adds a cycle latency on write channels
  parameter bit          SPILL_AW         = 1'b1,
  parameter bit          SPILL_W          = 1'b0,
  parameter bit          SPILL_B          = 1'b0,
  // add spill register on read manager ports, adds a cycle latency on read channels
  parameter bit          SPILL_AR         = 1'b1,
  parameter bit          SPILL_R          = 1'b0
) (
  input  logic   clk_i,                  // Clock
  input  logic   rst_ni,                 // Asynchronous reset active low
  input  logic   test_i,                 // Testmode enable
  AXI_BUS.Subordinate  sbr [NO_SBR_PORTS-1:0], // subordinate ports
  AXI_BUS.Manager mgr                     // manager port
);

  typedef logic [SBR_AXI_ID_WIDTH-1:0] sbr_id_t;
  typedef logic [MGR_AXI_ID_WIDTH-1:0] mgr_id_t;
  typedef logic [AXI_ADDR_WIDTH -1:0]  addr_t;
  typedef logic [AXI_DATA_WIDTH-1:0]   data_t;
  typedef logic [AXI_DATA_WIDTH/8-1:0] strb_t;
  typedef logic [AXI_USER_WIDTH-1:0]   user_t;
  // channels typedef
  `AXI_TYPEDEF_AW_CHAN_T(sbr_aw_chan_t, addr_t, sbr_id_t, user_t)
  `AXI_TYPEDEF_AW_CHAN_T(mgr_aw_chan_t, addr_t, mgr_id_t, user_t)

  `AXI_TYPEDEF_W_CHAN_T(w_chan_t, data_t, strb_t, user_t)

  `AXI_TYPEDEF_B_CHAN_T(sbr_b_chan_t, sbr_id_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T(mgr_b_chan_t, mgr_id_t, user_t)

  `AXI_TYPEDEF_AR_CHAN_T(sbr_ar_chan_t, addr_t, sbr_id_t, user_t)
  `AXI_TYPEDEF_AR_CHAN_T(mgr_ar_chan_t, addr_t, mgr_id_t, user_t)

  `AXI_TYPEDEF_R_CHAN_T(sbr_r_chan_t, data_t, sbr_id_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(mgr_r_chan_t, data_t, mgr_id_t, user_t)

  `AXI_TYPEDEF_REQ_T(sbr_port_axi_req_t, sbr_aw_chan_t, w_chan_t, sbr_ar_chan_t)
  `AXI_TYPEDEF_RSP_T(sbr_port_axi_rsp_t, sbr_b_chan_t, sbr_r_chan_t)

  `AXI_TYPEDEF_REQ_T(mgr_port_axi_req_t, mgr_aw_chan_t, w_chan_t, mgr_ar_chan_t)
  `AXI_TYPEDEF_RSP_T(mgr_port_axi_rsp_t, mgr_b_chan_t, mgr_r_chan_t)

  sbr_port_axi_req_t [NO_SBR_PORTS-1:0] sbr_reqs;
  sbr_port_axi_rsp_t [NO_SBR_PORTS-1:0] sbr_rsps;
  mgr_port_axi_req_t                    mgr_req;
  mgr_port_axi_rsp_t                    mgr_rsp;

  for (genvar i = 0; i < NO_SBR_PORTS; i++) begin : gen_assign_sbr_ports
    `AXI_ASSIGN_TO_REQ(sbr_reqs[i], sbr[i])
    `AXI_ASSIGN_FROM_RSP(sbr[i], sbr_rsps[i])
  end

  `AXI_ASSIGN_FROM_REQ(mgr, mgr_req)
  `AXI_ASSIGN_TO_RSP(mgr_rsp, mgr)

  axi_mux #(
    .SbrIDWidth         ( SBR_AXI_ID_WIDTH   ),
    .sbr_aw_chan_t      ( sbr_aw_chan_t      ), // AW Channel Type, subordinate ports
    .mgr_aw_chan_t      ( mgr_aw_chan_t      ), // AW Channel Type, manager port
    .w_chan_t           ( w_chan_t           ), //  W Channel Type, all ports
    .sbr_b_chan_t       ( sbr_b_chan_t       ), //  B Channel Type, subordinate ports
    .mgr_b_chan_t       ( mgr_b_chan_t       ), //  B Channel Type, manager port
    .sbr_ar_chan_t      ( sbr_ar_chan_t      ), // AR Channel Type, subordinate ports
    .mgr_ar_chan_t      ( mgr_ar_chan_t      ), // AR Channel Type, manager port
    .sbr_r_chan_t       ( sbr_r_chan_t       ), //  R Channel Type, subordinate ports
    .mgr_r_chan_t       ( mgr_r_chan_t       ), //  R Channel Type, manager port
    .sbr_port_axi_req_t ( sbr_port_axi_req_t ),
    .sbr_port_axi_rsp_t ( sbr_port_axi_rsp_t ),
    .mgr_port_axi_req_t ( mgr_port_axi_req_t ),
    .mgr_port_axi_rsp_t ( mgr_port_axi_rsp_t ),
    .NumSbrPorts        ( NO_SBR_PORTS       ), // Number of subordinate ports
    .MaxWTrans          ( MAX_W_TRANS        ),
    .FallThrough        ( FALL_THROUGH       ),
    .SpillAw            ( SPILL_AW           ),
    .SpillW             ( SPILL_W            ),
    .SpillB             ( SPILL_B            ),
    .SpillAr            ( SPILL_AR           ),
    .SpillR             ( SPILL_R            )
  ) i_axi_mux (
    .clk_i      ( clk_i    ), // Clock
    .rst_ni     ( rst_ni   ), // Asynchronous reset active low
    .test_i     ( test_i   ), // Test Mode enable
    .sbr_ports_req_i ( sbr_reqs ),
    .sbr_ports_rsp_o ( sbr_rsps ),
    .mgr_port_req_o  ( mgr_req  ),
    .mgr_port_rsp_i  ( mgr_rsp  )
  );
endmodule
