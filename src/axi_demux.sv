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

// AXI Demultiplexer: This module splits an AXI bus from one slave port to multiple master ports.
// - The AW and AR channels each have a `_select_i` to determine the master port to which
//   they are sent. The selection signal has to be constant during ax_valid.
// - Multiple transactions can be in flight to different mast ports if
//   they have different IDs. The module will stall the Ax if it goes to a different
//   master port where other transactions with the same ID are still in flight.
//   This module will reorder read responses from different master ports, when the AXI id's are
//   different!
// - In accordance with the AXI spec, this module can reorder and interleave read responses from
//   different master ports when the IDs of the responses differ.

// register macros
`include "common_cells/registers.svh"

module axi_demux #(
  parameter int unsigned AxiIdWidth     = 1,     // ID Width
  parameter type         aw_chan_t      = logic, // AW Channel Type
  parameter type         w_chan_t       = logic, //  W Channel Type
  parameter type         b_chan_t       = logic, //  B Channel Type
  parameter type         ar_chan_t      = logic, // AR Channel Type
  parameter type         r_chan_t       = logic, //  R Channel Type
  // Number of Master ports that can be connected
  parameter int unsigned NoMstPorts     = 3,
  // Maximum number of outstanding transactions, determines the depth of the W FIFO
  parameter int unsigned MaxTrans       = 8,
  // the lower bits of the axi id, that get used for stalling on 'same' id to a different mst port
  // the number of couters that get instatntiated is 2**`AxiLookBits`
  parameter int unsigned AxiLookBits    = 3,
  // If enabled, this demultiplexer is purely combinatorial
  parameter bit          FallThrough    = 1'b0,
  // add spill register in AW path before the lookup in ID counter
  parameter bit          SpillAw        = 1'b1,
  parameter bit          SpillW         = 1'b0,
  parameter bit          SpillB         = 1'b0,
  // add spill register in AR path before the lookup in ID counter
  parameter bit          SpillAr        = 1'b1,
  parameter bit          SpillR         = 1'b0,
  // Dependent parameters, DO NOT OVERRIDE!
  parameter type         select_t       = logic [$clog2(NoMstPorts)-1:0] // MST port select type
) (
  input  logic clk_i,   // Clock
  input  logic rst_ni,  // Asynchronous reset active low
  input  logic test_i,  // Testmode enable
  // slave port
  // AW channel
  input  aw_chan_t                  slv_aw_chan_i,
  input  select_t                   slv_aw_select_i, // must be stable while slv_aw_valid_i
  input  logic                      slv_aw_valid_i,
  output logic                      slv_aw_ready_o,
  //  W channel
  input  w_chan_t                   slv_w_chan_i,
  input  logic                      slv_w_valid_i,
  output logic                      slv_w_ready_o,
  //  B channel
  output b_chan_t                   slv_b_chan_o,
  output logic                      slv_b_valid_o,
  input  logic                      slv_b_ready_i,
  // AR channel
  input  ar_chan_t                  slv_ar_chan_i,
  input  select_t                   slv_ar_select_i, // must be stable while slv_ar_valid_i
  input  logic                      slv_ar_valid_i,
  output logic                      slv_ar_ready_o,
  //  R channel
  output r_chan_t                   slv_r_chan_o,
  output logic                      slv_r_valid_o,
  input  logic                      slv_r_ready_i,
  // master ports
  // AW channel
  output aw_chan_t [NoMstPorts-1:0] mst_aw_chans_o,
  output logic     [NoMstPorts-1:0] mst_aw_valids_o,
  input  logic     [NoMstPorts-1:0] mst_aw_readies_i,
  //  W channel
  output w_chan_t  [NoMstPorts-1:0] mst_w_chans_o,
  output logic     [NoMstPorts-1:0] mst_w_valids_o,
  input  logic     [NoMstPorts-1:0] mst_w_readies_i,
  //  B channel
  input  b_chan_t  [NoMstPorts-1:0] mst_b_chans_i,
  input  logic     [NoMstPorts-1:0] mst_b_valids_i,
  output logic     [NoMstPorts-1:0] mst_b_readies_o,
  // AR channel
  output ar_chan_t [NoMstPorts-1:0] mst_ar_chans_o,
  output logic     [NoMstPorts-1:0] mst_ar_valids_o,
  input  logic     [NoMstPorts-1:0] mst_ar_readies_i,
  //  R channel
  input  r_chan_t  [NoMstPorts-1:0] mst_r_chans_i,
  input  logic     [NoMstPorts-1:0] mst_r_valids_i,
  output logic     [NoMstPorts-1:0] mst_r_readies_o
);

  // lies in conjunction with max trans, is the counter width
  localparam int unsigned IdCounterWidth = $clog2(MaxTrans);

  // pass through if only one master port
  if (NoMstPorts == 32'h1) begin : gen_no_demux
    // aw channel
    assign mst_aw_chans_o[0]  = slv_aw_chan_i;
    assign mst_aw_valids_o[0] = slv_aw_valid_i;
    assign slv_aw_ready_o     = mst_aw_readies_i[0];
    // w channel
    assign mst_w_chans_o[0]   = slv_w_chan_i;
    assign mst_w_valids_o[0]  = slv_w_valid_i;
    assign slv_w_ready_o      = mst_w_readies_i[0];
    // b channel
    assign slv_b_chan_o       = mst_b_chans_i[0];
    assign slv_b_valid_o      = mst_b_valids_i[0];
    assign mst_b_readies_o[0] = slv_b_ready_i;
    // ar channel
    assign mst_ar_chans_o[0]  = slv_ar_chan_i;
    assign mst_ar_valids_o[0] = slv_ar_valid_i;
    assign slv_ar_ready_o     = mst_ar_readies_i[0];
    // r channel
    assign slv_r_chan_o       = mst_r_chans_i[0];
    assign slv_r_valid_o      = mst_r_valids_i[0];
    assign mst_r_readies_o[0] = slv_r_ready_i;

  // other non degenerate cases
  end else begin : gen_demux
    //--------------------------------------
    // Typedefs for the Fifo's / Queues
    //--------------------------------------
    typedef logic [AxiIdWidth-1:0] axi_id_t;
    typedef struct packed {
      aw_chan_t aw_chan;
      select_t  aw_select;
    } aw_chan_select_t;
    typedef struct packed {
      ar_chan_t ar_chan;
      select_t  ar_select;
    } ar_chan_select_t;

    //--------------------------------------
    //--------------------------------------
    // Signal Declarations
    //--------------------------------------
    //--------------------------------------

    //--------------------------------------
    // Write Transaction
    //--------------------------------------
    // comes from spill register at input
    aw_chan_select_t slv_aw_chan_select;
    logic            slv_aw_valid,       slv_aw_ready;

    // AW ID counter
    select_t         lookup_aw_select;
    logic            aw_select_occupied, aw_id_cnt_full;
    logic            aw_push;
    // Upon an ATOP load, inject IDs from the AW into the AR channel
    logic            atop_inject;

    // W FIFO: stores the decision to which master W beats should go
    logic            w_fifo_pop;
    logic            w_fifo_full,        w_fifo_empty;
    select_t         w_select;

    // Register which locks the AW valid signal
    logic            lock_aw_valid_d,    lock_aw_valid_q, load_aw_lock;
    logic            aw_valid,           aw_ready;

    // W channel from spill reg
    w_chan_t         slv_w_chan;
    logic            slv_w_valid,        slv_w_ready;
    // B channel to spill register
    b_chan_t         slv_b_chan;
    logic            slv_b_valid,        slv_b_ready;

    //--------------------------------------
    // Read Transaction
    //--------------------------------------
    // comes from spill register at input
    ar_chan_select_t slv_ar_chan_select;
    logic            slv_ar_valid,       slv_ar_ready;

    // AR ID counter
    select_t         lookup_ar_select;
    logic            ar_select_occupied, ar_id_cnt_full;
    logic            ar_push;

    // Register which locks the AR valid signel
    logic            lock_ar_valid_d,    lock_ar_valid_q, load_ar_lock;
    logic            ar_valid,           ar_ready;

    // R channel to spill register
    r_chan_t         slv_r_chan;
    logic            slv_r_valid,        slv_r_ready;

    //--------------------------------------
    //--------------------------------------
    // Channel Control
    //--------------------------------------
    //--------------------------------------

    //--------------------------------------
    // AW Channel
    //--------------------------------------
    // spill register at the channel input
    aw_chan_select_t slv_aw_chan_select_in;
    assign slv_aw_chan_select_in.aw_chan   = slv_aw_chan_i;
    assign slv_aw_chan_select_in.aw_select = slv_aw_select_i;
    spill_register #(
      .T       ( aw_chan_select_t      ),
      .Bypass  ( ~SpillAw              ) // because module param indicates if we want a spill reg
    ) i_aw_spill_reg (
      .clk_i   ( clk_i                 ),
      .rst_ni  ( rst_ni                ),
      .valid_i ( slv_aw_valid_i        ),
      .ready_o ( slv_aw_ready_o        ),
      .data_i  ( slv_aw_chan_select_in ),
      .valid_o ( slv_aw_valid          ),
      .ready_i ( slv_aw_ready          ),
      .data_o  ( slv_aw_chan_select    )
    );

    // Control of the AW handshake
    always_comb begin
      // AXI Handshakes
      slv_aw_ready = 1'b0;
      aw_valid     = 1'b0;
      // `lock_aw_valid`, used to be protocol conform as it is not allowed to deassert
      // a valid if there was no corresponding ready. As this process has to be able to inject
      // an AXI ID into the counter of the AR channel on an ATOP, there could be a case where
      // this process waits on `aw_ready` but in the mean time on the AR channel the counter gets
      // full.
      lock_aw_valid_d = lock_aw_valid_q;
      load_aw_lock    = 1'b0;
      // AW ID counter and W FIFO
      aw_push      = 1'b0;
      // ATOP injection into ar counter
      atop_inject  = 1'b0;
      // we had an arbitration decision, the valid is locked, wait for the transaction
      if (lock_aw_valid_q) begin
        aw_valid = 1'b1;
        // transaction
        if (aw_ready) begin
          slv_aw_ready    = 1'b1;
          lock_aw_valid_d = 1'b0;
          load_aw_lock    = 1'b1;
          atop_inject     = slv_aw_chan_select.aw_chan.atop[5]; // inject the ATOP if necessary
        end
      end else begin
        // Process can start handling a transaction if its `i_aw_id_counter` and `w_fifo` have
        // space in them. Further check if we could inject something on the AR channel.
        if (!aw_id_cnt_full && !w_fifo_full && !ar_id_cnt_full) begin
          // there is a valid AW vector make the id lookup and go further, if it passes
          if (slv_aw_valid && (!aw_select_occupied ||
             (slv_aw_chan_select.aw_select == lookup_aw_select))) begin
            // connect the handshake
            aw_valid     = 1'b1;
            // push arbitration to the W FIFO regardless, do not wait for the AW transaction
            aw_push      = 1'b1;
            // on AW transaction
            if (aw_ready) begin
              slv_aw_ready = 1'b1;
              atop_inject  = slv_aw_chan_select.aw_chan.atop[5];
            // no AW transaction this cycle, lock the decision
            end else begin
              lock_aw_valid_d = 1'b1;
              load_aw_lock    = 1'b1;
            end
          end
        end
      end
    end

    // lock the valid signal, as the selection gets pushed into the W FIFO on first assertion,
    // prevent further pushing
    `FFLARN(lock_aw_valid_q, lock_aw_valid_d, load_aw_lock, '0, clk_i, rst_ni)

    axi_demux_id_counters #(
      .AxiIdBits         ( AxiLookBits    ),
      .CounterWidth      ( IdCounterWidth ),
      .mst_port_select_t ( select_t       )
    ) i_aw_id_counter (
      .clk_i                        ( clk_i                                         ),
      .rst_ni                       ( rst_ni                                        ),
      .lookup_axi_id_i              ( slv_aw_chan_select.aw_chan.id[0+:AxiLookBits] ),
      .lookup_mst_select_o          ( lookup_aw_select                              ),
      .lookup_mst_select_occupied_o ( aw_select_occupied                            ),
      .full_o                       ( aw_id_cnt_full                                ),
      .inject_axi_id_i              ( '0                                            ),
      .inject_i                     ( 1'b0                                          ),
      .push_axi_id_i                ( slv_aw_chan_select.aw_chan.id[0+:AxiLookBits] ),
      .push_mst_select_i            ( slv_aw_chan_select.aw_select                  ),
      .push_i                       ( aw_push                                       ),
      .pop_axi_id_i                 ( slv_b_chan.id[0+:AxiLookBits]                 ),
      .pop_i                        ( slv_b_valid & slv_b_ready                     )
    );
    // pop from ID counter on outward transaction

    // FIFO to save W selection
    fifo_v3 #(
      .FALL_THROUGH ( FallThrough ),
      .DEPTH        ( MaxTrans    ),
      .dtype        ( select_t    )
    ) i_w_fifo (
      .clk_i     ( clk_i                        ),
      .rst_ni    ( rst_ni                       ),
      .flush_i   ( 1'b0                         ),
      .testmode_i( test_i                       ),
      .full_o    ( w_fifo_full                  ),
      .empty_o   ( w_fifo_empty                 ),
      .usage_o   (                              ),
      .data_i    ( slv_aw_chan_select.aw_select ),
      .push_i    ( aw_push                      ), // controlled from proc_aw_chan
      .data_o    ( w_select                     ), // where the w beat should go
      .pop_i     ( w_fifo_pop                   )  // controlled from proc_w_chan
    );

    // AW demux
    // replicate AW channels
    assign mst_aw_chans_o  = {NoMstPorts{slv_aw_chan_select.aw_chan}};
    assign mst_aw_valids_o = (aw_valid) ? (1 << slv_aw_chan_select.aw_select)            : '0;
    assign aw_ready        = (aw_valid) ? mst_aw_readies_i[slv_aw_chan_select.aw_select] : 1'b0;

    //--------------------------------------
    //  W Channel
    //--------------------------------------
    spill_register #(
      .T       ( w_chan_t      ),
      .Bypass  ( ~SpillW       )
    ) i_w_spill_reg(
      .clk_i   ( clk_i         ),
      .rst_ni  ( rst_ni        ),
      .valid_i ( slv_w_valid_i ),
      .ready_o ( slv_w_ready_o ),
      .data_i  ( slv_w_chan_i  ),
      .valid_o ( slv_w_valid   ),
      .ready_i ( slv_w_ready   ),
      .data_o  ( slv_w_chan    )
    );

    // AXI W Channel
    // replicate the W channels
    assign mst_w_chans_o = {NoMstPorts{slv_w_chan}};
    always_comb begin
      // AXI handshakes
      mst_w_valids_o = '0;
      slv_w_ready    = 1'b0;
      // FIFO control
      w_fifo_pop     = 1'b0;
      // Control: only do something if we expect some w beats and i_b_decerr_fifo is not full
      if (!w_fifo_empty) begin
        mst_w_valids_o[w_select] = slv_w_valid;
        slv_w_ready              = mst_w_readies_i[w_select];
        // when the last W beat occurs, pop the select FIFO
        w_fifo_pop = slv_w_valid & mst_w_readies_i[w_select] & slv_w_chan.last;
      end
    end

    //--------------------------------------
    //  B Channel
    //--------------------------------------
    // optional spill register
    spill_register #(
      .T       ( b_chan_t      ),
      .Bypass  ( ~SpillB       )
    ) i_b_spill_reg (
      .clk_i   ( clk_i         ),
      .rst_ni  ( rst_ni        ),
      .valid_i ( slv_b_valid   ),
      .ready_o ( slv_b_ready   ),
      .data_i  ( slv_b_chan    ),
      .valid_o ( slv_b_valid_o ),
      .ready_i ( slv_b_ready_i ),
      .data_o  ( slv_b_chan_o  )
    );

    // Arbitration of the different B responses
    rr_arb_tree #(
      .NumIn    ( NoMstPorts    ),
      .DataType ( b_chan_t      ),
      .AxiVldRdy( 1'b1          ),
      .LockIn   ( 1'b1          )
    ) i_b_mux (
      .clk_i  ( clk_i             ),
      .rst_ni ( rst_ni            ),
      .flush_i( 1'b0              ),
      .rr_i   ( '0                ),
      .req_i  ( mst_b_valids_i    ),
      .gnt_o  ( mst_b_readies_o   ),
      .data_i ( mst_b_chans_i     ),
      .gnt_i  ( slv_b_ready       ),
      .req_o  ( slv_b_valid       ),
      .data_o ( slv_b_chan        ),
      .idx_o  (                   )
    );

    //--------------------------------------
    //  AR Channel
    //--------------------------------------
    ar_chan_select_t slv_ar_chan_select_in;
    assign slv_ar_chan_select_in.ar_chan   = slv_ar_chan_i;
    assign slv_ar_chan_select_in.ar_select = slv_ar_select_i;
    spill_register #(
      .T       ( ar_chan_select_t      ),
      .Bypass  ( ~SpillAr              )
    ) i_ar_spill_reg (
      .clk_i   ( clk_i                 ),
      .rst_ni  ( rst_ni                ),
      .valid_i ( slv_ar_valid_i        ),
      .ready_o ( slv_ar_ready_o        ),
      .data_i  ( slv_ar_chan_select_in ),
      .valid_o ( slv_ar_valid          ),
      .ready_i ( slv_ar_ready          ),
      .data_o  ( slv_ar_chan_select    )
    );

    // control of the AR handshake
    always_comb begin
      // AXI Handshakes
      slv_ar_ready    = 1'b0;
      ar_valid        = 1'b0;
      // `lock_ar_valid`: Used to be protocol conform as it is not allowed to deassert `ar_valid`
      // if there was no corresponding `ar_ready`. There is the possibility that an injection
      // of a R response from an `atop` from the AW channel can change the occupied flag of the
      // `i_ar_id_counter`, even if it was previously empty. This FF prevents the deassertion.
      lock_ar_valid_d = lock_ar_valid_q;
      load_ar_lock    = 1'b0;
      // AR id counter
      ar_push         = 1'b0;
      // The process had an arbitration decision in a previous cycle, the valid is locked,
      // wait for the AR transaction.
      if (lock_ar_valid_q) begin
        ar_valid = 1'b1;
        // transaction
        if (ar_ready) begin
          slv_ar_ready    = 1'b1;
          ar_push         = 1'b1;
          lock_ar_valid_d = 1'b0;
          load_ar_lock    = 1'b1;
        end
      end else begin
        // The process can start handling AR transaction if `i_ar_id_counter` has space.
        if (!ar_id_cnt_full) begin
          // There is a valid AR, so look the ID up.
          if (slv_ar_valid && (!ar_select_occupied ||
             (slv_ar_chan_select.ar_select == lookup_ar_select))) begin
            // connect the AR handshake
            ar_valid     = 1'b1;
            // on transaction
            if (ar_ready) begin
              slv_ar_ready = 1'b1;
              ar_push      = 1'b1;
            // no transaction this cycle, lock the valid decision!
            end else begin
              lock_ar_valid_d = 1'b1;
              load_ar_lock    = 1'b1;
            end
          end
        end
      end
    end

    // this ff is needed so that ar does not get de-asserted if an atop gets injected
    `FFLARN(lock_ar_valid_q, lock_ar_valid_d, load_ar_lock, '0, clk_i, rst_ni)

    axi_demux_id_counters #(
      .AxiIdBits         ( AxiLookBits    ),
      .CounterWidth      ( IdCounterWidth ),
      .mst_port_select_t ( select_t       )
    ) i_ar_id_counter (
      .clk_i                        ( clk_i                                         ),
      .rst_ni                       ( rst_ni                                        ),
      .lookup_axi_id_i              ( slv_ar_chan_select.ar_chan.id[0+:AxiLookBits] ),
      .lookup_mst_select_o          ( lookup_ar_select                              ),
      .lookup_mst_select_occupied_o ( ar_select_occupied                            ),
      .full_o                       ( ar_id_cnt_full                                ),
      .inject_axi_id_i              ( slv_aw_chan_select.aw_chan.id[0+:AxiLookBits] ),
      .inject_i                     ( atop_inject                                   ),
      .push_axi_id_i                ( slv_ar_chan_select.ar_chan.id[0+:AxiLookBits] ),
      .push_mst_select_i            ( slv_ar_chan_select.ar_select                  ),
      .push_i                       ( ar_push                                       ),
      .pop_axi_id_i                 ( slv_r_chan.id[0+:AxiLookBits]                 ),
      .pop_i                        ( slv_r_valid & slv_r_ready & slv_r_chan.last   )
    );
    // pop the ID from the counter on a last read transaction

    // AR demux
    // replicate AR channel
    assign mst_ar_chans_o  = {NoMstPorts{slv_ar_chan_select.ar_chan}};
    assign mst_ar_valids_o = (ar_valid) ? (1 << slv_ar_chan_select.ar_select)            : '0;
    assign ar_ready        = (ar_valid) ? mst_ar_readies_i[slv_ar_chan_select.ar_select] : 1'b0;

    //--------------------------------------
    //  R Channel
    //--------------------------------------
    // optional spill register
    spill_register #(
      .T       ( r_chan_t      ),
      .Bypass  ( ~SpillR       )
    ) i_r_spill_reg (
      .clk_i   ( clk_i         ),
      .rst_ni  ( rst_ni        ),
      .valid_i ( slv_r_valid   ),
      .ready_o ( slv_r_ready   ),
      .data_i  ( slv_r_chan    ),
      .valid_o ( slv_r_valid_o ),
      .ready_i ( slv_r_ready_i ),
      .data_o  ( slv_r_chan_o  )
    );

    // Arbitration of the different r responses
    rr_arb_tree #(
      .NumIn    ( NoMstPorts  ),
      .DataType ( r_chan_t    ),
      .AxiVldRdy( 1'b1        ),
      .LockIn   ( 1'b1        )
    ) i_r_mux (
      .clk_i  ( clk_i           ),
      .rst_ni ( rst_ni          ),
      .flush_i( 1'b0            ),
      .rr_i   ( '0              ),
      .req_i  ( mst_r_valids_i  ),
      .gnt_o  ( mst_r_readies_o ),
      .data_i ( mst_r_chans_i   ),
      .gnt_i  ( slv_r_ready     ),
      .req_o  ( slv_r_valid     ),
      .data_o ( slv_r_chan      ),
      .idx_o  (                 )
    );

// Validate parameters.
// pragma translate_off
`ifndef VERILATOR
    initial begin: validate_params
      no_mst_ports: assume (NoMstPorts > 0) else
        $fatal(1, "The Number of slaves (NoMstPorts) has to be at least 1");
      AXI_ID_BITS:  assume (AxiIdWidth >= AxiLookBits) else
        $fatal(1, "AxiIdBits has to be equal or smaller than AxiIdWidth.");
    end
    default disable iff (!rst_ni);
    aw_select: assume property( @(posedge clk_i) (slv_aw_select_i < NoMstPorts)) else
      $fatal(1, "slv_aw_select_i is %d: AW has selected a slave that is not defined.\
                 NoMstPorts: %d", slv_aw_select_i, NoMstPorts);
    ar_select: assume property( @(posedge clk_i) (slv_aw_select_i < NoMstPorts)) else
      $fatal(1, "slv_ar_select_i is %d: AR has selected a slave that is not defined.\
                 NoMstPorts: %d", slv_ar_select_i, NoMstPorts);
    aw_valid_stable: assert property( @(posedge clk_i) (aw_valid && !aw_ready) |=> aw_valid) else
      $fatal(1, "aw_valid was deasserted, when aw_ready = 0 in last cycle.");
    ar_valid_stable: assert property( @(posedge clk_i)
                               (ar_valid && !ar_ready) |=> ar_valid) else
      $fatal(1, "ar_valid was deasserted, when ar_ready = 0 in last cycle.");
    aw_stable: assert property( @(posedge clk_i) (aw_valid && !aw_ready)
                               |=> $stable(slv_aw_chan_select)) else
      $fatal(1, "slv_aw_chan_select unstable with valid set.");
    ar_stable: assert property( @(posedge clk_i) (ar_valid && !ar_ready)
                               |=> $stable(slv_ar_chan_select)) else
      $fatal(1, "slv_aw_chan_select unstable with valid set.");
`endif
// pragma translate_on
  end
endmodule

module axi_demux_id_counters #(
  // the lower bits of the AXI ID that should be considered, results in 2**AXI_ID_BITS counters
  parameter int unsigned AxiIdBits         = 2,
  parameter int unsigned CounterWidth      = 4,
  parameter type         mst_port_select_t = logic
) (
  input                        clk_i,   // Clock
  input                        rst_ni,  // Asynchronous reset active low
  // lookup
  input  logic [AxiIdBits-1:0] lookup_axi_id_i,
  output mst_port_select_t     lookup_mst_select_o,
  output logic                 lookup_mst_select_occupied_o,
  // push
  output logic                 full_o,
  input  logic [AxiIdBits-1:0] push_axi_id_i,
  input  mst_port_select_t     push_mst_select_i,
  input  logic                 push_i,
  // inject ATOPs in AR channel
  input  logic [AxiIdBits-1:0] inject_axi_id_i,
  input  logic                 inject_i,
  // pop
  input  logic [AxiIdBits-1:0] pop_axi_id_i,
  input  logic                 pop_i
);
  localparam int unsigned NoCounters = 2**AxiIdBits;
  typedef logic [CounterWidth-1:0] cnt_t;

  // registers, each gets loaded when push_en[i]
  mst_port_select_t [NoCounters-1:0] mst_select_q;

  // counter signals
  logic [NoCounters-1:0] push_en, inject_en, pop_en, occupied, cnt_full;

  //-----------------------------------
  // Lookup
  //-----------------------------------
  assign lookup_mst_select_o          = mst_select_q[lookup_axi_id_i];
  assign lookup_mst_select_occupied_o = occupied[lookup_axi_id_i];
  //-----------------------------------
  // Push and Pop
  //-----------------------------------
  assign push_en   = (push_i)   ? (1 << push_axi_id_i)   : '0;
  assign inject_en = (inject_i) ? (1 << inject_axi_id_i) : '0;
  assign pop_en    = (pop_i)    ? (1 << pop_axi_id_i)    : '0;
  assign full_o    = |cnt_full;
  // counters
  for (genvar i = 0; i < NoCounters; i++) begin : gen_counters
    logic cnt_en, cnt_down, overflow;
    cnt_t cnt_delta, in_flight;
    always_comb begin
      case ({push_en[i], inject_en[i], pop_en[i]})
        3'b001  : begin // pop_i = -1
          cnt_en    = 1'b1;
          cnt_down  = 1'b1;
          cnt_delta = cnt_t'(1);
        end
        3'b010  : begin // inject_i = +1
          cnt_en    = 1'b1;
          cnt_down  = 1'b0;
          cnt_delta = cnt_t'(1);
        end
     // 3'b011, inject_i & pop_i = 0 --> use default
        3'b100  : begin // push_i = +1
          cnt_en    = 1'b1;
          cnt_down  = 1'b0;
          cnt_delta = cnt_t'(1);
        end
     // 3'b101, push_i & pop_i = 0 --> use default
        3'b110  : begin // push_i & inject_i = +2
          cnt_en    = 1'b1;
          cnt_down  = 1'b0;
          cnt_delta = cnt_t'(2);
        end
        3'b111  : begin // push_i & inject_i & pop_i = +1
          cnt_en    = 1'b1;
          cnt_down  = 1'b0;
          cnt_delta = cnt_t'(1);
        end
        default : begin // do nothing to the counters
          cnt_en    = 1'b0;
          cnt_down  = 1'b0;
          cnt_delta = cnt_t'(0);
        end
      endcase
    end

    delta_counter #(
      .WIDTH           ( CounterWidth ),
      .STICKY_OVERFLOW ( 1'b0         )
    ) i_in_flight_cnt (
      .clk_i      ( clk_i     ),
      .rst_ni     ( rst_ni    ),
      .clear_i    ( 1'b0      ),
      .en_i       ( cnt_en    ),
      .load_i     ( 1'b0      ),
      .down_i     ( cnt_down  ),
      .delta_i    ( cnt_delta ),
      .d_i        ( '0        ),
      .q_o        ( in_flight ),
      .overflow_o ( overflow  )
    );
    assign occupied[i] = |in_flight;
    assign cnt_full[i] = overflow | (&in_flight);

    // holds the selection signal for this id
    `FFLARN(mst_select_q[i], push_mst_select_i, push_en[i], '0, clk_i, rst_ni)

// pragma translate_off
`ifndef VERILATOR
    // Validate parameters.
    cnt_underflow: assert property(
      @(posedge clk_i) disable iff (~rst_ni) (pop_en[i] |=> !overflow)) else
        $fatal(1, "axi_demux_id_counters > Counter: %0d underflowed.\
                   The reason is probably a faulty AXI response.", i);
`endif
// pragma translate_on
  end
  // moved to macro in genvar above
  // always_ff @(posedge clk_i, negedge rst_ni) begin : proc_mst_port_sel_reg
  //   if (!rst_ni) begin
  //     mst_select_q <= '0;
  //   end else begin
  //     for (int unsigned i = 0; i < NoCounters; i++) begin
  //       if (push_en[i]) begin
  //         mst_select_q[i] <= push_mst_select_i;
  //       end
  //     end
  //   end
  // end
endmodule

// interface wrapper
`include "axi/assign.svh"
`include "axi/typedef.svh"
module axi_demux_wrap #(
  parameter int unsigned AxiIdWidth     = 0, // Synopsys DC requires a default value for param.
  parameter int unsigned AxiAddrWidth   = 0,
  parameter int unsigned AxiDataWidth   = 0,
  parameter int unsigned AxiUserWidth   = 0,
  parameter int unsigned NoMstPorts     = 3,
  parameter int unsigned MaxTrans       = 8,
  parameter int unsigned AxiLookBits    = 3,
  parameter bit          FallThrough    = 1'b0,
  parameter bit          SpillAw        = 1'b1,
  parameter bit          SpillW         = 1'b0,
  parameter bit          SpillB         = 1'b0,
  parameter bit          SpillAr        = 1'b1,
  parameter bit          SpillR         = 1'b0,
  // Dependent parameters, DO NOT OVERRIDE!
  parameter type         select_t       = logic [$clog2(NoMstPorts)-1:0] // MST port select type
) (
  input  logic    clk_i,               // Clock
  input  logic    rst_ni,              // Asynchronous reset active low
  input  logic    test_i,              // Testmode enable
  input  select_t slv_aw_select_i,     // has to be stable, when aw_valid
  input  select_t slv_ar_select_i,     // has to be stable, when ar_valid
  AXI_BUS.Slave   slv,                 // slave port
  AXI_BUS.Master  mst [NoMstPorts-1:0] // master ports
);

  typedef logic [AxiIdWidth-1:0]       id_t;
  typedef logic [AxiAddrWidth-1:0]   addr_t;
  typedef logic [AxiDataWidth-1:0]   data_t;
  typedef logic [AxiDataWidth/8-1:0] strb_t;
  typedef logic [AxiUserWidth-1:0]   user_t;
  `AXI_TYPEDEF_AW_CHAN_T( aw_chan_t, addr_t, id_t,         user_t);
  `AXI_TYPEDEF_W_CHAN_T (  w_chan_t, data_t,       strb_t, user_t);
  `AXI_TYPEDEF_B_CHAN_T (  b_chan_t,         id_t,         user_t);
  `AXI_TYPEDEF_AR_CHAN_T( ar_chan_t, addr_t, id_t,         user_t);
  `AXI_TYPEDEF_R_CHAN_T (  r_chan_t, data_t, id_t,         user_t);
  `AXI_TYPEDEF_REQ_T    (     req_t, aw_chan_t, w_chan_t, ar_chan_t);
  `AXI_TYPEDEF_RESP_T   (    resp_t,  b_chan_t, r_chan_t) ;

  req_t                   slv_req;
  resp_t                  slv_resp;
  req_t  [NoMstPorts-1:0] mst_req;
  resp_t [NoMstPorts-1:0] mst_resp;

  // master ports
  // AW channel
  aw_chan_t [NoMstPorts-1:0] mst_aw_chans;
  logic     [NoMstPorts-1:0] mst_aw_valids;
  logic     [NoMstPorts-1:0] mst_aw_readies;
  //  W channel
  w_chan_t  [NoMstPorts-1:0] mst_w_chans;
  logic     [NoMstPorts-1:0] mst_w_valids;
  logic     [NoMstPorts-1:0] mst_w_readies;
  //  B channel
  b_chan_t  [NoMstPorts-1:0] mst_b_chans;
  logic     [NoMstPorts-1:0] mst_b_valids;
  logic     [NoMstPorts-1:0] mst_b_readies;
  // AR channel
  ar_chan_t [NoMstPorts-1:0] mst_ar_chans;
  logic     [NoMstPorts-1:0] mst_ar_valids;
  logic     [NoMstPorts-1:0] mst_ar_readies;
  //  R channel
  r_chan_t  [NoMstPorts-1:0] mst_r_chans;
  logic     [NoMstPorts-1:0] mst_r_valids;
  logic     [NoMstPorts-1:0] mst_r_readies;

  `AXI_ASSIGN_TO_REQ    ( slv_req,  slv      );
  `AXI_ASSIGN_FROM_RESP ( slv,      slv_resp );

  for (genvar i = 0; i < NoMstPorts; i++) begin : gen_assign_mst_ports
    assign mst_req[i].aw       = mst_aw_chans[i]      ;
    assign mst_req[i].aw_valid = mst_aw_valids[i]     ;
    assign mst_aw_readies[i]   = mst_resp[i].aw_ready ;

    assign mst_req[i].w        = mst_w_chans[i]       ;
    assign mst_req[i].w_valid  = mst_w_valids[i]      ;
    assign mst_w_readies[i]    = mst_resp[i].w_ready  ;

    assign mst_b_chans[i]      = mst_resp[i].b        ;
    assign mst_b_valids[i]     = mst_resp[i].b_valid  ;
    assign mst_req[i].b_ready  = mst_b_readies[i]     ;

    assign mst_req[i].ar       = mst_ar_chans[i]      ;
    assign mst_req[i].ar_valid = mst_ar_valids[i]     ;
    assign mst_ar_readies[i]   = mst_resp[i].ar_ready ;

    assign mst_r_chans[i]      = mst_resp[i].r        ;
    assign mst_r_valids[i]     = mst_resp[i].r_valid  ;
    assign mst_req[i].r_ready  = mst_r_readies[i]     ;

    `AXI_ASSIGN_FROM_REQ  ( mst[i]     , mst_req[i]  );
    `AXI_ASSIGN_TO_RESP   ( mst_resp[i], mst[i]      );
  end

  axi_demux #(
    .AxiIdWidth     ( AxiIdWidth     ), // ID Width
    .aw_chan_t      ( aw_chan_t      ), // AW Channel Type
    .w_chan_t       (  w_chan_t      ), //  W Channel Type
    .b_chan_t       (  b_chan_t      ), //  B Channel Type
    .ar_chan_t      ( ar_chan_t      ), // AR Channel Type
    .r_chan_t       (  r_chan_t      ), //  R Channel Type
    .NoMstPorts     ( NoMstPorts     ),
    .MaxTrans       ( MaxTrans       ),
    .IdCounterWidth ( IdCounterWidth ),
    .AxiLookBits    ( AxiLookBits    ),
    .FallThrough    ( FallThrough    ),
    .SpillAw        ( SpillAw        ),
    .SpillW         ( SpillW         ),
    .SpillB         ( SpillR         ),
    .SpillAr        ( SpillAr        ),
    .SpillR         ( SpillR         )
  ) i_axi_demux (
    .clk_i,   // Clock
    .rst_ni,  // Asynchronous reset active low
    .test_i,  // Testmode enable
    // slave port
    // AW channel
    .slv_aw_chan_i    ( slv_req.aw        ),
    .slv_aw_select_i  ( slv_aw_select_i   ), // must be stable while slv_aw_valid_i
    .slv_aw_valid_i   ( slv_req.aw_valid  ),
    .slv_aw_ready_o   ( slv_resp.aw_ready ),
    //  W channel
    .slv_w_chan_i     ( slv_req.w         ),
    .slv_w_valid_i    ( slv_req.w_valid   ),
    .slv_w_ready_o    ( slv_resp.w_ready  ),
    //  B channel
    .slv_b_chan_o     ( slv_resp.b        ),
    .slv_b_valid_o    ( slv_resp.b_valid  ),
    .slv_b_ready_i    ( slv_req.b_ready   ),
    // AR channel
    .slv_ar_chan_i    ( slv_req.ar        ),
    .slv_ar_select_i  ( slv_ar_select_i   ), // must be stable while slv_ar_valid_i
    .slv_ar_valid_i   ( slv_req.ar_valid  ),
    .slv_ar_ready_o   ( slv_resp.ar_ready ),
    //  R channel
    .slv_r_chan_o     ( slv_resp.r        ),
    .slv_r_valid_o    ( slv_resp.r_valid  ),
    .slv_r_ready_i    ( slv_req.r_ready   ),
    // master ports
    // AW channel
    .mst_aw_chans_o   ( mst_aw_chans      ),
    .mst_aw_valids_o  ( mst_aw_valids     ),
    .mst_aw_readies_i ( mst_aw_readies    ),
     //  W channel
    .mst_w_chans_o    ( mst_w_chans       ),
    .mst_w_valids_o   ( mst_w_valids      ),
    .mst_w_readies_i  ( mst_w_readies     ),
     //  B channel
    .mst_b_chans_i    ( mst_b_chans       ),
    .mst_b_valids_i   ( mst_b_valids      ),
    .mst_b_readies_o  ( mst_b_readies     ),
     // AR channel
    .mst_ar_chans_o   ( mst_ar_chans      ),
    .mst_ar_valids_o  ( mst_ar_valids     ),
    .mst_ar_readies_i ( mst_ar_readies    ),
     //  R channel
    .mst_r_chans_i    ( mst_r_chans       ),
    .mst_r_valids_i   ( mst_r_valids      ),
    .mst_r_readies_o  ( mst_r_readies     )
  );
endmodule
