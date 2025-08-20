// Copyright 2023 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51
//
// Authors:
// - Wolfgang Roenninger <wroennin@iis.ee.ethz.ch>
// - Andreas Kurth <akurth@iis.ee.ethz.ch>
// - Thomas Benz <tbenz@iis.ee.ethz.ch>

`include "axi/typedef.svh"
`include "common_cells/registers.svh"

/// Split AXI4 bursts into single-beat transactions.
///
/// ## Limitations
///
/// - This module does not support wrapping ([`axi_pkg::BURST_WRAP`](package.axi_pkg)) bursts and
///   responds to such bursts with slave error(s).
/// - This module does not support atomic operations (ATOPs) and responds to ATOPs with a slave
///   error.  Place an [`axi_atop_filter`](module.axi_atop_filter) before this module if upstream
///   modules can generate ATOPs.
module axi_burst_splitter_gran #(
  /// Maximum number of AXI read bursts outstanding at the same time
  parameter int unsigned MaxReadTxns   = 32'd0,
  /// Maximum number of AXI write bursts outstanding at the same time
  parameter int unsigned MaxWriteTxns  = 32'd0,
  /// Internal ID queue can work in two bandwidth modes: see id_queue.sv for details
  parameter bit          FullBW        = 1'b0,
  /// Cut paths through the IP
  parameter bit          CutPath       = 1'b0,
  /// Disable checks, handle unsupported transfers as bypass instead of reporting an error
  parameter bit          DisableChecks = 1'b0,
  // AXI Bus Types
  parameter int unsigned AddrWidth     = 32'd0,
  parameter int unsigned DataWidth     = 32'd0,
  parameter int unsigned IdWidth       = 32'd0,
  parameter int unsigned UserWidth     = 32'd0,
  parameter type         axi_req_t     = logic,
  parameter type         axi_resp_t    = logic,
  parameter type         axi_aw_chan_t = logic,
  parameter type         axi_w_chan_t  = logic,
  parameter type         axi_b_chan_t  = logic,
  parameter type         axi_ar_chan_t = logic,
  parameter type         axi_r_chan_t  = logic
) (
  input  logic  clk_i,
  input  logic  rst_ni,

  // length
  input  axi_pkg::len_t len_limit_i,

  // Input / Slave Port
  input  axi_req_t  slv_req_i,
  output axi_resp_t slv_resp_o,

  // Output / Master Port
  output axi_req_t  mst_req_o,
  input  axi_resp_t mst_resp_i
);

  // Demultiplex between supported and unsupported transactions.
  axi_req_t   slv_req,  act_req,  unsupported_req;
  axi_resp_t  slv_resp, act_resp, unsupported_resp;

  axi_multicut #(
    .NoCuts    ( CutPath  ),
    .aw_chan_t ( axi_aw_chan_t ),
    .w_chan_t  ( axi_w_chan_t  ),
    .b_chan_t  ( axi_b_chan_t  ),
    .ar_chan_t ( axi_ar_chan_t ),
    .r_chan_t  ( axi_r_chan_t  ),
    .axi_req_t ( axi_req_t     ),
    .axi_resp_t( axi_resp_t    )
  ) i_axi_multicut (
    .clk_i,
    .rst_ni,
    .slv_req_i ,
    .slv_resp_o,
    .mst_req_o   ( slv_req  ),
    .mst_resp_i  ( slv_resp )
  );

  logic sel_aw_unsupported, sel_ar_unsupported;
  localparam int unsigned MaxTxns = (MaxReadTxns > MaxWriteTxns) ? MaxReadTxns : MaxWriteTxns;
  axi_demux_simple #(
    .AxiIdWidth   ( IdWidth     ),
    .axi_req_t    ( axi_req_t   ),
    .axi_resp_t   ( axi_resp_t  ),
    .NoMstPorts   ( 2           ),
    .MaxTrans     ( MaxTxns     ),
    .AxiLookBits  ( IdWidth     )
  ) i_demux_supported_vs_unsupported (
    .clk_i,
    .rst_ni,
    .test_i           ( 1'b0                          ),
    .slv_req_i        ( slv_req ),
    .slv_aw_select_i  ( sel_aw_unsupported            ),
    .slv_ar_select_i  ( sel_ar_unsupported            ),
    .slv_resp_o       ( slv_resp ),
    .mst_reqs_o       ( {unsupported_req,  act_req}   ),
    .mst_resps_i      ( {unsupported_resp, act_resp}  )
  );

  // Define supported transactions.
  function bit txn_supported(axi_pkg::atop_t atop, axi_pkg::burst_t burst, axi_pkg::cache_t cache,
      axi_pkg::len_t len, axi_pkg::len_t len_limit);

    // if the splitter does not touch the transaction: allow it
    if (len >= len_limit) begin
      return 1'b1;

    //
    end else begin

      // Wrapping bursts are currently not supported to be split
      if (burst == axi_pkg::BURST_WRAP) return 1'b0;

      // ATOP bursts are not supported.
      if (atop != '0 & len > 0) return 1'b0;

      // The AXI Spec (A3.4.1) only allows splitting non-modifiable transactions ..
      if (!axi_pkg::modifiable(cache)) begin
        // .. if they are INCR bursts and longer than 16 beats.
        return (burst == axi_pkg::BURST_INCR) & (len > 16);
      end

      // All other transactions are supported for splitting.
      return 1'b1;
    end
  endfunction


  assign sel_aw_unsupported = DisableChecks ? 1'b0 : ~txn_supported(slv_req.aw.atop,
                                              slv_req.aw.burst, slv_req.aw.cache, slv_req.aw.len,
                                              len_limit_i);

  assign sel_ar_unsupported = DisableChecks ? 1'b0 : ~txn_supported('0, slv_req.ar.burst,
                                              slv_req.ar.cache, slv_req.ar.len, len_limit_i);

  // Respond to unsupported transactions with slave errors.
  axi_err_slv #(
    .AxiIdWidth ( IdWidth               ),
    .axi_req_t  ( axi_req_t             ),
    .axi_resp_t ( axi_resp_t            ),
    .Resp       ( axi_pkg::RESP_SLVERR  ),
    .ATOPs      ( 1'b0                  ),  // The burst splitter does not support ATOPs.
    .MaxTrans   ( 1                     )   // Splitting bursts implies a low-performance bus.
  ) i_err_slv (
    .clk_i,
    .rst_ni,
    .test_i     ( 1'b0              ),
    .slv_req_i  ( unsupported_req   ),
    .slv_resp_o ( unsupported_resp  )
  );

  // --------------------------------------------------
  // AW Channel
  // --------------------------------------------------
  logic           w_cnt_dec, w_cnt_req, w_cnt_gnt, w_cnt_err;
  axi_pkg::len_t  w_cnt_len;
  axi_burst_splitter_gran_ax_chan #(
    .chan_t   ( axi_aw_chan_t ),
    .IdWidth  ( IdWidth       ),
    .MaxTxns  ( MaxWriteTxns  ),
    .CutPath  ( CutPath       ),
    .FullBW   ( FullBW        )
  ) i_axi_burst_splitter_gran_aw_chan (
    .clk_i,
    .rst_ni,
    .len_limit_i,
    .ax_i           ( act_req.aw           ),
    .ax_valid_i     ( act_req.aw_valid     ),
    .ax_ready_o     ( act_resp.aw_ready    ),
    .ax_o           ( mst_req_o.aw         ),
    .ax_valid_o     ( mst_req_o.aw_valid   ),
    .ax_ready_i     ( mst_resp_i.aw_ready  ),
    .cnt_id_i       ( mst_resp_i.b.id      ),
    .cnt_len_o      ( w_cnt_len            ),
    .cnt_set_err_i  ( mst_resp_i.b.resp[1] ),
    .cnt_err_o      ( w_cnt_err            ),
    .cnt_dec_i      ( w_cnt_dec            ),
    .cnt_req_i      ( w_cnt_req            ),
    .cnt_gnt_o      ( w_cnt_gnt            )
  );

  // --------------------------------------------------
  // W Channel
  // --------------------------------------------------
  // keep a state where we are in the fragmentation of the w
  axi_pkg::len_t w_len_d, w_len_q;
  logic          w_len_vld_q, w_len_vld_d;


  // Feed through, except `last`, which needs to be modified
  always_comb begin : proc_w_frag
    mst_req_o.w        = act_req.w;
    w_len_d            = w_len_q;
    w_len_vld_d        = w_len_vld_q;
    // the entire detection machine is only required if len_limit > 0
    if (len_limit_i != 8'h00) begin
      // In the case we are in the granular mode: last is from req or when w_len valid and '0.
      mst_req_o.w.last = (w_len_vld_q & (w_len_q == 8'h00)) | act_req.w.last;
      // only advance the machine if w ready and valid
      if (act_resp.w_ready & act_req.w_valid)  begin
        // the counter is not yet valid, set it to valid and initialize
        if (!w_len_vld_q) begin
          w_len_vld_d = 1'b1;
          w_len_d     = len_limit_i - 8'h01;
        end else begin
          w_len_d = w_len_q - 8'h01;
          // in the last case, reinitialize the counter
          if (w_len_q == 8'h00) begin
            w_len_d          = len_limit_i;
          end
        end
        // final overwrite. if a downstream last comes, the counter is invalid and set to 0
        if (act_req.w.last) begin
          w_len_vld_d  = 1'b0;
          w_len_d      = 8'h00;
        end
      end
    end else begin
      // we operate in the legacy mode -> every w is last
      mst_req_o.w.last = 1'b1;
    end
  end

  assign mst_req_o.w_valid  = act_req.w_valid;
  assign act_resp.w_ready   = mst_resp_i.w_ready;

  // --------------------------------------------------
  // B Channel
  // --------------------------------------------------
  // Filter B response, except for the last one
  enum logic {BReady, BWait} b_state_d, b_state_q;
  logic b_err_d, b_err_q;
  always_comb begin
    mst_req_o.b_ready = 1'b0;
    act_resp.b        = '0;
    act_resp.b_valid  = 1'b0;
    w_cnt_dec         = 1'b0;
    w_cnt_req         = 1'b0;
    b_err_d           = b_err_q;
    b_state_d         = b_state_q;

    unique case (b_state_q)
      BReady: begin
        if (mst_resp_i.b_valid) begin
          w_cnt_req = 1'b1;
          if (w_cnt_gnt) begin
            if (w_cnt_len < ({1'b0, len_limit_i} + 9'h001)) begin
              act_resp.b = mst_resp_i.b;
              if (w_cnt_err) begin
                act_resp.b.resp = axi_pkg::RESP_SLVERR;
              end
              act_resp.b_valid  = 1'b1;
              w_cnt_dec         = 1'b1;
              if (act_req.b_ready) begin
                mst_req_o.b_ready = 1'b1;
              end else begin
                b_state_d = BWait;
                b_err_d   = w_cnt_err;
              end
            end else begin
              mst_req_o.b_ready = 1'b1;
              w_cnt_dec         = 1'b1;
            end
          end
        end
      end
      BWait: begin
        act_resp.b = mst_resp_i.b;
        if (b_err_q) begin
          act_resp.b.resp = axi_pkg::RESP_SLVERR;
        end
        act_resp.b_valid  = 1'b1;
        if (mst_resp_i.b_valid && act_req.b_ready) begin
          mst_req_o.b_ready = 1'b1;
          b_state_d         = BReady;
        end
      end
      default: /*do nothing*/;
    endcase
  end

  // --------------------------------------------------
  // AR Channel
  // --------------------------------------------------
  // See description of `ax_chan` module.
  logic           r_cnt_dec, r_cnt_req, r_cnt_gnt;
  axi_pkg::len_t  r_cnt_len;
  axi_burst_splitter_gran_ax_chan #(
    .chan_t   ( axi_ar_chan_t ),
    .IdWidth  ( IdWidth       ),
    .MaxTxns  ( MaxReadTxns   ),
    .CutPath  ( CutPath       ),
    .FullBW   ( FullBW        )
  ) i_axi_burst_splitter_gran_ar_chan (
    .clk_i,
    .rst_ni,
    .len_limit_i,
    .ax_i           ( act_req.ar          ),
    .ax_valid_i     ( act_req.ar_valid    ),
    .ax_ready_o     ( act_resp.ar_ready   ),
    .ax_o           ( mst_req_o.ar        ),
    .ax_valid_o     ( mst_req_o.ar_valid  ),
    .ax_ready_i     ( mst_resp_i.ar_ready ),
    .cnt_id_i       ( mst_resp_i.r.id     ),
    .cnt_len_o      ( r_cnt_len           ),
    .cnt_set_err_i  ( 1'b0                ),
    .cnt_err_o      (                     ),
    .cnt_dec_i      ( r_cnt_dec           ),
    .cnt_req_i      ( r_cnt_req           ),
    .cnt_gnt_o      ( r_cnt_gnt           )
  );

  // --------------------------------------------------
  // R Channel
  // --------------------------------------------------
  // Reconstruct `last`, feed rest through.
  logic r_last_d, r_last_q;
  enum logic {RFeedthrough, RWait} r_state_d, r_state_q;
  always_comb begin
    r_cnt_dec         = 1'b0;
    r_cnt_req         = 1'b0;
    r_last_d          = r_last_q;
    r_state_d         = r_state_q;
    mst_req_o.r_ready = 1'b0;
    act_resp.r        = mst_resp_i.r;
    act_resp.r.last   = 1'b0;
    act_resp.r_valid  = 1'b0;

    unique case (r_state_q)
      RFeedthrough: begin
        // If downstream has an R beat and the R counters can give us the remaining length of
        // that burst, ...
        if (mst_resp_i.r_valid) begin
          // if downstream is last
          if (mst_resp_i.r.last) begin
            r_cnt_req = 1'b1;
            if (r_cnt_gnt) begin
              r_last_d = (r_cnt_len < ({1'b0, len_limit_i} + 9'h001));
              act_resp.r.last   = r_last_d;
              // Decrement the counter.
              r_cnt_dec         = 1'b1;
              // Try to forward the beat upstream.
              act_resp.r_valid  = 1'b1;
              if (act_req.r_ready) begin
                // Acknowledge downstream.
                mst_req_o.r_ready = 1'b1;
              end else begin
                // Wait for upstream to become ready.
                r_state_d = RWait;
              end
            end
          end else begin
            // downstream was not last, just a normal read to pass through
            r_last_d = 1'b0;
            act_resp.r.last   = r_last_d;
            // Try to forward the beat upstream.
            act_resp.r_valid  = 1'b1;
            if (act_req.r_ready) begin
              // Acknowledge downstream.
              mst_req_o.r_ready = 1'b1;
            end else begin
              // Wait for upstream to become ready.
              r_state_d = RWait;
            end
          end
        end
      end
      RWait: begin
        act_resp.r.last   = r_last_q;
        act_resp.r_valid  = mst_resp_i.r_valid;
        if (mst_resp_i.r_valid && act_req.r_ready) begin
          mst_req_o.r_ready = 1'b1;
          r_state_d         = RFeedthrough;
        end
      end
      default: /*do nothing*/;
    endcase
  end

  // --------------------------------------------------
  // Flip-Flops
  // --------------------------------------------------
  `FFARN(b_err_q, b_err_d, 1'b0, clk_i, rst_ni)
  `FFARN(b_state_q, b_state_d, BReady, clk_i, rst_ni)
  `FFARN(r_last_q, r_last_d, 1'b0, clk_i, rst_ni)
  `FFARN(r_state_q, r_state_d, RFeedthrough, clk_i, rst_ni)
  `FFARN(w_len_q, w_len_d, 8'h00, clk_i, rst_ni)
  `FFARN(w_len_vld_q, w_len_vld_d, 1'b0, clk_i, rst_ni)

  // --------------------------------------------------
  // Assumptions and assertions
  // --------------------------------------------------
  `ifndef VERILATOR
  // pragma translate_off
  default disable iff (!rst_ni);
  // Inputs
  assume property (@(posedge clk_i) slv_req_i.aw_valid |->
      txn_supported(slv_req_i.aw.atop, slv_req_i.aw.burst, slv_req_i.aw.cache, slv_req_i.aw.len,
                    len_limit_i)
    ) else $warning("Unsupported AW transaction received, returning slave error!");
  assume property (@(posedge clk_i) slv_req_i.ar_valid |->
      txn_supported('0, slv_req_i.ar.burst, slv_req_i.ar.cache, slv_req_i.ar.len, len_limit_i)
    ) else $warning("Unsupported AR transaction received, returning slave error!");
  // Outputs
  assert property (@(posedge clk_i) mst_req_o.aw_valid |-> mst_req_o.aw.len <= len_limit_i)
    else $fatal(1, "AW burst longer than a single beat emitted!");
  assert property (@(posedge clk_i) mst_req_o.ar_valid |-> mst_req_o.ar.len <= len_limit_i)
    else $fatal(1, "AR burst longer than a single beat emitted!");
  // pragma translate_on
  `endif

endmodule



/// Internal module of [`axi_burst_splitter_gran`](module.axi_burst_splitter_gran) to control
/// Ax channels.
///
/// Store burst lengths in counters, which are associated to AXI IDs through ID queues (to allow
/// reordering of responses w.r.t. requests).
module axi_burst_splitter_gran_ax_chan #(
  parameter type         chan_t  = logic,
  parameter int unsigned IdWidth = 32'd0,
  parameter int unsigned MaxTxns = 32'd0,
  parameter bit          CutPath =  1'b0,
  parameter bit          FullBW  =  1'b0,
  parameter type         id_t    = logic[IdWidth-1:0]
) (
  input  logic          clk_i,
  input  logic          rst_ni,

  // length
  input  axi_pkg::len_t len_limit_i,

  input  chan_t         ax_i,
  input  logic          ax_valid_i,
  output logic          ax_ready_o,
  output chan_t         ax_o,
  output logic          ax_valid_o,
  input  logic          ax_ready_i,

  input  id_t           cnt_id_i,
  output axi_pkg::len_t cnt_len_o,
  input  logic          cnt_set_err_i,
  output logic          cnt_err_o,
  input  logic          cnt_dec_i,
  input  logic          cnt_req_i,
  output logic          cnt_gnt_o
);

  typedef logic[IdWidth-1:0]           cnt_id_t;
  typedef logic[axi_pkg::LenWidth:0] num_beats_t;

  chan_t      ax_d, ax_q;
  // keep the number of remaining beats. != len
  num_beats_t num_beats_d, num_beats_q;
  // maximum number of beats to subtract in one go
  num_beats_t max_beats;


  logic cnt_alloc_req, cnt_alloc_gnt;
  axi_burst_splitter_gran_counters #(
    .MaxTxns ( MaxTxns  ),
    .IdWidth ( IdWidth  ),
    .CutPath ( CutPath  ),
    .FullBW  ( FullBW   )
  ) i_axi_burst_splitter_gran_counters (
    .clk_i,
    .rst_ni,
    .alloc_id_i     ( ax_i.id       ),
    .alloc_len_i    ( ax_i.len      ),
    .alloc_req_i    ( cnt_alloc_req ),
    .alloc_gnt_o    ( cnt_alloc_gnt ),
    .cnt_id_i       ( cnt_id_i      ),
    .cnt_len_o      ( cnt_len_o     ),
    .cnt_set_err_i  ( cnt_set_err_i ),
    .cnt_err_o      ( cnt_err_o     ),
    .cnt_dec_i      ( cnt_dec_i     ),
    .cnt_delta_i    ( max_beats     ),
    .cnt_req_i      ( cnt_req_i     ),
    .cnt_gnt_o      ( cnt_gnt_o     )
  );

  // assign the max_beats depending on the limit value. Limit value is given as an AXI len.
  // limit = 0 means one beat each AX
  assign max_beats = {1'b0, len_limit_i} + 9'h001;

  enum logic {Idle, Busy} state_d, state_q;
  always_comb begin
    cnt_alloc_req = 1'b0;
    ax_d          = ax_q;
    state_d       = state_q;
    num_beats_d   = num_beats_q;
    ax_o          = '0;
    ax_valid_o    = 1'b0;
    ax_ready_o    = 1'b0;
    unique case (state_q)
      Idle: begin
        if (ax_valid_i && cnt_alloc_gnt) begin

          // No splitting required -> feed through.
          if (ax_i.len <= len_limit_i) begin
            ax_o          = ax_i;
            ax_valid_o    = 1'b1;
            // As soon as downstream is ready, allocate a counter and acknowledge upstream.
            if (ax_ready_i) begin
              cnt_alloc_req = 1'b1;
              ax_ready_o    = 1'b1;
            end

          // Splitting required.
          end else begin
            // Store Ax, allocate a counter, and acknowledge upstream.
            ax_d          = ax_i;
            cnt_alloc_req = 1'b1;
            ax_ready_o    = 1'b1;
            // As burst is too long, we will need to send multiple
            state_d = Busy;
            num_beats_d = ({1'b0, ax_i.len} + 9'h001);
            // Try to feed first burst through.
            ax_o          = ax_d;
            // if we are here we can send the length limit once for sure
            ax_o.len      = len_limit_i;
            ax_valid_o    = 1'b1;
            if (ax_ready_i) begin
              // Reduce number of bursts still to be sent by one and increment address.
              num_beats_d = ({1'b0, ax_i.len} + 9'h001) - max_beats;
              if (ax_d.burst == axi_pkg::BURST_INCR) begin
                // Align
                ax_d.addr = axi_pkg::aligned_addr(axi_pkg::largest_addr_t'(ax_d.addr), ax_d.size);
                // modify the address
                ax_d.addr += (1 << ax_d.size) * max_beats;
              end
            end
          end
        end
      end
      Busy: begin
        // Sent next burst from split.
        ax_o       = ax_q;
        ax_valid_o = 1'b1;
        // emit the proper length
        if (num_beats_q <= max_beats) begin
          // this is the remainder
          ax_o.len = axi_pkg::len_t'(num_beats_q - 9'h001);
        end else begin
          ax_o.len = len_limit_i;
        end
        // next state
        if (ax_ready_i) begin
          if (num_beats_q <= max_beats) begin
            // If this was the last burst, go back to idle.
            state_d = Idle;
          end else begin
            // Otherwise, continue with the next burst.
            num_beats_d = num_beats_q - max_beats;
            if (ax_q.burst == axi_pkg::BURST_INCR) begin
              ax_d.addr = axi_pkg::aligned_addr(axi_pkg::largest_addr_t'(ax_q.addr), ax_q.size);
              ax_d.addr += (1 << ax_q.size) * max_beats;
            end
          end
        end
      end
      default: /*do nothing*/;
    endcase
  end

  // registers
  `FFARN(ax_q, ax_d, '0, clk_i, rst_ni)
  `FFARN(state_q, state_d, Idle, clk_i, rst_ni)
  `FFARN(num_beats_q, num_beats_d, 9'h000, clk_i, rst_ni)
endmodule



/// Internal module of [`axi_burst_splitter_gran`](module.axi_burst_splitter_gran) to order
/// transactions.
module axi_burst_splitter_gran_counters #(
  parameter int unsigned MaxTxns = 32'd0,
  parameter int unsigned IdWidth = 32'd0,
  parameter bit          CutPath =  1'b0,
  parameter bit          FullBW  =  1'b0,
  parameter type         id_t    = logic [IdWidth-1:0],
  parameter type         cnt_t   = logic [axi_pkg::LenWidth:0]
) (
  input  logic          clk_i,
  input  logic          rst_ni,

  input  id_t           alloc_id_i,
  input  axi_pkg::len_t alloc_len_i,
  input  logic          alloc_req_i,
  output logic          alloc_gnt_o,

  input  id_t           cnt_id_i,
  output axi_pkg::len_t cnt_len_o,
  input  logic          cnt_set_err_i,
  output logic          cnt_err_o,
  input  logic          cnt_dec_i,
  input  cnt_t          cnt_delta_i,
  input  logic          cnt_req_i,
  output logic          cnt_gnt_o
);

  // the allocation interface can be cut
  typedef struct packed {
    id_t           id;
    axi_pkg::len_t len;
  } alloc_pld_t;

  alloc_pld_t alloc_pld_in, alloc_pld_out;
  logic       alloc_req;
  logic       alloc_gnt;

  assign alloc_pld_in.id  = alloc_id_i;
  assign alloc_pld_in.len = alloc_len_i;

  if (CutPath) begin : gen_spill
    spill_register #(
      .T      ( alloc_pld_t ),
      .Bypass ( 1'b0        )
    ) i_spill_register_alloc (
      .clk_i,
      .rst_ni,
      .valid_i ( alloc_req_i   ),
      .ready_o ( alloc_gnt_o   ),
      .data_i  ( alloc_pld_in  ),
      .valid_o ( alloc_req     ),
      .ready_i ( alloc_gnt     ),
      .data_o  ( alloc_pld_out )
    );
  end else begin : gen_no_spill
    assign alloc_req = alloc_req_i;
    assign alloc_gnt_o = alloc_gnt;
    assign alloc_pld_out = alloc_pld_in;
  end

  localparam int unsigned CntIdxWidth = (MaxTxns > 1) ? $clog2(MaxTxns) : 32'd1;
  typedef logic [CntIdxWidth-1:0]         cnt_idx_t;
  logic [MaxTxns-1:0]  cnt_dec, cnt_free, cnt_set, err_d, err_q, cnt_clr;
  cnt_t                cnt_inp;
  cnt_t [MaxTxns-1:0]  cnt_oup;
  cnt_idx_t            cnt_free_idx, cnt_r_idx;
  for (genvar i = 0; i < MaxTxns; i++) begin : gen_cnt
    delta_counter #(
      .WIDTH ( $bits(cnt_t) )
    ) i_cnt (
      .clk_i,
      .rst_ni,
      .clear_i    ( cnt_clr[i]   ),
      .en_i       ( cnt_dec[i]   ),
      .load_i     ( cnt_set[i]   ),
      .down_i     ( 1'b1         ),
      .delta_i    ( cnt_delta_i  ),
      .d_i        ( cnt_inp      ),
      .q_o        ( cnt_oup[i]   ),
      .overflow_o ( cnt_clr[i]   )
    );
    assign cnt_free[i] = (cnt_oup[i] == '0);
  end
  assign cnt_inp = {1'b0, alloc_pld_out.len} + 1;

  lzc #(
    .WIDTH  ( MaxTxns ),
    .MODE   ( 1'b0    )  // start counting at index 0
  ) i_lzc (
    .in_i    ( cnt_free     ),
    .cnt_o   ( cnt_free_idx ),
    .empty_o (              )
  );

  logic idq_inp_req, idq_inp_gnt,
        idq_oup_gnt, idq_oup_valid, idq_oup_pop;
  id_queue #(
    .ID_WIDTH ( $bits(id_t) ),
    .CAPACITY ( MaxTxns     ),
    .FULL_BW  ( FullBW      ),
    .data_t   ( cnt_idx_t   )
  ) i_idq (
    .clk_i,
    .rst_ni,
    .inp_id_i         ( alloc_pld_out.id ),
    .inp_data_i       ( cnt_free_idx  ),
    .inp_req_i        ( idq_inp_req   ),
    .inp_gnt_o        ( idq_inp_gnt   ),
    .exists_data_i    ( '0            ),
    .exists_mask_i    ( '0            ),
    .exists_req_i     ( 1'b0          ),
    .exists_o         (/* keep open */),
    .exists_gnt_o     (/* keep open */),
    .oup_id_i         ( cnt_id_i      ),
    .oup_pop_i        ( idq_oup_pop   ),
    .oup_req_i        ( cnt_req_i     ),
    .oup_data_o       ( cnt_r_idx     ),
    .oup_data_valid_o ( idq_oup_valid ),
    .oup_gnt_o        ( idq_oup_gnt   )
  );
  assign idq_inp_req = alloc_req   & alloc_gnt;
  assign alloc_gnt   = idq_inp_gnt & |(cnt_free);
  assign cnt_gnt_o   = idq_oup_gnt & idq_oup_valid;
  logic [8:0] read_len;
  assign read_len    = cnt_oup[cnt_r_idx] - 1;
  assign cnt_len_o   = read_len[7:0];

  assign idq_oup_pop = cnt_req_i & cnt_gnt_o & cnt_dec_i & (cnt_len_o < cnt_delta_i);
  always_comb begin
    cnt_dec            = '0;
    cnt_dec[cnt_r_idx] = cnt_req_i & cnt_gnt_o & cnt_dec_i;
  end
  always_comb begin
    cnt_set               = '0;
    cnt_set[cnt_free_idx] = alloc_req & alloc_gnt;
  end
  always_comb begin
    err_d     = err_q;
    cnt_err_o = err_q[cnt_r_idx];
    if (cnt_req_i && cnt_gnt_o && cnt_set_err_i) begin
      err_d[cnt_r_idx] = 1'b1;
      cnt_err_o        = 1'b1;
    end
    if (alloc_req && alloc_gnt) begin
      err_d[cnt_free_idx] = 1'b0;
    end
  end

  // registers
  `FFARN(err_q, err_d, '0, clk_i, rst_ni)

  `ifndef VERILATOR
  // pragma translate_off
  assume property (@(posedge clk_i) idq_oup_gnt |-> idq_oup_valid)
    else $warning("Invalid output at ID queue, read not granted!");
  // pragma translate_on
  `endif

endmodule
