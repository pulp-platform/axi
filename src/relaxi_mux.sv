// register macros
`include "common_cells/assertions.svh"
`include "common_cells/registers.svh"

module relaxi_mux #(
  parameter int unsigned SlvAxiIDWidth  = 32'd0,   // field width (now 9)
  parameter int unsigned SlvIdBits      = 32'd0,   // index position (5)
  parameter type         slv_aw_chan_t  = logic,
  parameter type         mst_aw_chan_t  = logic,
  parameter type         w_chan_t       = logic,
  parameter type         slv_b_chan_t   = logic,
  parameter type         mst_b_chan_t   = logic,
  parameter type         slv_ar_chan_t  = logic,
  parameter type         mst_ar_chan_t  = logic,
  parameter type         slv_r_chan_t   = logic,
  parameter type         mst_r_chan_t   = logic,
  parameter type         slv_req_t      = logic,
  parameter type         slv_resp_t     = logic,
  parameter type         mst_req_t      = logic,
  parameter type         mst_resp_t     = logic,
  parameter int unsigned NoSlvPorts     = 32'd0,
  parameter int unsigned MaxWTrans      = 32'd8,
  parameter bit          FallThrough    = 1'b0,
  parameter bit          SpillAw        = 1'b1,
  parameter bit          SpillW         = 1'b0,
  parameter bit          SpillB         = 1'b0,
  parameter bit          SpillAr        = 1'b1,
  parameter bit          SpillR         = 1'b0,
  // VCS fix: explicit channel widths to avoid $bits() on parametric types.
  // Must be passed from instantiation site where types are concrete.
  parameter int unsigned MstAwChanWidth = 1,
  parameter int unsigned WChanWidth     = 1,
  parameter int unsigned MstBChanWidth  = 1,
  parameter int unsigned MstArChanWidth = 1,
  parameter int unsigned MstRChanWidth  = 1
) (
  input  logic                       clk_i,
  input  logic                       rst_ni,
  input  logic                       test_i,
  input  slv_req_t  [NoSlvPorts-1:0] slv_reqs_i,
  output slv_resp_t [NoSlvPorts-1:0] slv_resps_o,
  output mst_req_t                   mst_req_o,
  input  mst_resp_t                  mst_resp_i,
  output logic [1:0]                 fault_o
);

  localparam int unsigned MstIdxBits    = $clog2(NoSlvPorts);
  localparam int unsigned MstAxiIDWidth = SlvAxiIDWidth;

  // ECC (id_prepend) contributes both bits; all TMR sources contribute corrected only
  logic [NoSlvPorts-1:0][1:0] prepend_fault; // one per gen_id_prepend instance
  logic [12:0] tmr_faults;   // 0-4: spills, 5: arb, 6: arb, 7-9: lock_aw x3,
                             // 10: w_fifo, 11: w_sel_enc vote, 12: w payload vote

  // pass through if only one slave port
  if (NoSlvPorts == 32'h1) begin : gen_no_mux
    logic [2:0] no_mux_aw_valid_slv, no_mux_aw_ready_slv;
    logic [2:0] no_mux_aw_valid_mst, no_mux_aw_ready_mst;
    logic [2:0] no_mux_w_valid_slv,  no_mux_w_ready_slv;
    logic [2:0] no_mux_w_valid_mst,  no_mux_w_ready_mst;
    logic [2:0] no_mux_b_valid_mst,  no_mux_b_ready_mst;
    logic [2:0] no_mux_b_valid_slv,  no_mux_b_ready_slv;
    logic [2:0] no_mux_ar_valid_slv, no_mux_ar_ready_slv;
    logic [2:0] no_mux_ar_valid_mst, no_mux_ar_ready_mst;
    logic [2:0] no_mux_r_valid_mst,  no_mux_r_ready_mst;
    logic [2:0] no_mux_r_valid_slv,  no_mux_r_ready_slv;
    logic [4:0] no_mux_faults;

    assign no_mux_aw_valid_slv        = slv_reqs_i[0].aw_valid;
    assign no_mux_aw_ready_mst        = mst_resp_i.aw_ready;
    assign slv_resps_o[0].aw_ready    = no_mux_aw_ready_slv;
    assign mst_req_o.aw_valid         = no_mux_aw_valid_mst;
    assign no_mux_w_valid_slv         = slv_reqs_i[0].w_valid;
    assign no_mux_w_ready_mst         = mst_resp_i.w_ready;
    assign slv_resps_o[0].w_ready     = no_mux_w_ready_slv;
    assign mst_req_o.w_valid          = no_mux_w_valid_mst;
    assign no_mux_b_valid_mst         = mst_resp_i.b_valid;
    assign no_mux_b_ready_slv         = slv_reqs_i[0].b_ready;
    assign mst_req_o.b_ready          = no_mux_b_ready_mst;
    assign slv_resps_o[0].b_valid     = no_mux_b_valid_slv;
    assign no_mux_ar_valid_slv        = slv_reqs_i[0].ar_valid;
    assign no_mux_ar_ready_mst        = mst_resp_i.ar_ready;
    assign slv_resps_o[0].ar_ready    = no_mux_ar_ready_slv;
    assign mst_req_o.ar_valid         = no_mux_ar_valid_mst;
    assign no_mux_r_valid_mst         = mst_resp_i.r_valid;
    assign no_mux_r_ready_slv         = slv_reqs_i[0].r_ready;
    assign mst_req_o.r_ready          = no_mux_r_ready_mst;
    assign slv_resps_o[0].r_valid     = no_mux_r_valid_slv;

    rel_spill_register #(
      .T            ( mst_aw_chan_t ),
      .Bypass       ( ~SpillAw     ),
      .TmrHandshake ( 1'b1         ),
      .DataCorrector( 1'b0         )
    ) i_aw_spill_reg (
      .clk_i, .rst_ni,
      .valid_i          ( no_mux_aw_valid_slv ),
      .ready_o          ( no_mux_aw_ready_slv ),
      .data_i           ( slv_reqs_i[0].aw   ),
      .valid_o          ( no_mux_aw_valid_mst ),
      .ready_i          ( no_mux_aw_ready_mst ),
      .data_o           ( mst_req_o.aw        ),
      .fault_o          ( no_mux_faults[0]    ),
      .data_corrector_o (                     ),
      .data_corrected_i ( '0                  )
    );
    rel_spill_register #(
      .T            ( w_chan_t ),
      .Bypass       ( ~SpillW ),
      .TmrHandshake ( 1'b1   ),
      .DataCorrector( 1'b0   )
    ) i_w_spill_reg (
      .clk_i, .rst_ni,
      .valid_i          ( no_mux_w_valid_slv ),
      .ready_o          ( no_mux_w_ready_slv ),
      .data_i           ( slv_reqs_i[0].w   ),
      .valid_o          ( no_mux_w_valid_mst ),
      .ready_i          ( no_mux_w_ready_mst ),
      .data_o           ( mst_req_o.w        ),
      .fault_o          ( no_mux_faults[1]   ),
      .data_corrector_o (                    ),
      .data_corrected_i ( '0                 )
    );
    rel_spill_register #(
      .T            ( mst_b_chan_t ),
      .Bypass       ( ~SpillB     ),
      .TmrHandshake ( 1'b1        ),
      .DataCorrector( 1'b0        )
    ) i_b_spill_reg (
      .clk_i, .rst_ni,
      .valid_i          ( no_mux_b_valid_mst ),
      .ready_o          ( no_mux_b_ready_mst ),
      .data_i           ( mst_resp_i.b       ),
      .valid_o          ( no_mux_b_valid_slv ),
      .ready_i          ( no_mux_b_ready_slv ),
      .data_o           ( slv_resps_o[0].b   ),
      .fault_o          ( no_mux_faults[2]   ),
      .data_corrector_o (                    ),
      .data_corrected_i ( '0                 )
    );
    rel_spill_register #(
      .T            ( mst_ar_chan_t ),
      .Bypass       ( ~SpillAr     ),
      .TmrHandshake ( 1'b1         ),
      .DataCorrector( 1'b0         )
    ) i_ar_spill_reg (
      .clk_i, .rst_ni,
      .valid_i          ( no_mux_ar_valid_slv ),
      .ready_o          ( no_mux_ar_ready_slv ),
      .data_i           ( slv_reqs_i[0].ar   ),
      .valid_o          ( no_mux_ar_valid_mst ),
      .ready_i          ( no_mux_ar_ready_mst ),
      .data_o           ( mst_req_o.ar        ),
      .fault_o          ( no_mux_faults[3]    ),
      .data_corrector_o (                     ),
      .data_corrected_i ( '0                  )
    );
    rel_spill_register #(
      .T            ( mst_r_chan_t ),
      .Bypass       ( ~SpillR     ),
      .TmrHandshake ( 1'b1        ),
      .DataCorrector( 1'b0        )
    ) i_r_spill_reg (
      .clk_i, .rst_ni,
      .valid_i          ( no_mux_r_valid_mst ),
      .ready_o          ( no_mux_r_ready_mst ),
      .data_i           ( mst_resp_i.r       ),
      .valid_o          ( no_mux_r_valid_slv ),
      .ready_i          ( no_mux_r_ready_slv ),
      .data_o           ( slv_resps_o[0].r   ),
      .fault_o          ( no_mux_faults[4]   ),
      .data_corrector_o (                    ),
      .data_corrected_i ( '0                 )
    );

    assign fault_o[0] = |no_mux_faults;
    assign fault_o[1] = 1'b0;

// pragma translate_off
    `ASSERT_INIT(CorrectIdWidthSlvAw, $bits(slv_reqs_i[0].aw.id) == SlvAxiIDWidth)
    `ASSERT_INIT(CorrectIdWidthSlvB,  $bits(slv_resps_o[0].b.id) == SlvAxiIDWidth)
    `ASSERT_INIT(CorrectIdWidthSlvAr, $bits(slv_reqs_i[0].ar.id) == SlvAxiIDWidth)
    `ASSERT_INIT(CorrectIdWidthSlvR,  $bits(slv_resps_o[0].r.id) == SlvAxiIDWidth)
    `ASSERT_INIT(CorrectIdWidthMstAw, $bits(mst_req_o.aw.id)     == SlvAxiIDWidth)
    `ASSERT_INIT(CorrectIdWidthMstB,  $bits(mst_resp_i.b.id)     == SlvAxiIDWidth)
    `ASSERT_INIT(CorrectIdWidthMstAr, $bits(mst_req_o.ar.id)     == SlvAxiIDWidth)
    `ASSERT_INIT(CorrectIdWidthMstR,  $bits(mst_resp_i.r.id)     == SlvAxiIDWidth)
// pragma translate_on

  end else begin : gen_mux

    typedef logic [MstIdxBits-1:0] switch_id_t;
    logic [2:0][MstIdxBits-1:0] aw_arb_idx;

    // ---------------------------------------------------------------
    // VCS fix: declare channel arrays and locals as flat logic vectors.
    // Packed arrays of parametric struct types are not correctly
    // elaborated by VCS — $bits() on parametric types returns wrong
    // values, causing signals to be missing or misaligned.
    // Use explicit widths passed from instantiation site instead.
    // ---------------------------------------------------------------
    logic [NoSlvPorts-1:0][MstAwChanWidth-1:0] slv_aw_chans;
    logic [NoSlvPorts-1:0][2:0]                slv_aw_valids, slv_aw_readies;
    logic [NoSlvPorts-1:0][WChanWidth-1:0]     slv_w_chans;
    logic [NoSlvPorts-1:0][2:0]                slv_w_valids,  slv_w_readies;
    logic [NoSlvPorts-1:0][MstBChanWidth-1:0]  slv_b_chans;
    logic [NoSlvPorts-1:0][2:0]                slv_b_valids,  slv_b_readies;
    logic [NoSlvPorts-1:0][MstArChanWidth-1:0] slv_ar_chans;
    logic [NoSlvPorts-1:0][2:0]                slv_ar_valids, slv_ar_readies;
    logic [NoSlvPorts-1:0][MstRChanWidth-1:0]  slv_r_chans;
    logic [NoSlvPorts-1:0][2:0]                slv_r_valids,  slv_r_readies;

    // Flat logic locals for channel data
    logic [MstAwChanWidth-1:0] mst_aw_chan;
    logic [WChanWidth-1:0]     mst_w_chan;
    logic [MstBChanWidth-1:0]  mst_b_chan;
    logic [MstArChanWidth-1:0] mst_ar_chan;
    logic [MstRChanWidth-1:0]  mst_r_chan;

    // Struct-typed views for field access — assigned from flat logic.
    // QuestaSim does not support type_t'(expr).field in one expression,
    // so we use intermediate struct signals.
    mst_aw_chan_t mst_aw_chan_s;
    w_chan_t      mst_w_chan_s;
    mst_b_chan_t  mst_b_chan_s;
    mst_ar_chan_t mst_ar_chan_s;
    mst_r_chan_t  mst_r_chan_s;

    assign mst_aw_chan_s = mst_aw_chan_t'(mst_aw_chan);
    assign mst_w_chan_s  = w_chan_t'(mst_w_chan);
    assign mst_b_chan_s  = mst_b_chan_t'(mst_b_chan);
    assign mst_ar_chan_s = mst_ar_chan_t'(mst_ar_chan);
    assign mst_r_chan_s  = mst_r_chan_t'(mst_r_chan);

    logic [2:0]      mst_aw_valid, mst_aw_ready;
    logic [2:0]      aw_valid,     aw_ready;
    logic [2:0]      lock_aw_valid_d, lock_aw_valid_q, lock_aw_valid_next;
    logic [2:0]      load_aw_lock;
    logic [2:0][1:0] alt_lock_aw_valid;
    logic [2:0]      w_fifo_full, w_fifo_empty;
    logic [2:0]      w_fifo_push, w_fifo_pop;

    logic [2:0]      mst_w_valid, mst_w_ready;

    logic [2:0]                    mst_b_valid;
    logic [2:0]                    ar_valid, ar_ready;
    logic [2:0]                    mst_r_valid;

    // Triplicated decode and steering wires for B and R
    logic [2:0][MstAxiIDWidth-1:0] b_id_corr,      r_id_corr;
    logic [2:0][1:0]               b_id_dec_fault, r_id_dec_fault;
    switch_id_t [2:0]              switch_b_id,    switch_r_id;
    logic [2:0]                    b_sel_oor,      r_sel_oor;
    switch_id_t [2:0]              b_sel_safe,     r_sel_safe;

    localparam int unsigned SelEcc = hsiao_ecc_pkg::min_ecc(MstIdxBits);
    localparam int unsigned SelCw  = MstIdxBits + SelEcc;

    logic [2:0][SelCw-1:0]      w_sel_enc_tmr;     // three encoders
    logic [SelCw-1:0]           w_sel_enc_voted;   // voted codeword into FIFO
    logic [SelCw-1:0]           w_sel_enc_q;       // codeword out of FIFO
    logic [2:0][MstIdxBits-1:0] w_sel_rep;         // three decoders
    logic [2:0][1:0]            w_sel_dec_fault;   // per-replica err_o
    logic [1:0]                 w_sel_dec_reduced;

    logic [2:0] mux_aw_valid_o, mux_aw_ready_i;
    logic [2:0] mux_w_valid_o,  mux_w_ready_i;
    logic [2:0] mux_b_valid_i,  mux_b_ready_o;
    logic [2:0] mux_ar_valid_o, mux_ar_ready_i;
    logic [2:0] mux_r_valid_i,  mux_r_ready_o;

    assign mst_req_o.aw_valid = mux_aw_valid_o;
    assign mux_aw_ready_i     = mst_resp_i.aw_ready;
    assign mst_req_o.w_valid  = mux_w_valid_o;
    assign mux_w_ready_i      = mst_resp_i.w_ready;
    assign mux_b_valid_i      = mst_resp_i.b_valid;
    assign mst_req_o.b_ready  = mux_b_ready_o;
    assign mst_req_o.ar_valid = mux_ar_valid_o;
    assign mux_ar_ready_i     = mst_resp_i.ar_ready;
    assign mux_r_valid_i      = mst_resp_i.r_valid;
    assign mst_req_o.r_ready  = mux_r_ready_o;

    //--------------------------------------
    // ID prepend for all slave ports
    //--------------------------------------
    for (genvar i = 0; i < NoSlvPorts; i++) begin : gen_id_prepend
      localparam [MstIdxBits-1:0] SLV_IDX = i;
      relaxi_id_prepend #(
        .NoBus             ( 32'd1         ),
        .AxiIdWidthSlvPort ( SlvIdBits     ),
        .AxiIdWidthMstPort ( SlvAxiIDWidth ),
        .slv_aw_chan_t     ( slv_aw_chan_t ),
        .slv_w_chan_t      ( w_chan_t      ),
        .slv_b_chan_t      ( slv_b_chan_t  ),
        .slv_ar_chan_t     ( slv_ar_chan_t ),
        .slv_r_chan_t      ( slv_r_chan_t  ),
        .mst_aw_chan_t     ( mst_aw_chan_t ),
        .mst_w_chan_t      ( w_chan_t      ),
        .mst_b_chan_t      ( mst_b_chan_t  ),
        .mst_ar_chan_t     ( mst_ar_chan_t ),
        .mst_r_chan_t      ( mst_r_chan_t  )
      ) i_id_prepend (
        .pre_id_i         ( switch_id_t'(i)         ),
        .slv_aw_chans_i   ( slv_reqs_i[i].aw        ),
        .slv_aw_valids_i  ( slv_reqs_i[i].aw_valid  ),
        .slv_aw_readies_o ( slv_resps_o[i].aw_ready ),
        .slv_w_chans_i    ( slv_reqs_i[i].w         ),
        .slv_w_valids_i   ( slv_reqs_i[i].w_valid   ),
        .slv_w_readies_o  ( slv_resps_o[i].w_ready  ),
        .slv_b_chans_o    ( slv_resps_o[i].b        ),
        .slv_b_valids_o   ( slv_resps_o[i].b_valid  ),
        .slv_b_readies_i  ( slv_reqs_i[i].b_ready   ),
        .slv_ar_chans_i   ( slv_reqs_i[i].ar        ),
        .slv_ar_valids_i  ( slv_reqs_i[i].ar_valid  ),
        .slv_ar_readies_o ( slv_resps_o[i].ar_ready ),
        .slv_r_chans_o    ( slv_resps_o[i].r        ),
        .slv_r_valids_o   ( slv_resps_o[i].r_valid  ),
        .slv_r_readies_i  ( slv_reqs_i[i].r_ready   ),
        .mst_aw_chans_o   ( slv_aw_chans[i]         ),
        .mst_aw_valids_o  ( slv_aw_valids[i]        ),
        .mst_aw_readies_i ( slv_aw_readies[i]       ),
        .mst_w_chans_o    ( slv_w_chans[i]          ),
        .mst_w_valids_o   ( slv_w_valids[i]         ),
        .mst_w_readies_i  ( slv_w_readies[i]        ),
        .mst_b_chans_i    ( slv_b_chans[i]          ),
        .mst_b_valids_i   ( slv_b_valids[i]         ),
        .mst_b_readies_o  ( slv_b_readies[i]        ),
        .mst_ar_chans_o   ( slv_ar_chans[i]         ),
        .mst_ar_valids_o  ( slv_ar_valids[i]        ),
        .mst_ar_readies_i ( slv_ar_readies[i]       ),
        .mst_r_chans_i    ( slv_r_chans[i]          ),
        .mst_r_valids_i   ( slv_r_valids[i]         ),
        .mst_r_readies_o  ( slv_r_readies[i]        ),
        .fault_o          ( prepend_fault[i]        ) // 2-bit
      );
    end

    //--------------------------------------
    // AW Channel
    //--------------------------------------
    rel_rr_arb_tree #(
      .NumIn    ( NoSlvPorts    ),
      .DataType ( mst_aw_chan_t ),
      .AxiVldRdy( 1'b1          ),
      .LockIn   ( 1'b1          ),
      .TmrStatus( 1'b1          )
    ) i_aw_arbiter (
      .clk_i   ( clk_i          ),
      .rst_ni  ( rst_ni         ),
      .flush_i ( 1'b0           ),
      .rr_i    ( '0             ),
      .req_i   ( slv_aw_valids  ),
      .gnt_o   ( slv_aw_readies ),
      .data_i  ( slv_aw_chans   ),
      .gnt_i   ( aw_ready       ),
      .req_o   ( aw_valid       ),
      .data_o  ( mst_aw_chan    ),
      .idx_o   ( aw_arb_idx     ),
      .fault_o ( tmr_faults[5]  )
    );

    for (genvar i = 0; i < 3; i++) begin
      always_comb begin
        lock_aw_valid_d[i] = lock_aw_valid_q[i];
        load_aw_lock[i]    = 1'b0;
        w_fifo_push[i]     = 1'b0;
        mst_aw_valid[i]    = 1'b0;
        aw_ready[i]        = 1'b0;
        if (lock_aw_valid_q[i]) begin
          mst_aw_valid[i] = 1'b1;
          if (mst_aw_ready[i]) begin
            aw_ready[i]        = 1'b1;
            lock_aw_valid_d[i] = 1'b0;
            load_aw_lock[i]    = 1'b1;
          end
        end else begin
          if (!w_fifo_full[i] && aw_valid[i]) begin
            mst_aw_valid[i] = 1'b1;
            w_fifo_push[i]  = 1'b1;
            if (mst_aw_ready[i]) begin
              aw_ready[i] = 1'b1;
            end else begin
              lock_aw_valid_d[i] = 1'b1;
              load_aw_lock[i]    = 1'b1;
            end
          end
        end
      end
    end

    for (genvar i = 0; i < 3; i++) begin : gen_lock_aw_alt
      for (genvar j = 0; j < 2; j++) begin
        assign alt_lock_aw_valid[i][j] = lock_aw_valid_next[(i+j+1) % 3];
      end
    end

    for (genvar i = 0; i < 3; i++) begin : gen_lock_aw
      TMR_voter_fail #(.VoterType(1)) i_lock_aw_voted (
        .a_i              ( lock_aw_valid_next[i]   ),
        .b_i              ( alt_lock_aw_valid[i][0] ),
        .c_i              ( alt_lock_aw_valid[i][1] ),
        .majority_o       ( lock_aw_valid_q[i]      ),
        .fault_detected_o ( tmr_faults[7+i]         )   // 7,8,9 (distinct per replica)
      );

      always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni)              lock_aw_valid_next[i] <= 1'b0;
        else if (load_aw_lock[i]) lock_aw_valid_next[i] <= lock_aw_valid_d[i];
        else                      lock_aw_valid_next[i] <= lock_aw_valid_q[i];
      end
    end

    for (genvar i = 0; i < 3; i++) begin : gen_w_sel_enc
      hsiao_ecc_enc #(
        .DataWidth ( MstIdxBits )
      ) i_enc (
        .in  ( aw_arb_idx[i]    ),
        .out ( w_sel_enc_tmr[i] )
      );
    end

    bitwise_TMR_voter_fail #(
      .DataWidth ( SelCw ),
      .VoterType ( 1     )
    ) i_w_sel_enc_vote (
      .a_i              ( w_sel_enc_tmr[0] ),
      .b_i              ( w_sel_enc_tmr[1] ),
      .c_i              ( w_sel_enc_tmr[2] ),
      .majority_o       ( w_sel_enc_voted  ),
      .fault_detected_o ( tmr_faults[11]   )
    );

    rel_fifo #(
      .FallThrough ( FallThrough ),
      .DataWidth   ( SelCw       ),
      .Depth       ( MaxWTrans   ),
      .TmrStatus   ( 1'b1        ),
      .DataHasEcc  ( 1'b1        )
    ) i_w_fifo (
      .clk_i,
      .rst_ni,
      .flush_i    ( '0                                              ),
      .testmode_i ( test_i                                          ),
      .full_o     ( w_fifo_full                                     ),
      .empty_o    ( w_fifo_empty                                    ),
      .usage_o    (                                                 ),
      // Use struct view for field access
      .data_i     ( w_sel_enc_voted                                 ),
      .push_i     ( w_fifo_push                                     ),
      .data_o     ( w_sel_enc_q                                     ),
      .pop_i      ( w_fifo_pop                                      ),
      .fault_o    ( tmr_faults[10]                                  )
    );

    for (genvar i = 0; i < 3; i++) begin : gen_w_sel_dec
      hsiao_ecc_dec #(
        .DataWidth ( MstIdxBits )
      ) i_dec (
        .in         ( w_sel_enc_q        ),
        .out        ( w_sel_rep[i]       ),
        .syndrome_o (                    ),
        .err_o      ( w_sel_dec_fault[i] )
      );
    end

    rel_spill_register #(
      .T            ( mst_aw_chan_t ),
      .Bypass       ( ~SpillAw     ),
      .TmrHandshake ( 1'b1         ),
      .DataCorrector( 1'b0         )
    ) i_aw_spill_reg (
      .clk_i, .rst_ni,
      .valid_i          ( mst_aw_valid   ),
      .ready_o          ( mst_aw_ready   ),
      .data_i           ( mst_aw_chan    ),
      .valid_o          ( mux_aw_valid_o ),
      .ready_i          ( mux_aw_ready_i ),
      .data_o           ( mst_req_o.aw   ),
      .fault_o          ( tmr_faults[0]  ),
      .data_corrector_o (                ),
      .data_corrected_i ( '0             )
    );

    //--------------------------------------
    // W Channel
    //--------------------------------------

    // Three independent payload paths on the per-replica selects, voted per
    // bit at the ECC boundary. A fault in one replica's select corrupts that
    // path entirely and is outvoted; a fault on any voter output alters one
    // payload bit and stays within SECDED range.
    localparam int unsigned WChanBits = $bits(w_chan_t);

    logic [2:0][WChanBits-1:0] w_payload_raw;
    logic      [WChanBits-1:0] w_payload, w_payload_faults;

    for (genvar r = 0; r < 3; r++) begin : gen_w_mux_rep
      always_comb begin
        w_payload_raw[r] = '0;
        for (int unsigned j = 0; j < NoSlvPorts; j++)
          if (w_sel_rep[r] == switch_id_t'(j)) w_payload_raw[r] = slv_w_chans[j];
      end
    end

    for (genvar b = 0; b < WChanBits; b++) begin : gen_w_payload_vote
      TMR_voter_fail #(.VoterType(1)) i_w_vote (
        .a_i              ( w_payload_raw[0][b] ),
        .b_i              ( w_payload_raw[1][b] ),
        .c_i              ( w_payload_raw[2][b] ),
        .majority_o       ( w_payload[b]        ),
        .fault_detected_o ( w_payload_faults[b] )
      );
    end

    assign tmr_faults[12] = |w_payload_faults;
    assign mst_w_chan = w_payload;

    always_comb begin
      mst_w_valid   = '0;
      slv_w_readies = '0;
      w_fifo_pop    = '0;
      for (int i = 0; i < 3; i++) begin
        if (!w_fifo_empty[i] && (w_sel_rep[i] < NoSlvPorts)) begin
          mst_w_valid[i]                 = slv_w_valids[w_sel_rep[i]][i];
          slv_w_readies[w_sel_rep[i]][i] = mst_w_ready[i];
          w_fifo_pop[i] = slv_w_valids[w_sel_rep[i]][i] & mst_w_ready[i]
                          & mst_w_chan_s.last[i];
        end
      end
    end

    rel_spill_register #(
      .T            ( w_chan_t ),
      .Bypass       ( ~SpillW ),
      .TmrHandshake ( 1'b1   ),
      .DataCorrector( 1'b0   )
    ) i_w_spill_reg (
      .clk_i, .rst_ni,
      .valid_i          ( mst_w_valid   ),
      .ready_o          ( mst_w_ready   ),
      .data_i           ( mst_w_chan    ),
      .valid_o          ( mux_w_valid_o ),
      .ready_i          ( mux_w_ready_i ),
      .data_o           ( mst_req_o.w   ),
      .fault_o          ( tmr_faults[1] ),
      .data_corrector_o (               ),
      .data_corrected_i ( '0            )
    );

    //--------------------------------------
    // B Channel
    //--------------------------------------
    // Replicate B channel using genvar to avoid struct replication in VCS
    for (genvar i = 0; i < NoSlvPorts; i++) begin : gen_b_chan_replicate
      assign slv_b_chans[i] = mst_b_chan;
    end

    for (genvar r = 0; r < 3; r++) begin : gen_b_id_dec
      relaxi_id_dec #(
        .IdWidth ( MstAxiIDWidth )
      ) i_b_dec (
        .id_i     ( mst_b_chan_s.id     ),
        .id_ecc_i ( mst_b_chan_s.id_ecc ),
        .id_o     ( b_id_corr[r]        ),
        .err_o    ( b_id_dec_fault[r]   )
      );
      assign switch_b_id[r] = b_id_corr[r][SlvIdBits +: MstIdxBits];
      assign b_sel_oor[r]   = (switch_b_id[r] >= NoSlvPorts);
      assign b_sel_safe[r]  = b_sel_oor[r] ? '0 : switch_b_id[r];
    end

    for (genvar j = 0; j < NoSlvPorts; j++) begin : gen_b_valid_slv
      for (genvar r = 0; r < 3; r++) begin : gen_b_valid_tmr
        assign slv_b_valids[j][r] = mst_b_valid[r]
                                  & (b_sel_safe[r] == j)
                                  & !b_sel_oor[r]
                                  & !b_id_dec_fault[r][1];
      end
    end

    // Route the backward ready signal per-replica to maintain total isolation
    logic [2:0] b_ready_in_tmr;
    for (genvar r = 0; r < 3; r++) begin : gen_b_ready_mux
      assign b_ready_in_tmr[r] = slv_b_readies[b_sel_safe[r]][r];
    end

    rel_spill_register #(
      .T            ( mst_b_chan_t ),
      .Bypass       ( ~SpillB     ),
      .TmrHandshake ( 1'b1        ),
      .DataCorrector( 1'b0        )
    ) i_b_spill_reg (
      .clk_i, .rst_ni,
      .valid_i          ( mux_b_valid_i              ),
      .ready_o          ( mux_b_ready_o              ),
      .data_i           ( mst_resp_i.b               ),
      .valid_o          ( mst_b_valid                ),
      .ready_i          ( b_ready_in_tmr             ),
      .data_o           ( mst_b_chan                 ),
      .fault_o          ( tmr_faults[2]              ),
      .data_corrector_o (                            ),
      .data_corrected_i ( '0                         )
    );

    //--------------------------------------
    // AR Channel
    //--------------------------------------
    rel_rr_arb_tree #(
      .NumIn    ( NoSlvPorts    ),
      .DataType ( mst_ar_chan_t ),
      .AxiVldRdy( 1'b1          ),
      .LockIn   ( 1'b1          ),
      .TmrStatus( 1'b1          )
    ) i_ar_arbiter (
      .clk_i   ( clk_i          ),
      .rst_ni  ( rst_ni         ),
      .flush_i ( 1'b0           ),
      .rr_i    ( '0             ),
      .req_i   ( slv_ar_valids  ),
      .gnt_o   ( slv_ar_readies ),
      .data_i  ( slv_ar_chans   ),
      .gnt_i   ( ar_ready       ),
      .req_o   ( ar_valid       ),
      .data_o  ( mst_ar_chan    ),
      .idx_o   (                ),
      .fault_o ( tmr_faults[6]  )
    );

    rel_spill_register #(
      .T            ( mst_ar_chan_t ),
      .Bypass       ( ~SpillAr     ),
      .TmrHandshake ( 1'b1         ),
      .DataCorrector( 1'b0         )
    ) i_ar_spill_reg (
      .clk_i, .rst_ni,
      .valid_i          ( ar_valid       ),
      .ready_o          ( ar_ready       ),
      .data_i           ( mst_ar_chan    ),
      .valid_o          ( mux_ar_valid_o ),
      .ready_i          ( mux_ar_ready_i ),
      .data_o           ( mst_req_o.ar   ),
      .fault_o          ( tmr_faults[3]  ),
      .data_corrector_o (               ),
      .data_corrected_i ( '0            )
    );

    //--------------------------------------
    // R Channel
    //--------------------------------------
    // Replicate R channel using genvar
    for (genvar i = 0; i < NoSlvPorts; i++) begin : gen_r_chan_replicate
      assign slv_r_chans[i] = mst_r_chan;
    end

    for (genvar r = 0; r < 3; r++) begin : gen_r_id_dec
      relaxi_id_dec #(
        .IdWidth ( MstAxiIDWidth )
      ) i_r_dec (
        .id_i     ( mst_r_chan_s.id     ),
        .id_ecc_i ( mst_r_chan_s.id_ecc ),
        .id_o     ( r_id_corr[r]        ),
        .err_o    ( r_id_dec_fault[r]   )
      );
      assign switch_r_id[r] = r_id_corr[r][SlvIdBits +: MstIdxBits];
      assign r_sel_oor[r]   = (switch_r_id[r] >= NoSlvPorts);
      assign r_sel_safe[r]  = r_sel_oor[r] ? '0 : switch_r_id[r];
    end

    for (genvar j = 0; j < NoSlvPorts; j++) begin : gen_r_valid_slv
      for (genvar r = 0; r < 3; r++) begin : gen_r_valid_tmr
        assign slv_r_valids[j][r] = mst_r_valid[r]
                                  & (r_sel_safe[r] == j)
                                  & !r_sel_oor[r]
                                  & !r_id_dec_fault[r][1];
      end
    end

    // from up by the B channel on line 407, and place it here:
    logic [2:0] r_ready_in_tmr;
    for (genvar r = 0; r < 3; r++) begin : gen_r_ready_mux
      assign r_ready_in_tmr[r] = slv_r_readies[r_sel_safe[r]][r];
    end

    rel_spill_register #(
      .T            ( mst_r_chan_t ),
      .Bypass       ( ~SpillR     ),
      .TmrHandshake ( 1'b1        ),
      .DataCorrector( 1'b0        )
    ) i_r_spill_reg (
      .clk_i, .rst_ni,
      .valid_i          ( mux_r_valid_i              ),
      .ready_o          ( mux_r_ready_o              ),
      .data_i           ( mst_resp_i.r               ),
      .valid_o          ( mst_r_valid                ),
      .ready_i          ( r_ready_in_tmr             ),
      .data_o           ( mst_r_chan                 ),
      .fault_o          ( tmr_faults[4]              ),
      .data_corrector_o (                            ),
      .data_corrected_i ( '0                         )
    );

    logic [1:0] prepend_fault_reduced;
    always_comb begin
      prepend_fault_reduced = 2'b00;
      for (int k = 0; k < NoSlvPorts; k++)
        prepend_fault_reduced |= prepend_fault[k];
    end

    logic [1:0] b_id_dec_reduced, r_id_dec_reduced;
    logic       sel_oor_any;

    always_comb begin
      w_sel_dec_reduced = 2'b00;
      b_id_dec_reduced  = 2'b00;
      r_id_dec_reduced  = 2'b00;
      sel_oor_any       = 1'b0;
      for (int i = 0; i < 3; i++) begin
        w_sel_dec_reduced |= w_sel_dec_fault[i];
        if (mst_b_valid[i]) begin
          b_id_dec_reduced |= b_id_dec_fault[i];
          sel_oor_any      |= b_sel_oor[i];
        end
        if (mst_r_valid[i]) begin
          r_id_dec_reduced |= r_id_dec_fault[i];
          sel_oor_any      |= r_sel_oor[i];
        end
      end
    end

    assign fault_o[0] = prepend_fault_reduced[0] | |tmr_faults | w_sel_dec_reduced[0]
                      | b_id_dec_reduced[0] | r_id_dec_reduced[0];
    assign fault_o[1] = prepend_fault_reduced[1] | w_sel_dec_reduced[1]
                      | b_id_dec_reduced[1] | r_id_dec_reduced[1] | sel_oor_any;
  end

// pragma translate_off
`ifndef VERILATOR
  initial begin
    assert (SlvAxiIDWidth > 0) else $fatal(1, "AXI ID width of slave ports must be non-zero!");
    assert (NoSlvPorts > 0)    else $fatal(1, "Number of slave ports must be non-zero!");
    assert (MaxWTrans > 0)     else $fatal(1, "Maximum outstanding writes must be non-zero!");
    assert ($unsigned($bits(slv_reqs_i[0].aw.id)) == SlvAxiIDWidth)
      else $fatal(1, "ID width of AW channel of slave ports does not match parameter!");
    assert ($unsigned($bits(slv_reqs_i[0].ar.id)) == SlvAxiIDWidth)
      else $fatal(1, "ID width of AR channel of slave ports does not match parameter!");
    assert ($unsigned($bits(slv_resps_o[0].b.id)) == SlvAxiIDWidth)
      else $fatal(1, "ID width of B channel of slave ports does not match parameter!");
    assert ($unsigned($bits(slv_resps_o[0].r.id)) == SlvAxiIDWidth)
      else $fatal(1, "ID width of R channel of slave ports does not match parameter!");
    assert ($unsigned($bits(mst_req_o.aw.id)) == MstAxiIDWidth)
      else $fatal(1, "ID width of AW channel of master port is wrong!");
    assert ($unsigned($bits(mst_req_o.ar.id)) == MstAxiIDWidth)
      else $fatal(1, "ID width of AR channel of master port is wrong!");
    assert ($unsigned($bits(mst_resp_i.b.id)) == MstAxiIDWidth)
      else $fatal(1, "ID width of B channel of master port is wrong!");
    assert ($unsigned($bits(mst_resp_i.r.id)) == MstAxiIDWidth)
      else $fatal(1, "ID width of R channel of master port is wrong!");
    assert (MstAwChanWidth == $bits(mst_aw_chan_t))
      else $fatal(1, "MstAwChanWidth does not match $bits(mst_aw_chan_t)!");
    assert (WChanWidth == $bits(w_chan_t))
      else $fatal(1, "WChanWidth does not match $bits(w_chan_t)!");
    assert (MstBChanWidth == $bits(mst_b_chan_t))
      else $fatal(1, "MstBChanWidth does not match $bits(mst_b_chan_t)!");
    assert (MstArChanWidth == $bits(mst_ar_chan_t))
      else $fatal(1, "MstArChanWidth does not match $bits(mst_ar_chan_t)!");
    assert (MstRChanWidth == $bits(mst_r_chan_t))
      else $fatal(1, "MstRChanWidth does not match $bits(mst_r_chan_t)!");
  end
`endif
// pragma translate_on
endmodule
