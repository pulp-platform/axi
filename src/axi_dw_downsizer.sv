// Copyright 2020 ETH Zurich and University of Bologna.
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
// - Matheus Cavalcante <matheusd@iis.ee.ethz.ch>

// Description:
// Data width downsize conversion.
// Connects a wide manager to a narrower subordinate.

// NOTE: The downsizer does not support WRAP bursts, and will answer with SLVERR
// upon receiving a burst of such type.  The downsizer does support FIXED
// bursts, but only if they consist of a single beat; it will answer with SLVERR
// on multi-beat FIXED bursts.
module axi_dw_downsizer #(
    parameter int unsigned MaxReads         = 1    , // Number of outstanding reads
    parameter int unsigned SbrPortDataWidth = 8    , // Data width of the sbr port
    parameter int unsigned MgrPortDataWidth = 8    , // Data width of the mgr port
    parameter int unsigned AddrWidth        = 1    , // Address width
    parameter int unsigned IdWidth          = 1    , // ID width
    parameter type aw_chan_t                = logic, // AW Channel Type
    parameter type mgr_w_chan_t             = logic, //  W Channel Type for mgr port
    parameter type sbr_w_chan_t             = logic, //  W Channel Type for sbr port
    parameter type b_chan_t                 = logic, //  B Channel Type
    parameter type ar_chan_t                = logic, // AR Channel Type
    parameter type mgr_r_chan_t             = logic, //  R Channel Type for mgr port
    parameter type sbr_r_chan_t             = logic, //  R Channel Type for sbr port
    parameter type mgr_port_axi_req_t       = logic, // AXI Request Type for mgr ports
    parameter type mgr_port_axi_rsp_t       = logic, // AXI Response Type for mgr ports
    parameter type sbr_port_axi_req_t       = logic, // AXI Request Type for sbr ports
    parameter type sbr_port_axi_rsp_t       = logic  // AXI Response Type for sbr ports
  ) (
    input  logic              clk_i,
    input  logic              rst_ni,
    // Subordinate interface
    input  sbr_port_axi_req_t sbr_port_req_i,
    output sbr_port_axi_rsp_t sbr_port_rsp_o,
    // Manager interface
    output mgr_port_axi_req_t mgr_port_req_o,
    input  mgr_port_axi_rsp_t mgr_port_rsp_i
  );

  /*****************
   *  DEFINITIONS  *
   *****************/
  import axi_pkg::aligned_addr;
  import axi_pkg::modifiable  ;

  import cf_math_pkg::idx_width;

  // Type used to index which adapter is handling each outstanding transaction.
  localparam TranIdWidth = MaxReads > 1 ? $clog2(MaxReads) : 1;
  typedef logic [TranIdWidth-1:0] tran_id_t;

  // Data width
  localparam SbrPortStrbWidth = SbrPortDataWidth / 8;
  localparam MgrPortStrbWidth = MgrPortDataWidth / 8;

  localparam SbrPortMaxSize = $clog2(SbrPortStrbWidth);
  localparam MgrPortMaxSize = $clog2(MgrPortStrbWidth);

  localparam SbrPortByteMask = SbrPortStrbWidth - 1;
  localparam MgrPortByteMask = MgrPortStrbWidth - 1;

  // Byte-grouped data words
  typedef logic [MgrPortStrbWidth-1:0][7:0] mgr_data_t;
  typedef logic [SbrPortStrbWidth-1:0][7:0] sbr_data_t;

  // Address width
  typedef logic [AddrWidth-1:0] addr_t;

  // ID width
  typedef logic [IdWidth-1:0] id_t;

  // Length of burst after upsizing
  typedef logic [$clog2(SbrPortStrbWidth/MgrPortStrbWidth) + 7:0] burst_len_t;

  // Internal AXI bus
  mgr_port_axi_req_t mgr_req;
  mgr_port_axi_rsp_t mgr_rsp;

  /**************
   *  ARBITERS  *
   **************/

  // R

  sbr_r_chan_t [MaxReads-1:0] sbr_r_tran;
  logic        [MaxReads-1:0] sbr_r_valid_tran;
  logic        [MaxReads-1:0] sbr_r_ready_tran;

  rr_arb_tree #(
    .NumIn    (MaxReads    ),
    .DataType (sbr_r_chan_t),
    .AxiVldRdy(1'b1        ),
    .ExtPrio  (1'b0        ),
    .LockIn   (1'b1        )
  ) i_sbr_r_arb (
    .clk_i  (clk_i            ),
    .rst_ni (rst_ni           ),
    .flush_i(1'b0             ),
    .rr_i   ('0               ),
    .req_i  (sbr_r_valid_tran ),
    .gnt_o  (sbr_r_ready_tran ),
    .data_i (sbr_r_tran       ),
    .gnt_i  (sbr_port_req_i.r_ready),
    .req_o  (sbr_port_rsp_o.r_valid),
    .data_o (sbr_port_rsp_o.r      ),
    .idx_o  (/* Unused */     )
  );

  logic [MaxReads-1:0] mgr_r_ready_tran;
  assign mgr_req.r_ready = |mgr_r_ready_tran;

  // AR

  id_t                 arb_sbr_ar_id;
  logic                arb_sbr_ar_req;
  logic                arb_sbr_ar_gnt;
  logic [MaxReads-1:0] arb_sbr_ar_gnt_tran;
  // Multiplex AR subordinate between AR and AW for the injection of atomic operations with an R response.
  logic                inject_aw_into_ar;
  logic                inject_aw_into_ar_req;
  logic                inject_aw_into_ar_gnt;

  assign arb_sbr_ar_gnt = |arb_sbr_ar_gnt_tran;

  rr_arb_tree #(
    .NumIn     (2      ),
    .DataWidth (IdWidth),
    .ExtPrio   (1'b0   ),
    .AxiVldRdy (1'b1   ),
    .LockIn    (1'b0   )
  ) i_sbr_ar_arb (
    .clk_i   (clk_i                                      ),
    .rst_ni  (rst_ni                                     ),
    .flush_i (1'b0                                       ),
    .rr_i    ('0                                         ),
    .req_i   ({inject_aw_into_ar_req, sbr_port_req_i.ar_valid}),
    .gnt_o   ({inject_aw_into_ar_gnt, sbr_port_rsp_o.ar_ready}),
    .data_i  ({sbr_port_req_i.aw.id, sbr_port_req_i.ar.id}         ),
    .req_o   (arb_sbr_ar_req                             ),
    .gnt_i   (arb_sbr_ar_gnt                             ),
    .data_o  (arb_sbr_ar_id                              ),
    .idx_o   (inject_aw_into_ar                          )
  );

  ar_chan_t [MaxReads-1:0] mgr_ar_tran;
  id_t      [MaxReads-1:0] mgr_ar_id;
  logic     [MaxReads-1:0] mgr_ar_valid_tran;
  logic     [MaxReads-1:0] mgr_ar_ready_tran;
  tran_id_t                mgr_req_idx;

  rr_arb_tree #(
    .NumIn    (MaxReads ),
    .DataType (ar_chan_t),
    .AxiVldRdy(1'b1     ),
    .ExtPrio  (1'b0     ),
    .LockIn   (1'b1     )
  ) i_mgr_ar_arb (
    .clk_i  (clk_i            ),
    .rst_ni (rst_ni           ),
    .flush_i(1'b0             ),
    .rr_i   ('0               ),
    .req_i  (mgr_ar_valid_tran),
    .gnt_o  (mgr_ar_ready_tran),
    .data_i (mgr_ar_tran      ),
    .gnt_i  (mgr_rsp.ar_ready ),
    .req_o  (mgr_req.ar_valid ),
    .data_o (mgr_req.ar       ),
    .idx_o  (mgr_req_idx      )
  );

  /*****************
   *  ERROR SUBORDINATE  *
   *****************/

  mgr_port_axi_req_t axi_err_req;
  mgr_port_axi_rsp_t axi_err_rsp;

  axi_err_sbr #(
    .IdWidth   (IdWidth             ),
    .Resp      (axi_pkg::RESP_SLVERR),
    .axi_req_t (mgr_port_axi_req_t  ),
    .axi_rsp_t (mgr_port_axi_rsp_t  )
  ) i_axi_err_sbr (
    .clk_i    (clk_i      ),
    .rst_ni   (rst_ni     ),
    .test_i   (1'b0       ),
    .sbr_port_req_i(axi_err_req),
    .sbr_port_rsp_o(axi_err_rsp)
  );

  /***********
   *  DEMUX  *
   ***********/

  // Requests can be sent either to the error subordinate,
  // or to the DWC's manager port.

  logic [MaxReads-1:0] mgr_req_ar_err;
  logic                mgr_req_aw_err;

  axi_demux #(
    .IdWidth     (IdWidth           ),
    .LookBits    (IdWidth           ),
    .aw_chan_t   (aw_chan_t         ),
    .w_chan_t    (mgr_w_chan_t      ),
    .b_chan_t    (b_chan_t          ),
    .ar_chan_t   (ar_chan_t         ),
    .r_chan_t    (mgr_r_chan_t      ),
    .axi_req_t   (mgr_port_axi_req_t),
    .axi_rsp_t   (mgr_port_axi_rsp_t),
    .NumMgrPorts (2                 ),
    .MaxTrans    (MaxReads          ),
    .SpillAw     (1'b1              ) // Required to break dependency between AW and W channels
  ) i_axi_demux (
    .clk_i          (clk_i                      ),
    .rst_ni         (rst_ni                     ),
    .test_i         (1'b0                       ),
    .mgr_ports_req_o     ({axi_err_req, mgr_port_req_o}   ),
    .mgr_ports_rsp_i     ({axi_err_rsp, mgr_port_rsp_i}   ),
    .sbr_ar_select_i(mgr_req_ar_err[mgr_req_idx]),
    .sbr_aw_select_i(mgr_req_aw_err             ),
    .sbr_port_req_i      (mgr_req                    ),
    .sbr_port_rsp_o      (mgr_rsp                    )
  );

  /**********
   *  READ  *
   **********/

  typedef enum logic [2:0] {
    R_IDLE         ,
    R_INJECT_AW    ,
    R_PASSTHROUGH  ,
    R_INCR_DOWNSIZE,
    R_SPLIT_INCR_DOWNSIZE
  } r_state_e;

  typedef struct packed {
    ar_chan_t ar                ;
    logic ar_valid              ;
    logic ar_throw_error        ;
    sbr_r_chan_t r              ;
    logic r_valid               ;
    burst_len_t burst_len       ;
    axi_pkg::size_t orig_ar_size;
    logic injected_aw           ;
  } r_req_t;

  // Write-related type, but w_req_q is referenced from Read logic
  typedef struct packed {
    aw_chan_t aw                  ;
    logic aw_valid                ;
    logic aw_throw_error          ;
    burst_len_t burst_len         ;
    axi_pkg::len_t orig_aw_len    ;
    axi_pkg::burst_t orig_aw_burst;
    axi_pkg::resp_t burst_resp    ;
    axi_pkg::size_t orig_aw_size  ;
  } w_req_t;

  w_req_t   w_req_d, w_req_q;

  // Decide which downsizer will handle the incoming AXI transaction
  logic     [MaxReads-1:0] idle_read_downsizer;
  tran_id_t                idx_ar_downsizer;

  // Find an idle downsizer to handle this transaction
  tran_id_t idx_idle_downsizer;
  lzc #(
    .WIDTH(MaxReads)
  ) i_idle_lzc (
    .in_i   (idle_read_downsizer),
    .cnt_o  (idx_idle_downsizer ),
    .empty_o(/* Unused */       )
  );

  // Is there already another downsizer handling a transaction with the same id
  logic     [MaxReads-1:0] id_clash_downsizer;
  tran_id_t                idx_id_clash_downsizer;
  for (genvar t = 0; t < MaxReads; t++) begin: gen_id_clash
    assign id_clash_downsizer[t] = arb_sbr_ar_id == mgr_ar_id[t] && !idle_read_downsizer[t];
  end

  onehot_to_bin #(
    .ONEHOT_WIDTH(MaxReads)
  ) i_id_clash_onehot_to_bin (
    .onehot(id_clash_downsizer    ),
    .bin   (idx_id_clash_downsizer)
  );

  // Choose an idle downsizer, unless there is an id clash
  assign idx_ar_downsizer = (|id_clash_downsizer) ? idx_id_clash_downsizer : idx_idle_downsizer;

  // This ID queue is used to resolve which downsizer is handling
  // each outstanding read transaction.

  logic     [MaxReads-1:0] idqueue_push;
  logic     [MaxReads-1:0] idqueue_pop;
  tran_id_t                idqueue_id;
  logic                    idqueue_valid;

  id_queue #(
    .ID_WIDTH(IdWidth  ),
    .CAPACITY(MaxReads ),
    .data_t  (tran_id_t)
  ) i_read_id_queue (
    .clk_i           (clk_i           ),
    .rst_ni          (rst_ni          ),
    .inp_id_i        (arb_sbr_ar_id   ),
    .inp_data_i      (idx_ar_downsizer),
    .inp_req_i       (|idqueue_push   ),
    .inp_gnt_o       (/* Unused  */   ),
    .oup_id_i        (mgr_rsp.r.id    ),
    .oup_pop_i       (|idqueue_pop    ),
    .oup_req_i       (1'b1            ),
    .oup_data_o      (idqueue_id      ),
    .oup_data_valid_o(idqueue_valid   ),
    .oup_gnt_o       (/* Unused  */   ),
    .exists_data_i   ('0              ),
    .exists_mask_i   ('0              ),
    .exists_req_i    ('0              ),
    .exists_o        (/* Unused  */   ),
    .exists_gnt_o    (/* Unused  */   )
  );

  for (genvar t = 0; unsigned'(t) < MaxReads; t++) begin: gen_read_downsizer
    r_state_e r_state_d, r_state_q;
    r_req_t r_req_d    , r_req_q  ;

    // Are we idle?
    assign idle_read_downsizer[t] = (r_state_q == R_IDLE) || (r_state_q == R_INJECT_AW);

    // Byte-grouped data signal for the serialization step
    sbr_data_t r_data;

    always_comb begin
      // Maintain state
      r_state_d = r_state_q;
      r_req_d   = r_req_q  ;

      // AR Channel
      mgr_ar_tran[t]       = r_req_q.ar      ;
      mgr_ar_id[t]         = r_req_q.ar.id   ;
      mgr_ar_valid_tran[t] = r_req_q.ar_valid;

      // Throw an error
      mgr_req_ar_err[t] = r_req_q.ar_throw_error;

      // R Channel
      sbr_r_tran[t]       = r_req_q.r      ;
      sbr_r_valid_tran[t] = r_req_q.r_valid;

      idqueue_push[t] = '0;
      idqueue_pop[t]  = '0;

      arb_sbr_ar_gnt_tran[t] = 1'b0;

      mgr_r_ready_tran[t] = 1'b0;

      // Got a grant on the AR channel
      if (mgr_ar_valid_tran[t] && mgr_ar_ready_tran[t]) begin
        r_req_d.ar_valid       = 1'b0;
        r_req_d.ar_throw_error = 1'b0;
      end

      // Initialize r_data
      r_data = r_req_q.r.data;

      case (r_state_q)
        R_IDLE : begin
          // Reset channels
          r_req_d.ar = '0;
          r_req_d.r  = '0;

          // New read request
          if (arb_sbr_ar_req && (idx_ar_downsizer == t)) begin
            arb_sbr_ar_gnt_tran[t] = 1'b1;

            // Push to ID queue
            idqueue_push[t] = 1'b1;

            // Must inject an AW request into this upsizer
            if (inject_aw_into_ar) begin
              r_state_d = R_INJECT_AW;
            end else begin
              // Default state
              r_state_d = R_PASSTHROUGH;

              // Save beat
              r_req_d.ar           = sbr_port_req_i.ar     ;
              r_req_d.ar_valid     = 1'b1             ;
              r_req_d.burst_len    = sbr_port_req_i.ar.len ;
              r_req_d.orig_ar_size = sbr_port_req_i.ar.size;
              r_req_d.injected_aw  = 1'b0             ;

              case (r_req_d.ar.burst)
                axi_pkg::BURST_INCR : begin
                  // Evaluate downsize ratio
                  automatic addr_t size_mask  = (1 << r_req_d.ar.size) - 1                                        ;
                  automatic addr_t conv_ratio = ((1 << r_req_d.ar.size) + MgrPortStrbWidth - 1) / MgrPortStrbWidth;

                  // Evaluate output burst length
                  automatic addr_t align_adj = (r_req_d.ar.addr & size_mask & ~MgrPortByteMask) / MgrPortStrbWidth;
                  r_req_d.burst_len          = (r_req_d.ar.len + 1) * conv_ratio - align_adj - 1                  ;

                  if (conv_ratio != 1) begin
                    r_req_d.ar.size = MgrPortMaxSize;

                    if (r_req_d.burst_len <= 255) begin
                      r_state_d      = R_INCR_DOWNSIZE  ;
                      r_req_d.ar.len = r_req_d.burst_len;
                    end else begin
                      r_state_d      = R_SPLIT_INCR_DOWNSIZE;
                      r_req_d.ar.len = 255 - align_adj      ;
                    end
                  end
                end

                axi_pkg::BURST_FIXED: begin
                  // Single transaction
                  if (r_req_d.ar.len == '0) begin
                    // Evaluate downsize ratio
                    automatic addr_t size_mask  = (1 << r_req_d.ar.size) - 1                                        ;
                    automatic addr_t conv_ratio = ((1 << r_req_d.ar.size) + MgrPortStrbWidth - 1) / MgrPortStrbWidth;

                    // Evaluate output burst length
                    automatic addr_t align_adj = (r_req_d.ar.addr & size_mask & ~MgrPortByteMask) / MgrPortStrbWidth;
                    r_req_d.burst_len          = (conv_ratio >= align_adj + 1) ? (conv_ratio - align_adj - 1) : 0;

                    if (conv_ratio != 1) begin
                      r_state_d        = R_INCR_DOWNSIZE    ;
                      r_req_d.ar.len   = r_req_d.burst_len  ;
                      r_req_d.ar.size  = MgrPortMaxSize  ;
                      r_req_d.ar.burst = axi_pkg::BURST_INCR;
                    end
                  end else begin
                    // The downsizer does not support fixed burts
                    r_req_d.ar_throw_error = 1'b1;
                  end
                end

                axi_pkg::BURST_WRAP: begin
                  // The DW converter does not support this type of burst.
                  r_state_d              = R_PASSTHROUGH;
                  r_req_d.ar_throw_error = 1'b1         ;
                end
              endcase
            end
          end
        end

        R_INJECT_AW : begin
          // Save beat
          r_req_d.ar.id        = w_req_q.aw.id        ;
          r_req_d.ar.addr      = w_req_q.aw.addr      ;
          r_req_d.ar.size      = w_req_q.orig_aw_size ;
          r_req_d.ar.burst     = w_req_q.orig_aw_burst;
          r_req_d.ar.len       = w_req_q.orig_aw_len  ;
          r_req_d.ar.lock      = w_req_q.aw.lock      ;
          r_req_d.ar.cache     = w_req_q.aw.cache     ;
          r_req_d.ar.prot      = w_req_q.aw.prot      ;
          r_req_d.ar.qos       = w_req_q.aw.qos       ;
          r_req_d.ar.region    = w_req_q.aw.region    ;
          r_req_d.ar.user      = w_req_q.aw.user      ;
          r_req_d.ar_valid     = 1'b0                 ; // Injected "AR"s from AW are not valid.
          r_req_d.burst_len    = w_req_q.orig_aw_len  ;
          r_req_d.orig_ar_size = w_req_q.orig_aw_size ;
          r_req_d.injected_aw  = 1'b1                 ;

          // Default state
          r_state_d = R_PASSTHROUGH;

          case (r_req_d.ar.burst)
            axi_pkg::BURST_INCR : begin
              // Evaluate downsize ratio
              automatic addr_t size_mask  = (1 << r_req_d.ar.size) - 1                                        ;
              automatic addr_t conv_ratio = ((1 << r_req_d.ar.size) + MgrPortStrbWidth - 1) / MgrPortStrbWidth;

              // Evaluate output burst length
              automatic addr_t align_adj = (r_req_d.ar.addr & size_mask & ~MgrPortByteMask) / MgrPortStrbWidth;
              r_req_d.burst_len          = (r_req_d.ar.len + 1) * conv_ratio - align_adj - 1                  ;

              if (conv_ratio != 1) begin
                r_req_d.ar.size = MgrPortMaxSize;

                if (r_req_d.burst_len <= 255) begin
                  r_state_d      = R_INCR_DOWNSIZE  ;
                  r_req_d.ar.len = r_req_d.burst_len;
                end else begin
                  r_state_d      = R_SPLIT_INCR_DOWNSIZE;
                  r_req_d.ar.len = 255 - align_adj      ;
                end
              end
            end

            axi_pkg::BURST_FIXED: begin
              // Single transaction
              if (r_req_d.ar.len == '0) begin
                // Evaluate downsize ratio
                automatic addr_t size_mask  = (1 << r_req_d.ar.size) - 1                                        ;
                automatic addr_t conv_ratio = ((1 << r_req_d.ar.size) + MgrPortStrbWidth - 1) / MgrPortStrbWidth;

                // Evaluate output burst length
                automatic addr_t align_adj = (r_req_d.ar.addr & size_mask & ~MgrPortByteMask) / MgrPortStrbWidth;
                r_req_d.burst_len          = (conv_ratio >= align_adj + 1) ? (conv_ratio - align_adj - 1) : 0;

                if (conv_ratio != 1) begin
                  r_state_d        = R_INCR_DOWNSIZE    ;
                  r_req_d.ar.len   = r_req_d.burst_len  ;
                  r_req_d.ar.size  = MgrPortMaxSize     ;
                  r_req_d.ar.burst = axi_pkg::BURST_INCR;
                end
              end else begin
                // The downsizer does not support fixed burts
                r_req_d.ar_throw_error = 1'b1;
              end
            end

            axi_pkg::BURST_WRAP: begin
              // The DW converter does not support this type of burst.
              r_state_d              = R_PASSTHROUGH;
              r_req_d.ar_throw_error = 1'b1         ;
            end
          endcase
        end

        R_PASSTHROUGH, R_INCR_DOWNSIZE, R_SPLIT_INCR_DOWNSIZE: begin
          // Got a grant on the R channel
          if (sbr_r_valid_tran[t] && sbr_r_ready_tran[t]) begin
            r_req_d.r       = '0  ;
            r_req_d.r_valid = 1'b0;
            r_data          = '0  ;
          end

          // Request was accepted
          if (!r_req_q.ar_valid)
            // Our turn
            if ((idqueue_id == t) && idqueue_valid)
              // Ready to accept more data
              if (!sbr_r_valid_tran[t] || (sbr_r_valid_tran[t] && sbr_r_ready_tran[t])) begin
                mgr_r_ready_tran[t] = 1'b1;

                if (mgr_rsp.r_valid) begin
                  automatic addr_t mgr_port_offset = MgrPortStrbWidth == 1 ? '0 : r_req_q.ar.addr[idx_width(MgrPortStrbWidth)-1:0];
                  automatic addr_t sbr_port_offset = SbrPortStrbWidth == 1 ? '0 : r_req_q.ar.addr[idx_width(SbrPortStrbWidth)-1:0];

                  // Serialization
                  for (int b = 0; b < SbrPortStrbWidth; b++)
                    if ((b >= sbr_port_offset) &&
                        (b - sbr_port_offset < (1 << r_req_q.orig_ar_size)) &&
                        (b + mgr_port_offset - sbr_port_offset < MgrPortStrbWidth)) begin
                      r_data[b] = mgr_rsp.r.data[8*(b + mgr_port_offset - sbr_port_offset) +: 8];
                    end

                  r_req_d.burst_len = r_req_q.burst_len - 1   ;
                  r_req_d.ar.len    = r_req_q.ar.len - 1      ;
                  r_req_d.r.data    = r_data                  ;
                  r_req_d.r.last    = (r_req_q.burst_len == 0);
                  r_req_d.r.id      = mgr_rsp.r.id           ;
                  r_req_d.r.user    = mgr_rsp.r.user         ;

                  // Merge response of this beat with prior one according to precedence rules.
                  r_req_d.r.resp = axi_pkg::resp_precedence(r_req_q.r.resp, mgr_rsp.r.resp);

                  case (r_req_d.ar.burst)
                    axi_pkg::BURST_INCR: begin
                      r_req_d.ar.addr = aligned_addr(r_req_q.ar.addr, r_req_q.ar.size) + (1 << r_req_q.ar.size);
                    end
                    axi_pkg::BURST_FIXED: begin
                      r_req_d.ar.addr = r_req_q.ar.addr;
                    end
                  endcase

                  if (r_req_q.burst_len == 0)
                    idqueue_pop[t] = 1'b1;

                  case (r_state_q)
                    R_PASSTHROUGH :
                      // Forward data as soon as we can
                      r_req_d.r_valid = 1'b1;

                    R_INCR_DOWNSIZE, R_SPLIT_INCR_DOWNSIZE:
                      // Forward when the burst is finished, or after filling up a word
                      if (r_req_q.burst_len == 0 || (aligned_addr(r_req_d.ar.addr, r_req_q.orig_ar_size) != aligned_addr(r_req_q.ar.addr, r_req_q.orig_ar_size)))
                        r_req_d.r_valid = 1'b1;
                  endcase

                  // Trigger another burst request, if needed
                  if (r_state_q == R_SPLIT_INCR_DOWNSIZE)
                    // Finished current burst, but whole transaction hasn't finished
                    if (r_req_q.ar.len == '0 && r_req_q.burst_len != '0) begin
                      r_req_d.ar_valid = !r_req_q.injected_aw;
                      r_req_d.ar.len   = (r_req_d.burst_len <= 255) ? r_req_d.burst_len : 255;
                    end
                end
              end

          if (sbr_r_valid_tran[t] && sbr_r_ready_tran[t])
            if (r_req_q.burst_len == '1)
              r_state_d = R_IDLE;
        end
      endcase
    end

    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        r_state_q <= R_IDLE;
        r_req_q   <= '0    ;
      end else begin
        r_state_q <= r_state_d;
        r_req_q   <= r_req_d  ;
      end
    end
  end : gen_read_downsizer

  /***********
   *  WRITE  *
   ***********/
  typedef enum logic [1:0] {
    W_IDLE         ,
    W_PASSTHROUGH  ,
    W_INCR_DOWNSIZE,
    W_SPLIT_INCR_DOWNSIZE
  } w_state_e;

  w_state_e w_state_d, w_state_q;

  // This FIFO holds the number of bursts generated by each write transactions handled by this downsizer.
  // This is used to forward only the correct B beats to the subordinate.
  logic forward_b_beat_i;
  logic forward_b_beat_o;
  logic forward_b_beat_push;
  logic forward_b_beat_pop;
  logic forward_b_beat_full;

  fifo_v3 #(
    .DATA_WIDTH  (1       ),
    .DEPTH       (MaxReads),
    .FALL_THROUGH(1'b1    )
  ) i_forward_b_beats_queue (
    .clk_i     (clk_i               ),
    .rst_ni    (rst_ni              ),
    .flush_i   (1'b0                ),
    .testmode_i(1'b0                ),
    .data_i    (forward_b_beat_i    ),
    .push_i    (forward_b_beat_push ),
    .full_o    (forward_b_beat_full ),
    .data_o    (forward_b_beat_o    ),
    .pop_i     (forward_b_beat_pop  ),
    .empty_o   (/* Unused */        ),
    .usage_o   (/* Unused */        )
  );

  // Byte-grouped data signal for the lane steering step
  mgr_data_t w_data;

  always_comb begin
    inject_aw_into_ar_req = 1'b0;

    // i_num_b_beats default state
    forward_b_beat_i    = '0  ;
    forward_b_beat_push = 1'b0;
    forward_b_beat_pop  = 1'b0;

    // Maintain state
    w_state_d = w_state_q;
    w_req_d   = w_req_q  ;

    // AW Channel
    mgr_req.aw          = w_req_q.aw      ;
    mgr_req.aw_valid    = w_req_q.aw_valid;
    sbr_port_rsp_o.aw_ready = '0               ;

    // Throw an error.
    mgr_req_aw_err = w_req_q.aw_throw_error;

    // W Channel
    mgr_req.w         = '0;
    mgr_req.w_valid   = '0;
    sbr_port_rsp_o.w_ready = '0;

    // Initialize w_data
    w_data = '0;

    // B Channel (No latency)
    if (mgr_rsp.b_valid) begin
      // Merge response of this burst with prior one according to precedence rules.
      w_req_d.burst_resp = axi_pkg::resp_precedence(w_req_q.burst_resp, mgr_rsp.b.resp);
    end
    sbr_port_rsp_o.b      = mgr_rsp.b         ;
    sbr_port_rsp_o.b.resp = w_req_d.burst_resp;

    // Each write transaction might trigger several B beats on the manager (narrow) side.
    // Only forward the last B beat of each transaction.
    if (forward_b_beat_o) begin
      sbr_port_rsp_o.b_valid = mgr_rsp.b_valid ;
      mgr_req.b_ready   = sbr_port_req_i.b_ready;

      // Got an ack on the B channel. Pop transaction.
      if (mgr_req.b_ready && mgr_rsp.b_valid)
        forward_b_beat_pop = 1'b1;
    end else begin
      // Otherwise, just acknowlegde the B beats
      sbr_port_rsp_o.b_valid  = 1'b0           ;
      mgr_req.b_ready    = 1'b1           ;
      forward_b_beat_pop = mgr_rsp.b_valid;
    end

    // Got a grant on the AW channel
    if (mgr_req.aw_valid & mgr_rsp.aw_ready) begin
      w_req_d.aw_valid       = 1'b0;
      w_req_d.aw_throw_error = 1'b0;
    end

    case (w_state_q)
      W_PASSTHROUGH, W_INCR_DOWNSIZE, W_SPLIT_INCR_DOWNSIZE: begin
        // Request was accepted
        if (!w_req_q.aw_valid)
          if (sbr_port_req_i.w_valid) begin
            automatic addr_t mgr_port_offset = MgrPortStrbWidth == 1 ? '0 : w_req_q.aw.addr[idx_width(MgrPortStrbWidth)-1:0];
            automatic addr_t sbr_port_offset = SbrPortStrbWidth == 1 ? '0 : w_req_q.aw.addr[idx_width(SbrPortStrbWidth)-1:0];

            // Valid output
            mgr_req.w_valid = 1'b1               ;
            mgr_req.w.last  = w_req_q.aw.len == 0;
            mgr_req.w.user  = sbr_port_req_i.w.user   ;

            // Lane steering
            for (int b = 0; b < SbrPortStrbWidth; b++)
              if ((b >= sbr_port_offset) &&
                  (b - sbr_port_offset < (1 << w_req_q.orig_aw_size)) &&
                  (b + mgr_port_offset - sbr_port_offset < MgrPortStrbWidth)) begin
                w_data[b + mgr_port_offset - sbr_port_offset]         = sbr_port_req_i.w.data[8*b +: 8];
                mgr_req.w.strb[b + mgr_port_offset - sbr_port_offset] = sbr_port_req_i.w.strb[b]       ;
              end
            mgr_req.w.data = w_data;
          end

        // Acknowledgment
        if (mgr_rsp.w_ready && mgr_req.w_valid) begin
          w_req_d.burst_len = w_req_q.burst_len - 1;
          w_req_d.aw.len    = w_req_q.aw.len - 1   ;

          case (w_req_d.aw.burst)
            axi_pkg::BURST_INCR: begin
              w_req_d.aw.addr = aligned_addr(w_req_q.aw.addr, w_req_q.aw.size) + (1 << w_req_q.aw.size);
            end
            axi_pkg::BURST_FIXED: begin
              w_req_d.aw.addr = w_req_q.aw.addr;
            end
          endcase

          case (w_state_q)
            W_PASSTHROUGH:
              sbr_port_rsp_o.w_ready = 1'b1;

            W_INCR_DOWNSIZE, W_SPLIT_INCR_DOWNSIZE:
              if (w_req_q.burst_len == 0 || (aligned_addr(w_req_d.aw.addr, w_req_q.orig_aw_size) != aligned_addr(w_req_q.aw.addr, w_req_q.orig_aw_size)))
                sbr_port_rsp_o.w_ready = 1'b1;
          endcase

          // Trigger another burst request, if needed
          if (w_state_q == W_SPLIT_INCR_DOWNSIZE)
            // Finished current burst, but whole transaction hasn't finished
            if (w_req_q.aw.len == '0 && w_req_q.burst_len != '0 && !forward_b_beat_full) begin
              w_req_d.aw_valid = 1'b1;
              w_req_d.aw.len   = (w_req_d.burst_len <= 255) ? w_req_d.burst_len : 255;

              // We will receive an extraneous B beat. Ignore it.
              forward_b_beat_i    = 1'b0;
              forward_b_beat_push = 1'b1;
            end

          if (w_req_q.burst_len == 0 && !forward_b_beat_full) begin
            w_state_d = W_IDLE;

            forward_b_beat_push = 1'b1;
            forward_b_beat_i    = 1'b1;
          end
        end
      end
    endcase

    // Can start a new request as soon as w_state_d is W_IDLE
    if (w_state_d == W_IDLE) begin
      // Reset channels
      w_req_d.aw             = '0                ;
      w_req_d.aw_valid       = 1'b0              ;
      w_req_d.aw_throw_error = 1'b0              ;
      w_req_d.burst_resp     = axi_pkg::RESP_OKAY;

      if (!forward_b_beat_full) begin
        if (sbr_port_req_i.aw_valid && sbr_port_req_i.aw.atop[axi_pkg::ATOP_R_RESP]) begin // ATOP with an R response
          inject_aw_into_ar_req = 1'b1                 ;
          sbr_port_rsp_o.aw_ready   = inject_aw_into_ar_gnt;
        end else begin // Regular AW
          sbr_port_rsp_o.aw_ready = 1'b1;
        end

        // New write request
        if (sbr_port_req_i.aw_valid && sbr_port_rsp_o.aw_ready) begin
          // Default state
          w_state_d = W_PASSTHROUGH;

          // Save beat
          w_req_d.aw            = sbr_port_req_i.aw      ;
          w_req_d.aw_valid      = 1'b1              ;
          w_req_d.burst_len     = sbr_port_req_i.aw.len  ;
          w_req_d.orig_aw_len   = sbr_port_req_i.aw.len  ;
          w_req_d.orig_aw_size  = sbr_port_req_i.aw.size ;
          w_req_d.orig_aw_burst = sbr_port_req_i.aw.burst;

          case (sbr_port_req_i.aw.burst)
            axi_pkg::BURST_INCR: begin
              // Evaluate downsize ratio
              automatic addr_t size_mask  = (1 << sbr_port_req_i.aw.size) - 1                                        ;
              automatic addr_t conv_ratio = ((1 << sbr_port_req_i.aw.size) + MgrPortStrbWidth - 1) / MgrPortStrbWidth;

              // Evaluate output burst length
              automatic addr_t align_adj = (sbr_port_req_i.aw.addr & size_mask & ~MgrPortByteMask) / MgrPortStrbWidth;
              w_req_d.burst_len          = (sbr_port_req_i.aw.len + 1) * conv_ratio - align_adj - 1                  ;

              if (conv_ratio != 1) begin
                w_req_d.aw.size = MgrPortMaxSize;

                if (w_req_d.burst_len <= 255) begin
                  w_state_d      = W_INCR_DOWNSIZE  ;
                  w_req_d.aw.len = w_req_d.burst_len;
                end else begin
                  w_state_d      = W_SPLIT_INCR_DOWNSIZE;
                  w_req_d.aw.len = 255 - align_adj      ;
                end
              end
            end

            axi_pkg::BURST_FIXED: begin
              // Single transaction
              if (sbr_port_req_i.aw.len == '0) begin
                // Evaluate downsize ratio
                automatic addr_t size_mask  = (1 << sbr_port_req_i.aw.size) - 1                                        ;
                automatic addr_t conv_ratio = ((1 << sbr_port_req_i.aw.size) + MgrPortStrbWidth - 1) / MgrPortStrbWidth;

                // Evaluate output burst length
                automatic addr_t align_adj = (sbr_port_req_i.aw.addr & size_mask & ~MgrPortByteMask) / MgrPortStrbWidth;
                w_req_d.burst_len          = (conv_ratio >= align_adj + 1) ? (conv_ratio - align_adj - 1) : 0;

                if (conv_ratio != 1) begin
                  w_state_d        = W_INCR_DOWNSIZE    ;
                  w_req_d.aw.len   = w_req_d.burst_len  ;
                  w_req_d.aw.size  = MgrPortMaxSize     ;
                  w_req_d.aw.burst = axi_pkg::BURST_INCR;
                end
              end else begin
                // The downsizer does not support fixed bursts
                w_req_d.aw_throw_error = 1'b1;
              end
            end

            axi_pkg::BURST_WRAP: begin
              // The DW converter does not support this type of burst.
              w_state_d              = W_PASSTHROUGH;
              w_req_d.aw_throw_error = 1'b1         ;
            end
          endcase
        end
      end
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      w_state_q <= W_IDLE;
      w_req_q   <= '0    ;
    end else begin
      w_state_q <= w_state_d;
      w_req_q   <= w_req_d  ;
    end
  end

endmodule : axi_dw_downsizer
