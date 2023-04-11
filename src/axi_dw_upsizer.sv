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
// Data width upsize conversion.
// Connects a narrow manager to a wider subordinate.

// NOTE: The upsizer does not support WRAP bursts, and will answer with SLVERR
// upon receiving a burst of such type.

module axi_dw_upsizer #(
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
  import axi_pkg::beat_addr   ;
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

  // Byte-grouped data words
  typedef logic [MgrPortStrbWidth-1:0][7:0] mgr_data_t;
  typedef logic [SbrPortStrbWidth-1:0][7:0] sbr_data_t;

  // Address width
  typedef logic [AddrWidth-1:0] addr_t;

  // ID width
  typedef logic [IdWidth-1:0] id_t;

  // Length of burst after upsizing
  typedef logic [$clog2(MgrPortStrbWidth/SbrPortStrbWidth) + 7:0] burst_len_t;

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
    .clk_i  (clk_i                                      ),
    .rst_ni (rst_ni                                     ),
    .flush_i(1'b0                                       ),
    .rr_i   ('0                                         ),
    .req_i  ({inject_aw_into_ar_req, sbr_port_req_i.ar_valid}),
    .gnt_o  ({inject_aw_into_ar_gnt, sbr_port_rsp_o.ar_ready}),
    .data_i ({sbr_port_req_i.aw.id, sbr_port_req_i.ar.id}         ),
    .req_o  (arb_sbr_ar_req                             ),
    .gnt_i  (arb_sbr_ar_gnt                             ),
    .data_o (arb_sbr_ar_id                              ),
    .idx_o  (inject_aw_into_ar                          )
  );

  ar_chan_t [MaxReads-1:0] mgr_ar_tran;
  id_t      [MaxReads-1:0] mgr_ar_id;
  logic     [MaxReads-1:0] mgr_ar_valid_tran;
  logic     [MaxReads-1:0] mgr_ar_ready_tran;
  tran_id_t                mgr_req_idx;

  rr_arb_tree #(
    .NumIn    (MaxReads) ,
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

  typedef enum logic [1:0] {
    R_IDLE       ,
    R_INJECT_AW  ,
    R_PASSTHROUGH,
    R_INCR_UPSIZE
  } r_state_e;

  // Write-related type, but w_req_q is referenced from Read logic
  typedef struct packed {
    aw_chan_t aw                ;
    logic aw_valid              ;
    logic aw_throw_error        ;
    mgr_w_chan_t w              ;
    logic w_valid               ;
    axi_pkg::len_t burst_len    ;
    axi_pkg::size_t orig_aw_size;
  } w_req_t;

  w_req_t   w_req_d, w_req_q;

  // Decide which upsizer will handle the incoming AXI transaction
  logic     [MaxReads-1:0] idle_read_upsizer;
  tran_id_t                idx_ar_upsizer ;

  // Find an idle upsizer to handle this transaction
  tran_id_t idx_idle_upsizer;
  lzc #(
    .WIDTH(MaxReads)
  ) i_idle_lzc (
    .in_i   (idle_read_upsizer),
    .cnt_o  (idx_idle_upsizer ),
    .empty_o(/* Unused */     )
  );

  // Is there already another upsizer handling a transaction with the same id
  logic     [MaxReads-1:0] id_clash_upsizer;
  tran_id_t                idx_id_clash_upsizer ;
  for (genvar t = 0; t < MaxReads; t++) begin: gen_id_clash
    assign id_clash_upsizer[t] = arb_sbr_ar_id == mgr_ar_id[t] && !idle_read_upsizer[t];
  end

  onehot_to_bin #(
    .ONEHOT_WIDTH(MaxReads)
  ) i_id_clash_onehot_to_bin (
    .onehot(id_clash_upsizer    ),
    .bin   (idx_id_clash_upsizer)
  );

  // Choose an idle upsizer, unless there is an id clash
  assign idx_ar_upsizer = (|id_clash_upsizer) ? idx_id_clash_upsizer : idx_idle_upsizer;

  // This logic is used to resolve which upsizer is handling
  // each outstanding read transaction

  logic     r_upsizer_valid;
  tran_id_t idx_r_upsizer;

  logic [MaxReads-1:0] rid_upsizer_match;

  // Is there a upsizer handling this transaction?
  assign r_upsizer_valid = |rid_upsizer_match;

  for (genvar t = 0; t < MaxReads; t++) begin: gen_rid_match
    assign rid_upsizer_match[t] = (mgr_rsp.r.id == mgr_ar_id[t]) && !idle_read_upsizer[t];
  end

  onehot_to_bin #(
    .ONEHOT_WIDTH(MaxReads)
  ) i_rid_upsizer_lzc (
    .onehot(rid_upsizer_match),
    .bin   (idx_r_upsizer    )
  );

  typedef struct packed {
    ar_chan_t ar                ;
    logic ar_valid              ;
    logic ar_throw_error        ;
    axi_pkg::len_t burst_len    ;
    axi_pkg::size_t orig_ar_size;
  } r_req_t;

  for (genvar t = 0; unsigned'(t) < MaxReads; t++) begin: gen_read_upsizer
    r_state_e r_state_d, r_state_q;
    r_req_t r_req_d    , r_req_q  ;

    // Are we idle?
    assign idle_read_upsizer[t] = (r_state_q == R_IDLE) || (r_state_q == R_INJECT_AW);

    // Byte-grouped data signal for the lane steering step
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
      // No latency
      sbr_r_tran[t]      = '0             ;
      sbr_r_tran[t].id   = mgr_rsp.r.id  ;
      sbr_r_tran[t].resp = mgr_rsp.r.resp;
      sbr_r_tran[t].user = mgr_rsp.r.user;

      arb_sbr_ar_gnt_tran[t] = 1'b0;

      mgr_r_ready_tran[t] = 1'b0;
      sbr_r_valid_tran[t] = 1'b0;

      // Got a grant on the AR channel
      if (mgr_ar_valid_tran[t] && mgr_ar_ready_tran[t]) begin
        r_req_d.ar_valid       = 1'b0;
        r_req_d.ar_throw_error = 1'b0;
      end

      // Initialize r_data
      r_data = '0;

      case (r_state_q)
        R_IDLE : begin
          // Reset channels
          r_req_d.ar = '0;

          // New read request
          if (arb_sbr_ar_req && (idx_ar_upsizer == t)) begin
            arb_sbr_ar_gnt_tran[t] = 1'b1;

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

              case (r_req_d.ar.burst)
                axi_pkg::BURST_INCR: begin
                  // Modifiable transaction
                  if (modifiable(r_req_d.ar.cache)) begin
                    // No need to upsize single-beat transactions.
                    if (r_req_d.ar.len != '0) begin
                      // Evaluate output burst length
                      automatic addr_t start_addr = aligned_addr(r_req_d.ar.addr, MgrPortMaxSize);
                      automatic addr_t end_addr   = aligned_addr(beat_addr(r_req_d.ar.addr,
                          r_req_d.orig_ar_size, r_req_d.burst_len, r_req_d.ar.burst,
                          r_req_d.burst_len), MgrPortMaxSize);
                      r_req_d.ar.len  = (end_addr - start_addr) >> MgrPortMaxSize;
                      r_req_d.ar.size = MgrPortMaxSize                           ;
                      r_state_d       = R_INCR_UPSIZE                            ;
                    end
                  end
                end

                axi_pkg::BURST_FIXED: begin
                  // Passes through the upsizer without any changes
                  r_state_d = R_PASSTHROUGH;
                end

                axi_pkg::BURST_WRAP: begin
                  // The DW converter does not support this kind of burst ...
                  r_state_d              = R_PASSTHROUGH;
                  r_req_d.ar_throw_error = 1'b1         ;

                  // ... but might if this is a single-beat transaction
                  if (r_req_d.ar.len == '0)
                    r_req_d.ar_throw_error = 1'b0;
                end
              endcase
            end
          end
        end

        R_INJECT_AW : begin
          // Save beat
          // During this cycle, w_req_q stores the original AW request
          r_req_d.ar.id        = w_req_q.aw.id       ;
          r_req_d.ar.addr      = w_req_q.aw.addr     ;
          r_req_d.ar.size      = w_req_q.orig_aw_size;
          r_req_d.ar.burst     = w_req_q.aw.burst    ;
          r_req_d.ar.len       = w_req_q.burst_len   ;
          r_req_d.ar.lock      = w_req_q.aw.lock     ;
          r_req_d.ar.cache     = w_req_q.aw.cache    ;
          r_req_d.ar.prot      = w_req_q.aw.prot     ;
          r_req_d.ar.qos       = w_req_q.aw.qos      ;
          r_req_d.ar.region    = w_req_q.aw.region   ;
          r_req_d.ar.user      = w_req_q.aw.user     ;
          r_req_d.ar_valid     = 1'b0                ; // Injected "AR"s from AW are not valid.
          r_req_d.burst_len    = w_req_q.burst_len   ;
          r_req_d.orig_ar_size = w_req_q.orig_aw_size;

          // Default state
          r_state_d = R_PASSTHROUGH;

          case (r_req_d.ar.burst)
            axi_pkg::BURST_INCR: begin
              // Modifiable transaction
              if (modifiable(r_req_d.ar.cache)) begin
                // No need to upsize single-beat transactions.
                if (r_req_d.ar.len != '0) begin
                  // Evaluate output burst length
                  automatic addr_t start_addr = aligned_addr(r_req_d.ar.addr, MgrPortMaxSize);
                  automatic addr_t end_addr   = aligned_addr(beat_addr(r_req_d.ar.addr,
                      r_req_d.orig_ar_size, r_req_d.burst_len, r_req_d.ar.burst,
                      r_req_d.burst_len), MgrPortMaxSize);
                  r_req_d.ar.len  = (end_addr - start_addr) >> MgrPortMaxSize;
                  r_req_d.ar.size = MgrPortMaxSize                           ;
                  r_state_d       = R_INCR_UPSIZE                            ;
                end
              end
            end

            axi_pkg::BURST_FIXED: begin
              // Passes through the upsizer without any changes
              r_state_d = R_PASSTHROUGH;
            end

            axi_pkg::BURST_WRAP: begin
              // The DW converter does not support this kind of burst ...
              r_state_d              = R_PASSTHROUGH;
              r_req_d.ar_throw_error = 1'b1         ;

              // ... but might if this is a single-beat transaction
              if (r_req_d.ar.len == '0)
                r_req_d.ar_throw_error = 1'b0;
            end
          endcase
        end

        R_PASSTHROUGH, R_INCR_UPSIZE: begin
          // Request was accepted
          if (!r_req_q.ar_valid)
            if (mgr_rsp.r_valid && (idx_r_upsizer == t) && r_upsizer_valid) begin
              automatic addr_t mgr_port_offset = MgrPortStrbWidth == 1 ? '0 : r_req_q.ar.addr[idx_width(MgrPortStrbWidth)-1:0];
              automatic addr_t sbr_port_offset = SbrPortStrbWidth == 1 ? '0 : r_req_q.ar.addr[idx_width(SbrPortStrbWidth)-1:0];

              // Valid output
              sbr_r_valid_tran[t] = 1'b1                                       ;
              sbr_r_tran[t].last  = mgr_rsp.r.last && (r_req_q.burst_len == 0);

              // Lane steering
              for (int b = 0; b < MgrPortStrbWidth; b++) begin
                if ((b >= mgr_port_offset) &&
                    (b - mgr_port_offset < (1 << r_req_q.orig_ar_size)) &&
                    (b + sbr_port_offset - mgr_port_offset < SbrPortStrbWidth)) begin
                  r_data[b + sbr_port_offset - mgr_port_offset] = mgr_rsp.r.data[8*b +: 8];
                end
              end
              sbr_r_tran[t].data = r_data;

              // Acknowledgment
              if (sbr_r_ready_tran[t]) begin
                r_req_d.burst_len = r_req_q.burst_len - 1;

                case (r_req_q.ar.burst)
                  axi_pkg::BURST_INCR: begin
                    r_req_d.ar.addr = aligned_addr(r_req_q.ar.addr, r_req_q.orig_ar_size) + (1 << r_req_q.orig_ar_size);
                  end
                  axi_pkg::BURST_FIXED: begin
                    r_req_d.ar.addr = r_req_q.ar.addr;
                  end
                endcase

                case (r_state_q)
                  R_PASSTHROUGH:
                    mgr_r_ready_tran[t] = 1'b1;

                  R_INCR_UPSIZE:
                    if (r_req_q.burst_len == 0 || (aligned_addr(r_req_d.ar.addr, MgrPortMaxSize) != aligned_addr(r_req_q.ar.addr, MgrPortMaxSize)))
                      mgr_r_ready_tran[t] = 1'b1;
                endcase

                if (r_req_q.burst_len == '0)
                  r_state_d = R_IDLE;
              end
            end
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
  end : gen_read_upsizer

  /***********
   *  WRITE  *
   ***********/

  typedef enum logic [1:0] {
    W_IDLE       ,
    W_PASSTHROUGH,
    W_INCR_UPSIZE
  } w_state_e;

  w_state_e w_state_d, w_state_q;

  // Byte-grouped data signal for the serialization step
  mgr_data_t w_data;

  always_comb begin
    inject_aw_into_ar_req = 1'b0;

    // Maintain state
    w_state_d = w_state_q;
    w_req_d   = w_req_q  ;

    // AW Channel
    mgr_req.aw         = w_req_q.aw      ;
    mgr_req.aw_valid   = w_req_q.aw_valid;
    sbr_port_rsp_o.aw_ready = '0              ;

    // Throw an error.
    mgr_req_aw_err = w_req_q.aw_throw_error;

    // W Channel
    mgr_req.w         = w_req_q.w      ;
    mgr_req.w_valid   = w_req_q.w_valid;
    sbr_port_rsp_o.w_ready = '0             ;

    // Initialize w_data
    w_data = w_req_q.w.data;

    // B Channel (No latency)
    sbr_port_rsp_o.b       = mgr_rsp.b        ;
    sbr_port_rsp_o.b_valid = mgr_rsp.b_valid  ;
    mgr_req.b_ready   = sbr_port_req_i.b_ready;

    // Got a grant on the AW channel
    if (mgr_req.aw_valid && mgr_rsp.aw_ready) begin
      w_req_d.aw_valid       = 1'b0;
      w_req_d.aw_throw_error = 1'b0;
    end

    case (w_state_q)
      W_PASSTHROUGH, W_INCR_UPSIZE: begin
        // Got a grant on the W channel
        if (mgr_req.w_valid && mgr_rsp.w_ready) begin
          w_data          = '0  ;
          w_req_d.w       = '0  ;
          w_req_d.w_valid = 1'b0;
        end

        // Request was accepted
        if (!w_req_q.aw_valid) begin
          // Ready if downstream interface is idle, or if it is ready
          sbr_port_rsp_o.w_ready = ~mgr_req.w_valid || mgr_rsp.w_ready;

          if (sbr_port_req_i.w_valid && sbr_port_rsp_o.w_ready) begin
            automatic addr_t mgr_port_offset = MgrPortStrbWidth == 1 ? '0 : w_req_q.aw.addr[idx_width(MgrPortStrbWidth)-1:0];
            automatic addr_t sbr_port_offset = SbrPortStrbWidth == 1 ? '0 : w_req_q.aw.addr[idx_width(SbrPortStrbWidth)-1:0];

            // Serialization
            for (int b = 0; b < MgrPortStrbWidth; b++)
              if ((b >= mgr_port_offset) &&
                  (b - mgr_port_offset < (1 << w_req_q.orig_aw_size)) &&
                  (b + sbr_port_offset - mgr_port_offset < SbrPortStrbWidth)) begin
                w_data[b]         = sbr_port_req_i.w.data[8*(b + sbr_port_offset - mgr_port_offset) +: 8];
                w_req_d.w.strb[b] = sbr_port_req_i.w.strb[b + sbr_port_offset - mgr_port_offset]         ;
              end

            w_req_d.burst_len = w_req_q.burst_len - 1   ;
            w_req_d.w.data    = w_data                  ;
            w_req_d.w.last    = (w_req_q.burst_len == 0);
            w_req_d.w.user    = sbr_port_req_i.w.user        ;

            case (w_req_q.aw.burst)
              axi_pkg::BURST_INCR: begin
                w_req_d.aw.addr = aligned_addr(w_req_q.aw.addr, w_req_q.orig_aw_size) + (1 << w_req_q.orig_aw_size);
              end
              axi_pkg::BURST_FIXED: begin
                w_req_d.aw.addr = w_req_q.aw.addr;
              end
            endcase

            case (w_state_q)
              W_PASSTHROUGH:
                // Forward data as soon as we can
                w_req_d.w_valid = 1'b1;

              W_INCR_UPSIZE:
                // Forward when the burst is finished, or after filling up a word
                if (w_req_q.burst_len == 0 || (aligned_addr(w_req_d.aw.addr, MgrPortMaxSize) != aligned_addr(w_req_q.aw.addr, MgrPortMaxSize)))
                  w_req_d.w_valid = 1'b1;
            endcase
          end
        end

        if (mgr_req.w_valid && mgr_rsp.w_ready)
          if (w_req_q.burst_len == '1) begin
            sbr_port_rsp_o.w_ready = 1'b0  ;
            w_state_d          = W_IDLE;
          end
      end
    endcase

    // Can start a new request as soon as w_state_d is W_IDLE
    if (w_state_d == W_IDLE) begin
      // Reset channels
      w_req_d.aw             = '0  ;
      w_req_d.aw_valid       = 1'b0;
      w_req_d.aw_throw_error = 1'b0;
      w_req_d.w              = '0  ;
      w_req_d.w_valid        = 1'b0;

      if (sbr_port_req_i.aw_valid && sbr_port_req_i.aw.atop[axi_pkg::ATOP_R_RESP]) begin // ATOP with an R response
        inject_aw_into_ar_req = 1'b1                 ;
        sbr_port_rsp_o.aw_ready   = inject_aw_into_ar_gnt;
      end else begin // Regular AW
        sbr_port_rsp_o.aw_ready = 1'b1;
      end

      // New write request
      if (sbr_port_req_i.aw_valid & sbr_port_rsp_o.aw_ready) begin
        // Default state
        w_state_d = W_PASSTHROUGH;

        // Save beat
        w_req_d.aw       = sbr_port_req_i.aw;
        w_req_d.aw_valid = 1'b1        ;

        w_req_d.burst_len    = sbr_port_req_i.aw.len ;
        w_req_d.orig_aw_size = sbr_port_req_i.aw.size;

        case (sbr_port_req_i.aw.burst)
          axi_pkg::BURST_INCR: begin
            // Modifiable transaction
            if (modifiable(sbr_port_req_i.aw.cache))
              // No need to upsize single-beat transactions.
              if (sbr_port_req_i.aw.len != '0) begin
                // Evaluate output burst length
                automatic addr_t start_addr = aligned_addr(sbr_port_req_i.aw.addr, MgrPortMaxSize);
                automatic addr_t end_addr   = aligned_addr(beat_addr(sbr_port_req_i.aw.addr,
                    sbr_port_req_i.aw.size, sbr_port_req_i.aw.len, sbr_port_req_i.aw.burst, sbr_port_req_i.aw.len),
                    MgrPortMaxSize);

                w_req_d.aw.len  = (end_addr - start_addr) >> MgrPortMaxSize;
                w_req_d.aw.size = MgrPortMaxSize                           ;
                w_state_d       = W_INCR_UPSIZE                            ;
              end
          end

          axi_pkg::BURST_FIXED: begin
            // Passes through the upsizer without any changes
            w_state_d = W_PASSTHROUGH;
          end

          axi_pkg::BURST_WRAP: begin
            // The DW converter does not support this kind of burst ...
            w_state_d              = W_PASSTHROUGH;
            w_req_d.aw_throw_error = 1'b1         ;

            // ... but might if this is a single-beat transaction
            if (sbr_port_req_i.aw.len == '0)
              w_req_d.aw_throw_error = 1'b0;
          end
        endcase
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

endmodule : axi_dw_upsizer
