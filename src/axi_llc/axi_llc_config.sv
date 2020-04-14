/* Copyright 2019 ETH Zurich and University of Bologna.
 * Copyright and related rights are licensed under the Solderpad Hardware
 * License, Version 0.51 (the “License”); you may not use this file except in
 * compliance with the License.  You may obtain a copy of the License at
 * http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
 * or agreed to in writing, software, hardware and materials distributed under
 * this License is distributed on an “AS IS” BASIS, WITHOUT WARRANTIES OR
 * CONDITIONS OF ANY KIND, either express or implied. See the License for the
 * specific language governing permissions and limitations under the License.
 *
 * File:   llc_config.sv
 * Author: Wolfgang Roenninger <wroennin@student.ethz.ch>
 * Date:   17.06.2019
 *
 * Description: Contains the Config registers to the LLC
 *              It handels Axi LITE transactions onto the Config registers
 *              The configuration can be only written onto, if the AXI_LITE
 *              `prot` signal is correctly set.
 */

module axi_llc_config #(
  parameter axi_llc_pkg::llc_cfg_t     Cfg        = -1,
  parameter axi_llc_pkg::llc_axi_cfg_t AxiCfg     = -1,
  parameter type                       desc_t         = logic,
  parameter type                       lite_aw_chan_t = logic,
  parameter type                       lite_w_chan_t  = logic,
  parameter type                       lite_b_chan_t  = logic,
  parameter type                       lite_ar_chan_t = logic,
  parameter type                       lite_r_chan_t  = logic,
  parameter type                       lite_req_t     = logic,
  parameter type                       lite_resp_t    = logic,
  parameter type                       rule_full_t    = logic,
  parameter type                       rule_lite_t    = logic
) (
  input  logic clk_i,    // Clock
  input  logic rst_ni,   // Asynchronous reset active low
  // config port
  input  lite_req_t  conf_req_i,
  output lite_resp_t conf_resp_o,
  // SPM lock output
  output logic [Cfg.SetAssociativity-1:0]  spm_lock_o, // only store new tags in not SPM locked ones
  output logic [Cfg.SetAssociativity-1:0]  flushed_o,  // lookup tags in ways not flushed
  // descriptor out (for flushing)
  output desc_t                            desc_o,
  output logic                             desc_valid_o,
  input  logic                             desc_ready_i,
  // AXI address input from slave port for controlling bypass
  input  logic [AxiCfg.AddrWidthFull-1:0]  slv_aw_addr_i,
  input  logic [AxiCfg.AddrWidthFull-1:0]  slv_ar_addr_i,
  output logic                             mst_aw_bypass_o,
  output logic                             mst_ar_bypass_o,
  // flush control signals to prevent new data in ax_cutter loading
  output logic                             llc_isolate_o,
  input  logic                             llc_isolated_i,
  input  logic                             aw_unit_busy_i,
  input  logic                             ar_unit_busy_i,
  input  logic                             flush_desc_recv_i,
  // performance counter inputs for hit/miss ratio determination
  input  logic                             hit_valid_i,
  input  logic                             hit_ready_i,
  input  logic                             miss_valid_i,
  input  logic                             miss_ready_i,
  input  logic                             evict_flag_i,
  input  logic                             refil_flag_i,
  input  logic                             flush_flag_i,
  // BIST input
  input  logic  [Cfg.SetAssociativity-1:0] bist_res_i,
  input  logic                             bist_valid_i,
  // main axi addr rule, used for setting the bypass
  input  rule_full_t                       axi_ram_rule_i,
  input  rule_full_t                       axi_spm_rule_i,
  // Cfg address rule, only listens to start address and computes the rest from that
  input  logic [AxiCfg.LitePortAddrWidth-1:0 ] cfg_start_addr_i
);
  localparam int unsigned LiteStrbWidth = AxiCfg.LitePortDataWidth / 8;
  typedef logic [AxiCfg.LitePortAddrWidth-1:0] addr_t;
  typedef logic [AxiCfg.LitePortDataWidth-1:0] data_t;

  // Definition of the configuration registers.
  // The data width of the AXI LITE port determines the maximum set associativity!
  localparam int unsigned NO_CFG_REGS = 32'd15;
  typedef enum logic [3:0] {
    REG_NO_BLOCKS = 4'b1110, // read only, fixed
    REG_NO_LINES  = 4'b1101, // read only, fixed
    REG_SET_ASSO  = 4'b1100, // read only, fixed

    REG_BIST_OUT  = 4'b1011, // read only
    REG_FLUSHED   = 4'b1010, // read only

    REG_FLUSH_CNT = 4'b1001, // read only
    REG_REFIL_CNT = 4'b1000, // read only
    REG_EVICT_CNT = 4'b0111, // read only
    REG_MISS_CNT  = 4'b0110, // read only
    REG_HIT_CNT   = 4'b0101, // read only
    REG_DESC_CNT  = 4'b0100, // read only
    REG_CYCLE_CNT = 4'b0011, // read only

    REG_PCNT_CFG  = 4'b0010, // read and write [0]: enable, [1]: clear
    REG_FLUSH     = 4'b0001, // read and write
    REG_SPM_CFG   = 4'b0000  // read and write
  } llc_cfg_reg_e;

  // determine the reset value for registers not set to '0.
  localparam int unsigned HalfSetAsso   = Cfg.SetAssociativity / 2;
  localparam addr_t       AddrOffset    = addr_t'(AxiCfg.LitePortDataWidth / 8);
  localparam data_t       CfgResetValue = data_t'('0); // default spm config is all cache
  // define case addresses decode
  rule_lite_t [NO_CFG_REGS-1:0]    cfg_addr_map;
  logic  [$clog2(NO_CFG_REGS)-1:0] aw_reg_idx,       ar_reg_idx;
  logic                            cfg_aw_dec_valid, cfg_ar_dec_valid;

  always_comb begin : proc_lite_addr_map
    // default assignments
    cfg_addr_map = '0;
    for (int unsigned i = 0; i < NO_CFG_REGS; i++) begin
      cfg_addr_map[i].idx        = i;
      cfg_addr_map[i].start_addr = cfg_start_addr_i + i * AddrOffset;
      cfg_addr_map[i].end_addr   = cfg_start_addr_i + i * AddrOffset + AddrOffset;
    end
  end

  // Flipflop signals declaration
  data_t [NO_CFG_REGS-1:0]         config_d,     config_q;
  logic  [LiteStrbWidth-1:0]       load_spm,     load_flush,  load_pcnt_cfg;
  logic                            en_cycle_cnt, en_desc_cnt, en_hit_cnt,    en_miss_cnt;
  logic                            load_aw,      load_ar,     load_flushed;
  // flush flags
  logic [Cfg.SetAssociativity-1:0] to_flush_d,    to_flush_q;
  logic                            load_to_flush;
  // transaction busy flags
  logic                            aw_busy_d, aw_busy_q;
  lite_aw_chan_t                   aw_d,      aw_q;
  logic                            b_busy_d,  b_busy_q;
  logic                            ar_busy_d, ar_busy_q;
  lite_ar_chan_t                   ar_d,      ar_q;
  // counter signals for flush control
  logic                            clear_cnt;
  logic                            en_send_cnt, en_recv_cnt;
  logic                            load_cnt;
  logic [Cfg.IndexLength-1:0]      flush_addr, to_recieve;
  // lzc signals
  logic [$clog2(Cfg.SetAssociativity)-1:0] to_flush_nub;
  logic                                    lzc_empty;
  logic [Cfg.SetAssociativity-1:0]         flush_way_ind;
  // control signals
  logic req_flush;
  logic aw_lock;
  logic clear_flush;

  // spm_lock output are the lowest bit of the registers
  assign spm_lock_o = config_q[REG_SPM_CFG][0+:Cfg.SetAssociativity];
  assign flushed_o  = config_q[REG_FLUSHED][0+:Cfg.SetAssociativity];

  ////////////////////////////////////////////////////////////
  // Write Cfg Register
  ////////////////////////////////////////////////////////////
  always_comb begin : proc_write
    // default assignments
    config_d[REG_PCNT_CFG] = config_q[REG_PCNT_CFG];
    load_pcnt_cfg          = '0;
    config_d[REG_FLUSH]    = config_q[REG_FLUSH];
    load_flush             = '0;
    config_d[REG_SPM_CFG]  = config_q[REG_SPM_CFG];
    load_spm               = '0;
    aw_busy_d              = aw_busy_q;
    aw_d                   = aw_q;
    load_aw                = 1'b0;
    b_busy_d               = b_busy_q;
    // Handshakes
    conf_resp_o.aw_ready   = 1'b0;
    conf_resp_o.w_ready    = 1'b0;
    conf_resp_o.b_valid    = 1'b0;
    // request flush when b response is sent back, activates flush fsm
    req_flush              = 1'b0;

    // B Response output Lite interface
    if (cfg_aw_dec_valid) begin
      conf_resp_o.b.resp = axi_pkg::RESP_OKAY;
    end else begin
      conf_resp_o.b.resp = axi_pkg::RESP_SLVERR;
    end

    // we write the w beat to the register
    if (aw_busy_q && !b_busy_q) begin
      conf_resp_o.w_ready = 1'b1;
      // W transaction
      if (conf_req_i.w_valid) begin
        // only write the data, if decode is valid and protection signal is right!
        if (cfg_aw_dec_valid) begin
          // further are only these two registers writable
          case (llc_cfg_reg_e'(aw_reg_idx))
            REG_PCNT_CFG : begin
              config_d[REG_PCNT_CFG] = conf_req_i.w.data;
              load_pcnt_cfg          = conf_req_i.w.strb;
            end
            REG_FLUSH    : begin
              config_d[REG_FLUSH]    = conf_req_i.w.data;
              load_flush             = conf_req_i.w.strb;
            end
            REG_SPM_CFG  : begin
              config_d[REG_SPM_CFG]  = conf_req_i.w.data;
              load_spm               = conf_req_i.w.strb;
            end
            default : /* do nothing if address is not right */;
          endcase
        end
        // go to state send B, we have written something
        b_busy_d = 1'b1;
      end

    // we send the b response
    end else if (aw_busy_q && b_busy_q) begin
      conf_resp_o.b_valid = 1'b1;
      // B transaction
      if(conf_req_i.b_ready) begin
        aw_busy_d = 1'b0;
        b_busy_d  = 1'b0;
        // request flush if a write was successful
        req_flush = 1'b1;
      end

    // we wait for a aw vector
    end else begin
      // only be ready if aw is not locked
      if(!aw_lock) begin
        conf_resp_o.aw_ready = 1'b1;
        // AW transaction
        if(conf_req_i.aw_valid) begin
          aw_busy_d = 1'b1;
          aw_d      = conf_req_i.aw;
          load_aw   = 1'b1;
        end
      end
      // reset the config_q.flush register, if the user flush is finished
      if(clear_flush) begin
        config_d[REG_FLUSH]  = '0;
        load_flush           = '1;
      end
    end
  end

  addr_decode #(
    .NoIndices ( NO_CFG_REGS ),
    .NoRules   ( NO_CFG_REGS ),
    .addr_t    ( addr_t      ),
    .rule_t    ( rule_lite_t )
  ) i_aw_cfg_addr_decode (
    .addr_i           ( aw_q.addr        ),
    .addr_map_i       ( cfg_addr_map     ),
    .idx_o            ( aw_reg_idx       ),
    .dec_valid_o      ( cfg_aw_dec_valid ),
    .dec_error_o      ( /*not used*/ ),
    .en_default_idx_i ( 1'b0         ), // not used
    .default_idx_i    ( '0           )  // not used
  );

  ////////////////////////////////////////////////////////////
  // Read Cfg Register
  ////////////////////////////////////////////////////////////
  always_comb begin : proc_read
    // default assignments
    ar_busy_d = ar_busy_q;
    ar_d      = ar_q;
    load_ar   = 1'b0;
    // Handshakes
    conf_resp_o.ar_ready = 1'b0;
    conf_resp_o.r_valid  = 1'b0;
    // Read Output Lite interface
    if(cfg_ar_dec_valid) begin
      conf_resp_o.r.data = config_q[ar_reg_idx]; // from addr decode
      conf_resp_o.r.resp = axi_pkg::RESP_OKAY;
    end else begin
      conf_resp_o.r.data = data_t'(32'hBADC0DED);
      conf_resp_o.r.resp = axi_pkg::RESP_SLVERR;
    end

    // Handle the Transactions
    if (ar_busy_q) begin
      conf_resp_o.r_valid  = 1'b1;
      // R transaction
      if (conf_req_i.r_ready) begin
        ar_busy_d = 1'b0;
      end
    // we are ready to take a new read transaction
    end else
      conf_resp_o.ar_ready = 1'b1;
      // AR transaction
      if (conf_req_i.ar_valid) begin
        ar_busy_d = 1'b1;
        ar_d      = conf_req_i.ar;
        load_ar   = 1'b1;
    end
  end

  addr_decode #(
    .NoIndices ( NO_CFG_REGS ),
    .NoRules   ( NO_CFG_REGS ),
    .addr_t    ( addr_t      ),
    .rule_t    ( rule_lite_t )
  ) i_ar_cfg_addr_decode (
    .addr_i           ( ar_q.addr        ),
    .addr_map_i       ( cfg_addr_map     ),
    .idx_o            ( ar_reg_idx       ),
    .dec_valid_o      ( cfg_ar_dec_valid ),
    .dec_error_o      ( /*not used*/     ),
    .en_default_idx_i ( 1'b0             ), // not used
    .default_idx_i    ( '0               )  // not used
  );

  ////////////////////////////////////////////////////////////
  // Flush and Bypass Control
  ////////////////////////////////////////////////////////////
  // states for the control FSM
  typedef enum logic [3:0] {
    FsmIdle,
    FsmWaitAx,
    FsmWaitSplitter,
    FsmInitFlush,
    FsmSendFlush,
    FsmWaitFlush,
    FsmEndFlush
  } flush_fsm_e;
  flush_fsm_e flush_state_d, flush_state_q;
  logic       switch_state;

  // local address maps for bypass 1:DRAM 0:SPM
  rule_full_t [1:0] axi_addr_map;
  always_comb begin : proc_axi_rule
    axi_addr_map[0] = axi_spm_rule_i;
    axi_addr_map[1] = axi_ram_rule_i;
    // define that spm always goes to the llc
    axi_addr_map[0].idx = 1'b0;
    // define that all burst go to the bypass, if flushed is completely set
    axi_addr_map[1].idx = (config_q[REG_FLUSHED][Cfg.SetAssociativity-1:0] == '1);
  end

  addr_decode #(
    .NoIndices ( 2           ),
    .NoRules   ( 2           ),
    .addr_t    ( addr_t      ),
    .rule_t    ( rule_full_t )
  ) i_aw_addr_decode (
    .addr_i           ( slv_aw_addr_i   ),
    .addr_map_i       ( axi_addr_map    ),
    .idx_o            ( mst_aw_bypass_o ),
    .dec_valid_o      ( /*not used*/    ),
    .dec_error_o      ( /*not used*/    ),
    .en_default_idx_i ( 1'b1            ),
    .default_idx_i    ( '0              )  // on decerror go to llc
  );

  addr_decode #(
    .NoIndices ( 2           ),
    .NoRules   ( 2           ),
    .addr_t    ( addr_t      ),
    .rule_t    ( rule_full_t )
  ) i_ar_addr_decode (
    .addr_i           ( slv_ar_addr_i   ),
    .addr_map_i       ( axi_addr_map    ),
    .idx_o            ( mst_ar_bypass_o ),
    .dec_valid_o      ( /*not used*/    ),
    .dec_error_o      ( /*not used*/    ),
    .en_default_idx_i ( 1'b1            ), // on decerror go to llc
    .default_idx_i    ( '0              )
  );

  always_comb begin : proc_flush_control
    // default assignments
    flush_state_d  = flush_state_q;
    // slave port gets isolated during flush
    llc_isolate_o  = 1'b1;
    // flushed register
    config_d[REG_FLUSHED] = config_q[REG_FLUSHED];
    // to flush register
    to_flush_d     = to_flush_q;
    // control signals to proc_write
    desc_valid_o   = 1'b0;
    aw_lock        = 1'b1; // prevent that new AWs get accepted during flushing
    clear_flush    = 1'b0; // clear the user set flush register, if flush finished
    // signals for the descriptor send and receive counters
    clear_cnt      = 1'b0;
    en_send_cnt    = 1'b0;
    en_recv_cnt    = 1'b0;
    load_cnt       = 1'b0;

    // FSM for controlling the AW AR input to the cache and flush control
    unique case (flush_state_q)
      FsmIdle :  begin
        // this state is normal operation, allow Cfg editing and do not isolate main AXI
        aw_lock       = 1'b0;
        llc_isolate_o = 1'b0;
        // change state, if there is a flush request
        if (req_flush) begin
          flush_state_d = FsmWaitAx;
        end
      end
      FsmWaitAx : begin
        // wait until main AXI is free
        if (llc_isolated_i) begin
          flush_state_d = FsmWaitSplitter;
        end
      end
      FsmWaitSplitter : begin
        // wait till none of the splitter units still have vectors in them
        if (!aw_unit_busy_i && !ar_unit_busy_i) begin
          flush_state_d = FsmInitFlush;
        end
      end
      FsmInitFlush : begin
        // this state determines which cache way should be flushed
        // it also sets up the counters for state-keeping how along the flush operation is going
        // define if the user requested a flush
        if (|config_q[REG_FLUSH][Cfg.SetAssociativity-1:0]) begin
          to_flush_d = config_q[REG_FLUSH][Cfg.SetAssociativity-1:0] &
                          ~config_q[REG_FLUSHED][Cfg.SetAssociativity-1:0];
        end else begin
          to_flush_d            = config_q[REG_SPM_CFG][Cfg.SetAssociativity-1:0] &
                                      ~config_q[REG_FLUSHED][Cfg.SetAssociativity-1:0];
          config_d[REG_FLUSHED] = config_q[REG_SPM_CFG][Cfg.SetAssociativity-1:0] &
                                      config_q[REG_FLUSHED][Cfg.SetAssociativity-1:0];
        end
        // now determine if we have something to do at all
        if (to_flush_d == '0) begin
          // nothing to flush, go to idle
          flush_state_d = FsmIdle;
          // reset the flushed register to SPM as new requests can enter the cache
          clear_flush   = 1'b1;
        end else begin
          flush_state_d = FsmSendFlush;
          load_cnt      = 1'b1;
        end
      end
      FsmSendFlush : begin
        // this state sends all required flush descriptors to the specified way
        desc_valid_o = 1'b1;
        // transaction
        if (desc_ready_i) begin
          // last flush descriptor for this way?
          if (flush_addr == '1) begin
            flush_state_d = FsmWaitFlush;
          end else begin
            en_send_cnt = 1'b1;
          end
        end
        // further enable the receive counter if the input signal is high
        if (flush_desc_recv_i) begin
          en_recv_cnt = 1'b1;
        end
      end
      FsmWaitFlush : begin
        // this state waits till all flush operations have exited the cache, then `FsmEndFlush`
        if (flush_desc_recv_i) begin
          if(to_recieve == '0) begin
            flush_state_d = FsmEndFlush;
          end else begin
            en_recv_cnt = 1'b1;
          end
        end
      end
      FsmEndFlush : begin
        // this state decides, if we have other ways to flush, or if we can go back to idle
        clear_cnt    = 1'b1;
        if (to_flush_q == flush_way_ind) begin
          flush_state_d = FsmIdle;
          // reset the flushed register to SPM as new requests can enter the cache
          config_d[REG_FLUSHED][Cfg.SetAssociativity-1:0] =
              config_q[REG_SPM_CFG][Cfg.SetAssociativity-1:0];
          to_flush_d    = '0;
          clear_flush   = 1'b1;
        end else begin
          // there are still ways to flush
          flush_state_d = FsmInitFlush;
          config_d[REG_FLUSHED][Cfg.SetAssociativity-1:0] =
              config_q[REG_FLUSHED][Cfg.SetAssociativity-1:0] | flush_way_ind;
        end
      end
      default : /*do nothing*/;
    endcase
  end

  assign switch_state  = (flush_state_d         != flush_state_q);
  assign load_flushed  = (config_d[REG_FLUSHED] != config_q[REG_FLUSHED]);
  assign load_to_flush = (to_flush_d            != to_flush_q);

  ////////////////////////////////////////////////////////////
  // Flush Descriptor generation
  ////////////////////////////////////////////////////////////
  always_comb begin : proc_desc_o
    // default assignment
    desc_o       = '0;
    // populate descriptor
    desc_o.a_x_addr[Cfg.ByteOffsetLength+Cfg.BlockOffsetLength+:Cfg.IndexLength] = flush_addr;
    desc_o.a_x_burst = axi_pkg::BURST_INCR;
    desc_o.x_resp    = axi_pkg::RESP_OKAY;
    desc_o.way_ind   = flush_way_ind;
    desc_o.flush     = 1'b1;
  end

  // trailing zero counter for determination of way to flush
  lzc #(
  /// The width of the input vector.
  .WIDTH ( Cfg.SetAssociativity ),
  .MODE  (                 1'b0 ) // 0 -> trailing zero, 1 -> leading zero
  ) i_lzc_flush (
  .in_i    ( to_flush_q   ),
  .cnt_o   ( to_flush_nub ),
  .empty_o (    lzc_empty ) // asserted if all bits in in_i are zero
  );
  // onehot indicator signal (decode)
  assign flush_way_ind = (lzc_empty) ? '0 : data_t'(1) << to_flush_nub;

  // counter for flushing control
  counter #(
    .WIDTH      (Cfg.IndexLength)
  ) i_flush_send_counter (
    .clk_i      ( clk_i          ),
    .rst_ni     ( rst_ni         ),
    .clear_i    ( clear_cnt      ),  // synchronous clear
    .en_i       ( en_send_cnt    ),  // enable the counter
    .load_i     ( load_cnt       ),
    .down_i     ( 1'b0           ),  // downcount, default is up
    .d_i        ( '0             ),
    .q_o        ( flush_addr     ),
    .overflow_o ( /*not used*/   )
  );

  counter #(
    .WIDTH      (Cfg.IndexLength)
  ) i_flush_recv_counter (
    .clk_i      ( clk_i             ),
    .rst_ni     ( rst_ni            ),
    .clear_i    ( clear_cnt         ),
    .en_i       ( en_recv_cnt       ),
    .load_i     ( load_cnt          ),
    .down_i     ( 1'b1              ),
    .d_i        ( '1                ),
    .q_o        ( to_recieve        ),
    .overflow_o ( /*not used*/      )
  );

  ////////////////////////////////////////////////////////////
  // performance counter control
  ////////////////////////////////////////////////////////////
  localparam int unsigned ActPerfWidth = (AxiCfg.LitePortDataWidth < axi_llc_pkg::PerfWidth) ?
                                          AxiCfg.LitePortDataWidth : axi_llc_pkg::PerfWidth;
  typedef logic [ActPerfWidth-1:0] perf_t;
  // assign all not defined config_q signals to 0
  if (ActPerfWidth < AxiCfg.LitePortDataWidth) begin : gen_tie_config_cnt_0
    assign config_q[REG_FLUSH_CNT][AxiCfg.LitePortDataWidth-1:ActPerfWidth] = '0;
    assign config_q[REG_REFIL_CNT][AxiCfg.LitePortDataWidth-1:ActPerfWidth] = '0;
    assign config_q[REG_EVICT_CNT][AxiCfg.LitePortDataWidth-1:ActPerfWidth] = '0;
    assign config_q[REG_MISS_CNT] [AxiCfg.LitePortDataWidth-1:ActPerfWidth] = '0;
    assign config_q[REG_HIT_CNT]  [AxiCfg.LitePortDataWidth-1:ActPerfWidth] = '0;
    assign config_q[REG_DESC_CNT] [AxiCfg.LitePortDataWidth-1:ActPerfWidth] = '0;
    assign config_q[REG_CYCLE_CNT][AxiCfg.LitePortDataWidth-1:ActPerfWidth] = '0;
  end

  always_comb begin : proc_perf_cnt
    // default assignments
    config_d[REG_CYCLE_CNT][ActPerfWidth-1:0] = config_q[REG_CYCLE_CNT][ActPerfWidth-1:0];
    en_cycle_cnt                              = 1'b0;
    config_d[REG_DESC_CNT][ActPerfWidth-1:0]  = config_q[REG_DESC_CNT][ActPerfWidth-1:0];
    en_desc_cnt                               = 1'b0;
    config_d[REG_HIT_CNT][ActPerfWidth-1:0]   = config_q[REG_HIT_CNT][ActPerfWidth-1:0];
    en_hit_cnt                                = 1'b0;
    config_d[REG_MISS_CNT][ActPerfWidth-1:0]  = config_q[REG_MISS_CNT][ActPerfWidth-1:0];
    config_d[REG_EVICT_CNT][ActPerfWidth-1:0] = config_q[REG_EVICT_CNT][ActPerfWidth-1:0];
    config_d[REG_REFIL_CNT][ActPerfWidth-1:0] = config_q[REG_REFIL_CNT][ActPerfWidth-1:0];
    config_d[REG_FLUSH_CNT][ActPerfWidth-1:0] = config_q[REG_FLUSH_CNT][ActPerfWidth-1:0];
    en_miss_cnt                               = 1'b0;
    // control when enabled
    if (config_q[REG_PCNT_CFG][32'd1]) begin
      // clear is set
      config_d[REG_CYCLE_CNT][ActPerfWidth-1:0] = '0;
      en_cycle_cnt                              = 1'b1;
      config_d[REG_DESC_CNT][ActPerfWidth-1:0]  = '0;
      en_desc_cnt                               = 1'b1;
      config_d[REG_HIT_CNT][ActPerfWidth-1:0]   = '0;
      en_hit_cnt                                = 1'b1;
      config_d[REG_MISS_CNT][ActPerfWidth-1:0]  = '0;
      config_d[REG_EVICT_CNT][ActPerfWidth-1:0] = '0;
      config_d[REG_REFIL_CNT][ActPerfWidth-1:0] = '0;
      config_d[REG_FLUSH_CNT][ActPerfWidth-1:0] = '0;
      en_miss_cnt                               = 1'b1;
    end else if (config_q[REG_PCNT_CFG][32'd0]) begin
      // no clear but enabled
      // count every cycle regardless of valid flags
      config_d[REG_CYCLE_CNT][ActPerfWidth-1:0] =
          config_q[REG_CYCLE_CNT][ActPerfWidth-1:0] + perf_t'(1);
      en_cycle_cnt = 1'b1;
      if (hit_valid_i && hit_ready_i) begin
        // count hits
        config_d[REG_HIT_CNT][ActPerfWidth-1:0] =
            config_q[REG_HIT_CNT][ActPerfWidth-1:0] + perf_t'(1);
        en_hit_cnt = 1'b1;
      end else if (miss_valid_i && miss_ready_i) begin
        // count misses
        config_d[REG_MISS_CNT][ActPerfWidth-1:0] =
            config_q[REG_MISS_CNT][ActPerfWidth-1:0] + perf_t'(1);
        if (evict_flag_i) begin
          config_d[REG_EVICT_CNT][ActPerfWidth-1:0] =
              config_q[REG_EVICT_CNT][ActPerfWidth-1:0] + perf_t'(1);
        end
        if (refil_flag_i) begin
          config_d[REG_REFIL_CNT][ActPerfWidth-1:0] =
              config_q[REG_REFIL_CNT][ActPerfWidth-1:0] + perf_t'(1);
        end
        if (flush_flag_i) begin
          config_d[REG_FLUSH_CNT][ActPerfWidth-1:0] =
              config_q[REG_FLUSH_CNT][ActPerfWidth-1:0] + perf_t'(1);
        end
        en_miss_cnt            = 1'b1;
      end
      if (en_hit_cnt || en_miss_cnt) begin
        // count descriptors
        config_d[REG_DESC_CNT][ActPerfWidth-1:0] =
            config_q[REG_DESC_CNT][ActPerfWidth-1:0] + perf_t'(1);
        en_desc_cnt            = 1'b1;
      end
    end
  end

  ////////////////////////////////////////////////////////////
  // Assignment of static LLC configuration information
  ////////////////////////////////////////////////////////////
  assign config_q[REG_SET_ASSO]  = data_t'(Cfg.SetAssociativity);
  assign config_q[REG_NO_LINES]  = data_t'(Cfg.NoLines);
  assign config_q[REG_NO_BLOCKS] = data_t'(Cfg.NoBlocks);

  ////////////////////////////////////////////////////////////
  // Configuration FlipFlops
  ////////////////////////////////////////////////////////////
  always_ff @(posedge clk_i, negedge rst_ni) begin
    if (!rst_ni) begin
      aw_busy_q                                 <= '0;
      aw_q                                      <= '0;
      b_busy_q                                  <= '0;
      ar_busy_q                                 <= '0;
      ar_q                                      <= '0;
      to_flush_q                                <= '0;
      flush_state_q                             <= FsmIdle;
      config_q[REG_BIST_OUT]                    <= '0; // read only
      config_q[REG_FLUSHED]                     <= CfgResetValue; // read only has to be the same as SPMCfg default
      config_q[REG_FLUSH_CNT][ActPerfWidth-1:0] <= '0; // only reset the ones that are really
      config_q[REG_REFIL_CNT][ActPerfWidth-1:0] <= '0; // counters, prefent inferring of latches
      config_q[REG_EVICT_CNT][ActPerfWidth-1:0] <= '0;
      config_q[REG_MISS_CNT][ActPerfWidth-1:0]  <= '0;
      config_q[REG_HIT_CNT][ActPerfWidth-1:0]   <= '0;
      config_q[REG_DESC_CNT][ActPerfWidth-1:0]  <= '0;
      config_q[REG_CYCLE_CNT][ActPerfWidth-1:0] <= '0;
      config_q[REG_PCNT_CFG]                    <= '0;
      config_q[REG_FLUSH]                       <= '0;
      config_q[REG_SPM_CFG]                     <= CfgResetValue; // has to be the same as Flushed default
    end else begin
      aw_busy_q    <= aw_busy_d;
      b_busy_q     <= b_busy_d;
      ar_busy_q    <= ar_busy_d;
      // load aw addr
      if (load_aw) begin
        aw_q <= aw_d;
      end
      // load ar addr
      if (load_ar) begin
        ar_q <= ar_d;
      end
      // update BIST response
      if (bist_valid_i) begin
        config_q[REG_BIST_OUT] <= bist_res_i;
      end
      // flush FSM
      if (switch_state) begin
        flush_state_q <= flush_state_d;
      end
      // update to flush register
      if (load_to_flush) begin
        to_flush_q <= to_flush_d;
      end
      // update Flushed register
      if (load_flushed) begin
        config_q[REG_FLUSHED] <= config_d[REG_FLUSHED];
      end
      // update which way should be spm
      for (int unsigned i = 0; i < LiteStrbWidth; i++) begin
        if (load_spm[i]) begin
          config_q[REG_SPM_CFG][i*8+:8] <= config_d[REG_SPM_CFG][i*8+:8];
        end
      end
      // update the user settable flush register
      for (int unsigned i = 0; i < LiteStrbWidth; i++) begin
        if (load_flush[i]) begin
          config_q[REG_FLUSH][i*8+:8] <= config_d[REG_FLUSH][i*8+:8];
        end
      end
      // performance counters
      // update the performance counter cfg
      for (int unsigned i = 0; i < LiteStrbWidth; i++) begin
        if (load_pcnt_cfg[i]) begin
          config_q[REG_PCNT_CFG][i*8+:8] <= config_d[REG_PCNT_CFG][i*8+:8];
        end
      end
      if (en_cycle_cnt) begin
        config_q[REG_CYCLE_CNT][ActPerfWidth-1:0] <= config_d[REG_CYCLE_CNT][ActPerfWidth-1:0];
      end
      if (en_desc_cnt) begin
        config_q[REG_DESC_CNT][ActPerfWidth-1:0] <= config_d[REG_DESC_CNT][ActPerfWidth-1:0];
      end
      if (en_hit_cnt) begin
        config_q[REG_HIT_CNT][ActPerfWidth-1:0] <= config_d[REG_HIT_CNT][ActPerfWidth-1:0];
      end
      if (en_miss_cnt) begin
        config_q[REG_MISS_CNT][ActPerfWidth-1:0]  <= config_d[REG_MISS_CNT][ActPerfWidth-1:0];
        config_q[REG_EVICT_CNT][ActPerfWidth-1:0] <= config_d[REG_EVICT_CNT][ActPerfWidth-1:0];
        config_q[REG_REFIL_CNT][ActPerfWidth-1:0] <= config_d[REG_REFIL_CNT][ActPerfWidth-1:0];
        config_q[REG_FLUSH_CNT][ActPerfWidth-1:0] <= config_d[REG_FLUSH_CNT][ActPerfWidth-1:0];
      end
    end
  end

  initial begin : proc_check_params
    set_asso      : assume (Cfg.SetAssociativity <= AxiCfg.LitePortDataWidth) else
      $fatal(1, $sformatf("LLCCfg > The maximum set associativity has to be equal or smaller than \
                           the data width of the configuration AXI LITE."));
    axi_lite_data : assume ((AxiCfg.LitePortDataWidth == 32'd64) ||
                            (AxiCfg.LitePortDataWidth == 32'd32)) else
      $warning("LitePortDataWidth > Not using AXI4 defined LITE data width!!!");
  end

  initial begin : proc_llc_hello
    @(posedge rst_ni);
    $display("###############################################################################");
    $display("###############################################################################");
    $display("LLC module instantiated!");
    $display("###############################################################################");
    $display("Cache Size parameters:");
    $display($sformatf("SetAssociativity (Number of Ways)  (decimal): %d", Cfg.SetAssociativity ));
    $display($sformatf("Number of Cache Lines per Set      (decimal): %d", Cfg.NoLines          ));
    $display($sformatf("Number of Blocks per Cache Line    (decimal): %d", Cfg.NoBlocks         ));
    $display($sformatf("Block Sizs in Bits                 (decimal): %d", Cfg.BlockSize        ));
    $display($sformatf("Tag Length of Axi Address          (decimal): %d", Cfg.TagLength        ));
    $display($sformatf("Index Length of Axi Address        (decimal): %d", Cfg.IndexLength      ));
    $display($sformatf("Block Offset Length of Axi Address (decimal): %d", Cfg.BlockOffsetLength));
    $display($sformatf("Byte Offset Length of Axi Address  (decimal): %d", Cfg.ByteOffsetLength ));
    $display("###############################################################################");
    $display("AXI Port parameters:");
    $display("Slave port (CPU):");
    $display($sformatf("ID   width (decimal): %d", AxiCfg.SlvPortIdWidth ));
    $display($sformatf("ADDR width (decimal): %d", AxiCfg.AddrWidthFull  ));
    $display($sformatf("DATA width (decimal): %d", AxiCfg.DataWidthFull  ));
    $display($sformatf("STRB width (decimal): %d", AxiCfg.DataWidthFull/8));
    $display("Master port (memory):");
    $display($sformatf("ID   width (decimal): %d", AxiCfg.SlvPortIdWidth + 1));
    $display($sformatf("ADDR width (decimal): %d", AxiCfg.AddrWidthFull     ));
    $display($sformatf("DATA width (decimal): %d", AxiCfg.DataWidthFull     ));
    $display($sformatf("STRB width (decimal): %d", AxiCfg.DataWidthFull/8   ));
    $display("Config LITE port:");
    $display($sformatf("ADDR width (decimal): %d", AxiCfg.LitePortAddrWidth  ));
    $display($sformatf("DATA width (decimal): %d", AxiCfg.LitePortDataWidth  ));
    $display($sformatf("STRB width (decimal): %d", AxiCfg.LitePortDataWidth/8));
    $display("###############################################################################");
    $display("Address mapping information:");
    $display($sformatf("Ram Start Address (hex): %h", axi_ram_rule_i.start_addr ));
    $display($sformatf("Ram End   Address (hex): %h", axi_ram_rule_i.end_addr   ));
    $display($sformatf("SPM Start Address (hex): %h", axi_spm_rule_i.start_addr ));
    $display($sformatf("SPM End   Address (hex): %h", axi_spm_rule_i.end_addr   ));
    $display($sformatf("CFG:REG_SPM_CFG   (hex): %h", cfg_addr_map[REG_SPM_CFG  ].start_addr ));
    $display($sformatf("CFG:REG_FLUSH     (hex): %h", cfg_addr_map[REG_FLUSH    ].start_addr ));
    $display($sformatf("CFG:REG_PCNT_CFG  (hex): %h", cfg_addr_map[REG_PCNT_CFG ].start_addr ));
    $display($sformatf("CFG:REG_CYCLE_CNT (hex): %h", cfg_addr_map[REG_CYCLE_CNT].start_addr ));
    $display($sformatf("CFG:REG_DESC_CNT  (hex): %h", cfg_addr_map[REG_DESC_CNT ].start_addr ));
    $display($sformatf("CFG:REG_HIT_CNT   (hex): %h", cfg_addr_map[REG_HIT_CNT  ].start_addr ));
    $display($sformatf("CFG:REG_MISS_CNT  (hex): %h", cfg_addr_map[REG_MISS_CNT ].start_addr ));
    $display($sformatf("CFG:REG_EVICT_CNT (hex): %h", cfg_addr_map[REG_EVICT_CNT].start_addr ));
    $display($sformatf("CFG:REG_REFIL_CNT (hex): %h", cfg_addr_map[REG_REFIL_CNT].start_addr ));
    $display($sformatf("CFG:REG_FLUSH_CNT (hex): %h", cfg_addr_map[REG_FLUSH_CNT].start_addr ));
    $display($sformatf("CFG:REG_FLUSHED   (hex): %h", cfg_addr_map[REG_FLUSHED  ].start_addr ));
    $display($sformatf("CFG:REG_BIST_OUT  (hex): %h", cfg_addr_map[REG_BIST_OUT ].start_addr ));
    $display($sformatf("CFG:REG_SET_ASSO  (hex): %h", cfg_addr_map[REG_SET_ASSO ].start_addr ));
    $display($sformatf("CFG:REG_NO_LINES  (hex): %h", cfg_addr_map[REG_NO_LINES ].start_addr ));
    $display($sformatf("CFG:REG_NO_BLOCKS (hex): %h", cfg_addr_map[REG_NO_BLOCKS].start_addr ));
    $display("###############################################################################");
    $display("###############################################################################");
  end
endmodule
