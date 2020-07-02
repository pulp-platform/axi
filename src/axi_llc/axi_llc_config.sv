// Copyright 2019 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the “License”); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an “AS IS” BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// File:   axi_llc_config.sv
// Author: Wolfgang Roenninger <wroennin@iis.ee.ethz.ch>
// Date:   17.06.2019

/// # Configuration of `axi_llc`
///
/// Contains the configuration registers of the `axi_llc`.
///
/// ## Register Map
///
/// The configuration registers are exposed over an AXI4-Lite port.
/// Registers are all 8-byte aligned.
///
/// Detailed descriptions of the individual registers can be found below.
///
/// | Name        | Address (HEX) | read/write | Description                                      |
/// |:-----------:|:-------------:|:----------:|:------------------------------------------------:|
/// | `CfgSpm`    | `0x00`        | read-write | [SPM Configuration](###CfgSpm)                   |
/// | `CfgFlush`  | `0x08`        | read-write | [Flush Configuration](###CfgFlush)               |
/// | `Flushed`   | `0x10`        | read-only  | [Flushed Flag](###Flushed)                       |
/// | `BistOut`   | `0x18`        | read-only  | [Tag Storage BIST Result](###BistOut)            |
/// | `SetAsso`   | `0x20`        | read-only  | [Instantiated Set-Associativity](###SetAsso)     |
/// | `NumLines`  | `0x28`        | read-only  | [Instantiated Number of Cache-Lines](###NumLines)|
/// | `NumBlocks` | `0x30`        | read-only  | [Instantiated Number of Blocks](###NumBlocks)    |
/// | `Version`   | `0x38`        | read-only  | [AXI LLC Version](###Version)                    |
///
/// ### CfgSpm
///
/// The scratch-pad-memory configuration register.
/// This register is read and writable on the AXI4-Lite port.
///
/// Register Bit Map:
/// | Bits                    | Reset Value | Function                |
/// |:-----------------------:|:-----------:|:-----------------------:|
/// | `[0]`                   | `1'b0`      | SPM Configuration Set-0 |
/// | ...                     | ...         | ...                     |
/// | `[SetAssociativity-1]`  | `1'b0`      | SPM Configuration Set-X |
/// | `[63:SetAssociativity]` | `'0`        | Reserved                |
///
///
/// ### CfgFlush
///
/// Flush configuration register.
/// This register is read and writable on the AXI4-Lite port.
///
/// This register enables flushing of individual cache sets.
///
/// Register Bit Map:
/// | Bits                    | Reset Value | Function            |
/// |:-----------------------:|:-----------:|:-------------------:|
/// | `[0]`                   | `1'b0`      | Flush Trigger Set-0 |
/// | ...                     | ...         | ...                 |
/// | `[SetAssociativity-1]`  | `1'b0`      | Flush Trigger Set-X |
/// | `[63:SetAssociativity]` | `'0`        | Reserved            |
///
///
/// ### Flushed
///
/// Flushed status of the individual cache sets.
/// This register is read only on the AXI4-Lite port.
///
/// These bits are set, if the corresponding set is in a flushed state.
/// Sets configured as SPM will have the corresponding bits set.
///
/// Register Bit Map:
/// | Bits                    | Reset Value | Function               |
/// |:-----------------------:|:-----------:|:----------------------:|
/// | `[0]`                   | `1'b0`      | Flushed Status Set-0   |
/// | ...                     | ...         | ...                    |
/// | `[SetAssociativity-1]`  | `1'b0`      | Flushed Status Set-X   |
/// | `[63:SetAssociativity]` | `'0`        | Reserved               |
///
///
/// ### BistOut
///
/// Build-in self-test result of the tag-storage macros.
/// When
///
/// Register Bit Map:
/// | Bits                    | Reset Value | Function         |
/// |:-----------------------:|:-----------:|:----------------:|
/// | `[0]`                   | `1'b0`      | BIST Error Set-0 |
/// | ...                     | ...         | ...              |
/// | `[SetAssociativity-1]`  | `1'b0`      | BIST Error Set-X |
/// | `[63:SetAssociativity]` | `'0`        | Reserved         |
///
///
/// ### SetAsso
///
/// Register showing the instantiated cache set-associativity.
/// This register is read only on the AXI4-Lite port.
///
/// Equal to the parameter of `axi_llc_top` `SetAssociativity`.
///
/// Register Bit Map:
/// | Bits     | Reset Value        | Function          |
/// |:--------:|:------------------:|:-----------------:|
/// | `[63:0]` | `SetAssociativity` | Set-Associativity |
///
///
/// ### NumLines
///
/// Register showing the instantiated number of cache lines per set.
/// This register is read only on the AXI4-Lite port.
///
/// Equal to the parameter of `axi_llc_top` `NumLines`.
///
/// Register Bit Map:
/// | Bits     | Reset Value | Function        |
/// |:--------:|:-----------:|:---------------:|
/// | `[63:0]` | `NumLines`   | Number of Lines |
///
///
/// ### `NumBlocks`
///
/// Register showing the instantiated number of blocks per cache-line.
/// This register is read only on the AXI4-Lite port.
///
/// Equal to the parameter of `axi_llc_top` `NumBlocks`.
///
/// Register Bit Map:
/// | Bits     | Reset Value | Function         |
/// |:--------:|:-----------:|:----------------:|
/// | `[63:0]` | `NumBlocks`  | Number of Blocks |
///
///
/// ### `Version`
///
/// Register showing the instantiated version of the module `axi_llc`.
/// This register is read only on the AXI4-Lite port.
///
/// This value is defined by `axi_llc_pkg::AxiLlcVersion`.
///
/// Register Bit Map:
/// | Bits     | Reset Value                   | Function                    |
/// |:--------:|:-----------------------------:|:---------------------------:|
/// | `[63:0]` | `axi_llc_pkg::AxiLlcVersion`  | Shows the `axi_llc_version` |
///
module axi_llc_config #(
  /// Static AXI LLC configuration.
  parameter axi_llc_pkg::llc_cfg_t Cfg = axi_llc_pkg::llc_cfg_t'{default: '0},
  /// Give the exact AXI parameters in struct form. This is passed down from
  /// [`axi_llc_top`](module.axi_llc_top).
  ///
  /// Required struct definition in: `axi_llc_pkg`.
  parameter axi_llc_pkg::llc_axi_cfg_t AxiCfg = axi_llc_pkg::llc_axi_cfg_t'{default: '0},
  /// Descriptor type. This is requires as this module emits the flush descriptors.
  /// Struct definition is in [`axi_llc_top`](module.axi_llc_top).
  parameter type desc_t = logic,
  /// AXI4-Lite request struct definition.
  parameter type lite_req_t = logic,
  /// AXI4-Lite response struct definition.
  parameter type lite_resp_t = logic,
  /// Address rule struct for `common_cells/addr_decode`. Is used for bypass `axi_demux`
  /// steering.
  parameter type rule_full_t = logic,
  /// Type for indicating the set associativity, same as way_ind_t in `axi_llc_top`.
  parameter type set_asso_t = logic,
  /// Address type for the memory regions defined for caching and SPM. The same width as
  /// the address field of the AXI4+ATOP slave and master port.
  parameter type addr_full_t = logic
) (
  /// Rising-edge clock
  input logic clk_i,
  /// Asynchronous reset, active low
  input logic rst_ni,
  /// AXI4-Lite slave port request.
  ///
  /// Here the configuration registers are exposed.
  input lite_req_t conf_req_i,
  /// AXI4-Lite slave port response.
  ///
  /// Here the configuration registers are exposed.
  output lite_resp_t conf_resp_o,
  /// SPM lock.
  ///
  /// The cache only stores new tags in ways which are not SPM locked.
  output set_asso_t spm_lock_o,
  /// Flushed way flag.
  ///
  /// This signal defines all ways which are flushed and have no valid tags in them.
  /// Tags are not looked up in the ways which are flushed.
  output set_asso_t flushed_o,
  /// Flush descriptor output.
  ///
  /// Payload data for flush descriptors. These descriptors are generated either by configuring
  /// cache ways to SPM or when an explicit flush was triggered.
  output desc_t desc_o,
  /// Flush descriptor handshake, valid
  output logic desc_valid_o,
  /// Flush descriptor handshake, ready
  input logic desc_ready_i,
  /// AXI4 AW address from AXI4 slave port.
  ///
  /// This is for controlling the bypass multiplexer.
  input addr_full_t slv_aw_addr_i,
  /// AXI4 AR address from AXI4 slave port.
  ///
  /// This is for controlling the bypass multiplexer.
  input addr_full_t slv_ar_addr_i,
  /// Bypass selection for the AXI AW channel.
  output logic mst_aw_bypass_o,
  /// Bypass selection for the AXI AR channel.
  output logic mst_ar_bypass_o,
  /// Isolate the AXI slave port.
  ///
  /// Flush control sets this signal to prevent active cache accesses during flushing.
  /// This is to preserve data integrity when a cache flush is underway.
  output logic llc_isolate_o,
  /// The AXI salve port is isolated.
  ///
  /// This signals the flush FSM that it can safely perform the flush.
  input logic llc_isolated_i,
  /// The AW descriptor generation unit is busy.
  ///
  /// This signal is needed for the flush control so that no active functional descriptors
  /// interfere with the flush operation.
  input logic aw_unit_busy_i,
  /// The AR descriptor generation unit is busy.
  ///
  /// This signal is needed for the flush control so that no active functional descriptors
  /// interfere with the flush operation.
  input logic ar_unit_busy_i,
  /// A flush descriptor is finished flushing its cache line.
  ///
  /// This is for controlling the counters which keep track of how many flush descriptors are
  /// underway.
  input logic flush_desc_recv_i,
  /// Result data of the BIST from the tag storage macros.
  input set_asso_t bist_res_i,
  /// Result data of the BIST from the tag storage macros is valid.
  input logic bist_valid_i,
  /// Address rule for the AXI memory region which maps onto the cache.
  ///
  /// This rule is used to set the AXI LLC bypass.
  /// If all cache ways are flushed, accesses onto this address region take the bypass directly
  /// to main memory.
  input  rule_full_t axi_cached_rule_i,
  /// Address rule for the AXI memory region which maps to the scratch pad memory region.
  ///
  /// Accesses are only successful, if the corresponding way is mapped as SPM
  input  rule_full_t axi_spm_rule_i
);
  // register macros from `common_cells`
  `include "common_cells/registers.svh"

  // Define the configuration register address alignment.
  localparam int unsigned AlignToBytes = 32'd8;
  localparam int unsigned CfgRegWidth  = 32'd8 * AlignToBytes;
  // Data type definition for the union which maps the Cfg regs to the structs.
  typedef logic [7:0]                        byte_t;
  typedef logic [CfgRegWidth-1:0]            data_cfg_t;
  typedef logic [AlignToBytes-1:0]           strb_cfg_t;
  // Type for the Set Associativity puls padding
  localparam int unsigned SetAssoPadWidth = CfgRegWidth - Cfg.SetAssociativity;
  typedef logic [SetAssoPadWidth-1:0]        pad_asso_t; // Zero padding

  // Definition of the configuration registers.
  // The registers are aligned to `AlignToBytes`.
  localparam int unsigned NumCfgRegs      = 32'd8;
  localparam int unsigned NumBytesCfgRegs = AlignToBytes * NumCfgRegs;

  // Define the struct mapping of all configuration registers.
  // Functional bits are byte aligned to `AlignToBytes`.
  typedef struct packed {
    data_cfg_t Version;     // read only, fixed
    data_cfg_t NumBlocks;   // read only, fixed
    data_cfg_t NumLines;    // read only, fixed
    data_cfg_t SetAsso;     // read only, fixed
    pad_asso_t PadBistOut;  // Map to '0
    set_asso_t BistOut;     // read only
    pad_asso_t PadFlushed;  // Map to '0
    set_asso_t Flushed;     // read only
    pad_asso_t PadFlush;    // Map to '0
    set_asso_t CfgFlush;    // read and write
    pad_asso_t PadSpm;      // Map to '0
    set_asso_t CfgSpm;      // read and write
  } struct_reg_data_t;
  // Struct for strobe values for each register:
  typedef struct packed {
    strb_cfg_t Version;
    strb_cfg_t NumBlocks;
    strb_cfg_t NumLines;
    strb_cfg_t SetAsso;
    strb_cfg_t BistOut;
    strb_cfg_t Flushed;
    strb_cfg_t CfgFlush;
    strb_cfg_t CfgSpm;
  } struct_reg_strb_t;

  // Define a union for the configuration register data:
  // * Once as pure bytes for the module `i_axi_lite_regs`.
  // * Once as `struct_reg_data_t` for easy access into the individual fields.
  // Be careful with with the assignment of the zero padding inside the struct representation!
  typedef union packed {
    byte_t [NumBytesCfgRegs-1:0] ByteMap;
    struct_reg_data_t            StructMap;
  } union_reg_data_t;

  typedef union packed {
    logic [NumBytesCfgRegs-1:0]  LogicMap;
    struct_reg_strb_t            StrbMap;
  } union_reg_strb_t;

  // define the reset value for the configuration registers.
  localparam union_reg_data_t CfgRstValue = struct_reg_data_t'{
    Version:   data_cfg_t'(axi_llc_pkg::AxiLlcVersion),
    NumBlocks: data_cfg_t'(Cfg.NumBlocks),
    NumLines:  data_cfg_t'(Cfg.NumLines),
    SetAsso:   data_cfg_t'(Cfg.SetAssociativity),
    default:   '0
  };

  // define the read-only values for the individual aligned registers
  localparam union_reg_strb_t CfgReadOnly = struct_reg_strb_t'{
    Version:   {AlignToBytes{1'b1}}, // read-only
    NumBlocks: {AlignToBytes{1'b1}}, // read-only
    NumLines:  {AlignToBytes{1'b1}}, // read-only
    SetAsso:   {AlignToBytes{1'b1}}, // read-only
    BistOut:   {AlignToBytes{1'b1}}, // read-only
    Flushed:   {AlignToBytes{1'b1}}, // read-only
    CfgFlush:  {AlignToBytes{1'b0}}, // read and write
    CfgSpm:    {AlignToBytes{1'b0}}  // read and write
  };

  // Flipflop signals declaration
  union_reg_data_t config_d,    config_q; // Configuration register mapped to AXI
  union_reg_strb_t config_load;           // Load enable for the configuration registers
  union_reg_strb_t config_wr;             // AXI has written to this configuration register

  // Counter signals for flush control
  logic                                    clear_cnt;
  logic                                    en_send_cnt, en_recv_cnt;
  logic                                    load_cnt;
  logic [Cfg.IndexLength-1:0]              flush_addr,  to_recieve;
  // Trailing zero counter signals, for flush descriptor generation.
  logic [$clog2(Cfg.SetAssociativity)-1:0] to_flush_nub;
  logic                                    lzc_empty;
  set_asso_t                               flush_way_ind;

  ////////////////////////
  // AXI Bypass control //
  ////////////////////////
  // local address maps for bypass 1:Bypass 0:LLC
  rule_full_t [1:0] axi_addr_map;
  always_comb begin : proc_axi_rule
    axi_addr_map[0] = axi_spm_rule_i;
    axi_addr_map[1] = axi_cached_rule_i;
    // Define that accesses to the SPM region always go into the `axi_llc`.
    axi_addr_map[0].idx = 1'b0;
    // define that all burst go to the bypass, if flushed is completely set
    axi_addr_map[1].idx = &config_q.StructMap.Flushed;
  end

  addr_decode #(
    .NoIndices ( 32'd2       ),
    .NoRules   ( 32'd2       ),
    .addr_t    ( addr_full_t ),
    .rule_t    ( rule_full_t )
  ) i_aw_addr_decode (
    .addr_i           ( slv_aw_addr_i   ),
    .addr_map_i       ( axi_addr_map    ),
    .idx_o            ( mst_aw_bypass_o ),
    .dec_valid_o      ( /*not used*/    ),
    .dec_error_o      ( /*not used*/    ),
    .en_default_idx_i ( 1'b1            ),
    .default_idx_i    ( 1'b1            )  // on decerror go through bypass
  );

  addr_decode #(
    .NoIndices ( 32'd2       ),
    .NoRules   ( 32'd2       ),
    .addr_t    ( addr_full_t ),
    .rule_t    ( rule_full_t )
  ) i_ar_addr_decode (
    .addr_i           ( slv_ar_addr_i   ),
    .addr_map_i       ( axi_addr_map    ),
    .idx_o            ( mst_ar_bypass_o ),
    .dec_valid_o      ( /*not used*/    ),
    .dec_error_o      ( /*not used*/    ),
    .en_default_idx_i ( 1'b1            ), // on decerror go through bypass
    .default_idx_i    ( 1'b1            )
  );

  //////////////////////////////////////////////////////////////////
  // Configuration registers: Flush Control, Performance Counters //
  //////////////////////////////////////////////////////////////////
  // States for the control FSM
  typedef enum logic [3:0] {
    FsmIdle,
    FsmWaitAx,
    FsmWaitSplitter,
    FsmInitFlush,
    FsmSendFlush,
    FsmWaitFlush,
    FsmEndFlush,
    FsmPreInit
  } flush_fsm_e;
  flush_fsm_e flush_state_d, flush_state_q;
  logic       switch_state;
  set_asso_t  to_flush_d,    to_flush_q;
  logic       load_to_flush;

  `FFLARN(flush_state_q, flush_state_d, switch_state, FsmPreInit, clk_i, rst_ni)
  `FFLARN(to_flush_q, to_flush_d, load_to_flush, '0, clk_i, rst_ni)
  // Load enable signals, so that the FF is only active when needed.
  assign switch_state  = (flush_state_d != flush_state_q);
  assign load_to_flush = (to_flush_d    != to_flush_q);

  always_comb begin : proc_axi_llc_cfg
    // Default assignments
    // Ensure that the struct padding is always '0!
    // Not used fields are also tied to '0!
    config_d.StructMap = struct_reg_data_t'{
      Version:   data_cfg_t'(axi_llc_pkg::AxiLlcVersion),
      NumBlocks: data_cfg_t'(Cfg.NumBlocks),
      NumLines:  data_cfg_t'(Cfg.NumLines),
      SetAsso:   data_cfg_t'(Cfg.SetAssociativity),
      BistOut:   bist_res_i,
      Flushed:   config_q.StructMap.Flushed,
      CfgFlush:  config_q.StructMap.CfgFlush,
      CfgSpm:    config_q.StructMap.CfgSpm,
      default:   '0
    };
    // load enables, default is zero, if needed set below
    config_load.StrbMap = struct_reg_strb_t'{
      BistOut:  {AlignToBytes{bist_valid_i}},
      CfgFlush: {AlignToBytes{1'b1}},        // default one to prevent overwrite from AXI on flush
      CfgSpm:   {AlignToBytes{1'b1}},        // default one to prevent overwrite from AXI on flush
      default: '0
    };
    // Flush state machine
    flush_state_d  = flush_state_q;
    // Slave port is isolated during flush.
    llc_isolate_o  = 1'b1;
    // To flush register, holds the ways which have to be flushed.
    to_flush_d     = to_flush_q;
    // Emit flush descriptors.
    desc_valid_o   = 1'b0;
    // Default signal definitions for the descriptor send and receive counter control.
    clear_cnt      = 1'b0;
    en_send_cnt    = 1'b0;
    en_recv_cnt    = 1'b0;
    load_cnt       = 1'b0;

    // FSM for controlling the AW AR input to the cache and flush control
    unique case (flush_state_q)
      FsmIdle:  begin
        // this state is normal operation, allow Cfg editing of the fields `CfgSpm` and `CfgFlush`
        // and do not isolate main AXI
        config_load.StrbMap.CfgSpm   = strb_cfg_t'(1'b0);
        config_load.StrbMap.CfgFlush = strb_cfg_t'(1'b0);
        llc_isolate_o                = 1'b0;
        // Change state, if there is a flush request, i.e. if one of the configuration fields
        // has been written by AXI
        if ((|config_wr.StrbMap.CfgSpm) || (|config_wr.StrbMap.CfgFlush)) begin
          flush_state_d = FsmWaitAx;
        end
      end
      FsmWaitAx: begin
        // wait until main AXI is free
        if (llc_isolated_i) begin
          flush_state_d = FsmWaitSplitter;
        end
      end
      FsmWaitSplitter: begin
        // wait till none of the splitter units still have vectors in them
        if (!aw_unit_busy_i && !ar_unit_busy_i) begin
          flush_state_d = FsmInitFlush;
        end
      end
      FsmInitFlush: begin
        // this state determines which cache way should be flushed
        // it also sets up the counters for state-keeping how along the flush operation is going
        // define if the user requested a flush
        if (|config_q.StructMap.CfgFlush) begin
          to_flush_d = config_q.StructMap.CfgFlush & ~config_q.StructMap.Flushed;
        end else begin
          to_flush_d                  = config_q.StructMap.CfgSpm & ~config_q.StructMap.Flushed;
          config_d.StructMap.Flushed  = config_q.StructMap.CfgSpm &  config_q.StructMap.Flushed;
          config_load.StrbMap.Flushed = {AlignToBytes{1'b1}};
        end
        // now determine if we have something to do at all
        if (to_flush_d == '0) begin
          // nothing to flush, go to idle
          flush_state_d = FsmIdle;
          // reset the flushed register to SPM as new requests can enter the cache
          // load signal od `CfgFlush` is default 1
          config_d.StructMap.CfgFlush = set_asso_t'(1'b0);
        end else begin
          flush_state_d = FsmSendFlush;
          load_cnt      = 1'b1;
        end
      end
      FsmSendFlush: begin
        // this state sends all required flush descriptors to the specified way
        desc_valid_o = 1'b1;
        // transaction
        if (desc_ready_i) begin
          // last flush descriptor for this way?
          if (flush_addr == {Cfg.IndexLength{1'b1}}) begin
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
          if(to_recieve == {Cfg.IndexLength{1'b0}}) begin
            flush_state_d = FsmEndFlush;
          end else begin
            en_recv_cnt = 1'b1;
          end
        end
      end
      FsmEndFlush: begin
        // this state decides, if we have other ways to flush, or if we can go back to idle
        clear_cnt    = 1'b1;
        if (to_flush_q == flush_way_ind) begin
          flush_state_d = FsmIdle;
          // reset the flushed register to SPM as new requests can enter the cache
          config_d.StructMap.Flushed  = config_q.StructMap.CfgSpm;
          config_load.StrbMap.Flushed = {AlignToBytes{1'b1}};
          to_flush_d                  = set_asso_t'(1'b0);
          // Clear the `CfgFlush` register, load enable is default '1
          config_d.StructMap.CfgFlush = set_asso_t'(1'b0);
        end else begin
          // there are still ways to flush
          flush_state_d               = FsmInitFlush;
          config_d.StructMap.Flushed  = config_q.StructMap.Flushed | flush_way_ind;
          config_load.StrbMap.Flushed = {AlignToBytes{1'b1}};
        end
      end
      FsmPreInit: begin
        // The state machine starts in this state. It remains in this state until the
        // BIST of the tag storage macros is finished.
        // When the result of the BIST comes in, it is also written to the SPM configuration.
        // However does not trigger a flush. This is to have per default tag-macros with errors
        // to be mapped as SPM, so that they are not used. However they can be enabled using
        // the normal SPM configuration.
        if (bist_valid_i) begin
          flush_state_d               = FsmIdle;
          config_d.StructMap.CfgSpm   = bist_res_i;
          // No load specified for CfgSpm, as per default the reg is loaded anyway.
          config_d.StructMap.Flushed  = bist_res_i;
          config_load.StrbMap.Flushed = {AlignToBytes{1'b1}};
        end
      end
      default : /*do nothing*/;
    endcase
  end

  ////////////////////////
  // Output assignments //
  ////////////////////////
  // Flush descriptor output is static, except for the fields defined here.
  assign desc_o = desc_t'{
    a_x_addr:  {{Cfg.TagLength{1'b0}}, flush_addr, {Cfg.ByteOffsetLength+Cfg.BlockOffsetLength{1'b0}}},
    a_x_len:   axi_pkg::len_t'(Cfg.NumBlocks - 32'd1),
    a_x_size:  axi_pkg::size_t'($clog2(Cfg.BlockSize / 32'd8)),
    a_x_burst: axi_pkg::BURST_INCR,
    x_resp:    axi_pkg::RESP_OKAY,
    way_ind:   flush_way_ind,
    flush:     1'b1,
    default:   '0
  };
  // Configuration registers which are used in other modules.
  assign spm_lock_o = config_q.StructMap.CfgSpm;
  assign flushed_o  = config_q.StructMap.Flushed;

  // This trailing zero counter determines which way should be flushed next.
  lzc #(
    .WIDTH ( Cfg.SetAssociativity ),
    .MODE  ( 1'b0                 )
  ) i_lzc_flush (
    .in_i    ( to_flush_q   ),
    .cnt_o   ( to_flush_nub ),
    .empty_o ( lzc_empty    )
  );
  // Decode flush way indicator from binary to one-hot signal.
  assign flush_way_ind = (lzc_empty) ? set_asso_t'(1'b0) : set_asso_t'(64'd1) << to_flush_nub;

  ///////////////////////////////
  // Counter for flush control //
  ///////////////////////////////
  // This counts how many flush descriptors have been sent.
  counter #(
    .WIDTH ( Cfg.IndexLength )
  ) i_flush_send_counter (
    .clk_i      ( clk_i                   ),
    .rst_ni     ( rst_ni                  ),
    .clear_i    ( clear_cnt               ),
    .en_i       ( en_send_cnt             ),
    .load_i     ( load_cnt                ),
    .down_i     ( 1'b0                    ),
    .d_i        ( {Cfg.IndexLength{1'b0}} ),
    .q_o        ( flush_addr              ),
    .overflow_o ( /*not used*/            )
  );

  // This counts how many flush descriptors are not done flushing.
  counter #(
    .WIDTH ( Cfg.IndexLength )
  ) i_flush_recv_counter (
    .clk_i      ( clk_i                   ),
    .rst_ni     ( rst_ni                  ),
    .clear_i    ( clear_cnt               ),
    .en_i       ( en_recv_cnt             ),
    .load_i     ( load_cnt                ),
    .down_i     ( 1'b1                    ),
    .d_i        ( {Cfg.IndexLength{1'b1}} ),
    .q_o        ( to_recieve              ),
    .overflow_o ( /*not used*/            )
  );

  ///////////////////////////////////////
  // AXI4-Lite configuration registers //
  ///////////////////////////////////////
  // This module holds the configuration registers which can be accessed over the AXI4-Lite port.
  axi_lite_regs#(
    .RegNumBytes  ( NumBytesCfgRegs          ),
    .AxiAddrWidth ( AxiCfg.LitePortAddrWidth ),
    .AxiDataWidth ( AxiCfg.LitePortDataWidth ),
    .PrivProtOnly ( 1'b0                     ),
    .SecuProtOnly ( 1'b0                     ),
    .AxiReadOnly  ( CfgReadOnly.LogicMap     ),
    .RegRstVal    ( CfgRstValue.ByteMap      ),
    .req_lite_t   ( lite_req_t               ),
    .resp_lite_t  ( lite_resp_t              )
  ) i_axi_lite_regs (
    .clk_i,
    .rst_ni,
    .axi_req_i   ( conf_req_i           ),
    .axi_resp_o  ( conf_resp_o          ),
    .wr_active_o ( config_wr.LogicMap   ),
    .rd_active_o ( /*Not used*/         ),
    .reg_d_i     ( config_d.ByteMap     ),
    .reg_load_i  ( config_load.LogicMap ),
    .reg_q_o     ( config_q.ByteMap     )
  );

  initial begin : proc_check_params
    set_asso      : assert (Cfg.SetAssociativity < CfgRegWidth) else
        $fatal(1, $sformatf("LlcCfg: The maximum set associativity (%0d) has to be smaller than \
                             the the configuration register alignment in bits: %0d (dec).\n \
                             Reason: SystemVerilog requires a min struct field width of one.",
                             Cfg.SetAssociativity, CfgRegWidth));
    axi_lite_data : assume ((AxiCfg.LitePortDataWidth == 32'd64) ||
                            (AxiCfg.LitePortDataWidth == 32'd32)) else
        $warning("LitePortDataWidth: Not using AXI4 defined LITE data width!!!");
  end

  initial begin : proc_llc_hello
    @(posedge rst_ni);
    $display("###############################################################################");
    $display("###############################################################################");
    $display("AXI LLC module instantiated:");
    $display("%m");
    $display("###############################################################################");
    $display("Cache Size parameters:");
    $display($sformatf("SetAssociativity (Number of Ways)  (decimal): %d", Cfg.SetAssociativity ));
    $display($sformatf("Number of Cache Lines per Set      (decimal): %d", Cfg.NumLines         ));
    $display($sformatf("Number of Blocks per Cache Line    (decimal): %d", Cfg.NumBlocks        ));
    $display($sformatf("Block Size in Bits                 (decimal): %d", Cfg.BlockSize        ));
    $display($sformatf("Tag Length of AXI Address          (decimal): %d", Cfg.TagLength        ));
    $display($sformatf("Index Length of AXI Address        (decimal): %d", Cfg.IndexLength      ));
    $display($sformatf("Block Offset Length of AXI Address (decimal): %d", Cfg.BlockOffsetLength));
    $display($sformatf("Byte Offset Length of AXI Address  (decimal): %d", Cfg.ByteOffsetLength ));
    $display("###############################################################################");
    $display("AXI4 Port parameters:");
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
    $display("Address mapping information:");
    $display($sformatf("Ram Start Address (hex): %h", axi_cached_rule_i.start_addr ));
    $display($sformatf("Ram End   Address (hex): %h", axi_cached_rule_i.end_addr   ));
    $display($sformatf("SPM Start Address (hex): %h", axi_spm_rule_i.start_addr    ));
    $display($sformatf("SPM End   Address (hex): %h", axi_spm_rule_i.end_addr      ));
    $display("###############################################################################");
    $display("###############################################################################");
//     $display($sformatf("CFG:REG_SPM_CFG   (hex): %h", cfg_addr_map[REG_SPM_CFG  ].start_addr ));
//     $display($sformatf("CFG:REG_FLUSH     (hex): %h", cfg_addr_map[REG_FLUSH    ].start_addr ));
//     $display($sformatf("CFG:REG_PCNT_CFG  (hex): %h", cfg_addr_map[REG_PCNT_CFG ].start_addr ));
//     $display($sformatf("CFG:REG_CYCLE_CNT (hex): %h", cfg_addr_map[REG_CYCLE_CNT].start_addr ));
//     $display($sformatf("CFG:REG_DESC_CNT  (hex): %h", cfg_addr_map[REG_DESC_CNT ].start_addr ));
//     $display($sformatf("CFG:REG_HIT_CNT   (hex): %h", cfg_addr_map[REG_HIT_CNT  ].start_addr ));
//     $display($sformatf("CFG:REG_MISS_CNT  (hex): %h", cfg_addr_map[REG_MISS_CNT ].start_addr ));
//     $display($sformatf("CFG:REG_EVICT_CNT (hex): %h", cfg_addr_map[REG_EVICT_CNT].start_addr ));
//     $display($sformatf("CFG:REG_REFIL_CNT (hex): %h", cfg_addr_map[REG_REFIL_CNT].start_addr ));
//     $display($sformatf("CFG:REG_FLUSH_CNT (hex): %h", cfg_addr_map[REG_FLUSH_CNT].start_addr ));
//     $display($sformatf("CFG:REG_FLUSHED   (hex): %h", cfg_addr_map[REG_FLUSHED  ].start_addr ));
//     $display($sformatf("CFG:REG_BIST_OUT  (hex): %h", cfg_addr_map[REG_BIST_OUT ].start_addr ));
//     $display($sformatf("CFG:REG_SET_ASSO  (hex): %h", cfg_addr_map[REG_SET_ASSO ].start_addr ));
//     $display($sformatf("CFG:REG_NO_LINES  (hex): %h", cfg_addr_map[REG_NO_LINES ].start_addr ));
//     $display($sformatf("CFG:REG_NO_BLOCKS (hex): %h", cfg_addr_map[REG_NO_BLOCKS].start_addr ));
//     $display("###############################################################################");
  end
endmodule
