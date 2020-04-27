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

// Author: Andreas Kurth  <akurth@iis.ee.ethz.ch>

/// Internal module of [`axi_tlb`](module.axi_tlb): L1 translation table.
module axi_tlb_l1 #(
  /// Width of addresses in input address space
  parameter int unsigned InpAddrWidth = 0,
  /// Width of addresses in output address space
  parameter int unsigned OupAddrWidth = 0,
  /// Number of entries in translation table
  parameter int unsigned NumEntries = 0,
  /// Address width of configuration AXI4-Lite port
  parameter int unsigned CfgAxiAddrWidth = 0,
  /// Data width of configuration AXI4-Lite port
  parameter int unsigned CfgAxiDataWidth = 0,
  /// Request type of configuration AXI4-Lite slave port
  parameter type lite_req_t = logic,
  /// Response type of configuration AXI4-Lite slave port
  parameter type lite_resp_t = logic,
  /// Type of translation result.  Must have a single-bit field `hit` and an `addr` field as wide as
  /// the output address.
  parameter type res_t = logic,
  /// Derived (=do not override) type of input addresses
  parameter type inp_addr_t = logic [InpAddrWidth-1:0],
  /// Derived (=do not override) type of output addresses
  parameter type oup_addr_t = logic [OupAddrWidth-1:0]
) (
  /// Rising-edge clock of all ports
  input  logic        clk_i,
  /// Asynchronous reset, active low
  input  logic        rst_ni,
  /// Test mode enable
  input  logic        test_en_i,
  /// Write request input address
  input  inp_addr_t   wr_req_addr_i,
  /// Write request valid
  input  logic        wr_req_valid_i,
  /// Write request ready
  output logic        wr_req_ready_o,
  /// Write translation result
  output res_t        wr_res_o,
  /// Write translation result valid
  output logic        wr_res_valid_o,
  /// Write translation result ready
  input  logic        wr_res_ready_i,
  /// Read request input address
  input  inp_addr_t   rd_req_addr_i,
  /// Read request valid
  input  logic        rd_req_valid_i,
  /// Read request ready
  output logic        rd_req_ready_o,
  /// Read translation result
  output res_t        rd_res_o,
  /// Read translation result valid
  output logic        rd_res_valid_o,
  /// Read translation result ready
  input  logic        rd_res_ready_i,
  /// Configuration port request
  input  lite_req_t   cfg_req_i,
  /// Configuration port response
  output lite_resp_t  cfg_resp_o
);

  localparam int unsigned InpPageNumWidth = InpAddrWidth - 12;
  localparam int unsigned OupPageNumWidth = OupAddrWidth - 12;

  /// Page number in input address space
  typedef logic [InpPageNumWidth-1:0] inp_page_t;
  /// Page number in output address space
  typedef logic [OupPageNumWidth-1:0] oup_page_t;
  /// Translation table entry with 4 KiB page granularity
  typedef struct packed {
    /// Number of first page in input address segment
    inp_page_t  first;
    /// Number of last page (inclusive) in input address segment
    inp_page_t  last;
    /// Number of first page in output address segment; that is, the output address segment starts
    /// at this `base` page.
    oup_page_t  base;
    /// Defines whether this entry is valid.
    logic       valid;
    /// Defines whether this entry can only be used for read accesses.
    logic       read_only;
  } entry_t;

  entry_t [NumEntries-1:0]  entries;
  inp_page_t                wr_req_page,
                            rd_req_page;

  // Write channel
  assign wr_req_page = wr_req_addr_i >> 12;
  axi_tlb_l1_chan #(
    .NumEntries     ( NumEntries  ),
    .IsWriteChannel ( 1'b1        ),
    .req_page_t     ( inp_page_t  ),
    .entry_t        ( entry_t     ),
    .res_t          ( res_t       )
  ) i_wr_chan (
    .clk_i,
    .rst_ni,
    .test_en_i,
    .entries_i    ( entries         ),
    .req_page_i   ( wr_req_page     ),
    .req_valid_i  ( wr_req_valid_i  ),
    .req_ready_o  ( wr_req_ready_o  ),
    .res_o        ( wr_res_o        ),
    .res_valid_o  ( wr_res_valid_o  ),
    .res_ready_i  ( wr_res_ready_i  )
  );

  // Read channel
  assign rd_req_page = rd_req_addr_i >> 12;
  axi_tlb_l1_chan #(
    .NumEntries     ( NumEntries  ),
    .IsWriteChannel ( 1'b0        ),
    .req_page_t     ( inp_page_t  ),
    .entry_t        ( entry_t     ),
    .res_t          ( res_t       )
  ) i_rd_chan (
    .clk_i,
    .rst_ni,
    .test_en_i,
    .entries_i    ( entries         ),
    .req_page_i   ( rd_req_page     ),
    .req_valid_i  ( rd_req_valid_i  ),
    .req_ready_o  ( rd_req_ready_o  ),
    .res_o        ( rd_res_o        ),
    .res_valid_o  ( rd_res_valid_o  ),
    .res_ready_i  ( rd_res_ready_i  )
  );

  // Table entries from AXI4-Lite registers
  localparam NumAxiRegs = 13; // TODO
  localparam RegDataWidth = 42; // TODO
  axi_lite_regs #(
    .NumAxiRegs     ( NumAxiRegs      ),
    .AxiAddrWidth   ( CfgAxiAddrWidth ),
    .AxiDataWidth   ( CfgAxiDataWidth ),
    .PrivProtOnly   ( 1'b0            ),
    .SecuProtOnly   ( 1'b0            ),
    .RegDataWidth   ( RegDataWidth    ),
    .AxiReadOnly    ( 1'b0            ),
    .req_lite_t     ( lite_req_t      ),
    .resp_lite_t    ( lite_resp_t     )
  ) i_regs (
    .clk_i,
    .rst_ni,
    .axi_req_i        ( cfg_req_i                             ),
    .axi_resp_o       ( cfg_resp_o                            ),
    .axi_base_addr_i  ( /* TODO */                            ),
    .axi_wr_idx_o     ( /* unused */                          ),
    .axi_wr_active_o  ( /* unused */                          ),
    .axi_rd_idx_o     ( /* unused */                          ),
    .axi_rd_active_o  ( /* unused */                          ),
    .reg_d_i          ( '{NumAxiRegs{'{RegDataWidth{1'b0}}}}  ),
    .reg_load_i       ( '{NumAxiRegs{1'b0}}                   ),
    .reg_q_o          ( /* TODO */                            )
  );

  `ifndef VERILATOR
  // pragma translate_off
  initial begin
    assert (InpAddrWidth > 12)
      else $fatal(1, "Input address space must be larger than one 4 KiB page!");
    assert (OupAddrWidth > 12)
      else $fatal(1, "Output address space must be larger than one 4 KiB page!");
  end
  // pragma translate_on
  `endif

endmodule


/// Internal module of [`axi_tlb_l1`](module.axi_tlb_l1): Channel handler.
module axi_tlb_l1_chan #(
  /// Number of entries in translation table
  parameter int unsigned NumEntries = 0,
  /// Is this channel is used for writes?
  parameter logic IsWriteChannel = 1'b0,
  /// Type of request page number
  parameter type req_page_t = logic,
  /// Type of a translation table entry
  parameter type entry_t = logic,
  /// Type of translation result
  parameter type res_t = logic
) (
  /// Rising-edge clock
  input  logic                    clk_i,
  /// Asynchronous reset, active low
  input  logic                    rst_ni,
  /// Test mode enable
  input  logic                    test_en_i,
  /// Translation table entries
  input  entry_t [NumEntries-1:0] entries_i,
  /// Request page number
  input  req_page_t               req_page_i,
  /// Request valid
  input  logic                    req_valid_i,
  /// Request ready
  output logic                    req_ready_o,
  /// Translation result
  output res_t                    res_o,
  /// Translation result valid
  output logic                    res_valid_o,
  /// Translation result ready
  input  logic                    res_ready_i
);

  localparam int unsigned EntryIdxWidth = NumEntries > 1 ? $clog2(NumEntries) : 1;

  typedef logic [EntryIdxWidth-1:0] entry_idx_t;

  // Determine all entries matching a request.
  logic [NumEntries-1:0] entry_matches;
  for (genvar i = 0; i < NumEntries; i++) begin : gen_matches
    assign entry_matches[i] = entries[i].valid & req_valid_i
        & (req_page_i >= entries[i].first)
        & (req_page_i <= entries[i].last)
        & (~IsWriteChannel | ~entries[i].read_only);
  end

  // Determine entry with lowest index that matches the request.
  entry_idx_t match_idx;
  logic       no_match;
  lzc #(
    .WIDTH  ( NumEntries  ),
    .MODE   ( 1'b0        )   // trailing zeros -> lowest match
  ) i_lzc (
    .in_i     ( entry_matches ),
    .cnt_o    ( match_idx     ),
    .empty_o  ( no_match      )
  );

  // Handle request and translate address.
  logic res_valid, res_ready;
  res_t res;
  always_comb begin
    res_valid = 1'b0;
    req_ready_o = 1'b0;
    res = '{default: '0};
    if (req_valid_i) begin
      res_o.hit = ~no_match;
      res_o.addr = (entries[match_idx].base + (req_page_i - entries[match_idx].first)) << 12;
      res_valid = 1'b1;
      req_ready_o = res_ready;
    end
  end
  // Store translation in fall-through register.  This prevents changes in the translated address
  // due to changes in `entries` while downstream handshake is outstanding.
  fall_through_register #(
    .T  ( res_t )
  ) i_res_ft_reg (
    .clk_i,
    .rst_ni,
    .clr_i      ( 1'b0        ),
    .testmode_i ( test_en_i   ),
    .valid_i    ( res_valid   ),
    .ready_o    ( res_ready   ),
    .data_i     ( res         ),
    .valid_o    ( res_valid_o ),
    .ready_i    ( res_ready_i ),
    .data_o     ( res_o       )
  );

endmodule
