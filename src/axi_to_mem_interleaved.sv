// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Authors:
// - Wolfgang Roenninger <wroennin@iis.ee.ethz.ch>
// - Thomas Benz <tbenz@iis.ee.ethz.ch>
// - Michael Rogenmoser <michaero@iis.ee.ethz.ch>

/// AXI4+ATOP to SRAM memory subordinate. Allows for parallel read and write transactions.
/// Allows reads to bypass writes, in contrast to `axi_to_mem`, however needs more hardware.
module axi_to_mem_interleaved #(
  /// AXI4+ATOP request type. See `include/axi/typedef.svh`.
  parameter type         axi_req_t  = logic,
  /// AXI4+ATOP response type. See `include/axi/typedef.svh`.
  parameter type         axi_rsp_t  = logic,
  /// Address width, has to be less or equal than the width off the AXI address field.
  /// Determines the width of `mem_addr_o`. Has to be wide enough to emit the memory region
  /// which should be accessible.
  parameter int unsigned AddrWidth  = 0,
  /// AXI4+ATOP data width.
  parameter int unsigned DataWidth  = 0,
  /// AXI4+ATOP ID width.
  parameter int unsigned IdWidth    = 0,
  /// Number of banks at output, must evenly divide `DataWidth`.
  parameter int unsigned NumBanks   = 0,
  /// Depth of memory response buffer. This should be equal to the memory response latency.
  parameter int unsigned BufDepth   = 1,
  /// Hide write requests if the strb == '0
  parameter bit          HideStrb   = 1'b0,
  /// Depth of output fifo/fall_through_register. Increase for asymmetric backpressure (contention) on banks.
  parameter int unsigned OutFifoDepth = 1,
  /// Dependent parameter, do not override. Memory address type.
  parameter type addr_t     = logic [AddrWidth-1:0],
  /// Dependent parameter, do not override. Memory data type.
  parameter type mem_data_t = logic [DataWidth/NumBanks-1:0],
  /// Dependent parameter, do not override. Memory write strobe type.
  parameter type mem_strb_t = logic [DataWidth/NumBanks/8-1:0]
) (
  /// Clock input.
  input  logic                           clk_i,
  /// Asynchronous reset, active low.
  input  logic                           rst_ni,
  /// The unit is busy handling an AXI4+ATOP request.
  output logic                           busy_o,
  /// AXI4+ATOP subordinate port, request input.
  input  axi_req_t                       axi_req_i,
  /// AXI4+ATOP subordinate port, response output.
  output axi_rsp_t                       axi_rsp_o,
  /// Memory stream manager, request is valid for this bank.
  output logic           [NumBanks-1:0]  mem_req_o,
  /// Memory stream manager, request can be granted by this bank.
  input  logic           [NumBanks-1:0]  mem_gnt_i,
  /// Memory stream manager, byte address of the request.
  output addr_t          [NumBanks-1:0]  mem_addr_o,
  /// Memory stream manager, write data for this bank. Valid when `mem_req_o`.
  output mem_data_t      [NumBanks-1:0]  mem_wdata_o,
  /// Memory stream manager, byte-wise strobe (byte enable).
  output mem_strb_t      [NumBanks-1:0]  mem_strb_o,
  /// Memory stream manager, `axi_pkg::atop_t` signal associated with this request.
  output axi_pkg::atop_t [NumBanks-1:0]  mem_atop_o,
  /// Memory stream manager, write enable. Then asserted store of `mem_w_data` is requested.
  output logic           [NumBanks-1:0]  mem_we_o,
  /// Memory stream manager, response is valid. This module expects always a response valid for a
  /// request regardless if the request was a write or a read.
  input  logic           [NumBanks-1:0]  mem_rvalid_i,
  /// Memory stream manager, read response data.
  input  mem_data_t      [NumBanks-1:0]  mem_rdata_i
);

  // internal signals
  logic w_busy, r_busy;
  logic [NumBanks-1:0] arb_outcome, arb_outcome_head;

  // internal AXI buses
  axi_req_t r_axi_req, w_axi_req;
  axi_rsp_t r_axi_rsp, w_axi_rsp;

  // internal TCDM buses
  logic           [NumBanks-1:0]  r_mem_req,    w_mem_req;
  logic           [NumBanks-1:0]  r_mem_gnt,    w_mem_gnt;
  addr_t          [NumBanks-1:0]  r_mem_addr,   w_mem_addr;
  mem_data_t      [NumBanks-1:0]  r_mem_wdata,  w_mem_wdata;
  mem_strb_t      [NumBanks-1:0]  r_mem_strb,   w_mem_strb;
  axi_pkg::atop_t [NumBanks-1:0]  r_mem_atop,   w_mem_atop;
  logic           [NumBanks-1:0]  r_mem_we,     w_mem_we;
  logic           [NumBanks-1:0]  r_mem_rvalid, w_mem_rvalid;
  mem_data_t      [NumBanks-1:0]  r_mem_rdata,  w_mem_rdata;

  // split AXI bus in read and write
  always_comb begin : proc_axi_rw_split
    axi_rsp_o.r          = r_axi_rsp.r;
    axi_rsp_o.r_valid    = r_axi_rsp.r_valid;
    axi_rsp_o.ar_ready   = r_axi_rsp.ar_ready;
    axi_rsp_o.b          = w_axi_rsp.b;
    axi_rsp_o.b_valid    = w_axi_rsp.b_valid;
    axi_rsp_o.w_ready    = w_axi_rsp.w_ready;
    axi_rsp_o.aw_ready   = w_axi_rsp.aw_ready;

    w_axi_req             = '0;
    w_axi_req.aw          = axi_req_i.aw;
    w_axi_req.aw_valid    = axi_req_i.aw_valid;
    w_axi_req.w           = axi_req_i.w;
    w_axi_req.w_valid     = axi_req_i.w_valid;
    w_axi_req.b_ready     = axi_req_i.b_ready;

    r_axi_req             = '0;
    r_axi_req.ar          = axi_req_i.ar;
    r_axi_req.ar_valid    = axi_req_i.ar_valid;
    r_axi_req.r_ready     = axi_req_i.r_ready;
  end

  axi_to_mem #(
    .axi_req_t   ( axi_req_t    ),
    .axi_rsp_t   ( axi_rsp_t    ),
    .AddrWidth   ( AddrWidth    ),
    .DataWidth   ( DataWidth    ),
    .IdWidth     ( IdWidth      ),
    .NumBanks    ( NumBanks     ),
    .BufDepth    ( BufDepth     ),
    .HideStrb    ( HideStrb     ),
    .OutFifoDepth( OutFifoDepth )
  ) i_axi_to_mem_write (
    .clk_i        ( clk_i         ),
    .rst_ni       ( rst_ni        ),
    .busy_o       ( w_busy        ),
    .axi_req_i    ( w_axi_req     ),
    .axi_rsp_o    ( w_axi_rsp     ),
    .mem_req_o    ( w_mem_req     ),
    .mem_gnt_i    ( w_mem_gnt     ),
    .mem_addr_o   ( w_mem_addr    ),
    .mem_wdata_o  ( w_mem_wdata   ),
    .mem_strb_o   ( w_mem_strb    ),
    .mem_atop_o   ( w_mem_atop    ),
    .mem_we_o     ( w_mem_we      ),
    .mem_rvalid_i ( w_mem_rvalid  ),
    .mem_rdata_i  ( w_mem_rdata   )
  );

  axi_to_mem #(
    .axi_req_t    ( axi_req_t    ),
    .axi_rsp_t    ( axi_rsp_t    ),
    .AddrWidth    ( AddrWidth    ),
    .DataWidth    ( DataWidth    ),
    .IdWidth      ( IdWidth      ),
    .NumBanks     ( NumBanks     ),
    .BufDepth     ( BufDepth     ),
    .HideStrb     ( HideStrb     ),
    .OutFifoDepth ( OutFifoDepth )
  ) i_axi_to_mem_read (
    .clk_i        ( clk_i         ),
    .rst_ni       ( rst_ni        ),
    .busy_o       ( r_busy        ),
    .axi_req_i    ( r_axi_req     ),
    .axi_rsp_o    ( r_axi_rsp     ),
    .mem_req_o    ( r_mem_req     ),
    .mem_gnt_i    ( r_mem_gnt     ),
    .mem_addr_o   ( r_mem_addr    ),
    .mem_wdata_o  ( r_mem_wdata   ),
    .mem_strb_o   ( r_mem_strb    ),
    .mem_atop_o   ( r_mem_atop    ),
    .mem_we_o     ( r_mem_we      ),
    .mem_rvalid_i ( r_mem_rvalid  ),
    .mem_rdata_i  ( r_mem_rdata   )
  );

  // create a struct for the rr-arb-tree
  typedef struct packed {
    addr_t          addr;
    mem_data_t      wdata;
    mem_strb_t      strb;
    logic           we;
    axi_pkg::atop_t atop;
  } mem_req_payload_t;

  mem_req_payload_t [NumBanks-1:0] r_payload, w_payload, payload;

  for (genvar i = 0; i < NumBanks; i++) begin
    // pack the mem
    assign r_payload[i].addr  = r_mem_addr[i];
    assign r_payload[i].wdata = r_mem_wdata[i];
    assign r_payload[i].strb  = r_mem_strb[i];
    assign r_payload[i].we    = r_mem_we[i];
    assign r_payload[i].atop  = r_mem_atop[i];

    assign w_payload[i].addr  = w_mem_addr[i];
    assign w_payload[i].wdata = w_mem_wdata[i];
    assign w_payload[i].strb  = w_mem_strb[i];
    assign w_payload[i].we    = w_mem_we[i];
    assign w_payload[i].atop  = w_mem_atop[i];

    assign mem_addr_o [i] = payload[i].addr;
    assign mem_wdata_o[i] = payload[i].wdata;
    assign mem_strb_o [i] = payload[i].strb;
    assign mem_we_o   [i] = payload[i].we;
    assign mem_atop_o [i] = payload[i].atop;

    // route data back to both channels
    assign w_mem_rdata[i]  = mem_rdata_i[i];
    assign r_mem_rdata[i]  = mem_rdata_i[i];

    assign w_mem_rvalid[i] = mem_rvalid_i[i] & !arb_outcome_head[i];
    assign r_mem_rvalid[i] = mem_rvalid_i[i] &  arb_outcome_head[i];

    // fine-grain arbitration
    rr_arb_tree #(
      .NumIn     ( 2                 ),
      .DataType  ( mem_req_payload_t )
    ) i_rr_arb_tree (
      .clk_i    ( clk_i                          ),
      .rst_ni   ( rst_ni                         ),
      .flush_i  ( 1'b0                           ),
      .rr_i     (  '0                            ),
      .req_i    ( { r_mem_req[i], w_mem_req[i] } ),
      .gnt_o    ( { r_mem_gnt[i], w_mem_gnt[i] } ),
      .data_i   ( { r_payload[i], w_payload[i] } ),
      .req_o    ( mem_req_o[i]                   ),
      .gnt_i    ( mem_gnt_i[i]                   ),
      .data_o   ( payload[i]                     ),
      .idx_o    ( arb_outcome[i]                 )
    );

    // back-routing store
    fifo_v3 #(
      .DATA_WIDTH ( 1            ),
      .DEPTH      ( BufDepth + 1 )
    ) i_fifo_v3_response_trgt_store (
      .clk_i      ( clk_i                       ),
      .rst_ni     ( rst_ni                      ),
      .flush_i    ( 1'b0                        ),
      .testmode_i ( 1'b0                        ),
      .full_o     ( ),
      .empty_o    ( ),
      .usage_o    ( ),
      .data_i     ( arb_outcome[i]              ),
      .push_i     ( mem_req_o[i] & mem_gnt_i[i] ),
      .data_o     ( arb_outcome_head[i]         ),
      .pop_i      ( mem_rvalid_i[i]             )
    );
  end

endmodule : axi_to_mem_interleaved
