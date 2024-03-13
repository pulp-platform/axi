// Copyright 2024 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Authors:
// - Gianna Paulin <pauling@iis.ee.ethz.ch>
// - Thomas Benz <tbenz@iis.ee.ethz.ch>

`include "common_cells/registers.svh"
/// AXI4+ATOP slave module which translates AXI bursts into a memory stream
/// which behaves as a memory containing only `0` data which cannot be
/// overwritten by `write` operations.
/// - `read`: grants the request and returns data `0`.
/// - `write`: grants the request, write data goes into nothingness (can be used as data sink)
/// If both read and write channels of the AXI4+ATOP are active, both will have an
/// utilization of 50%.
module axi_zero_mem #(
  /// AXI4+ATOP request type. See `include/axi/typedef.svh`.
  parameter type         axi_req_t  = logic,
  /// AXI4+ATOP response type. See `include/axi/typedef.svh`.
  parameter type         axi_resp_t = logic,
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
  /// Dependent parameter, do not override. Memory address type.
  localparam type addr_t     = logic [AddrWidth-1:0],
  /// Dependent parameter, do not override. Memory data type.
  localparam type mem_data_t = logic [DataWidth/NumBanks-1:0],
  /// Dependent parameter, do not override. Memory write strobe type.
  localparam type mem_strb_t = logic [DataWidth/NumBanks/8-1:0]
) (
  /// Clock input.
  input  logic                           clk_i,
  /// Asynchronous reset, active low.
  input  logic                           rst_ni,
  /// The unit is busy handling an AXI4+ATOP request.
  output logic                           busy_o,
  /// AXI4+ATOP slave port, request input.
  input  axi_req_t                       axi_req_i,
  /// AXI4+ATOP slave port, response output.
  output axi_resp_t                      axi_resp_o
);

  logic zero_mem_gnt, zero_mem_req, zero_mem_we;
  logic zero_mem_valid_req_d, zero_mem_valid_req_q;

  axi_to_detailed_mem #(
    .axi_req_t   ( axi_req_t  ),
    .axi_resp_t  ( axi_resp_t ),
    .AddrWidth   ( AddrWidth  ),
    .DataWidth   ( DataWidth  ),
    .IdWidth     ( IdWidth    ),
    .NumBanks    ( 32'd1      ),
    .BufDepth    ( BufDepth   ),
    .HideStrb    (  1'b0      ),
    .OutFifoDepth( 32'd1      )
  ) i_axi_to_detailed_mem (
    .clk_i,
    .rst_ni,
    .busy_o,
    .axi_req_i,
    .axi_resp_o,
    .mem_req_o    ( zero_mem_req         ),
    .mem_gnt_i    ( zero_mem_gnt         ),
    .mem_addr_o   ( /* NC */             ),
    .mem_wdata_o  ( /* NC */             ),
    .mem_strb_o   ( /* NC */             ),
    .mem_atop_o   ( /* NC */             ),
    .mem_lock_o   ( /* NC */             ),
    .mem_we_o     ( /* NC */             ),
    .mem_id_o     ( /* NC */             ),
    .mem_user_o   ( /* NC */             ),
    .mem_cache_o  ( /* NC */             ),
    .mem_prot_o   ( /* NC */             ),
    .mem_qos_o    ( /* NC */             ),
    .mem_region_o ( /* NC */             ),
    .mem_rvalid_i ( zero_mem_valid_req_q ),
    .mem_rdata_i  ( '0                   ),
    .mem_err_i    ( 1'b0                 ),
    .mem_exokay_i ( 1'b0                 )
  );

  assign zero_mem_gnt = zero_mem_req;
  assign zero_mem_valid_req_d = zero_mem_gnt & zero_mem_req;

  `FF(zero_mem_valid_req_q, zero_mem_valid_req_d, '0, clk_i, rst_ni)

endmodule
