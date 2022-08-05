// Copyright 2022 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Author:
// Michael Rogenmoser <michaero@iis.ee.ethz.ch>

`include "axi/assign.svh"
/// AXI4+ATOP to memory-protocol interconnect. Completely separates the read and write channel to
/// individual mem ports. This can only be used when addresses for the same bank are accessible
/// from different memory ports.
module axi_to_mem_split #(
  /// AXI4+ATOP request type. See `include/axi/typedef.svh`.
  parameter type         axi_req_t    = logic,
  /// AXI4+ATOP response type. See `include/axi/typedef.svh`.
  parameter type         axi_resp_t   = logic,
  /// Address width, has to be less or equal than the width off the AXI address field.
  /// Determines the width of `mem_addr_o`. Has to be wide enough to emit the memory region
  /// which should be accessible.
  parameter int unsigned AddrWidth    = 0,
  /// AXI4+ATOP data width.
  parameter int unsigned AxiDataWidth = 0,
  /// AXI4+ATOP ID width.
  parameter int unsigned IdWidth      = 0,
  /// Memory data width, must evenly divide `DataWidth`.
  parameter int unsigned MemDataWidth = 0, // must divide `AxiDataWidth` without remainder
  /// Depth of memory response buffer. This should be equal to the memory response latency.
  parameter int unsigned BufDepth     = 0,
  /// Hide write requests if the strb == '0
  parameter bit          HideStrb   = 1'b0,
  /// Dependent parameters, do not override. Number of memory ports.
  parameter int unsigned NumMemPorts  = 2*AxiDataWidth/MemDataWidth,
  /// Dependent parameter, do not override. Memory address type.
  parameter type         addr_t       = logic [AddrWidth-1:0],
  /// Dependent parameter, do not override. Memory data type.
  parameter type         mem_data_t   = logic [MemDataWidth-1:0],
  /// Dependent parameter, do not override. Memory write strobe type.
  parameter type         mem_strb_t   = logic [MemDataWidth/8-1:0]
) (
  /// Clock input.
  input logic                              clk_i,
  /// Asynchronous reset, active low.
  input logic                              rst_ni,
  /// The unit is busy handling an AXI4+ATOP request.
  output logic                             busy_o,
  /// AXI4+ATOP slave port, request input.
  input  axi_req_t                         axi_req_i,
  /// AXI4+ATOP slave port, response output.
  output axi_resp_t                        axi_resp_o,
  /// Memory stream master, request is valid for this bank.
  output logic           [NumMemPorts-1:0] mem_req_o,
  /// Memory stream master, request can be granted by this bank.
  input  logic           [NumMemPorts-1:0] mem_gnt_i,
  /// Memory stream master, byte address of the request.
  output addr_t          [NumMemPorts-1:0] mem_addr_o,   // byte address
  /// Memory stream master, write data for this bank. Valid when `mem_req_o`.
  output mem_data_t      [NumMemPorts-1:0] mem_wdata_o,  // write data
  /// Memory stream master, byte-wise strobe (byte enable).
  output mem_strb_t      [NumMemPorts-1:0] mem_strb_o,   // byte-wise strobe
  /// Memory stream master, `axi_pkg::atop_t` signal associated with this request.
  output axi_pkg::atop_t [NumMemPorts-1:0] mem_atop_o,   // atomic operation
  /// Memory stream master, write enable. Then asserted store of `mem_w_data` is requested.
  output logic           [NumMemPorts-1:0] mem_we_o,     // write enable
  /// Memory stream master, response is valid. This module expects always a response valid for a
  /// request regardless if the request was a write or a read.
  input  logic           [NumMemPorts-1:0] mem_rvalid_i, // response valid
  /// Memory stream master, read response data.
  input  mem_data_t      [NumMemPorts-1:0] mem_rdata_i   // read data
);

  axi_req_t axi_read_req, axi_write_req;
  axi_resp_t axi_read_resp, axi_write_resp;

  logic read_busy, write_busy;

  always_comb begin: proc_axi_rw_split
    `AXI_SET_R_STRUCT(axi_resp_o.r, axi_read_resp.r)
    axi_resp_o.r_valid     = axi_read_resp.r_valid;
    axi_resp_o.ar_ready    = axi_read_resp.ar_ready;
    `AXI_SET_B_STRUCT(axi_resp_o.b, axi_write_resp.b)
    axi_resp_o.b_valid     = axi_write_resp.b_valid;
    axi_resp_o.aw_ready    = axi_write_resp.aw_ready;
    axi_resp_o.w_ready     = axi_write_resp.w_ready;

    axi_write_req = '0;
    `AXI_SET_AW_STRUCT(axi_write_req.aw, axi_req_i.aw)
    axi_write_req.aw_valid = axi_req_i.aw_valid;
    `AXI_SET_W_STRUCT(axi_write_req.w, axi_req_i.w)
    axi_write_req.w_valid = axi_req_i.w_valid;
    axi_write_req.b_ready = axi_req_i.b_ready;

    axi_read_req = '0;
    `AXI_SET_AR_STRUCT(axi_read_req.ar, axi_req_i.ar)
    axi_read_req.ar_valid = axi_req_i.ar_valid;
    axi_read_req.r_ready  = axi_req_i.r_ready;
  end

  assign busy_o = read_busy || write_busy;

  axi_to_mem #(
    .axi_req_t  ( axi_req_t     ),
    .axi_resp_t ( axi_resp_t    ),
    .AddrWidth  ( AddrWidth     ),
    .DataWidth  ( AxiDataWidth  ),
    .IdWidth    ( IdWidth       ),
    .NumBanks   ( NumMemPorts/2 ),
    .BufDepth   ( BufDepth      ),
    .HideStrb   ( 1'b0          )
  ) i_axi_to_mem_read (
    .clk_i,
    .rst_ni,
    .busy_o       ( read_busy                        ),
    .axi_req_i    ( axi_read_req                     ),
    .axi_resp_o   ( axi_read_resp                    ),
    .mem_req_o    ( mem_req_o    [NumMemPorts/2-1:0] ),
    .mem_gnt_i    ( mem_gnt_i    [NumMemPorts/2-1:0] ),
    .mem_addr_o   ( mem_addr_o   [NumMemPorts/2-1:0] ),
    .mem_wdata_o  ( mem_wdata_o  [NumMemPorts/2-1:0] ),
    .mem_strb_o   ( mem_strb_o   [NumMemPorts/2-1:0] ),
    .mem_atop_o   ( mem_atop_o   [NumMemPorts/2-1:0] ),
    .mem_we_o     ( mem_we_o     [NumMemPorts/2-1:0] ),
    .mem_rvalid_i ( mem_rvalid_i [NumMemPorts/2-1:0] ),
    .mem_rdata_i  ( mem_rdata_i  [NumMemPorts/2-1:0] )
  );

  axi_to_mem #(
    .axi_req_t  ( axi_req_t     ),
    .axi_resp_t ( axi_resp_t    ),
    .AddrWidth  ( AddrWidth     ),
    .DataWidth  ( AxiDataWidth  ),
    .IdWidth    ( IdWidth       ),
    .NumBanks   ( NumMemPorts/2 ),
    .BufDepth   ( BufDepth      ),
    .HideStrb   ( HideStrb      )
  ) i_axi_to_mem_write (
    .clk_i,
    .rst_ni,
    .busy_o       ( write_busy                                 ),
    .axi_req_i    ( axi_write_req                              ),
    .axi_resp_o   ( axi_write_resp                             ),
    .mem_req_o    ( mem_req_o    [NumMemPorts-1:NumMemPorts/2] ),
    .mem_gnt_i    ( mem_gnt_i    [NumMemPorts-1:NumMemPorts/2] ),
    .mem_addr_o   ( mem_addr_o   [NumMemPorts-1:NumMemPorts/2] ),
    .mem_wdata_o  ( mem_wdata_o  [NumMemPorts-1:NumMemPorts/2] ),
    .mem_strb_o   ( mem_strb_o   [NumMemPorts-1:NumMemPorts/2] ),
    .mem_atop_o   ( mem_atop_o   [NumMemPorts-1:NumMemPorts/2] ),
    .mem_we_o     ( mem_we_o     [NumMemPorts-1:NumMemPorts/2] ),
    .mem_rvalid_i ( mem_rvalid_i [NumMemPorts-1:NumMemPorts/2] ),
    .mem_rdata_i  ( mem_rdata_i  [NumMemPorts-1:NumMemPorts/2] )
  );

endmodule

`include "axi/typedef.svh"
/// AXI4+ATOP interface wrapper for `axi_to_mem_split`
module axi_to_mem_split_intf #(
  /// AXI4+ATOP ID width
  parameter int unsigned AXI_ID_WIDTH   = 32'b0,
  /// AXI4+ATOP address width
  parameter int unsigned AXI_ADDR_WIDTH = 32'b0,
  /// AXI4+ATOP data width
  parameter int unsigned AXI_DATA_WIDTH = 32'b0,
  /// AXI4+ATOP user width
  parameter int unsigned AXI_USER_WIDTH = 32'b0,
  /// Memory data width, must evenly divide `DataWidth`.
  parameter int unsigned MEM_DATA_WIDTH = 32'b0,
  /// See `axi_to_mem`, parameter `BufDepth`.
  parameter int unsigned BUF_DEPTH      = 0,
  /// Hide write requests if the strb == '0
  parameter bit          HIDE_STRB      = 1'b0,
  /// Dependent parameters, do not override. Number of memory ports.
  parameter int unsigned NUM_MEM_PORTS  = 2*AXI_DATA_WIDTH/MEM_DATA_WIDTH,
  /// Dependent parameter, do not override. See `axi_to_mem`, parameter `addr_t`.
  parameter type addr_t     = logic [AXI_ADDR_WIDTH-1:0],
  /// Dependent parameter, do not override. See `axi_to_mem`, parameter `mem_data_t`.
  parameter type mem_data_t = logic [MEM_DATA_WIDTH-1:0],
  /// Dependent parameter, do not override. See `axi_to_mem`, parameter `mem_strb_t`.
  parameter type mem_strb_t = logic [MEM_DATA_WIDTH/8-1:0]
) (
  /// Clock input.
  input  logic                               clk_i,
  /// Asynchronous reset, active low.
  input  logic                               rst_ni,
  /// See `axi_to_mem_split`, port `busy_o`.
  output logic                               busy_o,
  /// AXI4+ATOP slave interface port.
  AXI_BUS.Slave                              axi_bus,
  /// See `axi_to_mem_split`, port `mem_req_o`.
  output logic           [NUM_MEM_PORTS-1:0] mem_req_o,
  /// See `axi_to_mem_split`, port `mem_gnt_i`.
  input  logic           [NUM_MEM_PORTS-1:0] mem_gnt_i,
  /// See `axi_to_mem_split`, port `mem_addr_o`.
  output addr_t          [NUM_MEM_PORTS-1:0] mem_addr_o,
  /// See `axi_to_mem_split`, port `mem_wdata_o`.
  output mem_data_t      [NUM_MEM_PORTS-1:0] mem_wdata_o,
  /// See `axi_to_mem_split`, port `mem_strb_o`.
  output mem_strb_t      [NUM_MEM_PORTS-1:0] mem_strb_o,
  /// See `axi_to_mem_split`, port `mem_atop_o`.
  output axi_pkg::atop_t [NUM_MEM_PORTS-1:0] mem_atop_o,
  /// See `axi_to_mem_split`, port `mem_we_o`.
  output logic           [NUM_MEM_PORTS-1:0] mem_we_o,
  /// See `axi_to_mem_split`, port `mem_rvalid_i`.
  input  logic           [NUM_MEM_PORTS-1:0] mem_rvalid_i,
  /// See `axi_to_mem_split`, port `mem_rdata_i`.
  input  mem_data_t      [NUM_MEM_PORTS-1:0] mem_rdata_i
);

  typedef logic [AXI_ID_WIDTH-1:0] id_t;
  typedef logic [AXI_DATA_WIDTH-1:0] data_t;
  typedef logic [AXI_DATA_WIDTH/8-1:0] strb_t;
  typedef logic [AXI_USER_WIDTH-1:0] user_t;
  `AXI_TYPEDEF_ALL(axi, addr_t, id_t, data_t, strb_t, user_t)

  axi_req_t axi_req;
  axi_resp_t axi_resp;
  `AXI_ASSIGN_TO_REQ(axi_req, axi_bus)
  `AXI_ASSIGN_FROM_RESP(axi_bus, axi_resp)

  axi_to_mem_split #(
    .axi_req_t    ( axi_req_t      ),
    .axi_resp_t   ( axi_resp_t     ),
    .AxiDataWidth ( AXI_DATA_WIDTH ),
    .AddrWidth    ( AXI_ADDR_WIDTH ),
    .IdWidth      ( AXI_ID_WIDTH   ),
    .MemDataWidth ( MEM_DATA_WIDTH ), // must divide `AxiDataWidth` without remainder
    .BufDepth     ( BUF_DEPTH      ),
    .HideStrb     ( HIDE_STRB      )
  ) i_axi_to_mem_split (
    .clk_i,
    .rst_ni,
    .busy_o,
    .axi_req_i (axi_req),
    .axi_resp_o (axi_resp),
    .mem_req_o,
    .mem_gnt_i,
    .mem_addr_o,
    .mem_wdata_o,
    .mem_strb_o,
    .mem_atop_o,
    .mem_we_o,
    .mem_rvalid_i,
    .mem_rdata_i
  );

endmodule
