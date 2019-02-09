// Copyright 2019 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// File          : axi_data_width_converter.sv
// Author        : Matheus Cavalcante <matheusd@iis.ee.ethz.ch>
// Created       : 31.01.2019
//
// Copyright (C) 2019 ETH Zurich, University of Bologna
// All rights reserved.

import axi_pkg::*;

module axi_data_width_converter #(
  parameter int unsigned MASTER_DATA_WIDTH = 64,
  parameter int unsigned SLAVE_DATA_WIDTH  = 64
) (
  AXI_BUS.in  in,
  AXI_BUS.out out
);

`ifndef SYNTHESIS
  initial begin
    assert(in.AXI_ADDR_WIDTH == out.AXI_ADDR_WIDTH);
    assert(in.AXI_ID_WIDTH   <= out.AXI_ID_WIDTH  );
    assert(in.AXI_USER_WIDTH == out.AXI_USER_WIDTH);
  end
`endif

  generate
    if (MASTER_DATA_WIDTH == SLAVE_DATA_WIDTH) begin: NO_WIDTH_CONVERSION
      axi_join i_axi_join (
        .in,
        .out
      );
    end

    if (MASTER_DATA_WIDTH < SLAVE_DATA_WIDTH) begin: UPSCALE
      axi_upscale i_axi_upscale #(
        .MASTER_DATA_WIDTH,
        .SLAVE_DATA_WIDTH
      ) (
        .in,
        .out
      );
    end

    if (MASTER_DATA_WIDTH > SLAVE_DATA_WIDTH) begin: DOWNSCALE
      axi_downscale i_axi_downscale #(
        .MASTER_DATA_WIDTH,
        .SLAVE_DATA_WIDTH
      ) (
        .in,
        .out
      );
    end
  endgenerate

endmodule // axi_data_width_converter
