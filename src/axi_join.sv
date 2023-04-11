// Copyright (c) 2014-2018 ETH Zurich, University of Bologna
//
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
// - Fabian Schuiki <fschuiki@iis.ee.ethz.ch>
// - Andreas Kurth <akurth@iis.ee.ethz.ch>

`include "axi/assign.svh"

/// A connector that joins two AXI interfaces.
module axi_join_intf (
  AXI_BUS.Subordinate  in,
  AXI_BUS.Manager out
);

  `AXI_ASSIGN(out, in)

// pragma translate_off
`ifndef VERILATOR
  initial begin
    assert(in.AXI_ADDR_WIDTH == out.AXI_ADDR_WIDTH);
    assert(in.AXI_DATA_WIDTH == out.AXI_DATA_WIDTH);
    assert(in.AXI_ID_WIDTH   <= out.AXI_ID_WIDTH  );
    assert(in.AXI_USER_WIDTH == out.AXI_USER_WIDTH);
  end
`endif
// pragma translate_on

endmodule
