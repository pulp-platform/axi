// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// APB Bus with Single Master and Multiple Slave Interfaces
// Each slave is accessible at exactly one address segment, and the address ranges of no two slaves
// may overlap. If the input address of this bus is not in any slave address segment, the bus
// responds with slverr; otherwise, this bus feeds all signals through to the slave. The slaves see
// offset-compensated addresses, e.g., if this bus gets ADDR_BEGIN[i] as input address, slave i will
// get address 0.
module apb_bus #(
  // Number of slaves.
  parameter int unsigned N_SLV  = 0,
  // Address ranges of the slaves. Slave i is mapped in the inclusive interval from ADDR_BEGIN[i] to
  // ADDR_END[i].
  parameter logic [N_SLV-1:0][31:0] ADDR_BEGIN  = '0,
  parameter logic [N_SLV-1:0][31:0] ADDR_END    = '0
) (
  // Input
  input  logic                    pclk_i,
  input  logic                    preset_ni,
  input  logic             [31:0] paddr_i,
  input  logic              [2:0] pprot_i,
  input  logic                    psel_i,
  input  logic                    penable_i,
  input  logic                    pwrite_i,
  input  logic             [31:0] pwdata_i,
  input  logic              [3:0] pstrb_i,
  output logic                    pready_o,
  output logic             [31:0] prdata_o,
  output logic                    pslverr_o,

  // Outputs
  output logic [N_SLV-1:0]        pclk_o,
  output logic [N_SLV-1:0]        preset_no,
  output logic [N_SLV-1:0][31:0]  paddr_o,
  output logic [N_SLV-1:0] [2:0]  pprot_o,
  output logic [N_SLV-1:0]        psel_o,
  output logic [N_SLV-1:0]        penable_o,
  output logic [N_SLV-1:0]        pwrite_o,
  output logic [N_SLV-1:0][31:0]  pwdata_o,
  output logic [N_SLV-1:0] [3:0]  pstrb_o,
  input  logic [N_SLV-1:0]        pready_i,
  input  logic [N_SLV-1:0][31:0]  prdata_i,
  input  logic [N_SLV-1:0]        pslverr_i
);

  logic [$clog2(N_SLV)-1:0] sel_idx;
  logic dec_err;

  for (genvar i = 0; i < N_SLV; i++) begin: gen_oup_demux
    assign pclk_o[i]    = pclk_i;
    assign preset_no[i] = preset_ni;
    assign paddr_o[i]   = paddr_i - ADDR_BEGIN[i];
    assign pprot_o[i]   = pprot_i;
    assign psel_o[i]    = psel_i & (paddr_i >= ADDR_BEGIN[i] && paddr_i <= ADDR_END[i]);
    assign penable_o[i] = penable_i;
    assign pwrite_o[i]  = pwrite_i;
    assign pwdata_o[i]  = pwdata_i;
    assign pstrb_o[i]   = pstrb_i;
  end

  assign dec_err = psel_i & ~(|psel_o);

  onehot_to_bin #(.ONEHOT_WIDTH(N_SLV)) i_sel_idx (
    .onehot (psel_o),
    .bin    (sel_idx)
  );

  always_comb begin
    if (psel_i) begin
      if (dec_err) begin
        pready_o  = 1'b1;
        prdata_o  = '0;
        pslverr_o = 1'b1;
      end else begin
        pready_o  = pready_i[sel_idx];
        prdata_o  = prdata_i[sel_idx];
        pslverr_o = pslverr_i[sel_idx];
      end
    end else begin // !psel_i
      pready_o  = 1'b0;
      prdata_o  = '0;
      pslverr_o = 1'b0;
    end
  end

// Validate parameters.
// pragma translate_off
`ifndef VERILATOR
  initial begin: p_assertions
    assert (N_SLV >= 1) else $fatal(1, "The number of slave ports must be at least 1!");
  end
  for (genvar i = 0; i < N_SLV; i++) begin: gen_assert_addr_outer
    initial begin
      assert (ADDR_BEGIN[i] <= ADDR_END[i])
        else $fatal(1, "Invalid address range for slave %0d", i);
    end
    for (genvar j = 0; j < N_SLV; j++) begin: gen_assert_addr_inner
      initial begin
        if (i != j) begin
          if (ADDR_BEGIN[j] >= ADDR_BEGIN[i]) begin
            assert (ADDR_BEGIN[j] > ADDR_END[i])
              else $fatal("Address range of slaves %0d and %0d overlap!", i, j);
          end else begin
            assert (ADDR_END[j] < ADDR_BEGIN[i])
              else $fatal("Address range of slaves %0d and %0d overlap!", i, j);
          end
        end
      end
    end
  end
`endif
// pragma translate_on

endmodule
