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

`include "axi/assign.svh"
`include "axi/typedef.svh"

/// Testbench for [`axi_tlb`](module.axi_tlb)
module tb_axi_tlb #(
  // DUT Parameters
  parameter int unsigned AxiSlvPortAddrWidth = 32,
  parameter int unsigned AxiMstPortAddrWidth = 64,
  parameter int unsigned AxiDataWidth = 32,
  parameter int unsigned AxiIdWidth = 4,
  parameter int unsigned AxiUserWidth = 4,
  parameter int unsigned AxiSlvPortMaxTxns = 4,
  parameter int unsigned CfgAxiAddrWidth = 32,
  parameter int unsigned CfgAxiDataWidth = 32,
  parameter int unsigned L1NumEntries = 4,
  parameter bit L1CutAx = 1'b1,
  // TB Parameters
  parameter int unsigned NumReads = 1000,
  parameter int unsigned NumWrites = 1000,
  parameter time CyclTime = 10ns,
  parameter time ApplTime = 2ns,
  parameter time TestTime = 8ns
);

  // Clock and reset
  logic clk,  rst_n;
  clk_rst_gen #(
    .CLK_PERIOD     ( CyclTime  ),
    .RST_CLK_CYCLES ( 5         )
  ) i_clk_rst_gen (
    .clk_o  ( clk   ),
    .rst_no ( rst_n )
  );

  // Interfaces
  AXI_BUS_DV #(
    .AXI_ADDR_WIDTH ( AxiSlvPortAddrWidth ),
    .AXI_DATA_WIDTH ( AxiDataWidth        ),
    .AXI_ID_WIDTH   ( AxiIdWidth          ),
    .AXI_USER_WIDTH ( AxiUserWidth        )
  ) upstream_dv (clk);
  AXI_BUS #(
    .AXI_ADDR_WIDTH ( AxiSlvPortAddrWidth ),
    .AXI_DATA_WIDTH ( AxiDataWidth        ),
    .AXI_ID_WIDTH   ( AxiIdWidth          ),
    .AXI_USER_WIDTH ( AxiUserWidth        )
  ) upstream ();
  `AXI_ASSIGN(upstream, upstream_dv)
  AXI_BUS #(
    .AXI_ADDR_WIDTH ( AxiMstPortAddrWidth ),
    .AXI_DATA_WIDTH ( AxiDataWidth        ),
    .AXI_ID_WIDTH   ( AxiIdWidth          ),
    .AXI_USER_WIDTH ( AxiUserWidth        )
  ) downstream ();
  AXI_BUS_DV #(
    .AXI_ADDR_WIDTH ( AxiMstPortAddrWidth ),
    .AXI_DATA_WIDTH ( AxiDataWidth        ),
    .AXI_ID_WIDTH   ( AxiIdWidth          ),
    .AXI_USER_WIDTH ( AxiUserWidth        )
  ) downstream_dv (clk);
  `AXI_ASSIGN(downstream_dv, downstream)
  AXI_LITE_DV #(
    .AXI_ADDR_WIDTH ( CfgAxiAddrWidth ),
    .AXI_DATA_WIDTH ( CfgAxiDataWidth )
  ) cfg_dv (clk);
  AXI_LITE #(
    .AXI_ADDR_WIDTH ( CfgAxiAddrWidth ),
    .AXI_DATA_WIDTH ( CfgAxiDataWidth )
  ) cfg ();
  `AXI_LITE_ASSIGN(cfg, cfg_dv)

  // DUT
  axi_tlb_intf #(
    .AXI_SLV_PORT_ADDR_WIDTH  ( AxiSlvPortAddrWidth ),
    .AXI_MST_PORT_ADDR_WIDTH  ( AxiMstPortAddrWidth ),
    .AXI_DATA_WIDTH           ( AxiDataWidth        ),
    .AXI_ID_WIDTH             ( AxiIdWidth          ),
    .AXI_USER_WIDTH           ( AxiUserWidth        ),
    .AXI_SLV_PORT_MAX_TXNS    ( AxiSlvPortMaxTxns   ),
    .CFG_AXI_ADDR_WIDTH       ( CfgAxiAddrWidth     ),
    .CFG_AXI_DATA_WIDTH       ( CfgAxiDataWidth     ),
    .L1_NUM_ENTRIES           ( L1NumEntries        ),
    .L1_CUT_AX                ( L1CutAx             )
  ) i_dut (
    .clk_i      ( clk         ),
    .rst_ni     ( rst_n       ),
    .test_en_i  ( 1'b0        ),
    .slv        ( upstream    ),
    .mst        ( downstream  ),
    .cfg        ( cfg         )
  );

  // Configuration port driver
  axi_test::axi_lite_driver #(
    .AW ( CfgAxiAddrWidth ),
    .DW ( CfgAxiDataWidth ),
    .TA ( ApplTime        ),
    .TT ( TestTime        )
  ) cfg_driver = new(cfg_dv);
  typedef logic [CfgAxiAddrWidth-1:0] cfg_addr_t;
  typedef logic [CfgAxiDataWidth-1:0] cfg_data_t;
  task automatic write_cfg(cfg_addr_t addr, cfg_data_t data);
    axi_pkg::resp_t resp;
    fork
      cfg_driver.send_aw(addr, '0);
      cfg_driver.send_w(data, 4'b1111);
    join
    cfg_driver.recv_b(resp);
    assert(resp == axi_pkg::RESP_OKAY);
  endtask
  typedef logic [31:0] pfn_t;
  localparam pfn_t first_pfn = 32'h1;      // first PFN (page frame number) of input range
  localparam pfn_t last_pfn = 32'h7_FFFF;  // last PFN of input range
  localparam pfn_t base_pfn = 32'h1_0000;  // map to output range starting with this address
  initial begin
    cfg_driver.reset_master();
    wait (rst_n);
    write_cfg(32'h0000_0000, first_pfn);
    write_cfg(32'h0000_0004, last_pfn);
    write_cfg(32'h0000_0008, base_pfn);
    // make valid and read-writable
    if (AxiMstPortAddrWidth <= 32) begin
      write_cfg(32'h0000_000C, 32'h0000_0001);
    end else begin
      write_cfg(32'h0000_0010, 32'h0000_0001);
    end
  end

  // Capture transactions into upstream and downstream queues.
  localparam AxiStrbWidth = AxiDataWidth / 8;
  typedef logic [AxiSlvPortAddrWidth-1:0] slv_addr_t;
  typedef logic [AxiMstPortAddrWidth-1:0] mst_addr_t;
  typedef logic [AxiDataWidth-1:0]        data_t;
  typedef logic [AxiIdWidth-1:0]          id_t;
  typedef logic [AxiStrbWidth-1:0]        strb_t;
  typedef logic [AxiUserWidth-1:0]        user_t;
  `AXI_TYPEDEF_AW_CHAN_T(slv_aw_t, slv_addr_t, id_t, user_t)
  `AXI_TYPEDEF_AW_CHAN_T(mst_aw_t, mst_addr_t, id_t, user_t)
  `AXI_TYPEDEF_W_CHAN_T(w_t, data_t, strb_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T(b_t, id_t, user_t)
  `AXI_TYPEDEF_AR_CHAN_T(slv_ar_t, slv_addr_t, id_t, user_t)
  `AXI_TYPEDEF_AR_CHAN_T(mst_ar_t, mst_addr_t, id_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(r_t, data_t, id_t, user_t)
  localparam int unsigned AxiNumIds = 2**AxiIdWidth;
  mst_aw_t  downstream_aw,
            downstream_exp_aw_queue[$];
  w_t       upstream_w,
            downstream_w,
            downstream_exp_w_queue[$];
  b_t       upstream_b,
            downstream_b_queue[AxiNumIds-1:0][$],
            downstream_b;
  mst_ar_t  downstream_ar,
            downstream_exp_ar_queue[$];
  r_t       upstream_r,
            downstream_r_queue[AxiNumIds-1:0][$],
            downstream_r;
  `AXI_ASSIGN_TO_W(upstream_w, upstream)
  `AXI_ASSIGN_TO_B(upstream_b, upstream)
  `AXI_ASSIGN_TO_R(upstream_r, upstream)
  `AXI_ASSIGN_TO_AW(downstream_aw, downstream)
  `AXI_ASSIGN_TO_W(downstream_w, downstream)
  `AXI_ASSIGN_TO_B(downstream_b, downstream)
  `AXI_ASSIGN_TO_AR(downstream_ar, downstream)
  `AXI_ASSIGN_TO_R(downstream_r, downstream)
  function bit addr_in_pfn_range(slv_addr_t addr, pfn_t first_pfn, pfn_t last_pfn);
    automatic pfn_t pfn = addr >> 12;
    return (pfn >= first_pfn) && (pfn <= last_pfn);
  endfunction
  function bit addr_is_mapped(slv_addr_t addr);
    return addr_in_pfn_range(addr, first_pfn, last_pfn);
  endfunction
  function mst_addr_t addr_maps_to(slv_addr_t addr);
    automatic pfn_t maps_to_pfn = (addr >> 12) + base_pfn - first_pfn;
    return (maps_to_pfn << 12) | (addr & 12'hFFF);
  endfunction

  typedef struct {
    bit goes_through;
    id_t id;
    axi_pkg::len_t len;
  } dcsn_t;
  dcsn_t w_dcsn_queue[$], b_dcsn_queue[AxiNumIds-1:0][$], r_dcsn_queue[AxiNumIds-1:0][$];

  initial begin
    wait (rst_n);
    forever begin
      @(posedge clk);
      #TestTime;
      // AW
      if (upstream.aw_valid && upstream.aw_ready) begin
        automatic dcsn_t w_dcsn;
        w_dcsn.id = upstream.aw_id;
        if (addr_is_mapped(upstream.aw_addr)) begin
          automatic mst_aw_t exp_aw;
          `AXI_SET_TO_AW(exp_aw, upstream)
          exp_aw.addr = addr_maps_to(upstream.aw_addr);
          downstream_exp_aw_queue.push_back(exp_aw);
          w_dcsn.goes_through = 1'b1;
        end else begin
          w_dcsn.goes_through = 1'b0;
        end
        w_dcsn.len = upstream.aw_len;
        w_dcsn_queue.push_back(w_dcsn);
      end
      if (downstream.aw_valid && downstream.aw_ready) begin
        automatic mst_aw_t exp_aw;
        assert (downstream_exp_aw_queue.size() != 0)
          else $fatal(1, "Unexpected AW at master port!");
        exp_aw = downstream_exp_aw_queue.pop_front();
        assert (downstream_aw == exp_aw)
          else $error("AW at master port does not match: %p != %p!", downstream_aw, exp_aw);
      end
      // W
      if (upstream.w_valid && upstream.w_ready) begin
        automatic dcsn_t w_dcsn;
        assert (w_dcsn_queue.size() != 0)
          else $fatal(1, "W beat that TB cannot handle at slave port!");
        w_dcsn = w_dcsn_queue[0];
        if (w_dcsn.goes_through) begin
          downstream_exp_w_queue.push_back(upstream_w);
        end
        if (upstream_w.last) begin
          b_dcsn_queue[w_dcsn.id].push_back(w_dcsn);
          void'(w_dcsn_queue.pop_front());
        end
      end
      if (downstream.w_valid && downstream.w_ready) begin
        automatic w_t exp_w;
        assert (downstream_exp_w_queue.size() != 0)
          else $fatal(1, "Unexpected W at master port!");
        exp_w = downstream_exp_w_queue.pop_front();
        assert (downstream_w == exp_w)
          else $error("W at master port does not match: %p != %p!", downstream_w, exp_w);
      end
      // B
      if (downstream.b_valid && downstream.b_ready) begin
        downstream_b_queue[downstream.b_id].push_back(downstream_b);
      end
      if (upstream.b_valid && upstream.b_ready) begin
        automatic b_t exp_b;
        automatic dcsn_t b_dcsn;
        assert (b_dcsn_queue[upstream.b_id].size() != 0)
          else $fatal(1, "Unexpected B with ID %0d at slave port!", upstream.b_id);
        b_dcsn = b_dcsn_queue[upstream.b_id].pop_front();
        if (b_dcsn.goes_through) begin
          assert (downstream_b_queue[upstream.b_id].size() != 0)
            else $fatal(1, "Unexpected B with ID %0d at slave port!", upstream.b_id);
          exp_b = downstream_b_queue[upstream.b_id].pop_front();
        end else begin
          exp_b = '{
            id: b_dcsn.id,
            resp: axi_pkg::RESP_SLVERR,
            user: 'x
          };
        end
        assert (upstream_b ==? exp_b)
          else $error("B at slave port does not match: %p != %p!", upstream_b, exp_b);
      end
      // AR
      if (upstream.ar_valid && upstream.ar_ready) begin
        automatic dcsn_t r_dcsn;
        r_dcsn.id = upstream.ar_id;
        if (addr_is_mapped(upstream.ar_addr)) begin
          automatic mst_ar_t exp_ar;
          `AXI_SET_TO_AR(exp_ar, upstream)
          exp_ar.addr = addr_maps_to(upstream.ar_addr);
          downstream_exp_ar_queue.push_back(exp_ar);
          r_dcsn.goes_through = 1'b1;
        end else begin
          r_dcsn.goes_through = 1'b0;
        end
        r_dcsn.len = upstream.ar_len;
        r_dcsn_queue[r_dcsn.id].push_back(r_dcsn);
      end
      if (downstream.ar_valid && downstream.ar_ready) begin
        automatic mst_ar_t exp_ar;
        assert (downstream_exp_ar_queue.size() != 0)
          else $fatal(1, "Unexpected AR at master port!");
        exp_ar = downstream_exp_ar_queue.pop_front();
        assert (downstream_ar == exp_ar)
          else $error("AR at master port does not match: %p != %p!", downstream_ar, exp_ar);
      end
      // R
      if (downstream.r_valid && downstream.r_ready) begin
        downstream_r_queue[downstream.r_id].push_back(downstream_r);
      end
      if (upstream.r_valid && upstream.r_ready) begin
        automatic r_t exp_r;
        automatic dcsn_t r_dcsn;
        assert (r_dcsn_queue[upstream.r_id].size() != 0)
          else $fatal(1, "Unexpected R with ID %0d at slave port!", upstream.r_id);
        r_dcsn = r_dcsn_queue[upstream.r_id][0];
        if (r_dcsn.goes_through) begin
          assert (downstream_r_queue[upstream.r_id].size() != 0)
            else $fatal(1, "Unexpected R with ID %0d at slave port!", upstream.r_id);
          exp_r = downstream_r_queue[upstream.r_id].pop_front();
        end else begin
          exp_r = '{
            data: 'x,
            id: r_dcsn.id,
            last: (r_dcsn.len == '0),
            resp: axi_pkg::RESP_SLVERR,
            user: 'x
          };
        end
        assert (upstream_r ==? exp_r)
          else $error("R at slave port does not match: %p != %p!", upstream_r, exp_r);
        if (r_dcsn.len == '0) begin
          assert (exp_r.last) else $error("Expected last R beat!");
          void'(r_dcsn_queue[exp_r.id].pop_front());
        end else begin
          r_dcsn_queue[exp_r.id][0].len -= 1;
        end
      end
    end
  end

  // Upstream driver
  logic end_of_sim;
  axi_test::axi_rand_master #(
    .AW               ( AxiSlvPortAddrWidth ),
    .DW               ( AxiDataWidth        ),
    .IW               ( AxiIdWidth          ),
    .UW               ( AxiUserWidth        ),
    .TA               ( ApplTime            ),
    .TT               ( TestTime            ),
    .MAX_READ_TXNS    ( 20                  ),
    .MAX_WRITE_TXNS   ( 20                  ),
    .AXI_EXCLS        ( 1'b1                ),
    .AXI_ATOPS        ( 1'b1                ),
    .AXI_BURST_FIXED  ( 1'b1                ),
    .AXI_BURST_INCR   ( 1'b1                ),
    .AXI_BURST_WRAP   ( 1'b1                )
  ) upstream_driver = new(upstream_dv);
  initial begin
    end_of_sim = 1'b0;
    // TODO: add two memory regions: one that is mapped in the TLB and one that is not
    //upstream_driver.add_memory_region(32'h0000_0000, 32'h1000_0000, axi_pkg::DEVICE_NONBUFFERABLE);
    //upstream_driver.add_memory_region(/* ... */);
    upstream_driver.reset();
    wait (rst_n);
    upstream_driver.run(NumReads, NumWrites);
    end_of_sim = 1'b1;
  end

  // Downstream driver
  axi_test::axi_rand_slave #(
    .AW ( AxiMstPortAddrWidth ),
    .DW ( AxiDataWidth        ),
    .IW ( AxiIdWidth          ),
    .UW ( AxiUserWidth        ),
    .TA ( ApplTime            ),
    .TT ( TestTime            )
  ) downstream_driver = new(downstream_dv);
  initial begin
    downstream_driver.reset();
    wait (rst_n);
    downstream_driver.run();
  end

endmodule
