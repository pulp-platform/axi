// Copyright 2018-2020 ETH Zurich and University of Bologna.
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
// - Andreas Kurth <akurth@iis.ee.ethz.ch>
// - Wolfgang Roenninger <wroennin@iis.ee.ethz.ch>

`include "axi/assign.svh"
`include "axi/typedef.svh"

class tb_iw_converter_ax #(
  type ax_t = logic,
  type id_t = logic
);

  ax_t upstream_ax;
  id_t downstream_id;

  function new(ax_t upstream_ax);
    this.upstream_ax   = upstream_ax;
    this.downstream_id = 'x;
  endfunction

  // Compare all fields of two AXs except their IDs.
  function bit equals_except_id(ax_t other_ax);
    // Override ID field of other AX, then use the field-by-field equality operator.
    other_ax.id = this.upstream_ax.id;
    return this.upstream_ax == other_ax;
  endfunction

endclass

module tb_axi_iw_converter #(
  // DUT Parameters
  parameter int unsigned TbAxiSlvPortIdWidth      = 32'd0,
  parameter int unsigned TbAxiMstPortIdWidth      = 32'd0,
  parameter int unsigned TbAxiSlvPortMaxUniqIds   = 32'd0,
  parameter int unsigned TbAxiSlvPortMaxTxnsPerId = 32'd0,
  parameter int unsigned TbAxiSlvPortMaxTxns      = 32'd0,
  parameter int unsigned TbAxiMstPortMaxUniqIds   = 32'd0,
  parameter int unsigned TbAxiMstPortMaxTxnsPerId = 32'd0,
  parameter int unsigned TbAxiAddrWidth           = 32'd32,
  parameter int unsigned TbAxiDataWidth           = 32'd32,
  parameter int unsigned TbAxiUserWidth           = 32'd4,
  // TB Parameters
  parameter int unsigned TbNumReadTxns            = 32'd100,
  parameter int unsigned TbNumWriteTxns           = 32'd200,
  parameter bit          TbEnAtop                 = 1'b1,
  parameter bit          TbEnExcl                 = 1'b0
);
  // AXI4+ATOP channel parameter

  // TB timing parameter
  localparam time CyclTime = 10ns;
  localparam time ApplTime = 2ns;
  localparam time TestTime = 8ns;

  // Driver definitions
  typedef axi_test::axi_rand_master#(
    // AXI interface parameters
    .AW            (TbAxiAddrWidth),
    .DW            (TbAxiDataWidth),
    .IW            (TbAxiSlvPortIdWidth),
    .UW            (TbAxiUserWidth),
    // Stimuli application and test time
    .TA            (ApplTime),
    .TT            (TestTime),
    // Maximum number of read and write transactions in flight
    .MAX_READ_TXNS (20),
    .MAX_WRITE_TXNS(20),
    .AXI_EXCLS     (TbEnExcl),
    .AXI_ATOPS     (TbEnAtop)
  ) rand_axi_master_t;
  typedef axi_test::axi_rand_slave#(
    // AXI interface parameters
    .AW(TbAxiAddrWidth),
    .DW(TbAxiDataWidth),
    .IW(TbAxiMstPortIdWidth),
    .UW(TbAxiUserWidth),
    // Stimuli application and test time
    .TA(ApplTime),
    .TT(TestTime)
  ) rand_axi_slave_t;

  // TB signals
  logic clk, rst_n, sim_done;

  //-----------------------------------
  // Clock generator
  //-----------------------------------
  clk_rst_gen #(
    .ClkPeriod   (CyclTime),
    .RstClkCycles(5)
  ) i_clk_gen (
    .clk_o (clk),
    .rst_no(rst_n)
  );

  AXI_BUS_DV #(
    .AXI_ADDR_WIDTH(TbAxiAddrWidth),
    .AXI_DATA_WIDTH(TbAxiDataWidth),
    .AXI_ID_WIDTH  (TbAxiSlvPortIdWidth),
    .AXI_USER_WIDTH(TbAxiUserWidth)
  ) axi_upstream_dv (
    clk
  );

  AXI_BUS #(
    .AXI_ADDR_WIDTH(TbAxiAddrWidth),
    .AXI_DATA_WIDTH(TbAxiDataWidth),
    .AXI_ID_WIDTH  (TbAxiSlvPortIdWidth),
    .AXI_USER_WIDTH(TbAxiUserWidth)
  ) axi_upstream ();

  `AXI_ASSIGN(axi_upstream, axi_upstream_dv);

  AXI_BUS_DV #(
    .AXI_ADDR_WIDTH(TbAxiAddrWidth),
    .AXI_DATA_WIDTH(TbAxiDataWidth),
    .AXI_ID_WIDTH  (TbAxiMstPortIdWidth),
    .AXI_USER_WIDTH(TbAxiUserWidth)
  ) axi_downstream_dv (
    clk
  );

  AXI_BUS #(
    .AXI_ADDR_WIDTH(TbAxiAddrWidth),
    .AXI_DATA_WIDTH(TbAxiDataWidth),
    .AXI_ID_WIDTH  (TbAxiMstPortIdWidth),
    .AXI_USER_WIDTH(TbAxiUserWidth)
  ) axi_downstream ();

  `AXI_ASSIGN(axi_downstream_dv, axi_downstream);

  initial begin : proc_rand_master
    automatic rand_axi_master_t axi_master = new(axi_upstream_dv);
    sim_done = 1'b0;
    @(posedge rst_n);
    axi_master.reset();
    axi_master.add_memory_region('0, '1, axi_pkg::DEVICE_NONBUFFERABLE);
    repeat (5) @(posedge clk);
    axi_master.run(TbNumReadTxns, TbNumWriteTxns);

    sim_done = 1'b1;
  end

  initial begin : proc_rand_slave
    automatic rand_axi_slave_t axi_slave = new(axi_downstream_dv);
    @(posedge rst_n);
    axi_slave.reset();
    axi_slave.run();
  end

  initial begin : proc_sim_stop
    @(posedge rst_n);
    wait (|sim_done);
    repeat (10) @(posedge clk);
    $finish();
  end

  axi_iw_converter_intf #(
    .AXI_SLV_PORT_ID_WIDTH       (TbAxiSlvPortIdWidth),
    .AXI_MST_PORT_ID_WIDTH       (TbAxiMstPortIdWidth),
    .AXI_SLV_PORT_MAX_UNIQ_IDS   (TbAxiSlvPortMaxUniqIds),
    .AXI_SLV_PORT_MAX_TXNS_PER_ID(TbAxiSlvPortMaxTxnsPerId),
    .AXI_SLV_PORT_MAX_TXNS       (TbAxiSlvPortMaxTxns),
    .AXI_MST_PORT_MAX_UNIQ_IDS   (TbAxiMstPortMaxUniqIds),
    .AXI_MST_PORT_MAX_TXNS_PER_ID(TbAxiMstPortMaxTxnsPerId),
    .AXI_ADDR_WIDTH              (TbAxiAddrWidth),
    .AXI_DATA_WIDTH              (TbAxiDataWidth),
    .AXI_USER_WIDTH              (TbAxiUserWidth)
  ) i_dut (
    .clk_i (clk),
    .rst_ni(rst_n),
    .slv   (axi_upstream),
    .mst   (axi_downstream)
  );

  typedef rand_axi_master_t::addr_t addr_t;
  typedef rand_axi_master_t::data_t data_t;
  typedef rand_axi_master_t::id_t id_t;
  typedef logic [rand_axi_master_t::DW/8-1:0] strb_t;
  typedef rand_axi_master_t::user_t user_t;
  `AXI_TYPEDEF_AW_CHAN_T(aw_beat_t, addr_t, id_t, user_t)
  `AXI_TYPEDEF_W_CHAN_T(w_beat_t, data_t, strb_t, user_t)
  `AXI_TYPEDEF_AR_CHAN_T(ar_beat_t, addr_t, id_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(r_beat_t, data_t, id_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T(b_beat_t, id_t, user_t)
  typedef tb_iw_converter_ax#(
    .ax_t(aw_beat_t),
    .id_t(id_t)
  ) aw_t;
  typedef tb_iw_converter_ax#(
    .ax_t(ar_beat_t),
    .id_t(id_t)
  ) ar_t;
  aw_t aws_by_addr[addr_t], aws_by_downstream_id[id_t][$], aws_by_upstream_id[id_t][$];
  w_beat_t ws[$];
  ar_t ars_by_addr[addr_t], ars_by_downstream_id[id_t][$], ars_by_upstream_id[id_t][$];
  r_beat_t rs_by_upstream_id[id_t][$];
  b_beat_t bs_by_upstream_id[id_t][$];

  initial begin
    @(posedge rst_n);
    while (1) begin
      @(posedge clk);
      #(TestTime);
      // Monitor upstream ARs ----------------------------------------------------------------------
      if (axi_upstream.ar_valid && axi_upstream.ar_ready) begin
        automatic ar_t ar;
        automatic ar_beat_t ar_beat;
        // Sameple upstream AR.
        `AXI_SET_TO_AR(ar_beat, axi_upstream)
        ar = new(ar_beat);
        if (ars_by_addr.exists(ar_beat.addr)) begin
          $fatal(1, "Two concurrent ARs to the same address not supported by TB!");
        end
        // Insert AR into by-address and by-upstream-ID data structures.
        ars_by_addr[ar_beat.addr] = ar;
        ars_by_upstream_id[ar_beat.id].push_back(ar);
      end
      // Monitor downstream ARs --------------------------------------------------------------------
      if (axi_downstream.ar_valid && axi_downstream.ar_ready) begin
        automatic ar_t ar;
        automatic ar_beat_t ar_beat;
        automatic id_t other_downstream_id;
        // Sample downstream AR.
        `AXI_SET_TO_AR(ar_beat, axi_downstream)
        // Obtain tracked AR.
        ar = ars_by_addr[ar_beat.addr];
        if (ar == null) begin
          $fatal(1, "Unknown AR with address 0x%016x!", axi_downstream.ar_addr);
        end
        // Update with downstream ID.
        ar.downstream_id = axi_downstream.ar_id;
        // Insert to ARs by downstream ID.
        ars_by_downstream_id[ar.downstream_id].push_back(ar);
        // Assert that downstream and upstream AR beat are equal; only their ID may be different.
        assert (ar.equals_except_id(ar_beat))
        else
          $error(
            "Downstream AR beat %p differs from upstream AR beat %p!", ar_beat, ar.upstream_ax
          );
        // Assert that all upstream beats with that ID have the same downstream ID.  It is
        // sufficient if we check that the downstream ID of this AR matches that of the first AR
        // with the same upstream ID.
        other_downstream_id = ars_by_upstream_id[ar.upstream_ax.id][0].downstream_id;
        assert (ar.downstream_id == other_downstream_id)
        else
          $error(
            "Illegal downstream ID 0x%0x for AR with upstream ID 0x%0x: ",
            ar.downstream_id,
            ar.upstream_ax.id,
            "another AR with the same upstream ID has downstream ID 0x%0x!",
            other_downstream_id
          );
      end
      // Monitor downstream Rs ---------------------------------------------------------------------
      if (axi_downstream.r_valid && axi_downstream.r_ready) begin
        automatic ar_t ar;
        automatic r_beat_t r_beat;
        // Sample downstream R.
        `AXI_SET_TO_R(r_beat, axi_downstream)
        //$info("Downstream R: %p", r_beat);
        // Obtain corresponding AR.
        if (!ars_by_downstream_id.exists(
            r_beat.id
          ) || ars_by_downstream_id[r_beat.id][0] == null) begin
          $fatal(1, "Unknown R with ID 0x%0x: %p", r_beat.id, r_beat);
        end
        ar = ars_by_downstream_id[r_beat.id][0];
        // Set upstream ID from AR.
        r_beat.id = ar.upstream_ax.id;
        // If this was the last R beat of a burst, delete all references to the corresponding AR.
        if (axi_downstream.r_last) begin
          ars_by_addr.delete(ar.upstream_ax.addr);
          void'(ars_by_downstream_id[axi_downstream.r_id].pop_front());
          void'(ars_by_upstream_id[ar.upstream_ax.id].pop_front());
        end
        // Insert R into upstream queue.
        rs_by_upstream_id[r_beat.id].push_back(r_beat);
      end
      // Monitor upstream Rs -----------------------------------------------------------------------
      if (axi_upstream.r_valid && axi_upstream.r_ready) begin
        automatic r_beat_t r_beat, exp_r_beat;
        // Sample upstream R.
        `AXI_SET_TO_R(r_beat, axi_upstream)
        // Compare for equality to front of queue.
        exp_r_beat = rs_by_upstream_id[r_beat.id].pop_front();
        assert (r_beat == exp_r_beat)
        else
          $error(
            "Incorrect upstream R beat with ID 0x%0x: %p != %p", r_beat.id, r_beat, exp_r_beat
          );
      end
      // Monitor upstream AWs ----------------------------------------------------------------------
      if (axi_upstream.aw_valid && axi_upstream.aw_ready) begin
        automatic aw_t aw;
        automatic aw_beat_t aw_beat;
        // Sample upstream AW.
        `AXI_SET_TO_AW(aw_beat, axi_upstream)
        aw = new(aw_beat);
        if (aws_by_addr.exists(aw_beat.addr)) begin
          $fatal(1, "Two concurrent AWs to the same address not supported by TB!");
        end
        // Insert AW into by-address and by-upstream-ID data structures.
        aws_by_addr[aw_beat.addr] = aw;
        aws_by_upstream_id[aw_beat.id].push_back(aw);
        // For ATOPs with a read response, additionally insert a phony AR to which the corresponding
        // R beat can be matched.
        if (aw_beat.atop[axi_pkg::ATOP_R_RESP]) begin
          automatic ar_t ar;
          automatic ar_beat_t ar_beat;
          `AXI_SET_AR_STRUCT(ar_beat, aw_beat)
          ar = new(ar_beat);
          if (ars_by_addr.exists(ar_beat.addr)) begin
            $fatal(1, "ATOP with read response to the same address as a concurrent AR ",
                   "is not supported by TB!");
          end
          ars_by_addr[ar_beat.addr] = ar;
          ars_by_upstream_id[ar_beat.id].push_back(ar);
        end
      end
      // Monitor downstream AWs --------------------------------------------------------------------
      if (axi_downstream.aw_valid && axi_downstream.aw_ready) begin
        automatic aw_t aw;
        automatic aw_beat_t aw_beat;
        automatic id_t other_downstream_id;
        // Sample downstream AW.
        `AXI_SET_TO_AW(aw_beat, axi_downstream)
        // Obtain tracked AW.
        aw = aws_by_addr[aw_beat.addr];
        if (aw == null) begin
          $fatal(1, "Unknown AW with address 0x%016x!", axi_downstream.aw_addr);
        end
        // Update with downstream ID.
        aw.downstream_id = axi_downstream.aw_id;
        // Insert to AWs by downstream ID.
        aws_by_downstream_id[aw.downstream_id].push_back(aw);
        // Assert that downstream and upstream AW beat are equal; only their ID may be different.
        assert (aw.equals_except_id(aw_beat))
        else
          $error(
            "Downstream AW beat %p differs from upstream AW beat %p!", aw_beat, aw.upstream_ax
          );
        // Assert that all upstream beats with that ID have the same downstream ID.  It is
        // sufficient if we check that the downstream ID of this AW matches that of the first AW
        // with the same upstream ID.
        other_downstream_id = aws_by_upstream_id[aw.upstream_ax.id][0].downstream_id;
        assert (aw.downstream_id == other_downstream_id)
        else
          $error(
            "Illegal downstream ID 0x%0x for AW with upstream ID 0x%0x: ",
            aw.downstream_id,
            aw.upstream_ax.id,
            "another AW with the same upstream ID has downstream ID 0x%0x!",
            other_downstream_id
          );
        // For ATOPs with a read response, additionally update the corresponding phony AR.
        if (aw_beat.atop[axi_pkg::ATOP_R_RESP]) begin
          automatic ar_t ar = ars_by_upstream_id[aw.upstream_ax.id][0];
          ar.downstream_id = aw.downstream_id;
          ars_by_downstream_id[aw.downstream_id].push_back(ar);
        end
      end
      // Monitor upstream Ws -----------------------------------------------------------------------
      if (axi_upstream.w_valid && axi_upstream.w_ready) begin
        automatic w_beat_t w_beat;
        // Sample upstream W.
        `AXI_SET_TO_W(w_beat, axi_upstream)
        // W beats are totally ordered and have no ID, so we push them to a single queue.
        ws.push_back(w_beat);
      end
      // Monitor downstream Ws ---------------------------------------------------------------------
      if (axi_downstream.w_valid && axi_downstream.w_ready) begin
        automatic w_beat_t w_beat, exp_w_beat;
        // Sample downstream W.
        `AXI_SET_TO_W(w_beat, axi_downstream)
        // Compare this W beat to the front entry in the queue.
        if (ws.size() == 0) $fatal(1, "Unknown W beat %p!", w_beat);
        exp_w_beat = ws.pop_front();
        assert (w_beat == exp_w_beat)
        else $error("Illegal downstream W beat: %p != %p", w_beat, exp_w_beat);
      end
      // Monitor downstream Bs ---------------------------------------------------------------------
      if (axi_upstream.b_valid && axi_upstream.b_ready) begin
        automatic aw_t aw;
        automatic b_beat_t b_beat;
        // Sample downstream B.
        `AXI_SET_TO_B(b_beat, axi_downstream)
        // Obtain corresponding AW.
        aw = aws_by_downstream_id[b_beat.id][0];
        if (aw == null) begin
          $fatal(1, "Unknown AW with ID 0x%0xd for B %p!", b_beat.id, b_beat);
        end
        // Replace ID by upstream ID and insert into upstream queue.
        b_beat.id = aw.upstream_ax.id;
        bs_by_upstream_id[b_beat.id].push_back(b_beat);
        // Since there is only one B beat per AW, delete all references to the AW.
        aws_by_addr.delete(aw.upstream_ax.addr);
        void'(aws_by_downstream_id[axi_downstream.b_id].pop_front());
        void'(aws_by_upstream_id[aw.upstream_ax.id].pop_front());
      end
      // Monitor upstream Bs -----------------------------------------------------------------------
      if (axi_upstream.b_valid && axi_upstream.b_ready) begin
        automatic b_beat_t b_beat, exp_b_beat;
        // Sample upstream B.
        `AXI_SET_TO_B(b_beat, axi_upstream)
        // Compare for equality to front of queue.
        exp_b_beat = bs_by_upstream_id[b_beat.id].pop_front();
        assert (b_beat == exp_b_beat)
        else
          $error(
            "Incorrect upstream B beat with ID 0x%0x: %p != %p", b_beat.id, b_beat, exp_b_beat
          );
      end
    end
  end

  initial begin
    @(posedge rst_n);
    // Wait for the end of simulation.
    wait (|sim_done);
    // Assert that all AWs sent by upstream were processed.
    foreach (aws_by_upstream_id[i]) begin
      assert (aws_by_upstream_id[i].size() == 0)
      else
        $error(
          "%0d AWs with upstream ID 0x%0x were not processed: %p",
          aws_by_upstream_id[i].size(),
          i,
          aws_by_upstream_id[i]
        );
    end
    // Assert that all Ws sent by upstream were processed.
    assert (ws.size() == 0)
    else $error("%0d Ws were not processed", ws.size());
    // Assert that all Bs were sent upstream.
    foreach (bs_by_upstream_id[i]) begin
      assert (bs_by_upstream_id[i].size() == 0)
      else
        $error(
          "%0d Bs with upstream ID 0x%0x were not processed: %p",
          bs_by_upstream_id[i].size(),
          i,
          bs_by_upstream_id[i]
        );
    end
    // Assert that all ARs sent by upstream were processed.
    foreach (ars_by_upstream_id[i]) begin
      assert (ars_by_upstream_id[i].size() == 0)
      else
        $error(
          "%0d ARs with upstream ID 0x%0x were not processed: %p",
          ars_by_upstream_id[i].size(),
          i,
          ars_by_upstream_id[i]
        );
    end
    // Assert that all Rs were sent upstream.
    foreach (rs_by_upstream_id[i]) begin
      assert (rs_by_upstream_id[i].size() == 0)
      else
        $error(
          "%0d Rs with upstream ID 0x%0x were not processed: %p",
          rs_by_upstream_id[i].size(),
          i,
          rs_by_upstream_id[i]
        );
    end
  end

endmodule
