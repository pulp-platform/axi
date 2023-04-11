// Copyright (c) 2019 ETH Zurich and University of Bologna.
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
// - Florian Zaruba <zarubaf@iis.ee.ethz.ch>
// - Wolfgang Roenninger <wroennin@iis.ee.ethz.ch>

// `axi_xbar_monitor` implements an AXI bus monitor that is tuned for the AXI crossbar.
// It snoops on each of the subordinates and manager ports of the crossbar and
// populates FIFOs and ID queues to validate that no AXI beats get
// lost or sent to the wrong destination.

package tb_axi_xbar_pkg;
  class axi_xbar_monitor #(
    parameter int unsigned AddrWidth,
    parameter int unsigned DataWidth,
    parameter int unsigned IdWidthManagers,
    parameter int unsigned IdWidthSubordinates,
    parameter int unsigned UserWidth,
    parameter int unsigned NumManagers,
    parameter int unsigned NumSubordinates,
    parameter int unsigned NumAddrRules,
    parameter type         rule_t,
    parameter rule_t [NumAddrRules-1:0] AddrMap,
      // Stimuli application and test time
    parameter time  TimeTest
  );
    typedef logic [IdWidthManagers-1:0] mgr_axi_id_t;
    typedef logic [IdWidthSubordinates-1:0]  sbr_axi_id_t;
    typedef logic [AddrWidth-1:0]      axi_addr_t;

    typedef logic [$clog2(NumManagers)-1:0] idx_mgr_t;
    typedef int unsigned                  idx_sbr_t; // from rule_t

    typedef struct packed {
      mgr_axi_id_t mgr_axi_id;
      logic        last;
    } manager_exp_t;
    typedef struct packed {
      sbr_axi_id_t   sbr_axi_id;
      axi_addr_t     sbr_axi_addr;
      axi_pkg::len_t sbr_axi_len;
    } exp_ax_t;
    typedef struct packed {
      sbr_axi_id_t sbr_axi_id;
      logic        last;
    } subordinate_exp_t;

    typedef rand_id_queue_pkg::rand_id_queue #(
      .data_t   ( manager_exp_t   ),
      .ID_WIDTH ( IdWidthManagers )
    ) manager_exp_queue_t;
    typedef rand_id_queue_pkg::rand_id_queue #(
      .data_t   ( exp_ax_t      ),
      .ID_WIDTH ( IdWidthSubordinates )
    ) ax_queue_t;

    typedef rand_id_queue_pkg::rand_id_queue #(
      .data_t   ( subordinate_exp_t   ),
      .ID_WIDTH ( IdWidthSubordinates )
    ) subordinate_exp_queue_t;

    //-----------------------------------------
    // Monitoring virtual interfaces
    //-----------------------------------------
    virtual AXI_BUS_DV #(
      .AXI_ADDR_WIDTH ( AddrWidth      ),
      .AXI_DATA_WIDTH ( DataWidth      ),
      .AXI_ID_WIDTH   ( IdWidthManagers ),
      .AXI_USER_WIDTH ( UserWidth      )
    ) managers_axi [NumManagers-1:0];
    virtual AXI_BUS_DV #(
      .AXI_ADDR_WIDTH ( AddrWidth      ),
      .AXI_DATA_WIDTH ( DataWidth      ),
      .AXI_ID_WIDTH   ( IdWidthSubordinates  ),
      .AXI_USER_WIDTH ( UserWidth      )
    ) subordinates_axi [NumSubordinates-1:0];
    //-----------------------------------------
    // Queues and FIFOs to hold the expected ids
    //-----------------------------------------
    // Write transactions
    ax_queue_t         exp_aw_queue [NumSubordinates-1:0];
    subordinate_exp_t        exp_w_fifo   [NumSubordinates-1:0][$];
    subordinate_exp_t        act_w_fifo   [NumSubordinates-1:0][$];
    manager_exp_queue_t exp_b_queue  [NumManagers-1:0];

    // Read transactions
    ax_queue_t            exp_ar_queue  [NumSubordinates-1:0];
    manager_exp_queue_t    exp_r_queue  [NumManagers-1:0];

    //-----------------------------------------
    // Bookkeeping
    //-----------------------------------------
    longint unsigned tests_expected;
    longint unsigned tests_conducted;
    longint unsigned tests_failed;
    semaphore        cnt_sem;

    //-----------------------------------------
    // Constructor
    //-----------------------------------------
    function new(
      virtual AXI_BUS_DV #(
        .AXI_ADDR_WIDTH ( AddrWidth      ),
        .AXI_DATA_WIDTH ( DataWidth      ),
        .AXI_ID_WIDTH   ( IdWidthManagers ),
        .AXI_USER_WIDTH ( UserWidth      )
      ) axi_managers_vif [NumManagers-1:0],
      virtual AXI_BUS_DV #(
        .AXI_ADDR_WIDTH ( AddrWidth      ),
        .AXI_DATA_WIDTH ( DataWidth      ),
        .AXI_ID_WIDTH   ( IdWidthSubordinates  ),
        .AXI_USER_WIDTH ( UserWidth      )
      ) axi_subordinates_vif [NumSubordinates-1:0]
    );
      begin
        this.managers_axi     = axi_managers_vif;
        this.subordinates_axi      = axi_subordinates_vif;
        this.tests_expected  = 0;
        this.tests_conducted = 0;
        this.tests_failed    = 0;
        for (int unsigned i = 0; i < NumManagers; i++) begin
          this.exp_b_queue[i] = new;
          this.exp_r_queue[i] = new;
        end
        for (int unsigned i = 0; i < NumSubordinates; i++) begin
          this.exp_aw_queue[i] = new;
          this.exp_ar_queue[i] = new;
        end
        this.cnt_sem = new(1);
      end
    endfunction

    // when start the testing
    task cycle_start;
      #TimeTest;
    endtask

    // when is cycle finished
    task cycle_end;
      @(posedge managers_axi[0].clk_i);
    endtask

    // This task monitors a subordinate ports of the crossbar. Every time an AW beat is seen
    // it populates an id queue at the right manager port (if there is no expected decode error),
    // populates the expected b response in its own id_queue and in case when the atomic bit [5]
    // is set it also injects an expected response in the R channel.
    task automatic monitor_mgr_aw(input int unsigned i);
      idx_sbr_t    to_subordinate_idx;
      exp_ax_t     exp_aw;
      sbr_axi_id_t exp_aw_id;
      bit          decerr;

      manager_exp_t exp_b;

      if (managers_axi[i].aw_valid && managers_axi[i].aw_ready) begin
        // check if it should go to a decerror
        decerr = 1'b1;
        for (int unsigned j = 0; j < NumAddrRules; j++) begin
          if ((managers_axi[i].aw_addr >= AddrMap[j].start_addr) &&
              (managers_axi[i].aw_addr < AddrMap[j].end_addr)) begin
            to_subordinate_idx = idx_sbr_t'(AddrMap[j].idx);
            decerr = 1'b0;
          end
        end
        // send the exp aw beat down into the queue of the subordinate when no decerror
        if (!decerr) begin
          exp_aw_id = {idx_mgr_t'(i), managers_axi[i].aw_id};
          // $display("Test exp aw_id: %b",exp_aw_id);
          exp_aw = '{sbr_axi_id:   exp_aw_id,
                     sbr_axi_addr: managers_axi[i].aw_addr,
                     sbr_axi_len:  managers_axi[i].aw_len   };
          this.exp_aw_queue[to_subordinate_idx].push(exp_aw_id, exp_aw);
          incr_expected_tests(3);
          $display("%0tns > Manager %0d: AW to Subordinate %0d: Axi ID: %b",
              $time, i, to_subordinate_idx, managers_axi[i].aw_id);
        end else begin
          $display("%0tns > Manager %0d: AW to Decerror: Axi ID: %b",
              $time, i, to_subordinate_idx, managers_axi[i].aw_id);
        end
        // populate the expected b queue anyway
        exp_b = '{mgr_axi_id: managers_axi[i].aw_id, last: 1'b1};
        this.exp_b_queue[i].push(managers_axi[i].aw_id, exp_b);
        incr_expected_tests(1);
        $display("        Expect B response.");
        // inject expected r beats on this id, if it is an atop
        if(managers_axi[i].aw_atop[5]) begin
          // push the required r beats into the right fifo (reuse the exp_b variable)
          $display("        Expect R response, len: %0d.", managers_axi[i].aw_len);
          for (int unsigned j = 0; j <= managers_axi[i].aw_len; j++) begin
            exp_b = (j == managers_axi[i].aw_len) ?
                '{mgr_axi_id: managers_axi[i].aw_id, last: 1'b1} :
                '{mgr_axi_id: managers_axi[i].aw_id, last: 1'b0};
            this.exp_r_queue[i].push(managers_axi[i].aw_id, exp_b);
            incr_expected_tests(1);
          end
        end
      end
    endtask : monitor_mgr_aw

    // This task monitors a subordinate port of the crossbar. Every time there is an AW vector it
    // gets checked for its contents and if it was expected. The task then pushes an expected
    // amount of W beats in the respective fifo. Emphasis of the last flag.
    task automatic monitor_sbr_aw(input int unsigned i);
      exp_ax_t    exp_aw;
      subordinate_exp_t exp_sbr_w;
      //  $display("%0t > Was triggered: aw_valid %b, aw_ready: %b",
      //       $time(), subordinates_axi[i].aw_valid, subordinates_axi[i].aw_ready);
      if (subordinates_axi[i].aw_valid && subordinates_axi[i].aw_ready) begin
        // test if the aw beat was expected
        exp_aw = this.exp_aw_queue[i].pop_id(subordinates_axi[i].aw_id);
        $display("%0tns > Subordinate  %0d: AW Axi ID: %b",
            $time, i, subordinates_axi[i].aw_id);
        if (exp_aw.sbr_axi_id != subordinates_axi[i].aw_id) begin
          incr_failed_tests(1);
          $warning("Subordinate %0d: Unexpected AW with ID: %b", i, subordinates_axi[i].aw_id);
        end
        if (exp_aw.sbr_axi_addr != subordinates_axi[i].aw_addr) begin
          incr_failed_tests(1);
          $warning("Subordinate %0d: Unexpected AW with ID: %b and ADDR: %h, exp: %h",
              i, subordinates_axi[i].aw_id, subordinates_axi[i].aw_addr, exp_aw.sbr_axi_addr);
        end
        if (exp_aw.sbr_axi_len != subordinates_axi[i].aw_len) begin
          incr_failed_tests(1);
          $warning("Subordinate %0d: Unexpected AW with ID: %b and LEN: %h, exp: %h",
              i, subordinates_axi[i].aw_id, subordinates_axi[i].aw_len, exp_aw.sbr_axi_len);
        end
        incr_conducted_tests(3);

        // push the required w beats into the right fifo
        incr_expected_tests(subordinates_axi[i].aw_len + 1);
        for (int unsigned j = 0; j <= subordinates_axi[i].aw_len; j++) begin
          exp_sbr_w = (j == subordinates_axi[i].aw_len) ?
              '{sbr_axi_id: subordinates_axi[i].aw_id, last: 1'b1} :
              '{sbr_axi_id: subordinates_axi[i].aw_id, last: 1'b0};
          this.exp_w_fifo[i].push_back(exp_sbr_w);
        end
      end
    endtask : monitor_sbr_aw

    // This task just pushes every W beat that gets sent on a manager port in its respective fifo.
    task automatic monitor_sbr_w(input int unsigned i);
      subordinate_exp_t     act_sbr_w;
      if (subordinates_axi[i].w_valid && subordinates_axi[i].w_ready) begin
        // $display("%0t > W beat on Subordinate %0d, last flag: %b", $time, i, subordinates_axi[i].w_last);
        act_sbr_w = '{last: subordinates_axi[i].w_last , default:'0};
        this.act_w_fifo[i].push_back(act_sbr_w);
      end
    endtask : monitor_sbr_w

    // This task compares the expected and actual W beats on a manager port. The reason that
    // this is not done in `monitor_sbr_w` is that there can be per protocol W beats on the
    // channel, before AW is sent to the subordinate.
    task automatic check_sbr_w(input int unsigned i);
      subordinate_exp_t exp_w, act_w;
      while (this.exp_w_fifo[i].size() != 0 && this.act_w_fifo[i].size() != 0) begin

        exp_w = this.exp_w_fifo[i].pop_front();
        act_w = this.act_w_fifo[i].pop_front();
        // do the check
        incr_conducted_tests(1);
        if(exp_w.last != act_w.last) begin
          incr_failed_tests(1);
          $warning("Subordinate %d: unexpected W beat last flag %b, expected: %b.",
                 i, act_w.last, exp_w.last);
        end
      end
    endtask : check_sbr_w

    // This task checks if a B response is allowed on a subordinate port of the crossbar.
    task automatic monitor_mgr_b(input int unsigned i);
      manager_exp_t exp_b;
      mgr_axi_id_t axi_b_id;
      if (managers_axi[i].b_valid && managers_axi[i].b_ready) begin
        incr_conducted_tests(1);
        axi_b_id = managers_axi[i].b_id;
        $display("%0tns > Manager %0d: Got last B with id: %b",
                $time, i, axi_b_id);
        if (this.exp_b_queue[i].is_empty()) begin
          incr_failed_tests(1);
          $warning("Manager %d: unexpected B beat with ID: %b detected!", i, axi_b_id);
        end else begin
          exp_b = this.exp_b_queue[i].pop_id(axi_b_id);
          if (axi_b_id != exp_b.mgr_axi_id) begin
            incr_failed_tests(1);
            $warning("Manager: %d got unexpected B with ID: %b", i, axi_b_id);
          end
        end
      end
    endtask : monitor_mgr_b

    // This task monitors the AR channel of a subordinate port of the crossbar. For each AR it populates
    // the corresponding ID queue with the number of r beats indicated on the `ar_len` field.
    // Emphasis on the last flag. We will detect reordering, if the last flags do not match,
    // as each `random` burst tend to have a different length.
    task automatic monitor_mgr_ar(input int unsigned i);
      mgr_axi_id_t   mgr_axi_id;
      axi_addr_t     mgr_axi_addr;
      axi_pkg::len_t mgr_axi_len;

      idx_sbr_t      exp_sbr_idx;
      sbr_axi_id_t   exp_sbr_axi_id;
      exp_ax_t       exp_sbr_ar;
      manager_exp_t   exp_mgr_r;

      logic          exp_decerr;

      if (managers_axi[i].ar_valid && managers_axi[i].ar_ready) begin
        exp_decerr     = 1'b1;
        mgr_axi_id     = managers_axi[i].ar_id;
        mgr_axi_addr   = managers_axi[i].ar_addr;
        mgr_axi_len    = managers_axi[i].ar_len;
        exp_sbr_axi_id = {idx_mgr_t'(i), mgr_axi_id};
        exp_sbr_idx    = '0;
        for (int unsigned j = 0; j < NumAddrRules; j++) begin
          if ((mgr_axi_addr >= AddrMap[j].start_addr) && (mgr_axi_addr < AddrMap[j].end_addr)) begin
            exp_sbr_idx = AddrMap[j].idx;
            exp_decerr  = 1'b0;
          end
        end
        if (exp_decerr) begin
          $display("%0tns > Manager %0d: AR to Decerror: Axi ID: %b",
              $time, i, mgr_axi_id);
        end else begin
          $display("%0tns > Manager %0d: AR to Subordinate %0d: Axi ID: %b",
              $time, i, exp_sbr_idx, mgr_axi_id);
          // push the expected vectors AW for exp_sbr
          exp_sbr_ar = '{sbr_axi_id:    exp_sbr_axi_id,
                         sbr_axi_addr:  mgr_axi_addr,
                         sbr_axi_len:   mgr_axi_len     };
          //$display("Expected Sbr Axi Id is: %b", exp_sbr_axi_id);
          this.exp_ar_queue[exp_sbr_idx].push(exp_sbr_axi_id, exp_sbr_ar);
          incr_expected_tests(1);
        end
        // push the required r beats into the right fifo
          $display("        Expect R response, len: %0d.", managers_axi[i].ar_len);
          for (int unsigned j = 0; j <= mgr_axi_len; j++) begin
          exp_mgr_r = (j == mgr_axi_len) ? '{mgr_axi_id: mgr_axi_id, last: 1'b1} :
                                           '{mgr_axi_id: mgr_axi_id, last: 1'b0};
          this.exp_r_queue[i].push(mgr_axi_id, exp_mgr_r);
          incr_expected_tests(1);
        end
      end
    endtask : monitor_mgr_ar

    // This task monitors a manager port of the crossbar and checks if a transmitted AR beat was
    // expected.
    task automatic monitor_sbr_ar(input int unsigned i);
      exp_ax_t       exp_sbr_ar;
      sbr_axi_id_t   sbr_axi_id;
      if (subordinates_axi[i].ar_valid && subordinates_axi[i].ar_ready) begin
        incr_conducted_tests(1);
        sbr_axi_id = subordinates_axi[i].ar_id;
        if (this.exp_ar_queue[i].is_empty()) begin
          incr_failed_tests(1);
        end else begin
          // check that the ids are the same
          exp_sbr_ar = this.exp_ar_queue[i].pop_id(sbr_axi_id);
          $display("%0tns > Subordinate  %0d: AR Axi ID: %b", $time, i, sbr_axi_id);
          if (exp_sbr_ar.sbr_axi_id != sbr_axi_id) begin
            incr_failed_tests(1);
            $warning("Subordinate  %d: Unexpected AR with ID: %b", i, sbr_axi_id);
          end
        end
      end
    endtask : monitor_sbr_ar

    // This task does the R channel monitoring on a subordinate port. It compares the last flags,
    // which are determined by the sequence of previously sent AR vectors.
    task automatic monitor_mgr_r(input int unsigned i);
      manager_exp_t exp_mgr_r;
      mgr_axi_id_t mgr_axi_r_id;
      logic        mgr_axi_r_last;
      if (managers_axi[i].r_valid && managers_axi[i].r_ready) begin
        incr_conducted_tests(1);
        mgr_axi_r_id   = managers_axi[i].r_id;
        mgr_axi_r_last = managers_axi[i].r_last;
        if (mgr_axi_r_last) begin
          $display("%0tns > Manager %0d: Got last R with id: %b",
                   $time, i, mgr_axi_r_id);
        end
        if (this.exp_r_queue[i].is_empty()) begin
          incr_failed_tests(1);
          $warning("Manager %d: unexpected R beat with ID: %b detected!", i, mgr_axi_r_id);
        end else begin
          exp_mgr_r = this.exp_r_queue[i].pop_id(mgr_axi_r_id);
          if (mgr_axi_r_id != exp_mgr_r.mgr_axi_id) begin
            incr_failed_tests(1);
            $warning("Manager: %d got unexpected R with ID: %b", i, mgr_axi_r_id);
          end
          if (mgr_axi_r_last != exp_mgr_r.last) begin
            incr_failed_tests(1);
            $warning("Manager: %d got unexpected R with ID: %b and last flag: %b",
                i, mgr_axi_r_id, mgr_axi_r_last);
          end
        end
      end
    endtask : monitor_mgr_r

    // Some tasks to manage bookkeeping of the tests conducted.
    task incr_expected_tests(input int unsigned times);
      cnt_sem.get();
      this.tests_expected += times;
      cnt_sem.put();
    endtask : incr_expected_tests

    task incr_conducted_tests(input int unsigned times);
      cnt_sem.get();
      this.tests_conducted += times;
      cnt_sem.put();
    endtask : incr_conducted_tests

    task incr_failed_tests(input int unsigned times);
      cnt_sem.get();
      this.tests_failed += times;
      cnt_sem.put();
    endtask : incr_failed_tests

    // This task invokes the various monitoring tasks. It first forks in two, spitting
    // the tasks that should continuously run and the ones that get invoked every clock cycle.
    // For the tasks every clock cycle all processes that only push something in the fifo's and
    // Queues get run. When they are finished the processes that pop something get run.
    task run();
      Continous: fork
        begin
          do begin
            cycle_start();
            // at every cycle span some monitoring processes
            // execute all processes that put something into the queues
            PushMon: fork
              proc_mgr_aw: begin
                for (int unsigned i = 0; i < NumManagers; i++) begin
                  monitor_mgr_aw(i);
                end
              end
              proc_mgr_ar: begin
                for (int unsigned i = 0; i < NumManagers; i++) begin
                  monitor_mgr_ar(i);
                end
              end
            join : PushMon
            // this one pops and pushes something
            proc_sbr_aw: begin
              for (int unsigned i = 0; i < NumSubordinates; i++) begin
                monitor_sbr_aw(i);
              end
            end
            proc_sbr_w: begin
              for (int unsigned i = 0; i < NumSubordinates; i++) begin
                monitor_sbr_w(i);
              end
            end
            // These only pop somethong from the queses
            PopMon: fork
              proc_mgr_b: begin
                for (int unsigned i = 0; i < NumManagers; i++) begin
                  monitor_mgr_b(i);
                end
              end
              proc_sbr_ar: begin
                for (int unsigned i = 0; i < NumSubordinates; i++) begin
                  monitor_sbr_ar(i);
                end
              end
              proc_mgr_r: begin
                for (int unsigned i = 0; i < NumManagers; i++) begin
                  monitor_mgr_r(i);
                end
              end
            join : PopMon
            // check the subordinate W fifos last
            proc_check_sbr_w: begin
              for (int unsigned i = 0; i < NumSubordinates; i++) begin
                check_sbr_w(i);
              end
            end
            cycle_end();
          end while (1'b1);
        end
      join
    endtask : run

    task print_result();
      $info("Simulation has ended!");
      $display("Tests Expected:  %d", this.tests_expected);
      $display("Tests Conducted: %d", this.tests_conducted);
      $display("Tests Failed:    %d", this.tests_failed);
      if(tests_failed > 0) begin
        $error("Simulation encountered unexpected Transactions!!!!!!");
      end
      if(tests_conducted == 0) begin
        $error("Simulation did not conduct any tests!");
      end
    endtask : print_result
  endclass : axi_xbar_monitor
endpackage
