// Copyright (c) 2020 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Author: Matheus Cavalcante <matheusd@iis.ee.ethz.ch>

// `axi_dw_upsizer_monitor` implements an AXI bus monitor that is tuned
// for the AXI Data Width Upsizer. It snoops on the slave and master port
// of the upsizer and populates FIFOs and ID queues to validate that no
// AXI beats get lost.

package tb_axi_dw_pkg;
  /****************
   *  BASE CLASS  *
   ****************/

  class axi_dw_monitor #(
      parameter int unsigned AxiAddrWidth       ,
      parameter int unsigned AxiSlvPortDataWidth,
      parameter int unsigned AxiMstPortDataWidth,
      parameter int unsigned AxiIdWidth         ,
      parameter int unsigned AxiUserWidth       ,
      // Stimuli application and test time
      parameter time TimeTest
    );

    localparam AxiSlvPortStrbWidth = AxiSlvPortDataWidth / 8;
    localparam AxiMstPortStrbWidth = AxiMstPortDataWidth / 8;

    localparam AxiSlvPortMaxSize = $clog2(AxiSlvPortStrbWidth);
    localparam AxiMstPortMaxSize = $clog2(AxiMstPortStrbWidth);

    localparam AxiSlvPortByteMask = AxiSlvPortStrbWidth - 1;
    localparam AxiMstPortByteMask = AxiMstPortStrbWidth - 1;

    typedef logic [AxiIdWidth-1:0] axi_id_t    ;
    typedef logic [AxiAddrWidth-1:0] axi_addr_t;
    typedef axi_pkg::len_t axi_len_t           ;

    typedef struct packed {
      axi_id_t axi_id;
      logic last     ;
    } exp_t;
    typedef struct packed {
      axi_id_t slv_axi_id    ;
      axi_addr_t slv_axi_addr;
      axi_len_t slv_axi_len  ;
    } exp_ax_t;

    typedef rand_id_queue_pkg::rand_id_queue #(
      .data_t  (exp_t     ),
      .ID_WIDTH(AxiIdWidth)
    ) exp_queue_t;
    typedef rand_id_queue_pkg::rand_id_queue #(
      .data_t  (exp_ax_t  ),
      .ID_WIDTH(AxiIdWidth)
    ) ax_queue_t;

    /************************
     *  Virtual Interfaces  *
     ************************/

    virtual AXI_BUS_DV #(
      .AXI_ADDR_WIDTH(AxiAddrWidth       ),
      .AXI_DATA_WIDTH(AxiSlvPortDataWidth),
      .AXI_ID_WIDTH  (AxiIdWidth         ),
      .AXI_USER_WIDTH(AxiUserWidth       )
    ) master_axi;
    virtual AXI_BUS_DV #(
      .AXI_ADDR_WIDTH(AxiAddrWidth       ),
      .AXI_DATA_WIDTH(AxiMstPortDataWidth),
      .AXI_ID_WIDTH  (AxiIdWidth         ),
      .AXI_USER_WIDTH(AxiUserWidth       )
    ) slave_axi;

    /*****************
     *  Bookkeeping  *
     *****************/

    longint unsigned tests_expected;
    longint unsigned tests_conducted;
    longint unsigned tests_failed;
    semaphore        cnt_sem;

    // Queues and FIFOs to hold the expected AXIDs

    // Write transactions
    ax_queue_t  exp_aw_queue;
    exp_t       exp_w_fifo [$];
    exp_t       act_w_fifo [$];
    exp_queue_t exp_b_queue;

    // Read transactions
    ax_queue_t  exp_ar_queue;
    exp_queue_t exp_r_queue;

    /*****************
     *  Constructor  *
     *****************/

    function new (
        virtual AXI_BUS_DV #(
          .AXI_ADDR_WIDTH(AxiAddrWidth       ),
          .AXI_DATA_WIDTH(AxiSlvPortDataWidth),
          .AXI_ID_WIDTH  (AxiIdWidth         ),
          .AXI_USER_WIDTH(AxiUserWidth       )
        ) axi_master_vif,
        virtual AXI_BUS_DV #(
          .AXI_ADDR_WIDTH(AxiAddrWidth       ),
          .AXI_DATA_WIDTH(AxiMstPortDataWidth),
          .AXI_ID_WIDTH  (AxiIdWidth         ),
          .AXI_USER_WIDTH(AxiUserWidth       )
        ) axi_slave_vif
      );
      begin
        this.master_axi      = axi_master_vif;
        this.slave_axi       = axi_slave_vif ;
        this.tests_expected  = 0             ;
        this.tests_conducted = 0             ;
        this.tests_failed    = 0             ;
        this.exp_b_queue     = new           ;
        this.exp_r_queue     = new           ;
        this.exp_aw_queue    = new           ;
        this.exp_ar_queue    = new           ;
        this.cnt_sem         = new(1)        ;
      end
    endfunction

    task cycle_start;
      #TimeTest;
    endtask: cycle_start

    task cycle_end;
      @(posedge master_axi.clk_i);
    endtask: cycle_end

    /**************
     *  Monitors  *
     **************/

    virtual task automatic monitor_mst_aw ();
    endtask

    virtual task automatic monitor_mst_ar ();
    endtask

    // This task monitors the slave port of the DW converter. Every time there is an AW vector it
    // gets checked for its contents and if it was expected. The task then pushes an expected
    // amount of W beats in the respective fifo. Emphasis of the last flag.
    task automatic monitor_slv_aw ();
      exp_ax_t exp_aw;
      exp_t    exp_slv_w;
      if (slave_axi.aw_valid && slave_axi.aw_ready) begin
        // Test if the AW beat was expected
        exp_aw = this.exp_aw_queue.pop_id(slave_axi.aw_id);
        if (exp_aw.slv_axi_id != slave_axi.aw_id) begin
          incr_failed_tests(1)                                         ;
          $warning("Slave: Unexpected AW with ID: %b", slave_axi.aw_id);
        end
        if (exp_aw.slv_axi_addr != slave_axi.aw_addr) begin
          incr_failed_tests(1);
          $warning("Slave : Unexpected AW with ID: %b and ADDR: %h, exp: %h",
            slave_axi.aw_id, slave_axi.aw_addr, exp_aw.slv_axi_addr);
        end
        if (exp_aw.slv_axi_len != slave_axi.aw_len) begin
          incr_failed_tests(1);
          $warning("Slave: Unexpected AW with ID: %b and LEN: %h, exp: %h",
            slave_axi.aw_id, slave_axi.aw_len, exp_aw.slv_axi_len);
        end
        incr_conducted_tests(3);

        // Push the required W beats into the right fifo
        for (int unsigned j = 0; j <= slave_axi.aw_len; j++) begin
          exp_slv_w.axi_id = slave_axi.aw_id;
          exp_slv_w.last   = (j == slave_axi.aw_len) ? 1'b1 : 1'b0;
          this.exp_w_fifo.push_back(exp_slv_w);
          incr_expected_tests(1)              ;
        end
      end
    endtask : monitor_slv_aw

    // This task just pushes every W beat that gets sent on a master port in its respective fifo.
    task automatic monitor_slv_w ();
      exp_t act_slv_w;
      if (slave_axi.w_valid && slave_axi.w_ready) begin
        act_slv_w.last   = slave_axi.w_last ;
        act_slv_w.axi_id = 'x               ;
        this.act_w_fifo.push_back(act_slv_w);
      end
    endtask : monitor_slv_w

    // This task compares the expected and actual W beats on a master port. The reason that
    // this is not done in `monitor_slv_w` is that there can be per protocol W beats on the
    // channel, before AW is sent to the slave.
    task automatic check_slv_w ();
      exp_t exp_w, act_w;
      while (this.exp_w_fifo.size() != 0 && this.act_w_fifo.size() != 0) begin

        exp_w = this.exp_w_fifo.pop_front();
        act_w = this.act_w_fifo.pop_front();
        // do the check
        incr_conducted_tests(1);
        if(exp_w.last != act_w.last) begin
          incr_failed_tests(1);
          $warning("Slave: unexpected W beat last flag %b, expected: %b.",
            act_w.last, exp_w.last);
        end
      end
    endtask : check_slv_w

    // This task checks if a B response is allowed on a slave port of the upsizer.
    task automatic monitor_mst_b ();
      exp_t    exp_b;
      axi_id_t axi_b_id;
      if (master_axi.b_valid && master_axi.b_ready) begin
        incr_conducted_tests(1);
        axi_b_id = master_axi.b_id;
        $display("%0tns > Master: Got last B with ID: %b",
          $time, axi_b_id);
        if (this.exp_b_queue.empty()) begin
          incr_failed_tests(1)                                                 ;
          $warning("Master: unexpected B beat with ID: %b detected!", axi_b_id);
        end else begin
          exp_b = this.exp_b_queue.pop_id(axi_b_id);
          if (axi_b_id != exp_b.axi_id) begin
            incr_failed_tests(1)                                      ;
            $warning("Master: got unexpected B with ID: %b", axi_b_id);
          end
        end
      end
    endtask : monitor_mst_b

    // This task monitors a master port of the DW converter and checks if a transmitted
    // AR beat was expected.
    task automatic monitor_slv_ar ();
      exp_ax_t exp_slv_ar;
      axi_id_t slv_axi_id;
      if (slave_axi.ar_valid && slave_axi.ar_ready) begin
        incr_conducted_tests(1);
        slv_axi_id = slave_axi.ar_id;
        if (this.exp_ar_queue.empty()) begin
          incr_failed_tests(1);
        end else begin
          // check that the ids are the same
          exp_slv_ar = this.exp_ar_queue.pop_id(slv_axi_id);
          $display("%0tns > Slave: AR with ID: %b", $time, slv_axi_id);
          if (exp_slv_ar.slv_axi_id != slv_axi_id) begin
            incr_failed_tests(1)                                    ;
            $warning("Slave: Unexpected AR with ID: %b", slv_axi_id);
          end
        end
      end
    endtask : monitor_slv_ar

    // This task does the R channel monitoring on a slave port. It compares the last flags,
    // which are determined by the sequence of previously sent AR vectors.
    task automatic monitor_mst_r ();
      exp_t    exp_mst_r;
      axi_id_t mst_axi_r_id;
      logic    mst_axi_r_last;
      if (master_axi.r_valid && master_axi.r_ready) begin
        incr_conducted_tests(1);
        mst_axi_r_id   = master_axi.r_id  ;
        mst_axi_r_last = master_axi.r_last;
        if (mst_axi_r_last) begin
          $display("%0tns > Master: Got last R with ID: %b",
            $time, mst_axi_r_id);
        end
        if (this.exp_r_queue.empty()) begin
          incr_failed_tests(1)                                                     ;
          $warning("Master: unexpected R beat with ID: %b detected!", mst_axi_r_id);
        end else begin
          exp_mst_r = this.exp_r_queue.pop_id(mst_axi_r_id);
          if (mst_axi_r_id != exp_mst_r.axi_id) begin
            incr_failed_tests(1)                                          ;
            $warning("Master: got unexpected R with ID: %b", mst_axi_r_id);
          end
          if (mst_axi_r_last != exp_mst_r.last) begin
            incr_failed_tests(1);
            $warning("Master: got unexpected R with ID: %b and last flag: %b",
              mst_axi_r_id, mst_axi_r_last);
          end
        end
      end
    endtask : monitor_mst_r

    // Some tasks to manage bookkeeping of the tests conducted.
    task incr_expected_tests(input int unsigned times);
      cnt_sem.get()               ;
      this.tests_expected += times;
      cnt_sem.put()               ;
    endtask : incr_expected_tests

    task incr_conducted_tests(input int unsigned times);
      cnt_sem.get()                ;
      this.tests_conducted += times;
      cnt_sem.put()                ;
    endtask : incr_conducted_tests

    task incr_failed_tests(input int unsigned times);
      cnt_sem.get()             ;
      this.tests_failed += times;
      cnt_sem.put()             ;
    endtask : incr_failed_tests

    // This task invokes the various monitoring tasks. It first forks in two, splitting
    // the tasks that should continuously run and the ones that get invoked every clock cycle.
    // For the tasks every clock cycle all processes that only push something in the fifo's and
    // Queues get run. When they are finished the processes that pop something get run.
    task run();
      Continous: fork
        begin
          do begin
            // At every cycle, spawn some monitoring processes.
            cycle_start();

            // Execute all processes that push something into the queues
            PushMon: fork
              proc_mst_aw: monitor_mst_aw();
              proc_mst_ar: monitor_mst_ar();
            join: PushMon

            // These pop and push something
            proc_slv_aw: monitor_slv_aw();
            proc_slv_w : monitor_slv_w() ;

            // These only pop something from the queues
            PopMon: fork
              proc_mst_b : monitor_mst_b() ;
              proc_slv_ar: monitor_slv_ar();
              proc_mst_r : monitor_mst_r() ;
            join : PopMon

            // Check the slave W FIFOs last
            proc_check_slv_w: check_slv_w();

            cycle_end();
          end while (1'b1);
        end
      join: Continous
    endtask : run

    task print_result()                                    ;
      $info("Simulation has ended!")                       ;
      $display("Tests Expected:  %d", this.tests_expected) ;
      $display("Tests Conducted: %d", this.tests_conducted);
      $display("Tests Failed:    %d", this.tests_failed)   ;
      if(tests_failed > 0) begin
        $error("Simulation encountered unexpected transactions!!!!!!");
      end
    endtask : print_result

  endclass : axi_dw_monitor


  /*************
   *  UPSIZER  *
   *************/

  class axi_dw_upsizer_monitor #(
      parameter int unsigned AxiAddrWidth       ,
      parameter int unsigned AxiSlvPortDataWidth,
      parameter int unsigned AxiMstPortDataWidth,
      parameter int unsigned AxiIdWidth         ,
      parameter int unsigned AxiUserWidth       ,
      // Stimuli application and test time
      parameter time TimeTest
    ) extends axi_dw_monitor #(
      .AxiAddrWidth       (AxiAddrWidth       ),
      .AxiSlvPortDataWidth(AxiSlvPortDataWidth),
      .AxiMstPortDataWidth(AxiMstPortDataWidth),
      .AxiIdWidth         (AxiIdWidth         ),
      .AxiUserWidth       (AxiUserWidth       ),
      .TimeTest           (TimeTest           )
    );

    /*****************
     *  Constructor  *
     *****************/

    function new (
        virtual AXI_BUS_DV #(
          .AXI_ADDR_WIDTH(AxiAddrWidth       ),
          .AXI_DATA_WIDTH(AxiSlvPortDataWidth),
          .AXI_ID_WIDTH  (AxiIdWidth         ),
          .AXI_USER_WIDTH(AxiUserWidth       )
        ) axi_master_vif,
        virtual AXI_BUS_DV #(
          .AXI_ADDR_WIDTH(AxiAddrWidth       ),
          .AXI_DATA_WIDTH(AxiMstPortDataWidth),
          .AXI_ID_WIDTH  (AxiIdWidth         ),
          .AXI_USER_WIDTH(AxiUserWidth       )
        ) axi_slave_vif
      );
      begin
        super.new(axi_master_vif, axi_slave_vif);
      end
    endfunction

    /**************
     *  Monitors  *
     **************/

    // This task monitors a slave port of the upsizer. Every time an AW beat is seen, it populates
    // the id queue of the right master port, populates the expected b response in its own id_queue
    // and in case when the atomic bit [5] is set it also injects an expected response in the R channel.
    task automatic monitor_mst_aw ();
      exp_ax_t exp_aw;
      exp_t    exp_b;

      if (master_axi.aw_valid && master_axi.aw_ready) begin
        // Non-modifiable transaction
        if (!axi_pkg::modifiable(master_axi.aw_cache)) begin
          // We expect that the transaction will not be modified
          exp_aw = '{
            slv_axi_id  : master_axi.aw_id  ,
            slv_axi_addr: master_axi.aw_addr,
            slv_axi_len : master_axi.aw_len
          } ;
        end
        // Modifiable transaction
        else begin
          case (master_axi.aw_burst)
            // Passthrough upsize
            axi_pkg::BURST_FIXED: begin
              exp_aw = '{
                slv_axi_id  : master_axi.aw_id  ,
                slv_axi_addr: master_axi.aw_addr,
                slv_axi_len : master_axi.aw_len
              };
            end
            // INCR upsize
            axi_pkg::BURST_INCR: begin
              automatic axi_addr_t aligned_start = axi_pkg::aligned_addr(master_axi.aw_addr, AxiMstPortMaxSize)                                                                                                  ;
              automatic axi_addr_t aligned_end   = axi_pkg::aligned_addr(axi_pkg::aligned_addr(master_axi.aw_addr, master_axi.aw_size) + (unsigned'(master_axi.aw_len) << master_axi.aw_size), AxiMstPortMaxSize);

              exp_aw = '{
                slv_axi_id  : master_axi.aw_id  ,
                slv_axi_addr: master_axi.aw_addr,
                slv_axi_len : (aligned_end - aligned_start) >> AxiMstPortMaxSize
              };
            end
            // WRAP upsize
            axi_pkg::BURST_WRAP: begin
              exp_aw = '0;
              $warning("WRAP bursts are not supported.");
            end
          endcase
          this.exp_aw_queue.push(master_axi.aw_id, exp_aw);
          incr_expected_tests(3)                          ;
          $display("%0tns > Master: AW to Slave: Axi ID: %b",
            $time, master_axi.aw_id);
        end

        // Populate the expected B queue
        exp_b = '{axi_id: master_axi.aw_id, last: 1'b1};
        this.exp_b_queue.push(master_axi.aw_id, exp_b);
        incr_expected_tests(1)                        ;
        $display("        Expect B response.")        ;

        // Inject expected R beats on this id, if it is an atop
        if(master_axi.aw_atop[5]) begin
          // Push the required R beats into the right fifo (reuse the exp_b variable)
          $display("        Expect R response, len: %0d.", master_axi.aw_len);
          for (int unsigned j = 0; j <= master_axi.aw_len; j++) begin
            exp_b.axi_id = master_axi.aw_id;
            exp_b.last   = (j == master_axi.aw_len) ? 1'b1 : 1'b0;
            this.exp_r_queue.push(master_axi.aw_id, exp_b);
            incr_expected_tests(1)                        ;
          end
        end
      end
    endtask : monitor_mst_aw

    // This task monitors the AR channel of a slave port of the upsizer. For each AR it populates
    // the corresponding ID queue with the number of R beats indicated on the `ar_len` field.
    // Emphasis on the last flag.
    task automatic monitor_mst_ar ();
      exp_ax_t exp_slv_ar;
      exp_t    exp_mst_r;

      if (master_axi.ar_valid && master_axi.ar_ready) begin
        // Non-modifiable transaction
        if (!axi_pkg::modifiable(master_axi.ar_cache)) begin
          // We expect that the transaction will not be modified
          exp_slv_ar = '{
            slv_axi_id  : master_axi.ar_id  ,
            slv_axi_addr: master_axi.ar_addr,
            slv_axi_len : master_axi.ar_len
          } ;
        end
        // Modifiable transaction
        else begin
          case (master_axi.ar_burst)
            // Passthrough upsize
            axi_pkg::BURST_FIXED: begin
              exp_slv_ar.slv_axi_id   = master_axi.ar_id  ;
              exp_slv_ar.slv_axi_addr = master_axi.ar_addr;
              exp_slv_ar.slv_axi_len  = master_axi.ar_len ;
            end
            // INCR upsize
            axi_pkg::BURST_INCR: begin
              automatic axi_addr_t aligned_start = axi_pkg::aligned_addr(master_axi.ar_addr, AxiMstPortMaxSize)                                                                                                  ;
              automatic axi_addr_t aligned_end   = axi_pkg::aligned_addr(axi_pkg::aligned_addr(master_axi.ar_addr, master_axi.ar_size) + (unsigned'(master_axi.ar_len) << master_axi.ar_size), AxiMstPortMaxSize);

              exp_slv_ar = '{
                slv_axi_id  : master_axi.ar_id  ,
                slv_axi_addr: master_axi.ar_addr,
                slv_axi_len : (aligned_end - aligned_start) >> AxiMstPortMaxSize
              };
            end
            // WRAP upsize
            axi_pkg::BURST_WRAP: begin
              exp_slv_ar = '0;
              $warning("WRAP bursts are not supported.");
            end
          endcase
          this.exp_ar_queue.push(master_axi.ar_id, exp_slv_ar);
          incr_expected_tests(1)                              ;
          $display("%0tns > Master: AR to Slave: Axi ID: %b",
            $time, master_axi.ar_id);
        end

        // Push the required R beats into the right fifo
        $display("        Expect R response, len: %0d.", master_axi.ar_len);
        for (int unsigned j = 0; j <= master_axi.ar_len; j++) begin
          exp_mst_r.axi_id = master_axi.ar_id;
          exp_mst_r.last   = (j == master_axi.ar_len) ? 1'b1 : 1'b0;
          this.exp_r_queue.push(master_axi.ar_id, exp_mst_r);
          incr_expected_tests(1)                            ;
        end
      end
    endtask : monitor_mst_ar
  endclass : axi_dw_upsizer_monitor

  /***************
   *  DOWNSIZER  *
   ***************/

  class axi_dw_downsizer_monitor #(
      parameter int unsigned AxiAddrWidth       ,
      parameter int unsigned AxiSlvPortDataWidth,
      parameter int unsigned AxiMstPortDataWidth,
      parameter int unsigned AxiIdWidth         ,
      parameter int unsigned AxiUserWidth       ,
      // Stimuli application and test time
      parameter time TimeTest
    ) extends axi_dw_monitor #(
      .AxiAddrWidth       (AxiAddrWidth       ),
      .AxiSlvPortDataWidth(AxiSlvPortDataWidth),
      .AxiMstPortDataWidth(AxiMstPortDataWidth),
      .AxiIdWidth         (AxiIdWidth         ),
      .AxiUserWidth       (AxiUserWidth       ),
      .TimeTest           (TimeTest           )
    );

    /*****************
     *  Constructor  *
     *****************/

    function new (
        virtual AXI_BUS_DV #(
          .AXI_ADDR_WIDTH(AxiAddrWidth       ),
          .AXI_DATA_WIDTH(AxiSlvPortDataWidth),
          .AXI_ID_WIDTH  (AxiIdWidth         ),
          .AXI_USER_WIDTH(AxiUserWidth       )
        ) axi_master_vif,
        virtual AXI_BUS_DV #(
          .AXI_ADDR_WIDTH(AxiAddrWidth       ),
          .AXI_DATA_WIDTH(AxiMstPortDataWidth),
          .AXI_ID_WIDTH  (AxiIdWidth         ),
          .AXI_USER_WIDTH(AxiUserWidth       )
        ) axi_slave_vif
      );
      begin
        super.new(axi_master_vif, axi_slave_vif);
      end
    endfunction

    /**************
     *  Monitors  *
     **************/

    // This task monitors a slave port of the downsizer. Every time an AW beat is seen, it populates
    // the id queue at the master port, populates the expected B response in its own id_queue and in
    // case when the atomic bit [5] is set it also injects an expected response in the R channel.
    task automatic monitor_mst_aw ();
      exp_ax_t exp_aw;
      exp_t    exp_b;

      if (master_axi.aw_valid && master_axi.aw_ready) begin
        case (master_axi.aw_burst)
          axi_pkg::BURST_INCR: begin
            automatic int unsigned downsize_ratio = ((1'b1 << master_axi.aw_size) + AxiMstPortStrbWidth - 1) / AxiMstPortStrbWidth ;

            // Transaction unchanged
            if (downsize_ratio == 1) begin
              exp_aw = '{
                slv_axi_id  : master_axi.aw_id  ,
                slv_axi_addr: master_axi.aw_addr,
                slv_axi_len : master_axi.aw_len
              };

              this.exp_aw_queue.push(master_axi.aw_id, exp_aw);
              incr_expected_tests(3)                          ;
            end
            // INCR downsize
            else begin
              automatic axi_addr_t size_mask          = (1'b1 << master_axi.aw_size) - 1                                            ;
              automatic axi_addr_t aligned_adjustment = (master_axi.aw_addr & size_mask & ~AxiMstPortByteMask) / AxiMstPortStrbWidth;
              automatic int unsigned num_beats        = (master_axi.aw_len + 1) * downsize_ratio - aligned_adjustment               ;
              // One burst
              if (num_beats <= 256) begin
                exp_aw = '{
                  slv_axi_id  : master_axi.aw_id  ,
                  slv_axi_addr: master_axi.aw_addr,
                  slv_axi_len : num_beats - 1
                };

                this.exp_aw_queue.push(master_axi.aw_id, exp_aw);
                incr_expected_tests(3)                          ;
              end
              // Need to split the incoming burst into several INCR bursts
              else begin
                automatic axi_addr_t burst_addr;
                automatic axi_len_t burst_len  ;

                // First burst is a "partial" burst
                burst_len = 255 - aligned_adjustment;
                exp_aw    = '{
                  slv_axi_id  : master_axi.aw_id  ,
                  slv_axi_addr: master_axi.aw_addr,
                  slv_axi_len : burst_len
                }                                               ;
                this.exp_aw_queue.push(master_axi.aw_id, exp_aw);
                incr_expected_tests(3)                          ;

                // Push the other bursts in a loop
                num_beats  = num_beats - burst_len - 1                                                                   ;
                burst_addr = axi_pkg::beat_addr(burst_addr, AxiMstPortMaxSize, burst_len, axi_pkg::BURST_INCR, burst_len);
                while (num_beats != 0) begin
                  burst_len = (num_beats - 1) % 256;
                  exp_aw    = '{
                    slv_axi_id  : master_axi.aw_id,
                    slv_axi_addr: burst_addr      ,
                    slv_axi_len : burst_len
                  }                                               ;
                  this.exp_aw_queue.push(master_axi.aw_id, exp_aw);
                  incr_expected_tests(3)                          ;

                  num_beats  = num_beats - burst_len - 1                                                                   ;
                  burst_addr = axi_pkg::beat_addr(burst_addr, AxiMstPortMaxSize, burst_len, axi_pkg::BURST_INCR, burst_len);
                end while (num_beats != 0);
              end
            end
          end
          // Passthrough downsize
          axi_pkg::BURST_FIXED: begin
            automatic int unsigned downsize_ratio = ((1'b1 << master_axi.aw_size) + AxiMstPortStrbWidth - 1) / AxiMstPortStrbWidth;

            // Transaction unchanged
            if (downsize_ratio == 1) begin
              exp_aw = '{
                slv_axi_id  : master_axi.aw_id  ,
                slv_axi_addr: master_axi.aw_addr,
                slv_axi_len : master_axi.aw_len
              };

              this.exp_aw_queue.push(master_axi.aw_id, exp_aw);
              incr_expected_tests(3)                          ;
            end
            // Split into master_axi.aw_len + 1 INCR bursts
            else begin
              for (int unsigned j = 0; j <= master_axi.aw_len; j++) begin
                exp_aw = '{
                  slv_axi_id  : master_axi.aw_id  ,
                  slv_axi_addr: master_axi.aw_addr,
                  slv_axi_len : master_axi.aw_len
                };

                this.exp_aw_queue.push(master_axi.aw_id, exp_aw);
                incr_expected_tests(3)                          ;
              end
            end
          end
          // WRAP downsize
          axi_pkg::BURST_WRAP: begin
            exp_aw = '0;
            $warning("WRAP bursts are not supported.");
          end
        endcase

        $display("%0tns > Master: AW to Slave: with ID: %b",
          $time, master_axi.aw_id);

        // Populate the expected B queue
        exp_b = '{axi_id: master_axi.aw_id, last: 1'b1};
        this.exp_b_queue.push(master_axi.aw_id, exp_b);
        incr_expected_tests(1)                        ;
        $display("        Expect B response.")        ;

        // Inject expected R beats on this id, if it is an atop
        if(master_axi.aw_atop[5]) begin
          // Push the required R beats into the right fifo (reuse the exp_b variable)
          $display("        Expect R response, len: %0d.", master_axi.aw_len);
          for (int unsigned j = 0; j <= master_axi.aw_len; j++) begin
            exp_b.axi_id = master_axi.aw_id;
            exp_b.last   = (j == master_axi.aw_len) ? 1'b1 : 1'b0;
            this.exp_r_queue.push(master_axi.aw_id, exp_b);
            incr_expected_tests(1)                        ;
          end
        end
      end
    endtask : monitor_mst_aw

    // This task monitors the AR channel of a slave port of the downsizer. For each AR it populates
    // the corresponding ID queue with the number of R beats indicated on the `ar_len` field.
    // Emphasis on the last flag.
    task automatic monitor_mst_ar ();
      exp_ax_t exp_slv_ar;
      exp_t    exp_mst_r;

      if (master_axi.ar_valid && master_axi.ar_ready) begin
        case (master_axi.ar_burst)
          axi_pkg::BURST_INCR: begin
            automatic int unsigned downsize_ratio = ((1'b1 << master_axi.ar_size) + AxiMstPortStrbWidth - 1) / AxiMstPortStrbWidth ;

            // Transaction unchanged
            if (downsize_ratio == 1) begin
              exp_slv_ar = '{
                slv_axi_id  : master_axi.ar_id  ,
                slv_axi_addr: master_axi.ar_addr,
                slv_axi_len : master_axi.ar_len
              };

              this.exp_ar_queue.push(master_axi.ar_id, exp_slv_ar);
              incr_expected_tests(1)                              ;
            end
            // INCR downsize
            else begin
              automatic axi_addr_t size_mask          = (1 << master_axi.ar_size) - 1                                               ;
              automatic axi_addr_t aligned_adjustment = (master_axi.ar_addr & size_mask & ~AxiMstPortByteMask) / AxiMstPortStrbWidth;
              automatic int unsigned num_beats        = (master_axi.ar_len + 1) * downsize_ratio - aligned_adjustment               ;
              // One burst
              if (num_beats <= 256) begin
                exp_slv_ar = '{
                  slv_axi_id  : master_axi.ar_id  ,
                  slv_axi_addr: master_axi.ar_addr,
                  slv_axi_len : num_beats - 1
                };

                this.exp_ar_queue.push(master_axi.ar_id, exp_slv_ar);
                incr_expected_tests(1)                              ;
              end
              // Need to split the incoming burst into several INCR bursts
              else begin
                automatic axi_addr_t burst_addr;
                automatic axi_len_t burst_len  ;

                // First burst is a "partial" burst
                burst_len  = 255 - aligned_adjustment;
                exp_slv_ar = '{
                  slv_axi_id  : master_axi.ar_id  ,
                  slv_axi_addr: master_axi.ar_addr,
                  slv_axi_len : burst_len
                }                                                   ;
                this.exp_ar_queue.push(master_axi.ar_id, exp_slv_ar);
                incr_expected_tests(1)                              ;

                // Push the other bursts in a loop
                num_beats  = num_beats - burst_len - 1                                                                   ;
                burst_addr = axi_pkg::beat_addr(burst_addr, AxiMstPortMaxSize, burst_len, axi_pkg::BURST_INCR, burst_len);
                while (num_beats != 0) begin
                  burst_len  = (num_beats - 1) % 256;
                  exp_slv_ar = '{
                    slv_axi_id  : master_axi.ar_id,
                    slv_axi_addr: burst_addr      ,
                    slv_axi_len : burst_len
                  }                                                   ;
                  this.exp_ar_queue.push(master_axi.ar_id, exp_slv_ar);
                  incr_expected_tests(1)                              ;

                  num_beats  = num_beats - burst_len - 1                                                                   ;
                  burst_addr = axi_pkg::beat_addr(burst_addr, AxiMstPortMaxSize, burst_len, axi_pkg::BURST_INCR, burst_len);
                end while (num_beats != 0);
              end
            end
          end
          // Passthrough downsize
          axi_pkg::BURST_FIXED: begin
            automatic int unsigned downsize_ratio = ((1'b1 << master_axi.ar_size) + AxiMstPortStrbWidth - 1) / AxiMstPortStrbWidth;

            // Transaction unchanged
            if (downsize_ratio == 1) begin
              exp_slv_ar = '{
                slv_axi_id  : master_axi.ar_id  ,
                slv_axi_addr: master_axi.ar_addr,
                slv_axi_len : master_axi.ar_len
              };

              this.exp_ar_queue.push(master_axi.ar_id, exp_slv_ar);
              incr_expected_tests(1)                              ;
            end
            // Split into master_axi.ar_len + 1 INCR bursts
            else begin
              for (int unsigned j = 0; j <= master_axi.ar_len; j++) begin
                exp_slv_ar = '{
                  slv_axi_id  : master_axi.ar_id  ,
                  slv_axi_addr: master_axi.ar_addr,
                  slv_axi_len : master_axi.ar_len
                };

                this.exp_ar_queue.push(master_axi.ar_id, exp_slv_ar);
                incr_expected_tests(1)                              ;
              end
            end
          end
          // WRAP downsize
          axi_pkg::BURST_WRAP: begin
            exp_slv_ar = '0;
            $warning("WRAP bursts are not supported.");
          end
        endcase

        $display("%0tns > Master: AR to Slave: with ID: %b",
          $time, master_axi.ar_id);

        // Push the required R beats into the right fifo
        $display("        Expect R response, len: %0d.", master_axi.ar_len);
        for (int unsigned j = 0; j <= master_axi.ar_len; j++) begin
          exp_mst_r.axi_id = master_axi.ar_id;
          exp_mst_r.last   = (j == master_axi.ar_len) ? 1'b1 : 1'b0;
          this.exp_r_queue.push(master_axi.ar_id, exp_mst_r);
          incr_expected_tests(1)                            ;
        end
      end
    endtask : monitor_mst_ar
  endclass : axi_dw_downsizer_monitor

endpackage: tb_axi_dw_pkg
