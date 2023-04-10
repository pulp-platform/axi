// Copyright (c) 2020 ETH Zurich and University of Bologna.
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
// - Matheus Cavalcante <matheusd@iis.ee.ethz.ch>

// `axi_dw_upsizer_monitor` implements an AXI bus monitor that is tuned
// for the AXI Data Width Converters. It snoops on the subordinate and manager port
// of the DWCs and populates FIFOs and ID queues to validate that no
// AXI beats get lost.

package tb_axi_dw_pkg       ;
  import axi_pkg::len_t     ;
  import axi_pkg::burst_t   ;
  import axi_pkg::size_t    ;
  import axi_pkg::cache_t   ;
  import axi_pkg::modifiable;

  /****************
   *  BASE CLASS  *
   ****************/

  class axi_dw_monitor #(
      parameter int unsigned AddrWidth       ,
      parameter int unsigned SbrPortDataWidth,
      parameter int unsigned MgrPortDataWidth,
      parameter int unsigned IdWidth         ,
      parameter int unsigned UserWidth       ,
      // Stimuli application and test time
      parameter time TimeTest
    );

    localparam SbrPortStrbWidth = SbrPortDataWidth / 8;
    localparam MgrPortStrbWidth = MgrPortDataWidth / 8;

    localparam SbrPortMaxSize = $clog2(SbrPortStrbWidth);
    localparam MgrPortMaxSize = $clog2(MgrPortStrbWidth);

    typedef logic [IdWidth-1:0] axi_id_t    ;
    typedef logic [AddrWidth-1:0] axi_addr_t;

    typedef logic [SbrPortDataWidth-1:0] sbr_port_data_t;
    typedef logic [SbrPortStrbWidth-1:0] sbr_port_strb_t;
    typedef logic [MgrPortDataWidth-1:0] mgr_port_data_t;
    typedef logic [MgrPortStrbWidth-1:0] mgr_port_strb_t;

    typedef struct packed {
      axi_id_t axi_id;
      logic axi_last ;
    } exp_b_t;
    typedef struct packed {
      axi_id_t axi_id         ;
      sbr_port_data_t axi_data;
      sbr_port_strb_t axi_strb;
      logic axi_last          ;
    } exp_sbr_rw_t;
    typedef struct packed {
      axi_id_t axi_id         ;
      mgr_port_data_t axi_data;
      mgr_port_strb_t axi_strb;
      logic axi_last          ;
    } exp_mgr_rw_t;
    typedef struct packed {
      axi_id_t axi_id    ;
      axi_addr_t axi_addr;
      len_t axi_len      ;
      burst_t axi_burst  ;
      size_t axi_size    ;
      cache_t axi_cache  ;
    } exp_ax_t;

    typedef rand_id_queue_pkg::rand_id_queue #(
      .data_t  (exp_ax_t),
      .ID_WIDTH(IdWidth )
    ) ax_queue_t;
    typedef rand_id_queue_pkg::rand_id_queue #(
      .data_t  (exp_b_t),
      .ID_WIDTH(IdWidth)
    ) b_queue_t;
    typedef rand_id_queue_pkg::rand_id_queue #(
      .data_t  (exp_sbr_rw_t),
      .ID_WIDTH(IdWidth     )
    ) sbr_r_queue_t;
    typedef rand_id_queue_pkg::rand_id_queue #(
      .data_t  (exp_mgr_rw_t),
      .ID_WIDTH(IdWidth     )
    ) mgr_r_queue_t;

    /**********************
     *  Helper functions  *
     **********************/

    // Returns a byte mask corresponding to the size of the AXI transaction
    function automatic axi_addr_t size_mask(axi_pkg::size_t size);
      return (axi_addr_t'(1) << size) - 1;
    endfunction

    /**
     * Returns the conversion rate between tgt_size and src_size.
     * @return ceil(num_bytes(tgt_size)/num_bytes(src_size))
     */
    function automatic int unsigned conv_ratio(axi_pkg::size_t tgt_size, axi_pkg::size_t src_size)         ;
      return (axi_pkg::num_bytes(tgt_size) + axi_pkg::num_bytes(src_size) - 1)/axi_pkg::num_bytes(src_size);
    endfunction: conv_ratio

    /************************
     *  Virtual Interfaces  *
     ************************/

    virtual AXI_BUS_DV #(
      .AXI_ADDR_WIDTH(AddrWidth       ),
      .AXI_DATA_WIDTH(SbrPortDataWidth),
      .AXI_ID_WIDTH  (IdWidth         ),
      .AXI_USER_WIDTH(UserWidth       )
    ) sbr_port_axi;
    virtual AXI_BUS_DV #(
      .AXI_ADDR_WIDTH(AddrWidth       ),
      .AXI_DATA_WIDTH(MgrPortDataWidth),
      .AXI_ID_WIDTH  (IdWidth         ),
      .AXI_USER_WIDTH(UserWidth       )
    ) mgr_port_axi;

    /*****************
     *  Bookkeeping  *
     *****************/

    longint unsigned tests_expected;
    longint unsigned tests_conducted;
    longint unsigned tests_failed;
    semaphore        cnt_sem;

    // Queues and FIFOs to hold the expected AXIDs

    // Write transactions
    ax_queue_t   exp_mgr_port_aw_queue;
    exp_ax_t     act_mgr_port_aw_queue [$];
    exp_ax_t     act_sbr_port_aw_queue [$];
    exp_mgr_rw_t exp_mgr_port_w_queue [$];
    exp_mgr_rw_t act_mgr_port_w_queue [$];
    exp_sbr_rw_t act_sbr_port_w_queue [$];
    b_queue_t    exp_sbr_port_b_queue;

    // Read transactions
    ax_queue_t    exp_mgr_port_ar_queue;
    ax_queue_t    act_mgr_port_ar_queue;
    ax_queue_t    act_sbr_port_ar_queue;
    exp_sbr_rw_t  act_sbr_port_r_queue [$];
    sbr_r_queue_t exp_sbr_port_r_queue;

    /*****************
     *  Constructor  *
     *****************/

    function new (
        virtual AXI_BUS_DV #(
          .AXI_ADDR_WIDTH(AddrWidth       ),
          .AXI_DATA_WIDTH(SbrPortDataWidth),
          .AXI_ID_WIDTH  (IdWidth         ),
          .AXI_USER_WIDTH(UserWidth       )
        ) sbr_port_vif,
        virtual AXI_BUS_DV #(
          .AXI_ADDR_WIDTH(AddrWidth       ),
          .AXI_DATA_WIDTH(MgrPortDataWidth),
          .AXI_ID_WIDTH  (IdWidth         ),
          .AXI_USER_WIDTH(UserWidth       )
        ) mgr_port_vif
      );
      begin
        this.sbr_port_axi          = sbr_port_vif;
        this.mgr_port_axi          = mgr_port_vif;
        this.tests_expected        = 0           ;
        this.tests_conducted       = 0           ;
        this.tests_failed          = 0           ;
        this.exp_sbr_port_b_queue  = new         ;
        this.exp_sbr_port_r_queue  = new         ;
        this.exp_mgr_port_aw_queue = new         ;
        this.exp_mgr_port_ar_queue = new         ;
        this.act_mgr_port_ar_queue = new         ;
        this.act_sbr_port_ar_queue = new         ;
        this.cnt_sem               = new(1)      ;
      end
    endfunction

    task cycle_start;
      #TimeTest;
    endtask: cycle_start

    task cycle_end;
      @(posedge sbr_port_axi.clk_i);
    endtask: cycle_end

    /**************
     *  Monitors  *
     **************/

    /*
     * You need to override this task. Use it to push the expected AW requests on
     * the subordinate side, and the B and R responses expected on the manager side.
     */
    virtual task automatic mon_sbr_port_aw ()    ;
      $error("This task needs to be overridden.");
    endtask : mon_sbr_port_aw

    /*
     * You need to override this task. Use it to push the expected W requests on
     * the subordinate side.
     */
    virtual task automatic mon_sbr_port_w ()     ;
      $error("This task needs to be overridden.");
    endtask : mon_sbr_port_w

    /*
     * You need to override this task. Use it to push the expected R responses on
     * the manager side.
     */
    virtual task automatic mon_mgr_port_r ()     ;
      $error("This task needs to be overridden.");
    endtask : mon_mgr_port_r

    /*
     * You need to override this task. Use it to push the expected AR requests on
     * the subordinate side, and the R responses expected on the manager side.
     */
    virtual task automatic mon_sbr_port_ar ()    ;
      $error("This task needs to be overridden.");
    endtask : mon_sbr_port_ar

    /*
     * This tasks stores the beats seen by the AR, AW and W channels
     * into the respective queues.
     */
    virtual task automatic store_channels ();
      if (sbr_port_axi.ar_valid && sbr_port_axi.ar_ready)
        act_sbr_port_ar_queue.push(sbr_port_axi.ar_id,
          '{
            axi_id   : sbr_port_axi.ar_id   ,
            axi_burst: sbr_port_axi.ar_burst,
            axi_size : sbr_port_axi.ar_size ,
            axi_addr : sbr_port_axi.ar_addr ,
            axi_len  : sbr_port_axi.ar_len  ,
            axi_cache: sbr_port_axi.ar_cache
          });

      if (sbr_port_axi.aw_valid && sbr_port_axi.aw_ready) begin
        act_sbr_port_aw_queue.push_back('{
            axi_id   : sbr_port_axi.aw_id   ,
            axi_burst: sbr_port_axi.aw_burst,
            axi_size : sbr_port_axi.aw_size ,
            axi_addr : sbr_port_axi.aw_addr ,
            axi_len  : sbr_port_axi.aw_len  ,
            axi_cache: sbr_port_axi.aw_cache
          });

        // This request generates an R response.
        // Push this to the AR queue.
        if (sbr_port_axi.aw_atop[axi_pkg::ATOP_R_RESP])
          act_sbr_port_ar_queue.push(sbr_port_axi.aw_id,
            '{
              axi_id   : sbr_port_axi.aw_id   ,
              axi_burst: sbr_port_axi.aw_burst,
              axi_size : sbr_port_axi.aw_size ,
              axi_addr : sbr_port_axi.aw_addr ,
              axi_len  : sbr_port_axi.aw_len  ,
              axi_cache: sbr_port_axi.aw_cache
            });
      end

      if (sbr_port_axi.w_valid && sbr_port_axi.w_ready)
        this.act_sbr_port_w_queue.push_back('{
            axi_id  : {IdWidth{1'b?}}    ,
            axi_data: sbr_port_axi.w_data,
            axi_strb: sbr_port_axi.w_strb,
            axi_last: sbr_port_axi.w_last
          });

      if (sbr_port_axi.r_valid && sbr_port_axi.r_ready)
        this.act_sbr_port_r_queue.push_back('{
            axi_id  : sbr_port_axi.r_id       ,
            axi_data: sbr_port_axi.r_data     ,
            axi_strb: {SbrPortStrbWidth{1'b?}},
            axi_last: sbr_port_axi.r_last
          });

      if (mgr_port_axi.ar_valid && mgr_port_axi.ar_ready)
        act_mgr_port_ar_queue.push(mgr_port_axi.ar_id,
          '{
            axi_id   : mgr_port_axi.ar_id   ,
            axi_burst: mgr_port_axi.ar_burst,
            axi_size : mgr_port_axi.ar_size ,
            axi_addr : mgr_port_axi.ar_addr ,
            axi_len  : mgr_port_axi.ar_len  ,
            axi_cache: mgr_port_axi.ar_cache
          });

      if (mgr_port_axi.aw_valid && mgr_port_axi.aw_ready) begin
        act_mgr_port_aw_queue.push_back('{
            axi_id   : mgr_port_axi.aw_id   ,
            axi_burst: mgr_port_axi.aw_burst,
            axi_size : mgr_port_axi.aw_size ,
            axi_addr : mgr_port_axi.aw_addr ,
            axi_len  : mgr_port_axi.aw_len  ,
            axi_cache: mgr_port_axi.aw_cache
          });

        // This request generates an R response.
        // Push this to the AR queue.
        if (mgr_port_axi.aw_atop[axi_pkg::ATOP_R_RESP])
          act_mgr_port_ar_queue.push(mgr_port_axi.aw_id,
            '{
              axi_id   : mgr_port_axi.aw_id   ,
              axi_burst: mgr_port_axi.aw_burst,
              axi_size : mgr_port_axi.aw_size ,
              axi_addr : mgr_port_axi.aw_addr ,
              axi_len  : mgr_port_axi.aw_len  ,
              axi_cache: mgr_port_axi.aw_cache
            });
      end

      if (mgr_port_axi.w_valid && mgr_port_axi.w_ready)
        this.act_mgr_port_w_queue.push_back('{
            axi_id  : {IdWidth{1'b?}}    ,
            axi_data: mgr_port_axi.w_data,
            axi_strb: mgr_port_axi.w_strb,
            axi_last: mgr_port_axi.w_last
          });
    endtask

    /*
     * This task monitors the manager port of the DW converter. Every time it gets an AW transaction,
     * it gets checked for its contents against the expected beat on the `exp_aw_queue`.
     */
    task automatic mon_mgr_port_aw ();
      exp_ax_t exp_aw;
      if (mgr_port_axi.aw_valid && mgr_port_axi.aw_ready) begin
        // Test if the AW beat was expected
        exp_aw = this.exp_mgr_port_aw_queue.pop_id(mgr_port_axi.aw_id);
        if (exp_aw.axi_id != mgr_port_axi.aw_id) begin
          incr_failed_tests(1)                                            ;
          $warning("Subordinate: Unexpected AW with ID: %b", mgr_port_axi.aw_id);
        end
        if (exp_aw.axi_addr != mgr_port_axi.aw_addr) begin
          incr_failed_tests(1);
          $warning("Subordinate: Unexpected AW with ID: %b and ADDR: %h, exp: %h",
            mgr_port_axi.aw_id, mgr_port_axi.aw_addr, exp_aw.axi_addr);
        end
        if (exp_aw.axi_len != mgr_port_axi.aw_len) begin
          incr_failed_tests(1);
          $warning("Subordinate: Unexpected AW with ID: %b and LEN: %h, exp: %h",
            mgr_port_axi.aw_id, mgr_port_axi.aw_len, exp_aw.axi_len);
        end
        if (exp_aw.axi_burst != mgr_port_axi.aw_burst) begin
          incr_failed_tests(1);
          $warning("Subordinate: Unexpected AW with ID: %b and BURST: %h, exp: %h",
            mgr_port_axi.aw_id, mgr_port_axi.aw_burst, exp_aw.axi_burst);
        end
        if (exp_aw.axi_size != mgr_port_axi.aw_size) begin
          incr_failed_tests(1);
          $warning("Subordinate: Unexpected AW with ID: %b and SIZE: %h, exp: %h",
            mgr_port_axi.aw_id, mgr_port_axi.aw_size, exp_aw.axi_size);
        end
        if (exp_aw.axi_cache != mgr_port_axi.aw_cache) begin
          incr_failed_tests(1);
          $warning("Subordinate: Unexpected AW with ID: %b and CACHE: %b, exp: %b",
            mgr_port_axi.aw_id, mgr_port_axi.aw_cache, exp_aw.axi_cache);
        end
        incr_conducted_tests(6);
      end
    endtask : mon_mgr_port_aw

    /*
     * This task compares the expected and actual W beats on the manager port.
     */
    task automatic mon_mgr_port_w ();
      exp_mgr_rw_t exp_w, act_w;
      while (this.exp_mgr_port_w_queue.size() != 0 && this.act_mgr_port_w_queue.size() != 0) begin
        exp_w = this.exp_mgr_port_w_queue.pop_front();
        act_w = this.act_mgr_port_w_queue.pop_front();
        // Do the checks
        if (exp_w.axi_data != act_w.axi_data) begin
          incr_failed_tests(1);
          $warning("Subordinate: Unexpected W with DATA: %h, exp: %h",
            act_w.axi_data, exp_w.axi_data);
        end
        if (exp_w.axi_strb != act_w.axi_strb) begin
          incr_failed_tests(1);
          $warning("Subordinate: Unexpected W with STRB: %h, exp: %h",
            act_w.axi_strb, exp_w.axi_strb);
        end
        if (exp_w.axi_last != act_w.axi_last) begin
          incr_failed_tests(1);
          $warning("Subordinate: Unexpected W with LAST: %b, exp: %b",
            act_w.axi_last, exp_w.axi_last);
        end
        incr_conducted_tests(3);
      end
    endtask : mon_mgr_port_w

    /*
     * This task checks if a B response is allowed on a subordinate port of the DW converter.
     */
    task automatic mon_sbr_port_b ();
      exp_b_t  exp_b;
      axi_id_t axi_b_id;
      if (sbr_port_axi.b_valid && sbr_port_axi.b_ready) begin
        incr_conducted_tests(1);
        axi_b_id = sbr_port_axi.b_id;
        $display("%0tns > Manager: Got last B with ID: %b",
          $time, axi_b_id);
        if (this.exp_sbr_port_b_queue.is_empty()) begin
          incr_failed_tests(1)                                                 ;
          $warning("Manager: unexpected B beat with ID: %b detected!", axi_b_id);
        end else begin
          exp_b = this.exp_sbr_port_b_queue.pop_id(axi_b_id);
          if (axi_b_id != exp_b.axi_id) begin
            incr_failed_tests(1)                                      ;
            $warning("Manager: got unexpected B with ID: %b", axi_b_id);
          end
        end
      end
    endtask : mon_sbr_port_b

    /*
     * This task monitors a the manager port of the DW converter and checks
     * if the AR beats were all expected.
     */
    task automatic mon_mgr_port_ar ();
      exp_ax_t exp_ar;
      if (mgr_port_axi.ar_valid && mgr_port_axi.ar_ready) begin
        // Test if the AR beat was expected
        exp_ar = this.exp_mgr_port_ar_queue.pop_id(mgr_port_axi.ar_id);
        if (exp_ar.axi_id != mgr_port_axi.ar_id) begin
          incr_failed_tests(1)                                            ;
          $warning("Subordinate: Unexpected AR with ID: %b", mgr_port_axi.ar_id);
        end
        if (exp_ar.axi_addr != mgr_port_axi.ar_addr) begin
          incr_failed_tests(1);
          $warning("Subordinate: Unexpected AR with ID: %b and ADDR: %h, exp: %h",
            mgr_port_axi.ar_id, mgr_port_axi.ar_addr, exp_ar.axi_addr);
        end
        if (exp_ar.axi_len != mgr_port_axi.ar_len) begin
          incr_failed_tests(1);
          $warning("Subordinate: Unexpected AR with ID: %b and LEN: %h, exp: %h",
            mgr_port_axi.ar_id, mgr_port_axi.ar_len, exp_ar.axi_len);
        end
        if (exp_ar.axi_burst != mgr_port_axi.ar_burst) begin
          incr_failed_tests(1);
          $warning("Subordinate: Unexpected AR with ID: %b and BURST: %h, exp: %h",
            mgr_port_axi.ar_id, mgr_port_axi.ar_burst, exp_ar.axi_burst);
        end
        if (exp_ar.axi_size != mgr_port_axi.ar_size) begin
          incr_failed_tests(1);
          $warning("Subordinate: Unexpected AR with ID: %b and SIZE: %h, exp: %h",
            mgr_port_axi.ar_id, mgr_port_axi.ar_size, exp_ar.axi_size);
        end
        if (exp_ar.axi_cache != mgr_port_axi.ar_cache) begin
          incr_failed_tests(1);
          $warning("Subordinate: Unexpected AR with ID: %b and CACHE: %b, exp: %b",
            mgr_port_axi.ar_id, mgr_port_axi.ar_cache, exp_ar.axi_cache);
        end
        incr_conducted_tests(6);
      end
    endtask : mon_mgr_port_ar

    /*
     * This task does the R channel monitoring on a subordinate port. It compares the last flags,
     * which are determined by the sequence of previously sent AR vectors.
     */
    task automatic mon_sbr_port_r ();
      exp_sbr_rw_t exp_r;
      if (act_sbr_port_r_queue.size() != 0) begin
        exp_sbr_rw_t act_r = act_sbr_port_r_queue[0] ;
        if (exp_sbr_port_r_queue.queues[act_r.axi_id].size() != 0) begin
          exp_r = exp_sbr_port_r_queue.pop_id(act_r.axi_id);
          void'(act_sbr_port_r_queue.pop_front());

          // Do the checks
          if (exp_r.axi_id != act_r.axi_id) begin
            incr_failed_tests(1);
            $warning("Subordinate: Unexpected R with ID: %b",
              act_r.axi_id);
          end
          if (exp_r.axi_last != act_r.axi_last) begin
            incr_failed_tests(1);
            $warning("Subordinate: Unexpected R with ID: %b and LAST: %b, exp: %b",
              act_r.axi_id, act_r.axi_last, exp_r.axi_last);
          end
          if (exp_r.axi_data != act_r.axi_data) begin
            incr_failed_tests(1);
            $warning("Subordinate: Unexpected R with ID: %b and DATA: %h, exp: %h",
              act_r.axi_id, act_r.axi_data, exp_r.axi_data);
          end
          incr_conducted_tests(3);
        end
      end
    endtask : mon_sbr_port_r

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

    /*
     * This task invokes the various monitoring tasks. First, all processes that only
     * push something in the FIFOs are invoked. After they are finished, the processes
     * that pop something from them are invoked.
     */
    task run();
      forever begin
        // At every cycle, spawn some monitoring processes.
        cycle_start();

        // Execute all processes that push something into the queues
        PushMon: fork
          proc_mgr_aw       : mon_sbr_port_aw();
          proc_mgr_ar       : mon_sbr_port_ar();
          proc_mgr_w        : mon_sbr_port_w() ;
          proc_sbr_r        : mon_mgr_port_r() ;
          proc_store_channel: store_channels() ;
        join: PushMon

        // These only pop something from the queues
        PopMon: fork
          proc_sbr_aw: mon_mgr_port_aw();
          proc_mgr_b : mon_sbr_port_b() ;
          proc_sbr_ar: mon_mgr_port_ar();
          proc_mgr_r : mon_sbr_port_r() ;
        join : PopMon

        // Check the subordinate W FIFOs last
        proc_check_sbr_w: mon_mgr_port_w();

        cycle_end();
      end
    endtask : run

    task print_result()                                    ;
      $info("Simulation has ended!")                       ;
      $display("Tests Expected:  %d", this.tests_expected) ;
      $display("Tests Conducted: %d", this.tests_conducted);
      $display("Tests Failed:    %d", this.tests_failed)   ;
      if (tests_failed > 0) begin
        $error("Simulation encountered unexpected transactions!");
      end
    endtask : print_result

  endclass : axi_dw_monitor

  /*************
   *  UPSIZER  *
   *************/

  class axi_dw_upsizer_monitor #(
      parameter int unsigned AddrWidth       ,
      parameter int unsigned SbrPortDataWidth,
      parameter int unsigned MgrPortDataWidth,
      parameter int unsigned IdWidth         ,
      parameter int unsigned UserWidth       ,
      // Stimuli application and test time
      parameter time TimeTest
    ) extends axi_dw_monitor #(
      .AddrWidth       (AddrWidth       ),
      .SbrPortDataWidth(SbrPortDataWidth),
      .MgrPortDataWidth(MgrPortDataWidth),
      .IdWidth         (IdWidth         ),
      .UserWidth       (UserWidth       ),
      .TimeTest        (TimeTest        )
    );

    local static shortint unsigned sbr_port_r_cnt[axi_id_t];
    local static shortint unsigned mgr_port_r_cnt[axi_id_t];
    local static shortint unsigned sbr_port_w_cnt;
    local static shortint unsigned mgr_port_w_cnt;
    local static exp_mgr_rw_t      mgr_port_w;
    local static shortint unsigned mgr_port_w_pnt;

    /*****************
     *  Constructor  *
     *****************/

    function new (
        virtual AXI_BUS_DV #(
          .AXI_ADDR_WIDTH(AddrWidth       ),
          .AXI_DATA_WIDTH(SbrPortDataWidth),
          .AXI_ID_WIDTH  (IdWidth         ),
          .AXI_USER_WIDTH(UserWidth       )
        ) sbr_port_vif,
        virtual AXI_BUS_DV #(
          .AXI_ADDR_WIDTH(AddrWidth       ),
          .AXI_DATA_WIDTH(MgrPortDataWidth),
          .AXI_ID_WIDTH  (IdWidth         ),
          .AXI_USER_WIDTH(UserWidth       )
        ) mgr_port_vif
      );
      begin
        super.new(sbr_port_vif, mgr_port_vif);
        sbr_port_w_cnt = '0;
        mgr_port_w_cnt = '0;
        mgr_port_w_pnt = '1;
        mgr_port_w     = '0;
        for (int unsigned id = 0; id < 2**IdWidth; id++) begin
          sbr_port_r_cnt[id] = '0;
          mgr_port_r_cnt[id] = '0;
        end
      end
    endfunction

    /**************
     *  Monitors  *
     **************/

    task automatic mon_sbr_port_aw ();
      exp_ax_t exp_aw;

      if (sbr_port_axi.aw_valid && sbr_port_axi.aw_ready) begin
        // Non-modifiable transaction
        if (!axi_pkg::modifiable(sbr_port_axi.aw_cache)) begin
          // We expect that the transaction will not be modified
          exp_aw = '{
            axi_id   : sbr_port_axi.aw_id   ,
            axi_addr : sbr_port_axi.aw_addr ,
            axi_len  : sbr_port_axi.aw_len  ,
            axi_burst: sbr_port_axi.aw_burst,
            axi_size : sbr_port_axi.aw_size ,
            axi_cache: sbr_port_axi.aw_cache
          } ;
        end
        // Modifiable transaction
        else begin
          case (sbr_port_axi.aw_burst)
            // Passthrough upsize
            axi_pkg::BURST_FIXED: begin
              exp_aw = '{
                axi_id   : sbr_port_axi.aw_id   ,
                axi_addr : sbr_port_axi.aw_addr ,
                axi_len  : sbr_port_axi.aw_len  ,
                axi_burst: sbr_port_axi.aw_burst,
                axi_size : sbr_port_axi.aw_size ,
                axi_cache: sbr_port_axi.aw_cache
              };
            end
            // INCR upsize
            axi_pkg::BURST_INCR: begin
              automatic axi_addr_t aligned_start = axi_pkg::aligned_addr(sbr_port_axi.aw_addr, MgrPortMaxSize)                                                                                                        ;
              automatic axi_addr_t aligned_end   = axi_pkg::aligned_addr(axi_pkg::aligned_addr(sbr_port_axi.aw_addr, sbr_port_axi.aw_size) + (unsigned'(sbr_port_axi.aw_len) << sbr_port_axi.aw_size), MgrPortMaxSize);

              exp_aw = '{
                axi_id   : sbr_port_axi.aw_id                              ,
                axi_addr : sbr_port_axi.aw_addr                            ,
                axi_len  : (aligned_end - aligned_start) >> MgrPortMaxSize ,
                axi_burst: sbr_port_axi.aw_burst                           ,
                axi_size : sbr_port_axi.aw_len == 0 ? sbr_port_axi.aw_size : MgrPortMaxSize,
                axi_cache: sbr_port_axi.aw_cache
              };
            end
            // WRAP upsize
            axi_pkg::BURST_WRAP: begin
              exp_aw = '0;
              $warning("WRAP bursts are not supported.");
            end
          endcase
          this.exp_mgr_port_aw_queue.push(sbr_port_axi.aw_id, exp_aw);
          incr_expected_tests(6)                                     ;
          $display("%0tns > Manager: AW with ID: %b",
            $time, sbr_port_axi.aw_id);
        end

        // Populate the expected B responses
        this.exp_sbr_port_b_queue.push(sbr_port_axi.aw_id, '{
            axi_id  : sbr_port_axi.aw_id,
            axi_last: 1'b1
          })                                   ;
        incr_expected_tests(1)                 ;
        $display("        Expect B response.") ;
      end
    endtask : mon_sbr_port_aw

    task automatic mon_sbr_port_w ();
      if (act_sbr_port_w_queue.size() != 0) begin
        exp_sbr_rw_t act_sbr_w = act_sbr_port_w_queue[0];

        if (act_mgr_port_aw_queue.size() != 0 && act_sbr_port_aw_queue.size() != 0) begin
          // Retrieve the AW requests related to this W beat
          exp_ax_t act_mgr_aw = act_mgr_port_aw_queue[0];
          exp_ax_t act_sbr_aw = act_sbr_port_aw_queue[0];

          // Calculate the offsets
          shortint unsigned mgr_port_lower_byte =
          axi_pkg::beat_lower_byte(act_mgr_aw.axi_addr, act_mgr_aw.axi_size, act_mgr_aw.axi_len, act_mgr_aw.axi_burst, MgrPortStrbWidth, mgr_port_w_cnt);
          shortint unsigned mgr_port_upper_byte =
          axi_pkg::beat_upper_byte(act_mgr_aw.axi_addr, act_mgr_aw.axi_size, act_mgr_aw.axi_len, act_mgr_aw.axi_burst, MgrPortStrbWidth, mgr_port_w_cnt);
          shortint unsigned sbr_port_lower_byte =
          axi_pkg::beat_lower_byte(act_sbr_aw.axi_addr, act_sbr_aw.axi_size, act_sbr_aw.axi_len, act_sbr_aw.axi_burst, SbrPortStrbWidth, sbr_port_w_cnt);
          shortint unsigned sbr_port_upper_byte =
          axi_pkg::beat_upper_byte(act_sbr_aw.axi_addr, act_sbr_aw.axi_size, act_sbr_aw.axi_len, act_sbr_aw.axi_burst, SbrPortStrbWidth, sbr_port_w_cnt);

          shortint unsigned bytes_copied = 0;
          // Pointer inside the outcoming word
          if (mgr_port_w_pnt == '1)
            mgr_port_w_pnt = mgr_port_lower_byte;

          mgr_port_w.axi_last = mgr_port_w_cnt == act_mgr_aw.axi_len;
          for (shortint unsigned b = sbr_port_lower_byte; b <= sbr_port_upper_byte; b++) begin
            if (b + mgr_port_w_pnt - sbr_port_lower_byte == MgrPortStrbWidth)
              break;
            mgr_port_w.axi_data[8*(b + mgr_port_w_pnt - sbr_port_lower_byte) +: 8] = act_sbr_w.axi_data[8*b +: 8];
            mgr_port_w.axi_strb[b + mgr_port_w_pnt - sbr_port_lower_byte]          = act_sbr_w.axi_strb[b]       ;
            bytes_copied++;
          end

          // Increment the len counters
          sbr_port_w_cnt++              ;
          mgr_port_w_pnt += bytes_copied;

          if (act_mgr_aw.axi_burst == axi_pkg::BURST_FIXED // No upsizing
              || mgr_port_w_pnt == MgrPortStrbWidth        // Filled up an outcoming W beat
              || act_sbr_w.axi_last                        // Last beat of a W burst
            ) begin
            // Don't care for the bits outside these accessed by this request
            for (int unsigned b = 0; b < MgrPortStrbWidth; b++)
              if (!(mgr_port_lower_byte <= b && b <= mgr_port_upper_byte))
                mgr_port_w.axi_data[8*b +: 8] = {8{1'b?}};

            this.exp_mgr_port_w_queue.push_back(mgr_port_w);
            incr_expected_tests(3)                         ;

            // Increment the len counter
            mgr_port_w_cnt++;

            // Reset W beat
            mgr_port_w     = '0;
            mgr_port_w_pnt = '1;
          end

          // Pop the AW request from the queues
          if (sbr_port_w_cnt == act_sbr_aw.axi_len + 1) begin
            void'(act_sbr_port_aw_queue.pop_front());
            sbr_port_w_cnt = 0;
          end
          if (mgr_port_w_cnt == act_mgr_aw.axi_len + 1) begin
            void'(act_mgr_port_aw_queue.pop_front());
            mgr_port_w_cnt = 0;
          end

          // Pop the W request
          void'(act_sbr_port_w_queue.pop_front());
        end
      end
    endtask : mon_sbr_port_w

    task automatic mon_sbr_port_ar ();
      exp_ax_t exp_sbr_ar;
      exp_b_t  exp_mgr_r;

      if (sbr_port_axi.ar_valid && sbr_port_axi.ar_ready) begin
        // Non-modifiable transaction
        if (!axi_pkg::modifiable(sbr_port_axi.ar_cache)) begin
          // We expect that the transaction will not be modified
          exp_sbr_ar = '{
            axi_id   : sbr_port_axi.ar_id   ,
            axi_addr : sbr_port_axi.ar_addr ,
            axi_len  : sbr_port_axi.ar_len  ,
            axi_burst: sbr_port_axi.ar_burst,
            axi_size : sbr_port_axi.ar_size ,
            axi_cache: sbr_port_axi.ar_cache
          };
        end
        // Modifiable transaction
        else begin
          case (sbr_port_axi.ar_burst)
            // Passthrough upsize
            axi_pkg::BURST_FIXED: begin
              exp_sbr_ar = '{
                axi_id   : sbr_port_axi.ar_id   ,
                axi_addr : sbr_port_axi.ar_addr ,
                axi_len  : sbr_port_axi.ar_len  ,
                axi_burst: sbr_port_axi.ar_burst,
                axi_size : sbr_port_axi.ar_size ,
                axi_cache: sbr_port_axi.ar_cache
              };
            end
            // INCR upsize
            axi_pkg::BURST_INCR: begin
              automatic axi_addr_t aligned_start = axi_pkg::aligned_addr(sbr_port_axi.ar_addr, MgrPortMaxSize)                                                                                                        ;
              automatic axi_addr_t aligned_end   = axi_pkg::aligned_addr(axi_pkg::aligned_addr(sbr_port_axi.ar_addr, sbr_port_axi.ar_size) + (unsigned'(sbr_port_axi.ar_len) << sbr_port_axi.ar_size), MgrPortMaxSize);

              exp_sbr_ar = '{
                axi_id   : sbr_port_axi.ar_id                              ,
                axi_addr : sbr_port_axi.ar_addr                            ,
                axi_len  : (aligned_end - aligned_start) >> MgrPortMaxSize ,
                axi_burst: sbr_port_axi.ar_burst                           ,
                axi_size : sbr_port_axi.ar_len == 0 ? sbr_port_axi.ar_size : MgrPortMaxSize,
                axi_cache: sbr_port_axi.ar_cache
              };
            end
            // WRAP upsize
            axi_pkg::BURST_WRAP: begin
              exp_sbr_ar = '0;
              $warning("WRAP bursts are not supported.");
            end
          endcase
          this.exp_mgr_port_ar_queue.push(sbr_port_axi.ar_id, exp_sbr_ar);
          incr_expected_tests(6)                                         ;
          $display("%0tns > Manager: AR with ID: %b",
            $time, sbr_port_axi.ar_id);
        end
      end
    endtask : mon_sbr_port_ar

    task automatic mon_mgr_port_r ();
      if (mgr_port_axi.r_valid && mgr_port_axi.r_ready) begin
        // Retrieve the AR requests related to this R beat
        exp_ax_t act_mgr_ar = act_mgr_port_ar_queue.get(mgr_port_axi.r_id);
        exp_ax_t act_sbr_ar = act_sbr_port_ar_queue.get(mgr_port_axi.r_id);
        axi_id_t id         = mgr_port_axi.r_id                           ;

        // Calculate the offsets inside the incoming word
        shortint unsigned mgr_port_lower_byte =
        axi_pkg::beat_lower_byte(act_mgr_ar.axi_addr, act_mgr_ar.axi_size, act_mgr_ar.axi_len, act_mgr_ar.axi_burst, MgrPortStrbWidth, mgr_port_r_cnt[id]);
        shortint unsigned mgr_port_upper_byte =
        axi_pkg::beat_upper_byte(act_mgr_ar.axi_addr, act_mgr_ar.axi_size, act_mgr_ar.axi_len, act_mgr_ar.axi_burst, MgrPortStrbWidth, mgr_port_r_cnt[id]);
        // Pointer inside the incoming word
        shortint unsigned mgr_port_data_pointer = mgr_port_lower_byte;

        // Conversion ratio. How many R beats are generated from this incoming R beat.
        int unsigned conversion_ratio = axi_pkg::modifiable(act_mgr_ar.axi_cache) ? conv_ratio(act_mgr_ar.axi_size, act_sbr_ar.axi_size) : 1;

        // Several R beats generated from this incoming R beat
        for (int unsigned beat = 0; beat < conversion_ratio; beat++) begin
          exp_sbr_rw_t act_sbr_r = '0;

          // Calculate the offsets inside the outcoming word
          shortint unsigned sbr_port_lower_byte =
          axi_pkg::beat_lower_byte(act_sbr_ar.axi_addr, act_sbr_ar.axi_size, act_sbr_ar.axi_len, act_sbr_ar.axi_burst, SbrPortStrbWidth, sbr_port_r_cnt[id]);
          shortint unsigned sbr_port_upper_byte =
          axi_pkg::beat_upper_byte(act_sbr_ar.axi_addr, act_sbr_ar.axi_size, act_sbr_ar.axi_len, act_sbr_ar.axi_burst, SbrPortStrbWidth, sbr_port_r_cnt[id]);

          shortint unsigned bytes_copied = 0;

          act_sbr_r.axi_id   = mgr_port_axi.r_id                       ;
          act_sbr_r.axi_last = sbr_port_r_cnt[id] == act_sbr_ar.axi_len;
          act_sbr_r.axi_data = {SbrPortDataWidth{1'b?}}                ;
          act_sbr_r.axi_strb = {SbrPortStrbWidth{1'b?}}                ;
          for (shortint unsigned b = mgr_port_data_pointer; b <= mgr_port_upper_byte; b++) begin
            act_sbr_r.axi_data[8*(b + sbr_port_lower_byte - mgr_port_data_pointer) +: 8] = mgr_port_axi.r_data[8*b +: 8];
            bytes_copied++;
            if (b + sbr_port_lower_byte - mgr_port_data_pointer == sbr_port_upper_byte)
              break;
          end
          this.exp_sbr_port_r_queue.push(act_sbr_r.axi_id, act_sbr_r);
          incr_expected_tests(3)                                     ;

          // Increment the len counters
          sbr_port_r_cnt[id]++                 ;
          mgr_port_data_pointer += bytes_copied;

          // Used the whole R beat
          if (mgr_port_data_pointer == MgrPortStrbWidth)
            break;
          // Finished the R beat
          if (act_sbr_r.axi_last)
            break;
        end

        // Increment the len counter
        mgr_port_r_cnt[id]++;

        // Pop the AR request from the queues
        if (mgr_port_r_cnt[id] == act_mgr_ar.axi_len + 1) begin
          void'(act_mgr_port_ar_queue.pop_id(act_mgr_ar.axi_id));
          mgr_port_r_cnt[id] = 0;
        end
        if (sbr_port_r_cnt[id] == act_sbr_ar.axi_len + 1) begin
          void'(act_sbr_port_ar_queue.pop_id(act_sbr_ar.axi_id));
          sbr_port_r_cnt[id] = 0;
        end
      end
    endtask: mon_mgr_port_r
  endclass : axi_dw_upsizer_monitor

  /***************
   *  DOWNSIZER  *
   ***************/

  class axi_dw_downsizer_monitor #(
      parameter int unsigned AddrWidth       ,
      parameter int unsigned SbrPortDataWidth,
      parameter int unsigned MgrPortDataWidth,
      parameter int unsigned IdWidth         ,
      parameter int unsigned UserWidth       ,
      // Stimuli application and test time
      parameter time TimeTest
    ) extends axi_dw_monitor #(
      .AddrWidth       (AddrWidth       ),
      .SbrPortDataWidth(SbrPortDataWidth),
      .MgrPortDataWidth(MgrPortDataWidth),
      .IdWidth         (IdWidth         ),
      .UserWidth       (UserWidth       ),
      .TimeTest        (TimeTest        )
    );

    local static shortint unsigned sbr_port_r_cnt[axi_id_t];
    local static shortint unsigned mgr_port_r_cnt[axi_id_t];
    local static exp_sbr_rw_t      sbr_port_r[axi_id_t];
    local static shortint unsigned sbr_port_r_pnt[axi_id_t];
    local static shortint unsigned sbr_port_w_cnt;
    local static shortint unsigned mgr_port_w_cnt;

    /**********************
     *  Helper functions  *
     **********************/

    /*
     * Returns how many beats of the incoming AXI transaction will be dropped after downsizing
     * due to an unaligned memory address.
     */
    function automatic len_t aligned_adjustment(axi_addr_t addr, axi_pkg::size_t size)               ;
      return (addr & size_mask(size) & ~size_mask(MgrPortMaxSize))/axi_pkg::num_bytes(MgrPortMaxSize);
    endfunction: aligned_adjustment

    /*****************
     *  Constructor  *
     *****************/

    function new (
        virtual AXI_BUS_DV #(
          .AXI_ADDR_WIDTH(AddrWidth       ),
          .AXI_DATA_WIDTH(SbrPortDataWidth),
          .AXI_ID_WIDTH  (IdWidth         ),
          .AXI_USER_WIDTH(UserWidth       )
        ) sbr_port_vif,
        virtual AXI_BUS_DV #(
          .AXI_ADDR_WIDTH(AddrWidth       ),
          .AXI_DATA_WIDTH(MgrPortDataWidth),
          .AXI_ID_WIDTH  (IdWidth         ),
          .AXI_USER_WIDTH(UserWidth       )
        ) mgr_port_vif
      );
      begin
        super.new(sbr_port_vif, mgr_port_vif);

        sbr_port_w_cnt = 0;
        mgr_port_w_cnt = 0;
        for (int unsigned id = 0; id < 2**IdWidth; id++) begin
          sbr_port_r_cnt[id] = '0;
          mgr_port_r_cnt[id] = '0;
          sbr_port_r[id]     = '0;
          sbr_port_r_pnt[id] = '1;
        end
      end
    endfunction

    /**************
     *  Monitors  *
     **************/

    task automatic mon_sbr_port_aw ();
      exp_ax_t exp_aw;

      if (sbr_port_axi.aw_valid && sbr_port_axi.aw_ready) begin
        case (sbr_port_axi.aw_burst)
          axi_pkg::BURST_INCR: begin
            // Transaction unchanged
            if (conv_ratio(sbr_port_axi.aw_size, MgrPortMaxSize) == 1) begin
              exp_aw = '{
                axi_id   : sbr_port_axi.aw_id   ,
                axi_addr : sbr_port_axi.aw_addr ,
                axi_len  : sbr_port_axi.aw_len  ,
                axi_burst: sbr_port_axi.aw_burst,
                axi_size : sbr_port_axi.aw_size ,
                axi_cache: sbr_port_axi.aw_cache
              };

              this.exp_mgr_port_aw_queue.push(sbr_port_axi.aw_id, exp_aw);
              incr_expected_tests(6)                                     ;
            end
            // INCR downsize
            else begin
              automatic int unsigned num_beats = (sbr_port_axi.aw_len + 1) * conv_ratio(sbr_port_axi.aw_size, MgrPortMaxSize) - aligned_adjustment(sbr_port_axi.aw_addr, sbr_port_axi.aw_size);
              // One burst
              if (num_beats <= 256) begin
                exp_aw = '{
                  axi_id   : sbr_port_axi.aw_id   ,
                  axi_addr : sbr_port_axi.aw_addr ,
                  axi_len  : num_beats - 1        ,
                  axi_burst: sbr_port_axi.aw_burst,
                  axi_size : MgrPortMaxSize       ,
                  axi_cache: sbr_port_axi.aw_cache
                };

                this.exp_mgr_port_aw_queue.push(sbr_port_axi.aw_id, exp_aw);
                incr_expected_tests(6)                                     ;
              end
              // Need to split the incoming burst into several INCR bursts
              else begin
                automatic axi_addr_t burst_addr;
                automatic len_t burst_len      ;

                // First burst is a "partial" burst
                burst_len = 255 - aligned_adjustment(sbr_port_axi.aw_addr, sbr_port_axi.aw_size);
                exp_aw    = '{
                  axi_id   : sbr_port_axi.aw_id   ,
                  axi_addr : sbr_port_axi.aw_addr ,
                  axi_len  : burst_len            ,
                  axi_burst: sbr_port_axi.aw_burst,
                  axi_size : MgrPortMaxSize       ,
                  axi_cache: sbr_port_axi.aw_cache
                }                                                          ;
                this.exp_mgr_port_aw_queue.push(sbr_port_axi.aw_id, exp_aw);
                incr_expected_tests(6)                                     ;

                // Push the other bursts in a loop
                num_beats  = num_beats - burst_len - 1                                                                                                                   ;
                burst_addr = axi_pkg::beat_addr(axi_pkg::aligned_addr(sbr_port_axi.aw_addr, MgrPortMaxSize), MgrPortMaxSize, burst_len, axi_pkg::BURST_INCR, burst_len+1);
                while (num_beats != 0) begin
                  burst_len  = num_beats >= 256 ? 255 : num_beats - 1;
                  exp_aw    = '{
                    axi_id   : sbr_port_axi.aw_id   ,
                    axi_addr : burst_addr           ,
                    axi_len  : burst_len            ,
                    axi_burst: sbr_port_axi.aw_burst,
                    axi_size : MgrPortMaxSize       ,
                    axi_cache: sbr_port_axi.aw_cache
                  }                                                          ;
                  this.exp_mgr_port_aw_queue.push(sbr_port_axi.aw_id, exp_aw);
                  incr_expected_tests(6)                                     ;

                  num_beats  = num_beats - burst_len - 1                                                                  ;
                  burst_addr = axi_pkg::beat_addr(burst_addr, MgrPortMaxSize, burst_len, axi_pkg::BURST_INCR, burst_len+1);
                end;
              end
            end
          end
          // Passthrough downsize
          axi_pkg::BURST_FIXED: begin
            // Transaction unchanged
            if (conv_ratio(sbr_port_axi.aw_size, MgrPortMaxSize) == 1) begin
              exp_aw = '{
                axi_id   : sbr_port_axi.aw_id   ,
                axi_addr : sbr_port_axi.aw_addr ,
                axi_len  : sbr_port_axi.aw_len  ,
                axi_burst: sbr_port_axi.aw_burst,
                axi_size : sbr_port_axi.aw_size ,
                axi_cache: sbr_port_axi.aw_cache
              };

              this.exp_mgr_port_aw_queue.push(sbr_port_axi.aw_id, exp_aw);
              incr_expected_tests(6)                                     ;
            end
            // Split into manager_axi.aw_len + 1 INCR bursts
            else begin
              for (int unsigned j = 0; j <= sbr_port_axi.aw_len; j++) begin
                exp_aw.axi_id    = sbr_port_axi.aw_id   ;
                exp_aw.axi_addr  = sbr_port_axi.aw_addr ;
                exp_aw.axi_burst = axi_pkg::BURST_INCR  ;
                exp_aw.axi_size  = MgrPortMaxSize       ;
                exp_aw.axi_cache = sbr_port_axi.aw_cache;
                if (conv_ratio(sbr_port_axi.aw_size, MgrPortMaxSize) >= aligned_adjustment(sbr_port_axi.aw_addr, sbr_port_axi.aw_size) + 1)
                  exp_aw.axi_len = conv_ratio(sbr_port_axi.aw_size, MgrPortMaxSize) - aligned_adjustment(sbr_port_axi.aw_addr, sbr_port_axi.aw_size) - 1;
                else
                  exp_aw.axi_len = 0;

                this.exp_mgr_port_aw_queue.push(sbr_port_axi.aw_id, exp_aw);
                incr_expected_tests(6)                                     ;
              end
            end
          end
          // WRAP downsize
          axi_pkg::BURST_WRAP: begin
            exp_aw = '0;
            $warning("WRAP bursts are not supported.");
          end
        endcase

        $display("%0tns > Manager: AW with ID: %b",
          $time, sbr_port_axi.aw_id);

        // Populate the expected B queue
        this.exp_sbr_port_b_queue.push(sbr_port_axi.aw_id, '{
            axi_id  : sbr_port_axi.aw_id,
            axi_last: 1'b1
          })                                  ;
        incr_expected_tests(1)                ;
        $display("        Expect B response.");
      end
    endtask : mon_sbr_port_aw

    task automatic mon_sbr_port_w ();
      if (act_sbr_port_w_queue.size() != 0) begin
        exp_sbr_rw_t act_sbr_w = act_sbr_port_w_queue[0];

        if (act_mgr_port_aw_queue.size() != 0 && act_sbr_port_aw_queue.size() != 0) begin
          // Retrieve the AW requests related to this W beat
          exp_ax_t act_mgr_aw = act_mgr_port_aw_queue[0];
          exp_ax_t act_sbr_aw = act_sbr_port_aw_queue[0];

          // Address of the current beat
          axi_addr_t sbr_aw_addr = axi_pkg::beat_addr(act_sbr_aw.axi_addr, act_sbr_aw.axi_size, act_sbr_aw.axi_len, act_sbr_aw.axi_burst, sbr_port_w_cnt);

          // Calculate the offsets inside the incoming word
          shortint unsigned sbr_port_lower_byte =
          axi_pkg::beat_lower_byte(act_sbr_aw.axi_addr, act_sbr_aw.axi_size, act_sbr_aw.axi_len, act_sbr_aw.axi_burst, SbrPortStrbWidth, sbr_port_w_cnt);
          // Pointer inside the incoming word
          shortint unsigned sbr_port_data_pointer = sbr_port_lower_byte;

          // Several W beats generated from this incoming W beat
          int unsigned beat_cnt = conv_ratio(act_sbr_aw.axi_size, MgrPortMaxSize) - aligned_adjustment(sbr_aw_addr, act_sbr_aw.axi_size);

          for (int unsigned beat = 0; beat < beat_cnt; beat++) begin
            exp_mgr_rw_t act_mgr_w = '0;

            // Calculate the offsets inside the outcoming word
            shortint unsigned mgr_port_lower_byte =
            axi_pkg::beat_lower_byte(act_mgr_aw.axi_addr, act_mgr_aw.axi_size, act_mgr_aw.axi_len, act_mgr_aw.axi_burst, MgrPortStrbWidth, mgr_port_w_cnt);
            shortint unsigned mgr_port_upper_byte =
            axi_pkg::beat_upper_byte(act_mgr_aw.axi_addr, act_mgr_aw.axi_size, act_mgr_aw.axi_len, act_mgr_aw.axi_burst, MgrPortStrbWidth, mgr_port_w_cnt);

            shortint unsigned bytes_copied = 0;

            act_mgr_w.axi_id   = act_mgr_aw.axi_id                   ;
            act_mgr_w.axi_last = mgr_port_w_cnt == act_mgr_aw.axi_len;
            act_mgr_w.axi_data = '0                                  ;
            for (shortint unsigned b = sbr_port_data_pointer; b < SbrPortStrbWidth; b++) begin
              if (b + mgr_port_lower_byte - sbr_port_data_pointer == MgrPortStrbWidth)
                break;
              act_mgr_w.axi_data[8*(b + mgr_port_lower_byte - sbr_port_data_pointer) +: 8] = act_sbr_w.axi_data[8*b +: 8];
              act_mgr_w.axi_strb[b + mgr_port_lower_byte - sbr_port_data_pointer]          = act_sbr_w.axi_strb[b]       ;
              bytes_copied++;
            end
            // Don't care for the bits outside these accessed by this request
            for (int unsigned b = 0; b < MgrPortStrbWidth; b++)
              if (!(mgr_port_lower_byte <= b && b <= mgr_port_upper_byte))
                act_mgr_w.axi_data[8*b +: 8] = {8{1'b?}};

            this.exp_mgr_port_w_queue.push_back(act_mgr_w);
            incr_expected_tests(3)                        ;

            // Increment the len counters
            mgr_port_w_cnt++                     ;
            sbr_port_data_pointer += bytes_copied;

            // Used the whole W beat
            if (sbr_port_data_pointer == SbrPortStrbWidth)
              break;
          end

          // Increment the len counter
          sbr_port_w_cnt++;

          // Pop the AW request from the queues
          if (sbr_port_w_cnt == act_sbr_aw.axi_len + 1) begin
            void'(act_sbr_port_aw_queue.pop_front());
            sbr_port_w_cnt = 0;
          end
          if (mgr_port_w_cnt == act_mgr_aw.axi_len + 1) begin
            void'(act_mgr_port_aw_queue.pop_front());
            mgr_port_w_cnt = 0;
          end

          // Pop the W request
          void'(act_sbr_port_w_queue.pop_front());
        end
      end
    endtask: mon_sbr_port_w

    task automatic mon_sbr_port_ar ();
      exp_ax_t exp_sbr_ar;
      exp_b_t  exp_mgr_r;

      if (sbr_port_axi.ar_valid && sbr_port_axi.ar_ready) begin
        case (sbr_port_axi.ar_burst)
          axi_pkg::BURST_INCR: begin
            // Transaction unchanged
            if (conv_ratio(sbr_port_axi.ar_size, MgrPortMaxSize) == 1) begin
              exp_sbr_ar = '{
                axi_id   : sbr_port_axi.ar_id   ,
                axi_addr : sbr_port_axi.ar_addr ,
                axi_len  : sbr_port_axi.ar_len  ,
                axi_burst: sbr_port_axi.ar_burst,
                axi_size : sbr_port_axi.ar_size ,
                axi_cache: sbr_port_axi.ar_cache
              };

              this.exp_mgr_port_ar_queue.push(sbr_port_axi.ar_id, exp_sbr_ar);
              incr_expected_tests(6)                                         ;
            end
            // INCR downsize
            else begin
              automatic int unsigned num_beats = (sbr_port_axi.ar_len + 1) * conv_ratio(sbr_port_axi.ar_size, MgrPortMaxSize) - aligned_adjustment(sbr_port_axi.ar_addr, sbr_port_axi.ar_size);
              // One burst
              if (num_beats <= 256) begin
                exp_sbr_ar = '{
                  axi_id   : sbr_port_axi.ar_id   ,
                  axi_addr : sbr_port_axi.ar_addr ,
                  axi_len  : num_beats - 1        ,
                  axi_burst: sbr_port_axi.ar_burst,
                  axi_size : MgrPortMaxSize       ,
                  axi_cache: sbr_port_axi.ar_cache
                };

                this.exp_mgr_port_ar_queue.push(sbr_port_axi.ar_id, exp_sbr_ar);
                incr_expected_tests(6)                                         ;
              end
              // Need to split the incoming burst into several INCR bursts
              else begin
                automatic axi_addr_t burst_addr;
                automatic len_t burst_len      ;

                // First burst is a "partial" burst
                burst_len  = 255 - aligned_adjustment(sbr_port_axi.ar_addr, sbr_port_axi.ar_size);
                exp_sbr_ar = '{
                  axi_id   : sbr_port_axi.ar_id   ,
                  axi_addr : sbr_port_axi.ar_addr ,
                  axi_len  : burst_len            ,
                  axi_burst: sbr_port_axi.ar_burst,
                  axi_size : MgrPortMaxSize       ,
                  axi_cache: sbr_port_axi.ar_cache
                }                                                              ;
                this.exp_mgr_port_ar_queue.push(sbr_port_axi.ar_id, exp_sbr_ar);
                incr_expected_tests(6)                                         ;

                // Push the other bursts in a loop
                num_beats  = num_beats - burst_len - 1                                                                                                                   ;
                burst_addr = axi_pkg::beat_addr(axi_pkg::aligned_addr(sbr_port_axi.ar_addr, MgrPortMaxSize), MgrPortMaxSize, burst_len, axi_pkg::BURST_INCR, burst_len+1);
                while (num_beats != 0) begin
                  burst_len  = num_beats >= 256 ? 255 : num_beats - 1;
                  exp_sbr_ar = '{
                    axi_id   : sbr_port_axi.ar_id   ,
                    axi_addr : burst_addr           ,
                    axi_len  : burst_len            ,
                    axi_burst: sbr_port_axi.ar_burst,
                    axi_size : MgrPortMaxSize       ,
                    axi_cache: sbr_port_axi.ar_cache
                  }                                                              ;
                  this.exp_mgr_port_ar_queue.push(sbr_port_axi.ar_id, exp_sbr_ar);
                  incr_expected_tests(6)                                         ;

                  num_beats  = num_beats - burst_len - 1                                                                  ;
                  burst_addr = axi_pkg::beat_addr(burst_addr, MgrPortMaxSize, burst_len, axi_pkg::BURST_INCR, burst_len+1);
                end;
              end
            end
          end
          // Passthrough downsize
          axi_pkg::BURST_FIXED: begin
            // Transaction unchanged
            if (conv_ratio(sbr_port_axi.ar_size, MgrPortMaxSize) == 1) begin
              exp_sbr_ar = '{
                axi_id   : sbr_port_axi.ar_id   ,
                axi_addr : sbr_port_axi.ar_addr ,
                axi_len  : sbr_port_axi.ar_len  ,
                axi_burst: sbr_port_axi.ar_burst,
                axi_size : sbr_port_axi.ar_size ,
                axi_cache: sbr_port_axi.ar_cache
              };

              this.exp_mgr_port_ar_queue.push(sbr_port_axi.ar_id, exp_sbr_ar);
              incr_expected_tests(6)                                         ;
            end
            // Split into manager_axi.ar_len + 1 INCR bursts
            else begin
              for (int unsigned j = 0; j <= sbr_port_axi.ar_len; j++) begin
                exp_sbr_ar.axi_id    = sbr_port_axi.ar_id   ;
                exp_sbr_ar.axi_addr  = sbr_port_axi.ar_addr ;
                exp_sbr_ar.axi_burst = axi_pkg::BURST_INCR  ;
                exp_sbr_ar.axi_size  = MgrPortMaxSize       ;
                exp_sbr_ar.axi_cache = sbr_port_axi.ar_cache;
                if (conv_ratio(sbr_port_axi.ar_size, MgrPortMaxSize) >= aligned_adjustment(sbr_port_axi.ar_addr, sbr_port_axi.ar_size) + 1)
                  exp_sbr_ar.axi_len = conv_ratio(sbr_port_axi.ar_size, MgrPortMaxSize) - aligned_adjustment(sbr_port_axi.ar_addr, sbr_port_axi.ar_size) - 1;
                else
                  exp_sbr_ar.axi_len = 0;

                this.exp_mgr_port_ar_queue.push(sbr_port_axi.ar_id, exp_sbr_ar);
                incr_expected_tests(6)                                         ;
              end
            end
          end
          // WRAP downsize
          axi_pkg::BURST_WRAP: begin
            exp_sbr_ar = '0;
            $warning("WRAP bursts are not supported.");
          end
        endcase

        $display("%0tns > Manager: AR with ID: %b",
          $time, sbr_port_axi.ar_id);
      end
    endtask : mon_sbr_port_ar

    virtual task automatic mon_mgr_port_r();
      if (mgr_port_axi.r_valid && mgr_port_axi.r_ready) begin
        // Retrieve the AR requests related to this R beat
        exp_ax_t act_mgr_ar = act_mgr_port_ar_queue.get(mgr_port_axi.r_id);
        exp_ax_t act_sbr_ar = act_sbr_port_ar_queue.get(mgr_port_axi.r_id);
        axi_id_t id         = mgr_port_axi.r_id                           ;

        // Calculate the offsets
        shortint unsigned mgr_port_lower_byte =
        axi_pkg::beat_lower_byte(act_mgr_ar.axi_addr, act_mgr_ar.axi_size, act_mgr_ar.axi_len, act_mgr_ar.axi_burst, MgrPortStrbWidth, mgr_port_r_cnt[id]);
        shortint unsigned mgr_port_upper_byte =
        axi_pkg::beat_upper_byte(act_mgr_ar.axi_addr, act_mgr_ar.axi_size, act_mgr_ar.axi_len, act_mgr_ar.axi_burst, MgrPortStrbWidth, mgr_port_r_cnt[id]);
        shortint unsigned sbr_port_lower_byte =
        axi_pkg::beat_lower_byte(act_sbr_ar.axi_addr, act_sbr_ar.axi_size, act_sbr_ar.axi_len, act_sbr_ar.axi_burst, SbrPortStrbWidth, sbr_port_r_cnt[id]);
        shortint unsigned sbr_port_upper_byte =
        axi_pkg::beat_upper_byte(act_sbr_ar.axi_addr, act_sbr_ar.axi_size, act_sbr_ar.axi_len, act_sbr_ar.axi_burst, SbrPortStrbWidth, sbr_port_r_cnt[id]);

        // Pointer inside the outcoming word
        shortint unsigned bytes_copied = 0;
        if (sbr_port_r_pnt[id] == '1)
          sbr_port_r_pnt[id] = sbr_port_lower_byte;

        sbr_port_r[id].axi_id   = id                                      ;
        sbr_port_r[id].axi_last = sbr_port_r_cnt[id] == act_sbr_ar.axi_len;
        for (shortint unsigned b = mgr_port_lower_byte; b <= mgr_port_upper_byte; b++) begin
          if (b + sbr_port_r_pnt[id] - mgr_port_lower_byte == SbrPortStrbWidth)
            break;
          sbr_port_r[id].axi_data[8*(b + sbr_port_r_pnt[id] - mgr_port_lower_byte) +: 8] = mgr_port_axi.r_data[8*b +: 8];
          bytes_copied++;
        end

        // Increment the len counters
        mgr_port_r_cnt[id]++              ;
        sbr_port_r_pnt[id] += bytes_copied;

        if (sbr_port_r_pnt[id] == sbr_port_upper_byte + 1                // Used all bits from the incoming R beat
            || sbr_port_r_pnt[id] == SbrPortStrbWidth                    // Filled up an outcoming R beat
            || conv_ratio(act_sbr_ar.axi_size, act_mgr_ar.axi_size) == 1 // Not downsizing
            || mgr_port_axi.r_last                                       // Last beat of an R burst
          ) begin
          // Don't care for the bits outside these accessed by this request
          for (int unsigned b = 0; b < SbrPortStrbWidth; b++)
            if (!(sbr_port_lower_byte <= b && b <= sbr_port_upper_byte))
              sbr_port_r[id].axi_data[8*b +: 8] = {8{1'b?}};

          this.exp_sbr_port_r_queue.push(id, sbr_port_r[id]);
          incr_expected_tests(3)                            ;

          // Increment the len counter
          sbr_port_r_cnt[id]++;

          // Reset R beat
          sbr_port_r[id]     = '0;
          sbr_port_r_pnt[id] = '1;
        end

        // Pop the AW request from the queues
        if (sbr_port_r_cnt[id] == act_sbr_ar.axi_len + 1) begin
          void'(act_sbr_port_ar_queue.pop_id(id));
          sbr_port_r_cnt[id] = 0;
        end
        if (mgr_port_r_cnt[id] == act_mgr_ar.axi_len + 1) begin
          void'(act_mgr_port_ar_queue.pop_id(id));
          mgr_port_r_cnt[id] = 0;
        end
      end
    endtask : mon_mgr_port_r
  endclass : axi_dw_downsizer_monitor

endpackage: tb_axi_dw_pkg
