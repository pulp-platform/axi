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
// for the AXI Data Width Converters. It snoops on the slave and master port
// of the DWCs and populates FIFOs and ID queues to validate that no
// AXI beats get lost.

package tb_axi_dw_pkg    ;
  import axi_pkg::len_t  ;
  import axi_pkg::burst_t;
  import axi_pkg::size_t ;

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

    typedef logic [AxiIdWidth-1:0] axi_id_t    ;
    typedef logic [AxiAddrWidth-1:0] axi_addr_t;

    typedef logic [AxiSlvPortDataWidth-1:0] slv_port_data_t;
    typedef logic [AxiSlvPortStrbWidth-1:0] slv_port_strb_t;
    typedef logic [AxiMstPortDataWidth-1:0] mst_port_data_t;
    typedef logic [AxiMstPortStrbWidth-1:0] mst_port_strb_t;

    typedef struct packed {
      axi_id_t axi_id;
      logic axi_last ;
    } exp_b_t;
    typedef struct packed {
      axi_id_t axi_id         ;
      slv_port_data_t axi_data;
      slv_port_strb_t axi_strb;
      logic axi_last          ;
    } exp_rw_t;
    typedef struct packed {
      axi_id_t axi_id    ;
      axi_addr_t axi_addr;
      len_t axi_len      ;
      burst_t axi_burst  ;
      size_t axi_size    ;
    } exp_ax_t;

    typedef rand_id_queue_pkg::rand_id_queue #(
      .data_t  (exp_ax_t  ),
      .ID_WIDTH(AxiIdWidth)
    ) ax_queue_t;
    typedef rand_id_queue_pkg::rand_id_queue #(
      .data_t  (exp_b_t   ),
      .ID_WIDTH(AxiIdWidth)
    ) b_queue_t;
    typedef rand_id_queue_pkg::rand_id_queue #(
      .data_t  (exp_rw_t  ),
      .ID_WIDTH(AxiIdWidth)
    ) r_queue_t;

    /**********************
     *  Helper functions  *
     **********************/

    // Returns a byte mask corresponding to the size of the AXI transaction
    function automatic axi_addr_t size_mask(axi_pkg::size_t size);
      return (axi_addr_t'(1) << size) - 1;
    endfunction

    /************************
     *  Virtual Interfaces  *
     ************************/

    virtual AXI_BUS_DV #(
      .AXI_ADDR_WIDTH(AxiAddrWidth       ),
      .AXI_DATA_WIDTH(AxiSlvPortDataWidth),
      .AXI_ID_WIDTH  (AxiIdWidth         ),
      .AXI_USER_WIDTH(AxiUserWidth       )
    ) slv_port_axi;
    virtual AXI_BUS_DV #(
      .AXI_ADDR_WIDTH(AxiAddrWidth       ),
      .AXI_DATA_WIDTH(AxiMstPortDataWidth),
      .AXI_ID_WIDTH  (AxiIdWidth         ),
      .AXI_USER_WIDTH(AxiUserWidth       )
    ) mst_port_axi;

    /*****************
     *  Bookkeeping  *
     *****************/

    longint unsigned tests_expected;
    longint unsigned tests_conducted;
    longint unsigned tests_failed;
    semaphore        cnt_sem;

    // Queues and FIFOs to hold the expected AXIDs

    // Write transactions
    ax_queue_t exp_mst_port_aw_queue;
    exp_ax_t   act_mst_port_aw_queue [$];
    exp_ax_t   act_slv_port_aw_queue [$];
    exp_rw_t   exp_mst_port_w_queue [$];
    exp_rw_t   act_mst_port_w_queue [$];
    exp_rw_t   act_slv_port_w_queue [$];
    b_queue_t  exp_slv_port_b_queue;

    // Read transactions
    ax_queue_t exp_mst_port_ar_queue;
    ax_queue_t act_mst_port_ar_queue;
    ax_queue_t act_slv_port_ar_queue;
    r_queue_t  exp_slv_port_r_queue;

    /*****************
     *  Constructor  *
     *****************/

    function new (
        virtual AXI_BUS_DV #(
          .AXI_ADDR_WIDTH(AxiAddrWidth       ),
          .AXI_DATA_WIDTH(AxiSlvPortDataWidth),
          .AXI_ID_WIDTH  (AxiIdWidth         ),
          .AXI_USER_WIDTH(AxiUserWidth       )
        ) slv_port_vif,
        virtual AXI_BUS_DV #(
          .AXI_ADDR_WIDTH(AxiAddrWidth       ),
          .AXI_DATA_WIDTH(AxiMstPortDataWidth),
          .AXI_ID_WIDTH  (AxiIdWidth         ),
          .AXI_USER_WIDTH(AxiUserWidth       )
        ) mst_port_vif
      );
      begin
        this.slv_port_axi          = slv_port_vif;
        this.mst_port_axi          = mst_port_vif;
        this.tests_expected        = 0           ;
        this.tests_conducted       = 0           ;
        this.tests_failed          = 0           ;
        this.exp_slv_port_b_queue  = new         ;
        this.exp_slv_port_r_queue  = new         ;
        this.exp_mst_port_aw_queue = new         ;
        this.exp_mst_port_ar_queue = new         ;
        this.act_mst_port_ar_queue = new         ;
        this.act_slv_port_ar_queue = new         ;
        this.cnt_sem               = new(1)      ;
      end
    endfunction

    task cycle_start;
      #TimeTest;
    endtask: cycle_start

    task cycle_end;
      @(posedge slv_port_axi.clk_i);
    endtask: cycle_end

    /**************
     *  Monitors  *
     **************/

    /*
     * You need to override this task. Use it to push the expected AW requests on
     * the slave side, and the B and R responses expected on the master side.
     */
    virtual task automatic mon_slv_port_aw ()    ;
      $error("This task needs to be overridden.");
    endtask : mon_slv_port_aw

    /*
     * You need to override this task. Use it to push the expected W requests on
     * the slave side.
     *
     * The `act_mst_port_aw_queue` and `act_slv_port_aw_queue` contain the AW
     * requests on the Master and Slave port.
     */
    virtual task automatic mon_slv_port_w ()     ;
      $error("This task needs to be overridden.");
    endtask : mon_slv_port_w

    /*
     * You need to override this task. Use it to push the expected AR requests on
     * the slave side, and the R responses expected on the master side.
     */
    virtual task automatic mon_slv_port_ar ()    ;
      $error("This task needs to be overridden.");
    endtask : mon_slv_port_ar

    /*
     * This tasks stores the beats seen by the AR, AW and W channels
     * into the respective queues.
     */
    virtual task automatic store_channels ();
      if (slv_port_axi.ar_valid && slv_port_axi.ar_ready)
        act_slv_port_ar_queue.push(slv_port_axi.ar_id,
          '{
            axi_id   : slv_port_axi.ar_id   ,
            axi_burst: slv_port_axi.ar_burst,
            axi_size : slv_port_axi.ar_size ,
            axi_addr : slv_port_axi.ar_addr ,
            axi_len  : slv_port_axi.ar_len
          });

      if (slv_port_axi.aw_valid && slv_port_axi.aw_ready)
        act_slv_port_aw_queue.push_back('{
            axi_id   : slv_port_axi.aw_id   ,
            axi_burst: slv_port_axi.aw_burst,
            axi_size : slv_port_axi.aw_size ,
            axi_addr : slv_port_axi.aw_addr ,
            axi_len  : slv_port_axi.aw_len
          });

      if (slv_port_axi.w_valid && slv_port_axi.w_ready)
        this.act_slv_port_w_queue.push_back('{
            axi_id  : {AxiIdWidth{1'b?}} ,
            axi_data: slv_port_axi.w_data,
            axi_strb: slv_port_axi.w_strb,
            axi_last: slv_port_axi.w_last
          });

      if (mst_port_axi.ar_valid && mst_port_axi.ar_ready)
        act_mst_port_ar_queue.push(mst_port_axi.ar_id,
          '{
            axi_id   : mst_port_axi.ar_id   ,
            axi_burst: mst_port_axi.ar_burst,
            axi_size : mst_port_axi.ar_size ,
            axi_addr : mst_port_axi.ar_addr ,
            axi_len  : mst_port_axi.ar_len
          });

      if (mst_port_axi.aw_valid && mst_port_axi.aw_ready)
        act_mst_port_aw_queue.push_back('{
            axi_id   : mst_port_axi.aw_id   ,
            axi_burst: mst_port_axi.aw_burst,
            axi_size : mst_port_axi.aw_size ,
            axi_addr : mst_port_axi.aw_addr ,
            axi_len  : mst_port_axi.aw_len
          });

      if (mst_port_axi.w_valid && mst_port_axi.w_ready)
        this.act_mst_port_w_queue.push_back('{
            axi_id  : {AxiIdWidth{1'b?}} ,
            axi_data: mst_port_axi.w_data,
            axi_strb: mst_port_axi.w_strb,
            axi_last: mst_port_axi.w_last
          });
    endtask

    /*
     * This task monitors the master port of the DW converter. Every time it gets an AW transaction,
     * it gets checked for its contents against the expected beat on the `exp_aw_queue`.
     */
    task automatic mon_mst_port_aw ();
      exp_ax_t exp_aw;
      if (mst_port_axi.aw_valid && mst_port_axi.aw_ready) begin
        // Test if the AW beat was expected
        exp_aw = this.exp_mst_port_aw_queue.pop_id(mst_port_axi.aw_id);
        if (exp_aw.axi_id != mst_port_axi.aw_id) begin
          incr_failed_tests(1)                                            ;
          $warning("Slave: Unexpected AW with ID: %b", mst_port_axi.aw_id);
        end
        if (exp_aw.axi_addr != mst_port_axi.aw_addr) begin
          incr_failed_tests(1);
          $warning("Slave: Unexpected AW with ID: %b and ADDR: %h, exp: %h",
            mst_port_axi.aw_id, mst_port_axi.aw_addr, exp_aw.axi_addr);
        end
        if (exp_aw.axi_len != mst_port_axi.aw_len) begin
          incr_failed_tests(1);
          $warning("Slave: Unexpected AW with ID: %b and LEN: %h, exp: %h",
            mst_port_axi.aw_id, mst_port_axi.aw_len, exp_aw.axi_len);
        end
        if (exp_aw.axi_burst != mst_port_axi.aw_burst) begin
          incr_failed_tests(1);
          $warning("Slave: Unexpected AW with ID: %b and BURST: %h, exp: %h",
            mst_port_axi.aw_id, mst_port_axi.aw_burst, exp_aw.axi_burst);
        end
        if (exp_aw.axi_size != mst_port_axi.aw_size) begin
          incr_failed_tests(1);
          $warning("Slave: Unexpected AW with ID: %b and SIZE: %h, exp: %h",
            mst_port_axi.aw_id, mst_port_axi.aw_size, exp_aw.axi_size);
        end
        incr_conducted_tests(5);
      end
    endtask : mon_mst_port_aw

    /*
     * This task compares the expected and actual W beats on the master port.
     */
    task automatic mon_mst_port_w ();
      exp_rw_t exp_w, act_w;
      while (this.exp_mst_port_w_queue.size() != 0 && this.act_mst_port_w_queue.size() != 0) begin
        exp_w = this.exp_mst_port_w_queue.pop_front();
        act_w = this.act_mst_port_w_queue.pop_front();
        // Do the checks
        if (exp_w.axi_data != act_w.axi_data) begin
          incr_failed_tests(1);
          $warning("Slave: Unexpected W with DATA: %h, exp: %h",
            act_w.axi_data, exp_w.axi_data);
        end
        if (exp_w.axi_strb != act_w.axi_strb) begin
          incr_failed_tests(1);
          $warning("Slave: Unexpected W with STRB: %h, exp: %h",
            act_w.axi_strb, exp_w.axi_strb);
        end
        if (exp_w.axi_last != act_w.axi_last) begin
          incr_failed_tests(1);
          $warning("Slave: Unexpected W with LAST: %b, exp: %b",
            act_w.axi_last, exp_w.axi_last);
        end
        incr_conducted_tests(3);
      end
    endtask : mon_mst_port_w

    /*
     * This task checks if a B response is allowed on a slave port of the DW converter.
     */
    task automatic mon_slv_port_b ();
      exp_b_t  exp_b;
      axi_id_t axi_b_id;
      if (slv_port_axi.b_valid && slv_port_axi.b_ready) begin
        incr_conducted_tests(1);
        axi_b_id = slv_port_axi.b_id;
        $display("%0tns > Master: Got last B with ID: %b",
          $time, axi_b_id);
        if (this.exp_slv_port_b_queue.empty()) begin
          incr_failed_tests(1)                                                 ;
          $warning("Master: unexpected B beat with ID: %b detected!", axi_b_id);
        end else begin
          exp_b = this.exp_slv_port_b_queue.pop_id(axi_b_id);
          if (axi_b_id != exp_b.axi_id) begin
            incr_failed_tests(1)                                      ;
            $warning("Master: got unexpected B with ID: %b", axi_b_id);
          end
        end
      end
    endtask : mon_slv_port_b

    /*
     * This task monitors a the master port of the DW converter and checks
     * if the AR beats were all expected.
     */
    task automatic mon_mst_port_ar ();
      exp_ax_t exp_ar;
      if (mst_port_axi.ar_valid && mst_port_axi.ar_ready) begin
        // Test if the AR beat was expected
        exp_ar = this.exp_mst_port_ar_queue.pop_id(mst_port_axi.ar_id);
        if (exp_ar.axi_id != mst_port_axi.ar_id) begin
          incr_failed_tests(1)                                            ;
          $warning("Slave: Unexpected AR with ID: %b", mst_port_axi.ar_id);
        end
        if (exp_ar.axi_addr != mst_port_axi.ar_addr) begin
          incr_failed_tests(1);
          $warning("Slave: Unexpected AR with ID: %b and ADDR: %h, exp: %h",
            mst_port_axi.ar_id, mst_port_axi.ar_addr, exp_ar.axi_addr);
        end
        if (exp_ar.axi_len != mst_port_axi.ar_len) begin
          incr_failed_tests(1);
          $warning("Slave: Unexpected AR with ID: %b and LEN: %h, exp: %h",
            mst_port_axi.ar_id, mst_port_axi.ar_len, exp_ar.axi_len);
        end
        if (exp_ar.axi_burst != mst_port_axi.ar_burst) begin
          incr_failed_tests(1);
          $warning("Slave: Unexpected AR with ID: %b and BURST: %h, exp: %h",
            mst_port_axi.ar_id, mst_port_axi.ar_burst, exp_ar.axi_burst);
        end
        if (exp_ar.axi_size != mst_port_axi.ar_size) begin
          incr_failed_tests(1);
          $warning("Slave: Unexpected AR with ID: %b and SIZE: %h, exp: %h",
            mst_port_axi.ar_id, mst_port_axi.ar_size, exp_ar.axi_size);
        end
        incr_conducted_tests(5);
      end
    endtask : mon_mst_port_ar

    /*
     * This task does the R channel monitoring on a slave port. It compares the last flags,
     * which are determined by the sequence of previously sent AR vectors.
     */
    task automatic mon_slv_port_r ();
      exp_rw_t exp_r;
      if (slv_port_axi.r_valid && slv_port_axi.r_ready) begin
        exp_r = this.exp_slv_port_r_queue.pop_id(slv_port_axi.r_id);
        // Do the checks
        if (exp_r.axi_id != slv_port_axi.r_id) begin
          incr_failed_tests(1);
          $warning("Slave: Unexpected R with ID: %b",
            slv_port_axi.r_id);
        end
        if (exp_r.axi_last != slv_port_axi.r_last) begin
          incr_failed_tests(1);
          $warning("Slave: Unexpected R with ID: %b and LAST: %b, exp: %b",
            slv_port_axi.r_id, slv_port_axi.r_last, exp_r.axi_last);
        end
        if (exp_r.axi_data != slv_port_axi.r_data) begin
          incr_failed_tests(1);
          $warning("Slave: Unexpected R with ID: %b and DATA: %h, exp: %h",
            slv_port_axi.r_id, slv_port_axi.r_data, exp_r.axi_data);
        end
        incr_conducted_tests(3);
      end
    endtask : mon_slv_port_r

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
          proc_mst_aw       : mon_slv_port_aw();
          proc_mst_ar       : mon_slv_port_ar();
          proc_mst_w        : mon_slv_port_w() ;
          proc_store_channel: store_channels() ;
        join: PushMon

        // These only pop something from the queues
        PopMon: fork
          proc_slv_aw: mon_mst_port_aw();
          proc_mst_b : mon_slv_port_b() ;
          proc_slv_ar: mon_mst_port_ar();
          proc_mst_r : mon_slv_port_r() ;
        join : PopMon

        // Check the slave W FIFOs last
        proc_check_slv_w: mon_mst_port_w();

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
        ) slv_port_vif,
        virtual AXI_BUS_DV #(
          .AXI_ADDR_WIDTH(AxiAddrWidth       ),
          .AXI_DATA_WIDTH(AxiMstPortDataWidth),
          .AXI_ID_WIDTH  (AxiIdWidth         ),
          .AXI_USER_WIDTH(AxiUserWidth       )
        ) mst_port_vif
      );
      begin
        super.new(slv_port_vif, mst_port_vif);
      end
    endfunction

    /**************
     *  Monitors  *
     **************/

    task automatic mon_slv_port_aw ();
      exp_ax_t exp_aw;

      if (slv_port_axi.aw_valid && slv_port_axi.aw_ready) begin
        // Non-modifiable transaction
        if (!axi_pkg::modifiable(slv_port_axi.aw_cache)) begin
          // We expect that the transaction will not be modified
          exp_aw = '{
            axi_id   : slv_port_axi.aw_id   ,
            axi_addr : slv_port_axi.aw_addr ,
            axi_len  : slv_port_axi.aw_len  ,
            axi_burst: slv_port_axi.aw_burst,
            axi_size : slv_port_axi.aw_size
          } ;
        end
        // Modifiable transaction
        else begin
          case (slv_port_axi.aw_burst)
            // Passthrough upsize
            axi_pkg::BURST_FIXED: begin
              exp_aw = '{
                axi_id   : slv_port_axi.aw_id   ,
                axi_addr : slv_port_axi.aw_addr ,
                axi_len  : slv_port_axi.aw_len  ,
                axi_burst: slv_port_axi.aw_burst,
                axi_size : slv_port_axi.aw_size
              };
            end
            // INCR upsize
            axi_pkg::BURST_INCR: begin
              automatic axi_addr_t aligned_start = axi_pkg::aligned_addr(slv_port_axi.aw_addr, AxiMstPortMaxSize)                                                                                                        ;
              automatic axi_addr_t aligned_end   = axi_pkg::aligned_addr(axi_pkg::aligned_addr(slv_port_axi.aw_addr, slv_port_axi.aw_size) + (unsigned'(slv_port_axi.aw_len) << slv_port_axi.aw_size), AxiMstPortMaxSize);

              exp_aw = '{
                axi_id   : slv_port_axi.aw_id                                ,
                axi_addr : slv_port_axi.aw_addr                              ,
                axi_len  : (aligned_end - aligned_start) >> AxiMstPortMaxSize,
                axi_burst: slv_port_axi.aw_burst                             ,
                axi_size : AxiMstPortMaxSize
              };
            end
            // WRAP upsize
            axi_pkg::BURST_WRAP: begin
              exp_aw = '0;
              $warning("WRAP bursts are not supported.");
            end
          endcase
          this.exp_mst_port_aw_queue.push(slv_port_axi.aw_id, exp_aw);
          incr_expected_tests(5)                                     ;
          $display("%0tns > Master: AW with ID: %b",
            $time, slv_port_axi.aw_id);
        end

        // Populate the expected B responses
        this.exp_slv_port_b_queue.push(slv_port_axi.aw_id, '{
            axi_id  : slv_port_axi.aw_id,
            axi_last: 1'b1
          })                                   ;
        incr_expected_tests(1)                 ;
        $display("        Expect B response.") ;
      end
    endtask : mon_slv_port_aw

    task automatic mon_slv_port_ar ();
      exp_ax_t exp_slv_ar;
      exp_b_t  exp_mst_r;

      if (slv_port_axi.ar_valid && slv_port_axi.ar_ready) begin
        // Non-modifiable transaction
        if (!axi_pkg::modifiable(slv_port_axi.ar_cache)) begin
          // We expect that the transaction will not be modified
          exp_slv_ar = '{
            axi_id   : slv_port_axi.ar_id   ,
            axi_addr : slv_port_axi.ar_addr ,
            axi_len  : slv_port_axi.ar_len  ,
            axi_burst: slv_port_axi.ar_burst,
            axi_size : slv_port_axi.ar_size
          };
        end
        // Modifiable transaction
        else begin
          case (slv_port_axi.ar_burst)
            // Passthrough upsize
            axi_pkg::BURST_FIXED: begin
              exp_slv_ar = '{
                axi_id   : slv_port_axi.ar_id   ,
                axi_addr : slv_port_axi.ar_addr ,
                axi_len  : slv_port_axi.ar_len  ,
                axi_burst: slv_port_axi.ar_burst,
                axi_size : slv_port_axi.ar_size
              };
            end
            // INCR upsize
            axi_pkg::BURST_INCR: begin
              automatic axi_addr_t aligned_start = axi_pkg::aligned_addr(slv_port_axi.ar_addr, AxiMstPortMaxSize)                                                                                                        ;
              automatic axi_addr_t aligned_end   = axi_pkg::aligned_addr(axi_pkg::aligned_addr(slv_port_axi.ar_addr, slv_port_axi.ar_size) + (unsigned'(slv_port_axi.ar_len) << slv_port_axi.ar_size), AxiMstPortMaxSize);

              exp_slv_ar = '{
                axi_id   : slv_port_axi.ar_id                                ,
                axi_addr : slv_port_axi.ar_addr                              ,
                axi_len  : (aligned_end - aligned_start) >> AxiMstPortMaxSize,
                axi_burst: slv_port_axi.ar_burst                             ,
                axi_size : AxiMstPortMaxSize
              };
            end
            // WRAP upsize
            axi_pkg::BURST_WRAP: begin
              exp_slv_ar = '0;
              $warning("WRAP bursts are not supported.");
            end
          endcase
          this.exp_mst_port_ar_queue.push(slv_port_axi.ar_id, exp_slv_ar);
          incr_expected_tests(5)                                         ;
          $display("%0tns > Master: AR with ID: %b",
            $time, slv_port_axi.ar_id);
        end
      end
    endtask : mon_slv_port_ar
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

    local static shortint unsigned slv_port_w_cnt;
    local static shortint unsigned mst_port_w_cnt;

    /**********************
     *  Helper functions  *
     **********************/

    /**
     * Returns the downsize ratio between the incoming AXI transaction and the outcoming
     * transaction of axsize AxiMstPortMaxSize.
     * @return ceil(num_bytes(size)/num_bytes(AxiMstPortMaxSize))
     */
    function automatic int unsigned downsize_ratio(axi_pkg::size_t size)                                                 ;
      return (axi_pkg::num_bytes(size) + axi_pkg::num_bytes(AxiMstPortMaxSize) - 1)/axi_pkg::num_bytes(AxiMstPortMaxSize);
    endfunction: downsize_ratio

    /*
     * Returns how many beats of the incoming AXI transaction will be dropped after downsizing
     * due to an unaligned memory address.
     */
    function automatic len_t aligned_adjustment(axi_addr_t addr, axi_pkg::size_t size)                     ;
      return (addr & size_mask(size) & ~size_mask(AxiMstPortMaxSize))/axi_pkg::num_bytes(AxiMstPortMaxSize);
    endfunction: aligned_adjustment

    /*****************
     *  Constructor  *
     *****************/

    function new (
        virtual AXI_BUS_DV #(
          .AXI_ADDR_WIDTH(AxiAddrWidth       ),
          .AXI_DATA_WIDTH(AxiSlvPortDataWidth),
          .AXI_ID_WIDTH  (AxiIdWidth         ),
          .AXI_USER_WIDTH(AxiUserWidth       )
        ) slv_port_vif,
        virtual AXI_BUS_DV #(
          .AXI_ADDR_WIDTH(AxiAddrWidth       ),
          .AXI_DATA_WIDTH(AxiMstPortDataWidth),
          .AXI_ID_WIDTH  (AxiIdWidth         ),
          .AXI_USER_WIDTH(AxiUserWidth       )
        ) mst_port_vif
      );
      begin
        super.new(slv_port_vif, mst_port_vif);

        slv_port_w_cnt = 0;
        mst_port_w_cnt = 0;
      end
    endfunction

    /**************
     *  Monitors  *
     **************/

    task automatic mon_slv_port_aw ();
      exp_ax_t exp_aw;

      if (slv_port_axi.aw_valid && slv_port_axi.aw_ready) begin
        case (slv_port_axi.aw_burst)
          axi_pkg::BURST_INCR: begin
            // Transaction unchanged
            if (downsize_ratio(slv_port_axi.aw_size) == 1) begin
              exp_aw = '{
                axi_id   : slv_port_axi.aw_id   ,
                axi_addr : slv_port_axi.aw_addr ,
                axi_len  : slv_port_axi.aw_len  ,
                axi_burst: slv_port_axi.aw_burst,
                axi_size : slv_port_axi.aw_size
              };

              this.exp_mst_port_aw_queue.push(slv_port_axi.aw_id, exp_aw);
              incr_expected_tests(5)                                     ;
            end
            // INCR downsize
            else begin
              automatic int unsigned num_beats = (slv_port_axi.aw_len + 1) * downsize_ratio(slv_port_axi.aw_size) - aligned_adjustment(slv_port_axi.aw_addr, slv_port_axi.aw_size);
              // One burst
              if (num_beats <= 256) begin
                exp_aw = '{
                  axi_id   : slv_port_axi.aw_id   ,
                  axi_addr : slv_port_axi.aw_addr ,
                  axi_len  : num_beats - 1        ,
                  axi_burst: slv_port_axi.aw_burst,
                  axi_size : AxiMstPortMaxSize
                };

                this.exp_mst_port_aw_queue.push(slv_port_axi.aw_id, exp_aw);
                incr_expected_tests(5)                                     ;
              end
              // Need to split the incoming burst into several INCR bursts
              else begin
                automatic axi_addr_t burst_addr;
                automatic len_t burst_len      ;

                // First burst is a "partial" burst
                burst_len = 255 - aligned_adjustment(slv_port_axi.aw_addr, slv_port_axi.aw_size);
                exp_aw    = '{
                  axi_id   : slv_port_axi.aw_id   ,
                  axi_addr : slv_port_axi.aw_addr ,
                  axi_len  : burst_len            ,
                  axi_burst: slv_port_axi.aw_burst,
                  axi_size : AxiMstPortMaxSize
                }                                                          ;
                this.exp_mst_port_aw_queue.push(slv_port_axi.aw_id, exp_aw);
                incr_expected_tests(5)                                     ;

                // Push the other bursts in a loop
                num_beats  = num_beats - burst_len - 1                                                                   ;
                burst_addr = axi_pkg::beat_addr(burst_addr, AxiMstPortMaxSize, burst_len, axi_pkg::BURST_INCR, burst_len);
                while (num_beats != 0) begin
                  burst_len = (num_beats - 1) % 256;
                  exp_aw    = '{
                    axi_id   : slv_port_axi.aw_id   ,
                    axi_addr : burst_addr           ,
                    axi_len  : burst_len            ,
                    axi_burst: slv_port_axi.aw_burst,
                    axi_size : AxiMstPortMaxSize
                  }                                                          ;
                  this.exp_mst_port_aw_queue.push(slv_port_axi.aw_id, exp_aw);
                  incr_expected_tests(5)                                     ;

                  num_beats  = num_beats - burst_len - 1                                                                   ;
                  burst_addr = axi_pkg::beat_addr(burst_addr, AxiMstPortMaxSize, burst_len, axi_pkg::BURST_INCR, burst_len);
                end;
              end
            end
          end
          // Passthrough downsize
          axi_pkg::BURST_FIXED: begin
            // Transaction unchanged
            if (downsize_ratio(slv_port_axi.aw_size) == 1) begin
              exp_aw = '{
                axi_id   : slv_port_axi.aw_id   ,
                axi_addr : slv_port_axi.aw_addr ,
                axi_len  : slv_port_axi.aw_len  ,
                axi_burst: slv_port_axi.aw_burst,
                axi_size : slv_port_axi.aw_size
              };

              this.exp_mst_port_aw_queue.push(slv_port_axi.aw_id, exp_aw);
              incr_expected_tests(5)                                     ;
            end
            // Split into master_axi.aw_len + 1 INCR bursts
            else begin
              for (int unsigned j = 0; j <= slv_port_axi.aw_len; j++) begin
                exp_aw.axi_id    = slv_port_axi.aw_id  ;
                exp_aw.axi_addr  = slv_port_axi.aw_addr;
                exp_aw.axi_burst = axi_pkg::BURST_INCR ;
                exp_aw.axi_size  = AxiMstPortMaxSize   ;
                if (downsize_ratio(slv_port_axi.aw_size) >= aligned_adjustment(slv_port_axi.aw_addr, slv_port_axi.aw_size) + 1)
                  exp_aw.axi_len = downsize_ratio(slv_port_axi.aw_size) - aligned_adjustment(slv_port_axi.aw_addr, slv_port_axi.aw_size) - 1;
                else
                  exp_aw.axi_len = 0;

                this.exp_mst_port_aw_queue.push(slv_port_axi.aw_id, exp_aw);
                incr_expected_tests(5)                                     ;
              end
            end
          end
          // WRAP downsize
          axi_pkg::BURST_WRAP: begin
            exp_aw = '0;
            $warning("WRAP bursts are not supported.");
          end
        endcase

        $display("%0tns > Master: AW with ID: %b",
          $time, slv_port_axi.aw_id);

        // Populate the expected B queue
        this.exp_slv_port_b_queue.push(slv_port_axi.aw_id, '{
            axi_id  : slv_port_axi.aw_id,
            axi_last: 1'b1
          })                                  ;
        incr_expected_tests(1)                ;
        $display("        Expect B response.");
      end
    endtask : mon_slv_port_aw

    task automatic mon_slv_port_w ();
      if (act_slv_port_w_queue.size() != 0) begin
        exp_rw_t act_slv_w = act_slv_port_w_queue[0];

        if (act_mst_port_aw_queue.size() != 0 && act_slv_port_aw_queue.size() != 0) begin
          // Retrieve the AW requests related to this W beat
          exp_ax_t act_mst_aw = act_mst_port_aw_queue[0];
          exp_ax_t act_slv_aw = act_slv_port_aw_queue[0];

          // Calculate the offsets inside the incoming word
          shortint unsigned slv_port_lower_byte =
          axi_pkg::beat_lower_byte(act_slv_aw.axi_addr, act_slv_aw.axi_size, act_slv_aw.axi_len, act_slv_aw.axi_burst, AxiSlvPortStrbWidth, slv_port_w_cnt);
          // Pointer inside the incoming word
          shortint unsigned slv_port_data_pointer = slv_port_lower_byte;

          // Several W beats generated from this incoming W beat
          for (int unsigned beat = 0; beat < downsize_ratio(act_slv_aw.axi_size); beat++) begin
            exp_rw_t act_mst_w = '0;

            // Calculate the offsets inside the outcoming word
            shortint unsigned mst_port_lower_byte =
            axi_pkg::beat_lower_byte(act_mst_aw.axi_addr, act_mst_aw.axi_size, act_mst_aw.axi_len, act_mst_aw.axi_burst, AxiMstPortStrbWidth, mst_port_w_cnt);
            shortint unsigned mst_port_upper_byte =
            axi_pkg::beat_upper_byte(act_mst_aw.axi_addr, act_mst_aw.axi_size, act_mst_aw.axi_len, act_mst_aw.axi_burst, AxiMstPortStrbWidth, mst_port_w_cnt);

            shortint unsigned bytes_copied = 0;

            act_mst_w.axi_id   = act_mst_aw.axi_id                   ;
            act_mst_w.axi_last = mst_port_w_cnt == act_mst_aw.axi_len;
            act_mst_w.axi_data = {AxiMstPortDataWidth{1'b?}}         ;
            for (shortint unsigned b = slv_port_data_pointer; b < AxiSlvPortStrbWidth; b++) begin
              if (b + mst_port_lower_byte - slv_port_data_pointer == AxiMstPortStrbWidth)
                break;
              act_mst_w.axi_data[8*(b + mst_port_lower_byte - slv_port_data_pointer) +: 8] = act_slv_w.axi_strb[b] ? act_slv_w.axi_data[8*b +: 8] : {8{1'b?}};
              act_mst_w.axi_strb[b + mst_port_lower_byte - slv_port_data_pointer]          = act_slv_w.axi_strb[b];
              bytes_copied++ ;
            end
            this.exp_mst_port_w_queue.push_back(act_mst_w);
            incr_expected_tests(3)                        ;

            // Increment the len counters
            mst_port_w_cnt++                                   ;
            slv_port_data_pointer += bytes_copied              ;

            // Used the whole W beat
            if (slv_port_data_pointer == AxiSlvPortStrbWidth)
              break;
          end

          // Increment the len counter
          slv_port_w_cnt++;

          // Pop the AW request from the queues
          if (slv_port_w_cnt == act_slv_aw.axi_len + 1) begin
            void'(act_slv_port_aw_queue.pop_front());
            slv_port_w_cnt = 0;
          end
          if (mst_port_w_cnt == act_mst_aw.axi_len + 1) begin
            void'(act_mst_port_aw_queue.pop_front());
            mst_port_w_cnt = 0;
          end

          // Pop the W request
          void'(act_slv_port_w_queue.pop_front());
        end
      end
    endtask: mon_slv_port_w

    task automatic mon_slv_port_ar ();
      exp_ax_t exp_slv_ar;
      exp_b_t  exp_mst_r;

      if (slv_port_axi.ar_valid && slv_port_axi.ar_ready) begin
        case (slv_port_axi.ar_burst)
          axi_pkg::BURST_INCR: begin
            // Transaction unchanged
            if (downsize_ratio(slv_port_axi.ar_size) == 1) begin
              exp_slv_ar = '{
                axi_id   : slv_port_axi.ar_id   ,
                axi_addr : slv_port_axi.ar_addr ,
                axi_len  : slv_port_axi.ar_len  ,
                axi_burst: slv_port_axi.ar_burst,
                axi_size : slv_port_axi.ar_size
              };

              this.exp_mst_port_ar_queue.push(slv_port_axi.ar_id, exp_slv_ar);
              incr_expected_tests(5)                                         ;
            end
            // INCR downsize
            else begin
              automatic int unsigned num_beats = (slv_port_axi.ar_len + 1) * downsize_ratio(slv_port_axi.ar_size) - aligned_adjustment(slv_port_axi.ar_addr, slv_port_axi.ar_size);
              // One burst
              if (num_beats <= 256) begin
                exp_slv_ar = '{
                  axi_id   : slv_port_axi.ar_id   ,
                  axi_addr : slv_port_axi.ar_addr ,
                  axi_len  : num_beats - 1        ,
                  axi_burst: slv_port_axi.ar_burst,
                  axi_size : AxiMstPortMaxSize
                };

                this.exp_mst_port_ar_queue.push(slv_port_axi.ar_id, exp_slv_ar);
                incr_expected_tests(5)                                         ;
              end
              // Need to split the incoming burst into several INCR bursts
              else begin
                automatic axi_addr_t burst_addr;
                automatic len_t burst_len      ;

                // First burst is a "partial" burst
                burst_len  = 255 - aligned_adjustment(slv_port_axi.ar_addr, slv_port_axi.ar_size);
                exp_slv_ar = '{
                  axi_id   : slv_port_axi.ar_id   ,
                  axi_addr : slv_port_axi.ar_addr ,
                  axi_len  : burst_len            ,
                  axi_burst: slv_port_axi.ar_burst,
                  axi_size : AxiMstPortMaxSize
                }                                                              ;
                this.exp_mst_port_ar_queue.push(slv_port_axi.ar_id, exp_slv_ar);
                incr_expected_tests(5)                                         ;

                // Push the other bursts in a loop
                num_beats  = num_beats - burst_len - 1                                                                   ;
                burst_addr = axi_pkg::beat_addr(burst_addr, AxiMstPortMaxSize, burst_len, axi_pkg::BURST_INCR, burst_len);
                while (num_beats != 0) begin
                  burst_len  = (num_beats - 1) % 256;
                  exp_slv_ar = '{
                    axi_id   : slv_port_axi.ar_id   ,
                    axi_addr : burst_addr           ,
                    axi_len  : burst_len            ,
                    axi_burst: slv_port_axi.ar_burst,
                    axi_size : AxiMstPortMaxSize
                  }                                                              ;
                  this.exp_mst_port_ar_queue.push(slv_port_axi.ar_id, exp_slv_ar);
                  incr_expected_tests(5)                                         ;

                  num_beats  = num_beats - burst_len - 1                                                                   ;
                  burst_addr = axi_pkg::beat_addr(burst_addr, AxiMstPortMaxSize, burst_len, axi_pkg::BURST_INCR, burst_len);
                end;
              end
            end
          end
          // Passthrough downsize
          axi_pkg::BURST_FIXED: begin
            // Transaction unchanged
            if (downsize_ratio(slv_port_axi.ar_size) == 1) begin
              exp_slv_ar = '{
                axi_id   : slv_port_axi.ar_id   ,
                axi_addr : slv_port_axi.ar_addr ,
                axi_len  : slv_port_axi.ar_len  ,
                axi_burst: slv_port_axi.ar_burst,
                axi_size : slv_port_axi.ar_size
              };

              this.exp_mst_port_ar_queue.push(slv_port_axi.ar_id, exp_slv_ar);
              incr_expected_tests(5)                                         ;
            end
            // Split into master_axi.ar_len + 1 INCR bursts
            else begin
              for (int unsigned j = 0; j <= slv_port_axi.ar_len; j++) begin
                exp_slv_ar.axi_id    = slv_port_axi.aw_id  ;
                exp_slv_ar.axi_addr  = slv_port_axi.aw_addr;
                exp_slv_ar.axi_burst = axi_pkg::BURST_INCR ;
                exp_slv_ar.axi_size  = AxiMstPortMaxSize   ;
                if (downsize_ratio(slv_port_axi.ar_size) >= aligned_adjustment(slv_port_axi.ar_addr, slv_port_axi.ar_size) + 1)
                  exp_slv_ar.axi_len = downsize_ratio(slv_port_axi.ar_size) - aligned_adjustment(slv_port_axi.ar_addr, slv_port_axi.ar_size) - 1;
                else
                  exp_slv_ar.axi_len = 0;

                this.exp_mst_port_ar_queue.push(slv_port_axi.ar_id, exp_slv_ar);
                incr_expected_tests(5)                                         ;
              end
            end
          end
          // WRAP downsize
          axi_pkg::BURST_WRAP: begin
            exp_slv_ar = '0;
            $warning("WRAP bursts are not supported.");
          end
        endcase

        $display("%0tns > Master: AR with ID: %b",
          $time, slv_port_axi.ar_id);
      end
    endtask : mon_slv_port_ar
  endclass : axi_dw_downsizer_monitor

endpackage: tb_axi_dw_pkg
