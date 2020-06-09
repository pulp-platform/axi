// Copyright (c) 2019 ETH Zurich, University of Bologna
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
// File:   aw_splitter.sv
// Author: Wolfgang Roenninger <wroennin@student.ethz.ch>
// Date:   03.05.2019
//
// Description: Provides Testbench configuration utility for the `tb_axi_llc`.
//
//
//
// virtual monitor interface for the monitor class
import axi_pkg::*;

`include "axi/typedef.svh"

package llc_axi;
  // Axi4 IdWidth specification
  // 4 is recommended by AXI standard, so lets stick to it, do not change
  localparam IdWidth                 =  6;
  localparam IdWidthSlave            =  IdWidth;    // IdWidth of the slave bus from CPU
  localparam IdWidthMaster           =  IdWidth + 1;    // IdWidth of the master bus to memory
  localparam AddrWidth               =  64;    // Axi Address Width
  localparam DataWidth               =  64;    // Axi Data Width
  localparam StrbWidth               =  DataWidth / 8;
  localparam DataWidthLite           =  32;    // Axi Lite Data Width (must be either 32-bit or 64-bit per spec, but only 64 bit for components requiring 64-bit atomic access, what the cfg not is --> always leave this at 32-bit!)
  localparam StrbWidthLite           =  DataWidthLite / 8;
  localparam UserWidth               =  1;

  typedef logic [IdWidth-1:0]       id_t;
  typedef logic [IdWidthMaster-1:0] id_mst_t;
  typedef logic [IdWidthSlave-1:0]  id_slv_t;
  typedef logic [AddrWidth-1:0]     addr_t;
  typedef logic [DataWidth-1:0]     data_t;
  typedef logic [StrbWidth-1:0]     strb_t;
  typedef logic [DataWidthLite-1:0] data_lite_t;
  typedef logic [StrbWidthLite-1:0] strb_lite_t;
  typedef logic [UserWidth-1:0]     user_t;

  `AXI_TYPEDEF_AW_CHAN_T ( aw_chan_t,     addr_t,         id_t,             user_t )
  `AXI_TYPEDEF_AW_CHAN_T ( aw_chan_mst_t, addr_t,         id_mst_t,         user_t )
  `AXI_TYPEDEF_AW_CHAN_T ( aw_chan_slv_t, addr_t,         id_slv_t,         user_t )
  `AXI_TYPEDEF_W_CHAN_T  (  w_chan_t,             data_t,           strb_t, user_t )
  `AXI_TYPEDEF_B_CHAN_T  (  b_chan_t,                     id_t,             user_t )
  `AXI_TYPEDEF_B_CHAN_T  (  b_chan_mst_t,                 id_mst_t,         user_t )
  `AXI_TYPEDEF_B_CHAN_T  (  b_chan_slv_t,                 id_slv_t,         user_t )
  `AXI_TYPEDEF_AR_CHAN_T ( ar_chan_t,     addr_t,         id_t,             user_t )
  `AXI_TYPEDEF_AR_CHAN_T ( ar_chan_mst_t, addr_t,         id_mst_t,         user_t )
  `AXI_TYPEDEF_AR_CHAN_T ( ar_chan_slv_t, addr_t,         id_slv_t,         user_t )
  `AXI_TYPEDEF_R_CHAN_T  (  r_chan_t,             data_t, id_t,             user_t )
  `AXI_TYPEDEF_R_CHAN_T  (  r_chan_mst_t,         data_t, id_mst_t,         user_t )
  `AXI_TYPEDEF_R_CHAN_T  (  r_chan_slv_t,         data_t, id_slv_t,         user_t )

  `AXI_TYPEDEF_REQ_T  (  req_t, aw_chan_t, w_chan_t, ar_chan_t )
  `AXI_TYPEDEF_RESP_T ( resp_t,  b_chan_t, r_chan_t            )
  `AXI_TYPEDEF_REQ_T  (  req_mst_t, aw_chan_mst_t,  w_chan_t,       ar_chan_mst_t )
  `AXI_TYPEDEF_RESP_T ( resp_mst_t,  b_chan_mst_t,  r_chan_mst_t                  )
  `AXI_TYPEDEF_REQ_T  (  req_slv_t, aw_chan_slv_t,  w_chan_t,       ar_chan_slv_t )
  `AXI_TYPEDEF_RESP_T ( resp_slv_t,  b_chan_slv_t,  r_chan_slv_t                  )

  // AXI4 Lite
  `AXI_LITE_TYPEDEF_AW_CHAN_T ( aw_chan_lite_t, addr_t                   )
  `AXI_LITE_TYPEDEF_W_CHAN_T  (  w_chan_lite_t, data_lite_t, strb_lite_t )
  `AXI_LITE_TYPEDEF_B_CHAN_T  (  b_chan_lite_t                           )
  `AXI_LITE_TYPEDEF_AR_CHAN_T ( ar_chan_lite_t, addr_t                   )
  `AXI_LITE_TYPEDEF_R_CHAN_T  (  r_chan_lite_t, data_lite_t              )
  `AXI_LITE_TYPEDEF_REQ_T  (  req_lite_t, aw_chan_lite_t, w_chan_lite_t, ar_chan_lite_t )
  `AXI_LITE_TYPEDEF_RESP_T ( resp_lite_t,  b_chan_lite_t, r_chan_lite_t                 )
endpackage

interface AXI_MONITOR_INTF (
  input logic clk_i, rst_ni,
  input llc_axi::req_slv_t   req_slv,
  input llc_axi::resp_slv_t  resp_slv,
  input end_sim
);
endinterface

package tb_axi_llc_pkg;

  // timing characteristics
  localparam time clockPeriod   = 100ns;
  localparam time appliSkew     = 20ns;
  localparam time aquisSkew     = 20ns;

  // how long the reset is active
  localparam int rstCycles = 5;

  // how big is the main memory
  localparam int numWords  = 2**18;

  // how many axi Ids can there be
  localparam longint nbSlaveIds = 2**llc_axi::IdWidthSlave;

  // Error count threshold
  localparam int errCntThresh = 10;

  // -------------------------------------------
  // Progress class
  // -------------------------------------------
  // this class beepd book of the progress and counts encountered errors
  class progress;
    longint numResp, acqCnt, errCnt, totAcqCnt, totErrCnt;
    string  name;

    // constructor
    function new(string name);
      begin
        this.name       = name;
        this.acqCnt     = 0;
        this.errCnt     = 0;
        this.numResp    = 0;
        this.totAcqCnt  = 0;
        this.totErrCnt  = 0;
      end
    endfunction : new

    function void reset(longint numResp_);
      begin
        this.acqCnt   = 0;
        this.errCnt   = 0;
        this.numResp  = numResp_;
      end
    endfunction : reset

    function void addRes(int isError);
      begin
        this.acqCnt++;
        this.totAcqCnt++;
        this.errCnt     += isError;
        this.totErrCnt  += isError;
        // stop if error threshold is reached
        if ( this.errCnt >= errCntThresh && errCntThresh > 0 ) begin
          $error("%s> simulation stoppend (Error Threshold = %d reached).",
              this.name, errCntThresh);
          $stop();
        end
      end
    endfunction : addRes

    function void printToFile(string file, bit summary = 0);
      begin
        int fptr;

        // sanitize string
        for(fptr=0; fptr<$size(file);fptr++) begin
          if(file[fptr] == " " || file[fptr] == "/" || file[fptr] == "\\") begin
            file[fptr] = "_";
          end
        end

        fptr = $fopen(file,"w");
        if(summary) begin
          $fdisplay(fptr, "Simulation Summary of %s", this.name);
          $fdisplay(fptr, "total: %01d of %01d vectors failed (%03.3f%%) ",
                    this.totErrCnt,
                    this.totAcqCnt,
                    $itor(this.totErrCnt) / ($itor(this.totAcqCnt) * 100.0 + 0.000000001));
          if(this.totErrCnt == 0) begin
            $fdisplay(fptr, "CI: PASSED");
          end else begin
            $fdisplay(fptr, "CI: FAILED");
          end
        end else begin
          $fdisplay(fptr, "test name: %s", file);
          $fdisplay(fptr, "this test: %01d of %01d vectors failed (%03.3f%%) ",
                    this.errCnt,
                    this.acqCnt,
                    $itor(this.errCnt) / $itor(this.acqCnt) * 100.0);

          $fdisplay(fptr, "total so far: %01d of %01d vectors failed (%03.3f%%) ",
                    this.totErrCnt,
                    this.totAcqCnt,
                    $itor(this.totErrCnt) / $itor(this.totAcqCnt) * 100.0);
        end
        $fclose(fptr);
      end
    endfunction : printToFile
  endclass : progress

  // -------------------------------------------
  // Monitor class
  // monitors the axi channel and checks the expected responses of the LLC
  // -------------------------------------------
  // This class has two memories, one representing the CPU view of the main memory
  // the other representing the backing memory.
  // This class serves as the main memory for the LLC. Each time a read or write request
  // gets issued to the LLC, both memories get initialized with random data, if no request was
  // previously made onto that particular memory location. On write data transfers the respective
  // memories get updated. On appropriate requests or evictions of the cache, the content gets
  // cross checked between the two memories.
  class axi_llc_monitor #(
    parameter int  AW       ,
    parameter int  DW       ,
    parameter int  IW       ,
    parameter int  UW       ,
    parameter time TA = 0ns , // stimuli application time
    parameter time TT = 0ns   // stimuli test time
    );

    // create virtual interface handle
    // interface for master from cpu
    virtual AXI_MONITOR_INTF vif;

    typedef axi_test::axi_driver #(
      .AW(AW), .DW(DW), .IW(IW), .UW(UW), .TA(TA), .TT(TT)
    ) axi_driver_t;
    typedef rand_id_queue_pkg::rand_id_queue #(
      .data_t   (axi_driver_t::ax_beat_t),
      .ID_WIDTH (IW)
    ) rand_ax_beat_queue_t;
    typedef rand_id_queue_pkg::rand_id_queue #(
      .data_t   (axi_driver_t::r_beat_t),
      .ID_WIDTH (IW)
    ) r_beat_queue_t;
    typedef axi_driver_t::ax_beat_t ax_beat_t;
    typedef axi_driver_t::w_beat_t w_beat_t;
    typedef axi_driver_t::b_beat_t b_beat_t;
    typedef axi_driver_t::r_beat_t r_beat_t;

    // slave driver (Main memory)
    axi_driver_t slv_drv;

    // variables
    string  name;                                      // name of the instantiated class
    llc_axi::addr_t spm_mem_base;                      // base of the main memory
    llc_axi::addr_t spm_mem_range;                     // range of the main memory
    // bookkeeping
    tb_axi_llc_pkg::progress progress;                 // progress class
    // modeled memory (Word addressed!)
    llc_axi::data_t cpu_mem_array[llc_axi::addr_t];    // cpu_view of the memory
    llc_axi::data_t bak_mem_array[llc_axi::addr_t];    // main memory

    // fifos for the expected transactions (monitoring)
    // W / B channel
    llc_axi::addr_t       w_addr_fifo[$];
    llc_axi::w_chan_t     w_beat_fifo[$];
    llc_axi::b_chan_slv_t b_beat_fifo[$];
    // fifos for the expected transactions
    // R channel
    llc_axi::addr_t       r_addr_fifo[nbSlaveIds][$];
    llc_axi::r_chan_slv_t r_beat_fifo[nbSlaveIds][$];

    // slave driver queues
    rand_ax_beat_queue_t b_queue;
    ax_beat_t            aw_queue[$];
    w_beat_t             w_queue[$];
    llc_axi::addr_t      w_mem_addr_queue[$];
    r_beat_queue_t       r_beat_queue;

    // constructor
    function new(
      string          name,
      llc_axi::addr_t spm_mem_base,
      llc_axi::addr_t spm_mem_range,
      virtual AXI_MONITOR_INTF axi_monitor_intf,
      virtual AXI_BUS_DV #(
        .AXI_ADDR_WIDTH(AW),
        .AXI_DATA_WIDTH(DW),
        .AXI_ID_WIDTH  (IW),
        .AXI_USER_WIDTH(UW)
      ) axi
    );
      begin
        // get the interface
        this.vif           = axi_monitor_intf;
        this.slv_drv       = new(axi);
        this.name          = name;
        this.spm_mem_base  = spm_mem_base;
        this.spm_mem_range = spm_mem_range;
        this.progress      = new("monitor_progress");
        this.b_queue       = new;
        this.r_beat_queue  = new;
        this.reset();
      end
    endfunction : new

    function void reset();
      slv_drv.reset_slave();
    endfunction : reset

    // when start the testing
    task cycle_start;
      #TT;
    endtask

    // when is cyckle finished
    task cycle_end;
      @(posedge vif.clk_i);
    endtask

    // listens on the aw channel and pushes the bursts into fifos
    task monitor_aw;
      automatic logic                 rand_success;
      automatic llc_axi::addr_t       w_beat_addr;
      automatic llc_axi::addr_t       word;
      automatic llc_axi::data_t       init_data;
      automatic llc_axi::w_chan_t     w_chan_beat;
      automatic llc_axi::b_chan_slv_t b_chan_beat;
      automatic llc_axi::addr_t       base_addr;    // base addr to inititalyte the whole line
      longint cnt;
      do begin
        cycle_start();
        // we have a transaction on the AW channel --> populate the fifos
        if ( vif.req_slv.aw_valid && vif.resp_slv.aw_ready ) begin
          //$display("%s> Pushing AW with id: %d into queues.", this.name, vif.req_slv.aw.id);
          //$display($time());
          // push the required w channel beats into the fifo
          w_beat_addr = vif.req_slv.aw.addr;
          for (int i = vif.req_slv.aw.len; i >= 0; i--) begin
            //$display("%s> push %d",this.name, i);
            w_chan_beat = '0;
            this.w_addr_fifo.push_back(w_beat_addr);
            // look, if the index in the mem arrays exists, if not initialyse it with random data
            word = w_beat_addr >> 3;
            if (!this.cpu_mem_array.exists(word) && !this.bak_mem_array.exists(word)) begin
              // initialyse to unkown, if it is an spm sccess
              if ((w_beat_addr >= this.spm_mem_base) &&
                  (w_beat_addr < (this.spm_mem_base + this.spm_mem_range))) begin
                init_data = 'X;
              // normal mem access, initialyze random
              end else begin
                rand_success = std::randomize(init_data); assert(rand_success);
              end
              this.cpu_mem_array[word] = init_data;
              this.bak_mem_array[word] = init_data;
              // initialyze all words around for non spm it also if they do not exist,
              // because the refill will fetch more around it!
              if ((w_beat_addr >= (this.spm_mem_base + this.spm_mem_range)) ||
                  (w_beat_addr < this.spm_mem_base)) begin
                // $display("%h",word);
                base_addr = word >> 3;
                base_addr = base_addr << 3;
                // $display("%h",base_addr);
                for (int j = 0; j < 8; j++) begin
                  rand_success = std::randomize(init_data); assert(rand_success);
                  // $display(j);
                  // $display("%h",j);
                  // $display("%h", word+j);
                  if (!this.cpu_mem_array.exists(base_addr+j)) begin
                    // $display("Wrote Data");
                    this.cpu_mem_array[base_addr+j] = init_data;
                  end
                  if (!this.bak_mem_array.exists(base_addr+j)) begin
                    // $display("Wrote bak data");
                    this.bak_mem_array[base_addr+j] = init_data;
                  end
                end
              end
            end else if ((this.cpu_mem_array.exists(word) && !this.bak_mem_array.exists(word)) ||
                        (!this.cpu_mem_array.exists(word) && this.bak_mem_array.exists(word))) begin
              $fatal("only one of the mem arrays is initialyzed");
            end

            // populate the beat fifo
            if ( i == 0 ) begin
              // last beat in w channel
              w_chan_beat.last = 1'b1;
            end else begin
              // all other beats update address
              unique case (vif.req_slv.aw.burst)
                axi_pkg::BURST_FIXED : begin
                  // Nothing, address stays the same
                end
                axi_pkg::BURST_INCR  : begin
                  w_beat_addr = w_beat_addr + 2**vif.req_slv.aw.size;
                end
                axi_pkg::BURST_WRAP  : begin
                  $error("Not supported wrapping burst at this time.");
                end
                default : $fatal(1, "Not exisiting Axi Burst detected.");
              endcase
            end
            this.w_beat_fifo.push_back(w_chan_beat);
          end
          // push one b response into the fifo
          b_chan_beat.id   = vif.req_slv.aw.id;
          b_chan_beat.resp = axi_pkg::RESP_OKAY;
          b_beat_fifo.push_back(b_chan_beat);
        end
        cycle_end();
      end while ( !vif.end_sim );
    endtask : monitor_aw

    // listens on the w channel and pops the w beats and buts them into the memory array
    task monitor_w;
      automatic llc_axi::addr_t     w_beat_addr;
      automatic llc_axi::w_chan_t   w_chan_beat;
      automatic llc_axi::data_t     temp_data;
      do begin
        cycle_start();
        // we have a transaction on the W channel --> pop fifo and write memory
        if ( vif.req_slv.w_valid && vif.resp_slv.w_ready ) begin
          w_beat_addr = this.w_addr_fifo.pop_front();
          // pop the address and the expected beat
          // word addressed
          w_beat_addr = w_beat_addr >> 3;
          //$display("%s> W beat to LLC, updating memory at: %016X", this.name, w_beat_addr<<3);
          w_chan_beat = w_beat_fifo.pop_front();
          assert ( vif.req_slv.w.last == w_chan_beat.last ) else
            $fatal(1, "%s> Last signals in monitor and LLC Bus do not match.\n\
                       Expected: %b \nObserved: %b",
                this.name, w_chan_beat.last, vif.req_slv.w.last);
          // write the data into the memory array bytewise over the temp variable
          temp_data = this.cpu_mem_array[w_beat_addr];
          //$display("Old value: %016X", temp_data);
          for (int i = 0; i < llc_axi::DataWidth/8; i++) begin
            if ( vif.req_slv.w.strb[i] ) begin
              temp_data[8*i+:8] = vif.req_slv.w.data[8*i+:8];
            end
          end
          //$display("New value: %016X", temp_data);
          cycle_end();
          // push the data at the clock edge into the memory array
          this.cpu_mem_array[w_beat_addr] = temp_data;
        end else begin
          cycle_end();
        end
      end while ( !vif.end_sim );
    endtask : monitor_w

    // listens on the b channel and pops the b beats
    task monitor_b;
      automatic llc_axi::b_chan_slv_t b_chan_beat;
      do begin
        cycle_start();
        // we have a transaction on the b channel
        if ( vif.resp_slv.b_valid && vif.req_slv.b_ready ) begin
          //$display("%s> B beat from LLC", this.name);
          // pop expected b channel and compare
          b_chan_beat = b_beat_fifo.pop_front();
          assert ( b_chan_beat.id == vif.resp_slv.b.id ) else
            $fatal(1, "%s> Expected B response has anoter ID than wa observed.\n\
                       Expected: %d \nChannel:  %d", this.name, b_chan_beat.id, vif.resp_slv.b.id);
          if (vif.resp_slv.b.resp != axi_pkg::RESP_OKAY) begin
            $error("%s> LLC did respond with the Error condition: %d",
                this.name, vif.resp_slv.b.resp);
          end
        end
        cycle_end();
      end while ( !vif.end_sim );
    endtask : monitor_b

    // listens on the A channel and checks the recieved beats against the memory state
    task monitor_ar;
      automatic logic                 rand_success;
      automatic llc_axi::addr_t       r_beat_addr;
      automatic llc_axi::addr_t       word;
      automatic llc_axi::data_t       init_data;
      automatic llc_axi::r_chan_slv_t r_chan_beat;
      automatic llc_axi::id_slv_t     r_id;
      automatic llc_axi::addr_t       base_addr;    // base addr to inititalyte the whole line
      do begin
        cycle_start();
        // we have a transaction on the ar channel --> populate the fifo with the right ID
        if ( vif.req_slv.ar_valid && vif.resp_slv.ar_ready ) begin
          //$display("%s> Detected Read request with ID: %d", this.name, vif.req_slv.ar.id);
          r_beat_addr = vif.req_slv.ar.addr;
          r_id        = vif.req_slv.ar.id;
          for (int i = vif.req_slv.ar.len; i >= 0; i--) begin
            r_chan_beat = '0;
            r_chan_beat.id = r_id;
            r_addr_fifo[r_id].push_back(r_beat_addr);

            // look, if the index in the mem arrays exists, if not initialyse it with random data
            word = r_beat_addr >> 3;
            if (!this.cpu_mem_array.exists(word) && !this.bak_mem_array.exists(word)) begin
              // initialyse to unkown, if it is an spm sccess
              if ((r_beat_addr >= this.spm_mem_base) &&
                  (r_beat_addr < (this.spm_mem_base + this.spm_mem_range))) begin
                init_data = 'X;
              // normal mem access, initialyze random
              end else begin
                rand_success = std::randomize(init_data); assert(rand_success);
              end
              this.cpu_mem_array[word] = init_data;
              this.bak_mem_array[word] = init_data;
              // initialyze all words around for non spm it also if they do not exist,
              // because the refill will fetch more around it!
              if ((r_beat_addr >= (this.spm_mem_base + this.spm_mem_range)) ||
                  (r_beat_addr < this.spm_mem_base)) begin
                base_addr = word >> 3;
                base_addr = base_addr << 3;
                for (int j = 0; j < 8; j++) begin
                  rand_success = std::randomize(init_data); assert(rand_success);
                  //$display(j);
                  //$display("%h", word+j);
                  if (!this.cpu_mem_array.exists(base_addr+j)) begin
                    //$display("Wrote data");
                    this.cpu_mem_array[base_addr+j] = init_data;
                  end
                  if (!this.bak_mem_array.exists(base_addr+j)) begin
                    //$display("Wrote bak Data");
                    this.bak_mem_array[base_addr+j] = init_data;
                  end
                end
              end
            end else if ((this.cpu_mem_array.exists(word) && !this.bak_mem_array.exists(word)) ||
                        (!this.cpu_mem_array.exists(word) && this.bak_mem_array.exists(word))) begin
              $fatal("only one of the mem arrays is initialyzed");
            end

            if ( i == 0 ) begin
              // last beat in w channel
              r_chan_beat.last = 1'b1;
            end else begin
              // all other beats update address
              unique case (vif.req_slv.ar.burst)
                axi_pkg::BURST_FIXED : begin
                  // Nothing, address stays the same
                end
                axi_pkg::BURST_INCR  : begin
                  r_beat_addr = r_beat_addr + 2**vif.req_slv.ar.size;
                end
                axi_pkg::BURST_WRAP  : begin
                  $error("Not supported wrapping burst at this time.");
                end
                default : $fatal(1, "Not exisiting Axi Burst detected.");
              endcase
            end
            r_beat_fifo[r_id].push_back(r_chan_beat);
          end
          // debug
          //$display("%s> Read Address FIFO", this.name);
          //$display("%p", this.r_addr_fifo);
          //$display("%S> Write Address FIFO", this.name);
          //$display("%p", this.r_beat_fifo);
        end
        cycle_end();
      end while (!vif.end_sim);
    endtask : monitor_ar

    // listens on the R channel and compares the sent beats against the expected ones in its memory
    task monitor_r;
      automatic llc_axi::addr_t       r_beat_addr;
      automatic llc_axi::r_chan_slv_t r_chan_beat;
      automatic llc_axi::id_slv_t     r_id;
      automatic bit                   ok;
      do begin
        cycle_start();
        // transaction on the r channel --> pop fifo and compare against expected in memory
        if (vif.resp_slv.r_valid && vif.req_slv.r_ready) begin
          //$display("%s> Detected Read beat with ID: %d", this.name, vif.resp_slv.r.id);
          r_id        = vif.resp_slv.r.id;
          r_beat_addr = this.r_addr_fifo[r_id].pop_front();
          // word addressing
          r_beat_addr = r_beat_addr >> 3;
          //$display("Word Addr: %016X",r_beat_addr<<3);
          r_chan_beat = this.r_beat_fifo[r_id].pop_front();
          // assert the last bit
          assert (vif.resp_slv.r.last === r_chan_beat.last) else
            $fatal(1, "%s> Last signals in monitor and LLC R Chan do not match.\n\
                       Expected: %b \nObserved: %b",
                       this.name, r_chan_beat.last, vif.resp_slv.r.last);
          // assert the id match
          assert (r_id === r_chan_beat.id) else
            $fatal(1, "%s> R channel ID is something else than expected.\n\
                       Expected: %b \nObserved: %b", this.name, r_chan_beat.id, r_id);
          // compare the observed date against the one in out array
          if (!this.cpu_mem_array.exists(r_beat_addr)) begin
            $info("The memory location: %h does not exist", r_beat_addr);
          end
          ok = (this.cpu_mem_array[r_beat_addr] === vif.resp_slv.r.data);
          // error
          if( !ok ) begin
            $error("%s> Read missmatch of received and expected response:\n\
                    Address:  %016X \nWord:     %016X\nBlock:    %016X\nINDEX:    %016X\n\
                    TAG:      %016X\nRecieved: %016X \nExpected: %016X ",
                this.name, r_beat_addr<<3, r_beat_addr, r_beat_addr[2:0], r_beat_addr[12:3],
                r_beat_addr[63:13], vif.resp_slv.r.data, this.cpu_mem_array[r_beat_addr]);
          end else begin
            //$display("Address: %016X \n Recieved: %016X \n Expected: %016X ",
            //    r_beat_addr<<3, vif.resp_slv.r.data, cpu_mem_array[r_beat_addr]);
          end
          this.progress.addRes(!ok);
        end
        cycle_end();
      end while (!vif.end_sim);
    endtask : monitor_r

    ///////////////////////////////////////////////////////////////////////////////
    // Memory Slave
    ///////////////////////////////////////////////////////////////////////////////
    task automatic rand_wait(input int unsigned min, max);
      int unsigned rand_success , cycles;
      rand_success = std::randomize(cycles) with {
        cycles >= min;
        cycles <= max;
      };
      assert (rand_success) else $error("Failed to randomize wait cycles!");
      repeat (cycles) @(posedge this.slv_drv.axi.clk_i);
    endtask : rand_wait

    // these tasks are the slave main memory
    task recv_aws();
      do begin
        automatic ax_beat_t aw_beat;
        //automatic w_beat_t  w_beat = new;
        automatic llc_axi::addr_t     w_beat_addr;

        rand_wait(0, 10);
        this.slv_drv.recv_aw(aw_beat);
        //$display("Got AW Refill vector");
        //print_aw_beat(aw_beat);

        this.aw_queue.push_back(aw_beat);
        w_beat_addr = aw_beat.ax_addr;
        // push the accessed addresses into the fifo
        for (int i = aw_beat.ax_len; i >= 0; i--) begin
          automatic llc_axi::addr_t word;         // word address
          automatic w_beat_t        w_beat = new;

          this.w_mem_addr_queue.push_back(w_beat_addr);
          word = w_beat_addr >> 3;
          // make the expected w beats --> look in cpu mem for data
          if (this.cpu_mem_array.exists(word)) begin
            w_beat.w_data = this.cpu_mem_array[word];
          end else begin
            $fatal("Detected Eviction onto memory that was not initialyzed from cpu!!!");
          end
          w_beat.w_strb = '1; // we are the mem slave, the llc always sends on the whole bus width
          w_beat.w_last = 1'b0;
          w_beat.w_user = '0;

          // populate the beat fifo
          if ( i == 0 ) begin
            // last beat in w channel
            w_beat.w_last = 1'b1;
          end else begin
            // all other beats update address
            unique case (aw_beat.ax_burst)
              axi_pkg::BURST_FIXED : begin
                // Nothing, address stays the same
              end
              axi_pkg::BURST_INCR  : begin
                w_beat_addr = w_beat_addr + 2**aw_beat.ax_size;
              end
              axi_pkg::BURST_WRAP  : begin
                $error("Not supported wrapping burst at this time.");
              end
              default : $fatal(1, "Not exisiting Axi Burst detected.");
            endcase
          end
          this.w_queue.push_back(w_beat);

        end
      end while ( !vif.end_sim );
    endtask : recv_aws

    task recv_ws();
      do begin
        automatic ax_beat_t       aw_beat;
        automatic w_beat_t        w_beat;
        automatic w_beat_t        exp_w_beat;
        automatic llc_axi::addr_t w_addr;
        automatic llc_axi::addr_t word;
        automatic bit             error;

        forever begin
          rand_wait(0, 10);
          this.slv_drv.recv_w(w_beat);
          // crosscheck if it is the expected one
          w_addr     = this.w_mem_addr_queue.pop_front();
          word       = w_addr >> 3;
          exp_w_beat = this.w_queue.pop_front();
          if (!this.bak_mem_array.exists(word)) begin
            $fatal("made a evict opartation onto an address in bak_mem that does not exist!");
          end
          // compare everyting
          error =         !(exp_w_beat.w_data === w_beat.w_data);
          error = error | !(exp_w_beat.w_strb === w_beat.w_strb);
          error = error | !(exp_w_beat.w_last === w_beat.w_last);
          error = 1'b0;
          // error
          if( error ) begin
            $error("%s> Missmatch of recieved and expected Response, evict write.", this.name);
            $display("Expected w_beat");
            print_w_beat(exp_w_beat, w_addr, word);
            $display("Actual w_beat");
            print_w_beat(w_beat, w_addr, word);
            //$error("Address: %016X \nRecieved Data: %016X \nExpected Data: %016X ",
            //  w_addr, w_beat.w_data, exp_w_beat.w_data);
          end
          this.progress.addRes(error);
          // write the data into the backing memory
          this.bak_mem_array[word] = w_beat.w_data;
          if (w_beat.w_last) begin
            break;
          end
        end
        wait (this.aw_queue.size() > 0);
        aw_beat = this.aw_queue.pop_front();
        this.b_queue.push(aw_beat.ax_id, aw_beat);
      end while ( !vif.end_sim );
    endtask : recv_ws

    task send_bs();
      automatic ax_beat_t aw_beat;
      automatic b_beat_t  b_beat = new;
      do begin

        rand_wait(0, 10);
        wait(!this.b_queue.empty());
        aw_beat       = this.b_queue.pop();
        b_beat.b_id   = aw_beat.ax_id;
        b_beat.b_resp = axi_pkg::RESP_OKAY;
        b_beat.b_user = '0;
        this.slv_drv.send_b(b_beat);
      end while ( !vif.end_sim );
    endtask : send_bs

    task recv_ars();
      do begin
        automatic ax_beat_t       ar_beat; // the AR beat recieved
        automatic llc_axi::addr_t r_addr;  // address of the r beat
        automatic llc_axi::addr_t word;    // word address for looking up data in the bak_mem_array

        rand_wait(0, 10);
        this.slv_drv.recv_ar(ar_beat);
        //$display("AR refill detected");
        //print_ar_beat(ar_beat);
        // ar_queue.push(ar_beat.ax_id, ar_beat);
        // push the addresses for the read responses
        r_addr = ar_beat.ax_addr;

        for (int i = ar_beat.ax_len; i >= 0; i--) begin
          automatic r_beat_t r_beat = new;
          word = r_addr >> 3;
          // make the response r beats --> look in bak mem for data
          r_beat.r_id = ar_beat.ax_id;
          if (this.bak_mem_array.exists(word)) begin
            r_beat.r_data = this.bak_mem_array[word];
          end else begin
            $display("Addr: %h", r_addr);
            $display("Word: %h", word);
            $display("Data: %h", this.bak_mem_array[word]);
            $fatal(1, "Detected Refill from memory that was not initialyzed!!!");
          end
          r_beat.r_resp = axi_pkg::RESP_OKAY;
          r_beat.r_last = 1'b0;
          r_beat.r_user = '0;

          //$display("Pushing R Beat into Queue with ID: %h", ar_beat.ax_id);
          //print_r_beat(r_beat, r_addr, word);

          // update the address
          if ( i == 0 ) begin
            // last beat in w channel
            r_beat.r_last = 1'b1;
          end else begin
            // all other beats update address
            unique case (ar_beat.ax_burst)
              axi_pkg::BURST_FIXED : begin
                // Nothing, address stays the same
              end
              axi_pkg::BURST_INCR  : begin
                r_addr = r_addr + 2**ar_beat.ax_size;
              end
              axi_pkg::BURST_WRAP  : begin
                $error("Not supported wrapping burst at this time.");
              end
              default : $fatal(1, "Not exisiting Axi Burst detected.");
            endcase
          end
          this.r_beat_queue.push(ar_beat.ax_id, r_beat);
        end // for

      end while ( !vif.end_sim );
    endtask : recv_ars

    task send_rs();
      do begin
        automatic r_beat_t r_beat;
        // wait till we have some beats to send
        wait (!this.r_beat_queue.empty());
        rand_wait(0, 10);
        r_beat = this.r_beat_queue.pop();
        //$display("Sending R refill beat");
        //print_r_beat(r_beat, '0, '0);
        this.slv_drv.send_r(r_beat);
      end while ( !vif.end_sim );
    endtask : send_rs

    task print_aw_beat(input ax_beat_t aw_beat);
      $display("###############################################################");
      $info("AW Beat");
      $display("ID:     %h", aw_beat.ax_id);
      $display("ADDR:   %h", aw_beat.ax_addr);
      $display("WORD:   %h", aw_beat.ax_addr >> 3);
      $display("LEN:    %h", aw_beat.ax_len);
      $display("SIZE:   %h", aw_beat.ax_size);
      $display("BURST:  %h", aw_beat.ax_burst);
      $display("LOCK:   %h", aw_beat.ax_lock);
      $display("CACHE:  %h", aw_beat.ax_cache);
      $display("PROT:   %h", aw_beat.ax_prot);
      $display("QOS:    %h", aw_beat.ax_qos);
      $display("REGION: %h", aw_beat.ax_region);
      $display("ATOP:   %h", aw_beat.ax_atop);
      $display("USER:   %h", aw_beat.ax_user);
      $display("###############################################################");
    endtask : print_aw_beat

    task print_w_beat(input w_beat_t w_beat, llc_axi::addr_t w_addr, llc_axi::addr_t word);
      $display("###############################################################");
      $info("W Beat");
      $display("ADDR:   %h", w_addr);
      $display("WORD:   %h", word);
      $display("DATA:   %h", w_beat.w_data);
      $display("SRTB:   %h", w_beat.w_strb);
      $display("LAST:   %h", w_beat.w_last);
      $display("USER:   %h", w_beat.w_user);
      $display("###############################################################");
    endtask : print_w_beat

    task print_b_beat(input b_beat_t b_beat);
      $display("###############################################################");
      $info("B Beat");
      $display("ID:     %h", b_beat.b_id);
      $display("RESP:   %h", b_beat.b_resp);
      $display("USER:   %h", b_beat.b_user);
      $display("###############################################################");
    endtask : print_b_beat

    task print_ar_beat(input ax_beat_t ar_beat);
      $display("###############################################################");
      $info("AR Beat");
      $display("ID:     %h", ar_beat.ax_id);
      $display("ADDR:   %h", ar_beat.ax_addr);
      $display("WORD:   %h", ar_beat.ax_addr >> 3);
      $display("LEN:    %h", ar_beat.ax_len);
      $display("SIZE:   %h", ar_beat.ax_size);
      $display("BURST:  %h", ar_beat.ax_burst);
      $display("LOCK:   %h", ar_beat.ax_lock);
      $display("CACHE:  %h", ar_beat.ax_cache);
      $display("PROT:   %h", ar_beat.ax_prot);
      $display("QOS:    %h", ar_beat.ax_qos);
      $display("REGION: %h", ar_beat.ax_region);
      $display("ATOP:   %h", ar_beat.ax_atop);
      $display("USER:   %h", ar_beat.ax_user);
      $display("###############################################################");
    endtask : print_ar_beat

    task print_r_beat(input r_beat_t r_beat, llc_axi::addr_t r_addr, llc_axi::addr_t word);
      $display("###############################################################");
      $info("R Beat");
      $display("ID:     %h", r_beat.r_id);
      $display("ADDR:   %h", r_addr);
      $display("WORD:   %h", word);
      $display("DATA:   %h", r_beat.r_data);
      $display("RESP:   %h", r_beat.r_resp);
      $display("LAST:   %h", r_beat.r_last);
      $display("USER:   %h", r_beat.r_user);
      $display("###############################################################");
    endtask : print_r_beat

    task initialize_mem;
      llc_axi::addr_t addr = '0;
      for (longint i = 0; i < numWords; i++) begin
        this.cpu_mem_array[i] = 'x;
      end
    endtask : initialize_mem

    // run all the tasks
    task monitor_channel;
      //initialize_mem();
      fork
        monitor_aw();
        monitor_w();
        monitor_b();
        monitor_ar();
        monitor_r();
        recv_aws();
        recv_ws();
        send_bs();
        recv_ars();
        send_rs();
      join
    endtask : monitor_channel
  endclass : axi_llc_monitor
endpackage
