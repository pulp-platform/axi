// Copyright (c) 2018 ETH Zurich, University of Bologna
//
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Test infrastructure for APB interfaces
package apb_test;

  // Simple APB driver with thread-safe 32-bit read and write functions
  class apb_driver #(
    parameter time TA = 0ns,
    parameter time TT = 0ns
  );

    virtual APB_DV apb;
    semaphore lock;

    function new(virtual APB_DV apb);
      this.apb = apb;
      this.lock = new(1);
    endfunction

    task reset_master;
      apb.paddr   <= '0;
      apb.pprot   <= '0;
      apb.psel    <= 1'b0;
      apb.penable <= 1'b0;
      apb.pwrite  <= 1'b0;
      apb.pwdata  <= '0;
      apb.pstrb   <= '0;
    endtask

    task reset_slave;
      apb.pready  <= 1'b0;
      apb.prdata  <= '0;
      apb.pslverr <= 1'b0;
    endtask

    task cycle_start;
      #TT;
    endtask

    task cycle_end;
      @(posedge apb.clk_i);
    endtask

    task read(
      input  logic [31:0] addr,
      output logic [31:0] data,
      output logic err
    );
      while (!lock.try_get()) begin
        cycle_end();
      end
      apb.paddr   <= #TA addr;
      apb.pwrite  <= #TA 1'b0;
      apb.psel    <= #TA 1'b1;
      cycle_end();
      apb.penable <= #TA 1'b1;
      cycle_start();
      while (!apb.pready) begin
        cycle_end();
        cycle_start();
      end
      data  = apb.prdata;
      err   = apb.pslverr;
      cycle_end();
      apb.paddr   <= #TA '0;
      apb.psel    <= #TA 1'b0;
      apb.penable <= #TA 1'b0;
      lock.put();
    endtask

    task write(
      input  logic [31:0] addr,
      input  logic [31:0] data,
      input  logic  [3:0] strb,
      output logic err
    );
      while (!lock.try_get()) begin
        cycle_end();
      end
      apb.paddr   <= #TA addr;
      apb.pwdata  <= #TA data;
      apb.pstrb   <= #TA strb;
      apb.pwrite  <= #TA 1'b1;
      apb.psel    <= #TA 1'b1;
      cycle_end();
      apb.penable <= #TA 1'b1;
      cycle_start();
      while (!apb.pready) begin
        cycle_end();
        cycle_start();
      end
      err = apb.pslverr;
      cycle_end();
      apb.paddr   <= #TA '0;
      apb.pwdata  <= #TA '0;
      apb.pstrb   <= #TA '0;
      apb.pwrite  <= #TA 1'b0;
      apb.psel    <= #TA 1'b0;
      apb.penable <= #TA 1'b0;
      lock.put();
    endtask

  endclass

endpackage
