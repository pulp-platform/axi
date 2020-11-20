// Copyright (c) 2019 ETH Zurich, University of Bologna
// All rights reserved.
//
// This code is under development and not yet released to the public.
// Until it is released, the code is under the copyright of ETH Zurich and
// the University of Bologna, and may contain confidential and/or unpublished
// work. Any reuse/redistribution is strictly forbidden without written
// permission from ETH Zurich.
//
// Thomas Benz <tbenz@ethz.ch>

// fixture for the AXi DMA backend
// the fixture instantiates the DMA backend, a golden model of the backend , and tasks controlling
// both.

`timescale 1ns/1ns
module fixture_axi_dma_backend();

    // `include "../axi/include/axi/assign.svh"
    // `define MEM_DEBUG 1
    `include "axi/assign.svh"
    `include "axi/typedef.svh"

    //--------------------------------------
    // Parameters
    //--------------------------------------
    localparam TA          = 0.2ns;  // must be nonzero to avoid Snitch load fifo double pop glitch
    localparam TT          = 0.8ns;
    localparam HalfPeriod  = 50ns;
    localparam Reset       = 75ns;

    localparam DataWidth   = 512;
    localparam AddrWidth   = 64;
    localparam StrbWidth   = DataWidth / 8;
    localparam IdWidth     = 6;
    localparam UserWidth   = 1;

    typedef union packed {
        logic [StrbWidth-1:0][7:0] bytes;
        logic [DataWidth-1:0]      data;
    } block_t;

    /// Address Type
    typedef logic [  AddrWidth-1:0] addr_t;
    /// Data Type
    typedef logic [  DataWidth-1:0] data_t;
    /// Strobe Type
    typedef logic [  StrbWidth-1:0] strb_t;
    /// AXI ID Type
    typedef logic [    IdWidth-1:0] axi_id_t;
    /// AXI USER Type
    typedef logic [  UserWidth-1:0] user_t;
    /// 1D burst request
    typedef struct packed {
        axi_id_t            id;
        addr_t              src, dst, num_bytes;
        axi_pkg::cache_t    cache_src, cache_dst;
        axi_pkg::burst_t    burst_src, burst_dst;
        logic               decouple_rw;
        logic               deburst;
        logic               serialize;
    } burst_req_t;

    `AXI_TYPEDEF_AW_CHAN_T(aw_chan_dma_t, addr_t, axi_id_t, user_t)
    `AXI_TYPEDEF_W_CHAN_T(w_chan_t, data_t, strb_t, user_t)
    `AXI_TYPEDEF_B_CHAN_T(b_chan_dma_t, axi_id_t, user_t)

    `AXI_TYPEDEF_AR_CHAN_T(ar_chan_dma_t, addr_t, axi_id_t, user_t)
    `AXI_TYPEDEF_R_CHAN_T(r_chan_dma_t, data_t, axi_id_t, user_t)

    `AXI_TYPEDEF_REQ_T(dma_req_t, aw_chan_dma_t, w_chan_t, ar_chan_dma_t)
    `AXI_TYPEDEF_RESP_T(dma_resp_t, b_chan_dma_t, r_chan_dma_t)

    //--------------------------------------
    // Clock and Reset
    //--------------------------------------
    logic clk;
    initial begin
        forever begin
            clk = 0;
            #HalfPeriod;
            clk = 1;
            #HalfPeriod;
        end
    end

    logic rst_n;
    initial begin
        rst_n = 0;
        #Reset;
        rst_n = 1;
    end

    task wait_for_reset;
       @(posedge rst_n);
       @(posedge clk);
    endtask

    //--------------------------------------
    // DUT Axi busses
    //--------------------------------------
    dma_req_t  axi_dma_req;
    dma_resp_t axi_dma_res;

    AXI_BUS_DV #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) dma (clk);

    AXI_BUS #(
        .AXI_ADDR_WIDTH  ( AddrWidth   ),
        .AXI_DATA_WIDTH  ( DataWidth   ),
        .AXI_ID_WIDTH    ( IdWidth     ),
        .AXI_USER_WIDTH  ( 1           )
    ) mem ();

    `AXI_ASSIGN (dma, mem)
    `AXI_ASSIGN_FROM_REQ(mem, axi_dma_req)
    `AXI_ASSIGN_TO_RESP(axi_dma_res, mem)

    //--------------------------------------
    // DUT AXI Memory System
    //--------------------------------------
    // lfsr
    logic [784:0] lfsr_dut_q, lfsr_dut_d;

    // transaction id
    logic [  7:0] transaction_id = 0;

    // Memory
    block_t dma_memory [bit [64-$clog2($bits(block_t))-1:0]];

    // Handle the data output from dma. Model of the memory acting as AXI slave.
    typedef axi_test::axi_driver #(.AW(AddrWidth), .DW(DataWidth), .IW(IdWidth), .UW(1), .TA(0.1*2*HalfPeriod), .TT(0.9*2*HalfPeriod)) driver_dma_t;
    driver_dma_t driver_dma = new(dma);
    initial begin
        automatic driver_dma_t::ax_beat_t aw_dma_queue[$], ar_dma_queue[$];
        automatic driver_dma_t::b_beat_t b_dma_queue[$];
        automatic string sb = "";

        event ar_dma_received, aw_dma_received, b_dma_ready;
        event lfsr_dut_read;
        event lfsr_dut_read_completed;

        driver_dma.reset_slave();
        @(posedge rst_n);
        $display("AXI reset done");

        fork
            // AW
            forever begin
                automatic driver_dma_t::ax_beat_t dma_tx;
                driver_dma.recv_aw(dma_tx);
`ifdef MEM_DEBUG
                $display("%d: AW - id: %4d - addr: %d - len: %4d - size: %4d - burst: %b",
                             $time(), dma_tx.ax_id, dma_tx.ax_addr, dma_tx.ax_len, dma_tx.ax_size, dma_tx.ax_burst );
`endif
                aw_dma_queue.push_back(dma_tx);
                -> aw_dma_received;
            end
            // AR
            forever begin
                automatic driver_dma_t::ax_beat_t dma_tx;
                driver_dma.recv_ar(dma_tx);
`ifdef MEM_DEBUG
                $display("%d: AR - id: %4d - addr: %d - len: %4d - size: %4d - burst: %b",
                            $time(), dma_tx.ax_id, dma_tx.ax_addr, dma_tx.ax_len, dma_tx.ax_size, dma_tx.ax_burst );
`endif
                ar_dma_queue.push_back(dma_tx);
                -> ar_dma_received;
            end
            // R
            forever begin
                automatic driver_dma_t::r_beat_t dma_tx = new();
                automatic driver_dma_t::ax_beat_t dma_ax;
                automatic bit [AddrWidth-1:0] word;
                while (ar_dma_queue.size() == 0) @ar_dma_received;
                dma_ax = ar_dma_queue[0];
                word = dma_ax.ax_addr >> 6;
                dma_tx.r_id = dma_ax.ax_id;
                if (!dma_memory.exists(word)) begin
                    dma_memory[word].data = lfsr_dut_q[784:273];
                    //shift 513x
                    repeat(513) begin
                        // next state
                        for (int i = 1; i < 785; i = i +1) lfsr_dut_d[i-1] = lfsr_dut_q[i];
                        lfsr_dut_d[784] = lfsr_dut_q[0];
                        lfsr_dut_d[692] = lfsr_dut_q[0] ^ lfsr_dut_q[693];
                        lfsr_dut_q      = lfsr_dut_d;
                    end
                end
                dma_tx.r_data = dma_memory[word].data;
                dma_tx.r_resp = axi_pkg::RESP_OKAY;
                dma_tx.r_last = (dma_ax.ax_len == 0);
`ifdef MEM_DEBUG
                $display("%d:  R - id: %4d - data: %x - resp: %x                - last: %b (0x%x)",
                        $time(), dma_tx.r_id, dma_tx.r_data, dma_tx.r_resp, dma_tx.r_last, word << 6);
`endif
                dma_ax.ax_addr >>= dma_ax.ax_size;
                dma_ax.ax_addr += (dma_ax.ax_burst !== 0);
                dma_ax.ax_addr <<= dma_ax.ax_size;
                dma_ax.ax_len -= 1;
                if (dma_tx.r_last) begin
                    ar_dma_queue.pop_front();
                end
                driver_dma.send_r(dma_tx);
            end
            // W
            forever begin
                automatic driver_dma_t::w_beat_t dma_tx;
                automatic driver_dma_t::ax_beat_t dma_ax;
                automatic bit [AddrWidth-1:0] word;
                driver_dma.recv_w(dma_tx);
                while (aw_dma_queue.size() == 0) @ar_dma_received;
                dma_ax = aw_dma_queue[0];
                word = dma_ax.ax_addr >> 6;
                //$display("Ready to write");
                //$display("%x", word);
                for (int i = 0; i < StrbWidth; i++) begin
                    if (dma_tx.w_strb[i]) begin
                          dma_memory[word].bytes[i] = dma_tx.w_data[i*8+:8];
                    end
                end
`ifdef MEM_DEBUG
                $display("%d:  W -            data: %x - strb: %x - last: %b (0x%x)",
                       $time(), dma_tx.w_data, dma_tx.w_strb, dma_tx.w_last, word << 6);
`endif
                dma_ax.ax_addr >>= dma_ax.ax_size;
                dma_ax.ax_addr += (dma_ax.ax_burst !== 0);
                dma_ax.ax_addr <<= dma_ax.ax_size;
                dma_ax.ax_len -= 1;
                if (dma_tx.w_last) begin
                    automatic driver_dma_t::b_beat_t dma_tx = new();
                    dma_tx.b_id = dma_ax.ax_id;
                    dma_tx.b_user = dma_ax.ax_user;
                    aw_dma_queue.pop_front();
                    b_dma_queue.push_back(dma_tx);
                    -> b_dma_ready;
                end
            end
            // B
            forever begin
                automatic driver_dma_t::b_beat_t dma_tx;
                while (b_dma_queue.size() == 0) @b_dma_ready;
                driver_dma.send_b(b_dma_queue[0]);
                b_dma_queue.pop_front();
            end
        join_any
    end

    //--------------------------------------
    // DMA instantiation
    //--------------------------------------
    burst_req_t burst_req;
    logic burst_req_valid;
    logic burst_req_ready;
    logic backend_idle;

    axi_dma_backend #(
        .DataWidth           ( DataWidth           ),
        .AddrWidth           ( AddrWidth           ),
        .IdWidth             ( IdWidth             ),
        .DmaIdWidth          ( 32                  ),
        .AxReqFifoDepth      ( 3                   ),
        .TransFifoDepth      ( 2                   ),
        .BufferDepth         ( 3                   ),
        .axi_req_t           ( dma_req_t           ),
        .axi_res_t           ( dma_resp_t          ),
        .burst_req_t         ( burst_req_t         ),
        .DmaTracing          ( 1                   )
    ) i_dut_axi_backend (
        .clk_i              ( clk              ),
        .rst_ni             ( rst_n            ),
        .axi_dma_req_o      ( axi_dma_req      ),
        .axi_dma_res_i      ( axi_dma_res      ),
        .burst_req_i        ( burst_req        ),
        .valid_i            ( burst_req_valid  ),
        .ready_o            ( burst_req_ready  ),
        .backend_idle_o     ( backend_idle     ),
        .trans_complete_o   ( ),
        .dma_id_i           ( '0               )
    );

    //--------------------------------------
    // DMA DUT tasks
    //--------------------------------------
    task oned_dut_launch (
        input logic [   IdWidth-1:0] transf_id_i,
        input logic [ AddrWidth-1:0] src_addr_i,  dst_addr_i,  num_bytes_i,
        input logic [           1:0] src_burst_i, dst_burst_i,
        input logic [           3:0] src_cache_i, dst_cache_i,
        input logic                  decouple_rw_i,
        input logic                  serialize_i,
        input logic                  deburst_i
    );
        burst_req_valid        <= 1'b0;
        burst_req              <=  '0;
        @(posedge clk);
        while (burst_req_ready !== 1) @(posedge clk);
        // write data
        burst_req.id           <= transf_id_i;
        burst_req.src          <= src_addr_i;
        burst_req.dst          <= dst_addr_i;
        burst_req.num_bytes    <= num_bytes_i;
        burst_req.cache_src    <= src_cache_i;
        burst_req.cache_dst    <= dst_cache_i;
        burst_req.burst_src    <= src_burst_i;
        burst_req.burst_dst    <= dst_burst_i;
        burst_req.decouple_rw  <= decouple_rw_i;
        burst_req.deburst      <= deburst_i;
        burst_req.serialize    <= serialize_i;
        burst_req_valid        <= 1'b1;
        // wait and set to 0
        @(posedge clk);
        burst_req_valid        <= 1'b0;
        burst_req              <=  '0;
    endtask

    task oned_reset ();
        burst_req_valid        <= 1'b0;
        burst_req              <=  '0;
    endtask

    task wait_for_dut_completion ();
        repeat(10) @(posedge clk);
        while (backend_idle === 0) @(posedge clk);
        repeat(50) @(posedge clk);
    endtask

    task clear_dut_memory ();
        dma_memory.delete();
    endtask

    task reset_dut_lfsr ();
        lfsr_dut_q <= 'hc0a232c162b2bab5b960668030f4efce27940bd0de965f0b8d4315f15b79704195e4e0a6b495fc269f65ae17e10e9ca98510fc143327a292b418597f9dd175fc91c3d61be287d5462a23e00fa7ae906ae9eb339ab5225021356138cd46b6e5a73540c5591116b6b5e08d2c0e54eaf0d5143b33b2186b6cf841c076a98c412a63981f0e323dce93481ed1c37e4f1d7553b6c2fba1a3af6c3ad88b15ad58812ba07d1753917ac4e6ab1e8c4f67a47b4b0f48a34f42a52c546e979f4e4968e80a732a0a5e7a51146cf08482f349f94336752b765c0b1d70803d883d5058d127264335213da4163c62f65a4e65501b90fa5f177675c0747cfca328e131bfb3f7bcc5c27680c7bf86491f4ed3d36c25531edfa74b1e32fafe426958ae356eb8ef0fd818eaca4227a667b7c934ebfa282ab6bfc6db89b927c91a41e63a9554dced774f30268d0725a1a565368703b9f81d5c027ba196ef8b803a51c639c7ead834e1d6bc537d33800fe5eb12f1ed67758f1dfe85ffdbae56e8ef27f2ecedcee75b8dbb5f5f1a629ba3b755;
    endtask

    //--------------------------------------
    // Osmium Model
    //--------------------------------------
    // Memory
    block_t osmium_memory [bit [64-$clog2($bits(block_t))-1:0]];
    // lfsr
    logic [784:0] lfsr_osmium_q,lfsr_osmium_d;

    task oned_osmium_launch (
        input logic [   IdWidth-1:0] transf_id_i,
        input logic [ AddrWidth-1:0] src_addr_i,  dst_addr_i,  num_bytes_i,
        input logic [           1:0] src_burst_i, dst_burst_i,
        input logic [           3:0] src_cache_i, dst_cache_i,
        input logic                  decouple_rw_i,
        input logic                  deburst_i,
        input logic                  serialize_i
    );
        logic [63:0] read_addr,   write_addr;
        logic [63:0] read_word,   write_word;
        logic [ 6:0] read_offset, write_offset;
        // perform the transfer
        for(int i = 0; i < num_bytes_i; i = i + 1) begin
            read_addr     = src_addr_i + i;
            write_addr    = dst_addr_i + i;
            read_word     = src_burst_i == 2'b00 ? src_addr_i >> 6 : read_addr  >> 6;
            write_word    = dst_burst_i == 2'b00 ? dst_addr_i >> 6 : write_addr >> 6;
            read_offset   = read_addr [5:0];
            write_offset  = write_addr[5:0];

            // do the read
            if (!osmium_memory.exists(read_word) === 1) begin
                osmium_memory[read_word].data = lfsr_osmium_q[784:273];
                //shift 513x
                repeat(513) begin
                    // next state
                    for (int i = 1; i < 785; i = i +1) lfsr_osmium_d[i-1] = lfsr_osmium_q[i];
                    lfsr_osmium_d[784] = lfsr_osmium_q[0];
                    lfsr_osmium_d[692] = lfsr_osmium_q[0] ^ lfsr_osmium_q[693];
                    lfsr_osmium_q      = lfsr_osmium_d;
                end
            end
            // do the write
            osmium_memory[write_word].bytes[write_offset] = osmium_memory[read_word].bytes[read_offset];
            // $display("W: %d - %d    R: %d - %d", write_word, write_offset, read_word, read_offset);
        end

    endtask

    task clear_osmium_memory ();
        osmium_memory.delete();
    endtask

    task reset_osmium_lfsr ();
        lfsr_osmium_q = 'hc0a232c162b2bab5b960668030f4efce27940bd0de965f0b8d4315f15b79704195e4e0a6b495fc269f65ae17e10e9ca98510fc143327a292b418597f9dd175fc91c3d61be287d5462a23e00fa7ae906ae9eb339ab5225021356138cd46b6e5a73540c5591116b6b5e08d2c0e54eaf0d5143b33b2186b6cf841c076a98c412a63981f0e323dce93481ed1c37e4f1d7553b6c2fba1a3af6c3ad88b15ad58812ba07d1753917ac4e6ab1e8c4f67a47b4b0f48a34f42a52c546e979f4e4968e80a732a0a5e7a51146cf08482f349f94336752b765c0b1d70803d883d5058d127264335213da4163c62f65a4e65501b90fa5f177675c0747cfca328e131bfb3f7bcc5c27680c7bf86491f4ed3d36c25531edfa74b1e32fafe426958ae356eb8ef0fd818eaca4227a667b7c934ebfa282ab6bfc6db89b927c91a41e63a9554dced774f30268d0725a1a565368703b9f81d5c027ba196ef8b803a51c639c7ead834e1d6bc537d33800fe5eb12f1ed67758f1dfe85ffdbae56e8ef27f2ecedcee75b8dbb5f5f1a629ba3b755;
    endtask

    //--------------------------------------
    // Compare Memory content
    //--------------------------------------
    task compare_memories ();

        // go through osmium memory and compare contents
        foreach(osmium_memory[i]) begin
            if (osmium_memory[i] !== dma_memory[i]) $fatal("Memory mismatch @ %x\nexpect: %x\ngot   :%x\n", i << 6, osmium_memory[i], dma_memory[i]);
        end
        // go through dma memory and compare contents
        foreach(dma_memory[i]) begin
            if (osmium_memory[i] !== dma_memory[i]) $fatal("Memory mismatch @ %x\nexpect: %x\ngot   :%x\n", i << 6, osmium_memory[i], dma_memory[i]);
        end

        // it worked :P
        $display(" - :D");

    endtask

    //--------------------------------------
    // Master tasks
    //--------------------------------------

    task clear_memory ();
        clear_dut_memory();
        clear_osmium_memory();
    endtask

    task reset_lfsr ();
        reset_dut_lfsr();
        reset_osmium_lfsr();
    endtask

    task oned_launch (
        input logic [   IdWidth-1:0] transf_id_i,
        input logic [ AddrWidth-1:0] src_addr_i,  dst_addr_i,  num_bytes_i,
        input logic                  decouple_rw_i,
        input logic                  deburst_i,
        input logic                  serialize_i,
        input logic                  wait_for_completion_i
    );
        // keep a log file
        int my_file;
        my_file = $fopen("dma_transfers.txt", "a+");
        $write("ID: %d  SRC: 0x%x  DST: 0x%x  LEN: %d  DECOUPLE: %1b DEBURST: %1b SERIALIZE: %1b", transf_id_i, src_addr_i, dst_addr_i, num_bytes_i, decouple_rw_i, deburst_i, serialize_i );
        $fwrite (my_file, "ID: %d  SRC: 0x%x  DST: 0x%x  LEN: %d  DECOUPLE: %1b DEBURST: %1b SERIALIZE: %1b\n", transf_id_i, src_addr_i, dst_addr_i, num_bytes_i, decouple_rw_i, deburst_i, serialize_i );
        $fclose(my_file);

        // cache and burst is ignored
        oned_dut_launch(transf_id_i, src_addr_i, dst_addr_i, num_bytes_i, 2'b01, 2'b01, 4'h0, 4'h0, decouple_rw_i, deburst_i, serialize_i);
        // wait if requested
        if (wait_for_completion_i)
            wait_for_dut_completion();
        // run model
        oned_osmium_launch(transf_id_i, src_addr_i, dst_addr_i, num_bytes_i, 2'b01, 2'b01, 4'h0, 4'h0, decouple_rw_i, deburst_i, serialize_i);
    endtask

    task reset ();
        int my_file;
        oned_reset();
        wait_for_reset();
        // clear trace file
        my_file = $fopen("dma_transfers.txt", "w");
        $fwrite(my_file, "Transfers launched:\n");
        $fclose(my_file);
    endtask

    task oned_random_launch(
        input  logic [15:0] max_len,
        input  logic        wait_for_completion
    );

        logic [   IdWidth-1:0] transf_id;
        logic [ AddrWidth-1:0] src_addr,  dst_addr,  num_bytes;
        logic                  decouple_rw;
        logic                  deburst;
        logic                  serialize;

        transf_id         = $urandom();
        // transf_id         = transaction_id;
        src_addr[63:32]   = $urandom();
        src_addr[31: 0]   = $urandom();
        dst_addr[63:32]   = $urandom();
        dst_addr[31: 0]   = $urandom();
        num_bytes         = 0;
        num_bytes[15: 0]  = $urandom_range(max_len, 1);
        decouple_rw       = $urandom();
        deburst           = $urandom();
        serialize         = $urandom();

        // transaction_id    = transaction_id + 1;

        oned_launch(transf_id, src_addr, dst_addr, num_bytes, decouple_rw, deburst, serialize, wait_for_completion);

    endtask

endmodule : fixture_axi_dma_backend
