// Copyright (c) 2020 ETH Zurich, University of Bologna
// All rights reserved.
//
// This code is under development and not yet released to the public.
// Until it is released, the code is under the copyright of ETH Zurich and
// the University of Bologna, and may contain confidential and/or unpublished
// work. Any reuse/redistribution is strictly forbidden without written
// permission from ETH Zurich.
//
// Thomas Benz <tbenz@ethz.ch>

/// Splits a generic 1D transfer in AXI-conform transfers
module axi_dma_burst_reshaper #(
    /// Data width of the AXI bus
    parameter int unsigned DataWidth = -1,
    /// Address width of the AXI bus
    parameter int unsigned AddrWidth = -1,
    /// ID width of the AXI bus
    parameter int unsigned IdWidth = -1,
    /// Arbitrary 1D burst request definition:
    /// - id: the AXI id used - this id should be constant, as the DMA does not support reordering
    /// - src, dst: source and destination address, same width as the AXI 4 interface
    /// - num_bytes: the length of the contiguous 1D transfer requested, can be up to 32/64 bit long
    ///              num_bytes will be interpreted as an unsigned number
    ///              A value of 0 will cause the backend to discard the transfer prematurely
    /// - src_cache, dst_cache: the configuration of the cache fields in the AX beats
    /// - src_burst, dst_burst: currently only incremental bursts are supported (2'b01)
    /// - decouple_rw: if set to true, there is no longer exactly one AXI write_request issued for 
    ///   every read request. This mode can improve performance of unaligned transfers when crossing
    ///   the AXI page boundaries.
    /// - deburst: if set, the DMA will split all bursts in single transfers
    parameter type         burst_req_t = logic,
    /// Read request definition. Includes:
    /// - ax descriptor
    ///  - id: AXI id
    ///  - last: last transaction in burst
    ///  - address: address of burst
    ///  - length: burst length
    ///  - size: bytes in each burst
    ///  - burst: burst type; only INC supported
    ///  - cache: cache type
    /// - r descriptor
    ///  - offset: initial misalignment
    ///  - tailer: final misalignment
    ///  - shift: amount the data needs to be shifted to realign it
    parameter type         read_req_t = logic,
    /// Write request definition. Includes:
    /// - ax descriptor
    ///  - id: AXI id
    ///  - last: last transaction in burst
    ///  - address: address of burst
    ///  - length: burst length
    ///  - size: bytes in each burst
    ///  - burst: burst type; only INC supported
    ///  - cache: cache type
    /// - w descriptor
    ///  - offset: initial misalignment
    ///  - tailer: final misalignment
    ///  - num_beats: number of beats in the burst
    ///  - is_single: burst length is 0
    parameter type         write_req_t = logic

) (
    /// Clock
    input  logic          clk_i,
    /// Asynchronous reset, active low
    input  logic          rst_ni,
    /// Arbitrary 1D burst request
    input  burst_req_t    burst_req_i,

    /// Handshake: burst request is valid
    input  logic          valid_i,
    /// Handshake: burst request can be accepted
    output logic          ready_o,

    /// Write transfer request
    output write_req_t    write_req_o,
    /// Read transfer request
    output read_req_t     read_req_o,

    /// Handshake: read transfer request valid
    output logic          r_valid_o,
    /// Handshake: read transfer request ready
    input  logic          r_ready_i,
    /// Handshake: write transfer request valid
    output logic          w_valid_o,
    /// Handshake: write transfer request ready
    input  logic          w_ready_i
);

    localparam int unsigned StrbWidth     = DataWidth / 8;
    localparam int unsigned OffsetWidth   = $clog2(StrbWidth);
    localparam int unsigned PageSize      = (256 * StrbWidth > 4096) ? 4096 :  256 * StrbWidth;
    localparam int unsigned PageAddrWidth = $clog2(PageSize);
    /// Offset type
    typedef logic [  OffsetWidth-1:0] offset_t;
    /// Address Type
    typedef logic [    AddrWidth-1:0] addr_t;
    /// AXI ID Type
    typedef logic [      IdWidth-1:0] axi_id_t;

    /// Type containing burst description for each channel independently
    typedef struct packed {
        axi_id_t          id;
        addr_t            addr;
        addr_t            num_bytes;
        axi_pkg::cache_t  cache;
        axi_pkg::burst_t  burst;
        logic             valid;
    } burst_chan_t;

    /// Type containing burst description 
    typedef struct packed {
        burst_chan_t  src;
        burst_chan_t  dst;
        offset_t      shift;
        logic         decouple_rw;
        logic         deburst;
    } burst_decoupled_t;

    //--------------------------------------
    // state; internally hold one transfer
    //-------------------------------------- 
    burst_decoupled_t burst_d, burst_q;

    //--------------------------------------
    // page boundary check
    //-------------------------------------- 
    logic [PageAddrWidth-1:0] r_page_offset;
    logic [PageAddrWidth  :0] r_num_bytes_to_pb;
    logic [PageAddrWidth-1:0] w_page_offset;
    logic [PageAddrWidth  :0] w_num_bytes_to_pb;
    logic [PageAddrWidth  :0] c_num_bytes_to_pb;

    always_comb begin : proc_write_page_boundry_check
        // implement deburst operation
        if (burst_q.deburst) begin
            // deburst
            // read pages
            r_page_offset     = burst_q.src.addr[OffsetWidth-1:0];
            // how many transfers are remaining until the end of the bus?
            r_num_bytes_to_pb = (StrbWidth - r_page_offset) % (2 * StrbWidth);

            // write pages
            w_page_offset     = burst_q.dst.addr[OffsetWidth-1:0];
            // how many transfers are remaining until the end of the bus?
            w_num_bytes_to_pb = (StrbWidth - w_page_offset) % (2 * StrbWidth);
        end else begin
            // bursts allowed
            // read pages
            r_page_offset     = burst_q.src.addr[PageAddrWidth-1:0];
            // how many transfers are remaining in current page?
            r_num_bytes_to_pb = PageSize - r_page_offset;

            // write pages
            w_page_offset     = burst_q.dst.addr[PageAddrWidth-1:0];
            // how many transfers are remaining in current page?
            w_num_bytes_to_pb = PageSize - w_page_offset;
        end
        // how many transfers are remaining when concerning both r/w pages?
        // take the boundary that is closer
        c_num_bytes_to_pb = (r_num_bytes_to_pb > w_num_bytes_to_pb) ?
                             w_num_bytes_to_pb : r_num_bytes_to_pb;
                             
    end

    //--------------------------------------
    // Synchronized R/W process
    //-------------------------------------- 
    logic [PageAddrWidth:0] r_num_bytes_possible;
    logic [PageAddrWidth:0] r_num_bytes;
    logic                   r_finish;
    logic [OffsetWidth-1:0] r_addr_offset;

    logic [PageAddrWidth:0] w_num_bytes_possible;
    logic [PageAddrWidth:0] w_num_bytes;
    logic                   w_finish;
    logic [OffsetWidth-1:0] w_addr_offset;

    always_comb begin : proc_read_write_transaction

        // default: keep last state
        burst_d = burst_q;

        //--------------------------------------
        // Specify read transaction
        //-------------------------------------- 
        // max num bytes according to page(s)
        r_num_bytes_possible = (burst_q.decouple_rw == 1'b1) ?
                                r_num_bytes_to_pb : c_num_bytes_to_pb;

        // more bytes remaining than we can send
        if (burst_q.src.num_bytes > r_num_bytes_possible) begin
            r_num_bytes           = r_num_bytes_possible;
            // calculate remainder
            burst_d.src.num_bytes = burst_q.src.num_bytes - r_num_bytes_possible;
            // not finished
            r_finish              = 1'b0;
            // next address, depends on burst type. only type 01 is supported yet
            burst_d.src.addr      = (burst_q.src.burst == axi_pkg::BURST_INCR) ?
                                    burst_q.src.addr + r_num_bytes : burst_q.src.addr;

        // remaining bytes fit in one burst
        // reset storage for the read channel to stop this channel
        end else begin 
            r_num_bytes   = burst_q.src.num_bytes[PageAddrWidth:0];
            // default: when a transfer is finished, set it to 0
            burst_d.src   = '0;
            // finished
            r_finish      = 1'b1;
        end

        // calculate the address offset aligned to transfer sizes.
        r_addr_offset     = burst_q.src.addr[OffsetWidth-1:0];

        // create the AR request
        read_req_o.ar.addr     = { burst_q.src.addr[AddrWidth-1:OffsetWidth],
                                   {{OffsetWidth}{1'b0}} };
        read_req_o.ar.len      = ((r_num_bytes + r_addr_offset - 1) >> OffsetWidth);
        read_req_o.ar.size     = axi_pkg::size_t'(OffsetWidth);
        read_req_o.ar.id       = burst_q.src.id;
        read_req_o.ar.last     = r_finish;
        read_req_o.ar.burst    = burst_q.src.burst;
        read_req_o.ar.cache    = burst_q.src.cache;
        r_valid_o              = burst_q.decouple_rw ? 
                                 burst_q.src.valid : burst_q.src.valid & w_ready_i;

        // create the R request
        read_req_o.r.offset = r_addr_offset;
        read_req_o.r.tailer = OffsetWidth'(r_num_bytes + r_addr_offset);
        // shift is determined on a per 1D request base
        read_req_o.r.shift  = burst_q.shift;

        //--------------------------------------
        // Specify write transaction
        //-------------------------------------- 
        // max num bytes according to page(s)
        w_num_bytes_possible = (burst_q.decouple_rw == 1'b1) ?
                                w_num_bytes_to_pb : c_num_bytes_to_pb;

        // more bytes remaining than we can send
        if (burst_q.dst.num_bytes > w_num_bytes_possible) begin
            w_num_bytes           = w_num_bytes_possible;
            // calculate remainder
            burst_d.dst.num_bytes = burst_q.dst.num_bytes - w_num_bytes_possible;
            // not finished
            w_finish              = 1'b0;
            // next address, depends on burst type. only type 01 is supported yet
            burst_d.dst.addr      = (burst_q.dst.burst == axi_pkg::BURST_INCR) ?
                                     burst_q.dst.addr + w_num_bytes : burst_q.dst.addr;

        // remaining bytes fit in one burst
        // reset storage for the write channel to stop this channel
        end else begin 
            w_num_bytes   = burst_q.dst.num_bytes[PageAddrWidth:0];
            // default: when a transfer is finished, set it to 0
            burst_d.dst   = '0;
            // finished
            w_finish      = 1'b1;
        end

        // calculate the address offset aligned to transfer sizes.
        w_addr_offset     = burst_q.dst.addr[OffsetWidth-1:0];

        // create the AW request
        write_req_o.aw.addr     = { burst_q.dst.addr[AddrWidth-1:OffsetWidth],
                                    {{OffsetWidth}{1'b0}} };
        write_req_o.aw.len      = ((w_num_bytes + w_addr_offset - 1) >> OffsetWidth);
        write_req_o.aw.size     = axi_pkg::size_t'(OffsetWidth);
        write_req_o.aw.id       = burst_q.dst.id;
        // hand over internal transaction id
        write_req_o.aw.last     = w_finish;
        write_req_o.aw.burst    = burst_q.dst.burst;
        write_req_o.aw.cache    = burst_q.dst.cache;
        w_valid_o               = burst_q.decouple_rw ? 
                                  burst_q.dst.valid : burst_q.dst.valid & r_ready_i;

        // create the W request
        write_req_o.w.offset    = w_addr_offset;
        write_req_o.w.tailer    = OffsetWidth'(w_num_bytes + w_addr_offset);
        write_req_o.w.num_beats = write_req_o.aw.len;
        // is the transfer be only one beat in length? Counters don't have to be initialized then.
        write_req_o.w.is_single = (write_req_o.aw.len == '0);

        //--------------------------------------
        // Module control
        //-------------------------------------- 
        ready_o = r_finish & w_finish & valid_i & r_ready_i & w_ready_i;

        //--------------------------------------
        // Refill
        //-------------------------------------- 
        // new request is taken in if both r and w machines are ready.
        if (ready_o) begin
            // unfortunately this is unpacked
            burst_d.src.id          = burst_req_i.id;
            burst_d.src.addr        = burst_req_i.src;
            burst_d.src.num_bytes   = burst_req_i.num_bytes;
            burst_d.src.cache       = burst_req_i.cache_src;
            burst_d.src.burst       = burst_req_i.burst_src;
            // check if transfer is possible -> num_bytes has to be larger than 0
            burst_d.src.valid       = (burst_req_i.num_bytes == '0) ? 1'b0 : valid_i;

            burst_d.dst.id          = burst_req_i.id;
            burst_d.dst.addr        = burst_req_i.dst;
            burst_d.dst.num_bytes   = burst_req_i.num_bytes;
            burst_d.dst.cache       = burst_req_i.cache_dst;
            burst_d.dst.burst       = burst_req_i.burst_dst;
            // check if transfer is possible -> num_bytes has to be larger than 0
            burst_d.dst.valid       = (burst_req_i.num_bytes == '0) ? 1'b0 : valid_i;

            burst_d.decouple_rw     = burst_req_i.decouple_rw;
            burst_d.deburst         = burst_req_i.deburst;
            // shift is calculated for each 1D transfer
            burst_d.shift           = burst_req_i.src[OffsetWidth-1:0] -
                                      burst_req_i.dst[OffsetWidth-1:0];

            // assertions
            // pragma translate_off
            `ifndef VERILATOR
            assert property (@(posedge clk_i) disable iff (~rst_ni) 
                    (valid_i |-> burst_req_i.burst_src inside {axi_pkg::BURST_INCR})) else
                $fatal(1, "Unsupported DMA src_burst request..");
            assert property (@(posedge clk_i) disable iff (~rst_ni) 
                    (valid_i |-> burst_req_i.burst_dst inside {axi_pkg::BURST_INCR})) else
                $fatal(1, "Unsupported DMA dst_burst request.");
            `endif
            // pragma translate_on
        end
    end

    //--------------------------------------
    // State
    //--------------------------------------     
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin 
            burst_q.decouple_rw        <= '0;
            burst_q.deburst            <= '0;
            burst_q.shift              <= '0;
            burst_q.src                <= '0;
            burst_q.dst                <= '0;
        end else begin
            burst_q.decouple_rw        <= burst_d.decouple_rw;
            burst_q.deburst            <= burst_d.deburst;
            burst_q.shift              <= burst_d.shift;
            // couple read and write machines in the coupled test
            if (burst_d.decouple_rw) begin
                if (r_ready_i)              burst_q.src <= burst_d.src;
                if (w_ready_i)              burst_q.dst <= burst_d.dst;
            end else begin
                if (r_ready_i & w_ready_i)  burst_q.src <= burst_d.src;
                if (w_ready_i & r_ready_i)  burst_q.dst <= burst_d.dst; 
            end               
        end
    end
endmodule : axi_dma_burst_reshaper
