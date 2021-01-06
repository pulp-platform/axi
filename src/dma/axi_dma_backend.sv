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

/// The backend implements the generic 1D data transfer on an AXI BUS
module axi_dma_backend #(
    /// Data width of the AXI bus
    parameter int unsigned DataWidth = -1,
    /// Address width of the AXI bus
    parameter int unsigned AddrWidth = -1,
    /// ID width of the AXI bus
    parameter int unsigned IdWidth = -1,
    /// Number of AX beats that can be in-flight
    parameter int unsigned AxReqFifoDepth = -1,
    /// Number of generic 1D requests that can be buffered
    parameter int unsigned TransFifoDepth = -1,
    /// Number of elements the realignment buffer can hold. To achieve
    /// full performance a depth of 3 is minimally required.
    parameter int unsigned BufferDepth = -1,
    /// AXI4+ATOP request struct definition.
    parameter type         axi_req_t = logic,
    /// AXI4+ATOP response struct definition.
    parameter type         axi_res_t = logic,
    /// Arbitrary 1D burst request definition:
    /// - `id`: the AXI id used - this id should be constant, as the DMA does not support reordering
    /// - `src`, `dst`: source and destination address, same width as the AXI 4 channels
    /// - `num_bytes`: the length of the contiguous 1D transfer requested, can be up to 32/64 bit long
    ///              num_bytes will be interpreted as an unsigned number
    ///              A value of 0 will cause the backend to discard the transfer prematurely
    /// - `src_cache`, `dst_cache`: the configuration of the cache fields in the AX beats
    /// - `src_burst`, `dst_burst`: currently only incremental bursts are supported (`2'b01`)
    /// - `decouple_rw`: if set to true, there is no longer exactly one AXI write_request issued for
    ///   every read request. This mode can improve performance of unaligned transfers when crossing
    ///   the AXI page boundaries.
    /// - `deburst`: if set, the DMA will split all bursts in single transfers
    /// - `serialize`: if set, the DMA will only send AX belonging to a given Arbitrary 1D burst request
    ///              at a time. This is default behavior to prevent deadlocks. Setting `serialize` to
    ///              zero violates the AXI4+ATOP specification.
    parameter type         burst_req_t = logic,
    /// Give each DMA backend a unique id
    parameter int unsigned DmaIdWidth = -1,
    /// Enable or disable tracing
    parameter bit          DmaTracing = 0

) (
    /// Clock
    input  logic                    clk_i,
    /// Asynchronous reset, active low
    input  logic                    rst_ni,
    /// AXI4+ATOP master request
    output axi_req_t                axi_dma_req_o,
    /// AXI4+ATOP master response
    input  axi_res_t                axi_dma_res_i,
    /// Arbitrary 1D burst request
    input  burst_req_t              burst_req_i,
    /// Handshake: 1D burst request is valid
    input  logic                    valid_i,
    /// Handshake: 1D burst can be accepted
    output logic                    ready_o,
    /// High if the backend is idle
    output logic                    backend_idle_o,
    /// Event: a 1D burst request has completed
    output logic                    trans_complete_o,
    /// unique DMA id
    input  logic [DmaIdWidth-1:0]   dma_id_i
);

    /// Number of bytes per word
    localparam int unsigned StrobeWidth = DataWidth / 8;
    /// Offset width
    localparam int unsigned OffsetWidth = $clog2(StrobeWidth);
    /// Offset type
    typedef logic [OffsetWidth-1:0] offset_t;
    /// Address Type
    typedef logic [  AddrWidth-1:0] addr_t;
    /// AXI ID Type
    typedef logic [    IdWidth-1:0] axi_id_t;

    /// id: AXI id
    /// last: last transaction in burst
    /// address: address of burst
    /// length: burst length
    /// size: bytes in each burst
    /// burst: burst type; only INC supported
    /// cache: cache type
    typedef struct packed {
        axi_id_t          id;
        logic             last;
        addr_t            addr;
        axi_pkg::len_t    len;
        axi_pkg::size_t   size;
        axi_pkg::burst_t  burst;
        axi_pkg::cache_t  cache;
    } desc_ax_t;

    /// offset: initial misalignment
    /// tailer: final misalignment
    /// shift: amount the data needs to be shifted to realign it
    typedef struct packed {
        offset_t offset;
        offset_t tailer;
        offset_t shift;
    } desc_r_t;

    /// offset: initial misalignment
    /// tailer: final misalignment
    /// num_beats: number of beats in the burst
    /// is_single: burst length is 0
    typedef struct packed {
        offset_t       offset;
        offset_t       tailer;
        axi_pkg::len_t num_beats;
        logic          is_single;
    } desc_w_t;

    /// Write request definition
    typedef struct packed {
        desc_ax_t aw;
        desc_w_t  w;
    } write_req_t;

    /// Read request definition
    typedef struct packed {
        desc_ax_t ar;
        desc_r_t  r;
    } read_req_t;

    //--------------------------------------
    // Assertions
    //--------------------------------------
    // pragma translate_off
    `ifndef VERILATOR
    initial begin
        assert (DataWidth inside {16, 32, 64, 128, 256, 512, 1024})
            else $fatal(1, "16 <= DataWidth <= 1024");
        assert (AddrWidth >= 32 & AddrWidth <=   128)
            else $fatal(1, " 8 <= AddrWidth <=   128");
    end
    `endif
    // pragma translate_on

    //--------------------------------------
    // Request Fifo
    //--------------------------------------
    burst_req_t  burst_req;
    logic        burst_req_empty;
    logic        burst_req_pop;
    logic        burst_req_full;

    // buffer the input requests in a fifo
    fifo_v3 #(
        .dtype     ( burst_req_t        ),
        .DEPTH     ( TransFifoDepth     )
    ) i_burst_request_fifo (
        .clk_i     ( clk_i              ),
        .rst_ni    ( rst_ni             ),
        .flush_i   ( 1'b0               ),
        .testmode_i( 1'b0               ),
        .full_o    ( burst_req_full     ),
        .empty_o   ( burst_req_empty    ),
        .usage_o   ( ),
        .data_i    ( burst_req_i        ),
        .push_i    ( valid_i && ready_o ),
        .data_o    ( burst_req          ),
        .pop_i     ( burst_req_pop      )
    );

    assign ready_o = !burst_req_full;

    //--------------------------------------
    // Burst reshaper
    //--------------------------------------
    write_req_t  write_req;
    read_req_t   read_req;

    logic        read_req_valid;
    logic        read_req_ready;
    logic        write_req_valid;
    logic        write_req_ready;

    // send the next burst either immediately or once the last burst
    // has been completed. The former mode is not AXI4+ATOP spec
    // conform and may result in deadlocks!
    logic in_flight_d, in_flight_q;
    logic burst_valid;
    always_comb begin : proc_select_burst_valid
        if (burst_req.serialize) begin
            // AXI4-conform behavior. As both the buffer and the memory system
            // assume in-order operation.
            burst_valid = ~burst_req_empty & (~in_flight_q | trans_complete_o);
        end else begin
            // legacy, non-AXI4-conform behavior. Send as many AX as possible
            // This can lead to deadlocks due to in-memory reordering
            burst_valid = ~burst_req_empty;
        end
    end

    // transforms arbitrary burst into AXI conform bursts
    axi_dma_burst_reshaper #(
        .DataWidth     ( DataWidth     ),
        .AddrWidth     ( AddrWidth     ),
        .IdWidth       ( IdWidth       ),
        .burst_req_t   ( burst_req_t   ),
        .read_req_t    ( read_req_t    ),
        .write_req_t   ( write_req_t   )
    ) i_axi_dma_burst_reshaper (
        .clk_i         ( clk_i              ),
        .rst_ni        ( rst_ni             ),
        .burst_req_i   ( burst_req          ),
        .valid_i       ( burst_valid        ),
        .ready_o       ( burst_req_pop      ),
        .write_req_o   ( write_req          ),
        .read_req_o    ( read_req           ),
        .r_valid_o     ( read_req_valid     ),
        .r_ready_i     ( read_req_ready     ),
        .w_valid_o     ( write_req_valid    ),
        .w_ready_i     ( write_req_ready    )
    );

    //--------------------------------------
    // Data mover
    //--------------------------------------
    axi_dma_data_mover #(
        .DataWidth      ( DataWidth       ),
        .ReqFifoDepth   ( AxReqFifoDepth  ),
        .BufferDepth    ( BufferDepth     ),
        .read_req_t     ( read_req_t      ),
        .write_req_t    ( write_req_t     ),
        .axi_req_t      ( axi_req_t       ),
        .axi_res_t      ( axi_res_t       ),
        .desc_ax_t      ( desc_ax_t       ),
        .desc_r_t       ( desc_r_t        ),
        .desc_w_t       ( desc_w_t        )
    ) i_axi_dma_data_mover (
        .clk_i             ( clk_i             ),
        .rst_ni            ( rst_ni            ),
        .axi_dma_req_o     ( axi_dma_req_o     ),
        .axi_dma_res_i     ( axi_dma_res_i     ),
        .read_req_i        ( read_req          ),
        .write_req_i       ( write_req         ),
        .r_valid_i         ( read_req_valid    ),
        .r_ready_o         ( read_req_ready    ),
        .w_valid_i         ( write_req_valid   ),
        .w_ready_o         ( write_req_ready   ),
        .data_mover_idle_o ( backend_idle_o    ),
        .trans_complete_o  ( trans_complete_o  )
    );

    //--------------------------------------
    // In-flight check
    //--------------------------------------
    // to conform to the AXI4+ATOP spec: only send a burst
    // once the last one has been completed . This check can be overridden
    always_comb begin : proc_in_flight_check

        // default: last state
        in_flight_d = in_flight_q;

        // new transfer: set in-flight to one
        if (burst_req_pop & ~burst_req_empty) begin
            in_flight_d = 1;
        end else begin
            // no new transfer and the old retires -> idle
            if (trans_complete_o) begin
                in_flight_d = 0;
            end
        end
    end

    always_ff @(posedge clk_i or negedge rst_ni) begin : proc_in_flight_check_state
        if(~rst_ni) begin
            in_flight_q <= 0;
        end else begin
            in_flight_q <= in_flight_d;
        end
    end

    //--------------------------------------
    // Tracer
    //--------------------------------------
    //pragma translate_off
    `ifndef SYNTHESYS
    `ifndef VERILATOR
    generate if (DmaTracing) begin : gen_dma_tracer
        string fn;
        integer f;

        logic [DataWidth/8-1:0][BufferDepth-1:0][7:0] buffer_mem;

        // open file
        initial begin
            #1;
            $sformat(fn, "dma_trace_%05x.log", dma_id_i);
            f = $fopen(fn, "w");
            $display("[Tracer] Logging DMA %d to %s", dma_id_i, fn);
        end

        // access buffer memory storage
        for(genvar d = 0; d < BufferDepth; d++) begin
            for(genvar i = 0; i < DataWidth/8-1; i++) begin
                assign buffer_mem[i][d] =
                    i_axi_dma_data_mover.i_axi_dma_data_path.fifo_buffer[i].i_fifo_buffer.mem_q[d];
            end
        end

        // do the tracing
        always_ff @(posedge clk_i) begin : proc_tracer
            // dict
            automatic longint               dma_meta        [string];
            automatic longint               dma_backend     [string];
            automatic longint               dma_burst_res   [string];
            automatic longint               dma_data_mover  [string];
            automatic logic [DataWidth-1:0] dma_data_path   [string];
            automatic string                dma_string;

            // start of python dict
            dma_string = "{";

            // we do not dump while reset
            if (rst_ni) begin

                // commented signals are currently not used by the python golden model :)

                //--------------------------------------
                // Metadata
                //--------------------------------------
                dma_meta = '{
                    // time
                    "time"           : $time(),
                    "DataWidth"      : DataWidth,
                    "AddrWidth"      : AddrWidth,
                    "IdWidth"        : IdWidth,
                    "AxReqFifoDepth" : AxReqFifoDepth,
                    "TransFifoDepth" : TransFifoDepth,
                    "BufferDepth"    : BufferDepth
                };

                //--------------------------------------
                // Backend
                //--------------------------------------
                dma_backend = '{
                    // dma backend interface
                    "backend_burst_req_id"                : burst_req_i.id,
                    "backend_burst_req_src"               : burst_req_i.src,
                    "backend_burst_req_dst"               : burst_req_i.dst,
                    "backend_burst_req_num_bytes"         : burst_req_i.num_bytes,
                    // "backend_burst_req_cache_src"         : burst_req_i.cache_src,
                    // "backend_burst_req_cache_dst"         : burst_req_i.cache_dst,
                    // "backend_burst_req_burst_src"         : burst_req_i.burst_src,
                    // "backend_burst_req_burst_dst"         : burst_req_i.burst_dst,
                    "backend_burst_req_burst_decouple_rw" : burst_req_i.decouple_rw,
                    "backend_burst_req_burst_deburst"     : burst_req_i.deburst,
                    "backend_burst_req_valid"             : valid_i,
                    "backend_burst_req_ready"             : ready_o,
                    "backend_idle"                        : backend_idle_o,
                    "transfer_completed"                  : trans_complete_o
                };

                //--------------------------------------
                // Burst Reshaper
                //--------------------------------------
                dma_burst_res = '{
                    // burst request
                    "burst_reshaper_burst_req_id"          : i_axi_dma_burst_reshaper.burst_req_i.id,
                    "burst_reshaper_burst_req_src"         : i_axi_dma_burst_reshaper.burst_req_i.src,
                    "burst_reshaper_burst_req_dst"         : i_axi_dma_burst_reshaper.burst_req_i.dst,
                    "burst_reshaper_burst_req_num_bytes"   : i_axi_dma_burst_reshaper.burst_req_i.num_bytes,
                    // "burst_reshaper_burst_req_cache_src"   : i_axi_dma_burst_reshaper.burst_req_i.cache_src,
                    // "burst_reshaper_burst_req_cache_dst"   : i_axi_dma_burst_reshaper.burst_req_i.cache_dst,
                    // "burst_reshaper_burst_req_burst_src"   : i_axi_dma_burst_reshaper.burst_req_i.burst_src,
                    // "burst_reshaper_burst_req_burst_dst"   : i_axi_dma_burst_reshaper.burst_req_i.burst_dst,
                    "burst_reshaper_burst_req_decouple_rw" : i_axi_dma_burst_reshaper.burst_req_i.decouple_rw,
                    "burst_reshaper_burst_req_deburst"     : i_axi_dma_burst_reshaper.burst_req_i.deburst,
                    "burst_reshaper_burst_req_valid"       : i_axi_dma_burst_reshaper.valid_i,
                    "burst_reshaper_burst_req_ready"       : i_axi_dma_burst_reshaper.ready_o,
                    // write request
                    "burst_reshaper_write_req_aw_id"       : i_axi_dma_burst_reshaper.write_req_o.aw.id,
                    "burst_reshaper_write_req_aw_last"     : i_axi_dma_burst_reshaper.write_req_o.aw.last,
                    "burst_reshaper_write_req_aw_addr"     : i_axi_dma_burst_reshaper.write_req_o.aw.addr,
                    "burst_reshaper_write_req_aw_len"      : i_axi_dma_burst_reshaper.write_req_o.aw.len,
                    "burst_reshaper_write_req_aw_size"     : i_axi_dma_burst_reshaper.write_req_o.aw.size,
                    "burst_reshaper_write_req_aw_burst"    : i_axi_dma_burst_reshaper.write_req_o.aw.burst,
                    "burst_reshaper_write_req_aw_cache"    : i_axi_dma_burst_reshaper.write_req_o.aw.cache,
                    "burst_reshaper_write_req_w_offset"    : i_axi_dma_burst_reshaper.write_req_o.w.offset,
                    "burst_reshaper_write_req_w_tailer"    : i_axi_dma_burst_reshaper.write_req_o.w.tailer,
                    "burst_reshaper_write_req_w_num_beats" : i_axi_dma_burst_reshaper.write_req_o.w.num_beats,
                    // "burst_reshaper_write_req_w_is_single" : i_axi_dma_burst_reshaper.write_req_o.w.is_single,
                    "burst_reshaper_write_req_valid"       : i_axi_dma_burst_reshaper.w_valid_o,
                    "burst_reshaper_write_req_ready"       : i_axi_dma_burst_reshaper.w_ready_i,
                    // read request
                    "burst_reshaper_read_req_ar_id"        : i_axi_dma_burst_reshaper.read_req_o.ar.id,
                    "burst_reshaper_read_req_ar_last"      : i_axi_dma_burst_reshaper.read_req_o.ar.last,
                    "burst_reshaper_read_req_ar_addr"      : i_axi_dma_burst_reshaper.read_req_o.ar.addr,
                    "burst_reshaper_read_req_ar_len"       : i_axi_dma_burst_reshaper.read_req_o.ar.len,
                    "burst_reshaper_read_req_ar_size"      : i_axi_dma_burst_reshaper.read_req_o.ar.size,
                    "burst_reshaper_read_req_ar_burst"     : i_axi_dma_burst_reshaper.read_req_o.ar.burst,
                    "burst_reshaper_read_req_ar_cache"     : i_axi_dma_burst_reshaper.read_req_o.ar.cache,
                    "burst_reshaper_read_req_r_offset"     : i_axi_dma_burst_reshaper.read_req_o.r.offset,
                    "burst_reshaper_read_req_r_tailer"     : i_axi_dma_burst_reshaper.read_req_o.r.tailer,
                    "burst_reshaper_read_req_r_shift"      : i_axi_dma_burst_reshaper.read_req_o.r.shift,
                    "burst_reshaper_read_req_valid"        : i_axi_dma_burst_reshaper.r_valid_o,
                    "burst_reshaper_read_req_ready"        : i_axi_dma_burst_reshaper.r_ready_i// ,
                    // current burst
                    // "burst_reshaper_burst_src_id"          : i_axi_dma_burst_reshaper.burst_q.src.id,
                    // "burst_reshaper_burst_src_addr"        : i_axi_dma_burst_reshaper.burst_q.src.addr,
                    // "burst_reshaper_burst_src_num_bytes"   : i_axi_dma_burst_reshaper.burst_q.src.num_bytes,
                    // "burst_reshaper_burst_src_cache"       : i_axi_dma_burst_reshaper.burst_q.src.cache,
                    // "burst_reshaper_burst_src_burst"       : i_axi_dma_burst_reshaper.burst_q.src.burst,
                    // "burst_reshaper_burst_src_valid"       : i_axi_dma_burst_reshaper.burst_q.src.valid,
                    // "burst_reshaper_burst_dst_id"          : i_axi_dma_burst_reshaper.burst_q.dst.id,
                    // "burst_reshaper_burst_dst_addr"        : i_axi_dma_burst_reshaper.burst_q.dst.addr,
                    // "burst_reshaper_burst_dst_num_bytes"   : i_axi_dma_burst_reshaper.burst_q.dst.num_bytes,
                    // "burst_reshaper_burst_dst_cache"       : i_axi_dma_burst_reshaper.burst_q.dst.cache,
                    // "burst_reshaper_burst_dst_burst"       : i_axi_dma_burst_reshaper.burst_q.dst.burst,
                    // "burst_reshaper_burst_dst_valid"       : i_axi_dma_burst_reshaper.burst_q.dst.valid,
                    // "burst_reshaper_burst_shift"           : i_axi_dma_burst_reshaper.burst_q.shift,
                    // "burst_reshaper_burst_decouple_rw"     : i_axi_dma_burst_reshaper.burst_q.decouple_rw,
                    // "burst_reshaper_burst_deburst"         : i_axi_dma_burst_reshaper.burst_q.deburst,
                    // page
                    // "burst_reshaper_r_page_offset"         : i_axi_dma_burst_reshaper.r_page_offset,
                    // "burst_reshaper_r_num_bytes_to_pb"     : i_axi_dma_burst_reshaper.r_num_bytes_to_pb,
                    // "burst_reshaper_w_page_offset"         : i_axi_dma_burst_reshaper.w_page_offset,
                    // "burst_reshaper_w_num_bytes_to_pb"     : i_axi_dma_burst_reshaper.w_num_bytes_to_pb,
                    // "burst_reshaper_c_num_bytes_to_pb"     : i_axi_dma_burst_reshaper.c_num_bytes_to_pb,
                    // issue process
                    // "burst_reshaper_r_num_bytes_possible"  : i_axi_dma_burst_reshaper.r_num_bytes_possible,
                    // "burst_reshaper_r_num_bytes"           : i_axi_dma_burst_reshaper.r_num_bytes,
                    // "burst_reshaper_r_finish"              : i_axi_dma_burst_reshaper.r_finish,
                    // "burst_reshaper_r_addr_offset"         : i_axi_dma_burst_reshaper.r_addr_offset,
                    // "burst_reshaper_w_num_bytes_possible"  : i_axi_dma_burst_reshaper.w_num_bytes_possible,
                    // "burst_reshaper_w_num_bytes"           : i_axi_dma_burst_reshaper.w_num_bytes,
                    // "burst_reshaper_w_finish"              : i_axi_dma_burst_reshaper.w_finish,
                    // "burst_reshaper_w_addr_offset"         : i_axi_dma_burst_reshaper.w_addr_offset
                };

                //--------------------------------------
                // Data Mover
                //--------------------------------------
                dma_data_mover = '{
                    // AR emitter
                    // "data_mover_ar_emitter_full"                 : i_axi_dma_data_mover.ar_emitter_full,
                    // "data_mover_ar_emitter_empty"                : i_axi_dma_data_mover.ar_emitter_empty,
                    // "data_mover_ar_emitter_push"                 : i_axi_dma_data_mover.ar_emitter_push,
                    // "data_mover_ar_emitter_pop"                  : i_axi_dma_data_mover.ar_emitter_pop,
                    // AW emitter
                    // "data_mover_aw_emitter_full"                 : i_axi_dma_data_mover.aw_emitter_full,
                    // "data_mover_aw_emitter_empty"                : i_axi_dma_data_mover.aw_emitter_empty,
                    // "data_mover_aw_emitter_push"                 : i_axi_dma_data_mover.aw_emitter_push,
                    // "data_mover_aw_emitter_pop"                  : i_axi_dma_data_mover.aw_emitter_pop,
                    // "data_mover_is_last_aw"                      : i_axi_dma_data_mover.is_last_aw,
                    // R emitter
                    // "data_mover_r_emitter_full"                  : i_axi_dma_data_mover.r_emitter_full,
                    // "data_mover_r_emitter_empty"                 : i_axi_dma_data_mover.r_emitter_empty,
                    // "data_mover_r_emitter_push"                  : i_axi_dma_data_mover.r_emitter_push,
                    // "data_mover_r_emitter_pop"                   : i_axi_dma_data_mover.r_emitter_pop,
                    // W emitter
                    // "data_mover_w_emitter_full"                  : i_axi_dma_data_mover.w_emitter_full,
                    // "data_mover_w_emitter_empty"                 : i_axi_dma_data_mover.w_emitter_empty,
                    // "data_mover_w_emitter_push"                  : i_axi_dma_data_mover.w_emitter_push,
                    // "data_mover_w_emitter_pop"                   : i_axi_dma_data_mover.w_emitter_pop,
                    // AW AXI signals
                    // "axi_dma_bus_aw_id"                          : i_axi_dma_data_mover.axi_dma_req_o.aw.id,
                    // "axi_dma_bus_aw_addr"                        : i_axi_dma_data_mover.axi_dma_req_o.aw.addr,
                    "axi_dma_bus_aw_len"                         : i_axi_dma_data_mover.axi_dma_req_o.aw.len,
                    "axi_dma_bus_aw_size"                        : i_axi_dma_data_mover.axi_dma_req_o.aw.size,
                    // "axi_dma_bus_aw_burst"                       : i_axi_dma_data_mover.axi_dma_req_o.aw.burst,
                    // "axi_dma_bus_aw_cache"                       : i_axi_dma_data_mover.axi_dma_req_o.aw.cache,
                    "axi_dma_bus_aw_valid"                       : i_axi_dma_data_mover.axi_dma_req_o.aw_valid,
                    "axi_dma_bus_aw_ready"                       : i_axi_dma_data_mover.axi_dma_res_i.aw_ready,
                    // B AXI signals
                    "axi_dma_bus_b_ready"                        : i_axi_dma_data_mover.axi_dma_req_o.b_ready,
                    "axi_dma_bus_b_valid"                        : i_axi_dma_data_mover.axi_dma_res_i.b_valid,
                    // AR AXI signals
                    // "axi_dma_bus_ar_id"                          : i_axi_dma_data_mover.axi_dma_req_o.ar.id,
                    // "axi_dma_bus_ar_addr"                        : i_axi_dma_data_mover.axi_dma_req_o.ar.addr,
                    "axi_dma_bus_ar_len"                         : i_axi_dma_data_mover.axi_dma_req_o.ar.len,
                    "axi_dma_bus_ar_size"                        : i_axi_dma_data_mover.axi_dma_req_o.ar.size,
                    // "axi_dma_bus_ar_burst"                       : i_axi_dma_data_mover.axi_dma_req_o.ar.burst,
                    // "axi_dma_bus_ar_cache"                       : i_axi_dma_data_mover.axi_dma_req_o.ar.cache,
                    "axi_dma_bus_ar_valid"                       : i_axi_dma_data_mover.axi_dma_req_o.ar_valid,
                    "axi_dma_bus_ar_ready"                       : i_axi_dma_data_mover.axi_dma_res_i.ar_ready
                };

                //--------------------------------------
                // Data Path
                //--------------------------------------
                dma_data_path = '{
                    // r channel
                    "data_path_r_dp_valid"                       : i_axi_dma_data_mover.i_axi_dma_data_path.r_dp_valid_i,
                    "data_path_r_dp_ready"                       : i_axi_dma_data_mover.i_axi_dma_data_path.r_dp_ready_o,
                    "data_path_r_tailer_i"                       : i_axi_dma_data_mover.i_axi_dma_data_path.r_tailer_i,
                    "data_path_r_offset_i"                       : i_axi_dma_data_mover.i_axi_dma_data_path.r_offset_i,
                    "data_path_r_shift_i"                        : i_axi_dma_data_mover.i_axi_dma_data_path.r_shift_i,
                    "axi_dma_bus_r_valid"                        : i_axi_dma_data_mover.i_axi_dma_data_path.r_valid_i,
                    // "axi_dma_bus_r_data"                         : i_axi_dma_data_mover.i_axi_dma_data_path.r_data_i,
                    // "axi_dma_bus_r_last"                         : i_axi_dma_data_mover.i_axi_dma_data_path.r_last_i,
                    // "axi_dma_bus_r_resp"                         : i_axi_dma_data_mover.i_axi_dma_data_path.r_resp_i,
                    "axi_dma_bus_r_ready"                        : i_axi_dma_data_mover.i_axi_dma_data_path.r_ready_o,
                    // w channel
                    "data_path_w_dp_valid"                       : i_axi_dma_data_mover.i_axi_dma_data_path.w_dp_valid_i,
                    "data_path_w_dp_ready"                       : i_axi_dma_data_mover.i_axi_dma_data_path.w_dp_ready_o,
                    "data_path_w_tailer_i"                       : i_axi_dma_data_mover.i_axi_dma_data_path.w_tailer_i,
                    "data_path_w_offset_i"                       : i_axi_dma_data_mover.i_axi_dma_data_path.w_offset_i,
                    "data_path_w_num_beats"                      : i_axi_dma_data_mover.i_axi_dma_data_path.w_num_beats_i,
                    "data_path_w_is_single"                      : i_axi_dma_data_mover.i_axi_dma_data_path.w_is_single_i,
                    "axi_dma_bus_w_valid"                        : i_axi_dma_data_mover.i_axi_dma_data_path.w_valid_o,
                    // "axi_dma_bus_w_data"                         : i_axi_dma_data_mover.i_axi_dma_data_path.w_data_o,
                    "axi_dma_bus_w_strb"                         : i_axi_dma_data_mover.i_axi_dma_data_path.w_strb_o,
                    // "axi_dma_bus_w_last"                         : i_axi_dma_data_mover.i_axi_dma_data_path.w_last_o,
                    "axi_dma_bus_w_ready"                        : i_axi_dma_data_mover.i_axi_dma_data_path.w_ready_i,
                    // mask pre-calculation
                    "data_path_r_first_mask"                     : i_axi_dma_data_mover.i_axi_dma_data_path.r_first_mask,
                    "data_path_r_last_mask"                      : i_axi_dma_data_mover.i_axi_dma_data_path.r_last_mask,
                    "data_path_w_first_mask"                     : i_axi_dma_data_mover.i_axi_dma_data_path.w_first_mask,
                    "data_path_w_last_mask"                      : i_axi_dma_data_mover.i_axi_dma_data_path.w_last_mask,
                    // barrel shifter
                    // "data_path_buffer_in"                        : i_axi_dma_data_mover.i_axi_dma_data_path.buffer_in,
                    "data_path_read_aligned_in_mask"             : i_axi_dma_data_mover.i_axi_dma_data_path.read_aligned_in_mask,
                    "data_path_write_aligned_in_mask"            : i_axi_dma_data_mover.i_axi_dma_data_path.in_mask,
                    // in mask generation
                    // "data_path_is_first_r"                       : i_axi_dma_data_mover.i_axi_dma_data_path.is_first_r,
                    // "data_path_is_first_r_d"                     : i_axi_dma_data_mover.i_axi_dma_data_path.is_first_r_d,
                    // "data_path_is_first_r_d"                     : i_axi_dma_data_mover.i_axi_dma_data_path.is_first_r_d,
                    // read control
                    // "data_path_buffer_full"                      : i_axi_dma_data_mover.i_axi_dma_data_path.buffer_full,
                    // "data_path_buffer_push"                      : i_axi_dma_data_mover.i_axi_dma_data_path.buffer_push,
                    // "data_path_full"                             : i_axi_dma_data_mover.i_axi_dma_data_path.full,
                    "data_path_push"                             : i_axi_dma_data_mover.i_axi_dma_data_path.push,
                    // out mask generation
                    "data_path_out_mask"                         : i_axi_dma_data_mover.i_axi_dma_data_path.out_mask,
                    // "data_path_is_first_w"                       : i_axi_dma_data_mover.i_axi_dma_data_path.is_first_w,
                    // "data_path_is_last_w"                        : i_axi_dma_data_mover.i_axi_dma_data_path.is_last_w,
                    // write control
                    // "data_path_buffer_out"                       : i_axi_dma_data_mover.i_axi_dma_data_path.buffer_out,
                    // "data_path_buffer_empty"                     : i_axi_dma_data_mover.i_axi_dma_data_path.buffer_empty,
                    // "data_path_buffer_pop"                       : i_axi_dma_data_mover.i_axi_dma_data_path.buffer_pop,
                    // "data_path_w_num_beats"                      : i_axi_dma_data_mover.i_axi_dma_data_path.w_num_beats_q,
                    // "data_path_w_cnt_valid"                      : i_axi_dma_data_mover.i_axi_dma_data_path.w_cnt_valid_q,
                    "data_path_pop"                              : i_axi_dma_data_mover.i_axi_dma_data_path.pop// ,
                    // "data_path_write_happening"                  : i_axi_dma_data_mover.i_axi_dma_data_path.write_happening,
                    // "data_path_ready_to_write"                   : i_axi_dma_data_mover.i_axi_dma_data_path.ready_to_write,
                    // "data_path_first_possible"                   : i_axi_dma_data_mover.i_axi_dma_data_path.first_possible,
                    // "data_path_buffer_clean"                     : i_axi_dma_data_mover.i_axi_dma_data_path.buffer_clean
                };

                // write dicts to string
                foreach(dma_meta[key])       dma_string = $sformatf("%s'%s': 0x%0x, ", dma_string, key, dma_meta[key]);
                // only write bulk of data if dma is actually active :)
                if (!backend_idle_o | valid_i & ready_o | i_axi_dma_burst_reshaper.valid_i & i_axi_dma_burst_reshaper.ready_o |
                    i_axi_dma_burst_reshaper.burst_q.src.valid | i_axi_dma_burst_reshaper.burst_q.dst.valid |  trans_complete_o) begin
                    foreach(dma_backend[key])    dma_string = $sformatf("%s'%s': 0x%0x, ", dma_string, key, dma_backend[key]);
                    foreach(dma_burst_res[key])  dma_string = $sformatf("%s'%s': 0x%0x, ", dma_string, key, dma_burst_res[key]);
                    foreach(dma_data_mover[key]) dma_string = $sformatf("%s'%s': 0x%0x, ", dma_string, key, dma_data_mover[key]);
                    foreach(dma_data_path[key])  dma_string = $sformatf("%s'%s': 0x%0x, ", dma_string, key, dma_data_path[key]);

                    //--------------------------------------
                    // Realign Buffer Data Store
                    //--------------------------------------
                    // for(int d = 0; d < BUFFER_DEPTH; d++) begin
                    //     for(int i = 0; i < DATA_WIDTH/8; i++) begin
                    //         dma_string = $sformatf("%s'buffer_mem_%0d_level_%0d': 0x%0x, ",
                    //                      dma_string, i, d, buffer_mem[i][d]
                    //         );
                    //     end
                    // end
                end
                dma_string = $sformatf("%s}", dma_string);
                $fwrite(f, dma_string);
                $fwrite(f, "\n");
            end
        end
        // close the file
        final begin
            $fclose(f);
        end
    end
    endgenerate
    `endif
    `endif
    //pragma translate_on
endmodule : axi_dma_backend
