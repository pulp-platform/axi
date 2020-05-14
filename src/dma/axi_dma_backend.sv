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
    parameter int unsigned DATA_WIDTH         = -1,
    /// Address width of the AXI bus
    parameter int unsigned ADDR_WIDTH         = -1,
    /// ID width of the AXI bus
    parameter int unsigned ID_WIDTH           = -1,
    /// Number of AX beats that can be in-flight
    parameter int unsigned AXI_REQ_FIFO_DEPTH = -1,
    /// Number of generic 1D requests that can be buffered
    parameter int unsigned REQ_FIFO_DEPTH     = -1,
    /// Number of elements the realignment buffer can hold. To achieve
    /// full performance a depth of 3 is minimally required.
    parameter int unsigned BUFFER_DEPTH       = -1,
    /// AXI4+ATOP request struct definition.
    parameter type         axi_req_t          = logic,
    /// AXI4+ATOP response struct definition.
    parameter type         axi_res_t          = logic,
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
    parameter type         burst_req_t        = logic

) (
    /// Clock
    input  logic        clk_i,
    /// Asynchronous reset, active low
    input  logic        rst_ni,
    // AXI4 bus
    /// AXI4+ATOP master request
    output axi_req_t    axi_dma_req_o,
    /// AXI4+ATOP master response
    input  axi_res_t    axi_dma_res_i,
    // arbitrary 1D burst request
    /// Arbitrary 1D burst request
    input  burst_req_t  burst_req_i,
    // handshaking 
    /// Handshake: 1D burst request is valid
    input  logic        valid_i,
    /// Handshake: 1D burst can be accepted
    output logic        ready_o,
    // status signal
    /// High if the backend is idle
    output logic        backend_idle_o,
    // a 1D burst request has been completed
    /// Event: a 1D burst request has completed
    output logic        trans_complete_o
);
    
    /// Number of bytes per word
    localparam STOBE_WIDTH  = DATA_WIDTH / 8;
    /// Offset width
    localparam OFFSET_WIDTH = $clog2(STOBE_WIDTH);
    /// Offset type
    typedef logic [OFFSET_WIDTH-1:0] offset_t;
    /// Beat type 
    typedef logic [             7:0] beatlen_t;
    /// Address Type
    typedef logic [  ADDR_WIDTH-1:0] addr_t;
    /// AXI ID Type
    typedef logic [    ID_WIDTH-1:0] axi_id_t;
    
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
        offset_t  offset;
        offset_t  tailer;
        beatlen_t num_beats;
        logic     is_single;
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
    // Request Fifo
    //-------------------------------------- 
    burst_req_t  burst_req;
    logic        burst_req_empty;
    logic        burst_req_pop;
    logic        burst_req_full;

    // buffer the input requests in a fifo
    fifo_v3 #(
        .dtype     ( burst_req_t        ),
        .DEPTH     ( REQ_FIFO_DEPTH     )
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

    // transforms arbitrary burst into AXI conform bursts
    axi_dma_burst_reshaper #(
        .DATA_WIDTH    ( DATA_WIDTH    ),
        .ADDR_WIDTH    ( ADDR_WIDTH    ),
        .ID_WIDTH      ( ID_WIDTH      ),
        .burst_req_t   ( burst_req_t   ),
        .read_req_t    ( read_req_t    ),
        .write_req_t   ( write_req_t   )
    ) i_axi_dma_burst_reshaper (
        .clk_i         ( clk_i              ),
        .rst_ni        ( rst_ni             ),
        .burst_req_i   ( burst_req          ),
        .valid_i       ( ~burst_req_empty   ),
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
        .DATA_WIDTH     ( DATA_WIDTH          ),
        .REQ_FIFO_DEPTH ( AXI_REQ_FIFO_DEPTH  ),
        .BUFFER_DEPTH   ( BUFFER_DEPTH        ),
        .read_req_t     ( read_req_t          ),
        .write_req_t    ( write_req_t         ),
        .axi_req_t      ( axi_req_t           ),
        .axi_res_t      ( axi_res_t           ),
        .desc_ax_t      ( desc_ax_t           ),
        .desc_r_t       ( desc_r_t            ),
        .desc_w_t       ( desc_w_t            )
    ) i_axi_dma_data_mover (
        .clk_i             ( clk_i               ),
        .rst_ni            ( rst_ni              ),
        .axi_dma_req_o     ( axi_dma_req_o       ),
        .axi_dma_res_i     ( axi_dma_res_i       ),
        .read_req_i        ( read_req            ),
        .write_req_i       ( write_req           ),
        .r_valid_i         ( read_req_valid      ),
        .r_ready_o         ( read_req_ready      ),
        .w_valid_i         ( write_req_valid     ),
        .w_ready_o         ( write_req_ready     ),
        .data_mover_idle_o ( backend_idle_o      ),
        .trans_complete_o  ( trans_complete_o    )
    );

endmodule : axi_dma_backend
