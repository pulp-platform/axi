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

/// Module, that controls the AXI bus. Takes two configuration structs (R/W) as an
/// input. Implements the DMA functionality on the AXI bus.
/// R and W config structs need to appear at the input simultaneously; sending a 
/// R config w/o the corresponding W could lead to wrong AXI transfers.
module axi_dma_data_mover #(
    /// Data width of the AXI bus
    parameter int unsigned DataWidth = -1,
    /// Number of AX beats that can be in-flight
    parameter int unsigned ReqFifoDepth = -1,
    /// Number of elements the realignment buffer can hold. To achieve
    /// full performance a depth of 3 is minimally required.
    parameter int unsigned BufferDepth = -1,
    /// AXI4+ATOP request struct definition.
    parameter type         axi_req_t = logic,
    /// AXI4+ATOP response struct definition.
    parameter type         axi_res_t = logic,
    /// ax descriptor
    /// - `id`: AXI id
    /// - `last`: last transaction in burst
    /// - `address`: address of burst
    /// - `length`: burst length
    /// - `size`: bytes in each burst
    /// - `burst`: burst type; only INC supported
    /// - `cache`: cache type
    parameter type         desc_ax_t = logic,
    /// r descriptor
    /// - `offset`: initial misalignment
    /// - `tailer`: final misalignment
    /// - `shift`: amount the data needs to be shifted to realign it
    parameter type         desc_r_t = logic,
    /// w descriptor
    /// - `offset`: initial misalignment
    /// - `tailer`: final misalignment
    /// - `num_beats`: number of beats in the burst
    /// - `is_single`: burst length is 0
    parameter type         desc_w_t = logic,
    /// Read request definition. Includes:
    /// - ax descriptor
    ///  - `id`: AXI id
    ///  - `last`: last transaction in burst
    ///  - `address`: address of burst
    ///  - `length`: burst length
    ///  - `size`: bytes in each burst
    ///  - `burst`: burst type; only INC supported
    ///  - `cache`: cache type
    /// - r descriptor
    ///  - `offset`: initial misalignment
    ///  - `tailer`: final misalignment
    ///  - `shift`: amount the data needs to be shifted to realign it
    parameter type         read_req_t = logic,
    /// Write request definition. Includes:
    /// - ax descriptor
    ///  - `id`: AXI id
    ///  - `last`: last transaction in burst
    ///  - `address`: address of burst
    ///  - `length`: burst length
    ///  - `size`: bytes in each burst
    ///  - `burst`: burst type; only INC supported
    ///  - `cache`: cache type
    /// - w descriptor
    ///  - `offset`: initial misalignment
    ///  - `tailer`: final misalignment
    ///  - `num_beats`: number of beats in the burst
    ///  - `is_single`: burst length is 0
    parameter type         write_req_t = logic
) (
    /// Clock
    input  logic         clk_i,
    /// Asynchronous reset, active low
    input  logic         rst_ni,
    /// AXI4+ATOP master request
    output axi_req_t     axi_dma_req_o,
    /// AXI4+ATOP master response
    input  axi_res_t     axi_dma_res_i,
    /// Read transfer request
    input read_req_t     read_req_i,
    /// Write transfer request
    input write_req_t    write_req_i,
    /// Handshake: read transfer request valid
    input  logic         r_valid_i,
    /// Handshake: read transfer request ready
    output logic         r_ready_o,
    /// Handshake: write transfer request valid
    input  logic         w_valid_i,
    /// Handshake: write transfer request ready
    output logic         w_ready_o,
    /// High if the data mover is idle
    output logic         data_mover_idle_o,
    /// Event: a transaction has completed
    output logic         trans_complete_o
);

    localparam int unsigned StrbWidth = DataWidth / 8;
    // local types
    typedef logic [DataWidth-1:0] data_t;
    typedef logic [StrbWidth-1:0] strb_t;

    //--------------------------------------
    // AR emitter
    //-------------------------------------- 
    // object currently at the tail of the fifo
    desc_ax_t current_ar_req;
    // control signals
    logic ar_emitter_full;
    logic ar_emitter_empty;
    logic ar_emitter_push;
    logic ar_emitter_pop;

    // instanciate a fifo to buffer the address read requests
    fifo_v3 #(
        .FALL_THROUGH  ( 1'b0                 ), 
        .DEPTH         ( ReqFifoDepth         ),
        .dtype         ( desc_ax_t            )
    ) i_fifo_ar_emitter (
        .clk_i         ( clk_i                ),
        .rst_ni        ( rst_ni               ),
        .flush_i       ( 1'b0                 ),
        .testmode_i    ( 1'b0                 ),
        .full_o        ( ar_emitter_full      ),
        .empty_o       ( ar_emitter_empty     ),
        .usage_o       ( ),
        .data_i        ( read_req_i.ar        ),
        .push_i        ( ar_emitter_push      ),
        .data_o        ( current_ar_req       ),
        .pop_i         ( ar_emitter_pop       )
    );

    //--------------------------------------
    // AW emitter
    //-------------------------------------- 
    // object currently at the tail of the fifo
    desc_ax_t current_aw_req;
    // control signals
    logic aw_emitter_full;
    logic aw_emitter_empty;
    logic aw_emitter_push;
    logic aw_emitter_pop;

    // instantiate a fifo to buffer the address write requests
    fifo_v3 #(
        .FALL_THROUGH  ( 1'b0                  ), 
        .dtype         ( desc_ax_t             ), 
        .DEPTH         ( ReqFifoDepth          )
    ) i_fifo_aw_emitter (
        .clk_i         ( clk_i                 ),
        .rst_ni        ( rst_ni                ),
        .flush_i       ( 1'b0                  ),
        .testmode_i    ( 1'b0                  ),
        .full_o        ( aw_emitter_full       ),
        .empty_o       ( aw_emitter_empty      ),
        .usage_o       ( ),
        .data_i        ( write_req_i.aw        ),
        .push_i        ( aw_emitter_push       ),
        .data_o        ( current_aw_req        ),
        .pop_i         ( aw_emitter_pop        )
    );

    //--------------------------------------
    // R emitter
    //-------------------------------------- 
    // object currently at the tail of the fifo
    desc_r_t current_r_req;
    // control signals
    logic r_emitter_full;
    logic r_emitter_empty;
    logic r_emitter_push;
    logic r_emitter_pop;

    // instantiate a fifo to buffer the read requests
    fifo_v3 #(
        .FALL_THROUGH  ( 1'b0                 ), 
        .dtype         ( desc_r_t             ),
        .DEPTH         ( ReqFifoDepth         )
    ) i_fifo_r_emitter (
        .clk_i         ( clk_i                ),
        .rst_ni        ( rst_ni               ),
        .flush_i       ( 1'b0                 ),
        .testmode_i    ( 1'b0                 ),
        .full_o        ( r_emitter_full       ),
        .empty_o       ( r_emitter_empty      ),
        .usage_o       ( ),
        .data_i        ( read_req_i.r         ),
        .push_i        ( r_emitter_push       ),
        .data_o        ( current_r_req        ),
        .pop_i         ( r_emitter_pop        )
    );

    //--------------------------------------
    // W emitter
    //--------------------------------------
    // object currently at the tail of the fifo 
    desc_w_t current_w_req;
    // control signals
    logic w_emitter_full;
    logic w_emitter_empty;
    logic w_emitter_push;
    logic w_emitter_pop;

    // instanciate a fifo to buffer the read requests
    fifo_v3 #(
        .FALL_THROUGH  ( 1'b0                  ), 
        .dtype         ( desc_w_t              ),
        .DEPTH         ( ReqFifoDepth          )
    ) i_fifo_w_emitter (
        .clk_i         ( clk_i                 ),
        .rst_ni        ( rst_ni                ),
        .flush_i       ( 1'b0                  ),
        .testmode_i    ( 1'b0                  ),
        .full_o        ( w_emitter_full        ),
        .empty_o       ( w_emitter_empty       ),
        .usage_o       ( ),
        .data_i        ( write_req_i.w         ),
        .push_i        ( w_emitter_push        ),
        .data_o        ( current_w_req         ),
        .pop_i         ( w_emitter_pop         )
    );

    //--------------------------------------
    // instantiate of the data path
    //--------------------------------------
    // AXI bus signals from and to the datapath 
    data_t          r_data;
    axi_pkg::resp_t r_resp;
    logic           r_last;
    logic           r_valid;
    logic           r_ready;
    data_t          w_data;
    strb_t          w_strb;
    logic           w_valid;
    logic           w_last;
    logic           w_ready;

    logic           w_next;

    axi_dma_data_path #(
        .DataWidth     ( DataWidth         ),
        .BufferDepth   ( BufferDepth       )
    ) i_axi_dma_data_path (
        .clk_i                ( clk_i                    ),
        .rst_ni               ( rst_ni                   ),
        .r_dp_valid_i         ( ~r_emitter_empty         ),
        .r_dp_ready_o         ( r_emitter_pop            ),
        .w_dp_valid_i         ( ~w_emitter_empty         ),
        .w_dp_ready_o         ( w_emitter_pop            ),
        .data_path_idle_o     ( data_mover_idle_o        ),
        // AXI R signals
        .r_data_i             ( r_data                   ),
        .r_valid_i            ( r_valid                  ),
        .r_last_i             ( r_last                   ),
        .r_resp_i             ( r_resp                   ),
        .r_ready_o            ( r_ready                  ),
        // R control
        .r_tailer_i           ( current_r_req.tailer     ),
        .r_offset_i           ( current_r_req.offset     ),
        .r_shift_i            ( current_r_req.shift      ),
        // AXI W signals
        .w_data_o             ( w_data                   ),
        .w_strb_o             ( w_strb                   ),
        .w_valid_o            ( w_valid                  ),
        .w_last_o             ( w_last                   ),
        .w_ready_i            ( w_ready                  ),
        // W control
        .w_offset_i           ( current_w_req.offset     ),
        .w_tailer_i           ( current_w_req.tailer     ),
        .w_num_beats_i        ( current_w_req.num_beats  ),
        .w_is_single_i        ( current_w_req.is_single  )
    );

    //--------------------------------------
    // Refill control
    //-------------------------------------- 
    // the ax and x fifos of both channels are filled
    // together, as request come bundled.
    always_comb begin : proc_refill
        // Read related channels
        r_ready_o          = ~ar_emitter_full & ~r_emitter_full;
        r_emitter_push     = r_valid_i & r_ready_o;
        ar_emitter_push    = r_valid_i & r_ready_o;

        // Write related channels
        w_ready_o          = ~aw_emitter_full & ~w_emitter_full;
        w_emitter_push     = w_valid_i & w_ready_o;
        aw_emitter_push    = w_valid_i & w_ready_o;
    end

    //--------------------------------------
    // Bus control
    //-------------------------------------- 
    // here the AXI bus is unpacked/packed.
    always_comb begin : proc_bus_packer
        // defaults: not used signals -> 0
        axi_dma_req_o = '0;

        // assign R signals
        r_data                 = axi_dma_res_i.r.data;
        r_resp                 = axi_dma_res_i.r.resp;
        r_last                 = axi_dma_res_i.r.last;
        r_valid                = axi_dma_res_i.r_valid;
        axi_dma_req_o.r_ready  = r_ready;

        // assign W signals
        axi_dma_req_o.w.data   = w_data;
        axi_dma_req_o.w.strb   = w_strb;
        axi_dma_req_o.w.last   = w_last;
        axi_dma_req_o.w_valid  = w_valid;
        w_ready                = axi_dma_res_i.w_ready;

        // AW signals
        axi_dma_req_o.aw.id    = current_aw_req.id;
        axi_dma_req_o.aw.addr  = current_aw_req.addr;
        axi_dma_req_o.aw.len   = current_aw_req.len;
        axi_dma_req_o.aw.size  = current_aw_req.size;
        axi_dma_req_o.aw.burst = current_aw_req.burst;
        axi_dma_req_o.aw.cache = current_aw_req.cache;
        // flow control
        axi_dma_req_o.aw_valid = ~aw_emitter_empty;
        aw_emitter_pop         = axi_dma_res_i.aw_ready & axi_dma_req_o.aw_valid;

        // B signals
        // we are always ready to accept b signals, as we do not need them
        // inside the DMA (we don't care if write failed)
        axi_dma_req_o.b_ready = 1'b1;

        // AR signals
        axi_dma_req_o.ar.id    = current_ar_req.id;
        axi_dma_req_o.ar.addr  = current_ar_req.addr;
        axi_dma_req_o.ar.len   = current_ar_req.len;
        axi_dma_req_o.ar.size  = current_ar_req.size;
        axi_dma_req_o.ar.burst = current_ar_req.burst;
        axi_dma_req_o.ar.cache = current_ar_req.cache;
        // flow control
        axi_dma_req_o.ar_valid = ~ar_emitter_empty;
        ar_emitter_pop         = axi_dma_res_i.ar_ready & axi_dma_req_o.ar_valid;
    end

    //--------------------------------------
    // ID control
    //-------------------------------------- 
    logic is_last_aw;
    fifo_v3 #(
        .DEPTH       ( ReqFifoDepth + BufferDepth ),
        .dtype       ( logic                      )
    ) i_last_transaction_queue (
        .clk_i       ( clk_i                 ),
        .rst_ni      ( rst_ni                ),
        .flush_i     ( 1'b0                  ),
        .testmode_i  ( 1'b0                  ),
        .full_o      ( ),
        .empty_o     ( ),
        .usage_o     ( ),
        .data_i      ( current_aw_req.last   ),
        .push_i      ( aw_emitter_pop        ),
        .data_o      ( is_last_aw            ),
        .pop_i       ( axi_dma_res_i.b_valid )
    );
    assign trans_complete_o = is_last_aw & axi_dma_res_i.b_valid;

endmodule : axi_dma_data_mover
