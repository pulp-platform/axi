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

/// Data path for the AXI DMA. This modules handles the R/W channel of the
/// AXI protocol.
/// Module gets read stream, realigns data and emits a write stream.
/// AXI-like valid/ready handshaking is used to communicate with the rest 
/// of the backend.
module axi_dma_data_path #(
    /// Data width of the AXI bus
    parameter int DataWidth = -1,
    /// Number of elements the realignment buffer can hold. To achieve
    /// full performance a depth of 3 is minimally required.
    parameter int BufferDepth = -1,
    // DO NOT OVERWRITE THIS PARAMETER
    parameter int StrbWidth = DataWidth / 8,
    parameter int OffsetWidth = $clog2(StrbWidth)
) (
    // status signals
    /// Clock
    input  logic                   clk_i,
    /// Asynchronous reset, active low
    input  logic                   rst_ni,

    // handshaking signals
    /// Handshake: read side of data path is presented with a valid request
    input  logic                   r_dp_valid_i,
    /// Handshake: read side of data path is ready to accept new requests
    output logic                   r_dp_ready_o,
    /// Handshake: write side of data path is presented with a valid request
    input  logic                   w_dp_valid_i,
    /// Handshake: write side of data path is ready to accept new requests
    output logic                   w_dp_ready_o,

    // status signal
    /// High if the data path is idle
    output logic                   data_path_idle_o,

    // r-channel
    /// Read data from the AXI bus
    input  logic [DataWidth-1:0]   r_data_i,
    /// Valid signal of the AXI r channel
    input  logic                   r_valid_i,
    /// Last signal of the AXI r channel
    input  logic                   r_last_i,
    /// Response signal of the AXI r channel
    input  logic [            1:0] r_resp_i,
    /// Ready signal of the AXI r channel
    output logic                   r_ready_o,

    /// number of bytes the end of the read transfer is short to reach a 
    /// Bus-aligned boundary
    input  logic [OffsetWidth-1:0] r_tailer_i,
    /// number of bytes the read transfers starts after a 
    /// Bus-aligned boundary    
    input  logic [OffsetWidth-1:0] r_offset_i,
    /// The amount the read data has to be shifted to write-align it
    input  logic [OffsetWidth-1:0] r_shift_i,

    // w-channel
    /// Write data of the AXI bus
    output logic [DataWidth-1:0]   w_data_o,
    /// Write strobe of the AXI bus
    output logic [StrbWidth-1:0]   w_strb_o,
    /// Valid signal of the AXI w channel
    output logic                   w_valid_o,
    /// Last signal of the AXI w channel
    output logic                   w_last_o,
    /// Ready signal of the AXI w channel
    input  logic                   w_ready_i,

    /// number of bytes the write transfers starts after a 
    /// Bus-aligned boundary   
    input  logic [OffsetWidth-1:0] w_offset_i,
    /// number of bytes the end of the write transfer is short to reach a 
    /// Bus-aligned boundary
    input  logic [OffsetWidth-1:0] w_tailer_i,
    /// Number of beats requested by this transfer
    input  logic [            7:0] w_num_beats_i,
    /// True if the transfer only consists of a single beat
    input  logic                   w_is_single_i
); 

    // buffer contains 8 data bits per FIFO
    // buffer is at least 3 deep to prevent stalls

    // 64 bit DATA Width example:
    // DDDDDDDD DDDDDDDD DDDDDDDD DDDDDDDD DDDDDDDD DDDDDDDD DDDDDDDD DDDDDDDD <- head
    // DDDDDDDD DDDDDDDD DDDDDDDD DDDDDDDD DDDDDDDD DDDDDDDD DDDDDDDD DDDDDDDD
    // DDDDDDDD DDDDDDDD DDDDDDDD DDDDDDDD DDDDDDDD DDDDDDDD DDDDDDDD DDDDDDDD <- tail
    // -byte7--|-byte6--|-byte5--|-byte4--|-byte3--|-byte2--|-byte1--|-byte0--|


    //--------------------------------------
    // Mask pre-calculation
    //-------------------------------------- 
    // in contiguous transfers that are unaligned, there will be some 
    // invalid bytes at the beginning and the end of the stream
    // example: 25B in 64 bit system
    // iiiivvvv|vvvvvvvv|vvvvvvvv|vvvvviii
    // last msk|----full mask----|first msk

    // offsets needed for masks to fill/empty buffer
    logic [StrbWidth-1:0] r_first_mask;
    logic [StrbWidth-1:0] r_last_mask;
    logic [StrbWidth-1:0] w_first_mask;
    logic [StrbWidth-1:0] w_last_mask;

    // read align masks
    assign r_first_mask = '1 << r_offset_i;
    assign r_last_mask  = '1 >> (StrbWidth - r_tailer_i);

    // write align masks
    assign w_first_mask = '1 << w_offset_i;
    assign w_last_mask  = '1 >> (StrbWidth - w_tailer_i);


    //--------------------------------------
    // Barrel shifter
    //-------------------------------------- 
    // data arrives in chuncks of length DATA_WDITH, the buffer will be filled with
    // the realigned data. StrbWidth bytes will be inserted starting from the
    // provided address, overflows will naturally wrap

    // signals connected to the buffer
    logic [StrbWidth-1:0][7:0] buffer_in;

    // read aligned in mask. needs to be rotated together with the data before 
    // it can be used to fill in valid data into the buffer
    logic [StrbWidth-1:0]      read_aligned_in_mask;

    // in mask is write aligned, so it is the result of the read aligned in mask
    // that is rotated together with the data in the barrel shifter
    logic [StrbWidth-1:0]      in_mask;

    // a barrel shifter is a concatenation of the same array with itself and a normal
    // shift. 
    assign buffer_in = {r_data_i, r_data_i} >> (r_shift_i * 8);
    assign in_mask   = {read_aligned_in_mask, read_aligned_in_mask}  >> r_shift_i;

    //--------------------------------------
    // In mask generation
    //-------------------------------------- 
    // in the case of unaligned reads -> not all data is valid
    logic is_first_r, is_first_r_d;

    always_comb begin : proc_in_mask_generator
        // default case: all ones
        read_aligned_in_mask = '1;
        // is first word: some bytes at the beginning may be invalid
        read_aligned_in_mask = is_first_r ?
            read_aligned_in_mask & r_first_mask : read_aligned_in_mask;
        // is last word in write burst: some bytes at the end may be invalid
        if (r_tailer_i != '0) begin
            read_aligned_in_mask = r_last_i ?
                read_aligned_in_mask & r_last_mask : read_aligned_in_mask;
        end
    end

    //--------------------------------------
    // Read control
    //-------------------------------------- 
    logic [StrbWidth-1:0] buffer_full;
    logic [StrbWidth-1:0] buffer_push;
    logic                 full;
    // this signal is used for pushing data to the control fifo
    logic                 push;

    always_comb begin : proc_read_control
        // sticky is first bit for read
        if (r_valid_i & !r_last_i) begin
            // new transfer has started
            is_first_r_d = 1'b0;
        end else if (r_last_i & r_valid_i) begin
            // finish read burst
            is_first_r_d = 1'b1;
        end else begin
            // no change
            is_first_r_d = is_first_r;
        end

        // the buffer can be pushed to if all the masked fifo buffers (in_mask) are not full.
        full = |(buffer_full & in_mask);
        // the read can accept data if the buffer is not full
        r_ready_o = ~full;

        // once valid data is applied, it can be pushed in all the selected (in_mask) buffers
        push        = r_valid_i && ~full;
        buffer_push = push ? in_mask : '0;
        
        // r_dp_ready_o is triggered by the last element arriving from the read
        r_dp_ready_o = r_dp_valid_i && r_last_i && r_valid_i && ~full;; 
    end

    //--------------------------------------
    // Out mask generation -> wstrb mask
    //-------------------------------------- 
    // only pop the data actually needed for write from the buffer,
    // determine valid data to pop by calculation the wstrb
    logic [StrbWidth-1:0] out_mask;
    logic                      is_first_w;
    logic                      is_last_w;

    always_comb begin : proc_out_mask_generator
        // default case: all ones
        out_mask = '1;
        // is first word: some bytes at the beginning may be invalid
        out_mask = is_first_w ? (out_mask & w_first_mask) : out_mask;
        // is last word in write burst: some bytes at the end may be invalid
        if (w_tailer_i != '0) begin
            out_mask = is_last_w ? out_mask & w_last_mask : out_mask;
        end
    end

    //--------------------------------------
    // Write control
    //-------------------------------------- 
    // once buffer contains a full line -> all fifos are non-empty
    // push it out.
    // signals connected to the buffer
    logic [StrbWidth-1:0][7:0] buffer_out;
    logic [StrbWidth-1:0]      buffer_empty;
    logic [StrbWidth-1:0]      buffer_pop;

    // write is decoupled from read, due to misalignments in the read/write
    // addresses, page crossing can be encountered at any time.
    // To handle this efficiently, a 2-to-1 or 1-to-2 mapping of r/w beats
    // is required. The write unit needs to keep track of progress through 
    // a counter and cannot use `r_last` for that.
    logic [7:0] w_num_beats_d, w_num_beats_q;
    logic       w_cnt_valid_d, w_cnt_valid_q;

    // data from buffer is popped
    logic       pop;
    // write happens                 
    logic       write_happening;
    // buffer is ready to write the requested data
    logic       ready_to_write;
    // first transfer is possible - this signal is used to detect
    // the first write transfer in a burst
    logic       first_possible;
    // buffer is completely empty
    logic       buffer_clean;

    always_comb begin : proc_write_control
        // counter
        w_num_beats_d   = w_num_beats_q;
        w_cnt_valid_d   = w_cnt_valid_q;
        // buffer ctrl
        pop             = 1'b0;
        buffer_pop      =  'b0;
        write_happening = 1'b0;
        ready_to_write  = 1'b0;
        first_possible  = 1'b0;
        // bus signals
        w_valid_o       = 1'b0;
        w_data_o        =  '0;
        w_strb_o        =  '0;
        w_last_o        = 1'b0;
        // mask control
        is_first_w      = 1'b0;
        is_last_w       = 1'b0;
        // data flow
        w_dp_ready_o    = 1'b0;


        // all elements needed (defined by the mask) are in the buffer and the buffer is non-empty
        ready_to_write  = ((~buffer_empty & out_mask) == out_mask) && (buffer_empty != '1);

        // data needed by the first mask is available in the buffer -> r_first happened for sure
        // this signal can be high during a transfer as well, it needs to be masked
        first_possible  = ((~buffer_empty & w_first_mask) == w_first_mask) && (buffer_empty != '1);

        // the buffer is completely empty (debug only signal)
        buffer_clean    = &(buffer_empty);

        // write happening: both the bus (w_ready) and the buffer (ready_to_write) is high
        write_happening = ready_to_write & w_ready_i;

        // signal the control fifo it could be popped
        pop             = write_happening;

        // the main buffer is conditionally to the write mask popped
        buffer_pop      = write_happening ? out_mask : '0;

        // signal the bus that we are ready
        w_valid_o       = ready_to_write;

        // control the write to the bus apply data to the bus only if data should be written
        if (ready_to_write == 1'b1) begin
            // assign data from buffers, mask out non valid entries
            for (int i = 0; i < StrbWidth; i++) begin
                w_data_o[i*8 +: 8] = out_mask[i] ? buffer_out[i] : 8'b0;   
            end
            // assign the out mask to the strobe
            w_strb_o = out_mask;
        end

        // differentiate between the burst and non-burst case. If a transfer 
        // consists just of one beat the counters are disabled
        if (w_is_single_i) begin
            // in the single case the transfer is both first and last.
            is_first_w = 1'b1;
            is_last_w  = 1'b1;

        // in the bursted case the counters are needed to keep track of the progress of sending
        // beats. The w_last_o depends on the state of the counter
        end else begin
            // first transfer happens as soon as a) the buffer is ready for a first transfer and b) 
            // the counter is currently invalid 
            is_first_w = first_possible & ~w_cnt_valid_q;

            // last happens as soon as a) the counter is valid and b) the counter is now down to 1
            is_last_w  = w_cnt_valid_q & (w_num_beats_q == 8'h01);

            // load the counter with data in a first cycle, only modifying state if bus is ready
            if (is_first_w && write_happening) begin
                w_num_beats_d = w_num_beats_i;
                w_cnt_valid_d = 1'b1;
            end

            // if we hit the last element, invalidate the counter, only modifying state
            // if bus is ready
            if (is_last_w && write_happening) begin
                w_cnt_valid_d = 1'b0;
            end

            // count down the beats if the counter is valid and valid data is written to the bus
            if (w_cnt_valid_q && write_happening) w_num_beats_d = w_num_beats_q - 8'h01;
        end

        // the w_last_o signal should only be applied to the bus if an actual transfer happens
        w_last_o = is_last_w & ready_to_write;

        // we are ready for the next transfer internally, once the w_last_o signal is applied
        w_dp_ready_o = is_last_w & write_happening;
    end


    //--------------------------------------
    // Buffer - implemented as fifo
    //--------------------------------------
    logic control_empty;

    for (genvar i = 0; i < StrbWidth; i++) begin : fifo_buffer
        fifo_v3 #(
            .FALL_THROUGH   ( 1'b0         ),
            .DATA_WIDTH     ( 8            ),
            .DEPTH          ( BufferDepth  )
        ) i_fifo_buffer (
            .clk_i          ( clk_i           ),
            .rst_ni         ( rst_ni          ),
            .flush_i        ( 1'b0            ),
            .testmode_i     ( 1'b0            ),
            .full_o         ( buffer_full [i] ),
            .empty_o        ( buffer_empty[i] ),
            .usage_o        ( ),
            .data_i         ( buffer_in   [i] ),
            .push_i         ( buffer_push [i] ),
            .data_o         ( buffer_out  [i] ),
            .pop_i          ( buffer_pop  [i] )
        );
    end

    //--------------------------------------
    // Module Control
    //-------------------------------------
    assign data_path_idle_o = !(r_dp_valid_i | r_dp_ready_o |
                                w_dp_valid_i | w_dp_ready_o | !buffer_clean);

    always_ff @(posedge clk_i or negedge rst_ni) begin : proc_ff
        if (!rst_ni) begin
            is_first_r    <= 1'b1;
            w_cnt_valid_q <= 1'b0;
            w_num_beats_q <= 8'h0;
        end else begin
            // running_q <= running_d;
            if (r_valid_i & r_ready_o) is_first_r <= is_first_r_d;
            w_cnt_valid_q <= w_cnt_valid_d;
            w_num_beats_q <= w_num_beats_d;
        end
    end

endmodule : axi_dma_data_path
