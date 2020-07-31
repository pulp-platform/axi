module log_barrel_shifter_tb();


    localparam int unsigned NumInputs  = 8;
    localparam int unsigned ShiftWidth = cf_math_pkg::idx_width(NumInputs);
    typedef logic[7:0] data_t;

    logic[ShiftWidth-1:0] shift_i;
    data_t [NumInputs-1:0] data_i;
    data_t [NumInputs-1:0] data_o;


    initial begin
        data_i  = 64'hdeadbeefcafebabe;
        shift_i = 0;

        for(int i = 0; i < 255; i++) begin
            #1;
            shift_i = i;
            #0;
            $display("%h < %h", data_o, shift_i);
        end
        #20;
        $stop();
    end



    log_barrel_shifter #(
        .NumInputs ( NumInputs  ), 
        .data_t    ( data_t     )
    ) i_log_barrel_shifter (
        .shift_i   ( shift_i    ),
        .data_i    ( data_i     ),
        .data_o    ( data_o     )
    );

endmodule : log_barrel_shifter_tb
