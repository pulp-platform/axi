module log_barrel_shifter #(
    parameter int unsigned NumInputs  = -1,
    parameter type         data_t     = logic,
    // do not touch !!!
    parameter int unsigned ShiftWidth = (NumInputs > 32'd1) ? unsigned'($clog2(NumInputs)) : 32'd1,
    parameter type         shift_t    = logic[ShiftWidth-1:0]
) (
    input shift_t                   shift_i,
    input  data_t [NumInputs-1:0]   data_i,
    output data_t [NumInputs-1:0]   data_o
);

    function int unsigned wrap (
        input int unsigned idx, 
        input int unsigned local_shift
    );
        return (idx - local_shift) % NumInputs;
    endfunction
 
    // intermediate nodes
    data_t [ShiftWidth-1:0][NumInputs-1:0] data;

    // generate barrel shifter
    for (genvar lvl = 0; unsigned'(lvl) < ShiftWidth; lvl++) begin : gen_levels
        // local shift
        localparam int unsigned LocalShift = 2**lvl;
        // generate nodes
        for (genvar node = 0; unsigned'(node) < NumInputs; node++) begin : gen_nodes
            // the wrapped index of the previous level
            localparam int unsigned ShiftedIdx = wrap (node, LocalShift);
            // connect first level to inputs
            if (lvl == 0) begin : gen_first_level
                assign data[lvl][node] = shift_i[lvl] ? data_i[ShiftedIdx] : data_i[node];
            // internal nodes
            end else begin : gen_internal_level
                assign data[lvl][node] = shift_i[lvl] ? data[lvl-1][ShiftedIdx] : data[lvl-1][node];
            end
        end
    end

    // assign output
    assign data_o = data[ShiftWidth-1];


endmodule : log_barrel_shifter
