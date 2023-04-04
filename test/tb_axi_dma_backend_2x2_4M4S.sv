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

// top level of the simulation for the AXI DMA backend

`timescale 1ns/1ns
module tb_axi_dma_backend;

    fixture_axi_dma_backend fix ();
    string line;
    int fd,code;
    int dma_id, src_add, dst_add, size;

    initial begin

        fix.reset();
        fix.clear_memory();
        fix.reset_lfsr();

        fd = $fopen("/home/jvikram/crosspoint/axi/test/traces_4cl_tb.txt","r");
        while($fgets(line,fd)) begin
            if(line.match("(\/\/.*)?$"))
                line = line.prematch();
            if (!line.match("[0-f]")) continue;
            code = $sscanf(line,"%h %h %h %h", dma_id, src_add, dst_add, size);
            //$displayh("%h %h %h %h\n", dma_id, src_add, dst_add, size);
            fix.oned_random_launch(4, src_add, dst_add, dma_id, size, 0);
            $display();
        end
        fix.oned_random_launch(4, src_add, dst_add, dma_id, size, 1);

        $display("\nDone with test 1 :D");

        $fclose(fd);
        
        // // ultra short transfers
        // for (int i = 0; i < 20000; i = i + 1) begin
        //     fix.oned_random_launch(4, 0);
        //     $display();
        // end
        // fix.oned_random_launch(4, 1);
        // //fix.compare_memories();
        // $display("\nDone with test 1 :D");
        
        // // medium short transfers
        // for (int i = 0; i < 20000; i = i + 1) begin
        //     fix.oned_random_launch(10, 0);
        //     $display();
        // end
        // fix.oned_random_launch(10, 1);
        // //fix.compare_memories();
        // $display("\nDone with test 2 :D");
        
        // // // short transfers
        // for (int i = 0; i < 25000; i = i + 1) begin
        //     fix.oned_random_launch(100, 0);
        //     $display();
        // end
        // fix.oned_random_launch(100, 1);
        // //fix.compare_memories();
        // $display("\nDone with test 3 :D");
        
        //  // // medium transfers
        // for (int i = 0; i < 1000; i = i + 1) begin
        //     fix.oned_random_launch(1000, 0);
        //     $display();
        // end
        // fix.oned_random_launch(1000, 1);
        // //fix.compare_memories();
        // $display("\nDone with test 4 :D");
        
        // // long transfers
        // for (int i = 0; i < 250; i = i + 1) begin
        //     fix.oned_random_launch(10000, 0);
        //     $display();
        // end
        // fix.oned_random_launch(10000, 1);
        // //fix.compare_memories();
        // $display("\nDone with test 5 :D");
        
        // // ultra long transfers
        // for (int i = 0; i < 100; i = i + 1) begin
        //     fix.oned_random_launch(65000, 0);
        //     $display();
        // end
        // fix.oned_random_launch(65000, 1);
        // //fix.compare_memories();
        // $display("\nDone with test 6 :D");
        
        $display("\nDone :D (in %18.9f seconds", $time() / 1000000000.0);
        $display("SUCCESS");
        $stop();
    end

endmodule

