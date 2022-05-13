
log * -r

add wave -position end -label Clock -color "light blue"  sim:/tb_axi_llc/i_axi_llc_dut/i_aw_splitter/clk_i
add wave -position end -label Reset -color "orange"      sim:/tb_axi_llc/i_axi_llc_dut/i_aw_splitter/rst_ni

add wave -position end -divider "AXI SLV"
add wave -position end -label AXI_SLV_REQ -color "pink"  sim:/tb_axi_llc/i_axi_llc_dut/slv_req_i
add wave -position end -label AXI_SLV_RESP -color "pink" sim:/tb_axi_llc/i_axi_llc_dut/slv_resp_o

add wave -position end -divider "AXI MST"
add wave -position end -label AXI_MST_REQ  sim:/tb_axi_llc/i_axi_llc_dut/mst_req_o
add wave -position end -label AXI_MST_RESP sim:/tb_axi_llc/i_axi_llc_dut/mst_resp_i

add wave -position end -divider "AXI CFG"
add wave -position end -label AXI_MST_REQ  sim:/tb_axi_llc/i_axi_llc_dut/conf_req_i
add wave -position end -label AXI_MST_RESP sim:/tb_axi_llc/i_axi_llc_dut/conf_resp_o

add wave -position end -divider "DESC"
add wave -position end -label "rw_desc"       sim:/tb_axi_llc/i_axi_llc_dut/rw_desc
add wave -position end -label "rw_desc_valid" sim:/tb_axi_llc/i_axi_llc_dut/rw_desc_valid
add wave -position end -label "rw_desc_ready" sim:/tb_axi_llc/i_axi_llc_dut/rw_desc_ready

add wave -position end -divider "DESC"
add wave -position end -label "desc"       sim:/tb_axi_llc/i_axi_llc_dut/desc
add wave -position end -label "hit_valid" sim:/tb_axi_llc/i_axi_llc_dut/hit_valid
add wave -position end -label "hit_ready" sim:/tb_axi_llc/i_axi_llc_dut/hit_ready
add wave -position end -label "miss_valid" sim:/tb_axi_llc/i_axi_llc_dut/miss_valid
add wave -position end -label "miss_ready" sim:/tb_axi_llc/i_axi_llc_dut/miss_ready



add wave -position end -divider "RAM"
add wave -position end -label "way_inp"       sim:/tb_axi_llc/i_axi_llc_dut/to_way
add wave -position end -label "way_inp_valid" sim:/tb_axi_llc/i_axi_llc_dut/to_way_valid
add wave -position end -label "way_inp_ready" sim:/tb_axi_llc/i_axi_llc_dut/to_way_ready
add wave -position end -label "evict_way_out"       sim:/tb_axi_llc/i_axi_llc_dut/evict_way_out
add wave -position end -label "evict_way_out_valid" sim:/tb_axi_llc/i_axi_llc_dut/evict_way_out_valid
add wave -position end -label "read_way_out"        sim:/tb_axi_llc/i_axi_llc_dut/read_way_out
add wave -position end -label "read_way_out_valid"  sim:/tb_axi_llc/i_axi_llc_dut/read_way_out_valid



add wave -position end -divider "RAM CONTENT"
add wave -position end -label "inp_valid_dist" sim:/tb_axi_llc/i_axi_llc_dut/i_llc_ways/way_inp_valid

add wave -position end -label "out_dist" sim:/tb_axi_llc/i_axi_llc_dut/i_llc_ways/way_out
add wave -position end -label "out_valid_dist" sim:/tb_axi_llc/i_axi_llc_dut/i_llc_ways/way_out_valid

#add wave -position end -label "Way7: RAM" sim:/tb_axi_llc/i_axi_llc_dut/i_llc_ways/genblk2[7]/i_data_way/i_data_sram/ram

#add wave -position end -label "Way6: RAM" sim:/tb_axi_llc/i_axi_llc_dut/i_llc_ways/genblk2[6]/i_data_way/i_data_sram/ram
#add wave -position end -label "Way5: RAM" sim:/tb_axi_llc/i_axi_llc_dut/i_llc_ways/genblk2[5]/i_data_way/i_data_sram/ram
#add wave -position end -label "Way4: RAM" sim:/tb_axi_llc/i_axi_llc_dut/i_llc_ways/genblk2[4]/i_data_way/i_data_sram/ram
#add wave -position end -label "Way3: RAM" sim:/tb_axi_llc/i_axi_llc_dut/i_llc_ways/genblk2[3]/i_data_way/i_data_sram/ram
#add wave -position end -label "Way2: RAM" sim:/tb_axi_llc/i_axi_llc_dut/i_llc_ways/genblk2[2]/i_data_way/i_data_sram/ram
#add wave -position end -label "Way1: RAM" sim:/tb_axi_llc/i_axi_llc_dut/i_llc_ways/genblk2[1]/i_data_way/i_data_sram/ram
#add wave -position end -label "Way0: RAM" sim:/tb_axi_llc/i_axi_llc_dut/i_llc_ways/genblk2[0]/i_data_way/i_data_sram/ram



run 61ns
#mem load -i /scratch/msc19f10/llc/umcL65/modelsim/scripts/memcontent/main.mem -format mti -startaddress 4095 -endaddress 0 /tb_axi_llc/i_memory/ram

