add wave -noupdate /tb_axi_sim_mem/axi_dv/clk_i
add wave -noupdate -divider AW
add wave -noupdate /tb_axi_sim_mem/i_sim_mem/axi_req_i.aw
add wave -noupdate /tb_axi_sim_mem/i_sim_mem/axi_req_i.aw_valid
add wave -noupdate /tb_axi_sim_mem/i_sim_mem/axi_rsp_o.aw_ready
add wave -noupdate -divider W
add wave -noupdate /tb_axi_sim_mem/i_sim_mem/axi_req_i.w
add wave -noupdate /tb_axi_sim_mem/i_sim_mem/axi_req_i.w_valid
add wave -noupdate /tb_axi_sim_mem/i_sim_mem/axi_rsp_o.w_ready
add wave -noupdate -divider B
add wave -noupdate /tb_axi_sim_mem/i_sim_mem/axi_rsp_o.b
add wave -noupdate /tb_axi_sim_mem/i_sim_mem/axi_rsp_o.b_valid
add wave -noupdate /tb_axi_sim_mem/i_sim_mem/axi_req_i.b_ready
add wave -noupdate -divider AR
add wave -noupdate /tb_axi_sim_mem/i_sim_mem/axi_req_i.ar
add wave -noupdate /tb_axi_sim_mem/i_sim_mem/axi_req_i.ar_valid
add wave -noupdate /tb_axi_sim_mem/i_sim_mem/axi_rsp_o.ar_ready
add wave -noupdate -divider R
add wave -noupdate /tb_axi_sim_mem/i_sim_mem/axi_rsp_o.r
add wave -noupdate /tb_axi_sim_mem/i_sim_mem/axi_rsp_o.r_valid
add wave -noupdate /tb_axi_sim_mem/i_sim_mem/axi_req_i.r_ready
