onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate /tb_axi_rt_unit/i_axi_burst_splitter/clk_i
add wave -noupdate /tb_axi_rt_unit/i_axi_burst_splitter/rst_ni
add wave -noupdate /tb_axi_rt_unit/i_axi_burst_splitter/len_limit_i
add wave -noupdate -group inbound /tb_axi_rt_unit/i_axi_burst_splitter/slv_req_i
add wave -noupdate -group inbound /tb_axi_rt_unit/i_axi_burst_splitter/slv_resp_o
add wave -noupdate -group inbound -label AW_master /tb_axi_rt_unit/i_signal_highlighter_master_aw/in_wave
add wave -noupdate -group inbound -label W_master /tb_axi_rt_unit/i_signal_highlighter_master_w/in_wave
add wave -noupdate -group inbound -label B_master /tb_axi_rt_unit/i_signal_highlighter_master_b/in_wave
add wave -noupdate -group inbound -label AR_master /tb_axi_rt_unit/i_signal_highlighter_master_ar/in_wave
add wave -noupdate -group inbound -label R_master /tb_axi_rt_unit/i_signal_highlighter_master_r/in_wave
add wave -noupdate -group outbound /tb_axi_rt_unit/i_axi_burst_splitter/mst_req_o
add wave -noupdate -group outbound /tb_axi_rt_unit/i_axi_burst_splitter/mst_resp_i
add wave -noupdate -group outbound -label AW_slave /tb_axi_rt_unit/i_signal_highlighter_slave_aw/in_wave
add wave -noupdate -group outbound -label W_slave /tb_axi_rt_unit/i_signal_highlighter_slave_w/in_wave
add wave -noupdate -group outbound -label B_slave /tb_axi_rt_unit/i_signal_highlighter_slave_b/in_wave
add wave -noupdate -group outbound -label AR_slave /tb_axi_rt_unit/i_signal_highlighter_slave_ar/in_wave
add wave -noupdate -group outbound -label R_slave /tb_axi_rt_unit/i_signal_highlighter_slave_r/in_wave
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {115 ns} 0}
quietly wave cursor active 1
configure wave -namecolwidth 150
configure wave -valuecolwidth 100
configure wave -justifyvalue left
configure wave -signalnamewidth 1
configure wave -snapdistance 10
configure wave -datasetprefix 0
configure wave -rowmargin 4
configure wave -childrowmargin 2
configure wave -gridoffset 0
configure wave -gridperiod 1
configure wave -griddelta 40
configure wave -timeline 0
configure wave -timelineunits ns
update
WaveRestoreZoom {26 ns} {259 ns}
