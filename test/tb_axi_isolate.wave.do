log -r /*
onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate -label Clock /tb_axi_isolate/i_dut/clk_i
add wave -noupdate -label Reset /tb_axi_isolate/i_dut/rst_ni
add wave -noupdate -divider {Slave Ports}
add wave -noupdate -group {Master AW} /tb_axi_isolate/master/aw_id
add wave -noupdate -group {Master AW} /tb_axi_isolate/master/aw_addr
add wave -noupdate -group {Master AW} /tb_axi_isolate/master/aw_len
add wave -noupdate -group {Master AW} /tb_axi_isolate/master/aw_size
add wave -noupdate -group {Master AW} /tb_axi_isolate/master/aw_burst
add wave -noupdate -group {Master AW} /tb_axi_isolate/master/aw_lock
add wave -noupdate -group {Master AW} /tb_axi_isolate/master/aw_cache
add wave -noupdate -group {Master AW} /tb_axi_isolate/master/aw_prot
add wave -noupdate -group {Master AW} /tb_axi_isolate/master/aw_qos
add wave -noupdate -group {Master AW} /tb_axi_isolate/master/aw_region
add wave -noupdate -group {Master AW} /tb_axi_isolate/master/aw_atop
add wave -noupdate -group {Master AW} /tb_axi_isolate/master/aw_user
add wave -noupdate -group {Master AW} /tb_axi_isolate/master/aw_valid
add wave -noupdate -group {Master AW} /tb_axi_isolate/master/aw_ready
add wave -noupdate -group {Master W} /tb_axi_isolate/master/w_data
add wave -noupdate -group {Master W} /tb_axi_isolate/master/w_strb
add wave -noupdate -group {Master W} /tb_axi_isolate/master/w_last
add wave -noupdate -group {Master W} /tb_axi_isolate/master/w_user
add wave -noupdate -group {Master W} /tb_axi_isolate/master/w_valid
add wave -noupdate -group {Master W} /tb_axi_isolate/master/w_ready
add wave -noupdate -group {Master B} /tb_axi_isolate/master/b_id
add wave -noupdate -group {Master B} /tb_axi_isolate/master/b_resp
add wave -noupdate -group {Master B} /tb_axi_isolate/master/b_user
add wave -noupdate -group {Master B} /tb_axi_isolate/master/b_valid
add wave -noupdate -group {Master B} /tb_axi_isolate/master/b_ready
add wave -noupdate -group {Master AR} /tb_axi_isolate/master/ar_id
add wave -noupdate -group {Master AR} /tb_axi_isolate/master/ar_addr
add wave -noupdate -group {Master AR} /tb_axi_isolate/master/ar_len
add wave -noupdate -group {Master AR} /tb_axi_isolate/master/ar_size
add wave -noupdate -group {Master AR} /tb_axi_isolate/master/ar_burst
add wave -noupdate -group {Master AR} /tb_axi_isolate/master/ar_lock
add wave -noupdate -group {Master AR} /tb_axi_isolate/master/ar_cache
add wave -noupdate -group {Master AR} /tb_axi_isolate/master/ar_prot
add wave -noupdate -group {Master AR} /tb_axi_isolate/master/ar_qos
add wave -noupdate -group {Master AR} /tb_axi_isolate/master/ar_region
add wave -noupdate -group {Master AR} /tb_axi_isolate/master/ar_user
add wave -noupdate -group {Master AR} /tb_axi_isolate/master/ar_valid
add wave -noupdate -group {Master AR} /tb_axi_isolate/master/ar_ready
add wave -noupdate -group {Master R} /tb_axi_isolate/master/r_id
add wave -noupdate -group {Master R} /tb_axi_isolate/master/r_data
add wave -noupdate -group {Master R} /tb_axi_isolate/master/r_resp
add wave -noupdate -group {Master R} /tb_axi_isolate/master/r_last
add wave -noupdate -group {Master R} /tb_axi_isolate/master/r_user
add wave -noupdate -group {Master R} /tb_axi_isolate/master/r_valid
add wave -noupdate -group {Master R} /tb_axi_isolate/master/r_ready
add wave -noupdate -divider {Master Ports}
add wave -noupdate -group {Slave AW} /tb_axi_isolate/slave/aw_id
add wave -noupdate -group {Slave AW} /tb_axi_isolate/slave/aw_addr
add wave -noupdate -group {Slave AW} /tb_axi_isolate/slave/aw_len
add wave -noupdate -group {Slave AW} /tb_axi_isolate/slave/aw_size
add wave -noupdate -group {Slave AW} /tb_axi_isolate/slave/aw_burst
add wave -noupdate -group {Slave AW} /tb_axi_isolate/slave/aw_lock
add wave -noupdate -group {Slave AW} /tb_axi_isolate/slave/aw_cache
add wave -noupdate -group {Slave AW} /tb_axi_isolate/slave/aw_prot
add wave -noupdate -group {Slave AW} /tb_axi_isolate/slave/aw_qos
add wave -noupdate -group {Slave AW} /tb_axi_isolate/slave/aw_region
add wave -noupdate -group {Slave AW} /tb_axi_isolate/slave/aw_atop
add wave -noupdate -group {Slave AW} /tb_axi_isolate/slave/aw_user
add wave -noupdate -group {Slave AW} /tb_axi_isolate/slave/aw_valid
add wave -noupdate -group {Slave AW} /tb_axi_isolate/slave/aw_ready
add wave -noupdate -group {Slave W} /tb_axi_isolate/slave/w_data
add wave -noupdate -group {Slave W} /tb_axi_isolate/slave/w_strb
add wave -noupdate -group {Slave W} /tb_axi_isolate/slave/w_last
add wave -noupdate -group {Slave W} /tb_axi_isolate/slave/w_user
add wave -noupdate -group {Slave W} /tb_axi_isolate/slave/w_valid
add wave -noupdate -group {Slave W} /tb_axi_isolate/slave/w_ready
add wave -noupdate -group {Slave B} /tb_axi_isolate/slave/b_id
add wave -noupdate -group {Slave B} /tb_axi_isolate/slave/b_resp
add wave -noupdate -group {Slave B} /tb_axi_isolate/slave/b_user
add wave -noupdate -group {Slave B} /tb_axi_isolate/slave/b_valid
add wave -noupdate -group {Slave B} /tb_axi_isolate/slave/b_ready
add wave -noupdate -group {Slave AR} /tb_axi_isolate/slave/ar_id
add wave -noupdate -group {Slave AR} /tb_axi_isolate/slave/ar_addr
add wave -noupdate -group {Slave AR} /tb_axi_isolate/slave/ar_len
add wave -noupdate -group {Slave AR} /tb_axi_isolate/slave/ar_size
add wave -noupdate -group {Slave AR} /tb_axi_isolate/slave/ar_burst
add wave -noupdate -group {Slave AR} /tb_axi_isolate/slave/ar_lock
add wave -noupdate -group {Slave AR} /tb_axi_isolate/slave/ar_cache
add wave -noupdate -group {Slave AR} /tb_axi_isolate/slave/ar_prot
add wave -noupdate -group {Slave AR} /tb_axi_isolate/slave/ar_qos
add wave -noupdate -group {Slave AR} /tb_axi_isolate/slave/ar_region
add wave -noupdate -group {Slave AR} /tb_axi_isolate/slave/ar_user
add wave -noupdate -group {Slave AR} /tb_axi_isolate/slave/ar_valid
add wave -noupdate -group {Slave AR} /tb_axi_isolate/slave/ar_ready
add wave -noupdate -group {Slave R} /tb_axi_isolate/slave/r_id
add wave -noupdate -group {Slave R} /tb_axi_isolate/slave/r_data
add wave -noupdate -group {Slave R} /tb_axi_isolate/slave/r_resp
add wave -noupdate -group {Slave R} /tb_axi_isolate/slave/r_last
add wave -noupdate -group {Slave R} /tb_axi_isolate/slave/r_user
add wave -noupdate -group {Slave R} /tb_axi_isolate/slave/r_valid
add wave -noupdate -group {Slave R} /tb_axi_isolate/slave/r_ready
add wave -noupdate -divider Custom
add wave -noupdate -label isolate_i /tb_axi_isolate/i_dut/isolate_i
add wave -noupdate -label isolated_o /tb_axi_isolate/i_dut/isolated_o
add wave -noupdate -label state_aw_q /tb_axi_isolate/i_dut/i_axi_isolate/state_aw_q
add wave -noupdate -label pending_aw_q -radix unsigned /tb_axi_isolate/i_dut/i_axi_isolate/pending_aw_q
add wave -noupdate -label pending_w_q -radix unsigned /tb_axi_isolate/i_dut/i_axi_isolate/pending_w_q
add wave -noupdate -label state_ar_q /tb_axi_isolate/i_dut/i_axi_isolate/state_ar_q
add wave -noupdate -label pending_ar_q -radix unsigned /tb_axi_isolate/i_dut/i_axi_isolate/pending_ar_q
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {718 ns} 0}
quietly wave cursor active 1
configure wave -namecolwidth 264
configure wave -valuecolwidth 100
configure wave -justifyvalue left
configure wave -signalnamewidth 0
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
WaveRestoreZoom {12 ns} {7033 ns}
