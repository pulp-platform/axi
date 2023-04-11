log -r /*
onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate -label Clock /tb_axi_isolate/i_dut/clk_i
add wave -noupdate -label Reset /tb_axi_isolate/i_dut/rst_ni
add wave -noupdate -divider {Subordinate Ports}
add wave -noupdate -group {Manager AW} /tb_axi_isolate/manager/aw_id
add wave -noupdate -group {Manager AW} /tb_axi_isolate/manager/aw_addr
add wave -noupdate -group {Manager AW} /tb_axi_isolate/manager/aw_len
add wave -noupdate -group {Manager AW} /tb_axi_isolate/manager/aw_size
add wave -noupdate -group {Manager AW} /tb_axi_isolate/manager/aw_burst
add wave -noupdate -group {Manager AW} /tb_axi_isolate/manager/aw_lock
add wave -noupdate -group {Manager AW} /tb_axi_isolate/manager/aw_cache
add wave -noupdate -group {Manager AW} /tb_axi_isolate/manager/aw_prot
add wave -noupdate -group {Manager AW} /tb_axi_isolate/manager/aw_qos
add wave -noupdate -group {Manager AW} /tb_axi_isolate/manager/aw_region
add wave -noupdate -group {Manager AW} /tb_axi_isolate/manager/aw_atop
add wave -noupdate -group {Manager AW} /tb_axi_isolate/manager/aw_user
add wave -noupdate -group {Manager AW} /tb_axi_isolate/manager/aw_valid
add wave -noupdate -group {Manager AW} /tb_axi_isolate/manager/aw_ready
add wave -noupdate -group {Manager W} /tb_axi_isolate/manager/w_data
add wave -noupdate -group {Manager W} /tb_axi_isolate/manager/w_strb
add wave -noupdate -group {Manager W} /tb_axi_isolate/manager/w_last
add wave -noupdate -group {Manager W} /tb_axi_isolate/manager/w_user
add wave -noupdate -group {Manager W} /tb_axi_isolate/manager/w_valid
add wave -noupdate -group {Manager W} /tb_axi_isolate/manager/w_ready
add wave -noupdate -group {Manager B} /tb_axi_isolate/manager/b_id
add wave -noupdate -group {Manager B} /tb_axi_isolate/manager/b_resp
add wave -noupdate -group {Manager B} /tb_axi_isolate/manager/b_user
add wave -noupdate -group {Manager B} /tb_axi_isolate/manager/b_valid
add wave -noupdate -group {Manager B} /tb_axi_isolate/manager/b_ready
add wave -noupdate -group {Manager AR} /tb_axi_isolate/manager/ar_id
add wave -noupdate -group {Manager AR} /tb_axi_isolate/manager/ar_addr
add wave -noupdate -group {Manager AR} /tb_axi_isolate/manager/ar_len
add wave -noupdate -group {Manager AR} /tb_axi_isolate/manager/ar_size
add wave -noupdate -group {Manager AR} /tb_axi_isolate/manager/ar_burst
add wave -noupdate -group {Manager AR} /tb_axi_isolate/manager/ar_lock
add wave -noupdate -group {Manager AR} /tb_axi_isolate/manager/ar_cache
add wave -noupdate -group {Manager AR} /tb_axi_isolate/manager/ar_prot
add wave -noupdate -group {Manager AR} /tb_axi_isolate/manager/ar_qos
add wave -noupdate -group {Manager AR} /tb_axi_isolate/manager/ar_region
add wave -noupdate -group {Manager AR} /tb_axi_isolate/manager/ar_user
add wave -noupdate -group {Manager AR} /tb_axi_isolate/manager/ar_valid
add wave -noupdate -group {Manager AR} /tb_axi_isolate/manager/ar_ready
add wave -noupdate -group {Manager R} /tb_axi_isolate/manager/r_id
add wave -noupdate -group {Manager R} /tb_axi_isolate/manager/r_data
add wave -noupdate -group {Manager R} /tb_axi_isolate/manager/r_resp
add wave -noupdate -group {Manager R} /tb_axi_isolate/manager/r_last
add wave -noupdate -group {Manager R} /tb_axi_isolate/manager/r_user
add wave -noupdate -group {Manager R} /tb_axi_isolate/manager/r_valid
add wave -noupdate -group {Manager R} /tb_axi_isolate/manager/r_ready
add wave -noupdate -divider {Manager Ports}
add wave -noupdate -group {Subordinate AW} /tb_axi_isolate/subordinate/aw_id
add wave -noupdate -group {Subordinate AW} /tb_axi_isolate/subordinate/aw_addr
add wave -noupdate -group {Subordinate AW} /tb_axi_isolate/subordinate/aw_len
add wave -noupdate -group {Subordinate AW} /tb_axi_isolate/subordinate/aw_size
add wave -noupdate -group {Subordinate AW} /tb_axi_isolate/subordinate/aw_burst
add wave -noupdate -group {Subordinate AW} /tb_axi_isolate/subordinate/aw_lock
add wave -noupdate -group {Subordinate AW} /tb_axi_isolate/subordinate/aw_cache
add wave -noupdate -group {Subordinate AW} /tb_axi_isolate/subordinate/aw_prot
add wave -noupdate -group {Subordinate AW} /tb_axi_isolate/subordinate/aw_qos
add wave -noupdate -group {Subordinate AW} /tb_axi_isolate/subordinate/aw_region
add wave -noupdate -group {Subordinate AW} /tb_axi_isolate/subordinate/aw_atop
add wave -noupdate -group {Subordinate AW} /tb_axi_isolate/subordinate/aw_user
add wave -noupdate -group {Subordinate AW} /tb_axi_isolate/subordinate/aw_valid
add wave -noupdate -group {Subordinate AW} /tb_axi_isolate/subordinate/aw_ready
add wave -noupdate -group {Subordinate W} /tb_axi_isolate/subordinate/w_data
add wave -noupdate -group {Subordinate W} /tb_axi_isolate/subordinate/w_strb
add wave -noupdate -group {Subordinate W} /tb_axi_isolate/subordinate/w_last
add wave -noupdate -group {Subordinate W} /tb_axi_isolate/subordinate/w_user
add wave -noupdate -group {Subordinate W} /tb_axi_isolate/subordinate/w_valid
add wave -noupdate -group {Subordinate W} /tb_axi_isolate/subordinate/w_ready
add wave -noupdate -group {Subordinate B} /tb_axi_isolate/subordinate/b_id
add wave -noupdate -group {Subordinate B} /tb_axi_isolate/subordinate/b_resp
add wave -noupdate -group {Subordinate B} /tb_axi_isolate/subordinate/b_user
add wave -noupdate -group {Subordinate B} /tb_axi_isolate/subordinate/b_valid
add wave -noupdate -group {Subordinate B} /tb_axi_isolate/subordinate/b_ready
add wave -noupdate -group {Subordinate AR} /tb_axi_isolate/subordinate/ar_id
add wave -noupdate -group {Subordinate AR} /tb_axi_isolate/subordinate/ar_addr
add wave -noupdate -group {Subordinate AR} /tb_axi_isolate/subordinate/ar_len
add wave -noupdate -group {Subordinate AR} /tb_axi_isolate/subordinate/ar_size
add wave -noupdate -group {Subordinate AR} /tb_axi_isolate/subordinate/ar_burst
add wave -noupdate -group {Subordinate AR} /tb_axi_isolate/subordinate/ar_lock
add wave -noupdate -group {Subordinate AR} /tb_axi_isolate/subordinate/ar_cache
add wave -noupdate -group {Subordinate AR} /tb_axi_isolate/subordinate/ar_prot
add wave -noupdate -group {Subordinate AR} /tb_axi_isolate/subordinate/ar_qos
add wave -noupdate -group {Subordinate AR} /tb_axi_isolate/subordinate/ar_region
add wave -noupdate -group {Subordinate AR} /tb_axi_isolate/subordinate/ar_user
add wave -noupdate -group {Subordinate AR} /tb_axi_isolate/subordinate/ar_valid
add wave -noupdate -group {Subordinate AR} /tb_axi_isolate/subordinate/ar_ready
add wave -noupdate -group {Subordinate R} /tb_axi_isolate/subordinate/r_id
add wave -noupdate -group {Subordinate R} /tb_axi_isolate/subordinate/r_data
add wave -noupdate -group {Subordinate R} /tb_axi_isolate/subordinate/r_resp
add wave -noupdate -group {Subordinate R} /tb_axi_isolate/subordinate/r_last
add wave -noupdate -group {Subordinate R} /tb_axi_isolate/subordinate/r_user
add wave -noupdate -group {Subordinate R} /tb_axi_isolate/subordinate/r_valid
add wave -noupdate -group {Subordinate R} /tb_axi_isolate/subordinate/r_ready
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
