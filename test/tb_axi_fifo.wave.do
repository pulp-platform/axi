onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate -label Clock /tb_axi_fifo/i_dut/clk_i
add wave -noupdate -label Reset /tb_axi_fifo/i_dut/rst_ni
add wave -noupdate -divider {Subordinate Ports}
add wave -noupdate -expand -group {Manager AW} /tb_axi_fifo/manager/aw_id
add wave -noupdate -expand -group {Manager AW} /tb_axi_fifo/manager/aw_addr
add wave -noupdate -expand -group {Manager AW} /tb_axi_fifo/manager/aw_len
add wave -noupdate -expand -group {Manager AW} /tb_axi_fifo/manager/aw_size
add wave -noupdate -expand -group {Manager AW} /tb_axi_fifo/manager/aw_burst
add wave -noupdate -expand -group {Manager AW} /tb_axi_fifo/manager/aw_lock
add wave -noupdate -expand -group {Manager AW} /tb_axi_fifo/manager/aw_cache
add wave -noupdate -expand -group {Manager AW} /tb_axi_fifo/manager/aw_prot
add wave -noupdate -expand -group {Manager AW} /tb_axi_fifo/manager/aw_qos
add wave -noupdate -expand -group {Manager AW} /tb_axi_fifo/manager/aw_region
add wave -noupdate -expand -group {Manager AW} /tb_axi_fifo/manager/aw_atop
add wave -noupdate -expand -group {Manager AW} /tb_axi_fifo/manager/aw_user
add wave -noupdate -expand -group {Manager AW} /tb_axi_fifo/manager/aw_valid
add wave -noupdate -expand -group {Manager AW} /tb_axi_fifo/manager/aw_ready
add wave -noupdate -group {Manager W} /tb_axi_fifo/manager/w_data
add wave -noupdate -group {Manager W} /tb_axi_fifo/manager/w_strb
add wave -noupdate -group {Manager W} /tb_axi_fifo/manager/w_last
add wave -noupdate -group {Manager W} /tb_axi_fifo/manager/w_user
add wave -noupdate -group {Manager W} /tb_axi_fifo/manager/w_valid
add wave -noupdate -group {Manager W} /tb_axi_fifo/manager/w_ready
add wave -noupdate -group {Manager B} /tb_axi_fifo/manager/b_id
add wave -noupdate -group {Manager B} /tb_axi_fifo/manager/b_resp
add wave -noupdate -group {Manager B} /tb_axi_fifo/manager/b_user
add wave -noupdate -group {Manager B} /tb_axi_fifo/manager/b_valid
add wave -noupdate -group {Manager B} /tb_axi_fifo/manager/b_ready
add wave -noupdate -expand -group {Manager AR} /tb_axi_fifo/manager/ar_id
add wave -noupdate -expand -group {Manager AR} /tb_axi_fifo/manager/ar_addr
add wave -noupdate -expand -group {Manager AR} /tb_axi_fifo/manager/ar_len
add wave -noupdate -expand -group {Manager AR} /tb_axi_fifo/manager/ar_size
add wave -noupdate -expand -group {Manager AR} /tb_axi_fifo/manager/ar_burst
add wave -noupdate -expand -group {Manager AR} /tb_axi_fifo/manager/ar_lock
add wave -noupdate -expand -group {Manager AR} /tb_axi_fifo/manager/ar_cache
add wave -noupdate -expand -group {Manager AR} /tb_axi_fifo/manager/ar_prot
add wave -noupdate -expand -group {Manager AR} /tb_axi_fifo/manager/ar_qos
add wave -noupdate -expand -group {Manager AR} /tb_axi_fifo/manager/ar_region
add wave -noupdate -expand -group {Manager AR} /tb_axi_fifo/manager/ar_user
add wave -noupdate -expand -group {Manager AR} /tb_axi_fifo/manager/ar_valid
add wave -noupdate -expand -group {Manager AR} /tb_axi_fifo/manager/ar_ready
add wave -noupdate -group {Manager R} /tb_axi_fifo/manager/r_id
add wave -noupdate -group {Manager R} /tb_axi_fifo/manager/r_data
add wave -noupdate -group {Manager R} /tb_axi_fifo/manager/r_resp
add wave -noupdate -group {Manager R} /tb_axi_fifo/manager/r_last
add wave -noupdate -group {Manager R} /tb_axi_fifo/manager/r_user
add wave -noupdate -group {Manager R} /tb_axi_fifo/manager/r_valid
add wave -noupdate -group {Manager R} /tb_axi_fifo/manager/r_ready
add wave -noupdate -divider {Manager Ports}
add wave -noupdate -expand -group {Subordinate AW} /tb_axi_fifo/subordinate/aw_id
add wave -noupdate -expand -group {Subordinate AW} /tb_axi_fifo/subordinate/aw_addr
add wave -noupdate -expand -group {Subordinate AW} /tb_axi_fifo/subordinate/aw_len
add wave -noupdate -expand -group {Subordinate AW} /tb_axi_fifo/subordinate/aw_size
add wave -noupdate -expand -group {Subordinate AW} /tb_axi_fifo/subordinate/aw_burst
add wave -noupdate -expand -group {Subordinate AW} /tb_axi_fifo/subordinate/aw_lock
add wave -noupdate -expand -group {Subordinate AW} /tb_axi_fifo/subordinate/aw_cache
add wave -noupdate -expand -group {Subordinate AW} /tb_axi_fifo/subordinate/aw_prot
add wave -noupdate -expand -group {Subordinate AW} /tb_axi_fifo/subordinate/aw_qos
add wave -noupdate -expand -group {Subordinate AW} /tb_axi_fifo/subordinate/aw_region
add wave -noupdate -expand -group {Subordinate AW} /tb_axi_fifo/subordinate/aw_atop
add wave -noupdate -expand -group {Subordinate AW} /tb_axi_fifo/subordinate/aw_user
add wave -noupdate -expand -group {Subordinate AW} /tb_axi_fifo/subordinate/aw_valid
add wave -noupdate -expand -group {Subordinate AW} /tb_axi_fifo/subordinate/aw_ready
add wave -noupdate -group {Subordinate W} /tb_axi_fifo/subordinate/w_data
add wave -noupdate -group {Subordinate W} /tb_axi_fifo/subordinate/w_strb
add wave -noupdate -group {Subordinate W} /tb_axi_fifo/subordinate/w_last
add wave -noupdate -group {Subordinate W} /tb_axi_fifo/subordinate/w_user
add wave -noupdate -group {Subordinate W} /tb_axi_fifo/subordinate/w_valid
add wave -noupdate -group {Subordinate W} /tb_axi_fifo/subordinate/w_ready
add wave -noupdate -group {Subordinate B} /tb_axi_fifo/subordinate/b_id
add wave -noupdate -group {Subordinate B} /tb_axi_fifo/subordinate/b_resp
add wave -noupdate -group {Subordinate B} /tb_axi_fifo/subordinate/b_user
add wave -noupdate -group {Subordinate B} /tb_axi_fifo/subordinate/b_valid
add wave -noupdate -group {Subordinate B} /tb_axi_fifo/subordinate/b_ready
add wave -noupdate -expand -group {Subordinate AR} /tb_axi_fifo/subordinate/ar_id
add wave -noupdate -expand -group {Subordinate AR} /tb_axi_fifo/subordinate/ar_addr
add wave -noupdate -expand -group {Subordinate AR} /tb_axi_fifo/subordinate/ar_len
add wave -noupdate -expand -group {Subordinate AR} /tb_axi_fifo/subordinate/ar_size
add wave -noupdate -expand -group {Subordinate AR} /tb_axi_fifo/subordinate/ar_burst
add wave -noupdate -expand -group {Subordinate AR} /tb_axi_fifo/subordinate/ar_lock
add wave -noupdate -expand -group {Subordinate AR} /tb_axi_fifo/subordinate/ar_cache
add wave -noupdate -expand -group {Subordinate AR} /tb_axi_fifo/subordinate/ar_prot
add wave -noupdate -expand -group {Subordinate AR} /tb_axi_fifo/subordinate/ar_qos
add wave -noupdate -expand -group {Subordinate AR} /tb_axi_fifo/subordinate/ar_region
add wave -noupdate -expand -group {Subordinate AR} /tb_axi_fifo/subordinate/ar_user
add wave -noupdate -expand -group {Subordinate AR} /tb_axi_fifo/subordinate/ar_valid
add wave -noupdate -expand -group {Subordinate AR} /tb_axi_fifo/subordinate/ar_ready
add wave -noupdate -group {Subordinate R} /tb_axi_fifo/subordinate/r_id
add wave -noupdate -group {Subordinate R} /tb_axi_fifo/subordinate/r_data
add wave -noupdate -group {Subordinate R} /tb_axi_fifo/subordinate/r_resp
add wave -noupdate -group {Subordinate R} /tb_axi_fifo/subordinate/r_last
add wave -noupdate -group {Subordinate R} /tb_axi_fifo/subordinate/r_user
add wave -noupdate -group {Subordinate R} /tb_axi_fifo/subordinate/r_valid
add wave -noupdate -group {Subordinate R} /tb_axi_fifo/subordinate/r_ready
add wave -noupdate -divider Custom
add wave -noupdate -expand -group {AW FiFo} /tb_axi_fifo/i_dut/i_axi_fifo/gen_axi_fifo/i_aw_fifo/clk_i
add wave -noupdate -expand -group {AW FiFo} /tb_axi_fifo/i_dut/i_axi_fifo/gen_axi_fifo/i_aw_fifo/rst_ni
add wave -noupdate -expand -group {AW FiFo} /tb_axi_fifo/i_dut/i_axi_fifo/gen_axi_fifo/i_aw_fifo/flush_i
add wave -noupdate -expand -group {AW FiFo} /tb_axi_fifo/i_dut/i_axi_fifo/gen_axi_fifo/i_aw_fifo/testmode_i
add wave -noupdate -expand -group {AW FiFo} /tb_axi_fifo/i_dut/i_axi_fifo/gen_axi_fifo/i_aw_fifo/full_o
add wave -noupdate -expand -group {AW FiFo} /tb_axi_fifo/i_dut/i_axi_fifo/gen_axi_fifo/i_aw_fifo/empty_o
add wave -noupdate -expand -group {AW FiFo} /tb_axi_fifo/i_dut/i_axi_fifo/gen_axi_fifo/i_aw_fifo/usage_o
add wave -noupdate -expand -group {AW FiFo} /tb_axi_fifo/i_dut/i_axi_fifo/gen_axi_fifo/i_aw_fifo/data_i
add wave -noupdate -expand -group {AW FiFo} /tb_axi_fifo/i_dut/i_axi_fifo/gen_axi_fifo/i_aw_fifo/push_i
add wave -noupdate -expand -group {AW FiFo} /tb_axi_fifo/i_dut/i_axi_fifo/gen_axi_fifo/i_aw_fifo/data_o
add wave -noupdate -expand -group {AW FiFo} /tb_axi_fifo/i_dut/i_axi_fifo/gen_axi_fifo/i_aw_fifo/pop_i
add wave -noupdate -expand -group {W FiFo} /tb_axi_fifo/i_dut/i_axi_fifo/gen_axi_fifo/i_w_fifo/clk_i
add wave -noupdate -expand -group {W FiFo} /tb_axi_fifo/i_dut/i_axi_fifo/gen_axi_fifo/i_w_fifo/rst_ni
add wave -noupdate -expand -group {W FiFo} /tb_axi_fifo/i_dut/i_axi_fifo/gen_axi_fifo/i_w_fifo/flush_i
add wave -noupdate -expand -group {W FiFo} /tb_axi_fifo/i_dut/i_axi_fifo/gen_axi_fifo/i_w_fifo/testmode_i
add wave -noupdate -expand -group {W FiFo} /tb_axi_fifo/i_dut/i_axi_fifo/gen_axi_fifo/i_w_fifo/full_o
add wave -noupdate -expand -group {W FiFo} /tb_axi_fifo/i_dut/i_axi_fifo/gen_axi_fifo/i_w_fifo/empty_o
add wave -noupdate -expand -group {W FiFo} /tb_axi_fifo/i_dut/i_axi_fifo/gen_axi_fifo/i_w_fifo/usage_o
add wave -noupdate -expand -group {W FiFo} /tb_axi_fifo/i_dut/i_axi_fifo/gen_axi_fifo/i_w_fifo/data_i
add wave -noupdate -expand -group {W FiFo} /tb_axi_fifo/i_dut/i_axi_fifo/gen_axi_fifo/i_w_fifo/push_i
add wave -noupdate -expand -group {W FiFo} /tb_axi_fifo/i_dut/i_axi_fifo/gen_axi_fifo/i_w_fifo/data_o
add wave -noupdate -expand -group {W FiFo} /tb_axi_fifo/i_dut/i_axi_fifo/gen_axi_fifo/i_w_fifo/pop_i
add wave -noupdate -expand -group {B FiFo} /tb_axi_fifo/i_dut/i_axi_fifo/gen_axi_fifo/i_b_fifo/clk_i
add wave -noupdate -expand -group {B FiFo} /tb_axi_fifo/i_dut/i_axi_fifo/gen_axi_fifo/i_b_fifo/rst_ni
add wave -noupdate -expand -group {B FiFo} /tb_axi_fifo/i_dut/i_axi_fifo/gen_axi_fifo/i_b_fifo/flush_i
add wave -noupdate -expand -group {B FiFo} /tb_axi_fifo/i_dut/i_axi_fifo/gen_axi_fifo/i_b_fifo/testmode_i
add wave -noupdate -expand -group {B FiFo} /tb_axi_fifo/i_dut/i_axi_fifo/gen_axi_fifo/i_b_fifo/full_o
add wave -noupdate -expand -group {B FiFo} /tb_axi_fifo/i_dut/i_axi_fifo/gen_axi_fifo/i_b_fifo/empty_o
add wave -noupdate -expand -group {B FiFo} /tb_axi_fifo/i_dut/i_axi_fifo/gen_axi_fifo/i_b_fifo/usage_o
add wave -noupdate -expand -group {B FiFo} /tb_axi_fifo/i_dut/i_axi_fifo/gen_axi_fifo/i_b_fifo/data_i
add wave -noupdate -expand -group {B FiFo} /tb_axi_fifo/i_dut/i_axi_fifo/gen_axi_fifo/i_b_fifo/push_i
add wave -noupdate -expand -group {B FiFo} /tb_axi_fifo/i_dut/i_axi_fifo/gen_axi_fifo/i_b_fifo/data_o
add wave -noupdate -expand -group {B FiFo} /tb_axi_fifo/i_dut/i_axi_fifo/gen_axi_fifo/i_b_fifo/pop_i
add wave -noupdate -expand -group {Ar FiFo} /tb_axi_fifo/i_dut/i_axi_fifo/gen_axi_fifo/i_ar_fifo/clk_i
add wave -noupdate -expand -group {Ar FiFo} /tb_axi_fifo/i_dut/i_axi_fifo/gen_axi_fifo/i_ar_fifo/rst_ni
add wave -noupdate -expand -group {Ar FiFo} /tb_axi_fifo/i_dut/i_axi_fifo/gen_axi_fifo/i_ar_fifo/flush_i
add wave -noupdate -expand -group {Ar FiFo} /tb_axi_fifo/i_dut/i_axi_fifo/gen_axi_fifo/i_ar_fifo/testmode_i
add wave -noupdate -expand -group {Ar FiFo} /tb_axi_fifo/i_dut/i_axi_fifo/gen_axi_fifo/i_ar_fifo/full_o
add wave -noupdate -expand -group {Ar FiFo} /tb_axi_fifo/i_dut/i_axi_fifo/gen_axi_fifo/i_ar_fifo/empty_o
add wave -noupdate -expand -group {Ar FiFo} /tb_axi_fifo/i_dut/i_axi_fifo/gen_axi_fifo/i_ar_fifo/usage_o
add wave -noupdate -expand -group {Ar FiFo} /tb_axi_fifo/i_dut/i_axi_fifo/gen_axi_fifo/i_ar_fifo/data_i
add wave -noupdate -expand -group {Ar FiFo} /tb_axi_fifo/i_dut/i_axi_fifo/gen_axi_fifo/i_ar_fifo/push_i
add wave -noupdate -expand -group {Ar FiFo} /tb_axi_fifo/i_dut/i_axi_fifo/gen_axi_fifo/i_ar_fifo/data_o
add wave -noupdate -expand -group {Ar FiFo} /tb_axi_fifo/i_dut/i_axi_fifo/gen_axi_fifo/i_ar_fifo/pop_i
add wave -noupdate -expand -group {R FiFo} /tb_axi_fifo/i_dut/i_axi_fifo/gen_axi_fifo/i_r_fifo/clk_i
add wave -noupdate -expand -group {R FiFo} /tb_axi_fifo/i_dut/i_axi_fifo/gen_axi_fifo/i_r_fifo/rst_ni
add wave -noupdate -expand -group {R FiFo} /tb_axi_fifo/i_dut/i_axi_fifo/gen_axi_fifo/i_r_fifo/flush_i
add wave -noupdate -expand -group {R FiFo} /tb_axi_fifo/i_dut/i_axi_fifo/gen_axi_fifo/i_r_fifo/testmode_i
add wave -noupdate -expand -group {R FiFo} /tb_axi_fifo/i_dut/i_axi_fifo/gen_axi_fifo/i_r_fifo/full_o
add wave -noupdate -expand -group {R FiFo} /tb_axi_fifo/i_dut/i_axi_fifo/gen_axi_fifo/i_r_fifo/empty_o
add wave -noupdate -expand -group {R FiFo} /tb_axi_fifo/i_dut/i_axi_fifo/gen_axi_fifo/i_r_fifo/usage_o
add wave -noupdate -expand -group {R FiFo} /tb_axi_fifo/i_dut/i_axi_fifo/gen_axi_fifo/i_r_fifo/data_i
add wave -noupdate -expand -group {R FiFo} /tb_axi_fifo/i_dut/i_axi_fifo/gen_axi_fifo/i_r_fifo/push_i
add wave -noupdate -expand -group {R FiFo} /tb_axi_fifo/i_dut/i_axi_fifo/gen_axi_fifo/i_r_fifo/data_o
add wave -noupdate -expand -group {R FiFo} /tb_axi_fifo/i_dut/i_axi_fifo/gen_axi_fifo/i_r_fifo/pop_i
add wave -noupdate -divider {DUT Ports}
add wave -noupdate -expand -group {DUT sbr AW} /tb_axi_fifo/i_dut/i_axi_fifo/sbr_req_i.aw_valid
add wave -noupdate -expand -group {DUT sbr AW} /tb_axi_fifo/i_dut/i_axi_fifo/sbr_resp_o.aw_ready
add wave -noupdate -expand -group {DUT sbr AW} /tb_axi_fifo/i_dut/i_axi_fifo/sbr_req_i.aw
add wave -noupdate -expand -group {DUT sbr W} /tb_axi_fifo/i_dut/i_axi_fifo/sbr_req_i.w
add wave -noupdate -expand -group {DUT sbr W} /tb_axi_fifo/i_dut/i_axi_fifo/sbr_req_i.w_valid
add wave -noupdate -expand -group {DUT sbr W} /tb_axi_fifo/i_dut/i_axi_fifo/sbr_resp_o.w_ready
add wave -noupdate -expand -group {DUT sbr B} /tb_axi_fifo/i_dut/i_axi_fifo/sbr_resp_o.b_valid
add wave -noupdate -expand -group {DUT sbr B} /tb_axi_fifo/i_dut/i_axi_fifo/sbr_req_i.b_ready
add wave -noupdate -expand -group {DUT sbr B} /tb_axi_fifo/i_dut/i_axi_fifo/sbr_resp_o.b
add wave -noupdate -expand -group {DUT sbr AR} /tb_axi_fifo/i_dut/i_axi_fifo/sbr_req_i.ar_valid
add wave -noupdate -expand -group {DUT sbr AR} /tb_axi_fifo/i_dut/i_axi_fifo/sbr_resp_o.ar_ready
add wave -noupdate -expand -group {DUT sbr AR} /tb_axi_fifo/i_dut/i_axi_fifo/sbr_req_i.ar
add wave -noupdate -expand -group {DUT sbr R} /tb_axi_fifo/i_dut/i_axi_fifo/sbr_resp_o.r_valid
add wave -noupdate -expand -group {DUT sbr R} /tb_axi_fifo/i_dut/i_axi_fifo/sbr_req_i.r_ready
add wave -noupdate -expand -group {DUT sbr R} /tb_axi_fifo/i_dut/i_axi_fifo/sbr_resp_o.r
add wave -noupdate -expand -group {DUT mgr AW} /tb_axi_fifo/i_dut/i_axi_fifo/mgr_req_o.aw_valid
add wave -noupdate -expand -group {DUT mgr AW} /tb_axi_fifo/i_dut/i_axi_fifo/mgr_resp_i.aw_ready
add wave -noupdate -expand -group {DUT mgr AW} /tb_axi_fifo/i_dut/i_axi_fifo/mgr_req_o.aw
add wave -noupdate -expand -group {DUT mgr W} /tb_axi_fifo/i_dut/i_axi_fifo/mgr_req_o.w
add wave -noupdate -expand -group {DUT mgr W} /tb_axi_fifo/i_dut/i_axi_fifo/mgr_req_o.w_valid
add wave -noupdate -expand -group {DUT mgr W} /tb_axi_fifo/i_dut/i_axi_fifo/mgr_resp_i.w_ready
add wave -noupdate -expand -group {DUT mgr B} /tb_axi_fifo/i_dut/i_axi_fifo/mgr_resp_i.b_valid
add wave -noupdate -expand -group {DUT mgr B} /tb_axi_fifo/i_dut/i_axi_fifo/mgr_req_o.b_ready
add wave -noupdate -expand -group {DUT mgr B} /tb_axi_fifo/i_dut/i_axi_fifo/mgr_resp_i.b
add wave -noupdate -expand -group {DUT mgr AR} /tb_axi_fifo/i_dut/i_axi_fifo/mgr_req_o.ar_valid
add wave -noupdate -expand -group {DUT mgr AR} /tb_axi_fifo/i_dut/i_axi_fifo/mgr_resp_i.ar_ready
add wave -noupdate -expand -group {DUT mgr AR} /tb_axi_fifo/i_dut/i_axi_fifo/mgr_req_o.ar
add wave -noupdate -expand -group {DUT mgr R} /tb_axi_fifo/i_dut/i_axi_fifo/mgr_resp_i.r_valid
add wave -noupdate -expand -group {DUT mgr R} /tb_axi_fifo/i_dut/i_axi_fifo/mgr_req_o.r_ready
add wave -noupdate -expand -group {DUT mgr R} /tb_axi_fifo/i_dut/i_axi_fifo/mgr_resp_i.r
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {70 ns} 0}
quietly wave cursor active 1
configure wave -namecolwidth 197
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
WaveRestoreZoom {0 ns} {841 ns}
