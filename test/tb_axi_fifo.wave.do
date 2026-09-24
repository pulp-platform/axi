onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate -label Clock /tb_axi_fifo/i_dut/clk_i
add wave -noupdate -label Reset /tb_axi_fifo/i_dut/rst_ni
add wave -noupdate -divider {Slave Ports}
add wave -noupdate -expand -group {Master AW} /tb_axi_fifo/master/aw_id
add wave -noupdate -expand -group {Master AW} /tb_axi_fifo/master/aw_addr
add wave -noupdate -expand -group {Master AW} /tb_axi_fifo/master/aw_len
add wave -noupdate -expand -group {Master AW} /tb_axi_fifo/master/aw_size
add wave -noupdate -expand -group {Master AW} /tb_axi_fifo/master/aw_burst
add wave -noupdate -expand -group {Master AW} /tb_axi_fifo/master/aw_lock
add wave -noupdate -expand -group {Master AW} /tb_axi_fifo/master/aw_cache
add wave -noupdate -expand -group {Master AW} /tb_axi_fifo/master/aw_prot
add wave -noupdate -expand -group {Master AW} /tb_axi_fifo/master/aw_qos
add wave -noupdate -expand -group {Master AW} /tb_axi_fifo/master/aw_region
add wave -noupdate -expand -group {Master AW} /tb_axi_fifo/master/aw_atop
add wave -noupdate -expand -group {Master AW} /tb_axi_fifo/master/aw_user
add wave -noupdate -expand -group {Master AW} /tb_axi_fifo/master/aw_valid
add wave -noupdate -expand -group {Master AW} /tb_axi_fifo/master/aw_ready
add wave -noupdate -group {Master W} /tb_axi_fifo/master/w_data
add wave -noupdate -group {Master W} /tb_axi_fifo/master/w_strb
add wave -noupdate -group {Master W} /tb_axi_fifo/master/w_last
add wave -noupdate -group {Master W} /tb_axi_fifo/master/w_user
add wave -noupdate -group {Master W} /tb_axi_fifo/master/w_valid
add wave -noupdate -group {Master W} /tb_axi_fifo/master/w_ready
add wave -noupdate -group {Master B} /tb_axi_fifo/master/b_id
add wave -noupdate -group {Master B} /tb_axi_fifo/master/b_resp
add wave -noupdate -group {Master B} /tb_axi_fifo/master/b_user
add wave -noupdate -group {Master B} /tb_axi_fifo/master/b_valid
add wave -noupdate -group {Master B} /tb_axi_fifo/master/b_ready
add wave -noupdate -expand -group {Master AR} /tb_axi_fifo/master/ar_id
add wave -noupdate -expand -group {Master AR} /tb_axi_fifo/master/ar_addr
add wave -noupdate -expand -group {Master AR} /tb_axi_fifo/master/ar_len
add wave -noupdate -expand -group {Master AR} /tb_axi_fifo/master/ar_size
add wave -noupdate -expand -group {Master AR} /tb_axi_fifo/master/ar_burst
add wave -noupdate -expand -group {Master AR} /tb_axi_fifo/master/ar_lock
add wave -noupdate -expand -group {Master AR} /tb_axi_fifo/master/ar_cache
add wave -noupdate -expand -group {Master AR} /tb_axi_fifo/master/ar_prot
add wave -noupdate -expand -group {Master AR} /tb_axi_fifo/master/ar_qos
add wave -noupdate -expand -group {Master AR} /tb_axi_fifo/master/ar_region
add wave -noupdate -expand -group {Master AR} /tb_axi_fifo/master/ar_user
add wave -noupdate -expand -group {Master AR} /tb_axi_fifo/master/ar_valid
add wave -noupdate -expand -group {Master AR} /tb_axi_fifo/master/ar_ready
add wave -noupdate -group {Master R} /tb_axi_fifo/master/r_id
add wave -noupdate -group {Master R} /tb_axi_fifo/master/r_data
add wave -noupdate -group {Master R} /tb_axi_fifo/master/r_resp
add wave -noupdate -group {Master R} /tb_axi_fifo/master/r_last
add wave -noupdate -group {Master R} /tb_axi_fifo/master/r_user
add wave -noupdate -group {Master R} /tb_axi_fifo/master/r_valid
add wave -noupdate -group {Master R} /tb_axi_fifo/master/r_ready
add wave -noupdate -divider {Master Ports}
add wave -noupdate -expand -group {Slave AW} /tb_axi_fifo/slave/aw_id
add wave -noupdate -expand -group {Slave AW} /tb_axi_fifo/slave/aw_addr
add wave -noupdate -expand -group {Slave AW} /tb_axi_fifo/slave/aw_len
add wave -noupdate -expand -group {Slave AW} /tb_axi_fifo/slave/aw_size
add wave -noupdate -expand -group {Slave AW} /tb_axi_fifo/slave/aw_burst
add wave -noupdate -expand -group {Slave AW} /tb_axi_fifo/slave/aw_lock
add wave -noupdate -expand -group {Slave AW} /tb_axi_fifo/slave/aw_cache
add wave -noupdate -expand -group {Slave AW} /tb_axi_fifo/slave/aw_prot
add wave -noupdate -expand -group {Slave AW} /tb_axi_fifo/slave/aw_qos
add wave -noupdate -expand -group {Slave AW} /tb_axi_fifo/slave/aw_region
add wave -noupdate -expand -group {Slave AW} /tb_axi_fifo/slave/aw_atop
add wave -noupdate -expand -group {Slave AW} /tb_axi_fifo/slave/aw_user
add wave -noupdate -expand -group {Slave AW} /tb_axi_fifo/slave/aw_valid
add wave -noupdate -expand -group {Slave AW} /tb_axi_fifo/slave/aw_ready
add wave -noupdate -group {Slave W} /tb_axi_fifo/slave/w_data
add wave -noupdate -group {Slave W} /tb_axi_fifo/slave/w_strb
add wave -noupdate -group {Slave W} /tb_axi_fifo/slave/w_last
add wave -noupdate -group {Slave W} /tb_axi_fifo/slave/w_user
add wave -noupdate -group {Slave W} /tb_axi_fifo/slave/w_valid
add wave -noupdate -group {Slave W} /tb_axi_fifo/slave/w_ready
add wave -noupdate -group {Slave B} /tb_axi_fifo/slave/b_id
add wave -noupdate -group {Slave B} /tb_axi_fifo/slave/b_resp
add wave -noupdate -group {Slave B} /tb_axi_fifo/slave/b_user
add wave -noupdate -group {Slave B} /tb_axi_fifo/slave/b_valid
add wave -noupdate -group {Slave B} /tb_axi_fifo/slave/b_ready
add wave -noupdate -expand -group {Slave AR} /tb_axi_fifo/slave/ar_id
add wave -noupdate -expand -group {Slave AR} /tb_axi_fifo/slave/ar_addr
add wave -noupdate -expand -group {Slave AR} /tb_axi_fifo/slave/ar_len
add wave -noupdate -expand -group {Slave AR} /tb_axi_fifo/slave/ar_size
add wave -noupdate -expand -group {Slave AR} /tb_axi_fifo/slave/ar_burst
add wave -noupdate -expand -group {Slave AR} /tb_axi_fifo/slave/ar_lock
add wave -noupdate -expand -group {Slave AR} /tb_axi_fifo/slave/ar_cache
add wave -noupdate -expand -group {Slave AR} /tb_axi_fifo/slave/ar_prot
add wave -noupdate -expand -group {Slave AR} /tb_axi_fifo/slave/ar_qos
add wave -noupdate -expand -group {Slave AR} /tb_axi_fifo/slave/ar_region
add wave -noupdate -expand -group {Slave AR} /tb_axi_fifo/slave/ar_user
add wave -noupdate -expand -group {Slave AR} /tb_axi_fifo/slave/ar_valid
add wave -noupdate -expand -group {Slave AR} /tb_axi_fifo/slave/ar_ready
add wave -noupdate -group {Slave R} /tb_axi_fifo/slave/r_id
add wave -noupdate -group {Slave R} /tb_axi_fifo/slave/r_data
add wave -noupdate -group {Slave R} /tb_axi_fifo/slave/r_resp
add wave -noupdate -group {Slave R} /tb_axi_fifo/slave/r_last
add wave -noupdate -group {Slave R} /tb_axi_fifo/slave/r_user
add wave -noupdate -group {Slave R} /tb_axi_fifo/slave/r_valid
add wave -noupdate -group {Slave R} /tb_axi_fifo/slave/r_ready
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
add wave -noupdate -expand -group {DUT slv AW} /tb_axi_fifo/i_dut/i_axi_fifo/slv_req_i.aw_valid
add wave -noupdate -expand -group {DUT slv AW} /tb_axi_fifo/i_dut/i_axi_fifo/slv_resp_o.aw_ready
add wave -noupdate -expand -group {DUT slv AW} /tb_axi_fifo/i_dut/i_axi_fifo/slv_req_i.aw
add wave -noupdate -expand -group {DUT slv W} /tb_axi_fifo/i_dut/i_axi_fifo/slv_req_i.w
add wave -noupdate -expand -group {DUT slv W} /tb_axi_fifo/i_dut/i_axi_fifo/slv_req_i.w_valid
add wave -noupdate -expand -group {DUT slv W} /tb_axi_fifo/i_dut/i_axi_fifo/slv_resp_o.w_ready
add wave -noupdate -expand -group {DUT slv B} /tb_axi_fifo/i_dut/i_axi_fifo/slv_resp_o.b_valid
add wave -noupdate -expand -group {DUT slv B} /tb_axi_fifo/i_dut/i_axi_fifo/slv_req_i.b_ready
add wave -noupdate -expand -group {DUT slv B} /tb_axi_fifo/i_dut/i_axi_fifo/slv_resp_o.b
add wave -noupdate -expand -group {DUT slv AR} /tb_axi_fifo/i_dut/i_axi_fifo/slv_req_i.ar_valid
add wave -noupdate -expand -group {DUT slv AR} /tb_axi_fifo/i_dut/i_axi_fifo/slv_resp_o.ar_ready
add wave -noupdate -expand -group {DUT slv AR} /tb_axi_fifo/i_dut/i_axi_fifo/slv_req_i.ar
add wave -noupdate -expand -group {DUT slv R} /tb_axi_fifo/i_dut/i_axi_fifo/slv_resp_o.r_valid
add wave -noupdate -expand -group {DUT slv R} /tb_axi_fifo/i_dut/i_axi_fifo/slv_req_i.r_ready
add wave -noupdate -expand -group {DUT slv R} /tb_axi_fifo/i_dut/i_axi_fifo/slv_resp_o.r
add wave -noupdate -expand -group {DUT mst AW} /tb_axi_fifo/i_dut/i_axi_fifo/mst_req_o.aw_valid
add wave -noupdate -expand -group {DUT mst AW} /tb_axi_fifo/i_dut/i_axi_fifo/mst_resp_i.aw_ready
add wave -noupdate -expand -group {DUT mst AW} /tb_axi_fifo/i_dut/i_axi_fifo/mst_req_o.aw
add wave -noupdate -expand -group {DUT mst W} /tb_axi_fifo/i_dut/i_axi_fifo/mst_req_o.w
add wave -noupdate -expand -group {DUT mst W} /tb_axi_fifo/i_dut/i_axi_fifo/mst_req_o.w_valid
add wave -noupdate -expand -group {DUT mst W} /tb_axi_fifo/i_dut/i_axi_fifo/mst_resp_i.w_ready
add wave -noupdate -expand -group {DUT mst B} /tb_axi_fifo/i_dut/i_axi_fifo/mst_resp_i.b_valid
add wave -noupdate -expand -group {DUT mst B} /tb_axi_fifo/i_dut/i_axi_fifo/mst_req_o.b_ready
add wave -noupdate -expand -group {DUT mst B} /tb_axi_fifo/i_dut/i_axi_fifo/mst_resp_i.b
add wave -noupdate -expand -group {DUT mst AR} /tb_axi_fifo/i_dut/i_axi_fifo/mst_req_o.ar_valid
add wave -noupdate -expand -group {DUT mst AR} /tb_axi_fifo/i_dut/i_axi_fifo/mst_resp_i.ar_ready
add wave -noupdate -expand -group {DUT mst AR} /tb_axi_fifo/i_dut/i_axi_fifo/mst_req_o.ar
add wave -noupdate -expand -group {DUT mst R} /tb_axi_fifo/i_dut/i_axi_fifo/mst_resp_i.r_valid
add wave -noupdate -expand -group {DUT mst R} /tb_axi_fifo/i_dut/i_axi_fifo/mst_req_o.r_ready
add wave -noupdate -expand -group {DUT mst R} /tb_axi_fifo/i_dut/i_axi_fifo/mst_resp_i.r
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
