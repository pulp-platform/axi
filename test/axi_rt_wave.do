onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate /tb_axi_rt_unit/i_axi_rt_unit/clk_i
add wave -noupdate /tb_axi_rt_unit/i_axi_rt_unit/rst_ni
add wave -noupdate -divider -height 30 {AXI IN}
add wave -noupdate /tb_axi_rt_unit/i_axi_rt_unit/slv_req_i
add wave -noupdate /tb_axi_rt_unit/i_axi_rt_unit/slv_resp_o
add wave -noupdate -divider -height 30 {AXI OUT}
add wave -noupdate /tb_axi_rt_unit/i_axi_rt_unit/mst_req_o
add wave -noupdate /tb_axi_rt_unit/i_axi_rt_unit/mst_resp_i
add wave -noupdate -divider -height 30 {Top Signals}
add wave -noupdate -group {Top-level Signals} /tb_axi_rt_unit/i_axi_rt_unit/rt_enable_i
add wave -noupdate -group {Top-level Signals} /tb_axi_rt_unit/i_axi_rt_unit/rt_bypassed_o
add wave -noupdate -group {Top-level Signals} /tb_axi_rt_unit/i_axi_rt_unit/len_limit_i
add wave -noupdate -group {Top-level Signals} /tb_axi_rt_unit/i_axi_rt_unit/num_w_pending_o
add wave -noupdate -group {Top-level Signals} /tb_axi_rt_unit/i_axi_rt_unit/num_aw_pending_o
add wave -noupdate -group {Top-level Signals} /tb_axi_rt_unit/i_axi_rt_unit/rt_rule_i
add wave -noupdate -group {Top-level Signals} /tb_axi_rt_unit/i_axi_rt_unit/w_decode_error_o
add wave -noupdate -group {Top-level Signals} /tb_axi_rt_unit/i_axi_rt_unit/r_decode_error_o
add wave -noupdate -group {Top-level Signals} /tb_axi_rt_unit/i_axi_rt_unit/imtu_enable_i
add wave -noupdate -group {Top-level Signals} /tb_axi_rt_unit/i_axi_rt_unit/imtu_abort_i
add wave -noupdate -group {Top-level Signals} /tb_axi_rt_unit/i_axi_rt_unit/w_budget_i
add wave -noupdate -group {Top-level Signals} /tb_axi_rt_unit/i_axi_rt_unit/w_budget_left_o
add wave -noupdate -group {Top-level Signals} /tb_axi_rt_unit/i_axi_rt_unit/w_period_i
add wave -noupdate -group {Top-level Signals} /tb_axi_rt_unit/i_axi_rt_unit/w_period_left_o
add wave -noupdate -group {Top-level Signals} /tb_axi_rt_unit/i_axi_rt_unit/r_budget_i
add wave -noupdate -group {Top-level Signals} /tb_axi_rt_unit/i_axi_rt_unit/r_budget_left_o
add wave -noupdate -group {Top-level Signals} /tb_axi_rt_unit/i_axi_rt_unit/r_period_i
add wave -noupdate -group {Top-level Signals} /tb_axi_rt_unit/i_axi_rt_unit/r_period_left_o
add wave -noupdate -group {Top-level Signals} /tb_axi_rt_unit/i_axi_rt_unit/isolate_o
add wave -noupdate -group {Top-level Signals} /tb_axi_rt_unit/i_axi_rt_unit/isolated_o
add wave -noupdate -group {Isolate Stage} /tb_axi_rt_unit/i_axi_rt_unit/i_axi_isolate/clk_i
add wave -noupdate -group {Isolate Stage} /tb_axi_rt_unit/i_axi_rt_unit/i_axi_isolate/rst_ni
add wave -noupdate -group {Isolate Stage} /tb_axi_rt_unit/i_axi_rt_unit/i_axi_isolate/slv_req_i
add wave -noupdate -group {Isolate Stage} /tb_axi_rt_unit/i_axi_rt_unit/i_axi_isolate/slv_resp_o
add wave -noupdate -group {Isolate Stage} /tb_axi_rt_unit/i_axi_rt_unit/i_axi_isolate/mst_req_o
add wave -noupdate -group {Isolate Stage} /tb_axi_rt_unit/i_axi_rt_unit/i_axi_isolate/mst_resp_i
add wave -noupdate -group {Isolate Stage} /tb_axi_rt_unit/i_axi_rt_unit/i_axi_isolate/isolate_i
add wave -noupdate -group {Isolate Stage} /tb_axi_rt_unit/i_axi_rt_unit/i_axi_isolate/isolated_o
add wave -noupdate -group {Burst Splitter} /tb_axi_rt_unit/i_axi_rt_unit/i_axi_burst_splitter/clk_i
add wave -noupdate -group {Burst Splitter} /tb_axi_rt_unit/i_axi_rt_unit/i_axi_burst_splitter/rst_ni
add wave -noupdate -group {Burst Splitter} /tb_axi_rt_unit/i_axi_rt_unit/i_axi_burst_splitter/len_limit_i
add wave -noupdate -group {Burst Splitter} /tb_axi_rt_unit/i_axi_rt_unit/i_axi_burst_splitter/slv_req_i
add wave -noupdate -group {Burst Splitter} /tb_axi_rt_unit/i_axi_rt_unit/i_axi_burst_splitter/slv_resp_o
add wave -noupdate -group {Burst Splitter} -expand /tb_axi_rt_unit/i_axi_rt_unit/i_axi_burst_splitter/mst_req_o
add wave -noupdate -group {Burst Splitter} -expand /tb_axi_rt_unit/i_axi_rt_unit/i_axi_burst_splitter/mst_resp_i
add wave -noupdate -group {Write Buffer} /tb_axi_rt_unit/i_axi_rt_unit/i_axi_write_buffer/clk_i
add wave -noupdate -group {Write Buffer} /tb_axi_rt_unit/i_axi_rt_unit/i_axi_write_buffer/rst_ni
add wave -noupdate -group {Write Buffer} /tb_axi_rt_unit/i_axi_rt_unit/i_axi_write_buffer/slv_req_i
add wave -noupdate -group {Write Buffer} /tb_axi_rt_unit/i_axi_rt_unit/i_axi_write_buffer/slv_resp_o
add wave -noupdate -group {Write Buffer} -expand /tb_axi_rt_unit/i_axi_rt_unit/i_axi_write_buffer/mst_req_o
add wave -noupdate -group {Write Buffer} -expand /tb_axi_rt_unit/i_axi_rt_unit/i_axi_write_buffer/mst_resp_i
add wave -noupdate -group {Write Buffer} /tb_axi_rt_unit/i_axi_rt_unit/i_axi_write_buffer/num_w_stored_o
add wave -noupdate -group {Write Buffer} /tb_axi_rt_unit/i_axi_rt_unit/i_axi_write_buffer/num_aw_stored_o
add wave -noupdate -group {Write Buffer Internals} /tb_axi_rt_unit/i_axi_rt_unit/i_axi_write_buffer/clk_i
add wave -noupdate -group {Write Buffer Internals} /tb_axi_rt_unit/i_axi_rt_unit/i_axi_write_buffer/rst_ni
add wave -noupdate -group {Write Buffer Internals} /tb_axi_rt_unit/i_axi_rt_unit/i_axi_write_buffer/slv_req_i
add wave -noupdate -group {Write Buffer Internals} /tb_axi_rt_unit/i_axi_rt_unit/i_axi_write_buffer/slv_resp_o
add wave -noupdate -group {Write Buffer Internals} -expand /tb_axi_rt_unit/i_axi_rt_unit/i_axi_write_buffer/mst_req_o
add wave -noupdate -group {Write Buffer Internals} -expand /tb_axi_rt_unit/i_axi_rt_unit/i_axi_write_buffer/mst_resp_i
add wave -noupdate -group {Write Buffer Internals} /tb_axi_rt_unit/i_axi_rt_unit/i_axi_write_buffer/num_w_stored_o
add wave -noupdate -group {Write Buffer Internals} /tb_axi_rt_unit/i_axi_rt_unit/i_axi_write_buffer/num_aw_stored_o
add wave -noupdate -group {Write Buffer Internals} /tb_axi_rt_unit/i_axi_rt_unit/i_axi_write_buffer/ingress_w_last
add wave -noupdate -group {Write Buffer Internals} /tb_axi_rt_unit/i_axi_rt_unit/i_axi_write_buffer/egress_w_last
add wave -noupdate -group {Write Buffer Internals} /tb_axi_rt_unit/i_axi_rt_unit/i_axi_write_buffer/egress_w_ready
add wave -noupdate -group {Write Buffer Internals} /tb_axi_rt_unit/i_axi_rt_unit/i_axi_write_buffer/egress_w_valid
add wave -noupdate -group {Write Buffer Internals} /tb_axi_rt_unit/i_axi_rt_unit/i_axi_write_buffer/egress_aw_ready
add wave -noupdate -group {Write Buffer Internals} /tb_axi_rt_unit/i_axi_rt_unit/i_axi_write_buffer/egress_aw_valid
add wave -noupdate -group {Write Buffer Internals} /tb_axi_rt_unit/i_axi_rt_unit/i_axi_write_buffer/mgmt_ready_w
add wave -noupdate -group {Write Buffer Internals} /tb_axi_rt_unit/i_axi_rt_unit/i_axi_write_buffer/mgmt_ready_aw
add wave -noupdate -group {Write Buffer Internals} /tb_axi_rt_unit/i_axi_rt_unit/i_axi_write_buffer/mgmt_valid_w
add wave -noupdate -group {Write Buffer Internals} /tb_axi_rt_unit/i_axi_rt_unit/i_axi_write_buffer/mgmt_valid_aw
add wave -noupdate -group {Write Buffer Internals} /tb_axi_rt_unit/i_axi_rt_unit/i_axi_write_buffer/num_lasts_d
add wave -noupdate -group {Write Buffer Internals} /tb_axi_rt_unit/i_axi_rt_unit/i_axi_write_buffer/num_lasts_q
TreeUpdate [SetDefaultTree]
quietly WaveActivateNextPane
WaveRestoreCursors {{Cursor 1} {9392776 ps} 0}
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
WaveRestoreZoom {445340 ps} {1197614 ps}
