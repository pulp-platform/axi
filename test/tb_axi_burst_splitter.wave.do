onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate -expand -group upstream /tb_axi_burst_splitter/upstream/aw_id
add wave -noupdate -expand -group upstream /tb_axi_burst_splitter/upstream/aw_addr
add wave -noupdate -expand -group upstream /tb_axi_burst_splitter/upstream/aw_len
add wave -noupdate -expand -group upstream /tb_axi_burst_splitter/upstream/aw_size
add wave -noupdate -expand -group upstream /tb_axi_burst_splitter/upstream/aw_burst
add wave -noupdate -expand -group upstream /tb_axi_burst_splitter/upstream/aw_lock
add wave -noupdate -expand -group upstream /tb_axi_burst_splitter/upstream/aw_cache
add wave -noupdate -expand -group upstream /tb_axi_burst_splitter/upstream/aw_prot
add wave -noupdate -expand -group upstream /tb_axi_burst_splitter/upstream/aw_qos
add wave -noupdate -expand -group upstream /tb_axi_burst_splitter/upstream/aw_region
add wave -noupdate -expand -group upstream /tb_axi_burst_splitter/upstream/aw_atop
add wave -noupdate -expand -group upstream /tb_axi_burst_splitter/upstream/aw_user
add wave -noupdate -expand -group upstream /tb_axi_burst_splitter/upstream/aw_valid
add wave -noupdate -expand -group upstream /tb_axi_burst_splitter/upstream/aw_ready
add wave -noupdate -expand -group upstream /tb_axi_burst_splitter/upstream/w_data
add wave -noupdate -expand -group upstream /tb_axi_burst_splitter/upstream/w_strb
add wave -noupdate -expand -group upstream /tb_axi_burst_splitter/upstream/w_last
add wave -noupdate -expand -group upstream /tb_axi_burst_splitter/upstream/w_user
add wave -noupdate -expand -group upstream /tb_axi_burst_splitter/upstream/w_valid
add wave -noupdate -expand -group upstream /tb_axi_burst_splitter/upstream/w_ready
add wave -noupdate -expand -group upstream /tb_axi_burst_splitter/upstream/b_id
add wave -noupdate -expand -group upstream /tb_axi_burst_splitter/upstream/b_resp
add wave -noupdate -expand -group upstream /tb_axi_burst_splitter/upstream/b_user
add wave -noupdate -expand -group upstream /tb_axi_burst_splitter/upstream/b_valid
add wave -noupdate -expand -group upstream /tb_axi_burst_splitter/upstream/b_ready
add wave -noupdate -expand -group upstream /tb_axi_burst_splitter/upstream/ar_id
add wave -noupdate -expand -group upstream /tb_axi_burst_splitter/upstream/ar_addr
add wave -noupdate -expand -group upstream /tb_axi_burst_splitter/upstream/ar_len
add wave -noupdate -expand -group upstream /tb_axi_burst_splitter/upstream/ar_size
add wave -noupdate -expand -group upstream /tb_axi_burst_splitter/upstream/ar_burst
add wave -noupdate -expand -group upstream /tb_axi_burst_splitter/upstream/ar_lock
add wave -noupdate -expand -group upstream /tb_axi_burst_splitter/upstream/ar_cache
add wave -noupdate -expand -group upstream /tb_axi_burst_splitter/upstream/ar_prot
add wave -noupdate -expand -group upstream /tb_axi_burst_splitter/upstream/ar_qos
add wave -noupdate -expand -group upstream /tb_axi_burst_splitter/upstream/ar_region
add wave -noupdate -expand -group upstream /tb_axi_burst_splitter/upstream/ar_user
add wave -noupdate -expand -group upstream /tb_axi_burst_splitter/upstream/ar_valid
add wave -noupdate -expand -group upstream /tb_axi_burst_splitter/upstream/ar_ready
add wave -noupdate -expand -group upstream /tb_axi_burst_splitter/upstream/r_id
add wave -noupdate -expand -group upstream /tb_axi_burst_splitter/upstream/r_data
add wave -noupdate -expand -group upstream /tb_axi_burst_splitter/upstream/r_resp
add wave -noupdate -expand -group upstream /tb_axi_burst_splitter/upstream/r_last
add wave -noupdate -expand -group upstream /tb_axi_burst_splitter/upstream/r_user
add wave -noupdate -expand -group upstream /tb_axi_burst_splitter/upstream/r_valid
add wave -noupdate -expand -group upstream /tb_axi_burst_splitter/upstream/r_ready
add wave -noupdate -group downstream /tb_axi_burst_splitter/downstream/aw_id
add wave -noupdate -group downstream /tb_axi_burst_splitter/downstream/aw_addr
add wave -noupdate -group downstream /tb_axi_burst_splitter/downstream/aw_len
add wave -noupdate -group downstream /tb_axi_burst_splitter/downstream/aw_size
add wave -noupdate -group downstream /tb_axi_burst_splitter/downstream/aw_burst
add wave -noupdate -group downstream /tb_axi_burst_splitter/downstream/aw_lock
add wave -noupdate -group downstream /tb_axi_burst_splitter/downstream/aw_cache
add wave -noupdate -group downstream /tb_axi_burst_splitter/downstream/aw_prot
add wave -noupdate -group downstream /tb_axi_burst_splitter/downstream/aw_qos
add wave -noupdate -group downstream /tb_axi_burst_splitter/downstream/aw_region
add wave -noupdate -group downstream /tb_axi_burst_splitter/downstream/aw_atop
add wave -noupdate -group downstream /tb_axi_burst_splitter/downstream/aw_user
add wave -noupdate -group downstream /tb_axi_burst_splitter/downstream/aw_valid
add wave -noupdate -group downstream /tb_axi_burst_splitter/downstream/aw_ready
add wave -noupdate -group downstream /tb_axi_burst_splitter/downstream/w_data
add wave -noupdate -group downstream /tb_axi_burst_splitter/downstream/w_strb
add wave -noupdate -group downstream /tb_axi_burst_splitter/downstream/w_last
add wave -noupdate -group downstream /tb_axi_burst_splitter/downstream/w_user
add wave -noupdate -group downstream /tb_axi_burst_splitter/downstream/w_valid
add wave -noupdate -group downstream /tb_axi_burst_splitter/downstream/w_ready
add wave -noupdate -group downstream /tb_axi_burst_splitter/downstream/b_id
add wave -noupdate -group downstream /tb_axi_burst_splitter/downstream/b_resp
add wave -noupdate -group downstream /tb_axi_burst_splitter/downstream/b_user
add wave -noupdate -group downstream /tb_axi_burst_splitter/downstream/b_valid
add wave -noupdate -group downstream /tb_axi_burst_splitter/downstream/b_ready
add wave -noupdate -group downstream /tb_axi_burst_splitter/downstream/ar_id
add wave -noupdate -group downstream /tb_axi_burst_splitter/downstream/ar_addr
add wave -noupdate -group downstream /tb_axi_burst_splitter/downstream/ar_len
add wave -noupdate -group downstream /tb_axi_burst_splitter/downstream/ar_size
add wave -noupdate -group downstream /tb_axi_burst_splitter/downstream/ar_burst
add wave -noupdate -group downstream /tb_axi_burst_splitter/downstream/ar_lock
add wave -noupdate -group downstream /tb_axi_burst_splitter/downstream/ar_cache
add wave -noupdate -group downstream /tb_axi_burst_splitter/downstream/ar_prot
add wave -noupdate -group downstream /tb_axi_burst_splitter/downstream/ar_qos
add wave -noupdate -group downstream /tb_axi_burst_splitter/downstream/ar_region
add wave -noupdate -group downstream /tb_axi_burst_splitter/downstream/ar_user
add wave -noupdate -group downstream /tb_axi_burst_splitter/downstream/ar_valid
add wave -noupdate -group downstream /tb_axi_burst_splitter/downstream/ar_ready
add wave -noupdate -group downstream /tb_axi_burst_splitter/downstream/r_id
add wave -noupdate -group downstream /tb_axi_burst_splitter/downstream/r_data
add wave -noupdate -group downstream /tb_axi_burst_splitter/downstream/r_resp
add wave -noupdate -group downstream /tb_axi_burst_splitter/downstream/r_last
add wave -noupdate -group downstream /tb_axi_burst_splitter/downstream/r_user
add wave -noupdate -group downstream /tb_axi_burst_splitter/downstream/r_valid
add wave -noupdate -group downstream /tb_axi_burst_splitter/downstream/r_ready
add wave -noupdate -group r_cnt /tb_axi_burst_splitter/dut/r_cnt_dec
add wave -noupdate -group r_cnt /tb_axi_burst_splitter/dut/r_cnt_set
add wave -noupdate -group r_cnt /tb_axi_burst_splitter/dut/r_cnt_inp
add wave -noupdate -group r_cnt /tb_axi_burst_splitter/dut/r_cnt_oup
add wave -noupdate -group r_cnt /tb_axi_burst_splitter/dut/r_cnt_free
add wave -noupdate -group r_cnt /tb_axi_burst_splitter/dut/r_cnt_free_idx
add wave -noupdate -group r_cnt /tb_axi_burst_splitter/dut/r_cnt_r_idx
add wave -noupdate -group r_cnt /tb_axi_burst_splitter/dut/r_cnt_idq_inp_req
add wave -noupdate -group r_cnt /tb_axi_burst_splitter/dut/r_cnt_idq_inp_gnt
add wave -noupdate -group r_cnt /tb_axi_burst_splitter/dut/r_cnt_idq_oup_gnt
add wave -noupdate -group r_cnt /tb_axi_burst_splitter/dut/r_cnt_idq_oup_valid
add wave -noupdate -group r_cnt /tb_axi_burst_splitter/dut/r_cnt_idq_pop
add wave -noupdate /tb_axi_burst_splitter/dut/ar_state_q
add wave -noupdate /tb_axi_burst_splitter/dut/r_last_q
add wave -noupdate /tb_axi_burst_splitter/dut/r_state_q
add wave -noupdate -group r_cnt_idq /tb_axi_burst_splitter/dut/i_r_cnt_idq/inp_id_i
add wave -noupdate -group r_cnt_idq /tb_axi_burst_splitter/dut/i_r_cnt_idq/inp_data_i
add wave -noupdate -group r_cnt_idq /tb_axi_burst_splitter/dut/i_r_cnt_idq/inp_req_i
add wave -noupdate -group r_cnt_idq /tb_axi_burst_splitter/dut/i_r_cnt_idq/inp_gnt_o
add wave -noupdate -group r_cnt_idq /tb_axi_burst_splitter/dut/i_r_cnt_idq/oup_id_i
add wave -noupdate -group r_cnt_idq /tb_axi_burst_splitter/dut/i_r_cnt_idq/oup_pop_i
add wave -noupdate -group r_cnt_idq /tb_axi_burst_splitter/dut/i_r_cnt_idq/oup_req_i
add wave -noupdate -group r_cnt_idq /tb_axi_burst_splitter/dut/i_r_cnt_idq/oup_data_o
add wave -noupdate -group r_cnt_idq /tb_axi_burst_splitter/dut/i_r_cnt_idq/oup_data_valid_o
add wave -noupdate -group r_cnt_idq /tb_axi_burst_splitter/dut/i_r_cnt_idq/oup_gnt_o
add wave -noupdate -group r_cnt_idq /tb_axi_burst_splitter/dut/i_r_cnt_idq/head_tail_d
add wave -noupdate -group r_cnt_idq /tb_axi_burst_splitter/dut/i_r_cnt_idq/head_tail_q
add wave -noupdate -group r_cnt_idq /tb_axi_burst_splitter/dut/i_r_cnt_idq/linked_data_d
add wave -noupdate -group r_cnt_idq /tb_axi_burst_splitter/dut/i_r_cnt_idq/linked_data_q
add wave -noupdate -group r_cnt_idq /tb_axi_burst_splitter/dut/i_r_cnt_idq/full
add wave -noupdate -group r_cnt_idq /tb_axi_burst_splitter/dut/i_r_cnt_idq/match_id_valid
add wave -noupdate -group r_cnt_idq /tb_axi_burst_splitter/dut/i_r_cnt_idq/no_id_match
add wave -noupdate -group r_cnt_idq /tb_axi_burst_splitter/dut/i_r_cnt_idq/head_tail_free
add wave -noupdate -group r_cnt_idq /tb_axi_burst_splitter/dut/i_r_cnt_idq/idx_matches_id
add wave -noupdate -group r_cnt_idq /tb_axi_burst_splitter/dut/i_r_cnt_idq/exists_match
add wave -noupdate -group r_cnt_idq /tb_axi_burst_splitter/dut/i_r_cnt_idq/linked_data_free
add wave -noupdate -group r_cnt_idq /tb_axi_burst_splitter/dut/i_r_cnt_idq/match_id
add wave -noupdate -group r_cnt_idq /tb_axi_burst_splitter/dut/i_r_cnt_idq/head_tail_free_idx
add wave -noupdate -group r_cnt_idq /tb_axi_burst_splitter/dut/i_r_cnt_idq/match_idx
add wave -noupdate -group r_cnt_idq /tb_axi_burst_splitter/dut/i_r_cnt_idq/linked_data_free_idx
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {401263200 ps} 0}
quietly wave cursor active 1
configure wave -namecolwidth 182
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
configure wave -timelineunits ps
update
WaveRestoreZoom {394414020 ps} {408174020 ps}
