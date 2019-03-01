onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate -expand -group dut/apb /tb_axi_perf_mon/dut/pclk_i
add wave -noupdate -expand -group dut/apb /tb_axi_perf_mon/dut/preset_ni
add wave -noupdate -expand -group dut/apb /tb_axi_perf_mon/dut/paddr_i
add wave -noupdate -expand -group dut/apb /tb_axi_perf_mon/dut/pprot_i
add wave -noupdate -expand -group dut/apb /tb_axi_perf_mon/dut/psel_i
add wave -noupdate -expand -group dut/apb /tb_axi_perf_mon/dut/penable_i
add wave -noupdate -expand -group dut/apb /tb_axi_perf_mon/dut/pwrite_i
add wave -noupdate -expand -group dut/apb /tb_axi_perf_mon/dut/pwdata_i
add wave -noupdate -expand -group dut/apb /tb_axi_perf_mon/dut/pstrb_i
add wave -noupdate -expand -group dut/apb /tb_axi_perf_mon/dut/pready_o
add wave -noupdate -expand -group dut/apb /tb_axi_perf_mon/dut/prdata_o
add wave -noupdate -expand -group dut/apb /tb_axi_perf_mon/dut/pslverr_o
add wave -noupdate -expand -group {dut/axi[0]} {/tb_axi_perf_mon/dut/clk_axi_i[0]}
add wave -noupdate -expand -group {dut/axi[0]} {/tb_axi_perf_mon/dut/rst_axi_ni[0]}
add wave -noupdate -expand -group {dut/axi[0]} {/tb_axi_perf_mon/dut/ar_id_i[0]}
add wave -noupdate -expand -group {dut/axi[0]} {/tb_axi_perf_mon/dut/ar_len_i[0]}
add wave -noupdate -expand -group {dut/axi[0]} {/tb_axi_perf_mon/dut/ar_size_i[0]}
add wave -noupdate -expand -group {dut/axi[0]} {/tb_axi_perf_mon/dut/ar_lock_i[0]}
add wave -noupdate -expand -group {dut/axi[0]} {/tb_axi_perf_mon/dut/ar_valid_i[0]}
add wave -noupdate -expand -group {dut/axi[0]} {/tb_axi_perf_mon/dut/ar_ready_i[0]}
add wave -noupdate -expand -group {dut/axi[0]} {/tb_axi_perf_mon/dut/aw_id_i[0]}
add wave -noupdate -expand -group {dut/axi[0]} {/tb_axi_perf_mon/dut/aw_len_i[0]}
add wave -noupdate -expand -group {dut/axi[0]} {/tb_axi_perf_mon/dut/aw_size_i[0]}
add wave -noupdate -expand -group {dut/axi[0]} {/tb_axi_perf_mon/dut/aw_lock_i[0]}
add wave -noupdate -expand -group {dut/axi[0]} {/tb_axi_perf_mon/dut/aw_atop_i[0]}
add wave -noupdate -expand -group {dut/axi[0]} {/tb_axi_perf_mon/dut/aw_valid_i[0]}
add wave -noupdate -expand -group {dut/axi[0]} {/tb_axi_perf_mon/dut/aw_ready_i[0]}
add wave -noupdate -expand -group {dut/axi[0]} {/tb_axi_perf_mon/dut/r_id_i[0]}
add wave -noupdate -expand -group {dut/axi[0]} {/tb_axi_perf_mon/dut/r_last_i[0]}
add wave -noupdate -expand -group {dut/axi[0]} {/tb_axi_perf_mon/dut/r_valid_i[0]}
add wave -noupdate -expand -group {dut/axi[0]} {/tb_axi_perf_mon/dut/r_ready_i[0]}
add wave -noupdate -expand -group {dut/axi[0]} {/tb_axi_perf_mon/dut/w_last_i[0]}
add wave -noupdate -expand -group {dut/axi[0]} {/tb_axi_perf_mon/dut/w_valid_i[0]}
add wave -noupdate -expand -group {dut/axi[0]} {/tb_axi_perf_mon/dut/w_ready_i[0]}
add wave -noupdate -expand -group {dut/axi[0]} {/tb_axi_perf_mon/dut/b_id_i[0]}
add wave -noupdate -expand -group {dut/axi[0]} {/tb_axi_perf_mon/dut/b_resp_i[0]}
add wave -noupdate -expand -group {dut/axi[0]} {/tb_axi_perf_mon/dut/b_valid_i[0]}
add wave -noupdate -expand -group {dut/axi[0]} {/tb_axi_perf_mon/dut/b_ready_i[0]}
add wave -noupdate -group {dut/mon[0]/ctrl_reg} {/tb_axi_perf_mon/dut/gen_mon[0]/i_ctrl_reg/pclk_i}
add wave -noupdate -group {dut/mon[0]/ctrl_reg} {/tb_axi_perf_mon/dut/gen_mon[0]/i_ctrl_reg/preset_ni}
add wave -noupdate -group {dut/mon[0]/ctrl_reg} {/tb_axi_perf_mon/dut/gen_mon[0]/i_ctrl_reg/paddr_i}
add wave -noupdate -group {dut/mon[0]/ctrl_reg} {/tb_axi_perf_mon/dut/gen_mon[0]/i_ctrl_reg/pprot_i}
add wave -noupdate -group {dut/mon[0]/ctrl_reg} {/tb_axi_perf_mon/dut/gen_mon[0]/i_ctrl_reg/psel_i}
add wave -noupdate -group {dut/mon[0]/ctrl_reg} {/tb_axi_perf_mon/dut/gen_mon[0]/i_ctrl_reg/penable_i}
add wave -noupdate -group {dut/mon[0]/ctrl_reg} {/tb_axi_perf_mon/dut/gen_mon[0]/i_ctrl_reg/pwrite_i}
add wave -noupdate -group {dut/mon[0]/ctrl_reg} {/tb_axi_perf_mon/dut/gen_mon[0]/i_ctrl_reg/pwdata_i}
add wave -noupdate -group {dut/mon[0]/ctrl_reg} {/tb_axi_perf_mon/dut/gen_mon[0]/i_ctrl_reg/pstrb_i}
add wave -noupdate -group {dut/mon[0]/ctrl_reg} {/tb_axi_perf_mon/dut/gen_mon[0]/i_ctrl_reg/pready_o}
add wave -noupdate -group {dut/mon[0]/ctrl_reg} {/tb_axi_perf_mon/dut/gen_mon[0]/i_ctrl_reg/prdata_o}
add wave -noupdate -group {dut/mon[0]/ctrl_reg} {/tb_axi_perf_mon/dut/gen_mon[0]/i_ctrl_reg/pslverr_o}
add wave -noupdate -group {dut/mon[0]/ctrl_reg} {/tb_axi_perf_mon/dut/gen_mon[0]/i_ctrl_reg/init_i}
add wave -noupdate -group {dut/mon[0]/ctrl_reg} {/tb_axi_perf_mon/dut/gen_mon[0]/i_ctrl_reg/q_o}
add wave -noupdate -group {dut/mon[0]/ctrl_reg} {/tb_axi_perf_mon/dut/gen_mon[0]/i_ctrl_reg/reg_d}
add wave -noupdate -group {dut/mon[0]/ctrl_reg} {/tb_axi_perf_mon/dut/gen_mon[0]/i_ctrl_reg/reg_q}
add wave -noupdate -expand -group {dut/mon[0]} -radix binary {/tb_axi_perf_mon/dut/gen_mon[0]/clr}
add wave -noupdate -expand -group {dut/mon[0]} -radix binary {/tb_axi_perf_mon/dut/gen_mon[0]/en}
add wave -noupdate -expand -group {dut/mon[0]} -radix unsigned {/tb_axi_perf_mon/dut/gen_mon[0]/cnt_clk}
add wave -noupdate -expand -group {dut/mon[0]} -radix binary {/tb_axi_perf_mon/dut/gen_mon[0]/cnt_clk_oflw}
add wave -noupdate -expand -group {dut/mon[0]} -radix unsigned {/tb_axi_perf_mon/dut/gen_mon[0]/hs_cnt_ar}
add wave -noupdate -expand -group {dut/mon[0]} -radix unsigned {/tb_axi_perf_mon/dut/gen_mon[0]/hs_cnt_aw}
add wave -noupdate -expand -group {dut/mon[0]} -radix binary {/tb_axi_perf_mon/dut/gen_mon[0]/hs_cnt_ar_oflw}
add wave -noupdate -expand -group {dut/mon[0]} -radix binary {/tb_axi_perf_mon/dut/gen_mon[0]/hs_cnt_aw_oflw}
add wave -noupdate -expand -group {dut/mon[0]} -radix unsigned {/tb_axi_perf_mon/dut/gen_mon[0]/hs_cnt_r}
add wave -noupdate -expand -group {dut/mon[0]} -radix unsigned {/tb_axi_perf_mon/dut/gen_mon[0]/hs_cnt_w}
add wave -noupdate -expand -group {dut/mon[0]} -radix binary {/tb_axi_perf_mon/dut/gen_mon[0]/hs_cnt_r_oflw}
add wave -noupdate -expand -group {dut/mon[0]} -radix binary {/tb_axi_perf_mon/dut/gen_mon[0]/hs_cnt_w_oflw}
add wave -noupdate -expand -group {dut/mon[0]} -radix unsigned -childformat {{{/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_max_r[9]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_max_r[8]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_max_r[7]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_max_r[6]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_max_r[5]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_max_r[4]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_max_r[3]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_max_r[2]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_max_r[1]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_max_r[0]} -radix decimal}} -subitemconfig {{/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_max_r[9]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_max_r[8]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_max_r[7]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_max_r[6]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_max_r[5]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_max_r[4]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_max_r[3]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_max_r[2]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_max_r[1]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_max_r[0]} {-height 16 -radix decimal}} {/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_max_r}
add wave -noupdate -expand -group {dut/mon[0]} -radix unsigned {/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_max_w}
add wave -noupdate -expand -group {dut/mon[0]} -radix binary {/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_max_r_oflw}
add wave -noupdate -expand -group {dut/mon[0]} -radix binary {/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_max_w_oflw}
add wave -noupdate -expand -group {dut/mon[0]} -radix unsigned {/tb_axi_perf_mon/dut/gen_mon[0]/gen_fl_txn/r_cnt}
add wave -noupdate -expand -group {dut/mon[0]} -radix binary {/tb_axi_perf_mon/dut/gen_mon[0]/gen_fl_txn/r_inc}
add wave -noupdate -expand -group {dut/mon[0]} -radix binary {/tb_axi_perf_mon/dut/gen_mon[0]/gen_fl_txn/r_dec}
add wave -noupdate -expand -group {dut/mon[0]} -radix unsigned -childformat {{{/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[62]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[61]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[60]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[59]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[58]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[57]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[56]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[55]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[54]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[53]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[52]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[51]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[50]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[49]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[48]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[47]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[46]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[45]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[44]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[43]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[42]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[41]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[40]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[39]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[38]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[37]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[36]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[35]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[34]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[33]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[32]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[31]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[30]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[29]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[28]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[27]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[26]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[25]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[24]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[23]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[22]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[21]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[20]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[19]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[18]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[17]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[16]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[15]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[14]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[13]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[12]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[11]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[10]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[9]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[8]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[7]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[6]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[5]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[4]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[3]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[2]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[1]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[0]} -radix decimal}} -subitemconfig {{/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[62]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[61]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[60]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[59]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[58]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[57]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[56]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[55]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[54]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[53]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[52]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[51]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[50]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[49]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[48]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[47]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[46]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[45]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[44]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[43]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[42]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[41]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[40]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[39]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[38]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[37]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[36]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[35]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[34]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[33]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[32]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[31]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[30]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[29]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[28]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[27]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[26]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[25]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[24]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[23]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[22]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[21]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[20]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[19]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[18]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[17]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[16]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[15]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[14]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[13]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[12]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[11]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[10]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[9]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[8]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[7]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[6]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[5]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[4]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[3]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[2]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[1]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r[0]} {-height 16 -radix decimal}} {/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r}
add wave -noupdate -expand -group {dut/mon[0]} -radix unsigned {/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_w}
add wave -noupdate -expand -group {dut/mon[0]} -radix unsigned {/tb_axi_perf_mon/dut/gen_mon[0]/gen_fl_txn/w_cnt}
add wave -noupdate -expand -group {dut/mon[0]} -radix binary {/tb_axi_perf_mon/dut/gen_mon[0]/gen_fl_txn/w_inc}
add wave -noupdate -expand -group {dut/mon[0]} -radix binary {/tb_axi_perf_mon/dut/gen_mon[0]/gen_fl_txn/w_dec}
add wave -noupdate -expand -group {dut/mon[0]} -radix binary {/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_r_oflw}
add wave -noupdate -expand -group {dut/mon[0]} -radix binary {/tb_axi_perf_mon/dut/gen_mon[0]/fl_txn_acc_w_oflw}
add wave -noupdate -expand -group {dut/mon[0]} -radix unsigned {/tb_axi_perf_mon/dut/gen_mon[0]/fl_dat_cnt_r}
add wave -noupdate -expand -group {dut/mon[0]} -radix unsigned {/tb_axi_perf_mon/dut/gen_mon[0]/fl_dat_cnt_w}
add wave -noupdate -expand -group {dut/mon[0]} -radix unsigned {/tb_axi_perf_mon/dut/gen_mon[0]/fl_dat_max_r}
add wave -noupdate -expand -group {dut/mon[0]} -radix unsigned {/tb_axi_perf_mon/dut/gen_mon[0]/fl_dat_max_w}
add wave -noupdate -expand -group {dut/mon[0]} -radix binary {/tb_axi_perf_mon/dut/gen_mon[0]/fl_dat_cnt_r_oflw}
add wave -noupdate -expand -group {dut/mon[0]} -radix binary {/tb_axi_perf_mon/dut/gen_mon[0]/fl_dat_cnt_w_oflw}
add wave -noupdate -expand -group {dut/mon[0]} -radix binary {/tb_axi_perf_mon/dut/gen_mon[0]/fl_dat_max_r_oflw}
add wave -noupdate -expand -group {dut/mon[0]} -radix binary {/tb_axi_perf_mon/dut/gen_mon[0]/fl_dat_max_w_oflw}
add wave -noupdate -expand -group {dut/mon[0]} -radix unsigned {/tb_axi_perf_mon/dut/gen_mon[0]/fl_dat_acc_r}
add wave -noupdate -expand -group {dut/mon[0]} -radix unsigned {/tb_axi_perf_mon/dut/gen_mon[0]/fl_dat_acc_w}
add wave -noupdate -expand -group {dut/mon[0]} -radix binary {/tb_axi_perf_mon/dut/gen_mon[0]/fl_dat_acc_r_oflw}
add wave -noupdate -expand -group {dut/mon[0]} -radix binary {/tb_axi_perf_mon/dut/gen_mon[0]/fl_dat_acc_w_oflw}
add wave -noupdate -expand -group {dut/mon[0]} -radix unsigned {/tb_axi_perf_mon/dut/gen_mon[0]/tx_dat_cnt_r}
add wave -noupdate -expand -group {dut/mon[0]} -radix unsigned {/tb_axi_perf_mon/dut/gen_mon[0]/tx_dat_cnt_w}
add wave -noupdate -expand -group {dut/mon[0]} -radix binary {/tb_axi_perf_mon/dut/gen_mon[0]/tx_dat_cnt_r_oflw}
add wave -noupdate -expand -group {dut/mon[0]} -radix binary {/tb_axi_perf_mon/dut/gen_mon[0]/tx_dat_cnt_w_oflw}
add wave -noupdate -expand -group {dut/mon[0]} -radix unsigned {/tb_axi_perf_mon/dut/gen_mon[0]/stall_max_ar}
add wave -noupdate -expand -group {dut/mon[0]} -radix unsigned {/tb_axi_perf_mon/dut/gen_mon[0]/stall_max_aw}
add wave -noupdate -expand -group {dut/mon[0]} -radix unsigned {/tb_axi_perf_mon/dut/gen_mon[0]/stall_max_r}
add wave -noupdate -expand -group {dut/mon[0]} -radix unsigned {/tb_axi_perf_mon/dut/gen_mon[0]/stall_max_w}
add wave -noupdate -expand -group {dut/mon[0]} -radix unsigned {/tb_axi_perf_mon/dut/gen_mon[0]/stall_max_b}
add wave -noupdate -expand -group {dut/mon[0]} -radix binary {/tb_axi_perf_mon/dut/gen_mon[0]/stall_max_ar_oflw}
add wave -noupdate -expand -group {dut/mon[0]} -radix binary {/tb_axi_perf_mon/dut/gen_mon[0]/stall_max_aw_oflw}
add wave -noupdate -expand -group {dut/mon[0]} -radix binary {/tb_axi_perf_mon/dut/gen_mon[0]/stall_max_r_oflw}
add wave -noupdate -expand -group {dut/mon[0]} -radix binary {/tb_axi_perf_mon/dut/gen_mon[0]/stall_max_w_oflw}
add wave -noupdate -expand -group {dut/mon[0]} -radix binary {/tb_axi_perf_mon/dut/gen_mon[0]/stall_max_b_oflw}
add wave -noupdate -expand -group {dut/mon[0]} -radix unsigned {/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_ar}
add wave -noupdate -expand -group {dut/mon[0]} -radix unsigned {/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_aw}
add wave -noupdate -expand -group {dut/mon[0]} -radix unsigned {/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_b}
add wave -noupdate -expand -group {dut/mon[0]} -radix binary {/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_ar_oflw}
add wave -noupdate -expand -group {dut/mon[0]} -radix binary {/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_aw_oflw}
add wave -noupdate -expand -group {dut/mon[0]} -radix binary {/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_b_oflw}
add wave -noupdate -expand -group {dut/mon[0]} -radix unsigned -childformat {{{/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_r[55]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_r[54]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_r[53]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_r[52]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_r[51]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_r[50]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_r[49]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_r[48]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_r[47]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_r[46]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_r[45]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_r[44]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_r[43]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_r[42]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_r[41]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_r[40]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_r[39]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_r[38]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_r[37]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_r[36]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_r[35]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_r[34]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_r[33]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_r[32]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_r[31]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_r[30]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_r[29]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_r[28]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_r[27]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_r[26]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_r[25]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_r[24]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_r[23]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_r[22]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_r[21]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_r[20]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_r[19]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_r[18]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_r[17]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_r[16]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_r[15]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_r[14]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_r[13]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_r[12]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_r[11]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_r[10]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_r[9]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_r[8]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_r[7]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_r[6]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_r[5]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_r[4]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_r[3]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_r[2]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_r[1]} -radix decimal} {{/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_r[0]} -radix decimal}} -subitemconfig {{/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_r[55]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_r[54]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_r[53]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_r[52]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_r[51]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_r[50]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_r[49]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_r[48]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_r[47]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_r[46]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_r[45]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_r[44]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_r[43]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_r[42]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_r[41]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_r[40]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_r[39]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_r[38]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_r[37]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_r[36]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_r[35]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_r[34]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_r[33]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_r[32]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_r[31]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_r[30]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_r[29]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_r[28]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_r[27]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_r[26]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_r[25]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_r[24]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_r[23]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_r[22]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_r[21]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_r[20]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_r[19]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_r[18]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_r[17]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_r[16]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_r[15]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_r[14]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_r[13]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_r[12]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_r[11]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_r[10]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_r[9]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_r[8]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_r[7]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_r[6]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_r[5]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_r[4]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_r[3]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_r[2]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_r[1]} {-height 16 -radix decimal} {/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_r[0]} {-height 16 -radix decimal}} {/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_r}
add wave -noupdate -expand -group {dut/mon[0]} -radix unsigned {/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_w}
add wave -noupdate -expand -group {dut/mon[0]} -radix binary {/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_r_oflw}
add wave -noupdate -expand -group {dut/mon[0]} -radix binary {/tb_axi_perf_mon/dut/gen_mon[0]/stall_cnt_w_oflw}
add wave -noupdate -expand -group {dut/mon[0]} -radix unsigned {/tb_axi_perf_mon/dut/gen_mon[0]/excl_cnt_ar}
add wave -noupdate -expand -group {dut/mon[0]} -radix unsigned {/tb_axi_perf_mon/dut/gen_mon[0]/excl_cnt_aw}
add wave -noupdate -expand -group {dut/mon[0]} -radix unsigned {/tb_axi_perf_mon/dut/gen_mon[0]/excl_cnt_b}
add wave -noupdate -expand -group {dut/mon[0]} -radix binary {/tb_axi_perf_mon/dut/gen_mon[0]/excl_cnt_ar_oflw}
add wave -noupdate -expand -group {dut/mon[0]} -radix binary {/tb_axi_perf_mon/dut/gen_mon[0]/excl_cnt_aw_oflw}
add wave -noupdate -expand -group {dut/mon[0]} -radix binary {/tb_axi_perf_mon/dut/gen_mon[0]/excl_cnt_b_oflw}
add wave -noupdate -expand -group {dut/mon[0]} -radix unsigned {/tb_axi_perf_mon/dut/gen_mon[0]/atop_cnt_st}
add wave -noupdate -expand -group {dut/mon[0]} -radix unsigned {/tb_axi_perf_mon/dut/gen_mon[0]/atop_cnt_ld}
add wave -noupdate -expand -group {dut/mon[0]} -radix unsigned {/tb_axi_perf_mon/dut/gen_mon[0]/atop_cnt_swp}
add wave -noupdate -expand -group {dut/mon[0]} -radix unsigned {/tb_axi_perf_mon/dut/gen_mon[0]/atop_cnt_cmp}
add wave -noupdate -expand -group {dut/mon[0]} -radix binary {/tb_axi_perf_mon/dut/gen_mon[0]/atop_cnt_st_oflw}
add wave -noupdate -expand -group {dut/mon[0]} -radix binary {/tb_axi_perf_mon/dut/gen_mon[0]/atop_cnt_ld_oflw}
add wave -noupdate -expand -group {dut/mon[0]} -radix binary {/tb_axi_perf_mon/dut/gen_mon[0]/atop_cnt_swp_oflw}
add wave -noupdate -expand -group {dut/mon[0]} -radix binary {/tb_axi_perf_mon/dut/gen_mon[0]/atop_cnt_cmp_oflw}
add wave -noupdate -expand -group {dut/mon[0]} -radix binary {/tb_axi_perf_mon/dut/gen_mon[0]/cap_reg}
add wave -noupdate -expand -group {dut/mon[0]} {/tb_axi_perf_mon/dut/gen_mon[0]/oup_reg}
add wave -noupdate -group {dut/axi[1]} {/tb_axi_perf_mon/dut/clk_axi_i[1]}
add wave -noupdate -group {dut/axi[1]} {/tb_axi_perf_mon/dut/rst_axi_ni[1]}
add wave -noupdate -group {dut/axi[1]} {/tb_axi_perf_mon/dut/ar_id_i[1]}
add wave -noupdate -group {dut/axi[1]} {/tb_axi_perf_mon/dut/ar_len_i[1]}
add wave -noupdate -group {dut/axi[1]} {/tb_axi_perf_mon/dut/ar_size_i[1]}
add wave -noupdate -group {dut/axi[1]} {/tb_axi_perf_mon/dut/ar_lock_i[1]}
add wave -noupdate -group {dut/axi[1]} {/tb_axi_perf_mon/dut/ar_valid_i[1]}
add wave -noupdate -group {dut/axi[1]} {/tb_axi_perf_mon/dut/ar_ready_i[1]}
add wave -noupdate -group {dut/axi[1]} {/tb_axi_perf_mon/dut/aw_id_i[1]}
add wave -noupdate -group {dut/axi[1]} {/tb_axi_perf_mon/dut/aw_len_i[1]}
add wave -noupdate -group {dut/axi[1]} {/tb_axi_perf_mon/dut/aw_size_i[1]}
add wave -noupdate -group {dut/axi[1]} {/tb_axi_perf_mon/dut/aw_lock_i[1]}
add wave -noupdate -group {dut/axi[1]} {/tb_axi_perf_mon/dut/aw_atop_i[1]}
add wave -noupdate -group {dut/axi[1]} {/tb_axi_perf_mon/dut/aw_valid_i[1]}
add wave -noupdate -group {dut/axi[1]} {/tb_axi_perf_mon/dut/aw_ready_i[1]}
add wave -noupdate -group {dut/axi[1]} {/tb_axi_perf_mon/dut/r_id_i[1]}
add wave -noupdate -group {dut/axi[1]} {/tb_axi_perf_mon/dut/r_last_i[1]}
add wave -noupdate -group {dut/axi[1]} {/tb_axi_perf_mon/dut/r_valid_i[1]}
add wave -noupdate -group {dut/axi[1]} {/tb_axi_perf_mon/dut/r_ready_i[1]}
add wave -noupdate -group {dut/axi[1]} {/tb_axi_perf_mon/dut/w_last_i[1]}
add wave -noupdate -group {dut/axi[1]} {/tb_axi_perf_mon/dut/w_valid_i[1]}
add wave -noupdate -group {dut/axi[1]} {/tb_axi_perf_mon/dut/w_ready_i[1]}
add wave -noupdate -group {dut/axi[1]} {/tb_axi_perf_mon/dut/b_id_i[1]}
add wave -noupdate -group {dut/axi[1]} {/tb_axi_perf_mon/dut/b_resp_i[1]}
add wave -noupdate -group {dut/axi[1]} {/tb_axi_perf_mon/dut/b_valid_i[1]}
add wave -noupdate -group {dut/axi[1]} {/tb_axi_perf_mon/dut/b_ready_i[1]}
add wave -noupdate -group {dut/mon[1]} {/tb_axi_perf_mon/dut/gen_mon[1]/clr}
add wave -noupdate -group {dut/mon[1]} {/tb_axi_perf_mon/dut/gen_mon[1]/en}
add wave -noupdate -group {dut/mon[1]} {/tb_axi_perf_mon/dut/gen_mon[1]/cnt_clk}
add wave -noupdate -group {dut/mon[1]} {/tb_axi_perf_mon/dut/gen_mon[1]/cnt_clk_oflw}
add wave -noupdate -group {dut/mon[1]} {/tb_axi_perf_mon/dut/gen_mon[1]/hs_cnt_ar}
add wave -noupdate -group {dut/mon[1]} {/tb_axi_perf_mon/dut/gen_mon[1]/hs_cnt_aw}
add wave -noupdate -group {dut/mon[1]} {/tb_axi_perf_mon/dut/gen_mon[1]/hs_cnt_ar_oflw}
add wave -noupdate -group {dut/mon[1]} {/tb_axi_perf_mon/dut/gen_mon[1]/hs_cnt_aw_oflw}
add wave -noupdate -group {dut/mon[1]} {/tb_axi_perf_mon/dut/gen_mon[1]/hs_cnt_r}
add wave -noupdate -group {dut/mon[1]} {/tb_axi_perf_mon/dut/gen_mon[1]/hs_cnt_w}
add wave -noupdate -group {dut/mon[1]} {/tb_axi_perf_mon/dut/gen_mon[1]/hs_cnt_r_oflw}
add wave -noupdate -group {dut/mon[1]} {/tb_axi_perf_mon/dut/gen_mon[1]/hs_cnt_w_oflw}
add wave -noupdate -group {dut/mon[1]} {/tb_axi_perf_mon/dut/gen_mon[1]/fl_txn_max_r}
add wave -noupdate -group {dut/mon[1]} {/tb_axi_perf_mon/dut/gen_mon[1]/fl_txn_max_w}
add wave -noupdate -group {dut/mon[1]} {/tb_axi_perf_mon/dut/gen_mon[1]/fl_txn_max_r_oflw}
add wave -noupdate -group {dut/mon[1]} {/tb_axi_perf_mon/dut/gen_mon[1]/fl_txn_max_w_oflw}
add wave -noupdate -group {dut/mon[1]} {/tb_axi_perf_mon/dut/gen_mon[1]/fl_txn_acc_r}
add wave -noupdate -group {dut/mon[1]} {/tb_axi_perf_mon/dut/gen_mon[1]/fl_txn_acc_w}
add wave -noupdate -group {dut/mon[1]} {/tb_axi_perf_mon/dut/gen_mon[1]/fl_txn_acc_r_oflw}
add wave -noupdate -group {dut/mon[1]} {/tb_axi_perf_mon/dut/gen_mon[1]/fl_txn_acc_w_oflw}
add wave -noupdate -group {dut/mon[1]} {/tb_axi_perf_mon/dut/gen_mon[1]/fl_dat_cnt_r}
add wave -noupdate -group {dut/mon[1]} {/tb_axi_perf_mon/dut/gen_mon[1]/fl_dat_cnt_w}
add wave -noupdate -group {dut/mon[1]} {/tb_axi_perf_mon/dut/gen_mon[1]/fl_dat_max_r}
add wave -noupdate -group {dut/mon[1]} {/tb_axi_perf_mon/dut/gen_mon[1]/fl_dat_max_w}
add wave -noupdate -group {dut/mon[1]} {/tb_axi_perf_mon/dut/gen_mon[1]/fl_dat_cnt_r_oflw}
add wave -noupdate -group {dut/mon[1]} {/tb_axi_perf_mon/dut/gen_mon[1]/fl_dat_cnt_w_oflw}
add wave -noupdate -group {dut/mon[1]} {/tb_axi_perf_mon/dut/gen_mon[1]/fl_dat_max_r_oflw}
add wave -noupdate -group {dut/mon[1]} {/tb_axi_perf_mon/dut/gen_mon[1]/fl_dat_max_w_oflw}
add wave -noupdate -group {dut/mon[1]} {/tb_axi_perf_mon/dut/gen_mon[1]/fl_dat_acc_r}
add wave -noupdate -group {dut/mon[1]} {/tb_axi_perf_mon/dut/gen_mon[1]/fl_dat_acc_w}
add wave -noupdate -group {dut/mon[1]} {/tb_axi_perf_mon/dut/gen_mon[1]/fl_dat_acc_r_oflw}
add wave -noupdate -group {dut/mon[1]} {/tb_axi_perf_mon/dut/gen_mon[1]/fl_dat_acc_w_oflw}
add wave -noupdate -group {dut/mon[1]} {/tb_axi_perf_mon/dut/gen_mon[1]/tx_dat_cnt_r}
add wave -noupdate -group {dut/mon[1]} {/tb_axi_perf_mon/dut/gen_mon[1]/tx_dat_cnt_w}
add wave -noupdate -group {dut/mon[1]} {/tb_axi_perf_mon/dut/gen_mon[1]/tx_dat_cnt_r_oflw}
add wave -noupdate -group {dut/mon[1]} {/tb_axi_perf_mon/dut/gen_mon[1]/tx_dat_cnt_w_oflw}
add wave -noupdate -group {dut/mon[1]} {/tb_axi_perf_mon/dut/gen_mon[1]/stall_max_ar}
add wave -noupdate -group {dut/mon[1]} {/tb_axi_perf_mon/dut/gen_mon[1]/stall_max_aw}
add wave -noupdate -group {dut/mon[1]} {/tb_axi_perf_mon/dut/gen_mon[1]/stall_max_r}
add wave -noupdate -group {dut/mon[1]} {/tb_axi_perf_mon/dut/gen_mon[1]/stall_max_w}
add wave -noupdate -group {dut/mon[1]} {/tb_axi_perf_mon/dut/gen_mon[1]/stall_max_b}
add wave -noupdate -group {dut/mon[1]} {/tb_axi_perf_mon/dut/gen_mon[1]/stall_max_ar_oflw}
add wave -noupdate -group {dut/mon[1]} {/tb_axi_perf_mon/dut/gen_mon[1]/stall_max_aw_oflw}
add wave -noupdate -group {dut/mon[1]} {/tb_axi_perf_mon/dut/gen_mon[1]/stall_max_r_oflw}
add wave -noupdate -group {dut/mon[1]} {/tb_axi_perf_mon/dut/gen_mon[1]/stall_max_w_oflw}
add wave -noupdate -group {dut/mon[1]} {/tb_axi_perf_mon/dut/gen_mon[1]/stall_max_b_oflw}
add wave -noupdate -group {dut/mon[1]} {/tb_axi_perf_mon/dut/gen_mon[1]/stall_cnt_ar}
add wave -noupdate -group {dut/mon[1]} {/tb_axi_perf_mon/dut/gen_mon[1]/stall_cnt_aw}
add wave -noupdate -group {dut/mon[1]} {/tb_axi_perf_mon/dut/gen_mon[1]/stall_cnt_b}
add wave -noupdate -group {dut/mon[1]} {/tb_axi_perf_mon/dut/gen_mon[1]/stall_cnt_ar_oflw}
add wave -noupdate -group {dut/mon[1]} {/tb_axi_perf_mon/dut/gen_mon[1]/stall_cnt_aw_oflw}
add wave -noupdate -group {dut/mon[1]} {/tb_axi_perf_mon/dut/gen_mon[1]/stall_cnt_b_oflw}
add wave -noupdate -group {dut/mon[1]} {/tb_axi_perf_mon/dut/gen_mon[1]/stall_cnt_r}
add wave -noupdate -group {dut/mon[1]} {/tb_axi_perf_mon/dut/gen_mon[1]/stall_cnt_w}
add wave -noupdate -group {dut/mon[1]} {/tb_axi_perf_mon/dut/gen_mon[1]/stall_cnt_r_oflw}
add wave -noupdate -group {dut/mon[1]} {/tb_axi_perf_mon/dut/gen_mon[1]/stall_cnt_w_oflw}
add wave -noupdate -group {dut/mon[1]} {/tb_axi_perf_mon/dut/gen_mon[1]/excl_cnt_ar}
add wave -noupdate -group {dut/mon[1]} {/tb_axi_perf_mon/dut/gen_mon[1]/excl_cnt_aw}
add wave -noupdate -group {dut/mon[1]} {/tb_axi_perf_mon/dut/gen_mon[1]/excl_cnt_b}
add wave -noupdate -group {dut/mon[1]} {/tb_axi_perf_mon/dut/gen_mon[1]/excl_cnt_ar_oflw}
add wave -noupdate -group {dut/mon[1]} {/tb_axi_perf_mon/dut/gen_mon[1]/excl_cnt_aw_oflw}
add wave -noupdate -group {dut/mon[1]} {/tb_axi_perf_mon/dut/gen_mon[1]/excl_cnt_b_oflw}
add wave -noupdate -group {dut/mon[1]} {/tb_axi_perf_mon/dut/gen_mon[1]/atop_cnt_st}
add wave -noupdate -group {dut/mon[1]} {/tb_axi_perf_mon/dut/gen_mon[1]/atop_cnt_ld}
add wave -noupdate -group {dut/mon[1]} {/tb_axi_perf_mon/dut/gen_mon[1]/atop_cnt_swp}
add wave -noupdate -group {dut/mon[1]} {/tb_axi_perf_mon/dut/gen_mon[1]/atop_cnt_cmp}
add wave -noupdate -group {dut/mon[1]} {/tb_axi_perf_mon/dut/gen_mon[1]/atop_cnt_st_oflw}
add wave -noupdate -group {dut/mon[1]} {/tb_axi_perf_mon/dut/gen_mon[1]/atop_cnt_ld_oflw}
add wave -noupdate -group {dut/mon[1]} {/tb_axi_perf_mon/dut/gen_mon[1]/atop_cnt_swp_oflw}
add wave -noupdate -group {dut/mon[1]} {/tb_axi_perf_mon/dut/gen_mon[1]/atop_cnt_cmp_oflw}
add wave -noupdate -group {dut/mon[1]} {/tb_axi_perf_mon/dut/gen_mon[1]/cap_reg}
add wave -noupdate -group {dut/mon[1]} {/tb_axi_perf_mon/dut/gen_mon[1]/oup_reg}
add wave -noupdate -radix binary {/tb_axi_perf_mon/dut/gen_mon[0]/gen_fl_txn/fl_atop_b_q}
add wave -noupdate -radix binary {/tb_axi_perf_mon/dut/gen_mon[0]/gen_fl_txn/fl_atop_r_q}
TreeUpdate [SetDefaultTree]
configure wave -namecolwidth 228
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
