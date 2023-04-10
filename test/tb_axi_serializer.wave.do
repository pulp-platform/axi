onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate /tb_axi_serializer/i_dut/i_axi_serializer/clk_i
add wave -noupdate /tb_axi_serializer/i_dut/i_axi_serializer/rst_ni
add wave -noupdate /tb_axi_serializer/i_dut/i_axi_serializer/sbr_req_i
add wave -noupdate /tb_axi_serializer/i_dut/i_axi_serializer/sbr_resp_o
add wave -noupdate /tb_axi_serializer/i_dut/i_axi_serializer/mgr_req_o
add wave -noupdate /tb_axi_serializer/i_dut/i_axi_serializer/mgr_resp_i
add wave -noupdate /tb_axi_serializer/i_dut/i_axi_serializer/rd_fifo_full
add wave -noupdate /tb_axi_serializer/i_dut/i_axi_serializer/rd_fifo_empty
add wave -noupdate /tb_axi_serializer/i_dut/i_axi_serializer/rd_fifo_push
add wave -noupdate /tb_axi_serializer/i_dut/i_axi_serializer/rd_fifo_pop
add wave -noupdate /tb_axi_serializer/i_dut/i_axi_serializer/wr_fifo_full
add wave -noupdate /tb_axi_serializer/i_dut/i_axi_serializer/wr_fifo_empty
add wave -noupdate /tb_axi_serializer/i_dut/i_axi_serializer/wr_fifo_push
add wave -noupdate /tb_axi_serializer/i_dut/i_axi_serializer/wr_fifo_pop
add wave -noupdate /tb_axi_serializer/i_dut/i_axi_serializer/b_id
add wave -noupdate /tb_axi_serializer/i_dut/i_axi_serializer/r_id
add wave -noupdate /tb_axi_serializer/i_dut/i_axi_serializer/state_q
add wave -noupdate /tb_axi_serializer/i_dut/i_axi_serializer/state_d
add wave -noupdate /tb_axi_serializer/end_of_sim
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {0 ns} 0}
quietly wave cursor active 1
configure wave -namecolwidth 279
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
WaveRestoreZoom {0 ns} {112225215 ns}
