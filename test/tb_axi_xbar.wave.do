log -r *
onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate /tb_axi_xbar/i_xbar_dut/clk_i
add wave -noupdate /tb_axi_xbar/i_xbar_dut/rst_ni
add wave -noupdate /tb_axi_xbar/i_xbar_dut/test_i
add wave -noupdate -expand -subitemconfig {{/tb_axi_xbar/i_xbar_dut/slv_ports_req_i[5]} -expand {/tb_axi_xbar/i_xbar_dut/slv_ports_req_i[4]} -expand {/tb_axi_xbar/i_xbar_dut/slv_ports_req_i[3]} -expand {/tb_axi_xbar/i_xbar_dut/slv_ports_req_i[2]} -expand {/tb_axi_xbar/i_xbar_dut/slv_ports_req_i[1]} -expand {/tb_axi_xbar/i_xbar_dut/slv_ports_req_i[0]} -expand} /tb_axi_xbar/i_xbar_dut/slv_ports_req_i
add wave -noupdate -expand -subitemconfig {{/tb_axi_xbar/i_xbar_dut/slv_ports_resp_o[4]} -expand} /tb_axi_xbar/i_xbar_dut/slv_ports_resp_o
add wave -noupdate -subitemconfig {{/tb_axi_xbar/i_xbar_dut/mst_ports_req_o[6]} -expand} /tb_axi_xbar/i_xbar_dut/mst_ports_req_o
add wave -noupdate -expand -subitemconfig {{/tb_axi_xbar/i_xbar_dut/mst_ports_resp_i[3]} -expand} /tb_axi_xbar/i_xbar_dut/mst_ports_resp_i
add wave -noupdate /tb_axi_xbar/i_xbar_dut/addr_map_i
add wave -noupdate /tb_axi_xbar/i_xbar_dut/en_default_mst_port_i
add wave -noupdate /tb_axi_xbar/i_xbar_dut/default_mst_port_i
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {69999122 ns} 0}
quietly wave cursor active 1
configure wave -namecolwidth 303
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
WaveRestoreZoom {25059972 ns} {72366580 ns}
