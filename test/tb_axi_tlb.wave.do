add wave -noupdate /tb_axi_tlb/i_dut/clk_i
add wave -noupdate /tb_axi_tlb/i_dut/rst_ni
add wave -noupdate -expand -group dut /tb_axi_tlb/i_dut/test_en_i
add wave -noupdate -expand -group dut -group {Slv Port AW} /tb_axi_tlb/i_dut/slv_req.aw
add wave -noupdate -expand -group dut -group {Slv Port AW} /tb_axi_tlb/i_dut/slv_req.aw_valid
add wave -noupdate -expand -group dut -group {Slv Port AW} /tb_axi_tlb/i_dut/slv_resp.aw_ready
add wave -noupdate -expand -group dut -group {Mst Port AW} /tb_axi_tlb/i_dut/mst_req.aw
add wave -noupdate -expand -group dut -group {Mst Port AW} /tb_axi_tlb/i_dut/mst_req.aw_valid
add wave -noupdate -expand -group dut -group {Mst Port AW} /tb_axi_tlb/i_dut/mst_resp.aw_ready
add wave -noupdate -expand -group dut -group {Slv Port W} /tb_axi_tlb/i_dut/slv_req.w
add wave -noupdate -expand -group dut -group {Slv Port W} /tb_axi_tlb/i_dut/slv_req.w_valid
add wave -noupdate -expand -group dut -group {Slv Port W} /tb_axi_tlb/i_dut/slv_resp.w_ready
add wave -noupdate -expand -group dut -group {Mst Port W} /tb_axi_tlb/i_dut/mst_req.w
add wave -noupdate -expand -group dut -group {Mst Port W} /tb_axi_tlb/i_dut/mst_req.w_valid
add wave -noupdate -expand -group dut -group {Mst Port W} /tb_axi_tlb/i_dut/mst_resp.w_ready
add wave -noupdate -expand -group dut -group {Mst Port B} /tb_axi_tlb/i_dut/mst_resp.b
add wave -noupdate -expand -group dut -group {Mst Port B} /tb_axi_tlb/i_dut/mst_resp.b.id
add wave -noupdate -expand -group dut -group {Mst Port B} /tb_axi_tlb/i_dut/mst_resp.b.resp
add wave -noupdate -expand -group dut -group {Mst Port B} /tb_axi_tlb/i_dut/mst_resp.b.user
add wave -noupdate -expand -group dut -group {Mst Port B} /tb_axi_tlb/i_dut/mst_resp.b_valid
add wave -noupdate -expand -group dut -group {Mst Port B} /tb_axi_tlb/i_dut/mst_req.b_ready
add wave -noupdate -expand -group dut -group {Slv Port B} /tb_axi_tlb/i_dut/slv_resp.b
add wave -noupdate -expand -group dut -group {Slv Port B} /tb_axi_tlb/i_dut/slv_resp.b_valid
add wave -noupdate -expand -group dut -group {Slv Port B} /tb_axi_tlb/i_dut/slv_req.b_ready
add wave -noupdate -expand -group dut -group {Slv Port AR} /tb_axi_tlb/i_dut/slv_req.ar
add wave -noupdate -expand -group dut -group {Slv Port AR} /tb_axi_tlb/i_dut/slv_req.ar_valid
add wave -noupdate -expand -group dut -group {Slv Port AR} /tb_axi_tlb/i_dut/slv_resp.ar_ready
add wave -noupdate -expand -group dut -group {Mst Port AR} /tb_axi_tlb/i_dut/mst_req.ar
add wave -noupdate -expand -group dut -group {Mst Port AR} /tb_axi_tlb/i_dut/mst_req.ar_valid
add wave -noupdate -expand -group dut -group {Mst Port AR} /tb_axi_tlb/i_dut/mst_resp.ar_ready
add wave -noupdate -expand -group dut -group {Mst Port R} /tb_axi_tlb/i_dut/mst_resp.r
add wave -noupdate -expand -group dut -group {Mst Port R} /tb_axi_tlb/i_dut/mst_resp.r_valid
add wave -noupdate -expand -group dut -group {Mst Port R} /tb_axi_tlb/i_dut/mst_req.r_ready
add wave -noupdate -expand -group dut -group {Slv Port R} /tb_axi_tlb/i_dut/slv_resp.r
add wave -noupdate -expand -group dut -group {Slv Port R} /tb_axi_tlb/i_dut/slv_resp.r_valid
add wave -noupdate -expand -group dut -group {Slv Port R} /tb_axi_tlb/i_dut/slv_req.r_ready
add wave -noupdate -expand -group dut -group {Cfg Port} /tb_axi_tlb/i_dut/cfg_req.aw
add wave -noupdate -expand -group dut -group {Cfg Port} /tb_axi_tlb/i_dut/cfg_req.aw_valid
add wave -noupdate -expand -group dut -group {Cfg Port} /tb_axi_tlb/i_dut/cfg_resp.aw_ready
add wave -noupdate -expand -group dut -group {Cfg Port} /tb_axi_tlb/i_dut/cfg_req.w
add wave -noupdate -expand -group dut -group {Cfg Port} /tb_axi_tlb/i_dut/cfg_req.w_valid
add wave -noupdate -expand -group dut -group {Cfg Port} /tb_axi_tlb/i_dut/cfg_resp.w_ready
add wave -noupdate -expand -group dut -group {Cfg Port} /tb_axi_tlb/i_dut/cfg_resp.b
add wave -noupdate -expand -group dut -group {Cfg Port} /tb_axi_tlb/i_dut/cfg_resp.b_valid
add wave -noupdate -expand -group dut -group {Cfg Port} /tb_axi_tlb/i_dut/cfg_req.b_ready
add wave -noupdate -expand -group dut -group {Cfg Port} /tb_axi_tlb/i_dut/cfg_req.ar
add wave -noupdate -expand -group dut -group {Cfg Port} /tb_axi_tlb/i_dut/cfg_req.ar_valid
add wave -noupdate -expand -group dut -group {Cfg Port} /tb_axi_tlb/i_dut/cfg_resp.ar_ready
add wave -noupdate -expand -group dut -group {Cfg Port} /tb_axi_tlb/i_dut/cfg_resp.r
add wave -noupdate -expand -group dut -group {Cfg Port} /tb_axi_tlb/i_dut/cfg_resp.r_valid
add wave -noupdate -expand -group dut -group {Cfg Port} /tb_axi_tlb/i_dut/cfg_req.r_ready
add wave -noupdate -group l1_tlb /tb_axi_tlb/i_dut/i_axi_tlb/i_l1_tlb/*
