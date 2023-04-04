# This script was generated automatically by bender.
set ROOT "/home/jvikram/crosspoint/axi"

if {[catch {vlog -incr -sv \
    -svinputport=compat \
    -override_timescale 1ns/1ps \
    -suppress 2583 \
    +define+TARGET_SIMULATION \
    +define+TARGET_TEST \
    +define+TARGET_VSIM \
    "+incdir+$ROOT/.bender/git/checkouts/common_cells-ecf39c06fbbac60d/include" \
    "+incdir+$ROOT/include" \
    "$ROOT/.bender/git/checkouts/common_verification-9891eaba585d537d/src/clk_rst_gen.sv" \
    "$ROOT/.bender/git/checkouts/common_verification-9891eaba585d537d/src/rand_id_queue.sv" \
    "$ROOT/.bender/git/checkouts/common_verification-9891eaba585d537d/src/rand_stream_mst.sv" \
    "$ROOT/.bender/git/checkouts/common_verification-9891eaba585d537d/src/rand_synch_holdable_driver.sv" \
    "$ROOT/.bender/git/checkouts/common_verification-9891eaba585d537d/src/rand_verif_pkg.sv" \
    "$ROOT/.bender/git/checkouts/common_verification-9891eaba585d537d/src/sim_timeout.sv" \
    "$ROOT/.bender/git/checkouts/common_verification-9891eaba585d537d/src/rand_synch_driver.sv" \
    "$ROOT/.bender/git/checkouts/common_verification-9891eaba585d537d/src/rand_stream_slv.sv"
}]} {return 1}

if {[catch {vlog -incr -sv \
    -svinputport=compat \
    -override_timescale 1ns/1ps \
    -suppress 2583 \
    +define+TARGET_SIMULATION \
    +define+TARGET_TEST \
    +define+TARGET_VSIM \
    "+incdir+$ROOT/.bender/git/checkouts/common_cells-ecf39c06fbbac60d/include" \
    "+incdir+$ROOT/include" \
    "$ROOT/.bender/git/checkouts/common_verification-9891eaba585d537d/test/tb_clk_rst_gen.sv"
}]} {return 1}

if {[catch {vlog -incr -sv \
    -svinputport=compat \
    -override_timescale 1ns/1ps \
    -suppress 2583 \
    +define+TARGET_SIMULATION \
    +define+TARGET_TEST \
    +define+TARGET_VSIM \
    "+incdir+$ROOT/.bender/git/checkouts/common_cells-ecf39c06fbbac60d/include" \
    "+incdir+$ROOT/include" \
    "$ROOT/.bender/git/checkouts/tech_cells_generic-9dd79c3e4b5c8549/src/rtl/tc_sram.sv"
}]} {return 1}

if {[catch {vlog -incr -sv \
    -svinputport=compat \
    -override_timescale 1ns/1ps \
    -suppress 2583 \
    +define+TARGET_SIMULATION \
    +define+TARGET_TEST \
    +define+TARGET_VSIM \
    "+incdir+$ROOT/.bender/git/checkouts/common_cells-ecf39c06fbbac60d/include" \
    "+incdir+$ROOT/include" \
    "$ROOT/.bender/git/checkouts/tech_cells_generic-9dd79c3e4b5c8549/src/rtl/tc_clk.sv"
}]} {return 1}

if {[catch {vlog -incr -sv \
    -svinputport=compat \
    -override_timescale 1ns/1ps \
    -suppress 2583 \
    +define+TARGET_SIMULATION \
    +define+TARGET_TEST \
    +define+TARGET_VSIM \
    "+incdir+$ROOT/.bender/git/checkouts/common_cells-ecf39c06fbbac60d/include" \
    "+incdir+$ROOT/include" \
    "$ROOT/.bender/git/checkouts/tech_cells_generic-9dd79c3e4b5c8549/src/deprecated/cluster_pwr_cells.sv" \
    "$ROOT/.bender/git/checkouts/tech_cells_generic-9dd79c3e4b5c8549/src/deprecated/generic_memory.sv" \
    "$ROOT/.bender/git/checkouts/tech_cells_generic-9dd79c3e4b5c8549/src/deprecated/generic_rom.sv" \
    "$ROOT/.bender/git/checkouts/tech_cells_generic-9dd79c3e4b5c8549/src/deprecated/pad_functional.sv" \
    "$ROOT/.bender/git/checkouts/tech_cells_generic-9dd79c3e4b5c8549/src/deprecated/pulp_buffer.sv" \
    "$ROOT/.bender/git/checkouts/tech_cells_generic-9dd79c3e4b5c8549/src/deprecated/pulp_pwr_cells.sv"
}]} {return 1}

if {[catch {vlog -incr -sv \
    -svinputport=compat \
    -override_timescale 1ns/1ps \
    -suppress 2583 \
    +define+TARGET_SIMULATION \
    +define+TARGET_TEST \
    +define+TARGET_VSIM \
    "+incdir+$ROOT/.bender/git/checkouts/common_cells-ecf39c06fbbac60d/include" \
    "+incdir+$ROOT/include" \
    "$ROOT/.bender/git/checkouts/tech_cells_generic-9dd79c3e4b5c8549/src/tc_pwr.sv"
}]} {return 1}

if {[catch {vlog -incr -sv \
    -svinputport=compat \
    -override_timescale 1ns/1ps \
    -suppress 2583 \
    +define+TARGET_SIMULATION \
    +define+TARGET_TEST \
    +define+TARGET_VSIM \
    "+incdir+$ROOT/.bender/git/checkouts/common_cells-ecf39c06fbbac60d/include" \
    "+incdir+$ROOT/include" \
    "$ROOT/.bender/git/checkouts/tech_cells_generic-9dd79c3e4b5c8549/test/tb_tc_sram.sv"
}]} {return 1}

if {[catch {vlog -incr -sv \
    -svinputport=compat \
    -override_timescale 1ns/1ps \
    -suppress 2583 \
    +define+TARGET_SIMULATION \
    +define+TARGET_TEST \
    +define+TARGET_VSIM \
    "+incdir+$ROOT/.bender/git/checkouts/common_cells-ecf39c06fbbac60d/include" \
    "+incdir+$ROOT/include" \
    "$ROOT/.bender/git/checkouts/tech_cells_generic-9dd79c3e4b5c8549/src/deprecated/pulp_clock_gating_async.sv" \
    "$ROOT/.bender/git/checkouts/tech_cells_generic-9dd79c3e4b5c8549/src/deprecated/cluster_clk_cells.sv" \
    "$ROOT/.bender/git/checkouts/tech_cells_generic-9dd79c3e4b5c8549/src/deprecated/pulp_clk_cells.sv"
}]} {return 1}

if {[catch {vlog -incr -sv \
    -svinputport=compat \
    -override_timescale 1ns/1ps \
    -suppress 2583 \
    +define+TARGET_SIMULATION \
    +define+TARGET_TEST \
    +define+TARGET_VSIM \
    "+incdir+$ROOT/.bender/git/checkouts/common_cells-ecf39c06fbbac60d/include" \
    "+incdir+$ROOT/include" \
    "$ROOT/.bender/git/checkouts/common_cells-ecf39c06fbbac60d/src/binary_to_gray.sv" \
    "$ROOT/.bender/git/checkouts/common_cells-ecf39c06fbbac60d/src/cb_filter_pkg.sv" \
    "$ROOT/.bender/git/checkouts/common_cells-ecf39c06fbbac60d/src/cc_onehot.sv" \
    "$ROOT/.bender/git/checkouts/common_cells-ecf39c06fbbac60d/src/cf_math_pkg.sv" \
    "$ROOT/.bender/git/checkouts/common_cells-ecf39c06fbbac60d/src/clk_int_div.sv" \
    "$ROOT/.bender/git/checkouts/common_cells-ecf39c06fbbac60d/src/delta_counter.sv" \
    "$ROOT/.bender/git/checkouts/common_cells-ecf39c06fbbac60d/src/ecc_pkg.sv" \
    "$ROOT/.bender/git/checkouts/common_cells-ecf39c06fbbac60d/src/edge_propagator_tx.sv" \
    "$ROOT/.bender/git/checkouts/common_cells-ecf39c06fbbac60d/src/exp_backoff.sv" \
    "$ROOT/.bender/git/checkouts/common_cells-ecf39c06fbbac60d/src/fifo_v3.sv" \
    "$ROOT/.bender/git/checkouts/common_cells-ecf39c06fbbac60d/src/gray_to_binary.sv" \
    "$ROOT/.bender/git/checkouts/common_cells-ecf39c06fbbac60d/src/isochronous_4phase_handshake.sv" \
    "$ROOT/.bender/git/checkouts/common_cells-ecf39c06fbbac60d/src/isochronous_spill_register.sv" \
    "$ROOT/.bender/git/checkouts/common_cells-ecf39c06fbbac60d/src/lfsr.sv" \
    "$ROOT/.bender/git/checkouts/common_cells-ecf39c06fbbac60d/src/lfsr_16bit.sv" \
    "$ROOT/.bender/git/checkouts/common_cells-ecf39c06fbbac60d/src/lfsr_8bit.sv" \
    "$ROOT/.bender/git/checkouts/common_cells-ecf39c06fbbac60d/src/mv_filter.sv" \
    "$ROOT/.bender/git/checkouts/common_cells-ecf39c06fbbac60d/src/onehot_to_bin.sv" \
    "$ROOT/.bender/git/checkouts/common_cells-ecf39c06fbbac60d/src/plru_tree.sv" \
    "$ROOT/.bender/git/checkouts/common_cells-ecf39c06fbbac60d/src/popcount.sv" \
    "$ROOT/.bender/git/checkouts/common_cells-ecf39c06fbbac60d/src/rr_arb_tree.sv" \
    "$ROOT/.bender/git/checkouts/common_cells-ecf39c06fbbac60d/src/rstgen_bypass.sv" \
    "$ROOT/.bender/git/checkouts/common_cells-ecf39c06fbbac60d/src/serial_deglitch.sv" \
    "$ROOT/.bender/git/checkouts/common_cells-ecf39c06fbbac60d/src/shift_reg.sv" \
    "$ROOT/.bender/git/checkouts/common_cells-ecf39c06fbbac60d/src/spill_register_flushable.sv" \
    "$ROOT/.bender/git/checkouts/common_cells-ecf39c06fbbac60d/src/stream_demux.sv" \
    "$ROOT/.bender/git/checkouts/common_cells-ecf39c06fbbac60d/src/stream_filter.sv" \
    "$ROOT/.bender/git/checkouts/common_cells-ecf39c06fbbac60d/src/stream_fork.sv" \
    "$ROOT/.bender/git/checkouts/common_cells-ecf39c06fbbac60d/src/stream_intf.sv" \
    "$ROOT/.bender/git/checkouts/common_cells-ecf39c06fbbac60d/src/stream_join.sv" \
    "$ROOT/.bender/git/checkouts/common_cells-ecf39c06fbbac60d/src/stream_mux.sv" \
    "$ROOT/.bender/git/checkouts/common_cells-ecf39c06fbbac60d/src/sub_per_hash.sv" \
    "$ROOT/.bender/git/checkouts/common_cells-ecf39c06fbbac60d/src/sync.sv" \
    "$ROOT/.bender/git/checkouts/common_cells-ecf39c06fbbac60d/src/sync_wedge.sv" \
    "$ROOT/.bender/git/checkouts/common_cells-ecf39c06fbbac60d/src/unread.sv" \
    "$ROOT/.bender/git/checkouts/common_cells-ecf39c06fbbac60d/src/cdc_reset_ctrlr_pkg.sv" \
    "$ROOT/.bender/git/checkouts/common_cells-ecf39c06fbbac60d/src/cdc_2phase.sv" \
    "$ROOT/.bender/git/checkouts/common_cells-ecf39c06fbbac60d/src/cdc_4phase.sv" \
    "$ROOT/.bender/git/checkouts/common_cells-ecf39c06fbbac60d/src/addr_decode.sv" \
    "$ROOT/.bender/git/checkouts/common_cells-ecf39c06fbbac60d/src/cb_filter.sv" \
    "$ROOT/.bender/git/checkouts/common_cells-ecf39c06fbbac60d/src/cdc_fifo_2phase.sv" \
    "$ROOT/.bender/git/checkouts/common_cells-ecf39c06fbbac60d/src/counter.sv" \
    "$ROOT/.bender/git/checkouts/common_cells-ecf39c06fbbac60d/src/ecc_decode.sv" \
    "$ROOT/.bender/git/checkouts/common_cells-ecf39c06fbbac60d/src/ecc_encode.sv" \
    "$ROOT/.bender/git/checkouts/common_cells-ecf39c06fbbac60d/src/edge_detect.sv" \
    "$ROOT/.bender/git/checkouts/common_cells-ecf39c06fbbac60d/src/lzc.sv" \
    "$ROOT/.bender/git/checkouts/common_cells-ecf39c06fbbac60d/src/max_counter.sv" \
    "$ROOT/.bender/git/checkouts/common_cells-ecf39c06fbbac60d/src/rstgen.sv" \
    "$ROOT/.bender/git/checkouts/common_cells-ecf39c06fbbac60d/src/spill_register.sv" \
    "$ROOT/.bender/git/checkouts/common_cells-ecf39c06fbbac60d/src/stream_delay.sv" \
    "$ROOT/.bender/git/checkouts/common_cells-ecf39c06fbbac60d/src/stream_fifo.sv" \
    "$ROOT/.bender/git/checkouts/common_cells-ecf39c06fbbac60d/src/stream_fork_dynamic.sv" \
    "$ROOT/.bender/git/checkouts/common_cells-ecf39c06fbbac60d/src/cdc_reset_ctrlr.sv" \
    "$ROOT/.bender/git/checkouts/common_cells-ecf39c06fbbac60d/src/cdc_fifo_gray.sv" \
    "$ROOT/.bender/git/checkouts/common_cells-ecf39c06fbbac60d/src/fall_through_register.sv" \
    "$ROOT/.bender/git/checkouts/common_cells-ecf39c06fbbac60d/src/id_queue.sv" \
    "$ROOT/.bender/git/checkouts/common_cells-ecf39c06fbbac60d/src/stream_to_mem.sv" \
    "$ROOT/.bender/git/checkouts/common_cells-ecf39c06fbbac60d/src/stream_arbiter_flushable.sv" \
    "$ROOT/.bender/git/checkouts/common_cells-ecf39c06fbbac60d/src/stream_register.sv" \
    "$ROOT/.bender/git/checkouts/common_cells-ecf39c06fbbac60d/src/stream_xbar.sv" \
    "$ROOT/.bender/git/checkouts/common_cells-ecf39c06fbbac60d/src/cdc_fifo_gray_clearable.sv" \
    "$ROOT/.bender/git/checkouts/common_cells-ecf39c06fbbac60d/src/cdc_2phase_clearable.sv" \
    "$ROOT/.bender/git/checkouts/common_cells-ecf39c06fbbac60d/src/stream_arbiter.sv" \
    "$ROOT/.bender/git/checkouts/common_cells-ecf39c06fbbac60d/src/stream_omega_net.sv"
}]} {return 1}

if {[catch {vlog -incr -sv \
    -svinputport=compat \
    -override_timescale 1ns/1ps \
    -suppress 2583 \
    +define+TARGET_SIMULATION \
    +define+TARGET_TEST \
    +define+TARGET_VSIM \
    "+incdir+$ROOT/.bender/git/checkouts/common_cells-ecf39c06fbbac60d/include" \
    "+incdir+$ROOT/include" \
    "$ROOT/.bender/git/checkouts/common_cells-ecf39c06fbbac60d/src/deprecated/sram.sv"
}]} {return 1}

if {[catch {vlog -incr -sv \
    -svinputport=compat \
    -override_timescale 1ns/1ps \
    -suppress 2583 \
    +define+TARGET_SIMULATION \
    +define+TARGET_TEST \
    +define+TARGET_VSIM \
    "+incdir+$ROOT/.bender/git/checkouts/common_cells-ecf39c06fbbac60d/include" \
    "+incdir+$ROOT/include" \
    "$ROOT/.bender/git/checkouts/common_cells-ecf39c06fbbac60d/test/addr_decode_tb.sv" \
    "$ROOT/.bender/git/checkouts/common_cells-ecf39c06fbbac60d/test/cb_filter_tb.sv" \
    "$ROOT/.bender/git/checkouts/common_cells-ecf39c06fbbac60d/test/cdc_2phase_tb.sv" \
    "$ROOT/.bender/git/checkouts/common_cells-ecf39c06fbbac60d/test/cdc_2phase_clearable_tb.sv" \
    "$ROOT/.bender/git/checkouts/common_cells-ecf39c06fbbac60d/test/cdc_fifo_tb.sv" \
    "$ROOT/.bender/git/checkouts/common_cells-ecf39c06fbbac60d/test/cdc_fifo_clearable_tb.sv" \
    "$ROOT/.bender/git/checkouts/common_cells-ecf39c06fbbac60d/test/fifo_tb.sv" \
    "$ROOT/.bender/git/checkouts/common_cells-ecf39c06fbbac60d/test/graycode_tb.sv" \
    "$ROOT/.bender/git/checkouts/common_cells-ecf39c06fbbac60d/test/id_queue_tb.sv" \
    "$ROOT/.bender/git/checkouts/common_cells-ecf39c06fbbac60d/test/popcount_tb.sv" \
    "$ROOT/.bender/git/checkouts/common_cells-ecf39c06fbbac60d/test/rr_arb_tree_tb.sv" \
    "$ROOT/.bender/git/checkouts/common_cells-ecf39c06fbbac60d/test/stream_test.sv" \
    "$ROOT/.bender/git/checkouts/common_cells-ecf39c06fbbac60d/test/stream_register_tb.sv" \
    "$ROOT/.bender/git/checkouts/common_cells-ecf39c06fbbac60d/test/stream_to_mem_tb.sv" \
    "$ROOT/.bender/git/checkouts/common_cells-ecf39c06fbbac60d/test/sub_per_hash_tb.sv" \
    "$ROOT/.bender/git/checkouts/common_cells-ecf39c06fbbac60d/test/isochronous_crossing_tb.sv" \
    "$ROOT/.bender/git/checkouts/common_cells-ecf39c06fbbac60d/test/stream_omega_net_tb.sv" \
    "$ROOT/.bender/git/checkouts/common_cells-ecf39c06fbbac60d/test/stream_xbar_tb.sv" \
    "$ROOT/.bender/git/checkouts/common_cells-ecf39c06fbbac60d/test/clk_int_div_tb.sv"
}]} {return 1}

if {[catch {vlog -incr -sv \
    -svinputport=compat \
    -override_timescale 1ns/1ps \
    -suppress 2583 \
    +define+TARGET_SIMULATION \
    +define+TARGET_TEST \
    +define+TARGET_VSIM \
    "+incdir+$ROOT/.bender/git/checkouts/common_cells-ecf39c06fbbac60d/include" \
    "+incdir+$ROOT/include" \
    "$ROOT/.bender/git/checkouts/common_cells-ecf39c06fbbac60d/src/deprecated/clock_divider_counter.sv" \
    "$ROOT/.bender/git/checkouts/common_cells-ecf39c06fbbac60d/src/deprecated/clk_div.sv" \
    "$ROOT/.bender/git/checkouts/common_cells-ecf39c06fbbac60d/src/deprecated/find_first_one.sv" \
    "$ROOT/.bender/git/checkouts/common_cells-ecf39c06fbbac60d/src/deprecated/generic_LFSR_8bit.sv" \
    "$ROOT/.bender/git/checkouts/common_cells-ecf39c06fbbac60d/src/deprecated/generic_fifo.sv" \
    "$ROOT/.bender/git/checkouts/common_cells-ecf39c06fbbac60d/src/deprecated/prioarbiter.sv" \
    "$ROOT/.bender/git/checkouts/common_cells-ecf39c06fbbac60d/src/deprecated/pulp_sync.sv" \
    "$ROOT/.bender/git/checkouts/common_cells-ecf39c06fbbac60d/src/deprecated/pulp_sync_wedge.sv" \
    "$ROOT/.bender/git/checkouts/common_cells-ecf39c06fbbac60d/src/deprecated/rrarbiter.sv" \
    "$ROOT/.bender/git/checkouts/common_cells-ecf39c06fbbac60d/src/deprecated/clock_divider.sv" \
    "$ROOT/.bender/git/checkouts/common_cells-ecf39c06fbbac60d/src/deprecated/fifo_v2.sv" \
    "$ROOT/.bender/git/checkouts/common_cells-ecf39c06fbbac60d/src/deprecated/fifo_v1.sv" \
    "$ROOT/.bender/git/checkouts/common_cells-ecf39c06fbbac60d/src/edge_propagator_ack.sv" \
    "$ROOT/.bender/git/checkouts/common_cells-ecf39c06fbbac60d/src/edge_propagator.sv" \
    "$ROOT/.bender/git/checkouts/common_cells-ecf39c06fbbac60d/src/edge_propagator_rx.sv"
}]} {return 1}

if {[catch {vlog -incr -sv \
    -svinputport=compat \
    -override_timescale 1ns/1ps \
    -suppress 2583 \
    -lint -pedanticerrors \
    +define+TARGET_SIMULATION \
    +define+TARGET_TEST \
    +define+TARGET_VSIM \
    "+incdir+$ROOT/.bender/git/checkouts/common_cells-ecf39c06fbbac60d/include" \
    "+incdir+$ROOT/include" \
    "$ROOT/src/axi_pkg.sv" \
    "$ROOT/src/axi_intf.sv" \
    "$ROOT/src/axi_atop_filter.sv" \
    "$ROOT/src/axi_burst_splitter.sv" \
    "$ROOT/src/axi_cdc_dst.sv" \
    "$ROOT/src/axi_cdc_src.sv" \
    "$ROOT/src/axi_cut.sv" \
    "$ROOT/src/axi_delayer.sv" \
    "$ROOT/src/axi_demux.sv" \
    "$ROOT/src/axi_dw_downsizer.sv" \
    "$ROOT/src/axi_dw_upsizer.sv" \
    "$ROOT/src/axi_id_remap.sv" \
    "$ROOT/src/axi_id_prepend.sv" \
    "$ROOT/src/axi_isolate.sv" \
    "$ROOT/src/axi_join.sv" \
    "$ROOT/src/axi_lite_demux.sv" \
    "$ROOT/src/axi_lite_join.sv" \
    "$ROOT/src/axi_lite_mailbox.sv" \
    "$ROOT/src/axi_lite_mux.sv" \
    "$ROOT/src/axi_lite_regs.sv" \
    "$ROOT/src/axi_lite_to_apb.sv" \
    "$ROOT/src/axi_lite_to_axi.sv" \
    "$ROOT/src/axi_modify_address.sv" \
    "$ROOT/src/axi_mux.sv" \
    "$ROOT/src/axi_serializer.sv" \
    "$ROOT/src/axi_cdc.sv" \
    "$ROOT/src/axi_err_slv.sv" \
    "$ROOT/src/axi_dw_converter.sv" \
    "$ROOT/src/axi_id_serialize.sv" \
    "$ROOT/src/axi_multicut.sv" \
    "$ROOT/src/axi_to_axi_lite.sv" \
    "$ROOT/src/axi_iw_converter.sv" \
    "$ROOT/src/axi_lite_xbar.sv" \
    "$ROOT/src/axi_xbar.sv" \
    "$ROOT/src/axi_xp.sv" \
    "$ROOT/src/axi_dma_backend.sv" \
    "$ROOT/src/axi_dma_burst_reshaper.sv" \
    "$ROOT/src/axi_dma_data_mover.sv" \
    "$ROOT/src/axi_dma_data_path.sv" \
    "$ROOT/src/axi_aw_w_sync.sv"
}]} {return 1}

if {[catch {vlog -incr -sv \
    -svinputport=compat \
    -override_timescale 1ns/1ps \
    -suppress 2583 \
    +define+TARGET_SIMULATION \
    +define+TARGET_TEST \
    +define+TARGET_VSIM \
    "+incdir+$ROOT/.bender/git/checkouts/common_cells-ecf39c06fbbac60d/include" \
    "+incdir+$ROOT/include" \
    "$ROOT/src/axi_sim_mem.sv" \
    "$ROOT/src/axi_test.sv"
}]} {return 1}

if {[catch {vlog -incr -sv \
    -svinputport=compat \
    -override_timescale 1ns/1ps \
    -suppress 2583 \
    +define+TARGET_SIMULATION \
    +define+TARGET_TEST \
    +define+TARGET_VSIM \
    "+incdir+$ROOT/.bender/git/checkouts/common_cells-ecf39c06fbbac60d/include" \
    "+incdir+$ROOT/include" \
    "$ROOT/test/tb_axi_dw_pkg.sv" \
    "$ROOT/test/tb_axi_xbar_pkg.sv" \
    "$ROOT/test/tb_axi_xp_pkg.sv" \
    "$ROOT/test/tb_axi_addr_test.sv" \
    "$ROOT/test/tb_axi_atop_filter.sv" \
    "$ROOT/test/tb_axi_cdc.sv" \
    "$ROOT/test/tb_axi_delayer.sv" \
    "$ROOT/test/tb_axi_dw_downsizer.sv" \
    "$ROOT/test/tb_axi_dw_upsizer.sv" \
    "$ROOT/test/tb_axi_isolate.sv" \
    "$ROOT/test/tb_axi_lite_mailbox.sv" \
    "$ROOT/test/tb_axi_lite_regs.sv" \
    "$ROOT/test/tb_axi_iw_converter.sv" \
    "$ROOT/test/tb_axi_lite_to_apb.sv" \
    "$ROOT/test/tb_axi_lite_to_axi.sv" \
    "$ROOT/test/tb_axi_lite_xbar.sv" \
    "$ROOT/test/tb_axi_modify_address.sv" \
    "$ROOT/test/tb_axi_serializer.sv" \
    "$ROOT/test/tb_axi_sim_mem.sv" \
    "$ROOT/test/tb_axi_to_axi_lite.sv" \
    "$ROOT/test/tb_axi_xbar.sv" \
    "$ROOT/test/tb_axi_xp.sv" \
    "$ROOT/test/tb_axi_dma_backend.sv" \
    "$ROOT/test/fixture_axi_dma_backend.sv"
}]} {return 1}
return 0
