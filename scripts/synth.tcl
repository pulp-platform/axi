# Copyright (c) 2018 ETH Zurich, University of Bologna
# All rights reserved.
#
# This code is under development and not yet released to the public.
# Until it is released, the code is under the copyright of ETH Zurich and
# the University of Bologna, and may contain confidential and/or unpublished
# work. Any reuse/redistribution is strictly forbidden without written
# permission from ETH Zurich.
#
# Fabian Schuiki <fschuiki@iis.ee.ethz.ch>

set ROOT [file normalize [file join [file dirname [info script]] ..]]

analyze -format sv [list \
	$ROOT/src/axi_pkg.sv \
	$ROOT/src/axi_intf.sv \
	$ROOT/src/axi_fifo.sv \
	$ROOT/src/axi_to_axi_lite.sv \
	$ROOT/src/axi_lite_to_axi.sv \
	$ROOT/test/synth_bench.sv \
]

remove_design -all
elaborate synth_bench
