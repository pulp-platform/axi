#!/bin/bash
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

set -e
ROOT=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)

[ ! -z "$VLOG" ] || VLOG=vlog
[ ! -z "$VOPT" ] || VOPT=vopt

$VLOG -sv \
	"$ROOT"/src/axi_pkg.sv \
	"$ROOT"/src/axi_intf.sv \
	"$ROOT"/src/axi_fifo.sv \
	"$ROOT"/src/axi_to_axi_lite.sv \
	"$ROOT"/src/axi_lite_to_axi.sv \
	"$ROOT"/src/axi_lite_xbar.sv \
	"$ROOT"/src/axi_arbiter.sv \
	"$ROOT"/src/axi_address_resolver.sv \
	"$ROOT"/src/axi_find_first_one.sv \
	"$ROOT"/test/tb_axi_lite_to_axi.sv \
	"$ROOT"/test/tb_axi_to_axi_lite.sv \
	"$ROOT"/test/tb_axi_lite_xbar.sv \
	"$ROOT"/test/synth_bench.sv

VOPTFLAGS="+cover=bcfst+/dut"

for top in tb_axi_lite_to_axi tb_axi_to_axi_lite synth_bench; do
	$VOPT $VOPT_FLAGS ${top} -o ${top}_opt +acc -check_synthesis
done
