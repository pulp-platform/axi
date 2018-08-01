#!/bin/bash
# Copyright (c) 2014-2018 ETH Zurich, University of Bologna
#
# Copyright and related rights are licensed under the Solderpad Hardware
# License, Version 0.51 (the "License"); you may not use this file except in
# compliance with the License.  You may obtain a copy of the License at
# http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
# or agreed to in writing, software, hardware and materials distributed under
# this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
# CONDITIONS OF ANY KIND, either express or implied. See the License for the
# specific language governing permissions and limitations under the License.
#
# Fabian Schuiki <fschuiki@iis.ee.ethz.ch>

set -e
ROOT=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)

[ ! -z "$VLOG" ] || VLOG=vlog
[ ! -z "$VOPT" ] || VOPT=vopt

$VLOG -sv \
	"$ROOT"/src/axi_pkg.sv \
	"$ROOT"/src/axi_intf.sv \
	"$ROOT"/src/axi_to_axi_lite.sv \
	"$ROOT"/src/axi_lite_to_axi.sv \
	"$ROOT"/src/axi_lite_xbar.sv \
	"$ROOT"/src/axi_arbiter.sv \
	"$ROOT"/src/axi_address_resolver.sv \
	"$ROOT"/test/tb_axi_lite_to_axi.sv \
	"$ROOT"/test/tb_axi_to_axi_lite.sv \
	"$ROOT"/test/tb_axi_lite_xbar.sv \
	"$ROOT"/test/synth_bench.sv

VOPTFLAGS="+cover=bcfst+/dut"
