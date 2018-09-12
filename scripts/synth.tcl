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

set ROOT [file normalize [file join [file dirname [info script]] ..]]

analyze -format sv [list \
	$ROOT/src/axi_pkg.sv \
	$ROOT/src/axi_intf.sv \
	$ROOT/src/axi_fifo.sv \
	$ROOT/src/axi_to_axi_lite.sv \
	$ROOT/src/axi_lite_to_axi.sv \
	$ROOT/src/axi_lite_xbar.sv \
	$ROOT/src/axi_arbiter.sv \
	$ROOT/src/axi_address_resolver.sv \
	$ROOT/src/axi_find_first_one.sv \
	$ROOT/test/synth_bench.sv \
]

remove_design -all
elaborate synth_bench
