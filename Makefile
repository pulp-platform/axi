# Copyright and related rights are licensed under the Solderpad Hardware
# License, Version 0.51 (the "License"); you may not use this file except in
# compliance with the License.  You may obtain a copy of the License at
# http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
# or agreed to in writing, software, hardware and materials distributed under
# this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
# CONDITIONS OF ANY KIND, either express or implied. See the License for the
# specific language governing permissions and limitations under the License.
#
# Authors:
# - Thomas Benz <tbenz@iis.ee.ethz.ch>

VSIM        ?= "vsim"
SYNOPSYS_DC ?= "dc_shell"

TBS ?= sim-axi_addr_test.log sim-axi_atop_filter.log sim-axi_cdc.log sim-axi_delayer.log sim-axi_dw_downsizer.log sim-axi_dw_upsizer.log sim-axi_fifo.log sim-axi_isolate.log sim-axi_iw_converter.log sim-axi_lite_regs.log sim-axi_lite_to_apb.log sim-axi_lite_to_axi.log sim-axi_lite_mailbox.log sim-axi_lite_xbar.log sim-axi_modify_address.log sim-axi_serializer.log sim-axi_sim_mem.log sim-axi_to_axi_lite.log sim-axi_to_mem_banked.log sim-axi_xbar.log

.SHELL: bash

.PHONY: all sim_all clean

all: compile.log elab.log sim_all

sim_all: $(TBS)

build:
	mkdir -p $@

compile.log: Bender.yml | build
	export VSIM=$(VSIM); cd build && ../scripts/compile_vsim.sh | tee ../$@
	(! grep -n "Error:" $@)

elab.log: Bender.yml | build
	export SYNOPSYS_DC=$(SYNOPSYS_DC); cd build && ../scripts/synth.sh | tee ../$@

sim-%.log: compile.log
	export VSIM=$(VSIM); cd build && ../scripts/run_vsim.sh --random-seed $* | tee ../$@
	(! grep -n "Error:" $@)
	(! grep -n "Fatal:" $@)

clean:
	rm -rf build
	rm -f  *.log
