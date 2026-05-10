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

# select IIS-internal tool commands if we run on IIS machines
ifneq (,$(wildcard /etc/iis.version))
	VSIM        ?= questa-2025.1 vsim
	SYNOPSYS_DC ?= synopsys-2022.03 dcnxt_shell
else
	VSIM        ?= vsim
	SYNOPSYS_DC ?= dc_shell
endif

VERILATOR    ?= verilator

TBS             ?= axi_addr_test \
               axi_atop_filter \
               axi_cdc axi_delayer \
               axi_dw_downsizer \
               axi_dw_upsizer \
               axi_fifo \
               axi_isolate \
               axi_iw_converter \
               axi_lite_regs \
               axi_lite_to_apb \
               axi_lite_to_axi \
               axi_lite_mailbox \
               axi_lite_xbar \
               axi_modify_address \
               axi_serializer \
               axi_sim_mem \
               axi_to_axi_lite \
               axi_to_mem_banked \
               axi_xbar

SIM_TARGETS             := $(addsuffix .log,$(addprefix sim-,$(TBS)))
SIM_VERILATOR_TARGETS   := $(addsuffix .log,$(addprefix sim-verilator-,$(TBS)))


.SHELL: bash

.PHONY: help all sim_all sim_all_verilator verilator clean


help:
	@echo ""
	@echo "--- Synopsys DC ---"
	@echo "elab.log:              elaborates all files using Synopsys DC"
	@echo ""
	@echo "--- Questasim ---"
	@echo "compile.log:           compile files using Questasim"
	@echo "sim-#TB#.log:          simulate a testbench with Questasim"
	@echo "sim_all:               simulate all testbenches with Questasim"
	@echo ""
	@echo "--- Verilator ---"
	@echo "compile-verilator.log: lint-check and generate Verilator file lists"
	@echo "sim-verilator-#TB#.log: simulate a testbench with Verilator"
	@echo "sim_all_verilator:     simulate all testbenches with Verilator"
	@echo ""
	@echo "Available testbenches:"
	@echo "$(addprefix ###############-#,$(TBS))" | sed -e 's/ /\n/g' | sed -e 's/#/ /g'
	@echo ""
	@echo "clean:                 remove generated files"
	@echo ""


all: compile.log elab.log sim_all


sim_all: $(SIM_TARGETS)


sim_all_verilator: $(SIM_VERILATOR_TARGETS)


build:
	mkdir -p $@


elab.log: Bender.yml | build
	export SYNOPSYS_DC="$(SYNOPSYS_DC)"; cd build && ../scripts/synth.sh | tee ../$@
	(! grep -n "Error:" $@)


compile.log: Bender.yml | build
	export VSIM="$(VSIM)"; cd build && ../scripts/compile_vsim.sh | tee ../$@
	(! grep -n "Error:" $@)


sim-%.log: compile.log
	export VSIM="$(VSIM)"; cd build && ../scripts/run_vsim.sh --random-seed $* | tee ../$@
	(! grep -n "Error:" $@)
	(! grep -n "Fatal:" $@)


compile-verilator.log: Bender.yml | build
	export VERILATOR="$(VERILATOR)"; cd build && ../scripts/compile_verilator.sh | tee ../compile-verilator.log
	(! grep -n "Error:" compile-verilator.log)


sim-verilator-%.log: compile-verilator.log
	export VERILATOR="$(VERILATOR)"; cd build && ../scripts/run_verilator.sh --random-seed $* | tee ../sim-verilator-$*.log
	(! grep -n "Error:" sim-verilator-$*.log)
	(! grep -n "Fatal:" sim-verilator-$*.log)


clean:
	rm -rf build
	rm -f  *.log
