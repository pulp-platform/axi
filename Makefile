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

TBS         ?= axi_addr_test \
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

SIM_TARGETS := $(addsuffix .log,$(addprefix sim-,$(TBS)))

# RTL run of the netlist testbench, for golden comparison (same tb, no netlist)
.PHONY: sim_rtl_compare
#sim_rtl.log: | build
#	bender script vsim -t simulation -t test \
#		--vlog-arg="-suppress 2583" --vlog-arg="-override_timescale 1ns/1ps" \
#		> build/compile_rtl.tcl
#	echo 'vopt +acc $(TBENCH_NETLIST) -o $(TBENCH_NETLIST)_rtl_opt' >> build/compile_rtl.tcl
#	export VSIM="$(VSIM)"; cd build && \
#		$(VSIM) -c -do "source compile_rtl.tcl; \
#		     vsim $(TBENCH_NETLIST)_rtl_opt; \
#		     run -all; quit" | tee ../sim_rtl.log

sim_rtl.log: | build
	bender script vsim -t simulation -t test \
		--vlog-arg="-suppress 2583" --vlog-arg="-override_timescale 1ns/1ps" \
		> build/compile_rtl.tcl
	echo 'vopt +acc $(TBENCH_NETLIST) -o $(TBENCH_NETLIST)_rtl_opt' >> build/compile_rtl.tcl
	export VSIM="$(VSIM)"; cd build && \
		$(VSIM) -c -do "source compile_rtl.tcl; \
		     vsim $(TBENCH_NETLIST)_rtl_opt -wlf rtl.wlf; \
		     log -r /*; \
		     run -all; quit" | tee ../sim_rtl.log

# ------------------------------------------------------------------------------
# Post-synthesis netlist simulation (Questa)
# ------------------------------------------------------------------------------
ROOT ?= $(realpath .)
TBENCH_NETLIST ?= tb_axi_xbar_zoix

# Vendor precompiled Questa cell library (has specify; loads in 2025.1)
CELL_LIB_NAME ?= sc7p5mcpp84_12lpplus_base_lvt_c16
CELL_LIB_PATH ?= /usr/pack/gf-12-kgf/arm/gf/12lpplus/sc7p5mcpp84_base_lvt_c16/r5p0/questa.dz/2021.2/$(CELL_LIB_NAME)

# SDF (COND-stripped so IOPATHs match the cell specify paths)
NETLIST_SDF_RAW ?= $(ROOT)/monitor-synth/synopsys/out/relaxi_xbar_sspg_0p72v_125c_0.55ns/netlist_relaxi_xbar.sdf
NETLIST_SDF     ?= $(ROOT)/monitor-synth/synopsys/out/relaxi_xbar_sspg_0p72v_125c_0.55ns/netlist_relaxi_xbar_nocond.sdf
SDF_SCOPE       ?= /tb_axi_xbar_zoix/i_xbar_dut/i_dut

ifeq ($(NETLIST_SIM),1)
	NETLIST_TARGET     := -t netlist_sim
	NETLIST_VOPT_FLAGS := +define+NETLIST_SIM +acc -L $(CELL_LIB_NAME)
  ifeq ($(SDF),1)
	NETLIST_VSIM_FLAGS := +notimingchecks -sdfnoerror -suppress 3251 \
	                      -L $(CELL_LIB_NAME) \
	                      -sdfmax $(SDF_SCOPE)=$(NETLIST_SDF)
	NETLIST_SDF_DEP    := $(NETLIST_SDF)
  else
	NETLIST_VSIM_FLAGS := +notimingchecks +nospecify -suppress 3251 \
	                      -L $(CELL_LIB_NAME)
	NETLIST_SDF_DEP    :=
  endif
endif

compile_netlist.tcl: Bender.yml | build
	bender script vsim \
		-t simulation -t test $(NETLIST_TARGET) \
		--vlog-arg="-suppress 2583" \
		--vlog-arg="-override_timescale 1ns/1ps" \
		> build/compile_netlist.tcl

compile_netlist.log: compile_netlist.tcl
	export VSIM="$(VSIM)"; cd build && \
		$(VSIM) -c -do "quit -code [source compile_netlist.tcl]" | tee ../compile_netlist.log
	(! grep -n "Error:" compile_netlist.log)

sim_netlist.log: compile_netlist.log $(NETLIST_SDF_DEP) map_cell_lib
	export VSIM="$(VSIM)"; cd build && \
		$(VSIM) -c \
		-do "vopt $(NETLIST_VOPT_FLAGS) $(TBENCH_NETLIST) -o $(TBENCH_NETLIST)_opt -gTbEnAtop=0; \
		     vsim $(TBENCH_NETLIST)_opt $(NETLIST_VSIM_FLAGS); \
		     log -r /*; run -all; quit" \
		| tee ../sim_netlist.log

.SHELL: bash

.PHONY: map_cell_lib
map_cell_lib:
	cd build && questa-2025.1 vmap $(CELL_LIB_NAME) $(CELL_LIB_PATH)

$(NETLIST_SDF): $(NETLIST_SDF_RAW) scripts/strip_cond.py
	python3 scripts/strip_cond.py $< $@

.PHONY: help all sim_all clean


help:
	@echo ""
	@echo "elab.log:     elaborates all files using Synopsys DC"
	@echo "compile.log:  compile files using Questasim"
	@echo "sim-#TB#.log: simulates a given testbench, available TBs are:"
	@echo "$(addprefix ###############-#,$(TBS))" | sed -e 's/ /\n/g' | sed -e 's/#/ /g'
	@echo "sim_all:      simulates all available testbenches"
	@echo ""
	@echo "clean:        cleans generated files"
	@echo ""


all: compile.log elab.log sim_all


sim_all: $(SIM_TARGETS)


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


clean:
	rm -rf build
	rm -f  *.log
