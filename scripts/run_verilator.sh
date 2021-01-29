#!/bin/bash
# Copyright (c) 2021 ETH Zurich, University of Bologna
#
# Copyright and related rights are licensed under the Solderpad Hardware
# License, Version 0.51 (the "License"); you may not use this file except in
# compliance with the License.  You may obtain a copy of the License at
# http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
# or agreed to in writing, software, hardware and materials distributed under
# this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
# CONDITIONS OF ANY KIND, either express or implied. See the License for the
# specific language governing permissions and limitations under the License.

set -e
ROOT=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)

[ ! -z "$VERILATOR" ] || VERILATOR="verilator"

bender script verilator -t synthesis -t synth_test > ./verilator.f

VERILATOR_FLAGS=()
VERILATOR_FLAGS+=(-Wno-fatal)

$VERILATOR --top-module axi_synth_bench --lint-only -f verilator.f ${VERILATOR_FLAGS[@]}
