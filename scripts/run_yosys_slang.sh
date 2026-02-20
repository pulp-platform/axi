#!/bin/bash
# Copyright (c) 2024 ETH Zurich, University of Bologna
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
# Authors:
# - Michael Rogenmoser <michaero@iis.ee.ethz.ch>

set -e
ROOT=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)

[ ! -z "$YOSYS" ] || YOSYS="yosys"

bender script flist-plus -t synthesis -t synth_test > ./slang.flist

$YOSYS -m slang -p "read_slang -f slang.flist --allow-use-before-declare --ignore-unknown-modules --keep-hierarchy --top axi_synth_bench; hierarchy; exit"
