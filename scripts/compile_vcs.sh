#!/bin/bash
# Copyright (c) 2022 ETH Zurich, University of Bologna
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
# - Thomas Benz <tbenz@iis.ee.ethz.ch>

set -e

[ ! -z "$VLOGAN" ] || VLOGAN=vlogan

bender script vcs -t test -t rtl -t simulation \
    --vlog-arg="-full64" \
    --vlog-arg="-nc" \
    --vlog-arg="-q" \
    --vlog-arg="-assert svaext" \
    --vlog-arg="-timescale=1ns/1ps" \
    --vlogan-bin="$VLOGAN" \
    | grep -v "ROOT=" | sed '3 i ROOT="../"' \
    > compile_vcs.sh

source compile_vcs.sh
