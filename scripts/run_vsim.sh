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
# Andreas Kurth  <akurth@iis.ee.ethz.ch>

set -e
ROOT=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)

[ ! -z "$VSIM" ] || VSIM=vsim

call_vsim() {
    echo "run -all" | $VSIM "$@" | tee vsim.log 2>&1
    grep "Errors: 0," vsim.log
}

exec_test() {
    if [ ! -e "$ROOT/test/tb_$1.sv" ]; then
        echo "Testbench for '$1' not found!"
        exit 1
    fi
    case "$1" in
        axi_lite_to_axi)
            for DW in 8 16 32 64 128 256 512 1024; do
                call_vsim tb_axi_lite_to_axi -GDW=$DW -t 1ps -c
            done
            ;;
        axi_dw_downsizer)
            for DW in 8 16 32 64 128 256 512 1024; do
                for (( MULT = 2; MULT <= `echo 1024/$DW`; MULT *= 2 )); do
                    call_vsim tb_axi_dw_downsizer -GDW=$DW -GMULT=$MULT -t 1ps -c
                done
            done
            ;;
        axi_dw_upsizer)
            for DW in 8 16 32 64 128 256 512 1024; do
                for (( MULT = `echo 1024/$DW | bc`; MULT > 1; MULT /= 2 )); do
                    call_vsim tb_axi_dw_upsizer -GDW=$DW -GMULT=$MULT -t 1ps -c
                done
            done
            ;;
        axi_cdc|axi_delayer)
            call_vsim tb_$1
            ;;
        axi_atop_filter)
            for MAX_TXNS in 1 3 12; do
                call_vsim tb_axi_atop_filter -GN_TXNS=1000 -GAXI_MAX_WRITE_TXNS=$MAX_TXNS
            done
            ;;
        axi_lite_regs)
            for PRIV in 0 1; do
                for SECU in 0 1; do
                    call_vsim tb_axi_lite_regs -GPrivProtOnly=$PRIV -GSecuProtOnly=$SECU
                done
            done
            ;;
        *)
            call_vsim tb_$1 -t 1ns -coverage -voptargs="+acc +cover=bcesfx"
            ;;
    esac
    touch "$1.tested"
}

if [ "$#" -eq 0 ]; then
    tests=()
    while IFS=  read -r -d $'\0'; do
        tb_name="$(basename -s .sv $REPLY)"
        dut_name="${tb_name#tb_}"
        tests+=("$dut_name")
    done < <(find "$ROOT/test" -name 'tb_*.sv' -a \( ! -name '*_pkg.sv' \) -print0)
else
    tests=("$@")
fi

for t in "${tests[@]}"; do
    exec_test $t
done
