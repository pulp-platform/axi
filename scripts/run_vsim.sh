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
# Authors:
# - Andreas Kurth <akurth@iis.ee.ethz.ch>
# - Fabian Schuiki <fschuiki@iis.ee.ethz.ch>
# - Matheus Cavalcante <matheusd@iis.ee.ethz.ch>

set -euo pipefail
ROOT=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)

if test -z ${VSIM+x}; then
    VSIM=vsim
fi

# Seed values for `sv_seed`; can be extended with specific values on a per-TB basis, as well as with
# a random number by passing the `--random` flag.  The default value, 0, is always included to stay
# regression-consistent.
SEEDS=(0)

call_vsim() {
    for seed in ${SEEDS[@]}; do
        echo "run -all" | $VSIM -sv_seed $seed "$@" | tee vsim.log 2>&1
        grep "Errors: 0," vsim.log
    done
}

exec_test() {
    if [ ! -e "$ROOT/test/tb_$1.sv" ]; then
        echo "Testbench for '$1' not found!"
        exit 1
    fi
    case "$1" in
        axi_atop_filter)
            for MAX_TXNS in 1 3 12; do
                call_vsim tb_axi_atop_filter -gTB_N_TXNS=1000 -gTB_AXI_MAX_WRITE_TXNS=$MAX_TXNS
            done
            ;;
        axi_cdc|axi_delayer)
            call_vsim tb_$1
            ;;
        axi_dw_downsizer)
            for AxiSlvPortDataWidth in 8 16 32 64 128 256 512 1024; do
                for (( AxiMstPortDataWidth = 8; \
                        AxiMstPortDataWidth < $AxiSlvPortDataWidth; \
                        AxiMstPortDataWidth *= 2 )); \
                do
                    call_vsim tb_axi_dw_downsizer \
                            -gTbAxiSlvPortDataWidth=$AxiSlvPortDataWidth \
                            -gTbAxiMstPortDataWidth=$AxiMstPortDataWidth -t 1ps
                done
            done
            ;;
        axi_dw_upsizer)
            for AxiSlvPortDataWidth in 8 16 32 64 128 256 512 1024; do
                for (( AxiMstPortDataWidth = $AxiSlvPortDataWidth*2; \
                        AxiMstPortDataWidth <= 1024; \
                        AxiMstPortDataWidth *= 2 )); \
                do
                    call_vsim tb_axi_dw_upsizer \
                            -gTbAxiSlvPortDataWidth=$AxiSlvPortDataWidth \
                            -gTbAxiMstPortDataWidth=$AxiMstPortDataWidth -t 1ps
                done
            done
            ;;
        axi_lite_regs)
            SEEDS+=(10 42)
            for PRIV in 0 1; do
                for SECU in 0 1; do
                    for BYTES in 42 200 369; do
                        call_vsim tb_axi_lite_regs -gTbPrivProtOnly=$PRIV -gTbSecuProtOnly=$SECU \
                                -gTbRegNumBytes=$BYTES -t 1ps
                    done
                done
            done
            ;;
        axi_lite_to_apb)
            for PIPE_REQ in 0 1; do
                for PIPE_RESP in 0 1; do
                    call_vsim tb_axi_lite_to_apb -gTbPipelineRequest=$PIPE_REQ \
                            -gTbPipelineResponse=$PIPE_RESP
                done
            done
            ;;
        axi_lite_to_axi)
            for DW in 8 16 32 64 128 256 512 1024; do
                call_vsim tb_axi_lite_to_axi -gTB_DW=$DW -t 1ps
            done
            ;;
        axi_sim_mem)
            for AW in 16 32 64; do
                for DW in 32 64 128 256 512 1024; do
                    call_vsim tb_axi_sim_mem -gTbAddrWidth=$AW -gTbDataWidth=$DW -t 1ps
                done
            done
            ;;
        axi_xbar)
            for Atop in 0 1; do
                for Exclusive in 0 1; do
                    call_vsim tb_axi_xbar -gTbEnAtop=$Atop -gTbEnExcl=$Exclusive
                done
            done
            ;;
        *)
            call_vsim tb_$1 -t 1ns -coverage -voptargs="+acc +cover=bcesfx"
            ;;
    esac
}

# Parse flags.
PARAMS=""
while (( "$#" )); do
    case "$1" in
        --random-seed)
            SEEDS+=(random)
            shift;;
        -*--*) # unsupported flag
            echo "Error: Unsupported flag '$1'." >&2
            exit 1;;
        *) # preserve positional arguments
            PARAMS="$PARAMS $1"
            shift;;
    esac
done
eval set -- "$PARAMS"

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
