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
#
# Authors:
# - Fabian Schuiki <fschuiki@iis.ee.ethz.ch>
# - Florian Zaruba <zarubaf@iis.ee.ethz.ch>
# - Andreas Kurth <akurth@iis.ee.ethz.ch>
# - Thomas Benz <tbenz@iis.ee.ethz.ch>

set -euo pipefail
ROOT=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)

[ -n "${VERILATOR+x}" ] || VERILATOR="verilator"

# Seed values for randomization. 0 is always included for regression consistency.
# Individual exec_test cases may append additional seeds.
SEEDS=(0)

VERILATOR_FLAGS=(
    --binary
    --timing
    -Wno-fatal
    -Wno-WIDTHTRUNC
    -Wno-WIDTHEXPAND
    -Wno-ASCRANGE
    -Wno-PINMISSING
    -Wno-IMPLICIT
)

# call_verilator <tb_name> [<-GParam=val> ...]
# Compiles the testbench with the given top-level parameters and runs it for
# each seed in SEEDS.  Analogous to call_vsim in run_vsim.sh.
call_verilator() {
    local tb="$1"
    shift
    local gflags=("$@")

    local outdir="Vtb_${tb}"

    echo "Compiling tb_${tb}${gflags:+ ${gflags[*]}}..."
    $VERILATOR "${VERILATOR_FLAGS[@]}" \
        -f "$ROOT/build/verilator_tb.f" \
        --top-module "tb_${tb}" \
        --Mdir "${outdir}" \
        "${gflags[@]}"

    for seed in "${SEEDS[@]}"; do
        if [[ "$seed" == "random" ]]; then
            seed=$RANDOM
        fi
        echo "Running tb_${tb} (seed=${seed})${gflags:+ ${gflags[*]}}..."
        "./${outdir}/V${tb}" "+verilator+seed+${seed}" | tee verilator.log 2>&1
        grep "Errors: 0," verilator.log
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
                call_verilator axi_atop_filter -GTB_N_TXNS=1000 -GTB_AXI_MAX_WRITE_TXNS=$MAX_TXNS
            done
            ;;
        axi_cdc|axi_delayer)
            call_verilator "$1"
            ;;
        axi_dw_downsizer)
            call_verilator axi_dw_downsizer \
                -GTbAxiSlvPortDataWidth=32 \
                -GTbAxiMstPortDataWidth=16 \
                -GTbInitialBStallCycles=100000
            call_verilator axi_dw_downsizer \
                -GTbAxiSlvPortDataWidth=32 \
                -GTbAxiMstPortDataWidth=16 \
                -GTbInitialRStallCycles=100000
            for AxiSlvPortDataWidth in 8 16 32 64 128 256 512 1024; do
                for (( AxiMstPortDataWidth = 8; \
                        AxiMstPortDataWidth < AxiSlvPortDataWidth; \
                        AxiMstPortDataWidth *= 2 )); do
                    call_verilator axi_dw_downsizer \
                        -GTbAxiSlvPortDataWidth=$AxiSlvPortDataWidth \
                        -GTbAxiMstPortDataWidth=$AxiMstPortDataWidth
                done
            done
            ;;
        axi_dw_upsizer)
            for AxiSlvPortDataWidth in 8 16 32 64 128 256 512 1024; do
                for (( AxiMstPortDataWidth = AxiSlvPortDataWidth*2; \
                        AxiMstPortDataWidth <= 1024; \
                        AxiMstPortDataWidth *= 2 )); do
                    call_verilator axi_dw_upsizer \
                        -GTbAxiSlvPortDataWidth=$AxiSlvPortDataWidth \
                        -GTbAxiMstPortDataWidth=$AxiMstPortDataWidth
                done
            done
            ;;
        axi_fifo)
            for DEPTH in 0 1 16; do
                for FALL_THROUGH in 0 1; do
                    call_verilator axi_fifo -GDepth=$DEPTH -GFallThrough=$FALL_THROUGH
                done
            done
            ;;
        axi_iw_converter)
            for SLV_PORT_IW in 1 2 3 4 8; do
                MAX_SLV_PORT_IDS=$((2**SLV_PORT_IW))
                EXCL_OPTS=(0)
                if [ $SLV_PORT_IW -eq 3 ]; then
                    EXCL_OPTS+=(1)
                fi
                for EXCL in "${EXCL_OPTS[@]}"; do
                    MAX_UNIQ_SLV_PORT_IDS_OPTS=(1 2)
                    if [ $MAX_SLV_PORT_IDS -gt 2 ]; then
                        MAX_UNIQ_SLV_PORT_IDS_OPTS+=(3 4)
                    fi
                    if [ $(( MAX_SLV_PORT_IDS/2 )) -ge 4 ]; then
                        MAX_UNIQ_SLV_PORT_IDS_OPTS+=($((MAX_SLV_PORT_IDS/2-1)))
                    fi
                    MAX_UNIQ_SLV_PORT_IDS_OPTS+=($MAX_SLV_PORT_IDS)
                    for MST_PORT_IW in 1 2 3 4; do
                        if [ $MST_PORT_IW -lt $SLV_PORT_IW ]; then
                            for MAX_UNIQ_SLV_PORT_IDS in "${MAX_UNIQ_SLV_PORT_IDS_OPTS[@]}"; do
                                MAX_MST_PORT_IDS=$((2**MST_PORT_IW))
                                if [ $MAX_UNIQ_SLV_PORT_IDS -le $MAX_MST_PORT_IDS ]; then
                                    call_verilator axi_iw_converter \
                                        -GTbEnExcl=$EXCL \
                                        -GTbAxiSlvPortIdWidth=$SLV_PORT_IW \
                                        -GTbAxiMstPortIdWidth=$MST_PORT_IW \
                                        -GTbAxiSlvPortMaxUniqIds=$MAX_UNIQ_SLV_PORT_IDS \
                                        -GTbAxiSlvPortMaxTxnsPerId=5
                                else
                                    call_verilator axi_iw_converter \
                                        -GTbEnExcl=$EXCL \
                                        -GTbAxiSlvPortIdWidth=$SLV_PORT_IW \
                                        -GTbAxiMstPortIdWidth=$MST_PORT_IW \
                                        -GTbAxiSlvPortMaxUniqIds=$MAX_UNIQ_SLV_PORT_IDS \
                                        -GTbAxiSlvPortMaxTxns=31 \
                                        -GTbAxiMstPortMaxUniqIds=$((2**MST_PORT_IW)) \
                                        -GTbAxiMstPortMaxTxnsPerId=7
                                fi
                            done
                        else
                            call_verilator axi_iw_converter \
                                -GTbEnExcl=$EXCL \
                                -GTbAxiSlvPortIdWidth=$SLV_PORT_IW \
                                -GTbAxiMstPortIdWidth=$MST_PORT_IW \
                                -GTbAxiSlvPortMaxTxnsPerId=3
                        fi
                    done
                done
            done
            ;;
        axi_lite_regs)
            SEEDS+=(10 42)
            for PRIV in 0 1; do
                for SECU in 0 1; do
                    for BYTES in 42 200 369; do
                        call_verilator axi_lite_regs \
                            -GTbPrivProtOnly=$PRIV \
                            -GTbSecuProtOnly=$SECU \
                            -GTbRegNumBytes=$BYTES
                    done
                done
            done
            ;;
        axi_lite_to_apb)
            for PIPE_REQ in 0 1; do
                for PIPE_RESP in 0 1; do
                    call_verilator axi_lite_to_apb \
                        -GTbPipelineRequest=$PIPE_REQ \
                        -GTbPipelineResponse=$PIPE_RESP
                done
            done
            ;;
        axi_lite_to_axi)
            for DW in 8 16 32 64 128 256 512 1024; do
                call_verilator axi_lite_to_axi -GTB_DW=$DW
            done
            ;;
        axi_sim_mem)
            for AW in 16 32 64; do
                for DW in 32 64 128 256 512 1024; do
                    call_verilator axi_sim_mem -GTbAddrWidth=$AW -GTbDataWidth=$DW
                done
            done
            ;;
        axi_xbar)
            for NumMst in 1 6; do
                for NumSlv in 1 8; do
                    for Atop in 0 1; do
                        for Exclusive in 0 1; do
                            for UniqueIds in 0 1; do
                                call_verilator axi_xbar \
                                    -GTbNumMasters=$NumMst \
                                    -GTbNumSlaves=$NumSlv \
                                    -GTbEnAtop=$Atop \
                                    -GTbEnExcl=$Exclusive \
                                    -GTbUniqueIds=$UniqueIds
                            done
                        done
                    done
                done
            done
            ;;
        axi_to_mem_banked)
            for MEM_LAT in 1 2; do
                for BANK_FACTOR in 1 2; do
                    for NUM_BANKS in 1 2; do
                        for AXI_DATA_WIDTH in 64 256; do
                            ACT_BANKS=$((2*BANK_FACTOR*NUM_BANKS))
                            MEM_DATA_WIDTH=$((AXI_DATA_WIDTH/NUM_BANKS))
                            call_verilator axi_to_mem_banked \
                                -GTbAxiDataWidth=$AXI_DATA_WIDTH \
                                -GTbNumWords=2048 \
                                -GTbNumBanks=$ACT_BANKS \
                                -GTbMemDataWidth=$MEM_DATA_WIDTH \
                                -GTbMemLatency=$MEM_LAT \
                                -GTbNumWrites=2000 \
                                -GTbNumReads=2000
                        done
                    done
                done
            done
            ;;
        axi_lite_dw_converter)
            for DWSLV in 32 64 128; do
                for DWMST in 16 32 64; do
                    call_verilator axi_lite_dw_converter \
                        -GTbAxiDataWidthSlv=$DWSLV \
                        -GTbAxiDataWidthMst=$DWMST
                done
            done
            ;;
        *)
            call_verilator "$1"
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
        -*--*)
            echo "Error: Unsupported flag '$1'." >&2
            exit 1;;
        *)
            PARAMS="$PARAMS $1"
            shift;;
    esac
done
eval set -- "$PARAMS"

if [ "$#" -eq 0 ]; then
    tests=()
    while IFS= read -r -d $'\0'; do
        tb_name="$(basename -s .sv "$REPLY")"
        dut_name="${tb_name#tb_}"
        tests+=("$dut_name")
    done < <(find "$ROOT/test" -name 'tb_*.sv' -not -name '*_pkg.sv' -print0)
else
    tests=("$@")
fi

for t in "${tests[@]}"; do
    exec_test "$t"
done
