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
# - Michael Rogenmoser <michaero@iis.ee.ethz.ch>

set -euo pipefail
ROOT=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)

VERILATOR="${VERILATOR:-verilator}"

SEEDS=(1)

compile_and_run() {
    local tb_module="$1"
    shift
    local params=("$@")
    local build_dir="build_${tb_module}"

    # Build a unique directory name incorporating parameters to allow parallel runs
    for p in "${params[@]+"${params[@]}"}"; do
        build_dir="${build_dir}_${p//=/_}"
    done

    mkdir -p "$build_dir"

    bender script verilator -t test -t rtl -t simulation > "$build_dir/verilator.f"

    VERILATOR_FLAGS=()
    VERILATOR_FLAGS+=(-Wno-fatal)
    VERILATOR_FLAGS+=(--timing)
    VERILATOR_FLAGS+=(--assert)
    VERILATOR_FLAGS+=(--binary)
    VERILATOR_FLAGS+=(--top-module "$tb_module")
    for p in "${params[@]+"${params[@]}"}"; do
        VERILATOR_FLAGS+=("-G${p}")
    done
    VERILATOR_FLAGS+=(-f "$build_dir/verilator.f")
    VERILATOR_FLAGS+=(-Mdir "$build_dir/obj_dir")

    $VERILATOR "${VERILATOR_FLAGS[@]}"

    for seed in "${SEEDS[@]}"; do
        "$build_dir/obj_dir/V${tb_module}" "+verilator+seed+${seed}"
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
                compile_and_run tb_axi_atop_filter \
                    "TB_N_TXNS=1000" \
                    "TB_AXI_MAX_WRITE_TXNS=${MAX_TXNS}"
            done
            ;;
        axi_cdc|axi_delayer)
            compile_and_run tb_$1
            ;;
        axi_dw_downsizer)
            compile_and_run tb_axi_dw_downsizer \
                "TbAxiSlvPortDataWidth=32" \
                "TbAxiMstPortDataWidth=16" \
                "TbInitialBStallCycles=100000"
            compile_and_run tb_axi_dw_downsizer \
                "TbAxiSlvPortDataWidth=32" \
                "TbAxiMstPortDataWidth=16" \
                "TbInitialRStallCycles=100000"
            for AxiSlvPortDataWidth in 8 16 32 64 128 256 512 1024; do
                for (( AxiMstPortDataWidth = 8; \
                        AxiMstPortDataWidth < AxiSlvPortDataWidth; \
                        AxiMstPortDataWidth *= 2 )); \
                do
                    compile_and_run tb_axi_dw_downsizer \
                        "TbAxiSlvPortDataWidth=${AxiSlvPortDataWidth}" \
                        "TbAxiMstPortDataWidth=${AxiMstPortDataWidth}"
                done
            done
            ;;
        axi_dw_upsizer)
            for AxiSlvPortDataWidth in 8 16 32 64 128 256 512 1024; do
                for (( AxiMstPortDataWidth = AxiSlvPortDataWidth*2; \
                        AxiMstPortDataWidth <= 1024; \
                        AxiMstPortDataWidth *= 2 )); \
                do
                    compile_and_run tb_axi_dw_upsizer \
                        "TbAxiSlvPortDataWidth=${AxiSlvPortDataWidth}" \
                        "TbAxiMstPortDataWidth=${AxiMstPortDataWidth}"
                done
            done
            ;;
        axi_fifo)
            for DEPTH in 0 1 16; do
                for FALL_THROUGH in 0 1; do
                    compile_and_run tb_axi_fifo \
                        "Depth=${DEPTH}" \
                        "FallThrough=${FALL_THROUGH}"
                done
            done
            ;;
        axi_iw_converter)
            for SLV_PORT_IW in 1 2 3 4 8; do
                MAX_SLV_PORT_IDS=$((2**SLV_PORT_IW))
                MAX_UNIQ_SLV_PORT_IDS_OPTS=(1 2)
                EXCL_OPTS=(0)
                if [ $SLV_PORT_IW -eq 3 ]; then
                    EXCL_OPTS+=(1)
                fi
                for EXCL in "${EXCL_OPTS[@]}"; do
                    if [ $MAX_SLV_PORT_IDS -gt 2 ]; then
                        MAX_UNIQ_SLV_PORT_IDS_OPTS+=(3 4)
                    fi
                    if [ $(($MAX_SLV_PORT_IDS/2)) -ge 4 ]; then
                        MAX_UNIQ_SLV_PORT_IDS_OPTS+=($((MAX_SLV_PORT_IDS/2-1)))
                    fi
                    MAX_UNIQ_SLV_PORT_IDS_OPTS+=($MAX_SLV_PORT_IDS)
                    for MST_PORT_IW in 1 2 3 4; do
                        if [ $MST_PORT_IW -lt $SLV_PORT_IW ]; then
                            for MAX_UNIQ_SLV_PORT_IDS in "${MAX_UNIQ_SLV_PORT_IDS_OPTS[@]}"; do
                                MAX_MST_PORT_IDS=$((2**MST_PORT_IW))
                                if [ $MAX_UNIQ_SLV_PORT_IDS -le $MAX_MST_PORT_IDS ]; then
                                    compile_and_run tb_axi_iw_converter \
                                        "TbEnExcl=${EXCL}" \
                                        "TbAxiSlvPortIdWidth=${SLV_PORT_IW}" \
                                        "TbAxiMstPortIdWidth=${MST_PORT_IW}" \
                                        "TbAxiSlvPortMaxUniqIds=${MAX_UNIQ_SLV_PORT_IDS}" \
                                        "TbAxiSlvPortMaxTxnsPerId=5"
                                else
                                    compile_and_run tb_axi_iw_converter \
                                        "TbEnExcl=${EXCL}" \
                                        "TbAxiSlvPortIdWidth=${SLV_PORT_IW}" \
                                        "TbAxiMstPortIdWidth=${MST_PORT_IW}" \
                                        "TbAxiSlvPortMaxUniqIds=${MAX_UNIQ_SLV_PORT_IDS}" \
                                        "TbAxiSlvPortMaxTxns=31" \
                                        "TbAxiMstPortMaxUniqIds=$((2**MST_PORT_IW))" \
                                        "TbAxiMstPortMaxTxnsPerId=7"
                                fi
                            done
                        else
                            compile_and_run tb_axi_iw_converter \
                                "TbEnExcl=${EXCL}" \
                                "TbAxiSlvPortIdWidth=${SLV_PORT_IW}" \
                                "TbAxiMstPortIdWidth=${MST_PORT_IW}" \
                                "TbAxiSlvPortMaxTxnsPerId=3"
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
                        compile_and_run tb_axi_lite_regs \
                            "TbPrivProtOnly=${PRIV}" \
                            "TbSecuProtOnly=${SECU}" \
                            "TbRegNumBytes=${BYTES}"
                    done
                done
            done
            ;;
        axi_lite_to_apb)
            for PIPE_REQ in 0 1; do
                for PIPE_RESP in 0 1; do
                    compile_and_run tb_axi_lite_to_apb \
                        "TbPipelineRequest=${PIPE_REQ}" \
                        "TbPipelineResponse=${PIPE_RESP}"
                done
            done
            ;;
        axi_lite_to_axi)
            for DW in 8 16 32 64 128 256 512 1024; do
                compile_and_run tb_axi_lite_to_axi "TB_DW=${DW}"
            done
            ;;
        axi_sim_mem)
            for AW in 16 32 64; do
                for DW in 32 64 128 256 512 1024; do
                    compile_and_run tb_axi_sim_mem \
                        "TbAddrWidth=${AW}" \
                        "TbDataWidth=${DW}"
                done
            done
            ;;
        axi_xbar)
            for NumMst in 1 6; do
                for NumSlv in 1 8; do
                    for Atop in 0 1; do
                        for Exclusive in 0 1; do
                            for UniqueIds in 0 1; do
                                compile_and_run tb_axi_xbar \
                                    "TbNumMasters=${NumMst}" \
                                    "TbNumSlaves=${NumSlv}" \
                                    "TbEnAtop=${Atop}" \
                                    "TbEnExcl=${Exclusive}" \
                                    "TbUniqueIds=${UniqueIds}"
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
                            compile_and_run tb_axi_to_mem_banked \
                                "TbAxiDataWidth=${AXI_DATA_WIDTH}" \
                                "TbNumWords=2048" \
                                "TbNumBanks=${ACT_BANKS}" \
                                "TbMemDataWidth=${MEM_DATA_WIDTH}" \
                                "TbMemLatency=${MEM_LAT}" \
                                "TbNumWrites=2000" \
                                "TbNumReads=2000"
                        done
                    done
                done
            done
            ;;
        axi_lite_dw_converter)
            for DWSLV in 32 64 128; do
                for DWMST in 16 32 64; do
                    compile_and_run tb_axi_lite_dw_converter \
                        "TbAxiDataWidthSlv=${DWSLV}" \
                        "TbAxiDataWidthMst=${DWMST}"
                done
            done
            ;;
        *)
            compile_and_run tb_$1
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
    exec_test "$t"
done
