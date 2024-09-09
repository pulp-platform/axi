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
# - Wolfgang Roenninger <wroennin@iis.ee.ethz.ch>

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
        axi_fifo)
            for DEPTH in 0 1 16; do
                for FALL_THROUGH in 0 1; do
                    call_vsim tb_axi_fifo -gDepth=$DEPTH \
                            -gFallThrough=$FALL_THROUGH
                done
            done
            ;;
        axi_iw_converter)
            for SLV_PORT_IW in 1 2 3 4 8; do
                MAX_SLV_PORT_IDS=$((2**SLV_PORT_IW))
                MAX_UNIQ_SLV_PORT_IDS_OPTS=(1 2)
                EXCL_OPTS=(0)
                if [ $SLV_PORT_IW -eq 3 ]; then
                    # Save time by not testing exclusive accesses for every parametrization.
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
                        if [ $MST_PORT_IW -lt $SLV_PORT_IW ]; then # downsize
                            for MAX_UNIQ_SLV_PORT_IDS in "${MAX_UNIQ_SLV_PORT_IDS_OPTS[@]}"; do
                                MAX_MST_PORT_IDS=$((2**MST_PORT_IW))
                                if [ $MAX_UNIQ_SLV_PORT_IDS -le $MAX_MST_PORT_IDS ]; then
                                    call_vsim tb_axi_iw_converter \
                                            -t 1ns -coverage -classdebug \
                                            -voptargs="+acc +cover=bcesfx" \
                                            -GTbEnExcl=$EXCL \
                                            -GTbAxiSlvPortIdWidth=$SLV_PORT_IW \
                                            -GTbAxiMstPortIdWidth=$MST_PORT_IW \
                                            -GTbAxiSlvPortMaxUniqIds=$MAX_UNIQ_SLV_PORT_IDS \
                                            -GTbAxiSlvPortMaxTxnsPerId=5
                                else
                                    call_vsim tb_axi_iw_converter \
                                            -t 1ns -coverage -classdebug \
                                            -voptargs="+acc +cover=bcesfx" \
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
                            call_vsim tb_axi_iw_converter \
                                    -t 1ns -coverage -classdebug \
                                    -voptargs="+acc +cover=bcesfx" \
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
        axi_to_mem_banked)
            for MEM_LAT in 1 2; do
                for BANK_FACTOR in 1 2; do
                    for NUM_BANKS in 1 2 ; do
                        for AXI_DATA_WIDTH in 64 256 ; do
                            ACT_BANKS=$((2*$BANK_FACTOR*$NUM_BANKS))
                            MEM_DATA_WIDTH=$(($AXI_DATA_WIDTH/$NUM_BANKS))
                            call_vsim tb_axi_to_mem_banked \
                                -voptargs="+acc +cover=bcesfx" \
                                -gTbAxiDataWidth=$AXI_DATA_WIDTH \
                                -gTbNumWords=2048 \
                                -gTbNumBanks=$ACT_BANKS \
                                -gTbMemDataWidth=$MEM_DATA_WIDTH \
                                -gTbMemLatency=$MEM_LAT \
                                -gTbNumWrites=2000 \
                                -gTbNumReads=2000
                        done
                    done
                done
            done
            ;;
        axi_xbar)
            for GEN_ATOP in 0 1; do
                for NUM_MST in 1 6; do
                    for NUM_SLV in 2 9; do
                        for MST_ID_USE in 3 5; do
                            MST_ID=5
                            for DATA_WIDTH in 64 256; do
                                for PIPE in 0 1; do
                                    call_vsim tb_axi_xbar -t 1ns      \
                                        -gTbNumMasters=$NUM_MST       \
                                        -gTbNumSlaves=$NUM_SLV        \
                                        -gTbAxiIdWidthMasters=$MST_ID \
                                        -gTbAxiIdUsed=$MST_ID_USE     \
                                        -gTbAxiDataWidth=$DATA_WIDTH  \
                                        -gTbPipeline=$PIPE            \
                                        -gTbEnAtop=$GEN_ATOP
                                done
                            done
                        done
                    done
                done
            done
            ;;
        axi_lite_dw_converter)
            for DWSLV in 32 64 128; do
                for DWMST in 16 32 64; do
                    call_vsim tb_axi_lite_dw_converter -gTbAxiDataWidthSlv=$DWSLV -gTbAxiDataWidthMst=$DWMST
                done
            done
            ;;
        axi_mcast_xbar)
            for GEN_ATOP in 0 1; do
                for NUM_MST in 1 6; do
                    for NUM_SLV in 2 9; do
                        for MST_ID_USE in 3 5; do
                            MST_ID=5
                            for DATA_WIDTH in 64 256; do
                                for PIPE in 0; do
                                    for UNIQUE_IDS in 0 1; do
                                        call_vsim tb_axi_mcast_xbar -t 1ns \
                                            -gTbNumMasters=$NUM_MST        \
                                            -gTbNumMcastSlaves=$NUM_SLV    \
                                            -gTbAxiIdWidthMasters=$MST_ID  \
                                            -gTbAxiIdUsed=$MST_ID_USE      \
                                            -gTbAxiDataWidth=$DATA_WIDTH   \
                                            -gTbPipeline=$PIPE             \
                                            -gTbEnAtop=$GEN_ATOP           \
                                            -gTbUniqueIds=$UNIQUE_IDS
                                    done
                                done
                            done
                        done
                    done
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
