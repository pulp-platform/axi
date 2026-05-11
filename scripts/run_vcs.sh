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

set -euo pipefail
ROOT=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)

# Seed values for `sv_seed`; can be extended with specific values on a per-TB basis, as well as with
# a random number by passing the `--random` flag.  The default value, 0, is always included to stay
# regression-consistent.
SEEDS=(0)

call_vcs() {
    $VCS -Mlib=work-"${@: -1}" -Mdir=work-"${@: -1}" $VCS_OPT  "$@"
    for seed in ${SEEDS[@]}; do
        echo
        echo "----"
        echo "Running with seed: $seed"
        echo "VCS options: $VCS_OPT"
        ./"${@: -1}" +ntb_random_seed=$seed -exitstatus | tee "${@: -1}"_$seed.log 2>&1
        (! grep -n "Error" "${@: -1}"_$seed.log)
        (! grep -n "Fatal" "${@: -1}"_$seed.log)
    done
    # cleanup
    echo
    echo "----"
    echo "Cleanup"
    rm -rf work-"${@: -1}"
    rm -rf "${@: -1}".daidir
    rm -f  "${@: -1}"
    echo "Done"
    echo "----"
    echo
    echo
}

exec_test() {
    if [ ! -e "$ROOT/test/tb_$1.sv" ]; then
        echo "Testbench for '$1' not found!"
        exit 1
    fi
    case "$1" in
        axi_atop_filter)
            for MAX_TXNS in 1 3 12; do
                call_vcs tb_axi_atop_filter \
                -pvalue+TB_N_TXNS=1000 \
                -pvalue+TB_AXI_MAX_WRITE_TXNS=$MAX_TXNS \
                -o tb_axi_atop_filter_${MAX_TXNS}.vcs
            done
            ;;
        axi_cdc)
            call_vcs tb_axi_cdc -o tb_axi_cdc.vcs
            ;;
        axi_delayer)
            call_vcs tb_axi_delayer -o tb_axi_delayer.vcs
            ;;
        axi_dw_downsizer)
            for AxiSlvPortDataWidth in 8 16 32 64 128 256 512 1024; do
                for (( AxiMstPortDataWidth = 8; \
                        AxiMstPortDataWidth < $AxiSlvPortDataWidth; \
                        AxiMstPortDataWidth *= 2 )); \
                do
                    call_vcs tb_axi_dw_downsizer \
                            -pvalue+TbAxiSlvPortDataWidth=$AxiSlvPortDataWidth \
                            -pvalue+TbAxiMstPortDataWidth=$AxiMstPortDataWidth \
                            -o tb_axi_dw_downsizer_${AxiSlvPortDataWidth}_${AxiMstPortDataWidth}.vcs
                done
            done
            ;;
        axi_dw_upsizer)
            for AxiSlvPortDataWidth in 8 16 32 64 128 256 512 1024; do
                for (( AxiMstPortDataWidth = $AxiSlvPortDataWidth*2; \
                        AxiMstPortDataWidth <= 1024; \
                        AxiMstPortDataWidth *= 2 )); \
                do
                    call_vcs tb_axi_dw_upsizer \
                            -pvalue+TbAxiSlvPortDataWidth=$AxiSlvPortDataWidth \
                            -pvalue+TbAxiMstPortDataWidth=$AxiMstPortDataWidth \
                            -o tb_axi_dw_upsizer_${AxiSlvPortDataWidth}_${AxiMstPortDataWidth}.vcs
                done
            done
            ;;
        axi_fifo)
            for DEPTH in 0 1 16; do
                for FALL_THROUGH in 0 1; do
                    call_vcs tb_axi_fifo \
                            -pvalue+Depth=$DEPTH \
                            -pvalue+FallThrough=$FALL_THROUGH \
                            -o tb_axi_fifo_${DEPTH}_${FALL_THROUGH}.vcs
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
                                    call_vcs tb_axi_iw_converter \
                                            -pvalue+TbEnExcl=$EXCL \
                                            -pvalue+TbAxiSlvPortIdWidth=$SLV_PORT_IW \
                                            -pvalue+TbAxiMstPortIdWidth=$MST_PORT_IW \
                                            -pvalue+TbAxiSlvPortMaxUniqIds=$MAX_UNIQ_SLV_PORT_IDS \
                                            -pvalue+TbAxiSlvPortMaxTxnsPerId=5 \
                                            -o tb_axi_iw_converter_${EXCL}_${SLV_PORT_IW}_${MST_PORT_IW}_${MAX_UNIQ_SLV_PORT_IDS}.vcs
                                else
                                    call_vcs tb_axi_iw_converter \
                                            -pvalue+TbEnExcl=$EXCL \
                                            -pvalue+TbAxiSlvPortIdWidth=$SLV_PORT_IW \
                                            -pvalue+TbAxiMstPortIdWidth=$MST_PORT_IW \
                                            -pvalue+TbAxiSlvPortMaxUniqIds=$MAX_UNIQ_SLV_PORT_IDS \
                                            -pvalue+TbAxiSlvPortMaxTxns=31 \
                                            -pvalue+TbAxiMstPortMaxUniqIds=$((2**MST_PORT_IW)) \
                                            -pvalue+TbAxiMstPortMaxTxnsPerId=7 \
                                            -o tb_axi_iw_converter_${EXCL}_${SLV_PORT_IW}_${MST_PORT_IW}_${MAX_UNIQ_SLV_PORT_IDS}_$((2**MST_PORT_IW)).vcs
                                fi
                            done
                        else
                            call_vcs tb_axi_iw_converter \
                                    -pvalue+TbEnExcl=$EXCL \
                                    -pvalue+TbAxiSlvPortIdWidth=$SLV_PORT_IW \
                                    -pvalue+TbAxiMstPortIdWidth=$MST_PORT_IW \
                                    -pvalue+TbAxiSlvPortMaxTxnsPerId=3 \
                                    -o tb_axi_iw_converter_${EXCL}_${SLV_PORT_IW}_${MST_PORT_IW}.vcs
                        fi
                    done
                done
            done
            ;;
        axi_lite_regs)
            for PRIV in 0 1; do
                for SECU in 0 1; do
                    for BYTES in 42 369; do
                        call_vcs tb_axi_lite_regs \
                                -pvalue+TbPrivProtOnly=$PRIV \
                                -pvalue+TbSecuProtOnly=$SECU \
                                -pvalue+TbRegNumBytes=$BYTES \
                                -o tb_axi_lite_regs_${PRIV}_${SECU}_${BYTES}.vcs
                    done
                done
            done
            ;;
        axi_lite_to_apb)
            for PIPE_REQ in 0 1; do
                for PIPE_RESP in 0 1; do
                    call_vcs tb_axi_lite_to_apb \
                            -pvalue+TbPipelineRequest=$PIPE_REQ \
                            -pvalue+TbPipelineResponse=$PIPE_RESP \
                            -o tb_axi_lite_to_apb_${PIPE_REQ}_${PIPE_RESP}.vcs
                done
            done
            ;;
        axi_lite_to_axi)
            for DW in 8 16 32 64 128 256 512 1024; do
                call_vcs tb_axi_lite_to_axi \
                        -pvalue+TB_DW=$DW \
                        -o tb_axi_lite_to_axi_${DW}.vcs
            done
            ;;
        axi_sim_mem)
            for AW in 16 32 64; do
                for DW in 32 64 128 256 512 1024; do
                    call_vcs tb_axi_sim_mem \
                        -pvalue+TbAddrWidth=$AW \
                        -pvalue+TbDataWidth=$DW \
                        -o tb_axi_sim_mem_${AW}_${DW}.vcs
                done
            done
            ;;
        axi_xbar)
            for NumMst in 1 6; do
                for NumSlv in 1 8; do
                    for Atop in 0 1; do
                        for Exclusive in 0 1; do
                            for UniqueIds in 0 1; do
                                for DataWidth in 64 256; do
                                    for Pipe in 0 1; do
                                        call_vcs tb_axi_xbar \
                                            -pvalue+TbNumMasters=$NumMst \
                                            -pvalue+TbNumSlaves=$NumSlv \
                                            -pvalue+TbEnAtop=$Atop \
                                            -pvalue+TbEnExcl=$Exclusive \
                                            -pvalue+TbUniqueIds=$UniqueIds \
                                            -pvalue+TbAxiDataWidth=$DataWidth  \
                                            -pvalue+TbPipeline=$Pipe \
                                            -o tb_axi_xbar_${NumMst}_${NumSlv}_${Atop}_${Exclusive}_${UniqueIds}_${DataWidth}_${Pipe}.vcs
                                    done
                                done
                            done
                        done
                    done
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
                            call_vcs tb_axi_to_mem_banked \
                                -pvalue+TbAxiDataWidth=$AXI_DATA_WIDTH \
                                -pvalue+TbNumWords=2048 \
                                -pvalue+TbNumBanks=$ACT_BANKS \
                                -pvalue+TbMemDataWidth=$MEM_DATA_WIDTH \
                                -pvalue+TbMemLatency=$MEM_LAT \
                                -pvalue+TbNumWrites=2000 \
                                -pvalue+TbNumReads=2000 \
                                -o tb_axi_to_mem_banked_${AXI_DATA_WIDTH}_${ACT_BANKS}_${MEM_DATA_WIDTH}_${MEM_LAT}.vcs
                        done
                    done
                done
            done
            ;;
        *)
            call_vcs tb_$1 -o tb_${1}.vcs
            ;;
    esac
}

# Parse flags.
PARAMS=""
while (( "$#" )); do
    case "$1" in
        --random-seed)
            SEEDS+=($RANDOM)
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
