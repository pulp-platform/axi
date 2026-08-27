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
# a random number by passing the `--random-seed` flag.  The default value, 0, is always included to
# stay regression-consistent.
SEEDS=(0)

# Every simulation (one parametrization run with one seed) gets a deterministic index in the
# enumeration order of this script. Parallelism is provided by the CI: a heavy sweep is split by
# putting `parallel: N` on its job together with `VSIM_SHARDED=1`. Each copy walks the same
# enumeration but executes only the configs whose index falls on its shard (round-robin over
# `CI_NODE_INDEX`/`CI_NODE_TOTAL`). The `VSIM_SHARDED` opt-in is needed because `parallel:matrix`
# jobs also get `CI_NODE_*` set, where they mean the matrix position, not a sweep shard.
#
# Reproduce one CI shard locally with e.g.:
#   VSIM_SHARDED=1 CI_NODE_INDEX=2 CI_NODE_TOTAL=2 ../scripts/run_vsim.sh axi_xbar
# Pass `--list` to print the enumerated configs with their indices instead of simulating.
CONFIG_IDX=0
NUM_EXECUTED=0
SHARD_INDEX=1
SHARD_TOTAL=1
if [[ -n ${VSIM_SHARDED:-} ]]; then
    SHARD_INDEX=${CI_NODE_INDEX:-1}
    SHARD_TOTAL=${CI_NODE_TOTAL:-1}
fi
LIST_ONLY=0

call_vsim() {
    local seed log
    for seed in "${SEEDS[@]}"; do
        CONFIG_IDX=$((CONFIG_IDX + 1))
        if (( (CONFIG_IDX - 1) % SHARD_TOTAL != SHARD_INDEX - 1 )); then
            continue
        fi
        if (( LIST_ONLY )); then
            echo "$CONFIG_IDX: $* -sv_seed $seed"
            continue
        fi
        # One log file per config, so a full sweep leaves every log behind and the actual value
        # of a random seed can be recovered from the log after a failure.
        log="vsim-$1-$CONFIG_IDX.log"
        echo "run -all" | $VSIM -sv_seed "$seed" "$@" 2>&1 | tee "$log"
        grep "Errors: 0," "$log"
        NUM_EXECUTED=$((NUM_EXECUTED + 1))
    done
}

exec_test() {
    # Work on a per-test copy so that any per-TB seed additions below do not leak into the
    # subsequent tests of a full run.
    local SEEDS=("${SEEDS[@]}")
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
            call_vsim tb_axi_dw_downsizer \
                    -gTbAxiSlvPortDataWidth=32 \
                    -gTbAxiMstPortDataWidth=16 \
                    -gTbInitialBStallCycles=100000 -t 1ps
            call_vsim tb_axi_dw_downsizer \
                    -gTbAxiSlvPortDataWidth=32 \
                    -gTbAxiMstPortDataWidth=16 \
                    -gTbInitialRStallCycles=100000 -t 1ps
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
                                            -t 1ns \
                                            -GTbEnExcl=$EXCL \
                                            -GTbAxiSlvPortIdWidth=$SLV_PORT_IW \
                                            -GTbAxiMstPortIdWidth=$MST_PORT_IW \
                                            -GTbAxiSlvPortMaxUniqIds=$MAX_UNIQ_SLV_PORT_IDS \
                                            -GTbAxiSlvPortMaxTxnsPerId=5
                                else
                                    call_vsim tb_axi_iw_converter \
                                            -t 1ns \
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
                                    -t 1ns \
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
        axi_xbar)
            # Sweep 1: vary exclusive-access and unique-id handling.
            for NumMst in 1 6; do
                for NumSlv in 1 8; do
                    for Atop in 0 1; do
                        for Exclusive in 0 1; do
                            for UniqueIds in 0 1; do
                                call_vsim tb_axi_xbar -gTbNumMasters=$NumMst -gTbNumSlaves=$NumSlv \
                                        -gTbEnAtop=$Atop -gTbEnExcl=$Exclusive \
                                        -gTbUniqueIds=$UniqueIds
                            done
                        done
                    done
                done
            done
            # Sweep 2: vary ID-width usage, data width and pipelining.
            for GEN_ATOP in 0 1; do
                for NUM_MST in 1 6; do
                    NUM_SLV=9
                    MST_ID=5
                    # Sweep both IdUsed < IdWidth (3) and IdUsed == IdWidth (5), as the equal-width
                    # case exercises a distinct code path in the ID handling.
                    for MST_ID_USE in 3 5; do
                        for DATA_WIDTH in 64 256; do
                            for PIPE in 0 1; do
                                call_vsim tb_axi_xbar -t 1ns \
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
            ;;
        axi_to_mem_banked)
            for MEM_LAT in 1 2; do
                for BANK_FACTOR in 1 2; do
                    for NUM_BANKS in 1 2 ; do
                        for AXI_DATA_WIDTH in 64 256 ; do
                            ACT_BANKS=$((2*$BANK_FACTOR*$NUM_BANKS))
                            MEM_DATA_WIDTH=$(($AXI_DATA_WIDTH/$NUM_BANKS))
                            call_vsim tb_axi_to_mem_banked \
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
        axi_lite_dw_converter)
            for DWSLV in 32 64 128; do
                for DWMST in 16 32 64; do
                    call_vsim tb_axi_lite_dw_converter -gTbAxiDataWidthSlv=$DWSLV -gTbAxiDataWidthMst=$DWMST
                done
            done
            ;;
        *)
            call_vsim tb_$1 -t 1ns
            ;;
    esac
}

# Parse arguments.
tests=()
while (( "$#" )); do
    case "$1" in
        --random-seed)
            SEEDS+=(random)
            shift;;
        --list)
            LIST_ONLY=1
            shift;;
        -*) # unsupported flag (any dash-prefixed token not matched above)
            echo "Error: Unsupported flag '$1'." >&2
            exit 1;;
        *) # positional argument: a test name
            tests+=("$1")
            shift;;
    esac
done

if [ ${#tests[@]} -eq 0 ]; then
    while IFS=  read -r -d $'\0'; do
        tb_name="$(basename -s .sv $REPLY)"
        dut_name="${tb_name#tb_}"
        tests+=("$dut_name")
    done < <(find "$ROOT/test" -name 'tb_*.sv' -a \( ! -name '*_pkg.sv' \) -print0)
fi

for t in "${tests[@]}"; do
    exec_test $t
done

# A shard that matches no config at all (e.g. more shards than a test has configs) must fail
# loudly instead of passing as a vacuously green CI job.
if (( ! LIST_ONLY && NUM_EXECUTED == 0 )); then
    echo "Error: no simulations executed on this shard (shard $SHARD_INDEX of $SHARD_TOTAL)." >&2
    exit 1
fi
