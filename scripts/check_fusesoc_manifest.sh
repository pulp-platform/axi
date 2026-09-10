#!/bin/bash
# Copyright (c) 2026 ETH Zurich, University of Bologna
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
# - Chen Wu <chenwu@iis.ee.ethz.ch>
#
# Check that the FuseSoC core file stays in sync with the Bender manifest.
# Two invariants are enforced:
#   1. Every source file Bender lists for this package (simulation and test
#      targets) is referenced in the .core file.
#   2. Every file referenced in the .core file exists on disk.

set -euo pipefail
cd "$(dirname "$0")/.."

CORE_FILE=axi.core

bender_files=$(bender script flist --relative-path --no-deps -t simulation -t test | sed '/^$/d' | sort -u)
core_files=$(grep -oE '(src|test|include)/[A-Za-z0-9_./-]+\.svh?' "$CORE_FILE" | sort -u)

ret=0

missing_in_core=$(comm -23 <(echo "$bender_files") <(echo "$core_files"))
if [ -n "$missing_in_core" ]; then
    echo "ERROR: listed in Bender.yml but missing from $CORE_FILE:" >&2
    echo "$missing_in_core" >&2
    ret=1
fi

for f in $core_files; do
    if [ ! -f "$f" ]; then
        echo "ERROR: listed in $CORE_FILE but does not exist: $f" >&2
        ret=1
    fi
done

if [ "$ret" -eq 0 ]; then
    echo "$CORE_FILE is in sync with Bender.yml"
fi
exit "$ret"
