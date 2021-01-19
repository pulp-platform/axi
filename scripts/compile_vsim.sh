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

set -e

[ ! -z "$VSIM" ] || VSIM=vsim

bender script vsim -t test \
    --vlog-arg="-svinputport=compat" \
    --vlog-arg="-override_timescale 1ns/1ps" \
    --vlog-arg="-suppress 2583" \
    > compile.tcl
echo 'return 0' >> compile.tcl

# Add `-lint -pendanticerrors` flags only for the files in this repository.
# Patching the compile script in this way is quite ugly, maybe there should be a Bender command to
# add arguments just for certain targets.
for x in axi_pkg; do
  # Adapted from https://unix.stackexchange.com/a/200610.
  POSIXLY_CORRECT=1 awk -v N=6 "
    BEGIN{N--}
    NR > N {
      if (/.*src\/$x\.sv/)
        print \"    -lint -pedanticerrors \\\\\"
      print l[NR % N]
    }
    {l[NR % N] = \$0}
    END{
      for (i = NR > N ? NR - N + 1 : 1; i <= NR; i++) print l[i % N]
    }" < compile.tcl > compile.patched.tcl
  mv compile{.patched,}.tcl
done

$VSIM -c -do 'exit -code [source compile.tcl]'
