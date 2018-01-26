#!/bin/bash
# Copyright (c) 2018 ETH Zurich, University of Bologna
# All rights reserved.
#
# This code is under development and not yet released to the public.
# Until it is released, the code is under the copyright of ETH Zurich and
# the University of Bologna, and may contain confidential and/or unpublished
# work. Any reuse/redistribution is strictly forbidden without written
# permission from ETH Zurich.
#
# Fabian Schuiki <fschuiki@iis.ee.ethz.ch>

set -e
ROOT=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)

[ ! -z "$VLOG" ] || VLOG="synopsys dc_shell -64"

cat "$ROOT"/scripts/synth.tcl | $SYNOPSYS_DC | tee synth.log 2>&1
! grep -i "error:" synth.log
