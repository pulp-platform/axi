# Active read byte enables

axi_to_detailed_mem currently emits the unrelated W-channel strobe for a read.
Generate the active bytes from the actual read beat instead. Keep W strobes for
writes. The output request/bank response protocol remains unchanged.
Read strobes are useful to downstream bridges that must avoid side effects on
inactive banks. They do not by themselves suppress inactive memory requests.
This is separate from #427's already merged response-error reduction fix.

Base AXI: `d436bd4936ba1c49cd87521df54580c5159114d3` (master).
Base register_interface: `d6e1d4cdaab7870f4faf3f88a1c788eaf5ac129d` (master).
AXI's actual declared common_cells revision is
`db42769334b4589b4b3fc671b34513bdb98be565`.
The bridge additionally uses common_cells 1.39.0
`9ca8a7655f741e7dd5736669a20a301325194c28` for its unchanged legacy cells.
There are no dependency upgrades. The two generations use different cell names.
No tech cell is instantiated by the tested hierarchy.

The same test covers 96 reads: byte counts 1/2/4/8, all offsets 0..7,
and INCR lengths 1/2/4, with R backpressure. Its address-interval oracle does
not use DUT strobes or axi_pkg byte-range helpers. The first unaligned beat
ends at the transfer-size boundary; later beats start on that boundary.
The test also covers all 256 write strobes, write data, IDs, responses and LAST.
The unrelated W strobe remains 0xA5 during reads.
VCS W-2024.09-SP1 runs use a 2 ms HDL deadline and 60 s wall limit.
Every accepted run requires a single DONE, zero errors, normal finish and no
assertion/deadline/control errors. A nonzero test error count is failure even
if simv exits zero. No assertions are disabled.

| Mode | Checks | Original errors | Mask only errors | Both fixes errors |
| --- | ---: | ---: | ---: | ---: |
| Direct actual memory converter | 5476 | 448 | 0 | not needed |
| Actual full register bridge | 52420 original, 52240 both | 588 | 140 | 0 |

The bridge's check count decreases because inactive-bank MMIO transactions no
longer reach the peer. All 352 input cases and all independent expectations
remain identical. The direct-memory mode checks byte masks/data/responses;
it does not claim that axi_to_detailed_mem suppresses inactive-bank requests.
The register mode uses a side-effect-counting MMIO peer after the actual bridge.

Separate actual generic DC `compile -no_map` checks expose all module ports.
Both versions have zero latches, combinational loops, multiple drivers,
unexplained cells or final blackboxes. This is not technology timing or area signoff.

| Hierarchy | Original flip-flops/cells | Candidate flip-flops/cells |
| --- | ---: | ---: |
| Full axi_to_detailed_mem | 589 / 7632 | 581 / 8099 |
| Full axi_to_reg_v2 | 1095 / 11653 | 1087 / 12118 |

Set `AXI`, `CC2`, `CC1`, and `REG` to the exact inputs stated above.
Set `TEST` to this public test file. Use independent output directories and fixed
inputs for every comparison. The following compiles the direct mode. The bridge
mode adds the shown legacy cells and register sources and omits DIRECT_MEMORY.

```bash
mkdir run-read-banks
cd run-read-banks
sources=("$CC2/src/cc_pkg.sv" "$AXI/src/axi_pkg.sv" "$AXI/src/axi_intf.sv")
for cell in cc_fifo cc_stream_fifo cc_stream_mux cc_stream_fork \
            cc_stream_fork_dynamic cc_stream_join_dynamic cc_stream_join; do
  sources+=("$CC2/src/$cell.sv")
done
# Direct-memory mode:
timeout 180 vcs -full64 -sverilog -timescale=1ns/1ps +lint=all \
  +define+DIRECT_MEMORY "+incdir+$CC2/include+$AXI/include" \
  "${sources[@]}" "$AXI/src/axi_to_detailed_mem.sv" "$TEST" \
  -top tb_axi_narrow_read_banks -o simv -l compile.log
timeout 60 ./simv -l run.log
```

For the bridge mode, retain the same `sources` and add:

```bash
sources+=("$CC1/src/cf_math_pkg.sv")
for cell in lzc rr_arb_tree stream_arbiter_flushable stream_arbiter \
            spill_register_flushable spill_register; do
  sources+=("$CC1/src/$cell.sv")
done
for cell in periph_to_reg reg_demux reg_mux; do
  sources+=("$REG/src/$cell.sv")
done
timeout 180 vcs -full64 -sverilog -timescale=1ns/1ps +lint=all \
  "+incdir+$CC2/include+$CC1/include+$AXI/include+$REG/include" \
  "${sources[@]}" "$AXI/src/axi_to_detailed_mem.sv" \
  "$REG/src/axi_to_reg_v2.sv" "$TEST" \
  -top tb_axi_narrow_read_banks -o simv -l compile.log
timeout 60 ./simv -l run.log
```

Keep the same test and dependencies when comparing original and candidate DUT
files. The original files come from the stated bases. The two changes must be
selected independently for the original/mask-only/both bridge comparison.

AI assistance: OpenAI Codex assisted implementation, test and validation.
