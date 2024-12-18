# Changelog
All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](http://keepachangelog.com/en/1.0.0/)
and this project adheres to [Semantic Versioning](http://semver.org/spec/v2.0.0.html).


## Unreleased

## 0.39.6 - 2024-12-04
### Added
- Support connectivity in `axi_intercon_gen`. #351
- Add `iomsb` function to avoid underflow in array lengths to `axi_pkg`. #355

### Fixed
- Make the case statements in `axi_dw_upsizer` unique. Add default cases to prevent simulator warnings. #348
- Fix write channel assertions in `axi_rw_split`. #357
- Tie unused `demux` port in pass-through termination in `axi_isolate`. #359

### Changed
- Improve VCS and Verilator support treewide. #358
- Update `common_verification` to `v0.2.4` to include Verilator fixes.

## 0.39.5 - 2024-10-24

### Fixed
- Disabled the interface variant of `axi_xbar_unmuxed` for VCS, as VCS does not support multi-dimensional arrays of interfaces yet.

### Changed
- `axi_id_serialize`: Revert #342 to fix boot problems of CVA6 in Cheshire.

## 0.39.4 - 2024-07-25 (Yanked 2024-10-23)
### Added
- `axi_sim_mem`: Increase number of request ports, add multiport interface variant.
- `axi_bus_compare`: Optionally consider AXI `size` field to only compare used data.
- `AXI_BUS_DV`: Add property checking that bursts do not cross 4KiB page boundaries.
- Add `axi_xbar_unmuxed`: Partial crossbar with unmultiplexed mst_ports.

### Fixed
- `axi_bus_compare`: Fix mismatch detection.
- `axi_to_detailed_mem`: Only respond with `exokay` if `lock` was set on the request.
  Bump `common_cells` for `mem_to_banks` fix.
- `axi_dw_downsizer`: Fix `i_forward_b_beats_queue` underflow.
- `axi_atop_filter`: Add reset state to internal FSM to avoid simulation bug in XSIM.
- `axi_test`: Ensure random requests do not cross 4KiB page boundaries.

### Changed
- `axi_id_serializer`: Change internal design (and behavior) for simpler code, less hardware, and
  less stalling.

`v0.39.4` is fully **backward-compatible** to `v0.39.3`.

## 0.39.3 - 2024-05-08
### Added
- `axi_sim_mem`: Allow response data for uninitialized region to have configurable defined value.
- `axi_test`: add `clear_memory_regions` to `axi_rand_master`.
- `axi_test`: Add `add_traffic_shaping_with_size` to `axi_rand_master` to allow for traffic shaping
  with a custom size.

### Changed
- `axi_pkg`: Adjust `LatencyMode` parameter of `xbar_cfg_t` to bit vector from `xbar_pipeline_e`
  enum to allow custom configurations.

`v0.39.3` is fully **backward-compatible** to `v0.39.2`.

## 0.39.2 - 2024-03-13

### Added
- `axi_interleaved_xbar`: An experimental crossbar extension interleaving memory transfers over #334
  subordinate devices. ***Use at your own risk***.
- `axi_zero_mem`: Implementing *\dev\zero* function for AXI. #334

### Fixed
- `axi_to_detailed_mem`: VCS crashed on default parameters 0, changed them to 1 #334
- `axi_to_mem`: Add missing testmode pins #327
- `axi_sim_mem`: Fix byte calculation in R and W forks #331

`v0.39.2` is fully **backward-compatible** to `v0.39.1`.

## 0.39.1 - 2023-09-05

### Added
- `axi_cdc`: Add `SyncStages` parameter.
- `axi_to_mem_interleaved`: Add interface variant.
- `axi_burst_splitter`: Expose `id_queue`'s `FULL_BW` parameter.
- `axi_chan_compare`: Add parameter to allow reordered transactions.
- Add `AXI_HIGHLIGHT` macro to highlight AXI signals.
- Add flat port instantiation macros.

### Fixed
- `axi_test`: Avoid false negatives for misaligned reads in `axi_scoreboard`.
- `axi_to_detailed_mem`: Ensure proper propagation or `err` and `exokay` signals.

## 0.39.0 - 2023-07-20

### Added
- Synthesizable IPs:
  - `axi_bus_compare` and `axi_slave_compare`; two synthesizable verification IPs meant to be used
    to compare two AXI buses on an FPGA.
  - `axi_lite_from_mem` and `axi_from_mem` acting like SRAMs making AXI4 requests downstream.
  - `axi_lite_dw_converter`: Convert the data width of AXI4-Lite transactions. Emits the
     appropriate amount of downstream transactions to perform the whole requested access.
  - `axi_rw_join` and `axi_rw_split` to split/join the read and write channels of an AXI bus.
- `CT`-macros allowing to instantiate AXI structs with custom channel type names.
- `axi_pkg': Add documentation to `xbar_cfg_t`.
- Testbench IPs:
  - `axi_chan_compare.sv`: Non-synthesizable module comparing two AXI channels of the same type
  - Add `axi_file_master` to `axi_test`, allowing file-based AXI verification approaches.
  - Add `#_width` functions to `axi_test` returning the width of the AXI channels.

### Changed
- Synthesizable IPs:
  - `axi_demux`: Replace FIFO between AW and W channel by a register plus a counter.  This prevents
    AWs from being issued to one master port while Ws from another burst are ongoing to another
    master port.  This is required to prevents deadlocks due to circular waits downstream. Removes
    `FallThrough` parameter from `axi_demux`.
  - Split the `axi_demux` logic and timing decoupling. A new module called `axi_demux_simple` contains
    the core logic.
  - `axi_dw_downsizer` uses `axi_pkg::RESP_EXOKAY` as a default value.
  - Simplify the `casez` in `axi_id_remap`.
  - Add optional explicit mapping to the `axi_id_serialize` module.
  - Expand `axi_to_mem` to `axi_to_detailed_mem` exposing all of AXI's side-signals; namely `id`, `user`,
    `cache`, `prot`, `qos`, `region`, `atop`. Add possibility to inject `err` and `exokay`.
  - `axi_xbar`: Add parameter `PipelineStages` to `axi_pkg::xbar_cfg_t`. This adds `axi_multicuts`
    in the crossed connections in the `xbar` between the *demuxes* and *muxes*. Improve inline
    documentation.
  - Move `mem_to_banks` to `common_cells`.
- `axi_pkg`: Improve for better compatibility with *Vivado*.
- `axi_test:
  - `axi_lite_rand_slave`: `R` response field is now randomized.
  - Remove excessive prints from random master and slave.
  - Properly size-align the address.
- `axi_pkg`: Define `localparams` to define AXI type widths.
- Update `common_cells` from version `v1.26.0` to `v1.27.0`.
- Tooling:
  - Use `pulp-platform/pulp-actions/gitlab-ci@v2` in the GitHub CI to communicate with the internal CI.
  - Bump `DC Shell version` from `2019.12` to `2022.03`
  - No longer check *ModelSim* versions `10.7e` and `2021.3`, add `2022.3`.
  - More thorough verification runs for the `xbar`.
  - Start transitioning from shell script to Makefile to run simulations.
- Use `scripts/update_authors` to update authors, slight manual fixes performed.

### Fixed
- `axi_to_mem_banked`: Reduce hardware by properly setting `UniqueIds`.
- `axi_to_mem_interleaved` and `axi_to_mem_split` properly instantiates a demultiplexer now.
  Adds `test_i` port for DFT.

### Breaking Changes
There are breaking changes between `v0.38.0` and `v0.39.0`:
- `axi_demux`: `FallThrough` parameter was removed.
- `axi_xbar`: `axi_pkg::xbar_cfg_t` added `PipelineStages` parameter.
- `axi_to_mem_interleaved` and `axi_to_mem_split`: Added `test_i` input port.

## 0.38.0 - 2022-09-28

### Added
- Add `axi_dumper` and `axi_dumper_interpret` script to dump log from an AXI bus for debugging
  purposes.
- Add FuseSoC and Vivado XSIM limited test to CI
- `assign.svh`: Add macros to assign flat buses using the Vivado naming style.
- `axi_lfsr` and `axi_lite_lfsr`: Add AXI4 and AXI4 Lite LFSR Subordinate devices.
- `axi_xp`: Add crosspoint with homomorphous slave and master ports.

### Changed
- Improve compatibility with FuseSoC
- Improve compatibility with Vivado XSIM
- Performance improvements to `axi_to_mem`
- Use `scripts/update_authors` to update authors, slight manual fixes performed.

`v0.38.0` is fully **backward-compatible** to `v0.36.0` and `v0.37.0`.


## 0.37.0 - 2022-08-30

### Added
- `axi_fifo`: Inserts a FIFO into all 5 AXI4 channels; add module and its testbench
- `axi_test`: Add `mapped` mode to the random classes as well as additional functionality to the
  scoreboard class.
- `axi_throttle`: Add a module that limits the maximum number of outstanding transfers sent to the
  downstream logic.
- `axi_to_mem`: AXI4+ATOP slave to control on chip memory.
- `axi_to_mem_banked`:  AXI4+ATOP slave to control on chip memory, with banking support, higher
  throughput than `axi_to_mem`.
- `axi_to_mem_interleaved`: AXI4+ATOP slave to control on chip memory, interleaved to prevent
  deadlocks.
- `axi_to_mem_split`: AXI4+ATOP slave to control memory protocol interconnect.
- `Bender`: Add dependency `tech_cells_generic` `v0.2.2` for generic SRAM macro for simulation.

### Changed
- `axi_demux`: Add module docstring
- `axi_sim_mem`: Add the capability to emit read and write errors
- `Bender`: Update dependency `common_cells` to `v1.26.0` from `v1.21.0` (required by
  `axi_throttle`)
- Remove `docs` directory, move content to `doc` folder. `docs` is automatically created and
  populated during the CI run.
- Update vsim version to `2021.3` in CI, drop test for `2020.1` and `2021.1`

### Fixed
- `axi_lite_demux`: Improve compatibility with vsim version 10.7b.
- `axi_lite_mux`: Reduce complexity of W channel at master port by removing an unnecessary
  multiplexer.

`v0.37.0` is fully **backward-compatible** to `v0.36.0`.


## 0.36.0 - 2022-07-07

### Added
- Add Monitor modport to `AXI_BUS`, `AXI_LITE`, and `AXI_LITE_DV` interfaces.


## 0.35.3 - 2022-05-03

### Fixed
- `axi_demux`: Eliminate unnecessary stalls of AW channel when the AR channel has reached its
  maximum number of transactions.  Prior to this fix, `axi_demux` would always stall AWs while read
  transactions were at their maximum (that is, while `MaxTrans` read transactions were outstanding).
  However, this stall is only required when the AW that is being handled by `axi_demux` is an atomic
  operation (ATOP) that entails an R response.  This fix therefore removes unnecessary stalls as
  well as an unnecessary dependency between reads and writes.  The integrity of data or transactions
  was not affected by this problem.


## 0.35.2 - 2022-04-14

### Fixed
- `axi_lite_mux_intf`: Fix type of `slv` and `mst` interface ports; they were `AXI_BUS` instead of
  `AXI_LITE`.
- `axi_xbar_intf`: Fix order of parameters.  Prior to this fix, the `CONNECTIVITY` parameter was
  defined using the `Cfg` parameter before the `Cfg` parameter was defined.
- `axi_test::axi_rand_master`: Improve compatibility with simulators by changing an implication
  inside an assertion to a conditional assertion.


## 0.35.1 - 2022-03-31

### Fixed
- `axi_demux` and `axi_lite_demux`: Add missing spill registers for configurations with a single
  master port.
- `axi_demux_intf`: Add missing parameter (`ATOP_SUPPORT`) to optionally disable support for atomic
  operations.
- `axi_mux` and `axi_lite_mux`: Add missing spill registers for configurations with a single slave
  port.
- `axi_lite_mux_intf`: Add missing parameter values on the internal `axi_lite_mux` instance
  (`axi_req_t` and `axi_resp_t`).
- `axi_sim_mem`: Propagate the AR channel's user signal correctly to the monitor.


## 0.35.0 - 2022-03-11

### Added
- `axi_sim_mem`: Add monitoring interface to observe the point of coherency between the write and
  the read channel.

### Fixed
- `axi_sim_mem`: Keep R response stable while not accepted.


## 0.34.0 - 2022-03-09

### Added
- `axi_demux` and `axi_isolate`: Add parameter `AtopSupport` to optionally disable the support for
  atomic operations (ATOPs).  This parameter defaults to `1'b1`, i.e., ATOPs are supported.
  Therefore, this change is backward-compatible.
- `axi_isolate`: Add parameter `TerminateTransaction` to optionally respond to transactions during
  isolation.  This parameter defaults to `1'b0`, i.e., transactions do not get responses.
  Therefore, this change is backward-compatible.
- `axi_xbar`: Add `Connectivity` parameter to enable the implementation of partially-connected
  crossbars.  This parameter defaults to `'1`, i.e., every slave port is connected to every master
  port.  Therefore, this change is backward-compatible.
- `axi_test`: Add monitor class `axi_monitor`.
- `axi_test::axi_driver`: Add monitor tasks.

### Changed
- `axi_isolate`: Add parameters for the address, data, ID, and user signal width.  This is required
  for the implementation of the `TerminateTransaction` parameter (see *Added* section).  This change
  is **backward-incompatible** for all instances of `axi_isolate` outside this repository.  Users
  must update all instances of `axi_isolate` in their code.  The interface variant is not affected
  and remains backward-compatible.


## 0.33.1 - 2022-02-26

### Fixed
- `axi_xbar_intf`: Add missing `ATOPS` parameter to optionally disable the support of atomic
  operations (introduced in v0.25.0 for `axi_xbar`).  The default value of the added parameter makes
  this fix backward-compatible.


## 0.33.0 - 2022-02-21

### Added
- Add `axi_sim_mem_intf` interface variant of `axi_sim_mem`.

### Fixed
- `axi_cdc`: Improve compatibility with VCS by restricting a QuestaSim workaround to be used only
  for QuestaSim (issue #207).
- `axi_id_remap`: Improve compatibility with Verilator by excluding `assert`s for that tool.
- `axi_lite_demux`: Improve compatibility with VCS (issue #187 reported for `axi_demux`, which was
  fixed in v0.29.2).
- `axi_xbar`: Improve compatibility with VCS by adding VCS-specific code that does not use constant
  function calls (#208).


## 0.32.0 - 2022-01-25

### Changed
- `axi_atop_filter`, `axi_burst_splitter`, `axi_cut`, `axi_delayer`, `axi_demux`, `axi_err_slv`,
  `axi_isolate`, `axi_lite_demux`, `axi_lite_mux`, `axi_lite_to_axi`, and `axi_lite_xbar`,
  `axi_multicut`, `axi_serializer`, `axi_sim_mem`:  Prefix `req_t` and `resp_t` type parameters with
  `axi_`.  This prevents type collisions in tools that have problems with correct type resolution
  and isolation.  This change is **backward-incompatible** for all instances of the listed modules
  outside this repository.  Users must update all instances of the listed modules in their code.
  Interface variants are not affected and remain backward-compatible.


## 0.31.1 - 2022-01-17

### Fixed
- `axi_xbar`: Fix signal width for single master port.  Before this fix, a crossbar instantiated
  with a single master port would contain arrays with incorrect dimensions.


## 0.31.0 - 2021-12-07

### Added
- Add three modules to convert between any two AXI ID widths under many different concurrency
  requirements:
  - `axi_iw_converter` is the top-level module that converts between any two AXI ID widths with all
    supported parameters.  It upsizes IDs by extending the MSBs with zeros and joins two interfaces
    with identical ID widths.  For downsizing IDs, it instantiates one of the following two modules:
  - `axi_id_remap` remaps AXI IDs from wide IDs at the slave port to narrower IDs at the master
    port without serializing transactions.
  - `axi_id_serialize` reduces AXI IDs by serializing transactions when necessary.


## 0.30.0 - 2021-12-01

### Added
- Add `axi_lite_xbar_intf` interface variant of `axi_lite_xbar`.

### Fixed
- `axi_lite_demux`: Improve compatibility with new version of QuestaSim's optimizer (`vopt`).
  Before this workaround, QuestaSim 2021.1 could segfault on instances of `axi_lite_demux`.


## 0.29.2 - 2021-11-12

### Fixed
- `axi_demux`: Improve compatibility with VCS (#187).  The workaround of #169 was not compatible
  with VCS 2020.12.  That workaround is now only active if `TARGET_VSIM` is defined.
- `axi_dw_downsizer` and `axi_dw_upsizer` (part of `axi_dw_converter`): Avoid latch inference on the
  Mentor Precision synthesis tool.
- `axi_lite_cdc_src_intf`: Fix `_i` and `_o` suffixes in instantiation of `axi_cdc_src`.
- `axi_test::axi_rand_slave`: Improve compatibility with VCS (#175).
- `axi_test::axi_scoreboard`: Add default value to parameters to improve compatibility with some
  tools.


## 0.29.1 - 2021-06-02

### Fixed
- `axi_lite_to_apb_intf`: Add missing parameters, which were added to `axi_lite_to_apb` in v0.28.0.


## 0.29.0 - 2021-05-06

### Changed
- `axi_xbar` and `axi_demux`: Add support for unique IDs by adding a `UniqueIds` parameter to both
  modules (#172).  If you can guarantee that the ID of each transaction is always unique among all
  in-flight transactions in the same direction, setting the `UniqueIds` parameter to `1'b1`
  simplifies the demultiplexer (see documentation of `axi_demux` for details).  This change is
  backward-compatible on `axi_demux` (because the default value of the new parameter is `1'b0`).
  As `axi_xbar` is configured with the `xbar_cfg_t` `struct`, this change is *not
  backward-compatible* for `axi_xbar` (except for `xbar_cfg_t`s initialized with a `default` part).

### Fixed
- `axi_test::axi_rand_master`: Refactor ID legalization into common function to simplify the
  implementation and remove redundant code.  No known functional bug was fixed, but the correctness
  of the refactored code can be asserted more easily.


## 0.28.0 - 2021-04-15

### Added
- Add source- and destination-clock-domain "halves" for the clock domain crossing (CDC):
  `axi_cdc_src` and `axi_cdc_dst`.  This is implemented by refactoring the `axi_cdc` module, so the
  implementation is reused from the existing `axi_cdc` module.  To avoid code duplication, `axi_cdc`
  now instantiates an `axi_cdc_src` connected to an `axi_cdc_dst`.

### Changed
- `axi_lite_to_apb`: Make pipeline registers on request and response path optional (can be enabled
  with the new `PipelineRequest` and `PipelineResponse` `parameter`s), and disable those pipeline
  registers by default.

### Fixed
- `axi_demux`: Improve compatibility with new version of QuestaSim's optimizer (`vopt`) (#169).
  Before this workaround, QuestaSim 2020.2 and 2021.1 could segfault on instances of `axi_demux`.


## 0.27.1 - 2021-02-01

### Fixed
- `axi_dw_downsizer` and `axi_dw_upsizer` (part of `axi_dw_converter`): Fix declaration order of
  `w_req_t`, `w_req_d`, and `w_req_q` to remove problematic forward references.
- FuseSoC: Fix version of `common_cells` (`1.21.0`).


## 0.27.0 - 2021-02-01

### Added
- `assign.svh`: Add macros for assigning between AXI-Lite `struct`s, both inside a process
  (`AXI_LITE_SET_*_STRUCT`) and outside a process (`AXI_LITE_ASSIGN_*_STRUCT`).  This is safer than
  assigning `struct`s with a simple `=`, because the macros assign individual fields.
- `typedef.svh`: Add `AXI_TYPEDEF_ALL` and `AXI_LITE_TYPEDEF_ALL` macros for defining all channels
  and request/response `struct`s of an AXI4+ATOPs and an AXI4-Lite interface, respectively, in a
  single macro call.
- `axi_test::axi_rand_slave`: Add parameter `RAND_RESP`, which enables randomization of the `resp`
  field in B and R beats.

### Changed
- `axi_test::axi_rand_master`: Randomize the QoS field.
- Update `common_verification` dependency to `0.2.0`, which has been released for more than a year.
- Update `common_cells` dependency to `1.21.0` to align on version `0.2.0` of the
  `common_verification` dependency.  This includes version `1.20.1` of `common_cells`, which fixes
  an out-of-bounds index in `axi_burst_splitter` (#150).


## 0.26.0 - 2021-01-19

### Added
- Add infinite, simulation-only memory `axi_sim_mem`.
- `assign.svh`: Add macros for assigning between `struct`s, both inside a process
  (`AXI_SET_*_STRUCT`) and outside a process (`AXI_ASSIGN_*_STRUCT`).  This is safer than assigning
  `struct`s with a simple `=`, because the macros assign individual fields.  (Fields that mismatch
  between two `struct`s, e.g., due to different `user` signal widths, should, and in some cases
  must, be still assigned separately.)

### Changed
- Rename the following classes in `axi_test` to follow the convention that all user-facing objects
  in this repository start with `axi_`:
  - `rand_axi_lite_master` to `axi_lite_rand_master`,
  - `rand_axi_lite_slave` to `axi_lite_rand_slave`,
  - `rand_axi_master` to `axi_rand_master`, and
  - `rand_axi_slave` to `axi_rand_slave`.


## 0.25.0 - 2021-01-14

### Added
- `axi_xbar`: Add parameter to disable support for atomic operations (`ATOPs`).

### Changed
- `AXI_BUS`, `AXI_BUS_ASYNC`, `AXI_BUS_DV`, `AXI_LITE`, and `AXI_LITE_DV`: Change type of every
  parameter from `int` to `int unsigned`.  An unsigned type is more appropriate, because none of
  those parameters can actually take a negative value, and it improves compatibility with some
  tools.
- `axi_test::rand_axi_lite_slave` and `axi_test::rand_axi_lite_master`: Change type of address and
  data width parameters (`AW` and `DW`) from `int` to `int unsigned`.  Same rationale as for
  `AXI_BUS` (et al.) above.

### Fixed
- `axi_demux`: Break combinatorial simulation loop.
- `axi_xbar`: Improve compatibility with vsim version 10.6c (and earlier) by introducing a
  workaround for a tool limitation (#133).
- `tb_axi_lite_regs`: Removed superfluous hardcoded assertion.
- Improve compatibility with Vivado XSim by disabling formal properties in `axi_demux`,
  `axi_err_slv`, and `axi_xbar` if `XSIM` is defined.


## 0.24.2 - 2021-01-11

### Changed
- `axi_test::rand_axi_lite_master` and `axi_test::rand_axi_lite_slave`: Specify default values for
  parameters to improve compatibility with tools that require a default value for every parameter.

### Fixed
- `axi_lite_demux`: Move `typedef` out of `generate` block to improve compatibility with VCS.
- `axi_test::rand_axi_master` and `axi_test::rand_axi_slave`: Fix call to `randomize` function for
  class variables.  Prior to this fix, the `std::randomize()` function was used for three class
  variables, but class variables must use the `.randomize()` member function.


## 0.24.1 - 2020-11-04

### Changed
- Update `common_cells` dependency to `1.20.0` to fix file order in IPApproX.

### Fixed
- `doc/axi_lite_mailbox`: Fix position of `RFIFOL` and `WFIFOL` in `STATUS` register.
- IPApproX:
  - Add missing link against `common_cells_lib`.
  - Fix include path for `common_cells`.
  - Fix version specification of `common_verification`.


## 0.24.0 - 2020-10-27

### Added
- `axi_pkg`: Add function that defines response precedence.

### Changed
- `axi_dw_downsizer` and `axi_dw_upsizer`: Pipeline injection of atomic AWs into the AR channel to
  shorten the critical path.

### Fixed
- `axi_dw_downsizer` and `axi_dw_upsizer`: Improve portability of bit slice assignment constructs.
- `axi_dw_downsizer`:
  - Forward worst response among split transactions.
  - Fix overflow of B forward FIFO.
- `axi_test`: Remove minimal length constraint from `rand_atop_burst`.


## 0.23.2 - 2020-09-14

### Fixed
- `ips_list.yml`: Add missing `common_verification` dependency.


## 0.23.1 - 2020-06-19

### Fixed
- `axi_lite_demux_intf`: Fix passing of `req_t` and `resp_t` parameters to `axi_lite_demux`.
- `axi_lite_xbar`: Add missing `slv_a{w,r}_cache_i` connections on `axi_lite_to_axi` instance.


## 0.23.0 - 2020-05-11

### Added
- `axi_lite_regs`: Add memory-mapped registers with AXI4-Lite slave port and the option to make
  individual bytes read-only.

### Changed
- Interfaces `AXI_LITE` and `AXI_LITE_DV`: add `aw_prot` and `ar_prot` signals.
  - The `AXI_LITE_ASSIGN*` and `AXI_LITE_SET*` macros (in `include/axi/assign.svh`) have been
    updated to include the two new interface signals.
  - `axi_test::axi_lite_driver`: A new `prot` function argument has been added to the `send_aw`,
    `send_ar`, `recv_aw`, and `recv_ar` functions.
  - `axi_test::rand_axi_lite_master`:
    - A new `w_prot` and `r_prot` function argument has been added to the `write` and `read`
      function, respectively.  The new arguments have a default value of `'0`.
    - The `send_aws` and the `send_ars` function now randomizes the `prot` signal of each AW and AR,
      respectively.
  - `axi_test::rand_axi_slave`: Display `prot` signal (but otherwise still ignore it).

### Fixed
- `rand_axi_master` (in `axi_test`): Another fix to respect burst type restrictions when emitting
  ATOPs.


## 0.22.1 - 2020-05-11

### Fixed
- `rand_axi_master` (in `axi_test`): Respect burst type restrictions when emitting ATOPs.


## 0.22.0 - 2020-05-01

### Added
- `axi_pkg`: Add `bufferable` and `modifiable` helper functions.
- `axi_dw_converter`: Add support for single-beat *fixed* bursts in the downsizer and for *fixed*
  bursts of any length in the upsizer.

### Changed
- `axi_dw_downsizer` (part of `axi_dw_converter`): Downsize regardless of the *modifiable* bit of
  incoming transactions.  Previously, non-*modifiable* transactions whose attributes would have to
  be modified for downsizing were rejected with a slave error.  As of this change, transactions are
  downsized and their attributes modified even if their *modifiable* bit is not set.  This is
  permitted by a note in the AXI specification (page A4-65 of IHI0022H).

### Fixed
- `axi_dw_downsizer` (part of `axi_dw_converter`): Fix condition for keeping transactions that have
  a smaller `size` than the master/downstream port unmodified.


## 0.21.0 - 2020-04-27

### Added
- `axi_serializer`: serialize transactions with different IDs to the same ID.

### Changed
- `axi_modify_address`:
  - Simplify redundant `slv_resp_t` and `mst_resp_t` parameters to single `axi_resp_t` parameter.
  - Remove unnecessary `slv_a{r,w}_addr_o` outputs, which were fed back from the `slv_req_i` inputs.
    Those signals can instead be derived outside `axi_modify_address`.
- `axi_modify_address_intf`:
  - Change name of slave port to `slv` and master port to `mst` and change name of associated
    parameters to align them with repository conventions.
  - Change type of parameters to `int unsigned` because their values are unsigned.
  - Add parameters for data, ID, and user width to avoid derivation from interface, which is
    incompatible with many tools.
  - Add missing I/O suffixes to port names and align them with `axi_modify_address`.

### Fixed
- `axi_modify_address_intf`: Fix type parameters passed to actual implementation.


## 0.20.0 - 2020-04-22

### Added
- `axi_pkg`: Add `wrap_boundary` function to calculate the boundary of a wrapping burst.
- `axi_test`: The random AXI master `rand_axi_master` can now emit wrapping bursts (but does not do
  so by default).  Three new parameters control the burst types of the emitted transactions; not
  setting those parameters means the random master behaves as it did before this change.
- Interface `AXI_BUS_DV`: Add `Monitor` modport, in which all signals are inputs.
- `axi/assign.svh`: Add `AXI_ASSIGN_MONITOR` macro, which assigns an `AXI_BUS` to an
  `AXI_BUS_DV.Monitor`.
- Package `axi_test`: Add `axi_scoreboard` class, which checks that data read from a memory address
  matches data written to that address.

### Changed
- `axi_pkg`:
  - The `beat_addr` function now supports all burst types.  Due to this, the function has two new
    arguments (the length and type of the burst).
  - The `beat_upper_byte` and `beat_lower_byte` functions internally call `beat_addr`, so they have
    two new arguments as well.


## 0.19.0 - 2020-04-21

### Changed
- `axi_lite_to_axi`: Expose `AxCACHE` signals.  It is now possible to define the `cache` signal of
  AXI transactions coming out of this module by driving the added `slv_aw_cache_i` and
  `slv_ar_cache_i` inputs.  To retain the behavior prior to this change, tie those two inputs to
  zero.


## 0.18.1 - 2020-04-08

### Fixed
- `axi_modify_address`: Fix unconnected `w_valid`.
- `axi_dw_converter`: Fix internal inversion of up- and downconversion, which led to incorrect lane
  steering and serialization.
- `rand_axi_master` (in `axi_test`): In ATOP mode, this module could get stuck receiving an R beat
  when only writes (without ATOP read responses) were left to complete.  This has been fixed.
- `assign.svh`: Remove spurious semicolons.
- `axi_lite_to_apb`: Fix message of assertion checking the strobe width.


## 0.18.0 - 2020-03-24

### Added
- `axi_dw_converter`: a data width converter between AXI interfaces of any data width.  Depending on
  its parametrization, this module instantiates one of the following:
  - `axi_dw_downsizer`: a data width converter between a wide AXI master and a narrower slave.
  - `axi_dw_upsizer`: a data width converter between a narrow AXI master and a wider slave.


## 0.17.0 - 2020-03-23

### Added
- Add `axi_isolate` to isolate downstream slaves from receiving new transactions.

### Changed
- `axi_lite_to_axi`: Add mandatory `AxiDataWidth` parameter to enable fix mentioned below.

### Fixed
- Improve compatibility with Xcelium:
  - by removing unsupported hierarchical argument to `$bits()` function in `axi_lite_to_axi`;
  - by removing unsupported `struct` assignment in `axi_lite_demux`.


## 0.16.3 - 2020-03-19

### Changed
- `axi_err_slv`: Add optional parameter to define data returned by read response.  The parameter
  defaults to a 64-bit value, so buses with data width larger than or equal to 64 bit see an
  additional 32-bit value in error responses compared to the prior version.  Other than that, this
  change is fully backward compatible.


## 0.16.2 - 2020-03-16

### Fixed
- `axi_atop_filter`: Fix underflow in counter for `AxiMaxWriteTxns = 1`.


## 0.16.1 - 2020-03-13

### Fixed
- Remove whitespace in and semicolon after macro calls.
- `axi_intf`: Improve Verilator compatibility by disabling unsupported assertions.


## 0.16.0 - 2020-03-11

### Added
- `axi_cdc_intf`: Add interface variant of AXI clock domain crossing.

### Fixed
- `axi_cdc`: Remove unused global `import axi_pkg::*`.
- `axi_intf`: Remove global `import axi_pkg::*` and explicitly use symbols from `axi_pkg`.
- `axi_lite_cut_intf`: Add missing assigns to and from interface ports.
- `tb_axi_cdc`:
  - Remove global `import axi_pkg::*`.
  - Define channels with `AXI_TYPEDEF` macros instead of local `typedef`s.

### Removed
- Remove unused `AXI_ARBITRATION` and `AXI_ROUTING_RULES` interfaces.


## 0.15.1 - 2020-03-09

### Added
- `axi_intf`: Add single-channel assertions to `AXI_BUS_DV`.

### Fixed
- `axi_lite_to_apb`: Fix the interface version (`axi_lite_to_apb_intf`) to match the changes from
  version `0.15.0`.
- `axi_demux`: When `MaxTrans` was 1, the `IdCounterWidth` became 0.  This has been fixed.
- `axi_atop_filter`:
  - The master interface of this module in one case depended on `aw_ready` before applying
    `w_valid`, which is a violation of the AXI specification that can lead to deadlocks.  This issue
    has been fixed by removing that dependency.
  - The slave interface of this module could illegally change the value of B and R beats between
    valid and handshake.  This has been fixed.
- `rand_axi_master` (in `axi_test`):
  - Fix infinite wait in `send_ws` task.
  - Decouple generation of AWs from sending them.  This allows to apply W beats before or
    simultaneous with AW beats.
- `rand_axi_slave` (in `axi_test`):
  - Decouple receiving of Ws from receiving of AWs.  This allows to receive W beats independent of
    AW beats.
- Update `common_cells` to `1.16.4` to fix synthesis warning in `id_queue`.


## 0.15.0 - 2020-02-28

### Added
- `axi_burst_splitter`: Split AXI4 bursts to single-beat transactions.

### Changed
- `axi_lite_to_apb`: The `psel` field of the `apb_req_t` struct is now a single bit.  That is, every
  APB slave has its own request struct.  Accordingly, `apb_req_o` is now an array with `NoApbSlaves`
  entries.
- `axi_decerr_slv` has been replaced by a more generic `axi_err_slv`, which takes the kind of error
  as parameter.  This `axi_err_slv` no longer has a `FallThrough` parameter; instead, a response
  (i.e., B or R beat) now always comes one cycle after the AW or AR beat (as required by the AXI
  Spec) but the slave can accept a W beat in the same cycle as the corresponding AW beat.
  Additionally, `axi_err_slv` got a parameter `ATOPs` that defines if it supports atomic operations.
- `axi_to_axi_lite`: Rework module to structs and add burst support.

### Fixed
- `axi_demux`: The `case` statement controlling the counters had not been specified `unique` even
  though it qualified for it.  This has been fixed.
- `axi_lite_mux_intf`: Fix signal names in internal assignments, names of parameters of
  `axi_lite_mux` instance, and typos in assertion messages.


## 0.14.0 - 2020-02-24

### Added
- Add `axi_lite_mailbox`: AXI4-Lite mailbox.


## 0.13.0 - 2020-02-18

### Added
- `axi_xbar_intf`: Add interface variant of crossbar.

### Fixed
- `axi_atop_filter`: Fix ModelSim warnings by adding `default` statement.  The signal in the `case`
  has a single bit, and both values were correctly handled in synthesis.  However, when starting
  simulation, the signal has an undefined value, and ModelSim threw warnings that this violated the
  `unique` condition.
- `axi_demux`: Move `typedef` outside `generate` for compatibility with VCS.
- `axi_id_prepend`:
  - Fix text of some assertion messages.
  - Fix case of prepending a single-bit ID.
- `tb_axi_xbar`: Fix for localparam `AxiIdWidthSlaves` to be dependent on the number of masters.


## 0.12.0 - 2020-02-14

### Added
- `axi_lite_to_apb`: AXI4-Lite to APB4 converter.


## 0.11.0 - 2020-02-13

### Added
- `axi_cdc`: Add a safe AXI clock domain crossing (CDC) implementation.

### Changed
- The interface variants of `axi_demux` and `axi_mux` have been changed to match the convention for
  interface variants in this repository:
  - `axi_demux_wrap`: Change name to `axi_demux_intf` and change parameter names to ALL_CAPS.
  - `axi_mux_wrap`: Change name to `axi_mux_intf`, and change parameter names to ALL_CAPS.
- `axi_demux`: Default parameters to `0`.

### Fixed
- `axi_demux`: Add parameter case for `NoMstPorts == 1`.


## 0.10.2 - 2020-02-13

### Fixed
- `axi_atop_filter`: Remove unreachable `default` in `unique case` block.
- `axi_demux_wrap`: Fix signals passed to demux.
- `axi_lite_demux_intf`: Fix signal passed to demux.
- `axi_lite_mux`: Add missing declaration of `r_fifo_push`.


## 0.10.1 - 2020-02-12

### Fixed
- `axi_lite_xbar`: Fix synthesis for `NoMstPorts == 1`.


## 0.10.0 - 2020-02-11

### Added
- `axi_lite_xbar`: fully-connected AXI4-Lite crossbar.
- `axi_lite_demux`: AXI4-Lite demultiplexer from one slave port to a configurable number of master
  ports.
- `axi_lite_mux`: AXI4-Lite multiplexer from a configurable number of slave ports to one master
  port.

### Changed
- `axi_test`: Extended package with random AXI4-Lite master and slave test bench classes.


## 0.9.2 - 2020-02-11

### Fixed
- `axi_pkg`: Fix value of `CUT_ALL_PORTS` (in `xbar_latency_e`) in Vivado synthesis.


## 0.9.1 - 2020-01-18

### Fixed
- `axi_decerr_slv`: Fix parameter to be UpperCamelCase


## 0.9.0 - 2020-01-16

### Added
- `axi_test`: Constrained randomizing AXI master (`rand_axi_master`) and slave (`rand_axi_slave`).
  - `rand_axi_master` issues a configurable number of read and write transactions to configurable
    memory regions (address ranges with associated memory types) and with random properties within
    constraints (e.g., burst length, exclusive accesses, atomic operations).
  - `rand_axi_slave` responds to transactions with random delays and data.
- `axi_pkg`: AXI memory types (`mem_type_t`) and functions `get_arcache` and `get_awcache` to
  calculate `AxCACHE` bits for a given memory type.
- Add `axi_decerr_slv`.
- Add `axi_id_prepend`.
- Add fully compliant `axi_xbar`.
- Add documentation on `axi_mux`, `axi_demux` and `axi_xbar`
- Module overview to `README.md`

### Changed
- `axi_test`: The `reset` tasks in `axi_driver` and `axi_lite_driver` are now functions.
- Bump `common_cells` to `1.16.0` which contains the address decoding logic used in `axi_xbar`.

### Fixed
- `axi_intf` move import into interface bodies.
- `axi_pkg` make functions automatic, fixing a problem with Synopsys.


## 0.8.2 - 2019-12-20

### Fixed
- `src_files.yml`: Add `only_local` flag for `axi_test`.
- `axi_test`:
  - Add missing default parameters to `axi_lite_driver`.
  - Move wildcard import from `axi_test` into package to prevent pollution of compilation unit.


## 0.8.1 - 2019-12-19

### Added
- `axi_pkg`: Functions to calculate addresses and byte positions within a beat.


## 0.8.0 - 2019-12-19

All modules have been changed from SystemVerilog interfaces to struct ports.  Thus, all modules in
this repository are now available in tools that do not support interfaces.  Interfaces are now
opt-in: every module has a variant with `_intf` suffix that is functionally equivalent but has
interfaces instead of struct ports.  If you would like to keep using interfaces, please add an
`_intf` suffix to any module you are using from this repository.  Some `_intf` variants require more
parameters (e.g., to define the ID width) than the module prior to this release, but otherwise the
`_intf` variants are drop-in replacements.

We encourage the use of structs to build AXI infrastructure, and we have added a set of `typdef`
macros and have extended the `assign` macros to keep designers productive and prevent mismatches.

Additionally, we have removed a set of modules that had known issues.  We will provide new
implementations for these modules in near-term releases and no longer support the removed modules.

The individual changes for each module follow.

### Added
- `assign.svh`:
  - Macros for setting an AXI or AXI-Lite interface from channel or request/response structs inside
    a process (`AXI_SET_FROM_*` and `AXI_LITE_SET_FROM_*`) and outside a process like an assignment
    (`AXI_ASSIGN_FROM_*` and `AXI_LITE_ASSIGN_FROM_*`).
  - Macros for setting channel or request/response structs to the signals of an AXI or AXI-Lite
    interface inside a process (`AXI_SET_TO_*` and `AXI_LITE_SET_TO_*`) and outside a process like
    an assignment (`AXI_ASSIGN_TO_*`, `AXI_LITE_ASSIGN_TO_*`).
- `typedef.svh`: Macros for defining AXI or AXI-Lite channel (`AXI_TYPEDEF_*_CHAN_T` and
  `AXI_LITE_TYPEDEF_*_CHAN_T`) and request/response structs (`AXI_TYPEDEF_RE{Q,SP}_T` and
  `AXI_LITE_TYPEDEF_RE{Q,SP}_T`).

### Changed
- `axi_atop_filter` has been changed from interfaces to struct ports.  Please use the newly added
  `axi_atop_filter_intf` module if you prefer interfaces.
- `axi_cut` has been changed from interfaces to struct ports.  Please use the newly added
  `axi_cut_intf` module if you prefer interfaces.
- `axi_delayer` has been changed from interfaces to struct ports.  Please use the newly added
  `axi_delayer_intf` module if you prefer interfaces.
- `axi_join` has been renamed to `axi_join_intf`, and `axi_lite_join` has been renamed to
  `axi_lite_join_intf`.  To join two structs, simply assign them instead.
- `axi_multicut` has been changed from interfaces to struct ports.  Please use the newly added
  `axi_multicut_intf` module if you prefer interfaces.
- `axi_modify_address` has been changed from interfaces to struct ports.  Please use the newly added
  `axi_modify_address_intf` module if you prefer interfaces.
- `axi_lite_to_axi` has been changed from interfaces to struct ports.  Please use the newly added
  `axi_lite_to_axi_intf` module if you prefer interfaces.

### Removed
- `axi_lite_xbar`:  This interconnect module was not a full crossbar and its routing rules interface
  no longer fits our demands.  A replacement will be provided in a near-term release.
- `axi_address_resolver` was used together with `axi_lite_xbar` and is removed along with it.  If a
  standalone replacement for this module is required, please use `addr_decoder` from `common_cells`.
- `axi_arbiter` was used together with `axi_lite_xbar` and is removed along with it.  If a
  standalone replacement of this module is required, please use `rr_arb_tree` from `common_cells`.
  A near-term release will introduce an AXI multiplexer and demultiplexer to suit protocol-specific
  needs.
- `axi_id_remap` had problems with ordering and ATOPs.  A new, correct implementation will be
  provided in a near-term release.
- `axi_lite_cut` has been rendered unnecessary by changing `axi_cut` to struct ports.  To get a cut
  with AXI-Lite ports, simply pass AXI-Lite channels and request/response structs as parameters.  If
  you prefer interfaces, please replace any `axi_lite_cut` with the newly added `axi_lite_cut_intf`
  module.
- `axi_lite_multicut`: same rationale and transition procedure as for `axi_lite_cut`.
- In `axi_pkg`, the `*Width` `localparam`s and the `id_t`, `addr_t`, etc. `typedef`s have been
  removed.  There is no one-fits-all value of these parameters, so we cannot provide a generic
  definition for them in this package.  Please use the added macros in `typedef.svh` to define your
  own types with a few lines of code (which you can put into your own package, for example).


## 0.7.2 - 2019-12-03

### Fixed
- axi_to_axi_lite: Fix underflow in internal buffers.
- axi_to_axi_lite: Remove restriction on size of internal buffers.


## 0.7.1 - 2019-11-19

### Changed
- axi_multicut: Simplified implementation without changing I/O behavior.

### Fixed
- src_files: Removed `axi_test.sv` from synthesized files.
- tb_axi_lite_xbar: Fixed AW->W dependency.


## 0.7.0 - 2019-05-28

### Changed
- The `in` and `out` modports have been removed from the interface definition of both AXI and AXI
  Lite.  These modports were "aliases" of `Slave` and `Master`, respectively, and caused problems
  because many tools did not recognize the aliases as being identical to `Slave` and `Master`.


## 0.6.0 - 2019-02-27

### Changed
- AXI interfaces now include the `aw_atop` signal. Interfaces, macros, and existing modules and
  TBs in this repository have been updated. The ReadMe has been updated to guide users of this
  repository on how to deal with the `aw_atop` signal.

### Added
- Add AXI atomic operations (ATOPs) filter.

### Fixed
- Replace non-ASCII characters in Solderpad license text.
- Add a trailing semicolon to the `AXI_ASSIGN()` and `AXI_LITE_ASSIGN()` macros in `assign.svh`
  (#8). Those macros can now be used without a semicolon. Existing code that uses the macros with a
  semicolon do not break.


## 0.5.0 - 2018-12-18
- Add axi channel delayer

### Changed
- Remove clock from `AXI_BUS` and `AXI_LITE`.  Such a clock signal is useful for testing purposes
  but confusing (or even harmful) in hardware designs.  For testing purposes, the `AXI_BUS_DV` and
  `AXI_LITE_DV` (suffix for "design verification") interfaces have been defined instead.

### Fixed
- Update `src_files.yml` to match `Bender.yml`.
- Add missing `axi_test` to compile script.


## 0.4.5 - 2018-09-12
### Fixed
- Fix `common_cells` dependency to open-source repo


## 0.4.4 - 2018-09-06
### Changed
- Make `axi_cut` and `axi_multicut` verilator compatible


## 0.4.3 - 2018-08-01
### Changed
- Add license file and adjust copyright headers.


## 0.4.2 - 2018-06-02
### Fixed
- Add test mode signal to `axi_to_axi_lite` adapter, used in the FIFOs.
- Remove `axi_find_first_one` from src_files.yml
- Fix release ID issue in ID `axi_id_remap`


## 0.4.1 - 2018-03-23
### Fixed
- Remove time unit from test package. Fixes an issue in the AXI driver.


## 0.4.0 - 2018-03-20
### Added
- Add AXI ID remapper.

### Fixed
- Fixed typos in the AXI and AXI-Lite multicuts.
- Fixed ID width in AXI ID remapper.
- AXI join now asserts if width of outgoing ID is larger or equal to width of incoming ID.


## 0.3.0 - 2018-03-09
### Added
- AXI and AXI-Lite multicuts


## 0.2.1 - 2018-03-09
### Fixed
- Remove `axi_find_first_one.sv` from manifest


## 0.2.0 - 2018-03-09
### Added
- AXI cut


## 0.1.0 - 2018-03-09
- Initial release with various interfaces, drivers for testbenches, and utility modules.
