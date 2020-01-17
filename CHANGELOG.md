# Changelog
All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](http://keepachangelog.com/en/1.0.0/)
and this project adheres to [Semantic Versioning](http://semver.org/spec/v2.0.0.html).


## Unreleased

### Added

### Changed

### Fixed

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
