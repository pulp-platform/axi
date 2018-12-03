# Changelog
All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](http://keepachangelog.com/en/1.0.0/)
and this project adheres to [Semantic Versioning](http://semver.org/spec/v2.0.0.html).

## Unreleased
- Add AXI atomic operations (ATOP) filter

## 0.5.0 - 2018-11-29
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
