# Changelog
이 프로젝트의 모든 주요 변경 사항은 이 파일에 기록됩니다.

이 파일의 형식은 [Keep a Changelog](http://keepachangelog.com/en/1.0.0/)를 기반으로 하며,
이 프로젝트는 [Semantic Versioning](http://semver.org/spec/v2.0.0.html)을 따릅니다.


## Unreleased

## 0.39.9 - 2025-11-21

### Added
- `assign`: 플랫 AXI 포트에 대한 할당 추가. #392
- `axi_inval_filter` 추가. #386

### Fixed
- `axi_to_detailed_mem`: HideStrb 사용 시 잘못된 쓰기 응답 방지. #383
- `axi_dw_downsizer`: 린팅 경고 수정. #385
- `axi_burst_unwrap`: 과도하게 비관적인 어설션 제거. #387
- `axi_burst_splitter_gran`: IP가 안정적인 `w.last`를 갖도록 보장. #393
- `axi_fifo_delay_dyn_intf`: 딜레이 포트에 DELAY_WIDTH 사용. #395
- `axi_to_mem`: dead_response_fifo의 strb 입력 수정. #389
- `axi_id_prepend`: 암묵적 변환 린터 경고 수정. #397

### Changed
- `axi_burst_unwrap`: 수정 불가능한 WRAP 버스트만 무효화하도록 변경. #382


## 0.39.8 - 2025-06-24
### Added
- AXI 버스의 각 채널을 개별적으로 지연시킬 수 있는 비합성 IP 추가. #380
- AXI-Realm용으로 개발된 `burst_splitter`의 세분화 버전 추가. #377
- CI에 Verilator를 사용한 정교화(elaboration) 린팅 패스 추가. #378

### Fixed
- `axi_burst_splitter`: 주소 정렬 문제 수정. #375
- `axi_lite_to_apb`: 여러 수정 사항. #375
- `axi_to_mem`: 엣지 케이스 수정. #376
- 여러 린트 수정. #374

### Changed
- `axi_sim_mem`: B 및 R 채널에서 user 필드 전파. #373
- CI에서 VSIM 버전 2025.1로 전환. #378


## 0.39.7 - 2025-05-20
### Added
- `axi_burst_unwrap` 추가. #326

### Fixed
- `axi_dw_upsizer`: r_data의 불필요하게 넓은 인덱스를 피하도록 수정. #362
- [test] morty CI 오류를 수정하기 위해 생성자에서 begin/end 제거
- `axi_lite_lfsr`: 누락된 신호 선언 추가. (#363)
- `axi_to_mem_interleaved`: busy 신호 수정.
- `axi_dw_downsizer`: Verilator 호환성을 위해 불필요하게 넓은 인덱스 수정. #366

### Changed
- llc-partition 테스트에 임의 user 신호 생성 추가. #315
- `common_verification`을 `v0.2.4`에서 `v0.2.5`로 업데이트.
- `axi_cut`에 선택적 채널 바이패스 추가.

## 0.39.6 - 2024-12-04
### Added
- `axi_intercon_gen`에 연결성 지원 추가. #351
- 배열 길이의 언더플로를 방지하기 위한 `iomsb` 함수를 `axi_pkg`에 추가. #355

### Fixed
- `axi_dw_upsizer`의 case 문을 unique로 만들기. 시뮬레이터 경고를 방지하기 위한 기본 case 추가. #348
- `axi_rw_split`의 쓰기 채널 어설션 수정. #357
- `axi_isolate`의 패스스루 종단에서 미사용 `demux` 포트 연결. #359

### Changed
- VCS 및 Verilator 지원을 전반적으로 개선. #358
- Verilator 수정 사항을 포함한 `common_verification`을 `v0.2.4`로 업데이트.

## 0.39.5 - 2024-10-24

### Fixed
- VCS가 아직 다차원 인터페이스 배열을 지원하지 않으므로 VCS에서 `axi_xbar_unmuxed`의 인터페이스 변형을 비활성화.

### Changed
- `axi_id_serialize`: Cheshire에서 CVA6 부팅 문제를 수정하기 위해 #342를 되돌림.

## 0.39.4 - 2024-07-25 (Yanked 2024-10-23)
### Added
- `axi_sim_mem`: 요청 포트 수 증가, 멀티포트 인터페이스 변형 추가.
- `axi_bus_compare`: 사용된 데이터만 비교하기 위해 AXI `size` 필드를 선택적으로 고려.
- `AXI_BUS_DV`: 버스트가 4KiB 페이지 경계를 넘지 않는다는 속성 검사 추가.
- `axi_xbar_unmuxed` 추가: 멀티플렉서 해제된 mst_ports를 가진 부분 크로스바.

### Fixed
- `axi_bus_compare`: 불일치 감지 수정.
- `axi_to_detailed_mem`: 요청에 `lock`이 설정된 경우에만 `exokay`로 응답하도록 수정.
  `mem_to_banks` 수정을 위해 `common_cells` 버전 업.
- `axi_dw_downsizer`: `i_forward_b_beats_queue` 언더플로 수정.
- `axi_atop_filter`: XSIM 시뮬레이션 버그를 방지하기 위해 내부 FSM에 리셋 상태 추가.
- `axi_test`: 임의 요청이 4KiB 페이지 경계를 넘지 않도록 보장.

### Changed
- `axi_id_serializer`: 더 단순한 코드, 더 적은 하드웨어, 더 적은 스톨링을 위해 내부 설계(및 동작) 변경.

`v0.39.4`는 `v0.39.3`과 완전히 **하위 호환됩니다**.

## 0.39.3 - 2024-05-08
### Added
- `axi_sim_mem`: 초기화되지 않은 영역의 응답 데이터에 구성 가능한 정의 값 허용.
- `axi_test`: `axi_rand_master`에 `clear_memory_regions` 추가.
- `axi_test`: `axi_rand_master`에 `add_traffic_shaping_with_size` 추가하여 커스텀 크기를 이용한 트래픽 쉐이핑 허용.

### Changed
- `axi_pkg`: `xbar_cfg_t`의 `LatencyMode` 파라미터를 커스텀 구성을 허용하기 위해 `xbar_pipeline_e` 열거형에서 비트 벡터로 조정.

`v0.39.3`은 `v0.39.2`와 완전히 **하위 호환됩니다**.

## 0.39.2 - 2024-03-13

### Added
- `axi_interleaved_xbar`: 종속 장치에 메모리 전송을 인터리빙하는 실험적 크로스바 확장. #334
  ***자신의 책임 하에 사용하세요***.
- `axi_zero_mem`: AXI용 *\dev\zero* 기능 구현. #334

### Fixed
- `axi_to_detailed_mem`: VCS가 기본 파라미터 0에서 충돌하여 1로 변경. #334
- `axi_to_mem`: 누락된 테스트 모드 핀 추가. #327
- `axi_sim_mem`: R 및 W fork에서 바이트 계산 수정. #331

`v0.39.2`는 `v0.39.1`과 완전히 **하위 호환됩니다**.

## 0.39.1 - 2023-09-05

### Added
- `axi_cdc`: `SyncStages` 파라미터 추가.
- `axi_to_mem_interleaved`: 인터페이스 변형 추가.
- `axi_burst_splitter`: `id_queue`의 `FULL_BW` 파라미터 노출.
- `axi_chan_compare`: 재순서(reordered) 트랜잭션을 허용하는 파라미터 추가.
- AXI 신호를 강조 표시하는 `AXI_HIGHLIGHT` 매크로 추가.
- 플랫 포트 인스턴스화 매크로 추가.

### Fixed
- `axi_test`: `axi_scoreboard`에서 잘못 정렬된 읽기에 대한 거짓 음성 방지.
- `axi_to_detailed_mem`: `err` 및 `exokay` 신호의 적절한 전파 보장.

## 0.39.0 - 2023-07-20

### Added
- 합성 가능한 IP:
  - `axi_bus_compare`와 `axi_slave_compare`: FPGA에서 두 AXI 버스를 비교하기 위한 합성 가능한 검증 IP.
  - `axi_lite_from_mem`과 `axi_from_mem`: SRAM처럼 동작하며 하위 AXI4 요청을 발생시킴.
  - `axi_lite_dw_converter`: AXI4-Lite 트랜잭션의 데이터 폭 변환. 요청된 전체 접근을 수행하기 위해 적절한 수의 하위 트랜잭션 발생.
  - `axi_rw_join`과 `axi_rw_split`: AXI 버스의 읽기 및 쓰기 채널 분리/결합.
- 커스텀 채널 타입 이름으로 AXI struct를 인스턴스화하는 `CT` 매크로.
- `axi_pkg`: `xbar_cfg_t`에 문서 추가.
- 테스트벤치 IP:
  - `axi_chan_compare.sv`: 동일한 타입의 두 AXI 채널을 비교하는 비합성 모듈.
  - `axi_test`에 `axi_file_master` 추가: 파일 기반 AXI 검증 접근법 지원.
  - `axi_test`에 AXI 채널의 폭을 반환하는 `#_width` 함수 추가.

### Changed
- 합성 가능한 IP:
  - `axi_demux`: AW와 W 채널 사이의 FIFO를 레지스터와 카운터로 교체. 이를 통해 다른 버스트의 W가 다른 마스터 포트로 진행 중일 때 한 마스터 포트로 AW가 발행되는 것을 방지. 하위에서 순환 대기로 인한 데드락을 방지하기 위해 필요. `axi_demux`에서 `FallThrough` 파라미터 제거.
  - `axi_demux` 로직과 타이밍 디커플링을 분리. 새 모듈 `axi_demux_simple`이 핵심 로직을 포함.
  - `axi_dw_downsizer`: `axi_pkg::RESP_EXOKAY`를 기본값으로 사용.
  - `axi_id_remap`의 `casez` 단순화.
  - `axi_id_serialize` 모듈에 선택적 명시적 매핑 추가.
  - `axi_to_mem`을 `axi_to_detailed_mem`으로 확장하여 AXI의 부가 신호(`id`, `user`, `cache`, `prot`, `qos`, `region`, `atop`) 노출 및 `err`와 `exokay` 주입 가능.
  - `axi_xbar`: `axi_pkg::xbar_cfg_t`에 `PipelineStages` 파라미터 추가. *demux*와 *mux* 사이 크로스 연결에 `axi_multicuts` 추가. 인라인 문서 개선.
  - `mem_to_banks`를 `common_cells`로 이동.
- `axi_pkg`: *Vivado*와의 호환성 향상.
- `axi_test`:
  - `axi_lite_rand_slave`: `R` 응답 필드를 이제 무작위화.
  - 무작위 마스터 및 슬레이브에서 과도한 출력 제거.
  - 주소를 올바르게 크기 정렬.
- `axi_pkg`: AXI 타입 폭을 정의하는 `localparam` 정의.
- `common_cells`를 버전 `v1.26.0`에서 `v1.27.0`으로 업데이트.
- 툴링:
  - GitHub CI에서 내부 CI와 통신하기 위해 `pulp-platform/pulp-actions/gitlab-ci@v2` 사용.
  - `DC Shell version`을 `2019.12`에서 `2022.03`으로 업.
  - *ModelSim* 버전 `10.7e` 및 `2021.3` 검사 중단, `2022.3` 추가.
  - `xbar`에 대한 더 철저한 검증 실행.
  - 시뮬레이션 실행을 위해 쉘 스크립트에서 Makefile로 전환 시작.
- `scripts/update_authors`를 사용하여 저자 업데이트, 약간의 수동 수정 수행.

### Fixed
- `axi_to_mem_banked`: `UniqueIds`를 올바르게 설정하여 하드웨어 감소.
- `axi_to_mem_interleaved`와 `axi_to_mem_split`이 이제 올바르게 디멀티플렉서를 인스턴스화. DFT를 위한 `test_i` 포트 추가.

### Breaking Changes
`v0.38.0`과 `v0.39.0` 사이에 하위 호환성이 깨지는 변경 사항이 있습니다:
- `axi_demux`: `FallThrough` 파라미터 제거.
- `axi_xbar`: `axi_pkg::xbar_cfg_t`에 `PipelineStages` 파라미터 추가.
- `axi_to_mem_interleaved`와 `axi_to_mem_split`: `test_i` 입력 포트 추가.

## 0.38.0 - 2022-09-28

### Added
- 디버깅 목적으로 AXI 버스의 로그를 덤프하기 위한 `axi_dumper` 및 `axi_dumper_interpret` 스크립트 추가.
- CI에 FuseSoC 및 Vivado XSIM 제한 테스트 추가.
- `assign.svh`: Vivado 명명 스타일을 사용하여 플랫 버스를 할당하는 매크로 추가.
- `axi_lfsr` 및 `axi_lite_lfsr`: AXI4 및 AXI4 Lite LFSR 종속(Subordinate) 장치 추가.
- `axi_xp`: 동형의 슬레이브 및 마스터 포트를 가진 크로스포인트 추가.

### Changed
- FuseSoC와의 호환성 개선.
- Vivado XSIM과의 호환성 개선.
- `axi_to_mem` 성능 개선.
- `scripts/update_authors`를 사용하여 저자 업데이트, 약간의 수동 수정 수행.

`v0.38.0`은 `v0.36.0` 및 `v0.37.0`과 완전히 **하위 호환됩니다**.


## 0.37.0 - 2022-08-30

### Added
- `axi_fifo`: 5개의 AXI4 채널 모두에 FIFO 삽입; 모듈 및 테스트벤치 추가.
- `axi_test`: 무작위 클래스에 `mapped` 모드 추가 및 scoreboard 클래스에 추가 기능 추가.
- `axi_throttle`: 하위 로직으로 전송되는 최대 미처리 전송 수를 제한하는 모듈 추가.
- `axi_to_mem`: 온칩 메모리를 제어하는 AXI4+ATOP 슬레이브.
- `axi_to_mem_banked`: 뱅킹 지원을 통해 `axi_to_mem`보다 높은 처리량으로 온칩 메모리를 제어하는 AXI4+ATOP 슬레이브.
- `axi_to_mem_interleaved`: 데드락 방지를 위해 인터리빙된 온칩 메모리를 제어하는 AXI4+ATOP 슬레이브.
- `axi_to_mem_split`: 메모리 프로토콜 인터커넥트를 제어하는 AXI4+ATOP 슬레이브.
- `Bender`: 시뮬레이션용 범용 SRAM 매크로를 위한 의존성 `tech_cells_generic` `v0.2.2` 추가.

### Changed
- `axi_demux`: 모듈 독스트링 추가.
- `axi_sim_mem`: 읽기 및 쓰기 오류를 발생시킬 수 있는 기능 추가.
- `Bender`: `common_cells` 의존성을 `v1.21.0`에서 `v1.26.0`으로 업데이트 (`axi_throttle`에 필요).
- `docs` 디렉터리 제거, 내용을 `doc` 폴더로 이동. `docs`는 CI 실행 중 자동으로 생성 및 채워짐.
- CI에서 vsim 버전을 `2021.3`으로 업데이트, `2020.1` 및 `2021.1` 테스트 중단.

### Fixed
- `axi_lite_demux`: vsim 버전 10.7b와의 호환성 개선.
- `axi_lite_mux`: 불필요한 멀티플렉서를 제거하여 마스터 포트의 W 채널 복잡도 감소.

`v0.37.0`은 `v0.36.0`과 완전히 **하위 호환됩니다**.


## 0.36.0 - 2022-07-07

### Added
- `AXI_BUS`, `AXI_LITE`, `AXI_LITE_DV` 인터페이스에 Monitor modport 추가.


## 0.35.3 - 2022-05-03

### Fixed
- `axi_demux`: AR 채널이 최대 트랜잭션 수에 도달했을 때 AW 채널의 불필요한 스톨 제거. 이 수정 이전에는 읽기 트랜잭션이 최대에 달한 경우(`MaxTrans` 읽기 트랜잭션이 미처리된 경우) `axi_demux`가 항상 AW를 스톨시켰습니다. 그러나 이 스톨은 `axi_demux`가 처리 중인 AW가 R 응답을 수반하는 원자적 연산(ATOP)인 경우에만 필요합니다. 따라서 이 수정은 불필요한 스톨과 읽기와 쓰기 사이의 불필요한 의존성을 제거합니다. 데이터 또는 트랜잭션의 무결성은 이 문제의 영향을 받지 않았습니다.


## 0.35.2 - 2022-04-14

### Fixed
- `axi_lite_mux_intf`: `slv` 및 `mst` 인터페이스 포트의 타입 수정; `AXI_LITE` 대신 `AXI_BUS`였습니다.
- `axi_xbar_intf`: 파라미터 순서 수정. 이 수정 이전에는 `CONNECTIVITY` 파라미터가 `Cfg` 파라미터가 정의되기 전에 `Cfg` 파라미터를 사용하여 정의되었습니다.
- `axi_test::axi_rand_master`: 어설션 내의 함의(implication)를 조건부 어설션으로 변경하여 시뮬레이터 호환성 개선.


## 0.35.1 - 2022-03-31

### Fixed
- `axi_demux`와 `axi_lite_demux`: 단일 마스터 포트 구성에서 누락된 spill 레지스터 추가.
- `axi_demux_intf`: 원자적 연산 지원을 선택적으로 비활성화하기 위한 누락된 파라미터(`ATOP_SUPPORT`) 추가.
- `axi_mux`와 `axi_lite_mux`: 단일 슬레이브 포트 구성에서 누락된 spill 레지스터 추가.
- `axi_lite_mux_intf`: 내부 `axi_lite_mux` 인스턴스에 누락된 파라미터 값(`axi_req_t` 및 `axi_resp_t`) 추가.
- `axi_sim_mem`: AR 채널의 user 신호를 모니터로 올바르게 전파.


## 0.35.0 - 2022-03-11

### Added
- `axi_sim_mem`: 쓰기 채널과 읽기 채널 사이의 일관성 지점을 관찰하기 위한 모니터링 인터페이스 추가.

### Fixed
- `axi_sim_mem`: 수락되지 않는 동안 R 응답을 안정적으로 유지.


## 0.34.0 - 2022-03-09

### Added
- `axi_demux`와 `axi_isolate`: 원자적 연산(ATOP) 지원을 선택적으로 비활성화하기 위한 `AtopSupport` 파라미터 추가. 이 파라미터의 기본값은 `1'b1`이므로 ATOP가 지원됩니다. 따라서 이 변경은 하위 호환됩니다.
- `axi_isolate`: 격리 중 트랜잭션에 선택적으로 응답하기 위한 `TerminateTransaction` 파라미터 추가. 이 파라미터의 기본값은 `1'b0`이므로 트랜잭션은 응답을 받지 않습니다. 따라서 이 변경은 하위 호환됩니다.
- `axi_xbar`: 부분적으로 연결된 크로스바 구현을 위한 `Connectivity` 파라미터 추가. 이 파라미터의 기본값은 `'1`이므로 모든 슬레이브 포트가 모든 마스터 포트에 연결됩니다. 따라서 이 변경은 하위 호환됩니다.
- `axi_test`: 모니터 클래스 `axi_monitor` 추가.
- `axi_test::axi_driver`: 모니터 태스크 추가.

### Changed
- `axi_isolate`: 주소, 데이터, ID, user 신호 폭에 대한 파라미터 추가. 이는 `TerminateTransaction` 파라미터 구현에 필요합니다(*Added* 섹션 참조). 이 변경은 이 저장소 외부의 모든 `axi_isolate` 인스턴스에 대해 **하위 호환되지 않습니다**. 사용자는 코드의 모든 `axi_isolate` 인스턴스를 업데이트해야 합니다. 인터페이스 변형은 영향받지 않으며 하위 호환성이 유지됩니다.


## 0.33.1 - 2022-02-26

### Fixed
- `axi_xbar_intf`: 원자적 연산 지원을 선택적으로 비활성화하기 위한 누락된 `ATOPS` 파라미터 추가(v0.25.0에서 `axi_xbar`에 도입됨). 추가된 파라미터의 기본값으로 인해 이 수정은 하위 호환됩니다.


## 0.33.0 - 2022-02-21

### Added
- `axi_sim_mem`의 인터페이스 변형인 `axi_sim_mem_intf` 추가.

### Fixed
- `axi_cdc`: QuestaSim 전용 워크어라운드만 사용하도록 제한하여 VCS와의 호환성 개선(이슈 #207).
- `axi_id_remap`: 해당 도구에 대해 `assert`를 제외하여 Verilator 호환성 개선.
- `axi_lite_demux`: VCS와의 호환성 개선(이슈 #187, `axi_demux`에 보고되어 v0.29.2에서 수정됨).
- `axi_xbar`: 상수 함수 호출을 사용하지 않는 VCS 전용 코드를 추가하여 VCS 호환성 개선(#208).


## 0.32.0 - 2022-01-25

### Changed
- `axi_atop_filter`, `axi_burst_splitter`, `axi_cut`, `axi_delayer`, `axi_demux`, `axi_err_slv`,
  `axi_isolate`, `axi_lite_demux`, `axi_lite_mux`, `axi_lite_to_axi`, `axi_lite_xbar`,
  `axi_multicut`, `axi_serializer`, `axi_sim_mem`: `req_t` 및 `resp_t` 타입 파라미터에 `axi_` 접두어 추가. 이는 올바른 타입 해석 및 격리에 문제가 있는 도구에서의 타입 충돌을 방지합니다. 이 변경은 이 저장소 외부의 나열된 모든 모듈 인스턴스에 대해 **하위 호환되지 않습니다**. 사용자는 코드의 나열된 모듈의 모든 인스턴스를 업데이트해야 합니다. 인터페이스 변형은 영향받지 않으며 하위 호환성이 유지됩니다.


## 0.31.1 - 2022-01-17

### Fixed
- `axi_xbar`: 단일 마스터 포트의 신호 폭 수정. 이 수정 이전에는 단일 마스터 포트로 인스턴스화된 크로스바가 잘못된 차원의 배열을 포함했습니다.


## 0.31.0 - 2021-12-07

### Added
- 다양한 동시성 요구 사항 하에서 임의의 두 AXI ID 폭 사이를 변환하는 세 개의 모듈 추가:
  - `axi_iw_converter`: 지원되는 모든 파라미터로 임의의 두 AXI ID 폭 간 변환을 수행하는 최상위 모듈. MSB를 0으로 확장하여 ID를 업사이즈하고 동일한 ID 폭의 두 인터페이스를 결합합니다. ID 다운사이징을 위해 다음 두 모듈 중 하나를 인스턴스화합니다:
  - `axi_id_remap`: 트랜잭션을 직렬화하지 않고 슬레이브 포트의 넓은 ID를 마스터 포트의 더 좁은 ID로 리매핑.
  - `axi_id_serialize`: 필요할 때 트랜잭션을 직렬화하여 AXI ID 축소.


## 0.30.0 - 2021-12-01

### Added
- `axi_lite_xbar`의 인터페이스 변형인 `axi_lite_xbar_intf` 추가.

### Fixed
- `axi_lite_demux`: QuestaSim 옵티마이저(`vopt`)의 새 버전과의 호환성 개선. 이 워크어라운드 이전에는 QuestaSim 2021.1이 `axi_lite_demux` 인스턴스에서 세그폴트가 발생할 수 있었습니다.


## 0.29.2 - 2021-11-12

### Fixed
- `axi_demux`: VCS와의 호환성 개선(#187). #169의 워크어라운드가 VCS 2020.12와 호환되지 않았습니다. 해당 워크어라운드는 이제 `TARGET_VSIM`이 정의된 경우에만 활성화됩니다.
- `axi_dw_downsizer`와 `axi_dw_upsizer`(`axi_dw_converter`의 일부): Mentor Precision 합성 도구에서 래치 추론 방지.
- `axi_lite_cdc_src_intf`: `axi_cdc_src` 인스턴스화에서 `_i` 및 `_o` 접미사 수정.
- `axi_test::axi_rand_slave`: VCS와의 호환성 개선(#175).
- `axi_test::axi_scoreboard`: 일부 도구와의 호환성 개선을 위해 파라미터에 기본값 추가.


## 0.29.1 - 2021-06-02

### Fixed
- `axi_lite_to_apb_intf`: v0.28.0에서 `axi_lite_to_apb`에 추가된 누락된 파라미터 추가.


## 0.29.0 - 2021-05-06

### Changed
- `axi_xbar`와 `axi_demux`: 두 모듈 모두에 `UniqueIds` 파라미터를 추가하여 고유 ID 지원(#172). 동일 방향의 모든 미처리 트랜잭션 중 각 트랜잭션의 ID가 항상 고유함을 보장할 수 있다면, `UniqueIds` 파라미터를 `1'b1`로 설정하여 디멀티플렉서를 단순화할 수 있습니다(자세한 내용은 `axi_demux` 문서 참조). 이 변경은 `axi_demux`에서 하위 호환됩니다(새 파라미터의 기본값이 `1'b0`이므로). `axi_xbar`는 `xbar_cfg_t` `struct`로 구성되므로 이 변경은 `axi_xbar`에서는 *하위 호환되지 않습니다*(`default` 부분으로 초기화된 `xbar_cfg_t` 제외).

### Fixed
- `axi_test::axi_rand_master`: 구현을 단순화하고 중복 코드를 제거하기 위해 ID 합법화를 공통 함수로 리팩터링. 알려진 기능적 버그는 수정되지 않았으나, 리팩터링된 코드의 정확성을 더 쉽게 검증할 수 있습니다.


## 0.28.0 - 2021-04-15

### Added
- 클록 도메인 크로싱(CDC)을 위한 소스 클록 도메인 "반쪽"과 목적지 클록 도메인 "반쪽" 추가:
  `axi_cdc_src`와 `axi_cdc_dst`. `axi_cdc` 모듈을 리팩터링하여 구현하므로 기존 `axi_cdc` 모듈의 구현이 재사용됩니다. 코드 중복을 피하기 위해 `axi_cdc`는 이제 `axi_cdc_src`와 `axi_cdc_dst`를 연결하여 인스턴스화합니다.

### Changed
- `axi_lite_to_apb`: 요청 및 응답 경로의 파이프라인 레지스터를 선택적으로 사용 가능(새 `PipelineRequest` 및 `PipelineResponse` `parameter`로 활성화 가능), 기본적으로 비활성화.

### Fixed
- `axi_demux`: QuestaSim 옵티마이저(`vopt`)의 새 버전과의 호환성 개선(#169). 이 워크어라운드 이전에는 QuestaSim 2020.2 및 2021.1이 `axi_demux` 인스턴스에서 세그폴트가 발생할 수 있었습니다.


## 0.27.1 - 2021-02-01

### Fixed
- `axi_dw_downsizer`와 `axi_dw_upsizer`(`axi_dw_converter`의 일부): 문제가 있는 전방 참조를 제거하기 위해 `w_req_t`, `w_req_d`, `w_req_q` 선언 순서 수정.
- FuseSoC: `common_cells`의 버전 수정(`1.21.0`).


## 0.27.0 - 2021-02-01

### Added
- `assign.svh`: AXI-Lite `struct` 간 할당을 위한 매크로 추가: 프로세스 내부(`AXI_LITE_SET_*_STRUCT`)와 프로세스 외부(`AXI_LITE_ASSIGN_*_STRUCT`). 이는 개별 필드를 할당하기 때문에 단순히 `=`로 `struct`를 할당하는 것보다 안전합니다.
- `typedef.svh`: AXI4+ATOP 및 AXI4-Lite 인터페이스의 모든 채널과 요청/응답 `struct`를 단일 매크로 호출로 정의하는 `AXI_TYPEDEF_ALL` 및 `AXI_LITE_TYPEDEF_ALL` 매크로 추가.
- `axi_test::axi_rand_slave`: B 및 R 비트의 `resp` 필드 무작위화를 활성화하는 `RAND_RESP` 파라미터 추가.

### Changed
- `axi_test::axi_rand_master`: QoS 필드 무작위화.
- `common_verification` 의존성을 `0.2.0`으로 업데이트(1년 이상 전에 릴리스됨).
- `common_verification` 의존성의 버전 `0.2.0`에 맞추기 위해 `common_cells` 의존성을 `1.21.0`으로 업데이트. 이는 `axi_burst_splitter`에서 범위를 벗어난 인덱스를 수정한 `common_cells` 버전 `1.20.1`을 포함합니다(#150).


## 0.26.0 - 2021-01-19

### Added
- 무한, 시뮬레이션 전용 메모리 `axi_sim_mem` 추가.
- `assign.svh`: `struct` 간 할당을 위한 매크로 추가: 프로세스 내부(`AXI_SET_*_STRUCT`)와 프로세스 외부(`AXI_ASSIGN_*_STRUCT`). 이는 개별 필드를 할당하기 때문에 단순히 `=`로 `struct`를 할당하는 것보다 안전합니다. (두 `struct` 사이에서 일치하지 않는 필드, 예를 들어 다른 `user` 신호 폭으로 인한 경우, 별도로 할당해야 하며 일부 경우에는 반드시 그렇게 해야 합니다.)

### Changed
- `axi_test`의 다음 클래스들을 이 저장소의 모든 사용자 대면 객체가 `axi_`로 시작하는 규칙을 따르도록 이름 변경:
  - `rand_axi_lite_master`를 `axi_lite_rand_master`로,
  - `rand_axi_lite_slave`를 `axi_lite_rand_slave`로,
  - `rand_axi_master`를 `axi_rand_master`로,
  - `rand_axi_slave`를 `axi_rand_slave`로.


## 0.25.0 - 2021-01-14

### Added
- `axi_xbar`: 원자적 연산(`ATOPs`) 지원을 비활성화하는 파라미터 추가.

### Changed
- `AXI_BUS`, `AXI_BUS_ASYNC`, `AXI_BUS_DV`, `AXI_LITE`, `AXI_LITE_DV`: 모든 파라미터의 타입을 `int`에서 `int unsigned`로 변경. 해당 파라미터가 실제로 음수 값을 취할 수 없으므로 부호 없는 타입이 더 적합하며, 일부 도구와의 호환성을 개선합니다.
- `axi_test::rand_axi_lite_slave`와 `axi_test::rand_axi_lite_master`: 주소 및 데이터 폭 파라미터(`AW` 및 `DW`)의 타입을 `int`에서 `int unsigned`로 변경. `AXI_BUS`(등)와 동일한 이유.

### Fixed
- `axi_demux`: 조합 시뮬레이션 루프 제거.
- `axi_xbar`: 도구 제한을 위한 워크어라운드 도입으로 vsim 버전 10.6c(및 이전 버전)와의 호환성 개선(#133).
- `tb_axi_lite_regs`: 불필요한 하드코딩된 어설션 제거.
- `axi_demux`, `axi_err_slv`, `axi_xbar`에서 `XSIM`이 정의된 경우 형식 속성을 비활성화하여 Vivado XSim과의 호환성 개선.


## 0.24.2 - 2021-01-11

### Changed
- `axi_test::rand_axi_lite_master`와 `axi_test::rand_axi_lite_slave`: 모든 파라미터에 기본값이 필요한 도구와의 호환성 개선을 위해 파라미터에 기본값 지정.

### Fixed
- `axi_lite_demux`: VCS와의 호환성 개선을 위해 `generate` 블록 밖으로 `typedef` 이동.
- `axi_test::rand_axi_master`와 `axi_test::rand_axi_slave`: 클래스 변수에 대한 `randomize` 함수 호출 수정. 이 수정 이전에는 세 개의 클래스 변수에 `std::randomize()` 함수가 사용되었으나, 클래스 변수는 `.randomize()` 멤버 함수를 사용해야 합니다.


## 0.24.1 - 2020-11-04

### Changed
- IPApproX에서 파일 순서를 수정하기 위해 `common_cells` 의존성을 `1.20.0`으로 업데이트.

### Fixed
- `doc/axi_lite_mailbox`: `STATUS` 레지스터에서 `RFIFOL` 및 `WFIFOL`의 위치 수정.
- IPApproX:
  - `common_cells_lib`에 대한 누락된 링크 추가.
  - `common_cells`의 인클루드 경로 수정.
  - `common_verification`의 버전 명세 수정.


## 0.24.0 - 2020-10-27

### Added
- `axi_pkg`: 응답 우선순위를 정의하는 함수 추가.

### Changed
- `axi_dw_downsizer`와 `axi_dw_upsizer`: 크리티컬 패스 단축을 위해 원자적 AW를 AR 채널로 주입하는 파이프라인 추가.

### Fixed
- `axi_dw_downsizer`와 `axi_dw_upsizer`: 비트 슬라이스 할당 구성의 이식성 개선.
- `axi_dw_downsizer`:
  - 분할된 트랜잭션 중 최악의 응답 전달.
  - B 전달 FIFO 오버플로 수정.
- `axi_test`: `rand_atop_burst`에서 최소 길이 제약 제거.


## 0.23.2 - 2020-09-14

### Fixed
- `ips_list.yml`: 누락된 `common_verification` 의존성 추가.


## 0.23.1 - 2020-06-19

### Fixed
- `axi_lite_demux_intf`: `axi_lite_demux`에 `req_t` 및 `resp_t` 파라미터 전달 수정.
- `axi_lite_xbar`: `axi_lite_to_axi` 인스턴스에서 누락된 `slv_a{w,r}_cache_i` 연결 추가.


## 0.23.0 - 2020-05-11

### Added
- `axi_lite_regs`: AXI4-Lite 슬레이브 포트와 개별 바이트를 읽기 전용으로 만드는 옵션을 가진 메모리 매핑 레지스터 추가.

### Changed
- 인터페이스 `AXI_LITE`와 `AXI_LITE_DV`: `aw_prot` 및 `ar_prot` 신호 추가.
  - `AXI_LITE_ASSIGN*` 및 `AXI_LITE_SET*` 매크로(`include/axi/assign.svh`)가 두 개의 새 인터페이스 신호를 포함하도록 업데이트됨.
  - `axi_test::axi_lite_driver`: `send_aw`, `send_ar`, `recv_aw`, `recv_ar` 함수에 새 `prot` 함수 인수 추가.
  - `axi_test::rand_axi_lite_master`:
    - `write` 및 `read` 함수에 각각 새 `w_prot` 및 `r_prot` 함수 인수 추가. 새 인수는 기본값 `'0`을 가짐.
    - `send_aws` 및 `send_ars` 함수가 이제 각 AW 및 AR의 `prot` 신호를 무작위화.
  - `axi_test::rand_axi_slave`: `prot` 신호 표시(그 외에는 무시).

### Fixed
- `rand_axi_master`(`axi_test` 내): ATOP를 발행할 때 버스트 타입 제한을 준수하는 또 다른 수정.


## 0.22.1 - 2020-05-11

### Fixed
- `rand_axi_master`(`axi_test` 내): ATOP를 발행할 때 버스트 타입 제한 준수.


## 0.22.0 - 2020-05-01

### Added
- `axi_pkg`: `bufferable` 및 `modifiable` 헬퍼 함수 추가.
- `axi_dw_converter`: 다운사이저에서 단일 비트 *fixed* 버스트 지원 추가 및 업사이저에서 임의 길이의 *fixed* 버스트 지원 추가.

### Changed
- `axi_dw_downsizer`(`axi_dw_converter`의 일부): 들어오는 트랜잭션의 *modifiable* 비트와 관계없이 다운사이징 수행. 이전에는 다운사이징을 위해 속성을 수정해야 하는 비*modifiable* 트랜잭션이 슬레이브 오류로 거부되었습니다. 이 변경 이후에는 *modifiable* 비트가 설정되지 않더라도 트랜잭션이 다운사이징되고 속성이 수정됩니다. 이는 AXI 사양(IHI0022H의 A4-65 페이지)의 주석에 의해 허용됩니다.

### Fixed
- `axi_dw_downsizer`(`axi_dw_converter`의 일부): 마스터/하위 포트보다 작은 `size`를 가진 트랜잭션을 수정 없이 유지하는 조건 수정.


## 0.21.0 - 2020-04-27

### Added
- `axi_serializer`: 다른 ID를 가진 트랜잭션을 동일한 ID로 직렬화.

### Changed
- `axi_modify_address`:
  - 중복된 `slv_resp_t` 및 `mst_resp_t` 파라미터를 단일 `axi_resp_t` 파라미터로 단순화.
  - `slv_req_i` 입력으로부터 피드백되던 불필요한 `slv_a{r,w}_addr_o` 출력 제거. 해당 신호는 `axi_modify_address` 외부에서 유도할 수 있습니다.
- `axi_modify_address_intf`:
  - 슬레이브 포트 이름을 `slv`, 마스터 포트 이름을 `mst`로 변경하고 저장소 규칙에 맞게 관련 파라미터 이름 변경.
  - 값이 부호 없는 타입이므로 파라미터 타입을 `int unsigned`로 변경.
  - 인터페이스로부터의 유도가 많은 도구와 호환되지 않으므로 데이터, ID, user 폭에 대한 파라미터 추가.
  - 포트 이름에 누락된 I/O 접미사 추가 및 `axi_modify_address`와 정렬.

### Fixed
- `axi_modify_address_intf`: 실제 구현에 전달되는 타입 파라미터 수정.


## 0.20.0 - 2020-04-22

### Added
- `axi_pkg`: 래핑 버스트의 경계를 계산하는 `wrap_boundary` 함수 추가.
- `axi_test`: 무작위 AXI 마스터 `rand_axi_master`가 이제 래핑 버스트를 발행할 수 있음(기본적으로는 발행하지 않음). 세 개의 새 파라미터가 발행되는 트랜잭션의 버스트 타입을 제어합니다; 해당 파라미터를 설정하지 않으면 무작위 마스터는 이 변경 이전과 동일하게 동작합니다.
- 인터페이스 `AXI_BUS_DV`: 모든 신호가 입력인 `Monitor` modport 추가.
- `axi/assign.svh`: `AXI_BUS`를 `AXI_BUS_DV.Monitor`에 할당하는 `AXI_ASSIGN_MONITOR` 매크로 추가.
- 패키지 `axi_test`: 메모리 주소에서 읽은 데이터가 해당 주소에 쓰여진 데이터와 일치하는지 확인하는 `axi_scoreboard` 클래스 추가.

### Changed
- `axi_pkg`:
  - `beat_addr` 함수가 이제 모든 버스트 타입을 지원합니다. 이로 인해 함수에 두 개의 새 인수(버스트의 길이 및 타입)가 추가되었습니다.
  - `beat_upper_byte` 및 `beat_lower_byte` 함수가 내부적으로 `beat_addr`를 호출하므로 두 개의 새 인수도 추가되었습니다.


## 0.19.0 - 2020-04-21

### Changed
- `axi_lite_to_axi`: `AxCACHE` 신호 노출. 추가된 `slv_aw_cache_i` 및 `slv_ar_cache_i` 입력을 구동하여 이 모듈에서 나오는 AXI 트랜잭션의 `cache` 신호를 정의할 수 있습니다. 이 변경 이전의 동작을 유지하려면 두 입력을 0으로 연결합니다.


## 0.18.1 - 2020-04-08

### Fixed
- `axi_modify_address`: 연결되지 않은 `w_valid` 수정.
- `axi_dw_converter`: 업/다운 변환의 내부 반전 수정, 잘못된 레인 스티어링 및 직렬화로 이어졌음.
- `rand_axi_master`(`axi_test` 내): ATOP 모드에서 완료되어야 할 쓰기(ATOP 읽기 응답 없음)만 남은 경우 R 비트 수신 중 모듈이 멈출 수 있었습니다. 이 문제가 수정되었습니다.
- `assign.svh`: 불필요한 세미콜론 제거.
- `axi_lite_to_apb`: strobe 폭 확인 어설션 메시지 수정.


## 0.18.0 - 2020-03-24

### Added
- `axi_dw_converter`: 임의의 데이터 폭의 AXI 인터페이스 사이의 데이터 폭 변환기. 파라미터화에 따라 이 모듈은 다음 중 하나를 인스턴스화합니다:
  - `axi_dw_downsizer`: 넓은 AXI 마스터와 더 좁은 슬레이브 사이의 데이터 폭 변환기.
  - `axi_dw_upsizer`: 좁은 AXI 마스터와 더 넓은 슬레이브 사이의 데이터 폭 변환기.


## 0.17.0 - 2020-03-23

### Added
- 하위 슬레이브가 새 트랜잭션을 받지 못하도록 격리하는 `axi_isolate` 추가.

### Changed
- `axi_lite_to_axi`: 아래에 언급된 수정을 활성화하기 위해 필수 `AxiDataWidth` 파라미터 추가.

### Fixed
- Xcelium과의 호환성 개선:
  - `axi_lite_to_axi`에서 `$bits()` 함수에 대한 지원되지 않는 계층적 인수 제거;
  - `axi_lite_demux`에서 지원되지 않는 `struct` 할당 제거.


## 0.16.3 - 2020-03-19

### Changed
- `axi_err_slv`: 읽기 응답으로 반환되는 데이터를 정의하는 선택적 파라미터 추가. 이 파라미터는 64비트 값을 기본으로 하므로, 데이터 폭이 64비트 이상인 버스는 이전 버전 대비 오류 응답에서 추가적인 32비트 값을 볼 수 있습니다. 그 외에는 이 변경이 완전히 하위 호환됩니다.


## 0.16.2 - 2020-03-16

### Fixed
- `axi_atop_filter`: `AxiMaxWriteTxns = 1`에서 카운터 언더플로 수정.


## 0.16.1 - 2020-03-13

### Fixed
- 매크로 호출의 공백 및 세미콜론 제거.
- `axi_intf`: 지원되지 않는 어설션을 비활성화하여 Verilator 호환성 개선.


## 0.16.0 - 2020-03-11

### Added
- `axi_cdc_intf`: AXI 클록 도메인 크로싱의 인터페이스 변형 추가.

### Fixed
- `axi_cdc`: 미사용 전역 `import axi_pkg::*` 제거.
- `axi_intf`: 전역 `import axi_pkg::*` 제거 및 `axi_pkg`의 심볼 명시적 사용.
- `axi_lite_cut_intf`: 인터페이스 포트로의/로부터의 누락된 할당 추가.
- `tb_axi_cdc`:
  - 전역 `import axi_pkg::*` 제거.
  - 로컬 `typedef` 대신 `AXI_TYPEDEF` 매크로로 채널 정의.

### Removed
- 미사용 `AXI_ARBITRATION` 및 `AXI_ROUTING_RULES` 인터페이스 제거.


## 0.15.1 - 2020-03-09

### Added
- `axi_intf`: `AXI_BUS_DV`에 단일 채널 어설션 추가.

### Fixed
- `axi_lite_to_apb`: 버전 `0.15.0`의 변경 사항을 반영하도록 인터페이스 버전(`axi_lite_to_apb_intf`) 수정.
- `axi_demux`: `MaxTrans`가 1일 때 `IdCounterWidth`가 0이 되는 문제 수정.
- `axi_atop_filter`:
  - 이 모듈의 마스터 인터페이스가 한 경우에 `w_valid`를 적용하기 전에 `aw_ready`에 의존했는데, 이는 데드락으로 이어질 수 있는 AXI 사양 위반입니다. 해당 의존성을 제거하여 수정.
  - 이 모듈의 슬레이브 인터페이스가 valid와 핸드쉐이크 사이에 B 및 R 비트 값을 불법적으로 변경할 수 있었습니다. 이 문제가 수정되었습니다.
- `rand_axi_master`(`axi_test` 내):
  - `send_ws` 태스크에서 무한 대기 수정.
  - AW 생성을 전송과 분리. 이를 통해 AW 비트보다 먼저 또는 동시에 W 비트를 적용할 수 있습니다.
- `rand_axi_slave`(`axi_test` 내):
  - AW 수신으로부터 W 수신 분리. AW 비트와 독립적으로 W 비트를 수신할 수 있습니다.
- `id_queue`의 합성 경고를 수정하기 위해 `common_cells`를 `1.16.4`로 업데이트.


## 0.15.0 - 2020-02-28

### Added
- `axi_burst_splitter`: AXI4 버스트를 단일 비트 트랜잭션으로 분할.

### Changed
- `axi_lite_to_apb`: `apb_req_t` struct의 `psel` 필드가 이제 단일 비트. 즉, 모든 APB 슬레이브가 자체 요청 struct를 가집니다. 따라서 `apb_req_o`는 이제 `NoApbSlaves` 항목을 가진 배열입니다.
- `axi_decerr_slv`가 더 일반적인 `axi_err_slv`로 대체되었으며, 오류 종류를 파라미터로 받습니다. 이 `axi_err_slv`는 더 이상 `FallThrough` 파라미터를 가지지 않으며, 응답(즉, B 또는 R 비트)은 항상 AW 또는 AR 비트 이후 한 사이클에 옵니다(AXI 사양에서 요구하는 대로). 단, 슬레이브는 해당하는 AW 비트와 동일한 사이클에 W 비트를 수락할 수 있습니다. 또한 `axi_err_slv`는 원자적 연산 지원 여부를 정의하는 `ATOPs` 파라미터를 받습니다.
- `axi_to_axi_lite`: struct 기반으로 모듈 재작업 및 버스트 지원 추가.

### Fixed
- `axi_demux`: 카운터를 제어하는 `case` 문이 `unique`로 지정되지 않았으나 해당 조건을 충족했습니다. 이 문제가 수정되었습니다.
- `axi_lite_mux_intf`: 내부 할당의 신호 이름, `axi_lite_mux` 인스턴스의 파라미터 이름 및 어설션 메시지의 오타 수정.


## 0.14.0 - 2020-02-24

### Added
- `axi_lite_mailbox` 추가: AXI4-Lite 메일박스.


## 0.13.0 - 2020-02-18

### Added
- `axi_xbar_intf`: 크로스바의 인터페이스 변형 추가.

### Fixed
- `axi_atop_filter`: `default` 문 추가로 ModelSim 경고 수정. `case`의 신호가 단일 비트이며 두 값 모두 합성에서 올바르게 처리되었습니다. 그러나 시뮬레이션 시작 시 신호가 정의되지 않은 값을 가지므로 ModelSim이 이것이 `unique` 조건을 위반한다는 경고를 발생시켰습니다.
- `axi_demux`: VCS와의 호환성을 위해 `generate` 외부로 `typedef` 이동.
- `axi_id_prepend`:
  - 일부 어설션 메시지 텍스트 수정.
  - 단일 비트 ID 앞에 붙이는 경우 수정.
- `tb_axi_xbar`: 마스터 수에 의존하도록 로컬파라미터 `AxiIdWidthSlaves` 수정.


## 0.12.0 - 2020-02-14

### Added
- `axi_lite_to_apb`: AXI4-Lite에서 APB4로의 변환기.


## 0.11.0 - 2020-02-13

### Added
- `axi_cdc`: 안전한 AXI 클록 도메인 크로싱(CDC) 구현 추가.

### Changed
- `axi_demux`와 `axi_mux`의 인터페이스 변형이 이 저장소의 인터페이스 변형 규칙에 맞게 변경되었습니다:
  - `axi_demux_wrap`: 이름을 `axi_demux_intf`로 변경하고 파라미터 이름을 ALL_CAPS로 변경.
  - `axi_mux_wrap`: 이름을 `axi_mux_intf`로 변경하고 파라미터 이름을 ALL_CAPS로 변경.
- `axi_demux`: 기본 파라미터를 `0`으로 설정.

### Fixed
- `axi_demux`: `NoMstPorts == 1`에 대한 파라미터 케이스 추가.


## 0.10.2 - 2020-02-13

### Fixed
- `axi_atop_filter`: `unique case` 블록에서 도달 불가능한 `default` 제거.
- `axi_demux_wrap`: demux에 전달되는 신호 수정.
- `axi_lite_demux_intf`: demux에 전달되는 신호 수정.
- `axi_lite_mux`: `r_fifo_push` 누락된 선언 추가.


## 0.10.1 - 2020-02-12

### Fixed
- `axi_lite_xbar`: `NoMstPorts == 1`에서 합성 수정.


## 0.10.0 - 2020-02-11

### Added
- `axi_lite_xbar`: 완전 연결된 AXI4-Lite 크로스바.
- `axi_lite_demux`: 하나의 슬레이브 포트에서 설정 가능한 수의 마스터 포트로의 AXI4-Lite 디멀티플렉서.
- `axi_lite_mux`: 설정 가능한 수의 슬레이브 포트에서 하나의 마스터 포트로의 AXI4-Lite 멀티플렉서.

### Changed
- `axi_test`: 무작위 AXI4-Lite 마스터 및 슬레이브 테스트벤치 클래스로 패키지 확장.


## 0.9.2 - 2020-02-11

### Fixed
- `axi_pkg`: Vivado 합성에서 `CUT_ALL_PORTS`의 값 수정(`xbar_latency_e` 내).


## 0.9.1 - 2020-01-18

### Fixed
- `axi_decerr_slv`: 파라미터를 UpperCamelCase로 수정.


## 0.9.0 - 2020-01-16

### Added
- `axi_test`: 제약된 무작위 AXI 마스터(`rand_axi_master`)와 슬레이브(`rand_axi_slave`).
  - `rand_axi_master`는 설정 가능한 메모리 영역(관련 메모리 타입을 가진 주소 범위)에 설정 가능한 수의 읽기 및 쓰기 트랜잭션을 제약 내에서 무작위 속성(예: 버스트 길이, 독점 접근, 원자적 연산)으로 발행합니다.
  - `rand_axi_slave`는 무작위 지연 및 데이터로 트랜잭션에 응답합니다.
- `axi_pkg`: AXI 메모리 타입(`mem_type_t`) 및 주어진 메모리 타입에 대한 `AxCACHE` 비트를 계산하는 `get_arcache`와 `get_awcache` 함수.
- `axi_decerr_slv` 추가.
- `axi_id_prepend` 추가.
- 완전히 규격을 준수하는 `axi_xbar` 추가.
- `axi_mux`, `axi_demux`, `axi_xbar`에 대한 문서 추가.
- `README.md`에 모듈 개요 추가.

### Changed
- `axi_test`: `axi_driver` 및 `axi_lite_driver`의 `reset` 태스크가 이제 함수입니다.
- `axi_xbar`에서 사용되는 주소 디코딩 로직을 포함하는 `common_cells`를 `1.16.0`으로 업.

### Fixed
- `axi_intf`: import를 인터페이스 본문으로 이동.
- `axi_pkg`: Synopsys 문제를 수정하기 위해 함수를 자동(automatic)으로 지정.


## 0.8.2 - 2019-12-20

### Fixed
- `src_files.yml`: `axi_test`에 `only_local` 플래그 추가.
- `axi_test`:
  - `axi_lite_driver`에 누락된 기본 파라미터 추가.
  - `axi_test`에서 패키지로 와일드카드 import 이동하여 컴파일 단위 오염 방지.


## 0.8.1 - 2019-12-19

### Added
- `axi_pkg`: 비트 내 주소 및 바이트 위치를 계산하는 함수.


## 0.8.0 - 2019-12-19

모든 모듈이 SystemVerilog 인터페이스에서 struct 포트로 변경되었습니다. 따라서 이 저장소의 모든 모듈은 이제 인터페이스를 지원하지 않는 도구에서도 사용 가능합니다. 인터페이스는 이제 선택 사항입니다: 모든 모듈은 기능적으로 동일하지만 struct 포트 대신 인터페이스를 가진 `_intf` 접미사의 변형을 가집니다. 인터페이스를 계속 사용하려면 이 저장소에서 사용하는 모든 모듈에 `_intf` 접미사를 추가하세요. 일부 `_intf` 변형은 이 릴리스 이전의 모듈보다 더 많은 파라미터(예: ID 폭 정의)를 필요로 하지만, 그 외에는 `_intf` 변형이 드롭인 교체품입니다.

AXI 인프라를 구축하기 위해 struct 사용을 권장하며, 설계자의 생산성을 높이고 불일치를 방지하기 위해 `typedef` 매크로 세트를 추가하고 `assign` 매크로를 확장했습니다.

또한 알려진 문제가 있는 모듈 세트를 제거했습니다. 해당 모듈들에 대한 새 구현은 단기 릴리스에서 제공될 예정이며, 제거된 모듈은 더 이상 지원되지 않습니다.

각 모듈별 개별 변경 사항은 다음과 같습니다.

### Added
- `assign.svh`:
  - 프로세스 내부(`AXI_SET_FROM_*` 및 `AXI_LITE_SET_FROM_*`)와 할당처럼 프로세스 외부(`AXI_ASSIGN_FROM_*` 및 `AXI_LITE_ASSIGN_FROM_*`)에서 채널 또는 요청/응답 struct로부터 AXI 또는 AXI-Lite 인터페이스를 설정하는 매크로.
  - 프로세스 내부(`AXI_SET_TO_*` 및 `AXI_LITE_SET_TO_*`)와 할당처럼 프로세스 외부(`AXI_ASSIGN_TO_*`, `AXI_LITE_ASSIGN_TO_*`)에서 AXI 또는 AXI-Lite 인터페이스의 신호를 채널 또는 요청/응답 struct로 설정하는 매크로.
- `typedef.svh`: AXI 또는 AXI-Lite 채널(`AXI_TYPEDEF_*_CHAN_T` 및 `AXI_LITE_TYPEDEF_*_CHAN_T`)과 요청/응답 struct(`AXI_TYPEDEF_RE{Q,SP}_T` 및 `AXI_LITE_TYPEDEF_RE{Q,SP}_T`)를 정의하기 위한 매크로.

### Changed
- `axi_atop_filter`: 인터페이스에서 struct 포트로 변경. 인터페이스를 선호하는 경우 새로 추가된 `axi_atop_filter_intf` 모듈을 사용하세요.
- `axi_cut`: 인터페이스에서 struct 포트로 변경. 인터페이스를 선호하는 경우 새로 추가된 `axi_cut_intf` 모듈을 사용하세요.
- `axi_delayer`: 인터페이스에서 struct 포트로 변경. 인터페이스를 선호하는 경우 새로 추가된 `axi_delayer_intf` 모듈을 사용하세요.
- `axi_join`이 `axi_join_intf`로, `axi_lite_join`이 `axi_lite_join_intf`로 이름 변경. 두 struct를 결합하려면 단순히 할당을 사용하세요.
- `axi_multicut`: 인터페이스에서 struct 포트로 변경. 인터페이스를 선호하는 경우 새로 추가된 `axi_multicut_intf` 모듈을 사용하세요.
- `axi_modify_address`: 인터페이스에서 struct 포트로 변경. 인터페이스를 선호하는 경우 새로 추가된 `axi_modify_address_intf` 모듈을 사용하세요.
- `axi_lite_to_axi`: 인터페이스에서 struct 포트로 변경. 인터페이스를 선호하는 경우 새로 추가된 `axi_lite_to_axi_intf` 모듈을 사용하세요.

### Removed
- `axi_lite_xbar`: 이 인터커넥트 모듈은 완전한 크로스바가 아니었으며 그 라우팅 규칙 인터페이스가 더 이상 요구 사항에 맞지 않습니다. 대체품은 단기 릴리스에서 제공될 예정입니다.
- `axi_address_resolver`: `axi_lite_xbar`와 함께 사용되었으며 함께 제거됩니다. 이 모듈의 독립적인 대체품이 필요한 경우 `common_cells`의 `addr_decoder`를 사용하세요.
- `axi_arbiter`: `axi_lite_xbar`와 함께 사용되었으며 함께 제거됩니다. 이 모듈의 독립적인 대체품이 필요한 경우 `common_cells`의 `rr_arb_tree`를 사용하세요. 단기 릴리스에서 프로토콜 특화 요구를 충족하는 AXI 멀티플렉서 및 디멀티플렉서가 도입될 예정입니다.
- `axi_id_remap`: 순서 및 ATOP에 문제가 있었습니다. 올바른 새 구현이 단기 릴리스에서 제공될 예정입니다.
- `axi_lite_cut`: `axi_cut`을 struct 포트로 변경함으로써 불필요해졌습니다. AXI-Lite 포트로 컷을 얻으려면 단순히 AXI-Lite 채널과 요청/응답 struct를 파라미터로 전달하세요. 인터페이스를 선호하는 경우 `axi_lite_cut`을 새로 추가된 `axi_lite_cut_intf` 모듈로 교체하세요.
- `axi_lite_multicut`: `axi_lite_cut`과 동일한 이유 및 전환 절차.
- `axi_pkg`에서 `*Width` `localparam`과 `id_t`, `addr_t` 등의 `typedef`가 제거되었습니다. 이 파라미터들은 모든 경우에 맞는 하나의 값이 없으므로 이 패키지에서 일반적인 정의를 제공할 수 없습니다. 몇 줄의 코드로 자체 타입을 정의하기 위해 `typedef.svh`에 추가된 매크로를 사용하세요(예를 들어 자체 패키지에 넣을 수 있습니다).


## 0.7.2 - 2019-12-03

### Fixed
- axi_to_axi_lite: 내부 버퍼 언더플로 수정.
- axi_to_axi_lite: 내부 버퍼 크기 제한 제거.


## 0.7.1 - 2019-11-19

### Changed
- axi_multicut: I/O 동작 변경 없이 구현 단순화.

### Fixed
- src_files: 합성 파일에서 `axi_test.sv` 제거.
- tb_axi_lite_xbar: AW->W 의존성 수정.


## 0.7.0 - 2019-05-28

### Changed
- AXI 및 AXI Lite 인터페이스 정의에서 `in` 및 `out` modport가 제거되었습니다. 이 modport들은 각각 `Slave`와 `Master`의 "별칭"이었으나, 많은 도구가 별칭을 `Slave` 및 `Master`와 동일한 것으로 인식하지 못해 문제가 발생했습니다.


## 0.6.0 - 2019-02-27

### Changed
- AXI 인터페이스에 이제 `aw_atop` 신호가 포함됩니다. 이 저장소의 인터페이스, 매크로, 기존 모듈 및 테스트벤치가 업데이트되었습니다. ReadMe가 `aw_atop` 신호를 처리하는 방법을 저장소 사용자에게 안내하도록 업데이트되었습니다.

### Added
- AXI 원자적 연산(ATOPs) 필터 추가.

### Fixed
- Solderpad 라이선스 텍스트에서 비ASCII 문자 교체.
- `assign.svh`의 `AXI_ASSIGN()` 및 `AXI_LITE_ASSIGN()` 매크로에 뒤따르는 세미콜론 추가(#8). 이제 해당 매크로를 세미콜론 없이 사용할 수 있습니다. 세미콜론과 함께 매크로를 사용하는 기존 코드는 영향받지 않습니다.


## 0.5.0 - 2018-12-18
- AXI 채널 딜레이어 추가.

### Changed
- `AXI_BUS` 및 `AXI_LITE`에서 클록 제거. 이러한 클록 신호는 테스트 목적으로는 유용하지만 하드웨어 설계에서는 혼란스럽거나 심지어 해롭습니다. 테스트 목적으로는 대신 `AXI_BUS_DV` 및 `AXI_LITE_DV`("설계 검증"을 위한 접미사) 인터페이스가 정의되었습니다.

### Fixed
- `Bender.yml`에 맞게 `src_files.yml` 업데이트.
- 컴파일 스크립트에 누락된 `axi_test` 추가.


## 0.4.5 - 2018-09-12
### Fixed
- `common_cells` 의존성을 오픈소스 저장소로 수정.


## 0.4.4 - 2018-09-06
### Changed
- `axi_cut` 및 `axi_multicut`을 Verilator 호환 가능하게 변경.


## 0.4.3 - 2018-08-01
### Changed
- 라이선스 파일 추가 및 저작권 헤더 조정.


## 0.4.2 - 2018-06-02
### Fixed
- `axi_to_axi_lite` 어댑터에 테스트 모드 신호 추가(FIFO에서 사용됨).
- `src_files.yml`에서 `axi_find_first_one` 제거.
- ID `axi_id_remap`의 릴리스 ID 문제 수정.


## 0.4.1 - 2018-03-23
### Fixed
- 테스트 패키지에서 시간 단위 제거. AXI 드라이버의 문제 수정.


## 0.4.0 - 2018-03-20
### Added
- AXI ID 리매퍼 추가.

### Fixed
- AXI 및 AXI-Lite 멀티컷의 오타 수정.
- AXI ID 리매퍼의 ID 폭 수정.
- AXI join이 이제 나가는 ID 폭이 들어오는 ID 폭보다 크거나 같은 경우 어설션합니다.


## 0.3.0 - 2018-03-09
### Added
- AXI 및 AXI-Lite 멀티컷.


## 0.2.1 - 2018-03-09
### Fixed
- 매니페스트에서 `axi_find_first_one.sv` 제거.


## 0.2.0 - 2018-03-09
### Added
- AXI 컷.


## 0.1.0 - 2018-03-09
- 다양한 인터페이스, 테스트벤치용 드라이버, 유틸리티 모듈을 포함한 초기 릴리스.
