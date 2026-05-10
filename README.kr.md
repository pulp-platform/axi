# 고성능 온칩 통신을 위한 AXI SystemVerilog 모듈
[![CI status](https://github.com/pulp-platform/axi/actions/workflows/gitlab-ci.yml/badge.svg?branch=master)](https://github.com/pulp-platform/axi/actions/workflows/gitlab-ci.yml?query=branch%3Amaster)
[![GitHub tag (latest SemVer)](https://img.shields.io/github/v/tag/pulp-platform/axi?color=blue&label=current&sort=semver)](CHANGELOG.md)
[![SHL-0.51 license](https://img.shields.io/badge/license-SHL--0.51-green)](LICENSE)

이 저장소는 [AXI4 또는 AXI4-Lite 표준][AMBA 5 Spec]을 준수하는 온칩 통신 네트워크를 구축하기 위한 모듈들을 제공합니다. 고성능 통신을 위해 AXI4[+AXI5의 ATOPs](#원자적-연산)를 구현하며, 경량 통신을 위해 AXI4-Lite를 구현합니다. DMA 엔진 및 온칩 메모리 컨트롤러와 같은 엔드포인트를 포함한 완전한 엔드투엔드 통신 플랫폼 제공을 목표로 합니다.

**설계 목표**는 다음과 같습니다:
- **토폴로지 독립성**: 사용자가 임의의 네트워크 토폴로지를 구현할 수 있도록 프로토콜 [멀티플렉서](src/axi_mux.sv) 및 [디멀티플렉서](src/axi_demux.sv)와 같은 기본 빌딩 블록을 제공합니다. 또한 [크로스바](src/axi_xbar.sv)와 같이 일반적으로 사용되는 인터커넥트 컴포넌트도 제공합니다.
- **모듈성**: 가능한 한 설정 기반 설계보다 조합 기반 설계를 선호합니다. 하드웨어에 *유닉스 철학*을 적용하려 노력합니다: 각 모듈이 하나의 일을 잘 수행하도록 만듭니다. 이는 보다 특화된 네트워크를 구축할 때 파라미터 값을 변경하는 것보다 모듈을 연속으로 인스턴스화하는 경우가 더 많음을 의미합니다.
- **이기종 네트워크 적합성**: 모듈은 데이터 폭과 트랜잭션 동시성 측면에서 파라미터화가 가능합니다. 이를 통해 다양한 성능(예: 대역폭, 동시성, 타이밍), 전력, 면적 요구사항에 최적화된 네트워크를 생성할 수 있습니다. [데이터 폭 변환기](src/axi_dw_converter.sv) 및 [ID 폭 변환기](src/axi_iw_converter.sv)와 같은 모듈을 제공하여 서로 다른 특성을 가진 서브네트워크를 연결함으로써 이기종 온칩 네트워크를 구성할 수 있습니다.
- **완전한 AXI 표준 준수**.
- **다양한 [EDA 도구(최신 버전 포함)와의 호환성](#어떤-eda-도구를-지원하나요)** 및 표준화된 합성 가능한 SystemVerilog 구현.

이 저장소의 모듈에 대한 **설계 및 마이크로아키텍처**는 [**이 논문**](https://ieeexplore.ieee.org/document/9522037)([프리프린트](https://arxiv.org/pdf/2009.05334))에 설명되어 있습니다. 본 연구를 인용하실 경우 해당 논문을 참고해 주세요.


## 모듈 목록

아래 표에 링크된 문서 외에도, [인라인 docstring에서 자동 생성된 문서](https://pulp-platform.github.io/axi/master)를 정비하고 있습니다. (해당 URL에서 `master`를 특정 태그로 교체하면 해당 버전의 문서를 볼 수 있습니다.)

| 이름                                                        | 설명                                                                                                   | 문서                             |
|-------------------------------------------------------------|------------------------------------------------------------------------------------------------------|----------------------------------|
| [`axi_atop_filter`](src/axi_atop_filter.sv)                 | `aw_atop` 값이 0이 아닌 쓰기 트랜잭션인 원자적 연산(ATOP)을 필터링합니다.                              |                                  |
| [`axi_burst_splitter`](src/axi_burst_splitter.sv)           | AXI4 버스트 전송을 단일 비트 트랜잭션으로 분할합니다.                                                  |                                  |
| [`axi_burst_splitter_gran`](src/axi_burst_splitter_gran.sv) | AXI4 버스트 전송을 런타임 설정 가능한 단위의 트랜잭션으로 분할합니다.                                  |                                  |
| [`axi_burst_unwrap`](src/axi_burst_unwrap.sv)               | AXI4 랩핑 버스트 전송을 최대 두 개의 증분 버스트로 변환합니다.                                         |                                  |
| [`axi_cdc`](src/axi_cdc.sv)                                 | Gray FIFO 구현을 기반으로 한 AXI 클록 도메인 교차(CDC).                                                |                                  |
| [`axi_cut`](src/axi_cut.sv)                                 | 입력과 출력 사이의 모든 조합 경로를 차단합니다.                                                         |                                  |
| [`axi_delayer`](src/axi_delayer.sv)                         | AXI 채널을 (무작위로) 지연시킬 수 있는 합성 가능한 모듈.                                               |                                  |
| [`axi_demux_simple`](src/axi_demux_simple.sv)               | 스필 레지스터가 없는 디멀티플렉서.                                                                      | [Doc](doc/axi_demux.md)          |
| [`axi_demux`](src/axi_demux.sv)                             | AXI 버스를 하나의 슬레이브 포트에서 여러 마스터 포트로 디멀티플렉싱합니다.                              | [Doc](doc/axi_demux.md)          |
| [`axi_dw_converter`](src/axi_dw_converter.sv)               | 임의의 데이터 폭을 가진 AXI 인터페이스 간의 데이터 폭 변환기.                                          |                                  |
| [`axi_dw_downsizer`](src/axi_dw_downsizer.sv)               | 넓은 AXI 마스터와 좁은 AXI 슬레이브 간의 데이터 폭 다운사이저.                                         |                                  |
| [`axi_dw_upsizer`](src/axi_dw_upsizer.sv)                   | 좁은 AXI 마스터와 넓은 AXI 슬레이브 간의 데이터 폭 업사이저.                                           |                                  |
| [`axi_err_slv`](src/axi_err_slv.sv)                         | 수신된 트랜잭션에 항상 AXI 디코드/슬레이브 에러로 응답합니다.                                          |                                  |
| [`axi_fifo`](src/axi_fifo.sv)                               | 요청을 버퍼링하기 위한 각 AXI4 채널용 FIFO.                                                            |                                  |
| [`axi_from_mem`](src/axi_from_mem.sv)                       | SRAM처럼 동작하며 하위로 AXI4 요청을 생성하는 모듈.                                                    |                                  |
| [`axi_id_prepend`](src/axi_id_prepend.sv)                   | AXI ID의 MSB를 앞에 추가하거나 제거하는 모듈.                                                          |                                  |
| [`axi_id_remap`](src/axi_id_remap.sv)                       | 슬레이브 포트의 넓은 AXI ID를 마스터 포트의 좁은 ID로 재매핑합니다.                                    | [Doc][doc.axi_id_remap]          |
| [`axi_id_serialize`](src/axi_id_serialize.sv)               | 필요한 경우 트랜잭션을 직렬화하여 AXI ID를 줄입니다.                                                   | [Doc][doc.axi_id_serialize]      |
| [`axi_interleaved_xbar`](src/axi_interleaved_xbar.sv)       | 크로스바의 인터리브 버전. 이 모듈은 실험적이므로 사용에 주의하십시오.                                  |                                  |
| [`axi_intf`](src/axi_intf.sv)                               | 지원하는 인터페이스를 정의하는 파일.                                                                    |                                  |
| [`axi_inval_filter`](src/axi_inval_filter.sv)               | AXI4 AW 채널을 감청하고 단일 캐시라인 무효화를 발행합니다.                                             |                                  |
| [`axi_isolate`](src/axi_isolate.sv)                         | 하위 슬레이브가 새로운 AXI4 트랜잭션을 수신하지 못하도록 격리할 수 있는 모듈.                          |                                  |
| [`axi_iw_converter`](src/axi_iw_converter.sv)               | 임의의 두 AXI ID 폭 간 변환.                                                                           | [Doc][doc.axi_iw_converter]      |
| [`axi_join`](src/axi_join.sv)                               | 두 AXI 인터페이스를 연결하는 커넥터.                                                                    |                                  |
| [`axi_lfsr`](src/axi_lfsr.sv)                               | AXI4에 연결된 LFSR; 읽기는 의사 난수 데이터를 반환하고 쓰기는 체크섬으로 압축됩니다.                  |                                  |
| [`axi_lite_demux`](src/axi_lite_demux.sv)                   | AXI4-Lite 버스를 하나의 슬레이브 포트에서 여러 마스터 포트로 디멀티플렉싱합니다.                       | [Doc](doc/axi_lite_demux.md)     |
| [`axi_lite_dw_converter`](src/axi_lite_dw_converter.sv)     | 두 AXI-Lite 버스 간의 데이터 폭 변환기.                                                                | [Doc][doc.axi_lite_dw_converter] |
| [`axi_lite_from_mem`](src/axi_lite_from_mem.sv)             | SRAM처럼 동작하며 하위로 AXI4-Lite 요청을 생성하는 모듈.                                               |                                  |
| [`axi_lite_join`](src/axi_lite_join.sv)                     | 두 AXI-Lite 인터페이스를 연결하는 커넥터.                                                              |                                  |
| [`axi_lite_lfsr`](src/axi_lite_lfsr.sv)                     | AXI4-Lite에 연결된 LFSR; 읽기는 의사 난수 데이터를 반환하고 쓰기는 체크섬으로 압축됩니다.             |                                  |
| [`axi_lite_mailbox`](src/axi_lite_mailbox.sv)               | 두 슬레이브 포트와 사용량 기반 인터럽트를 갖춘 AXI4-Lite 메일박스.                                    | [Doc](doc/axi_lite_mailbox.md)   |
| [`axi_lite_mux`](src/axi_lite_mux.sv)                       | AXI4-Lite 슬레이브 포트들을 하나의 마스터 포트로 멀티플렉싱합니다.                                     | [Doc](doc/axi_lite_mux.md)       |
| [`axi_lite_regs`](src/axi_lite_regs.sv)                     | 선택적 읽기 전용 및 보호 기능을 갖춘 AXI4-Lite 레지스터.                                              | [Doc][doc.axi_lite_regs]         |
| [`axi_lite_to_apb`](src/axi_lite_to_apb.sv)                 | AXI4-Lite에서 APB4로의 프로토콜 변환기.                                                                |                                  |
| [`axi_lite_to_axi`](src/axi_lite_to_axi.sv)                 | AXI4-Lite에서 AXI4로의 프로토콜 변환기.                                                                |                                  |
| [`axi_lite_xbar`](src/axi_lite_xbar.sv)                     | 임의의 수의 슬레이브 및 마스터 포트를 가진 완전 연결 AXI4-Lite 크로스바.                               | [Doc](doc/axi_lite_xbar.md)      |
| [`axi_modify_address`](src/axi_modify_address.sv)           | AXI 요청의 주소를 변경할 수 있는 커넥터.                                                               |                                  |
| [`axi_multicut`](src/axi_multicut.sv)                       | 긴 AXI 버스의 타이밍 여유를 완화하는 데 사용할 수 있는 AXI 레지스터.                                  |                                  |
| [`axi_mux`](src/axi_mux.sv)                                 | AXI4 슬레이브 포트들을 하나의 마스터 포트로 멀티플렉싱합니다.                                          | [Doc](doc/axi_mux.md)            |
| [`axi_pkg`](src/axi_pkg.sv)                                 | AXI 정의, 공통 구조체 및 유용한 헬퍼 함수를 포함합니다.                                                |                                  |
| [`axi_rw_join`](src/axi_rw_join.sv)                         | 읽기 슬레이브와 쓰기 슬레이브를 단일 읽기/쓰기 마스터로 결합합니다.                                   |                                  |
| [`axi_rw_split`](src/axi_rw_split.sv)                       | 단일 읽기/쓰기 슬레이브를 하나의 읽기 마스터와 하나의 쓰기 마스터로 분리합니다.                        |                                  |
| [`axi_serializer`](src/axi_serializer.sv)                   | 서로 다른 ID를 가진 트랜잭션을 동일한 ID로 직렬화합니다.                                               |                                  |
| [`axi_slave_compare`](src/axi_slave_compare.sv)             | 두 슬레이브 장치를 비교합니다.                                                                          |                                  |
| [`axi_throttle`](src/axi_throttle.sv)                       | 하위 로직으로 전송되는 미처리 전송의 최대 수를 제한합니다.                                             |                                  |
| [`axi_test`](src/axi_test.sv)                               | AXI 인터페이스를 위한 테스트벤치 유틸리티 모음.                                                        |                                  |
| [`axi_to_axi_lite`](src/axi_to_axi_lite.sv)                 | AXI4에서 AXI4-Lite로의 프로토콜 변환기.                                                                |                                  |
| [`axi_to_mem`](src/axi_to_mem.sv)                           | AXI4에서 메모리 프로토콜(req, gnt, rvalid)로의 변환기. 뱅크형, 인터리브형, 분할형 변형 포함.          |                                  |
| [`axi_xbar`](src/axi_xbar.sv)                               | 임의의 수의 슬레이브 및 마스터 포트를 가진 완전 연결 AXI4+ATOP 크로스바.                               | [Doc](doc/axi_xbar.md)           |
| [`axi_xbar_unmuxed`](src/axi_xbar_unmuxed.sv)               | 임의의 수의 슬레이브 및 마스터 포트를 가진 완전 연결 AXI4+ATOP 크로스바의 디멀티플렉서 측.            | [Doc](doc/axi_xbar.md)           |
| [`axi_xp`](src/axi_xp.sv)                                   | 동형 슬레이브 및 마스터 포트를 가진 AXI 크로스포인트(XP).                                             |                                  |
| [`axi_zero_mem`](src/axi_zero_mem.sv)                       | AXI에 연결된 /dev/zero. 모든 읽기는 0을 반환하고 쓰기는 흡수됩니다.                                   |                                  |

## 합성 가능한 검증 모듈

다음 모듈들은 검증 목적으로만 사용하도록 설계되었지만 FPGA 환경에서 사용할 수 있도록 합성 가능합니다.

| 이름                                                 | 설명                                                                                                    |
|------------------------------------------------------|---------------------------------------------------------------------------------------------------------|
| [`axi_bus_compare`](src/axi_bus_compare.sv)          | 동일 유형(동일 클록 도메인)의 두 버스를 비교하고, 불일치 시 이벤트를 반환합니다.                       |
| [`axi_fifo_delay_dyn`](src/axi_fifo_delay_dyn.sv)    | AXI 버스의 각 채널을 개별적으로 지연 및 버퍼링합니다.                                                  |
| [`axi_slave_compare`](src/axi_slave_compare.sv)      | 동일 유형(동일 클록 도메인)의 두 슬레이브 장치를 비교하고, 불일치 시 이벤트를 반환합니다.             |


### 시뮬레이션 전용 모듈

위의 합성 및 시뮬레이션 모두에서 사용 가능한 모듈 외에, 다음 모듈들은 시뮬레이션에서만 사용 가능합니다. 이 모듈들은 당사의 테스트벤치에서 널리 사용되며, 이 저장소 외부의 AXI 모듈 및 시스템을 위한 테스트벤치 구축에도 적합합니다.

| 이름                                                 | 설명                                                                                                   |
|------------------------------------------------------|--------------------------------------------------------------------------------------------------------|
| [`axi_chan_compare`](src/axi_chan_compare.sv)        | 동일 유형의 두 AXI 채널을 비교하는 비합성 모듈.                                                        |
| [`axi_chan_logger`](src/axi_test.sv)                 | AXI4(+ATOPs) 포트의 트랜잭션을 파일에 기록합니다.                                                      |
| [`axi_driver`](src/axi_test.sv)                      | 임의의 채널에서 개별 비트를 송수신할 수 있는 AXI4(+ATOPs)용 저수준 드라이버.                          |
| [`axi_dumper`](src/axi_dumper.sv)                    | 디버깅을 위해 `axi_dumper_interpret` 스크립트로 해석될 로그를 파일에 덤프합니다.                       |
| [`axi_file_master`](src/axi_test.sv)                 | 파일 기반 테스트벤치를 위한 AXI4 마스터.                                                               |
| [`axi_lite_driver`](src/axi_test.sv)                 | 임의의 채널에서 개별 비트를 송수신할 수 있는 AXI4-Lite용 저수준 드라이버.                             |
| [`axi_lite_rand_master`](src/axi_test.sv)            | 사용자 정의 제약 조건 내에서 무작위 트랜잭션을 발행하는 AXI4-Lite 마스터 컴포넌트.                    |
| [`axi_lite_rand_slave`](src/axi_test.sv)             | 제약 가능한 무작위 지연 및 데이터로 트랜잭션에 응답하는 AXI4-Lite 슬레이브 컴포넌트.                  |
| [`axi_rand_master`](src/axi_test.sv)                 | 사용자 정의 제약 조건 내에서 무작위 트랜잭션을 발행하는 AXI4(+ATOPs) 마스터 컴포넌트.                 |
| [`axi_rand_slave`](src/axi_test.sv)                  | 제약 가능한 무작위 지연 및 데이터로 트랜잭션에 응답하는 AXI4(+ATOPs) 슬레이브 컴포넌트.               |
| [`axi_scoreboard`](src/axi_test.sv)                  | 모니터링된 AXI4(+ATOPs) 포트에 의해서만 변경되는 메모리를 모델링하는 스코어보드.                      |
| [`axi_sim_mem`](src/axi_sim_mem.sv)                  | AXI4 슬레이브 포트를 가진 무한 메모리.                                                                 |



## 원자적 연산

AXI4+ATOPs는 전체 AXI4 사양에 더해 [AMBA 5 사양][AMBA 5 Spec]의 섹션 E1.1에 정의된 원자적 연산(ATOP)을 의미합니다. 이는 ATOP을 구현하지 않는 모듈과 그러한 모듈을 포함하는 시스템에 다음과 같은 영향을 미칩니다:

- ATOP을 발행하지 않는 마스터는 `aw_atop`을 `'0`으로 설정해야 합니다.
- ATOP을 지원하지 않는 슬레이브는 인터페이스 문서에 이를 명시해야 하며 `aw_atop` 신호를 무시할 수 있습니다.
- 시스템 설계자는 다음을 보장할 책임이 있습니다:
  1. 어떤 마스터가 ATOP을 발행할 수 있는 슬레이브가 ATOP을 지원하지 않는 경우, 해당 슬레이브 앞에 [`axi_atop_filter`](src/axi_atop_filter.sv)를 배치하고,
  2. 이 저장소의 모든 (AXI4-Lite가 아닌) 모듈의 입력에서 `aw_atop` 신호가 올바르게 정의되어 있는지 확인합니다.

ATOP을 지원하는 마스터 및 슬레이브는 [AMBA 5 사양][AMBA 5 Spec]의 섹션 E1.1을 준수해야 합니다. 특히:
- `aw_atop[axi_pkg::ATOP_R_RESP]` 비트가 설정된 ATOP은 쓰기 응답(B 채널) 비트와 하나 이상의 읽기 응답(R 채널) 비트를 생성합니다. 마스터 포트에서 `aw_atop[axi_pkg::ATOP_R_RESP]` 비트가 설정될 수 있는 모든 모듈은 각 ATOP 요청에 대해 B 및 R 비트 모두를 (임의의 순서로, 동시 핸드셰이크 없이) 처리할 수 있어야 합니다. 슬레이브 포트에서 `aw_atop[axi_pkg::ATOP_R_RESP]` 비트가 설정될 수 있는 모든 모듈은 각 ATOP 요청에 대해 적절한 수의 B 및 R 비트로 응답해야 합니다.
- ATOP은 동시에 미처리 상태인 다른 트랜잭션과 동일한 AXI ID를 사용해서는 안 됩니다.


## 어떤 EDA 도구를 지원하나요?

당사 코드는 표준 SystemVerilog([IEEE 1800-2012][], 정확히는)로 작성되어 있으므로, 더 중요한 질문은 귀사의 EDA 도구가 SystemVerilog의 어떤 부분집합을 지원하느냐입니다.

당사는 다양한 EDA 도구와의 호환성을 목표로 합니다. 이를 위해 특히 합성 가능한 모듈에서 가능한 한 단순한 언어 구조를 사용하려 노력합니다. 더 많은 EDA 도구와의 호환성을 위해 코드를 더욱 단순화하는 기여를 장려합니다. 또한 특정 EDA 도구가 당사 코드와 관련하여 겪는 문제를 해결하는 기여도 환영합니다. 단, 다음 조건을 충족해야 합니다:
- 해당 EDA 도구가 합리적으로 널리 사용되고,
- 최신 버전의 해당 EDA 도구가 영향을 받으며,
- 해결책이 다른 도구의 기능을 손상시키지 않고,
- 해결책이 코드를 크게 복잡하게 만들거나 유지보수 부담을 증가시키지 않아야 합니다.

또한, SystemVerilog 언어 지원 문제는 EDA 벤더에 직접 보고할 것을 권장합니다. 당사 코드는 완전히 공개되어 있으며, 발견된 언어 문제에 대한 테스트 케이스로 EDA 벤더와 공유할 수 있고 또 그렇게 해야 합니다.

각 릴리즈 및 기본 브랜치의 모든 코드는 적어도 하나의 업계 표준 RTL 시뮬레이터 및 합성 도구의 최신 버전에서 테스트됩니다. [CI 설정](./.gitlab-ci.yml)을 통해 어떤 버전의 어떤 도구를 사용하는지 확인할 수 있습니다.


[AMBA 5 Spec]: https://developer.arm.com/documentation/ihi0022/hc
[IEEE 1800-2012]: https://standards.ieee.org/standard/1800-2012.html
[doc.axi_id_remap]: https://pulp-platform.github.io/axi/master/module.axi_id_remap
[doc.axi_id_serialize]: https://pulp-platform.github.io/axi/master/module.axi_id_serialize
[doc.axi_iw_converter]: https://pulp-platform.github.io/axi/master/module.axi_iw_converter
[doc.axi_lite_regs]: https://pulp-platform.github.io/axi/master/module.axi_lite_regs
