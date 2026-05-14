# axi4_burst_split.sv

## 파일 목적 및 개요

`axi4_burst_split`는 AXI4 데이터 경로에 **burst split 기능**을 삽입하고, split 기준인 `len_limit_i`를 **AXI4-Lite 레지스터로 런타임 제어**할 수 있게 만든 통합 모듈입니다.

이 모듈은 내부적으로 다음 두 IP를 결합합니다.

- `axi_burst_splitter_gran`: AXI4 burst를 설정된 길이 기준으로 분할
- `axi_lite_regs`: AXI4-Lite로 접근 가능한 설정 레지스터 제공

즉, 소프트웨어는 AXI4-Lite를 통해 레지스터 offset `0x0`의 하위 8비트를 갱신하여, burst splitter의 `len_limit_i` 값을 동적으로 바꿀 수 있습니다.

---

## Block Diagram

```mermaid
flowchart LR
  subgraph CFG[AXI4-Lite Control Plane]
    CPU[SW / CPU]
    REGS[axi_lite_regs\nReg[0] = len_limit]
    CPU -->|AXI4-Lite AW/W/AR| REGS
    REGS -->|B/R| CPU
  end

  subgraph DATA[AXI4 Data Plane]
    S[AXI4 Slave-side Input]
    SPLIT[axi_burst_splitter_gran]
    M[AXI4 Master-side Output]
    S --> SPLIT --> M
  end

  REGS -->|reg_q[0][7:0]| SPLIT
```

---

## 주요 파라미터

| 파라미터 | 기본값 | 설명 |
|---|---:|---|
| `MaxReadTxns` | `2` | 동시에 처리 가능한 read burst transaction 수 |
| `MaxWriteTxns` | `2` | 동시에 처리 가능한 write burst transaction 수 |
| `FullBW` | `0` | 내부 ID queue bandwidth 모드 |
| `CutPath` | `0` | 내부 경로 cut 여부 |
| `DisableChecks` | `0` | 미지원 transaction 검사 비활성화 |
| `AddrWidth` | `32` | AXI4 주소 폭 |
| `DataWidth` | `64` | AXI4 데이터 폭 |
| `IdWidth` | `4` | AXI4 ID 폭 |
| `UserWidth` | `1` | AXI4 USER 폭 |
| `CfgAddrWidth` | `12` | AXI4-Lite 제어 포트 주소 폭 |
| `CfgDataWidth` | `32` | AXI4-Lite 제어 포트 데이터 폭 |
| `LenLimitResetVal` | `15` | len_limit 레지스터 reset 값(8-bit) |

---

## 포트 구성

## 1) 공통 포트

- `clk_i`, `rst_ni`
- `test_i` (현재 내부 로직에서 직접 사용되지 않으며 통합 호환용으로 노출)

## 2) AXI4-Lite 제어 포트 (`cfg_*`)

- `cfg_aw_*`, `cfg_w_*`, `cfg_b_*`, `cfg_ar_*`, `cfg_r_*`
- `axi_lite_regs` 인스턴스와 1:1로 연결되어 설정 레지스터 접근에 사용

## 3) AXI4 데이터 포트

- Slave-side 입력: `slv_*`
- Master-side 출력/응답: `mst_*`

내부에서는 flat 포트를 `axi_req_t / axi_resp_t` struct로 변환하여 `axi_burst_splitter_gran`에 연결합니다.

---

## 내부 동작 상세

1. `axi/typedef.svh`의 매크로를 사용해 AXI4/AXI4-Lite channel 및 req/resp 타입을 생성합니다.
2. `cfg_*` 신호를 `cfg_req_t`로 패킹하고, `cfg_resp_t`를 다시 flat 신호로 언패킹합니다.
3. `axi_lite_regs`를 `RegNumBytes=4`로 구성해 4바이트 제어 레지스터 공간을 만듭니다.
4. `RegRstVal`의 첫 바이트를 `LenLimitResetVal`로 설정합니다.
5. `reg_q[0]`을 `axi_burst_splitter_gran.len_limit_i`에 연결합니다.
6. AXI4 데이터 경로는 `slv_* -> slv_req -> axi_burst_splitter_gran -> mst_req -> mst_*`로 전달됩니다.

---

## 레지스터 맵

기본적으로 `axi_lite_regs`의 4바이트 공간을 사용합니다.

| Offset | Name | Width | Access | 설명 |
|---:|---|---:|---|---|
| `0x00` | `LEN_LIMIT` | 8 | RW | `axi_burst_splitter_gran.len_limit_i`에 직접 연결 |
| `0x01` | Reserved | 8 | RW | 현재 미사용 |
| `0x02` | Reserved | 8 | RW | 현재 미사용 |
| `0x03` | Reserved | 8 | RW | 현재 미사용 |

> 주의: `len_limit_i`는 AXI `AxLEN` 인코딩을 따르므로, 값 `0`은 1-beat burst를 의미합니다.

---

## 설계/검토 포인트

- `test_i`는 현재 내부 로직에서 사용되지 않으므로, lint 정책에 따라 unused 신호 처리(예: `/* verilator lint_off UNUSED */`)를 고려할 수 있습니다.
- 단일 파일 lint만으로는 `axi_pkg` 정의를 포함한 전체 컴파일 컨텍스트가 부족할 수 있으므로, 상위 빌드 스크립트(`src_files.yml`, Bender 타깃) 기반 검증이 필요합니다.
- 시스템 통합 시 `CfgDataWidth`/`CfgAddrWidth` 설정이 SoC의 AXI4-Lite interconnect 설정과 일치해야 합니다.
