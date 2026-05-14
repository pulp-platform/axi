# axi_burst_splitter_gran_wrapper.sv

## 파일 목적 및 개요

`axi_burst_splitter_gran_wrapper`는 `axi_burst_splitter_gran` 모듈을 AMD Vivado Custom IP로 패키징하기 쉽도록 만든 flat-port 래퍼입니다.

원본 `axi_burst_splitter_gran`은 AXI request/response 구조체 타입을 파라미터로 받아 동작합니다. Vivado IP Packager는 이러한 SystemVerilog struct 포트보다 `s_axi_*` / `m_axi_*` 형태의 개별 AXI 포트를 더 잘 인식하므로, 이 래퍼는 다음 기능을 제공합니다.

- `aclk`, `aresetn` 클럭/리셋 포트
- Vivado AXI4 인터페이스 추론용 `X_INTERFACE_INFO` / `X_INTERFACE_PARAMETER` 속성
- upstream 쪽 `S_AXI` slave flat 포트
- downstream 쪽 `M_AXI` master flat 포트
- flat AXI 신호와 내부 AXI request/response struct 사이의 변환 로직
- `axi_burst_splitter_gran`의 `len_limit_i` 제어 입력 노출

---

## 주요 파라미터

| 파라미터 | 기본값 | 설명 |
|---|---:|---|
| `MAX_READ_TXNS` | `2` | 동시에 outstanding 가능한 read burst 수 |
| `MAX_WRITE_TXNS` | `2` | 동시에 outstanding 가능한 write burst 수 |
| `FULL_BW` | `0` | 내부 ID queue bandwidth 모드 |
| `CUT_PATH` | `0` | 내부 multicut 경로 cut 설정 |
| `DISABLE_CHECKS` | `0` | unsupported transaction check 비활성화 여부 |
| `AXI_ADDR_WIDTH` | `32` | AXI 주소 폭 |
| `AXI_DATA_WIDTH` | `32` | AXI 데이터 폭 |
| `AXI_ID_WIDTH` | `1` | AXI ID 폭 |
| `AXI_USER_WIDTH` | `1` | AXI user 신호 폭 |

`AXI_ID_WIDTH`와 `AXI_USER_WIDTH`는 flat IP 포트 생성을 위해 최소 1 이상이어야 합니다.

---

## 포트 구성

### 공통 제어 포트

| 포트 | 방향 | 설명 |
|---|---|---|
| `aclk` | input | `S_AXI`와 `M_AXI`에 연결되는 공통 clock |
| `aresetn` | input | active-low reset |
| `len_limit_i` | input | splitter가 방출할 최대 burst 길이의 AXI `AxLEN` encoding (`0`은 1 beat) |

### AXI4 flat 포트

- `S_AXI`: wrapper의 slave-side AXI4 입력 인터페이스입니다. 원본 모듈의 `slv_req_i` / `slv_resp_o`에 연결됩니다.
- `M_AXI`: wrapper의 master-side AXI4 출력 인터페이스입니다. 원본 모듈의 `mst_req_o` / `mst_resp_i`에 연결됩니다.

각 인터페이스는 AW, W, B, AR, R 채널의 ID, address, burst, data, response, user, valid/ready 신호를 flat port로 제공합니다.

---

## 내부 동작

1. `include/axi/typedef.svh`의 AXI typedef 매크로로 wrapper 내부 request/response struct 타입을 정의합니다.
2. `S_AXI` flat 입력 포트를 `slv_req` struct로 패킹하고, `slv_resp` struct를 `S_AXI` flat 출력으로 언패킹합니다.
3. `mst_req` struct를 `M_AXI` flat 출력으로 언패킹하고, `M_AXI` flat 입력 응답을 `mst_resp` struct로 패킹합니다.
4. AXI4에는 ATOP 신호가 없으므로 slave AW channel의 내부 `atop` 필드는 `0`으로 고정합니다.
5. 변환된 struct와 `len_limit_i`를 사용해 원본 `axi_burst_splitter_gran`을 인스턴스화합니다.

---

## 사용 예시

Vivado IP Packager에서 `axi_burst_splitter_gran_wrapper`를 top module로 지정하면 `S_AXI` slave 및 `M_AXI` master AXI4 인터페이스를 추론할 수 있습니다.

```systemverilog
axi_burst_splitter_gran_wrapper #(
  .MAX_READ_TXNS  ( 4  ),
  .MAX_WRITE_TXNS ( 4  ),
  .AXI_ADDR_WIDTH ( 32 ),
  .AXI_DATA_WIDTH ( 64 ),
  .AXI_ID_WIDTH   ( 4  ),
  .AXI_USER_WIDTH ( 1  )
) i_burst_splitter (
  .aclk,
  .aresetn,
  .len_limit_i,
  // S_AXI flat 포트 연결
  // M_AXI flat 포트 연결
);
```
