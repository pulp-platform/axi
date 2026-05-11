# axi_rw_split.sv

## 개요

하나의 읽기/쓰기 슬레이브를 읽기 전용 마스터와 쓰기 전용 마스터로 분리하는 모듈입니다.

- 슬레이브의 AR, R 채널 → 읽기 마스터로 연결
- 슬레이브의 AW, W, B 채널 → 쓰기 마스터로 연결

## 블록 다이어그램

```mermaid
graph LR
    SLV["읽기/쓰기 슬레이브<br/>slv_req_i<br/>(AR/AW/W/R/B)"]

    subgraph axi_rw_split
        SPLIT["신호 직접 매핑<br/>(AR,R → 읽기 마스터)<br/>(AW,W,B → 쓰기 마스터)"]
    end

    RD_MST["읽기 마스터<br/>mst_read_req_o<br/>(AR/R 전용)"]
    WR_MST["쓰기 마스터<br/>mst_write_req_o<br/>(AW/W/B 전용)"]

    SLV --> SPLIT
    SPLIT -->|AR, R| RD_MST
    SPLIT -->|AW, W, B| WR_MST
```

## 파라미터

| 파라미터 | 타입 | 기본값 | 설명 |
|---------|------|--------|------|
| `axi_req_t` | `type` | `logic` | AXI4 요청 구조체 타입 |
| `axi_resp_t` | `type` | `logic` | AXI4 응답 구조체 타입 |

## 포트

| 포트 | 방향 | 설명 |
|------|------|------|
| `clk_i` | 입력 | 클록 |
| `rst_ni` | 입력 | 비동기 리셋 (액티브 로우) |
| `slv_req_i` | 입력 | 읽기/쓰기 슬레이브 요청 |
| `slv_resp_o` | 출력 | 슬레이브 응답 |
| `mst_read_req_o` | 출력 | 읽기 마스터 요청 (AR/R만 유효) |
| `mst_read_resp_i` | 입력 | 읽기 마스터 응답 |
| `mst_write_req_o` | 출력 | 쓰기 마스터 요청 (AW/W/B만 유효) |
| `mst_write_resp_i` | 입력 | 쓰기 마스터 응답 |

## 채널 연결 규칙

| 채널 | 소스 | 목적지 |
|------|------|--------|
| AR | `slv_req_i.ar` | `mst_read_req_o.ar` |
| R | `mst_read_resp_i.r` | `slv_resp_o.r` |
| AW | `slv_req_i.aw` | `mst_write_req_o.aw` |
| W | `slv_req_i.w` | `mst_write_req_o.w` |
| B | `mst_write_resp_i.b` | `slv_resp_o.b` |

어서션: 슬레이브의 AR이 읽기 마스터에서만, AW가 쓰기 마스터에서만 처리되도록 검증합니다.

## axi_rw_join과의 관계

`axi_rw_split`은 `axi_rw_join`의 역방향 연산입니다.

## 의존성

- `axi/assign.svh`
- `common_cells/assertions.svh`
