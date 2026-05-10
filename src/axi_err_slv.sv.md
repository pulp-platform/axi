# `axi_err_slv` — AXI 에러 슬레이브

## 모듈 개요 및 기능

`axi_err_slv`는 수신된 모든 AXI4 트랜잭션에 대해 **에러 응답(DECERR 또는 SLVERR)**을 반환하는 더미 슬레이브입니다. 주소 디코더에서 매핑되지 않은 주소 영역에 배치되어 잘못된 접근에 대한 프로토콜 준수 에러 응답을 보장합니다.

`ATOPs=1`이면 내부에 `axi_atop_filter`를 인스턴스화하여 원자 연산도 올바르게 처리합니다.

---

## Mermaid 블록 다이어그램

```mermaid
block-betty
  columns 3

  slv["슬레이브 포트\nslv_req_i / slv_resp_o"]
  space
  resp["에러 응답 생성 로직\n(B: DECERR/SLVERR\n R: RespData + DECERR/SLVERR)"]

  block:internal:1
    columns 1
    atop["axi_atop_filter\n(ATOPs=1일 때)"]
    w_fifo["fifo_v3 (W)\n트랜잭션 ID 버퍼"]
    b_fifo["fifo_v3 (B)\n응답 ID 큐"]
    r_fifo["fifo_v3 (R)\n{ID, len} 큐"]
    r_cnt["counter\nR 비트 카운터"]
  end

  slv --> atop
  atop --> w_fifo
  w_fifo --> b_fifo
  b_fifo --> resp
  slv --> r_fifo
  r_fifo --> r_cnt
  r_cnt --> resp
  resp --> slv
```

---

## 파라미터 테이블

| 이름 | 타입 | 기본값 | 설명 |
|---|---|---|---|
| `AxiIdWidth` | `int unsigned` | `0` | AXI ID 폭 |
| `axi_req_t` | `type` | `logic` | AXI 요청 구조체 타입 |
| `axi_resp_t` | `type` | `logic` | AXI 응답 구조체 타입 |
| `Resp` | `axi_pkg::resp_t` | `RESP_DECERR` | 반환할 에러 응답 코드 |
| `RespWidth` | `int unsigned` | `32'd64` | R 응답 데이터 폭 |
| `RespData` | `logic [RespWidth-1:0]` | `64'hCA11AB1EBADCAB1E` | R 채널 반환 데이터값 |
| `ATOPs` | `bit` | `1'b1` | ATOP 지원 활성화 |
| `MaxTrans` | `int unsigned` | `1` | 버퍼링 가능한 최대 트랜잭션 수 |

---

## 포트 테이블

| 포트 이름 | 방향 | 폭 | 설명 |
|---|---|---|---|
| `clk_i` | input | 1 | 클록 |
| `rst_ni` | input | 1 | 비동기 리셋 (active-low) |
| `test_i` | input | 1 | 테스트 모드 활성화 |
| `slv_req_i` | input | `axi_req_t` | 슬레이브 포트 요청 입력 |
| `slv_resp_o` | output | `axi_resp_t` | 슬레이브 포트 응답 출력 |

---

## 내부 아키텍처

### ATOP 처리

- `ATOPs=1`: 내부에 `axi_atop_filter`를 삽입하여 ATOP 트랜잭션을 먼저 필터링
- `ATOPs=0`: 직결, ATOP 수신 시 어서션 오류

### 쓰기 트랜잭션 처리 흐름

```
AW 수신 → i_w_fifo (ID 저장, 최대 MaxTrans개)
W 비트 수신 → 흡수 (last W 감지 시) → i_b_fifo (ID 전달)
i_b_fifo 비어있지 않으면 → B 응답 생성 (resp=Resp, id=b_fifo_data)
```

### 읽기 트랜잭션 처리 흐름

```
AR 수신 → i_r_fifo ({id, len} 저장, 최대 MaxTrans개)
비지 상태가 아니고 r_fifo 비어있지 않으면:
  → r_busy 세트, r_counter에 len 로드
  → R 응답 버스트 생성 (data=RespData, resp=Resp)
  → r_beats_q가 0이 되면 last=1, r_fifo 팝
```

### R 비트 카운터

다운카운터로 버스트의 남은 비트 수를 추적하며 `r.last` 신호를 올바르게 생성합니다.

---

## 인스턴스화하는 서브모듈

| 인스턴스 이름 | 모듈 | 역할 |
|---|---|---|
| `i_atop_filter` | `axi_atop_filter` | ATOP 처리 (ATOPs=1) |
| `i_w_fifo` | `fifo_v3` | AW ID 버퍼 (fall-through, depth=MaxTrans) |
| `i_b_fifo` | `fifo_v3` | B 응답 ID 큐 (depth=2) |
| `i_r_fifo` | `fifo_v3` | AR {ID, len} 큐 (depth=MaxTrans) |
| `i_r_counter` | `counter` | R 버스트 비트 카운터 (다운카운터) |

---

## 타이밍/레이턴시 특성

- **쓰기**: AW 수신 후 W.last 감지 다음 사이클에 B 응답
- **읽기**: AR 수신 후 `len+1`개의 R 비트를 순차 발행
- **동시 트랜잭션**: 최대 `MaxTrans`개 AW/AR 버퍼링

---

## 특수 동작

- **R 응답 데이터**: `RespData`(기본값 `0xCA11AB1EBADCAB1E`)로 고정 반환
- **B 응답 코드**: `Resp` 파라미터 값(`RESP_DECERR` 또는 `RESP_SLVERR`)
- **마스터 포트 없음**: 슬레이브 포트만 존재, 모든 트랜잭션을 로컬 처리

### 어서션

- `Resp`는 반드시 `RESP_DECERR` 또는 `RESP_SLVERR`이어야 함
- `ATOPs=0`이면 ATOP 수신 시 시뮬레이션 `$fatal` 오류 발생
