# axi_intf

## 모듈 개요 및 기능

`axi_intf.sv`는 AXI4 및 AXI4-Lite 프로토콜을 위한 SystemVerilog **인터페이스(interface)** 정의 모음 파일입니다. 개별 로직 신호를 묶어 재사용 가능한 인터페이스 타입으로 제공합니다.

포함된 인터페이스:

| 인터페이스 이름 | 설명 |
|----------------|------|
| `AXI_BUS` | 표준 AXI4 Full 동기 인터페이스 |
| `AXI_BUS_DV` | 설계 검증용 클록 기반 AXI4 인터페이스 (AXI 프로토콜 assertion 포함) |
| `AXI_BUS_ASYNC` | 비동기 AXI4 인터페이스 (write/read token 기반 핸드쉐이크) |
| `AXI_BUS_ASYNC_GRAY` | Gray code CDC용 비동기 AXI4 인터페이스 (FIFO 배열 + 포인터 방식) |
| `AXI_LITE` | AXI4-Lite 동기 인터페이스 |
| `AXI_LITE_DV` | 설계 검증용 클록 기반 AXI4-Lite 인터페이스 |
| `AXI_LITE_ASYNC_GRAY` | Gray code CDC용 비동기 AXI4-Lite 인터페이스 |

---

## Mermaid 블록 다이어그램

```mermaid
block-betting
  columns 3

  subgraph AXI_BUS["AXI_BUS / AXI_BUS_DV"]
    direction TB
    AW["AW 채널\n(id, addr, len, size,\nburst, lock, cache,\nprot, qos, region,\natop, user, valid, ready)"]
    W["W 채널\n(data, strb, last,\nuser, valid, ready)"]
    B["B 채널\n(id, resp, user,\nvalid, ready)"]
    AR["AR 채널\n(id, addr, len, size,\nburst, lock, cache,\nprot, qos, region,\nuser, valid, ready)"]
    R["R 채널\n(id, data, resp, last,\nuser, valid, ready)"]
  end
```

### 인터페이스별 modport 구조

```mermaid
block-betting
  columns 3

  M["Master modport\n(AW/W/AR: output\nB/R: input)"]
  S["Slave modport\n(AW/W/AR: input\nB/R: output)"]
  MON["Monitor modport\n(모든 신호: input)"]
```

---

## 파라미터 테이블

### AXI_BUS / AXI_BUS_DV

| 이름 | 타입 | 기본값 | 설명 |
|------|------|--------|------|
| `AXI_ADDR_WIDTH` | `int unsigned` | `0` | 주소 폭 |
| `AXI_DATA_WIDTH` | `int unsigned` | `0` | 데이터 폭 |
| `AXI_ID_WIDTH` | `int unsigned` | `0` | ID 폭 |
| `AXI_USER_WIDTH` | `int unsigned` | `0` | User 신호 폭 |

### AXI_BUS_ASYNC

| 이름 | 타입 | 기본값 | 설명 |
|------|------|--------|------|
| `AXI_ADDR_WIDTH` | `int unsigned` | `0` | 주소 폭 |
| `AXI_DATA_WIDTH` | `int unsigned` | `0` | 데이터 폭 |
| `AXI_ID_WIDTH` | `int unsigned` | `0` | ID 폭 |
| `AXI_USER_WIDTH` | `int unsigned` | `0` | User 신호 폭 |
| `BUFFER_WIDTH` | `int unsigned` | `0` | 토큰(포인터) 폭 |

### AXI_BUS_ASYNC_GRAY / AXI_LITE_ASYNC_GRAY

| 이름 | 타입 | 기본값 | 설명 |
|------|------|--------|------|
| `AXI_ADDR_WIDTH` | `int unsigned` | `0` | 주소 폭 |
| `AXI_DATA_WIDTH` | `int unsigned` | `0` | 데이터 폭 |
| `AXI_ID_WIDTH` | `int unsigned` | `0` | ID 폭 (GRAY 버전) |
| `AXI_USER_WIDTH` | `int unsigned` | `0` | User 신호 폭 |
| `LOG_DEPTH` | `int unsigned` | `0` | FIFO 깊이 log2 값 (2^LOG_DEPTH 엔트리) |

### AXI_LITE / AXI_LITE_DV

| 이름 | 타입 | 기본값 | 설명 |
|------|------|--------|------|
| `AXI_ADDR_WIDTH` | `int unsigned` | `0` | 주소 폭 |
| `AXI_DATA_WIDTH` | `int unsigned` | `0` | 데이터 폭 |

---

## 포트 테이블

### AXI_BUS 신호 목록

| 채널 | 신호 이름 | 방향(Master) | 방향(Slave) | 폭 | 설명 |
|------|-----------|:---:|:---:|----|----|
| AW | `aw_id` | output | input | `AXI_ID_WIDTH` | 트랜잭션 ID |
| AW | `aw_addr` | output | input | `AXI_ADDR_WIDTH` | 시작 주소 |
| AW | `aw_len` | output | input | 8 | 버스트 길이 |
| AW | `aw_size` | output | input | 3 | 전송 크기 |
| AW | `aw_burst` | output | input | 2 | 버스트 타입 |
| AW | `aw_lock` | output | input | 1 | 잠금 타입 |
| AW | `aw_cache` | output | input | 4 | 메모리 특성 |
| AW | `aw_prot` | output | input | 3 | 보호 타입 |
| AW | `aw_qos` | output | input | 4 | QoS 식별자 |
| AW | `aw_region` | output | input | 4 | 리전 식별자 |
| AW | `aw_atop` | output | input | 6 | 원자 연산 타입 |
| AW | `aw_user` | output | input | `AXI_USER_WIDTH` | 사용자 신호 |
| AW | `aw_valid` | output | input | 1 | 유효 신호 |
| AW | `aw_ready` | input | output | 1 | 준비 신호 |
| W | `w_data` | output | input | `AXI_DATA_WIDTH` | 쓰기 데이터 |
| W | `w_strb` | output | input | `AXI_DATA_WIDTH/8` | 바이트 스트로브 |
| W | `w_last` | output | input | 1 | 마지막 버스트 비트 |
| W | `w_user` | output | input | `AXI_USER_WIDTH` | 사용자 신호 |
| W | `w_valid` | output | input | 1 | 유효 신호 |
| W | `w_ready` | input | output | 1 | 준비 신호 |
| B | `b_id` | input | output | `AXI_ID_WIDTH` | 응답 ID |
| B | `b_resp` | input | output | 2 | 응답 코드 |
| B | `b_user` | input | output | `AXI_USER_WIDTH` | 사용자 신호 |
| B | `b_valid` | input | output | 1 | 유효 신호 |
| B | `b_ready` | output | input | 1 | 준비 신호 |
| AR | `ar_id` | output | input | `AXI_ID_WIDTH` | 트랜잭션 ID |
| AR | `ar_addr` | output | input | `AXI_ADDR_WIDTH` | 시작 주소 |
| AR | `ar_len` | output | input | 8 | 버스트 길이 |
| AR | `ar_size` | output | input | 3 | 전송 크기 |
| AR | `ar_burst` | output | input | 2 | 버스트 타입 |
| AR | `ar_lock` | output | input | 1 | 잠금 타입 |
| AR | `ar_cache` | output | input | 4 | 메모리 특성 |
| AR | `ar_prot` | output | input | 3 | 보호 타입 |
| AR | `ar_qos` | output | input | 4 | QoS 식별자 |
| AR | `ar_region` | output | input | 4 | 리전 식별자 |
| AR | `ar_user` | output | input | `AXI_USER_WIDTH` | 사용자 신호 |
| AR | `ar_valid` | output | input | 1 | 유효 신호 |
| AR | `ar_ready` | input | output | 1 | 준비 신호 |
| R | `r_id` | input | output | `AXI_ID_WIDTH` | 데이터 ID |
| R | `r_data` | input | output | `AXI_DATA_WIDTH` | 읽기 데이터 |
| R | `r_resp` | input | output | 2 | 응답 코드 |
| R | `r_last` | input | output | 1 | 마지막 버스트 비트 |
| R | `r_user` | input | output | `AXI_USER_WIDTH` | 사용자 신호 |
| R | `r_valid` | input | output | 1 | 유효 신호 |
| R | `r_ready` | output | input | 1 | 준비 신호 |

---

## 내부 아키텍처 설명

### AXI_BUS_ASYNC

동기 valid/ready 핸드쉐이크 대신 write token / read pointer 쌍(`aw_writetoken`, `aw_readpointer` 등)으로 각 채널 제어. CDC(Clock Domain Crossing) 설계를 위한 비동기 인터페이스입니다.

### AXI_BUS_ASYNC_GRAY / AXI_LITE_ASYNC_GRAY

각 채널별로 2^LOG_DEPTH 엔트리 배열(`aw_data`, `w_data` 등)과 Gray code 포인터(`aw_wptr`, `aw_rptr` 등)를 가지는 FIFO 기반 CDC 인터페이스입니다.

### AXI_BUS_DV (설계 검증용)

클록 포트(`clk_i`)를 받아 아래 assertion을 내장합니다:
- AW/W/B/AR/R 각 채널: valid & !ready 사이클에서 모든 신호 안정성 보장
- INCR 버스트가 4KiB 경계를 넘지 않음 검증

---

## 인스턴스화하는 서브모듈 목록

없음 (인터페이스 정의 파일)

---

## 타이밍/레이턴시 특성

- `AXI_BUS`, `AXI_LITE`: 동기 valid/ready 핸드쉐이크. 연결 자체의 레이턴시 없음
- `AXI_BUS_ASYNC`: 비동기 토큰 기반 CDC. CDC 지연은 사용하는 CDC 회로에 의존
- `AXI_BUS_ASYNC_GRAY`: Gray code FIFO 기반. 2사이클 이상의 동기화 지연 예상

---

## 특수 동작

- `AXI_BUS_DV`와 `AXI_LITE_DV`의 assertion은 `pragma translate_off`로 감싸져 합성에서 제외
- 4KiB 버스트 경계 위반 assertion: INCR 버스트에서만 적용 (`aw_burst != BURST_INCR`이면 스킵)
- `AXI_BUS_ASYNC_GRAY`와 `AXI_LITE_ASYNC_GRAY`는 `axi/typedef.svh`로부터 채널 구조체 타입 정의를 include하여 사용
