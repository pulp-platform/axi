# axi_inval_filter

## 모듈 개요 및 기능

`axi_inval_filter`는 AXI4 버스에서 AW(Write Address) 채널을 모니터링하여 캐시 무효화(cache invalidation) 요청을 생성하는 모듈입니다. 나머지 채널(W, B, AR, R)은 Slave 포트에서 Master 포트로 투명하게 통과(pass-through)됩니다.

주요 동작:
- AW 트랜잭션이 수락될 때 AW 채널 정보를 내부 FIFO에 저장
- FSM이 FIFO에서 AW 정보를 꺼내 L1 캐시 라인 크기 단위로 연속적인 캐시 무효화 주소를 발행
- 버스트 트랜잭션이 캐시 라인 경계를 넘으면 여러 번의 무효화 요청을 순차 발행
- `en_i` 신호로 무효화 기능 활성화/비활성화 가능

---

## Mermaid 블록 다이어그램

```mermaid
block-betting
  columns 5

  SLV["슬레이브 포트\n(slv_req_i / slv_resp_o)"]
  space
  CORE["axi_inval_filter\n내부 로직"]
  space
  MST["마스터 포트\n(mst_req_o / mst_resp_i)"]

  space:5

  space:2
  FIFO["fifo_v3\n(AW FIFO\nDepth=MaxTxns)"]
  space
  INV["캐시 무효화 출력\n(inval_addr_o\ninval_valid_o\ninval_ready_i)"]

  space:5

  space:2
  FSM["FSM\n(Idle / Invalidating)"]

  SLV --> CORE
  CORE --> MST
  CORE --> FIFO
  FIFO --> FSM
  FSM --> INV
```

> **클록 도메인:** 단일 클록 도메인 (`clk_i`). 비동기 리셋 (`rst_ni`, active low).

---

## 파라미터 테이블

| 이름 | 타입 | 기본값 | 설명 |
|------|------|--------|------|
| `MaxTxns` | `int unsigned` | `0` | AW FIFO 깊이 (동시 진행 중인 최대 쓰기 버스트 수) |
| `AddrWidth` | `int unsigned` | `0` | AXI 주소 폭 (비트) |
| `L1LineWidth` | `int unsigned` | `0` | L1 캐시 라인 크기 (바이트) |
| `aw_chan_t` | `type` | `logic` | AXI AW 채널 구조체 타입 |
| `req_t` | `type` | `logic` | AXI 요청 구조체 타입 |
| `resp_t` | `type` | `logic` | AXI 응답 구조체 타입 |

---

## 포트 테이블

| 이름 | 방향 | 폭 | 설명 |
|------|------|----|------|
| `clk_i` | input | 1 | 클록 |
| `rst_ni` | input | 1 | 비동기 리셋 (active low) |
| `en_i` | input | 1 | 무효화 기능 활성화 |
| `slv_req_i` | input | `req_t` | Slave 포트 AXI 요청 |
| `slv_resp_o` | output | `resp_t` | Slave 포트 AXI 응답 |
| `mst_req_o` | output | `req_t` | Master 포트 AXI 요청 |
| `mst_resp_i` | input | `resp_t` | Master 포트 AXI 응답 |
| `inval_addr_o` | output | `AddrWidth` | 캐시 무효화 대상 주소 |
| `inval_valid_o` | output | 1 | 무효화 요청 유효 신호 |
| `inval_ready_i` | input | 1 | 무효화 요청 수락 신호 |

---

## 내부 아키텍처 설명

### AXI 핸들링 (axi 블록)

기본 동작은 완전 pass-through (`mst_req_o = slv_req_i`, `slv_resp_o = mst_resp_i`).

AW FIFO가 가득 찬 경우:
- `slv_resp_o.aw_ready = 0`: 슬레이브 포트의 새 AW 트랜잭션 차단
- `mst_req_o.aw_valid = 0`: 마스터 포트로의 AW 전달 차단

### AW FIFO 제어

- PUSH 조건: `en_i & slv_req_i.aw_valid & slv_resp_o.aw_ready` (AW 트랜잭션이 수락될 때)
- FALL_THROUGH=1 (즉시 출력)
- 깊이: `MaxTxns`

### 무효화 FSM (inval_fsm)

```
        fifo_empty=0 && inval_ready_i
Idle ──────────────────────────────────> Idle (단일 라인 버스트)
  │                                       또는
  │  addr 미정렬 또는 버스트 크기 > L1LineWidth
  └────────────────────────────────────> Invalidating
                    │
                    │ inval_ready_i & offset >= 버스트 크기
                    └──────────────────> Idle (FIFO POP)
```

**Idle 상태:**
- FIFO가 비어 있지 않고 `inval_ready_i`이면:
  - 버스트가 첫 라인에서 완료되면 FIFO POP
  - 미정렬이거나 버스트가 라인을 넘으면 Invalidating 상태로 전환, `inval_offset = L1LineWidth - 주소_오프셋`

**Invalidating 상태:**
- `inval_ready_i`마다 `inval_offset += L1LineWidth`
- `inval_offset >= 버스트_총_바이트`이면 Idle 복귀 및 FIFO POP

### 무효화 주소 계산

```
inval_addr_o = aw_fifo_data.addr + inval_offset_q
```

---

## 인스턴스화하는 서브모듈 목록

| 서브모듈 | 인스턴스 이름 | 역할 |
|----------|--------------|------|
| `fifo_v3` | `i_aw_fifo` | AW 채널 정보 저장 FIFO |

---

## 타이밍/레이턴시 특성

- AXI 채널(W, B, AR, R): 완전 조합 pass-through, **0 사이클 레이턴시**
- AW 채널: pass-through이나 FIFO full 시 차단
- 무효화 요청: AW 수락 후 FIFO 출력까지 0 사이클(FALL_THROUGH=1), 이후 FSM 처리 시작
- 단일 라인 무효화: 1사이클 처리
- 다중 라인 무효화: L1 라인 수만큼 사이클 소요 (inval_ready_i 의존)

---

## 특수 동작

- **미정렬 주소 처리**: 버스트 시작 주소가 캐시 라인에 정렬되지 않은 경우, 첫 번째 무효화는 주소 시작부터 해당 라인 끝까지, 이후 L1LineWidth 단위로 무효화
- **`en_i=0`**: FIFO push가 발생하지 않아 무효화 요청 생성 없음. AXI 트래픽은 정상 pass-through
- **버스트 크기 계산**: `(aw_len + 1) << aw_size`로 총 전송 바이트 계산
