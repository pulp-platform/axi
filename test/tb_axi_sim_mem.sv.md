# tb_axi_sim_mem.sv

## 개요

`axi_sim_mem` 모듈의 테스트벤치입니다. 시뮬레이션용 AXI 메모리 모델의 올바른 동작(읽기/쓰기, 초기화되지 않은 데이터 경고 등)을 검증합니다.

## 테스트 구성

```mermaid
graph LR
    subgraph tb_axi_sim_mem
        DRV["axi_driver<br/>(AXI 드라이버)"]
        DUT["axi_sim_mem<br/>(시뮬레이션 메모리 DUT)"]
    end

    DRV -->|AXI 트랜잭션| DUT
    DUT -->|읽기 데이터| DRV
```

## 파라미터

| 파라미터 | 기본값 | 설명 |
|---------|--------|------|
| `TbTclk` | 10ns | 클록 주기 |
| `TbAddrWidth` | 64 | 주소 폭 |
| `TbDataWidth` | 128 | 데이터 폭 |
| `TbIdWidth` | 6 | ID 폭 |
| `TbUserWidth` | 2 | 사용자 신호 폭 |
| `TbWarnUninitialized` | `1'b0` | 초기화되지 않은 메모리 경고 |
| `TbApplDelay` | 2ns | 신호 적용 지연 |
| `TbAcqDelay` | 8ns | 신호 획득 지연 |

## 검증 시나리오

```mermaid
sequenceDiagram
    participant D as axi_driver
    participant M as axi_sim_mem

    D->>M: 쓰기 요청 (AW + W)
    M-->>D: B (쓰기 응답)
    D->>M: 읽기 요청 (AR)
    M-->>D: R (이전 쓰기 데이터 반환)
    Note over M: TbWarnUninitialized=1 시<br/>초기화 전 읽기 경고 출력
```

## 테스트 시나리오

1. `axi_driver`로 임의 주소에 쓰기 트랜잭션 생성
2. `axi_sim_mem`이 데이터 저장
3. 동일 주소 읽기 트랜잭션으로 저장된 데이터 검증
4. 초기화 전 읽기 시 경고 동작 확인 (TbWarnUninitialized=1)
5. 버스트 읽기/쓰기 트랜잭션 지원 검증

## 검증 대상

`axi_sim_mem`: 시뮬레이션 전용 AXI 메모리 모델 (지연 없는 반응)

## 의존성

- `axi/assign.svh`, `axi/typedef.svh`
- `axi_test` (axi_driver)
- `clk_rst_gen` (common_verification)
