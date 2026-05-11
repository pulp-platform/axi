# run_vsim.sh

## 파일 목적 및 개요

`run_vsim.sh`는 AXI IP 프로젝트의 각 테스트벤치를 **ModelSim/QuestaSim (`vsim`)** 으로 실행하는 회귀 테스트 스크립트입니다. ETH Zurich / University of Bologna가 개발하였으며 Solderpad Hardware License v0.51 하에 배포됩니다.

`test/` 디렉터리에서 `tb_*.sv` 파일들을 자동 탐색하거나, 인자로 지정한 테스트만 선택적으로 실행할 수 있습니다. 각 테스트벤치는 다양한 파라미터 조합으로 실행되며, 시드(seed) 기반 랜덤 회귀 테스트도 지원합니다. `run_verilator.sh`와 동일한 테스트 커버리지를 vsim 환경에서 제공하도록 설계되었습니다.

---

## 주요 파라미터 / 변수 설명

### 환경 변수

| 변수 | 기본값 | 설명 |
|---|---|---|
| `VSIM` | `vsim` | 사용할 vsim 실행 파일 경로. 환경 변수로 재정의 가능. |
| `ROOT` | 스크립트 위치 기준 상위 디렉터리 | 프로젝트 루트 경로. 자동 계산. |

### 스크립트 내부 변수

| 변수 | 기본값 | 설명 |
|---|---|---|
| `SEEDS` | `(0)` | 랜덤화 시드 배열. 기본값 0은 항상 포함(회귀 일관성 보장). `--random-seed` 플래그로 추가 가능. |

### 명령줄 플래그

| 플래그 | 설명 |
|---|---|
| `--random-seed` | SEEDS 배열에 `random` 추가. 실행 시마다 `$RANDOM`으로 무작위 시드 사용. |
| `[테스트명 ...]` | 실행할 DUT 이름 목록. 생략 시 `test/tb_*.sv` 전체를 자동 탐색. |

### vsim 주요 옵션

| 옵션 | 설명 |
|---|---|
| `-sv_seed <N>` | SystemVerilog 시뮬레이션 시드 설정 |
| `-c` | 커맨드라인(배치) 모드 실행 |
| `-t 1ns` / `-t 1ps` | 타임스텝 설정 |
| `-coverage` | 코드 커버리지 수집 활성화 |
| `-classdebug` | 클래스 디버그 활성화 |
| `-voptargs="+acc +cover=bcesfx"` | 커버리지 범위 설정 (브랜치/조건/식/문장/FSM/토글) |
| `-g<ParamName>=<val>` | 탑-레벨 제네릭/파라미터 재정의 |

---

## 내부 로직 / 단계 설명

### 핵심 함수: `call_vsim [vsim 인자...]`

1. `SEEDS` 배열의 각 시드에 대해 반복:
   - `echo "run -all" | $VSIM -sv_seed $seed "$@"` 명령으로 시뮬레이션 실행.
   - 실행 결과를 `vsim.log`에 저장.
   - `grep "Errors: 0,"` 으로 오류 없음 확인 (실패 시 스크립트 종료).

### 핵심 함수: `exec_test <dut_name>`

- `test/tb_{dut_name}.sv` 파일 존재 여부 확인.
- DUT 이름에 따라 `case` 분기로 파라미터 조합을 결정하고 `call_vsim` 호출.

### 지원 테스트 및 파라미터 조합

| 테스트 | 파라미터 조합 | 특이 사항 |
|---|---|---|
| `axi_atop_filter` | `TB_AXI_MAX_WRITE_TXNS` = 1, 3, 12 | |
| `axi_cdc`, `axi_delayer` | 파라미터 없음 | |
| `axi_dw_downsizer` | Slv/Mst 데이터폭 다중 조합 | `-t 1ps`, BStall/RStall 스트레스 케이스 포함 |
| `axi_dw_upsizer` | Slv/Mst 데이터폭 조합 (8~1024) | `-t 1ps` |
| `axi_fifo` | Depth (0,1,16) × FallThrough (0,1) | |
| `axi_iw_converter` | SlvPortIdWidth, MstPortIdWidth, MaxUniqIds, Exclusive 다중 조합 | `-coverage -classdebug -voptargs` 포함 |
| `axi_lite_regs` | PrivProtOnly, SecuProtOnly, RegNumBytes 다중 조합 | 시드 (0, 10, 42) 추가 |
| `axi_lite_to_apb` | PipelineRequest × PipelineResponse | |
| `axi_lite_to_axi` | 데이터폭 (8~1024) | `-t 1ps` |
| `axi_sim_mem` | AddrWidth (16,32,64) × DataWidth (32~1024) | `-t 1ps` |
| `axi_xbar` | NumMasters, NumSlaves, EnAtop, EnExcl, UniqueIds 다중 조합 (첫 번째 case) | 두 번째 case에 추가 파라미터 조합도 정의됨 |
| `axi_to_mem_banked` | MemLatency, BankFactor, NumBanks, AXI_DATA_WIDTH 다중 조합 | `-voptargs="+acc +cover=bcesfx"` |
| `axi_lite_dw_converter` | SlvDataWidth × MstDataWidth | |
| 기타 | 파라미터 없음 | `-t 1ns -coverage -voptargs="+acc +cover=bcesfx"` |

---

## Mermaid 블록 다이어그램 (흐름도)

```mermaid
flowchart TD
    A([스크립트 시작]) --> B[set -euo pipefail\nROOT 경로 계산]
    B --> C[VSIM 환경변수 확인]
    C --> D[SEEDS=0 초기화]
    D --> E[인자 파싱\n--random-seed 처리]
    E --> F{인자로\n테스트 이름 지정?}
    F -- 예 --> G[지정된 테스트 목록 사용]
    F -- 아니오 --> H[find ROOT/test tb_*.sv\n전체 테스트 자동 탐색]
    G & H --> I[for t in tests:\nexec_test t]
    I --> J{tb_t.sv\n존재?}
    J -- 아니오 --> K([오류 종료: testbench not found])
    J -- 예 --> L[case 분기:\n파라미터 조합 결정]
    L --> M[call_vsim tb_name\n파라미터 인자들]
    M --> N[for seed in SEEDS:\necho run -all | vsim -sv_seed N\n→ vsim.log]
    N --> O{grep Errors: 0,\n성공?}
    O -- 실패 --> P([오류 종료])
    O -- 성공 --> Q{모든 시드\n완료?}
    Q -- 아니오 --> N
    Q -- 예 --> R{모든 파라미터\n조합 완료?}
    R -- 아니오 --> M
    R -- 예 --> S{모든 테스트\n완료?}
    S -- 아니오 --> I
    S -- 예 --> T([정상 종료])
```

---

## 사용 방법 및 예시

### 모든 테스트 실행

```bash
cd /home/user/axi
bash scripts/run_vsim.sh
```

### 특정 테스트만 실행

```bash
bash scripts/run_vsim.sh axi_fifo
bash scripts/run_vsim.sh axi_xbar axi_cdc
```

### 랜덤 시드 추가 실행

```bash
bash scripts/run_vsim.sh --random-seed axi_lite_regs
```

### 특정 vsim 실행 파일 지정

```bash
VSIM=/opt/questasim/bin/vsim bash scripts/run_vsim.sh
```

### 사전 요구 사항

- `scripts/compile_vsim.sh` 실행으로 라이브러리 컴파일이 먼저 완료되어야 합니다.
- **vsim (ModelSim / QuestaSim)**: PATH에 존재하거나 `VSIM` 환경 변수로 지정.
- `test/tb_*.sv` 테스트벤치 파일이 존재해야 합니다.

### 생성 파일

| 파일 | 내용 |
|---|---|
| `vsim.log` | 마지막으로 실행된 시뮬레이션 로그 |

### run_verilator.sh와의 차이점

| 항목 | run_verilator.sh | run_vsim.sh |
|---|---|---|
| 시뮬레이터 | Verilator (오픈소스) | ModelSim/QuestaSim (상용) |
| 컴파일 방식 | 각 TB마다 컴파일 후 실행 | compile_vsim.sh로 사전 컴파일 필요 |
| 커버리지 | 미지원 | `-coverage -voptargs` 옵션 지원 |
| 타임스케일 | `--timing` 플래그 | `-t 1ns/1ps` 옵션 |
