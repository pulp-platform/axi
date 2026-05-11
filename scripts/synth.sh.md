# synth.sh

## 파일 목적 및 개요

`synth.sh`는 AXI IP 프로젝트의 합성 타겟(`axi_synth_bench`)을 **Synopsys Design Compiler (`dc_shell`)** 을 사용하여 논리 합성(Logic Synthesis)하는 스크립트입니다. ETH Zurich / University of Bologna가 개발하였으며 Solderpad Hardware License v0.51 하에 배포됩니다.

주요 동작:
1. 합성용 Tcl 스크립트(`synth.tcl`)를 동적으로 생성합니다.
2. Synopsys Design Compiler를 호출하여 합성을 실행합니다.
3. 합성 로그에서 경고(warning)와 오류(error)를 검사합니다.
4. 합성 성공 시 `synth.completed` 완료 마커 파일을 생성합니다.

---

## 주요 파라미터 / 변수 설명

| 변수 / 파일 | 기본값 | 설명 |
|---|---|---|
| `SYNOPSYS_DC` | `synopsys dc_shell -64` | 사용할 Synopsys Design Compiler 실행 명령. 환경 변수로 재정의 가능. |
| `ROOT` | 스크립트 위치 기준 상위 디렉터리 | 프로젝트 루트 경로. 자동 계산. |
| `synth.tcl` | (생성 파일) | 합성에 사용되는 Tcl 스크립트. 실행 시마다 재생성. |
| `synth.log` | (생성 파일) | Design Compiler 실행 결과 로그. |
| `synth.completed` | (생성 파일) | 합성 성공 시 생성되는 완료 마커 파일 (`touch` 명령으로 생성). |

### synth.tcl 내용

| 명령 | 역할 |
|---|---|
| `remove_design -all` | 이전 합성 결과를 초기화 |
| `bender script synopsys -t synth_test` | 합성 타겟 파일 목록 및 설정을 Synopsys 형식으로 출력 |
| `elaborate axi_synth_bench` | `axi_synth_bench` 모듈을 합성용으로 정교화(Elaborate) |

---

## 내부 로직 / 단계 설명

1. **오류 즉시 종료 설정** (`set -e`): 어떤 명령이 실패해도 스크립트를 즉시 중단.
2. **루트 경로 계산**: `BASH_SOURCE[0]`를 기준으로 프로젝트 루트(`ROOT`)를 절대 경로로 설정.
3. **SYNOPSYS_DC 확인**: 환경 변수가 설정되지 않은 경우 `synopsys dc_shell -64`를 기본값으로 사용.
4. **synth.tcl 생성**:
   - `remove_design -all` 명령을 첫 줄로 작성.
   - `bender script synopsys -t synth_test`의 출력을 이어 붙임 (소스 파일 읽기 및 컴파일 명령 포함).
   - `elaborate axi_synth_bench` 명령을 마지막에 추가.
5. **Design Compiler 실행**: 생성된 `synth.tcl`을 파이프로 전달하여 dc_shell 실행. 결과를 `synth.log`에 동시 저장 (`tee`).
6. **로그 검사**:
   - `grep -i "warning:" synth.log || true`: 경고 출력 (오류 아님, 실패해도 계속 진행).
   - `grep -i "error:" synth.log && false`: 오류 발견 시 스크립트 강제 실패.
7. **완료 마커 생성**: `touch synth.completed` 으로 합성 성공을 표시.

---

## Mermaid 블록 다이어그램 (흐름도)

```mermaid
flowchart TD
    A([스크립트 시작]) --> B[set -e 설정\nROOT 경로 계산]
    B --> C{SYNOPSYS_DC\n환경 변수 설정?}
    C -- 예 --> D[환경 변수 사용]
    C -- 아니오 --> E[기본값:\nsynopsys dc_shell -64]
    D & E --> F[synth.tcl 생성 시작\nremove_design -all 작성]
    F --> G[bender script synopsys\n-t synth_test 출력\n→ synth.tcl 에 추가]
    G --> H[elaborate axi_synth_bench\n→ synth.tcl 에 추가]
    H --> I[cat synth.tcl\n| SYNOPSYS_DC\n| tee synth.log]
    I --> J{Design Compiler\n실행 성공?}
    J -- 실패 --> K([오류 종료])
    J -- 성공 --> L[grep -i warning: synth.log\n경고 출력 확인 - 비치명적]
    L --> M{grep -i error:\nsynth.log}
    M -- 오류 발견 --> N([오류 종료: && false])
    M -- 오류 없음 --> O[touch synth.completed\n완료 마커 생성]
    O --> P([정상 종료])
```

---

## 사용 방법 및 예시

### 기본 실행

```bash
cd /home/user/axi
bash scripts/synth.sh
```

### 특정 Design Compiler 경로 지정

```bash
SYNOPSYS_DC="/opt/synopsys/dc/bin/dc_shell -64" bash scripts/synth.sh
```

### 합성 성공 여부 확인

```bash
# synth.completed 파일 존재 시 합성 성공
ls -la synth.completed
```

### 합성 로그 확인

```bash
# 경고 목록 확인
grep -i "warning:" synth.log

# 오류 목록 확인
grep -i "error:" synth.log
```

### 사전 요구 사항

- **Synopsys Design Compiler**: `dc_shell` 또는 `SYNOPSYS_DC` 환경 변수로 지정한 실행 파일이 PATH에 존재해야 함.
- **bender**: `synopsys` 스크립트 출력을 위해 필요. PATH에 존재하거나 사전 설치 필요 (`scripts/install_tools.sh` 참조).
- 라이선스: Synopsys Design Compiler 라이선스 서버 접근 권한 필요.

### 생성 파일

| 파일 | 내용 |
|---|---|
| `synth.tcl` | 동적 생성되는 합성용 Tcl 스크립트 |
| `synth.log` | Design Compiler 실행 전체 로그 |
| `synth.completed` | 합성 성공 완료 마커 (빈 파일) |

### 주의 사항

- `synth.tcl`은 실행할 때마다 덮어씌워집니다.
- 오류(`error:`) 발생 시 `synth.completed` 파일이 생성되지 않으므로, CI/CD에서 완료 여부 확인에 활용할 수 있습니다.
- 경고(`warning:`)는 로그에 출력되지만 스크립트를 실패시키지 않습니다.
