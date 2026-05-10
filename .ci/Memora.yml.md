# .ci/Memora.yml

## 파일 개요 및 목적

`Memora.yml`은 **Memora** 빌드 캐시 시스템의 설정 파일입니다. Memora는 CI(지속적 통합) 파이프라인에서 빌드 아티팩트를 캐싱하여 불필요한 재빌드를 방지합니다. 각 아티팩트 항목은 입력 파일 집합과 출력 경로를 선언하고, 입력이 변경되지 않은 경우 캐시에서 출력을 재사용합니다.

이 파일은 `.gitlab-ci.yml`의 `memora_retry.sh lookup/insert` 호출과 연동되어 동작합니다.

---

## Mermaid 블록 다이어그램

```mermaid
graph TD
    subgraph Build[빌드 아티팩트]
        vsim["vsim-%<br/>(Questa/Vsim 컴파일)"]
        dc["synopsys_dc<br/>(Synopsys DC 합성)"]
    end

    subgraph Tests[테스트 아티팩트 (일부)]
        t1[axi_addr_test-%]
        t2[axi_atop_filter-%]
        t3[axi_cdc-%]
        t4[axi_delayer-%]
        t5[axi_dw_downsizer-%]
        t6[axi_dw_upsizer-%]
        t7["... (총 22개)"]
        t8[axi_xbar-%]
    end

    cache_root["캐시 루트<br/>/home/gitlabci/buildcache/axi"]
    cache_root --> vsim
    cache_root --> dc
    vsim --> t1
    vsim --> t2
    vsim --> t3
    vsim --> t4
    vsim --> t5
    vsim --> t6
    vsim --> t7
    vsim --> t8
```

---

## 주요 섹션/변수 설명 테이블

| 항목 | 설명 |
|------|------|
| `cache_root_dir` | 빌드 캐시가 저장되는 로컬 경로 (`/home/gitlabci/buildcache/axi`) |
| `artifacts` | 캐싱 대상 아티팩트 목록. 각 항목은 `inputs`와 `outputs`로 구성됨 |
| `vsim-%` | Questasim/Vsim 컴파일 결과물. `%`는 VSIM 버전 번호로 치환됨 |
| `synopsys_dc` | Synopsys Design Compiler 합성 결과물 |
| `axi_*-%` | 개별 AXI 모듈 시뮬레이션 테스트 결과물. `%`는 VSIM 버전 번호 |

### 공통 inputs 구성

| 입력 파일 | 역할 |
|-----------|------|
| `Bender.yml` | 외부 IP 의존성 선언 |
| `include/` | SystemVerilog 헤더 디렉토리 |
| `.gitlab-ci.yml` | 시뮬레이터/합성 툴 버전 정보 |
| `scripts/compile_vsim.sh` | vsim 컴파일 스크립트 |
| `scripts/run_vsim.sh` | vsim 실행 스크립트 |
| `src/axi_pkg.sv` | AXI 패키지 (모든 테스트에 공통 포함) |
| `src/axi_intf.sv` | AXI 인터페이스 (모든 테스트에 공통 포함) |
| `src/axi_test.sv` | AXI 테스트 인프라 (모든 테스트에 공통 포함) |
| `test/tb_<모듈명>.sv` | 해당 모듈의 테스트벤치 파일 |

### outputs 구성

| 아티팩트 | 출력 경로 |
|----------|----------|
| `vsim-%` | `build/work-<버전>` |
| `synopsys_dc` | `build/synth.completed` |
| `axi_*-%` | `build/<모듈명>-<버전>.tested` |

---

## 동작 방식 상세 설명

1. **캐시 조회 (`lookup`)**: CI 파이프라인에서 `memora_retry.sh lookup <아티팩트명>`을 실행. 입력 파일들의 해시를 계산하여 캐시 서버에서 동일한 해시의 결과물이 있는지 확인.
2. **캐시 히트**: 이미 캐시에 결과물이 있으면 재컴파일/재테스트 없이 `get` 명령으로 다운로드.
3. **캐시 미스**: 입력이 변경된 경우 실제 빌드/테스트를 수행하고, 완료 후 `insert` 명령으로 결과물을 캐시에 등록.
4. **와일드카드 `%`**: 아티팩트 이름의 `%`는 VSIM 버전 번호(예: `2025.1`)로 치환되어 버전별 캐시를 구분.

---

## 사용 방법 및 예시

Memora는 `.gitlab-ci.yml`에서 `memora_retry.sh` 스크립트를 통해 호출됩니다.

```bash
# 캐시 조회 (캐시 히트 시 0 반환, 미스 시 비-0 반환)
$CI_PROJECT_DIR/.gitlab-ci.d/memora_retry.sh lookup vsim-2025.1

# 캐시에서 아티팩트 다운로드
$CI_PROJECT_DIR/.gitlab-ci.d/memora_retry.sh get vsim-2025.1

# 빌드 후 캐시에 등록
$CI_PROJECT_DIR/.gitlab-ci.d/memora_retry.sh insert vsim-2025.1
```

### 전형적인 CI 사용 패턴 (`.gitlab-ci.yml` 발췌)

```yaml
- if ! memora_retry.sh lookup vsim-$VSIM_VER; then
    cd build && ../scripts/compile_vsim.sh && mv work{,-$VSIM_VER}
    memora_retry.sh insert vsim-$VSIM_VER
  fi
```

새로운 테스트 모듈을 추가할 때는 다음 형식으로 항목을 추가합니다:

```yaml
  axi_new_module-%:
    inputs:
      - Bender.yml
      - include
      - scripts/run_vsim.sh
      - src/axi_pkg.sv
      - src/axi_intf.sv
      - src/axi_test.sv
      - src/axi_new_module.sv
      - test/tb_axi_new_module.sv
    outputs:
      - build/axi_new_module-%.tested
```
