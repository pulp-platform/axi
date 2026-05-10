# .gitlab-ci.d/memora_retry.sh

## 파일 개요 및 목적

`memora_retry.sh`는 **Memora 캐시 명령의 재시도 래퍼 스크립트**입니다. Memora 명령 실행 시 네트워크 오류나 일시적 장애로 인해 실패할 수 있는 경우를 대비하여, 최대 10회까지 자동으로 재시도합니다. `.gitlab-ci.yml`의 모든 `memora` 호출은 이 스크립트를 통해 이루어집니다.

---

## Mermaid 블록 다이어그램

```mermaid
flowchart TD
    A[시작: memora_retry.sh 인수...] --> B[i=1, max_attempts=10]
    B --> C["memora 인수... 실행"]
    C -->|성공 (exit 0)| D[스크립트 정상 종료]
    C -->|실패 (exit 비0)| E["실패 메시지 출력\n'Attempt i/10 of memora... failed.'"]
    E --> F{i >= max_attempts?}
    F -->|예 (10회 초과)| G["중단 메시지 출력\n'keeps failing; aborting!'\nexit 1"]
    F -->|아니오| H[i = i + 1]
    H --> C
```

---

## 주요 섹션/변수/파라미터 설명 테이블

| 항목 | 값 | 설명 |
|------|-----|------|
| 인터프리터 | `/usr/bin/env bash` | bash 셸 스크립트 |
| `i` | 초기값 `1` | 현재 시도 횟수 |
| `max_attempts` | `10` | 최대 재시도 횟수 |
| `"$@"` | 모든 인수 전달 | `memora` 명령에 전달될 인수 (예: `lookup vsim-2025.1`) |
| 종료 코드 | `0` (성공) / `1` (최대 재시도 초과) | 스크립트 종료 상태 |

### memora 명령 유형

| 명령 | 설명 |
|------|------|
| `memora lookup <아티팩트>` | 캐시에 아티팩트가 있는지 확인 |
| `memora get <아티팩트>` | 캐시에서 아티팩트 다운로드 |
| `memora insert <아티팩트>` | 아티팩트를 캐시에 업로드/등록 |

---

## 동작 방식 상세 설명

스크립트는 단순하지만 견고한 재시도 루프를 구현합니다:

1. `while ! memora "$@"` 루프가 `memora` 명령을 실행합니다.
2. `memora`가 성공(exit code 0)하면 루프가 즉시 종료되고 스크립트도 정상 종료됩니다.
3. `memora`가 실패하면 현재 시도 번호와 최대 횟수를 출력합니다.
4. 현재 시도 횟수 `i`가 `max_attempts`(10)에 도달하면 오류 메시지 출력 후 `exit 1`로 종료합니다.
5. 아직 재시도 횟수가 남아 있으면 `i`를 증가시키고 다시 시도합니다.

**재시도 간 딜레이 없음**: 스크립트에는 `sleep` 명령이 없습니다. 실패 즉시 재시도합니다. 이는 캐시 서버가 일시적으로 바쁜 경우에만 효과적이며, 지속적인 오류에는 10번의 빠른 재시도 후 실패합니다.

---

## 사용 방법 및 예시

`.gitlab-ci.yml`에서의 호출 예시:

```bash
# 캐시 조회 - 캐시 미스 시 빌드 수행
if ! $CI_PROJECT_DIR/.gitlab-ci.d/memora_retry.sh lookup vsim-2025.1; then
    cd build && ../scripts/compile_vsim.sh
    $CI_PROJECT_DIR/.gitlab-ci.d/memora_retry.sh insert vsim-2025.1
fi

# 캐시에서 아티팩트 가져오기
$CI_PROJECT_DIR/.gitlab-ci.d/memora_retry.sh get vsim-2025.1
```

직접 실행 예시:

```bash
# 스크립트에 실행 권한 부여 후 사용
chmod +x .gitlab-ci.d/memora_retry.sh

# lookup 재시도 (최대 10회)
.gitlab-ci.d/memora_retry.sh lookup axi_xbar-2025.1

# insert 재시도 (빌드 후 캐시 등록)
.gitlab-ci.d/memora_retry.sh insert axi_xbar-2025.1
```

**실패 시 출력 예시**:
```
Attempt 1/10 of 'memora lookup vsim-2025.1' failed.
Attempt 2/10 of 'memora lookup vsim-2025.1' failed.
...
'memora lookup vsim-2025.1' keeps failing; aborting!
```
