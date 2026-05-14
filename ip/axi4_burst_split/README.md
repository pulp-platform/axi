# axi4_burst_split AMD Custom IP

이 디렉토리는 `src/axi4_burst_split.sv`를 **복사하지 않고 경로 참조 방식**으로 Vivado AMD Custom IP로 패키징하기 위한 스크립트를 제공합니다.

## 구성
- `package_ip.tcl`: Vivado IP packager 실행 스크립트
- `files.f`: 참조하는 소스 경로 목록(복사 없음)

## 사용 방법
Vivado Tcl 콘솔에서:

```tcl
cd <repo>/ip/axi4_burst_split
source package_ip.tcl
```

패키징 결과는 `ip/axi4_burst_split/build/axi4_burst_split_ip/packaged` 아래에 생성됩니다.
