# axi_lite_regs_wrapper.sv

## 파일 목적 및 개요

`axi_lite_regs_wrapper`는 `axi_lite_regs` 모듈을 AMD Vivado Custom IP로 패키징하기 쉽도록 만든 flat-port 래퍼입니다.

원본 `axi_lite_regs`는 내부적으로 AXI4-Lite request/response 구조체와 byte 배열 포트를 사용하지만, Vivado IP Packager는 AXI4-Lite 인터페이스를 `s_axi_*` 형태의 개별 포트로 노출하는 구성을 더 잘 인식합니다. 이 래퍼는 다음을 제공합니다.

- `s_axi_aclk`, `s_axi_aresetn` 클럭/리셋 포트
- Vivado AXI4-Lite 인터페이스 추론용 `X_INTERFACE_INFO` / `X_INTERFACE_PARAMETER` 속성
- `s_axi_aw*`, `s_axi_w*`, `s_axi_b*`, `s_axi_ar*`, `s_axi_r*` flat AXI4-Lite slave 포트
- `reg_d_i` / `reg_q_o` byte 배열을 packed vector로 노출하는 변환 로직
- packed `REG_RST_VAL` 파라미터를 원본 모듈의 unpacked byte 배열 파라미터로 변환하는 helper function

---

## 주요 파라미터

| 파라미터 | 기본값 | 설명 |
|---|---:|---|
| `REG_NUM_BYTES` | `32` | 레지스터 필드 크기(바이트 단위) |
| `AXI_ADDR_WIDTH` | `32` | AXI4-Lite 주소 폭 |
| `AXI_DATA_WIDTH` | `32` | AXI4-Lite 데이터 폭 |
| `PRIV_PROT_ONLY` | `0` | privileged access만 허용할지 여부 |
| `SECU_PROT_ONLY` | `0` | secure access만 허용할지 여부 |
| `AXI_READ_ONLY` | all `0` | byte별 AXI 쓰기 금지 설정 |
| `REG_RST_VAL` | all `8'h00` | byte 0이 `[7:0]`에 위치하는 packed reset 값 |

---

## 포트 구성

### AMD Vivado AXI4-Lite slave 포트

`S_AXI` 인터페이스로 인식될 수 있도록 다음 flat 포트를 제공합니다.

- Write address: `s_axi_awaddr`, `s_axi_awprot`, `s_axi_awvalid`, `s_axi_awready`
- Write data: `s_axi_wdata`, `s_axi_wstrb`, `s_axi_wvalid`, `s_axi_wready`
- Write response: `s_axi_bresp`, `s_axi_bvalid`, `s_axi_bready`
- Read address: `s_axi_araddr`, `s_axi_arprot`, `s_axi_arvalid`, `s_axi_arready`
- Read data/response: `s_axi_rdata`, `s_axi_rresp`, `s_axi_rvalid`, `s_axi_rready`

### 레지스터 sideband 포트

| 포트 | 방향 | 설명 |
|---|---|---|
| `wr_active_o` | output | AXI 쓰기가 현재 cycle에 접근한 byte 표시 |
| `rd_active_o` | output | AXI 읽기가 현재 cycle에 접근한 byte 표시 |
| `reg_d_i` | input | byte 0이 `[7:0]`인 packed direct-load 입력값 |
| `reg_load_i` | input | byte별 direct-load enable |
| `reg_q_o` | output | byte 0이 `[7:0]`인 packed 레지스터 출력값 |

---

## 내부 동작

1. AXI4-Lite flat 포트를 `req_lite_t` / `resp_lite_t` 구조체에 수동 연결합니다.
2. `reg_d_i` packed vector를 byte 배열 `reg_d`로 변환합니다.
3. `axi_lite_regs`의 byte 배열 출력 `reg_q`를 packed vector `reg_q_o`로 변환합니다.
4. packed 파라미터 `REG_RST_VAL`은 `unpack_bytes()` 함수로 byte 배열 localparam `REG_RST_VAL_UNPACKED`가 됩니다.
5. 변환된 구조체/배열 신호로 원본 `axi_lite_regs`를 인스턴스화합니다.

---

## 사용 예시

Vivado IP Packager에서 `axi_lite_regs_wrapper`를 top module로 지정하면 `S_AXI` AXI4-Lite slave 인터페이스를 추론할 수 있습니다.

```systemverilog
axi_lite_regs_wrapper #(
  .REG_NUM_BYTES  ( 32 ),
  .AXI_ADDR_WIDTH ( 32 ),
  .AXI_DATA_WIDTH ( 32 )
) i_regs (
  .s_axi_aclk,
  .s_axi_aresetn,
  // s_axi_* AXI4-Lite 포트 연결
  .wr_active_o,
  .rd_active_o,
  .reg_d_i,
  .reg_load_i,
  .reg_q_o
);
```
