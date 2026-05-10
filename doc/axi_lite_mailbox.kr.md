# AXI4-Lite Mailbox

`axi_lite_mailbox`은 하드웨어 메일박스를 구현하며, 두 개의 AXI4-Lite 슬레이브 포트가 두 개의 FIFO를 통해 서로 연결됩니다. 포트 0에 쓴 데이터는 포트 1의 읽기 데이터로 제공되고, 반대의 경우도 마찬가지입니다.
이 모듈은 각 포트에 대해 인터럽트를 지원하며, [IRQEN](#irqen-register) 레지스터로 활성화할 수 있습니다. 인터럽트는 읽기([RIRQT](#rirqt-register)) 및 쓰기([WIRQT](#wirqt-register)) FIFO의 채움 수준에 따라 트리거되도록 설정할 수 있습니다. 또한 [ERROR](#error-register) 레지스터에 정의된 메일박스 오류 조건에서 인터럽트를 트리거하는 것도 가능합니다.


## Module Parameters

이 표는 모듈의 파라미터를 설명합니다.

| Name           | Type           | Description                                                                                  |
|:---------------|:---------------|:---------------------------------------------------------------------------------------------|
| `MailboxDepth` | `int unsigned `| 두 슬레이브 포트 사이의 FIFO 깊이, 최솟값 `32'd2`                                             |
| `IrqEdgeTrig`  | `bit`          | 인터럽트 트리거 모드. <br/>[0]: 레벨 트리거 <br/>[1]: 엣지 트리거                              |
| `IrqActHigh`   | `bit`          | 인터럽트 극성. <br/>[0]: 액티브 로우 / 하강 엣지 <br/>[1]: 액티브 하이 / 상승 엣지             |
| `AxiAddrWidth` | `int unsigned` | AW 및 AR 채널의 AXI4-Lite 주소 폭                                                             |
| `AxiDataWidth` | `int unsigned` | W 및 R 채널의 AXI4-Lite 데이터 폭                                                             |
| `req_lite_t`   | `type`         | `AXI_LITE_TYPEDEF_REQ_T` 매크로에 따름                                                        |
| `resp_lite_t`  | `type`         | `AXI_LITE_TYPEDEF_RESP_T` 매크로에 따름                                                       |


## Module Ports

이 표는 모듈의 포트를 설명합니다.

| Name           | Type                       | Description                                            |
|:---------------|:---------------------------|:-------------------------------------------------------|
| `clk_i`        | `input  logic`             | 클럭                                                   |
| `rst_ni`       | `input  logic`             | 액티브 로우 비동기 리셋                                 |
| `test_i`       | `input  logic`             | 테스트 모드 활성화                                      |
| `slv_reqs_i`   | `input  req_lite_t  [1:0]` | 두 AXI4-Lite 포트의 요청                               |
| `slv_resps_o`  | `output resp_lite_t [1:0]` | 두 AXI4-Lite 포트의 응답                               |
| `irq_o`        | `output logic       [1:0]` | 각 포트의 인터럽트 출력                                 |
| `base_addr_i`  | `input  addr_t      [1:0]` | 각 포트의 베이스 주소                                   |



## Register Address Mapping

이 표는 레지스터의 종류와 각각의 주소 매핑을 설명합니다. 주소는 파라미터 `AxiDataWidth` 및 해당 인덱스와 연결된 포트의 `base_addr_i[*]`에 따라 결정됩니다.
`base_addr_i[*]`가 `'0`이고 `AxiDataWidth`가 32비트 및 64비트일 때의 결과 주소에 대한 두 가지 예시 열이 제공됩니다.
각 레지스터는 접근 유형 `R/W = 읽기 및 쓰기`, `R = 읽기 전용`, `W = 쓰기 전용` 중 하나를 가집니다. 읽기 전용 레지스터에 쓰기 또는 쓰기 전용 레지스터에서 읽기를 시도하면 `axi_pkg::RESP_SLVERR`로 응답합니다.

| Base Address + Offset\*AxiDataWidth/8 | Address for `AxiDataWidth = 32` | Address for `AxiDataWidth = 64` | Register Name                     | Access Type | Default Value | Description                       |
|:--------------------------------------|:-------------------------------:|:-------------------------------:|:---------------------------------:|:-----------:|:-------------:|:----------------------------------|
| base_addr_i + 0\*AxiDataWidth/8       | 0x00                            | 0x00                            | [MBOXW](#mboxw-register)          | W           | N/A           | 데이터 쓰기 주소                   |
| base_addr_i + 1\*AxiDataWidth/8       | 0x04                            | 0x08                            | [MBOXR](#mboxr-register)          | R           | N/A           | 데이터 읽기 주소                   |
| base_addr_i + 2\*AxiDataWidth/8       | 0x08                            | 0x10                            | [STATUS](#status-register)        | R           | `0x1`         | 메일박스 상태 플래그               |
| base_addr_i + 3\*AxiDataWidth/8       | 0x0C                            | 0x18                            | [ERROR](#error-register)          | R           | `0x0`         | 오류 플래그                        |
| base_addr_i + 4\*AxiDataWidth/8       | 0x10                            | 0x20                            | [WIRQT](#wirqt-register)          | R/W         | `0x0`         | 쓰기 데이터 인터럽트 임계값        |
| base_addr_i + 5\*AxiDataWidth/8       | 0x14                            | 0x28                            | [RIRQT](#rirqt-register)          | R/W         | `0x0`         | 읽기 데이터 인터럽트 임계값        |
| base_addr_i + 6\*AxiDataWidth/8       | 0x18                            | 0x30                            | [IRQS](#irqs-register)            | R/W         | `0x0`         | 인터럽트 상태 레지스터             |
| base_addr_i + 7\*AxiDataWidth/8       | 0x1C                            | 0x38                            | [IRQEN](#irqen-register)          | R/W         | `0x0`         | 인터럽트 활성화 레지스터           |
| base_addr_i + 8\*AxiDataWidth/8       | 0x20                            | 0x40                            | [IRQP](#irqp-register)            | R           | `0x0`         | 인터럽트 대기 레지스터             |
| base_addr_i + 9\*AxiDataWidth/8       | 0x24                            | 0x48                            | [CRTL](#ctrl-register)            | R/W         | `0x0`         | 모듈 제어 레지스터                 |


### MBOXW Register

메일박스 쓰기 레지스터. 여기에 쓰면 다른 슬레이브 포트로 데이터를 전송합니다. FIFO의 채움 포인터가 [WIRQT Register](#wirqt-register)를 초과하면 인터럽트 요청이 발생합니다(활성화된 경우).
FIFO가 가득 찬 경우 쓰기는 무시되고 `axi_pkg::RESP_SLVERR`가 반환됩니다. 아울러 [ERROR Register](#error-register)의 해당 비트가 설정됩니다.


### MBOXR Register

메일박스 읽기 레지스터. 여기서 읽으면 다른 슬레이브 포트로부터 데이터를 수신합니다. FIFO의 채움 포인터가 [RIRQT Register](#rirqt-register)를 초과하면 인터럽트 요청이 발생합니다(활성화된 경우).
FIFO가 비어 있는 경우 읽기 응답으로 `axi_pkg::RESP_SLVERR`가 반환됩니다. 아울러 [ERROR Register](#error-register)의 해당 비트가 설정됩니다.


### STATUS Register

메일박스 상태 레지스터. 이 읽기 전용 레지스터는 메일박스의 현재 상태를 나타냅니다.

| Bit(s)             | Name     | Access Type | Reset Value | Description                                                                                                                                                                                |
|:------------------:|:--------:|:-----------:|:-----------:|:-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| `AxiDataWidth-1:4` | Reserved |             |             | 예약됨                                                                                                                                                                                     |
| `3`                | RFIFOL   | R           | `1'b0`      | 읽기 FIFO 수준이 `RIRQT`에 설정된 임계값보다 높음 <br/>[0]: 읽기 FIFO 수준이 임계값 이하. <br/>[1]: 읽기 FIFO 수준이 임계값 초과.                                                          |
| `2`                | WFIFOL   | R           | `1'b0`      | 쓰기 FIFO 수준이 `WIRQT`에 설정된 임계값보다 높음 <br/>[0]: 쓰기 FIFO 수준이 임계값 이하. <br/>[1]: 쓰기 FIFO 수준이 임계값 초과.                                                          |
| `1`                | Full     | R           | `1'b0`      | 쓰기 FIFO가 가득 차서 이후 메일박스 쓰기가 무시됨 <br/>[0]: 쓰기 데이터를 위한 공간 있음. <br/>[1]: 데이터를 위한 공간 없음. 쓰기는 무시되고 `axi_pkg::RESP_SLVERR`로 응답됨.             |
| `0`                | Empty    | R           | `1'b1`      | 읽기 FIFO가 비어 있음 <br/>[0]: 데이터 사용 가능. <br/>[1]: 사용 가능한 데이터 없음. 읽기는 `axi_pkg::RESP_SLVERR`로 응답됨.                                                               |


### ERROR Register

메일박스 오류 레지스터. 이 읽기 전용 레지스터는 빈 FIFO에서 읽기가 발생했거나 가득 찬 FIFO에 쓰기가 발생했는지에 대한 정보를 담고 있습니다. 이 레지스터는 읽을 때 초기화됩니다.

| Bit(s)             | Name        | Access Type | Reset Value | Description                                                                            |
|:------------------:|:-----------:|:-----------:|:-----------:|:---------------------------------------------------------------------------------------|
| `AxiDataWidth-1:2` | Reserved    |             |             | 예약됨                                                                                 |
| `1`                | Write Error | R           | `1'b0`      | 가득 찬 메일박스에 쓰기 시도함. <br/>[0]: 오류 없음. <br/>[1]: 메일박스 쓰기 오류.    |
| `0`                | Read Error  | R           | `1'b1`      | 빈 메일박스에서 읽기 시도함. <br/>[0]: 오류 없음. <br/>[1]: 메일박스 읽기 오류.       |


### WIRQT Register

쓰기 인터럽트 요청 임계값 레지스터. W 채널에 연결된 FIFO의 사용량 포인터가 이 값을 초과하면 쓰기 임계값 IRQ가 트리거되고 해당 [STATUS register](#status-register) 비트가 설정됩니다.
이 레지스터에 `MailboxDepth` 파라미터보다 크거나 같은 값을 쓰면, 쓰기 FIFO가 가득 찰 때 IRQ가 트리거되도록 `MailboxDepth - 1`로 감소됩니다.

| Bit(s)                                | Name     | Access Type | Reset Value | Description               |
|:-------------------------------------:|:--------:|:-----------:|:-----------:|:--------------------------|
| `AxiDataWidth-1:$clog2(MailboxDepth)` | Reserved |             |             | 예약됨                    |
| `$clog2(MailboxDepth)-1:0`            | `WIRQT`  | R/W         | `'0`        | 쓰기 IRQ 임계값 수준      |


### RIRQT Register

읽기 인터럽트 요청 임계값 레지스터. R 채널에 연결된 FIFO의 채움 포인터가 이 값을 초과하면 읽기 임계값 IRQ가 트리거되고 해당 [STATUS register](#status-register) 비트가 설정됩니다.
이 레지스터에 `MailboxDepth` 파라미터보다 크거나 같은 값을 쓰면, 읽기 FIFO가 가득 찰 때 IRQ가 트리거되도록 `MailboxDepth - 1`로 감소됩니다.

| Bit(s)                                | Name     | Access Type | Reset Value | Description              |
|:-------------------------------------:|:--------:|:-----------:|:-----------:|:-------------------------|
| `AxiDataWidth-1:$clog2(MailboxDepth)` | Reserved |             |             | 예약됨                   |
| `$clog2(MailboxDepth)-1:0`            | `RIRQT`  | R/W         | `'0`        | 읽기 IRQ 임계값 수준     |


### IRQS Register

인터럽트 요청 상태 레지스터. 이 레지스터는 해당 슬레이브 포트의 현재 인터럽트 상태를 나타냅니다. [IRQEN register](#irqen-register)에서 활성화할 수 있는 세 가지 유형의 인터럽트가 있습니다. 이 레지스터의 비트는 스티키(sticky)로, 트리거 조건이 충족될 때 설정됩니다. 아래에 설명된 인터럽트 요청 상태를 확인(acknowledge)함으로써 이 레지스터를 명시적으로 초기화해야 합니다. 해당 인터럽트가 활성화되지 않은 경우에도 이 레지스터는 업데이트됩니다.
* `EIRQ`:  오류 인터럽트 요청. 빈 메일박스에서 읽기가 발생하거나 가득 찬 메일박스에 쓰기가 발생하면 하이로 설정됩니다.
* `RTIRQ`: 읽기 임계값 인터럽트 요청. R 채널에 연결된 FIFO의 채움 포인터가 `RIRQT`에 설정된 임계값보다 높으면 하이로 설정됩니다.
* `WTIRQ`: 쓰기 임계값 인터럽트 요청. W 채널에 연결된 FIFO의 채움 포인터가 `WIRQT`에 설정된 임계값보다 높으면 하이로 설정됩니다.
인터럽트 요청을 확인하려면 다음 표에 설명된 해당 비트에 `1'b1`을 씁니다.

| Bit(s)             | Name     | Access Type | Reset Value | Description                                                                                                                                                                                 |
|:------------------:|:--------:|:-----------:|:-----------:|:--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| `AxiDataWidth-1:3` | Reserved |             |             | 예약됨                                                                                                                                                                                      |
| `2`                | `EIRQ`   | R/W         | `1'b0`      | 읽기 시: <br/>[0]: 인터럽트 요청 없음 <br/>[1]: 메일박스 접근 오류                              <br/>쓰기 시: <br/>[0]: 확인 안 함 <br/>[1]: 인터럽트 요청 확인 및 초기화                 |
| `1`                | `RTIRQ`  | R/W         | `1'b0`      | 읽기 시: <br/>[0]: 인터럽트 요청 없음 <br/>[1]: 읽기 메일박스의 사용량 수준 임계값 초과           <br/>쓰기 시: <br/>[0]: 확인 안 함 <br/>[1]: 인터럽트 요청 확인 및 초기화                |
| `0`                | `WTIRQ`  | R/W         | `1'b0`      | 읽기 시: <br/>[0]: 인터럽트 요청 없음 <br/>[1]: 쓰기 메일박스의 사용량 수준 임계값 초과          <br/>쓰기 시: <br/>[0]: 확인 안 함 <br/>[1]: 인터럽트 요청 확인 및 초기화                |


### IRQEN Register

인터럽트 요청 활성화 레지스터. 다음 표의 해당 비트를 설정하여 [IRQS](#irqs-register)의 인터럽트를 활성화할 수 있습니다.

| Bit(s)             | Name     | Access Type | Reset Value | Description                                                             |
|:------------------:|:--------:|:-----------:|:-----------:|:------------------------------------------------------------------------|
| `AxiDataWidth-1:3` | Reserved |             |             | 예약됨                                                                  |
| `2`                | `EIRQ`   | R/W         | `1'b0`      | [0]: 오류 IRQ 비활성화 <br/>[1]: 오류 IRQ 활성화                        |
| `1`                | `RTIRQ`  | R/W         | `1'b0`      | [0]: 읽기 임계값 IRQ 비활성화 <br/>[1]: 읽기 임계값 IRQ 활성화          |
| `0`                | `WTIRQ`  | R/W         | `1'b0`      | [0]: 쓰기 임계값 IRQ 비활성화 <br/>[1]: 쓰기 임계값 IRQ 활성화          |


### IRQP Register

인터럽트 요청 대기 레지스터. 이 읽기 전용 레지스터는 해당 슬레이브 포트의 대기 중인 인터럽트를 나타냅니다. [IRQS](#irqs-register)와 [IRQEN](#irqen-register) 레지스터의 비트 AND 연산으로 생성됩니다.
인터럽트는 이 레지스터의 비트들의 OR 연산으로 트리거됩니다.

| Bit(s)             | Name     | Access Type | Reset Value | Description                                                               |
|:------------------:|:--------:|:-----------:|:-----------:|:--------------------------------------------------------------------------|
| `AxiDataWidth-1:3` | Reserved |             |             | 예약됨                                                                    |
| `2`                | `EIRQ`   | R           | `1'b0`      | [0]: 오류 IRQ 대기 없음 <br/>[1]: 오류 IRQ 대기 중                        |
| `1`                | `RTIRQ`  | R           | `1'b0`      | [0]: 읽기 임계값 IRQ 대기 없음 <br/>[1]: 읽기 임계값 IRQ 대기 중          |
| `0`                | `WTIRQ`  | R           | `1'b0`      | [0]: 쓰기 임계값 IRQ 대기 없음 <br/>[1]: 쓰기 임계값 IRQ 대기 중          |


### CTRL Register

메일박스 제어 레지스터. 각 인터페이스에서 FIFO를 초기화할 수 있습니다. 각 FIFO의 플러시 신호는 각 슬레이브 포트에서 이 레지스터의 해당 비트의 OR 조합입니다. 레지스터 쓰기 시 FIFO가 초기화되고 레지스터는 리셋됩니다.

| Bit(s)             | Name     | Access Type | Reset Value | Description                                  |
|:------------------:|:--------:|:-----------:|:-----------:|:---------------------------------------------|
| `AxiDataWidth-1:2` | Reserved |             |             | 예약됨                                       |
| `1`                | `RTIRQ`  | W           | `1'b0`      | 이 포트의 읽기 FIFO 플러시                   |
| `0`                | `WTIRQ`  | W           | `1'b0`      | 이 포트의 쓰기 FIFO 플러시                   |
