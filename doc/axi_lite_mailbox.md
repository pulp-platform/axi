# AXI4-Lite Mailbox

`axi_lite_mailbox` implements a hardware mailbox, where two AXI4-Lite subordinate ports are connected to each other over two FIFOs. Data written on port 0 is made available on the read data at port 1 and vice versa.
The module features an interrupt for each port which can be enabled with the [IRQEN](#irqen-register) register. Interrupts can be configured to trigger depending on the fill levels of the read ([RIRQT](#rirqt-register)) and write ([WIRQT](#wirqt-register)) FIFO. It is further possible to trigger an interrupt on an mailbox error condition as defined by the [ERROR](#error-register) register.


## Module Parameters

This table describes the parameters of the module.

| Name           | Type           | Description                                                                                  |
|:---------------|:---------------|:---------------------------------------------------------------------------------------------|
| `MailboxDepth` | `int unsigned `| The depth of the FIFOs between the two subordinate ports, min `32'd2`                              |
| `IrqEdgeTrig`  | `bit`          | Interrupts trigger mode. <br/>[0]: level trigger <br/>[1]: edge trigger                      |
| `IrqActHigh`   | `bit`          | Interrupts polarity. <br/>[0]: active low / falling edge <br/>[1]: active high / rising edge |
| `AddrWidth`    | `int unsigned` | The AXI4-Lite address width on the AW and AR channels                                        |
| `DataWidth`    | `int unsigned` | The AXI4-Lite data width on the W and R channels                                             |
| `req_lite_t`   | `type`         | In accordance with the `AXI_LITE_TYPEDEF_REQ_T` macro                                        |
| `rsp_lite_t`   | `type`         | In accordance with the `AXI_LITE_TYPEDEF_RSP_T` macro                                        |


## Module Ports

This table describes the ports of the module.

| Name           | Type                      | Description                                            |
|:---------------|:--------------------------|:-------------------------------------------------------|
| `clk_i`        | `input  logic`            | clock                                                  |
| `rst_ni`       | `input  logic`            | asynchronous reset active low                          |
| `test_i`       | `input  logic`            | testmode enable                                        |
| `sbr_ports_req_i`   | `input  req_lite_t [1:0]` | requests of the two AXI4-Lite ports                    |
| `sbr_ports_rsp_o`   | `output rsp_lite_t [1:0]` | responses of the two AXI4-Lite ports                   |
| `irq_o`        | `output logic      [1:0]` | interrupt output for each port                         |
| `base_addr_i`  | `input  addr_t     [1:0]` | base address for each port                             |



## Register Address Mapping

This table describes the type of register and the respective address mapping. The address depends on the parameter `DataWidth` and the respective `base_addr_i[*]` of the port associated to the index.
There are two example columns given for the resulting address for a `base_addr_i[*]` of `'0` and `DataWidth` of 32 and 64 bit.
Each register has one of the access types `R/W = read and write`, `R = read-only` and `W = write-only`. Writes to read-only and reads from write-only registers are responded by an `axi_pkg::RESP_SLVERR`.

| Base Address + Offset\*DataWidth/8 | Address for `DataWidth = 32` | Address for `DataWidth = 64` | Register Name                     | Access Type | Default Value | Description                       |
|:-----------------------------------|:----------------------------:|:----------------------------:|:---------------------------------:|:-----------:|:-------------:|:----------------------------------|
| base_addr_i + 0\*DataWidth/8       | 0x00                         | 0x00                         | [MBOXW](#mboxw-register)          | W           | N/A           | Write data address                |
| base_addr_i + 1\*DataWidth/8       | 0x04                         | 0x08                         | [MBOXR](#mboxr-register)          | R           | N/A           | Read data address                 |
| base_addr_i + 2\*DataWidth/8       | 0x08                         | 0x10                         | [STATUS](#status-register)        | R           | `0x1`         | Status flags of the mailbox       |
| base_addr_i + 3\*DataWidth/8       | 0x0C                         | 0x18                         | [ERROR](#error-register)          | R           | `0x0`         | Error flags                       |
| base_addr_i + 4\*DataWidth/8       | 0x10                         | 0x20                         | [WIRQT](#wirqt-register)          | R/W         | `0x0`         | Write data interrupt threshold    |
| base_addr_i + 5\*DataWidth/8       | 0x14                         | 0x28                         | [RIRQT](#rirqt-register)          | R/W         | `0x0`         | Read data interrupt threshold     |
| base_addr_i + 6\*DataWidth/8       | 0x18                         | 0x30                         | [IRQS](#irqs-register)            | R/W         | `0x0`         | Interrupt status register         |
| base_addr_i + 7\*DataWidth/8       | 0x1C                         | 0x38                         | [IRQEN](#irqen-register)          | R/W         | `0x0`         | Interrupt enable register         |
| base_addr_i + 8\*DataWidth/8       | 0x20                         | 0x40                         | [IRQP](#irqp-register)            | R           | `0x0`         | Interrupt pending register        |
| base_addr_i + 9\*DataWidth/8       | 0x24                         | 0x48                         | [CRTL](#ctrl-register)            | R/W         | `0x0`         | Module control register           |


### MBOXW Register

Mailbox write register. Write here to send data to the other subordinate port. A interrupt request will be raised when the fill pointer of the FIFO surpasses the [WIRQT Register](#wirqt-register) (if enabled).
Writes are ignored when the FIFO is full and a `axi_pkg::RESP_SLVERR` is returned. Additionally the corresponding bit in the [ERROR Register](#error-register) is set.


### MBOXR Register

Mailbox read register. Read here to receive data from the other subordinate port. A interrupt request will be raised when the fill pointer of the FIFO surpasses the [RIRQT Register](#rirqt-register) (if enabled).
When the FIFO is empty, the read response `axi_pkg::RESP_SLVERR` is returned. Additionally the corresponding bit in the [ERROR Register](#error-register) is set.


### STATUS Register

Mailbox status register. This read-only register holds the current status of the mailbox.

| Bit(s)          | Name     | Access Type | Reset Value | Description                                                                                                                                                                                |
|:---------------:|:--------:|:-----------:|:-----------:|:-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| `DataWidth-1:4` | Reserved |             |             | Reserved                                                                                                                                                                                   |
| `3`             | RFIFOL   | R           | `1'b0`      | Read FIFO level is higher than the threshold set in `RIRQT` <br/>[0]: Write FIFO level is less or equal to the threshold. <br/>[1]: Read FIFO level is higher than the threshold.          |
| `2`             | WFIFOL   | R           | `1'b0`      | Write FIFO level is higher than the threshold set in `WIRQT` <br/>[0]: Write FIFO level is less or equal to the threshold. <br/>[1]: Write FIFO level is higher than the threshold.        |
| `1`             | Full     | R           | `1'b0`      | Write FIFO is full and subsequent writes to mailbox are ignored <br/>[0]: Space for write data. <br/>[1]: No space for data, writes are ignored and responded with `axi_pkg::RESP_SLVERR`. |
| `0`             | Empty    | R           | `1'b1`      | Read FIFO is empty <br/>[0]: Data is available. <br/>[1]: No available data, reads respond with `axi_pkg::RESP_SLVERR`.                                                                    |


### ERROR Register

Mailbox error register. This read-only register contains information if a read occurred on an empty FIFO or a write occurred on a full FIFO. This register is cleared on read.

| Bit(s)          | Name        | Access Type | Reset Value | Description                                                                            |
|:---------------:|:-----------:|:-----------:|:-----------:|:---------------------------------------------------------------------------------------|
| `DataWidth-1:2` | Reserved    |             |             | Reserved                                                                               |
| `1`             | Write Error | R           | `1'b0`      | Attempted write to a full mailbox. <br/>[0]: No Error. <br/>[1]: Mailbox write error.  |
| `0`             | Read Error  | R           | `1'b1`      | Attempted read from an empty mailbox <br/>[0]: No Error. <br/>[1]: Mailbox read error. |


### WIRQT Register

Write interrupt request threshold register. When the usage pointer of the FIFO connected to the W channel exceeds this value, a write threshold IRQ is triggered and the corresponding [STATUS register](#status-register) bit is set.
When a value larger than or equal to the `MailboxDepth` parameter is written to this register, it gets reduced to `MailboxDepth - 1` to ensure an IRQ is triggered when the write FIFO is full.

| Bit(s)                             | Name     | Access Type | Reset Value | Description               |
|:----------------------------------:|:--------:|:-----------:|:-----------:|:--------------------------|
| `DataWidth-1:$clog2(MailboxDepth)` | Reserved |             |             | Reserved                  |
| `$clog2(MailboxDepth)-1:0`         | `WIRQT`  | R/W         | `'0`        | Write IRQ threshold level |


### RIRQT Register

Read interrupt request threshold register. When the fill pointer of the FIFO connected to the R channel exceeds this value, a read threshold IRQ is triggered and the corresponding [STATUS register](#status-register) bit is set.
When a value larger than or equal to the `MailboxDepth` parameter is written to this register, it gets reduced to `MailboxDepth - 1` to ensure an IRQ is triggered when the read FIFO is full.

| Bit(s)                             | Name     | Access Type | Reset Value | Description              |
|:----------------------------------:|:--------:|:-----------:|:-----------:|:-------------------------|
| `DataWidth-1:$clog2(MailboxDepth)` | Reserved |             |             | Reserved                 |
| `$clog2(MailboxDepth)-1:0`         | `RIRQT`  | R/W         | `'0`        | Read IRQ threshold level |


### IRQS Register

Interrupt request status register. This register holds the current interrupt status of this subordinate port. There are three types of interrupts which can be enabled in the [IRQEN register](#irqen-register). The bits inside this register are sticky and get set when the trigger condition is fulfilled. This register has to be cleared explicitly by acknowledging the interrupt request status described below. This register will also get updated when the respective interrupt is not enabled.
* `EIRQ`:  Error interrupt request, is set to high when there was a read from an empty mailbox or a write to a full mailbox.
* `RTIRQ`: Read threshold interrupt request, is set to high when the fill pointer of the FIFO connected to the R channel is higher than the threshold set in `RIRQT`.
* `WTIRQ`: Write threshold interrupt request, is set to high when the fill pointer of the FIFO connected to the W channel is higher than the threshold set in `WIRQT`.
To acknowledge an interrupt request write a `1'b1` to the corresponding bit described in following table.

| Bit(s)          | Name     | Access Type | Reset Value | Description                                                                                                                                                                                 |
|:---------------:|:--------:|:-----------:|:-----------:|:--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| `DataWidth-1:3` | Reserved |             |             | Reserved                                                                                                                                                                                    |
| `2`             | `EIRQ`   | R/W         | `1'b0`      | On read: <br/>[0]: No interrupt request <br/>[1]: Error on mailbox access                        <br/>On write: <br/>[0]: No acknowledge <br/>[1]: Acknowledge and clear interrupt request  |
| `1`             | `RTIRQ`  | R/W         | `1'b0`      | On read: <br/>[0]: No interrupt request <br/>[1]: Usage level threshold in read mailbox exceeded  <br/>On write: <br/>[0]: No acknowledge <br/>[1]: Acknowledge and clear interrupt request |
| `0`             | `WTIRQ`  | R/W         | `1'b0`      | On read: <br/>[0]: No interrupt request <br/>[1]: Usage level threshold in write mailbox exceeded <br/>On write: <br/>[0]: No acknowledge <br/>[1]: Acknowledge and clear interrupt request |


### IRQEN Register

Interrupt request enable register. Here the interrupts from [IRQS](#irqs-register) can be enabled by setting the corresponding bit in the following table.

| Bit(s)          | Name     | Access Type | Reset Value | Description                                                             |
|:---------------:|:--------:|:-----------:|:-----------:|:------------------------------------------------------------------------|
| `DataWidth-1:3` | Reserved |             |             | Reserved                                                                |
| `2`             | `EIRQ`   | R/W         | `1'b0`      | [0]: Error IRQ disabled <br/>[1]: Error IRQ enabled                     |
| `1`             | `RTIRQ`  | R/W         | `1'b0`      | [0]: Read threshold IRQ disabled <br/>[1]: Read threshold IRQ enabled   |
| `0`             | `WTIRQ`  | R/W         | `1'b0`      | [0]: Write threshold IRQ disabled <br/>[1]: Write threshold IRQ enabled |


### IRQP Register

Interrupt request pending register. This read-only register holds the pending interrupts for this subordinate port. It is generated by the bitwise AND of the [IRQS](#irqs-register) and [IRQEN](#irqen-register) registers.
An interrupt gets triggered by the OR of the bits of this register.

| Bit(s)          | Name     | Access Type | Reset Value | Description                                                               |
|:---------------:|:--------:|:-----------:|:-----------:|:--------------------------------------------------------------------------|
| `DataWidth-1:3` | Reserved |             |             | Reserved                                                                  |
| `2`             | `EIRQ`   | R           | `1'b0`      | [0]: No error IRQ pending <br/>[1]: Error IRQ pending                     |
| `1`             | `RTIRQ`  | R           | `1'b0`      | [0]: No read threshold IRQ pending <br/>[1]: Read threshold IRQ pending   |
| `0`             | `WTIRQ`  | R           | `1'b0`      | [0]: No write threshold IRQ pending <br/>[1]: Write threshold IRQ pending |


### CTRL Register

Mailbox control register. Here the FIFOs can be cleared from each interface. The flush signal of each FIFO is the OR combination of the respective bit of this register at each subordinate port. On register write, the FIFO is cleared and the register is reset.

| Bit(s)          | Name     | Access Type | Reset Value | Description                                  |
|:---------------:|:--------:|:-----------:|:-----------:|:---------------------------------------------|
| `DataWidth-1:2` | Reserved |             |             | Reserved                                     |
| `1`             | `RTIRQ`  | W           | `1'b0`      | Flush the read FIFO for this port            |
| `0`             | `WTIRQ`  | W           | `1'b0`      | Flush the write FIFO for this port           |
