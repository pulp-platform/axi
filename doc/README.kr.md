# AXI 모듈 문서

이 폴더에는 다음 모듈들의 문서가 포함되어 있습니다:

- [AXI Crossbar (`axi_xbar`)](axi_xbar.md)
- [AXI Demultiplexer (`axi_demux`)](axi_demux.md)
- [AXI Multiplexer (`axi_mux`)](axi_mux.md)
- [AXI4-Lite Mailbox (`axi_lite_mailbox`)](axi_lite_mailbox.md)


## 관련 규격

이 문서들에서는 *AMBA AXI and ACE Protocol Specification, Issue F.b*를 준수하며, 이를 *AXI Spec*으로 약칭합니다.


## 용어 정의

AXI Glossary에 정의된 용어를 따릅니다 (AXI Spec 433페이지 참조).

아울러 다음 용어를 추가로 정의합니다.

### Handshake

valid 및 ready 신호가 있는 채널에서, 클록 에지에서 valid와 ready가 모두 high일 때 *handshake*가 발생합니다. handshake 과정에 대한 자세한 내용은 AXI Spec의 A3.2.1절을 참조하십시오.

### In Flight

특정 인터페이스에서 트랜잭션의 `Ax` 비트에 대한 handshake는 완료되었으나, 해당 트랜잭션의 (마지막) 응답에 대한 handshake가 아직 발생하지 않은 경우, 그 트랜잭션은 해당 인터페이스에서 *in flight* 상태라고 합니다.

### Pending

valid 신호는 high이고 ready 신호는 low인 경우, 특정 채널에서 handshake가 *pending* 상태라고 합니다.
