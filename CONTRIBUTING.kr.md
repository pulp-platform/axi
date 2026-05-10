# 기여 가이드라인

## 코딩 스타일

이 저장소의 모든 SystemVerilog 코드는 [lowRISC의 SystemVerilog 코딩 스타일 가이드](https://github.com/lowRISC/style-guides/blob/master/VerilogCodingStyle.md)와 다음 규칙을 _반드시_ 준수해야 합니다:

- 모든 모듈 이름은 _반드시_ `axi_`로 시작해야 합니다.

- 사용자 인터페이스 모듈은 _반드시_ AXI 포트로 SystemVerilog `struct`를 사용해야 합니다. 구체적인 `struct` 타입은 _반드시_ 모듈의 `parameter`로 정의해야 합니다. `struct`의 필드는 _반드시_ 당사의 [`typedef` 매크로](https://github.com/pulp-platform/axi/blob/master/include/axi/typedef.svh)에서 정의된 것과 일치해야 합니다.

- 사용자 인터페이스 모듈은 AXI 포트로 SystemVerilog 인터페이스를 사용하는 변형 버전을 _함께 제공할 수 있습니다_.
  - 그러한 인터페이스 변형 모듈은 인터페이스를 원본 모듈의 `struct` 포트에 연결하는 것 외에 어떠한 기능도 _구현해서는 안 됩니다_.
  - 인터페이스 변형의 이름은 _반드시_ 원본 모듈 이름에 `_intf` 접미사를 붙인 이름이어야 합니다.
  - 인터페이스 변형의 파라미터는 반드시 `ALL_CAPS` 형식으로 표기해야 합니다.


## 협업 가이드라인

[`pulp-platform`의 협업 가이드라인](https://github.com/pulp-platform/style-guidelines/blob/master/CONTRIBUTING.md)을 따릅니다.
