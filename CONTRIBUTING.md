# Contribution Guidelines

## Collaboration Guidelines

We follow [`pulp-platform`'s Collaboration
Guidelines](https://github.com/pulp-platform/style-guidelines/blob/master/CONTRIBUTING.md).

## Coding Style

Preamble: The key words "MUST", "MUST NOT", "REQUIRED", "SHALL", "SHALL NOT", "SHOULD", "SHOULD NOT", "RECOMMENDED", "NOT RECOMMENDED", "MAY", and "OPTIONAL" in this document are to be interpreted as described in [BCP 14](https://tools.ietf.org/html/bcp14) [[RFC2119]](https://tools.ietf.org/html/rfc2119) [[RFC8174]](https://tools.ietf.org/html/rfc8174) when, and only when, they appear in all capitals, as shown here.

All SystemVerilog code in this repository MUST adhere to the [SystemVerilog Coding Style Guide by
lowRISC](https://github.com/lowRISC/style-guides/blob/master/VerilogCodingStyle.md) and the
following rules:

### Synthesizable modules

All module names MUST start with `axi_`.

User-facing modules MUST have SystemVerilog `struct`s as AXI ports.  The concrete `struct` type
MUST be defined as `parameter` to the module.  The fields of the `struct` MUST correspond to
those defined by our [`typedef`
macros](https://github.com/pulp-platform/axi/blob/master/include/axi/typedef.svh).

User-facing modules MAY come with a variant that has SystemVerilog interfaces as AXI ports.
Such an interface variant module MUST NOT implement any functionality except wiring its
interfaces to the `struct` ports of the original module.
The name of an interface variant MUST be the name of the original module suffixed by `_intf`.

#### Parameters

##### Legal Types

Every `parameter` of a synthesizable `module` MUST be either:
(a) a `type`, or
(b) a (vector of) one of the following SystemVerilog types:
  - `bit` or `logic`, which MAY be `signed` (but are by default implicitly `unsigned`), or
  - `byte`, `shortint`, `int`, or `longint`, which MUST be followed by `unsigned` or `signed`, or

(c) a `typedef`ed type of one of the types in (b).

In particular, `struct`s and `string`s MUST NOT be used as `parameter` of a synthesizable `module`.

Rationale: Many tools do not properly implement complex types for `parameter`s.

For non-synthesizable `module`s and `class`es, the key words MUST and MUST NOT in this section are relaxed to SHOULD and SHOULD NOT, respectively.  (In particular, testbench `module`s MAY use `time` and `string` parameters.)

##### Signedness

If an integer parameter (i.e., `byte`, `shortint`, `int`, or `longint`) is not supposed to take negative values, it MUST be declared `unsigned` instead of `signed`.

##### Default Value

Every `parameter` MUST have a default value.

If possible, the default value SHOULD be a *null* value that is outside the legal range of the parameter (e.g., a signal width of zero).  In this case, the `module` SHOULD contain an assertion to ensure that the parameter is set to a value other than the *null* value at instantiation.

Rationale: Many tools require `parameter`s to have a default value, but in many cases a `parameter` that is not set at instantiation indicates an error that should be detected. 

##### Derived Parameters

The parameter list of a `module` MUST NOT contain `localparam`s.  Rationale: Unsupported by some tools.

Instead, if the value of a parameter is derived from another parameter and should not be overridden at instantiation, the line above the derived parameter SHOULD be as follows:
```sv
/// Dependent parameter, DO NOT OVERRIDE!
```

##### Names

- The name of a non-`type` `parameter` MUST be in `UpperCamelCase`.
  Rationale: [style guide](https://github.com/lowRISC/style-guides/blob/master/VerilogCodingStyle.md#constants).
- The name of a `type` `parameter` MUST be in `lower_snake_case` and end with `_t`.
  Rationale: [style guide](https://github.com/lowRISC/style-guides/blob/master/VerilogCodingStyle.md#summary-2).
- The name of a non-`type` `parameter` MUST NOT be prefixed with `Axi`.
  Example: A `module` with a parametrizable data width has a `parameter` named `DataWidth`, not ~`AxiDataWidth`~.
  Rationale: Every `module` name starts with `axi_` and prefixing `parameter`s with `Axi` is redundant.
- If a `parameter` only applies to one port, its name MUST start with the prefix of the port (converted to the casing dictated above and to singular if the port is an array) or with `Num` (see below) followed by the prefix of the port.
  Example: For a crossbar, the ID width of each of its subordinate ports (part of an array prefixed `sbr_ports_`) would be given by a `parameter` named `SbrPortIdWidth`, and the request type of each of its subordinate ports would be given by a `parameter` named `sbr_port_axi_req_t`.
- Conversely, if a `parameter` applies to more than one port, its name MUST NOT start with the prefix of one of the ports.
- If the name of a `type` `parameter` does not have a port-specific prefix, it MUST be prefixed with `axi_`.
  Rationale: Some tools do not properly scope type definitions, and adding a topic-specific prefix reduces the chance of type name collisions.
- If a `parameter` defines the number of bits in a signal, its name SHOULD end with `Width`.
- If a `parameter` defines a quantity other than bits in a signal, its name SHOULD contain `Num` followed by a noun in plural.  `No` MUST NOT be used to denote a quantity `parameter`.  (Rationale: easily mistaken for negation, e.g., "no registers").
- If a `parameter` defines the maximum value of a quantity, its name SHOULD contain `Max` followed by a noun in plural.
- The name of every `parameter` of a testbench `module` MUST start with `Tb` or `tb_`.  The name of any `parameter` of a non-testbench `module` MUST NOT start with `Tb` or `tb_`.
  Rationale: The name of each `parameter` of a top-level `module` that is to be assigned a value when the simulator is invoked must be unique among all simulated `module`s; see https://github.com/pulp-platform/axi/pull/152#issuecomment-766141984.

##### Examples

A crossbar with multiple `sbr_ports` and `mgr_ports` could have the following among its parameters:
```sv
/// Number of subordinate ports of the crossbar
parameter int unsigned NumSbrPorts = 0,
/// Number of manager ports of the crossbar
parameter int unsigned NumMgrPorts = 0,
/// AXI address width
parameter int unsigned AddrWidth = 0,
/// AXI data width
parameter int unsigned DataWidth = 0,
/// AXI ID width at the subordinate ports
parameter int unsigned SbrPortIdWidth = 0,
/// Maximum number of in-flight transactions at each subordinate port
parameter int unsigned SbrPortMaxTxns = 0,
/// Maximum number of in-flight transactions at each manager port
parameter int unsigned MgrPortMaxTxns = 0,
/// AXI4(+ATOPs) request struct of each subordinate port
parameter type sbr_port_axi_req_t = logic,
/// AXI4 response struct of each subordinate port
parameter type sbr_port_axi_rsp_t = logic,
/// AXI4(+ATOPs) request struct of each manager port
parameter type mgr_port_axi_req_t = logic,
/// AXI4 response struct of each manager port
parameter type mgr_port_axi_rsp_t = logic,
```

#### Ports

- Each input port MUST end with `_i` (or `_ni` if it is active-low).
- Each output port MUST end with `_o` (or `_no` if it is active-low).
- The name of each subordinate port MUST contain `sbr_port_` (or `sbr_ports_` if the port is an array).
- The name of each manager port MUST contain `mgr_port_` (or `mgr_ports_` if the port is an array).
- The name of each request port MUST contain `_req` directly before the input/output suffix.
- The name of each response port MUST contain `_rsp` directly before the input/output suffix.

##### Examples

A module with a single AXI-Lite subordinate port could contain in its `input`s and `output`s:
```sv
input  axi_lite_req_t sbr_port_req_i,
output axi_lite_rsp_t sbr_port_rsp_o,
```

A CDC from a `src_clk_i` to a `dst_clk_i` would contain in its `input`s and `output`s:
```sv
// Subordinate Port in Source Clock Domain
input  axi_req_t src_sbr_port_req_i,
output axi_rsp_t src_sbr_port_rsp_o,
// Manager Port in Destination Clock Domain
output axi_req_t dst_mgr_port_req_o,
input  axi_rsp_t dst_mgr_port_rsp_i,
```

A crossbar with multiple subordinate and manager ports would contain in its `input`s and `output`s:
```sv
// Subordinate Ports
input  sbr_port_axi_req_t [NumSbrPorts-1:0] sbr_ports_req_i,
output sbr_port_axi_rsp_t [NumSbrPorts-1:0] sbr_ports_rsp_o,
// Manager Ports
output mgr_port_axi_req_t [NumMgrPorts-1:0] mgr_ports_req_o,
input  mgr_port_axi_rsp_t [NumMgrPorts-1:0] mgr_ports_rsp_i,
```

A protocol converter from AXI to AXI-Lite would contain in its `input`s and `output`s:
```sv
// AXI Subordinate Port
input  sbr_port_axi_req_t sbr_port_req_i,
output sbr_port_axi_rsp_t sbr_port_rsp_o,
// AXI-Lite Manager Port
output mgr_port_axi_lite_req_t mgr_port_req_o,
input  mgr_port_axi_lite_rsp_t mgr_port_rsp_i,
```


#### Channel and Request/Response Types

In this section, `X` MUST be either `axi` or `axi_lite` in accordance with whether the type is part of full AXI or AXI-Lite.

- A channel type MUST end with `X_Y_chan_t`, where `Y` is one of `aw`, `w`, `b`, `ar`, or `r` and MUST correspond to the channel type.
- A request type MUST end with `X_req_t`.
- A response type MUST end with `X_rsp_t`.


#### Interfaces

- This repository defines four `interface`s: `axi_if`, `axi_dv_if`, `axi_lite_if`, and `axi_lite_dv_if`.
  Rationale for naming: compliant with [Google Verible's `interface-name-style`](https://google.github.io/verible/verilog_lint.html#interface-name-style) and consistent with the [name of types in the style guide we follow](https://github.com/lowRISC/style-guides/blob/master/VerilogCodingStyle.md#summary-2) (which does not have rules for naming interfaces).
- The `modport`s are named `sbr_port` (for a subordinate port `modport`), `mgr_port` (for a manager port `modport`), and `mon_port` (for an all-`input` monitor `modport`).
  Rationale: consistent with the naming of non-`interface` ports.
- The non-`dv` interfaces MUST be synthesizable.  The `dv` `interface`s are used for design verification and MAY contain non-synthesizable code.
- All `parameter`s in an `interface` MUST obey the rules in the above *Parameters* section.
- The name of each subordinate port `interface` MUST contain `sbr_port` (or `sbr_ports` if the `interface` port is an array).
- The name of each manager port `interface` MUST contain `mgr_port` (or `mgr_ports` if the `interface` port is an array).
- Arrays of `interface`s MUST be unpacked (i.e., dimensions after identifier). The dimensions MUST be in big-endian notation (e.g., `[0:N-1]`). Dimensions SHOULD be zero-based unless there are strong reasons against it. Zero-based dimensions SHOULD use the short `[N]` notation. There MUST NOT be a space between identifier and dimensions.

##### Examples

A crossbar (or rather, its `_intf` variant) with multiple subordinate and manager ports would contain in its port list:
```sv
axi_if.sbr_port sbr_ports[NumSbrPorts],
axi_if.mgr_port mgr_ports[NumMgrPorts],
```
