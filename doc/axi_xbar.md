# AXI4+ATOP Fully-Connected Crossbar

`axi_xbar` is a fully-connected crossbar that implements the full AXI4 specification plus atomic operations (ATOPs) from AXI5.


## Design Overview

`axi_xbar` is a fully-connected crossbar, which means that each manager module that is connected to a *subordinate port* for of the crossbar has direct wires to all subordinate modules that are connected to the *manager ports* of the crossbar.
A block-diagram of the crossbar is shown below:

![Block-diagram showing the design of the full AXI4 Crossbar.](axi_xbar.png  "Block-diagram showing the design of the full AXI4 Crossbar.")

The crossbar has a configurable number of subordinate and manager ports.

The ID width of the manager ports is wider than that of the subordinate ports.  The additional ID bits are used by the internal multiplexers to route responses.  The ID width of the manager ports must be `IdWidthSbrPorts + $clog_2(NumSbrPorts)`.


## Address Map

One address map is shared by all manager ports.  The *address map* contains an arbitrary number of rules (but at least one).  Each *rule* maps one address range to one manager port.  Multiple rules can map to the same manager port.  The address ranges of two rules may overlap: in case two address ranges overlap, the rule at the higher (more significant) position in the address map prevails.

Each address range includes the start address but does **not** include the end address.  That is, an address *matches* an address range if and only if
```
    addr >= start_addr && addr < end_addr
```
The start address must be less than or equal to the end address.

The address map can be defined and changed at run time (it is an input signal to the crossbar).  However, the address map must not be changed while any AW or AR channel of any subordinate port is valid.


## Decode Errors and Default Subordinate Port

Each subordinate port has its own internal *decode error subordinate* module.  If the address of a transaction does not match any rule, the transaction is routed to that decode error subordinate module.  That module absorbs each transaction and responds with a decode error (with the proper number of beats).  The data of each read response beat is `32'hBADCAB1E` (zero-extended or truncated to match the data width).

Each subordinate port can have a default manager port.  If the default manager port is enabled for a subordinate port, any address on that subordinate port that does not match any rule is routed to the default manager port instead of the decode error subordinate.  The default manager port can be enabled and changed at run time (it is an input signal to the crossbar), and the same restrictions as for the address map apply.


## Configuration

The crossbar is configured through the `Cfg` parameter with a `axi_pkg::xbar_cfg_t` struct.  That struct has the following fields:

| Name              | Type               | Definition |
|:------------------|:-------------------|:-----------|
| `NumSbrPorts`     | `int unsigned`     | The number of AXI subordinate ports of the crossbar (in other words, how many AXI manager modules can be attached). |
| `NumMgrPorts`     | `int unsigned`     | The number of AXI manager ports of the crossbar (in other words, how many AXI subordinate modules can be attached). |
| `MaxMgrTrans`     | `int unsigned`     | Each subordinate port can have at most this many transactions [in flight](../doc#in-flight). |
| `MaxSbrTrans`     | `int unsigned`     | Each manager port can have at most this many transactions per ID [in flight](../doc#in-flight). |
| `FallThrough`     | `bit`              | Routing decisions on the AW channel fall through to the W channel.  Enabling this allows the crossbar to accept a W beat in the same cycle as the corresponding AW beat, but it increases the combinatorial path of the W channel with logic from the AW channel. |
| `LatencyMode`     | `enum logic [9:0]` | Latency on the individual channels, defined in detail in section *Pipelining and Latency* below. |
| `IdWidthSbrPorts` | `int unsigned`     | The AXI ID width of the subordinate ports. |
| `IdUsedSbrPorts`  | `int unsigned`     | The number of subordinate port ID bits (starting at the least significant) the crossbar uses to determine the uniqueness of an AXI ID (see section *Ordering and Stalls* below).  This value has to be less or equal than `IdWidthSbrPorts`. |
| `UniqueIds`       | `bit`              | If you can guarantee that the ID of each transaction is always unique among all in-flight transactions in the same direction, setting this parameter to `1'b1` simplifies the crossbar.  See the [`axi_demux` documentation](axi_demux#ordering-and-stalls) for details. |
| `AddrWidth`       | `int unsigned`     | The AXI address width. |
| `DataWidth`       | `int unsigned`     | The AXI data width. |
| `NumAddrRules`    | `int unsigned`     | The number of address map rules. |

The other parameters are types to define the ports of the crossbar.  The `*_chan_t` and `*_req_t`/`*_rsp_t` types must be bound in accordance to the configuration with the `AXI_TYPEDEF` macros defined in `axi/typedef.svh`.  The `rule_t` type must be bound to an address decoding rule with the same address width as in the configuration, and `axi_pkg` contains definitions for 64- and 32-bit addresses.

### Pipelining and Latency

The `LatencyMode` parameter allows to insert spill registers after each channel (AW, W, B, AR, and R) of each manager port (i.e., each multiplexer) and before each channel of each subordinate port (i.e., each demultiplexer).  Spill registers cut combinatorial paths, so this parameter reduces the length of combinatorial paths through the crossbar.

Some common configurations are given in the `xbar_latency_e` `enum`.  The recommended configuration (`CUT_ALL_AX`) is to have a latency of 2 on the AW and AR channels because these channels have the most combinatorial logic on them.  Additionally, `FallThrough` should be set to `0` to prevent logic on the AW channel from extending combinatorial paths on the W channel.  However, it is possible to run the crossbar in a fully combinatorial configuration by setting `LatencyMode` to `NO_LATENCY` and `FallThrough` to `1`.

If two crossbars are connected in both directions, meaning both have one of their manager ports connected to a subordinate port of the other, the `LatencyMode` of both crossbars must be set to either `CUT_SBR_PORTS`, `CUT_MGR_PORTS`, or `CUT_ALL_PORTS`.  Any other latency mode will lead to timing loops on the uncut channels between the two crossbars.  The latency mode of the two crossbars does not have to be identical.


## Ports

| Name                    | Description |
|:------------------------|:------------|
| `clk_i`                 | Clock to which all other signals (except `rst_ni`) are synchronous. |
| `rst_ni`                | Reset, asynchronous, active-low. |
| `test_i`                | Test mode enable (active-high). |
| `sbr_ports_*`           | Array of subordinate ports of the crossbar.  The array index of each port is the index of the subordinate port.  This index will be prepended to all requests at one of the manager ports. |
| `mgr_ports_*`           | Array of manager ports of the crossbar.  The array index of each port is the index of the manager port. |
| `addr_map_i`            | Address map of the crossbar (see section *Address Map* above). |
| `en_default_mgr_port_i` | One bit per subordinate port that defines whether the default manager port is active for that subordinate port (see section *Decode Errors and Default Subordinate Port* above). |
| `default_mgr_port_i`    | One manager port index per subordinate port that defines the default manager port for that subordinate port (if active). |


## Ordering and Stalls

When one subordinate port receives two transactions with the same ID and direction (i.e., both read or both write) but targeting two different manager ports, it will not accept the second transaction until the first has completed.  During this time, the crossbar stalls the AR or AW channel of that subordinate port.  To determine whether two transactions have the same ID, the `IdUsedSbrPorts` least-significant bits are compared.  That parameter can be set to the full `IdWidthSbrPorts` to avoid false ID conflicts, or it can be set to a lower value to reduce area and delay at the cost of more false conflicts.

The reason for this ordering constraint is that AXI transactions with the same ID and direction must remain ordered.  If this crossbar would forward both transactions described above, the second manager port could get a response before the first one, and the crossbar would have to reorder the responses before returning them on the manager port.  However, for efficiency reasons, this crossbar does not have reorder buffers.


## Verification Methodology

This module has been verified with a directed random verification testbench, described and implemented in `test/tb_axi_xbar.sv`.


## Design Rationale for No Pipelining Inside Crossbar

Inserting spill registers between demuxers and muxers seems attractive to further reduce the length of combinatorial paths in the crossbar.  However, this can lead to deadlocks in the W channel where two different muxes at the manager ports would circular wait on two different demuxes (TODO).  In fact, spill registers between the switching modules causes all four deadlock criteria to be met.  Recall that the criteria are:

1. Mutual Exclusion
2. Hold and Wait
3. No Preemption
4. Circular Wait

The first criterion is given by the nature of a multiplexer on the W channel: all W beats have to arrive in the same order as the AW beats regardless of the ID at the subordinate module.  Thus, the different manager ports of the multiplexer exclude each other because the order is given by the arbitration tree of the AW channel.

The second and third criterion are inherent to the AXI protocol:  For (2), the valid signal has to be held high until the ready signal goes high.  For (3), AXI does not allow interleaving of W beats and requires W bursts to be in the same order as AW beats.

The fourth criterion is thus the only one that can be broken to prevent deadlocks.  However, inserting a spill register between a manager port of the demultiplexer and a subordinate port of the multiplexer can lead to a circular dependency inside the W FIFOs.  This comes from the particular way the round robin arbiter from the AW channel in the multiplexer defines its priorities.  It is constructed in a way by giving each of its subordinate ports an increasing priority and then comparing pairwise down till a winner is chosen.  When the winner gets transferred, the priority state is advanced by one position, preventing starvation.

The problem can be shown with an example.  Assume an arbitration tree with 10 inputs.  Two requests want to be served in the same clock cycle.  The one with the higher priority wins and the priority state advances.  In the next cycle again the same two inputs have a request waiting.  Again it is possible that the same port as last time wins as the priority shifted only one position further.  This can lead in conjunction with the other arbitration trees in the other muxes of the crossbar to the circular dependencies inside the FIFOs.  Removing the spill register between the demultiplexer and multiplexer forces the switching decision into the W FIFOs in the same clock cycle.  This leads to a strict ordering of the switching decision, thus preventing the circular wait.
