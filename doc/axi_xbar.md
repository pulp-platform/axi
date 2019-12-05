### AXI Full Crossbar

This module is called `axi_xbar`. It features a full crossbar design, meaning that each master module, which is connected to the bar's slave ports, has a direct wiring to the salves connected to the master ports of the design.
A block-diagram of the crossbar is shown below:

![Block-diagram showing the design of the full AXI4 Crossbar.](figures/axi_xbar.png  "Block-diagram showing the design of the full AXI4 Crossbar.")

The crossbar has a variable number of slave and master ports. To the slave ports master modules get connected. The opposite applies to the master ports.

One defining characteristic of the master ports is that the AXI ID width of them is wider than the one of the slave ports. This has to do with the used AXI multiplexers. The ID width of the master ports can be calculated with:

```
id\_width\_master\_port = id\_width\_slave\_port + log<sub>2<\sub>(no_\_slave\_ports)
```

The design has one global address mapping for all its master ports. The design of the address mapping allows for multiple physical address ranges to be mapped to the same master port. It is also possible to change the address mapping, as the map is defined as a signal. However this change should only be done, when no master connected to the crossbar has an open transaction currently in flight.

Each master module connected to the crossbar has its own decode error slave module. When the address decoding encounters a decode error, the transaction gets absorbed in this module. The module absorbs each transaction made to it and answers always with a decode error response. The data of the read response is defined on each beat with the symbol `32h'BADCAB1E`. This response gets truncated or zero extended to match the configured data with of the module.

Each slave port has the possibility to get a default master port mapping. Meaning that unmatched addresses get set to the indicated master port, instead to the decode error slave module. The same restriction applies to the default master port mapping regarding the changing of the applied signal.

The crossbar features a configuration struct which fixes all parameters needed in the submodules instantiated in the design. One of these is called `LatencyMode`. This is a special enum defined in the package `axi_pkg` of the repository. It defines which spill register of the axi demuxes and muxes get instantiated. The recommended configuration is to have a latency of two on the AW and AR channels as they have the most and longest control logic in them. The reason being the ID counters. Additionally it is recommended to not set the fall-through parameter as then the longest path will be long. It is however possible to run the crossbar in a fully combinatorical fashion. Further, like with the other AXI modules, it is necessary to give the AXI channel structs as parameters. Due to the extension of the ID it is necessary to define the structs for each the slave and the master ports. The final parameter specifies the rule struct of the address mapping.

Following table describes the parameters of the configuration struct in detail:

| Name | Type | Function |
|:------------------ |:----------------- |:---------------------------------- |
| `NoSlvPorts` | `int unsigned` | The Number of slave ports created on the crossbar. This many master modules can be connected to it. |
| `NoMstPorts` | `int unsigned` | The number of master ports created on the xbar. This many slave modules can be connected to it. |
| `MaxMstTrans` | `int unsigned` | Each master module connected to the crossbar can issue this many read and write transactions in the worst case. |
| `MaxSlvTrans` | `int unsigned` | Each master port of the crossbar (to the slave modules) supports at most this may transactions in flight by id. |
| `FallThrough` | `bit` | The FIFO's which store the switching decision from the AW channel to the W channel are in FallThrough mode. |
| `LatencyMode` | `enum logic [9:0]` | A 10 bit vector which encodes the generation of spill registers on different points in the crossbar. The `enum xbar_latency_t` found in `axi_pkg` has some common configurations. |
| `AxiIdWidthSlvPorts` | `int unsigned` | The AXI ID width of the slave ports. |
| `AxiIdUsedSlvPorts` | `int unsigned` |  The crossbar uses this many LSB's of the slave port AXI ID to determine the uniqueness of an AXI ID. This value has to be equal or smaller than the AXI ID width of the slave ports. |
| `AxiIdWidthMstPorts` | `int unsigned` | The AXI ID width of the master ports. |
| `AxiAddrWidth` | `int unsigned` | The AXI ADDRESS width of the slave ports. |
| `AxiDataWidth` | `int unsigned` | The AXI DATA width of the slave ports. |
| `NoAddrRules` | `int unsigned` | The crossbar has this many address rules. |


The non trivial ports of the full crossbar can be described as follows:
* `slv_ports_req_i`, `slv_ports_resp_o`: Are defining the slave ports of the crossbar. They are arrays of the requests and responses of all master modules on the design. The array index corresponds to the index of the slave port. This index will be prepended to all requests of a particular master module when it leaves the crossbar through one of the master ports.
* `mst_ports_req_o`,`mst_ports_resp_i`: Are defining the master ports of the crossbar. Again they are defined as an array respectively. When a default master port is chosen, the request with the corresponding index will transmit the AXI request.
* `addr_map_i`: The physical address map of the crossbar. It defines which AXI address ranges get mapped to which master port. The detailed description of the fields of this array of structs was described in [@sec:axi-address-decoding].
`en_default_mst_port_i`: This vector has the width equal to the number of slave ports defined in the configuration struct of the crossbar. The vector index corresponding to the slave port. When set, the default master port for this particular slave port is enabled. When it is not needed to have a default master port mapping set this port to `'0`. In this case the crossbar will answer with decode errors, when a master issues a request to an unmapped address.
`defaut_mst_port_i`: This array is a collection of indices specifying the default master port of the respective slave port when it is enabled. When the functionality is not needed set this input to `'0`.


The crossbar was functionally tested with targeted random verification. The design can be instantiated with a variable number of random AXI master and slave modules to it. The test-bench has a monitor, which snoops on the AXI transactions of each master and slave port of the design. The monitor models the crossbar with a network of FIFO's. When the monitor sees a new transaction of one of the master modules, it models how many beats of the other channels it expects and to which slave module the transaction should be sent. All master modules are sending transactions at the same time, saturating the crossbar.

During implementation there was a version of the crossbar which also had the option for spill registers between the AXI demuxes and muxes. However the test-bench revealed that that version could lead to deadlocks in the W channel where two different muxes at the master ports would cyclic wait on two different demuxes. It turned out that in this configuration with the spill registers between the switching modules all four of the deadlock criteria where met. The criteria being:

> 1. Mutual Exclusion
> 2. Hold and Wait
> 3. No Preemption
> 4. Circular Wait

The first criteria is given in the nature of a multiplexer for an AXI W channel. The property being that all W beats have to arrive in order of the AW vectors regardless of ID at the slave module. So the different master ports of the multiplexer exclude each other because the order is given by the arbitration tree of the AW channel.

The second and third criteria are inherent to the AXI protocol. The valid signal has to be hold at high when it is set till the corresponding ready signal also goes to high indicating a transfer of a beat. And the protocol further states that when a transaction is initialized with an AW or AR beat then all of the corresponding W, B or R beats have to complete otherwise the protocol is violated.

This leaves only the fourth property to break so that a deadlock is not possible. Having the spill registers between a master port of the demultiplexer and a slave port of the multiplexer can lead to circular dependency states inside the W FIFO's. This comes from the particular way the round robin arbiter from the AW channel in the multiplexer defines its priorities. It is constructed in a way by giving each of its slave ports an increasing priority and then comparing pairwise down till a winner is chosen. When the winner gets transferred the priority state is advanced by one position, preventing starvation. The problem can be shown with an example. Have an arbitration tree with 10 inputs. Two requests want to be served in the same clock cycle. The one with the higher priority wins and the priority state advances. In the next cycle again the same two inputs have a request waiting. Again it is possible that the same port as last time wins as the priority shifted only one position further. This can lead in conjunction with the other arbitration trees in the other muxes of the crossbar to the cyclic dependencies inside the FIFO's. Now removing the spill register between the demux and mux, it forces the switching decision into the W FIFO's in the same clock cycle. This leads to a strict ordering of the switching decision,  preventing the creation of circular waiting.
