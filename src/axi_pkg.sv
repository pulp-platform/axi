// Copyright (c) 2014-2018 ETH Zurich, University of Bologna
//
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Fabian Schuiki <fschuiki@iis.ee.ethz.ch>

package axi_pkg;

  typedef logic [1:0] burst_t;
  typedef logic [1:0] resp_t;
  typedef logic [3:0] cache_t;
  typedef logic [2:0] prot_t;
  typedef logic [3:0] qos_t;
  typedef logic [3:0] region_t;
  typedef logic [7:0] len_t;
  typedef logic [2:0] size_t;
  typedef logic [5:0] atop_t; // atomic operations
  typedef logic [3:0] nsaid_t; // non-secure address identifier

  localparam BURST_FIXED = 2'b00;
  localparam BURST_INCR  = 2'b01;
  localparam BURST_WRAP  = 2'b10;

  localparam RESP_OKAY   = 2'b00;
  localparam RESP_EXOKAY = 2'b01;
  localparam RESP_SLVERR = 2'b10;
  localparam RESP_DECERR = 2'b11;

  localparam CACHE_BUFFERABLE = 4'b0001;
  localparam CACHE_MODIFIABLE = 4'b0010;
  localparam CACHE_RD_ALLOC   = 4'b0100;
  localparam CACHE_WR_ALLOC   = 4'b1000;

  // MEMORY TYPE
  typedef enum logic [3:0] {
    DEVICE_NONBUFFERABLE,
    DEVICE_BUFFERABLE,
    NORMAL_NONCACHEABLE_NONBUFFERABLE,
    NORMAL_NONCACHEABLE_BUFFERABLE,
    WTHRU_NOALLOCATE,
    WTHRU_RALLOCATE,
    WTHRU_WALLOCATE,
    WTHRU_RWALLOCATE,
    WBACK_NOALLOCATE,
    WBACK_RALLOCATE,
    WBACK_WALLOCATE,
    WBACK_RWALLOCATE
  } mem_type_t;

  function automatic logic [3:0] get_arcache(mem_type_t mtype);
    unique case (mtype)
      DEVICE_NONBUFFERABLE              : return 4'b0000;
      DEVICE_BUFFERABLE                 : return 4'b0001;
      NORMAL_NONCACHEABLE_NONBUFFERABLE : return 4'b0010;
      NORMAL_NONCACHEABLE_BUFFERABLE    : return 4'b0011;
      WTHRU_NOALLOCATE                  : return 4'b1010;
      WTHRU_RALLOCATE                   : return 4'b1110;
      WTHRU_WALLOCATE                   : return 4'b1010;
      WTHRU_RWALLOCATE                  : return 4'b1110;
      WBACK_NOALLOCATE                  : return 4'b1011;
      WBACK_RALLOCATE                   : return 4'b1111;
      WBACK_WALLOCATE                   : return 4'b1011;
      WBACK_RWALLOCATE                  : return 4'b1111;
    endcase // mtype
  endfunction

  function automatic logic [3:0] get_awcache(mem_type_t mtype);
    unique case (mtype)
      DEVICE_NONBUFFERABLE              : return 4'b0000;
      DEVICE_BUFFERABLE                 : return 4'b0001;
      NORMAL_NONCACHEABLE_NONBUFFERABLE : return 4'b0010;
      NORMAL_NONCACHEABLE_BUFFERABLE    : return 4'b0011;
      WTHRU_NOALLOCATE                  : return 4'b0110;
      WTHRU_RALLOCATE                   : return 4'b0110;
      WTHRU_WALLOCATE                   : return 4'b1110;
      WTHRU_RWALLOCATE                  : return 4'b1110;
      WBACK_NOALLOCATE                  : return 4'b0111;
      WBACK_RALLOCATE                   : return 4'b0111;
      WBACK_WALLOCATE                   : return 4'b1111;
      WBACK_RWALLOCATE                  : return 4'b1111;
    endcase // mtype
  endfunction

  // ATOP[5:0]
  localparam ATOP_ATOMICSWAP  = 6'b110000;
  localparam ATOP_ATOMICCMP   = 6'b110001;
  // ATOP[5:4]
  localparam ATOP_NONE        = 2'b00;
  localparam ATOP_ATOMICSTORE = 2'b01;
  localparam ATOP_ATOMICLOAD  = 2'b10;
  // ATOP[3]
  localparam ATOP_LITTLE_END  = 1'b0;
  localparam ATOP_BIG_END     = 1'b1;
  // ATOP[2:0]
  localparam ATOP_ADD   = 3'b000;
  localparam ATOP_CLR   = 3'b001;
  localparam ATOP_EOR   = 3'b010;
  localparam ATOP_SET   = 3'b011;
  localparam ATOP_SMAX  = 3'b100;
  localparam ATOP_SMIN  = 3'b101;
  localparam ATOP_UMAX  = 3'b110;
  localparam ATOP_UMIN  = 3'b111;

  // axi xbar configurations
  // enum for the latency modes
  typedef enum logic [2:0] {
    NO_LATENCY,
    CUT_SLV_AX,
    CUT_MST_AX,
    CUT_ALL_AX,
    CUT_SLV_PORTS,
    CUT_MST_PORTS,
    CUT_ALL_PORTS
  } xbar_latency_t;
  // cfg struct for axi_xbar.sv
  typedef struct packed {
    int unsigned   NoSlvPorts;         // # of slave ports, so many masters are connected to the xbar
    int unsigned   NoMstPorts;         // # of master ports, so many slaves are connected to the xbar
    int unsigned   MaxMstTrans;        // Maxi # of outstanding transactions per r/w per master
    int unsigned   MaxSlvTrans;        // Maxi # of outstanding write transactions per slave
    bit            FallThrough;        // AreAW -> W Fifo's in Fall through mode (1'b0 = long paths)
    xbar_latency_t LatencyMode;        // See xbar_latency_t and get_xbarlatmode
    int unsigned   AxiIdWidthSlvPorts; // Axi Id Width of the Slave Ports
    int unsigned   AxiIdUsedSlvPorts;  // this many LSB's of the SlvPortAxiId get used in demux
    int unsigned   AxiIdWidthMstPorts; // ==> $clog2(NoSLVPorts) + AxiIdWidthSlvPorts !!
    int unsigned   AxiAddrWidth;       // Axi Address Width
    int unsigned   AxiDataWidth;       // Axi Data Width
    int unsigned   NoAddrRules;        // # of Address Rules in the memory map
  } xbar_cfg_t;

  // Latenency confirurations
  // This struct holds the bits to be set for parameters SPILL_XX in axi_demux.sv and axi_mux.sv
  typedef struct packed {
    bit DemuxAw;
    bit DemuxW;
    bit DemuxB;
    bit DemuxAr;
    bit DemuxR;
    bit MuxAw;
    bit MuxW;
    bit MuxB;
    bit MuxAr;
    bit MuxR;
  } xbar_spill_t;

  function automatic xbar_spill_t get_xbarlatmode (xbar_latency_t lat);
    unique case (lat)
      NO_LATENCY    : return '{default: 1'b0}; // combinational (no spill regs)
      // one cycle latency on ax channels
      CUT_SLV_AX    : return '{DemuxAw: 1'b1, DemuxAr: 1'b1, default: 1'b0};
      // one cycle latency on ax channels
      CUT_MST_AX    : return '{MuxAw:   1'b1, MuxAr:   1'b1, default: 1'b0};
      // two cycle latency on ax channels
      CUT_ALL_AX    : return '{DemuxAw: 1'b1, DemuxAr: 1'b1,
                               MuxAw:   1'b1, MuxAr:   1'b1, default: 1'b0};
      // one cycle latency on all channels
      CUT_SLV_PORTS : return '{DemuxAw: 1'b1, DemuxW: 1'b1,  DemuxB:  1'b1,
                               DemuxAr: 1'b1, DemuxR: 1'b1,  default: 1'b0};
      // one cycle latency on all channels
      CUT_MST_PORTS : return '{MuxAw:   1'b1, MuxW:   1'b1,  MuxB:    1'b1,
                               MuxAr:   1'b1, MuxR:   1'b1,  default: 1'b0};
      CUT_ALL_PORTS : return '{default: 1'b1}; // two cycle latency on all channels
      // default is CUT_ALL_AX
      default       : return '{DemuxAw: 1'b1, DemuxAr: 1'b1,
                               MuxAw:   1'b1, MuxAr:   1'b1, default: 1'b0};
    endcase // lat
  endfunction

  // address rule struct for the axi xbar
  typedef struct packed {
    int unsigned mst_port_idx;
    logic [63:0] start_addr;
    logic [63:0] end_addr;
  } xbar_rule_64_t;

  typedef struct packed {
    int unsigned mst_port_idx;
    logic [31:0] start_addr;
    logic [31:0] end_addr;
  } xbar_rule_32_t;
endpackage
