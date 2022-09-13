// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Authors:
// - Wolfgang Roenninger <wroennin@iis.ee.ethz.ch>
// - Andreas Kurth <akurth@iis.ee.ethz.ch>
// - Fabian Schuiki <fschuiki@iis.ee.ethz.ch>

/// A synthesis test bench which instantiates various adapter variants.
module axi_synth_bench (
  input logic clk_i,
  input logic rst_ni
);

  localparam int AXI_ADDR_WIDTH[6] = '{32, 64, 1, 2, 42, 129};
  localparam int AXI_ID_USER_WIDTH[3] = '{0, 1, 8};
  localparam int NUM_SLAVE_MASTER[3] = '{1, 2, 4};

  // AXI_DATA_WIDTH = {8, 16, 32, 64, 128, 256, 512, 1024}
  for (genvar i = 0; i < 8; i++) begin
    localparam DW = (2**i) * 8;
    synth_slice #(.AW(32), .DW(DW), .IW(8), .UW(8)) s(.*);
  end

  // AXI_ADDR_WIDTH
  for (genvar i = 0; i < 6; i++) begin
    localparam int AW = AXI_ADDR_WIDTH[i];
    synth_slice #(.AW(AW), .DW(32), .IW(8), .UW(8)) s(.*);
  end

  // AXI_ID_WIDTH and AXI_USER_WIDTH
  for (genvar i = 0; i < 3; i++) begin
    localparam int UW = AXI_ID_USER_WIDTH[i];
    localparam int IW = (UW == 0) ? 1 : UW;
    synth_slice #(.AW(32), .DW(32), .IW(IW), .UW(UW)) s(.*);
  end

  // ATOP Filter
  for (genvar iID = 1; iID <= 8; iID++) begin
    localparam int IW = iID;
    for (genvar iTxn = 1; iTxn <= 12; iTxn++) begin
      localparam int WT = iTxn;
      synth_axi_atop_filter #(
        .AXI_ADDR_WIDTH     (64),
        .AXI_DATA_WIDTH     (64),
        .AXI_ID_WIDTH       (IW),
        .AXI_USER_WIDTH     (4),
        .AXI_MAX_WRITE_TXNS (WT)
      ) i_filter (.*);
    end
  end

  // AXI4-Lite crossbar
  for (genvar i = 0; i < 3; i++) begin
    synth_axi_lite_xbar #(
      .NoSlvMst  ( NUM_SLAVE_MASTER[i] )
    ) i_lite_xbar (.*);
  end

  // Clock Domain Crossing
  for (genvar i = 0; i < 6; i++) begin
    localparam int AW = AXI_ADDR_WIDTH[i];
    for (genvar j = 0; j < 3; j++) begin
      localparam IUW = AXI_ID_USER_WIDTH[j];
      synth_axi_cdc #(
        .AXI_ADDR_WIDTH (AW),
        .AXI_DATA_WIDTH (128),
        .AXI_ID_WIDTH   (IUW),
        .AXI_USER_WIDTH (IUW)
      ) i_cdc (.*);
    end
  end

  // AXI4-Lite to APB bridge
  for (genvar i_data = 0; i_data < 3; i_data++) begin
    localparam int unsigned DataWidth = (2**i_data) * 8;
    for (genvar i_slv = 0; i_slv < 3; i_slv++) begin
      synth_axi_lite_to_apb #(
        .NoApbSlaves ( NUM_SLAVE_MASTER[i_slv] ),
        .DataWidth   ( DataWidth               )
      ) i_axi_lite_to_apb (.*);
    end
  end

  // AXI4-Lite Mailbox
  for (genvar i_irq_mode = 0; i_irq_mode < 4; i_irq_mode++) begin
    localparam bit EDGE_TRIG = i_irq_mode[0];
    localparam bit ACT_HIGH  = i_irq_mode[1];
    for (genvar i_depth = 2; i_depth < 8; i_depth++) begin
      localparam int unsigned DEPTH = 2**i_depth;
      synth_axi_lite_mailbox #(
        .MAILBOX_DEPTH ( DEPTH     ),
        .IRQ_EDGE_TRIG ( EDGE_TRIG ),
        .IRQ_ACT_HIGH  ( ACT_HIGH  )
      ) i_axi_lite_mailbox (.*);
    end
  end

  // AXI Isolation module
  for (genvar i = 0; i < 6; i++) begin
    synth_axi_isolate #(
      .NumPending   ( AXI_ADDR_WIDTH[i] ),
      .AxiIdWidth   ( 32'd10            ),
      .AxiAddrWidth ( 32'd64            ),
      .AxiDataWidth ( 32'd512           ),
      .AxiUserWidth ( 32'd10            )
    ) i_synth_axi_isolate (.*);
  end

  for (genvar i = 0; i < 6; i++) begin
    localparam int unsigned SLV_PORT_ADDR_WIDTH = AXI_ADDR_WIDTH[i];
    if (SLV_PORT_ADDR_WIDTH > 12) begin
      for (genvar j = 0; j < 6; j++) begin
        localparam int unsigned MST_PORT_ADDR_WIDTH = AXI_ADDR_WIDTH[j];
        if (MST_PORT_ADDR_WIDTH > 12) begin
          synth_axi_modify_address #(
            .AXI_SLV_PORT_ADDR_WIDTH  (SLV_PORT_ADDR_WIDTH),
            .AXI_MST_PORT_ADDR_WIDTH  (MST_PORT_ADDR_WIDTH),
            .AXI_DATA_WIDTH           (128),
            .AXI_ID_WIDTH             (5),
            .AXI_USER_WIDTH           (2)
          ) i_synth_axi_modify_address ();
        end
      end
    end
  end

  // AXI4+ATOP serializer
  for (genvar i = 0; i < 6; i++) begin
    synth_axi_serializer #(
      .NumPending   ( AXI_ADDR_WIDTH[i] ),
      .AxiIdWidth   ( 32'd10            ),
      .AxiAddrWidth ( 32'd64            ),
      .AxiDataWidth ( 32'd512           ),
      .AxiUserWidth ( 32'd10            )
    ) i_synth_axi_serializer (.*);
  end

  // AXI4-Lite Registers
  for (genvar i = 0; i < 6; i++) begin
    localparam int unsigned NUM_BYTES[6] = '{1, 4, 42, 64, 129, 512};
    synth_axi_lite_regs #(
      .REG_NUM_BYTES  ( NUM_BYTES[i]      ),
      .AXI_ADDR_WIDTH ( 32'd32            ),
      .AXI_DATA_WIDTH ( 32'd32            )
    ) i_axi_lite_regs (.*);
  end

  // AXI ID width converter
  for (genvar i_iwus = 0; i_iwus < 3; i_iwus++) begin : gen_iw_upstream
    localparam int unsigned AxiIdWidthUs = AXI_ID_USER_WIDTH[i_iwus] + 1;
    for (genvar i_iwds = 0; i_iwds < 3; i_iwds++) begin : gen_iw_downstream
      localparam int unsigned AxiIdWidthDs = AXI_ID_USER_WIDTH[i_iwds] + 1;
      localparam int unsigned TableSize    = 2**AxiIdWidthDs;
      synth_axi_iw_converter # (
        .AxiSlvPortIdWidth      ( AxiIdWidthUs    ),
        .AxiMstPortIdWidth      ( AxiIdWidthDs    ),
        .AxiSlvPortMaxUniqIds   ( 2**AxiIdWidthUs ),
        .AxiSlvPortMaxTxnsPerId ( 13              ),
        .AxiSlvPortMaxTxns      ( 81              ),
        .AxiMstPortMaxUniqIds   ( 2**AxiIdWidthDs ),
        .AxiMstPortMaxTxnsPerId ( 11              ),
        .AxiAddrWidth           ( 32'd64          ),
        .AxiDataWidth           ( 32'd512         ),
        .AxiUserWidth           ( 32'd10          )
      ) i_synth_axi_iw_converter (.*);
    end
  end

  // AXI4+ATOP on chip memory slave banked
  for (genvar i = 0; i < 5; i++) begin : gen_axi_to_mem_banked_data
    for (genvar j = 0; j < 4; j++) begin : gen_axi_to_mem_banked_bank_num
      for (genvar k = 0; k < 2; k++) begin : gen_axi_to_mem_banked_bank_addr
        localparam int unsigned DATA_WIDTH_AXI[5]   = {32'd32, 32'd64, 32'd128, 32'd256, 32'd512};
        localparam int unsigned NUM_BANKS[4]        = {32'd2,  32'd4,  32'd6,   32'd8};
        localparam int unsigned ADDR_WIDTH_BANKS[2] = {32'd5,  32'd11};

        synth_axi_to_mem_banked #(
          .AxiDataWidth  ( DATA_WIDTH_AXI[i]   ),
          .BankNum       ( NUM_BANKS[j]        ),
          .BankAddrWidth ( ADDR_WIDTH_BANKS[k] )
        ) i_axi_to_mem_banked (.*);
      end
    end
  end



endmodule


module synth_slice #(
  parameter int AW = -1,
  parameter int DW = -1,
  parameter int IW = -1,
  parameter int UW = -1
)(
  input logic clk_i,
  input logic rst_ni
);

  AXI_BUS #(
    .AXI_ADDR_WIDTH(AW),
    .AXI_DATA_WIDTH(DW),
    .AXI_ID_WIDTH(IW),
    .AXI_USER_WIDTH(UW)
  ) a_full(), b_full();

  AXI_LITE #(
    .AXI_ADDR_WIDTH(AW),
    .AXI_DATA_WIDTH(DW)
  ) a_lite(), b_lite();

  axi_to_axi_lite_intf #(
    .AXI_ID_WIDTH       (IW),
    .AXI_ADDR_WIDTH     (AW),
    .AXI_DATA_WIDTH     (DW),
    .AXI_USER_WIDTH     (UW),
    .AXI_MAX_WRITE_TXNS (32'd10),
    .AXI_MAX_READ_TXNS  (32'd10),
    .FALL_THROUGH       (1'b0)
  ) a (
    .clk_i      (clk_i),
    .rst_ni     (rst_ni),
    .testmode_i (1'b0),
    .slv        (a_full.Slave),
    .mst        (a_lite.Master)
  );
  axi_lite_to_axi_intf #(
    .AXI_DATA_WIDTH (DW)
  ) b (
    .in   (b_lite.Slave),
    .slv_aw_cache_i ('0),
    .slv_ar_cache_i ('0),
    .out  (b_full.Master)
  );

endmodule


module synth_axi_atop_filter #(
  parameter int unsigned AXI_ADDR_WIDTH = 0,
  parameter int unsigned AXI_DATA_WIDTH = 0,
  parameter int unsigned AXI_ID_WIDTH = 0,
  parameter int unsigned AXI_USER_WIDTH = 0,
  parameter int unsigned AXI_MAX_WRITE_TXNS = 0
) (
  input logic clk_i,
  input logic rst_ni
);

  AXI_BUS #(
    .AXI_ADDR_WIDTH (AXI_ADDR_WIDTH),
    .AXI_DATA_WIDTH (AXI_DATA_WIDTH),
    .AXI_ID_WIDTH   (AXI_ID_WIDTH),
    .AXI_USER_WIDTH (AXI_USER_WIDTH)
  ) upstream ();

  AXI_BUS #(
    .AXI_ADDR_WIDTH (AXI_ADDR_WIDTH),
    .AXI_DATA_WIDTH (AXI_DATA_WIDTH),
    .AXI_ID_WIDTH   (AXI_ID_WIDTH),
    .AXI_USER_WIDTH (AXI_USER_WIDTH)
  ) downstream ();

  axi_atop_filter_intf #(
    .AXI_ID_WIDTH       (AXI_ID_WIDTH),
    .AXI_MAX_WRITE_TXNS (AXI_MAX_WRITE_TXNS)
  ) dut (
    .clk_i  (clk_i),
    .rst_ni (rst_ni),
    .slv    (upstream),
    .mst    (downstream)
  );
endmodule

`include "axi/typedef.svh"

module synth_axi_lite_to_apb #(
  parameter int unsigned NoApbSlaves = 0,
  parameter int unsigned DataWidth   = 0
) (
  input logic clk_i,  // Clock
  input logic rst_ni  // Asynchronous reset active low
);

  typedef logic [31:0]            addr_t;
  typedef logic [DataWidth-1:0]   data_t;
  typedef logic [DataWidth/8-1:0] strb_t;

  typedef struct packed {
    addr_t          paddr;   // same as AXI4-Lite
    axi_pkg::prot_t pprot;   // same as AXI4-Lite, specification is the same
    logic           psel;    // one request line per connected APB4 slave
    logic           penable; // enable signal shows second APB4 cycle
    logic           pwrite;  // write enable
    data_t          pwdata;  // write data, comes from W channel
    strb_t          pstrb;   // write strb, comes from W channel
  } apb_req_t;

  typedef struct packed {
    logic  pready;   // slave signals that it is ready
    data_t prdata;   // read data, connects to R channel
    logic  pslverr;  // gets translated into either `axi_pkg::RESP_OK` or `axi_pkg::RESP_SLVERR`
  } apb_resp_t;

  `AXI_LITE_TYPEDEF_AW_CHAN_T(aw_chan_t, addr_t)
  `AXI_LITE_TYPEDEF_W_CHAN_T(w_chan_t, data_t, strb_t)
  `AXI_LITE_TYPEDEF_B_CHAN_T(b_chan_t)
  `AXI_LITE_TYPEDEF_AR_CHAN_T(ar_chan_t, addr_t)
  `AXI_LITE_TYPEDEF_R_CHAN_T(r_chan_t, data_t)
  `AXI_LITE_TYPEDEF_REQ_T(axi_req_t, aw_chan_t, w_chan_t, ar_chan_t)
  `AXI_LITE_TYPEDEF_RESP_T(axi_resp_t, b_chan_t, r_chan_t)

  axi_req_t                    axi_req;
  axi_resp_t                   axi_resp;
  apb_req_t  [NoApbSlaves-1:0] apb_req;
  apb_resp_t [NoApbSlaves-1:0] apb_resp;

  axi_pkg::xbar_rule_32_t [NoApbSlaves-1:0] addr_map;

  axi_lite_to_apb #(
    .NoApbSlaves     ( NoApbSlaves             ),
    .NoRules         ( NoApbSlaves             ),
    .AddrWidth       ( 32'd32                  ),
    .DataWidth       ( DataWidth               ),
    .axi_lite_req_t  ( axi_req_t               ),
    .axi_lite_resp_t ( axi_resp_t              ),
    .apb_req_t       ( apb_req_t               ),
    .apb_resp_t      ( apb_resp_t              ),
    .rule_t          ( axi_pkg::xbar_rule_32_t )
  ) i_axi_lite_to_apb_dut (
    .clk_i           ( clk_i    ),
    .rst_ni          ( rst_ni   ),
    .axi_lite_req_i  ( axi_req  ),
    .axi_lite_resp_o ( axi_resp ),
    .apb_req_o       ( apb_req  ),
    .apb_resp_i      ( apb_resp ),
    .addr_map_i      ( addr_map )
  );

endmodule

module synth_axi_cdc #(
  parameter int unsigned AXI_ADDR_WIDTH = 0,
  parameter int unsigned AXI_DATA_WIDTH = 0,
  parameter int unsigned AXI_ID_WIDTH = 0,
  parameter int unsigned AXI_USER_WIDTH = 0
) (
  input logic clk_i,
  input logic rst_ni
);

  AXI_BUS #(
    .AXI_ADDR_WIDTH (AXI_ADDR_WIDTH),
    .AXI_DATA_WIDTH (AXI_DATA_WIDTH),
    .AXI_ID_WIDTH   (AXI_ID_WIDTH),
    .AXI_USER_WIDTH (AXI_USER_WIDTH)
  ) upstream ();

  AXI_BUS #(
    .AXI_ADDR_WIDTH (AXI_ADDR_WIDTH),
    .AXI_DATA_WIDTH (AXI_DATA_WIDTH),
    .AXI_ID_WIDTH   (AXI_ID_WIDTH),
    .AXI_USER_WIDTH (AXI_USER_WIDTH)
  ) downstream ();

  axi_cdc_intf #(
    .AXI_ID_WIDTH   (AXI_ID_WIDTH),
    .AXI_ADDR_WIDTH (AXI_ADDR_WIDTH),
    .AXI_DATA_WIDTH (AXI_DATA_WIDTH),
    .AXI_USER_WIDTH (AXI_USER_WIDTH),
    .LOG_DEPTH      (2)
  ) dut (
    .src_clk_i  (clk_i),
    .src_rst_ni (rst_ni),
    .src        (upstream),
    .dst_clk_i  (clk_i),
    .dst_rst_ni (rst_ni),
    .dst        (downstream)
  );

endmodule

`include "axi/typedef.svh"

module synth_axi_lite_xbar #(
  parameter int unsigned NoSlvMst = 32'd1
) (
  input logic clk_i,  // Clock
  input logic rst_ni  // Asynchronous reset active low
);
  typedef logic [32'd32-1:0]   addr_t;
  typedef logic [32'd32-1:0]   data_t;
  typedef logic [32'd32/8-1:0] strb_t;

  `AXI_LITE_TYPEDEF_AW_CHAN_T(aw_chan_t, addr_t)
  `AXI_LITE_TYPEDEF_W_CHAN_T(w_chan_t, data_t, strb_t)
  `AXI_LITE_TYPEDEF_B_CHAN_T(b_chan_t)
  `AXI_LITE_TYPEDEF_AR_CHAN_T(ar_chan_t, addr_t)
  `AXI_LITE_TYPEDEF_R_CHAN_T(r_chan_t, data_t)
  `AXI_LITE_TYPEDEF_REQ_T(axi_req_t, aw_chan_t, w_chan_t, ar_chan_t)
  `AXI_LITE_TYPEDEF_RESP_T(axi_resp_t, b_chan_t, r_chan_t)
  localparam axi_pkg::xbar_cfg_t XbarCfg = '{
    NoSlvPorts:         NoSlvMst,
    NoMstPorts:         NoSlvMst,
    MaxMstTrans:        32'd5,
    MaxSlvTrans:        32'd5,
    FallThrough:        1'b1,
    LatencyMode:        axi_pkg::CUT_ALL_PORTS,
    AxiAddrWidth:       32'd32,
    AxiDataWidth:       32'd32,
    NoAddrRules:        NoSlvMst,
    default:            '0
  };

  axi_pkg::xbar_rule_32_t [NoSlvMst-1:0] addr_map;
  logic                                  test;
  axi_req_t               [NoSlvMst-1:0] mst_reqs,  slv_reqs;
  axi_resp_t              [NoSlvMst-1:0] mst_resps, slv_resps;

  axi_lite_xbar #(
    .Cfg        ( XbarCfg                 ),
    .aw_chan_t  (  aw_chan_t              ),
    .w_chan_t   (   w_chan_t              ),
    .b_chan_t   (   b_chan_t              ),
    .ar_chan_t  (  ar_chan_t              ),
    .r_chan_t   (   r_chan_t              ),
    .axi_req_t  (  axi_req_t              ),
    .axi_resp_t ( axi_resp_t              ),
    .rule_t     ( axi_pkg::xbar_rule_32_t )
  ) i_xbar_dut (
    .clk_i                 ( clk_i     ),
    .rst_ni                ( rst_ni    ),
    .test_i                ( test      ),
    .slv_ports_req_i       ( mst_reqs  ),
    .slv_ports_resp_o      ( mst_resps ),
    .mst_ports_req_o       ( slv_reqs  ),
    .mst_ports_resp_i      ( slv_resps ),
    .addr_map_i            ( addr_map  ),
    .en_default_mst_port_i ( '0        ),
    .default_mst_port_i    ( '0        )
  );
endmodule

module synth_axi_lite_mailbox #(
  parameter int unsigned MAILBOX_DEPTH = 32'd1,
  parameter bit          IRQ_EDGE_TRIG = 1'b0,
  parameter bit          IRQ_ACT_HIGH  = 1'b0
) (
  input logic clk_i,  // Clock
  input logic rst_ni  // Asynchronous reset active low
);
  typedef logic [32'd32-1:0]   addr_t;

  AXI_LITE #(
    .AXI_ADDR_WIDTH (32'd32),
    .AXI_DATA_WIDTH (32'd32)
  ) slv [1:0] ();

  logic        test;
  logic  [1:0] irq;
  addr_t [1:0] base_addr;

  axi_lite_mailbox_intf #(
    .MAILBOX_DEPTH  ( MAILBOX_DEPTH  ),
    .IRQ_EDGE_TRIG  ( IRQ_EDGE_TRIG  ),
    .IRQ_ACT_HIGH   ( IRQ_ACT_HIGH   ),
    .AXI_ADDR_WIDTH ( 32'd32         ),
    .AXI_DATA_WIDTH ( 32'd32         )
  ) i_axi_lite_mailbox (
    .clk_i       ( clk_i     ), // Clock
    .rst_ni      ( rst_ni    ), // Asynchronous reset active low
    .test_i      ( test      ), // Testmode enable
    // slave ports [1:0]
    .slv         ( slv       ),
    .irq_o       ( irq       ), // interrupt output for each port
    .base_addr_i ( base_addr )  // base address for each port
  );
endmodule

module synth_axi_isolate #(
  parameter int unsigned NumPending   = 32'd16, // number of pending requests
  parameter int unsigned AxiIdWidth   = 32'd0,  // AXI ID width
  parameter int unsigned AxiAddrWidth = 32'd0,  // AXI address width
  parameter int unsigned AxiDataWidth = 32'd0,  // AXI data width
  parameter int unsigned AxiUserWidth = 32'd0   // AXI user width
) (
  input clk_i,
  input rst_ni
);

  AXI_BUS #(
    .AXI_ADDR_WIDTH ( AxiIdWidth   ),
    .AXI_DATA_WIDTH ( AxiAddrWidth ),
    .AXI_ID_WIDTH   ( AxiDataWidth ),
    .AXI_USER_WIDTH ( AxiUserWidth )
  ) axi[1:0] ();

  logic isolate, isolated;

  axi_isolate_intf #(
    .NUM_PENDING    ( NumPending   ), // number of pending requests
    .AXI_ID_WIDTH   ( AxiIdWidth   ), // AXI ID width
    .AXI_ADDR_WIDTH ( AxiAddrWidth ), // AXI address width
    .AXI_DATA_WIDTH ( AxiDataWidth ), // AXI data width
    .AXI_USER_WIDTH ( AxiUserWidth )  // AXI user width
  ) i_axi_isolate_dut (
    .clk_i,
    .rst_ni,
    .slv        ( axi[0]   ), // slave port
    .mst        ( axi[1]   ), // master port
    .isolate_i  ( isolate  ), // isolate master port from slave port
    .isolated_o ( isolated )  // master port is isolated from slave port
  );
endmodule

module synth_axi_modify_address #(
  parameter int unsigned AXI_SLV_PORT_ADDR_WIDTH = 0,
  parameter int unsigned AXI_MST_PORT_ADDR_WIDTH = 0,
  parameter int unsigned AXI_DATA_WIDTH = 0,
  parameter int unsigned AXI_ID_WIDTH = 0,
  parameter int unsigned AXI_USER_WIDTH = 0
) ();

  AXI_BUS #(
    .AXI_ADDR_WIDTH (AXI_SLV_PORT_ADDR_WIDTH),
    .AXI_DATA_WIDTH (AXI_DATA_WIDTH),
    .AXI_ID_WIDTH   (AXI_ID_WIDTH),
    .AXI_USER_WIDTH (AXI_USER_WIDTH)
  ) upstream ();

  AXI_BUS #(
    .AXI_ADDR_WIDTH (AXI_MST_PORT_ADDR_WIDTH),
    .AXI_DATA_WIDTH (AXI_DATA_WIDTH),
    .AXI_ID_WIDTH   (AXI_ID_WIDTH),
    .AXI_USER_WIDTH (AXI_USER_WIDTH)
  ) downstream ();

  logic [AXI_MST_PORT_ADDR_WIDTH-1:0] mst_aw_addr,
                                      mst_ar_addr;
  axi_modify_address_intf #(
    .AXI_SLV_PORT_ADDR_WIDTH  (AXI_SLV_PORT_ADDR_WIDTH),
    .AXI_MST_PORT_ADDR_WIDTH  (AXI_MST_PORT_ADDR_WIDTH),
    .AXI_DATA_WIDTH           (AXI_DATA_WIDTH),
    .AXI_ID_WIDTH             (AXI_ID_WIDTH),
    .AXI_USER_WIDTH           (AXI_USER_WIDTH)
  ) dut (
    .slv            (upstream),
    .mst_aw_addr_i  (mst_aw_addr),
    .mst_ar_addr_i  (mst_ar_addr),
    .mst            (downstream)
  );
endmodule

module synth_axi_serializer #(
  parameter int unsigned NumPending   = 32'd16, // number of pending requests
  parameter int unsigned AxiIdWidth   = 32'd0,  // AXI ID width
  parameter int unsigned AxiAddrWidth = 32'd0,  // AXI address width
  parameter int unsigned AxiDataWidth = 32'd0,  // AXI data width
  parameter int unsigned AxiUserWidth = 32'd0   // AXI user width
) (
  input clk_i,
  input rst_ni
);

  AXI_BUS #(
    .AXI_ADDR_WIDTH ( AxiIdWidth   ),
    .AXI_DATA_WIDTH ( AxiAddrWidth ),
    .AXI_ID_WIDTH   ( AxiDataWidth ),
    .AXI_USER_WIDTH ( AxiUserWidth )
  ) axi[1:0] ();

  axi_serializer_intf #(
    .MAX_READ_TXNS  ( NumPending   ), // Number of pending requests
    .MAX_WRITE_TXNS ( NumPending   ), // Number of pending requests
    .AXI_ID_WIDTH   ( AxiIdWidth   ), // AXI ID width
    .AXI_ADDR_WIDTH ( AxiAddrWidth ), // AXI address width
    .AXI_DATA_WIDTH ( AxiDataWidth ), // AXI data width
    .AXI_USER_WIDTH ( AxiUserWidth )  // AXI user width
  ) i_axi_isolate_dut (
    .clk_i,
    .rst_ni,
    .slv        ( axi[0]   ), // slave port
    .mst        ( axi[1]   )  // master port
  );
endmodule

module synth_axi_lite_regs #(
  parameter int unsigned REG_NUM_BYTES  = 32'd0,
  parameter int unsigned AXI_ADDR_WIDTH = 32'd0,
  parameter int unsigned AXI_DATA_WIDTH = 32'd0
) (
  input logic clk_i,
  input logic rst_ni
);
  typedef logic [7:0] byte_t;

  AXI_LITE #(
    .AXI_ADDR_WIDTH ( AXI_ADDR_WIDTH ),
    .AXI_DATA_WIDTH ( AXI_DATA_WIDTH )
  ) slv ();

  logic  [REG_NUM_BYTES-1:0] wr_active, rd_active;
  byte_t [REG_NUM_BYTES-1:0] reg_d,     reg_q;
  logic  [REG_NUM_BYTES-1:0] reg_load;

  axi_lite_regs_intf #(
    .REG_NUM_BYTES  ( REG_NUM_BYTES          ),
    .AXI_ADDR_WIDTH ( AXI_ADDR_WIDTH         ),
    .AXI_DATA_WIDTH ( AXI_DATA_WIDTH         ),
    .PRIV_PROT_ONLY ( 1'd0                   ),
    .SECU_PROT_ONLY ( 1'd0                   ),
    .AXI_READ_ONLY  ( {REG_NUM_BYTES{1'b0}}  ),
    .REG_RST_VAL    ( {REG_NUM_BYTES{8'h00}} )
  ) i_axi_lite_regs (
    .clk_i,
    .rst_ni,
    .slv         ( slv         ),
    .wr_active_o ( wr_active   ),
    .rd_active_o ( rd_active   ),
    .reg_d_i     ( reg_d       ),
    .reg_load_i  ( reg_load    ),
    .reg_q_o     ( reg_q       )
  );
endmodule

module synth_axi_iw_converter # (
  parameter int unsigned AxiSlvPortIdWidth = 32'd0,
  parameter int unsigned AxiMstPortIdWidth = 32'd0,
  parameter int unsigned AxiSlvPortMaxUniqIds = 32'd0,
  parameter int unsigned AxiSlvPortMaxTxnsPerId = 32'd0,
  parameter int unsigned AxiSlvPortMaxTxns = 32'd0,
  parameter int unsigned AxiMstPortMaxUniqIds = 32'd0,
  parameter int unsigned AxiMstPortMaxTxnsPerId = 32'd0,
  parameter int unsigned AxiAddrWidth = 32'd0,
  parameter int unsigned AxiDataWidth = 32'd0,
  parameter int unsigned AxiUserWidth = 32'd0
) (
  input logic clk_i,
  input logic rst_ni
);
  AXI_BUS #(
    .AXI_ADDR_WIDTH ( AxiAddrWidth      ),
    .AXI_DATA_WIDTH ( AxiDataWidth      ),
    .AXI_ID_WIDTH   ( AxiSlvPortIdWidth ),
    .AXI_USER_WIDTH ( AxiUserWidth      )
  ) upstream ();
  AXI_BUS #(
    .AXI_ADDR_WIDTH ( AxiAddrWidth      ),
    .AXI_DATA_WIDTH ( AxiDataWidth      ),
    .AXI_ID_WIDTH   ( AxiMstPortIdWidth ),
    .AXI_USER_WIDTH ( AxiUserWidth      )
  ) downstream ();

  axi_iw_converter_intf #(
    .AXI_SLV_PORT_ID_WIDTH        (AxiSlvPortIdWidth      ),
    .AXI_MST_PORT_ID_WIDTH        (AxiMstPortIdWidth      ),
    .AXI_SLV_PORT_MAX_UNIQ_IDS    (AxiMstPortIdWidth      ),
    .AXI_SLV_PORT_MAX_TXNS_PER_ID (AxiSlvPortMaxTxnsPerId ),
    .AXI_SLV_PORT_MAX_TXNS        (AxiSlvPortMaxTxns      ),
    .AXI_MST_PORT_MAX_UNIQ_IDS    (AxiMstPortMaxUniqIds   ),
    .AXI_MST_PORT_MAX_TXNS_PER_ID (AxiMstPortMaxTxnsPerId ),
    .AXI_ADDR_WIDTH               (AxiAddrWidth           ),
    .AXI_DATA_WIDTH               (AxiDataWidth           ),
    .AXI_USER_WIDTH               (AxiUserWidth           )
  ) i_axi_iw_converter_dut (
    .clk_i,
    .rst_ni,
    .slv     ( upstream   ),
    .mst     ( downstream )
  );
endmodule

module synth_axi_to_mem_banked #(
  parameter int unsigned AxiDataWidth  = 32'd0,
  parameter int unsigned BankNum       = 32'd0,
  parameter int unsigned BankAddrWidth = 32'd0
) (
  input logic clk_i,
  input logic rst_ni
);
  localparam int unsigned AxiIdWidth    = 32'd10;
  localparam int unsigned AxiAddrWidth  = 32'd64;
  localparam int unsigned AxiStrbWidth  = AxiDataWidth / 32'd8;
  localparam int unsigned AxiUserWidth  = 32'd8;
  localparam int unsigned BankDataWidth = 32'd2 * AxiDataWidth / BankNum;
  localparam int unsigned BankStrbWidth = BankDataWidth / 32'd8;
  localparam int unsigned BankLatency   = 32'd1;

  typedef logic [BankAddrWidth-1:0] mem_addr_t;
  typedef logic [BankDataWidth-1:0] mem_data_t;
  typedef logic [BankStrbWidth-1:0] mem_strb_t;

  AXI_BUS #(
    .AXI_ADDR_WIDTH ( AxiIdWidth   ),
    .AXI_DATA_WIDTH ( AxiAddrWidth ),
    .AXI_ID_WIDTH   ( AxiDataWidth ),
    .AXI_USER_WIDTH ( AxiUserWidth )
  ) axi ();

  // Misc signals
  logic                             test;
  logic           [1:0]             axi_to_mem_busy;
  // Signals for mem macros
  logic           [BankNum-1:0] mem_req;
  logic           [BankNum-1:0] mem_gnt;
  mem_addr_t      [BankNum-1:0] mem_addr;
  logic           [BankNum-1:0] mem_we;
  mem_data_t      [BankNum-1:0] mem_wdata;
  mem_strb_t      [BankNum-1:0] mem_be;
  axi_pkg::atop_t [BankNum-1:0] mem_atop;
  mem_data_t      [BankNum-1:0] mem_rdata;


  axi_to_mem_banked_intf #(
    .AXI_ID_WIDTH    ( AxiIdWidth    ),
    .AXI_ADDR_WIDTH  ( AxiAddrWidth  ),
    .AXI_DATA_WIDTH  ( AxiDataWidth  ),
    .AXI_USER_WIDTH  ( AxiUserWidth  ),
    .MEM_NUM_BANKS   ( BankNum       ),
    .MEM_ADDR_WIDTH  ( BankAddrWidth ),
    .MEM_DATA_WIDTH  ( BankDataWidth ),
    .MEM_LATENCY     ( BankLatency   )
  ) i_axi_to_mem_banked_intf (
    .clk_i,
    .rst_ni,
    .test_i            ( test            ),
    .slv               ( axi             ),
    .mem_req_o         ( mem_req         ),
    .mem_gnt_i         ( mem_gnt         ),
    .mem_add_o         ( mem_addr        ),
    .mem_we_o          ( mem_we          ),
    .mem_wdata_o       ( mem_wdata       ),
    .mem_be_o          ( mem_be          ),
    .mem_atop_o        ( mem_atop        ),
    .mem_rdata_i       ( mem_rdata       ),
    .axi_to_mem_busy_o ( axi_to_mem_busy )
  );

endmodule

module synth_axi_demux import axi_pkg::*; #(
  parameter int unsigned   NoMstPorts      = 32'd8,
  parameter bit            UniqueIds       = 0,
  parameter xbar_latency_e LatencyMode     = NO_LATENCY,
  // axi configuration
  parameter int unsigned AxiIdWidthMasters =  4,
  parameter int unsigned AxiIdUsed         =  3, // Has to be <= AxiIdWidthMasters
  parameter int unsigned AxiAddrWidth      =  32,    // Axi Address Width
  parameter int unsigned AxiDataWidth      =  32,    // Axi Data Width
  parameter int unsigned AxiStrbWidth      =  AxiDataWidth / 8,
  parameter int unsigned AxiUserWidth      =  1,
  // axi types
  parameter type id_t                      = logic [AxiIdWidthMasters-1:0],
  parameter type addr_t                    = logic [AxiAddrWidth-1:0],
  parameter type data_t                    = logic [AxiDataWidth-1:0],
  parameter type strb_t                    = logic [AxiStrbWidth-1:0],
  parameter type user_t                    = logic [AxiUserWidth-1:0],
  // select signal types
  parameter int unsigned SelectWidth       = (NoMstPorts > 32'd1) ? $clog2(NoMstPorts) : 32'd1,
  parameter type         select_t          = logic [SelectWidth-1:0]
) (
  input  logic clk_i,
  input  logic rst_ni,

  // Select signals
  input  select_t slv_aw_select_i,
  input  select_t slv_ar_select_i,

  /***********************************
  /* Slave ports request inputs
  ***********************************/

  // AW
  input id_t              slv_aw_id,
  input addr_t            slv_aw_addr,
  input axi_pkg::len_t    slv_aw_len,
  input axi_pkg::size_t   slv_aw_size,
  input axi_pkg::burst_t  slv_aw_burst,
  input logic             slv_aw_lock,
  input axi_pkg::cache_t  slv_aw_cache,
  input axi_pkg::prot_t   slv_aw_prot,
  input axi_pkg::qos_t    slv_aw_qos,
  input axi_pkg::region_t slv_aw_region,
  input axi_pkg::atop_t   slv_aw_atop,
  input user_t            slv_aw_user,
  input logic             slv_aw_valid,
  // W
  input data_t            slv_w_data,
  input strb_t            slv_w_strb,
  input logic             slv_w_last,
  input user_t            slv_w_user,
  input logic             slv_w_valid,
  // B
  input logic             slv_b_ready,
  // AR
  input id_t              slv_ar_id,
  input addr_t            slv_ar_addr,
  input axi_pkg::len_t    slv_ar_len,
  input axi_pkg::size_t   slv_ar_size,
  input axi_pkg::burst_t  slv_ar_burst,
  input logic             slv_ar_lock,
  input axi_pkg::cache_t  slv_ar_cache,
  input axi_pkg::prot_t   slv_ar_prot,
  input axi_pkg::qos_t    slv_ar_qos,
  input axi_pkg::region_t slv_ar_region,
  input user_t            slv_ar_user,
  input logic             slv_ar_valid,
  // R
  input logic             slv_r_ready,

  /***********************************
  /* Slave ports response outputs
  ***********************************/

  // AW
  output logic           slv_aw_ready,
  // AR
  output logic           slv_ar_ready,
  // W
  output logic           slv_w_ready,
  // B
  output logic           slv_b_valid,
  output id_t            slv_b_id,
  output axi_pkg::resp_t slv_b_resp,
  output user_t          slv_b_user,
  // R
  output logic           slv_r_valid,
  output id_t            slv_r_id,
  output data_t          slv_r_data,
  output axi_pkg::resp_t slv_r_resp,
  output logic           slv_r_last,
  output user_t          slv_r_user,

  /***********************************
  /* Master ports request outputs
  ***********************************/

  // AW
  output id_t              [NoMstPorts-1:0] mst_aw_id,
  output addr_t            [NoMstPorts-1:0] mst_aw_addr,
  output axi_pkg::len_t    [NoMstPorts-1:0] mst_aw_len,
  output axi_pkg::size_t   [NoMstPorts-1:0] mst_aw_size,
  output axi_pkg::burst_t  [NoMstPorts-1:0] mst_aw_burst,
  output logic             [NoMstPorts-1:0] mst_aw_lock,
  output axi_pkg::cache_t  [NoMstPorts-1:0] mst_aw_cache,
  output axi_pkg::prot_t   [NoMstPorts-1:0] mst_aw_prot,
  output axi_pkg::qos_t    [NoMstPorts-1:0] mst_aw_qos,
  output axi_pkg::region_t [NoMstPorts-1:0] mst_aw_region,
  output axi_pkg::atop_t   [NoMstPorts-1:0] mst_aw_atop,
  output user_t            [NoMstPorts-1:0] mst_aw_user,
  output logic             [NoMstPorts-1:0] mst_aw_valid,
  // W
  output data_t            [NoMstPorts-1:0] mst_w_data,
  output strb_t            [NoMstPorts-1:0] mst_w_strb,
  output logic             [NoMstPorts-1:0] mst_w_last,
  output user_t            [NoMstPorts-1:0] mst_w_user,
  output logic             [NoMstPorts-1:0] mst_w_valid,
  // B
  output logic             [NoMstPorts-1:0] mst_b_ready,
  // AR
  output id_t              [NoMstPorts-1:0] mst_ar_id,
  output addr_t            [NoMstPorts-1:0] mst_ar_addr,
  output axi_pkg::len_t    [NoMstPorts-1:0] mst_ar_len,
  output axi_pkg::size_t   [NoMstPorts-1:0] mst_ar_size,
  output axi_pkg::burst_t  [NoMstPorts-1:0] mst_ar_burst,
  output logic             [NoMstPorts-1:0] mst_ar_lock,
  output axi_pkg::cache_t  [NoMstPorts-1:0] mst_ar_cache,
  output axi_pkg::prot_t   [NoMstPorts-1:0] mst_ar_prot,
  output axi_pkg::qos_t    [NoMstPorts-1:0] mst_ar_qos,
  output axi_pkg::region_t [NoMstPorts-1:0] mst_ar_region,
  output user_t            [NoMstPorts-1:0] mst_ar_user,
  output logic             [NoMstPorts-1:0] mst_ar_valid,
  // R
  output logic             [NoMstPorts-1:0] mst_r_ready,

  /***********************************
  /* Master ports response inputs
  ***********************************/

  // AW
  input logic           [NoMstPorts-1:0] mst_aw_ready,
  // AR
  input logic           [NoMstPorts-1:0] mst_ar_ready,
  // W
  input logic           [NoMstPorts-1:0] mst_w_ready,
  // B
  input logic           [NoMstPorts-1:0] mst_b_valid,
  input id_t            [NoMstPorts-1:0] mst_b_id,
  input axi_pkg::resp_t [NoMstPorts-1:0] mst_b_resp,
  input user_t          [NoMstPorts-1:0] mst_b_user,
  // R
  input logic           [NoMstPorts-1:0] mst_r_valid,
  input id_t            [NoMstPorts-1:0] mst_r_id,
  input data_t          [NoMstPorts-1:0] mst_r_data,
  input axi_pkg::resp_t [NoMstPorts-1:0] mst_r_resp,
  input logic           [NoMstPorts-1:0] mst_r_last,
  input user_t          [NoMstPorts-1:0] mst_r_user

);

  `AXI_TYPEDEF_AW_CHAN_T(aw_chan_t, addr_t, id_t, user_t)
  `AXI_TYPEDEF_W_CHAN_T(w_chan_t, data_t, strb_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T(b_chan_t, id_t, user_t)

  `AXI_TYPEDEF_AR_CHAN_T(ar_chan_t, addr_t, id_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(r_chan_t, data_t, id_t, user_t)

  `AXI_TYPEDEF_REQ_T(req_t, aw_chan_t, w_chan_t, ar_chan_t)
  `AXI_TYPEDEF_RESP_T(resp_t, b_chan_t, r_chan_t)

  req_t                   slv_req;
  req_t  [NoMstPorts-1:0] mst_reqs;
  resp_t                  slv_resp;
  resp_t [NoMstPorts-1:0] mst_resps;

  // Connect XBAR interfaces
  assign slv_req.aw.id     = slv_aw_id;
  assign slv_req.aw.addr   = slv_aw_addr;
  assign slv_req.aw.len    = slv_aw_len;
  assign slv_req.aw.size   = slv_aw_size;
  assign slv_req.aw.burst  = slv_aw_burst;
  assign slv_req.aw.lock   = slv_aw_lock;
  assign slv_req.aw.cache  = slv_aw_cache;
  assign slv_req.aw.prot   = slv_aw_prot;
  assign slv_req.aw.qos    = slv_aw_qos;
  assign slv_req.aw.region = slv_aw_region;
  assign slv_req.aw.atop   = slv_aw_atop;
  assign slv_req.aw.user   = slv_aw_user;
  assign slv_req.aw_valid  = slv_aw_valid;
  assign slv_req.w.data    = slv_w_data;
  assign slv_req.w.strb    = slv_w_strb;
  assign slv_req.w.last    = slv_w_last;
  assign slv_req.w.user    = slv_w_user;
  assign slv_req.w_valid   = slv_w_valid;
  assign slv_req.b_ready   = slv_b_ready;
  assign slv_req.ar.id     = slv_ar_id;
  assign slv_req.ar.addr   = slv_ar_addr;
  assign slv_req.ar.len    = slv_ar_len;
  assign slv_req.ar.size   = slv_ar_size;
  assign slv_req.ar.burst  = slv_ar_burst;
  assign slv_req.ar.lock   = slv_ar_lock;
  assign slv_req.ar.cache  = slv_ar_cache;
  assign slv_req.ar.prot   = slv_ar_prot;
  assign slv_req.ar.qos    = slv_ar_qos;
  assign slv_req.ar.region = slv_ar_region;
  assign slv_req.ar.user   = slv_ar_user;
  assign slv_req.ar_valid  = slv_ar_valid;
  assign slv_req.r_ready   = slv_r_ready;
  // Response
  assign slv_aw_ready = slv_resp.aw_ready;
  assign slv_ar_ready = slv_resp.ar_ready;
  assign slv_w_ready  = slv_resp.w_ready;
  assign slv_b_valid  = slv_resp.b_valid;
  assign slv_b_id     = slv_resp.b.id;
  assign slv_b_resp   = slv_resp.b.resp;
  assign slv_b_user   = slv_resp.b.user;
  assign slv_r_valid  = slv_resp.r_valid;
  assign slv_r_id     = slv_resp.r.id;
  assign slv_r_data   = slv_resp.r.data;
  assign slv_r_resp   = slv_resp.r.resp;
  assign slv_r_last   = slv_resp.r.last;
  assign slv_r_user   = slv_resp.r.user;

  generate
    for (genvar i = 0; i < NoMstPorts; i++) begin : g_connect_mst_port
      // Request
      assign mst_aw_id[i]     = mst_reqs[i].aw.id;
      assign mst_aw_addr[i]   = mst_reqs[i].aw.addr;
      assign mst_aw_len[i]    = mst_reqs[i].aw.len;
      assign mst_aw_size[i]   = mst_reqs[i].aw.size;
      assign mst_aw_burst[i]  = mst_reqs[i].aw.burst;
      assign mst_aw_lock[i]   = mst_reqs[i].aw.lock;
      assign mst_aw_cache[i]  = mst_reqs[i].aw.cache;
      assign mst_aw_prot[i]   = mst_reqs[i].aw.prot;
      assign mst_aw_qos[i]    = mst_reqs[i].aw.qos;
      assign mst_aw_region[i] = mst_reqs[i].aw.region;
      assign mst_aw_atop[i]   = mst_reqs[i].aw.atop;
      assign mst_aw_user[i]   = mst_reqs[i].aw.user;
      assign mst_aw_valid[i]  = mst_reqs[i].aw_valid;
      assign mst_w_data[i]    = mst_reqs[i].w.data;
      assign mst_w_strb[i]    = mst_reqs[i].w.strb;
      assign mst_w_last[i]    = mst_reqs[i].w.last;
      assign mst_w_user[i]    = mst_reqs[i].w.user;
      assign mst_w_valid[i]   = mst_reqs[i].w_valid;
      assign mst_b_ready[i]   = mst_reqs[i].b_ready;
      assign mst_ar_id[i]     = mst_reqs[i].ar.id;
      assign mst_ar_addr[i]   = mst_reqs[i].ar.addr;
      assign mst_ar_len[i]    = mst_reqs[i].ar.len;
      assign mst_ar_size[i]   = mst_reqs[i].ar.size;
      assign mst_ar_burst[i]  = mst_reqs[i].ar.burst;
      assign mst_ar_lock[i]   = mst_reqs[i].ar.lock;
      assign mst_ar_cache[i]  = mst_reqs[i].ar.cache;
      assign mst_ar_prot[i]   = mst_reqs[i].ar.prot;
      assign mst_ar_qos[i]    = mst_reqs[i].ar.qos;
      assign mst_ar_region[i] = mst_reqs[i].ar.region;
      assign mst_ar_user[i]   = mst_reqs[i].ar.user;
      assign mst_ar_valid[i]  = mst_reqs[i].ar_valid;
      assign mst_r_ready[i]   = mst_reqs[i].r_ready;
      // Response
      assign mst_resps[i].aw_ready = mst_aw_ready[i];
      assign mst_resps[i].ar_ready = mst_ar_ready[i];
      assign mst_resps[i].w_ready  = mst_w_ready[i];
      assign mst_resps[i].b_valid  = mst_b_valid[i];
      assign mst_resps[i].b.id     = mst_b_id[i];
      assign mst_resps[i].b.resp   = mst_b_resp[i];
      assign mst_resps[i].b.user   = mst_b_user[i];
      assign mst_resps[i].r_valid  = mst_r_valid[i];
      assign mst_resps[i].r.id     = mst_r_id[i];
      assign mst_resps[i].r.data   = mst_r_data[i];
      assign mst_resps[i].r.resp   = mst_r_resp[i];
      assign mst_resps[i].r.last   = mst_r_last[i];
      assign mst_resps[i].r.user   = mst_r_user[i];
    end
  endgenerate

  axi_demux #(
    .AxiIdWidth (AxiIdWidthMasters),
    .AtopSupport(1'b0),
    .aw_chan_t  (aw_chan_t),
    .w_chan_t   (w_chan_t),
    .b_chan_t   (b_chan_t),
    .ar_chan_t  (ar_chan_t),
    .r_chan_t   (r_chan_t),
    .axi_req_t  (req_t),
    .axi_resp_t (resp_t),
    .NoMstPorts (NoMstPorts),
    .MaxTrans   (10),
    .AxiLookBits(AxiIdUsed),
    .UniqueIds  (UniqueIds),
    .FallThrough(1'b0),
    .SpillAw    (LatencyMode[9]),
    .SpillW     (LatencyMode[8]),
    .SpillB     (LatencyMode[7]),
    .SpillAr    (LatencyMode[6]),
    .SpillR     (LatencyMode[5])
  ) i_axi_demux (
    .clk_i          (clk_i),
    .rst_ni         (rst_ni),
    .test_i         ('0),
    .slv_req_i      (slv_req),
    .slv_aw_select_i(slv_aw_select_i),
    .slv_ar_select_i(slv_ar_select_i),
    .slv_resp_o     (slv_resp),
    .mst_reqs_o     (mst_reqs),
    .mst_resps_i    (mst_resps)
  );
endmodule
