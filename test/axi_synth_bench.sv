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
// - Michael Rogenmoser <michaero@iis.ee.ethz.ch>

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
      .NumPending ( AXI_ADDR_WIDTH[i] ),
      .IdWidth    ( 32'd10            ),
      .AddrWidth  ( 32'd64            ),
      .DataWidth  ( 32'd512           ),
      .UserWidth  ( 32'd10            )
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
      .NumPending ( AXI_ADDR_WIDTH[i] ),
      .IdWidth    ( 32'd10            ),
      .AddrWidth  ( 32'd64            ),
      .DataWidth  ( 32'd512           ),
      .UserWidth  ( 32'd10            )
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
    localparam int unsigned IdWidthUs = AXI_ID_USER_WIDTH[i_iwus] + 1;
    for (genvar i_iwds = 0; i_iwds < 3; i_iwds++) begin : gen_iw_downstream
      localparam int unsigned IdWidthDs = AXI_ID_USER_WIDTH[i_iwds] + 1;
      localparam int unsigned TableSize    = 2**IdWidthDs;
      synth_axi_iw_converter # (
        .SlvPortIdWidth      ( IdWidthUs    ),
        .MstPortIdWidth      ( IdWidthDs    ),
        .SlvPortMaxUniqIds   ( 2**IdWidthUs ),
        .SlvPortMaxTxnsPerId ( 13           ),
        .SlvPortMaxTxns      ( 81           ),
        .MstPortMaxUniqIds   ( 2**IdWidthDs ),
        .MstPortMaxTxnsPerId ( 11           ),
        .AddrWidth           ( 32'd64       ),
        .DataWidth           ( 32'd512      ),
        .UserWidth           ( 32'd10       )
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
          .DataWidth  ( DATA_WIDTH_AXI[i]   ),
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
  } apb_rsp_t;

  `AXI_LITE_TYPEDEF_AW_CHAN_T(aw_chan_t, addr_t)
  `AXI_LITE_TYPEDEF_W_CHAN_T(w_chan_t, data_t, strb_t)
  `AXI_LITE_TYPEDEF_B_CHAN_T(b_chan_t)
  `AXI_LITE_TYPEDEF_AR_CHAN_T(ar_chan_t, addr_t)
  `AXI_LITE_TYPEDEF_R_CHAN_T(r_chan_t, data_t)
  `AXI_LITE_TYPEDEF_REQ_T(axi_req_t, aw_chan_t, w_chan_t, ar_chan_t)
  `AXI_LITE_TYPEDEF_RSP_T(axi_rsp_t, b_chan_t, r_chan_t)

  axi_req_t                   axi_req;
  axi_rsp_t                   axi_rsp;
  apb_req_t [NoApbSlaves-1:0] apb_req;
  apb_rsp_t [NoApbSlaves-1:0] apb_rsp;

  axi_pkg::xbar_rule_32_t [NoApbSlaves-1:0] addr_map;

  axi_lite_to_apb #(
    .NoApbSlaves    ( NoApbSlaves             ),
    .NoRules        ( NoApbSlaves             ),
    .AddrWidth      ( 32'd32                  ),
    .DataWidth      ( DataWidth               ),
    .axi_lite_req_t ( axi_req_t               ),
    .axi_lite_rsp_t ( axi_rsp_t               ),
    .apb_req_t      ( apb_req_t               ),
    .apb_rsp_t      ( apb_rsp_t               ),
    .rule_t         ( axi_pkg::xbar_rule_32_t )
  ) i_axi_lite_to_apb_dut (
    .clk_i          ( clk_i    ),
    .rst_ni         ( rst_ni   ),
    .axi_lite_req_i ( axi_req  ),
    .axi_lite_rsp_o ( axi_rsp  ),
    .apb_req_o      ( apb_req  ),
    .apb_rsp_i      ( apb_rsp  ),
    .addr_map_i     ( addr_map )
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
  `AXI_LITE_TYPEDEF_REQ_T(axi_lite_req_t, aw_chan_t, w_chan_t, ar_chan_t)
  `AXI_LITE_TYPEDEF_RSP_T(axi_lite_rsp_t, b_chan_t, r_chan_t)
  localparam axi_pkg::xbar_cfg_t XbarCfg = '{
    NoSlvPorts:         NoSlvMst,
    NoMstPorts:         NoSlvMst,
    MaxMstTrans:        32'd5,
    MaxSlvTrans:        32'd5,
    FallThrough:        1'b1,
    LatencyMode:        axi_pkg::CUT_ALL_PORTS,
    AddrWidth:          32'd32,
    DataWidth:          32'd32,
    NoAddrRules:        NoSlvMst,
    default:            '0
  };

  axi_pkg::xbar_rule_32_t [NoSlvMst-1:0] addr_map;
  logic                                  test;
  axi_lite_req_t          [NoSlvMst-1:0] mst_reqs, slv_reqs;
  axi_lite_rsp_t          [NoSlvMst-1:0] mst_rsps, slv_rsps;

  axi_lite_xbar #(
    .Cfg             ( XbarCfg                 ),
    .aw_chan_t       (      aw_chan_t          ),
    .w_chan_t        (       w_chan_t          ),
    .b_chan_t        (       b_chan_t          ),
    .ar_chan_t       (      ar_chan_t          ),
    .r_chan_t        (       r_chan_t          ),
    .axi_lite_req_t  ( axi_lite_req_t          ),
    .axi_lite_rsp_t  ( axi_lite_rsp_t          ),
    .rule_t          ( axi_pkg::xbar_rule_32_t )
  ) i_xbar_dut (
    .clk_i                 ( clk_i    ),
    .rst_ni                ( rst_ni   ),
    .test_i                ( test     ),
    .slv_ports_req_i       ( mst_reqs ),
    .slv_ports_rsp_o       ( mst_rsps ),
    .mst_ports_req_o       ( slv_reqs ),
    .mst_ports_rsp_i       ( slv_rsps ),
    .addr_map_i            ( addr_map ),
    .en_default_mst_port_i ( '0       ),
    .default_mst_port_i    ( '0       )
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
  parameter int unsigned NumPending = 32'd16, // number of pending requests
  parameter int unsigned IdWidth    = 32'd0,  // AXI ID width
  parameter int unsigned AddrWidth  = 32'd0,  // AXI address width
  parameter int unsigned DataWidth  = 32'd0,  // AXI data width
  parameter int unsigned UserWidth  = 32'd0   // AXI user width
) (
  input clk_i,
  input rst_ni
);

  AXI_BUS #(
    .AXI_ADDR_WIDTH ( IdWidth   ),
    .AXI_DATA_WIDTH ( AddrWidth ),
    .AXI_ID_WIDTH   ( DataWidth ),
    .AXI_USER_WIDTH ( UserWidth )
  ) axi[1:0] ();

  logic isolate, isolated;

  axi_isolate_intf #(
    .NUM_PENDING    ( NumPending ), // number of pending requests
    .AXI_ID_WIDTH   ( IdWidth    ), // AXI ID width
    .AXI_ADDR_WIDTH ( AddrWidth  ), // AXI address width
    .AXI_DATA_WIDTH ( DataWidth  ), // AXI data width
    .AXI_USER_WIDTH ( UserWidth  )  // AXI user width
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
  parameter int unsigned NumPending = 32'd16, // number of pending requests
  parameter int unsigned IdWidth    = 32'd0,  // AXI ID width
  parameter int unsigned AddrWidth  = 32'd0,  // AXI address width
  parameter int unsigned DataWidth  = 32'd0,  // AXI data width
  parameter int unsigned UserWidth  = 32'd0   // AXI user width
) (
  input clk_i,
  input rst_ni
);

  AXI_BUS #(
    .AXI_ADDR_WIDTH ( IdWidth   ),
    .AXI_DATA_WIDTH ( AddrWidth ),
    .AXI_ID_WIDTH   ( DataWidth ),
    .AXI_USER_WIDTH ( UserWidth )
  ) axi[1:0] ();

  axi_serializer_intf #(
    .MAX_READ_TXNS  ( NumPending   ), // Number of pending requests
    .MAX_WRITE_TXNS ( NumPending   ), // Number of pending requests
    .AXI_ID_WIDTH   ( IdWidth   ), // AXI ID width
    .AXI_ADDR_WIDTH ( AddrWidth ), // AXI address width
    .AXI_DATA_WIDTH ( DataWidth ), // AXI data width
    .AXI_USER_WIDTH ( UserWidth )  // AXI user width
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
  parameter int unsigned SlvPortIdWidth = 32'd0,
  parameter int unsigned MstPortIdWidth = 32'd0,
  parameter int unsigned SlvPortMaxUniqIds = 32'd0,
  parameter int unsigned SlvPortMaxTxnsPerId = 32'd0,
  parameter int unsigned SlvPortMaxTxns = 32'd0,
  parameter int unsigned MstPortMaxUniqIds = 32'd0,
  parameter int unsigned MstPortMaxTxnsPerId = 32'd0,
  parameter int unsigned AddrWidth = 32'd0,
  parameter int unsigned DataWidth = 32'd0,
  parameter int unsigned UserWidth = 32'd0
) (
  input logic clk_i,
  input logic rst_ni
);
  AXI_BUS #(
    .AXI_ADDR_WIDTH ( AddrWidth      ),
    .AXI_DATA_WIDTH ( DataWidth      ),
    .AXI_ID_WIDTH   ( SlvPortIdWidth ),
    .AXI_USER_WIDTH ( UserWidth      )
  ) upstream ();
  AXI_BUS #(
    .AXI_ADDR_WIDTH ( AddrWidth      ),
    .AXI_DATA_WIDTH ( DataWidth      ),
    .AXI_ID_WIDTH   ( MstPortIdWidth ),
    .AXI_USER_WIDTH ( UserWidth      )
  ) downstream ();

  axi_iw_converter_intf #(
    .AXI_SLV_PORT_ID_WIDTH        (SlvPortIdWidth      ),
    .AXI_MST_PORT_ID_WIDTH        (MstPortIdWidth      ),
    .AXI_SLV_PORT_MAX_UNIQ_IDS    (MstPortIdWidth      ),
    .AXI_SLV_PORT_MAX_TXNS_PER_ID (SlvPortMaxTxnsPerId ),
    .AXI_SLV_PORT_MAX_TXNS        (SlvPortMaxTxns      ),
    .AXI_MST_PORT_MAX_UNIQ_IDS    (MstPortMaxUniqIds   ),
    .AXI_MST_PORT_MAX_TXNS_PER_ID (MstPortMaxTxnsPerId ),
    .AXI_ADDR_WIDTH               (AddrWidth           ),
    .AXI_DATA_WIDTH               (DataWidth           ),
    .AXI_USER_WIDTH               (UserWidth           )
  ) i_axi_iw_converter_dut (
    .clk_i,
    .rst_ni,
    .slv     ( upstream   ),
    .mst     ( downstream )
  );
endmodule

module synth_axi_to_mem_banked #(
  parameter int unsigned DataWidth  = 32'd0,
  parameter int unsigned BankNum       = 32'd0,
  parameter int unsigned BankAddrWidth = 32'd0
) (
  input logic clk_i,
  input logic rst_ni
);
  localparam int unsigned IdWidth    = 32'd10;
  localparam int unsigned AddrWidth  = 32'd64;
  localparam int unsigned StrbWidth  = DataWidth / 32'd8;
  localparam int unsigned UserWidth  = 32'd8;
  localparam int unsigned BankDataWidth = 32'd2 * DataWidth / BankNum;
  localparam int unsigned BankStrbWidth = BankDataWidth / 32'd8;
  localparam int unsigned BankLatency   = 32'd1;

  typedef logic [BankAddrWidth-1:0] mem_addr_t;
  typedef logic [BankDataWidth-1:0] mem_data_t;
  typedef logic [BankStrbWidth-1:0] mem_strb_t;

  AXI_BUS #(
    .AXI_ADDR_WIDTH ( IdWidth   ),
    .AXI_DATA_WIDTH ( AddrWidth ),
    .AXI_ID_WIDTH   ( DataWidth ),
    .AXI_USER_WIDTH ( UserWidth )
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
    .AXI_ID_WIDTH    ( IdWidth       ),
    .AXI_ADDR_WIDTH  ( AddrWidth     ),
    .AXI_DATA_WIDTH  ( DataWidth     ),
    .AXI_USER_WIDTH  ( UserWidth     ),
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
