`timescale 1ns/1ps

module tb_axi4_burst_split;
  localparam int unsigned AddrWidth    = 32;
  localparam int unsigned DataWidth    = 32;
  localparam int unsigned IdWidth      = 2;
  localparam int unsigned UserWidth    = 1;
  localparam int unsigned CfgAddrWidth = 8;
  localparam int unsigned CfgDataWidth = 32;

  logic clk;
  logic rst_n;

  always #5ns clk = ~clk;

  // AXI-Lite config IF
  logic [CfgAddrWidth-1:0]  cfg_aw_addr;
  logic [2:0]               cfg_aw_prot;
  logic                     cfg_aw_valid;
  logic                     cfg_aw_ready;
  logic [CfgDataWidth-1:0]  cfg_w_data;
  logic [CfgDataWidth/8-1:0] cfg_w_strb;
  logic                     cfg_w_valid;
  logic                     cfg_w_ready;
  logic [1:0]               cfg_b_resp;
  logic                     cfg_b_valid;
  logic                     cfg_b_ready;
  logic [CfgAddrWidth-1:0]  cfg_ar_addr;
  logic [2:0]               cfg_ar_prot;
  logic                     cfg_ar_valid;
  logic                     cfg_ar_ready;
  logic [CfgDataWidth-1:0]  cfg_r_data;
  logic [1:0]               cfg_r_resp;
  logic                     cfg_r_valid;
  logic                     cfg_r_ready;

  // AXI slave-side stimuli
  logic [IdWidth-1:0]       slv_aw_id;
  logic [AddrWidth-1:0]     slv_aw_addr;
  logic [7:0]               slv_aw_len;
  logic [2:0]               slv_aw_size;
  logic [1:0]               slv_aw_burst;
  logic                     slv_aw_lock;
  logic [3:0]               slv_aw_cache;
  logic [2:0]               slv_aw_prot;
  logic [3:0]               slv_aw_qos;
  logic [3:0]               slv_aw_region;
  logic [UserWidth-1:0]     slv_aw_user;
  logic                     slv_aw_valid;
  logic                     slv_aw_ready;
  logic [DataWidth-1:0]     slv_w_data;
  logic [DataWidth/8-1:0]   slv_w_strb;
  logic                     slv_w_last;
  logic [UserWidth-1:0]     slv_w_user;
  logic                     slv_w_valid;
  logic                     slv_w_ready;
  logic [IdWidth-1:0]       slv_b_id;
  logic [1:0]               slv_b_resp;
  logic [UserWidth-1:0]     slv_b_user;
  logic                     slv_b_valid;
  logic                     slv_b_ready;

  // AXI read side tied-off
  logic [IdWidth-1:0]       slv_ar_id;
  logic [AddrWidth-1:0]     slv_ar_addr;
  logic [7:0]               slv_ar_len;
  logic [2:0]               slv_ar_size;
  logic [1:0]               slv_ar_burst;
  logic                     slv_ar_lock;
  logic [3:0]               slv_ar_cache;
  logic [2:0]               slv_ar_prot;
  logic [3:0]               slv_ar_qos;
  logic [3:0]               slv_ar_region;
  logic [UserWidth-1:0]     slv_ar_user;
  logic                     slv_ar_valid;
  logic                     slv_ar_ready;
  logic [IdWidth-1:0]       slv_r_id;
  logic [DataWidth-1:0]     slv_r_data;
  logic [1:0]               slv_r_resp;
  logic                     slv_r_last;
  logic [UserWidth-1:0]     slv_r_user;
  logic                     slv_r_valid;
  logic                     slv_r_ready;

  // AXI master-side observe/response
  logic [IdWidth-1:0]       mst_aw_id;
  logic [AddrWidth-1:0]     mst_aw_addr;
  logic [7:0]               mst_aw_len;
  logic [2:0]               mst_aw_size;
  logic [1:0]               mst_aw_burst;
  logic                     mst_aw_lock;
  logic [3:0]               mst_aw_cache;
  logic [2:0]               mst_aw_prot;
  logic [3:0]               mst_aw_qos;
  logic [3:0]               mst_aw_region;
  logic [UserWidth-1:0]     mst_aw_user;
  logic                     mst_aw_valid;
  logic                     mst_aw_ready;
  logic [DataWidth-1:0]     mst_w_data;
  logic [DataWidth/8-1:0]   mst_w_strb;
  logic                     mst_w_last;
  logic [UserWidth-1:0]     mst_w_user;
  logic                     mst_w_valid;
  logic                     mst_w_ready;
  logic [IdWidth-1:0]       mst_b_id;
  logic [1:0]               mst_b_resp;
  logic [UserWidth-1:0]     mst_b_user;
  logic                     mst_b_valid;
  logic                     mst_b_ready;

  logic [IdWidth-1:0]       mst_ar_id;
  logic [AddrWidth-1:0]     mst_ar_addr;
  logic [7:0]               mst_ar_len;
  logic [2:0]               mst_ar_size;
  logic [1:0]               mst_ar_burst;
  logic                     mst_ar_lock;
  logic [3:0]               mst_ar_cache;
  logic [2:0]               mst_ar_prot;
  logic [3:0]               mst_ar_qos;
  logic [3:0]               mst_ar_region;
  logic [UserWidth-1:0]     mst_ar_user;
  logic                     mst_ar_valid;
  logic                     mst_ar_ready;
  logic [IdWidth-1:0]       mst_r_id;
  logic [DataWidth-1:0]     mst_r_data;
  logic [1:0]               mst_r_resp;
  logic                     mst_r_last;
  logic [UserWidth-1:0]     mst_r_user;
  logic                     mst_r_valid;
  logic                     mst_r_ready;

  axi4_burst_split #(
    .MaxReadTxns  ( 2 ),
    .MaxWriteTxns ( 2 ),
    .AddrWidth    ( AddrWidth ),
    .DataWidth    ( DataWidth ),
    .IdWidth      ( IdWidth ),
    .UserWidth    ( UserWidth ),
    .CfgAddrWidth ( CfgAddrWidth ),
    .CfgDataWidth ( CfgDataWidth ),
    .LenLimitResetVal ( 8'd3 )
  ) dut (
    .clk_i(clk), .rst_ni(rst_n), .test_i(1'b0),
    .cfg_aw_addr_i(cfg_aw_addr), .cfg_aw_prot_i(cfg_aw_prot), .cfg_aw_valid_i(cfg_aw_valid), .cfg_aw_ready_o(cfg_aw_ready),
    .cfg_w_data_i(cfg_w_data), .cfg_w_strb_i(cfg_w_strb), .cfg_w_valid_i(cfg_w_valid), .cfg_w_ready_o(cfg_w_ready),
    .cfg_b_resp_o(cfg_b_resp), .cfg_b_valid_o(cfg_b_valid), .cfg_b_ready_i(cfg_b_ready),
    .cfg_ar_addr_i(cfg_ar_addr), .cfg_ar_prot_i(cfg_ar_prot), .cfg_ar_valid_i(cfg_ar_valid), .cfg_ar_ready_o(cfg_ar_ready),
    .cfg_r_data_o(cfg_r_data), .cfg_r_resp_o(cfg_r_resp), .cfg_r_valid_o(cfg_r_valid), .cfg_r_ready_i(cfg_r_ready),
    .slv_aw_id_i(slv_aw_id), .slv_aw_addr_i(slv_aw_addr), .slv_aw_len_i(slv_aw_len), .slv_aw_size_i(slv_aw_size), .slv_aw_burst_i(slv_aw_burst), .slv_aw_lock_i(slv_aw_lock),
    .slv_aw_cache_i(slv_aw_cache), .slv_aw_prot_i(slv_aw_prot), .slv_aw_qos_i(slv_aw_qos), .slv_aw_region_i(slv_aw_region), .slv_aw_user_i(slv_aw_user),
    .slv_aw_valid_i(slv_aw_valid), .slv_aw_ready_o(slv_aw_ready), .slv_w_data_i(slv_w_data), .slv_w_strb_i(slv_w_strb), .slv_w_last_i(slv_w_last), .slv_w_user_i(slv_w_user),
    .slv_w_valid_i(slv_w_valid), .slv_w_ready_o(slv_w_ready), .slv_b_id_o(slv_b_id), .slv_b_resp_o(slv_b_resp), .slv_b_user_o(slv_b_user), .slv_b_valid_o(slv_b_valid), .slv_b_ready_i(slv_b_ready),
    .slv_ar_id_i(slv_ar_id), .slv_ar_addr_i(slv_ar_addr), .slv_ar_len_i(slv_ar_len), .slv_ar_size_i(slv_ar_size), .slv_ar_burst_i(slv_ar_burst), .slv_ar_lock_i(slv_ar_lock),
    .slv_ar_cache_i(slv_ar_cache), .slv_ar_prot_i(slv_ar_prot), .slv_ar_qos_i(slv_ar_qos), .slv_ar_region_i(slv_ar_region), .slv_ar_user_i(slv_ar_user), .slv_ar_valid_i(slv_ar_valid),
    .slv_ar_ready_o(slv_ar_ready), .slv_r_id_o(slv_r_id), .slv_r_data_o(slv_r_data), .slv_r_resp_o(slv_r_resp), .slv_r_last_o(slv_r_last), .slv_r_user_o(slv_r_user), .slv_r_valid_o(slv_r_valid), .slv_r_ready_i(slv_r_ready),
    .mst_aw_id_o(mst_aw_id), .mst_aw_addr_o(mst_aw_addr), .mst_aw_len_o(mst_aw_len), .mst_aw_size_o(mst_aw_size), .mst_aw_burst_o(mst_aw_burst), .mst_aw_lock_o(mst_aw_lock),
    .mst_aw_cache_o(mst_aw_cache), .mst_aw_prot_o(mst_aw_prot), .mst_aw_qos_o(mst_aw_qos), .mst_aw_region_o(mst_aw_region), .mst_aw_user_o(mst_aw_user), .mst_aw_valid_o(mst_aw_valid), .mst_aw_ready_i(mst_aw_ready),
    .mst_w_data_o(mst_w_data), .mst_w_strb_o(mst_w_strb), .mst_w_last_o(mst_w_last), .mst_w_user_o(mst_w_user), .mst_w_valid_o(mst_w_valid), .mst_w_ready_i(mst_w_ready),
    .mst_b_id_i(mst_b_id), .mst_b_resp_i(mst_b_resp), .mst_b_user_i(mst_b_user), .mst_b_valid_i(mst_b_valid), .mst_b_ready_o(mst_b_ready),
    .mst_ar_id_o(mst_ar_id), .mst_ar_addr_o(mst_ar_addr), .mst_ar_len_o(mst_ar_len), .mst_ar_size_o(mst_ar_size), .mst_ar_burst_o(mst_ar_burst), .mst_ar_lock_o(mst_ar_lock),
    .mst_ar_cache_o(mst_ar_cache), .mst_ar_prot_o(mst_ar_prot), .mst_ar_qos_o(mst_ar_qos), .mst_ar_region_o(mst_ar_region), .mst_ar_user_o(mst_ar_user), .mst_ar_valid_o(mst_ar_valid), .mst_ar_ready_i(mst_ar_ready),
    .mst_r_id_i(mst_r_id), .mst_r_data_i(mst_r_data), .mst_r_resp_i(mst_r_resp), .mst_r_last_i(mst_r_last), .mst_r_user_i(mst_r_user), .mst_r_valid_i(mst_r_valid), .mst_r_ready_o(mst_r_ready)
  );

  int aw_seen;
  int wlast_seen;
  int beat_in_chunk;
  int pending_b;

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      aw_seen <= 0; wlast_seen <= 0; beat_in_chunk <= 0; pending_b <= 0;
      mst_b_valid <= 0;
    end else begin
      if (mst_aw_valid && mst_aw_ready) begin
        aw_seen <= aw_seen + 1;
        assert (mst_aw_len == 8'd1) else $fatal(1, "Expected split AWLEN=1, got %0d", mst_aw_len);
        pending_b <= pending_b + 1;
      end
      if (mst_w_valid && mst_w_ready) begin
        beat_in_chunk <= beat_in_chunk + 1;
        if (mst_w_last) begin
          wlast_seen <= wlast_seen + 1;
          assert (beat_in_chunk == 1) else $fatal(1, "Expected WLAST every 2 beats");
          beat_in_chunk <= 0;
        end
      end
      mst_b_valid <= 1'b0;
      if ((pending_b > 0) && mst_b_ready) begin
        mst_b_valid <= 1'b1;
        pending_b <= pending_b - 1;
      end
    end
  end

  task automatic axil_write(input logic [CfgAddrWidth-1:0] addr, input logic [CfgDataWidth-1:0] data);
    begin
      cfg_aw_addr = addr; cfg_aw_prot = '0; cfg_aw_valid = 1'b1;
      cfg_w_data = data; cfg_w_strb = '1; cfg_w_valid = 1'b1;
      do @(posedge clk); while (!(cfg_aw_ready && cfg_w_ready));
      cfg_aw_valid = 1'b0; cfg_w_valid = 1'b0;
      cfg_b_ready = 1'b1;
      do @(posedge clk); while (!cfg_b_valid);
      cfg_b_ready = 1'b0;
    end
  endtask

  task automatic send_write_burst;
    begin
      slv_aw_id = '0; slv_aw_addr = 32'h1000; slv_aw_len = 8'd3; slv_aw_size = 3'd2;
      slv_aw_burst = 2'b01; slv_aw_lock = 1'b0; slv_aw_cache = 4'hF; slv_aw_prot = '0;
      slv_aw_qos = '0; slv_aw_region = '0; slv_aw_user = '0; slv_aw_valid = 1'b1;
      do @(posedge clk); while (!slv_aw_ready);
      slv_aw_valid = 1'b0;

      for (int i = 0; i < 4; i++) begin
        slv_w_data = i;
        slv_w_strb = '1;
        slv_w_user = '0;
        slv_w_last = (i == 3);
        slv_w_valid = 1'b1;
        do @(posedge clk); while (!slv_w_ready);
        slv_w_valid = 1'b0;
      end

      slv_b_ready = 1'b1;
      do @(posedge clk); while (!slv_b_valid);
      slv_b_ready = 1'b0;
    end
  endtask

  initial begin
    clk = 0; rst_n = 0;
    cfg_aw_addr='0; cfg_aw_prot='0; cfg_aw_valid=0; cfg_w_data='0; cfg_w_strb='0; cfg_w_valid=0; cfg_b_ready=0;
    cfg_ar_addr='0; cfg_ar_prot='0; cfg_ar_valid=0; cfg_r_ready=0;
    slv_aw_valid=0; slv_w_valid=0; slv_b_ready=0; slv_ar_valid=0; slv_r_ready=0;
    slv_ar_id='0; slv_ar_addr='0; slv_ar_len='0; slv_ar_size='0; slv_ar_burst='0; slv_ar_lock='0;
    slv_ar_cache='0; slv_ar_prot='0; slv_ar_qos='0; slv_ar_region='0; slv_ar_user='0;
    mst_aw_ready=1; mst_w_ready=1; mst_b_id='0; mst_b_resp=2'b00; mst_b_user='0;
    mst_ar_ready=1; mst_r_id='0; mst_r_data='0; mst_r_resp='0; mst_r_last=1'b0; mst_r_user='0; mst_r_valid=1'b0;

    repeat (5) @(posedge clk);
    rst_n = 1;
    repeat (2) @(posedge clk);

    // len_limit = 1 => split into chunks of 2 beats.
    axil_write('0, 32'h0000_0001);
    send_write_burst();

    repeat (10) @(posedge clk);

    assert (aw_seen == 2) else $fatal(1, "Expected 2 AW transactions after split, got %0d", aw_seen);
    assert (wlast_seen == 2) else $fatal(1, "Expected 2 WLAST pulses after split, got %0d", wlast_seen);

    $display("TB PASS: aw_seen=%0d wlast_seen=%0d", aw_seen, wlast_seen);
    $finish;
  end

endmodule
