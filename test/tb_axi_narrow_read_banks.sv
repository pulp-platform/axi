// Copyright 2026 CheshireAra contributors.
// SPDX-License-Identifier: Apache-2.0
// Real AXI path, with direct-memory or register-interface protocol peers.
`timescale 1ns/1ps
`include "axi/typedef.svh"
module tb_axi_narrow_read_banks;
  typedef logic[31:0] addr_t;
  typedef logic[63:0] data_t;
  typedef logic[7:0] strb_t;
  typedef logic[2:0] id_t;
  typedef logic user_t;
  `AXI_TYPEDEF_ALL_CT(test_axi,axi_req_t,axi_rsp_t,addr_t,id_t,data_t,strb_t,user_t)
  typedef struct packed {logic valid,write;addr_t addr;logic[31:0] wdata;logic[3:0] wstrb;} reg_req_t;
  typedef struct packed {logic ready,error;logic[31:0] rdata;} reg_rsp_t;
  bit clk=0,rst_n=0;
  always #5ns clk=~clk;
  axi_req_t req='0;axi_rsp_t rsp;
  reg_req_t reg_req;reg_rsp_t reg_rsp;
  int cases=0,checks=0,errors=0,observed[128],expected[128];
  int bank_count[2],bank_want=0;
  logic[3:0] bank_mask[2][16];
  addr_t bank_addr[2][16];
  bit checking=0;
  int cycles=0;
  logic [1:0] bank_valid,bank_ready,bank_we,bank_response;
  logic [1:0][3:0] bank_strobes;
  logic [1:0][31:0] bank_addresses,bank_data;
  `ifdef DIRECT_MEMORY
  assign bank_ready='1;
  always @(posedge clk)begin
    bank_response<=rst_n?bank_valid:'0;
    for(int b=0;b<2;b++)bank_data[b]<=reg_value(bank_addresses[b]);
  end
  axi_to_detailed_mem #(.AddrWidth(32),.DataWidth(64),.IdWidth(3),.UserWidth(1),
  .NumBanks(2),.BufDepth(1),.axi_req_t(axi_req_t),.axi_resp_t(axi_rsp_t)) bridge (
  .clk_i(clk),.rst_ni(rst_n),.busy_o(),.axi_req_i(req),.axi_resp_o(rsp),
  .mem_req_o(bank_valid),.mem_gnt_i(bank_ready),.mem_addr_o(bank_addresses),
  .mem_wdata_o(),.mem_strb_o(bank_strobes),.mem_atop_o(),.mem_lock_o(),.mem_we_o(bank_we),
  .mem_id_o(),.mem_user_o(),.mem_cache_o(),.mem_prot_o(),.mem_qos_o(),.mem_region_o(),
  .mem_rvalid_i(bank_response),.mem_rdata_i(bank_data),.mem_err_i('0),.mem_exokay_i('0));
  `else
  axi_to_reg_v2 #(.AxiAddrWidth(32),.AxiDataWidth(64),.AxiIdWidth(3),.AxiUserWidth(1),
  .RegDataWidth(32),.CutMemReqs(1'b1),.CutMemRsps(1'b1),
  .axi_req_t(axi_req_t),.axi_rsp_t(axi_rsp_t),.reg_req_t(reg_req_t),.reg_rsp_t(reg_rsp_t))
  bridge(.clk_i(clk),.rst_ni(rst_n),.axi_req_i(req),.axi_rsp_o(rsp),
  .reg_req_o(reg_req),.reg_rsp_i(reg_rsp),.reg_id_o(),.busy_o());

  assign bank_valid=bridge.mem_qvalid;assign bank_ready=bridge.mem_qready;
  assign bank_strobes=bridge.mem_strb;assign bank_addresses=bridge.mem_addr;
  `endif
  function automatic logic[31:0] reg_value(input addr_t a);
    return {8'(a+3),8'(a+2),8'(a+1),8'(a)};
  endfunction
  assign reg_rsp='{ready:1'b1,error:1'b0,rdata:reg_value(reg_req.addr)};
  task automatic check(input bit good,input string label,input logic[63:0] got,want);
    checks++;if(!good)begin errors++;if(errors<30)$display("NARROW_ERROR case=%0d %s got=%h want=%h",cases,label,got,want);end
  endtask
  always @(posedge clk)if(rst_n)begin
    cycles++;
    if(req.ar_valid&&rsp.ar_ready)$display("NARROW_AR case=%0d addr=%h len=%0d size=%0d",cases,req.ar.addr,req.ar.len,req.ar.size);
    if(req.r_ready&&rsp.r_valid)$display("NARROW_R case=%0d last=%b",cases,rsp.r.last);
    `ifndef DIRECT_MEMORY
    if(reg_req.valid && reg_rsp.ready)begin
      check(checking,"no unsolicited MMIO",checking,1);
      observed[(reg_req.addr>>2)&127]++;
      if(reg_req.write)begin
        check(reg_req.wdata===(reg_req.addr[2]?32'h12345678:32'h9abcdef0),"write payload",reg_req.wdata,reg_req.addr[2]?32'h12345678:32'h9abcdef0);
        check(reg_req.wstrb===bank_mask[reg_req.addr[2]][0],"write byte enables",reg_req.wstrb,bank_mask[reg_req.addr[2]][0]);
      end
    end
    `endif
    if(checking)for(int b=0;b<2;b++)if(bank_valid[b] && bank_ready[b])begin
      int n; n=bank_count[b];bank_count[b]++;
      check(n<bank_want,"bank beat count",n,bank_want);
      if(n<bank_want)begin
        check(bank_strobes[b]===bank_mask[b][n],"beat byte mask",bank_strobes[b],bank_mask[b][n]);
        check(bank_addresses[b]===bank_addr[b][n],"bank address",bank_addresses[b],bank_addr[b][n]);
      end
    end
  end
  task automatic start_case;
    @(negedge clk);cases++;checking=1;$display("NARROW_BEGIN case=%0d",cases);
    for(int i=0;i<128;i++)begin observed[i]=0;expected[i]=0;end
    bank_count[0]=0;bank_count[1]=0;
  endtask
  task automatic finish_case;
    repeat(5)@(negedge clk);
    `ifndef DIRECT_MEMORY
    for(int i=0;i<128;i++)check(observed[i]==expected[i],"MMIO side-effect count",observed[i],expected[i]);
    `endif
    for(int b=0;b<2;b++)check(bank_count[b]==bank_want,"complete bank beats",bank_count[b],bank_want);
    checking=0;$display("NARROW_END case=%0d",cases);
  endtask
  task automatic read_case(input int address,size,beats);
    int a,aligned,upper,word_base;logic[7:0] mask;
    start_case();bank_want=beats;
    aligned=(address/(1<<size))*(1<<size);
    for(int beat=0;beat<beats;beat++)begin
      a=beat==0?address:aligned+beat*(1<<size);
      upper=(a/(1<<size))*(1<<size)+(1<<size)-1;
      word_base=(a/8)*8;mask=0;
      // Independent address interval: no DUT strobe or axi_pkg helper is used.
      for(int byte_addr=a;byte_addr<=upper;byte_addr++)mask[byte_addr-word_base]=1;
      for(int b=0;b<2;b++)begin
        bank_mask[b][beat]=mask[b*4+:4];bank_addr[b][beat]=word_base+b*4;
        if(mask[b*4+:4]!=0)expected[((word_base+b*4)>>2)&127]++;
      end
    end
    req.ar='{id:3'h5,addr:32'(address),len:8'(beats-1),size:3'(size),burst:axi_pkg::BURST_INCR,default:'0};
    req.ar_valid=1;req.w.strb=8'ha5;
    do @(posedge clk);while(!rsp.ar_ready);
    @(negedge clk);req.ar_valid=0;
    for(int beat=0;beat<beats;beat++)begin
      // Keep R under backpressure long enough to exercise response storage.
      req.r_ready=0;repeat(3)@(negedge clk);
      req.r_ready=1;do @(posedge clk);while(!rsp.r_valid);
      check(rsp.r.id===3'h5,"read ID",rsp.r.id,5);
      check(rsp.r.resp===axi_pkg::RESP_OKAY,"read response",rsp.r.resp,0);
      check(rsp.r.last===(beat==beats-1),"read LAST",rsp.r.last,beat==beats-1);
      for(int b=0;b<2;b++)for(int k=0;k<4;k++)if(bank_mask[b][beat][k])
        check(rsp.r.data[(b*4+k)*8+:8]===8'(bank_addr[b][beat]+k),"active read byte",rsp.r.data[(b*4+k)*8+:8],8'(bank_addr[b][beat]+k));
      @(negedge clk);req.r_ready=0;
    end
    finish_case();
  endtask
  task automatic write_case(input logic[7:0] strobes);
    start_case();bank_want=1;
    for(int b=0;b<2;b++)begin bank_mask[b][0]=strobes[b*4+:4];bank_addr[b][0]=32'h100+b*4;if(strobes[b*4+:4]!=0)expected[(32'h100+b*4)>>2]++;end
    req.aw='{id:3'h6,addr:32'h100,size:3'd3,burst:axi_pkg::BURST_INCR,default:'0};req.aw_valid=1;
    req.w='{data:64'h123456789abcdef0,strb:strobes,last:1'b1,default:'0};req.w_valid=1;
    fork
      begin do @(posedge clk);while(!rsp.aw_ready);@(negedge clk);req.aw_valid=0;end
      begin do @(posedge clk);while(!rsp.w_ready);@(negedge clk);req.w_valid=0;end
    join
    req.b_ready=1;
    do @(posedge clk);while(!rsp.b_valid);
    check(rsp.b.id===3'h6,"write ID",rsp.b.id,6);check(rsp.b.resp===0,"write response",rsp.b.resp,0);
    @(negedge clk);req.b_ready=0;finish_case();
  endtask
  initial begin
    repeat(5)@(negedge clk);rst_n=1;
    for(int size=0;size<4;size++)for(int offset=0;offset<8;offset++)begin
      read_case('h100+offset,size,1);read_case('h100+offset,size,2);read_case('h100+offset,size,4);
    end
    for(int strb=0;strb<256;strb++)write_case(8'(strb));
    repeat(10)@(negedge clk);
    $display("NARROW_DONE cases=%0d checks=%0d errors=%0d",cases,checks,errors);$finish;
  end
  initial begin #2ms;$fatal(1,"NARROW_HDL_LIMIT case=%0d req=%h rsp=%h bank_counts=%0d/%0d",cases,req,rsp,bank_count[0],bank_count[1]);end
endmodule
