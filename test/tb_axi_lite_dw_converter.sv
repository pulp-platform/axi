// Copyright (c) 2020 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Authors:
// - Wolfgang Roenninger <wroennin@iis.ee.ethz.ch>
// - Michael Rogenmoser <michaero@iis.ee.ethz.ch>


`include "axi/typedef.svh"
`include "axi/assign.svh"
/// Testbench for the AXI4-Lite data width conversion module.
module tb_axi_lite_dw_converter #(
  /// Address width of the AXI4-Lite ports.
  parameter int unsigned TbAxiAddrWidth    = 32'd32,
  /// Data Width of the slave port.
  parameter int unsigned TbAxiDataWidthSlv = 32'd32,
  /// Data Width of the master port.
  parameter int unsigned TbAxiDataWidthMst = 32'd128,
  /// Number of write transactions.
  parameter int unsigned NumWrites         = 32'd10000,
  /// Number of read tranactions.
  parameter int unsigned NumReads          = 32'd10000
);
  // Random master no Transactions
  // timing parameters
  localparam time CyclTime = 10ns;
  localparam time ApplTime =  2ns;
  localparam time TestTime =  8ns;
  // AXI configuration
  localparam int unsigned TbAxiStrbWidthSlv =  TbAxiDataWidthSlv / 32'd8;
  localparam int unsigned TbAxiStrbWidthMst =  TbAxiDataWidthMst / 32'd8;
  // Type definitions
  typedef logic [TbAxiAddrWidth-1:0]    addr_t;
  typedef logic [TbAxiDataWidthSlv-1:0] data_slv_t;
  typedef logic [TbAxiStrbWidthSlv-1:0] strb_slv_t;
  typedef logic [TbAxiDataWidthMst-1:0] data_mst_t;
  typedef logic [TbAxiStrbWidthMst-1:0] strb_mst_t;


  `AXI_LITE_TYPEDEF_AW_CHAN_T(aw_chan_lite_t, addr_t)
  `AXI_LITE_TYPEDEF_W_CHAN_T(w_chan_lite_slv_t, data_slv_t, strb_slv_t)
  `AXI_LITE_TYPEDEF_W_CHAN_T(w_chan_lite_mst_t, data_mst_t, strb_mst_t)
  `AXI_LITE_TYPEDEF_B_CHAN_T(b_chan_lite_t)

  `AXI_LITE_TYPEDEF_AR_CHAN_T(ar_chan_lite_t, addr_t)
  `AXI_LITE_TYPEDEF_R_CHAN_T(r_chan_lite_slv_t, data_slv_t)
  `AXI_LITE_TYPEDEF_R_CHAN_T(r_chan_lite_mst_t, data_mst_t)


  `AXI_LITE_TYPEDEF_REQ_T(req_lite_slv_t, aw_chan_lite_t, w_chan_lite_slv_t, ar_chan_lite_t)
  `AXI_LITE_TYPEDEF_RESP_T(res_lite_slv_t, b_chan_lite_t, r_chan_lite_slv_t)

  `AXI_LITE_TYPEDEF_REQ_T(req_lite_mst_t, aw_chan_lite_t, w_chan_lite_mst_t, ar_chan_lite_t)
  `AXI_LITE_TYPEDEF_RESP_T(res_lite_mst_t, b_chan_lite_t, r_chan_lite_mst_t)


  typedef axi_test::axi_lite_rand_master #(
    // AXI interface parameters
    .AW ( TbAxiAddrWidth    ),
    .DW ( TbAxiDataWidthSlv ),
    // Stimuli application and test time
    .TA ( ApplTime          ),
    .TT ( TestTime          ),
    .MIN_ADDR (  0          ),
    .MAX_ADDR ( '1          ),
    .MAX_READ_TXNS  ( 100   ),
    .MAX_WRITE_TXNS ( 100   )
  ) rand_lite_master_t;
  typedef axi_test::axi_lite_rand_slave #(
    // AXI interface parameters
    .AW ( TbAxiAddrWidth    ),
    .DW ( TbAxiDataWidthMst ),
    // Stimuli application and test time
    .TA ( ApplTime          ),
    .TT ( TestTime          )
  ) rand_lite_slave_t;

  // -------------
  // DUT signals
  // -------------
  logic clk;
  // DUT signals
  logic rst_n;
  logic end_of_sim;

  // master structs
  req_lite_slv_t  master_req;
  res_lite_slv_t master_res;

  // slave structs
  req_lite_mst_t  slave_req;
  res_lite_mst_t slave_res;

  // -------------------------------
  // AXI Interfaces
  // -------------------------------
  AXI_LITE #(
    .AXI_ADDR_WIDTH ( TbAxiAddrWidth    ),
    .AXI_DATA_WIDTH ( TbAxiDataWidthSlv )
  ) master ();
  AXI_LITE_DV #(
    .AXI_ADDR_WIDTH ( TbAxiAddrWidth    ),
    .AXI_DATA_WIDTH ( TbAxiDataWidthSlv )
  ) master_dv (clk);
  `AXI_LITE_ASSIGN(master, master_dv)
  `AXI_LITE_ASSIGN_TO_REQ(master_req, master)
  `AXI_LITE_ASSIGN_TO_RESP(master_res, master)

  AXI_LITE #(
    .AXI_ADDR_WIDTH ( TbAxiAddrWidth    ),
    .AXI_DATA_WIDTH ( TbAxiDataWidthMst )
  ) slave ();
  AXI_LITE_DV #(
    .AXI_ADDR_WIDTH ( TbAxiAddrWidth    ),
    .AXI_DATA_WIDTH ( TbAxiDataWidthMst )
  ) slave_dv (clk);
  `AXI_LITE_ASSIGN(slave_dv, slave)
  `AXI_LITE_ASSIGN_TO_REQ(slave_req, slave)
  `AXI_LITE_ASSIGN_TO_RESP(slave_res, slave)
  // -------------------------------
  // AXI Rand Masters and Slaves
  // -------------------------------
  // Masters control simulation run time
  initial begin : proc_generate_traffic
    automatic rand_lite_master_t lite_axi_master = new ( master_dv, "MST_0");
    automatic data_slv_t      data = '0;
    automatic axi_pkg::resp_t resp = '0;
    end_of_sim <= 1'b0;
    lite_axi_master.reset();
    @(posedge rst_n);
    lite_axi_master.write(32'h0000_1100, axi_pkg::prot_t'('0), data_slv_t'(64'hDEADBEEFDEADBEEF),
        strb_slv_t'(8'hFF), resp);
    lite_axi_master.read(32'h0000_e100, axi_pkg::prot_t'('0), data, resp);
    lite_axi_master.run(NumReads, NumWrites);
    end_of_sim <= 1'b1;
  end

  initial begin : proc_recieve_traffic
    automatic rand_lite_slave_t lite_axi_slave = new( slave_dv , "SLV_0");
    lite_axi_slave.reset();
    @(posedge rst_n);
    lite_axi_slave.run();
  end

  // FIFOs for sampling the channels
  // Slave Port
  aw_chan_lite_t    fifo_slv_aw[$];
  w_chan_lite_slv_t fifo_slv_w[$];
  b_chan_lite_t     fifo_slv_b[$];
  ar_chan_lite_t    fifo_slv_ar[$];
  r_chan_lite_slv_t fifo_slv_r[$];

  aw_chan_lite_t    fifo_mst_aw[$];
  w_chan_lite_mst_t fifo_mst_w[$];
  b_chan_lite_t     fifo_mst_b[$];
  ar_chan_lite_t    fifo_mst_ar[$];
  r_chan_lite_mst_t fifo_mst_r[$];
  // Sampling processes
  initial begin : proc_sample
    forever begin
      @(posedge clk);
      #TestTime;
      if (rst_n) begin
        if (master_req.aw_valid && master_res.aw_ready) begin
          fifo_slv_aw.push_back(master_req.aw);
        end
        if (master_req.w_valid && master_res.w_ready) begin
          fifo_slv_w.push_back(master_req.w);
        end
        if (master_res.b_valid && master_req.b_ready) begin
          fifo_slv_b.push_back(master_res.b);
        end
        if (master_req.ar_valid && master_res.ar_ready) begin
          fifo_slv_ar.push_back(master_req.ar);
        end
        if (master_res.r_valid && master_req.r_ready) begin
          fifo_slv_r.push_back(master_res.r);
        end
        if (slave_req.aw_valid && slave_res.aw_ready) begin
          fifo_mst_aw.push_back(slave_req.aw);
        end
        if (slave_req.w_valid && slave_res.w_ready) begin
          fifo_mst_w.push_back(slave_req.w);
        end
        if (slave_res.b_valid && slave_req.b_ready) begin
          fifo_mst_b.push_back(slave_res.b);
        end
        if (slave_req.ar_valid && slave_res.ar_ready) begin
          fifo_mst_ar.push_back(slave_req.ar);
        end
        if (slave_res.r_valid && slave_req.r_ready) begin
          fifo_mst_r.push_back(slave_res.r);
        end
      end
    end
  end

  if (TbAxiDataWidthMst < TbAxiDataWidthSlv) begin : gen_down_gm
    localparam int unsigned DataDivFactor = TbAxiDataWidthSlv / TbAxiDataWidthMst;
    localparam int unsigned AddrShift     = $clog2(TbAxiDataWidthMst/8);
    localparam int unsigned SelWidth      = $clog2(DataDivFactor);
    typedef logic [SelWidth-1:0] sel_t;
    aw_chan_lite_t    fifo_exp_aw[$];
    w_chan_lite_mst_t fifo_exp_w[$];
    ar_chan_lite_t    fifo_exp_ar[$];

    // Golden model for down conversion
    initial begin : proc_write_exp_gen
      automatic aw_chan_lite_t    chan_aw, exp_aw;
      automatic w_chan_lite_slv_t chan_w;
      automatic w_chan_lite_mst_t exp_w;
      automatic int unsigned      num_vectors; // Number of expected transactions generated
      automatic addr_t            exp_addr;
      automatic sel_t             w_sel;

      forever begin
        wait((fifo_slv_aw.size() > 0) && (fifo_slv_w.size() > 0));
        chan_aw  = fifo_slv_aw.pop_front();
        chan_w   = fifo_slv_w.pop_front();
        exp_addr = chan_aw.addr;
        exp_addr = exp_addr >> (AddrShift + SelWidth);
        for (int unsigned i = 0; i < DataDivFactor; i++) begin
          // Generate expected AW vector
          exp_aw = aw_chan_lite_t'{
            addr: ((exp_addr << SelWidth) + i) << AddrShift,
            prot: chan_aw.prot
          };
          fifo_exp_aw.push_back(exp_aw);
          // Generate expected W vector
          exp_w    = w_chan_lite_mst_t'{
            data: chan_w.data[i*TbAxiDataWidthMst+:TbAxiDataWidthMst],
            strb: chan_w.strb[i*TbAxiStrbWidthMst+:TbAxiStrbWidthMst]
          };
          fifo_exp_w.push_back(exp_w);
        end
      end
    end

    initial begin : proc_aw_exp_check
      automatic aw_chan_lite_t chan_aw, exp_aw;
      forever begin
        wait((fifo_exp_aw.size() > 0) && (fifo_mst_aw.size() > 0));
        chan_aw = fifo_mst_aw.pop_front();
        exp_aw  = fifo_exp_aw.pop_front();
        assert (chan_aw.addr == exp_aw.addr) else
            $error("Master port> AW.addr is not expected: EXP: %h ACT:%h",
                exp_aw.addr, chan_aw.addr);
        assert (chan_aw.prot == exp_aw.prot) else
            $error("Master port> AW.prot is not expected: EXP: %h ACT:%h",
                   exp_aw.prot, chan_aw.prot);
      end
    end
    initial begin : proc_w_exp_check
      automatic w_chan_lite_mst_t chan_w, exp_w;
      forever begin
        wait((fifo_exp_w.size() > 0) && (fifo_mst_w.size() > 0));
        chan_w = fifo_mst_w.pop_front();
        exp_w  = fifo_exp_w.pop_front();
        assert (chan_w.data == exp_w.data) else
            $error("Master port> W.data is not expected: EXP: %h ACT:%h",
                exp_w.data, chan_w.data);
        assert (chan_w.strb == exp_w.strb) else
            $error("Master port> W.strb is not expected: EXP: %h ACT:%h",
                   exp_w.strb, chan_w.strb);
      end
    end
    initial begin : proc_b_exp_check
      automatic b_chan_lite_t exp_b, act_b;
      forever begin
        // wait until there are this many B responses in the sampling FIFO
        wait(fifo_mst_b.size() >= DataDivFactor);
        exp_b = axi_pkg::RESP_OKAY;
        for (int unsigned i = 0; i < DataDivFactor; i++) begin
          act_b = fifo_mst_b.pop_front();
          exp_b = exp_b | act_b;
        end
        // Do the check
        wait(fifo_slv_b.size() > 0);
        act_b = fifo_slv_b.pop_front();
        assert(exp_b.resp == act_b.resp) else
            $error("Slave port> B.resp is not expected: EXP: %h ACT: %h", exp_b.resp, act_b.resp);
      end
    end
    initial begin : proc_ar_exp_check
      automatic ar_chan_lite_t chan_ar, exp_ar;
      forever begin
        wait((fifo_exp_ar.size() > 0) && (fifo_mst_ar.size() > 0));
        chan_ar = fifo_mst_ar.pop_front();
        exp_ar  = fifo_exp_ar.pop_front();
        assert (chan_ar.addr == exp_ar.addr) else
            $error("Master port> AR.addr is not expected: EXP: %h ACT:%h",
                exp_ar.addr, chan_ar.addr);
        assert (chan_ar.prot == exp_ar.prot) else
            $error("Master port> AR.prot is not expected: EXP: %h ACT:%h",
                   exp_ar.prot, chan_ar.prot);
      end
    end
    initial begin : proc_r_exp_check
      automatic r_chan_lite_slv_t exp_r, act_r;
      automatic r_chan_lite_mst_t mst_r;
      forever begin
        wait(fifo_slv_r.size() > 0);
        act_r = fifo_slv_r.pop_front();
        exp_r = r_chan_lite_slv_t'{default: '0};
        // Build the expected R response from the master port fifo.
        for (int unsigned i = 0; i < DataDivFactor; i++) begin
          mst_r = fifo_mst_r.pop_front();
          exp_r.data[i*TbAxiDataWidthMst+:TbAxiDataWidthMst] = mst_r.data;
          exp_r.resp = exp_r.resp | mst_r.resp;
        end
        assert (act_r.data == exp_r.data) else
            $error("Slave port> R.data is not expected: EXP: %h ACT:%h",
                exp_r.data, act_r.data);
        assert (act_r.resp == exp_r.resp) else
            $error("Slave port> R.resp is not expected: EXP: %h ACT:%h",
                   exp_r.resp, act_r.resp);
      end
    end
  end else if (TbAxiDataWidthMst == TbAxiDataWidthSlv) begin
    initial begin : proc_passthrough_check
      forever begin
        @(posedge clk);
        #TestTime;
        if (rst_n) begin
          assert (master_req == slave_req);
          assert (master_res == slave_res);
        end
      end
    end
  end else begin
    // Upsizer
    localparam int unsigned DataMultFactor = TbAxiDataWidthMst / TbAxiDataWidthSlv;
    localparam int unsigned AddrShift      = $clog2(TbAxiDataWidthSlv/8);
    localparam int unsigned SelWidth       = $clog2(DataMultFactor);
    typedef logic [SelWidth-1:0] sel_t;

    sel_t             fifo_exp_r_offs[$];

    initial begin : proc_aw_w_check
      automatic aw_chan_lite_t    mst_aw_chan, slv_aw_chan;
      automatic w_chan_lite_slv_t slv_w_chan;
      automatic w_chan_lite_mst_t mst_w_chan;
      automatic addr_t            exp_addr;
      automatic sel_t             w_sel;
      automatic logic [TbAxiDataWidthMst/8-1:0] slv_w_strb_concat;

      forever begin
        wait((fifo_slv_aw.size() > 0) && (fifo_mst_aw.size() > 0) && (fifo_slv_w.size() > 0) && (fifo_mst_w.size() > 0));
        slv_aw_chan = fifo_slv_aw.pop_front();
        slv_w_chan  = fifo_slv_w.pop_front();
        mst_aw_chan = fifo_mst_aw.pop_front();
        mst_w_chan  = fifo_mst_w.pop_front();
        w_sel       = slv_aw_chan.addr[AddrShift+SelWidth-1:AddrShift];

        assert (slv_aw_chan == mst_aw_chan) else $error("Master port> AW is not expected: EXP: %h ACT: %h",
            slv_aw_chan, mst_aw_chan);
        assert (slv_w_chan.data == mst_w_chan.data[TbAxiDataWidthSlv-1:0]) else $error("Master port> W.data is not expected: EXP: %h ACT: %h",
            slv_w_chan.data, mst_w_chan.data);

        slv_w_strb_concat = slv_w_chan.strb << (w_sel*TbAxiDataWidthSlv/8);
        assert (slv_w_strb_concat == mst_w_chan.strb) else $error("Master port> W.strb is not expected: EXP: %h ACT: %h",
            slv_w_chan.strb, mst_w_chan.strb);
      end
    end

    initial begin : proc_b_check
      automatic b_chan_lite_t b_act, b_exp;
      forever begin
        wait((fifo_slv_b.size() > 0) && (fifo_mst_b.size() > 0));
        b_act = fifo_slv_b.pop_front();
        b_exp = fifo_mst_b.pop_front();
        assert (b_act == b_exp) else  $error("Slave port> B.resp is not expected: EXP: %h ACT:%h",
            b_exp.resp, b_act.resp);
      end
    end

    initial begin : proc_ar_check
      automatic ar_chan_lite_t mst_ar_chan, slv_ar_chan;
      automatic sel_t r_sel;

      forever begin
        wait((fifo_slv_ar.size() > 0) && (fifo_mst_ar.size() > 0));
        slv_ar_chan = fifo_slv_ar.pop_front();
        mst_ar_chan = fifo_mst_ar.pop_front();
        r_sel = slv_ar_chan.addr[AddrShift+SelWidth-1:AddrShift];
        fifo_exp_r_offs.push_back(r_sel);

        assert (slv_ar_chan == mst_ar_chan) else $error("Master port> AR is not expected: EXP: %h ACT: %h",
          slv_ar_chan, mst_ar_chan);
      end
    end

    initial begin : proc_r_check
      automatic r_chan_lite_slv_t slv_r_chan;
      automatic r_chan_lite_mst_t mst_r_chan;
      automatic sel_t             r_sel;

      forever begin
        wait((fifo_slv_r.size() > 0) && (fifo_mst_r.size() > 0) && (fifo_exp_r_offs.size() > 0));
        slv_r_chan = fifo_slv_r.pop_front();
        mst_r_chan = fifo_mst_r.pop_front();
        r_sel      = fifo_exp_r_offs.pop_front();

        assert (slv_r_chan.resp == mst_r_chan.resp) else $error("Slave port> R.resp is not expected: EXP: %h, ACT: %h",
          mst_r_chan.resp, slv_r_chan.resp);
        assert (slv_r_chan.data == data_slv_t'(mst_r_chan.data >> (r_sel*TbAxiDataWidthSlv))) else $error("Slave port> R.data is not expected: EXP: %h, ACT: %h",
          mst_r_chan.data, slv_r_chan.data);
      end
    end

  end


  initial begin : proc_stop_sim
    wait (end_of_sim);
    repeat (1000) @(posedge clk);
    $display("Simulation stopped as all Masters transferred their data, Success.",);
    $stop();
  end

  //-----------------------------------
  // Clock generator
  //-----------------------------------
  clk_rst_gen #(
    .ClkPeriod   ( CyclTime ),
    .RstClkCycles( 5        )
  ) i_clk_gen (
    .clk_o (clk),
    .rst_no(rst_n)
  );

  //-----------------------------------
  // DUT
  //-----------------------------------
  axi_lite_dw_converter_intf #(
    .AXI_ADDR_WIDTH          ( TbAxiAddrWidth    ),
    .AXI_SLV_PORT_DATA_WIDTH ( TbAxiDataWidthSlv ),
    .AXI_MST_PORT_DATA_WIDTH ( TbAxiDataWidthMst )
  ) i_axi_lite_dw_downsizer_dut (
    .clk_i  ( clk    ),
    .rst_ni ( rst_n  ),
    .slv    ( master ),
    .mst    ( slave  )
  );
endmodule
