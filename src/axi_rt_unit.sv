module axi_rt_unit #(
  // parameter int unsigned NumOutstanding = 32'd0,
  // parameter int unsigned WBufferDepth   = 32'd0,
  parameter int unsigned AddrWidth      = 32'd0,
  parameter int unsigned DataWidth      = 32'd0,
  parameter int unsigned IdWidth        = 32'd0,
  parameter int unsigned UserWidth      = 32'd0,
  parameter int unsigned NumAddrRegions = 32'd0,
  parameter int unsigned NumRules       = 32'd0,
  parameter int unsigned NumPending     = 32'd0,
  parameter type         rt_rule_t      = logic,
  parameter type         addr_t         = logic,
  parameter type         axi_req_t      = logic,
  parameter type         axi_resp_t     = logic
)(
  input logic clk_i,
  input logic rst_ni,

  // Input / Slave Port
  input  axi_req_t  slv_req_i,
  output axi_resp_t slv_resp_o,

  // Output / Master Port
  output axi_req_t  mst_req_o,
  input  axi_resp_t mst_resp_i,

  // address rules
  input  rt_rule_t [NumRules-1:0] rt_rule_i
);

  // number of bytes transferred via one ax
  logic [11:0] aw_bytes;
  logic [11:0] ar_bytes;


  // // pass through
  // assign mst_req_o  = slv_req_i;
  // assign slv_resp_o = mst_resp_i;

  // get number of bytes transferred
  assign aw_bytes = ({1'b0, slv_req_i.aw.len} + 9'h001) << (slv_req_i.aw.size);
  assign ar_bytes = ({1'b0, slv_req_i.ar.len} + 9'h001) << (slv_req_i.ar.size);


  // address decoding
  addr_decode #(
    .NoIndices ( NumAddrRegions ),
    .NoRules   ( NumRules       ),
    .addr_t    ( addr_t         ),
    .rule_t    ( rt_rule_t      ),
    .Napot     ( 1'b0           )
  ) i_addr_decode_aw (
    .addr_i           ( slv_req_i.aw.addr ),
    .addr_map_i       ( rt_rule_i         ),
    .idx_o            ( ),
    .dec_valid_o      ( ),
    .dec_error_o      ( ),
    .en_default_idx_i ( '0                ),
    .default_idx_i    ( '0                )
  );

  addr_decode #(
    .NoIndices ( NumAddrRegions ),
    .NoRules   ( NumRules       ),
    .addr_t    ( addr_t         ),
    .rule_t    ( rt_rule_t      ),
    .Napot     ( 1'b0           )
  ) i_addr_decode_ar (
    .addr_i           ( slv_req_i.ar.addr ),
    .addr_map_i       ( rt_rule_i         ),
    .idx_o            ( ),
    .dec_valid_o      ( ),
    .dec_error_o      ( ),
    .en_default_idx_i ( '0                ),
    .default_idx_i    ( '0                )
  );


axi_isolate #(
  .NumPending           ( NumPending   ),
  .TerminateTransaction ( 1'b0         ),
  .AtopSupport          ( 1'b1         ),
  .AxiAddrWidth         ( AddrWidth    ),
  .AxiDataWidth         ( DataWidth    ),
  .AxiIdWidth           ( IdWidth      ),
  .AxiUserWidth         ( UserWidth    ),
  .axi_req_t            ( axi_req_t    ),
  .axi_resp_t           ( axi_resp_t   )
) i_axi_isolate (
  .clk_i,
  .rst_ni,
  .slv_req_i  ( slv_req_i  ),
  .slv_resp_o ( slv_resp_o ),
  .mst_req_o  ( mst_req_o  ),
  .mst_resp_i ( mst_resp_i ),
  .isolate_i  ( aw_bytes[10]  ),
  .isolated_o (  )
);


endmodule
