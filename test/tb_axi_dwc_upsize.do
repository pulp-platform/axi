add wave -position insertpoint  \
  sim:/tb_axi_dwc_upsize/dwc_1/UPSIZE/i_axi_data_upsize/MI_DATA_WIDTH \
  sim:/tb_axi_dwc_upsize/dwc_1/UPSIZE/i_axi_data_upsize/SI_DATA_WIDTH \
  sim:/tb_axi_dwc_upsize/dwc_1/UPSIZE/i_axi_data_upsize/MI_BYTES \
  sim:/tb_axi_dwc_upsize/dwc_1/UPSIZE/i_axi_data_upsize/MI_BYTE_MASK \
  sim:/tb_axi_dwc_upsize/dwc_1/UPSIZE/i_axi_data_upsize/SI_BYTES \
  sim:/tb_axi_dwc_upsize/dwc_1/UPSIZE/i_axi_data_upsize/SI_BYTE_MASK \
  sim:/tb_axi_dwc_upsize/dwc_1/UPSIZE/i_axi_data_upsize/clk_i \
  sim:/tb_axi_dwc_upsize/dwc_1/UPSIZE/i_axi_data_upsize/rst_ni \
  sim:/tb_axi_dwc_upsize/dwc_1/UPSIZE/i_axi_data_upsize/r_state_d \
  sim:/tb_axi_dwc_upsize/dwc_1/UPSIZE/i_axi_data_upsize/r_state_q \
  sim:/tb_axi_dwc_upsize/dwc_1/UPSIZE/i_axi_data_upsize/r_req_d \
  sim:/tb_axi_dwc_upsize/dwc_1/UPSIZE/i_axi_data_upsize/r_req_q \
  sim:/tb_axi_dwc_upsize/dwc_1/UPSIZE/i_axi_data_upsize/w_state_d \
  sim:/tb_axi_dwc_upsize/dwc_1/UPSIZE/i_axi_data_upsize/w_state_q \
  sim:/tb_axi_dwc_upsize/dwc_1/UPSIZE/i_axi_data_upsize/w_req_d \
  sim:/tb_axi_dwc_upsize/dwc_1/UPSIZE/i_axi_data_upsize/w_req_q

add wave -position insertpoint -group in sim:/tb_axi_dwc_upsize/dwc_1/UPSIZE/i_axi_data_upsize/in/*
add wave -position insertpoint -group out sim:/tb_axi_dwc_upsize/dwc_1/UPSIZE/i_axi_data_upsize/out/*