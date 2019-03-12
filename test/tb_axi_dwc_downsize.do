add wave -position insertpoint  \
  sim:/tb_axi_dwc_downsize/dwc_1/DOWNSIZE/i_axi_data_downsize/MI_DATA_WIDTH \
  sim:/tb_axi_dwc_downsize/dwc_1/DOWNSIZE/i_axi_data_downsize/SI_DATA_WIDTH \
  sim:/tb_axi_dwc_downsize/dwc_1/DOWNSIZE/i_axi_data_downsize/MI_BYTES \
  sim:/tb_axi_dwc_downsize/dwc_1/DOWNSIZE/i_axi_data_downsize/MI_BYTE_MASK \
  sim:/tb_axi_dwc_downsize/dwc_1/DOWNSIZE/i_axi_data_downsize/SI_BYTES \
  sim:/tb_axi_dwc_downsize/dwc_1/DOWNSIZE/i_axi_data_downsize/SI_BYTE_MASK \
  sim:/tb_axi_dwc_downsize/dwc_1/DOWNSIZE/i_axi_data_downsize/clk_i \
  sim:/tb_axi_dwc_downsize/dwc_1/DOWNSIZE/i_axi_data_downsize/rst_ni \
  sim:/tb_axi_dwc_downsize/dwc_1/DOWNSIZE/i_axi_data_downsize/r_state_d \
  sim:/tb_axi_dwc_downsize/dwc_1/DOWNSIZE/i_axi_data_downsize/r_state_q \
  sim:/tb_axi_dwc_downsize/dwc_1/DOWNSIZE/i_axi_data_downsize/r_req_d \
  sim:/tb_axi_dwc_downsize/dwc_1/DOWNSIZE/i_axi_data_downsize/r_req_q \
  sim:/tb_axi_dwc_downsize/dwc_1/DOWNSIZE/i_axi_data_downsize/w_state_d \
  sim:/tb_axi_dwc_downsize/dwc_1/DOWNSIZE/i_axi_data_downsize/w_state_q \
  sim:/tb_axi_dwc_downsize/dwc_1/DOWNSIZE/i_axi_data_downsize/w_req_d \
  sim:/tb_axi_dwc_downsize/dwc_1/DOWNSIZE/i_axi_data_downsize/w_req_q

add wave -position insertpoint -group in sim:/tb_axi_dwc_downsize/dwc_1/DOWNSIZE/i_axi_data_downsize/in/*
add wave -position insertpoint -group out sim:/tb_axi_dwc_downsize/dwc_1/DOWNSIZE/i_axi_data_downsize/out/*