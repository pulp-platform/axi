# Vivado IP packaging script for axi4_burst_split
# Usage (in Vivado Tcl console):
#   cd <repo>/ip/axi4_burst_split
#   source package_ip.tcl

set script_dir [file normalize [file dirname [info script]]]
set repo_root  [file normalize [file join $script_dir .. ..]]
set ip_root    [file normalize [file join $script_dir build axi4_burst_split_ip]]
set part_name  "xc7z020clg400-1"

file mkdir $ip_root
create_project -force axi4_burst_split_ip $ip_root -part $part_name
set_property target_language Verilog [current_project]
set_property simulator_language Mixed [current_project]

# Add RTL via path references (do not copy sources)
add_files -norecurse [file join $repo_root src axi_pkg.sv]
add_files -norecurse [file join $repo_root src axi_lite_regs.sv]
add_files -norecurse [file join $repo_root src axi_burst_splitter_gran.sv]
add_files -norecurse [file join $repo_root src axi4_burst_split.sv]

# Include directories for typedef/header dependencies
set cc_includes [glob -nocomplain [file join $repo_root .bender git checkouts common_cells-* include]]
set incdirs [list [file join $repo_root include]]
if {[llength $cc_includes] > 0} {
  lappend incdirs [lindex $cc_includes 0]
}
set_property include_dirs $incdirs [current_fileset]

update_compile_order -fileset sources_1

ipx::package_project -root_dir $ip_root/packaged -vendor user.org -library user -taxonomy /UserIP -import_files
set core [ipx::current_core]
set_property name axi4_burst_split $core
set_property display_name {AXI4 Burst Split with AXI-Lite Control} $core
set_property description {AXI4 burst splitter with software-programmable len_limit via AXI4-Lite} $core
set_property version 1.0 $core

ipx::save_core $core
close_project
puts "INFO: Packaged IP at $ip_root/packaged"
