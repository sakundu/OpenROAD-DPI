source "helpers.tcl"
read_lef Nangate45/Nangate45.lef
read_def fragmented_row02.def
detailed_placement
check_placement

set def_file [make_result_file fragmented_row02.def]
write_def $def_file
diff_file $def_file fragmented_row02.defok
