import NeedlemanWunschLean.Examples

namespace NW

/-- info: 'NW.nw_mono_in_score' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms nw_mono_in_score

/-- info: 'NW.alignScore_eq_nw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms alignScore_eq_nw

/-- info: 'NW.align_is_optimal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms align_is_optimal

/-- info: 'NW.nw_symm_of_symmetric_score' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms nw_symm_of_symmetric_score

/-- info: 'NW.nw_ge_diag_self_score' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms nw_ge_diag_self_score

/-- info: 'NW.nwFast_eq_nw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms nwFast_eq_nw

/-- info: 'NW.alignFast_eq_align' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms alignFast_eq_align

/-- info: 'NW.alignFast_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms alignFast_correct

/-- info: 'NW.example_gattaca_gcatgcu' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms example_gattaca_gcatgcu

/-- info: 'NW.example_gattaca_gcatgcu_unit_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms example_gattaca_gcatgcu_unit_gap

/-- info: 'NW.example_hello_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms example_hello_self

/-- info: 'NW.example_gattaca_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms example_gattaca_self

/-- info: 'NW.align_hello_self_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms align_hello_self_correct

end NW
