import NeedlemanWunschLean.DP

namespace NW

theorem example_gattaca_gcatgcu :
    nw exampleScore exampleGap "GATTACA".toList "GCATGCU".toList = -1 := by
  rw [← nwFast_eq_nw]; decide

theorem example_gattaca_gcatgcu_unit_gap :
    nw exampleScore (-1) "GATTACA".toList "GCATGCU".toList = 0 := by
  rw [← nwFast_eq_nw]; decide

theorem example_hello_self : nw exampleScore exampleGap "HELLO".toList "HELLO".toList = 5 := by
  rw [← nwFast_eq_nw]; decide

theorem example_gattaca_self :
    nw exampleScore exampleGap "GATTACA".toList "GATTACA".toList = 7 := by
  rw [← nwFast_eq_nw]; decide

theorem example_abc_empty : nw exampleScore exampleGap "ABC".toList [] = -6 := by
  simp [nw, exampleGap]

theorem example_empty_xyz : nw exampleScore exampleGap [] "XYZ".toList = -6 := by
  simp [nw, exampleGap]

theorem align_hello_self_correct :
    alignScore exampleScore exampleGap
      (align exampleScore exampleGap "HELLO".toList "HELLO".toList) = 5 := by
  rw [alignScore_eq_nw, example_hello_self]

#eval alignFast exampleScore exampleGap "GATTACA".toList "GCATGCU".toList
#eval alignFast exampleScore (-1) "GATTACA".toList "GCATGCU".toList

end NW
