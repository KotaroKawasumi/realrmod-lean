import RMod.BrundanEllis.StackingReferenceHexagonMiddle6
import RMod.BrundanEllis.StackingReferenceSparseMatrixCheck
import RMod.BrundanEllis.StackingReferenceHexagonAtoms635
import RMod.BrundanEllis.StackingReferenceHexagonRowColumn635

/-! Seven closed product identities for one reference triple.
The proof uses only verified atomic maps and ordinary kernel reduction. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
set_option linter.unusedSimpArgs false
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonCases6
open Superfusion

private theorem left0Middle6_eq_case_3_5_row_0_0_0 : (left0Middle6 3 5) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms635.assocABC) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_3_5_row_0_0_1 : (left0Middle6 3 5) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms635.assocABC) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_3_5_row_0_0_2 : (left0Middle6 3 5) ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms635.assocABC) ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_3_5_row_0_0_3 : (left0Middle6 3 5) ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms635.assocABC) ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_3_5_row_1_0_0 : (left0Middle6 3 5) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms635.assocABC) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_3_5_row_1_0_1 : (left0Middle6 3 5) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms635.assocABC) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_3_5_row_1_0_2 : (left0Middle6 3 5) ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms635.assocABC) ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_3_5_row_1_0_3 : (left0Middle6 3 5) ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms635.assocABC) ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_3_5_row_2_0_0 : (left0Middle6 3 5) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms635.assocABC) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_3_5_row_2_0_1 : (left0Middle6 3 5) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms635.assocABC) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_3_5_row_2_0_2 : (left0Middle6 3 5) ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms635.assocABC) ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_3_5_row_2_0_3 : (left0Middle6 3 5) ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms635.assocABC) ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_3_5_row_3_0_0 : (left0Middle6 3 5) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms635.assocABC) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_3_5_row_3_0_1 : (left0Middle6 3 5) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms635.assocABC) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_3_5_row_3_0_2 : (left0Middle6 3 5) ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms635.assocABC) ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_3_5_row_3_0_3 : (left0Middle6 3 5) ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms635.assocABC) ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_3_5_row_4_0_0 : (left0Middle6 3 5) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms635.assocABC) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_3_5_row_4_0_1 : (left0Middle6 3 5) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms635.assocABC) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_3_5_row_4_0_2 : (left0Middle6 3 5) ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms635.assocABC) ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_3_5_row_4_0_3 : (left0Middle6 3 5) ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms635.assocABC) ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_3_5_row_5_0_0 : (left0Middle6 3 5) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms635.assocABC) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_3_5_row_5_0_1 : (left0Middle6 3 5) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms635.assocABC) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_3_5_row_5_0_2 : (left0Middle6 3 5) ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms635.assocABC) ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_3_5_row_5_0_3 : (left0Middle6 3 5) ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms635.assocABC) ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_3_5_row_6_0_0 : (left0Middle6 3 5) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms635.assocABC) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_3_5_row_6_0_1 : (left0Middle6 3 5) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms635.assocABC) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_3_5_row_6_0_2 : (left0Middle6 3 5) ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms635.assocABC) ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_3_5_row_6_0_3 : (left0Middle6 3 5) ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms635.assocABC) ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_3_5_row_7_0_0 : (left0Middle6 3 5) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms635.assocABC) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_3_5_row_7_0_1 : (left0Middle6 3 5) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms635.assocABC) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_3_5_row_7_0_2 : (left0Middle6 3 5) ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms635.assocABC) ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_3_5_row_7_0_3 : (left0Middle6 3 5) ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms635.assocABC) ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_3_5_checked : left0Middle6 3 5 = HexagonAtoms635.assocABC := by
  funext r
  fin_cases r
  · exact left0Middle6_eq_case_3_5_row_0_0_0
  · exact left0Middle6_eq_case_3_5_row_0_0_1
  · exact left0Middle6_eq_case_3_5_row_0_0_2
  · exact left0Middle6_eq_case_3_5_row_0_0_3
  · exact left0Middle6_eq_case_3_5_row_1_0_0
  · exact left0Middle6_eq_case_3_5_row_1_0_1
  · exact left0Middle6_eq_case_3_5_row_1_0_2
  · exact left0Middle6_eq_case_3_5_row_1_0_3
  · exact left0Middle6_eq_case_3_5_row_2_0_0
  · exact left0Middle6_eq_case_3_5_row_2_0_1
  · exact left0Middle6_eq_case_3_5_row_2_0_2
  · exact left0Middle6_eq_case_3_5_row_2_0_3
  · exact left0Middle6_eq_case_3_5_row_3_0_0
  · exact left0Middle6_eq_case_3_5_row_3_0_1
  · exact left0Middle6_eq_case_3_5_row_3_0_2
  · exact left0Middle6_eq_case_3_5_row_3_0_3
  · exact left0Middle6_eq_case_3_5_row_4_0_0
  · exact left0Middle6_eq_case_3_5_row_4_0_1
  · exact left0Middle6_eq_case_3_5_row_4_0_2
  · exact left0Middle6_eq_case_3_5_row_4_0_3
  · exact left0Middle6_eq_case_3_5_row_5_0_0
  · exact left0Middle6_eq_case_3_5_row_5_0_1
  · exact left0Middle6_eq_case_3_5_row_5_0_2
  · exact left0Middle6_eq_case_3_5_row_5_0_3
  · exact left0Middle6_eq_case_3_5_row_6_0_0
  · exact left0Middle6_eq_case_3_5_row_6_0_1
  · exact left0Middle6_eq_case_3_5_row_6_0_2
  · exact left0Middle6_eq_case_3_5_row_6_0_3
  · exact left0Middle6_eq_case_3_5_row_7_0_0
  · exact left0Middle6_eq_case_3_5_row_7_0_1
  · exact left0Middle6_eq_case_3_5_row_7_0_2
  · exact left0Middle6_eq_case_3_5_row_7_0_3

set_option backward.isDefEq.respectTransparency false in
theorem left0Middle6_eq_case_3_5 : left0Middle6 3 5 = outerRightZ 6 3 5 * associatorZ 6 3 5 := by
  simpa only [HexagonAtoms635.assocABC_eq,
    HexagonAtoms635.outerABC_eq,
    HexagonAtoms635.assocBAC_eq,
    HexagonAtoms635.innerABC_eq,
    HexagonAtoms635.innerRightABC_eq,
    HexagonAtoms635.inverseACB_eq,
    HexagonAtoms635.innerACB_eq,
    HexagonAtoms635.assocBCA_eq,
    HexagonAtoms635.innerRightBAC_eq,
    HexagonAtoms635.assocCAB_eq,
    HexagonAtoms635.outerLeftABC_eq,
    HexagonRowColumn635.product0_eq,
    HexagonRowColumn635.product1_eq,
    HexagonRowColumn635.product2_eq,
    HexagonRowColumn635.product3_eq,
    HexagonRowColumn635.product4_eq,
    HexagonRowColumn635.product5_eq,
    HexagonRowColumn635.product6_eq,
    HexagonRowColumn635.product7_eq] using left0Middle6_eq_case_3_5_checked

private theorem left1Middle6_eq_case_3_5_row_0_0_0 : (left1Middle6 3 5) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 4)) = (HexagonAtoms635.assocBAC) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_3_5_row_0_0_1 : (left1Middle6 3 5) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 4)) = (HexagonAtoms635.assocBAC) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_3_5_row_0_0_2 : (left1Middle6 3 5) ((0 : Fin 2), (0 : Fin 4), (2 : Fin 4)) = (HexagonAtoms635.assocBAC) ((0 : Fin 2), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_3_5_row_0_0_3 : (left1Middle6 3 5) ((0 : Fin 2), (0 : Fin 4), (3 : Fin 4)) = (HexagonAtoms635.assocBAC) ((0 : Fin 2), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_3_5_row_0_1_0 : (left1Middle6 3 5) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 4)) = (HexagonAtoms635.assocBAC) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_3_5_row_0_1_1 : (left1Middle6 3 5) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 4)) = (HexagonAtoms635.assocBAC) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_3_5_row_0_1_2 : (left1Middle6 3 5) ((0 : Fin 2), (1 : Fin 4), (2 : Fin 4)) = (HexagonAtoms635.assocBAC) ((0 : Fin 2), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_3_5_row_0_1_3 : (left1Middle6 3 5) ((0 : Fin 2), (1 : Fin 4), (3 : Fin 4)) = (HexagonAtoms635.assocBAC) ((0 : Fin 2), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_3_5_row_0_2_0 : (left1Middle6 3 5) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 4)) = (HexagonAtoms635.assocBAC) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_3_5_row_0_2_1 : (left1Middle6 3 5) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 4)) = (HexagonAtoms635.assocBAC) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_3_5_row_0_2_2 : (left1Middle6 3 5) ((0 : Fin 2), (2 : Fin 4), (2 : Fin 4)) = (HexagonAtoms635.assocBAC) ((0 : Fin 2), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_3_5_row_0_2_3 : (left1Middle6 3 5) ((0 : Fin 2), (2 : Fin 4), (3 : Fin 4)) = (HexagonAtoms635.assocBAC) ((0 : Fin 2), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_3_5_row_0_3_0 : (left1Middle6 3 5) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 4)) = (HexagonAtoms635.assocBAC) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_3_5_row_0_3_1 : (left1Middle6 3 5) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 4)) = (HexagonAtoms635.assocBAC) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_3_5_row_0_3_2 : (left1Middle6 3 5) ((0 : Fin 2), (3 : Fin 4), (2 : Fin 4)) = (HexagonAtoms635.assocBAC) ((0 : Fin 2), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_3_5_row_0_3_3 : (left1Middle6 3 5) ((0 : Fin 2), (3 : Fin 4), (3 : Fin 4)) = (HexagonAtoms635.assocBAC) ((0 : Fin 2), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_3_5_row_1_0_0 : (left1Middle6 3 5) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 4)) = (HexagonAtoms635.assocBAC) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_3_5_row_1_0_1 : (left1Middle6 3 5) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 4)) = (HexagonAtoms635.assocBAC) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_3_5_row_1_0_2 : (left1Middle6 3 5) ((1 : Fin 2), (0 : Fin 4), (2 : Fin 4)) = (HexagonAtoms635.assocBAC) ((1 : Fin 2), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_3_5_row_1_0_3 : (left1Middle6 3 5) ((1 : Fin 2), (0 : Fin 4), (3 : Fin 4)) = (HexagonAtoms635.assocBAC) ((1 : Fin 2), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_3_5_row_1_1_0 : (left1Middle6 3 5) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 4)) = (HexagonAtoms635.assocBAC) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_3_5_row_1_1_1 : (left1Middle6 3 5) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 4)) = (HexagonAtoms635.assocBAC) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_3_5_row_1_1_2 : (left1Middle6 3 5) ((1 : Fin 2), (1 : Fin 4), (2 : Fin 4)) = (HexagonAtoms635.assocBAC) ((1 : Fin 2), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_3_5_row_1_1_3 : (left1Middle6 3 5) ((1 : Fin 2), (1 : Fin 4), (3 : Fin 4)) = (HexagonAtoms635.assocBAC) ((1 : Fin 2), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_3_5_row_1_2_0 : (left1Middle6 3 5) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 4)) = (HexagonAtoms635.assocBAC) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_3_5_row_1_2_1 : (left1Middle6 3 5) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 4)) = (HexagonAtoms635.assocBAC) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_3_5_row_1_2_2 : (left1Middle6 3 5) ((1 : Fin 2), (2 : Fin 4), (2 : Fin 4)) = (HexagonAtoms635.assocBAC) ((1 : Fin 2), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_3_5_row_1_2_3 : (left1Middle6 3 5) ((1 : Fin 2), (2 : Fin 4), (3 : Fin 4)) = (HexagonAtoms635.assocBAC) ((1 : Fin 2), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_3_5_row_1_3_0 : (left1Middle6 3 5) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 4)) = (HexagonAtoms635.assocBAC) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_3_5_row_1_3_1 : (left1Middle6 3 5) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 4)) = (HexagonAtoms635.assocBAC) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_3_5_row_1_3_2 : (left1Middle6 3 5) ((1 : Fin 2), (3 : Fin 4), (2 : Fin 4)) = (HexagonAtoms635.assocBAC) ((1 : Fin 2), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_3_5_row_1_3_3 : (left1Middle6 3 5) ((1 : Fin 2), (3 : Fin 4), (3 : Fin 4)) = (HexagonAtoms635.assocBAC) ((1 : Fin 2), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_3_5_checked : left1Middle6 3 5 = HexagonAtoms635.assocBAC := by
  funext r
  fin_cases r
  · exact left1Middle6_eq_case_3_5_row_0_0_0
  · exact left1Middle6_eq_case_3_5_row_0_0_1
  · exact left1Middle6_eq_case_3_5_row_0_0_2
  · exact left1Middle6_eq_case_3_5_row_0_0_3
  · exact left1Middle6_eq_case_3_5_row_0_1_0
  · exact left1Middle6_eq_case_3_5_row_0_1_1
  · exact left1Middle6_eq_case_3_5_row_0_1_2
  · exact left1Middle6_eq_case_3_5_row_0_1_3
  · exact left1Middle6_eq_case_3_5_row_0_2_0
  · exact left1Middle6_eq_case_3_5_row_0_2_1
  · exact left1Middle6_eq_case_3_5_row_0_2_2
  · exact left1Middle6_eq_case_3_5_row_0_2_3
  · exact left1Middle6_eq_case_3_5_row_0_3_0
  · exact left1Middle6_eq_case_3_5_row_0_3_1
  · exact left1Middle6_eq_case_3_5_row_0_3_2
  · exact left1Middle6_eq_case_3_5_row_0_3_3
  · exact left1Middle6_eq_case_3_5_row_1_0_0
  · exact left1Middle6_eq_case_3_5_row_1_0_1
  · exact left1Middle6_eq_case_3_5_row_1_0_2
  · exact left1Middle6_eq_case_3_5_row_1_0_3
  · exact left1Middle6_eq_case_3_5_row_1_1_0
  · exact left1Middle6_eq_case_3_5_row_1_1_1
  · exact left1Middle6_eq_case_3_5_row_1_1_2
  · exact left1Middle6_eq_case_3_5_row_1_1_3
  · exact left1Middle6_eq_case_3_5_row_1_2_0
  · exact left1Middle6_eq_case_3_5_row_1_2_1
  · exact left1Middle6_eq_case_3_5_row_1_2_2
  · exact left1Middle6_eq_case_3_5_row_1_2_3
  · exact left1Middle6_eq_case_3_5_row_1_3_0
  · exact left1Middle6_eq_case_3_5_row_1_3_1
  · exact left1Middle6_eq_case_3_5_row_1_3_2
  · exact left1Middle6_eq_case_3_5_row_1_3_3

set_option backward.isDefEq.respectTransparency false in
theorem left1Middle6_eq_case_3_5 : left1Middle6 3 5 = associatorZ 3 6 5 * innerLeftZ 6 3 5 := by
  simpa only [HexagonAtoms635.assocABC_eq,
    HexagonAtoms635.outerABC_eq,
    HexagonAtoms635.assocBAC_eq,
    HexagonAtoms635.innerABC_eq,
    HexagonAtoms635.innerRightABC_eq,
    HexagonAtoms635.inverseACB_eq,
    HexagonAtoms635.innerACB_eq,
    HexagonAtoms635.assocBCA_eq,
    HexagonAtoms635.innerRightBAC_eq,
    HexagonAtoms635.assocCAB_eq,
    HexagonAtoms635.outerLeftABC_eq,
    HexagonRowColumn635.product0_eq,
    HexagonRowColumn635.product1_eq,
    HexagonRowColumn635.product2_eq,
    HexagonRowColumn635.product3_eq,
    HexagonRowColumn635.product4_eq,
    HexagonRowColumn635.product5_eq,
    HexagonRowColumn635.product6_eq,
    HexagonRowColumn635.product7_eq] using left1Middle6_eq_case_3_5_checked

private theorem right0Middle6_eq_case_3_5_row_0_0_0 : (right0Middle6 3 5) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms635.assocABC) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_3_5_row_0_0_1 : (right0Middle6 3 5) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms635.assocABC) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_3_5_row_0_0_2 : (right0Middle6 3 5) ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms635.assocABC) ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_3_5_row_0_0_3 : (right0Middle6 3 5) ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms635.assocABC) ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_3_5_row_1_0_0 : (right0Middle6 3 5) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms635.assocABC) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_3_5_row_1_0_1 : (right0Middle6 3 5) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms635.assocABC) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_3_5_row_1_0_2 : (right0Middle6 3 5) ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms635.assocABC) ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_3_5_row_1_0_3 : (right0Middle6 3 5) ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms635.assocABC) ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_3_5_row_2_0_0 : (right0Middle6 3 5) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms635.assocABC) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_3_5_row_2_0_1 : (right0Middle6 3 5) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms635.assocABC) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_3_5_row_2_0_2 : (right0Middle6 3 5) ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms635.assocABC) ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_3_5_row_2_0_3 : (right0Middle6 3 5) ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms635.assocABC) ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_3_5_row_3_0_0 : (right0Middle6 3 5) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms635.assocABC) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_3_5_row_3_0_1 : (right0Middle6 3 5) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms635.assocABC) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_3_5_row_3_0_2 : (right0Middle6 3 5) ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms635.assocABC) ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_3_5_row_3_0_3 : (right0Middle6 3 5) ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms635.assocABC) ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_3_5_row_4_0_0 : (right0Middle6 3 5) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms635.assocABC) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_3_5_row_4_0_1 : (right0Middle6 3 5) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms635.assocABC) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_3_5_row_4_0_2 : (right0Middle6 3 5) ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms635.assocABC) ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_3_5_row_4_0_3 : (right0Middle6 3 5) ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms635.assocABC) ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_3_5_row_5_0_0 : (right0Middle6 3 5) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms635.assocABC) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_3_5_row_5_0_1 : (right0Middle6 3 5) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms635.assocABC) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_3_5_row_5_0_2 : (right0Middle6 3 5) ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms635.assocABC) ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_3_5_row_5_0_3 : (right0Middle6 3 5) ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms635.assocABC) ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_3_5_row_6_0_0 : (right0Middle6 3 5) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms635.assocABC) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_3_5_row_6_0_1 : (right0Middle6 3 5) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms635.assocABC) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_3_5_row_6_0_2 : (right0Middle6 3 5) ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms635.assocABC) ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_3_5_row_6_0_3 : (right0Middle6 3 5) ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms635.assocABC) ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_3_5_row_7_0_0 : (right0Middle6 3 5) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms635.assocABC) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_3_5_row_7_0_1 : (right0Middle6 3 5) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms635.assocABC) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_3_5_row_7_0_2 : (right0Middle6 3 5) ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms635.assocABC) ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_3_5_row_7_0_3 : (right0Middle6 3 5) ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms635.assocABC) ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_3_5_checked : right0Middle6 3 5 = HexagonAtoms635.assocABC := by
  funext r
  fin_cases r
  · exact right0Middle6_eq_case_3_5_row_0_0_0
  · exact right0Middle6_eq_case_3_5_row_0_0_1
  · exact right0Middle6_eq_case_3_5_row_0_0_2
  · exact right0Middle6_eq_case_3_5_row_0_0_3
  · exact right0Middle6_eq_case_3_5_row_1_0_0
  · exact right0Middle6_eq_case_3_5_row_1_0_1
  · exact right0Middle6_eq_case_3_5_row_1_0_2
  · exact right0Middle6_eq_case_3_5_row_1_0_3
  · exact right0Middle6_eq_case_3_5_row_2_0_0
  · exact right0Middle6_eq_case_3_5_row_2_0_1
  · exact right0Middle6_eq_case_3_5_row_2_0_2
  · exact right0Middle6_eq_case_3_5_row_2_0_3
  · exact right0Middle6_eq_case_3_5_row_3_0_0
  · exact right0Middle6_eq_case_3_5_row_3_0_1
  · exact right0Middle6_eq_case_3_5_row_3_0_2
  · exact right0Middle6_eq_case_3_5_row_3_0_3
  · exact right0Middle6_eq_case_3_5_row_4_0_0
  · exact right0Middle6_eq_case_3_5_row_4_0_1
  · exact right0Middle6_eq_case_3_5_row_4_0_2
  · exact right0Middle6_eq_case_3_5_row_4_0_3
  · exact right0Middle6_eq_case_3_5_row_5_0_0
  · exact right0Middle6_eq_case_3_5_row_5_0_1
  · exact right0Middle6_eq_case_3_5_row_5_0_2
  · exact right0Middle6_eq_case_3_5_row_5_0_3
  · exact right0Middle6_eq_case_3_5_row_6_0_0
  · exact right0Middle6_eq_case_3_5_row_6_0_1
  · exact right0Middle6_eq_case_3_5_row_6_0_2
  · exact right0Middle6_eq_case_3_5_row_6_0_3
  · exact right0Middle6_eq_case_3_5_row_7_0_0
  · exact right0Middle6_eq_case_3_5_row_7_0_1
  · exact right0Middle6_eq_case_3_5_row_7_0_2
  · exact right0Middle6_eq_case_3_5_row_7_0_3

set_option backward.isDefEq.respectTransparency false in
theorem right0Middle6_eq_case_3_5 : right0Middle6 3 5 = innerRightZ 6 3 5 * associatorZ 6 3 5 := by
  simpa only [HexagonAtoms635.assocABC_eq,
    HexagonAtoms635.outerABC_eq,
    HexagonAtoms635.assocBAC_eq,
    HexagonAtoms635.innerABC_eq,
    HexagonAtoms635.innerRightABC_eq,
    HexagonAtoms635.inverseACB_eq,
    HexagonAtoms635.innerACB_eq,
    HexagonAtoms635.assocBCA_eq,
    HexagonAtoms635.innerRightBAC_eq,
    HexagonAtoms635.assocCAB_eq,
    HexagonAtoms635.outerLeftABC_eq,
    HexagonRowColumn635.product0_eq,
    HexagonRowColumn635.product1_eq,
    HexagonRowColumn635.product2_eq,
    HexagonRowColumn635.product3_eq,
    HexagonRowColumn635.product4_eq,
    HexagonRowColumn635.product5_eq,
    HexagonRowColumn635.product6_eq,
    HexagonRowColumn635.product7_eq] using right0Middle6_eq_case_3_5_checked

private theorem right1Middle6_eq_case_3_5_row_0_0_0 : (right1Middle6 3 5) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn635.rows_inverseACB HexagonRowColumn635.cols_right0) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_3_5_row_0_0_1 : (right1Middle6 3 5) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn635.rows_inverseACB HexagonRowColumn635.cols_right0) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_3_5_row_0_0_2 : (right1Middle6 3 5) ((0 : Fin 2), (0 : Fin 4), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn635.rows_inverseACB HexagonRowColumn635.cols_right0) ((0 : Fin 2), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_3_5_row_0_0_3 : (right1Middle6 3 5) ((0 : Fin 2), (0 : Fin 4), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn635.rows_inverseACB HexagonRowColumn635.cols_right0) ((0 : Fin 2), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_3_5_row_0_1_0 : (right1Middle6 3 5) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn635.rows_inverseACB HexagonRowColumn635.cols_right0) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_3_5_row_0_1_1 : (right1Middle6 3 5) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn635.rows_inverseACB HexagonRowColumn635.cols_right0) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_3_5_row_0_1_2 : (right1Middle6 3 5) ((0 : Fin 2), (1 : Fin 4), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn635.rows_inverseACB HexagonRowColumn635.cols_right0) ((0 : Fin 2), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_3_5_row_0_1_3 : (right1Middle6 3 5) ((0 : Fin 2), (1 : Fin 4), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn635.rows_inverseACB HexagonRowColumn635.cols_right0) ((0 : Fin 2), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_3_5_row_0_2_0 : (right1Middle6 3 5) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn635.rows_inverseACB HexagonRowColumn635.cols_right0) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_3_5_row_0_2_1 : (right1Middle6 3 5) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn635.rows_inverseACB HexagonRowColumn635.cols_right0) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_3_5_row_0_2_2 : (right1Middle6 3 5) ((0 : Fin 2), (2 : Fin 4), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn635.rows_inverseACB HexagonRowColumn635.cols_right0) ((0 : Fin 2), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_3_5_row_0_2_3 : (right1Middle6 3 5) ((0 : Fin 2), (2 : Fin 4), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn635.rows_inverseACB HexagonRowColumn635.cols_right0) ((0 : Fin 2), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_3_5_row_0_3_0 : (right1Middle6 3 5) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn635.rows_inverseACB HexagonRowColumn635.cols_right0) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_3_5_row_0_3_1 : (right1Middle6 3 5) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn635.rows_inverseACB HexagonRowColumn635.cols_right0) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_3_5_row_0_3_2 : (right1Middle6 3 5) ((0 : Fin 2), (3 : Fin 4), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn635.rows_inverseACB HexagonRowColumn635.cols_right0) ((0 : Fin 2), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_3_5_row_0_3_3 : (right1Middle6 3 5) ((0 : Fin 2), (3 : Fin 4), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn635.rows_inverseACB HexagonRowColumn635.cols_right0) ((0 : Fin 2), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_3_5_row_1_0_0 : (right1Middle6 3 5) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn635.rows_inverseACB HexagonRowColumn635.cols_right0) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_3_5_row_1_0_1 : (right1Middle6 3 5) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn635.rows_inverseACB HexagonRowColumn635.cols_right0) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_3_5_row_1_0_2 : (right1Middle6 3 5) ((1 : Fin 2), (0 : Fin 4), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn635.rows_inverseACB HexagonRowColumn635.cols_right0) ((1 : Fin 2), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_3_5_row_1_0_3 : (right1Middle6 3 5) ((1 : Fin 2), (0 : Fin 4), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn635.rows_inverseACB HexagonRowColumn635.cols_right0) ((1 : Fin 2), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_3_5_row_1_1_0 : (right1Middle6 3 5) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn635.rows_inverseACB HexagonRowColumn635.cols_right0) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_3_5_row_1_1_1 : (right1Middle6 3 5) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn635.rows_inverseACB HexagonRowColumn635.cols_right0) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_3_5_row_1_1_2 : (right1Middle6 3 5) ((1 : Fin 2), (1 : Fin 4), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn635.rows_inverseACB HexagonRowColumn635.cols_right0) ((1 : Fin 2), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_3_5_row_1_1_3 : (right1Middle6 3 5) ((1 : Fin 2), (1 : Fin 4), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn635.rows_inverseACB HexagonRowColumn635.cols_right0) ((1 : Fin 2), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_3_5_row_1_2_0 : (right1Middle6 3 5) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn635.rows_inverseACB HexagonRowColumn635.cols_right0) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_3_5_row_1_2_1 : (right1Middle6 3 5) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn635.rows_inverseACB HexagonRowColumn635.cols_right0) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_3_5_row_1_2_2 : (right1Middle6 3 5) ((1 : Fin 2), (2 : Fin 4), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn635.rows_inverseACB HexagonRowColumn635.cols_right0) ((1 : Fin 2), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_3_5_row_1_2_3 : (right1Middle6 3 5) ((1 : Fin 2), (2 : Fin 4), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn635.rows_inverseACB HexagonRowColumn635.cols_right0) ((1 : Fin 2), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_3_5_row_1_3_0 : (right1Middle6 3 5) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn635.rows_inverseACB HexagonRowColumn635.cols_right0) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_3_5_row_1_3_1 : (right1Middle6 3 5) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn635.rows_inverseACB HexagonRowColumn635.cols_right0) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_3_5_row_1_3_2 : (right1Middle6 3 5) ((1 : Fin 2), (3 : Fin 4), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn635.rows_inverseACB HexagonRowColumn635.cols_right0) ((1 : Fin 2), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_3_5_row_1_3_3 : (right1Middle6 3 5) ((1 : Fin 2), (3 : Fin 4), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn635.rows_inverseACB HexagonRowColumn635.cols_right0) ((1 : Fin 2), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_3_5_checked : right1Middle6 3 5 = rowColumnMul HexagonRowColumn635.rows_inverseACB HexagonRowColumn635.cols_right0 := by
  funext r
  fin_cases r
  · exact right1Middle6_eq_case_3_5_row_0_0_0
  · exact right1Middle6_eq_case_3_5_row_0_0_1
  · exact right1Middle6_eq_case_3_5_row_0_0_2
  · exact right1Middle6_eq_case_3_5_row_0_0_3
  · exact right1Middle6_eq_case_3_5_row_0_1_0
  · exact right1Middle6_eq_case_3_5_row_0_1_1
  · exact right1Middle6_eq_case_3_5_row_0_1_2
  · exact right1Middle6_eq_case_3_5_row_0_1_3
  · exact right1Middle6_eq_case_3_5_row_0_2_0
  · exact right1Middle6_eq_case_3_5_row_0_2_1
  · exact right1Middle6_eq_case_3_5_row_0_2_2
  · exact right1Middle6_eq_case_3_5_row_0_2_3
  · exact right1Middle6_eq_case_3_5_row_0_3_0
  · exact right1Middle6_eq_case_3_5_row_0_3_1
  · exact right1Middle6_eq_case_3_5_row_0_3_2
  · exact right1Middle6_eq_case_3_5_row_0_3_3
  · exact right1Middle6_eq_case_3_5_row_1_0_0
  · exact right1Middle6_eq_case_3_5_row_1_0_1
  · exact right1Middle6_eq_case_3_5_row_1_0_2
  · exact right1Middle6_eq_case_3_5_row_1_0_3
  · exact right1Middle6_eq_case_3_5_row_1_1_0
  · exact right1Middle6_eq_case_3_5_row_1_1_1
  · exact right1Middle6_eq_case_3_5_row_1_1_2
  · exact right1Middle6_eq_case_3_5_row_1_1_3
  · exact right1Middle6_eq_case_3_5_row_1_2_0
  · exact right1Middle6_eq_case_3_5_row_1_2_1
  · exact right1Middle6_eq_case_3_5_row_1_2_2
  · exact right1Middle6_eq_case_3_5_row_1_2_3
  · exact right1Middle6_eq_case_3_5_row_1_3_0
  · exact right1Middle6_eq_case_3_5_row_1_3_1
  · exact right1Middle6_eq_case_3_5_row_1_3_2
  · exact right1Middle6_eq_case_3_5_row_1_3_3

set_option backward.isDefEq.respectTransparency false in
theorem right1Middle6_eq_case_3_5 : right1Middle6 3 5 = associatorInverseZ 6 5 3 * right0Middle6 3 5 := by
  simpa only [HexagonAtoms635.assocABC_eq,
    HexagonAtoms635.outerABC_eq,
    HexagonAtoms635.assocBAC_eq,
    HexagonAtoms635.innerABC_eq,
    HexagonAtoms635.innerRightABC_eq,
    HexagonAtoms635.inverseACB_eq,
    HexagonAtoms635.innerACB_eq,
    HexagonAtoms635.assocBCA_eq,
    HexagonAtoms635.innerRightBAC_eq,
    HexagonAtoms635.assocCAB_eq,
    HexagonAtoms635.outerLeftABC_eq,
    HexagonRowColumn635.product0_eq,
    HexagonRowColumn635.product1_eq,
    HexagonRowColumn635.product2_eq,
    HexagonRowColumn635.product3_eq,
    HexagonRowColumn635.product4_eq,
    HexagonRowColumn635.product5_eq,
    HexagonRowColumn635.product6_eq,
    HexagonRowColumn635.product7_eq] using right1Middle6_eq_case_3_5_checked

private theorem right2Middle6_eq_case_3_5_row_0_0_0 : (right2Middle6 3 5) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 4)) = (right1Middle6 3 5) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_3_5_row_0_0_1 : (right2Middle6 3 5) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 4)) = (right1Middle6 3 5) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_3_5_row_0_0_2 : (right2Middle6 3 5) ((0 : Fin 2), (0 : Fin 4), (2 : Fin 4)) = (right1Middle6 3 5) ((0 : Fin 2), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_3_5_row_0_0_3 : (right2Middle6 3 5) ((0 : Fin 2), (0 : Fin 4), (3 : Fin 4)) = (right1Middle6 3 5) ((0 : Fin 2), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_3_5_row_0_1_0 : (right2Middle6 3 5) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 4)) = (right1Middle6 3 5) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_3_5_row_0_1_1 : (right2Middle6 3 5) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 4)) = (right1Middle6 3 5) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_3_5_row_0_1_2 : (right2Middle6 3 5) ((0 : Fin 2), (1 : Fin 4), (2 : Fin 4)) = (right1Middle6 3 5) ((0 : Fin 2), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_3_5_row_0_1_3 : (right2Middle6 3 5) ((0 : Fin 2), (1 : Fin 4), (3 : Fin 4)) = (right1Middle6 3 5) ((0 : Fin 2), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_3_5_row_0_2_0 : (right2Middle6 3 5) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 4)) = (right1Middle6 3 5) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_3_5_row_0_2_1 : (right2Middle6 3 5) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 4)) = (right1Middle6 3 5) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_3_5_row_0_2_2 : (right2Middle6 3 5) ((0 : Fin 2), (2 : Fin 4), (2 : Fin 4)) = (right1Middle6 3 5) ((0 : Fin 2), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_3_5_row_0_2_3 : (right2Middle6 3 5) ((0 : Fin 2), (2 : Fin 4), (3 : Fin 4)) = (right1Middle6 3 5) ((0 : Fin 2), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_3_5_row_0_3_0 : (right2Middle6 3 5) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 4)) = (right1Middle6 3 5) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_3_5_row_0_3_1 : (right2Middle6 3 5) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 4)) = (right1Middle6 3 5) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_3_5_row_0_3_2 : (right2Middle6 3 5) ((0 : Fin 2), (3 : Fin 4), (2 : Fin 4)) = (right1Middle6 3 5) ((0 : Fin 2), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_3_5_row_0_3_3 : (right2Middle6 3 5) ((0 : Fin 2), (3 : Fin 4), (3 : Fin 4)) = (right1Middle6 3 5) ((0 : Fin 2), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_3_5_row_1_0_0 : (right2Middle6 3 5) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 4)) = (right1Middle6 3 5) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_3_5_row_1_0_1 : (right2Middle6 3 5) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 4)) = (right1Middle6 3 5) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_3_5_row_1_0_2 : (right2Middle6 3 5) ((1 : Fin 2), (0 : Fin 4), (2 : Fin 4)) = (right1Middle6 3 5) ((1 : Fin 2), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_3_5_row_1_0_3 : (right2Middle6 3 5) ((1 : Fin 2), (0 : Fin 4), (3 : Fin 4)) = (right1Middle6 3 5) ((1 : Fin 2), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_3_5_row_1_1_0 : (right2Middle6 3 5) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 4)) = (right1Middle6 3 5) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_3_5_row_1_1_1 : (right2Middle6 3 5) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 4)) = (right1Middle6 3 5) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_3_5_row_1_1_2 : (right2Middle6 3 5) ((1 : Fin 2), (1 : Fin 4), (2 : Fin 4)) = (right1Middle6 3 5) ((1 : Fin 2), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_3_5_row_1_1_3 : (right2Middle6 3 5) ((1 : Fin 2), (1 : Fin 4), (3 : Fin 4)) = (right1Middle6 3 5) ((1 : Fin 2), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_3_5_row_1_2_0 : (right2Middle6 3 5) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 4)) = (right1Middle6 3 5) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_3_5_row_1_2_1 : (right2Middle6 3 5) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 4)) = (right1Middle6 3 5) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_3_5_row_1_2_2 : (right2Middle6 3 5) ((1 : Fin 2), (2 : Fin 4), (2 : Fin 4)) = (right1Middle6 3 5) ((1 : Fin 2), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_3_5_row_1_2_3 : (right2Middle6 3 5) ((1 : Fin 2), (2 : Fin 4), (3 : Fin 4)) = (right1Middle6 3 5) ((1 : Fin 2), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_3_5_row_1_3_0 : (right2Middle6 3 5) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 4)) = (right1Middle6 3 5) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_3_5_row_1_3_1 : (right2Middle6 3 5) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 4)) = (right1Middle6 3 5) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_3_5_row_1_3_2 : (right2Middle6 3 5) ((1 : Fin 2), (3 : Fin 4), (2 : Fin 4)) = (right1Middle6 3 5) ((1 : Fin 2), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_3_5_row_1_3_3 : (right2Middle6 3 5) ((1 : Fin 2), (3 : Fin 4), (3 : Fin 4)) = (right1Middle6 3 5) ((1 : Fin 2), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_3_5_checked : right2Middle6 3 5 = right1Middle6 3 5 := by
  funext r
  fin_cases r
  · exact right2Middle6_eq_case_3_5_row_0_0_0
  · exact right2Middle6_eq_case_3_5_row_0_0_1
  · exact right2Middle6_eq_case_3_5_row_0_0_2
  · exact right2Middle6_eq_case_3_5_row_0_0_3
  · exact right2Middle6_eq_case_3_5_row_0_1_0
  · exact right2Middle6_eq_case_3_5_row_0_1_1
  · exact right2Middle6_eq_case_3_5_row_0_1_2
  · exact right2Middle6_eq_case_3_5_row_0_1_3
  · exact right2Middle6_eq_case_3_5_row_0_2_0
  · exact right2Middle6_eq_case_3_5_row_0_2_1
  · exact right2Middle6_eq_case_3_5_row_0_2_2
  · exact right2Middle6_eq_case_3_5_row_0_2_3
  · exact right2Middle6_eq_case_3_5_row_0_3_0
  · exact right2Middle6_eq_case_3_5_row_0_3_1
  · exact right2Middle6_eq_case_3_5_row_0_3_2
  · exact right2Middle6_eq_case_3_5_row_0_3_3
  · exact right2Middle6_eq_case_3_5_row_1_0_0
  · exact right2Middle6_eq_case_3_5_row_1_0_1
  · exact right2Middle6_eq_case_3_5_row_1_0_2
  · exact right2Middle6_eq_case_3_5_row_1_0_3
  · exact right2Middle6_eq_case_3_5_row_1_1_0
  · exact right2Middle6_eq_case_3_5_row_1_1_1
  · exact right2Middle6_eq_case_3_5_row_1_1_2
  · exact right2Middle6_eq_case_3_5_row_1_1_3
  · exact right2Middle6_eq_case_3_5_row_1_2_0
  · exact right2Middle6_eq_case_3_5_row_1_2_1
  · exact right2Middle6_eq_case_3_5_row_1_2_2
  · exact right2Middle6_eq_case_3_5_row_1_2_3
  · exact right2Middle6_eq_case_3_5_row_1_3_0
  · exact right2Middle6_eq_case_3_5_row_1_3_1
  · exact right2Middle6_eq_case_3_5_row_1_3_2
  · exact right2Middle6_eq_case_3_5_row_1_3_3

set_option backward.isDefEq.respectTransparency false in
theorem right2Middle6_eq_case_3_5 : right2Middle6 3 5 = innerLeftZ 6 5 3 * right1Middle6 3 5 := by
  simpa only [HexagonAtoms635.assocABC_eq,
    HexagonAtoms635.outerABC_eq,
    HexagonAtoms635.assocBAC_eq,
    HexagonAtoms635.innerABC_eq,
    HexagonAtoms635.innerRightABC_eq,
    HexagonAtoms635.inverseACB_eq,
    HexagonAtoms635.innerACB_eq,
    HexagonAtoms635.assocBCA_eq,
    HexagonAtoms635.innerRightBAC_eq,
    HexagonAtoms635.assocCAB_eq,
    HexagonAtoms635.outerLeftABC_eq,
    HexagonRowColumn635.product0_eq,
    HexagonRowColumn635.product1_eq,
    HexagonRowColumn635.product2_eq,
    HexagonRowColumn635.product3_eq,
    HexagonRowColumn635.product4_eq,
    HexagonRowColumn635.product5_eq,
    HexagonRowColumn635.product6_eq,
    HexagonRowColumn635.product7_eq] using right2Middle6_eq_case_3_5_checked

private theorem leftFinal6_case_3_5_row_0_0_0 : (((-1 : ℤ) ^ (leftScaleBit 6 3 5).val * positiveScale (leftScaleExponent 6 3 5)) •
      (rowColumnMul HexagonRowColumn635.rows_assocBCA HexagonRowColumn635.cols_left0)) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 4)) = (negativeScale (leftScaleExponent 6 3 5) • (left1Middle6 3 5)) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal6_case_3_5_row_0_0_1 : (((-1 : ℤ) ^ (leftScaleBit 6 3 5).val * positiveScale (leftScaleExponent 6 3 5)) •
      (rowColumnMul HexagonRowColumn635.rows_assocBCA HexagonRowColumn635.cols_left0)) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 4)) = (negativeScale (leftScaleExponent 6 3 5) • (left1Middle6 3 5)) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal6_case_3_5_row_0_0_2 : (((-1 : ℤ) ^ (leftScaleBit 6 3 5).val * positiveScale (leftScaleExponent 6 3 5)) •
      (rowColumnMul HexagonRowColumn635.rows_assocBCA HexagonRowColumn635.cols_left0)) ((0 : Fin 2), (0 : Fin 4), (2 : Fin 4)) = (negativeScale (leftScaleExponent 6 3 5) • (left1Middle6 3 5)) ((0 : Fin 2), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal6_case_3_5_row_0_0_3 : (((-1 : ℤ) ^ (leftScaleBit 6 3 5).val * positiveScale (leftScaleExponent 6 3 5)) •
      (rowColumnMul HexagonRowColumn635.rows_assocBCA HexagonRowColumn635.cols_left0)) ((0 : Fin 2), (0 : Fin 4), (3 : Fin 4)) = (negativeScale (leftScaleExponent 6 3 5) • (left1Middle6 3 5)) ((0 : Fin 2), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal6_case_3_5_row_0_1_0 : (((-1 : ℤ) ^ (leftScaleBit 6 3 5).val * positiveScale (leftScaleExponent 6 3 5)) •
      (rowColumnMul HexagonRowColumn635.rows_assocBCA HexagonRowColumn635.cols_left0)) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 4)) = (negativeScale (leftScaleExponent 6 3 5) • (left1Middle6 3 5)) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal6_case_3_5_row_0_1_1 : (((-1 : ℤ) ^ (leftScaleBit 6 3 5).val * positiveScale (leftScaleExponent 6 3 5)) •
      (rowColumnMul HexagonRowColumn635.rows_assocBCA HexagonRowColumn635.cols_left0)) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 4)) = (negativeScale (leftScaleExponent 6 3 5) • (left1Middle6 3 5)) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal6_case_3_5_row_0_1_2 : (((-1 : ℤ) ^ (leftScaleBit 6 3 5).val * positiveScale (leftScaleExponent 6 3 5)) •
      (rowColumnMul HexagonRowColumn635.rows_assocBCA HexagonRowColumn635.cols_left0)) ((0 : Fin 2), (1 : Fin 4), (2 : Fin 4)) = (negativeScale (leftScaleExponent 6 3 5) • (left1Middle6 3 5)) ((0 : Fin 2), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal6_case_3_5_row_0_1_3 : (((-1 : ℤ) ^ (leftScaleBit 6 3 5).val * positiveScale (leftScaleExponent 6 3 5)) •
      (rowColumnMul HexagonRowColumn635.rows_assocBCA HexagonRowColumn635.cols_left0)) ((0 : Fin 2), (1 : Fin 4), (3 : Fin 4)) = (negativeScale (leftScaleExponent 6 3 5) • (left1Middle6 3 5)) ((0 : Fin 2), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal6_case_3_5_row_0_2_0 : (((-1 : ℤ) ^ (leftScaleBit 6 3 5).val * positiveScale (leftScaleExponent 6 3 5)) •
      (rowColumnMul HexagonRowColumn635.rows_assocBCA HexagonRowColumn635.cols_left0)) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 4)) = (negativeScale (leftScaleExponent 6 3 5) • (left1Middle6 3 5)) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal6_case_3_5_row_0_2_1 : (((-1 : ℤ) ^ (leftScaleBit 6 3 5).val * positiveScale (leftScaleExponent 6 3 5)) •
      (rowColumnMul HexagonRowColumn635.rows_assocBCA HexagonRowColumn635.cols_left0)) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 4)) = (negativeScale (leftScaleExponent 6 3 5) • (left1Middle6 3 5)) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal6_case_3_5_row_0_2_2 : (((-1 : ℤ) ^ (leftScaleBit 6 3 5).val * positiveScale (leftScaleExponent 6 3 5)) •
      (rowColumnMul HexagonRowColumn635.rows_assocBCA HexagonRowColumn635.cols_left0)) ((0 : Fin 2), (2 : Fin 4), (2 : Fin 4)) = (negativeScale (leftScaleExponent 6 3 5) • (left1Middle6 3 5)) ((0 : Fin 2), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal6_case_3_5_row_0_2_3 : (((-1 : ℤ) ^ (leftScaleBit 6 3 5).val * positiveScale (leftScaleExponent 6 3 5)) •
      (rowColumnMul HexagonRowColumn635.rows_assocBCA HexagonRowColumn635.cols_left0)) ((0 : Fin 2), (2 : Fin 4), (3 : Fin 4)) = (negativeScale (leftScaleExponent 6 3 5) • (left1Middle6 3 5)) ((0 : Fin 2), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal6_case_3_5_row_0_3_0 : (((-1 : ℤ) ^ (leftScaleBit 6 3 5).val * positiveScale (leftScaleExponent 6 3 5)) •
      (rowColumnMul HexagonRowColumn635.rows_assocBCA HexagonRowColumn635.cols_left0)) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 4)) = (negativeScale (leftScaleExponent 6 3 5) • (left1Middle6 3 5)) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal6_case_3_5_row_0_3_1 : (((-1 : ℤ) ^ (leftScaleBit 6 3 5).val * positiveScale (leftScaleExponent 6 3 5)) •
      (rowColumnMul HexagonRowColumn635.rows_assocBCA HexagonRowColumn635.cols_left0)) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 4)) = (negativeScale (leftScaleExponent 6 3 5) • (left1Middle6 3 5)) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal6_case_3_5_row_0_3_2 : (((-1 : ℤ) ^ (leftScaleBit 6 3 5).val * positiveScale (leftScaleExponent 6 3 5)) •
      (rowColumnMul HexagonRowColumn635.rows_assocBCA HexagonRowColumn635.cols_left0)) ((0 : Fin 2), (3 : Fin 4), (2 : Fin 4)) = (negativeScale (leftScaleExponent 6 3 5) • (left1Middle6 3 5)) ((0 : Fin 2), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal6_case_3_5_row_0_3_3 : (((-1 : ℤ) ^ (leftScaleBit 6 3 5).val * positiveScale (leftScaleExponent 6 3 5)) •
      (rowColumnMul HexagonRowColumn635.rows_assocBCA HexagonRowColumn635.cols_left0)) ((0 : Fin 2), (3 : Fin 4), (3 : Fin 4)) = (negativeScale (leftScaleExponent 6 3 5) • (left1Middle6 3 5)) ((0 : Fin 2), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal6_case_3_5_row_1_0_0 : (((-1 : ℤ) ^ (leftScaleBit 6 3 5).val * positiveScale (leftScaleExponent 6 3 5)) •
      (rowColumnMul HexagonRowColumn635.rows_assocBCA HexagonRowColumn635.cols_left0)) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 4)) = (negativeScale (leftScaleExponent 6 3 5) • (left1Middle6 3 5)) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal6_case_3_5_row_1_0_1 : (((-1 : ℤ) ^ (leftScaleBit 6 3 5).val * positiveScale (leftScaleExponent 6 3 5)) •
      (rowColumnMul HexagonRowColumn635.rows_assocBCA HexagonRowColumn635.cols_left0)) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 4)) = (negativeScale (leftScaleExponent 6 3 5) • (left1Middle6 3 5)) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal6_case_3_5_row_1_0_2 : (((-1 : ℤ) ^ (leftScaleBit 6 3 5).val * positiveScale (leftScaleExponent 6 3 5)) •
      (rowColumnMul HexagonRowColumn635.rows_assocBCA HexagonRowColumn635.cols_left0)) ((1 : Fin 2), (0 : Fin 4), (2 : Fin 4)) = (negativeScale (leftScaleExponent 6 3 5) • (left1Middle6 3 5)) ((1 : Fin 2), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal6_case_3_5_row_1_0_3 : (((-1 : ℤ) ^ (leftScaleBit 6 3 5).val * positiveScale (leftScaleExponent 6 3 5)) •
      (rowColumnMul HexagonRowColumn635.rows_assocBCA HexagonRowColumn635.cols_left0)) ((1 : Fin 2), (0 : Fin 4), (3 : Fin 4)) = (negativeScale (leftScaleExponent 6 3 5) • (left1Middle6 3 5)) ((1 : Fin 2), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal6_case_3_5_row_1_1_0 : (((-1 : ℤ) ^ (leftScaleBit 6 3 5).val * positiveScale (leftScaleExponent 6 3 5)) •
      (rowColumnMul HexagonRowColumn635.rows_assocBCA HexagonRowColumn635.cols_left0)) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 4)) = (negativeScale (leftScaleExponent 6 3 5) • (left1Middle6 3 5)) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal6_case_3_5_row_1_1_1 : (((-1 : ℤ) ^ (leftScaleBit 6 3 5).val * positiveScale (leftScaleExponent 6 3 5)) •
      (rowColumnMul HexagonRowColumn635.rows_assocBCA HexagonRowColumn635.cols_left0)) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 4)) = (negativeScale (leftScaleExponent 6 3 5) • (left1Middle6 3 5)) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal6_case_3_5_row_1_1_2 : (((-1 : ℤ) ^ (leftScaleBit 6 3 5).val * positiveScale (leftScaleExponent 6 3 5)) •
      (rowColumnMul HexagonRowColumn635.rows_assocBCA HexagonRowColumn635.cols_left0)) ((1 : Fin 2), (1 : Fin 4), (2 : Fin 4)) = (negativeScale (leftScaleExponent 6 3 5) • (left1Middle6 3 5)) ((1 : Fin 2), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal6_case_3_5_row_1_1_3 : (((-1 : ℤ) ^ (leftScaleBit 6 3 5).val * positiveScale (leftScaleExponent 6 3 5)) •
      (rowColumnMul HexagonRowColumn635.rows_assocBCA HexagonRowColumn635.cols_left0)) ((1 : Fin 2), (1 : Fin 4), (3 : Fin 4)) = (negativeScale (leftScaleExponent 6 3 5) • (left1Middle6 3 5)) ((1 : Fin 2), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal6_case_3_5_row_1_2_0 : (((-1 : ℤ) ^ (leftScaleBit 6 3 5).val * positiveScale (leftScaleExponent 6 3 5)) •
      (rowColumnMul HexagonRowColumn635.rows_assocBCA HexagonRowColumn635.cols_left0)) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 4)) = (negativeScale (leftScaleExponent 6 3 5) • (left1Middle6 3 5)) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal6_case_3_5_row_1_2_1 : (((-1 : ℤ) ^ (leftScaleBit 6 3 5).val * positiveScale (leftScaleExponent 6 3 5)) •
      (rowColumnMul HexagonRowColumn635.rows_assocBCA HexagonRowColumn635.cols_left0)) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 4)) = (negativeScale (leftScaleExponent 6 3 5) • (left1Middle6 3 5)) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal6_case_3_5_row_1_2_2 : (((-1 : ℤ) ^ (leftScaleBit 6 3 5).val * positiveScale (leftScaleExponent 6 3 5)) •
      (rowColumnMul HexagonRowColumn635.rows_assocBCA HexagonRowColumn635.cols_left0)) ((1 : Fin 2), (2 : Fin 4), (2 : Fin 4)) = (negativeScale (leftScaleExponent 6 3 5) • (left1Middle6 3 5)) ((1 : Fin 2), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal6_case_3_5_row_1_2_3 : (((-1 : ℤ) ^ (leftScaleBit 6 3 5).val * positiveScale (leftScaleExponent 6 3 5)) •
      (rowColumnMul HexagonRowColumn635.rows_assocBCA HexagonRowColumn635.cols_left0)) ((1 : Fin 2), (2 : Fin 4), (3 : Fin 4)) = (negativeScale (leftScaleExponent 6 3 5) • (left1Middle6 3 5)) ((1 : Fin 2), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal6_case_3_5_row_1_3_0 : (((-1 : ℤ) ^ (leftScaleBit 6 3 5).val * positiveScale (leftScaleExponent 6 3 5)) •
      (rowColumnMul HexagonRowColumn635.rows_assocBCA HexagonRowColumn635.cols_left0)) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 4)) = (negativeScale (leftScaleExponent 6 3 5) • (left1Middle6 3 5)) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal6_case_3_5_row_1_3_1 : (((-1 : ℤ) ^ (leftScaleBit 6 3 5).val * positiveScale (leftScaleExponent 6 3 5)) •
      (rowColumnMul HexagonRowColumn635.rows_assocBCA HexagonRowColumn635.cols_left0)) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 4)) = (negativeScale (leftScaleExponent 6 3 5) • (left1Middle6 3 5)) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal6_case_3_5_row_1_3_2 : (((-1 : ℤ) ^ (leftScaleBit 6 3 5).val * positiveScale (leftScaleExponent 6 3 5)) •
      (rowColumnMul HexagonRowColumn635.rows_assocBCA HexagonRowColumn635.cols_left0)) ((1 : Fin 2), (3 : Fin 4), (2 : Fin 4)) = (negativeScale (leftScaleExponent 6 3 5) • (left1Middle6 3 5)) ((1 : Fin 2), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal6_case_3_5_row_1_3_3 : (((-1 : ℤ) ^ (leftScaleBit 6 3 5).val * positiveScale (leftScaleExponent 6 3 5)) •
      (rowColumnMul HexagonRowColumn635.rows_assocBCA HexagonRowColumn635.cols_left0)) ((1 : Fin 2), (3 : Fin 4), (3 : Fin 4)) = (negativeScale (leftScaleExponent 6 3 5) • (left1Middle6 3 5)) ((1 : Fin 2), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal6_case_3_5_checked : ((-1 : ℤ) ^ (leftScaleBit 6 3 5).val * positiveScale (leftScaleExponent 6 3 5)) •
      (rowColumnMul HexagonRowColumn635.rows_assocBCA HexagonRowColumn635.cols_left0) = negativeScale (leftScaleExponent 6 3 5) • (left1Middle6 3 5) := by
  funext r
  fin_cases r
  · exact leftFinal6_case_3_5_row_0_0_0
  · exact leftFinal6_case_3_5_row_0_0_1
  · exact leftFinal6_case_3_5_row_0_0_2
  · exact leftFinal6_case_3_5_row_0_0_3
  · exact leftFinal6_case_3_5_row_0_1_0
  · exact leftFinal6_case_3_5_row_0_1_1
  · exact leftFinal6_case_3_5_row_0_1_2
  · exact leftFinal6_case_3_5_row_0_1_3
  · exact leftFinal6_case_3_5_row_0_2_0
  · exact leftFinal6_case_3_5_row_0_2_1
  · exact leftFinal6_case_3_5_row_0_2_2
  · exact leftFinal6_case_3_5_row_0_2_3
  · exact leftFinal6_case_3_5_row_0_3_0
  · exact leftFinal6_case_3_5_row_0_3_1
  · exact leftFinal6_case_3_5_row_0_3_2
  · exact leftFinal6_case_3_5_row_0_3_3
  · exact leftFinal6_case_3_5_row_1_0_0
  · exact leftFinal6_case_3_5_row_1_0_1
  · exact leftFinal6_case_3_5_row_1_0_2
  · exact leftFinal6_case_3_5_row_1_0_3
  · exact leftFinal6_case_3_5_row_1_1_0
  · exact leftFinal6_case_3_5_row_1_1_1
  · exact leftFinal6_case_3_5_row_1_1_2
  · exact leftFinal6_case_3_5_row_1_1_3
  · exact leftFinal6_case_3_5_row_1_2_0
  · exact leftFinal6_case_3_5_row_1_2_1
  · exact leftFinal6_case_3_5_row_1_2_2
  · exact leftFinal6_case_3_5_row_1_2_3
  · exact leftFinal6_case_3_5_row_1_3_0
  · exact leftFinal6_case_3_5_row_1_3_1
  · exact leftFinal6_case_3_5_row_1_3_2
  · exact leftFinal6_case_3_5_row_1_3_3

set_option backward.isDefEq.respectTransparency false in
theorem leftFinal6_case_3_5 : ((-1 : ℤ) ^ (leftScaleBit 6 3 5).val * positiveScale (leftScaleExponent 6 3 5)) •
      (associatorZ 3 5 6 * left0Middle6 3 5) = negativeScale (leftScaleExponent 6 3 5) • (innerRightZ 3 6 5 * left1Middle6 3 5) := by
  simpa only [HexagonAtoms635.assocABC_eq,
    HexagonAtoms635.outerABC_eq,
    HexagonAtoms635.assocBAC_eq,
    HexagonAtoms635.innerABC_eq,
    HexagonAtoms635.innerRightABC_eq,
    HexagonAtoms635.inverseACB_eq,
    HexagonAtoms635.innerACB_eq,
    HexagonAtoms635.assocBCA_eq,
    HexagonAtoms635.innerRightBAC_eq,
    HexagonAtoms635.assocCAB_eq,
    HexagonAtoms635.outerLeftABC_eq,
    HexagonRowColumn635.product0_eq,
    HexagonRowColumn635.product1_eq,
    HexagonRowColumn635.product2_eq,
    HexagonRowColumn635.product3_eq,
    HexagonRowColumn635.product4_eq,
    HexagonRowColumn635.product5_eq,
    HexagonRowColumn635.product6_eq,
    HexagonRowColumn635.product7_eq] using leftFinal6_case_3_5_checked

private theorem rightFinal6_case_3_5_row_0_0_0 : (((-1 : ℤ) ^ (rightScaleBit 6 3 5).val * positiveScale (rightScaleExponent 6 3 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 3 : ℤ)) • HexagonAtoms635.outerLeftABC) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 6 3 5) • (rowColumnMul HexagonRowColumn635.rows_assocCAB HexagonRowColumn635.cols_right2)) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal6_case_3_5_row_0_0_1 : (((-1 : ℤ) ^ (rightScaleBit 6 3 5).val * positiveScale (rightScaleExponent 6 3 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 3 : ℤ)) • HexagonAtoms635.outerLeftABC) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 6 3 5) • (rowColumnMul HexagonRowColumn635.rows_assocCAB HexagonRowColumn635.cols_right2)) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal6_case_3_5_row_0_0_2 : (((-1 : ℤ) ^ (rightScaleBit 6 3 5).val * positiveScale (rightScaleExponent 6 3 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 3 : ℤ)) • HexagonAtoms635.outerLeftABC) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 6 3 5) • (rowColumnMul HexagonRowColumn635.rows_assocCAB HexagonRowColumn635.cols_right2)) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal6_case_3_5_row_0_0_3 : (((-1 : ℤ) ^ (rightScaleBit 6 3 5).val * positiveScale (rightScaleExponent 6 3 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 3 : ℤ)) • HexagonAtoms635.outerLeftABC) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 6 3 5) • (rowColumnMul HexagonRowColumn635.rows_assocCAB HexagonRowColumn635.cols_right2)) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal6_case_3_5_row_0_1_0 : (((-1 : ℤ) ^ (rightScaleBit 6 3 5).val * positiveScale (rightScaleExponent 6 3 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 3 : ℤ)) • HexagonAtoms635.outerLeftABC) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 6 3 5) • (rowColumnMul HexagonRowColumn635.rows_assocCAB HexagonRowColumn635.cols_right2)) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal6_case_3_5_row_0_1_1 : (((-1 : ℤ) ^ (rightScaleBit 6 3 5).val * positiveScale (rightScaleExponent 6 3 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 3 : ℤ)) • HexagonAtoms635.outerLeftABC) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 6 3 5) • (rowColumnMul HexagonRowColumn635.rows_assocCAB HexagonRowColumn635.cols_right2)) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal6_case_3_5_row_0_1_2 : (((-1 : ℤ) ^ (rightScaleBit 6 3 5).val * positiveScale (rightScaleExponent 6 3 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 3 : ℤ)) • HexagonAtoms635.outerLeftABC) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 6 3 5) • (rowColumnMul HexagonRowColumn635.rows_assocCAB HexagonRowColumn635.cols_right2)) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal6_case_3_5_row_0_1_3 : (((-1 : ℤ) ^ (rightScaleBit 6 3 5).val * positiveScale (rightScaleExponent 6 3 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 3 : ℤ)) • HexagonAtoms635.outerLeftABC) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 6 3 5) • (rowColumnMul HexagonRowColumn635.rows_assocCAB HexagonRowColumn635.cols_right2)) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal6_case_3_5_row_1_0_0 : (((-1 : ℤ) ^ (rightScaleBit 6 3 5).val * positiveScale (rightScaleExponent 6 3 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 3 : ℤ)) • HexagonAtoms635.outerLeftABC) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 6 3 5) • (rowColumnMul HexagonRowColumn635.rows_assocCAB HexagonRowColumn635.cols_right2)) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal6_case_3_5_row_1_0_1 : (((-1 : ℤ) ^ (rightScaleBit 6 3 5).val * positiveScale (rightScaleExponent 6 3 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 3 : ℤ)) • HexagonAtoms635.outerLeftABC) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 6 3 5) • (rowColumnMul HexagonRowColumn635.rows_assocCAB HexagonRowColumn635.cols_right2)) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal6_case_3_5_row_1_0_2 : (((-1 : ℤ) ^ (rightScaleBit 6 3 5).val * positiveScale (rightScaleExponent 6 3 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 3 : ℤ)) • HexagonAtoms635.outerLeftABC) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 6 3 5) • (rowColumnMul HexagonRowColumn635.rows_assocCAB HexagonRowColumn635.cols_right2)) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal6_case_3_5_row_1_0_3 : (((-1 : ℤ) ^ (rightScaleBit 6 3 5).val * positiveScale (rightScaleExponent 6 3 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 3 : ℤ)) • HexagonAtoms635.outerLeftABC) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 6 3 5) • (rowColumnMul HexagonRowColumn635.rows_assocCAB HexagonRowColumn635.cols_right2)) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal6_case_3_5_row_1_1_0 : (((-1 : ℤ) ^ (rightScaleBit 6 3 5).val * positiveScale (rightScaleExponent 6 3 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 3 : ℤ)) • HexagonAtoms635.outerLeftABC) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 6 3 5) • (rowColumnMul HexagonRowColumn635.rows_assocCAB HexagonRowColumn635.cols_right2)) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal6_case_3_5_row_1_1_1 : (((-1 : ℤ) ^ (rightScaleBit 6 3 5).val * positiveScale (rightScaleExponent 6 3 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 3 : ℤ)) • HexagonAtoms635.outerLeftABC) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 6 3 5) • (rowColumnMul HexagonRowColumn635.rows_assocCAB HexagonRowColumn635.cols_right2)) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal6_case_3_5_row_1_1_2 : (((-1 : ℤ) ^ (rightScaleBit 6 3 5).val * positiveScale (rightScaleExponent 6 3 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 3 : ℤ)) • HexagonAtoms635.outerLeftABC) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 6 3 5) • (rowColumnMul HexagonRowColumn635.rows_assocCAB HexagonRowColumn635.cols_right2)) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal6_case_3_5_row_1_1_3 : (((-1 : ℤ) ^ (rightScaleBit 6 3 5).val * positiveScale (rightScaleExponent 6 3 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 3 : ℤ)) • HexagonAtoms635.outerLeftABC) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 6 3 5) • (rowColumnMul HexagonRowColumn635.rows_assocCAB HexagonRowColumn635.cols_right2)) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal6_case_3_5_row_2_0_0 : (((-1 : ℤ) ^ (rightScaleBit 6 3 5).val * positiveScale (rightScaleExponent 6 3 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 3 : ℤ)) • HexagonAtoms635.outerLeftABC) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 6 3 5) • (rowColumnMul HexagonRowColumn635.rows_assocCAB HexagonRowColumn635.cols_right2)) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal6_case_3_5_row_2_0_1 : (((-1 : ℤ) ^ (rightScaleBit 6 3 5).val * positiveScale (rightScaleExponent 6 3 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 3 : ℤ)) • HexagonAtoms635.outerLeftABC) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 6 3 5) • (rowColumnMul HexagonRowColumn635.rows_assocCAB HexagonRowColumn635.cols_right2)) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal6_case_3_5_row_2_0_2 : (((-1 : ℤ) ^ (rightScaleBit 6 3 5).val * positiveScale (rightScaleExponent 6 3 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 3 : ℤ)) • HexagonAtoms635.outerLeftABC) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 6 3 5) • (rowColumnMul HexagonRowColumn635.rows_assocCAB HexagonRowColumn635.cols_right2)) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal6_case_3_5_row_2_0_3 : (((-1 : ℤ) ^ (rightScaleBit 6 3 5).val * positiveScale (rightScaleExponent 6 3 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 3 : ℤ)) • HexagonAtoms635.outerLeftABC) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 6 3 5) • (rowColumnMul HexagonRowColumn635.rows_assocCAB HexagonRowColumn635.cols_right2)) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal6_case_3_5_row_2_1_0 : (((-1 : ℤ) ^ (rightScaleBit 6 3 5).val * positiveScale (rightScaleExponent 6 3 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 3 : ℤ)) • HexagonAtoms635.outerLeftABC) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 6 3 5) • (rowColumnMul HexagonRowColumn635.rows_assocCAB HexagonRowColumn635.cols_right2)) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal6_case_3_5_row_2_1_1 : (((-1 : ℤ) ^ (rightScaleBit 6 3 5).val * positiveScale (rightScaleExponent 6 3 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 3 : ℤ)) • HexagonAtoms635.outerLeftABC) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 6 3 5) • (rowColumnMul HexagonRowColumn635.rows_assocCAB HexagonRowColumn635.cols_right2)) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal6_case_3_5_row_2_1_2 : (((-1 : ℤ) ^ (rightScaleBit 6 3 5).val * positiveScale (rightScaleExponent 6 3 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 3 : ℤ)) • HexagonAtoms635.outerLeftABC) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 6 3 5) • (rowColumnMul HexagonRowColumn635.rows_assocCAB HexagonRowColumn635.cols_right2)) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal6_case_3_5_row_2_1_3 : (((-1 : ℤ) ^ (rightScaleBit 6 3 5).val * positiveScale (rightScaleExponent 6 3 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 3 : ℤ)) • HexagonAtoms635.outerLeftABC) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 6 3 5) • (rowColumnMul HexagonRowColumn635.rows_assocCAB HexagonRowColumn635.cols_right2)) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal6_case_3_5_row_3_0_0 : (((-1 : ℤ) ^ (rightScaleBit 6 3 5).val * positiveScale (rightScaleExponent 6 3 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 3 : ℤ)) • HexagonAtoms635.outerLeftABC) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 6 3 5) • (rowColumnMul HexagonRowColumn635.rows_assocCAB HexagonRowColumn635.cols_right2)) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal6_case_3_5_row_3_0_1 : (((-1 : ℤ) ^ (rightScaleBit 6 3 5).val * positiveScale (rightScaleExponent 6 3 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 3 : ℤ)) • HexagonAtoms635.outerLeftABC) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 6 3 5) • (rowColumnMul HexagonRowColumn635.rows_assocCAB HexagonRowColumn635.cols_right2)) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal6_case_3_5_row_3_0_2 : (((-1 : ℤ) ^ (rightScaleBit 6 3 5).val * positiveScale (rightScaleExponent 6 3 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 3 : ℤ)) • HexagonAtoms635.outerLeftABC) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 6 3 5) • (rowColumnMul HexagonRowColumn635.rows_assocCAB HexagonRowColumn635.cols_right2)) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal6_case_3_5_row_3_0_3 : (((-1 : ℤ) ^ (rightScaleBit 6 3 5).val * positiveScale (rightScaleExponent 6 3 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 3 : ℤ)) • HexagonAtoms635.outerLeftABC) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 6 3 5) • (rowColumnMul HexagonRowColumn635.rows_assocCAB HexagonRowColumn635.cols_right2)) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal6_case_3_5_row_3_1_0 : (((-1 : ℤ) ^ (rightScaleBit 6 3 5).val * positiveScale (rightScaleExponent 6 3 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 3 : ℤ)) • HexagonAtoms635.outerLeftABC) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 6 3 5) • (rowColumnMul HexagonRowColumn635.rows_assocCAB HexagonRowColumn635.cols_right2)) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal6_case_3_5_row_3_1_1 : (((-1 : ℤ) ^ (rightScaleBit 6 3 5).val * positiveScale (rightScaleExponent 6 3 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 3 : ℤ)) • HexagonAtoms635.outerLeftABC) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 6 3 5) • (rowColumnMul HexagonRowColumn635.rows_assocCAB HexagonRowColumn635.cols_right2)) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal6_case_3_5_row_3_1_2 : (((-1 : ℤ) ^ (rightScaleBit 6 3 5).val * positiveScale (rightScaleExponent 6 3 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 3 : ℤ)) • HexagonAtoms635.outerLeftABC) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 6 3 5) • (rowColumnMul HexagonRowColumn635.rows_assocCAB HexagonRowColumn635.cols_right2)) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal6_case_3_5_row_3_1_3 : (((-1 : ℤ) ^ (rightScaleBit 6 3 5).val * positiveScale (rightScaleExponent 6 3 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 3 : ℤ)) • HexagonAtoms635.outerLeftABC) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 6 3 5) • (rowColumnMul HexagonRowColumn635.rows_assocCAB HexagonRowColumn635.cols_right2)) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal6_case_3_5_checked : ((-1 : ℤ) ^ (rightScaleBit 6 3 5).val * positiveScale (rightScaleExponent 6 3 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 3 : ℤ)) • HexagonAtoms635.outerLeftABC = negativeScale (rightScaleExponent 6 3 5) • (rowColumnMul HexagonRowColumn635.rows_assocCAB HexagonRowColumn635.cols_right2) := by
  funext r
  fin_cases r
  · exact rightFinal6_case_3_5_row_0_0_0
  · exact rightFinal6_case_3_5_row_0_0_1
  · exact rightFinal6_case_3_5_row_0_0_2
  · exact rightFinal6_case_3_5_row_0_0_3
  · exact rightFinal6_case_3_5_row_0_1_0
  · exact rightFinal6_case_3_5_row_0_1_1
  · exact rightFinal6_case_3_5_row_0_1_2
  · exact rightFinal6_case_3_5_row_0_1_3
  · exact rightFinal6_case_3_5_row_1_0_0
  · exact rightFinal6_case_3_5_row_1_0_1
  · exact rightFinal6_case_3_5_row_1_0_2
  · exact rightFinal6_case_3_5_row_1_0_3
  · exact rightFinal6_case_3_5_row_1_1_0
  · exact rightFinal6_case_3_5_row_1_1_1
  · exact rightFinal6_case_3_5_row_1_1_2
  · exact rightFinal6_case_3_5_row_1_1_3
  · exact rightFinal6_case_3_5_row_2_0_0
  · exact rightFinal6_case_3_5_row_2_0_1
  · exact rightFinal6_case_3_5_row_2_0_2
  · exact rightFinal6_case_3_5_row_2_0_3
  · exact rightFinal6_case_3_5_row_2_1_0
  · exact rightFinal6_case_3_5_row_2_1_1
  · exact rightFinal6_case_3_5_row_2_1_2
  · exact rightFinal6_case_3_5_row_2_1_3
  · exact rightFinal6_case_3_5_row_3_0_0
  · exact rightFinal6_case_3_5_row_3_0_1
  · exact rightFinal6_case_3_5_row_3_0_2
  · exact rightFinal6_case_3_5_row_3_0_3
  · exact rightFinal6_case_3_5_row_3_1_0
  · exact rightFinal6_case_3_5_row_3_1_1
  · exact rightFinal6_case_3_5_row_3_1_2
  · exact rightFinal6_case_3_5_row_3_1_3

set_option backward.isDefEq.respectTransparency false in
theorem rightFinal6_case_3_5 : ((-1 : ℤ) ^ (rightScaleBit 6 3 5).val * positiveScale (rightScaleExponent 6 3 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 3 : ℤ)) • outerLeftZ 6 3 5 = negativeScale (rightScaleExponent 6 3 5) • (associatorZ 5 6 3 * right2Middle6 3 5) := by
  simpa only [HexagonAtoms635.assocABC_eq,
    HexagonAtoms635.outerABC_eq,
    HexagonAtoms635.assocBAC_eq,
    HexagonAtoms635.innerABC_eq,
    HexagonAtoms635.innerRightABC_eq,
    HexagonAtoms635.inverseACB_eq,
    HexagonAtoms635.innerACB_eq,
    HexagonAtoms635.assocBCA_eq,
    HexagonAtoms635.innerRightBAC_eq,
    HexagonAtoms635.assocCAB_eq,
    HexagonAtoms635.outerLeftABC_eq,
    HexagonRowColumn635.product0_eq,
    HexagonRowColumn635.product1_eq,
    HexagonRowColumn635.product2_eq,
    HexagonRowColumn635.product3_eq,
    HexagonRowColumn635.product4_eq,
    HexagonRowColumn635.product5_eq,
    HexagonRowColumn635.product6_eq,
    HexagonRowColumn635.product7_eq] using rightFinal6_case_3_5_checked

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonCases6
