import RMod.BrundanEllis.StackingReferenceHexagonMiddle6
import RMod.BrundanEllis.StackingReferenceSparseMatrixCheck
import RMod.BrundanEllis.StackingReferenceHexagonAtoms653
import RMod.BrundanEllis.StackingReferenceHexagonRowColumn653

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

private theorem left0Middle6_eq_case_5_3_row_0_0_0 : (left0Middle6 5 3) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms653.assocABC) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_5_3_row_0_0_1 : (left0Middle6 5 3) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms653.assocABC) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_5_3_row_0_0_2 : (left0Middle6 5 3) ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms653.assocABC) ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_5_3_row_0_0_3 : (left0Middle6 5 3) ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms653.assocABC) ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_5_3_row_1_0_0 : (left0Middle6 5 3) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms653.assocABC) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_5_3_row_1_0_1 : (left0Middle6 5 3) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms653.assocABC) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_5_3_row_1_0_2 : (left0Middle6 5 3) ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms653.assocABC) ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_5_3_row_1_0_3 : (left0Middle6 5 3) ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms653.assocABC) ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_5_3_row_2_0_0 : (left0Middle6 5 3) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms653.assocABC) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_5_3_row_2_0_1 : (left0Middle6 5 3) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms653.assocABC) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_5_3_row_2_0_2 : (left0Middle6 5 3) ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms653.assocABC) ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_5_3_row_2_0_3 : (left0Middle6 5 3) ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms653.assocABC) ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_5_3_row_3_0_0 : (left0Middle6 5 3) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms653.assocABC) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_5_3_row_3_0_1 : (left0Middle6 5 3) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms653.assocABC) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_5_3_row_3_0_2 : (left0Middle6 5 3) ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms653.assocABC) ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_5_3_row_3_0_3 : (left0Middle6 5 3) ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms653.assocABC) ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_5_3_row_4_0_0 : (left0Middle6 5 3) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms653.assocABC) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_5_3_row_4_0_1 : (left0Middle6 5 3) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms653.assocABC) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_5_3_row_4_0_2 : (left0Middle6 5 3) ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms653.assocABC) ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_5_3_row_4_0_3 : (left0Middle6 5 3) ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms653.assocABC) ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_5_3_row_5_0_0 : (left0Middle6 5 3) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms653.assocABC) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_5_3_row_5_0_1 : (left0Middle6 5 3) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms653.assocABC) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_5_3_row_5_0_2 : (left0Middle6 5 3) ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms653.assocABC) ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_5_3_row_5_0_3 : (left0Middle6 5 3) ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms653.assocABC) ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_5_3_row_6_0_0 : (left0Middle6 5 3) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms653.assocABC) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_5_3_row_6_0_1 : (left0Middle6 5 3) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms653.assocABC) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_5_3_row_6_0_2 : (left0Middle6 5 3) ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms653.assocABC) ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_5_3_row_6_0_3 : (left0Middle6 5 3) ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms653.assocABC) ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_5_3_row_7_0_0 : (left0Middle6 5 3) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms653.assocABC) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_5_3_row_7_0_1 : (left0Middle6 5 3) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms653.assocABC) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_5_3_row_7_0_2 : (left0Middle6 5 3) ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms653.assocABC) ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_5_3_row_7_0_3 : (left0Middle6 5 3) ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms653.assocABC) ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_5_3_checked : left0Middle6 5 3 = HexagonAtoms653.assocABC := by
  funext r
  fin_cases r
  · exact left0Middle6_eq_case_5_3_row_0_0_0
  · exact left0Middle6_eq_case_5_3_row_0_0_1
  · exact left0Middle6_eq_case_5_3_row_0_0_2
  · exact left0Middle6_eq_case_5_3_row_0_0_3
  · exact left0Middle6_eq_case_5_3_row_1_0_0
  · exact left0Middle6_eq_case_5_3_row_1_0_1
  · exact left0Middle6_eq_case_5_3_row_1_0_2
  · exact left0Middle6_eq_case_5_3_row_1_0_3
  · exact left0Middle6_eq_case_5_3_row_2_0_0
  · exact left0Middle6_eq_case_5_3_row_2_0_1
  · exact left0Middle6_eq_case_5_3_row_2_0_2
  · exact left0Middle6_eq_case_5_3_row_2_0_3
  · exact left0Middle6_eq_case_5_3_row_3_0_0
  · exact left0Middle6_eq_case_5_3_row_3_0_1
  · exact left0Middle6_eq_case_5_3_row_3_0_2
  · exact left0Middle6_eq_case_5_3_row_3_0_3
  · exact left0Middle6_eq_case_5_3_row_4_0_0
  · exact left0Middle6_eq_case_5_3_row_4_0_1
  · exact left0Middle6_eq_case_5_3_row_4_0_2
  · exact left0Middle6_eq_case_5_3_row_4_0_3
  · exact left0Middle6_eq_case_5_3_row_5_0_0
  · exact left0Middle6_eq_case_5_3_row_5_0_1
  · exact left0Middle6_eq_case_5_3_row_5_0_2
  · exact left0Middle6_eq_case_5_3_row_5_0_3
  · exact left0Middle6_eq_case_5_3_row_6_0_0
  · exact left0Middle6_eq_case_5_3_row_6_0_1
  · exact left0Middle6_eq_case_5_3_row_6_0_2
  · exact left0Middle6_eq_case_5_3_row_6_0_3
  · exact left0Middle6_eq_case_5_3_row_7_0_0
  · exact left0Middle6_eq_case_5_3_row_7_0_1
  · exact left0Middle6_eq_case_5_3_row_7_0_2
  · exact left0Middle6_eq_case_5_3_row_7_0_3

set_option backward.isDefEq.respectTransparency false in
theorem left0Middle6_eq_case_5_3 : left0Middle6 5 3 = outerRightZ 6 5 3 * associatorZ 6 5 3 := by
  simpa only [HexagonAtoms653.assocABC_eq,
    HexagonAtoms653.outerABC_eq,
    HexagonAtoms653.assocBAC_eq,
    HexagonAtoms653.innerABC_eq,
    HexagonAtoms653.innerRightABC_eq,
    HexagonAtoms653.inverseACB_eq,
    HexagonAtoms653.innerACB_eq,
    HexagonAtoms653.assocBCA_eq,
    HexagonAtoms653.innerRightBAC_eq,
    HexagonAtoms653.assocCAB_eq,
    HexagonAtoms653.outerLeftABC_eq,
    HexagonRowColumn653.product0_eq,
    HexagonRowColumn653.product1_eq,
    HexagonRowColumn653.product2_eq,
    HexagonRowColumn653.product3_eq,
    HexagonRowColumn653.product4_eq,
    HexagonRowColumn653.product5_eq,
    HexagonRowColumn653.product6_eq,
    HexagonRowColumn653.product7_eq] using left0Middle6_eq_case_5_3_checked

private theorem left1Middle6_eq_case_5_3_row_0_0_0 : (left1Middle6 5 3) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms653.assocBAC) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_5_3_row_0_0_1 : (left1Middle6 5 3) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms653.assocBAC) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_5_3_row_0_0_2 : (left1Middle6 5 3) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms653.assocBAC) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_5_3_row_0_0_3 : (left1Middle6 5 3) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms653.assocBAC) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_5_3_row_0_1_0 : (left1Middle6 5 3) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms653.assocBAC) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_5_3_row_0_1_1 : (left1Middle6 5 3) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms653.assocBAC) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_5_3_row_0_1_2 : (left1Middle6 5 3) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms653.assocBAC) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_5_3_row_0_1_3 : (left1Middle6 5 3) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms653.assocBAC) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_5_3_row_1_0_0 : (left1Middle6 5 3) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms653.assocBAC) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_5_3_row_1_0_1 : (left1Middle6 5 3) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms653.assocBAC) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_5_3_row_1_0_2 : (left1Middle6 5 3) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms653.assocBAC) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_5_3_row_1_0_3 : (left1Middle6 5 3) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms653.assocBAC) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_5_3_row_1_1_0 : (left1Middle6 5 3) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms653.assocBAC) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_5_3_row_1_1_1 : (left1Middle6 5 3) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms653.assocBAC) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_5_3_row_1_1_2 : (left1Middle6 5 3) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms653.assocBAC) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_5_3_row_1_1_3 : (left1Middle6 5 3) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms653.assocBAC) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_5_3_row_2_0_0 : (left1Middle6 5 3) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms653.assocBAC) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_5_3_row_2_0_1 : (left1Middle6 5 3) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms653.assocBAC) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_5_3_row_2_0_2 : (left1Middle6 5 3) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms653.assocBAC) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_5_3_row_2_0_3 : (left1Middle6 5 3) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms653.assocBAC) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_5_3_row_2_1_0 : (left1Middle6 5 3) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms653.assocBAC) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_5_3_row_2_1_1 : (left1Middle6 5 3) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms653.assocBAC) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_5_3_row_2_1_2 : (left1Middle6 5 3) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms653.assocBAC) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_5_3_row_2_1_3 : (left1Middle6 5 3) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms653.assocBAC) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_5_3_row_3_0_0 : (left1Middle6 5 3) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms653.assocBAC) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_5_3_row_3_0_1 : (left1Middle6 5 3) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms653.assocBAC) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_5_3_row_3_0_2 : (left1Middle6 5 3) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms653.assocBAC) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_5_3_row_3_0_3 : (left1Middle6 5 3) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms653.assocBAC) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_5_3_row_3_1_0 : (left1Middle6 5 3) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms653.assocBAC) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_5_3_row_3_1_1 : (left1Middle6 5 3) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms653.assocBAC) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_5_3_row_3_1_2 : (left1Middle6 5 3) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms653.assocBAC) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_5_3_row_3_1_3 : (left1Middle6 5 3) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms653.assocBAC) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_5_3_checked : left1Middle6 5 3 = HexagonAtoms653.assocBAC := by
  funext r
  fin_cases r
  · exact left1Middle6_eq_case_5_3_row_0_0_0
  · exact left1Middle6_eq_case_5_3_row_0_0_1
  · exact left1Middle6_eq_case_5_3_row_0_0_2
  · exact left1Middle6_eq_case_5_3_row_0_0_3
  · exact left1Middle6_eq_case_5_3_row_0_1_0
  · exact left1Middle6_eq_case_5_3_row_0_1_1
  · exact left1Middle6_eq_case_5_3_row_0_1_2
  · exact left1Middle6_eq_case_5_3_row_0_1_3
  · exact left1Middle6_eq_case_5_3_row_1_0_0
  · exact left1Middle6_eq_case_5_3_row_1_0_1
  · exact left1Middle6_eq_case_5_3_row_1_0_2
  · exact left1Middle6_eq_case_5_3_row_1_0_3
  · exact left1Middle6_eq_case_5_3_row_1_1_0
  · exact left1Middle6_eq_case_5_3_row_1_1_1
  · exact left1Middle6_eq_case_5_3_row_1_1_2
  · exact left1Middle6_eq_case_5_3_row_1_1_3
  · exact left1Middle6_eq_case_5_3_row_2_0_0
  · exact left1Middle6_eq_case_5_3_row_2_0_1
  · exact left1Middle6_eq_case_5_3_row_2_0_2
  · exact left1Middle6_eq_case_5_3_row_2_0_3
  · exact left1Middle6_eq_case_5_3_row_2_1_0
  · exact left1Middle6_eq_case_5_3_row_2_1_1
  · exact left1Middle6_eq_case_5_3_row_2_1_2
  · exact left1Middle6_eq_case_5_3_row_2_1_3
  · exact left1Middle6_eq_case_5_3_row_3_0_0
  · exact left1Middle6_eq_case_5_3_row_3_0_1
  · exact left1Middle6_eq_case_5_3_row_3_0_2
  · exact left1Middle6_eq_case_5_3_row_3_0_3
  · exact left1Middle6_eq_case_5_3_row_3_1_0
  · exact left1Middle6_eq_case_5_3_row_3_1_1
  · exact left1Middle6_eq_case_5_3_row_3_1_2
  · exact left1Middle6_eq_case_5_3_row_3_1_3

set_option backward.isDefEq.respectTransparency false in
theorem left1Middle6_eq_case_5_3 : left1Middle6 5 3 = associatorZ 5 6 3 * innerLeftZ 6 5 3 := by
  simpa only [HexagonAtoms653.assocABC_eq,
    HexagonAtoms653.outerABC_eq,
    HexagonAtoms653.assocBAC_eq,
    HexagonAtoms653.innerABC_eq,
    HexagonAtoms653.innerRightABC_eq,
    HexagonAtoms653.inverseACB_eq,
    HexagonAtoms653.innerACB_eq,
    HexagonAtoms653.assocBCA_eq,
    HexagonAtoms653.innerRightBAC_eq,
    HexagonAtoms653.assocCAB_eq,
    HexagonAtoms653.outerLeftABC_eq,
    HexagonRowColumn653.product0_eq,
    HexagonRowColumn653.product1_eq,
    HexagonRowColumn653.product2_eq,
    HexagonRowColumn653.product3_eq,
    HexagonRowColumn653.product4_eq,
    HexagonRowColumn653.product5_eq,
    HexagonRowColumn653.product6_eq,
    HexagonRowColumn653.product7_eq] using left1Middle6_eq_case_5_3_checked

private theorem right0Middle6_eq_case_5_3_row_0_0_0 : (right0Middle6 5 3) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms653.assocABC) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_5_3_row_0_0_1 : (right0Middle6 5 3) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms653.assocABC) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_5_3_row_0_0_2 : (right0Middle6 5 3) ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms653.assocABC) ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_5_3_row_0_0_3 : (right0Middle6 5 3) ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms653.assocABC) ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_5_3_row_1_0_0 : (right0Middle6 5 3) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms653.assocABC) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_5_3_row_1_0_1 : (right0Middle6 5 3) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms653.assocABC) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_5_3_row_1_0_2 : (right0Middle6 5 3) ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms653.assocABC) ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_5_3_row_1_0_3 : (right0Middle6 5 3) ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms653.assocABC) ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_5_3_row_2_0_0 : (right0Middle6 5 3) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms653.assocABC) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_5_3_row_2_0_1 : (right0Middle6 5 3) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms653.assocABC) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_5_3_row_2_0_2 : (right0Middle6 5 3) ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms653.assocABC) ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_5_3_row_2_0_3 : (right0Middle6 5 3) ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms653.assocABC) ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_5_3_row_3_0_0 : (right0Middle6 5 3) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms653.assocABC) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_5_3_row_3_0_1 : (right0Middle6 5 3) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms653.assocABC) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_5_3_row_3_0_2 : (right0Middle6 5 3) ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms653.assocABC) ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_5_3_row_3_0_3 : (right0Middle6 5 3) ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms653.assocABC) ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_5_3_row_4_0_0 : (right0Middle6 5 3) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms653.assocABC) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_5_3_row_4_0_1 : (right0Middle6 5 3) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms653.assocABC) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_5_3_row_4_0_2 : (right0Middle6 5 3) ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms653.assocABC) ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_5_3_row_4_0_3 : (right0Middle6 5 3) ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms653.assocABC) ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_5_3_row_5_0_0 : (right0Middle6 5 3) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms653.assocABC) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_5_3_row_5_0_1 : (right0Middle6 5 3) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms653.assocABC) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_5_3_row_5_0_2 : (right0Middle6 5 3) ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms653.assocABC) ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_5_3_row_5_0_3 : (right0Middle6 5 3) ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms653.assocABC) ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_5_3_row_6_0_0 : (right0Middle6 5 3) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms653.assocABC) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_5_3_row_6_0_1 : (right0Middle6 5 3) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms653.assocABC) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_5_3_row_6_0_2 : (right0Middle6 5 3) ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms653.assocABC) ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_5_3_row_6_0_3 : (right0Middle6 5 3) ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms653.assocABC) ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_5_3_row_7_0_0 : (right0Middle6 5 3) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms653.assocABC) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_5_3_row_7_0_1 : (right0Middle6 5 3) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms653.assocABC) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_5_3_row_7_0_2 : (right0Middle6 5 3) ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms653.assocABC) ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_5_3_row_7_0_3 : (right0Middle6 5 3) ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms653.assocABC) ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_5_3_checked : right0Middle6 5 3 = HexagonAtoms653.assocABC := by
  funext r
  fin_cases r
  · exact right0Middle6_eq_case_5_3_row_0_0_0
  · exact right0Middle6_eq_case_5_3_row_0_0_1
  · exact right0Middle6_eq_case_5_3_row_0_0_2
  · exact right0Middle6_eq_case_5_3_row_0_0_3
  · exact right0Middle6_eq_case_5_3_row_1_0_0
  · exact right0Middle6_eq_case_5_3_row_1_0_1
  · exact right0Middle6_eq_case_5_3_row_1_0_2
  · exact right0Middle6_eq_case_5_3_row_1_0_3
  · exact right0Middle6_eq_case_5_3_row_2_0_0
  · exact right0Middle6_eq_case_5_3_row_2_0_1
  · exact right0Middle6_eq_case_5_3_row_2_0_2
  · exact right0Middle6_eq_case_5_3_row_2_0_3
  · exact right0Middle6_eq_case_5_3_row_3_0_0
  · exact right0Middle6_eq_case_5_3_row_3_0_1
  · exact right0Middle6_eq_case_5_3_row_3_0_2
  · exact right0Middle6_eq_case_5_3_row_3_0_3
  · exact right0Middle6_eq_case_5_3_row_4_0_0
  · exact right0Middle6_eq_case_5_3_row_4_0_1
  · exact right0Middle6_eq_case_5_3_row_4_0_2
  · exact right0Middle6_eq_case_5_3_row_4_0_3
  · exact right0Middle6_eq_case_5_3_row_5_0_0
  · exact right0Middle6_eq_case_5_3_row_5_0_1
  · exact right0Middle6_eq_case_5_3_row_5_0_2
  · exact right0Middle6_eq_case_5_3_row_5_0_3
  · exact right0Middle6_eq_case_5_3_row_6_0_0
  · exact right0Middle6_eq_case_5_3_row_6_0_1
  · exact right0Middle6_eq_case_5_3_row_6_0_2
  · exact right0Middle6_eq_case_5_3_row_6_0_3
  · exact right0Middle6_eq_case_5_3_row_7_0_0
  · exact right0Middle6_eq_case_5_3_row_7_0_1
  · exact right0Middle6_eq_case_5_3_row_7_0_2
  · exact right0Middle6_eq_case_5_3_row_7_0_3

set_option backward.isDefEq.respectTransparency false in
theorem right0Middle6_eq_case_5_3 : right0Middle6 5 3 = innerRightZ 6 5 3 * associatorZ 6 5 3 := by
  simpa only [HexagonAtoms653.assocABC_eq,
    HexagonAtoms653.outerABC_eq,
    HexagonAtoms653.assocBAC_eq,
    HexagonAtoms653.innerABC_eq,
    HexagonAtoms653.innerRightABC_eq,
    HexagonAtoms653.inverseACB_eq,
    HexagonAtoms653.innerACB_eq,
    HexagonAtoms653.assocBCA_eq,
    HexagonAtoms653.innerRightBAC_eq,
    HexagonAtoms653.assocCAB_eq,
    HexagonAtoms653.outerLeftABC_eq,
    HexagonRowColumn653.product0_eq,
    HexagonRowColumn653.product1_eq,
    HexagonRowColumn653.product2_eq,
    HexagonRowColumn653.product3_eq,
    HexagonRowColumn653.product4_eq,
    HexagonRowColumn653.product5_eq,
    HexagonRowColumn653.product6_eq,
    HexagonRowColumn653.product7_eq] using right0Middle6_eq_case_5_3_checked

private theorem right1Middle6_eq_case_5_3_row_0_0_0 : (right1Middle6 5 3) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn653.rows_inverseACB HexagonRowColumn653.cols_right0) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_5_3_row_0_0_1 : (right1Middle6 5 3) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn653.rows_inverseACB HexagonRowColumn653.cols_right0) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_5_3_row_0_0_2 : (right1Middle6 5 3) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn653.rows_inverseACB HexagonRowColumn653.cols_right0) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_5_3_row_0_0_3 : (right1Middle6 5 3) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn653.rows_inverseACB HexagonRowColumn653.cols_right0) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_5_3_row_0_1_0 : (right1Middle6 5 3) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn653.rows_inverseACB HexagonRowColumn653.cols_right0) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_5_3_row_0_1_1 : (right1Middle6 5 3) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn653.rows_inverseACB HexagonRowColumn653.cols_right0) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_5_3_row_0_1_2 : (right1Middle6 5 3) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn653.rows_inverseACB HexagonRowColumn653.cols_right0) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_5_3_row_0_1_3 : (right1Middle6 5 3) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn653.rows_inverseACB HexagonRowColumn653.cols_right0) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_5_3_row_1_0_0 : (right1Middle6 5 3) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn653.rows_inverseACB HexagonRowColumn653.cols_right0) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_5_3_row_1_0_1 : (right1Middle6 5 3) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn653.rows_inverseACB HexagonRowColumn653.cols_right0) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_5_3_row_1_0_2 : (right1Middle6 5 3) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn653.rows_inverseACB HexagonRowColumn653.cols_right0) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_5_3_row_1_0_3 : (right1Middle6 5 3) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn653.rows_inverseACB HexagonRowColumn653.cols_right0) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_5_3_row_1_1_0 : (right1Middle6 5 3) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn653.rows_inverseACB HexagonRowColumn653.cols_right0) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_5_3_row_1_1_1 : (right1Middle6 5 3) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn653.rows_inverseACB HexagonRowColumn653.cols_right0) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_5_3_row_1_1_2 : (right1Middle6 5 3) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn653.rows_inverseACB HexagonRowColumn653.cols_right0) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_5_3_row_1_1_3 : (right1Middle6 5 3) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn653.rows_inverseACB HexagonRowColumn653.cols_right0) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_5_3_row_2_0_0 : (right1Middle6 5 3) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn653.rows_inverseACB HexagonRowColumn653.cols_right0) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_5_3_row_2_0_1 : (right1Middle6 5 3) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn653.rows_inverseACB HexagonRowColumn653.cols_right0) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_5_3_row_2_0_2 : (right1Middle6 5 3) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn653.rows_inverseACB HexagonRowColumn653.cols_right0) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_5_3_row_2_0_3 : (right1Middle6 5 3) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn653.rows_inverseACB HexagonRowColumn653.cols_right0) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_5_3_row_2_1_0 : (right1Middle6 5 3) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn653.rows_inverseACB HexagonRowColumn653.cols_right0) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_5_3_row_2_1_1 : (right1Middle6 5 3) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn653.rows_inverseACB HexagonRowColumn653.cols_right0) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_5_3_row_2_1_2 : (right1Middle6 5 3) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn653.rows_inverseACB HexagonRowColumn653.cols_right0) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_5_3_row_2_1_3 : (right1Middle6 5 3) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn653.rows_inverseACB HexagonRowColumn653.cols_right0) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_5_3_row_3_0_0 : (right1Middle6 5 3) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn653.rows_inverseACB HexagonRowColumn653.cols_right0) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_5_3_row_3_0_1 : (right1Middle6 5 3) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn653.rows_inverseACB HexagonRowColumn653.cols_right0) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_5_3_row_3_0_2 : (right1Middle6 5 3) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn653.rows_inverseACB HexagonRowColumn653.cols_right0) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_5_3_row_3_0_3 : (right1Middle6 5 3) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn653.rows_inverseACB HexagonRowColumn653.cols_right0) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_5_3_row_3_1_0 : (right1Middle6 5 3) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn653.rows_inverseACB HexagonRowColumn653.cols_right0) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_5_3_row_3_1_1 : (right1Middle6 5 3) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn653.rows_inverseACB HexagonRowColumn653.cols_right0) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_5_3_row_3_1_2 : (right1Middle6 5 3) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn653.rows_inverseACB HexagonRowColumn653.cols_right0) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_5_3_row_3_1_3 : (right1Middle6 5 3) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn653.rows_inverseACB HexagonRowColumn653.cols_right0) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_5_3_checked : right1Middle6 5 3 = rowColumnMul HexagonRowColumn653.rows_inverseACB HexagonRowColumn653.cols_right0 := by
  funext r
  fin_cases r
  · exact right1Middle6_eq_case_5_3_row_0_0_0
  · exact right1Middle6_eq_case_5_3_row_0_0_1
  · exact right1Middle6_eq_case_5_3_row_0_0_2
  · exact right1Middle6_eq_case_5_3_row_0_0_3
  · exact right1Middle6_eq_case_5_3_row_0_1_0
  · exact right1Middle6_eq_case_5_3_row_0_1_1
  · exact right1Middle6_eq_case_5_3_row_0_1_2
  · exact right1Middle6_eq_case_5_3_row_0_1_3
  · exact right1Middle6_eq_case_5_3_row_1_0_0
  · exact right1Middle6_eq_case_5_3_row_1_0_1
  · exact right1Middle6_eq_case_5_3_row_1_0_2
  · exact right1Middle6_eq_case_5_3_row_1_0_3
  · exact right1Middle6_eq_case_5_3_row_1_1_0
  · exact right1Middle6_eq_case_5_3_row_1_1_1
  · exact right1Middle6_eq_case_5_3_row_1_1_2
  · exact right1Middle6_eq_case_5_3_row_1_1_3
  · exact right1Middle6_eq_case_5_3_row_2_0_0
  · exact right1Middle6_eq_case_5_3_row_2_0_1
  · exact right1Middle6_eq_case_5_3_row_2_0_2
  · exact right1Middle6_eq_case_5_3_row_2_0_3
  · exact right1Middle6_eq_case_5_3_row_2_1_0
  · exact right1Middle6_eq_case_5_3_row_2_1_1
  · exact right1Middle6_eq_case_5_3_row_2_1_2
  · exact right1Middle6_eq_case_5_3_row_2_1_3
  · exact right1Middle6_eq_case_5_3_row_3_0_0
  · exact right1Middle6_eq_case_5_3_row_3_0_1
  · exact right1Middle6_eq_case_5_3_row_3_0_2
  · exact right1Middle6_eq_case_5_3_row_3_0_3
  · exact right1Middle6_eq_case_5_3_row_3_1_0
  · exact right1Middle6_eq_case_5_3_row_3_1_1
  · exact right1Middle6_eq_case_5_3_row_3_1_2
  · exact right1Middle6_eq_case_5_3_row_3_1_3

set_option backward.isDefEq.respectTransparency false in
theorem right1Middle6_eq_case_5_3 : right1Middle6 5 3 = associatorInverseZ 6 3 5 * right0Middle6 5 3 := by
  simpa only [HexagonAtoms653.assocABC_eq,
    HexagonAtoms653.outerABC_eq,
    HexagonAtoms653.assocBAC_eq,
    HexagonAtoms653.innerABC_eq,
    HexagonAtoms653.innerRightABC_eq,
    HexagonAtoms653.inverseACB_eq,
    HexagonAtoms653.innerACB_eq,
    HexagonAtoms653.assocBCA_eq,
    HexagonAtoms653.innerRightBAC_eq,
    HexagonAtoms653.assocCAB_eq,
    HexagonAtoms653.outerLeftABC_eq,
    HexagonRowColumn653.product0_eq,
    HexagonRowColumn653.product1_eq,
    HexagonRowColumn653.product2_eq,
    HexagonRowColumn653.product3_eq,
    HexagonRowColumn653.product4_eq,
    HexagonRowColumn653.product5_eq,
    HexagonRowColumn653.product6_eq,
    HexagonRowColumn653.product7_eq] using right1Middle6_eq_case_5_3_checked

private theorem right2Middle6_eq_case_5_3_row_0_0_0 : (right2Middle6 5 3) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (right1Middle6 5 3) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_5_3_row_0_0_1 : (right2Middle6 5 3) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (right1Middle6 5 3) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_5_3_row_0_0_2 : (right2Middle6 5 3) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (right1Middle6 5 3) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_5_3_row_0_0_3 : (right2Middle6 5 3) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (right1Middle6 5 3) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_5_3_row_0_1_0 : (right2Middle6 5 3) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (right1Middle6 5 3) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_5_3_row_0_1_1 : (right2Middle6 5 3) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (right1Middle6 5 3) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_5_3_row_0_1_2 : (right2Middle6 5 3) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (right1Middle6 5 3) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_5_3_row_0_1_3 : (right2Middle6 5 3) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (right1Middle6 5 3) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_5_3_row_1_0_0 : (right2Middle6 5 3) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (right1Middle6 5 3) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_5_3_row_1_0_1 : (right2Middle6 5 3) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (right1Middle6 5 3) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_5_3_row_1_0_2 : (right2Middle6 5 3) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (right1Middle6 5 3) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_5_3_row_1_0_3 : (right2Middle6 5 3) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (right1Middle6 5 3) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_5_3_row_1_1_0 : (right2Middle6 5 3) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (right1Middle6 5 3) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_5_3_row_1_1_1 : (right2Middle6 5 3) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (right1Middle6 5 3) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_5_3_row_1_1_2 : (right2Middle6 5 3) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (right1Middle6 5 3) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_5_3_row_1_1_3 : (right2Middle6 5 3) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (right1Middle6 5 3) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_5_3_row_2_0_0 : (right2Middle6 5 3) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (right1Middle6 5 3) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_5_3_row_2_0_1 : (right2Middle6 5 3) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (right1Middle6 5 3) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_5_3_row_2_0_2 : (right2Middle6 5 3) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (right1Middle6 5 3) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_5_3_row_2_0_3 : (right2Middle6 5 3) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (right1Middle6 5 3) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_5_3_row_2_1_0 : (right2Middle6 5 3) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (right1Middle6 5 3) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_5_3_row_2_1_1 : (right2Middle6 5 3) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (right1Middle6 5 3) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_5_3_row_2_1_2 : (right2Middle6 5 3) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (right1Middle6 5 3) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_5_3_row_2_1_3 : (right2Middle6 5 3) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (right1Middle6 5 3) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_5_3_row_3_0_0 : (right2Middle6 5 3) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (right1Middle6 5 3) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_5_3_row_3_0_1 : (right2Middle6 5 3) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (right1Middle6 5 3) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_5_3_row_3_0_2 : (right2Middle6 5 3) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (right1Middle6 5 3) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_5_3_row_3_0_3 : (right2Middle6 5 3) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (right1Middle6 5 3) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_5_3_row_3_1_0 : (right2Middle6 5 3) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (right1Middle6 5 3) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_5_3_row_3_1_1 : (right2Middle6 5 3) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (right1Middle6 5 3) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_5_3_row_3_1_2 : (right2Middle6 5 3) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (right1Middle6 5 3) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_5_3_row_3_1_3 : (right2Middle6 5 3) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (right1Middle6 5 3) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_5_3_checked : right2Middle6 5 3 = right1Middle6 5 3 := by
  funext r
  fin_cases r
  · exact right2Middle6_eq_case_5_3_row_0_0_0
  · exact right2Middle6_eq_case_5_3_row_0_0_1
  · exact right2Middle6_eq_case_5_3_row_0_0_2
  · exact right2Middle6_eq_case_5_3_row_0_0_3
  · exact right2Middle6_eq_case_5_3_row_0_1_0
  · exact right2Middle6_eq_case_5_3_row_0_1_1
  · exact right2Middle6_eq_case_5_3_row_0_1_2
  · exact right2Middle6_eq_case_5_3_row_0_1_3
  · exact right2Middle6_eq_case_5_3_row_1_0_0
  · exact right2Middle6_eq_case_5_3_row_1_0_1
  · exact right2Middle6_eq_case_5_3_row_1_0_2
  · exact right2Middle6_eq_case_5_3_row_1_0_3
  · exact right2Middle6_eq_case_5_3_row_1_1_0
  · exact right2Middle6_eq_case_5_3_row_1_1_1
  · exact right2Middle6_eq_case_5_3_row_1_1_2
  · exact right2Middle6_eq_case_5_3_row_1_1_3
  · exact right2Middle6_eq_case_5_3_row_2_0_0
  · exact right2Middle6_eq_case_5_3_row_2_0_1
  · exact right2Middle6_eq_case_5_3_row_2_0_2
  · exact right2Middle6_eq_case_5_3_row_2_0_3
  · exact right2Middle6_eq_case_5_3_row_2_1_0
  · exact right2Middle6_eq_case_5_3_row_2_1_1
  · exact right2Middle6_eq_case_5_3_row_2_1_2
  · exact right2Middle6_eq_case_5_3_row_2_1_3
  · exact right2Middle6_eq_case_5_3_row_3_0_0
  · exact right2Middle6_eq_case_5_3_row_3_0_1
  · exact right2Middle6_eq_case_5_3_row_3_0_2
  · exact right2Middle6_eq_case_5_3_row_3_0_3
  · exact right2Middle6_eq_case_5_3_row_3_1_0
  · exact right2Middle6_eq_case_5_3_row_3_1_1
  · exact right2Middle6_eq_case_5_3_row_3_1_2
  · exact right2Middle6_eq_case_5_3_row_3_1_3

set_option backward.isDefEq.respectTransparency false in
theorem right2Middle6_eq_case_5_3 : right2Middle6 5 3 = innerLeftZ 6 3 5 * right1Middle6 5 3 := by
  simpa only [HexagonAtoms653.assocABC_eq,
    HexagonAtoms653.outerABC_eq,
    HexagonAtoms653.assocBAC_eq,
    HexagonAtoms653.innerABC_eq,
    HexagonAtoms653.innerRightABC_eq,
    HexagonAtoms653.inverseACB_eq,
    HexagonAtoms653.innerACB_eq,
    HexagonAtoms653.assocBCA_eq,
    HexagonAtoms653.innerRightBAC_eq,
    HexagonAtoms653.assocCAB_eq,
    HexagonAtoms653.outerLeftABC_eq,
    HexagonRowColumn653.product0_eq,
    HexagonRowColumn653.product1_eq,
    HexagonRowColumn653.product2_eq,
    HexagonRowColumn653.product3_eq,
    HexagonRowColumn653.product4_eq,
    HexagonRowColumn653.product5_eq,
    HexagonRowColumn653.product6_eq,
    HexagonRowColumn653.product7_eq] using right2Middle6_eq_case_5_3_checked

private theorem leftFinal6_case_5_3_row_0_0_0 : (((-1 : ℤ) ^ (leftScaleBit 6 5 3).val * positiveScale (leftScaleExponent 6 5 3)) •
      (rowColumnMul HexagonRowColumn653.rows_assocBCA HexagonRowColumn653.cols_left0)) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 6 5 3) • (left1Middle6 5 3)) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem leftFinal6_case_5_3_row_0_0_1 : (((-1 : ℤ) ^ (leftScaleBit 6 5 3).val * positiveScale (leftScaleExponent 6 5 3)) •
      (rowColumnMul HexagonRowColumn653.rows_assocBCA HexagonRowColumn653.cols_left0)) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 6 5 3) • (left1Middle6 5 3)) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem leftFinal6_case_5_3_row_0_0_2 : (((-1 : ℤ) ^ (leftScaleBit 6 5 3).val * positiveScale (leftScaleExponent 6 5 3)) •
      (rowColumnMul HexagonRowColumn653.rows_assocBCA HexagonRowColumn653.cols_left0)) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 6 5 3) • (left1Middle6 5 3)) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem leftFinal6_case_5_3_row_0_0_3 : (((-1 : ℤ) ^ (leftScaleBit 6 5 3).val * positiveScale (leftScaleExponent 6 5 3)) •
      (rowColumnMul HexagonRowColumn653.rows_assocBCA HexagonRowColumn653.cols_left0)) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 6 5 3) • (left1Middle6 5 3)) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem leftFinal6_case_5_3_row_0_1_0 : (((-1 : ℤ) ^ (leftScaleBit 6 5 3).val * positiveScale (leftScaleExponent 6 5 3)) •
      (rowColumnMul HexagonRowColumn653.rows_assocBCA HexagonRowColumn653.cols_left0)) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 6 5 3) • (left1Middle6 5 3)) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem leftFinal6_case_5_3_row_0_1_1 : (((-1 : ℤ) ^ (leftScaleBit 6 5 3).val * positiveScale (leftScaleExponent 6 5 3)) •
      (rowColumnMul HexagonRowColumn653.rows_assocBCA HexagonRowColumn653.cols_left0)) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 6 5 3) • (left1Middle6 5 3)) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem leftFinal6_case_5_3_row_0_1_2 : (((-1 : ℤ) ^ (leftScaleBit 6 5 3).val * positiveScale (leftScaleExponent 6 5 3)) •
      (rowColumnMul HexagonRowColumn653.rows_assocBCA HexagonRowColumn653.cols_left0)) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 6 5 3) • (left1Middle6 5 3)) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem leftFinal6_case_5_3_row_0_1_3 : (((-1 : ℤ) ^ (leftScaleBit 6 5 3).val * positiveScale (leftScaleExponent 6 5 3)) •
      (rowColumnMul HexagonRowColumn653.rows_assocBCA HexagonRowColumn653.cols_left0)) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 6 5 3) • (left1Middle6 5 3)) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem leftFinal6_case_5_3_row_1_0_0 : (((-1 : ℤ) ^ (leftScaleBit 6 5 3).val * positiveScale (leftScaleExponent 6 5 3)) •
      (rowColumnMul HexagonRowColumn653.rows_assocBCA HexagonRowColumn653.cols_left0)) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 6 5 3) • (left1Middle6 5 3)) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem leftFinal6_case_5_3_row_1_0_1 : (((-1 : ℤ) ^ (leftScaleBit 6 5 3).val * positiveScale (leftScaleExponent 6 5 3)) •
      (rowColumnMul HexagonRowColumn653.rows_assocBCA HexagonRowColumn653.cols_left0)) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 6 5 3) • (left1Middle6 5 3)) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem leftFinal6_case_5_3_row_1_0_2 : (((-1 : ℤ) ^ (leftScaleBit 6 5 3).val * positiveScale (leftScaleExponent 6 5 3)) •
      (rowColumnMul HexagonRowColumn653.rows_assocBCA HexagonRowColumn653.cols_left0)) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 6 5 3) • (left1Middle6 5 3)) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem leftFinal6_case_5_3_row_1_0_3 : (((-1 : ℤ) ^ (leftScaleBit 6 5 3).val * positiveScale (leftScaleExponent 6 5 3)) •
      (rowColumnMul HexagonRowColumn653.rows_assocBCA HexagonRowColumn653.cols_left0)) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 6 5 3) • (left1Middle6 5 3)) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem leftFinal6_case_5_3_row_1_1_0 : (((-1 : ℤ) ^ (leftScaleBit 6 5 3).val * positiveScale (leftScaleExponent 6 5 3)) •
      (rowColumnMul HexagonRowColumn653.rows_assocBCA HexagonRowColumn653.cols_left0)) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 6 5 3) • (left1Middle6 5 3)) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem leftFinal6_case_5_3_row_1_1_1 : (((-1 : ℤ) ^ (leftScaleBit 6 5 3).val * positiveScale (leftScaleExponent 6 5 3)) •
      (rowColumnMul HexagonRowColumn653.rows_assocBCA HexagonRowColumn653.cols_left0)) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 6 5 3) • (left1Middle6 5 3)) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem leftFinal6_case_5_3_row_1_1_2 : (((-1 : ℤ) ^ (leftScaleBit 6 5 3).val * positiveScale (leftScaleExponent 6 5 3)) •
      (rowColumnMul HexagonRowColumn653.rows_assocBCA HexagonRowColumn653.cols_left0)) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 6 5 3) • (left1Middle6 5 3)) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem leftFinal6_case_5_3_row_1_1_3 : (((-1 : ℤ) ^ (leftScaleBit 6 5 3).val * positiveScale (leftScaleExponent 6 5 3)) •
      (rowColumnMul HexagonRowColumn653.rows_assocBCA HexagonRowColumn653.cols_left0)) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 6 5 3) • (left1Middle6 5 3)) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem leftFinal6_case_5_3_row_2_0_0 : (((-1 : ℤ) ^ (leftScaleBit 6 5 3).val * positiveScale (leftScaleExponent 6 5 3)) •
      (rowColumnMul HexagonRowColumn653.rows_assocBCA HexagonRowColumn653.cols_left0)) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 6 5 3) • (left1Middle6 5 3)) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem leftFinal6_case_5_3_row_2_0_1 : (((-1 : ℤ) ^ (leftScaleBit 6 5 3).val * positiveScale (leftScaleExponent 6 5 3)) •
      (rowColumnMul HexagonRowColumn653.rows_assocBCA HexagonRowColumn653.cols_left0)) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 6 5 3) • (left1Middle6 5 3)) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem leftFinal6_case_5_3_row_2_0_2 : (((-1 : ℤ) ^ (leftScaleBit 6 5 3).val * positiveScale (leftScaleExponent 6 5 3)) •
      (rowColumnMul HexagonRowColumn653.rows_assocBCA HexagonRowColumn653.cols_left0)) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 6 5 3) • (left1Middle6 5 3)) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem leftFinal6_case_5_3_row_2_0_3 : (((-1 : ℤ) ^ (leftScaleBit 6 5 3).val * positiveScale (leftScaleExponent 6 5 3)) •
      (rowColumnMul HexagonRowColumn653.rows_assocBCA HexagonRowColumn653.cols_left0)) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 6 5 3) • (left1Middle6 5 3)) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem leftFinal6_case_5_3_row_2_1_0 : (((-1 : ℤ) ^ (leftScaleBit 6 5 3).val * positiveScale (leftScaleExponent 6 5 3)) •
      (rowColumnMul HexagonRowColumn653.rows_assocBCA HexagonRowColumn653.cols_left0)) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 6 5 3) • (left1Middle6 5 3)) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem leftFinal6_case_5_3_row_2_1_1 : (((-1 : ℤ) ^ (leftScaleBit 6 5 3).val * positiveScale (leftScaleExponent 6 5 3)) •
      (rowColumnMul HexagonRowColumn653.rows_assocBCA HexagonRowColumn653.cols_left0)) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 6 5 3) • (left1Middle6 5 3)) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem leftFinal6_case_5_3_row_2_1_2 : (((-1 : ℤ) ^ (leftScaleBit 6 5 3).val * positiveScale (leftScaleExponent 6 5 3)) •
      (rowColumnMul HexagonRowColumn653.rows_assocBCA HexagonRowColumn653.cols_left0)) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 6 5 3) • (left1Middle6 5 3)) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem leftFinal6_case_5_3_row_2_1_3 : (((-1 : ℤ) ^ (leftScaleBit 6 5 3).val * positiveScale (leftScaleExponent 6 5 3)) •
      (rowColumnMul HexagonRowColumn653.rows_assocBCA HexagonRowColumn653.cols_left0)) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 6 5 3) • (left1Middle6 5 3)) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem leftFinal6_case_5_3_row_3_0_0 : (((-1 : ℤ) ^ (leftScaleBit 6 5 3).val * positiveScale (leftScaleExponent 6 5 3)) •
      (rowColumnMul HexagonRowColumn653.rows_assocBCA HexagonRowColumn653.cols_left0)) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 6 5 3) • (left1Middle6 5 3)) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem leftFinal6_case_5_3_row_3_0_1 : (((-1 : ℤ) ^ (leftScaleBit 6 5 3).val * positiveScale (leftScaleExponent 6 5 3)) •
      (rowColumnMul HexagonRowColumn653.rows_assocBCA HexagonRowColumn653.cols_left0)) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 6 5 3) • (left1Middle6 5 3)) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem leftFinal6_case_5_3_row_3_0_2 : (((-1 : ℤ) ^ (leftScaleBit 6 5 3).val * positiveScale (leftScaleExponent 6 5 3)) •
      (rowColumnMul HexagonRowColumn653.rows_assocBCA HexagonRowColumn653.cols_left0)) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 6 5 3) • (left1Middle6 5 3)) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem leftFinal6_case_5_3_row_3_0_3 : (((-1 : ℤ) ^ (leftScaleBit 6 5 3).val * positiveScale (leftScaleExponent 6 5 3)) •
      (rowColumnMul HexagonRowColumn653.rows_assocBCA HexagonRowColumn653.cols_left0)) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 6 5 3) • (left1Middle6 5 3)) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem leftFinal6_case_5_3_row_3_1_0 : (((-1 : ℤ) ^ (leftScaleBit 6 5 3).val * positiveScale (leftScaleExponent 6 5 3)) •
      (rowColumnMul HexagonRowColumn653.rows_assocBCA HexagonRowColumn653.cols_left0)) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 6 5 3) • (left1Middle6 5 3)) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem leftFinal6_case_5_3_row_3_1_1 : (((-1 : ℤ) ^ (leftScaleBit 6 5 3).val * positiveScale (leftScaleExponent 6 5 3)) •
      (rowColumnMul HexagonRowColumn653.rows_assocBCA HexagonRowColumn653.cols_left0)) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 6 5 3) • (left1Middle6 5 3)) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem leftFinal6_case_5_3_row_3_1_2 : (((-1 : ℤ) ^ (leftScaleBit 6 5 3).val * positiveScale (leftScaleExponent 6 5 3)) •
      (rowColumnMul HexagonRowColumn653.rows_assocBCA HexagonRowColumn653.cols_left0)) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 6 5 3) • (left1Middle6 5 3)) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem leftFinal6_case_5_3_row_3_1_3 : (((-1 : ℤ) ^ (leftScaleBit 6 5 3).val * positiveScale (leftScaleExponent 6 5 3)) •
      (rowColumnMul HexagonRowColumn653.rows_assocBCA HexagonRowColumn653.cols_left0)) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 6 5 3) • (left1Middle6 5 3)) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem leftFinal6_case_5_3_checked : ((-1 : ℤ) ^ (leftScaleBit 6 5 3).val * positiveScale (leftScaleExponent 6 5 3)) •
      (rowColumnMul HexagonRowColumn653.rows_assocBCA HexagonRowColumn653.cols_left0) = negativeScale (leftScaleExponent 6 5 3) • (left1Middle6 5 3) := by
  funext r
  fin_cases r
  · exact leftFinal6_case_5_3_row_0_0_0
  · exact leftFinal6_case_5_3_row_0_0_1
  · exact leftFinal6_case_5_3_row_0_0_2
  · exact leftFinal6_case_5_3_row_0_0_3
  · exact leftFinal6_case_5_3_row_0_1_0
  · exact leftFinal6_case_5_3_row_0_1_1
  · exact leftFinal6_case_5_3_row_0_1_2
  · exact leftFinal6_case_5_3_row_0_1_3
  · exact leftFinal6_case_5_3_row_1_0_0
  · exact leftFinal6_case_5_3_row_1_0_1
  · exact leftFinal6_case_5_3_row_1_0_2
  · exact leftFinal6_case_5_3_row_1_0_3
  · exact leftFinal6_case_5_3_row_1_1_0
  · exact leftFinal6_case_5_3_row_1_1_1
  · exact leftFinal6_case_5_3_row_1_1_2
  · exact leftFinal6_case_5_3_row_1_1_3
  · exact leftFinal6_case_5_3_row_2_0_0
  · exact leftFinal6_case_5_3_row_2_0_1
  · exact leftFinal6_case_5_3_row_2_0_2
  · exact leftFinal6_case_5_3_row_2_0_3
  · exact leftFinal6_case_5_3_row_2_1_0
  · exact leftFinal6_case_5_3_row_2_1_1
  · exact leftFinal6_case_5_3_row_2_1_2
  · exact leftFinal6_case_5_3_row_2_1_3
  · exact leftFinal6_case_5_3_row_3_0_0
  · exact leftFinal6_case_5_3_row_3_0_1
  · exact leftFinal6_case_5_3_row_3_0_2
  · exact leftFinal6_case_5_3_row_3_0_3
  · exact leftFinal6_case_5_3_row_3_1_0
  · exact leftFinal6_case_5_3_row_3_1_1
  · exact leftFinal6_case_5_3_row_3_1_2
  · exact leftFinal6_case_5_3_row_3_1_3

set_option backward.isDefEq.respectTransparency false in
theorem leftFinal6_case_5_3 : ((-1 : ℤ) ^ (leftScaleBit 6 5 3).val * positiveScale (leftScaleExponent 6 5 3)) •
      (associatorZ 5 3 6 * left0Middle6 5 3) = negativeScale (leftScaleExponent 6 5 3) • (innerRightZ 5 6 3 * left1Middle6 5 3) := by
  simpa only [HexagonAtoms653.assocABC_eq,
    HexagonAtoms653.outerABC_eq,
    HexagonAtoms653.assocBAC_eq,
    HexagonAtoms653.innerABC_eq,
    HexagonAtoms653.innerRightABC_eq,
    HexagonAtoms653.inverseACB_eq,
    HexagonAtoms653.innerACB_eq,
    HexagonAtoms653.assocBCA_eq,
    HexagonAtoms653.innerRightBAC_eq,
    HexagonAtoms653.assocCAB_eq,
    HexagonAtoms653.outerLeftABC_eq,
    HexagonRowColumn653.product0_eq,
    HexagonRowColumn653.product1_eq,
    HexagonRowColumn653.product2_eq,
    HexagonRowColumn653.product3_eq,
    HexagonRowColumn653.product4_eq,
    HexagonRowColumn653.product5_eq,
    HexagonRowColumn653.product6_eq,
    HexagonRowColumn653.product7_eq] using leftFinal6_case_5_3_checked

private theorem rightFinal6_case_5_3_row_0_0_0 : (((-1 : ℤ) ^ (rightScaleBit 6 5 3).val * positiveScale (rightScaleExponent 6 5 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 3 5 : ℤ)) • HexagonAtoms653.outerLeftABC) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 4)) = (negativeScale (rightScaleExponent 6 5 3) • (rowColumnMul HexagonRowColumn653.rows_assocCAB HexagonRowColumn653.cols_right2)) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem rightFinal6_case_5_3_row_0_0_1 : (((-1 : ℤ) ^ (rightScaleBit 6 5 3).val * positiveScale (rightScaleExponent 6 5 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 3 5 : ℤ)) • HexagonAtoms653.outerLeftABC) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 4)) = (negativeScale (rightScaleExponent 6 5 3) • (rowColumnMul HexagonRowColumn653.rows_assocCAB HexagonRowColumn653.cols_right2)) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem rightFinal6_case_5_3_row_0_0_2 : (((-1 : ℤ) ^ (rightScaleBit 6 5 3).val * positiveScale (rightScaleExponent 6 5 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 3 5 : ℤ)) • HexagonAtoms653.outerLeftABC) ((0 : Fin 2), (0 : Fin 4), (2 : Fin 4)) = (negativeScale (rightScaleExponent 6 5 3) • (rowColumnMul HexagonRowColumn653.rows_assocCAB HexagonRowColumn653.cols_right2)) ((0 : Fin 2), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem rightFinal6_case_5_3_row_0_0_3 : (((-1 : ℤ) ^ (rightScaleBit 6 5 3).val * positiveScale (rightScaleExponent 6 5 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 3 5 : ℤ)) • HexagonAtoms653.outerLeftABC) ((0 : Fin 2), (0 : Fin 4), (3 : Fin 4)) = (negativeScale (rightScaleExponent 6 5 3) • (rowColumnMul HexagonRowColumn653.rows_assocCAB HexagonRowColumn653.cols_right2)) ((0 : Fin 2), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem rightFinal6_case_5_3_row_0_1_0 : (((-1 : ℤ) ^ (rightScaleBit 6 5 3).val * positiveScale (rightScaleExponent 6 5 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 3 5 : ℤ)) • HexagonAtoms653.outerLeftABC) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 4)) = (negativeScale (rightScaleExponent 6 5 3) • (rowColumnMul HexagonRowColumn653.rows_assocCAB HexagonRowColumn653.cols_right2)) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem rightFinal6_case_5_3_row_0_1_1 : (((-1 : ℤ) ^ (rightScaleBit 6 5 3).val * positiveScale (rightScaleExponent 6 5 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 3 5 : ℤ)) • HexagonAtoms653.outerLeftABC) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 4)) = (negativeScale (rightScaleExponent 6 5 3) • (rowColumnMul HexagonRowColumn653.rows_assocCAB HexagonRowColumn653.cols_right2)) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem rightFinal6_case_5_3_row_0_1_2 : (((-1 : ℤ) ^ (rightScaleBit 6 5 3).val * positiveScale (rightScaleExponent 6 5 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 3 5 : ℤ)) • HexagonAtoms653.outerLeftABC) ((0 : Fin 2), (1 : Fin 4), (2 : Fin 4)) = (negativeScale (rightScaleExponent 6 5 3) • (rowColumnMul HexagonRowColumn653.rows_assocCAB HexagonRowColumn653.cols_right2)) ((0 : Fin 2), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem rightFinal6_case_5_3_row_0_1_3 : (((-1 : ℤ) ^ (rightScaleBit 6 5 3).val * positiveScale (rightScaleExponent 6 5 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 3 5 : ℤ)) • HexagonAtoms653.outerLeftABC) ((0 : Fin 2), (1 : Fin 4), (3 : Fin 4)) = (negativeScale (rightScaleExponent 6 5 3) • (rowColumnMul HexagonRowColumn653.rows_assocCAB HexagonRowColumn653.cols_right2)) ((0 : Fin 2), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem rightFinal6_case_5_3_row_0_2_0 : (((-1 : ℤ) ^ (rightScaleBit 6 5 3).val * positiveScale (rightScaleExponent 6 5 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 3 5 : ℤ)) • HexagonAtoms653.outerLeftABC) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 4)) = (negativeScale (rightScaleExponent 6 5 3) • (rowColumnMul HexagonRowColumn653.rows_assocCAB HexagonRowColumn653.cols_right2)) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem rightFinal6_case_5_3_row_0_2_1 : (((-1 : ℤ) ^ (rightScaleBit 6 5 3).val * positiveScale (rightScaleExponent 6 5 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 3 5 : ℤ)) • HexagonAtoms653.outerLeftABC) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 4)) = (negativeScale (rightScaleExponent 6 5 3) • (rowColumnMul HexagonRowColumn653.rows_assocCAB HexagonRowColumn653.cols_right2)) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem rightFinal6_case_5_3_row_0_2_2 : (((-1 : ℤ) ^ (rightScaleBit 6 5 3).val * positiveScale (rightScaleExponent 6 5 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 3 5 : ℤ)) • HexagonAtoms653.outerLeftABC) ((0 : Fin 2), (2 : Fin 4), (2 : Fin 4)) = (negativeScale (rightScaleExponent 6 5 3) • (rowColumnMul HexagonRowColumn653.rows_assocCAB HexagonRowColumn653.cols_right2)) ((0 : Fin 2), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem rightFinal6_case_5_3_row_0_2_3 : (((-1 : ℤ) ^ (rightScaleBit 6 5 3).val * positiveScale (rightScaleExponent 6 5 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 3 5 : ℤ)) • HexagonAtoms653.outerLeftABC) ((0 : Fin 2), (2 : Fin 4), (3 : Fin 4)) = (negativeScale (rightScaleExponent 6 5 3) • (rowColumnMul HexagonRowColumn653.rows_assocCAB HexagonRowColumn653.cols_right2)) ((0 : Fin 2), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem rightFinal6_case_5_3_row_0_3_0 : (((-1 : ℤ) ^ (rightScaleBit 6 5 3).val * positiveScale (rightScaleExponent 6 5 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 3 5 : ℤ)) • HexagonAtoms653.outerLeftABC) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 4)) = (negativeScale (rightScaleExponent 6 5 3) • (rowColumnMul HexagonRowColumn653.rows_assocCAB HexagonRowColumn653.cols_right2)) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem rightFinal6_case_5_3_row_0_3_1 : (((-1 : ℤ) ^ (rightScaleBit 6 5 3).val * positiveScale (rightScaleExponent 6 5 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 3 5 : ℤ)) • HexagonAtoms653.outerLeftABC) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 4)) = (negativeScale (rightScaleExponent 6 5 3) • (rowColumnMul HexagonRowColumn653.rows_assocCAB HexagonRowColumn653.cols_right2)) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem rightFinal6_case_5_3_row_0_3_2 : (((-1 : ℤ) ^ (rightScaleBit 6 5 3).val * positiveScale (rightScaleExponent 6 5 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 3 5 : ℤ)) • HexagonAtoms653.outerLeftABC) ((0 : Fin 2), (3 : Fin 4), (2 : Fin 4)) = (negativeScale (rightScaleExponent 6 5 3) • (rowColumnMul HexagonRowColumn653.rows_assocCAB HexagonRowColumn653.cols_right2)) ((0 : Fin 2), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem rightFinal6_case_5_3_row_0_3_3 : (((-1 : ℤ) ^ (rightScaleBit 6 5 3).val * positiveScale (rightScaleExponent 6 5 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 3 5 : ℤ)) • HexagonAtoms653.outerLeftABC) ((0 : Fin 2), (3 : Fin 4), (3 : Fin 4)) = (negativeScale (rightScaleExponent 6 5 3) • (rowColumnMul HexagonRowColumn653.rows_assocCAB HexagonRowColumn653.cols_right2)) ((0 : Fin 2), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem rightFinal6_case_5_3_row_1_0_0 : (((-1 : ℤ) ^ (rightScaleBit 6 5 3).val * positiveScale (rightScaleExponent 6 5 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 3 5 : ℤ)) • HexagonAtoms653.outerLeftABC) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 4)) = (negativeScale (rightScaleExponent 6 5 3) • (rowColumnMul HexagonRowColumn653.rows_assocCAB HexagonRowColumn653.cols_right2)) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem rightFinal6_case_5_3_row_1_0_1 : (((-1 : ℤ) ^ (rightScaleBit 6 5 3).val * positiveScale (rightScaleExponent 6 5 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 3 5 : ℤ)) • HexagonAtoms653.outerLeftABC) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 4)) = (negativeScale (rightScaleExponent 6 5 3) • (rowColumnMul HexagonRowColumn653.rows_assocCAB HexagonRowColumn653.cols_right2)) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem rightFinal6_case_5_3_row_1_0_2 : (((-1 : ℤ) ^ (rightScaleBit 6 5 3).val * positiveScale (rightScaleExponent 6 5 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 3 5 : ℤ)) • HexagonAtoms653.outerLeftABC) ((1 : Fin 2), (0 : Fin 4), (2 : Fin 4)) = (negativeScale (rightScaleExponent 6 5 3) • (rowColumnMul HexagonRowColumn653.rows_assocCAB HexagonRowColumn653.cols_right2)) ((1 : Fin 2), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem rightFinal6_case_5_3_row_1_0_3 : (((-1 : ℤ) ^ (rightScaleBit 6 5 3).val * positiveScale (rightScaleExponent 6 5 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 3 5 : ℤ)) • HexagonAtoms653.outerLeftABC) ((1 : Fin 2), (0 : Fin 4), (3 : Fin 4)) = (negativeScale (rightScaleExponent 6 5 3) • (rowColumnMul HexagonRowColumn653.rows_assocCAB HexagonRowColumn653.cols_right2)) ((1 : Fin 2), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem rightFinal6_case_5_3_row_1_1_0 : (((-1 : ℤ) ^ (rightScaleBit 6 5 3).val * positiveScale (rightScaleExponent 6 5 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 3 5 : ℤ)) • HexagonAtoms653.outerLeftABC) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 4)) = (negativeScale (rightScaleExponent 6 5 3) • (rowColumnMul HexagonRowColumn653.rows_assocCAB HexagonRowColumn653.cols_right2)) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem rightFinal6_case_5_3_row_1_1_1 : (((-1 : ℤ) ^ (rightScaleBit 6 5 3).val * positiveScale (rightScaleExponent 6 5 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 3 5 : ℤ)) • HexagonAtoms653.outerLeftABC) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 4)) = (negativeScale (rightScaleExponent 6 5 3) • (rowColumnMul HexagonRowColumn653.rows_assocCAB HexagonRowColumn653.cols_right2)) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem rightFinal6_case_5_3_row_1_1_2 : (((-1 : ℤ) ^ (rightScaleBit 6 5 3).val * positiveScale (rightScaleExponent 6 5 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 3 5 : ℤ)) • HexagonAtoms653.outerLeftABC) ((1 : Fin 2), (1 : Fin 4), (2 : Fin 4)) = (negativeScale (rightScaleExponent 6 5 3) • (rowColumnMul HexagonRowColumn653.rows_assocCAB HexagonRowColumn653.cols_right2)) ((1 : Fin 2), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem rightFinal6_case_5_3_row_1_1_3 : (((-1 : ℤ) ^ (rightScaleBit 6 5 3).val * positiveScale (rightScaleExponent 6 5 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 3 5 : ℤ)) • HexagonAtoms653.outerLeftABC) ((1 : Fin 2), (1 : Fin 4), (3 : Fin 4)) = (negativeScale (rightScaleExponent 6 5 3) • (rowColumnMul HexagonRowColumn653.rows_assocCAB HexagonRowColumn653.cols_right2)) ((1 : Fin 2), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem rightFinal6_case_5_3_row_1_2_0 : (((-1 : ℤ) ^ (rightScaleBit 6 5 3).val * positiveScale (rightScaleExponent 6 5 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 3 5 : ℤ)) • HexagonAtoms653.outerLeftABC) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 4)) = (negativeScale (rightScaleExponent 6 5 3) • (rowColumnMul HexagonRowColumn653.rows_assocCAB HexagonRowColumn653.cols_right2)) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem rightFinal6_case_5_3_row_1_2_1 : (((-1 : ℤ) ^ (rightScaleBit 6 5 3).val * positiveScale (rightScaleExponent 6 5 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 3 5 : ℤ)) • HexagonAtoms653.outerLeftABC) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 4)) = (negativeScale (rightScaleExponent 6 5 3) • (rowColumnMul HexagonRowColumn653.rows_assocCAB HexagonRowColumn653.cols_right2)) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem rightFinal6_case_5_3_row_1_2_2 : (((-1 : ℤ) ^ (rightScaleBit 6 5 3).val * positiveScale (rightScaleExponent 6 5 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 3 5 : ℤ)) • HexagonAtoms653.outerLeftABC) ((1 : Fin 2), (2 : Fin 4), (2 : Fin 4)) = (negativeScale (rightScaleExponent 6 5 3) • (rowColumnMul HexagonRowColumn653.rows_assocCAB HexagonRowColumn653.cols_right2)) ((1 : Fin 2), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem rightFinal6_case_5_3_row_1_2_3 : (((-1 : ℤ) ^ (rightScaleBit 6 5 3).val * positiveScale (rightScaleExponent 6 5 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 3 5 : ℤ)) • HexagonAtoms653.outerLeftABC) ((1 : Fin 2), (2 : Fin 4), (3 : Fin 4)) = (negativeScale (rightScaleExponent 6 5 3) • (rowColumnMul HexagonRowColumn653.rows_assocCAB HexagonRowColumn653.cols_right2)) ((1 : Fin 2), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem rightFinal6_case_5_3_row_1_3_0 : (((-1 : ℤ) ^ (rightScaleBit 6 5 3).val * positiveScale (rightScaleExponent 6 5 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 3 5 : ℤ)) • HexagonAtoms653.outerLeftABC) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 4)) = (negativeScale (rightScaleExponent 6 5 3) • (rowColumnMul HexagonRowColumn653.rows_assocCAB HexagonRowColumn653.cols_right2)) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem rightFinal6_case_5_3_row_1_3_1 : (((-1 : ℤ) ^ (rightScaleBit 6 5 3).val * positiveScale (rightScaleExponent 6 5 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 3 5 : ℤ)) • HexagonAtoms653.outerLeftABC) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 4)) = (negativeScale (rightScaleExponent 6 5 3) • (rowColumnMul HexagonRowColumn653.rows_assocCAB HexagonRowColumn653.cols_right2)) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem rightFinal6_case_5_3_row_1_3_2 : (((-1 : ℤ) ^ (rightScaleBit 6 5 3).val * positiveScale (rightScaleExponent 6 5 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 3 5 : ℤ)) • HexagonAtoms653.outerLeftABC) ((1 : Fin 2), (3 : Fin 4), (2 : Fin 4)) = (negativeScale (rightScaleExponent 6 5 3) • (rowColumnMul HexagonRowColumn653.rows_assocCAB HexagonRowColumn653.cols_right2)) ((1 : Fin 2), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem rightFinal6_case_5_3_row_1_3_3 : (((-1 : ℤ) ^ (rightScaleBit 6 5 3).val * positiveScale (rightScaleExponent 6 5 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 3 5 : ℤ)) • HexagonAtoms653.outerLeftABC) ((1 : Fin 2), (3 : Fin 4), (3 : Fin 4)) = (negativeScale (rightScaleExponent 6 5 3) • (rowColumnMul HexagonRowColumn653.rows_assocCAB HexagonRowColumn653.cols_right2)) ((1 : Fin 2), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem rightFinal6_case_5_3_checked : ((-1 : ℤ) ^ (rightScaleBit 6 5 3).val * positiveScale (rightScaleExponent 6 5 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 3 5 : ℤ)) • HexagonAtoms653.outerLeftABC = negativeScale (rightScaleExponent 6 5 3) • (rowColumnMul HexagonRowColumn653.rows_assocCAB HexagonRowColumn653.cols_right2) := by
  funext r
  fin_cases r
  · exact rightFinal6_case_5_3_row_0_0_0
  · exact rightFinal6_case_5_3_row_0_0_1
  · exact rightFinal6_case_5_3_row_0_0_2
  · exact rightFinal6_case_5_3_row_0_0_3
  · exact rightFinal6_case_5_3_row_0_1_0
  · exact rightFinal6_case_5_3_row_0_1_1
  · exact rightFinal6_case_5_3_row_0_1_2
  · exact rightFinal6_case_5_3_row_0_1_3
  · exact rightFinal6_case_5_3_row_0_2_0
  · exact rightFinal6_case_5_3_row_0_2_1
  · exact rightFinal6_case_5_3_row_0_2_2
  · exact rightFinal6_case_5_3_row_0_2_3
  · exact rightFinal6_case_5_3_row_0_3_0
  · exact rightFinal6_case_5_3_row_0_3_1
  · exact rightFinal6_case_5_3_row_0_3_2
  · exact rightFinal6_case_5_3_row_0_3_3
  · exact rightFinal6_case_5_3_row_1_0_0
  · exact rightFinal6_case_5_3_row_1_0_1
  · exact rightFinal6_case_5_3_row_1_0_2
  · exact rightFinal6_case_5_3_row_1_0_3
  · exact rightFinal6_case_5_3_row_1_1_0
  · exact rightFinal6_case_5_3_row_1_1_1
  · exact rightFinal6_case_5_3_row_1_1_2
  · exact rightFinal6_case_5_3_row_1_1_3
  · exact rightFinal6_case_5_3_row_1_2_0
  · exact rightFinal6_case_5_3_row_1_2_1
  · exact rightFinal6_case_5_3_row_1_2_2
  · exact rightFinal6_case_5_3_row_1_2_3
  · exact rightFinal6_case_5_3_row_1_3_0
  · exact rightFinal6_case_5_3_row_1_3_1
  · exact rightFinal6_case_5_3_row_1_3_2
  · exact rightFinal6_case_5_3_row_1_3_3

set_option backward.isDefEq.respectTransparency false in
theorem rightFinal6_case_5_3 : ((-1 : ℤ) ^ (rightScaleBit 6 5 3).val * positiveScale (rightScaleExponent 6 5 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 3 5 : ℤ)) • outerLeftZ 6 5 3 = negativeScale (rightScaleExponent 6 5 3) • (associatorZ 3 6 5 * right2Middle6 5 3) := by
  simpa only [HexagonAtoms653.assocABC_eq,
    HexagonAtoms653.outerABC_eq,
    HexagonAtoms653.assocBAC_eq,
    HexagonAtoms653.innerABC_eq,
    HexagonAtoms653.innerRightABC_eq,
    HexagonAtoms653.inverseACB_eq,
    HexagonAtoms653.innerACB_eq,
    HexagonAtoms653.assocBCA_eq,
    HexagonAtoms653.innerRightBAC_eq,
    HexagonAtoms653.assocCAB_eq,
    HexagonAtoms653.outerLeftABC_eq,
    HexagonRowColumn653.product0_eq,
    HexagonRowColumn653.product1_eq,
    HexagonRowColumn653.product2_eq,
    HexagonRowColumn653.product3_eq,
    HexagonRowColumn653.product4_eq,
    HexagonRowColumn653.product5_eq,
    HexagonRowColumn653.product6_eq,
    HexagonRowColumn653.product7_eq] using rightFinal6_case_5_3_checked

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonCases6
