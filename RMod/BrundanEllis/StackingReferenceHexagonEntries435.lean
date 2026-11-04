import RMod.BrundanEllis.StackingReferenceHexagonMiddle4
import RMod.BrundanEllis.StackingReferenceSparseMatrixCheck
import RMod.BrundanEllis.StackingReferenceHexagonAtoms435
import RMod.BrundanEllis.StackingReferenceHexagonRowColumn435

/-! Seven closed product identities for one reference triple.
The proof uses only verified atomic maps and ordinary kernel reduction. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
set_option linter.unusedSimpArgs false
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonCases4
open Superfusion

private theorem left0Middle4_eq_case_3_5_row_0_0_0 : (left0Middle4 3 5) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms435.assocABC) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_3_5_row_0_0_1 : (left0Middle4 3 5) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms435.assocABC) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_3_5_row_0_0_2 : (left0Middle4 3 5) ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms435.assocABC) ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_3_5_row_0_0_3 : (left0Middle4 3 5) ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms435.assocABC) ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_3_5_row_1_0_0 : (left0Middle4 3 5) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms435.assocABC) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_3_5_row_1_0_1 : (left0Middle4 3 5) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms435.assocABC) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_3_5_row_1_0_2 : (left0Middle4 3 5) ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms435.assocABC) ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_3_5_row_1_0_3 : (left0Middle4 3 5) ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms435.assocABC) ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_3_5_row_2_0_0 : (left0Middle4 3 5) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms435.assocABC) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_3_5_row_2_0_1 : (left0Middle4 3 5) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms435.assocABC) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_3_5_row_2_0_2 : (left0Middle4 3 5) ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms435.assocABC) ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_3_5_row_2_0_3 : (left0Middle4 3 5) ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms435.assocABC) ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_3_5_row_3_0_0 : (left0Middle4 3 5) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms435.assocABC) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_3_5_row_3_0_1 : (left0Middle4 3 5) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms435.assocABC) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_3_5_row_3_0_2 : (left0Middle4 3 5) ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms435.assocABC) ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_3_5_row_3_0_3 : (left0Middle4 3 5) ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms435.assocABC) ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_3_5_row_4_0_0 : (left0Middle4 3 5) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms435.assocABC) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_3_5_row_4_0_1 : (left0Middle4 3 5) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms435.assocABC) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_3_5_row_4_0_2 : (left0Middle4 3 5) ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms435.assocABC) ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_3_5_row_4_0_3 : (left0Middle4 3 5) ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms435.assocABC) ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_3_5_row_5_0_0 : (left0Middle4 3 5) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms435.assocABC) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_3_5_row_5_0_1 : (left0Middle4 3 5) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms435.assocABC) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_3_5_row_5_0_2 : (left0Middle4 3 5) ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms435.assocABC) ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_3_5_row_5_0_3 : (left0Middle4 3 5) ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms435.assocABC) ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_3_5_row_6_0_0 : (left0Middle4 3 5) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms435.assocABC) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_3_5_row_6_0_1 : (left0Middle4 3 5) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms435.assocABC) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_3_5_row_6_0_2 : (left0Middle4 3 5) ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms435.assocABC) ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_3_5_row_6_0_3 : (left0Middle4 3 5) ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms435.assocABC) ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_3_5_row_7_0_0 : (left0Middle4 3 5) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms435.assocABC) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_3_5_row_7_0_1 : (left0Middle4 3 5) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms435.assocABC) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_3_5_row_7_0_2 : (left0Middle4 3 5) ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms435.assocABC) ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_3_5_row_7_0_3 : (left0Middle4 3 5) ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms435.assocABC) ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_3_5_checked : left0Middle4 3 5 = HexagonAtoms435.assocABC := by
  funext r
  fin_cases r
  · exact left0Middle4_eq_case_3_5_row_0_0_0
  · exact left0Middle4_eq_case_3_5_row_0_0_1
  · exact left0Middle4_eq_case_3_5_row_0_0_2
  · exact left0Middle4_eq_case_3_5_row_0_0_3
  · exact left0Middle4_eq_case_3_5_row_1_0_0
  · exact left0Middle4_eq_case_3_5_row_1_0_1
  · exact left0Middle4_eq_case_3_5_row_1_0_2
  · exact left0Middle4_eq_case_3_5_row_1_0_3
  · exact left0Middle4_eq_case_3_5_row_2_0_0
  · exact left0Middle4_eq_case_3_5_row_2_0_1
  · exact left0Middle4_eq_case_3_5_row_2_0_2
  · exact left0Middle4_eq_case_3_5_row_2_0_3
  · exact left0Middle4_eq_case_3_5_row_3_0_0
  · exact left0Middle4_eq_case_3_5_row_3_0_1
  · exact left0Middle4_eq_case_3_5_row_3_0_2
  · exact left0Middle4_eq_case_3_5_row_3_0_3
  · exact left0Middle4_eq_case_3_5_row_4_0_0
  · exact left0Middle4_eq_case_3_5_row_4_0_1
  · exact left0Middle4_eq_case_3_5_row_4_0_2
  · exact left0Middle4_eq_case_3_5_row_4_0_3
  · exact left0Middle4_eq_case_3_5_row_5_0_0
  · exact left0Middle4_eq_case_3_5_row_5_0_1
  · exact left0Middle4_eq_case_3_5_row_5_0_2
  · exact left0Middle4_eq_case_3_5_row_5_0_3
  · exact left0Middle4_eq_case_3_5_row_6_0_0
  · exact left0Middle4_eq_case_3_5_row_6_0_1
  · exact left0Middle4_eq_case_3_5_row_6_0_2
  · exact left0Middle4_eq_case_3_5_row_6_0_3
  · exact left0Middle4_eq_case_3_5_row_7_0_0
  · exact left0Middle4_eq_case_3_5_row_7_0_1
  · exact left0Middle4_eq_case_3_5_row_7_0_2
  · exact left0Middle4_eq_case_3_5_row_7_0_3

set_option backward.isDefEq.respectTransparency false in
theorem left0Middle4_eq_case_3_5 : left0Middle4 3 5 = outerRightZ 4 3 5 * associatorZ 4 3 5 := by
  simpa only [HexagonAtoms435.assocABC_eq,
    HexagonAtoms435.outerABC_eq,
    HexagonAtoms435.assocBAC_eq,
    HexagonAtoms435.innerABC_eq,
    HexagonAtoms435.innerRightABC_eq,
    HexagonAtoms435.inverseACB_eq,
    HexagonAtoms435.innerACB_eq,
    HexagonAtoms435.assocBCA_eq,
    HexagonAtoms435.innerRightBAC_eq,
    HexagonAtoms435.assocCAB_eq,
    HexagonAtoms435.outerLeftABC_eq,
    HexagonRowColumn435.product0_eq,
    HexagonRowColumn435.product1_eq,
    HexagonRowColumn435.product2_eq,
    HexagonRowColumn435.product3_eq,
    HexagonRowColumn435.product4_eq,
    HexagonRowColumn435.product5_eq,
    HexagonRowColumn435.product6_eq,
    HexagonRowColumn435.product7_eq] using left0Middle4_eq_case_3_5_checked

private theorem left1Middle4_eq_case_3_5_row_0_0_0 : (left1Middle4 3 5) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms435.assocBAC) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_3_5_row_0_0_1 : (left1Middle4 3 5) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms435.assocBAC) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_3_5_row_0_0_2 : (left1Middle4 3 5) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms435.assocBAC) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_3_5_row_0_0_3 : (left1Middle4 3 5) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms435.assocBAC) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_3_5_row_0_1_0 : (left1Middle4 3 5) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms435.assocBAC) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_3_5_row_0_1_1 : (left1Middle4 3 5) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms435.assocBAC) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_3_5_row_0_1_2 : (left1Middle4 3 5) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms435.assocBAC) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_3_5_row_0_1_3 : (left1Middle4 3 5) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms435.assocBAC) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_3_5_row_1_0_0 : (left1Middle4 3 5) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms435.assocBAC) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_3_5_row_1_0_1 : (left1Middle4 3 5) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms435.assocBAC) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_3_5_row_1_0_2 : (left1Middle4 3 5) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms435.assocBAC) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_3_5_row_1_0_3 : (left1Middle4 3 5) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms435.assocBAC) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_3_5_row_1_1_0 : (left1Middle4 3 5) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms435.assocBAC) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_3_5_row_1_1_1 : (left1Middle4 3 5) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms435.assocBAC) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_3_5_row_1_1_2 : (left1Middle4 3 5) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms435.assocBAC) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_3_5_row_1_1_3 : (left1Middle4 3 5) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms435.assocBAC) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_3_5_row_2_0_0 : (left1Middle4 3 5) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms435.assocBAC) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_3_5_row_2_0_1 : (left1Middle4 3 5) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms435.assocBAC) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_3_5_row_2_0_2 : (left1Middle4 3 5) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms435.assocBAC) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_3_5_row_2_0_3 : (left1Middle4 3 5) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms435.assocBAC) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_3_5_row_2_1_0 : (left1Middle4 3 5) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms435.assocBAC) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_3_5_row_2_1_1 : (left1Middle4 3 5) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms435.assocBAC) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_3_5_row_2_1_2 : (left1Middle4 3 5) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms435.assocBAC) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_3_5_row_2_1_3 : (left1Middle4 3 5) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms435.assocBAC) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_3_5_row_3_0_0 : (left1Middle4 3 5) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms435.assocBAC) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_3_5_row_3_0_1 : (left1Middle4 3 5) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms435.assocBAC) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_3_5_row_3_0_2 : (left1Middle4 3 5) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms435.assocBAC) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_3_5_row_3_0_3 : (left1Middle4 3 5) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms435.assocBAC) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_3_5_row_3_1_0 : (left1Middle4 3 5) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms435.assocBAC) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_3_5_row_3_1_1 : (left1Middle4 3 5) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms435.assocBAC) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_3_5_row_3_1_2 : (left1Middle4 3 5) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms435.assocBAC) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_3_5_row_3_1_3 : (left1Middle4 3 5) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms435.assocBAC) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_3_5_checked : left1Middle4 3 5 = HexagonAtoms435.assocBAC := by
  funext r
  fin_cases r
  · exact left1Middle4_eq_case_3_5_row_0_0_0
  · exact left1Middle4_eq_case_3_5_row_0_0_1
  · exact left1Middle4_eq_case_3_5_row_0_0_2
  · exact left1Middle4_eq_case_3_5_row_0_0_3
  · exact left1Middle4_eq_case_3_5_row_0_1_0
  · exact left1Middle4_eq_case_3_5_row_0_1_1
  · exact left1Middle4_eq_case_3_5_row_0_1_2
  · exact left1Middle4_eq_case_3_5_row_0_1_3
  · exact left1Middle4_eq_case_3_5_row_1_0_0
  · exact left1Middle4_eq_case_3_5_row_1_0_1
  · exact left1Middle4_eq_case_3_5_row_1_0_2
  · exact left1Middle4_eq_case_3_5_row_1_0_3
  · exact left1Middle4_eq_case_3_5_row_1_1_0
  · exact left1Middle4_eq_case_3_5_row_1_1_1
  · exact left1Middle4_eq_case_3_5_row_1_1_2
  · exact left1Middle4_eq_case_3_5_row_1_1_3
  · exact left1Middle4_eq_case_3_5_row_2_0_0
  · exact left1Middle4_eq_case_3_5_row_2_0_1
  · exact left1Middle4_eq_case_3_5_row_2_0_2
  · exact left1Middle4_eq_case_3_5_row_2_0_3
  · exact left1Middle4_eq_case_3_5_row_2_1_0
  · exact left1Middle4_eq_case_3_5_row_2_1_1
  · exact left1Middle4_eq_case_3_5_row_2_1_2
  · exact left1Middle4_eq_case_3_5_row_2_1_3
  · exact left1Middle4_eq_case_3_5_row_3_0_0
  · exact left1Middle4_eq_case_3_5_row_3_0_1
  · exact left1Middle4_eq_case_3_5_row_3_0_2
  · exact left1Middle4_eq_case_3_5_row_3_0_3
  · exact left1Middle4_eq_case_3_5_row_3_1_0
  · exact left1Middle4_eq_case_3_5_row_3_1_1
  · exact left1Middle4_eq_case_3_5_row_3_1_2
  · exact left1Middle4_eq_case_3_5_row_3_1_3

set_option backward.isDefEq.respectTransparency false in
theorem left1Middle4_eq_case_3_5 : left1Middle4 3 5 = associatorZ 3 4 5 * innerLeftZ 4 3 5 := by
  simpa only [HexagonAtoms435.assocABC_eq,
    HexagonAtoms435.outerABC_eq,
    HexagonAtoms435.assocBAC_eq,
    HexagonAtoms435.innerABC_eq,
    HexagonAtoms435.innerRightABC_eq,
    HexagonAtoms435.inverseACB_eq,
    HexagonAtoms435.innerACB_eq,
    HexagonAtoms435.assocBCA_eq,
    HexagonAtoms435.innerRightBAC_eq,
    HexagonAtoms435.assocCAB_eq,
    HexagonAtoms435.outerLeftABC_eq,
    HexagonRowColumn435.product0_eq,
    HexagonRowColumn435.product1_eq,
    HexagonRowColumn435.product2_eq,
    HexagonRowColumn435.product3_eq,
    HexagonRowColumn435.product4_eq,
    HexagonRowColumn435.product5_eq,
    HexagonRowColumn435.product6_eq,
    HexagonRowColumn435.product7_eq] using left1Middle4_eq_case_3_5_checked

private theorem right0Middle4_eq_case_3_5_row_0_0_0 : (right0Middle4 3 5) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms435.assocABC) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_3_5_row_0_0_1 : (right0Middle4 3 5) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms435.assocABC) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_3_5_row_0_0_2 : (right0Middle4 3 5) ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms435.assocABC) ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_3_5_row_0_0_3 : (right0Middle4 3 5) ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms435.assocABC) ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_3_5_row_1_0_0 : (right0Middle4 3 5) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms435.assocABC) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_3_5_row_1_0_1 : (right0Middle4 3 5) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms435.assocABC) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_3_5_row_1_0_2 : (right0Middle4 3 5) ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms435.assocABC) ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_3_5_row_1_0_3 : (right0Middle4 3 5) ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms435.assocABC) ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_3_5_row_2_0_0 : (right0Middle4 3 5) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms435.assocABC) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_3_5_row_2_0_1 : (right0Middle4 3 5) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms435.assocABC) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_3_5_row_2_0_2 : (right0Middle4 3 5) ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms435.assocABC) ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_3_5_row_2_0_3 : (right0Middle4 3 5) ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms435.assocABC) ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_3_5_row_3_0_0 : (right0Middle4 3 5) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms435.assocABC) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_3_5_row_3_0_1 : (right0Middle4 3 5) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms435.assocABC) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_3_5_row_3_0_2 : (right0Middle4 3 5) ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms435.assocABC) ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_3_5_row_3_0_3 : (right0Middle4 3 5) ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms435.assocABC) ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_3_5_row_4_0_0 : (right0Middle4 3 5) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms435.assocABC) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_3_5_row_4_0_1 : (right0Middle4 3 5) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms435.assocABC) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_3_5_row_4_0_2 : (right0Middle4 3 5) ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms435.assocABC) ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_3_5_row_4_0_3 : (right0Middle4 3 5) ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms435.assocABC) ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_3_5_row_5_0_0 : (right0Middle4 3 5) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms435.assocABC) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_3_5_row_5_0_1 : (right0Middle4 3 5) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms435.assocABC) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_3_5_row_5_0_2 : (right0Middle4 3 5) ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms435.assocABC) ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_3_5_row_5_0_3 : (right0Middle4 3 5) ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms435.assocABC) ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_3_5_row_6_0_0 : (right0Middle4 3 5) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms435.assocABC) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_3_5_row_6_0_1 : (right0Middle4 3 5) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms435.assocABC) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_3_5_row_6_0_2 : (right0Middle4 3 5) ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms435.assocABC) ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_3_5_row_6_0_3 : (right0Middle4 3 5) ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms435.assocABC) ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_3_5_row_7_0_0 : (right0Middle4 3 5) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms435.assocABC) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_3_5_row_7_0_1 : (right0Middle4 3 5) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms435.assocABC) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_3_5_row_7_0_2 : (right0Middle4 3 5) ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms435.assocABC) ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_3_5_row_7_0_3 : (right0Middle4 3 5) ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms435.assocABC) ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_3_5_checked : right0Middle4 3 5 = HexagonAtoms435.assocABC := by
  funext r
  fin_cases r
  · exact right0Middle4_eq_case_3_5_row_0_0_0
  · exact right0Middle4_eq_case_3_5_row_0_0_1
  · exact right0Middle4_eq_case_3_5_row_0_0_2
  · exact right0Middle4_eq_case_3_5_row_0_0_3
  · exact right0Middle4_eq_case_3_5_row_1_0_0
  · exact right0Middle4_eq_case_3_5_row_1_0_1
  · exact right0Middle4_eq_case_3_5_row_1_0_2
  · exact right0Middle4_eq_case_3_5_row_1_0_3
  · exact right0Middle4_eq_case_3_5_row_2_0_0
  · exact right0Middle4_eq_case_3_5_row_2_0_1
  · exact right0Middle4_eq_case_3_5_row_2_0_2
  · exact right0Middle4_eq_case_3_5_row_2_0_3
  · exact right0Middle4_eq_case_3_5_row_3_0_0
  · exact right0Middle4_eq_case_3_5_row_3_0_1
  · exact right0Middle4_eq_case_3_5_row_3_0_2
  · exact right0Middle4_eq_case_3_5_row_3_0_3
  · exact right0Middle4_eq_case_3_5_row_4_0_0
  · exact right0Middle4_eq_case_3_5_row_4_0_1
  · exact right0Middle4_eq_case_3_5_row_4_0_2
  · exact right0Middle4_eq_case_3_5_row_4_0_3
  · exact right0Middle4_eq_case_3_5_row_5_0_0
  · exact right0Middle4_eq_case_3_5_row_5_0_1
  · exact right0Middle4_eq_case_3_5_row_5_0_2
  · exact right0Middle4_eq_case_3_5_row_5_0_3
  · exact right0Middle4_eq_case_3_5_row_6_0_0
  · exact right0Middle4_eq_case_3_5_row_6_0_1
  · exact right0Middle4_eq_case_3_5_row_6_0_2
  · exact right0Middle4_eq_case_3_5_row_6_0_3
  · exact right0Middle4_eq_case_3_5_row_7_0_0
  · exact right0Middle4_eq_case_3_5_row_7_0_1
  · exact right0Middle4_eq_case_3_5_row_7_0_2
  · exact right0Middle4_eq_case_3_5_row_7_0_3

set_option backward.isDefEq.respectTransparency false in
theorem right0Middle4_eq_case_3_5 : right0Middle4 3 5 = innerRightZ 4 3 5 * associatorZ 4 3 5 := by
  simpa only [HexagonAtoms435.assocABC_eq,
    HexagonAtoms435.outerABC_eq,
    HexagonAtoms435.assocBAC_eq,
    HexagonAtoms435.innerABC_eq,
    HexagonAtoms435.innerRightABC_eq,
    HexagonAtoms435.inverseACB_eq,
    HexagonAtoms435.innerACB_eq,
    HexagonAtoms435.assocBCA_eq,
    HexagonAtoms435.innerRightBAC_eq,
    HexagonAtoms435.assocCAB_eq,
    HexagonAtoms435.outerLeftABC_eq,
    HexagonRowColumn435.product0_eq,
    HexagonRowColumn435.product1_eq,
    HexagonRowColumn435.product2_eq,
    HexagonRowColumn435.product3_eq,
    HexagonRowColumn435.product4_eq,
    HexagonRowColumn435.product5_eq,
    HexagonRowColumn435.product6_eq,
    HexagonRowColumn435.product7_eq] using right0Middle4_eq_case_3_5_checked

private theorem right1Middle4_eq_case_3_5_row_0_0_0 : (right1Middle4 3 5) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn435.rows_inverseACB HexagonRowColumn435.cols_right0) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_3_5_row_0_0_1 : (right1Middle4 3 5) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn435.rows_inverseACB HexagonRowColumn435.cols_right0) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_3_5_row_0_0_2 : (right1Middle4 3 5) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn435.rows_inverseACB HexagonRowColumn435.cols_right0) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_3_5_row_0_0_3 : (right1Middle4 3 5) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn435.rows_inverseACB HexagonRowColumn435.cols_right0) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_3_5_row_0_1_0 : (right1Middle4 3 5) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn435.rows_inverseACB HexagonRowColumn435.cols_right0) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_3_5_row_0_1_1 : (right1Middle4 3 5) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn435.rows_inverseACB HexagonRowColumn435.cols_right0) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_3_5_row_0_1_2 : (right1Middle4 3 5) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn435.rows_inverseACB HexagonRowColumn435.cols_right0) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_3_5_row_0_1_3 : (right1Middle4 3 5) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn435.rows_inverseACB HexagonRowColumn435.cols_right0) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_3_5_row_1_0_0 : (right1Middle4 3 5) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn435.rows_inverseACB HexagonRowColumn435.cols_right0) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_3_5_row_1_0_1 : (right1Middle4 3 5) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn435.rows_inverseACB HexagonRowColumn435.cols_right0) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_3_5_row_1_0_2 : (right1Middle4 3 5) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn435.rows_inverseACB HexagonRowColumn435.cols_right0) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_3_5_row_1_0_3 : (right1Middle4 3 5) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn435.rows_inverseACB HexagonRowColumn435.cols_right0) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_3_5_row_1_1_0 : (right1Middle4 3 5) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn435.rows_inverseACB HexagonRowColumn435.cols_right0) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_3_5_row_1_1_1 : (right1Middle4 3 5) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn435.rows_inverseACB HexagonRowColumn435.cols_right0) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_3_5_row_1_1_2 : (right1Middle4 3 5) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn435.rows_inverseACB HexagonRowColumn435.cols_right0) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_3_5_row_1_1_3 : (right1Middle4 3 5) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn435.rows_inverseACB HexagonRowColumn435.cols_right0) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_3_5_row_2_0_0 : (right1Middle4 3 5) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn435.rows_inverseACB HexagonRowColumn435.cols_right0) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_3_5_row_2_0_1 : (right1Middle4 3 5) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn435.rows_inverseACB HexagonRowColumn435.cols_right0) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_3_5_row_2_0_2 : (right1Middle4 3 5) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn435.rows_inverseACB HexagonRowColumn435.cols_right0) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_3_5_row_2_0_3 : (right1Middle4 3 5) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn435.rows_inverseACB HexagonRowColumn435.cols_right0) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_3_5_row_2_1_0 : (right1Middle4 3 5) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn435.rows_inverseACB HexagonRowColumn435.cols_right0) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_3_5_row_2_1_1 : (right1Middle4 3 5) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn435.rows_inverseACB HexagonRowColumn435.cols_right0) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_3_5_row_2_1_2 : (right1Middle4 3 5) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn435.rows_inverseACB HexagonRowColumn435.cols_right0) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_3_5_row_2_1_3 : (right1Middle4 3 5) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn435.rows_inverseACB HexagonRowColumn435.cols_right0) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_3_5_row_3_0_0 : (right1Middle4 3 5) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn435.rows_inverseACB HexagonRowColumn435.cols_right0) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_3_5_row_3_0_1 : (right1Middle4 3 5) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn435.rows_inverseACB HexagonRowColumn435.cols_right0) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_3_5_row_3_0_2 : (right1Middle4 3 5) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn435.rows_inverseACB HexagonRowColumn435.cols_right0) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_3_5_row_3_0_3 : (right1Middle4 3 5) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn435.rows_inverseACB HexagonRowColumn435.cols_right0) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_3_5_row_3_1_0 : (right1Middle4 3 5) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn435.rows_inverseACB HexagonRowColumn435.cols_right0) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_3_5_row_3_1_1 : (right1Middle4 3 5) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn435.rows_inverseACB HexagonRowColumn435.cols_right0) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_3_5_row_3_1_2 : (right1Middle4 3 5) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn435.rows_inverseACB HexagonRowColumn435.cols_right0) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_3_5_row_3_1_3 : (right1Middle4 3 5) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn435.rows_inverseACB HexagonRowColumn435.cols_right0) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_3_5_checked : right1Middle4 3 5 = rowColumnMul HexagonRowColumn435.rows_inverseACB HexagonRowColumn435.cols_right0 := by
  funext r
  fin_cases r
  · exact right1Middle4_eq_case_3_5_row_0_0_0
  · exact right1Middle4_eq_case_3_5_row_0_0_1
  · exact right1Middle4_eq_case_3_5_row_0_0_2
  · exact right1Middle4_eq_case_3_5_row_0_0_3
  · exact right1Middle4_eq_case_3_5_row_0_1_0
  · exact right1Middle4_eq_case_3_5_row_0_1_1
  · exact right1Middle4_eq_case_3_5_row_0_1_2
  · exact right1Middle4_eq_case_3_5_row_0_1_3
  · exact right1Middle4_eq_case_3_5_row_1_0_0
  · exact right1Middle4_eq_case_3_5_row_1_0_1
  · exact right1Middle4_eq_case_3_5_row_1_0_2
  · exact right1Middle4_eq_case_3_5_row_1_0_3
  · exact right1Middle4_eq_case_3_5_row_1_1_0
  · exact right1Middle4_eq_case_3_5_row_1_1_1
  · exact right1Middle4_eq_case_3_5_row_1_1_2
  · exact right1Middle4_eq_case_3_5_row_1_1_3
  · exact right1Middle4_eq_case_3_5_row_2_0_0
  · exact right1Middle4_eq_case_3_5_row_2_0_1
  · exact right1Middle4_eq_case_3_5_row_2_0_2
  · exact right1Middle4_eq_case_3_5_row_2_0_3
  · exact right1Middle4_eq_case_3_5_row_2_1_0
  · exact right1Middle4_eq_case_3_5_row_2_1_1
  · exact right1Middle4_eq_case_3_5_row_2_1_2
  · exact right1Middle4_eq_case_3_5_row_2_1_3
  · exact right1Middle4_eq_case_3_5_row_3_0_0
  · exact right1Middle4_eq_case_3_5_row_3_0_1
  · exact right1Middle4_eq_case_3_5_row_3_0_2
  · exact right1Middle4_eq_case_3_5_row_3_0_3
  · exact right1Middle4_eq_case_3_5_row_3_1_0
  · exact right1Middle4_eq_case_3_5_row_3_1_1
  · exact right1Middle4_eq_case_3_5_row_3_1_2
  · exact right1Middle4_eq_case_3_5_row_3_1_3

set_option backward.isDefEq.respectTransparency false in
theorem right1Middle4_eq_case_3_5 : right1Middle4 3 5 = associatorInverseZ 4 5 3 * right0Middle4 3 5 := by
  simpa only [HexagonAtoms435.assocABC_eq,
    HexagonAtoms435.outerABC_eq,
    HexagonAtoms435.assocBAC_eq,
    HexagonAtoms435.innerABC_eq,
    HexagonAtoms435.innerRightABC_eq,
    HexagonAtoms435.inverseACB_eq,
    HexagonAtoms435.innerACB_eq,
    HexagonAtoms435.assocBCA_eq,
    HexagonAtoms435.innerRightBAC_eq,
    HexagonAtoms435.assocCAB_eq,
    HexagonAtoms435.outerLeftABC_eq,
    HexagonRowColumn435.product0_eq,
    HexagonRowColumn435.product1_eq,
    HexagonRowColumn435.product2_eq,
    HexagonRowColumn435.product3_eq,
    HexagonRowColumn435.product4_eq,
    HexagonRowColumn435.product5_eq,
    HexagonRowColumn435.product6_eq,
    HexagonRowColumn435.product7_eq] using right1Middle4_eq_case_3_5_checked

private theorem right2Middle4_eq_case_3_5_row_0_0_0 : (right2Middle4 3 5) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (right1Middle4 3 5) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_3_5_row_0_0_1 : (right2Middle4 3 5) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (right1Middle4 3 5) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_3_5_row_0_0_2 : (right2Middle4 3 5) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (right1Middle4 3 5) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_3_5_row_0_0_3 : (right2Middle4 3 5) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (right1Middle4 3 5) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_3_5_row_0_1_0 : (right2Middle4 3 5) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (right1Middle4 3 5) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_3_5_row_0_1_1 : (right2Middle4 3 5) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (right1Middle4 3 5) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_3_5_row_0_1_2 : (right2Middle4 3 5) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (right1Middle4 3 5) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_3_5_row_0_1_3 : (right2Middle4 3 5) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (right1Middle4 3 5) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_3_5_row_1_0_0 : (right2Middle4 3 5) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (right1Middle4 3 5) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_3_5_row_1_0_1 : (right2Middle4 3 5) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (right1Middle4 3 5) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_3_5_row_1_0_2 : (right2Middle4 3 5) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (right1Middle4 3 5) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_3_5_row_1_0_3 : (right2Middle4 3 5) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (right1Middle4 3 5) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_3_5_row_1_1_0 : (right2Middle4 3 5) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (right1Middle4 3 5) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_3_5_row_1_1_1 : (right2Middle4 3 5) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (right1Middle4 3 5) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_3_5_row_1_1_2 : (right2Middle4 3 5) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (right1Middle4 3 5) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_3_5_row_1_1_3 : (right2Middle4 3 5) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (right1Middle4 3 5) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_3_5_row_2_0_0 : (right2Middle4 3 5) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (right1Middle4 3 5) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_3_5_row_2_0_1 : (right2Middle4 3 5) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (right1Middle4 3 5) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_3_5_row_2_0_2 : (right2Middle4 3 5) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (right1Middle4 3 5) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_3_5_row_2_0_3 : (right2Middle4 3 5) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (right1Middle4 3 5) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_3_5_row_2_1_0 : (right2Middle4 3 5) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (right1Middle4 3 5) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_3_5_row_2_1_1 : (right2Middle4 3 5) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (right1Middle4 3 5) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_3_5_row_2_1_2 : (right2Middle4 3 5) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (right1Middle4 3 5) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_3_5_row_2_1_3 : (right2Middle4 3 5) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (right1Middle4 3 5) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_3_5_row_3_0_0 : (right2Middle4 3 5) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (right1Middle4 3 5) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_3_5_row_3_0_1 : (right2Middle4 3 5) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (right1Middle4 3 5) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_3_5_row_3_0_2 : (right2Middle4 3 5) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (right1Middle4 3 5) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_3_5_row_3_0_3 : (right2Middle4 3 5) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (right1Middle4 3 5) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_3_5_row_3_1_0 : (right2Middle4 3 5) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (right1Middle4 3 5) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_3_5_row_3_1_1 : (right2Middle4 3 5) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (right1Middle4 3 5) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_3_5_row_3_1_2 : (right2Middle4 3 5) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (right1Middle4 3 5) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_3_5_row_3_1_3 : (right2Middle4 3 5) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (right1Middle4 3 5) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_3_5_checked : right2Middle4 3 5 = right1Middle4 3 5 := by
  funext r
  fin_cases r
  · exact right2Middle4_eq_case_3_5_row_0_0_0
  · exact right2Middle4_eq_case_3_5_row_0_0_1
  · exact right2Middle4_eq_case_3_5_row_0_0_2
  · exact right2Middle4_eq_case_3_5_row_0_0_3
  · exact right2Middle4_eq_case_3_5_row_0_1_0
  · exact right2Middle4_eq_case_3_5_row_0_1_1
  · exact right2Middle4_eq_case_3_5_row_0_1_2
  · exact right2Middle4_eq_case_3_5_row_0_1_3
  · exact right2Middle4_eq_case_3_5_row_1_0_0
  · exact right2Middle4_eq_case_3_5_row_1_0_1
  · exact right2Middle4_eq_case_3_5_row_1_0_2
  · exact right2Middle4_eq_case_3_5_row_1_0_3
  · exact right2Middle4_eq_case_3_5_row_1_1_0
  · exact right2Middle4_eq_case_3_5_row_1_1_1
  · exact right2Middle4_eq_case_3_5_row_1_1_2
  · exact right2Middle4_eq_case_3_5_row_1_1_3
  · exact right2Middle4_eq_case_3_5_row_2_0_0
  · exact right2Middle4_eq_case_3_5_row_2_0_1
  · exact right2Middle4_eq_case_3_5_row_2_0_2
  · exact right2Middle4_eq_case_3_5_row_2_0_3
  · exact right2Middle4_eq_case_3_5_row_2_1_0
  · exact right2Middle4_eq_case_3_5_row_2_1_1
  · exact right2Middle4_eq_case_3_5_row_2_1_2
  · exact right2Middle4_eq_case_3_5_row_2_1_3
  · exact right2Middle4_eq_case_3_5_row_3_0_0
  · exact right2Middle4_eq_case_3_5_row_3_0_1
  · exact right2Middle4_eq_case_3_5_row_3_0_2
  · exact right2Middle4_eq_case_3_5_row_3_0_3
  · exact right2Middle4_eq_case_3_5_row_3_1_0
  · exact right2Middle4_eq_case_3_5_row_3_1_1
  · exact right2Middle4_eq_case_3_5_row_3_1_2
  · exact right2Middle4_eq_case_3_5_row_3_1_3

set_option backward.isDefEq.respectTransparency false in
theorem right2Middle4_eq_case_3_5 : right2Middle4 3 5 = innerLeftZ 4 5 3 * right1Middle4 3 5 := by
  simpa only [HexagonAtoms435.assocABC_eq,
    HexagonAtoms435.outerABC_eq,
    HexagonAtoms435.assocBAC_eq,
    HexagonAtoms435.innerABC_eq,
    HexagonAtoms435.innerRightABC_eq,
    HexagonAtoms435.inverseACB_eq,
    HexagonAtoms435.innerACB_eq,
    HexagonAtoms435.assocBCA_eq,
    HexagonAtoms435.innerRightBAC_eq,
    HexagonAtoms435.assocCAB_eq,
    HexagonAtoms435.outerLeftABC_eq,
    HexagonRowColumn435.product0_eq,
    HexagonRowColumn435.product1_eq,
    HexagonRowColumn435.product2_eq,
    HexagonRowColumn435.product3_eq,
    HexagonRowColumn435.product4_eq,
    HexagonRowColumn435.product5_eq,
    HexagonRowColumn435.product6_eq,
    HexagonRowColumn435.product7_eq] using right2Middle4_eq_case_3_5_checked

private theorem leftFinal4_case_3_5_row_0_0_0 : (((-1 : ℤ) ^ (leftScaleBit 4 3 5).val * positiveScale (leftScaleExponent 4 3 5)) •
      (rowColumnMul HexagonRowColumn435.rows_assocBCA HexagonRowColumn435.cols_left0)) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 4 3 5) • (left1Middle4 3 5)) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal4_case_3_5_row_0_0_1 : (((-1 : ℤ) ^ (leftScaleBit 4 3 5).val * positiveScale (leftScaleExponent 4 3 5)) •
      (rowColumnMul HexagonRowColumn435.rows_assocBCA HexagonRowColumn435.cols_left0)) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 4 3 5) • (left1Middle4 3 5)) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal4_case_3_5_row_0_0_2 : (((-1 : ℤ) ^ (leftScaleBit 4 3 5).val * positiveScale (leftScaleExponent 4 3 5)) •
      (rowColumnMul HexagonRowColumn435.rows_assocBCA HexagonRowColumn435.cols_left0)) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 4 3 5) • (left1Middle4 3 5)) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal4_case_3_5_row_0_0_3 : (((-1 : ℤ) ^ (leftScaleBit 4 3 5).val * positiveScale (leftScaleExponent 4 3 5)) •
      (rowColumnMul HexagonRowColumn435.rows_assocBCA HexagonRowColumn435.cols_left0)) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 4 3 5) • (left1Middle4 3 5)) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal4_case_3_5_row_0_1_0 : (((-1 : ℤ) ^ (leftScaleBit 4 3 5).val * positiveScale (leftScaleExponent 4 3 5)) •
      (rowColumnMul HexagonRowColumn435.rows_assocBCA HexagonRowColumn435.cols_left0)) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 4 3 5) • (left1Middle4 3 5)) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal4_case_3_5_row_0_1_1 : (((-1 : ℤ) ^ (leftScaleBit 4 3 5).val * positiveScale (leftScaleExponent 4 3 5)) •
      (rowColumnMul HexagonRowColumn435.rows_assocBCA HexagonRowColumn435.cols_left0)) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 4 3 5) • (left1Middle4 3 5)) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal4_case_3_5_row_0_1_2 : (((-1 : ℤ) ^ (leftScaleBit 4 3 5).val * positiveScale (leftScaleExponent 4 3 5)) •
      (rowColumnMul HexagonRowColumn435.rows_assocBCA HexagonRowColumn435.cols_left0)) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 4 3 5) • (left1Middle4 3 5)) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal4_case_3_5_row_0_1_3 : (((-1 : ℤ) ^ (leftScaleBit 4 3 5).val * positiveScale (leftScaleExponent 4 3 5)) •
      (rowColumnMul HexagonRowColumn435.rows_assocBCA HexagonRowColumn435.cols_left0)) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 4 3 5) • (left1Middle4 3 5)) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal4_case_3_5_row_1_0_0 : (((-1 : ℤ) ^ (leftScaleBit 4 3 5).val * positiveScale (leftScaleExponent 4 3 5)) •
      (rowColumnMul HexagonRowColumn435.rows_assocBCA HexagonRowColumn435.cols_left0)) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 4 3 5) • (left1Middle4 3 5)) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal4_case_3_5_row_1_0_1 : (((-1 : ℤ) ^ (leftScaleBit 4 3 5).val * positiveScale (leftScaleExponent 4 3 5)) •
      (rowColumnMul HexagonRowColumn435.rows_assocBCA HexagonRowColumn435.cols_left0)) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 4 3 5) • (left1Middle4 3 5)) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal4_case_3_5_row_1_0_2 : (((-1 : ℤ) ^ (leftScaleBit 4 3 5).val * positiveScale (leftScaleExponent 4 3 5)) •
      (rowColumnMul HexagonRowColumn435.rows_assocBCA HexagonRowColumn435.cols_left0)) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 4 3 5) • (left1Middle4 3 5)) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal4_case_3_5_row_1_0_3 : (((-1 : ℤ) ^ (leftScaleBit 4 3 5).val * positiveScale (leftScaleExponent 4 3 5)) •
      (rowColumnMul HexagonRowColumn435.rows_assocBCA HexagonRowColumn435.cols_left0)) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 4 3 5) • (left1Middle4 3 5)) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal4_case_3_5_row_1_1_0 : (((-1 : ℤ) ^ (leftScaleBit 4 3 5).val * positiveScale (leftScaleExponent 4 3 5)) •
      (rowColumnMul HexagonRowColumn435.rows_assocBCA HexagonRowColumn435.cols_left0)) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 4 3 5) • (left1Middle4 3 5)) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal4_case_3_5_row_1_1_1 : (((-1 : ℤ) ^ (leftScaleBit 4 3 5).val * positiveScale (leftScaleExponent 4 3 5)) •
      (rowColumnMul HexagonRowColumn435.rows_assocBCA HexagonRowColumn435.cols_left0)) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 4 3 5) • (left1Middle4 3 5)) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal4_case_3_5_row_1_1_2 : (((-1 : ℤ) ^ (leftScaleBit 4 3 5).val * positiveScale (leftScaleExponent 4 3 5)) •
      (rowColumnMul HexagonRowColumn435.rows_assocBCA HexagonRowColumn435.cols_left0)) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 4 3 5) • (left1Middle4 3 5)) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal4_case_3_5_row_1_1_3 : (((-1 : ℤ) ^ (leftScaleBit 4 3 5).val * positiveScale (leftScaleExponent 4 3 5)) •
      (rowColumnMul HexagonRowColumn435.rows_assocBCA HexagonRowColumn435.cols_left0)) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 4 3 5) • (left1Middle4 3 5)) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal4_case_3_5_row_2_0_0 : (((-1 : ℤ) ^ (leftScaleBit 4 3 5).val * positiveScale (leftScaleExponent 4 3 5)) •
      (rowColumnMul HexagonRowColumn435.rows_assocBCA HexagonRowColumn435.cols_left0)) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 4 3 5) • (left1Middle4 3 5)) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal4_case_3_5_row_2_0_1 : (((-1 : ℤ) ^ (leftScaleBit 4 3 5).val * positiveScale (leftScaleExponent 4 3 5)) •
      (rowColumnMul HexagonRowColumn435.rows_assocBCA HexagonRowColumn435.cols_left0)) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 4 3 5) • (left1Middle4 3 5)) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal4_case_3_5_row_2_0_2 : (((-1 : ℤ) ^ (leftScaleBit 4 3 5).val * positiveScale (leftScaleExponent 4 3 5)) •
      (rowColumnMul HexagonRowColumn435.rows_assocBCA HexagonRowColumn435.cols_left0)) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 4 3 5) • (left1Middle4 3 5)) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal4_case_3_5_row_2_0_3 : (((-1 : ℤ) ^ (leftScaleBit 4 3 5).val * positiveScale (leftScaleExponent 4 3 5)) •
      (rowColumnMul HexagonRowColumn435.rows_assocBCA HexagonRowColumn435.cols_left0)) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 4 3 5) • (left1Middle4 3 5)) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal4_case_3_5_row_2_1_0 : (((-1 : ℤ) ^ (leftScaleBit 4 3 5).val * positiveScale (leftScaleExponent 4 3 5)) •
      (rowColumnMul HexagonRowColumn435.rows_assocBCA HexagonRowColumn435.cols_left0)) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 4 3 5) • (left1Middle4 3 5)) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal4_case_3_5_row_2_1_1 : (((-1 : ℤ) ^ (leftScaleBit 4 3 5).val * positiveScale (leftScaleExponent 4 3 5)) •
      (rowColumnMul HexagonRowColumn435.rows_assocBCA HexagonRowColumn435.cols_left0)) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 4 3 5) • (left1Middle4 3 5)) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal4_case_3_5_row_2_1_2 : (((-1 : ℤ) ^ (leftScaleBit 4 3 5).val * positiveScale (leftScaleExponent 4 3 5)) •
      (rowColumnMul HexagonRowColumn435.rows_assocBCA HexagonRowColumn435.cols_left0)) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 4 3 5) • (left1Middle4 3 5)) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal4_case_3_5_row_2_1_3 : (((-1 : ℤ) ^ (leftScaleBit 4 3 5).val * positiveScale (leftScaleExponent 4 3 5)) •
      (rowColumnMul HexagonRowColumn435.rows_assocBCA HexagonRowColumn435.cols_left0)) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 4 3 5) • (left1Middle4 3 5)) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal4_case_3_5_row_3_0_0 : (((-1 : ℤ) ^ (leftScaleBit 4 3 5).val * positiveScale (leftScaleExponent 4 3 5)) •
      (rowColumnMul HexagonRowColumn435.rows_assocBCA HexagonRowColumn435.cols_left0)) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 4 3 5) • (left1Middle4 3 5)) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal4_case_3_5_row_3_0_1 : (((-1 : ℤ) ^ (leftScaleBit 4 3 5).val * positiveScale (leftScaleExponent 4 3 5)) •
      (rowColumnMul HexagonRowColumn435.rows_assocBCA HexagonRowColumn435.cols_left0)) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 4 3 5) • (left1Middle4 3 5)) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal4_case_3_5_row_3_0_2 : (((-1 : ℤ) ^ (leftScaleBit 4 3 5).val * positiveScale (leftScaleExponent 4 3 5)) •
      (rowColumnMul HexagonRowColumn435.rows_assocBCA HexagonRowColumn435.cols_left0)) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 4 3 5) • (left1Middle4 3 5)) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal4_case_3_5_row_3_0_3 : (((-1 : ℤ) ^ (leftScaleBit 4 3 5).val * positiveScale (leftScaleExponent 4 3 5)) •
      (rowColumnMul HexagonRowColumn435.rows_assocBCA HexagonRowColumn435.cols_left0)) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 4 3 5) • (left1Middle4 3 5)) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal4_case_3_5_row_3_1_0 : (((-1 : ℤ) ^ (leftScaleBit 4 3 5).val * positiveScale (leftScaleExponent 4 3 5)) •
      (rowColumnMul HexagonRowColumn435.rows_assocBCA HexagonRowColumn435.cols_left0)) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 4 3 5) • (left1Middle4 3 5)) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal4_case_3_5_row_3_1_1 : (((-1 : ℤ) ^ (leftScaleBit 4 3 5).val * positiveScale (leftScaleExponent 4 3 5)) •
      (rowColumnMul HexagonRowColumn435.rows_assocBCA HexagonRowColumn435.cols_left0)) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 4 3 5) • (left1Middle4 3 5)) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal4_case_3_5_row_3_1_2 : (((-1 : ℤ) ^ (leftScaleBit 4 3 5).val * positiveScale (leftScaleExponent 4 3 5)) •
      (rowColumnMul HexagonRowColumn435.rows_assocBCA HexagonRowColumn435.cols_left0)) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 4 3 5) • (left1Middle4 3 5)) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal4_case_3_5_row_3_1_3 : (((-1 : ℤ) ^ (leftScaleBit 4 3 5).val * positiveScale (leftScaleExponent 4 3 5)) •
      (rowColumnMul HexagonRowColumn435.rows_assocBCA HexagonRowColumn435.cols_left0)) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 4 3 5) • (left1Middle4 3 5)) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal4_case_3_5_checked : ((-1 : ℤ) ^ (leftScaleBit 4 3 5).val * positiveScale (leftScaleExponent 4 3 5)) •
      (rowColumnMul HexagonRowColumn435.rows_assocBCA HexagonRowColumn435.cols_left0) = negativeScale (leftScaleExponent 4 3 5) • (left1Middle4 3 5) := by
  funext r
  fin_cases r
  · exact leftFinal4_case_3_5_row_0_0_0
  · exact leftFinal4_case_3_5_row_0_0_1
  · exact leftFinal4_case_3_5_row_0_0_2
  · exact leftFinal4_case_3_5_row_0_0_3
  · exact leftFinal4_case_3_5_row_0_1_0
  · exact leftFinal4_case_3_5_row_0_1_1
  · exact leftFinal4_case_3_5_row_0_1_2
  · exact leftFinal4_case_3_5_row_0_1_3
  · exact leftFinal4_case_3_5_row_1_0_0
  · exact leftFinal4_case_3_5_row_1_0_1
  · exact leftFinal4_case_3_5_row_1_0_2
  · exact leftFinal4_case_3_5_row_1_0_3
  · exact leftFinal4_case_3_5_row_1_1_0
  · exact leftFinal4_case_3_5_row_1_1_1
  · exact leftFinal4_case_3_5_row_1_1_2
  · exact leftFinal4_case_3_5_row_1_1_3
  · exact leftFinal4_case_3_5_row_2_0_0
  · exact leftFinal4_case_3_5_row_2_0_1
  · exact leftFinal4_case_3_5_row_2_0_2
  · exact leftFinal4_case_3_5_row_2_0_3
  · exact leftFinal4_case_3_5_row_2_1_0
  · exact leftFinal4_case_3_5_row_2_1_1
  · exact leftFinal4_case_3_5_row_2_1_2
  · exact leftFinal4_case_3_5_row_2_1_3
  · exact leftFinal4_case_3_5_row_3_0_0
  · exact leftFinal4_case_3_5_row_3_0_1
  · exact leftFinal4_case_3_5_row_3_0_2
  · exact leftFinal4_case_3_5_row_3_0_3
  · exact leftFinal4_case_3_5_row_3_1_0
  · exact leftFinal4_case_3_5_row_3_1_1
  · exact leftFinal4_case_3_5_row_3_1_2
  · exact leftFinal4_case_3_5_row_3_1_3

set_option backward.isDefEq.respectTransparency false in
theorem leftFinal4_case_3_5 : ((-1 : ℤ) ^ (leftScaleBit 4 3 5).val * positiveScale (leftScaleExponent 4 3 5)) •
      (associatorZ 3 5 4 * left0Middle4 3 5) = negativeScale (leftScaleExponent 4 3 5) • (innerRightZ 3 4 5 * left1Middle4 3 5) := by
  simpa only [HexagonAtoms435.assocABC_eq,
    HexagonAtoms435.outerABC_eq,
    HexagonAtoms435.assocBAC_eq,
    HexagonAtoms435.innerABC_eq,
    HexagonAtoms435.innerRightABC_eq,
    HexagonAtoms435.inverseACB_eq,
    HexagonAtoms435.innerACB_eq,
    HexagonAtoms435.assocBCA_eq,
    HexagonAtoms435.innerRightBAC_eq,
    HexagonAtoms435.assocCAB_eq,
    HexagonAtoms435.outerLeftABC_eq,
    HexagonRowColumn435.product0_eq,
    HexagonRowColumn435.product1_eq,
    HexagonRowColumn435.product2_eq,
    HexagonRowColumn435.product3_eq,
    HexagonRowColumn435.product4_eq,
    HexagonRowColumn435.product5_eq,
    HexagonRowColumn435.product6_eq,
    HexagonRowColumn435.product7_eq] using leftFinal4_case_3_5_checked

private theorem rightFinal4_case_3_5_row_0_0_0 : (((-1 : ℤ) ^ (rightScaleBit 4 3 5).val * positiveScale (rightScaleExponent 4 3 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 5 3 : ℤ)) • HexagonAtoms435.outerLeftABC) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 4 3 5) • (rowColumnMul HexagonRowColumn435.rows_assocCAB HexagonRowColumn435.cols_right2)) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal4_case_3_5_row_0_0_1 : (((-1 : ℤ) ^ (rightScaleBit 4 3 5).val * positiveScale (rightScaleExponent 4 3 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 5 3 : ℤ)) • HexagonAtoms435.outerLeftABC) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 4 3 5) • (rowColumnMul HexagonRowColumn435.rows_assocCAB HexagonRowColumn435.cols_right2)) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal4_case_3_5_row_0_0_2 : (((-1 : ℤ) ^ (rightScaleBit 4 3 5).val * positiveScale (rightScaleExponent 4 3 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 5 3 : ℤ)) • HexagonAtoms435.outerLeftABC) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 4 3 5) • (rowColumnMul HexagonRowColumn435.rows_assocCAB HexagonRowColumn435.cols_right2)) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal4_case_3_5_row_0_0_3 : (((-1 : ℤ) ^ (rightScaleBit 4 3 5).val * positiveScale (rightScaleExponent 4 3 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 5 3 : ℤ)) • HexagonAtoms435.outerLeftABC) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 4 3 5) • (rowColumnMul HexagonRowColumn435.rows_assocCAB HexagonRowColumn435.cols_right2)) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal4_case_3_5_row_0_1_0 : (((-1 : ℤ) ^ (rightScaleBit 4 3 5).val * positiveScale (rightScaleExponent 4 3 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 5 3 : ℤ)) • HexagonAtoms435.outerLeftABC) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 4 3 5) • (rowColumnMul HexagonRowColumn435.rows_assocCAB HexagonRowColumn435.cols_right2)) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal4_case_3_5_row_0_1_1 : (((-1 : ℤ) ^ (rightScaleBit 4 3 5).val * positiveScale (rightScaleExponent 4 3 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 5 3 : ℤ)) • HexagonAtoms435.outerLeftABC) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 4 3 5) • (rowColumnMul HexagonRowColumn435.rows_assocCAB HexagonRowColumn435.cols_right2)) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal4_case_3_5_row_0_1_2 : (((-1 : ℤ) ^ (rightScaleBit 4 3 5).val * positiveScale (rightScaleExponent 4 3 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 5 3 : ℤ)) • HexagonAtoms435.outerLeftABC) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 4 3 5) • (rowColumnMul HexagonRowColumn435.rows_assocCAB HexagonRowColumn435.cols_right2)) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal4_case_3_5_row_0_1_3 : (((-1 : ℤ) ^ (rightScaleBit 4 3 5).val * positiveScale (rightScaleExponent 4 3 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 5 3 : ℤ)) • HexagonAtoms435.outerLeftABC) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 4 3 5) • (rowColumnMul HexagonRowColumn435.rows_assocCAB HexagonRowColumn435.cols_right2)) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal4_case_3_5_row_1_0_0 : (((-1 : ℤ) ^ (rightScaleBit 4 3 5).val * positiveScale (rightScaleExponent 4 3 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 5 3 : ℤ)) • HexagonAtoms435.outerLeftABC) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 4 3 5) • (rowColumnMul HexagonRowColumn435.rows_assocCAB HexagonRowColumn435.cols_right2)) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal4_case_3_5_row_1_0_1 : (((-1 : ℤ) ^ (rightScaleBit 4 3 5).val * positiveScale (rightScaleExponent 4 3 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 5 3 : ℤ)) • HexagonAtoms435.outerLeftABC) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 4 3 5) • (rowColumnMul HexagonRowColumn435.rows_assocCAB HexagonRowColumn435.cols_right2)) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal4_case_3_5_row_1_0_2 : (((-1 : ℤ) ^ (rightScaleBit 4 3 5).val * positiveScale (rightScaleExponent 4 3 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 5 3 : ℤ)) • HexagonAtoms435.outerLeftABC) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 4 3 5) • (rowColumnMul HexagonRowColumn435.rows_assocCAB HexagonRowColumn435.cols_right2)) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal4_case_3_5_row_1_0_3 : (((-1 : ℤ) ^ (rightScaleBit 4 3 5).val * positiveScale (rightScaleExponent 4 3 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 5 3 : ℤ)) • HexagonAtoms435.outerLeftABC) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 4 3 5) • (rowColumnMul HexagonRowColumn435.rows_assocCAB HexagonRowColumn435.cols_right2)) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal4_case_3_5_row_1_1_0 : (((-1 : ℤ) ^ (rightScaleBit 4 3 5).val * positiveScale (rightScaleExponent 4 3 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 5 3 : ℤ)) • HexagonAtoms435.outerLeftABC) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 4 3 5) • (rowColumnMul HexagonRowColumn435.rows_assocCAB HexagonRowColumn435.cols_right2)) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal4_case_3_5_row_1_1_1 : (((-1 : ℤ) ^ (rightScaleBit 4 3 5).val * positiveScale (rightScaleExponent 4 3 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 5 3 : ℤ)) • HexagonAtoms435.outerLeftABC) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 4 3 5) • (rowColumnMul HexagonRowColumn435.rows_assocCAB HexagonRowColumn435.cols_right2)) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal4_case_3_5_row_1_1_2 : (((-1 : ℤ) ^ (rightScaleBit 4 3 5).val * positiveScale (rightScaleExponent 4 3 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 5 3 : ℤ)) • HexagonAtoms435.outerLeftABC) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 4 3 5) • (rowColumnMul HexagonRowColumn435.rows_assocCAB HexagonRowColumn435.cols_right2)) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal4_case_3_5_row_1_1_3 : (((-1 : ℤ) ^ (rightScaleBit 4 3 5).val * positiveScale (rightScaleExponent 4 3 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 5 3 : ℤ)) • HexagonAtoms435.outerLeftABC) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 4 3 5) • (rowColumnMul HexagonRowColumn435.rows_assocCAB HexagonRowColumn435.cols_right2)) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal4_case_3_5_row_2_0_0 : (((-1 : ℤ) ^ (rightScaleBit 4 3 5).val * positiveScale (rightScaleExponent 4 3 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 5 3 : ℤ)) • HexagonAtoms435.outerLeftABC) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 4 3 5) • (rowColumnMul HexagonRowColumn435.rows_assocCAB HexagonRowColumn435.cols_right2)) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal4_case_3_5_row_2_0_1 : (((-1 : ℤ) ^ (rightScaleBit 4 3 5).val * positiveScale (rightScaleExponent 4 3 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 5 3 : ℤ)) • HexagonAtoms435.outerLeftABC) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 4 3 5) • (rowColumnMul HexagonRowColumn435.rows_assocCAB HexagonRowColumn435.cols_right2)) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal4_case_3_5_row_2_0_2 : (((-1 : ℤ) ^ (rightScaleBit 4 3 5).val * positiveScale (rightScaleExponent 4 3 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 5 3 : ℤ)) • HexagonAtoms435.outerLeftABC) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 4 3 5) • (rowColumnMul HexagonRowColumn435.rows_assocCAB HexagonRowColumn435.cols_right2)) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal4_case_3_5_row_2_0_3 : (((-1 : ℤ) ^ (rightScaleBit 4 3 5).val * positiveScale (rightScaleExponent 4 3 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 5 3 : ℤ)) • HexagonAtoms435.outerLeftABC) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 4 3 5) • (rowColumnMul HexagonRowColumn435.rows_assocCAB HexagonRowColumn435.cols_right2)) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal4_case_3_5_row_2_1_0 : (((-1 : ℤ) ^ (rightScaleBit 4 3 5).val * positiveScale (rightScaleExponent 4 3 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 5 3 : ℤ)) • HexagonAtoms435.outerLeftABC) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 4 3 5) • (rowColumnMul HexagonRowColumn435.rows_assocCAB HexagonRowColumn435.cols_right2)) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal4_case_3_5_row_2_1_1 : (((-1 : ℤ) ^ (rightScaleBit 4 3 5).val * positiveScale (rightScaleExponent 4 3 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 5 3 : ℤ)) • HexagonAtoms435.outerLeftABC) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 4 3 5) • (rowColumnMul HexagonRowColumn435.rows_assocCAB HexagonRowColumn435.cols_right2)) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal4_case_3_5_row_2_1_2 : (((-1 : ℤ) ^ (rightScaleBit 4 3 5).val * positiveScale (rightScaleExponent 4 3 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 5 3 : ℤ)) • HexagonAtoms435.outerLeftABC) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 4 3 5) • (rowColumnMul HexagonRowColumn435.rows_assocCAB HexagonRowColumn435.cols_right2)) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal4_case_3_5_row_2_1_3 : (((-1 : ℤ) ^ (rightScaleBit 4 3 5).val * positiveScale (rightScaleExponent 4 3 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 5 3 : ℤ)) • HexagonAtoms435.outerLeftABC) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 4 3 5) • (rowColumnMul HexagonRowColumn435.rows_assocCAB HexagonRowColumn435.cols_right2)) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal4_case_3_5_row_3_0_0 : (((-1 : ℤ) ^ (rightScaleBit 4 3 5).val * positiveScale (rightScaleExponent 4 3 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 5 3 : ℤ)) • HexagonAtoms435.outerLeftABC) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 4 3 5) • (rowColumnMul HexagonRowColumn435.rows_assocCAB HexagonRowColumn435.cols_right2)) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal4_case_3_5_row_3_0_1 : (((-1 : ℤ) ^ (rightScaleBit 4 3 5).val * positiveScale (rightScaleExponent 4 3 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 5 3 : ℤ)) • HexagonAtoms435.outerLeftABC) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 4 3 5) • (rowColumnMul HexagonRowColumn435.rows_assocCAB HexagonRowColumn435.cols_right2)) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal4_case_3_5_row_3_0_2 : (((-1 : ℤ) ^ (rightScaleBit 4 3 5).val * positiveScale (rightScaleExponent 4 3 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 5 3 : ℤ)) • HexagonAtoms435.outerLeftABC) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 4 3 5) • (rowColumnMul HexagonRowColumn435.rows_assocCAB HexagonRowColumn435.cols_right2)) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal4_case_3_5_row_3_0_3 : (((-1 : ℤ) ^ (rightScaleBit 4 3 5).val * positiveScale (rightScaleExponent 4 3 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 5 3 : ℤ)) • HexagonAtoms435.outerLeftABC) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 4 3 5) • (rowColumnMul HexagonRowColumn435.rows_assocCAB HexagonRowColumn435.cols_right2)) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal4_case_3_5_row_3_1_0 : (((-1 : ℤ) ^ (rightScaleBit 4 3 5).val * positiveScale (rightScaleExponent 4 3 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 5 3 : ℤ)) • HexagonAtoms435.outerLeftABC) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 4 3 5) • (rowColumnMul HexagonRowColumn435.rows_assocCAB HexagonRowColumn435.cols_right2)) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal4_case_3_5_row_3_1_1 : (((-1 : ℤ) ^ (rightScaleBit 4 3 5).val * positiveScale (rightScaleExponent 4 3 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 5 3 : ℤ)) • HexagonAtoms435.outerLeftABC) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 4 3 5) • (rowColumnMul HexagonRowColumn435.rows_assocCAB HexagonRowColumn435.cols_right2)) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal4_case_3_5_row_3_1_2 : (((-1 : ℤ) ^ (rightScaleBit 4 3 5).val * positiveScale (rightScaleExponent 4 3 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 5 3 : ℤ)) • HexagonAtoms435.outerLeftABC) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 4 3 5) • (rowColumnMul HexagonRowColumn435.rows_assocCAB HexagonRowColumn435.cols_right2)) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal4_case_3_5_row_3_1_3 : (((-1 : ℤ) ^ (rightScaleBit 4 3 5).val * positiveScale (rightScaleExponent 4 3 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 5 3 : ℤ)) • HexagonAtoms435.outerLeftABC) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 4 3 5) • (rowColumnMul HexagonRowColumn435.rows_assocCAB HexagonRowColumn435.cols_right2)) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal4_case_3_5_checked : ((-1 : ℤ) ^ (rightScaleBit 4 3 5).val * positiveScale (rightScaleExponent 4 3 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 5 3 : ℤ)) • HexagonAtoms435.outerLeftABC = negativeScale (rightScaleExponent 4 3 5) • (rowColumnMul HexagonRowColumn435.rows_assocCAB HexagonRowColumn435.cols_right2) := by
  funext r
  fin_cases r
  · exact rightFinal4_case_3_5_row_0_0_0
  · exact rightFinal4_case_3_5_row_0_0_1
  · exact rightFinal4_case_3_5_row_0_0_2
  · exact rightFinal4_case_3_5_row_0_0_3
  · exact rightFinal4_case_3_5_row_0_1_0
  · exact rightFinal4_case_3_5_row_0_1_1
  · exact rightFinal4_case_3_5_row_0_1_2
  · exact rightFinal4_case_3_5_row_0_1_3
  · exact rightFinal4_case_3_5_row_1_0_0
  · exact rightFinal4_case_3_5_row_1_0_1
  · exact rightFinal4_case_3_5_row_1_0_2
  · exact rightFinal4_case_3_5_row_1_0_3
  · exact rightFinal4_case_3_5_row_1_1_0
  · exact rightFinal4_case_3_5_row_1_1_1
  · exact rightFinal4_case_3_5_row_1_1_2
  · exact rightFinal4_case_3_5_row_1_1_3
  · exact rightFinal4_case_3_5_row_2_0_0
  · exact rightFinal4_case_3_5_row_2_0_1
  · exact rightFinal4_case_3_5_row_2_0_2
  · exact rightFinal4_case_3_5_row_2_0_3
  · exact rightFinal4_case_3_5_row_2_1_0
  · exact rightFinal4_case_3_5_row_2_1_1
  · exact rightFinal4_case_3_5_row_2_1_2
  · exact rightFinal4_case_3_5_row_2_1_3
  · exact rightFinal4_case_3_5_row_3_0_0
  · exact rightFinal4_case_3_5_row_3_0_1
  · exact rightFinal4_case_3_5_row_3_0_2
  · exact rightFinal4_case_3_5_row_3_0_3
  · exact rightFinal4_case_3_5_row_3_1_0
  · exact rightFinal4_case_3_5_row_3_1_1
  · exact rightFinal4_case_3_5_row_3_1_2
  · exact rightFinal4_case_3_5_row_3_1_3

set_option backward.isDefEq.respectTransparency false in
theorem rightFinal4_case_3_5 : ((-1 : ℤ) ^ (rightScaleBit 4 3 5).val * positiveScale (rightScaleExponent 4 3 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 5 3 : ℤ)) • outerLeftZ 4 3 5 = negativeScale (rightScaleExponent 4 3 5) • (associatorZ 5 4 3 * right2Middle4 3 5) := by
  simpa only [HexagonAtoms435.assocABC_eq,
    HexagonAtoms435.outerABC_eq,
    HexagonAtoms435.assocBAC_eq,
    HexagonAtoms435.innerABC_eq,
    HexagonAtoms435.innerRightABC_eq,
    HexagonAtoms435.inverseACB_eq,
    HexagonAtoms435.innerACB_eq,
    HexagonAtoms435.assocBCA_eq,
    HexagonAtoms435.innerRightBAC_eq,
    HexagonAtoms435.assocCAB_eq,
    HexagonAtoms435.outerLeftABC_eq,
    HexagonRowColumn435.product0_eq,
    HexagonRowColumn435.product1_eq,
    HexagonRowColumn435.product2_eq,
    HexagonRowColumn435.product3_eq,
    HexagonRowColumn435.product4_eq,
    HexagonRowColumn435.product5_eq,
    HexagonRowColumn435.product6_eq,
    HexagonRowColumn435.product7_eq] using rightFinal4_case_3_5_checked

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonCases4
