import RMod.BrundanEllis.StackingReferenceHexagonMiddle3
import RMod.BrundanEllis.StackingReferenceSparseMatrixCheck
import RMod.BrundanEllis.StackingReferenceHexagonAtoms366
import RMod.BrundanEllis.StackingReferenceHexagonRowColumn366

/-! Seven closed product identities for one reference triple.
The proof uses only verified atomic maps and ordinary kernel reduction. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
set_option linter.unusedSimpArgs false
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonCases3
open Superfusion

private theorem left0Middle3_eq_case_6_6_row_0_0_0 : (left0Middle3 6 6) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (HexagonAtoms366.assocABC) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left0Middle3_eq_case_6_6_row_0_0_1 : (left0Middle3 6 6) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (HexagonAtoms366.assocABC) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left0Middle3_eq_case_6_6_row_0_1_0 : (left0Middle3 6 6) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (HexagonAtoms366.assocABC) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left0Middle3_eq_case_6_6_row_0_1_1 : (left0Middle3 6 6) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (HexagonAtoms366.assocABC) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left0Middle3_eq_case_6_6_row_0_2_0 : (left0Middle3 6 6) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (HexagonAtoms366.assocABC) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left0Middle3_eq_case_6_6_row_0_2_1 : (left0Middle3 6 6) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (HexagonAtoms366.assocABC) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left0Middle3_eq_case_6_6_row_0_3_0 : (left0Middle3 6 6) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (HexagonAtoms366.assocABC) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left0Middle3_eq_case_6_6_row_0_3_1 : (left0Middle3 6 6) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (HexagonAtoms366.assocABC) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left0Middle3_eq_case_6_6_row_1_0_0 : (left0Middle3 6 6) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (HexagonAtoms366.assocABC) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left0Middle3_eq_case_6_6_row_1_0_1 : (left0Middle3 6 6) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (HexagonAtoms366.assocABC) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left0Middle3_eq_case_6_6_row_1_1_0 : (left0Middle3 6 6) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (HexagonAtoms366.assocABC) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left0Middle3_eq_case_6_6_row_1_1_1 : (left0Middle3 6 6) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (HexagonAtoms366.assocABC) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left0Middle3_eq_case_6_6_row_1_2_0 : (left0Middle3 6 6) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (HexagonAtoms366.assocABC) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left0Middle3_eq_case_6_6_row_1_2_1 : (left0Middle3 6 6) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (HexagonAtoms366.assocABC) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left0Middle3_eq_case_6_6_row_1_3_0 : (left0Middle3 6 6) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (HexagonAtoms366.assocABC) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left0Middle3_eq_case_6_6_row_1_3_1 : (left0Middle3 6 6) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (HexagonAtoms366.assocABC) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left0Middle3_eq_case_6_6_checked : left0Middle3 6 6 = HexagonAtoms366.assocABC := by
  funext r
  fin_cases r
  · exact left0Middle3_eq_case_6_6_row_0_0_0
  · exact left0Middle3_eq_case_6_6_row_0_0_1
  · exact left0Middle3_eq_case_6_6_row_0_1_0
  · exact left0Middle3_eq_case_6_6_row_0_1_1
  · exact left0Middle3_eq_case_6_6_row_0_2_0
  · exact left0Middle3_eq_case_6_6_row_0_2_1
  · exact left0Middle3_eq_case_6_6_row_0_3_0
  · exact left0Middle3_eq_case_6_6_row_0_3_1
  · exact left0Middle3_eq_case_6_6_row_1_0_0
  · exact left0Middle3_eq_case_6_6_row_1_0_1
  · exact left0Middle3_eq_case_6_6_row_1_1_0
  · exact left0Middle3_eq_case_6_6_row_1_1_1
  · exact left0Middle3_eq_case_6_6_row_1_2_0
  · exact left0Middle3_eq_case_6_6_row_1_2_1
  · exact left0Middle3_eq_case_6_6_row_1_3_0
  · exact left0Middle3_eq_case_6_6_row_1_3_1

set_option backward.isDefEq.respectTransparency false in
theorem left0Middle3_eq_case_6_6 : left0Middle3 6 6 = outerRightZ 3 6 6 * associatorZ 3 6 6 := by
  simpa only [HexagonAtoms366.assocABC_eq,
    HexagonAtoms366.outerABC_eq,
    HexagonAtoms366.assocBAC_eq,
    HexagonAtoms366.innerABC_eq,
    HexagonAtoms366.innerRightABC_eq,
    HexagonAtoms366.inverseACB_eq,
    HexagonAtoms366.innerACB_eq,
    HexagonAtoms366.assocBCA_eq,
    HexagonAtoms366.innerRightBAC_eq,
    HexagonAtoms366.assocCAB_eq,
    HexagonAtoms366.outerLeftABC_eq,
    HexagonRowColumn366.innerACB_alias,
    HexagonRowColumn366.assocCAB_alias,
    HexagonRowColumn366.product0_eq,
    HexagonRowColumn366.product1_eq,
    HexagonRowColumn366.product2_eq,
    HexagonRowColumn366.product3_eq,
    HexagonRowColumn366.product4_eq,
    HexagonRowColumn366.product5_eq,
    HexagonRowColumn366.product6_eq,
    HexagonRowColumn366.product7_eq] using left0Middle3_eq_case_6_6_checked

private theorem left1Middle3_eq_case_6_6_row_0_0_0 : (left1Middle3 6 6) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (HexagonAtoms366.assocBAC) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left1Middle3_eq_case_6_6_row_0_0_1 : (left1Middle3 6 6) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (HexagonAtoms366.assocBAC) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left1Middle3_eq_case_6_6_row_0_1_0 : (left1Middle3 6 6) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (HexagonAtoms366.assocBAC) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left1Middle3_eq_case_6_6_row_0_1_1 : (left1Middle3 6 6) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (HexagonAtoms366.assocBAC) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left1Middle3_eq_case_6_6_row_1_0_0 : (left1Middle3 6 6) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (HexagonAtoms366.assocBAC) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left1Middle3_eq_case_6_6_row_1_0_1 : (left1Middle3 6 6) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (HexagonAtoms366.assocBAC) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left1Middle3_eq_case_6_6_row_1_1_0 : (left1Middle3 6 6) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (HexagonAtoms366.assocBAC) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left1Middle3_eq_case_6_6_row_1_1_1 : (left1Middle3 6 6) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (HexagonAtoms366.assocBAC) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left1Middle3_eq_case_6_6_row_2_0_0 : (left1Middle3 6 6) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (HexagonAtoms366.assocBAC) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left1Middle3_eq_case_6_6_row_2_0_1 : (left1Middle3 6 6) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (HexagonAtoms366.assocBAC) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left1Middle3_eq_case_6_6_row_2_1_0 : (left1Middle3 6 6) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (HexagonAtoms366.assocBAC) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left1Middle3_eq_case_6_6_row_2_1_1 : (left1Middle3 6 6) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (HexagonAtoms366.assocBAC) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left1Middle3_eq_case_6_6_row_3_0_0 : (left1Middle3 6 6) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (HexagonAtoms366.assocBAC) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left1Middle3_eq_case_6_6_row_3_0_1 : (left1Middle3 6 6) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (HexagonAtoms366.assocBAC) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left1Middle3_eq_case_6_6_row_3_1_0 : (left1Middle3 6 6) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (HexagonAtoms366.assocBAC) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left1Middle3_eq_case_6_6_row_3_1_1 : (left1Middle3 6 6) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (HexagonAtoms366.assocBAC) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left1Middle3_eq_case_6_6_checked : left1Middle3 6 6 = HexagonAtoms366.assocBAC := by
  funext r
  fin_cases r
  · exact left1Middle3_eq_case_6_6_row_0_0_0
  · exact left1Middle3_eq_case_6_6_row_0_0_1
  · exact left1Middle3_eq_case_6_6_row_0_1_0
  · exact left1Middle3_eq_case_6_6_row_0_1_1
  · exact left1Middle3_eq_case_6_6_row_1_0_0
  · exact left1Middle3_eq_case_6_6_row_1_0_1
  · exact left1Middle3_eq_case_6_6_row_1_1_0
  · exact left1Middle3_eq_case_6_6_row_1_1_1
  · exact left1Middle3_eq_case_6_6_row_2_0_0
  · exact left1Middle3_eq_case_6_6_row_2_0_1
  · exact left1Middle3_eq_case_6_6_row_2_1_0
  · exact left1Middle3_eq_case_6_6_row_2_1_1
  · exact left1Middle3_eq_case_6_6_row_3_0_0
  · exact left1Middle3_eq_case_6_6_row_3_0_1
  · exact left1Middle3_eq_case_6_6_row_3_1_0
  · exact left1Middle3_eq_case_6_6_row_3_1_1

set_option backward.isDefEq.respectTransparency false in
theorem left1Middle3_eq_case_6_6 : left1Middle3 6 6 = associatorZ 6 3 6 * innerLeftZ 3 6 6 := by
  simpa only [HexagonAtoms366.assocABC_eq,
    HexagonAtoms366.outerABC_eq,
    HexagonAtoms366.assocBAC_eq,
    HexagonAtoms366.innerABC_eq,
    HexagonAtoms366.innerRightABC_eq,
    HexagonAtoms366.inverseACB_eq,
    HexagonAtoms366.innerACB_eq,
    HexagonAtoms366.assocBCA_eq,
    HexagonAtoms366.innerRightBAC_eq,
    HexagonAtoms366.assocCAB_eq,
    HexagonAtoms366.outerLeftABC_eq,
    HexagonRowColumn366.innerACB_alias,
    HexagonRowColumn366.assocCAB_alias,
    HexagonRowColumn366.product0_eq,
    HexagonRowColumn366.product1_eq,
    HexagonRowColumn366.product2_eq,
    HexagonRowColumn366.product3_eq,
    HexagonRowColumn366.product4_eq,
    HexagonRowColumn366.product5_eq,
    HexagonRowColumn366.product6_eq,
    HexagonRowColumn366.product7_eq] using left1Middle3_eq_case_6_6_checked

private theorem right0Middle3_eq_case_6_6_row_0_0_0 : (right0Middle3 6 6) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn366.rows_innerRightABC HexagonRowColumn366.cols_assocABC) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right0Middle3_eq_case_6_6_row_0_0_1 : (right0Middle3 6 6) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn366.rows_innerRightABC HexagonRowColumn366.cols_assocABC) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right0Middle3_eq_case_6_6_row_0_1_0 : (right0Middle3 6 6) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn366.rows_innerRightABC HexagonRowColumn366.cols_assocABC) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right0Middle3_eq_case_6_6_row_0_1_1 : (right0Middle3 6 6) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn366.rows_innerRightABC HexagonRowColumn366.cols_assocABC) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right0Middle3_eq_case_6_6_row_0_2_0 : (right0Middle3 6 6) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn366.rows_innerRightABC HexagonRowColumn366.cols_assocABC) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right0Middle3_eq_case_6_6_row_0_2_1 : (right0Middle3 6 6) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn366.rows_innerRightABC HexagonRowColumn366.cols_assocABC) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right0Middle3_eq_case_6_6_row_0_3_0 : (right0Middle3 6 6) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn366.rows_innerRightABC HexagonRowColumn366.cols_assocABC) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right0Middle3_eq_case_6_6_row_0_3_1 : (right0Middle3 6 6) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn366.rows_innerRightABC HexagonRowColumn366.cols_assocABC) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right0Middle3_eq_case_6_6_row_1_0_0 : (right0Middle3 6 6) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn366.rows_innerRightABC HexagonRowColumn366.cols_assocABC) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right0Middle3_eq_case_6_6_row_1_0_1 : (right0Middle3 6 6) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn366.rows_innerRightABC HexagonRowColumn366.cols_assocABC) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right0Middle3_eq_case_6_6_row_1_1_0 : (right0Middle3 6 6) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn366.rows_innerRightABC HexagonRowColumn366.cols_assocABC) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right0Middle3_eq_case_6_6_row_1_1_1 : (right0Middle3 6 6) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn366.rows_innerRightABC HexagonRowColumn366.cols_assocABC) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right0Middle3_eq_case_6_6_row_1_2_0 : (right0Middle3 6 6) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn366.rows_innerRightABC HexagonRowColumn366.cols_assocABC) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right0Middle3_eq_case_6_6_row_1_2_1 : (right0Middle3 6 6) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn366.rows_innerRightABC HexagonRowColumn366.cols_assocABC) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right0Middle3_eq_case_6_6_row_1_3_0 : (right0Middle3 6 6) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn366.rows_innerRightABC HexagonRowColumn366.cols_assocABC) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right0Middle3_eq_case_6_6_row_1_3_1 : (right0Middle3 6 6) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn366.rows_innerRightABC HexagonRowColumn366.cols_assocABC) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right0Middle3_eq_case_6_6_checked : right0Middle3 6 6 = rowColumnMul HexagonRowColumn366.rows_innerRightABC HexagonRowColumn366.cols_assocABC := by
  funext r
  fin_cases r
  · exact right0Middle3_eq_case_6_6_row_0_0_0
  · exact right0Middle3_eq_case_6_6_row_0_0_1
  · exact right0Middle3_eq_case_6_6_row_0_1_0
  · exact right0Middle3_eq_case_6_6_row_0_1_1
  · exact right0Middle3_eq_case_6_6_row_0_2_0
  · exact right0Middle3_eq_case_6_6_row_0_2_1
  · exact right0Middle3_eq_case_6_6_row_0_3_0
  · exact right0Middle3_eq_case_6_6_row_0_3_1
  · exact right0Middle3_eq_case_6_6_row_1_0_0
  · exact right0Middle3_eq_case_6_6_row_1_0_1
  · exact right0Middle3_eq_case_6_6_row_1_1_0
  · exact right0Middle3_eq_case_6_6_row_1_1_1
  · exact right0Middle3_eq_case_6_6_row_1_2_0
  · exact right0Middle3_eq_case_6_6_row_1_2_1
  · exact right0Middle3_eq_case_6_6_row_1_3_0
  · exact right0Middle3_eq_case_6_6_row_1_3_1

set_option backward.isDefEq.respectTransparency false in
theorem right0Middle3_eq_case_6_6 : right0Middle3 6 6 = innerRightZ 3 6 6 * associatorZ 3 6 6 := by
  simpa only [HexagonAtoms366.assocABC_eq,
    HexagonAtoms366.outerABC_eq,
    HexagonAtoms366.assocBAC_eq,
    HexagonAtoms366.innerABC_eq,
    HexagonAtoms366.innerRightABC_eq,
    HexagonAtoms366.inverseACB_eq,
    HexagonAtoms366.innerACB_eq,
    HexagonAtoms366.assocBCA_eq,
    HexagonAtoms366.innerRightBAC_eq,
    HexagonAtoms366.assocCAB_eq,
    HexagonAtoms366.outerLeftABC_eq,
    HexagonRowColumn366.innerACB_alias,
    HexagonRowColumn366.assocCAB_alias,
    HexagonRowColumn366.product0_eq,
    HexagonRowColumn366.product1_eq,
    HexagonRowColumn366.product2_eq,
    HexagonRowColumn366.product3_eq,
    HexagonRowColumn366.product4_eq,
    HexagonRowColumn366.product5_eq,
    HexagonRowColumn366.product6_eq,
    HexagonRowColumn366.product7_eq] using right0Middle3_eq_case_6_6_checked

private theorem right1Middle3_eq_case_6_6_row_0_0_0 : (right1Middle3 6 6) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn366.rows_inverseACB HexagonRowColumn366.cols_right0) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right1Middle3_eq_case_6_6_row_0_0_1 : (right1Middle3 6 6) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn366.rows_inverseACB HexagonRowColumn366.cols_right0) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right1Middle3_eq_case_6_6_row_0_1_0 : (right1Middle3 6 6) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn366.rows_inverseACB HexagonRowColumn366.cols_right0) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right1Middle3_eq_case_6_6_row_0_1_1 : (right1Middle3 6 6) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn366.rows_inverseACB HexagonRowColumn366.cols_right0) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right1Middle3_eq_case_6_6_row_1_0_0 : (right1Middle3 6 6) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn366.rows_inverseACB HexagonRowColumn366.cols_right0) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right1Middle3_eq_case_6_6_row_1_0_1 : (right1Middle3 6 6) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn366.rows_inverseACB HexagonRowColumn366.cols_right0) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right1Middle3_eq_case_6_6_row_1_1_0 : (right1Middle3 6 6) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn366.rows_inverseACB HexagonRowColumn366.cols_right0) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right1Middle3_eq_case_6_6_row_1_1_1 : (right1Middle3 6 6) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn366.rows_inverseACB HexagonRowColumn366.cols_right0) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right1Middle3_eq_case_6_6_row_2_0_0 : (right1Middle3 6 6) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn366.rows_inverseACB HexagonRowColumn366.cols_right0) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right1Middle3_eq_case_6_6_row_2_0_1 : (right1Middle3 6 6) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn366.rows_inverseACB HexagonRowColumn366.cols_right0) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right1Middle3_eq_case_6_6_row_2_1_0 : (right1Middle3 6 6) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn366.rows_inverseACB HexagonRowColumn366.cols_right0) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right1Middle3_eq_case_6_6_row_2_1_1 : (right1Middle3 6 6) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn366.rows_inverseACB HexagonRowColumn366.cols_right0) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right1Middle3_eq_case_6_6_row_3_0_0 : (right1Middle3 6 6) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn366.rows_inverseACB HexagonRowColumn366.cols_right0) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right1Middle3_eq_case_6_6_row_3_0_1 : (right1Middle3 6 6) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn366.rows_inverseACB HexagonRowColumn366.cols_right0) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right1Middle3_eq_case_6_6_row_3_1_0 : (right1Middle3 6 6) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn366.rows_inverseACB HexagonRowColumn366.cols_right0) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right1Middle3_eq_case_6_6_row_3_1_1 : (right1Middle3 6 6) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn366.rows_inverseACB HexagonRowColumn366.cols_right0) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right1Middle3_eq_case_6_6_checked : right1Middle3 6 6 = rowColumnMul HexagonRowColumn366.rows_inverseACB HexagonRowColumn366.cols_right0 := by
  funext r
  fin_cases r
  · exact right1Middle3_eq_case_6_6_row_0_0_0
  · exact right1Middle3_eq_case_6_6_row_0_0_1
  · exact right1Middle3_eq_case_6_6_row_0_1_0
  · exact right1Middle3_eq_case_6_6_row_0_1_1
  · exact right1Middle3_eq_case_6_6_row_1_0_0
  · exact right1Middle3_eq_case_6_6_row_1_0_1
  · exact right1Middle3_eq_case_6_6_row_1_1_0
  · exact right1Middle3_eq_case_6_6_row_1_1_1
  · exact right1Middle3_eq_case_6_6_row_2_0_0
  · exact right1Middle3_eq_case_6_6_row_2_0_1
  · exact right1Middle3_eq_case_6_6_row_2_1_0
  · exact right1Middle3_eq_case_6_6_row_2_1_1
  · exact right1Middle3_eq_case_6_6_row_3_0_0
  · exact right1Middle3_eq_case_6_6_row_3_0_1
  · exact right1Middle3_eq_case_6_6_row_3_1_0
  · exact right1Middle3_eq_case_6_6_row_3_1_1

set_option backward.isDefEq.respectTransparency false in
theorem right1Middle3_eq_case_6_6 : right1Middle3 6 6 = associatorInverseZ 3 6 6 * right0Middle3 6 6 := by
  simpa only [HexagonAtoms366.assocABC_eq,
    HexagonAtoms366.outerABC_eq,
    HexagonAtoms366.assocBAC_eq,
    HexagonAtoms366.innerABC_eq,
    HexagonAtoms366.innerRightABC_eq,
    HexagonAtoms366.inverseACB_eq,
    HexagonAtoms366.innerACB_eq,
    HexagonAtoms366.assocBCA_eq,
    HexagonAtoms366.innerRightBAC_eq,
    HexagonAtoms366.assocCAB_eq,
    HexagonAtoms366.outerLeftABC_eq,
    HexagonRowColumn366.innerACB_alias,
    HexagonRowColumn366.assocCAB_alias,
    HexagonRowColumn366.product0_eq,
    HexagonRowColumn366.product1_eq,
    HexagonRowColumn366.product2_eq,
    HexagonRowColumn366.product3_eq,
    HexagonRowColumn366.product4_eq,
    HexagonRowColumn366.product5_eq,
    HexagonRowColumn366.product6_eq,
    HexagonRowColumn366.product7_eq] using right1Middle3_eq_case_6_6_checked

private theorem right2Middle3_eq_case_6_6_row_0_0_0 : (right2Middle3 6 6) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (right1Middle3 6 6) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right2Middle3_eq_case_6_6_row_0_0_1 : (right2Middle3 6 6) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (right1Middle3 6 6) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right2Middle3_eq_case_6_6_row_0_1_0 : (right2Middle3 6 6) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (right1Middle3 6 6) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right2Middle3_eq_case_6_6_row_0_1_1 : (right2Middle3 6 6) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (right1Middle3 6 6) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right2Middle3_eq_case_6_6_row_1_0_0 : (right2Middle3 6 6) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (right1Middle3 6 6) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right2Middle3_eq_case_6_6_row_1_0_1 : (right2Middle3 6 6) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (right1Middle3 6 6) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right2Middle3_eq_case_6_6_row_1_1_0 : (right2Middle3 6 6) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (right1Middle3 6 6) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right2Middle3_eq_case_6_6_row_1_1_1 : (right2Middle3 6 6) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (right1Middle3 6 6) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right2Middle3_eq_case_6_6_row_2_0_0 : (right2Middle3 6 6) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (right1Middle3 6 6) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right2Middle3_eq_case_6_6_row_2_0_1 : (right2Middle3 6 6) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (right1Middle3 6 6) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right2Middle3_eq_case_6_6_row_2_1_0 : (right2Middle3 6 6) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (right1Middle3 6 6) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right2Middle3_eq_case_6_6_row_2_1_1 : (right2Middle3 6 6) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (right1Middle3 6 6) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right2Middle3_eq_case_6_6_row_3_0_0 : (right2Middle3 6 6) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (right1Middle3 6 6) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right2Middle3_eq_case_6_6_row_3_0_1 : (right2Middle3 6 6) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (right1Middle3 6 6) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right2Middle3_eq_case_6_6_row_3_1_0 : (right2Middle3 6 6) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (right1Middle3 6 6) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right2Middle3_eq_case_6_6_row_3_1_1 : (right2Middle3 6 6) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (right1Middle3 6 6) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right2Middle3_eq_case_6_6_checked : right2Middle3 6 6 = right1Middle3 6 6 := by
  funext r
  fin_cases r
  · exact right2Middle3_eq_case_6_6_row_0_0_0
  · exact right2Middle3_eq_case_6_6_row_0_0_1
  · exact right2Middle3_eq_case_6_6_row_0_1_0
  · exact right2Middle3_eq_case_6_6_row_0_1_1
  · exact right2Middle3_eq_case_6_6_row_1_0_0
  · exact right2Middle3_eq_case_6_6_row_1_0_1
  · exact right2Middle3_eq_case_6_6_row_1_1_0
  · exact right2Middle3_eq_case_6_6_row_1_1_1
  · exact right2Middle3_eq_case_6_6_row_2_0_0
  · exact right2Middle3_eq_case_6_6_row_2_0_1
  · exact right2Middle3_eq_case_6_6_row_2_1_0
  · exact right2Middle3_eq_case_6_6_row_2_1_1
  · exact right2Middle3_eq_case_6_6_row_3_0_0
  · exact right2Middle3_eq_case_6_6_row_3_0_1
  · exact right2Middle3_eq_case_6_6_row_3_1_0
  · exact right2Middle3_eq_case_6_6_row_3_1_1

set_option backward.isDefEq.respectTransparency false in
theorem right2Middle3_eq_case_6_6 : right2Middle3 6 6 = innerLeftZ 3 6 6 * right1Middle3 6 6 := by
  simpa only [HexagonAtoms366.assocABC_eq,
    HexagonAtoms366.outerABC_eq,
    HexagonAtoms366.assocBAC_eq,
    HexagonAtoms366.innerABC_eq,
    HexagonAtoms366.innerRightABC_eq,
    HexagonAtoms366.inverseACB_eq,
    HexagonAtoms366.innerACB_eq,
    HexagonAtoms366.assocBCA_eq,
    HexagonAtoms366.innerRightBAC_eq,
    HexagonAtoms366.assocCAB_eq,
    HexagonAtoms366.outerLeftABC_eq,
    HexagonRowColumn366.innerACB_alias,
    HexagonRowColumn366.assocCAB_alias,
    HexagonRowColumn366.product0_eq,
    HexagonRowColumn366.product1_eq,
    HexagonRowColumn366.product2_eq,
    HexagonRowColumn366.product3_eq,
    HexagonRowColumn366.product4_eq,
    HexagonRowColumn366.product5_eq,
    HexagonRowColumn366.product6_eq,
    HexagonRowColumn366.product7_eq] using right2Middle3_eq_case_6_6_checked

private theorem leftFinal3_case_6_6_row_0_0_0 : (((-1 : ℤ) ^ (leftScaleBit 3 6 6).val * positiveScale (leftScaleExponent 3 6 6)) •
      (rowColumnMul HexagonRowColumn366.rows_assocBCA HexagonRowColumn366.cols_left0)) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (negativeScale (leftScaleExponent 3 6 6) • (left1Middle3 6 6)) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem leftFinal3_case_6_6_row_0_0_1 : (((-1 : ℤ) ^ (leftScaleBit 3 6 6).val * positiveScale (leftScaleExponent 3 6 6)) •
      (rowColumnMul HexagonRowColumn366.rows_assocBCA HexagonRowColumn366.cols_left0)) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (negativeScale (leftScaleExponent 3 6 6) • (left1Middle3 6 6)) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem leftFinal3_case_6_6_row_0_1_0 : (((-1 : ℤ) ^ (leftScaleBit 3 6 6).val * positiveScale (leftScaleExponent 3 6 6)) •
      (rowColumnMul HexagonRowColumn366.rows_assocBCA HexagonRowColumn366.cols_left0)) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (negativeScale (leftScaleExponent 3 6 6) • (left1Middle3 6 6)) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem leftFinal3_case_6_6_row_0_1_1 : (((-1 : ℤ) ^ (leftScaleBit 3 6 6).val * positiveScale (leftScaleExponent 3 6 6)) •
      (rowColumnMul HexagonRowColumn366.rows_assocBCA HexagonRowColumn366.cols_left0)) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (negativeScale (leftScaleExponent 3 6 6) • (left1Middle3 6 6)) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem leftFinal3_case_6_6_row_1_0_0 : (((-1 : ℤ) ^ (leftScaleBit 3 6 6).val * positiveScale (leftScaleExponent 3 6 6)) •
      (rowColumnMul HexagonRowColumn366.rows_assocBCA HexagonRowColumn366.cols_left0)) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (negativeScale (leftScaleExponent 3 6 6) • (left1Middle3 6 6)) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem leftFinal3_case_6_6_row_1_0_1 : (((-1 : ℤ) ^ (leftScaleBit 3 6 6).val * positiveScale (leftScaleExponent 3 6 6)) •
      (rowColumnMul HexagonRowColumn366.rows_assocBCA HexagonRowColumn366.cols_left0)) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (negativeScale (leftScaleExponent 3 6 6) • (left1Middle3 6 6)) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem leftFinal3_case_6_6_row_1_1_0 : (((-1 : ℤ) ^ (leftScaleBit 3 6 6).val * positiveScale (leftScaleExponent 3 6 6)) •
      (rowColumnMul HexagonRowColumn366.rows_assocBCA HexagonRowColumn366.cols_left0)) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (negativeScale (leftScaleExponent 3 6 6) • (left1Middle3 6 6)) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem leftFinal3_case_6_6_row_1_1_1 : (((-1 : ℤ) ^ (leftScaleBit 3 6 6).val * positiveScale (leftScaleExponent 3 6 6)) •
      (rowColumnMul HexagonRowColumn366.rows_assocBCA HexagonRowColumn366.cols_left0)) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (negativeScale (leftScaleExponent 3 6 6) • (left1Middle3 6 6)) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem leftFinal3_case_6_6_row_2_0_0 : (((-1 : ℤ) ^ (leftScaleBit 3 6 6).val * positiveScale (leftScaleExponent 3 6 6)) •
      (rowColumnMul HexagonRowColumn366.rows_assocBCA HexagonRowColumn366.cols_left0)) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (negativeScale (leftScaleExponent 3 6 6) • (left1Middle3 6 6)) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem leftFinal3_case_6_6_row_2_0_1 : (((-1 : ℤ) ^ (leftScaleBit 3 6 6).val * positiveScale (leftScaleExponent 3 6 6)) •
      (rowColumnMul HexagonRowColumn366.rows_assocBCA HexagonRowColumn366.cols_left0)) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (negativeScale (leftScaleExponent 3 6 6) • (left1Middle3 6 6)) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem leftFinal3_case_6_6_row_2_1_0 : (((-1 : ℤ) ^ (leftScaleBit 3 6 6).val * positiveScale (leftScaleExponent 3 6 6)) •
      (rowColumnMul HexagonRowColumn366.rows_assocBCA HexagonRowColumn366.cols_left0)) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (negativeScale (leftScaleExponent 3 6 6) • (left1Middle3 6 6)) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem leftFinal3_case_6_6_row_2_1_1 : (((-1 : ℤ) ^ (leftScaleBit 3 6 6).val * positiveScale (leftScaleExponent 3 6 6)) •
      (rowColumnMul HexagonRowColumn366.rows_assocBCA HexagonRowColumn366.cols_left0)) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (negativeScale (leftScaleExponent 3 6 6) • (left1Middle3 6 6)) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem leftFinal3_case_6_6_row_3_0_0 : (((-1 : ℤ) ^ (leftScaleBit 3 6 6).val * positiveScale (leftScaleExponent 3 6 6)) •
      (rowColumnMul HexagonRowColumn366.rows_assocBCA HexagonRowColumn366.cols_left0)) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (negativeScale (leftScaleExponent 3 6 6) • (left1Middle3 6 6)) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem leftFinal3_case_6_6_row_3_0_1 : (((-1 : ℤ) ^ (leftScaleBit 3 6 6).val * positiveScale (leftScaleExponent 3 6 6)) •
      (rowColumnMul HexagonRowColumn366.rows_assocBCA HexagonRowColumn366.cols_left0)) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (negativeScale (leftScaleExponent 3 6 6) • (left1Middle3 6 6)) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem leftFinal3_case_6_6_row_3_1_0 : (((-1 : ℤ) ^ (leftScaleBit 3 6 6).val * positiveScale (leftScaleExponent 3 6 6)) •
      (rowColumnMul HexagonRowColumn366.rows_assocBCA HexagonRowColumn366.cols_left0)) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (negativeScale (leftScaleExponent 3 6 6) • (left1Middle3 6 6)) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem leftFinal3_case_6_6_row_3_1_1 : (((-1 : ℤ) ^ (leftScaleBit 3 6 6).val * positiveScale (leftScaleExponent 3 6 6)) •
      (rowColumnMul HexagonRowColumn366.rows_assocBCA HexagonRowColumn366.cols_left0)) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (negativeScale (leftScaleExponent 3 6 6) • (left1Middle3 6 6)) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem leftFinal3_case_6_6_checked : ((-1 : ℤ) ^ (leftScaleBit 3 6 6).val * positiveScale (leftScaleExponent 3 6 6)) •
      (rowColumnMul HexagonRowColumn366.rows_assocBCA HexagonRowColumn366.cols_left0) = negativeScale (leftScaleExponent 3 6 6) • (left1Middle3 6 6) := by
  funext r
  fin_cases r
  · exact leftFinal3_case_6_6_row_0_0_0
  · exact leftFinal3_case_6_6_row_0_0_1
  · exact leftFinal3_case_6_6_row_0_1_0
  · exact leftFinal3_case_6_6_row_0_1_1
  · exact leftFinal3_case_6_6_row_1_0_0
  · exact leftFinal3_case_6_6_row_1_0_1
  · exact leftFinal3_case_6_6_row_1_1_0
  · exact leftFinal3_case_6_6_row_1_1_1
  · exact leftFinal3_case_6_6_row_2_0_0
  · exact leftFinal3_case_6_6_row_2_0_1
  · exact leftFinal3_case_6_6_row_2_1_0
  · exact leftFinal3_case_6_6_row_2_1_1
  · exact leftFinal3_case_6_6_row_3_0_0
  · exact leftFinal3_case_6_6_row_3_0_1
  · exact leftFinal3_case_6_6_row_3_1_0
  · exact leftFinal3_case_6_6_row_3_1_1

set_option backward.isDefEq.respectTransparency false in
theorem leftFinal3_case_6_6 : ((-1 : ℤ) ^ (leftScaleBit 3 6 6).val * positiveScale (leftScaleExponent 3 6 6)) •
      (associatorZ 6 6 3 * left0Middle3 6 6) = negativeScale (leftScaleExponent 3 6 6) • (innerRightZ 6 3 6 * left1Middle3 6 6) := by
  simpa only [HexagonAtoms366.assocABC_eq,
    HexagonAtoms366.outerABC_eq,
    HexagonAtoms366.assocBAC_eq,
    HexagonAtoms366.innerABC_eq,
    HexagonAtoms366.innerRightABC_eq,
    HexagonAtoms366.inverseACB_eq,
    HexagonAtoms366.innerACB_eq,
    HexagonAtoms366.assocBCA_eq,
    HexagonAtoms366.innerRightBAC_eq,
    HexagonAtoms366.assocCAB_eq,
    HexagonAtoms366.outerLeftABC_eq,
    HexagonRowColumn366.innerACB_alias,
    HexagonRowColumn366.assocCAB_alias,
    HexagonRowColumn366.product0_eq,
    HexagonRowColumn366.product1_eq,
    HexagonRowColumn366.product2_eq,
    HexagonRowColumn366.product3_eq,
    HexagonRowColumn366.product4_eq,
    HexagonRowColumn366.product5_eq,
    HexagonRowColumn366.product6_eq,
    HexagonRowColumn366.product7_eq] using leftFinal3_case_6_6_checked

private theorem rightFinal3_case_6_6_row_0_0_0 : (((-1 : ℤ) ^ (rightScaleBit 3 6 6).val * positiveScale (rightScaleExponent 3 6 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 6 6 : ℤ)) • HexagonAtoms366.outerLeftABC) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (negativeScale (rightScaleExponent 3 6 6) • (rowColumnMul HexagonRowColumn366.rows_assocBAC HexagonRowColumn366.cols_right2)) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem rightFinal3_case_6_6_row_0_0_1 : (((-1 : ℤ) ^ (rightScaleBit 3 6 6).val * positiveScale (rightScaleExponent 3 6 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 6 6 : ℤ)) • HexagonAtoms366.outerLeftABC) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (negativeScale (rightScaleExponent 3 6 6) • (rowColumnMul HexagonRowColumn366.rows_assocBAC HexagonRowColumn366.cols_right2)) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem rightFinal3_case_6_6_row_0_1_0 : (((-1 : ℤ) ^ (rightScaleBit 3 6 6).val * positiveScale (rightScaleExponent 3 6 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 6 6 : ℤ)) • HexagonAtoms366.outerLeftABC) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (negativeScale (rightScaleExponent 3 6 6) • (rowColumnMul HexagonRowColumn366.rows_assocBAC HexagonRowColumn366.cols_right2)) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem rightFinal3_case_6_6_row_0_1_1 : (((-1 : ℤ) ^ (rightScaleBit 3 6 6).val * positiveScale (rightScaleExponent 3 6 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 6 6 : ℤ)) • HexagonAtoms366.outerLeftABC) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (negativeScale (rightScaleExponent 3 6 6) • (rowColumnMul HexagonRowColumn366.rows_assocBAC HexagonRowColumn366.cols_right2)) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem rightFinal3_case_6_6_row_1_0_0 : (((-1 : ℤ) ^ (rightScaleBit 3 6 6).val * positiveScale (rightScaleExponent 3 6 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 6 6 : ℤ)) • HexagonAtoms366.outerLeftABC) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (negativeScale (rightScaleExponent 3 6 6) • (rowColumnMul HexagonRowColumn366.rows_assocBAC HexagonRowColumn366.cols_right2)) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem rightFinal3_case_6_6_row_1_0_1 : (((-1 : ℤ) ^ (rightScaleBit 3 6 6).val * positiveScale (rightScaleExponent 3 6 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 6 6 : ℤ)) • HexagonAtoms366.outerLeftABC) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (negativeScale (rightScaleExponent 3 6 6) • (rowColumnMul HexagonRowColumn366.rows_assocBAC HexagonRowColumn366.cols_right2)) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem rightFinal3_case_6_6_row_1_1_0 : (((-1 : ℤ) ^ (rightScaleBit 3 6 6).val * positiveScale (rightScaleExponent 3 6 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 6 6 : ℤ)) • HexagonAtoms366.outerLeftABC) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (negativeScale (rightScaleExponent 3 6 6) • (rowColumnMul HexagonRowColumn366.rows_assocBAC HexagonRowColumn366.cols_right2)) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem rightFinal3_case_6_6_row_1_1_1 : (((-1 : ℤ) ^ (rightScaleBit 3 6 6).val * positiveScale (rightScaleExponent 3 6 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 6 6 : ℤ)) • HexagonAtoms366.outerLeftABC) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (negativeScale (rightScaleExponent 3 6 6) • (rowColumnMul HexagonRowColumn366.rows_assocBAC HexagonRowColumn366.cols_right2)) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem rightFinal3_case_6_6_row_2_0_0 : (((-1 : ℤ) ^ (rightScaleBit 3 6 6).val * positiveScale (rightScaleExponent 3 6 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 6 6 : ℤ)) • HexagonAtoms366.outerLeftABC) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (negativeScale (rightScaleExponent 3 6 6) • (rowColumnMul HexagonRowColumn366.rows_assocBAC HexagonRowColumn366.cols_right2)) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem rightFinal3_case_6_6_row_2_0_1 : (((-1 : ℤ) ^ (rightScaleBit 3 6 6).val * positiveScale (rightScaleExponent 3 6 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 6 6 : ℤ)) • HexagonAtoms366.outerLeftABC) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (negativeScale (rightScaleExponent 3 6 6) • (rowColumnMul HexagonRowColumn366.rows_assocBAC HexagonRowColumn366.cols_right2)) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem rightFinal3_case_6_6_row_2_1_0 : (((-1 : ℤ) ^ (rightScaleBit 3 6 6).val * positiveScale (rightScaleExponent 3 6 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 6 6 : ℤ)) • HexagonAtoms366.outerLeftABC) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (negativeScale (rightScaleExponent 3 6 6) • (rowColumnMul HexagonRowColumn366.rows_assocBAC HexagonRowColumn366.cols_right2)) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem rightFinal3_case_6_6_row_2_1_1 : (((-1 : ℤ) ^ (rightScaleBit 3 6 6).val * positiveScale (rightScaleExponent 3 6 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 6 6 : ℤ)) • HexagonAtoms366.outerLeftABC) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (negativeScale (rightScaleExponent 3 6 6) • (rowColumnMul HexagonRowColumn366.rows_assocBAC HexagonRowColumn366.cols_right2)) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem rightFinal3_case_6_6_row_3_0_0 : (((-1 : ℤ) ^ (rightScaleBit 3 6 6).val * positiveScale (rightScaleExponent 3 6 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 6 6 : ℤ)) • HexagonAtoms366.outerLeftABC) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (negativeScale (rightScaleExponent 3 6 6) • (rowColumnMul HexagonRowColumn366.rows_assocBAC HexagonRowColumn366.cols_right2)) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem rightFinal3_case_6_6_row_3_0_1 : (((-1 : ℤ) ^ (rightScaleBit 3 6 6).val * positiveScale (rightScaleExponent 3 6 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 6 6 : ℤ)) • HexagonAtoms366.outerLeftABC) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (negativeScale (rightScaleExponent 3 6 6) • (rowColumnMul HexagonRowColumn366.rows_assocBAC HexagonRowColumn366.cols_right2)) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem rightFinal3_case_6_6_row_3_1_0 : (((-1 : ℤ) ^ (rightScaleBit 3 6 6).val * positiveScale (rightScaleExponent 3 6 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 6 6 : ℤ)) • HexagonAtoms366.outerLeftABC) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (negativeScale (rightScaleExponent 3 6 6) • (rowColumnMul HexagonRowColumn366.rows_assocBAC HexagonRowColumn366.cols_right2)) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem rightFinal3_case_6_6_row_3_1_1 : (((-1 : ℤ) ^ (rightScaleBit 3 6 6).val * positiveScale (rightScaleExponent 3 6 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 6 6 : ℤ)) • HexagonAtoms366.outerLeftABC) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (negativeScale (rightScaleExponent 3 6 6) • (rowColumnMul HexagonRowColumn366.rows_assocBAC HexagonRowColumn366.cols_right2)) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem rightFinal3_case_6_6_checked : ((-1 : ℤ) ^ (rightScaleBit 3 6 6).val * positiveScale (rightScaleExponent 3 6 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 6 6 : ℤ)) • HexagonAtoms366.outerLeftABC = negativeScale (rightScaleExponent 3 6 6) • (rowColumnMul HexagonRowColumn366.rows_assocBAC HexagonRowColumn366.cols_right2) := by
  funext r
  fin_cases r
  · exact rightFinal3_case_6_6_row_0_0_0
  · exact rightFinal3_case_6_6_row_0_0_1
  · exact rightFinal3_case_6_6_row_0_1_0
  · exact rightFinal3_case_6_6_row_0_1_1
  · exact rightFinal3_case_6_6_row_1_0_0
  · exact rightFinal3_case_6_6_row_1_0_1
  · exact rightFinal3_case_6_6_row_1_1_0
  · exact rightFinal3_case_6_6_row_1_1_1
  · exact rightFinal3_case_6_6_row_2_0_0
  · exact rightFinal3_case_6_6_row_2_0_1
  · exact rightFinal3_case_6_6_row_2_1_0
  · exact rightFinal3_case_6_6_row_2_1_1
  · exact rightFinal3_case_6_6_row_3_0_0
  · exact rightFinal3_case_6_6_row_3_0_1
  · exact rightFinal3_case_6_6_row_3_1_0
  · exact rightFinal3_case_6_6_row_3_1_1

set_option backward.isDefEq.respectTransparency false in
theorem rightFinal3_case_6_6 : ((-1 : ℤ) ^ (rightScaleBit 3 6 6).val * positiveScale (rightScaleExponent 3 6 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 6 6 : ℤ)) • outerLeftZ 3 6 6 = negativeScale (rightScaleExponent 3 6 6) • (associatorZ 6 3 6 * right2Middle3 6 6) := by
  simpa only [HexagonAtoms366.assocABC_eq,
    HexagonAtoms366.outerABC_eq,
    HexagonAtoms366.assocBAC_eq,
    HexagonAtoms366.innerABC_eq,
    HexagonAtoms366.innerRightABC_eq,
    HexagonAtoms366.inverseACB_eq,
    HexagonAtoms366.innerACB_eq,
    HexagonAtoms366.assocBCA_eq,
    HexagonAtoms366.innerRightBAC_eq,
    HexagonAtoms366.assocCAB_eq,
    HexagonAtoms366.outerLeftABC_eq,
    HexagonRowColumn366.innerACB_alias,
    HexagonRowColumn366.assocCAB_alias,
    HexagonRowColumn366.product0_eq,
    HexagonRowColumn366.product1_eq,
    HexagonRowColumn366.product2_eq,
    HexagonRowColumn366.product3_eq,
    HexagonRowColumn366.product4_eq,
    HexagonRowColumn366.product5_eq,
    HexagonRowColumn366.product6_eq,
    HexagonRowColumn366.product7_eq] using rightFinal3_case_6_6_checked

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonCases3
