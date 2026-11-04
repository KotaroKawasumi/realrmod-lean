import RMod.BrundanEllis.StackingReferenceHexagonMiddle6
import RMod.BrundanEllis.StackingReferenceSparseMatrixCheck
import RMod.BrundanEllis.StackingReferenceHexagonAtoms661
import RMod.BrundanEllis.StackingReferenceHexagonRowColumn661

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

private theorem left0Middle6_eq_case_6_1_row_0_0_0 : (left0Middle6 6 1) ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8)) = (rowColumnMul HexagonRowColumn661.rows_outerABC HexagonRowColumn661.cols_assocABC) ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem left0Middle6_eq_case_6_1_row_0_0_1 : (left0Middle6 6 1) ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8)) = (rowColumnMul HexagonRowColumn661.rows_outerABC HexagonRowColumn661.cols_assocABC) ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem left0Middle6_eq_case_6_1_row_0_0_2 : (left0Middle6 6 1) ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8)) = (rowColumnMul HexagonRowColumn661.rows_outerABC HexagonRowColumn661.cols_assocABC) ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem left0Middle6_eq_case_6_1_row_0_0_3 : (left0Middle6 6 1) ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8)) = (rowColumnMul HexagonRowColumn661.rows_outerABC HexagonRowColumn661.cols_assocABC) ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem left0Middle6_eq_case_6_1_row_0_0_4 : (left0Middle6 6 1) ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8)) = (rowColumnMul HexagonRowColumn661.rows_outerABC HexagonRowColumn661.cols_assocABC) ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem left0Middle6_eq_case_6_1_row_0_0_5 : (left0Middle6 6 1) ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8)) = (rowColumnMul HexagonRowColumn661.rows_outerABC HexagonRowColumn661.cols_assocABC) ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem left0Middle6_eq_case_6_1_row_0_0_6 : (left0Middle6 6 1) ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8)) = (rowColumnMul HexagonRowColumn661.rows_outerABC HexagonRowColumn661.cols_assocABC) ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem left0Middle6_eq_case_6_1_row_0_0_7 : (left0Middle6 6 1) ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8)) = (rowColumnMul HexagonRowColumn661.rows_outerABC HexagonRowColumn661.cols_assocABC) ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem left0Middle6_eq_case_6_1_row_1_0_0 : (left0Middle6 6 1) ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8)) = (rowColumnMul HexagonRowColumn661.rows_outerABC HexagonRowColumn661.cols_assocABC) ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem left0Middle6_eq_case_6_1_row_1_0_1 : (left0Middle6 6 1) ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8)) = (rowColumnMul HexagonRowColumn661.rows_outerABC HexagonRowColumn661.cols_assocABC) ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem left0Middle6_eq_case_6_1_row_1_0_2 : (left0Middle6 6 1) ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8)) = (rowColumnMul HexagonRowColumn661.rows_outerABC HexagonRowColumn661.cols_assocABC) ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem left0Middle6_eq_case_6_1_row_1_0_3 : (left0Middle6 6 1) ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8)) = (rowColumnMul HexagonRowColumn661.rows_outerABC HexagonRowColumn661.cols_assocABC) ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem left0Middle6_eq_case_6_1_row_1_0_4 : (left0Middle6 6 1) ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8)) = (rowColumnMul HexagonRowColumn661.rows_outerABC HexagonRowColumn661.cols_assocABC) ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem left0Middle6_eq_case_6_1_row_1_0_5 : (left0Middle6 6 1) ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8)) = (rowColumnMul HexagonRowColumn661.rows_outerABC HexagonRowColumn661.cols_assocABC) ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem left0Middle6_eq_case_6_1_row_1_0_6 : (left0Middle6 6 1) ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8)) = (rowColumnMul HexagonRowColumn661.rows_outerABC HexagonRowColumn661.cols_assocABC) ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem left0Middle6_eq_case_6_1_row_1_0_7 : (left0Middle6 6 1) ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8)) = (rowColumnMul HexagonRowColumn661.rows_outerABC HexagonRowColumn661.cols_assocABC) ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem left0Middle6_eq_case_6_1_checked : left0Middle6 6 1 = rowColumnMul HexagonRowColumn661.rows_outerABC HexagonRowColumn661.cols_assocABC := by
  funext r
  fin_cases r
  · exact left0Middle6_eq_case_6_1_row_0_0_0
  · exact left0Middle6_eq_case_6_1_row_0_0_1
  · exact left0Middle6_eq_case_6_1_row_0_0_2
  · exact left0Middle6_eq_case_6_1_row_0_0_3
  · exact left0Middle6_eq_case_6_1_row_0_0_4
  · exact left0Middle6_eq_case_6_1_row_0_0_5
  · exact left0Middle6_eq_case_6_1_row_0_0_6
  · exact left0Middle6_eq_case_6_1_row_0_0_7
  · exact left0Middle6_eq_case_6_1_row_1_0_0
  · exact left0Middle6_eq_case_6_1_row_1_0_1
  · exact left0Middle6_eq_case_6_1_row_1_0_2
  · exact left0Middle6_eq_case_6_1_row_1_0_3
  · exact left0Middle6_eq_case_6_1_row_1_0_4
  · exact left0Middle6_eq_case_6_1_row_1_0_5
  · exact left0Middle6_eq_case_6_1_row_1_0_6
  · exact left0Middle6_eq_case_6_1_row_1_0_7

set_option backward.isDefEq.respectTransparency false in
theorem left0Middle6_eq_case_6_1 : left0Middle6 6 1 = outerRightZ 6 6 1 * associatorZ 6 6 1 := by
  simpa only [HexagonAtoms661.assocABC_eq,
    HexagonAtoms661.outerABC_eq,
    HexagonAtoms661.assocBAC_eq,
    HexagonAtoms661.innerABC_eq,
    HexagonAtoms661.innerRightABC_eq,
    HexagonAtoms661.inverseACB_eq,
    HexagonAtoms661.innerACB_eq,
    HexagonAtoms661.assocBCA_eq,
    HexagonAtoms661.innerRightBAC_eq,
    HexagonAtoms661.assocCAB_eq,
    HexagonAtoms661.outerLeftABC_eq,
    HexagonRowColumn661.assocBAC_alias,
    HexagonRowColumn661.innerRightBAC_alias,
    HexagonRowColumn661.product0_eq,
    HexagonRowColumn661.product1_eq,
    HexagonRowColumn661.product2_eq,
    HexagonRowColumn661.product3_eq,
    HexagonRowColumn661.product4_eq,
    HexagonRowColumn661.product5_eq,
    HexagonRowColumn661.product6_eq,
    HexagonRowColumn661.product7_eq] using left0Middle6_eq_case_6_1_checked

private theorem left1Middle6_eq_case_6_1_row_0_0_0 : (left1Middle6 6 1) ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8)) = (rowColumnMul HexagonRowColumn661.rows_assocABC HexagonRowColumn661.cols_innerABC) ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem left1Middle6_eq_case_6_1_row_0_0_1 : (left1Middle6 6 1) ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8)) = (rowColumnMul HexagonRowColumn661.rows_assocABC HexagonRowColumn661.cols_innerABC) ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem left1Middle6_eq_case_6_1_row_0_0_2 : (left1Middle6 6 1) ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8)) = (rowColumnMul HexagonRowColumn661.rows_assocABC HexagonRowColumn661.cols_innerABC) ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem left1Middle6_eq_case_6_1_row_0_0_3 : (left1Middle6 6 1) ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8)) = (rowColumnMul HexagonRowColumn661.rows_assocABC HexagonRowColumn661.cols_innerABC) ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem left1Middle6_eq_case_6_1_row_0_0_4 : (left1Middle6 6 1) ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8)) = (rowColumnMul HexagonRowColumn661.rows_assocABC HexagonRowColumn661.cols_innerABC) ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem left1Middle6_eq_case_6_1_row_0_0_5 : (left1Middle6 6 1) ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8)) = (rowColumnMul HexagonRowColumn661.rows_assocABC HexagonRowColumn661.cols_innerABC) ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem left1Middle6_eq_case_6_1_row_0_0_6 : (left1Middle6 6 1) ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8)) = (rowColumnMul HexagonRowColumn661.rows_assocABC HexagonRowColumn661.cols_innerABC) ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem left1Middle6_eq_case_6_1_row_0_0_7 : (left1Middle6 6 1) ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8)) = (rowColumnMul HexagonRowColumn661.rows_assocABC HexagonRowColumn661.cols_innerABC) ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem left1Middle6_eq_case_6_1_row_1_0_0 : (left1Middle6 6 1) ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8)) = (rowColumnMul HexagonRowColumn661.rows_assocABC HexagonRowColumn661.cols_innerABC) ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem left1Middle6_eq_case_6_1_row_1_0_1 : (left1Middle6 6 1) ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8)) = (rowColumnMul HexagonRowColumn661.rows_assocABC HexagonRowColumn661.cols_innerABC) ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem left1Middle6_eq_case_6_1_row_1_0_2 : (left1Middle6 6 1) ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8)) = (rowColumnMul HexagonRowColumn661.rows_assocABC HexagonRowColumn661.cols_innerABC) ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem left1Middle6_eq_case_6_1_row_1_0_3 : (left1Middle6 6 1) ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8)) = (rowColumnMul HexagonRowColumn661.rows_assocABC HexagonRowColumn661.cols_innerABC) ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem left1Middle6_eq_case_6_1_row_1_0_4 : (left1Middle6 6 1) ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8)) = (rowColumnMul HexagonRowColumn661.rows_assocABC HexagonRowColumn661.cols_innerABC) ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem left1Middle6_eq_case_6_1_row_1_0_5 : (left1Middle6 6 1) ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8)) = (rowColumnMul HexagonRowColumn661.rows_assocABC HexagonRowColumn661.cols_innerABC) ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem left1Middle6_eq_case_6_1_row_1_0_6 : (left1Middle6 6 1) ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8)) = (rowColumnMul HexagonRowColumn661.rows_assocABC HexagonRowColumn661.cols_innerABC) ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem left1Middle6_eq_case_6_1_row_1_0_7 : (left1Middle6 6 1) ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8)) = (rowColumnMul HexagonRowColumn661.rows_assocABC HexagonRowColumn661.cols_innerABC) ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem left1Middle6_eq_case_6_1_checked : left1Middle6 6 1 = rowColumnMul HexagonRowColumn661.rows_assocABC HexagonRowColumn661.cols_innerABC := by
  funext r
  fin_cases r
  · exact left1Middle6_eq_case_6_1_row_0_0_0
  · exact left1Middle6_eq_case_6_1_row_0_0_1
  · exact left1Middle6_eq_case_6_1_row_0_0_2
  · exact left1Middle6_eq_case_6_1_row_0_0_3
  · exact left1Middle6_eq_case_6_1_row_0_0_4
  · exact left1Middle6_eq_case_6_1_row_0_0_5
  · exact left1Middle6_eq_case_6_1_row_0_0_6
  · exact left1Middle6_eq_case_6_1_row_0_0_7
  · exact left1Middle6_eq_case_6_1_row_1_0_0
  · exact left1Middle6_eq_case_6_1_row_1_0_1
  · exact left1Middle6_eq_case_6_1_row_1_0_2
  · exact left1Middle6_eq_case_6_1_row_1_0_3
  · exact left1Middle6_eq_case_6_1_row_1_0_4
  · exact left1Middle6_eq_case_6_1_row_1_0_5
  · exact left1Middle6_eq_case_6_1_row_1_0_6
  · exact left1Middle6_eq_case_6_1_row_1_0_7

set_option backward.isDefEq.respectTransparency false in
theorem left1Middle6_eq_case_6_1 : left1Middle6 6 1 = associatorZ 6 6 1 * innerLeftZ 6 6 1 := by
  simpa only [HexagonAtoms661.assocABC_eq,
    HexagonAtoms661.outerABC_eq,
    HexagonAtoms661.assocBAC_eq,
    HexagonAtoms661.innerABC_eq,
    HexagonAtoms661.innerRightABC_eq,
    HexagonAtoms661.inverseACB_eq,
    HexagonAtoms661.innerACB_eq,
    HexagonAtoms661.assocBCA_eq,
    HexagonAtoms661.innerRightBAC_eq,
    HexagonAtoms661.assocCAB_eq,
    HexagonAtoms661.outerLeftABC_eq,
    HexagonRowColumn661.assocBAC_alias,
    HexagonRowColumn661.innerRightBAC_alias,
    HexagonRowColumn661.product0_eq,
    HexagonRowColumn661.product1_eq,
    HexagonRowColumn661.product2_eq,
    HexagonRowColumn661.product3_eq,
    HexagonRowColumn661.product4_eq,
    HexagonRowColumn661.product5_eq,
    HexagonRowColumn661.product6_eq,
    HexagonRowColumn661.product7_eq] using left1Middle6_eq_case_6_1_checked

private theorem right0Middle6_eq_case_6_1_row_0_0_0 : (right0Middle6 6 1) ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8)) = (HexagonAtoms661.assocABC) ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right0Middle6_eq_case_6_1_row_0_0_1 : (right0Middle6 6 1) ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8)) = (HexagonAtoms661.assocABC) ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right0Middle6_eq_case_6_1_row_0_0_2 : (right0Middle6 6 1) ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8)) = (HexagonAtoms661.assocABC) ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right0Middle6_eq_case_6_1_row_0_0_3 : (right0Middle6 6 1) ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8)) = (HexagonAtoms661.assocABC) ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right0Middle6_eq_case_6_1_row_0_0_4 : (right0Middle6 6 1) ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8)) = (HexagonAtoms661.assocABC) ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right0Middle6_eq_case_6_1_row_0_0_5 : (right0Middle6 6 1) ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8)) = (HexagonAtoms661.assocABC) ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right0Middle6_eq_case_6_1_row_0_0_6 : (right0Middle6 6 1) ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8)) = (HexagonAtoms661.assocABC) ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right0Middle6_eq_case_6_1_row_0_0_7 : (right0Middle6 6 1) ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8)) = (HexagonAtoms661.assocABC) ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right0Middle6_eq_case_6_1_row_1_0_0 : (right0Middle6 6 1) ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8)) = (HexagonAtoms661.assocABC) ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right0Middle6_eq_case_6_1_row_1_0_1 : (right0Middle6 6 1) ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8)) = (HexagonAtoms661.assocABC) ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right0Middle6_eq_case_6_1_row_1_0_2 : (right0Middle6 6 1) ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8)) = (HexagonAtoms661.assocABC) ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right0Middle6_eq_case_6_1_row_1_0_3 : (right0Middle6 6 1) ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8)) = (HexagonAtoms661.assocABC) ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right0Middle6_eq_case_6_1_row_1_0_4 : (right0Middle6 6 1) ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8)) = (HexagonAtoms661.assocABC) ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right0Middle6_eq_case_6_1_row_1_0_5 : (right0Middle6 6 1) ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8)) = (HexagonAtoms661.assocABC) ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right0Middle6_eq_case_6_1_row_1_0_6 : (right0Middle6 6 1) ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8)) = (HexagonAtoms661.assocABC) ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right0Middle6_eq_case_6_1_row_1_0_7 : (right0Middle6 6 1) ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8)) = (HexagonAtoms661.assocABC) ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right0Middle6_eq_case_6_1_checked : right0Middle6 6 1 = HexagonAtoms661.assocABC := by
  funext r
  fin_cases r
  · exact right0Middle6_eq_case_6_1_row_0_0_0
  · exact right0Middle6_eq_case_6_1_row_0_0_1
  · exact right0Middle6_eq_case_6_1_row_0_0_2
  · exact right0Middle6_eq_case_6_1_row_0_0_3
  · exact right0Middle6_eq_case_6_1_row_0_0_4
  · exact right0Middle6_eq_case_6_1_row_0_0_5
  · exact right0Middle6_eq_case_6_1_row_0_0_6
  · exact right0Middle6_eq_case_6_1_row_0_0_7
  · exact right0Middle6_eq_case_6_1_row_1_0_0
  · exact right0Middle6_eq_case_6_1_row_1_0_1
  · exact right0Middle6_eq_case_6_1_row_1_0_2
  · exact right0Middle6_eq_case_6_1_row_1_0_3
  · exact right0Middle6_eq_case_6_1_row_1_0_4
  · exact right0Middle6_eq_case_6_1_row_1_0_5
  · exact right0Middle6_eq_case_6_1_row_1_0_6
  · exact right0Middle6_eq_case_6_1_row_1_0_7

set_option backward.isDefEq.respectTransparency false in
theorem right0Middle6_eq_case_6_1 : right0Middle6 6 1 = innerRightZ 6 6 1 * associatorZ 6 6 1 := by
  simpa only [HexagonAtoms661.assocABC_eq,
    HexagonAtoms661.outerABC_eq,
    HexagonAtoms661.assocBAC_eq,
    HexagonAtoms661.innerABC_eq,
    HexagonAtoms661.innerRightABC_eq,
    HexagonAtoms661.inverseACB_eq,
    HexagonAtoms661.innerACB_eq,
    HexagonAtoms661.assocBCA_eq,
    HexagonAtoms661.innerRightBAC_eq,
    HexagonAtoms661.assocCAB_eq,
    HexagonAtoms661.outerLeftABC_eq,
    HexagonRowColumn661.assocBAC_alias,
    HexagonRowColumn661.innerRightBAC_alias,
    HexagonRowColumn661.product0_eq,
    HexagonRowColumn661.product1_eq,
    HexagonRowColumn661.product2_eq,
    HexagonRowColumn661.product3_eq,
    HexagonRowColumn661.product4_eq,
    HexagonRowColumn661.product5_eq,
    HexagonRowColumn661.product6_eq,
    HexagonRowColumn661.product7_eq] using right0Middle6_eq_case_6_1_checked

private theorem right1Middle6_eq_case_6_1_row_0_0_0 : (right1Middle6 6 1) ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8)) = (rowColumnMul HexagonRowColumn661.rows_inverseACB HexagonRowColumn661.cols_right0) ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right1Middle6_eq_case_6_1_row_0_0_1 : (right1Middle6 6 1) ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8)) = (rowColumnMul HexagonRowColumn661.rows_inverseACB HexagonRowColumn661.cols_right0) ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right1Middle6_eq_case_6_1_row_0_0_2 : (right1Middle6 6 1) ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8)) = (rowColumnMul HexagonRowColumn661.rows_inverseACB HexagonRowColumn661.cols_right0) ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right1Middle6_eq_case_6_1_row_0_0_3 : (right1Middle6 6 1) ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8)) = (rowColumnMul HexagonRowColumn661.rows_inverseACB HexagonRowColumn661.cols_right0) ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right1Middle6_eq_case_6_1_row_0_0_4 : (right1Middle6 6 1) ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8)) = (rowColumnMul HexagonRowColumn661.rows_inverseACB HexagonRowColumn661.cols_right0) ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right1Middle6_eq_case_6_1_row_0_0_5 : (right1Middle6 6 1) ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8)) = (rowColumnMul HexagonRowColumn661.rows_inverseACB HexagonRowColumn661.cols_right0) ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right1Middle6_eq_case_6_1_row_0_0_6 : (right1Middle6 6 1) ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8)) = (rowColumnMul HexagonRowColumn661.rows_inverseACB HexagonRowColumn661.cols_right0) ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right1Middle6_eq_case_6_1_row_0_0_7 : (right1Middle6 6 1) ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8)) = (rowColumnMul HexagonRowColumn661.rows_inverseACB HexagonRowColumn661.cols_right0) ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right1Middle6_eq_case_6_1_row_1_0_0 : (right1Middle6 6 1) ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8)) = (rowColumnMul HexagonRowColumn661.rows_inverseACB HexagonRowColumn661.cols_right0) ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right1Middle6_eq_case_6_1_row_1_0_1 : (right1Middle6 6 1) ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8)) = (rowColumnMul HexagonRowColumn661.rows_inverseACB HexagonRowColumn661.cols_right0) ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right1Middle6_eq_case_6_1_row_1_0_2 : (right1Middle6 6 1) ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8)) = (rowColumnMul HexagonRowColumn661.rows_inverseACB HexagonRowColumn661.cols_right0) ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right1Middle6_eq_case_6_1_row_1_0_3 : (right1Middle6 6 1) ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8)) = (rowColumnMul HexagonRowColumn661.rows_inverseACB HexagonRowColumn661.cols_right0) ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right1Middle6_eq_case_6_1_row_1_0_4 : (right1Middle6 6 1) ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8)) = (rowColumnMul HexagonRowColumn661.rows_inverseACB HexagonRowColumn661.cols_right0) ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right1Middle6_eq_case_6_1_row_1_0_5 : (right1Middle6 6 1) ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8)) = (rowColumnMul HexagonRowColumn661.rows_inverseACB HexagonRowColumn661.cols_right0) ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right1Middle6_eq_case_6_1_row_1_0_6 : (right1Middle6 6 1) ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8)) = (rowColumnMul HexagonRowColumn661.rows_inverseACB HexagonRowColumn661.cols_right0) ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right1Middle6_eq_case_6_1_row_1_0_7 : (right1Middle6 6 1) ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8)) = (rowColumnMul HexagonRowColumn661.rows_inverseACB HexagonRowColumn661.cols_right0) ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right1Middle6_eq_case_6_1_checked : right1Middle6 6 1 = rowColumnMul HexagonRowColumn661.rows_inverseACB HexagonRowColumn661.cols_right0 := by
  funext r
  fin_cases r
  · exact right1Middle6_eq_case_6_1_row_0_0_0
  · exact right1Middle6_eq_case_6_1_row_0_0_1
  · exact right1Middle6_eq_case_6_1_row_0_0_2
  · exact right1Middle6_eq_case_6_1_row_0_0_3
  · exact right1Middle6_eq_case_6_1_row_0_0_4
  · exact right1Middle6_eq_case_6_1_row_0_0_5
  · exact right1Middle6_eq_case_6_1_row_0_0_6
  · exact right1Middle6_eq_case_6_1_row_0_0_7
  · exact right1Middle6_eq_case_6_1_row_1_0_0
  · exact right1Middle6_eq_case_6_1_row_1_0_1
  · exact right1Middle6_eq_case_6_1_row_1_0_2
  · exact right1Middle6_eq_case_6_1_row_1_0_3
  · exact right1Middle6_eq_case_6_1_row_1_0_4
  · exact right1Middle6_eq_case_6_1_row_1_0_5
  · exact right1Middle6_eq_case_6_1_row_1_0_6
  · exact right1Middle6_eq_case_6_1_row_1_0_7

set_option backward.isDefEq.respectTransparency false in
theorem right1Middle6_eq_case_6_1 : right1Middle6 6 1 = associatorInverseZ 6 1 6 * right0Middle6 6 1 := by
  simpa only [HexagonAtoms661.assocABC_eq,
    HexagonAtoms661.outerABC_eq,
    HexagonAtoms661.assocBAC_eq,
    HexagonAtoms661.innerABC_eq,
    HexagonAtoms661.innerRightABC_eq,
    HexagonAtoms661.inverseACB_eq,
    HexagonAtoms661.innerACB_eq,
    HexagonAtoms661.assocBCA_eq,
    HexagonAtoms661.innerRightBAC_eq,
    HexagonAtoms661.assocCAB_eq,
    HexagonAtoms661.outerLeftABC_eq,
    HexagonRowColumn661.assocBAC_alias,
    HexagonRowColumn661.innerRightBAC_alias,
    HexagonRowColumn661.product0_eq,
    HexagonRowColumn661.product1_eq,
    HexagonRowColumn661.product2_eq,
    HexagonRowColumn661.product3_eq,
    HexagonRowColumn661.product4_eq,
    HexagonRowColumn661.product5_eq,
    HexagonRowColumn661.product6_eq,
    HexagonRowColumn661.product7_eq] using right1Middle6_eq_case_6_1_checked

private theorem right2Middle6_eq_case_6_1_row_0_0_0 : (right2Middle6 6 1) ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8)) = (right1Middle6 6 1) ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right2Middle6_eq_case_6_1_row_0_0_1 : (right2Middle6 6 1) ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8)) = (right1Middle6 6 1) ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right2Middle6_eq_case_6_1_row_0_0_2 : (right2Middle6 6 1) ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8)) = (right1Middle6 6 1) ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right2Middle6_eq_case_6_1_row_0_0_3 : (right2Middle6 6 1) ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8)) = (right1Middle6 6 1) ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right2Middle6_eq_case_6_1_row_0_0_4 : (right2Middle6 6 1) ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8)) = (right1Middle6 6 1) ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right2Middle6_eq_case_6_1_row_0_0_5 : (right2Middle6 6 1) ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8)) = (right1Middle6 6 1) ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right2Middle6_eq_case_6_1_row_0_0_6 : (right2Middle6 6 1) ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8)) = (right1Middle6 6 1) ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right2Middle6_eq_case_6_1_row_0_0_7 : (right2Middle6 6 1) ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8)) = (right1Middle6 6 1) ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right2Middle6_eq_case_6_1_row_1_0_0 : (right2Middle6 6 1) ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8)) = (right1Middle6 6 1) ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right2Middle6_eq_case_6_1_row_1_0_1 : (right2Middle6 6 1) ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8)) = (right1Middle6 6 1) ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right2Middle6_eq_case_6_1_row_1_0_2 : (right2Middle6 6 1) ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8)) = (right1Middle6 6 1) ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right2Middle6_eq_case_6_1_row_1_0_3 : (right2Middle6 6 1) ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8)) = (right1Middle6 6 1) ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right2Middle6_eq_case_6_1_row_1_0_4 : (right2Middle6 6 1) ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8)) = (right1Middle6 6 1) ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right2Middle6_eq_case_6_1_row_1_0_5 : (right2Middle6 6 1) ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8)) = (right1Middle6 6 1) ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right2Middle6_eq_case_6_1_row_1_0_6 : (right2Middle6 6 1) ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8)) = (right1Middle6 6 1) ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right2Middle6_eq_case_6_1_row_1_0_7 : (right2Middle6 6 1) ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8)) = (right1Middle6 6 1) ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right2Middle6_eq_case_6_1_checked : right2Middle6 6 1 = right1Middle6 6 1 := by
  funext r
  fin_cases r
  · exact right2Middle6_eq_case_6_1_row_0_0_0
  · exact right2Middle6_eq_case_6_1_row_0_0_1
  · exact right2Middle6_eq_case_6_1_row_0_0_2
  · exact right2Middle6_eq_case_6_1_row_0_0_3
  · exact right2Middle6_eq_case_6_1_row_0_0_4
  · exact right2Middle6_eq_case_6_1_row_0_0_5
  · exact right2Middle6_eq_case_6_1_row_0_0_6
  · exact right2Middle6_eq_case_6_1_row_0_0_7
  · exact right2Middle6_eq_case_6_1_row_1_0_0
  · exact right2Middle6_eq_case_6_1_row_1_0_1
  · exact right2Middle6_eq_case_6_1_row_1_0_2
  · exact right2Middle6_eq_case_6_1_row_1_0_3
  · exact right2Middle6_eq_case_6_1_row_1_0_4
  · exact right2Middle6_eq_case_6_1_row_1_0_5
  · exact right2Middle6_eq_case_6_1_row_1_0_6
  · exact right2Middle6_eq_case_6_1_row_1_0_7

set_option backward.isDefEq.respectTransparency false in
theorem right2Middle6_eq_case_6_1 : right2Middle6 6 1 = innerLeftZ 6 1 6 * right1Middle6 6 1 := by
  simpa only [HexagonAtoms661.assocABC_eq,
    HexagonAtoms661.outerABC_eq,
    HexagonAtoms661.assocBAC_eq,
    HexagonAtoms661.innerABC_eq,
    HexagonAtoms661.innerRightABC_eq,
    HexagonAtoms661.inverseACB_eq,
    HexagonAtoms661.innerACB_eq,
    HexagonAtoms661.assocBCA_eq,
    HexagonAtoms661.innerRightBAC_eq,
    HexagonAtoms661.assocCAB_eq,
    HexagonAtoms661.outerLeftABC_eq,
    HexagonRowColumn661.assocBAC_alias,
    HexagonRowColumn661.innerRightBAC_alias,
    HexagonRowColumn661.product0_eq,
    HexagonRowColumn661.product1_eq,
    HexagonRowColumn661.product2_eq,
    HexagonRowColumn661.product3_eq,
    HexagonRowColumn661.product4_eq,
    HexagonRowColumn661.product5_eq,
    HexagonRowColumn661.product6_eq,
    HexagonRowColumn661.product7_eq] using right2Middle6_eq_case_6_1_checked

private theorem leftFinal6_case_6_1_row_0_0_0 : (((-1 : ℤ) ^ (leftScaleBit 6 6 1).val * positiveScale (leftScaleExponent 6 6 1)) •
      (rowColumnMul HexagonRowColumn661.rows_assocBCA HexagonRowColumn661.cols_left0)) ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8)) = (negativeScale (leftScaleExponent 6 6 1) • (left1Middle6 6 1)) ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem leftFinal6_case_6_1_row_0_0_1 : (((-1 : ℤ) ^ (leftScaleBit 6 6 1).val * positiveScale (leftScaleExponent 6 6 1)) •
      (rowColumnMul HexagonRowColumn661.rows_assocBCA HexagonRowColumn661.cols_left0)) ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8)) = (negativeScale (leftScaleExponent 6 6 1) • (left1Middle6 6 1)) ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem leftFinal6_case_6_1_row_0_0_2 : (((-1 : ℤ) ^ (leftScaleBit 6 6 1).val * positiveScale (leftScaleExponent 6 6 1)) •
      (rowColumnMul HexagonRowColumn661.rows_assocBCA HexagonRowColumn661.cols_left0)) ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8)) = (negativeScale (leftScaleExponent 6 6 1) • (left1Middle6 6 1)) ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem leftFinal6_case_6_1_row_0_0_3 : (((-1 : ℤ) ^ (leftScaleBit 6 6 1).val * positiveScale (leftScaleExponent 6 6 1)) •
      (rowColumnMul HexagonRowColumn661.rows_assocBCA HexagonRowColumn661.cols_left0)) ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8)) = (negativeScale (leftScaleExponent 6 6 1) • (left1Middle6 6 1)) ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem leftFinal6_case_6_1_row_0_0_4 : (((-1 : ℤ) ^ (leftScaleBit 6 6 1).val * positiveScale (leftScaleExponent 6 6 1)) •
      (rowColumnMul HexagonRowColumn661.rows_assocBCA HexagonRowColumn661.cols_left0)) ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8)) = (negativeScale (leftScaleExponent 6 6 1) • (left1Middle6 6 1)) ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem leftFinal6_case_6_1_row_0_0_5 : (((-1 : ℤ) ^ (leftScaleBit 6 6 1).val * positiveScale (leftScaleExponent 6 6 1)) •
      (rowColumnMul HexagonRowColumn661.rows_assocBCA HexagonRowColumn661.cols_left0)) ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8)) = (negativeScale (leftScaleExponent 6 6 1) • (left1Middle6 6 1)) ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem leftFinal6_case_6_1_row_0_0_6 : (((-1 : ℤ) ^ (leftScaleBit 6 6 1).val * positiveScale (leftScaleExponent 6 6 1)) •
      (rowColumnMul HexagonRowColumn661.rows_assocBCA HexagonRowColumn661.cols_left0)) ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8)) = (negativeScale (leftScaleExponent 6 6 1) • (left1Middle6 6 1)) ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem leftFinal6_case_6_1_row_0_0_7 : (((-1 : ℤ) ^ (leftScaleBit 6 6 1).val * positiveScale (leftScaleExponent 6 6 1)) •
      (rowColumnMul HexagonRowColumn661.rows_assocBCA HexagonRowColumn661.cols_left0)) ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8)) = (negativeScale (leftScaleExponent 6 6 1) • (left1Middle6 6 1)) ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem leftFinal6_case_6_1_row_1_0_0 : (((-1 : ℤ) ^ (leftScaleBit 6 6 1).val * positiveScale (leftScaleExponent 6 6 1)) •
      (rowColumnMul HexagonRowColumn661.rows_assocBCA HexagonRowColumn661.cols_left0)) ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8)) = (negativeScale (leftScaleExponent 6 6 1) • (left1Middle6 6 1)) ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem leftFinal6_case_6_1_row_1_0_1 : (((-1 : ℤ) ^ (leftScaleBit 6 6 1).val * positiveScale (leftScaleExponent 6 6 1)) •
      (rowColumnMul HexagonRowColumn661.rows_assocBCA HexagonRowColumn661.cols_left0)) ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8)) = (negativeScale (leftScaleExponent 6 6 1) • (left1Middle6 6 1)) ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem leftFinal6_case_6_1_row_1_0_2 : (((-1 : ℤ) ^ (leftScaleBit 6 6 1).val * positiveScale (leftScaleExponent 6 6 1)) •
      (rowColumnMul HexagonRowColumn661.rows_assocBCA HexagonRowColumn661.cols_left0)) ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8)) = (negativeScale (leftScaleExponent 6 6 1) • (left1Middle6 6 1)) ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem leftFinal6_case_6_1_row_1_0_3 : (((-1 : ℤ) ^ (leftScaleBit 6 6 1).val * positiveScale (leftScaleExponent 6 6 1)) •
      (rowColumnMul HexagonRowColumn661.rows_assocBCA HexagonRowColumn661.cols_left0)) ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8)) = (negativeScale (leftScaleExponent 6 6 1) • (left1Middle6 6 1)) ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem leftFinal6_case_6_1_row_1_0_4 : (((-1 : ℤ) ^ (leftScaleBit 6 6 1).val * positiveScale (leftScaleExponent 6 6 1)) •
      (rowColumnMul HexagonRowColumn661.rows_assocBCA HexagonRowColumn661.cols_left0)) ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8)) = (negativeScale (leftScaleExponent 6 6 1) • (left1Middle6 6 1)) ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem leftFinal6_case_6_1_row_1_0_5 : (((-1 : ℤ) ^ (leftScaleBit 6 6 1).val * positiveScale (leftScaleExponent 6 6 1)) •
      (rowColumnMul HexagonRowColumn661.rows_assocBCA HexagonRowColumn661.cols_left0)) ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8)) = (negativeScale (leftScaleExponent 6 6 1) • (left1Middle6 6 1)) ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem leftFinal6_case_6_1_row_1_0_6 : (((-1 : ℤ) ^ (leftScaleBit 6 6 1).val * positiveScale (leftScaleExponent 6 6 1)) •
      (rowColumnMul HexagonRowColumn661.rows_assocBCA HexagonRowColumn661.cols_left0)) ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8)) = (negativeScale (leftScaleExponent 6 6 1) • (left1Middle6 6 1)) ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem leftFinal6_case_6_1_row_1_0_7 : (((-1 : ℤ) ^ (leftScaleBit 6 6 1).val * positiveScale (leftScaleExponent 6 6 1)) •
      (rowColumnMul HexagonRowColumn661.rows_assocBCA HexagonRowColumn661.cols_left0)) ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8)) = (negativeScale (leftScaleExponent 6 6 1) • (left1Middle6 6 1)) ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem leftFinal6_case_6_1_checked : ((-1 : ℤ) ^ (leftScaleBit 6 6 1).val * positiveScale (leftScaleExponent 6 6 1)) •
      (rowColumnMul HexagonRowColumn661.rows_assocBCA HexagonRowColumn661.cols_left0) = negativeScale (leftScaleExponent 6 6 1) • (left1Middle6 6 1) := by
  funext r
  fin_cases r
  · exact leftFinal6_case_6_1_row_0_0_0
  · exact leftFinal6_case_6_1_row_0_0_1
  · exact leftFinal6_case_6_1_row_0_0_2
  · exact leftFinal6_case_6_1_row_0_0_3
  · exact leftFinal6_case_6_1_row_0_0_4
  · exact leftFinal6_case_6_1_row_0_0_5
  · exact leftFinal6_case_6_1_row_0_0_6
  · exact leftFinal6_case_6_1_row_0_0_7
  · exact leftFinal6_case_6_1_row_1_0_0
  · exact leftFinal6_case_6_1_row_1_0_1
  · exact leftFinal6_case_6_1_row_1_0_2
  · exact leftFinal6_case_6_1_row_1_0_3
  · exact leftFinal6_case_6_1_row_1_0_4
  · exact leftFinal6_case_6_1_row_1_0_5
  · exact leftFinal6_case_6_1_row_1_0_6
  · exact leftFinal6_case_6_1_row_1_0_7

set_option backward.isDefEq.respectTransparency false in
theorem leftFinal6_case_6_1 : ((-1 : ℤ) ^ (leftScaleBit 6 6 1).val * positiveScale (leftScaleExponent 6 6 1)) •
      (associatorZ 6 1 6 * left0Middle6 6 1) = negativeScale (leftScaleExponent 6 6 1) • (innerRightZ 6 6 1 * left1Middle6 6 1) := by
  simpa only [HexagonAtoms661.assocABC_eq,
    HexagonAtoms661.outerABC_eq,
    HexagonAtoms661.assocBAC_eq,
    HexagonAtoms661.innerABC_eq,
    HexagonAtoms661.innerRightABC_eq,
    HexagonAtoms661.inverseACB_eq,
    HexagonAtoms661.innerACB_eq,
    HexagonAtoms661.assocBCA_eq,
    HexagonAtoms661.innerRightBAC_eq,
    HexagonAtoms661.assocCAB_eq,
    HexagonAtoms661.outerLeftABC_eq,
    HexagonRowColumn661.assocBAC_alias,
    HexagonRowColumn661.innerRightBAC_alias,
    HexagonRowColumn661.product0_eq,
    HexagonRowColumn661.product1_eq,
    HexagonRowColumn661.product2_eq,
    HexagonRowColumn661.product3_eq,
    HexagonRowColumn661.product4_eq,
    HexagonRowColumn661.product5_eq,
    HexagonRowColumn661.product6_eq,
    HexagonRowColumn661.product7_eq] using leftFinal6_case_6_1_checked

private theorem rightFinal6_case_6_1_row_0_0_0 : (((-1 : ℤ) ^ (rightScaleBit 6 6 1).val * positiveScale (rightScaleExponent 6 6 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 1 6 : ℤ)) • HexagonAtoms661.outerLeftABC) ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8)) = (negativeScale (rightScaleExponent 6 6 1) • (rowColumnMul HexagonRowColumn661.rows_assocCAB HexagonRowColumn661.cols_right2)) ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem rightFinal6_case_6_1_row_0_0_1 : (((-1 : ℤ) ^ (rightScaleBit 6 6 1).val * positiveScale (rightScaleExponent 6 6 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 1 6 : ℤ)) • HexagonAtoms661.outerLeftABC) ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8)) = (negativeScale (rightScaleExponent 6 6 1) • (rowColumnMul HexagonRowColumn661.rows_assocCAB HexagonRowColumn661.cols_right2)) ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem rightFinal6_case_6_1_row_0_0_2 : (((-1 : ℤ) ^ (rightScaleBit 6 6 1).val * positiveScale (rightScaleExponent 6 6 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 1 6 : ℤ)) • HexagonAtoms661.outerLeftABC) ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8)) = (negativeScale (rightScaleExponent 6 6 1) • (rowColumnMul HexagonRowColumn661.rows_assocCAB HexagonRowColumn661.cols_right2)) ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem rightFinal6_case_6_1_row_0_0_3 : (((-1 : ℤ) ^ (rightScaleBit 6 6 1).val * positiveScale (rightScaleExponent 6 6 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 1 6 : ℤ)) • HexagonAtoms661.outerLeftABC) ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8)) = (negativeScale (rightScaleExponent 6 6 1) • (rowColumnMul HexagonRowColumn661.rows_assocCAB HexagonRowColumn661.cols_right2)) ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem rightFinal6_case_6_1_row_0_0_4 : (((-1 : ℤ) ^ (rightScaleBit 6 6 1).val * positiveScale (rightScaleExponent 6 6 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 1 6 : ℤ)) • HexagonAtoms661.outerLeftABC) ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8)) = (negativeScale (rightScaleExponent 6 6 1) • (rowColumnMul HexagonRowColumn661.rows_assocCAB HexagonRowColumn661.cols_right2)) ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem rightFinal6_case_6_1_row_0_0_5 : (((-1 : ℤ) ^ (rightScaleBit 6 6 1).val * positiveScale (rightScaleExponent 6 6 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 1 6 : ℤ)) • HexagonAtoms661.outerLeftABC) ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8)) = (negativeScale (rightScaleExponent 6 6 1) • (rowColumnMul HexagonRowColumn661.rows_assocCAB HexagonRowColumn661.cols_right2)) ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem rightFinal6_case_6_1_row_0_0_6 : (((-1 : ℤ) ^ (rightScaleBit 6 6 1).val * positiveScale (rightScaleExponent 6 6 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 1 6 : ℤ)) • HexagonAtoms661.outerLeftABC) ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8)) = (negativeScale (rightScaleExponent 6 6 1) • (rowColumnMul HexagonRowColumn661.rows_assocCAB HexagonRowColumn661.cols_right2)) ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem rightFinal6_case_6_1_row_0_0_7 : (((-1 : ℤ) ^ (rightScaleBit 6 6 1).val * positiveScale (rightScaleExponent 6 6 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 1 6 : ℤ)) • HexagonAtoms661.outerLeftABC) ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8)) = (negativeScale (rightScaleExponent 6 6 1) • (rowColumnMul HexagonRowColumn661.rows_assocCAB HexagonRowColumn661.cols_right2)) ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem rightFinal6_case_6_1_row_1_0_0 : (((-1 : ℤ) ^ (rightScaleBit 6 6 1).val * positiveScale (rightScaleExponent 6 6 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 1 6 : ℤ)) • HexagonAtoms661.outerLeftABC) ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8)) = (negativeScale (rightScaleExponent 6 6 1) • (rowColumnMul HexagonRowColumn661.rows_assocCAB HexagonRowColumn661.cols_right2)) ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem rightFinal6_case_6_1_row_1_0_1 : (((-1 : ℤ) ^ (rightScaleBit 6 6 1).val * positiveScale (rightScaleExponent 6 6 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 1 6 : ℤ)) • HexagonAtoms661.outerLeftABC) ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8)) = (negativeScale (rightScaleExponent 6 6 1) • (rowColumnMul HexagonRowColumn661.rows_assocCAB HexagonRowColumn661.cols_right2)) ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem rightFinal6_case_6_1_row_1_0_2 : (((-1 : ℤ) ^ (rightScaleBit 6 6 1).val * positiveScale (rightScaleExponent 6 6 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 1 6 : ℤ)) • HexagonAtoms661.outerLeftABC) ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8)) = (negativeScale (rightScaleExponent 6 6 1) • (rowColumnMul HexagonRowColumn661.rows_assocCAB HexagonRowColumn661.cols_right2)) ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem rightFinal6_case_6_1_row_1_0_3 : (((-1 : ℤ) ^ (rightScaleBit 6 6 1).val * positiveScale (rightScaleExponent 6 6 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 1 6 : ℤ)) • HexagonAtoms661.outerLeftABC) ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8)) = (negativeScale (rightScaleExponent 6 6 1) • (rowColumnMul HexagonRowColumn661.rows_assocCAB HexagonRowColumn661.cols_right2)) ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem rightFinal6_case_6_1_row_1_0_4 : (((-1 : ℤ) ^ (rightScaleBit 6 6 1).val * positiveScale (rightScaleExponent 6 6 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 1 6 : ℤ)) • HexagonAtoms661.outerLeftABC) ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8)) = (negativeScale (rightScaleExponent 6 6 1) • (rowColumnMul HexagonRowColumn661.rows_assocCAB HexagonRowColumn661.cols_right2)) ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem rightFinal6_case_6_1_row_1_0_5 : (((-1 : ℤ) ^ (rightScaleBit 6 6 1).val * positiveScale (rightScaleExponent 6 6 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 1 6 : ℤ)) • HexagonAtoms661.outerLeftABC) ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8)) = (negativeScale (rightScaleExponent 6 6 1) • (rowColumnMul HexagonRowColumn661.rows_assocCAB HexagonRowColumn661.cols_right2)) ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem rightFinal6_case_6_1_row_1_0_6 : (((-1 : ℤ) ^ (rightScaleBit 6 6 1).val * positiveScale (rightScaleExponent 6 6 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 1 6 : ℤ)) • HexagonAtoms661.outerLeftABC) ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8)) = (negativeScale (rightScaleExponent 6 6 1) • (rowColumnMul HexagonRowColumn661.rows_assocCAB HexagonRowColumn661.cols_right2)) ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem rightFinal6_case_6_1_row_1_0_7 : (((-1 : ℤ) ^ (rightScaleBit 6 6 1).val * positiveScale (rightScaleExponent 6 6 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 1 6 : ℤ)) • HexagonAtoms661.outerLeftABC) ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8)) = (negativeScale (rightScaleExponent 6 6 1) • (rowColumnMul HexagonRowColumn661.rows_assocCAB HexagonRowColumn661.cols_right2)) ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem rightFinal6_case_6_1_checked : ((-1 : ℤ) ^ (rightScaleBit 6 6 1).val * positiveScale (rightScaleExponent 6 6 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 1 6 : ℤ)) • HexagonAtoms661.outerLeftABC = negativeScale (rightScaleExponent 6 6 1) • (rowColumnMul HexagonRowColumn661.rows_assocCAB HexagonRowColumn661.cols_right2) := by
  funext r
  fin_cases r
  · exact rightFinal6_case_6_1_row_0_0_0
  · exact rightFinal6_case_6_1_row_0_0_1
  · exact rightFinal6_case_6_1_row_0_0_2
  · exact rightFinal6_case_6_1_row_0_0_3
  · exact rightFinal6_case_6_1_row_0_0_4
  · exact rightFinal6_case_6_1_row_0_0_5
  · exact rightFinal6_case_6_1_row_0_0_6
  · exact rightFinal6_case_6_1_row_0_0_7
  · exact rightFinal6_case_6_1_row_1_0_0
  · exact rightFinal6_case_6_1_row_1_0_1
  · exact rightFinal6_case_6_1_row_1_0_2
  · exact rightFinal6_case_6_1_row_1_0_3
  · exact rightFinal6_case_6_1_row_1_0_4
  · exact rightFinal6_case_6_1_row_1_0_5
  · exact rightFinal6_case_6_1_row_1_0_6
  · exact rightFinal6_case_6_1_row_1_0_7

set_option backward.isDefEq.respectTransparency false in
theorem rightFinal6_case_6_1 : ((-1 : ℤ) ^ (rightScaleBit 6 6 1).val * positiveScale (rightScaleExponent 6 6 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 1 6 : ℤ)) • outerLeftZ 6 6 1 = negativeScale (rightScaleExponent 6 6 1) • (associatorZ 1 6 6 * right2Middle6 6 1) := by
  simpa only [HexagonAtoms661.assocABC_eq,
    HexagonAtoms661.outerABC_eq,
    HexagonAtoms661.assocBAC_eq,
    HexagonAtoms661.innerABC_eq,
    HexagonAtoms661.innerRightABC_eq,
    HexagonAtoms661.inverseACB_eq,
    HexagonAtoms661.innerACB_eq,
    HexagonAtoms661.assocBCA_eq,
    HexagonAtoms661.innerRightBAC_eq,
    HexagonAtoms661.assocCAB_eq,
    HexagonAtoms661.outerLeftABC_eq,
    HexagonRowColumn661.assocBAC_alias,
    HexagonRowColumn661.innerRightBAC_alias,
    HexagonRowColumn661.product0_eq,
    HexagonRowColumn661.product1_eq,
    HexagonRowColumn661.product2_eq,
    HexagonRowColumn661.product3_eq,
    HexagonRowColumn661.product4_eq,
    HexagonRowColumn661.product5_eq,
    HexagonRowColumn661.product6_eq,
    HexagonRowColumn661.product7_eq] using rightFinal6_case_6_1_checked

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonCases6
