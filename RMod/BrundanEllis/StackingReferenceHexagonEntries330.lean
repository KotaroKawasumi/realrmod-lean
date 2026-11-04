import RMod.BrundanEllis.StackingReferenceHexagonMiddle3
import RMod.BrundanEllis.StackingReferenceSparseMatrixCheck
import RMod.BrundanEllis.StackingReferenceHexagonAtoms330
import RMod.BrundanEllis.StackingReferenceHexagonRowColumn330

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

private theorem left0Middle3_eq_case_3_0_row_0_0_0 : (left0Middle3 3 0) ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn330.rows_outerABC HexagonRowColumn330.cols_assocABC) ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_3_0_row_0_0_1 : (left0Middle3 3 0) ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn330.rows_outerABC HexagonRowColumn330.cols_assocABC) ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_3_0_row_0_0_2 : (left0Middle3 3 0) ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn330.rows_outerABC HexagonRowColumn330.cols_assocABC) ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_3_0_row_0_0_3 : (left0Middle3 3 0) ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn330.rows_outerABC HexagonRowColumn330.cols_assocABC) ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_3_0_row_0_1_0 : (left0Middle3 3 0) ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn330.rows_outerABC HexagonRowColumn330.cols_assocABC) ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_3_0_row_0_1_1 : (left0Middle3 3 0) ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn330.rows_outerABC HexagonRowColumn330.cols_assocABC) ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_3_0_row_0_1_2 : (left0Middle3 3 0) ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn330.rows_outerABC HexagonRowColumn330.cols_assocABC) ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_3_0_row_0_1_3 : (left0Middle3 3 0) ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn330.rows_outerABC HexagonRowColumn330.cols_assocABC) ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_3_0_row_0_2_0 : (left0Middle3 3 0) ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn330.rows_outerABC HexagonRowColumn330.cols_assocABC) ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_3_0_row_0_2_1 : (left0Middle3 3 0) ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn330.rows_outerABC HexagonRowColumn330.cols_assocABC) ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_3_0_row_0_2_2 : (left0Middle3 3 0) ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn330.rows_outerABC HexagonRowColumn330.cols_assocABC) ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_3_0_row_0_2_3 : (left0Middle3 3 0) ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn330.rows_outerABC HexagonRowColumn330.cols_assocABC) ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_3_0_row_0_3_0 : (left0Middle3 3 0) ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn330.rows_outerABC HexagonRowColumn330.cols_assocABC) ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_3_0_row_0_3_1 : (left0Middle3 3 0) ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn330.rows_outerABC HexagonRowColumn330.cols_assocABC) ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_3_0_row_0_3_2 : (left0Middle3 3 0) ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn330.rows_outerABC HexagonRowColumn330.cols_assocABC) ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_3_0_row_0_3_3 : (left0Middle3 3 0) ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn330.rows_outerABC HexagonRowColumn330.cols_assocABC) ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_3_0_checked : left0Middle3 3 0 = rowColumnMul HexagonRowColumn330.rows_outerABC HexagonRowColumn330.cols_assocABC := by
  funext r
  fin_cases r
  · exact left0Middle3_eq_case_3_0_row_0_0_0
  · exact left0Middle3_eq_case_3_0_row_0_0_1
  · exact left0Middle3_eq_case_3_0_row_0_0_2
  · exact left0Middle3_eq_case_3_0_row_0_0_3
  · exact left0Middle3_eq_case_3_0_row_0_1_0
  · exact left0Middle3_eq_case_3_0_row_0_1_1
  · exact left0Middle3_eq_case_3_0_row_0_1_2
  · exact left0Middle3_eq_case_3_0_row_0_1_3
  · exact left0Middle3_eq_case_3_0_row_0_2_0
  · exact left0Middle3_eq_case_3_0_row_0_2_1
  · exact left0Middle3_eq_case_3_0_row_0_2_2
  · exact left0Middle3_eq_case_3_0_row_0_2_3
  · exact left0Middle3_eq_case_3_0_row_0_3_0
  · exact left0Middle3_eq_case_3_0_row_0_3_1
  · exact left0Middle3_eq_case_3_0_row_0_3_2
  · exact left0Middle3_eq_case_3_0_row_0_3_3

set_option backward.isDefEq.respectTransparency false in
theorem left0Middle3_eq_case_3_0 : left0Middle3 3 0 = outerRightZ 3 3 0 * associatorZ 3 3 0 := by
  simpa only [HexagonAtoms330.assocABC_eq,
    HexagonAtoms330.outerABC_eq,
    HexagonAtoms330.assocBAC_eq,
    HexagonAtoms330.innerABC_eq,
    HexagonAtoms330.innerRightABC_eq,
    HexagonAtoms330.inverseACB_eq,
    HexagonAtoms330.innerACB_eq,
    HexagonAtoms330.assocBCA_eq,
    HexagonAtoms330.innerRightBAC_eq,
    HexagonAtoms330.assocCAB_eq,
    HexagonAtoms330.outerLeftABC_eq,
    HexagonRowColumn330.assocBAC_alias,
    HexagonRowColumn330.innerRightBAC_alias,
    HexagonRowColumn330.product0_eq,
    HexagonRowColumn330.product1_eq,
    HexagonRowColumn330.product2_eq,
    HexagonRowColumn330.product3_eq,
    HexagonRowColumn330.product4_eq,
    HexagonRowColumn330.product5_eq,
    HexagonRowColumn330.product6_eq,
    HexagonRowColumn330.product7_eq] using left0Middle3_eq_case_3_0_checked

private theorem left1Middle3_eq_case_3_0_row_0_0_0 : (left1Middle3 3 0) ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn330.rows_assocABC HexagonRowColumn330.cols_innerABC) ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_3_0_row_0_0_1 : (left1Middle3 3 0) ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn330.rows_assocABC HexagonRowColumn330.cols_innerABC) ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_3_0_row_0_0_2 : (left1Middle3 3 0) ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn330.rows_assocABC HexagonRowColumn330.cols_innerABC) ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_3_0_row_0_0_3 : (left1Middle3 3 0) ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn330.rows_assocABC HexagonRowColumn330.cols_innerABC) ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_3_0_row_0_1_0 : (left1Middle3 3 0) ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn330.rows_assocABC HexagonRowColumn330.cols_innerABC) ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_3_0_row_0_1_1 : (left1Middle3 3 0) ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn330.rows_assocABC HexagonRowColumn330.cols_innerABC) ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_3_0_row_0_1_2 : (left1Middle3 3 0) ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn330.rows_assocABC HexagonRowColumn330.cols_innerABC) ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_3_0_row_0_1_3 : (left1Middle3 3 0) ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn330.rows_assocABC HexagonRowColumn330.cols_innerABC) ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_3_0_row_0_2_0 : (left1Middle3 3 0) ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn330.rows_assocABC HexagonRowColumn330.cols_innerABC) ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_3_0_row_0_2_1 : (left1Middle3 3 0) ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn330.rows_assocABC HexagonRowColumn330.cols_innerABC) ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_3_0_row_0_2_2 : (left1Middle3 3 0) ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn330.rows_assocABC HexagonRowColumn330.cols_innerABC) ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_3_0_row_0_2_3 : (left1Middle3 3 0) ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn330.rows_assocABC HexagonRowColumn330.cols_innerABC) ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_3_0_row_0_3_0 : (left1Middle3 3 0) ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn330.rows_assocABC HexagonRowColumn330.cols_innerABC) ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_3_0_row_0_3_1 : (left1Middle3 3 0) ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn330.rows_assocABC HexagonRowColumn330.cols_innerABC) ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_3_0_row_0_3_2 : (left1Middle3 3 0) ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn330.rows_assocABC HexagonRowColumn330.cols_innerABC) ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_3_0_row_0_3_3 : (left1Middle3 3 0) ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn330.rows_assocABC HexagonRowColumn330.cols_innerABC) ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_3_0_checked : left1Middle3 3 0 = rowColumnMul HexagonRowColumn330.rows_assocABC HexagonRowColumn330.cols_innerABC := by
  funext r
  fin_cases r
  · exact left1Middle3_eq_case_3_0_row_0_0_0
  · exact left1Middle3_eq_case_3_0_row_0_0_1
  · exact left1Middle3_eq_case_3_0_row_0_0_2
  · exact left1Middle3_eq_case_3_0_row_0_0_3
  · exact left1Middle3_eq_case_3_0_row_0_1_0
  · exact left1Middle3_eq_case_3_0_row_0_1_1
  · exact left1Middle3_eq_case_3_0_row_0_1_2
  · exact left1Middle3_eq_case_3_0_row_0_1_3
  · exact left1Middle3_eq_case_3_0_row_0_2_0
  · exact left1Middle3_eq_case_3_0_row_0_2_1
  · exact left1Middle3_eq_case_3_0_row_0_2_2
  · exact left1Middle3_eq_case_3_0_row_0_2_3
  · exact left1Middle3_eq_case_3_0_row_0_3_0
  · exact left1Middle3_eq_case_3_0_row_0_3_1
  · exact left1Middle3_eq_case_3_0_row_0_3_2
  · exact left1Middle3_eq_case_3_0_row_0_3_3

set_option backward.isDefEq.respectTransparency false in
theorem left1Middle3_eq_case_3_0 : left1Middle3 3 0 = associatorZ 3 3 0 * innerLeftZ 3 3 0 := by
  simpa only [HexagonAtoms330.assocABC_eq,
    HexagonAtoms330.outerABC_eq,
    HexagonAtoms330.assocBAC_eq,
    HexagonAtoms330.innerABC_eq,
    HexagonAtoms330.innerRightABC_eq,
    HexagonAtoms330.inverseACB_eq,
    HexagonAtoms330.innerACB_eq,
    HexagonAtoms330.assocBCA_eq,
    HexagonAtoms330.innerRightBAC_eq,
    HexagonAtoms330.assocCAB_eq,
    HexagonAtoms330.outerLeftABC_eq,
    HexagonRowColumn330.assocBAC_alias,
    HexagonRowColumn330.innerRightBAC_alias,
    HexagonRowColumn330.product0_eq,
    HexagonRowColumn330.product1_eq,
    HexagonRowColumn330.product2_eq,
    HexagonRowColumn330.product3_eq,
    HexagonRowColumn330.product4_eq,
    HexagonRowColumn330.product5_eq,
    HexagonRowColumn330.product6_eq,
    HexagonRowColumn330.product7_eq] using left1Middle3_eq_case_3_0_checked

private theorem right0Middle3_eq_case_3_0_row_0_0_0 : (right0Middle3 3 0) ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4)) = (HexagonAtoms330.assocABC) ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_3_0_row_0_0_1 : (right0Middle3 3 0) ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4)) = (HexagonAtoms330.assocABC) ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_3_0_row_0_0_2 : (right0Middle3 3 0) ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4)) = (HexagonAtoms330.assocABC) ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_3_0_row_0_0_3 : (right0Middle3 3 0) ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4)) = (HexagonAtoms330.assocABC) ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_3_0_row_0_1_0 : (right0Middle3 3 0) ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4)) = (HexagonAtoms330.assocABC) ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_3_0_row_0_1_1 : (right0Middle3 3 0) ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4)) = (HexagonAtoms330.assocABC) ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_3_0_row_0_1_2 : (right0Middle3 3 0) ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4)) = (HexagonAtoms330.assocABC) ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_3_0_row_0_1_3 : (right0Middle3 3 0) ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4)) = (HexagonAtoms330.assocABC) ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_3_0_row_0_2_0 : (right0Middle3 3 0) ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4)) = (HexagonAtoms330.assocABC) ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_3_0_row_0_2_1 : (right0Middle3 3 0) ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4)) = (HexagonAtoms330.assocABC) ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_3_0_row_0_2_2 : (right0Middle3 3 0) ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4)) = (HexagonAtoms330.assocABC) ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_3_0_row_0_2_3 : (right0Middle3 3 0) ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4)) = (HexagonAtoms330.assocABC) ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_3_0_row_0_3_0 : (right0Middle3 3 0) ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4)) = (HexagonAtoms330.assocABC) ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_3_0_row_0_3_1 : (right0Middle3 3 0) ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4)) = (HexagonAtoms330.assocABC) ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_3_0_row_0_3_2 : (right0Middle3 3 0) ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4)) = (HexagonAtoms330.assocABC) ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_3_0_row_0_3_3 : (right0Middle3 3 0) ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4)) = (HexagonAtoms330.assocABC) ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_3_0_checked : right0Middle3 3 0 = HexagonAtoms330.assocABC := by
  funext r
  fin_cases r
  · exact right0Middle3_eq_case_3_0_row_0_0_0
  · exact right0Middle3_eq_case_3_0_row_0_0_1
  · exact right0Middle3_eq_case_3_0_row_0_0_2
  · exact right0Middle3_eq_case_3_0_row_0_0_3
  · exact right0Middle3_eq_case_3_0_row_0_1_0
  · exact right0Middle3_eq_case_3_0_row_0_1_1
  · exact right0Middle3_eq_case_3_0_row_0_1_2
  · exact right0Middle3_eq_case_3_0_row_0_1_3
  · exact right0Middle3_eq_case_3_0_row_0_2_0
  · exact right0Middle3_eq_case_3_0_row_0_2_1
  · exact right0Middle3_eq_case_3_0_row_0_2_2
  · exact right0Middle3_eq_case_3_0_row_0_2_3
  · exact right0Middle3_eq_case_3_0_row_0_3_0
  · exact right0Middle3_eq_case_3_0_row_0_3_1
  · exact right0Middle3_eq_case_3_0_row_0_3_2
  · exact right0Middle3_eq_case_3_0_row_0_3_3

set_option backward.isDefEq.respectTransparency false in
theorem right0Middle3_eq_case_3_0 : right0Middle3 3 0 = innerRightZ 3 3 0 * associatorZ 3 3 0 := by
  simpa only [HexagonAtoms330.assocABC_eq,
    HexagonAtoms330.outerABC_eq,
    HexagonAtoms330.assocBAC_eq,
    HexagonAtoms330.innerABC_eq,
    HexagonAtoms330.innerRightABC_eq,
    HexagonAtoms330.inverseACB_eq,
    HexagonAtoms330.innerACB_eq,
    HexagonAtoms330.assocBCA_eq,
    HexagonAtoms330.innerRightBAC_eq,
    HexagonAtoms330.assocCAB_eq,
    HexagonAtoms330.outerLeftABC_eq,
    HexagonRowColumn330.assocBAC_alias,
    HexagonRowColumn330.innerRightBAC_alias,
    HexagonRowColumn330.product0_eq,
    HexagonRowColumn330.product1_eq,
    HexagonRowColumn330.product2_eq,
    HexagonRowColumn330.product3_eq,
    HexagonRowColumn330.product4_eq,
    HexagonRowColumn330.product5_eq,
    HexagonRowColumn330.product6_eq,
    HexagonRowColumn330.product7_eq] using right0Middle3_eq_case_3_0_checked

private theorem right1Middle3_eq_case_3_0_row_0_0_0 : (right1Middle3 3 0) ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4)) = (right0Middle3 3 0) ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_3_0_row_0_0_1 : (right1Middle3 3 0) ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4)) = (right0Middle3 3 0) ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_3_0_row_0_0_2 : (right1Middle3 3 0) ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4)) = (right0Middle3 3 0) ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_3_0_row_0_0_3 : (right1Middle3 3 0) ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4)) = (right0Middle3 3 0) ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_3_0_row_0_1_0 : (right1Middle3 3 0) ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4)) = (right0Middle3 3 0) ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_3_0_row_0_1_1 : (right1Middle3 3 0) ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4)) = (right0Middle3 3 0) ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_3_0_row_0_1_2 : (right1Middle3 3 0) ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4)) = (right0Middle3 3 0) ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_3_0_row_0_1_3 : (right1Middle3 3 0) ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4)) = (right0Middle3 3 0) ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_3_0_row_0_2_0 : (right1Middle3 3 0) ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4)) = (right0Middle3 3 0) ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_3_0_row_0_2_1 : (right1Middle3 3 0) ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4)) = (right0Middle3 3 0) ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_3_0_row_0_2_2 : (right1Middle3 3 0) ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4)) = (right0Middle3 3 0) ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_3_0_row_0_2_3 : (right1Middle3 3 0) ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4)) = (right0Middle3 3 0) ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_3_0_row_0_3_0 : (right1Middle3 3 0) ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4)) = (right0Middle3 3 0) ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_3_0_row_0_3_1 : (right1Middle3 3 0) ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4)) = (right0Middle3 3 0) ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_3_0_row_0_3_2 : (right1Middle3 3 0) ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4)) = (right0Middle3 3 0) ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_3_0_row_0_3_3 : (right1Middle3 3 0) ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4)) = (right0Middle3 3 0) ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_3_0_checked : right1Middle3 3 0 = right0Middle3 3 0 := by
  funext r
  fin_cases r
  · exact right1Middle3_eq_case_3_0_row_0_0_0
  · exact right1Middle3_eq_case_3_0_row_0_0_1
  · exact right1Middle3_eq_case_3_0_row_0_0_2
  · exact right1Middle3_eq_case_3_0_row_0_0_3
  · exact right1Middle3_eq_case_3_0_row_0_1_0
  · exact right1Middle3_eq_case_3_0_row_0_1_1
  · exact right1Middle3_eq_case_3_0_row_0_1_2
  · exact right1Middle3_eq_case_3_0_row_0_1_3
  · exact right1Middle3_eq_case_3_0_row_0_2_0
  · exact right1Middle3_eq_case_3_0_row_0_2_1
  · exact right1Middle3_eq_case_3_0_row_0_2_2
  · exact right1Middle3_eq_case_3_0_row_0_2_3
  · exact right1Middle3_eq_case_3_0_row_0_3_0
  · exact right1Middle3_eq_case_3_0_row_0_3_1
  · exact right1Middle3_eq_case_3_0_row_0_3_2
  · exact right1Middle3_eq_case_3_0_row_0_3_3

set_option backward.isDefEq.respectTransparency false in
theorem right1Middle3_eq_case_3_0 : right1Middle3 3 0 = associatorInverseZ 3 0 3 * right0Middle3 3 0 := by
  simpa only [HexagonAtoms330.assocABC_eq,
    HexagonAtoms330.outerABC_eq,
    HexagonAtoms330.assocBAC_eq,
    HexagonAtoms330.innerABC_eq,
    HexagonAtoms330.innerRightABC_eq,
    HexagonAtoms330.inverseACB_eq,
    HexagonAtoms330.innerACB_eq,
    HexagonAtoms330.assocBCA_eq,
    HexagonAtoms330.innerRightBAC_eq,
    HexagonAtoms330.assocCAB_eq,
    HexagonAtoms330.outerLeftABC_eq,
    HexagonRowColumn330.assocBAC_alias,
    HexagonRowColumn330.innerRightBAC_alias,
    HexagonRowColumn330.product0_eq,
    HexagonRowColumn330.product1_eq,
    HexagonRowColumn330.product2_eq,
    HexagonRowColumn330.product3_eq,
    HexagonRowColumn330.product4_eq,
    HexagonRowColumn330.product5_eq,
    HexagonRowColumn330.product6_eq,
    HexagonRowColumn330.product7_eq] using right1Middle3_eq_case_3_0_checked

private theorem right2Middle3_eq_case_3_0_row_0_0_0 : (right2Middle3 3 0) ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4)) = (right1Middle3 3 0) ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_3_0_row_0_0_1 : (right2Middle3 3 0) ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4)) = (right1Middle3 3 0) ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_3_0_row_0_0_2 : (right2Middle3 3 0) ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4)) = (right1Middle3 3 0) ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_3_0_row_0_0_3 : (right2Middle3 3 0) ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4)) = (right1Middle3 3 0) ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_3_0_row_0_1_0 : (right2Middle3 3 0) ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4)) = (right1Middle3 3 0) ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_3_0_row_0_1_1 : (right2Middle3 3 0) ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4)) = (right1Middle3 3 0) ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_3_0_row_0_1_2 : (right2Middle3 3 0) ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4)) = (right1Middle3 3 0) ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_3_0_row_0_1_3 : (right2Middle3 3 0) ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4)) = (right1Middle3 3 0) ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_3_0_row_0_2_0 : (right2Middle3 3 0) ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4)) = (right1Middle3 3 0) ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_3_0_row_0_2_1 : (right2Middle3 3 0) ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4)) = (right1Middle3 3 0) ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_3_0_row_0_2_2 : (right2Middle3 3 0) ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4)) = (right1Middle3 3 0) ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_3_0_row_0_2_3 : (right2Middle3 3 0) ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4)) = (right1Middle3 3 0) ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_3_0_row_0_3_0 : (right2Middle3 3 0) ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4)) = (right1Middle3 3 0) ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_3_0_row_0_3_1 : (right2Middle3 3 0) ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4)) = (right1Middle3 3 0) ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_3_0_row_0_3_2 : (right2Middle3 3 0) ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4)) = (right1Middle3 3 0) ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_3_0_row_0_3_3 : (right2Middle3 3 0) ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4)) = (right1Middle3 3 0) ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_3_0_checked : right2Middle3 3 0 = right1Middle3 3 0 := by
  funext r
  fin_cases r
  · exact right2Middle3_eq_case_3_0_row_0_0_0
  · exact right2Middle3_eq_case_3_0_row_0_0_1
  · exact right2Middle3_eq_case_3_0_row_0_0_2
  · exact right2Middle3_eq_case_3_0_row_0_0_3
  · exact right2Middle3_eq_case_3_0_row_0_1_0
  · exact right2Middle3_eq_case_3_0_row_0_1_1
  · exact right2Middle3_eq_case_3_0_row_0_1_2
  · exact right2Middle3_eq_case_3_0_row_0_1_3
  · exact right2Middle3_eq_case_3_0_row_0_2_0
  · exact right2Middle3_eq_case_3_0_row_0_2_1
  · exact right2Middle3_eq_case_3_0_row_0_2_2
  · exact right2Middle3_eq_case_3_0_row_0_2_3
  · exact right2Middle3_eq_case_3_0_row_0_3_0
  · exact right2Middle3_eq_case_3_0_row_0_3_1
  · exact right2Middle3_eq_case_3_0_row_0_3_2
  · exact right2Middle3_eq_case_3_0_row_0_3_3

set_option backward.isDefEq.respectTransparency false in
theorem right2Middle3_eq_case_3_0 : right2Middle3 3 0 = innerLeftZ 3 0 3 * right1Middle3 3 0 := by
  simpa only [HexagonAtoms330.assocABC_eq,
    HexagonAtoms330.outerABC_eq,
    HexagonAtoms330.assocBAC_eq,
    HexagonAtoms330.innerABC_eq,
    HexagonAtoms330.innerRightABC_eq,
    HexagonAtoms330.inverseACB_eq,
    HexagonAtoms330.innerACB_eq,
    HexagonAtoms330.assocBCA_eq,
    HexagonAtoms330.innerRightBAC_eq,
    HexagonAtoms330.assocCAB_eq,
    HexagonAtoms330.outerLeftABC_eq,
    HexagonRowColumn330.assocBAC_alias,
    HexagonRowColumn330.innerRightBAC_alias,
    HexagonRowColumn330.product0_eq,
    HexagonRowColumn330.product1_eq,
    HexagonRowColumn330.product2_eq,
    HexagonRowColumn330.product3_eq,
    HexagonRowColumn330.product4_eq,
    HexagonRowColumn330.product5_eq,
    HexagonRowColumn330.product6_eq,
    HexagonRowColumn330.product7_eq] using right2Middle3_eq_case_3_0_checked

private theorem leftFinal3_case_3_0_row_0_0_0 : (((-1 : ℤ) ^ (leftScaleBit 3 3 0).val * positiveScale (leftScaleExponent 3 3 0)) •
      (left0Middle3 3 0)) ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4)) = (negativeScale (leftScaleExponent 3 3 0) • (left1Middle3 3 0)) ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal3_case_3_0_row_0_0_1 : (((-1 : ℤ) ^ (leftScaleBit 3 3 0).val * positiveScale (leftScaleExponent 3 3 0)) •
      (left0Middle3 3 0)) ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4)) = (negativeScale (leftScaleExponent 3 3 0) • (left1Middle3 3 0)) ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal3_case_3_0_row_0_0_2 : (((-1 : ℤ) ^ (leftScaleBit 3 3 0).val * positiveScale (leftScaleExponent 3 3 0)) •
      (left0Middle3 3 0)) ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4)) = (negativeScale (leftScaleExponent 3 3 0) • (left1Middle3 3 0)) ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal3_case_3_0_row_0_0_3 : (((-1 : ℤ) ^ (leftScaleBit 3 3 0).val * positiveScale (leftScaleExponent 3 3 0)) •
      (left0Middle3 3 0)) ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4)) = (negativeScale (leftScaleExponent 3 3 0) • (left1Middle3 3 0)) ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal3_case_3_0_row_0_1_0 : (((-1 : ℤ) ^ (leftScaleBit 3 3 0).val * positiveScale (leftScaleExponent 3 3 0)) •
      (left0Middle3 3 0)) ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4)) = (negativeScale (leftScaleExponent 3 3 0) • (left1Middle3 3 0)) ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal3_case_3_0_row_0_1_1 : (((-1 : ℤ) ^ (leftScaleBit 3 3 0).val * positiveScale (leftScaleExponent 3 3 0)) •
      (left0Middle3 3 0)) ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4)) = (negativeScale (leftScaleExponent 3 3 0) • (left1Middle3 3 0)) ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal3_case_3_0_row_0_1_2 : (((-1 : ℤ) ^ (leftScaleBit 3 3 0).val * positiveScale (leftScaleExponent 3 3 0)) •
      (left0Middle3 3 0)) ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4)) = (negativeScale (leftScaleExponent 3 3 0) • (left1Middle3 3 0)) ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal3_case_3_0_row_0_1_3 : (((-1 : ℤ) ^ (leftScaleBit 3 3 0).val * positiveScale (leftScaleExponent 3 3 0)) •
      (left0Middle3 3 0)) ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4)) = (negativeScale (leftScaleExponent 3 3 0) • (left1Middle3 3 0)) ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal3_case_3_0_row_0_2_0 : (((-1 : ℤ) ^ (leftScaleBit 3 3 0).val * positiveScale (leftScaleExponent 3 3 0)) •
      (left0Middle3 3 0)) ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4)) = (negativeScale (leftScaleExponent 3 3 0) • (left1Middle3 3 0)) ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal3_case_3_0_row_0_2_1 : (((-1 : ℤ) ^ (leftScaleBit 3 3 0).val * positiveScale (leftScaleExponent 3 3 0)) •
      (left0Middle3 3 0)) ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4)) = (negativeScale (leftScaleExponent 3 3 0) • (left1Middle3 3 0)) ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal3_case_3_0_row_0_2_2 : (((-1 : ℤ) ^ (leftScaleBit 3 3 0).val * positiveScale (leftScaleExponent 3 3 0)) •
      (left0Middle3 3 0)) ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4)) = (negativeScale (leftScaleExponent 3 3 0) • (left1Middle3 3 0)) ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal3_case_3_0_row_0_2_3 : (((-1 : ℤ) ^ (leftScaleBit 3 3 0).val * positiveScale (leftScaleExponent 3 3 0)) •
      (left0Middle3 3 0)) ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4)) = (negativeScale (leftScaleExponent 3 3 0) • (left1Middle3 3 0)) ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal3_case_3_0_row_0_3_0 : (((-1 : ℤ) ^ (leftScaleBit 3 3 0).val * positiveScale (leftScaleExponent 3 3 0)) •
      (left0Middle3 3 0)) ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4)) = (negativeScale (leftScaleExponent 3 3 0) • (left1Middle3 3 0)) ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal3_case_3_0_row_0_3_1 : (((-1 : ℤ) ^ (leftScaleBit 3 3 0).val * positiveScale (leftScaleExponent 3 3 0)) •
      (left0Middle3 3 0)) ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4)) = (negativeScale (leftScaleExponent 3 3 0) • (left1Middle3 3 0)) ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal3_case_3_0_row_0_3_2 : (((-1 : ℤ) ^ (leftScaleBit 3 3 0).val * positiveScale (leftScaleExponent 3 3 0)) •
      (left0Middle3 3 0)) ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4)) = (negativeScale (leftScaleExponent 3 3 0) • (left1Middle3 3 0)) ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal3_case_3_0_row_0_3_3 : (((-1 : ℤ) ^ (leftScaleBit 3 3 0).val * positiveScale (leftScaleExponent 3 3 0)) •
      (left0Middle3 3 0)) ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4)) = (negativeScale (leftScaleExponent 3 3 0) • (left1Middle3 3 0)) ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal3_case_3_0_checked : ((-1 : ℤ) ^ (leftScaleBit 3 3 0).val * positiveScale (leftScaleExponent 3 3 0)) •
      (left0Middle3 3 0) = negativeScale (leftScaleExponent 3 3 0) • (left1Middle3 3 0) := by
  funext r
  fin_cases r
  · exact leftFinal3_case_3_0_row_0_0_0
  · exact leftFinal3_case_3_0_row_0_0_1
  · exact leftFinal3_case_3_0_row_0_0_2
  · exact leftFinal3_case_3_0_row_0_0_3
  · exact leftFinal3_case_3_0_row_0_1_0
  · exact leftFinal3_case_3_0_row_0_1_1
  · exact leftFinal3_case_3_0_row_0_1_2
  · exact leftFinal3_case_3_0_row_0_1_3
  · exact leftFinal3_case_3_0_row_0_2_0
  · exact leftFinal3_case_3_0_row_0_2_1
  · exact leftFinal3_case_3_0_row_0_2_2
  · exact leftFinal3_case_3_0_row_0_2_3
  · exact leftFinal3_case_3_0_row_0_3_0
  · exact leftFinal3_case_3_0_row_0_3_1
  · exact leftFinal3_case_3_0_row_0_3_2
  · exact leftFinal3_case_3_0_row_0_3_3

set_option backward.isDefEq.respectTransparency false in
theorem leftFinal3_case_3_0 : ((-1 : ℤ) ^ (leftScaleBit 3 3 0).val * positiveScale (leftScaleExponent 3 3 0)) •
      (associatorZ 3 0 3 * left0Middle3 3 0) = negativeScale (leftScaleExponent 3 3 0) • (innerRightZ 3 3 0 * left1Middle3 3 0) := by
  simpa only [HexagonAtoms330.assocABC_eq,
    HexagonAtoms330.outerABC_eq,
    HexagonAtoms330.assocBAC_eq,
    HexagonAtoms330.innerABC_eq,
    HexagonAtoms330.innerRightABC_eq,
    HexagonAtoms330.inverseACB_eq,
    HexagonAtoms330.innerACB_eq,
    HexagonAtoms330.assocBCA_eq,
    HexagonAtoms330.innerRightBAC_eq,
    HexagonAtoms330.assocCAB_eq,
    HexagonAtoms330.outerLeftABC_eq,
    HexagonRowColumn330.assocBAC_alias,
    HexagonRowColumn330.innerRightBAC_alias,
    HexagonRowColumn330.product0_eq,
    HexagonRowColumn330.product1_eq,
    HexagonRowColumn330.product2_eq,
    HexagonRowColumn330.product3_eq,
    HexagonRowColumn330.product4_eq,
    HexagonRowColumn330.product5_eq,
    HexagonRowColumn330.product6_eq,
    HexagonRowColumn330.product7_eq] using leftFinal3_case_3_0_checked

private theorem rightFinal3_case_3_0_row_0_0_0 : (((-1 : ℤ) ^ (rightScaleBit 3 3 0).val * positiveScale (rightScaleExponent 3 3 0) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 0 3 : ℤ)) • HexagonAtoms330.outerLeftABC) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (negativeScale (rightScaleExponent 3 3 0) • (rowColumnMul HexagonRowColumn330.rows_assocCAB HexagonRowColumn330.cols_right2)) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal3_case_3_0_row_0_0_1 : (((-1 : ℤ) ^ (rightScaleBit 3 3 0).val * positiveScale (rightScaleExponent 3 3 0) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 0 3 : ℤ)) • HexagonAtoms330.outerLeftABC) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (negativeScale (rightScaleExponent 3 3 0) • (rowColumnMul HexagonRowColumn330.rows_assocCAB HexagonRowColumn330.cols_right2)) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal3_case_3_0_row_0_0_2 : (((-1 : ℤ) ^ (rightScaleBit 3 3 0).val * positiveScale (rightScaleExponent 3 3 0) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 0 3 : ℤ)) • HexagonAtoms330.outerLeftABC) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (negativeScale (rightScaleExponent 3 3 0) • (rowColumnMul HexagonRowColumn330.rows_assocCAB HexagonRowColumn330.cols_right2)) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal3_case_3_0_row_0_0_3 : (((-1 : ℤ) ^ (rightScaleBit 3 3 0).val * positiveScale (rightScaleExponent 3 3 0) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 0 3 : ℤ)) • HexagonAtoms330.outerLeftABC) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (negativeScale (rightScaleExponent 3 3 0) • (rowColumnMul HexagonRowColumn330.rows_assocCAB HexagonRowColumn330.cols_right2)) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal3_case_3_0_row_1_0_0 : (((-1 : ℤ) ^ (rightScaleBit 3 3 0).val * positiveScale (rightScaleExponent 3 3 0) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 0 3 : ℤ)) • HexagonAtoms330.outerLeftABC) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (negativeScale (rightScaleExponent 3 3 0) • (rowColumnMul HexagonRowColumn330.rows_assocCAB HexagonRowColumn330.cols_right2)) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal3_case_3_0_row_1_0_1 : (((-1 : ℤ) ^ (rightScaleBit 3 3 0).val * positiveScale (rightScaleExponent 3 3 0) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 0 3 : ℤ)) • HexagonAtoms330.outerLeftABC) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (negativeScale (rightScaleExponent 3 3 0) • (rowColumnMul HexagonRowColumn330.rows_assocCAB HexagonRowColumn330.cols_right2)) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal3_case_3_0_row_1_0_2 : (((-1 : ℤ) ^ (rightScaleBit 3 3 0).val * positiveScale (rightScaleExponent 3 3 0) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 0 3 : ℤ)) • HexagonAtoms330.outerLeftABC) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (negativeScale (rightScaleExponent 3 3 0) • (rowColumnMul HexagonRowColumn330.rows_assocCAB HexagonRowColumn330.cols_right2)) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal3_case_3_0_row_1_0_3 : (((-1 : ℤ) ^ (rightScaleBit 3 3 0).val * positiveScale (rightScaleExponent 3 3 0) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 0 3 : ℤ)) • HexagonAtoms330.outerLeftABC) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (negativeScale (rightScaleExponent 3 3 0) • (rowColumnMul HexagonRowColumn330.rows_assocCAB HexagonRowColumn330.cols_right2)) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal3_case_3_0_row_2_0_0 : (((-1 : ℤ) ^ (rightScaleBit 3 3 0).val * positiveScale (rightScaleExponent 3 3 0) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 0 3 : ℤ)) • HexagonAtoms330.outerLeftABC) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (negativeScale (rightScaleExponent 3 3 0) • (rowColumnMul HexagonRowColumn330.rows_assocCAB HexagonRowColumn330.cols_right2)) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal3_case_3_0_row_2_0_1 : (((-1 : ℤ) ^ (rightScaleBit 3 3 0).val * positiveScale (rightScaleExponent 3 3 0) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 0 3 : ℤ)) • HexagonAtoms330.outerLeftABC) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (negativeScale (rightScaleExponent 3 3 0) • (rowColumnMul HexagonRowColumn330.rows_assocCAB HexagonRowColumn330.cols_right2)) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal3_case_3_0_row_2_0_2 : (((-1 : ℤ) ^ (rightScaleBit 3 3 0).val * positiveScale (rightScaleExponent 3 3 0) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 0 3 : ℤ)) • HexagonAtoms330.outerLeftABC) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (negativeScale (rightScaleExponent 3 3 0) • (rowColumnMul HexagonRowColumn330.rows_assocCAB HexagonRowColumn330.cols_right2)) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal3_case_3_0_row_2_0_3 : (((-1 : ℤ) ^ (rightScaleBit 3 3 0).val * positiveScale (rightScaleExponent 3 3 0) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 0 3 : ℤ)) • HexagonAtoms330.outerLeftABC) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (negativeScale (rightScaleExponent 3 3 0) • (rowColumnMul HexagonRowColumn330.rows_assocCAB HexagonRowColumn330.cols_right2)) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal3_case_3_0_row_3_0_0 : (((-1 : ℤ) ^ (rightScaleBit 3 3 0).val * positiveScale (rightScaleExponent 3 3 0) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 0 3 : ℤ)) • HexagonAtoms330.outerLeftABC) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (negativeScale (rightScaleExponent 3 3 0) • (rowColumnMul HexagonRowColumn330.rows_assocCAB HexagonRowColumn330.cols_right2)) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal3_case_3_0_row_3_0_1 : (((-1 : ℤ) ^ (rightScaleBit 3 3 0).val * positiveScale (rightScaleExponent 3 3 0) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 0 3 : ℤ)) • HexagonAtoms330.outerLeftABC) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (negativeScale (rightScaleExponent 3 3 0) • (rowColumnMul HexagonRowColumn330.rows_assocCAB HexagonRowColumn330.cols_right2)) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal3_case_3_0_row_3_0_2 : (((-1 : ℤ) ^ (rightScaleBit 3 3 0).val * positiveScale (rightScaleExponent 3 3 0) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 0 3 : ℤ)) • HexagonAtoms330.outerLeftABC) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (negativeScale (rightScaleExponent 3 3 0) • (rowColumnMul HexagonRowColumn330.rows_assocCAB HexagonRowColumn330.cols_right2)) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal3_case_3_0_row_3_0_3 : (((-1 : ℤ) ^ (rightScaleBit 3 3 0).val * positiveScale (rightScaleExponent 3 3 0) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 0 3 : ℤ)) • HexagonAtoms330.outerLeftABC) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (negativeScale (rightScaleExponent 3 3 0) • (rowColumnMul HexagonRowColumn330.rows_assocCAB HexagonRowColumn330.cols_right2)) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal3_case_3_0_checked : ((-1 : ℤ) ^ (rightScaleBit 3 3 0).val * positiveScale (rightScaleExponent 3 3 0) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 0 3 : ℤ)) • HexagonAtoms330.outerLeftABC = negativeScale (rightScaleExponent 3 3 0) • (rowColumnMul HexagonRowColumn330.rows_assocCAB HexagonRowColumn330.cols_right2) := by
  funext r
  fin_cases r
  · exact rightFinal3_case_3_0_row_0_0_0
  · exact rightFinal3_case_3_0_row_0_0_1
  · exact rightFinal3_case_3_0_row_0_0_2
  · exact rightFinal3_case_3_0_row_0_0_3
  · exact rightFinal3_case_3_0_row_1_0_0
  · exact rightFinal3_case_3_0_row_1_0_1
  · exact rightFinal3_case_3_0_row_1_0_2
  · exact rightFinal3_case_3_0_row_1_0_3
  · exact rightFinal3_case_3_0_row_2_0_0
  · exact rightFinal3_case_3_0_row_2_0_1
  · exact rightFinal3_case_3_0_row_2_0_2
  · exact rightFinal3_case_3_0_row_2_0_3
  · exact rightFinal3_case_3_0_row_3_0_0
  · exact rightFinal3_case_3_0_row_3_0_1
  · exact rightFinal3_case_3_0_row_3_0_2
  · exact rightFinal3_case_3_0_row_3_0_3

set_option backward.isDefEq.respectTransparency false in
theorem rightFinal3_case_3_0 : ((-1 : ℤ) ^ (rightScaleBit 3 3 0).val * positiveScale (rightScaleExponent 3 3 0) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 0 3 : ℤ)) • outerLeftZ 3 3 0 = negativeScale (rightScaleExponent 3 3 0) • (associatorZ 0 3 3 * right2Middle3 3 0) := by
  simpa only [HexagonAtoms330.assocABC_eq,
    HexagonAtoms330.outerABC_eq,
    HexagonAtoms330.assocBAC_eq,
    HexagonAtoms330.innerABC_eq,
    HexagonAtoms330.innerRightABC_eq,
    HexagonAtoms330.inverseACB_eq,
    HexagonAtoms330.innerACB_eq,
    HexagonAtoms330.assocBCA_eq,
    HexagonAtoms330.innerRightBAC_eq,
    HexagonAtoms330.assocCAB_eq,
    HexagonAtoms330.outerLeftABC_eq,
    HexagonRowColumn330.assocBAC_alias,
    HexagonRowColumn330.innerRightBAC_alias,
    HexagonRowColumn330.product0_eq,
    HexagonRowColumn330.product1_eq,
    HexagonRowColumn330.product2_eq,
    HexagonRowColumn330.product3_eq,
    HexagonRowColumn330.product4_eq,
    HexagonRowColumn330.product5_eq,
    HexagonRowColumn330.product6_eq,
    HexagonRowColumn330.product7_eq] using rightFinal3_case_3_0_checked

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonCases3
