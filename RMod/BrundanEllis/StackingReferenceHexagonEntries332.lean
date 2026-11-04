import RMod.BrundanEllis.StackingReferenceHexagonMiddle3
import RMod.BrundanEllis.StackingReferenceSparseMatrixCheck
import RMod.BrundanEllis.StackingReferenceHexagonAtoms332
import RMod.BrundanEllis.StackingReferenceHexagonRowColumn332

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

private theorem left0Middle3_eq_case_3_2_row_0_0_0 : (left0Middle3 3 2) ((0 : Fin 2), (0 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn332.rows_outerABC HexagonRowColumn332.cols_assocABC) ((0 : Fin 2), (0 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem left0Middle3_eq_case_3_2_row_0_1_0 : (left0Middle3 3 2) ((0 : Fin 2), (1 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn332.rows_outerABC HexagonRowColumn332.cols_assocABC) ((0 : Fin 2), (1 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem left0Middle3_eq_case_3_2_row_0_2_0 : (left0Middle3 3 2) ((0 : Fin 2), (2 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn332.rows_outerABC HexagonRowColumn332.cols_assocABC) ((0 : Fin 2), (2 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem left0Middle3_eq_case_3_2_row_0_3_0 : (left0Middle3 3 2) ((0 : Fin 2), (3 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn332.rows_outerABC HexagonRowColumn332.cols_assocABC) ((0 : Fin 2), (3 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem left0Middle3_eq_case_3_2_row_0_4_0 : (left0Middle3 3 2) ((0 : Fin 2), (4 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn332.rows_outerABC HexagonRowColumn332.cols_assocABC) ((0 : Fin 2), (4 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem left0Middle3_eq_case_3_2_row_0_5_0 : (left0Middle3 3 2) ((0 : Fin 2), (5 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn332.rows_outerABC HexagonRowColumn332.cols_assocABC) ((0 : Fin 2), (5 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem left0Middle3_eq_case_3_2_row_0_6_0 : (left0Middle3 3 2) ((0 : Fin 2), (6 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn332.rows_outerABC HexagonRowColumn332.cols_assocABC) ((0 : Fin 2), (6 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem left0Middle3_eq_case_3_2_row_0_7_0 : (left0Middle3 3 2) ((0 : Fin 2), (7 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn332.rows_outerABC HexagonRowColumn332.cols_assocABC) ((0 : Fin 2), (7 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem left0Middle3_eq_case_3_2_row_1_0_0 : (left0Middle3 3 2) ((1 : Fin 2), (0 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn332.rows_outerABC HexagonRowColumn332.cols_assocABC) ((1 : Fin 2), (0 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem left0Middle3_eq_case_3_2_row_1_1_0 : (left0Middle3 3 2) ((1 : Fin 2), (1 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn332.rows_outerABC HexagonRowColumn332.cols_assocABC) ((1 : Fin 2), (1 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem left0Middle3_eq_case_3_2_row_1_2_0 : (left0Middle3 3 2) ((1 : Fin 2), (2 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn332.rows_outerABC HexagonRowColumn332.cols_assocABC) ((1 : Fin 2), (2 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem left0Middle3_eq_case_3_2_row_1_3_0 : (left0Middle3 3 2) ((1 : Fin 2), (3 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn332.rows_outerABC HexagonRowColumn332.cols_assocABC) ((1 : Fin 2), (3 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem left0Middle3_eq_case_3_2_row_1_4_0 : (left0Middle3 3 2) ((1 : Fin 2), (4 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn332.rows_outerABC HexagonRowColumn332.cols_assocABC) ((1 : Fin 2), (4 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem left0Middle3_eq_case_3_2_row_1_5_0 : (left0Middle3 3 2) ((1 : Fin 2), (5 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn332.rows_outerABC HexagonRowColumn332.cols_assocABC) ((1 : Fin 2), (5 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem left0Middle3_eq_case_3_2_row_1_6_0 : (left0Middle3 3 2) ((1 : Fin 2), (6 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn332.rows_outerABC HexagonRowColumn332.cols_assocABC) ((1 : Fin 2), (6 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem left0Middle3_eq_case_3_2_row_1_7_0 : (left0Middle3 3 2) ((1 : Fin 2), (7 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn332.rows_outerABC HexagonRowColumn332.cols_assocABC) ((1 : Fin 2), (7 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem left0Middle3_eq_case_3_2_checked : left0Middle3 3 2 = rowColumnMul HexagonRowColumn332.rows_outerABC HexagonRowColumn332.cols_assocABC := by
  funext r
  fin_cases r
  · exact left0Middle3_eq_case_3_2_row_0_0_0
  · exact left0Middle3_eq_case_3_2_row_0_1_0
  · exact left0Middle3_eq_case_3_2_row_0_2_0
  · exact left0Middle3_eq_case_3_2_row_0_3_0
  · exact left0Middle3_eq_case_3_2_row_0_4_0
  · exact left0Middle3_eq_case_3_2_row_0_5_0
  · exact left0Middle3_eq_case_3_2_row_0_6_0
  · exact left0Middle3_eq_case_3_2_row_0_7_0
  · exact left0Middle3_eq_case_3_2_row_1_0_0
  · exact left0Middle3_eq_case_3_2_row_1_1_0
  · exact left0Middle3_eq_case_3_2_row_1_2_0
  · exact left0Middle3_eq_case_3_2_row_1_3_0
  · exact left0Middle3_eq_case_3_2_row_1_4_0
  · exact left0Middle3_eq_case_3_2_row_1_5_0
  · exact left0Middle3_eq_case_3_2_row_1_6_0
  · exact left0Middle3_eq_case_3_2_row_1_7_0

set_option backward.isDefEq.respectTransparency false in
theorem left0Middle3_eq_case_3_2 : left0Middle3 3 2 = outerRightZ 3 3 2 * associatorZ 3 3 2 := by
  simpa only [HexagonAtoms332.assocABC_eq,
    HexagonAtoms332.outerABC_eq,
    HexagonAtoms332.assocBAC_eq,
    HexagonAtoms332.innerABC_eq,
    HexagonAtoms332.innerRightABC_eq,
    HexagonAtoms332.inverseACB_eq,
    HexagonAtoms332.innerACB_eq,
    HexagonAtoms332.assocBCA_eq,
    HexagonAtoms332.innerRightBAC_eq,
    HexagonAtoms332.assocCAB_eq,
    HexagonAtoms332.outerLeftABC_eq,
    HexagonRowColumn332.assocBAC_alias,
    HexagonRowColumn332.innerRightBAC_alias,
    HexagonRowColumn332.product0_eq,
    HexagonRowColumn332.product1_eq,
    HexagonRowColumn332.product2_eq,
    HexagonRowColumn332.product3_eq,
    HexagonRowColumn332.product4_eq,
    HexagonRowColumn332.product5_eq,
    HexagonRowColumn332.product6_eq,
    HexagonRowColumn332.product7_eq] using left0Middle3_eq_case_3_2_checked

private theorem left1Middle3_eq_case_3_2_row_0_0_0 : (left1Middle3 3 2) ((0 : Fin 2), (0 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn332.rows_assocABC HexagonRowColumn332.cols_innerABC) ((0 : Fin 2), (0 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem left1Middle3_eq_case_3_2_row_0_1_0 : (left1Middle3 3 2) ((0 : Fin 2), (1 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn332.rows_assocABC HexagonRowColumn332.cols_innerABC) ((0 : Fin 2), (1 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem left1Middle3_eq_case_3_2_row_0_2_0 : (left1Middle3 3 2) ((0 : Fin 2), (2 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn332.rows_assocABC HexagonRowColumn332.cols_innerABC) ((0 : Fin 2), (2 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem left1Middle3_eq_case_3_2_row_0_3_0 : (left1Middle3 3 2) ((0 : Fin 2), (3 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn332.rows_assocABC HexagonRowColumn332.cols_innerABC) ((0 : Fin 2), (3 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem left1Middle3_eq_case_3_2_row_0_4_0 : (left1Middle3 3 2) ((0 : Fin 2), (4 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn332.rows_assocABC HexagonRowColumn332.cols_innerABC) ((0 : Fin 2), (4 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem left1Middle3_eq_case_3_2_row_0_5_0 : (left1Middle3 3 2) ((0 : Fin 2), (5 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn332.rows_assocABC HexagonRowColumn332.cols_innerABC) ((0 : Fin 2), (5 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem left1Middle3_eq_case_3_2_row_0_6_0 : (left1Middle3 3 2) ((0 : Fin 2), (6 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn332.rows_assocABC HexagonRowColumn332.cols_innerABC) ((0 : Fin 2), (6 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem left1Middle3_eq_case_3_2_row_0_7_0 : (left1Middle3 3 2) ((0 : Fin 2), (7 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn332.rows_assocABC HexagonRowColumn332.cols_innerABC) ((0 : Fin 2), (7 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem left1Middle3_eq_case_3_2_row_1_0_0 : (left1Middle3 3 2) ((1 : Fin 2), (0 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn332.rows_assocABC HexagonRowColumn332.cols_innerABC) ((1 : Fin 2), (0 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem left1Middle3_eq_case_3_2_row_1_1_0 : (left1Middle3 3 2) ((1 : Fin 2), (1 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn332.rows_assocABC HexagonRowColumn332.cols_innerABC) ((1 : Fin 2), (1 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem left1Middle3_eq_case_3_2_row_1_2_0 : (left1Middle3 3 2) ((1 : Fin 2), (2 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn332.rows_assocABC HexagonRowColumn332.cols_innerABC) ((1 : Fin 2), (2 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem left1Middle3_eq_case_3_2_row_1_3_0 : (left1Middle3 3 2) ((1 : Fin 2), (3 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn332.rows_assocABC HexagonRowColumn332.cols_innerABC) ((1 : Fin 2), (3 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem left1Middle3_eq_case_3_2_row_1_4_0 : (left1Middle3 3 2) ((1 : Fin 2), (4 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn332.rows_assocABC HexagonRowColumn332.cols_innerABC) ((1 : Fin 2), (4 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem left1Middle3_eq_case_3_2_row_1_5_0 : (left1Middle3 3 2) ((1 : Fin 2), (5 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn332.rows_assocABC HexagonRowColumn332.cols_innerABC) ((1 : Fin 2), (5 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem left1Middle3_eq_case_3_2_row_1_6_0 : (left1Middle3 3 2) ((1 : Fin 2), (6 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn332.rows_assocABC HexagonRowColumn332.cols_innerABC) ((1 : Fin 2), (6 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem left1Middle3_eq_case_3_2_row_1_7_0 : (left1Middle3 3 2) ((1 : Fin 2), (7 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn332.rows_assocABC HexagonRowColumn332.cols_innerABC) ((1 : Fin 2), (7 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem left1Middle3_eq_case_3_2_checked : left1Middle3 3 2 = rowColumnMul HexagonRowColumn332.rows_assocABC HexagonRowColumn332.cols_innerABC := by
  funext r
  fin_cases r
  · exact left1Middle3_eq_case_3_2_row_0_0_0
  · exact left1Middle3_eq_case_3_2_row_0_1_0
  · exact left1Middle3_eq_case_3_2_row_0_2_0
  · exact left1Middle3_eq_case_3_2_row_0_3_0
  · exact left1Middle3_eq_case_3_2_row_0_4_0
  · exact left1Middle3_eq_case_3_2_row_0_5_0
  · exact left1Middle3_eq_case_3_2_row_0_6_0
  · exact left1Middle3_eq_case_3_2_row_0_7_0
  · exact left1Middle3_eq_case_3_2_row_1_0_0
  · exact left1Middle3_eq_case_3_2_row_1_1_0
  · exact left1Middle3_eq_case_3_2_row_1_2_0
  · exact left1Middle3_eq_case_3_2_row_1_3_0
  · exact left1Middle3_eq_case_3_2_row_1_4_0
  · exact left1Middle3_eq_case_3_2_row_1_5_0
  · exact left1Middle3_eq_case_3_2_row_1_6_0
  · exact left1Middle3_eq_case_3_2_row_1_7_0

set_option backward.isDefEq.respectTransparency false in
theorem left1Middle3_eq_case_3_2 : left1Middle3 3 2 = associatorZ 3 3 2 * innerLeftZ 3 3 2 := by
  simpa only [HexagonAtoms332.assocABC_eq,
    HexagonAtoms332.outerABC_eq,
    HexagonAtoms332.assocBAC_eq,
    HexagonAtoms332.innerABC_eq,
    HexagonAtoms332.innerRightABC_eq,
    HexagonAtoms332.inverseACB_eq,
    HexagonAtoms332.innerACB_eq,
    HexagonAtoms332.assocBCA_eq,
    HexagonAtoms332.innerRightBAC_eq,
    HexagonAtoms332.assocCAB_eq,
    HexagonAtoms332.outerLeftABC_eq,
    HexagonRowColumn332.assocBAC_alias,
    HexagonRowColumn332.innerRightBAC_alias,
    HexagonRowColumn332.product0_eq,
    HexagonRowColumn332.product1_eq,
    HexagonRowColumn332.product2_eq,
    HexagonRowColumn332.product3_eq,
    HexagonRowColumn332.product4_eq,
    HexagonRowColumn332.product5_eq,
    HexagonRowColumn332.product6_eq,
    HexagonRowColumn332.product7_eq] using left1Middle3_eq_case_3_2_checked

private theorem right0Middle3_eq_case_3_2_row_0_0_0 : (right0Middle3 3 2) ((0 : Fin 2), (0 : Fin 8), (0 : Fin 1)) = (HexagonAtoms332.assocABC) ((0 : Fin 2), (0 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem right0Middle3_eq_case_3_2_row_0_1_0 : (right0Middle3 3 2) ((0 : Fin 2), (1 : Fin 8), (0 : Fin 1)) = (HexagonAtoms332.assocABC) ((0 : Fin 2), (1 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem right0Middle3_eq_case_3_2_row_0_2_0 : (right0Middle3 3 2) ((0 : Fin 2), (2 : Fin 8), (0 : Fin 1)) = (HexagonAtoms332.assocABC) ((0 : Fin 2), (2 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem right0Middle3_eq_case_3_2_row_0_3_0 : (right0Middle3 3 2) ((0 : Fin 2), (3 : Fin 8), (0 : Fin 1)) = (HexagonAtoms332.assocABC) ((0 : Fin 2), (3 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem right0Middle3_eq_case_3_2_row_0_4_0 : (right0Middle3 3 2) ((0 : Fin 2), (4 : Fin 8), (0 : Fin 1)) = (HexagonAtoms332.assocABC) ((0 : Fin 2), (4 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem right0Middle3_eq_case_3_2_row_0_5_0 : (right0Middle3 3 2) ((0 : Fin 2), (5 : Fin 8), (0 : Fin 1)) = (HexagonAtoms332.assocABC) ((0 : Fin 2), (5 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem right0Middle3_eq_case_3_2_row_0_6_0 : (right0Middle3 3 2) ((0 : Fin 2), (6 : Fin 8), (0 : Fin 1)) = (HexagonAtoms332.assocABC) ((0 : Fin 2), (6 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem right0Middle3_eq_case_3_2_row_0_7_0 : (right0Middle3 3 2) ((0 : Fin 2), (7 : Fin 8), (0 : Fin 1)) = (HexagonAtoms332.assocABC) ((0 : Fin 2), (7 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem right0Middle3_eq_case_3_2_row_1_0_0 : (right0Middle3 3 2) ((1 : Fin 2), (0 : Fin 8), (0 : Fin 1)) = (HexagonAtoms332.assocABC) ((1 : Fin 2), (0 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem right0Middle3_eq_case_3_2_row_1_1_0 : (right0Middle3 3 2) ((1 : Fin 2), (1 : Fin 8), (0 : Fin 1)) = (HexagonAtoms332.assocABC) ((1 : Fin 2), (1 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem right0Middle3_eq_case_3_2_row_1_2_0 : (right0Middle3 3 2) ((1 : Fin 2), (2 : Fin 8), (0 : Fin 1)) = (HexagonAtoms332.assocABC) ((1 : Fin 2), (2 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem right0Middle3_eq_case_3_2_row_1_3_0 : (right0Middle3 3 2) ((1 : Fin 2), (3 : Fin 8), (0 : Fin 1)) = (HexagonAtoms332.assocABC) ((1 : Fin 2), (3 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem right0Middle3_eq_case_3_2_row_1_4_0 : (right0Middle3 3 2) ((1 : Fin 2), (4 : Fin 8), (0 : Fin 1)) = (HexagonAtoms332.assocABC) ((1 : Fin 2), (4 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem right0Middle3_eq_case_3_2_row_1_5_0 : (right0Middle3 3 2) ((1 : Fin 2), (5 : Fin 8), (0 : Fin 1)) = (HexagonAtoms332.assocABC) ((1 : Fin 2), (5 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem right0Middle3_eq_case_3_2_row_1_6_0 : (right0Middle3 3 2) ((1 : Fin 2), (6 : Fin 8), (0 : Fin 1)) = (HexagonAtoms332.assocABC) ((1 : Fin 2), (6 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem right0Middle3_eq_case_3_2_row_1_7_0 : (right0Middle3 3 2) ((1 : Fin 2), (7 : Fin 8), (0 : Fin 1)) = (HexagonAtoms332.assocABC) ((1 : Fin 2), (7 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem right0Middle3_eq_case_3_2_checked : right0Middle3 3 2 = HexagonAtoms332.assocABC := by
  funext r
  fin_cases r
  · exact right0Middle3_eq_case_3_2_row_0_0_0
  · exact right0Middle3_eq_case_3_2_row_0_1_0
  · exact right0Middle3_eq_case_3_2_row_0_2_0
  · exact right0Middle3_eq_case_3_2_row_0_3_0
  · exact right0Middle3_eq_case_3_2_row_0_4_0
  · exact right0Middle3_eq_case_3_2_row_0_5_0
  · exact right0Middle3_eq_case_3_2_row_0_6_0
  · exact right0Middle3_eq_case_3_2_row_0_7_0
  · exact right0Middle3_eq_case_3_2_row_1_0_0
  · exact right0Middle3_eq_case_3_2_row_1_1_0
  · exact right0Middle3_eq_case_3_2_row_1_2_0
  · exact right0Middle3_eq_case_3_2_row_1_3_0
  · exact right0Middle3_eq_case_3_2_row_1_4_0
  · exact right0Middle3_eq_case_3_2_row_1_5_0
  · exact right0Middle3_eq_case_3_2_row_1_6_0
  · exact right0Middle3_eq_case_3_2_row_1_7_0

set_option backward.isDefEq.respectTransparency false in
theorem right0Middle3_eq_case_3_2 : right0Middle3 3 2 = innerRightZ 3 3 2 * associatorZ 3 3 2 := by
  simpa only [HexagonAtoms332.assocABC_eq,
    HexagonAtoms332.outerABC_eq,
    HexagonAtoms332.assocBAC_eq,
    HexagonAtoms332.innerABC_eq,
    HexagonAtoms332.innerRightABC_eq,
    HexagonAtoms332.inverseACB_eq,
    HexagonAtoms332.innerACB_eq,
    HexagonAtoms332.assocBCA_eq,
    HexagonAtoms332.innerRightBAC_eq,
    HexagonAtoms332.assocCAB_eq,
    HexagonAtoms332.outerLeftABC_eq,
    HexagonRowColumn332.assocBAC_alias,
    HexagonRowColumn332.innerRightBAC_alias,
    HexagonRowColumn332.product0_eq,
    HexagonRowColumn332.product1_eq,
    HexagonRowColumn332.product2_eq,
    HexagonRowColumn332.product3_eq,
    HexagonRowColumn332.product4_eq,
    HexagonRowColumn332.product5_eq,
    HexagonRowColumn332.product6_eq,
    HexagonRowColumn332.product7_eq] using right0Middle3_eq_case_3_2_checked

private theorem right1Middle3_eq_case_3_2_row_0_0_0 : (right1Middle3 3 2) ((0 : Fin 2), (0 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn332.rows_inverseACB HexagonRowColumn332.cols_right0) ((0 : Fin 2), (0 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem right1Middle3_eq_case_3_2_row_0_1_0 : (right1Middle3 3 2) ((0 : Fin 2), (1 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn332.rows_inverseACB HexagonRowColumn332.cols_right0) ((0 : Fin 2), (1 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem right1Middle3_eq_case_3_2_row_0_2_0 : (right1Middle3 3 2) ((0 : Fin 2), (2 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn332.rows_inverseACB HexagonRowColumn332.cols_right0) ((0 : Fin 2), (2 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem right1Middle3_eq_case_3_2_row_0_3_0 : (right1Middle3 3 2) ((0 : Fin 2), (3 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn332.rows_inverseACB HexagonRowColumn332.cols_right0) ((0 : Fin 2), (3 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem right1Middle3_eq_case_3_2_row_0_4_0 : (right1Middle3 3 2) ((0 : Fin 2), (4 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn332.rows_inverseACB HexagonRowColumn332.cols_right0) ((0 : Fin 2), (4 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem right1Middle3_eq_case_3_2_row_0_5_0 : (right1Middle3 3 2) ((0 : Fin 2), (5 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn332.rows_inverseACB HexagonRowColumn332.cols_right0) ((0 : Fin 2), (5 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem right1Middle3_eq_case_3_2_row_0_6_0 : (right1Middle3 3 2) ((0 : Fin 2), (6 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn332.rows_inverseACB HexagonRowColumn332.cols_right0) ((0 : Fin 2), (6 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem right1Middle3_eq_case_3_2_row_0_7_0 : (right1Middle3 3 2) ((0 : Fin 2), (7 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn332.rows_inverseACB HexagonRowColumn332.cols_right0) ((0 : Fin 2), (7 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem right1Middle3_eq_case_3_2_row_1_0_0 : (right1Middle3 3 2) ((1 : Fin 2), (0 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn332.rows_inverseACB HexagonRowColumn332.cols_right0) ((1 : Fin 2), (0 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem right1Middle3_eq_case_3_2_row_1_1_0 : (right1Middle3 3 2) ((1 : Fin 2), (1 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn332.rows_inverseACB HexagonRowColumn332.cols_right0) ((1 : Fin 2), (1 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem right1Middle3_eq_case_3_2_row_1_2_0 : (right1Middle3 3 2) ((1 : Fin 2), (2 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn332.rows_inverseACB HexagonRowColumn332.cols_right0) ((1 : Fin 2), (2 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem right1Middle3_eq_case_3_2_row_1_3_0 : (right1Middle3 3 2) ((1 : Fin 2), (3 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn332.rows_inverseACB HexagonRowColumn332.cols_right0) ((1 : Fin 2), (3 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem right1Middle3_eq_case_3_2_row_1_4_0 : (right1Middle3 3 2) ((1 : Fin 2), (4 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn332.rows_inverseACB HexagonRowColumn332.cols_right0) ((1 : Fin 2), (4 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem right1Middle3_eq_case_3_2_row_1_5_0 : (right1Middle3 3 2) ((1 : Fin 2), (5 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn332.rows_inverseACB HexagonRowColumn332.cols_right0) ((1 : Fin 2), (5 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem right1Middle3_eq_case_3_2_row_1_6_0 : (right1Middle3 3 2) ((1 : Fin 2), (6 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn332.rows_inverseACB HexagonRowColumn332.cols_right0) ((1 : Fin 2), (6 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem right1Middle3_eq_case_3_2_row_1_7_0 : (right1Middle3 3 2) ((1 : Fin 2), (7 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn332.rows_inverseACB HexagonRowColumn332.cols_right0) ((1 : Fin 2), (7 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem right1Middle3_eq_case_3_2_checked : right1Middle3 3 2 = rowColumnMul HexagonRowColumn332.rows_inverseACB HexagonRowColumn332.cols_right0 := by
  funext r
  fin_cases r
  · exact right1Middle3_eq_case_3_2_row_0_0_0
  · exact right1Middle3_eq_case_3_2_row_0_1_0
  · exact right1Middle3_eq_case_3_2_row_0_2_0
  · exact right1Middle3_eq_case_3_2_row_0_3_0
  · exact right1Middle3_eq_case_3_2_row_0_4_0
  · exact right1Middle3_eq_case_3_2_row_0_5_0
  · exact right1Middle3_eq_case_3_2_row_0_6_0
  · exact right1Middle3_eq_case_3_2_row_0_7_0
  · exact right1Middle3_eq_case_3_2_row_1_0_0
  · exact right1Middle3_eq_case_3_2_row_1_1_0
  · exact right1Middle3_eq_case_3_2_row_1_2_0
  · exact right1Middle3_eq_case_3_2_row_1_3_0
  · exact right1Middle3_eq_case_3_2_row_1_4_0
  · exact right1Middle3_eq_case_3_2_row_1_5_0
  · exact right1Middle3_eq_case_3_2_row_1_6_0
  · exact right1Middle3_eq_case_3_2_row_1_7_0

set_option backward.isDefEq.respectTransparency false in
theorem right1Middle3_eq_case_3_2 : right1Middle3 3 2 = associatorInverseZ 3 2 3 * right0Middle3 3 2 := by
  simpa only [HexagonAtoms332.assocABC_eq,
    HexagonAtoms332.outerABC_eq,
    HexagonAtoms332.assocBAC_eq,
    HexagonAtoms332.innerABC_eq,
    HexagonAtoms332.innerRightABC_eq,
    HexagonAtoms332.inverseACB_eq,
    HexagonAtoms332.innerACB_eq,
    HexagonAtoms332.assocBCA_eq,
    HexagonAtoms332.innerRightBAC_eq,
    HexagonAtoms332.assocCAB_eq,
    HexagonAtoms332.outerLeftABC_eq,
    HexagonRowColumn332.assocBAC_alias,
    HexagonRowColumn332.innerRightBAC_alias,
    HexagonRowColumn332.product0_eq,
    HexagonRowColumn332.product1_eq,
    HexagonRowColumn332.product2_eq,
    HexagonRowColumn332.product3_eq,
    HexagonRowColumn332.product4_eq,
    HexagonRowColumn332.product5_eq,
    HexagonRowColumn332.product6_eq,
    HexagonRowColumn332.product7_eq] using right1Middle3_eq_case_3_2_checked

private theorem right2Middle3_eq_case_3_2_row_0_0_0 : (right2Middle3 3 2) ((0 : Fin 2), (0 : Fin 8), (0 : Fin 1)) = (right1Middle3 3 2) ((0 : Fin 2), (0 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem right2Middle3_eq_case_3_2_row_0_1_0 : (right2Middle3 3 2) ((0 : Fin 2), (1 : Fin 8), (0 : Fin 1)) = (right1Middle3 3 2) ((0 : Fin 2), (1 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem right2Middle3_eq_case_3_2_row_0_2_0 : (right2Middle3 3 2) ((0 : Fin 2), (2 : Fin 8), (0 : Fin 1)) = (right1Middle3 3 2) ((0 : Fin 2), (2 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem right2Middle3_eq_case_3_2_row_0_3_0 : (right2Middle3 3 2) ((0 : Fin 2), (3 : Fin 8), (0 : Fin 1)) = (right1Middle3 3 2) ((0 : Fin 2), (3 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem right2Middle3_eq_case_3_2_row_0_4_0 : (right2Middle3 3 2) ((0 : Fin 2), (4 : Fin 8), (0 : Fin 1)) = (right1Middle3 3 2) ((0 : Fin 2), (4 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem right2Middle3_eq_case_3_2_row_0_5_0 : (right2Middle3 3 2) ((0 : Fin 2), (5 : Fin 8), (0 : Fin 1)) = (right1Middle3 3 2) ((0 : Fin 2), (5 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem right2Middle3_eq_case_3_2_row_0_6_0 : (right2Middle3 3 2) ((0 : Fin 2), (6 : Fin 8), (0 : Fin 1)) = (right1Middle3 3 2) ((0 : Fin 2), (6 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem right2Middle3_eq_case_3_2_row_0_7_0 : (right2Middle3 3 2) ((0 : Fin 2), (7 : Fin 8), (0 : Fin 1)) = (right1Middle3 3 2) ((0 : Fin 2), (7 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem right2Middle3_eq_case_3_2_row_1_0_0 : (right2Middle3 3 2) ((1 : Fin 2), (0 : Fin 8), (0 : Fin 1)) = (right1Middle3 3 2) ((1 : Fin 2), (0 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem right2Middle3_eq_case_3_2_row_1_1_0 : (right2Middle3 3 2) ((1 : Fin 2), (1 : Fin 8), (0 : Fin 1)) = (right1Middle3 3 2) ((1 : Fin 2), (1 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem right2Middle3_eq_case_3_2_row_1_2_0 : (right2Middle3 3 2) ((1 : Fin 2), (2 : Fin 8), (0 : Fin 1)) = (right1Middle3 3 2) ((1 : Fin 2), (2 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem right2Middle3_eq_case_3_2_row_1_3_0 : (right2Middle3 3 2) ((1 : Fin 2), (3 : Fin 8), (0 : Fin 1)) = (right1Middle3 3 2) ((1 : Fin 2), (3 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem right2Middle3_eq_case_3_2_row_1_4_0 : (right2Middle3 3 2) ((1 : Fin 2), (4 : Fin 8), (0 : Fin 1)) = (right1Middle3 3 2) ((1 : Fin 2), (4 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem right2Middle3_eq_case_3_2_row_1_5_0 : (right2Middle3 3 2) ((1 : Fin 2), (5 : Fin 8), (0 : Fin 1)) = (right1Middle3 3 2) ((1 : Fin 2), (5 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem right2Middle3_eq_case_3_2_row_1_6_0 : (right2Middle3 3 2) ((1 : Fin 2), (6 : Fin 8), (0 : Fin 1)) = (right1Middle3 3 2) ((1 : Fin 2), (6 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem right2Middle3_eq_case_3_2_row_1_7_0 : (right2Middle3 3 2) ((1 : Fin 2), (7 : Fin 8), (0 : Fin 1)) = (right1Middle3 3 2) ((1 : Fin 2), (7 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem right2Middle3_eq_case_3_2_checked : right2Middle3 3 2 = right1Middle3 3 2 := by
  funext r
  fin_cases r
  · exact right2Middle3_eq_case_3_2_row_0_0_0
  · exact right2Middle3_eq_case_3_2_row_0_1_0
  · exact right2Middle3_eq_case_3_2_row_0_2_0
  · exact right2Middle3_eq_case_3_2_row_0_3_0
  · exact right2Middle3_eq_case_3_2_row_0_4_0
  · exact right2Middle3_eq_case_3_2_row_0_5_0
  · exact right2Middle3_eq_case_3_2_row_0_6_0
  · exact right2Middle3_eq_case_3_2_row_0_7_0
  · exact right2Middle3_eq_case_3_2_row_1_0_0
  · exact right2Middle3_eq_case_3_2_row_1_1_0
  · exact right2Middle3_eq_case_3_2_row_1_2_0
  · exact right2Middle3_eq_case_3_2_row_1_3_0
  · exact right2Middle3_eq_case_3_2_row_1_4_0
  · exact right2Middle3_eq_case_3_2_row_1_5_0
  · exact right2Middle3_eq_case_3_2_row_1_6_0
  · exact right2Middle3_eq_case_3_2_row_1_7_0

set_option backward.isDefEq.respectTransparency false in
theorem right2Middle3_eq_case_3_2 : right2Middle3 3 2 = innerLeftZ 3 2 3 * right1Middle3 3 2 := by
  simpa only [HexagonAtoms332.assocABC_eq,
    HexagonAtoms332.outerABC_eq,
    HexagonAtoms332.assocBAC_eq,
    HexagonAtoms332.innerABC_eq,
    HexagonAtoms332.innerRightABC_eq,
    HexagonAtoms332.inverseACB_eq,
    HexagonAtoms332.innerACB_eq,
    HexagonAtoms332.assocBCA_eq,
    HexagonAtoms332.innerRightBAC_eq,
    HexagonAtoms332.assocCAB_eq,
    HexagonAtoms332.outerLeftABC_eq,
    HexagonRowColumn332.assocBAC_alias,
    HexagonRowColumn332.innerRightBAC_alias,
    HexagonRowColumn332.product0_eq,
    HexagonRowColumn332.product1_eq,
    HexagonRowColumn332.product2_eq,
    HexagonRowColumn332.product3_eq,
    HexagonRowColumn332.product4_eq,
    HexagonRowColumn332.product5_eq,
    HexagonRowColumn332.product6_eq,
    HexagonRowColumn332.product7_eq] using right2Middle3_eq_case_3_2_checked

private theorem leftFinal3_case_3_2_row_0_0_0 : (((-1 : ℤ) ^ (leftScaleBit 3 3 2).val * positiveScale (leftScaleExponent 3 3 2)) •
      (rowColumnMul HexagonRowColumn332.rows_assocBCA HexagonRowColumn332.cols_left0)) ((0 : Fin 2), (0 : Fin 8), (0 : Fin 1)) = (negativeScale (leftScaleExponent 3 3 2) • (left1Middle3 3 2)) ((0 : Fin 2), (0 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem leftFinal3_case_3_2_row_0_1_0 : (((-1 : ℤ) ^ (leftScaleBit 3 3 2).val * positiveScale (leftScaleExponent 3 3 2)) •
      (rowColumnMul HexagonRowColumn332.rows_assocBCA HexagonRowColumn332.cols_left0)) ((0 : Fin 2), (1 : Fin 8), (0 : Fin 1)) = (negativeScale (leftScaleExponent 3 3 2) • (left1Middle3 3 2)) ((0 : Fin 2), (1 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem leftFinal3_case_3_2_row_0_2_0 : (((-1 : ℤ) ^ (leftScaleBit 3 3 2).val * positiveScale (leftScaleExponent 3 3 2)) •
      (rowColumnMul HexagonRowColumn332.rows_assocBCA HexagonRowColumn332.cols_left0)) ((0 : Fin 2), (2 : Fin 8), (0 : Fin 1)) = (negativeScale (leftScaleExponent 3 3 2) • (left1Middle3 3 2)) ((0 : Fin 2), (2 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem leftFinal3_case_3_2_row_0_3_0 : (((-1 : ℤ) ^ (leftScaleBit 3 3 2).val * positiveScale (leftScaleExponent 3 3 2)) •
      (rowColumnMul HexagonRowColumn332.rows_assocBCA HexagonRowColumn332.cols_left0)) ((0 : Fin 2), (3 : Fin 8), (0 : Fin 1)) = (negativeScale (leftScaleExponent 3 3 2) • (left1Middle3 3 2)) ((0 : Fin 2), (3 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem leftFinal3_case_3_2_row_0_4_0 : (((-1 : ℤ) ^ (leftScaleBit 3 3 2).val * positiveScale (leftScaleExponent 3 3 2)) •
      (rowColumnMul HexagonRowColumn332.rows_assocBCA HexagonRowColumn332.cols_left0)) ((0 : Fin 2), (4 : Fin 8), (0 : Fin 1)) = (negativeScale (leftScaleExponent 3 3 2) • (left1Middle3 3 2)) ((0 : Fin 2), (4 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem leftFinal3_case_3_2_row_0_5_0 : (((-1 : ℤ) ^ (leftScaleBit 3 3 2).val * positiveScale (leftScaleExponent 3 3 2)) •
      (rowColumnMul HexagonRowColumn332.rows_assocBCA HexagonRowColumn332.cols_left0)) ((0 : Fin 2), (5 : Fin 8), (0 : Fin 1)) = (negativeScale (leftScaleExponent 3 3 2) • (left1Middle3 3 2)) ((0 : Fin 2), (5 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem leftFinal3_case_3_2_row_0_6_0 : (((-1 : ℤ) ^ (leftScaleBit 3 3 2).val * positiveScale (leftScaleExponent 3 3 2)) •
      (rowColumnMul HexagonRowColumn332.rows_assocBCA HexagonRowColumn332.cols_left0)) ((0 : Fin 2), (6 : Fin 8), (0 : Fin 1)) = (negativeScale (leftScaleExponent 3 3 2) • (left1Middle3 3 2)) ((0 : Fin 2), (6 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem leftFinal3_case_3_2_row_0_7_0 : (((-1 : ℤ) ^ (leftScaleBit 3 3 2).val * positiveScale (leftScaleExponent 3 3 2)) •
      (rowColumnMul HexagonRowColumn332.rows_assocBCA HexagonRowColumn332.cols_left0)) ((0 : Fin 2), (7 : Fin 8), (0 : Fin 1)) = (negativeScale (leftScaleExponent 3 3 2) • (left1Middle3 3 2)) ((0 : Fin 2), (7 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem leftFinal3_case_3_2_row_1_0_0 : (((-1 : ℤ) ^ (leftScaleBit 3 3 2).val * positiveScale (leftScaleExponent 3 3 2)) •
      (rowColumnMul HexagonRowColumn332.rows_assocBCA HexagonRowColumn332.cols_left0)) ((1 : Fin 2), (0 : Fin 8), (0 : Fin 1)) = (negativeScale (leftScaleExponent 3 3 2) • (left1Middle3 3 2)) ((1 : Fin 2), (0 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem leftFinal3_case_3_2_row_1_1_0 : (((-1 : ℤ) ^ (leftScaleBit 3 3 2).val * positiveScale (leftScaleExponent 3 3 2)) •
      (rowColumnMul HexagonRowColumn332.rows_assocBCA HexagonRowColumn332.cols_left0)) ((1 : Fin 2), (1 : Fin 8), (0 : Fin 1)) = (negativeScale (leftScaleExponent 3 3 2) • (left1Middle3 3 2)) ((1 : Fin 2), (1 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem leftFinal3_case_3_2_row_1_2_0 : (((-1 : ℤ) ^ (leftScaleBit 3 3 2).val * positiveScale (leftScaleExponent 3 3 2)) •
      (rowColumnMul HexagonRowColumn332.rows_assocBCA HexagonRowColumn332.cols_left0)) ((1 : Fin 2), (2 : Fin 8), (0 : Fin 1)) = (negativeScale (leftScaleExponent 3 3 2) • (left1Middle3 3 2)) ((1 : Fin 2), (2 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem leftFinal3_case_3_2_row_1_3_0 : (((-1 : ℤ) ^ (leftScaleBit 3 3 2).val * positiveScale (leftScaleExponent 3 3 2)) •
      (rowColumnMul HexagonRowColumn332.rows_assocBCA HexagonRowColumn332.cols_left0)) ((1 : Fin 2), (3 : Fin 8), (0 : Fin 1)) = (negativeScale (leftScaleExponent 3 3 2) • (left1Middle3 3 2)) ((1 : Fin 2), (3 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem leftFinal3_case_3_2_row_1_4_0 : (((-1 : ℤ) ^ (leftScaleBit 3 3 2).val * positiveScale (leftScaleExponent 3 3 2)) •
      (rowColumnMul HexagonRowColumn332.rows_assocBCA HexagonRowColumn332.cols_left0)) ((1 : Fin 2), (4 : Fin 8), (0 : Fin 1)) = (negativeScale (leftScaleExponent 3 3 2) • (left1Middle3 3 2)) ((1 : Fin 2), (4 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem leftFinal3_case_3_2_row_1_5_0 : (((-1 : ℤ) ^ (leftScaleBit 3 3 2).val * positiveScale (leftScaleExponent 3 3 2)) •
      (rowColumnMul HexagonRowColumn332.rows_assocBCA HexagonRowColumn332.cols_left0)) ((1 : Fin 2), (5 : Fin 8), (0 : Fin 1)) = (negativeScale (leftScaleExponent 3 3 2) • (left1Middle3 3 2)) ((1 : Fin 2), (5 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem leftFinal3_case_3_2_row_1_6_0 : (((-1 : ℤ) ^ (leftScaleBit 3 3 2).val * positiveScale (leftScaleExponent 3 3 2)) •
      (rowColumnMul HexagonRowColumn332.rows_assocBCA HexagonRowColumn332.cols_left0)) ((1 : Fin 2), (6 : Fin 8), (0 : Fin 1)) = (negativeScale (leftScaleExponent 3 3 2) • (left1Middle3 3 2)) ((1 : Fin 2), (6 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem leftFinal3_case_3_2_row_1_7_0 : (((-1 : ℤ) ^ (leftScaleBit 3 3 2).val * positiveScale (leftScaleExponent 3 3 2)) •
      (rowColumnMul HexagonRowColumn332.rows_assocBCA HexagonRowColumn332.cols_left0)) ((1 : Fin 2), (7 : Fin 8), (0 : Fin 1)) = (negativeScale (leftScaleExponent 3 3 2) • (left1Middle3 3 2)) ((1 : Fin 2), (7 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem leftFinal3_case_3_2_checked : ((-1 : ℤ) ^ (leftScaleBit 3 3 2).val * positiveScale (leftScaleExponent 3 3 2)) •
      (rowColumnMul HexagonRowColumn332.rows_assocBCA HexagonRowColumn332.cols_left0) = negativeScale (leftScaleExponent 3 3 2) • (left1Middle3 3 2) := by
  funext r
  fin_cases r
  · exact leftFinal3_case_3_2_row_0_0_0
  · exact leftFinal3_case_3_2_row_0_1_0
  · exact leftFinal3_case_3_2_row_0_2_0
  · exact leftFinal3_case_3_2_row_0_3_0
  · exact leftFinal3_case_3_2_row_0_4_0
  · exact leftFinal3_case_3_2_row_0_5_0
  · exact leftFinal3_case_3_2_row_0_6_0
  · exact leftFinal3_case_3_2_row_0_7_0
  · exact leftFinal3_case_3_2_row_1_0_0
  · exact leftFinal3_case_3_2_row_1_1_0
  · exact leftFinal3_case_3_2_row_1_2_0
  · exact leftFinal3_case_3_2_row_1_3_0
  · exact leftFinal3_case_3_2_row_1_4_0
  · exact leftFinal3_case_3_2_row_1_5_0
  · exact leftFinal3_case_3_2_row_1_6_0
  · exact leftFinal3_case_3_2_row_1_7_0

set_option backward.isDefEq.respectTransparency false in
theorem leftFinal3_case_3_2 : ((-1 : ℤ) ^ (leftScaleBit 3 3 2).val * positiveScale (leftScaleExponent 3 3 2)) •
      (associatorZ 3 2 3 * left0Middle3 3 2) = negativeScale (leftScaleExponent 3 3 2) • (innerRightZ 3 3 2 * left1Middle3 3 2) := by
  simpa only [HexagonAtoms332.assocABC_eq,
    HexagonAtoms332.outerABC_eq,
    HexagonAtoms332.assocBAC_eq,
    HexagonAtoms332.innerABC_eq,
    HexagonAtoms332.innerRightABC_eq,
    HexagonAtoms332.inverseACB_eq,
    HexagonAtoms332.innerACB_eq,
    HexagonAtoms332.assocBCA_eq,
    HexagonAtoms332.innerRightBAC_eq,
    HexagonAtoms332.assocCAB_eq,
    HexagonAtoms332.outerLeftABC_eq,
    HexagonRowColumn332.assocBAC_alias,
    HexagonRowColumn332.innerRightBAC_alias,
    HexagonRowColumn332.product0_eq,
    HexagonRowColumn332.product1_eq,
    HexagonRowColumn332.product2_eq,
    HexagonRowColumn332.product3_eq,
    HexagonRowColumn332.product4_eq,
    HexagonRowColumn332.product5_eq,
    HexagonRowColumn332.product6_eq,
    HexagonRowColumn332.product7_eq] using leftFinal3_case_3_2_checked

private theorem rightFinal3_case_3_2_row_0_0_0 : (((-1 : ℤ) ^ (rightScaleBit 3 3 2).val * positiveScale (rightScaleExponent 3 3 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 3 : ℤ)) • HexagonAtoms332.outerLeftABC) ((0 : Fin 4), (0 : Fin 4), (0 : Fin 1)) = (negativeScale (rightScaleExponent 3 3 2) • (rowColumnMul HexagonRowColumn332.rows_assocCAB HexagonRowColumn332.cols_right2)) ((0 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem rightFinal3_case_3_2_row_0_1_0 : (((-1 : ℤ) ^ (rightScaleBit 3 3 2).val * positiveScale (rightScaleExponent 3 3 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 3 : ℤ)) • HexagonAtoms332.outerLeftABC) ((0 : Fin 4), (1 : Fin 4), (0 : Fin 1)) = (negativeScale (rightScaleExponent 3 3 2) • (rowColumnMul HexagonRowColumn332.rows_assocCAB HexagonRowColumn332.cols_right2)) ((0 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem rightFinal3_case_3_2_row_0_2_0 : (((-1 : ℤ) ^ (rightScaleBit 3 3 2).val * positiveScale (rightScaleExponent 3 3 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 3 : ℤ)) • HexagonAtoms332.outerLeftABC) ((0 : Fin 4), (2 : Fin 4), (0 : Fin 1)) = (negativeScale (rightScaleExponent 3 3 2) • (rowColumnMul HexagonRowColumn332.rows_assocCAB HexagonRowColumn332.cols_right2)) ((0 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem rightFinal3_case_3_2_row_0_3_0 : (((-1 : ℤ) ^ (rightScaleBit 3 3 2).val * positiveScale (rightScaleExponent 3 3 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 3 : ℤ)) • HexagonAtoms332.outerLeftABC) ((0 : Fin 4), (3 : Fin 4), (0 : Fin 1)) = (negativeScale (rightScaleExponent 3 3 2) • (rowColumnMul HexagonRowColumn332.rows_assocCAB HexagonRowColumn332.cols_right2)) ((0 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem rightFinal3_case_3_2_row_1_0_0 : (((-1 : ℤ) ^ (rightScaleBit 3 3 2).val * positiveScale (rightScaleExponent 3 3 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 3 : ℤ)) • HexagonAtoms332.outerLeftABC) ((1 : Fin 4), (0 : Fin 4), (0 : Fin 1)) = (negativeScale (rightScaleExponent 3 3 2) • (rowColumnMul HexagonRowColumn332.rows_assocCAB HexagonRowColumn332.cols_right2)) ((1 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem rightFinal3_case_3_2_row_1_1_0 : (((-1 : ℤ) ^ (rightScaleBit 3 3 2).val * positiveScale (rightScaleExponent 3 3 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 3 : ℤ)) • HexagonAtoms332.outerLeftABC) ((1 : Fin 4), (1 : Fin 4), (0 : Fin 1)) = (negativeScale (rightScaleExponent 3 3 2) • (rowColumnMul HexagonRowColumn332.rows_assocCAB HexagonRowColumn332.cols_right2)) ((1 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem rightFinal3_case_3_2_row_1_2_0 : (((-1 : ℤ) ^ (rightScaleBit 3 3 2).val * positiveScale (rightScaleExponent 3 3 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 3 : ℤ)) • HexagonAtoms332.outerLeftABC) ((1 : Fin 4), (2 : Fin 4), (0 : Fin 1)) = (negativeScale (rightScaleExponent 3 3 2) • (rowColumnMul HexagonRowColumn332.rows_assocCAB HexagonRowColumn332.cols_right2)) ((1 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem rightFinal3_case_3_2_row_1_3_0 : (((-1 : ℤ) ^ (rightScaleBit 3 3 2).val * positiveScale (rightScaleExponent 3 3 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 3 : ℤ)) • HexagonAtoms332.outerLeftABC) ((1 : Fin 4), (3 : Fin 4), (0 : Fin 1)) = (negativeScale (rightScaleExponent 3 3 2) • (rowColumnMul HexagonRowColumn332.rows_assocCAB HexagonRowColumn332.cols_right2)) ((1 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem rightFinal3_case_3_2_row_2_0_0 : (((-1 : ℤ) ^ (rightScaleBit 3 3 2).val * positiveScale (rightScaleExponent 3 3 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 3 : ℤ)) • HexagonAtoms332.outerLeftABC) ((2 : Fin 4), (0 : Fin 4), (0 : Fin 1)) = (negativeScale (rightScaleExponent 3 3 2) • (rowColumnMul HexagonRowColumn332.rows_assocCAB HexagonRowColumn332.cols_right2)) ((2 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem rightFinal3_case_3_2_row_2_1_0 : (((-1 : ℤ) ^ (rightScaleBit 3 3 2).val * positiveScale (rightScaleExponent 3 3 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 3 : ℤ)) • HexagonAtoms332.outerLeftABC) ((2 : Fin 4), (1 : Fin 4), (0 : Fin 1)) = (negativeScale (rightScaleExponent 3 3 2) • (rowColumnMul HexagonRowColumn332.rows_assocCAB HexagonRowColumn332.cols_right2)) ((2 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem rightFinal3_case_3_2_row_2_2_0 : (((-1 : ℤ) ^ (rightScaleBit 3 3 2).val * positiveScale (rightScaleExponent 3 3 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 3 : ℤ)) • HexagonAtoms332.outerLeftABC) ((2 : Fin 4), (2 : Fin 4), (0 : Fin 1)) = (negativeScale (rightScaleExponent 3 3 2) • (rowColumnMul HexagonRowColumn332.rows_assocCAB HexagonRowColumn332.cols_right2)) ((2 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem rightFinal3_case_3_2_row_2_3_0 : (((-1 : ℤ) ^ (rightScaleBit 3 3 2).val * positiveScale (rightScaleExponent 3 3 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 3 : ℤ)) • HexagonAtoms332.outerLeftABC) ((2 : Fin 4), (3 : Fin 4), (0 : Fin 1)) = (negativeScale (rightScaleExponent 3 3 2) • (rowColumnMul HexagonRowColumn332.rows_assocCAB HexagonRowColumn332.cols_right2)) ((2 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem rightFinal3_case_3_2_row_3_0_0 : (((-1 : ℤ) ^ (rightScaleBit 3 3 2).val * positiveScale (rightScaleExponent 3 3 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 3 : ℤ)) • HexagonAtoms332.outerLeftABC) ((3 : Fin 4), (0 : Fin 4), (0 : Fin 1)) = (negativeScale (rightScaleExponent 3 3 2) • (rowColumnMul HexagonRowColumn332.rows_assocCAB HexagonRowColumn332.cols_right2)) ((3 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem rightFinal3_case_3_2_row_3_1_0 : (((-1 : ℤ) ^ (rightScaleBit 3 3 2).val * positiveScale (rightScaleExponent 3 3 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 3 : ℤ)) • HexagonAtoms332.outerLeftABC) ((3 : Fin 4), (1 : Fin 4), (0 : Fin 1)) = (negativeScale (rightScaleExponent 3 3 2) • (rowColumnMul HexagonRowColumn332.rows_assocCAB HexagonRowColumn332.cols_right2)) ((3 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem rightFinal3_case_3_2_row_3_2_0 : (((-1 : ℤ) ^ (rightScaleBit 3 3 2).val * positiveScale (rightScaleExponent 3 3 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 3 : ℤ)) • HexagonAtoms332.outerLeftABC) ((3 : Fin 4), (2 : Fin 4), (0 : Fin 1)) = (negativeScale (rightScaleExponent 3 3 2) • (rowColumnMul HexagonRowColumn332.rows_assocCAB HexagonRowColumn332.cols_right2)) ((3 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem rightFinal3_case_3_2_row_3_3_0 : (((-1 : ℤ) ^ (rightScaleBit 3 3 2).val * positiveScale (rightScaleExponent 3 3 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 3 : ℤ)) • HexagonAtoms332.outerLeftABC) ((3 : Fin 4), (3 : Fin 4), (0 : Fin 1)) = (negativeScale (rightScaleExponent 3 3 2) • (rowColumnMul HexagonRowColumn332.rows_assocCAB HexagonRowColumn332.cols_right2)) ((3 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem rightFinal3_case_3_2_checked : ((-1 : ℤ) ^ (rightScaleBit 3 3 2).val * positiveScale (rightScaleExponent 3 3 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 3 : ℤ)) • HexagonAtoms332.outerLeftABC = negativeScale (rightScaleExponent 3 3 2) • (rowColumnMul HexagonRowColumn332.rows_assocCAB HexagonRowColumn332.cols_right2) := by
  funext r
  fin_cases r
  · exact rightFinal3_case_3_2_row_0_0_0
  · exact rightFinal3_case_3_2_row_0_1_0
  · exact rightFinal3_case_3_2_row_0_2_0
  · exact rightFinal3_case_3_2_row_0_3_0
  · exact rightFinal3_case_3_2_row_1_0_0
  · exact rightFinal3_case_3_2_row_1_1_0
  · exact rightFinal3_case_3_2_row_1_2_0
  · exact rightFinal3_case_3_2_row_1_3_0
  · exact rightFinal3_case_3_2_row_2_0_0
  · exact rightFinal3_case_3_2_row_2_1_0
  · exact rightFinal3_case_3_2_row_2_2_0
  · exact rightFinal3_case_3_2_row_2_3_0
  · exact rightFinal3_case_3_2_row_3_0_0
  · exact rightFinal3_case_3_2_row_3_1_0
  · exact rightFinal3_case_3_2_row_3_2_0
  · exact rightFinal3_case_3_2_row_3_3_0

set_option backward.isDefEq.respectTransparency false in
theorem rightFinal3_case_3_2 : ((-1 : ℤ) ^ (rightScaleBit 3 3 2).val * positiveScale (rightScaleExponent 3 3 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 3 : ℤ)) • outerLeftZ 3 3 2 = negativeScale (rightScaleExponent 3 3 2) • (associatorZ 2 3 3 * right2Middle3 3 2) := by
  simpa only [HexagonAtoms332.assocABC_eq,
    HexagonAtoms332.outerABC_eq,
    HexagonAtoms332.assocBAC_eq,
    HexagonAtoms332.innerABC_eq,
    HexagonAtoms332.innerRightABC_eq,
    HexagonAtoms332.inverseACB_eq,
    HexagonAtoms332.innerACB_eq,
    HexagonAtoms332.assocBCA_eq,
    HexagonAtoms332.innerRightBAC_eq,
    HexagonAtoms332.assocCAB_eq,
    HexagonAtoms332.outerLeftABC_eq,
    HexagonRowColumn332.assocBAC_alias,
    HexagonRowColumn332.innerRightBAC_alias,
    HexagonRowColumn332.product0_eq,
    HexagonRowColumn332.product1_eq,
    HexagonRowColumn332.product2_eq,
    HexagonRowColumn332.product3_eq,
    HexagonRowColumn332.product4_eq,
    HexagonRowColumn332.product5_eq,
    HexagonRowColumn332.product6_eq,
    HexagonRowColumn332.product7_eq] using rightFinal3_case_3_2_checked

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonCases3
