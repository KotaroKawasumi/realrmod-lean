import RMod.BrundanEllis.StackingReferenceHexagonMiddle5
import RMod.BrundanEllis.StackingReferenceSparseMatrixCheck
import RMod.BrundanEllis.StackingReferenceHexagonAtoms556
import RMod.BrundanEllis.StackingReferenceHexagonRowColumn556

/-! Seven closed product identities for one reference triple.
The proof uses only verified atomic maps and ordinary kernel reduction. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
set_option linter.unusedSimpArgs false
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonCases5
open Superfusion

private theorem left0Middle5_eq_case_5_6_row_0_0_0 : (left0Middle5 5 6) ((0 : Fin 2), (0 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn556.rows_outerABC HexagonRowColumn556.cols_assocABC) ((0 : Fin 2), (0 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem left0Middle5_eq_case_5_6_row_0_1_0 : (left0Middle5 5 6) ((0 : Fin 2), (1 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn556.rows_outerABC HexagonRowColumn556.cols_assocABC) ((0 : Fin 2), (1 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem left0Middle5_eq_case_5_6_row_0_2_0 : (left0Middle5 5 6) ((0 : Fin 2), (2 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn556.rows_outerABC HexagonRowColumn556.cols_assocABC) ((0 : Fin 2), (2 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem left0Middle5_eq_case_5_6_row_0_3_0 : (left0Middle5 5 6) ((0 : Fin 2), (3 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn556.rows_outerABC HexagonRowColumn556.cols_assocABC) ((0 : Fin 2), (3 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem left0Middle5_eq_case_5_6_row_0_4_0 : (left0Middle5 5 6) ((0 : Fin 2), (4 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn556.rows_outerABC HexagonRowColumn556.cols_assocABC) ((0 : Fin 2), (4 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem left0Middle5_eq_case_5_6_row_0_5_0 : (left0Middle5 5 6) ((0 : Fin 2), (5 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn556.rows_outerABC HexagonRowColumn556.cols_assocABC) ((0 : Fin 2), (5 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem left0Middle5_eq_case_5_6_row_0_6_0 : (left0Middle5 5 6) ((0 : Fin 2), (6 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn556.rows_outerABC HexagonRowColumn556.cols_assocABC) ((0 : Fin 2), (6 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem left0Middle5_eq_case_5_6_row_0_7_0 : (left0Middle5 5 6) ((0 : Fin 2), (7 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn556.rows_outerABC HexagonRowColumn556.cols_assocABC) ((0 : Fin 2), (7 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem left0Middle5_eq_case_5_6_row_1_0_0 : (left0Middle5 5 6) ((1 : Fin 2), (0 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn556.rows_outerABC HexagonRowColumn556.cols_assocABC) ((1 : Fin 2), (0 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem left0Middle5_eq_case_5_6_row_1_1_0 : (left0Middle5 5 6) ((1 : Fin 2), (1 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn556.rows_outerABC HexagonRowColumn556.cols_assocABC) ((1 : Fin 2), (1 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem left0Middle5_eq_case_5_6_row_1_2_0 : (left0Middle5 5 6) ((1 : Fin 2), (2 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn556.rows_outerABC HexagonRowColumn556.cols_assocABC) ((1 : Fin 2), (2 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem left0Middle5_eq_case_5_6_row_1_3_0 : (left0Middle5 5 6) ((1 : Fin 2), (3 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn556.rows_outerABC HexagonRowColumn556.cols_assocABC) ((1 : Fin 2), (3 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem left0Middle5_eq_case_5_6_row_1_4_0 : (left0Middle5 5 6) ((1 : Fin 2), (4 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn556.rows_outerABC HexagonRowColumn556.cols_assocABC) ((1 : Fin 2), (4 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem left0Middle5_eq_case_5_6_row_1_5_0 : (left0Middle5 5 6) ((1 : Fin 2), (5 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn556.rows_outerABC HexagonRowColumn556.cols_assocABC) ((1 : Fin 2), (5 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem left0Middle5_eq_case_5_6_row_1_6_0 : (left0Middle5 5 6) ((1 : Fin 2), (6 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn556.rows_outerABC HexagonRowColumn556.cols_assocABC) ((1 : Fin 2), (6 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem left0Middle5_eq_case_5_6_row_1_7_0 : (left0Middle5 5 6) ((1 : Fin 2), (7 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn556.rows_outerABC HexagonRowColumn556.cols_assocABC) ((1 : Fin 2), (7 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem left0Middle5_eq_case_5_6_checked : left0Middle5 5 6 = rowColumnMul HexagonRowColumn556.rows_outerABC HexagonRowColumn556.cols_assocABC := by
  funext r
  fin_cases r
  · exact left0Middle5_eq_case_5_6_row_0_0_0
  · exact left0Middle5_eq_case_5_6_row_0_1_0
  · exact left0Middle5_eq_case_5_6_row_0_2_0
  · exact left0Middle5_eq_case_5_6_row_0_3_0
  · exact left0Middle5_eq_case_5_6_row_0_4_0
  · exact left0Middle5_eq_case_5_6_row_0_5_0
  · exact left0Middle5_eq_case_5_6_row_0_6_0
  · exact left0Middle5_eq_case_5_6_row_0_7_0
  · exact left0Middle5_eq_case_5_6_row_1_0_0
  · exact left0Middle5_eq_case_5_6_row_1_1_0
  · exact left0Middle5_eq_case_5_6_row_1_2_0
  · exact left0Middle5_eq_case_5_6_row_1_3_0
  · exact left0Middle5_eq_case_5_6_row_1_4_0
  · exact left0Middle5_eq_case_5_6_row_1_5_0
  · exact left0Middle5_eq_case_5_6_row_1_6_0
  · exact left0Middle5_eq_case_5_6_row_1_7_0

set_option backward.isDefEq.respectTransparency false in
theorem left0Middle5_eq_case_5_6 : left0Middle5 5 6 = outerRightZ 5 5 6 * associatorZ 5 5 6 := by
  simpa only [HexagonAtoms556.assocABC_eq,
    HexagonAtoms556.outerABC_eq,
    HexagonAtoms556.assocBAC_eq,
    HexagonAtoms556.innerABC_eq,
    HexagonAtoms556.innerRightABC_eq,
    HexagonAtoms556.inverseACB_eq,
    HexagonAtoms556.innerACB_eq,
    HexagonAtoms556.assocBCA_eq,
    HexagonAtoms556.innerRightBAC_eq,
    HexagonAtoms556.assocCAB_eq,
    HexagonAtoms556.outerLeftABC_eq,
    HexagonRowColumn556.assocBAC_alias,
    HexagonRowColumn556.innerRightBAC_alias,
    HexagonRowColumn556.product0_eq,
    HexagonRowColumn556.product1_eq,
    HexagonRowColumn556.product2_eq,
    HexagonRowColumn556.product3_eq,
    HexagonRowColumn556.product4_eq,
    HexagonRowColumn556.product5_eq,
    HexagonRowColumn556.product6_eq,
    HexagonRowColumn556.product7_eq] using left0Middle5_eq_case_5_6_checked

private theorem left1Middle5_eq_case_5_6_row_0_0_0 : (left1Middle5 5 6) ((0 : Fin 2), (0 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn556.rows_assocABC HexagonRowColumn556.cols_innerABC) ((0 : Fin 2), (0 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem left1Middle5_eq_case_5_6_row_0_1_0 : (left1Middle5 5 6) ((0 : Fin 2), (1 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn556.rows_assocABC HexagonRowColumn556.cols_innerABC) ((0 : Fin 2), (1 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem left1Middle5_eq_case_5_6_row_0_2_0 : (left1Middle5 5 6) ((0 : Fin 2), (2 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn556.rows_assocABC HexagonRowColumn556.cols_innerABC) ((0 : Fin 2), (2 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem left1Middle5_eq_case_5_6_row_0_3_0 : (left1Middle5 5 6) ((0 : Fin 2), (3 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn556.rows_assocABC HexagonRowColumn556.cols_innerABC) ((0 : Fin 2), (3 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem left1Middle5_eq_case_5_6_row_0_4_0 : (left1Middle5 5 6) ((0 : Fin 2), (4 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn556.rows_assocABC HexagonRowColumn556.cols_innerABC) ((0 : Fin 2), (4 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem left1Middle5_eq_case_5_6_row_0_5_0 : (left1Middle5 5 6) ((0 : Fin 2), (5 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn556.rows_assocABC HexagonRowColumn556.cols_innerABC) ((0 : Fin 2), (5 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem left1Middle5_eq_case_5_6_row_0_6_0 : (left1Middle5 5 6) ((0 : Fin 2), (6 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn556.rows_assocABC HexagonRowColumn556.cols_innerABC) ((0 : Fin 2), (6 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem left1Middle5_eq_case_5_6_row_0_7_0 : (left1Middle5 5 6) ((0 : Fin 2), (7 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn556.rows_assocABC HexagonRowColumn556.cols_innerABC) ((0 : Fin 2), (7 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem left1Middle5_eq_case_5_6_row_1_0_0 : (left1Middle5 5 6) ((1 : Fin 2), (0 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn556.rows_assocABC HexagonRowColumn556.cols_innerABC) ((1 : Fin 2), (0 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem left1Middle5_eq_case_5_6_row_1_1_0 : (left1Middle5 5 6) ((1 : Fin 2), (1 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn556.rows_assocABC HexagonRowColumn556.cols_innerABC) ((1 : Fin 2), (1 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem left1Middle5_eq_case_5_6_row_1_2_0 : (left1Middle5 5 6) ((1 : Fin 2), (2 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn556.rows_assocABC HexagonRowColumn556.cols_innerABC) ((1 : Fin 2), (2 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem left1Middle5_eq_case_5_6_row_1_3_0 : (left1Middle5 5 6) ((1 : Fin 2), (3 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn556.rows_assocABC HexagonRowColumn556.cols_innerABC) ((1 : Fin 2), (3 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem left1Middle5_eq_case_5_6_row_1_4_0 : (left1Middle5 5 6) ((1 : Fin 2), (4 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn556.rows_assocABC HexagonRowColumn556.cols_innerABC) ((1 : Fin 2), (4 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem left1Middle5_eq_case_5_6_row_1_5_0 : (left1Middle5 5 6) ((1 : Fin 2), (5 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn556.rows_assocABC HexagonRowColumn556.cols_innerABC) ((1 : Fin 2), (5 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem left1Middle5_eq_case_5_6_row_1_6_0 : (left1Middle5 5 6) ((1 : Fin 2), (6 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn556.rows_assocABC HexagonRowColumn556.cols_innerABC) ((1 : Fin 2), (6 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem left1Middle5_eq_case_5_6_row_1_7_0 : (left1Middle5 5 6) ((1 : Fin 2), (7 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn556.rows_assocABC HexagonRowColumn556.cols_innerABC) ((1 : Fin 2), (7 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem left1Middle5_eq_case_5_6_checked : left1Middle5 5 6 = rowColumnMul HexagonRowColumn556.rows_assocABC HexagonRowColumn556.cols_innerABC := by
  funext r
  fin_cases r
  · exact left1Middle5_eq_case_5_6_row_0_0_0
  · exact left1Middle5_eq_case_5_6_row_0_1_0
  · exact left1Middle5_eq_case_5_6_row_0_2_0
  · exact left1Middle5_eq_case_5_6_row_0_3_0
  · exact left1Middle5_eq_case_5_6_row_0_4_0
  · exact left1Middle5_eq_case_5_6_row_0_5_0
  · exact left1Middle5_eq_case_5_6_row_0_6_0
  · exact left1Middle5_eq_case_5_6_row_0_7_0
  · exact left1Middle5_eq_case_5_6_row_1_0_0
  · exact left1Middle5_eq_case_5_6_row_1_1_0
  · exact left1Middle5_eq_case_5_6_row_1_2_0
  · exact left1Middle5_eq_case_5_6_row_1_3_0
  · exact left1Middle5_eq_case_5_6_row_1_4_0
  · exact left1Middle5_eq_case_5_6_row_1_5_0
  · exact left1Middle5_eq_case_5_6_row_1_6_0
  · exact left1Middle5_eq_case_5_6_row_1_7_0

set_option backward.isDefEq.respectTransparency false in
theorem left1Middle5_eq_case_5_6 : left1Middle5 5 6 = associatorZ 5 5 6 * innerLeftZ 5 5 6 := by
  simpa only [HexagonAtoms556.assocABC_eq,
    HexagonAtoms556.outerABC_eq,
    HexagonAtoms556.assocBAC_eq,
    HexagonAtoms556.innerABC_eq,
    HexagonAtoms556.innerRightABC_eq,
    HexagonAtoms556.inverseACB_eq,
    HexagonAtoms556.innerACB_eq,
    HexagonAtoms556.assocBCA_eq,
    HexagonAtoms556.innerRightBAC_eq,
    HexagonAtoms556.assocCAB_eq,
    HexagonAtoms556.outerLeftABC_eq,
    HexagonRowColumn556.assocBAC_alias,
    HexagonRowColumn556.innerRightBAC_alias,
    HexagonRowColumn556.product0_eq,
    HexagonRowColumn556.product1_eq,
    HexagonRowColumn556.product2_eq,
    HexagonRowColumn556.product3_eq,
    HexagonRowColumn556.product4_eq,
    HexagonRowColumn556.product5_eq,
    HexagonRowColumn556.product6_eq,
    HexagonRowColumn556.product7_eq] using left1Middle5_eq_case_5_6_checked

private theorem right0Middle5_eq_case_5_6_row_0_0_0 : (right0Middle5 5 6) ((0 : Fin 2), (0 : Fin 8), (0 : Fin 1)) = (HexagonAtoms556.assocABC) ((0 : Fin 2), (0 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem right0Middle5_eq_case_5_6_row_0_1_0 : (right0Middle5 5 6) ((0 : Fin 2), (1 : Fin 8), (0 : Fin 1)) = (HexagonAtoms556.assocABC) ((0 : Fin 2), (1 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem right0Middle5_eq_case_5_6_row_0_2_0 : (right0Middle5 5 6) ((0 : Fin 2), (2 : Fin 8), (0 : Fin 1)) = (HexagonAtoms556.assocABC) ((0 : Fin 2), (2 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem right0Middle5_eq_case_5_6_row_0_3_0 : (right0Middle5 5 6) ((0 : Fin 2), (3 : Fin 8), (0 : Fin 1)) = (HexagonAtoms556.assocABC) ((0 : Fin 2), (3 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem right0Middle5_eq_case_5_6_row_0_4_0 : (right0Middle5 5 6) ((0 : Fin 2), (4 : Fin 8), (0 : Fin 1)) = (HexagonAtoms556.assocABC) ((0 : Fin 2), (4 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem right0Middle5_eq_case_5_6_row_0_5_0 : (right0Middle5 5 6) ((0 : Fin 2), (5 : Fin 8), (0 : Fin 1)) = (HexagonAtoms556.assocABC) ((0 : Fin 2), (5 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem right0Middle5_eq_case_5_6_row_0_6_0 : (right0Middle5 5 6) ((0 : Fin 2), (6 : Fin 8), (0 : Fin 1)) = (HexagonAtoms556.assocABC) ((0 : Fin 2), (6 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem right0Middle5_eq_case_5_6_row_0_7_0 : (right0Middle5 5 6) ((0 : Fin 2), (7 : Fin 8), (0 : Fin 1)) = (HexagonAtoms556.assocABC) ((0 : Fin 2), (7 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem right0Middle5_eq_case_5_6_row_1_0_0 : (right0Middle5 5 6) ((1 : Fin 2), (0 : Fin 8), (0 : Fin 1)) = (HexagonAtoms556.assocABC) ((1 : Fin 2), (0 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem right0Middle5_eq_case_5_6_row_1_1_0 : (right0Middle5 5 6) ((1 : Fin 2), (1 : Fin 8), (0 : Fin 1)) = (HexagonAtoms556.assocABC) ((1 : Fin 2), (1 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem right0Middle5_eq_case_5_6_row_1_2_0 : (right0Middle5 5 6) ((1 : Fin 2), (2 : Fin 8), (0 : Fin 1)) = (HexagonAtoms556.assocABC) ((1 : Fin 2), (2 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem right0Middle5_eq_case_5_6_row_1_3_0 : (right0Middle5 5 6) ((1 : Fin 2), (3 : Fin 8), (0 : Fin 1)) = (HexagonAtoms556.assocABC) ((1 : Fin 2), (3 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem right0Middle5_eq_case_5_6_row_1_4_0 : (right0Middle5 5 6) ((1 : Fin 2), (4 : Fin 8), (0 : Fin 1)) = (HexagonAtoms556.assocABC) ((1 : Fin 2), (4 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem right0Middle5_eq_case_5_6_row_1_5_0 : (right0Middle5 5 6) ((1 : Fin 2), (5 : Fin 8), (0 : Fin 1)) = (HexagonAtoms556.assocABC) ((1 : Fin 2), (5 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem right0Middle5_eq_case_5_6_row_1_6_0 : (right0Middle5 5 6) ((1 : Fin 2), (6 : Fin 8), (0 : Fin 1)) = (HexagonAtoms556.assocABC) ((1 : Fin 2), (6 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem right0Middle5_eq_case_5_6_row_1_7_0 : (right0Middle5 5 6) ((1 : Fin 2), (7 : Fin 8), (0 : Fin 1)) = (HexagonAtoms556.assocABC) ((1 : Fin 2), (7 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem right0Middle5_eq_case_5_6_checked : right0Middle5 5 6 = HexagonAtoms556.assocABC := by
  funext r
  fin_cases r
  · exact right0Middle5_eq_case_5_6_row_0_0_0
  · exact right0Middle5_eq_case_5_6_row_0_1_0
  · exact right0Middle5_eq_case_5_6_row_0_2_0
  · exact right0Middle5_eq_case_5_6_row_0_3_0
  · exact right0Middle5_eq_case_5_6_row_0_4_0
  · exact right0Middle5_eq_case_5_6_row_0_5_0
  · exact right0Middle5_eq_case_5_6_row_0_6_0
  · exact right0Middle5_eq_case_5_6_row_0_7_0
  · exact right0Middle5_eq_case_5_6_row_1_0_0
  · exact right0Middle5_eq_case_5_6_row_1_1_0
  · exact right0Middle5_eq_case_5_6_row_1_2_0
  · exact right0Middle5_eq_case_5_6_row_1_3_0
  · exact right0Middle5_eq_case_5_6_row_1_4_0
  · exact right0Middle5_eq_case_5_6_row_1_5_0
  · exact right0Middle5_eq_case_5_6_row_1_6_0
  · exact right0Middle5_eq_case_5_6_row_1_7_0

set_option backward.isDefEq.respectTransparency false in
theorem right0Middle5_eq_case_5_6 : right0Middle5 5 6 = innerRightZ 5 5 6 * associatorZ 5 5 6 := by
  simpa only [HexagonAtoms556.assocABC_eq,
    HexagonAtoms556.outerABC_eq,
    HexagonAtoms556.assocBAC_eq,
    HexagonAtoms556.innerABC_eq,
    HexagonAtoms556.innerRightABC_eq,
    HexagonAtoms556.inverseACB_eq,
    HexagonAtoms556.innerACB_eq,
    HexagonAtoms556.assocBCA_eq,
    HexagonAtoms556.innerRightBAC_eq,
    HexagonAtoms556.assocCAB_eq,
    HexagonAtoms556.outerLeftABC_eq,
    HexagonRowColumn556.assocBAC_alias,
    HexagonRowColumn556.innerRightBAC_alias,
    HexagonRowColumn556.product0_eq,
    HexagonRowColumn556.product1_eq,
    HexagonRowColumn556.product2_eq,
    HexagonRowColumn556.product3_eq,
    HexagonRowColumn556.product4_eq,
    HexagonRowColumn556.product5_eq,
    HexagonRowColumn556.product6_eq,
    HexagonRowColumn556.product7_eq] using right0Middle5_eq_case_5_6_checked

private theorem right1Middle5_eq_case_5_6_row_0_0_0 : (right1Middle5 5 6) ((0 : Fin 2), (0 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn556.rows_inverseACB HexagonRowColumn556.cols_right0) ((0 : Fin 2), (0 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem right1Middle5_eq_case_5_6_row_0_1_0 : (right1Middle5 5 6) ((0 : Fin 2), (1 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn556.rows_inverseACB HexagonRowColumn556.cols_right0) ((0 : Fin 2), (1 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem right1Middle5_eq_case_5_6_row_0_2_0 : (right1Middle5 5 6) ((0 : Fin 2), (2 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn556.rows_inverseACB HexagonRowColumn556.cols_right0) ((0 : Fin 2), (2 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem right1Middle5_eq_case_5_6_row_0_3_0 : (right1Middle5 5 6) ((0 : Fin 2), (3 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn556.rows_inverseACB HexagonRowColumn556.cols_right0) ((0 : Fin 2), (3 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem right1Middle5_eq_case_5_6_row_0_4_0 : (right1Middle5 5 6) ((0 : Fin 2), (4 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn556.rows_inverseACB HexagonRowColumn556.cols_right0) ((0 : Fin 2), (4 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem right1Middle5_eq_case_5_6_row_0_5_0 : (right1Middle5 5 6) ((0 : Fin 2), (5 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn556.rows_inverseACB HexagonRowColumn556.cols_right0) ((0 : Fin 2), (5 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem right1Middle5_eq_case_5_6_row_0_6_0 : (right1Middle5 5 6) ((0 : Fin 2), (6 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn556.rows_inverseACB HexagonRowColumn556.cols_right0) ((0 : Fin 2), (6 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem right1Middle5_eq_case_5_6_row_0_7_0 : (right1Middle5 5 6) ((0 : Fin 2), (7 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn556.rows_inverseACB HexagonRowColumn556.cols_right0) ((0 : Fin 2), (7 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem right1Middle5_eq_case_5_6_row_1_0_0 : (right1Middle5 5 6) ((1 : Fin 2), (0 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn556.rows_inverseACB HexagonRowColumn556.cols_right0) ((1 : Fin 2), (0 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem right1Middle5_eq_case_5_6_row_1_1_0 : (right1Middle5 5 6) ((1 : Fin 2), (1 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn556.rows_inverseACB HexagonRowColumn556.cols_right0) ((1 : Fin 2), (1 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem right1Middle5_eq_case_5_6_row_1_2_0 : (right1Middle5 5 6) ((1 : Fin 2), (2 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn556.rows_inverseACB HexagonRowColumn556.cols_right0) ((1 : Fin 2), (2 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem right1Middle5_eq_case_5_6_row_1_3_0 : (right1Middle5 5 6) ((1 : Fin 2), (3 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn556.rows_inverseACB HexagonRowColumn556.cols_right0) ((1 : Fin 2), (3 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem right1Middle5_eq_case_5_6_row_1_4_0 : (right1Middle5 5 6) ((1 : Fin 2), (4 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn556.rows_inverseACB HexagonRowColumn556.cols_right0) ((1 : Fin 2), (4 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem right1Middle5_eq_case_5_6_row_1_5_0 : (right1Middle5 5 6) ((1 : Fin 2), (5 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn556.rows_inverseACB HexagonRowColumn556.cols_right0) ((1 : Fin 2), (5 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem right1Middle5_eq_case_5_6_row_1_6_0 : (right1Middle5 5 6) ((1 : Fin 2), (6 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn556.rows_inverseACB HexagonRowColumn556.cols_right0) ((1 : Fin 2), (6 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem right1Middle5_eq_case_5_6_row_1_7_0 : (right1Middle5 5 6) ((1 : Fin 2), (7 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn556.rows_inverseACB HexagonRowColumn556.cols_right0) ((1 : Fin 2), (7 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem right1Middle5_eq_case_5_6_checked : right1Middle5 5 6 = rowColumnMul HexagonRowColumn556.rows_inverseACB HexagonRowColumn556.cols_right0 := by
  funext r
  fin_cases r
  · exact right1Middle5_eq_case_5_6_row_0_0_0
  · exact right1Middle5_eq_case_5_6_row_0_1_0
  · exact right1Middle5_eq_case_5_6_row_0_2_0
  · exact right1Middle5_eq_case_5_6_row_0_3_0
  · exact right1Middle5_eq_case_5_6_row_0_4_0
  · exact right1Middle5_eq_case_5_6_row_0_5_0
  · exact right1Middle5_eq_case_5_6_row_0_6_0
  · exact right1Middle5_eq_case_5_6_row_0_7_0
  · exact right1Middle5_eq_case_5_6_row_1_0_0
  · exact right1Middle5_eq_case_5_6_row_1_1_0
  · exact right1Middle5_eq_case_5_6_row_1_2_0
  · exact right1Middle5_eq_case_5_6_row_1_3_0
  · exact right1Middle5_eq_case_5_6_row_1_4_0
  · exact right1Middle5_eq_case_5_6_row_1_5_0
  · exact right1Middle5_eq_case_5_6_row_1_6_0
  · exact right1Middle5_eq_case_5_6_row_1_7_0

set_option backward.isDefEq.respectTransparency false in
theorem right1Middle5_eq_case_5_6 : right1Middle5 5 6 = associatorInverseZ 5 6 5 * right0Middle5 5 6 := by
  simpa only [HexagonAtoms556.assocABC_eq,
    HexagonAtoms556.outerABC_eq,
    HexagonAtoms556.assocBAC_eq,
    HexagonAtoms556.innerABC_eq,
    HexagonAtoms556.innerRightABC_eq,
    HexagonAtoms556.inverseACB_eq,
    HexagonAtoms556.innerACB_eq,
    HexagonAtoms556.assocBCA_eq,
    HexagonAtoms556.innerRightBAC_eq,
    HexagonAtoms556.assocCAB_eq,
    HexagonAtoms556.outerLeftABC_eq,
    HexagonRowColumn556.assocBAC_alias,
    HexagonRowColumn556.innerRightBAC_alias,
    HexagonRowColumn556.product0_eq,
    HexagonRowColumn556.product1_eq,
    HexagonRowColumn556.product2_eq,
    HexagonRowColumn556.product3_eq,
    HexagonRowColumn556.product4_eq,
    HexagonRowColumn556.product5_eq,
    HexagonRowColumn556.product6_eq,
    HexagonRowColumn556.product7_eq] using right1Middle5_eq_case_5_6_checked

private theorem right2Middle5_eq_case_5_6_row_0_0_0 : (right2Middle5 5 6) ((0 : Fin 2), (0 : Fin 8), (0 : Fin 1)) = (right1Middle5 5 6) ((0 : Fin 2), (0 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem right2Middle5_eq_case_5_6_row_0_1_0 : (right2Middle5 5 6) ((0 : Fin 2), (1 : Fin 8), (0 : Fin 1)) = (right1Middle5 5 6) ((0 : Fin 2), (1 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem right2Middle5_eq_case_5_6_row_0_2_0 : (right2Middle5 5 6) ((0 : Fin 2), (2 : Fin 8), (0 : Fin 1)) = (right1Middle5 5 6) ((0 : Fin 2), (2 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem right2Middle5_eq_case_5_6_row_0_3_0 : (right2Middle5 5 6) ((0 : Fin 2), (3 : Fin 8), (0 : Fin 1)) = (right1Middle5 5 6) ((0 : Fin 2), (3 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem right2Middle5_eq_case_5_6_row_0_4_0 : (right2Middle5 5 6) ((0 : Fin 2), (4 : Fin 8), (0 : Fin 1)) = (right1Middle5 5 6) ((0 : Fin 2), (4 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem right2Middle5_eq_case_5_6_row_0_5_0 : (right2Middle5 5 6) ((0 : Fin 2), (5 : Fin 8), (0 : Fin 1)) = (right1Middle5 5 6) ((0 : Fin 2), (5 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem right2Middle5_eq_case_5_6_row_0_6_0 : (right2Middle5 5 6) ((0 : Fin 2), (6 : Fin 8), (0 : Fin 1)) = (right1Middle5 5 6) ((0 : Fin 2), (6 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem right2Middle5_eq_case_5_6_row_0_7_0 : (right2Middle5 5 6) ((0 : Fin 2), (7 : Fin 8), (0 : Fin 1)) = (right1Middle5 5 6) ((0 : Fin 2), (7 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem right2Middle5_eq_case_5_6_row_1_0_0 : (right2Middle5 5 6) ((1 : Fin 2), (0 : Fin 8), (0 : Fin 1)) = (right1Middle5 5 6) ((1 : Fin 2), (0 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem right2Middle5_eq_case_5_6_row_1_1_0 : (right2Middle5 5 6) ((1 : Fin 2), (1 : Fin 8), (0 : Fin 1)) = (right1Middle5 5 6) ((1 : Fin 2), (1 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem right2Middle5_eq_case_5_6_row_1_2_0 : (right2Middle5 5 6) ((1 : Fin 2), (2 : Fin 8), (0 : Fin 1)) = (right1Middle5 5 6) ((1 : Fin 2), (2 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem right2Middle5_eq_case_5_6_row_1_3_0 : (right2Middle5 5 6) ((1 : Fin 2), (3 : Fin 8), (0 : Fin 1)) = (right1Middle5 5 6) ((1 : Fin 2), (3 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem right2Middle5_eq_case_5_6_row_1_4_0 : (right2Middle5 5 6) ((1 : Fin 2), (4 : Fin 8), (0 : Fin 1)) = (right1Middle5 5 6) ((1 : Fin 2), (4 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem right2Middle5_eq_case_5_6_row_1_5_0 : (right2Middle5 5 6) ((1 : Fin 2), (5 : Fin 8), (0 : Fin 1)) = (right1Middle5 5 6) ((1 : Fin 2), (5 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem right2Middle5_eq_case_5_6_row_1_6_0 : (right2Middle5 5 6) ((1 : Fin 2), (6 : Fin 8), (0 : Fin 1)) = (right1Middle5 5 6) ((1 : Fin 2), (6 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem right2Middle5_eq_case_5_6_row_1_7_0 : (right2Middle5 5 6) ((1 : Fin 2), (7 : Fin 8), (0 : Fin 1)) = (right1Middle5 5 6) ((1 : Fin 2), (7 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem right2Middle5_eq_case_5_6_checked : right2Middle5 5 6 = right1Middle5 5 6 := by
  funext r
  fin_cases r
  · exact right2Middle5_eq_case_5_6_row_0_0_0
  · exact right2Middle5_eq_case_5_6_row_0_1_0
  · exact right2Middle5_eq_case_5_6_row_0_2_0
  · exact right2Middle5_eq_case_5_6_row_0_3_0
  · exact right2Middle5_eq_case_5_6_row_0_4_0
  · exact right2Middle5_eq_case_5_6_row_0_5_0
  · exact right2Middle5_eq_case_5_6_row_0_6_0
  · exact right2Middle5_eq_case_5_6_row_0_7_0
  · exact right2Middle5_eq_case_5_6_row_1_0_0
  · exact right2Middle5_eq_case_5_6_row_1_1_0
  · exact right2Middle5_eq_case_5_6_row_1_2_0
  · exact right2Middle5_eq_case_5_6_row_1_3_0
  · exact right2Middle5_eq_case_5_6_row_1_4_0
  · exact right2Middle5_eq_case_5_6_row_1_5_0
  · exact right2Middle5_eq_case_5_6_row_1_6_0
  · exact right2Middle5_eq_case_5_6_row_1_7_0

set_option backward.isDefEq.respectTransparency false in
theorem right2Middle5_eq_case_5_6 : right2Middle5 5 6 = innerLeftZ 5 6 5 * right1Middle5 5 6 := by
  simpa only [HexagonAtoms556.assocABC_eq,
    HexagonAtoms556.outerABC_eq,
    HexagonAtoms556.assocBAC_eq,
    HexagonAtoms556.innerABC_eq,
    HexagonAtoms556.innerRightABC_eq,
    HexagonAtoms556.inverseACB_eq,
    HexagonAtoms556.innerACB_eq,
    HexagonAtoms556.assocBCA_eq,
    HexagonAtoms556.innerRightBAC_eq,
    HexagonAtoms556.assocCAB_eq,
    HexagonAtoms556.outerLeftABC_eq,
    HexagonRowColumn556.assocBAC_alias,
    HexagonRowColumn556.innerRightBAC_alias,
    HexagonRowColumn556.product0_eq,
    HexagonRowColumn556.product1_eq,
    HexagonRowColumn556.product2_eq,
    HexagonRowColumn556.product3_eq,
    HexagonRowColumn556.product4_eq,
    HexagonRowColumn556.product5_eq,
    HexagonRowColumn556.product6_eq,
    HexagonRowColumn556.product7_eq] using right2Middle5_eq_case_5_6_checked

private theorem leftFinal5_case_5_6_row_0_0_0 : (((-1 : ℤ) ^ (leftScaleBit 5 5 6).val * positiveScale (leftScaleExponent 5 5 6)) •
      (rowColumnMul HexagonRowColumn556.rows_assocBCA HexagonRowColumn556.cols_left0)) ((0 : Fin 2), (0 : Fin 8), (0 : Fin 1)) = (negativeScale (leftScaleExponent 5 5 6) • (left1Middle5 5 6)) ((0 : Fin 2), (0 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem leftFinal5_case_5_6_row_0_1_0 : (((-1 : ℤ) ^ (leftScaleBit 5 5 6).val * positiveScale (leftScaleExponent 5 5 6)) •
      (rowColumnMul HexagonRowColumn556.rows_assocBCA HexagonRowColumn556.cols_left0)) ((0 : Fin 2), (1 : Fin 8), (0 : Fin 1)) = (negativeScale (leftScaleExponent 5 5 6) • (left1Middle5 5 6)) ((0 : Fin 2), (1 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem leftFinal5_case_5_6_row_0_2_0 : (((-1 : ℤ) ^ (leftScaleBit 5 5 6).val * positiveScale (leftScaleExponent 5 5 6)) •
      (rowColumnMul HexagonRowColumn556.rows_assocBCA HexagonRowColumn556.cols_left0)) ((0 : Fin 2), (2 : Fin 8), (0 : Fin 1)) = (negativeScale (leftScaleExponent 5 5 6) • (left1Middle5 5 6)) ((0 : Fin 2), (2 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem leftFinal5_case_5_6_row_0_3_0 : (((-1 : ℤ) ^ (leftScaleBit 5 5 6).val * positiveScale (leftScaleExponent 5 5 6)) •
      (rowColumnMul HexagonRowColumn556.rows_assocBCA HexagonRowColumn556.cols_left0)) ((0 : Fin 2), (3 : Fin 8), (0 : Fin 1)) = (negativeScale (leftScaleExponent 5 5 6) • (left1Middle5 5 6)) ((0 : Fin 2), (3 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem leftFinal5_case_5_6_row_0_4_0 : (((-1 : ℤ) ^ (leftScaleBit 5 5 6).val * positiveScale (leftScaleExponent 5 5 6)) •
      (rowColumnMul HexagonRowColumn556.rows_assocBCA HexagonRowColumn556.cols_left0)) ((0 : Fin 2), (4 : Fin 8), (0 : Fin 1)) = (negativeScale (leftScaleExponent 5 5 6) • (left1Middle5 5 6)) ((0 : Fin 2), (4 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem leftFinal5_case_5_6_row_0_5_0 : (((-1 : ℤ) ^ (leftScaleBit 5 5 6).val * positiveScale (leftScaleExponent 5 5 6)) •
      (rowColumnMul HexagonRowColumn556.rows_assocBCA HexagonRowColumn556.cols_left0)) ((0 : Fin 2), (5 : Fin 8), (0 : Fin 1)) = (negativeScale (leftScaleExponent 5 5 6) • (left1Middle5 5 6)) ((0 : Fin 2), (5 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem leftFinal5_case_5_6_row_0_6_0 : (((-1 : ℤ) ^ (leftScaleBit 5 5 6).val * positiveScale (leftScaleExponent 5 5 6)) •
      (rowColumnMul HexagonRowColumn556.rows_assocBCA HexagonRowColumn556.cols_left0)) ((0 : Fin 2), (6 : Fin 8), (0 : Fin 1)) = (negativeScale (leftScaleExponent 5 5 6) • (left1Middle5 5 6)) ((0 : Fin 2), (6 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem leftFinal5_case_5_6_row_0_7_0 : (((-1 : ℤ) ^ (leftScaleBit 5 5 6).val * positiveScale (leftScaleExponent 5 5 6)) •
      (rowColumnMul HexagonRowColumn556.rows_assocBCA HexagonRowColumn556.cols_left0)) ((0 : Fin 2), (7 : Fin 8), (0 : Fin 1)) = (negativeScale (leftScaleExponent 5 5 6) • (left1Middle5 5 6)) ((0 : Fin 2), (7 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem leftFinal5_case_5_6_row_1_0_0 : (((-1 : ℤ) ^ (leftScaleBit 5 5 6).val * positiveScale (leftScaleExponent 5 5 6)) •
      (rowColumnMul HexagonRowColumn556.rows_assocBCA HexagonRowColumn556.cols_left0)) ((1 : Fin 2), (0 : Fin 8), (0 : Fin 1)) = (negativeScale (leftScaleExponent 5 5 6) • (left1Middle5 5 6)) ((1 : Fin 2), (0 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem leftFinal5_case_5_6_row_1_1_0 : (((-1 : ℤ) ^ (leftScaleBit 5 5 6).val * positiveScale (leftScaleExponent 5 5 6)) •
      (rowColumnMul HexagonRowColumn556.rows_assocBCA HexagonRowColumn556.cols_left0)) ((1 : Fin 2), (1 : Fin 8), (0 : Fin 1)) = (negativeScale (leftScaleExponent 5 5 6) • (left1Middle5 5 6)) ((1 : Fin 2), (1 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem leftFinal5_case_5_6_row_1_2_0 : (((-1 : ℤ) ^ (leftScaleBit 5 5 6).val * positiveScale (leftScaleExponent 5 5 6)) •
      (rowColumnMul HexagonRowColumn556.rows_assocBCA HexagonRowColumn556.cols_left0)) ((1 : Fin 2), (2 : Fin 8), (0 : Fin 1)) = (negativeScale (leftScaleExponent 5 5 6) • (left1Middle5 5 6)) ((1 : Fin 2), (2 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem leftFinal5_case_5_6_row_1_3_0 : (((-1 : ℤ) ^ (leftScaleBit 5 5 6).val * positiveScale (leftScaleExponent 5 5 6)) •
      (rowColumnMul HexagonRowColumn556.rows_assocBCA HexagonRowColumn556.cols_left0)) ((1 : Fin 2), (3 : Fin 8), (0 : Fin 1)) = (negativeScale (leftScaleExponent 5 5 6) • (left1Middle5 5 6)) ((1 : Fin 2), (3 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem leftFinal5_case_5_6_row_1_4_0 : (((-1 : ℤ) ^ (leftScaleBit 5 5 6).val * positiveScale (leftScaleExponent 5 5 6)) •
      (rowColumnMul HexagonRowColumn556.rows_assocBCA HexagonRowColumn556.cols_left0)) ((1 : Fin 2), (4 : Fin 8), (0 : Fin 1)) = (negativeScale (leftScaleExponent 5 5 6) • (left1Middle5 5 6)) ((1 : Fin 2), (4 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem leftFinal5_case_5_6_row_1_5_0 : (((-1 : ℤ) ^ (leftScaleBit 5 5 6).val * positiveScale (leftScaleExponent 5 5 6)) •
      (rowColumnMul HexagonRowColumn556.rows_assocBCA HexagonRowColumn556.cols_left0)) ((1 : Fin 2), (5 : Fin 8), (0 : Fin 1)) = (negativeScale (leftScaleExponent 5 5 6) • (left1Middle5 5 6)) ((1 : Fin 2), (5 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem leftFinal5_case_5_6_row_1_6_0 : (((-1 : ℤ) ^ (leftScaleBit 5 5 6).val * positiveScale (leftScaleExponent 5 5 6)) •
      (rowColumnMul HexagonRowColumn556.rows_assocBCA HexagonRowColumn556.cols_left0)) ((1 : Fin 2), (6 : Fin 8), (0 : Fin 1)) = (negativeScale (leftScaleExponent 5 5 6) • (left1Middle5 5 6)) ((1 : Fin 2), (6 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem leftFinal5_case_5_6_row_1_7_0 : (((-1 : ℤ) ^ (leftScaleBit 5 5 6).val * positiveScale (leftScaleExponent 5 5 6)) •
      (rowColumnMul HexagonRowColumn556.rows_assocBCA HexagonRowColumn556.cols_left0)) ((1 : Fin 2), (7 : Fin 8), (0 : Fin 1)) = (negativeScale (leftScaleExponent 5 5 6) • (left1Middle5 5 6)) ((1 : Fin 2), (7 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem leftFinal5_case_5_6_checked : ((-1 : ℤ) ^ (leftScaleBit 5 5 6).val * positiveScale (leftScaleExponent 5 5 6)) •
      (rowColumnMul HexagonRowColumn556.rows_assocBCA HexagonRowColumn556.cols_left0) = negativeScale (leftScaleExponent 5 5 6) • (left1Middle5 5 6) := by
  funext r
  fin_cases r
  · exact leftFinal5_case_5_6_row_0_0_0
  · exact leftFinal5_case_5_6_row_0_1_0
  · exact leftFinal5_case_5_6_row_0_2_0
  · exact leftFinal5_case_5_6_row_0_3_0
  · exact leftFinal5_case_5_6_row_0_4_0
  · exact leftFinal5_case_5_6_row_0_5_0
  · exact leftFinal5_case_5_6_row_0_6_0
  · exact leftFinal5_case_5_6_row_0_7_0
  · exact leftFinal5_case_5_6_row_1_0_0
  · exact leftFinal5_case_5_6_row_1_1_0
  · exact leftFinal5_case_5_6_row_1_2_0
  · exact leftFinal5_case_5_6_row_1_3_0
  · exact leftFinal5_case_5_6_row_1_4_0
  · exact leftFinal5_case_5_6_row_1_5_0
  · exact leftFinal5_case_5_6_row_1_6_0
  · exact leftFinal5_case_5_6_row_1_7_0

set_option backward.isDefEq.respectTransparency false in
theorem leftFinal5_case_5_6 : ((-1 : ℤ) ^ (leftScaleBit 5 5 6).val * positiveScale (leftScaleExponent 5 5 6)) •
      (associatorZ 5 6 5 * left0Middle5 5 6) = negativeScale (leftScaleExponent 5 5 6) • (innerRightZ 5 5 6 * left1Middle5 5 6) := by
  simpa only [HexagonAtoms556.assocABC_eq,
    HexagonAtoms556.outerABC_eq,
    HexagonAtoms556.assocBAC_eq,
    HexagonAtoms556.innerABC_eq,
    HexagonAtoms556.innerRightABC_eq,
    HexagonAtoms556.inverseACB_eq,
    HexagonAtoms556.innerACB_eq,
    HexagonAtoms556.assocBCA_eq,
    HexagonAtoms556.innerRightBAC_eq,
    HexagonAtoms556.assocCAB_eq,
    HexagonAtoms556.outerLeftABC_eq,
    HexagonRowColumn556.assocBAC_alias,
    HexagonRowColumn556.innerRightBAC_alias,
    HexagonRowColumn556.product0_eq,
    HexagonRowColumn556.product1_eq,
    HexagonRowColumn556.product2_eq,
    HexagonRowColumn556.product3_eq,
    HexagonRowColumn556.product4_eq,
    HexagonRowColumn556.product5_eq,
    HexagonRowColumn556.product6_eq,
    HexagonRowColumn556.product7_eq] using leftFinal5_case_5_6_checked

private theorem rightFinal5_case_5_6_row_0_0_0 : (((-1 : ℤ) ^ (rightScaleBit 5 5 6).val * positiveScale (rightScaleExponent 5 5 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 6 5 : ℤ)) • HexagonAtoms556.outerLeftABC) ((0 : Fin 4), (0 : Fin 4), (0 : Fin 1)) = (negativeScale (rightScaleExponent 5 5 6) • (rowColumnMul HexagonRowColumn556.rows_assocCAB HexagonRowColumn556.cols_right2)) ((0 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem rightFinal5_case_5_6_row_0_1_0 : (((-1 : ℤ) ^ (rightScaleBit 5 5 6).val * positiveScale (rightScaleExponent 5 5 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 6 5 : ℤ)) • HexagonAtoms556.outerLeftABC) ((0 : Fin 4), (1 : Fin 4), (0 : Fin 1)) = (negativeScale (rightScaleExponent 5 5 6) • (rowColumnMul HexagonRowColumn556.rows_assocCAB HexagonRowColumn556.cols_right2)) ((0 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem rightFinal5_case_5_6_row_0_2_0 : (((-1 : ℤ) ^ (rightScaleBit 5 5 6).val * positiveScale (rightScaleExponent 5 5 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 6 5 : ℤ)) • HexagonAtoms556.outerLeftABC) ((0 : Fin 4), (2 : Fin 4), (0 : Fin 1)) = (negativeScale (rightScaleExponent 5 5 6) • (rowColumnMul HexagonRowColumn556.rows_assocCAB HexagonRowColumn556.cols_right2)) ((0 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem rightFinal5_case_5_6_row_0_3_0 : (((-1 : ℤ) ^ (rightScaleBit 5 5 6).val * positiveScale (rightScaleExponent 5 5 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 6 5 : ℤ)) • HexagonAtoms556.outerLeftABC) ((0 : Fin 4), (3 : Fin 4), (0 : Fin 1)) = (negativeScale (rightScaleExponent 5 5 6) • (rowColumnMul HexagonRowColumn556.rows_assocCAB HexagonRowColumn556.cols_right2)) ((0 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem rightFinal5_case_5_6_row_1_0_0 : (((-1 : ℤ) ^ (rightScaleBit 5 5 6).val * positiveScale (rightScaleExponent 5 5 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 6 5 : ℤ)) • HexagonAtoms556.outerLeftABC) ((1 : Fin 4), (0 : Fin 4), (0 : Fin 1)) = (negativeScale (rightScaleExponent 5 5 6) • (rowColumnMul HexagonRowColumn556.rows_assocCAB HexagonRowColumn556.cols_right2)) ((1 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem rightFinal5_case_5_6_row_1_1_0 : (((-1 : ℤ) ^ (rightScaleBit 5 5 6).val * positiveScale (rightScaleExponent 5 5 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 6 5 : ℤ)) • HexagonAtoms556.outerLeftABC) ((1 : Fin 4), (1 : Fin 4), (0 : Fin 1)) = (negativeScale (rightScaleExponent 5 5 6) • (rowColumnMul HexagonRowColumn556.rows_assocCAB HexagonRowColumn556.cols_right2)) ((1 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem rightFinal5_case_5_6_row_1_2_0 : (((-1 : ℤ) ^ (rightScaleBit 5 5 6).val * positiveScale (rightScaleExponent 5 5 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 6 5 : ℤ)) • HexagonAtoms556.outerLeftABC) ((1 : Fin 4), (2 : Fin 4), (0 : Fin 1)) = (negativeScale (rightScaleExponent 5 5 6) • (rowColumnMul HexagonRowColumn556.rows_assocCAB HexagonRowColumn556.cols_right2)) ((1 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem rightFinal5_case_5_6_row_1_3_0 : (((-1 : ℤ) ^ (rightScaleBit 5 5 6).val * positiveScale (rightScaleExponent 5 5 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 6 5 : ℤ)) • HexagonAtoms556.outerLeftABC) ((1 : Fin 4), (3 : Fin 4), (0 : Fin 1)) = (negativeScale (rightScaleExponent 5 5 6) • (rowColumnMul HexagonRowColumn556.rows_assocCAB HexagonRowColumn556.cols_right2)) ((1 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem rightFinal5_case_5_6_row_2_0_0 : (((-1 : ℤ) ^ (rightScaleBit 5 5 6).val * positiveScale (rightScaleExponent 5 5 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 6 5 : ℤ)) • HexagonAtoms556.outerLeftABC) ((2 : Fin 4), (0 : Fin 4), (0 : Fin 1)) = (negativeScale (rightScaleExponent 5 5 6) • (rowColumnMul HexagonRowColumn556.rows_assocCAB HexagonRowColumn556.cols_right2)) ((2 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem rightFinal5_case_5_6_row_2_1_0 : (((-1 : ℤ) ^ (rightScaleBit 5 5 6).val * positiveScale (rightScaleExponent 5 5 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 6 5 : ℤ)) • HexagonAtoms556.outerLeftABC) ((2 : Fin 4), (1 : Fin 4), (0 : Fin 1)) = (negativeScale (rightScaleExponent 5 5 6) • (rowColumnMul HexagonRowColumn556.rows_assocCAB HexagonRowColumn556.cols_right2)) ((2 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem rightFinal5_case_5_6_row_2_2_0 : (((-1 : ℤ) ^ (rightScaleBit 5 5 6).val * positiveScale (rightScaleExponent 5 5 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 6 5 : ℤ)) • HexagonAtoms556.outerLeftABC) ((2 : Fin 4), (2 : Fin 4), (0 : Fin 1)) = (negativeScale (rightScaleExponent 5 5 6) • (rowColumnMul HexagonRowColumn556.rows_assocCAB HexagonRowColumn556.cols_right2)) ((2 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem rightFinal5_case_5_6_row_2_3_0 : (((-1 : ℤ) ^ (rightScaleBit 5 5 6).val * positiveScale (rightScaleExponent 5 5 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 6 5 : ℤ)) • HexagonAtoms556.outerLeftABC) ((2 : Fin 4), (3 : Fin 4), (0 : Fin 1)) = (negativeScale (rightScaleExponent 5 5 6) • (rowColumnMul HexagonRowColumn556.rows_assocCAB HexagonRowColumn556.cols_right2)) ((2 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem rightFinal5_case_5_6_row_3_0_0 : (((-1 : ℤ) ^ (rightScaleBit 5 5 6).val * positiveScale (rightScaleExponent 5 5 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 6 5 : ℤ)) • HexagonAtoms556.outerLeftABC) ((3 : Fin 4), (0 : Fin 4), (0 : Fin 1)) = (negativeScale (rightScaleExponent 5 5 6) • (rowColumnMul HexagonRowColumn556.rows_assocCAB HexagonRowColumn556.cols_right2)) ((3 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem rightFinal5_case_5_6_row_3_1_0 : (((-1 : ℤ) ^ (rightScaleBit 5 5 6).val * positiveScale (rightScaleExponent 5 5 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 6 5 : ℤ)) • HexagonAtoms556.outerLeftABC) ((3 : Fin 4), (1 : Fin 4), (0 : Fin 1)) = (negativeScale (rightScaleExponent 5 5 6) • (rowColumnMul HexagonRowColumn556.rows_assocCAB HexagonRowColumn556.cols_right2)) ((3 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem rightFinal5_case_5_6_row_3_2_0 : (((-1 : ℤ) ^ (rightScaleBit 5 5 6).val * positiveScale (rightScaleExponent 5 5 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 6 5 : ℤ)) • HexagonAtoms556.outerLeftABC) ((3 : Fin 4), (2 : Fin 4), (0 : Fin 1)) = (negativeScale (rightScaleExponent 5 5 6) • (rowColumnMul HexagonRowColumn556.rows_assocCAB HexagonRowColumn556.cols_right2)) ((3 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem rightFinal5_case_5_6_row_3_3_0 : (((-1 : ℤ) ^ (rightScaleBit 5 5 6).val * positiveScale (rightScaleExponent 5 5 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 6 5 : ℤ)) • HexagonAtoms556.outerLeftABC) ((3 : Fin 4), (3 : Fin 4), (0 : Fin 1)) = (negativeScale (rightScaleExponent 5 5 6) • (rowColumnMul HexagonRowColumn556.rows_assocCAB HexagonRowColumn556.cols_right2)) ((3 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 1)
  decide +kernel

private theorem rightFinal5_case_5_6_checked : ((-1 : ℤ) ^ (rightScaleBit 5 5 6).val * positiveScale (rightScaleExponent 5 5 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 6 5 : ℤ)) • HexagonAtoms556.outerLeftABC = negativeScale (rightScaleExponent 5 5 6) • (rowColumnMul HexagonRowColumn556.rows_assocCAB HexagonRowColumn556.cols_right2) := by
  funext r
  fin_cases r
  · exact rightFinal5_case_5_6_row_0_0_0
  · exact rightFinal5_case_5_6_row_0_1_0
  · exact rightFinal5_case_5_6_row_0_2_0
  · exact rightFinal5_case_5_6_row_0_3_0
  · exact rightFinal5_case_5_6_row_1_0_0
  · exact rightFinal5_case_5_6_row_1_1_0
  · exact rightFinal5_case_5_6_row_1_2_0
  · exact rightFinal5_case_5_6_row_1_3_0
  · exact rightFinal5_case_5_6_row_2_0_0
  · exact rightFinal5_case_5_6_row_2_1_0
  · exact rightFinal5_case_5_6_row_2_2_0
  · exact rightFinal5_case_5_6_row_2_3_0
  · exact rightFinal5_case_5_6_row_3_0_0
  · exact rightFinal5_case_5_6_row_3_1_0
  · exact rightFinal5_case_5_6_row_3_2_0
  · exact rightFinal5_case_5_6_row_3_3_0

set_option backward.isDefEq.respectTransparency false in
theorem rightFinal5_case_5_6 : ((-1 : ℤ) ^ (rightScaleBit 5 5 6).val * positiveScale (rightScaleExponent 5 5 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 6 5 : ℤ)) • outerLeftZ 5 5 6 = negativeScale (rightScaleExponent 5 5 6) • (associatorZ 6 5 5 * right2Middle5 5 6) := by
  simpa only [HexagonAtoms556.assocABC_eq,
    HexagonAtoms556.outerABC_eq,
    HexagonAtoms556.assocBAC_eq,
    HexagonAtoms556.innerABC_eq,
    HexagonAtoms556.innerRightABC_eq,
    HexagonAtoms556.inverseACB_eq,
    HexagonAtoms556.innerACB_eq,
    HexagonAtoms556.assocBCA_eq,
    HexagonAtoms556.innerRightBAC_eq,
    HexagonAtoms556.assocCAB_eq,
    HexagonAtoms556.outerLeftABC_eq,
    HexagonRowColumn556.assocBAC_alias,
    HexagonRowColumn556.innerRightBAC_alias,
    HexagonRowColumn556.product0_eq,
    HexagonRowColumn556.product1_eq,
    HexagonRowColumn556.product2_eq,
    HexagonRowColumn556.product3_eq,
    HexagonRowColumn556.product4_eq,
    HexagonRowColumn556.product5_eq,
    HexagonRowColumn556.product6_eq,
    HexagonRowColumn556.product7_eq] using rightFinal5_case_5_6_checked

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonCases5
