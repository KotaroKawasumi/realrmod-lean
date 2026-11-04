import RMod.BrundanEllis.StackingReferenceHexagonMiddle5
import RMod.BrundanEllis.StackingReferenceSparseMatrixCheck
import RMod.BrundanEllis.StackingReferenceHexagonAtoms567
import RMod.BrundanEllis.StackingReferenceHexagonRowColumn567

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

private theorem left0Middle5_eq_case_6_7_row_0_0_0 : (left0Middle5 6 7) ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn567.rows_outerABC HexagonRowColumn567.cols_assocABC) ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_6_7_row_0_0_1 : (left0Middle5 6 7) ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn567.rows_outerABC HexagonRowColumn567.cols_assocABC) ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_6_7_row_0_0_2 : (left0Middle5 6 7) ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn567.rows_outerABC HexagonRowColumn567.cols_assocABC) ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_6_7_row_0_0_3 : (left0Middle5 6 7) ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn567.rows_outerABC HexagonRowColumn567.cols_assocABC) ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_6_7_row_0_1_0 : (left0Middle5 6 7) ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn567.rows_outerABC HexagonRowColumn567.cols_assocABC) ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_6_7_row_0_1_1 : (left0Middle5 6 7) ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn567.rows_outerABC HexagonRowColumn567.cols_assocABC) ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_6_7_row_0_1_2 : (left0Middle5 6 7) ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn567.rows_outerABC HexagonRowColumn567.cols_assocABC) ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_6_7_row_0_1_3 : (left0Middle5 6 7) ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn567.rows_outerABC HexagonRowColumn567.cols_assocABC) ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_6_7_row_0_2_0 : (left0Middle5 6 7) ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn567.rows_outerABC HexagonRowColumn567.cols_assocABC) ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_6_7_row_0_2_1 : (left0Middle5 6 7) ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn567.rows_outerABC HexagonRowColumn567.cols_assocABC) ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_6_7_row_0_2_2 : (left0Middle5 6 7) ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn567.rows_outerABC HexagonRowColumn567.cols_assocABC) ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_6_7_row_0_2_3 : (left0Middle5 6 7) ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn567.rows_outerABC HexagonRowColumn567.cols_assocABC) ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_6_7_row_0_3_0 : (left0Middle5 6 7) ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn567.rows_outerABC HexagonRowColumn567.cols_assocABC) ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_6_7_row_0_3_1 : (left0Middle5 6 7) ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn567.rows_outerABC HexagonRowColumn567.cols_assocABC) ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_6_7_row_0_3_2 : (left0Middle5 6 7) ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn567.rows_outerABC HexagonRowColumn567.cols_assocABC) ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_6_7_row_0_3_3 : (left0Middle5 6 7) ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn567.rows_outerABC HexagonRowColumn567.cols_assocABC) ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_6_7_checked : left0Middle5 6 7 = rowColumnMul HexagonRowColumn567.rows_outerABC HexagonRowColumn567.cols_assocABC := by
  funext r
  fin_cases r
  · exact left0Middle5_eq_case_6_7_row_0_0_0
  · exact left0Middle5_eq_case_6_7_row_0_0_1
  · exact left0Middle5_eq_case_6_7_row_0_0_2
  · exact left0Middle5_eq_case_6_7_row_0_0_3
  · exact left0Middle5_eq_case_6_7_row_0_1_0
  · exact left0Middle5_eq_case_6_7_row_0_1_1
  · exact left0Middle5_eq_case_6_7_row_0_1_2
  · exact left0Middle5_eq_case_6_7_row_0_1_3
  · exact left0Middle5_eq_case_6_7_row_0_2_0
  · exact left0Middle5_eq_case_6_7_row_0_2_1
  · exact left0Middle5_eq_case_6_7_row_0_2_2
  · exact left0Middle5_eq_case_6_7_row_0_2_3
  · exact left0Middle5_eq_case_6_7_row_0_3_0
  · exact left0Middle5_eq_case_6_7_row_0_3_1
  · exact left0Middle5_eq_case_6_7_row_0_3_2
  · exact left0Middle5_eq_case_6_7_row_0_3_3

set_option backward.isDefEq.respectTransparency false in
theorem left0Middle5_eq_case_6_7 : left0Middle5 6 7 = outerRightZ 5 6 7 * associatorZ 5 6 7 := by
  simpa only [HexagonAtoms567.assocABC_eq,
    HexagonAtoms567.outerABC_eq,
    HexagonAtoms567.assocBAC_eq,
    HexagonAtoms567.innerABC_eq,
    HexagonAtoms567.innerRightABC_eq,
    HexagonAtoms567.inverseACB_eq,
    HexagonAtoms567.innerACB_eq,
    HexagonAtoms567.assocBCA_eq,
    HexagonAtoms567.innerRightBAC_eq,
    HexagonAtoms567.assocCAB_eq,
    HexagonAtoms567.outerLeftABC_eq,
    HexagonRowColumn567.product0_eq,
    HexagonRowColumn567.product1_eq,
    HexagonRowColumn567.product2_eq,
    HexagonRowColumn567.product3_eq,
    HexagonRowColumn567.product4_eq,
    HexagonRowColumn567.product5_eq,
    HexagonRowColumn567.product6_eq,
    HexagonRowColumn567.product7_eq] using left0Middle5_eq_case_6_7_checked

private theorem left1Middle5_eq_case_6_7_row_0_0_0 : (left1Middle5 6 7) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms567.assocBAC) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_6_7_row_0_0_1 : (left1Middle5 6 7) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms567.assocBAC) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_6_7_row_0_0_2 : (left1Middle5 6 7) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms567.assocBAC) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_6_7_row_0_0_3 : (left1Middle5 6 7) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms567.assocBAC) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_6_7_row_0_1_0 : (left1Middle5 6 7) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms567.assocBAC) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_6_7_row_0_1_1 : (left1Middle5 6 7) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms567.assocBAC) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_6_7_row_0_1_2 : (left1Middle5 6 7) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms567.assocBAC) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_6_7_row_0_1_3 : (left1Middle5 6 7) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms567.assocBAC) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_6_7_row_1_0_0 : (left1Middle5 6 7) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms567.assocBAC) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_6_7_row_1_0_1 : (left1Middle5 6 7) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms567.assocBAC) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_6_7_row_1_0_2 : (left1Middle5 6 7) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms567.assocBAC) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_6_7_row_1_0_3 : (left1Middle5 6 7) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms567.assocBAC) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_6_7_row_1_1_0 : (left1Middle5 6 7) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms567.assocBAC) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_6_7_row_1_1_1 : (left1Middle5 6 7) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms567.assocBAC) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_6_7_row_1_1_2 : (left1Middle5 6 7) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms567.assocBAC) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_6_7_row_1_1_3 : (left1Middle5 6 7) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms567.assocBAC) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_6_7_checked : left1Middle5 6 7 = HexagonAtoms567.assocBAC := by
  funext r
  fin_cases r
  · exact left1Middle5_eq_case_6_7_row_0_0_0
  · exact left1Middle5_eq_case_6_7_row_0_0_1
  · exact left1Middle5_eq_case_6_7_row_0_0_2
  · exact left1Middle5_eq_case_6_7_row_0_0_3
  · exact left1Middle5_eq_case_6_7_row_0_1_0
  · exact left1Middle5_eq_case_6_7_row_0_1_1
  · exact left1Middle5_eq_case_6_7_row_0_1_2
  · exact left1Middle5_eq_case_6_7_row_0_1_3
  · exact left1Middle5_eq_case_6_7_row_1_0_0
  · exact left1Middle5_eq_case_6_7_row_1_0_1
  · exact left1Middle5_eq_case_6_7_row_1_0_2
  · exact left1Middle5_eq_case_6_7_row_1_0_3
  · exact left1Middle5_eq_case_6_7_row_1_1_0
  · exact left1Middle5_eq_case_6_7_row_1_1_1
  · exact left1Middle5_eq_case_6_7_row_1_1_2
  · exact left1Middle5_eq_case_6_7_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem left1Middle5_eq_case_6_7 : left1Middle5 6 7 = associatorZ 6 5 7 * innerLeftZ 5 6 7 := by
  simpa only [HexagonAtoms567.assocABC_eq,
    HexagonAtoms567.outerABC_eq,
    HexagonAtoms567.assocBAC_eq,
    HexagonAtoms567.innerABC_eq,
    HexagonAtoms567.innerRightABC_eq,
    HexagonAtoms567.inverseACB_eq,
    HexagonAtoms567.innerACB_eq,
    HexagonAtoms567.assocBCA_eq,
    HexagonAtoms567.innerRightBAC_eq,
    HexagonAtoms567.assocCAB_eq,
    HexagonAtoms567.outerLeftABC_eq,
    HexagonRowColumn567.product0_eq,
    HexagonRowColumn567.product1_eq,
    HexagonRowColumn567.product2_eq,
    HexagonRowColumn567.product3_eq,
    HexagonRowColumn567.product4_eq,
    HexagonRowColumn567.product5_eq,
    HexagonRowColumn567.product6_eq,
    HexagonRowColumn567.product7_eq] using left1Middle5_eq_case_6_7_checked

private theorem right0Middle5_eq_case_6_7_row_0_0_0 : (right0Middle5 6 7) ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn567.rows_innerRightABC HexagonRowColumn567.cols_assocABC) ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_6_7_row_0_0_1 : (right0Middle5 6 7) ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn567.rows_innerRightABC HexagonRowColumn567.cols_assocABC) ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_6_7_row_0_0_2 : (right0Middle5 6 7) ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn567.rows_innerRightABC HexagonRowColumn567.cols_assocABC) ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_6_7_row_0_0_3 : (right0Middle5 6 7) ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn567.rows_innerRightABC HexagonRowColumn567.cols_assocABC) ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_6_7_row_0_1_0 : (right0Middle5 6 7) ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn567.rows_innerRightABC HexagonRowColumn567.cols_assocABC) ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_6_7_row_0_1_1 : (right0Middle5 6 7) ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn567.rows_innerRightABC HexagonRowColumn567.cols_assocABC) ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_6_7_row_0_1_2 : (right0Middle5 6 7) ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn567.rows_innerRightABC HexagonRowColumn567.cols_assocABC) ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_6_7_row_0_1_3 : (right0Middle5 6 7) ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn567.rows_innerRightABC HexagonRowColumn567.cols_assocABC) ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_6_7_row_0_2_0 : (right0Middle5 6 7) ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn567.rows_innerRightABC HexagonRowColumn567.cols_assocABC) ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_6_7_row_0_2_1 : (right0Middle5 6 7) ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn567.rows_innerRightABC HexagonRowColumn567.cols_assocABC) ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_6_7_row_0_2_2 : (right0Middle5 6 7) ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn567.rows_innerRightABC HexagonRowColumn567.cols_assocABC) ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_6_7_row_0_2_3 : (right0Middle5 6 7) ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn567.rows_innerRightABC HexagonRowColumn567.cols_assocABC) ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_6_7_row_0_3_0 : (right0Middle5 6 7) ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn567.rows_innerRightABC HexagonRowColumn567.cols_assocABC) ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_6_7_row_0_3_1 : (right0Middle5 6 7) ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn567.rows_innerRightABC HexagonRowColumn567.cols_assocABC) ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_6_7_row_0_3_2 : (right0Middle5 6 7) ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn567.rows_innerRightABC HexagonRowColumn567.cols_assocABC) ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_6_7_row_0_3_3 : (right0Middle5 6 7) ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn567.rows_innerRightABC HexagonRowColumn567.cols_assocABC) ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_6_7_checked : right0Middle5 6 7 = rowColumnMul HexagonRowColumn567.rows_innerRightABC HexagonRowColumn567.cols_assocABC := by
  funext r
  fin_cases r
  · exact right0Middle5_eq_case_6_7_row_0_0_0
  · exact right0Middle5_eq_case_6_7_row_0_0_1
  · exact right0Middle5_eq_case_6_7_row_0_0_2
  · exact right0Middle5_eq_case_6_7_row_0_0_3
  · exact right0Middle5_eq_case_6_7_row_0_1_0
  · exact right0Middle5_eq_case_6_7_row_0_1_1
  · exact right0Middle5_eq_case_6_7_row_0_1_2
  · exact right0Middle5_eq_case_6_7_row_0_1_3
  · exact right0Middle5_eq_case_6_7_row_0_2_0
  · exact right0Middle5_eq_case_6_7_row_0_2_1
  · exact right0Middle5_eq_case_6_7_row_0_2_2
  · exact right0Middle5_eq_case_6_7_row_0_2_3
  · exact right0Middle5_eq_case_6_7_row_0_3_0
  · exact right0Middle5_eq_case_6_7_row_0_3_1
  · exact right0Middle5_eq_case_6_7_row_0_3_2
  · exact right0Middle5_eq_case_6_7_row_0_3_3

set_option backward.isDefEq.respectTransparency false in
theorem right0Middle5_eq_case_6_7 : right0Middle5 6 7 = innerRightZ 5 6 7 * associatorZ 5 6 7 := by
  simpa only [HexagonAtoms567.assocABC_eq,
    HexagonAtoms567.outerABC_eq,
    HexagonAtoms567.assocBAC_eq,
    HexagonAtoms567.innerABC_eq,
    HexagonAtoms567.innerRightABC_eq,
    HexagonAtoms567.inverseACB_eq,
    HexagonAtoms567.innerACB_eq,
    HexagonAtoms567.assocBCA_eq,
    HexagonAtoms567.innerRightBAC_eq,
    HexagonAtoms567.assocCAB_eq,
    HexagonAtoms567.outerLeftABC_eq,
    HexagonRowColumn567.product0_eq,
    HexagonRowColumn567.product1_eq,
    HexagonRowColumn567.product2_eq,
    HexagonRowColumn567.product3_eq,
    HexagonRowColumn567.product4_eq,
    HexagonRowColumn567.product5_eq,
    HexagonRowColumn567.product6_eq,
    HexagonRowColumn567.product7_eq] using right0Middle5_eq_case_6_7_checked

private theorem right1Middle5_eq_case_6_7_row_0_0_0 : (right1Middle5 6 7) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn567.rows_inverseACB HexagonRowColumn567.cols_right0) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_6_7_row_0_0_1 : (right1Middle5 6 7) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn567.rows_inverseACB HexagonRowColumn567.cols_right0) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_6_7_row_0_0_2 : (right1Middle5 6 7) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn567.rows_inverseACB HexagonRowColumn567.cols_right0) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_6_7_row_0_0_3 : (right1Middle5 6 7) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn567.rows_inverseACB HexagonRowColumn567.cols_right0) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_6_7_row_0_1_0 : (right1Middle5 6 7) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn567.rows_inverseACB HexagonRowColumn567.cols_right0) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_6_7_row_0_1_1 : (right1Middle5 6 7) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn567.rows_inverseACB HexagonRowColumn567.cols_right0) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_6_7_row_0_1_2 : (right1Middle5 6 7) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn567.rows_inverseACB HexagonRowColumn567.cols_right0) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_6_7_row_0_1_3 : (right1Middle5 6 7) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn567.rows_inverseACB HexagonRowColumn567.cols_right0) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_6_7_row_1_0_0 : (right1Middle5 6 7) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn567.rows_inverseACB HexagonRowColumn567.cols_right0) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_6_7_row_1_0_1 : (right1Middle5 6 7) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn567.rows_inverseACB HexagonRowColumn567.cols_right0) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_6_7_row_1_0_2 : (right1Middle5 6 7) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn567.rows_inverseACB HexagonRowColumn567.cols_right0) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_6_7_row_1_0_3 : (right1Middle5 6 7) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn567.rows_inverseACB HexagonRowColumn567.cols_right0) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_6_7_row_1_1_0 : (right1Middle5 6 7) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn567.rows_inverseACB HexagonRowColumn567.cols_right0) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_6_7_row_1_1_1 : (right1Middle5 6 7) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn567.rows_inverseACB HexagonRowColumn567.cols_right0) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_6_7_row_1_1_2 : (right1Middle5 6 7) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn567.rows_inverseACB HexagonRowColumn567.cols_right0) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_6_7_row_1_1_3 : (right1Middle5 6 7) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn567.rows_inverseACB HexagonRowColumn567.cols_right0) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_6_7_checked : right1Middle5 6 7 = rowColumnMul HexagonRowColumn567.rows_inverseACB HexagonRowColumn567.cols_right0 := by
  funext r
  fin_cases r
  · exact right1Middle5_eq_case_6_7_row_0_0_0
  · exact right1Middle5_eq_case_6_7_row_0_0_1
  · exact right1Middle5_eq_case_6_7_row_0_0_2
  · exact right1Middle5_eq_case_6_7_row_0_0_3
  · exact right1Middle5_eq_case_6_7_row_0_1_0
  · exact right1Middle5_eq_case_6_7_row_0_1_1
  · exact right1Middle5_eq_case_6_7_row_0_1_2
  · exact right1Middle5_eq_case_6_7_row_0_1_3
  · exact right1Middle5_eq_case_6_7_row_1_0_0
  · exact right1Middle5_eq_case_6_7_row_1_0_1
  · exact right1Middle5_eq_case_6_7_row_1_0_2
  · exact right1Middle5_eq_case_6_7_row_1_0_3
  · exact right1Middle5_eq_case_6_7_row_1_1_0
  · exact right1Middle5_eq_case_6_7_row_1_1_1
  · exact right1Middle5_eq_case_6_7_row_1_1_2
  · exact right1Middle5_eq_case_6_7_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem right1Middle5_eq_case_6_7 : right1Middle5 6 7 = associatorInverseZ 5 7 6 * right0Middle5 6 7 := by
  simpa only [HexagonAtoms567.assocABC_eq,
    HexagonAtoms567.outerABC_eq,
    HexagonAtoms567.assocBAC_eq,
    HexagonAtoms567.innerABC_eq,
    HexagonAtoms567.innerRightABC_eq,
    HexagonAtoms567.inverseACB_eq,
    HexagonAtoms567.innerACB_eq,
    HexagonAtoms567.assocBCA_eq,
    HexagonAtoms567.innerRightBAC_eq,
    HexagonAtoms567.assocCAB_eq,
    HexagonAtoms567.outerLeftABC_eq,
    HexagonRowColumn567.product0_eq,
    HexagonRowColumn567.product1_eq,
    HexagonRowColumn567.product2_eq,
    HexagonRowColumn567.product3_eq,
    HexagonRowColumn567.product4_eq,
    HexagonRowColumn567.product5_eq,
    HexagonRowColumn567.product6_eq,
    HexagonRowColumn567.product7_eq] using right1Middle5_eq_case_6_7_checked

private theorem right2Middle5_eq_case_6_7_row_0_0_0 : (right2Middle5 6 7) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (right1Middle5 6 7) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_6_7_row_0_0_1 : (right2Middle5 6 7) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (right1Middle5 6 7) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_6_7_row_0_0_2 : (right2Middle5 6 7) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (right1Middle5 6 7) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_6_7_row_0_0_3 : (right2Middle5 6 7) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (right1Middle5 6 7) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_6_7_row_0_1_0 : (right2Middle5 6 7) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (right1Middle5 6 7) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_6_7_row_0_1_1 : (right2Middle5 6 7) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (right1Middle5 6 7) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_6_7_row_0_1_2 : (right2Middle5 6 7) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (right1Middle5 6 7) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_6_7_row_0_1_3 : (right2Middle5 6 7) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (right1Middle5 6 7) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_6_7_row_1_0_0 : (right2Middle5 6 7) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (right1Middle5 6 7) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_6_7_row_1_0_1 : (right2Middle5 6 7) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (right1Middle5 6 7) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_6_7_row_1_0_2 : (right2Middle5 6 7) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (right1Middle5 6 7) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_6_7_row_1_0_3 : (right2Middle5 6 7) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (right1Middle5 6 7) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_6_7_row_1_1_0 : (right2Middle5 6 7) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (right1Middle5 6 7) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_6_7_row_1_1_1 : (right2Middle5 6 7) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (right1Middle5 6 7) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_6_7_row_1_1_2 : (right2Middle5 6 7) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (right1Middle5 6 7) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_6_7_row_1_1_3 : (right2Middle5 6 7) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (right1Middle5 6 7) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_6_7_checked : right2Middle5 6 7 = right1Middle5 6 7 := by
  funext r
  fin_cases r
  · exact right2Middle5_eq_case_6_7_row_0_0_0
  · exact right2Middle5_eq_case_6_7_row_0_0_1
  · exact right2Middle5_eq_case_6_7_row_0_0_2
  · exact right2Middle5_eq_case_6_7_row_0_0_3
  · exact right2Middle5_eq_case_6_7_row_0_1_0
  · exact right2Middle5_eq_case_6_7_row_0_1_1
  · exact right2Middle5_eq_case_6_7_row_0_1_2
  · exact right2Middle5_eq_case_6_7_row_0_1_3
  · exact right2Middle5_eq_case_6_7_row_1_0_0
  · exact right2Middle5_eq_case_6_7_row_1_0_1
  · exact right2Middle5_eq_case_6_7_row_1_0_2
  · exact right2Middle5_eq_case_6_7_row_1_0_3
  · exact right2Middle5_eq_case_6_7_row_1_1_0
  · exact right2Middle5_eq_case_6_7_row_1_1_1
  · exact right2Middle5_eq_case_6_7_row_1_1_2
  · exact right2Middle5_eq_case_6_7_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem right2Middle5_eq_case_6_7 : right2Middle5 6 7 = innerLeftZ 5 7 6 * right1Middle5 6 7 := by
  simpa only [HexagonAtoms567.assocABC_eq,
    HexagonAtoms567.outerABC_eq,
    HexagonAtoms567.assocBAC_eq,
    HexagonAtoms567.innerABC_eq,
    HexagonAtoms567.innerRightABC_eq,
    HexagonAtoms567.inverseACB_eq,
    HexagonAtoms567.innerACB_eq,
    HexagonAtoms567.assocBCA_eq,
    HexagonAtoms567.innerRightBAC_eq,
    HexagonAtoms567.assocCAB_eq,
    HexagonAtoms567.outerLeftABC_eq,
    HexagonRowColumn567.product0_eq,
    HexagonRowColumn567.product1_eq,
    HexagonRowColumn567.product2_eq,
    HexagonRowColumn567.product3_eq,
    HexagonRowColumn567.product4_eq,
    HexagonRowColumn567.product5_eq,
    HexagonRowColumn567.product6_eq,
    HexagonRowColumn567.product7_eq] using right2Middle5_eq_case_6_7_checked

private theorem leftFinal5_case_6_7_row_0_0_0 : (((-1 : ℤ) ^ (leftScaleBit 5 6 7).val * positiveScale (leftScaleExponent 5 6 7)) •
      (rowColumnMul HexagonRowColumn567.rows_assocBCA HexagonRowColumn567.cols_left0)) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 5 6 7) • (left1Middle5 6 7)) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_6_7_row_0_0_1 : (((-1 : ℤ) ^ (leftScaleBit 5 6 7).val * positiveScale (leftScaleExponent 5 6 7)) •
      (rowColumnMul HexagonRowColumn567.rows_assocBCA HexagonRowColumn567.cols_left0)) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 5 6 7) • (left1Middle5 6 7)) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_6_7_row_0_0_2 : (((-1 : ℤ) ^ (leftScaleBit 5 6 7).val * positiveScale (leftScaleExponent 5 6 7)) •
      (rowColumnMul HexagonRowColumn567.rows_assocBCA HexagonRowColumn567.cols_left0)) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 5 6 7) • (left1Middle5 6 7)) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_6_7_row_0_0_3 : (((-1 : ℤ) ^ (leftScaleBit 5 6 7).val * positiveScale (leftScaleExponent 5 6 7)) •
      (rowColumnMul HexagonRowColumn567.rows_assocBCA HexagonRowColumn567.cols_left0)) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 5 6 7) • (left1Middle5 6 7)) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_6_7_row_0_1_0 : (((-1 : ℤ) ^ (leftScaleBit 5 6 7).val * positiveScale (leftScaleExponent 5 6 7)) •
      (rowColumnMul HexagonRowColumn567.rows_assocBCA HexagonRowColumn567.cols_left0)) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 5 6 7) • (left1Middle5 6 7)) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_6_7_row_0_1_1 : (((-1 : ℤ) ^ (leftScaleBit 5 6 7).val * positiveScale (leftScaleExponent 5 6 7)) •
      (rowColumnMul HexagonRowColumn567.rows_assocBCA HexagonRowColumn567.cols_left0)) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 5 6 7) • (left1Middle5 6 7)) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_6_7_row_0_1_2 : (((-1 : ℤ) ^ (leftScaleBit 5 6 7).val * positiveScale (leftScaleExponent 5 6 7)) •
      (rowColumnMul HexagonRowColumn567.rows_assocBCA HexagonRowColumn567.cols_left0)) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 5 6 7) • (left1Middle5 6 7)) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_6_7_row_0_1_3 : (((-1 : ℤ) ^ (leftScaleBit 5 6 7).val * positiveScale (leftScaleExponent 5 6 7)) •
      (rowColumnMul HexagonRowColumn567.rows_assocBCA HexagonRowColumn567.cols_left0)) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 5 6 7) • (left1Middle5 6 7)) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_6_7_row_1_0_0 : (((-1 : ℤ) ^ (leftScaleBit 5 6 7).val * positiveScale (leftScaleExponent 5 6 7)) •
      (rowColumnMul HexagonRowColumn567.rows_assocBCA HexagonRowColumn567.cols_left0)) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 5 6 7) • (left1Middle5 6 7)) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_6_7_row_1_0_1 : (((-1 : ℤ) ^ (leftScaleBit 5 6 7).val * positiveScale (leftScaleExponent 5 6 7)) •
      (rowColumnMul HexagonRowColumn567.rows_assocBCA HexagonRowColumn567.cols_left0)) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 5 6 7) • (left1Middle5 6 7)) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_6_7_row_1_0_2 : (((-1 : ℤ) ^ (leftScaleBit 5 6 7).val * positiveScale (leftScaleExponent 5 6 7)) •
      (rowColumnMul HexagonRowColumn567.rows_assocBCA HexagonRowColumn567.cols_left0)) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 5 6 7) • (left1Middle5 6 7)) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_6_7_row_1_0_3 : (((-1 : ℤ) ^ (leftScaleBit 5 6 7).val * positiveScale (leftScaleExponent 5 6 7)) •
      (rowColumnMul HexagonRowColumn567.rows_assocBCA HexagonRowColumn567.cols_left0)) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 5 6 7) • (left1Middle5 6 7)) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_6_7_row_1_1_0 : (((-1 : ℤ) ^ (leftScaleBit 5 6 7).val * positiveScale (leftScaleExponent 5 6 7)) •
      (rowColumnMul HexagonRowColumn567.rows_assocBCA HexagonRowColumn567.cols_left0)) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 5 6 7) • (left1Middle5 6 7)) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_6_7_row_1_1_1 : (((-1 : ℤ) ^ (leftScaleBit 5 6 7).val * positiveScale (leftScaleExponent 5 6 7)) •
      (rowColumnMul HexagonRowColumn567.rows_assocBCA HexagonRowColumn567.cols_left0)) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 5 6 7) • (left1Middle5 6 7)) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_6_7_row_1_1_2 : (((-1 : ℤ) ^ (leftScaleBit 5 6 7).val * positiveScale (leftScaleExponent 5 6 7)) •
      (rowColumnMul HexagonRowColumn567.rows_assocBCA HexagonRowColumn567.cols_left0)) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 5 6 7) • (left1Middle5 6 7)) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_6_7_row_1_1_3 : (((-1 : ℤ) ^ (leftScaleBit 5 6 7).val * positiveScale (leftScaleExponent 5 6 7)) •
      (rowColumnMul HexagonRowColumn567.rows_assocBCA HexagonRowColumn567.cols_left0)) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 5 6 7) • (left1Middle5 6 7)) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_6_7_checked : ((-1 : ℤ) ^ (leftScaleBit 5 6 7).val * positiveScale (leftScaleExponent 5 6 7)) •
      (rowColumnMul HexagonRowColumn567.rows_assocBCA HexagonRowColumn567.cols_left0) = negativeScale (leftScaleExponent 5 6 7) • (left1Middle5 6 7) := by
  funext r
  fin_cases r
  · exact leftFinal5_case_6_7_row_0_0_0
  · exact leftFinal5_case_6_7_row_0_0_1
  · exact leftFinal5_case_6_7_row_0_0_2
  · exact leftFinal5_case_6_7_row_0_0_3
  · exact leftFinal5_case_6_7_row_0_1_0
  · exact leftFinal5_case_6_7_row_0_1_1
  · exact leftFinal5_case_6_7_row_0_1_2
  · exact leftFinal5_case_6_7_row_0_1_3
  · exact leftFinal5_case_6_7_row_1_0_0
  · exact leftFinal5_case_6_7_row_1_0_1
  · exact leftFinal5_case_6_7_row_1_0_2
  · exact leftFinal5_case_6_7_row_1_0_3
  · exact leftFinal5_case_6_7_row_1_1_0
  · exact leftFinal5_case_6_7_row_1_1_1
  · exact leftFinal5_case_6_7_row_1_1_2
  · exact leftFinal5_case_6_7_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem leftFinal5_case_6_7 : ((-1 : ℤ) ^ (leftScaleBit 5 6 7).val * positiveScale (leftScaleExponent 5 6 7)) •
      (associatorZ 6 7 5 * left0Middle5 6 7) = negativeScale (leftScaleExponent 5 6 7) • (innerRightZ 6 5 7 * left1Middle5 6 7) := by
  simpa only [HexagonAtoms567.assocABC_eq,
    HexagonAtoms567.outerABC_eq,
    HexagonAtoms567.assocBAC_eq,
    HexagonAtoms567.innerABC_eq,
    HexagonAtoms567.innerRightABC_eq,
    HexagonAtoms567.inverseACB_eq,
    HexagonAtoms567.innerACB_eq,
    HexagonAtoms567.assocBCA_eq,
    HexagonAtoms567.innerRightBAC_eq,
    HexagonAtoms567.assocCAB_eq,
    HexagonAtoms567.outerLeftABC_eq,
    HexagonRowColumn567.product0_eq,
    HexagonRowColumn567.product1_eq,
    HexagonRowColumn567.product2_eq,
    HexagonRowColumn567.product3_eq,
    HexagonRowColumn567.product4_eq,
    HexagonRowColumn567.product5_eq,
    HexagonRowColumn567.product6_eq,
    HexagonRowColumn567.product7_eq] using leftFinal5_case_6_7_checked

private theorem rightFinal5_case_6_7_row_0_0_0 : (((-1 : ℤ) ^ (rightScaleBit 5 6 7).val * positiveScale (rightScaleExponent 5 6 7) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 7 6 : ℤ)) • HexagonAtoms567.outerLeftABC) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 5 6 7) • (rowColumnMul HexagonRowColumn567.rows_assocCAB HexagonRowColumn567.cols_right2)) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_6_7_row_0_0_1 : (((-1 : ℤ) ^ (rightScaleBit 5 6 7).val * positiveScale (rightScaleExponent 5 6 7) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 7 6 : ℤ)) • HexagonAtoms567.outerLeftABC) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 5 6 7) • (rowColumnMul HexagonRowColumn567.rows_assocCAB HexagonRowColumn567.cols_right2)) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_6_7_row_0_0_2 : (((-1 : ℤ) ^ (rightScaleBit 5 6 7).val * positiveScale (rightScaleExponent 5 6 7) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 7 6 : ℤ)) • HexagonAtoms567.outerLeftABC) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 5 6 7) • (rowColumnMul HexagonRowColumn567.rows_assocCAB HexagonRowColumn567.cols_right2)) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_6_7_row_0_0_3 : (((-1 : ℤ) ^ (rightScaleBit 5 6 7).val * positiveScale (rightScaleExponent 5 6 7) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 7 6 : ℤ)) • HexagonAtoms567.outerLeftABC) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 5 6 7) • (rowColumnMul HexagonRowColumn567.rows_assocCAB HexagonRowColumn567.cols_right2)) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_6_7_row_0_1_0 : (((-1 : ℤ) ^ (rightScaleBit 5 6 7).val * positiveScale (rightScaleExponent 5 6 7) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 7 6 : ℤ)) • HexagonAtoms567.outerLeftABC) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 5 6 7) • (rowColumnMul HexagonRowColumn567.rows_assocCAB HexagonRowColumn567.cols_right2)) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_6_7_row_0_1_1 : (((-1 : ℤ) ^ (rightScaleBit 5 6 7).val * positiveScale (rightScaleExponent 5 6 7) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 7 6 : ℤ)) • HexagonAtoms567.outerLeftABC) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 5 6 7) • (rowColumnMul HexagonRowColumn567.rows_assocCAB HexagonRowColumn567.cols_right2)) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_6_7_row_0_1_2 : (((-1 : ℤ) ^ (rightScaleBit 5 6 7).val * positiveScale (rightScaleExponent 5 6 7) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 7 6 : ℤ)) • HexagonAtoms567.outerLeftABC) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 5 6 7) • (rowColumnMul HexagonRowColumn567.rows_assocCAB HexagonRowColumn567.cols_right2)) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_6_7_row_0_1_3 : (((-1 : ℤ) ^ (rightScaleBit 5 6 7).val * positiveScale (rightScaleExponent 5 6 7) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 7 6 : ℤ)) • HexagonAtoms567.outerLeftABC) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 5 6 7) • (rowColumnMul HexagonRowColumn567.rows_assocCAB HexagonRowColumn567.cols_right2)) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_6_7_row_1_0_0 : (((-1 : ℤ) ^ (rightScaleBit 5 6 7).val * positiveScale (rightScaleExponent 5 6 7) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 7 6 : ℤ)) • HexagonAtoms567.outerLeftABC) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 5 6 7) • (rowColumnMul HexagonRowColumn567.rows_assocCAB HexagonRowColumn567.cols_right2)) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_6_7_row_1_0_1 : (((-1 : ℤ) ^ (rightScaleBit 5 6 7).val * positiveScale (rightScaleExponent 5 6 7) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 7 6 : ℤ)) • HexagonAtoms567.outerLeftABC) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 5 6 7) • (rowColumnMul HexagonRowColumn567.rows_assocCAB HexagonRowColumn567.cols_right2)) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_6_7_row_1_0_2 : (((-1 : ℤ) ^ (rightScaleBit 5 6 7).val * positiveScale (rightScaleExponent 5 6 7) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 7 6 : ℤ)) • HexagonAtoms567.outerLeftABC) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 5 6 7) • (rowColumnMul HexagonRowColumn567.rows_assocCAB HexagonRowColumn567.cols_right2)) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_6_7_row_1_0_3 : (((-1 : ℤ) ^ (rightScaleBit 5 6 7).val * positiveScale (rightScaleExponent 5 6 7) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 7 6 : ℤ)) • HexagonAtoms567.outerLeftABC) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 5 6 7) • (rowColumnMul HexagonRowColumn567.rows_assocCAB HexagonRowColumn567.cols_right2)) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_6_7_row_1_1_0 : (((-1 : ℤ) ^ (rightScaleBit 5 6 7).val * positiveScale (rightScaleExponent 5 6 7) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 7 6 : ℤ)) • HexagonAtoms567.outerLeftABC) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 5 6 7) • (rowColumnMul HexagonRowColumn567.rows_assocCAB HexagonRowColumn567.cols_right2)) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_6_7_row_1_1_1 : (((-1 : ℤ) ^ (rightScaleBit 5 6 7).val * positiveScale (rightScaleExponent 5 6 7) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 7 6 : ℤ)) • HexagonAtoms567.outerLeftABC) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 5 6 7) • (rowColumnMul HexagonRowColumn567.rows_assocCAB HexagonRowColumn567.cols_right2)) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_6_7_row_1_1_2 : (((-1 : ℤ) ^ (rightScaleBit 5 6 7).val * positiveScale (rightScaleExponent 5 6 7) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 7 6 : ℤ)) • HexagonAtoms567.outerLeftABC) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 5 6 7) • (rowColumnMul HexagonRowColumn567.rows_assocCAB HexagonRowColumn567.cols_right2)) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_6_7_row_1_1_3 : (((-1 : ℤ) ^ (rightScaleBit 5 6 7).val * positiveScale (rightScaleExponent 5 6 7) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 7 6 : ℤ)) • HexagonAtoms567.outerLeftABC) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 5 6 7) • (rowColumnMul HexagonRowColumn567.rows_assocCAB HexagonRowColumn567.cols_right2)) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_6_7_checked : ((-1 : ℤ) ^ (rightScaleBit 5 6 7).val * positiveScale (rightScaleExponent 5 6 7) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 7 6 : ℤ)) • HexagonAtoms567.outerLeftABC = negativeScale (rightScaleExponent 5 6 7) • (rowColumnMul HexagonRowColumn567.rows_assocCAB HexagonRowColumn567.cols_right2) := by
  funext r
  fin_cases r
  · exact rightFinal5_case_6_7_row_0_0_0
  · exact rightFinal5_case_6_7_row_0_0_1
  · exact rightFinal5_case_6_7_row_0_0_2
  · exact rightFinal5_case_6_7_row_0_0_3
  · exact rightFinal5_case_6_7_row_0_1_0
  · exact rightFinal5_case_6_7_row_0_1_1
  · exact rightFinal5_case_6_7_row_0_1_2
  · exact rightFinal5_case_6_7_row_0_1_3
  · exact rightFinal5_case_6_7_row_1_0_0
  · exact rightFinal5_case_6_7_row_1_0_1
  · exact rightFinal5_case_6_7_row_1_0_2
  · exact rightFinal5_case_6_7_row_1_0_3
  · exact rightFinal5_case_6_7_row_1_1_0
  · exact rightFinal5_case_6_7_row_1_1_1
  · exact rightFinal5_case_6_7_row_1_1_2
  · exact rightFinal5_case_6_7_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem rightFinal5_case_6_7 : ((-1 : ℤ) ^ (rightScaleBit 5 6 7).val * positiveScale (rightScaleExponent 5 6 7) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 7 6 : ℤ)) • outerLeftZ 5 6 7 = negativeScale (rightScaleExponent 5 6 7) • (associatorZ 7 5 6 * right2Middle5 6 7) := by
  simpa only [HexagonAtoms567.assocABC_eq,
    HexagonAtoms567.outerABC_eq,
    HexagonAtoms567.assocBAC_eq,
    HexagonAtoms567.innerABC_eq,
    HexagonAtoms567.innerRightABC_eq,
    HexagonAtoms567.inverseACB_eq,
    HexagonAtoms567.innerACB_eq,
    HexagonAtoms567.assocBCA_eq,
    HexagonAtoms567.innerRightBAC_eq,
    HexagonAtoms567.assocCAB_eq,
    HexagonAtoms567.outerLeftABC_eq,
    HexagonRowColumn567.product0_eq,
    HexagonRowColumn567.product1_eq,
    HexagonRowColumn567.product2_eq,
    HexagonRowColumn567.product3_eq,
    HexagonRowColumn567.product4_eq,
    HexagonRowColumn567.product5_eq,
    HexagonRowColumn567.product6_eq,
    HexagonRowColumn567.product7_eq] using rightFinal5_case_6_7_checked

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonCases5
