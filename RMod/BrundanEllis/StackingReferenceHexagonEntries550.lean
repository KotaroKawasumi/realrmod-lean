import RMod.BrundanEllis.StackingReferenceHexagonMiddle5
import RMod.BrundanEllis.StackingReferenceSparseMatrixCheck
import RMod.BrundanEllis.StackingReferenceHexagonAtoms550
import RMod.BrundanEllis.StackingReferenceHexagonRowColumn550

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

private theorem left0Middle5_eq_case_5_0_row_0_0_0 : (left0Middle5 5 0) ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn550.rows_outerABC HexagonRowColumn550.cols_assocABC) ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_5_0_row_0_0_1 : (left0Middle5 5 0) ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn550.rows_outerABC HexagonRowColumn550.cols_assocABC) ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_5_0_row_0_0_2 : (left0Middle5 5 0) ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn550.rows_outerABC HexagonRowColumn550.cols_assocABC) ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_5_0_row_0_0_3 : (left0Middle5 5 0) ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn550.rows_outerABC HexagonRowColumn550.cols_assocABC) ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_5_0_row_0_1_0 : (left0Middle5 5 0) ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn550.rows_outerABC HexagonRowColumn550.cols_assocABC) ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_5_0_row_0_1_1 : (left0Middle5 5 0) ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn550.rows_outerABC HexagonRowColumn550.cols_assocABC) ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_5_0_row_0_1_2 : (left0Middle5 5 0) ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn550.rows_outerABC HexagonRowColumn550.cols_assocABC) ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_5_0_row_0_1_3 : (left0Middle5 5 0) ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn550.rows_outerABC HexagonRowColumn550.cols_assocABC) ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_5_0_row_0_2_0 : (left0Middle5 5 0) ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn550.rows_outerABC HexagonRowColumn550.cols_assocABC) ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_5_0_row_0_2_1 : (left0Middle5 5 0) ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn550.rows_outerABC HexagonRowColumn550.cols_assocABC) ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_5_0_row_0_2_2 : (left0Middle5 5 0) ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn550.rows_outerABC HexagonRowColumn550.cols_assocABC) ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_5_0_row_0_2_3 : (left0Middle5 5 0) ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn550.rows_outerABC HexagonRowColumn550.cols_assocABC) ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_5_0_row_0_3_0 : (left0Middle5 5 0) ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn550.rows_outerABC HexagonRowColumn550.cols_assocABC) ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_5_0_row_0_3_1 : (left0Middle5 5 0) ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn550.rows_outerABC HexagonRowColumn550.cols_assocABC) ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_5_0_row_0_3_2 : (left0Middle5 5 0) ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn550.rows_outerABC HexagonRowColumn550.cols_assocABC) ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_5_0_row_0_3_3 : (left0Middle5 5 0) ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn550.rows_outerABC HexagonRowColumn550.cols_assocABC) ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_5_0_checked : left0Middle5 5 0 = rowColumnMul HexagonRowColumn550.rows_outerABC HexagonRowColumn550.cols_assocABC := by
  funext r
  fin_cases r
  · exact left0Middle5_eq_case_5_0_row_0_0_0
  · exact left0Middle5_eq_case_5_0_row_0_0_1
  · exact left0Middle5_eq_case_5_0_row_0_0_2
  · exact left0Middle5_eq_case_5_0_row_0_0_3
  · exact left0Middle5_eq_case_5_0_row_0_1_0
  · exact left0Middle5_eq_case_5_0_row_0_1_1
  · exact left0Middle5_eq_case_5_0_row_0_1_2
  · exact left0Middle5_eq_case_5_0_row_0_1_3
  · exact left0Middle5_eq_case_5_0_row_0_2_0
  · exact left0Middle5_eq_case_5_0_row_0_2_1
  · exact left0Middle5_eq_case_5_0_row_0_2_2
  · exact left0Middle5_eq_case_5_0_row_0_2_3
  · exact left0Middle5_eq_case_5_0_row_0_3_0
  · exact left0Middle5_eq_case_5_0_row_0_3_1
  · exact left0Middle5_eq_case_5_0_row_0_3_2
  · exact left0Middle5_eq_case_5_0_row_0_3_3

set_option backward.isDefEq.respectTransparency false in
theorem left0Middle5_eq_case_5_0 : left0Middle5 5 0 = outerRightZ 5 5 0 * associatorZ 5 5 0 := by
  simpa only [HexagonAtoms550.assocABC_eq,
    HexagonAtoms550.outerABC_eq,
    HexagonAtoms550.assocBAC_eq,
    HexagonAtoms550.innerABC_eq,
    HexagonAtoms550.innerRightABC_eq,
    HexagonAtoms550.inverseACB_eq,
    HexagonAtoms550.innerACB_eq,
    HexagonAtoms550.assocBCA_eq,
    HexagonAtoms550.innerRightBAC_eq,
    HexagonAtoms550.assocCAB_eq,
    HexagonAtoms550.outerLeftABC_eq,
    HexagonRowColumn550.assocBAC_alias,
    HexagonRowColumn550.innerRightBAC_alias,
    HexagonRowColumn550.product0_eq,
    HexagonRowColumn550.product1_eq,
    HexagonRowColumn550.product2_eq,
    HexagonRowColumn550.product3_eq,
    HexagonRowColumn550.product4_eq,
    HexagonRowColumn550.product5_eq,
    HexagonRowColumn550.product6_eq,
    HexagonRowColumn550.product7_eq] using left0Middle5_eq_case_5_0_checked

private theorem left1Middle5_eq_case_5_0_row_0_0_0 : (left1Middle5 5 0) ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn550.rows_assocABC HexagonRowColumn550.cols_innerABC) ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_5_0_row_0_0_1 : (left1Middle5 5 0) ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn550.rows_assocABC HexagonRowColumn550.cols_innerABC) ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_5_0_row_0_0_2 : (left1Middle5 5 0) ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn550.rows_assocABC HexagonRowColumn550.cols_innerABC) ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_5_0_row_0_0_3 : (left1Middle5 5 0) ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn550.rows_assocABC HexagonRowColumn550.cols_innerABC) ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_5_0_row_0_1_0 : (left1Middle5 5 0) ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn550.rows_assocABC HexagonRowColumn550.cols_innerABC) ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_5_0_row_0_1_1 : (left1Middle5 5 0) ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn550.rows_assocABC HexagonRowColumn550.cols_innerABC) ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_5_0_row_0_1_2 : (left1Middle5 5 0) ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn550.rows_assocABC HexagonRowColumn550.cols_innerABC) ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_5_0_row_0_1_3 : (left1Middle5 5 0) ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn550.rows_assocABC HexagonRowColumn550.cols_innerABC) ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_5_0_row_0_2_0 : (left1Middle5 5 0) ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn550.rows_assocABC HexagonRowColumn550.cols_innerABC) ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_5_0_row_0_2_1 : (left1Middle5 5 0) ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn550.rows_assocABC HexagonRowColumn550.cols_innerABC) ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_5_0_row_0_2_2 : (left1Middle5 5 0) ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn550.rows_assocABC HexagonRowColumn550.cols_innerABC) ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_5_0_row_0_2_3 : (left1Middle5 5 0) ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn550.rows_assocABC HexagonRowColumn550.cols_innerABC) ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_5_0_row_0_3_0 : (left1Middle5 5 0) ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn550.rows_assocABC HexagonRowColumn550.cols_innerABC) ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_5_0_row_0_3_1 : (left1Middle5 5 0) ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn550.rows_assocABC HexagonRowColumn550.cols_innerABC) ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_5_0_row_0_3_2 : (left1Middle5 5 0) ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn550.rows_assocABC HexagonRowColumn550.cols_innerABC) ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_5_0_row_0_3_3 : (left1Middle5 5 0) ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn550.rows_assocABC HexagonRowColumn550.cols_innerABC) ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_5_0_checked : left1Middle5 5 0 = rowColumnMul HexagonRowColumn550.rows_assocABC HexagonRowColumn550.cols_innerABC := by
  funext r
  fin_cases r
  · exact left1Middle5_eq_case_5_0_row_0_0_0
  · exact left1Middle5_eq_case_5_0_row_0_0_1
  · exact left1Middle5_eq_case_5_0_row_0_0_2
  · exact left1Middle5_eq_case_5_0_row_0_0_3
  · exact left1Middle5_eq_case_5_0_row_0_1_0
  · exact left1Middle5_eq_case_5_0_row_0_1_1
  · exact left1Middle5_eq_case_5_0_row_0_1_2
  · exact left1Middle5_eq_case_5_0_row_0_1_3
  · exact left1Middle5_eq_case_5_0_row_0_2_0
  · exact left1Middle5_eq_case_5_0_row_0_2_1
  · exact left1Middle5_eq_case_5_0_row_0_2_2
  · exact left1Middle5_eq_case_5_0_row_0_2_3
  · exact left1Middle5_eq_case_5_0_row_0_3_0
  · exact left1Middle5_eq_case_5_0_row_0_3_1
  · exact left1Middle5_eq_case_5_0_row_0_3_2
  · exact left1Middle5_eq_case_5_0_row_0_3_3

set_option backward.isDefEq.respectTransparency false in
theorem left1Middle5_eq_case_5_0 : left1Middle5 5 0 = associatorZ 5 5 0 * innerLeftZ 5 5 0 := by
  simpa only [HexagonAtoms550.assocABC_eq,
    HexagonAtoms550.outerABC_eq,
    HexagonAtoms550.assocBAC_eq,
    HexagonAtoms550.innerABC_eq,
    HexagonAtoms550.innerRightABC_eq,
    HexagonAtoms550.inverseACB_eq,
    HexagonAtoms550.innerACB_eq,
    HexagonAtoms550.assocBCA_eq,
    HexagonAtoms550.innerRightBAC_eq,
    HexagonAtoms550.assocCAB_eq,
    HexagonAtoms550.outerLeftABC_eq,
    HexagonRowColumn550.assocBAC_alias,
    HexagonRowColumn550.innerRightBAC_alias,
    HexagonRowColumn550.product0_eq,
    HexagonRowColumn550.product1_eq,
    HexagonRowColumn550.product2_eq,
    HexagonRowColumn550.product3_eq,
    HexagonRowColumn550.product4_eq,
    HexagonRowColumn550.product5_eq,
    HexagonRowColumn550.product6_eq,
    HexagonRowColumn550.product7_eq] using left1Middle5_eq_case_5_0_checked

private theorem right0Middle5_eq_case_5_0_row_0_0_0 : (right0Middle5 5 0) ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4)) = (HexagonAtoms550.assocABC) ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_5_0_row_0_0_1 : (right0Middle5 5 0) ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4)) = (HexagonAtoms550.assocABC) ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_5_0_row_0_0_2 : (right0Middle5 5 0) ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4)) = (HexagonAtoms550.assocABC) ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_5_0_row_0_0_3 : (right0Middle5 5 0) ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4)) = (HexagonAtoms550.assocABC) ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_5_0_row_0_1_0 : (right0Middle5 5 0) ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4)) = (HexagonAtoms550.assocABC) ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_5_0_row_0_1_1 : (right0Middle5 5 0) ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4)) = (HexagonAtoms550.assocABC) ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_5_0_row_0_1_2 : (right0Middle5 5 0) ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4)) = (HexagonAtoms550.assocABC) ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_5_0_row_0_1_3 : (right0Middle5 5 0) ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4)) = (HexagonAtoms550.assocABC) ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_5_0_row_0_2_0 : (right0Middle5 5 0) ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4)) = (HexagonAtoms550.assocABC) ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_5_0_row_0_2_1 : (right0Middle5 5 0) ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4)) = (HexagonAtoms550.assocABC) ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_5_0_row_0_2_2 : (right0Middle5 5 0) ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4)) = (HexagonAtoms550.assocABC) ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_5_0_row_0_2_3 : (right0Middle5 5 0) ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4)) = (HexagonAtoms550.assocABC) ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_5_0_row_0_3_0 : (right0Middle5 5 0) ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4)) = (HexagonAtoms550.assocABC) ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_5_0_row_0_3_1 : (right0Middle5 5 0) ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4)) = (HexagonAtoms550.assocABC) ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_5_0_row_0_3_2 : (right0Middle5 5 0) ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4)) = (HexagonAtoms550.assocABC) ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_5_0_row_0_3_3 : (right0Middle5 5 0) ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4)) = (HexagonAtoms550.assocABC) ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_5_0_checked : right0Middle5 5 0 = HexagonAtoms550.assocABC := by
  funext r
  fin_cases r
  · exact right0Middle5_eq_case_5_0_row_0_0_0
  · exact right0Middle5_eq_case_5_0_row_0_0_1
  · exact right0Middle5_eq_case_5_0_row_0_0_2
  · exact right0Middle5_eq_case_5_0_row_0_0_3
  · exact right0Middle5_eq_case_5_0_row_0_1_0
  · exact right0Middle5_eq_case_5_0_row_0_1_1
  · exact right0Middle5_eq_case_5_0_row_0_1_2
  · exact right0Middle5_eq_case_5_0_row_0_1_3
  · exact right0Middle5_eq_case_5_0_row_0_2_0
  · exact right0Middle5_eq_case_5_0_row_0_2_1
  · exact right0Middle5_eq_case_5_0_row_0_2_2
  · exact right0Middle5_eq_case_5_0_row_0_2_3
  · exact right0Middle5_eq_case_5_0_row_0_3_0
  · exact right0Middle5_eq_case_5_0_row_0_3_1
  · exact right0Middle5_eq_case_5_0_row_0_3_2
  · exact right0Middle5_eq_case_5_0_row_0_3_3

set_option backward.isDefEq.respectTransparency false in
theorem right0Middle5_eq_case_5_0 : right0Middle5 5 0 = innerRightZ 5 5 0 * associatorZ 5 5 0 := by
  simpa only [HexagonAtoms550.assocABC_eq,
    HexagonAtoms550.outerABC_eq,
    HexagonAtoms550.assocBAC_eq,
    HexagonAtoms550.innerABC_eq,
    HexagonAtoms550.innerRightABC_eq,
    HexagonAtoms550.inverseACB_eq,
    HexagonAtoms550.innerACB_eq,
    HexagonAtoms550.assocBCA_eq,
    HexagonAtoms550.innerRightBAC_eq,
    HexagonAtoms550.assocCAB_eq,
    HexagonAtoms550.outerLeftABC_eq,
    HexagonRowColumn550.assocBAC_alias,
    HexagonRowColumn550.innerRightBAC_alias,
    HexagonRowColumn550.product0_eq,
    HexagonRowColumn550.product1_eq,
    HexagonRowColumn550.product2_eq,
    HexagonRowColumn550.product3_eq,
    HexagonRowColumn550.product4_eq,
    HexagonRowColumn550.product5_eq,
    HexagonRowColumn550.product6_eq,
    HexagonRowColumn550.product7_eq] using right0Middle5_eq_case_5_0_checked

private theorem right1Middle5_eq_case_5_0_row_0_0_0 : (right1Middle5 5 0) ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4)) = (right0Middle5 5 0) ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_5_0_row_0_0_1 : (right1Middle5 5 0) ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4)) = (right0Middle5 5 0) ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_5_0_row_0_0_2 : (right1Middle5 5 0) ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4)) = (right0Middle5 5 0) ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_5_0_row_0_0_3 : (right1Middle5 5 0) ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4)) = (right0Middle5 5 0) ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_5_0_row_0_1_0 : (right1Middle5 5 0) ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4)) = (right0Middle5 5 0) ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_5_0_row_0_1_1 : (right1Middle5 5 0) ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4)) = (right0Middle5 5 0) ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_5_0_row_0_1_2 : (right1Middle5 5 0) ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4)) = (right0Middle5 5 0) ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_5_0_row_0_1_3 : (right1Middle5 5 0) ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4)) = (right0Middle5 5 0) ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_5_0_row_0_2_0 : (right1Middle5 5 0) ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4)) = (right0Middle5 5 0) ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_5_0_row_0_2_1 : (right1Middle5 5 0) ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4)) = (right0Middle5 5 0) ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_5_0_row_0_2_2 : (right1Middle5 5 0) ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4)) = (right0Middle5 5 0) ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_5_0_row_0_2_3 : (right1Middle5 5 0) ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4)) = (right0Middle5 5 0) ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_5_0_row_0_3_0 : (right1Middle5 5 0) ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4)) = (right0Middle5 5 0) ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_5_0_row_0_3_1 : (right1Middle5 5 0) ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4)) = (right0Middle5 5 0) ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_5_0_row_0_3_2 : (right1Middle5 5 0) ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4)) = (right0Middle5 5 0) ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_5_0_row_0_3_3 : (right1Middle5 5 0) ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4)) = (right0Middle5 5 0) ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_5_0_checked : right1Middle5 5 0 = right0Middle5 5 0 := by
  funext r
  fin_cases r
  · exact right1Middle5_eq_case_5_0_row_0_0_0
  · exact right1Middle5_eq_case_5_0_row_0_0_1
  · exact right1Middle5_eq_case_5_0_row_0_0_2
  · exact right1Middle5_eq_case_5_0_row_0_0_3
  · exact right1Middle5_eq_case_5_0_row_0_1_0
  · exact right1Middle5_eq_case_5_0_row_0_1_1
  · exact right1Middle5_eq_case_5_0_row_0_1_2
  · exact right1Middle5_eq_case_5_0_row_0_1_3
  · exact right1Middle5_eq_case_5_0_row_0_2_0
  · exact right1Middle5_eq_case_5_0_row_0_2_1
  · exact right1Middle5_eq_case_5_0_row_0_2_2
  · exact right1Middle5_eq_case_5_0_row_0_2_3
  · exact right1Middle5_eq_case_5_0_row_0_3_0
  · exact right1Middle5_eq_case_5_0_row_0_3_1
  · exact right1Middle5_eq_case_5_0_row_0_3_2
  · exact right1Middle5_eq_case_5_0_row_0_3_3

set_option backward.isDefEq.respectTransparency false in
theorem right1Middle5_eq_case_5_0 : right1Middle5 5 0 = associatorInverseZ 5 0 5 * right0Middle5 5 0 := by
  simpa only [HexagonAtoms550.assocABC_eq,
    HexagonAtoms550.outerABC_eq,
    HexagonAtoms550.assocBAC_eq,
    HexagonAtoms550.innerABC_eq,
    HexagonAtoms550.innerRightABC_eq,
    HexagonAtoms550.inverseACB_eq,
    HexagonAtoms550.innerACB_eq,
    HexagonAtoms550.assocBCA_eq,
    HexagonAtoms550.innerRightBAC_eq,
    HexagonAtoms550.assocCAB_eq,
    HexagonAtoms550.outerLeftABC_eq,
    HexagonRowColumn550.assocBAC_alias,
    HexagonRowColumn550.innerRightBAC_alias,
    HexagonRowColumn550.product0_eq,
    HexagonRowColumn550.product1_eq,
    HexagonRowColumn550.product2_eq,
    HexagonRowColumn550.product3_eq,
    HexagonRowColumn550.product4_eq,
    HexagonRowColumn550.product5_eq,
    HexagonRowColumn550.product6_eq,
    HexagonRowColumn550.product7_eq] using right1Middle5_eq_case_5_0_checked

private theorem right2Middle5_eq_case_5_0_row_0_0_0 : (right2Middle5 5 0) ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4)) = (right1Middle5 5 0) ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_5_0_row_0_0_1 : (right2Middle5 5 0) ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4)) = (right1Middle5 5 0) ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_5_0_row_0_0_2 : (right2Middle5 5 0) ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4)) = (right1Middle5 5 0) ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_5_0_row_0_0_3 : (right2Middle5 5 0) ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4)) = (right1Middle5 5 0) ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_5_0_row_0_1_0 : (right2Middle5 5 0) ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4)) = (right1Middle5 5 0) ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_5_0_row_0_1_1 : (right2Middle5 5 0) ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4)) = (right1Middle5 5 0) ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_5_0_row_0_1_2 : (right2Middle5 5 0) ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4)) = (right1Middle5 5 0) ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_5_0_row_0_1_3 : (right2Middle5 5 0) ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4)) = (right1Middle5 5 0) ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_5_0_row_0_2_0 : (right2Middle5 5 0) ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4)) = (right1Middle5 5 0) ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_5_0_row_0_2_1 : (right2Middle5 5 0) ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4)) = (right1Middle5 5 0) ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_5_0_row_0_2_2 : (right2Middle5 5 0) ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4)) = (right1Middle5 5 0) ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_5_0_row_0_2_3 : (right2Middle5 5 0) ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4)) = (right1Middle5 5 0) ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_5_0_row_0_3_0 : (right2Middle5 5 0) ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4)) = (right1Middle5 5 0) ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_5_0_row_0_3_1 : (right2Middle5 5 0) ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4)) = (right1Middle5 5 0) ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_5_0_row_0_3_2 : (right2Middle5 5 0) ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4)) = (right1Middle5 5 0) ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_5_0_row_0_3_3 : (right2Middle5 5 0) ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4)) = (right1Middle5 5 0) ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_5_0_checked : right2Middle5 5 0 = right1Middle5 5 0 := by
  funext r
  fin_cases r
  · exact right2Middle5_eq_case_5_0_row_0_0_0
  · exact right2Middle5_eq_case_5_0_row_0_0_1
  · exact right2Middle5_eq_case_5_0_row_0_0_2
  · exact right2Middle5_eq_case_5_0_row_0_0_3
  · exact right2Middle5_eq_case_5_0_row_0_1_0
  · exact right2Middle5_eq_case_5_0_row_0_1_1
  · exact right2Middle5_eq_case_5_0_row_0_1_2
  · exact right2Middle5_eq_case_5_0_row_0_1_3
  · exact right2Middle5_eq_case_5_0_row_0_2_0
  · exact right2Middle5_eq_case_5_0_row_0_2_1
  · exact right2Middle5_eq_case_5_0_row_0_2_2
  · exact right2Middle5_eq_case_5_0_row_0_2_3
  · exact right2Middle5_eq_case_5_0_row_0_3_0
  · exact right2Middle5_eq_case_5_0_row_0_3_1
  · exact right2Middle5_eq_case_5_0_row_0_3_2
  · exact right2Middle5_eq_case_5_0_row_0_3_3

set_option backward.isDefEq.respectTransparency false in
theorem right2Middle5_eq_case_5_0 : right2Middle5 5 0 = innerLeftZ 5 0 5 * right1Middle5 5 0 := by
  simpa only [HexagonAtoms550.assocABC_eq,
    HexagonAtoms550.outerABC_eq,
    HexagonAtoms550.assocBAC_eq,
    HexagonAtoms550.innerABC_eq,
    HexagonAtoms550.innerRightABC_eq,
    HexagonAtoms550.inverseACB_eq,
    HexagonAtoms550.innerACB_eq,
    HexagonAtoms550.assocBCA_eq,
    HexagonAtoms550.innerRightBAC_eq,
    HexagonAtoms550.assocCAB_eq,
    HexagonAtoms550.outerLeftABC_eq,
    HexagonRowColumn550.assocBAC_alias,
    HexagonRowColumn550.innerRightBAC_alias,
    HexagonRowColumn550.product0_eq,
    HexagonRowColumn550.product1_eq,
    HexagonRowColumn550.product2_eq,
    HexagonRowColumn550.product3_eq,
    HexagonRowColumn550.product4_eq,
    HexagonRowColumn550.product5_eq,
    HexagonRowColumn550.product6_eq,
    HexagonRowColumn550.product7_eq] using right2Middle5_eq_case_5_0_checked

private theorem leftFinal5_case_5_0_row_0_0_0 : (((-1 : ℤ) ^ (leftScaleBit 5 5 0).val * positiveScale (leftScaleExponent 5 5 0)) •
      (left0Middle5 5 0)) ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4)) = (negativeScale (leftScaleExponent 5 5 0) • (left1Middle5 5 0)) ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal5_case_5_0_row_0_0_1 : (((-1 : ℤ) ^ (leftScaleBit 5 5 0).val * positiveScale (leftScaleExponent 5 5 0)) •
      (left0Middle5 5 0)) ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4)) = (negativeScale (leftScaleExponent 5 5 0) • (left1Middle5 5 0)) ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal5_case_5_0_row_0_0_2 : (((-1 : ℤ) ^ (leftScaleBit 5 5 0).val * positiveScale (leftScaleExponent 5 5 0)) •
      (left0Middle5 5 0)) ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4)) = (negativeScale (leftScaleExponent 5 5 0) • (left1Middle5 5 0)) ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal5_case_5_0_row_0_0_3 : (((-1 : ℤ) ^ (leftScaleBit 5 5 0).val * positiveScale (leftScaleExponent 5 5 0)) •
      (left0Middle5 5 0)) ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4)) = (negativeScale (leftScaleExponent 5 5 0) • (left1Middle5 5 0)) ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal5_case_5_0_row_0_1_0 : (((-1 : ℤ) ^ (leftScaleBit 5 5 0).val * positiveScale (leftScaleExponent 5 5 0)) •
      (left0Middle5 5 0)) ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4)) = (negativeScale (leftScaleExponent 5 5 0) • (left1Middle5 5 0)) ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal5_case_5_0_row_0_1_1 : (((-1 : ℤ) ^ (leftScaleBit 5 5 0).val * positiveScale (leftScaleExponent 5 5 0)) •
      (left0Middle5 5 0)) ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4)) = (negativeScale (leftScaleExponent 5 5 0) • (left1Middle5 5 0)) ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal5_case_5_0_row_0_1_2 : (((-1 : ℤ) ^ (leftScaleBit 5 5 0).val * positiveScale (leftScaleExponent 5 5 0)) •
      (left0Middle5 5 0)) ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4)) = (negativeScale (leftScaleExponent 5 5 0) • (left1Middle5 5 0)) ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal5_case_5_0_row_0_1_3 : (((-1 : ℤ) ^ (leftScaleBit 5 5 0).val * positiveScale (leftScaleExponent 5 5 0)) •
      (left0Middle5 5 0)) ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4)) = (negativeScale (leftScaleExponent 5 5 0) • (left1Middle5 5 0)) ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal5_case_5_0_row_0_2_0 : (((-1 : ℤ) ^ (leftScaleBit 5 5 0).val * positiveScale (leftScaleExponent 5 5 0)) •
      (left0Middle5 5 0)) ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4)) = (negativeScale (leftScaleExponent 5 5 0) • (left1Middle5 5 0)) ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal5_case_5_0_row_0_2_1 : (((-1 : ℤ) ^ (leftScaleBit 5 5 0).val * positiveScale (leftScaleExponent 5 5 0)) •
      (left0Middle5 5 0)) ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4)) = (negativeScale (leftScaleExponent 5 5 0) • (left1Middle5 5 0)) ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal5_case_5_0_row_0_2_2 : (((-1 : ℤ) ^ (leftScaleBit 5 5 0).val * positiveScale (leftScaleExponent 5 5 0)) •
      (left0Middle5 5 0)) ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4)) = (negativeScale (leftScaleExponent 5 5 0) • (left1Middle5 5 0)) ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal5_case_5_0_row_0_2_3 : (((-1 : ℤ) ^ (leftScaleBit 5 5 0).val * positiveScale (leftScaleExponent 5 5 0)) •
      (left0Middle5 5 0)) ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4)) = (negativeScale (leftScaleExponent 5 5 0) • (left1Middle5 5 0)) ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal5_case_5_0_row_0_3_0 : (((-1 : ℤ) ^ (leftScaleBit 5 5 0).val * positiveScale (leftScaleExponent 5 5 0)) •
      (left0Middle5 5 0)) ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4)) = (negativeScale (leftScaleExponent 5 5 0) • (left1Middle5 5 0)) ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal5_case_5_0_row_0_3_1 : (((-1 : ℤ) ^ (leftScaleBit 5 5 0).val * positiveScale (leftScaleExponent 5 5 0)) •
      (left0Middle5 5 0)) ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4)) = (negativeScale (leftScaleExponent 5 5 0) • (left1Middle5 5 0)) ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal5_case_5_0_row_0_3_2 : (((-1 : ℤ) ^ (leftScaleBit 5 5 0).val * positiveScale (leftScaleExponent 5 5 0)) •
      (left0Middle5 5 0)) ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4)) = (negativeScale (leftScaleExponent 5 5 0) • (left1Middle5 5 0)) ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal5_case_5_0_row_0_3_3 : (((-1 : ℤ) ^ (leftScaleBit 5 5 0).val * positiveScale (leftScaleExponent 5 5 0)) •
      (left0Middle5 5 0)) ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4)) = (negativeScale (leftScaleExponent 5 5 0) • (left1Middle5 5 0)) ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal5_case_5_0_checked : ((-1 : ℤ) ^ (leftScaleBit 5 5 0).val * positiveScale (leftScaleExponent 5 5 0)) •
      (left0Middle5 5 0) = negativeScale (leftScaleExponent 5 5 0) • (left1Middle5 5 0) := by
  funext r
  fin_cases r
  · exact leftFinal5_case_5_0_row_0_0_0
  · exact leftFinal5_case_5_0_row_0_0_1
  · exact leftFinal5_case_5_0_row_0_0_2
  · exact leftFinal5_case_5_0_row_0_0_3
  · exact leftFinal5_case_5_0_row_0_1_0
  · exact leftFinal5_case_5_0_row_0_1_1
  · exact leftFinal5_case_5_0_row_0_1_2
  · exact leftFinal5_case_5_0_row_0_1_3
  · exact leftFinal5_case_5_0_row_0_2_0
  · exact leftFinal5_case_5_0_row_0_2_1
  · exact leftFinal5_case_5_0_row_0_2_2
  · exact leftFinal5_case_5_0_row_0_2_3
  · exact leftFinal5_case_5_0_row_0_3_0
  · exact leftFinal5_case_5_0_row_0_3_1
  · exact leftFinal5_case_5_0_row_0_3_2
  · exact leftFinal5_case_5_0_row_0_3_3

set_option backward.isDefEq.respectTransparency false in
theorem leftFinal5_case_5_0 : ((-1 : ℤ) ^ (leftScaleBit 5 5 0).val * positiveScale (leftScaleExponent 5 5 0)) •
      (associatorZ 5 0 5 * left0Middle5 5 0) = negativeScale (leftScaleExponent 5 5 0) • (innerRightZ 5 5 0 * left1Middle5 5 0) := by
  simpa only [HexagonAtoms550.assocABC_eq,
    HexagonAtoms550.outerABC_eq,
    HexagonAtoms550.assocBAC_eq,
    HexagonAtoms550.innerABC_eq,
    HexagonAtoms550.innerRightABC_eq,
    HexagonAtoms550.inverseACB_eq,
    HexagonAtoms550.innerACB_eq,
    HexagonAtoms550.assocBCA_eq,
    HexagonAtoms550.innerRightBAC_eq,
    HexagonAtoms550.assocCAB_eq,
    HexagonAtoms550.outerLeftABC_eq,
    HexagonRowColumn550.assocBAC_alias,
    HexagonRowColumn550.innerRightBAC_alias,
    HexagonRowColumn550.product0_eq,
    HexagonRowColumn550.product1_eq,
    HexagonRowColumn550.product2_eq,
    HexagonRowColumn550.product3_eq,
    HexagonRowColumn550.product4_eq,
    HexagonRowColumn550.product5_eq,
    HexagonRowColumn550.product6_eq,
    HexagonRowColumn550.product7_eq] using leftFinal5_case_5_0_checked

private theorem rightFinal5_case_5_0_row_0_0_0 : (((-1 : ℤ) ^ (rightScaleBit 5 5 0).val * positiveScale (rightScaleExponent 5 5 0) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 0 5 : ℤ)) • HexagonAtoms550.outerLeftABC) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (negativeScale (rightScaleExponent 5 5 0) • (rowColumnMul HexagonRowColumn550.rows_assocCAB HexagonRowColumn550.cols_right2)) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal5_case_5_0_row_0_0_1 : (((-1 : ℤ) ^ (rightScaleBit 5 5 0).val * positiveScale (rightScaleExponent 5 5 0) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 0 5 : ℤ)) • HexagonAtoms550.outerLeftABC) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (negativeScale (rightScaleExponent 5 5 0) • (rowColumnMul HexagonRowColumn550.rows_assocCAB HexagonRowColumn550.cols_right2)) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal5_case_5_0_row_0_0_2 : (((-1 : ℤ) ^ (rightScaleBit 5 5 0).val * positiveScale (rightScaleExponent 5 5 0) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 0 5 : ℤ)) • HexagonAtoms550.outerLeftABC) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (negativeScale (rightScaleExponent 5 5 0) • (rowColumnMul HexagonRowColumn550.rows_assocCAB HexagonRowColumn550.cols_right2)) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal5_case_5_0_row_0_0_3 : (((-1 : ℤ) ^ (rightScaleBit 5 5 0).val * positiveScale (rightScaleExponent 5 5 0) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 0 5 : ℤ)) • HexagonAtoms550.outerLeftABC) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (negativeScale (rightScaleExponent 5 5 0) • (rowColumnMul HexagonRowColumn550.rows_assocCAB HexagonRowColumn550.cols_right2)) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal5_case_5_0_row_1_0_0 : (((-1 : ℤ) ^ (rightScaleBit 5 5 0).val * positiveScale (rightScaleExponent 5 5 0) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 0 5 : ℤ)) • HexagonAtoms550.outerLeftABC) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (negativeScale (rightScaleExponent 5 5 0) • (rowColumnMul HexagonRowColumn550.rows_assocCAB HexagonRowColumn550.cols_right2)) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal5_case_5_0_row_1_0_1 : (((-1 : ℤ) ^ (rightScaleBit 5 5 0).val * positiveScale (rightScaleExponent 5 5 0) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 0 5 : ℤ)) • HexagonAtoms550.outerLeftABC) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (negativeScale (rightScaleExponent 5 5 0) • (rowColumnMul HexagonRowColumn550.rows_assocCAB HexagonRowColumn550.cols_right2)) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal5_case_5_0_row_1_0_2 : (((-1 : ℤ) ^ (rightScaleBit 5 5 0).val * positiveScale (rightScaleExponent 5 5 0) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 0 5 : ℤ)) • HexagonAtoms550.outerLeftABC) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (negativeScale (rightScaleExponent 5 5 0) • (rowColumnMul HexagonRowColumn550.rows_assocCAB HexagonRowColumn550.cols_right2)) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal5_case_5_0_row_1_0_3 : (((-1 : ℤ) ^ (rightScaleBit 5 5 0).val * positiveScale (rightScaleExponent 5 5 0) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 0 5 : ℤ)) • HexagonAtoms550.outerLeftABC) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (negativeScale (rightScaleExponent 5 5 0) • (rowColumnMul HexagonRowColumn550.rows_assocCAB HexagonRowColumn550.cols_right2)) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal5_case_5_0_row_2_0_0 : (((-1 : ℤ) ^ (rightScaleBit 5 5 0).val * positiveScale (rightScaleExponent 5 5 0) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 0 5 : ℤ)) • HexagonAtoms550.outerLeftABC) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (negativeScale (rightScaleExponent 5 5 0) • (rowColumnMul HexagonRowColumn550.rows_assocCAB HexagonRowColumn550.cols_right2)) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal5_case_5_0_row_2_0_1 : (((-1 : ℤ) ^ (rightScaleBit 5 5 0).val * positiveScale (rightScaleExponent 5 5 0) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 0 5 : ℤ)) • HexagonAtoms550.outerLeftABC) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (negativeScale (rightScaleExponent 5 5 0) • (rowColumnMul HexagonRowColumn550.rows_assocCAB HexagonRowColumn550.cols_right2)) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal5_case_5_0_row_2_0_2 : (((-1 : ℤ) ^ (rightScaleBit 5 5 0).val * positiveScale (rightScaleExponent 5 5 0) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 0 5 : ℤ)) • HexagonAtoms550.outerLeftABC) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (negativeScale (rightScaleExponent 5 5 0) • (rowColumnMul HexagonRowColumn550.rows_assocCAB HexagonRowColumn550.cols_right2)) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal5_case_5_0_row_2_0_3 : (((-1 : ℤ) ^ (rightScaleBit 5 5 0).val * positiveScale (rightScaleExponent 5 5 0) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 0 5 : ℤ)) • HexagonAtoms550.outerLeftABC) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (negativeScale (rightScaleExponent 5 5 0) • (rowColumnMul HexagonRowColumn550.rows_assocCAB HexagonRowColumn550.cols_right2)) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal5_case_5_0_row_3_0_0 : (((-1 : ℤ) ^ (rightScaleBit 5 5 0).val * positiveScale (rightScaleExponent 5 5 0) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 0 5 : ℤ)) • HexagonAtoms550.outerLeftABC) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (negativeScale (rightScaleExponent 5 5 0) • (rowColumnMul HexagonRowColumn550.rows_assocCAB HexagonRowColumn550.cols_right2)) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal5_case_5_0_row_3_0_1 : (((-1 : ℤ) ^ (rightScaleBit 5 5 0).val * positiveScale (rightScaleExponent 5 5 0) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 0 5 : ℤ)) • HexagonAtoms550.outerLeftABC) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (negativeScale (rightScaleExponent 5 5 0) • (rowColumnMul HexagonRowColumn550.rows_assocCAB HexagonRowColumn550.cols_right2)) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal5_case_5_0_row_3_0_2 : (((-1 : ℤ) ^ (rightScaleBit 5 5 0).val * positiveScale (rightScaleExponent 5 5 0) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 0 5 : ℤ)) • HexagonAtoms550.outerLeftABC) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (negativeScale (rightScaleExponent 5 5 0) • (rowColumnMul HexagonRowColumn550.rows_assocCAB HexagonRowColumn550.cols_right2)) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal5_case_5_0_row_3_0_3 : (((-1 : ℤ) ^ (rightScaleBit 5 5 0).val * positiveScale (rightScaleExponent 5 5 0) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 0 5 : ℤ)) • HexagonAtoms550.outerLeftABC) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (negativeScale (rightScaleExponent 5 5 0) • (rowColumnMul HexagonRowColumn550.rows_assocCAB HexagonRowColumn550.cols_right2)) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal5_case_5_0_checked : ((-1 : ℤ) ^ (rightScaleBit 5 5 0).val * positiveScale (rightScaleExponent 5 5 0) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 0 5 : ℤ)) • HexagonAtoms550.outerLeftABC = negativeScale (rightScaleExponent 5 5 0) • (rowColumnMul HexagonRowColumn550.rows_assocCAB HexagonRowColumn550.cols_right2) := by
  funext r
  fin_cases r
  · exact rightFinal5_case_5_0_row_0_0_0
  · exact rightFinal5_case_5_0_row_0_0_1
  · exact rightFinal5_case_5_0_row_0_0_2
  · exact rightFinal5_case_5_0_row_0_0_3
  · exact rightFinal5_case_5_0_row_1_0_0
  · exact rightFinal5_case_5_0_row_1_0_1
  · exact rightFinal5_case_5_0_row_1_0_2
  · exact rightFinal5_case_5_0_row_1_0_3
  · exact rightFinal5_case_5_0_row_2_0_0
  · exact rightFinal5_case_5_0_row_2_0_1
  · exact rightFinal5_case_5_0_row_2_0_2
  · exact rightFinal5_case_5_0_row_2_0_3
  · exact rightFinal5_case_5_0_row_3_0_0
  · exact rightFinal5_case_5_0_row_3_0_1
  · exact rightFinal5_case_5_0_row_3_0_2
  · exact rightFinal5_case_5_0_row_3_0_3

set_option backward.isDefEq.respectTransparency false in
theorem rightFinal5_case_5_0 : ((-1 : ℤ) ^ (rightScaleBit 5 5 0).val * positiveScale (rightScaleExponent 5 5 0) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 0 5 : ℤ)) • outerLeftZ 5 5 0 = negativeScale (rightScaleExponent 5 5 0) • (associatorZ 0 5 5 * right2Middle5 5 0) := by
  simpa only [HexagonAtoms550.assocABC_eq,
    HexagonAtoms550.outerABC_eq,
    HexagonAtoms550.assocBAC_eq,
    HexagonAtoms550.innerABC_eq,
    HexagonAtoms550.innerRightABC_eq,
    HexagonAtoms550.inverseACB_eq,
    HexagonAtoms550.innerACB_eq,
    HexagonAtoms550.assocBCA_eq,
    HexagonAtoms550.innerRightBAC_eq,
    HexagonAtoms550.assocCAB_eq,
    HexagonAtoms550.outerLeftABC_eq,
    HexagonRowColumn550.assocBAC_alias,
    HexagonRowColumn550.innerRightBAC_alias,
    HexagonRowColumn550.product0_eq,
    HexagonRowColumn550.product1_eq,
    HexagonRowColumn550.product2_eq,
    HexagonRowColumn550.product3_eq,
    HexagonRowColumn550.product4_eq,
    HexagonRowColumn550.product5_eq,
    HexagonRowColumn550.product6_eq,
    HexagonRowColumn550.product7_eq] using rightFinal5_case_5_0_checked

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonCases5
