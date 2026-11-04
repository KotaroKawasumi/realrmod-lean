import RMod.BrundanEllis.StackingReferenceHexagonMiddle6
import RMod.BrundanEllis.StackingReferenceSparseMatrixCheck
import RMod.BrundanEllis.StackingReferenceHexagonAtoms616
import RMod.BrundanEllis.StackingReferenceHexagonRowColumn616

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

private theorem left0Middle6_eq_case_1_6_row_0_0_0 : (left0Middle6 1 6) ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8)) = (rowColumnMul HexagonRowColumn616.rows_outerABC HexagonRowColumn616.cols_assocABC) ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem left0Middle6_eq_case_1_6_row_0_0_1 : (left0Middle6 1 6) ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8)) = (rowColumnMul HexagonRowColumn616.rows_outerABC HexagonRowColumn616.cols_assocABC) ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem left0Middle6_eq_case_1_6_row_0_0_2 : (left0Middle6 1 6) ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8)) = (rowColumnMul HexagonRowColumn616.rows_outerABC HexagonRowColumn616.cols_assocABC) ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem left0Middle6_eq_case_1_6_row_0_0_3 : (left0Middle6 1 6) ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8)) = (rowColumnMul HexagonRowColumn616.rows_outerABC HexagonRowColumn616.cols_assocABC) ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem left0Middle6_eq_case_1_6_row_0_0_4 : (left0Middle6 1 6) ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8)) = (rowColumnMul HexagonRowColumn616.rows_outerABC HexagonRowColumn616.cols_assocABC) ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem left0Middle6_eq_case_1_6_row_0_0_5 : (left0Middle6 1 6) ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8)) = (rowColumnMul HexagonRowColumn616.rows_outerABC HexagonRowColumn616.cols_assocABC) ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem left0Middle6_eq_case_1_6_row_0_0_6 : (left0Middle6 1 6) ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8)) = (rowColumnMul HexagonRowColumn616.rows_outerABC HexagonRowColumn616.cols_assocABC) ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem left0Middle6_eq_case_1_6_row_0_0_7 : (left0Middle6 1 6) ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8)) = (rowColumnMul HexagonRowColumn616.rows_outerABC HexagonRowColumn616.cols_assocABC) ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem left0Middle6_eq_case_1_6_row_1_0_0 : (left0Middle6 1 6) ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8)) = (rowColumnMul HexagonRowColumn616.rows_outerABC HexagonRowColumn616.cols_assocABC) ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem left0Middle6_eq_case_1_6_row_1_0_1 : (left0Middle6 1 6) ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8)) = (rowColumnMul HexagonRowColumn616.rows_outerABC HexagonRowColumn616.cols_assocABC) ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem left0Middle6_eq_case_1_6_row_1_0_2 : (left0Middle6 1 6) ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8)) = (rowColumnMul HexagonRowColumn616.rows_outerABC HexagonRowColumn616.cols_assocABC) ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem left0Middle6_eq_case_1_6_row_1_0_3 : (left0Middle6 1 6) ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8)) = (rowColumnMul HexagonRowColumn616.rows_outerABC HexagonRowColumn616.cols_assocABC) ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem left0Middle6_eq_case_1_6_row_1_0_4 : (left0Middle6 1 6) ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8)) = (rowColumnMul HexagonRowColumn616.rows_outerABC HexagonRowColumn616.cols_assocABC) ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem left0Middle6_eq_case_1_6_row_1_0_5 : (left0Middle6 1 6) ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8)) = (rowColumnMul HexagonRowColumn616.rows_outerABC HexagonRowColumn616.cols_assocABC) ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem left0Middle6_eq_case_1_6_row_1_0_6 : (left0Middle6 1 6) ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8)) = (rowColumnMul HexagonRowColumn616.rows_outerABC HexagonRowColumn616.cols_assocABC) ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem left0Middle6_eq_case_1_6_row_1_0_7 : (left0Middle6 1 6) ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8)) = (rowColumnMul HexagonRowColumn616.rows_outerABC HexagonRowColumn616.cols_assocABC) ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem left0Middle6_eq_case_1_6_checked : left0Middle6 1 6 = rowColumnMul HexagonRowColumn616.rows_outerABC HexagonRowColumn616.cols_assocABC := by
  funext r
  fin_cases r
  · exact left0Middle6_eq_case_1_6_row_0_0_0
  · exact left0Middle6_eq_case_1_6_row_0_0_1
  · exact left0Middle6_eq_case_1_6_row_0_0_2
  · exact left0Middle6_eq_case_1_6_row_0_0_3
  · exact left0Middle6_eq_case_1_6_row_0_0_4
  · exact left0Middle6_eq_case_1_6_row_0_0_5
  · exact left0Middle6_eq_case_1_6_row_0_0_6
  · exact left0Middle6_eq_case_1_6_row_0_0_7
  · exact left0Middle6_eq_case_1_6_row_1_0_0
  · exact left0Middle6_eq_case_1_6_row_1_0_1
  · exact left0Middle6_eq_case_1_6_row_1_0_2
  · exact left0Middle6_eq_case_1_6_row_1_0_3
  · exact left0Middle6_eq_case_1_6_row_1_0_4
  · exact left0Middle6_eq_case_1_6_row_1_0_5
  · exact left0Middle6_eq_case_1_6_row_1_0_6
  · exact left0Middle6_eq_case_1_6_row_1_0_7

set_option backward.isDefEq.respectTransparency false in
theorem left0Middle6_eq_case_1_6 : left0Middle6 1 6 = outerRightZ 6 1 6 * associatorZ 6 1 6 := by
  simpa only [HexagonAtoms616.assocABC_eq,
    HexagonAtoms616.outerABC_eq,
    HexagonAtoms616.assocBAC_eq,
    HexagonAtoms616.innerABC_eq,
    HexagonAtoms616.innerRightABC_eq,
    HexagonAtoms616.inverseACB_eq,
    HexagonAtoms616.innerACB_eq,
    HexagonAtoms616.assocBCA_eq,
    HexagonAtoms616.innerRightBAC_eq,
    HexagonAtoms616.assocCAB_eq,
    HexagonAtoms616.outerLeftABC_eq,
    HexagonRowColumn616.assocBCA_alias,
    HexagonRowColumn616.product0_eq,
    HexagonRowColumn616.product1_eq,
    HexagonRowColumn616.product2_eq,
    HexagonRowColumn616.product3_eq,
    HexagonRowColumn616.product4_eq,
    HexagonRowColumn616.product5_eq,
    HexagonRowColumn616.product6_eq,
    HexagonRowColumn616.product7_eq] using left0Middle6_eq_case_1_6_checked

private theorem left1Middle6_eq_case_1_6_row_0_0_0 : (left1Middle6 1 6) ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8)) = (HexagonAtoms616.assocBAC) ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem left1Middle6_eq_case_1_6_row_0_0_1 : (left1Middle6 1 6) ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8)) = (HexagonAtoms616.assocBAC) ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem left1Middle6_eq_case_1_6_row_0_0_2 : (left1Middle6 1 6) ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8)) = (HexagonAtoms616.assocBAC) ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem left1Middle6_eq_case_1_6_row_0_0_3 : (left1Middle6 1 6) ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8)) = (HexagonAtoms616.assocBAC) ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem left1Middle6_eq_case_1_6_row_0_0_4 : (left1Middle6 1 6) ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8)) = (HexagonAtoms616.assocBAC) ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem left1Middle6_eq_case_1_6_row_0_0_5 : (left1Middle6 1 6) ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8)) = (HexagonAtoms616.assocBAC) ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem left1Middle6_eq_case_1_6_row_0_0_6 : (left1Middle6 1 6) ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8)) = (HexagonAtoms616.assocBAC) ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem left1Middle6_eq_case_1_6_row_0_0_7 : (left1Middle6 1 6) ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8)) = (HexagonAtoms616.assocBAC) ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem left1Middle6_eq_case_1_6_row_1_0_0 : (left1Middle6 1 6) ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8)) = (HexagonAtoms616.assocBAC) ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem left1Middle6_eq_case_1_6_row_1_0_1 : (left1Middle6 1 6) ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8)) = (HexagonAtoms616.assocBAC) ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem left1Middle6_eq_case_1_6_row_1_0_2 : (left1Middle6 1 6) ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8)) = (HexagonAtoms616.assocBAC) ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem left1Middle6_eq_case_1_6_row_1_0_3 : (left1Middle6 1 6) ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8)) = (HexagonAtoms616.assocBAC) ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem left1Middle6_eq_case_1_6_row_1_0_4 : (left1Middle6 1 6) ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8)) = (HexagonAtoms616.assocBAC) ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem left1Middle6_eq_case_1_6_row_1_0_5 : (left1Middle6 1 6) ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8)) = (HexagonAtoms616.assocBAC) ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem left1Middle6_eq_case_1_6_row_1_0_6 : (left1Middle6 1 6) ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8)) = (HexagonAtoms616.assocBAC) ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem left1Middle6_eq_case_1_6_row_1_0_7 : (left1Middle6 1 6) ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8)) = (HexagonAtoms616.assocBAC) ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem left1Middle6_eq_case_1_6_checked : left1Middle6 1 6 = HexagonAtoms616.assocBAC := by
  funext r
  fin_cases r
  · exact left1Middle6_eq_case_1_6_row_0_0_0
  · exact left1Middle6_eq_case_1_6_row_0_0_1
  · exact left1Middle6_eq_case_1_6_row_0_0_2
  · exact left1Middle6_eq_case_1_6_row_0_0_3
  · exact left1Middle6_eq_case_1_6_row_0_0_4
  · exact left1Middle6_eq_case_1_6_row_0_0_5
  · exact left1Middle6_eq_case_1_6_row_0_0_6
  · exact left1Middle6_eq_case_1_6_row_0_0_7
  · exact left1Middle6_eq_case_1_6_row_1_0_0
  · exact left1Middle6_eq_case_1_6_row_1_0_1
  · exact left1Middle6_eq_case_1_6_row_1_0_2
  · exact left1Middle6_eq_case_1_6_row_1_0_3
  · exact left1Middle6_eq_case_1_6_row_1_0_4
  · exact left1Middle6_eq_case_1_6_row_1_0_5
  · exact left1Middle6_eq_case_1_6_row_1_0_6
  · exact left1Middle6_eq_case_1_6_row_1_0_7

set_option backward.isDefEq.respectTransparency false in
theorem left1Middle6_eq_case_1_6 : left1Middle6 1 6 = associatorZ 1 6 6 * innerLeftZ 6 1 6 := by
  simpa only [HexagonAtoms616.assocABC_eq,
    HexagonAtoms616.outerABC_eq,
    HexagonAtoms616.assocBAC_eq,
    HexagonAtoms616.innerABC_eq,
    HexagonAtoms616.innerRightABC_eq,
    HexagonAtoms616.inverseACB_eq,
    HexagonAtoms616.innerACB_eq,
    HexagonAtoms616.assocBCA_eq,
    HexagonAtoms616.innerRightBAC_eq,
    HexagonAtoms616.assocCAB_eq,
    HexagonAtoms616.outerLeftABC_eq,
    HexagonRowColumn616.assocBCA_alias,
    HexagonRowColumn616.product0_eq,
    HexagonRowColumn616.product1_eq,
    HexagonRowColumn616.product2_eq,
    HexagonRowColumn616.product3_eq,
    HexagonRowColumn616.product4_eq,
    HexagonRowColumn616.product5_eq,
    HexagonRowColumn616.product6_eq,
    HexagonRowColumn616.product7_eq] using left1Middle6_eq_case_1_6_checked

private theorem right0Middle6_eq_case_1_6_row_0_0_0 : (right0Middle6 1 6) ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8)) = (HexagonAtoms616.assocABC) ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right0Middle6_eq_case_1_6_row_0_0_1 : (right0Middle6 1 6) ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8)) = (HexagonAtoms616.assocABC) ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right0Middle6_eq_case_1_6_row_0_0_2 : (right0Middle6 1 6) ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8)) = (HexagonAtoms616.assocABC) ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right0Middle6_eq_case_1_6_row_0_0_3 : (right0Middle6 1 6) ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8)) = (HexagonAtoms616.assocABC) ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right0Middle6_eq_case_1_6_row_0_0_4 : (right0Middle6 1 6) ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8)) = (HexagonAtoms616.assocABC) ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right0Middle6_eq_case_1_6_row_0_0_5 : (right0Middle6 1 6) ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8)) = (HexagonAtoms616.assocABC) ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right0Middle6_eq_case_1_6_row_0_0_6 : (right0Middle6 1 6) ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8)) = (HexagonAtoms616.assocABC) ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right0Middle6_eq_case_1_6_row_0_0_7 : (right0Middle6 1 6) ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8)) = (HexagonAtoms616.assocABC) ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right0Middle6_eq_case_1_6_row_1_0_0 : (right0Middle6 1 6) ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8)) = (HexagonAtoms616.assocABC) ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right0Middle6_eq_case_1_6_row_1_0_1 : (right0Middle6 1 6) ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8)) = (HexagonAtoms616.assocABC) ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right0Middle6_eq_case_1_6_row_1_0_2 : (right0Middle6 1 6) ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8)) = (HexagonAtoms616.assocABC) ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right0Middle6_eq_case_1_6_row_1_0_3 : (right0Middle6 1 6) ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8)) = (HexagonAtoms616.assocABC) ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right0Middle6_eq_case_1_6_row_1_0_4 : (right0Middle6 1 6) ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8)) = (HexagonAtoms616.assocABC) ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right0Middle6_eq_case_1_6_row_1_0_5 : (right0Middle6 1 6) ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8)) = (HexagonAtoms616.assocABC) ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right0Middle6_eq_case_1_6_row_1_0_6 : (right0Middle6 1 6) ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8)) = (HexagonAtoms616.assocABC) ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right0Middle6_eq_case_1_6_row_1_0_7 : (right0Middle6 1 6) ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8)) = (HexagonAtoms616.assocABC) ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right0Middle6_eq_case_1_6_checked : right0Middle6 1 6 = HexagonAtoms616.assocABC := by
  funext r
  fin_cases r
  · exact right0Middle6_eq_case_1_6_row_0_0_0
  · exact right0Middle6_eq_case_1_6_row_0_0_1
  · exact right0Middle6_eq_case_1_6_row_0_0_2
  · exact right0Middle6_eq_case_1_6_row_0_0_3
  · exact right0Middle6_eq_case_1_6_row_0_0_4
  · exact right0Middle6_eq_case_1_6_row_0_0_5
  · exact right0Middle6_eq_case_1_6_row_0_0_6
  · exact right0Middle6_eq_case_1_6_row_0_0_7
  · exact right0Middle6_eq_case_1_6_row_1_0_0
  · exact right0Middle6_eq_case_1_6_row_1_0_1
  · exact right0Middle6_eq_case_1_6_row_1_0_2
  · exact right0Middle6_eq_case_1_6_row_1_0_3
  · exact right0Middle6_eq_case_1_6_row_1_0_4
  · exact right0Middle6_eq_case_1_6_row_1_0_5
  · exact right0Middle6_eq_case_1_6_row_1_0_6
  · exact right0Middle6_eq_case_1_6_row_1_0_7

set_option backward.isDefEq.respectTransparency false in
theorem right0Middle6_eq_case_1_6 : right0Middle6 1 6 = innerRightZ 6 1 6 * associatorZ 6 1 6 := by
  simpa only [HexagonAtoms616.assocABC_eq,
    HexagonAtoms616.outerABC_eq,
    HexagonAtoms616.assocBAC_eq,
    HexagonAtoms616.innerABC_eq,
    HexagonAtoms616.innerRightABC_eq,
    HexagonAtoms616.inverseACB_eq,
    HexagonAtoms616.innerACB_eq,
    HexagonAtoms616.assocBCA_eq,
    HexagonAtoms616.innerRightBAC_eq,
    HexagonAtoms616.assocCAB_eq,
    HexagonAtoms616.outerLeftABC_eq,
    HexagonRowColumn616.assocBCA_alias,
    HexagonRowColumn616.product0_eq,
    HexagonRowColumn616.product1_eq,
    HexagonRowColumn616.product2_eq,
    HexagonRowColumn616.product3_eq,
    HexagonRowColumn616.product4_eq,
    HexagonRowColumn616.product5_eq,
    HexagonRowColumn616.product6_eq,
    HexagonRowColumn616.product7_eq] using right0Middle6_eq_case_1_6_checked

private theorem right1Middle6_eq_case_1_6_row_0_0_0 : (right1Middle6 1 6) ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8)) = (rowColumnMul HexagonRowColumn616.rows_inverseACB HexagonRowColumn616.cols_right0) ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right1Middle6_eq_case_1_6_row_0_0_1 : (right1Middle6 1 6) ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8)) = (rowColumnMul HexagonRowColumn616.rows_inverseACB HexagonRowColumn616.cols_right0) ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right1Middle6_eq_case_1_6_row_0_0_2 : (right1Middle6 1 6) ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8)) = (rowColumnMul HexagonRowColumn616.rows_inverseACB HexagonRowColumn616.cols_right0) ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right1Middle6_eq_case_1_6_row_0_0_3 : (right1Middle6 1 6) ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8)) = (rowColumnMul HexagonRowColumn616.rows_inverseACB HexagonRowColumn616.cols_right0) ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right1Middle6_eq_case_1_6_row_0_0_4 : (right1Middle6 1 6) ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8)) = (rowColumnMul HexagonRowColumn616.rows_inverseACB HexagonRowColumn616.cols_right0) ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right1Middle6_eq_case_1_6_row_0_0_5 : (right1Middle6 1 6) ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8)) = (rowColumnMul HexagonRowColumn616.rows_inverseACB HexagonRowColumn616.cols_right0) ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right1Middle6_eq_case_1_6_row_0_0_6 : (right1Middle6 1 6) ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8)) = (rowColumnMul HexagonRowColumn616.rows_inverseACB HexagonRowColumn616.cols_right0) ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right1Middle6_eq_case_1_6_row_0_0_7 : (right1Middle6 1 6) ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8)) = (rowColumnMul HexagonRowColumn616.rows_inverseACB HexagonRowColumn616.cols_right0) ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right1Middle6_eq_case_1_6_row_1_0_0 : (right1Middle6 1 6) ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8)) = (rowColumnMul HexagonRowColumn616.rows_inverseACB HexagonRowColumn616.cols_right0) ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right1Middle6_eq_case_1_6_row_1_0_1 : (right1Middle6 1 6) ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8)) = (rowColumnMul HexagonRowColumn616.rows_inverseACB HexagonRowColumn616.cols_right0) ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right1Middle6_eq_case_1_6_row_1_0_2 : (right1Middle6 1 6) ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8)) = (rowColumnMul HexagonRowColumn616.rows_inverseACB HexagonRowColumn616.cols_right0) ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right1Middle6_eq_case_1_6_row_1_0_3 : (right1Middle6 1 6) ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8)) = (rowColumnMul HexagonRowColumn616.rows_inverseACB HexagonRowColumn616.cols_right0) ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right1Middle6_eq_case_1_6_row_1_0_4 : (right1Middle6 1 6) ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8)) = (rowColumnMul HexagonRowColumn616.rows_inverseACB HexagonRowColumn616.cols_right0) ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right1Middle6_eq_case_1_6_row_1_0_5 : (right1Middle6 1 6) ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8)) = (rowColumnMul HexagonRowColumn616.rows_inverseACB HexagonRowColumn616.cols_right0) ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right1Middle6_eq_case_1_6_row_1_0_6 : (right1Middle6 1 6) ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8)) = (rowColumnMul HexagonRowColumn616.rows_inverseACB HexagonRowColumn616.cols_right0) ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right1Middle6_eq_case_1_6_row_1_0_7 : (right1Middle6 1 6) ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8)) = (rowColumnMul HexagonRowColumn616.rows_inverseACB HexagonRowColumn616.cols_right0) ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right1Middle6_eq_case_1_6_checked : right1Middle6 1 6 = rowColumnMul HexagonRowColumn616.rows_inverseACB HexagonRowColumn616.cols_right0 := by
  funext r
  fin_cases r
  · exact right1Middle6_eq_case_1_6_row_0_0_0
  · exact right1Middle6_eq_case_1_6_row_0_0_1
  · exact right1Middle6_eq_case_1_6_row_0_0_2
  · exact right1Middle6_eq_case_1_6_row_0_0_3
  · exact right1Middle6_eq_case_1_6_row_0_0_4
  · exact right1Middle6_eq_case_1_6_row_0_0_5
  · exact right1Middle6_eq_case_1_6_row_0_0_6
  · exact right1Middle6_eq_case_1_6_row_0_0_7
  · exact right1Middle6_eq_case_1_6_row_1_0_0
  · exact right1Middle6_eq_case_1_6_row_1_0_1
  · exact right1Middle6_eq_case_1_6_row_1_0_2
  · exact right1Middle6_eq_case_1_6_row_1_0_3
  · exact right1Middle6_eq_case_1_6_row_1_0_4
  · exact right1Middle6_eq_case_1_6_row_1_0_5
  · exact right1Middle6_eq_case_1_6_row_1_0_6
  · exact right1Middle6_eq_case_1_6_row_1_0_7

set_option backward.isDefEq.respectTransparency false in
theorem right1Middle6_eq_case_1_6 : right1Middle6 1 6 = associatorInverseZ 6 6 1 * right0Middle6 1 6 := by
  simpa only [HexagonAtoms616.assocABC_eq,
    HexagonAtoms616.outerABC_eq,
    HexagonAtoms616.assocBAC_eq,
    HexagonAtoms616.innerABC_eq,
    HexagonAtoms616.innerRightABC_eq,
    HexagonAtoms616.inverseACB_eq,
    HexagonAtoms616.innerACB_eq,
    HexagonAtoms616.assocBCA_eq,
    HexagonAtoms616.innerRightBAC_eq,
    HexagonAtoms616.assocCAB_eq,
    HexagonAtoms616.outerLeftABC_eq,
    HexagonRowColumn616.assocBCA_alias,
    HexagonRowColumn616.product0_eq,
    HexagonRowColumn616.product1_eq,
    HexagonRowColumn616.product2_eq,
    HexagonRowColumn616.product3_eq,
    HexagonRowColumn616.product4_eq,
    HexagonRowColumn616.product5_eq,
    HexagonRowColumn616.product6_eq,
    HexagonRowColumn616.product7_eq] using right1Middle6_eq_case_1_6_checked

private theorem right2Middle6_eq_case_1_6_row_0_0_0 : (right2Middle6 1 6) ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8)) = (rowColumnMul HexagonRowColumn616.rows_innerACB HexagonRowColumn616.cols_right1) ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right2Middle6_eq_case_1_6_row_0_0_1 : (right2Middle6 1 6) ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8)) = (rowColumnMul HexagonRowColumn616.rows_innerACB HexagonRowColumn616.cols_right1) ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right2Middle6_eq_case_1_6_row_0_0_2 : (right2Middle6 1 6) ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8)) = (rowColumnMul HexagonRowColumn616.rows_innerACB HexagonRowColumn616.cols_right1) ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right2Middle6_eq_case_1_6_row_0_0_3 : (right2Middle6 1 6) ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8)) = (rowColumnMul HexagonRowColumn616.rows_innerACB HexagonRowColumn616.cols_right1) ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right2Middle6_eq_case_1_6_row_0_0_4 : (right2Middle6 1 6) ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8)) = (rowColumnMul HexagonRowColumn616.rows_innerACB HexagonRowColumn616.cols_right1) ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right2Middle6_eq_case_1_6_row_0_0_5 : (right2Middle6 1 6) ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8)) = (rowColumnMul HexagonRowColumn616.rows_innerACB HexagonRowColumn616.cols_right1) ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right2Middle6_eq_case_1_6_row_0_0_6 : (right2Middle6 1 6) ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8)) = (rowColumnMul HexagonRowColumn616.rows_innerACB HexagonRowColumn616.cols_right1) ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right2Middle6_eq_case_1_6_row_0_0_7 : (right2Middle6 1 6) ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8)) = (rowColumnMul HexagonRowColumn616.rows_innerACB HexagonRowColumn616.cols_right1) ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right2Middle6_eq_case_1_6_row_1_0_0 : (right2Middle6 1 6) ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8)) = (rowColumnMul HexagonRowColumn616.rows_innerACB HexagonRowColumn616.cols_right1) ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right2Middle6_eq_case_1_6_row_1_0_1 : (right2Middle6 1 6) ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8)) = (rowColumnMul HexagonRowColumn616.rows_innerACB HexagonRowColumn616.cols_right1) ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right2Middle6_eq_case_1_6_row_1_0_2 : (right2Middle6 1 6) ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8)) = (rowColumnMul HexagonRowColumn616.rows_innerACB HexagonRowColumn616.cols_right1) ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right2Middle6_eq_case_1_6_row_1_0_3 : (right2Middle6 1 6) ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8)) = (rowColumnMul HexagonRowColumn616.rows_innerACB HexagonRowColumn616.cols_right1) ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right2Middle6_eq_case_1_6_row_1_0_4 : (right2Middle6 1 6) ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8)) = (rowColumnMul HexagonRowColumn616.rows_innerACB HexagonRowColumn616.cols_right1) ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right2Middle6_eq_case_1_6_row_1_0_5 : (right2Middle6 1 6) ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8)) = (rowColumnMul HexagonRowColumn616.rows_innerACB HexagonRowColumn616.cols_right1) ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right2Middle6_eq_case_1_6_row_1_0_6 : (right2Middle6 1 6) ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8)) = (rowColumnMul HexagonRowColumn616.rows_innerACB HexagonRowColumn616.cols_right1) ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right2Middle6_eq_case_1_6_row_1_0_7 : (right2Middle6 1 6) ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8)) = (rowColumnMul HexagonRowColumn616.rows_innerACB HexagonRowColumn616.cols_right1) ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right2Middle6_eq_case_1_6_checked : right2Middle6 1 6 = rowColumnMul HexagonRowColumn616.rows_innerACB HexagonRowColumn616.cols_right1 := by
  funext r
  fin_cases r
  · exact right2Middle6_eq_case_1_6_row_0_0_0
  · exact right2Middle6_eq_case_1_6_row_0_0_1
  · exact right2Middle6_eq_case_1_6_row_0_0_2
  · exact right2Middle6_eq_case_1_6_row_0_0_3
  · exact right2Middle6_eq_case_1_6_row_0_0_4
  · exact right2Middle6_eq_case_1_6_row_0_0_5
  · exact right2Middle6_eq_case_1_6_row_0_0_6
  · exact right2Middle6_eq_case_1_6_row_0_0_7
  · exact right2Middle6_eq_case_1_6_row_1_0_0
  · exact right2Middle6_eq_case_1_6_row_1_0_1
  · exact right2Middle6_eq_case_1_6_row_1_0_2
  · exact right2Middle6_eq_case_1_6_row_1_0_3
  · exact right2Middle6_eq_case_1_6_row_1_0_4
  · exact right2Middle6_eq_case_1_6_row_1_0_5
  · exact right2Middle6_eq_case_1_6_row_1_0_6
  · exact right2Middle6_eq_case_1_6_row_1_0_7

set_option backward.isDefEq.respectTransparency false in
theorem right2Middle6_eq_case_1_6 : right2Middle6 1 6 = innerLeftZ 6 6 1 * right1Middle6 1 6 := by
  simpa only [HexagonAtoms616.assocABC_eq,
    HexagonAtoms616.outerABC_eq,
    HexagonAtoms616.assocBAC_eq,
    HexagonAtoms616.innerABC_eq,
    HexagonAtoms616.innerRightABC_eq,
    HexagonAtoms616.inverseACB_eq,
    HexagonAtoms616.innerACB_eq,
    HexagonAtoms616.assocBCA_eq,
    HexagonAtoms616.innerRightBAC_eq,
    HexagonAtoms616.assocCAB_eq,
    HexagonAtoms616.outerLeftABC_eq,
    HexagonRowColumn616.assocBCA_alias,
    HexagonRowColumn616.product0_eq,
    HexagonRowColumn616.product1_eq,
    HexagonRowColumn616.product2_eq,
    HexagonRowColumn616.product3_eq,
    HexagonRowColumn616.product4_eq,
    HexagonRowColumn616.product5_eq,
    HexagonRowColumn616.product6_eq,
    HexagonRowColumn616.product7_eq] using right2Middle6_eq_case_1_6_checked

private theorem leftFinal6_case_1_6_row_0_0_0 : (((-1 : ℤ) ^ (leftScaleBit 6 1 6).val * positiveScale (leftScaleExponent 6 1 6)) •
      (rowColumnMul HexagonRowColumn616.rows_assocBAC HexagonRowColumn616.cols_left0)) ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8)) = (negativeScale (leftScaleExponent 6 1 6) • (rowColumnMul HexagonRowColumn616.rows_innerRightBAC HexagonRowColumn616.cols_left1)) ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem leftFinal6_case_1_6_row_0_0_1 : (((-1 : ℤ) ^ (leftScaleBit 6 1 6).val * positiveScale (leftScaleExponent 6 1 6)) •
      (rowColumnMul HexagonRowColumn616.rows_assocBAC HexagonRowColumn616.cols_left0)) ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8)) = (negativeScale (leftScaleExponent 6 1 6) • (rowColumnMul HexagonRowColumn616.rows_innerRightBAC HexagonRowColumn616.cols_left1)) ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem leftFinal6_case_1_6_row_0_0_2 : (((-1 : ℤ) ^ (leftScaleBit 6 1 6).val * positiveScale (leftScaleExponent 6 1 6)) •
      (rowColumnMul HexagonRowColumn616.rows_assocBAC HexagonRowColumn616.cols_left0)) ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8)) = (negativeScale (leftScaleExponent 6 1 6) • (rowColumnMul HexagonRowColumn616.rows_innerRightBAC HexagonRowColumn616.cols_left1)) ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem leftFinal6_case_1_6_row_0_0_3 : (((-1 : ℤ) ^ (leftScaleBit 6 1 6).val * positiveScale (leftScaleExponent 6 1 6)) •
      (rowColumnMul HexagonRowColumn616.rows_assocBAC HexagonRowColumn616.cols_left0)) ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8)) = (negativeScale (leftScaleExponent 6 1 6) • (rowColumnMul HexagonRowColumn616.rows_innerRightBAC HexagonRowColumn616.cols_left1)) ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem leftFinal6_case_1_6_row_0_0_4 : (((-1 : ℤ) ^ (leftScaleBit 6 1 6).val * positiveScale (leftScaleExponent 6 1 6)) •
      (rowColumnMul HexagonRowColumn616.rows_assocBAC HexagonRowColumn616.cols_left0)) ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8)) = (negativeScale (leftScaleExponent 6 1 6) • (rowColumnMul HexagonRowColumn616.rows_innerRightBAC HexagonRowColumn616.cols_left1)) ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem leftFinal6_case_1_6_row_0_0_5 : (((-1 : ℤ) ^ (leftScaleBit 6 1 6).val * positiveScale (leftScaleExponent 6 1 6)) •
      (rowColumnMul HexagonRowColumn616.rows_assocBAC HexagonRowColumn616.cols_left0)) ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8)) = (negativeScale (leftScaleExponent 6 1 6) • (rowColumnMul HexagonRowColumn616.rows_innerRightBAC HexagonRowColumn616.cols_left1)) ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem leftFinal6_case_1_6_row_0_0_6 : (((-1 : ℤ) ^ (leftScaleBit 6 1 6).val * positiveScale (leftScaleExponent 6 1 6)) •
      (rowColumnMul HexagonRowColumn616.rows_assocBAC HexagonRowColumn616.cols_left0)) ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8)) = (negativeScale (leftScaleExponent 6 1 6) • (rowColumnMul HexagonRowColumn616.rows_innerRightBAC HexagonRowColumn616.cols_left1)) ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem leftFinal6_case_1_6_row_0_0_7 : (((-1 : ℤ) ^ (leftScaleBit 6 1 6).val * positiveScale (leftScaleExponent 6 1 6)) •
      (rowColumnMul HexagonRowColumn616.rows_assocBAC HexagonRowColumn616.cols_left0)) ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8)) = (negativeScale (leftScaleExponent 6 1 6) • (rowColumnMul HexagonRowColumn616.rows_innerRightBAC HexagonRowColumn616.cols_left1)) ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem leftFinal6_case_1_6_row_1_0_0 : (((-1 : ℤ) ^ (leftScaleBit 6 1 6).val * positiveScale (leftScaleExponent 6 1 6)) •
      (rowColumnMul HexagonRowColumn616.rows_assocBAC HexagonRowColumn616.cols_left0)) ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8)) = (negativeScale (leftScaleExponent 6 1 6) • (rowColumnMul HexagonRowColumn616.rows_innerRightBAC HexagonRowColumn616.cols_left1)) ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem leftFinal6_case_1_6_row_1_0_1 : (((-1 : ℤ) ^ (leftScaleBit 6 1 6).val * positiveScale (leftScaleExponent 6 1 6)) •
      (rowColumnMul HexagonRowColumn616.rows_assocBAC HexagonRowColumn616.cols_left0)) ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8)) = (negativeScale (leftScaleExponent 6 1 6) • (rowColumnMul HexagonRowColumn616.rows_innerRightBAC HexagonRowColumn616.cols_left1)) ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem leftFinal6_case_1_6_row_1_0_2 : (((-1 : ℤ) ^ (leftScaleBit 6 1 6).val * positiveScale (leftScaleExponent 6 1 6)) •
      (rowColumnMul HexagonRowColumn616.rows_assocBAC HexagonRowColumn616.cols_left0)) ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8)) = (negativeScale (leftScaleExponent 6 1 6) • (rowColumnMul HexagonRowColumn616.rows_innerRightBAC HexagonRowColumn616.cols_left1)) ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem leftFinal6_case_1_6_row_1_0_3 : (((-1 : ℤ) ^ (leftScaleBit 6 1 6).val * positiveScale (leftScaleExponent 6 1 6)) •
      (rowColumnMul HexagonRowColumn616.rows_assocBAC HexagonRowColumn616.cols_left0)) ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8)) = (negativeScale (leftScaleExponent 6 1 6) • (rowColumnMul HexagonRowColumn616.rows_innerRightBAC HexagonRowColumn616.cols_left1)) ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem leftFinal6_case_1_6_row_1_0_4 : (((-1 : ℤ) ^ (leftScaleBit 6 1 6).val * positiveScale (leftScaleExponent 6 1 6)) •
      (rowColumnMul HexagonRowColumn616.rows_assocBAC HexagonRowColumn616.cols_left0)) ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8)) = (negativeScale (leftScaleExponent 6 1 6) • (rowColumnMul HexagonRowColumn616.rows_innerRightBAC HexagonRowColumn616.cols_left1)) ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem leftFinal6_case_1_6_row_1_0_5 : (((-1 : ℤ) ^ (leftScaleBit 6 1 6).val * positiveScale (leftScaleExponent 6 1 6)) •
      (rowColumnMul HexagonRowColumn616.rows_assocBAC HexagonRowColumn616.cols_left0)) ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8)) = (negativeScale (leftScaleExponent 6 1 6) • (rowColumnMul HexagonRowColumn616.rows_innerRightBAC HexagonRowColumn616.cols_left1)) ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem leftFinal6_case_1_6_row_1_0_6 : (((-1 : ℤ) ^ (leftScaleBit 6 1 6).val * positiveScale (leftScaleExponent 6 1 6)) •
      (rowColumnMul HexagonRowColumn616.rows_assocBAC HexagonRowColumn616.cols_left0)) ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8)) = (negativeScale (leftScaleExponent 6 1 6) • (rowColumnMul HexagonRowColumn616.rows_innerRightBAC HexagonRowColumn616.cols_left1)) ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem leftFinal6_case_1_6_row_1_0_7 : (((-1 : ℤ) ^ (leftScaleBit 6 1 6).val * positiveScale (leftScaleExponent 6 1 6)) •
      (rowColumnMul HexagonRowColumn616.rows_assocBAC HexagonRowColumn616.cols_left0)) ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8)) = (negativeScale (leftScaleExponent 6 1 6) • (rowColumnMul HexagonRowColumn616.rows_innerRightBAC HexagonRowColumn616.cols_left1)) ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem leftFinal6_case_1_6_checked : ((-1 : ℤ) ^ (leftScaleBit 6 1 6).val * positiveScale (leftScaleExponent 6 1 6)) •
      (rowColumnMul HexagonRowColumn616.rows_assocBAC HexagonRowColumn616.cols_left0) = negativeScale (leftScaleExponent 6 1 6) • (rowColumnMul HexagonRowColumn616.rows_innerRightBAC HexagonRowColumn616.cols_left1) := by
  funext r
  fin_cases r
  · exact leftFinal6_case_1_6_row_0_0_0
  · exact leftFinal6_case_1_6_row_0_0_1
  · exact leftFinal6_case_1_6_row_0_0_2
  · exact leftFinal6_case_1_6_row_0_0_3
  · exact leftFinal6_case_1_6_row_0_0_4
  · exact leftFinal6_case_1_6_row_0_0_5
  · exact leftFinal6_case_1_6_row_0_0_6
  · exact leftFinal6_case_1_6_row_0_0_7
  · exact leftFinal6_case_1_6_row_1_0_0
  · exact leftFinal6_case_1_6_row_1_0_1
  · exact leftFinal6_case_1_6_row_1_0_2
  · exact leftFinal6_case_1_6_row_1_0_3
  · exact leftFinal6_case_1_6_row_1_0_4
  · exact leftFinal6_case_1_6_row_1_0_5
  · exact leftFinal6_case_1_6_row_1_0_6
  · exact leftFinal6_case_1_6_row_1_0_7

set_option backward.isDefEq.respectTransparency false in
theorem leftFinal6_case_1_6 : ((-1 : ℤ) ^ (leftScaleBit 6 1 6).val * positiveScale (leftScaleExponent 6 1 6)) •
      (associatorZ 1 6 6 * left0Middle6 1 6) = negativeScale (leftScaleExponent 6 1 6) • (innerRightZ 1 6 6 * left1Middle6 1 6) := by
  simpa only [HexagonAtoms616.assocABC_eq,
    HexagonAtoms616.outerABC_eq,
    HexagonAtoms616.assocBAC_eq,
    HexagonAtoms616.innerABC_eq,
    HexagonAtoms616.innerRightABC_eq,
    HexagonAtoms616.inverseACB_eq,
    HexagonAtoms616.innerACB_eq,
    HexagonAtoms616.assocBCA_eq,
    HexagonAtoms616.innerRightBAC_eq,
    HexagonAtoms616.assocCAB_eq,
    HexagonAtoms616.outerLeftABC_eq,
    HexagonRowColumn616.assocBCA_alias,
    HexagonRowColumn616.product0_eq,
    HexagonRowColumn616.product1_eq,
    HexagonRowColumn616.product2_eq,
    HexagonRowColumn616.product3_eq,
    HexagonRowColumn616.product4_eq,
    HexagonRowColumn616.product5_eq,
    HexagonRowColumn616.product6_eq,
    HexagonRowColumn616.product7_eq] using leftFinal6_case_1_6_checked

private theorem rightFinal6_case_1_6_row_0_0_0 : (((-1 : ℤ) ^ (rightScaleBit 6 1 6).val * positiveScale (rightScaleExponent 6 1 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 6 1 : ℤ)) • HexagonAtoms616.outerLeftABC) ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8)) = (negativeScale (rightScaleExponent 6 1 6) • (rowColumnMul HexagonRowColumn616.rows_assocCAB HexagonRowColumn616.cols_right2)) ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem rightFinal6_case_1_6_row_0_0_1 : (((-1 : ℤ) ^ (rightScaleBit 6 1 6).val * positiveScale (rightScaleExponent 6 1 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 6 1 : ℤ)) • HexagonAtoms616.outerLeftABC) ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8)) = (negativeScale (rightScaleExponent 6 1 6) • (rowColumnMul HexagonRowColumn616.rows_assocCAB HexagonRowColumn616.cols_right2)) ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem rightFinal6_case_1_6_row_0_0_2 : (((-1 : ℤ) ^ (rightScaleBit 6 1 6).val * positiveScale (rightScaleExponent 6 1 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 6 1 : ℤ)) • HexagonAtoms616.outerLeftABC) ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8)) = (negativeScale (rightScaleExponent 6 1 6) • (rowColumnMul HexagonRowColumn616.rows_assocCAB HexagonRowColumn616.cols_right2)) ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem rightFinal6_case_1_6_row_0_0_3 : (((-1 : ℤ) ^ (rightScaleBit 6 1 6).val * positiveScale (rightScaleExponent 6 1 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 6 1 : ℤ)) • HexagonAtoms616.outerLeftABC) ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8)) = (negativeScale (rightScaleExponent 6 1 6) • (rowColumnMul HexagonRowColumn616.rows_assocCAB HexagonRowColumn616.cols_right2)) ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem rightFinal6_case_1_6_row_0_0_4 : (((-1 : ℤ) ^ (rightScaleBit 6 1 6).val * positiveScale (rightScaleExponent 6 1 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 6 1 : ℤ)) • HexagonAtoms616.outerLeftABC) ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8)) = (negativeScale (rightScaleExponent 6 1 6) • (rowColumnMul HexagonRowColumn616.rows_assocCAB HexagonRowColumn616.cols_right2)) ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem rightFinal6_case_1_6_row_0_0_5 : (((-1 : ℤ) ^ (rightScaleBit 6 1 6).val * positiveScale (rightScaleExponent 6 1 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 6 1 : ℤ)) • HexagonAtoms616.outerLeftABC) ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8)) = (negativeScale (rightScaleExponent 6 1 6) • (rowColumnMul HexagonRowColumn616.rows_assocCAB HexagonRowColumn616.cols_right2)) ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem rightFinal6_case_1_6_row_0_0_6 : (((-1 : ℤ) ^ (rightScaleBit 6 1 6).val * positiveScale (rightScaleExponent 6 1 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 6 1 : ℤ)) • HexagonAtoms616.outerLeftABC) ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8)) = (negativeScale (rightScaleExponent 6 1 6) • (rowColumnMul HexagonRowColumn616.rows_assocCAB HexagonRowColumn616.cols_right2)) ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem rightFinal6_case_1_6_row_0_0_7 : (((-1 : ℤ) ^ (rightScaleBit 6 1 6).val * positiveScale (rightScaleExponent 6 1 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 6 1 : ℤ)) • HexagonAtoms616.outerLeftABC) ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8)) = (negativeScale (rightScaleExponent 6 1 6) • (rowColumnMul HexagonRowColumn616.rows_assocCAB HexagonRowColumn616.cols_right2)) ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem rightFinal6_case_1_6_row_1_0_0 : (((-1 : ℤ) ^ (rightScaleBit 6 1 6).val * positiveScale (rightScaleExponent 6 1 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 6 1 : ℤ)) • HexagonAtoms616.outerLeftABC) ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8)) = (negativeScale (rightScaleExponent 6 1 6) • (rowColumnMul HexagonRowColumn616.rows_assocCAB HexagonRowColumn616.cols_right2)) ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem rightFinal6_case_1_6_row_1_0_1 : (((-1 : ℤ) ^ (rightScaleBit 6 1 6).val * positiveScale (rightScaleExponent 6 1 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 6 1 : ℤ)) • HexagonAtoms616.outerLeftABC) ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8)) = (negativeScale (rightScaleExponent 6 1 6) • (rowColumnMul HexagonRowColumn616.rows_assocCAB HexagonRowColumn616.cols_right2)) ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem rightFinal6_case_1_6_row_1_0_2 : (((-1 : ℤ) ^ (rightScaleBit 6 1 6).val * positiveScale (rightScaleExponent 6 1 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 6 1 : ℤ)) • HexagonAtoms616.outerLeftABC) ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8)) = (negativeScale (rightScaleExponent 6 1 6) • (rowColumnMul HexagonRowColumn616.rows_assocCAB HexagonRowColumn616.cols_right2)) ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem rightFinal6_case_1_6_row_1_0_3 : (((-1 : ℤ) ^ (rightScaleBit 6 1 6).val * positiveScale (rightScaleExponent 6 1 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 6 1 : ℤ)) • HexagonAtoms616.outerLeftABC) ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8)) = (negativeScale (rightScaleExponent 6 1 6) • (rowColumnMul HexagonRowColumn616.rows_assocCAB HexagonRowColumn616.cols_right2)) ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem rightFinal6_case_1_6_row_1_0_4 : (((-1 : ℤ) ^ (rightScaleBit 6 1 6).val * positiveScale (rightScaleExponent 6 1 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 6 1 : ℤ)) • HexagonAtoms616.outerLeftABC) ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8)) = (negativeScale (rightScaleExponent 6 1 6) • (rowColumnMul HexagonRowColumn616.rows_assocCAB HexagonRowColumn616.cols_right2)) ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem rightFinal6_case_1_6_row_1_0_5 : (((-1 : ℤ) ^ (rightScaleBit 6 1 6).val * positiveScale (rightScaleExponent 6 1 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 6 1 : ℤ)) • HexagonAtoms616.outerLeftABC) ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8)) = (negativeScale (rightScaleExponent 6 1 6) • (rowColumnMul HexagonRowColumn616.rows_assocCAB HexagonRowColumn616.cols_right2)) ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem rightFinal6_case_1_6_row_1_0_6 : (((-1 : ℤ) ^ (rightScaleBit 6 1 6).val * positiveScale (rightScaleExponent 6 1 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 6 1 : ℤ)) • HexagonAtoms616.outerLeftABC) ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8)) = (negativeScale (rightScaleExponent 6 1 6) • (rowColumnMul HexagonRowColumn616.rows_assocCAB HexagonRowColumn616.cols_right2)) ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem rightFinal6_case_1_6_row_1_0_7 : (((-1 : ℤ) ^ (rightScaleBit 6 1 6).val * positiveScale (rightScaleExponent 6 1 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 6 1 : ℤ)) • HexagonAtoms616.outerLeftABC) ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8)) = (negativeScale (rightScaleExponent 6 1 6) • (rowColumnMul HexagonRowColumn616.rows_assocCAB HexagonRowColumn616.cols_right2)) ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem rightFinal6_case_1_6_checked : ((-1 : ℤ) ^ (rightScaleBit 6 1 6).val * positiveScale (rightScaleExponent 6 1 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 6 1 : ℤ)) • HexagonAtoms616.outerLeftABC = negativeScale (rightScaleExponent 6 1 6) • (rowColumnMul HexagonRowColumn616.rows_assocCAB HexagonRowColumn616.cols_right2) := by
  funext r
  fin_cases r
  · exact rightFinal6_case_1_6_row_0_0_0
  · exact rightFinal6_case_1_6_row_0_0_1
  · exact rightFinal6_case_1_6_row_0_0_2
  · exact rightFinal6_case_1_6_row_0_0_3
  · exact rightFinal6_case_1_6_row_0_0_4
  · exact rightFinal6_case_1_6_row_0_0_5
  · exact rightFinal6_case_1_6_row_0_0_6
  · exact rightFinal6_case_1_6_row_0_0_7
  · exact rightFinal6_case_1_6_row_1_0_0
  · exact rightFinal6_case_1_6_row_1_0_1
  · exact rightFinal6_case_1_6_row_1_0_2
  · exact rightFinal6_case_1_6_row_1_0_3
  · exact rightFinal6_case_1_6_row_1_0_4
  · exact rightFinal6_case_1_6_row_1_0_5
  · exact rightFinal6_case_1_6_row_1_0_6
  · exact rightFinal6_case_1_6_row_1_0_7

set_option backward.isDefEq.respectTransparency false in
theorem rightFinal6_case_1_6 : ((-1 : ℤ) ^ (rightScaleBit 6 1 6).val * positiveScale (rightScaleExponent 6 1 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 6 1 : ℤ)) • outerLeftZ 6 1 6 = negativeScale (rightScaleExponent 6 1 6) • (associatorZ 6 6 1 * right2Middle6 1 6) := by
  simpa only [HexagonAtoms616.assocABC_eq,
    HexagonAtoms616.outerABC_eq,
    HexagonAtoms616.assocBAC_eq,
    HexagonAtoms616.innerABC_eq,
    HexagonAtoms616.innerRightABC_eq,
    HexagonAtoms616.inverseACB_eq,
    HexagonAtoms616.innerACB_eq,
    HexagonAtoms616.assocBCA_eq,
    HexagonAtoms616.innerRightBAC_eq,
    HexagonAtoms616.assocCAB_eq,
    HexagonAtoms616.outerLeftABC_eq,
    HexagonRowColumn616.assocBCA_alias,
    HexagonRowColumn616.product0_eq,
    HexagonRowColumn616.product1_eq,
    HexagonRowColumn616.product2_eq,
    HexagonRowColumn616.product3_eq,
    HexagonRowColumn616.product4_eq,
    HexagonRowColumn616.product5_eq,
    HexagonRowColumn616.product6_eq,
    HexagonRowColumn616.product7_eq] using rightFinal6_case_1_6_checked

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonCases6
