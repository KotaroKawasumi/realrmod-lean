import RMod.BrundanEllis.StackingReferenceHexagonMiddle6
import RMod.BrundanEllis.StackingReferenceSparseMatrixCheck
import RMod.BrundanEllis.StackingReferenceHexagonAtoms665
import RMod.BrundanEllis.StackingReferenceHexagonRowColumn665

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

private theorem left0Middle6_eq_case_6_5_row_0_0_0 : (left0Middle6 6 5) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (HexagonAtoms665.assocABC) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle6_eq_case_6_5_row_0_0_1 : (left0Middle6 6 5) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (HexagonAtoms665.assocABC) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle6_eq_case_6_5_row_0_1_0 : (left0Middle6 6 5) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (HexagonAtoms665.assocABC) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle6_eq_case_6_5_row_0_1_1 : (left0Middle6 6 5) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (HexagonAtoms665.assocABC) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle6_eq_case_6_5_row_0_2_0 : (left0Middle6 6 5) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (HexagonAtoms665.assocABC) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle6_eq_case_6_5_row_0_2_1 : (left0Middle6 6 5) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (HexagonAtoms665.assocABC) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle6_eq_case_6_5_row_0_3_0 : (left0Middle6 6 5) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (HexagonAtoms665.assocABC) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle6_eq_case_6_5_row_0_3_1 : (left0Middle6 6 5) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (HexagonAtoms665.assocABC) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle6_eq_case_6_5_row_1_0_0 : (left0Middle6 6 5) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (HexagonAtoms665.assocABC) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle6_eq_case_6_5_row_1_0_1 : (left0Middle6 6 5) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (HexagonAtoms665.assocABC) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle6_eq_case_6_5_row_1_1_0 : (left0Middle6 6 5) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (HexagonAtoms665.assocABC) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle6_eq_case_6_5_row_1_1_1 : (left0Middle6 6 5) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (HexagonAtoms665.assocABC) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle6_eq_case_6_5_row_1_2_0 : (left0Middle6 6 5) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (HexagonAtoms665.assocABC) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle6_eq_case_6_5_row_1_2_1 : (left0Middle6 6 5) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (HexagonAtoms665.assocABC) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle6_eq_case_6_5_row_1_3_0 : (left0Middle6 6 5) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (HexagonAtoms665.assocABC) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle6_eq_case_6_5_row_1_3_1 : (left0Middle6 6 5) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (HexagonAtoms665.assocABC) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle6_eq_case_6_5_checked : left0Middle6 6 5 = HexagonAtoms665.assocABC := by
  funext r
  fin_cases r
  · exact left0Middle6_eq_case_6_5_row_0_0_0
  · exact left0Middle6_eq_case_6_5_row_0_0_1
  · exact left0Middle6_eq_case_6_5_row_0_1_0
  · exact left0Middle6_eq_case_6_5_row_0_1_1
  · exact left0Middle6_eq_case_6_5_row_0_2_0
  · exact left0Middle6_eq_case_6_5_row_0_2_1
  · exact left0Middle6_eq_case_6_5_row_0_3_0
  · exact left0Middle6_eq_case_6_5_row_0_3_1
  · exact left0Middle6_eq_case_6_5_row_1_0_0
  · exact left0Middle6_eq_case_6_5_row_1_0_1
  · exact left0Middle6_eq_case_6_5_row_1_1_0
  · exact left0Middle6_eq_case_6_5_row_1_1_1
  · exact left0Middle6_eq_case_6_5_row_1_2_0
  · exact left0Middle6_eq_case_6_5_row_1_2_1
  · exact left0Middle6_eq_case_6_5_row_1_3_0
  · exact left0Middle6_eq_case_6_5_row_1_3_1

set_option backward.isDefEq.respectTransparency false in
theorem left0Middle6_eq_case_6_5 : left0Middle6 6 5 = outerRightZ 6 6 5 * associatorZ 6 6 5 := by
  simpa only [HexagonAtoms665.assocABC_eq,
    HexagonAtoms665.outerABC_eq,
    HexagonAtoms665.assocBAC_eq,
    HexagonAtoms665.innerABC_eq,
    HexagonAtoms665.innerRightABC_eq,
    HexagonAtoms665.inverseACB_eq,
    HexagonAtoms665.innerACB_eq,
    HexagonAtoms665.assocBCA_eq,
    HexagonAtoms665.innerRightBAC_eq,
    HexagonAtoms665.assocCAB_eq,
    HexagonAtoms665.outerLeftABC_eq,
    HexagonRowColumn665.assocBAC_alias,
    HexagonRowColumn665.innerRightBAC_alias,
    HexagonRowColumn665.product0_eq,
    HexagonRowColumn665.product1_eq,
    HexagonRowColumn665.product2_eq,
    HexagonRowColumn665.product3_eq,
    HexagonRowColumn665.product4_eq,
    HexagonRowColumn665.product5_eq,
    HexagonRowColumn665.product6_eq,
    HexagonRowColumn665.product7_eq] using left0Middle6_eq_case_6_5_checked

private theorem left1Middle6_eq_case_6_5_row_0_0_0 : (left1Middle6 6 5) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn665.rows_assocABC HexagonRowColumn665.cols_innerABC) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle6_eq_case_6_5_row_0_0_1 : (left1Middle6 6 5) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn665.rows_assocABC HexagonRowColumn665.cols_innerABC) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle6_eq_case_6_5_row_0_1_0 : (left1Middle6 6 5) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn665.rows_assocABC HexagonRowColumn665.cols_innerABC) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle6_eq_case_6_5_row_0_1_1 : (left1Middle6 6 5) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn665.rows_assocABC HexagonRowColumn665.cols_innerABC) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle6_eq_case_6_5_row_0_2_0 : (left1Middle6 6 5) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn665.rows_assocABC HexagonRowColumn665.cols_innerABC) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle6_eq_case_6_5_row_0_2_1 : (left1Middle6 6 5) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn665.rows_assocABC HexagonRowColumn665.cols_innerABC) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle6_eq_case_6_5_row_0_3_0 : (left1Middle6 6 5) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn665.rows_assocABC HexagonRowColumn665.cols_innerABC) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle6_eq_case_6_5_row_0_3_1 : (left1Middle6 6 5) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn665.rows_assocABC HexagonRowColumn665.cols_innerABC) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle6_eq_case_6_5_row_1_0_0 : (left1Middle6 6 5) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn665.rows_assocABC HexagonRowColumn665.cols_innerABC) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle6_eq_case_6_5_row_1_0_1 : (left1Middle6 6 5) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn665.rows_assocABC HexagonRowColumn665.cols_innerABC) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle6_eq_case_6_5_row_1_1_0 : (left1Middle6 6 5) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn665.rows_assocABC HexagonRowColumn665.cols_innerABC) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle6_eq_case_6_5_row_1_1_1 : (left1Middle6 6 5) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn665.rows_assocABC HexagonRowColumn665.cols_innerABC) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle6_eq_case_6_5_row_1_2_0 : (left1Middle6 6 5) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn665.rows_assocABC HexagonRowColumn665.cols_innerABC) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle6_eq_case_6_5_row_1_2_1 : (left1Middle6 6 5) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn665.rows_assocABC HexagonRowColumn665.cols_innerABC) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle6_eq_case_6_5_row_1_3_0 : (left1Middle6 6 5) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn665.rows_assocABC HexagonRowColumn665.cols_innerABC) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle6_eq_case_6_5_row_1_3_1 : (left1Middle6 6 5) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn665.rows_assocABC HexagonRowColumn665.cols_innerABC) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle6_eq_case_6_5_checked : left1Middle6 6 5 = rowColumnMul HexagonRowColumn665.rows_assocABC HexagonRowColumn665.cols_innerABC := by
  funext r
  fin_cases r
  · exact left1Middle6_eq_case_6_5_row_0_0_0
  · exact left1Middle6_eq_case_6_5_row_0_0_1
  · exact left1Middle6_eq_case_6_5_row_0_1_0
  · exact left1Middle6_eq_case_6_5_row_0_1_1
  · exact left1Middle6_eq_case_6_5_row_0_2_0
  · exact left1Middle6_eq_case_6_5_row_0_2_1
  · exact left1Middle6_eq_case_6_5_row_0_3_0
  · exact left1Middle6_eq_case_6_5_row_0_3_1
  · exact left1Middle6_eq_case_6_5_row_1_0_0
  · exact left1Middle6_eq_case_6_5_row_1_0_1
  · exact left1Middle6_eq_case_6_5_row_1_1_0
  · exact left1Middle6_eq_case_6_5_row_1_1_1
  · exact left1Middle6_eq_case_6_5_row_1_2_0
  · exact left1Middle6_eq_case_6_5_row_1_2_1
  · exact left1Middle6_eq_case_6_5_row_1_3_0
  · exact left1Middle6_eq_case_6_5_row_1_3_1

set_option backward.isDefEq.respectTransparency false in
theorem left1Middle6_eq_case_6_5 : left1Middle6 6 5 = associatorZ 6 6 5 * innerLeftZ 6 6 5 := by
  simpa only [HexagonAtoms665.assocABC_eq,
    HexagonAtoms665.outerABC_eq,
    HexagonAtoms665.assocBAC_eq,
    HexagonAtoms665.innerABC_eq,
    HexagonAtoms665.innerRightABC_eq,
    HexagonAtoms665.inverseACB_eq,
    HexagonAtoms665.innerACB_eq,
    HexagonAtoms665.assocBCA_eq,
    HexagonAtoms665.innerRightBAC_eq,
    HexagonAtoms665.assocCAB_eq,
    HexagonAtoms665.outerLeftABC_eq,
    HexagonRowColumn665.assocBAC_alias,
    HexagonRowColumn665.innerRightBAC_alias,
    HexagonRowColumn665.product0_eq,
    HexagonRowColumn665.product1_eq,
    HexagonRowColumn665.product2_eq,
    HexagonRowColumn665.product3_eq,
    HexagonRowColumn665.product4_eq,
    HexagonRowColumn665.product5_eq,
    HexagonRowColumn665.product6_eq,
    HexagonRowColumn665.product7_eq] using left1Middle6_eq_case_6_5_checked

private theorem right0Middle6_eq_case_6_5_row_0_0_0 : (right0Middle6 6 5) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (HexagonAtoms665.assocABC) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle6_eq_case_6_5_row_0_0_1 : (right0Middle6 6 5) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (HexagonAtoms665.assocABC) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle6_eq_case_6_5_row_0_1_0 : (right0Middle6 6 5) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (HexagonAtoms665.assocABC) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle6_eq_case_6_5_row_0_1_1 : (right0Middle6 6 5) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (HexagonAtoms665.assocABC) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle6_eq_case_6_5_row_0_2_0 : (right0Middle6 6 5) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (HexagonAtoms665.assocABC) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle6_eq_case_6_5_row_0_2_1 : (right0Middle6 6 5) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (HexagonAtoms665.assocABC) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle6_eq_case_6_5_row_0_3_0 : (right0Middle6 6 5) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (HexagonAtoms665.assocABC) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle6_eq_case_6_5_row_0_3_1 : (right0Middle6 6 5) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (HexagonAtoms665.assocABC) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle6_eq_case_6_5_row_1_0_0 : (right0Middle6 6 5) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (HexagonAtoms665.assocABC) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle6_eq_case_6_5_row_1_0_1 : (right0Middle6 6 5) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (HexagonAtoms665.assocABC) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle6_eq_case_6_5_row_1_1_0 : (right0Middle6 6 5) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (HexagonAtoms665.assocABC) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle6_eq_case_6_5_row_1_1_1 : (right0Middle6 6 5) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (HexagonAtoms665.assocABC) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle6_eq_case_6_5_row_1_2_0 : (right0Middle6 6 5) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (HexagonAtoms665.assocABC) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle6_eq_case_6_5_row_1_2_1 : (right0Middle6 6 5) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (HexagonAtoms665.assocABC) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle6_eq_case_6_5_row_1_3_0 : (right0Middle6 6 5) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (HexagonAtoms665.assocABC) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle6_eq_case_6_5_row_1_3_1 : (right0Middle6 6 5) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (HexagonAtoms665.assocABC) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle6_eq_case_6_5_checked : right0Middle6 6 5 = HexagonAtoms665.assocABC := by
  funext r
  fin_cases r
  · exact right0Middle6_eq_case_6_5_row_0_0_0
  · exact right0Middle6_eq_case_6_5_row_0_0_1
  · exact right0Middle6_eq_case_6_5_row_0_1_0
  · exact right0Middle6_eq_case_6_5_row_0_1_1
  · exact right0Middle6_eq_case_6_5_row_0_2_0
  · exact right0Middle6_eq_case_6_5_row_0_2_1
  · exact right0Middle6_eq_case_6_5_row_0_3_0
  · exact right0Middle6_eq_case_6_5_row_0_3_1
  · exact right0Middle6_eq_case_6_5_row_1_0_0
  · exact right0Middle6_eq_case_6_5_row_1_0_1
  · exact right0Middle6_eq_case_6_5_row_1_1_0
  · exact right0Middle6_eq_case_6_5_row_1_1_1
  · exact right0Middle6_eq_case_6_5_row_1_2_0
  · exact right0Middle6_eq_case_6_5_row_1_2_1
  · exact right0Middle6_eq_case_6_5_row_1_3_0
  · exact right0Middle6_eq_case_6_5_row_1_3_1

set_option backward.isDefEq.respectTransparency false in
theorem right0Middle6_eq_case_6_5 : right0Middle6 6 5 = innerRightZ 6 6 5 * associatorZ 6 6 5 := by
  simpa only [HexagonAtoms665.assocABC_eq,
    HexagonAtoms665.outerABC_eq,
    HexagonAtoms665.assocBAC_eq,
    HexagonAtoms665.innerABC_eq,
    HexagonAtoms665.innerRightABC_eq,
    HexagonAtoms665.inverseACB_eq,
    HexagonAtoms665.innerACB_eq,
    HexagonAtoms665.assocBCA_eq,
    HexagonAtoms665.innerRightBAC_eq,
    HexagonAtoms665.assocCAB_eq,
    HexagonAtoms665.outerLeftABC_eq,
    HexagonRowColumn665.assocBAC_alias,
    HexagonRowColumn665.innerRightBAC_alias,
    HexagonRowColumn665.product0_eq,
    HexagonRowColumn665.product1_eq,
    HexagonRowColumn665.product2_eq,
    HexagonRowColumn665.product3_eq,
    HexagonRowColumn665.product4_eq,
    HexagonRowColumn665.product5_eq,
    HexagonRowColumn665.product6_eq,
    HexagonRowColumn665.product7_eq] using right0Middle6_eq_case_6_5_checked

private theorem right1Middle6_eq_case_6_5_row_0_0_0 : (right1Middle6 6 5) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn665.rows_inverseACB HexagonRowColumn665.cols_right0) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle6_eq_case_6_5_row_0_0_1 : (right1Middle6 6 5) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn665.rows_inverseACB HexagonRowColumn665.cols_right0) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle6_eq_case_6_5_row_0_1_0 : (right1Middle6 6 5) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn665.rows_inverseACB HexagonRowColumn665.cols_right0) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle6_eq_case_6_5_row_0_1_1 : (right1Middle6 6 5) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn665.rows_inverseACB HexagonRowColumn665.cols_right0) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle6_eq_case_6_5_row_0_2_0 : (right1Middle6 6 5) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn665.rows_inverseACB HexagonRowColumn665.cols_right0) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle6_eq_case_6_5_row_0_2_1 : (right1Middle6 6 5) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn665.rows_inverseACB HexagonRowColumn665.cols_right0) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle6_eq_case_6_5_row_0_3_0 : (right1Middle6 6 5) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn665.rows_inverseACB HexagonRowColumn665.cols_right0) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle6_eq_case_6_5_row_0_3_1 : (right1Middle6 6 5) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn665.rows_inverseACB HexagonRowColumn665.cols_right0) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle6_eq_case_6_5_row_1_0_0 : (right1Middle6 6 5) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn665.rows_inverseACB HexagonRowColumn665.cols_right0) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle6_eq_case_6_5_row_1_0_1 : (right1Middle6 6 5) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn665.rows_inverseACB HexagonRowColumn665.cols_right0) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle6_eq_case_6_5_row_1_1_0 : (right1Middle6 6 5) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn665.rows_inverseACB HexagonRowColumn665.cols_right0) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle6_eq_case_6_5_row_1_1_1 : (right1Middle6 6 5) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn665.rows_inverseACB HexagonRowColumn665.cols_right0) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle6_eq_case_6_5_row_1_2_0 : (right1Middle6 6 5) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn665.rows_inverseACB HexagonRowColumn665.cols_right0) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle6_eq_case_6_5_row_1_2_1 : (right1Middle6 6 5) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn665.rows_inverseACB HexagonRowColumn665.cols_right0) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle6_eq_case_6_5_row_1_3_0 : (right1Middle6 6 5) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn665.rows_inverseACB HexagonRowColumn665.cols_right0) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle6_eq_case_6_5_row_1_3_1 : (right1Middle6 6 5) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn665.rows_inverseACB HexagonRowColumn665.cols_right0) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle6_eq_case_6_5_checked : right1Middle6 6 5 = rowColumnMul HexagonRowColumn665.rows_inverseACB HexagonRowColumn665.cols_right0 := by
  funext r
  fin_cases r
  · exact right1Middle6_eq_case_6_5_row_0_0_0
  · exact right1Middle6_eq_case_6_5_row_0_0_1
  · exact right1Middle6_eq_case_6_5_row_0_1_0
  · exact right1Middle6_eq_case_6_5_row_0_1_1
  · exact right1Middle6_eq_case_6_5_row_0_2_0
  · exact right1Middle6_eq_case_6_5_row_0_2_1
  · exact right1Middle6_eq_case_6_5_row_0_3_0
  · exact right1Middle6_eq_case_6_5_row_0_3_1
  · exact right1Middle6_eq_case_6_5_row_1_0_0
  · exact right1Middle6_eq_case_6_5_row_1_0_1
  · exact right1Middle6_eq_case_6_5_row_1_1_0
  · exact right1Middle6_eq_case_6_5_row_1_1_1
  · exact right1Middle6_eq_case_6_5_row_1_2_0
  · exact right1Middle6_eq_case_6_5_row_1_2_1
  · exact right1Middle6_eq_case_6_5_row_1_3_0
  · exact right1Middle6_eq_case_6_5_row_1_3_1

set_option backward.isDefEq.respectTransparency false in
theorem right1Middle6_eq_case_6_5 : right1Middle6 6 5 = associatorInverseZ 6 5 6 * right0Middle6 6 5 := by
  simpa only [HexagonAtoms665.assocABC_eq,
    HexagonAtoms665.outerABC_eq,
    HexagonAtoms665.assocBAC_eq,
    HexagonAtoms665.innerABC_eq,
    HexagonAtoms665.innerRightABC_eq,
    HexagonAtoms665.inverseACB_eq,
    HexagonAtoms665.innerACB_eq,
    HexagonAtoms665.assocBCA_eq,
    HexagonAtoms665.innerRightBAC_eq,
    HexagonAtoms665.assocCAB_eq,
    HexagonAtoms665.outerLeftABC_eq,
    HexagonRowColumn665.assocBAC_alias,
    HexagonRowColumn665.innerRightBAC_alias,
    HexagonRowColumn665.product0_eq,
    HexagonRowColumn665.product1_eq,
    HexagonRowColumn665.product2_eq,
    HexagonRowColumn665.product3_eq,
    HexagonRowColumn665.product4_eq,
    HexagonRowColumn665.product5_eq,
    HexagonRowColumn665.product6_eq,
    HexagonRowColumn665.product7_eq] using right1Middle6_eq_case_6_5_checked

private theorem right2Middle6_eq_case_6_5_row_0_0_0 : (right2Middle6 6 5) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (right1Middle6 6 5) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle6_eq_case_6_5_row_0_0_1 : (right2Middle6 6 5) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (right1Middle6 6 5) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle6_eq_case_6_5_row_0_1_0 : (right2Middle6 6 5) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (right1Middle6 6 5) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle6_eq_case_6_5_row_0_1_1 : (right2Middle6 6 5) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (right1Middle6 6 5) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle6_eq_case_6_5_row_0_2_0 : (right2Middle6 6 5) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (right1Middle6 6 5) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle6_eq_case_6_5_row_0_2_1 : (right2Middle6 6 5) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (right1Middle6 6 5) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle6_eq_case_6_5_row_0_3_0 : (right2Middle6 6 5) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (right1Middle6 6 5) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle6_eq_case_6_5_row_0_3_1 : (right2Middle6 6 5) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (right1Middle6 6 5) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle6_eq_case_6_5_row_1_0_0 : (right2Middle6 6 5) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (right1Middle6 6 5) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle6_eq_case_6_5_row_1_0_1 : (right2Middle6 6 5) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (right1Middle6 6 5) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle6_eq_case_6_5_row_1_1_0 : (right2Middle6 6 5) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (right1Middle6 6 5) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle6_eq_case_6_5_row_1_1_1 : (right2Middle6 6 5) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (right1Middle6 6 5) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle6_eq_case_6_5_row_1_2_0 : (right2Middle6 6 5) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (right1Middle6 6 5) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle6_eq_case_6_5_row_1_2_1 : (right2Middle6 6 5) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (right1Middle6 6 5) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle6_eq_case_6_5_row_1_3_0 : (right2Middle6 6 5) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (right1Middle6 6 5) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle6_eq_case_6_5_row_1_3_1 : (right2Middle6 6 5) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (right1Middle6 6 5) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle6_eq_case_6_5_checked : right2Middle6 6 5 = right1Middle6 6 5 := by
  funext r
  fin_cases r
  · exact right2Middle6_eq_case_6_5_row_0_0_0
  · exact right2Middle6_eq_case_6_5_row_0_0_1
  · exact right2Middle6_eq_case_6_5_row_0_1_0
  · exact right2Middle6_eq_case_6_5_row_0_1_1
  · exact right2Middle6_eq_case_6_5_row_0_2_0
  · exact right2Middle6_eq_case_6_5_row_0_2_1
  · exact right2Middle6_eq_case_6_5_row_0_3_0
  · exact right2Middle6_eq_case_6_5_row_0_3_1
  · exact right2Middle6_eq_case_6_5_row_1_0_0
  · exact right2Middle6_eq_case_6_5_row_1_0_1
  · exact right2Middle6_eq_case_6_5_row_1_1_0
  · exact right2Middle6_eq_case_6_5_row_1_1_1
  · exact right2Middle6_eq_case_6_5_row_1_2_0
  · exact right2Middle6_eq_case_6_5_row_1_2_1
  · exact right2Middle6_eq_case_6_5_row_1_3_0
  · exact right2Middle6_eq_case_6_5_row_1_3_1

set_option backward.isDefEq.respectTransparency false in
theorem right2Middle6_eq_case_6_5 : right2Middle6 6 5 = innerLeftZ 6 5 6 * right1Middle6 6 5 := by
  simpa only [HexagonAtoms665.assocABC_eq,
    HexagonAtoms665.outerABC_eq,
    HexagonAtoms665.assocBAC_eq,
    HexagonAtoms665.innerABC_eq,
    HexagonAtoms665.innerRightABC_eq,
    HexagonAtoms665.inverseACB_eq,
    HexagonAtoms665.innerACB_eq,
    HexagonAtoms665.assocBCA_eq,
    HexagonAtoms665.innerRightBAC_eq,
    HexagonAtoms665.assocCAB_eq,
    HexagonAtoms665.outerLeftABC_eq,
    HexagonRowColumn665.assocBAC_alias,
    HexagonRowColumn665.innerRightBAC_alias,
    HexagonRowColumn665.product0_eq,
    HexagonRowColumn665.product1_eq,
    HexagonRowColumn665.product2_eq,
    HexagonRowColumn665.product3_eq,
    HexagonRowColumn665.product4_eq,
    HexagonRowColumn665.product5_eq,
    HexagonRowColumn665.product6_eq,
    HexagonRowColumn665.product7_eq] using right2Middle6_eq_case_6_5_checked

private theorem leftFinal6_case_6_5_row_0_0_0 : (((-1 : ℤ) ^ (leftScaleBit 6 6 5).val * positiveScale (leftScaleExponent 6 6 5)) •
      (rowColumnMul HexagonRowColumn665.rows_assocBCA HexagonRowColumn665.cols_left0)) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 6 6 5) • (left1Middle6 6 5)) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal6_case_6_5_row_0_0_1 : (((-1 : ℤ) ^ (leftScaleBit 6 6 5).val * positiveScale (leftScaleExponent 6 6 5)) •
      (rowColumnMul HexagonRowColumn665.rows_assocBCA HexagonRowColumn665.cols_left0)) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 6 6 5) • (left1Middle6 6 5)) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal6_case_6_5_row_0_1_0 : (((-1 : ℤ) ^ (leftScaleBit 6 6 5).val * positiveScale (leftScaleExponent 6 6 5)) •
      (rowColumnMul HexagonRowColumn665.rows_assocBCA HexagonRowColumn665.cols_left0)) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 6 6 5) • (left1Middle6 6 5)) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal6_case_6_5_row_0_1_1 : (((-1 : ℤ) ^ (leftScaleBit 6 6 5).val * positiveScale (leftScaleExponent 6 6 5)) •
      (rowColumnMul HexagonRowColumn665.rows_assocBCA HexagonRowColumn665.cols_left0)) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 6 6 5) • (left1Middle6 6 5)) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal6_case_6_5_row_0_2_0 : (((-1 : ℤ) ^ (leftScaleBit 6 6 5).val * positiveScale (leftScaleExponent 6 6 5)) •
      (rowColumnMul HexagonRowColumn665.rows_assocBCA HexagonRowColumn665.cols_left0)) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 6 6 5) • (left1Middle6 6 5)) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal6_case_6_5_row_0_2_1 : (((-1 : ℤ) ^ (leftScaleBit 6 6 5).val * positiveScale (leftScaleExponent 6 6 5)) •
      (rowColumnMul HexagonRowColumn665.rows_assocBCA HexagonRowColumn665.cols_left0)) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 6 6 5) • (left1Middle6 6 5)) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal6_case_6_5_row_0_3_0 : (((-1 : ℤ) ^ (leftScaleBit 6 6 5).val * positiveScale (leftScaleExponent 6 6 5)) •
      (rowColumnMul HexagonRowColumn665.rows_assocBCA HexagonRowColumn665.cols_left0)) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 6 6 5) • (left1Middle6 6 5)) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal6_case_6_5_row_0_3_1 : (((-1 : ℤ) ^ (leftScaleBit 6 6 5).val * positiveScale (leftScaleExponent 6 6 5)) •
      (rowColumnMul HexagonRowColumn665.rows_assocBCA HexagonRowColumn665.cols_left0)) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 6 6 5) • (left1Middle6 6 5)) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal6_case_6_5_row_1_0_0 : (((-1 : ℤ) ^ (leftScaleBit 6 6 5).val * positiveScale (leftScaleExponent 6 6 5)) •
      (rowColumnMul HexagonRowColumn665.rows_assocBCA HexagonRowColumn665.cols_left0)) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 6 6 5) • (left1Middle6 6 5)) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal6_case_6_5_row_1_0_1 : (((-1 : ℤ) ^ (leftScaleBit 6 6 5).val * positiveScale (leftScaleExponent 6 6 5)) •
      (rowColumnMul HexagonRowColumn665.rows_assocBCA HexagonRowColumn665.cols_left0)) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 6 6 5) • (left1Middle6 6 5)) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal6_case_6_5_row_1_1_0 : (((-1 : ℤ) ^ (leftScaleBit 6 6 5).val * positiveScale (leftScaleExponent 6 6 5)) •
      (rowColumnMul HexagonRowColumn665.rows_assocBCA HexagonRowColumn665.cols_left0)) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 6 6 5) • (left1Middle6 6 5)) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal6_case_6_5_row_1_1_1 : (((-1 : ℤ) ^ (leftScaleBit 6 6 5).val * positiveScale (leftScaleExponent 6 6 5)) •
      (rowColumnMul HexagonRowColumn665.rows_assocBCA HexagonRowColumn665.cols_left0)) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 6 6 5) • (left1Middle6 6 5)) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal6_case_6_5_row_1_2_0 : (((-1 : ℤ) ^ (leftScaleBit 6 6 5).val * positiveScale (leftScaleExponent 6 6 5)) •
      (rowColumnMul HexagonRowColumn665.rows_assocBCA HexagonRowColumn665.cols_left0)) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 6 6 5) • (left1Middle6 6 5)) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal6_case_6_5_row_1_2_1 : (((-1 : ℤ) ^ (leftScaleBit 6 6 5).val * positiveScale (leftScaleExponent 6 6 5)) •
      (rowColumnMul HexagonRowColumn665.rows_assocBCA HexagonRowColumn665.cols_left0)) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 6 6 5) • (left1Middle6 6 5)) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal6_case_6_5_row_1_3_0 : (((-1 : ℤ) ^ (leftScaleBit 6 6 5).val * positiveScale (leftScaleExponent 6 6 5)) •
      (rowColumnMul HexagonRowColumn665.rows_assocBCA HexagonRowColumn665.cols_left0)) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 6 6 5) • (left1Middle6 6 5)) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal6_case_6_5_row_1_3_1 : (((-1 : ℤ) ^ (leftScaleBit 6 6 5).val * positiveScale (leftScaleExponent 6 6 5)) •
      (rowColumnMul HexagonRowColumn665.rows_assocBCA HexagonRowColumn665.cols_left0)) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 6 6 5) • (left1Middle6 6 5)) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal6_case_6_5_checked : ((-1 : ℤ) ^ (leftScaleBit 6 6 5).val * positiveScale (leftScaleExponent 6 6 5)) •
      (rowColumnMul HexagonRowColumn665.rows_assocBCA HexagonRowColumn665.cols_left0) = negativeScale (leftScaleExponent 6 6 5) • (left1Middle6 6 5) := by
  funext r
  fin_cases r
  · exact leftFinal6_case_6_5_row_0_0_0
  · exact leftFinal6_case_6_5_row_0_0_1
  · exact leftFinal6_case_6_5_row_0_1_0
  · exact leftFinal6_case_6_5_row_0_1_1
  · exact leftFinal6_case_6_5_row_0_2_0
  · exact leftFinal6_case_6_5_row_0_2_1
  · exact leftFinal6_case_6_5_row_0_3_0
  · exact leftFinal6_case_6_5_row_0_3_1
  · exact leftFinal6_case_6_5_row_1_0_0
  · exact leftFinal6_case_6_5_row_1_0_1
  · exact leftFinal6_case_6_5_row_1_1_0
  · exact leftFinal6_case_6_5_row_1_1_1
  · exact leftFinal6_case_6_5_row_1_2_0
  · exact leftFinal6_case_6_5_row_1_2_1
  · exact leftFinal6_case_6_5_row_1_3_0
  · exact leftFinal6_case_6_5_row_1_3_1

set_option backward.isDefEq.respectTransparency false in
theorem leftFinal6_case_6_5 : ((-1 : ℤ) ^ (leftScaleBit 6 6 5).val * positiveScale (leftScaleExponent 6 6 5)) •
      (associatorZ 6 5 6 * left0Middle6 6 5) = negativeScale (leftScaleExponent 6 6 5) • (innerRightZ 6 6 5 * left1Middle6 6 5) := by
  simpa only [HexagonAtoms665.assocABC_eq,
    HexagonAtoms665.outerABC_eq,
    HexagonAtoms665.assocBAC_eq,
    HexagonAtoms665.innerABC_eq,
    HexagonAtoms665.innerRightABC_eq,
    HexagonAtoms665.inverseACB_eq,
    HexagonAtoms665.innerACB_eq,
    HexagonAtoms665.assocBCA_eq,
    HexagonAtoms665.innerRightBAC_eq,
    HexagonAtoms665.assocCAB_eq,
    HexagonAtoms665.outerLeftABC_eq,
    HexagonRowColumn665.assocBAC_alias,
    HexagonRowColumn665.innerRightBAC_alias,
    HexagonRowColumn665.product0_eq,
    HexagonRowColumn665.product1_eq,
    HexagonRowColumn665.product2_eq,
    HexagonRowColumn665.product3_eq,
    HexagonRowColumn665.product4_eq,
    HexagonRowColumn665.product5_eq,
    HexagonRowColumn665.product6_eq,
    HexagonRowColumn665.product7_eq] using leftFinal6_case_6_5_checked

private theorem rightFinal6_case_6_5_row_0_0_0 : (((-1 : ℤ) ^ (rightScaleBit 6 6 5).val * positiveScale (rightScaleExponent 6 6 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 6 : ℤ)) • HexagonAtoms665.outerLeftABC) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (negativeScale (rightScaleExponent 6 6 5) • (rowColumnMul HexagonRowColumn665.rows_assocCAB HexagonRowColumn665.cols_right2)) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal6_case_6_5_row_0_0_1 : (((-1 : ℤ) ^ (rightScaleBit 6 6 5).val * positiveScale (rightScaleExponent 6 6 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 6 : ℤ)) • HexagonAtoms665.outerLeftABC) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (negativeScale (rightScaleExponent 6 6 5) • (rowColumnMul HexagonRowColumn665.rows_assocCAB HexagonRowColumn665.cols_right2)) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal6_case_6_5_row_0_1_0 : (((-1 : ℤ) ^ (rightScaleBit 6 6 5).val * positiveScale (rightScaleExponent 6 6 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 6 : ℤ)) • HexagonAtoms665.outerLeftABC) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (negativeScale (rightScaleExponent 6 6 5) • (rowColumnMul HexagonRowColumn665.rows_assocCAB HexagonRowColumn665.cols_right2)) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal6_case_6_5_row_0_1_1 : (((-1 : ℤ) ^ (rightScaleBit 6 6 5).val * positiveScale (rightScaleExponent 6 6 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 6 : ℤ)) • HexagonAtoms665.outerLeftABC) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (negativeScale (rightScaleExponent 6 6 5) • (rowColumnMul HexagonRowColumn665.rows_assocCAB HexagonRowColumn665.cols_right2)) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal6_case_6_5_row_0_2_0 : (((-1 : ℤ) ^ (rightScaleBit 6 6 5).val * positiveScale (rightScaleExponent 6 6 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 6 : ℤ)) • HexagonAtoms665.outerLeftABC) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (negativeScale (rightScaleExponent 6 6 5) • (rowColumnMul HexagonRowColumn665.rows_assocCAB HexagonRowColumn665.cols_right2)) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal6_case_6_5_row_0_2_1 : (((-1 : ℤ) ^ (rightScaleBit 6 6 5).val * positiveScale (rightScaleExponent 6 6 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 6 : ℤ)) • HexagonAtoms665.outerLeftABC) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (negativeScale (rightScaleExponent 6 6 5) • (rowColumnMul HexagonRowColumn665.rows_assocCAB HexagonRowColumn665.cols_right2)) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal6_case_6_5_row_0_3_0 : (((-1 : ℤ) ^ (rightScaleBit 6 6 5).val * positiveScale (rightScaleExponent 6 6 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 6 : ℤ)) • HexagonAtoms665.outerLeftABC) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (negativeScale (rightScaleExponent 6 6 5) • (rowColumnMul HexagonRowColumn665.rows_assocCAB HexagonRowColumn665.cols_right2)) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal6_case_6_5_row_0_3_1 : (((-1 : ℤ) ^ (rightScaleBit 6 6 5).val * positiveScale (rightScaleExponent 6 6 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 6 : ℤ)) • HexagonAtoms665.outerLeftABC) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (negativeScale (rightScaleExponent 6 6 5) • (rowColumnMul HexagonRowColumn665.rows_assocCAB HexagonRowColumn665.cols_right2)) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal6_case_6_5_row_1_0_0 : (((-1 : ℤ) ^ (rightScaleBit 6 6 5).val * positiveScale (rightScaleExponent 6 6 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 6 : ℤ)) • HexagonAtoms665.outerLeftABC) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (negativeScale (rightScaleExponent 6 6 5) • (rowColumnMul HexagonRowColumn665.rows_assocCAB HexagonRowColumn665.cols_right2)) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal6_case_6_5_row_1_0_1 : (((-1 : ℤ) ^ (rightScaleBit 6 6 5).val * positiveScale (rightScaleExponent 6 6 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 6 : ℤ)) • HexagonAtoms665.outerLeftABC) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (negativeScale (rightScaleExponent 6 6 5) • (rowColumnMul HexagonRowColumn665.rows_assocCAB HexagonRowColumn665.cols_right2)) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal6_case_6_5_row_1_1_0 : (((-1 : ℤ) ^ (rightScaleBit 6 6 5).val * positiveScale (rightScaleExponent 6 6 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 6 : ℤ)) • HexagonAtoms665.outerLeftABC) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (negativeScale (rightScaleExponent 6 6 5) • (rowColumnMul HexagonRowColumn665.rows_assocCAB HexagonRowColumn665.cols_right2)) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal6_case_6_5_row_1_1_1 : (((-1 : ℤ) ^ (rightScaleBit 6 6 5).val * positiveScale (rightScaleExponent 6 6 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 6 : ℤ)) • HexagonAtoms665.outerLeftABC) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (negativeScale (rightScaleExponent 6 6 5) • (rowColumnMul HexagonRowColumn665.rows_assocCAB HexagonRowColumn665.cols_right2)) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal6_case_6_5_row_1_2_0 : (((-1 : ℤ) ^ (rightScaleBit 6 6 5).val * positiveScale (rightScaleExponent 6 6 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 6 : ℤ)) • HexagonAtoms665.outerLeftABC) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (negativeScale (rightScaleExponent 6 6 5) • (rowColumnMul HexagonRowColumn665.rows_assocCAB HexagonRowColumn665.cols_right2)) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal6_case_6_5_row_1_2_1 : (((-1 : ℤ) ^ (rightScaleBit 6 6 5).val * positiveScale (rightScaleExponent 6 6 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 6 : ℤ)) • HexagonAtoms665.outerLeftABC) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (negativeScale (rightScaleExponent 6 6 5) • (rowColumnMul HexagonRowColumn665.rows_assocCAB HexagonRowColumn665.cols_right2)) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal6_case_6_5_row_1_3_0 : (((-1 : ℤ) ^ (rightScaleBit 6 6 5).val * positiveScale (rightScaleExponent 6 6 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 6 : ℤ)) • HexagonAtoms665.outerLeftABC) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (negativeScale (rightScaleExponent 6 6 5) • (rowColumnMul HexagonRowColumn665.rows_assocCAB HexagonRowColumn665.cols_right2)) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal6_case_6_5_row_1_3_1 : (((-1 : ℤ) ^ (rightScaleBit 6 6 5).val * positiveScale (rightScaleExponent 6 6 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 6 : ℤ)) • HexagonAtoms665.outerLeftABC) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (negativeScale (rightScaleExponent 6 6 5) • (rowColumnMul HexagonRowColumn665.rows_assocCAB HexagonRowColumn665.cols_right2)) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal6_case_6_5_checked : ((-1 : ℤ) ^ (rightScaleBit 6 6 5).val * positiveScale (rightScaleExponent 6 6 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 6 : ℤ)) • HexagonAtoms665.outerLeftABC = negativeScale (rightScaleExponent 6 6 5) • (rowColumnMul HexagonRowColumn665.rows_assocCAB HexagonRowColumn665.cols_right2) := by
  funext r
  fin_cases r
  · exact rightFinal6_case_6_5_row_0_0_0
  · exact rightFinal6_case_6_5_row_0_0_1
  · exact rightFinal6_case_6_5_row_0_1_0
  · exact rightFinal6_case_6_5_row_0_1_1
  · exact rightFinal6_case_6_5_row_0_2_0
  · exact rightFinal6_case_6_5_row_0_2_1
  · exact rightFinal6_case_6_5_row_0_3_0
  · exact rightFinal6_case_6_5_row_0_3_1
  · exact rightFinal6_case_6_5_row_1_0_0
  · exact rightFinal6_case_6_5_row_1_0_1
  · exact rightFinal6_case_6_5_row_1_1_0
  · exact rightFinal6_case_6_5_row_1_1_1
  · exact rightFinal6_case_6_5_row_1_2_0
  · exact rightFinal6_case_6_5_row_1_2_1
  · exact rightFinal6_case_6_5_row_1_3_0
  · exact rightFinal6_case_6_5_row_1_3_1

set_option backward.isDefEq.respectTransparency false in
theorem rightFinal6_case_6_5 : ((-1 : ℤ) ^ (rightScaleBit 6 6 5).val * positiveScale (rightScaleExponent 6 6 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 6 : ℤ)) • outerLeftZ 6 6 5 = negativeScale (rightScaleExponent 6 6 5) • (associatorZ 5 6 6 * right2Middle6 6 5) := by
  simpa only [HexagonAtoms665.assocABC_eq,
    HexagonAtoms665.outerABC_eq,
    HexagonAtoms665.assocBAC_eq,
    HexagonAtoms665.innerABC_eq,
    HexagonAtoms665.innerRightABC_eq,
    HexagonAtoms665.inverseACB_eq,
    HexagonAtoms665.innerACB_eq,
    HexagonAtoms665.assocBCA_eq,
    HexagonAtoms665.innerRightBAC_eq,
    HexagonAtoms665.assocCAB_eq,
    HexagonAtoms665.outerLeftABC_eq,
    HexagonRowColumn665.assocBAC_alias,
    HexagonRowColumn665.innerRightBAC_alias,
    HexagonRowColumn665.product0_eq,
    HexagonRowColumn665.product1_eq,
    HexagonRowColumn665.product2_eq,
    HexagonRowColumn665.product3_eq,
    HexagonRowColumn665.product4_eq,
    HexagonRowColumn665.product5_eq,
    HexagonRowColumn665.product6_eq,
    HexagonRowColumn665.product7_eq] using rightFinal6_case_6_5_checked

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonCases6
