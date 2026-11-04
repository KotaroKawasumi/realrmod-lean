import RMod.BrundanEllis.StackingReferenceHexagonMiddle3
import RMod.BrundanEllis.StackingReferenceSparseMatrixCheck
import RMod.BrundanEllis.StackingReferenceHexagonAtoms331
import RMod.BrundanEllis.StackingReferenceHexagonRowColumn331

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

private theorem left0Middle3_eq_case_3_1_row_0_0_0 : (left0Middle3 3 1) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (HexagonAtoms331.assocABC) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left0Middle3_eq_case_3_1_row_0_0_1 : (left0Middle3 3 1) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (HexagonAtoms331.assocABC) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left0Middle3_eq_case_3_1_row_0_1_0 : (left0Middle3 3 1) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (HexagonAtoms331.assocABC) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left0Middle3_eq_case_3_1_row_0_1_1 : (left0Middle3 3 1) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (HexagonAtoms331.assocABC) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left0Middle3_eq_case_3_1_row_0_2_0 : (left0Middle3 3 1) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (HexagonAtoms331.assocABC) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left0Middle3_eq_case_3_1_row_0_2_1 : (left0Middle3 3 1) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (HexagonAtoms331.assocABC) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left0Middle3_eq_case_3_1_row_0_3_0 : (left0Middle3 3 1) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (HexagonAtoms331.assocABC) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left0Middle3_eq_case_3_1_row_0_3_1 : (left0Middle3 3 1) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (HexagonAtoms331.assocABC) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left0Middle3_eq_case_3_1_row_1_0_0 : (left0Middle3 3 1) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (HexagonAtoms331.assocABC) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left0Middle3_eq_case_3_1_row_1_0_1 : (left0Middle3 3 1) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (HexagonAtoms331.assocABC) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left0Middle3_eq_case_3_1_row_1_1_0 : (left0Middle3 3 1) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (HexagonAtoms331.assocABC) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left0Middle3_eq_case_3_1_row_1_1_1 : (left0Middle3 3 1) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (HexagonAtoms331.assocABC) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left0Middle3_eq_case_3_1_row_1_2_0 : (left0Middle3 3 1) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (HexagonAtoms331.assocABC) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left0Middle3_eq_case_3_1_row_1_2_1 : (left0Middle3 3 1) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (HexagonAtoms331.assocABC) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left0Middle3_eq_case_3_1_row_1_3_0 : (left0Middle3 3 1) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (HexagonAtoms331.assocABC) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left0Middle3_eq_case_3_1_row_1_3_1 : (left0Middle3 3 1) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (HexagonAtoms331.assocABC) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left0Middle3_eq_case_3_1_checked : left0Middle3 3 1 = HexagonAtoms331.assocABC := by
  funext r
  fin_cases r
  · exact left0Middle3_eq_case_3_1_row_0_0_0
  · exact left0Middle3_eq_case_3_1_row_0_0_1
  · exact left0Middle3_eq_case_3_1_row_0_1_0
  · exact left0Middle3_eq_case_3_1_row_0_1_1
  · exact left0Middle3_eq_case_3_1_row_0_2_0
  · exact left0Middle3_eq_case_3_1_row_0_2_1
  · exact left0Middle3_eq_case_3_1_row_0_3_0
  · exact left0Middle3_eq_case_3_1_row_0_3_1
  · exact left0Middle3_eq_case_3_1_row_1_0_0
  · exact left0Middle3_eq_case_3_1_row_1_0_1
  · exact left0Middle3_eq_case_3_1_row_1_1_0
  · exact left0Middle3_eq_case_3_1_row_1_1_1
  · exact left0Middle3_eq_case_3_1_row_1_2_0
  · exact left0Middle3_eq_case_3_1_row_1_2_1
  · exact left0Middle3_eq_case_3_1_row_1_3_0
  · exact left0Middle3_eq_case_3_1_row_1_3_1

set_option backward.isDefEq.respectTransparency false in
theorem left0Middle3_eq_case_3_1 : left0Middle3 3 1 = outerRightZ 3 3 1 * associatorZ 3 3 1 := by
  simpa only [HexagonAtoms331.assocABC_eq,
    HexagonAtoms331.outerABC_eq,
    HexagonAtoms331.assocBAC_eq,
    HexagonAtoms331.innerABC_eq,
    HexagonAtoms331.innerRightABC_eq,
    HexagonAtoms331.inverseACB_eq,
    HexagonAtoms331.innerACB_eq,
    HexagonAtoms331.assocBCA_eq,
    HexagonAtoms331.innerRightBAC_eq,
    HexagonAtoms331.assocCAB_eq,
    HexagonAtoms331.outerLeftABC_eq,
    HexagonRowColumn331.assocBAC_alias,
    HexagonRowColumn331.innerRightBAC_alias,
    HexagonRowColumn331.product0_eq,
    HexagonRowColumn331.product1_eq,
    HexagonRowColumn331.product2_eq,
    HexagonRowColumn331.product3_eq,
    HexagonRowColumn331.product4_eq,
    HexagonRowColumn331.product5_eq,
    HexagonRowColumn331.product6_eq,
    HexagonRowColumn331.product7_eq] using left0Middle3_eq_case_3_1_checked

private theorem left1Middle3_eq_case_3_1_row_0_0_0 : (left1Middle3 3 1) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn331.rows_assocABC HexagonRowColumn331.cols_innerABC) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left1Middle3_eq_case_3_1_row_0_0_1 : (left1Middle3 3 1) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn331.rows_assocABC HexagonRowColumn331.cols_innerABC) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left1Middle3_eq_case_3_1_row_0_1_0 : (left1Middle3 3 1) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn331.rows_assocABC HexagonRowColumn331.cols_innerABC) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left1Middle3_eq_case_3_1_row_0_1_1 : (left1Middle3 3 1) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn331.rows_assocABC HexagonRowColumn331.cols_innerABC) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left1Middle3_eq_case_3_1_row_0_2_0 : (left1Middle3 3 1) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn331.rows_assocABC HexagonRowColumn331.cols_innerABC) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left1Middle3_eq_case_3_1_row_0_2_1 : (left1Middle3 3 1) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn331.rows_assocABC HexagonRowColumn331.cols_innerABC) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left1Middle3_eq_case_3_1_row_0_3_0 : (left1Middle3 3 1) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn331.rows_assocABC HexagonRowColumn331.cols_innerABC) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left1Middle3_eq_case_3_1_row_0_3_1 : (left1Middle3 3 1) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn331.rows_assocABC HexagonRowColumn331.cols_innerABC) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left1Middle3_eq_case_3_1_row_1_0_0 : (left1Middle3 3 1) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn331.rows_assocABC HexagonRowColumn331.cols_innerABC) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left1Middle3_eq_case_3_1_row_1_0_1 : (left1Middle3 3 1) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn331.rows_assocABC HexagonRowColumn331.cols_innerABC) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left1Middle3_eq_case_3_1_row_1_1_0 : (left1Middle3 3 1) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn331.rows_assocABC HexagonRowColumn331.cols_innerABC) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left1Middle3_eq_case_3_1_row_1_1_1 : (left1Middle3 3 1) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn331.rows_assocABC HexagonRowColumn331.cols_innerABC) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left1Middle3_eq_case_3_1_row_1_2_0 : (left1Middle3 3 1) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn331.rows_assocABC HexagonRowColumn331.cols_innerABC) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left1Middle3_eq_case_3_1_row_1_2_1 : (left1Middle3 3 1) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn331.rows_assocABC HexagonRowColumn331.cols_innerABC) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left1Middle3_eq_case_3_1_row_1_3_0 : (left1Middle3 3 1) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn331.rows_assocABC HexagonRowColumn331.cols_innerABC) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left1Middle3_eq_case_3_1_row_1_3_1 : (left1Middle3 3 1) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn331.rows_assocABC HexagonRowColumn331.cols_innerABC) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left1Middle3_eq_case_3_1_checked : left1Middle3 3 1 = rowColumnMul HexagonRowColumn331.rows_assocABC HexagonRowColumn331.cols_innerABC := by
  funext r
  fin_cases r
  · exact left1Middle3_eq_case_3_1_row_0_0_0
  · exact left1Middle3_eq_case_3_1_row_0_0_1
  · exact left1Middle3_eq_case_3_1_row_0_1_0
  · exact left1Middle3_eq_case_3_1_row_0_1_1
  · exact left1Middle3_eq_case_3_1_row_0_2_0
  · exact left1Middle3_eq_case_3_1_row_0_2_1
  · exact left1Middle3_eq_case_3_1_row_0_3_0
  · exact left1Middle3_eq_case_3_1_row_0_3_1
  · exact left1Middle3_eq_case_3_1_row_1_0_0
  · exact left1Middle3_eq_case_3_1_row_1_0_1
  · exact left1Middle3_eq_case_3_1_row_1_1_0
  · exact left1Middle3_eq_case_3_1_row_1_1_1
  · exact left1Middle3_eq_case_3_1_row_1_2_0
  · exact left1Middle3_eq_case_3_1_row_1_2_1
  · exact left1Middle3_eq_case_3_1_row_1_3_0
  · exact left1Middle3_eq_case_3_1_row_1_3_1

set_option backward.isDefEq.respectTransparency false in
theorem left1Middle3_eq_case_3_1 : left1Middle3 3 1 = associatorZ 3 3 1 * innerLeftZ 3 3 1 := by
  simpa only [HexagonAtoms331.assocABC_eq,
    HexagonAtoms331.outerABC_eq,
    HexagonAtoms331.assocBAC_eq,
    HexagonAtoms331.innerABC_eq,
    HexagonAtoms331.innerRightABC_eq,
    HexagonAtoms331.inverseACB_eq,
    HexagonAtoms331.innerACB_eq,
    HexagonAtoms331.assocBCA_eq,
    HexagonAtoms331.innerRightBAC_eq,
    HexagonAtoms331.assocCAB_eq,
    HexagonAtoms331.outerLeftABC_eq,
    HexagonRowColumn331.assocBAC_alias,
    HexagonRowColumn331.innerRightBAC_alias,
    HexagonRowColumn331.product0_eq,
    HexagonRowColumn331.product1_eq,
    HexagonRowColumn331.product2_eq,
    HexagonRowColumn331.product3_eq,
    HexagonRowColumn331.product4_eq,
    HexagonRowColumn331.product5_eq,
    HexagonRowColumn331.product6_eq,
    HexagonRowColumn331.product7_eq] using left1Middle3_eq_case_3_1_checked

private theorem right0Middle3_eq_case_3_1_row_0_0_0 : (right0Middle3 3 1) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (HexagonAtoms331.assocABC) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right0Middle3_eq_case_3_1_row_0_0_1 : (right0Middle3 3 1) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (HexagonAtoms331.assocABC) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right0Middle3_eq_case_3_1_row_0_1_0 : (right0Middle3 3 1) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (HexagonAtoms331.assocABC) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right0Middle3_eq_case_3_1_row_0_1_1 : (right0Middle3 3 1) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (HexagonAtoms331.assocABC) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right0Middle3_eq_case_3_1_row_0_2_0 : (right0Middle3 3 1) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (HexagonAtoms331.assocABC) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right0Middle3_eq_case_3_1_row_0_2_1 : (right0Middle3 3 1) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (HexagonAtoms331.assocABC) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right0Middle3_eq_case_3_1_row_0_3_0 : (right0Middle3 3 1) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (HexagonAtoms331.assocABC) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right0Middle3_eq_case_3_1_row_0_3_1 : (right0Middle3 3 1) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (HexagonAtoms331.assocABC) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right0Middle3_eq_case_3_1_row_1_0_0 : (right0Middle3 3 1) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (HexagonAtoms331.assocABC) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right0Middle3_eq_case_3_1_row_1_0_1 : (right0Middle3 3 1) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (HexagonAtoms331.assocABC) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right0Middle3_eq_case_3_1_row_1_1_0 : (right0Middle3 3 1) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (HexagonAtoms331.assocABC) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right0Middle3_eq_case_3_1_row_1_1_1 : (right0Middle3 3 1) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (HexagonAtoms331.assocABC) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right0Middle3_eq_case_3_1_row_1_2_0 : (right0Middle3 3 1) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (HexagonAtoms331.assocABC) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right0Middle3_eq_case_3_1_row_1_2_1 : (right0Middle3 3 1) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (HexagonAtoms331.assocABC) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right0Middle3_eq_case_3_1_row_1_3_0 : (right0Middle3 3 1) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (HexagonAtoms331.assocABC) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right0Middle3_eq_case_3_1_row_1_3_1 : (right0Middle3 3 1) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (HexagonAtoms331.assocABC) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right0Middle3_eq_case_3_1_checked : right0Middle3 3 1 = HexagonAtoms331.assocABC := by
  funext r
  fin_cases r
  · exact right0Middle3_eq_case_3_1_row_0_0_0
  · exact right0Middle3_eq_case_3_1_row_0_0_1
  · exact right0Middle3_eq_case_3_1_row_0_1_0
  · exact right0Middle3_eq_case_3_1_row_0_1_1
  · exact right0Middle3_eq_case_3_1_row_0_2_0
  · exact right0Middle3_eq_case_3_1_row_0_2_1
  · exact right0Middle3_eq_case_3_1_row_0_3_0
  · exact right0Middle3_eq_case_3_1_row_0_3_1
  · exact right0Middle3_eq_case_3_1_row_1_0_0
  · exact right0Middle3_eq_case_3_1_row_1_0_1
  · exact right0Middle3_eq_case_3_1_row_1_1_0
  · exact right0Middle3_eq_case_3_1_row_1_1_1
  · exact right0Middle3_eq_case_3_1_row_1_2_0
  · exact right0Middle3_eq_case_3_1_row_1_2_1
  · exact right0Middle3_eq_case_3_1_row_1_3_0
  · exact right0Middle3_eq_case_3_1_row_1_3_1

set_option backward.isDefEq.respectTransparency false in
theorem right0Middle3_eq_case_3_1 : right0Middle3 3 1 = innerRightZ 3 3 1 * associatorZ 3 3 1 := by
  simpa only [HexagonAtoms331.assocABC_eq,
    HexagonAtoms331.outerABC_eq,
    HexagonAtoms331.assocBAC_eq,
    HexagonAtoms331.innerABC_eq,
    HexagonAtoms331.innerRightABC_eq,
    HexagonAtoms331.inverseACB_eq,
    HexagonAtoms331.innerACB_eq,
    HexagonAtoms331.assocBCA_eq,
    HexagonAtoms331.innerRightBAC_eq,
    HexagonAtoms331.assocCAB_eq,
    HexagonAtoms331.outerLeftABC_eq,
    HexagonRowColumn331.assocBAC_alias,
    HexagonRowColumn331.innerRightBAC_alias,
    HexagonRowColumn331.product0_eq,
    HexagonRowColumn331.product1_eq,
    HexagonRowColumn331.product2_eq,
    HexagonRowColumn331.product3_eq,
    HexagonRowColumn331.product4_eq,
    HexagonRowColumn331.product5_eq,
    HexagonRowColumn331.product6_eq,
    HexagonRowColumn331.product7_eq] using right0Middle3_eq_case_3_1_checked

private theorem right1Middle3_eq_case_3_1_row_0_0_0 : (right1Middle3 3 1) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn331.rows_inverseACB HexagonRowColumn331.cols_right0) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right1Middle3_eq_case_3_1_row_0_0_1 : (right1Middle3 3 1) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn331.rows_inverseACB HexagonRowColumn331.cols_right0) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right1Middle3_eq_case_3_1_row_0_1_0 : (right1Middle3 3 1) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn331.rows_inverseACB HexagonRowColumn331.cols_right0) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right1Middle3_eq_case_3_1_row_0_1_1 : (right1Middle3 3 1) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn331.rows_inverseACB HexagonRowColumn331.cols_right0) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right1Middle3_eq_case_3_1_row_0_2_0 : (right1Middle3 3 1) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn331.rows_inverseACB HexagonRowColumn331.cols_right0) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right1Middle3_eq_case_3_1_row_0_2_1 : (right1Middle3 3 1) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn331.rows_inverseACB HexagonRowColumn331.cols_right0) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right1Middle3_eq_case_3_1_row_0_3_0 : (right1Middle3 3 1) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn331.rows_inverseACB HexagonRowColumn331.cols_right0) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right1Middle3_eq_case_3_1_row_0_3_1 : (right1Middle3 3 1) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn331.rows_inverseACB HexagonRowColumn331.cols_right0) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right1Middle3_eq_case_3_1_row_1_0_0 : (right1Middle3 3 1) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn331.rows_inverseACB HexagonRowColumn331.cols_right0) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right1Middle3_eq_case_3_1_row_1_0_1 : (right1Middle3 3 1) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn331.rows_inverseACB HexagonRowColumn331.cols_right0) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right1Middle3_eq_case_3_1_row_1_1_0 : (right1Middle3 3 1) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn331.rows_inverseACB HexagonRowColumn331.cols_right0) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right1Middle3_eq_case_3_1_row_1_1_1 : (right1Middle3 3 1) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn331.rows_inverseACB HexagonRowColumn331.cols_right0) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right1Middle3_eq_case_3_1_row_1_2_0 : (right1Middle3 3 1) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn331.rows_inverseACB HexagonRowColumn331.cols_right0) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right1Middle3_eq_case_3_1_row_1_2_1 : (right1Middle3 3 1) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn331.rows_inverseACB HexagonRowColumn331.cols_right0) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right1Middle3_eq_case_3_1_row_1_3_0 : (right1Middle3 3 1) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn331.rows_inverseACB HexagonRowColumn331.cols_right0) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right1Middle3_eq_case_3_1_row_1_3_1 : (right1Middle3 3 1) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn331.rows_inverseACB HexagonRowColumn331.cols_right0) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right1Middle3_eq_case_3_1_checked : right1Middle3 3 1 = rowColumnMul HexagonRowColumn331.rows_inverseACB HexagonRowColumn331.cols_right0 := by
  funext r
  fin_cases r
  · exact right1Middle3_eq_case_3_1_row_0_0_0
  · exact right1Middle3_eq_case_3_1_row_0_0_1
  · exact right1Middle3_eq_case_3_1_row_0_1_0
  · exact right1Middle3_eq_case_3_1_row_0_1_1
  · exact right1Middle3_eq_case_3_1_row_0_2_0
  · exact right1Middle3_eq_case_3_1_row_0_2_1
  · exact right1Middle3_eq_case_3_1_row_0_3_0
  · exact right1Middle3_eq_case_3_1_row_0_3_1
  · exact right1Middle3_eq_case_3_1_row_1_0_0
  · exact right1Middle3_eq_case_3_1_row_1_0_1
  · exact right1Middle3_eq_case_3_1_row_1_1_0
  · exact right1Middle3_eq_case_3_1_row_1_1_1
  · exact right1Middle3_eq_case_3_1_row_1_2_0
  · exact right1Middle3_eq_case_3_1_row_1_2_1
  · exact right1Middle3_eq_case_3_1_row_1_3_0
  · exact right1Middle3_eq_case_3_1_row_1_3_1

set_option backward.isDefEq.respectTransparency false in
theorem right1Middle3_eq_case_3_1 : right1Middle3 3 1 = associatorInverseZ 3 1 3 * right0Middle3 3 1 := by
  simpa only [HexagonAtoms331.assocABC_eq,
    HexagonAtoms331.outerABC_eq,
    HexagonAtoms331.assocBAC_eq,
    HexagonAtoms331.innerABC_eq,
    HexagonAtoms331.innerRightABC_eq,
    HexagonAtoms331.inverseACB_eq,
    HexagonAtoms331.innerACB_eq,
    HexagonAtoms331.assocBCA_eq,
    HexagonAtoms331.innerRightBAC_eq,
    HexagonAtoms331.assocCAB_eq,
    HexagonAtoms331.outerLeftABC_eq,
    HexagonRowColumn331.assocBAC_alias,
    HexagonRowColumn331.innerRightBAC_alias,
    HexagonRowColumn331.product0_eq,
    HexagonRowColumn331.product1_eq,
    HexagonRowColumn331.product2_eq,
    HexagonRowColumn331.product3_eq,
    HexagonRowColumn331.product4_eq,
    HexagonRowColumn331.product5_eq,
    HexagonRowColumn331.product6_eq,
    HexagonRowColumn331.product7_eq] using right1Middle3_eq_case_3_1_checked

private theorem right2Middle3_eq_case_3_1_row_0_0_0 : (right2Middle3 3 1) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (right1Middle3 3 1) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right2Middle3_eq_case_3_1_row_0_0_1 : (right2Middle3 3 1) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (right1Middle3 3 1) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right2Middle3_eq_case_3_1_row_0_1_0 : (right2Middle3 3 1) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (right1Middle3 3 1) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right2Middle3_eq_case_3_1_row_0_1_1 : (right2Middle3 3 1) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (right1Middle3 3 1) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right2Middle3_eq_case_3_1_row_0_2_0 : (right2Middle3 3 1) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (right1Middle3 3 1) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right2Middle3_eq_case_3_1_row_0_2_1 : (right2Middle3 3 1) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (right1Middle3 3 1) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right2Middle3_eq_case_3_1_row_0_3_0 : (right2Middle3 3 1) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (right1Middle3 3 1) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right2Middle3_eq_case_3_1_row_0_3_1 : (right2Middle3 3 1) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (right1Middle3 3 1) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right2Middle3_eq_case_3_1_row_1_0_0 : (right2Middle3 3 1) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (right1Middle3 3 1) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right2Middle3_eq_case_3_1_row_1_0_1 : (right2Middle3 3 1) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (right1Middle3 3 1) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right2Middle3_eq_case_3_1_row_1_1_0 : (right2Middle3 3 1) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (right1Middle3 3 1) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right2Middle3_eq_case_3_1_row_1_1_1 : (right2Middle3 3 1) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (right1Middle3 3 1) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right2Middle3_eq_case_3_1_row_1_2_0 : (right2Middle3 3 1) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (right1Middle3 3 1) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right2Middle3_eq_case_3_1_row_1_2_1 : (right2Middle3 3 1) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (right1Middle3 3 1) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right2Middle3_eq_case_3_1_row_1_3_0 : (right2Middle3 3 1) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (right1Middle3 3 1) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right2Middle3_eq_case_3_1_row_1_3_1 : (right2Middle3 3 1) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (right1Middle3 3 1) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right2Middle3_eq_case_3_1_checked : right2Middle3 3 1 = right1Middle3 3 1 := by
  funext r
  fin_cases r
  · exact right2Middle3_eq_case_3_1_row_0_0_0
  · exact right2Middle3_eq_case_3_1_row_0_0_1
  · exact right2Middle3_eq_case_3_1_row_0_1_0
  · exact right2Middle3_eq_case_3_1_row_0_1_1
  · exact right2Middle3_eq_case_3_1_row_0_2_0
  · exact right2Middle3_eq_case_3_1_row_0_2_1
  · exact right2Middle3_eq_case_3_1_row_0_3_0
  · exact right2Middle3_eq_case_3_1_row_0_3_1
  · exact right2Middle3_eq_case_3_1_row_1_0_0
  · exact right2Middle3_eq_case_3_1_row_1_0_1
  · exact right2Middle3_eq_case_3_1_row_1_1_0
  · exact right2Middle3_eq_case_3_1_row_1_1_1
  · exact right2Middle3_eq_case_3_1_row_1_2_0
  · exact right2Middle3_eq_case_3_1_row_1_2_1
  · exact right2Middle3_eq_case_3_1_row_1_3_0
  · exact right2Middle3_eq_case_3_1_row_1_3_1

set_option backward.isDefEq.respectTransparency false in
theorem right2Middle3_eq_case_3_1 : right2Middle3 3 1 = innerLeftZ 3 1 3 * right1Middle3 3 1 := by
  simpa only [HexagonAtoms331.assocABC_eq,
    HexagonAtoms331.outerABC_eq,
    HexagonAtoms331.assocBAC_eq,
    HexagonAtoms331.innerABC_eq,
    HexagonAtoms331.innerRightABC_eq,
    HexagonAtoms331.inverseACB_eq,
    HexagonAtoms331.innerACB_eq,
    HexagonAtoms331.assocBCA_eq,
    HexagonAtoms331.innerRightBAC_eq,
    HexagonAtoms331.assocCAB_eq,
    HexagonAtoms331.outerLeftABC_eq,
    HexagonRowColumn331.assocBAC_alias,
    HexagonRowColumn331.innerRightBAC_alias,
    HexagonRowColumn331.product0_eq,
    HexagonRowColumn331.product1_eq,
    HexagonRowColumn331.product2_eq,
    HexagonRowColumn331.product3_eq,
    HexagonRowColumn331.product4_eq,
    HexagonRowColumn331.product5_eq,
    HexagonRowColumn331.product6_eq,
    HexagonRowColumn331.product7_eq] using right2Middle3_eq_case_3_1_checked

private theorem leftFinal3_case_3_1_row_0_0_0 : (((-1 : ℤ) ^ (leftScaleBit 3 3 1).val * positiveScale (leftScaleExponent 3 3 1)) •
      (rowColumnMul HexagonRowColumn331.rows_assocBCA HexagonRowColumn331.cols_left0)) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 3 3 1) • (left1Middle3 3 1)) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem leftFinal3_case_3_1_row_0_0_1 : (((-1 : ℤ) ^ (leftScaleBit 3 3 1).val * positiveScale (leftScaleExponent 3 3 1)) •
      (rowColumnMul HexagonRowColumn331.rows_assocBCA HexagonRowColumn331.cols_left0)) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 3 3 1) • (left1Middle3 3 1)) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem leftFinal3_case_3_1_row_0_1_0 : (((-1 : ℤ) ^ (leftScaleBit 3 3 1).val * positiveScale (leftScaleExponent 3 3 1)) •
      (rowColumnMul HexagonRowColumn331.rows_assocBCA HexagonRowColumn331.cols_left0)) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 3 3 1) • (left1Middle3 3 1)) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem leftFinal3_case_3_1_row_0_1_1 : (((-1 : ℤ) ^ (leftScaleBit 3 3 1).val * positiveScale (leftScaleExponent 3 3 1)) •
      (rowColumnMul HexagonRowColumn331.rows_assocBCA HexagonRowColumn331.cols_left0)) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 3 3 1) • (left1Middle3 3 1)) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem leftFinal3_case_3_1_row_0_2_0 : (((-1 : ℤ) ^ (leftScaleBit 3 3 1).val * positiveScale (leftScaleExponent 3 3 1)) •
      (rowColumnMul HexagonRowColumn331.rows_assocBCA HexagonRowColumn331.cols_left0)) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 3 3 1) • (left1Middle3 3 1)) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem leftFinal3_case_3_1_row_0_2_1 : (((-1 : ℤ) ^ (leftScaleBit 3 3 1).val * positiveScale (leftScaleExponent 3 3 1)) •
      (rowColumnMul HexagonRowColumn331.rows_assocBCA HexagonRowColumn331.cols_left0)) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 3 3 1) • (left1Middle3 3 1)) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem leftFinal3_case_3_1_row_0_3_0 : (((-1 : ℤ) ^ (leftScaleBit 3 3 1).val * positiveScale (leftScaleExponent 3 3 1)) •
      (rowColumnMul HexagonRowColumn331.rows_assocBCA HexagonRowColumn331.cols_left0)) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 3 3 1) • (left1Middle3 3 1)) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem leftFinal3_case_3_1_row_0_3_1 : (((-1 : ℤ) ^ (leftScaleBit 3 3 1).val * positiveScale (leftScaleExponent 3 3 1)) •
      (rowColumnMul HexagonRowColumn331.rows_assocBCA HexagonRowColumn331.cols_left0)) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 3 3 1) • (left1Middle3 3 1)) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem leftFinal3_case_3_1_row_1_0_0 : (((-1 : ℤ) ^ (leftScaleBit 3 3 1).val * positiveScale (leftScaleExponent 3 3 1)) •
      (rowColumnMul HexagonRowColumn331.rows_assocBCA HexagonRowColumn331.cols_left0)) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 3 3 1) • (left1Middle3 3 1)) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem leftFinal3_case_3_1_row_1_0_1 : (((-1 : ℤ) ^ (leftScaleBit 3 3 1).val * positiveScale (leftScaleExponent 3 3 1)) •
      (rowColumnMul HexagonRowColumn331.rows_assocBCA HexagonRowColumn331.cols_left0)) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 3 3 1) • (left1Middle3 3 1)) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem leftFinal3_case_3_1_row_1_1_0 : (((-1 : ℤ) ^ (leftScaleBit 3 3 1).val * positiveScale (leftScaleExponent 3 3 1)) •
      (rowColumnMul HexagonRowColumn331.rows_assocBCA HexagonRowColumn331.cols_left0)) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 3 3 1) • (left1Middle3 3 1)) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem leftFinal3_case_3_1_row_1_1_1 : (((-1 : ℤ) ^ (leftScaleBit 3 3 1).val * positiveScale (leftScaleExponent 3 3 1)) •
      (rowColumnMul HexagonRowColumn331.rows_assocBCA HexagonRowColumn331.cols_left0)) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 3 3 1) • (left1Middle3 3 1)) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem leftFinal3_case_3_1_row_1_2_0 : (((-1 : ℤ) ^ (leftScaleBit 3 3 1).val * positiveScale (leftScaleExponent 3 3 1)) •
      (rowColumnMul HexagonRowColumn331.rows_assocBCA HexagonRowColumn331.cols_left0)) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 3 3 1) • (left1Middle3 3 1)) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem leftFinal3_case_3_1_row_1_2_1 : (((-1 : ℤ) ^ (leftScaleBit 3 3 1).val * positiveScale (leftScaleExponent 3 3 1)) •
      (rowColumnMul HexagonRowColumn331.rows_assocBCA HexagonRowColumn331.cols_left0)) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 3 3 1) • (left1Middle3 3 1)) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem leftFinal3_case_3_1_row_1_3_0 : (((-1 : ℤ) ^ (leftScaleBit 3 3 1).val * positiveScale (leftScaleExponent 3 3 1)) •
      (rowColumnMul HexagonRowColumn331.rows_assocBCA HexagonRowColumn331.cols_left0)) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 3 3 1) • (left1Middle3 3 1)) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem leftFinal3_case_3_1_row_1_3_1 : (((-1 : ℤ) ^ (leftScaleBit 3 3 1).val * positiveScale (leftScaleExponent 3 3 1)) •
      (rowColumnMul HexagonRowColumn331.rows_assocBCA HexagonRowColumn331.cols_left0)) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 3 3 1) • (left1Middle3 3 1)) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem leftFinal3_case_3_1_checked : ((-1 : ℤ) ^ (leftScaleBit 3 3 1).val * positiveScale (leftScaleExponent 3 3 1)) •
      (rowColumnMul HexagonRowColumn331.rows_assocBCA HexagonRowColumn331.cols_left0) = negativeScale (leftScaleExponent 3 3 1) • (left1Middle3 3 1) := by
  funext r
  fin_cases r
  · exact leftFinal3_case_3_1_row_0_0_0
  · exact leftFinal3_case_3_1_row_0_0_1
  · exact leftFinal3_case_3_1_row_0_1_0
  · exact leftFinal3_case_3_1_row_0_1_1
  · exact leftFinal3_case_3_1_row_0_2_0
  · exact leftFinal3_case_3_1_row_0_2_1
  · exact leftFinal3_case_3_1_row_0_3_0
  · exact leftFinal3_case_3_1_row_0_3_1
  · exact leftFinal3_case_3_1_row_1_0_0
  · exact leftFinal3_case_3_1_row_1_0_1
  · exact leftFinal3_case_3_1_row_1_1_0
  · exact leftFinal3_case_3_1_row_1_1_1
  · exact leftFinal3_case_3_1_row_1_2_0
  · exact leftFinal3_case_3_1_row_1_2_1
  · exact leftFinal3_case_3_1_row_1_3_0
  · exact leftFinal3_case_3_1_row_1_3_1

set_option backward.isDefEq.respectTransparency false in
theorem leftFinal3_case_3_1 : ((-1 : ℤ) ^ (leftScaleBit 3 3 1).val * positiveScale (leftScaleExponent 3 3 1)) •
      (associatorZ 3 1 3 * left0Middle3 3 1) = negativeScale (leftScaleExponent 3 3 1) • (innerRightZ 3 3 1 * left1Middle3 3 1) := by
  simpa only [HexagonAtoms331.assocABC_eq,
    HexagonAtoms331.outerABC_eq,
    HexagonAtoms331.assocBAC_eq,
    HexagonAtoms331.innerABC_eq,
    HexagonAtoms331.innerRightABC_eq,
    HexagonAtoms331.inverseACB_eq,
    HexagonAtoms331.innerACB_eq,
    HexagonAtoms331.assocBCA_eq,
    HexagonAtoms331.innerRightBAC_eq,
    HexagonAtoms331.assocCAB_eq,
    HexagonAtoms331.outerLeftABC_eq,
    HexagonRowColumn331.assocBAC_alias,
    HexagonRowColumn331.innerRightBAC_alias,
    HexagonRowColumn331.product0_eq,
    HexagonRowColumn331.product1_eq,
    HexagonRowColumn331.product2_eq,
    HexagonRowColumn331.product3_eq,
    HexagonRowColumn331.product4_eq,
    HexagonRowColumn331.product5_eq,
    HexagonRowColumn331.product6_eq,
    HexagonRowColumn331.product7_eq] using leftFinal3_case_3_1_checked

private theorem rightFinal3_case_3_1_row_0_0_0 : (((-1 : ℤ) ^ (rightScaleBit 3 3 1).val * positiveScale (rightScaleExponent 3 3 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 1 3 : ℤ)) • HexagonAtoms331.outerLeftABC) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (negativeScale (rightScaleExponent 3 3 1) • (rowColumnMul HexagonRowColumn331.rows_assocCAB HexagonRowColumn331.cols_right2)) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem rightFinal3_case_3_1_row_0_0_1 : (((-1 : ℤ) ^ (rightScaleBit 3 3 1).val * positiveScale (rightScaleExponent 3 3 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 1 3 : ℤ)) • HexagonAtoms331.outerLeftABC) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (negativeScale (rightScaleExponent 3 3 1) • (rowColumnMul HexagonRowColumn331.rows_assocCAB HexagonRowColumn331.cols_right2)) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem rightFinal3_case_3_1_row_0_1_0 : (((-1 : ℤ) ^ (rightScaleBit 3 3 1).val * positiveScale (rightScaleExponent 3 3 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 1 3 : ℤ)) • HexagonAtoms331.outerLeftABC) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (negativeScale (rightScaleExponent 3 3 1) • (rowColumnMul HexagonRowColumn331.rows_assocCAB HexagonRowColumn331.cols_right2)) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem rightFinal3_case_3_1_row_0_1_1 : (((-1 : ℤ) ^ (rightScaleBit 3 3 1).val * positiveScale (rightScaleExponent 3 3 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 1 3 : ℤ)) • HexagonAtoms331.outerLeftABC) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (negativeScale (rightScaleExponent 3 3 1) • (rowColumnMul HexagonRowColumn331.rows_assocCAB HexagonRowColumn331.cols_right2)) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem rightFinal3_case_3_1_row_1_0_0 : (((-1 : ℤ) ^ (rightScaleBit 3 3 1).val * positiveScale (rightScaleExponent 3 3 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 1 3 : ℤ)) • HexagonAtoms331.outerLeftABC) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (negativeScale (rightScaleExponent 3 3 1) • (rowColumnMul HexagonRowColumn331.rows_assocCAB HexagonRowColumn331.cols_right2)) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem rightFinal3_case_3_1_row_1_0_1 : (((-1 : ℤ) ^ (rightScaleBit 3 3 1).val * positiveScale (rightScaleExponent 3 3 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 1 3 : ℤ)) • HexagonAtoms331.outerLeftABC) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (negativeScale (rightScaleExponent 3 3 1) • (rowColumnMul HexagonRowColumn331.rows_assocCAB HexagonRowColumn331.cols_right2)) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem rightFinal3_case_3_1_row_1_1_0 : (((-1 : ℤ) ^ (rightScaleBit 3 3 1).val * positiveScale (rightScaleExponent 3 3 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 1 3 : ℤ)) • HexagonAtoms331.outerLeftABC) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (negativeScale (rightScaleExponent 3 3 1) • (rowColumnMul HexagonRowColumn331.rows_assocCAB HexagonRowColumn331.cols_right2)) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem rightFinal3_case_3_1_row_1_1_1 : (((-1 : ℤ) ^ (rightScaleBit 3 3 1).val * positiveScale (rightScaleExponent 3 3 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 1 3 : ℤ)) • HexagonAtoms331.outerLeftABC) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (negativeScale (rightScaleExponent 3 3 1) • (rowColumnMul HexagonRowColumn331.rows_assocCAB HexagonRowColumn331.cols_right2)) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem rightFinal3_case_3_1_row_2_0_0 : (((-1 : ℤ) ^ (rightScaleBit 3 3 1).val * positiveScale (rightScaleExponent 3 3 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 1 3 : ℤ)) • HexagonAtoms331.outerLeftABC) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (negativeScale (rightScaleExponent 3 3 1) • (rowColumnMul HexagonRowColumn331.rows_assocCAB HexagonRowColumn331.cols_right2)) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem rightFinal3_case_3_1_row_2_0_1 : (((-1 : ℤ) ^ (rightScaleBit 3 3 1).val * positiveScale (rightScaleExponent 3 3 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 1 3 : ℤ)) • HexagonAtoms331.outerLeftABC) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (negativeScale (rightScaleExponent 3 3 1) • (rowColumnMul HexagonRowColumn331.rows_assocCAB HexagonRowColumn331.cols_right2)) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem rightFinal3_case_3_1_row_2_1_0 : (((-1 : ℤ) ^ (rightScaleBit 3 3 1).val * positiveScale (rightScaleExponent 3 3 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 1 3 : ℤ)) • HexagonAtoms331.outerLeftABC) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (negativeScale (rightScaleExponent 3 3 1) • (rowColumnMul HexagonRowColumn331.rows_assocCAB HexagonRowColumn331.cols_right2)) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem rightFinal3_case_3_1_row_2_1_1 : (((-1 : ℤ) ^ (rightScaleBit 3 3 1).val * positiveScale (rightScaleExponent 3 3 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 1 3 : ℤ)) • HexagonAtoms331.outerLeftABC) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (negativeScale (rightScaleExponent 3 3 1) • (rowColumnMul HexagonRowColumn331.rows_assocCAB HexagonRowColumn331.cols_right2)) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem rightFinal3_case_3_1_row_3_0_0 : (((-1 : ℤ) ^ (rightScaleBit 3 3 1).val * positiveScale (rightScaleExponent 3 3 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 1 3 : ℤ)) • HexagonAtoms331.outerLeftABC) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (negativeScale (rightScaleExponent 3 3 1) • (rowColumnMul HexagonRowColumn331.rows_assocCAB HexagonRowColumn331.cols_right2)) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem rightFinal3_case_3_1_row_3_0_1 : (((-1 : ℤ) ^ (rightScaleBit 3 3 1).val * positiveScale (rightScaleExponent 3 3 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 1 3 : ℤ)) • HexagonAtoms331.outerLeftABC) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (negativeScale (rightScaleExponent 3 3 1) • (rowColumnMul HexagonRowColumn331.rows_assocCAB HexagonRowColumn331.cols_right2)) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem rightFinal3_case_3_1_row_3_1_0 : (((-1 : ℤ) ^ (rightScaleBit 3 3 1).val * positiveScale (rightScaleExponent 3 3 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 1 3 : ℤ)) • HexagonAtoms331.outerLeftABC) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (negativeScale (rightScaleExponent 3 3 1) • (rowColumnMul HexagonRowColumn331.rows_assocCAB HexagonRowColumn331.cols_right2)) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem rightFinal3_case_3_1_row_3_1_1 : (((-1 : ℤ) ^ (rightScaleBit 3 3 1).val * positiveScale (rightScaleExponent 3 3 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 1 3 : ℤ)) • HexagonAtoms331.outerLeftABC) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (negativeScale (rightScaleExponent 3 3 1) • (rowColumnMul HexagonRowColumn331.rows_assocCAB HexagonRowColumn331.cols_right2)) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem rightFinal3_case_3_1_checked : ((-1 : ℤ) ^ (rightScaleBit 3 3 1).val * positiveScale (rightScaleExponent 3 3 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 1 3 : ℤ)) • HexagonAtoms331.outerLeftABC = negativeScale (rightScaleExponent 3 3 1) • (rowColumnMul HexagonRowColumn331.rows_assocCAB HexagonRowColumn331.cols_right2) := by
  funext r
  fin_cases r
  · exact rightFinal3_case_3_1_row_0_0_0
  · exact rightFinal3_case_3_1_row_0_0_1
  · exact rightFinal3_case_3_1_row_0_1_0
  · exact rightFinal3_case_3_1_row_0_1_1
  · exact rightFinal3_case_3_1_row_1_0_0
  · exact rightFinal3_case_3_1_row_1_0_1
  · exact rightFinal3_case_3_1_row_1_1_0
  · exact rightFinal3_case_3_1_row_1_1_1
  · exact rightFinal3_case_3_1_row_2_0_0
  · exact rightFinal3_case_3_1_row_2_0_1
  · exact rightFinal3_case_3_1_row_2_1_0
  · exact rightFinal3_case_3_1_row_2_1_1
  · exact rightFinal3_case_3_1_row_3_0_0
  · exact rightFinal3_case_3_1_row_3_0_1
  · exact rightFinal3_case_3_1_row_3_1_0
  · exact rightFinal3_case_3_1_row_3_1_1

set_option backward.isDefEq.respectTransparency false in
theorem rightFinal3_case_3_1 : ((-1 : ℤ) ^ (rightScaleBit 3 3 1).val * positiveScale (rightScaleExponent 3 3 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 1 3 : ℤ)) • outerLeftZ 3 3 1 = negativeScale (rightScaleExponent 3 3 1) • (associatorZ 1 3 3 * right2Middle3 3 1) := by
  simpa only [HexagonAtoms331.assocABC_eq,
    HexagonAtoms331.outerABC_eq,
    HexagonAtoms331.assocBAC_eq,
    HexagonAtoms331.innerABC_eq,
    HexagonAtoms331.innerRightABC_eq,
    HexagonAtoms331.inverseACB_eq,
    HexagonAtoms331.innerACB_eq,
    HexagonAtoms331.assocBCA_eq,
    HexagonAtoms331.innerRightBAC_eq,
    HexagonAtoms331.assocCAB_eq,
    HexagonAtoms331.outerLeftABC_eq,
    HexagonRowColumn331.assocBAC_alias,
    HexagonRowColumn331.innerRightBAC_alias,
    HexagonRowColumn331.product0_eq,
    HexagonRowColumn331.product1_eq,
    HexagonRowColumn331.product2_eq,
    HexagonRowColumn331.product3_eq,
    HexagonRowColumn331.product4_eq,
    HexagonRowColumn331.product5_eq,
    HexagonRowColumn331.product6_eq,
    HexagonRowColumn331.product7_eq] using rightFinal3_case_3_1_checked

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonCases3
