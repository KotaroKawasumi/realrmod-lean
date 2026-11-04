import RMod.BrundanEllis.StackingReferenceHexagonMiddle5
import RMod.BrundanEllis.StackingReferenceSparseMatrixCheck
import RMod.BrundanEllis.StackingReferenceHexagonAtoms557
import RMod.BrundanEllis.StackingReferenceHexagonRowColumn557

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

private theorem left0Middle5_eq_case_5_7_row_0_0_0 : (left0Middle5 5 7) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (HexagonAtoms557.assocABC) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_5_7_row_0_0_1 : (left0Middle5 5 7) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (HexagonAtoms557.assocABC) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_5_7_row_0_1_0 : (left0Middle5 5 7) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (HexagonAtoms557.assocABC) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_5_7_row_0_1_1 : (left0Middle5 5 7) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (HexagonAtoms557.assocABC) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_5_7_row_0_2_0 : (left0Middle5 5 7) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (HexagonAtoms557.assocABC) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_5_7_row_0_2_1 : (left0Middle5 5 7) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (HexagonAtoms557.assocABC) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_5_7_row_0_3_0 : (left0Middle5 5 7) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (HexagonAtoms557.assocABC) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_5_7_row_0_3_1 : (left0Middle5 5 7) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (HexagonAtoms557.assocABC) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_5_7_row_1_0_0 : (left0Middle5 5 7) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (HexagonAtoms557.assocABC) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_5_7_row_1_0_1 : (left0Middle5 5 7) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (HexagonAtoms557.assocABC) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_5_7_row_1_1_0 : (left0Middle5 5 7) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (HexagonAtoms557.assocABC) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_5_7_row_1_1_1 : (left0Middle5 5 7) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (HexagonAtoms557.assocABC) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_5_7_row_1_2_0 : (left0Middle5 5 7) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (HexagonAtoms557.assocABC) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_5_7_row_1_2_1 : (left0Middle5 5 7) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (HexagonAtoms557.assocABC) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_5_7_row_1_3_0 : (left0Middle5 5 7) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (HexagonAtoms557.assocABC) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_5_7_row_1_3_1 : (left0Middle5 5 7) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (HexagonAtoms557.assocABC) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_5_7_checked : left0Middle5 5 7 = HexagonAtoms557.assocABC := by
  funext r
  fin_cases r
  · exact left0Middle5_eq_case_5_7_row_0_0_0
  · exact left0Middle5_eq_case_5_7_row_0_0_1
  · exact left0Middle5_eq_case_5_7_row_0_1_0
  · exact left0Middle5_eq_case_5_7_row_0_1_1
  · exact left0Middle5_eq_case_5_7_row_0_2_0
  · exact left0Middle5_eq_case_5_7_row_0_2_1
  · exact left0Middle5_eq_case_5_7_row_0_3_0
  · exact left0Middle5_eq_case_5_7_row_0_3_1
  · exact left0Middle5_eq_case_5_7_row_1_0_0
  · exact left0Middle5_eq_case_5_7_row_1_0_1
  · exact left0Middle5_eq_case_5_7_row_1_1_0
  · exact left0Middle5_eq_case_5_7_row_1_1_1
  · exact left0Middle5_eq_case_5_7_row_1_2_0
  · exact left0Middle5_eq_case_5_7_row_1_2_1
  · exact left0Middle5_eq_case_5_7_row_1_3_0
  · exact left0Middle5_eq_case_5_7_row_1_3_1

set_option backward.isDefEq.respectTransparency false in
theorem left0Middle5_eq_case_5_7 : left0Middle5 5 7 = outerRightZ 5 5 7 * associatorZ 5 5 7 := by
  simpa only [HexagonAtoms557.assocABC_eq,
    HexagonAtoms557.outerABC_eq,
    HexagonAtoms557.assocBAC_eq,
    HexagonAtoms557.innerABC_eq,
    HexagonAtoms557.innerRightABC_eq,
    HexagonAtoms557.inverseACB_eq,
    HexagonAtoms557.innerACB_eq,
    HexagonAtoms557.assocBCA_eq,
    HexagonAtoms557.innerRightBAC_eq,
    HexagonAtoms557.assocCAB_eq,
    HexagonAtoms557.outerLeftABC_eq,
    HexagonRowColumn557.assocBAC_alias,
    HexagonRowColumn557.innerRightBAC_alias,
    HexagonRowColumn557.product0_eq,
    HexagonRowColumn557.product1_eq,
    HexagonRowColumn557.product2_eq,
    HexagonRowColumn557.product3_eq,
    HexagonRowColumn557.product4_eq,
    HexagonRowColumn557.product5_eq,
    HexagonRowColumn557.product6_eq,
    HexagonRowColumn557.product7_eq] using left0Middle5_eq_case_5_7_checked

private theorem left1Middle5_eq_case_5_7_row_0_0_0 : (left1Middle5 5 7) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn557.rows_assocABC HexagonRowColumn557.cols_innerABC) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_5_7_row_0_0_1 : (left1Middle5 5 7) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn557.rows_assocABC HexagonRowColumn557.cols_innerABC) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_5_7_row_0_1_0 : (left1Middle5 5 7) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn557.rows_assocABC HexagonRowColumn557.cols_innerABC) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_5_7_row_0_1_1 : (left1Middle5 5 7) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn557.rows_assocABC HexagonRowColumn557.cols_innerABC) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_5_7_row_0_2_0 : (left1Middle5 5 7) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn557.rows_assocABC HexagonRowColumn557.cols_innerABC) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_5_7_row_0_2_1 : (left1Middle5 5 7) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn557.rows_assocABC HexagonRowColumn557.cols_innerABC) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_5_7_row_0_3_0 : (left1Middle5 5 7) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn557.rows_assocABC HexagonRowColumn557.cols_innerABC) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_5_7_row_0_3_1 : (left1Middle5 5 7) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn557.rows_assocABC HexagonRowColumn557.cols_innerABC) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_5_7_row_1_0_0 : (left1Middle5 5 7) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn557.rows_assocABC HexagonRowColumn557.cols_innerABC) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_5_7_row_1_0_1 : (left1Middle5 5 7) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn557.rows_assocABC HexagonRowColumn557.cols_innerABC) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_5_7_row_1_1_0 : (left1Middle5 5 7) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn557.rows_assocABC HexagonRowColumn557.cols_innerABC) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_5_7_row_1_1_1 : (left1Middle5 5 7) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn557.rows_assocABC HexagonRowColumn557.cols_innerABC) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_5_7_row_1_2_0 : (left1Middle5 5 7) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn557.rows_assocABC HexagonRowColumn557.cols_innerABC) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_5_7_row_1_2_1 : (left1Middle5 5 7) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn557.rows_assocABC HexagonRowColumn557.cols_innerABC) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_5_7_row_1_3_0 : (left1Middle5 5 7) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn557.rows_assocABC HexagonRowColumn557.cols_innerABC) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_5_7_row_1_3_1 : (left1Middle5 5 7) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn557.rows_assocABC HexagonRowColumn557.cols_innerABC) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_5_7_checked : left1Middle5 5 7 = rowColumnMul HexagonRowColumn557.rows_assocABC HexagonRowColumn557.cols_innerABC := by
  funext r
  fin_cases r
  · exact left1Middle5_eq_case_5_7_row_0_0_0
  · exact left1Middle5_eq_case_5_7_row_0_0_1
  · exact left1Middle5_eq_case_5_7_row_0_1_0
  · exact left1Middle5_eq_case_5_7_row_0_1_1
  · exact left1Middle5_eq_case_5_7_row_0_2_0
  · exact left1Middle5_eq_case_5_7_row_0_2_1
  · exact left1Middle5_eq_case_5_7_row_0_3_0
  · exact left1Middle5_eq_case_5_7_row_0_3_1
  · exact left1Middle5_eq_case_5_7_row_1_0_0
  · exact left1Middle5_eq_case_5_7_row_1_0_1
  · exact left1Middle5_eq_case_5_7_row_1_1_0
  · exact left1Middle5_eq_case_5_7_row_1_1_1
  · exact left1Middle5_eq_case_5_7_row_1_2_0
  · exact left1Middle5_eq_case_5_7_row_1_2_1
  · exact left1Middle5_eq_case_5_7_row_1_3_0
  · exact left1Middle5_eq_case_5_7_row_1_3_1

set_option backward.isDefEq.respectTransparency false in
theorem left1Middle5_eq_case_5_7 : left1Middle5 5 7 = associatorZ 5 5 7 * innerLeftZ 5 5 7 := by
  simpa only [HexagonAtoms557.assocABC_eq,
    HexagonAtoms557.outerABC_eq,
    HexagonAtoms557.assocBAC_eq,
    HexagonAtoms557.innerABC_eq,
    HexagonAtoms557.innerRightABC_eq,
    HexagonAtoms557.inverseACB_eq,
    HexagonAtoms557.innerACB_eq,
    HexagonAtoms557.assocBCA_eq,
    HexagonAtoms557.innerRightBAC_eq,
    HexagonAtoms557.assocCAB_eq,
    HexagonAtoms557.outerLeftABC_eq,
    HexagonRowColumn557.assocBAC_alias,
    HexagonRowColumn557.innerRightBAC_alias,
    HexagonRowColumn557.product0_eq,
    HexagonRowColumn557.product1_eq,
    HexagonRowColumn557.product2_eq,
    HexagonRowColumn557.product3_eq,
    HexagonRowColumn557.product4_eq,
    HexagonRowColumn557.product5_eq,
    HexagonRowColumn557.product6_eq,
    HexagonRowColumn557.product7_eq] using left1Middle5_eq_case_5_7_checked

private theorem right0Middle5_eq_case_5_7_row_0_0_0 : (right0Middle5 5 7) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (HexagonAtoms557.assocABC) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_5_7_row_0_0_1 : (right0Middle5 5 7) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (HexagonAtoms557.assocABC) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_5_7_row_0_1_0 : (right0Middle5 5 7) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (HexagonAtoms557.assocABC) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_5_7_row_0_1_1 : (right0Middle5 5 7) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (HexagonAtoms557.assocABC) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_5_7_row_0_2_0 : (right0Middle5 5 7) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (HexagonAtoms557.assocABC) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_5_7_row_0_2_1 : (right0Middle5 5 7) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (HexagonAtoms557.assocABC) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_5_7_row_0_3_0 : (right0Middle5 5 7) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (HexagonAtoms557.assocABC) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_5_7_row_0_3_1 : (right0Middle5 5 7) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (HexagonAtoms557.assocABC) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_5_7_row_1_0_0 : (right0Middle5 5 7) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (HexagonAtoms557.assocABC) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_5_7_row_1_0_1 : (right0Middle5 5 7) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (HexagonAtoms557.assocABC) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_5_7_row_1_1_0 : (right0Middle5 5 7) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (HexagonAtoms557.assocABC) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_5_7_row_1_1_1 : (right0Middle5 5 7) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (HexagonAtoms557.assocABC) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_5_7_row_1_2_0 : (right0Middle5 5 7) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (HexagonAtoms557.assocABC) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_5_7_row_1_2_1 : (right0Middle5 5 7) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (HexagonAtoms557.assocABC) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_5_7_row_1_3_0 : (right0Middle5 5 7) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (HexagonAtoms557.assocABC) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_5_7_row_1_3_1 : (right0Middle5 5 7) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (HexagonAtoms557.assocABC) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_5_7_checked : right0Middle5 5 7 = HexagonAtoms557.assocABC := by
  funext r
  fin_cases r
  · exact right0Middle5_eq_case_5_7_row_0_0_0
  · exact right0Middle5_eq_case_5_7_row_0_0_1
  · exact right0Middle5_eq_case_5_7_row_0_1_0
  · exact right0Middle5_eq_case_5_7_row_0_1_1
  · exact right0Middle5_eq_case_5_7_row_0_2_0
  · exact right0Middle5_eq_case_5_7_row_0_2_1
  · exact right0Middle5_eq_case_5_7_row_0_3_0
  · exact right0Middle5_eq_case_5_7_row_0_3_1
  · exact right0Middle5_eq_case_5_7_row_1_0_0
  · exact right0Middle5_eq_case_5_7_row_1_0_1
  · exact right0Middle5_eq_case_5_7_row_1_1_0
  · exact right0Middle5_eq_case_5_7_row_1_1_1
  · exact right0Middle5_eq_case_5_7_row_1_2_0
  · exact right0Middle5_eq_case_5_7_row_1_2_1
  · exact right0Middle5_eq_case_5_7_row_1_3_0
  · exact right0Middle5_eq_case_5_7_row_1_3_1

set_option backward.isDefEq.respectTransparency false in
theorem right0Middle5_eq_case_5_7 : right0Middle5 5 7 = innerRightZ 5 5 7 * associatorZ 5 5 7 := by
  simpa only [HexagonAtoms557.assocABC_eq,
    HexagonAtoms557.outerABC_eq,
    HexagonAtoms557.assocBAC_eq,
    HexagonAtoms557.innerABC_eq,
    HexagonAtoms557.innerRightABC_eq,
    HexagonAtoms557.inverseACB_eq,
    HexagonAtoms557.innerACB_eq,
    HexagonAtoms557.assocBCA_eq,
    HexagonAtoms557.innerRightBAC_eq,
    HexagonAtoms557.assocCAB_eq,
    HexagonAtoms557.outerLeftABC_eq,
    HexagonRowColumn557.assocBAC_alias,
    HexagonRowColumn557.innerRightBAC_alias,
    HexagonRowColumn557.product0_eq,
    HexagonRowColumn557.product1_eq,
    HexagonRowColumn557.product2_eq,
    HexagonRowColumn557.product3_eq,
    HexagonRowColumn557.product4_eq,
    HexagonRowColumn557.product5_eq,
    HexagonRowColumn557.product6_eq,
    HexagonRowColumn557.product7_eq] using right0Middle5_eq_case_5_7_checked

private theorem right1Middle5_eq_case_5_7_row_0_0_0 : (right1Middle5 5 7) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn557.rows_inverseACB HexagonRowColumn557.cols_right0) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_5_7_row_0_0_1 : (right1Middle5 5 7) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn557.rows_inverseACB HexagonRowColumn557.cols_right0) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_5_7_row_0_1_0 : (right1Middle5 5 7) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn557.rows_inverseACB HexagonRowColumn557.cols_right0) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_5_7_row_0_1_1 : (right1Middle5 5 7) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn557.rows_inverseACB HexagonRowColumn557.cols_right0) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_5_7_row_0_2_0 : (right1Middle5 5 7) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn557.rows_inverseACB HexagonRowColumn557.cols_right0) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_5_7_row_0_2_1 : (right1Middle5 5 7) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn557.rows_inverseACB HexagonRowColumn557.cols_right0) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_5_7_row_0_3_0 : (right1Middle5 5 7) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn557.rows_inverseACB HexagonRowColumn557.cols_right0) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_5_7_row_0_3_1 : (right1Middle5 5 7) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn557.rows_inverseACB HexagonRowColumn557.cols_right0) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_5_7_row_1_0_0 : (right1Middle5 5 7) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn557.rows_inverseACB HexagonRowColumn557.cols_right0) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_5_7_row_1_0_1 : (right1Middle5 5 7) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn557.rows_inverseACB HexagonRowColumn557.cols_right0) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_5_7_row_1_1_0 : (right1Middle5 5 7) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn557.rows_inverseACB HexagonRowColumn557.cols_right0) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_5_7_row_1_1_1 : (right1Middle5 5 7) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn557.rows_inverseACB HexagonRowColumn557.cols_right0) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_5_7_row_1_2_0 : (right1Middle5 5 7) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn557.rows_inverseACB HexagonRowColumn557.cols_right0) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_5_7_row_1_2_1 : (right1Middle5 5 7) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn557.rows_inverseACB HexagonRowColumn557.cols_right0) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_5_7_row_1_3_0 : (right1Middle5 5 7) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn557.rows_inverseACB HexagonRowColumn557.cols_right0) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_5_7_row_1_3_1 : (right1Middle5 5 7) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn557.rows_inverseACB HexagonRowColumn557.cols_right0) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_5_7_checked : right1Middle5 5 7 = rowColumnMul HexagonRowColumn557.rows_inverseACB HexagonRowColumn557.cols_right0 := by
  funext r
  fin_cases r
  · exact right1Middle5_eq_case_5_7_row_0_0_0
  · exact right1Middle5_eq_case_5_7_row_0_0_1
  · exact right1Middle5_eq_case_5_7_row_0_1_0
  · exact right1Middle5_eq_case_5_7_row_0_1_1
  · exact right1Middle5_eq_case_5_7_row_0_2_0
  · exact right1Middle5_eq_case_5_7_row_0_2_1
  · exact right1Middle5_eq_case_5_7_row_0_3_0
  · exact right1Middle5_eq_case_5_7_row_0_3_1
  · exact right1Middle5_eq_case_5_7_row_1_0_0
  · exact right1Middle5_eq_case_5_7_row_1_0_1
  · exact right1Middle5_eq_case_5_7_row_1_1_0
  · exact right1Middle5_eq_case_5_7_row_1_1_1
  · exact right1Middle5_eq_case_5_7_row_1_2_0
  · exact right1Middle5_eq_case_5_7_row_1_2_1
  · exact right1Middle5_eq_case_5_7_row_1_3_0
  · exact right1Middle5_eq_case_5_7_row_1_3_1

set_option backward.isDefEq.respectTransparency false in
theorem right1Middle5_eq_case_5_7 : right1Middle5 5 7 = associatorInverseZ 5 7 5 * right0Middle5 5 7 := by
  simpa only [HexagonAtoms557.assocABC_eq,
    HexagonAtoms557.outerABC_eq,
    HexagonAtoms557.assocBAC_eq,
    HexagonAtoms557.innerABC_eq,
    HexagonAtoms557.innerRightABC_eq,
    HexagonAtoms557.inverseACB_eq,
    HexagonAtoms557.innerACB_eq,
    HexagonAtoms557.assocBCA_eq,
    HexagonAtoms557.innerRightBAC_eq,
    HexagonAtoms557.assocCAB_eq,
    HexagonAtoms557.outerLeftABC_eq,
    HexagonRowColumn557.assocBAC_alias,
    HexagonRowColumn557.innerRightBAC_alias,
    HexagonRowColumn557.product0_eq,
    HexagonRowColumn557.product1_eq,
    HexagonRowColumn557.product2_eq,
    HexagonRowColumn557.product3_eq,
    HexagonRowColumn557.product4_eq,
    HexagonRowColumn557.product5_eq,
    HexagonRowColumn557.product6_eq,
    HexagonRowColumn557.product7_eq] using right1Middle5_eq_case_5_7_checked

private theorem right2Middle5_eq_case_5_7_row_0_0_0 : (right2Middle5 5 7) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (right1Middle5 5 7) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_5_7_row_0_0_1 : (right2Middle5 5 7) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (right1Middle5 5 7) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_5_7_row_0_1_0 : (right2Middle5 5 7) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (right1Middle5 5 7) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_5_7_row_0_1_1 : (right2Middle5 5 7) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (right1Middle5 5 7) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_5_7_row_0_2_0 : (right2Middle5 5 7) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (right1Middle5 5 7) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_5_7_row_0_2_1 : (right2Middle5 5 7) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (right1Middle5 5 7) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_5_7_row_0_3_0 : (right2Middle5 5 7) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (right1Middle5 5 7) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_5_7_row_0_3_1 : (right2Middle5 5 7) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (right1Middle5 5 7) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_5_7_row_1_0_0 : (right2Middle5 5 7) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (right1Middle5 5 7) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_5_7_row_1_0_1 : (right2Middle5 5 7) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (right1Middle5 5 7) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_5_7_row_1_1_0 : (right2Middle5 5 7) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (right1Middle5 5 7) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_5_7_row_1_1_1 : (right2Middle5 5 7) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (right1Middle5 5 7) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_5_7_row_1_2_0 : (right2Middle5 5 7) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (right1Middle5 5 7) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_5_7_row_1_2_1 : (right2Middle5 5 7) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (right1Middle5 5 7) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_5_7_row_1_3_0 : (right2Middle5 5 7) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (right1Middle5 5 7) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_5_7_row_1_3_1 : (right2Middle5 5 7) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (right1Middle5 5 7) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_5_7_checked : right2Middle5 5 7 = right1Middle5 5 7 := by
  funext r
  fin_cases r
  · exact right2Middle5_eq_case_5_7_row_0_0_0
  · exact right2Middle5_eq_case_5_7_row_0_0_1
  · exact right2Middle5_eq_case_5_7_row_0_1_0
  · exact right2Middle5_eq_case_5_7_row_0_1_1
  · exact right2Middle5_eq_case_5_7_row_0_2_0
  · exact right2Middle5_eq_case_5_7_row_0_2_1
  · exact right2Middle5_eq_case_5_7_row_0_3_0
  · exact right2Middle5_eq_case_5_7_row_0_3_1
  · exact right2Middle5_eq_case_5_7_row_1_0_0
  · exact right2Middle5_eq_case_5_7_row_1_0_1
  · exact right2Middle5_eq_case_5_7_row_1_1_0
  · exact right2Middle5_eq_case_5_7_row_1_1_1
  · exact right2Middle5_eq_case_5_7_row_1_2_0
  · exact right2Middle5_eq_case_5_7_row_1_2_1
  · exact right2Middle5_eq_case_5_7_row_1_3_0
  · exact right2Middle5_eq_case_5_7_row_1_3_1

set_option backward.isDefEq.respectTransparency false in
theorem right2Middle5_eq_case_5_7 : right2Middle5 5 7 = innerLeftZ 5 7 5 * right1Middle5 5 7 := by
  simpa only [HexagonAtoms557.assocABC_eq,
    HexagonAtoms557.outerABC_eq,
    HexagonAtoms557.assocBAC_eq,
    HexagonAtoms557.innerABC_eq,
    HexagonAtoms557.innerRightABC_eq,
    HexagonAtoms557.inverseACB_eq,
    HexagonAtoms557.innerACB_eq,
    HexagonAtoms557.assocBCA_eq,
    HexagonAtoms557.innerRightBAC_eq,
    HexagonAtoms557.assocCAB_eq,
    HexagonAtoms557.outerLeftABC_eq,
    HexagonRowColumn557.assocBAC_alias,
    HexagonRowColumn557.innerRightBAC_alias,
    HexagonRowColumn557.product0_eq,
    HexagonRowColumn557.product1_eq,
    HexagonRowColumn557.product2_eq,
    HexagonRowColumn557.product3_eq,
    HexagonRowColumn557.product4_eq,
    HexagonRowColumn557.product5_eq,
    HexagonRowColumn557.product6_eq,
    HexagonRowColumn557.product7_eq] using right2Middle5_eq_case_5_7_checked

private theorem leftFinal5_case_5_7_row_0_0_0 : (((-1 : ℤ) ^ (leftScaleBit 5 5 7).val * positiveScale (leftScaleExponent 5 5 7)) •
      (rowColumnMul HexagonRowColumn557.rows_assocBCA HexagonRowColumn557.cols_left0)) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 5 5 7) • (left1Middle5 5 7)) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem leftFinal5_case_5_7_row_0_0_1 : (((-1 : ℤ) ^ (leftScaleBit 5 5 7).val * positiveScale (leftScaleExponent 5 5 7)) •
      (rowColumnMul HexagonRowColumn557.rows_assocBCA HexagonRowColumn557.cols_left0)) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 5 5 7) • (left1Middle5 5 7)) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem leftFinal5_case_5_7_row_0_1_0 : (((-1 : ℤ) ^ (leftScaleBit 5 5 7).val * positiveScale (leftScaleExponent 5 5 7)) •
      (rowColumnMul HexagonRowColumn557.rows_assocBCA HexagonRowColumn557.cols_left0)) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 5 5 7) • (left1Middle5 5 7)) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem leftFinal5_case_5_7_row_0_1_1 : (((-1 : ℤ) ^ (leftScaleBit 5 5 7).val * positiveScale (leftScaleExponent 5 5 7)) •
      (rowColumnMul HexagonRowColumn557.rows_assocBCA HexagonRowColumn557.cols_left0)) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 5 5 7) • (left1Middle5 5 7)) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem leftFinal5_case_5_7_row_0_2_0 : (((-1 : ℤ) ^ (leftScaleBit 5 5 7).val * positiveScale (leftScaleExponent 5 5 7)) •
      (rowColumnMul HexagonRowColumn557.rows_assocBCA HexagonRowColumn557.cols_left0)) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 5 5 7) • (left1Middle5 5 7)) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem leftFinal5_case_5_7_row_0_2_1 : (((-1 : ℤ) ^ (leftScaleBit 5 5 7).val * positiveScale (leftScaleExponent 5 5 7)) •
      (rowColumnMul HexagonRowColumn557.rows_assocBCA HexagonRowColumn557.cols_left0)) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 5 5 7) • (left1Middle5 5 7)) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem leftFinal5_case_5_7_row_0_3_0 : (((-1 : ℤ) ^ (leftScaleBit 5 5 7).val * positiveScale (leftScaleExponent 5 5 7)) •
      (rowColumnMul HexagonRowColumn557.rows_assocBCA HexagonRowColumn557.cols_left0)) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 5 5 7) • (left1Middle5 5 7)) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem leftFinal5_case_5_7_row_0_3_1 : (((-1 : ℤ) ^ (leftScaleBit 5 5 7).val * positiveScale (leftScaleExponent 5 5 7)) •
      (rowColumnMul HexagonRowColumn557.rows_assocBCA HexagonRowColumn557.cols_left0)) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 5 5 7) • (left1Middle5 5 7)) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem leftFinal5_case_5_7_row_1_0_0 : (((-1 : ℤ) ^ (leftScaleBit 5 5 7).val * positiveScale (leftScaleExponent 5 5 7)) •
      (rowColumnMul HexagonRowColumn557.rows_assocBCA HexagonRowColumn557.cols_left0)) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 5 5 7) • (left1Middle5 5 7)) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem leftFinal5_case_5_7_row_1_0_1 : (((-1 : ℤ) ^ (leftScaleBit 5 5 7).val * positiveScale (leftScaleExponent 5 5 7)) •
      (rowColumnMul HexagonRowColumn557.rows_assocBCA HexagonRowColumn557.cols_left0)) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 5 5 7) • (left1Middle5 5 7)) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem leftFinal5_case_5_7_row_1_1_0 : (((-1 : ℤ) ^ (leftScaleBit 5 5 7).val * positiveScale (leftScaleExponent 5 5 7)) •
      (rowColumnMul HexagonRowColumn557.rows_assocBCA HexagonRowColumn557.cols_left0)) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 5 5 7) • (left1Middle5 5 7)) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem leftFinal5_case_5_7_row_1_1_1 : (((-1 : ℤ) ^ (leftScaleBit 5 5 7).val * positiveScale (leftScaleExponent 5 5 7)) •
      (rowColumnMul HexagonRowColumn557.rows_assocBCA HexagonRowColumn557.cols_left0)) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 5 5 7) • (left1Middle5 5 7)) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem leftFinal5_case_5_7_row_1_2_0 : (((-1 : ℤ) ^ (leftScaleBit 5 5 7).val * positiveScale (leftScaleExponent 5 5 7)) •
      (rowColumnMul HexagonRowColumn557.rows_assocBCA HexagonRowColumn557.cols_left0)) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 5 5 7) • (left1Middle5 5 7)) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem leftFinal5_case_5_7_row_1_2_1 : (((-1 : ℤ) ^ (leftScaleBit 5 5 7).val * positiveScale (leftScaleExponent 5 5 7)) •
      (rowColumnMul HexagonRowColumn557.rows_assocBCA HexagonRowColumn557.cols_left0)) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 5 5 7) • (left1Middle5 5 7)) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem leftFinal5_case_5_7_row_1_3_0 : (((-1 : ℤ) ^ (leftScaleBit 5 5 7).val * positiveScale (leftScaleExponent 5 5 7)) •
      (rowColumnMul HexagonRowColumn557.rows_assocBCA HexagonRowColumn557.cols_left0)) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 5 5 7) • (left1Middle5 5 7)) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem leftFinal5_case_5_7_row_1_3_1 : (((-1 : ℤ) ^ (leftScaleBit 5 5 7).val * positiveScale (leftScaleExponent 5 5 7)) •
      (rowColumnMul HexagonRowColumn557.rows_assocBCA HexagonRowColumn557.cols_left0)) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 5 5 7) • (left1Middle5 5 7)) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem leftFinal5_case_5_7_checked : ((-1 : ℤ) ^ (leftScaleBit 5 5 7).val * positiveScale (leftScaleExponent 5 5 7)) •
      (rowColumnMul HexagonRowColumn557.rows_assocBCA HexagonRowColumn557.cols_left0) = negativeScale (leftScaleExponent 5 5 7) • (left1Middle5 5 7) := by
  funext r
  fin_cases r
  · exact leftFinal5_case_5_7_row_0_0_0
  · exact leftFinal5_case_5_7_row_0_0_1
  · exact leftFinal5_case_5_7_row_0_1_0
  · exact leftFinal5_case_5_7_row_0_1_1
  · exact leftFinal5_case_5_7_row_0_2_0
  · exact leftFinal5_case_5_7_row_0_2_1
  · exact leftFinal5_case_5_7_row_0_3_0
  · exact leftFinal5_case_5_7_row_0_3_1
  · exact leftFinal5_case_5_7_row_1_0_0
  · exact leftFinal5_case_5_7_row_1_0_1
  · exact leftFinal5_case_5_7_row_1_1_0
  · exact leftFinal5_case_5_7_row_1_1_1
  · exact leftFinal5_case_5_7_row_1_2_0
  · exact leftFinal5_case_5_7_row_1_2_1
  · exact leftFinal5_case_5_7_row_1_3_0
  · exact leftFinal5_case_5_7_row_1_3_1

set_option backward.isDefEq.respectTransparency false in
theorem leftFinal5_case_5_7 : ((-1 : ℤ) ^ (leftScaleBit 5 5 7).val * positiveScale (leftScaleExponent 5 5 7)) •
      (associatorZ 5 7 5 * left0Middle5 5 7) = negativeScale (leftScaleExponent 5 5 7) • (innerRightZ 5 5 7 * left1Middle5 5 7) := by
  simpa only [HexagonAtoms557.assocABC_eq,
    HexagonAtoms557.outerABC_eq,
    HexagonAtoms557.assocBAC_eq,
    HexagonAtoms557.innerABC_eq,
    HexagonAtoms557.innerRightABC_eq,
    HexagonAtoms557.inverseACB_eq,
    HexagonAtoms557.innerACB_eq,
    HexagonAtoms557.assocBCA_eq,
    HexagonAtoms557.innerRightBAC_eq,
    HexagonAtoms557.assocCAB_eq,
    HexagonAtoms557.outerLeftABC_eq,
    HexagonRowColumn557.assocBAC_alias,
    HexagonRowColumn557.innerRightBAC_alias,
    HexagonRowColumn557.product0_eq,
    HexagonRowColumn557.product1_eq,
    HexagonRowColumn557.product2_eq,
    HexagonRowColumn557.product3_eq,
    HexagonRowColumn557.product4_eq,
    HexagonRowColumn557.product5_eq,
    HexagonRowColumn557.product6_eq,
    HexagonRowColumn557.product7_eq] using leftFinal5_case_5_7_checked

private theorem rightFinal5_case_5_7_row_0_0_0 : (((-1 : ℤ) ^ (rightScaleBit 5 5 7).val * positiveScale (rightScaleExponent 5 5 7) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 7 5 : ℤ)) • HexagonAtoms557.outerLeftABC) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (negativeScale (rightScaleExponent 5 5 7) • (rowColumnMul HexagonRowColumn557.rows_assocCAB HexagonRowColumn557.cols_right2)) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem rightFinal5_case_5_7_row_0_0_1 : (((-1 : ℤ) ^ (rightScaleBit 5 5 7).val * positiveScale (rightScaleExponent 5 5 7) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 7 5 : ℤ)) • HexagonAtoms557.outerLeftABC) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (negativeScale (rightScaleExponent 5 5 7) • (rowColumnMul HexagonRowColumn557.rows_assocCAB HexagonRowColumn557.cols_right2)) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem rightFinal5_case_5_7_row_0_1_0 : (((-1 : ℤ) ^ (rightScaleBit 5 5 7).val * positiveScale (rightScaleExponent 5 5 7) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 7 5 : ℤ)) • HexagonAtoms557.outerLeftABC) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (negativeScale (rightScaleExponent 5 5 7) • (rowColumnMul HexagonRowColumn557.rows_assocCAB HexagonRowColumn557.cols_right2)) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem rightFinal5_case_5_7_row_0_1_1 : (((-1 : ℤ) ^ (rightScaleBit 5 5 7).val * positiveScale (rightScaleExponent 5 5 7) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 7 5 : ℤ)) • HexagonAtoms557.outerLeftABC) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (negativeScale (rightScaleExponent 5 5 7) • (rowColumnMul HexagonRowColumn557.rows_assocCAB HexagonRowColumn557.cols_right2)) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem rightFinal5_case_5_7_row_1_0_0 : (((-1 : ℤ) ^ (rightScaleBit 5 5 7).val * positiveScale (rightScaleExponent 5 5 7) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 7 5 : ℤ)) • HexagonAtoms557.outerLeftABC) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (negativeScale (rightScaleExponent 5 5 7) • (rowColumnMul HexagonRowColumn557.rows_assocCAB HexagonRowColumn557.cols_right2)) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem rightFinal5_case_5_7_row_1_0_1 : (((-1 : ℤ) ^ (rightScaleBit 5 5 7).val * positiveScale (rightScaleExponent 5 5 7) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 7 5 : ℤ)) • HexagonAtoms557.outerLeftABC) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (negativeScale (rightScaleExponent 5 5 7) • (rowColumnMul HexagonRowColumn557.rows_assocCAB HexagonRowColumn557.cols_right2)) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem rightFinal5_case_5_7_row_1_1_0 : (((-1 : ℤ) ^ (rightScaleBit 5 5 7).val * positiveScale (rightScaleExponent 5 5 7) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 7 5 : ℤ)) • HexagonAtoms557.outerLeftABC) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (negativeScale (rightScaleExponent 5 5 7) • (rowColumnMul HexagonRowColumn557.rows_assocCAB HexagonRowColumn557.cols_right2)) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem rightFinal5_case_5_7_row_1_1_1 : (((-1 : ℤ) ^ (rightScaleBit 5 5 7).val * positiveScale (rightScaleExponent 5 5 7) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 7 5 : ℤ)) • HexagonAtoms557.outerLeftABC) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (negativeScale (rightScaleExponent 5 5 7) • (rowColumnMul HexagonRowColumn557.rows_assocCAB HexagonRowColumn557.cols_right2)) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem rightFinal5_case_5_7_row_2_0_0 : (((-1 : ℤ) ^ (rightScaleBit 5 5 7).val * positiveScale (rightScaleExponent 5 5 7) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 7 5 : ℤ)) • HexagonAtoms557.outerLeftABC) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (negativeScale (rightScaleExponent 5 5 7) • (rowColumnMul HexagonRowColumn557.rows_assocCAB HexagonRowColumn557.cols_right2)) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem rightFinal5_case_5_7_row_2_0_1 : (((-1 : ℤ) ^ (rightScaleBit 5 5 7).val * positiveScale (rightScaleExponent 5 5 7) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 7 5 : ℤ)) • HexagonAtoms557.outerLeftABC) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (negativeScale (rightScaleExponent 5 5 7) • (rowColumnMul HexagonRowColumn557.rows_assocCAB HexagonRowColumn557.cols_right2)) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem rightFinal5_case_5_7_row_2_1_0 : (((-1 : ℤ) ^ (rightScaleBit 5 5 7).val * positiveScale (rightScaleExponent 5 5 7) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 7 5 : ℤ)) • HexagonAtoms557.outerLeftABC) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (negativeScale (rightScaleExponent 5 5 7) • (rowColumnMul HexagonRowColumn557.rows_assocCAB HexagonRowColumn557.cols_right2)) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem rightFinal5_case_5_7_row_2_1_1 : (((-1 : ℤ) ^ (rightScaleBit 5 5 7).val * positiveScale (rightScaleExponent 5 5 7) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 7 5 : ℤ)) • HexagonAtoms557.outerLeftABC) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (negativeScale (rightScaleExponent 5 5 7) • (rowColumnMul HexagonRowColumn557.rows_assocCAB HexagonRowColumn557.cols_right2)) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem rightFinal5_case_5_7_row_3_0_0 : (((-1 : ℤ) ^ (rightScaleBit 5 5 7).val * positiveScale (rightScaleExponent 5 5 7) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 7 5 : ℤ)) • HexagonAtoms557.outerLeftABC) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (negativeScale (rightScaleExponent 5 5 7) • (rowColumnMul HexagonRowColumn557.rows_assocCAB HexagonRowColumn557.cols_right2)) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem rightFinal5_case_5_7_row_3_0_1 : (((-1 : ℤ) ^ (rightScaleBit 5 5 7).val * positiveScale (rightScaleExponent 5 5 7) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 7 5 : ℤ)) • HexagonAtoms557.outerLeftABC) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (negativeScale (rightScaleExponent 5 5 7) • (rowColumnMul HexagonRowColumn557.rows_assocCAB HexagonRowColumn557.cols_right2)) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem rightFinal5_case_5_7_row_3_1_0 : (((-1 : ℤ) ^ (rightScaleBit 5 5 7).val * positiveScale (rightScaleExponent 5 5 7) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 7 5 : ℤ)) • HexagonAtoms557.outerLeftABC) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (negativeScale (rightScaleExponent 5 5 7) • (rowColumnMul HexagonRowColumn557.rows_assocCAB HexagonRowColumn557.cols_right2)) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem rightFinal5_case_5_7_row_3_1_1 : (((-1 : ℤ) ^ (rightScaleBit 5 5 7).val * positiveScale (rightScaleExponent 5 5 7) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 7 5 : ℤ)) • HexagonAtoms557.outerLeftABC) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (negativeScale (rightScaleExponent 5 5 7) • (rowColumnMul HexagonRowColumn557.rows_assocCAB HexagonRowColumn557.cols_right2)) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem rightFinal5_case_5_7_checked : ((-1 : ℤ) ^ (rightScaleBit 5 5 7).val * positiveScale (rightScaleExponent 5 5 7) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 7 5 : ℤ)) • HexagonAtoms557.outerLeftABC = negativeScale (rightScaleExponent 5 5 7) • (rowColumnMul HexagonRowColumn557.rows_assocCAB HexagonRowColumn557.cols_right2) := by
  funext r
  fin_cases r
  · exact rightFinal5_case_5_7_row_0_0_0
  · exact rightFinal5_case_5_7_row_0_0_1
  · exact rightFinal5_case_5_7_row_0_1_0
  · exact rightFinal5_case_5_7_row_0_1_1
  · exact rightFinal5_case_5_7_row_1_0_0
  · exact rightFinal5_case_5_7_row_1_0_1
  · exact rightFinal5_case_5_7_row_1_1_0
  · exact rightFinal5_case_5_7_row_1_1_1
  · exact rightFinal5_case_5_7_row_2_0_0
  · exact rightFinal5_case_5_7_row_2_0_1
  · exact rightFinal5_case_5_7_row_2_1_0
  · exact rightFinal5_case_5_7_row_2_1_1
  · exact rightFinal5_case_5_7_row_3_0_0
  · exact rightFinal5_case_5_7_row_3_0_1
  · exact rightFinal5_case_5_7_row_3_1_0
  · exact rightFinal5_case_5_7_row_3_1_1

set_option backward.isDefEq.respectTransparency false in
theorem rightFinal5_case_5_7 : ((-1 : ℤ) ^ (rightScaleBit 5 5 7).val * positiveScale (rightScaleExponent 5 5 7) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 7 5 : ℤ)) • outerLeftZ 5 5 7 = negativeScale (rightScaleExponent 5 5 7) • (associatorZ 7 5 5 * right2Middle5 5 7) := by
  simpa only [HexagonAtoms557.assocABC_eq,
    HexagonAtoms557.outerABC_eq,
    HexagonAtoms557.assocBAC_eq,
    HexagonAtoms557.innerABC_eq,
    HexagonAtoms557.innerRightABC_eq,
    HexagonAtoms557.inverseACB_eq,
    HexagonAtoms557.innerACB_eq,
    HexagonAtoms557.assocBCA_eq,
    HexagonAtoms557.innerRightBAC_eq,
    HexagonAtoms557.assocCAB_eq,
    HexagonAtoms557.outerLeftABC_eq,
    HexagonRowColumn557.assocBAC_alias,
    HexagonRowColumn557.innerRightBAC_alias,
    HexagonRowColumn557.product0_eq,
    HexagonRowColumn557.product1_eq,
    HexagonRowColumn557.product2_eq,
    HexagonRowColumn557.product3_eq,
    HexagonRowColumn557.product4_eq,
    HexagonRowColumn557.product5_eq,
    HexagonRowColumn557.product6_eq,
    HexagonRowColumn557.product7_eq] using rightFinal5_case_5_7_checked

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonCases5
