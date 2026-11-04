import RMod.BrundanEllis.StackingReferenceHexagonMiddle3
import RMod.BrundanEllis.StackingReferenceSparseMatrixCheck
import RMod.BrundanEllis.StackingReferenceHexagonAtoms347
import RMod.BrundanEllis.StackingReferenceHexagonRowColumn347

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

private theorem left0Middle3_eq_case_4_7_row_0_0_0 : (left0Middle3 4 7) ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn347.rows_outerABC HexagonRowColumn347.cols_assocABC) ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_4_7_row_0_0_1 : (left0Middle3 4 7) ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn347.rows_outerABC HexagonRowColumn347.cols_assocABC) ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_4_7_row_0_0_2 : (left0Middle3 4 7) ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn347.rows_outerABC HexagonRowColumn347.cols_assocABC) ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_4_7_row_0_0_3 : (left0Middle3 4 7) ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn347.rows_outerABC HexagonRowColumn347.cols_assocABC) ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_4_7_row_0_1_0 : (left0Middle3 4 7) ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn347.rows_outerABC HexagonRowColumn347.cols_assocABC) ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_4_7_row_0_1_1 : (left0Middle3 4 7) ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn347.rows_outerABC HexagonRowColumn347.cols_assocABC) ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_4_7_row_0_1_2 : (left0Middle3 4 7) ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn347.rows_outerABC HexagonRowColumn347.cols_assocABC) ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_4_7_row_0_1_3 : (left0Middle3 4 7) ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn347.rows_outerABC HexagonRowColumn347.cols_assocABC) ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_4_7_row_0_2_0 : (left0Middle3 4 7) ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn347.rows_outerABC HexagonRowColumn347.cols_assocABC) ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_4_7_row_0_2_1 : (left0Middle3 4 7) ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn347.rows_outerABC HexagonRowColumn347.cols_assocABC) ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_4_7_row_0_2_2 : (left0Middle3 4 7) ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn347.rows_outerABC HexagonRowColumn347.cols_assocABC) ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_4_7_row_0_2_3 : (left0Middle3 4 7) ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn347.rows_outerABC HexagonRowColumn347.cols_assocABC) ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_4_7_row_0_3_0 : (left0Middle3 4 7) ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn347.rows_outerABC HexagonRowColumn347.cols_assocABC) ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_4_7_row_0_3_1 : (left0Middle3 4 7) ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn347.rows_outerABC HexagonRowColumn347.cols_assocABC) ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_4_7_row_0_3_2 : (left0Middle3 4 7) ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn347.rows_outerABC HexagonRowColumn347.cols_assocABC) ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_4_7_row_0_3_3 : (left0Middle3 4 7) ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn347.rows_outerABC HexagonRowColumn347.cols_assocABC) ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_4_7_checked : left0Middle3 4 7 = rowColumnMul HexagonRowColumn347.rows_outerABC HexagonRowColumn347.cols_assocABC := by
  funext r
  fin_cases r
  · exact left0Middle3_eq_case_4_7_row_0_0_0
  · exact left0Middle3_eq_case_4_7_row_0_0_1
  · exact left0Middle3_eq_case_4_7_row_0_0_2
  · exact left0Middle3_eq_case_4_7_row_0_0_3
  · exact left0Middle3_eq_case_4_7_row_0_1_0
  · exact left0Middle3_eq_case_4_7_row_0_1_1
  · exact left0Middle3_eq_case_4_7_row_0_1_2
  · exact left0Middle3_eq_case_4_7_row_0_1_3
  · exact left0Middle3_eq_case_4_7_row_0_2_0
  · exact left0Middle3_eq_case_4_7_row_0_2_1
  · exact left0Middle3_eq_case_4_7_row_0_2_2
  · exact left0Middle3_eq_case_4_7_row_0_2_3
  · exact left0Middle3_eq_case_4_7_row_0_3_0
  · exact left0Middle3_eq_case_4_7_row_0_3_1
  · exact left0Middle3_eq_case_4_7_row_0_3_2
  · exact left0Middle3_eq_case_4_7_row_0_3_3

set_option backward.isDefEq.respectTransparency false in
theorem left0Middle3_eq_case_4_7 : left0Middle3 4 7 = outerRightZ 3 4 7 * associatorZ 3 4 7 := by
  simpa only [HexagonAtoms347.assocABC_eq,
    HexagonAtoms347.outerABC_eq,
    HexagonAtoms347.assocBAC_eq,
    HexagonAtoms347.innerABC_eq,
    HexagonAtoms347.innerRightABC_eq,
    HexagonAtoms347.inverseACB_eq,
    HexagonAtoms347.innerACB_eq,
    HexagonAtoms347.assocBCA_eq,
    HexagonAtoms347.innerRightBAC_eq,
    HexagonAtoms347.assocCAB_eq,
    HexagonAtoms347.outerLeftABC_eq,
    HexagonRowColumn347.product0_eq,
    HexagonRowColumn347.product1_eq,
    HexagonRowColumn347.product2_eq,
    HexagonRowColumn347.product3_eq,
    HexagonRowColumn347.product4_eq,
    HexagonRowColumn347.product5_eq,
    HexagonRowColumn347.product6_eq,
    HexagonRowColumn347.product7_eq] using left0Middle3_eq_case_4_7_checked

private theorem left1Middle3_eq_case_4_7_row_0_0_0 : (left1Middle3 4 7) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms347.assocBAC) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_4_7_row_0_0_1 : (left1Middle3 4 7) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms347.assocBAC) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_4_7_row_0_0_2 : (left1Middle3 4 7) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms347.assocBAC) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_4_7_row_0_0_3 : (left1Middle3 4 7) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms347.assocBAC) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_4_7_row_0_1_0 : (left1Middle3 4 7) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms347.assocBAC) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_4_7_row_0_1_1 : (left1Middle3 4 7) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms347.assocBAC) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_4_7_row_0_1_2 : (left1Middle3 4 7) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms347.assocBAC) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_4_7_row_0_1_3 : (left1Middle3 4 7) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms347.assocBAC) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_4_7_row_1_0_0 : (left1Middle3 4 7) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms347.assocBAC) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_4_7_row_1_0_1 : (left1Middle3 4 7) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms347.assocBAC) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_4_7_row_1_0_2 : (left1Middle3 4 7) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms347.assocBAC) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_4_7_row_1_0_3 : (left1Middle3 4 7) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms347.assocBAC) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_4_7_row_1_1_0 : (left1Middle3 4 7) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms347.assocBAC) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_4_7_row_1_1_1 : (left1Middle3 4 7) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms347.assocBAC) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_4_7_row_1_1_2 : (left1Middle3 4 7) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms347.assocBAC) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_4_7_row_1_1_3 : (left1Middle3 4 7) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms347.assocBAC) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_4_7_checked : left1Middle3 4 7 = HexagonAtoms347.assocBAC := by
  funext r
  fin_cases r
  · exact left1Middle3_eq_case_4_7_row_0_0_0
  · exact left1Middle3_eq_case_4_7_row_0_0_1
  · exact left1Middle3_eq_case_4_7_row_0_0_2
  · exact left1Middle3_eq_case_4_7_row_0_0_3
  · exact left1Middle3_eq_case_4_7_row_0_1_0
  · exact left1Middle3_eq_case_4_7_row_0_1_1
  · exact left1Middle3_eq_case_4_7_row_0_1_2
  · exact left1Middle3_eq_case_4_7_row_0_1_3
  · exact left1Middle3_eq_case_4_7_row_1_0_0
  · exact left1Middle3_eq_case_4_7_row_1_0_1
  · exact left1Middle3_eq_case_4_7_row_1_0_2
  · exact left1Middle3_eq_case_4_7_row_1_0_3
  · exact left1Middle3_eq_case_4_7_row_1_1_0
  · exact left1Middle3_eq_case_4_7_row_1_1_1
  · exact left1Middle3_eq_case_4_7_row_1_1_2
  · exact left1Middle3_eq_case_4_7_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem left1Middle3_eq_case_4_7 : left1Middle3 4 7 = associatorZ 4 3 7 * innerLeftZ 3 4 7 := by
  simpa only [HexagonAtoms347.assocABC_eq,
    HexagonAtoms347.outerABC_eq,
    HexagonAtoms347.assocBAC_eq,
    HexagonAtoms347.innerABC_eq,
    HexagonAtoms347.innerRightABC_eq,
    HexagonAtoms347.inverseACB_eq,
    HexagonAtoms347.innerACB_eq,
    HexagonAtoms347.assocBCA_eq,
    HexagonAtoms347.innerRightBAC_eq,
    HexagonAtoms347.assocCAB_eq,
    HexagonAtoms347.outerLeftABC_eq,
    HexagonRowColumn347.product0_eq,
    HexagonRowColumn347.product1_eq,
    HexagonRowColumn347.product2_eq,
    HexagonRowColumn347.product3_eq,
    HexagonRowColumn347.product4_eq,
    HexagonRowColumn347.product5_eq,
    HexagonRowColumn347.product6_eq,
    HexagonRowColumn347.product7_eq] using left1Middle3_eq_case_4_7_checked

private theorem right0Middle3_eq_case_4_7_row_0_0_0 : (right0Middle3 4 7) ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4)) = (HexagonAtoms347.assocABC) ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_4_7_row_0_0_1 : (right0Middle3 4 7) ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4)) = (HexagonAtoms347.assocABC) ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_4_7_row_0_0_2 : (right0Middle3 4 7) ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4)) = (HexagonAtoms347.assocABC) ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_4_7_row_0_0_3 : (right0Middle3 4 7) ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4)) = (HexagonAtoms347.assocABC) ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_4_7_row_0_1_0 : (right0Middle3 4 7) ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4)) = (HexagonAtoms347.assocABC) ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_4_7_row_0_1_1 : (right0Middle3 4 7) ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4)) = (HexagonAtoms347.assocABC) ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_4_7_row_0_1_2 : (right0Middle3 4 7) ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4)) = (HexagonAtoms347.assocABC) ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_4_7_row_0_1_3 : (right0Middle3 4 7) ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4)) = (HexagonAtoms347.assocABC) ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_4_7_row_0_2_0 : (right0Middle3 4 7) ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4)) = (HexagonAtoms347.assocABC) ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_4_7_row_0_2_1 : (right0Middle3 4 7) ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4)) = (HexagonAtoms347.assocABC) ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_4_7_row_0_2_2 : (right0Middle3 4 7) ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4)) = (HexagonAtoms347.assocABC) ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_4_7_row_0_2_3 : (right0Middle3 4 7) ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4)) = (HexagonAtoms347.assocABC) ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_4_7_row_0_3_0 : (right0Middle3 4 7) ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4)) = (HexagonAtoms347.assocABC) ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_4_7_row_0_3_1 : (right0Middle3 4 7) ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4)) = (HexagonAtoms347.assocABC) ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_4_7_row_0_3_2 : (right0Middle3 4 7) ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4)) = (HexagonAtoms347.assocABC) ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_4_7_row_0_3_3 : (right0Middle3 4 7) ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4)) = (HexagonAtoms347.assocABC) ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_4_7_checked : right0Middle3 4 7 = HexagonAtoms347.assocABC := by
  funext r
  fin_cases r
  · exact right0Middle3_eq_case_4_7_row_0_0_0
  · exact right0Middle3_eq_case_4_7_row_0_0_1
  · exact right0Middle3_eq_case_4_7_row_0_0_2
  · exact right0Middle3_eq_case_4_7_row_0_0_3
  · exact right0Middle3_eq_case_4_7_row_0_1_0
  · exact right0Middle3_eq_case_4_7_row_0_1_1
  · exact right0Middle3_eq_case_4_7_row_0_1_2
  · exact right0Middle3_eq_case_4_7_row_0_1_3
  · exact right0Middle3_eq_case_4_7_row_0_2_0
  · exact right0Middle3_eq_case_4_7_row_0_2_1
  · exact right0Middle3_eq_case_4_7_row_0_2_2
  · exact right0Middle3_eq_case_4_7_row_0_2_3
  · exact right0Middle3_eq_case_4_7_row_0_3_0
  · exact right0Middle3_eq_case_4_7_row_0_3_1
  · exact right0Middle3_eq_case_4_7_row_0_3_2
  · exact right0Middle3_eq_case_4_7_row_0_3_3

set_option backward.isDefEq.respectTransparency false in
theorem right0Middle3_eq_case_4_7 : right0Middle3 4 7 = innerRightZ 3 4 7 * associatorZ 3 4 7 := by
  simpa only [HexagonAtoms347.assocABC_eq,
    HexagonAtoms347.outerABC_eq,
    HexagonAtoms347.assocBAC_eq,
    HexagonAtoms347.innerABC_eq,
    HexagonAtoms347.innerRightABC_eq,
    HexagonAtoms347.inverseACB_eq,
    HexagonAtoms347.innerACB_eq,
    HexagonAtoms347.assocBCA_eq,
    HexagonAtoms347.innerRightBAC_eq,
    HexagonAtoms347.assocCAB_eq,
    HexagonAtoms347.outerLeftABC_eq,
    HexagonRowColumn347.product0_eq,
    HexagonRowColumn347.product1_eq,
    HexagonRowColumn347.product2_eq,
    HexagonRowColumn347.product3_eq,
    HexagonRowColumn347.product4_eq,
    HexagonRowColumn347.product5_eq,
    HexagonRowColumn347.product6_eq,
    HexagonRowColumn347.product7_eq] using right0Middle3_eq_case_4_7_checked

private theorem right1Middle3_eq_case_4_7_row_0_0_0 : (right1Middle3 4 7) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn347.rows_inverseACB HexagonRowColumn347.cols_right0) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_4_7_row_0_0_1 : (right1Middle3 4 7) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn347.rows_inverseACB HexagonRowColumn347.cols_right0) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_4_7_row_0_0_2 : (right1Middle3 4 7) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn347.rows_inverseACB HexagonRowColumn347.cols_right0) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_4_7_row_0_0_3 : (right1Middle3 4 7) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn347.rows_inverseACB HexagonRowColumn347.cols_right0) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_4_7_row_0_1_0 : (right1Middle3 4 7) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn347.rows_inverseACB HexagonRowColumn347.cols_right0) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_4_7_row_0_1_1 : (right1Middle3 4 7) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn347.rows_inverseACB HexagonRowColumn347.cols_right0) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_4_7_row_0_1_2 : (right1Middle3 4 7) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn347.rows_inverseACB HexagonRowColumn347.cols_right0) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_4_7_row_0_1_3 : (right1Middle3 4 7) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn347.rows_inverseACB HexagonRowColumn347.cols_right0) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_4_7_row_1_0_0 : (right1Middle3 4 7) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn347.rows_inverseACB HexagonRowColumn347.cols_right0) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_4_7_row_1_0_1 : (right1Middle3 4 7) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn347.rows_inverseACB HexagonRowColumn347.cols_right0) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_4_7_row_1_0_2 : (right1Middle3 4 7) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn347.rows_inverseACB HexagonRowColumn347.cols_right0) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_4_7_row_1_0_3 : (right1Middle3 4 7) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn347.rows_inverseACB HexagonRowColumn347.cols_right0) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_4_7_row_1_1_0 : (right1Middle3 4 7) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn347.rows_inverseACB HexagonRowColumn347.cols_right0) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_4_7_row_1_1_1 : (right1Middle3 4 7) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn347.rows_inverseACB HexagonRowColumn347.cols_right0) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_4_7_row_1_1_2 : (right1Middle3 4 7) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn347.rows_inverseACB HexagonRowColumn347.cols_right0) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_4_7_row_1_1_3 : (right1Middle3 4 7) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn347.rows_inverseACB HexagonRowColumn347.cols_right0) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_4_7_checked : right1Middle3 4 7 = rowColumnMul HexagonRowColumn347.rows_inverseACB HexagonRowColumn347.cols_right0 := by
  funext r
  fin_cases r
  · exact right1Middle3_eq_case_4_7_row_0_0_0
  · exact right1Middle3_eq_case_4_7_row_0_0_1
  · exact right1Middle3_eq_case_4_7_row_0_0_2
  · exact right1Middle3_eq_case_4_7_row_0_0_3
  · exact right1Middle3_eq_case_4_7_row_0_1_0
  · exact right1Middle3_eq_case_4_7_row_0_1_1
  · exact right1Middle3_eq_case_4_7_row_0_1_2
  · exact right1Middle3_eq_case_4_7_row_0_1_3
  · exact right1Middle3_eq_case_4_7_row_1_0_0
  · exact right1Middle3_eq_case_4_7_row_1_0_1
  · exact right1Middle3_eq_case_4_7_row_1_0_2
  · exact right1Middle3_eq_case_4_7_row_1_0_3
  · exact right1Middle3_eq_case_4_7_row_1_1_0
  · exact right1Middle3_eq_case_4_7_row_1_1_1
  · exact right1Middle3_eq_case_4_7_row_1_1_2
  · exact right1Middle3_eq_case_4_7_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem right1Middle3_eq_case_4_7 : right1Middle3 4 7 = associatorInverseZ 3 7 4 * right0Middle3 4 7 := by
  simpa only [HexagonAtoms347.assocABC_eq,
    HexagonAtoms347.outerABC_eq,
    HexagonAtoms347.assocBAC_eq,
    HexagonAtoms347.innerABC_eq,
    HexagonAtoms347.innerRightABC_eq,
    HexagonAtoms347.inverseACB_eq,
    HexagonAtoms347.innerACB_eq,
    HexagonAtoms347.assocBCA_eq,
    HexagonAtoms347.innerRightBAC_eq,
    HexagonAtoms347.assocCAB_eq,
    HexagonAtoms347.outerLeftABC_eq,
    HexagonRowColumn347.product0_eq,
    HexagonRowColumn347.product1_eq,
    HexagonRowColumn347.product2_eq,
    HexagonRowColumn347.product3_eq,
    HexagonRowColumn347.product4_eq,
    HexagonRowColumn347.product5_eq,
    HexagonRowColumn347.product6_eq,
    HexagonRowColumn347.product7_eq] using right1Middle3_eq_case_4_7_checked

private theorem right2Middle3_eq_case_4_7_row_0_0_0 : (right2Middle3 4 7) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (right1Middle3 4 7) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_4_7_row_0_0_1 : (right2Middle3 4 7) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (right1Middle3 4 7) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_4_7_row_0_0_2 : (right2Middle3 4 7) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (right1Middle3 4 7) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_4_7_row_0_0_3 : (right2Middle3 4 7) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (right1Middle3 4 7) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_4_7_row_0_1_0 : (right2Middle3 4 7) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (right1Middle3 4 7) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_4_7_row_0_1_1 : (right2Middle3 4 7) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (right1Middle3 4 7) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_4_7_row_0_1_2 : (right2Middle3 4 7) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (right1Middle3 4 7) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_4_7_row_0_1_3 : (right2Middle3 4 7) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (right1Middle3 4 7) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_4_7_row_1_0_0 : (right2Middle3 4 7) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (right1Middle3 4 7) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_4_7_row_1_0_1 : (right2Middle3 4 7) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (right1Middle3 4 7) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_4_7_row_1_0_2 : (right2Middle3 4 7) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (right1Middle3 4 7) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_4_7_row_1_0_3 : (right2Middle3 4 7) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (right1Middle3 4 7) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_4_7_row_1_1_0 : (right2Middle3 4 7) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (right1Middle3 4 7) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_4_7_row_1_1_1 : (right2Middle3 4 7) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (right1Middle3 4 7) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_4_7_row_1_1_2 : (right2Middle3 4 7) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (right1Middle3 4 7) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_4_7_row_1_1_3 : (right2Middle3 4 7) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (right1Middle3 4 7) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_4_7_checked : right2Middle3 4 7 = right1Middle3 4 7 := by
  funext r
  fin_cases r
  · exact right2Middle3_eq_case_4_7_row_0_0_0
  · exact right2Middle3_eq_case_4_7_row_0_0_1
  · exact right2Middle3_eq_case_4_7_row_0_0_2
  · exact right2Middle3_eq_case_4_7_row_0_0_3
  · exact right2Middle3_eq_case_4_7_row_0_1_0
  · exact right2Middle3_eq_case_4_7_row_0_1_1
  · exact right2Middle3_eq_case_4_7_row_0_1_2
  · exact right2Middle3_eq_case_4_7_row_0_1_3
  · exact right2Middle3_eq_case_4_7_row_1_0_0
  · exact right2Middle3_eq_case_4_7_row_1_0_1
  · exact right2Middle3_eq_case_4_7_row_1_0_2
  · exact right2Middle3_eq_case_4_7_row_1_0_3
  · exact right2Middle3_eq_case_4_7_row_1_1_0
  · exact right2Middle3_eq_case_4_7_row_1_1_1
  · exact right2Middle3_eq_case_4_7_row_1_1_2
  · exact right2Middle3_eq_case_4_7_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem right2Middle3_eq_case_4_7 : right2Middle3 4 7 = innerLeftZ 3 7 4 * right1Middle3 4 7 := by
  simpa only [HexagonAtoms347.assocABC_eq,
    HexagonAtoms347.outerABC_eq,
    HexagonAtoms347.assocBAC_eq,
    HexagonAtoms347.innerABC_eq,
    HexagonAtoms347.innerRightABC_eq,
    HexagonAtoms347.inverseACB_eq,
    HexagonAtoms347.innerACB_eq,
    HexagonAtoms347.assocBCA_eq,
    HexagonAtoms347.innerRightBAC_eq,
    HexagonAtoms347.assocCAB_eq,
    HexagonAtoms347.outerLeftABC_eq,
    HexagonRowColumn347.product0_eq,
    HexagonRowColumn347.product1_eq,
    HexagonRowColumn347.product2_eq,
    HexagonRowColumn347.product3_eq,
    HexagonRowColumn347.product4_eq,
    HexagonRowColumn347.product5_eq,
    HexagonRowColumn347.product6_eq,
    HexagonRowColumn347.product7_eq] using right2Middle3_eq_case_4_7_checked

private theorem leftFinal3_case_4_7_row_0_0_0 : (((-1 : ℤ) ^ (leftScaleBit 3 4 7).val * positiveScale (leftScaleExponent 3 4 7)) •
      (rowColumnMul HexagonRowColumn347.rows_assocBCA HexagonRowColumn347.cols_left0)) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 3 4 7) • (left1Middle3 4 7)) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal3_case_4_7_row_0_0_1 : (((-1 : ℤ) ^ (leftScaleBit 3 4 7).val * positiveScale (leftScaleExponent 3 4 7)) •
      (rowColumnMul HexagonRowColumn347.rows_assocBCA HexagonRowColumn347.cols_left0)) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 3 4 7) • (left1Middle3 4 7)) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal3_case_4_7_row_0_0_2 : (((-1 : ℤ) ^ (leftScaleBit 3 4 7).val * positiveScale (leftScaleExponent 3 4 7)) •
      (rowColumnMul HexagonRowColumn347.rows_assocBCA HexagonRowColumn347.cols_left0)) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 3 4 7) • (left1Middle3 4 7)) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal3_case_4_7_row_0_0_3 : (((-1 : ℤ) ^ (leftScaleBit 3 4 7).val * positiveScale (leftScaleExponent 3 4 7)) •
      (rowColumnMul HexagonRowColumn347.rows_assocBCA HexagonRowColumn347.cols_left0)) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 3 4 7) • (left1Middle3 4 7)) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal3_case_4_7_row_0_1_0 : (((-1 : ℤ) ^ (leftScaleBit 3 4 7).val * positiveScale (leftScaleExponent 3 4 7)) •
      (rowColumnMul HexagonRowColumn347.rows_assocBCA HexagonRowColumn347.cols_left0)) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 3 4 7) • (left1Middle3 4 7)) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal3_case_4_7_row_0_1_1 : (((-1 : ℤ) ^ (leftScaleBit 3 4 7).val * positiveScale (leftScaleExponent 3 4 7)) •
      (rowColumnMul HexagonRowColumn347.rows_assocBCA HexagonRowColumn347.cols_left0)) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 3 4 7) • (left1Middle3 4 7)) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal3_case_4_7_row_0_1_2 : (((-1 : ℤ) ^ (leftScaleBit 3 4 7).val * positiveScale (leftScaleExponent 3 4 7)) •
      (rowColumnMul HexagonRowColumn347.rows_assocBCA HexagonRowColumn347.cols_left0)) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 3 4 7) • (left1Middle3 4 7)) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal3_case_4_7_row_0_1_3 : (((-1 : ℤ) ^ (leftScaleBit 3 4 7).val * positiveScale (leftScaleExponent 3 4 7)) •
      (rowColumnMul HexagonRowColumn347.rows_assocBCA HexagonRowColumn347.cols_left0)) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 3 4 7) • (left1Middle3 4 7)) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal3_case_4_7_row_1_0_0 : (((-1 : ℤ) ^ (leftScaleBit 3 4 7).val * positiveScale (leftScaleExponent 3 4 7)) •
      (rowColumnMul HexagonRowColumn347.rows_assocBCA HexagonRowColumn347.cols_left0)) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 3 4 7) • (left1Middle3 4 7)) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal3_case_4_7_row_1_0_1 : (((-1 : ℤ) ^ (leftScaleBit 3 4 7).val * positiveScale (leftScaleExponent 3 4 7)) •
      (rowColumnMul HexagonRowColumn347.rows_assocBCA HexagonRowColumn347.cols_left0)) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 3 4 7) • (left1Middle3 4 7)) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal3_case_4_7_row_1_0_2 : (((-1 : ℤ) ^ (leftScaleBit 3 4 7).val * positiveScale (leftScaleExponent 3 4 7)) •
      (rowColumnMul HexagonRowColumn347.rows_assocBCA HexagonRowColumn347.cols_left0)) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 3 4 7) • (left1Middle3 4 7)) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal3_case_4_7_row_1_0_3 : (((-1 : ℤ) ^ (leftScaleBit 3 4 7).val * positiveScale (leftScaleExponent 3 4 7)) •
      (rowColumnMul HexagonRowColumn347.rows_assocBCA HexagonRowColumn347.cols_left0)) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 3 4 7) • (left1Middle3 4 7)) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal3_case_4_7_row_1_1_0 : (((-1 : ℤ) ^ (leftScaleBit 3 4 7).val * positiveScale (leftScaleExponent 3 4 7)) •
      (rowColumnMul HexagonRowColumn347.rows_assocBCA HexagonRowColumn347.cols_left0)) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 3 4 7) • (left1Middle3 4 7)) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal3_case_4_7_row_1_1_1 : (((-1 : ℤ) ^ (leftScaleBit 3 4 7).val * positiveScale (leftScaleExponent 3 4 7)) •
      (rowColumnMul HexagonRowColumn347.rows_assocBCA HexagonRowColumn347.cols_left0)) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 3 4 7) • (left1Middle3 4 7)) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal3_case_4_7_row_1_1_2 : (((-1 : ℤ) ^ (leftScaleBit 3 4 7).val * positiveScale (leftScaleExponent 3 4 7)) •
      (rowColumnMul HexagonRowColumn347.rows_assocBCA HexagonRowColumn347.cols_left0)) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 3 4 7) • (left1Middle3 4 7)) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal3_case_4_7_row_1_1_3 : (((-1 : ℤ) ^ (leftScaleBit 3 4 7).val * positiveScale (leftScaleExponent 3 4 7)) •
      (rowColumnMul HexagonRowColumn347.rows_assocBCA HexagonRowColumn347.cols_left0)) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 3 4 7) • (left1Middle3 4 7)) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal3_case_4_7_checked : ((-1 : ℤ) ^ (leftScaleBit 3 4 7).val * positiveScale (leftScaleExponent 3 4 7)) •
      (rowColumnMul HexagonRowColumn347.rows_assocBCA HexagonRowColumn347.cols_left0) = negativeScale (leftScaleExponent 3 4 7) • (left1Middle3 4 7) := by
  funext r
  fin_cases r
  · exact leftFinal3_case_4_7_row_0_0_0
  · exact leftFinal3_case_4_7_row_0_0_1
  · exact leftFinal3_case_4_7_row_0_0_2
  · exact leftFinal3_case_4_7_row_0_0_3
  · exact leftFinal3_case_4_7_row_0_1_0
  · exact leftFinal3_case_4_7_row_0_1_1
  · exact leftFinal3_case_4_7_row_0_1_2
  · exact leftFinal3_case_4_7_row_0_1_3
  · exact leftFinal3_case_4_7_row_1_0_0
  · exact leftFinal3_case_4_7_row_1_0_1
  · exact leftFinal3_case_4_7_row_1_0_2
  · exact leftFinal3_case_4_7_row_1_0_3
  · exact leftFinal3_case_4_7_row_1_1_0
  · exact leftFinal3_case_4_7_row_1_1_1
  · exact leftFinal3_case_4_7_row_1_1_2
  · exact leftFinal3_case_4_7_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem leftFinal3_case_4_7 : ((-1 : ℤ) ^ (leftScaleBit 3 4 7).val * positiveScale (leftScaleExponent 3 4 7)) •
      (associatorZ 4 7 3 * left0Middle3 4 7) = negativeScale (leftScaleExponent 3 4 7) • (innerRightZ 4 3 7 * left1Middle3 4 7) := by
  simpa only [HexagonAtoms347.assocABC_eq,
    HexagonAtoms347.outerABC_eq,
    HexagonAtoms347.assocBAC_eq,
    HexagonAtoms347.innerABC_eq,
    HexagonAtoms347.innerRightABC_eq,
    HexagonAtoms347.inverseACB_eq,
    HexagonAtoms347.innerACB_eq,
    HexagonAtoms347.assocBCA_eq,
    HexagonAtoms347.innerRightBAC_eq,
    HexagonAtoms347.assocCAB_eq,
    HexagonAtoms347.outerLeftABC_eq,
    HexagonRowColumn347.product0_eq,
    HexagonRowColumn347.product1_eq,
    HexagonRowColumn347.product2_eq,
    HexagonRowColumn347.product3_eq,
    HexagonRowColumn347.product4_eq,
    HexagonRowColumn347.product5_eq,
    HexagonRowColumn347.product6_eq,
    HexagonRowColumn347.product7_eq] using leftFinal3_case_4_7_checked

private theorem rightFinal3_case_4_7_row_0_0_0 : (((-1 : ℤ) ^ (rightScaleBit 3 4 7).val * positiveScale (rightScaleExponent 3 4 7) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 7 4 : ℤ)) • HexagonAtoms347.outerLeftABC) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (negativeScale (rightScaleExponent 3 4 7) • (rowColumnMul HexagonRowColumn347.rows_assocCAB HexagonRowColumn347.cols_right2)) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal3_case_4_7_row_0_0_1 : (((-1 : ℤ) ^ (rightScaleBit 3 4 7).val * positiveScale (rightScaleExponent 3 4 7) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 7 4 : ℤ)) • HexagonAtoms347.outerLeftABC) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (negativeScale (rightScaleExponent 3 4 7) • (rowColumnMul HexagonRowColumn347.rows_assocCAB HexagonRowColumn347.cols_right2)) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal3_case_4_7_row_0_0_2 : (((-1 : ℤ) ^ (rightScaleBit 3 4 7).val * positiveScale (rightScaleExponent 3 4 7) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 7 4 : ℤ)) • HexagonAtoms347.outerLeftABC) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (negativeScale (rightScaleExponent 3 4 7) • (rowColumnMul HexagonRowColumn347.rows_assocCAB HexagonRowColumn347.cols_right2)) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal3_case_4_7_row_0_0_3 : (((-1 : ℤ) ^ (rightScaleBit 3 4 7).val * positiveScale (rightScaleExponent 3 4 7) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 7 4 : ℤ)) • HexagonAtoms347.outerLeftABC) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (negativeScale (rightScaleExponent 3 4 7) • (rowColumnMul HexagonRowColumn347.rows_assocCAB HexagonRowColumn347.cols_right2)) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal3_case_4_7_row_1_0_0 : (((-1 : ℤ) ^ (rightScaleBit 3 4 7).val * positiveScale (rightScaleExponent 3 4 7) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 7 4 : ℤ)) • HexagonAtoms347.outerLeftABC) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (negativeScale (rightScaleExponent 3 4 7) • (rowColumnMul HexagonRowColumn347.rows_assocCAB HexagonRowColumn347.cols_right2)) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal3_case_4_7_row_1_0_1 : (((-1 : ℤ) ^ (rightScaleBit 3 4 7).val * positiveScale (rightScaleExponent 3 4 7) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 7 4 : ℤ)) • HexagonAtoms347.outerLeftABC) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (negativeScale (rightScaleExponent 3 4 7) • (rowColumnMul HexagonRowColumn347.rows_assocCAB HexagonRowColumn347.cols_right2)) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal3_case_4_7_row_1_0_2 : (((-1 : ℤ) ^ (rightScaleBit 3 4 7).val * positiveScale (rightScaleExponent 3 4 7) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 7 4 : ℤ)) • HexagonAtoms347.outerLeftABC) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (negativeScale (rightScaleExponent 3 4 7) • (rowColumnMul HexagonRowColumn347.rows_assocCAB HexagonRowColumn347.cols_right2)) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal3_case_4_7_row_1_0_3 : (((-1 : ℤ) ^ (rightScaleBit 3 4 7).val * positiveScale (rightScaleExponent 3 4 7) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 7 4 : ℤ)) • HexagonAtoms347.outerLeftABC) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (negativeScale (rightScaleExponent 3 4 7) • (rowColumnMul HexagonRowColumn347.rows_assocCAB HexagonRowColumn347.cols_right2)) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal3_case_4_7_row_2_0_0 : (((-1 : ℤ) ^ (rightScaleBit 3 4 7).val * positiveScale (rightScaleExponent 3 4 7) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 7 4 : ℤ)) • HexagonAtoms347.outerLeftABC) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (negativeScale (rightScaleExponent 3 4 7) • (rowColumnMul HexagonRowColumn347.rows_assocCAB HexagonRowColumn347.cols_right2)) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal3_case_4_7_row_2_0_1 : (((-1 : ℤ) ^ (rightScaleBit 3 4 7).val * positiveScale (rightScaleExponent 3 4 7) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 7 4 : ℤ)) • HexagonAtoms347.outerLeftABC) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (negativeScale (rightScaleExponent 3 4 7) • (rowColumnMul HexagonRowColumn347.rows_assocCAB HexagonRowColumn347.cols_right2)) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal3_case_4_7_row_2_0_2 : (((-1 : ℤ) ^ (rightScaleBit 3 4 7).val * positiveScale (rightScaleExponent 3 4 7) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 7 4 : ℤ)) • HexagonAtoms347.outerLeftABC) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (negativeScale (rightScaleExponent 3 4 7) • (rowColumnMul HexagonRowColumn347.rows_assocCAB HexagonRowColumn347.cols_right2)) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal3_case_4_7_row_2_0_3 : (((-1 : ℤ) ^ (rightScaleBit 3 4 7).val * positiveScale (rightScaleExponent 3 4 7) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 7 4 : ℤ)) • HexagonAtoms347.outerLeftABC) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (negativeScale (rightScaleExponent 3 4 7) • (rowColumnMul HexagonRowColumn347.rows_assocCAB HexagonRowColumn347.cols_right2)) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal3_case_4_7_row_3_0_0 : (((-1 : ℤ) ^ (rightScaleBit 3 4 7).val * positiveScale (rightScaleExponent 3 4 7) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 7 4 : ℤ)) • HexagonAtoms347.outerLeftABC) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (negativeScale (rightScaleExponent 3 4 7) • (rowColumnMul HexagonRowColumn347.rows_assocCAB HexagonRowColumn347.cols_right2)) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal3_case_4_7_row_3_0_1 : (((-1 : ℤ) ^ (rightScaleBit 3 4 7).val * positiveScale (rightScaleExponent 3 4 7) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 7 4 : ℤ)) • HexagonAtoms347.outerLeftABC) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (negativeScale (rightScaleExponent 3 4 7) • (rowColumnMul HexagonRowColumn347.rows_assocCAB HexagonRowColumn347.cols_right2)) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal3_case_4_7_row_3_0_2 : (((-1 : ℤ) ^ (rightScaleBit 3 4 7).val * positiveScale (rightScaleExponent 3 4 7) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 7 4 : ℤ)) • HexagonAtoms347.outerLeftABC) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (negativeScale (rightScaleExponent 3 4 7) • (rowColumnMul HexagonRowColumn347.rows_assocCAB HexagonRowColumn347.cols_right2)) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal3_case_4_7_row_3_0_3 : (((-1 : ℤ) ^ (rightScaleBit 3 4 7).val * positiveScale (rightScaleExponent 3 4 7) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 7 4 : ℤ)) • HexagonAtoms347.outerLeftABC) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (negativeScale (rightScaleExponent 3 4 7) • (rowColumnMul HexagonRowColumn347.rows_assocCAB HexagonRowColumn347.cols_right2)) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal3_case_4_7_checked : ((-1 : ℤ) ^ (rightScaleBit 3 4 7).val * positiveScale (rightScaleExponent 3 4 7) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 7 4 : ℤ)) • HexagonAtoms347.outerLeftABC = negativeScale (rightScaleExponent 3 4 7) • (rowColumnMul HexagonRowColumn347.rows_assocCAB HexagonRowColumn347.cols_right2) := by
  funext r
  fin_cases r
  · exact rightFinal3_case_4_7_row_0_0_0
  · exact rightFinal3_case_4_7_row_0_0_1
  · exact rightFinal3_case_4_7_row_0_0_2
  · exact rightFinal3_case_4_7_row_0_0_3
  · exact rightFinal3_case_4_7_row_1_0_0
  · exact rightFinal3_case_4_7_row_1_0_1
  · exact rightFinal3_case_4_7_row_1_0_2
  · exact rightFinal3_case_4_7_row_1_0_3
  · exact rightFinal3_case_4_7_row_2_0_0
  · exact rightFinal3_case_4_7_row_2_0_1
  · exact rightFinal3_case_4_7_row_2_0_2
  · exact rightFinal3_case_4_7_row_2_0_3
  · exact rightFinal3_case_4_7_row_3_0_0
  · exact rightFinal3_case_4_7_row_3_0_1
  · exact rightFinal3_case_4_7_row_3_0_2
  · exact rightFinal3_case_4_7_row_3_0_3

set_option backward.isDefEq.respectTransparency false in
theorem rightFinal3_case_4_7 : ((-1 : ℤ) ^ (rightScaleBit 3 4 7).val * positiveScale (rightScaleExponent 3 4 7) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 7 4 : ℤ)) • outerLeftZ 3 4 7 = negativeScale (rightScaleExponent 3 4 7) • (associatorZ 7 3 4 * right2Middle3 4 7) := by
  simpa only [HexagonAtoms347.assocABC_eq,
    HexagonAtoms347.outerABC_eq,
    HexagonAtoms347.assocBAC_eq,
    HexagonAtoms347.innerABC_eq,
    HexagonAtoms347.innerRightABC_eq,
    HexagonAtoms347.inverseACB_eq,
    HexagonAtoms347.innerACB_eq,
    HexagonAtoms347.assocBCA_eq,
    HexagonAtoms347.innerRightBAC_eq,
    HexagonAtoms347.assocCAB_eq,
    HexagonAtoms347.outerLeftABC_eq,
    HexagonRowColumn347.product0_eq,
    HexagonRowColumn347.product1_eq,
    HexagonRowColumn347.product2_eq,
    HexagonRowColumn347.product3_eq,
    HexagonRowColumn347.product4_eq,
    HexagonRowColumn347.product5_eq,
    HexagonRowColumn347.product6_eq,
    HexagonRowColumn347.product7_eq] using rightFinal3_case_4_7_checked

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonCases3
