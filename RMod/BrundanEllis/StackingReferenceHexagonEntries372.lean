import RMod.BrundanEllis.StackingReferenceHexagonMiddle3
import RMod.BrundanEllis.StackingReferenceSparseMatrixCheck
import RMod.BrundanEllis.StackingReferenceHexagonAtoms372
import RMod.BrundanEllis.StackingReferenceHexagonRowColumn372

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

private theorem left0Middle3_eq_case_7_2_row_0_0_0 : (left0Middle3 7 2) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn372.rows_outerABC HexagonRowColumn372.cols_assocABC) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_7_2_row_0_0_1 : (left0Middle3 7 2) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn372.rows_outerABC HexagonRowColumn372.cols_assocABC) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_7_2_row_0_0_2 : (left0Middle3 7 2) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn372.rows_outerABC HexagonRowColumn372.cols_assocABC) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_7_2_row_0_0_3 : (left0Middle3 7 2) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn372.rows_outerABC HexagonRowColumn372.cols_assocABC) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_7_2_row_0_1_0 : (left0Middle3 7 2) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn372.rows_outerABC HexagonRowColumn372.cols_assocABC) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_7_2_row_0_1_1 : (left0Middle3 7 2) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn372.rows_outerABC HexagonRowColumn372.cols_assocABC) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_7_2_row_0_1_2 : (left0Middle3 7 2) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn372.rows_outerABC HexagonRowColumn372.cols_assocABC) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_7_2_row_0_1_3 : (left0Middle3 7 2) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn372.rows_outerABC HexagonRowColumn372.cols_assocABC) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_7_2_row_1_0_0 : (left0Middle3 7 2) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn372.rows_outerABC HexagonRowColumn372.cols_assocABC) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_7_2_row_1_0_1 : (left0Middle3 7 2) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn372.rows_outerABC HexagonRowColumn372.cols_assocABC) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_7_2_row_1_0_2 : (left0Middle3 7 2) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn372.rows_outerABC HexagonRowColumn372.cols_assocABC) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_7_2_row_1_0_3 : (left0Middle3 7 2) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn372.rows_outerABC HexagonRowColumn372.cols_assocABC) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_7_2_row_1_1_0 : (left0Middle3 7 2) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn372.rows_outerABC HexagonRowColumn372.cols_assocABC) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_7_2_row_1_1_1 : (left0Middle3 7 2) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn372.rows_outerABC HexagonRowColumn372.cols_assocABC) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_7_2_row_1_1_2 : (left0Middle3 7 2) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn372.rows_outerABC HexagonRowColumn372.cols_assocABC) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_7_2_row_1_1_3 : (left0Middle3 7 2) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn372.rows_outerABC HexagonRowColumn372.cols_assocABC) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_7_2_checked : left0Middle3 7 2 = rowColumnMul HexagonRowColumn372.rows_outerABC HexagonRowColumn372.cols_assocABC := by
  funext r
  fin_cases r
  · exact left0Middle3_eq_case_7_2_row_0_0_0
  · exact left0Middle3_eq_case_7_2_row_0_0_1
  · exact left0Middle3_eq_case_7_2_row_0_0_2
  · exact left0Middle3_eq_case_7_2_row_0_0_3
  · exact left0Middle3_eq_case_7_2_row_0_1_0
  · exact left0Middle3_eq_case_7_2_row_0_1_1
  · exact left0Middle3_eq_case_7_2_row_0_1_2
  · exact left0Middle3_eq_case_7_2_row_0_1_3
  · exact left0Middle3_eq_case_7_2_row_1_0_0
  · exact left0Middle3_eq_case_7_2_row_1_0_1
  · exact left0Middle3_eq_case_7_2_row_1_0_2
  · exact left0Middle3_eq_case_7_2_row_1_0_3
  · exact left0Middle3_eq_case_7_2_row_1_1_0
  · exact left0Middle3_eq_case_7_2_row_1_1_1
  · exact left0Middle3_eq_case_7_2_row_1_1_2
  · exact left0Middle3_eq_case_7_2_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem left0Middle3_eq_case_7_2 : left0Middle3 7 2 = outerRightZ 3 7 2 * associatorZ 3 7 2 := by
  simpa only [HexagonAtoms372.assocABC_eq,
    HexagonAtoms372.outerABC_eq,
    HexagonAtoms372.assocBAC_eq,
    HexagonAtoms372.innerABC_eq,
    HexagonAtoms372.innerRightABC_eq,
    HexagonAtoms372.inverseACB_eq,
    HexagonAtoms372.innerACB_eq,
    HexagonAtoms372.assocBCA_eq,
    HexagonAtoms372.innerRightBAC_eq,
    HexagonAtoms372.assocCAB_eq,
    HexagonAtoms372.outerLeftABC_eq,
    HexagonRowColumn372.product0_eq,
    HexagonRowColumn372.product1_eq,
    HexagonRowColumn372.product2_eq,
    HexagonRowColumn372.product3_eq,
    HexagonRowColumn372.product4_eq,
    HexagonRowColumn372.product5_eq,
    HexagonRowColumn372.product6_eq,
    HexagonRowColumn372.product7_eq] using left0Middle3_eq_case_7_2_checked

private theorem left1Middle3_eq_case_7_2_row_0_0_0 : (left1Middle3 7 2) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms372.assocBAC) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_7_2_row_0_0_1 : (left1Middle3 7 2) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms372.assocBAC) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_7_2_row_0_0_2 : (left1Middle3 7 2) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms372.assocBAC) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_7_2_row_0_0_3 : (left1Middle3 7 2) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms372.assocBAC) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_7_2_row_0_1_0 : (left1Middle3 7 2) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms372.assocBAC) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_7_2_row_0_1_1 : (left1Middle3 7 2) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms372.assocBAC) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_7_2_row_0_1_2 : (left1Middle3 7 2) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms372.assocBAC) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_7_2_row_0_1_3 : (left1Middle3 7 2) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms372.assocBAC) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_7_2_row_1_0_0 : (left1Middle3 7 2) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms372.assocBAC) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_7_2_row_1_0_1 : (left1Middle3 7 2) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms372.assocBAC) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_7_2_row_1_0_2 : (left1Middle3 7 2) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms372.assocBAC) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_7_2_row_1_0_3 : (left1Middle3 7 2) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms372.assocBAC) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_7_2_row_1_1_0 : (left1Middle3 7 2) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms372.assocBAC) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_7_2_row_1_1_1 : (left1Middle3 7 2) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms372.assocBAC) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_7_2_row_1_1_2 : (left1Middle3 7 2) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms372.assocBAC) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_7_2_row_1_1_3 : (left1Middle3 7 2) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms372.assocBAC) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_7_2_checked : left1Middle3 7 2 = HexagonAtoms372.assocBAC := by
  funext r
  fin_cases r
  · exact left1Middle3_eq_case_7_2_row_0_0_0
  · exact left1Middle3_eq_case_7_2_row_0_0_1
  · exact left1Middle3_eq_case_7_2_row_0_0_2
  · exact left1Middle3_eq_case_7_2_row_0_0_3
  · exact left1Middle3_eq_case_7_2_row_0_1_0
  · exact left1Middle3_eq_case_7_2_row_0_1_1
  · exact left1Middle3_eq_case_7_2_row_0_1_2
  · exact left1Middle3_eq_case_7_2_row_0_1_3
  · exact left1Middle3_eq_case_7_2_row_1_0_0
  · exact left1Middle3_eq_case_7_2_row_1_0_1
  · exact left1Middle3_eq_case_7_2_row_1_0_2
  · exact left1Middle3_eq_case_7_2_row_1_0_3
  · exact left1Middle3_eq_case_7_2_row_1_1_0
  · exact left1Middle3_eq_case_7_2_row_1_1_1
  · exact left1Middle3_eq_case_7_2_row_1_1_2
  · exact left1Middle3_eq_case_7_2_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem left1Middle3_eq_case_7_2 : left1Middle3 7 2 = associatorZ 7 3 2 * innerLeftZ 3 7 2 := by
  simpa only [HexagonAtoms372.assocABC_eq,
    HexagonAtoms372.outerABC_eq,
    HexagonAtoms372.assocBAC_eq,
    HexagonAtoms372.innerABC_eq,
    HexagonAtoms372.innerRightABC_eq,
    HexagonAtoms372.inverseACB_eq,
    HexagonAtoms372.innerACB_eq,
    HexagonAtoms372.assocBCA_eq,
    HexagonAtoms372.innerRightBAC_eq,
    HexagonAtoms372.assocCAB_eq,
    HexagonAtoms372.outerLeftABC_eq,
    HexagonRowColumn372.product0_eq,
    HexagonRowColumn372.product1_eq,
    HexagonRowColumn372.product2_eq,
    HexagonRowColumn372.product3_eq,
    HexagonRowColumn372.product4_eq,
    HexagonRowColumn372.product5_eq,
    HexagonRowColumn372.product6_eq,
    HexagonRowColumn372.product7_eq] using left1Middle3_eq_case_7_2_checked

private theorem right0Middle3_eq_case_7_2_row_0_0_0 : (right0Middle3 7 2) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms372.assocABC) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_7_2_row_0_0_1 : (right0Middle3 7 2) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms372.assocABC) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_7_2_row_0_0_2 : (right0Middle3 7 2) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms372.assocABC) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_7_2_row_0_0_3 : (right0Middle3 7 2) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms372.assocABC) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_7_2_row_0_1_0 : (right0Middle3 7 2) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms372.assocABC) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_7_2_row_0_1_1 : (right0Middle3 7 2) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms372.assocABC) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_7_2_row_0_1_2 : (right0Middle3 7 2) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms372.assocABC) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_7_2_row_0_1_3 : (right0Middle3 7 2) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms372.assocABC) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_7_2_row_1_0_0 : (right0Middle3 7 2) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms372.assocABC) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_7_2_row_1_0_1 : (right0Middle3 7 2) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms372.assocABC) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_7_2_row_1_0_2 : (right0Middle3 7 2) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms372.assocABC) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_7_2_row_1_0_3 : (right0Middle3 7 2) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms372.assocABC) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_7_2_row_1_1_0 : (right0Middle3 7 2) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms372.assocABC) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_7_2_row_1_1_1 : (right0Middle3 7 2) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms372.assocABC) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_7_2_row_1_1_2 : (right0Middle3 7 2) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms372.assocABC) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_7_2_row_1_1_3 : (right0Middle3 7 2) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms372.assocABC) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_7_2_checked : right0Middle3 7 2 = HexagonAtoms372.assocABC := by
  funext r
  fin_cases r
  · exact right0Middle3_eq_case_7_2_row_0_0_0
  · exact right0Middle3_eq_case_7_2_row_0_0_1
  · exact right0Middle3_eq_case_7_2_row_0_0_2
  · exact right0Middle3_eq_case_7_2_row_0_0_3
  · exact right0Middle3_eq_case_7_2_row_0_1_0
  · exact right0Middle3_eq_case_7_2_row_0_1_1
  · exact right0Middle3_eq_case_7_2_row_0_1_2
  · exact right0Middle3_eq_case_7_2_row_0_1_3
  · exact right0Middle3_eq_case_7_2_row_1_0_0
  · exact right0Middle3_eq_case_7_2_row_1_0_1
  · exact right0Middle3_eq_case_7_2_row_1_0_2
  · exact right0Middle3_eq_case_7_2_row_1_0_3
  · exact right0Middle3_eq_case_7_2_row_1_1_0
  · exact right0Middle3_eq_case_7_2_row_1_1_1
  · exact right0Middle3_eq_case_7_2_row_1_1_2
  · exact right0Middle3_eq_case_7_2_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem right0Middle3_eq_case_7_2 : right0Middle3 7 2 = innerRightZ 3 7 2 * associatorZ 3 7 2 := by
  simpa only [HexagonAtoms372.assocABC_eq,
    HexagonAtoms372.outerABC_eq,
    HexagonAtoms372.assocBAC_eq,
    HexagonAtoms372.innerABC_eq,
    HexagonAtoms372.innerRightABC_eq,
    HexagonAtoms372.inverseACB_eq,
    HexagonAtoms372.innerACB_eq,
    HexagonAtoms372.assocBCA_eq,
    HexagonAtoms372.innerRightBAC_eq,
    HexagonAtoms372.assocCAB_eq,
    HexagonAtoms372.outerLeftABC_eq,
    HexagonRowColumn372.product0_eq,
    HexagonRowColumn372.product1_eq,
    HexagonRowColumn372.product2_eq,
    HexagonRowColumn372.product3_eq,
    HexagonRowColumn372.product4_eq,
    HexagonRowColumn372.product5_eq,
    HexagonRowColumn372.product6_eq,
    HexagonRowColumn372.product7_eq] using right0Middle3_eq_case_7_2_checked

private theorem right1Middle3_eq_case_7_2_row_0_0_0 : (right1Middle3 7 2) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn372.rows_inverseACB HexagonRowColumn372.cols_right0) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_7_2_row_0_0_1 : (right1Middle3 7 2) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn372.rows_inverseACB HexagonRowColumn372.cols_right0) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_7_2_row_0_0_2 : (right1Middle3 7 2) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn372.rows_inverseACB HexagonRowColumn372.cols_right0) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_7_2_row_0_0_3 : (right1Middle3 7 2) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn372.rows_inverseACB HexagonRowColumn372.cols_right0) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_7_2_row_0_1_0 : (right1Middle3 7 2) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn372.rows_inverseACB HexagonRowColumn372.cols_right0) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_7_2_row_0_1_1 : (right1Middle3 7 2) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn372.rows_inverseACB HexagonRowColumn372.cols_right0) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_7_2_row_0_1_2 : (right1Middle3 7 2) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn372.rows_inverseACB HexagonRowColumn372.cols_right0) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_7_2_row_0_1_3 : (right1Middle3 7 2) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn372.rows_inverseACB HexagonRowColumn372.cols_right0) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_7_2_row_1_0_0 : (right1Middle3 7 2) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn372.rows_inverseACB HexagonRowColumn372.cols_right0) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_7_2_row_1_0_1 : (right1Middle3 7 2) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn372.rows_inverseACB HexagonRowColumn372.cols_right0) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_7_2_row_1_0_2 : (right1Middle3 7 2) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn372.rows_inverseACB HexagonRowColumn372.cols_right0) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_7_2_row_1_0_3 : (right1Middle3 7 2) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn372.rows_inverseACB HexagonRowColumn372.cols_right0) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_7_2_row_1_1_0 : (right1Middle3 7 2) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn372.rows_inverseACB HexagonRowColumn372.cols_right0) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_7_2_row_1_1_1 : (right1Middle3 7 2) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn372.rows_inverseACB HexagonRowColumn372.cols_right0) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_7_2_row_1_1_2 : (right1Middle3 7 2) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn372.rows_inverseACB HexagonRowColumn372.cols_right0) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_7_2_row_1_1_3 : (right1Middle3 7 2) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn372.rows_inverseACB HexagonRowColumn372.cols_right0) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_7_2_checked : right1Middle3 7 2 = rowColumnMul HexagonRowColumn372.rows_inverseACB HexagonRowColumn372.cols_right0 := by
  funext r
  fin_cases r
  · exact right1Middle3_eq_case_7_2_row_0_0_0
  · exact right1Middle3_eq_case_7_2_row_0_0_1
  · exact right1Middle3_eq_case_7_2_row_0_0_2
  · exact right1Middle3_eq_case_7_2_row_0_0_3
  · exact right1Middle3_eq_case_7_2_row_0_1_0
  · exact right1Middle3_eq_case_7_2_row_0_1_1
  · exact right1Middle3_eq_case_7_2_row_0_1_2
  · exact right1Middle3_eq_case_7_2_row_0_1_3
  · exact right1Middle3_eq_case_7_2_row_1_0_0
  · exact right1Middle3_eq_case_7_2_row_1_0_1
  · exact right1Middle3_eq_case_7_2_row_1_0_2
  · exact right1Middle3_eq_case_7_2_row_1_0_3
  · exact right1Middle3_eq_case_7_2_row_1_1_0
  · exact right1Middle3_eq_case_7_2_row_1_1_1
  · exact right1Middle3_eq_case_7_2_row_1_1_2
  · exact right1Middle3_eq_case_7_2_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem right1Middle3_eq_case_7_2 : right1Middle3 7 2 = associatorInverseZ 3 2 7 * right0Middle3 7 2 := by
  simpa only [HexagonAtoms372.assocABC_eq,
    HexagonAtoms372.outerABC_eq,
    HexagonAtoms372.assocBAC_eq,
    HexagonAtoms372.innerABC_eq,
    HexagonAtoms372.innerRightABC_eq,
    HexagonAtoms372.inverseACB_eq,
    HexagonAtoms372.innerACB_eq,
    HexagonAtoms372.assocBCA_eq,
    HexagonAtoms372.innerRightBAC_eq,
    HexagonAtoms372.assocCAB_eq,
    HexagonAtoms372.outerLeftABC_eq,
    HexagonRowColumn372.product0_eq,
    HexagonRowColumn372.product1_eq,
    HexagonRowColumn372.product2_eq,
    HexagonRowColumn372.product3_eq,
    HexagonRowColumn372.product4_eq,
    HexagonRowColumn372.product5_eq,
    HexagonRowColumn372.product6_eq,
    HexagonRowColumn372.product7_eq] using right1Middle3_eq_case_7_2_checked

private theorem right2Middle3_eq_case_7_2_row_0_0_0 : (right2Middle3 7 2) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (right1Middle3 7 2) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_7_2_row_0_0_1 : (right2Middle3 7 2) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (right1Middle3 7 2) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_7_2_row_0_0_2 : (right2Middle3 7 2) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (right1Middle3 7 2) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_7_2_row_0_0_3 : (right2Middle3 7 2) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (right1Middle3 7 2) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_7_2_row_0_1_0 : (right2Middle3 7 2) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (right1Middle3 7 2) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_7_2_row_0_1_1 : (right2Middle3 7 2) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (right1Middle3 7 2) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_7_2_row_0_1_2 : (right2Middle3 7 2) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (right1Middle3 7 2) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_7_2_row_0_1_3 : (right2Middle3 7 2) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (right1Middle3 7 2) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_7_2_row_1_0_0 : (right2Middle3 7 2) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (right1Middle3 7 2) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_7_2_row_1_0_1 : (right2Middle3 7 2) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (right1Middle3 7 2) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_7_2_row_1_0_2 : (right2Middle3 7 2) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (right1Middle3 7 2) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_7_2_row_1_0_3 : (right2Middle3 7 2) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (right1Middle3 7 2) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_7_2_row_1_1_0 : (right2Middle3 7 2) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (right1Middle3 7 2) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_7_2_row_1_1_1 : (right2Middle3 7 2) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (right1Middle3 7 2) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_7_2_row_1_1_2 : (right2Middle3 7 2) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (right1Middle3 7 2) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_7_2_row_1_1_3 : (right2Middle3 7 2) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (right1Middle3 7 2) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_7_2_checked : right2Middle3 7 2 = right1Middle3 7 2 := by
  funext r
  fin_cases r
  · exact right2Middle3_eq_case_7_2_row_0_0_0
  · exact right2Middle3_eq_case_7_2_row_0_0_1
  · exact right2Middle3_eq_case_7_2_row_0_0_2
  · exact right2Middle3_eq_case_7_2_row_0_0_3
  · exact right2Middle3_eq_case_7_2_row_0_1_0
  · exact right2Middle3_eq_case_7_2_row_0_1_1
  · exact right2Middle3_eq_case_7_2_row_0_1_2
  · exact right2Middle3_eq_case_7_2_row_0_1_3
  · exact right2Middle3_eq_case_7_2_row_1_0_0
  · exact right2Middle3_eq_case_7_2_row_1_0_1
  · exact right2Middle3_eq_case_7_2_row_1_0_2
  · exact right2Middle3_eq_case_7_2_row_1_0_3
  · exact right2Middle3_eq_case_7_2_row_1_1_0
  · exact right2Middle3_eq_case_7_2_row_1_1_1
  · exact right2Middle3_eq_case_7_2_row_1_1_2
  · exact right2Middle3_eq_case_7_2_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem right2Middle3_eq_case_7_2 : right2Middle3 7 2 = innerLeftZ 3 2 7 * right1Middle3 7 2 := by
  simpa only [HexagonAtoms372.assocABC_eq,
    HexagonAtoms372.outerABC_eq,
    HexagonAtoms372.assocBAC_eq,
    HexagonAtoms372.innerABC_eq,
    HexagonAtoms372.innerRightABC_eq,
    HexagonAtoms372.inverseACB_eq,
    HexagonAtoms372.innerACB_eq,
    HexagonAtoms372.assocBCA_eq,
    HexagonAtoms372.innerRightBAC_eq,
    HexagonAtoms372.assocCAB_eq,
    HexagonAtoms372.outerLeftABC_eq,
    HexagonRowColumn372.product0_eq,
    HexagonRowColumn372.product1_eq,
    HexagonRowColumn372.product2_eq,
    HexagonRowColumn372.product3_eq,
    HexagonRowColumn372.product4_eq,
    HexagonRowColumn372.product5_eq,
    HexagonRowColumn372.product6_eq,
    HexagonRowColumn372.product7_eq] using right2Middle3_eq_case_7_2_checked

private theorem leftFinal3_case_7_2_row_0_0_0 : (((-1 : ℤ) ^ (leftScaleBit 3 7 2).val * positiveScale (leftScaleExponent 3 7 2)) •
      (rowColumnMul HexagonRowColumn372.rows_assocBCA HexagonRowColumn372.cols_left0)) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 3 7 2) • (left1Middle3 7 2)) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal3_case_7_2_row_0_0_1 : (((-1 : ℤ) ^ (leftScaleBit 3 7 2).val * positiveScale (leftScaleExponent 3 7 2)) •
      (rowColumnMul HexagonRowColumn372.rows_assocBCA HexagonRowColumn372.cols_left0)) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 3 7 2) • (left1Middle3 7 2)) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal3_case_7_2_row_0_0_2 : (((-1 : ℤ) ^ (leftScaleBit 3 7 2).val * positiveScale (leftScaleExponent 3 7 2)) •
      (rowColumnMul HexagonRowColumn372.rows_assocBCA HexagonRowColumn372.cols_left0)) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 3 7 2) • (left1Middle3 7 2)) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal3_case_7_2_row_0_0_3 : (((-1 : ℤ) ^ (leftScaleBit 3 7 2).val * positiveScale (leftScaleExponent 3 7 2)) •
      (rowColumnMul HexagonRowColumn372.rows_assocBCA HexagonRowColumn372.cols_left0)) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 3 7 2) • (left1Middle3 7 2)) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal3_case_7_2_row_0_1_0 : (((-1 : ℤ) ^ (leftScaleBit 3 7 2).val * positiveScale (leftScaleExponent 3 7 2)) •
      (rowColumnMul HexagonRowColumn372.rows_assocBCA HexagonRowColumn372.cols_left0)) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 3 7 2) • (left1Middle3 7 2)) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal3_case_7_2_row_0_1_1 : (((-1 : ℤ) ^ (leftScaleBit 3 7 2).val * positiveScale (leftScaleExponent 3 7 2)) •
      (rowColumnMul HexagonRowColumn372.rows_assocBCA HexagonRowColumn372.cols_left0)) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 3 7 2) • (left1Middle3 7 2)) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal3_case_7_2_row_0_1_2 : (((-1 : ℤ) ^ (leftScaleBit 3 7 2).val * positiveScale (leftScaleExponent 3 7 2)) •
      (rowColumnMul HexagonRowColumn372.rows_assocBCA HexagonRowColumn372.cols_left0)) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 3 7 2) • (left1Middle3 7 2)) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal3_case_7_2_row_0_1_3 : (((-1 : ℤ) ^ (leftScaleBit 3 7 2).val * positiveScale (leftScaleExponent 3 7 2)) •
      (rowColumnMul HexagonRowColumn372.rows_assocBCA HexagonRowColumn372.cols_left0)) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 3 7 2) • (left1Middle3 7 2)) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal3_case_7_2_row_1_0_0 : (((-1 : ℤ) ^ (leftScaleBit 3 7 2).val * positiveScale (leftScaleExponent 3 7 2)) •
      (rowColumnMul HexagonRowColumn372.rows_assocBCA HexagonRowColumn372.cols_left0)) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 3 7 2) • (left1Middle3 7 2)) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal3_case_7_2_row_1_0_1 : (((-1 : ℤ) ^ (leftScaleBit 3 7 2).val * positiveScale (leftScaleExponent 3 7 2)) •
      (rowColumnMul HexagonRowColumn372.rows_assocBCA HexagonRowColumn372.cols_left0)) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 3 7 2) • (left1Middle3 7 2)) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal3_case_7_2_row_1_0_2 : (((-1 : ℤ) ^ (leftScaleBit 3 7 2).val * positiveScale (leftScaleExponent 3 7 2)) •
      (rowColumnMul HexagonRowColumn372.rows_assocBCA HexagonRowColumn372.cols_left0)) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 3 7 2) • (left1Middle3 7 2)) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal3_case_7_2_row_1_0_3 : (((-1 : ℤ) ^ (leftScaleBit 3 7 2).val * positiveScale (leftScaleExponent 3 7 2)) •
      (rowColumnMul HexagonRowColumn372.rows_assocBCA HexagonRowColumn372.cols_left0)) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 3 7 2) • (left1Middle3 7 2)) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal3_case_7_2_row_1_1_0 : (((-1 : ℤ) ^ (leftScaleBit 3 7 2).val * positiveScale (leftScaleExponent 3 7 2)) •
      (rowColumnMul HexagonRowColumn372.rows_assocBCA HexagonRowColumn372.cols_left0)) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 3 7 2) • (left1Middle3 7 2)) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal3_case_7_2_row_1_1_1 : (((-1 : ℤ) ^ (leftScaleBit 3 7 2).val * positiveScale (leftScaleExponent 3 7 2)) •
      (rowColumnMul HexagonRowColumn372.rows_assocBCA HexagonRowColumn372.cols_left0)) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 3 7 2) • (left1Middle3 7 2)) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal3_case_7_2_row_1_1_2 : (((-1 : ℤ) ^ (leftScaleBit 3 7 2).val * positiveScale (leftScaleExponent 3 7 2)) •
      (rowColumnMul HexagonRowColumn372.rows_assocBCA HexagonRowColumn372.cols_left0)) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 3 7 2) • (left1Middle3 7 2)) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal3_case_7_2_row_1_1_3 : (((-1 : ℤ) ^ (leftScaleBit 3 7 2).val * positiveScale (leftScaleExponent 3 7 2)) •
      (rowColumnMul HexagonRowColumn372.rows_assocBCA HexagonRowColumn372.cols_left0)) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 3 7 2) • (left1Middle3 7 2)) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal3_case_7_2_checked : ((-1 : ℤ) ^ (leftScaleBit 3 7 2).val * positiveScale (leftScaleExponent 3 7 2)) •
      (rowColumnMul HexagonRowColumn372.rows_assocBCA HexagonRowColumn372.cols_left0) = negativeScale (leftScaleExponent 3 7 2) • (left1Middle3 7 2) := by
  funext r
  fin_cases r
  · exact leftFinal3_case_7_2_row_0_0_0
  · exact leftFinal3_case_7_2_row_0_0_1
  · exact leftFinal3_case_7_2_row_0_0_2
  · exact leftFinal3_case_7_2_row_0_0_3
  · exact leftFinal3_case_7_2_row_0_1_0
  · exact leftFinal3_case_7_2_row_0_1_1
  · exact leftFinal3_case_7_2_row_0_1_2
  · exact leftFinal3_case_7_2_row_0_1_3
  · exact leftFinal3_case_7_2_row_1_0_0
  · exact leftFinal3_case_7_2_row_1_0_1
  · exact leftFinal3_case_7_2_row_1_0_2
  · exact leftFinal3_case_7_2_row_1_0_3
  · exact leftFinal3_case_7_2_row_1_1_0
  · exact leftFinal3_case_7_2_row_1_1_1
  · exact leftFinal3_case_7_2_row_1_1_2
  · exact leftFinal3_case_7_2_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem leftFinal3_case_7_2 : ((-1 : ℤ) ^ (leftScaleBit 3 7 2).val * positiveScale (leftScaleExponent 3 7 2)) •
      (associatorZ 7 2 3 * left0Middle3 7 2) = negativeScale (leftScaleExponent 3 7 2) • (innerRightZ 7 3 2 * left1Middle3 7 2) := by
  simpa only [HexagonAtoms372.assocABC_eq,
    HexagonAtoms372.outerABC_eq,
    HexagonAtoms372.assocBAC_eq,
    HexagonAtoms372.innerABC_eq,
    HexagonAtoms372.innerRightABC_eq,
    HexagonAtoms372.inverseACB_eq,
    HexagonAtoms372.innerACB_eq,
    HexagonAtoms372.assocBCA_eq,
    HexagonAtoms372.innerRightBAC_eq,
    HexagonAtoms372.assocCAB_eq,
    HexagonAtoms372.outerLeftABC_eq,
    HexagonRowColumn372.product0_eq,
    HexagonRowColumn372.product1_eq,
    HexagonRowColumn372.product2_eq,
    HexagonRowColumn372.product3_eq,
    HexagonRowColumn372.product4_eq,
    HexagonRowColumn372.product5_eq,
    HexagonRowColumn372.product6_eq,
    HexagonRowColumn372.product7_eq] using leftFinal3_case_7_2_checked

private theorem rightFinal3_case_7_2_row_0_0_0 : (((-1 : ℤ) ^ (rightScaleBit 3 7 2).val * positiveScale (rightScaleExponent 3 7 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 7 : ℤ)) • HexagonAtoms372.outerLeftABC) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 3 7 2) • (rowColumnMul HexagonRowColumn372.rows_assocCAB HexagonRowColumn372.cols_right2)) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal3_case_7_2_row_0_0_1 : (((-1 : ℤ) ^ (rightScaleBit 3 7 2).val * positiveScale (rightScaleExponent 3 7 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 7 : ℤ)) • HexagonAtoms372.outerLeftABC) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 3 7 2) • (rowColumnMul HexagonRowColumn372.rows_assocCAB HexagonRowColumn372.cols_right2)) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal3_case_7_2_row_0_0_2 : (((-1 : ℤ) ^ (rightScaleBit 3 7 2).val * positiveScale (rightScaleExponent 3 7 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 7 : ℤ)) • HexagonAtoms372.outerLeftABC) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 3 7 2) • (rowColumnMul HexagonRowColumn372.rows_assocCAB HexagonRowColumn372.cols_right2)) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal3_case_7_2_row_0_0_3 : (((-1 : ℤ) ^ (rightScaleBit 3 7 2).val * positiveScale (rightScaleExponent 3 7 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 7 : ℤ)) • HexagonAtoms372.outerLeftABC) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 3 7 2) • (rowColumnMul HexagonRowColumn372.rows_assocCAB HexagonRowColumn372.cols_right2)) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal3_case_7_2_row_0_1_0 : (((-1 : ℤ) ^ (rightScaleBit 3 7 2).val * positiveScale (rightScaleExponent 3 7 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 7 : ℤ)) • HexagonAtoms372.outerLeftABC) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 3 7 2) • (rowColumnMul HexagonRowColumn372.rows_assocCAB HexagonRowColumn372.cols_right2)) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal3_case_7_2_row_0_1_1 : (((-1 : ℤ) ^ (rightScaleBit 3 7 2).val * positiveScale (rightScaleExponent 3 7 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 7 : ℤ)) • HexagonAtoms372.outerLeftABC) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 3 7 2) • (rowColumnMul HexagonRowColumn372.rows_assocCAB HexagonRowColumn372.cols_right2)) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal3_case_7_2_row_0_1_2 : (((-1 : ℤ) ^ (rightScaleBit 3 7 2).val * positiveScale (rightScaleExponent 3 7 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 7 : ℤ)) • HexagonAtoms372.outerLeftABC) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 3 7 2) • (rowColumnMul HexagonRowColumn372.rows_assocCAB HexagonRowColumn372.cols_right2)) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal3_case_7_2_row_0_1_3 : (((-1 : ℤ) ^ (rightScaleBit 3 7 2).val * positiveScale (rightScaleExponent 3 7 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 7 : ℤ)) • HexagonAtoms372.outerLeftABC) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 3 7 2) • (rowColumnMul HexagonRowColumn372.rows_assocCAB HexagonRowColumn372.cols_right2)) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal3_case_7_2_row_1_0_0 : (((-1 : ℤ) ^ (rightScaleBit 3 7 2).val * positiveScale (rightScaleExponent 3 7 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 7 : ℤ)) • HexagonAtoms372.outerLeftABC) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 3 7 2) • (rowColumnMul HexagonRowColumn372.rows_assocCAB HexagonRowColumn372.cols_right2)) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal3_case_7_2_row_1_0_1 : (((-1 : ℤ) ^ (rightScaleBit 3 7 2).val * positiveScale (rightScaleExponent 3 7 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 7 : ℤ)) • HexagonAtoms372.outerLeftABC) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 3 7 2) • (rowColumnMul HexagonRowColumn372.rows_assocCAB HexagonRowColumn372.cols_right2)) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal3_case_7_2_row_1_0_2 : (((-1 : ℤ) ^ (rightScaleBit 3 7 2).val * positiveScale (rightScaleExponent 3 7 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 7 : ℤ)) • HexagonAtoms372.outerLeftABC) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 3 7 2) • (rowColumnMul HexagonRowColumn372.rows_assocCAB HexagonRowColumn372.cols_right2)) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal3_case_7_2_row_1_0_3 : (((-1 : ℤ) ^ (rightScaleBit 3 7 2).val * positiveScale (rightScaleExponent 3 7 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 7 : ℤ)) • HexagonAtoms372.outerLeftABC) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 3 7 2) • (rowColumnMul HexagonRowColumn372.rows_assocCAB HexagonRowColumn372.cols_right2)) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal3_case_7_2_row_1_1_0 : (((-1 : ℤ) ^ (rightScaleBit 3 7 2).val * positiveScale (rightScaleExponent 3 7 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 7 : ℤ)) • HexagonAtoms372.outerLeftABC) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 3 7 2) • (rowColumnMul HexagonRowColumn372.rows_assocCAB HexagonRowColumn372.cols_right2)) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal3_case_7_2_row_1_1_1 : (((-1 : ℤ) ^ (rightScaleBit 3 7 2).val * positiveScale (rightScaleExponent 3 7 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 7 : ℤ)) • HexagonAtoms372.outerLeftABC) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 3 7 2) • (rowColumnMul HexagonRowColumn372.rows_assocCAB HexagonRowColumn372.cols_right2)) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal3_case_7_2_row_1_1_2 : (((-1 : ℤ) ^ (rightScaleBit 3 7 2).val * positiveScale (rightScaleExponent 3 7 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 7 : ℤ)) • HexagonAtoms372.outerLeftABC) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 3 7 2) • (rowColumnMul HexagonRowColumn372.rows_assocCAB HexagonRowColumn372.cols_right2)) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal3_case_7_2_row_1_1_3 : (((-1 : ℤ) ^ (rightScaleBit 3 7 2).val * positiveScale (rightScaleExponent 3 7 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 7 : ℤ)) • HexagonAtoms372.outerLeftABC) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 3 7 2) • (rowColumnMul HexagonRowColumn372.rows_assocCAB HexagonRowColumn372.cols_right2)) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal3_case_7_2_checked : ((-1 : ℤ) ^ (rightScaleBit 3 7 2).val * positiveScale (rightScaleExponent 3 7 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 7 : ℤ)) • HexagonAtoms372.outerLeftABC = negativeScale (rightScaleExponent 3 7 2) • (rowColumnMul HexagonRowColumn372.rows_assocCAB HexagonRowColumn372.cols_right2) := by
  funext r
  fin_cases r
  · exact rightFinal3_case_7_2_row_0_0_0
  · exact rightFinal3_case_7_2_row_0_0_1
  · exact rightFinal3_case_7_2_row_0_0_2
  · exact rightFinal3_case_7_2_row_0_0_3
  · exact rightFinal3_case_7_2_row_0_1_0
  · exact rightFinal3_case_7_2_row_0_1_1
  · exact rightFinal3_case_7_2_row_0_1_2
  · exact rightFinal3_case_7_2_row_0_1_3
  · exact rightFinal3_case_7_2_row_1_0_0
  · exact rightFinal3_case_7_2_row_1_0_1
  · exact rightFinal3_case_7_2_row_1_0_2
  · exact rightFinal3_case_7_2_row_1_0_3
  · exact rightFinal3_case_7_2_row_1_1_0
  · exact rightFinal3_case_7_2_row_1_1_1
  · exact rightFinal3_case_7_2_row_1_1_2
  · exact rightFinal3_case_7_2_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem rightFinal3_case_7_2 : ((-1 : ℤ) ^ (rightScaleBit 3 7 2).val * positiveScale (rightScaleExponent 3 7 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 7 : ℤ)) • outerLeftZ 3 7 2 = negativeScale (rightScaleExponent 3 7 2) • (associatorZ 2 3 7 * right2Middle3 7 2) := by
  simpa only [HexagonAtoms372.assocABC_eq,
    HexagonAtoms372.outerABC_eq,
    HexagonAtoms372.assocBAC_eq,
    HexagonAtoms372.innerABC_eq,
    HexagonAtoms372.innerRightABC_eq,
    HexagonAtoms372.inverseACB_eq,
    HexagonAtoms372.innerACB_eq,
    HexagonAtoms372.assocBCA_eq,
    HexagonAtoms372.innerRightBAC_eq,
    HexagonAtoms372.assocCAB_eq,
    HexagonAtoms372.outerLeftABC_eq,
    HexagonRowColumn372.product0_eq,
    HexagonRowColumn372.product1_eq,
    HexagonRowColumn372.product2_eq,
    HexagonRowColumn372.product3_eq,
    HexagonRowColumn372.product4_eq,
    HexagonRowColumn372.product5_eq,
    HexagonRowColumn372.product6_eq,
    HexagonRowColumn372.product7_eq] using rightFinal3_case_7_2_checked

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonCases3
