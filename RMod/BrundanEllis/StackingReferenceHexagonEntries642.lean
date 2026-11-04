import RMod.BrundanEllis.StackingReferenceHexagonMiddle6
import RMod.BrundanEllis.StackingReferenceSparseMatrixCheck
import RMod.BrundanEllis.StackingReferenceHexagonAtoms642
import RMod.BrundanEllis.StackingReferenceHexagonRowColumn642

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

private theorem left0Middle6_eq_case_4_2_row_0_0_0 : (left0Middle6 4 2) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn642.rows_outerABC HexagonRowColumn642.cols_assocABC) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_4_2_row_0_0_1 : (left0Middle6 4 2) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn642.rows_outerABC HexagonRowColumn642.cols_assocABC) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_4_2_row_0_0_2 : (left0Middle6 4 2) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn642.rows_outerABC HexagonRowColumn642.cols_assocABC) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_4_2_row_0_0_3 : (left0Middle6 4 2) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn642.rows_outerABC HexagonRowColumn642.cols_assocABC) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_4_2_row_0_1_0 : (left0Middle6 4 2) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn642.rows_outerABC HexagonRowColumn642.cols_assocABC) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_4_2_row_0_1_1 : (left0Middle6 4 2) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn642.rows_outerABC HexagonRowColumn642.cols_assocABC) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_4_2_row_0_1_2 : (left0Middle6 4 2) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn642.rows_outerABC HexagonRowColumn642.cols_assocABC) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_4_2_row_0_1_3 : (left0Middle6 4 2) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn642.rows_outerABC HexagonRowColumn642.cols_assocABC) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_4_2_row_1_0_0 : (left0Middle6 4 2) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn642.rows_outerABC HexagonRowColumn642.cols_assocABC) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_4_2_row_1_0_1 : (left0Middle6 4 2) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn642.rows_outerABC HexagonRowColumn642.cols_assocABC) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_4_2_row_1_0_2 : (left0Middle6 4 2) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn642.rows_outerABC HexagonRowColumn642.cols_assocABC) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_4_2_row_1_0_3 : (left0Middle6 4 2) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn642.rows_outerABC HexagonRowColumn642.cols_assocABC) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_4_2_row_1_1_0 : (left0Middle6 4 2) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn642.rows_outerABC HexagonRowColumn642.cols_assocABC) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_4_2_row_1_1_1 : (left0Middle6 4 2) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn642.rows_outerABC HexagonRowColumn642.cols_assocABC) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_4_2_row_1_1_2 : (left0Middle6 4 2) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn642.rows_outerABC HexagonRowColumn642.cols_assocABC) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_4_2_row_1_1_3 : (left0Middle6 4 2) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn642.rows_outerABC HexagonRowColumn642.cols_assocABC) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_4_2_checked : left0Middle6 4 2 = rowColumnMul HexagonRowColumn642.rows_outerABC HexagonRowColumn642.cols_assocABC := by
  funext r
  fin_cases r
  · exact left0Middle6_eq_case_4_2_row_0_0_0
  · exact left0Middle6_eq_case_4_2_row_0_0_1
  · exact left0Middle6_eq_case_4_2_row_0_0_2
  · exact left0Middle6_eq_case_4_2_row_0_0_3
  · exact left0Middle6_eq_case_4_2_row_0_1_0
  · exact left0Middle6_eq_case_4_2_row_0_1_1
  · exact left0Middle6_eq_case_4_2_row_0_1_2
  · exact left0Middle6_eq_case_4_2_row_0_1_3
  · exact left0Middle6_eq_case_4_2_row_1_0_0
  · exact left0Middle6_eq_case_4_2_row_1_0_1
  · exact left0Middle6_eq_case_4_2_row_1_0_2
  · exact left0Middle6_eq_case_4_2_row_1_0_3
  · exact left0Middle6_eq_case_4_2_row_1_1_0
  · exact left0Middle6_eq_case_4_2_row_1_1_1
  · exact left0Middle6_eq_case_4_2_row_1_1_2
  · exact left0Middle6_eq_case_4_2_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem left0Middle6_eq_case_4_2 : left0Middle6 4 2 = outerRightZ 6 4 2 * associatorZ 6 4 2 := by
  simpa only [HexagonAtoms642.assocABC_eq,
    HexagonAtoms642.outerABC_eq,
    HexagonAtoms642.assocBAC_eq,
    HexagonAtoms642.innerABC_eq,
    HexagonAtoms642.innerRightABC_eq,
    HexagonAtoms642.inverseACB_eq,
    HexagonAtoms642.innerACB_eq,
    HexagonAtoms642.assocBCA_eq,
    HexagonAtoms642.innerRightBAC_eq,
    HexagonAtoms642.assocCAB_eq,
    HexagonAtoms642.outerLeftABC_eq,
    HexagonRowColumn642.product0_eq,
    HexagonRowColumn642.product1_eq,
    HexagonRowColumn642.product2_eq,
    HexagonRowColumn642.product3_eq,
    HexagonRowColumn642.product4_eq,
    HexagonRowColumn642.product5_eq,
    HexagonRowColumn642.product6_eq,
    HexagonRowColumn642.product7_eq] using left0Middle6_eq_case_4_2_checked

private theorem left1Middle6_eq_case_4_2_row_0_0_0 : (left1Middle6 4 2) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms642.assocBAC) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_4_2_row_0_0_1 : (left1Middle6 4 2) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms642.assocBAC) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_4_2_row_0_0_2 : (left1Middle6 4 2) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms642.assocBAC) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_4_2_row_0_0_3 : (left1Middle6 4 2) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms642.assocBAC) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_4_2_row_1_0_0 : (left1Middle6 4 2) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms642.assocBAC) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_4_2_row_1_0_1 : (left1Middle6 4 2) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms642.assocBAC) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_4_2_row_1_0_2 : (left1Middle6 4 2) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms642.assocBAC) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_4_2_row_1_0_3 : (left1Middle6 4 2) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms642.assocBAC) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_4_2_row_2_0_0 : (left1Middle6 4 2) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms642.assocBAC) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_4_2_row_2_0_1 : (left1Middle6 4 2) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms642.assocBAC) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_4_2_row_2_0_2 : (left1Middle6 4 2) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms642.assocBAC) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_4_2_row_2_0_3 : (left1Middle6 4 2) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms642.assocBAC) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_4_2_row_3_0_0 : (left1Middle6 4 2) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms642.assocBAC) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_4_2_row_3_0_1 : (left1Middle6 4 2) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms642.assocBAC) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_4_2_row_3_0_2 : (left1Middle6 4 2) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms642.assocBAC) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_4_2_row_3_0_3 : (left1Middle6 4 2) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms642.assocBAC) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_4_2_checked : left1Middle6 4 2 = HexagonAtoms642.assocBAC := by
  funext r
  fin_cases r
  · exact left1Middle6_eq_case_4_2_row_0_0_0
  · exact left1Middle6_eq_case_4_2_row_0_0_1
  · exact left1Middle6_eq_case_4_2_row_0_0_2
  · exact left1Middle6_eq_case_4_2_row_0_0_3
  · exact left1Middle6_eq_case_4_2_row_1_0_0
  · exact left1Middle6_eq_case_4_2_row_1_0_1
  · exact left1Middle6_eq_case_4_2_row_1_0_2
  · exact left1Middle6_eq_case_4_2_row_1_0_3
  · exact left1Middle6_eq_case_4_2_row_2_0_0
  · exact left1Middle6_eq_case_4_2_row_2_0_1
  · exact left1Middle6_eq_case_4_2_row_2_0_2
  · exact left1Middle6_eq_case_4_2_row_2_0_3
  · exact left1Middle6_eq_case_4_2_row_3_0_0
  · exact left1Middle6_eq_case_4_2_row_3_0_1
  · exact left1Middle6_eq_case_4_2_row_3_0_2
  · exact left1Middle6_eq_case_4_2_row_3_0_3

set_option backward.isDefEq.respectTransparency false in
theorem left1Middle6_eq_case_4_2 : left1Middle6 4 2 = associatorZ 4 6 2 * innerLeftZ 6 4 2 := by
  simpa only [HexagonAtoms642.assocABC_eq,
    HexagonAtoms642.outerABC_eq,
    HexagonAtoms642.assocBAC_eq,
    HexagonAtoms642.innerABC_eq,
    HexagonAtoms642.innerRightABC_eq,
    HexagonAtoms642.inverseACB_eq,
    HexagonAtoms642.innerACB_eq,
    HexagonAtoms642.assocBCA_eq,
    HexagonAtoms642.innerRightBAC_eq,
    HexagonAtoms642.assocCAB_eq,
    HexagonAtoms642.outerLeftABC_eq,
    HexagonRowColumn642.product0_eq,
    HexagonRowColumn642.product1_eq,
    HexagonRowColumn642.product2_eq,
    HexagonRowColumn642.product3_eq,
    HexagonRowColumn642.product4_eq,
    HexagonRowColumn642.product5_eq,
    HexagonRowColumn642.product6_eq,
    HexagonRowColumn642.product7_eq] using left1Middle6_eq_case_4_2_checked

private theorem right0Middle6_eq_case_4_2_row_0_0_0 : (right0Middle6 4 2) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms642.assocABC) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_4_2_row_0_0_1 : (right0Middle6 4 2) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms642.assocABC) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_4_2_row_0_0_2 : (right0Middle6 4 2) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms642.assocABC) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_4_2_row_0_0_3 : (right0Middle6 4 2) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms642.assocABC) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_4_2_row_0_1_0 : (right0Middle6 4 2) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms642.assocABC) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_4_2_row_0_1_1 : (right0Middle6 4 2) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms642.assocABC) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_4_2_row_0_1_2 : (right0Middle6 4 2) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms642.assocABC) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_4_2_row_0_1_3 : (right0Middle6 4 2) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms642.assocABC) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_4_2_row_1_0_0 : (right0Middle6 4 2) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms642.assocABC) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_4_2_row_1_0_1 : (right0Middle6 4 2) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms642.assocABC) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_4_2_row_1_0_2 : (right0Middle6 4 2) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms642.assocABC) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_4_2_row_1_0_3 : (right0Middle6 4 2) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms642.assocABC) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_4_2_row_1_1_0 : (right0Middle6 4 2) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms642.assocABC) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_4_2_row_1_1_1 : (right0Middle6 4 2) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms642.assocABC) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_4_2_row_1_1_2 : (right0Middle6 4 2) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms642.assocABC) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_4_2_row_1_1_3 : (right0Middle6 4 2) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms642.assocABC) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_4_2_checked : right0Middle6 4 2 = HexagonAtoms642.assocABC := by
  funext r
  fin_cases r
  · exact right0Middle6_eq_case_4_2_row_0_0_0
  · exact right0Middle6_eq_case_4_2_row_0_0_1
  · exact right0Middle6_eq_case_4_2_row_0_0_2
  · exact right0Middle6_eq_case_4_2_row_0_0_3
  · exact right0Middle6_eq_case_4_2_row_0_1_0
  · exact right0Middle6_eq_case_4_2_row_0_1_1
  · exact right0Middle6_eq_case_4_2_row_0_1_2
  · exact right0Middle6_eq_case_4_2_row_0_1_3
  · exact right0Middle6_eq_case_4_2_row_1_0_0
  · exact right0Middle6_eq_case_4_2_row_1_0_1
  · exact right0Middle6_eq_case_4_2_row_1_0_2
  · exact right0Middle6_eq_case_4_2_row_1_0_3
  · exact right0Middle6_eq_case_4_2_row_1_1_0
  · exact right0Middle6_eq_case_4_2_row_1_1_1
  · exact right0Middle6_eq_case_4_2_row_1_1_2
  · exact right0Middle6_eq_case_4_2_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem right0Middle6_eq_case_4_2 : right0Middle6 4 2 = innerRightZ 6 4 2 * associatorZ 6 4 2 := by
  simpa only [HexagonAtoms642.assocABC_eq,
    HexagonAtoms642.outerABC_eq,
    HexagonAtoms642.assocBAC_eq,
    HexagonAtoms642.innerABC_eq,
    HexagonAtoms642.innerRightABC_eq,
    HexagonAtoms642.inverseACB_eq,
    HexagonAtoms642.innerACB_eq,
    HexagonAtoms642.assocBCA_eq,
    HexagonAtoms642.innerRightBAC_eq,
    HexagonAtoms642.assocCAB_eq,
    HexagonAtoms642.outerLeftABC_eq,
    HexagonRowColumn642.product0_eq,
    HexagonRowColumn642.product1_eq,
    HexagonRowColumn642.product2_eq,
    HexagonRowColumn642.product3_eq,
    HexagonRowColumn642.product4_eq,
    HexagonRowColumn642.product5_eq,
    HexagonRowColumn642.product6_eq,
    HexagonRowColumn642.product7_eq] using right0Middle6_eq_case_4_2_checked

private theorem right1Middle6_eq_case_4_2_row_0_0_0 : (right1Middle6 4 2) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn642.rows_inverseACB HexagonRowColumn642.cols_right0) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_4_2_row_0_0_1 : (right1Middle6 4 2) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn642.rows_inverseACB HexagonRowColumn642.cols_right0) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_4_2_row_0_0_2 : (right1Middle6 4 2) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn642.rows_inverseACB HexagonRowColumn642.cols_right0) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_4_2_row_0_0_3 : (right1Middle6 4 2) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn642.rows_inverseACB HexagonRowColumn642.cols_right0) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_4_2_row_1_0_0 : (right1Middle6 4 2) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn642.rows_inverseACB HexagonRowColumn642.cols_right0) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_4_2_row_1_0_1 : (right1Middle6 4 2) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn642.rows_inverseACB HexagonRowColumn642.cols_right0) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_4_2_row_1_0_2 : (right1Middle6 4 2) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn642.rows_inverseACB HexagonRowColumn642.cols_right0) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_4_2_row_1_0_3 : (right1Middle6 4 2) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn642.rows_inverseACB HexagonRowColumn642.cols_right0) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_4_2_row_2_0_0 : (right1Middle6 4 2) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn642.rows_inverseACB HexagonRowColumn642.cols_right0) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_4_2_row_2_0_1 : (right1Middle6 4 2) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn642.rows_inverseACB HexagonRowColumn642.cols_right0) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_4_2_row_2_0_2 : (right1Middle6 4 2) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn642.rows_inverseACB HexagonRowColumn642.cols_right0) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_4_2_row_2_0_3 : (right1Middle6 4 2) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn642.rows_inverseACB HexagonRowColumn642.cols_right0) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_4_2_row_3_0_0 : (right1Middle6 4 2) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn642.rows_inverseACB HexagonRowColumn642.cols_right0) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_4_2_row_3_0_1 : (right1Middle6 4 2) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn642.rows_inverseACB HexagonRowColumn642.cols_right0) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_4_2_row_3_0_2 : (right1Middle6 4 2) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn642.rows_inverseACB HexagonRowColumn642.cols_right0) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_4_2_row_3_0_3 : (right1Middle6 4 2) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn642.rows_inverseACB HexagonRowColumn642.cols_right0) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_4_2_checked : right1Middle6 4 2 = rowColumnMul HexagonRowColumn642.rows_inverseACB HexagonRowColumn642.cols_right0 := by
  funext r
  fin_cases r
  · exact right1Middle6_eq_case_4_2_row_0_0_0
  · exact right1Middle6_eq_case_4_2_row_0_0_1
  · exact right1Middle6_eq_case_4_2_row_0_0_2
  · exact right1Middle6_eq_case_4_2_row_0_0_3
  · exact right1Middle6_eq_case_4_2_row_1_0_0
  · exact right1Middle6_eq_case_4_2_row_1_0_1
  · exact right1Middle6_eq_case_4_2_row_1_0_2
  · exact right1Middle6_eq_case_4_2_row_1_0_3
  · exact right1Middle6_eq_case_4_2_row_2_0_0
  · exact right1Middle6_eq_case_4_2_row_2_0_1
  · exact right1Middle6_eq_case_4_2_row_2_0_2
  · exact right1Middle6_eq_case_4_2_row_2_0_3
  · exact right1Middle6_eq_case_4_2_row_3_0_0
  · exact right1Middle6_eq_case_4_2_row_3_0_1
  · exact right1Middle6_eq_case_4_2_row_3_0_2
  · exact right1Middle6_eq_case_4_2_row_3_0_3

set_option backward.isDefEq.respectTransparency false in
theorem right1Middle6_eq_case_4_2 : right1Middle6 4 2 = associatorInverseZ 6 2 4 * right0Middle6 4 2 := by
  simpa only [HexagonAtoms642.assocABC_eq,
    HexagonAtoms642.outerABC_eq,
    HexagonAtoms642.assocBAC_eq,
    HexagonAtoms642.innerABC_eq,
    HexagonAtoms642.innerRightABC_eq,
    HexagonAtoms642.inverseACB_eq,
    HexagonAtoms642.innerACB_eq,
    HexagonAtoms642.assocBCA_eq,
    HexagonAtoms642.innerRightBAC_eq,
    HexagonAtoms642.assocCAB_eq,
    HexagonAtoms642.outerLeftABC_eq,
    HexagonRowColumn642.product0_eq,
    HexagonRowColumn642.product1_eq,
    HexagonRowColumn642.product2_eq,
    HexagonRowColumn642.product3_eq,
    HexagonRowColumn642.product4_eq,
    HexagonRowColumn642.product5_eq,
    HexagonRowColumn642.product6_eq,
    HexagonRowColumn642.product7_eq] using right1Middle6_eq_case_4_2_checked

private theorem right2Middle6_eq_case_4_2_row_0_0_0 : (right2Middle6 4 2) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (right1Middle6 4 2) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_4_2_row_0_0_1 : (right2Middle6 4 2) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (right1Middle6 4 2) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_4_2_row_0_0_2 : (right2Middle6 4 2) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (right1Middle6 4 2) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_4_2_row_0_0_3 : (right2Middle6 4 2) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (right1Middle6 4 2) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_4_2_row_1_0_0 : (right2Middle6 4 2) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (right1Middle6 4 2) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_4_2_row_1_0_1 : (right2Middle6 4 2) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (right1Middle6 4 2) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_4_2_row_1_0_2 : (right2Middle6 4 2) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (right1Middle6 4 2) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_4_2_row_1_0_3 : (right2Middle6 4 2) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (right1Middle6 4 2) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_4_2_row_2_0_0 : (right2Middle6 4 2) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (right1Middle6 4 2) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_4_2_row_2_0_1 : (right2Middle6 4 2) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (right1Middle6 4 2) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_4_2_row_2_0_2 : (right2Middle6 4 2) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (right1Middle6 4 2) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_4_2_row_2_0_3 : (right2Middle6 4 2) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (right1Middle6 4 2) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_4_2_row_3_0_0 : (right2Middle6 4 2) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (right1Middle6 4 2) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_4_2_row_3_0_1 : (right2Middle6 4 2) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (right1Middle6 4 2) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_4_2_row_3_0_2 : (right2Middle6 4 2) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (right1Middle6 4 2) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_4_2_row_3_0_3 : (right2Middle6 4 2) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (right1Middle6 4 2) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_4_2_checked : right2Middle6 4 2 = right1Middle6 4 2 := by
  funext r
  fin_cases r
  · exact right2Middle6_eq_case_4_2_row_0_0_0
  · exact right2Middle6_eq_case_4_2_row_0_0_1
  · exact right2Middle6_eq_case_4_2_row_0_0_2
  · exact right2Middle6_eq_case_4_2_row_0_0_3
  · exact right2Middle6_eq_case_4_2_row_1_0_0
  · exact right2Middle6_eq_case_4_2_row_1_0_1
  · exact right2Middle6_eq_case_4_2_row_1_0_2
  · exact right2Middle6_eq_case_4_2_row_1_0_3
  · exact right2Middle6_eq_case_4_2_row_2_0_0
  · exact right2Middle6_eq_case_4_2_row_2_0_1
  · exact right2Middle6_eq_case_4_2_row_2_0_2
  · exact right2Middle6_eq_case_4_2_row_2_0_3
  · exact right2Middle6_eq_case_4_2_row_3_0_0
  · exact right2Middle6_eq_case_4_2_row_3_0_1
  · exact right2Middle6_eq_case_4_2_row_3_0_2
  · exact right2Middle6_eq_case_4_2_row_3_0_3

set_option backward.isDefEq.respectTransparency false in
theorem right2Middle6_eq_case_4_2 : right2Middle6 4 2 = innerLeftZ 6 2 4 * right1Middle6 4 2 := by
  simpa only [HexagonAtoms642.assocABC_eq,
    HexagonAtoms642.outerABC_eq,
    HexagonAtoms642.assocBAC_eq,
    HexagonAtoms642.innerABC_eq,
    HexagonAtoms642.innerRightABC_eq,
    HexagonAtoms642.inverseACB_eq,
    HexagonAtoms642.innerACB_eq,
    HexagonAtoms642.assocBCA_eq,
    HexagonAtoms642.innerRightBAC_eq,
    HexagonAtoms642.assocCAB_eq,
    HexagonAtoms642.outerLeftABC_eq,
    HexagonRowColumn642.product0_eq,
    HexagonRowColumn642.product1_eq,
    HexagonRowColumn642.product2_eq,
    HexagonRowColumn642.product3_eq,
    HexagonRowColumn642.product4_eq,
    HexagonRowColumn642.product5_eq,
    HexagonRowColumn642.product6_eq,
    HexagonRowColumn642.product7_eq] using right2Middle6_eq_case_4_2_checked

private theorem leftFinal6_case_4_2_row_0_0_0 : (((-1 : ℤ) ^ (leftScaleBit 6 4 2).val * positiveScale (leftScaleExponent 6 4 2)) •
      (rowColumnMul HexagonRowColumn642.rows_assocBCA HexagonRowColumn642.cols_left0)) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (negativeScale (leftScaleExponent 6 4 2) • (left1Middle6 4 2)) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal6_case_4_2_row_0_0_1 : (((-1 : ℤ) ^ (leftScaleBit 6 4 2).val * positiveScale (leftScaleExponent 6 4 2)) •
      (rowColumnMul HexagonRowColumn642.rows_assocBCA HexagonRowColumn642.cols_left0)) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (negativeScale (leftScaleExponent 6 4 2) • (left1Middle6 4 2)) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal6_case_4_2_row_0_0_2 : (((-1 : ℤ) ^ (leftScaleBit 6 4 2).val * positiveScale (leftScaleExponent 6 4 2)) •
      (rowColumnMul HexagonRowColumn642.rows_assocBCA HexagonRowColumn642.cols_left0)) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (negativeScale (leftScaleExponent 6 4 2) • (left1Middle6 4 2)) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal6_case_4_2_row_0_0_3 : (((-1 : ℤ) ^ (leftScaleBit 6 4 2).val * positiveScale (leftScaleExponent 6 4 2)) •
      (rowColumnMul HexagonRowColumn642.rows_assocBCA HexagonRowColumn642.cols_left0)) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (negativeScale (leftScaleExponent 6 4 2) • (left1Middle6 4 2)) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal6_case_4_2_row_1_0_0 : (((-1 : ℤ) ^ (leftScaleBit 6 4 2).val * positiveScale (leftScaleExponent 6 4 2)) •
      (rowColumnMul HexagonRowColumn642.rows_assocBCA HexagonRowColumn642.cols_left0)) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (negativeScale (leftScaleExponent 6 4 2) • (left1Middle6 4 2)) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal6_case_4_2_row_1_0_1 : (((-1 : ℤ) ^ (leftScaleBit 6 4 2).val * positiveScale (leftScaleExponent 6 4 2)) •
      (rowColumnMul HexagonRowColumn642.rows_assocBCA HexagonRowColumn642.cols_left0)) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (negativeScale (leftScaleExponent 6 4 2) • (left1Middle6 4 2)) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal6_case_4_2_row_1_0_2 : (((-1 : ℤ) ^ (leftScaleBit 6 4 2).val * positiveScale (leftScaleExponent 6 4 2)) •
      (rowColumnMul HexagonRowColumn642.rows_assocBCA HexagonRowColumn642.cols_left0)) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (negativeScale (leftScaleExponent 6 4 2) • (left1Middle6 4 2)) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal6_case_4_2_row_1_0_3 : (((-1 : ℤ) ^ (leftScaleBit 6 4 2).val * positiveScale (leftScaleExponent 6 4 2)) •
      (rowColumnMul HexagonRowColumn642.rows_assocBCA HexagonRowColumn642.cols_left0)) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (negativeScale (leftScaleExponent 6 4 2) • (left1Middle6 4 2)) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal6_case_4_2_row_2_0_0 : (((-1 : ℤ) ^ (leftScaleBit 6 4 2).val * positiveScale (leftScaleExponent 6 4 2)) •
      (rowColumnMul HexagonRowColumn642.rows_assocBCA HexagonRowColumn642.cols_left0)) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (negativeScale (leftScaleExponent 6 4 2) • (left1Middle6 4 2)) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal6_case_4_2_row_2_0_1 : (((-1 : ℤ) ^ (leftScaleBit 6 4 2).val * positiveScale (leftScaleExponent 6 4 2)) •
      (rowColumnMul HexagonRowColumn642.rows_assocBCA HexagonRowColumn642.cols_left0)) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (negativeScale (leftScaleExponent 6 4 2) • (left1Middle6 4 2)) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal6_case_4_2_row_2_0_2 : (((-1 : ℤ) ^ (leftScaleBit 6 4 2).val * positiveScale (leftScaleExponent 6 4 2)) •
      (rowColumnMul HexagonRowColumn642.rows_assocBCA HexagonRowColumn642.cols_left0)) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (negativeScale (leftScaleExponent 6 4 2) • (left1Middle6 4 2)) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal6_case_4_2_row_2_0_3 : (((-1 : ℤ) ^ (leftScaleBit 6 4 2).val * positiveScale (leftScaleExponent 6 4 2)) •
      (rowColumnMul HexagonRowColumn642.rows_assocBCA HexagonRowColumn642.cols_left0)) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (negativeScale (leftScaleExponent 6 4 2) • (left1Middle6 4 2)) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal6_case_4_2_row_3_0_0 : (((-1 : ℤ) ^ (leftScaleBit 6 4 2).val * positiveScale (leftScaleExponent 6 4 2)) •
      (rowColumnMul HexagonRowColumn642.rows_assocBCA HexagonRowColumn642.cols_left0)) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (negativeScale (leftScaleExponent 6 4 2) • (left1Middle6 4 2)) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal6_case_4_2_row_3_0_1 : (((-1 : ℤ) ^ (leftScaleBit 6 4 2).val * positiveScale (leftScaleExponent 6 4 2)) •
      (rowColumnMul HexagonRowColumn642.rows_assocBCA HexagonRowColumn642.cols_left0)) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (negativeScale (leftScaleExponent 6 4 2) • (left1Middle6 4 2)) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal6_case_4_2_row_3_0_2 : (((-1 : ℤ) ^ (leftScaleBit 6 4 2).val * positiveScale (leftScaleExponent 6 4 2)) •
      (rowColumnMul HexagonRowColumn642.rows_assocBCA HexagonRowColumn642.cols_left0)) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (negativeScale (leftScaleExponent 6 4 2) • (left1Middle6 4 2)) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal6_case_4_2_row_3_0_3 : (((-1 : ℤ) ^ (leftScaleBit 6 4 2).val * positiveScale (leftScaleExponent 6 4 2)) •
      (rowColumnMul HexagonRowColumn642.rows_assocBCA HexagonRowColumn642.cols_left0)) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (negativeScale (leftScaleExponent 6 4 2) • (left1Middle6 4 2)) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal6_case_4_2_checked : ((-1 : ℤ) ^ (leftScaleBit 6 4 2).val * positiveScale (leftScaleExponent 6 4 2)) •
      (rowColumnMul HexagonRowColumn642.rows_assocBCA HexagonRowColumn642.cols_left0) = negativeScale (leftScaleExponent 6 4 2) • (left1Middle6 4 2) := by
  funext r
  fin_cases r
  · exact leftFinal6_case_4_2_row_0_0_0
  · exact leftFinal6_case_4_2_row_0_0_1
  · exact leftFinal6_case_4_2_row_0_0_2
  · exact leftFinal6_case_4_2_row_0_0_3
  · exact leftFinal6_case_4_2_row_1_0_0
  · exact leftFinal6_case_4_2_row_1_0_1
  · exact leftFinal6_case_4_2_row_1_0_2
  · exact leftFinal6_case_4_2_row_1_0_3
  · exact leftFinal6_case_4_2_row_2_0_0
  · exact leftFinal6_case_4_2_row_2_0_1
  · exact leftFinal6_case_4_2_row_2_0_2
  · exact leftFinal6_case_4_2_row_2_0_3
  · exact leftFinal6_case_4_2_row_3_0_0
  · exact leftFinal6_case_4_2_row_3_0_1
  · exact leftFinal6_case_4_2_row_3_0_2
  · exact leftFinal6_case_4_2_row_3_0_3

set_option backward.isDefEq.respectTransparency false in
theorem leftFinal6_case_4_2 : ((-1 : ℤ) ^ (leftScaleBit 6 4 2).val * positiveScale (leftScaleExponent 6 4 2)) •
      (associatorZ 4 2 6 * left0Middle6 4 2) = negativeScale (leftScaleExponent 6 4 2) • (innerRightZ 4 6 2 * left1Middle6 4 2) := by
  simpa only [HexagonAtoms642.assocABC_eq,
    HexagonAtoms642.outerABC_eq,
    HexagonAtoms642.assocBAC_eq,
    HexagonAtoms642.innerABC_eq,
    HexagonAtoms642.innerRightABC_eq,
    HexagonAtoms642.inverseACB_eq,
    HexagonAtoms642.innerACB_eq,
    HexagonAtoms642.assocBCA_eq,
    HexagonAtoms642.innerRightBAC_eq,
    HexagonAtoms642.assocCAB_eq,
    HexagonAtoms642.outerLeftABC_eq,
    HexagonRowColumn642.product0_eq,
    HexagonRowColumn642.product1_eq,
    HexagonRowColumn642.product2_eq,
    HexagonRowColumn642.product3_eq,
    HexagonRowColumn642.product4_eq,
    HexagonRowColumn642.product5_eq,
    HexagonRowColumn642.product6_eq,
    HexagonRowColumn642.product7_eq] using leftFinal6_case_4_2_checked

private theorem rightFinal6_case_4_2_row_0_0_0 : (((-1 : ℤ) ^ (rightScaleBit 6 4 2).val * positiveScale (rightScaleExponent 6 4 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 2 4 : ℤ)) • HexagonAtoms642.outerLeftABC) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 6 4 2) • (rowColumnMul HexagonRowColumn642.rows_assocCAB HexagonRowColumn642.cols_right2)) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal6_case_4_2_row_0_0_1 : (((-1 : ℤ) ^ (rightScaleBit 6 4 2).val * positiveScale (rightScaleExponent 6 4 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 2 4 : ℤ)) • HexagonAtoms642.outerLeftABC) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 6 4 2) • (rowColumnMul HexagonRowColumn642.rows_assocCAB HexagonRowColumn642.cols_right2)) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal6_case_4_2_row_0_0_2 : (((-1 : ℤ) ^ (rightScaleBit 6 4 2).val * positiveScale (rightScaleExponent 6 4 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 2 4 : ℤ)) • HexagonAtoms642.outerLeftABC) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 6 4 2) • (rowColumnMul HexagonRowColumn642.rows_assocCAB HexagonRowColumn642.cols_right2)) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal6_case_4_2_row_0_0_3 : (((-1 : ℤ) ^ (rightScaleBit 6 4 2).val * positiveScale (rightScaleExponent 6 4 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 2 4 : ℤ)) • HexagonAtoms642.outerLeftABC) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 6 4 2) • (rowColumnMul HexagonRowColumn642.rows_assocCAB HexagonRowColumn642.cols_right2)) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal6_case_4_2_row_0_1_0 : (((-1 : ℤ) ^ (rightScaleBit 6 4 2).val * positiveScale (rightScaleExponent 6 4 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 2 4 : ℤ)) • HexagonAtoms642.outerLeftABC) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 6 4 2) • (rowColumnMul HexagonRowColumn642.rows_assocCAB HexagonRowColumn642.cols_right2)) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal6_case_4_2_row_0_1_1 : (((-1 : ℤ) ^ (rightScaleBit 6 4 2).val * positiveScale (rightScaleExponent 6 4 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 2 4 : ℤ)) • HexagonAtoms642.outerLeftABC) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 6 4 2) • (rowColumnMul HexagonRowColumn642.rows_assocCAB HexagonRowColumn642.cols_right2)) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal6_case_4_2_row_0_1_2 : (((-1 : ℤ) ^ (rightScaleBit 6 4 2).val * positiveScale (rightScaleExponent 6 4 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 2 4 : ℤ)) • HexagonAtoms642.outerLeftABC) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 6 4 2) • (rowColumnMul HexagonRowColumn642.rows_assocCAB HexagonRowColumn642.cols_right2)) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal6_case_4_2_row_0_1_3 : (((-1 : ℤ) ^ (rightScaleBit 6 4 2).val * positiveScale (rightScaleExponent 6 4 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 2 4 : ℤ)) • HexagonAtoms642.outerLeftABC) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 6 4 2) • (rowColumnMul HexagonRowColumn642.rows_assocCAB HexagonRowColumn642.cols_right2)) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal6_case_4_2_row_1_0_0 : (((-1 : ℤ) ^ (rightScaleBit 6 4 2).val * positiveScale (rightScaleExponent 6 4 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 2 4 : ℤ)) • HexagonAtoms642.outerLeftABC) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 6 4 2) • (rowColumnMul HexagonRowColumn642.rows_assocCAB HexagonRowColumn642.cols_right2)) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal6_case_4_2_row_1_0_1 : (((-1 : ℤ) ^ (rightScaleBit 6 4 2).val * positiveScale (rightScaleExponent 6 4 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 2 4 : ℤ)) • HexagonAtoms642.outerLeftABC) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 6 4 2) • (rowColumnMul HexagonRowColumn642.rows_assocCAB HexagonRowColumn642.cols_right2)) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal6_case_4_2_row_1_0_2 : (((-1 : ℤ) ^ (rightScaleBit 6 4 2).val * positiveScale (rightScaleExponent 6 4 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 2 4 : ℤ)) • HexagonAtoms642.outerLeftABC) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 6 4 2) • (rowColumnMul HexagonRowColumn642.rows_assocCAB HexagonRowColumn642.cols_right2)) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal6_case_4_2_row_1_0_3 : (((-1 : ℤ) ^ (rightScaleBit 6 4 2).val * positiveScale (rightScaleExponent 6 4 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 2 4 : ℤ)) • HexagonAtoms642.outerLeftABC) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 6 4 2) • (rowColumnMul HexagonRowColumn642.rows_assocCAB HexagonRowColumn642.cols_right2)) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal6_case_4_2_row_1_1_0 : (((-1 : ℤ) ^ (rightScaleBit 6 4 2).val * positiveScale (rightScaleExponent 6 4 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 2 4 : ℤ)) • HexagonAtoms642.outerLeftABC) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 6 4 2) • (rowColumnMul HexagonRowColumn642.rows_assocCAB HexagonRowColumn642.cols_right2)) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal6_case_4_2_row_1_1_1 : (((-1 : ℤ) ^ (rightScaleBit 6 4 2).val * positiveScale (rightScaleExponent 6 4 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 2 4 : ℤ)) • HexagonAtoms642.outerLeftABC) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 6 4 2) • (rowColumnMul HexagonRowColumn642.rows_assocCAB HexagonRowColumn642.cols_right2)) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal6_case_4_2_row_1_1_2 : (((-1 : ℤ) ^ (rightScaleBit 6 4 2).val * positiveScale (rightScaleExponent 6 4 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 2 4 : ℤ)) • HexagonAtoms642.outerLeftABC) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 6 4 2) • (rowColumnMul HexagonRowColumn642.rows_assocCAB HexagonRowColumn642.cols_right2)) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal6_case_4_2_row_1_1_3 : (((-1 : ℤ) ^ (rightScaleBit 6 4 2).val * positiveScale (rightScaleExponent 6 4 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 2 4 : ℤ)) • HexagonAtoms642.outerLeftABC) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 6 4 2) • (rowColumnMul HexagonRowColumn642.rows_assocCAB HexagonRowColumn642.cols_right2)) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal6_case_4_2_checked : ((-1 : ℤ) ^ (rightScaleBit 6 4 2).val * positiveScale (rightScaleExponent 6 4 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 2 4 : ℤ)) • HexagonAtoms642.outerLeftABC = negativeScale (rightScaleExponent 6 4 2) • (rowColumnMul HexagonRowColumn642.rows_assocCAB HexagonRowColumn642.cols_right2) := by
  funext r
  fin_cases r
  · exact rightFinal6_case_4_2_row_0_0_0
  · exact rightFinal6_case_4_2_row_0_0_1
  · exact rightFinal6_case_4_2_row_0_0_2
  · exact rightFinal6_case_4_2_row_0_0_3
  · exact rightFinal6_case_4_2_row_0_1_0
  · exact rightFinal6_case_4_2_row_0_1_1
  · exact rightFinal6_case_4_2_row_0_1_2
  · exact rightFinal6_case_4_2_row_0_1_3
  · exact rightFinal6_case_4_2_row_1_0_0
  · exact rightFinal6_case_4_2_row_1_0_1
  · exact rightFinal6_case_4_2_row_1_0_2
  · exact rightFinal6_case_4_2_row_1_0_3
  · exact rightFinal6_case_4_2_row_1_1_0
  · exact rightFinal6_case_4_2_row_1_1_1
  · exact rightFinal6_case_4_2_row_1_1_2
  · exact rightFinal6_case_4_2_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem rightFinal6_case_4_2 : ((-1 : ℤ) ^ (rightScaleBit 6 4 2).val * positiveScale (rightScaleExponent 6 4 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 2 4 : ℤ)) • outerLeftZ 6 4 2 = negativeScale (rightScaleExponent 6 4 2) • (associatorZ 2 6 4 * right2Middle6 4 2) := by
  simpa only [HexagonAtoms642.assocABC_eq,
    HexagonAtoms642.outerABC_eq,
    HexagonAtoms642.assocBAC_eq,
    HexagonAtoms642.innerABC_eq,
    HexagonAtoms642.innerRightABC_eq,
    HexagonAtoms642.inverseACB_eq,
    HexagonAtoms642.innerACB_eq,
    HexagonAtoms642.assocBCA_eq,
    HexagonAtoms642.innerRightBAC_eq,
    HexagonAtoms642.assocCAB_eq,
    HexagonAtoms642.outerLeftABC_eq,
    HexagonRowColumn642.product0_eq,
    HexagonRowColumn642.product1_eq,
    HexagonRowColumn642.product2_eq,
    HexagonRowColumn642.product3_eq,
    HexagonRowColumn642.product4_eq,
    HexagonRowColumn642.product5_eq,
    HexagonRowColumn642.product6_eq,
    HexagonRowColumn642.product7_eq] using rightFinal6_case_4_2_checked

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonCases6
