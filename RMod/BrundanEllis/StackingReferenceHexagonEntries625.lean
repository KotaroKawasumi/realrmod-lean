import RMod.BrundanEllis.StackingReferenceHexagonMiddle6
import RMod.BrundanEllis.StackingReferenceSparseMatrixCheck
import RMod.BrundanEllis.StackingReferenceHexagonAtoms625
import RMod.BrundanEllis.StackingReferenceHexagonRowColumn625

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

private theorem left0Middle6_eq_case_2_5_row_0_0_0 : (left0Middle6 2 5) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = (rowColumnMul HexagonRowColumn625.rows_outerABC HexagonRowColumn625.cols_assocABC) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem left0Middle6_eq_case_2_5_row_0_0_1 : (left0Middle6 2 5) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = (rowColumnMul HexagonRowColumn625.rows_outerABC HexagonRowColumn625.cols_assocABC) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem left0Middle6_eq_case_2_5_row_0_0_2 : (left0Middle6 2 5) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = (rowColumnMul HexagonRowColumn625.rows_outerABC HexagonRowColumn625.cols_assocABC) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem left0Middle6_eq_case_2_5_row_0_0_3 : (left0Middle6 2 5) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = (rowColumnMul HexagonRowColumn625.rows_outerABC HexagonRowColumn625.cols_assocABC) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem left0Middle6_eq_case_2_5_row_0_0_4 : (left0Middle6 2 5) ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = (rowColumnMul HexagonRowColumn625.rows_outerABC HexagonRowColumn625.cols_assocABC) ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem left0Middle6_eq_case_2_5_row_0_0_5 : (left0Middle6 2 5) ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = (rowColumnMul HexagonRowColumn625.rows_outerABC HexagonRowColumn625.cols_assocABC) ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem left0Middle6_eq_case_2_5_row_0_0_6 : (left0Middle6 2 5) ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = (rowColumnMul HexagonRowColumn625.rows_outerABC HexagonRowColumn625.cols_assocABC) ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem left0Middle6_eq_case_2_5_row_0_0_7 : (left0Middle6 2 5) ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = (rowColumnMul HexagonRowColumn625.rows_outerABC HexagonRowColumn625.cols_assocABC) ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem left0Middle6_eq_case_2_5_row_1_0_0 : (left0Middle6 2 5) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = (rowColumnMul HexagonRowColumn625.rows_outerABC HexagonRowColumn625.cols_assocABC) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem left0Middle6_eq_case_2_5_row_1_0_1 : (left0Middle6 2 5) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = (rowColumnMul HexagonRowColumn625.rows_outerABC HexagonRowColumn625.cols_assocABC) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem left0Middle6_eq_case_2_5_row_1_0_2 : (left0Middle6 2 5) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = (rowColumnMul HexagonRowColumn625.rows_outerABC HexagonRowColumn625.cols_assocABC) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem left0Middle6_eq_case_2_5_row_1_0_3 : (left0Middle6 2 5) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = (rowColumnMul HexagonRowColumn625.rows_outerABC HexagonRowColumn625.cols_assocABC) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem left0Middle6_eq_case_2_5_row_1_0_4 : (left0Middle6 2 5) ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = (rowColumnMul HexagonRowColumn625.rows_outerABC HexagonRowColumn625.cols_assocABC) ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem left0Middle6_eq_case_2_5_row_1_0_5 : (left0Middle6 2 5) ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = (rowColumnMul HexagonRowColumn625.rows_outerABC HexagonRowColumn625.cols_assocABC) ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem left0Middle6_eq_case_2_5_row_1_0_6 : (left0Middle6 2 5) ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = (rowColumnMul HexagonRowColumn625.rows_outerABC HexagonRowColumn625.cols_assocABC) ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem left0Middle6_eq_case_2_5_row_1_0_7 : (left0Middle6 2 5) ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = (rowColumnMul HexagonRowColumn625.rows_outerABC HexagonRowColumn625.cols_assocABC) ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem left0Middle6_eq_case_2_5_row_2_0_0 : (left0Middle6 2 5) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = (rowColumnMul HexagonRowColumn625.rows_outerABC HexagonRowColumn625.cols_assocABC) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem left0Middle6_eq_case_2_5_row_2_0_1 : (left0Middle6 2 5) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = (rowColumnMul HexagonRowColumn625.rows_outerABC HexagonRowColumn625.cols_assocABC) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem left0Middle6_eq_case_2_5_row_2_0_2 : (left0Middle6 2 5) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = (rowColumnMul HexagonRowColumn625.rows_outerABC HexagonRowColumn625.cols_assocABC) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem left0Middle6_eq_case_2_5_row_2_0_3 : (left0Middle6 2 5) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = (rowColumnMul HexagonRowColumn625.rows_outerABC HexagonRowColumn625.cols_assocABC) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem left0Middle6_eq_case_2_5_row_2_0_4 : (left0Middle6 2 5) ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = (rowColumnMul HexagonRowColumn625.rows_outerABC HexagonRowColumn625.cols_assocABC) ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem left0Middle6_eq_case_2_5_row_2_0_5 : (left0Middle6 2 5) ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = (rowColumnMul HexagonRowColumn625.rows_outerABC HexagonRowColumn625.cols_assocABC) ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem left0Middle6_eq_case_2_5_row_2_0_6 : (left0Middle6 2 5) ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = (rowColumnMul HexagonRowColumn625.rows_outerABC HexagonRowColumn625.cols_assocABC) ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem left0Middle6_eq_case_2_5_row_2_0_7 : (left0Middle6 2 5) ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = (rowColumnMul HexagonRowColumn625.rows_outerABC HexagonRowColumn625.cols_assocABC) ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem left0Middle6_eq_case_2_5_row_3_0_0 : (left0Middle6 2 5) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = (rowColumnMul HexagonRowColumn625.rows_outerABC HexagonRowColumn625.cols_assocABC) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem left0Middle6_eq_case_2_5_row_3_0_1 : (left0Middle6 2 5) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = (rowColumnMul HexagonRowColumn625.rows_outerABC HexagonRowColumn625.cols_assocABC) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem left0Middle6_eq_case_2_5_row_3_0_2 : (left0Middle6 2 5) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = (rowColumnMul HexagonRowColumn625.rows_outerABC HexagonRowColumn625.cols_assocABC) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem left0Middle6_eq_case_2_5_row_3_0_3 : (left0Middle6 2 5) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = (rowColumnMul HexagonRowColumn625.rows_outerABC HexagonRowColumn625.cols_assocABC) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem left0Middle6_eq_case_2_5_row_3_0_4 : (left0Middle6 2 5) ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = (rowColumnMul HexagonRowColumn625.rows_outerABC HexagonRowColumn625.cols_assocABC) ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem left0Middle6_eq_case_2_5_row_3_0_5 : (left0Middle6 2 5) ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = (rowColumnMul HexagonRowColumn625.rows_outerABC HexagonRowColumn625.cols_assocABC) ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem left0Middle6_eq_case_2_5_row_3_0_6 : (left0Middle6 2 5) ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = (rowColumnMul HexagonRowColumn625.rows_outerABC HexagonRowColumn625.cols_assocABC) ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem left0Middle6_eq_case_2_5_row_3_0_7 : (left0Middle6 2 5) ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = (rowColumnMul HexagonRowColumn625.rows_outerABC HexagonRowColumn625.cols_assocABC) ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem left0Middle6_eq_case_2_5_checked : left0Middle6 2 5 = rowColumnMul HexagonRowColumn625.rows_outerABC HexagonRowColumn625.cols_assocABC := by
  funext r
  fin_cases r
  · exact left0Middle6_eq_case_2_5_row_0_0_0
  · exact left0Middle6_eq_case_2_5_row_0_0_1
  · exact left0Middle6_eq_case_2_5_row_0_0_2
  · exact left0Middle6_eq_case_2_5_row_0_0_3
  · exact left0Middle6_eq_case_2_5_row_0_0_4
  · exact left0Middle6_eq_case_2_5_row_0_0_5
  · exact left0Middle6_eq_case_2_5_row_0_0_6
  · exact left0Middle6_eq_case_2_5_row_0_0_7
  · exact left0Middle6_eq_case_2_5_row_1_0_0
  · exact left0Middle6_eq_case_2_5_row_1_0_1
  · exact left0Middle6_eq_case_2_5_row_1_0_2
  · exact left0Middle6_eq_case_2_5_row_1_0_3
  · exact left0Middle6_eq_case_2_5_row_1_0_4
  · exact left0Middle6_eq_case_2_5_row_1_0_5
  · exact left0Middle6_eq_case_2_5_row_1_0_6
  · exact left0Middle6_eq_case_2_5_row_1_0_7
  · exact left0Middle6_eq_case_2_5_row_2_0_0
  · exact left0Middle6_eq_case_2_5_row_2_0_1
  · exact left0Middle6_eq_case_2_5_row_2_0_2
  · exact left0Middle6_eq_case_2_5_row_2_0_3
  · exact left0Middle6_eq_case_2_5_row_2_0_4
  · exact left0Middle6_eq_case_2_5_row_2_0_5
  · exact left0Middle6_eq_case_2_5_row_2_0_6
  · exact left0Middle6_eq_case_2_5_row_2_0_7
  · exact left0Middle6_eq_case_2_5_row_3_0_0
  · exact left0Middle6_eq_case_2_5_row_3_0_1
  · exact left0Middle6_eq_case_2_5_row_3_0_2
  · exact left0Middle6_eq_case_2_5_row_3_0_3
  · exact left0Middle6_eq_case_2_5_row_3_0_4
  · exact left0Middle6_eq_case_2_5_row_3_0_5
  · exact left0Middle6_eq_case_2_5_row_3_0_6
  · exact left0Middle6_eq_case_2_5_row_3_0_7

set_option backward.isDefEq.respectTransparency false in
theorem left0Middle6_eq_case_2_5 : left0Middle6 2 5 = outerRightZ 6 2 5 * associatorZ 6 2 5 := by
  simpa only [HexagonAtoms625.assocABC_eq,
    HexagonAtoms625.outerABC_eq,
    HexagonAtoms625.assocBAC_eq,
    HexagonAtoms625.innerABC_eq,
    HexagonAtoms625.innerRightABC_eq,
    HexagonAtoms625.inverseACB_eq,
    HexagonAtoms625.innerACB_eq,
    HexagonAtoms625.assocBCA_eq,
    HexagonAtoms625.innerRightBAC_eq,
    HexagonAtoms625.assocCAB_eq,
    HexagonAtoms625.outerLeftABC_eq,
    HexagonRowColumn625.product0_eq,
    HexagonRowColumn625.product1_eq,
    HexagonRowColumn625.product2_eq,
    HexagonRowColumn625.product3_eq,
    HexagonRowColumn625.product4_eq,
    HexagonRowColumn625.product5_eq,
    HexagonRowColumn625.product6_eq,
    HexagonRowColumn625.product7_eq] using left0Middle6_eq_case_2_5_checked

private theorem left1Middle6_eq_case_2_5_row_0_0_0 : (left1Middle6 2 5) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) = (HexagonAtoms625.assocBAC) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem left1Middle6_eq_case_2_5_row_0_0_1 : (left1Middle6 2 5) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) = (HexagonAtoms625.assocBAC) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem left1Middle6_eq_case_2_5_row_0_0_2 : (left1Middle6 2 5) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) = (HexagonAtoms625.assocBAC) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem left1Middle6_eq_case_2_5_row_0_0_3 : (left1Middle6 2 5) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) = (HexagonAtoms625.assocBAC) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem left1Middle6_eq_case_2_5_row_0_0_4 : (left1Middle6 2 5) ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) = (HexagonAtoms625.assocBAC) ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem left1Middle6_eq_case_2_5_row_0_0_5 : (left1Middle6 2 5) ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) = (HexagonAtoms625.assocBAC) ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem left1Middle6_eq_case_2_5_row_0_0_6 : (left1Middle6 2 5) ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) = (HexagonAtoms625.assocBAC) ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem left1Middle6_eq_case_2_5_row_0_0_7 : (left1Middle6 2 5) ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) = (HexagonAtoms625.assocBAC) ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem left1Middle6_eq_case_2_5_row_0_1_0 : (left1Middle6 2 5) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) = (HexagonAtoms625.assocBAC) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem left1Middle6_eq_case_2_5_row_0_1_1 : (left1Middle6 2 5) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) = (HexagonAtoms625.assocBAC) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem left1Middle6_eq_case_2_5_row_0_1_2 : (left1Middle6 2 5) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) = (HexagonAtoms625.assocBAC) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem left1Middle6_eq_case_2_5_row_0_1_3 : (left1Middle6 2 5) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) = (HexagonAtoms625.assocBAC) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem left1Middle6_eq_case_2_5_row_0_1_4 : (left1Middle6 2 5) ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) = (HexagonAtoms625.assocBAC) ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem left1Middle6_eq_case_2_5_row_0_1_5 : (left1Middle6 2 5) ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) = (HexagonAtoms625.assocBAC) ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem left1Middle6_eq_case_2_5_row_0_1_6 : (left1Middle6 2 5) ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) = (HexagonAtoms625.assocBAC) ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem left1Middle6_eq_case_2_5_row_0_1_7 : (left1Middle6 2 5) ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) = (HexagonAtoms625.assocBAC) ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem left1Middle6_eq_case_2_5_row_1_0_0 : (left1Middle6 2 5) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) = (HexagonAtoms625.assocBAC) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem left1Middle6_eq_case_2_5_row_1_0_1 : (left1Middle6 2 5) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) = (HexagonAtoms625.assocBAC) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem left1Middle6_eq_case_2_5_row_1_0_2 : (left1Middle6 2 5) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) = (HexagonAtoms625.assocBAC) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem left1Middle6_eq_case_2_5_row_1_0_3 : (left1Middle6 2 5) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) = (HexagonAtoms625.assocBAC) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem left1Middle6_eq_case_2_5_row_1_0_4 : (left1Middle6 2 5) ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) = (HexagonAtoms625.assocBAC) ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem left1Middle6_eq_case_2_5_row_1_0_5 : (left1Middle6 2 5) ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) = (HexagonAtoms625.assocBAC) ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem left1Middle6_eq_case_2_5_row_1_0_6 : (left1Middle6 2 5) ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) = (HexagonAtoms625.assocBAC) ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem left1Middle6_eq_case_2_5_row_1_0_7 : (left1Middle6 2 5) ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) = (HexagonAtoms625.assocBAC) ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem left1Middle6_eq_case_2_5_row_1_1_0 : (left1Middle6 2 5) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) = (HexagonAtoms625.assocBAC) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem left1Middle6_eq_case_2_5_row_1_1_1 : (left1Middle6 2 5) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) = (HexagonAtoms625.assocBAC) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem left1Middle6_eq_case_2_5_row_1_1_2 : (left1Middle6 2 5) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) = (HexagonAtoms625.assocBAC) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem left1Middle6_eq_case_2_5_row_1_1_3 : (left1Middle6 2 5) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) = (HexagonAtoms625.assocBAC) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem left1Middle6_eq_case_2_5_row_1_1_4 : (left1Middle6 2 5) ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) = (HexagonAtoms625.assocBAC) ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem left1Middle6_eq_case_2_5_row_1_1_5 : (left1Middle6 2 5) ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) = (HexagonAtoms625.assocBAC) ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem left1Middle6_eq_case_2_5_row_1_1_6 : (left1Middle6 2 5) ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) = (HexagonAtoms625.assocBAC) ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem left1Middle6_eq_case_2_5_row_1_1_7 : (left1Middle6 2 5) ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) = (HexagonAtoms625.assocBAC) ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem left1Middle6_eq_case_2_5_checked : left1Middle6 2 5 = HexagonAtoms625.assocBAC := by
  funext r
  fin_cases r
  · exact left1Middle6_eq_case_2_5_row_0_0_0
  · exact left1Middle6_eq_case_2_5_row_0_0_1
  · exact left1Middle6_eq_case_2_5_row_0_0_2
  · exact left1Middle6_eq_case_2_5_row_0_0_3
  · exact left1Middle6_eq_case_2_5_row_0_0_4
  · exact left1Middle6_eq_case_2_5_row_0_0_5
  · exact left1Middle6_eq_case_2_5_row_0_0_6
  · exact left1Middle6_eq_case_2_5_row_0_0_7
  · exact left1Middle6_eq_case_2_5_row_0_1_0
  · exact left1Middle6_eq_case_2_5_row_0_1_1
  · exact left1Middle6_eq_case_2_5_row_0_1_2
  · exact left1Middle6_eq_case_2_5_row_0_1_3
  · exact left1Middle6_eq_case_2_5_row_0_1_4
  · exact left1Middle6_eq_case_2_5_row_0_1_5
  · exact left1Middle6_eq_case_2_5_row_0_1_6
  · exact left1Middle6_eq_case_2_5_row_0_1_7
  · exact left1Middle6_eq_case_2_5_row_1_0_0
  · exact left1Middle6_eq_case_2_5_row_1_0_1
  · exact left1Middle6_eq_case_2_5_row_1_0_2
  · exact left1Middle6_eq_case_2_5_row_1_0_3
  · exact left1Middle6_eq_case_2_5_row_1_0_4
  · exact left1Middle6_eq_case_2_5_row_1_0_5
  · exact left1Middle6_eq_case_2_5_row_1_0_6
  · exact left1Middle6_eq_case_2_5_row_1_0_7
  · exact left1Middle6_eq_case_2_5_row_1_1_0
  · exact left1Middle6_eq_case_2_5_row_1_1_1
  · exact left1Middle6_eq_case_2_5_row_1_1_2
  · exact left1Middle6_eq_case_2_5_row_1_1_3
  · exact left1Middle6_eq_case_2_5_row_1_1_4
  · exact left1Middle6_eq_case_2_5_row_1_1_5
  · exact left1Middle6_eq_case_2_5_row_1_1_6
  · exact left1Middle6_eq_case_2_5_row_1_1_7

set_option backward.isDefEq.respectTransparency false in
theorem left1Middle6_eq_case_2_5 : left1Middle6 2 5 = associatorZ 2 6 5 * innerLeftZ 6 2 5 := by
  simpa only [HexagonAtoms625.assocABC_eq,
    HexagonAtoms625.outerABC_eq,
    HexagonAtoms625.assocBAC_eq,
    HexagonAtoms625.innerABC_eq,
    HexagonAtoms625.innerRightABC_eq,
    HexagonAtoms625.inverseACB_eq,
    HexagonAtoms625.innerACB_eq,
    HexagonAtoms625.assocBCA_eq,
    HexagonAtoms625.innerRightBAC_eq,
    HexagonAtoms625.assocCAB_eq,
    HexagonAtoms625.outerLeftABC_eq,
    HexagonRowColumn625.product0_eq,
    HexagonRowColumn625.product1_eq,
    HexagonRowColumn625.product2_eq,
    HexagonRowColumn625.product3_eq,
    HexagonRowColumn625.product4_eq,
    HexagonRowColumn625.product5_eq,
    HexagonRowColumn625.product6_eq,
    HexagonRowColumn625.product7_eq] using left1Middle6_eq_case_2_5_checked

private theorem right0Middle6_eq_case_2_5_row_0_0_0 : (right0Middle6 2 5) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = (HexagonAtoms625.assocABC) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem right0Middle6_eq_case_2_5_row_0_0_1 : (right0Middle6 2 5) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = (HexagonAtoms625.assocABC) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem right0Middle6_eq_case_2_5_row_0_0_2 : (right0Middle6 2 5) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = (HexagonAtoms625.assocABC) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem right0Middle6_eq_case_2_5_row_0_0_3 : (right0Middle6 2 5) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = (HexagonAtoms625.assocABC) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem right0Middle6_eq_case_2_5_row_0_0_4 : (right0Middle6 2 5) ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = (HexagonAtoms625.assocABC) ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem right0Middle6_eq_case_2_5_row_0_0_5 : (right0Middle6 2 5) ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = (HexagonAtoms625.assocABC) ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem right0Middle6_eq_case_2_5_row_0_0_6 : (right0Middle6 2 5) ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = (HexagonAtoms625.assocABC) ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem right0Middle6_eq_case_2_5_row_0_0_7 : (right0Middle6 2 5) ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = (HexagonAtoms625.assocABC) ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem right0Middle6_eq_case_2_5_row_1_0_0 : (right0Middle6 2 5) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = (HexagonAtoms625.assocABC) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem right0Middle6_eq_case_2_5_row_1_0_1 : (right0Middle6 2 5) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = (HexagonAtoms625.assocABC) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem right0Middle6_eq_case_2_5_row_1_0_2 : (right0Middle6 2 5) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = (HexagonAtoms625.assocABC) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem right0Middle6_eq_case_2_5_row_1_0_3 : (right0Middle6 2 5) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = (HexagonAtoms625.assocABC) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem right0Middle6_eq_case_2_5_row_1_0_4 : (right0Middle6 2 5) ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = (HexagonAtoms625.assocABC) ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem right0Middle6_eq_case_2_5_row_1_0_5 : (right0Middle6 2 5) ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = (HexagonAtoms625.assocABC) ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem right0Middle6_eq_case_2_5_row_1_0_6 : (right0Middle6 2 5) ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = (HexagonAtoms625.assocABC) ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem right0Middle6_eq_case_2_5_row_1_0_7 : (right0Middle6 2 5) ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = (HexagonAtoms625.assocABC) ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem right0Middle6_eq_case_2_5_row_2_0_0 : (right0Middle6 2 5) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = (HexagonAtoms625.assocABC) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem right0Middle6_eq_case_2_5_row_2_0_1 : (right0Middle6 2 5) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = (HexagonAtoms625.assocABC) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem right0Middle6_eq_case_2_5_row_2_0_2 : (right0Middle6 2 5) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = (HexagonAtoms625.assocABC) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem right0Middle6_eq_case_2_5_row_2_0_3 : (right0Middle6 2 5) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = (HexagonAtoms625.assocABC) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem right0Middle6_eq_case_2_5_row_2_0_4 : (right0Middle6 2 5) ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = (HexagonAtoms625.assocABC) ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem right0Middle6_eq_case_2_5_row_2_0_5 : (right0Middle6 2 5) ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = (HexagonAtoms625.assocABC) ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem right0Middle6_eq_case_2_5_row_2_0_6 : (right0Middle6 2 5) ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = (HexagonAtoms625.assocABC) ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem right0Middle6_eq_case_2_5_row_2_0_7 : (right0Middle6 2 5) ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = (HexagonAtoms625.assocABC) ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem right0Middle6_eq_case_2_5_row_3_0_0 : (right0Middle6 2 5) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = (HexagonAtoms625.assocABC) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem right0Middle6_eq_case_2_5_row_3_0_1 : (right0Middle6 2 5) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = (HexagonAtoms625.assocABC) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem right0Middle6_eq_case_2_5_row_3_0_2 : (right0Middle6 2 5) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = (HexagonAtoms625.assocABC) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem right0Middle6_eq_case_2_5_row_3_0_3 : (right0Middle6 2 5) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = (HexagonAtoms625.assocABC) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem right0Middle6_eq_case_2_5_row_3_0_4 : (right0Middle6 2 5) ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = (HexagonAtoms625.assocABC) ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem right0Middle6_eq_case_2_5_row_3_0_5 : (right0Middle6 2 5) ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = (HexagonAtoms625.assocABC) ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem right0Middle6_eq_case_2_5_row_3_0_6 : (right0Middle6 2 5) ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = (HexagonAtoms625.assocABC) ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem right0Middle6_eq_case_2_5_row_3_0_7 : (right0Middle6 2 5) ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = (HexagonAtoms625.assocABC) ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem right0Middle6_eq_case_2_5_checked : right0Middle6 2 5 = HexagonAtoms625.assocABC := by
  funext r
  fin_cases r
  · exact right0Middle6_eq_case_2_5_row_0_0_0
  · exact right0Middle6_eq_case_2_5_row_0_0_1
  · exact right0Middle6_eq_case_2_5_row_0_0_2
  · exact right0Middle6_eq_case_2_5_row_0_0_3
  · exact right0Middle6_eq_case_2_5_row_0_0_4
  · exact right0Middle6_eq_case_2_5_row_0_0_5
  · exact right0Middle6_eq_case_2_5_row_0_0_6
  · exact right0Middle6_eq_case_2_5_row_0_0_7
  · exact right0Middle6_eq_case_2_5_row_1_0_0
  · exact right0Middle6_eq_case_2_5_row_1_0_1
  · exact right0Middle6_eq_case_2_5_row_1_0_2
  · exact right0Middle6_eq_case_2_5_row_1_0_3
  · exact right0Middle6_eq_case_2_5_row_1_0_4
  · exact right0Middle6_eq_case_2_5_row_1_0_5
  · exact right0Middle6_eq_case_2_5_row_1_0_6
  · exact right0Middle6_eq_case_2_5_row_1_0_7
  · exact right0Middle6_eq_case_2_5_row_2_0_0
  · exact right0Middle6_eq_case_2_5_row_2_0_1
  · exact right0Middle6_eq_case_2_5_row_2_0_2
  · exact right0Middle6_eq_case_2_5_row_2_0_3
  · exact right0Middle6_eq_case_2_5_row_2_0_4
  · exact right0Middle6_eq_case_2_5_row_2_0_5
  · exact right0Middle6_eq_case_2_5_row_2_0_6
  · exact right0Middle6_eq_case_2_5_row_2_0_7
  · exact right0Middle6_eq_case_2_5_row_3_0_0
  · exact right0Middle6_eq_case_2_5_row_3_0_1
  · exact right0Middle6_eq_case_2_5_row_3_0_2
  · exact right0Middle6_eq_case_2_5_row_3_0_3
  · exact right0Middle6_eq_case_2_5_row_3_0_4
  · exact right0Middle6_eq_case_2_5_row_3_0_5
  · exact right0Middle6_eq_case_2_5_row_3_0_6
  · exact right0Middle6_eq_case_2_5_row_3_0_7

set_option backward.isDefEq.respectTransparency false in
theorem right0Middle6_eq_case_2_5 : right0Middle6 2 5 = innerRightZ 6 2 5 * associatorZ 6 2 5 := by
  simpa only [HexagonAtoms625.assocABC_eq,
    HexagonAtoms625.outerABC_eq,
    HexagonAtoms625.assocBAC_eq,
    HexagonAtoms625.innerABC_eq,
    HexagonAtoms625.innerRightABC_eq,
    HexagonAtoms625.inverseACB_eq,
    HexagonAtoms625.innerACB_eq,
    HexagonAtoms625.assocBCA_eq,
    HexagonAtoms625.innerRightBAC_eq,
    HexagonAtoms625.assocCAB_eq,
    HexagonAtoms625.outerLeftABC_eq,
    HexagonRowColumn625.product0_eq,
    HexagonRowColumn625.product1_eq,
    HexagonRowColumn625.product2_eq,
    HexagonRowColumn625.product3_eq,
    HexagonRowColumn625.product4_eq,
    HexagonRowColumn625.product5_eq,
    HexagonRowColumn625.product6_eq,
    HexagonRowColumn625.product7_eq] using right0Middle6_eq_case_2_5_checked

private theorem right1Middle6_eq_case_2_5_row_0_0_0 : (right1Middle6 2 5) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) = (rowColumnMul HexagonRowColumn625.rows_inverseACB HexagonRowColumn625.cols_right0) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem right1Middle6_eq_case_2_5_row_0_0_1 : (right1Middle6 2 5) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) = (rowColumnMul HexagonRowColumn625.rows_inverseACB HexagonRowColumn625.cols_right0) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem right1Middle6_eq_case_2_5_row_0_0_2 : (right1Middle6 2 5) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) = (rowColumnMul HexagonRowColumn625.rows_inverseACB HexagonRowColumn625.cols_right0) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem right1Middle6_eq_case_2_5_row_0_0_3 : (right1Middle6 2 5) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) = (rowColumnMul HexagonRowColumn625.rows_inverseACB HexagonRowColumn625.cols_right0) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem right1Middle6_eq_case_2_5_row_0_0_4 : (right1Middle6 2 5) ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) = (rowColumnMul HexagonRowColumn625.rows_inverseACB HexagonRowColumn625.cols_right0) ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem right1Middle6_eq_case_2_5_row_0_0_5 : (right1Middle6 2 5) ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) = (rowColumnMul HexagonRowColumn625.rows_inverseACB HexagonRowColumn625.cols_right0) ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem right1Middle6_eq_case_2_5_row_0_0_6 : (right1Middle6 2 5) ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) = (rowColumnMul HexagonRowColumn625.rows_inverseACB HexagonRowColumn625.cols_right0) ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem right1Middle6_eq_case_2_5_row_0_0_7 : (right1Middle6 2 5) ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) = (rowColumnMul HexagonRowColumn625.rows_inverseACB HexagonRowColumn625.cols_right0) ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem right1Middle6_eq_case_2_5_row_0_1_0 : (right1Middle6 2 5) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) = (rowColumnMul HexagonRowColumn625.rows_inverseACB HexagonRowColumn625.cols_right0) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem right1Middle6_eq_case_2_5_row_0_1_1 : (right1Middle6 2 5) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) = (rowColumnMul HexagonRowColumn625.rows_inverseACB HexagonRowColumn625.cols_right0) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem right1Middle6_eq_case_2_5_row_0_1_2 : (right1Middle6 2 5) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) = (rowColumnMul HexagonRowColumn625.rows_inverseACB HexagonRowColumn625.cols_right0) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem right1Middle6_eq_case_2_5_row_0_1_3 : (right1Middle6 2 5) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) = (rowColumnMul HexagonRowColumn625.rows_inverseACB HexagonRowColumn625.cols_right0) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem right1Middle6_eq_case_2_5_row_0_1_4 : (right1Middle6 2 5) ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) = (rowColumnMul HexagonRowColumn625.rows_inverseACB HexagonRowColumn625.cols_right0) ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem right1Middle6_eq_case_2_5_row_0_1_5 : (right1Middle6 2 5) ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) = (rowColumnMul HexagonRowColumn625.rows_inverseACB HexagonRowColumn625.cols_right0) ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem right1Middle6_eq_case_2_5_row_0_1_6 : (right1Middle6 2 5) ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) = (rowColumnMul HexagonRowColumn625.rows_inverseACB HexagonRowColumn625.cols_right0) ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem right1Middle6_eq_case_2_5_row_0_1_7 : (right1Middle6 2 5) ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) = (rowColumnMul HexagonRowColumn625.rows_inverseACB HexagonRowColumn625.cols_right0) ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem right1Middle6_eq_case_2_5_row_1_0_0 : (right1Middle6 2 5) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) = (rowColumnMul HexagonRowColumn625.rows_inverseACB HexagonRowColumn625.cols_right0) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem right1Middle6_eq_case_2_5_row_1_0_1 : (right1Middle6 2 5) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) = (rowColumnMul HexagonRowColumn625.rows_inverseACB HexagonRowColumn625.cols_right0) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem right1Middle6_eq_case_2_5_row_1_0_2 : (right1Middle6 2 5) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) = (rowColumnMul HexagonRowColumn625.rows_inverseACB HexagonRowColumn625.cols_right0) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem right1Middle6_eq_case_2_5_row_1_0_3 : (right1Middle6 2 5) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) = (rowColumnMul HexagonRowColumn625.rows_inverseACB HexagonRowColumn625.cols_right0) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem right1Middle6_eq_case_2_5_row_1_0_4 : (right1Middle6 2 5) ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) = (rowColumnMul HexagonRowColumn625.rows_inverseACB HexagonRowColumn625.cols_right0) ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem right1Middle6_eq_case_2_5_row_1_0_5 : (right1Middle6 2 5) ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) = (rowColumnMul HexagonRowColumn625.rows_inverseACB HexagonRowColumn625.cols_right0) ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem right1Middle6_eq_case_2_5_row_1_0_6 : (right1Middle6 2 5) ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) = (rowColumnMul HexagonRowColumn625.rows_inverseACB HexagonRowColumn625.cols_right0) ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem right1Middle6_eq_case_2_5_row_1_0_7 : (right1Middle6 2 5) ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) = (rowColumnMul HexagonRowColumn625.rows_inverseACB HexagonRowColumn625.cols_right0) ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem right1Middle6_eq_case_2_5_row_1_1_0 : (right1Middle6 2 5) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) = (rowColumnMul HexagonRowColumn625.rows_inverseACB HexagonRowColumn625.cols_right0) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem right1Middle6_eq_case_2_5_row_1_1_1 : (right1Middle6 2 5) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) = (rowColumnMul HexagonRowColumn625.rows_inverseACB HexagonRowColumn625.cols_right0) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem right1Middle6_eq_case_2_5_row_1_1_2 : (right1Middle6 2 5) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) = (rowColumnMul HexagonRowColumn625.rows_inverseACB HexagonRowColumn625.cols_right0) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem right1Middle6_eq_case_2_5_row_1_1_3 : (right1Middle6 2 5) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) = (rowColumnMul HexagonRowColumn625.rows_inverseACB HexagonRowColumn625.cols_right0) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem right1Middle6_eq_case_2_5_row_1_1_4 : (right1Middle6 2 5) ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) = (rowColumnMul HexagonRowColumn625.rows_inverseACB HexagonRowColumn625.cols_right0) ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem right1Middle6_eq_case_2_5_row_1_1_5 : (right1Middle6 2 5) ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) = (rowColumnMul HexagonRowColumn625.rows_inverseACB HexagonRowColumn625.cols_right0) ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem right1Middle6_eq_case_2_5_row_1_1_6 : (right1Middle6 2 5) ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) = (rowColumnMul HexagonRowColumn625.rows_inverseACB HexagonRowColumn625.cols_right0) ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem right1Middle6_eq_case_2_5_row_1_1_7 : (right1Middle6 2 5) ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) = (rowColumnMul HexagonRowColumn625.rows_inverseACB HexagonRowColumn625.cols_right0) ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem right1Middle6_eq_case_2_5_checked : right1Middle6 2 5 = rowColumnMul HexagonRowColumn625.rows_inverseACB HexagonRowColumn625.cols_right0 := by
  funext r
  fin_cases r
  · exact right1Middle6_eq_case_2_5_row_0_0_0
  · exact right1Middle6_eq_case_2_5_row_0_0_1
  · exact right1Middle6_eq_case_2_5_row_0_0_2
  · exact right1Middle6_eq_case_2_5_row_0_0_3
  · exact right1Middle6_eq_case_2_5_row_0_0_4
  · exact right1Middle6_eq_case_2_5_row_0_0_5
  · exact right1Middle6_eq_case_2_5_row_0_0_6
  · exact right1Middle6_eq_case_2_5_row_0_0_7
  · exact right1Middle6_eq_case_2_5_row_0_1_0
  · exact right1Middle6_eq_case_2_5_row_0_1_1
  · exact right1Middle6_eq_case_2_5_row_0_1_2
  · exact right1Middle6_eq_case_2_5_row_0_1_3
  · exact right1Middle6_eq_case_2_5_row_0_1_4
  · exact right1Middle6_eq_case_2_5_row_0_1_5
  · exact right1Middle6_eq_case_2_5_row_0_1_6
  · exact right1Middle6_eq_case_2_5_row_0_1_7
  · exact right1Middle6_eq_case_2_5_row_1_0_0
  · exact right1Middle6_eq_case_2_5_row_1_0_1
  · exact right1Middle6_eq_case_2_5_row_1_0_2
  · exact right1Middle6_eq_case_2_5_row_1_0_3
  · exact right1Middle6_eq_case_2_5_row_1_0_4
  · exact right1Middle6_eq_case_2_5_row_1_0_5
  · exact right1Middle6_eq_case_2_5_row_1_0_6
  · exact right1Middle6_eq_case_2_5_row_1_0_7
  · exact right1Middle6_eq_case_2_5_row_1_1_0
  · exact right1Middle6_eq_case_2_5_row_1_1_1
  · exact right1Middle6_eq_case_2_5_row_1_1_2
  · exact right1Middle6_eq_case_2_5_row_1_1_3
  · exact right1Middle6_eq_case_2_5_row_1_1_4
  · exact right1Middle6_eq_case_2_5_row_1_1_5
  · exact right1Middle6_eq_case_2_5_row_1_1_6
  · exact right1Middle6_eq_case_2_5_row_1_1_7

set_option backward.isDefEq.respectTransparency false in
theorem right1Middle6_eq_case_2_5 : right1Middle6 2 5 = associatorInverseZ 6 5 2 * right0Middle6 2 5 := by
  simpa only [HexagonAtoms625.assocABC_eq,
    HexagonAtoms625.outerABC_eq,
    HexagonAtoms625.assocBAC_eq,
    HexagonAtoms625.innerABC_eq,
    HexagonAtoms625.innerRightABC_eq,
    HexagonAtoms625.inverseACB_eq,
    HexagonAtoms625.innerACB_eq,
    HexagonAtoms625.assocBCA_eq,
    HexagonAtoms625.innerRightBAC_eq,
    HexagonAtoms625.assocCAB_eq,
    HexagonAtoms625.outerLeftABC_eq,
    HexagonRowColumn625.product0_eq,
    HexagonRowColumn625.product1_eq,
    HexagonRowColumn625.product2_eq,
    HexagonRowColumn625.product3_eq,
    HexagonRowColumn625.product4_eq,
    HexagonRowColumn625.product5_eq,
    HexagonRowColumn625.product6_eq,
    HexagonRowColumn625.product7_eq] using right1Middle6_eq_case_2_5_checked

private theorem right2Middle6_eq_case_2_5_row_0_0_0 : (right2Middle6 2 5) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) = (right1Middle6 2 5) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem right2Middle6_eq_case_2_5_row_0_0_1 : (right2Middle6 2 5) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) = (right1Middle6 2 5) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem right2Middle6_eq_case_2_5_row_0_0_2 : (right2Middle6 2 5) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) = (right1Middle6 2 5) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem right2Middle6_eq_case_2_5_row_0_0_3 : (right2Middle6 2 5) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) = (right1Middle6 2 5) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem right2Middle6_eq_case_2_5_row_0_0_4 : (right2Middle6 2 5) ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) = (right1Middle6 2 5) ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem right2Middle6_eq_case_2_5_row_0_0_5 : (right2Middle6 2 5) ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) = (right1Middle6 2 5) ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem right2Middle6_eq_case_2_5_row_0_0_6 : (right2Middle6 2 5) ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) = (right1Middle6 2 5) ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem right2Middle6_eq_case_2_5_row_0_0_7 : (right2Middle6 2 5) ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) = (right1Middle6 2 5) ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem right2Middle6_eq_case_2_5_row_0_1_0 : (right2Middle6 2 5) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) = (right1Middle6 2 5) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem right2Middle6_eq_case_2_5_row_0_1_1 : (right2Middle6 2 5) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) = (right1Middle6 2 5) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem right2Middle6_eq_case_2_5_row_0_1_2 : (right2Middle6 2 5) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) = (right1Middle6 2 5) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem right2Middle6_eq_case_2_5_row_0_1_3 : (right2Middle6 2 5) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) = (right1Middle6 2 5) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem right2Middle6_eq_case_2_5_row_0_1_4 : (right2Middle6 2 5) ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) = (right1Middle6 2 5) ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem right2Middle6_eq_case_2_5_row_0_1_5 : (right2Middle6 2 5) ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) = (right1Middle6 2 5) ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem right2Middle6_eq_case_2_5_row_0_1_6 : (right2Middle6 2 5) ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) = (right1Middle6 2 5) ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem right2Middle6_eq_case_2_5_row_0_1_7 : (right2Middle6 2 5) ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) = (right1Middle6 2 5) ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem right2Middle6_eq_case_2_5_row_1_0_0 : (right2Middle6 2 5) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) = (right1Middle6 2 5) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem right2Middle6_eq_case_2_5_row_1_0_1 : (right2Middle6 2 5) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) = (right1Middle6 2 5) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem right2Middle6_eq_case_2_5_row_1_0_2 : (right2Middle6 2 5) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) = (right1Middle6 2 5) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem right2Middle6_eq_case_2_5_row_1_0_3 : (right2Middle6 2 5) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) = (right1Middle6 2 5) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem right2Middle6_eq_case_2_5_row_1_0_4 : (right2Middle6 2 5) ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) = (right1Middle6 2 5) ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem right2Middle6_eq_case_2_5_row_1_0_5 : (right2Middle6 2 5) ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) = (right1Middle6 2 5) ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem right2Middle6_eq_case_2_5_row_1_0_6 : (right2Middle6 2 5) ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) = (right1Middle6 2 5) ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem right2Middle6_eq_case_2_5_row_1_0_7 : (right2Middle6 2 5) ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) = (right1Middle6 2 5) ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem right2Middle6_eq_case_2_5_row_1_1_0 : (right2Middle6 2 5) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) = (right1Middle6 2 5) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem right2Middle6_eq_case_2_5_row_1_1_1 : (right2Middle6 2 5) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) = (right1Middle6 2 5) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem right2Middle6_eq_case_2_5_row_1_1_2 : (right2Middle6 2 5) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) = (right1Middle6 2 5) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem right2Middle6_eq_case_2_5_row_1_1_3 : (right2Middle6 2 5) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) = (right1Middle6 2 5) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem right2Middle6_eq_case_2_5_row_1_1_4 : (right2Middle6 2 5) ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) = (right1Middle6 2 5) ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem right2Middle6_eq_case_2_5_row_1_1_5 : (right2Middle6 2 5) ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) = (right1Middle6 2 5) ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem right2Middle6_eq_case_2_5_row_1_1_6 : (right2Middle6 2 5) ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) = (right1Middle6 2 5) ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem right2Middle6_eq_case_2_5_row_1_1_7 : (right2Middle6 2 5) ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) = (right1Middle6 2 5) ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem right2Middle6_eq_case_2_5_checked : right2Middle6 2 5 = right1Middle6 2 5 := by
  funext r
  fin_cases r
  · exact right2Middle6_eq_case_2_5_row_0_0_0
  · exact right2Middle6_eq_case_2_5_row_0_0_1
  · exact right2Middle6_eq_case_2_5_row_0_0_2
  · exact right2Middle6_eq_case_2_5_row_0_0_3
  · exact right2Middle6_eq_case_2_5_row_0_0_4
  · exact right2Middle6_eq_case_2_5_row_0_0_5
  · exact right2Middle6_eq_case_2_5_row_0_0_6
  · exact right2Middle6_eq_case_2_5_row_0_0_7
  · exact right2Middle6_eq_case_2_5_row_0_1_0
  · exact right2Middle6_eq_case_2_5_row_0_1_1
  · exact right2Middle6_eq_case_2_5_row_0_1_2
  · exact right2Middle6_eq_case_2_5_row_0_1_3
  · exact right2Middle6_eq_case_2_5_row_0_1_4
  · exact right2Middle6_eq_case_2_5_row_0_1_5
  · exact right2Middle6_eq_case_2_5_row_0_1_6
  · exact right2Middle6_eq_case_2_5_row_0_1_7
  · exact right2Middle6_eq_case_2_5_row_1_0_0
  · exact right2Middle6_eq_case_2_5_row_1_0_1
  · exact right2Middle6_eq_case_2_5_row_1_0_2
  · exact right2Middle6_eq_case_2_5_row_1_0_3
  · exact right2Middle6_eq_case_2_5_row_1_0_4
  · exact right2Middle6_eq_case_2_5_row_1_0_5
  · exact right2Middle6_eq_case_2_5_row_1_0_6
  · exact right2Middle6_eq_case_2_5_row_1_0_7
  · exact right2Middle6_eq_case_2_5_row_1_1_0
  · exact right2Middle6_eq_case_2_5_row_1_1_1
  · exact right2Middle6_eq_case_2_5_row_1_1_2
  · exact right2Middle6_eq_case_2_5_row_1_1_3
  · exact right2Middle6_eq_case_2_5_row_1_1_4
  · exact right2Middle6_eq_case_2_5_row_1_1_5
  · exact right2Middle6_eq_case_2_5_row_1_1_6
  · exact right2Middle6_eq_case_2_5_row_1_1_7

set_option backward.isDefEq.respectTransparency false in
theorem right2Middle6_eq_case_2_5 : right2Middle6 2 5 = innerLeftZ 6 5 2 * right1Middle6 2 5 := by
  simpa only [HexagonAtoms625.assocABC_eq,
    HexagonAtoms625.outerABC_eq,
    HexagonAtoms625.assocBAC_eq,
    HexagonAtoms625.innerABC_eq,
    HexagonAtoms625.innerRightABC_eq,
    HexagonAtoms625.inverseACB_eq,
    HexagonAtoms625.innerACB_eq,
    HexagonAtoms625.assocBCA_eq,
    HexagonAtoms625.innerRightBAC_eq,
    HexagonAtoms625.assocCAB_eq,
    HexagonAtoms625.outerLeftABC_eq,
    HexagonRowColumn625.product0_eq,
    HexagonRowColumn625.product1_eq,
    HexagonRowColumn625.product2_eq,
    HexagonRowColumn625.product3_eq,
    HexagonRowColumn625.product4_eq,
    HexagonRowColumn625.product5_eq,
    HexagonRowColumn625.product6_eq,
    HexagonRowColumn625.product7_eq] using right2Middle6_eq_case_2_5_checked

private theorem leftFinal6_case_2_5_row_0_0_0 : (((-1 : ℤ) ^ (leftScaleBit 6 2 5).val * positiveScale (leftScaleExponent 6 2 5)) •
      (rowColumnMul HexagonRowColumn625.rows_assocBCA HexagonRowColumn625.cols_left0)) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) = (negativeScale (leftScaleExponent 6 2 5) • (left1Middle6 2 5)) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem leftFinal6_case_2_5_row_0_0_1 : (((-1 : ℤ) ^ (leftScaleBit 6 2 5).val * positiveScale (leftScaleExponent 6 2 5)) •
      (rowColumnMul HexagonRowColumn625.rows_assocBCA HexagonRowColumn625.cols_left0)) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) = (negativeScale (leftScaleExponent 6 2 5) • (left1Middle6 2 5)) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem leftFinal6_case_2_5_row_0_0_2 : (((-1 : ℤ) ^ (leftScaleBit 6 2 5).val * positiveScale (leftScaleExponent 6 2 5)) •
      (rowColumnMul HexagonRowColumn625.rows_assocBCA HexagonRowColumn625.cols_left0)) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) = (negativeScale (leftScaleExponent 6 2 5) • (left1Middle6 2 5)) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem leftFinal6_case_2_5_row_0_0_3 : (((-1 : ℤ) ^ (leftScaleBit 6 2 5).val * positiveScale (leftScaleExponent 6 2 5)) •
      (rowColumnMul HexagonRowColumn625.rows_assocBCA HexagonRowColumn625.cols_left0)) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) = (negativeScale (leftScaleExponent 6 2 5) • (left1Middle6 2 5)) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem leftFinal6_case_2_5_row_0_0_4 : (((-1 : ℤ) ^ (leftScaleBit 6 2 5).val * positiveScale (leftScaleExponent 6 2 5)) •
      (rowColumnMul HexagonRowColumn625.rows_assocBCA HexagonRowColumn625.cols_left0)) ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) = (negativeScale (leftScaleExponent 6 2 5) • (left1Middle6 2 5)) ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem leftFinal6_case_2_5_row_0_0_5 : (((-1 : ℤ) ^ (leftScaleBit 6 2 5).val * positiveScale (leftScaleExponent 6 2 5)) •
      (rowColumnMul HexagonRowColumn625.rows_assocBCA HexagonRowColumn625.cols_left0)) ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) = (negativeScale (leftScaleExponent 6 2 5) • (left1Middle6 2 5)) ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem leftFinal6_case_2_5_row_0_0_6 : (((-1 : ℤ) ^ (leftScaleBit 6 2 5).val * positiveScale (leftScaleExponent 6 2 5)) •
      (rowColumnMul HexagonRowColumn625.rows_assocBCA HexagonRowColumn625.cols_left0)) ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) = (negativeScale (leftScaleExponent 6 2 5) • (left1Middle6 2 5)) ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem leftFinal6_case_2_5_row_0_0_7 : (((-1 : ℤ) ^ (leftScaleBit 6 2 5).val * positiveScale (leftScaleExponent 6 2 5)) •
      (rowColumnMul HexagonRowColumn625.rows_assocBCA HexagonRowColumn625.cols_left0)) ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) = (negativeScale (leftScaleExponent 6 2 5) • (left1Middle6 2 5)) ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem leftFinal6_case_2_5_row_0_1_0 : (((-1 : ℤ) ^ (leftScaleBit 6 2 5).val * positiveScale (leftScaleExponent 6 2 5)) •
      (rowColumnMul HexagonRowColumn625.rows_assocBCA HexagonRowColumn625.cols_left0)) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) = (negativeScale (leftScaleExponent 6 2 5) • (left1Middle6 2 5)) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem leftFinal6_case_2_5_row_0_1_1 : (((-1 : ℤ) ^ (leftScaleBit 6 2 5).val * positiveScale (leftScaleExponent 6 2 5)) •
      (rowColumnMul HexagonRowColumn625.rows_assocBCA HexagonRowColumn625.cols_left0)) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) = (negativeScale (leftScaleExponent 6 2 5) • (left1Middle6 2 5)) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem leftFinal6_case_2_5_row_0_1_2 : (((-1 : ℤ) ^ (leftScaleBit 6 2 5).val * positiveScale (leftScaleExponent 6 2 5)) •
      (rowColumnMul HexagonRowColumn625.rows_assocBCA HexagonRowColumn625.cols_left0)) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) = (negativeScale (leftScaleExponent 6 2 5) • (left1Middle6 2 5)) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem leftFinal6_case_2_5_row_0_1_3 : (((-1 : ℤ) ^ (leftScaleBit 6 2 5).val * positiveScale (leftScaleExponent 6 2 5)) •
      (rowColumnMul HexagonRowColumn625.rows_assocBCA HexagonRowColumn625.cols_left0)) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) = (negativeScale (leftScaleExponent 6 2 5) • (left1Middle6 2 5)) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem leftFinal6_case_2_5_row_0_1_4 : (((-1 : ℤ) ^ (leftScaleBit 6 2 5).val * positiveScale (leftScaleExponent 6 2 5)) •
      (rowColumnMul HexagonRowColumn625.rows_assocBCA HexagonRowColumn625.cols_left0)) ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) = (negativeScale (leftScaleExponent 6 2 5) • (left1Middle6 2 5)) ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem leftFinal6_case_2_5_row_0_1_5 : (((-1 : ℤ) ^ (leftScaleBit 6 2 5).val * positiveScale (leftScaleExponent 6 2 5)) •
      (rowColumnMul HexagonRowColumn625.rows_assocBCA HexagonRowColumn625.cols_left0)) ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) = (negativeScale (leftScaleExponent 6 2 5) • (left1Middle6 2 5)) ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem leftFinal6_case_2_5_row_0_1_6 : (((-1 : ℤ) ^ (leftScaleBit 6 2 5).val * positiveScale (leftScaleExponent 6 2 5)) •
      (rowColumnMul HexagonRowColumn625.rows_assocBCA HexagonRowColumn625.cols_left0)) ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) = (negativeScale (leftScaleExponent 6 2 5) • (left1Middle6 2 5)) ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem leftFinal6_case_2_5_row_0_1_7 : (((-1 : ℤ) ^ (leftScaleBit 6 2 5).val * positiveScale (leftScaleExponent 6 2 5)) •
      (rowColumnMul HexagonRowColumn625.rows_assocBCA HexagonRowColumn625.cols_left0)) ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) = (negativeScale (leftScaleExponent 6 2 5) • (left1Middle6 2 5)) ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem leftFinal6_case_2_5_row_1_0_0 : (((-1 : ℤ) ^ (leftScaleBit 6 2 5).val * positiveScale (leftScaleExponent 6 2 5)) •
      (rowColumnMul HexagonRowColumn625.rows_assocBCA HexagonRowColumn625.cols_left0)) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) = (negativeScale (leftScaleExponent 6 2 5) • (left1Middle6 2 5)) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem leftFinal6_case_2_5_row_1_0_1 : (((-1 : ℤ) ^ (leftScaleBit 6 2 5).val * positiveScale (leftScaleExponent 6 2 5)) •
      (rowColumnMul HexagonRowColumn625.rows_assocBCA HexagonRowColumn625.cols_left0)) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) = (negativeScale (leftScaleExponent 6 2 5) • (left1Middle6 2 5)) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem leftFinal6_case_2_5_row_1_0_2 : (((-1 : ℤ) ^ (leftScaleBit 6 2 5).val * positiveScale (leftScaleExponent 6 2 5)) •
      (rowColumnMul HexagonRowColumn625.rows_assocBCA HexagonRowColumn625.cols_left0)) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) = (negativeScale (leftScaleExponent 6 2 5) • (left1Middle6 2 5)) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem leftFinal6_case_2_5_row_1_0_3 : (((-1 : ℤ) ^ (leftScaleBit 6 2 5).val * positiveScale (leftScaleExponent 6 2 5)) •
      (rowColumnMul HexagonRowColumn625.rows_assocBCA HexagonRowColumn625.cols_left0)) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) = (negativeScale (leftScaleExponent 6 2 5) • (left1Middle6 2 5)) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem leftFinal6_case_2_5_row_1_0_4 : (((-1 : ℤ) ^ (leftScaleBit 6 2 5).val * positiveScale (leftScaleExponent 6 2 5)) •
      (rowColumnMul HexagonRowColumn625.rows_assocBCA HexagonRowColumn625.cols_left0)) ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) = (negativeScale (leftScaleExponent 6 2 5) • (left1Middle6 2 5)) ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem leftFinal6_case_2_5_row_1_0_5 : (((-1 : ℤ) ^ (leftScaleBit 6 2 5).val * positiveScale (leftScaleExponent 6 2 5)) •
      (rowColumnMul HexagonRowColumn625.rows_assocBCA HexagonRowColumn625.cols_left0)) ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) = (negativeScale (leftScaleExponent 6 2 5) • (left1Middle6 2 5)) ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem leftFinal6_case_2_5_row_1_0_6 : (((-1 : ℤ) ^ (leftScaleBit 6 2 5).val * positiveScale (leftScaleExponent 6 2 5)) •
      (rowColumnMul HexagonRowColumn625.rows_assocBCA HexagonRowColumn625.cols_left0)) ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) = (negativeScale (leftScaleExponent 6 2 5) • (left1Middle6 2 5)) ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem leftFinal6_case_2_5_row_1_0_7 : (((-1 : ℤ) ^ (leftScaleBit 6 2 5).val * positiveScale (leftScaleExponent 6 2 5)) •
      (rowColumnMul HexagonRowColumn625.rows_assocBCA HexagonRowColumn625.cols_left0)) ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) = (negativeScale (leftScaleExponent 6 2 5) • (left1Middle6 2 5)) ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem leftFinal6_case_2_5_row_1_1_0 : (((-1 : ℤ) ^ (leftScaleBit 6 2 5).val * positiveScale (leftScaleExponent 6 2 5)) •
      (rowColumnMul HexagonRowColumn625.rows_assocBCA HexagonRowColumn625.cols_left0)) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) = (negativeScale (leftScaleExponent 6 2 5) • (left1Middle6 2 5)) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem leftFinal6_case_2_5_row_1_1_1 : (((-1 : ℤ) ^ (leftScaleBit 6 2 5).val * positiveScale (leftScaleExponent 6 2 5)) •
      (rowColumnMul HexagonRowColumn625.rows_assocBCA HexagonRowColumn625.cols_left0)) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) = (negativeScale (leftScaleExponent 6 2 5) • (left1Middle6 2 5)) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem leftFinal6_case_2_5_row_1_1_2 : (((-1 : ℤ) ^ (leftScaleBit 6 2 5).val * positiveScale (leftScaleExponent 6 2 5)) •
      (rowColumnMul HexagonRowColumn625.rows_assocBCA HexagonRowColumn625.cols_left0)) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) = (negativeScale (leftScaleExponent 6 2 5) • (left1Middle6 2 5)) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem leftFinal6_case_2_5_row_1_1_3 : (((-1 : ℤ) ^ (leftScaleBit 6 2 5).val * positiveScale (leftScaleExponent 6 2 5)) •
      (rowColumnMul HexagonRowColumn625.rows_assocBCA HexagonRowColumn625.cols_left0)) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) = (negativeScale (leftScaleExponent 6 2 5) • (left1Middle6 2 5)) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem leftFinal6_case_2_5_row_1_1_4 : (((-1 : ℤ) ^ (leftScaleBit 6 2 5).val * positiveScale (leftScaleExponent 6 2 5)) •
      (rowColumnMul HexagonRowColumn625.rows_assocBCA HexagonRowColumn625.cols_left0)) ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) = (negativeScale (leftScaleExponent 6 2 5) • (left1Middle6 2 5)) ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem leftFinal6_case_2_5_row_1_1_5 : (((-1 : ℤ) ^ (leftScaleBit 6 2 5).val * positiveScale (leftScaleExponent 6 2 5)) •
      (rowColumnMul HexagonRowColumn625.rows_assocBCA HexagonRowColumn625.cols_left0)) ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) = (negativeScale (leftScaleExponent 6 2 5) • (left1Middle6 2 5)) ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem leftFinal6_case_2_5_row_1_1_6 : (((-1 : ℤ) ^ (leftScaleBit 6 2 5).val * positiveScale (leftScaleExponent 6 2 5)) •
      (rowColumnMul HexagonRowColumn625.rows_assocBCA HexagonRowColumn625.cols_left0)) ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) = (negativeScale (leftScaleExponent 6 2 5) • (left1Middle6 2 5)) ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem leftFinal6_case_2_5_row_1_1_7 : (((-1 : ℤ) ^ (leftScaleBit 6 2 5).val * positiveScale (leftScaleExponent 6 2 5)) •
      (rowColumnMul HexagonRowColumn625.rows_assocBCA HexagonRowColumn625.cols_left0)) ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) = (negativeScale (leftScaleExponent 6 2 5) • (left1Middle6 2 5)) ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem leftFinal6_case_2_5_checked : ((-1 : ℤ) ^ (leftScaleBit 6 2 5).val * positiveScale (leftScaleExponent 6 2 5)) •
      (rowColumnMul HexagonRowColumn625.rows_assocBCA HexagonRowColumn625.cols_left0) = negativeScale (leftScaleExponent 6 2 5) • (left1Middle6 2 5) := by
  funext r
  fin_cases r
  · exact leftFinal6_case_2_5_row_0_0_0
  · exact leftFinal6_case_2_5_row_0_0_1
  · exact leftFinal6_case_2_5_row_0_0_2
  · exact leftFinal6_case_2_5_row_0_0_3
  · exact leftFinal6_case_2_5_row_0_0_4
  · exact leftFinal6_case_2_5_row_0_0_5
  · exact leftFinal6_case_2_5_row_0_0_6
  · exact leftFinal6_case_2_5_row_0_0_7
  · exact leftFinal6_case_2_5_row_0_1_0
  · exact leftFinal6_case_2_5_row_0_1_1
  · exact leftFinal6_case_2_5_row_0_1_2
  · exact leftFinal6_case_2_5_row_0_1_3
  · exact leftFinal6_case_2_5_row_0_1_4
  · exact leftFinal6_case_2_5_row_0_1_5
  · exact leftFinal6_case_2_5_row_0_1_6
  · exact leftFinal6_case_2_5_row_0_1_7
  · exact leftFinal6_case_2_5_row_1_0_0
  · exact leftFinal6_case_2_5_row_1_0_1
  · exact leftFinal6_case_2_5_row_1_0_2
  · exact leftFinal6_case_2_5_row_1_0_3
  · exact leftFinal6_case_2_5_row_1_0_4
  · exact leftFinal6_case_2_5_row_1_0_5
  · exact leftFinal6_case_2_5_row_1_0_6
  · exact leftFinal6_case_2_5_row_1_0_7
  · exact leftFinal6_case_2_5_row_1_1_0
  · exact leftFinal6_case_2_5_row_1_1_1
  · exact leftFinal6_case_2_5_row_1_1_2
  · exact leftFinal6_case_2_5_row_1_1_3
  · exact leftFinal6_case_2_5_row_1_1_4
  · exact leftFinal6_case_2_5_row_1_1_5
  · exact leftFinal6_case_2_5_row_1_1_6
  · exact leftFinal6_case_2_5_row_1_1_7

set_option backward.isDefEq.respectTransparency false in
theorem leftFinal6_case_2_5 : ((-1 : ℤ) ^ (leftScaleBit 6 2 5).val * positiveScale (leftScaleExponent 6 2 5)) •
      (associatorZ 2 5 6 * left0Middle6 2 5) = negativeScale (leftScaleExponent 6 2 5) • (innerRightZ 2 6 5 * left1Middle6 2 5) := by
  simpa only [HexagonAtoms625.assocABC_eq,
    HexagonAtoms625.outerABC_eq,
    HexagonAtoms625.assocBAC_eq,
    HexagonAtoms625.innerABC_eq,
    HexagonAtoms625.innerRightABC_eq,
    HexagonAtoms625.inverseACB_eq,
    HexagonAtoms625.innerACB_eq,
    HexagonAtoms625.assocBCA_eq,
    HexagonAtoms625.innerRightBAC_eq,
    HexagonAtoms625.assocCAB_eq,
    HexagonAtoms625.outerLeftABC_eq,
    HexagonRowColumn625.product0_eq,
    HexagonRowColumn625.product1_eq,
    HexagonRowColumn625.product2_eq,
    HexagonRowColumn625.product3_eq,
    HexagonRowColumn625.product4_eq,
    HexagonRowColumn625.product5_eq,
    HexagonRowColumn625.product6_eq,
    HexagonRowColumn625.product7_eq] using leftFinal6_case_2_5_checked

private theorem rightFinal6_case_2_5_row_0_0_0 : (((-1 : ℤ) ^ (rightScaleBit 6 2 5).val * positiveScale (rightScaleExponent 6 2 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 2 : ℤ)) • HexagonAtoms625.outerLeftABC) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = (negativeScale (rightScaleExponent 6 2 5) • (rowColumnMul HexagonRowColumn625.rows_assocCAB HexagonRowColumn625.cols_right2)) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem rightFinal6_case_2_5_row_0_0_1 : (((-1 : ℤ) ^ (rightScaleBit 6 2 5).val * positiveScale (rightScaleExponent 6 2 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 2 : ℤ)) • HexagonAtoms625.outerLeftABC) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = (negativeScale (rightScaleExponent 6 2 5) • (rowColumnMul HexagonRowColumn625.rows_assocCAB HexagonRowColumn625.cols_right2)) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem rightFinal6_case_2_5_row_0_0_2 : (((-1 : ℤ) ^ (rightScaleBit 6 2 5).val * positiveScale (rightScaleExponent 6 2 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 2 : ℤ)) • HexagonAtoms625.outerLeftABC) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = (negativeScale (rightScaleExponent 6 2 5) • (rowColumnMul HexagonRowColumn625.rows_assocCAB HexagonRowColumn625.cols_right2)) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem rightFinal6_case_2_5_row_0_0_3 : (((-1 : ℤ) ^ (rightScaleBit 6 2 5).val * positiveScale (rightScaleExponent 6 2 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 2 : ℤ)) • HexagonAtoms625.outerLeftABC) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = (negativeScale (rightScaleExponent 6 2 5) • (rowColumnMul HexagonRowColumn625.rows_assocCAB HexagonRowColumn625.cols_right2)) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem rightFinal6_case_2_5_row_0_0_4 : (((-1 : ℤ) ^ (rightScaleBit 6 2 5).val * positiveScale (rightScaleExponent 6 2 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 2 : ℤ)) • HexagonAtoms625.outerLeftABC) ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = (negativeScale (rightScaleExponent 6 2 5) • (rowColumnMul HexagonRowColumn625.rows_assocCAB HexagonRowColumn625.cols_right2)) ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem rightFinal6_case_2_5_row_0_0_5 : (((-1 : ℤ) ^ (rightScaleBit 6 2 5).val * positiveScale (rightScaleExponent 6 2 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 2 : ℤ)) • HexagonAtoms625.outerLeftABC) ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = (negativeScale (rightScaleExponent 6 2 5) • (rowColumnMul HexagonRowColumn625.rows_assocCAB HexagonRowColumn625.cols_right2)) ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem rightFinal6_case_2_5_row_0_0_6 : (((-1 : ℤ) ^ (rightScaleBit 6 2 5).val * positiveScale (rightScaleExponent 6 2 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 2 : ℤ)) • HexagonAtoms625.outerLeftABC) ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = (negativeScale (rightScaleExponent 6 2 5) • (rowColumnMul HexagonRowColumn625.rows_assocCAB HexagonRowColumn625.cols_right2)) ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem rightFinal6_case_2_5_row_0_0_7 : (((-1 : ℤ) ^ (rightScaleBit 6 2 5).val * positiveScale (rightScaleExponent 6 2 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 2 : ℤ)) • HexagonAtoms625.outerLeftABC) ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = (negativeScale (rightScaleExponent 6 2 5) • (rowColumnMul HexagonRowColumn625.rows_assocCAB HexagonRowColumn625.cols_right2)) ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem rightFinal6_case_2_5_row_1_0_0 : (((-1 : ℤ) ^ (rightScaleBit 6 2 5).val * positiveScale (rightScaleExponent 6 2 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 2 : ℤ)) • HexagonAtoms625.outerLeftABC) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = (negativeScale (rightScaleExponent 6 2 5) • (rowColumnMul HexagonRowColumn625.rows_assocCAB HexagonRowColumn625.cols_right2)) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem rightFinal6_case_2_5_row_1_0_1 : (((-1 : ℤ) ^ (rightScaleBit 6 2 5).val * positiveScale (rightScaleExponent 6 2 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 2 : ℤ)) • HexagonAtoms625.outerLeftABC) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = (negativeScale (rightScaleExponent 6 2 5) • (rowColumnMul HexagonRowColumn625.rows_assocCAB HexagonRowColumn625.cols_right2)) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem rightFinal6_case_2_5_row_1_0_2 : (((-1 : ℤ) ^ (rightScaleBit 6 2 5).val * positiveScale (rightScaleExponent 6 2 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 2 : ℤ)) • HexagonAtoms625.outerLeftABC) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = (negativeScale (rightScaleExponent 6 2 5) • (rowColumnMul HexagonRowColumn625.rows_assocCAB HexagonRowColumn625.cols_right2)) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem rightFinal6_case_2_5_row_1_0_3 : (((-1 : ℤ) ^ (rightScaleBit 6 2 5).val * positiveScale (rightScaleExponent 6 2 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 2 : ℤ)) • HexagonAtoms625.outerLeftABC) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = (negativeScale (rightScaleExponent 6 2 5) • (rowColumnMul HexagonRowColumn625.rows_assocCAB HexagonRowColumn625.cols_right2)) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem rightFinal6_case_2_5_row_1_0_4 : (((-1 : ℤ) ^ (rightScaleBit 6 2 5).val * positiveScale (rightScaleExponent 6 2 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 2 : ℤ)) • HexagonAtoms625.outerLeftABC) ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = (negativeScale (rightScaleExponent 6 2 5) • (rowColumnMul HexagonRowColumn625.rows_assocCAB HexagonRowColumn625.cols_right2)) ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem rightFinal6_case_2_5_row_1_0_5 : (((-1 : ℤ) ^ (rightScaleBit 6 2 5).val * positiveScale (rightScaleExponent 6 2 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 2 : ℤ)) • HexagonAtoms625.outerLeftABC) ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = (negativeScale (rightScaleExponent 6 2 5) • (rowColumnMul HexagonRowColumn625.rows_assocCAB HexagonRowColumn625.cols_right2)) ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem rightFinal6_case_2_5_row_1_0_6 : (((-1 : ℤ) ^ (rightScaleBit 6 2 5).val * positiveScale (rightScaleExponent 6 2 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 2 : ℤ)) • HexagonAtoms625.outerLeftABC) ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = (negativeScale (rightScaleExponent 6 2 5) • (rowColumnMul HexagonRowColumn625.rows_assocCAB HexagonRowColumn625.cols_right2)) ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem rightFinal6_case_2_5_row_1_0_7 : (((-1 : ℤ) ^ (rightScaleBit 6 2 5).val * positiveScale (rightScaleExponent 6 2 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 2 : ℤ)) • HexagonAtoms625.outerLeftABC) ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = (negativeScale (rightScaleExponent 6 2 5) • (rowColumnMul HexagonRowColumn625.rows_assocCAB HexagonRowColumn625.cols_right2)) ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem rightFinal6_case_2_5_row_2_0_0 : (((-1 : ℤ) ^ (rightScaleBit 6 2 5).val * positiveScale (rightScaleExponent 6 2 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 2 : ℤ)) • HexagonAtoms625.outerLeftABC) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = (negativeScale (rightScaleExponent 6 2 5) • (rowColumnMul HexagonRowColumn625.rows_assocCAB HexagonRowColumn625.cols_right2)) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem rightFinal6_case_2_5_row_2_0_1 : (((-1 : ℤ) ^ (rightScaleBit 6 2 5).val * positiveScale (rightScaleExponent 6 2 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 2 : ℤ)) • HexagonAtoms625.outerLeftABC) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = (negativeScale (rightScaleExponent 6 2 5) • (rowColumnMul HexagonRowColumn625.rows_assocCAB HexagonRowColumn625.cols_right2)) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem rightFinal6_case_2_5_row_2_0_2 : (((-1 : ℤ) ^ (rightScaleBit 6 2 5).val * positiveScale (rightScaleExponent 6 2 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 2 : ℤ)) • HexagonAtoms625.outerLeftABC) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = (negativeScale (rightScaleExponent 6 2 5) • (rowColumnMul HexagonRowColumn625.rows_assocCAB HexagonRowColumn625.cols_right2)) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem rightFinal6_case_2_5_row_2_0_3 : (((-1 : ℤ) ^ (rightScaleBit 6 2 5).val * positiveScale (rightScaleExponent 6 2 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 2 : ℤ)) • HexagonAtoms625.outerLeftABC) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = (negativeScale (rightScaleExponent 6 2 5) • (rowColumnMul HexagonRowColumn625.rows_assocCAB HexagonRowColumn625.cols_right2)) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem rightFinal6_case_2_5_row_2_0_4 : (((-1 : ℤ) ^ (rightScaleBit 6 2 5).val * positiveScale (rightScaleExponent 6 2 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 2 : ℤ)) • HexagonAtoms625.outerLeftABC) ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = (negativeScale (rightScaleExponent 6 2 5) • (rowColumnMul HexagonRowColumn625.rows_assocCAB HexagonRowColumn625.cols_right2)) ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem rightFinal6_case_2_5_row_2_0_5 : (((-1 : ℤ) ^ (rightScaleBit 6 2 5).val * positiveScale (rightScaleExponent 6 2 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 2 : ℤ)) • HexagonAtoms625.outerLeftABC) ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = (negativeScale (rightScaleExponent 6 2 5) • (rowColumnMul HexagonRowColumn625.rows_assocCAB HexagonRowColumn625.cols_right2)) ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem rightFinal6_case_2_5_row_2_0_6 : (((-1 : ℤ) ^ (rightScaleBit 6 2 5).val * positiveScale (rightScaleExponent 6 2 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 2 : ℤ)) • HexagonAtoms625.outerLeftABC) ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = (negativeScale (rightScaleExponent 6 2 5) • (rowColumnMul HexagonRowColumn625.rows_assocCAB HexagonRowColumn625.cols_right2)) ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem rightFinal6_case_2_5_row_2_0_7 : (((-1 : ℤ) ^ (rightScaleBit 6 2 5).val * positiveScale (rightScaleExponent 6 2 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 2 : ℤ)) • HexagonAtoms625.outerLeftABC) ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = (negativeScale (rightScaleExponent 6 2 5) • (rowColumnMul HexagonRowColumn625.rows_assocCAB HexagonRowColumn625.cols_right2)) ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem rightFinal6_case_2_5_row_3_0_0 : (((-1 : ℤ) ^ (rightScaleBit 6 2 5).val * positiveScale (rightScaleExponent 6 2 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 2 : ℤ)) • HexagonAtoms625.outerLeftABC) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = (negativeScale (rightScaleExponent 6 2 5) • (rowColumnMul HexagonRowColumn625.rows_assocCAB HexagonRowColumn625.cols_right2)) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem rightFinal6_case_2_5_row_3_0_1 : (((-1 : ℤ) ^ (rightScaleBit 6 2 5).val * positiveScale (rightScaleExponent 6 2 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 2 : ℤ)) • HexagonAtoms625.outerLeftABC) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = (negativeScale (rightScaleExponent 6 2 5) • (rowColumnMul HexagonRowColumn625.rows_assocCAB HexagonRowColumn625.cols_right2)) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem rightFinal6_case_2_5_row_3_0_2 : (((-1 : ℤ) ^ (rightScaleBit 6 2 5).val * positiveScale (rightScaleExponent 6 2 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 2 : ℤ)) • HexagonAtoms625.outerLeftABC) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = (negativeScale (rightScaleExponent 6 2 5) • (rowColumnMul HexagonRowColumn625.rows_assocCAB HexagonRowColumn625.cols_right2)) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem rightFinal6_case_2_5_row_3_0_3 : (((-1 : ℤ) ^ (rightScaleBit 6 2 5).val * positiveScale (rightScaleExponent 6 2 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 2 : ℤ)) • HexagonAtoms625.outerLeftABC) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = (negativeScale (rightScaleExponent 6 2 5) • (rowColumnMul HexagonRowColumn625.rows_assocCAB HexagonRowColumn625.cols_right2)) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem rightFinal6_case_2_5_row_3_0_4 : (((-1 : ℤ) ^ (rightScaleBit 6 2 5).val * positiveScale (rightScaleExponent 6 2 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 2 : ℤ)) • HexagonAtoms625.outerLeftABC) ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = (negativeScale (rightScaleExponent 6 2 5) • (rowColumnMul HexagonRowColumn625.rows_assocCAB HexagonRowColumn625.cols_right2)) ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem rightFinal6_case_2_5_row_3_0_5 : (((-1 : ℤ) ^ (rightScaleBit 6 2 5).val * positiveScale (rightScaleExponent 6 2 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 2 : ℤ)) • HexagonAtoms625.outerLeftABC) ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = (negativeScale (rightScaleExponent 6 2 5) • (rowColumnMul HexagonRowColumn625.rows_assocCAB HexagonRowColumn625.cols_right2)) ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem rightFinal6_case_2_5_row_3_0_6 : (((-1 : ℤ) ^ (rightScaleBit 6 2 5).val * positiveScale (rightScaleExponent 6 2 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 2 : ℤ)) • HexagonAtoms625.outerLeftABC) ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = (negativeScale (rightScaleExponent 6 2 5) • (rowColumnMul HexagonRowColumn625.rows_assocCAB HexagonRowColumn625.cols_right2)) ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem rightFinal6_case_2_5_row_3_0_7 : (((-1 : ℤ) ^ (rightScaleBit 6 2 5).val * positiveScale (rightScaleExponent 6 2 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 2 : ℤ)) • HexagonAtoms625.outerLeftABC) ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = (negativeScale (rightScaleExponent 6 2 5) • (rowColumnMul HexagonRowColumn625.rows_assocCAB HexagonRowColumn625.cols_right2)) ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 8)
  decide +kernel

private theorem rightFinal6_case_2_5_checked : ((-1 : ℤ) ^ (rightScaleBit 6 2 5).val * positiveScale (rightScaleExponent 6 2 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 2 : ℤ)) • HexagonAtoms625.outerLeftABC = negativeScale (rightScaleExponent 6 2 5) • (rowColumnMul HexagonRowColumn625.rows_assocCAB HexagonRowColumn625.cols_right2) := by
  funext r
  fin_cases r
  · exact rightFinal6_case_2_5_row_0_0_0
  · exact rightFinal6_case_2_5_row_0_0_1
  · exact rightFinal6_case_2_5_row_0_0_2
  · exact rightFinal6_case_2_5_row_0_0_3
  · exact rightFinal6_case_2_5_row_0_0_4
  · exact rightFinal6_case_2_5_row_0_0_5
  · exact rightFinal6_case_2_5_row_0_0_6
  · exact rightFinal6_case_2_5_row_0_0_7
  · exact rightFinal6_case_2_5_row_1_0_0
  · exact rightFinal6_case_2_5_row_1_0_1
  · exact rightFinal6_case_2_5_row_1_0_2
  · exact rightFinal6_case_2_5_row_1_0_3
  · exact rightFinal6_case_2_5_row_1_0_4
  · exact rightFinal6_case_2_5_row_1_0_5
  · exact rightFinal6_case_2_5_row_1_0_6
  · exact rightFinal6_case_2_5_row_1_0_7
  · exact rightFinal6_case_2_5_row_2_0_0
  · exact rightFinal6_case_2_5_row_2_0_1
  · exact rightFinal6_case_2_5_row_2_0_2
  · exact rightFinal6_case_2_5_row_2_0_3
  · exact rightFinal6_case_2_5_row_2_0_4
  · exact rightFinal6_case_2_5_row_2_0_5
  · exact rightFinal6_case_2_5_row_2_0_6
  · exact rightFinal6_case_2_5_row_2_0_7
  · exact rightFinal6_case_2_5_row_3_0_0
  · exact rightFinal6_case_2_5_row_3_0_1
  · exact rightFinal6_case_2_5_row_3_0_2
  · exact rightFinal6_case_2_5_row_3_0_3
  · exact rightFinal6_case_2_5_row_3_0_4
  · exact rightFinal6_case_2_5_row_3_0_5
  · exact rightFinal6_case_2_5_row_3_0_6
  · exact rightFinal6_case_2_5_row_3_0_7

set_option backward.isDefEq.respectTransparency false in
theorem rightFinal6_case_2_5 : ((-1 : ℤ) ^ (rightScaleBit 6 2 5).val * positiveScale (rightScaleExponent 6 2 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 2 : ℤ)) • outerLeftZ 6 2 5 = negativeScale (rightScaleExponent 6 2 5) • (associatorZ 5 6 2 * right2Middle6 2 5) := by
  simpa only [HexagonAtoms625.assocABC_eq,
    HexagonAtoms625.outerABC_eq,
    HexagonAtoms625.assocBAC_eq,
    HexagonAtoms625.innerABC_eq,
    HexagonAtoms625.innerRightABC_eq,
    HexagonAtoms625.inverseACB_eq,
    HexagonAtoms625.innerACB_eq,
    HexagonAtoms625.assocBCA_eq,
    HexagonAtoms625.innerRightBAC_eq,
    HexagonAtoms625.assocCAB_eq,
    HexagonAtoms625.outerLeftABC_eq,
    HexagonRowColumn625.product0_eq,
    HexagonRowColumn625.product1_eq,
    HexagonRowColumn625.product2_eq,
    HexagonRowColumn625.product3_eq,
    HexagonRowColumn625.product4_eq,
    HexagonRowColumn625.product5_eq,
    HexagonRowColumn625.product6_eq,
    HexagonRowColumn625.product7_eq] using rightFinal6_case_2_5_checked

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonCases6
