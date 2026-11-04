import RMod.BrundanEllis.StackingReferenceHexagonMiddle6
import RMod.BrundanEllis.StackingReferenceSparseMatrixCheck
import RMod.BrundanEllis.StackingReferenceHexagonAtoms643
import RMod.BrundanEllis.StackingReferenceHexagonRowColumn643

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

private theorem left0Middle6_eq_case_4_3_row_0_0_0 : (left0Middle6 4 3) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = (rowColumnMul HexagonRowColumn643.rows_outerABC HexagonRowColumn643.cols_assocABC) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem left0Middle6_eq_case_4_3_row_0_0_1 : (left0Middle6 4 3) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = (rowColumnMul HexagonRowColumn643.rows_outerABC HexagonRowColumn643.cols_assocABC) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem left0Middle6_eq_case_4_3_row_0_0_2 : (left0Middle6 4 3) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = (rowColumnMul HexagonRowColumn643.rows_outerABC HexagonRowColumn643.cols_assocABC) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem left0Middle6_eq_case_4_3_row_0_0_3 : (left0Middle6 4 3) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = (rowColumnMul HexagonRowColumn643.rows_outerABC HexagonRowColumn643.cols_assocABC) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem left0Middle6_eq_case_4_3_row_0_0_4 : (left0Middle6 4 3) ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = (rowColumnMul HexagonRowColumn643.rows_outerABC HexagonRowColumn643.cols_assocABC) ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem left0Middle6_eq_case_4_3_row_0_0_5 : (left0Middle6 4 3) ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = (rowColumnMul HexagonRowColumn643.rows_outerABC HexagonRowColumn643.cols_assocABC) ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem left0Middle6_eq_case_4_3_row_0_0_6 : (left0Middle6 4 3) ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = (rowColumnMul HexagonRowColumn643.rows_outerABC HexagonRowColumn643.cols_assocABC) ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem left0Middle6_eq_case_4_3_row_0_0_7 : (left0Middle6 4 3) ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = (rowColumnMul HexagonRowColumn643.rows_outerABC HexagonRowColumn643.cols_assocABC) ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem left0Middle6_eq_case_4_3_row_1_0_0 : (left0Middle6 4 3) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = (rowColumnMul HexagonRowColumn643.rows_outerABC HexagonRowColumn643.cols_assocABC) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem left0Middle6_eq_case_4_3_row_1_0_1 : (left0Middle6 4 3) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = (rowColumnMul HexagonRowColumn643.rows_outerABC HexagonRowColumn643.cols_assocABC) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem left0Middle6_eq_case_4_3_row_1_0_2 : (left0Middle6 4 3) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = (rowColumnMul HexagonRowColumn643.rows_outerABC HexagonRowColumn643.cols_assocABC) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem left0Middle6_eq_case_4_3_row_1_0_3 : (left0Middle6 4 3) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = (rowColumnMul HexagonRowColumn643.rows_outerABC HexagonRowColumn643.cols_assocABC) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem left0Middle6_eq_case_4_3_row_1_0_4 : (left0Middle6 4 3) ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = (rowColumnMul HexagonRowColumn643.rows_outerABC HexagonRowColumn643.cols_assocABC) ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem left0Middle6_eq_case_4_3_row_1_0_5 : (left0Middle6 4 3) ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = (rowColumnMul HexagonRowColumn643.rows_outerABC HexagonRowColumn643.cols_assocABC) ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem left0Middle6_eq_case_4_3_row_1_0_6 : (left0Middle6 4 3) ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = (rowColumnMul HexagonRowColumn643.rows_outerABC HexagonRowColumn643.cols_assocABC) ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem left0Middle6_eq_case_4_3_row_1_0_7 : (left0Middle6 4 3) ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = (rowColumnMul HexagonRowColumn643.rows_outerABC HexagonRowColumn643.cols_assocABC) ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem left0Middle6_eq_case_4_3_row_2_0_0 : (left0Middle6 4 3) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = (rowColumnMul HexagonRowColumn643.rows_outerABC HexagonRowColumn643.cols_assocABC) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem left0Middle6_eq_case_4_3_row_2_0_1 : (left0Middle6 4 3) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = (rowColumnMul HexagonRowColumn643.rows_outerABC HexagonRowColumn643.cols_assocABC) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem left0Middle6_eq_case_4_3_row_2_0_2 : (left0Middle6 4 3) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = (rowColumnMul HexagonRowColumn643.rows_outerABC HexagonRowColumn643.cols_assocABC) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem left0Middle6_eq_case_4_3_row_2_0_3 : (left0Middle6 4 3) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = (rowColumnMul HexagonRowColumn643.rows_outerABC HexagonRowColumn643.cols_assocABC) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem left0Middle6_eq_case_4_3_row_2_0_4 : (left0Middle6 4 3) ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = (rowColumnMul HexagonRowColumn643.rows_outerABC HexagonRowColumn643.cols_assocABC) ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem left0Middle6_eq_case_4_3_row_2_0_5 : (left0Middle6 4 3) ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = (rowColumnMul HexagonRowColumn643.rows_outerABC HexagonRowColumn643.cols_assocABC) ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem left0Middle6_eq_case_4_3_row_2_0_6 : (left0Middle6 4 3) ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = (rowColumnMul HexagonRowColumn643.rows_outerABC HexagonRowColumn643.cols_assocABC) ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem left0Middle6_eq_case_4_3_row_2_0_7 : (left0Middle6 4 3) ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = (rowColumnMul HexagonRowColumn643.rows_outerABC HexagonRowColumn643.cols_assocABC) ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem left0Middle6_eq_case_4_3_row_3_0_0 : (left0Middle6 4 3) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = (rowColumnMul HexagonRowColumn643.rows_outerABC HexagonRowColumn643.cols_assocABC) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem left0Middle6_eq_case_4_3_row_3_0_1 : (left0Middle6 4 3) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = (rowColumnMul HexagonRowColumn643.rows_outerABC HexagonRowColumn643.cols_assocABC) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem left0Middle6_eq_case_4_3_row_3_0_2 : (left0Middle6 4 3) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = (rowColumnMul HexagonRowColumn643.rows_outerABC HexagonRowColumn643.cols_assocABC) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem left0Middle6_eq_case_4_3_row_3_0_3 : (left0Middle6 4 3) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = (rowColumnMul HexagonRowColumn643.rows_outerABC HexagonRowColumn643.cols_assocABC) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem left0Middle6_eq_case_4_3_row_3_0_4 : (left0Middle6 4 3) ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = (rowColumnMul HexagonRowColumn643.rows_outerABC HexagonRowColumn643.cols_assocABC) ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem left0Middle6_eq_case_4_3_row_3_0_5 : (left0Middle6 4 3) ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = (rowColumnMul HexagonRowColumn643.rows_outerABC HexagonRowColumn643.cols_assocABC) ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem left0Middle6_eq_case_4_3_row_3_0_6 : (left0Middle6 4 3) ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = (rowColumnMul HexagonRowColumn643.rows_outerABC HexagonRowColumn643.cols_assocABC) ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem left0Middle6_eq_case_4_3_row_3_0_7 : (left0Middle6 4 3) ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = (rowColumnMul HexagonRowColumn643.rows_outerABC HexagonRowColumn643.cols_assocABC) ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem left0Middle6_eq_case_4_3_checked : left0Middle6 4 3 = rowColumnMul HexagonRowColumn643.rows_outerABC HexagonRowColumn643.cols_assocABC := by
  funext r
  fin_cases r
  · exact left0Middle6_eq_case_4_3_row_0_0_0
  · exact left0Middle6_eq_case_4_3_row_0_0_1
  · exact left0Middle6_eq_case_4_3_row_0_0_2
  · exact left0Middle6_eq_case_4_3_row_0_0_3
  · exact left0Middle6_eq_case_4_3_row_0_0_4
  · exact left0Middle6_eq_case_4_3_row_0_0_5
  · exact left0Middle6_eq_case_4_3_row_0_0_6
  · exact left0Middle6_eq_case_4_3_row_0_0_7
  · exact left0Middle6_eq_case_4_3_row_1_0_0
  · exact left0Middle6_eq_case_4_3_row_1_0_1
  · exact left0Middle6_eq_case_4_3_row_1_0_2
  · exact left0Middle6_eq_case_4_3_row_1_0_3
  · exact left0Middle6_eq_case_4_3_row_1_0_4
  · exact left0Middle6_eq_case_4_3_row_1_0_5
  · exact left0Middle6_eq_case_4_3_row_1_0_6
  · exact left0Middle6_eq_case_4_3_row_1_0_7
  · exact left0Middle6_eq_case_4_3_row_2_0_0
  · exact left0Middle6_eq_case_4_3_row_2_0_1
  · exact left0Middle6_eq_case_4_3_row_2_0_2
  · exact left0Middle6_eq_case_4_3_row_2_0_3
  · exact left0Middle6_eq_case_4_3_row_2_0_4
  · exact left0Middle6_eq_case_4_3_row_2_0_5
  · exact left0Middle6_eq_case_4_3_row_2_0_6
  · exact left0Middle6_eq_case_4_3_row_2_0_7
  · exact left0Middle6_eq_case_4_3_row_3_0_0
  · exact left0Middle6_eq_case_4_3_row_3_0_1
  · exact left0Middle6_eq_case_4_3_row_3_0_2
  · exact left0Middle6_eq_case_4_3_row_3_0_3
  · exact left0Middle6_eq_case_4_3_row_3_0_4
  · exact left0Middle6_eq_case_4_3_row_3_0_5
  · exact left0Middle6_eq_case_4_3_row_3_0_6
  · exact left0Middle6_eq_case_4_3_row_3_0_7

set_option backward.isDefEq.respectTransparency false in
theorem left0Middle6_eq_case_4_3 : left0Middle6 4 3 = outerRightZ 6 4 3 * associatorZ 6 4 3 := by
  simpa only [HexagonAtoms643.assocABC_eq,
    HexagonAtoms643.outerABC_eq,
    HexagonAtoms643.assocBAC_eq,
    HexagonAtoms643.innerABC_eq,
    HexagonAtoms643.innerRightABC_eq,
    HexagonAtoms643.inverseACB_eq,
    HexagonAtoms643.innerACB_eq,
    HexagonAtoms643.assocBCA_eq,
    HexagonAtoms643.innerRightBAC_eq,
    HexagonAtoms643.assocCAB_eq,
    HexagonAtoms643.outerLeftABC_eq,
    HexagonRowColumn643.product0_eq,
    HexagonRowColumn643.product1_eq,
    HexagonRowColumn643.product2_eq,
    HexagonRowColumn643.product3_eq,
    HexagonRowColumn643.product4_eq,
    HexagonRowColumn643.product5_eq,
    HexagonRowColumn643.product6_eq,
    HexagonRowColumn643.product7_eq] using left0Middle6_eq_case_4_3_checked

private theorem left1Middle6_eq_case_4_3_row_0_0_0 : (left1Middle6 4 3) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = (HexagonAtoms643.assocBAC) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem left1Middle6_eq_case_4_3_row_0_0_1 : (left1Middle6 4 3) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = (HexagonAtoms643.assocBAC) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem left1Middle6_eq_case_4_3_row_0_0_2 : (left1Middle6 4 3) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = (HexagonAtoms643.assocBAC) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem left1Middle6_eq_case_4_3_row_0_0_3 : (left1Middle6 4 3) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = (HexagonAtoms643.assocBAC) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem left1Middle6_eq_case_4_3_row_0_0_4 : (left1Middle6 4 3) ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = (HexagonAtoms643.assocBAC) ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem left1Middle6_eq_case_4_3_row_0_0_5 : (left1Middle6 4 3) ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = (HexagonAtoms643.assocBAC) ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem left1Middle6_eq_case_4_3_row_0_0_6 : (left1Middle6 4 3) ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = (HexagonAtoms643.assocBAC) ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem left1Middle6_eq_case_4_3_row_0_0_7 : (left1Middle6 4 3) ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = (HexagonAtoms643.assocBAC) ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem left1Middle6_eq_case_4_3_row_1_0_0 : (left1Middle6 4 3) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = (HexagonAtoms643.assocBAC) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem left1Middle6_eq_case_4_3_row_1_0_1 : (left1Middle6 4 3) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = (HexagonAtoms643.assocBAC) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem left1Middle6_eq_case_4_3_row_1_0_2 : (left1Middle6 4 3) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = (HexagonAtoms643.assocBAC) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem left1Middle6_eq_case_4_3_row_1_0_3 : (left1Middle6 4 3) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = (HexagonAtoms643.assocBAC) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem left1Middle6_eq_case_4_3_row_1_0_4 : (left1Middle6 4 3) ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = (HexagonAtoms643.assocBAC) ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem left1Middle6_eq_case_4_3_row_1_0_5 : (left1Middle6 4 3) ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = (HexagonAtoms643.assocBAC) ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem left1Middle6_eq_case_4_3_row_1_0_6 : (left1Middle6 4 3) ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = (HexagonAtoms643.assocBAC) ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem left1Middle6_eq_case_4_3_row_1_0_7 : (left1Middle6 4 3) ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = (HexagonAtoms643.assocBAC) ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem left1Middle6_eq_case_4_3_row_2_0_0 : (left1Middle6 4 3) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = (HexagonAtoms643.assocBAC) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem left1Middle6_eq_case_4_3_row_2_0_1 : (left1Middle6 4 3) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = (HexagonAtoms643.assocBAC) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem left1Middle6_eq_case_4_3_row_2_0_2 : (left1Middle6 4 3) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = (HexagonAtoms643.assocBAC) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem left1Middle6_eq_case_4_3_row_2_0_3 : (left1Middle6 4 3) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = (HexagonAtoms643.assocBAC) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem left1Middle6_eq_case_4_3_row_2_0_4 : (left1Middle6 4 3) ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = (HexagonAtoms643.assocBAC) ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem left1Middle6_eq_case_4_3_row_2_0_5 : (left1Middle6 4 3) ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = (HexagonAtoms643.assocBAC) ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem left1Middle6_eq_case_4_3_row_2_0_6 : (left1Middle6 4 3) ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = (HexagonAtoms643.assocBAC) ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem left1Middle6_eq_case_4_3_row_2_0_7 : (left1Middle6 4 3) ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = (HexagonAtoms643.assocBAC) ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem left1Middle6_eq_case_4_3_row_3_0_0 : (left1Middle6 4 3) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = (HexagonAtoms643.assocBAC) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem left1Middle6_eq_case_4_3_row_3_0_1 : (left1Middle6 4 3) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = (HexagonAtoms643.assocBAC) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem left1Middle6_eq_case_4_3_row_3_0_2 : (left1Middle6 4 3) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = (HexagonAtoms643.assocBAC) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem left1Middle6_eq_case_4_3_row_3_0_3 : (left1Middle6 4 3) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = (HexagonAtoms643.assocBAC) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem left1Middle6_eq_case_4_3_row_3_0_4 : (left1Middle6 4 3) ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = (HexagonAtoms643.assocBAC) ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem left1Middle6_eq_case_4_3_row_3_0_5 : (left1Middle6 4 3) ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = (HexagonAtoms643.assocBAC) ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem left1Middle6_eq_case_4_3_row_3_0_6 : (left1Middle6 4 3) ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = (HexagonAtoms643.assocBAC) ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem left1Middle6_eq_case_4_3_row_3_0_7 : (left1Middle6 4 3) ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = (HexagonAtoms643.assocBAC) ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem left1Middle6_eq_case_4_3_checked : left1Middle6 4 3 = HexagonAtoms643.assocBAC := by
  funext r
  fin_cases r
  · exact left1Middle6_eq_case_4_3_row_0_0_0
  · exact left1Middle6_eq_case_4_3_row_0_0_1
  · exact left1Middle6_eq_case_4_3_row_0_0_2
  · exact left1Middle6_eq_case_4_3_row_0_0_3
  · exact left1Middle6_eq_case_4_3_row_0_0_4
  · exact left1Middle6_eq_case_4_3_row_0_0_5
  · exact left1Middle6_eq_case_4_3_row_0_0_6
  · exact left1Middle6_eq_case_4_3_row_0_0_7
  · exact left1Middle6_eq_case_4_3_row_1_0_0
  · exact left1Middle6_eq_case_4_3_row_1_0_1
  · exact left1Middle6_eq_case_4_3_row_1_0_2
  · exact left1Middle6_eq_case_4_3_row_1_0_3
  · exact left1Middle6_eq_case_4_3_row_1_0_4
  · exact left1Middle6_eq_case_4_3_row_1_0_5
  · exact left1Middle6_eq_case_4_3_row_1_0_6
  · exact left1Middle6_eq_case_4_3_row_1_0_7
  · exact left1Middle6_eq_case_4_3_row_2_0_0
  · exact left1Middle6_eq_case_4_3_row_2_0_1
  · exact left1Middle6_eq_case_4_3_row_2_0_2
  · exact left1Middle6_eq_case_4_3_row_2_0_3
  · exact left1Middle6_eq_case_4_3_row_2_0_4
  · exact left1Middle6_eq_case_4_3_row_2_0_5
  · exact left1Middle6_eq_case_4_3_row_2_0_6
  · exact left1Middle6_eq_case_4_3_row_2_0_7
  · exact left1Middle6_eq_case_4_3_row_3_0_0
  · exact left1Middle6_eq_case_4_3_row_3_0_1
  · exact left1Middle6_eq_case_4_3_row_3_0_2
  · exact left1Middle6_eq_case_4_3_row_3_0_3
  · exact left1Middle6_eq_case_4_3_row_3_0_4
  · exact left1Middle6_eq_case_4_3_row_3_0_5
  · exact left1Middle6_eq_case_4_3_row_3_0_6
  · exact left1Middle6_eq_case_4_3_row_3_0_7

set_option backward.isDefEq.respectTransparency false in
theorem left1Middle6_eq_case_4_3 : left1Middle6 4 3 = associatorZ 4 6 3 * innerLeftZ 6 4 3 := by
  simpa only [HexagonAtoms643.assocABC_eq,
    HexagonAtoms643.outerABC_eq,
    HexagonAtoms643.assocBAC_eq,
    HexagonAtoms643.innerABC_eq,
    HexagonAtoms643.innerRightABC_eq,
    HexagonAtoms643.inverseACB_eq,
    HexagonAtoms643.innerACB_eq,
    HexagonAtoms643.assocBCA_eq,
    HexagonAtoms643.innerRightBAC_eq,
    HexagonAtoms643.assocCAB_eq,
    HexagonAtoms643.outerLeftABC_eq,
    HexagonRowColumn643.product0_eq,
    HexagonRowColumn643.product1_eq,
    HexagonRowColumn643.product2_eq,
    HexagonRowColumn643.product3_eq,
    HexagonRowColumn643.product4_eq,
    HexagonRowColumn643.product5_eq,
    HexagonRowColumn643.product6_eq,
    HexagonRowColumn643.product7_eq] using left1Middle6_eq_case_4_3_checked

private theorem right0Middle6_eq_case_4_3_row_0_0_0 : (right0Middle6 4 3) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = (HexagonAtoms643.assocABC) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem right0Middle6_eq_case_4_3_row_0_0_1 : (right0Middle6 4 3) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = (HexagonAtoms643.assocABC) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem right0Middle6_eq_case_4_3_row_0_0_2 : (right0Middle6 4 3) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = (HexagonAtoms643.assocABC) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem right0Middle6_eq_case_4_3_row_0_0_3 : (right0Middle6 4 3) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = (HexagonAtoms643.assocABC) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem right0Middle6_eq_case_4_3_row_0_0_4 : (right0Middle6 4 3) ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = (HexagonAtoms643.assocABC) ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem right0Middle6_eq_case_4_3_row_0_0_5 : (right0Middle6 4 3) ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = (HexagonAtoms643.assocABC) ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem right0Middle6_eq_case_4_3_row_0_0_6 : (right0Middle6 4 3) ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = (HexagonAtoms643.assocABC) ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem right0Middle6_eq_case_4_3_row_0_0_7 : (right0Middle6 4 3) ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = (HexagonAtoms643.assocABC) ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem right0Middle6_eq_case_4_3_row_1_0_0 : (right0Middle6 4 3) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = (HexagonAtoms643.assocABC) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem right0Middle6_eq_case_4_3_row_1_0_1 : (right0Middle6 4 3) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = (HexagonAtoms643.assocABC) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem right0Middle6_eq_case_4_3_row_1_0_2 : (right0Middle6 4 3) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = (HexagonAtoms643.assocABC) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem right0Middle6_eq_case_4_3_row_1_0_3 : (right0Middle6 4 3) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = (HexagonAtoms643.assocABC) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem right0Middle6_eq_case_4_3_row_1_0_4 : (right0Middle6 4 3) ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = (HexagonAtoms643.assocABC) ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem right0Middle6_eq_case_4_3_row_1_0_5 : (right0Middle6 4 3) ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = (HexagonAtoms643.assocABC) ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem right0Middle6_eq_case_4_3_row_1_0_6 : (right0Middle6 4 3) ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = (HexagonAtoms643.assocABC) ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem right0Middle6_eq_case_4_3_row_1_0_7 : (right0Middle6 4 3) ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = (HexagonAtoms643.assocABC) ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem right0Middle6_eq_case_4_3_row_2_0_0 : (right0Middle6 4 3) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = (HexagonAtoms643.assocABC) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem right0Middle6_eq_case_4_3_row_2_0_1 : (right0Middle6 4 3) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = (HexagonAtoms643.assocABC) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem right0Middle6_eq_case_4_3_row_2_0_2 : (right0Middle6 4 3) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = (HexagonAtoms643.assocABC) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem right0Middle6_eq_case_4_3_row_2_0_3 : (right0Middle6 4 3) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = (HexagonAtoms643.assocABC) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem right0Middle6_eq_case_4_3_row_2_0_4 : (right0Middle6 4 3) ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = (HexagonAtoms643.assocABC) ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem right0Middle6_eq_case_4_3_row_2_0_5 : (right0Middle6 4 3) ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = (HexagonAtoms643.assocABC) ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem right0Middle6_eq_case_4_3_row_2_0_6 : (right0Middle6 4 3) ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = (HexagonAtoms643.assocABC) ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem right0Middle6_eq_case_4_3_row_2_0_7 : (right0Middle6 4 3) ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = (HexagonAtoms643.assocABC) ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem right0Middle6_eq_case_4_3_row_3_0_0 : (right0Middle6 4 3) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = (HexagonAtoms643.assocABC) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem right0Middle6_eq_case_4_3_row_3_0_1 : (right0Middle6 4 3) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = (HexagonAtoms643.assocABC) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem right0Middle6_eq_case_4_3_row_3_0_2 : (right0Middle6 4 3) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = (HexagonAtoms643.assocABC) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem right0Middle6_eq_case_4_3_row_3_0_3 : (right0Middle6 4 3) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = (HexagonAtoms643.assocABC) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem right0Middle6_eq_case_4_3_row_3_0_4 : (right0Middle6 4 3) ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = (HexagonAtoms643.assocABC) ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem right0Middle6_eq_case_4_3_row_3_0_5 : (right0Middle6 4 3) ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = (HexagonAtoms643.assocABC) ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem right0Middle6_eq_case_4_3_row_3_0_6 : (right0Middle6 4 3) ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = (HexagonAtoms643.assocABC) ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem right0Middle6_eq_case_4_3_row_3_0_7 : (right0Middle6 4 3) ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = (HexagonAtoms643.assocABC) ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem right0Middle6_eq_case_4_3_checked : right0Middle6 4 3 = HexagonAtoms643.assocABC := by
  funext r
  fin_cases r
  · exact right0Middle6_eq_case_4_3_row_0_0_0
  · exact right0Middle6_eq_case_4_3_row_0_0_1
  · exact right0Middle6_eq_case_4_3_row_0_0_2
  · exact right0Middle6_eq_case_4_3_row_0_0_3
  · exact right0Middle6_eq_case_4_3_row_0_0_4
  · exact right0Middle6_eq_case_4_3_row_0_0_5
  · exact right0Middle6_eq_case_4_3_row_0_0_6
  · exact right0Middle6_eq_case_4_3_row_0_0_7
  · exact right0Middle6_eq_case_4_3_row_1_0_0
  · exact right0Middle6_eq_case_4_3_row_1_0_1
  · exact right0Middle6_eq_case_4_3_row_1_0_2
  · exact right0Middle6_eq_case_4_3_row_1_0_3
  · exact right0Middle6_eq_case_4_3_row_1_0_4
  · exact right0Middle6_eq_case_4_3_row_1_0_5
  · exact right0Middle6_eq_case_4_3_row_1_0_6
  · exact right0Middle6_eq_case_4_3_row_1_0_7
  · exact right0Middle6_eq_case_4_3_row_2_0_0
  · exact right0Middle6_eq_case_4_3_row_2_0_1
  · exact right0Middle6_eq_case_4_3_row_2_0_2
  · exact right0Middle6_eq_case_4_3_row_2_0_3
  · exact right0Middle6_eq_case_4_3_row_2_0_4
  · exact right0Middle6_eq_case_4_3_row_2_0_5
  · exact right0Middle6_eq_case_4_3_row_2_0_6
  · exact right0Middle6_eq_case_4_3_row_2_0_7
  · exact right0Middle6_eq_case_4_3_row_3_0_0
  · exact right0Middle6_eq_case_4_3_row_3_0_1
  · exact right0Middle6_eq_case_4_3_row_3_0_2
  · exact right0Middle6_eq_case_4_3_row_3_0_3
  · exact right0Middle6_eq_case_4_3_row_3_0_4
  · exact right0Middle6_eq_case_4_3_row_3_0_5
  · exact right0Middle6_eq_case_4_3_row_3_0_6
  · exact right0Middle6_eq_case_4_3_row_3_0_7

set_option backward.isDefEq.respectTransparency false in
theorem right0Middle6_eq_case_4_3 : right0Middle6 4 3 = innerRightZ 6 4 3 * associatorZ 6 4 3 := by
  simpa only [HexagonAtoms643.assocABC_eq,
    HexagonAtoms643.outerABC_eq,
    HexagonAtoms643.assocBAC_eq,
    HexagonAtoms643.innerABC_eq,
    HexagonAtoms643.innerRightABC_eq,
    HexagonAtoms643.inverseACB_eq,
    HexagonAtoms643.innerACB_eq,
    HexagonAtoms643.assocBCA_eq,
    HexagonAtoms643.innerRightBAC_eq,
    HexagonAtoms643.assocCAB_eq,
    HexagonAtoms643.outerLeftABC_eq,
    HexagonRowColumn643.product0_eq,
    HexagonRowColumn643.product1_eq,
    HexagonRowColumn643.product2_eq,
    HexagonRowColumn643.product3_eq,
    HexagonRowColumn643.product4_eq,
    HexagonRowColumn643.product5_eq,
    HexagonRowColumn643.product6_eq,
    HexagonRowColumn643.product7_eq] using right0Middle6_eq_case_4_3_checked

private theorem right1Middle6_eq_case_4_3_row_0_0_0 : (right1Middle6 4 3) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = (rowColumnMul HexagonRowColumn643.rows_inverseACB HexagonRowColumn643.cols_right0) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem right1Middle6_eq_case_4_3_row_0_0_1 : (right1Middle6 4 3) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = (rowColumnMul HexagonRowColumn643.rows_inverseACB HexagonRowColumn643.cols_right0) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem right1Middle6_eq_case_4_3_row_0_0_2 : (right1Middle6 4 3) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = (rowColumnMul HexagonRowColumn643.rows_inverseACB HexagonRowColumn643.cols_right0) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem right1Middle6_eq_case_4_3_row_0_0_3 : (right1Middle6 4 3) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = (rowColumnMul HexagonRowColumn643.rows_inverseACB HexagonRowColumn643.cols_right0) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem right1Middle6_eq_case_4_3_row_0_0_4 : (right1Middle6 4 3) ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = (rowColumnMul HexagonRowColumn643.rows_inverseACB HexagonRowColumn643.cols_right0) ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem right1Middle6_eq_case_4_3_row_0_0_5 : (right1Middle6 4 3) ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = (rowColumnMul HexagonRowColumn643.rows_inverseACB HexagonRowColumn643.cols_right0) ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem right1Middle6_eq_case_4_3_row_0_0_6 : (right1Middle6 4 3) ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = (rowColumnMul HexagonRowColumn643.rows_inverseACB HexagonRowColumn643.cols_right0) ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem right1Middle6_eq_case_4_3_row_0_0_7 : (right1Middle6 4 3) ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = (rowColumnMul HexagonRowColumn643.rows_inverseACB HexagonRowColumn643.cols_right0) ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem right1Middle6_eq_case_4_3_row_1_0_0 : (right1Middle6 4 3) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = (rowColumnMul HexagonRowColumn643.rows_inverseACB HexagonRowColumn643.cols_right0) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem right1Middle6_eq_case_4_3_row_1_0_1 : (right1Middle6 4 3) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = (rowColumnMul HexagonRowColumn643.rows_inverseACB HexagonRowColumn643.cols_right0) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem right1Middle6_eq_case_4_3_row_1_0_2 : (right1Middle6 4 3) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = (rowColumnMul HexagonRowColumn643.rows_inverseACB HexagonRowColumn643.cols_right0) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem right1Middle6_eq_case_4_3_row_1_0_3 : (right1Middle6 4 3) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = (rowColumnMul HexagonRowColumn643.rows_inverseACB HexagonRowColumn643.cols_right0) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem right1Middle6_eq_case_4_3_row_1_0_4 : (right1Middle6 4 3) ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = (rowColumnMul HexagonRowColumn643.rows_inverseACB HexagonRowColumn643.cols_right0) ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem right1Middle6_eq_case_4_3_row_1_0_5 : (right1Middle6 4 3) ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = (rowColumnMul HexagonRowColumn643.rows_inverseACB HexagonRowColumn643.cols_right0) ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem right1Middle6_eq_case_4_3_row_1_0_6 : (right1Middle6 4 3) ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = (rowColumnMul HexagonRowColumn643.rows_inverseACB HexagonRowColumn643.cols_right0) ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem right1Middle6_eq_case_4_3_row_1_0_7 : (right1Middle6 4 3) ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = (rowColumnMul HexagonRowColumn643.rows_inverseACB HexagonRowColumn643.cols_right0) ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem right1Middle6_eq_case_4_3_row_2_0_0 : (right1Middle6 4 3) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = (rowColumnMul HexagonRowColumn643.rows_inverseACB HexagonRowColumn643.cols_right0) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem right1Middle6_eq_case_4_3_row_2_0_1 : (right1Middle6 4 3) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = (rowColumnMul HexagonRowColumn643.rows_inverseACB HexagonRowColumn643.cols_right0) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem right1Middle6_eq_case_4_3_row_2_0_2 : (right1Middle6 4 3) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = (rowColumnMul HexagonRowColumn643.rows_inverseACB HexagonRowColumn643.cols_right0) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem right1Middle6_eq_case_4_3_row_2_0_3 : (right1Middle6 4 3) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = (rowColumnMul HexagonRowColumn643.rows_inverseACB HexagonRowColumn643.cols_right0) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem right1Middle6_eq_case_4_3_row_2_0_4 : (right1Middle6 4 3) ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = (rowColumnMul HexagonRowColumn643.rows_inverseACB HexagonRowColumn643.cols_right0) ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem right1Middle6_eq_case_4_3_row_2_0_5 : (right1Middle6 4 3) ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = (rowColumnMul HexagonRowColumn643.rows_inverseACB HexagonRowColumn643.cols_right0) ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem right1Middle6_eq_case_4_3_row_2_0_6 : (right1Middle6 4 3) ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = (rowColumnMul HexagonRowColumn643.rows_inverseACB HexagonRowColumn643.cols_right0) ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem right1Middle6_eq_case_4_3_row_2_0_7 : (right1Middle6 4 3) ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = (rowColumnMul HexagonRowColumn643.rows_inverseACB HexagonRowColumn643.cols_right0) ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem right1Middle6_eq_case_4_3_row_3_0_0 : (right1Middle6 4 3) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = (rowColumnMul HexagonRowColumn643.rows_inverseACB HexagonRowColumn643.cols_right0) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem right1Middle6_eq_case_4_3_row_3_0_1 : (right1Middle6 4 3) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = (rowColumnMul HexagonRowColumn643.rows_inverseACB HexagonRowColumn643.cols_right0) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem right1Middle6_eq_case_4_3_row_3_0_2 : (right1Middle6 4 3) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = (rowColumnMul HexagonRowColumn643.rows_inverseACB HexagonRowColumn643.cols_right0) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem right1Middle6_eq_case_4_3_row_3_0_3 : (right1Middle6 4 3) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = (rowColumnMul HexagonRowColumn643.rows_inverseACB HexagonRowColumn643.cols_right0) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem right1Middle6_eq_case_4_3_row_3_0_4 : (right1Middle6 4 3) ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = (rowColumnMul HexagonRowColumn643.rows_inverseACB HexagonRowColumn643.cols_right0) ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem right1Middle6_eq_case_4_3_row_3_0_5 : (right1Middle6 4 3) ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = (rowColumnMul HexagonRowColumn643.rows_inverseACB HexagonRowColumn643.cols_right0) ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem right1Middle6_eq_case_4_3_row_3_0_6 : (right1Middle6 4 3) ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = (rowColumnMul HexagonRowColumn643.rows_inverseACB HexagonRowColumn643.cols_right0) ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem right1Middle6_eq_case_4_3_row_3_0_7 : (right1Middle6 4 3) ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = (rowColumnMul HexagonRowColumn643.rows_inverseACB HexagonRowColumn643.cols_right0) ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem right1Middle6_eq_case_4_3_checked : right1Middle6 4 3 = rowColumnMul HexagonRowColumn643.rows_inverseACB HexagonRowColumn643.cols_right0 := by
  funext r
  fin_cases r
  · exact right1Middle6_eq_case_4_3_row_0_0_0
  · exact right1Middle6_eq_case_4_3_row_0_0_1
  · exact right1Middle6_eq_case_4_3_row_0_0_2
  · exact right1Middle6_eq_case_4_3_row_0_0_3
  · exact right1Middle6_eq_case_4_3_row_0_0_4
  · exact right1Middle6_eq_case_4_3_row_0_0_5
  · exact right1Middle6_eq_case_4_3_row_0_0_6
  · exact right1Middle6_eq_case_4_3_row_0_0_7
  · exact right1Middle6_eq_case_4_3_row_1_0_0
  · exact right1Middle6_eq_case_4_3_row_1_0_1
  · exact right1Middle6_eq_case_4_3_row_1_0_2
  · exact right1Middle6_eq_case_4_3_row_1_0_3
  · exact right1Middle6_eq_case_4_3_row_1_0_4
  · exact right1Middle6_eq_case_4_3_row_1_0_5
  · exact right1Middle6_eq_case_4_3_row_1_0_6
  · exact right1Middle6_eq_case_4_3_row_1_0_7
  · exact right1Middle6_eq_case_4_3_row_2_0_0
  · exact right1Middle6_eq_case_4_3_row_2_0_1
  · exact right1Middle6_eq_case_4_3_row_2_0_2
  · exact right1Middle6_eq_case_4_3_row_2_0_3
  · exact right1Middle6_eq_case_4_3_row_2_0_4
  · exact right1Middle6_eq_case_4_3_row_2_0_5
  · exact right1Middle6_eq_case_4_3_row_2_0_6
  · exact right1Middle6_eq_case_4_3_row_2_0_7
  · exact right1Middle6_eq_case_4_3_row_3_0_0
  · exact right1Middle6_eq_case_4_3_row_3_0_1
  · exact right1Middle6_eq_case_4_3_row_3_0_2
  · exact right1Middle6_eq_case_4_3_row_3_0_3
  · exact right1Middle6_eq_case_4_3_row_3_0_4
  · exact right1Middle6_eq_case_4_3_row_3_0_5
  · exact right1Middle6_eq_case_4_3_row_3_0_6
  · exact right1Middle6_eq_case_4_3_row_3_0_7

set_option backward.isDefEq.respectTransparency false in
theorem right1Middle6_eq_case_4_3 : right1Middle6 4 3 = associatorInverseZ 6 3 4 * right0Middle6 4 3 := by
  simpa only [HexagonAtoms643.assocABC_eq,
    HexagonAtoms643.outerABC_eq,
    HexagonAtoms643.assocBAC_eq,
    HexagonAtoms643.innerABC_eq,
    HexagonAtoms643.innerRightABC_eq,
    HexagonAtoms643.inverseACB_eq,
    HexagonAtoms643.innerACB_eq,
    HexagonAtoms643.assocBCA_eq,
    HexagonAtoms643.innerRightBAC_eq,
    HexagonAtoms643.assocCAB_eq,
    HexagonAtoms643.outerLeftABC_eq,
    HexagonRowColumn643.product0_eq,
    HexagonRowColumn643.product1_eq,
    HexagonRowColumn643.product2_eq,
    HexagonRowColumn643.product3_eq,
    HexagonRowColumn643.product4_eq,
    HexagonRowColumn643.product5_eq,
    HexagonRowColumn643.product6_eq,
    HexagonRowColumn643.product7_eq] using right1Middle6_eq_case_4_3_checked

private theorem right2Middle6_eq_case_4_3_row_0_0_0 : (right2Middle6 4 3) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = (right1Middle6 4 3) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem right2Middle6_eq_case_4_3_row_0_0_1 : (right2Middle6 4 3) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = (right1Middle6 4 3) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem right2Middle6_eq_case_4_3_row_0_0_2 : (right2Middle6 4 3) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = (right1Middle6 4 3) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem right2Middle6_eq_case_4_3_row_0_0_3 : (right2Middle6 4 3) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = (right1Middle6 4 3) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem right2Middle6_eq_case_4_3_row_0_0_4 : (right2Middle6 4 3) ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = (right1Middle6 4 3) ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem right2Middle6_eq_case_4_3_row_0_0_5 : (right2Middle6 4 3) ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = (right1Middle6 4 3) ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem right2Middle6_eq_case_4_3_row_0_0_6 : (right2Middle6 4 3) ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = (right1Middle6 4 3) ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem right2Middle6_eq_case_4_3_row_0_0_7 : (right2Middle6 4 3) ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = (right1Middle6 4 3) ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem right2Middle6_eq_case_4_3_row_1_0_0 : (right2Middle6 4 3) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = (right1Middle6 4 3) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem right2Middle6_eq_case_4_3_row_1_0_1 : (right2Middle6 4 3) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = (right1Middle6 4 3) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem right2Middle6_eq_case_4_3_row_1_0_2 : (right2Middle6 4 3) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = (right1Middle6 4 3) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem right2Middle6_eq_case_4_3_row_1_0_3 : (right2Middle6 4 3) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = (right1Middle6 4 3) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem right2Middle6_eq_case_4_3_row_1_0_4 : (right2Middle6 4 3) ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = (right1Middle6 4 3) ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem right2Middle6_eq_case_4_3_row_1_0_5 : (right2Middle6 4 3) ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = (right1Middle6 4 3) ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem right2Middle6_eq_case_4_3_row_1_0_6 : (right2Middle6 4 3) ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = (right1Middle6 4 3) ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem right2Middle6_eq_case_4_3_row_1_0_7 : (right2Middle6 4 3) ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = (right1Middle6 4 3) ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem right2Middle6_eq_case_4_3_row_2_0_0 : (right2Middle6 4 3) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = (right1Middle6 4 3) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem right2Middle6_eq_case_4_3_row_2_0_1 : (right2Middle6 4 3) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = (right1Middle6 4 3) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem right2Middle6_eq_case_4_3_row_2_0_2 : (right2Middle6 4 3) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = (right1Middle6 4 3) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem right2Middle6_eq_case_4_3_row_2_0_3 : (right2Middle6 4 3) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = (right1Middle6 4 3) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem right2Middle6_eq_case_4_3_row_2_0_4 : (right2Middle6 4 3) ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = (right1Middle6 4 3) ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem right2Middle6_eq_case_4_3_row_2_0_5 : (right2Middle6 4 3) ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = (right1Middle6 4 3) ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem right2Middle6_eq_case_4_3_row_2_0_6 : (right2Middle6 4 3) ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = (right1Middle6 4 3) ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem right2Middle6_eq_case_4_3_row_2_0_7 : (right2Middle6 4 3) ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = (right1Middle6 4 3) ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem right2Middle6_eq_case_4_3_row_3_0_0 : (right2Middle6 4 3) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = (right1Middle6 4 3) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem right2Middle6_eq_case_4_3_row_3_0_1 : (right2Middle6 4 3) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = (right1Middle6 4 3) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem right2Middle6_eq_case_4_3_row_3_0_2 : (right2Middle6 4 3) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = (right1Middle6 4 3) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem right2Middle6_eq_case_4_3_row_3_0_3 : (right2Middle6 4 3) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = (right1Middle6 4 3) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem right2Middle6_eq_case_4_3_row_3_0_4 : (right2Middle6 4 3) ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = (right1Middle6 4 3) ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem right2Middle6_eq_case_4_3_row_3_0_5 : (right2Middle6 4 3) ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = (right1Middle6 4 3) ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem right2Middle6_eq_case_4_3_row_3_0_6 : (right2Middle6 4 3) ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = (right1Middle6 4 3) ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem right2Middle6_eq_case_4_3_row_3_0_7 : (right2Middle6 4 3) ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = (right1Middle6 4 3) ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem right2Middle6_eq_case_4_3_checked : right2Middle6 4 3 = right1Middle6 4 3 := by
  funext r
  fin_cases r
  · exact right2Middle6_eq_case_4_3_row_0_0_0
  · exact right2Middle6_eq_case_4_3_row_0_0_1
  · exact right2Middle6_eq_case_4_3_row_0_0_2
  · exact right2Middle6_eq_case_4_3_row_0_0_3
  · exact right2Middle6_eq_case_4_3_row_0_0_4
  · exact right2Middle6_eq_case_4_3_row_0_0_5
  · exact right2Middle6_eq_case_4_3_row_0_0_6
  · exact right2Middle6_eq_case_4_3_row_0_0_7
  · exact right2Middle6_eq_case_4_3_row_1_0_0
  · exact right2Middle6_eq_case_4_3_row_1_0_1
  · exact right2Middle6_eq_case_4_3_row_1_0_2
  · exact right2Middle6_eq_case_4_3_row_1_0_3
  · exact right2Middle6_eq_case_4_3_row_1_0_4
  · exact right2Middle6_eq_case_4_3_row_1_0_5
  · exact right2Middle6_eq_case_4_3_row_1_0_6
  · exact right2Middle6_eq_case_4_3_row_1_0_7
  · exact right2Middle6_eq_case_4_3_row_2_0_0
  · exact right2Middle6_eq_case_4_3_row_2_0_1
  · exact right2Middle6_eq_case_4_3_row_2_0_2
  · exact right2Middle6_eq_case_4_3_row_2_0_3
  · exact right2Middle6_eq_case_4_3_row_2_0_4
  · exact right2Middle6_eq_case_4_3_row_2_0_5
  · exact right2Middle6_eq_case_4_3_row_2_0_6
  · exact right2Middle6_eq_case_4_3_row_2_0_7
  · exact right2Middle6_eq_case_4_3_row_3_0_0
  · exact right2Middle6_eq_case_4_3_row_3_0_1
  · exact right2Middle6_eq_case_4_3_row_3_0_2
  · exact right2Middle6_eq_case_4_3_row_3_0_3
  · exact right2Middle6_eq_case_4_3_row_3_0_4
  · exact right2Middle6_eq_case_4_3_row_3_0_5
  · exact right2Middle6_eq_case_4_3_row_3_0_6
  · exact right2Middle6_eq_case_4_3_row_3_0_7

set_option backward.isDefEq.respectTransparency false in
theorem right2Middle6_eq_case_4_3 : right2Middle6 4 3 = innerLeftZ 6 3 4 * right1Middle6 4 3 := by
  simpa only [HexagonAtoms643.assocABC_eq,
    HexagonAtoms643.outerABC_eq,
    HexagonAtoms643.assocBAC_eq,
    HexagonAtoms643.innerABC_eq,
    HexagonAtoms643.innerRightABC_eq,
    HexagonAtoms643.inverseACB_eq,
    HexagonAtoms643.innerACB_eq,
    HexagonAtoms643.assocBCA_eq,
    HexagonAtoms643.innerRightBAC_eq,
    HexagonAtoms643.assocCAB_eq,
    HexagonAtoms643.outerLeftABC_eq,
    HexagonRowColumn643.product0_eq,
    HexagonRowColumn643.product1_eq,
    HexagonRowColumn643.product2_eq,
    HexagonRowColumn643.product3_eq,
    HexagonRowColumn643.product4_eq,
    HexagonRowColumn643.product5_eq,
    HexagonRowColumn643.product6_eq,
    HexagonRowColumn643.product7_eq] using right2Middle6_eq_case_4_3_checked

private theorem leftFinal6_case_4_3_row_0_0_0 : (((-1 : ℤ) ^ (leftScaleBit 6 4 3).val * positiveScale (leftScaleExponent 6 4 3)) •
      (rowColumnMul HexagonRowColumn643.rows_assocBCA HexagonRowColumn643.cols_left0)) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = (negativeScale (leftScaleExponent 6 4 3) • (left1Middle6 4 3)) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem leftFinal6_case_4_3_row_0_0_1 : (((-1 : ℤ) ^ (leftScaleBit 6 4 3).val * positiveScale (leftScaleExponent 6 4 3)) •
      (rowColumnMul HexagonRowColumn643.rows_assocBCA HexagonRowColumn643.cols_left0)) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = (negativeScale (leftScaleExponent 6 4 3) • (left1Middle6 4 3)) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem leftFinal6_case_4_3_row_0_0_2 : (((-1 : ℤ) ^ (leftScaleBit 6 4 3).val * positiveScale (leftScaleExponent 6 4 3)) •
      (rowColumnMul HexagonRowColumn643.rows_assocBCA HexagonRowColumn643.cols_left0)) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = (negativeScale (leftScaleExponent 6 4 3) • (left1Middle6 4 3)) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem leftFinal6_case_4_3_row_0_0_3 : (((-1 : ℤ) ^ (leftScaleBit 6 4 3).val * positiveScale (leftScaleExponent 6 4 3)) •
      (rowColumnMul HexagonRowColumn643.rows_assocBCA HexagonRowColumn643.cols_left0)) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = (negativeScale (leftScaleExponent 6 4 3) • (left1Middle6 4 3)) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem leftFinal6_case_4_3_row_0_0_4 : (((-1 : ℤ) ^ (leftScaleBit 6 4 3).val * positiveScale (leftScaleExponent 6 4 3)) •
      (rowColumnMul HexagonRowColumn643.rows_assocBCA HexagonRowColumn643.cols_left0)) ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = (negativeScale (leftScaleExponent 6 4 3) • (left1Middle6 4 3)) ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem leftFinal6_case_4_3_row_0_0_5 : (((-1 : ℤ) ^ (leftScaleBit 6 4 3).val * positiveScale (leftScaleExponent 6 4 3)) •
      (rowColumnMul HexagonRowColumn643.rows_assocBCA HexagonRowColumn643.cols_left0)) ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = (negativeScale (leftScaleExponent 6 4 3) • (left1Middle6 4 3)) ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem leftFinal6_case_4_3_row_0_0_6 : (((-1 : ℤ) ^ (leftScaleBit 6 4 3).val * positiveScale (leftScaleExponent 6 4 3)) •
      (rowColumnMul HexagonRowColumn643.rows_assocBCA HexagonRowColumn643.cols_left0)) ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = (negativeScale (leftScaleExponent 6 4 3) • (left1Middle6 4 3)) ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem leftFinal6_case_4_3_row_0_0_7 : (((-1 : ℤ) ^ (leftScaleBit 6 4 3).val * positiveScale (leftScaleExponent 6 4 3)) •
      (rowColumnMul HexagonRowColumn643.rows_assocBCA HexagonRowColumn643.cols_left0)) ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = (negativeScale (leftScaleExponent 6 4 3) • (left1Middle6 4 3)) ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem leftFinal6_case_4_3_row_1_0_0 : (((-1 : ℤ) ^ (leftScaleBit 6 4 3).val * positiveScale (leftScaleExponent 6 4 3)) •
      (rowColumnMul HexagonRowColumn643.rows_assocBCA HexagonRowColumn643.cols_left0)) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = (negativeScale (leftScaleExponent 6 4 3) • (left1Middle6 4 3)) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem leftFinal6_case_4_3_row_1_0_1 : (((-1 : ℤ) ^ (leftScaleBit 6 4 3).val * positiveScale (leftScaleExponent 6 4 3)) •
      (rowColumnMul HexagonRowColumn643.rows_assocBCA HexagonRowColumn643.cols_left0)) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = (negativeScale (leftScaleExponent 6 4 3) • (left1Middle6 4 3)) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem leftFinal6_case_4_3_row_1_0_2 : (((-1 : ℤ) ^ (leftScaleBit 6 4 3).val * positiveScale (leftScaleExponent 6 4 3)) •
      (rowColumnMul HexagonRowColumn643.rows_assocBCA HexagonRowColumn643.cols_left0)) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = (negativeScale (leftScaleExponent 6 4 3) • (left1Middle6 4 3)) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem leftFinal6_case_4_3_row_1_0_3 : (((-1 : ℤ) ^ (leftScaleBit 6 4 3).val * positiveScale (leftScaleExponent 6 4 3)) •
      (rowColumnMul HexagonRowColumn643.rows_assocBCA HexagonRowColumn643.cols_left0)) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = (negativeScale (leftScaleExponent 6 4 3) • (left1Middle6 4 3)) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem leftFinal6_case_4_3_row_1_0_4 : (((-1 : ℤ) ^ (leftScaleBit 6 4 3).val * positiveScale (leftScaleExponent 6 4 3)) •
      (rowColumnMul HexagonRowColumn643.rows_assocBCA HexagonRowColumn643.cols_left0)) ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = (negativeScale (leftScaleExponent 6 4 3) • (left1Middle6 4 3)) ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem leftFinal6_case_4_3_row_1_0_5 : (((-1 : ℤ) ^ (leftScaleBit 6 4 3).val * positiveScale (leftScaleExponent 6 4 3)) •
      (rowColumnMul HexagonRowColumn643.rows_assocBCA HexagonRowColumn643.cols_left0)) ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = (negativeScale (leftScaleExponent 6 4 3) • (left1Middle6 4 3)) ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem leftFinal6_case_4_3_row_1_0_6 : (((-1 : ℤ) ^ (leftScaleBit 6 4 3).val * positiveScale (leftScaleExponent 6 4 3)) •
      (rowColumnMul HexagonRowColumn643.rows_assocBCA HexagonRowColumn643.cols_left0)) ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = (negativeScale (leftScaleExponent 6 4 3) • (left1Middle6 4 3)) ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem leftFinal6_case_4_3_row_1_0_7 : (((-1 : ℤ) ^ (leftScaleBit 6 4 3).val * positiveScale (leftScaleExponent 6 4 3)) •
      (rowColumnMul HexagonRowColumn643.rows_assocBCA HexagonRowColumn643.cols_left0)) ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = (negativeScale (leftScaleExponent 6 4 3) • (left1Middle6 4 3)) ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem leftFinal6_case_4_3_row_2_0_0 : (((-1 : ℤ) ^ (leftScaleBit 6 4 3).val * positiveScale (leftScaleExponent 6 4 3)) •
      (rowColumnMul HexagonRowColumn643.rows_assocBCA HexagonRowColumn643.cols_left0)) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = (negativeScale (leftScaleExponent 6 4 3) • (left1Middle6 4 3)) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem leftFinal6_case_4_3_row_2_0_1 : (((-1 : ℤ) ^ (leftScaleBit 6 4 3).val * positiveScale (leftScaleExponent 6 4 3)) •
      (rowColumnMul HexagonRowColumn643.rows_assocBCA HexagonRowColumn643.cols_left0)) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = (negativeScale (leftScaleExponent 6 4 3) • (left1Middle6 4 3)) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem leftFinal6_case_4_3_row_2_0_2 : (((-1 : ℤ) ^ (leftScaleBit 6 4 3).val * positiveScale (leftScaleExponent 6 4 3)) •
      (rowColumnMul HexagonRowColumn643.rows_assocBCA HexagonRowColumn643.cols_left0)) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = (negativeScale (leftScaleExponent 6 4 3) • (left1Middle6 4 3)) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem leftFinal6_case_4_3_row_2_0_3 : (((-1 : ℤ) ^ (leftScaleBit 6 4 3).val * positiveScale (leftScaleExponent 6 4 3)) •
      (rowColumnMul HexagonRowColumn643.rows_assocBCA HexagonRowColumn643.cols_left0)) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = (negativeScale (leftScaleExponent 6 4 3) • (left1Middle6 4 3)) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem leftFinal6_case_4_3_row_2_0_4 : (((-1 : ℤ) ^ (leftScaleBit 6 4 3).val * positiveScale (leftScaleExponent 6 4 3)) •
      (rowColumnMul HexagonRowColumn643.rows_assocBCA HexagonRowColumn643.cols_left0)) ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = (negativeScale (leftScaleExponent 6 4 3) • (left1Middle6 4 3)) ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem leftFinal6_case_4_3_row_2_0_5 : (((-1 : ℤ) ^ (leftScaleBit 6 4 3).val * positiveScale (leftScaleExponent 6 4 3)) •
      (rowColumnMul HexagonRowColumn643.rows_assocBCA HexagonRowColumn643.cols_left0)) ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = (negativeScale (leftScaleExponent 6 4 3) • (left1Middle6 4 3)) ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem leftFinal6_case_4_3_row_2_0_6 : (((-1 : ℤ) ^ (leftScaleBit 6 4 3).val * positiveScale (leftScaleExponent 6 4 3)) •
      (rowColumnMul HexagonRowColumn643.rows_assocBCA HexagonRowColumn643.cols_left0)) ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = (negativeScale (leftScaleExponent 6 4 3) • (left1Middle6 4 3)) ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem leftFinal6_case_4_3_row_2_0_7 : (((-1 : ℤ) ^ (leftScaleBit 6 4 3).val * positiveScale (leftScaleExponent 6 4 3)) •
      (rowColumnMul HexagonRowColumn643.rows_assocBCA HexagonRowColumn643.cols_left0)) ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = (negativeScale (leftScaleExponent 6 4 3) • (left1Middle6 4 3)) ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem leftFinal6_case_4_3_row_3_0_0 : (((-1 : ℤ) ^ (leftScaleBit 6 4 3).val * positiveScale (leftScaleExponent 6 4 3)) •
      (rowColumnMul HexagonRowColumn643.rows_assocBCA HexagonRowColumn643.cols_left0)) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = (negativeScale (leftScaleExponent 6 4 3) • (left1Middle6 4 3)) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem leftFinal6_case_4_3_row_3_0_1 : (((-1 : ℤ) ^ (leftScaleBit 6 4 3).val * positiveScale (leftScaleExponent 6 4 3)) •
      (rowColumnMul HexagonRowColumn643.rows_assocBCA HexagonRowColumn643.cols_left0)) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = (negativeScale (leftScaleExponent 6 4 3) • (left1Middle6 4 3)) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem leftFinal6_case_4_3_row_3_0_2 : (((-1 : ℤ) ^ (leftScaleBit 6 4 3).val * positiveScale (leftScaleExponent 6 4 3)) •
      (rowColumnMul HexagonRowColumn643.rows_assocBCA HexagonRowColumn643.cols_left0)) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = (negativeScale (leftScaleExponent 6 4 3) • (left1Middle6 4 3)) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem leftFinal6_case_4_3_row_3_0_3 : (((-1 : ℤ) ^ (leftScaleBit 6 4 3).val * positiveScale (leftScaleExponent 6 4 3)) •
      (rowColumnMul HexagonRowColumn643.rows_assocBCA HexagonRowColumn643.cols_left0)) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = (negativeScale (leftScaleExponent 6 4 3) • (left1Middle6 4 3)) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem leftFinal6_case_4_3_row_3_0_4 : (((-1 : ℤ) ^ (leftScaleBit 6 4 3).val * positiveScale (leftScaleExponent 6 4 3)) •
      (rowColumnMul HexagonRowColumn643.rows_assocBCA HexagonRowColumn643.cols_left0)) ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = (negativeScale (leftScaleExponent 6 4 3) • (left1Middle6 4 3)) ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem leftFinal6_case_4_3_row_3_0_5 : (((-1 : ℤ) ^ (leftScaleBit 6 4 3).val * positiveScale (leftScaleExponent 6 4 3)) •
      (rowColumnMul HexagonRowColumn643.rows_assocBCA HexagonRowColumn643.cols_left0)) ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = (negativeScale (leftScaleExponent 6 4 3) • (left1Middle6 4 3)) ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem leftFinal6_case_4_3_row_3_0_6 : (((-1 : ℤ) ^ (leftScaleBit 6 4 3).val * positiveScale (leftScaleExponent 6 4 3)) •
      (rowColumnMul HexagonRowColumn643.rows_assocBCA HexagonRowColumn643.cols_left0)) ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = (negativeScale (leftScaleExponent 6 4 3) • (left1Middle6 4 3)) ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem leftFinal6_case_4_3_row_3_0_7 : (((-1 : ℤ) ^ (leftScaleBit 6 4 3).val * positiveScale (leftScaleExponent 6 4 3)) •
      (rowColumnMul HexagonRowColumn643.rows_assocBCA HexagonRowColumn643.cols_left0)) ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = (negativeScale (leftScaleExponent 6 4 3) • (left1Middle6 4 3)) ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem leftFinal6_case_4_3_checked : ((-1 : ℤ) ^ (leftScaleBit 6 4 3).val * positiveScale (leftScaleExponent 6 4 3)) •
      (rowColumnMul HexagonRowColumn643.rows_assocBCA HexagonRowColumn643.cols_left0) = negativeScale (leftScaleExponent 6 4 3) • (left1Middle6 4 3) := by
  funext r
  fin_cases r
  · exact leftFinal6_case_4_3_row_0_0_0
  · exact leftFinal6_case_4_3_row_0_0_1
  · exact leftFinal6_case_4_3_row_0_0_2
  · exact leftFinal6_case_4_3_row_0_0_3
  · exact leftFinal6_case_4_3_row_0_0_4
  · exact leftFinal6_case_4_3_row_0_0_5
  · exact leftFinal6_case_4_3_row_0_0_6
  · exact leftFinal6_case_4_3_row_0_0_7
  · exact leftFinal6_case_4_3_row_1_0_0
  · exact leftFinal6_case_4_3_row_1_0_1
  · exact leftFinal6_case_4_3_row_1_0_2
  · exact leftFinal6_case_4_3_row_1_0_3
  · exact leftFinal6_case_4_3_row_1_0_4
  · exact leftFinal6_case_4_3_row_1_0_5
  · exact leftFinal6_case_4_3_row_1_0_6
  · exact leftFinal6_case_4_3_row_1_0_7
  · exact leftFinal6_case_4_3_row_2_0_0
  · exact leftFinal6_case_4_3_row_2_0_1
  · exact leftFinal6_case_4_3_row_2_0_2
  · exact leftFinal6_case_4_3_row_2_0_3
  · exact leftFinal6_case_4_3_row_2_0_4
  · exact leftFinal6_case_4_3_row_2_0_5
  · exact leftFinal6_case_4_3_row_2_0_6
  · exact leftFinal6_case_4_3_row_2_0_7
  · exact leftFinal6_case_4_3_row_3_0_0
  · exact leftFinal6_case_4_3_row_3_0_1
  · exact leftFinal6_case_4_3_row_3_0_2
  · exact leftFinal6_case_4_3_row_3_0_3
  · exact leftFinal6_case_4_3_row_3_0_4
  · exact leftFinal6_case_4_3_row_3_0_5
  · exact leftFinal6_case_4_3_row_3_0_6
  · exact leftFinal6_case_4_3_row_3_0_7

set_option backward.isDefEq.respectTransparency false in
theorem leftFinal6_case_4_3 : ((-1 : ℤ) ^ (leftScaleBit 6 4 3).val * positiveScale (leftScaleExponent 6 4 3)) •
      (associatorZ 4 3 6 * left0Middle6 4 3) = negativeScale (leftScaleExponent 6 4 3) • (innerRightZ 4 6 3 * left1Middle6 4 3) := by
  simpa only [HexagonAtoms643.assocABC_eq,
    HexagonAtoms643.outerABC_eq,
    HexagonAtoms643.assocBAC_eq,
    HexagonAtoms643.innerABC_eq,
    HexagonAtoms643.innerRightABC_eq,
    HexagonAtoms643.inverseACB_eq,
    HexagonAtoms643.innerACB_eq,
    HexagonAtoms643.assocBCA_eq,
    HexagonAtoms643.innerRightBAC_eq,
    HexagonAtoms643.assocCAB_eq,
    HexagonAtoms643.outerLeftABC_eq,
    HexagonRowColumn643.product0_eq,
    HexagonRowColumn643.product1_eq,
    HexagonRowColumn643.product2_eq,
    HexagonRowColumn643.product3_eq,
    HexagonRowColumn643.product4_eq,
    HexagonRowColumn643.product5_eq,
    HexagonRowColumn643.product6_eq,
    HexagonRowColumn643.product7_eq] using leftFinal6_case_4_3_checked

private theorem rightFinal6_case_4_3_row_0_0_0 : (((-1 : ℤ) ^ (rightScaleBit 6 4 3).val * positiveScale (rightScaleExponent 6 4 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 3 4 : ℤ)) • HexagonAtoms643.outerLeftABC) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) = (negativeScale (rightScaleExponent 6 4 3) • (rowColumnMul HexagonRowColumn643.rows_assocCAB HexagonRowColumn643.cols_right2)) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem rightFinal6_case_4_3_row_0_0_1 : (((-1 : ℤ) ^ (rightScaleBit 6 4 3).val * positiveScale (rightScaleExponent 6 4 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 3 4 : ℤ)) • HexagonAtoms643.outerLeftABC) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) = (negativeScale (rightScaleExponent 6 4 3) • (rowColumnMul HexagonRowColumn643.rows_assocCAB HexagonRowColumn643.cols_right2)) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem rightFinal6_case_4_3_row_0_0_2 : (((-1 : ℤ) ^ (rightScaleBit 6 4 3).val * positiveScale (rightScaleExponent 6 4 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 3 4 : ℤ)) • HexagonAtoms643.outerLeftABC) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) = (negativeScale (rightScaleExponent 6 4 3) • (rowColumnMul HexagonRowColumn643.rows_assocCAB HexagonRowColumn643.cols_right2)) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem rightFinal6_case_4_3_row_0_0_3 : (((-1 : ℤ) ^ (rightScaleBit 6 4 3).val * positiveScale (rightScaleExponent 6 4 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 3 4 : ℤ)) • HexagonAtoms643.outerLeftABC) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) = (negativeScale (rightScaleExponent 6 4 3) • (rowColumnMul HexagonRowColumn643.rows_assocCAB HexagonRowColumn643.cols_right2)) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem rightFinal6_case_4_3_row_0_0_4 : (((-1 : ℤ) ^ (rightScaleBit 6 4 3).val * positiveScale (rightScaleExponent 6 4 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 3 4 : ℤ)) • HexagonAtoms643.outerLeftABC) ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) = (negativeScale (rightScaleExponent 6 4 3) • (rowColumnMul HexagonRowColumn643.rows_assocCAB HexagonRowColumn643.cols_right2)) ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem rightFinal6_case_4_3_row_0_0_5 : (((-1 : ℤ) ^ (rightScaleBit 6 4 3).val * positiveScale (rightScaleExponent 6 4 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 3 4 : ℤ)) • HexagonAtoms643.outerLeftABC) ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) = (negativeScale (rightScaleExponent 6 4 3) • (rowColumnMul HexagonRowColumn643.rows_assocCAB HexagonRowColumn643.cols_right2)) ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem rightFinal6_case_4_3_row_0_0_6 : (((-1 : ℤ) ^ (rightScaleBit 6 4 3).val * positiveScale (rightScaleExponent 6 4 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 3 4 : ℤ)) • HexagonAtoms643.outerLeftABC) ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) = (negativeScale (rightScaleExponent 6 4 3) • (rowColumnMul HexagonRowColumn643.rows_assocCAB HexagonRowColumn643.cols_right2)) ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem rightFinal6_case_4_3_row_0_0_7 : (((-1 : ℤ) ^ (rightScaleBit 6 4 3).val * positiveScale (rightScaleExponent 6 4 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 3 4 : ℤ)) • HexagonAtoms643.outerLeftABC) ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) = (negativeScale (rightScaleExponent 6 4 3) • (rowColumnMul HexagonRowColumn643.rows_assocCAB HexagonRowColumn643.cols_right2)) ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem rightFinal6_case_4_3_row_0_1_0 : (((-1 : ℤ) ^ (rightScaleBit 6 4 3).val * positiveScale (rightScaleExponent 6 4 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 3 4 : ℤ)) • HexagonAtoms643.outerLeftABC) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) = (negativeScale (rightScaleExponent 6 4 3) • (rowColumnMul HexagonRowColumn643.rows_assocCAB HexagonRowColumn643.cols_right2)) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem rightFinal6_case_4_3_row_0_1_1 : (((-1 : ℤ) ^ (rightScaleBit 6 4 3).val * positiveScale (rightScaleExponent 6 4 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 3 4 : ℤ)) • HexagonAtoms643.outerLeftABC) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) = (negativeScale (rightScaleExponent 6 4 3) • (rowColumnMul HexagonRowColumn643.rows_assocCAB HexagonRowColumn643.cols_right2)) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem rightFinal6_case_4_3_row_0_1_2 : (((-1 : ℤ) ^ (rightScaleBit 6 4 3).val * positiveScale (rightScaleExponent 6 4 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 3 4 : ℤ)) • HexagonAtoms643.outerLeftABC) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) = (negativeScale (rightScaleExponent 6 4 3) • (rowColumnMul HexagonRowColumn643.rows_assocCAB HexagonRowColumn643.cols_right2)) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem rightFinal6_case_4_3_row_0_1_3 : (((-1 : ℤ) ^ (rightScaleBit 6 4 3).val * positiveScale (rightScaleExponent 6 4 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 3 4 : ℤ)) • HexagonAtoms643.outerLeftABC) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) = (negativeScale (rightScaleExponent 6 4 3) • (rowColumnMul HexagonRowColumn643.rows_assocCAB HexagonRowColumn643.cols_right2)) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem rightFinal6_case_4_3_row_0_1_4 : (((-1 : ℤ) ^ (rightScaleBit 6 4 3).val * positiveScale (rightScaleExponent 6 4 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 3 4 : ℤ)) • HexagonAtoms643.outerLeftABC) ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) = (negativeScale (rightScaleExponent 6 4 3) • (rowColumnMul HexagonRowColumn643.rows_assocCAB HexagonRowColumn643.cols_right2)) ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem rightFinal6_case_4_3_row_0_1_5 : (((-1 : ℤ) ^ (rightScaleBit 6 4 3).val * positiveScale (rightScaleExponent 6 4 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 3 4 : ℤ)) • HexagonAtoms643.outerLeftABC) ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) = (negativeScale (rightScaleExponent 6 4 3) • (rowColumnMul HexagonRowColumn643.rows_assocCAB HexagonRowColumn643.cols_right2)) ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem rightFinal6_case_4_3_row_0_1_6 : (((-1 : ℤ) ^ (rightScaleBit 6 4 3).val * positiveScale (rightScaleExponent 6 4 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 3 4 : ℤ)) • HexagonAtoms643.outerLeftABC) ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) = (negativeScale (rightScaleExponent 6 4 3) • (rowColumnMul HexagonRowColumn643.rows_assocCAB HexagonRowColumn643.cols_right2)) ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem rightFinal6_case_4_3_row_0_1_7 : (((-1 : ℤ) ^ (rightScaleBit 6 4 3).val * positiveScale (rightScaleExponent 6 4 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 3 4 : ℤ)) • HexagonAtoms643.outerLeftABC) ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) = (negativeScale (rightScaleExponent 6 4 3) • (rowColumnMul HexagonRowColumn643.rows_assocCAB HexagonRowColumn643.cols_right2)) ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem rightFinal6_case_4_3_row_1_0_0 : (((-1 : ℤ) ^ (rightScaleBit 6 4 3).val * positiveScale (rightScaleExponent 6 4 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 3 4 : ℤ)) • HexagonAtoms643.outerLeftABC) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) = (negativeScale (rightScaleExponent 6 4 3) • (rowColumnMul HexagonRowColumn643.rows_assocCAB HexagonRowColumn643.cols_right2)) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem rightFinal6_case_4_3_row_1_0_1 : (((-1 : ℤ) ^ (rightScaleBit 6 4 3).val * positiveScale (rightScaleExponent 6 4 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 3 4 : ℤ)) • HexagonAtoms643.outerLeftABC) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) = (negativeScale (rightScaleExponent 6 4 3) • (rowColumnMul HexagonRowColumn643.rows_assocCAB HexagonRowColumn643.cols_right2)) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem rightFinal6_case_4_3_row_1_0_2 : (((-1 : ℤ) ^ (rightScaleBit 6 4 3).val * positiveScale (rightScaleExponent 6 4 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 3 4 : ℤ)) • HexagonAtoms643.outerLeftABC) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) = (negativeScale (rightScaleExponent 6 4 3) • (rowColumnMul HexagonRowColumn643.rows_assocCAB HexagonRowColumn643.cols_right2)) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem rightFinal6_case_4_3_row_1_0_3 : (((-1 : ℤ) ^ (rightScaleBit 6 4 3).val * positiveScale (rightScaleExponent 6 4 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 3 4 : ℤ)) • HexagonAtoms643.outerLeftABC) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) = (negativeScale (rightScaleExponent 6 4 3) • (rowColumnMul HexagonRowColumn643.rows_assocCAB HexagonRowColumn643.cols_right2)) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem rightFinal6_case_4_3_row_1_0_4 : (((-1 : ℤ) ^ (rightScaleBit 6 4 3).val * positiveScale (rightScaleExponent 6 4 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 3 4 : ℤ)) • HexagonAtoms643.outerLeftABC) ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) = (negativeScale (rightScaleExponent 6 4 3) • (rowColumnMul HexagonRowColumn643.rows_assocCAB HexagonRowColumn643.cols_right2)) ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem rightFinal6_case_4_3_row_1_0_5 : (((-1 : ℤ) ^ (rightScaleBit 6 4 3).val * positiveScale (rightScaleExponent 6 4 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 3 4 : ℤ)) • HexagonAtoms643.outerLeftABC) ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) = (negativeScale (rightScaleExponent 6 4 3) • (rowColumnMul HexagonRowColumn643.rows_assocCAB HexagonRowColumn643.cols_right2)) ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem rightFinal6_case_4_3_row_1_0_6 : (((-1 : ℤ) ^ (rightScaleBit 6 4 3).val * positiveScale (rightScaleExponent 6 4 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 3 4 : ℤ)) • HexagonAtoms643.outerLeftABC) ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) = (negativeScale (rightScaleExponent 6 4 3) • (rowColumnMul HexagonRowColumn643.rows_assocCAB HexagonRowColumn643.cols_right2)) ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem rightFinal6_case_4_3_row_1_0_7 : (((-1 : ℤ) ^ (rightScaleBit 6 4 3).val * positiveScale (rightScaleExponent 6 4 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 3 4 : ℤ)) • HexagonAtoms643.outerLeftABC) ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) = (negativeScale (rightScaleExponent 6 4 3) • (rowColumnMul HexagonRowColumn643.rows_assocCAB HexagonRowColumn643.cols_right2)) ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem rightFinal6_case_4_3_row_1_1_0 : (((-1 : ℤ) ^ (rightScaleBit 6 4 3).val * positiveScale (rightScaleExponent 6 4 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 3 4 : ℤ)) • HexagonAtoms643.outerLeftABC) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) = (negativeScale (rightScaleExponent 6 4 3) • (rowColumnMul HexagonRowColumn643.rows_assocCAB HexagonRowColumn643.cols_right2)) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem rightFinal6_case_4_3_row_1_1_1 : (((-1 : ℤ) ^ (rightScaleBit 6 4 3).val * positiveScale (rightScaleExponent 6 4 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 3 4 : ℤ)) • HexagonAtoms643.outerLeftABC) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) = (negativeScale (rightScaleExponent 6 4 3) • (rowColumnMul HexagonRowColumn643.rows_assocCAB HexagonRowColumn643.cols_right2)) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem rightFinal6_case_4_3_row_1_1_2 : (((-1 : ℤ) ^ (rightScaleBit 6 4 3).val * positiveScale (rightScaleExponent 6 4 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 3 4 : ℤ)) • HexagonAtoms643.outerLeftABC) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) = (negativeScale (rightScaleExponent 6 4 3) • (rowColumnMul HexagonRowColumn643.rows_assocCAB HexagonRowColumn643.cols_right2)) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem rightFinal6_case_4_3_row_1_1_3 : (((-1 : ℤ) ^ (rightScaleBit 6 4 3).val * positiveScale (rightScaleExponent 6 4 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 3 4 : ℤ)) • HexagonAtoms643.outerLeftABC) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) = (negativeScale (rightScaleExponent 6 4 3) • (rowColumnMul HexagonRowColumn643.rows_assocCAB HexagonRowColumn643.cols_right2)) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem rightFinal6_case_4_3_row_1_1_4 : (((-1 : ℤ) ^ (rightScaleBit 6 4 3).val * positiveScale (rightScaleExponent 6 4 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 3 4 : ℤ)) • HexagonAtoms643.outerLeftABC) ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) = (negativeScale (rightScaleExponent 6 4 3) • (rowColumnMul HexagonRowColumn643.rows_assocCAB HexagonRowColumn643.cols_right2)) ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem rightFinal6_case_4_3_row_1_1_5 : (((-1 : ℤ) ^ (rightScaleBit 6 4 3).val * positiveScale (rightScaleExponent 6 4 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 3 4 : ℤ)) • HexagonAtoms643.outerLeftABC) ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) = (negativeScale (rightScaleExponent 6 4 3) • (rowColumnMul HexagonRowColumn643.rows_assocCAB HexagonRowColumn643.cols_right2)) ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem rightFinal6_case_4_3_row_1_1_6 : (((-1 : ℤ) ^ (rightScaleBit 6 4 3).val * positiveScale (rightScaleExponent 6 4 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 3 4 : ℤ)) • HexagonAtoms643.outerLeftABC) ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) = (negativeScale (rightScaleExponent 6 4 3) • (rowColumnMul HexagonRowColumn643.rows_assocCAB HexagonRowColumn643.cols_right2)) ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem rightFinal6_case_4_3_row_1_1_7 : (((-1 : ℤ) ^ (rightScaleBit 6 4 3).val * positiveScale (rightScaleExponent 6 4 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 3 4 : ℤ)) • HexagonAtoms643.outerLeftABC) ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) = (negativeScale (rightScaleExponent 6 4 3) • (rowColumnMul HexagonRowColumn643.rows_assocCAB HexagonRowColumn643.cols_right2)) ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 8)
  decide +kernel

private theorem rightFinal6_case_4_3_checked : ((-1 : ℤ) ^ (rightScaleBit 6 4 3).val * positiveScale (rightScaleExponent 6 4 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 3 4 : ℤ)) • HexagonAtoms643.outerLeftABC = negativeScale (rightScaleExponent 6 4 3) • (rowColumnMul HexagonRowColumn643.rows_assocCAB HexagonRowColumn643.cols_right2) := by
  funext r
  fin_cases r
  · exact rightFinal6_case_4_3_row_0_0_0
  · exact rightFinal6_case_4_3_row_0_0_1
  · exact rightFinal6_case_4_3_row_0_0_2
  · exact rightFinal6_case_4_3_row_0_0_3
  · exact rightFinal6_case_4_3_row_0_0_4
  · exact rightFinal6_case_4_3_row_0_0_5
  · exact rightFinal6_case_4_3_row_0_0_6
  · exact rightFinal6_case_4_3_row_0_0_7
  · exact rightFinal6_case_4_3_row_0_1_0
  · exact rightFinal6_case_4_3_row_0_1_1
  · exact rightFinal6_case_4_3_row_0_1_2
  · exact rightFinal6_case_4_3_row_0_1_3
  · exact rightFinal6_case_4_3_row_0_1_4
  · exact rightFinal6_case_4_3_row_0_1_5
  · exact rightFinal6_case_4_3_row_0_1_6
  · exact rightFinal6_case_4_3_row_0_1_7
  · exact rightFinal6_case_4_3_row_1_0_0
  · exact rightFinal6_case_4_3_row_1_0_1
  · exact rightFinal6_case_4_3_row_1_0_2
  · exact rightFinal6_case_4_3_row_1_0_3
  · exact rightFinal6_case_4_3_row_1_0_4
  · exact rightFinal6_case_4_3_row_1_0_5
  · exact rightFinal6_case_4_3_row_1_0_6
  · exact rightFinal6_case_4_3_row_1_0_7
  · exact rightFinal6_case_4_3_row_1_1_0
  · exact rightFinal6_case_4_3_row_1_1_1
  · exact rightFinal6_case_4_3_row_1_1_2
  · exact rightFinal6_case_4_3_row_1_1_3
  · exact rightFinal6_case_4_3_row_1_1_4
  · exact rightFinal6_case_4_3_row_1_1_5
  · exact rightFinal6_case_4_3_row_1_1_6
  · exact rightFinal6_case_4_3_row_1_1_7

set_option backward.isDefEq.respectTransparency false in
theorem rightFinal6_case_4_3 : ((-1 : ℤ) ^ (rightScaleBit 6 4 3).val * positiveScale (rightScaleExponent 6 4 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 3 4 : ℤ)) • outerLeftZ 6 4 3 = negativeScale (rightScaleExponent 6 4 3) • (associatorZ 3 6 4 * right2Middle6 4 3) := by
  simpa only [HexagonAtoms643.assocABC_eq,
    HexagonAtoms643.outerABC_eq,
    HexagonAtoms643.assocBAC_eq,
    HexagonAtoms643.innerABC_eq,
    HexagonAtoms643.innerRightABC_eq,
    HexagonAtoms643.inverseACB_eq,
    HexagonAtoms643.innerACB_eq,
    HexagonAtoms643.assocBCA_eq,
    HexagonAtoms643.innerRightBAC_eq,
    HexagonAtoms643.assocCAB_eq,
    HexagonAtoms643.outerLeftABC_eq,
    HexagonRowColumn643.product0_eq,
    HexagonRowColumn643.product1_eq,
    HexagonRowColumn643.product2_eq,
    HexagonRowColumn643.product3_eq,
    HexagonRowColumn643.product4_eq,
    HexagonRowColumn643.product5_eq,
    HexagonRowColumn643.product6_eq,
    HexagonRowColumn643.product7_eq] using rightFinal6_case_4_3_checked

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonCases6
