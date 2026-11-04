import RMod.BrundanEllis.StackingReferenceHexagonMiddle3
import RMod.BrundanEllis.StackingReferenceSparseMatrixCheck
import RMod.BrundanEllis.StackingReferenceHexagonAtoms325
import RMod.BrundanEllis.StackingReferenceHexagonRowColumn325

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

private theorem left0Middle3_eq_case_2_5_row_0_0_0 : (left0Middle3 2 5) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn325.rows_outerABC HexagonRowColumn325.cols_assocABC) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_2_5_row_0_0_1 : (left0Middle3 2 5) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn325.rows_outerABC HexagonRowColumn325.cols_assocABC) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_2_5_row_0_0_2 : (left0Middle3 2 5) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn325.rows_outerABC HexagonRowColumn325.cols_assocABC) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_2_5_row_0_0_3 : (left0Middle3 2 5) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn325.rows_outerABC HexagonRowColumn325.cols_assocABC) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_2_5_row_0_1_0 : (left0Middle3 2 5) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn325.rows_outerABC HexagonRowColumn325.cols_assocABC) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_2_5_row_0_1_1 : (left0Middle3 2 5) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn325.rows_outerABC HexagonRowColumn325.cols_assocABC) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_2_5_row_0_1_2 : (left0Middle3 2 5) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn325.rows_outerABC HexagonRowColumn325.cols_assocABC) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_2_5_row_0_1_3 : (left0Middle3 2 5) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn325.rows_outerABC HexagonRowColumn325.cols_assocABC) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_2_5_row_1_0_0 : (left0Middle3 2 5) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn325.rows_outerABC HexagonRowColumn325.cols_assocABC) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_2_5_row_1_0_1 : (left0Middle3 2 5) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn325.rows_outerABC HexagonRowColumn325.cols_assocABC) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_2_5_row_1_0_2 : (left0Middle3 2 5) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn325.rows_outerABC HexagonRowColumn325.cols_assocABC) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_2_5_row_1_0_3 : (left0Middle3 2 5) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn325.rows_outerABC HexagonRowColumn325.cols_assocABC) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_2_5_row_1_1_0 : (left0Middle3 2 5) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn325.rows_outerABC HexagonRowColumn325.cols_assocABC) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_2_5_row_1_1_1 : (left0Middle3 2 5) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn325.rows_outerABC HexagonRowColumn325.cols_assocABC) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_2_5_row_1_1_2 : (left0Middle3 2 5) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn325.rows_outerABC HexagonRowColumn325.cols_assocABC) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_2_5_row_1_1_3 : (left0Middle3 2 5) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn325.rows_outerABC HexagonRowColumn325.cols_assocABC) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_2_5_row_2_0_0 : (left0Middle3 2 5) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn325.rows_outerABC HexagonRowColumn325.cols_assocABC) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_2_5_row_2_0_1 : (left0Middle3 2 5) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn325.rows_outerABC HexagonRowColumn325.cols_assocABC) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_2_5_row_2_0_2 : (left0Middle3 2 5) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn325.rows_outerABC HexagonRowColumn325.cols_assocABC) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_2_5_row_2_0_3 : (left0Middle3 2 5) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn325.rows_outerABC HexagonRowColumn325.cols_assocABC) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_2_5_row_2_1_0 : (left0Middle3 2 5) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn325.rows_outerABC HexagonRowColumn325.cols_assocABC) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_2_5_row_2_1_1 : (left0Middle3 2 5) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn325.rows_outerABC HexagonRowColumn325.cols_assocABC) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_2_5_row_2_1_2 : (left0Middle3 2 5) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn325.rows_outerABC HexagonRowColumn325.cols_assocABC) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_2_5_row_2_1_3 : (left0Middle3 2 5) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn325.rows_outerABC HexagonRowColumn325.cols_assocABC) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_2_5_row_3_0_0 : (left0Middle3 2 5) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn325.rows_outerABC HexagonRowColumn325.cols_assocABC) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_2_5_row_3_0_1 : (left0Middle3 2 5) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn325.rows_outerABC HexagonRowColumn325.cols_assocABC) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_2_5_row_3_0_2 : (left0Middle3 2 5) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn325.rows_outerABC HexagonRowColumn325.cols_assocABC) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_2_5_row_3_0_3 : (left0Middle3 2 5) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn325.rows_outerABC HexagonRowColumn325.cols_assocABC) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_2_5_row_3_1_0 : (left0Middle3 2 5) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn325.rows_outerABC HexagonRowColumn325.cols_assocABC) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_2_5_row_3_1_1 : (left0Middle3 2 5) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn325.rows_outerABC HexagonRowColumn325.cols_assocABC) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_2_5_row_3_1_2 : (left0Middle3 2 5) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn325.rows_outerABC HexagonRowColumn325.cols_assocABC) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_2_5_row_3_1_3 : (left0Middle3 2 5) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn325.rows_outerABC HexagonRowColumn325.cols_assocABC) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_2_5_checked : left0Middle3 2 5 = rowColumnMul HexagonRowColumn325.rows_outerABC HexagonRowColumn325.cols_assocABC := by
  funext r
  fin_cases r
  · exact left0Middle3_eq_case_2_5_row_0_0_0
  · exact left0Middle3_eq_case_2_5_row_0_0_1
  · exact left0Middle3_eq_case_2_5_row_0_0_2
  · exact left0Middle3_eq_case_2_5_row_0_0_3
  · exact left0Middle3_eq_case_2_5_row_0_1_0
  · exact left0Middle3_eq_case_2_5_row_0_1_1
  · exact left0Middle3_eq_case_2_5_row_0_1_2
  · exact left0Middle3_eq_case_2_5_row_0_1_3
  · exact left0Middle3_eq_case_2_5_row_1_0_0
  · exact left0Middle3_eq_case_2_5_row_1_0_1
  · exact left0Middle3_eq_case_2_5_row_1_0_2
  · exact left0Middle3_eq_case_2_5_row_1_0_3
  · exact left0Middle3_eq_case_2_5_row_1_1_0
  · exact left0Middle3_eq_case_2_5_row_1_1_1
  · exact left0Middle3_eq_case_2_5_row_1_1_2
  · exact left0Middle3_eq_case_2_5_row_1_1_3
  · exact left0Middle3_eq_case_2_5_row_2_0_0
  · exact left0Middle3_eq_case_2_5_row_2_0_1
  · exact left0Middle3_eq_case_2_5_row_2_0_2
  · exact left0Middle3_eq_case_2_5_row_2_0_3
  · exact left0Middle3_eq_case_2_5_row_2_1_0
  · exact left0Middle3_eq_case_2_5_row_2_1_1
  · exact left0Middle3_eq_case_2_5_row_2_1_2
  · exact left0Middle3_eq_case_2_5_row_2_1_3
  · exact left0Middle3_eq_case_2_5_row_3_0_0
  · exact left0Middle3_eq_case_2_5_row_3_0_1
  · exact left0Middle3_eq_case_2_5_row_3_0_2
  · exact left0Middle3_eq_case_2_5_row_3_0_3
  · exact left0Middle3_eq_case_2_5_row_3_1_0
  · exact left0Middle3_eq_case_2_5_row_3_1_1
  · exact left0Middle3_eq_case_2_5_row_3_1_2
  · exact left0Middle3_eq_case_2_5_row_3_1_3

set_option backward.isDefEq.respectTransparency false in
theorem left0Middle3_eq_case_2_5 : left0Middle3 2 5 = outerRightZ 3 2 5 * associatorZ 3 2 5 := by
  simpa only [HexagonAtoms325.assocABC_eq,
    HexagonAtoms325.outerABC_eq,
    HexagonAtoms325.assocBAC_eq,
    HexagonAtoms325.innerABC_eq,
    HexagonAtoms325.innerRightABC_eq,
    HexagonAtoms325.inverseACB_eq,
    HexagonAtoms325.innerACB_eq,
    HexagonAtoms325.assocBCA_eq,
    HexagonAtoms325.innerRightBAC_eq,
    HexagonAtoms325.assocCAB_eq,
    HexagonAtoms325.outerLeftABC_eq,
    HexagonRowColumn325.product0_eq,
    HexagonRowColumn325.product1_eq,
    HexagonRowColumn325.product2_eq,
    HexagonRowColumn325.product3_eq,
    HexagonRowColumn325.product4_eq,
    HexagonRowColumn325.product5_eq,
    HexagonRowColumn325.product6_eq,
    HexagonRowColumn325.product7_eq] using left0Middle3_eq_case_2_5_checked

private theorem left1Middle3_eq_case_2_5_row_0_0_0 : (left1Middle3 2 5) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms325.assocBAC) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_2_5_row_0_0_1 : (left1Middle3 2 5) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms325.assocBAC) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_2_5_row_0_0_2 : (left1Middle3 2 5) ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms325.assocBAC) ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_2_5_row_0_0_3 : (left1Middle3 2 5) ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms325.assocBAC) ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_2_5_row_1_0_0 : (left1Middle3 2 5) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms325.assocBAC) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_2_5_row_1_0_1 : (left1Middle3 2 5) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms325.assocBAC) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_2_5_row_1_0_2 : (left1Middle3 2 5) ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms325.assocBAC) ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_2_5_row_1_0_3 : (left1Middle3 2 5) ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms325.assocBAC) ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_2_5_row_2_0_0 : (left1Middle3 2 5) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms325.assocBAC) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_2_5_row_2_0_1 : (left1Middle3 2 5) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms325.assocBAC) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_2_5_row_2_0_2 : (left1Middle3 2 5) ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms325.assocBAC) ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_2_5_row_2_0_3 : (left1Middle3 2 5) ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms325.assocBAC) ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_2_5_row_3_0_0 : (left1Middle3 2 5) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms325.assocBAC) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_2_5_row_3_0_1 : (left1Middle3 2 5) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms325.assocBAC) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_2_5_row_3_0_2 : (left1Middle3 2 5) ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms325.assocBAC) ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_2_5_row_3_0_3 : (left1Middle3 2 5) ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms325.assocBAC) ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_2_5_row_4_0_0 : (left1Middle3 2 5) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms325.assocBAC) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_2_5_row_4_0_1 : (left1Middle3 2 5) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms325.assocBAC) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_2_5_row_4_0_2 : (left1Middle3 2 5) ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms325.assocBAC) ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_2_5_row_4_0_3 : (left1Middle3 2 5) ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms325.assocBAC) ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_2_5_row_5_0_0 : (left1Middle3 2 5) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms325.assocBAC) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_2_5_row_5_0_1 : (left1Middle3 2 5) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms325.assocBAC) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_2_5_row_5_0_2 : (left1Middle3 2 5) ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms325.assocBAC) ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_2_5_row_5_0_3 : (left1Middle3 2 5) ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms325.assocBAC) ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_2_5_row_6_0_0 : (left1Middle3 2 5) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms325.assocBAC) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_2_5_row_6_0_1 : (left1Middle3 2 5) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms325.assocBAC) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_2_5_row_6_0_2 : (left1Middle3 2 5) ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms325.assocBAC) ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_2_5_row_6_0_3 : (left1Middle3 2 5) ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms325.assocBAC) ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_2_5_row_7_0_0 : (left1Middle3 2 5) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms325.assocBAC) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_2_5_row_7_0_1 : (left1Middle3 2 5) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms325.assocBAC) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_2_5_row_7_0_2 : (left1Middle3 2 5) ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms325.assocBAC) ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_2_5_row_7_0_3 : (left1Middle3 2 5) ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms325.assocBAC) ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_2_5_checked : left1Middle3 2 5 = HexagonAtoms325.assocBAC := by
  funext r
  fin_cases r
  · exact left1Middle3_eq_case_2_5_row_0_0_0
  · exact left1Middle3_eq_case_2_5_row_0_0_1
  · exact left1Middle3_eq_case_2_5_row_0_0_2
  · exact left1Middle3_eq_case_2_5_row_0_0_3
  · exact left1Middle3_eq_case_2_5_row_1_0_0
  · exact left1Middle3_eq_case_2_5_row_1_0_1
  · exact left1Middle3_eq_case_2_5_row_1_0_2
  · exact left1Middle3_eq_case_2_5_row_1_0_3
  · exact left1Middle3_eq_case_2_5_row_2_0_0
  · exact left1Middle3_eq_case_2_5_row_2_0_1
  · exact left1Middle3_eq_case_2_5_row_2_0_2
  · exact left1Middle3_eq_case_2_5_row_2_0_3
  · exact left1Middle3_eq_case_2_5_row_3_0_0
  · exact left1Middle3_eq_case_2_5_row_3_0_1
  · exact left1Middle3_eq_case_2_5_row_3_0_2
  · exact left1Middle3_eq_case_2_5_row_3_0_3
  · exact left1Middle3_eq_case_2_5_row_4_0_0
  · exact left1Middle3_eq_case_2_5_row_4_0_1
  · exact left1Middle3_eq_case_2_5_row_4_0_2
  · exact left1Middle3_eq_case_2_5_row_4_0_3
  · exact left1Middle3_eq_case_2_5_row_5_0_0
  · exact left1Middle3_eq_case_2_5_row_5_0_1
  · exact left1Middle3_eq_case_2_5_row_5_0_2
  · exact left1Middle3_eq_case_2_5_row_5_0_3
  · exact left1Middle3_eq_case_2_5_row_6_0_0
  · exact left1Middle3_eq_case_2_5_row_6_0_1
  · exact left1Middle3_eq_case_2_5_row_6_0_2
  · exact left1Middle3_eq_case_2_5_row_6_0_3
  · exact left1Middle3_eq_case_2_5_row_7_0_0
  · exact left1Middle3_eq_case_2_5_row_7_0_1
  · exact left1Middle3_eq_case_2_5_row_7_0_2
  · exact left1Middle3_eq_case_2_5_row_7_0_3

set_option backward.isDefEq.respectTransparency false in
theorem left1Middle3_eq_case_2_5 : left1Middle3 2 5 = associatorZ 2 3 5 * innerLeftZ 3 2 5 := by
  simpa only [HexagonAtoms325.assocABC_eq,
    HexagonAtoms325.outerABC_eq,
    HexagonAtoms325.assocBAC_eq,
    HexagonAtoms325.innerABC_eq,
    HexagonAtoms325.innerRightABC_eq,
    HexagonAtoms325.inverseACB_eq,
    HexagonAtoms325.innerACB_eq,
    HexagonAtoms325.assocBCA_eq,
    HexagonAtoms325.innerRightBAC_eq,
    HexagonAtoms325.assocCAB_eq,
    HexagonAtoms325.outerLeftABC_eq,
    HexagonRowColumn325.product0_eq,
    HexagonRowColumn325.product1_eq,
    HexagonRowColumn325.product2_eq,
    HexagonRowColumn325.product3_eq,
    HexagonRowColumn325.product4_eq,
    HexagonRowColumn325.product5_eq,
    HexagonRowColumn325.product6_eq,
    HexagonRowColumn325.product7_eq] using left1Middle3_eq_case_2_5_checked

private theorem right0Middle3_eq_case_2_5_row_0_0_0 : (right0Middle3 2 5) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms325.assocABC) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_2_5_row_0_0_1 : (right0Middle3 2 5) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms325.assocABC) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_2_5_row_0_0_2 : (right0Middle3 2 5) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms325.assocABC) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_2_5_row_0_0_3 : (right0Middle3 2 5) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms325.assocABC) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_2_5_row_0_1_0 : (right0Middle3 2 5) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms325.assocABC) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_2_5_row_0_1_1 : (right0Middle3 2 5) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms325.assocABC) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_2_5_row_0_1_2 : (right0Middle3 2 5) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms325.assocABC) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_2_5_row_0_1_3 : (right0Middle3 2 5) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms325.assocABC) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_2_5_row_1_0_0 : (right0Middle3 2 5) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms325.assocABC) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_2_5_row_1_0_1 : (right0Middle3 2 5) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms325.assocABC) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_2_5_row_1_0_2 : (right0Middle3 2 5) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms325.assocABC) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_2_5_row_1_0_3 : (right0Middle3 2 5) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms325.assocABC) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_2_5_row_1_1_0 : (right0Middle3 2 5) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms325.assocABC) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_2_5_row_1_1_1 : (right0Middle3 2 5) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms325.assocABC) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_2_5_row_1_1_2 : (right0Middle3 2 5) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms325.assocABC) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_2_5_row_1_1_3 : (right0Middle3 2 5) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms325.assocABC) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_2_5_row_2_0_0 : (right0Middle3 2 5) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms325.assocABC) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_2_5_row_2_0_1 : (right0Middle3 2 5) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms325.assocABC) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_2_5_row_2_0_2 : (right0Middle3 2 5) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms325.assocABC) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_2_5_row_2_0_3 : (right0Middle3 2 5) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms325.assocABC) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_2_5_row_2_1_0 : (right0Middle3 2 5) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms325.assocABC) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_2_5_row_2_1_1 : (right0Middle3 2 5) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms325.assocABC) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_2_5_row_2_1_2 : (right0Middle3 2 5) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms325.assocABC) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_2_5_row_2_1_3 : (right0Middle3 2 5) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms325.assocABC) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_2_5_row_3_0_0 : (right0Middle3 2 5) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms325.assocABC) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_2_5_row_3_0_1 : (right0Middle3 2 5) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms325.assocABC) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_2_5_row_3_0_2 : (right0Middle3 2 5) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms325.assocABC) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_2_5_row_3_0_3 : (right0Middle3 2 5) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms325.assocABC) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_2_5_row_3_1_0 : (right0Middle3 2 5) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms325.assocABC) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_2_5_row_3_1_1 : (right0Middle3 2 5) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms325.assocABC) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_2_5_row_3_1_2 : (right0Middle3 2 5) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms325.assocABC) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_2_5_row_3_1_3 : (right0Middle3 2 5) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms325.assocABC) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_2_5_checked : right0Middle3 2 5 = HexagonAtoms325.assocABC := by
  funext r
  fin_cases r
  · exact right0Middle3_eq_case_2_5_row_0_0_0
  · exact right0Middle3_eq_case_2_5_row_0_0_1
  · exact right0Middle3_eq_case_2_5_row_0_0_2
  · exact right0Middle3_eq_case_2_5_row_0_0_3
  · exact right0Middle3_eq_case_2_5_row_0_1_0
  · exact right0Middle3_eq_case_2_5_row_0_1_1
  · exact right0Middle3_eq_case_2_5_row_0_1_2
  · exact right0Middle3_eq_case_2_5_row_0_1_3
  · exact right0Middle3_eq_case_2_5_row_1_0_0
  · exact right0Middle3_eq_case_2_5_row_1_0_1
  · exact right0Middle3_eq_case_2_5_row_1_0_2
  · exact right0Middle3_eq_case_2_5_row_1_0_3
  · exact right0Middle3_eq_case_2_5_row_1_1_0
  · exact right0Middle3_eq_case_2_5_row_1_1_1
  · exact right0Middle3_eq_case_2_5_row_1_1_2
  · exact right0Middle3_eq_case_2_5_row_1_1_3
  · exact right0Middle3_eq_case_2_5_row_2_0_0
  · exact right0Middle3_eq_case_2_5_row_2_0_1
  · exact right0Middle3_eq_case_2_5_row_2_0_2
  · exact right0Middle3_eq_case_2_5_row_2_0_3
  · exact right0Middle3_eq_case_2_5_row_2_1_0
  · exact right0Middle3_eq_case_2_5_row_2_1_1
  · exact right0Middle3_eq_case_2_5_row_2_1_2
  · exact right0Middle3_eq_case_2_5_row_2_1_3
  · exact right0Middle3_eq_case_2_5_row_3_0_0
  · exact right0Middle3_eq_case_2_5_row_3_0_1
  · exact right0Middle3_eq_case_2_5_row_3_0_2
  · exact right0Middle3_eq_case_2_5_row_3_0_3
  · exact right0Middle3_eq_case_2_5_row_3_1_0
  · exact right0Middle3_eq_case_2_5_row_3_1_1
  · exact right0Middle3_eq_case_2_5_row_3_1_2
  · exact right0Middle3_eq_case_2_5_row_3_1_3

set_option backward.isDefEq.respectTransparency false in
theorem right0Middle3_eq_case_2_5 : right0Middle3 2 5 = innerRightZ 3 2 5 * associatorZ 3 2 5 := by
  simpa only [HexagonAtoms325.assocABC_eq,
    HexagonAtoms325.outerABC_eq,
    HexagonAtoms325.assocBAC_eq,
    HexagonAtoms325.innerABC_eq,
    HexagonAtoms325.innerRightABC_eq,
    HexagonAtoms325.inverseACB_eq,
    HexagonAtoms325.innerACB_eq,
    HexagonAtoms325.assocBCA_eq,
    HexagonAtoms325.innerRightBAC_eq,
    HexagonAtoms325.assocCAB_eq,
    HexagonAtoms325.outerLeftABC_eq,
    HexagonRowColumn325.product0_eq,
    HexagonRowColumn325.product1_eq,
    HexagonRowColumn325.product2_eq,
    HexagonRowColumn325.product3_eq,
    HexagonRowColumn325.product4_eq,
    HexagonRowColumn325.product5_eq,
    HexagonRowColumn325.product6_eq,
    HexagonRowColumn325.product7_eq] using right0Middle3_eq_case_2_5_checked

private theorem right1Middle3_eq_case_2_5_row_0_0_0 : (right1Middle3 2 5) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn325.rows_inverseACB HexagonRowColumn325.cols_right0) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_2_5_row_0_0_1 : (right1Middle3 2 5) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn325.rows_inverseACB HexagonRowColumn325.cols_right0) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_2_5_row_0_0_2 : (right1Middle3 2 5) ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn325.rows_inverseACB HexagonRowColumn325.cols_right0) ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_2_5_row_0_0_3 : (right1Middle3 2 5) ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn325.rows_inverseACB HexagonRowColumn325.cols_right0) ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_2_5_row_1_0_0 : (right1Middle3 2 5) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn325.rows_inverseACB HexagonRowColumn325.cols_right0) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_2_5_row_1_0_1 : (right1Middle3 2 5) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn325.rows_inverseACB HexagonRowColumn325.cols_right0) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_2_5_row_1_0_2 : (right1Middle3 2 5) ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn325.rows_inverseACB HexagonRowColumn325.cols_right0) ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_2_5_row_1_0_3 : (right1Middle3 2 5) ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn325.rows_inverseACB HexagonRowColumn325.cols_right0) ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_2_5_row_2_0_0 : (right1Middle3 2 5) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn325.rows_inverseACB HexagonRowColumn325.cols_right0) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_2_5_row_2_0_1 : (right1Middle3 2 5) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn325.rows_inverseACB HexagonRowColumn325.cols_right0) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_2_5_row_2_0_2 : (right1Middle3 2 5) ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn325.rows_inverseACB HexagonRowColumn325.cols_right0) ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_2_5_row_2_0_3 : (right1Middle3 2 5) ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn325.rows_inverseACB HexagonRowColumn325.cols_right0) ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_2_5_row_3_0_0 : (right1Middle3 2 5) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn325.rows_inverseACB HexagonRowColumn325.cols_right0) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_2_5_row_3_0_1 : (right1Middle3 2 5) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn325.rows_inverseACB HexagonRowColumn325.cols_right0) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_2_5_row_3_0_2 : (right1Middle3 2 5) ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn325.rows_inverseACB HexagonRowColumn325.cols_right0) ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_2_5_row_3_0_3 : (right1Middle3 2 5) ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn325.rows_inverseACB HexagonRowColumn325.cols_right0) ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_2_5_row_4_0_0 : (right1Middle3 2 5) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn325.rows_inverseACB HexagonRowColumn325.cols_right0) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_2_5_row_4_0_1 : (right1Middle3 2 5) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn325.rows_inverseACB HexagonRowColumn325.cols_right0) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_2_5_row_4_0_2 : (right1Middle3 2 5) ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn325.rows_inverseACB HexagonRowColumn325.cols_right0) ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_2_5_row_4_0_3 : (right1Middle3 2 5) ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn325.rows_inverseACB HexagonRowColumn325.cols_right0) ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_2_5_row_5_0_0 : (right1Middle3 2 5) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn325.rows_inverseACB HexagonRowColumn325.cols_right0) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_2_5_row_5_0_1 : (right1Middle3 2 5) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn325.rows_inverseACB HexagonRowColumn325.cols_right0) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_2_5_row_5_0_2 : (right1Middle3 2 5) ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn325.rows_inverseACB HexagonRowColumn325.cols_right0) ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_2_5_row_5_0_3 : (right1Middle3 2 5) ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn325.rows_inverseACB HexagonRowColumn325.cols_right0) ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_2_5_row_6_0_0 : (right1Middle3 2 5) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn325.rows_inverseACB HexagonRowColumn325.cols_right0) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_2_5_row_6_0_1 : (right1Middle3 2 5) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn325.rows_inverseACB HexagonRowColumn325.cols_right0) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_2_5_row_6_0_2 : (right1Middle3 2 5) ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn325.rows_inverseACB HexagonRowColumn325.cols_right0) ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_2_5_row_6_0_3 : (right1Middle3 2 5) ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn325.rows_inverseACB HexagonRowColumn325.cols_right0) ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_2_5_row_7_0_0 : (right1Middle3 2 5) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn325.rows_inverseACB HexagonRowColumn325.cols_right0) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_2_5_row_7_0_1 : (right1Middle3 2 5) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn325.rows_inverseACB HexagonRowColumn325.cols_right0) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_2_5_row_7_0_2 : (right1Middle3 2 5) ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn325.rows_inverseACB HexagonRowColumn325.cols_right0) ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_2_5_row_7_0_3 : (right1Middle3 2 5) ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn325.rows_inverseACB HexagonRowColumn325.cols_right0) ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_2_5_checked : right1Middle3 2 5 = rowColumnMul HexagonRowColumn325.rows_inverseACB HexagonRowColumn325.cols_right0 := by
  funext r
  fin_cases r
  · exact right1Middle3_eq_case_2_5_row_0_0_0
  · exact right1Middle3_eq_case_2_5_row_0_0_1
  · exact right1Middle3_eq_case_2_5_row_0_0_2
  · exact right1Middle3_eq_case_2_5_row_0_0_3
  · exact right1Middle3_eq_case_2_5_row_1_0_0
  · exact right1Middle3_eq_case_2_5_row_1_0_1
  · exact right1Middle3_eq_case_2_5_row_1_0_2
  · exact right1Middle3_eq_case_2_5_row_1_0_3
  · exact right1Middle3_eq_case_2_5_row_2_0_0
  · exact right1Middle3_eq_case_2_5_row_2_0_1
  · exact right1Middle3_eq_case_2_5_row_2_0_2
  · exact right1Middle3_eq_case_2_5_row_2_0_3
  · exact right1Middle3_eq_case_2_5_row_3_0_0
  · exact right1Middle3_eq_case_2_5_row_3_0_1
  · exact right1Middle3_eq_case_2_5_row_3_0_2
  · exact right1Middle3_eq_case_2_5_row_3_0_3
  · exact right1Middle3_eq_case_2_5_row_4_0_0
  · exact right1Middle3_eq_case_2_5_row_4_0_1
  · exact right1Middle3_eq_case_2_5_row_4_0_2
  · exact right1Middle3_eq_case_2_5_row_4_0_3
  · exact right1Middle3_eq_case_2_5_row_5_0_0
  · exact right1Middle3_eq_case_2_5_row_5_0_1
  · exact right1Middle3_eq_case_2_5_row_5_0_2
  · exact right1Middle3_eq_case_2_5_row_5_0_3
  · exact right1Middle3_eq_case_2_5_row_6_0_0
  · exact right1Middle3_eq_case_2_5_row_6_0_1
  · exact right1Middle3_eq_case_2_5_row_6_0_2
  · exact right1Middle3_eq_case_2_5_row_6_0_3
  · exact right1Middle3_eq_case_2_5_row_7_0_0
  · exact right1Middle3_eq_case_2_5_row_7_0_1
  · exact right1Middle3_eq_case_2_5_row_7_0_2
  · exact right1Middle3_eq_case_2_5_row_7_0_3

set_option backward.isDefEq.respectTransparency false in
theorem right1Middle3_eq_case_2_5 : right1Middle3 2 5 = associatorInverseZ 3 5 2 * right0Middle3 2 5 := by
  simpa only [HexagonAtoms325.assocABC_eq,
    HexagonAtoms325.outerABC_eq,
    HexagonAtoms325.assocBAC_eq,
    HexagonAtoms325.innerABC_eq,
    HexagonAtoms325.innerRightABC_eq,
    HexagonAtoms325.inverseACB_eq,
    HexagonAtoms325.innerACB_eq,
    HexagonAtoms325.assocBCA_eq,
    HexagonAtoms325.innerRightBAC_eq,
    HexagonAtoms325.assocCAB_eq,
    HexagonAtoms325.outerLeftABC_eq,
    HexagonRowColumn325.product0_eq,
    HexagonRowColumn325.product1_eq,
    HexagonRowColumn325.product2_eq,
    HexagonRowColumn325.product3_eq,
    HexagonRowColumn325.product4_eq,
    HexagonRowColumn325.product5_eq,
    HexagonRowColumn325.product6_eq,
    HexagonRowColumn325.product7_eq] using right1Middle3_eq_case_2_5_checked

private theorem right2Middle3_eq_case_2_5_row_0_0_0 : (right2Middle3 2 5) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (right1Middle3 2 5) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_2_5_row_0_0_1 : (right2Middle3 2 5) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (right1Middle3 2 5) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_2_5_row_0_0_2 : (right2Middle3 2 5) ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (right1Middle3 2 5) ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_2_5_row_0_0_3 : (right2Middle3 2 5) ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (right1Middle3 2 5) ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_2_5_row_1_0_0 : (right2Middle3 2 5) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (right1Middle3 2 5) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_2_5_row_1_0_1 : (right2Middle3 2 5) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (right1Middle3 2 5) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_2_5_row_1_0_2 : (right2Middle3 2 5) ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (right1Middle3 2 5) ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_2_5_row_1_0_3 : (right2Middle3 2 5) ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (right1Middle3 2 5) ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_2_5_row_2_0_0 : (right2Middle3 2 5) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (right1Middle3 2 5) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_2_5_row_2_0_1 : (right2Middle3 2 5) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (right1Middle3 2 5) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_2_5_row_2_0_2 : (right2Middle3 2 5) ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (right1Middle3 2 5) ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_2_5_row_2_0_3 : (right2Middle3 2 5) ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (right1Middle3 2 5) ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_2_5_row_3_0_0 : (right2Middle3 2 5) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (right1Middle3 2 5) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_2_5_row_3_0_1 : (right2Middle3 2 5) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (right1Middle3 2 5) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_2_5_row_3_0_2 : (right2Middle3 2 5) ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (right1Middle3 2 5) ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_2_5_row_3_0_3 : (right2Middle3 2 5) ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (right1Middle3 2 5) ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_2_5_row_4_0_0 : (right2Middle3 2 5) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (right1Middle3 2 5) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_2_5_row_4_0_1 : (right2Middle3 2 5) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (right1Middle3 2 5) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_2_5_row_4_0_2 : (right2Middle3 2 5) ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (right1Middle3 2 5) ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_2_5_row_4_0_3 : (right2Middle3 2 5) ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (right1Middle3 2 5) ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_2_5_row_5_0_0 : (right2Middle3 2 5) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (right1Middle3 2 5) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_2_5_row_5_0_1 : (right2Middle3 2 5) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (right1Middle3 2 5) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_2_5_row_5_0_2 : (right2Middle3 2 5) ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (right1Middle3 2 5) ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_2_5_row_5_0_3 : (right2Middle3 2 5) ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (right1Middle3 2 5) ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_2_5_row_6_0_0 : (right2Middle3 2 5) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (right1Middle3 2 5) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_2_5_row_6_0_1 : (right2Middle3 2 5) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (right1Middle3 2 5) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_2_5_row_6_0_2 : (right2Middle3 2 5) ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (right1Middle3 2 5) ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_2_5_row_6_0_3 : (right2Middle3 2 5) ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (right1Middle3 2 5) ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_2_5_row_7_0_0 : (right2Middle3 2 5) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (right1Middle3 2 5) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_2_5_row_7_0_1 : (right2Middle3 2 5) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (right1Middle3 2 5) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_2_5_row_7_0_2 : (right2Middle3 2 5) ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (right1Middle3 2 5) ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_2_5_row_7_0_3 : (right2Middle3 2 5) ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (right1Middle3 2 5) ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_2_5_checked : right2Middle3 2 5 = right1Middle3 2 5 := by
  funext r
  fin_cases r
  · exact right2Middle3_eq_case_2_5_row_0_0_0
  · exact right2Middle3_eq_case_2_5_row_0_0_1
  · exact right2Middle3_eq_case_2_5_row_0_0_2
  · exact right2Middle3_eq_case_2_5_row_0_0_3
  · exact right2Middle3_eq_case_2_5_row_1_0_0
  · exact right2Middle3_eq_case_2_5_row_1_0_1
  · exact right2Middle3_eq_case_2_5_row_1_0_2
  · exact right2Middle3_eq_case_2_5_row_1_0_3
  · exact right2Middle3_eq_case_2_5_row_2_0_0
  · exact right2Middle3_eq_case_2_5_row_2_0_1
  · exact right2Middle3_eq_case_2_5_row_2_0_2
  · exact right2Middle3_eq_case_2_5_row_2_0_3
  · exact right2Middle3_eq_case_2_5_row_3_0_0
  · exact right2Middle3_eq_case_2_5_row_3_0_1
  · exact right2Middle3_eq_case_2_5_row_3_0_2
  · exact right2Middle3_eq_case_2_5_row_3_0_3
  · exact right2Middle3_eq_case_2_5_row_4_0_0
  · exact right2Middle3_eq_case_2_5_row_4_0_1
  · exact right2Middle3_eq_case_2_5_row_4_0_2
  · exact right2Middle3_eq_case_2_5_row_4_0_3
  · exact right2Middle3_eq_case_2_5_row_5_0_0
  · exact right2Middle3_eq_case_2_5_row_5_0_1
  · exact right2Middle3_eq_case_2_5_row_5_0_2
  · exact right2Middle3_eq_case_2_5_row_5_0_3
  · exact right2Middle3_eq_case_2_5_row_6_0_0
  · exact right2Middle3_eq_case_2_5_row_6_0_1
  · exact right2Middle3_eq_case_2_5_row_6_0_2
  · exact right2Middle3_eq_case_2_5_row_6_0_3
  · exact right2Middle3_eq_case_2_5_row_7_0_0
  · exact right2Middle3_eq_case_2_5_row_7_0_1
  · exact right2Middle3_eq_case_2_5_row_7_0_2
  · exact right2Middle3_eq_case_2_5_row_7_0_3

set_option backward.isDefEq.respectTransparency false in
theorem right2Middle3_eq_case_2_5 : right2Middle3 2 5 = innerLeftZ 3 5 2 * right1Middle3 2 5 := by
  simpa only [HexagonAtoms325.assocABC_eq,
    HexagonAtoms325.outerABC_eq,
    HexagonAtoms325.assocBAC_eq,
    HexagonAtoms325.innerABC_eq,
    HexagonAtoms325.innerRightABC_eq,
    HexagonAtoms325.inverseACB_eq,
    HexagonAtoms325.innerACB_eq,
    HexagonAtoms325.assocBCA_eq,
    HexagonAtoms325.innerRightBAC_eq,
    HexagonAtoms325.assocCAB_eq,
    HexagonAtoms325.outerLeftABC_eq,
    HexagonRowColumn325.product0_eq,
    HexagonRowColumn325.product1_eq,
    HexagonRowColumn325.product2_eq,
    HexagonRowColumn325.product3_eq,
    HexagonRowColumn325.product4_eq,
    HexagonRowColumn325.product5_eq,
    HexagonRowColumn325.product6_eq,
    HexagonRowColumn325.product7_eq] using right2Middle3_eq_case_2_5_checked

private theorem leftFinal3_case_2_5_row_0_0_0 : (((-1 : ℤ) ^ (leftScaleBit 3 2 5).val * positiveScale (leftScaleExponent 3 2 5)) •
      (rowColumnMul HexagonRowColumn325.rows_assocBCA HexagonRowColumn325.cols_left0)) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (negativeScale (leftScaleExponent 3 2 5) • (left1Middle3 2 5)) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem leftFinal3_case_2_5_row_0_0_1 : (((-1 : ℤ) ^ (leftScaleBit 3 2 5).val * positiveScale (leftScaleExponent 3 2 5)) •
      (rowColumnMul HexagonRowColumn325.rows_assocBCA HexagonRowColumn325.cols_left0)) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (negativeScale (leftScaleExponent 3 2 5) • (left1Middle3 2 5)) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem leftFinal3_case_2_5_row_0_0_2 : (((-1 : ℤ) ^ (leftScaleBit 3 2 5).val * positiveScale (leftScaleExponent 3 2 5)) •
      (rowColumnMul HexagonRowColumn325.rows_assocBCA HexagonRowColumn325.cols_left0)) ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (negativeScale (leftScaleExponent 3 2 5) • (left1Middle3 2 5)) ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem leftFinal3_case_2_5_row_0_0_3 : (((-1 : ℤ) ^ (leftScaleBit 3 2 5).val * positiveScale (leftScaleExponent 3 2 5)) •
      (rowColumnMul HexagonRowColumn325.rows_assocBCA HexagonRowColumn325.cols_left0)) ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (negativeScale (leftScaleExponent 3 2 5) • (left1Middle3 2 5)) ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem leftFinal3_case_2_5_row_1_0_0 : (((-1 : ℤ) ^ (leftScaleBit 3 2 5).val * positiveScale (leftScaleExponent 3 2 5)) •
      (rowColumnMul HexagonRowColumn325.rows_assocBCA HexagonRowColumn325.cols_left0)) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (negativeScale (leftScaleExponent 3 2 5) • (left1Middle3 2 5)) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem leftFinal3_case_2_5_row_1_0_1 : (((-1 : ℤ) ^ (leftScaleBit 3 2 5).val * positiveScale (leftScaleExponent 3 2 5)) •
      (rowColumnMul HexagonRowColumn325.rows_assocBCA HexagonRowColumn325.cols_left0)) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (negativeScale (leftScaleExponent 3 2 5) • (left1Middle3 2 5)) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem leftFinal3_case_2_5_row_1_0_2 : (((-1 : ℤ) ^ (leftScaleBit 3 2 5).val * positiveScale (leftScaleExponent 3 2 5)) •
      (rowColumnMul HexagonRowColumn325.rows_assocBCA HexagonRowColumn325.cols_left0)) ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (negativeScale (leftScaleExponent 3 2 5) • (left1Middle3 2 5)) ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem leftFinal3_case_2_5_row_1_0_3 : (((-1 : ℤ) ^ (leftScaleBit 3 2 5).val * positiveScale (leftScaleExponent 3 2 5)) •
      (rowColumnMul HexagonRowColumn325.rows_assocBCA HexagonRowColumn325.cols_left0)) ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (negativeScale (leftScaleExponent 3 2 5) • (left1Middle3 2 5)) ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem leftFinal3_case_2_5_row_2_0_0 : (((-1 : ℤ) ^ (leftScaleBit 3 2 5).val * positiveScale (leftScaleExponent 3 2 5)) •
      (rowColumnMul HexagonRowColumn325.rows_assocBCA HexagonRowColumn325.cols_left0)) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (negativeScale (leftScaleExponent 3 2 5) • (left1Middle3 2 5)) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem leftFinal3_case_2_5_row_2_0_1 : (((-1 : ℤ) ^ (leftScaleBit 3 2 5).val * positiveScale (leftScaleExponent 3 2 5)) •
      (rowColumnMul HexagonRowColumn325.rows_assocBCA HexagonRowColumn325.cols_left0)) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (negativeScale (leftScaleExponent 3 2 5) • (left1Middle3 2 5)) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem leftFinal3_case_2_5_row_2_0_2 : (((-1 : ℤ) ^ (leftScaleBit 3 2 5).val * positiveScale (leftScaleExponent 3 2 5)) •
      (rowColumnMul HexagonRowColumn325.rows_assocBCA HexagonRowColumn325.cols_left0)) ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (negativeScale (leftScaleExponent 3 2 5) • (left1Middle3 2 5)) ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem leftFinal3_case_2_5_row_2_0_3 : (((-1 : ℤ) ^ (leftScaleBit 3 2 5).val * positiveScale (leftScaleExponent 3 2 5)) •
      (rowColumnMul HexagonRowColumn325.rows_assocBCA HexagonRowColumn325.cols_left0)) ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (negativeScale (leftScaleExponent 3 2 5) • (left1Middle3 2 5)) ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem leftFinal3_case_2_5_row_3_0_0 : (((-1 : ℤ) ^ (leftScaleBit 3 2 5).val * positiveScale (leftScaleExponent 3 2 5)) •
      (rowColumnMul HexagonRowColumn325.rows_assocBCA HexagonRowColumn325.cols_left0)) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (negativeScale (leftScaleExponent 3 2 5) • (left1Middle3 2 5)) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem leftFinal3_case_2_5_row_3_0_1 : (((-1 : ℤ) ^ (leftScaleBit 3 2 5).val * positiveScale (leftScaleExponent 3 2 5)) •
      (rowColumnMul HexagonRowColumn325.rows_assocBCA HexagonRowColumn325.cols_left0)) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (negativeScale (leftScaleExponent 3 2 5) • (left1Middle3 2 5)) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem leftFinal3_case_2_5_row_3_0_2 : (((-1 : ℤ) ^ (leftScaleBit 3 2 5).val * positiveScale (leftScaleExponent 3 2 5)) •
      (rowColumnMul HexagonRowColumn325.rows_assocBCA HexagonRowColumn325.cols_left0)) ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (negativeScale (leftScaleExponent 3 2 5) • (left1Middle3 2 5)) ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem leftFinal3_case_2_5_row_3_0_3 : (((-1 : ℤ) ^ (leftScaleBit 3 2 5).val * positiveScale (leftScaleExponent 3 2 5)) •
      (rowColumnMul HexagonRowColumn325.rows_assocBCA HexagonRowColumn325.cols_left0)) ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (negativeScale (leftScaleExponent 3 2 5) • (left1Middle3 2 5)) ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem leftFinal3_case_2_5_row_4_0_0 : (((-1 : ℤ) ^ (leftScaleBit 3 2 5).val * positiveScale (leftScaleExponent 3 2 5)) •
      (rowColumnMul HexagonRowColumn325.rows_assocBCA HexagonRowColumn325.cols_left0)) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (negativeScale (leftScaleExponent 3 2 5) • (left1Middle3 2 5)) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem leftFinal3_case_2_5_row_4_0_1 : (((-1 : ℤ) ^ (leftScaleBit 3 2 5).val * positiveScale (leftScaleExponent 3 2 5)) •
      (rowColumnMul HexagonRowColumn325.rows_assocBCA HexagonRowColumn325.cols_left0)) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (negativeScale (leftScaleExponent 3 2 5) • (left1Middle3 2 5)) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem leftFinal3_case_2_5_row_4_0_2 : (((-1 : ℤ) ^ (leftScaleBit 3 2 5).val * positiveScale (leftScaleExponent 3 2 5)) •
      (rowColumnMul HexagonRowColumn325.rows_assocBCA HexagonRowColumn325.cols_left0)) ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (negativeScale (leftScaleExponent 3 2 5) • (left1Middle3 2 5)) ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem leftFinal3_case_2_5_row_4_0_3 : (((-1 : ℤ) ^ (leftScaleBit 3 2 5).val * positiveScale (leftScaleExponent 3 2 5)) •
      (rowColumnMul HexagonRowColumn325.rows_assocBCA HexagonRowColumn325.cols_left0)) ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (negativeScale (leftScaleExponent 3 2 5) • (left1Middle3 2 5)) ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem leftFinal3_case_2_5_row_5_0_0 : (((-1 : ℤ) ^ (leftScaleBit 3 2 5).val * positiveScale (leftScaleExponent 3 2 5)) •
      (rowColumnMul HexagonRowColumn325.rows_assocBCA HexagonRowColumn325.cols_left0)) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (negativeScale (leftScaleExponent 3 2 5) • (left1Middle3 2 5)) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem leftFinal3_case_2_5_row_5_0_1 : (((-1 : ℤ) ^ (leftScaleBit 3 2 5).val * positiveScale (leftScaleExponent 3 2 5)) •
      (rowColumnMul HexagonRowColumn325.rows_assocBCA HexagonRowColumn325.cols_left0)) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (negativeScale (leftScaleExponent 3 2 5) • (left1Middle3 2 5)) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem leftFinal3_case_2_5_row_5_0_2 : (((-1 : ℤ) ^ (leftScaleBit 3 2 5).val * positiveScale (leftScaleExponent 3 2 5)) •
      (rowColumnMul HexagonRowColumn325.rows_assocBCA HexagonRowColumn325.cols_left0)) ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (negativeScale (leftScaleExponent 3 2 5) • (left1Middle3 2 5)) ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem leftFinal3_case_2_5_row_5_0_3 : (((-1 : ℤ) ^ (leftScaleBit 3 2 5).val * positiveScale (leftScaleExponent 3 2 5)) •
      (rowColumnMul HexagonRowColumn325.rows_assocBCA HexagonRowColumn325.cols_left0)) ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (negativeScale (leftScaleExponent 3 2 5) • (left1Middle3 2 5)) ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem leftFinal3_case_2_5_row_6_0_0 : (((-1 : ℤ) ^ (leftScaleBit 3 2 5).val * positiveScale (leftScaleExponent 3 2 5)) •
      (rowColumnMul HexagonRowColumn325.rows_assocBCA HexagonRowColumn325.cols_left0)) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (negativeScale (leftScaleExponent 3 2 5) • (left1Middle3 2 5)) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem leftFinal3_case_2_5_row_6_0_1 : (((-1 : ℤ) ^ (leftScaleBit 3 2 5).val * positiveScale (leftScaleExponent 3 2 5)) •
      (rowColumnMul HexagonRowColumn325.rows_assocBCA HexagonRowColumn325.cols_left0)) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (negativeScale (leftScaleExponent 3 2 5) • (left1Middle3 2 5)) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem leftFinal3_case_2_5_row_6_0_2 : (((-1 : ℤ) ^ (leftScaleBit 3 2 5).val * positiveScale (leftScaleExponent 3 2 5)) •
      (rowColumnMul HexagonRowColumn325.rows_assocBCA HexagonRowColumn325.cols_left0)) ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (negativeScale (leftScaleExponent 3 2 5) • (left1Middle3 2 5)) ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem leftFinal3_case_2_5_row_6_0_3 : (((-1 : ℤ) ^ (leftScaleBit 3 2 5).val * positiveScale (leftScaleExponent 3 2 5)) •
      (rowColumnMul HexagonRowColumn325.rows_assocBCA HexagonRowColumn325.cols_left0)) ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (negativeScale (leftScaleExponent 3 2 5) • (left1Middle3 2 5)) ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem leftFinal3_case_2_5_row_7_0_0 : (((-1 : ℤ) ^ (leftScaleBit 3 2 5).val * positiveScale (leftScaleExponent 3 2 5)) •
      (rowColumnMul HexagonRowColumn325.rows_assocBCA HexagonRowColumn325.cols_left0)) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (negativeScale (leftScaleExponent 3 2 5) • (left1Middle3 2 5)) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem leftFinal3_case_2_5_row_7_0_1 : (((-1 : ℤ) ^ (leftScaleBit 3 2 5).val * positiveScale (leftScaleExponent 3 2 5)) •
      (rowColumnMul HexagonRowColumn325.rows_assocBCA HexagonRowColumn325.cols_left0)) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (negativeScale (leftScaleExponent 3 2 5) • (left1Middle3 2 5)) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem leftFinal3_case_2_5_row_7_0_2 : (((-1 : ℤ) ^ (leftScaleBit 3 2 5).val * positiveScale (leftScaleExponent 3 2 5)) •
      (rowColumnMul HexagonRowColumn325.rows_assocBCA HexagonRowColumn325.cols_left0)) ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (negativeScale (leftScaleExponent 3 2 5) • (left1Middle3 2 5)) ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem leftFinal3_case_2_5_row_7_0_3 : (((-1 : ℤ) ^ (leftScaleBit 3 2 5).val * positiveScale (leftScaleExponent 3 2 5)) •
      (rowColumnMul HexagonRowColumn325.rows_assocBCA HexagonRowColumn325.cols_left0)) ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (negativeScale (leftScaleExponent 3 2 5) • (left1Middle3 2 5)) ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem leftFinal3_case_2_5_checked : ((-1 : ℤ) ^ (leftScaleBit 3 2 5).val * positiveScale (leftScaleExponent 3 2 5)) •
      (rowColumnMul HexagonRowColumn325.rows_assocBCA HexagonRowColumn325.cols_left0) = negativeScale (leftScaleExponent 3 2 5) • (left1Middle3 2 5) := by
  funext r
  fin_cases r
  · exact leftFinal3_case_2_5_row_0_0_0
  · exact leftFinal3_case_2_5_row_0_0_1
  · exact leftFinal3_case_2_5_row_0_0_2
  · exact leftFinal3_case_2_5_row_0_0_3
  · exact leftFinal3_case_2_5_row_1_0_0
  · exact leftFinal3_case_2_5_row_1_0_1
  · exact leftFinal3_case_2_5_row_1_0_2
  · exact leftFinal3_case_2_5_row_1_0_3
  · exact leftFinal3_case_2_5_row_2_0_0
  · exact leftFinal3_case_2_5_row_2_0_1
  · exact leftFinal3_case_2_5_row_2_0_2
  · exact leftFinal3_case_2_5_row_2_0_3
  · exact leftFinal3_case_2_5_row_3_0_0
  · exact leftFinal3_case_2_5_row_3_0_1
  · exact leftFinal3_case_2_5_row_3_0_2
  · exact leftFinal3_case_2_5_row_3_0_3
  · exact leftFinal3_case_2_5_row_4_0_0
  · exact leftFinal3_case_2_5_row_4_0_1
  · exact leftFinal3_case_2_5_row_4_0_2
  · exact leftFinal3_case_2_5_row_4_0_3
  · exact leftFinal3_case_2_5_row_5_0_0
  · exact leftFinal3_case_2_5_row_5_0_1
  · exact leftFinal3_case_2_5_row_5_0_2
  · exact leftFinal3_case_2_5_row_5_0_3
  · exact leftFinal3_case_2_5_row_6_0_0
  · exact leftFinal3_case_2_5_row_6_0_1
  · exact leftFinal3_case_2_5_row_6_0_2
  · exact leftFinal3_case_2_5_row_6_0_3
  · exact leftFinal3_case_2_5_row_7_0_0
  · exact leftFinal3_case_2_5_row_7_0_1
  · exact leftFinal3_case_2_5_row_7_0_2
  · exact leftFinal3_case_2_5_row_7_0_3

set_option backward.isDefEq.respectTransparency false in
theorem leftFinal3_case_2_5 : ((-1 : ℤ) ^ (leftScaleBit 3 2 5).val * positiveScale (leftScaleExponent 3 2 5)) •
      (associatorZ 2 5 3 * left0Middle3 2 5) = negativeScale (leftScaleExponent 3 2 5) • (innerRightZ 2 3 5 * left1Middle3 2 5) := by
  simpa only [HexagonAtoms325.assocABC_eq,
    HexagonAtoms325.outerABC_eq,
    HexagonAtoms325.assocBAC_eq,
    HexagonAtoms325.innerABC_eq,
    HexagonAtoms325.innerRightABC_eq,
    HexagonAtoms325.inverseACB_eq,
    HexagonAtoms325.innerACB_eq,
    HexagonAtoms325.assocBCA_eq,
    HexagonAtoms325.innerRightBAC_eq,
    HexagonAtoms325.assocCAB_eq,
    HexagonAtoms325.outerLeftABC_eq,
    HexagonRowColumn325.product0_eq,
    HexagonRowColumn325.product1_eq,
    HexagonRowColumn325.product2_eq,
    HexagonRowColumn325.product3_eq,
    HexagonRowColumn325.product4_eq,
    HexagonRowColumn325.product5_eq,
    HexagonRowColumn325.product6_eq,
    HexagonRowColumn325.product7_eq] using leftFinal3_case_2_5_checked

private theorem rightFinal3_case_2_5_row_0_0_0 : (((-1 : ℤ) ^ (rightScaleBit 3 2 5).val * positiveScale (rightScaleExponent 3 2 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 5 2 : ℤ)) • HexagonAtoms325.outerLeftABC) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 4)) = (negativeScale (rightScaleExponent 3 2 5) • (rowColumnMul HexagonRowColumn325.rows_assocCAB HexagonRowColumn325.cols_right2)) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem rightFinal3_case_2_5_row_0_0_1 : (((-1 : ℤ) ^ (rightScaleBit 3 2 5).val * positiveScale (rightScaleExponent 3 2 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 5 2 : ℤ)) • HexagonAtoms325.outerLeftABC) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 4)) = (negativeScale (rightScaleExponent 3 2 5) • (rowColumnMul HexagonRowColumn325.rows_assocCAB HexagonRowColumn325.cols_right2)) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem rightFinal3_case_2_5_row_0_0_2 : (((-1 : ℤ) ^ (rightScaleBit 3 2 5).val * positiveScale (rightScaleExponent 3 2 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 5 2 : ℤ)) • HexagonAtoms325.outerLeftABC) ((0 : Fin 2), (0 : Fin 4), (2 : Fin 4)) = (negativeScale (rightScaleExponent 3 2 5) • (rowColumnMul HexagonRowColumn325.rows_assocCAB HexagonRowColumn325.cols_right2)) ((0 : Fin 2), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem rightFinal3_case_2_5_row_0_0_3 : (((-1 : ℤ) ^ (rightScaleBit 3 2 5).val * positiveScale (rightScaleExponent 3 2 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 5 2 : ℤ)) • HexagonAtoms325.outerLeftABC) ((0 : Fin 2), (0 : Fin 4), (3 : Fin 4)) = (negativeScale (rightScaleExponent 3 2 5) • (rowColumnMul HexagonRowColumn325.rows_assocCAB HexagonRowColumn325.cols_right2)) ((0 : Fin 2), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem rightFinal3_case_2_5_row_0_1_0 : (((-1 : ℤ) ^ (rightScaleBit 3 2 5).val * positiveScale (rightScaleExponent 3 2 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 5 2 : ℤ)) • HexagonAtoms325.outerLeftABC) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 4)) = (negativeScale (rightScaleExponent 3 2 5) • (rowColumnMul HexagonRowColumn325.rows_assocCAB HexagonRowColumn325.cols_right2)) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem rightFinal3_case_2_5_row_0_1_1 : (((-1 : ℤ) ^ (rightScaleBit 3 2 5).val * positiveScale (rightScaleExponent 3 2 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 5 2 : ℤ)) • HexagonAtoms325.outerLeftABC) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 4)) = (negativeScale (rightScaleExponent 3 2 5) • (rowColumnMul HexagonRowColumn325.rows_assocCAB HexagonRowColumn325.cols_right2)) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem rightFinal3_case_2_5_row_0_1_2 : (((-1 : ℤ) ^ (rightScaleBit 3 2 5).val * positiveScale (rightScaleExponent 3 2 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 5 2 : ℤ)) • HexagonAtoms325.outerLeftABC) ((0 : Fin 2), (1 : Fin 4), (2 : Fin 4)) = (negativeScale (rightScaleExponent 3 2 5) • (rowColumnMul HexagonRowColumn325.rows_assocCAB HexagonRowColumn325.cols_right2)) ((0 : Fin 2), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem rightFinal3_case_2_5_row_0_1_3 : (((-1 : ℤ) ^ (rightScaleBit 3 2 5).val * positiveScale (rightScaleExponent 3 2 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 5 2 : ℤ)) • HexagonAtoms325.outerLeftABC) ((0 : Fin 2), (1 : Fin 4), (3 : Fin 4)) = (negativeScale (rightScaleExponent 3 2 5) • (rowColumnMul HexagonRowColumn325.rows_assocCAB HexagonRowColumn325.cols_right2)) ((0 : Fin 2), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem rightFinal3_case_2_5_row_0_2_0 : (((-1 : ℤ) ^ (rightScaleBit 3 2 5).val * positiveScale (rightScaleExponent 3 2 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 5 2 : ℤ)) • HexagonAtoms325.outerLeftABC) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 4)) = (negativeScale (rightScaleExponent 3 2 5) • (rowColumnMul HexagonRowColumn325.rows_assocCAB HexagonRowColumn325.cols_right2)) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem rightFinal3_case_2_5_row_0_2_1 : (((-1 : ℤ) ^ (rightScaleBit 3 2 5).val * positiveScale (rightScaleExponent 3 2 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 5 2 : ℤ)) • HexagonAtoms325.outerLeftABC) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 4)) = (negativeScale (rightScaleExponent 3 2 5) • (rowColumnMul HexagonRowColumn325.rows_assocCAB HexagonRowColumn325.cols_right2)) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem rightFinal3_case_2_5_row_0_2_2 : (((-1 : ℤ) ^ (rightScaleBit 3 2 5).val * positiveScale (rightScaleExponent 3 2 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 5 2 : ℤ)) • HexagonAtoms325.outerLeftABC) ((0 : Fin 2), (2 : Fin 4), (2 : Fin 4)) = (negativeScale (rightScaleExponent 3 2 5) • (rowColumnMul HexagonRowColumn325.rows_assocCAB HexagonRowColumn325.cols_right2)) ((0 : Fin 2), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem rightFinal3_case_2_5_row_0_2_3 : (((-1 : ℤ) ^ (rightScaleBit 3 2 5).val * positiveScale (rightScaleExponent 3 2 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 5 2 : ℤ)) • HexagonAtoms325.outerLeftABC) ((0 : Fin 2), (2 : Fin 4), (3 : Fin 4)) = (negativeScale (rightScaleExponent 3 2 5) • (rowColumnMul HexagonRowColumn325.rows_assocCAB HexagonRowColumn325.cols_right2)) ((0 : Fin 2), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem rightFinal3_case_2_5_row_0_3_0 : (((-1 : ℤ) ^ (rightScaleBit 3 2 5).val * positiveScale (rightScaleExponent 3 2 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 5 2 : ℤ)) • HexagonAtoms325.outerLeftABC) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 4)) = (negativeScale (rightScaleExponent 3 2 5) • (rowColumnMul HexagonRowColumn325.rows_assocCAB HexagonRowColumn325.cols_right2)) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem rightFinal3_case_2_5_row_0_3_1 : (((-1 : ℤ) ^ (rightScaleBit 3 2 5).val * positiveScale (rightScaleExponent 3 2 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 5 2 : ℤ)) • HexagonAtoms325.outerLeftABC) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 4)) = (negativeScale (rightScaleExponent 3 2 5) • (rowColumnMul HexagonRowColumn325.rows_assocCAB HexagonRowColumn325.cols_right2)) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem rightFinal3_case_2_5_row_0_3_2 : (((-1 : ℤ) ^ (rightScaleBit 3 2 5).val * positiveScale (rightScaleExponent 3 2 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 5 2 : ℤ)) • HexagonAtoms325.outerLeftABC) ((0 : Fin 2), (3 : Fin 4), (2 : Fin 4)) = (negativeScale (rightScaleExponent 3 2 5) • (rowColumnMul HexagonRowColumn325.rows_assocCAB HexagonRowColumn325.cols_right2)) ((0 : Fin 2), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem rightFinal3_case_2_5_row_0_3_3 : (((-1 : ℤ) ^ (rightScaleBit 3 2 5).val * positiveScale (rightScaleExponent 3 2 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 5 2 : ℤ)) • HexagonAtoms325.outerLeftABC) ((0 : Fin 2), (3 : Fin 4), (3 : Fin 4)) = (negativeScale (rightScaleExponent 3 2 5) • (rowColumnMul HexagonRowColumn325.rows_assocCAB HexagonRowColumn325.cols_right2)) ((0 : Fin 2), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem rightFinal3_case_2_5_row_1_0_0 : (((-1 : ℤ) ^ (rightScaleBit 3 2 5).val * positiveScale (rightScaleExponent 3 2 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 5 2 : ℤ)) • HexagonAtoms325.outerLeftABC) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 4)) = (negativeScale (rightScaleExponent 3 2 5) • (rowColumnMul HexagonRowColumn325.rows_assocCAB HexagonRowColumn325.cols_right2)) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem rightFinal3_case_2_5_row_1_0_1 : (((-1 : ℤ) ^ (rightScaleBit 3 2 5).val * positiveScale (rightScaleExponent 3 2 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 5 2 : ℤ)) • HexagonAtoms325.outerLeftABC) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 4)) = (negativeScale (rightScaleExponent 3 2 5) • (rowColumnMul HexagonRowColumn325.rows_assocCAB HexagonRowColumn325.cols_right2)) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem rightFinal3_case_2_5_row_1_0_2 : (((-1 : ℤ) ^ (rightScaleBit 3 2 5).val * positiveScale (rightScaleExponent 3 2 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 5 2 : ℤ)) • HexagonAtoms325.outerLeftABC) ((1 : Fin 2), (0 : Fin 4), (2 : Fin 4)) = (negativeScale (rightScaleExponent 3 2 5) • (rowColumnMul HexagonRowColumn325.rows_assocCAB HexagonRowColumn325.cols_right2)) ((1 : Fin 2), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem rightFinal3_case_2_5_row_1_0_3 : (((-1 : ℤ) ^ (rightScaleBit 3 2 5).val * positiveScale (rightScaleExponent 3 2 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 5 2 : ℤ)) • HexagonAtoms325.outerLeftABC) ((1 : Fin 2), (0 : Fin 4), (3 : Fin 4)) = (negativeScale (rightScaleExponent 3 2 5) • (rowColumnMul HexagonRowColumn325.rows_assocCAB HexagonRowColumn325.cols_right2)) ((1 : Fin 2), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem rightFinal3_case_2_5_row_1_1_0 : (((-1 : ℤ) ^ (rightScaleBit 3 2 5).val * positiveScale (rightScaleExponent 3 2 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 5 2 : ℤ)) • HexagonAtoms325.outerLeftABC) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 4)) = (negativeScale (rightScaleExponent 3 2 5) • (rowColumnMul HexagonRowColumn325.rows_assocCAB HexagonRowColumn325.cols_right2)) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem rightFinal3_case_2_5_row_1_1_1 : (((-1 : ℤ) ^ (rightScaleBit 3 2 5).val * positiveScale (rightScaleExponent 3 2 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 5 2 : ℤ)) • HexagonAtoms325.outerLeftABC) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 4)) = (negativeScale (rightScaleExponent 3 2 5) • (rowColumnMul HexagonRowColumn325.rows_assocCAB HexagonRowColumn325.cols_right2)) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem rightFinal3_case_2_5_row_1_1_2 : (((-1 : ℤ) ^ (rightScaleBit 3 2 5).val * positiveScale (rightScaleExponent 3 2 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 5 2 : ℤ)) • HexagonAtoms325.outerLeftABC) ((1 : Fin 2), (1 : Fin 4), (2 : Fin 4)) = (negativeScale (rightScaleExponent 3 2 5) • (rowColumnMul HexagonRowColumn325.rows_assocCAB HexagonRowColumn325.cols_right2)) ((1 : Fin 2), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem rightFinal3_case_2_5_row_1_1_3 : (((-1 : ℤ) ^ (rightScaleBit 3 2 5).val * positiveScale (rightScaleExponent 3 2 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 5 2 : ℤ)) • HexagonAtoms325.outerLeftABC) ((1 : Fin 2), (1 : Fin 4), (3 : Fin 4)) = (negativeScale (rightScaleExponent 3 2 5) • (rowColumnMul HexagonRowColumn325.rows_assocCAB HexagonRowColumn325.cols_right2)) ((1 : Fin 2), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem rightFinal3_case_2_5_row_1_2_0 : (((-1 : ℤ) ^ (rightScaleBit 3 2 5).val * positiveScale (rightScaleExponent 3 2 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 5 2 : ℤ)) • HexagonAtoms325.outerLeftABC) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 4)) = (negativeScale (rightScaleExponent 3 2 5) • (rowColumnMul HexagonRowColumn325.rows_assocCAB HexagonRowColumn325.cols_right2)) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem rightFinal3_case_2_5_row_1_2_1 : (((-1 : ℤ) ^ (rightScaleBit 3 2 5).val * positiveScale (rightScaleExponent 3 2 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 5 2 : ℤ)) • HexagonAtoms325.outerLeftABC) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 4)) = (negativeScale (rightScaleExponent 3 2 5) • (rowColumnMul HexagonRowColumn325.rows_assocCAB HexagonRowColumn325.cols_right2)) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem rightFinal3_case_2_5_row_1_2_2 : (((-1 : ℤ) ^ (rightScaleBit 3 2 5).val * positiveScale (rightScaleExponent 3 2 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 5 2 : ℤ)) • HexagonAtoms325.outerLeftABC) ((1 : Fin 2), (2 : Fin 4), (2 : Fin 4)) = (negativeScale (rightScaleExponent 3 2 5) • (rowColumnMul HexagonRowColumn325.rows_assocCAB HexagonRowColumn325.cols_right2)) ((1 : Fin 2), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem rightFinal3_case_2_5_row_1_2_3 : (((-1 : ℤ) ^ (rightScaleBit 3 2 5).val * positiveScale (rightScaleExponent 3 2 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 5 2 : ℤ)) • HexagonAtoms325.outerLeftABC) ((1 : Fin 2), (2 : Fin 4), (3 : Fin 4)) = (negativeScale (rightScaleExponent 3 2 5) • (rowColumnMul HexagonRowColumn325.rows_assocCAB HexagonRowColumn325.cols_right2)) ((1 : Fin 2), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem rightFinal3_case_2_5_row_1_3_0 : (((-1 : ℤ) ^ (rightScaleBit 3 2 5).val * positiveScale (rightScaleExponent 3 2 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 5 2 : ℤ)) • HexagonAtoms325.outerLeftABC) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 4)) = (negativeScale (rightScaleExponent 3 2 5) • (rowColumnMul HexagonRowColumn325.rows_assocCAB HexagonRowColumn325.cols_right2)) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem rightFinal3_case_2_5_row_1_3_1 : (((-1 : ℤ) ^ (rightScaleBit 3 2 5).val * positiveScale (rightScaleExponent 3 2 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 5 2 : ℤ)) • HexagonAtoms325.outerLeftABC) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 4)) = (negativeScale (rightScaleExponent 3 2 5) • (rowColumnMul HexagonRowColumn325.rows_assocCAB HexagonRowColumn325.cols_right2)) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem rightFinal3_case_2_5_row_1_3_2 : (((-1 : ℤ) ^ (rightScaleBit 3 2 5).val * positiveScale (rightScaleExponent 3 2 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 5 2 : ℤ)) • HexagonAtoms325.outerLeftABC) ((1 : Fin 2), (3 : Fin 4), (2 : Fin 4)) = (negativeScale (rightScaleExponent 3 2 5) • (rowColumnMul HexagonRowColumn325.rows_assocCAB HexagonRowColumn325.cols_right2)) ((1 : Fin 2), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem rightFinal3_case_2_5_row_1_3_3 : (((-1 : ℤ) ^ (rightScaleBit 3 2 5).val * positiveScale (rightScaleExponent 3 2 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 5 2 : ℤ)) • HexagonAtoms325.outerLeftABC) ((1 : Fin 2), (3 : Fin 4), (3 : Fin 4)) = (negativeScale (rightScaleExponent 3 2 5) • (rowColumnMul HexagonRowColumn325.rows_assocCAB HexagonRowColumn325.cols_right2)) ((1 : Fin 2), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 4)
  decide +kernel

private theorem rightFinal3_case_2_5_checked : ((-1 : ℤ) ^ (rightScaleBit 3 2 5).val * positiveScale (rightScaleExponent 3 2 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 5 2 : ℤ)) • HexagonAtoms325.outerLeftABC = negativeScale (rightScaleExponent 3 2 5) • (rowColumnMul HexagonRowColumn325.rows_assocCAB HexagonRowColumn325.cols_right2) := by
  funext r
  fin_cases r
  · exact rightFinal3_case_2_5_row_0_0_0
  · exact rightFinal3_case_2_5_row_0_0_1
  · exact rightFinal3_case_2_5_row_0_0_2
  · exact rightFinal3_case_2_5_row_0_0_3
  · exact rightFinal3_case_2_5_row_0_1_0
  · exact rightFinal3_case_2_5_row_0_1_1
  · exact rightFinal3_case_2_5_row_0_1_2
  · exact rightFinal3_case_2_5_row_0_1_3
  · exact rightFinal3_case_2_5_row_0_2_0
  · exact rightFinal3_case_2_5_row_0_2_1
  · exact rightFinal3_case_2_5_row_0_2_2
  · exact rightFinal3_case_2_5_row_0_2_3
  · exact rightFinal3_case_2_5_row_0_3_0
  · exact rightFinal3_case_2_5_row_0_3_1
  · exact rightFinal3_case_2_5_row_0_3_2
  · exact rightFinal3_case_2_5_row_0_3_3
  · exact rightFinal3_case_2_5_row_1_0_0
  · exact rightFinal3_case_2_5_row_1_0_1
  · exact rightFinal3_case_2_5_row_1_0_2
  · exact rightFinal3_case_2_5_row_1_0_3
  · exact rightFinal3_case_2_5_row_1_1_0
  · exact rightFinal3_case_2_5_row_1_1_1
  · exact rightFinal3_case_2_5_row_1_1_2
  · exact rightFinal3_case_2_5_row_1_1_3
  · exact rightFinal3_case_2_5_row_1_2_0
  · exact rightFinal3_case_2_5_row_1_2_1
  · exact rightFinal3_case_2_5_row_1_2_2
  · exact rightFinal3_case_2_5_row_1_2_3
  · exact rightFinal3_case_2_5_row_1_3_0
  · exact rightFinal3_case_2_5_row_1_3_1
  · exact rightFinal3_case_2_5_row_1_3_2
  · exact rightFinal3_case_2_5_row_1_3_3

set_option backward.isDefEq.respectTransparency false in
theorem rightFinal3_case_2_5 : ((-1 : ℤ) ^ (rightScaleBit 3 2 5).val * positiveScale (rightScaleExponent 3 2 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 5 2 : ℤ)) • outerLeftZ 3 2 5 = negativeScale (rightScaleExponent 3 2 5) • (associatorZ 5 3 2 * right2Middle3 2 5) := by
  simpa only [HexagonAtoms325.assocABC_eq,
    HexagonAtoms325.outerABC_eq,
    HexagonAtoms325.assocBAC_eq,
    HexagonAtoms325.innerABC_eq,
    HexagonAtoms325.innerRightABC_eq,
    HexagonAtoms325.inverseACB_eq,
    HexagonAtoms325.innerACB_eq,
    HexagonAtoms325.assocBCA_eq,
    HexagonAtoms325.innerRightBAC_eq,
    HexagonAtoms325.assocCAB_eq,
    HexagonAtoms325.outerLeftABC_eq,
    HexagonRowColumn325.product0_eq,
    HexagonRowColumn325.product1_eq,
    HexagonRowColumn325.product2_eq,
    HexagonRowColumn325.product3_eq,
    HexagonRowColumn325.product4_eq,
    HexagonRowColumn325.product5_eq,
    HexagonRowColumn325.product6_eq,
    HexagonRowColumn325.product7_eq] using rightFinal3_case_2_5_checked

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonCases3
