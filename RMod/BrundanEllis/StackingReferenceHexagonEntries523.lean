import RMod.BrundanEllis.StackingReferenceHexagonMiddle5
import RMod.BrundanEllis.StackingReferenceSparseMatrixCheck
import RMod.BrundanEllis.StackingReferenceHexagonAtoms523
import RMod.BrundanEllis.StackingReferenceHexagonRowColumn523

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

private theorem left0Middle5_eq_case_2_3_row_0_0_0 : (left0Middle5 2 3) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn523.rows_outerABC HexagonRowColumn523.cols_assocABC) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_2_3_row_0_0_1 : (left0Middle5 2 3) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn523.rows_outerABC HexagonRowColumn523.cols_assocABC) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_2_3_row_0_0_2 : (left0Middle5 2 3) ((0 : Fin 2), (0 : Fin 4), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn523.rows_outerABC HexagonRowColumn523.cols_assocABC) ((0 : Fin 2), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_2_3_row_0_0_3 : (left0Middle5 2 3) ((0 : Fin 2), (0 : Fin 4), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn523.rows_outerABC HexagonRowColumn523.cols_assocABC) ((0 : Fin 2), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_2_3_row_0_1_0 : (left0Middle5 2 3) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn523.rows_outerABC HexagonRowColumn523.cols_assocABC) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_2_3_row_0_1_1 : (left0Middle5 2 3) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn523.rows_outerABC HexagonRowColumn523.cols_assocABC) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_2_3_row_0_1_2 : (left0Middle5 2 3) ((0 : Fin 2), (1 : Fin 4), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn523.rows_outerABC HexagonRowColumn523.cols_assocABC) ((0 : Fin 2), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_2_3_row_0_1_3 : (left0Middle5 2 3) ((0 : Fin 2), (1 : Fin 4), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn523.rows_outerABC HexagonRowColumn523.cols_assocABC) ((0 : Fin 2), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_2_3_row_0_2_0 : (left0Middle5 2 3) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn523.rows_outerABC HexagonRowColumn523.cols_assocABC) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_2_3_row_0_2_1 : (left0Middle5 2 3) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn523.rows_outerABC HexagonRowColumn523.cols_assocABC) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_2_3_row_0_2_2 : (left0Middle5 2 3) ((0 : Fin 2), (2 : Fin 4), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn523.rows_outerABC HexagonRowColumn523.cols_assocABC) ((0 : Fin 2), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_2_3_row_0_2_3 : (left0Middle5 2 3) ((0 : Fin 2), (2 : Fin 4), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn523.rows_outerABC HexagonRowColumn523.cols_assocABC) ((0 : Fin 2), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_2_3_row_0_3_0 : (left0Middle5 2 3) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn523.rows_outerABC HexagonRowColumn523.cols_assocABC) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_2_3_row_0_3_1 : (left0Middle5 2 3) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn523.rows_outerABC HexagonRowColumn523.cols_assocABC) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_2_3_row_0_3_2 : (left0Middle5 2 3) ((0 : Fin 2), (3 : Fin 4), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn523.rows_outerABC HexagonRowColumn523.cols_assocABC) ((0 : Fin 2), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_2_3_row_0_3_3 : (left0Middle5 2 3) ((0 : Fin 2), (3 : Fin 4), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn523.rows_outerABC HexagonRowColumn523.cols_assocABC) ((0 : Fin 2), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_2_3_row_1_0_0 : (left0Middle5 2 3) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn523.rows_outerABC HexagonRowColumn523.cols_assocABC) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_2_3_row_1_0_1 : (left0Middle5 2 3) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn523.rows_outerABC HexagonRowColumn523.cols_assocABC) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_2_3_row_1_0_2 : (left0Middle5 2 3) ((1 : Fin 2), (0 : Fin 4), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn523.rows_outerABC HexagonRowColumn523.cols_assocABC) ((1 : Fin 2), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_2_3_row_1_0_3 : (left0Middle5 2 3) ((1 : Fin 2), (0 : Fin 4), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn523.rows_outerABC HexagonRowColumn523.cols_assocABC) ((1 : Fin 2), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_2_3_row_1_1_0 : (left0Middle5 2 3) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn523.rows_outerABC HexagonRowColumn523.cols_assocABC) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_2_3_row_1_1_1 : (left0Middle5 2 3) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn523.rows_outerABC HexagonRowColumn523.cols_assocABC) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_2_3_row_1_1_2 : (left0Middle5 2 3) ((1 : Fin 2), (1 : Fin 4), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn523.rows_outerABC HexagonRowColumn523.cols_assocABC) ((1 : Fin 2), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_2_3_row_1_1_3 : (left0Middle5 2 3) ((1 : Fin 2), (1 : Fin 4), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn523.rows_outerABC HexagonRowColumn523.cols_assocABC) ((1 : Fin 2), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_2_3_row_1_2_0 : (left0Middle5 2 3) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn523.rows_outerABC HexagonRowColumn523.cols_assocABC) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_2_3_row_1_2_1 : (left0Middle5 2 3) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn523.rows_outerABC HexagonRowColumn523.cols_assocABC) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_2_3_row_1_2_2 : (left0Middle5 2 3) ((1 : Fin 2), (2 : Fin 4), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn523.rows_outerABC HexagonRowColumn523.cols_assocABC) ((1 : Fin 2), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_2_3_row_1_2_3 : (left0Middle5 2 3) ((1 : Fin 2), (2 : Fin 4), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn523.rows_outerABC HexagonRowColumn523.cols_assocABC) ((1 : Fin 2), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_2_3_row_1_3_0 : (left0Middle5 2 3) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn523.rows_outerABC HexagonRowColumn523.cols_assocABC) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_2_3_row_1_3_1 : (left0Middle5 2 3) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn523.rows_outerABC HexagonRowColumn523.cols_assocABC) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_2_3_row_1_3_2 : (left0Middle5 2 3) ((1 : Fin 2), (3 : Fin 4), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn523.rows_outerABC HexagonRowColumn523.cols_assocABC) ((1 : Fin 2), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_2_3_row_1_3_3 : (left0Middle5 2 3) ((1 : Fin 2), (3 : Fin 4), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn523.rows_outerABC HexagonRowColumn523.cols_assocABC) ((1 : Fin 2), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_2_3_checked : left0Middle5 2 3 = rowColumnMul HexagonRowColumn523.rows_outerABC HexagonRowColumn523.cols_assocABC := by
  funext r
  fin_cases r
  · exact left0Middle5_eq_case_2_3_row_0_0_0
  · exact left0Middle5_eq_case_2_3_row_0_0_1
  · exact left0Middle5_eq_case_2_3_row_0_0_2
  · exact left0Middle5_eq_case_2_3_row_0_0_3
  · exact left0Middle5_eq_case_2_3_row_0_1_0
  · exact left0Middle5_eq_case_2_3_row_0_1_1
  · exact left0Middle5_eq_case_2_3_row_0_1_2
  · exact left0Middle5_eq_case_2_3_row_0_1_3
  · exact left0Middle5_eq_case_2_3_row_0_2_0
  · exact left0Middle5_eq_case_2_3_row_0_2_1
  · exact left0Middle5_eq_case_2_3_row_0_2_2
  · exact left0Middle5_eq_case_2_3_row_0_2_3
  · exact left0Middle5_eq_case_2_3_row_0_3_0
  · exact left0Middle5_eq_case_2_3_row_0_3_1
  · exact left0Middle5_eq_case_2_3_row_0_3_2
  · exact left0Middle5_eq_case_2_3_row_0_3_3
  · exact left0Middle5_eq_case_2_3_row_1_0_0
  · exact left0Middle5_eq_case_2_3_row_1_0_1
  · exact left0Middle5_eq_case_2_3_row_1_0_2
  · exact left0Middle5_eq_case_2_3_row_1_0_3
  · exact left0Middle5_eq_case_2_3_row_1_1_0
  · exact left0Middle5_eq_case_2_3_row_1_1_1
  · exact left0Middle5_eq_case_2_3_row_1_1_2
  · exact left0Middle5_eq_case_2_3_row_1_1_3
  · exact left0Middle5_eq_case_2_3_row_1_2_0
  · exact left0Middle5_eq_case_2_3_row_1_2_1
  · exact left0Middle5_eq_case_2_3_row_1_2_2
  · exact left0Middle5_eq_case_2_3_row_1_2_3
  · exact left0Middle5_eq_case_2_3_row_1_3_0
  · exact left0Middle5_eq_case_2_3_row_1_3_1
  · exact left0Middle5_eq_case_2_3_row_1_3_2
  · exact left0Middle5_eq_case_2_3_row_1_3_3

set_option backward.isDefEq.respectTransparency false in
theorem left0Middle5_eq_case_2_3 : left0Middle5 2 3 = outerRightZ 5 2 3 * associatorZ 5 2 3 := by
  simpa only [HexagonAtoms523.assocABC_eq,
    HexagonAtoms523.outerABC_eq,
    HexagonAtoms523.assocBAC_eq,
    HexagonAtoms523.innerABC_eq,
    HexagonAtoms523.innerRightABC_eq,
    HexagonAtoms523.inverseACB_eq,
    HexagonAtoms523.innerACB_eq,
    HexagonAtoms523.assocBCA_eq,
    HexagonAtoms523.innerRightBAC_eq,
    HexagonAtoms523.assocCAB_eq,
    HexagonAtoms523.outerLeftABC_eq,
    HexagonRowColumn523.product0_eq,
    HexagonRowColumn523.product1_eq,
    HexagonRowColumn523.product2_eq,
    HexagonRowColumn523.product3_eq,
    HexagonRowColumn523.product4_eq,
    HexagonRowColumn523.product5_eq,
    HexagonRowColumn523.product6_eq,
    HexagonRowColumn523.product7_eq] using left0Middle5_eq_case_2_3_checked

private theorem left1Middle5_eq_case_2_3_row_0_0_0 : (left1Middle5 2 3) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms523.assocBAC) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_2_3_row_0_0_1 : (left1Middle5 2 3) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms523.assocBAC) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_2_3_row_0_0_2 : (left1Middle5 2 3) ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms523.assocBAC) ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_2_3_row_0_0_3 : (left1Middle5 2 3) ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms523.assocBAC) ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_2_3_row_1_0_0 : (left1Middle5 2 3) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms523.assocBAC) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_2_3_row_1_0_1 : (left1Middle5 2 3) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms523.assocBAC) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_2_3_row_1_0_2 : (left1Middle5 2 3) ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms523.assocBAC) ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_2_3_row_1_0_3 : (left1Middle5 2 3) ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms523.assocBAC) ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_2_3_row_2_0_0 : (left1Middle5 2 3) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms523.assocBAC) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_2_3_row_2_0_1 : (left1Middle5 2 3) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms523.assocBAC) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_2_3_row_2_0_2 : (left1Middle5 2 3) ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms523.assocBAC) ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_2_3_row_2_0_3 : (left1Middle5 2 3) ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms523.assocBAC) ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_2_3_row_3_0_0 : (left1Middle5 2 3) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms523.assocBAC) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_2_3_row_3_0_1 : (left1Middle5 2 3) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms523.assocBAC) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_2_3_row_3_0_2 : (left1Middle5 2 3) ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms523.assocBAC) ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_2_3_row_3_0_3 : (left1Middle5 2 3) ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms523.assocBAC) ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_2_3_row_4_0_0 : (left1Middle5 2 3) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms523.assocBAC) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_2_3_row_4_0_1 : (left1Middle5 2 3) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms523.assocBAC) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_2_3_row_4_0_2 : (left1Middle5 2 3) ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms523.assocBAC) ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_2_3_row_4_0_3 : (left1Middle5 2 3) ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms523.assocBAC) ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_2_3_row_5_0_0 : (left1Middle5 2 3) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms523.assocBAC) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_2_3_row_5_0_1 : (left1Middle5 2 3) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms523.assocBAC) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_2_3_row_5_0_2 : (left1Middle5 2 3) ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms523.assocBAC) ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_2_3_row_5_0_3 : (left1Middle5 2 3) ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms523.assocBAC) ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_2_3_row_6_0_0 : (left1Middle5 2 3) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms523.assocBAC) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_2_3_row_6_0_1 : (left1Middle5 2 3) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms523.assocBAC) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_2_3_row_6_0_2 : (left1Middle5 2 3) ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms523.assocBAC) ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_2_3_row_6_0_3 : (left1Middle5 2 3) ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms523.assocBAC) ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_2_3_row_7_0_0 : (left1Middle5 2 3) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms523.assocBAC) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_2_3_row_7_0_1 : (left1Middle5 2 3) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms523.assocBAC) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_2_3_row_7_0_2 : (left1Middle5 2 3) ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms523.assocBAC) ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_2_3_row_7_0_3 : (left1Middle5 2 3) ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms523.assocBAC) ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_2_3_checked : left1Middle5 2 3 = HexagonAtoms523.assocBAC := by
  funext r
  fin_cases r
  · exact left1Middle5_eq_case_2_3_row_0_0_0
  · exact left1Middle5_eq_case_2_3_row_0_0_1
  · exact left1Middle5_eq_case_2_3_row_0_0_2
  · exact left1Middle5_eq_case_2_3_row_0_0_3
  · exact left1Middle5_eq_case_2_3_row_1_0_0
  · exact left1Middle5_eq_case_2_3_row_1_0_1
  · exact left1Middle5_eq_case_2_3_row_1_0_2
  · exact left1Middle5_eq_case_2_3_row_1_0_3
  · exact left1Middle5_eq_case_2_3_row_2_0_0
  · exact left1Middle5_eq_case_2_3_row_2_0_1
  · exact left1Middle5_eq_case_2_3_row_2_0_2
  · exact left1Middle5_eq_case_2_3_row_2_0_3
  · exact left1Middle5_eq_case_2_3_row_3_0_0
  · exact left1Middle5_eq_case_2_3_row_3_0_1
  · exact left1Middle5_eq_case_2_3_row_3_0_2
  · exact left1Middle5_eq_case_2_3_row_3_0_3
  · exact left1Middle5_eq_case_2_3_row_4_0_0
  · exact left1Middle5_eq_case_2_3_row_4_0_1
  · exact left1Middle5_eq_case_2_3_row_4_0_2
  · exact left1Middle5_eq_case_2_3_row_4_0_3
  · exact left1Middle5_eq_case_2_3_row_5_0_0
  · exact left1Middle5_eq_case_2_3_row_5_0_1
  · exact left1Middle5_eq_case_2_3_row_5_0_2
  · exact left1Middle5_eq_case_2_3_row_5_0_3
  · exact left1Middle5_eq_case_2_3_row_6_0_0
  · exact left1Middle5_eq_case_2_3_row_6_0_1
  · exact left1Middle5_eq_case_2_3_row_6_0_2
  · exact left1Middle5_eq_case_2_3_row_6_0_3
  · exact left1Middle5_eq_case_2_3_row_7_0_0
  · exact left1Middle5_eq_case_2_3_row_7_0_1
  · exact left1Middle5_eq_case_2_3_row_7_0_2
  · exact left1Middle5_eq_case_2_3_row_7_0_3

set_option backward.isDefEq.respectTransparency false in
theorem left1Middle5_eq_case_2_3 : left1Middle5 2 3 = associatorZ 2 5 3 * innerLeftZ 5 2 3 := by
  simpa only [HexagonAtoms523.assocABC_eq,
    HexagonAtoms523.outerABC_eq,
    HexagonAtoms523.assocBAC_eq,
    HexagonAtoms523.innerABC_eq,
    HexagonAtoms523.innerRightABC_eq,
    HexagonAtoms523.inverseACB_eq,
    HexagonAtoms523.innerACB_eq,
    HexagonAtoms523.assocBCA_eq,
    HexagonAtoms523.innerRightBAC_eq,
    HexagonAtoms523.assocCAB_eq,
    HexagonAtoms523.outerLeftABC_eq,
    HexagonRowColumn523.product0_eq,
    HexagonRowColumn523.product1_eq,
    HexagonRowColumn523.product2_eq,
    HexagonRowColumn523.product3_eq,
    HexagonRowColumn523.product4_eq,
    HexagonRowColumn523.product5_eq,
    HexagonRowColumn523.product6_eq,
    HexagonRowColumn523.product7_eq] using left1Middle5_eq_case_2_3_checked

private theorem right0Middle5_eq_case_2_3_row_0_0_0 : (right0Middle5 2 3) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 4)) = (HexagonAtoms523.assocABC) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_2_3_row_0_0_1 : (right0Middle5 2 3) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 4)) = (HexagonAtoms523.assocABC) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_2_3_row_0_0_2 : (right0Middle5 2 3) ((0 : Fin 2), (0 : Fin 4), (2 : Fin 4)) = (HexagonAtoms523.assocABC) ((0 : Fin 2), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_2_3_row_0_0_3 : (right0Middle5 2 3) ((0 : Fin 2), (0 : Fin 4), (3 : Fin 4)) = (HexagonAtoms523.assocABC) ((0 : Fin 2), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_2_3_row_0_1_0 : (right0Middle5 2 3) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 4)) = (HexagonAtoms523.assocABC) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_2_3_row_0_1_1 : (right0Middle5 2 3) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 4)) = (HexagonAtoms523.assocABC) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_2_3_row_0_1_2 : (right0Middle5 2 3) ((0 : Fin 2), (1 : Fin 4), (2 : Fin 4)) = (HexagonAtoms523.assocABC) ((0 : Fin 2), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_2_3_row_0_1_3 : (right0Middle5 2 3) ((0 : Fin 2), (1 : Fin 4), (3 : Fin 4)) = (HexagonAtoms523.assocABC) ((0 : Fin 2), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_2_3_row_0_2_0 : (right0Middle5 2 3) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 4)) = (HexagonAtoms523.assocABC) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_2_3_row_0_2_1 : (right0Middle5 2 3) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 4)) = (HexagonAtoms523.assocABC) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_2_3_row_0_2_2 : (right0Middle5 2 3) ((0 : Fin 2), (2 : Fin 4), (2 : Fin 4)) = (HexagonAtoms523.assocABC) ((0 : Fin 2), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_2_3_row_0_2_3 : (right0Middle5 2 3) ((0 : Fin 2), (2 : Fin 4), (3 : Fin 4)) = (HexagonAtoms523.assocABC) ((0 : Fin 2), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_2_3_row_0_3_0 : (right0Middle5 2 3) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 4)) = (HexagonAtoms523.assocABC) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_2_3_row_0_3_1 : (right0Middle5 2 3) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 4)) = (HexagonAtoms523.assocABC) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_2_3_row_0_3_2 : (right0Middle5 2 3) ((0 : Fin 2), (3 : Fin 4), (2 : Fin 4)) = (HexagonAtoms523.assocABC) ((0 : Fin 2), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_2_3_row_0_3_3 : (right0Middle5 2 3) ((0 : Fin 2), (3 : Fin 4), (3 : Fin 4)) = (HexagonAtoms523.assocABC) ((0 : Fin 2), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_2_3_row_1_0_0 : (right0Middle5 2 3) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 4)) = (HexagonAtoms523.assocABC) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_2_3_row_1_0_1 : (right0Middle5 2 3) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 4)) = (HexagonAtoms523.assocABC) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_2_3_row_1_0_2 : (right0Middle5 2 3) ((1 : Fin 2), (0 : Fin 4), (2 : Fin 4)) = (HexagonAtoms523.assocABC) ((1 : Fin 2), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_2_3_row_1_0_3 : (right0Middle5 2 3) ((1 : Fin 2), (0 : Fin 4), (3 : Fin 4)) = (HexagonAtoms523.assocABC) ((1 : Fin 2), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_2_3_row_1_1_0 : (right0Middle5 2 3) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 4)) = (HexagonAtoms523.assocABC) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_2_3_row_1_1_1 : (right0Middle5 2 3) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 4)) = (HexagonAtoms523.assocABC) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_2_3_row_1_1_2 : (right0Middle5 2 3) ((1 : Fin 2), (1 : Fin 4), (2 : Fin 4)) = (HexagonAtoms523.assocABC) ((1 : Fin 2), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_2_3_row_1_1_3 : (right0Middle5 2 3) ((1 : Fin 2), (1 : Fin 4), (3 : Fin 4)) = (HexagonAtoms523.assocABC) ((1 : Fin 2), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_2_3_row_1_2_0 : (right0Middle5 2 3) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 4)) = (HexagonAtoms523.assocABC) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_2_3_row_1_2_1 : (right0Middle5 2 3) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 4)) = (HexagonAtoms523.assocABC) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_2_3_row_1_2_2 : (right0Middle5 2 3) ((1 : Fin 2), (2 : Fin 4), (2 : Fin 4)) = (HexagonAtoms523.assocABC) ((1 : Fin 2), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_2_3_row_1_2_3 : (right0Middle5 2 3) ((1 : Fin 2), (2 : Fin 4), (3 : Fin 4)) = (HexagonAtoms523.assocABC) ((1 : Fin 2), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_2_3_row_1_3_0 : (right0Middle5 2 3) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 4)) = (HexagonAtoms523.assocABC) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_2_3_row_1_3_1 : (right0Middle5 2 3) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 4)) = (HexagonAtoms523.assocABC) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_2_3_row_1_3_2 : (right0Middle5 2 3) ((1 : Fin 2), (3 : Fin 4), (2 : Fin 4)) = (HexagonAtoms523.assocABC) ((1 : Fin 2), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_2_3_row_1_3_3 : (right0Middle5 2 3) ((1 : Fin 2), (3 : Fin 4), (3 : Fin 4)) = (HexagonAtoms523.assocABC) ((1 : Fin 2), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_2_3_checked : right0Middle5 2 3 = HexagonAtoms523.assocABC := by
  funext r
  fin_cases r
  · exact right0Middle5_eq_case_2_3_row_0_0_0
  · exact right0Middle5_eq_case_2_3_row_0_0_1
  · exact right0Middle5_eq_case_2_3_row_0_0_2
  · exact right0Middle5_eq_case_2_3_row_0_0_3
  · exact right0Middle5_eq_case_2_3_row_0_1_0
  · exact right0Middle5_eq_case_2_3_row_0_1_1
  · exact right0Middle5_eq_case_2_3_row_0_1_2
  · exact right0Middle5_eq_case_2_3_row_0_1_3
  · exact right0Middle5_eq_case_2_3_row_0_2_0
  · exact right0Middle5_eq_case_2_3_row_0_2_1
  · exact right0Middle5_eq_case_2_3_row_0_2_2
  · exact right0Middle5_eq_case_2_3_row_0_2_3
  · exact right0Middle5_eq_case_2_3_row_0_3_0
  · exact right0Middle5_eq_case_2_3_row_0_3_1
  · exact right0Middle5_eq_case_2_3_row_0_3_2
  · exact right0Middle5_eq_case_2_3_row_0_3_3
  · exact right0Middle5_eq_case_2_3_row_1_0_0
  · exact right0Middle5_eq_case_2_3_row_1_0_1
  · exact right0Middle5_eq_case_2_3_row_1_0_2
  · exact right0Middle5_eq_case_2_3_row_1_0_3
  · exact right0Middle5_eq_case_2_3_row_1_1_0
  · exact right0Middle5_eq_case_2_3_row_1_1_1
  · exact right0Middle5_eq_case_2_3_row_1_1_2
  · exact right0Middle5_eq_case_2_3_row_1_1_3
  · exact right0Middle5_eq_case_2_3_row_1_2_0
  · exact right0Middle5_eq_case_2_3_row_1_2_1
  · exact right0Middle5_eq_case_2_3_row_1_2_2
  · exact right0Middle5_eq_case_2_3_row_1_2_3
  · exact right0Middle5_eq_case_2_3_row_1_3_0
  · exact right0Middle5_eq_case_2_3_row_1_3_1
  · exact right0Middle5_eq_case_2_3_row_1_3_2
  · exact right0Middle5_eq_case_2_3_row_1_3_3

set_option backward.isDefEq.respectTransparency false in
theorem right0Middle5_eq_case_2_3 : right0Middle5 2 3 = innerRightZ 5 2 3 * associatorZ 5 2 3 := by
  simpa only [HexagonAtoms523.assocABC_eq,
    HexagonAtoms523.outerABC_eq,
    HexagonAtoms523.assocBAC_eq,
    HexagonAtoms523.innerABC_eq,
    HexagonAtoms523.innerRightABC_eq,
    HexagonAtoms523.inverseACB_eq,
    HexagonAtoms523.innerACB_eq,
    HexagonAtoms523.assocBCA_eq,
    HexagonAtoms523.innerRightBAC_eq,
    HexagonAtoms523.assocCAB_eq,
    HexagonAtoms523.outerLeftABC_eq,
    HexagonRowColumn523.product0_eq,
    HexagonRowColumn523.product1_eq,
    HexagonRowColumn523.product2_eq,
    HexagonRowColumn523.product3_eq,
    HexagonRowColumn523.product4_eq,
    HexagonRowColumn523.product5_eq,
    HexagonRowColumn523.product6_eq,
    HexagonRowColumn523.product7_eq] using right0Middle5_eq_case_2_3_checked

private theorem right1Middle5_eq_case_2_3_row_0_0_0 : (right1Middle5 2 3) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn523.rows_inverseACB HexagonRowColumn523.cols_right0) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_2_3_row_0_0_1 : (right1Middle5 2 3) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn523.rows_inverseACB HexagonRowColumn523.cols_right0) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_2_3_row_0_0_2 : (right1Middle5 2 3) ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn523.rows_inverseACB HexagonRowColumn523.cols_right0) ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_2_3_row_0_0_3 : (right1Middle5 2 3) ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn523.rows_inverseACB HexagonRowColumn523.cols_right0) ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_2_3_row_1_0_0 : (right1Middle5 2 3) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn523.rows_inverseACB HexagonRowColumn523.cols_right0) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_2_3_row_1_0_1 : (right1Middle5 2 3) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn523.rows_inverseACB HexagonRowColumn523.cols_right0) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_2_3_row_1_0_2 : (right1Middle5 2 3) ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn523.rows_inverseACB HexagonRowColumn523.cols_right0) ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_2_3_row_1_0_3 : (right1Middle5 2 3) ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn523.rows_inverseACB HexagonRowColumn523.cols_right0) ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_2_3_row_2_0_0 : (right1Middle5 2 3) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn523.rows_inverseACB HexagonRowColumn523.cols_right0) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_2_3_row_2_0_1 : (right1Middle5 2 3) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn523.rows_inverseACB HexagonRowColumn523.cols_right0) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_2_3_row_2_0_2 : (right1Middle5 2 3) ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn523.rows_inverseACB HexagonRowColumn523.cols_right0) ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_2_3_row_2_0_3 : (right1Middle5 2 3) ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn523.rows_inverseACB HexagonRowColumn523.cols_right0) ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_2_3_row_3_0_0 : (right1Middle5 2 3) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn523.rows_inverseACB HexagonRowColumn523.cols_right0) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_2_3_row_3_0_1 : (right1Middle5 2 3) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn523.rows_inverseACB HexagonRowColumn523.cols_right0) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_2_3_row_3_0_2 : (right1Middle5 2 3) ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn523.rows_inverseACB HexagonRowColumn523.cols_right0) ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_2_3_row_3_0_3 : (right1Middle5 2 3) ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn523.rows_inverseACB HexagonRowColumn523.cols_right0) ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_2_3_row_4_0_0 : (right1Middle5 2 3) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn523.rows_inverseACB HexagonRowColumn523.cols_right0) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_2_3_row_4_0_1 : (right1Middle5 2 3) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn523.rows_inverseACB HexagonRowColumn523.cols_right0) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_2_3_row_4_0_2 : (right1Middle5 2 3) ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn523.rows_inverseACB HexagonRowColumn523.cols_right0) ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_2_3_row_4_0_3 : (right1Middle5 2 3) ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn523.rows_inverseACB HexagonRowColumn523.cols_right0) ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_2_3_row_5_0_0 : (right1Middle5 2 3) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn523.rows_inverseACB HexagonRowColumn523.cols_right0) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_2_3_row_5_0_1 : (right1Middle5 2 3) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn523.rows_inverseACB HexagonRowColumn523.cols_right0) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_2_3_row_5_0_2 : (right1Middle5 2 3) ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn523.rows_inverseACB HexagonRowColumn523.cols_right0) ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_2_3_row_5_0_3 : (right1Middle5 2 3) ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn523.rows_inverseACB HexagonRowColumn523.cols_right0) ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_2_3_row_6_0_0 : (right1Middle5 2 3) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn523.rows_inverseACB HexagonRowColumn523.cols_right0) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_2_3_row_6_0_1 : (right1Middle5 2 3) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn523.rows_inverseACB HexagonRowColumn523.cols_right0) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_2_3_row_6_0_2 : (right1Middle5 2 3) ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn523.rows_inverseACB HexagonRowColumn523.cols_right0) ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_2_3_row_6_0_3 : (right1Middle5 2 3) ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn523.rows_inverseACB HexagonRowColumn523.cols_right0) ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_2_3_row_7_0_0 : (right1Middle5 2 3) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn523.rows_inverseACB HexagonRowColumn523.cols_right0) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_2_3_row_7_0_1 : (right1Middle5 2 3) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn523.rows_inverseACB HexagonRowColumn523.cols_right0) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_2_3_row_7_0_2 : (right1Middle5 2 3) ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn523.rows_inverseACB HexagonRowColumn523.cols_right0) ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_2_3_row_7_0_3 : (right1Middle5 2 3) ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn523.rows_inverseACB HexagonRowColumn523.cols_right0) ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_2_3_checked : right1Middle5 2 3 = rowColumnMul HexagonRowColumn523.rows_inverseACB HexagonRowColumn523.cols_right0 := by
  funext r
  fin_cases r
  · exact right1Middle5_eq_case_2_3_row_0_0_0
  · exact right1Middle5_eq_case_2_3_row_0_0_1
  · exact right1Middle5_eq_case_2_3_row_0_0_2
  · exact right1Middle5_eq_case_2_3_row_0_0_3
  · exact right1Middle5_eq_case_2_3_row_1_0_0
  · exact right1Middle5_eq_case_2_3_row_1_0_1
  · exact right1Middle5_eq_case_2_3_row_1_0_2
  · exact right1Middle5_eq_case_2_3_row_1_0_3
  · exact right1Middle5_eq_case_2_3_row_2_0_0
  · exact right1Middle5_eq_case_2_3_row_2_0_1
  · exact right1Middle5_eq_case_2_3_row_2_0_2
  · exact right1Middle5_eq_case_2_3_row_2_0_3
  · exact right1Middle5_eq_case_2_3_row_3_0_0
  · exact right1Middle5_eq_case_2_3_row_3_0_1
  · exact right1Middle5_eq_case_2_3_row_3_0_2
  · exact right1Middle5_eq_case_2_3_row_3_0_3
  · exact right1Middle5_eq_case_2_3_row_4_0_0
  · exact right1Middle5_eq_case_2_3_row_4_0_1
  · exact right1Middle5_eq_case_2_3_row_4_0_2
  · exact right1Middle5_eq_case_2_3_row_4_0_3
  · exact right1Middle5_eq_case_2_3_row_5_0_0
  · exact right1Middle5_eq_case_2_3_row_5_0_1
  · exact right1Middle5_eq_case_2_3_row_5_0_2
  · exact right1Middle5_eq_case_2_3_row_5_0_3
  · exact right1Middle5_eq_case_2_3_row_6_0_0
  · exact right1Middle5_eq_case_2_3_row_6_0_1
  · exact right1Middle5_eq_case_2_3_row_6_0_2
  · exact right1Middle5_eq_case_2_3_row_6_0_3
  · exact right1Middle5_eq_case_2_3_row_7_0_0
  · exact right1Middle5_eq_case_2_3_row_7_0_1
  · exact right1Middle5_eq_case_2_3_row_7_0_2
  · exact right1Middle5_eq_case_2_3_row_7_0_3

set_option backward.isDefEq.respectTransparency false in
theorem right1Middle5_eq_case_2_3 : right1Middle5 2 3 = associatorInverseZ 5 3 2 * right0Middle5 2 3 := by
  simpa only [HexagonAtoms523.assocABC_eq,
    HexagonAtoms523.outerABC_eq,
    HexagonAtoms523.assocBAC_eq,
    HexagonAtoms523.innerABC_eq,
    HexagonAtoms523.innerRightABC_eq,
    HexagonAtoms523.inverseACB_eq,
    HexagonAtoms523.innerACB_eq,
    HexagonAtoms523.assocBCA_eq,
    HexagonAtoms523.innerRightBAC_eq,
    HexagonAtoms523.assocCAB_eq,
    HexagonAtoms523.outerLeftABC_eq,
    HexagonRowColumn523.product0_eq,
    HexagonRowColumn523.product1_eq,
    HexagonRowColumn523.product2_eq,
    HexagonRowColumn523.product3_eq,
    HexagonRowColumn523.product4_eq,
    HexagonRowColumn523.product5_eq,
    HexagonRowColumn523.product6_eq,
    HexagonRowColumn523.product7_eq] using right1Middle5_eq_case_2_3_checked

private theorem right2Middle5_eq_case_2_3_row_0_0_0 : (right2Middle5 2 3) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (right1Middle5 2 3) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_2_3_row_0_0_1 : (right2Middle5 2 3) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (right1Middle5 2 3) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_2_3_row_0_0_2 : (right2Middle5 2 3) ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (right1Middle5 2 3) ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_2_3_row_0_0_3 : (right2Middle5 2 3) ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (right1Middle5 2 3) ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_2_3_row_1_0_0 : (right2Middle5 2 3) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (right1Middle5 2 3) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_2_3_row_1_0_1 : (right2Middle5 2 3) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (right1Middle5 2 3) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_2_3_row_1_0_2 : (right2Middle5 2 3) ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (right1Middle5 2 3) ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_2_3_row_1_0_3 : (right2Middle5 2 3) ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (right1Middle5 2 3) ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_2_3_row_2_0_0 : (right2Middle5 2 3) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (right1Middle5 2 3) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_2_3_row_2_0_1 : (right2Middle5 2 3) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (right1Middle5 2 3) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_2_3_row_2_0_2 : (right2Middle5 2 3) ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (right1Middle5 2 3) ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_2_3_row_2_0_3 : (right2Middle5 2 3) ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (right1Middle5 2 3) ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_2_3_row_3_0_0 : (right2Middle5 2 3) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (right1Middle5 2 3) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_2_3_row_3_0_1 : (right2Middle5 2 3) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (right1Middle5 2 3) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_2_3_row_3_0_2 : (right2Middle5 2 3) ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (right1Middle5 2 3) ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_2_3_row_3_0_3 : (right2Middle5 2 3) ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (right1Middle5 2 3) ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_2_3_row_4_0_0 : (right2Middle5 2 3) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (right1Middle5 2 3) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_2_3_row_4_0_1 : (right2Middle5 2 3) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (right1Middle5 2 3) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_2_3_row_4_0_2 : (right2Middle5 2 3) ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (right1Middle5 2 3) ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_2_3_row_4_0_3 : (right2Middle5 2 3) ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (right1Middle5 2 3) ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_2_3_row_5_0_0 : (right2Middle5 2 3) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (right1Middle5 2 3) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_2_3_row_5_0_1 : (right2Middle5 2 3) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (right1Middle5 2 3) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_2_3_row_5_0_2 : (right2Middle5 2 3) ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (right1Middle5 2 3) ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_2_3_row_5_0_3 : (right2Middle5 2 3) ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (right1Middle5 2 3) ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_2_3_row_6_0_0 : (right2Middle5 2 3) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (right1Middle5 2 3) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_2_3_row_6_0_1 : (right2Middle5 2 3) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (right1Middle5 2 3) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_2_3_row_6_0_2 : (right2Middle5 2 3) ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (right1Middle5 2 3) ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_2_3_row_6_0_3 : (right2Middle5 2 3) ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (right1Middle5 2 3) ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_2_3_row_7_0_0 : (right2Middle5 2 3) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (right1Middle5 2 3) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_2_3_row_7_0_1 : (right2Middle5 2 3) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (right1Middle5 2 3) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_2_3_row_7_0_2 : (right2Middle5 2 3) ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (right1Middle5 2 3) ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_2_3_row_7_0_3 : (right2Middle5 2 3) ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (right1Middle5 2 3) ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_2_3_checked : right2Middle5 2 3 = right1Middle5 2 3 := by
  funext r
  fin_cases r
  · exact right2Middle5_eq_case_2_3_row_0_0_0
  · exact right2Middle5_eq_case_2_3_row_0_0_1
  · exact right2Middle5_eq_case_2_3_row_0_0_2
  · exact right2Middle5_eq_case_2_3_row_0_0_3
  · exact right2Middle5_eq_case_2_3_row_1_0_0
  · exact right2Middle5_eq_case_2_3_row_1_0_1
  · exact right2Middle5_eq_case_2_3_row_1_0_2
  · exact right2Middle5_eq_case_2_3_row_1_0_3
  · exact right2Middle5_eq_case_2_3_row_2_0_0
  · exact right2Middle5_eq_case_2_3_row_2_0_1
  · exact right2Middle5_eq_case_2_3_row_2_0_2
  · exact right2Middle5_eq_case_2_3_row_2_0_3
  · exact right2Middle5_eq_case_2_3_row_3_0_0
  · exact right2Middle5_eq_case_2_3_row_3_0_1
  · exact right2Middle5_eq_case_2_3_row_3_0_2
  · exact right2Middle5_eq_case_2_3_row_3_0_3
  · exact right2Middle5_eq_case_2_3_row_4_0_0
  · exact right2Middle5_eq_case_2_3_row_4_0_1
  · exact right2Middle5_eq_case_2_3_row_4_0_2
  · exact right2Middle5_eq_case_2_3_row_4_0_3
  · exact right2Middle5_eq_case_2_3_row_5_0_0
  · exact right2Middle5_eq_case_2_3_row_5_0_1
  · exact right2Middle5_eq_case_2_3_row_5_0_2
  · exact right2Middle5_eq_case_2_3_row_5_0_3
  · exact right2Middle5_eq_case_2_3_row_6_0_0
  · exact right2Middle5_eq_case_2_3_row_6_0_1
  · exact right2Middle5_eq_case_2_3_row_6_0_2
  · exact right2Middle5_eq_case_2_3_row_6_0_3
  · exact right2Middle5_eq_case_2_3_row_7_0_0
  · exact right2Middle5_eq_case_2_3_row_7_0_1
  · exact right2Middle5_eq_case_2_3_row_7_0_2
  · exact right2Middle5_eq_case_2_3_row_7_0_3

set_option backward.isDefEq.respectTransparency false in
theorem right2Middle5_eq_case_2_3 : right2Middle5 2 3 = innerLeftZ 5 3 2 * right1Middle5 2 3 := by
  simpa only [HexagonAtoms523.assocABC_eq,
    HexagonAtoms523.outerABC_eq,
    HexagonAtoms523.assocBAC_eq,
    HexagonAtoms523.innerABC_eq,
    HexagonAtoms523.innerRightABC_eq,
    HexagonAtoms523.inverseACB_eq,
    HexagonAtoms523.innerACB_eq,
    HexagonAtoms523.assocBCA_eq,
    HexagonAtoms523.innerRightBAC_eq,
    HexagonAtoms523.assocCAB_eq,
    HexagonAtoms523.outerLeftABC_eq,
    HexagonRowColumn523.product0_eq,
    HexagonRowColumn523.product1_eq,
    HexagonRowColumn523.product2_eq,
    HexagonRowColumn523.product3_eq,
    HexagonRowColumn523.product4_eq,
    HexagonRowColumn523.product5_eq,
    HexagonRowColumn523.product6_eq,
    HexagonRowColumn523.product7_eq] using right2Middle5_eq_case_2_3_checked

private theorem leftFinal5_case_2_3_row_0_0_0 : (((-1 : ℤ) ^ (leftScaleBit 5 2 3).val * positiveScale (leftScaleExponent 5 2 3)) •
      (rowColumnMul HexagonRowColumn523.rows_assocBCA HexagonRowColumn523.cols_left0)) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (negativeScale (leftScaleExponent 5 2 3) • (left1Middle5 2 3)) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_2_3_row_0_0_1 : (((-1 : ℤ) ^ (leftScaleBit 5 2 3).val * positiveScale (leftScaleExponent 5 2 3)) •
      (rowColumnMul HexagonRowColumn523.rows_assocBCA HexagonRowColumn523.cols_left0)) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (negativeScale (leftScaleExponent 5 2 3) • (left1Middle5 2 3)) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_2_3_row_0_0_2 : (((-1 : ℤ) ^ (leftScaleBit 5 2 3).val * positiveScale (leftScaleExponent 5 2 3)) •
      (rowColumnMul HexagonRowColumn523.rows_assocBCA HexagonRowColumn523.cols_left0)) ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (negativeScale (leftScaleExponent 5 2 3) • (left1Middle5 2 3)) ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_2_3_row_0_0_3 : (((-1 : ℤ) ^ (leftScaleBit 5 2 3).val * positiveScale (leftScaleExponent 5 2 3)) •
      (rowColumnMul HexagonRowColumn523.rows_assocBCA HexagonRowColumn523.cols_left0)) ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (negativeScale (leftScaleExponent 5 2 3) • (left1Middle5 2 3)) ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_2_3_row_1_0_0 : (((-1 : ℤ) ^ (leftScaleBit 5 2 3).val * positiveScale (leftScaleExponent 5 2 3)) •
      (rowColumnMul HexagonRowColumn523.rows_assocBCA HexagonRowColumn523.cols_left0)) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (negativeScale (leftScaleExponent 5 2 3) • (left1Middle5 2 3)) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_2_3_row_1_0_1 : (((-1 : ℤ) ^ (leftScaleBit 5 2 3).val * positiveScale (leftScaleExponent 5 2 3)) •
      (rowColumnMul HexagonRowColumn523.rows_assocBCA HexagonRowColumn523.cols_left0)) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (negativeScale (leftScaleExponent 5 2 3) • (left1Middle5 2 3)) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_2_3_row_1_0_2 : (((-1 : ℤ) ^ (leftScaleBit 5 2 3).val * positiveScale (leftScaleExponent 5 2 3)) •
      (rowColumnMul HexagonRowColumn523.rows_assocBCA HexagonRowColumn523.cols_left0)) ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (negativeScale (leftScaleExponent 5 2 3) • (left1Middle5 2 3)) ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_2_3_row_1_0_3 : (((-1 : ℤ) ^ (leftScaleBit 5 2 3).val * positiveScale (leftScaleExponent 5 2 3)) •
      (rowColumnMul HexagonRowColumn523.rows_assocBCA HexagonRowColumn523.cols_left0)) ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (negativeScale (leftScaleExponent 5 2 3) • (left1Middle5 2 3)) ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_2_3_row_2_0_0 : (((-1 : ℤ) ^ (leftScaleBit 5 2 3).val * positiveScale (leftScaleExponent 5 2 3)) •
      (rowColumnMul HexagonRowColumn523.rows_assocBCA HexagonRowColumn523.cols_left0)) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (negativeScale (leftScaleExponent 5 2 3) • (left1Middle5 2 3)) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_2_3_row_2_0_1 : (((-1 : ℤ) ^ (leftScaleBit 5 2 3).val * positiveScale (leftScaleExponent 5 2 3)) •
      (rowColumnMul HexagonRowColumn523.rows_assocBCA HexagonRowColumn523.cols_left0)) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (negativeScale (leftScaleExponent 5 2 3) • (left1Middle5 2 3)) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_2_3_row_2_0_2 : (((-1 : ℤ) ^ (leftScaleBit 5 2 3).val * positiveScale (leftScaleExponent 5 2 3)) •
      (rowColumnMul HexagonRowColumn523.rows_assocBCA HexagonRowColumn523.cols_left0)) ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (negativeScale (leftScaleExponent 5 2 3) • (left1Middle5 2 3)) ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_2_3_row_2_0_3 : (((-1 : ℤ) ^ (leftScaleBit 5 2 3).val * positiveScale (leftScaleExponent 5 2 3)) •
      (rowColumnMul HexagonRowColumn523.rows_assocBCA HexagonRowColumn523.cols_left0)) ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (negativeScale (leftScaleExponent 5 2 3) • (left1Middle5 2 3)) ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_2_3_row_3_0_0 : (((-1 : ℤ) ^ (leftScaleBit 5 2 3).val * positiveScale (leftScaleExponent 5 2 3)) •
      (rowColumnMul HexagonRowColumn523.rows_assocBCA HexagonRowColumn523.cols_left0)) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (negativeScale (leftScaleExponent 5 2 3) • (left1Middle5 2 3)) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_2_3_row_3_0_1 : (((-1 : ℤ) ^ (leftScaleBit 5 2 3).val * positiveScale (leftScaleExponent 5 2 3)) •
      (rowColumnMul HexagonRowColumn523.rows_assocBCA HexagonRowColumn523.cols_left0)) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (negativeScale (leftScaleExponent 5 2 3) • (left1Middle5 2 3)) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_2_3_row_3_0_2 : (((-1 : ℤ) ^ (leftScaleBit 5 2 3).val * positiveScale (leftScaleExponent 5 2 3)) •
      (rowColumnMul HexagonRowColumn523.rows_assocBCA HexagonRowColumn523.cols_left0)) ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (negativeScale (leftScaleExponent 5 2 3) • (left1Middle5 2 3)) ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_2_3_row_3_0_3 : (((-1 : ℤ) ^ (leftScaleBit 5 2 3).val * positiveScale (leftScaleExponent 5 2 3)) •
      (rowColumnMul HexagonRowColumn523.rows_assocBCA HexagonRowColumn523.cols_left0)) ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (negativeScale (leftScaleExponent 5 2 3) • (left1Middle5 2 3)) ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_2_3_row_4_0_0 : (((-1 : ℤ) ^ (leftScaleBit 5 2 3).val * positiveScale (leftScaleExponent 5 2 3)) •
      (rowColumnMul HexagonRowColumn523.rows_assocBCA HexagonRowColumn523.cols_left0)) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (negativeScale (leftScaleExponent 5 2 3) • (left1Middle5 2 3)) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_2_3_row_4_0_1 : (((-1 : ℤ) ^ (leftScaleBit 5 2 3).val * positiveScale (leftScaleExponent 5 2 3)) •
      (rowColumnMul HexagonRowColumn523.rows_assocBCA HexagonRowColumn523.cols_left0)) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (negativeScale (leftScaleExponent 5 2 3) • (left1Middle5 2 3)) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_2_3_row_4_0_2 : (((-1 : ℤ) ^ (leftScaleBit 5 2 3).val * positiveScale (leftScaleExponent 5 2 3)) •
      (rowColumnMul HexagonRowColumn523.rows_assocBCA HexagonRowColumn523.cols_left0)) ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (negativeScale (leftScaleExponent 5 2 3) • (left1Middle5 2 3)) ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_2_3_row_4_0_3 : (((-1 : ℤ) ^ (leftScaleBit 5 2 3).val * positiveScale (leftScaleExponent 5 2 3)) •
      (rowColumnMul HexagonRowColumn523.rows_assocBCA HexagonRowColumn523.cols_left0)) ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (negativeScale (leftScaleExponent 5 2 3) • (left1Middle5 2 3)) ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_2_3_row_5_0_0 : (((-1 : ℤ) ^ (leftScaleBit 5 2 3).val * positiveScale (leftScaleExponent 5 2 3)) •
      (rowColumnMul HexagonRowColumn523.rows_assocBCA HexagonRowColumn523.cols_left0)) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (negativeScale (leftScaleExponent 5 2 3) • (left1Middle5 2 3)) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_2_3_row_5_0_1 : (((-1 : ℤ) ^ (leftScaleBit 5 2 3).val * positiveScale (leftScaleExponent 5 2 3)) •
      (rowColumnMul HexagonRowColumn523.rows_assocBCA HexagonRowColumn523.cols_left0)) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (negativeScale (leftScaleExponent 5 2 3) • (left1Middle5 2 3)) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_2_3_row_5_0_2 : (((-1 : ℤ) ^ (leftScaleBit 5 2 3).val * positiveScale (leftScaleExponent 5 2 3)) •
      (rowColumnMul HexagonRowColumn523.rows_assocBCA HexagonRowColumn523.cols_left0)) ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (negativeScale (leftScaleExponent 5 2 3) • (left1Middle5 2 3)) ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_2_3_row_5_0_3 : (((-1 : ℤ) ^ (leftScaleBit 5 2 3).val * positiveScale (leftScaleExponent 5 2 3)) •
      (rowColumnMul HexagonRowColumn523.rows_assocBCA HexagonRowColumn523.cols_left0)) ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (negativeScale (leftScaleExponent 5 2 3) • (left1Middle5 2 3)) ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_2_3_row_6_0_0 : (((-1 : ℤ) ^ (leftScaleBit 5 2 3).val * positiveScale (leftScaleExponent 5 2 3)) •
      (rowColumnMul HexagonRowColumn523.rows_assocBCA HexagonRowColumn523.cols_left0)) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (negativeScale (leftScaleExponent 5 2 3) • (left1Middle5 2 3)) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_2_3_row_6_0_1 : (((-1 : ℤ) ^ (leftScaleBit 5 2 3).val * positiveScale (leftScaleExponent 5 2 3)) •
      (rowColumnMul HexagonRowColumn523.rows_assocBCA HexagonRowColumn523.cols_left0)) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (negativeScale (leftScaleExponent 5 2 3) • (left1Middle5 2 3)) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_2_3_row_6_0_2 : (((-1 : ℤ) ^ (leftScaleBit 5 2 3).val * positiveScale (leftScaleExponent 5 2 3)) •
      (rowColumnMul HexagonRowColumn523.rows_assocBCA HexagonRowColumn523.cols_left0)) ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (negativeScale (leftScaleExponent 5 2 3) • (left1Middle5 2 3)) ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_2_3_row_6_0_3 : (((-1 : ℤ) ^ (leftScaleBit 5 2 3).val * positiveScale (leftScaleExponent 5 2 3)) •
      (rowColumnMul HexagonRowColumn523.rows_assocBCA HexagonRowColumn523.cols_left0)) ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (negativeScale (leftScaleExponent 5 2 3) • (left1Middle5 2 3)) ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_2_3_row_7_0_0 : (((-1 : ℤ) ^ (leftScaleBit 5 2 3).val * positiveScale (leftScaleExponent 5 2 3)) •
      (rowColumnMul HexagonRowColumn523.rows_assocBCA HexagonRowColumn523.cols_left0)) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (negativeScale (leftScaleExponent 5 2 3) • (left1Middle5 2 3)) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_2_3_row_7_0_1 : (((-1 : ℤ) ^ (leftScaleBit 5 2 3).val * positiveScale (leftScaleExponent 5 2 3)) •
      (rowColumnMul HexagonRowColumn523.rows_assocBCA HexagonRowColumn523.cols_left0)) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (negativeScale (leftScaleExponent 5 2 3) • (left1Middle5 2 3)) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_2_3_row_7_0_2 : (((-1 : ℤ) ^ (leftScaleBit 5 2 3).val * positiveScale (leftScaleExponent 5 2 3)) •
      (rowColumnMul HexagonRowColumn523.rows_assocBCA HexagonRowColumn523.cols_left0)) ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (negativeScale (leftScaleExponent 5 2 3) • (left1Middle5 2 3)) ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_2_3_row_7_0_3 : (((-1 : ℤ) ^ (leftScaleBit 5 2 3).val * positiveScale (leftScaleExponent 5 2 3)) •
      (rowColumnMul HexagonRowColumn523.rows_assocBCA HexagonRowColumn523.cols_left0)) ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (negativeScale (leftScaleExponent 5 2 3) • (left1Middle5 2 3)) ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_2_3_checked : ((-1 : ℤ) ^ (leftScaleBit 5 2 3).val * positiveScale (leftScaleExponent 5 2 3)) •
      (rowColumnMul HexagonRowColumn523.rows_assocBCA HexagonRowColumn523.cols_left0) = negativeScale (leftScaleExponent 5 2 3) • (left1Middle5 2 3) := by
  funext r
  fin_cases r
  · exact leftFinal5_case_2_3_row_0_0_0
  · exact leftFinal5_case_2_3_row_0_0_1
  · exact leftFinal5_case_2_3_row_0_0_2
  · exact leftFinal5_case_2_3_row_0_0_3
  · exact leftFinal5_case_2_3_row_1_0_0
  · exact leftFinal5_case_2_3_row_1_0_1
  · exact leftFinal5_case_2_3_row_1_0_2
  · exact leftFinal5_case_2_3_row_1_0_3
  · exact leftFinal5_case_2_3_row_2_0_0
  · exact leftFinal5_case_2_3_row_2_0_1
  · exact leftFinal5_case_2_3_row_2_0_2
  · exact leftFinal5_case_2_3_row_2_0_3
  · exact leftFinal5_case_2_3_row_3_0_0
  · exact leftFinal5_case_2_3_row_3_0_1
  · exact leftFinal5_case_2_3_row_3_0_2
  · exact leftFinal5_case_2_3_row_3_0_3
  · exact leftFinal5_case_2_3_row_4_0_0
  · exact leftFinal5_case_2_3_row_4_0_1
  · exact leftFinal5_case_2_3_row_4_0_2
  · exact leftFinal5_case_2_3_row_4_0_3
  · exact leftFinal5_case_2_3_row_5_0_0
  · exact leftFinal5_case_2_3_row_5_0_1
  · exact leftFinal5_case_2_3_row_5_0_2
  · exact leftFinal5_case_2_3_row_5_0_3
  · exact leftFinal5_case_2_3_row_6_0_0
  · exact leftFinal5_case_2_3_row_6_0_1
  · exact leftFinal5_case_2_3_row_6_0_2
  · exact leftFinal5_case_2_3_row_6_0_3
  · exact leftFinal5_case_2_3_row_7_0_0
  · exact leftFinal5_case_2_3_row_7_0_1
  · exact leftFinal5_case_2_3_row_7_0_2
  · exact leftFinal5_case_2_3_row_7_0_3

set_option backward.isDefEq.respectTransparency false in
theorem leftFinal5_case_2_3 : ((-1 : ℤ) ^ (leftScaleBit 5 2 3).val * positiveScale (leftScaleExponent 5 2 3)) •
      (associatorZ 2 3 5 * left0Middle5 2 3) = negativeScale (leftScaleExponent 5 2 3) • (innerRightZ 2 5 3 * left1Middle5 2 3) := by
  simpa only [HexagonAtoms523.assocABC_eq,
    HexagonAtoms523.outerABC_eq,
    HexagonAtoms523.assocBAC_eq,
    HexagonAtoms523.innerABC_eq,
    HexagonAtoms523.innerRightABC_eq,
    HexagonAtoms523.inverseACB_eq,
    HexagonAtoms523.innerACB_eq,
    HexagonAtoms523.assocBCA_eq,
    HexagonAtoms523.innerRightBAC_eq,
    HexagonAtoms523.assocCAB_eq,
    HexagonAtoms523.outerLeftABC_eq,
    HexagonRowColumn523.product0_eq,
    HexagonRowColumn523.product1_eq,
    HexagonRowColumn523.product2_eq,
    HexagonRowColumn523.product3_eq,
    HexagonRowColumn523.product4_eq,
    HexagonRowColumn523.product5_eq,
    HexagonRowColumn523.product6_eq,
    HexagonRowColumn523.product7_eq] using leftFinal5_case_2_3_checked

private theorem rightFinal5_case_2_3_row_0_0_0 : (((-1 : ℤ) ^ (rightScaleBit 5 2 3).val * positiveScale (rightScaleExponent 5 2 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 3 2 : ℤ)) • HexagonAtoms523.outerLeftABC) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 5 2 3) • (rowColumnMul HexagonRowColumn523.rows_assocCAB HexagonRowColumn523.cols_right2)) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_2_3_row_0_0_1 : (((-1 : ℤ) ^ (rightScaleBit 5 2 3).val * positiveScale (rightScaleExponent 5 2 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 3 2 : ℤ)) • HexagonAtoms523.outerLeftABC) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 5 2 3) • (rowColumnMul HexagonRowColumn523.rows_assocCAB HexagonRowColumn523.cols_right2)) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_2_3_row_0_0_2 : (((-1 : ℤ) ^ (rightScaleBit 5 2 3).val * positiveScale (rightScaleExponent 5 2 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 3 2 : ℤ)) • HexagonAtoms523.outerLeftABC) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 5 2 3) • (rowColumnMul HexagonRowColumn523.rows_assocCAB HexagonRowColumn523.cols_right2)) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_2_3_row_0_0_3 : (((-1 : ℤ) ^ (rightScaleBit 5 2 3).val * positiveScale (rightScaleExponent 5 2 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 3 2 : ℤ)) • HexagonAtoms523.outerLeftABC) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 5 2 3) • (rowColumnMul HexagonRowColumn523.rows_assocCAB HexagonRowColumn523.cols_right2)) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_2_3_row_0_1_0 : (((-1 : ℤ) ^ (rightScaleBit 5 2 3).val * positiveScale (rightScaleExponent 5 2 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 3 2 : ℤ)) • HexagonAtoms523.outerLeftABC) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 5 2 3) • (rowColumnMul HexagonRowColumn523.rows_assocCAB HexagonRowColumn523.cols_right2)) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_2_3_row_0_1_1 : (((-1 : ℤ) ^ (rightScaleBit 5 2 3).val * positiveScale (rightScaleExponent 5 2 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 3 2 : ℤ)) • HexagonAtoms523.outerLeftABC) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 5 2 3) • (rowColumnMul HexagonRowColumn523.rows_assocCAB HexagonRowColumn523.cols_right2)) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_2_3_row_0_1_2 : (((-1 : ℤ) ^ (rightScaleBit 5 2 3).val * positiveScale (rightScaleExponent 5 2 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 3 2 : ℤ)) • HexagonAtoms523.outerLeftABC) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 5 2 3) • (rowColumnMul HexagonRowColumn523.rows_assocCAB HexagonRowColumn523.cols_right2)) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_2_3_row_0_1_3 : (((-1 : ℤ) ^ (rightScaleBit 5 2 3).val * positiveScale (rightScaleExponent 5 2 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 3 2 : ℤ)) • HexagonAtoms523.outerLeftABC) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 5 2 3) • (rowColumnMul HexagonRowColumn523.rows_assocCAB HexagonRowColumn523.cols_right2)) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_2_3_row_1_0_0 : (((-1 : ℤ) ^ (rightScaleBit 5 2 3).val * positiveScale (rightScaleExponent 5 2 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 3 2 : ℤ)) • HexagonAtoms523.outerLeftABC) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 5 2 3) • (rowColumnMul HexagonRowColumn523.rows_assocCAB HexagonRowColumn523.cols_right2)) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_2_3_row_1_0_1 : (((-1 : ℤ) ^ (rightScaleBit 5 2 3).val * positiveScale (rightScaleExponent 5 2 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 3 2 : ℤ)) • HexagonAtoms523.outerLeftABC) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 5 2 3) • (rowColumnMul HexagonRowColumn523.rows_assocCAB HexagonRowColumn523.cols_right2)) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_2_3_row_1_0_2 : (((-1 : ℤ) ^ (rightScaleBit 5 2 3).val * positiveScale (rightScaleExponent 5 2 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 3 2 : ℤ)) • HexagonAtoms523.outerLeftABC) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 5 2 3) • (rowColumnMul HexagonRowColumn523.rows_assocCAB HexagonRowColumn523.cols_right2)) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_2_3_row_1_0_3 : (((-1 : ℤ) ^ (rightScaleBit 5 2 3).val * positiveScale (rightScaleExponent 5 2 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 3 2 : ℤ)) • HexagonAtoms523.outerLeftABC) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 5 2 3) • (rowColumnMul HexagonRowColumn523.rows_assocCAB HexagonRowColumn523.cols_right2)) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_2_3_row_1_1_0 : (((-1 : ℤ) ^ (rightScaleBit 5 2 3).val * positiveScale (rightScaleExponent 5 2 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 3 2 : ℤ)) • HexagonAtoms523.outerLeftABC) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 5 2 3) • (rowColumnMul HexagonRowColumn523.rows_assocCAB HexagonRowColumn523.cols_right2)) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_2_3_row_1_1_1 : (((-1 : ℤ) ^ (rightScaleBit 5 2 3).val * positiveScale (rightScaleExponent 5 2 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 3 2 : ℤ)) • HexagonAtoms523.outerLeftABC) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 5 2 3) • (rowColumnMul HexagonRowColumn523.rows_assocCAB HexagonRowColumn523.cols_right2)) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_2_3_row_1_1_2 : (((-1 : ℤ) ^ (rightScaleBit 5 2 3).val * positiveScale (rightScaleExponent 5 2 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 3 2 : ℤ)) • HexagonAtoms523.outerLeftABC) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 5 2 3) • (rowColumnMul HexagonRowColumn523.rows_assocCAB HexagonRowColumn523.cols_right2)) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_2_3_row_1_1_3 : (((-1 : ℤ) ^ (rightScaleBit 5 2 3).val * positiveScale (rightScaleExponent 5 2 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 3 2 : ℤ)) • HexagonAtoms523.outerLeftABC) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 5 2 3) • (rowColumnMul HexagonRowColumn523.rows_assocCAB HexagonRowColumn523.cols_right2)) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_2_3_row_2_0_0 : (((-1 : ℤ) ^ (rightScaleBit 5 2 3).val * positiveScale (rightScaleExponent 5 2 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 3 2 : ℤ)) • HexagonAtoms523.outerLeftABC) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 5 2 3) • (rowColumnMul HexagonRowColumn523.rows_assocCAB HexagonRowColumn523.cols_right2)) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_2_3_row_2_0_1 : (((-1 : ℤ) ^ (rightScaleBit 5 2 3).val * positiveScale (rightScaleExponent 5 2 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 3 2 : ℤ)) • HexagonAtoms523.outerLeftABC) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 5 2 3) • (rowColumnMul HexagonRowColumn523.rows_assocCAB HexagonRowColumn523.cols_right2)) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_2_3_row_2_0_2 : (((-1 : ℤ) ^ (rightScaleBit 5 2 3).val * positiveScale (rightScaleExponent 5 2 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 3 2 : ℤ)) • HexagonAtoms523.outerLeftABC) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 5 2 3) • (rowColumnMul HexagonRowColumn523.rows_assocCAB HexagonRowColumn523.cols_right2)) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_2_3_row_2_0_3 : (((-1 : ℤ) ^ (rightScaleBit 5 2 3).val * positiveScale (rightScaleExponent 5 2 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 3 2 : ℤ)) • HexagonAtoms523.outerLeftABC) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 5 2 3) • (rowColumnMul HexagonRowColumn523.rows_assocCAB HexagonRowColumn523.cols_right2)) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_2_3_row_2_1_0 : (((-1 : ℤ) ^ (rightScaleBit 5 2 3).val * positiveScale (rightScaleExponent 5 2 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 3 2 : ℤ)) • HexagonAtoms523.outerLeftABC) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 5 2 3) • (rowColumnMul HexagonRowColumn523.rows_assocCAB HexagonRowColumn523.cols_right2)) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_2_3_row_2_1_1 : (((-1 : ℤ) ^ (rightScaleBit 5 2 3).val * positiveScale (rightScaleExponent 5 2 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 3 2 : ℤ)) • HexagonAtoms523.outerLeftABC) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 5 2 3) • (rowColumnMul HexagonRowColumn523.rows_assocCAB HexagonRowColumn523.cols_right2)) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_2_3_row_2_1_2 : (((-1 : ℤ) ^ (rightScaleBit 5 2 3).val * positiveScale (rightScaleExponent 5 2 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 3 2 : ℤ)) • HexagonAtoms523.outerLeftABC) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 5 2 3) • (rowColumnMul HexagonRowColumn523.rows_assocCAB HexagonRowColumn523.cols_right2)) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_2_3_row_2_1_3 : (((-1 : ℤ) ^ (rightScaleBit 5 2 3).val * positiveScale (rightScaleExponent 5 2 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 3 2 : ℤ)) • HexagonAtoms523.outerLeftABC) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 5 2 3) • (rowColumnMul HexagonRowColumn523.rows_assocCAB HexagonRowColumn523.cols_right2)) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_2_3_row_3_0_0 : (((-1 : ℤ) ^ (rightScaleBit 5 2 3).val * positiveScale (rightScaleExponent 5 2 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 3 2 : ℤ)) • HexagonAtoms523.outerLeftABC) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 5 2 3) • (rowColumnMul HexagonRowColumn523.rows_assocCAB HexagonRowColumn523.cols_right2)) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_2_3_row_3_0_1 : (((-1 : ℤ) ^ (rightScaleBit 5 2 3).val * positiveScale (rightScaleExponent 5 2 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 3 2 : ℤ)) • HexagonAtoms523.outerLeftABC) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 5 2 3) • (rowColumnMul HexagonRowColumn523.rows_assocCAB HexagonRowColumn523.cols_right2)) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_2_3_row_3_0_2 : (((-1 : ℤ) ^ (rightScaleBit 5 2 3).val * positiveScale (rightScaleExponent 5 2 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 3 2 : ℤ)) • HexagonAtoms523.outerLeftABC) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 5 2 3) • (rowColumnMul HexagonRowColumn523.rows_assocCAB HexagonRowColumn523.cols_right2)) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_2_3_row_3_0_3 : (((-1 : ℤ) ^ (rightScaleBit 5 2 3).val * positiveScale (rightScaleExponent 5 2 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 3 2 : ℤ)) • HexagonAtoms523.outerLeftABC) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 5 2 3) • (rowColumnMul HexagonRowColumn523.rows_assocCAB HexagonRowColumn523.cols_right2)) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_2_3_row_3_1_0 : (((-1 : ℤ) ^ (rightScaleBit 5 2 3).val * positiveScale (rightScaleExponent 5 2 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 3 2 : ℤ)) • HexagonAtoms523.outerLeftABC) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 5 2 3) • (rowColumnMul HexagonRowColumn523.rows_assocCAB HexagonRowColumn523.cols_right2)) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_2_3_row_3_1_1 : (((-1 : ℤ) ^ (rightScaleBit 5 2 3).val * positiveScale (rightScaleExponent 5 2 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 3 2 : ℤ)) • HexagonAtoms523.outerLeftABC) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 5 2 3) • (rowColumnMul HexagonRowColumn523.rows_assocCAB HexagonRowColumn523.cols_right2)) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_2_3_row_3_1_2 : (((-1 : ℤ) ^ (rightScaleBit 5 2 3).val * positiveScale (rightScaleExponent 5 2 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 3 2 : ℤ)) • HexagonAtoms523.outerLeftABC) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 5 2 3) • (rowColumnMul HexagonRowColumn523.rows_assocCAB HexagonRowColumn523.cols_right2)) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_2_3_row_3_1_3 : (((-1 : ℤ) ^ (rightScaleBit 5 2 3).val * positiveScale (rightScaleExponent 5 2 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 3 2 : ℤ)) • HexagonAtoms523.outerLeftABC) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 5 2 3) • (rowColumnMul HexagonRowColumn523.rows_assocCAB HexagonRowColumn523.cols_right2)) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_2_3_checked : ((-1 : ℤ) ^ (rightScaleBit 5 2 3).val * positiveScale (rightScaleExponent 5 2 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 3 2 : ℤ)) • HexagonAtoms523.outerLeftABC = negativeScale (rightScaleExponent 5 2 3) • (rowColumnMul HexagonRowColumn523.rows_assocCAB HexagonRowColumn523.cols_right2) := by
  funext r
  fin_cases r
  · exact rightFinal5_case_2_3_row_0_0_0
  · exact rightFinal5_case_2_3_row_0_0_1
  · exact rightFinal5_case_2_3_row_0_0_2
  · exact rightFinal5_case_2_3_row_0_0_3
  · exact rightFinal5_case_2_3_row_0_1_0
  · exact rightFinal5_case_2_3_row_0_1_1
  · exact rightFinal5_case_2_3_row_0_1_2
  · exact rightFinal5_case_2_3_row_0_1_3
  · exact rightFinal5_case_2_3_row_1_0_0
  · exact rightFinal5_case_2_3_row_1_0_1
  · exact rightFinal5_case_2_3_row_1_0_2
  · exact rightFinal5_case_2_3_row_1_0_3
  · exact rightFinal5_case_2_3_row_1_1_0
  · exact rightFinal5_case_2_3_row_1_1_1
  · exact rightFinal5_case_2_3_row_1_1_2
  · exact rightFinal5_case_2_3_row_1_1_3
  · exact rightFinal5_case_2_3_row_2_0_0
  · exact rightFinal5_case_2_3_row_2_0_1
  · exact rightFinal5_case_2_3_row_2_0_2
  · exact rightFinal5_case_2_3_row_2_0_3
  · exact rightFinal5_case_2_3_row_2_1_0
  · exact rightFinal5_case_2_3_row_2_1_1
  · exact rightFinal5_case_2_3_row_2_1_2
  · exact rightFinal5_case_2_3_row_2_1_3
  · exact rightFinal5_case_2_3_row_3_0_0
  · exact rightFinal5_case_2_3_row_3_0_1
  · exact rightFinal5_case_2_3_row_3_0_2
  · exact rightFinal5_case_2_3_row_3_0_3
  · exact rightFinal5_case_2_3_row_3_1_0
  · exact rightFinal5_case_2_3_row_3_1_1
  · exact rightFinal5_case_2_3_row_3_1_2
  · exact rightFinal5_case_2_3_row_3_1_3

set_option backward.isDefEq.respectTransparency false in
theorem rightFinal5_case_2_3 : ((-1 : ℤ) ^ (rightScaleBit 5 2 3).val * positiveScale (rightScaleExponent 5 2 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 3 2 : ℤ)) • outerLeftZ 5 2 3 = negativeScale (rightScaleExponent 5 2 3) • (associatorZ 3 5 2 * right2Middle5 2 3) := by
  simpa only [HexagonAtoms523.assocABC_eq,
    HexagonAtoms523.outerABC_eq,
    HexagonAtoms523.assocBAC_eq,
    HexagonAtoms523.innerABC_eq,
    HexagonAtoms523.innerRightABC_eq,
    HexagonAtoms523.inverseACB_eq,
    HexagonAtoms523.innerACB_eq,
    HexagonAtoms523.assocBCA_eq,
    HexagonAtoms523.innerRightBAC_eq,
    HexagonAtoms523.assocCAB_eq,
    HexagonAtoms523.outerLeftABC_eq,
    HexagonRowColumn523.product0_eq,
    HexagonRowColumn523.product1_eq,
    HexagonRowColumn523.product2_eq,
    HexagonRowColumn523.product3_eq,
    HexagonRowColumn523.product4_eq,
    HexagonRowColumn523.product5_eq,
    HexagonRowColumn523.product6_eq,
    HexagonRowColumn523.product7_eq] using rightFinal5_case_2_3_checked

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonCases5
