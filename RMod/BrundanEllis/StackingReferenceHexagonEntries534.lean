import RMod.BrundanEllis.StackingReferenceHexagonMiddle5
import RMod.BrundanEllis.StackingReferenceSparseMatrixCheck
import RMod.BrundanEllis.StackingReferenceHexagonAtoms534
import RMod.BrundanEllis.StackingReferenceHexagonRowColumn534

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

private theorem left0Middle5_eq_case_3_4_row_0_0_0 : (left0Middle5 3 4) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn534.rows_outerABC HexagonRowColumn534.cols_assocABC) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_3_4_row_0_0_1 : (left0Middle5 3 4) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn534.rows_outerABC HexagonRowColumn534.cols_assocABC) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_3_4_row_0_0_2 : (left0Middle5 3 4) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn534.rows_outerABC HexagonRowColumn534.cols_assocABC) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_3_4_row_0_0_3 : (left0Middle5 3 4) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn534.rows_outerABC HexagonRowColumn534.cols_assocABC) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_3_4_row_0_1_0 : (left0Middle5 3 4) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn534.rows_outerABC HexagonRowColumn534.cols_assocABC) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_3_4_row_0_1_1 : (left0Middle5 3 4) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn534.rows_outerABC HexagonRowColumn534.cols_assocABC) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_3_4_row_0_1_2 : (left0Middle5 3 4) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn534.rows_outerABC HexagonRowColumn534.cols_assocABC) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_3_4_row_0_1_3 : (left0Middle5 3 4) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn534.rows_outerABC HexagonRowColumn534.cols_assocABC) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_3_4_row_1_0_0 : (left0Middle5 3 4) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn534.rows_outerABC HexagonRowColumn534.cols_assocABC) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_3_4_row_1_0_1 : (left0Middle5 3 4) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn534.rows_outerABC HexagonRowColumn534.cols_assocABC) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_3_4_row_1_0_2 : (left0Middle5 3 4) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn534.rows_outerABC HexagonRowColumn534.cols_assocABC) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_3_4_row_1_0_3 : (left0Middle5 3 4) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn534.rows_outerABC HexagonRowColumn534.cols_assocABC) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_3_4_row_1_1_0 : (left0Middle5 3 4) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn534.rows_outerABC HexagonRowColumn534.cols_assocABC) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_3_4_row_1_1_1 : (left0Middle5 3 4) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn534.rows_outerABC HexagonRowColumn534.cols_assocABC) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_3_4_row_1_1_2 : (left0Middle5 3 4) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn534.rows_outerABC HexagonRowColumn534.cols_assocABC) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_3_4_row_1_1_3 : (left0Middle5 3 4) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn534.rows_outerABC HexagonRowColumn534.cols_assocABC) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_3_4_row_2_0_0 : (left0Middle5 3 4) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn534.rows_outerABC HexagonRowColumn534.cols_assocABC) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_3_4_row_2_0_1 : (left0Middle5 3 4) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn534.rows_outerABC HexagonRowColumn534.cols_assocABC) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_3_4_row_2_0_2 : (left0Middle5 3 4) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn534.rows_outerABC HexagonRowColumn534.cols_assocABC) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_3_4_row_2_0_3 : (left0Middle5 3 4) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn534.rows_outerABC HexagonRowColumn534.cols_assocABC) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_3_4_row_2_1_0 : (left0Middle5 3 4) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn534.rows_outerABC HexagonRowColumn534.cols_assocABC) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_3_4_row_2_1_1 : (left0Middle5 3 4) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn534.rows_outerABC HexagonRowColumn534.cols_assocABC) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_3_4_row_2_1_2 : (left0Middle5 3 4) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn534.rows_outerABC HexagonRowColumn534.cols_assocABC) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_3_4_row_2_1_3 : (left0Middle5 3 4) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn534.rows_outerABC HexagonRowColumn534.cols_assocABC) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_3_4_row_3_0_0 : (left0Middle5 3 4) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn534.rows_outerABC HexagonRowColumn534.cols_assocABC) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_3_4_row_3_0_1 : (left0Middle5 3 4) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn534.rows_outerABC HexagonRowColumn534.cols_assocABC) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_3_4_row_3_0_2 : (left0Middle5 3 4) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn534.rows_outerABC HexagonRowColumn534.cols_assocABC) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_3_4_row_3_0_3 : (left0Middle5 3 4) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn534.rows_outerABC HexagonRowColumn534.cols_assocABC) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_3_4_row_3_1_0 : (left0Middle5 3 4) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn534.rows_outerABC HexagonRowColumn534.cols_assocABC) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_3_4_row_3_1_1 : (left0Middle5 3 4) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn534.rows_outerABC HexagonRowColumn534.cols_assocABC) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_3_4_row_3_1_2 : (left0Middle5 3 4) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn534.rows_outerABC HexagonRowColumn534.cols_assocABC) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_3_4_row_3_1_3 : (left0Middle5 3 4) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn534.rows_outerABC HexagonRowColumn534.cols_assocABC) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_3_4_checked : left0Middle5 3 4 = rowColumnMul HexagonRowColumn534.rows_outerABC HexagonRowColumn534.cols_assocABC := by
  funext r
  fin_cases r
  · exact left0Middle5_eq_case_3_4_row_0_0_0
  · exact left0Middle5_eq_case_3_4_row_0_0_1
  · exact left0Middle5_eq_case_3_4_row_0_0_2
  · exact left0Middle5_eq_case_3_4_row_0_0_3
  · exact left0Middle5_eq_case_3_4_row_0_1_0
  · exact left0Middle5_eq_case_3_4_row_0_1_1
  · exact left0Middle5_eq_case_3_4_row_0_1_2
  · exact left0Middle5_eq_case_3_4_row_0_1_3
  · exact left0Middle5_eq_case_3_4_row_1_0_0
  · exact left0Middle5_eq_case_3_4_row_1_0_1
  · exact left0Middle5_eq_case_3_4_row_1_0_2
  · exact left0Middle5_eq_case_3_4_row_1_0_3
  · exact left0Middle5_eq_case_3_4_row_1_1_0
  · exact left0Middle5_eq_case_3_4_row_1_1_1
  · exact left0Middle5_eq_case_3_4_row_1_1_2
  · exact left0Middle5_eq_case_3_4_row_1_1_3
  · exact left0Middle5_eq_case_3_4_row_2_0_0
  · exact left0Middle5_eq_case_3_4_row_2_0_1
  · exact left0Middle5_eq_case_3_4_row_2_0_2
  · exact left0Middle5_eq_case_3_4_row_2_0_3
  · exact left0Middle5_eq_case_3_4_row_2_1_0
  · exact left0Middle5_eq_case_3_4_row_2_1_1
  · exact left0Middle5_eq_case_3_4_row_2_1_2
  · exact left0Middle5_eq_case_3_4_row_2_1_3
  · exact left0Middle5_eq_case_3_4_row_3_0_0
  · exact left0Middle5_eq_case_3_4_row_3_0_1
  · exact left0Middle5_eq_case_3_4_row_3_0_2
  · exact left0Middle5_eq_case_3_4_row_3_0_3
  · exact left0Middle5_eq_case_3_4_row_3_1_0
  · exact left0Middle5_eq_case_3_4_row_3_1_1
  · exact left0Middle5_eq_case_3_4_row_3_1_2
  · exact left0Middle5_eq_case_3_4_row_3_1_3

set_option backward.isDefEq.respectTransparency false in
theorem left0Middle5_eq_case_3_4 : left0Middle5 3 4 = outerRightZ 5 3 4 * associatorZ 5 3 4 := by
  simpa only [HexagonAtoms534.assocABC_eq,
    HexagonAtoms534.outerABC_eq,
    HexagonAtoms534.assocBAC_eq,
    HexagonAtoms534.innerABC_eq,
    HexagonAtoms534.innerRightABC_eq,
    HexagonAtoms534.inverseACB_eq,
    HexagonAtoms534.innerACB_eq,
    HexagonAtoms534.assocBCA_eq,
    HexagonAtoms534.innerRightBAC_eq,
    HexagonAtoms534.assocCAB_eq,
    HexagonAtoms534.outerLeftABC_eq,
    HexagonRowColumn534.product0_eq,
    HexagonRowColumn534.product1_eq,
    HexagonRowColumn534.product2_eq,
    HexagonRowColumn534.product3_eq,
    HexagonRowColumn534.product4_eq,
    HexagonRowColumn534.product5_eq,
    HexagonRowColumn534.product6_eq,
    HexagonRowColumn534.product7_eq] using left0Middle5_eq_case_3_4_checked

private theorem left1Middle5_eq_case_3_4_row_0_0_0 : (left1Middle5 3 4) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms534.assocBAC) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_3_4_row_0_0_1 : (left1Middle5 3 4) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms534.assocBAC) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_3_4_row_0_0_2 : (left1Middle5 3 4) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms534.assocBAC) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_3_4_row_0_0_3 : (left1Middle5 3 4) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms534.assocBAC) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_3_4_row_0_1_0 : (left1Middle5 3 4) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms534.assocBAC) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_3_4_row_0_1_1 : (left1Middle5 3 4) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms534.assocBAC) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_3_4_row_0_1_2 : (left1Middle5 3 4) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms534.assocBAC) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_3_4_row_0_1_3 : (left1Middle5 3 4) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms534.assocBAC) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_3_4_row_1_0_0 : (left1Middle5 3 4) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms534.assocBAC) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_3_4_row_1_0_1 : (left1Middle5 3 4) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms534.assocBAC) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_3_4_row_1_0_2 : (left1Middle5 3 4) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms534.assocBAC) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_3_4_row_1_0_3 : (left1Middle5 3 4) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms534.assocBAC) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_3_4_row_1_1_0 : (left1Middle5 3 4) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms534.assocBAC) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_3_4_row_1_1_1 : (left1Middle5 3 4) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms534.assocBAC) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_3_4_row_1_1_2 : (left1Middle5 3 4) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms534.assocBAC) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_3_4_row_1_1_3 : (left1Middle5 3 4) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms534.assocBAC) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_3_4_row_2_0_0 : (left1Middle5 3 4) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms534.assocBAC) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_3_4_row_2_0_1 : (left1Middle5 3 4) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms534.assocBAC) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_3_4_row_2_0_2 : (left1Middle5 3 4) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms534.assocBAC) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_3_4_row_2_0_3 : (left1Middle5 3 4) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms534.assocBAC) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_3_4_row_2_1_0 : (left1Middle5 3 4) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms534.assocBAC) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_3_4_row_2_1_1 : (left1Middle5 3 4) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms534.assocBAC) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_3_4_row_2_1_2 : (left1Middle5 3 4) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms534.assocBAC) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_3_4_row_2_1_3 : (left1Middle5 3 4) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms534.assocBAC) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_3_4_row_3_0_0 : (left1Middle5 3 4) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms534.assocBAC) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_3_4_row_3_0_1 : (left1Middle5 3 4) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms534.assocBAC) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_3_4_row_3_0_2 : (left1Middle5 3 4) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms534.assocBAC) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_3_4_row_3_0_3 : (left1Middle5 3 4) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms534.assocBAC) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_3_4_row_3_1_0 : (left1Middle5 3 4) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms534.assocBAC) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_3_4_row_3_1_1 : (left1Middle5 3 4) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms534.assocBAC) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_3_4_row_3_1_2 : (left1Middle5 3 4) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms534.assocBAC) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_3_4_row_3_1_3 : (left1Middle5 3 4) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms534.assocBAC) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_3_4_checked : left1Middle5 3 4 = HexagonAtoms534.assocBAC := by
  funext r
  fin_cases r
  · exact left1Middle5_eq_case_3_4_row_0_0_0
  · exact left1Middle5_eq_case_3_4_row_0_0_1
  · exact left1Middle5_eq_case_3_4_row_0_0_2
  · exact left1Middle5_eq_case_3_4_row_0_0_3
  · exact left1Middle5_eq_case_3_4_row_0_1_0
  · exact left1Middle5_eq_case_3_4_row_0_1_1
  · exact left1Middle5_eq_case_3_4_row_0_1_2
  · exact left1Middle5_eq_case_3_4_row_0_1_3
  · exact left1Middle5_eq_case_3_4_row_1_0_0
  · exact left1Middle5_eq_case_3_4_row_1_0_1
  · exact left1Middle5_eq_case_3_4_row_1_0_2
  · exact left1Middle5_eq_case_3_4_row_1_0_3
  · exact left1Middle5_eq_case_3_4_row_1_1_0
  · exact left1Middle5_eq_case_3_4_row_1_1_1
  · exact left1Middle5_eq_case_3_4_row_1_1_2
  · exact left1Middle5_eq_case_3_4_row_1_1_3
  · exact left1Middle5_eq_case_3_4_row_2_0_0
  · exact left1Middle5_eq_case_3_4_row_2_0_1
  · exact left1Middle5_eq_case_3_4_row_2_0_2
  · exact left1Middle5_eq_case_3_4_row_2_0_3
  · exact left1Middle5_eq_case_3_4_row_2_1_0
  · exact left1Middle5_eq_case_3_4_row_2_1_1
  · exact left1Middle5_eq_case_3_4_row_2_1_2
  · exact left1Middle5_eq_case_3_4_row_2_1_3
  · exact left1Middle5_eq_case_3_4_row_3_0_0
  · exact left1Middle5_eq_case_3_4_row_3_0_1
  · exact left1Middle5_eq_case_3_4_row_3_0_2
  · exact left1Middle5_eq_case_3_4_row_3_0_3
  · exact left1Middle5_eq_case_3_4_row_3_1_0
  · exact left1Middle5_eq_case_3_4_row_3_1_1
  · exact left1Middle5_eq_case_3_4_row_3_1_2
  · exact left1Middle5_eq_case_3_4_row_3_1_3

set_option backward.isDefEq.respectTransparency false in
theorem left1Middle5_eq_case_3_4 : left1Middle5 3 4 = associatorZ 3 5 4 * innerLeftZ 5 3 4 := by
  simpa only [HexagonAtoms534.assocABC_eq,
    HexagonAtoms534.outerABC_eq,
    HexagonAtoms534.assocBAC_eq,
    HexagonAtoms534.innerABC_eq,
    HexagonAtoms534.innerRightABC_eq,
    HexagonAtoms534.inverseACB_eq,
    HexagonAtoms534.innerACB_eq,
    HexagonAtoms534.assocBCA_eq,
    HexagonAtoms534.innerRightBAC_eq,
    HexagonAtoms534.assocCAB_eq,
    HexagonAtoms534.outerLeftABC_eq,
    HexagonRowColumn534.product0_eq,
    HexagonRowColumn534.product1_eq,
    HexagonRowColumn534.product2_eq,
    HexagonRowColumn534.product3_eq,
    HexagonRowColumn534.product4_eq,
    HexagonRowColumn534.product5_eq,
    HexagonRowColumn534.product6_eq,
    HexagonRowColumn534.product7_eq] using left1Middle5_eq_case_3_4_checked

private theorem right0Middle5_eq_case_3_4_row_0_0_0 : (right0Middle5 3 4) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms534.assocABC) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_3_4_row_0_0_1 : (right0Middle5 3 4) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms534.assocABC) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_3_4_row_0_0_2 : (right0Middle5 3 4) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms534.assocABC) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_3_4_row_0_0_3 : (right0Middle5 3 4) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms534.assocABC) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_3_4_row_0_1_0 : (right0Middle5 3 4) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms534.assocABC) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_3_4_row_0_1_1 : (right0Middle5 3 4) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms534.assocABC) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_3_4_row_0_1_2 : (right0Middle5 3 4) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms534.assocABC) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_3_4_row_0_1_3 : (right0Middle5 3 4) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms534.assocABC) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_3_4_row_1_0_0 : (right0Middle5 3 4) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms534.assocABC) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_3_4_row_1_0_1 : (right0Middle5 3 4) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms534.assocABC) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_3_4_row_1_0_2 : (right0Middle5 3 4) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms534.assocABC) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_3_4_row_1_0_3 : (right0Middle5 3 4) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms534.assocABC) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_3_4_row_1_1_0 : (right0Middle5 3 4) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms534.assocABC) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_3_4_row_1_1_1 : (right0Middle5 3 4) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms534.assocABC) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_3_4_row_1_1_2 : (right0Middle5 3 4) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms534.assocABC) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_3_4_row_1_1_3 : (right0Middle5 3 4) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms534.assocABC) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_3_4_row_2_0_0 : (right0Middle5 3 4) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms534.assocABC) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_3_4_row_2_0_1 : (right0Middle5 3 4) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms534.assocABC) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_3_4_row_2_0_2 : (right0Middle5 3 4) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms534.assocABC) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_3_4_row_2_0_3 : (right0Middle5 3 4) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms534.assocABC) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_3_4_row_2_1_0 : (right0Middle5 3 4) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms534.assocABC) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_3_4_row_2_1_1 : (right0Middle5 3 4) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms534.assocABC) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_3_4_row_2_1_2 : (right0Middle5 3 4) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms534.assocABC) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_3_4_row_2_1_3 : (right0Middle5 3 4) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms534.assocABC) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_3_4_row_3_0_0 : (right0Middle5 3 4) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms534.assocABC) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_3_4_row_3_0_1 : (right0Middle5 3 4) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms534.assocABC) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_3_4_row_3_0_2 : (right0Middle5 3 4) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms534.assocABC) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_3_4_row_3_0_3 : (right0Middle5 3 4) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms534.assocABC) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_3_4_row_3_1_0 : (right0Middle5 3 4) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms534.assocABC) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_3_4_row_3_1_1 : (right0Middle5 3 4) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms534.assocABC) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_3_4_row_3_1_2 : (right0Middle5 3 4) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms534.assocABC) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_3_4_row_3_1_3 : (right0Middle5 3 4) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms534.assocABC) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_3_4_checked : right0Middle5 3 4 = HexagonAtoms534.assocABC := by
  funext r
  fin_cases r
  · exact right0Middle5_eq_case_3_4_row_0_0_0
  · exact right0Middle5_eq_case_3_4_row_0_0_1
  · exact right0Middle5_eq_case_3_4_row_0_0_2
  · exact right0Middle5_eq_case_3_4_row_0_0_3
  · exact right0Middle5_eq_case_3_4_row_0_1_0
  · exact right0Middle5_eq_case_3_4_row_0_1_1
  · exact right0Middle5_eq_case_3_4_row_0_1_2
  · exact right0Middle5_eq_case_3_4_row_0_1_3
  · exact right0Middle5_eq_case_3_4_row_1_0_0
  · exact right0Middle5_eq_case_3_4_row_1_0_1
  · exact right0Middle5_eq_case_3_4_row_1_0_2
  · exact right0Middle5_eq_case_3_4_row_1_0_3
  · exact right0Middle5_eq_case_3_4_row_1_1_0
  · exact right0Middle5_eq_case_3_4_row_1_1_1
  · exact right0Middle5_eq_case_3_4_row_1_1_2
  · exact right0Middle5_eq_case_3_4_row_1_1_3
  · exact right0Middle5_eq_case_3_4_row_2_0_0
  · exact right0Middle5_eq_case_3_4_row_2_0_1
  · exact right0Middle5_eq_case_3_4_row_2_0_2
  · exact right0Middle5_eq_case_3_4_row_2_0_3
  · exact right0Middle5_eq_case_3_4_row_2_1_0
  · exact right0Middle5_eq_case_3_4_row_2_1_1
  · exact right0Middle5_eq_case_3_4_row_2_1_2
  · exact right0Middle5_eq_case_3_4_row_2_1_3
  · exact right0Middle5_eq_case_3_4_row_3_0_0
  · exact right0Middle5_eq_case_3_4_row_3_0_1
  · exact right0Middle5_eq_case_3_4_row_3_0_2
  · exact right0Middle5_eq_case_3_4_row_3_0_3
  · exact right0Middle5_eq_case_3_4_row_3_1_0
  · exact right0Middle5_eq_case_3_4_row_3_1_1
  · exact right0Middle5_eq_case_3_4_row_3_1_2
  · exact right0Middle5_eq_case_3_4_row_3_1_3

set_option backward.isDefEq.respectTransparency false in
theorem right0Middle5_eq_case_3_4 : right0Middle5 3 4 = innerRightZ 5 3 4 * associatorZ 5 3 4 := by
  simpa only [HexagonAtoms534.assocABC_eq,
    HexagonAtoms534.outerABC_eq,
    HexagonAtoms534.assocBAC_eq,
    HexagonAtoms534.innerABC_eq,
    HexagonAtoms534.innerRightABC_eq,
    HexagonAtoms534.inverseACB_eq,
    HexagonAtoms534.innerACB_eq,
    HexagonAtoms534.assocBCA_eq,
    HexagonAtoms534.innerRightBAC_eq,
    HexagonAtoms534.assocCAB_eq,
    HexagonAtoms534.outerLeftABC_eq,
    HexagonRowColumn534.product0_eq,
    HexagonRowColumn534.product1_eq,
    HexagonRowColumn534.product2_eq,
    HexagonRowColumn534.product3_eq,
    HexagonRowColumn534.product4_eq,
    HexagonRowColumn534.product5_eq,
    HexagonRowColumn534.product6_eq,
    HexagonRowColumn534.product7_eq] using right0Middle5_eq_case_3_4_checked

private theorem right1Middle5_eq_case_3_4_row_0_0_0 : (right1Middle5 3 4) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn534.rows_inverseACB HexagonRowColumn534.cols_right0) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_3_4_row_0_0_1 : (right1Middle5 3 4) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn534.rows_inverseACB HexagonRowColumn534.cols_right0) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_3_4_row_0_0_2 : (right1Middle5 3 4) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn534.rows_inverseACB HexagonRowColumn534.cols_right0) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_3_4_row_0_0_3 : (right1Middle5 3 4) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn534.rows_inverseACB HexagonRowColumn534.cols_right0) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_3_4_row_0_1_0 : (right1Middle5 3 4) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn534.rows_inverseACB HexagonRowColumn534.cols_right0) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_3_4_row_0_1_1 : (right1Middle5 3 4) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn534.rows_inverseACB HexagonRowColumn534.cols_right0) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_3_4_row_0_1_2 : (right1Middle5 3 4) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn534.rows_inverseACB HexagonRowColumn534.cols_right0) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_3_4_row_0_1_3 : (right1Middle5 3 4) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn534.rows_inverseACB HexagonRowColumn534.cols_right0) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_3_4_row_1_0_0 : (right1Middle5 3 4) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn534.rows_inverseACB HexagonRowColumn534.cols_right0) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_3_4_row_1_0_1 : (right1Middle5 3 4) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn534.rows_inverseACB HexagonRowColumn534.cols_right0) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_3_4_row_1_0_2 : (right1Middle5 3 4) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn534.rows_inverseACB HexagonRowColumn534.cols_right0) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_3_4_row_1_0_3 : (right1Middle5 3 4) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn534.rows_inverseACB HexagonRowColumn534.cols_right0) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_3_4_row_1_1_0 : (right1Middle5 3 4) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn534.rows_inverseACB HexagonRowColumn534.cols_right0) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_3_4_row_1_1_1 : (right1Middle5 3 4) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn534.rows_inverseACB HexagonRowColumn534.cols_right0) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_3_4_row_1_1_2 : (right1Middle5 3 4) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn534.rows_inverseACB HexagonRowColumn534.cols_right0) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_3_4_row_1_1_3 : (right1Middle5 3 4) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn534.rows_inverseACB HexagonRowColumn534.cols_right0) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_3_4_row_2_0_0 : (right1Middle5 3 4) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn534.rows_inverseACB HexagonRowColumn534.cols_right0) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_3_4_row_2_0_1 : (right1Middle5 3 4) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn534.rows_inverseACB HexagonRowColumn534.cols_right0) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_3_4_row_2_0_2 : (right1Middle5 3 4) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn534.rows_inverseACB HexagonRowColumn534.cols_right0) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_3_4_row_2_0_3 : (right1Middle5 3 4) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn534.rows_inverseACB HexagonRowColumn534.cols_right0) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_3_4_row_2_1_0 : (right1Middle5 3 4) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn534.rows_inverseACB HexagonRowColumn534.cols_right0) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_3_4_row_2_1_1 : (right1Middle5 3 4) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn534.rows_inverseACB HexagonRowColumn534.cols_right0) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_3_4_row_2_1_2 : (right1Middle5 3 4) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn534.rows_inverseACB HexagonRowColumn534.cols_right0) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_3_4_row_2_1_3 : (right1Middle5 3 4) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn534.rows_inverseACB HexagonRowColumn534.cols_right0) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_3_4_row_3_0_0 : (right1Middle5 3 4) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn534.rows_inverseACB HexagonRowColumn534.cols_right0) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_3_4_row_3_0_1 : (right1Middle5 3 4) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn534.rows_inverseACB HexagonRowColumn534.cols_right0) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_3_4_row_3_0_2 : (right1Middle5 3 4) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn534.rows_inverseACB HexagonRowColumn534.cols_right0) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_3_4_row_3_0_3 : (right1Middle5 3 4) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn534.rows_inverseACB HexagonRowColumn534.cols_right0) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_3_4_row_3_1_0 : (right1Middle5 3 4) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn534.rows_inverseACB HexagonRowColumn534.cols_right0) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_3_4_row_3_1_1 : (right1Middle5 3 4) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn534.rows_inverseACB HexagonRowColumn534.cols_right0) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_3_4_row_3_1_2 : (right1Middle5 3 4) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn534.rows_inverseACB HexagonRowColumn534.cols_right0) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_3_4_row_3_1_3 : (right1Middle5 3 4) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn534.rows_inverseACB HexagonRowColumn534.cols_right0) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_3_4_checked : right1Middle5 3 4 = rowColumnMul HexagonRowColumn534.rows_inverseACB HexagonRowColumn534.cols_right0 := by
  funext r
  fin_cases r
  · exact right1Middle5_eq_case_3_4_row_0_0_0
  · exact right1Middle5_eq_case_3_4_row_0_0_1
  · exact right1Middle5_eq_case_3_4_row_0_0_2
  · exact right1Middle5_eq_case_3_4_row_0_0_3
  · exact right1Middle5_eq_case_3_4_row_0_1_0
  · exact right1Middle5_eq_case_3_4_row_0_1_1
  · exact right1Middle5_eq_case_3_4_row_0_1_2
  · exact right1Middle5_eq_case_3_4_row_0_1_3
  · exact right1Middle5_eq_case_3_4_row_1_0_0
  · exact right1Middle5_eq_case_3_4_row_1_0_1
  · exact right1Middle5_eq_case_3_4_row_1_0_2
  · exact right1Middle5_eq_case_3_4_row_1_0_3
  · exact right1Middle5_eq_case_3_4_row_1_1_0
  · exact right1Middle5_eq_case_3_4_row_1_1_1
  · exact right1Middle5_eq_case_3_4_row_1_1_2
  · exact right1Middle5_eq_case_3_4_row_1_1_3
  · exact right1Middle5_eq_case_3_4_row_2_0_0
  · exact right1Middle5_eq_case_3_4_row_2_0_1
  · exact right1Middle5_eq_case_3_4_row_2_0_2
  · exact right1Middle5_eq_case_3_4_row_2_0_3
  · exact right1Middle5_eq_case_3_4_row_2_1_0
  · exact right1Middle5_eq_case_3_4_row_2_1_1
  · exact right1Middle5_eq_case_3_4_row_2_1_2
  · exact right1Middle5_eq_case_3_4_row_2_1_3
  · exact right1Middle5_eq_case_3_4_row_3_0_0
  · exact right1Middle5_eq_case_3_4_row_3_0_1
  · exact right1Middle5_eq_case_3_4_row_3_0_2
  · exact right1Middle5_eq_case_3_4_row_3_0_3
  · exact right1Middle5_eq_case_3_4_row_3_1_0
  · exact right1Middle5_eq_case_3_4_row_3_1_1
  · exact right1Middle5_eq_case_3_4_row_3_1_2
  · exact right1Middle5_eq_case_3_4_row_3_1_3

set_option backward.isDefEq.respectTransparency false in
theorem right1Middle5_eq_case_3_4 : right1Middle5 3 4 = associatorInverseZ 5 4 3 * right0Middle5 3 4 := by
  simpa only [HexagonAtoms534.assocABC_eq,
    HexagonAtoms534.outerABC_eq,
    HexagonAtoms534.assocBAC_eq,
    HexagonAtoms534.innerABC_eq,
    HexagonAtoms534.innerRightABC_eq,
    HexagonAtoms534.inverseACB_eq,
    HexagonAtoms534.innerACB_eq,
    HexagonAtoms534.assocBCA_eq,
    HexagonAtoms534.innerRightBAC_eq,
    HexagonAtoms534.assocCAB_eq,
    HexagonAtoms534.outerLeftABC_eq,
    HexagonRowColumn534.product0_eq,
    HexagonRowColumn534.product1_eq,
    HexagonRowColumn534.product2_eq,
    HexagonRowColumn534.product3_eq,
    HexagonRowColumn534.product4_eq,
    HexagonRowColumn534.product5_eq,
    HexagonRowColumn534.product6_eq,
    HexagonRowColumn534.product7_eq] using right1Middle5_eq_case_3_4_checked

private theorem right2Middle5_eq_case_3_4_row_0_0_0 : (right2Middle5 3 4) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (right1Middle5 3 4) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_3_4_row_0_0_1 : (right2Middle5 3 4) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (right1Middle5 3 4) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_3_4_row_0_0_2 : (right2Middle5 3 4) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (right1Middle5 3 4) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_3_4_row_0_0_3 : (right2Middle5 3 4) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (right1Middle5 3 4) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_3_4_row_0_1_0 : (right2Middle5 3 4) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (right1Middle5 3 4) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_3_4_row_0_1_1 : (right2Middle5 3 4) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (right1Middle5 3 4) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_3_4_row_0_1_2 : (right2Middle5 3 4) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (right1Middle5 3 4) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_3_4_row_0_1_3 : (right2Middle5 3 4) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (right1Middle5 3 4) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_3_4_row_1_0_0 : (right2Middle5 3 4) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (right1Middle5 3 4) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_3_4_row_1_0_1 : (right2Middle5 3 4) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (right1Middle5 3 4) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_3_4_row_1_0_2 : (right2Middle5 3 4) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (right1Middle5 3 4) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_3_4_row_1_0_3 : (right2Middle5 3 4) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (right1Middle5 3 4) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_3_4_row_1_1_0 : (right2Middle5 3 4) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (right1Middle5 3 4) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_3_4_row_1_1_1 : (right2Middle5 3 4) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (right1Middle5 3 4) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_3_4_row_1_1_2 : (right2Middle5 3 4) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (right1Middle5 3 4) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_3_4_row_1_1_3 : (right2Middle5 3 4) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (right1Middle5 3 4) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_3_4_row_2_0_0 : (right2Middle5 3 4) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (right1Middle5 3 4) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_3_4_row_2_0_1 : (right2Middle5 3 4) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (right1Middle5 3 4) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_3_4_row_2_0_2 : (right2Middle5 3 4) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (right1Middle5 3 4) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_3_4_row_2_0_3 : (right2Middle5 3 4) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (right1Middle5 3 4) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_3_4_row_2_1_0 : (right2Middle5 3 4) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (right1Middle5 3 4) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_3_4_row_2_1_1 : (right2Middle5 3 4) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (right1Middle5 3 4) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_3_4_row_2_1_2 : (right2Middle5 3 4) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (right1Middle5 3 4) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_3_4_row_2_1_3 : (right2Middle5 3 4) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (right1Middle5 3 4) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_3_4_row_3_0_0 : (right2Middle5 3 4) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (right1Middle5 3 4) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_3_4_row_3_0_1 : (right2Middle5 3 4) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (right1Middle5 3 4) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_3_4_row_3_0_2 : (right2Middle5 3 4) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (right1Middle5 3 4) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_3_4_row_3_0_3 : (right2Middle5 3 4) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (right1Middle5 3 4) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_3_4_row_3_1_0 : (right2Middle5 3 4) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (right1Middle5 3 4) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_3_4_row_3_1_1 : (right2Middle5 3 4) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (right1Middle5 3 4) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_3_4_row_3_1_2 : (right2Middle5 3 4) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (right1Middle5 3 4) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_3_4_row_3_1_3 : (right2Middle5 3 4) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (right1Middle5 3 4) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_3_4_checked : right2Middle5 3 4 = right1Middle5 3 4 := by
  funext r
  fin_cases r
  · exact right2Middle5_eq_case_3_4_row_0_0_0
  · exact right2Middle5_eq_case_3_4_row_0_0_1
  · exact right2Middle5_eq_case_3_4_row_0_0_2
  · exact right2Middle5_eq_case_3_4_row_0_0_3
  · exact right2Middle5_eq_case_3_4_row_0_1_0
  · exact right2Middle5_eq_case_3_4_row_0_1_1
  · exact right2Middle5_eq_case_3_4_row_0_1_2
  · exact right2Middle5_eq_case_3_4_row_0_1_3
  · exact right2Middle5_eq_case_3_4_row_1_0_0
  · exact right2Middle5_eq_case_3_4_row_1_0_1
  · exact right2Middle5_eq_case_3_4_row_1_0_2
  · exact right2Middle5_eq_case_3_4_row_1_0_3
  · exact right2Middle5_eq_case_3_4_row_1_1_0
  · exact right2Middle5_eq_case_3_4_row_1_1_1
  · exact right2Middle5_eq_case_3_4_row_1_1_2
  · exact right2Middle5_eq_case_3_4_row_1_1_3
  · exact right2Middle5_eq_case_3_4_row_2_0_0
  · exact right2Middle5_eq_case_3_4_row_2_0_1
  · exact right2Middle5_eq_case_3_4_row_2_0_2
  · exact right2Middle5_eq_case_3_4_row_2_0_3
  · exact right2Middle5_eq_case_3_4_row_2_1_0
  · exact right2Middle5_eq_case_3_4_row_2_1_1
  · exact right2Middle5_eq_case_3_4_row_2_1_2
  · exact right2Middle5_eq_case_3_4_row_2_1_3
  · exact right2Middle5_eq_case_3_4_row_3_0_0
  · exact right2Middle5_eq_case_3_4_row_3_0_1
  · exact right2Middle5_eq_case_3_4_row_3_0_2
  · exact right2Middle5_eq_case_3_4_row_3_0_3
  · exact right2Middle5_eq_case_3_4_row_3_1_0
  · exact right2Middle5_eq_case_3_4_row_3_1_1
  · exact right2Middle5_eq_case_3_4_row_3_1_2
  · exact right2Middle5_eq_case_3_4_row_3_1_3

set_option backward.isDefEq.respectTransparency false in
theorem right2Middle5_eq_case_3_4 : right2Middle5 3 4 = innerLeftZ 5 4 3 * right1Middle5 3 4 := by
  simpa only [HexagonAtoms534.assocABC_eq,
    HexagonAtoms534.outerABC_eq,
    HexagonAtoms534.assocBAC_eq,
    HexagonAtoms534.innerABC_eq,
    HexagonAtoms534.innerRightABC_eq,
    HexagonAtoms534.inverseACB_eq,
    HexagonAtoms534.innerACB_eq,
    HexagonAtoms534.assocBCA_eq,
    HexagonAtoms534.innerRightBAC_eq,
    HexagonAtoms534.assocCAB_eq,
    HexagonAtoms534.outerLeftABC_eq,
    HexagonRowColumn534.product0_eq,
    HexagonRowColumn534.product1_eq,
    HexagonRowColumn534.product2_eq,
    HexagonRowColumn534.product3_eq,
    HexagonRowColumn534.product4_eq,
    HexagonRowColumn534.product5_eq,
    HexagonRowColumn534.product6_eq,
    HexagonRowColumn534.product7_eq] using right2Middle5_eq_case_3_4_checked

private theorem leftFinal5_case_3_4_row_0_0_0 : (((-1 : ℤ) ^ (leftScaleBit 5 3 4).val * positiveScale (leftScaleExponent 5 3 4)) •
      (rowColumnMul HexagonRowColumn534.rows_assocBCA HexagonRowColumn534.cols_left0)) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 5 3 4) • (left1Middle5 3 4)) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal5_case_3_4_row_0_0_1 : (((-1 : ℤ) ^ (leftScaleBit 5 3 4).val * positiveScale (leftScaleExponent 5 3 4)) •
      (rowColumnMul HexagonRowColumn534.rows_assocBCA HexagonRowColumn534.cols_left0)) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 5 3 4) • (left1Middle5 3 4)) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal5_case_3_4_row_0_0_2 : (((-1 : ℤ) ^ (leftScaleBit 5 3 4).val * positiveScale (leftScaleExponent 5 3 4)) •
      (rowColumnMul HexagonRowColumn534.rows_assocBCA HexagonRowColumn534.cols_left0)) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 5 3 4) • (left1Middle5 3 4)) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal5_case_3_4_row_0_0_3 : (((-1 : ℤ) ^ (leftScaleBit 5 3 4).val * positiveScale (leftScaleExponent 5 3 4)) •
      (rowColumnMul HexagonRowColumn534.rows_assocBCA HexagonRowColumn534.cols_left0)) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 5 3 4) • (left1Middle5 3 4)) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal5_case_3_4_row_0_1_0 : (((-1 : ℤ) ^ (leftScaleBit 5 3 4).val * positiveScale (leftScaleExponent 5 3 4)) •
      (rowColumnMul HexagonRowColumn534.rows_assocBCA HexagonRowColumn534.cols_left0)) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 5 3 4) • (left1Middle5 3 4)) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal5_case_3_4_row_0_1_1 : (((-1 : ℤ) ^ (leftScaleBit 5 3 4).val * positiveScale (leftScaleExponent 5 3 4)) •
      (rowColumnMul HexagonRowColumn534.rows_assocBCA HexagonRowColumn534.cols_left0)) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 5 3 4) • (left1Middle5 3 4)) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal5_case_3_4_row_0_1_2 : (((-1 : ℤ) ^ (leftScaleBit 5 3 4).val * positiveScale (leftScaleExponent 5 3 4)) •
      (rowColumnMul HexagonRowColumn534.rows_assocBCA HexagonRowColumn534.cols_left0)) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 5 3 4) • (left1Middle5 3 4)) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal5_case_3_4_row_0_1_3 : (((-1 : ℤ) ^ (leftScaleBit 5 3 4).val * positiveScale (leftScaleExponent 5 3 4)) •
      (rowColumnMul HexagonRowColumn534.rows_assocBCA HexagonRowColumn534.cols_left0)) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 5 3 4) • (left1Middle5 3 4)) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal5_case_3_4_row_1_0_0 : (((-1 : ℤ) ^ (leftScaleBit 5 3 4).val * positiveScale (leftScaleExponent 5 3 4)) •
      (rowColumnMul HexagonRowColumn534.rows_assocBCA HexagonRowColumn534.cols_left0)) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 5 3 4) • (left1Middle5 3 4)) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal5_case_3_4_row_1_0_1 : (((-1 : ℤ) ^ (leftScaleBit 5 3 4).val * positiveScale (leftScaleExponent 5 3 4)) •
      (rowColumnMul HexagonRowColumn534.rows_assocBCA HexagonRowColumn534.cols_left0)) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 5 3 4) • (left1Middle5 3 4)) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal5_case_3_4_row_1_0_2 : (((-1 : ℤ) ^ (leftScaleBit 5 3 4).val * positiveScale (leftScaleExponent 5 3 4)) •
      (rowColumnMul HexagonRowColumn534.rows_assocBCA HexagonRowColumn534.cols_left0)) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 5 3 4) • (left1Middle5 3 4)) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal5_case_3_4_row_1_0_3 : (((-1 : ℤ) ^ (leftScaleBit 5 3 4).val * positiveScale (leftScaleExponent 5 3 4)) •
      (rowColumnMul HexagonRowColumn534.rows_assocBCA HexagonRowColumn534.cols_left0)) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 5 3 4) • (left1Middle5 3 4)) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal5_case_3_4_row_1_1_0 : (((-1 : ℤ) ^ (leftScaleBit 5 3 4).val * positiveScale (leftScaleExponent 5 3 4)) •
      (rowColumnMul HexagonRowColumn534.rows_assocBCA HexagonRowColumn534.cols_left0)) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 5 3 4) • (left1Middle5 3 4)) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal5_case_3_4_row_1_1_1 : (((-1 : ℤ) ^ (leftScaleBit 5 3 4).val * positiveScale (leftScaleExponent 5 3 4)) •
      (rowColumnMul HexagonRowColumn534.rows_assocBCA HexagonRowColumn534.cols_left0)) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 5 3 4) • (left1Middle5 3 4)) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal5_case_3_4_row_1_1_2 : (((-1 : ℤ) ^ (leftScaleBit 5 3 4).val * positiveScale (leftScaleExponent 5 3 4)) •
      (rowColumnMul HexagonRowColumn534.rows_assocBCA HexagonRowColumn534.cols_left0)) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 5 3 4) • (left1Middle5 3 4)) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal5_case_3_4_row_1_1_3 : (((-1 : ℤ) ^ (leftScaleBit 5 3 4).val * positiveScale (leftScaleExponent 5 3 4)) •
      (rowColumnMul HexagonRowColumn534.rows_assocBCA HexagonRowColumn534.cols_left0)) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 5 3 4) • (left1Middle5 3 4)) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal5_case_3_4_row_2_0_0 : (((-1 : ℤ) ^ (leftScaleBit 5 3 4).val * positiveScale (leftScaleExponent 5 3 4)) •
      (rowColumnMul HexagonRowColumn534.rows_assocBCA HexagonRowColumn534.cols_left0)) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 5 3 4) • (left1Middle5 3 4)) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal5_case_3_4_row_2_0_1 : (((-1 : ℤ) ^ (leftScaleBit 5 3 4).val * positiveScale (leftScaleExponent 5 3 4)) •
      (rowColumnMul HexagonRowColumn534.rows_assocBCA HexagonRowColumn534.cols_left0)) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 5 3 4) • (left1Middle5 3 4)) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal5_case_3_4_row_2_0_2 : (((-1 : ℤ) ^ (leftScaleBit 5 3 4).val * positiveScale (leftScaleExponent 5 3 4)) •
      (rowColumnMul HexagonRowColumn534.rows_assocBCA HexagonRowColumn534.cols_left0)) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 5 3 4) • (left1Middle5 3 4)) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal5_case_3_4_row_2_0_3 : (((-1 : ℤ) ^ (leftScaleBit 5 3 4).val * positiveScale (leftScaleExponent 5 3 4)) •
      (rowColumnMul HexagonRowColumn534.rows_assocBCA HexagonRowColumn534.cols_left0)) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 5 3 4) • (left1Middle5 3 4)) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal5_case_3_4_row_2_1_0 : (((-1 : ℤ) ^ (leftScaleBit 5 3 4).val * positiveScale (leftScaleExponent 5 3 4)) •
      (rowColumnMul HexagonRowColumn534.rows_assocBCA HexagonRowColumn534.cols_left0)) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 5 3 4) • (left1Middle5 3 4)) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal5_case_3_4_row_2_1_1 : (((-1 : ℤ) ^ (leftScaleBit 5 3 4).val * positiveScale (leftScaleExponent 5 3 4)) •
      (rowColumnMul HexagonRowColumn534.rows_assocBCA HexagonRowColumn534.cols_left0)) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 5 3 4) • (left1Middle5 3 4)) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal5_case_3_4_row_2_1_2 : (((-1 : ℤ) ^ (leftScaleBit 5 3 4).val * positiveScale (leftScaleExponent 5 3 4)) •
      (rowColumnMul HexagonRowColumn534.rows_assocBCA HexagonRowColumn534.cols_left0)) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 5 3 4) • (left1Middle5 3 4)) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal5_case_3_4_row_2_1_3 : (((-1 : ℤ) ^ (leftScaleBit 5 3 4).val * positiveScale (leftScaleExponent 5 3 4)) •
      (rowColumnMul HexagonRowColumn534.rows_assocBCA HexagonRowColumn534.cols_left0)) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 5 3 4) • (left1Middle5 3 4)) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal5_case_3_4_row_3_0_0 : (((-1 : ℤ) ^ (leftScaleBit 5 3 4).val * positiveScale (leftScaleExponent 5 3 4)) •
      (rowColumnMul HexagonRowColumn534.rows_assocBCA HexagonRowColumn534.cols_left0)) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 5 3 4) • (left1Middle5 3 4)) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal5_case_3_4_row_3_0_1 : (((-1 : ℤ) ^ (leftScaleBit 5 3 4).val * positiveScale (leftScaleExponent 5 3 4)) •
      (rowColumnMul HexagonRowColumn534.rows_assocBCA HexagonRowColumn534.cols_left0)) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 5 3 4) • (left1Middle5 3 4)) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal5_case_3_4_row_3_0_2 : (((-1 : ℤ) ^ (leftScaleBit 5 3 4).val * positiveScale (leftScaleExponent 5 3 4)) •
      (rowColumnMul HexagonRowColumn534.rows_assocBCA HexagonRowColumn534.cols_left0)) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 5 3 4) • (left1Middle5 3 4)) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal5_case_3_4_row_3_0_3 : (((-1 : ℤ) ^ (leftScaleBit 5 3 4).val * positiveScale (leftScaleExponent 5 3 4)) •
      (rowColumnMul HexagonRowColumn534.rows_assocBCA HexagonRowColumn534.cols_left0)) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 5 3 4) • (left1Middle5 3 4)) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal5_case_3_4_row_3_1_0 : (((-1 : ℤ) ^ (leftScaleBit 5 3 4).val * positiveScale (leftScaleExponent 5 3 4)) •
      (rowColumnMul HexagonRowColumn534.rows_assocBCA HexagonRowColumn534.cols_left0)) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 5 3 4) • (left1Middle5 3 4)) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal5_case_3_4_row_3_1_1 : (((-1 : ℤ) ^ (leftScaleBit 5 3 4).val * positiveScale (leftScaleExponent 5 3 4)) •
      (rowColumnMul HexagonRowColumn534.rows_assocBCA HexagonRowColumn534.cols_left0)) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 5 3 4) • (left1Middle5 3 4)) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal5_case_3_4_row_3_1_2 : (((-1 : ℤ) ^ (leftScaleBit 5 3 4).val * positiveScale (leftScaleExponent 5 3 4)) •
      (rowColumnMul HexagonRowColumn534.rows_assocBCA HexagonRowColumn534.cols_left0)) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 5 3 4) • (left1Middle5 3 4)) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal5_case_3_4_row_3_1_3 : (((-1 : ℤ) ^ (leftScaleBit 5 3 4).val * positiveScale (leftScaleExponent 5 3 4)) •
      (rowColumnMul HexagonRowColumn534.rows_assocBCA HexagonRowColumn534.cols_left0)) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 5 3 4) • (left1Middle5 3 4)) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal5_case_3_4_checked : ((-1 : ℤ) ^ (leftScaleBit 5 3 4).val * positiveScale (leftScaleExponent 5 3 4)) •
      (rowColumnMul HexagonRowColumn534.rows_assocBCA HexagonRowColumn534.cols_left0) = negativeScale (leftScaleExponent 5 3 4) • (left1Middle5 3 4) := by
  funext r
  fin_cases r
  · exact leftFinal5_case_3_4_row_0_0_0
  · exact leftFinal5_case_3_4_row_0_0_1
  · exact leftFinal5_case_3_4_row_0_0_2
  · exact leftFinal5_case_3_4_row_0_0_3
  · exact leftFinal5_case_3_4_row_0_1_0
  · exact leftFinal5_case_3_4_row_0_1_1
  · exact leftFinal5_case_3_4_row_0_1_2
  · exact leftFinal5_case_3_4_row_0_1_3
  · exact leftFinal5_case_3_4_row_1_0_0
  · exact leftFinal5_case_3_4_row_1_0_1
  · exact leftFinal5_case_3_4_row_1_0_2
  · exact leftFinal5_case_3_4_row_1_0_3
  · exact leftFinal5_case_3_4_row_1_1_0
  · exact leftFinal5_case_3_4_row_1_1_1
  · exact leftFinal5_case_3_4_row_1_1_2
  · exact leftFinal5_case_3_4_row_1_1_3
  · exact leftFinal5_case_3_4_row_2_0_0
  · exact leftFinal5_case_3_4_row_2_0_1
  · exact leftFinal5_case_3_4_row_2_0_2
  · exact leftFinal5_case_3_4_row_2_0_3
  · exact leftFinal5_case_3_4_row_2_1_0
  · exact leftFinal5_case_3_4_row_2_1_1
  · exact leftFinal5_case_3_4_row_2_1_2
  · exact leftFinal5_case_3_4_row_2_1_3
  · exact leftFinal5_case_3_4_row_3_0_0
  · exact leftFinal5_case_3_4_row_3_0_1
  · exact leftFinal5_case_3_4_row_3_0_2
  · exact leftFinal5_case_3_4_row_3_0_3
  · exact leftFinal5_case_3_4_row_3_1_0
  · exact leftFinal5_case_3_4_row_3_1_1
  · exact leftFinal5_case_3_4_row_3_1_2
  · exact leftFinal5_case_3_4_row_3_1_3

set_option backward.isDefEq.respectTransparency false in
theorem leftFinal5_case_3_4 : ((-1 : ℤ) ^ (leftScaleBit 5 3 4).val * positiveScale (leftScaleExponent 5 3 4)) •
      (associatorZ 3 4 5 * left0Middle5 3 4) = negativeScale (leftScaleExponent 5 3 4) • (innerRightZ 3 5 4 * left1Middle5 3 4) := by
  simpa only [HexagonAtoms534.assocABC_eq,
    HexagonAtoms534.outerABC_eq,
    HexagonAtoms534.assocBAC_eq,
    HexagonAtoms534.innerABC_eq,
    HexagonAtoms534.innerRightABC_eq,
    HexagonAtoms534.inverseACB_eq,
    HexagonAtoms534.innerACB_eq,
    HexagonAtoms534.assocBCA_eq,
    HexagonAtoms534.innerRightBAC_eq,
    HexagonAtoms534.assocCAB_eq,
    HexagonAtoms534.outerLeftABC_eq,
    HexagonRowColumn534.product0_eq,
    HexagonRowColumn534.product1_eq,
    HexagonRowColumn534.product2_eq,
    HexagonRowColumn534.product3_eq,
    HexagonRowColumn534.product4_eq,
    HexagonRowColumn534.product5_eq,
    HexagonRowColumn534.product6_eq,
    HexagonRowColumn534.product7_eq] using leftFinal5_case_3_4_checked

private theorem rightFinal5_case_3_4_row_0_0_0 : (((-1 : ℤ) ^ (rightScaleBit 5 3 4).val * positiveScale (rightScaleExponent 5 3 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 4 3 : ℤ)) • HexagonAtoms534.outerLeftABC) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (negativeScale (rightScaleExponent 5 3 4) • (rowColumnMul HexagonRowColumn534.rows_assocCAB HexagonRowColumn534.cols_right2)) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal5_case_3_4_row_0_0_1 : (((-1 : ℤ) ^ (rightScaleBit 5 3 4).val * positiveScale (rightScaleExponent 5 3 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 4 3 : ℤ)) • HexagonAtoms534.outerLeftABC) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (negativeScale (rightScaleExponent 5 3 4) • (rowColumnMul HexagonRowColumn534.rows_assocCAB HexagonRowColumn534.cols_right2)) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal5_case_3_4_row_0_0_2 : (((-1 : ℤ) ^ (rightScaleBit 5 3 4).val * positiveScale (rightScaleExponent 5 3 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 4 3 : ℤ)) • HexagonAtoms534.outerLeftABC) ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (negativeScale (rightScaleExponent 5 3 4) • (rowColumnMul HexagonRowColumn534.rows_assocCAB HexagonRowColumn534.cols_right2)) ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal5_case_3_4_row_0_0_3 : (((-1 : ℤ) ^ (rightScaleBit 5 3 4).val * positiveScale (rightScaleExponent 5 3 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 4 3 : ℤ)) • HexagonAtoms534.outerLeftABC) ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (negativeScale (rightScaleExponent 5 3 4) • (rowColumnMul HexagonRowColumn534.rows_assocCAB HexagonRowColumn534.cols_right2)) ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal5_case_3_4_row_1_0_0 : (((-1 : ℤ) ^ (rightScaleBit 5 3 4).val * positiveScale (rightScaleExponent 5 3 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 4 3 : ℤ)) • HexagonAtoms534.outerLeftABC) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (negativeScale (rightScaleExponent 5 3 4) • (rowColumnMul HexagonRowColumn534.rows_assocCAB HexagonRowColumn534.cols_right2)) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal5_case_3_4_row_1_0_1 : (((-1 : ℤ) ^ (rightScaleBit 5 3 4).val * positiveScale (rightScaleExponent 5 3 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 4 3 : ℤ)) • HexagonAtoms534.outerLeftABC) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (negativeScale (rightScaleExponent 5 3 4) • (rowColumnMul HexagonRowColumn534.rows_assocCAB HexagonRowColumn534.cols_right2)) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal5_case_3_4_row_1_0_2 : (((-1 : ℤ) ^ (rightScaleBit 5 3 4).val * positiveScale (rightScaleExponent 5 3 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 4 3 : ℤ)) • HexagonAtoms534.outerLeftABC) ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (negativeScale (rightScaleExponent 5 3 4) • (rowColumnMul HexagonRowColumn534.rows_assocCAB HexagonRowColumn534.cols_right2)) ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal5_case_3_4_row_1_0_3 : (((-1 : ℤ) ^ (rightScaleBit 5 3 4).val * positiveScale (rightScaleExponent 5 3 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 4 3 : ℤ)) • HexagonAtoms534.outerLeftABC) ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (negativeScale (rightScaleExponent 5 3 4) • (rowColumnMul HexagonRowColumn534.rows_assocCAB HexagonRowColumn534.cols_right2)) ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal5_case_3_4_row_2_0_0 : (((-1 : ℤ) ^ (rightScaleBit 5 3 4).val * positiveScale (rightScaleExponent 5 3 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 4 3 : ℤ)) • HexagonAtoms534.outerLeftABC) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (negativeScale (rightScaleExponent 5 3 4) • (rowColumnMul HexagonRowColumn534.rows_assocCAB HexagonRowColumn534.cols_right2)) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal5_case_3_4_row_2_0_1 : (((-1 : ℤ) ^ (rightScaleBit 5 3 4).val * positiveScale (rightScaleExponent 5 3 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 4 3 : ℤ)) • HexagonAtoms534.outerLeftABC) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (negativeScale (rightScaleExponent 5 3 4) • (rowColumnMul HexagonRowColumn534.rows_assocCAB HexagonRowColumn534.cols_right2)) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal5_case_3_4_row_2_0_2 : (((-1 : ℤ) ^ (rightScaleBit 5 3 4).val * positiveScale (rightScaleExponent 5 3 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 4 3 : ℤ)) • HexagonAtoms534.outerLeftABC) ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (negativeScale (rightScaleExponent 5 3 4) • (rowColumnMul HexagonRowColumn534.rows_assocCAB HexagonRowColumn534.cols_right2)) ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal5_case_3_4_row_2_0_3 : (((-1 : ℤ) ^ (rightScaleBit 5 3 4).val * positiveScale (rightScaleExponent 5 3 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 4 3 : ℤ)) • HexagonAtoms534.outerLeftABC) ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (negativeScale (rightScaleExponent 5 3 4) • (rowColumnMul HexagonRowColumn534.rows_assocCAB HexagonRowColumn534.cols_right2)) ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal5_case_3_4_row_3_0_0 : (((-1 : ℤ) ^ (rightScaleBit 5 3 4).val * positiveScale (rightScaleExponent 5 3 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 4 3 : ℤ)) • HexagonAtoms534.outerLeftABC) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (negativeScale (rightScaleExponent 5 3 4) • (rowColumnMul HexagonRowColumn534.rows_assocCAB HexagonRowColumn534.cols_right2)) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal5_case_3_4_row_3_0_1 : (((-1 : ℤ) ^ (rightScaleBit 5 3 4).val * positiveScale (rightScaleExponent 5 3 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 4 3 : ℤ)) • HexagonAtoms534.outerLeftABC) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (negativeScale (rightScaleExponent 5 3 4) • (rowColumnMul HexagonRowColumn534.rows_assocCAB HexagonRowColumn534.cols_right2)) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal5_case_3_4_row_3_0_2 : (((-1 : ℤ) ^ (rightScaleBit 5 3 4).val * positiveScale (rightScaleExponent 5 3 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 4 3 : ℤ)) • HexagonAtoms534.outerLeftABC) ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (negativeScale (rightScaleExponent 5 3 4) • (rowColumnMul HexagonRowColumn534.rows_assocCAB HexagonRowColumn534.cols_right2)) ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal5_case_3_4_row_3_0_3 : (((-1 : ℤ) ^ (rightScaleBit 5 3 4).val * positiveScale (rightScaleExponent 5 3 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 4 3 : ℤ)) • HexagonAtoms534.outerLeftABC) ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (negativeScale (rightScaleExponent 5 3 4) • (rowColumnMul HexagonRowColumn534.rows_assocCAB HexagonRowColumn534.cols_right2)) ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal5_case_3_4_row_4_0_0 : (((-1 : ℤ) ^ (rightScaleBit 5 3 4).val * positiveScale (rightScaleExponent 5 3 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 4 3 : ℤ)) • HexagonAtoms534.outerLeftABC) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (negativeScale (rightScaleExponent 5 3 4) • (rowColumnMul HexagonRowColumn534.rows_assocCAB HexagonRowColumn534.cols_right2)) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal5_case_3_4_row_4_0_1 : (((-1 : ℤ) ^ (rightScaleBit 5 3 4).val * positiveScale (rightScaleExponent 5 3 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 4 3 : ℤ)) • HexagonAtoms534.outerLeftABC) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (negativeScale (rightScaleExponent 5 3 4) • (rowColumnMul HexagonRowColumn534.rows_assocCAB HexagonRowColumn534.cols_right2)) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal5_case_3_4_row_4_0_2 : (((-1 : ℤ) ^ (rightScaleBit 5 3 4).val * positiveScale (rightScaleExponent 5 3 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 4 3 : ℤ)) • HexagonAtoms534.outerLeftABC) ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (negativeScale (rightScaleExponent 5 3 4) • (rowColumnMul HexagonRowColumn534.rows_assocCAB HexagonRowColumn534.cols_right2)) ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal5_case_3_4_row_4_0_3 : (((-1 : ℤ) ^ (rightScaleBit 5 3 4).val * positiveScale (rightScaleExponent 5 3 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 4 3 : ℤ)) • HexagonAtoms534.outerLeftABC) ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (negativeScale (rightScaleExponent 5 3 4) • (rowColumnMul HexagonRowColumn534.rows_assocCAB HexagonRowColumn534.cols_right2)) ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal5_case_3_4_row_5_0_0 : (((-1 : ℤ) ^ (rightScaleBit 5 3 4).val * positiveScale (rightScaleExponent 5 3 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 4 3 : ℤ)) • HexagonAtoms534.outerLeftABC) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (negativeScale (rightScaleExponent 5 3 4) • (rowColumnMul HexagonRowColumn534.rows_assocCAB HexagonRowColumn534.cols_right2)) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal5_case_3_4_row_5_0_1 : (((-1 : ℤ) ^ (rightScaleBit 5 3 4).val * positiveScale (rightScaleExponent 5 3 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 4 3 : ℤ)) • HexagonAtoms534.outerLeftABC) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (negativeScale (rightScaleExponent 5 3 4) • (rowColumnMul HexagonRowColumn534.rows_assocCAB HexagonRowColumn534.cols_right2)) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal5_case_3_4_row_5_0_2 : (((-1 : ℤ) ^ (rightScaleBit 5 3 4).val * positiveScale (rightScaleExponent 5 3 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 4 3 : ℤ)) • HexagonAtoms534.outerLeftABC) ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (negativeScale (rightScaleExponent 5 3 4) • (rowColumnMul HexagonRowColumn534.rows_assocCAB HexagonRowColumn534.cols_right2)) ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal5_case_3_4_row_5_0_3 : (((-1 : ℤ) ^ (rightScaleBit 5 3 4).val * positiveScale (rightScaleExponent 5 3 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 4 3 : ℤ)) • HexagonAtoms534.outerLeftABC) ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (negativeScale (rightScaleExponent 5 3 4) • (rowColumnMul HexagonRowColumn534.rows_assocCAB HexagonRowColumn534.cols_right2)) ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal5_case_3_4_row_6_0_0 : (((-1 : ℤ) ^ (rightScaleBit 5 3 4).val * positiveScale (rightScaleExponent 5 3 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 4 3 : ℤ)) • HexagonAtoms534.outerLeftABC) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (negativeScale (rightScaleExponent 5 3 4) • (rowColumnMul HexagonRowColumn534.rows_assocCAB HexagonRowColumn534.cols_right2)) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal5_case_3_4_row_6_0_1 : (((-1 : ℤ) ^ (rightScaleBit 5 3 4).val * positiveScale (rightScaleExponent 5 3 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 4 3 : ℤ)) • HexagonAtoms534.outerLeftABC) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (negativeScale (rightScaleExponent 5 3 4) • (rowColumnMul HexagonRowColumn534.rows_assocCAB HexagonRowColumn534.cols_right2)) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal5_case_3_4_row_6_0_2 : (((-1 : ℤ) ^ (rightScaleBit 5 3 4).val * positiveScale (rightScaleExponent 5 3 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 4 3 : ℤ)) • HexagonAtoms534.outerLeftABC) ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (negativeScale (rightScaleExponent 5 3 4) • (rowColumnMul HexagonRowColumn534.rows_assocCAB HexagonRowColumn534.cols_right2)) ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal5_case_3_4_row_6_0_3 : (((-1 : ℤ) ^ (rightScaleBit 5 3 4).val * positiveScale (rightScaleExponent 5 3 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 4 3 : ℤ)) • HexagonAtoms534.outerLeftABC) ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (negativeScale (rightScaleExponent 5 3 4) • (rowColumnMul HexagonRowColumn534.rows_assocCAB HexagonRowColumn534.cols_right2)) ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal5_case_3_4_row_7_0_0 : (((-1 : ℤ) ^ (rightScaleBit 5 3 4).val * positiveScale (rightScaleExponent 5 3 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 4 3 : ℤ)) • HexagonAtoms534.outerLeftABC) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (negativeScale (rightScaleExponent 5 3 4) • (rowColumnMul HexagonRowColumn534.rows_assocCAB HexagonRowColumn534.cols_right2)) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal5_case_3_4_row_7_0_1 : (((-1 : ℤ) ^ (rightScaleBit 5 3 4).val * positiveScale (rightScaleExponent 5 3 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 4 3 : ℤ)) • HexagonAtoms534.outerLeftABC) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (negativeScale (rightScaleExponent 5 3 4) • (rowColumnMul HexagonRowColumn534.rows_assocCAB HexagonRowColumn534.cols_right2)) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal5_case_3_4_row_7_0_2 : (((-1 : ℤ) ^ (rightScaleBit 5 3 4).val * positiveScale (rightScaleExponent 5 3 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 4 3 : ℤ)) • HexagonAtoms534.outerLeftABC) ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (negativeScale (rightScaleExponent 5 3 4) • (rowColumnMul HexagonRowColumn534.rows_assocCAB HexagonRowColumn534.cols_right2)) ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal5_case_3_4_row_7_0_3 : (((-1 : ℤ) ^ (rightScaleBit 5 3 4).val * positiveScale (rightScaleExponent 5 3 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 4 3 : ℤ)) • HexagonAtoms534.outerLeftABC) ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (negativeScale (rightScaleExponent 5 3 4) • (rowColumnMul HexagonRowColumn534.rows_assocCAB HexagonRowColumn534.cols_right2)) ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal5_case_3_4_checked : ((-1 : ℤ) ^ (rightScaleBit 5 3 4).val * positiveScale (rightScaleExponent 5 3 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 4 3 : ℤ)) • HexagonAtoms534.outerLeftABC = negativeScale (rightScaleExponent 5 3 4) • (rowColumnMul HexagonRowColumn534.rows_assocCAB HexagonRowColumn534.cols_right2) := by
  funext r
  fin_cases r
  · exact rightFinal5_case_3_4_row_0_0_0
  · exact rightFinal5_case_3_4_row_0_0_1
  · exact rightFinal5_case_3_4_row_0_0_2
  · exact rightFinal5_case_3_4_row_0_0_3
  · exact rightFinal5_case_3_4_row_1_0_0
  · exact rightFinal5_case_3_4_row_1_0_1
  · exact rightFinal5_case_3_4_row_1_0_2
  · exact rightFinal5_case_3_4_row_1_0_3
  · exact rightFinal5_case_3_4_row_2_0_0
  · exact rightFinal5_case_3_4_row_2_0_1
  · exact rightFinal5_case_3_4_row_2_0_2
  · exact rightFinal5_case_3_4_row_2_0_3
  · exact rightFinal5_case_3_4_row_3_0_0
  · exact rightFinal5_case_3_4_row_3_0_1
  · exact rightFinal5_case_3_4_row_3_0_2
  · exact rightFinal5_case_3_4_row_3_0_3
  · exact rightFinal5_case_3_4_row_4_0_0
  · exact rightFinal5_case_3_4_row_4_0_1
  · exact rightFinal5_case_3_4_row_4_0_2
  · exact rightFinal5_case_3_4_row_4_0_3
  · exact rightFinal5_case_3_4_row_5_0_0
  · exact rightFinal5_case_3_4_row_5_0_1
  · exact rightFinal5_case_3_4_row_5_0_2
  · exact rightFinal5_case_3_4_row_5_0_3
  · exact rightFinal5_case_3_4_row_6_0_0
  · exact rightFinal5_case_3_4_row_6_0_1
  · exact rightFinal5_case_3_4_row_6_0_2
  · exact rightFinal5_case_3_4_row_6_0_3
  · exact rightFinal5_case_3_4_row_7_0_0
  · exact rightFinal5_case_3_4_row_7_0_1
  · exact rightFinal5_case_3_4_row_7_0_2
  · exact rightFinal5_case_3_4_row_7_0_3

set_option backward.isDefEq.respectTransparency false in
theorem rightFinal5_case_3_4 : ((-1 : ℤ) ^ (rightScaleBit 5 3 4).val * positiveScale (rightScaleExponent 5 3 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 4 3 : ℤ)) • outerLeftZ 5 3 4 = negativeScale (rightScaleExponent 5 3 4) • (associatorZ 4 5 3 * right2Middle5 3 4) := by
  simpa only [HexagonAtoms534.assocABC_eq,
    HexagonAtoms534.outerABC_eq,
    HexagonAtoms534.assocBAC_eq,
    HexagonAtoms534.innerABC_eq,
    HexagonAtoms534.innerRightABC_eq,
    HexagonAtoms534.inverseACB_eq,
    HexagonAtoms534.innerACB_eq,
    HexagonAtoms534.assocBCA_eq,
    HexagonAtoms534.innerRightBAC_eq,
    HexagonAtoms534.assocCAB_eq,
    HexagonAtoms534.outerLeftABC_eq,
    HexagonRowColumn534.product0_eq,
    HexagonRowColumn534.product1_eq,
    HexagonRowColumn534.product2_eq,
    HexagonRowColumn534.product3_eq,
    HexagonRowColumn534.product4_eq,
    HexagonRowColumn534.product5_eq,
    HexagonRowColumn534.product6_eq,
    HexagonRowColumn534.product7_eq] using rightFinal5_case_3_4_checked

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonCases5
