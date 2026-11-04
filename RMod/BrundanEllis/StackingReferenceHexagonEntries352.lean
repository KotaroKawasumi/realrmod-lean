import RMod.BrundanEllis.StackingReferenceHexagonMiddle3
import RMod.BrundanEllis.StackingReferenceSparseMatrixCheck
import RMod.BrundanEllis.StackingReferenceHexagonAtoms352
import RMod.BrundanEllis.StackingReferenceHexagonRowColumn352

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

private theorem left0Middle3_eq_case_5_2_row_0_0_0 : (left0Middle3 5 2) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn352.rows_outerABC HexagonRowColumn352.cols_assocABC) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_5_2_row_0_0_1 : (left0Middle3 5 2) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn352.rows_outerABC HexagonRowColumn352.cols_assocABC) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_5_2_row_0_0_2 : (left0Middle3 5 2) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn352.rows_outerABC HexagonRowColumn352.cols_assocABC) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_5_2_row_0_0_3 : (left0Middle3 5 2) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn352.rows_outerABC HexagonRowColumn352.cols_assocABC) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_5_2_row_0_1_0 : (left0Middle3 5 2) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn352.rows_outerABC HexagonRowColumn352.cols_assocABC) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_5_2_row_0_1_1 : (left0Middle3 5 2) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn352.rows_outerABC HexagonRowColumn352.cols_assocABC) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_5_2_row_0_1_2 : (left0Middle3 5 2) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn352.rows_outerABC HexagonRowColumn352.cols_assocABC) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_5_2_row_0_1_3 : (left0Middle3 5 2) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn352.rows_outerABC HexagonRowColumn352.cols_assocABC) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_5_2_row_1_0_0 : (left0Middle3 5 2) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn352.rows_outerABC HexagonRowColumn352.cols_assocABC) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_5_2_row_1_0_1 : (left0Middle3 5 2) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn352.rows_outerABC HexagonRowColumn352.cols_assocABC) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_5_2_row_1_0_2 : (left0Middle3 5 2) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn352.rows_outerABC HexagonRowColumn352.cols_assocABC) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_5_2_row_1_0_3 : (left0Middle3 5 2) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn352.rows_outerABC HexagonRowColumn352.cols_assocABC) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_5_2_row_1_1_0 : (left0Middle3 5 2) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn352.rows_outerABC HexagonRowColumn352.cols_assocABC) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_5_2_row_1_1_1 : (left0Middle3 5 2) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn352.rows_outerABC HexagonRowColumn352.cols_assocABC) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_5_2_row_1_1_2 : (left0Middle3 5 2) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn352.rows_outerABC HexagonRowColumn352.cols_assocABC) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_5_2_row_1_1_3 : (left0Middle3 5 2) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn352.rows_outerABC HexagonRowColumn352.cols_assocABC) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_5_2_row_2_0_0 : (left0Middle3 5 2) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn352.rows_outerABC HexagonRowColumn352.cols_assocABC) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_5_2_row_2_0_1 : (left0Middle3 5 2) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn352.rows_outerABC HexagonRowColumn352.cols_assocABC) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_5_2_row_2_0_2 : (left0Middle3 5 2) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn352.rows_outerABC HexagonRowColumn352.cols_assocABC) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_5_2_row_2_0_3 : (left0Middle3 5 2) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn352.rows_outerABC HexagonRowColumn352.cols_assocABC) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_5_2_row_2_1_0 : (left0Middle3 5 2) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn352.rows_outerABC HexagonRowColumn352.cols_assocABC) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_5_2_row_2_1_1 : (left0Middle3 5 2) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn352.rows_outerABC HexagonRowColumn352.cols_assocABC) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_5_2_row_2_1_2 : (left0Middle3 5 2) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn352.rows_outerABC HexagonRowColumn352.cols_assocABC) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_5_2_row_2_1_3 : (left0Middle3 5 2) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn352.rows_outerABC HexagonRowColumn352.cols_assocABC) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_5_2_row_3_0_0 : (left0Middle3 5 2) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn352.rows_outerABC HexagonRowColumn352.cols_assocABC) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_5_2_row_3_0_1 : (left0Middle3 5 2) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn352.rows_outerABC HexagonRowColumn352.cols_assocABC) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_5_2_row_3_0_2 : (left0Middle3 5 2) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn352.rows_outerABC HexagonRowColumn352.cols_assocABC) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_5_2_row_3_0_3 : (left0Middle3 5 2) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn352.rows_outerABC HexagonRowColumn352.cols_assocABC) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_5_2_row_3_1_0 : (left0Middle3 5 2) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn352.rows_outerABC HexagonRowColumn352.cols_assocABC) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_5_2_row_3_1_1 : (left0Middle3 5 2) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn352.rows_outerABC HexagonRowColumn352.cols_assocABC) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_5_2_row_3_1_2 : (left0Middle3 5 2) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn352.rows_outerABC HexagonRowColumn352.cols_assocABC) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_5_2_row_3_1_3 : (left0Middle3 5 2) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn352.rows_outerABC HexagonRowColumn352.cols_assocABC) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_5_2_checked : left0Middle3 5 2 = rowColumnMul HexagonRowColumn352.rows_outerABC HexagonRowColumn352.cols_assocABC := by
  funext r
  fin_cases r
  · exact left0Middle3_eq_case_5_2_row_0_0_0
  · exact left0Middle3_eq_case_5_2_row_0_0_1
  · exact left0Middle3_eq_case_5_2_row_0_0_2
  · exact left0Middle3_eq_case_5_2_row_0_0_3
  · exact left0Middle3_eq_case_5_2_row_0_1_0
  · exact left0Middle3_eq_case_5_2_row_0_1_1
  · exact left0Middle3_eq_case_5_2_row_0_1_2
  · exact left0Middle3_eq_case_5_2_row_0_1_3
  · exact left0Middle3_eq_case_5_2_row_1_0_0
  · exact left0Middle3_eq_case_5_2_row_1_0_1
  · exact left0Middle3_eq_case_5_2_row_1_0_2
  · exact left0Middle3_eq_case_5_2_row_1_0_3
  · exact left0Middle3_eq_case_5_2_row_1_1_0
  · exact left0Middle3_eq_case_5_2_row_1_1_1
  · exact left0Middle3_eq_case_5_2_row_1_1_2
  · exact left0Middle3_eq_case_5_2_row_1_1_3
  · exact left0Middle3_eq_case_5_2_row_2_0_0
  · exact left0Middle3_eq_case_5_2_row_2_0_1
  · exact left0Middle3_eq_case_5_2_row_2_0_2
  · exact left0Middle3_eq_case_5_2_row_2_0_3
  · exact left0Middle3_eq_case_5_2_row_2_1_0
  · exact left0Middle3_eq_case_5_2_row_2_1_1
  · exact left0Middle3_eq_case_5_2_row_2_1_2
  · exact left0Middle3_eq_case_5_2_row_2_1_3
  · exact left0Middle3_eq_case_5_2_row_3_0_0
  · exact left0Middle3_eq_case_5_2_row_3_0_1
  · exact left0Middle3_eq_case_5_2_row_3_0_2
  · exact left0Middle3_eq_case_5_2_row_3_0_3
  · exact left0Middle3_eq_case_5_2_row_3_1_0
  · exact left0Middle3_eq_case_5_2_row_3_1_1
  · exact left0Middle3_eq_case_5_2_row_3_1_2
  · exact left0Middle3_eq_case_5_2_row_3_1_3

set_option backward.isDefEq.respectTransparency false in
theorem left0Middle3_eq_case_5_2 : left0Middle3 5 2 = outerRightZ 3 5 2 * associatorZ 3 5 2 := by
  simpa only [HexagonAtoms352.assocABC_eq,
    HexagonAtoms352.outerABC_eq,
    HexagonAtoms352.assocBAC_eq,
    HexagonAtoms352.innerABC_eq,
    HexagonAtoms352.innerRightABC_eq,
    HexagonAtoms352.inverseACB_eq,
    HexagonAtoms352.innerACB_eq,
    HexagonAtoms352.assocBCA_eq,
    HexagonAtoms352.innerRightBAC_eq,
    HexagonAtoms352.assocCAB_eq,
    HexagonAtoms352.outerLeftABC_eq,
    HexagonRowColumn352.product0_eq,
    HexagonRowColumn352.product1_eq,
    HexagonRowColumn352.product2_eq,
    HexagonRowColumn352.product3_eq,
    HexagonRowColumn352.product4_eq,
    HexagonRowColumn352.product5_eq,
    HexagonRowColumn352.product6_eq,
    HexagonRowColumn352.product7_eq] using left0Middle3_eq_case_5_2_checked

private theorem left1Middle3_eq_case_5_2_row_0_0_0 : (left1Middle3 5 2) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 4)) = (HexagonAtoms352.assocBAC) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_5_2_row_0_0_1 : (left1Middle3 5 2) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 4)) = (HexagonAtoms352.assocBAC) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_5_2_row_0_0_2 : (left1Middle3 5 2) ((0 : Fin 2), (0 : Fin 4), (2 : Fin 4)) = (HexagonAtoms352.assocBAC) ((0 : Fin 2), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_5_2_row_0_0_3 : (left1Middle3 5 2) ((0 : Fin 2), (0 : Fin 4), (3 : Fin 4)) = (HexagonAtoms352.assocBAC) ((0 : Fin 2), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_5_2_row_0_1_0 : (left1Middle3 5 2) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 4)) = (HexagonAtoms352.assocBAC) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_5_2_row_0_1_1 : (left1Middle3 5 2) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 4)) = (HexagonAtoms352.assocBAC) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_5_2_row_0_1_2 : (left1Middle3 5 2) ((0 : Fin 2), (1 : Fin 4), (2 : Fin 4)) = (HexagonAtoms352.assocBAC) ((0 : Fin 2), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_5_2_row_0_1_3 : (left1Middle3 5 2) ((0 : Fin 2), (1 : Fin 4), (3 : Fin 4)) = (HexagonAtoms352.assocBAC) ((0 : Fin 2), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_5_2_row_0_2_0 : (left1Middle3 5 2) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 4)) = (HexagonAtoms352.assocBAC) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_5_2_row_0_2_1 : (left1Middle3 5 2) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 4)) = (HexagonAtoms352.assocBAC) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_5_2_row_0_2_2 : (left1Middle3 5 2) ((0 : Fin 2), (2 : Fin 4), (2 : Fin 4)) = (HexagonAtoms352.assocBAC) ((0 : Fin 2), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_5_2_row_0_2_3 : (left1Middle3 5 2) ((0 : Fin 2), (2 : Fin 4), (3 : Fin 4)) = (HexagonAtoms352.assocBAC) ((0 : Fin 2), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_5_2_row_0_3_0 : (left1Middle3 5 2) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 4)) = (HexagonAtoms352.assocBAC) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_5_2_row_0_3_1 : (left1Middle3 5 2) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 4)) = (HexagonAtoms352.assocBAC) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_5_2_row_0_3_2 : (left1Middle3 5 2) ((0 : Fin 2), (3 : Fin 4), (2 : Fin 4)) = (HexagonAtoms352.assocBAC) ((0 : Fin 2), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_5_2_row_0_3_3 : (left1Middle3 5 2) ((0 : Fin 2), (3 : Fin 4), (3 : Fin 4)) = (HexagonAtoms352.assocBAC) ((0 : Fin 2), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_5_2_row_1_0_0 : (left1Middle3 5 2) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 4)) = (HexagonAtoms352.assocBAC) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_5_2_row_1_0_1 : (left1Middle3 5 2) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 4)) = (HexagonAtoms352.assocBAC) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_5_2_row_1_0_2 : (left1Middle3 5 2) ((1 : Fin 2), (0 : Fin 4), (2 : Fin 4)) = (HexagonAtoms352.assocBAC) ((1 : Fin 2), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_5_2_row_1_0_3 : (left1Middle3 5 2) ((1 : Fin 2), (0 : Fin 4), (3 : Fin 4)) = (HexagonAtoms352.assocBAC) ((1 : Fin 2), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_5_2_row_1_1_0 : (left1Middle3 5 2) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 4)) = (HexagonAtoms352.assocBAC) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_5_2_row_1_1_1 : (left1Middle3 5 2) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 4)) = (HexagonAtoms352.assocBAC) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_5_2_row_1_1_2 : (left1Middle3 5 2) ((1 : Fin 2), (1 : Fin 4), (2 : Fin 4)) = (HexagonAtoms352.assocBAC) ((1 : Fin 2), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_5_2_row_1_1_3 : (left1Middle3 5 2) ((1 : Fin 2), (1 : Fin 4), (3 : Fin 4)) = (HexagonAtoms352.assocBAC) ((1 : Fin 2), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_5_2_row_1_2_0 : (left1Middle3 5 2) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 4)) = (HexagonAtoms352.assocBAC) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_5_2_row_1_2_1 : (left1Middle3 5 2) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 4)) = (HexagonAtoms352.assocBAC) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_5_2_row_1_2_2 : (left1Middle3 5 2) ((1 : Fin 2), (2 : Fin 4), (2 : Fin 4)) = (HexagonAtoms352.assocBAC) ((1 : Fin 2), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_5_2_row_1_2_3 : (left1Middle3 5 2) ((1 : Fin 2), (2 : Fin 4), (3 : Fin 4)) = (HexagonAtoms352.assocBAC) ((1 : Fin 2), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_5_2_row_1_3_0 : (left1Middle3 5 2) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 4)) = (HexagonAtoms352.assocBAC) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_5_2_row_1_3_1 : (left1Middle3 5 2) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 4)) = (HexagonAtoms352.assocBAC) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_5_2_row_1_3_2 : (left1Middle3 5 2) ((1 : Fin 2), (3 : Fin 4), (2 : Fin 4)) = (HexagonAtoms352.assocBAC) ((1 : Fin 2), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_5_2_row_1_3_3 : (left1Middle3 5 2) ((1 : Fin 2), (3 : Fin 4), (3 : Fin 4)) = (HexagonAtoms352.assocBAC) ((1 : Fin 2), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_5_2_checked : left1Middle3 5 2 = HexagonAtoms352.assocBAC := by
  funext r
  fin_cases r
  · exact left1Middle3_eq_case_5_2_row_0_0_0
  · exact left1Middle3_eq_case_5_2_row_0_0_1
  · exact left1Middle3_eq_case_5_2_row_0_0_2
  · exact left1Middle3_eq_case_5_2_row_0_0_3
  · exact left1Middle3_eq_case_5_2_row_0_1_0
  · exact left1Middle3_eq_case_5_2_row_0_1_1
  · exact left1Middle3_eq_case_5_2_row_0_1_2
  · exact left1Middle3_eq_case_5_2_row_0_1_3
  · exact left1Middle3_eq_case_5_2_row_0_2_0
  · exact left1Middle3_eq_case_5_2_row_0_2_1
  · exact left1Middle3_eq_case_5_2_row_0_2_2
  · exact left1Middle3_eq_case_5_2_row_0_2_3
  · exact left1Middle3_eq_case_5_2_row_0_3_0
  · exact left1Middle3_eq_case_5_2_row_0_3_1
  · exact left1Middle3_eq_case_5_2_row_0_3_2
  · exact left1Middle3_eq_case_5_2_row_0_3_3
  · exact left1Middle3_eq_case_5_2_row_1_0_0
  · exact left1Middle3_eq_case_5_2_row_1_0_1
  · exact left1Middle3_eq_case_5_2_row_1_0_2
  · exact left1Middle3_eq_case_5_2_row_1_0_3
  · exact left1Middle3_eq_case_5_2_row_1_1_0
  · exact left1Middle3_eq_case_5_2_row_1_1_1
  · exact left1Middle3_eq_case_5_2_row_1_1_2
  · exact left1Middle3_eq_case_5_2_row_1_1_3
  · exact left1Middle3_eq_case_5_2_row_1_2_0
  · exact left1Middle3_eq_case_5_2_row_1_2_1
  · exact left1Middle3_eq_case_5_2_row_1_2_2
  · exact left1Middle3_eq_case_5_2_row_1_2_3
  · exact left1Middle3_eq_case_5_2_row_1_3_0
  · exact left1Middle3_eq_case_5_2_row_1_3_1
  · exact left1Middle3_eq_case_5_2_row_1_3_2
  · exact left1Middle3_eq_case_5_2_row_1_3_3

set_option backward.isDefEq.respectTransparency false in
theorem left1Middle3_eq_case_5_2 : left1Middle3 5 2 = associatorZ 5 3 2 * innerLeftZ 3 5 2 := by
  simpa only [HexagonAtoms352.assocABC_eq,
    HexagonAtoms352.outerABC_eq,
    HexagonAtoms352.assocBAC_eq,
    HexagonAtoms352.innerABC_eq,
    HexagonAtoms352.innerRightABC_eq,
    HexagonAtoms352.inverseACB_eq,
    HexagonAtoms352.innerACB_eq,
    HexagonAtoms352.assocBCA_eq,
    HexagonAtoms352.innerRightBAC_eq,
    HexagonAtoms352.assocCAB_eq,
    HexagonAtoms352.outerLeftABC_eq,
    HexagonRowColumn352.product0_eq,
    HexagonRowColumn352.product1_eq,
    HexagonRowColumn352.product2_eq,
    HexagonRowColumn352.product3_eq,
    HexagonRowColumn352.product4_eq,
    HexagonRowColumn352.product5_eq,
    HexagonRowColumn352.product6_eq,
    HexagonRowColumn352.product7_eq] using left1Middle3_eq_case_5_2_checked

private theorem right0Middle3_eq_case_5_2_row_0_0_0 : (right0Middle3 5 2) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms352.assocABC) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_5_2_row_0_0_1 : (right0Middle3 5 2) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms352.assocABC) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_5_2_row_0_0_2 : (right0Middle3 5 2) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms352.assocABC) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_5_2_row_0_0_3 : (right0Middle3 5 2) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms352.assocABC) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_5_2_row_0_1_0 : (right0Middle3 5 2) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms352.assocABC) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_5_2_row_0_1_1 : (right0Middle3 5 2) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms352.assocABC) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_5_2_row_0_1_2 : (right0Middle3 5 2) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms352.assocABC) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_5_2_row_0_1_3 : (right0Middle3 5 2) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms352.assocABC) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_5_2_row_1_0_0 : (right0Middle3 5 2) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms352.assocABC) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_5_2_row_1_0_1 : (right0Middle3 5 2) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms352.assocABC) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_5_2_row_1_0_2 : (right0Middle3 5 2) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms352.assocABC) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_5_2_row_1_0_3 : (right0Middle3 5 2) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms352.assocABC) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_5_2_row_1_1_0 : (right0Middle3 5 2) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms352.assocABC) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_5_2_row_1_1_1 : (right0Middle3 5 2) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms352.assocABC) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_5_2_row_1_1_2 : (right0Middle3 5 2) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms352.assocABC) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_5_2_row_1_1_3 : (right0Middle3 5 2) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms352.assocABC) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_5_2_row_2_0_0 : (right0Middle3 5 2) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms352.assocABC) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_5_2_row_2_0_1 : (right0Middle3 5 2) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms352.assocABC) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_5_2_row_2_0_2 : (right0Middle3 5 2) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms352.assocABC) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_5_2_row_2_0_3 : (right0Middle3 5 2) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms352.assocABC) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_5_2_row_2_1_0 : (right0Middle3 5 2) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms352.assocABC) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_5_2_row_2_1_1 : (right0Middle3 5 2) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms352.assocABC) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_5_2_row_2_1_2 : (right0Middle3 5 2) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms352.assocABC) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_5_2_row_2_1_3 : (right0Middle3 5 2) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms352.assocABC) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_5_2_row_3_0_0 : (right0Middle3 5 2) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms352.assocABC) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_5_2_row_3_0_1 : (right0Middle3 5 2) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms352.assocABC) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_5_2_row_3_0_2 : (right0Middle3 5 2) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms352.assocABC) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_5_2_row_3_0_3 : (right0Middle3 5 2) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms352.assocABC) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_5_2_row_3_1_0 : (right0Middle3 5 2) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms352.assocABC) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_5_2_row_3_1_1 : (right0Middle3 5 2) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms352.assocABC) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_5_2_row_3_1_2 : (right0Middle3 5 2) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms352.assocABC) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_5_2_row_3_1_3 : (right0Middle3 5 2) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms352.assocABC) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_5_2_checked : right0Middle3 5 2 = HexagonAtoms352.assocABC := by
  funext r
  fin_cases r
  · exact right0Middle3_eq_case_5_2_row_0_0_0
  · exact right0Middle3_eq_case_5_2_row_0_0_1
  · exact right0Middle3_eq_case_5_2_row_0_0_2
  · exact right0Middle3_eq_case_5_2_row_0_0_3
  · exact right0Middle3_eq_case_5_2_row_0_1_0
  · exact right0Middle3_eq_case_5_2_row_0_1_1
  · exact right0Middle3_eq_case_5_2_row_0_1_2
  · exact right0Middle3_eq_case_5_2_row_0_1_3
  · exact right0Middle3_eq_case_5_2_row_1_0_0
  · exact right0Middle3_eq_case_5_2_row_1_0_1
  · exact right0Middle3_eq_case_5_2_row_1_0_2
  · exact right0Middle3_eq_case_5_2_row_1_0_3
  · exact right0Middle3_eq_case_5_2_row_1_1_0
  · exact right0Middle3_eq_case_5_2_row_1_1_1
  · exact right0Middle3_eq_case_5_2_row_1_1_2
  · exact right0Middle3_eq_case_5_2_row_1_1_3
  · exact right0Middle3_eq_case_5_2_row_2_0_0
  · exact right0Middle3_eq_case_5_2_row_2_0_1
  · exact right0Middle3_eq_case_5_2_row_2_0_2
  · exact right0Middle3_eq_case_5_2_row_2_0_3
  · exact right0Middle3_eq_case_5_2_row_2_1_0
  · exact right0Middle3_eq_case_5_2_row_2_1_1
  · exact right0Middle3_eq_case_5_2_row_2_1_2
  · exact right0Middle3_eq_case_5_2_row_2_1_3
  · exact right0Middle3_eq_case_5_2_row_3_0_0
  · exact right0Middle3_eq_case_5_2_row_3_0_1
  · exact right0Middle3_eq_case_5_2_row_3_0_2
  · exact right0Middle3_eq_case_5_2_row_3_0_3
  · exact right0Middle3_eq_case_5_2_row_3_1_0
  · exact right0Middle3_eq_case_5_2_row_3_1_1
  · exact right0Middle3_eq_case_5_2_row_3_1_2
  · exact right0Middle3_eq_case_5_2_row_3_1_3

set_option backward.isDefEq.respectTransparency false in
theorem right0Middle3_eq_case_5_2 : right0Middle3 5 2 = innerRightZ 3 5 2 * associatorZ 3 5 2 := by
  simpa only [HexagonAtoms352.assocABC_eq,
    HexagonAtoms352.outerABC_eq,
    HexagonAtoms352.assocBAC_eq,
    HexagonAtoms352.innerABC_eq,
    HexagonAtoms352.innerRightABC_eq,
    HexagonAtoms352.inverseACB_eq,
    HexagonAtoms352.innerACB_eq,
    HexagonAtoms352.assocBCA_eq,
    HexagonAtoms352.innerRightBAC_eq,
    HexagonAtoms352.assocCAB_eq,
    HexagonAtoms352.outerLeftABC_eq,
    HexagonRowColumn352.product0_eq,
    HexagonRowColumn352.product1_eq,
    HexagonRowColumn352.product2_eq,
    HexagonRowColumn352.product3_eq,
    HexagonRowColumn352.product4_eq,
    HexagonRowColumn352.product5_eq,
    HexagonRowColumn352.product6_eq,
    HexagonRowColumn352.product7_eq] using right0Middle3_eq_case_5_2_checked

private theorem right1Middle3_eq_case_5_2_row_0_0_0 : (right1Middle3 5 2) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn352.rows_inverseACB HexagonRowColumn352.cols_right0) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_5_2_row_0_0_1 : (right1Middle3 5 2) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn352.rows_inverseACB HexagonRowColumn352.cols_right0) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_5_2_row_0_0_2 : (right1Middle3 5 2) ((0 : Fin 2), (0 : Fin 4), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn352.rows_inverseACB HexagonRowColumn352.cols_right0) ((0 : Fin 2), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_5_2_row_0_0_3 : (right1Middle3 5 2) ((0 : Fin 2), (0 : Fin 4), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn352.rows_inverseACB HexagonRowColumn352.cols_right0) ((0 : Fin 2), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_5_2_row_0_1_0 : (right1Middle3 5 2) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn352.rows_inverseACB HexagonRowColumn352.cols_right0) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_5_2_row_0_1_1 : (right1Middle3 5 2) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn352.rows_inverseACB HexagonRowColumn352.cols_right0) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_5_2_row_0_1_2 : (right1Middle3 5 2) ((0 : Fin 2), (1 : Fin 4), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn352.rows_inverseACB HexagonRowColumn352.cols_right0) ((0 : Fin 2), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_5_2_row_0_1_3 : (right1Middle3 5 2) ((0 : Fin 2), (1 : Fin 4), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn352.rows_inverseACB HexagonRowColumn352.cols_right0) ((0 : Fin 2), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_5_2_row_0_2_0 : (right1Middle3 5 2) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn352.rows_inverseACB HexagonRowColumn352.cols_right0) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_5_2_row_0_2_1 : (right1Middle3 5 2) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn352.rows_inverseACB HexagonRowColumn352.cols_right0) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_5_2_row_0_2_2 : (right1Middle3 5 2) ((0 : Fin 2), (2 : Fin 4), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn352.rows_inverseACB HexagonRowColumn352.cols_right0) ((0 : Fin 2), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_5_2_row_0_2_3 : (right1Middle3 5 2) ((0 : Fin 2), (2 : Fin 4), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn352.rows_inverseACB HexagonRowColumn352.cols_right0) ((0 : Fin 2), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_5_2_row_0_3_0 : (right1Middle3 5 2) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn352.rows_inverseACB HexagonRowColumn352.cols_right0) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_5_2_row_0_3_1 : (right1Middle3 5 2) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn352.rows_inverseACB HexagonRowColumn352.cols_right0) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_5_2_row_0_3_2 : (right1Middle3 5 2) ((0 : Fin 2), (3 : Fin 4), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn352.rows_inverseACB HexagonRowColumn352.cols_right0) ((0 : Fin 2), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_5_2_row_0_3_3 : (right1Middle3 5 2) ((0 : Fin 2), (3 : Fin 4), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn352.rows_inverseACB HexagonRowColumn352.cols_right0) ((0 : Fin 2), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_5_2_row_1_0_0 : (right1Middle3 5 2) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn352.rows_inverseACB HexagonRowColumn352.cols_right0) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_5_2_row_1_0_1 : (right1Middle3 5 2) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn352.rows_inverseACB HexagonRowColumn352.cols_right0) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_5_2_row_1_0_2 : (right1Middle3 5 2) ((1 : Fin 2), (0 : Fin 4), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn352.rows_inverseACB HexagonRowColumn352.cols_right0) ((1 : Fin 2), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_5_2_row_1_0_3 : (right1Middle3 5 2) ((1 : Fin 2), (0 : Fin 4), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn352.rows_inverseACB HexagonRowColumn352.cols_right0) ((1 : Fin 2), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_5_2_row_1_1_0 : (right1Middle3 5 2) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn352.rows_inverseACB HexagonRowColumn352.cols_right0) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_5_2_row_1_1_1 : (right1Middle3 5 2) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn352.rows_inverseACB HexagonRowColumn352.cols_right0) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_5_2_row_1_1_2 : (right1Middle3 5 2) ((1 : Fin 2), (1 : Fin 4), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn352.rows_inverseACB HexagonRowColumn352.cols_right0) ((1 : Fin 2), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_5_2_row_1_1_3 : (right1Middle3 5 2) ((1 : Fin 2), (1 : Fin 4), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn352.rows_inverseACB HexagonRowColumn352.cols_right0) ((1 : Fin 2), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_5_2_row_1_2_0 : (right1Middle3 5 2) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn352.rows_inverseACB HexagonRowColumn352.cols_right0) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_5_2_row_1_2_1 : (right1Middle3 5 2) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn352.rows_inverseACB HexagonRowColumn352.cols_right0) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_5_2_row_1_2_2 : (right1Middle3 5 2) ((1 : Fin 2), (2 : Fin 4), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn352.rows_inverseACB HexagonRowColumn352.cols_right0) ((1 : Fin 2), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_5_2_row_1_2_3 : (right1Middle3 5 2) ((1 : Fin 2), (2 : Fin 4), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn352.rows_inverseACB HexagonRowColumn352.cols_right0) ((1 : Fin 2), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_5_2_row_1_3_0 : (right1Middle3 5 2) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn352.rows_inverseACB HexagonRowColumn352.cols_right0) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_5_2_row_1_3_1 : (right1Middle3 5 2) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn352.rows_inverseACB HexagonRowColumn352.cols_right0) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_5_2_row_1_3_2 : (right1Middle3 5 2) ((1 : Fin 2), (3 : Fin 4), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn352.rows_inverseACB HexagonRowColumn352.cols_right0) ((1 : Fin 2), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_5_2_row_1_3_3 : (right1Middle3 5 2) ((1 : Fin 2), (3 : Fin 4), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn352.rows_inverseACB HexagonRowColumn352.cols_right0) ((1 : Fin 2), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_5_2_checked : right1Middle3 5 2 = rowColumnMul HexagonRowColumn352.rows_inverseACB HexagonRowColumn352.cols_right0 := by
  funext r
  fin_cases r
  · exact right1Middle3_eq_case_5_2_row_0_0_0
  · exact right1Middle3_eq_case_5_2_row_0_0_1
  · exact right1Middle3_eq_case_5_2_row_0_0_2
  · exact right1Middle3_eq_case_5_2_row_0_0_3
  · exact right1Middle3_eq_case_5_2_row_0_1_0
  · exact right1Middle3_eq_case_5_2_row_0_1_1
  · exact right1Middle3_eq_case_5_2_row_0_1_2
  · exact right1Middle3_eq_case_5_2_row_0_1_3
  · exact right1Middle3_eq_case_5_2_row_0_2_0
  · exact right1Middle3_eq_case_5_2_row_0_2_1
  · exact right1Middle3_eq_case_5_2_row_0_2_2
  · exact right1Middle3_eq_case_5_2_row_0_2_3
  · exact right1Middle3_eq_case_5_2_row_0_3_0
  · exact right1Middle3_eq_case_5_2_row_0_3_1
  · exact right1Middle3_eq_case_5_2_row_0_3_2
  · exact right1Middle3_eq_case_5_2_row_0_3_3
  · exact right1Middle3_eq_case_5_2_row_1_0_0
  · exact right1Middle3_eq_case_5_2_row_1_0_1
  · exact right1Middle3_eq_case_5_2_row_1_0_2
  · exact right1Middle3_eq_case_5_2_row_1_0_3
  · exact right1Middle3_eq_case_5_2_row_1_1_0
  · exact right1Middle3_eq_case_5_2_row_1_1_1
  · exact right1Middle3_eq_case_5_2_row_1_1_2
  · exact right1Middle3_eq_case_5_2_row_1_1_3
  · exact right1Middle3_eq_case_5_2_row_1_2_0
  · exact right1Middle3_eq_case_5_2_row_1_2_1
  · exact right1Middle3_eq_case_5_2_row_1_2_2
  · exact right1Middle3_eq_case_5_2_row_1_2_3
  · exact right1Middle3_eq_case_5_2_row_1_3_0
  · exact right1Middle3_eq_case_5_2_row_1_3_1
  · exact right1Middle3_eq_case_5_2_row_1_3_2
  · exact right1Middle3_eq_case_5_2_row_1_3_3

set_option backward.isDefEq.respectTransparency false in
theorem right1Middle3_eq_case_5_2 : right1Middle3 5 2 = associatorInverseZ 3 2 5 * right0Middle3 5 2 := by
  simpa only [HexagonAtoms352.assocABC_eq,
    HexagonAtoms352.outerABC_eq,
    HexagonAtoms352.assocBAC_eq,
    HexagonAtoms352.innerABC_eq,
    HexagonAtoms352.innerRightABC_eq,
    HexagonAtoms352.inverseACB_eq,
    HexagonAtoms352.innerACB_eq,
    HexagonAtoms352.assocBCA_eq,
    HexagonAtoms352.innerRightBAC_eq,
    HexagonAtoms352.assocCAB_eq,
    HexagonAtoms352.outerLeftABC_eq,
    HexagonRowColumn352.product0_eq,
    HexagonRowColumn352.product1_eq,
    HexagonRowColumn352.product2_eq,
    HexagonRowColumn352.product3_eq,
    HexagonRowColumn352.product4_eq,
    HexagonRowColumn352.product5_eq,
    HexagonRowColumn352.product6_eq,
    HexagonRowColumn352.product7_eq] using right1Middle3_eq_case_5_2_checked

private theorem right2Middle3_eq_case_5_2_row_0_0_0 : (right2Middle3 5 2) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 4)) = (right1Middle3 5 2) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_5_2_row_0_0_1 : (right2Middle3 5 2) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 4)) = (right1Middle3 5 2) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_5_2_row_0_0_2 : (right2Middle3 5 2) ((0 : Fin 2), (0 : Fin 4), (2 : Fin 4)) = (right1Middle3 5 2) ((0 : Fin 2), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_5_2_row_0_0_3 : (right2Middle3 5 2) ((0 : Fin 2), (0 : Fin 4), (3 : Fin 4)) = (right1Middle3 5 2) ((0 : Fin 2), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_5_2_row_0_1_0 : (right2Middle3 5 2) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 4)) = (right1Middle3 5 2) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_5_2_row_0_1_1 : (right2Middle3 5 2) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 4)) = (right1Middle3 5 2) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_5_2_row_0_1_2 : (right2Middle3 5 2) ((0 : Fin 2), (1 : Fin 4), (2 : Fin 4)) = (right1Middle3 5 2) ((0 : Fin 2), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_5_2_row_0_1_3 : (right2Middle3 5 2) ((0 : Fin 2), (1 : Fin 4), (3 : Fin 4)) = (right1Middle3 5 2) ((0 : Fin 2), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_5_2_row_0_2_0 : (right2Middle3 5 2) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 4)) = (right1Middle3 5 2) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_5_2_row_0_2_1 : (right2Middle3 5 2) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 4)) = (right1Middle3 5 2) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_5_2_row_0_2_2 : (right2Middle3 5 2) ((0 : Fin 2), (2 : Fin 4), (2 : Fin 4)) = (right1Middle3 5 2) ((0 : Fin 2), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_5_2_row_0_2_3 : (right2Middle3 5 2) ((0 : Fin 2), (2 : Fin 4), (3 : Fin 4)) = (right1Middle3 5 2) ((0 : Fin 2), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_5_2_row_0_3_0 : (right2Middle3 5 2) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 4)) = (right1Middle3 5 2) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_5_2_row_0_3_1 : (right2Middle3 5 2) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 4)) = (right1Middle3 5 2) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_5_2_row_0_3_2 : (right2Middle3 5 2) ((0 : Fin 2), (3 : Fin 4), (2 : Fin 4)) = (right1Middle3 5 2) ((0 : Fin 2), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_5_2_row_0_3_3 : (right2Middle3 5 2) ((0 : Fin 2), (3 : Fin 4), (3 : Fin 4)) = (right1Middle3 5 2) ((0 : Fin 2), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_5_2_row_1_0_0 : (right2Middle3 5 2) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 4)) = (right1Middle3 5 2) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_5_2_row_1_0_1 : (right2Middle3 5 2) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 4)) = (right1Middle3 5 2) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_5_2_row_1_0_2 : (right2Middle3 5 2) ((1 : Fin 2), (0 : Fin 4), (2 : Fin 4)) = (right1Middle3 5 2) ((1 : Fin 2), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_5_2_row_1_0_3 : (right2Middle3 5 2) ((1 : Fin 2), (0 : Fin 4), (3 : Fin 4)) = (right1Middle3 5 2) ((1 : Fin 2), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_5_2_row_1_1_0 : (right2Middle3 5 2) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 4)) = (right1Middle3 5 2) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_5_2_row_1_1_1 : (right2Middle3 5 2) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 4)) = (right1Middle3 5 2) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_5_2_row_1_1_2 : (right2Middle3 5 2) ((1 : Fin 2), (1 : Fin 4), (2 : Fin 4)) = (right1Middle3 5 2) ((1 : Fin 2), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_5_2_row_1_1_3 : (right2Middle3 5 2) ((1 : Fin 2), (1 : Fin 4), (3 : Fin 4)) = (right1Middle3 5 2) ((1 : Fin 2), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_5_2_row_1_2_0 : (right2Middle3 5 2) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 4)) = (right1Middle3 5 2) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_5_2_row_1_2_1 : (right2Middle3 5 2) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 4)) = (right1Middle3 5 2) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_5_2_row_1_2_2 : (right2Middle3 5 2) ((1 : Fin 2), (2 : Fin 4), (2 : Fin 4)) = (right1Middle3 5 2) ((1 : Fin 2), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_5_2_row_1_2_3 : (right2Middle3 5 2) ((1 : Fin 2), (2 : Fin 4), (3 : Fin 4)) = (right1Middle3 5 2) ((1 : Fin 2), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_5_2_row_1_3_0 : (right2Middle3 5 2) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 4)) = (right1Middle3 5 2) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_5_2_row_1_3_1 : (right2Middle3 5 2) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 4)) = (right1Middle3 5 2) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_5_2_row_1_3_2 : (right2Middle3 5 2) ((1 : Fin 2), (3 : Fin 4), (2 : Fin 4)) = (right1Middle3 5 2) ((1 : Fin 2), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_5_2_row_1_3_3 : (right2Middle3 5 2) ((1 : Fin 2), (3 : Fin 4), (3 : Fin 4)) = (right1Middle3 5 2) ((1 : Fin 2), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_5_2_checked : right2Middle3 5 2 = right1Middle3 5 2 := by
  funext r
  fin_cases r
  · exact right2Middle3_eq_case_5_2_row_0_0_0
  · exact right2Middle3_eq_case_5_2_row_0_0_1
  · exact right2Middle3_eq_case_5_2_row_0_0_2
  · exact right2Middle3_eq_case_5_2_row_0_0_3
  · exact right2Middle3_eq_case_5_2_row_0_1_0
  · exact right2Middle3_eq_case_5_2_row_0_1_1
  · exact right2Middle3_eq_case_5_2_row_0_1_2
  · exact right2Middle3_eq_case_5_2_row_0_1_3
  · exact right2Middle3_eq_case_5_2_row_0_2_0
  · exact right2Middle3_eq_case_5_2_row_0_2_1
  · exact right2Middle3_eq_case_5_2_row_0_2_2
  · exact right2Middle3_eq_case_5_2_row_0_2_3
  · exact right2Middle3_eq_case_5_2_row_0_3_0
  · exact right2Middle3_eq_case_5_2_row_0_3_1
  · exact right2Middle3_eq_case_5_2_row_0_3_2
  · exact right2Middle3_eq_case_5_2_row_0_3_3
  · exact right2Middle3_eq_case_5_2_row_1_0_0
  · exact right2Middle3_eq_case_5_2_row_1_0_1
  · exact right2Middle3_eq_case_5_2_row_1_0_2
  · exact right2Middle3_eq_case_5_2_row_1_0_3
  · exact right2Middle3_eq_case_5_2_row_1_1_0
  · exact right2Middle3_eq_case_5_2_row_1_1_1
  · exact right2Middle3_eq_case_5_2_row_1_1_2
  · exact right2Middle3_eq_case_5_2_row_1_1_3
  · exact right2Middle3_eq_case_5_2_row_1_2_0
  · exact right2Middle3_eq_case_5_2_row_1_2_1
  · exact right2Middle3_eq_case_5_2_row_1_2_2
  · exact right2Middle3_eq_case_5_2_row_1_2_3
  · exact right2Middle3_eq_case_5_2_row_1_3_0
  · exact right2Middle3_eq_case_5_2_row_1_3_1
  · exact right2Middle3_eq_case_5_2_row_1_3_2
  · exact right2Middle3_eq_case_5_2_row_1_3_3

set_option backward.isDefEq.respectTransparency false in
theorem right2Middle3_eq_case_5_2 : right2Middle3 5 2 = innerLeftZ 3 2 5 * right1Middle3 5 2 := by
  simpa only [HexagonAtoms352.assocABC_eq,
    HexagonAtoms352.outerABC_eq,
    HexagonAtoms352.assocBAC_eq,
    HexagonAtoms352.innerABC_eq,
    HexagonAtoms352.innerRightABC_eq,
    HexagonAtoms352.inverseACB_eq,
    HexagonAtoms352.innerACB_eq,
    HexagonAtoms352.assocBCA_eq,
    HexagonAtoms352.innerRightBAC_eq,
    HexagonAtoms352.assocCAB_eq,
    HexagonAtoms352.outerLeftABC_eq,
    HexagonRowColumn352.product0_eq,
    HexagonRowColumn352.product1_eq,
    HexagonRowColumn352.product2_eq,
    HexagonRowColumn352.product3_eq,
    HexagonRowColumn352.product4_eq,
    HexagonRowColumn352.product5_eq,
    HexagonRowColumn352.product6_eq,
    HexagonRowColumn352.product7_eq] using right2Middle3_eq_case_5_2_checked

private theorem leftFinal3_case_5_2_row_0_0_0 : (((-1 : ℤ) ^ (leftScaleBit 3 5 2).val * positiveScale (leftScaleExponent 3 5 2)) •
      (rowColumnMul HexagonRowColumn352.rows_assocBCA HexagonRowColumn352.cols_left0)) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 4)) = (negativeScale (leftScaleExponent 3 5 2) • (left1Middle3 5 2)) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal3_case_5_2_row_0_0_1 : (((-1 : ℤ) ^ (leftScaleBit 3 5 2).val * positiveScale (leftScaleExponent 3 5 2)) •
      (rowColumnMul HexagonRowColumn352.rows_assocBCA HexagonRowColumn352.cols_left0)) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 4)) = (negativeScale (leftScaleExponent 3 5 2) • (left1Middle3 5 2)) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal3_case_5_2_row_0_0_2 : (((-1 : ℤ) ^ (leftScaleBit 3 5 2).val * positiveScale (leftScaleExponent 3 5 2)) •
      (rowColumnMul HexagonRowColumn352.rows_assocBCA HexagonRowColumn352.cols_left0)) ((0 : Fin 2), (0 : Fin 4), (2 : Fin 4)) = (negativeScale (leftScaleExponent 3 5 2) • (left1Middle3 5 2)) ((0 : Fin 2), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal3_case_5_2_row_0_0_3 : (((-1 : ℤ) ^ (leftScaleBit 3 5 2).val * positiveScale (leftScaleExponent 3 5 2)) •
      (rowColumnMul HexagonRowColumn352.rows_assocBCA HexagonRowColumn352.cols_left0)) ((0 : Fin 2), (0 : Fin 4), (3 : Fin 4)) = (negativeScale (leftScaleExponent 3 5 2) • (left1Middle3 5 2)) ((0 : Fin 2), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal3_case_5_2_row_0_1_0 : (((-1 : ℤ) ^ (leftScaleBit 3 5 2).val * positiveScale (leftScaleExponent 3 5 2)) •
      (rowColumnMul HexagonRowColumn352.rows_assocBCA HexagonRowColumn352.cols_left0)) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 4)) = (negativeScale (leftScaleExponent 3 5 2) • (left1Middle3 5 2)) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal3_case_5_2_row_0_1_1 : (((-1 : ℤ) ^ (leftScaleBit 3 5 2).val * positiveScale (leftScaleExponent 3 5 2)) •
      (rowColumnMul HexagonRowColumn352.rows_assocBCA HexagonRowColumn352.cols_left0)) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 4)) = (negativeScale (leftScaleExponent 3 5 2) • (left1Middle3 5 2)) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal3_case_5_2_row_0_1_2 : (((-1 : ℤ) ^ (leftScaleBit 3 5 2).val * positiveScale (leftScaleExponent 3 5 2)) •
      (rowColumnMul HexagonRowColumn352.rows_assocBCA HexagonRowColumn352.cols_left0)) ((0 : Fin 2), (1 : Fin 4), (2 : Fin 4)) = (negativeScale (leftScaleExponent 3 5 2) • (left1Middle3 5 2)) ((0 : Fin 2), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal3_case_5_2_row_0_1_3 : (((-1 : ℤ) ^ (leftScaleBit 3 5 2).val * positiveScale (leftScaleExponent 3 5 2)) •
      (rowColumnMul HexagonRowColumn352.rows_assocBCA HexagonRowColumn352.cols_left0)) ((0 : Fin 2), (1 : Fin 4), (3 : Fin 4)) = (negativeScale (leftScaleExponent 3 5 2) • (left1Middle3 5 2)) ((0 : Fin 2), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal3_case_5_2_row_0_2_0 : (((-1 : ℤ) ^ (leftScaleBit 3 5 2).val * positiveScale (leftScaleExponent 3 5 2)) •
      (rowColumnMul HexagonRowColumn352.rows_assocBCA HexagonRowColumn352.cols_left0)) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 4)) = (negativeScale (leftScaleExponent 3 5 2) • (left1Middle3 5 2)) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal3_case_5_2_row_0_2_1 : (((-1 : ℤ) ^ (leftScaleBit 3 5 2).val * positiveScale (leftScaleExponent 3 5 2)) •
      (rowColumnMul HexagonRowColumn352.rows_assocBCA HexagonRowColumn352.cols_left0)) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 4)) = (negativeScale (leftScaleExponent 3 5 2) • (left1Middle3 5 2)) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal3_case_5_2_row_0_2_2 : (((-1 : ℤ) ^ (leftScaleBit 3 5 2).val * positiveScale (leftScaleExponent 3 5 2)) •
      (rowColumnMul HexagonRowColumn352.rows_assocBCA HexagonRowColumn352.cols_left0)) ((0 : Fin 2), (2 : Fin 4), (2 : Fin 4)) = (negativeScale (leftScaleExponent 3 5 2) • (left1Middle3 5 2)) ((0 : Fin 2), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal3_case_5_2_row_0_2_3 : (((-1 : ℤ) ^ (leftScaleBit 3 5 2).val * positiveScale (leftScaleExponent 3 5 2)) •
      (rowColumnMul HexagonRowColumn352.rows_assocBCA HexagonRowColumn352.cols_left0)) ((0 : Fin 2), (2 : Fin 4), (3 : Fin 4)) = (negativeScale (leftScaleExponent 3 5 2) • (left1Middle3 5 2)) ((0 : Fin 2), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal3_case_5_2_row_0_3_0 : (((-1 : ℤ) ^ (leftScaleBit 3 5 2).val * positiveScale (leftScaleExponent 3 5 2)) •
      (rowColumnMul HexagonRowColumn352.rows_assocBCA HexagonRowColumn352.cols_left0)) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 4)) = (negativeScale (leftScaleExponent 3 5 2) • (left1Middle3 5 2)) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal3_case_5_2_row_0_3_1 : (((-1 : ℤ) ^ (leftScaleBit 3 5 2).val * positiveScale (leftScaleExponent 3 5 2)) •
      (rowColumnMul HexagonRowColumn352.rows_assocBCA HexagonRowColumn352.cols_left0)) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 4)) = (negativeScale (leftScaleExponent 3 5 2) • (left1Middle3 5 2)) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal3_case_5_2_row_0_3_2 : (((-1 : ℤ) ^ (leftScaleBit 3 5 2).val * positiveScale (leftScaleExponent 3 5 2)) •
      (rowColumnMul HexagonRowColumn352.rows_assocBCA HexagonRowColumn352.cols_left0)) ((0 : Fin 2), (3 : Fin 4), (2 : Fin 4)) = (negativeScale (leftScaleExponent 3 5 2) • (left1Middle3 5 2)) ((0 : Fin 2), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal3_case_5_2_row_0_3_3 : (((-1 : ℤ) ^ (leftScaleBit 3 5 2).val * positiveScale (leftScaleExponent 3 5 2)) •
      (rowColumnMul HexagonRowColumn352.rows_assocBCA HexagonRowColumn352.cols_left0)) ((0 : Fin 2), (3 : Fin 4), (3 : Fin 4)) = (negativeScale (leftScaleExponent 3 5 2) • (left1Middle3 5 2)) ((0 : Fin 2), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal3_case_5_2_row_1_0_0 : (((-1 : ℤ) ^ (leftScaleBit 3 5 2).val * positiveScale (leftScaleExponent 3 5 2)) •
      (rowColumnMul HexagonRowColumn352.rows_assocBCA HexagonRowColumn352.cols_left0)) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 4)) = (negativeScale (leftScaleExponent 3 5 2) • (left1Middle3 5 2)) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal3_case_5_2_row_1_0_1 : (((-1 : ℤ) ^ (leftScaleBit 3 5 2).val * positiveScale (leftScaleExponent 3 5 2)) •
      (rowColumnMul HexagonRowColumn352.rows_assocBCA HexagonRowColumn352.cols_left0)) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 4)) = (negativeScale (leftScaleExponent 3 5 2) • (left1Middle3 5 2)) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal3_case_5_2_row_1_0_2 : (((-1 : ℤ) ^ (leftScaleBit 3 5 2).val * positiveScale (leftScaleExponent 3 5 2)) •
      (rowColumnMul HexagonRowColumn352.rows_assocBCA HexagonRowColumn352.cols_left0)) ((1 : Fin 2), (0 : Fin 4), (2 : Fin 4)) = (negativeScale (leftScaleExponent 3 5 2) • (left1Middle3 5 2)) ((1 : Fin 2), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal3_case_5_2_row_1_0_3 : (((-1 : ℤ) ^ (leftScaleBit 3 5 2).val * positiveScale (leftScaleExponent 3 5 2)) •
      (rowColumnMul HexagonRowColumn352.rows_assocBCA HexagonRowColumn352.cols_left0)) ((1 : Fin 2), (0 : Fin 4), (3 : Fin 4)) = (negativeScale (leftScaleExponent 3 5 2) • (left1Middle3 5 2)) ((1 : Fin 2), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal3_case_5_2_row_1_1_0 : (((-1 : ℤ) ^ (leftScaleBit 3 5 2).val * positiveScale (leftScaleExponent 3 5 2)) •
      (rowColumnMul HexagonRowColumn352.rows_assocBCA HexagonRowColumn352.cols_left0)) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 4)) = (negativeScale (leftScaleExponent 3 5 2) • (left1Middle3 5 2)) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal3_case_5_2_row_1_1_1 : (((-1 : ℤ) ^ (leftScaleBit 3 5 2).val * positiveScale (leftScaleExponent 3 5 2)) •
      (rowColumnMul HexagonRowColumn352.rows_assocBCA HexagonRowColumn352.cols_left0)) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 4)) = (negativeScale (leftScaleExponent 3 5 2) • (left1Middle3 5 2)) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal3_case_5_2_row_1_1_2 : (((-1 : ℤ) ^ (leftScaleBit 3 5 2).val * positiveScale (leftScaleExponent 3 5 2)) •
      (rowColumnMul HexagonRowColumn352.rows_assocBCA HexagonRowColumn352.cols_left0)) ((1 : Fin 2), (1 : Fin 4), (2 : Fin 4)) = (negativeScale (leftScaleExponent 3 5 2) • (left1Middle3 5 2)) ((1 : Fin 2), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal3_case_5_2_row_1_1_3 : (((-1 : ℤ) ^ (leftScaleBit 3 5 2).val * positiveScale (leftScaleExponent 3 5 2)) •
      (rowColumnMul HexagonRowColumn352.rows_assocBCA HexagonRowColumn352.cols_left0)) ((1 : Fin 2), (1 : Fin 4), (3 : Fin 4)) = (negativeScale (leftScaleExponent 3 5 2) • (left1Middle3 5 2)) ((1 : Fin 2), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal3_case_5_2_row_1_2_0 : (((-1 : ℤ) ^ (leftScaleBit 3 5 2).val * positiveScale (leftScaleExponent 3 5 2)) •
      (rowColumnMul HexagonRowColumn352.rows_assocBCA HexagonRowColumn352.cols_left0)) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 4)) = (negativeScale (leftScaleExponent 3 5 2) • (left1Middle3 5 2)) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal3_case_5_2_row_1_2_1 : (((-1 : ℤ) ^ (leftScaleBit 3 5 2).val * positiveScale (leftScaleExponent 3 5 2)) •
      (rowColumnMul HexagonRowColumn352.rows_assocBCA HexagonRowColumn352.cols_left0)) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 4)) = (negativeScale (leftScaleExponent 3 5 2) • (left1Middle3 5 2)) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal3_case_5_2_row_1_2_2 : (((-1 : ℤ) ^ (leftScaleBit 3 5 2).val * positiveScale (leftScaleExponent 3 5 2)) •
      (rowColumnMul HexagonRowColumn352.rows_assocBCA HexagonRowColumn352.cols_left0)) ((1 : Fin 2), (2 : Fin 4), (2 : Fin 4)) = (negativeScale (leftScaleExponent 3 5 2) • (left1Middle3 5 2)) ((1 : Fin 2), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal3_case_5_2_row_1_2_3 : (((-1 : ℤ) ^ (leftScaleBit 3 5 2).val * positiveScale (leftScaleExponent 3 5 2)) •
      (rowColumnMul HexagonRowColumn352.rows_assocBCA HexagonRowColumn352.cols_left0)) ((1 : Fin 2), (2 : Fin 4), (3 : Fin 4)) = (negativeScale (leftScaleExponent 3 5 2) • (left1Middle3 5 2)) ((1 : Fin 2), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal3_case_5_2_row_1_3_0 : (((-1 : ℤ) ^ (leftScaleBit 3 5 2).val * positiveScale (leftScaleExponent 3 5 2)) •
      (rowColumnMul HexagonRowColumn352.rows_assocBCA HexagonRowColumn352.cols_left0)) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 4)) = (negativeScale (leftScaleExponent 3 5 2) • (left1Middle3 5 2)) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal3_case_5_2_row_1_3_1 : (((-1 : ℤ) ^ (leftScaleBit 3 5 2).val * positiveScale (leftScaleExponent 3 5 2)) •
      (rowColumnMul HexagonRowColumn352.rows_assocBCA HexagonRowColumn352.cols_left0)) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 4)) = (negativeScale (leftScaleExponent 3 5 2) • (left1Middle3 5 2)) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal3_case_5_2_row_1_3_2 : (((-1 : ℤ) ^ (leftScaleBit 3 5 2).val * positiveScale (leftScaleExponent 3 5 2)) •
      (rowColumnMul HexagonRowColumn352.rows_assocBCA HexagonRowColumn352.cols_left0)) ((1 : Fin 2), (3 : Fin 4), (2 : Fin 4)) = (negativeScale (leftScaleExponent 3 5 2) • (left1Middle3 5 2)) ((1 : Fin 2), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal3_case_5_2_row_1_3_3 : (((-1 : ℤ) ^ (leftScaleBit 3 5 2).val * positiveScale (leftScaleExponent 3 5 2)) •
      (rowColumnMul HexagonRowColumn352.rows_assocBCA HexagonRowColumn352.cols_left0)) ((1 : Fin 2), (3 : Fin 4), (3 : Fin 4)) = (negativeScale (leftScaleExponent 3 5 2) • (left1Middle3 5 2)) ((1 : Fin 2), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal3_case_5_2_checked : ((-1 : ℤ) ^ (leftScaleBit 3 5 2).val * positiveScale (leftScaleExponent 3 5 2)) •
      (rowColumnMul HexagonRowColumn352.rows_assocBCA HexagonRowColumn352.cols_left0) = negativeScale (leftScaleExponent 3 5 2) • (left1Middle3 5 2) := by
  funext r
  fin_cases r
  · exact leftFinal3_case_5_2_row_0_0_0
  · exact leftFinal3_case_5_2_row_0_0_1
  · exact leftFinal3_case_5_2_row_0_0_2
  · exact leftFinal3_case_5_2_row_0_0_3
  · exact leftFinal3_case_5_2_row_0_1_0
  · exact leftFinal3_case_5_2_row_0_1_1
  · exact leftFinal3_case_5_2_row_0_1_2
  · exact leftFinal3_case_5_2_row_0_1_3
  · exact leftFinal3_case_5_2_row_0_2_0
  · exact leftFinal3_case_5_2_row_0_2_1
  · exact leftFinal3_case_5_2_row_0_2_2
  · exact leftFinal3_case_5_2_row_0_2_3
  · exact leftFinal3_case_5_2_row_0_3_0
  · exact leftFinal3_case_5_2_row_0_3_1
  · exact leftFinal3_case_5_2_row_0_3_2
  · exact leftFinal3_case_5_2_row_0_3_3
  · exact leftFinal3_case_5_2_row_1_0_0
  · exact leftFinal3_case_5_2_row_1_0_1
  · exact leftFinal3_case_5_2_row_1_0_2
  · exact leftFinal3_case_5_2_row_1_0_3
  · exact leftFinal3_case_5_2_row_1_1_0
  · exact leftFinal3_case_5_2_row_1_1_1
  · exact leftFinal3_case_5_2_row_1_1_2
  · exact leftFinal3_case_5_2_row_1_1_3
  · exact leftFinal3_case_5_2_row_1_2_0
  · exact leftFinal3_case_5_2_row_1_2_1
  · exact leftFinal3_case_5_2_row_1_2_2
  · exact leftFinal3_case_5_2_row_1_2_3
  · exact leftFinal3_case_5_2_row_1_3_0
  · exact leftFinal3_case_5_2_row_1_3_1
  · exact leftFinal3_case_5_2_row_1_3_2
  · exact leftFinal3_case_5_2_row_1_3_3

set_option backward.isDefEq.respectTransparency false in
theorem leftFinal3_case_5_2 : ((-1 : ℤ) ^ (leftScaleBit 3 5 2).val * positiveScale (leftScaleExponent 3 5 2)) •
      (associatorZ 5 2 3 * left0Middle3 5 2) = negativeScale (leftScaleExponent 3 5 2) • (innerRightZ 5 3 2 * left1Middle3 5 2) := by
  simpa only [HexagonAtoms352.assocABC_eq,
    HexagonAtoms352.outerABC_eq,
    HexagonAtoms352.assocBAC_eq,
    HexagonAtoms352.innerABC_eq,
    HexagonAtoms352.innerRightABC_eq,
    HexagonAtoms352.inverseACB_eq,
    HexagonAtoms352.innerACB_eq,
    HexagonAtoms352.assocBCA_eq,
    HexagonAtoms352.innerRightBAC_eq,
    HexagonAtoms352.assocCAB_eq,
    HexagonAtoms352.outerLeftABC_eq,
    HexagonRowColumn352.product0_eq,
    HexagonRowColumn352.product1_eq,
    HexagonRowColumn352.product2_eq,
    HexagonRowColumn352.product3_eq,
    HexagonRowColumn352.product4_eq,
    HexagonRowColumn352.product5_eq,
    HexagonRowColumn352.product6_eq,
    HexagonRowColumn352.product7_eq] using leftFinal3_case_5_2_checked

private theorem rightFinal3_case_5_2_row_0_0_0 : (((-1 : ℤ) ^ (rightScaleBit 3 5 2).val * positiveScale (rightScaleExponent 3 5 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 5 : ℤ)) • HexagonAtoms352.outerLeftABC) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (negativeScale (rightScaleExponent 3 5 2) • (rowColumnMul HexagonRowColumn352.rows_assocCAB HexagonRowColumn352.cols_right2)) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal3_case_5_2_row_0_0_1 : (((-1 : ℤ) ^ (rightScaleBit 3 5 2).val * positiveScale (rightScaleExponent 3 5 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 5 : ℤ)) • HexagonAtoms352.outerLeftABC) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (negativeScale (rightScaleExponent 3 5 2) • (rowColumnMul HexagonRowColumn352.rows_assocCAB HexagonRowColumn352.cols_right2)) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal3_case_5_2_row_0_0_2 : (((-1 : ℤ) ^ (rightScaleBit 3 5 2).val * positiveScale (rightScaleExponent 3 5 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 5 : ℤ)) • HexagonAtoms352.outerLeftABC) ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (negativeScale (rightScaleExponent 3 5 2) • (rowColumnMul HexagonRowColumn352.rows_assocCAB HexagonRowColumn352.cols_right2)) ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal3_case_5_2_row_0_0_3 : (((-1 : ℤ) ^ (rightScaleBit 3 5 2).val * positiveScale (rightScaleExponent 3 5 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 5 : ℤ)) • HexagonAtoms352.outerLeftABC) ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (negativeScale (rightScaleExponent 3 5 2) • (rowColumnMul HexagonRowColumn352.rows_assocCAB HexagonRowColumn352.cols_right2)) ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal3_case_5_2_row_1_0_0 : (((-1 : ℤ) ^ (rightScaleBit 3 5 2).val * positiveScale (rightScaleExponent 3 5 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 5 : ℤ)) • HexagonAtoms352.outerLeftABC) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (negativeScale (rightScaleExponent 3 5 2) • (rowColumnMul HexagonRowColumn352.rows_assocCAB HexagonRowColumn352.cols_right2)) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal3_case_5_2_row_1_0_1 : (((-1 : ℤ) ^ (rightScaleBit 3 5 2).val * positiveScale (rightScaleExponent 3 5 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 5 : ℤ)) • HexagonAtoms352.outerLeftABC) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (negativeScale (rightScaleExponent 3 5 2) • (rowColumnMul HexagonRowColumn352.rows_assocCAB HexagonRowColumn352.cols_right2)) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal3_case_5_2_row_1_0_2 : (((-1 : ℤ) ^ (rightScaleBit 3 5 2).val * positiveScale (rightScaleExponent 3 5 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 5 : ℤ)) • HexagonAtoms352.outerLeftABC) ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (negativeScale (rightScaleExponent 3 5 2) • (rowColumnMul HexagonRowColumn352.rows_assocCAB HexagonRowColumn352.cols_right2)) ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal3_case_5_2_row_1_0_3 : (((-1 : ℤ) ^ (rightScaleBit 3 5 2).val * positiveScale (rightScaleExponent 3 5 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 5 : ℤ)) • HexagonAtoms352.outerLeftABC) ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (negativeScale (rightScaleExponent 3 5 2) • (rowColumnMul HexagonRowColumn352.rows_assocCAB HexagonRowColumn352.cols_right2)) ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal3_case_5_2_row_2_0_0 : (((-1 : ℤ) ^ (rightScaleBit 3 5 2).val * positiveScale (rightScaleExponent 3 5 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 5 : ℤ)) • HexagonAtoms352.outerLeftABC) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (negativeScale (rightScaleExponent 3 5 2) • (rowColumnMul HexagonRowColumn352.rows_assocCAB HexagonRowColumn352.cols_right2)) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal3_case_5_2_row_2_0_1 : (((-1 : ℤ) ^ (rightScaleBit 3 5 2).val * positiveScale (rightScaleExponent 3 5 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 5 : ℤ)) • HexagonAtoms352.outerLeftABC) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (negativeScale (rightScaleExponent 3 5 2) • (rowColumnMul HexagonRowColumn352.rows_assocCAB HexagonRowColumn352.cols_right2)) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal3_case_5_2_row_2_0_2 : (((-1 : ℤ) ^ (rightScaleBit 3 5 2).val * positiveScale (rightScaleExponent 3 5 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 5 : ℤ)) • HexagonAtoms352.outerLeftABC) ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (negativeScale (rightScaleExponent 3 5 2) • (rowColumnMul HexagonRowColumn352.rows_assocCAB HexagonRowColumn352.cols_right2)) ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal3_case_5_2_row_2_0_3 : (((-1 : ℤ) ^ (rightScaleBit 3 5 2).val * positiveScale (rightScaleExponent 3 5 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 5 : ℤ)) • HexagonAtoms352.outerLeftABC) ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (negativeScale (rightScaleExponent 3 5 2) • (rowColumnMul HexagonRowColumn352.rows_assocCAB HexagonRowColumn352.cols_right2)) ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal3_case_5_2_row_3_0_0 : (((-1 : ℤ) ^ (rightScaleBit 3 5 2).val * positiveScale (rightScaleExponent 3 5 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 5 : ℤ)) • HexagonAtoms352.outerLeftABC) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (negativeScale (rightScaleExponent 3 5 2) • (rowColumnMul HexagonRowColumn352.rows_assocCAB HexagonRowColumn352.cols_right2)) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal3_case_5_2_row_3_0_1 : (((-1 : ℤ) ^ (rightScaleBit 3 5 2).val * positiveScale (rightScaleExponent 3 5 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 5 : ℤ)) • HexagonAtoms352.outerLeftABC) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (negativeScale (rightScaleExponent 3 5 2) • (rowColumnMul HexagonRowColumn352.rows_assocCAB HexagonRowColumn352.cols_right2)) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal3_case_5_2_row_3_0_2 : (((-1 : ℤ) ^ (rightScaleBit 3 5 2).val * positiveScale (rightScaleExponent 3 5 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 5 : ℤ)) • HexagonAtoms352.outerLeftABC) ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (negativeScale (rightScaleExponent 3 5 2) • (rowColumnMul HexagonRowColumn352.rows_assocCAB HexagonRowColumn352.cols_right2)) ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal3_case_5_2_row_3_0_3 : (((-1 : ℤ) ^ (rightScaleBit 3 5 2).val * positiveScale (rightScaleExponent 3 5 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 5 : ℤ)) • HexagonAtoms352.outerLeftABC) ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (negativeScale (rightScaleExponent 3 5 2) • (rowColumnMul HexagonRowColumn352.rows_assocCAB HexagonRowColumn352.cols_right2)) ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal3_case_5_2_row_4_0_0 : (((-1 : ℤ) ^ (rightScaleBit 3 5 2).val * positiveScale (rightScaleExponent 3 5 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 5 : ℤ)) • HexagonAtoms352.outerLeftABC) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (negativeScale (rightScaleExponent 3 5 2) • (rowColumnMul HexagonRowColumn352.rows_assocCAB HexagonRowColumn352.cols_right2)) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal3_case_5_2_row_4_0_1 : (((-1 : ℤ) ^ (rightScaleBit 3 5 2).val * positiveScale (rightScaleExponent 3 5 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 5 : ℤ)) • HexagonAtoms352.outerLeftABC) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (negativeScale (rightScaleExponent 3 5 2) • (rowColumnMul HexagonRowColumn352.rows_assocCAB HexagonRowColumn352.cols_right2)) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal3_case_5_2_row_4_0_2 : (((-1 : ℤ) ^ (rightScaleBit 3 5 2).val * positiveScale (rightScaleExponent 3 5 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 5 : ℤ)) • HexagonAtoms352.outerLeftABC) ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (negativeScale (rightScaleExponent 3 5 2) • (rowColumnMul HexagonRowColumn352.rows_assocCAB HexagonRowColumn352.cols_right2)) ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal3_case_5_2_row_4_0_3 : (((-1 : ℤ) ^ (rightScaleBit 3 5 2).val * positiveScale (rightScaleExponent 3 5 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 5 : ℤ)) • HexagonAtoms352.outerLeftABC) ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (negativeScale (rightScaleExponent 3 5 2) • (rowColumnMul HexagonRowColumn352.rows_assocCAB HexagonRowColumn352.cols_right2)) ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal3_case_5_2_row_5_0_0 : (((-1 : ℤ) ^ (rightScaleBit 3 5 2).val * positiveScale (rightScaleExponent 3 5 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 5 : ℤ)) • HexagonAtoms352.outerLeftABC) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (negativeScale (rightScaleExponent 3 5 2) • (rowColumnMul HexagonRowColumn352.rows_assocCAB HexagonRowColumn352.cols_right2)) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal3_case_5_2_row_5_0_1 : (((-1 : ℤ) ^ (rightScaleBit 3 5 2).val * positiveScale (rightScaleExponent 3 5 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 5 : ℤ)) • HexagonAtoms352.outerLeftABC) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (negativeScale (rightScaleExponent 3 5 2) • (rowColumnMul HexagonRowColumn352.rows_assocCAB HexagonRowColumn352.cols_right2)) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal3_case_5_2_row_5_0_2 : (((-1 : ℤ) ^ (rightScaleBit 3 5 2).val * positiveScale (rightScaleExponent 3 5 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 5 : ℤ)) • HexagonAtoms352.outerLeftABC) ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (negativeScale (rightScaleExponent 3 5 2) • (rowColumnMul HexagonRowColumn352.rows_assocCAB HexagonRowColumn352.cols_right2)) ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal3_case_5_2_row_5_0_3 : (((-1 : ℤ) ^ (rightScaleBit 3 5 2).val * positiveScale (rightScaleExponent 3 5 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 5 : ℤ)) • HexagonAtoms352.outerLeftABC) ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (negativeScale (rightScaleExponent 3 5 2) • (rowColumnMul HexagonRowColumn352.rows_assocCAB HexagonRowColumn352.cols_right2)) ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal3_case_5_2_row_6_0_0 : (((-1 : ℤ) ^ (rightScaleBit 3 5 2).val * positiveScale (rightScaleExponent 3 5 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 5 : ℤ)) • HexagonAtoms352.outerLeftABC) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (negativeScale (rightScaleExponent 3 5 2) • (rowColumnMul HexagonRowColumn352.rows_assocCAB HexagonRowColumn352.cols_right2)) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal3_case_5_2_row_6_0_1 : (((-1 : ℤ) ^ (rightScaleBit 3 5 2).val * positiveScale (rightScaleExponent 3 5 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 5 : ℤ)) • HexagonAtoms352.outerLeftABC) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (negativeScale (rightScaleExponent 3 5 2) • (rowColumnMul HexagonRowColumn352.rows_assocCAB HexagonRowColumn352.cols_right2)) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal3_case_5_2_row_6_0_2 : (((-1 : ℤ) ^ (rightScaleBit 3 5 2).val * positiveScale (rightScaleExponent 3 5 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 5 : ℤ)) • HexagonAtoms352.outerLeftABC) ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (negativeScale (rightScaleExponent 3 5 2) • (rowColumnMul HexagonRowColumn352.rows_assocCAB HexagonRowColumn352.cols_right2)) ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal3_case_5_2_row_6_0_3 : (((-1 : ℤ) ^ (rightScaleBit 3 5 2).val * positiveScale (rightScaleExponent 3 5 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 5 : ℤ)) • HexagonAtoms352.outerLeftABC) ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (negativeScale (rightScaleExponent 3 5 2) • (rowColumnMul HexagonRowColumn352.rows_assocCAB HexagonRowColumn352.cols_right2)) ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal3_case_5_2_row_7_0_0 : (((-1 : ℤ) ^ (rightScaleBit 3 5 2).val * positiveScale (rightScaleExponent 3 5 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 5 : ℤ)) • HexagonAtoms352.outerLeftABC) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (negativeScale (rightScaleExponent 3 5 2) • (rowColumnMul HexagonRowColumn352.rows_assocCAB HexagonRowColumn352.cols_right2)) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal3_case_5_2_row_7_0_1 : (((-1 : ℤ) ^ (rightScaleBit 3 5 2).val * positiveScale (rightScaleExponent 3 5 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 5 : ℤ)) • HexagonAtoms352.outerLeftABC) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (negativeScale (rightScaleExponent 3 5 2) • (rowColumnMul HexagonRowColumn352.rows_assocCAB HexagonRowColumn352.cols_right2)) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal3_case_5_2_row_7_0_2 : (((-1 : ℤ) ^ (rightScaleBit 3 5 2).val * positiveScale (rightScaleExponent 3 5 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 5 : ℤ)) • HexagonAtoms352.outerLeftABC) ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (negativeScale (rightScaleExponent 3 5 2) • (rowColumnMul HexagonRowColumn352.rows_assocCAB HexagonRowColumn352.cols_right2)) ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal3_case_5_2_row_7_0_3 : (((-1 : ℤ) ^ (rightScaleBit 3 5 2).val * positiveScale (rightScaleExponent 3 5 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 5 : ℤ)) • HexagonAtoms352.outerLeftABC) ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (negativeScale (rightScaleExponent 3 5 2) • (rowColumnMul HexagonRowColumn352.rows_assocCAB HexagonRowColumn352.cols_right2)) ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal3_case_5_2_checked : ((-1 : ℤ) ^ (rightScaleBit 3 5 2).val * positiveScale (rightScaleExponent 3 5 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 5 : ℤ)) • HexagonAtoms352.outerLeftABC = negativeScale (rightScaleExponent 3 5 2) • (rowColumnMul HexagonRowColumn352.rows_assocCAB HexagonRowColumn352.cols_right2) := by
  funext r
  fin_cases r
  · exact rightFinal3_case_5_2_row_0_0_0
  · exact rightFinal3_case_5_2_row_0_0_1
  · exact rightFinal3_case_5_2_row_0_0_2
  · exact rightFinal3_case_5_2_row_0_0_3
  · exact rightFinal3_case_5_2_row_1_0_0
  · exact rightFinal3_case_5_2_row_1_0_1
  · exact rightFinal3_case_5_2_row_1_0_2
  · exact rightFinal3_case_5_2_row_1_0_3
  · exact rightFinal3_case_5_2_row_2_0_0
  · exact rightFinal3_case_5_2_row_2_0_1
  · exact rightFinal3_case_5_2_row_2_0_2
  · exact rightFinal3_case_5_2_row_2_0_3
  · exact rightFinal3_case_5_2_row_3_0_0
  · exact rightFinal3_case_5_2_row_3_0_1
  · exact rightFinal3_case_5_2_row_3_0_2
  · exact rightFinal3_case_5_2_row_3_0_3
  · exact rightFinal3_case_5_2_row_4_0_0
  · exact rightFinal3_case_5_2_row_4_0_1
  · exact rightFinal3_case_5_2_row_4_0_2
  · exact rightFinal3_case_5_2_row_4_0_3
  · exact rightFinal3_case_5_2_row_5_0_0
  · exact rightFinal3_case_5_2_row_5_0_1
  · exact rightFinal3_case_5_2_row_5_0_2
  · exact rightFinal3_case_5_2_row_5_0_3
  · exact rightFinal3_case_5_2_row_6_0_0
  · exact rightFinal3_case_5_2_row_6_0_1
  · exact rightFinal3_case_5_2_row_6_0_2
  · exact rightFinal3_case_5_2_row_6_0_3
  · exact rightFinal3_case_5_2_row_7_0_0
  · exact rightFinal3_case_5_2_row_7_0_1
  · exact rightFinal3_case_5_2_row_7_0_2
  · exact rightFinal3_case_5_2_row_7_0_3

set_option backward.isDefEq.respectTransparency false in
theorem rightFinal3_case_5_2 : ((-1 : ℤ) ^ (rightScaleBit 3 5 2).val * positiveScale (rightScaleExponent 3 5 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 5 : ℤ)) • outerLeftZ 3 5 2 = negativeScale (rightScaleExponent 3 5 2) • (associatorZ 2 3 5 * right2Middle3 5 2) := by
  simpa only [HexagonAtoms352.assocABC_eq,
    HexagonAtoms352.outerABC_eq,
    HexagonAtoms352.assocBAC_eq,
    HexagonAtoms352.innerABC_eq,
    HexagonAtoms352.innerRightABC_eq,
    HexagonAtoms352.inverseACB_eq,
    HexagonAtoms352.innerACB_eq,
    HexagonAtoms352.assocBCA_eq,
    HexagonAtoms352.innerRightBAC_eq,
    HexagonAtoms352.assocCAB_eq,
    HexagonAtoms352.outerLeftABC_eq,
    HexagonRowColumn352.product0_eq,
    HexagonRowColumn352.product1_eq,
    HexagonRowColumn352.product2_eq,
    HexagonRowColumn352.product3_eq,
    HexagonRowColumn352.product4_eq,
    HexagonRowColumn352.product5_eq,
    HexagonRowColumn352.product6_eq,
    HexagonRowColumn352.product7_eq] using rightFinal3_case_5_2_checked

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonCases3
