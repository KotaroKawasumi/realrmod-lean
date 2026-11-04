import RMod.BrundanEllis.StackingReferenceHexagonMiddle3
import RMod.BrundanEllis.StackingReferenceSparseMatrixCheck
import RMod.BrundanEllis.StackingReferenceHexagonAtoms363
import RMod.BrundanEllis.StackingReferenceHexagonRowColumn363

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

private theorem left0Middle3_eq_case_6_3_row_0_0_0 : (left0Middle3 6 3) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn363.rows_outerABC HexagonRowColumn363.cols_assocABC) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_6_3_row_0_0_1 : (left0Middle3 6 3) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn363.rows_outerABC HexagonRowColumn363.cols_assocABC) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_6_3_row_0_0_2 : (left0Middle3 6 3) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn363.rows_outerABC HexagonRowColumn363.cols_assocABC) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_6_3_row_0_0_3 : (left0Middle3 6 3) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn363.rows_outerABC HexagonRowColumn363.cols_assocABC) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_6_3_row_0_1_0 : (left0Middle3 6 3) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn363.rows_outerABC HexagonRowColumn363.cols_assocABC) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_6_3_row_0_1_1 : (left0Middle3 6 3) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn363.rows_outerABC HexagonRowColumn363.cols_assocABC) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_6_3_row_0_1_2 : (left0Middle3 6 3) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn363.rows_outerABC HexagonRowColumn363.cols_assocABC) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_6_3_row_0_1_3 : (left0Middle3 6 3) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn363.rows_outerABC HexagonRowColumn363.cols_assocABC) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_6_3_row_1_0_0 : (left0Middle3 6 3) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn363.rows_outerABC HexagonRowColumn363.cols_assocABC) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_6_3_row_1_0_1 : (left0Middle3 6 3) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn363.rows_outerABC HexagonRowColumn363.cols_assocABC) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_6_3_row_1_0_2 : (left0Middle3 6 3) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn363.rows_outerABC HexagonRowColumn363.cols_assocABC) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_6_3_row_1_0_3 : (left0Middle3 6 3) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn363.rows_outerABC HexagonRowColumn363.cols_assocABC) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_6_3_row_1_1_0 : (left0Middle3 6 3) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn363.rows_outerABC HexagonRowColumn363.cols_assocABC) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_6_3_row_1_1_1 : (left0Middle3 6 3) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn363.rows_outerABC HexagonRowColumn363.cols_assocABC) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_6_3_row_1_1_2 : (left0Middle3 6 3) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn363.rows_outerABC HexagonRowColumn363.cols_assocABC) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_6_3_row_1_1_3 : (left0Middle3 6 3) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn363.rows_outerABC HexagonRowColumn363.cols_assocABC) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_6_3_row_2_0_0 : (left0Middle3 6 3) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn363.rows_outerABC HexagonRowColumn363.cols_assocABC) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_6_3_row_2_0_1 : (left0Middle3 6 3) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn363.rows_outerABC HexagonRowColumn363.cols_assocABC) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_6_3_row_2_0_2 : (left0Middle3 6 3) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn363.rows_outerABC HexagonRowColumn363.cols_assocABC) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_6_3_row_2_0_3 : (left0Middle3 6 3) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn363.rows_outerABC HexagonRowColumn363.cols_assocABC) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_6_3_row_2_1_0 : (left0Middle3 6 3) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn363.rows_outerABC HexagonRowColumn363.cols_assocABC) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_6_3_row_2_1_1 : (left0Middle3 6 3) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn363.rows_outerABC HexagonRowColumn363.cols_assocABC) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_6_3_row_2_1_2 : (left0Middle3 6 3) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn363.rows_outerABC HexagonRowColumn363.cols_assocABC) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_6_3_row_2_1_3 : (left0Middle3 6 3) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn363.rows_outerABC HexagonRowColumn363.cols_assocABC) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_6_3_row_3_0_0 : (left0Middle3 6 3) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn363.rows_outerABC HexagonRowColumn363.cols_assocABC) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_6_3_row_3_0_1 : (left0Middle3 6 3) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn363.rows_outerABC HexagonRowColumn363.cols_assocABC) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_6_3_row_3_0_2 : (left0Middle3 6 3) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn363.rows_outerABC HexagonRowColumn363.cols_assocABC) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_6_3_row_3_0_3 : (left0Middle3 6 3) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn363.rows_outerABC HexagonRowColumn363.cols_assocABC) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_6_3_row_3_1_0 : (left0Middle3 6 3) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn363.rows_outerABC HexagonRowColumn363.cols_assocABC) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_6_3_row_3_1_1 : (left0Middle3 6 3) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn363.rows_outerABC HexagonRowColumn363.cols_assocABC) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_6_3_row_3_1_2 : (left0Middle3 6 3) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn363.rows_outerABC HexagonRowColumn363.cols_assocABC) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_6_3_row_3_1_3 : (left0Middle3 6 3) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn363.rows_outerABC HexagonRowColumn363.cols_assocABC) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_6_3_checked : left0Middle3 6 3 = rowColumnMul HexagonRowColumn363.rows_outerABC HexagonRowColumn363.cols_assocABC := by
  funext r
  fin_cases r
  · exact left0Middle3_eq_case_6_3_row_0_0_0
  · exact left0Middle3_eq_case_6_3_row_0_0_1
  · exact left0Middle3_eq_case_6_3_row_0_0_2
  · exact left0Middle3_eq_case_6_3_row_0_0_3
  · exact left0Middle3_eq_case_6_3_row_0_1_0
  · exact left0Middle3_eq_case_6_3_row_0_1_1
  · exact left0Middle3_eq_case_6_3_row_0_1_2
  · exact left0Middle3_eq_case_6_3_row_0_1_3
  · exact left0Middle3_eq_case_6_3_row_1_0_0
  · exact left0Middle3_eq_case_6_3_row_1_0_1
  · exact left0Middle3_eq_case_6_3_row_1_0_2
  · exact left0Middle3_eq_case_6_3_row_1_0_3
  · exact left0Middle3_eq_case_6_3_row_1_1_0
  · exact left0Middle3_eq_case_6_3_row_1_1_1
  · exact left0Middle3_eq_case_6_3_row_1_1_2
  · exact left0Middle3_eq_case_6_3_row_1_1_3
  · exact left0Middle3_eq_case_6_3_row_2_0_0
  · exact left0Middle3_eq_case_6_3_row_2_0_1
  · exact left0Middle3_eq_case_6_3_row_2_0_2
  · exact left0Middle3_eq_case_6_3_row_2_0_3
  · exact left0Middle3_eq_case_6_3_row_2_1_0
  · exact left0Middle3_eq_case_6_3_row_2_1_1
  · exact left0Middle3_eq_case_6_3_row_2_1_2
  · exact left0Middle3_eq_case_6_3_row_2_1_3
  · exact left0Middle3_eq_case_6_3_row_3_0_0
  · exact left0Middle3_eq_case_6_3_row_3_0_1
  · exact left0Middle3_eq_case_6_3_row_3_0_2
  · exact left0Middle3_eq_case_6_3_row_3_0_3
  · exact left0Middle3_eq_case_6_3_row_3_1_0
  · exact left0Middle3_eq_case_6_3_row_3_1_1
  · exact left0Middle3_eq_case_6_3_row_3_1_2
  · exact left0Middle3_eq_case_6_3_row_3_1_3

set_option backward.isDefEq.respectTransparency false in
theorem left0Middle3_eq_case_6_3 : left0Middle3 6 3 = outerRightZ 3 6 3 * associatorZ 3 6 3 := by
  simpa only [HexagonAtoms363.assocABC_eq,
    HexagonAtoms363.outerABC_eq,
    HexagonAtoms363.assocBAC_eq,
    HexagonAtoms363.innerABC_eq,
    HexagonAtoms363.innerRightABC_eq,
    HexagonAtoms363.inverseACB_eq,
    HexagonAtoms363.innerACB_eq,
    HexagonAtoms363.assocBCA_eq,
    HexagonAtoms363.innerRightBAC_eq,
    HexagonAtoms363.assocCAB_eq,
    HexagonAtoms363.outerLeftABC_eq,
    HexagonRowColumn363.assocBCA_alias,
    HexagonRowColumn363.product0_eq,
    HexagonRowColumn363.product1_eq,
    HexagonRowColumn363.product2_eq,
    HexagonRowColumn363.product3_eq,
    HexagonRowColumn363.product4_eq,
    HexagonRowColumn363.product5_eq,
    HexagonRowColumn363.product6_eq,
    HexagonRowColumn363.product7_eq] using left0Middle3_eq_case_6_3_checked

private theorem left1Middle3_eq_case_6_3_row_0_0_0 : (left1Middle3 6 3) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms363.assocBAC) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_6_3_row_0_0_1 : (left1Middle3 6 3) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms363.assocBAC) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_6_3_row_0_0_2 : (left1Middle3 6 3) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms363.assocBAC) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_6_3_row_0_0_3 : (left1Middle3 6 3) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms363.assocBAC) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_6_3_row_0_1_0 : (left1Middle3 6 3) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms363.assocBAC) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_6_3_row_0_1_1 : (left1Middle3 6 3) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms363.assocBAC) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_6_3_row_0_1_2 : (left1Middle3 6 3) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms363.assocBAC) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_6_3_row_0_1_3 : (left1Middle3 6 3) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms363.assocBAC) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_6_3_row_1_0_0 : (left1Middle3 6 3) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms363.assocBAC) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_6_3_row_1_0_1 : (left1Middle3 6 3) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms363.assocBAC) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_6_3_row_1_0_2 : (left1Middle3 6 3) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms363.assocBAC) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_6_3_row_1_0_3 : (left1Middle3 6 3) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms363.assocBAC) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_6_3_row_1_1_0 : (left1Middle3 6 3) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms363.assocBAC) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_6_3_row_1_1_1 : (left1Middle3 6 3) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms363.assocBAC) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_6_3_row_1_1_2 : (left1Middle3 6 3) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms363.assocBAC) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_6_3_row_1_1_3 : (left1Middle3 6 3) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms363.assocBAC) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_6_3_row_2_0_0 : (left1Middle3 6 3) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms363.assocBAC) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_6_3_row_2_0_1 : (left1Middle3 6 3) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms363.assocBAC) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_6_3_row_2_0_2 : (left1Middle3 6 3) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms363.assocBAC) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_6_3_row_2_0_3 : (left1Middle3 6 3) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms363.assocBAC) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_6_3_row_2_1_0 : (left1Middle3 6 3) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms363.assocBAC) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_6_3_row_2_1_1 : (left1Middle3 6 3) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms363.assocBAC) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_6_3_row_2_1_2 : (left1Middle3 6 3) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms363.assocBAC) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_6_3_row_2_1_3 : (left1Middle3 6 3) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms363.assocBAC) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_6_3_row_3_0_0 : (left1Middle3 6 3) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms363.assocBAC) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_6_3_row_3_0_1 : (left1Middle3 6 3) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms363.assocBAC) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_6_3_row_3_0_2 : (left1Middle3 6 3) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms363.assocBAC) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_6_3_row_3_0_3 : (left1Middle3 6 3) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms363.assocBAC) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_6_3_row_3_1_0 : (left1Middle3 6 3) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms363.assocBAC) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_6_3_row_3_1_1 : (left1Middle3 6 3) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms363.assocBAC) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_6_3_row_3_1_2 : (left1Middle3 6 3) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms363.assocBAC) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_6_3_row_3_1_3 : (left1Middle3 6 3) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms363.assocBAC) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_6_3_checked : left1Middle3 6 3 = HexagonAtoms363.assocBAC := by
  funext r
  fin_cases r
  · exact left1Middle3_eq_case_6_3_row_0_0_0
  · exact left1Middle3_eq_case_6_3_row_0_0_1
  · exact left1Middle3_eq_case_6_3_row_0_0_2
  · exact left1Middle3_eq_case_6_3_row_0_0_3
  · exact left1Middle3_eq_case_6_3_row_0_1_0
  · exact left1Middle3_eq_case_6_3_row_0_1_1
  · exact left1Middle3_eq_case_6_3_row_0_1_2
  · exact left1Middle3_eq_case_6_3_row_0_1_3
  · exact left1Middle3_eq_case_6_3_row_1_0_0
  · exact left1Middle3_eq_case_6_3_row_1_0_1
  · exact left1Middle3_eq_case_6_3_row_1_0_2
  · exact left1Middle3_eq_case_6_3_row_1_0_3
  · exact left1Middle3_eq_case_6_3_row_1_1_0
  · exact left1Middle3_eq_case_6_3_row_1_1_1
  · exact left1Middle3_eq_case_6_3_row_1_1_2
  · exact left1Middle3_eq_case_6_3_row_1_1_3
  · exact left1Middle3_eq_case_6_3_row_2_0_0
  · exact left1Middle3_eq_case_6_3_row_2_0_1
  · exact left1Middle3_eq_case_6_3_row_2_0_2
  · exact left1Middle3_eq_case_6_3_row_2_0_3
  · exact left1Middle3_eq_case_6_3_row_2_1_0
  · exact left1Middle3_eq_case_6_3_row_2_1_1
  · exact left1Middle3_eq_case_6_3_row_2_1_2
  · exact left1Middle3_eq_case_6_3_row_2_1_3
  · exact left1Middle3_eq_case_6_3_row_3_0_0
  · exact left1Middle3_eq_case_6_3_row_3_0_1
  · exact left1Middle3_eq_case_6_3_row_3_0_2
  · exact left1Middle3_eq_case_6_3_row_3_0_3
  · exact left1Middle3_eq_case_6_3_row_3_1_0
  · exact left1Middle3_eq_case_6_3_row_3_1_1
  · exact left1Middle3_eq_case_6_3_row_3_1_2
  · exact left1Middle3_eq_case_6_3_row_3_1_3

set_option backward.isDefEq.respectTransparency false in
theorem left1Middle3_eq_case_6_3 : left1Middle3 6 3 = associatorZ 6 3 3 * innerLeftZ 3 6 3 := by
  simpa only [HexagonAtoms363.assocABC_eq,
    HexagonAtoms363.outerABC_eq,
    HexagonAtoms363.assocBAC_eq,
    HexagonAtoms363.innerABC_eq,
    HexagonAtoms363.innerRightABC_eq,
    HexagonAtoms363.inverseACB_eq,
    HexagonAtoms363.innerACB_eq,
    HexagonAtoms363.assocBCA_eq,
    HexagonAtoms363.innerRightBAC_eq,
    HexagonAtoms363.assocCAB_eq,
    HexagonAtoms363.outerLeftABC_eq,
    HexagonRowColumn363.assocBCA_alias,
    HexagonRowColumn363.product0_eq,
    HexagonRowColumn363.product1_eq,
    HexagonRowColumn363.product2_eq,
    HexagonRowColumn363.product3_eq,
    HexagonRowColumn363.product4_eq,
    HexagonRowColumn363.product5_eq,
    HexagonRowColumn363.product6_eq,
    HexagonRowColumn363.product7_eq] using left1Middle3_eq_case_6_3_checked

private theorem right0Middle3_eq_case_6_3_row_0_0_0 : (right0Middle3 6 3) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms363.assocABC) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_6_3_row_0_0_1 : (right0Middle3 6 3) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms363.assocABC) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_6_3_row_0_0_2 : (right0Middle3 6 3) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms363.assocABC) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_6_3_row_0_0_3 : (right0Middle3 6 3) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms363.assocABC) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_6_3_row_0_1_0 : (right0Middle3 6 3) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms363.assocABC) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_6_3_row_0_1_1 : (right0Middle3 6 3) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms363.assocABC) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_6_3_row_0_1_2 : (right0Middle3 6 3) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms363.assocABC) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_6_3_row_0_1_3 : (right0Middle3 6 3) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms363.assocABC) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_6_3_row_1_0_0 : (right0Middle3 6 3) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms363.assocABC) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_6_3_row_1_0_1 : (right0Middle3 6 3) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms363.assocABC) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_6_3_row_1_0_2 : (right0Middle3 6 3) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms363.assocABC) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_6_3_row_1_0_3 : (right0Middle3 6 3) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms363.assocABC) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_6_3_row_1_1_0 : (right0Middle3 6 3) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms363.assocABC) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_6_3_row_1_1_1 : (right0Middle3 6 3) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms363.assocABC) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_6_3_row_1_1_2 : (right0Middle3 6 3) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms363.assocABC) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_6_3_row_1_1_3 : (right0Middle3 6 3) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms363.assocABC) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_6_3_row_2_0_0 : (right0Middle3 6 3) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms363.assocABC) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_6_3_row_2_0_1 : (right0Middle3 6 3) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms363.assocABC) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_6_3_row_2_0_2 : (right0Middle3 6 3) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms363.assocABC) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_6_3_row_2_0_3 : (right0Middle3 6 3) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms363.assocABC) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_6_3_row_2_1_0 : (right0Middle3 6 3) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms363.assocABC) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_6_3_row_2_1_1 : (right0Middle3 6 3) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms363.assocABC) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_6_3_row_2_1_2 : (right0Middle3 6 3) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms363.assocABC) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_6_3_row_2_1_3 : (right0Middle3 6 3) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms363.assocABC) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_6_3_row_3_0_0 : (right0Middle3 6 3) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms363.assocABC) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_6_3_row_3_0_1 : (right0Middle3 6 3) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms363.assocABC) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_6_3_row_3_0_2 : (right0Middle3 6 3) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms363.assocABC) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_6_3_row_3_0_3 : (right0Middle3 6 3) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms363.assocABC) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_6_3_row_3_1_0 : (right0Middle3 6 3) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms363.assocABC) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_6_3_row_3_1_1 : (right0Middle3 6 3) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms363.assocABC) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_6_3_row_3_1_2 : (right0Middle3 6 3) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms363.assocABC) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_6_3_row_3_1_3 : (right0Middle3 6 3) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms363.assocABC) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_6_3_checked : right0Middle3 6 3 = HexagonAtoms363.assocABC := by
  funext r
  fin_cases r
  · exact right0Middle3_eq_case_6_3_row_0_0_0
  · exact right0Middle3_eq_case_6_3_row_0_0_1
  · exact right0Middle3_eq_case_6_3_row_0_0_2
  · exact right0Middle3_eq_case_6_3_row_0_0_3
  · exact right0Middle3_eq_case_6_3_row_0_1_0
  · exact right0Middle3_eq_case_6_3_row_0_1_1
  · exact right0Middle3_eq_case_6_3_row_0_1_2
  · exact right0Middle3_eq_case_6_3_row_0_1_3
  · exact right0Middle3_eq_case_6_3_row_1_0_0
  · exact right0Middle3_eq_case_6_3_row_1_0_1
  · exact right0Middle3_eq_case_6_3_row_1_0_2
  · exact right0Middle3_eq_case_6_3_row_1_0_3
  · exact right0Middle3_eq_case_6_3_row_1_1_0
  · exact right0Middle3_eq_case_6_3_row_1_1_1
  · exact right0Middle3_eq_case_6_3_row_1_1_2
  · exact right0Middle3_eq_case_6_3_row_1_1_3
  · exact right0Middle3_eq_case_6_3_row_2_0_0
  · exact right0Middle3_eq_case_6_3_row_2_0_1
  · exact right0Middle3_eq_case_6_3_row_2_0_2
  · exact right0Middle3_eq_case_6_3_row_2_0_3
  · exact right0Middle3_eq_case_6_3_row_2_1_0
  · exact right0Middle3_eq_case_6_3_row_2_1_1
  · exact right0Middle3_eq_case_6_3_row_2_1_2
  · exact right0Middle3_eq_case_6_3_row_2_1_3
  · exact right0Middle3_eq_case_6_3_row_3_0_0
  · exact right0Middle3_eq_case_6_3_row_3_0_1
  · exact right0Middle3_eq_case_6_3_row_3_0_2
  · exact right0Middle3_eq_case_6_3_row_3_0_3
  · exact right0Middle3_eq_case_6_3_row_3_1_0
  · exact right0Middle3_eq_case_6_3_row_3_1_1
  · exact right0Middle3_eq_case_6_3_row_3_1_2
  · exact right0Middle3_eq_case_6_3_row_3_1_3

set_option backward.isDefEq.respectTransparency false in
theorem right0Middle3_eq_case_6_3 : right0Middle3 6 3 = innerRightZ 3 6 3 * associatorZ 3 6 3 := by
  simpa only [HexagonAtoms363.assocABC_eq,
    HexagonAtoms363.outerABC_eq,
    HexagonAtoms363.assocBAC_eq,
    HexagonAtoms363.innerABC_eq,
    HexagonAtoms363.innerRightABC_eq,
    HexagonAtoms363.inverseACB_eq,
    HexagonAtoms363.innerACB_eq,
    HexagonAtoms363.assocBCA_eq,
    HexagonAtoms363.innerRightBAC_eq,
    HexagonAtoms363.assocCAB_eq,
    HexagonAtoms363.outerLeftABC_eq,
    HexagonRowColumn363.assocBCA_alias,
    HexagonRowColumn363.product0_eq,
    HexagonRowColumn363.product1_eq,
    HexagonRowColumn363.product2_eq,
    HexagonRowColumn363.product3_eq,
    HexagonRowColumn363.product4_eq,
    HexagonRowColumn363.product5_eq,
    HexagonRowColumn363.product6_eq,
    HexagonRowColumn363.product7_eq] using right0Middle3_eq_case_6_3_checked

private theorem right1Middle3_eq_case_6_3_row_0_0_0 : (right1Middle3 6 3) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn363.rows_inverseACB HexagonRowColumn363.cols_right0) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_6_3_row_0_0_1 : (right1Middle3 6 3) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn363.rows_inverseACB HexagonRowColumn363.cols_right0) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_6_3_row_0_0_2 : (right1Middle3 6 3) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn363.rows_inverseACB HexagonRowColumn363.cols_right0) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_6_3_row_0_0_3 : (right1Middle3 6 3) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn363.rows_inverseACB HexagonRowColumn363.cols_right0) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_6_3_row_0_1_0 : (right1Middle3 6 3) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn363.rows_inverseACB HexagonRowColumn363.cols_right0) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_6_3_row_0_1_1 : (right1Middle3 6 3) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn363.rows_inverseACB HexagonRowColumn363.cols_right0) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_6_3_row_0_1_2 : (right1Middle3 6 3) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn363.rows_inverseACB HexagonRowColumn363.cols_right0) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_6_3_row_0_1_3 : (right1Middle3 6 3) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn363.rows_inverseACB HexagonRowColumn363.cols_right0) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_6_3_row_1_0_0 : (right1Middle3 6 3) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn363.rows_inverseACB HexagonRowColumn363.cols_right0) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_6_3_row_1_0_1 : (right1Middle3 6 3) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn363.rows_inverseACB HexagonRowColumn363.cols_right0) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_6_3_row_1_0_2 : (right1Middle3 6 3) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn363.rows_inverseACB HexagonRowColumn363.cols_right0) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_6_3_row_1_0_3 : (right1Middle3 6 3) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn363.rows_inverseACB HexagonRowColumn363.cols_right0) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_6_3_row_1_1_0 : (right1Middle3 6 3) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn363.rows_inverseACB HexagonRowColumn363.cols_right0) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_6_3_row_1_1_1 : (right1Middle3 6 3) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn363.rows_inverseACB HexagonRowColumn363.cols_right0) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_6_3_row_1_1_2 : (right1Middle3 6 3) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn363.rows_inverseACB HexagonRowColumn363.cols_right0) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_6_3_row_1_1_3 : (right1Middle3 6 3) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn363.rows_inverseACB HexagonRowColumn363.cols_right0) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_6_3_row_2_0_0 : (right1Middle3 6 3) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn363.rows_inverseACB HexagonRowColumn363.cols_right0) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_6_3_row_2_0_1 : (right1Middle3 6 3) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn363.rows_inverseACB HexagonRowColumn363.cols_right0) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_6_3_row_2_0_2 : (right1Middle3 6 3) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn363.rows_inverseACB HexagonRowColumn363.cols_right0) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_6_3_row_2_0_3 : (right1Middle3 6 3) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn363.rows_inverseACB HexagonRowColumn363.cols_right0) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_6_3_row_2_1_0 : (right1Middle3 6 3) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn363.rows_inverseACB HexagonRowColumn363.cols_right0) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_6_3_row_2_1_1 : (right1Middle3 6 3) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn363.rows_inverseACB HexagonRowColumn363.cols_right0) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_6_3_row_2_1_2 : (right1Middle3 6 3) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn363.rows_inverseACB HexagonRowColumn363.cols_right0) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_6_3_row_2_1_3 : (right1Middle3 6 3) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn363.rows_inverseACB HexagonRowColumn363.cols_right0) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_6_3_row_3_0_0 : (right1Middle3 6 3) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn363.rows_inverseACB HexagonRowColumn363.cols_right0) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_6_3_row_3_0_1 : (right1Middle3 6 3) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn363.rows_inverseACB HexagonRowColumn363.cols_right0) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_6_3_row_3_0_2 : (right1Middle3 6 3) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn363.rows_inverseACB HexagonRowColumn363.cols_right0) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_6_3_row_3_0_3 : (right1Middle3 6 3) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn363.rows_inverseACB HexagonRowColumn363.cols_right0) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_6_3_row_3_1_0 : (right1Middle3 6 3) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn363.rows_inverseACB HexagonRowColumn363.cols_right0) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_6_3_row_3_1_1 : (right1Middle3 6 3) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn363.rows_inverseACB HexagonRowColumn363.cols_right0) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_6_3_row_3_1_2 : (right1Middle3 6 3) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn363.rows_inverseACB HexagonRowColumn363.cols_right0) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_6_3_row_3_1_3 : (right1Middle3 6 3) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn363.rows_inverseACB HexagonRowColumn363.cols_right0) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_6_3_checked : right1Middle3 6 3 = rowColumnMul HexagonRowColumn363.rows_inverseACB HexagonRowColumn363.cols_right0 := by
  funext r
  fin_cases r
  · exact right1Middle3_eq_case_6_3_row_0_0_0
  · exact right1Middle3_eq_case_6_3_row_0_0_1
  · exact right1Middle3_eq_case_6_3_row_0_0_2
  · exact right1Middle3_eq_case_6_3_row_0_0_3
  · exact right1Middle3_eq_case_6_3_row_0_1_0
  · exact right1Middle3_eq_case_6_3_row_0_1_1
  · exact right1Middle3_eq_case_6_3_row_0_1_2
  · exact right1Middle3_eq_case_6_3_row_0_1_3
  · exact right1Middle3_eq_case_6_3_row_1_0_0
  · exact right1Middle3_eq_case_6_3_row_1_0_1
  · exact right1Middle3_eq_case_6_3_row_1_0_2
  · exact right1Middle3_eq_case_6_3_row_1_0_3
  · exact right1Middle3_eq_case_6_3_row_1_1_0
  · exact right1Middle3_eq_case_6_3_row_1_1_1
  · exact right1Middle3_eq_case_6_3_row_1_1_2
  · exact right1Middle3_eq_case_6_3_row_1_1_3
  · exact right1Middle3_eq_case_6_3_row_2_0_0
  · exact right1Middle3_eq_case_6_3_row_2_0_1
  · exact right1Middle3_eq_case_6_3_row_2_0_2
  · exact right1Middle3_eq_case_6_3_row_2_0_3
  · exact right1Middle3_eq_case_6_3_row_2_1_0
  · exact right1Middle3_eq_case_6_3_row_2_1_1
  · exact right1Middle3_eq_case_6_3_row_2_1_2
  · exact right1Middle3_eq_case_6_3_row_2_1_3
  · exact right1Middle3_eq_case_6_3_row_3_0_0
  · exact right1Middle3_eq_case_6_3_row_3_0_1
  · exact right1Middle3_eq_case_6_3_row_3_0_2
  · exact right1Middle3_eq_case_6_3_row_3_0_3
  · exact right1Middle3_eq_case_6_3_row_3_1_0
  · exact right1Middle3_eq_case_6_3_row_3_1_1
  · exact right1Middle3_eq_case_6_3_row_3_1_2
  · exact right1Middle3_eq_case_6_3_row_3_1_3

set_option backward.isDefEq.respectTransparency false in
theorem right1Middle3_eq_case_6_3 : right1Middle3 6 3 = associatorInverseZ 3 3 6 * right0Middle3 6 3 := by
  simpa only [HexagonAtoms363.assocABC_eq,
    HexagonAtoms363.outerABC_eq,
    HexagonAtoms363.assocBAC_eq,
    HexagonAtoms363.innerABC_eq,
    HexagonAtoms363.innerRightABC_eq,
    HexagonAtoms363.inverseACB_eq,
    HexagonAtoms363.innerACB_eq,
    HexagonAtoms363.assocBCA_eq,
    HexagonAtoms363.innerRightBAC_eq,
    HexagonAtoms363.assocCAB_eq,
    HexagonAtoms363.outerLeftABC_eq,
    HexagonRowColumn363.assocBCA_alias,
    HexagonRowColumn363.product0_eq,
    HexagonRowColumn363.product1_eq,
    HexagonRowColumn363.product2_eq,
    HexagonRowColumn363.product3_eq,
    HexagonRowColumn363.product4_eq,
    HexagonRowColumn363.product5_eq,
    HexagonRowColumn363.product6_eq,
    HexagonRowColumn363.product7_eq] using right1Middle3_eq_case_6_3_checked

private theorem right2Middle3_eq_case_6_3_row_0_0_0 : (right2Middle3 6 3) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn363.rows_innerACB HexagonRowColumn363.cols_right1) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_6_3_row_0_0_1 : (right2Middle3 6 3) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn363.rows_innerACB HexagonRowColumn363.cols_right1) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_6_3_row_0_0_2 : (right2Middle3 6 3) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn363.rows_innerACB HexagonRowColumn363.cols_right1) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_6_3_row_0_0_3 : (right2Middle3 6 3) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn363.rows_innerACB HexagonRowColumn363.cols_right1) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_6_3_row_0_1_0 : (right2Middle3 6 3) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn363.rows_innerACB HexagonRowColumn363.cols_right1) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_6_3_row_0_1_1 : (right2Middle3 6 3) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn363.rows_innerACB HexagonRowColumn363.cols_right1) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_6_3_row_0_1_2 : (right2Middle3 6 3) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn363.rows_innerACB HexagonRowColumn363.cols_right1) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_6_3_row_0_1_3 : (right2Middle3 6 3) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn363.rows_innerACB HexagonRowColumn363.cols_right1) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_6_3_row_1_0_0 : (right2Middle3 6 3) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn363.rows_innerACB HexagonRowColumn363.cols_right1) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_6_3_row_1_0_1 : (right2Middle3 6 3) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn363.rows_innerACB HexagonRowColumn363.cols_right1) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_6_3_row_1_0_2 : (right2Middle3 6 3) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn363.rows_innerACB HexagonRowColumn363.cols_right1) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_6_3_row_1_0_3 : (right2Middle3 6 3) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn363.rows_innerACB HexagonRowColumn363.cols_right1) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_6_3_row_1_1_0 : (right2Middle3 6 3) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn363.rows_innerACB HexagonRowColumn363.cols_right1) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_6_3_row_1_1_1 : (right2Middle3 6 3) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn363.rows_innerACB HexagonRowColumn363.cols_right1) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_6_3_row_1_1_2 : (right2Middle3 6 3) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn363.rows_innerACB HexagonRowColumn363.cols_right1) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_6_3_row_1_1_3 : (right2Middle3 6 3) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn363.rows_innerACB HexagonRowColumn363.cols_right1) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_6_3_row_2_0_0 : (right2Middle3 6 3) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn363.rows_innerACB HexagonRowColumn363.cols_right1) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_6_3_row_2_0_1 : (right2Middle3 6 3) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn363.rows_innerACB HexagonRowColumn363.cols_right1) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_6_3_row_2_0_2 : (right2Middle3 6 3) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn363.rows_innerACB HexagonRowColumn363.cols_right1) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_6_3_row_2_0_3 : (right2Middle3 6 3) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn363.rows_innerACB HexagonRowColumn363.cols_right1) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_6_3_row_2_1_0 : (right2Middle3 6 3) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn363.rows_innerACB HexagonRowColumn363.cols_right1) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_6_3_row_2_1_1 : (right2Middle3 6 3) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn363.rows_innerACB HexagonRowColumn363.cols_right1) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_6_3_row_2_1_2 : (right2Middle3 6 3) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn363.rows_innerACB HexagonRowColumn363.cols_right1) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_6_3_row_2_1_3 : (right2Middle3 6 3) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn363.rows_innerACB HexagonRowColumn363.cols_right1) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_6_3_row_3_0_0 : (right2Middle3 6 3) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn363.rows_innerACB HexagonRowColumn363.cols_right1) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_6_3_row_3_0_1 : (right2Middle3 6 3) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn363.rows_innerACB HexagonRowColumn363.cols_right1) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_6_3_row_3_0_2 : (right2Middle3 6 3) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn363.rows_innerACB HexagonRowColumn363.cols_right1) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_6_3_row_3_0_3 : (right2Middle3 6 3) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn363.rows_innerACB HexagonRowColumn363.cols_right1) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_6_3_row_3_1_0 : (right2Middle3 6 3) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn363.rows_innerACB HexagonRowColumn363.cols_right1) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_6_3_row_3_1_1 : (right2Middle3 6 3) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn363.rows_innerACB HexagonRowColumn363.cols_right1) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_6_3_row_3_1_2 : (right2Middle3 6 3) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn363.rows_innerACB HexagonRowColumn363.cols_right1) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_6_3_row_3_1_3 : (right2Middle3 6 3) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn363.rows_innerACB HexagonRowColumn363.cols_right1) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_6_3_checked : right2Middle3 6 3 = rowColumnMul HexagonRowColumn363.rows_innerACB HexagonRowColumn363.cols_right1 := by
  funext r
  fin_cases r
  · exact right2Middle3_eq_case_6_3_row_0_0_0
  · exact right2Middle3_eq_case_6_3_row_0_0_1
  · exact right2Middle3_eq_case_6_3_row_0_0_2
  · exact right2Middle3_eq_case_6_3_row_0_0_3
  · exact right2Middle3_eq_case_6_3_row_0_1_0
  · exact right2Middle3_eq_case_6_3_row_0_1_1
  · exact right2Middle3_eq_case_6_3_row_0_1_2
  · exact right2Middle3_eq_case_6_3_row_0_1_3
  · exact right2Middle3_eq_case_6_3_row_1_0_0
  · exact right2Middle3_eq_case_6_3_row_1_0_1
  · exact right2Middle3_eq_case_6_3_row_1_0_2
  · exact right2Middle3_eq_case_6_3_row_1_0_3
  · exact right2Middle3_eq_case_6_3_row_1_1_0
  · exact right2Middle3_eq_case_6_3_row_1_1_1
  · exact right2Middle3_eq_case_6_3_row_1_1_2
  · exact right2Middle3_eq_case_6_3_row_1_1_3
  · exact right2Middle3_eq_case_6_3_row_2_0_0
  · exact right2Middle3_eq_case_6_3_row_2_0_1
  · exact right2Middle3_eq_case_6_3_row_2_0_2
  · exact right2Middle3_eq_case_6_3_row_2_0_3
  · exact right2Middle3_eq_case_6_3_row_2_1_0
  · exact right2Middle3_eq_case_6_3_row_2_1_1
  · exact right2Middle3_eq_case_6_3_row_2_1_2
  · exact right2Middle3_eq_case_6_3_row_2_1_3
  · exact right2Middle3_eq_case_6_3_row_3_0_0
  · exact right2Middle3_eq_case_6_3_row_3_0_1
  · exact right2Middle3_eq_case_6_3_row_3_0_2
  · exact right2Middle3_eq_case_6_3_row_3_0_3
  · exact right2Middle3_eq_case_6_3_row_3_1_0
  · exact right2Middle3_eq_case_6_3_row_3_1_1
  · exact right2Middle3_eq_case_6_3_row_3_1_2
  · exact right2Middle3_eq_case_6_3_row_3_1_3

set_option backward.isDefEq.respectTransparency false in
theorem right2Middle3_eq_case_6_3 : right2Middle3 6 3 = innerLeftZ 3 3 6 * right1Middle3 6 3 := by
  simpa only [HexagonAtoms363.assocABC_eq,
    HexagonAtoms363.outerABC_eq,
    HexagonAtoms363.assocBAC_eq,
    HexagonAtoms363.innerABC_eq,
    HexagonAtoms363.innerRightABC_eq,
    HexagonAtoms363.inverseACB_eq,
    HexagonAtoms363.innerACB_eq,
    HexagonAtoms363.assocBCA_eq,
    HexagonAtoms363.innerRightBAC_eq,
    HexagonAtoms363.assocCAB_eq,
    HexagonAtoms363.outerLeftABC_eq,
    HexagonRowColumn363.assocBCA_alias,
    HexagonRowColumn363.product0_eq,
    HexagonRowColumn363.product1_eq,
    HexagonRowColumn363.product2_eq,
    HexagonRowColumn363.product3_eq,
    HexagonRowColumn363.product4_eq,
    HexagonRowColumn363.product5_eq,
    HexagonRowColumn363.product6_eq,
    HexagonRowColumn363.product7_eq] using right2Middle3_eq_case_6_3_checked

private theorem leftFinal3_case_6_3_row_0_0_0 : (((-1 : ℤ) ^ (leftScaleBit 3 6 3).val * positiveScale (leftScaleExponent 3 6 3)) •
      (rowColumnMul HexagonRowColumn363.rows_assocBAC HexagonRowColumn363.cols_left0)) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 3 6 3) • (rowColumnMul HexagonRowColumn363.rows_innerRightBAC HexagonRowColumn363.cols_left1)) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal3_case_6_3_row_0_0_1 : (((-1 : ℤ) ^ (leftScaleBit 3 6 3).val * positiveScale (leftScaleExponent 3 6 3)) •
      (rowColumnMul HexagonRowColumn363.rows_assocBAC HexagonRowColumn363.cols_left0)) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 3 6 3) • (rowColumnMul HexagonRowColumn363.rows_innerRightBAC HexagonRowColumn363.cols_left1)) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal3_case_6_3_row_0_0_2 : (((-1 : ℤ) ^ (leftScaleBit 3 6 3).val * positiveScale (leftScaleExponent 3 6 3)) •
      (rowColumnMul HexagonRowColumn363.rows_assocBAC HexagonRowColumn363.cols_left0)) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 3 6 3) • (rowColumnMul HexagonRowColumn363.rows_innerRightBAC HexagonRowColumn363.cols_left1)) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal3_case_6_3_row_0_0_3 : (((-1 : ℤ) ^ (leftScaleBit 3 6 3).val * positiveScale (leftScaleExponent 3 6 3)) •
      (rowColumnMul HexagonRowColumn363.rows_assocBAC HexagonRowColumn363.cols_left0)) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 3 6 3) • (rowColumnMul HexagonRowColumn363.rows_innerRightBAC HexagonRowColumn363.cols_left1)) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal3_case_6_3_row_0_1_0 : (((-1 : ℤ) ^ (leftScaleBit 3 6 3).val * positiveScale (leftScaleExponent 3 6 3)) •
      (rowColumnMul HexagonRowColumn363.rows_assocBAC HexagonRowColumn363.cols_left0)) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 3 6 3) • (rowColumnMul HexagonRowColumn363.rows_innerRightBAC HexagonRowColumn363.cols_left1)) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal3_case_6_3_row_0_1_1 : (((-1 : ℤ) ^ (leftScaleBit 3 6 3).val * positiveScale (leftScaleExponent 3 6 3)) •
      (rowColumnMul HexagonRowColumn363.rows_assocBAC HexagonRowColumn363.cols_left0)) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 3 6 3) • (rowColumnMul HexagonRowColumn363.rows_innerRightBAC HexagonRowColumn363.cols_left1)) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal3_case_6_3_row_0_1_2 : (((-1 : ℤ) ^ (leftScaleBit 3 6 3).val * positiveScale (leftScaleExponent 3 6 3)) •
      (rowColumnMul HexagonRowColumn363.rows_assocBAC HexagonRowColumn363.cols_left0)) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 3 6 3) • (rowColumnMul HexagonRowColumn363.rows_innerRightBAC HexagonRowColumn363.cols_left1)) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal3_case_6_3_row_0_1_3 : (((-1 : ℤ) ^ (leftScaleBit 3 6 3).val * positiveScale (leftScaleExponent 3 6 3)) •
      (rowColumnMul HexagonRowColumn363.rows_assocBAC HexagonRowColumn363.cols_left0)) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 3 6 3) • (rowColumnMul HexagonRowColumn363.rows_innerRightBAC HexagonRowColumn363.cols_left1)) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal3_case_6_3_row_1_0_0 : (((-1 : ℤ) ^ (leftScaleBit 3 6 3).val * positiveScale (leftScaleExponent 3 6 3)) •
      (rowColumnMul HexagonRowColumn363.rows_assocBAC HexagonRowColumn363.cols_left0)) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 3 6 3) • (rowColumnMul HexagonRowColumn363.rows_innerRightBAC HexagonRowColumn363.cols_left1)) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal3_case_6_3_row_1_0_1 : (((-1 : ℤ) ^ (leftScaleBit 3 6 3).val * positiveScale (leftScaleExponent 3 6 3)) •
      (rowColumnMul HexagonRowColumn363.rows_assocBAC HexagonRowColumn363.cols_left0)) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 3 6 3) • (rowColumnMul HexagonRowColumn363.rows_innerRightBAC HexagonRowColumn363.cols_left1)) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal3_case_6_3_row_1_0_2 : (((-1 : ℤ) ^ (leftScaleBit 3 6 3).val * positiveScale (leftScaleExponent 3 6 3)) •
      (rowColumnMul HexagonRowColumn363.rows_assocBAC HexagonRowColumn363.cols_left0)) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 3 6 3) • (rowColumnMul HexagonRowColumn363.rows_innerRightBAC HexagonRowColumn363.cols_left1)) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal3_case_6_3_row_1_0_3 : (((-1 : ℤ) ^ (leftScaleBit 3 6 3).val * positiveScale (leftScaleExponent 3 6 3)) •
      (rowColumnMul HexagonRowColumn363.rows_assocBAC HexagonRowColumn363.cols_left0)) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 3 6 3) • (rowColumnMul HexagonRowColumn363.rows_innerRightBAC HexagonRowColumn363.cols_left1)) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal3_case_6_3_row_1_1_0 : (((-1 : ℤ) ^ (leftScaleBit 3 6 3).val * positiveScale (leftScaleExponent 3 6 3)) •
      (rowColumnMul HexagonRowColumn363.rows_assocBAC HexagonRowColumn363.cols_left0)) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 3 6 3) • (rowColumnMul HexagonRowColumn363.rows_innerRightBAC HexagonRowColumn363.cols_left1)) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal3_case_6_3_row_1_1_1 : (((-1 : ℤ) ^ (leftScaleBit 3 6 3).val * positiveScale (leftScaleExponent 3 6 3)) •
      (rowColumnMul HexagonRowColumn363.rows_assocBAC HexagonRowColumn363.cols_left0)) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 3 6 3) • (rowColumnMul HexagonRowColumn363.rows_innerRightBAC HexagonRowColumn363.cols_left1)) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal3_case_6_3_row_1_1_2 : (((-1 : ℤ) ^ (leftScaleBit 3 6 3).val * positiveScale (leftScaleExponent 3 6 3)) •
      (rowColumnMul HexagonRowColumn363.rows_assocBAC HexagonRowColumn363.cols_left0)) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 3 6 3) • (rowColumnMul HexagonRowColumn363.rows_innerRightBAC HexagonRowColumn363.cols_left1)) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal3_case_6_3_row_1_1_3 : (((-1 : ℤ) ^ (leftScaleBit 3 6 3).val * positiveScale (leftScaleExponent 3 6 3)) •
      (rowColumnMul HexagonRowColumn363.rows_assocBAC HexagonRowColumn363.cols_left0)) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 3 6 3) • (rowColumnMul HexagonRowColumn363.rows_innerRightBAC HexagonRowColumn363.cols_left1)) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal3_case_6_3_row_2_0_0 : (((-1 : ℤ) ^ (leftScaleBit 3 6 3).val * positiveScale (leftScaleExponent 3 6 3)) •
      (rowColumnMul HexagonRowColumn363.rows_assocBAC HexagonRowColumn363.cols_left0)) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 3 6 3) • (rowColumnMul HexagonRowColumn363.rows_innerRightBAC HexagonRowColumn363.cols_left1)) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal3_case_6_3_row_2_0_1 : (((-1 : ℤ) ^ (leftScaleBit 3 6 3).val * positiveScale (leftScaleExponent 3 6 3)) •
      (rowColumnMul HexagonRowColumn363.rows_assocBAC HexagonRowColumn363.cols_left0)) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 3 6 3) • (rowColumnMul HexagonRowColumn363.rows_innerRightBAC HexagonRowColumn363.cols_left1)) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal3_case_6_3_row_2_0_2 : (((-1 : ℤ) ^ (leftScaleBit 3 6 3).val * positiveScale (leftScaleExponent 3 6 3)) •
      (rowColumnMul HexagonRowColumn363.rows_assocBAC HexagonRowColumn363.cols_left0)) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 3 6 3) • (rowColumnMul HexagonRowColumn363.rows_innerRightBAC HexagonRowColumn363.cols_left1)) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal3_case_6_3_row_2_0_3 : (((-1 : ℤ) ^ (leftScaleBit 3 6 3).val * positiveScale (leftScaleExponent 3 6 3)) •
      (rowColumnMul HexagonRowColumn363.rows_assocBAC HexagonRowColumn363.cols_left0)) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 3 6 3) • (rowColumnMul HexagonRowColumn363.rows_innerRightBAC HexagonRowColumn363.cols_left1)) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal3_case_6_3_row_2_1_0 : (((-1 : ℤ) ^ (leftScaleBit 3 6 3).val * positiveScale (leftScaleExponent 3 6 3)) •
      (rowColumnMul HexagonRowColumn363.rows_assocBAC HexagonRowColumn363.cols_left0)) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 3 6 3) • (rowColumnMul HexagonRowColumn363.rows_innerRightBAC HexagonRowColumn363.cols_left1)) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal3_case_6_3_row_2_1_1 : (((-1 : ℤ) ^ (leftScaleBit 3 6 3).val * positiveScale (leftScaleExponent 3 6 3)) •
      (rowColumnMul HexagonRowColumn363.rows_assocBAC HexagonRowColumn363.cols_left0)) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 3 6 3) • (rowColumnMul HexagonRowColumn363.rows_innerRightBAC HexagonRowColumn363.cols_left1)) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal3_case_6_3_row_2_1_2 : (((-1 : ℤ) ^ (leftScaleBit 3 6 3).val * positiveScale (leftScaleExponent 3 6 3)) •
      (rowColumnMul HexagonRowColumn363.rows_assocBAC HexagonRowColumn363.cols_left0)) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 3 6 3) • (rowColumnMul HexagonRowColumn363.rows_innerRightBAC HexagonRowColumn363.cols_left1)) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal3_case_6_3_row_2_1_3 : (((-1 : ℤ) ^ (leftScaleBit 3 6 3).val * positiveScale (leftScaleExponent 3 6 3)) •
      (rowColumnMul HexagonRowColumn363.rows_assocBAC HexagonRowColumn363.cols_left0)) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 3 6 3) • (rowColumnMul HexagonRowColumn363.rows_innerRightBAC HexagonRowColumn363.cols_left1)) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal3_case_6_3_row_3_0_0 : (((-1 : ℤ) ^ (leftScaleBit 3 6 3).val * positiveScale (leftScaleExponent 3 6 3)) •
      (rowColumnMul HexagonRowColumn363.rows_assocBAC HexagonRowColumn363.cols_left0)) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 3 6 3) • (rowColumnMul HexagonRowColumn363.rows_innerRightBAC HexagonRowColumn363.cols_left1)) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal3_case_6_3_row_3_0_1 : (((-1 : ℤ) ^ (leftScaleBit 3 6 3).val * positiveScale (leftScaleExponent 3 6 3)) •
      (rowColumnMul HexagonRowColumn363.rows_assocBAC HexagonRowColumn363.cols_left0)) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 3 6 3) • (rowColumnMul HexagonRowColumn363.rows_innerRightBAC HexagonRowColumn363.cols_left1)) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal3_case_6_3_row_3_0_2 : (((-1 : ℤ) ^ (leftScaleBit 3 6 3).val * positiveScale (leftScaleExponent 3 6 3)) •
      (rowColumnMul HexagonRowColumn363.rows_assocBAC HexagonRowColumn363.cols_left0)) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 3 6 3) • (rowColumnMul HexagonRowColumn363.rows_innerRightBAC HexagonRowColumn363.cols_left1)) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal3_case_6_3_row_3_0_3 : (((-1 : ℤ) ^ (leftScaleBit 3 6 3).val * positiveScale (leftScaleExponent 3 6 3)) •
      (rowColumnMul HexagonRowColumn363.rows_assocBAC HexagonRowColumn363.cols_left0)) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 3 6 3) • (rowColumnMul HexagonRowColumn363.rows_innerRightBAC HexagonRowColumn363.cols_left1)) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal3_case_6_3_row_3_1_0 : (((-1 : ℤ) ^ (leftScaleBit 3 6 3).val * positiveScale (leftScaleExponent 3 6 3)) •
      (rowColumnMul HexagonRowColumn363.rows_assocBAC HexagonRowColumn363.cols_left0)) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 3 6 3) • (rowColumnMul HexagonRowColumn363.rows_innerRightBAC HexagonRowColumn363.cols_left1)) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal3_case_6_3_row_3_1_1 : (((-1 : ℤ) ^ (leftScaleBit 3 6 3).val * positiveScale (leftScaleExponent 3 6 3)) •
      (rowColumnMul HexagonRowColumn363.rows_assocBAC HexagonRowColumn363.cols_left0)) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 3 6 3) • (rowColumnMul HexagonRowColumn363.rows_innerRightBAC HexagonRowColumn363.cols_left1)) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal3_case_6_3_row_3_1_2 : (((-1 : ℤ) ^ (leftScaleBit 3 6 3).val * positiveScale (leftScaleExponent 3 6 3)) •
      (rowColumnMul HexagonRowColumn363.rows_assocBAC HexagonRowColumn363.cols_left0)) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 3 6 3) • (rowColumnMul HexagonRowColumn363.rows_innerRightBAC HexagonRowColumn363.cols_left1)) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal3_case_6_3_row_3_1_3 : (((-1 : ℤ) ^ (leftScaleBit 3 6 3).val * positiveScale (leftScaleExponent 3 6 3)) •
      (rowColumnMul HexagonRowColumn363.rows_assocBAC HexagonRowColumn363.cols_left0)) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 3 6 3) • (rowColumnMul HexagonRowColumn363.rows_innerRightBAC HexagonRowColumn363.cols_left1)) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal3_case_6_3_checked : ((-1 : ℤ) ^ (leftScaleBit 3 6 3).val * positiveScale (leftScaleExponent 3 6 3)) •
      (rowColumnMul HexagonRowColumn363.rows_assocBAC HexagonRowColumn363.cols_left0) = negativeScale (leftScaleExponent 3 6 3) • (rowColumnMul HexagonRowColumn363.rows_innerRightBAC HexagonRowColumn363.cols_left1) := by
  funext r
  fin_cases r
  · exact leftFinal3_case_6_3_row_0_0_0
  · exact leftFinal3_case_6_3_row_0_0_1
  · exact leftFinal3_case_6_3_row_0_0_2
  · exact leftFinal3_case_6_3_row_0_0_3
  · exact leftFinal3_case_6_3_row_0_1_0
  · exact leftFinal3_case_6_3_row_0_1_1
  · exact leftFinal3_case_6_3_row_0_1_2
  · exact leftFinal3_case_6_3_row_0_1_3
  · exact leftFinal3_case_6_3_row_1_0_0
  · exact leftFinal3_case_6_3_row_1_0_1
  · exact leftFinal3_case_6_3_row_1_0_2
  · exact leftFinal3_case_6_3_row_1_0_3
  · exact leftFinal3_case_6_3_row_1_1_0
  · exact leftFinal3_case_6_3_row_1_1_1
  · exact leftFinal3_case_6_3_row_1_1_2
  · exact leftFinal3_case_6_3_row_1_1_3
  · exact leftFinal3_case_6_3_row_2_0_0
  · exact leftFinal3_case_6_3_row_2_0_1
  · exact leftFinal3_case_6_3_row_2_0_2
  · exact leftFinal3_case_6_3_row_2_0_3
  · exact leftFinal3_case_6_3_row_2_1_0
  · exact leftFinal3_case_6_3_row_2_1_1
  · exact leftFinal3_case_6_3_row_2_1_2
  · exact leftFinal3_case_6_3_row_2_1_3
  · exact leftFinal3_case_6_3_row_3_0_0
  · exact leftFinal3_case_6_3_row_3_0_1
  · exact leftFinal3_case_6_3_row_3_0_2
  · exact leftFinal3_case_6_3_row_3_0_3
  · exact leftFinal3_case_6_3_row_3_1_0
  · exact leftFinal3_case_6_3_row_3_1_1
  · exact leftFinal3_case_6_3_row_3_1_2
  · exact leftFinal3_case_6_3_row_3_1_3

set_option backward.isDefEq.respectTransparency false in
theorem leftFinal3_case_6_3 : ((-1 : ℤ) ^ (leftScaleBit 3 6 3).val * positiveScale (leftScaleExponent 3 6 3)) •
      (associatorZ 6 3 3 * left0Middle3 6 3) = negativeScale (leftScaleExponent 3 6 3) • (innerRightZ 6 3 3 * left1Middle3 6 3) := by
  simpa only [HexagonAtoms363.assocABC_eq,
    HexagonAtoms363.outerABC_eq,
    HexagonAtoms363.assocBAC_eq,
    HexagonAtoms363.innerABC_eq,
    HexagonAtoms363.innerRightABC_eq,
    HexagonAtoms363.inverseACB_eq,
    HexagonAtoms363.innerACB_eq,
    HexagonAtoms363.assocBCA_eq,
    HexagonAtoms363.innerRightBAC_eq,
    HexagonAtoms363.assocCAB_eq,
    HexagonAtoms363.outerLeftABC_eq,
    HexagonRowColumn363.assocBCA_alias,
    HexagonRowColumn363.product0_eq,
    HexagonRowColumn363.product1_eq,
    HexagonRowColumn363.product2_eq,
    HexagonRowColumn363.product3_eq,
    HexagonRowColumn363.product4_eq,
    HexagonRowColumn363.product5_eq,
    HexagonRowColumn363.product6_eq,
    HexagonRowColumn363.product7_eq] using leftFinal3_case_6_3_checked

private theorem rightFinal3_case_6_3_row_0_0_0 : (((-1 : ℤ) ^ (rightScaleBit 3 6 3).val * positiveScale (rightScaleExponent 3 6 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 3 6 : ℤ)) • HexagonAtoms363.outerLeftABC) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 3 6 3) • (rowColumnMul HexagonRowColumn363.rows_assocCAB HexagonRowColumn363.cols_right2)) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal3_case_6_3_row_0_0_1 : (((-1 : ℤ) ^ (rightScaleBit 3 6 3).val * positiveScale (rightScaleExponent 3 6 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 3 6 : ℤ)) • HexagonAtoms363.outerLeftABC) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 3 6 3) • (rowColumnMul HexagonRowColumn363.rows_assocCAB HexagonRowColumn363.cols_right2)) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal3_case_6_3_row_0_0_2 : (((-1 : ℤ) ^ (rightScaleBit 3 6 3).val * positiveScale (rightScaleExponent 3 6 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 3 6 : ℤ)) • HexagonAtoms363.outerLeftABC) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 3 6 3) • (rowColumnMul HexagonRowColumn363.rows_assocCAB HexagonRowColumn363.cols_right2)) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal3_case_6_3_row_0_0_3 : (((-1 : ℤ) ^ (rightScaleBit 3 6 3).val * positiveScale (rightScaleExponent 3 6 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 3 6 : ℤ)) • HexagonAtoms363.outerLeftABC) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 3 6 3) • (rowColumnMul HexagonRowColumn363.rows_assocCAB HexagonRowColumn363.cols_right2)) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal3_case_6_3_row_0_1_0 : (((-1 : ℤ) ^ (rightScaleBit 3 6 3).val * positiveScale (rightScaleExponent 3 6 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 3 6 : ℤ)) • HexagonAtoms363.outerLeftABC) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 3 6 3) • (rowColumnMul HexagonRowColumn363.rows_assocCAB HexagonRowColumn363.cols_right2)) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal3_case_6_3_row_0_1_1 : (((-1 : ℤ) ^ (rightScaleBit 3 6 3).val * positiveScale (rightScaleExponent 3 6 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 3 6 : ℤ)) • HexagonAtoms363.outerLeftABC) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 3 6 3) • (rowColumnMul HexagonRowColumn363.rows_assocCAB HexagonRowColumn363.cols_right2)) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal3_case_6_3_row_0_1_2 : (((-1 : ℤ) ^ (rightScaleBit 3 6 3).val * positiveScale (rightScaleExponent 3 6 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 3 6 : ℤ)) • HexagonAtoms363.outerLeftABC) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 3 6 3) • (rowColumnMul HexagonRowColumn363.rows_assocCAB HexagonRowColumn363.cols_right2)) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal3_case_6_3_row_0_1_3 : (((-1 : ℤ) ^ (rightScaleBit 3 6 3).val * positiveScale (rightScaleExponent 3 6 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 3 6 : ℤ)) • HexagonAtoms363.outerLeftABC) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 3 6 3) • (rowColumnMul HexagonRowColumn363.rows_assocCAB HexagonRowColumn363.cols_right2)) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal3_case_6_3_row_1_0_0 : (((-1 : ℤ) ^ (rightScaleBit 3 6 3).val * positiveScale (rightScaleExponent 3 6 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 3 6 : ℤ)) • HexagonAtoms363.outerLeftABC) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 3 6 3) • (rowColumnMul HexagonRowColumn363.rows_assocCAB HexagonRowColumn363.cols_right2)) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal3_case_6_3_row_1_0_1 : (((-1 : ℤ) ^ (rightScaleBit 3 6 3).val * positiveScale (rightScaleExponent 3 6 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 3 6 : ℤ)) • HexagonAtoms363.outerLeftABC) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 3 6 3) • (rowColumnMul HexagonRowColumn363.rows_assocCAB HexagonRowColumn363.cols_right2)) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal3_case_6_3_row_1_0_2 : (((-1 : ℤ) ^ (rightScaleBit 3 6 3).val * positiveScale (rightScaleExponent 3 6 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 3 6 : ℤ)) • HexagonAtoms363.outerLeftABC) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 3 6 3) • (rowColumnMul HexagonRowColumn363.rows_assocCAB HexagonRowColumn363.cols_right2)) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal3_case_6_3_row_1_0_3 : (((-1 : ℤ) ^ (rightScaleBit 3 6 3).val * positiveScale (rightScaleExponent 3 6 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 3 6 : ℤ)) • HexagonAtoms363.outerLeftABC) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 3 6 3) • (rowColumnMul HexagonRowColumn363.rows_assocCAB HexagonRowColumn363.cols_right2)) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal3_case_6_3_row_1_1_0 : (((-1 : ℤ) ^ (rightScaleBit 3 6 3).val * positiveScale (rightScaleExponent 3 6 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 3 6 : ℤ)) • HexagonAtoms363.outerLeftABC) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 3 6 3) • (rowColumnMul HexagonRowColumn363.rows_assocCAB HexagonRowColumn363.cols_right2)) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal3_case_6_3_row_1_1_1 : (((-1 : ℤ) ^ (rightScaleBit 3 6 3).val * positiveScale (rightScaleExponent 3 6 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 3 6 : ℤ)) • HexagonAtoms363.outerLeftABC) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 3 6 3) • (rowColumnMul HexagonRowColumn363.rows_assocCAB HexagonRowColumn363.cols_right2)) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal3_case_6_3_row_1_1_2 : (((-1 : ℤ) ^ (rightScaleBit 3 6 3).val * positiveScale (rightScaleExponent 3 6 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 3 6 : ℤ)) • HexagonAtoms363.outerLeftABC) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 3 6 3) • (rowColumnMul HexagonRowColumn363.rows_assocCAB HexagonRowColumn363.cols_right2)) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal3_case_6_3_row_1_1_3 : (((-1 : ℤ) ^ (rightScaleBit 3 6 3).val * positiveScale (rightScaleExponent 3 6 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 3 6 : ℤ)) • HexagonAtoms363.outerLeftABC) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 3 6 3) • (rowColumnMul HexagonRowColumn363.rows_assocCAB HexagonRowColumn363.cols_right2)) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal3_case_6_3_row_2_0_0 : (((-1 : ℤ) ^ (rightScaleBit 3 6 3).val * positiveScale (rightScaleExponent 3 6 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 3 6 : ℤ)) • HexagonAtoms363.outerLeftABC) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 3 6 3) • (rowColumnMul HexagonRowColumn363.rows_assocCAB HexagonRowColumn363.cols_right2)) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal3_case_6_3_row_2_0_1 : (((-1 : ℤ) ^ (rightScaleBit 3 6 3).val * positiveScale (rightScaleExponent 3 6 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 3 6 : ℤ)) • HexagonAtoms363.outerLeftABC) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 3 6 3) • (rowColumnMul HexagonRowColumn363.rows_assocCAB HexagonRowColumn363.cols_right2)) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal3_case_6_3_row_2_0_2 : (((-1 : ℤ) ^ (rightScaleBit 3 6 3).val * positiveScale (rightScaleExponent 3 6 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 3 6 : ℤ)) • HexagonAtoms363.outerLeftABC) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 3 6 3) • (rowColumnMul HexagonRowColumn363.rows_assocCAB HexagonRowColumn363.cols_right2)) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal3_case_6_3_row_2_0_3 : (((-1 : ℤ) ^ (rightScaleBit 3 6 3).val * positiveScale (rightScaleExponent 3 6 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 3 6 : ℤ)) • HexagonAtoms363.outerLeftABC) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 3 6 3) • (rowColumnMul HexagonRowColumn363.rows_assocCAB HexagonRowColumn363.cols_right2)) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal3_case_6_3_row_2_1_0 : (((-1 : ℤ) ^ (rightScaleBit 3 6 3).val * positiveScale (rightScaleExponent 3 6 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 3 6 : ℤ)) • HexagonAtoms363.outerLeftABC) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 3 6 3) • (rowColumnMul HexagonRowColumn363.rows_assocCAB HexagonRowColumn363.cols_right2)) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal3_case_6_3_row_2_1_1 : (((-1 : ℤ) ^ (rightScaleBit 3 6 3).val * positiveScale (rightScaleExponent 3 6 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 3 6 : ℤ)) • HexagonAtoms363.outerLeftABC) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 3 6 3) • (rowColumnMul HexagonRowColumn363.rows_assocCAB HexagonRowColumn363.cols_right2)) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal3_case_6_3_row_2_1_2 : (((-1 : ℤ) ^ (rightScaleBit 3 6 3).val * positiveScale (rightScaleExponent 3 6 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 3 6 : ℤ)) • HexagonAtoms363.outerLeftABC) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 3 6 3) • (rowColumnMul HexagonRowColumn363.rows_assocCAB HexagonRowColumn363.cols_right2)) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal3_case_6_3_row_2_1_3 : (((-1 : ℤ) ^ (rightScaleBit 3 6 3).val * positiveScale (rightScaleExponent 3 6 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 3 6 : ℤ)) • HexagonAtoms363.outerLeftABC) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 3 6 3) • (rowColumnMul HexagonRowColumn363.rows_assocCAB HexagonRowColumn363.cols_right2)) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal3_case_6_3_row_3_0_0 : (((-1 : ℤ) ^ (rightScaleBit 3 6 3).val * positiveScale (rightScaleExponent 3 6 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 3 6 : ℤ)) • HexagonAtoms363.outerLeftABC) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 3 6 3) • (rowColumnMul HexagonRowColumn363.rows_assocCAB HexagonRowColumn363.cols_right2)) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal3_case_6_3_row_3_0_1 : (((-1 : ℤ) ^ (rightScaleBit 3 6 3).val * positiveScale (rightScaleExponent 3 6 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 3 6 : ℤ)) • HexagonAtoms363.outerLeftABC) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 3 6 3) • (rowColumnMul HexagonRowColumn363.rows_assocCAB HexagonRowColumn363.cols_right2)) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal3_case_6_3_row_3_0_2 : (((-1 : ℤ) ^ (rightScaleBit 3 6 3).val * positiveScale (rightScaleExponent 3 6 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 3 6 : ℤ)) • HexagonAtoms363.outerLeftABC) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 3 6 3) • (rowColumnMul HexagonRowColumn363.rows_assocCAB HexagonRowColumn363.cols_right2)) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal3_case_6_3_row_3_0_3 : (((-1 : ℤ) ^ (rightScaleBit 3 6 3).val * positiveScale (rightScaleExponent 3 6 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 3 6 : ℤ)) • HexagonAtoms363.outerLeftABC) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 3 6 3) • (rowColumnMul HexagonRowColumn363.rows_assocCAB HexagonRowColumn363.cols_right2)) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal3_case_6_3_row_3_1_0 : (((-1 : ℤ) ^ (rightScaleBit 3 6 3).val * positiveScale (rightScaleExponent 3 6 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 3 6 : ℤ)) • HexagonAtoms363.outerLeftABC) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 3 6 3) • (rowColumnMul HexagonRowColumn363.rows_assocCAB HexagonRowColumn363.cols_right2)) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal3_case_6_3_row_3_1_1 : (((-1 : ℤ) ^ (rightScaleBit 3 6 3).val * positiveScale (rightScaleExponent 3 6 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 3 6 : ℤ)) • HexagonAtoms363.outerLeftABC) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 3 6 3) • (rowColumnMul HexagonRowColumn363.rows_assocCAB HexagonRowColumn363.cols_right2)) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal3_case_6_3_row_3_1_2 : (((-1 : ℤ) ^ (rightScaleBit 3 6 3).val * positiveScale (rightScaleExponent 3 6 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 3 6 : ℤ)) • HexagonAtoms363.outerLeftABC) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 3 6 3) • (rowColumnMul HexagonRowColumn363.rows_assocCAB HexagonRowColumn363.cols_right2)) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal3_case_6_3_row_3_1_3 : (((-1 : ℤ) ^ (rightScaleBit 3 6 3).val * positiveScale (rightScaleExponent 3 6 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 3 6 : ℤ)) • HexagonAtoms363.outerLeftABC) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 3 6 3) • (rowColumnMul HexagonRowColumn363.rows_assocCAB HexagonRowColumn363.cols_right2)) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal3_case_6_3_checked : ((-1 : ℤ) ^ (rightScaleBit 3 6 3).val * positiveScale (rightScaleExponent 3 6 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 3 6 : ℤ)) • HexagonAtoms363.outerLeftABC = negativeScale (rightScaleExponent 3 6 3) • (rowColumnMul HexagonRowColumn363.rows_assocCAB HexagonRowColumn363.cols_right2) := by
  funext r
  fin_cases r
  · exact rightFinal3_case_6_3_row_0_0_0
  · exact rightFinal3_case_6_3_row_0_0_1
  · exact rightFinal3_case_6_3_row_0_0_2
  · exact rightFinal3_case_6_3_row_0_0_3
  · exact rightFinal3_case_6_3_row_0_1_0
  · exact rightFinal3_case_6_3_row_0_1_1
  · exact rightFinal3_case_6_3_row_0_1_2
  · exact rightFinal3_case_6_3_row_0_1_3
  · exact rightFinal3_case_6_3_row_1_0_0
  · exact rightFinal3_case_6_3_row_1_0_1
  · exact rightFinal3_case_6_3_row_1_0_2
  · exact rightFinal3_case_6_3_row_1_0_3
  · exact rightFinal3_case_6_3_row_1_1_0
  · exact rightFinal3_case_6_3_row_1_1_1
  · exact rightFinal3_case_6_3_row_1_1_2
  · exact rightFinal3_case_6_3_row_1_1_3
  · exact rightFinal3_case_6_3_row_2_0_0
  · exact rightFinal3_case_6_3_row_2_0_1
  · exact rightFinal3_case_6_3_row_2_0_2
  · exact rightFinal3_case_6_3_row_2_0_3
  · exact rightFinal3_case_6_3_row_2_1_0
  · exact rightFinal3_case_6_3_row_2_1_1
  · exact rightFinal3_case_6_3_row_2_1_2
  · exact rightFinal3_case_6_3_row_2_1_3
  · exact rightFinal3_case_6_3_row_3_0_0
  · exact rightFinal3_case_6_3_row_3_0_1
  · exact rightFinal3_case_6_3_row_3_0_2
  · exact rightFinal3_case_6_3_row_3_0_3
  · exact rightFinal3_case_6_3_row_3_1_0
  · exact rightFinal3_case_6_3_row_3_1_1
  · exact rightFinal3_case_6_3_row_3_1_2
  · exact rightFinal3_case_6_3_row_3_1_3

set_option backward.isDefEq.respectTransparency false in
theorem rightFinal3_case_6_3 : ((-1 : ℤ) ^ (rightScaleBit 3 6 3).val * positiveScale (rightScaleExponent 3 6 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 3 6 : ℤ)) • outerLeftZ 3 6 3 = negativeScale (rightScaleExponent 3 6 3) • (associatorZ 3 3 6 * right2Middle3 6 3) := by
  simpa only [HexagonAtoms363.assocABC_eq,
    HexagonAtoms363.outerABC_eq,
    HexagonAtoms363.assocBAC_eq,
    HexagonAtoms363.innerABC_eq,
    HexagonAtoms363.innerRightABC_eq,
    HexagonAtoms363.inverseACB_eq,
    HexagonAtoms363.innerACB_eq,
    HexagonAtoms363.assocBCA_eq,
    HexagonAtoms363.innerRightBAC_eq,
    HexagonAtoms363.assocCAB_eq,
    HexagonAtoms363.outerLeftABC_eq,
    HexagonRowColumn363.assocBCA_alias,
    HexagonRowColumn363.product0_eq,
    HexagonRowColumn363.product1_eq,
    HexagonRowColumn363.product2_eq,
    HexagonRowColumn363.product3_eq,
    HexagonRowColumn363.product4_eq,
    HexagonRowColumn363.product5_eq,
    HexagonRowColumn363.product6_eq,
    HexagonRowColumn363.product7_eq] using rightFinal3_case_6_3_checked

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonCases3
