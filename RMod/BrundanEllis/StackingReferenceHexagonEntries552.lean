import RMod.BrundanEllis.StackingReferenceHexagonMiddle5
import RMod.BrundanEllis.StackingReferenceSparseMatrixCheck
import RMod.BrundanEllis.StackingReferenceHexagonAtoms552
import RMod.BrundanEllis.StackingReferenceHexagonRowColumn552

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

private theorem left0Middle5_eq_case_5_2_row_0_0_0 : (left0Middle5 5 2) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn552.rows_outerABC HexagonRowColumn552.cols_assocABC) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_5_2_row_0_0_1 : (left0Middle5 5 2) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn552.rows_outerABC HexagonRowColumn552.cols_assocABC) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_5_2_row_0_0_2 : (left0Middle5 5 2) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn552.rows_outerABC HexagonRowColumn552.cols_assocABC) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_5_2_row_0_0_3 : (left0Middle5 5 2) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn552.rows_outerABC HexagonRowColumn552.cols_assocABC) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_5_2_row_0_1_0 : (left0Middle5 5 2) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn552.rows_outerABC HexagonRowColumn552.cols_assocABC) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_5_2_row_0_1_1 : (left0Middle5 5 2) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn552.rows_outerABC HexagonRowColumn552.cols_assocABC) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_5_2_row_0_1_2 : (left0Middle5 5 2) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn552.rows_outerABC HexagonRowColumn552.cols_assocABC) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_5_2_row_0_1_3 : (left0Middle5 5 2) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn552.rows_outerABC HexagonRowColumn552.cols_assocABC) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_5_2_row_1_0_0 : (left0Middle5 5 2) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn552.rows_outerABC HexagonRowColumn552.cols_assocABC) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_5_2_row_1_0_1 : (left0Middle5 5 2) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn552.rows_outerABC HexagonRowColumn552.cols_assocABC) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_5_2_row_1_0_2 : (left0Middle5 5 2) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn552.rows_outerABC HexagonRowColumn552.cols_assocABC) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_5_2_row_1_0_3 : (left0Middle5 5 2) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn552.rows_outerABC HexagonRowColumn552.cols_assocABC) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_5_2_row_1_1_0 : (left0Middle5 5 2) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn552.rows_outerABC HexagonRowColumn552.cols_assocABC) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_5_2_row_1_1_1 : (left0Middle5 5 2) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn552.rows_outerABC HexagonRowColumn552.cols_assocABC) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_5_2_row_1_1_2 : (left0Middle5 5 2) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn552.rows_outerABC HexagonRowColumn552.cols_assocABC) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_5_2_row_1_1_3 : (left0Middle5 5 2) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn552.rows_outerABC HexagonRowColumn552.cols_assocABC) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_5_2_row_2_0_0 : (left0Middle5 5 2) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn552.rows_outerABC HexagonRowColumn552.cols_assocABC) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_5_2_row_2_0_1 : (left0Middle5 5 2) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn552.rows_outerABC HexagonRowColumn552.cols_assocABC) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_5_2_row_2_0_2 : (left0Middle5 5 2) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn552.rows_outerABC HexagonRowColumn552.cols_assocABC) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_5_2_row_2_0_3 : (left0Middle5 5 2) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn552.rows_outerABC HexagonRowColumn552.cols_assocABC) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_5_2_row_2_1_0 : (left0Middle5 5 2) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn552.rows_outerABC HexagonRowColumn552.cols_assocABC) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_5_2_row_2_1_1 : (left0Middle5 5 2) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn552.rows_outerABC HexagonRowColumn552.cols_assocABC) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_5_2_row_2_1_2 : (left0Middle5 5 2) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn552.rows_outerABC HexagonRowColumn552.cols_assocABC) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_5_2_row_2_1_3 : (left0Middle5 5 2) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn552.rows_outerABC HexagonRowColumn552.cols_assocABC) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_5_2_row_3_0_0 : (left0Middle5 5 2) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn552.rows_outerABC HexagonRowColumn552.cols_assocABC) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_5_2_row_3_0_1 : (left0Middle5 5 2) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn552.rows_outerABC HexagonRowColumn552.cols_assocABC) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_5_2_row_3_0_2 : (left0Middle5 5 2) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn552.rows_outerABC HexagonRowColumn552.cols_assocABC) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_5_2_row_3_0_3 : (left0Middle5 5 2) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn552.rows_outerABC HexagonRowColumn552.cols_assocABC) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_5_2_row_3_1_0 : (left0Middle5 5 2) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn552.rows_outerABC HexagonRowColumn552.cols_assocABC) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_5_2_row_3_1_1 : (left0Middle5 5 2) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn552.rows_outerABC HexagonRowColumn552.cols_assocABC) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_5_2_row_3_1_2 : (left0Middle5 5 2) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn552.rows_outerABC HexagonRowColumn552.cols_assocABC) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_5_2_row_3_1_3 : (left0Middle5 5 2) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn552.rows_outerABC HexagonRowColumn552.cols_assocABC) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_5_2_checked : left0Middle5 5 2 = rowColumnMul HexagonRowColumn552.rows_outerABC HexagonRowColumn552.cols_assocABC := by
  funext r
  fin_cases r
  · exact left0Middle5_eq_case_5_2_row_0_0_0
  · exact left0Middle5_eq_case_5_2_row_0_0_1
  · exact left0Middle5_eq_case_5_2_row_0_0_2
  · exact left0Middle5_eq_case_5_2_row_0_0_3
  · exact left0Middle5_eq_case_5_2_row_0_1_0
  · exact left0Middle5_eq_case_5_2_row_0_1_1
  · exact left0Middle5_eq_case_5_2_row_0_1_2
  · exact left0Middle5_eq_case_5_2_row_0_1_3
  · exact left0Middle5_eq_case_5_2_row_1_0_0
  · exact left0Middle5_eq_case_5_2_row_1_0_1
  · exact left0Middle5_eq_case_5_2_row_1_0_2
  · exact left0Middle5_eq_case_5_2_row_1_0_3
  · exact left0Middle5_eq_case_5_2_row_1_1_0
  · exact left0Middle5_eq_case_5_2_row_1_1_1
  · exact left0Middle5_eq_case_5_2_row_1_1_2
  · exact left0Middle5_eq_case_5_2_row_1_1_3
  · exact left0Middle5_eq_case_5_2_row_2_0_0
  · exact left0Middle5_eq_case_5_2_row_2_0_1
  · exact left0Middle5_eq_case_5_2_row_2_0_2
  · exact left0Middle5_eq_case_5_2_row_2_0_3
  · exact left0Middle5_eq_case_5_2_row_2_1_0
  · exact left0Middle5_eq_case_5_2_row_2_1_1
  · exact left0Middle5_eq_case_5_2_row_2_1_2
  · exact left0Middle5_eq_case_5_2_row_2_1_3
  · exact left0Middle5_eq_case_5_2_row_3_0_0
  · exact left0Middle5_eq_case_5_2_row_3_0_1
  · exact left0Middle5_eq_case_5_2_row_3_0_2
  · exact left0Middle5_eq_case_5_2_row_3_0_3
  · exact left0Middle5_eq_case_5_2_row_3_1_0
  · exact left0Middle5_eq_case_5_2_row_3_1_1
  · exact left0Middle5_eq_case_5_2_row_3_1_2
  · exact left0Middle5_eq_case_5_2_row_3_1_3

set_option backward.isDefEq.respectTransparency false in
theorem left0Middle5_eq_case_5_2 : left0Middle5 5 2 = outerRightZ 5 5 2 * associatorZ 5 5 2 := by
  simpa only [HexagonAtoms552.assocABC_eq,
    HexagonAtoms552.outerABC_eq,
    HexagonAtoms552.assocBAC_eq,
    HexagonAtoms552.innerABC_eq,
    HexagonAtoms552.innerRightABC_eq,
    HexagonAtoms552.inverseACB_eq,
    HexagonAtoms552.innerACB_eq,
    HexagonAtoms552.assocBCA_eq,
    HexagonAtoms552.innerRightBAC_eq,
    HexagonAtoms552.assocCAB_eq,
    HexagonAtoms552.outerLeftABC_eq,
    HexagonRowColumn552.assocBAC_alias,
    HexagonRowColumn552.innerRightBAC_alias,
    HexagonRowColumn552.product0_eq,
    HexagonRowColumn552.product1_eq,
    HexagonRowColumn552.product2_eq,
    HexagonRowColumn552.product3_eq,
    HexagonRowColumn552.product4_eq,
    HexagonRowColumn552.product5_eq,
    HexagonRowColumn552.product6_eq,
    HexagonRowColumn552.product7_eq] using left0Middle5_eq_case_5_2_checked

private theorem left1Middle5_eq_case_5_2_row_0_0_0 : (left1Middle5 5 2) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn552.rows_assocABC HexagonRowColumn552.cols_innerABC) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_5_2_row_0_0_1 : (left1Middle5 5 2) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn552.rows_assocABC HexagonRowColumn552.cols_innerABC) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_5_2_row_0_0_2 : (left1Middle5 5 2) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn552.rows_assocABC HexagonRowColumn552.cols_innerABC) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_5_2_row_0_0_3 : (left1Middle5 5 2) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn552.rows_assocABC HexagonRowColumn552.cols_innerABC) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_5_2_row_0_1_0 : (left1Middle5 5 2) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn552.rows_assocABC HexagonRowColumn552.cols_innerABC) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_5_2_row_0_1_1 : (left1Middle5 5 2) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn552.rows_assocABC HexagonRowColumn552.cols_innerABC) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_5_2_row_0_1_2 : (left1Middle5 5 2) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn552.rows_assocABC HexagonRowColumn552.cols_innerABC) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_5_2_row_0_1_3 : (left1Middle5 5 2) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn552.rows_assocABC HexagonRowColumn552.cols_innerABC) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_5_2_row_1_0_0 : (left1Middle5 5 2) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn552.rows_assocABC HexagonRowColumn552.cols_innerABC) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_5_2_row_1_0_1 : (left1Middle5 5 2) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn552.rows_assocABC HexagonRowColumn552.cols_innerABC) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_5_2_row_1_0_2 : (left1Middle5 5 2) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn552.rows_assocABC HexagonRowColumn552.cols_innerABC) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_5_2_row_1_0_3 : (left1Middle5 5 2) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn552.rows_assocABC HexagonRowColumn552.cols_innerABC) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_5_2_row_1_1_0 : (left1Middle5 5 2) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn552.rows_assocABC HexagonRowColumn552.cols_innerABC) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_5_2_row_1_1_1 : (left1Middle5 5 2) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn552.rows_assocABC HexagonRowColumn552.cols_innerABC) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_5_2_row_1_1_2 : (left1Middle5 5 2) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn552.rows_assocABC HexagonRowColumn552.cols_innerABC) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_5_2_row_1_1_3 : (left1Middle5 5 2) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn552.rows_assocABC HexagonRowColumn552.cols_innerABC) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_5_2_row_2_0_0 : (left1Middle5 5 2) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn552.rows_assocABC HexagonRowColumn552.cols_innerABC) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_5_2_row_2_0_1 : (left1Middle5 5 2) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn552.rows_assocABC HexagonRowColumn552.cols_innerABC) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_5_2_row_2_0_2 : (left1Middle5 5 2) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn552.rows_assocABC HexagonRowColumn552.cols_innerABC) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_5_2_row_2_0_3 : (left1Middle5 5 2) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn552.rows_assocABC HexagonRowColumn552.cols_innerABC) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_5_2_row_2_1_0 : (left1Middle5 5 2) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn552.rows_assocABC HexagonRowColumn552.cols_innerABC) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_5_2_row_2_1_1 : (left1Middle5 5 2) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn552.rows_assocABC HexagonRowColumn552.cols_innerABC) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_5_2_row_2_1_2 : (left1Middle5 5 2) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn552.rows_assocABC HexagonRowColumn552.cols_innerABC) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_5_2_row_2_1_3 : (left1Middle5 5 2) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn552.rows_assocABC HexagonRowColumn552.cols_innerABC) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_5_2_row_3_0_0 : (left1Middle5 5 2) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn552.rows_assocABC HexagonRowColumn552.cols_innerABC) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_5_2_row_3_0_1 : (left1Middle5 5 2) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn552.rows_assocABC HexagonRowColumn552.cols_innerABC) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_5_2_row_3_0_2 : (left1Middle5 5 2) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn552.rows_assocABC HexagonRowColumn552.cols_innerABC) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_5_2_row_3_0_3 : (left1Middle5 5 2) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn552.rows_assocABC HexagonRowColumn552.cols_innerABC) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_5_2_row_3_1_0 : (left1Middle5 5 2) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn552.rows_assocABC HexagonRowColumn552.cols_innerABC) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_5_2_row_3_1_1 : (left1Middle5 5 2) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn552.rows_assocABC HexagonRowColumn552.cols_innerABC) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_5_2_row_3_1_2 : (left1Middle5 5 2) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn552.rows_assocABC HexagonRowColumn552.cols_innerABC) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_5_2_row_3_1_3 : (left1Middle5 5 2) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn552.rows_assocABC HexagonRowColumn552.cols_innerABC) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_5_2_checked : left1Middle5 5 2 = rowColumnMul HexagonRowColumn552.rows_assocABC HexagonRowColumn552.cols_innerABC := by
  funext r
  fin_cases r
  · exact left1Middle5_eq_case_5_2_row_0_0_0
  · exact left1Middle5_eq_case_5_2_row_0_0_1
  · exact left1Middle5_eq_case_5_2_row_0_0_2
  · exact left1Middle5_eq_case_5_2_row_0_0_3
  · exact left1Middle5_eq_case_5_2_row_0_1_0
  · exact left1Middle5_eq_case_5_2_row_0_1_1
  · exact left1Middle5_eq_case_5_2_row_0_1_2
  · exact left1Middle5_eq_case_5_2_row_0_1_3
  · exact left1Middle5_eq_case_5_2_row_1_0_0
  · exact left1Middle5_eq_case_5_2_row_1_0_1
  · exact left1Middle5_eq_case_5_2_row_1_0_2
  · exact left1Middle5_eq_case_5_2_row_1_0_3
  · exact left1Middle5_eq_case_5_2_row_1_1_0
  · exact left1Middle5_eq_case_5_2_row_1_1_1
  · exact left1Middle5_eq_case_5_2_row_1_1_2
  · exact left1Middle5_eq_case_5_2_row_1_1_3
  · exact left1Middle5_eq_case_5_2_row_2_0_0
  · exact left1Middle5_eq_case_5_2_row_2_0_1
  · exact left1Middle5_eq_case_5_2_row_2_0_2
  · exact left1Middle5_eq_case_5_2_row_2_0_3
  · exact left1Middle5_eq_case_5_2_row_2_1_0
  · exact left1Middle5_eq_case_5_2_row_2_1_1
  · exact left1Middle5_eq_case_5_2_row_2_1_2
  · exact left1Middle5_eq_case_5_2_row_2_1_3
  · exact left1Middle5_eq_case_5_2_row_3_0_0
  · exact left1Middle5_eq_case_5_2_row_3_0_1
  · exact left1Middle5_eq_case_5_2_row_3_0_2
  · exact left1Middle5_eq_case_5_2_row_3_0_3
  · exact left1Middle5_eq_case_5_2_row_3_1_0
  · exact left1Middle5_eq_case_5_2_row_3_1_1
  · exact left1Middle5_eq_case_5_2_row_3_1_2
  · exact left1Middle5_eq_case_5_2_row_3_1_3

set_option backward.isDefEq.respectTransparency false in
theorem left1Middle5_eq_case_5_2 : left1Middle5 5 2 = associatorZ 5 5 2 * innerLeftZ 5 5 2 := by
  simpa only [HexagonAtoms552.assocABC_eq,
    HexagonAtoms552.outerABC_eq,
    HexagonAtoms552.assocBAC_eq,
    HexagonAtoms552.innerABC_eq,
    HexagonAtoms552.innerRightABC_eq,
    HexagonAtoms552.inverseACB_eq,
    HexagonAtoms552.innerACB_eq,
    HexagonAtoms552.assocBCA_eq,
    HexagonAtoms552.innerRightBAC_eq,
    HexagonAtoms552.assocCAB_eq,
    HexagonAtoms552.outerLeftABC_eq,
    HexagonRowColumn552.assocBAC_alias,
    HexagonRowColumn552.innerRightBAC_alias,
    HexagonRowColumn552.product0_eq,
    HexagonRowColumn552.product1_eq,
    HexagonRowColumn552.product2_eq,
    HexagonRowColumn552.product3_eq,
    HexagonRowColumn552.product4_eq,
    HexagonRowColumn552.product5_eq,
    HexagonRowColumn552.product6_eq,
    HexagonRowColumn552.product7_eq] using left1Middle5_eq_case_5_2_checked

private theorem right0Middle5_eq_case_5_2_row_0_0_0 : (right0Middle5 5 2) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms552.assocABC) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_5_2_row_0_0_1 : (right0Middle5 5 2) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms552.assocABC) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_5_2_row_0_0_2 : (right0Middle5 5 2) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms552.assocABC) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_5_2_row_0_0_3 : (right0Middle5 5 2) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms552.assocABC) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_5_2_row_0_1_0 : (right0Middle5 5 2) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms552.assocABC) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_5_2_row_0_1_1 : (right0Middle5 5 2) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms552.assocABC) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_5_2_row_0_1_2 : (right0Middle5 5 2) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms552.assocABC) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_5_2_row_0_1_3 : (right0Middle5 5 2) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms552.assocABC) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_5_2_row_1_0_0 : (right0Middle5 5 2) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms552.assocABC) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_5_2_row_1_0_1 : (right0Middle5 5 2) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms552.assocABC) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_5_2_row_1_0_2 : (right0Middle5 5 2) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms552.assocABC) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_5_2_row_1_0_3 : (right0Middle5 5 2) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms552.assocABC) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_5_2_row_1_1_0 : (right0Middle5 5 2) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms552.assocABC) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_5_2_row_1_1_1 : (right0Middle5 5 2) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms552.assocABC) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_5_2_row_1_1_2 : (right0Middle5 5 2) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms552.assocABC) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_5_2_row_1_1_3 : (right0Middle5 5 2) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms552.assocABC) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_5_2_row_2_0_0 : (right0Middle5 5 2) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms552.assocABC) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_5_2_row_2_0_1 : (right0Middle5 5 2) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms552.assocABC) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_5_2_row_2_0_2 : (right0Middle5 5 2) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms552.assocABC) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_5_2_row_2_0_3 : (right0Middle5 5 2) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms552.assocABC) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_5_2_row_2_1_0 : (right0Middle5 5 2) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms552.assocABC) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_5_2_row_2_1_1 : (right0Middle5 5 2) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms552.assocABC) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_5_2_row_2_1_2 : (right0Middle5 5 2) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms552.assocABC) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_5_2_row_2_1_3 : (right0Middle5 5 2) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms552.assocABC) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_5_2_row_3_0_0 : (right0Middle5 5 2) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms552.assocABC) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_5_2_row_3_0_1 : (right0Middle5 5 2) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms552.assocABC) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_5_2_row_3_0_2 : (right0Middle5 5 2) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms552.assocABC) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_5_2_row_3_0_3 : (right0Middle5 5 2) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms552.assocABC) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_5_2_row_3_1_0 : (right0Middle5 5 2) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms552.assocABC) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_5_2_row_3_1_1 : (right0Middle5 5 2) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms552.assocABC) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_5_2_row_3_1_2 : (right0Middle5 5 2) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms552.assocABC) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_5_2_row_3_1_3 : (right0Middle5 5 2) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms552.assocABC) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_5_2_checked : right0Middle5 5 2 = HexagonAtoms552.assocABC := by
  funext r
  fin_cases r
  · exact right0Middle5_eq_case_5_2_row_0_0_0
  · exact right0Middle5_eq_case_5_2_row_0_0_1
  · exact right0Middle5_eq_case_5_2_row_0_0_2
  · exact right0Middle5_eq_case_5_2_row_0_0_3
  · exact right0Middle5_eq_case_5_2_row_0_1_0
  · exact right0Middle5_eq_case_5_2_row_0_1_1
  · exact right0Middle5_eq_case_5_2_row_0_1_2
  · exact right0Middle5_eq_case_5_2_row_0_1_3
  · exact right0Middle5_eq_case_5_2_row_1_0_0
  · exact right0Middle5_eq_case_5_2_row_1_0_1
  · exact right0Middle5_eq_case_5_2_row_1_0_2
  · exact right0Middle5_eq_case_5_2_row_1_0_3
  · exact right0Middle5_eq_case_5_2_row_1_1_0
  · exact right0Middle5_eq_case_5_2_row_1_1_1
  · exact right0Middle5_eq_case_5_2_row_1_1_2
  · exact right0Middle5_eq_case_5_2_row_1_1_3
  · exact right0Middle5_eq_case_5_2_row_2_0_0
  · exact right0Middle5_eq_case_5_2_row_2_0_1
  · exact right0Middle5_eq_case_5_2_row_2_0_2
  · exact right0Middle5_eq_case_5_2_row_2_0_3
  · exact right0Middle5_eq_case_5_2_row_2_1_0
  · exact right0Middle5_eq_case_5_2_row_2_1_1
  · exact right0Middle5_eq_case_5_2_row_2_1_2
  · exact right0Middle5_eq_case_5_2_row_2_1_3
  · exact right0Middle5_eq_case_5_2_row_3_0_0
  · exact right0Middle5_eq_case_5_2_row_3_0_1
  · exact right0Middle5_eq_case_5_2_row_3_0_2
  · exact right0Middle5_eq_case_5_2_row_3_0_3
  · exact right0Middle5_eq_case_5_2_row_3_1_0
  · exact right0Middle5_eq_case_5_2_row_3_1_1
  · exact right0Middle5_eq_case_5_2_row_3_1_2
  · exact right0Middle5_eq_case_5_2_row_3_1_3

set_option backward.isDefEq.respectTransparency false in
theorem right0Middle5_eq_case_5_2 : right0Middle5 5 2 = innerRightZ 5 5 2 * associatorZ 5 5 2 := by
  simpa only [HexagonAtoms552.assocABC_eq,
    HexagonAtoms552.outerABC_eq,
    HexagonAtoms552.assocBAC_eq,
    HexagonAtoms552.innerABC_eq,
    HexagonAtoms552.innerRightABC_eq,
    HexagonAtoms552.inverseACB_eq,
    HexagonAtoms552.innerACB_eq,
    HexagonAtoms552.assocBCA_eq,
    HexagonAtoms552.innerRightBAC_eq,
    HexagonAtoms552.assocCAB_eq,
    HexagonAtoms552.outerLeftABC_eq,
    HexagonRowColumn552.assocBAC_alias,
    HexagonRowColumn552.innerRightBAC_alias,
    HexagonRowColumn552.product0_eq,
    HexagonRowColumn552.product1_eq,
    HexagonRowColumn552.product2_eq,
    HexagonRowColumn552.product3_eq,
    HexagonRowColumn552.product4_eq,
    HexagonRowColumn552.product5_eq,
    HexagonRowColumn552.product6_eq,
    HexagonRowColumn552.product7_eq] using right0Middle5_eq_case_5_2_checked

private theorem right1Middle5_eq_case_5_2_row_0_0_0 : (right1Middle5 5 2) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn552.rows_inverseACB HexagonRowColumn552.cols_right0) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_5_2_row_0_0_1 : (right1Middle5 5 2) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn552.rows_inverseACB HexagonRowColumn552.cols_right0) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_5_2_row_0_0_2 : (right1Middle5 5 2) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn552.rows_inverseACB HexagonRowColumn552.cols_right0) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_5_2_row_0_0_3 : (right1Middle5 5 2) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn552.rows_inverseACB HexagonRowColumn552.cols_right0) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_5_2_row_0_1_0 : (right1Middle5 5 2) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn552.rows_inverseACB HexagonRowColumn552.cols_right0) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_5_2_row_0_1_1 : (right1Middle5 5 2) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn552.rows_inverseACB HexagonRowColumn552.cols_right0) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_5_2_row_0_1_2 : (right1Middle5 5 2) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn552.rows_inverseACB HexagonRowColumn552.cols_right0) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_5_2_row_0_1_3 : (right1Middle5 5 2) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn552.rows_inverseACB HexagonRowColumn552.cols_right0) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_5_2_row_1_0_0 : (right1Middle5 5 2) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn552.rows_inverseACB HexagonRowColumn552.cols_right0) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_5_2_row_1_0_1 : (right1Middle5 5 2) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn552.rows_inverseACB HexagonRowColumn552.cols_right0) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_5_2_row_1_0_2 : (right1Middle5 5 2) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn552.rows_inverseACB HexagonRowColumn552.cols_right0) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_5_2_row_1_0_3 : (right1Middle5 5 2) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn552.rows_inverseACB HexagonRowColumn552.cols_right0) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_5_2_row_1_1_0 : (right1Middle5 5 2) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn552.rows_inverseACB HexagonRowColumn552.cols_right0) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_5_2_row_1_1_1 : (right1Middle5 5 2) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn552.rows_inverseACB HexagonRowColumn552.cols_right0) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_5_2_row_1_1_2 : (right1Middle5 5 2) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn552.rows_inverseACB HexagonRowColumn552.cols_right0) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_5_2_row_1_1_3 : (right1Middle5 5 2) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn552.rows_inverseACB HexagonRowColumn552.cols_right0) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_5_2_row_2_0_0 : (right1Middle5 5 2) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn552.rows_inverseACB HexagonRowColumn552.cols_right0) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_5_2_row_2_0_1 : (right1Middle5 5 2) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn552.rows_inverseACB HexagonRowColumn552.cols_right0) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_5_2_row_2_0_2 : (right1Middle5 5 2) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn552.rows_inverseACB HexagonRowColumn552.cols_right0) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_5_2_row_2_0_3 : (right1Middle5 5 2) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn552.rows_inverseACB HexagonRowColumn552.cols_right0) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_5_2_row_2_1_0 : (right1Middle5 5 2) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn552.rows_inverseACB HexagonRowColumn552.cols_right0) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_5_2_row_2_1_1 : (right1Middle5 5 2) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn552.rows_inverseACB HexagonRowColumn552.cols_right0) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_5_2_row_2_1_2 : (right1Middle5 5 2) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn552.rows_inverseACB HexagonRowColumn552.cols_right0) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_5_2_row_2_1_3 : (right1Middle5 5 2) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn552.rows_inverseACB HexagonRowColumn552.cols_right0) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_5_2_row_3_0_0 : (right1Middle5 5 2) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn552.rows_inverseACB HexagonRowColumn552.cols_right0) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_5_2_row_3_0_1 : (right1Middle5 5 2) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn552.rows_inverseACB HexagonRowColumn552.cols_right0) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_5_2_row_3_0_2 : (right1Middle5 5 2) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn552.rows_inverseACB HexagonRowColumn552.cols_right0) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_5_2_row_3_0_3 : (right1Middle5 5 2) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn552.rows_inverseACB HexagonRowColumn552.cols_right0) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_5_2_row_3_1_0 : (right1Middle5 5 2) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn552.rows_inverseACB HexagonRowColumn552.cols_right0) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_5_2_row_3_1_1 : (right1Middle5 5 2) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn552.rows_inverseACB HexagonRowColumn552.cols_right0) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_5_2_row_3_1_2 : (right1Middle5 5 2) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn552.rows_inverseACB HexagonRowColumn552.cols_right0) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_5_2_row_3_1_3 : (right1Middle5 5 2) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn552.rows_inverseACB HexagonRowColumn552.cols_right0) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_5_2_checked : right1Middle5 5 2 = rowColumnMul HexagonRowColumn552.rows_inverseACB HexagonRowColumn552.cols_right0 := by
  funext r
  fin_cases r
  · exact right1Middle5_eq_case_5_2_row_0_0_0
  · exact right1Middle5_eq_case_5_2_row_0_0_1
  · exact right1Middle5_eq_case_5_2_row_0_0_2
  · exact right1Middle5_eq_case_5_2_row_0_0_3
  · exact right1Middle5_eq_case_5_2_row_0_1_0
  · exact right1Middle5_eq_case_5_2_row_0_1_1
  · exact right1Middle5_eq_case_5_2_row_0_1_2
  · exact right1Middle5_eq_case_5_2_row_0_1_3
  · exact right1Middle5_eq_case_5_2_row_1_0_0
  · exact right1Middle5_eq_case_5_2_row_1_0_1
  · exact right1Middle5_eq_case_5_2_row_1_0_2
  · exact right1Middle5_eq_case_5_2_row_1_0_3
  · exact right1Middle5_eq_case_5_2_row_1_1_0
  · exact right1Middle5_eq_case_5_2_row_1_1_1
  · exact right1Middle5_eq_case_5_2_row_1_1_2
  · exact right1Middle5_eq_case_5_2_row_1_1_3
  · exact right1Middle5_eq_case_5_2_row_2_0_0
  · exact right1Middle5_eq_case_5_2_row_2_0_1
  · exact right1Middle5_eq_case_5_2_row_2_0_2
  · exact right1Middle5_eq_case_5_2_row_2_0_3
  · exact right1Middle5_eq_case_5_2_row_2_1_0
  · exact right1Middle5_eq_case_5_2_row_2_1_1
  · exact right1Middle5_eq_case_5_2_row_2_1_2
  · exact right1Middle5_eq_case_5_2_row_2_1_3
  · exact right1Middle5_eq_case_5_2_row_3_0_0
  · exact right1Middle5_eq_case_5_2_row_3_0_1
  · exact right1Middle5_eq_case_5_2_row_3_0_2
  · exact right1Middle5_eq_case_5_2_row_3_0_3
  · exact right1Middle5_eq_case_5_2_row_3_1_0
  · exact right1Middle5_eq_case_5_2_row_3_1_1
  · exact right1Middle5_eq_case_5_2_row_3_1_2
  · exact right1Middle5_eq_case_5_2_row_3_1_3

set_option backward.isDefEq.respectTransparency false in
theorem right1Middle5_eq_case_5_2 : right1Middle5 5 2 = associatorInverseZ 5 2 5 * right0Middle5 5 2 := by
  simpa only [HexagonAtoms552.assocABC_eq,
    HexagonAtoms552.outerABC_eq,
    HexagonAtoms552.assocBAC_eq,
    HexagonAtoms552.innerABC_eq,
    HexagonAtoms552.innerRightABC_eq,
    HexagonAtoms552.inverseACB_eq,
    HexagonAtoms552.innerACB_eq,
    HexagonAtoms552.assocBCA_eq,
    HexagonAtoms552.innerRightBAC_eq,
    HexagonAtoms552.assocCAB_eq,
    HexagonAtoms552.outerLeftABC_eq,
    HexagonRowColumn552.assocBAC_alias,
    HexagonRowColumn552.innerRightBAC_alias,
    HexagonRowColumn552.product0_eq,
    HexagonRowColumn552.product1_eq,
    HexagonRowColumn552.product2_eq,
    HexagonRowColumn552.product3_eq,
    HexagonRowColumn552.product4_eq,
    HexagonRowColumn552.product5_eq,
    HexagonRowColumn552.product6_eq,
    HexagonRowColumn552.product7_eq] using right1Middle5_eq_case_5_2_checked

private theorem right2Middle5_eq_case_5_2_row_0_0_0 : (right2Middle5 5 2) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (right1Middle5 5 2) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_5_2_row_0_0_1 : (right2Middle5 5 2) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (right1Middle5 5 2) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_5_2_row_0_0_2 : (right2Middle5 5 2) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (right1Middle5 5 2) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_5_2_row_0_0_3 : (right2Middle5 5 2) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (right1Middle5 5 2) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_5_2_row_0_1_0 : (right2Middle5 5 2) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (right1Middle5 5 2) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_5_2_row_0_1_1 : (right2Middle5 5 2) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (right1Middle5 5 2) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_5_2_row_0_1_2 : (right2Middle5 5 2) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (right1Middle5 5 2) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_5_2_row_0_1_3 : (right2Middle5 5 2) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (right1Middle5 5 2) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_5_2_row_1_0_0 : (right2Middle5 5 2) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (right1Middle5 5 2) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_5_2_row_1_0_1 : (right2Middle5 5 2) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (right1Middle5 5 2) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_5_2_row_1_0_2 : (right2Middle5 5 2) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (right1Middle5 5 2) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_5_2_row_1_0_3 : (right2Middle5 5 2) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (right1Middle5 5 2) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_5_2_row_1_1_0 : (right2Middle5 5 2) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (right1Middle5 5 2) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_5_2_row_1_1_1 : (right2Middle5 5 2) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (right1Middle5 5 2) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_5_2_row_1_1_2 : (right2Middle5 5 2) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (right1Middle5 5 2) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_5_2_row_1_1_3 : (right2Middle5 5 2) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (right1Middle5 5 2) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_5_2_row_2_0_0 : (right2Middle5 5 2) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (right1Middle5 5 2) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_5_2_row_2_0_1 : (right2Middle5 5 2) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (right1Middle5 5 2) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_5_2_row_2_0_2 : (right2Middle5 5 2) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (right1Middle5 5 2) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_5_2_row_2_0_3 : (right2Middle5 5 2) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (right1Middle5 5 2) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_5_2_row_2_1_0 : (right2Middle5 5 2) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (right1Middle5 5 2) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_5_2_row_2_1_1 : (right2Middle5 5 2) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (right1Middle5 5 2) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_5_2_row_2_1_2 : (right2Middle5 5 2) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (right1Middle5 5 2) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_5_2_row_2_1_3 : (right2Middle5 5 2) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (right1Middle5 5 2) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_5_2_row_3_0_0 : (right2Middle5 5 2) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (right1Middle5 5 2) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_5_2_row_3_0_1 : (right2Middle5 5 2) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (right1Middle5 5 2) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_5_2_row_3_0_2 : (right2Middle5 5 2) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (right1Middle5 5 2) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_5_2_row_3_0_3 : (right2Middle5 5 2) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (right1Middle5 5 2) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_5_2_row_3_1_0 : (right2Middle5 5 2) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (right1Middle5 5 2) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_5_2_row_3_1_1 : (right2Middle5 5 2) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (right1Middle5 5 2) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_5_2_row_3_1_2 : (right2Middle5 5 2) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (right1Middle5 5 2) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_5_2_row_3_1_3 : (right2Middle5 5 2) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (right1Middle5 5 2) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_5_2_checked : right2Middle5 5 2 = right1Middle5 5 2 := by
  funext r
  fin_cases r
  · exact right2Middle5_eq_case_5_2_row_0_0_0
  · exact right2Middle5_eq_case_5_2_row_0_0_1
  · exact right2Middle5_eq_case_5_2_row_0_0_2
  · exact right2Middle5_eq_case_5_2_row_0_0_3
  · exact right2Middle5_eq_case_5_2_row_0_1_0
  · exact right2Middle5_eq_case_5_2_row_0_1_1
  · exact right2Middle5_eq_case_5_2_row_0_1_2
  · exact right2Middle5_eq_case_5_2_row_0_1_3
  · exact right2Middle5_eq_case_5_2_row_1_0_0
  · exact right2Middle5_eq_case_5_2_row_1_0_1
  · exact right2Middle5_eq_case_5_2_row_1_0_2
  · exact right2Middle5_eq_case_5_2_row_1_0_3
  · exact right2Middle5_eq_case_5_2_row_1_1_0
  · exact right2Middle5_eq_case_5_2_row_1_1_1
  · exact right2Middle5_eq_case_5_2_row_1_1_2
  · exact right2Middle5_eq_case_5_2_row_1_1_3
  · exact right2Middle5_eq_case_5_2_row_2_0_0
  · exact right2Middle5_eq_case_5_2_row_2_0_1
  · exact right2Middle5_eq_case_5_2_row_2_0_2
  · exact right2Middle5_eq_case_5_2_row_2_0_3
  · exact right2Middle5_eq_case_5_2_row_2_1_0
  · exact right2Middle5_eq_case_5_2_row_2_1_1
  · exact right2Middle5_eq_case_5_2_row_2_1_2
  · exact right2Middle5_eq_case_5_2_row_2_1_3
  · exact right2Middle5_eq_case_5_2_row_3_0_0
  · exact right2Middle5_eq_case_5_2_row_3_0_1
  · exact right2Middle5_eq_case_5_2_row_3_0_2
  · exact right2Middle5_eq_case_5_2_row_3_0_3
  · exact right2Middle5_eq_case_5_2_row_3_1_0
  · exact right2Middle5_eq_case_5_2_row_3_1_1
  · exact right2Middle5_eq_case_5_2_row_3_1_2
  · exact right2Middle5_eq_case_5_2_row_3_1_3

set_option backward.isDefEq.respectTransparency false in
theorem right2Middle5_eq_case_5_2 : right2Middle5 5 2 = innerLeftZ 5 2 5 * right1Middle5 5 2 := by
  simpa only [HexagonAtoms552.assocABC_eq,
    HexagonAtoms552.outerABC_eq,
    HexagonAtoms552.assocBAC_eq,
    HexagonAtoms552.innerABC_eq,
    HexagonAtoms552.innerRightABC_eq,
    HexagonAtoms552.inverseACB_eq,
    HexagonAtoms552.innerACB_eq,
    HexagonAtoms552.assocBCA_eq,
    HexagonAtoms552.innerRightBAC_eq,
    HexagonAtoms552.assocCAB_eq,
    HexagonAtoms552.outerLeftABC_eq,
    HexagonRowColumn552.assocBAC_alias,
    HexagonRowColumn552.innerRightBAC_alias,
    HexagonRowColumn552.product0_eq,
    HexagonRowColumn552.product1_eq,
    HexagonRowColumn552.product2_eq,
    HexagonRowColumn552.product3_eq,
    HexagonRowColumn552.product4_eq,
    HexagonRowColumn552.product5_eq,
    HexagonRowColumn552.product6_eq,
    HexagonRowColumn552.product7_eq] using right2Middle5_eq_case_5_2_checked

private theorem leftFinal5_case_5_2_row_0_0_0 : (((-1 : ℤ) ^ (leftScaleBit 5 5 2).val * positiveScale (leftScaleExponent 5 5 2)) •
      (rowColumnMul HexagonRowColumn552.rows_assocBCA HexagonRowColumn552.cols_left0)) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 5 5 2) • (left1Middle5 5 2)) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_5_2_row_0_0_1 : (((-1 : ℤ) ^ (leftScaleBit 5 5 2).val * positiveScale (leftScaleExponent 5 5 2)) •
      (rowColumnMul HexagonRowColumn552.rows_assocBCA HexagonRowColumn552.cols_left0)) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 5 5 2) • (left1Middle5 5 2)) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_5_2_row_0_0_2 : (((-1 : ℤ) ^ (leftScaleBit 5 5 2).val * positiveScale (leftScaleExponent 5 5 2)) •
      (rowColumnMul HexagonRowColumn552.rows_assocBCA HexagonRowColumn552.cols_left0)) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 5 5 2) • (left1Middle5 5 2)) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_5_2_row_0_0_3 : (((-1 : ℤ) ^ (leftScaleBit 5 5 2).val * positiveScale (leftScaleExponent 5 5 2)) •
      (rowColumnMul HexagonRowColumn552.rows_assocBCA HexagonRowColumn552.cols_left0)) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 5 5 2) • (left1Middle5 5 2)) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_5_2_row_0_1_0 : (((-1 : ℤ) ^ (leftScaleBit 5 5 2).val * positiveScale (leftScaleExponent 5 5 2)) •
      (rowColumnMul HexagonRowColumn552.rows_assocBCA HexagonRowColumn552.cols_left0)) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 5 5 2) • (left1Middle5 5 2)) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_5_2_row_0_1_1 : (((-1 : ℤ) ^ (leftScaleBit 5 5 2).val * positiveScale (leftScaleExponent 5 5 2)) •
      (rowColumnMul HexagonRowColumn552.rows_assocBCA HexagonRowColumn552.cols_left0)) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 5 5 2) • (left1Middle5 5 2)) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_5_2_row_0_1_2 : (((-1 : ℤ) ^ (leftScaleBit 5 5 2).val * positiveScale (leftScaleExponent 5 5 2)) •
      (rowColumnMul HexagonRowColumn552.rows_assocBCA HexagonRowColumn552.cols_left0)) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 5 5 2) • (left1Middle5 5 2)) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_5_2_row_0_1_3 : (((-1 : ℤ) ^ (leftScaleBit 5 5 2).val * positiveScale (leftScaleExponent 5 5 2)) •
      (rowColumnMul HexagonRowColumn552.rows_assocBCA HexagonRowColumn552.cols_left0)) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 5 5 2) • (left1Middle5 5 2)) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_5_2_row_1_0_0 : (((-1 : ℤ) ^ (leftScaleBit 5 5 2).val * positiveScale (leftScaleExponent 5 5 2)) •
      (rowColumnMul HexagonRowColumn552.rows_assocBCA HexagonRowColumn552.cols_left0)) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 5 5 2) • (left1Middle5 5 2)) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_5_2_row_1_0_1 : (((-1 : ℤ) ^ (leftScaleBit 5 5 2).val * positiveScale (leftScaleExponent 5 5 2)) •
      (rowColumnMul HexagonRowColumn552.rows_assocBCA HexagonRowColumn552.cols_left0)) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 5 5 2) • (left1Middle5 5 2)) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_5_2_row_1_0_2 : (((-1 : ℤ) ^ (leftScaleBit 5 5 2).val * positiveScale (leftScaleExponent 5 5 2)) •
      (rowColumnMul HexagonRowColumn552.rows_assocBCA HexagonRowColumn552.cols_left0)) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 5 5 2) • (left1Middle5 5 2)) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_5_2_row_1_0_3 : (((-1 : ℤ) ^ (leftScaleBit 5 5 2).val * positiveScale (leftScaleExponent 5 5 2)) •
      (rowColumnMul HexagonRowColumn552.rows_assocBCA HexagonRowColumn552.cols_left0)) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 5 5 2) • (left1Middle5 5 2)) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_5_2_row_1_1_0 : (((-1 : ℤ) ^ (leftScaleBit 5 5 2).val * positiveScale (leftScaleExponent 5 5 2)) •
      (rowColumnMul HexagonRowColumn552.rows_assocBCA HexagonRowColumn552.cols_left0)) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 5 5 2) • (left1Middle5 5 2)) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_5_2_row_1_1_1 : (((-1 : ℤ) ^ (leftScaleBit 5 5 2).val * positiveScale (leftScaleExponent 5 5 2)) •
      (rowColumnMul HexagonRowColumn552.rows_assocBCA HexagonRowColumn552.cols_left0)) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 5 5 2) • (left1Middle5 5 2)) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_5_2_row_1_1_2 : (((-1 : ℤ) ^ (leftScaleBit 5 5 2).val * positiveScale (leftScaleExponent 5 5 2)) •
      (rowColumnMul HexagonRowColumn552.rows_assocBCA HexagonRowColumn552.cols_left0)) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 5 5 2) • (left1Middle5 5 2)) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_5_2_row_1_1_3 : (((-1 : ℤ) ^ (leftScaleBit 5 5 2).val * positiveScale (leftScaleExponent 5 5 2)) •
      (rowColumnMul HexagonRowColumn552.rows_assocBCA HexagonRowColumn552.cols_left0)) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 5 5 2) • (left1Middle5 5 2)) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_5_2_row_2_0_0 : (((-1 : ℤ) ^ (leftScaleBit 5 5 2).val * positiveScale (leftScaleExponent 5 5 2)) •
      (rowColumnMul HexagonRowColumn552.rows_assocBCA HexagonRowColumn552.cols_left0)) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 5 5 2) • (left1Middle5 5 2)) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_5_2_row_2_0_1 : (((-1 : ℤ) ^ (leftScaleBit 5 5 2).val * positiveScale (leftScaleExponent 5 5 2)) •
      (rowColumnMul HexagonRowColumn552.rows_assocBCA HexagonRowColumn552.cols_left0)) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 5 5 2) • (left1Middle5 5 2)) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_5_2_row_2_0_2 : (((-1 : ℤ) ^ (leftScaleBit 5 5 2).val * positiveScale (leftScaleExponent 5 5 2)) •
      (rowColumnMul HexagonRowColumn552.rows_assocBCA HexagonRowColumn552.cols_left0)) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 5 5 2) • (left1Middle5 5 2)) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_5_2_row_2_0_3 : (((-1 : ℤ) ^ (leftScaleBit 5 5 2).val * positiveScale (leftScaleExponent 5 5 2)) •
      (rowColumnMul HexagonRowColumn552.rows_assocBCA HexagonRowColumn552.cols_left0)) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 5 5 2) • (left1Middle5 5 2)) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_5_2_row_2_1_0 : (((-1 : ℤ) ^ (leftScaleBit 5 5 2).val * positiveScale (leftScaleExponent 5 5 2)) •
      (rowColumnMul HexagonRowColumn552.rows_assocBCA HexagonRowColumn552.cols_left0)) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 5 5 2) • (left1Middle5 5 2)) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_5_2_row_2_1_1 : (((-1 : ℤ) ^ (leftScaleBit 5 5 2).val * positiveScale (leftScaleExponent 5 5 2)) •
      (rowColumnMul HexagonRowColumn552.rows_assocBCA HexagonRowColumn552.cols_left0)) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 5 5 2) • (left1Middle5 5 2)) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_5_2_row_2_1_2 : (((-1 : ℤ) ^ (leftScaleBit 5 5 2).val * positiveScale (leftScaleExponent 5 5 2)) •
      (rowColumnMul HexagonRowColumn552.rows_assocBCA HexagonRowColumn552.cols_left0)) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 5 5 2) • (left1Middle5 5 2)) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_5_2_row_2_1_3 : (((-1 : ℤ) ^ (leftScaleBit 5 5 2).val * positiveScale (leftScaleExponent 5 5 2)) •
      (rowColumnMul HexagonRowColumn552.rows_assocBCA HexagonRowColumn552.cols_left0)) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 5 5 2) • (left1Middle5 5 2)) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_5_2_row_3_0_0 : (((-1 : ℤ) ^ (leftScaleBit 5 5 2).val * positiveScale (leftScaleExponent 5 5 2)) •
      (rowColumnMul HexagonRowColumn552.rows_assocBCA HexagonRowColumn552.cols_left0)) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 5 5 2) • (left1Middle5 5 2)) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_5_2_row_3_0_1 : (((-1 : ℤ) ^ (leftScaleBit 5 5 2).val * positiveScale (leftScaleExponent 5 5 2)) •
      (rowColumnMul HexagonRowColumn552.rows_assocBCA HexagonRowColumn552.cols_left0)) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 5 5 2) • (left1Middle5 5 2)) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_5_2_row_3_0_2 : (((-1 : ℤ) ^ (leftScaleBit 5 5 2).val * positiveScale (leftScaleExponent 5 5 2)) •
      (rowColumnMul HexagonRowColumn552.rows_assocBCA HexagonRowColumn552.cols_left0)) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 5 5 2) • (left1Middle5 5 2)) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_5_2_row_3_0_3 : (((-1 : ℤ) ^ (leftScaleBit 5 5 2).val * positiveScale (leftScaleExponent 5 5 2)) •
      (rowColumnMul HexagonRowColumn552.rows_assocBCA HexagonRowColumn552.cols_left0)) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 5 5 2) • (left1Middle5 5 2)) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_5_2_row_3_1_0 : (((-1 : ℤ) ^ (leftScaleBit 5 5 2).val * positiveScale (leftScaleExponent 5 5 2)) •
      (rowColumnMul HexagonRowColumn552.rows_assocBCA HexagonRowColumn552.cols_left0)) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 5 5 2) • (left1Middle5 5 2)) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_5_2_row_3_1_1 : (((-1 : ℤ) ^ (leftScaleBit 5 5 2).val * positiveScale (leftScaleExponent 5 5 2)) •
      (rowColumnMul HexagonRowColumn552.rows_assocBCA HexagonRowColumn552.cols_left0)) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 5 5 2) • (left1Middle5 5 2)) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_5_2_row_3_1_2 : (((-1 : ℤ) ^ (leftScaleBit 5 5 2).val * positiveScale (leftScaleExponent 5 5 2)) •
      (rowColumnMul HexagonRowColumn552.rows_assocBCA HexagonRowColumn552.cols_left0)) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 5 5 2) • (left1Middle5 5 2)) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_5_2_row_3_1_3 : (((-1 : ℤ) ^ (leftScaleBit 5 5 2).val * positiveScale (leftScaleExponent 5 5 2)) •
      (rowColumnMul HexagonRowColumn552.rows_assocBCA HexagonRowColumn552.cols_left0)) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 5 5 2) • (left1Middle5 5 2)) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_5_2_checked : ((-1 : ℤ) ^ (leftScaleBit 5 5 2).val * positiveScale (leftScaleExponent 5 5 2)) •
      (rowColumnMul HexagonRowColumn552.rows_assocBCA HexagonRowColumn552.cols_left0) = negativeScale (leftScaleExponent 5 5 2) • (left1Middle5 5 2) := by
  funext r
  fin_cases r
  · exact leftFinal5_case_5_2_row_0_0_0
  · exact leftFinal5_case_5_2_row_0_0_1
  · exact leftFinal5_case_5_2_row_0_0_2
  · exact leftFinal5_case_5_2_row_0_0_3
  · exact leftFinal5_case_5_2_row_0_1_0
  · exact leftFinal5_case_5_2_row_0_1_1
  · exact leftFinal5_case_5_2_row_0_1_2
  · exact leftFinal5_case_5_2_row_0_1_3
  · exact leftFinal5_case_5_2_row_1_0_0
  · exact leftFinal5_case_5_2_row_1_0_1
  · exact leftFinal5_case_5_2_row_1_0_2
  · exact leftFinal5_case_5_2_row_1_0_3
  · exact leftFinal5_case_5_2_row_1_1_0
  · exact leftFinal5_case_5_2_row_1_1_1
  · exact leftFinal5_case_5_2_row_1_1_2
  · exact leftFinal5_case_5_2_row_1_1_3
  · exact leftFinal5_case_5_2_row_2_0_0
  · exact leftFinal5_case_5_2_row_2_0_1
  · exact leftFinal5_case_5_2_row_2_0_2
  · exact leftFinal5_case_5_2_row_2_0_3
  · exact leftFinal5_case_5_2_row_2_1_0
  · exact leftFinal5_case_5_2_row_2_1_1
  · exact leftFinal5_case_5_2_row_2_1_2
  · exact leftFinal5_case_5_2_row_2_1_3
  · exact leftFinal5_case_5_2_row_3_0_0
  · exact leftFinal5_case_5_2_row_3_0_1
  · exact leftFinal5_case_5_2_row_3_0_2
  · exact leftFinal5_case_5_2_row_3_0_3
  · exact leftFinal5_case_5_2_row_3_1_0
  · exact leftFinal5_case_5_2_row_3_1_1
  · exact leftFinal5_case_5_2_row_3_1_2
  · exact leftFinal5_case_5_2_row_3_1_3

set_option backward.isDefEq.respectTransparency false in
theorem leftFinal5_case_5_2 : ((-1 : ℤ) ^ (leftScaleBit 5 5 2).val * positiveScale (leftScaleExponent 5 5 2)) •
      (associatorZ 5 2 5 * left0Middle5 5 2) = negativeScale (leftScaleExponent 5 5 2) • (innerRightZ 5 5 2 * left1Middle5 5 2) := by
  simpa only [HexagonAtoms552.assocABC_eq,
    HexagonAtoms552.outerABC_eq,
    HexagonAtoms552.assocBAC_eq,
    HexagonAtoms552.innerABC_eq,
    HexagonAtoms552.innerRightABC_eq,
    HexagonAtoms552.inverseACB_eq,
    HexagonAtoms552.innerACB_eq,
    HexagonAtoms552.assocBCA_eq,
    HexagonAtoms552.innerRightBAC_eq,
    HexagonAtoms552.assocCAB_eq,
    HexagonAtoms552.outerLeftABC_eq,
    HexagonRowColumn552.assocBAC_alias,
    HexagonRowColumn552.innerRightBAC_alias,
    HexagonRowColumn552.product0_eq,
    HexagonRowColumn552.product1_eq,
    HexagonRowColumn552.product2_eq,
    HexagonRowColumn552.product3_eq,
    HexagonRowColumn552.product4_eq,
    HexagonRowColumn552.product5_eq,
    HexagonRowColumn552.product6_eq,
    HexagonRowColumn552.product7_eq] using leftFinal5_case_5_2_checked

private theorem rightFinal5_case_5_2_row_0_0_0 : (((-1 : ℤ) ^ (rightScaleBit 5 5 2).val * positiveScale (rightScaleExponent 5 5 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 2 5 : ℤ)) • HexagonAtoms552.outerLeftABC) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 5 5 2) • (rowColumnMul HexagonRowColumn552.rows_assocCAB HexagonRowColumn552.cols_right2)) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_5_2_row_0_0_1 : (((-1 : ℤ) ^ (rightScaleBit 5 5 2).val * positiveScale (rightScaleExponent 5 5 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 2 5 : ℤ)) • HexagonAtoms552.outerLeftABC) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 5 5 2) • (rowColumnMul HexagonRowColumn552.rows_assocCAB HexagonRowColumn552.cols_right2)) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_5_2_row_0_0_2 : (((-1 : ℤ) ^ (rightScaleBit 5 5 2).val * positiveScale (rightScaleExponent 5 5 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 2 5 : ℤ)) • HexagonAtoms552.outerLeftABC) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 5 5 2) • (rowColumnMul HexagonRowColumn552.rows_assocCAB HexagonRowColumn552.cols_right2)) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_5_2_row_0_0_3 : (((-1 : ℤ) ^ (rightScaleBit 5 5 2).val * positiveScale (rightScaleExponent 5 5 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 2 5 : ℤ)) • HexagonAtoms552.outerLeftABC) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 5 5 2) • (rowColumnMul HexagonRowColumn552.rows_assocCAB HexagonRowColumn552.cols_right2)) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_5_2_row_0_1_0 : (((-1 : ℤ) ^ (rightScaleBit 5 5 2).val * positiveScale (rightScaleExponent 5 5 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 2 5 : ℤ)) • HexagonAtoms552.outerLeftABC) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 5 5 2) • (rowColumnMul HexagonRowColumn552.rows_assocCAB HexagonRowColumn552.cols_right2)) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_5_2_row_0_1_1 : (((-1 : ℤ) ^ (rightScaleBit 5 5 2).val * positiveScale (rightScaleExponent 5 5 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 2 5 : ℤ)) • HexagonAtoms552.outerLeftABC) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 5 5 2) • (rowColumnMul HexagonRowColumn552.rows_assocCAB HexagonRowColumn552.cols_right2)) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_5_2_row_0_1_2 : (((-1 : ℤ) ^ (rightScaleBit 5 5 2).val * positiveScale (rightScaleExponent 5 5 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 2 5 : ℤ)) • HexagonAtoms552.outerLeftABC) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 5 5 2) • (rowColumnMul HexagonRowColumn552.rows_assocCAB HexagonRowColumn552.cols_right2)) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_5_2_row_0_1_3 : (((-1 : ℤ) ^ (rightScaleBit 5 5 2).val * positiveScale (rightScaleExponent 5 5 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 2 5 : ℤ)) • HexagonAtoms552.outerLeftABC) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 5 5 2) • (rowColumnMul HexagonRowColumn552.rows_assocCAB HexagonRowColumn552.cols_right2)) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_5_2_row_1_0_0 : (((-1 : ℤ) ^ (rightScaleBit 5 5 2).val * positiveScale (rightScaleExponent 5 5 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 2 5 : ℤ)) • HexagonAtoms552.outerLeftABC) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 5 5 2) • (rowColumnMul HexagonRowColumn552.rows_assocCAB HexagonRowColumn552.cols_right2)) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_5_2_row_1_0_1 : (((-1 : ℤ) ^ (rightScaleBit 5 5 2).val * positiveScale (rightScaleExponent 5 5 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 2 5 : ℤ)) • HexagonAtoms552.outerLeftABC) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 5 5 2) • (rowColumnMul HexagonRowColumn552.rows_assocCAB HexagonRowColumn552.cols_right2)) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_5_2_row_1_0_2 : (((-1 : ℤ) ^ (rightScaleBit 5 5 2).val * positiveScale (rightScaleExponent 5 5 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 2 5 : ℤ)) • HexagonAtoms552.outerLeftABC) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 5 5 2) • (rowColumnMul HexagonRowColumn552.rows_assocCAB HexagonRowColumn552.cols_right2)) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_5_2_row_1_0_3 : (((-1 : ℤ) ^ (rightScaleBit 5 5 2).val * positiveScale (rightScaleExponent 5 5 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 2 5 : ℤ)) • HexagonAtoms552.outerLeftABC) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 5 5 2) • (rowColumnMul HexagonRowColumn552.rows_assocCAB HexagonRowColumn552.cols_right2)) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_5_2_row_1_1_0 : (((-1 : ℤ) ^ (rightScaleBit 5 5 2).val * positiveScale (rightScaleExponent 5 5 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 2 5 : ℤ)) • HexagonAtoms552.outerLeftABC) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 5 5 2) • (rowColumnMul HexagonRowColumn552.rows_assocCAB HexagonRowColumn552.cols_right2)) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_5_2_row_1_1_1 : (((-1 : ℤ) ^ (rightScaleBit 5 5 2).val * positiveScale (rightScaleExponent 5 5 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 2 5 : ℤ)) • HexagonAtoms552.outerLeftABC) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 5 5 2) • (rowColumnMul HexagonRowColumn552.rows_assocCAB HexagonRowColumn552.cols_right2)) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_5_2_row_1_1_2 : (((-1 : ℤ) ^ (rightScaleBit 5 5 2).val * positiveScale (rightScaleExponent 5 5 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 2 5 : ℤ)) • HexagonAtoms552.outerLeftABC) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 5 5 2) • (rowColumnMul HexagonRowColumn552.rows_assocCAB HexagonRowColumn552.cols_right2)) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_5_2_row_1_1_3 : (((-1 : ℤ) ^ (rightScaleBit 5 5 2).val * positiveScale (rightScaleExponent 5 5 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 2 5 : ℤ)) • HexagonAtoms552.outerLeftABC) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 5 5 2) • (rowColumnMul HexagonRowColumn552.rows_assocCAB HexagonRowColumn552.cols_right2)) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_5_2_row_2_0_0 : (((-1 : ℤ) ^ (rightScaleBit 5 5 2).val * positiveScale (rightScaleExponent 5 5 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 2 5 : ℤ)) • HexagonAtoms552.outerLeftABC) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 5 5 2) • (rowColumnMul HexagonRowColumn552.rows_assocCAB HexagonRowColumn552.cols_right2)) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_5_2_row_2_0_1 : (((-1 : ℤ) ^ (rightScaleBit 5 5 2).val * positiveScale (rightScaleExponent 5 5 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 2 5 : ℤ)) • HexagonAtoms552.outerLeftABC) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 5 5 2) • (rowColumnMul HexagonRowColumn552.rows_assocCAB HexagonRowColumn552.cols_right2)) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_5_2_row_2_0_2 : (((-1 : ℤ) ^ (rightScaleBit 5 5 2).val * positiveScale (rightScaleExponent 5 5 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 2 5 : ℤ)) • HexagonAtoms552.outerLeftABC) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 5 5 2) • (rowColumnMul HexagonRowColumn552.rows_assocCAB HexagonRowColumn552.cols_right2)) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_5_2_row_2_0_3 : (((-1 : ℤ) ^ (rightScaleBit 5 5 2).val * positiveScale (rightScaleExponent 5 5 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 2 5 : ℤ)) • HexagonAtoms552.outerLeftABC) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 5 5 2) • (rowColumnMul HexagonRowColumn552.rows_assocCAB HexagonRowColumn552.cols_right2)) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_5_2_row_2_1_0 : (((-1 : ℤ) ^ (rightScaleBit 5 5 2).val * positiveScale (rightScaleExponent 5 5 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 2 5 : ℤ)) • HexagonAtoms552.outerLeftABC) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 5 5 2) • (rowColumnMul HexagonRowColumn552.rows_assocCAB HexagonRowColumn552.cols_right2)) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_5_2_row_2_1_1 : (((-1 : ℤ) ^ (rightScaleBit 5 5 2).val * positiveScale (rightScaleExponent 5 5 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 2 5 : ℤ)) • HexagonAtoms552.outerLeftABC) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 5 5 2) • (rowColumnMul HexagonRowColumn552.rows_assocCAB HexagonRowColumn552.cols_right2)) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_5_2_row_2_1_2 : (((-1 : ℤ) ^ (rightScaleBit 5 5 2).val * positiveScale (rightScaleExponent 5 5 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 2 5 : ℤ)) • HexagonAtoms552.outerLeftABC) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 5 5 2) • (rowColumnMul HexagonRowColumn552.rows_assocCAB HexagonRowColumn552.cols_right2)) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_5_2_row_2_1_3 : (((-1 : ℤ) ^ (rightScaleBit 5 5 2).val * positiveScale (rightScaleExponent 5 5 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 2 5 : ℤ)) • HexagonAtoms552.outerLeftABC) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 5 5 2) • (rowColumnMul HexagonRowColumn552.rows_assocCAB HexagonRowColumn552.cols_right2)) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_5_2_row_3_0_0 : (((-1 : ℤ) ^ (rightScaleBit 5 5 2).val * positiveScale (rightScaleExponent 5 5 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 2 5 : ℤ)) • HexagonAtoms552.outerLeftABC) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 5 5 2) • (rowColumnMul HexagonRowColumn552.rows_assocCAB HexagonRowColumn552.cols_right2)) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_5_2_row_3_0_1 : (((-1 : ℤ) ^ (rightScaleBit 5 5 2).val * positiveScale (rightScaleExponent 5 5 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 2 5 : ℤ)) • HexagonAtoms552.outerLeftABC) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 5 5 2) • (rowColumnMul HexagonRowColumn552.rows_assocCAB HexagonRowColumn552.cols_right2)) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_5_2_row_3_0_2 : (((-1 : ℤ) ^ (rightScaleBit 5 5 2).val * positiveScale (rightScaleExponent 5 5 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 2 5 : ℤ)) • HexagonAtoms552.outerLeftABC) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 5 5 2) • (rowColumnMul HexagonRowColumn552.rows_assocCAB HexagonRowColumn552.cols_right2)) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_5_2_row_3_0_3 : (((-1 : ℤ) ^ (rightScaleBit 5 5 2).val * positiveScale (rightScaleExponent 5 5 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 2 5 : ℤ)) • HexagonAtoms552.outerLeftABC) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 5 5 2) • (rowColumnMul HexagonRowColumn552.rows_assocCAB HexagonRowColumn552.cols_right2)) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_5_2_row_3_1_0 : (((-1 : ℤ) ^ (rightScaleBit 5 5 2).val * positiveScale (rightScaleExponent 5 5 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 2 5 : ℤ)) • HexagonAtoms552.outerLeftABC) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 5 5 2) • (rowColumnMul HexagonRowColumn552.rows_assocCAB HexagonRowColumn552.cols_right2)) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_5_2_row_3_1_1 : (((-1 : ℤ) ^ (rightScaleBit 5 5 2).val * positiveScale (rightScaleExponent 5 5 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 2 5 : ℤ)) • HexagonAtoms552.outerLeftABC) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 5 5 2) • (rowColumnMul HexagonRowColumn552.rows_assocCAB HexagonRowColumn552.cols_right2)) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_5_2_row_3_1_2 : (((-1 : ℤ) ^ (rightScaleBit 5 5 2).val * positiveScale (rightScaleExponent 5 5 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 2 5 : ℤ)) • HexagonAtoms552.outerLeftABC) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 5 5 2) • (rowColumnMul HexagonRowColumn552.rows_assocCAB HexagonRowColumn552.cols_right2)) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_5_2_row_3_1_3 : (((-1 : ℤ) ^ (rightScaleBit 5 5 2).val * positiveScale (rightScaleExponent 5 5 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 2 5 : ℤ)) • HexagonAtoms552.outerLeftABC) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 5 5 2) • (rowColumnMul HexagonRowColumn552.rows_assocCAB HexagonRowColumn552.cols_right2)) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_5_2_checked : ((-1 : ℤ) ^ (rightScaleBit 5 5 2).val * positiveScale (rightScaleExponent 5 5 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 2 5 : ℤ)) • HexagonAtoms552.outerLeftABC = negativeScale (rightScaleExponent 5 5 2) • (rowColumnMul HexagonRowColumn552.rows_assocCAB HexagonRowColumn552.cols_right2) := by
  funext r
  fin_cases r
  · exact rightFinal5_case_5_2_row_0_0_0
  · exact rightFinal5_case_5_2_row_0_0_1
  · exact rightFinal5_case_5_2_row_0_0_2
  · exact rightFinal5_case_5_2_row_0_0_3
  · exact rightFinal5_case_5_2_row_0_1_0
  · exact rightFinal5_case_5_2_row_0_1_1
  · exact rightFinal5_case_5_2_row_0_1_2
  · exact rightFinal5_case_5_2_row_0_1_3
  · exact rightFinal5_case_5_2_row_1_0_0
  · exact rightFinal5_case_5_2_row_1_0_1
  · exact rightFinal5_case_5_2_row_1_0_2
  · exact rightFinal5_case_5_2_row_1_0_3
  · exact rightFinal5_case_5_2_row_1_1_0
  · exact rightFinal5_case_5_2_row_1_1_1
  · exact rightFinal5_case_5_2_row_1_1_2
  · exact rightFinal5_case_5_2_row_1_1_3
  · exact rightFinal5_case_5_2_row_2_0_0
  · exact rightFinal5_case_5_2_row_2_0_1
  · exact rightFinal5_case_5_2_row_2_0_2
  · exact rightFinal5_case_5_2_row_2_0_3
  · exact rightFinal5_case_5_2_row_2_1_0
  · exact rightFinal5_case_5_2_row_2_1_1
  · exact rightFinal5_case_5_2_row_2_1_2
  · exact rightFinal5_case_5_2_row_2_1_3
  · exact rightFinal5_case_5_2_row_3_0_0
  · exact rightFinal5_case_5_2_row_3_0_1
  · exact rightFinal5_case_5_2_row_3_0_2
  · exact rightFinal5_case_5_2_row_3_0_3
  · exact rightFinal5_case_5_2_row_3_1_0
  · exact rightFinal5_case_5_2_row_3_1_1
  · exact rightFinal5_case_5_2_row_3_1_2
  · exact rightFinal5_case_5_2_row_3_1_3

set_option backward.isDefEq.respectTransparency false in
theorem rightFinal5_case_5_2 : ((-1 : ℤ) ^ (rightScaleBit 5 5 2).val * positiveScale (rightScaleExponent 5 5 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 2 5 : ℤ)) • outerLeftZ 5 5 2 = negativeScale (rightScaleExponent 5 5 2) • (associatorZ 2 5 5 * right2Middle5 5 2) := by
  simpa only [HexagonAtoms552.assocABC_eq,
    HexagonAtoms552.outerABC_eq,
    HexagonAtoms552.assocBAC_eq,
    HexagonAtoms552.innerABC_eq,
    HexagonAtoms552.innerRightABC_eq,
    HexagonAtoms552.inverseACB_eq,
    HexagonAtoms552.innerACB_eq,
    HexagonAtoms552.assocBCA_eq,
    HexagonAtoms552.innerRightBAC_eq,
    HexagonAtoms552.assocCAB_eq,
    HexagonAtoms552.outerLeftABC_eq,
    HexagonRowColumn552.assocBAC_alias,
    HexagonRowColumn552.innerRightBAC_alias,
    HexagonRowColumn552.product0_eq,
    HexagonRowColumn552.product1_eq,
    HexagonRowColumn552.product2_eq,
    HexagonRowColumn552.product3_eq,
    HexagonRowColumn552.product4_eq,
    HexagonRowColumn552.product5_eq,
    HexagonRowColumn552.product6_eq,
    HexagonRowColumn552.product7_eq] using rightFinal5_case_5_2_checked

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonCases5
