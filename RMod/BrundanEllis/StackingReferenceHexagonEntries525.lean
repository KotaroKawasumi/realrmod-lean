import RMod.BrundanEllis.StackingReferenceHexagonMiddle5
import RMod.BrundanEllis.StackingReferenceSparseMatrixCheck
import RMod.BrundanEllis.StackingReferenceHexagonAtoms525
import RMod.BrundanEllis.StackingReferenceHexagonRowColumn525

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

private theorem left0Middle5_eq_case_2_5_row_0_0_0 : (left0Middle5 2 5) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn525.rows_outerABC HexagonRowColumn525.cols_assocABC) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_2_5_row_0_0_1 : (left0Middle5 2 5) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn525.rows_outerABC HexagonRowColumn525.cols_assocABC) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_2_5_row_0_0_2 : (left0Middle5 2 5) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn525.rows_outerABC HexagonRowColumn525.cols_assocABC) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_2_5_row_0_0_3 : (left0Middle5 2 5) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn525.rows_outerABC HexagonRowColumn525.cols_assocABC) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_2_5_row_0_1_0 : (left0Middle5 2 5) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn525.rows_outerABC HexagonRowColumn525.cols_assocABC) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_2_5_row_0_1_1 : (left0Middle5 2 5) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn525.rows_outerABC HexagonRowColumn525.cols_assocABC) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_2_5_row_0_1_2 : (left0Middle5 2 5) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn525.rows_outerABC HexagonRowColumn525.cols_assocABC) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_2_5_row_0_1_3 : (left0Middle5 2 5) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn525.rows_outerABC HexagonRowColumn525.cols_assocABC) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_2_5_row_1_0_0 : (left0Middle5 2 5) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn525.rows_outerABC HexagonRowColumn525.cols_assocABC) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_2_5_row_1_0_1 : (left0Middle5 2 5) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn525.rows_outerABC HexagonRowColumn525.cols_assocABC) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_2_5_row_1_0_2 : (left0Middle5 2 5) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn525.rows_outerABC HexagonRowColumn525.cols_assocABC) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_2_5_row_1_0_3 : (left0Middle5 2 5) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn525.rows_outerABC HexagonRowColumn525.cols_assocABC) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_2_5_row_1_1_0 : (left0Middle5 2 5) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn525.rows_outerABC HexagonRowColumn525.cols_assocABC) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_2_5_row_1_1_1 : (left0Middle5 2 5) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn525.rows_outerABC HexagonRowColumn525.cols_assocABC) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_2_5_row_1_1_2 : (left0Middle5 2 5) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn525.rows_outerABC HexagonRowColumn525.cols_assocABC) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_2_5_row_1_1_3 : (left0Middle5 2 5) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn525.rows_outerABC HexagonRowColumn525.cols_assocABC) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_2_5_row_2_0_0 : (left0Middle5 2 5) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn525.rows_outerABC HexagonRowColumn525.cols_assocABC) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_2_5_row_2_0_1 : (left0Middle5 2 5) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn525.rows_outerABC HexagonRowColumn525.cols_assocABC) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_2_5_row_2_0_2 : (left0Middle5 2 5) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn525.rows_outerABC HexagonRowColumn525.cols_assocABC) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_2_5_row_2_0_3 : (left0Middle5 2 5) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn525.rows_outerABC HexagonRowColumn525.cols_assocABC) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_2_5_row_2_1_0 : (left0Middle5 2 5) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn525.rows_outerABC HexagonRowColumn525.cols_assocABC) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_2_5_row_2_1_1 : (left0Middle5 2 5) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn525.rows_outerABC HexagonRowColumn525.cols_assocABC) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_2_5_row_2_1_2 : (left0Middle5 2 5) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn525.rows_outerABC HexagonRowColumn525.cols_assocABC) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_2_5_row_2_1_3 : (left0Middle5 2 5) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn525.rows_outerABC HexagonRowColumn525.cols_assocABC) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_2_5_row_3_0_0 : (left0Middle5 2 5) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn525.rows_outerABC HexagonRowColumn525.cols_assocABC) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_2_5_row_3_0_1 : (left0Middle5 2 5) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn525.rows_outerABC HexagonRowColumn525.cols_assocABC) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_2_5_row_3_0_2 : (left0Middle5 2 5) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn525.rows_outerABC HexagonRowColumn525.cols_assocABC) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_2_5_row_3_0_3 : (left0Middle5 2 5) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn525.rows_outerABC HexagonRowColumn525.cols_assocABC) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_2_5_row_3_1_0 : (left0Middle5 2 5) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn525.rows_outerABC HexagonRowColumn525.cols_assocABC) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_2_5_row_3_1_1 : (left0Middle5 2 5) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn525.rows_outerABC HexagonRowColumn525.cols_assocABC) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_2_5_row_3_1_2 : (left0Middle5 2 5) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn525.rows_outerABC HexagonRowColumn525.cols_assocABC) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_2_5_row_3_1_3 : (left0Middle5 2 5) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn525.rows_outerABC HexagonRowColumn525.cols_assocABC) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_2_5_checked : left0Middle5 2 5 = rowColumnMul HexagonRowColumn525.rows_outerABC HexagonRowColumn525.cols_assocABC := by
  funext r
  fin_cases r
  · exact left0Middle5_eq_case_2_5_row_0_0_0
  · exact left0Middle5_eq_case_2_5_row_0_0_1
  · exact left0Middle5_eq_case_2_5_row_0_0_2
  · exact left0Middle5_eq_case_2_5_row_0_0_3
  · exact left0Middle5_eq_case_2_5_row_0_1_0
  · exact left0Middle5_eq_case_2_5_row_0_1_1
  · exact left0Middle5_eq_case_2_5_row_0_1_2
  · exact left0Middle5_eq_case_2_5_row_0_1_3
  · exact left0Middle5_eq_case_2_5_row_1_0_0
  · exact left0Middle5_eq_case_2_5_row_1_0_1
  · exact left0Middle5_eq_case_2_5_row_1_0_2
  · exact left0Middle5_eq_case_2_5_row_1_0_3
  · exact left0Middle5_eq_case_2_5_row_1_1_0
  · exact left0Middle5_eq_case_2_5_row_1_1_1
  · exact left0Middle5_eq_case_2_5_row_1_1_2
  · exact left0Middle5_eq_case_2_5_row_1_1_3
  · exact left0Middle5_eq_case_2_5_row_2_0_0
  · exact left0Middle5_eq_case_2_5_row_2_0_1
  · exact left0Middle5_eq_case_2_5_row_2_0_2
  · exact left0Middle5_eq_case_2_5_row_2_0_3
  · exact left0Middle5_eq_case_2_5_row_2_1_0
  · exact left0Middle5_eq_case_2_5_row_2_1_1
  · exact left0Middle5_eq_case_2_5_row_2_1_2
  · exact left0Middle5_eq_case_2_5_row_2_1_3
  · exact left0Middle5_eq_case_2_5_row_3_0_0
  · exact left0Middle5_eq_case_2_5_row_3_0_1
  · exact left0Middle5_eq_case_2_5_row_3_0_2
  · exact left0Middle5_eq_case_2_5_row_3_0_3
  · exact left0Middle5_eq_case_2_5_row_3_1_0
  · exact left0Middle5_eq_case_2_5_row_3_1_1
  · exact left0Middle5_eq_case_2_5_row_3_1_2
  · exact left0Middle5_eq_case_2_5_row_3_1_3

set_option backward.isDefEq.respectTransparency false in
theorem left0Middle5_eq_case_2_5 : left0Middle5 2 5 = outerRightZ 5 2 5 * associatorZ 5 2 5 := by
  simpa only [HexagonAtoms525.assocABC_eq,
    HexagonAtoms525.outerABC_eq,
    HexagonAtoms525.assocBAC_eq,
    HexagonAtoms525.innerABC_eq,
    HexagonAtoms525.innerRightABC_eq,
    HexagonAtoms525.inverseACB_eq,
    HexagonAtoms525.innerACB_eq,
    HexagonAtoms525.assocBCA_eq,
    HexagonAtoms525.innerRightBAC_eq,
    HexagonAtoms525.assocCAB_eq,
    HexagonAtoms525.outerLeftABC_eq,
    HexagonRowColumn525.assocBCA_alias,
    HexagonRowColumn525.product0_eq,
    HexagonRowColumn525.product1_eq,
    HexagonRowColumn525.product2_eq,
    HexagonRowColumn525.product3_eq,
    HexagonRowColumn525.product4_eq,
    HexagonRowColumn525.product5_eq,
    HexagonRowColumn525.product6_eq,
    HexagonRowColumn525.product7_eq] using left0Middle5_eq_case_2_5_checked

private theorem left1Middle5_eq_case_2_5_row_0_0_0 : (left1Middle5 2 5) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms525.assocBAC) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_2_5_row_0_0_1 : (left1Middle5 2 5) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms525.assocBAC) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_2_5_row_0_0_2 : (left1Middle5 2 5) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms525.assocBAC) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_2_5_row_0_0_3 : (left1Middle5 2 5) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms525.assocBAC) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_2_5_row_0_1_0 : (left1Middle5 2 5) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms525.assocBAC) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_2_5_row_0_1_1 : (left1Middle5 2 5) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms525.assocBAC) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_2_5_row_0_1_2 : (left1Middle5 2 5) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms525.assocBAC) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_2_5_row_0_1_3 : (left1Middle5 2 5) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms525.assocBAC) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_2_5_row_1_0_0 : (left1Middle5 2 5) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms525.assocBAC) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_2_5_row_1_0_1 : (left1Middle5 2 5) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms525.assocBAC) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_2_5_row_1_0_2 : (left1Middle5 2 5) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms525.assocBAC) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_2_5_row_1_0_3 : (left1Middle5 2 5) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms525.assocBAC) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_2_5_row_1_1_0 : (left1Middle5 2 5) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms525.assocBAC) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_2_5_row_1_1_1 : (left1Middle5 2 5) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms525.assocBAC) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_2_5_row_1_1_2 : (left1Middle5 2 5) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms525.assocBAC) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_2_5_row_1_1_3 : (left1Middle5 2 5) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms525.assocBAC) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_2_5_row_2_0_0 : (left1Middle5 2 5) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms525.assocBAC) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_2_5_row_2_0_1 : (left1Middle5 2 5) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms525.assocBAC) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_2_5_row_2_0_2 : (left1Middle5 2 5) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms525.assocBAC) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_2_5_row_2_0_3 : (left1Middle5 2 5) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms525.assocBAC) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_2_5_row_2_1_0 : (left1Middle5 2 5) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms525.assocBAC) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_2_5_row_2_1_1 : (left1Middle5 2 5) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms525.assocBAC) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_2_5_row_2_1_2 : (left1Middle5 2 5) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms525.assocBAC) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_2_5_row_2_1_3 : (left1Middle5 2 5) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms525.assocBAC) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_2_5_row_3_0_0 : (left1Middle5 2 5) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms525.assocBAC) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_2_5_row_3_0_1 : (left1Middle5 2 5) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms525.assocBAC) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_2_5_row_3_0_2 : (left1Middle5 2 5) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms525.assocBAC) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_2_5_row_3_0_3 : (left1Middle5 2 5) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms525.assocBAC) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_2_5_row_3_1_0 : (left1Middle5 2 5) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms525.assocBAC) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_2_5_row_3_1_1 : (left1Middle5 2 5) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms525.assocBAC) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_2_5_row_3_1_2 : (left1Middle5 2 5) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms525.assocBAC) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_2_5_row_3_1_3 : (left1Middle5 2 5) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms525.assocBAC) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_2_5_checked : left1Middle5 2 5 = HexagonAtoms525.assocBAC := by
  funext r
  fin_cases r
  · exact left1Middle5_eq_case_2_5_row_0_0_0
  · exact left1Middle5_eq_case_2_5_row_0_0_1
  · exact left1Middle5_eq_case_2_5_row_0_0_2
  · exact left1Middle5_eq_case_2_5_row_0_0_3
  · exact left1Middle5_eq_case_2_5_row_0_1_0
  · exact left1Middle5_eq_case_2_5_row_0_1_1
  · exact left1Middle5_eq_case_2_5_row_0_1_2
  · exact left1Middle5_eq_case_2_5_row_0_1_3
  · exact left1Middle5_eq_case_2_5_row_1_0_0
  · exact left1Middle5_eq_case_2_5_row_1_0_1
  · exact left1Middle5_eq_case_2_5_row_1_0_2
  · exact left1Middle5_eq_case_2_5_row_1_0_3
  · exact left1Middle5_eq_case_2_5_row_1_1_0
  · exact left1Middle5_eq_case_2_5_row_1_1_1
  · exact left1Middle5_eq_case_2_5_row_1_1_2
  · exact left1Middle5_eq_case_2_5_row_1_1_3
  · exact left1Middle5_eq_case_2_5_row_2_0_0
  · exact left1Middle5_eq_case_2_5_row_2_0_1
  · exact left1Middle5_eq_case_2_5_row_2_0_2
  · exact left1Middle5_eq_case_2_5_row_2_0_3
  · exact left1Middle5_eq_case_2_5_row_2_1_0
  · exact left1Middle5_eq_case_2_5_row_2_1_1
  · exact left1Middle5_eq_case_2_5_row_2_1_2
  · exact left1Middle5_eq_case_2_5_row_2_1_3
  · exact left1Middle5_eq_case_2_5_row_3_0_0
  · exact left1Middle5_eq_case_2_5_row_3_0_1
  · exact left1Middle5_eq_case_2_5_row_3_0_2
  · exact left1Middle5_eq_case_2_5_row_3_0_3
  · exact left1Middle5_eq_case_2_5_row_3_1_0
  · exact left1Middle5_eq_case_2_5_row_3_1_1
  · exact left1Middle5_eq_case_2_5_row_3_1_2
  · exact left1Middle5_eq_case_2_5_row_3_1_3

set_option backward.isDefEq.respectTransparency false in
theorem left1Middle5_eq_case_2_5 : left1Middle5 2 5 = associatorZ 2 5 5 * innerLeftZ 5 2 5 := by
  simpa only [HexagonAtoms525.assocABC_eq,
    HexagonAtoms525.outerABC_eq,
    HexagonAtoms525.assocBAC_eq,
    HexagonAtoms525.innerABC_eq,
    HexagonAtoms525.innerRightABC_eq,
    HexagonAtoms525.inverseACB_eq,
    HexagonAtoms525.innerACB_eq,
    HexagonAtoms525.assocBCA_eq,
    HexagonAtoms525.innerRightBAC_eq,
    HexagonAtoms525.assocCAB_eq,
    HexagonAtoms525.outerLeftABC_eq,
    HexagonRowColumn525.assocBCA_alias,
    HexagonRowColumn525.product0_eq,
    HexagonRowColumn525.product1_eq,
    HexagonRowColumn525.product2_eq,
    HexagonRowColumn525.product3_eq,
    HexagonRowColumn525.product4_eq,
    HexagonRowColumn525.product5_eq,
    HexagonRowColumn525.product6_eq,
    HexagonRowColumn525.product7_eq] using left1Middle5_eq_case_2_5_checked

private theorem right0Middle5_eq_case_2_5_row_0_0_0 : (right0Middle5 2 5) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms525.assocABC) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_2_5_row_0_0_1 : (right0Middle5 2 5) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms525.assocABC) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_2_5_row_0_0_2 : (right0Middle5 2 5) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms525.assocABC) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_2_5_row_0_0_3 : (right0Middle5 2 5) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms525.assocABC) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_2_5_row_0_1_0 : (right0Middle5 2 5) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms525.assocABC) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_2_5_row_0_1_1 : (right0Middle5 2 5) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms525.assocABC) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_2_5_row_0_1_2 : (right0Middle5 2 5) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms525.assocABC) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_2_5_row_0_1_3 : (right0Middle5 2 5) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms525.assocABC) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_2_5_row_1_0_0 : (right0Middle5 2 5) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms525.assocABC) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_2_5_row_1_0_1 : (right0Middle5 2 5) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms525.assocABC) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_2_5_row_1_0_2 : (right0Middle5 2 5) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms525.assocABC) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_2_5_row_1_0_3 : (right0Middle5 2 5) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms525.assocABC) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_2_5_row_1_1_0 : (right0Middle5 2 5) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms525.assocABC) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_2_5_row_1_1_1 : (right0Middle5 2 5) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms525.assocABC) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_2_5_row_1_1_2 : (right0Middle5 2 5) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms525.assocABC) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_2_5_row_1_1_3 : (right0Middle5 2 5) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms525.assocABC) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_2_5_row_2_0_0 : (right0Middle5 2 5) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms525.assocABC) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_2_5_row_2_0_1 : (right0Middle5 2 5) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms525.assocABC) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_2_5_row_2_0_2 : (right0Middle5 2 5) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms525.assocABC) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_2_5_row_2_0_3 : (right0Middle5 2 5) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms525.assocABC) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_2_5_row_2_1_0 : (right0Middle5 2 5) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms525.assocABC) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_2_5_row_2_1_1 : (right0Middle5 2 5) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms525.assocABC) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_2_5_row_2_1_2 : (right0Middle5 2 5) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms525.assocABC) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_2_5_row_2_1_3 : (right0Middle5 2 5) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms525.assocABC) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_2_5_row_3_0_0 : (right0Middle5 2 5) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms525.assocABC) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_2_5_row_3_0_1 : (right0Middle5 2 5) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms525.assocABC) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_2_5_row_3_0_2 : (right0Middle5 2 5) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms525.assocABC) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_2_5_row_3_0_3 : (right0Middle5 2 5) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms525.assocABC) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_2_5_row_3_1_0 : (right0Middle5 2 5) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms525.assocABC) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_2_5_row_3_1_1 : (right0Middle5 2 5) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms525.assocABC) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_2_5_row_3_1_2 : (right0Middle5 2 5) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms525.assocABC) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_2_5_row_3_1_3 : (right0Middle5 2 5) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms525.assocABC) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_2_5_checked : right0Middle5 2 5 = HexagonAtoms525.assocABC := by
  funext r
  fin_cases r
  · exact right0Middle5_eq_case_2_5_row_0_0_0
  · exact right0Middle5_eq_case_2_5_row_0_0_1
  · exact right0Middle5_eq_case_2_5_row_0_0_2
  · exact right0Middle5_eq_case_2_5_row_0_0_3
  · exact right0Middle5_eq_case_2_5_row_0_1_0
  · exact right0Middle5_eq_case_2_5_row_0_1_1
  · exact right0Middle5_eq_case_2_5_row_0_1_2
  · exact right0Middle5_eq_case_2_5_row_0_1_3
  · exact right0Middle5_eq_case_2_5_row_1_0_0
  · exact right0Middle5_eq_case_2_5_row_1_0_1
  · exact right0Middle5_eq_case_2_5_row_1_0_2
  · exact right0Middle5_eq_case_2_5_row_1_0_3
  · exact right0Middle5_eq_case_2_5_row_1_1_0
  · exact right0Middle5_eq_case_2_5_row_1_1_1
  · exact right0Middle5_eq_case_2_5_row_1_1_2
  · exact right0Middle5_eq_case_2_5_row_1_1_3
  · exact right0Middle5_eq_case_2_5_row_2_0_0
  · exact right0Middle5_eq_case_2_5_row_2_0_1
  · exact right0Middle5_eq_case_2_5_row_2_0_2
  · exact right0Middle5_eq_case_2_5_row_2_0_3
  · exact right0Middle5_eq_case_2_5_row_2_1_0
  · exact right0Middle5_eq_case_2_5_row_2_1_1
  · exact right0Middle5_eq_case_2_5_row_2_1_2
  · exact right0Middle5_eq_case_2_5_row_2_1_3
  · exact right0Middle5_eq_case_2_5_row_3_0_0
  · exact right0Middle5_eq_case_2_5_row_3_0_1
  · exact right0Middle5_eq_case_2_5_row_3_0_2
  · exact right0Middle5_eq_case_2_5_row_3_0_3
  · exact right0Middle5_eq_case_2_5_row_3_1_0
  · exact right0Middle5_eq_case_2_5_row_3_1_1
  · exact right0Middle5_eq_case_2_5_row_3_1_2
  · exact right0Middle5_eq_case_2_5_row_3_1_3

set_option backward.isDefEq.respectTransparency false in
theorem right0Middle5_eq_case_2_5 : right0Middle5 2 5 = innerRightZ 5 2 5 * associatorZ 5 2 5 := by
  simpa only [HexagonAtoms525.assocABC_eq,
    HexagonAtoms525.outerABC_eq,
    HexagonAtoms525.assocBAC_eq,
    HexagonAtoms525.innerABC_eq,
    HexagonAtoms525.innerRightABC_eq,
    HexagonAtoms525.inverseACB_eq,
    HexagonAtoms525.innerACB_eq,
    HexagonAtoms525.assocBCA_eq,
    HexagonAtoms525.innerRightBAC_eq,
    HexagonAtoms525.assocCAB_eq,
    HexagonAtoms525.outerLeftABC_eq,
    HexagonRowColumn525.assocBCA_alias,
    HexagonRowColumn525.product0_eq,
    HexagonRowColumn525.product1_eq,
    HexagonRowColumn525.product2_eq,
    HexagonRowColumn525.product3_eq,
    HexagonRowColumn525.product4_eq,
    HexagonRowColumn525.product5_eq,
    HexagonRowColumn525.product6_eq,
    HexagonRowColumn525.product7_eq] using right0Middle5_eq_case_2_5_checked

private theorem right1Middle5_eq_case_2_5_row_0_0_0 : (right1Middle5 2 5) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn525.rows_inverseACB HexagonRowColumn525.cols_right0) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_2_5_row_0_0_1 : (right1Middle5 2 5) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn525.rows_inverseACB HexagonRowColumn525.cols_right0) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_2_5_row_0_0_2 : (right1Middle5 2 5) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn525.rows_inverseACB HexagonRowColumn525.cols_right0) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_2_5_row_0_0_3 : (right1Middle5 2 5) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn525.rows_inverseACB HexagonRowColumn525.cols_right0) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_2_5_row_0_1_0 : (right1Middle5 2 5) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn525.rows_inverseACB HexagonRowColumn525.cols_right0) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_2_5_row_0_1_1 : (right1Middle5 2 5) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn525.rows_inverseACB HexagonRowColumn525.cols_right0) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_2_5_row_0_1_2 : (right1Middle5 2 5) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn525.rows_inverseACB HexagonRowColumn525.cols_right0) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_2_5_row_0_1_3 : (right1Middle5 2 5) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn525.rows_inverseACB HexagonRowColumn525.cols_right0) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_2_5_row_1_0_0 : (right1Middle5 2 5) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn525.rows_inverseACB HexagonRowColumn525.cols_right0) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_2_5_row_1_0_1 : (right1Middle5 2 5) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn525.rows_inverseACB HexagonRowColumn525.cols_right0) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_2_5_row_1_0_2 : (right1Middle5 2 5) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn525.rows_inverseACB HexagonRowColumn525.cols_right0) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_2_5_row_1_0_3 : (right1Middle5 2 5) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn525.rows_inverseACB HexagonRowColumn525.cols_right0) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_2_5_row_1_1_0 : (right1Middle5 2 5) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn525.rows_inverseACB HexagonRowColumn525.cols_right0) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_2_5_row_1_1_1 : (right1Middle5 2 5) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn525.rows_inverseACB HexagonRowColumn525.cols_right0) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_2_5_row_1_1_2 : (right1Middle5 2 5) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn525.rows_inverseACB HexagonRowColumn525.cols_right0) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_2_5_row_1_1_3 : (right1Middle5 2 5) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn525.rows_inverseACB HexagonRowColumn525.cols_right0) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_2_5_row_2_0_0 : (right1Middle5 2 5) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn525.rows_inverseACB HexagonRowColumn525.cols_right0) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_2_5_row_2_0_1 : (right1Middle5 2 5) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn525.rows_inverseACB HexagonRowColumn525.cols_right0) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_2_5_row_2_0_2 : (right1Middle5 2 5) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn525.rows_inverseACB HexagonRowColumn525.cols_right0) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_2_5_row_2_0_3 : (right1Middle5 2 5) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn525.rows_inverseACB HexagonRowColumn525.cols_right0) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_2_5_row_2_1_0 : (right1Middle5 2 5) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn525.rows_inverseACB HexagonRowColumn525.cols_right0) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_2_5_row_2_1_1 : (right1Middle5 2 5) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn525.rows_inverseACB HexagonRowColumn525.cols_right0) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_2_5_row_2_1_2 : (right1Middle5 2 5) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn525.rows_inverseACB HexagonRowColumn525.cols_right0) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_2_5_row_2_1_3 : (right1Middle5 2 5) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn525.rows_inverseACB HexagonRowColumn525.cols_right0) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_2_5_row_3_0_0 : (right1Middle5 2 5) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn525.rows_inverseACB HexagonRowColumn525.cols_right0) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_2_5_row_3_0_1 : (right1Middle5 2 5) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn525.rows_inverseACB HexagonRowColumn525.cols_right0) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_2_5_row_3_0_2 : (right1Middle5 2 5) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn525.rows_inverseACB HexagonRowColumn525.cols_right0) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_2_5_row_3_0_3 : (right1Middle5 2 5) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn525.rows_inverseACB HexagonRowColumn525.cols_right0) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_2_5_row_3_1_0 : (right1Middle5 2 5) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn525.rows_inverseACB HexagonRowColumn525.cols_right0) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_2_5_row_3_1_1 : (right1Middle5 2 5) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn525.rows_inverseACB HexagonRowColumn525.cols_right0) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_2_5_row_3_1_2 : (right1Middle5 2 5) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn525.rows_inverseACB HexagonRowColumn525.cols_right0) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_2_5_row_3_1_3 : (right1Middle5 2 5) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn525.rows_inverseACB HexagonRowColumn525.cols_right0) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_2_5_checked : right1Middle5 2 5 = rowColumnMul HexagonRowColumn525.rows_inverseACB HexagonRowColumn525.cols_right0 := by
  funext r
  fin_cases r
  · exact right1Middle5_eq_case_2_5_row_0_0_0
  · exact right1Middle5_eq_case_2_5_row_0_0_1
  · exact right1Middle5_eq_case_2_5_row_0_0_2
  · exact right1Middle5_eq_case_2_5_row_0_0_3
  · exact right1Middle5_eq_case_2_5_row_0_1_0
  · exact right1Middle5_eq_case_2_5_row_0_1_1
  · exact right1Middle5_eq_case_2_5_row_0_1_2
  · exact right1Middle5_eq_case_2_5_row_0_1_3
  · exact right1Middle5_eq_case_2_5_row_1_0_0
  · exact right1Middle5_eq_case_2_5_row_1_0_1
  · exact right1Middle5_eq_case_2_5_row_1_0_2
  · exact right1Middle5_eq_case_2_5_row_1_0_3
  · exact right1Middle5_eq_case_2_5_row_1_1_0
  · exact right1Middle5_eq_case_2_5_row_1_1_1
  · exact right1Middle5_eq_case_2_5_row_1_1_2
  · exact right1Middle5_eq_case_2_5_row_1_1_3
  · exact right1Middle5_eq_case_2_5_row_2_0_0
  · exact right1Middle5_eq_case_2_5_row_2_0_1
  · exact right1Middle5_eq_case_2_5_row_2_0_2
  · exact right1Middle5_eq_case_2_5_row_2_0_3
  · exact right1Middle5_eq_case_2_5_row_2_1_0
  · exact right1Middle5_eq_case_2_5_row_2_1_1
  · exact right1Middle5_eq_case_2_5_row_2_1_2
  · exact right1Middle5_eq_case_2_5_row_2_1_3
  · exact right1Middle5_eq_case_2_5_row_3_0_0
  · exact right1Middle5_eq_case_2_5_row_3_0_1
  · exact right1Middle5_eq_case_2_5_row_3_0_2
  · exact right1Middle5_eq_case_2_5_row_3_0_3
  · exact right1Middle5_eq_case_2_5_row_3_1_0
  · exact right1Middle5_eq_case_2_5_row_3_1_1
  · exact right1Middle5_eq_case_2_5_row_3_1_2
  · exact right1Middle5_eq_case_2_5_row_3_1_3

set_option backward.isDefEq.respectTransparency false in
theorem right1Middle5_eq_case_2_5 : right1Middle5 2 5 = associatorInverseZ 5 5 2 * right0Middle5 2 5 := by
  simpa only [HexagonAtoms525.assocABC_eq,
    HexagonAtoms525.outerABC_eq,
    HexagonAtoms525.assocBAC_eq,
    HexagonAtoms525.innerABC_eq,
    HexagonAtoms525.innerRightABC_eq,
    HexagonAtoms525.inverseACB_eq,
    HexagonAtoms525.innerACB_eq,
    HexagonAtoms525.assocBCA_eq,
    HexagonAtoms525.innerRightBAC_eq,
    HexagonAtoms525.assocCAB_eq,
    HexagonAtoms525.outerLeftABC_eq,
    HexagonRowColumn525.assocBCA_alias,
    HexagonRowColumn525.product0_eq,
    HexagonRowColumn525.product1_eq,
    HexagonRowColumn525.product2_eq,
    HexagonRowColumn525.product3_eq,
    HexagonRowColumn525.product4_eq,
    HexagonRowColumn525.product5_eq,
    HexagonRowColumn525.product6_eq,
    HexagonRowColumn525.product7_eq] using right1Middle5_eq_case_2_5_checked

private theorem right2Middle5_eq_case_2_5_row_0_0_0 : (right2Middle5 2 5) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn525.rows_innerACB HexagonRowColumn525.cols_right1) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_2_5_row_0_0_1 : (right2Middle5 2 5) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn525.rows_innerACB HexagonRowColumn525.cols_right1) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_2_5_row_0_0_2 : (right2Middle5 2 5) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn525.rows_innerACB HexagonRowColumn525.cols_right1) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_2_5_row_0_0_3 : (right2Middle5 2 5) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn525.rows_innerACB HexagonRowColumn525.cols_right1) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_2_5_row_0_1_0 : (right2Middle5 2 5) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn525.rows_innerACB HexagonRowColumn525.cols_right1) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_2_5_row_0_1_1 : (right2Middle5 2 5) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn525.rows_innerACB HexagonRowColumn525.cols_right1) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_2_5_row_0_1_2 : (right2Middle5 2 5) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn525.rows_innerACB HexagonRowColumn525.cols_right1) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_2_5_row_0_1_3 : (right2Middle5 2 5) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn525.rows_innerACB HexagonRowColumn525.cols_right1) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_2_5_row_1_0_0 : (right2Middle5 2 5) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn525.rows_innerACB HexagonRowColumn525.cols_right1) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_2_5_row_1_0_1 : (right2Middle5 2 5) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn525.rows_innerACB HexagonRowColumn525.cols_right1) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_2_5_row_1_0_2 : (right2Middle5 2 5) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn525.rows_innerACB HexagonRowColumn525.cols_right1) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_2_5_row_1_0_3 : (right2Middle5 2 5) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn525.rows_innerACB HexagonRowColumn525.cols_right1) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_2_5_row_1_1_0 : (right2Middle5 2 5) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn525.rows_innerACB HexagonRowColumn525.cols_right1) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_2_5_row_1_1_1 : (right2Middle5 2 5) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn525.rows_innerACB HexagonRowColumn525.cols_right1) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_2_5_row_1_1_2 : (right2Middle5 2 5) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn525.rows_innerACB HexagonRowColumn525.cols_right1) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_2_5_row_1_1_3 : (right2Middle5 2 5) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn525.rows_innerACB HexagonRowColumn525.cols_right1) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_2_5_row_2_0_0 : (right2Middle5 2 5) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn525.rows_innerACB HexagonRowColumn525.cols_right1) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_2_5_row_2_0_1 : (right2Middle5 2 5) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn525.rows_innerACB HexagonRowColumn525.cols_right1) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_2_5_row_2_0_2 : (right2Middle5 2 5) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn525.rows_innerACB HexagonRowColumn525.cols_right1) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_2_5_row_2_0_3 : (right2Middle5 2 5) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn525.rows_innerACB HexagonRowColumn525.cols_right1) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_2_5_row_2_1_0 : (right2Middle5 2 5) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn525.rows_innerACB HexagonRowColumn525.cols_right1) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_2_5_row_2_1_1 : (right2Middle5 2 5) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn525.rows_innerACB HexagonRowColumn525.cols_right1) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_2_5_row_2_1_2 : (right2Middle5 2 5) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn525.rows_innerACB HexagonRowColumn525.cols_right1) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_2_5_row_2_1_3 : (right2Middle5 2 5) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn525.rows_innerACB HexagonRowColumn525.cols_right1) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_2_5_row_3_0_0 : (right2Middle5 2 5) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn525.rows_innerACB HexagonRowColumn525.cols_right1) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_2_5_row_3_0_1 : (right2Middle5 2 5) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn525.rows_innerACB HexagonRowColumn525.cols_right1) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_2_5_row_3_0_2 : (right2Middle5 2 5) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn525.rows_innerACB HexagonRowColumn525.cols_right1) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_2_5_row_3_0_3 : (right2Middle5 2 5) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn525.rows_innerACB HexagonRowColumn525.cols_right1) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_2_5_row_3_1_0 : (right2Middle5 2 5) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn525.rows_innerACB HexagonRowColumn525.cols_right1) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_2_5_row_3_1_1 : (right2Middle5 2 5) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn525.rows_innerACB HexagonRowColumn525.cols_right1) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_2_5_row_3_1_2 : (right2Middle5 2 5) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn525.rows_innerACB HexagonRowColumn525.cols_right1) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_2_5_row_3_1_3 : (right2Middle5 2 5) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn525.rows_innerACB HexagonRowColumn525.cols_right1) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_2_5_checked : right2Middle5 2 5 = rowColumnMul HexagonRowColumn525.rows_innerACB HexagonRowColumn525.cols_right1 := by
  funext r
  fin_cases r
  · exact right2Middle5_eq_case_2_5_row_0_0_0
  · exact right2Middle5_eq_case_2_5_row_0_0_1
  · exact right2Middle5_eq_case_2_5_row_0_0_2
  · exact right2Middle5_eq_case_2_5_row_0_0_3
  · exact right2Middle5_eq_case_2_5_row_0_1_0
  · exact right2Middle5_eq_case_2_5_row_0_1_1
  · exact right2Middle5_eq_case_2_5_row_0_1_2
  · exact right2Middle5_eq_case_2_5_row_0_1_3
  · exact right2Middle5_eq_case_2_5_row_1_0_0
  · exact right2Middle5_eq_case_2_5_row_1_0_1
  · exact right2Middle5_eq_case_2_5_row_1_0_2
  · exact right2Middle5_eq_case_2_5_row_1_0_3
  · exact right2Middle5_eq_case_2_5_row_1_1_0
  · exact right2Middle5_eq_case_2_5_row_1_1_1
  · exact right2Middle5_eq_case_2_5_row_1_1_2
  · exact right2Middle5_eq_case_2_5_row_1_1_3
  · exact right2Middle5_eq_case_2_5_row_2_0_0
  · exact right2Middle5_eq_case_2_5_row_2_0_1
  · exact right2Middle5_eq_case_2_5_row_2_0_2
  · exact right2Middle5_eq_case_2_5_row_2_0_3
  · exact right2Middle5_eq_case_2_5_row_2_1_0
  · exact right2Middle5_eq_case_2_5_row_2_1_1
  · exact right2Middle5_eq_case_2_5_row_2_1_2
  · exact right2Middle5_eq_case_2_5_row_2_1_3
  · exact right2Middle5_eq_case_2_5_row_3_0_0
  · exact right2Middle5_eq_case_2_5_row_3_0_1
  · exact right2Middle5_eq_case_2_5_row_3_0_2
  · exact right2Middle5_eq_case_2_5_row_3_0_3
  · exact right2Middle5_eq_case_2_5_row_3_1_0
  · exact right2Middle5_eq_case_2_5_row_3_1_1
  · exact right2Middle5_eq_case_2_5_row_3_1_2
  · exact right2Middle5_eq_case_2_5_row_3_1_3

set_option backward.isDefEq.respectTransparency false in
theorem right2Middle5_eq_case_2_5 : right2Middle5 2 5 = innerLeftZ 5 5 2 * right1Middle5 2 5 := by
  simpa only [HexagonAtoms525.assocABC_eq,
    HexagonAtoms525.outerABC_eq,
    HexagonAtoms525.assocBAC_eq,
    HexagonAtoms525.innerABC_eq,
    HexagonAtoms525.innerRightABC_eq,
    HexagonAtoms525.inverseACB_eq,
    HexagonAtoms525.innerACB_eq,
    HexagonAtoms525.assocBCA_eq,
    HexagonAtoms525.innerRightBAC_eq,
    HexagonAtoms525.assocCAB_eq,
    HexagonAtoms525.outerLeftABC_eq,
    HexagonRowColumn525.assocBCA_alias,
    HexagonRowColumn525.product0_eq,
    HexagonRowColumn525.product1_eq,
    HexagonRowColumn525.product2_eq,
    HexagonRowColumn525.product3_eq,
    HexagonRowColumn525.product4_eq,
    HexagonRowColumn525.product5_eq,
    HexagonRowColumn525.product6_eq,
    HexagonRowColumn525.product7_eq] using right2Middle5_eq_case_2_5_checked

private theorem leftFinal5_case_2_5_row_0_0_0 : (((-1 : ℤ) ^ (leftScaleBit 5 2 5).val * positiveScale (leftScaleExponent 5 2 5)) •
      (rowColumnMul HexagonRowColumn525.rows_assocBAC HexagonRowColumn525.cols_left0)) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 5 2 5) • (rowColumnMul HexagonRowColumn525.rows_innerRightBAC HexagonRowColumn525.cols_left1)) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_2_5_row_0_0_1 : (((-1 : ℤ) ^ (leftScaleBit 5 2 5).val * positiveScale (leftScaleExponent 5 2 5)) •
      (rowColumnMul HexagonRowColumn525.rows_assocBAC HexagonRowColumn525.cols_left0)) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 5 2 5) • (rowColumnMul HexagonRowColumn525.rows_innerRightBAC HexagonRowColumn525.cols_left1)) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_2_5_row_0_0_2 : (((-1 : ℤ) ^ (leftScaleBit 5 2 5).val * positiveScale (leftScaleExponent 5 2 5)) •
      (rowColumnMul HexagonRowColumn525.rows_assocBAC HexagonRowColumn525.cols_left0)) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 5 2 5) • (rowColumnMul HexagonRowColumn525.rows_innerRightBAC HexagonRowColumn525.cols_left1)) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_2_5_row_0_0_3 : (((-1 : ℤ) ^ (leftScaleBit 5 2 5).val * positiveScale (leftScaleExponent 5 2 5)) •
      (rowColumnMul HexagonRowColumn525.rows_assocBAC HexagonRowColumn525.cols_left0)) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 5 2 5) • (rowColumnMul HexagonRowColumn525.rows_innerRightBAC HexagonRowColumn525.cols_left1)) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_2_5_row_0_1_0 : (((-1 : ℤ) ^ (leftScaleBit 5 2 5).val * positiveScale (leftScaleExponent 5 2 5)) •
      (rowColumnMul HexagonRowColumn525.rows_assocBAC HexagonRowColumn525.cols_left0)) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 5 2 5) • (rowColumnMul HexagonRowColumn525.rows_innerRightBAC HexagonRowColumn525.cols_left1)) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_2_5_row_0_1_1 : (((-1 : ℤ) ^ (leftScaleBit 5 2 5).val * positiveScale (leftScaleExponent 5 2 5)) •
      (rowColumnMul HexagonRowColumn525.rows_assocBAC HexagonRowColumn525.cols_left0)) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 5 2 5) • (rowColumnMul HexagonRowColumn525.rows_innerRightBAC HexagonRowColumn525.cols_left1)) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_2_5_row_0_1_2 : (((-1 : ℤ) ^ (leftScaleBit 5 2 5).val * positiveScale (leftScaleExponent 5 2 5)) •
      (rowColumnMul HexagonRowColumn525.rows_assocBAC HexagonRowColumn525.cols_left0)) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 5 2 5) • (rowColumnMul HexagonRowColumn525.rows_innerRightBAC HexagonRowColumn525.cols_left1)) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_2_5_row_0_1_3 : (((-1 : ℤ) ^ (leftScaleBit 5 2 5).val * positiveScale (leftScaleExponent 5 2 5)) •
      (rowColumnMul HexagonRowColumn525.rows_assocBAC HexagonRowColumn525.cols_left0)) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 5 2 5) • (rowColumnMul HexagonRowColumn525.rows_innerRightBAC HexagonRowColumn525.cols_left1)) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_2_5_row_1_0_0 : (((-1 : ℤ) ^ (leftScaleBit 5 2 5).val * positiveScale (leftScaleExponent 5 2 5)) •
      (rowColumnMul HexagonRowColumn525.rows_assocBAC HexagonRowColumn525.cols_left0)) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 5 2 5) • (rowColumnMul HexagonRowColumn525.rows_innerRightBAC HexagonRowColumn525.cols_left1)) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_2_5_row_1_0_1 : (((-1 : ℤ) ^ (leftScaleBit 5 2 5).val * positiveScale (leftScaleExponent 5 2 5)) •
      (rowColumnMul HexagonRowColumn525.rows_assocBAC HexagonRowColumn525.cols_left0)) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 5 2 5) • (rowColumnMul HexagonRowColumn525.rows_innerRightBAC HexagonRowColumn525.cols_left1)) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_2_5_row_1_0_2 : (((-1 : ℤ) ^ (leftScaleBit 5 2 5).val * positiveScale (leftScaleExponent 5 2 5)) •
      (rowColumnMul HexagonRowColumn525.rows_assocBAC HexagonRowColumn525.cols_left0)) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 5 2 5) • (rowColumnMul HexagonRowColumn525.rows_innerRightBAC HexagonRowColumn525.cols_left1)) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_2_5_row_1_0_3 : (((-1 : ℤ) ^ (leftScaleBit 5 2 5).val * positiveScale (leftScaleExponent 5 2 5)) •
      (rowColumnMul HexagonRowColumn525.rows_assocBAC HexagonRowColumn525.cols_left0)) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 5 2 5) • (rowColumnMul HexagonRowColumn525.rows_innerRightBAC HexagonRowColumn525.cols_left1)) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_2_5_row_1_1_0 : (((-1 : ℤ) ^ (leftScaleBit 5 2 5).val * positiveScale (leftScaleExponent 5 2 5)) •
      (rowColumnMul HexagonRowColumn525.rows_assocBAC HexagonRowColumn525.cols_left0)) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 5 2 5) • (rowColumnMul HexagonRowColumn525.rows_innerRightBAC HexagonRowColumn525.cols_left1)) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_2_5_row_1_1_1 : (((-1 : ℤ) ^ (leftScaleBit 5 2 5).val * positiveScale (leftScaleExponent 5 2 5)) •
      (rowColumnMul HexagonRowColumn525.rows_assocBAC HexagonRowColumn525.cols_left0)) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 5 2 5) • (rowColumnMul HexagonRowColumn525.rows_innerRightBAC HexagonRowColumn525.cols_left1)) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_2_5_row_1_1_2 : (((-1 : ℤ) ^ (leftScaleBit 5 2 5).val * positiveScale (leftScaleExponent 5 2 5)) •
      (rowColumnMul HexagonRowColumn525.rows_assocBAC HexagonRowColumn525.cols_left0)) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 5 2 5) • (rowColumnMul HexagonRowColumn525.rows_innerRightBAC HexagonRowColumn525.cols_left1)) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_2_5_row_1_1_3 : (((-1 : ℤ) ^ (leftScaleBit 5 2 5).val * positiveScale (leftScaleExponent 5 2 5)) •
      (rowColumnMul HexagonRowColumn525.rows_assocBAC HexagonRowColumn525.cols_left0)) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 5 2 5) • (rowColumnMul HexagonRowColumn525.rows_innerRightBAC HexagonRowColumn525.cols_left1)) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_2_5_row_2_0_0 : (((-1 : ℤ) ^ (leftScaleBit 5 2 5).val * positiveScale (leftScaleExponent 5 2 5)) •
      (rowColumnMul HexagonRowColumn525.rows_assocBAC HexagonRowColumn525.cols_left0)) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 5 2 5) • (rowColumnMul HexagonRowColumn525.rows_innerRightBAC HexagonRowColumn525.cols_left1)) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_2_5_row_2_0_1 : (((-1 : ℤ) ^ (leftScaleBit 5 2 5).val * positiveScale (leftScaleExponent 5 2 5)) •
      (rowColumnMul HexagonRowColumn525.rows_assocBAC HexagonRowColumn525.cols_left0)) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 5 2 5) • (rowColumnMul HexagonRowColumn525.rows_innerRightBAC HexagonRowColumn525.cols_left1)) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_2_5_row_2_0_2 : (((-1 : ℤ) ^ (leftScaleBit 5 2 5).val * positiveScale (leftScaleExponent 5 2 5)) •
      (rowColumnMul HexagonRowColumn525.rows_assocBAC HexagonRowColumn525.cols_left0)) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 5 2 5) • (rowColumnMul HexagonRowColumn525.rows_innerRightBAC HexagonRowColumn525.cols_left1)) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_2_5_row_2_0_3 : (((-1 : ℤ) ^ (leftScaleBit 5 2 5).val * positiveScale (leftScaleExponent 5 2 5)) •
      (rowColumnMul HexagonRowColumn525.rows_assocBAC HexagonRowColumn525.cols_left0)) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 5 2 5) • (rowColumnMul HexagonRowColumn525.rows_innerRightBAC HexagonRowColumn525.cols_left1)) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_2_5_row_2_1_0 : (((-1 : ℤ) ^ (leftScaleBit 5 2 5).val * positiveScale (leftScaleExponent 5 2 5)) •
      (rowColumnMul HexagonRowColumn525.rows_assocBAC HexagonRowColumn525.cols_left0)) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 5 2 5) • (rowColumnMul HexagonRowColumn525.rows_innerRightBAC HexagonRowColumn525.cols_left1)) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_2_5_row_2_1_1 : (((-1 : ℤ) ^ (leftScaleBit 5 2 5).val * positiveScale (leftScaleExponent 5 2 5)) •
      (rowColumnMul HexagonRowColumn525.rows_assocBAC HexagonRowColumn525.cols_left0)) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 5 2 5) • (rowColumnMul HexagonRowColumn525.rows_innerRightBAC HexagonRowColumn525.cols_left1)) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_2_5_row_2_1_2 : (((-1 : ℤ) ^ (leftScaleBit 5 2 5).val * positiveScale (leftScaleExponent 5 2 5)) •
      (rowColumnMul HexagonRowColumn525.rows_assocBAC HexagonRowColumn525.cols_left0)) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 5 2 5) • (rowColumnMul HexagonRowColumn525.rows_innerRightBAC HexagonRowColumn525.cols_left1)) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_2_5_row_2_1_3 : (((-1 : ℤ) ^ (leftScaleBit 5 2 5).val * positiveScale (leftScaleExponent 5 2 5)) •
      (rowColumnMul HexagonRowColumn525.rows_assocBAC HexagonRowColumn525.cols_left0)) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 5 2 5) • (rowColumnMul HexagonRowColumn525.rows_innerRightBAC HexagonRowColumn525.cols_left1)) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_2_5_row_3_0_0 : (((-1 : ℤ) ^ (leftScaleBit 5 2 5).val * positiveScale (leftScaleExponent 5 2 5)) •
      (rowColumnMul HexagonRowColumn525.rows_assocBAC HexagonRowColumn525.cols_left0)) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 5 2 5) • (rowColumnMul HexagonRowColumn525.rows_innerRightBAC HexagonRowColumn525.cols_left1)) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_2_5_row_3_0_1 : (((-1 : ℤ) ^ (leftScaleBit 5 2 5).val * positiveScale (leftScaleExponent 5 2 5)) •
      (rowColumnMul HexagonRowColumn525.rows_assocBAC HexagonRowColumn525.cols_left0)) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 5 2 5) • (rowColumnMul HexagonRowColumn525.rows_innerRightBAC HexagonRowColumn525.cols_left1)) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_2_5_row_3_0_2 : (((-1 : ℤ) ^ (leftScaleBit 5 2 5).val * positiveScale (leftScaleExponent 5 2 5)) •
      (rowColumnMul HexagonRowColumn525.rows_assocBAC HexagonRowColumn525.cols_left0)) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 5 2 5) • (rowColumnMul HexagonRowColumn525.rows_innerRightBAC HexagonRowColumn525.cols_left1)) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_2_5_row_3_0_3 : (((-1 : ℤ) ^ (leftScaleBit 5 2 5).val * positiveScale (leftScaleExponent 5 2 5)) •
      (rowColumnMul HexagonRowColumn525.rows_assocBAC HexagonRowColumn525.cols_left0)) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 5 2 5) • (rowColumnMul HexagonRowColumn525.rows_innerRightBAC HexagonRowColumn525.cols_left1)) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_2_5_row_3_1_0 : (((-1 : ℤ) ^ (leftScaleBit 5 2 5).val * positiveScale (leftScaleExponent 5 2 5)) •
      (rowColumnMul HexagonRowColumn525.rows_assocBAC HexagonRowColumn525.cols_left0)) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 5 2 5) • (rowColumnMul HexagonRowColumn525.rows_innerRightBAC HexagonRowColumn525.cols_left1)) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_2_5_row_3_1_1 : (((-1 : ℤ) ^ (leftScaleBit 5 2 5).val * positiveScale (leftScaleExponent 5 2 5)) •
      (rowColumnMul HexagonRowColumn525.rows_assocBAC HexagonRowColumn525.cols_left0)) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 5 2 5) • (rowColumnMul HexagonRowColumn525.rows_innerRightBAC HexagonRowColumn525.cols_left1)) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_2_5_row_3_1_2 : (((-1 : ℤ) ^ (leftScaleBit 5 2 5).val * positiveScale (leftScaleExponent 5 2 5)) •
      (rowColumnMul HexagonRowColumn525.rows_assocBAC HexagonRowColumn525.cols_left0)) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 5 2 5) • (rowColumnMul HexagonRowColumn525.rows_innerRightBAC HexagonRowColumn525.cols_left1)) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_2_5_row_3_1_3 : (((-1 : ℤ) ^ (leftScaleBit 5 2 5).val * positiveScale (leftScaleExponent 5 2 5)) •
      (rowColumnMul HexagonRowColumn525.rows_assocBAC HexagonRowColumn525.cols_left0)) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 5 2 5) • (rowColumnMul HexagonRowColumn525.rows_innerRightBAC HexagonRowColumn525.cols_left1)) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_2_5_checked : ((-1 : ℤ) ^ (leftScaleBit 5 2 5).val * positiveScale (leftScaleExponent 5 2 5)) •
      (rowColumnMul HexagonRowColumn525.rows_assocBAC HexagonRowColumn525.cols_left0) = negativeScale (leftScaleExponent 5 2 5) • (rowColumnMul HexagonRowColumn525.rows_innerRightBAC HexagonRowColumn525.cols_left1) := by
  funext r
  fin_cases r
  · exact leftFinal5_case_2_5_row_0_0_0
  · exact leftFinal5_case_2_5_row_0_0_1
  · exact leftFinal5_case_2_5_row_0_0_2
  · exact leftFinal5_case_2_5_row_0_0_3
  · exact leftFinal5_case_2_5_row_0_1_0
  · exact leftFinal5_case_2_5_row_0_1_1
  · exact leftFinal5_case_2_5_row_0_1_2
  · exact leftFinal5_case_2_5_row_0_1_3
  · exact leftFinal5_case_2_5_row_1_0_0
  · exact leftFinal5_case_2_5_row_1_0_1
  · exact leftFinal5_case_2_5_row_1_0_2
  · exact leftFinal5_case_2_5_row_1_0_3
  · exact leftFinal5_case_2_5_row_1_1_0
  · exact leftFinal5_case_2_5_row_1_1_1
  · exact leftFinal5_case_2_5_row_1_1_2
  · exact leftFinal5_case_2_5_row_1_1_3
  · exact leftFinal5_case_2_5_row_2_0_0
  · exact leftFinal5_case_2_5_row_2_0_1
  · exact leftFinal5_case_2_5_row_2_0_2
  · exact leftFinal5_case_2_5_row_2_0_3
  · exact leftFinal5_case_2_5_row_2_1_0
  · exact leftFinal5_case_2_5_row_2_1_1
  · exact leftFinal5_case_2_5_row_2_1_2
  · exact leftFinal5_case_2_5_row_2_1_3
  · exact leftFinal5_case_2_5_row_3_0_0
  · exact leftFinal5_case_2_5_row_3_0_1
  · exact leftFinal5_case_2_5_row_3_0_2
  · exact leftFinal5_case_2_5_row_3_0_3
  · exact leftFinal5_case_2_5_row_3_1_0
  · exact leftFinal5_case_2_5_row_3_1_1
  · exact leftFinal5_case_2_5_row_3_1_2
  · exact leftFinal5_case_2_5_row_3_1_3

set_option backward.isDefEq.respectTransparency false in
theorem leftFinal5_case_2_5 : ((-1 : ℤ) ^ (leftScaleBit 5 2 5).val * positiveScale (leftScaleExponent 5 2 5)) •
      (associatorZ 2 5 5 * left0Middle5 2 5) = negativeScale (leftScaleExponent 5 2 5) • (innerRightZ 2 5 5 * left1Middle5 2 5) := by
  simpa only [HexagonAtoms525.assocABC_eq,
    HexagonAtoms525.outerABC_eq,
    HexagonAtoms525.assocBAC_eq,
    HexagonAtoms525.innerABC_eq,
    HexagonAtoms525.innerRightABC_eq,
    HexagonAtoms525.inverseACB_eq,
    HexagonAtoms525.innerACB_eq,
    HexagonAtoms525.assocBCA_eq,
    HexagonAtoms525.innerRightBAC_eq,
    HexagonAtoms525.assocCAB_eq,
    HexagonAtoms525.outerLeftABC_eq,
    HexagonRowColumn525.assocBCA_alias,
    HexagonRowColumn525.product0_eq,
    HexagonRowColumn525.product1_eq,
    HexagonRowColumn525.product2_eq,
    HexagonRowColumn525.product3_eq,
    HexagonRowColumn525.product4_eq,
    HexagonRowColumn525.product5_eq,
    HexagonRowColumn525.product6_eq,
    HexagonRowColumn525.product7_eq] using leftFinal5_case_2_5_checked

private theorem rightFinal5_case_2_5_row_0_0_0 : (((-1 : ℤ) ^ (rightScaleBit 5 2 5).val * positiveScale (rightScaleExponent 5 2 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 5 2 : ℤ)) • HexagonAtoms525.outerLeftABC) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 5 2 5) • (rowColumnMul HexagonRowColumn525.rows_assocCAB HexagonRowColumn525.cols_right2)) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_2_5_row_0_0_1 : (((-1 : ℤ) ^ (rightScaleBit 5 2 5).val * positiveScale (rightScaleExponent 5 2 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 5 2 : ℤ)) • HexagonAtoms525.outerLeftABC) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 5 2 5) • (rowColumnMul HexagonRowColumn525.rows_assocCAB HexagonRowColumn525.cols_right2)) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_2_5_row_0_0_2 : (((-1 : ℤ) ^ (rightScaleBit 5 2 5).val * positiveScale (rightScaleExponent 5 2 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 5 2 : ℤ)) • HexagonAtoms525.outerLeftABC) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 5 2 5) • (rowColumnMul HexagonRowColumn525.rows_assocCAB HexagonRowColumn525.cols_right2)) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_2_5_row_0_0_3 : (((-1 : ℤ) ^ (rightScaleBit 5 2 5).val * positiveScale (rightScaleExponent 5 2 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 5 2 : ℤ)) • HexagonAtoms525.outerLeftABC) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 5 2 5) • (rowColumnMul HexagonRowColumn525.rows_assocCAB HexagonRowColumn525.cols_right2)) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_2_5_row_0_1_0 : (((-1 : ℤ) ^ (rightScaleBit 5 2 5).val * positiveScale (rightScaleExponent 5 2 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 5 2 : ℤ)) • HexagonAtoms525.outerLeftABC) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 5 2 5) • (rowColumnMul HexagonRowColumn525.rows_assocCAB HexagonRowColumn525.cols_right2)) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_2_5_row_0_1_1 : (((-1 : ℤ) ^ (rightScaleBit 5 2 5).val * positiveScale (rightScaleExponent 5 2 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 5 2 : ℤ)) • HexagonAtoms525.outerLeftABC) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 5 2 5) • (rowColumnMul HexagonRowColumn525.rows_assocCAB HexagonRowColumn525.cols_right2)) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_2_5_row_0_1_2 : (((-1 : ℤ) ^ (rightScaleBit 5 2 5).val * positiveScale (rightScaleExponent 5 2 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 5 2 : ℤ)) • HexagonAtoms525.outerLeftABC) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 5 2 5) • (rowColumnMul HexagonRowColumn525.rows_assocCAB HexagonRowColumn525.cols_right2)) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_2_5_row_0_1_3 : (((-1 : ℤ) ^ (rightScaleBit 5 2 5).val * positiveScale (rightScaleExponent 5 2 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 5 2 : ℤ)) • HexagonAtoms525.outerLeftABC) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 5 2 5) • (rowColumnMul HexagonRowColumn525.rows_assocCAB HexagonRowColumn525.cols_right2)) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_2_5_row_1_0_0 : (((-1 : ℤ) ^ (rightScaleBit 5 2 5).val * positiveScale (rightScaleExponent 5 2 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 5 2 : ℤ)) • HexagonAtoms525.outerLeftABC) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 5 2 5) • (rowColumnMul HexagonRowColumn525.rows_assocCAB HexagonRowColumn525.cols_right2)) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_2_5_row_1_0_1 : (((-1 : ℤ) ^ (rightScaleBit 5 2 5).val * positiveScale (rightScaleExponent 5 2 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 5 2 : ℤ)) • HexagonAtoms525.outerLeftABC) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 5 2 5) • (rowColumnMul HexagonRowColumn525.rows_assocCAB HexagonRowColumn525.cols_right2)) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_2_5_row_1_0_2 : (((-1 : ℤ) ^ (rightScaleBit 5 2 5).val * positiveScale (rightScaleExponent 5 2 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 5 2 : ℤ)) • HexagonAtoms525.outerLeftABC) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 5 2 5) • (rowColumnMul HexagonRowColumn525.rows_assocCAB HexagonRowColumn525.cols_right2)) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_2_5_row_1_0_3 : (((-1 : ℤ) ^ (rightScaleBit 5 2 5).val * positiveScale (rightScaleExponent 5 2 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 5 2 : ℤ)) • HexagonAtoms525.outerLeftABC) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 5 2 5) • (rowColumnMul HexagonRowColumn525.rows_assocCAB HexagonRowColumn525.cols_right2)) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_2_5_row_1_1_0 : (((-1 : ℤ) ^ (rightScaleBit 5 2 5).val * positiveScale (rightScaleExponent 5 2 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 5 2 : ℤ)) • HexagonAtoms525.outerLeftABC) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 5 2 5) • (rowColumnMul HexagonRowColumn525.rows_assocCAB HexagonRowColumn525.cols_right2)) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_2_5_row_1_1_1 : (((-1 : ℤ) ^ (rightScaleBit 5 2 5).val * positiveScale (rightScaleExponent 5 2 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 5 2 : ℤ)) • HexagonAtoms525.outerLeftABC) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 5 2 5) • (rowColumnMul HexagonRowColumn525.rows_assocCAB HexagonRowColumn525.cols_right2)) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_2_5_row_1_1_2 : (((-1 : ℤ) ^ (rightScaleBit 5 2 5).val * positiveScale (rightScaleExponent 5 2 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 5 2 : ℤ)) • HexagonAtoms525.outerLeftABC) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 5 2 5) • (rowColumnMul HexagonRowColumn525.rows_assocCAB HexagonRowColumn525.cols_right2)) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_2_5_row_1_1_3 : (((-1 : ℤ) ^ (rightScaleBit 5 2 5).val * positiveScale (rightScaleExponent 5 2 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 5 2 : ℤ)) • HexagonAtoms525.outerLeftABC) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 5 2 5) • (rowColumnMul HexagonRowColumn525.rows_assocCAB HexagonRowColumn525.cols_right2)) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_2_5_row_2_0_0 : (((-1 : ℤ) ^ (rightScaleBit 5 2 5).val * positiveScale (rightScaleExponent 5 2 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 5 2 : ℤ)) • HexagonAtoms525.outerLeftABC) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 5 2 5) • (rowColumnMul HexagonRowColumn525.rows_assocCAB HexagonRowColumn525.cols_right2)) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_2_5_row_2_0_1 : (((-1 : ℤ) ^ (rightScaleBit 5 2 5).val * positiveScale (rightScaleExponent 5 2 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 5 2 : ℤ)) • HexagonAtoms525.outerLeftABC) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 5 2 5) • (rowColumnMul HexagonRowColumn525.rows_assocCAB HexagonRowColumn525.cols_right2)) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_2_5_row_2_0_2 : (((-1 : ℤ) ^ (rightScaleBit 5 2 5).val * positiveScale (rightScaleExponent 5 2 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 5 2 : ℤ)) • HexagonAtoms525.outerLeftABC) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 5 2 5) • (rowColumnMul HexagonRowColumn525.rows_assocCAB HexagonRowColumn525.cols_right2)) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_2_5_row_2_0_3 : (((-1 : ℤ) ^ (rightScaleBit 5 2 5).val * positiveScale (rightScaleExponent 5 2 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 5 2 : ℤ)) • HexagonAtoms525.outerLeftABC) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 5 2 5) • (rowColumnMul HexagonRowColumn525.rows_assocCAB HexagonRowColumn525.cols_right2)) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_2_5_row_2_1_0 : (((-1 : ℤ) ^ (rightScaleBit 5 2 5).val * positiveScale (rightScaleExponent 5 2 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 5 2 : ℤ)) • HexagonAtoms525.outerLeftABC) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 5 2 5) • (rowColumnMul HexagonRowColumn525.rows_assocCAB HexagonRowColumn525.cols_right2)) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_2_5_row_2_1_1 : (((-1 : ℤ) ^ (rightScaleBit 5 2 5).val * positiveScale (rightScaleExponent 5 2 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 5 2 : ℤ)) • HexagonAtoms525.outerLeftABC) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 5 2 5) • (rowColumnMul HexagonRowColumn525.rows_assocCAB HexagonRowColumn525.cols_right2)) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_2_5_row_2_1_2 : (((-1 : ℤ) ^ (rightScaleBit 5 2 5).val * positiveScale (rightScaleExponent 5 2 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 5 2 : ℤ)) • HexagonAtoms525.outerLeftABC) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 5 2 5) • (rowColumnMul HexagonRowColumn525.rows_assocCAB HexagonRowColumn525.cols_right2)) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_2_5_row_2_1_3 : (((-1 : ℤ) ^ (rightScaleBit 5 2 5).val * positiveScale (rightScaleExponent 5 2 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 5 2 : ℤ)) • HexagonAtoms525.outerLeftABC) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 5 2 5) • (rowColumnMul HexagonRowColumn525.rows_assocCAB HexagonRowColumn525.cols_right2)) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_2_5_row_3_0_0 : (((-1 : ℤ) ^ (rightScaleBit 5 2 5).val * positiveScale (rightScaleExponent 5 2 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 5 2 : ℤ)) • HexagonAtoms525.outerLeftABC) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 5 2 5) • (rowColumnMul HexagonRowColumn525.rows_assocCAB HexagonRowColumn525.cols_right2)) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_2_5_row_3_0_1 : (((-1 : ℤ) ^ (rightScaleBit 5 2 5).val * positiveScale (rightScaleExponent 5 2 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 5 2 : ℤ)) • HexagonAtoms525.outerLeftABC) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 5 2 5) • (rowColumnMul HexagonRowColumn525.rows_assocCAB HexagonRowColumn525.cols_right2)) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_2_5_row_3_0_2 : (((-1 : ℤ) ^ (rightScaleBit 5 2 5).val * positiveScale (rightScaleExponent 5 2 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 5 2 : ℤ)) • HexagonAtoms525.outerLeftABC) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 5 2 5) • (rowColumnMul HexagonRowColumn525.rows_assocCAB HexagonRowColumn525.cols_right2)) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_2_5_row_3_0_3 : (((-1 : ℤ) ^ (rightScaleBit 5 2 5).val * positiveScale (rightScaleExponent 5 2 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 5 2 : ℤ)) • HexagonAtoms525.outerLeftABC) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 5 2 5) • (rowColumnMul HexagonRowColumn525.rows_assocCAB HexagonRowColumn525.cols_right2)) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_2_5_row_3_1_0 : (((-1 : ℤ) ^ (rightScaleBit 5 2 5).val * positiveScale (rightScaleExponent 5 2 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 5 2 : ℤ)) • HexagonAtoms525.outerLeftABC) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 5 2 5) • (rowColumnMul HexagonRowColumn525.rows_assocCAB HexagonRowColumn525.cols_right2)) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_2_5_row_3_1_1 : (((-1 : ℤ) ^ (rightScaleBit 5 2 5).val * positiveScale (rightScaleExponent 5 2 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 5 2 : ℤ)) • HexagonAtoms525.outerLeftABC) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 5 2 5) • (rowColumnMul HexagonRowColumn525.rows_assocCAB HexagonRowColumn525.cols_right2)) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_2_5_row_3_1_2 : (((-1 : ℤ) ^ (rightScaleBit 5 2 5).val * positiveScale (rightScaleExponent 5 2 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 5 2 : ℤ)) • HexagonAtoms525.outerLeftABC) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 5 2 5) • (rowColumnMul HexagonRowColumn525.rows_assocCAB HexagonRowColumn525.cols_right2)) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_2_5_row_3_1_3 : (((-1 : ℤ) ^ (rightScaleBit 5 2 5).val * positiveScale (rightScaleExponent 5 2 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 5 2 : ℤ)) • HexagonAtoms525.outerLeftABC) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 5 2 5) • (rowColumnMul HexagonRowColumn525.rows_assocCAB HexagonRowColumn525.cols_right2)) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_2_5_checked : ((-1 : ℤ) ^ (rightScaleBit 5 2 5).val * positiveScale (rightScaleExponent 5 2 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 5 2 : ℤ)) • HexagonAtoms525.outerLeftABC = negativeScale (rightScaleExponent 5 2 5) • (rowColumnMul HexagonRowColumn525.rows_assocCAB HexagonRowColumn525.cols_right2) := by
  funext r
  fin_cases r
  · exact rightFinal5_case_2_5_row_0_0_0
  · exact rightFinal5_case_2_5_row_0_0_1
  · exact rightFinal5_case_2_5_row_0_0_2
  · exact rightFinal5_case_2_5_row_0_0_3
  · exact rightFinal5_case_2_5_row_0_1_0
  · exact rightFinal5_case_2_5_row_0_1_1
  · exact rightFinal5_case_2_5_row_0_1_2
  · exact rightFinal5_case_2_5_row_0_1_3
  · exact rightFinal5_case_2_5_row_1_0_0
  · exact rightFinal5_case_2_5_row_1_0_1
  · exact rightFinal5_case_2_5_row_1_0_2
  · exact rightFinal5_case_2_5_row_1_0_3
  · exact rightFinal5_case_2_5_row_1_1_0
  · exact rightFinal5_case_2_5_row_1_1_1
  · exact rightFinal5_case_2_5_row_1_1_2
  · exact rightFinal5_case_2_5_row_1_1_3
  · exact rightFinal5_case_2_5_row_2_0_0
  · exact rightFinal5_case_2_5_row_2_0_1
  · exact rightFinal5_case_2_5_row_2_0_2
  · exact rightFinal5_case_2_5_row_2_0_3
  · exact rightFinal5_case_2_5_row_2_1_0
  · exact rightFinal5_case_2_5_row_2_1_1
  · exact rightFinal5_case_2_5_row_2_1_2
  · exact rightFinal5_case_2_5_row_2_1_3
  · exact rightFinal5_case_2_5_row_3_0_0
  · exact rightFinal5_case_2_5_row_3_0_1
  · exact rightFinal5_case_2_5_row_3_0_2
  · exact rightFinal5_case_2_5_row_3_0_3
  · exact rightFinal5_case_2_5_row_3_1_0
  · exact rightFinal5_case_2_5_row_3_1_1
  · exact rightFinal5_case_2_5_row_3_1_2
  · exact rightFinal5_case_2_5_row_3_1_3

set_option backward.isDefEq.respectTransparency false in
theorem rightFinal5_case_2_5 : ((-1 : ℤ) ^ (rightScaleBit 5 2 5).val * positiveScale (rightScaleExponent 5 2 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 5 2 : ℤ)) • outerLeftZ 5 2 5 = negativeScale (rightScaleExponent 5 2 5) • (associatorZ 5 5 2 * right2Middle5 2 5) := by
  simpa only [HexagonAtoms525.assocABC_eq,
    HexagonAtoms525.outerABC_eq,
    HexagonAtoms525.assocBAC_eq,
    HexagonAtoms525.innerABC_eq,
    HexagonAtoms525.innerRightABC_eq,
    HexagonAtoms525.inverseACB_eq,
    HexagonAtoms525.innerACB_eq,
    HexagonAtoms525.assocBCA_eq,
    HexagonAtoms525.innerRightBAC_eq,
    HexagonAtoms525.assocCAB_eq,
    HexagonAtoms525.outerLeftABC_eq,
    HexagonRowColumn525.assocBCA_alias,
    HexagonRowColumn525.product0_eq,
    HexagonRowColumn525.product1_eq,
    HexagonRowColumn525.product2_eq,
    HexagonRowColumn525.product3_eq,
    HexagonRowColumn525.product4_eq,
    HexagonRowColumn525.product5_eq,
    HexagonRowColumn525.product6_eq,
    HexagonRowColumn525.product7_eq] using rightFinal5_case_2_5_checked

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonCases5
