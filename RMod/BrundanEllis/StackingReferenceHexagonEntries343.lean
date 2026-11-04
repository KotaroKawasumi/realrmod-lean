import RMod.BrundanEllis.StackingReferenceHexagonMiddle3
import RMod.BrundanEllis.StackingReferenceSparseMatrixCheck
import RMod.BrundanEllis.StackingReferenceHexagonAtoms343
import RMod.BrundanEllis.StackingReferenceHexagonRowColumn343

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

private theorem left0Middle3_eq_case_4_3_row_0_0_0 : (left0Middle3 4 3) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn343.rows_outerABC HexagonRowColumn343.cols_assocABC) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_4_3_row_0_0_1 : (left0Middle3 4 3) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn343.rows_outerABC HexagonRowColumn343.cols_assocABC) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_4_3_row_0_0_2 : (left0Middle3 4 3) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn343.rows_outerABC HexagonRowColumn343.cols_assocABC) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_4_3_row_0_0_3 : (left0Middle3 4 3) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn343.rows_outerABC HexagonRowColumn343.cols_assocABC) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_4_3_row_0_1_0 : (left0Middle3 4 3) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn343.rows_outerABC HexagonRowColumn343.cols_assocABC) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_4_3_row_0_1_1 : (left0Middle3 4 3) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn343.rows_outerABC HexagonRowColumn343.cols_assocABC) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_4_3_row_0_1_2 : (left0Middle3 4 3) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn343.rows_outerABC HexagonRowColumn343.cols_assocABC) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_4_3_row_0_1_3 : (left0Middle3 4 3) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn343.rows_outerABC HexagonRowColumn343.cols_assocABC) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_4_3_row_1_0_0 : (left0Middle3 4 3) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn343.rows_outerABC HexagonRowColumn343.cols_assocABC) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_4_3_row_1_0_1 : (left0Middle3 4 3) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn343.rows_outerABC HexagonRowColumn343.cols_assocABC) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_4_3_row_1_0_2 : (left0Middle3 4 3) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn343.rows_outerABC HexagonRowColumn343.cols_assocABC) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_4_3_row_1_0_3 : (left0Middle3 4 3) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn343.rows_outerABC HexagonRowColumn343.cols_assocABC) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_4_3_row_1_1_0 : (left0Middle3 4 3) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn343.rows_outerABC HexagonRowColumn343.cols_assocABC) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_4_3_row_1_1_1 : (left0Middle3 4 3) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn343.rows_outerABC HexagonRowColumn343.cols_assocABC) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_4_3_row_1_1_2 : (left0Middle3 4 3) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn343.rows_outerABC HexagonRowColumn343.cols_assocABC) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_4_3_row_1_1_3 : (left0Middle3 4 3) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn343.rows_outerABC HexagonRowColumn343.cols_assocABC) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_4_3_row_2_0_0 : (left0Middle3 4 3) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn343.rows_outerABC HexagonRowColumn343.cols_assocABC) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_4_3_row_2_0_1 : (left0Middle3 4 3) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn343.rows_outerABC HexagonRowColumn343.cols_assocABC) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_4_3_row_2_0_2 : (left0Middle3 4 3) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn343.rows_outerABC HexagonRowColumn343.cols_assocABC) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_4_3_row_2_0_3 : (left0Middle3 4 3) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn343.rows_outerABC HexagonRowColumn343.cols_assocABC) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_4_3_row_2_1_0 : (left0Middle3 4 3) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn343.rows_outerABC HexagonRowColumn343.cols_assocABC) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_4_3_row_2_1_1 : (left0Middle3 4 3) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn343.rows_outerABC HexagonRowColumn343.cols_assocABC) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_4_3_row_2_1_2 : (left0Middle3 4 3) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn343.rows_outerABC HexagonRowColumn343.cols_assocABC) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_4_3_row_2_1_3 : (left0Middle3 4 3) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn343.rows_outerABC HexagonRowColumn343.cols_assocABC) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_4_3_row_3_0_0 : (left0Middle3 4 3) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn343.rows_outerABC HexagonRowColumn343.cols_assocABC) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_4_3_row_3_0_1 : (left0Middle3 4 3) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn343.rows_outerABC HexagonRowColumn343.cols_assocABC) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_4_3_row_3_0_2 : (left0Middle3 4 3) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn343.rows_outerABC HexagonRowColumn343.cols_assocABC) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_4_3_row_3_0_3 : (left0Middle3 4 3) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn343.rows_outerABC HexagonRowColumn343.cols_assocABC) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_4_3_row_3_1_0 : (left0Middle3 4 3) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn343.rows_outerABC HexagonRowColumn343.cols_assocABC) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_4_3_row_3_1_1 : (left0Middle3 4 3) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn343.rows_outerABC HexagonRowColumn343.cols_assocABC) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_4_3_row_3_1_2 : (left0Middle3 4 3) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn343.rows_outerABC HexagonRowColumn343.cols_assocABC) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_4_3_row_3_1_3 : (left0Middle3 4 3) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn343.rows_outerABC HexagonRowColumn343.cols_assocABC) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_4_3_checked : left0Middle3 4 3 = rowColumnMul HexagonRowColumn343.rows_outerABC HexagonRowColumn343.cols_assocABC := by
  funext r
  fin_cases r
  · exact left0Middle3_eq_case_4_3_row_0_0_0
  · exact left0Middle3_eq_case_4_3_row_0_0_1
  · exact left0Middle3_eq_case_4_3_row_0_0_2
  · exact left0Middle3_eq_case_4_3_row_0_0_3
  · exact left0Middle3_eq_case_4_3_row_0_1_0
  · exact left0Middle3_eq_case_4_3_row_0_1_1
  · exact left0Middle3_eq_case_4_3_row_0_1_2
  · exact left0Middle3_eq_case_4_3_row_0_1_3
  · exact left0Middle3_eq_case_4_3_row_1_0_0
  · exact left0Middle3_eq_case_4_3_row_1_0_1
  · exact left0Middle3_eq_case_4_3_row_1_0_2
  · exact left0Middle3_eq_case_4_3_row_1_0_3
  · exact left0Middle3_eq_case_4_3_row_1_1_0
  · exact left0Middle3_eq_case_4_3_row_1_1_1
  · exact left0Middle3_eq_case_4_3_row_1_1_2
  · exact left0Middle3_eq_case_4_3_row_1_1_3
  · exact left0Middle3_eq_case_4_3_row_2_0_0
  · exact left0Middle3_eq_case_4_3_row_2_0_1
  · exact left0Middle3_eq_case_4_3_row_2_0_2
  · exact left0Middle3_eq_case_4_3_row_2_0_3
  · exact left0Middle3_eq_case_4_3_row_2_1_0
  · exact left0Middle3_eq_case_4_3_row_2_1_1
  · exact left0Middle3_eq_case_4_3_row_2_1_2
  · exact left0Middle3_eq_case_4_3_row_2_1_3
  · exact left0Middle3_eq_case_4_3_row_3_0_0
  · exact left0Middle3_eq_case_4_3_row_3_0_1
  · exact left0Middle3_eq_case_4_3_row_3_0_2
  · exact left0Middle3_eq_case_4_3_row_3_0_3
  · exact left0Middle3_eq_case_4_3_row_3_1_0
  · exact left0Middle3_eq_case_4_3_row_3_1_1
  · exact left0Middle3_eq_case_4_3_row_3_1_2
  · exact left0Middle3_eq_case_4_3_row_3_1_3

set_option backward.isDefEq.respectTransparency false in
theorem left0Middle3_eq_case_4_3 : left0Middle3 4 3 = outerRightZ 3 4 3 * associatorZ 3 4 3 := by
  simpa only [HexagonAtoms343.assocABC_eq,
    HexagonAtoms343.outerABC_eq,
    HexagonAtoms343.assocBAC_eq,
    HexagonAtoms343.innerABC_eq,
    HexagonAtoms343.innerRightABC_eq,
    HexagonAtoms343.inverseACB_eq,
    HexagonAtoms343.innerACB_eq,
    HexagonAtoms343.assocBCA_eq,
    HexagonAtoms343.innerRightBAC_eq,
    HexagonAtoms343.assocCAB_eq,
    HexagonAtoms343.outerLeftABC_eq,
    HexagonRowColumn343.assocBCA_alias,
    HexagonRowColumn343.product0_eq,
    HexagonRowColumn343.product1_eq,
    HexagonRowColumn343.product2_eq,
    HexagonRowColumn343.product3_eq,
    HexagonRowColumn343.product4_eq,
    HexagonRowColumn343.product5_eq,
    HexagonRowColumn343.product6_eq,
    HexagonRowColumn343.product7_eq] using left0Middle3_eq_case_4_3_checked

private theorem left1Middle3_eq_case_4_3_row_0_0_0 : (left1Middle3 4 3) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms343.assocBAC) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_4_3_row_0_0_1 : (left1Middle3 4 3) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms343.assocBAC) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_4_3_row_0_0_2 : (left1Middle3 4 3) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms343.assocBAC) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_4_3_row_0_0_3 : (left1Middle3 4 3) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms343.assocBAC) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_4_3_row_0_1_0 : (left1Middle3 4 3) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms343.assocBAC) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_4_3_row_0_1_1 : (left1Middle3 4 3) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms343.assocBAC) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_4_3_row_0_1_2 : (left1Middle3 4 3) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms343.assocBAC) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_4_3_row_0_1_3 : (left1Middle3 4 3) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms343.assocBAC) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_4_3_row_1_0_0 : (left1Middle3 4 3) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms343.assocBAC) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_4_3_row_1_0_1 : (left1Middle3 4 3) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms343.assocBAC) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_4_3_row_1_0_2 : (left1Middle3 4 3) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms343.assocBAC) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_4_3_row_1_0_3 : (left1Middle3 4 3) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms343.assocBAC) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_4_3_row_1_1_0 : (left1Middle3 4 3) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms343.assocBAC) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_4_3_row_1_1_1 : (left1Middle3 4 3) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms343.assocBAC) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_4_3_row_1_1_2 : (left1Middle3 4 3) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms343.assocBAC) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_4_3_row_1_1_3 : (left1Middle3 4 3) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms343.assocBAC) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_4_3_row_2_0_0 : (left1Middle3 4 3) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms343.assocBAC) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_4_3_row_2_0_1 : (left1Middle3 4 3) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms343.assocBAC) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_4_3_row_2_0_2 : (left1Middle3 4 3) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms343.assocBAC) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_4_3_row_2_0_3 : (left1Middle3 4 3) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms343.assocBAC) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_4_3_row_2_1_0 : (left1Middle3 4 3) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms343.assocBAC) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_4_3_row_2_1_1 : (left1Middle3 4 3) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms343.assocBAC) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_4_3_row_2_1_2 : (left1Middle3 4 3) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms343.assocBAC) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_4_3_row_2_1_3 : (left1Middle3 4 3) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms343.assocBAC) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_4_3_row_3_0_0 : (left1Middle3 4 3) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms343.assocBAC) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_4_3_row_3_0_1 : (left1Middle3 4 3) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms343.assocBAC) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_4_3_row_3_0_2 : (left1Middle3 4 3) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms343.assocBAC) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_4_3_row_3_0_3 : (left1Middle3 4 3) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms343.assocBAC) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_4_3_row_3_1_0 : (left1Middle3 4 3) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms343.assocBAC) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_4_3_row_3_1_1 : (left1Middle3 4 3) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms343.assocBAC) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_4_3_row_3_1_2 : (left1Middle3 4 3) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms343.assocBAC) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_4_3_row_3_1_3 : (left1Middle3 4 3) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms343.assocBAC) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_4_3_checked : left1Middle3 4 3 = HexagonAtoms343.assocBAC := by
  funext r
  fin_cases r
  · exact left1Middle3_eq_case_4_3_row_0_0_0
  · exact left1Middle3_eq_case_4_3_row_0_0_1
  · exact left1Middle3_eq_case_4_3_row_0_0_2
  · exact left1Middle3_eq_case_4_3_row_0_0_3
  · exact left1Middle3_eq_case_4_3_row_0_1_0
  · exact left1Middle3_eq_case_4_3_row_0_1_1
  · exact left1Middle3_eq_case_4_3_row_0_1_2
  · exact left1Middle3_eq_case_4_3_row_0_1_3
  · exact left1Middle3_eq_case_4_3_row_1_0_0
  · exact left1Middle3_eq_case_4_3_row_1_0_1
  · exact left1Middle3_eq_case_4_3_row_1_0_2
  · exact left1Middle3_eq_case_4_3_row_1_0_3
  · exact left1Middle3_eq_case_4_3_row_1_1_0
  · exact left1Middle3_eq_case_4_3_row_1_1_1
  · exact left1Middle3_eq_case_4_3_row_1_1_2
  · exact left1Middle3_eq_case_4_3_row_1_1_3
  · exact left1Middle3_eq_case_4_3_row_2_0_0
  · exact left1Middle3_eq_case_4_3_row_2_0_1
  · exact left1Middle3_eq_case_4_3_row_2_0_2
  · exact left1Middle3_eq_case_4_3_row_2_0_3
  · exact left1Middle3_eq_case_4_3_row_2_1_0
  · exact left1Middle3_eq_case_4_3_row_2_1_1
  · exact left1Middle3_eq_case_4_3_row_2_1_2
  · exact left1Middle3_eq_case_4_3_row_2_1_3
  · exact left1Middle3_eq_case_4_3_row_3_0_0
  · exact left1Middle3_eq_case_4_3_row_3_0_1
  · exact left1Middle3_eq_case_4_3_row_3_0_2
  · exact left1Middle3_eq_case_4_3_row_3_0_3
  · exact left1Middle3_eq_case_4_3_row_3_1_0
  · exact left1Middle3_eq_case_4_3_row_3_1_1
  · exact left1Middle3_eq_case_4_3_row_3_1_2
  · exact left1Middle3_eq_case_4_3_row_3_1_3

set_option backward.isDefEq.respectTransparency false in
theorem left1Middle3_eq_case_4_3 : left1Middle3 4 3 = associatorZ 4 3 3 * innerLeftZ 3 4 3 := by
  simpa only [HexagonAtoms343.assocABC_eq,
    HexagonAtoms343.outerABC_eq,
    HexagonAtoms343.assocBAC_eq,
    HexagonAtoms343.innerABC_eq,
    HexagonAtoms343.innerRightABC_eq,
    HexagonAtoms343.inverseACB_eq,
    HexagonAtoms343.innerACB_eq,
    HexagonAtoms343.assocBCA_eq,
    HexagonAtoms343.innerRightBAC_eq,
    HexagonAtoms343.assocCAB_eq,
    HexagonAtoms343.outerLeftABC_eq,
    HexagonRowColumn343.assocBCA_alias,
    HexagonRowColumn343.product0_eq,
    HexagonRowColumn343.product1_eq,
    HexagonRowColumn343.product2_eq,
    HexagonRowColumn343.product3_eq,
    HexagonRowColumn343.product4_eq,
    HexagonRowColumn343.product5_eq,
    HexagonRowColumn343.product6_eq,
    HexagonRowColumn343.product7_eq] using left1Middle3_eq_case_4_3_checked

private theorem right0Middle3_eq_case_4_3_row_0_0_0 : (right0Middle3 4 3) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms343.assocABC) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_4_3_row_0_0_1 : (right0Middle3 4 3) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms343.assocABC) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_4_3_row_0_0_2 : (right0Middle3 4 3) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms343.assocABC) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_4_3_row_0_0_3 : (right0Middle3 4 3) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms343.assocABC) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_4_3_row_0_1_0 : (right0Middle3 4 3) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms343.assocABC) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_4_3_row_0_1_1 : (right0Middle3 4 3) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms343.assocABC) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_4_3_row_0_1_2 : (right0Middle3 4 3) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms343.assocABC) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_4_3_row_0_1_3 : (right0Middle3 4 3) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms343.assocABC) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_4_3_row_1_0_0 : (right0Middle3 4 3) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms343.assocABC) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_4_3_row_1_0_1 : (right0Middle3 4 3) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms343.assocABC) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_4_3_row_1_0_2 : (right0Middle3 4 3) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms343.assocABC) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_4_3_row_1_0_3 : (right0Middle3 4 3) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms343.assocABC) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_4_3_row_1_1_0 : (right0Middle3 4 3) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms343.assocABC) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_4_3_row_1_1_1 : (right0Middle3 4 3) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms343.assocABC) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_4_3_row_1_1_2 : (right0Middle3 4 3) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms343.assocABC) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_4_3_row_1_1_3 : (right0Middle3 4 3) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms343.assocABC) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_4_3_row_2_0_0 : (right0Middle3 4 3) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms343.assocABC) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_4_3_row_2_0_1 : (right0Middle3 4 3) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms343.assocABC) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_4_3_row_2_0_2 : (right0Middle3 4 3) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms343.assocABC) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_4_3_row_2_0_3 : (right0Middle3 4 3) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms343.assocABC) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_4_3_row_2_1_0 : (right0Middle3 4 3) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms343.assocABC) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_4_3_row_2_1_1 : (right0Middle3 4 3) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms343.assocABC) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_4_3_row_2_1_2 : (right0Middle3 4 3) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms343.assocABC) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_4_3_row_2_1_3 : (right0Middle3 4 3) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms343.assocABC) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_4_3_row_3_0_0 : (right0Middle3 4 3) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms343.assocABC) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_4_3_row_3_0_1 : (right0Middle3 4 3) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms343.assocABC) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_4_3_row_3_0_2 : (right0Middle3 4 3) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms343.assocABC) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_4_3_row_3_0_3 : (right0Middle3 4 3) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms343.assocABC) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_4_3_row_3_1_0 : (right0Middle3 4 3) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms343.assocABC) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_4_3_row_3_1_1 : (right0Middle3 4 3) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms343.assocABC) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_4_3_row_3_1_2 : (right0Middle3 4 3) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms343.assocABC) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_4_3_row_3_1_3 : (right0Middle3 4 3) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms343.assocABC) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_4_3_checked : right0Middle3 4 3 = HexagonAtoms343.assocABC := by
  funext r
  fin_cases r
  · exact right0Middle3_eq_case_4_3_row_0_0_0
  · exact right0Middle3_eq_case_4_3_row_0_0_1
  · exact right0Middle3_eq_case_4_3_row_0_0_2
  · exact right0Middle3_eq_case_4_3_row_0_0_3
  · exact right0Middle3_eq_case_4_3_row_0_1_0
  · exact right0Middle3_eq_case_4_3_row_0_1_1
  · exact right0Middle3_eq_case_4_3_row_0_1_2
  · exact right0Middle3_eq_case_4_3_row_0_1_3
  · exact right0Middle3_eq_case_4_3_row_1_0_0
  · exact right0Middle3_eq_case_4_3_row_1_0_1
  · exact right0Middle3_eq_case_4_3_row_1_0_2
  · exact right0Middle3_eq_case_4_3_row_1_0_3
  · exact right0Middle3_eq_case_4_3_row_1_1_0
  · exact right0Middle3_eq_case_4_3_row_1_1_1
  · exact right0Middle3_eq_case_4_3_row_1_1_2
  · exact right0Middle3_eq_case_4_3_row_1_1_3
  · exact right0Middle3_eq_case_4_3_row_2_0_0
  · exact right0Middle3_eq_case_4_3_row_2_0_1
  · exact right0Middle3_eq_case_4_3_row_2_0_2
  · exact right0Middle3_eq_case_4_3_row_2_0_3
  · exact right0Middle3_eq_case_4_3_row_2_1_0
  · exact right0Middle3_eq_case_4_3_row_2_1_1
  · exact right0Middle3_eq_case_4_3_row_2_1_2
  · exact right0Middle3_eq_case_4_3_row_2_1_3
  · exact right0Middle3_eq_case_4_3_row_3_0_0
  · exact right0Middle3_eq_case_4_3_row_3_0_1
  · exact right0Middle3_eq_case_4_3_row_3_0_2
  · exact right0Middle3_eq_case_4_3_row_3_0_3
  · exact right0Middle3_eq_case_4_3_row_3_1_0
  · exact right0Middle3_eq_case_4_3_row_3_1_1
  · exact right0Middle3_eq_case_4_3_row_3_1_2
  · exact right0Middle3_eq_case_4_3_row_3_1_3

set_option backward.isDefEq.respectTransparency false in
theorem right0Middle3_eq_case_4_3 : right0Middle3 4 3 = innerRightZ 3 4 3 * associatorZ 3 4 3 := by
  simpa only [HexagonAtoms343.assocABC_eq,
    HexagonAtoms343.outerABC_eq,
    HexagonAtoms343.assocBAC_eq,
    HexagonAtoms343.innerABC_eq,
    HexagonAtoms343.innerRightABC_eq,
    HexagonAtoms343.inverseACB_eq,
    HexagonAtoms343.innerACB_eq,
    HexagonAtoms343.assocBCA_eq,
    HexagonAtoms343.innerRightBAC_eq,
    HexagonAtoms343.assocCAB_eq,
    HexagonAtoms343.outerLeftABC_eq,
    HexagonRowColumn343.assocBCA_alias,
    HexagonRowColumn343.product0_eq,
    HexagonRowColumn343.product1_eq,
    HexagonRowColumn343.product2_eq,
    HexagonRowColumn343.product3_eq,
    HexagonRowColumn343.product4_eq,
    HexagonRowColumn343.product5_eq,
    HexagonRowColumn343.product6_eq,
    HexagonRowColumn343.product7_eq] using right0Middle3_eq_case_4_3_checked

private theorem right1Middle3_eq_case_4_3_row_0_0_0 : (right1Middle3 4 3) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn343.rows_inverseACB HexagonRowColumn343.cols_right0) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_4_3_row_0_0_1 : (right1Middle3 4 3) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn343.rows_inverseACB HexagonRowColumn343.cols_right0) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_4_3_row_0_0_2 : (right1Middle3 4 3) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn343.rows_inverseACB HexagonRowColumn343.cols_right0) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_4_3_row_0_0_3 : (right1Middle3 4 3) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn343.rows_inverseACB HexagonRowColumn343.cols_right0) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_4_3_row_0_1_0 : (right1Middle3 4 3) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn343.rows_inverseACB HexagonRowColumn343.cols_right0) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_4_3_row_0_1_1 : (right1Middle3 4 3) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn343.rows_inverseACB HexagonRowColumn343.cols_right0) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_4_3_row_0_1_2 : (right1Middle3 4 3) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn343.rows_inverseACB HexagonRowColumn343.cols_right0) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_4_3_row_0_1_3 : (right1Middle3 4 3) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn343.rows_inverseACB HexagonRowColumn343.cols_right0) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_4_3_row_1_0_0 : (right1Middle3 4 3) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn343.rows_inverseACB HexagonRowColumn343.cols_right0) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_4_3_row_1_0_1 : (right1Middle3 4 3) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn343.rows_inverseACB HexagonRowColumn343.cols_right0) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_4_3_row_1_0_2 : (right1Middle3 4 3) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn343.rows_inverseACB HexagonRowColumn343.cols_right0) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_4_3_row_1_0_3 : (right1Middle3 4 3) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn343.rows_inverseACB HexagonRowColumn343.cols_right0) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_4_3_row_1_1_0 : (right1Middle3 4 3) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn343.rows_inverseACB HexagonRowColumn343.cols_right0) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_4_3_row_1_1_1 : (right1Middle3 4 3) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn343.rows_inverseACB HexagonRowColumn343.cols_right0) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_4_3_row_1_1_2 : (right1Middle3 4 3) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn343.rows_inverseACB HexagonRowColumn343.cols_right0) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_4_3_row_1_1_3 : (right1Middle3 4 3) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn343.rows_inverseACB HexagonRowColumn343.cols_right0) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_4_3_row_2_0_0 : (right1Middle3 4 3) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn343.rows_inverseACB HexagonRowColumn343.cols_right0) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_4_3_row_2_0_1 : (right1Middle3 4 3) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn343.rows_inverseACB HexagonRowColumn343.cols_right0) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_4_3_row_2_0_2 : (right1Middle3 4 3) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn343.rows_inverseACB HexagonRowColumn343.cols_right0) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_4_3_row_2_0_3 : (right1Middle3 4 3) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn343.rows_inverseACB HexagonRowColumn343.cols_right0) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_4_3_row_2_1_0 : (right1Middle3 4 3) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn343.rows_inverseACB HexagonRowColumn343.cols_right0) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_4_3_row_2_1_1 : (right1Middle3 4 3) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn343.rows_inverseACB HexagonRowColumn343.cols_right0) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_4_3_row_2_1_2 : (right1Middle3 4 3) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn343.rows_inverseACB HexagonRowColumn343.cols_right0) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_4_3_row_2_1_3 : (right1Middle3 4 3) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn343.rows_inverseACB HexagonRowColumn343.cols_right0) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_4_3_row_3_0_0 : (right1Middle3 4 3) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn343.rows_inverseACB HexagonRowColumn343.cols_right0) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_4_3_row_3_0_1 : (right1Middle3 4 3) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn343.rows_inverseACB HexagonRowColumn343.cols_right0) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_4_3_row_3_0_2 : (right1Middle3 4 3) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn343.rows_inverseACB HexagonRowColumn343.cols_right0) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_4_3_row_3_0_3 : (right1Middle3 4 3) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn343.rows_inverseACB HexagonRowColumn343.cols_right0) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_4_3_row_3_1_0 : (right1Middle3 4 3) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn343.rows_inverseACB HexagonRowColumn343.cols_right0) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_4_3_row_3_1_1 : (right1Middle3 4 3) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn343.rows_inverseACB HexagonRowColumn343.cols_right0) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_4_3_row_3_1_2 : (right1Middle3 4 3) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn343.rows_inverseACB HexagonRowColumn343.cols_right0) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_4_3_row_3_1_3 : (right1Middle3 4 3) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn343.rows_inverseACB HexagonRowColumn343.cols_right0) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_4_3_checked : right1Middle3 4 3 = rowColumnMul HexagonRowColumn343.rows_inverseACB HexagonRowColumn343.cols_right0 := by
  funext r
  fin_cases r
  · exact right1Middle3_eq_case_4_3_row_0_0_0
  · exact right1Middle3_eq_case_4_3_row_0_0_1
  · exact right1Middle3_eq_case_4_3_row_0_0_2
  · exact right1Middle3_eq_case_4_3_row_0_0_3
  · exact right1Middle3_eq_case_4_3_row_0_1_0
  · exact right1Middle3_eq_case_4_3_row_0_1_1
  · exact right1Middle3_eq_case_4_3_row_0_1_2
  · exact right1Middle3_eq_case_4_3_row_0_1_3
  · exact right1Middle3_eq_case_4_3_row_1_0_0
  · exact right1Middle3_eq_case_4_3_row_1_0_1
  · exact right1Middle3_eq_case_4_3_row_1_0_2
  · exact right1Middle3_eq_case_4_3_row_1_0_3
  · exact right1Middle3_eq_case_4_3_row_1_1_0
  · exact right1Middle3_eq_case_4_3_row_1_1_1
  · exact right1Middle3_eq_case_4_3_row_1_1_2
  · exact right1Middle3_eq_case_4_3_row_1_1_3
  · exact right1Middle3_eq_case_4_3_row_2_0_0
  · exact right1Middle3_eq_case_4_3_row_2_0_1
  · exact right1Middle3_eq_case_4_3_row_2_0_2
  · exact right1Middle3_eq_case_4_3_row_2_0_3
  · exact right1Middle3_eq_case_4_3_row_2_1_0
  · exact right1Middle3_eq_case_4_3_row_2_1_1
  · exact right1Middle3_eq_case_4_3_row_2_1_2
  · exact right1Middle3_eq_case_4_3_row_2_1_3
  · exact right1Middle3_eq_case_4_3_row_3_0_0
  · exact right1Middle3_eq_case_4_3_row_3_0_1
  · exact right1Middle3_eq_case_4_3_row_3_0_2
  · exact right1Middle3_eq_case_4_3_row_3_0_3
  · exact right1Middle3_eq_case_4_3_row_3_1_0
  · exact right1Middle3_eq_case_4_3_row_3_1_1
  · exact right1Middle3_eq_case_4_3_row_3_1_2
  · exact right1Middle3_eq_case_4_3_row_3_1_3

set_option backward.isDefEq.respectTransparency false in
theorem right1Middle3_eq_case_4_3 : right1Middle3 4 3 = associatorInverseZ 3 3 4 * right0Middle3 4 3 := by
  simpa only [HexagonAtoms343.assocABC_eq,
    HexagonAtoms343.outerABC_eq,
    HexagonAtoms343.assocBAC_eq,
    HexagonAtoms343.innerABC_eq,
    HexagonAtoms343.innerRightABC_eq,
    HexagonAtoms343.inverseACB_eq,
    HexagonAtoms343.innerACB_eq,
    HexagonAtoms343.assocBCA_eq,
    HexagonAtoms343.innerRightBAC_eq,
    HexagonAtoms343.assocCAB_eq,
    HexagonAtoms343.outerLeftABC_eq,
    HexagonRowColumn343.assocBCA_alias,
    HexagonRowColumn343.product0_eq,
    HexagonRowColumn343.product1_eq,
    HexagonRowColumn343.product2_eq,
    HexagonRowColumn343.product3_eq,
    HexagonRowColumn343.product4_eq,
    HexagonRowColumn343.product5_eq,
    HexagonRowColumn343.product6_eq,
    HexagonRowColumn343.product7_eq] using right1Middle3_eq_case_4_3_checked

private theorem right2Middle3_eq_case_4_3_row_0_0_0 : (right2Middle3 4 3) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn343.rows_innerACB HexagonRowColumn343.cols_right1) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_4_3_row_0_0_1 : (right2Middle3 4 3) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn343.rows_innerACB HexagonRowColumn343.cols_right1) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_4_3_row_0_0_2 : (right2Middle3 4 3) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn343.rows_innerACB HexagonRowColumn343.cols_right1) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_4_3_row_0_0_3 : (right2Middle3 4 3) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn343.rows_innerACB HexagonRowColumn343.cols_right1) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_4_3_row_0_1_0 : (right2Middle3 4 3) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn343.rows_innerACB HexagonRowColumn343.cols_right1) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_4_3_row_0_1_1 : (right2Middle3 4 3) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn343.rows_innerACB HexagonRowColumn343.cols_right1) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_4_3_row_0_1_2 : (right2Middle3 4 3) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn343.rows_innerACB HexagonRowColumn343.cols_right1) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_4_3_row_0_1_3 : (right2Middle3 4 3) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn343.rows_innerACB HexagonRowColumn343.cols_right1) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_4_3_row_1_0_0 : (right2Middle3 4 3) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn343.rows_innerACB HexagonRowColumn343.cols_right1) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_4_3_row_1_0_1 : (right2Middle3 4 3) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn343.rows_innerACB HexagonRowColumn343.cols_right1) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_4_3_row_1_0_2 : (right2Middle3 4 3) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn343.rows_innerACB HexagonRowColumn343.cols_right1) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_4_3_row_1_0_3 : (right2Middle3 4 3) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn343.rows_innerACB HexagonRowColumn343.cols_right1) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_4_3_row_1_1_0 : (right2Middle3 4 3) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn343.rows_innerACB HexagonRowColumn343.cols_right1) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_4_3_row_1_1_1 : (right2Middle3 4 3) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn343.rows_innerACB HexagonRowColumn343.cols_right1) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_4_3_row_1_1_2 : (right2Middle3 4 3) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn343.rows_innerACB HexagonRowColumn343.cols_right1) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_4_3_row_1_1_3 : (right2Middle3 4 3) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn343.rows_innerACB HexagonRowColumn343.cols_right1) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_4_3_row_2_0_0 : (right2Middle3 4 3) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn343.rows_innerACB HexagonRowColumn343.cols_right1) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_4_3_row_2_0_1 : (right2Middle3 4 3) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn343.rows_innerACB HexagonRowColumn343.cols_right1) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_4_3_row_2_0_2 : (right2Middle3 4 3) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn343.rows_innerACB HexagonRowColumn343.cols_right1) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_4_3_row_2_0_3 : (right2Middle3 4 3) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn343.rows_innerACB HexagonRowColumn343.cols_right1) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_4_3_row_2_1_0 : (right2Middle3 4 3) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn343.rows_innerACB HexagonRowColumn343.cols_right1) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_4_3_row_2_1_1 : (right2Middle3 4 3) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn343.rows_innerACB HexagonRowColumn343.cols_right1) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_4_3_row_2_1_2 : (right2Middle3 4 3) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn343.rows_innerACB HexagonRowColumn343.cols_right1) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_4_3_row_2_1_3 : (right2Middle3 4 3) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn343.rows_innerACB HexagonRowColumn343.cols_right1) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_4_3_row_3_0_0 : (right2Middle3 4 3) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn343.rows_innerACB HexagonRowColumn343.cols_right1) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_4_3_row_3_0_1 : (right2Middle3 4 3) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn343.rows_innerACB HexagonRowColumn343.cols_right1) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_4_3_row_3_0_2 : (right2Middle3 4 3) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn343.rows_innerACB HexagonRowColumn343.cols_right1) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_4_3_row_3_0_3 : (right2Middle3 4 3) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn343.rows_innerACB HexagonRowColumn343.cols_right1) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_4_3_row_3_1_0 : (right2Middle3 4 3) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn343.rows_innerACB HexagonRowColumn343.cols_right1) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_4_3_row_3_1_1 : (right2Middle3 4 3) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn343.rows_innerACB HexagonRowColumn343.cols_right1) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_4_3_row_3_1_2 : (right2Middle3 4 3) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn343.rows_innerACB HexagonRowColumn343.cols_right1) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_4_3_row_3_1_3 : (right2Middle3 4 3) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn343.rows_innerACB HexagonRowColumn343.cols_right1) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_4_3_checked : right2Middle3 4 3 = rowColumnMul HexagonRowColumn343.rows_innerACB HexagonRowColumn343.cols_right1 := by
  funext r
  fin_cases r
  · exact right2Middle3_eq_case_4_3_row_0_0_0
  · exact right2Middle3_eq_case_4_3_row_0_0_1
  · exact right2Middle3_eq_case_4_3_row_0_0_2
  · exact right2Middle3_eq_case_4_3_row_0_0_3
  · exact right2Middle3_eq_case_4_3_row_0_1_0
  · exact right2Middle3_eq_case_4_3_row_0_1_1
  · exact right2Middle3_eq_case_4_3_row_0_1_2
  · exact right2Middle3_eq_case_4_3_row_0_1_3
  · exact right2Middle3_eq_case_4_3_row_1_0_0
  · exact right2Middle3_eq_case_4_3_row_1_0_1
  · exact right2Middle3_eq_case_4_3_row_1_0_2
  · exact right2Middle3_eq_case_4_3_row_1_0_3
  · exact right2Middle3_eq_case_4_3_row_1_1_0
  · exact right2Middle3_eq_case_4_3_row_1_1_1
  · exact right2Middle3_eq_case_4_3_row_1_1_2
  · exact right2Middle3_eq_case_4_3_row_1_1_3
  · exact right2Middle3_eq_case_4_3_row_2_0_0
  · exact right2Middle3_eq_case_4_3_row_2_0_1
  · exact right2Middle3_eq_case_4_3_row_2_0_2
  · exact right2Middle3_eq_case_4_3_row_2_0_3
  · exact right2Middle3_eq_case_4_3_row_2_1_0
  · exact right2Middle3_eq_case_4_3_row_2_1_1
  · exact right2Middle3_eq_case_4_3_row_2_1_2
  · exact right2Middle3_eq_case_4_3_row_2_1_3
  · exact right2Middle3_eq_case_4_3_row_3_0_0
  · exact right2Middle3_eq_case_4_3_row_3_0_1
  · exact right2Middle3_eq_case_4_3_row_3_0_2
  · exact right2Middle3_eq_case_4_3_row_3_0_3
  · exact right2Middle3_eq_case_4_3_row_3_1_0
  · exact right2Middle3_eq_case_4_3_row_3_1_1
  · exact right2Middle3_eq_case_4_3_row_3_1_2
  · exact right2Middle3_eq_case_4_3_row_3_1_3

set_option backward.isDefEq.respectTransparency false in
theorem right2Middle3_eq_case_4_3 : right2Middle3 4 3 = innerLeftZ 3 3 4 * right1Middle3 4 3 := by
  simpa only [HexagonAtoms343.assocABC_eq,
    HexagonAtoms343.outerABC_eq,
    HexagonAtoms343.assocBAC_eq,
    HexagonAtoms343.innerABC_eq,
    HexagonAtoms343.innerRightABC_eq,
    HexagonAtoms343.inverseACB_eq,
    HexagonAtoms343.innerACB_eq,
    HexagonAtoms343.assocBCA_eq,
    HexagonAtoms343.innerRightBAC_eq,
    HexagonAtoms343.assocCAB_eq,
    HexagonAtoms343.outerLeftABC_eq,
    HexagonRowColumn343.assocBCA_alias,
    HexagonRowColumn343.product0_eq,
    HexagonRowColumn343.product1_eq,
    HexagonRowColumn343.product2_eq,
    HexagonRowColumn343.product3_eq,
    HexagonRowColumn343.product4_eq,
    HexagonRowColumn343.product5_eq,
    HexagonRowColumn343.product6_eq,
    HexagonRowColumn343.product7_eq] using right2Middle3_eq_case_4_3_checked

private theorem leftFinal3_case_4_3_row_0_0_0 : (((-1 : ℤ) ^ (leftScaleBit 3 4 3).val * positiveScale (leftScaleExponent 3 4 3)) •
      (rowColumnMul HexagonRowColumn343.rows_assocBAC HexagonRowColumn343.cols_left0)) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 3 4 3) • (rowColumnMul HexagonRowColumn343.rows_innerRightBAC HexagonRowColumn343.cols_left1)) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal3_case_4_3_row_0_0_1 : (((-1 : ℤ) ^ (leftScaleBit 3 4 3).val * positiveScale (leftScaleExponent 3 4 3)) •
      (rowColumnMul HexagonRowColumn343.rows_assocBAC HexagonRowColumn343.cols_left0)) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 3 4 3) • (rowColumnMul HexagonRowColumn343.rows_innerRightBAC HexagonRowColumn343.cols_left1)) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal3_case_4_3_row_0_0_2 : (((-1 : ℤ) ^ (leftScaleBit 3 4 3).val * positiveScale (leftScaleExponent 3 4 3)) •
      (rowColumnMul HexagonRowColumn343.rows_assocBAC HexagonRowColumn343.cols_left0)) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 3 4 3) • (rowColumnMul HexagonRowColumn343.rows_innerRightBAC HexagonRowColumn343.cols_left1)) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal3_case_4_3_row_0_0_3 : (((-1 : ℤ) ^ (leftScaleBit 3 4 3).val * positiveScale (leftScaleExponent 3 4 3)) •
      (rowColumnMul HexagonRowColumn343.rows_assocBAC HexagonRowColumn343.cols_left0)) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 3 4 3) • (rowColumnMul HexagonRowColumn343.rows_innerRightBAC HexagonRowColumn343.cols_left1)) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal3_case_4_3_row_0_1_0 : (((-1 : ℤ) ^ (leftScaleBit 3 4 3).val * positiveScale (leftScaleExponent 3 4 3)) •
      (rowColumnMul HexagonRowColumn343.rows_assocBAC HexagonRowColumn343.cols_left0)) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 3 4 3) • (rowColumnMul HexagonRowColumn343.rows_innerRightBAC HexagonRowColumn343.cols_left1)) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal3_case_4_3_row_0_1_1 : (((-1 : ℤ) ^ (leftScaleBit 3 4 3).val * positiveScale (leftScaleExponent 3 4 3)) •
      (rowColumnMul HexagonRowColumn343.rows_assocBAC HexagonRowColumn343.cols_left0)) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 3 4 3) • (rowColumnMul HexagonRowColumn343.rows_innerRightBAC HexagonRowColumn343.cols_left1)) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal3_case_4_3_row_0_1_2 : (((-1 : ℤ) ^ (leftScaleBit 3 4 3).val * positiveScale (leftScaleExponent 3 4 3)) •
      (rowColumnMul HexagonRowColumn343.rows_assocBAC HexagonRowColumn343.cols_left0)) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 3 4 3) • (rowColumnMul HexagonRowColumn343.rows_innerRightBAC HexagonRowColumn343.cols_left1)) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal3_case_4_3_row_0_1_3 : (((-1 : ℤ) ^ (leftScaleBit 3 4 3).val * positiveScale (leftScaleExponent 3 4 3)) •
      (rowColumnMul HexagonRowColumn343.rows_assocBAC HexagonRowColumn343.cols_left0)) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 3 4 3) • (rowColumnMul HexagonRowColumn343.rows_innerRightBAC HexagonRowColumn343.cols_left1)) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal3_case_4_3_row_1_0_0 : (((-1 : ℤ) ^ (leftScaleBit 3 4 3).val * positiveScale (leftScaleExponent 3 4 3)) •
      (rowColumnMul HexagonRowColumn343.rows_assocBAC HexagonRowColumn343.cols_left0)) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 3 4 3) • (rowColumnMul HexagonRowColumn343.rows_innerRightBAC HexagonRowColumn343.cols_left1)) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal3_case_4_3_row_1_0_1 : (((-1 : ℤ) ^ (leftScaleBit 3 4 3).val * positiveScale (leftScaleExponent 3 4 3)) •
      (rowColumnMul HexagonRowColumn343.rows_assocBAC HexagonRowColumn343.cols_left0)) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 3 4 3) • (rowColumnMul HexagonRowColumn343.rows_innerRightBAC HexagonRowColumn343.cols_left1)) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal3_case_4_3_row_1_0_2 : (((-1 : ℤ) ^ (leftScaleBit 3 4 3).val * positiveScale (leftScaleExponent 3 4 3)) •
      (rowColumnMul HexagonRowColumn343.rows_assocBAC HexagonRowColumn343.cols_left0)) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 3 4 3) • (rowColumnMul HexagonRowColumn343.rows_innerRightBAC HexagonRowColumn343.cols_left1)) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal3_case_4_3_row_1_0_3 : (((-1 : ℤ) ^ (leftScaleBit 3 4 3).val * positiveScale (leftScaleExponent 3 4 3)) •
      (rowColumnMul HexagonRowColumn343.rows_assocBAC HexagonRowColumn343.cols_left0)) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 3 4 3) • (rowColumnMul HexagonRowColumn343.rows_innerRightBAC HexagonRowColumn343.cols_left1)) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal3_case_4_3_row_1_1_0 : (((-1 : ℤ) ^ (leftScaleBit 3 4 3).val * positiveScale (leftScaleExponent 3 4 3)) •
      (rowColumnMul HexagonRowColumn343.rows_assocBAC HexagonRowColumn343.cols_left0)) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 3 4 3) • (rowColumnMul HexagonRowColumn343.rows_innerRightBAC HexagonRowColumn343.cols_left1)) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal3_case_4_3_row_1_1_1 : (((-1 : ℤ) ^ (leftScaleBit 3 4 3).val * positiveScale (leftScaleExponent 3 4 3)) •
      (rowColumnMul HexagonRowColumn343.rows_assocBAC HexagonRowColumn343.cols_left0)) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 3 4 3) • (rowColumnMul HexagonRowColumn343.rows_innerRightBAC HexagonRowColumn343.cols_left1)) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal3_case_4_3_row_1_1_2 : (((-1 : ℤ) ^ (leftScaleBit 3 4 3).val * positiveScale (leftScaleExponent 3 4 3)) •
      (rowColumnMul HexagonRowColumn343.rows_assocBAC HexagonRowColumn343.cols_left0)) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 3 4 3) • (rowColumnMul HexagonRowColumn343.rows_innerRightBAC HexagonRowColumn343.cols_left1)) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal3_case_4_3_row_1_1_3 : (((-1 : ℤ) ^ (leftScaleBit 3 4 3).val * positiveScale (leftScaleExponent 3 4 3)) •
      (rowColumnMul HexagonRowColumn343.rows_assocBAC HexagonRowColumn343.cols_left0)) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 3 4 3) • (rowColumnMul HexagonRowColumn343.rows_innerRightBAC HexagonRowColumn343.cols_left1)) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal3_case_4_3_row_2_0_0 : (((-1 : ℤ) ^ (leftScaleBit 3 4 3).val * positiveScale (leftScaleExponent 3 4 3)) •
      (rowColumnMul HexagonRowColumn343.rows_assocBAC HexagonRowColumn343.cols_left0)) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 3 4 3) • (rowColumnMul HexagonRowColumn343.rows_innerRightBAC HexagonRowColumn343.cols_left1)) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal3_case_4_3_row_2_0_1 : (((-1 : ℤ) ^ (leftScaleBit 3 4 3).val * positiveScale (leftScaleExponent 3 4 3)) •
      (rowColumnMul HexagonRowColumn343.rows_assocBAC HexagonRowColumn343.cols_left0)) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 3 4 3) • (rowColumnMul HexagonRowColumn343.rows_innerRightBAC HexagonRowColumn343.cols_left1)) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal3_case_4_3_row_2_0_2 : (((-1 : ℤ) ^ (leftScaleBit 3 4 3).val * positiveScale (leftScaleExponent 3 4 3)) •
      (rowColumnMul HexagonRowColumn343.rows_assocBAC HexagonRowColumn343.cols_left0)) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 3 4 3) • (rowColumnMul HexagonRowColumn343.rows_innerRightBAC HexagonRowColumn343.cols_left1)) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal3_case_4_3_row_2_0_3 : (((-1 : ℤ) ^ (leftScaleBit 3 4 3).val * positiveScale (leftScaleExponent 3 4 3)) •
      (rowColumnMul HexagonRowColumn343.rows_assocBAC HexagonRowColumn343.cols_left0)) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 3 4 3) • (rowColumnMul HexagonRowColumn343.rows_innerRightBAC HexagonRowColumn343.cols_left1)) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal3_case_4_3_row_2_1_0 : (((-1 : ℤ) ^ (leftScaleBit 3 4 3).val * positiveScale (leftScaleExponent 3 4 3)) •
      (rowColumnMul HexagonRowColumn343.rows_assocBAC HexagonRowColumn343.cols_left0)) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 3 4 3) • (rowColumnMul HexagonRowColumn343.rows_innerRightBAC HexagonRowColumn343.cols_left1)) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal3_case_4_3_row_2_1_1 : (((-1 : ℤ) ^ (leftScaleBit 3 4 3).val * positiveScale (leftScaleExponent 3 4 3)) •
      (rowColumnMul HexagonRowColumn343.rows_assocBAC HexagonRowColumn343.cols_left0)) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 3 4 3) • (rowColumnMul HexagonRowColumn343.rows_innerRightBAC HexagonRowColumn343.cols_left1)) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal3_case_4_3_row_2_1_2 : (((-1 : ℤ) ^ (leftScaleBit 3 4 3).val * positiveScale (leftScaleExponent 3 4 3)) •
      (rowColumnMul HexagonRowColumn343.rows_assocBAC HexagonRowColumn343.cols_left0)) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 3 4 3) • (rowColumnMul HexagonRowColumn343.rows_innerRightBAC HexagonRowColumn343.cols_left1)) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal3_case_4_3_row_2_1_3 : (((-1 : ℤ) ^ (leftScaleBit 3 4 3).val * positiveScale (leftScaleExponent 3 4 3)) •
      (rowColumnMul HexagonRowColumn343.rows_assocBAC HexagonRowColumn343.cols_left0)) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 3 4 3) • (rowColumnMul HexagonRowColumn343.rows_innerRightBAC HexagonRowColumn343.cols_left1)) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal3_case_4_3_row_3_0_0 : (((-1 : ℤ) ^ (leftScaleBit 3 4 3).val * positiveScale (leftScaleExponent 3 4 3)) •
      (rowColumnMul HexagonRowColumn343.rows_assocBAC HexagonRowColumn343.cols_left0)) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 3 4 3) • (rowColumnMul HexagonRowColumn343.rows_innerRightBAC HexagonRowColumn343.cols_left1)) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal3_case_4_3_row_3_0_1 : (((-1 : ℤ) ^ (leftScaleBit 3 4 3).val * positiveScale (leftScaleExponent 3 4 3)) •
      (rowColumnMul HexagonRowColumn343.rows_assocBAC HexagonRowColumn343.cols_left0)) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 3 4 3) • (rowColumnMul HexagonRowColumn343.rows_innerRightBAC HexagonRowColumn343.cols_left1)) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal3_case_4_3_row_3_0_2 : (((-1 : ℤ) ^ (leftScaleBit 3 4 3).val * positiveScale (leftScaleExponent 3 4 3)) •
      (rowColumnMul HexagonRowColumn343.rows_assocBAC HexagonRowColumn343.cols_left0)) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 3 4 3) • (rowColumnMul HexagonRowColumn343.rows_innerRightBAC HexagonRowColumn343.cols_left1)) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal3_case_4_3_row_3_0_3 : (((-1 : ℤ) ^ (leftScaleBit 3 4 3).val * positiveScale (leftScaleExponent 3 4 3)) •
      (rowColumnMul HexagonRowColumn343.rows_assocBAC HexagonRowColumn343.cols_left0)) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 3 4 3) • (rowColumnMul HexagonRowColumn343.rows_innerRightBAC HexagonRowColumn343.cols_left1)) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal3_case_4_3_row_3_1_0 : (((-1 : ℤ) ^ (leftScaleBit 3 4 3).val * positiveScale (leftScaleExponent 3 4 3)) •
      (rowColumnMul HexagonRowColumn343.rows_assocBAC HexagonRowColumn343.cols_left0)) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 3 4 3) • (rowColumnMul HexagonRowColumn343.rows_innerRightBAC HexagonRowColumn343.cols_left1)) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal3_case_4_3_row_3_1_1 : (((-1 : ℤ) ^ (leftScaleBit 3 4 3).val * positiveScale (leftScaleExponent 3 4 3)) •
      (rowColumnMul HexagonRowColumn343.rows_assocBAC HexagonRowColumn343.cols_left0)) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 3 4 3) • (rowColumnMul HexagonRowColumn343.rows_innerRightBAC HexagonRowColumn343.cols_left1)) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal3_case_4_3_row_3_1_2 : (((-1 : ℤ) ^ (leftScaleBit 3 4 3).val * positiveScale (leftScaleExponent 3 4 3)) •
      (rowColumnMul HexagonRowColumn343.rows_assocBAC HexagonRowColumn343.cols_left0)) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 3 4 3) • (rowColumnMul HexagonRowColumn343.rows_innerRightBAC HexagonRowColumn343.cols_left1)) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal3_case_4_3_row_3_1_3 : (((-1 : ℤ) ^ (leftScaleBit 3 4 3).val * positiveScale (leftScaleExponent 3 4 3)) •
      (rowColumnMul HexagonRowColumn343.rows_assocBAC HexagonRowColumn343.cols_left0)) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 3 4 3) • (rowColumnMul HexagonRowColumn343.rows_innerRightBAC HexagonRowColumn343.cols_left1)) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal3_case_4_3_checked : ((-1 : ℤ) ^ (leftScaleBit 3 4 3).val * positiveScale (leftScaleExponent 3 4 3)) •
      (rowColumnMul HexagonRowColumn343.rows_assocBAC HexagonRowColumn343.cols_left0) = negativeScale (leftScaleExponent 3 4 3) • (rowColumnMul HexagonRowColumn343.rows_innerRightBAC HexagonRowColumn343.cols_left1) := by
  funext r
  fin_cases r
  · exact leftFinal3_case_4_3_row_0_0_0
  · exact leftFinal3_case_4_3_row_0_0_1
  · exact leftFinal3_case_4_3_row_0_0_2
  · exact leftFinal3_case_4_3_row_0_0_3
  · exact leftFinal3_case_4_3_row_0_1_0
  · exact leftFinal3_case_4_3_row_0_1_1
  · exact leftFinal3_case_4_3_row_0_1_2
  · exact leftFinal3_case_4_3_row_0_1_3
  · exact leftFinal3_case_4_3_row_1_0_0
  · exact leftFinal3_case_4_3_row_1_0_1
  · exact leftFinal3_case_4_3_row_1_0_2
  · exact leftFinal3_case_4_3_row_1_0_3
  · exact leftFinal3_case_4_3_row_1_1_0
  · exact leftFinal3_case_4_3_row_1_1_1
  · exact leftFinal3_case_4_3_row_1_1_2
  · exact leftFinal3_case_4_3_row_1_1_3
  · exact leftFinal3_case_4_3_row_2_0_0
  · exact leftFinal3_case_4_3_row_2_0_1
  · exact leftFinal3_case_4_3_row_2_0_2
  · exact leftFinal3_case_4_3_row_2_0_3
  · exact leftFinal3_case_4_3_row_2_1_0
  · exact leftFinal3_case_4_3_row_2_1_1
  · exact leftFinal3_case_4_3_row_2_1_2
  · exact leftFinal3_case_4_3_row_2_1_3
  · exact leftFinal3_case_4_3_row_3_0_0
  · exact leftFinal3_case_4_3_row_3_0_1
  · exact leftFinal3_case_4_3_row_3_0_2
  · exact leftFinal3_case_4_3_row_3_0_3
  · exact leftFinal3_case_4_3_row_3_1_0
  · exact leftFinal3_case_4_3_row_3_1_1
  · exact leftFinal3_case_4_3_row_3_1_2
  · exact leftFinal3_case_4_3_row_3_1_3

set_option backward.isDefEq.respectTransparency false in
theorem leftFinal3_case_4_3 : ((-1 : ℤ) ^ (leftScaleBit 3 4 3).val * positiveScale (leftScaleExponent 3 4 3)) •
      (associatorZ 4 3 3 * left0Middle3 4 3) = negativeScale (leftScaleExponent 3 4 3) • (innerRightZ 4 3 3 * left1Middle3 4 3) := by
  simpa only [HexagonAtoms343.assocABC_eq,
    HexagonAtoms343.outerABC_eq,
    HexagonAtoms343.assocBAC_eq,
    HexagonAtoms343.innerABC_eq,
    HexagonAtoms343.innerRightABC_eq,
    HexagonAtoms343.inverseACB_eq,
    HexagonAtoms343.innerACB_eq,
    HexagonAtoms343.assocBCA_eq,
    HexagonAtoms343.innerRightBAC_eq,
    HexagonAtoms343.assocCAB_eq,
    HexagonAtoms343.outerLeftABC_eq,
    HexagonRowColumn343.assocBCA_alias,
    HexagonRowColumn343.product0_eq,
    HexagonRowColumn343.product1_eq,
    HexagonRowColumn343.product2_eq,
    HexagonRowColumn343.product3_eq,
    HexagonRowColumn343.product4_eq,
    HexagonRowColumn343.product5_eq,
    HexagonRowColumn343.product6_eq,
    HexagonRowColumn343.product7_eq] using leftFinal3_case_4_3_checked

private theorem rightFinal3_case_4_3_row_0_0_0 : (((-1 : ℤ) ^ (rightScaleBit 3 4 3).val * positiveScale (rightScaleExponent 3 4 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 3 4 : ℤ)) • HexagonAtoms343.outerLeftABC) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 3 4 3) • (rowColumnMul HexagonRowColumn343.rows_assocCAB HexagonRowColumn343.cols_right2)) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal3_case_4_3_row_0_0_1 : (((-1 : ℤ) ^ (rightScaleBit 3 4 3).val * positiveScale (rightScaleExponent 3 4 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 3 4 : ℤ)) • HexagonAtoms343.outerLeftABC) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 3 4 3) • (rowColumnMul HexagonRowColumn343.rows_assocCAB HexagonRowColumn343.cols_right2)) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal3_case_4_3_row_0_0_2 : (((-1 : ℤ) ^ (rightScaleBit 3 4 3).val * positiveScale (rightScaleExponent 3 4 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 3 4 : ℤ)) • HexagonAtoms343.outerLeftABC) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 3 4 3) • (rowColumnMul HexagonRowColumn343.rows_assocCAB HexagonRowColumn343.cols_right2)) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal3_case_4_3_row_0_0_3 : (((-1 : ℤ) ^ (rightScaleBit 3 4 3).val * positiveScale (rightScaleExponent 3 4 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 3 4 : ℤ)) • HexagonAtoms343.outerLeftABC) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 3 4 3) • (rowColumnMul HexagonRowColumn343.rows_assocCAB HexagonRowColumn343.cols_right2)) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal3_case_4_3_row_0_1_0 : (((-1 : ℤ) ^ (rightScaleBit 3 4 3).val * positiveScale (rightScaleExponent 3 4 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 3 4 : ℤ)) • HexagonAtoms343.outerLeftABC) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 3 4 3) • (rowColumnMul HexagonRowColumn343.rows_assocCAB HexagonRowColumn343.cols_right2)) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal3_case_4_3_row_0_1_1 : (((-1 : ℤ) ^ (rightScaleBit 3 4 3).val * positiveScale (rightScaleExponent 3 4 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 3 4 : ℤ)) • HexagonAtoms343.outerLeftABC) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 3 4 3) • (rowColumnMul HexagonRowColumn343.rows_assocCAB HexagonRowColumn343.cols_right2)) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal3_case_4_3_row_0_1_2 : (((-1 : ℤ) ^ (rightScaleBit 3 4 3).val * positiveScale (rightScaleExponent 3 4 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 3 4 : ℤ)) • HexagonAtoms343.outerLeftABC) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 3 4 3) • (rowColumnMul HexagonRowColumn343.rows_assocCAB HexagonRowColumn343.cols_right2)) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal3_case_4_3_row_0_1_3 : (((-1 : ℤ) ^ (rightScaleBit 3 4 3).val * positiveScale (rightScaleExponent 3 4 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 3 4 : ℤ)) • HexagonAtoms343.outerLeftABC) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 3 4 3) • (rowColumnMul HexagonRowColumn343.rows_assocCAB HexagonRowColumn343.cols_right2)) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal3_case_4_3_row_1_0_0 : (((-1 : ℤ) ^ (rightScaleBit 3 4 3).val * positiveScale (rightScaleExponent 3 4 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 3 4 : ℤ)) • HexagonAtoms343.outerLeftABC) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 3 4 3) • (rowColumnMul HexagonRowColumn343.rows_assocCAB HexagonRowColumn343.cols_right2)) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal3_case_4_3_row_1_0_1 : (((-1 : ℤ) ^ (rightScaleBit 3 4 3).val * positiveScale (rightScaleExponent 3 4 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 3 4 : ℤ)) • HexagonAtoms343.outerLeftABC) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 3 4 3) • (rowColumnMul HexagonRowColumn343.rows_assocCAB HexagonRowColumn343.cols_right2)) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal3_case_4_3_row_1_0_2 : (((-1 : ℤ) ^ (rightScaleBit 3 4 3).val * positiveScale (rightScaleExponent 3 4 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 3 4 : ℤ)) • HexagonAtoms343.outerLeftABC) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 3 4 3) • (rowColumnMul HexagonRowColumn343.rows_assocCAB HexagonRowColumn343.cols_right2)) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal3_case_4_3_row_1_0_3 : (((-1 : ℤ) ^ (rightScaleBit 3 4 3).val * positiveScale (rightScaleExponent 3 4 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 3 4 : ℤ)) • HexagonAtoms343.outerLeftABC) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 3 4 3) • (rowColumnMul HexagonRowColumn343.rows_assocCAB HexagonRowColumn343.cols_right2)) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal3_case_4_3_row_1_1_0 : (((-1 : ℤ) ^ (rightScaleBit 3 4 3).val * positiveScale (rightScaleExponent 3 4 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 3 4 : ℤ)) • HexagonAtoms343.outerLeftABC) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 3 4 3) • (rowColumnMul HexagonRowColumn343.rows_assocCAB HexagonRowColumn343.cols_right2)) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal3_case_4_3_row_1_1_1 : (((-1 : ℤ) ^ (rightScaleBit 3 4 3).val * positiveScale (rightScaleExponent 3 4 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 3 4 : ℤ)) • HexagonAtoms343.outerLeftABC) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 3 4 3) • (rowColumnMul HexagonRowColumn343.rows_assocCAB HexagonRowColumn343.cols_right2)) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal3_case_4_3_row_1_1_2 : (((-1 : ℤ) ^ (rightScaleBit 3 4 3).val * positiveScale (rightScaleExponent 3 4 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 3 4 : ℤ)) • HexagonAtoms343.outerLeftABC) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 3 4 3) • (rowColumnMul HexagonRowColumn343.rows_assocCAB HexagonRowColumn343.cols_right2)) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal3_case_4_3_row_1_1_3 : (((-1 : ℤ) ^ (rightScaleBit 3 4 3).val * positiveScale (rightScaleExponent 3 4 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 3 4 : ℤ)) • HexagonAtoms343.outerLeftABC) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 3 4 3) • (rowColumnMul HexagonRowColumn343.rows_assocCAB HexagonRowColumn343.cols_right2)) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal3_case_4_3_row_2_0_0 : (((-1 : ℤ) ^ (rightScaleBit 3 4 3).val * positiveScale (rightScaleExponent 3 4 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 3 4 : ℤ)) • HexagonAtoms343.outerLeftABC) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 3 4 3) • (rowColumnMul HexagonRowColumn343.rows_assocCAB HexagonRowColumn343.cols_right2)) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal3_case_4_3_row_2_0_1 : (((-1 : ℤ) ^ (rightScaleBit 3 4 3).val * positiveScale (rightScaleExponent 3 4 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 3 4 : ℤ)) • HexagonAtoms343.outerLeftABC) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 3 4 3) • (rowColumnMul HexagonRowColumn343.rows_assocCAB HexagonRowColumn343.cols_right2)) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal3_case_4_3_row_2_0_2 : (((-1 : ℤ) ^ (rightScaleBit 3 4 3).val * positiveScale (rightScaleExponent 3 4 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 3 4 : ℤ)) • HexagonAtoms343.outerLeftABC) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 3 4 3) • (rowColumnMul HexagonRowColumn343.rows_assocCAB HexagonRowColumn343.cols_right2)) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal3_case_4_3_row_2_0_3 : (((-1 : ℤ) ^ (rightScaleBit 3 4 3).val * positiveScale (rightScaleExponent 3 4 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 3 4 : ℤ)) • HexagonAtoms343.outerLeftABC) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 3 4 3) • (rowColumnMul HexagonRowColumn343.rows_assocCAB HexagonRowColumn343.cols_right2)) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal3_case_4_3_row_2_1_0 : (((-1 : ℤ) ^ (rightScaleBit 3 4 3).val * positiveScale (rightScaleExponent 3 4 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 3 4 : ℤ)) • HexagonAtoms343.outerLeftABC) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 3 4 3) • (rowColumnMul HexagonRowColumn343.rows_assocCAB HexagonRowColumn343.cols_right2)) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal3_case_4_3_row_2_1_1 : (((-1 : ℤ) ^ (rightScaleBit 3 4 3).val * positiveScale (rightScaleExponent 3 4 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 3 4 : ℤ)) • HexagonAtoms343.outerLeftABC) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 3 4 3) • (rowColumnMul HexagonRowColumn343.rows_assocCAB HexagonRowColumn343.cols_right2)) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal3_case_4_3_row_2_1_2 : (((-1 : ℤ) ^ (rightScaleBit 3 4 3).val * positiveScale (rightScaleExponent 3 4 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 3 4 : ℤ)) • HexagonAtoms343.outerLeftABC) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 3 4 3) • (rowColumnMul HexagonRowColumn343.rows_assocCAB HexagonRowColumn343.cols_right2)) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal3_case_4_3_row_2_1_3 : (((-1 : ℤ) ^ (rightScaleBit 3 4 3).val * positiveScale (rightScaleExponent 3 4 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 3 4 : ℤ)) • HexagonAtoms343.outerLeftABC) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 3 4 3) • (rowColumnMul HexagonRowColumn343.rows_assocCAB HexagonRowColumn343.cols_right2)) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal3_case_4_3_row_3_0_0 : (((-1 : ℤ) ^ (rightScaleBit 3 4 3).val * positiveScale (rightScaleExponent 3 4 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 3 4 : ℤ)) • HexagonAtoms343.outerLeftABC) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 3 4 3) • (rowColumnMul HexagonRowColumn343.rows_assocCAB HexagonRowColumn343.cols_right2)) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal3_case_4_3_row_3_0_1 : (((-1 : ℤ) ^ (rightScaleBit 3 4 3).val * positiveScale (rightScaleExponent 3 4 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 3 4 : ℤ)) • HexagonAtoms343.outerLeftABC) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 3 4 3) • (rowColumnMul HexagonRowColumn343.rows_assocCAB HexagonRowColumn343.cols_right2)) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal3_case_4_3_row_3_0_2 : (((-1 : ℤ) ^ (rightScaleBit 3 4 3).val * positiveScale (rightScaleExponent 3 4 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 3 4 : ℤ)) • HexagonAtoms343.outerLeftABC) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 3 4 3) • (rowColumnMul HexagonRowColumn343.rows_assocCAB HexagonRowColumn343.cols_right2)) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal3_case_4_3_row_3_0_3 : (((-1 : ℤ) ^ (rightScaleBit 3 4 3).val * positiveScale (rightScaleExponent 3 4 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 3 4 : ℤ)) • HexagonAtoms343.outerLeftABC) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 3 4 3) • (rowColumnMul HexagonRowColumn343.rows_assocCAB HexagonRowColumn343.cols_right2)) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal3_case_4_3_row_3_1_0 : (((-1 : ℤ) ^ (rightScaleBit 3 4 3).val * positiveScale (rightScaleExponent 3 4 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 3 4 : ℤ)) • HexagonAtoms343.outerLeftABC) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 3 4 3) • (rowColumnMul HexagonRowColumn343.rows_assocCAB HexagonRowColumn343.cols_right2)) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal3_case_4_3_row_3_1_1 : (((-1 : ℤ) ^ (rightScaleBit 3 4 3).val * positiveScale (rightScaleExponent 3 4 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 3 4 : ℤ)) • HexagonAtoms343.outerLeftABC) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 3 4 3) • (rowColumnMul HexagonRowColumn343.rows_assocCAB HexagonRowColumn343.cols_right2)) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal3_case_4_3_row_3_1_2 : (((-1 : ℤ) ^ (rightScaleBit 3 4 3).val * positiveScale (rightScaleExponent 3 4 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 3 4 : ℤ)) • HexagonAtoms343.outerLeftABC) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 3 4 3) • (rowColumnMul HexagonRowColumn343.rows_assocCAB HexagonRowColumn343.cols_right2)) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal3_case_4_3_row_3_1_3 : (((-1 : ℤ) ^ (rightScaleBit 3 4 3).val * positiveScale (rightScaleExponent 3 4 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 3 4 : ℤ)) • HexagonAtoms343.outerLeftABC) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 3 4 3) • (rowColumnMul HexagonRowColumn343.rows_assocCAB HexagonRowColumn343.cols_right2)) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal3_case_4_3_checked : ((-1 : ℤ) ^ (rightScaleBit 3 4 3).val * positiveScale (rightScaleExponent 3 4 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 3 4 : ℤ)) • HexagonAtoms343.outerLeftABC = negativeScale (rightScaleExponent 3 4 3) • (rowColumnMul HexagonRowColumn343.rows_assocCAB HexagonRowColumn343.cols_right2) := by
  funext r
  fin_cases r
  · exact rightFinal3_case_4_3_row_0_0_0
  · exact rightFinal3_case_4_3_row_0_0_1
  · exact rightFinal3_case_4_3_row_0_0_2
  · exact rightFinal3_case_4_3_row_0_0_3
  · exact rightFinal3_case_4_3_row_0_1_0
  · exact rightFinal3_case_4_3_row_0_1_1
  · exact rightFinal3_case_4_3_row_0_1_2
  · exact rightFinal3_case_4_3_row_0_1_3
  · exact rightFinal3_case_4_3_row_1_0_0
  · exact rightFinal3_case_4_3_row_1_0_1
  · exact rightFinal3_case_4_3_row_1_0_2
  · exact rightFinal3_case_4_3_row_1_0_3
  · exact rightFinal3_case_4_3_row_1_1_0
  · exact rightFinal3_case_4_3_row_1_1_1
  · exact rightFinal3_case_4_3_row_1_1_2
  · exact rightFinal3_case_4_3_row_1_1_3
  · exact rightFinal3_case_4_3_row_2_0_0
  · exact rightFinal3_case_4_3_row_2_0_1
  · exact rightFinal3_case_4_3_row_2_0_2
  · exact rightFinal3_case_4_3_row_2_0_3
  · exact rightFinal3_case_4_3_row_2_1_0
  · exact rightFinal3_case_4_3_row_2_1_1
  · exact rightFinal3_case_4_3_row_2_1_2
  · exact rightFinal3_case_4_3_row_2_1_3
  · exact rightFinal3_case_4_3_row_3_0_0
  · exact rightFinal3_case_4_3_row_3_0_1
  · exact rightFinal3_case_4_3_row_3_0_2
  · exact rightFinal3_case_4_3_row_3_0_3
  · exact rightFinal3_case_4_3_row_3_1_0
  · exact rightFinal3_case_4_3_row_3_1_1
  · exact rightFinal3_case_4_3_row_3_1_2
  · exact rightFinal3_case_4_3_row_3_1_3

set_option backward.isDefEq.respectTransparency false in
theorem rightFinal3_case_4_3 : ((-1 : ℤ) ^ (rightScaleBit 3 4 3).val * positiveScale (rightScaleExponent 3 4 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 3 4 : ℤ)) • outerLeftZ 3 4 3 = negativeScale (rightScaleExponent 3 4 3) • (associatorZ 3 3 4 * right2Middle3 4 3) := by
  simpa only [HexagonAtoms343.assocABC_eq,
    HexagonAtoms343.outerABC_eq,
    HexagonAtoms343.assocBAC_eq,
    HexagonAtoms343.innerABC_eq,
    HexagonAtoms343.innerRightABC_eq,
    HexagonAtoms343.inverseACB_eq,
    HexagonAtoms343.innerACB_eq,
    HexagonAtoms343.assocBCA_eq,
    HexagonAtoms343.innerRightBAC_eq,
    HexagonAtoms343.assocCAB_eq,
    HexagonAtoms343.outerLeftABC_eq,
    HexagonRowColumn343.assocBCA_alias,
    HexagonRowColumn343.product0_eq,
    HexagonRowColumn343.product1_eq,
    HexagonRowColumn343.product2_eq,
    HexagonRowColumn343.product3_eq,
    HexagonRowColumn343.product4_eq,
    HexagonRowColumn343.product5_eq,
    HexagonRowColumn343.product6_eq,
    HexagonRowColumn343.product7_eq] using rightFinal3_case_4_3_checked

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonCases3
