import RMod.BrundanEllis.StackingReferenceHexagonMiddle7
import RMod.BrundanEllis.StackingReferenceSparseMatrixCheck
import RMod.BrundanEllis.StackingReferenceHexagonAtoms724
import RMod.BrundanEllis.StackingReferenceHexagonRowColumn724

/-! Seven closed product identities for one reference triple.
The proof uses only verified atomic maps and ordinary kernel reduction. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
set_option linter.unusedSimpArgs false
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonCases7
open Superfusion

private theorem left0Middle7_eq_case_2_4_row_0_0_0 : (left0Middle7 2 4) ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8)) = (rowColumnMul HexagonRowColumn724.rows_outerABC HexagonRowColumn724.cols_assocABC) ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem left0Middle7_eq_case_2_4_row_0_0_1 : (left0Middle7 2 4) ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8)) = (rowColumnMul HexagonRowColumn724.rows_outerABC HexagonRowColumn724.cols_assocABC) ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem left0Middle7_eq_case_2_4_row_0_0_2 : (left0Middle7 2 4) ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8)) = (rowColumnMul HexagonRowColumn724.rows_outerABC HexagonRowColumn724.cols_assocABC) ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem left0Middle7_eq_case_2_4_row_0_0_3 : (left0Middle7 2 4) ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8)) = (rowColumnMul HexagonRowColumn724.rows_outerABC HexagonRowColumn724.cols_assocABC) ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem left0Middle7_eq_case_2_4_row_0_0_4 : (left0Middle7 2 4) ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8)) = (rowColumnMul HexagonRowColumn724.rows_outerABC HexagonRowColumn724.cols_assocABC) ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem left0Middle7_eq_case_2_4_row_0_0_5 : (left0Middle7 2 4) ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8)) = (rowColumnMul HexagonRowColumn724.rows_outerABC HexagonRowColumn724.cols_assocABC) ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem left0Middle7_eq_case_2_4_row_0_0_6 : (left0Middle7 2 4) ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8)) = (rowColumnMul HexagonRowColumn724.rows_outerABC HexagonRowColumn724.cols_assocABC) ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem left0Middle7_eq_case_2_4_row_0_0_7 : (left0Middle7 2 4) ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8)) = (rowColumnMul HexagonRowColumn724.rows_outerABC HexagonRowColumn724.cols_assocABC) ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem left0Middle7_eq_case_2_4_row_1_0_0 : (left0Middle7 2 4) ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8)) = (rowColumnMul HexagonRowColumn724.rows_outerABC HexagonRowColumn724.cols_assocABC) ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem left0Middle7_eq_case_2_4_row_1_0_1 : (left0Middle7 2 4) ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8)) = (rowColumnMul HexagonRowColumn724.rows_outerABC HexagonRowColumn724.cols_assocABC) ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem left0Middle7_eq_case_2_4_row_1_0_2 : (left0Middle7 2 4) ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8)) = (rowColumnMul HexagonRowColumn724.rows_outerABC HexagonRowColumn724.cols_assocABC) ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem left0Middle7_eq_case_2_4_row_1_0_3 : (left0Middle7 2 4) ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8)) = (rowColumnMul HexagonRowColumn724.rows_outerABC HexagonRowColumn724.cols_assocABC) ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem left0Middle7_eq_case_2_4_row_1_0_4 : (left0Middle7 2 4) ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8)) = (rowColumnMul HexagonRowColumn724.rows_outerABC HexagonRowColumn724.cols_assocABC) ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem left0Middle7_eq_case_2_4_row_1_0_5 : (left0Middle7 2 4) ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8)) = (rowColumnMul HexagonRowColumn724.rows_outerABC HexagonRowColumn724.cols_assocABC) ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem left0Middle7_eq_case_2_4_row_1_0_6 : (left0Middle7 2 4) ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8)) = (rowColumnMul HexagonRowColumn724.rows_outerABC HexagonRowColumn724.cols_assocABC) ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem left0Middle7_eq_case_2_4_row_1_0_7 : (left0Middle7 2 4) ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8)) = (rowColumnMul HexagonRowColumn724.rows_outerABC HexagonRowColumn724.cols_assocABC) ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem left0Middle7_eq_case_2_4_checked : left0Middle7 2 4 = rowColumnMul HexagonRowColumn724.rows_outerABC HexagonRowColumn724.cols_assocABC := by
  funext r
  fin_cases r
  · exact left0Middle7_eq_case_2_4_row_0_0_0
  · exact left0Middle7_eq_case_2_4_row_0_0_1
  · exact left0Middle7_eq_case_2_4_row_0_0_2
  · exact left0Middle7_eq_case_2_4_row_0_0_3
  · exact left0Middle7_eq_case_2_4_row_0_0_4
  · exact left0Middle7_eq_case_2_4_row_0_0_5
  · exact left0Middle7_eq_case_2_4_row_0_0_6
  · exact left0Middle7_eq_case_2_4_row_0_0_7
  · exact left0Middle7_eq_case_2_4_row_1_0_0
  · exact left0Middle7_eq_case_2_4_row_1_0_1
  · exact left0Middle7_eq_case_2_4_row_1_0_2
  · exact left0Middle7_eq_case_2_4_row_1_0_3
  · exact left0Middle7_eq_case_2_4_row_1_0_4
  · exact left0Middle7_eq_case_2_4_row_1_0_5
  · exact left0Middle7_eq_case_2_4_row_1_0_6
  · exact left0Middle7_eq_case_2_4_row_1_0_7

set_option backward.isDefEq.respectTransparency false in
theorem left0Middle7_eq_case_2_4 : left0Middle7 2 4 = outerRightZ 7 2 4 * associatorZ 7 2 4 := by
  simpa only [HexagonAtoms724.assocABC_eq,
    HexagonAtoms724.outerABC_eq,
    HexagonAtoms724.assocBAC_eq,
    HexagonAtoms724.innerABC_eq,
    HexagonAtoms724.innerRightABC_eq,
    HexagonAtoms724.inverseACB_eq,
    HexagonAtoms724.innerACB_eq,
    HexagonAtoms724.assocBCA_eq,
    HexagonAtoms724.innerRightBAC_eq,
    HexagonAtoms724.assocCAB_eq,
    HexagonAtoms724.outerLeftABC_eq,
    HexagonRowColumn724.product0_eq,
    HexagonRowColumn724.product1_eq,
    HexagonRowColumn724.product2_eq,
    HexagonRowColumn724.product3_eq,
    HexagonRowColumn724.product4_eq,
    HexagonRowColumn724.product5_eq,
    HexagonRowColumn724.product6_eq,
    HexagonRowColumn724.product7_eq] using left0Middle7_eq_case_2_4_checked

private theorem left1Middle7_eq_case_2_4_row_0_0_0 : (left1Middle7 2 4) ((0 : Fin 1), (0 : Fin 2), (0 : Fin 8)) = (HexagonAtoms724.assocBAC) ((0 : Fin 1), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem left1Middle7_eq_case_2_4_row_0_0_1 : (left1Middle7 2 4) ((0 : Fin 1), (0 : Fin 2), (1 : Fin 8)) = (HexagonAtoms724.assocBAC) ((0 : Fin 1), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem left1Middle7_eq_case_2_4_row_0_0_2 : (left1Middle7 2 4) ((0 : Fin 1), (0 : Fin 2), (2 : Fin 8)) = (HexagonAtoms724.assocBAC) ((0 : Fin 1), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem left1Middle7_eq_case_2_4_row_0_0_3 : (left1Middle7 2 4) ((0 : Fin 1), (0 : Fin 2), (3 : Fin 8)) = (HexagonAtoms724.assocBAC) ((0 : Fin 1), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem left1Middle7_eq_case_2_4_row_0_0_4 : (left1Middle7 2 4) ((0 : Fin 1), (0 : Fin 2), (4 : Fin 8)) = (HexagonAtoms724.assocBAC) ((0 : Fin 1), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem left1Middle7_eq_case_2_4_row_0_0_5 : (left1Middle7 2 4) ((0 : Fin 1), (0 : Fin 2), (5 : Fin 8)) = (HexagonAtoms724.assocBAC) ((0 : Fin 1), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem left1Middle7_eq_case_2_4_row_0_0_6 : (left1Middle7 2 4) ((0 : Fin 1), (0 : Fin 2), (6 : Fin 8)) = (HexagonAtoms724.assocBAC) ((0 : Fin 1), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem left1Middle7_eq_case_2_4_row_0_0_7 : (left1Middle7 2 4) ((0 : Fin 1), (0 : Fin 2), (7 : Fin 8)) = (HexagonAtoms724.assocBAC) ((0 : Fin 1), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem left1Middle7_eq_case_2_4_row_0_1_0 : (left1Middle7 2 4) ((0 : Fin 1), (1 : Fin 2), (0 : Fin 8)) = (HexagonAtoms724.assocBAC) ((0 : Fin 1), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem left1Middle7_eq_case_2_4_row_0_1_1 : (left1Middle7 2 4) ((0 : Fin 1), (1 : Fin 2), (1 : Fin 8)) = (HexagonAtoms724.assocBAC) ((0 : Fin 1), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem left1Middle7_eq_case_2_4_row_0_1_2 : (left1Middle7 2 4) ((0 : Fin 1), (1 : Fin 2), (2 : Fin 8)) = (HexagonAtoms724.assocBAC) ((0 : Fin 1), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem left1Middle7_eq_case_2_4_row_0_1_3 : (left1Middle7 2 4) ((0 : Fin 1), (1 : Fin 2), (3 : Fin 8)) = (HexagonAtoms724.assocBAC) ((0 : Fin 1), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem left1Middle7_eq_case_2_4_row_0_1_4 : (left1Middle7 2 4) ((0 : Fin 1), (1 : Fin 2), (4 : Fin 8)) = (HexagonAtoms724.assocBAC) ((0 : Fin 1), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem left1Middle7_eq_case_2_4_row_0_1_5 : (left1Middle7 2 4) ((0 : Fin 1), (1 : Fin 2), (5 : Fin 8)) = (HexagonAtoms724.assocBAC) ((0 : Fin 1), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem left1Middle7_eq_case_2_4_row_0_1_6 : (left1Middle7 2 4) ((0 : Fin 1), (1 : Fin 2), (6 : Fin 8)) = (HexagonAtoms724.assocBAC) ((0 : Fin 1), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem left1Middle7_eq_case_2_4_row_0_1_7 : (left1Middle7 2 4) ((0 : Fin 1), (1 : Fin 2), (7 : Fin 8)) = (HexagonAtoms724.assocBAC) ((0 : Fin 1), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem left1Middle7_eq_case_2_4_checked : left1Middle7 2 4 = HexagonAtoms724.assocBAC := by
  funext r
  fin_cases r
  · exact left1Middle7_eq_case_2_4_row_0_0_0
  · exact left1Middle7_eq_case_2_4_row_0_0_1
  · exact left1Middle7_eq_case_2_4_row_0_0_2
  · exact left1Middle7_eq_case_2_4_row_0_0_3
  · exact left1Middle7_eq_case_2_4_row_0_0_4
  · exact left1Middle7_eq_case_2_4_row_0_0_5
  · exact left1Middle7_eq_case_2_4_row_0_0_6
  · exact left1Middle7_eq_case_2_4_row_0_0_7
  · exact left1Middle7_eq_case_2_4_row_0_1_0
  · exact left1Middle7_eq_case_2_4_row_0_1_1
  · exact left1Middle7_eq_case_2_4_row_0_1_2
  · exact left1Middle7_eq_case_2_4_row_0_1_3
  · exact left1Middle7_eq_case_2_4_row_0_1_4
  · exact left1Middle7_eq_case_2_4_row_0_1_5
  · exact left1Middle7_eq_case_2_4_row_0_1_6
  · exact left1Middle7_eq_case_2_4_row_0_1_7

set_option backward.isDefEq.respectTransparency false in
theorem left1Middle7_eq_case_2_4 : left1Middle7 2 4 = associatorZ 2 7 4 * innerLeftZ 7 2 4 := by
  simpa only [HexagonAtoms724.assocABC_eq,
    HexagonAtoms724.outerABC_eq,
    HexagonAtoms724.assocBAC_eq,
    HexagonAtoms724.innerABC_eq,
    HexagonAtoms724.innerRightABC_eq,
    HexagonAtoms724.inverseACB_eq,
    HexagonAtoms724.innerACB_eq,
    HexagonAtoms724.assocBCA_eq,
    HexagonAtoms724.innerRightBAC_eq,
    HexagonAtoms724.assocCAB_eq,
    HexagonAtoms724.outerLeftABC_eq,
    HexagonRowColumn724.product0_eq,
    HexagonRowColumn724.product1_eq,
    HexagonRowColumn724.product2_eq,
    HexagonRowColumn724.product3_eq,
    HexagonRowColumn724.product4_eq,
    HexagonRowColumn724.product5_eq,
    HexagonRowColumn724.product6_eq,
    HexagonRowColumn724.product7_eq] using left1Middle7_eq_case_2_4_checked

private theorem right0Middle7_eq_case_2_4_row_0_0_0 : (right0Middle7 2 4) ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8)) = (HexagonAtoms724.assocABC) ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right0Middle7_eq_case_2_4_row_0_0_1 : (right0Middle7 2 4) ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8)) = (HexagonAtoms724.assocABC) ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right0Middle7_eq_case_2_4_row_0_0_2 : (right0Middle7 2 4) ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8)) = (HexagonAtoms724.assocABC) ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right0Middle7_eq_case_2_4_row_0_0_3 : (right0Middle7 2 4) ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8)) = (HexagonAtoms724.assocABC) ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right0Middle7_eq_case_2_4_row_0_0_4 : (right0Middle7 2 4) ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8)) = (HexagonAtoms724.assocABC) ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right0Middle7_eq_case_2_4_row_0_0_5 : (right0Middle7 2 4) ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8)) = (HexagonAtoms724.assocABC) ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right0Middle7_eq_case_2_4_row_0_0_6 : (right0Middle7 2 4) ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8)) = (HexagonAtoms724.assocABC) ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right0Middle7_eq_case_2_4_row_0_0_7 : (right0Middle7 2 4) ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8)) = (HexagonAtoms724.assocABC) ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right0Middle7_eq_case_2_4_row_1_0_0 : (right0Middle7 2 4) ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8)) = (HexagonAtoms724.assocABC) ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right0Middle7_eq_case_2_4_row_1_0_1 : (right0Middle7 2 4) ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8)) = (HexagonAtoms724.assocABC) ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right0Middle7_eq_case_2_4_row_1_0_2 : (right0Middle7 2 4) ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8)) = (HexagonAtoms724.assocABC) ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right0Middle7_eq_case_2_4_row_1_0_3 : (right0Middle7 2 4) ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8)) = (HexagonAtoms724.assocABC) ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right0Middle7_eq_case_2_4_row_1_0_4 : (right0Middle7 2 4) ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8)) = (HexagonAtoms724.assocABC) ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right0Middle7_eq_case_2_4_row_1_0_5 : (right0Middle7 2 4) ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8)) = (HexagonAtoms724.assocABC) ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right0Middle7_eq_case_2_4_row_1_0_6 : (right0Middle7 2 4) ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8)) = (HexagonAtoms724.assocABC) ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right0Middle7_eq_case_2_4_row_1_0_7 : (right0Middle7 2 4) ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8)) = (HexagonAtoms724.assocABC) ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right0Middle7_eq_case_2_4_checked : right0Middle7 2 4 = HexagonAtoms724.assocABC := by
  funext r
  fin_cases r
  · exact right0Middle7_eq_case_2_4_row_0_0_0
  · exact right0Middle7_eq_case_2_4_row_0_0_1
  · exact right0Middle7_eq_case_2_4_row_0_0_2
  · exact right0Middle7_eq_case_2_4_row_0_0_3
  · exact right0Middle7_eq_case_2_4_row_0_0_4
  · exact right0Middle7_eq_case_2_4_row_0_0_5
  · exact right0Middle7_eq_case_2_4_row_0_0_6
  · exact right0Middle7_eq_case_2_4_row_0_0_7
  · exact right0Middle7_eq_case_2_4_row_1_0_0
  · exact right0Middle7_eq_case_2_4_row_1_0_1
  · exact right0Middle7_eq_case_2_4_row_1_0_2
  · exact right0Middle7_eq_case_2_4_row_1_0_3
  · exact right0Middle7_eq_case_2_4_row_1_0_4
  · exact right0Middle7_eq_case_2_4_row_1_0_5
  · exact right0Middle7_eq_case_2_4_row_1_0_6
  · exact right0Middle7_eq_case_2_4_row_1_0_7

set_option backward.isDefEq.respectTransparency false in
theorem right0Middle7_eq_case_2_4 : right0Middle7 2 4 = innerRightZ 7 2 4 * associatorZ 7 2 4 := by
  simpa only [HexagonAtoms724.assocABC_eq,
    HexagonAtoms724.outerABC_eq,
    HexagonAtoms724.assocBAC_eq,
    HexagonAtoms724.innerABC_eq,
    HexagonAtoms724.innerRightABC_eq,
    HexagonAtoms724.inverseACB_eq,
    HexagonAtoms724.innerACB_eq,
    HexagonAtoms724.assocBCA_eq,
    HexagonAtoms724.innerRightBAC_eq,
    HexagonAtoms724.assocCAB_eq,
    HexagonAtoms724.outerLeftABC_eq,
    HexagonRowColumn724.product0_eq,
    HexagonRowColumn724.product1_eq,
    HexagonRowColumn724.product2_eq,
    HexagonRowColumn724.product3_eq,
    HexagonRowColumn724.product4_eq,
    HexagonRowColumn724.product5_eq,
    HexagonRowColumn724.product6_eq,
    HexagonRowColumn724.product7_eq] using right0Middle7_eq_case_2_4_checked

private theorem right1Middle7_eq_case_2_4_row_0_0_0 : (right1Middle7 2 4) ((0 : Fin 1), (0 : Fin 2), (0 : Fin 8)) = (rowColumnMul HexagonRowColumn724.rows_inverseACB HexagonRowColumn724.cols_right0) ((0 : Fin 1), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right1Middle7_eq_case_2_4_row_0_0_1 : (right1Middle7 2 4) ((0 : Fin 1), (0 : Fin 2), (1 : Fin 8)) = (rowColumnMul HexagonRowColumn724.rows_inverseACB HexagonRowColumn724.cols_right0) ((0 : Fin 1), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right1Middle7_eq_case_2_4_row_0_0_2 : (right1Middle7 2 4) ((0 : Fin 1), (0 : Fin 2), (2 : Fin 8)) = (rowColumnMul HexagonRowColumn724.rows_inverseACB HexagonRowColumn724.cols_right0) ((0 : Fin 1), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right1Middle7_eq_case_2_4_row_0_0_3 : (right1Middle7 2 4) ((0 : Fin 1), (0 : Fin 2), (3 : Fin 8)) = (rowColumnMul HexagonRowColumn724.rows_inverseACB HexagonRowColumn724.cols_right0) ((0 : Fin 1), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right1Middle7_eq_case_2_4_row_0_0_4 : (right1Middle7 2 4) ((0 : Fin 1), (0 : Fin 2), (4 : Fin 8)) = (rowColumnMul HexagonRowColumn724.rows_inverseACB HexagonRowColumn724.cols_right0) ((0 : Fin 1), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right1Middle7_eq_case_2_4_row_0_0_5 : (right1Middle7 2 4) ((0 : Fin 1), (0 : Fin 2), (5 : Fin 8)) = (rowColumnMul HexagonRowColumn724.rows_inverseACB HexagonRowColumn724.cols_right0) ((0 : Fin 1), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right1Middle7_eq_case_2_4_row_0_0_6 : (right1Middle7 2 4) ((0 : Fin 1), (0 : Fin 2), (6 : Fin 8)) = (rowColumnMul HexagonRowColumn724.rows_inverseACB HexagonRowColumn724.cols_right0) ((0 : Fin 1), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right1Middle7_eq_case_2_4_row_0_0_7 : (right1Middle7 2 4) ((0 : Fin 1), (0 : Fin 2), (7 : Fin 8)) = (rowColumnMul HexagonRowColumn724.rows_inverseACB HexagonRowColumn724.cols_right0) ((0 : Fin 1), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right1Middle7_eq_case_2_4_row_0_1_0 : (right1Middle7 2 4) ((0 : Fin 1), (1 : Fin 2), (0 : Fin 8)) = (rowColumnMul HexagonRowColumn724.rows_inverseACB HexagonRowColumn724.cols_right0) ((0 : Fin 1), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right1Middle7_eq_case_2_4_row_0_1_1 : (right1Middle7 2 4) ((0 : Fin 1), (1 : Fin 2), (1 : Fin 8)) = (rowColumnMul HexagonRowColumn724.rows_inverseACB HexagonRowColumn724.cols_right0) ((0 : Fin 1), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right1Middle7_eq_case_2_4_row_0_1_2 : (right1Middle7 2 4) ((0 : Fin 1), (1 : Fin 2), (2 : Fin 8)) = (rowColumnMul HexagonRowColumn724.rows_inverseACB HexagonRowColumn724.cols_right0) ((0 : Fin 1), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right1Middle7_eq_case_2_4_row_0_1_3 : (right1Middle7 2 4) ((0 : Fin 1), (1 : Fin 2), (3 : Fin 8)) = (rowColumnMul HexagonRowColumn724.rows_inverseACB HexagonRowColumn724.cols_right0) ((0 : Fin 1), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right1Middle7_eq_case_2_4_row_0_1_4 : (right1Middle7 2 4) ((0 : Fin 1), (1 : Fin 2), (4 : Fin 8)) = (rowColumnMul HexagonRowColumn724.rows_inverseACB HexagonRowColumn724.cols_right0) ((0 : Fin 1), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right1Middle7_eq_case_2_4_row_0_1_5 : (right1Middle7 2 4) ((0 : Fin 1), (1 : Fin 2), (5 : Fin 8)) = (rowColumnMul HexagonRowColumn724.rows_inverseACB HexagonRowColumn724.cols_right0) ((0 : Fin 1), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right1Middle7_eq_case_2_4_row_0_1_6 : (right1Middle7 2 4) ((0 : Fin 1), (1 : Fin 2), (6 : Fin 8)) = (rowColumnMul HexagonRowColumn724.rows_inverseACB HexagonRowColumn724.cols_right0) ((0 : Fin 1), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right1Middle7_eq_case_2_4_row_0_1_7 : (right1Middle7 2 4) ((0 : Fin 1), (1 : Fin 2), (7 : Fin 8)) = (rowColumnMul HexagonRowColumn724.rows_inverseACB HexagonRowColumn724.cols_right0) ((0 : Fin 1), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right1Middle7_eq_case_2_4_checked : right1Middle7 2 4 = rowColumnMul HexagonRowColumn724.rows_inverseACB HexagonRowColumn724.cols_right0 := by
  funext r
  fin_cases r
  · exact right1Middle7_eq_case_2_4_row_0_0_0
  · exact right1Middle7_eq_case_2_4_row_0_0_1
  · exact right1Middle7_eq_case_2_4_row_0_0_2
  · exact right1Middle7_eq_case_2_4_row_0_0_3
  · exact right1Middle7_eq_case_2_4_row_0_0_4
  · exact right1Middle7_eq_case_2_4_row_0_0_5
  · exact right1Middle7_eq_case_2_4_row_0_0_6
  · exact right1Middle7_eq_case_2_4_row_0_0_7
  · exact right1Middle7_eq_case_2_4_row_0_1_0
  · exact right1Middle7_eq_case_2_4_row_0_1_1
  · exact right1Middle7_eq_case_2_4_row_0_1_2
  · exact right1Middle7_eq_case_2_4_row_0_1_3
  · exact right1Middle7_eq_case_2_4_row_0_1_4
  · exact right1Middle7_eq_case_2_4_row_0_1_5
  · exact right1Middle7_eq_case_2_4_row_0_1_6
  · exact right1Middle7_eq_case_2_4_row_0_1_7

set_option backward.isDefEq.respectTransparency false in
theorem right1Middle7_eq_case_2_4 : right1Middle7 2 4 = associatorInverseZ 7 4 2 * right0Middle7 2 4 := by
  simpa only [HexagonAtoms724.assocABC_eq,
    HexagonAtoms724.outerABC_eq,
    HexagonAtoms724.assocBAC_eq,
    HexagonAtoms724.innerABC_eq,
    HexagonAtoms724.innerRightABC_eq,
    HexagonAtoms724.inverseACB_eq,
    HexagonAtoms724.innerACB_eq,
    HexagonAtoms724.assocBCA_eq,
    HexagonAtoms724.innerRightBAC_eq,
    HexagonAtoms724.assocCAB_eq,
    HexagonAtoms724.outerLeftABC_eq,
    HexagonRowColumn724.product0_eq,
    HexagonRowColumn724.product1_eq,
    HexagonRowColumn724.product2_eq,
    HexagonRowColumn724.product3_eq,
    HexagonRowColumn724.product4_eq,
    HexagonRowColumn724.product5_eq,
    HexagonRowColumn724.product6_eq,
    HexagonRowColumn724.product7_eq] using right1Middle7_eq_case_2_4_checked

private theorem right2Middle7_eq_case_2_4_row_0_0_0 : (right2Middle7 2 4) ((0 : Fin 1), (0 : Fin 2), (0 : Fin 8)) = (right1Middle7 2 4) ((0 : Fin 1), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right2Middle7_eq_case_2_4_row_0_0_1 : (right2Middle7 2 4) ((0 : Fin 1), (0 : Fin 2), (1 : Fin 8)) = (right1Middle7 2 4) ((0 : Fin 1), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right2Middle7_eq_case_2_4_row_0_0_2 : (right2Middle7 2 4) ((0 : Fin 1), (0 : Fin 2), (2 : Fin 8)) = (right1Middle7 2 4) ((0 : Fin 1), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right2Middle7_eq_case_2_4_row_0_0_3 : (right2Middle7 2 4) ((0 : Fin 1), (0 : Fin 2), (3 : Fin 8)) = (right1Middle7 2 4) ((0 : Fin 1), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right2Middle7_eq_case_2_4_row_0_0_4 : (right2Middle7 2 4) ((0 : Fin 1), (0 : Fin 2), (4 : Fin 8)) = (right1Middle7 2 4) ((0 : Fin 1), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right2Middle7_eq_case_2_4_row_0_0_5 : (right2Middle7 2 4) ((0 : Fin 1), (0 : Fin 2), (5 : Fin 8)) = (right1Middle7 2 4) ((0 : Fin 1), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right2Middle7_eq_case_2_4_row_0_0_6 : (right2Middle7 2 4) ((0 : Fin 1), (0 : Fin 2), (6 : Fin 8)) = (right1Middle7 2 4) ((0 : Fin 1), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right2Middle7_eq_case_2_4_row_0_0_7 : (right2Middle7 2 4) ((0 : Fin 1), (0 : Fin 2), (7 : Fin 8)) = (right1Middle7 2 4) ((0 : Fin 1), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right2Middle7_eq_case_2_4_row_0_1_0 : (right2Middle7 2 4) ((0 : Fin 1), (1 : Fin 2), (0 : Fin 8)) = (right1Middle7 2 4) ((0 : Fin 1), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right2Middle7_eq_case_2_4_row_0_1_1 : (right2Middle7 2 4) ((0 : Fin 1), (1 : Fin 2), (1 : Fin 8)) = (right1Middle7 2 4) ((0 : Fin 1), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right2Middle7_eq_case_2_4_row_0_1_2 : (right2Middle7 2 4) ((0 : Fin 1), (1 : Fin 2), (2 : Fin 8)) = (right1Middle7 2 4) ((0 : Fin 1), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right2Middle7_eq_case_2_4_row_0_1_3 : (right2Middle7 2 4) ((0 : Fin 1), (1 : Fin 2), (3 : Fin 8)) = (right1Middle7 2 4) ((0 : Fin 1), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right2Middle7_eq_case_2_4_row_0_1_4 : (right2Middle7 2 4) ((0 : Fin 1), (1 : Fin 2), (4 : Fin 8)) = (right1Middle7 2 4) ((0 : Fin 1), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right2Middle7_eq_case_2_4_row_0_1_5 : (right2Middle7 2 4) ((0 : Fin 1), (1 : Fin 2), (5 : Fin 8)) = (right1Middle7 2 4) ((0 : Fin 1), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right2Middle7_eq_case_2_4_row_0_1_6 : (right2Middle7 2 4) ((0 : Fin 1), (1 : Fin 2), (6 : Fin 8)) = (right1Middle7 2 4) ((0 : Fin 1), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right2Middle7_eq_case_2_4_row_0_1_7 : (right2Middle7 2 4) ((0 : Fin 1), (1 : Fin 2), (7 : Fin 8)) = (right1Middle7 2 4) ((0 : Fin 1), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem right2Middle7_eq_case_2_4_checked : right2Middle7 2 4 = right1Middle7 2 4 := by
  funext r
  fin_cases r
  · exact right2Middle7_eq_case_2_4_row_0_0_0
  · exact right2Middle7_eq_case_2_4_row_0_0_1
  · exact right2Middle7_eq_case_2_4_row_0_0_2
  · exact right2Middle7_eq_case_2_4_row_0_0_3
  · exact right2Middle7_eq_case_2_4_row_0_0_4
  · exact right2Middle7_eq_case_2_4_row_0_0_5
  · exact right2Middle7_eq_case_2_4_row_0_0_6
  · exact right2Middle7_eq_case_2_4_row_0_0_7
  · exact right2Middle7_eq_case_2_4_row_0_1_0
  · exact right2Middle7_eq_case_2_4_row_0_1_1
  · exact right2Middle7_eq_case_2_4_row_0_1_2
  · exact right2Middle7_eq_case_2_4_row_0_1_3
  · exact right2Middle7_eq_case_2_4_row_0_1_4
  · exact right2Middle7_eq_case_2_4_row_0_1_5
  · exact right2Middle7_eq_case_2_4_row_0_1_6
  · exact right2Middle7_eq_case_2_4_row_0_1_7

set_option backward.isDefEq.respectTransparency false in
theorem right2Middle7_eq_case_2_4 : right2Middle7 2 4 = innerLeftZ 7 4 2 * right1Middle7 2 4 := by
  simpa only [HexagonAtoms724.assocABC_eq,
    HexagonAtoms724.outerABC_eq,
    HexagonAtoms724.assocBAC_eq,
    HexagonAtoms724.innerABC_eq,
    HexagonAtoms724.innerRightABC_eq,
    HexagonAtoms724.inverseACB_eq,
    HexagonAtoms724.innerACB_eq,
    HexagonAtoms724.assocBCA_eq,
    HexagonAtoms724.innerRightBAC_eq,
    HexagonAtoms724.assocCAB_eq,
    HexagonAtoms724.outerLeftABC_eq,
    HexagonRowColumn724.product0_eq,
    HexagonRowColumn724.product1_eq,
    HexagonRowColumn724.product2_eq,
    HexagonRowColumn724.product3_eq,
    HexagonRowColumn724.product4_eq,
    HexagonRowColumn724.product5_eq,
    HexagonRowColumn724.product6_eq,
    HexagonRowColumn724.product7_eq] using right2Middle7_eq_case_2_4_checked

private theorem leftFinal7_case_2_4_row_0_0_0 : (((-1 : ℤ) ^ (leftScaleBit 7 2 4).val * positiveScale (leftScaleExponent 7 2 4)) •
      (rowColumnMul HexagonRowColumn724.rows_assocBCA HexagonRowColumn724.cols_left0)) ((0 : Fin 1), (0 : Fin 2), (0 : Fin 8)) = (negativeScale (leftScaleExponent 7 2 4) • (left1Middle7 2 4)) ((0 : Fin 1), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem leftFinal7_case_2_4_row_0_0_1 : (((-1 : ℤ) ^ (leftScaleBit 7 2 4).val * positiveScale (leftScaleExponent 7 2 4)) •
      (rowColumnMul HexagonRowColumn724.rows_assocBCA HexagonRowColumn724.cols_left0)) ((0 : Fin 1), (0 : Fin 2), (1 : Fin 8)) = (negativeScale (leftScaleExponent 7 2 4) • (left1Middle7 2 4)) ((0 : Fin 1), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem leftFinal7_case_2_4_row_0_0_2 : (((-1 : ℤ) ^ (leftScaleBit 7 2 4).val * positiveScale (leftScaleExponent 7 2 4)) •
      (rowColumnMul HexagonRowColumn724.rows_assocBCA HexagonRowColumn724.cols_left0)) ((0 : Fin 1), (0 : Fin 2), (2 : Fin 8)) = (negativeScale (leftScaleExponent 7 2 4) • (left1Middle7 2 4)) ((0 : Fin 1), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem leftFinal7_case_2_4_row_0_0_3 : (((-1 : ℤ) ^ (leftScaleBit 7 2 4).val * positiveScale (leftScaleExponent 7 2 4)) •
      (rowColumnMul HexagonRowColumn724.rows_assocBCA HexagonRowColumn724.cols_left0)) ((0 : Fin 1), (0 : Fin 2), (3 : Fin 8)) = (negativeScale (leftScaleExponent 7 2 4) • (left1Middle7 2 4)) ((0 : Fin 1), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem leftFinal7_case_2_4_row_0_0_4 : (((-1 : ℤ) ^ (leftScaleBit 7 2 4).val * positiveScale (leftScaleExponent 7 2 4)) •
      (rowColumnMul HexagonRowColumn724.rows_assocBCA HexagonRowColumn724.cols_left0)) ((0 : Fin 1), (0 : Fin 2), (4 : Fin 8)) = (negativeScale (leftScaleExponent 7 2 4) • (left1Middle7 2 4)) ((0 : Fin 1), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem leftFinal7_case_2_4_row_0_0_5 : (((-1 : ℤ) ^ (leftScaleBit 7 2 4).val * positiveScale (leftScaleExponent 7 2 4)) •
      (rowColumnMul HexagonRowColumn724.rows_assocBCA HexagonRowColumn724.cols_left0)) ((0 : Fin 1), (0 : Fin 2), (5 : Fin 8)) = (negativeScale (leftScaleExponent 7 2 4) • (left1Middle7 2 4)) ((0 : Fin 1), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem leftFinal7_case_2_4_row_0_0_6 : (((-1 : ℤ) ^ (leftScaleBit 7 2 4).val * positiveScale (leftScaleExponent 7 2 4)) •
      (rowColumnMul HexagonRowColumn724.rows_assocBCA HexagonRowColumn724.cols_left0)) ((0 : Fin 1), (0 : Fin 2), (6 : Fin 8)) = (negativeScale (leftScaleExponent 7 2 4) • (left1Middle7 2 4)) ((0 : Fin 1), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem leftFinal7_case_2_4_row_0_0_7 : (((-1 : ℤ) ^ (leftScaleBit 7 2 4).val * positiveScale (leftScaleExponent 7 2 4)) •
      (rowColumnMul HexagonRowColumn724.rows_assocBCA HexagonRowColumn724.cols_left0)) ((0 : Fin 1), (0 : Fin 2), (7 : Fin 8)) = (negativeScale (leftScaleExponent 7 2 4) • (left1Middle7 2 4)) ((0 : Fin 1), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem leftFinal7_case_2_4_row_0_1_0 : (((-1 : ℤ) ^ (leftScaleBit 7 2 4).val * positiveScale (leftScaleExponent 7 2 4)) •
      (rowColumnMul HexagonRowColumn724.rows_assocBCA HexagonRowColumn724.cols_left0)) ((0 : Fin 1), (1 : Fin 2), (0 : Fin 8)) = (negativeScale (leftScaleExponent 7 2 4) • (left1Middle7 2 4)) ((0 : Fin 1), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem leftFinal7_case_2_4_row_0_1_1 : (((-1 : ℤ) ^ (leftScaleBit 7 2 4).val * positiveScale (leftScaleExponent 7 2 4)) •
      (rowColumnMul HexagonRowColumn724.rows_assocBCA HexagonRowColumn724.cols_left0)) ((0 : Fin 1), (1 : Fin 2), (1 : Fin 8)) = (negativeScale (leftScaleExponent 7 2 4) • (left1Middle7 2 4)) ((0 : Fin 1), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem leftFinal7_case_2_4_row_0_1_2 : (((-1 : ℤ) ^ (leftScaleBit 7 2 4).val * positiveScale (leftScaleExponent 7 2 4)) •
      (rowColumnMul HexagonRowColumn724.rows_assocBCA HexagonRowColumn724.cols_left0)) ((0 : Fin 1), (1 : Fin 2), (2 : Fin 8)) = (negativeScale (leftScaleExponent 7 2 4) • (left1Middle7 2 4)) ((0 : Fin 1), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem leftFinal7_case_2_4_row_0_1_3 : (((-1 : ℤ) ^ (leftScaleBit 7 2 4).val * positiveScale (leftScaleExponent 7 2 4)) •
      (rowColumnMul HexagonRowColumn724.rows_assocBCA HexagonRowColumn724.cols_left0)) ((0 : Fin 1), (1 : Fin 2), (3 : Fin 8)) = (negativeScale (leftScaleExponent 7 2 4) • (left1Middle7 2 4)) ((0 : Fin 1), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem leftFinal7_case_2_4_row_0_1_4 : (((-1 : ℤ) ^ (leftScaleBit 7 2 4).val * positiveScale (leftScaleExponent 7 2 4)) •
      (rowColumnMul HexagonRowColumn724.rows_assocBCA HexagonRowColumn724.cols_left0)) ((0 : Fin 1), (1 : Fin 2), (4 : Fin 8)) = (negativeScale (leftScaleExponent 7 2 4) • (left1Middle7 2 4)) ((0 : Fin 1), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem leftFinal7_case_2_4_row_0_1_5 : (((-1 : ℤ) ^ (leftScaleBit 7 2 4).val * positiveScale (leftScaleExponent 7 2 4)) •
      (rowColumnMul HexagonRowColumn724.rows_assocBCA HexagonRowColumn724.cols_left0)) ((0 : Fin 1), (1 : Fin 2), (5 : Fin 8)) = (negativeScale (leftScaleExponent 7 2 4) • (left1Middle7 2 4)) ((0 : Fin 1), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem leftFinal7_case_2_4_row_0_1_6 : (((-1 : ℤ) ^ (leftScaleBit 7 2 4).val * positiveScale (leftScaleExponent 7 2 4)) •
      (rowColumnMul HexagonRowColumn724.rows_assocBCA HexagonRowColumn724.cols_left0)) ((0 : Fin 1), (1 : Fin 2), (6 : Fin 8)) = (negativeScale (leftScaleExponent 7 2 4) • (left1Middle7 2 4)) ((0 : Fin 1), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem leftFinal7_case_2_4_row_0_1_7 : (((-1 : ℤ) ^ (leftScaleBit 7 2 4).val * positiveScale (leftScaleExponent 7 2 4)) •
      (rowColumnMul HexagonRowColumn724.rows_assocBCA HexagonRowColumn724.cols_left0)) ((0 : Fin 1), (1 : Fin 2), (7 : Fin 8)) = (negativeScale (leftScaleExponent 7 2 4) • (left1Middle7 2 4)) ((0 : Fin 1), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem leftFinal7_case_2_4_checked : ((-1 : ℤ) ^ (leftScaleBit 7 2 4).val * positiveScale (leftScaleExponent 7 2 4)) •
      (rowColumnMul HexagonRowColumn724.rows_assocBCA HexagonRowColumn724.cols_left0) = negativeScale (leftScaleExponent 7 2 4) • (left1Middle7 2 4) := by
  funext r
  fin_cases r
  · exact leftFinal7_case_2_4_row_0_0_0
  · exact leftFinal7_case_2_4_row_0_0_1
  · exact leftFinal7_case_2_4_row_0_0_2
  · exact leftFinal7_case_2_4_row_0_0_3
  · exact leftFinal7_case_2_4_row_0_0_4
  · exact leftFinal7_case_2_4_row_0_0_5
  · exact leftFinal7_case_2_4_row_0_0_6
  · exact leftFinal7_case_2_4_row_0_0_7
  · exact leftFinal7_case_2_4_row_0_1_0
  · exact leftFinal7_case_2_4_row_0_1_1
  · exact leftFinal7_case_2_4_row_0_1_2
  · exact leftFinal7_case_2_4_row_0_1_3
  · exact leftFinal7_case_2_4_row_0_1_4
  · exact leftFinal7_case_2_4_row_0_1_5
  · exact leftFinal7_case_2_4_row_0_1_6
  · exact leftFinal7_case_2_4_row_0_1_7

set_option backward.isDefEq.respectTransparency false in
theorem leftFinal7_case_2_4 : ((-1 : ℤ) ^ (leftScaleBit 7 2 4).val * positiveScale (leftScaleExponent 7 2 4)) •
      (associatorZ 2 4 7 * left0Middle7 2 4) = negativeScale (leftScaleExponent 7 2 4) • (innerRightZ 2 7 4 * left1Middle7 2 4) := by
  simpa only [HexagonAtoms724.assocABC_eq,
    HexagonAtoms724.outerABC_eq,
    HexagonAtoms724.assocBAC_eq,
    HexagonAtoms724.innerABC_eq,
    HexagonAtoms724.innerRightABC_eq,
    HexagonAtoms724.inverseACB_eq,
    HexagonAtoms724.innerACB_eq,
    HexagonAtoms724.assocBCA_eq,
    HexagonAtoms724.innerRightBAC_eq,
    HexagonAtoms724.assocCAB_eq,
    HexagonAtoms724.outerLeftABC_eq,
    HexagonRowColumn724.product0_eq,
    HexagonRowColumn724.product1_eq,
    HexagonRowColumn724.product2_eq,
    HexagonRowColumn724.product3_eq,
    HexagonRowColumn724.product4_eq,
    HexagonRowColumn724.product5_eq,
    HexagonRowColumn724.product6_eq,
    HexagonRowColumn724.product7_eq] using leftFinal7_case_2_4_checked

private theorem rightFinal7_case_2_4_row_0_0_0 : (((-1 : ℤ) ^ (rightScaleBit 7 2 4).val * positiveScale (rightScaleExponent 7 2 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 4 2 : ℤ)) • HexagonAtoms724.outerLeftABC) ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8)) = (negativeScale (rightScaleExponent 7 2 4) • (rowColumnMul HexagonRowColumn724.rows_assocCAB HexagonRowColumn724.cols_right2)) ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem rightFinal7_case_2_4_row_0_0_1 : (((-1 : ℤ) ^ (rightScaleBit 7 2 4).val * positiveScale (rightScaleExponent 7 2 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 4 2 : ℤ)) • HexagonAtoms724.outerLeftABC) ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8)) = (negativeScale (rightScaleExponent 7 2 4) • (rowColumnMul HexagonRowColumn724.rows_assocCAB HexagonRowColumn724.cols_right2)) ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem rightFinal7_case_2_4_row_0_0_2 : (((-1 : ℤ) ^ (rightScaleBit 7 2 4).val * positiveScale (rightScaleExponent 7 2 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 4 2 : ℤ)) • HexagonAtoms724.outerLeftABC) ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8)) = (negativeScale (rightScaleExponent 7 2 4) • (rowColumnMul HexagonRowColumn724.rows_assocCAB HexagonRowColumn724.cols_right2)) ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem rightFinal7_case_2_4_row_0_0_3 : (((-1 : ℤ) ^ (rightScaleBit 7 2 4).val * positiveScale (rightScaleExponent 7 2 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 4 2 : ℤ)) • HexagonAtoms724.outerLeftABC) ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8)) = (negativeScale (rightScaleExponent 7 2 4) • (rowColumnMul HexagonRowColumn724.rows_assocCAB HexagonRowColumn724.cols_right2)) ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem rightFinal7_case_2_4_row_0_0_4 : (((-1 : ℤ) ^ (rightScaleBit 7 2 4).val * positiveScale (rightScaleExponent 7 2 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 4 2 : ℤ)) • HexagonAtoms724.outerLeftABC) ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8)) = (negativeScale (rightScaleExponent 7 2 4) • (rowColumnMul HexagonRowColumn724.rows_assocCAB HexagonRowColumn724.cols_right2)) ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem rightFinal7_case_2_4_row_0_0_5 : (((-1 : ℤ) ^ (rightScaleBit 7 2 4).val * positiveScale (rightScaleExponent 7 2 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 4 2 : ℤ)) • HexagonAtoms724.outerLeftABC) ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8)) = (negativeScale (rightScaleExponent 7 2 4) • (rowColumnMul HexagonRowColumn724.rows_assocCAB HexagonRowColumn724.cols_right2)) ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem rightFinal7_case_2_4_row_0_0_6 : (((-1 : ℤ) ^ (rightScaleBit 7 2 4).val * positiveScale (rightScaleExponent 7 2 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 4 2 : ℤ)) • HexagonAtoms724.outerLeftABC) ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8)) = (negativeScale (rightScaleExponent 7 2 4) • (rowColumnMul HexagonRowColumn724.rows_assocCAB HexagonRowColumn724.cols_right2)) ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem rightFinal7_case_2_4_row_0_0_7 : (((-1 : ℤ) ^ (rightScaleBit 7 2 4).val * positiveScale (rightScaleExponent 7 2 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 4 2 : ℤ)) • HexagonAtoms724.outerLeftABC) ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8)) = (negativeScale (rightScaleExponent 7 2 4) • (rowColumnMul HexagonRowColumn724.rows_assocCAB HexagonRowColumn724.cols_right2)) ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem rightFinal7_case_2_4_row_1_0_0 : (((-1 : ℤ) ^ (rightScaleBit 7 2 4).val * positiveScale (rightScaleExponent 7 2 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 4 2 : ℤ)) • HexagonAtoms724.outerLeftABC) ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8)) = (negativeScale (rightScaleExponent 7 2 4) • (rowColumnMul HexagonRowColumn724.rows_assocCAB HexagonRowColumn724.cols_right2)) ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem rightFinal7_case_2_4_row_1_0_1 : (((-1 : ℤ) ^ (rightScaleBit 7 2 4).val * positiveScale (rightScaleExponent 7 2 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 4 2 : ℤ)) • HexagonAtoms724.outerLeftABC) ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8)) = (negativeScale (rightScaleExponent 7 2 4) • (rowColumnMul HexagonRowColumn724.rows_assocCAB HexagonRowColumn724.cols_right2)) ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem rightFinal7_case_2_4_row_1_0_2 : (((-1 : ℤ) ^ (rightScaleBit 7 2 4).val * positiveScale (rightScaleExponent 7 2 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 4 2 : ℤ)) • HexagonAtoms724.outerLeftABC) ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8)) = (negativeScale (rightScaleExponent 7 2 4) • (rowColumnMul HexagonRowColumn724.rows_assocCAB HexagonRowColumn724.cols_right2)) ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem rightFinal7_case_2_4_row_1_0_3 : (((-1 : ℤ) ^ (rightScaleBit 7 2 4).val * positiveScale (rightScaleExponent 7 2 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 4 2 : ℤ)) • HexagonAtoms724.outerLeftABC) ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8)) = (negativeScale (rightScaleExponent 7 2 4) • (rowColumnMul HexagonRowColumn724.rows_assocCAB HexagonRowColumn724.cols_right2)) ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem rightFinal7_case_2_4_row_1_0_4 : (((-1 : ℤ) ^ (rightScaleBit 7 2 4).val * positiveScale (rightScaleExponent 7 2 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 4 2 : ℤ)) • HexagonAtoms724.outerLeftABC) ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8)) = (negativeScale (rightScaleExponent 7 2 4) • (rowColumnMul HexagonRowColumn724.rows_assocCAB HexagonRowColumn724.cols_right2)) ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem rightFinal7_case_2_4_row_1_0_5 : (((-1 : ℤ) ^ (rightScaleBit 7 2 4).val * positiveScale (rightScaleExponent 7 2 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 4 2 : ℤ)) • HexagonAtoms724.outerLeftABC) ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8)) = (negativeScale (rightScaleExponent 7 2 4) • (rowColumnMul HexagonRowColumn724.rows_assocCAB HexagonRowColumn724.cols_right2)) ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem rightFinal7_case_2_4_row_1_0_6 : (((-1 : ℤ) ^ (rightScaleBit 7 2 4).val * positiveScale (rightScaleExponent 7 2 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 4 2 : ℤ)) • HexagonAtoms724.outerLeftABC) ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8)) = (negativeScale (rightScaleExponent 7 2 4) • (rowColumnMul HexagonRowColumn724.rows_assocCAB HexagonRowColumn724.cols_right2)) ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem rightFinal7_case_2_4_row_1_0_7 : (((-1 : ℤ) ^ (rightScaleBit 7 2 4).val * positiveScale (rightScaleExponent 7 2 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 4 2 : ℤ)) • HexagonAtoms724.outerLeftABC) ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8)) = (negativeScale (rightScaleExponent 7 2 4) • (rowColumnMul HexagonRowColumn724.rows_assocCAB HexagonRowColumn724.cols_right2)) ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 2) (b := 1) (c := 8)
  decide +kernel

private theorem rightFinal7_case_2_4_checked : ((-1 : ℤ) ^ (rightScaleBit 7 2 4).val * positiveScale (rightScaleExponent 7 2 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 4 2 : ℤ)) • HexagonAtoms724.outerLeftABC = negativeScale (rightScaleExponent 7 2 4) • (rowColumnMul HexagonRowColumn724.rows_assocCAB HexagonRowColumn724.cols_right2) := by
  funext r
  fin_cases r
  · exact rightFinal7_case_2_4_row_0_0_0
  · exact rightFinal7_case_2_4_row_0_0_1
  · exact rightFinal7_case_2_4_row_0_0_2
  · exact rightFinal7_case_2_4_row_0_0_3
  · exact rightFinal7_case_2_4_row_0_0_4
  · exact rightFinal7_case_2_4_row_0_0_5
  · exact rightFinal7_case_2_4_row_0_0_6
  · exact rightFinal7_case_2_4_row_0_0_7
  · exact rightFinal7_case_2_4_row_1_0_0
  · exact rightFinal7_case_2_4_row_1_0_1
  · exact rightFinal7_case_2_4_row_1_0_2
  · exact rightFinal7_case_2_4_row_1_0_3
  · exact rightFinal7_case_2_4_row_1_0_4
  · exact rightFinal7_case_2_4_row_1_0_5
  · exact rightFinal7_case_2_4_row_1_0_6
  · exact rightFinal7_case_2_4_row_1_0_7

set_option backward.isDefEq.respectTransparency false in
theorem rightFinal7_case_2_4 : ((-1 : ℤ) ^ (rightScaleBit 7 2 4).val * positiveScale (rightScaleExponent 7 2 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 4 2 : ℤ)) • outerLeftZ 7 2 4 = negativeScale (rightScaleExponent 7 2 4) • (associatorZ 4 7 2 * right2Middle7 2 4) := by
  simpa only [HexagonAtoms724.assocABC_eq,
    HexagonAtoms724.outerABC_eq,
    HexagonAtoms724.assocBAC_eq,
    HexagonAtoms724.innerABC_eq,
    HexagonAtoms724.innerRightABC_eq,
    HexagonAtoms724.inverseACB_eq,
    HexagonAtoms724.innerACB_eq,
    HexagonAtoms724.assocBCA_eq,
    HexagonAtoms724.innerRightBAC_eq,
    HexagonAtoms724.assocCAB_eq,
    HexagonAtoms724.outerLeftABC_eq,
    HexagonRowColumn724.product0_eq,
    HexagonRowColumn724.product1_eq,
    HexagonRowColumn724.product2_eq,
    HexagonRowColumn724.product3_eq,
    HexagonRowColumn724.product4_eq,
    HexagonRowColumn724.product5_eq,
    HexagonRowColumn724.product6_eq,
    HexagonRowColumn724.product7_eq] using rightFinal7_case_2_4_checked

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonCases7
