import RMod.BrundanEllis.StackingReferenceHexagonMiddle6
import RMod.BrundanEllis.StackingReferenceSparseMatrixCheck
import RMod.BrundanEllis.StackingReferenceHexagonAtoms615
import RMod.BrundanEllis.StackingReferenceHexagonRowColumn615

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

private theorem left0Middle6_eq_case_1_5_row_0_0_0 : (left0Middle6 1 5) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn615.rows_outerABC HexagonRowColumn615.cols_assocABC) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_1_5_row_0_0_1 : (left0Middle6 1 5) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn615.rows_outerABC HexagonRowColumn615.cols_assocABC) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_1_5_row_0_0_2 : (left0Middle6 1 5) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn615.rows_outerABC HexagonRowColumn615.cols_assocABC) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_1_5_row_0_0_3 : (left0Middle6 1 5) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn615.rows_outerABC HexagonRowColumn615.cols_assocABC) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_1_5_row_0_1_0 : (left0Middle6 1 5) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn615.rows_outerABC HexagonRowColumn615.cols_assocABC) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_1_5_row_0_1_1 : (left0Middle6 1 5) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn615.rows_outerABC HexagonRowColumn615.cols_assocABC) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_1_5_row_0_1_2 : (left0Middle6 1 5) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn615.rows_outerABC HexagonRowColumn615.cols_assocABC) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_1_5_row_0_1_3 : (left0Middle6 1 5) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn615.rows_outerABC HexagonRowColumn615.cols_assocABC) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_1_5_row_1_0_0 : (left0Middle6 1 5) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn615.rows_outerABC HexagonRowColumn615.cols_assocABC) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_1_5_row_1_0_1 : (left0Middle6 1 5) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn615.rows_outerABC HexagonRowColumn615.cols_assocABC) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_1_5_row_1_0_2 : (left0Middle6 1 5) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn615.rows_outerABC HexagonRowColumn615.cols_assocABC) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_1_5_row_1_0_3 : (left0Middle6 1 5) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn615.rows_outerABC HexagonRowColumn615.cols_assocABC) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_1_5_row_1_1_0 : (left0Middle6 1 5) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn615.rows_outerABC HexagonRowColumn615.cols_assocABC) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_1_5_row_1_1_1 : (left0Middle6 1 5) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn615.rows_outerABC HexagonRowColumn615.cols_assocABC) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_1_5_row_1_1_2 : (left0Middle6 1 5) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn615.rows_outerABC HexagonRowColumn615.cols_assocABC) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_1_5_row_1_1_3 : (left0Middle6 1 5) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn615.rows_outerABC HexagonRowColumn615.cols_assocABC) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_1_5_checked : left0Middle6 1 5 = rowColumnMul HexagonRowColumn615.rows_outerABC HexagonRowColumn615.cols_assocABC := by
  funext r
  fin_cases r
  · exact left0Middle6_eq_case_1_5_row_0_0_0
  · exact left0Middle6_eq_case_1_5_row_0_0_1
  · exact left0Middle6_eq_case_1_5_row_0_0_2
  · exact left0Middle6_eq_case_1_5_row_0_0_3
  · exact left0Middle6_eq_case_1_5_row_0_1_0
  · exact left0Middle6_eq_case_1_5_row_0_1_1
  · exact left0Middle6_eq_case_1_5_row_0_1_2
  · exact left0Middle6_eq_case_1_5_row_0_1_3
  · exact left0Middle6_eq_case_1_5_row_1_0_0
  · exact left0Middle6_eq_case_1_5_row_1_0_1
  · exact left0Middle6_eq_case_1_5_row_1_0_2
  · exact left0Middle6_eq_case_1_5_row_1_0_3
  · exact left0Middle6_eq_case_1_5_row_1_1_0
  · exact left0Middle6_eq_case_1_5_row_1_1_1
  · exact left0Middle6_eq_case_1_5_row_1_1_2
  · exact left0Middle6_eq_case_1_5_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem left0Middle6_eq_case_1_5 : left0Middle6 1 5 = outerRightZ 6 1 5 * associatorZ 6 1 5 := by
  simpa only [HexagonAtoms615.assocABC_eq,
    HexagonAtoms615.outerABC_eq,
    HexagonAtoms615.assocBAC_eq,
    HexagonAtoms615.innerABC_eq,
    HexagonAtoms615.innerRightABC_eq,
    HexagonAtoms615.inverseACB_eq,
    HexagonAtoms615.innerACB_eq,
    HexagonAtoms615.assocBCA_eq,
    HexagonAtoms615.innerRightBAC_eq,
    HexagonAtoms615.assocCAB_eq,
    HexagonAtoms615.outerLeftABC_eq,
    HexagonRowColumn615.product0_eq,
    HexagonRowColumn615.product1_eq,
    HexagonRowColumn615.product2_eq,
    HexagonRowColumn615.product3_eq,
    HexagonRowColumn615.product4_eq,
    HexagonRowColumn615.product5_eq,
    HexagonRowColumn615.product6_eq,
    HexagonRowColumn615.product7_eq] using left0Middle6_eq_case_1_5_checked

private theorem left1Middle6_eq_case_1_5_row_0_0_0 : (left1Middle6 1 5) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms615.assocBAC) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_1_5_row_0_0_1 : (left1Middle6 1 5) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms615.assocBAC) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_1_5_row_0_0_2 : (left1Middle6 1 5) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms615.assocBAC) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_1_5_row_0_0_3 : (left1Middle6 1 5) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms615.assocBAC) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_1_5_row_0_1_0 : (left1Middle6 1 5) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms615.assocBAC) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_1_5_row_0_1_1 : (left1Middle6 1 5) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms615.assocBAC) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_1_5_row_0_1_2 : (left1Middle6 1 5) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms615.assocBAC) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_1_5_row_0_1_3 : (left1Middle6 1 5) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms615.assocBAC) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_1_5_row_1_0_0 : (left1Middle6 1 5) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms615.assocBAC) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_1_5_row_1_0_1 : (left1Middle6 1 5) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms615.assocBAC) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_1_5_row_1_0_2 : (left1Middle6 1 5) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms615.assocBAC) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_1_5_row_1_0_3 : (left1Middle6 1 5) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms615.assocBAC) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_1_5_row_1_1_0 : (left1Middle6 1 5) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms615.assocBAC) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_1_5_row_1_1_1 : (left1Middle6 1 5) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms615.assocBAC) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_1_5_row_1_1_2 : (left1Middle6 1 5) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms615.assocBAC) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_1_5_row_1_1_3 : (left1Middle6 1 5) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms615.assocBAC) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_1_5_checked : left1Middle6 1 5 = HexagonAtoms615.assocBAC := by
  funext r
  fin_cases r
  · exact left1Middle6_eq_case_1_5_row_0_0_0
  · exact left1Middle6_eq_case_1_5_row_0_0_1
  · exact left1Middle6_eq_case_1_5_row_0_0_2
  · exact left1Middle6_eq_case_1_5_row_0_0_3
  · exact left1Middle6_eq_case_1_5_row_0_1_0
  · exact left1Middle6_eq_case_1_5_row_0_1_1
  · exact left1Middle6_eq_case_1_5_row_0_1_2
  · exact left1Middle6_eq_case_1_5_row_0_1_3
  · exact left1Middle6_eq_case_1_5_row_1_0_0
  · exact left1Middle6_eq_case_1_5_row_1_0_1
  · exact left1Middle6_eq_case_1_5_row_1_0_2
  · exact left1Middle6_eq_case_1_5_row_1_0_3
  · exact left1Middle6_eq_case_1_5_row_1_1_0
  · exact left1Middle6_eq_case_1_5_row_1_1_1
  · exact left1Middle6_eq_case_1_5_row_1_1_2
  · exact left1Middle6_eq_case_1_5_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem left1Middle6_eq_case_1_5 : left1Middle6 1 5 = associatorZ 1 6 5 * innerLeftZ 6 1 5 := by
  simpa only [HexagonAtoms615.assocABC_eq,
    HexagonAtoms615.outerABC_eq,
    HexagonAtoms615.assocBAC_eq,
    HexagonAtoms615.innerABC_eq,
    HexagonAtoms615.innerRightABC_eq,
    HexagonAtoms615.inverseACB_eq,
    HexagonAtoms615.innerACB_eq,
    HexagonAtoms615.assocBCA_eq,
    HexagonAtoms615.innerRightBAC_eq,
    HexagonAtoms615.assocCAB_eq,
    HexagonAtoms615.outerLeftABC_eq,
    HexagonRowColumn615.product0_eq,
    HexagonRowColumn615.product1_eq,
    HexagonRowColumn615.product2_eq,
    HexagonRowColumn615.product3_eq,
    HexagonRowColumn615.product4_eq,
    HexagonRowColumn615.product5_eq,
    HexagonRowColumn615.product6_eq,
    HexagonRowColumn615.product7_eq] using left1Middle6_eq_case_1_5_checked

private theorem right0Middle6_eq_case_1_5_row_0_0_0 : (right0Middle6 1 5) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms615.assocABC) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_1_5_row_0_0_1 : (right0Middle6 1 5) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms615.assocABC) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_1_5_row_0_0_2 : (right0Middle6 1 5) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms615.assocABC) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_1_5_row_0_0_3 : (right0Middle6 1 5) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms615.assocABC) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_1_5_row_0_1_0 : (right0Middle6 1 5) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms615.assocABC) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_1_5_row_0_1_1 : (right0Middle6 1 5) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms615.assocABC) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_1_5_row_0_1_2 : (right0Middle6 1 5) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms615.assocABC) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_1_5_row_0_1_3 : (right0Middle6 1 5) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms615.assocABC) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_1_5_row_1_0_0 : (right0Middle6 1 5) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms615.assocABC) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_1_5_row_1_0_1 : (right0Middle6 1 5) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms615.assocABC) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_1_5_row_1_0_2 : (right0Middle6 1 5) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms615.assocABC) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_1_5_row_1_0_3 : (right0Middle6 1 5) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms615.assocABC) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_1_5_row_1_1_0 : (right0Middle6 1 5) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms615.assocABC) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_1_5_row_1_1_1 : (right0Middle6 1 5) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms615.assocABC) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_1_5_row_1_1_2 : (right0Middle6 1 5) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms615.assocABC) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_1_5_row_1_1_3 : (right0Middle6 1 5) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms615.assocABC) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_1_5_checked : right0Middle6 1 5 = HexagonAtoms615.assocABC := by
  funext r
  fin_cases r
  · exact right0Middle6_eq_case_1_5_row_0_0_0
  · exact right0Middle6_eq_case_1_5_row_0_0_1
  · exact right0Middle6_eq_case_1_5_row_0_0_2
  · exact right0Middle6_eq_case_1_5_row_0_0_3
  · exact right0Middle6_eq_case_1_5_row_0_1_0
  · exact right0Middle6_eq_case_1_5_row_0_1_1
  · exact right0Middle6_eq_case_1_5_row_0_1_2
  · exact right0Middle6_eq_case_1_5_row_0_1_3
  · exact right0Middle6_eq_case_1_5_row_1_0_0
  · exact right0Middle6_eq_case_1_5_row_1_0_1
  · exact right0Middle6_eq_case_1_5_row_1_0_2
  · exact right0Middle6_eq_case_1_5_row_1_0_3
  · exact right0Middle6_eq_case_1_5_row_1_1_0
  · exact right0Middle6_eq_case_1_5_row_1_1_1
  · exact right0Middle6_eq_case_1_5_row_1_1_2
  · exact right0Middle6_eq_case_1_5_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem right0Middle6_eq_case_1_5 : right0Middle6 1 5 = innerRightZ 6 1 5 * associatorZ 6 1 5 := by
  simpa only [HexagonAtoms615.assocABC_eq,
    HexagonAtoms615.outerABC_eq,
    HexagonAtoms615.assocBAC_eq,
    HexagonAtoms615.innerABC_eq,
    HexagonAtoms615.innerRightABC_eq,
    HexagonAtoms615.inverseACB_eq,
    HexagonAtoms615.innerACB_eq,
    HexagonAtoms615.assocBCA_eq,
    HexagonAtoms615.innerRightBAC_eq,
    HexagonAtoms615.assocCAB_eq,
    HexagonAtoms615.outerLeftABC_eq,
    HexagonRowColumn615.product0_eq,
    HexagonRowColumn615.product1_eq,
    HexagonRowColumn615.product2_eq,
    HexagonRowColumn615.product3_eq,
    HexagonRowColumn615.product4_eq,
    HexagonRowColumn615.product5_eq,
    HexagonRowColumn615.product6_eq,
    HexagonRowColumn615.product7_eq] using right0Middle6_eq_case_1_5_checked

private theorem right1Middle6_eq_case_1_5_row_0_0_0 : (right1Middle6 1 5) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn615.rows_inverseACB HexagonRowColumn615.cols_right0) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_1_5_row_0_0_1 : (right1Middle6 1 5) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn615.rows_inverseACB HexagonRowColumn615.cols_right0) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_1_5_row_0_0_2 : (right1Middle6 1 5) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn615.rows_inverseACB HexagonRowColumn615.cols_right0) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_1_5_row_0_0_3 : (right1Middle6 1 5) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn615.rows_inverseACB HexagonRowColumn615.cols_right0) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_1_5_row_0_1_0 : (right1Middle6 1 5) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn615.rows_inverseACB HexagonRowColumn615.cols_right0) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_1_5_row_0_1_1 : (right1Middle6 1 5) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn615.rows_inverseACB HexagonRowColumn615.cols_right0) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_1_5_row_0_1_2 : (right1Middle6 1 5) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn615.rows_inverseACB HexagonRowColumn615.cols_right0) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_1_5_row_0_1_3 : (right1Middle6 1 5) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn615.rows_inverseACB HexagonRowColumn615.cols_right0) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_1_5_row_1_0_0 : (right1Middle6 1 5) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn615.rows_inverseACB HexagonRowColumn615.cols_right0) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_1_5_row_1_0_1 : (right1Middle6 1 5) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn615.rows_inverseACB HexagonRowColumn615.cols_right0) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_1_5_row_1_0_2 : (right1Middle6 1 5) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn615.rows_inverseACB HexagonRowColumn615.cols_right0) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_1_5_row_1_0_3 : (right1Middle6 1 5) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn615.rows_inverseACB HexagonRowColumn615.cols_right0) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_1_5_row_1_1_0 : (right1Middle6 1 5) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn615.rows_inverseACB HexagonRowColumn615.cols_right0) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_1_5_row_1_1_1 : (right1Middle6 1 5) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn615.rows_inverseACB HexagonRowColumn615.cols_right0) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_1_5_row_1_1_2 : (right1Middle6 1 5) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn615.rows_inverseACB HexagonRowColumn615.cols_right0) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_1_5_row_1_1_3 : (right1Middle6 1 5) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn615.rows_inverseACB HexagonRowColumn615.cols_right0) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_1_5_checked : right1Middle6 1 5 = rowColumnMul HexagonRowColumn615.rows_inverseACB HexagonRowColumn615.cols_right0 := by
  funext r
  fin_cases r
  · exact right1Middle6_eq_case_1_5_row_0_0_0
  · exact right1Middle6_eq_case_1_5_row_0_0_1
  · exact right1Middle6_eq_case_1_5_row_0_0_2
  · exact right1Middle6_eq_case_1_5_row_0_0_3
  · exact right1Middle6_eq_case_1_5_row_0_1_0
  · exact right1Middle6_eq_case_1_5_row_0_1_1
  · exact right1Middle6_eq_case_1_5_row_0_1_2
  · exact right1Middle6_eq_case_1_5_row_0_1_3
  · exact right1Middle6_eq_case_1_5_row_1_0_0
  · exact right1Middle6_eq_case_1_5_row_1_0_1
  · exact right1Middle6_eq_case_1_5_row_1_0_2
  · exact right1Middle6_eq_case_1_5_row_1_0_3
  · exact right1Middle6_eq_case_1_5_row_1_1_0
  · exact right1Middle6_eq_case_1_5_row_1_1_1
  · exact right1Middle6_eq_case_1_5_row_1_1_2
  · exact right1Middle6_eq_case_1_5_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem right1Middle6_eq_case_1_5 : right1Middle6 1 5 = associatorInverseZ 6 5 1 * right0Middle6 1 5 := by
  simpa only [HexagonAtoms615.assocABC_eq,
    HexagonAtoms615.outerABC_eq,
    HexagonAtoms615.assocBAC_eq,
    HexagonAtoms615.innerABC_eq,
    HexagonAtoms615.innerRightABC_eq,
    HexagonAtoms615.inverseACB_eq,
    HexagonAtoms615.innerACB_eq,
    HexagonAtoms615.assocBCA_eq,
    HexagonAtoms615.innerRightBAC_eq,
    HexagonAtoms615.assocCAB_eq,
    HexagonAtoms615.outerLeftABC_eq,
    HexagonRowColumn615.product0_eq,
    HexagonRowColumn615.product1_eq,
    HexagonRowColumn615.product2_eq,
    HexagonRowColumn615.product3_eq,
    HexagonRowColumn615.product4_eq,
    HexagonRowColumn615.product5_eq,
    HexagonRowColumn615.product6_eq,
    HexagonRowColumn615.product7_eq] using right1Middle6_eq_case_1_5_checked

private theorem right2Middle6_eq_case_1_5_row_0_0_0 : (right2Middle6 1 5) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (right1Middle6 1 5) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_1_5_row_0_0_1 : (right2Middle6 1 5) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (right1Middle6 1 5) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_1_5_row_0_0_2 : (right2Middle6 1 5) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (right1Middle6 1 5) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_1_5_row_0_0_3 : (right2Middle6 1 5) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (right1Middle6 1 5) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_1_5_row_0_1_0 : (right2Middle6 1 5) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (right1Middle6 1 5) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_1_5_row_0_1_1 : (right2Middle6 1 5) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (right1Middle6 1 5) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_1_5_row_0_1_2 : (right2Middle6 1 5) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (right1Middle6 1 5) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_1_5_row_0_1_3 : (right2Middle6 1 5) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (right1Middle6 1 5) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_1_5_row_1_0_0 : (right2Middle6 1 5) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (right1Middle6 1 5) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_1_5_row_1_0_1 : (right2Middle6 1 5) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (right1Middle6 1 5) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_1_5_row_1_0_2 : (right2Middle6 1 5) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (right1Middle6 1 5) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_1_5_row_1_0_3 : (right2Middle6 1 5) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (right1Middle6 1 5) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_1_5_row_1_1_0 : (right2Middle6 1 5) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (right1Middle6 1 5) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_1_5_row_1_1_1 : (right2Middle6 1 5) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (right1Middle6 1 5) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_1_5_row_1_1_2 : (right2Middle6 1 5) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (right1Middle6 1 5) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_1_5_row_1_1_3 : (right2Middle6 1 5) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (right1Middle6 1 5) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_1_5_checked : right2Middle6 1 5 = right1Middle6 1 5 := by
  funext r
  fin_cases r
  · exact right2Middle6_eq_case_1_5_row_0_0_0
  · exact right2Middle6_eq_case_1_5_row_0_0_1
  · exact right2Middle6_eq_case_1_5_row_0_0_2
  · exact right2Middle6_eq_case_1_5_row_0_0_3
  · exact right2Middle6_eq_case_1_5_row_0_1_0
  · exact right2Middle6_eq_case_1_5_row_0_1_1
  · exact right2Middle6_eq_case_1_5_row_0_1_2
  · exact right2Middle6_eq_case_1_5_row_0_1_3
  · exact right2Middle6_eq_case_1_5_row_1_0_0
  · exact right2Middle6_eq_case_1_5_row_1_0_1
  · exact right2Middle6_eq_case_1_5_row_1_0_2
  · exact right2Middle6_eq_case_1_5_row_1_0_3
  · exact right2Middle6_eq_case_1_5_row_1_1_0
  · exact right2Middle6_eq_case_1_5_row_1_1_1
  · exact right2Middle6_eq_case_1_5_row_1_1_2
  · exact right2Middle6_eq_case_1_5_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem right2Middle6_eq_case_1_5 : right2Middle6 1 5 = innerLeftZ 6 5 1 * right1Middle6 1 5 := by
  simpa only [HexagonAtoms615.assocABC_eq,
    HexagonAtoms615.outerABC_eq,
    HexagonAtoms615.assocBAC_eq,
    HexagonAtoms615.innerABC_eq,
    HexagonAtoms615.innerRightABC_eq,
    HexagonAtoms615.inverseACB_eq,
    HexagonAtoms615.innerACB_eq,
    HexagonAtoms615.assocBCA_eq,
    HexagonAtoms615.innerRightBAC_eq,
    HexagonAtoms615.assocCAB_eq,
    HexagonAtoms615.outerLeftABC_eq,
    HexagonRowColumn615.product0_eq,
    HexagonRowColumn615.product1_eq,
    HexagonRowColumn615.product2_eq,
    HexagonRowColumn615.product3_eq,
    HexagonRowColumn615.product4_eq,
    HexagonRowColumn615.product5_eq,
    HexagonRowColumn615.product6_eq,
    HexagonRowColumn615.product7_eq] using right2Middle6_eq_case_1_5_checked

private theorem leftFinal6_case_1_5_row_0_0_0 : (((-1 : ℤ) ^ (leftScaleBit 6 1 5).val * positiveScale (leftScaleExponent 6 1 5)) •
      (rowColumnMul HexagonRowColumn615.rows_assocBCA HexagonRowColumn615.cols_left0)) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 6 1 5) • (left1Middle6 1 5)) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal6_case_1_5_row_0_0_1 : (((-1 : ℤ) ^ (leftScaleBit 6 1 5).val * positiveScale (leftScaleExponent 6 1 5)) •
      (rowColumnMul HexagonRowColumn615.rows_assocBCA HexagonRowColumn615.cols_left0)) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 6 1 5) • (left1Middle6 1 5)) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal6_case_1_5_row_0_0_2 : (((-1 : ℤ) ^ (leftScaleBit 6 1 5).val * positiveScale (leftScaleExponent 6 1 5)) •
      (rowColumnMul HexagonRowColumn615.rows_assocBCA HexagonRowColumn615.cols_left0)) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 6 1 5) • (left1Middle6 1 5)) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal6_case_1_5_row_0_0_3 : (((-1 : ℤ) ^ (leftScaleBit 6 1 5).val * positiveScale (leftScaleExponent 6 1 5)) •
      (rowColumnMul HexagonRowColumn615.rows_assocBCA HexagonRowColumn615.cols_left0)) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 6 1 5) • (left1Middle6 1 5)) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal6_case_1_5_row_0_1_0 : (((-1 : ℤ) ^ (leftScaleBit 6 1 5).val * positiveScale (leftScaleExponent 6 1 5)) •
      (rowColumnMul HexagonRowColumn615.rows_assocBCA HexagonRowColumn615.cols_left0)) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 6 1 5) • (left1Middle6 1 5)) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal6_case_1_5_row_0_1_1 : (((-1 : ℤ) ^ (leftScaleBit 6 1 5).val * positiveScale (leftScaleExponent 6 1 5)) •
      (rowColumnMul HexagonRowColumn615.rows_assocBCA HexagonRowColumn615.cols_left0)) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 6 1 5) • (left1Middle6 1 5)) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal6_case_1_5_row_0_1_2 : (((-1 : ℤ) ^ (leftScaleBit 6 1 5).val * positiveScale (leftScaleExponent 6 1 5)) •
      (rowColumnMul HexagonRowColumn615.rows_assocBCA HexagonRowColumn615.cols_left0)) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 6 1 5) • (left1Middle6 1 5)) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal6_case_1_5_row_0_1_3 : (((-1 : ℤ) ^ (leftScaleBit 6 1 5).val * positiveScale (leftScaleExponent 6 1 5)) •
      (rowColumnMul HexagonRowColumn615.rows_assocBCA HexagonRowColumn615.cols_left0)) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 6 1 5) • (left1Middle6 1 5)) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal6_case_1_5_row_1_0_0 : (((-1 : ℤ) ^ (leftScaleBit 6 1 5).val * positiveScale (leftScaleExponent 6 1 5)) •
      (rowColumnMul HexagonRowColumn615.rows_assocBCA HexagonRowColumn615.cols_left0)) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 6 1 5) • (left1Middle6 1 5)) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal6_case_1_5_row_1_0_1 : (((-1 : ℤ) ^ (leftScaleBit 6 1 5).val * positiveScale (leftScaleExponent 6 1 5)) •
      (rowColumnMul HexagonRowColumn615.rows_assocBCA HexagonRowColumn615.cols_left0)) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 6 1 5) • (left1Middle6 1 5)) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal6_case_1_5_row_1_0_2 : (((-1 : ℤ) ^ (leftScaleBit 6 1 5).val * positiveScale (leftScaleExponent 6 1 5)) •
      (rowColumnMul HexagonRowColumn615.rows_assocBCA HexagonRowColumn615.cols_left0)) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 6 1 5) • (left1Middle6 1 5)) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal6_case_1_5_row_1_0_3 : (((-1 : ℤ) ^ (leftScaleBit 6 1 5).val * positiveScale (leftScaleExponent 6 1 5)) •
      (rowColumnMul HexagonRowColumn615.rows_assocBCA HexagonRowColumn615.cols_left0)) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 6 1 5) • (left1Middle6 1 5)) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal6_case_1_5_row_1_1_0 : (((-1 : ℤ) ^ (leftScaleBit 6 1 5).val * positiveScale (leftScaleExponent 6 1 5)) •
      (rowColumnMul HexagonRowColumn615.rows_assocBCA HexagonRowColumn615.cols_left0)) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 6 1 5) • (left1Middle6 1 5)) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal6_case_1_5_row_1_1_1 : (((-1 : ℤ) ^ (leftScaleBit 6 1 5).val * positiveScale (leftScaleExponent 6 1 5)) •
      (rowColumnMul HexagonRowColumn615.rows_assocBCA HexagonRowColumn615.cols_left0)) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 6 1 5) • (left1Middle6 1 5)) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal6_case_1_5_row_1_1_2 : (((-1 : ℤ) ^ (leftScaleBit 6 1 5).val * positiveScale (leftScaleExponent 6 1 5)) •
      (rowColumnMul HexagonRowColumn615.rows_assocBCA HexagonRowColumn615.cols_left0)) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 6 1 5) • (left1Middle6 1 5)) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal6_case_1_5_row_1_1_3 : (((-1 : ℤ) ^ (leftScaleBit 6 1 5).val * positiveScale (leftScaleExponent 6 1 5)) •
      (rowColumnMul HexagonRowColumn615.rows_assocBCA HexagonRowColumn615.cols_left0)) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 6 1 5) • (left1Middle6 1 5)) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal6_case_1_5_checked : ((-1 : ℤ) ^ (leftScaleBit 6 1 5).val * positiveScale (leftScaleExponent 6 1 5)) •
      (rowColumnMul HexagonRowColumn615.rows_assocBCA HexagonRowColumn615.cols_left0) = negativeScale (leftScaleExponent 6 1 5) • (left1Middle6 1 5) := by
  funext r
  fin_cases r
  · exact leftFinal6_case_1_5_row_0_0_0
  · exact leftFinal6_case_1_5_row_0_0_1
  · exact leftFinal6_case_1_5_row_0_0_2
  · exact leftFinal6_case_1_5_row_0_0_3
  · exact leftFinal6_case_1_5_row_0_1_0
  · exact leftFinal6_case_1_5_row_0_1_1
  · exact leftFinal6_case_1_5_row_0_1_2
  · exact leftFinal6_case_1_5_row_0_1_3
  · exact leftFinal6_case_1_5_row_1_0_0
  · exact leftFinal6_case_1_5_row_1_0_1
  · exact leftFinal6_case_1_5_row_1_0_2
  · exact leftFinal6_case_1_5_row_1_0_3
  · exact leftFinal6_case_1_5_row_1_1_0
  · exact leftFinal6_case_1_5_row_1_1_1
  · exact leftFinal6_case_1_5_row_1_1_2
  · exact leftFinal6_case_1_5_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem leftFinal6_case_1_5 : ((-1 : ℤ) ^ (leftScaleBit 6 1 5).val * positiveScale (leftScaleExponent 6 1 5)) •
      (associatorZ 1 5 6 * left0Middle6 1 5) = negativeScale (leftScaleExponent 6 1 5) • (innerRightZ 1 6 5 * left1Middle6 1 5) := by
  simpa only [HexagonAtoms615.assocABC_eq,
    HexagonAtoms615.outerABC_eq,
    HexagonAtoms615.assocBAC_eq,
    HexagonAtoms615.innerABC_eq,
    HexagonAtoms615.innerRightABC_eq,
    HexagonAtoms615.inverseACB_eq,
    HexagonAtoms615.innerACB_eq,
    HexagonAtoms615.assocBCA_eq,
    HexagonAtoms615.innerRightBAC_eq,
    HexagonAtoms615.assocCAB_eq,
    HexagonAtoms615.outerLeftABC_eq,
    HexagonRowColumn615.product0_eq,
    HexagonRowColumn615.product1_eq,
    HexagonRowColumn615.product2_eq,
    HexagonRowColumn615.product3_eq,
    HexagonRowColumn615.product4_eq,
    HexagonRowColumn615.product5_eq,
    HexagonRowColumn615.product6_eq,
    HexagonRowColumn615.product7_eq] using leftFinal6_case_1_5_checked

private theorem rightFinal6_case_1_5_row_0_0_0 : (((-1 : ℤ) ^ (rightScaleBit 6 1 5).val * positiveScale (rightScaleExponent 6 1 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 1 : ℤ)) • HexagonAtoms615.outerLeftABC) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 6 1 5) • (rowColumnMul HexagonRowColumn615.rows_assocCAB HexagonRowColumn615.cols_right2)) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal6_case_1_5_row_0_0_1 : (((-1 : ℤ) ^ (rightScaleBit 6 1 5).val * positiveScale (rightScaleExponent 6 1 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 1 : ℤ)) • HexagonAtoms615.outerLeftABC) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 6 1 5) • (rowColumnMul HexagonRowColumn615.rows_assocCAB HexagonRowColumn615.cols_right2)) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal6_case_1_5_row_0_0_2 : (((-1 : ℤ) ^ (rightScaleBit 6 1 5).val * positiveScale (rightScaleExponent 6 1 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 1 : ℤ)) • HexagonAtoms615.outerLeftABC) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 6 1 5) • (rowColumnMul HexagonRowColumn615.rows_assocCAB HexagonRowColumn615.cols_right2)) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal6_case_1_5_row_0_0_3 : (((-1 : ℤ) ^ (rightScaleBit 6 1 5).val * positiveScale (rightScaleExponent 6 1 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 1 : ℤ)) • HexagonAtoms615.outerLeftABC) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 6 1 5) • (rowColumnMul HexagonRowColumn615.rows_assocCAB HexagonRowColumn615.cols_right2)) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal6_case_1_5_row_0_1_0 : (((-1 : ℤ) ^ (rightScaleBit 6 1 5).val * positiveScale (rightScaleExponent 6 1 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 1 : ℤ)) • HexagonAtoms615.outerLeftABC) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 6 1 5) • (rowColumnMul HexagonRowColumn615.rows_assocCAB HexagonRowColumn615.cols_right2)) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal6_case_1_5_row_0_1_1 : (((-1 : ℤ) ^ (rightScaleBit 6 1 5).val * positiveScale (rightScaleExponent 6 1 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 1 : ℤ)) • HexagonAtoms615.outerLeftABC) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 6 1 5) • (rowColumnMul HexagonRowColumn615.rows_assocCAB HexagonRowColumn615.cols_right2)) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal6_case_1_5_row_0_1_2 : (((-1 : ℤ) ^ (rightScaleBit 6 1 5).val * positiveScale (rightScaleExponent 6 1 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 1 : ℤ)) • HexagonAtoms615.outerLeftABC) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 6 1 5) • (rowColumnMul HexagonRowColumn615.rows_assocCAB HexagonRowColumn615.cols_right2)) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal6_case_1_5_row_0_1_3 : (((-1 : ℤ) ^ (rightScaleBit 6 1 5).val * positiveScale (rightScaleExponent 6 1 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 1 : ℤ)) • HexagonAtoms615.outerLeftABC) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 6 1 5) • (rowColumnMul HexagonRowColumn615.rows_assocCAB HexagonRowColumn615.cols_right2)) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal6_case_1_5_row_1_0_0 : (((-1 : ℤ) ^ (rightScaleBit 6 1 5).val * positiveScale (rightScaleExponent 6 1 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 1 : ℤ)) • HexagonAtoms615.outerLeftABC) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 6 1 5) • (rowColumnMul HexagonRowColumn615.rows_assocCAB HexagonRowColumn615.cols_right2)) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal6_case_1_5_row_1_0_1 : (((-1 : ℤ) ^ (rightScaleBit 6 1 5).val * positiveScale (rightScaleExponent 6 1 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 1 : ℤ)) • HexagonAtoms615.outerLeftABC) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 6 1 5) • (rowColumnMul HexagonRowColumn615.rows_assocCAB HexagonRowColumn615.cols_right2)) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal6_case_1_5_row_1_0_2 : (((-1 : ℤ) ^ (rightScaleBit 6 1 5).val * positiveScale (rightScaleExponent 6 1 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 1 : ℤ)) • HexagonAtoms615.outerLeftABC) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 6 1 5) • (rowColumnMul HexagonRowColumn615.rows_assocCAB HexagonRowColumn615.cols_right2)) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal6_case_1_5_row_1_0_3 : (((-1 : ℤ) ^ (rightScaleBit 6 1 5).val * positiveScale (rightScaleExponent 6 1 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 1 : ℤ)) • HexagonAtoms615.outerLeftABC) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 6 1 5) • (rowColumnMul HexagonRowColumn615.rows_assocCAB HexagonRowColumn615.cols_right2)) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal6_case_1_5_row_1_1_0 : (((-1 : ℤ) ^ (rightScaleBit 6 1 5).val * positiveScale (rightScaleExponent 6 1 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 1 : ℤ)) • HexagonAtoms615.outerLeftABC) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 6 1 5) • (rowColumnMul HexagonRowColumn615.rows_assocCAB HexagonRowColumn615.cols_right2)) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal6_case_1_5_row_1_1_1 : (((-1 : ℤ) ^ (rightScaleBit 6 1 5).val * positiveScale (rightScaleExponent 6 1 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 1 : ℤ)) • HexagonAtoms615.outerLeftABC) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 6 1 5) • (rowColumnMul HexagonRowColumn615.rows_assocCAB HexagonRowColumn615.cols_right2)) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal6_case_1_5_row_1_1_2 : (((-1 : ℤ) ^ (rightScaleBit 6 1 5).val * positiveScale (rightScaleExponent 6 1 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 1 : ℤ)) • HexagonAtoms615.outerLeftABC) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 6 1 5) • (rowColumnMul HexagonRowColumn615.rows_assocCAB HexagonRowColumn615.cols_right2)) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal6_case_1_5_row_1_1_3 : (((-1 : ℤ) ^ (rightScaleBit 6 1 5).val * positiveScale (rightScaleExponent 6 1 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 1 : ℤ)) • HexagonAtoms615.outerLeftABC) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 6 1 5) • (rowColumnMul HexagonRowColumn615.rows_assocCAB HexagonRowColumn615.cols_right2)) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal6_case_1_5_checked : ((-1 : ℤ) ^ (rightScaleBit 6 1 5).val * positiveScale (rightScaleExponent 6 1 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 1 : ℤ)) • HexagonAtoms615.outerLeftABC = negativeScale (rightScaleExponent 6 1 5) • (rowColumnMul HexagonRowColumn615.rows_assocCAB HexagonRowColumn615.cols_right2) := by
  funext r
  fin_cases r
  · exact rightFinal6_case_1_5_row_0_0_0
  · exact rightFinal6_case_1_5_row_0_0_1
  · exact rightFinal6_case_1_5_row_0_0_2
  · exact rightFinal6_case_1_5_row_0_0_3
  · exact rightFinal6_case_1_5_row_0_1_0
  · exact rightFinal6_case_1_5_row_0_1_1
  · exact rightFinal6_case_1_5_row_0_1_2
  · exact rightFinal6_case_1_5_row_0_1_3
  · exact rightFinal6_case_1_5_row_1_0_0
  · exact rightFinal6_case_1_5_row_1_0_1
  · exact rightFinal6_case_1_5_row_1_0_2
  · exact rightFinal6_case_1_5_row_1_0_3
  · exact rightFinal6_case_1_5_row_1_1_0
  · exact rightFinal6_case_1_5_row_1_1_1
  · exact rightFinal6_case_1_5_row_1_1_2
  · exact rightFinal6_case_1_5_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem rightFinal6_case_1_5 : ((-1 : ℤ) ^ (rightScaleBit 6 1 5).val * positiveScale (rightScaleExponent 6 1 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 1 : ℤ)) • outerLeftZ 6 1 5 = negativeScale (rightScaleExponent 6 1 5) • (associatorZ 5 6 1 * right2Middle6 1 5) := by
  simpa only [HexagonAtoms615.assocABC_eq,
    HexagonAtoms615.outerABC_eq,
    HexagonAtoms615.assocBAC_eq,
    HexagonAtoms615.innerABC_eq,
    HexagonAtoms615.innerRightABC_eq,
    HexagonAtoms615.inverseACB_eq,
    HexagonAtoms615.innerACB_eq,
    HexagonAtoms615.assocBCA_eq,
    HexagonAtoms615.innerRightBAC_eq,
    HexagonAtoms615.assocCAB_eq,
    HexagonAtoms615.outerLeftABC_eq,
    HexagonRowColumn615.product0_eq,
    HexagonRowColumn615.product1_eq,
    HexagonRowColumn615.product2_eq,
    HexagonRowColumn615.product3_eq,
    HexagonRowColumn615.product4_eq,
    HexagonRowColumn615.product5_eq,
    HexagonRowColumn615.product6_eq,
    HexagonRowColumn615.product7_eq] using rightFinal6_case_1_5_checked

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonCases6
