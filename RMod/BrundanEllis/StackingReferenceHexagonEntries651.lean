import RMod.BrundanEllis.StackingReferenceHexagonMiddle6
import RMod.BrundanEllis.StackingReferenceSparseMatrixCheck
import RMod.BrundanEllis.StackingReferenceHexagonAtoms651
import RMod.BrundanEllis.StackingReferenceHexagonRowColumn651

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

private theorem left0Middle6_eq_case_5_1_row_0_0_0 : (left0Middle6 5 1) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn651.rows_outerABC HexagonRowColumn651.cols_assocABC) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_5_1_row_0_0_1 : (left0Middle6 5 1) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn651.rows_outerABC HexagonRowColumn651.cols_assocABC) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_5_1_row_0_0_2 : (left0Middle6 5 1) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn651.rows_outerABC HexagonRowColumn651.cols_assocABC) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_5_1_row_0_0_3 : (left0Middle6 5 1) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn651.rows_outerABC HexagonRowColumn651.cols_assocABC) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_5_1_row_0_1_0 : (left0Middle6 5 1) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn651.rows_outerABC HexagonRowColumn651.cols_assocABC) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_5_1_row_0_1_1 : (left0Middle6 5 1) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn651.rows_outerABC HexagonRowColumn651.cols_assocABC) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_5_1_row_0_1_2 : (left0Middle6 5 1) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn651.rows_outerABC HexagonRowColumn651.cols_assocABC) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_5_1_row_0_1_3 : (left0Middle6 5 1) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn651.rows_outerABC HexagonRowColumn651.cols_assocABC) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_5_1_row_1_0_0 : (left0Middle6 5 1) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn651.rows_outerABC HexagonRowColumn651.cols_assocABC) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_5_1_row_1_0_1 : (left0Middle6 5 1) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn651.rows_outerABC HexagonRowColumn651.cols_assocABC) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_5_1_row_1_0_2 : (left0Middle6 5 1) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn651.rows_outerABC HexagonRowColumn651.cols_assocABC) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_5_1_row_1_0_3 : (left0Middle6 5 1) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn651.rows_outerABC HexagonRowColumn651.cols_assocABC) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_5_1_row_1_1_0 : (left0Middle6 5 1) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn651.rows_outerABC HexagonRowColumn651.cols_assocABC) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_5_1_row_1_1_1 : (left0Middle6 5 1) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn651.rows_outerABC HexagonRowColumn651.cols_assocABC) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_5_1_row_1_1_2 : (left0Middle6 5 1) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn651.rows_outerABC HexagonRowColumn651.cols_assocABC) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_5_1_row_1_1_3 : (left0Middle6 5 1) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn651.rows_outerABC HexagonRowColumn651.cols_assocABC) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_5_1_checked : left0Middle6 5 1 = rowColumnMul HexagonRowColumn651.rows_outerABC HexagonRowColumn651.cols_assocABC := by
  funext r
  fin_cases r
  · exact left0Middle6_eq_case_5_1_row_0_0_0
  · exact left0Middle6_eq_case_5_1_row_0_0_1
  · exact left0Middle6_eq_case_5_1_row_0_0_2
  · exact left0Middle6_eq_case_5_1_row_0_0_3
  · exact left0Middle6_eq_case_5_1_row_0_1_0
  · exact left0Middle6_eq_case_5_1_row_0_1_1
  · exact left0Middle6_eq_case_5_1_row_0_1_2
  · exact left0Middle6_eq_case_5_1_row_0_1_3
  · exact left0Middle6_eq_case_5_1_row_1_0_0
  · exact left0Middle6_eq_case_5_1_row_1_0_1
  · exact left0Middle6_eq_case_5_1_row_1_0_2
  · exact left0Middle6_eq_case_5_1_row_1_0_3
  · exact left0Middle6_eq_case_5_1_row_1_1_0
  · exact left0Middle6_eq_case_5_1_row_1_1_1
  · exact left0Middle6_eq_case_5_1_row_1_1_2
  · exact left0Middle6_eq_case_5_1_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem left0Middle6_eq_case_5_1 : left0Middle6 5 1 = outerRightZ 6 5 1 * associatorZ 6 5 1 := by
  simpa only [HexagonAtoms651.assocABC_eq,
    HexagonAtoms651.outerABC_eq,
    HexagonAtoms651.assocBAC_eq,
    HexagonAtoms651.innerABC_eq,
    HexagonAtoms651.innerRightABC_eq,
    HexagonAtoms651.inverseACB_eq,
    HexagonAtoms651.innerACB_eq,
    HexagonAtoms651.assocBCA_eq,
    HexagonAtoms651.innerRightBAC_eq,
    HexagonAtoms651.assocCAB_eq,
    HexagonAtoms651.outerLeftABC_eq,
    HexagonRowColumn651.product0_eq,
    HexagonRowColumn651.product1_eq,
    HexagonRowColumn651.product2_eq,
    HexagonRowColumn651.product3_eq,
    HexagonRowColumn651.product4_eq,
    HexagonRowColumn651.product5_eq,
    HexagonRowColumn651.product6_eq,
    HexagonRowColumn651.product7_eq] using left0Middle6_eq_case_5_1_checked

private theorem left1Middle6_eq_case_5_1_row_0_0_0 : (left1Middle6 5 1) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms651.assocBAC) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_5_1_row_0_0_1 : (left1Middle6 5 1) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms651.assocBAC) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_5_1_row_0_0_2 : (left1Middle6 5 1) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms651.assocBAC) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_5_1_row_0_0_3 : (left1Middle6 5 1) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms651.assocBAC) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_5_1_row_0_1_0 : (left1Middle6 5 1) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms651.assocBAC) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_5_1_row_0_1_1 : (left1Middle6 5 1) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms651.assocBAC) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_5_1_row_0_1_2 : (left1Middle6 5 1) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms651.assocBAC) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_5_1_row_0_1_3 : (left1Middle6 5 1) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms651.assocBAC) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_5_1_row_1_0_0 : (left1Middle6 5 1) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms651.assocBAC) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_5_1_row_1_0_1 : (left1Middle6 5 1) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms651.assocBAC) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_5_1_row_1_0_2 : (left1Middle6 5 1) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms651.assocBAC) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_5_1_row_1_0_3 : (left1Middle6 5 1) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms651.assocBAC) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_5_1_row_1_1_0 : (left1Middle6 5 1) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms651.assocBAC) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_5_1_row_1_1_1 : (left1Middle6 5 1) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms651.assocBAC) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_5_1_row_1_1_2 : (left1Middle6 5 1) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms651.assocBAC) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_5_1_row_1_1_3 : (left1Middle6 5 1) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms651.assocBAC) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_5_1_checked : left1Middle6 5 1 = HexagonAtoms651.assocBAC := by
  funext r
  fin_cases r
  · exact left1Middle6_eq_case_5_1_row_0_0_0
  · exact left1Middle6_eq_case_5_1_row_0_0_1
  · exact left1Middle6_eq_case_5_1_row_0_0_2
  · exact left1Middle6_eq_case_5_1_row_0_0_3
  · exact left1Middle6_eq_case_5_1_row_0_1_0
  · exact left1Middle6_eq_case_5_1_row_0_1_1
  · exact left1Middle6_eq_case_5_1_row_0_1_2
  · exact left1Middle6_eq_case_5_1_row_0_1_3
  · exact left1Middle6_eq_case_5_1_row_1_0_0
  · exact left1Middle6_eq_case_5_1_row_1_0_1
  · exact left1Middle6_eq_case_5_1_row_1_0_2
  · exact left1Middle6_eq_case_5_1_row_1_0_3
  · exact left1Middle6_eq_case_5_1_row_1_1_0
  · exact left1Middle6_eq_case_5_1_row_1_1_1
  · exact left1Middle6_eq_case_5_1_row_1_1_2
  · exact left1Middle6_eq_case_5_1_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem left1Middle6_eq_case_5_1 : left1Middle6 5 1 = associatorZ 5 6 1 * innerLeftZ 6 5 1 := by
  simpa only [HexagonAtoms651.assocABC_eq,
    HexagonAtoms651.outerABC_eq,
    HexagonAtoms651.assocBAC_eq,
    HexagonAtoms651.innerABC_eq,
    HexagonAtoms651.innerRightABC_eq,
    HexagonAtoms651.inverseACB_eq,
    HexagonAtoms651.innerACB_eq,
    HexagonAtoms651.assocBCA_eq,
    HexagonAtoms651.innerRightBAC_eq,
    HexagonAtoms651.assocCAB_eq,
    HexagonAtoms651.outerLeftABC_eq,
    HexagonRowColumn651.product0_eq,
    HexagonRowColumn651.product1_eq,
    HexagonRowColumn651.product2_eq,
    HexagonRowColumn651.product3_eq,
    HexagonRowColumn651.product4_eq,
    HexagonRowColumn651.product5_eq,
    HexagonRowColumn651.product6_eq,
    HexagonRowColumn651.product7_eq] using left1Middle6_eq_case_5_1_checked

private theorem right0Middle6_eq_case_5_1_row_0_0_0 : (right0Middle6 5 1) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms651.assocABC) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_5_1_row_0_0_1 : (right0Middle6 5 1) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms651.assocABC) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_5_1_row_0_0_2 : (right0Middle6 5 1) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms651.assocABC) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_5_1_row_0_0_3 : (right0Middle6 5 1) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms651.assocABC) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_5_1_row_0_1_0 : (right0Middle6 5 1) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms651.assocABC) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_5_1_row_0_1_1 : (right0Middle6 5 1) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms651.assocABC) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_5_1_row_0_1_2 : (right0Middle6 5 1) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms651.assocABC) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_5_1_row_0_1_3 : (right0Middle6 5 1) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms651.assocABC) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_5_1_row_1_0_0 : (right0Middle6 5 1) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms651.assocABC) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_5_1_row_1_0_1 : (right0Middle6 5 1) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms651.assocABC) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_5_1_row_1_0_2 : (right0Middle6 5 1) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms651.assocABC) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_5_1_row_1_0_3 : (right0Middle6 5 1) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms651.assocABC) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_5_1_row_1_1_0 : (right0Middle6 5 1) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms651.assocABC) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_5_1_row_1_1_1 : (right0Middle6 5 1) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms651.assocABC) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_5_1_row_1_1_2 : (right0Middle6 5 1) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms651.assocABC) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_5_1_row_1_1_3 : (right0Middle6 5 1) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms651.assocABC) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_5_1_checked : right0Middle6 5 1 = HexagonAtoms651.assocABC := by
  funext r
  fin_cases r
  · exact right0Middle6_eq_case_5_1_row_0_0_0
  · exact right0Middle6_eq_case_5_1_row_0_0_1
  · exact right0Middle6_eq_case_5_1_row_0_0_2
  · exact right0Middle6_eq_case_5_1_row_0_0_3
  · exact right0Middle6_eq_case_5_1_row_0_1_0
  · exact right0Middle6_eq_case_5_1_row_0_1_1
  · exact right0Middle6_eq_case_5_1_row_0_1_2
  · exact right0Middle6_eq_case_5_1_row_0_1_3
  · exact right0Middle6_eq_case_5_1_row_1_0_0
  · exact right0Middle6_eq_case_5_1_row_1_0_1
  · exact right0Middle6_eq_case_5_1_row_1_0_2
  · exact right0Middle6_eq_case_5_1_row_1_0_3
  · exact right0Middle6_eq_case_5_1_row_1_1_0
  · exact right0Middle6_eq_case_5_1_row_1_1_1
  · exact right0Middle6_eq_case_5_1_row_1_1_2
  · exact right0Middle6_eq_case_5_1_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem right0Middle6_eq_case_5_1 : right0Middle6 5 1 = innerRightZ 6 5 1 * associatorZ 6 5 1 := by
  simpa only [HexagonAtoms651.assocABC_eq,
    HexagonAtoms651.outerABC_eq,
    HexagonAtoms651.assocBAC_eq,
    HexagonAtoms651.innerABC_eq,
    HexagonAtoms651.innerRightABC_eq,
    HexagonAtoms651.inverseACB_eq,
    HexagonAtoms651.innerACB_eq,
    HexagonAtoms651.assocBCA_eq,
    HexagonAtoms651.innerRightBAC_eq,
    HexagonAtoms651.assocCAB_eq,
    HexagonAtoms651.outerLeftABC_eq,
    HexagonRowColumn651.product0_eq,
    HexagonRowColumn651.product1_eq,
    HexagonRowColumn651.product2_eq,
    HexagonRowColumn651.product3_eq,
    HexagonRowColumn651.product4_eq,
    HexagonRowColumn651.product5_eq,
    HexagonRowColumn651.product6_eq,
    HexagonRowColumn651.product7_eq] using right0Middle6_eq_case_5_1_checked

private theorem right1Middle6_eq_case_5_1_row_0_0_0 : (right1Middle6 5 1) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn651.rows_inverseACB HexagonRowColumn651.cols_right0) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_5_1_row_0_0_1 : (right1Middle6 5 1) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn651.rows_inverseACB HexagonRowColumn651.cols_right0) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_5_1_row_0_0_2 : (right1Middle6 5 1) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn651.rows_inverseACB HexagonRowColumn651.cols_right0) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_5_1_row_0_0_3 : (right1Middle6 5 1) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn651.rows_inverseACB HexagonRowColumn651.cols_right0) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_5_1_row_0_1_0 : (right1Middle6 5 1) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn651.rows_inverseACB HexagonRowColumn651.cols_right0) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_5_1_row_0_1_1 : (right1Middle6 5 1) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn651.rows_inverseACB HexagonRowColumn651.cols_right0) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_5_1_row_0_1_2 : (right1Middle6 5 1) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn651.rows_inverseACB HexagonRowColumn651.cols_right0) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_5_1_row_0_1_3 : (right1Middle6 5 1) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn651.rows_inverseACB HexagonRowColumn651.cols_right0) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_5_1_row_1_0_0 : (right1Middle6 5 1) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn651.rows_inverseACB HexagonRowColumn651.cols_right0) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_5_1_row_1_0_1 : (right1Middle6 5 1) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn651.rows_inverseACB HexagonRowColumn651.cols_right0) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_5_1_row_1_0_2 : (right1Middle6 5 1) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn651.rows_inverseACB HexagonRowColumn651.cols_right0) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_5_1_row_1_0_3 : (right1Middle6 5 1) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn651.rows_inverseACB HexagonRowColumn651.cols_right0) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_5_1_row_1_1_0 : (right1Middle6 5 1) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn651.rows_inverseACB HexagonRowColumn651.cols_right0) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_5_1_row_1_1_1 : (right1Middle6 5 1) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn651.rows_inverseACB HexagonRowColumn651.cols_right0) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_5_1_row_1_1_2 : (right1Middle6 5 1) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn651.rows_inverseACB HexagonRowColumn651.cols_right0) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_5_1_row_1_1_3 : (right1Middle6 5 1) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn651.rows_inverseACB HexagonRowColumn651.cols_right0) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_5_1_checked : right1Middle6 5 1 = rowColumnMul HexagonRowColumn651.rows_inverseACB HexagonRowColumn651.cols_right0 := by
  funext r
  fin_cases r
  · exact right1Middle6_eq_case_5_1_row_0_0_0
  · exact right1Middle6_eq_case_5_1_row_0_0_1
  · exact right1Middle6_eq_case_5_1_row_0_0_2
  · exact right1Middle6_eq_case_5_1_row_0_0_3
  · exact right1Middle6_eq_case_5_1_row_0_1_0
  · exact right1Middle6_eq_case_5_1_row_0_1_1
  · exact right1Middle6_eq_case_5_1_row_0_1_2
  · exact right1Middle6_eq_case_5_1_row_0_1_3
  · exact right1Middle6_eq_case_5_1_row_1_0_0
  · exact right1Middle6_eq_case_5_1_row_1_0_1
  · exact right1Middle6_eq_case_5_1_row_1_0_2
  · exact right1Middle6_eq_case_5_1_row_1_0_3
  · exact right1Middle6_eq_case_5_1_row_1_1_0
  · exact right1Middle6_eq_case_5_1_row_1_1_1
  · exact right1Middle6_eq_case_5_1_row_1_1_2
  · exact right1Middle6_eq_case_5_1_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem right1Middle6_eq_case_5_1 : right1Middle6 5 1 = associatorInverseZ 6 1 5 * right0Middle6 5 1 := by
  simpa only [HexagonAtoms651.assocABC_eq,
    HexagonAtoms651.outerABC_eq,
    HexagonAtoms651.assocBAC_eq,
    HexagonAtoms651.innerABC_eq,
    HexagonAtoms651.innerRightABC_eq,
    HexagonAtoms651.inverseACB_eq,
    HexagonAtoms651.innerACB_eq,
    HexagonAtoms651.assocBCA_eq,
    HexagonAtoms651.innerRightBAC_eq,
    HexagonAtoms651.assocCAB_eq,
    HexagonAtoms651.outerLeftABC_eq,
    HexagonRowColumn651.product0_eq,
    HexagonRowColumn651.product1_eq,
    HexagonRowColumn651.product2_eq,
    HexagonRowColumn651.product3_eq,
    HexagonRowColumn651.product4_eq,
    HexagonRowColumn651.product5_eq,
    HexagonRowColumn651.product6_eq,
    HexagonRowColumn651.product7_eq] using right1Middle6_eq_case_5_1_checked

private theorem right2Middle6_eq_case_5_1_row_0_0_0 : (right2Middle6 5 1) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (right1Middle6 5 1) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_5_1_row_0_0_1 : (right2Middle6 5 1) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (right1Middle6 5 1) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_5_1_row_0_0_2 : (right2Middle6 5 1) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (right1Middle6 5 1) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_5_1_row_0_0_3 : (right2Middle6 5 1) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (right1Middle6 5 1) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_5_1_row_0_1_0 : (right2Middle6 5 1) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (right1Middle6 5 1) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_5_1_row_0_1_1 : (right2Middle6 5 1) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (right1Middle6 5 1) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_5_1_row_0_1_2 : (right2Middle6 5 1) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (right1Middle6 5 1) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_5_1_row_0_1_3 : (right2Middle6 5 1) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (right1Middle6 5 1) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_5_1_row_1_0_0 : (right2Middle6 5 1) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (right1Middle6 5 1) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_5_1_row_1_0_1 : (right2Middle6 5 1) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (right1Middle6 5 1) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_5_1_row_1_0_2 : (right2Middle6 5 1) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (right1Middle6 5 1) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_5_1_row_1_0_3 : (right2Middle6 5 1) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (right1Middle6 5 1) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_5_1_row_1_1_0 : (right2Middle6 5 1) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (right1Middle6 5 1) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_5_1_row_1_1_1 : (right2Middle6 5 1) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (right1Middle6 5 1) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_5_1_row_1_1_2 : (right2Middle6 5 1) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (right1Middle6 5 1) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_5_1_row_1_1_3 : (right2Middle6 5 1) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (right1Middle6 5 1) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_5_1_checked : right2Middle6 5 1 = right1Middle6 5 1 := by
  funext r
  fin_cases r
  · exact right2Middle6_eq_case_5_1_row_0_0_0
  · exact right2Middle6_eq_case_5_1_row_0_0_1
  · exact right2Middle6_eq_case_5_1_row_0_0_2
  · exact right2Middle6_eq_case_5_1_row_0_0_3
  · exact right2Middle6_eq_case_5_1_row_0_1_0
  · exact right2Middle6_eq_case_5_1_row_0_1_1
  · exact right2Middle6_eq_case_5_1_row_0_1_2
  · exact right2Middle6_eq_case_5_1_row_0_1_3
  · exact right2Middle6_eq_case_5_1_row_1_0_0
  · exact right2Middle6_eq_case_5_1_row_1_0_1
  · exact right2Middle6_eq_case_5_1_row_1_0_2
  · exact right2Middle6_eq_case_5_1_row_1_0_3
  · exact right2Middle6_eq_case_5_1_row_1_1_0
  · exact right2Middle6_eq_case_5_1_row_1_1_1
  · exact right2Middle6_eq_case_5_1_row_1_1_2
  · exact right2Middle6_eq_case_5_1_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem right2Middle6_eq_case_5_1 : right2Middle6 5 1 = innerLeftZ 6 1 5 * right1Middle6 5 1 := by
  simpa only [HexagonAtoms651.assocABC_eq,
    HexagonAtoms651.outerABC_eq,
    HexagonAtoms651.assocBAC_eq,
    HexagonAtoms651.innerABC_eq,
    HexagonAtoms651.innerRightABC_eq,
    HexagonAtoms651.inverseACB_eq,
    HexagonAtoms651.innerACB_eq,
    HexagonAtoms651.assocBCA_eq,
    HexagonAtoms651.innerRightBAC_eq,
    HexagonAtoms651.assocCAB_eq,
    HexagonAtoms651.outerLeftABC_eq,
    HexagonRowColumn651.product0_eq,
    HexagonRowColumn651.product1_eq,
    HexagonRowColumn651.product2_eq,
    HexagonRowColumn651.product3_eq,
    HexagonRowColumn651.product4_eq,
    HexagonRowColumn651.product5_eq,
    HexagonRowColumn651.product6_eq,
    HexagonRowColumn651.product7_eq] using right2Middle6_eq_case_5_1_checked

private theorem leftFinal6_case_5_1_row_0_0_0 : (((-1 : ℤ) ^ (leftScaleBit 6 5 1).val * positiveScale (leftScaleExponent 6 5 1)) •
      (rowColumnMul HexagonRowColumn651.rows_assocBCA HexagonRowColumn651.cols_left0)) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 6 5 1) • (left1Middle6 5 1)) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal6_case_5_1_row_0_0_1 : (((-1 : ℤ) ^ (leftScaleBit 6 5 1).val * positiveScale (leftScaleExponent 6 5 1)) •
      (rowColumnMul HexagonRowColumn651.rows_assocBCA HexagonRowColumn651.cols_left0)) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 6 5 1) • (left1Middle6 5 1)) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal6_case_5_1_row_0_0_2 : (((-1 : ℤ) ^ (leftScaleBit 6 5 1).val * positiveScale (leftScaleExponent 6 5 1)) •
      (rowColumnMul HexagonRowColumn651.rows_assocBCA HexagonRowColumn651.cols_left0)) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 6 5 1) • (left1Middle6 5 1)) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal6_case_5_1_row_0_0_3 : (((-1 : ℤ) ^ (leftScaleBit 6 5 1).val * positiveScale (leftScaleExponent 6 5 1)) •
      (rowColumnMul HexagonRowColumn651.rows_assocBCA HexagonRowColumn651.cols_left0)) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 6 5 1) • (left1Middle6 5 1)) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal6_case_5_1_row_0_1_0 : (((-1 : ℤ) ^ (leftScaleBit 6 5 1).val * positiveScale (leftScaleExponent 6 5 1)) •
      (rowColumnMul HexagonRowColumn651.rows_assocBCA HexagonRowColumn651.cols_left0)) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 6 5 1) • (left1Middle6 5 1)) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal6_case_5_1_row_0_1_1 : (((-1 : ℤ) ^ (leftScaleBit 6 5 1).val * positiveScale (leftScaleExponent 6 5 1)) •
      (rowColumnMul HexagonRowColumn651.rows_assocBCA HexagonRowColumn651.cols_left0)) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 6 5 1) • (left1Middle6 5 1)) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal6_case_5_1_row_0_1_2 : (((-1 : ℤ) ^ (leftScaleBit 6 5 1).val * positiveScale (leftScaleExponent 6 5 1)) •
      (rowColumnMul HexagonRowColumn651.rows_assocBCA HexagonRowColumn651.cols_left0)) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 6 5 1) • (left1Middle6 5 1)) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal6_case_5_1_row_0_1_3 : (((-1 : ℤ) ^ (leftScaleBit 6 5 1).val * positiveScale (leftScaleExponent 6 5 1)) •
      (rowColumnMul HexagonRowColumn651.rows_assocBCA HexagonRowColumn651.cols_left0)) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 6 5 1) • (left1Middle6 5 1)) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal6_case_5_1_row_1_0_0 : (((-1 : ℤ) ^ (leftScaleBit 6 5 1).val * positiveScale (leftScaleExponent 6 5 1)) •
      (rowColumnMul HexagonRowColumn651.rows_assocBCA HexagonRowColumn651.cols_left0)) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 6 5 1) • (left1Middle6 5 1)) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal6_case_5_1_row_1_0_1 : (((-1 : ℤ) ^ (leftScaleBit 6 5 1).val * positiveScale (leftScaleExponent 6 5 1)) •
      (rowColumnMul HexagonRowColumn651.rows_assocBCA HexagonRowColumn651.cols_left0)) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 6 5 1) • (left1Middle6 5 1)) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal6_case_5_1_row_1_0_2 : (((-1 : ℤ) ^ (leftScaleBit 6 5 1).val * positiveScale (leftScaleExponent 6 5 1)) •
      (rowColumnMul HexagonRowColumn651.rows_assocBCA HexagonRowColumn651.cols_left0)) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 6 5 1) • (left1Middle6 5 1)) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal6_case_5_1_row_1_0_3 : (((-1 : ℤ) ^ (leftScaleBit 6 5 1).val * positiveScale (leftScaleExponent 6 5 1)) •
      (rowColumnMul HexagonRowColumn651.rows_assocBCA HexagonRowColumn651.cols_left0)) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 6 5 1) • (left1Middle6 5 1)) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal6_case_5_1_row_1_1_0 : (((-1 : ℤ) ^ (leftScaleBit 6 5 1).val * positiveScale (leftScaleExponent 6 5 1)) •
      (rowColumnMul HexagonRowColumn651.rows_assocBCA HexagonRowColumn651.cols_left0)) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 6 5 1) • (left1Middle6 5 1)) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal6_case_5_1_row_1_1_1 : (((-1 : ℤ) ^ (leftScaleBit 6 5 1).val * positiveScale (leftScaleExponent 6 5 1)) •
      (rowColumnMul HexagonRowColumn651.rows_assocBCA HexagonRowColumn651.cols_left0)) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 6 5 1) • (left1Middle6 5 1)) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal6_case_5_1_row_1_1_2 : (((-1 : ℤ) ^ (leftScaleBit 6 5 1).val * positiveScale (leftScaleExponent 6 5 1)) •
      (rowColumnMul HexagonRowColumn651.rows_assocBCA HexagonRowColumn651.cols_left0)) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 6 5 1) • (left1Middle6 5 1)) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal6_case_5_1_row_1_1_3 : (((-1 : ℤ) ^ (leftScaleBit 6 5 1).val * positiveScale (leftScaleExponent 6 5 1)) •
      (rowColumnMul HexagonRowColumn651.rows_assocBCA HexagonRowColumn651.cols_left0)) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 6 5 1) • (left1Middle6 5 1)) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal6_case_5_1_checked : ((-1 : ℤ) ^ (leftScaleBit 6 5 1).val * positiveScale (leftScaleExponent 6 5 1)) •
      (rowColumnMul HexagonRowColumn651.rows_assocBCA HexagonRowColumn651.cols_left0) = negativeScale (leftScaleExponent 6 5 1) • (left1Middle6 5 1) := by
  funext r
  fin_cases r
  · exact leftFinal6_case_5_1_row_0_0_0
  · exact leftFinal6_case_5_1_row_0_0_1
  · exact leftFinal6_case_5_1_row_0_0_2
  · exact leftFinal6_case_5_1_row_0_0_3
  · exact leftFinal6_case_5_1_row_0_1_0
  · exact leftFinal6_case_5_1_row_0_1_1
  · exact leftFinal6_case_5_1_row_0_1_2
  · exact leftFinal6_case_5_1_row_0_1_3
  · exact leftFinal6_case_5_1_row_1_0_0
  · exact leftFinal6_case_5_1_row_1_0_1
  · exact leftFinal6_case_5_1_row_1_0_2
  · exact leftFinal6_case_5_1_row_1_0_3
  · exact leftFinal6_case_5_1_row_1_1_0
  · exact leftFinal6_case_5_1_row_1_1_1
  · exact leftFinal6_case_5_1_row_1_1_2
  · exact leftFinal6_case_5_1_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem leftFinal6_case_5_1 : ((-1 : ℤ) ^ (leftScaleBit 6 5 1).val * positiveScale (leftScaleExponent 6 5 1)) •
      (associatorZ 5 1 6 * left0Middle6 5 1) = negativeScale (leftScaleExponent 6 5 1) • (innerRightZ 5 6 1 * left1Middle6 5 1) := by
  simpa only [HexagonAtoms651.assocABC_eq,
    HexagonAtoms651.outerABC_eq,
    HexagonAtoms651.assocBAC_eq,
    HexagonAtoms651.innerABC_eq,
    HexagonAtoms651.innerRightABC_eq,
    HexagonAtoms651.inverseACB_eq,
    HexagonAtoms651.innerACB_eq,
    HexagonAtoms651.assocBCA_eq,
    HexagonAtoms651.innerRightBAC_eq,
    HexagonAtoms651.assocCAB_eq,
    HexagonAtoms651.outerLeftABC_eq,
    HexagonRowColumn651.product0_eq,
    HexagonRowColumn651.product1_eq,
    HexagonRowColumn651.product2_eq,
    HexagonRowColumn651.product3_eq,
    HexagonRowColumn651.product4_eq,
    HexagonRowColumn651.product5_eq,
    HexagonRowColumn651.product6_eq,
    HexagonRowColumn651.product7_eq] using leftFinal6_case_5_1_checked

private theorem rightFinal6_case_5_1_row_0_0_0 : (((-1 : ℤ) ^ (rightScaleBit 6 5 1).val * positiveScale (rightScaleExponent 6 5 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 1 5 : ℤ)) • HexagonAtoms651.outerLeftABC) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 6 5 1) • (rowColumnMul HexagonRowColumn651.rows_assocCAB HexagonRowColumn651.cols_right2)) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal6_case_5_1_row_0_0_1 : (((-1 : ℤ) ^ (rightScaleBit 6 5 1).val * positiveScale (rightScaleExponent 6 5 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 1 5 : ℤ)) • HexagonAtoms651.outerLeftABC) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 6 5 1) • (rowColumnMul HexagonRowColumn651.rows_assocCAB HexagonRowColumn651.cols_right2)) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal6_case_5_1_row_0_0_2 : (((-1 : ℤ) ^ (rightScaleBit 6 5 1).val * positiveScale (rightScaleExponent 6 5 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 1 5 : ℤ)) • HexagonAtoms651.outerLeftABC) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 6 5 1) • (rowColumnMul HexagonRowColumn651.rows_assocCAB HexagonRowColumn651.cols_right2)) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal6_case_5_1_row_0_0_3 : (((-1 : ℤ) ^ (rightScaleBit 6 5 1).val * positiveScale (rightScaleExponent 6 5 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 1 5 : ℤ)) • HexagonAtoms651.outerLeftABC) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 6 5 1) • (rowColumnMul HexagonRowColumn651.rows_assocCAB HexagonRowColumn651.cols_right2)) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal6_case_5_1_row_0_1_0 : (((-1 : ℤ) ^ (rightScaleBit 6 5 1).val * positiveScale (rightScaleExponent 6 5 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 1 5 : ℤ)) • HexagonAtoms651.outerLeftABC) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 6 5 1) • (rowColumnMul HexagonRowColumn651.rows_assocCAB HexagonRowColumn651.cols_right2)) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal6_case_5_1_row_0_1_1 : (((-1 : ℤ) ^ (rightScaleBit 6 5 1).val * positiveScale (rightScaleExponent 6 5 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 1 5 : ℤ)) • HexagonAtoms651.outerLeftABC) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 6 5 1) • (rowColumnMul HexagonRowColumn651.rows_assocCAB HexagonRowColumn651.cols_right2)) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal6_case_5_1_row_0_1_2 : (((-1 : ℤ) ^ (rightScaleBit 6 5 1).val * positiveScale (rightScaleExponent 6 5 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 1 5 : ℤ)) • HexagonAtoms651.outerLeftABC) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 6 5 1) • (rowColumnMul HexagonRowColumn651.rows_assocCAB HexagonRowColumn651.cols_right2)) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal6_case_5_1_row_0_1_3 : (((-1 : ℤ) ^ (rightScaleBit 6 5 1).val * positiveScale (rightScaleExponent 6 5 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 1 5 : ℤ)) • HexagonAtoms651.outerLeftABC) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 6 5 1) • (rowColumnMul HexagonRowColumn651.rows_assocCAB HexagonRowColumn651.cols_right2)) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal6_case_5_1_row_1_0_0 : (((-1 : ℤ) ^ (rightScaleBit 6 5 1).val * positiveScale (rightScaleExponent 6 5 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 1 5 : ℤ)) • HexagonAtoms651.outerLeftABC) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 6 5 1) • (rowColumnMul HexagonRowColumn651.rows_assocCAB HexagonRowColumn651.cols_right2)) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal6_case_5_1_row_1_0_1 : (((-1 : ℤ) ^ (rightScaleBit 6 5 1).val * positiveScale (rightScaleExponent 6 5 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 1 5 : ℤ)) • HexagonAtoms651.outerLeftABC) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 6 5 1) • (rowColumnMul HexagonRowColumn651.rows_assocCAB HexagonRowColumn651.cols_right2)) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal6_case_5_1_row_1_0_2 : (((-1 : ℤ) ^ (rightScaleBit 6 5 1).val * positiveScale (rightScaleExponent 6 5 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 1 5 : ℤ)) • HexagonAtoms651.outerLeftABC) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 6 5 1) • (rowColumnMul HexagonRowColumn651.rows_assocCAB HexagonRowColumn651.cols_right2)) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal6_case_5_1_row_1_0_3 : (((-1 : ℤ) ^ (rightScaleBit 6 5 1).val * positiveScale (rightScaleExponent 6 5 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 1 5 : ℤ)) • HexagonAtoms651.outerLeftABC) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 6 5 1) • (rowColumnMul HexagonRowColumn651.rows_assocCAB HexagonRowColumn651.cols_right2)) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal6_case_5_1_row_1_1_0 : (((-1 : ℤ) ^ (rightScaleBit 6 5 1).val * positiveScale (rightScaleExponent 6 5 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 1 5 : ℤ)) • HexagonAtoms651.outerLeftABC) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 6 5 1) • (rowColumnMul HexagonRowColumn651.rows_assocCAB HexagonRowColumn651.cols_right2)) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal6_case_5_1_row_1_1_1 : (((-1 : ℤ) ^ (rightScaleBit 6 5 1).val * positiveScale (rightScaleExponent 6 5 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 1 5 : ℤ)) • HexagonAtoms651.outerLeftABC) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 6 5 1) • (rowColumnMul HexagonRowColumn651.rows_assocCAB HexagonRowColumn651.cols_right2)) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal6_case_5_1_row_1_1_2 : (((-1 : ℤ) ^ (rightScaleBit 6 5 1).val * positiveScale (rightScaleExponent 6 5 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 1 5 : ℤ)) • HexagonAtoms651.outerLeftABC) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 6 5 1) • (rowColumnMul HexagonRowColumn651.rows_assocCAB HexagonRowColumn651.cols_right2)) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal6_case_5_1_row_1_1_3 : (((-1 : ℤ) ^ (rightScaleBit 6 5 1).val * positiveScale (rightScaleExponent 6 5 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 1 5 : ℤ)) • HexagonAtoms651.outerLeftABC) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 6 5 1) • (rowColumnMul HexagonRowColumn651.rows_assocCAB HexagonRowColumn651.cols_right2)) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal6_case_5_1_checked : ((-1 : ℤ) ^ (rightScaleBit 6 5 1).val * positiveScale (rightScaleExponent 6 5 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 1 5 : ℤ)) • HexagonAtoms651.outerLeftABC = negativeScale (rightScaleExponent 6 5 1) • (rowColumnMul HexagonRowColumn651.rows_assocCAB HexagonRowColumn651.cols_right2) := by
  funext r
  fin_cases r
  · exact rightFinal6_case_5_1_row_0_0_0
  · exact rightFinal6_case_5_1_row_0_0_1
  · exact rightFinal6_case_5_1_row_0_0_2
  · exact rightFinal6_case_5_1_row_0_0_3
  · exact rightFinal6_case_5_1_row_0_1_0
  · exact rightFinal6_case_5_1_row_0_1_1
  · exact rightFinal6_case_5_1_row_0_1_2
  · exact rightFinal6_case_5_1_row_0_1_3
  · exact rightFinal6_case_5_1_row_1_0_0
  · exact rightFinal6_case_5_1_row_1_0_1
  · exact rightFinal6_case_5_1_row_1_0_2
  · exact rightFinal6_case_5_1_row_1_0_3
  · exact rightFinal6_case_5_1_row_1_1_0
  · exact rightFinal6_case_5_1_row_1_1_1
  · exact rightFinal6_case_5_1_row_1_1_2
  · exact rightFinal6_case_5_1_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem rightFinal6_case_5_1 : ((-1 : ℤ) ^ (rightScaleBit 6 5 1).val * positiveScale (rightScaleExponent 6 5 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 1 5 : ℤ)) • outerLeftZ 6 5 1 = negativeScale (rightScaleExponent 6 5 1) • (associatorZ 1 6 5 * right2Middle6 5 1) := by
  simpa only [HexagonAtoms651.assocABC_eq,
    HexagonAtoms651.outerABC_eq,
    HexagonAtoms651.assocBAC_eq,
    HexagonAtoms651.innerABC_eq,
    HexagonAtoms651.innerRightABC_eq,
    HexagonAtoms651.inverseACB_eq,
    HexagonAtoms651.innerACB_eq,
    HexagonAtoms651.assocBCA_eq,
    HexagonAtoms651.innerRightBAC_eq,
    HexagonAtoms651.assocCAB_eq,
    HexagonAtoms651.outerLeftABC_eq,
    HexagonRowColumn651.product0_eq,
    HexagonRowColumn651.product1_eq,
    HexagonRowColumn651.product2_eq,
    HexagonRowColumn651.product3_eq,
    HexagonRowColumn651.product4_eq,
    HexagonRowColumn651.product5_eq,
    HexagonRowColumn651.product6_eq,
    HexagonRowColumn651.product7_eq] using rightFinal6_case_5_1_checked

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonCases6
