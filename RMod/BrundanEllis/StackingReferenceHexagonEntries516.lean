import RMod.BrundanEllis.StackingReferenceHexagonMiddle5
import RMod.BrundanEllis.StackingReferenceSparseMatrixCheck
import RMod.BrundanEllis.StackingReferenceHexagonAtoms516
import RMod.BrundanEllis.StackingReferenceHexagonRowColumn516

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

private theorem left0Middle5_eq_case_1_6_row_0_0_0 : (left0Middle5 1 6) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn516.rows_outerABC HexagonRowColumn516.cols_assocABC) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_1_6_row_0_0_1 : (left0Middle5 1 6) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn516.rows_outerABC HexagonRowColumn516.cols_assocABC) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_1_6_row_0_0_2 : (left0Middle5 1 6) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn516.rows_outerABC HexagonRowColumn516.cols_assocABC) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_1_6_row_0_0_3 : (left0Middle5 1 6) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn516.rows_outerABC HexagonRowColumn516.cols_assocABC) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_1_6_row_0_1_0 : (left0Middle5 1 6) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn516.rows_outerABC HexagonRowColumn516.cols_assocABC) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_1_6_row_0_1_1 : (left0Middle5 1 6) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn516.rows_outerABC HexagonRowColumn516.cols_assocABC) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_1_6_row_0_1_2 : (left0Middle5 1 6) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn516.rows_outerABC HexagonRowColumn516.cols_assocABC) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_1_6_row_0_1_3 : (left0Middle5 1 6) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn516.rows_outerABC HexagonRowColumn516.cols_assocABC) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_1_6_row_1_0_0 : (left0Middle5 1 6) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn516.rows_outerABC HexagonRowColumn516.cols_assocABC) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_1_6_row_1_0_1 : (left0Middle5 1 6) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn516.rows_outerABC HexagonRowColumn516.cols_assocABC) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_1_6_row_1_0_2 : (left0Middle5 1 6) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn516.rows_outerABC HexagonRowColumn516.cols_assocABC) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_1_6_row_1_0_3 : (left0Middle5 1 6) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn516.rows_outerABC HexagonRowColumn516.cols_assocABC) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_1_6_row_1_1_0 : (left0Middle5 1 6) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn516.rows_outerABC HexagonRowColumn516.cols_assocABC) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_1_6_row_1_1_1 : (left0Middle5 1 6) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn516.rows_outerABC HexagonRowColumn516.cols_assocABC) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_1_6_row_1_1_2 : (left0Middle5 1 6) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn516.rows_outerABC HexagonRowColumn516.cols_assocABC) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_1_6_row_1_1_3 : (left0Middle5 1 6) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn516.rows_outerABC HexagonRowColumn516.cols_assocABC) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_1_6_checked : left0Middle5 1 6 = rowColumnMul HexagonRowColumn516.rows_outerABC HexagonRowColumn516.cols_assocABC := by
  funext r
  fin_cases r
  · exact left0Middle5_eq_case_1_6_row_0_0_0
  · exact left0Middle5_eq_case_1_6_row_0_0_1
  · exact left0Middle5_eq_case_1_6_row_0_0_2
  · exact left0Middle5_eq_case_1_6_row_0_0_3
  · exact left0Middle5_eq_case_1_6_row_0_1_0
  · exact left0Middle5_eq_case_1_6_row_0_1_1
  · exact left0Middle5_eq_case_1_6_row_0_1_2
  · exact left0Middle5_eq_case_1_6_row_0_1_3
  · exact left0Middle5_eq_case_1_6_row_1_0_0
  · exact left0Middle5_eq_case_1_6_row_1_0_1
  · exact left0Middle5_eq_case_1_6_row_1_0_2
  · exact left0Middle5_eq_case_1_6_row_1_0_3
  · exact left0Middle5_eq_case_1_6_row_1_1_0
  · exact left0Middle5_eq_case_1_6_row_1_1_1
  · exact left0Middle5_eq_case_1_6_row_1_1_2
  · exact left0Middle5_eq_case_1_6_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem left0Middle5_eq_case_1_6 : left0Middle5 1 6 = outerRightZ 5 1 6 * associatorZ 5 1 6 := by
  simpa only [HexagonAtoms516.assocABC_eq,
    HexagonAtoms516.outerABC_eq,
    HexagonAtoms516.assocBAC_eq,
    HexagonAtoms516.innerABC_eq,
    HexagonAtoms516.innerRightABC_eq,
    HexagonAtoms516.inverseACB_eq,
    HexagonAtoms516.innerACB_eq,
    HexagonAtoms516.assocBCA_eq,
    HexagonAtoms516.innerRightBAC_eq,
    HexagonAtoms516.assocCAB_eq,
    HexagonAtoms516.outerLeftABC_eq,
    HexagonRowColumn516.product0_eq,
    HexagonRowColumn516.product1_eq,
    HexagonRowColumn516.product2_eq,
    HexagonRowColumn516.product3_eq,
    HexagonRowColumn516.product4_eq,
    HexagonRowColumn516.product5_eq,
    HexagonRowColumn516.product6_eq,
    HexagonRowColumn516.product7_eq] using left0Middle5_eq_case_1_6_checked

private theorem left1Middle5_eq_case_1_6_row_0_0_0 : (left1Middle5 1 6) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms516.assocBAC) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_1_6_row_0_0_1 : (left1Middle5 1 6) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms516.assocBAC) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_1_6_row_0_0_2 : (left1Middle5 1 6) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms516.assocBAC) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_1_6_row_0_0_3 : (left1Middle5 1 6) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms516.assocBAC) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_1_6_row_0_1_0 : (left1Middle5 1 6) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms516.assocBAC) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_1_6_row_0_1_1 : (left1Middle5 1 6) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms516.assocBAC) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_1_6_row_0_1_2 : (left1Middle5 1 6) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms516.assocBAC) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_1_6_row_0_1_3 : (left1Middle5 1 6) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms516.assocBAC) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_1_6_row_1_0_0 : (left1Middle5 1 6) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms516.assocBAC) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_1_6_row_1_0_1 : (left1Middle5 1 6) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms516.assocBAC) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_1_6_row_1_0_2 : (left1Middle5 1 6) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms516.assocBAC) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_1_6_row_1_0_3 : (left1Middle5 1 6) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms516.assocBAC) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_1_6_row_1_1_0 : (left1Middle5 1 6) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms516.assocBAC) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_1_6_row_1_1_1 : (left1Middle5 1 6) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms516.assocBAC) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_1_6_row_1_1_2 : (left1Middle5 1 6) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms516.assocBAC) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_1_6_row_1_1_3 : (left1Middle5 1 6) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms516.assocBAC) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_1_6_checked : left1Middle5 1 6 = HexagonAtoms516.assocBAC := by
  funext r
  fin_cases r
  · exact left1Middle5_eq_case_1_6_row_0_0_0
  · exact left1Middle5_eq_case_1_6_row_0_0_1
  · exact left1Middle5_eq_case_1_6_row_0_0_2
  · exact left1Middle5_eq_case_1_6_row_0_0_3
  · exact left1Middle5_eq_case_1_6_row_0_1_0
  · exact left1Middle5_eq_case_1_6_row_0_1_1
  · exact left1Middle5_eq_case_1_6_row_0_1_2
  · exact left1Middle5_eq_case_1_6_row_0_1_3
  · exact left1Middle5_eq_case_1_6_row_1_0_0
  · exact left1Middle5_eq_case_1_6_row_1_0_1
  · exact left1Middle5_eq_case_1_6_row_1_0_2
  · exact left1Middle5_eq_case_1_6_row_1_0_3
  · exact left1Middle5_eq_case_1_6_row_1_1_0
  · exact left1Middle5_eq_case_1_6_row_1_1_1
  · exact left1Middle5_eq_case_1_6_row_1_1_2
  · exact left1Middle5_eq_case_1_6_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem left1Middle5_eq_case_1_6 : left1Middle5 1 6 = associatorZ 1 5 6 * innerLeftZ 5 1 6 := by
  simpa only [HexagonAtoms516.assocABC_eq,
    HexagonAtoms516.outerABC_eq,
    HexagonAtoms516.assocBAC_eq,
    HexagonAtoms516.innerABC_eq,
    HexagonAtoms516.innerRightABC_eq,
    HexagonAtoms516.inverseACB_eq,
    HexagonAtoms516.innerACB_eq,
    HexagonAtoms516.assocBCA_eq,
    HexagonAtoms516.innerRightBAC_eq,
    HexagonAtoms516.assocCAB_eq,
    HexagonAtoms516.outerLeftABC_eq,
    HexagonRowColumn516.product0_eq,
    HexagonRowColumn516.product1_eq,
    HexagonRowColumn516.product2_eq,
    HexagonRowColumn516.product3_eq,
    HexagonRowColumn516.product4_eq,
    HexagonRowColumn516.product5_eq,
    HexagonRowColumn516.product6_eq,
    HexagonRowColumn516.product7_eq] using left1Middle5_eq_case_1_6_checked

private theorem right0Middle5_eq_case_1_6_row_0_0_0 : (right0Middle5 1 6) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms516.assocABC) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_1_6_row_0_0_1 : (right0Middle5 1 6) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms516.assocABC) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_1_6_row_0_0_2 : (right0Middle5 1 6) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms516.assocABC) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_1_6_row_0_0_3 : (right0Middle5 1 6) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms516.assocABC) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_1_6_row_0_1_0 : (right0Middle5 1 6) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms516.assocABC) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_1_6_row_0_1_1 : (right0Middle5 1 6) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms516.assocABC) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_1_6_row_0_1_2 : (right0Middle5 1 6) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms516.assocABC) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_1_6_row_0_1_3 : (right0Middle5 1 6) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms516.assocABC) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_1_6_row_1_0_0 : (right0Middle5 1 6) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms516.assocABC) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_1_6_row_1_0_1 : (right0Middle5 1 6) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms516.assocABC) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_1_6_row_1_0_2 : (right0Middle5 1 6) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms516.assocABC) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_1_6_row_1_0_3 : (right0Middle5 1 6) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms516.assocABC) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_1_6_row_1_1_0 : (right0Middle5 1 6) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms516.assocABC) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_1_6_row_1_1_1 : (right0Middle5 1 6) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms516.assocABC) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_1_6_row_1_1_2 : (right0Middle5 1 6) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms516.assocABC) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_1_6_row_1_1_3 : (right0Middle5 1 6) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms516.assocABC) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_1_6_checked : right0Middle5 1 6 = HexagonAtoms516.assocABC := by
  funext r
  fin_cases r
  · exact right0Middle5_eq_case_1_6_row_0_0_0
  · exact right0Middle5_eq_case_1_6_row_0_0_1
  · exact right0Middle5_eq_case_1_6_row_0_0_2
  · exact right0Middle5_eq_case_1_6_row_0_0_3
  · exact right0Middle5_eq_case_1_6_row_0_1_0
  · exact right0Middle5_eq_case_1_6_row_0_1_1
  · exact right0Middle5_eq_case_1_6_row_0_1_2
  · exact right0Middle5_eq_case_1_6_row_0_1_3
  · exact right0Middle5_eq_case_1_6_row_1_0_0
  · exact right0Middle5_eq_case_1_6_row_1_0_1
  · exact right0Middle5_eq_case_1_6_row_1_0_2
  · exact right0Middle5_eq_case_1_6_row_1_0_3
  · exact right0Middle5_eq_case_1_6_row_1_1_0
  · exact right0Middle5_eq_case_1_6_row_1_1_1
  · exact right0Middle5_eq_case_1_6_row_1_1_2
  · exact right0Middle5_eq_case_1_6_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem right0Middle5_eq_case_1_6 : right0Middle5 1 6 = innerRightZ 5 1 6 * associatorZ 5 1 6 := by
  simpa only [HexagonAtoms516.assocABC_eq,
    HexagonAtoms516.outerABC_eq,
    HexagonAtoms516.assocBAC_eq,
    HexagonAtoms516.innerABC_eq,
    HexagonAtoms516.innerRightABC_eq,
    HexagonAtoms516.inverseACB_eq,
    HexagonAtoms516.innerACB_eq,
    HexagonAtoms516.assocBCA_eq,
    HexagonAtoms516.innerRightBAC_eq,
    HexagonAtoms516.assocCAB_eq,
    HexagonAtoms516.outerLeftABC_eq,
    HexagonRowColumn516.product0_eq,
    HexagonRowColumn516.product1_eq,
    HexagonRowColumn516.product2_eq,
    HexagonRowColumn516.product3_eq,
    HexagonRowColumn516.product4_eq,
    HexagonRowColumn516.product5_eq,
    HexagonRowColumn516.product6_eq,
    HexagonRowColumn516.product7_eq] using right0Middle5_eq_case_1_6_checked

private theorem right1Middle5_eq_case_1_6_row_0_0_0 : (right1Middle5 1 6) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn516.rows_inverseACB HexagonRowColumn516.cols_right0) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_1_6_row_0_0_1 : (right1Middle5 1 6) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn516.rows_inverseACB HexagonRowColumn516.cols_right0) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_1_6_row_0_0_2 : (right1Middle5 1 6) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn516.rows_inverseACB HexagonRowColumn516.cols_right0) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_1_6_row_0_0_3 : (right1Middle5 1 6) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn516.rows_inverseACB HexagonRowColumn516.cols_right0) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_1_6_row_0_1_0 : (right1Middle5 1 6) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn516.rows_inverseACB HexagonRowColumn516.cols_right0) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_1_6_row_0_1_1 : (right1Middle5 1 6) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn516.rows_inverseACB HexagonRowColumn516.cols_right0) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_1_6_row_0_1_2 : (right1Middle5 1 6) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn516.rows_inverseACB HexagonRowColumn516.cols_right0) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_1_6_row_0_1_3 : (right1Middle5 1 6) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn516.rows_inverseACB HexagonRowColumn516.cols_right0) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_1_6_row_1_0_0 : (right1Middle5 1 6) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn516.rows_inverseACB HexagonRowColumn516.cols_right0) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_1_6_row_1_0_1 : (right1Middle5 1 6) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn516.rows_inverseACB HexagonRowColumn516.cols_right0) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_1_6_row_1_0_2 : (right1Middle5 1 6) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn516.rows_inverseACB HexagonRowColumn516.cols_right0) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_1_6_row_1_0_3 : (right1Middle5 1 6) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn516.rows_inverseACB HexagonRowColumn516.cols_right0) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_1_6_row_1_1_0 : (right1Middle5 1 6) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn516.rows_inverseACB HexagonRowColumn516.cols_right0) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_1_6_row_1_1_1 : (right1Middle5 1 6) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn516.rows_inverseACB HexagonRowColumn516.cols_right0) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_1_6_row_1_1_2 : (right1Middle5 1 6) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn516.rows_inverseACB HexagonRowColumn516.cols_right0) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_1_6_row_1_1_3 : (right1Middle5 1 6) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn516.rows_inverseACB HexagonRowColumn516.cols_right0) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_1_6_checked : right1Middle5 1 6 = rowColumnMul HexagonRowColumn516.rows_inverseACB HexagonRowColumn516.cols_right0 := by
  funext r
  fin_cases r
  · exact right1Middle5_eq_case_1_6_row_0_0_0
  · exact right1Middle5_eq_case_1_6_row_0_0_1
  · exact right1Middle5_eq_case_1_6_row_0_0_2
  · exact right1Middle5_eq_case_1_6_row_0_0_3
  · exact right1Middle5_eq_case_1_6_row_0_1_0
  · exact right1Middle5_eq_case_1_6_row_0_1_1
  · exact right1Middle5_eq_case_1_6_row_0_1_2
  · exact right1Middle5_eq_case_1_6_row_0_1_3
  · exact right1Middle5_eq_case_1_6_row_1_0_0
  · exact right1Middle5_eq_case_1_6_row_1_0_1
  · exact right1Middle5_eq_case_1_6_row_1_0_2
  · exact right1Middle5_eq_case_1_6_row_1_0_3
  · exact right1Middle5_eq_case_1_6_row_1_1_0
  · exact right1Middle5_eq_case_1_6_row_1_1_1
  · exact right1Middle5_eq_case_1_6_row_1_1_2
  · exact right1Middle5_eq_case_1_6_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem right1Middle5_eq_case_1_6 : right1Middle5 1 6 = associatorInverseZ 5 6 1 * right0Middle5 1 6 := by
  simpa only [HexagonAtoms516.assocABC_eq,
    HexagonAtoms516.outerABC_eq,
    HexagonAtoms516.assocBAC_eq,
    HexagonAtoms516.innerABC_eq,
    HexagonAtoms516.innerRightABC_eq,
    HexagonAtoms516.inverseACB_eq,
    HexagonAtoms516.innerACB_eq,
    HexagonAtoms516.assocBCA_eq,
    HexagonAtoms516.innerRightBAC_eq,
    HexagonAtoms516.assocCAB_eq,
    HexagonAtoms516.outerLeftABC_eq,
    HexagonRowColumn516.product0_eq,
    HexagonRowColumn516.product1_eq,
    HexagonRowColumn516.product2_eq,
    HexagonRowColumn516.product3_eq,
    HexagonRowColumn516.product4_eq,
    HexagonRowColumn516.product5_eq,
    HexagonRowColumn516.product6_eq,
    HexagonRowColumn516.product7_eq] using right1Middle5_eq_case_1_6_checked

private theorem right2Middle5_eq_case_1_6_row_0_0_0 : (right2Middle5 1 6) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (right1Middle5 1 6) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_1_6_row_0_0_1 : (right2Middle5 1 6) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (right1Middle5 1 6) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_1_6_row_0_0_2 : (right2Middle5 1 6) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (right1Middle5 1 6) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_1_6_row_0_0_3 : (right2Middle5 1 6) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (right1Middle5 1 6) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_1_6_row_0_1_0 : (right2Middle5 1 6) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (right1Middle5 1 6) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_1_6_row_0_1_1 : (right2Middle5 1 6) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (right1Middle5 1 6) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_1_6_row_0_1_2 : (right2Middle5 1 6) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (right1Middle5 1 6) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_1_6_row_0_1_3 : (right2Middle5 1 6) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (right1Middle5 1 6) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_1_6_row_1_0_0 : (right2Middle5 1 6) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (right1Middle5 1 6) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_1_6_row_1_0_1 : (right2Middle5 1 6) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (right1Middle5 1 6) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_1_6_row_1_0_2 : (right2Middle5 1 6) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (right1Middle5 1 6) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_1_6_row_1_0_3 : (right2Middle5 1 6) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (right1Middle5 1 6) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_1_6_row_1_1_0 : (right2Middle5 1 6) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (right1Middle5 1 6) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_1_6_row_1_1_1 : (right2Middle5 1 6) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (right1Middle5 1 6) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_1_6_row_1_1_2 : (right2Middle5 1 6) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (right1Middle5 1 6) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_1_6_row_1_1_3 : (right2Middle5 1 6) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (right1Middle5 1 6) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_1_6_checked : right2Middle5 1 6 = right1Middle5 1 6 := by
  funext r
  fin_cases r
  · exact right2Middle5_eq_case_1_6_row_0_0_0
  · exact right2Middle5_eq_case_1_6_row_0_0_1
  · exact right2Middle5_eq_case_1_6_row_0_0_2
  · exact right2Middle5_eq_case_1_6_row_0_0_3
  · exact right2Middle5_eq_case_1_6_row_0_1_0
  · exact right2Middle5_eq_case_1_6_row_0_1_1
  · exact right2Middle5_eq_case_1_6_row_0_1_2
  · exact right2Middle5_eq_case_1_6_row_0_1_3
  · exact right2Middle5_eq_case_1_6_row_1_0_0
  · exact right2Middle5_eq_case_1_6_row_1_0_1
  · exact right2Middle5_eq_case_1_6_row_1_0_2
  · exact right2Middle5_eq_case_1_6_row_1_0_3
  · exact right2Middle5_eq_case_1_6_row_1_1_0
  · exact right2Middle5_eq_case_1_6_row_1_1_1
  · exact right2Middle5_eq_case_1_6_row_1_1_2
  · exact right2Middle5_eq_case_1_6_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem right2Middle5_eq_case_1_6 : right2Middle5 1 6 = innerLeftZ 5 6 1 * right1Middle5 1 6 := by
  simpa only [HexagonAtoms516.assocABC_eq,
    HexagonAtoms516.outerABC_eq,
    HexagonAtoms516.assocBAC_eq,
    HexagonAtoms516.innerABC_eq,
    HexagonAtoms516.innerRightABC_eq,
    HexagonAtoms516.inverseACB_eq,
    HexagonAtoms516.innerACB_eq,
    HexagonAtoms516.assocBCA_eq,
    HexagonAtoms516.innerRightBAC_eq,
    HexagonAtoms516.assocCAB_eq,
    HexagonAtoms516.outerLeftABC_eq,
    HexagonRowColumn516.product0_eq,
    HexagonRowColumn516.product1_eq,
    HexagonRowColumn516.product2_eq,
    HexagonRowColumn516.product3_eq,
    HexagonRowColumn516.product4_eq,
    HexagonRowColumn516.product5_eq,
    HexagonRowColumn516.product6_eq,
    HexagonRowColumn516.product7_eq] using right2Middle5_eq_case_1_6_checked

private theorem leftFinal5_case_1_6_row_0_0_0 : (((-1 : ℤ) ^ (leftScaleBit 5 1 6).val * positiveScale (leftScaleExponent 5 1 6)) •
      (rowColumnMul HexagonRowColumn516.rows_assocBCA HexagonRowColumn516.cols_left0)) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 5 1 6) • (left1Middle5 1 6)) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_1_6_row_0_0_1 : (((-1 : ℤ) ^ (leftScaleBit 5 1 6).val * positiveScale (leftScaleExponent 5 1 6)) •
      (rowColumnMul HexagonRowColumn516.rows_assocBCA HexagonRowColumn516.cols_left0)) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 5 1 6) • (left1Middle5 1 6)) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_1_6_row_0_0_2 : (((-1 : ℤ) ^ (leftScaleBit 5 1 6).val * positiveScale (leftScaleExponent 5 1 6)) •
      (rowColumnMul HexagonRowColumn516.rows_assocBCA HexagonRowColumn516.cols_left0)) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 5 1 6) • (left1Middle5 1 6)) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_1_6_row_0_0_3 : (((-1 : ℤ) ^ (leftScaleBit 5 1 6).val * positiveScale (leftScaleExponent 5 1 6)) •
      (rowColumnMul HexagonRowColumn516.rows_assocBCA HexagonRowColumn516.cols_left0)) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 5 1 6) • (left1Middle5 1 6)) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_1_6_row_0_1_0 : (((-1 : ℤ) ^ (leftScaleBit 5 1 6).val * positiveScale (leftScaleExponent 5 1 6)) •
      (rowColumnMul HexagonRowColumn516.rows_assocBCA HexagonRowColumn516.cols_left0)) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 5 1 6) • (left1Middle5 1 6)) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_1_6_row_0_1_1 : (((-1 : ℤ) ^ (leftScaleBit 5 1 6).val * positiveScale (leftScaleExponent 5 1 6)) •
      (rowColumnMul HexagonRowColumn516.rows_assocBCA HexagonRowColumn516.cols_left0)) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 5 1 6) • (left1Middle5 1 6)) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_1_6_row_0_1_2 : (((-1 : ℤ) ^ (leftScaleBit 5 1 6).val * positiveScale (leftScaleExponent 5 1 6)) •
      (rowColumnMul HexagonRowColumn516.rows_assocBCA HexagonRowColumn516.cols_left0)) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 5 1 6) • (left1Middle5 1 6)) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_1_6_row_0_1_3 : (((-1 : ℤ) ^ (leftScaleBit 5 1 6).val * positiveScale (leftScaleExponent 5 1 6)) •
      (rowColumnMul HexagonRowColumn516.rows_assocBCA HexagonRowColumn516.cols_left0)) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 5 1 6) • (left1Middle5 1 6)) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_1_6_row_1_0_0 : (((-1 : ℤ) ^ (leftScaleBit 5 1 6).val * positiveScale (leftScaleExponent 5 1 6)) •
      (rowColumnMul HexagonRowColumn516.rows_assocBCA HexagonRowColumn516.cols_left0)) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 5 1 6) • (left1Middle5 1 6)) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_1_6_row_1_0_1 : (((-1 : ℤ) ^ (leftScaleBit 5 1 6).val * positiveScale (leftScaleExponent 5 1 6)) •
      (rowColumnMul HexagonRowColumn516.rows_assocBCA HexagonRowColumn516.cols_left0)) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 5 1 6) • (left1Middle5 1 6)) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_1_6_row_1_0_2 : (((-1 : ℤ) ^ (leftScaleBit 5 1 6).val * positiveScale (leftScaleExponent 5 1 6)) •
      (rowColumnMul HexagonRowColumn516.rows_assocBCA HexagonRowColumn516.cols_left0)) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 5 1 6) • (left1Middle5 1 6)) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_1_6_row_1_0_3 : (((-1 : ℤ) ^ (leftScaleBit 5 1 6).val * positiveScale (leftScaleExponent 5 1 6)) •
      (rowColumnMul HexagonRowColumn516.rows_assocBCA HexagonRowColumn516.cols_left0)) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 5 1 6) • (left1Middle5 1 6)) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_1_6_row_1_1_0 : (((-1 : ℤ) ^ (leftScaleBit 5 1 6).val * positiveScale (leftScaleExponent 5 1 6)) •
      (rowColumnMul HexagonRowColumn516.rows_assocBCA HexagonRowColumn516.cols_left0)) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 5 1 6) • (left1Middle5 1 6)) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_1_6_row_1_1_1 : (((-1 : ℤ) ^ (leftScaleBit 5 1 6).val * positiveScale (leftScaleExponent 5 1 6)) •
      (rowColumnMul HexagonRowColumn516.rows_assocBCA HexagonRowColumn516.cols_left0)) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 5 1 6) • (left1Middle5 1 6)) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_1_6_row_1_1_2 : (((-1 : ℤ) ^ (leftScaleBit 5 1 6).val * positiveScale (leftScaleExponent 5 1 6)) •
      (rowColumnMul HexagonRowColumn516.rows_assocBCA HexagonRowColumn516.cols_left0)) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 5 1 6) • (left1Middle5 1 6)) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_1_6_row_1_1_3 : (((-1 : ℤ) ^ (leftScaleBit 5 1 6).val * positiveScale (leftScaleExponent 5 1 6)) •
      (rowColumnMul HexagonRowColumn516.rows_assocBCA HexagonRowColumn516.cols_left0)) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 5 1 6) • (left1Middle5 1 6)) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_1_6_checked : ((-1 : ℤ) ^ (leftScaleBit 5 1 6).val * positiveScale (leftScaleExponent 5 1 6)) •
      (rowColumnMul HexagonRowColumn516.rows_assocBCA HexagonRowColumn516.cols_left0) = negativeScale (leftScaleExponent 5 1 6) • (left1Middle5 1 6) := by
  funext r
  fin_cases r
  · exact leftFinal5_case_1_6_row_0_0_0
  · exact leftFinal5_case_1_6_row_0_0_1
  · exact leftFinal5_case_1_6_row_0_0_2
  · exact leftFinal5_case_1_6_row_0_0_3
  · exact leftFinal5_case_1_6_row_0_1_0
  · exact leftFinal5_case_1_6_row_0_1_1
  · exact leftFinal5_case_1_6_row_0_1_2
  · exact leftFinal5_case_1_6_row_0_1_3
  · exact leftFinal5_case_1_6_row_1_0_0
  · exact leftFinal5_case_1_6_row_1_0_1
  · exact leftFinal5_case_1_6_row_1_0_2
  · exact leftFinal5_case_1_6_row_1_0_3
  · exact leftFinal5_case_1_6_row_1_1_0
  · exact leftFinal5_case_1_6_row_1_1_1
  · exact leftFinal5_case_1_6_row_1_1_2
  · exact leftFinal5_case_1_6_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem leftFinal5_case_1_6 : ((-1 : ℤ) ^ (leftScaleBit 5 1 6).val * positiveScale (leftScaleExponent 5 1 6)) •
      (associatorZ 1 6 5 * left0Middle5 1 6) = negativeScale (leftScaleExponent 5 1 6) • (innerRightZ 1 5 6 * left1Middle5 1 6) := by
  simpa only [HexagonAtoms516.assocABC_eq,
    HexagonAtoms516.outerABC_eq,
    HexagonAtoms516.assocBAC_eq,
    HexagonAtoms516.innerABC_eq,
    HexagonAtoms516.innerRightABC_eq,
    HexagonAtoms516.inverseACB_eq,
    HexagonAtoms516.innerACB_eq,
    HexagonAtoms516.assocBCA_eq,
    HexagonAtoms516.innerRightBAC_eq,
    HexagonAtoms516.assocCAB_eq,
    HexagonAtoms516.outerLeftABC_eq,
    HexagonRowColumn516.product0_eq,
    HexagonRowColumn516.product1_eq,
    HexagonRowColumn516.product2_eq,
    HexagonRowColumn516.product3_eq,
    HexagonRowColumn516.product4_eq,
    HexagonRowColumn516.product5_eq,
    HexagonRowColumn516.product6_eq,
    HexagonRowColumn516.product7_eq] using leftFinal5_case_1_6_checked

private theorem rightFinal5_case_1_6_row_0_0_0 : (((-1 : ℤ) ^ (rightScaleBit 5 1 6).val * positiveScale (rightScaleExponent 5 1 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 6 1 : ℤ)) • HexagonAtoms516.outerLeftABC) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 5 1 6) • (rowColumnMul HexagonRowColumn516.rows_assocCAB HexagonRowColumn516.cols_right2)) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_1_6_row_0_0_1 : (((-1 : ℤ) ^ (rightScaleBit 5 1 6).val * positiveScale (rightScaleExponent 5 1 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 6 1 : ℤ)) • HexagonAtoms516.outerLeftABC) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 5 1 6) • (rowColumnMul HexagonRowColumn516.rows_assocCAB HexagonRowColumn516.cols_right2)) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_1_6_row_0_0_2 : (((-1 : ℤ) ^ (rightScaleBit 5 1 6).val * positiveScale (rightScaleExponent 5 1 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 6 1 : ℤ)) • HexagonAtoms516.outerLeftABC) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 5 1 6) • (rowColumnMul HexagonRowColumn516.rows_assocCAB HexagonRowColumn516.cols_right2)) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_1_6_row_0_0_3 : (((-1 : ℤ) ^ (rightScaleBit 5 1 6).val * positiveScale (rightScaleExponent 5 1 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 6 1 : ℤ)) • HexagonAtoms516.outerLeftABC) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 5 1 6) • (rowColumnMul HexagonRowColumn516.rows_assocCAB HexagonRowColumn516.cols_right2)) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_1_6_row_0_1_0 : (((-1 : ℤ) ^ (rightScaleBit 5 1 6).val * positiveScale (rightScaleExponent 5 1 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 6 1 : ℤ)) • HexagonAtoms516.outerLeftABC) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 5 1 6) • (rowColumnMul HexagonRowColumn516.rows_assocCAB HexagonRowColumn516.cols_right2)) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_1_6_row_0_1_1 : (((-1 : ℤ) ^ (rightScaleBit 5 1 6).val * positiveScale (rightScaleExponent 5 1 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 6 1 : ℤ)) • HexagonAtoms516.outerLeftABC) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 5 1 6) • (rowColumnMul HexagonRowColumn516.rows_assocCAB HexagonRowColumn516.cols_right2)) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_1_6_row_0_1_2 : (((-1 : ℤ) ^ (rightScaleBit 5 1 6).val * positiveScale (rightScaleExponent 5 1 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 6 1 : ℤ)) • HexagonAtoms516.outerLeftABC) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 5 1 6) • (rowColumnMul HexagonRowColumn516.rows_assocCAB HexagonRowColumn516.cols_right2)) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_1_6_row_0_1_3 : (((-1 : ℤ) ^ (rightScaleBit 5 1 6).val * positiveScale (rightScaleExponent 5 1 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 6 1 : ℤ)) • HexagonAtoms516.outerLeftABC) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 5 1 6) • (rowColumnMul HexagonRowColumn516.rows_assocCAB HexagonRowColumn516.cols_right2)) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_1_6_row_1_0_0 : (((-1 : ℤ) ^ (rightScaleBit 5 1 6).val * positiveScale (rightScaleExponent 5 1 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 6 1 : ℤ)) • HexagonAtoms516.outerLeftABC) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 5 1 6) • (rowColumnMul HexagonRowColumn516.rows_assocCAB HexagonRowColumn516.cols_right2)) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_1_6_row_1_0_1 : (((-1 : ℤ) ^ (rightScaleBit 5 1 6).val * positiveScale (rightScaleExponent 5 1 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 6 1 : ℤ)) • HexagonAtoms516.outerLeftABC) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 5 1 6) • (rowColumnMul HexagonRowColumn516.rows_assocCAB HexagonRowColumn516.cols_right2)) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_1_6_row_1_0_2 : (((-1 : ℤ) ^ (rightScaleBit 5 1 6).val * positiveScale (rightScaleExponent 5 1 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 6 1 : ℤ)) • HexagonAtoms516.outerLeftABC) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 5 1 6) • (rowColumnMul HexagonRowColumn516.rows_assocCAB HexagonRowColumn516.cols_right2)) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_1_6_row_1_0_3 : (((-1 : ℤ) ^ (rightScaleBit 5 1 6).val * positiveScale (rightScaleExponent 5 1 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 6 1 : ℤ)) • HexagonAtoms516.outerLeftABC) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 5 1 6) • (rowColumnMul HexagonRowColumn516.rows_assocCAB HexagonRowColumn516.cols_right2)) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_1_6_row_1_1_0 : (((-1 : ℤ) ^ (rightScaleBit 5 1 6).val * positiveScale (rightScaleExponent 5 1 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 6 1 : ℤ)) • HexagonAtoms516.outerLeftABC) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 5 1 6) • (rowColumnMul HexagonRowColumn516.rows_assocCAB HexagonRowColumn516.cols_right2)) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_1_6_row_1_1_1 : (((-1 : ℤ) ^ (rightScaleBit 5 1 6).val * positiveScale (rightScaleExponent 5 1 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 6 1 : ℤ)) • HexagonAtoms516.outerLeftABC) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 5 1 6) • (rowColumnMul HexagonRowColumn516.rows_assocCAB HexagonRowColumn516.cols_right2)) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_1_6_row_1_1_2 : (((-1 : ℤ) ^ (rightScaleBit 5 1 6).val * positiveScale (rightScaleExponent 5 1 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 6 1 : ℤ)) • HexagonAtoms516.outerLeftABC) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 5 1 6) • (rowColumnMul HexagonRowColumn516.rows_assocCAB HexagonRowColumn516.cols_right2)) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_1_6_row_1_1_3 : (((-1 : ℤ) ^ (rightScaleBit 5 1 6).val * positiveScale (rightScaleExponent 5 1 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 6 1 : ℤ)) • HexagonAtoms516.outerLeftABC) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 5 1 6) • (rowColumnMul HexagonRowColumn516.rows_assocCAB HexagonRowColumn516.cols_right2)) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_1_6_checked : ((-1 : ℤ) ^ (rightScaleBit 5 1 6).val * positiveScale (rightScaleExponent 5 1 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 6 1 : ℤ)) • HexagonAtoms516.outerLeftABC = negativeScale (rightScaleExponent 5 1 6) • (rowColumnMul HexagonRowColumn516.rows_assocCAB HexagonRowColumn516.cols_right2) := by
  funext r
  fin_cases r
  · exact rightFinal5_case_1_6_row_0_0_0
  · exact rightFinal5_case_1_6_row_0_0_1
  · exact rightFinal5_case_1_6_row_0_0_2
  · exact rightFinal5_case_1_6_row_0_0_3
  · exact rightFinal5_case_1_6_row_0_1_0
  · exact rightFinal5_case_1_6_row_0_1_1
  · exact rightFinal5_case_1_6_row_0_1_2
  · exact rightFinal5_case_1_6_row_0_1_3
  · exact rightFinal5_case_1_6_row_1_0_0
  · exact rightFinal5_case_1_6_row_1_0_1
  · exact rightFinal5_case_1_6_row_1_0_2
  · exact rightFinal5_case_1_6_row_1_0_3
  · exact rightFinal5_case_1_6_row_1_1_0
  · exact rightFinal5_case_1_6_row_1_1_1
  · exact rightFinal5_case_1_6_row_1_1_2
  · exact rightFinal5_case_1_6_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem rightFinal5_case_1_6 : ((-1 : ℤ) ^ (rightScaleBit 5 1 6).val * positiveScale (rightScaleExponent 5 1 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 6 1 : ℤ)) • outerLeftZ 5 1 6 = negativeScale (rightScaleExponent 5 1 6) • (associatorZ 6 5 1 * right2Middle5 1 6) := by
  simpa only [HexagonAtoms516.assocABC_eq,
    HexagonAtoms516.outerABC_eq,
    HexagonAtoms516.assocBAC_eq,
    HexagonAtoms516.innerABC_eq,
    HexagonAtoms516.innerRightABC_eq,
    HexagonAtoms516.inverseACB_eq,
    HexagonAtoms516.innerACB_eq,
    HexagonAtoms516.assocBCA_eq,
    HexagonAtoms516.innerRightBAC_eq,
    HexagonAtoms516.assocCAB_eq,
    HexagonAtoms516.outerLeftABC_eq,
    HexagonRowColumn516.product0_eq,
    HexagonRowColumn516.product1_eq,
    HexagonRowColumn516.product2_eq,
    HexagonRowColumn516.product3_eq,
    HexagonRowColumn516.product4_eq,
    HexagonRowColumn516.product5_eq,
    HexagonRowColumn516.product6_eq,
    HexagonRowColumn516.product7_eq] using rightFinal5_case_1_6_checked

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonCases5
