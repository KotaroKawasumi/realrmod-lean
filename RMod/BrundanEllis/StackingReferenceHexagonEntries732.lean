import RMod.BrundanEllis.StackingReferenceHexagonMiddle7
import RMod.BrundanEllis.StackingReferenceSparseMatrixCheck
import RMod.BrundanEllis.StackingReferenceHexagonAtoms732
import RMod.BrundanEllis.StackingReferenceHexagonRowColumn732

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

private theorem left0Middle7_eq_case_3_2_row_0_0_0 : (left0Middle7 3 2) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn732.rows_outerABC HexagonRowColumn732.cols_assocABC) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle7_eq_case_3_2_row_0_0_1 : (left0Middle7 3 2) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn732.rows_outerABC HexagonRowColumn732.cols_assocABC) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle7_eq_case_3_2_row_0_0_2 : (left0Middle7 3 2) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn732.rows_outerABC HexagonRowColumn732.cols_assocABC) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle7_eq_case_3_2_row_0_0_3 : (left0Middle7 3 2) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn732.rows_outerABC HexagonRowColumn732.cols_assocABC) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle7_eq_case_3_2_row_0_1_0 : (left0Middle7 3 2) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn732.rows_outerABC HexagonRowColumn732.cols_assocABC) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle7_eq_case_3_2_row_0_1_1 : (left0Middle7 3 2) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn732.rows_outerABC HexagonRowColumn732.cols_assocABC) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle7_eq_case_3_2_row_0_1_2 : (left0Middle7 3 2) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn732.rows_outerABC HexagonRowColumn732.cols_assocABC) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle7_eq_case_3_2_row_0_1_3 : (left0Middle7 3 2) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn732.rows_outerABC HexagonRowColumn732.cols_assocABC) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle7_eq_case_3_2_row_1_0_0 : (left0Middle7 3 2) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn732.rows_outerABC HexagonRowColumn732.cols_assocABC) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle7_eq_case_3_2_row_1_0_1 : (left0Middle7 3 2) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn732.rows_outerABC HexagonRowColumn732.cols_assocABC) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle7_eq_case_3_2_row_1_0_2 : (left0Middle7 3 2) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn732.rows_outerABC HexagonRowColumn732.cols_assocABC) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle7_eq_case_3_2_row_1_0_3 : (left0Middle7 3 2) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn732.rows_outerABC HexagonRowColumn732.cols_assocABC) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle7_eq_case_3_2_row_1_1_0 : (left0Middle7 3 2) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn732.rows_outerABC HexagonRowColumn732.cols_assocABC) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle7_eq_case_3_2_row_1_1_1 : (left0Middle7 3 2) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn732.rows_outerABC HexagonRowColumn732.cols_assocABC) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle7_eq_case_3_2_row_1_1_2 : (left0Middle7 3 2) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn732.rows_outerABC HexagonRowColumn732.cols_assocABC) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle7_eq_case_3_2_row_1_1_3 : (left0Middle7 3 2) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn732.rows_outerABC HexagonRowColumn732.cols_assocABC) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle7_eq_case_3_2_checked : left0Middle7 3 2 = rowColumnMul HexagonRowColumn732.rows_outerABC HexagonRowColumn732.cols_assocABC := by
  funext r
  fin_cases r
  · exact left0Middle7_eq_case_3_2_row_0_0_0
  · exact left0Middle7_eq_case_3_2_row_0_0_1
  · exact left0Middle7_eq_case_3_2_row_0_0_2
  · exact left0Middle7_eq_case_3_2_row_0_0_3
  · exact left0Middle7_eq_case_3_2_row_0_1_0
  · exact left0Middle7_eq_case_3_2_row_0_1_1
  · exact left0Middle7_eq_case_3_2_row_0_1_2
  · exact left0Middle7_eq_case_3_2_row_0_1_3
  · exact left0Middle7_eq_case_3_2_row_1_0_0
  · exact left0Middle7_eq_case_3_2_row_1_0_1
  · exact left0Middle7_eq_case_3_2_row_1_0_2
  · exact left0Middle7_eq_case_3_2_row_1_0_3
  · exact left0Middle7_eq_case_3_2_row_1_1_0
  · exact left0Middle7_eq_case_3_2_row_1_1_1
  · exact left0Middle7_eq_case_3_2_row_1_1_2
  · exact left0Middle7_eq_case_3_2_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem left0Middle7_eq_case_3_2 : left0Middle7 3 2 = outerRightZ 7 3 2 * associatorZ 7 3 2 := by
  simpa only [HexagonAtoms732.assocABC_eq,
    HexagonAtoms732.outerABC_eq,
    HexagonAtoms732.assocBAC_eq,
    HexagonAtoms732.innerABC_eq,
    HexagonAtoms732.innerRightABC_eq,
    HexagonAtoms732.inverseACB_eq,
    HexagonAtoms732.innerACB_eq,
    HexagonAtoms732.assocBCA_eq,
    HexagonAtoms732.innerRightBAC_eq,
    HexagonAtoms732.assocCAB_eq,
    HexagonAtoms732.outerLeftABC_eq,
    HexagonRowColumn732.product0_eq,
    HexagonRowColumn732.product1_eq,
    HexagonRowColumn732.product2_eq,
    HexagonRowColumn732.product3_eq,
    HexagonRowColumn732.product4_eq,
    HexagonRowColumn732.product5_eq,
    HexagonRowColumn732.product6_eq,
    HexagonRowColumn732.product7_eq] using left0Middle7_eq_case_3_2_checked

private theorem left1Middle7_eq_case_3_2_row_0_0_0 : (left1Middle7 3 2) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms732.assocBAC) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle7_eq_case_3_2_row_0_0_1 : (left1Middle7 3 2) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms732.assocBAC) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle7_eq_case_3_2_row_0_0_2 : (left1Middle7 3 2) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms732.assocBAC) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle7_eq_case_3_2_row_0_0_3 : (left1Middle7 3 2) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms732.assocBAC) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle7_eq_case_3_2_row_0_1_0 : (left1Middle7 3 2) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms732.assocBAC) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle7_eq_case_3_2_row_0_1_1 : (left1Middle7 3 2) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms732.assocBAC) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle7_eq_case_3_2_row_0_1_2 : (left1Middle7 3 2) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms732.assocBAC) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle7_eq_case_3_2_row_0_1_3 : (left1Middle7 3 2) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms732.assocBAC) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle7_eq_case_3_2_row_1_0_0 : (left1Middle7 3 2) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms732.assocBAC) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle7_eq_case_3_2_row_1_0_1 : (left1Middle7 3 2) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms732.assocBAC) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle7_eq_case_3_2_row_1_0_2 : (left1Middle7 3 2) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms732.assocBAC) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle7_eq_case_3_2_row_1_0_3 : (left1Middle7 3 2) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms732.assocBAC) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle7_eq_case_3_2_row_1_1_0 : (left1Middle7 3 2) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms732.assocBAC) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle7_eq_case_3_2_row_1_1_1 : (left1Middle7 3 2) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms732.assocBAC) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle7_eq_case_3_2_row_1_1_2 : (left1Middle7 3 2) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms732.assocBAC) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle7_eq_case_3_2_row_1_1_3 : (left1Middle7 3 2) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms732.assocBAC) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle7_eq_case_3_2_checked : left1Middle7 3 2 = HexagonAtoms732.assocBAC := by
  funext r
  fin_cases r
  · exact left1Middle7_eq_case_3_2_row_0_0_0
  · exact left1Middle7_eq_case_3_2_row_0_0_1
  · exact left1Middle7_eq_case_3_2_row_0_0_2
  · exact left1Middle7_eq_case_3_2_row_0_0_3
  · exact left1Middle7_eq_case_3_2_row_0_1_0
  · exact left1Middle7_eq_case_3_2_row_0_1_1
  · exact left1Middle7_eq_case_3_2_row_0_1_2
  · exact left1Middle7_eq_case_3_2_row_0_1_3
  · exact left1Middle7_eq_case_3_2_row_1_0_0
  · exact left1Middle7_eq_case_3_2_row_1_0_1
  · exact left1Middle7_eq_case_3_2_row_1_0_2
  · exact left1Middle7_eq_case_3_2_row_1_0_3
  · exact left1Middle7_eq_case_3_2_row_1_1_0
  · exact left1Middle7_eq_case_3_2_row_1_1_1
  · exact left1Middle7_eq_case_3_2_row_1_1_2
  · exact left1Middle7_eq_case_3_2_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem left1Middle7_eq_case_3_2 : left1Middle7 3 2 = associatorZ 3 7 2 * innerLeftZ 7 3 2 := by
  simpa only [HexagonAtoms732.assocABC_eq,
    HexagonAtoms732.outerABC_eq,
    HexagonAtoms732.assocBAC_eq,
    HexagonAtoms732.innerABC_eq,
    HexagonAtoms732.innerRightABC_eq,
    HexagonAtoms732.inverseACB_eq,
    HexagonAtoms732.innerACB_eq,
    HexagonAtoms732.assocBCA_eq,
    HexagonAtoms732.innerRightBAC_eq,
    HexagonAtoms732.assocCAB_eq,
    HexagonAtoms732.outerLeftABC_eq,
    HexagonRowColumn732.product0_eq,
    HexagonRowColumn732.product1_eq,
    HexagonRowColumn732.product2_eq,
    HexagonRowColumn732.product3_eq,
    HexagonRowColumn732.product4_eq,
    HexagonRowColumn732.product5_eq,
    HexagonRowColumn732.product6_eq,
    HexagonRowColumn732.product7_eq] using left1Middle7_eq_case_3_2_checked

private theorem right0Middle7_eq_case_3_2_row_0_0_0 : (right0Middle7 3 2) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms732.assocABC) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle7_eq_case_3_2_row_0_0_1 : (right0Middle7 3 2) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms732.assocABC) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle7_eq_case_3_2_row_0_0_2 : (right0Middle7 3 2) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms732.assocABC) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle7_eq_case_3_2_row_0_0_3 : (right0Middle7 3 2) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms732.assocABC) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle7_eq_case_3_2_row_0_1_0 : (right0Middle7 3 2) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms732.assocABC) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle7_eq_case_3_2_row_0_1_1 : (right0Middle7 3 2) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms732.assocABC) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle7_eq_case_3_2_row_0_1_2 : (right0Middle7 3 2) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms732.assocABC) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle7_eq_case_3_2_row_0_1_3 : (right0Middle7 3 2) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms732.assocABC) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle7_eq_case_3_2_row_1_0_0 : (right0Middle7 3 2) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms732.assocABC) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle7_eq_case_3_2_row_1_0_1 : (right0Middle7 3 2) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms732.assocABC) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle7_eq_case_3_2_row_1_0_2 : (right0Middle7 3 2) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms732.assocABC) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle7_eq_case_3_2_row_1_0_3 : (right0Middle7 3 2) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms732.assocABC) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle7_eq_case_3_2_row_1_1_0 : (right0Middle7 3 2) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms732.assocABC) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle7_eq_case_3_2_row_1_1_1 : (right0Middle7 3 2) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms732.assocABC) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle7_eq_case_3_2_row_1_1_2 : (right0Middle7 3 2) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms732.assocABC) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle7_eq_case_3_2_row_1_1_3 : (right0Middle7 3 2) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms732.assocABC) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle7_eq_case_3_2_checked : right0Middle7 3 2 = HexagonAtoms732.assocABC := by
  funext r
  fin_cases r
  · exact right0Middle7_eq_case_3_2_row_0_0_0
  · exact right0Middle7_eq_case_3_2_row_0_0_1
  · exact right0Middle7_eq_case_3_2_row_0_0_2
  · exact right0Middle7_eq_case_3_2_row_0_0_3
  · exact right0Middle7_eq_case_3_2_row_0_1_0
  · exact right0Middle7_eq_case_3_2_row_0_1_1
  · exact right0Middle7_eq_case_3_2_row_0_1_2
  · exact right0Middle7_eq_case_3_2_row_0_1_3
  · exact right0Middle7_eq_case_3_2_row_1_0_0
  · exact right0Middle7_eq_case_3_2_row_1_0_1
  · exact right0Middle7_eq_case_3_2_row_1_0_2
  · exact right0Middle7_eq_case_3_2_row_1_0_3
  · exact right0Middle7_eq_case_3_2_row_1_1_0
  · exact right0Middle7_eq_case_3_2_row_1_1_1
  · exact right0Middle7_eq_case_3_2_row_1_1_2
  · exact right0Middle7_eq_case_3_2_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem right0Middle7_eq_case_3_2 : right0Middle7 3 2 = innerRightZ 7 3 2 * associatorZ 7 3 2 := by
  simpa only [HexagonAtoms732.assocABC_eq,
    HexagonAtoms732.outerABC_eq,
    HexagonAtoms732.assocBAC_eq,
    HexagonAtoms732.innerABC_eq,
    HexagonAtoms732.innerRightABC_eq,
    HexagonAtoms732.inverseACB_eq,
    HexagonAtoms732.innerACB_eq,
    HexagonAtoms732.assocBCA_eq,
    HexagonAtoms732.innerRightBAC_eq,
    HexagonAtoms732.assocCAB_eq,
    HexagonAtoms732.outerLeftABC_eq,
    HexagonRowColumn732.product0_eq,
    HexagonRowColumn732.product1_eq,
    HexagonRowColumn732.product2_eq,
    HexagonRowColumn732.product3_eq,
    HexagonRowColumn732.product4_eq,
    HexagonRowColumn732.product5_eq,
    HexagonRowColumn732.product6_eq,
    HexagonRowColumn732.product7_eq] using right0Middle7_eq_case_3_2_checked

private theorem right1Middle7_eq_case_3_2_row_0_0_0 : (right1Middle7 3 2) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn732.rows_inverseACB HexagonRowColumn732.cols_right0) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle7_eq_case_3_2_row_0_0_1 : (right1Middle7 3 2) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn732.rows_inverseACB HexagonRowColumn732.cols_right0) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle7_eq_case_3_2_row_0_0_2 : (right1Middle7 3 2) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn732.rows_inverseACB HexagonRowColumn732.cols_right0) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle7_eq_case_3_2_row_0_0_3 : (right1Middle7 3 2) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn732.rows_inverseACB HexagonRowColumn732.cols_right0) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle7_eq_case_3_2_row_0_1_0 : (right1Middle7 3 2) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn732.rows_inverseACB HexagonRowColumn732.cols_right0) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle7_eq_case_3_2_row_0_1_1 : (right1Middle7 3 2) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn732.rows_inverseACB HexagonRowColumn732.cols_right0) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle7_eq_case_3_2_row_0_1_2 : (right1Middle7 3 2) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn732.rows_inverseACB HexagonRowColumn732.cols_right0) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle7_eq_case_3_2_row_0_1_3 : (right1Middle7 3 2) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn732.rows_inverseACB HexagonRowColumn732.cols_right0) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle7_eq_case_3_2_row_1_0_0 : (right1Middle7 3 2) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn732.rows_inverseACB HexagonRowColumn732.cols_right0) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle7_eq_case_3_2_row_1_0_1 : (right1Middle7 3 2) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn732.rows_inverseACB HexagonRowColumn732.cols_right0) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle7_eq_case_3_2_row_1_0_2 : (right1Middle7 3 2) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn732.rows_inverseACB HexagonRowColumn732.cols_right0) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle7_eq_case_3_2_row_1_0_3 : (right1Middle7 3 2) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn732.rows_inverseACB HexagonRowColumn732.cols_right0) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle7_eq_case_3_2_row_1_1_0 : (right1Middle7 3 2) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn732.rows_inverseACB HexagonRowColumn732.cols_right0) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle7_eq_case_3_2_row_1_1_1 : (right1Middle7 3 2) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn732.rows_inverseACB HexagonRowColumn732.cols_right0) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle7_eq_case_3_2_row_1_1_2 : (right1Middle7 3 2) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn732.rows_inverseACB HexagonRowColumn732.cols_right0) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle7_eq_case_3_2_row_1_1_3 : (right1Middle7 3 2) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn732.rows_inverseACB HexagonRowColumn732.cols_right0) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle7_eq_case_3_2_checked : right1Middle7 3 2 = rowColumnMul HexagonRowColumn732.rows_inverseACB HexagonRowColumn732.cols_right0 := by
  funext r
  fin_cases r
  · exact right1Middle7_eq_case_3_2_row_0_0_0
  · exact right1Middle7_eq_case_3_2_row_0_0_1
  · exact right1Middle7_eq_case_3_2_row_0_0_2
  · exact right1Middle7_eq_case_3_2_row_0_0_3
  · exact right1Middle7_eq_case_3_2_row_0_1_0
  · exact right1Middle7_eq_case_3_2_row_0_1_1
  · exact right1Middle7_eq_case_3_2_row_0_1_2
  · exact right1Middle7_eq_case_3_2_row_0_1_3
  · exact right1Middle7_eq_case_3_2_row_1_0_0
  · exact right1Middle7_eq_case_3_2_row_1_0_1
  · exact right1Middle7_eq_case_3_2_row_1_0_2
  · exact right1Middle7_eq_case_3_2_row_1_0_3
  · exact right1Middle7_eq_case_3_2_row_1_1_0
  · exact right1Middle7_eq_case_3_2_row_1_1_1
  · exact right1Middle7_eq_case_3_2_row_1_1_2
  · exact right1Middle7_eq_case_3_2_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem right1Middle7_eq_case_3_2 : right1Middle7 3 2 = associatorInverseZ 7 2 3 * right0Middle7 3 2 := by
  simpa only [HexagonAtoms732.assocABC_eq,
    HexagonAtoms732.outerABC_eq,
    HexagonAtoms732.assocBAC_eq,
    HexagonAtoms732.innerABC_eq,
    HexagonAtoms732.innerRightABC_eq,
    HexagonAtoms732.inverseACB_eq,
    HexagonAtoms732.innerACB_eq,
    HexagonAtoms732.assocBCA_eq,
    HexagonAtoms732.innerRightBAC_eq,
    HexagonAtoms732.assocCAB_eq,
    HexagonAtoms732.outerLeftABC_eq,
    HexagonRowColumn732.product0_eq,
    HexagonRowColumn732.product1_eq,
    HexagonRowColumn732.product2_eq,
    HexagonRowColumn732.product3_eq,
    HexagonRowColumn732.product4_eq,
    HexagonRowColumn732.product5_eq,
    HexagonRowColumn732.product6_eq,
    HexagonRowColumn732.product7_eq] using right1Middle7_eq_case_3_2_checked

private theorem right2Middle7_eq_case_3_2_row_0_0_0 : (right2Middle7 3 2) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (right1Middle7 3 2) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle7_eq_case_3_2_row_0_0_1 : (right2Middle7 3 2) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (right1Middle7 3 2) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle7_eq_case_3_2_row_0_0_2 : (right2Middle7 3 2) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (right1Middle7 3 2) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle7_eq_case_3_2_row_0_0_3 : (right2Middle7 3 2) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (right1Middle7 3 2) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle7_eq_case_3_2_row_0_1_0 : (right2Middle7 3 2) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (right1Middle7 3 2) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle7_eq_case_3_2_row_0_1_1 : (right2Middle7 3 2) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (right1Middle7 3 2) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle7_eq_case_3_2_row_0_1_2 : (right2Middle7 3 2) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (right1Middle7 3 2) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle7_eq_case_3_2_row_0_1_3 : (right2Middle7 3 2) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (right1Middle7 3 2) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle7_eq_case_3_2_row_1_0_0 : (right2Middle7 3 2) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (right1Middle7 3 2) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle7_eq_case_3_2_row_1_0_1 : (right2Middle7 3 2) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (right1Middle7 3 2) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle7_eq_case_3_2_row_1_0_2 : (right2Middle7 3 2) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (right1Middle7 3 2) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle7_eq_case_3_2_row_1_0_3 : (right2Middle7 3 2) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (right1Middle7 3 2) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle7_eq_case_3_2_row_1_1_0 : (right2Middle7 3 2) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (right1Middle7 3 2) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle7_eq_case_3_2_row_1_1_1 : (right2Middle7 3 2) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (right1Middle7 3 2) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle7_eq_case_3_2_row_1_1_2 : (right2Middle7 3 2) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (right1Middle7 3 2) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle7_eq_case_3_2_row_1_1_3 : (right2Middle7 3 2) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (right1Middle7 3 2) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle7_eq_case_3_2_checked : right2Middle7 3 2 = right1Middle7 3 2 := by
  funext r
  fin_cases r
  · exact right2Middle7_eq_case_3_2_row_0_0_0
  · exact right2Middle7_eq_case_3_2_row_0_0_1
  · exact right2Middle7_eq_case_3_2_row_0_0_2
  · exact right2Middle7_eq_case_3_2_row_0_0_3
  · exact right2Middle7_eq_case_3_2_row_0_1_0
  · exact right2Middle7_eq_case_3_2_row_0_1_1
  · exact right2Middle7_eq_case_3_2_row_0_1_2
  · exact right2Middle7_eq_case_3_2_row_0_1_3
  · exact right2Middle7_eq_case_3_2_row_1_0_0
  · exact right2Middle7_eq_case_3_2_row_1_0_1
  · exact right2Middle7_eq_case_3_2_row_1_0_2
  · exact right2Middle7_eq_case_3_2_row_1_0_3
  · exact right2Middle7_eq_case_3_2_row_1_1_0
  · exact right2Middle7_eq_case_3_2_row_1_1_1
  · exact right2Middle7_eq_case_3_2_row_1_1_2
  · exact right2Middle7_eq_case_3_2_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem right2Middle7_eq_case_3_2 : right2Middle7 3 2 = innerLeftZ 7 2 3 * right1Middle7 3 2 := by
  simpa only [HexagonAtoms732.assocABC_eq,
    HexagonAtoms732.outerABC_eq,
    HexagonAtoms732.assocBAC_eq,
    HexagonAtoms732.innerABC_eq,
    HexagonAtoms732.innerRightABC_eq,
    HexagonAtoms732.inverseACB_eq,
    HexagonAtoms732.innerACB_eq,
    HexagonAtoms732.assocBCA_eq,
    HexagonAtoms732.innerRightBAC_eq,
    HexagonAtoms732.assocCAB_eq,
    HexagonAtoms732.outerLeftABC_eq,
    HexagonRowColumn732.product0_eq,
    HexagonRowColumn732.product1_eq,
    HexagonRowColumn732.product2_eq,
    HexagonRowColumn732.product3_eq,
    HexagonRowColumn732.product4_eq,
    HexagonRowColumn732.product5_eq,
    HexagonRowColumn732.product6_eq,
    HexagonRowColumn732.product7_eq] using right2Middle7_eq_case_3_2_checked

private theorem leftFinal7_case_3_2_row_0_0_0 : (((-1 : ℤ) ^ (leftScaleBit 7 3 2).val * positiveScale (leftScaleExponent 7 3 2)) •
      (rowColumnMul HexagonRowColumn732.rows_assocBCA HexagonRowColumn732.cols_left0)) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 7 3 2) • (left1Middle7 3 2)) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal7_case_3_2_row_0_0_1 : (((-1 : ℤ) ^ (leftScaleBit 7 3 2).val * positiveScale (leftScaleExponent 7 3 2)) •
      (rowColumnMul HexagonRowColumn732.rows_assocBCA HexagonRowColumn732.cols_left0)) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 7 3 2) • (left1Middle7 3 2)) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal7_case_3_2_row_0_0_2 : (((-1 : ℤ) ^ (leftScaleBit 7 3 2).val * positiveScale (leftScaleExponent 7 3 2)) •
      (rowColumnMul HexagonRowColumn732.rows_assocBCA HexagonRowColumn732.cols_left0)) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 7 3 2) • (left1Middle7 3 2)) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal7_case_3_2_row_0_0_3 : (((-1 : ℤ) ^ (leftScaleBit 7 3 2).val * positiveScale (leftScaleExponent 7 3 2)) •
      (rowColumnMul HexagonRowColumn732.rows_assocBCA HexagonRowColumn732.cols_left0)) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 7 3 2) • (left1Middle7 3 2)) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal7_case_3_2_row_0_1_0 : (((-1 : ℤ) ^ (leftScaleBit 7 3 2).val * positiveScale (leftScaleExponent 7 3 2)) •
      (rowColumnMul HexagonRowColumn732.rows_assocBCA HexagonRowColumn732.cols_left0)) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 7 3 2) • (left1Middle7 3 2)) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal7_case_3_2_row_0_1_1 : (((-1 : ℤ) ^ (leftScaleBit 7 3 2).val * positiveScale (leftScaleExponent 7 3 2)) •
      (rowColumnMul HexagonRowColumn732.rows_assocBCA HexagonRowColumn732.cols_left0)) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 7 3 2) • (left1Middle7 3 2)) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal7_case_3_2_row_0_1_2 : (((-1 : ℤ) ^ (leftScaleBit 7 3 2).val * positiveScale (leftScaleExponent 7 3 2)) •
      (rowColumnMul HexagonRowColumn732.rows_assocBCA HexagonRowColumn732.cols_left0)) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 7 3 2) • (left1Middle7 3 2)) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal7_case_3_2_row_0_1_3 : (((-1 : ℤ) ^ (leftScaleBit 7 3 2).val * positiveScale (leftScaleExponent 7 3 2)) •
      (rowColumnMul HexagonRowColumn732.rows_assocBCA HexagonRowColumn732.cols_left0)) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 7 3 2) • (left1Middle7 3 2)) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal7_case_3_2_row_1_0_0 : (((-1 : ℤ) ^ (leftScaleBit 7 3 2).val * positiveScale (leftScaleExponent 7 3 2)) •
      (rowColumnMul HexagonRowColumn732.rows_assocBCA HexagonRowColumn732.cols_left0)) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 7 3 2) • (left1Middle7 3 2)) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal7_case_3_2_row_1_0_1 : (((-1 : ℤ) ^ (leftScaleBit 7 3 2).val * positiveScale (leftScaleExponent 7 3 2)) •
      (rowColumnMul HexagonRowColumn732.rows_assocBCA HexagonRowColumn732.cols_left0)) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 7 3 2) • (left1Middle7 3 2)) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal7_case_3_2_row_1_0_2 : (((-1 : ℤ) ^ (leftScaleBit 7 3 2).val * positiveScale (leftScaleExponent 7 3 2)) •
      (rowColumnMul HexagonRowColumn732.rows_assocBCA HexagonRowColumn732.cols_left0)) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 7 3 2) • (left1Middle7 3 2)) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal7_case_3_2_row_1_0_3 : (((-1 : ℤ) ^ (leftScaleBit 7 3 2).val * positiveScale (leftScaleExponent 7 3 2)) •
      (rowColumnMul HexagonRowColumn732.rows_assocBCA HexagonRowColumn732.cols_left0)) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 7 3 2) • (left1Middle7 3 2)) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal7_case_3_2_row_1_1_0 : (((-1 : ℤ) ^ (leftScaleBit 7 3 2).val * positiveScale (leftScaleExponent 7 3 2)) •
      (rowColumnMul HexagonRowColumn732.rows_assocBCA HexagonRowColumn732.cols_left0)) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 7 3 2) • (left1Middle7 3 2)) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal7_case_3_2_row_1_1_1 : (((-1 : ℤ) ^ (leftScaleBit 7 3 2).val * positiveScale (leftScaleExponent 7 3 2)) •
      (rowColumnMul HexagonRowColumn732.rows_assocBCA HexagonRowColumn732.cols_left0)) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 7 3 2) • (left1Middle7 3 2)) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal7_case_3_2_row_1_1_2 : (((-1 : ℤ) ^ (leftScaleBit 7 3 2).val * positiveScale (leftScaleExponent 7 3 2)) •
      (rowColumnMul HexagonRowColumn732.rows_assocBCA HexagonRowColumn732.cols_left0)) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 7 3 2) • (left1Middle7 3 2)) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal7_case_3_2_row_1_1_3 : (((-1 : ℤ) ^ (leftScaleBit 7 3 2).val * positiveScale (leftScaleExponent 7 3 2)) •
      (rowColumnMul HexagonRowColumn732.rows_assocBCA HexagonRowColumn732.cols_left0)) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 7 3 2) • (left1Middle7 3 2)) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal7_case_3_2_checked : ((-1 : ℤ) ^ (leftScaleBit 7 3 2).val * positiveScale (leftScaleExponent 7 3 2)) •
      (rowColumnMul HexagonRowColumn732.rows_assocBCA HexagonRowColumn732.cols_left0) = negativeScale (leftScaleExponent 7 3 2) • (left1Middle7 3 2) := by
  funext r
  fin_cases r
  · exact leftFinal7_case_3_2_row_0_0_0
  · exact leftFinal7_case_3_2_row_0_0_1
  · exact leftFinal7_case_3_2_row_0_0_2
  · exact leftFinal7_case_3_2_row_0_0_3
  · exact leftFinal7_case_3_2_row_0_1_0
  · exact leftFinal7_case_3_2_row_0_1_1
  · exact leftFinal7_case_3_2_row_0_1_2
  · exact leftFinal7_case_3_2_row_0_1_3
  · exact leftFinal7_case_3_2_row_1_0_0
  · exact leftFinal7_case_3_2_row_1_0_1
  · exact leftFinal7_case_3_2_row_1_0_2
  · exact leftFinal7_case_3_2_row_1_0_3
  · exact leftFinal7_case_3_2_row_1_1_0
  · exact leftFinal7_case_3_2_row_1_1_1
  · exact leftFinal7_case_3_2_row_1_1_2
  · exact leftFinal7_case_3_2_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem leftFinal7_case_3_2 : ((-1 : ℤ) ^ (leftScaleBit 7 3 2).val * positiveScale (leftScaleExponent 7 3 2)) •
      (associatorZ 3 2 7 * left0Middle7 3 2) = negativeScale (leftScaleExponent 7 3 2) • (innerRightZ 3 7 2 * left1Middle7 3 2) := by
  simpa only [HexagonAtoms732.assocABC_eq,
    HexagonAtoms732.outerABC_eq,
    HexagonAtoms732.assocBAC_eq,
    HexagonAtoms732.innerABC_eq,
    HexagonAtoms732.innerRightABC_eq,
    HexagonAtoms732.inverseACB_eq,
    HexagonAtoms732.innerACB_eq,
    HexagonAtoms732.assocBCA_eq,
    HexagonAtoms732.innerRightBAC_eq,
    HexagonAtoms732.assocCAB_eq,
    HexagonAtoms732.outerLeftABC_eq,
    HexagonRowColumn732.product0_eq,
    HexagonRowColumn732.product1_eq,
    HexagonRowColumn732.product2_eq,
    HexagonRowColumn732.product3_eq,
    HexagonRowColumn732.product4_eq,
    HexagonRowColumn732.product5_eq,
    HexagonRowColumn732.product6_eq,
    HexagonRowColumn732.product7_eq] using leftFinal7_case_3_2_checked

private theorem rightFinal7_case_3_2_row_0_0_0 : (((-1 : ℤ) ^ (rightScaleBit 7 3 2).val * positiveScale (rightScaleExponent 7 3 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 2 3 : ℤ)) • HexagonAtoms732.outerLeftABC) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 7 3 2) • (rowColumnMul HexagonRowColumn732.rows_assocCAB HexagonRowColumn732.cols_right2)) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal7_case_3_2_row_0_0_1 : (((-1 : ℤ) ^ (rightScaleBit 7 3 2).val * positiveScale (rightScaleExponent 7 3 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 2 3 : ℤ)) • HexagonAtoms732.outerLeftABC) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 7 3 2) • (rowColumnMul HexagonRowColumn732.rows_assocCAB HexagonRowColumn732.cols_right2)) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal7_case_3_2_row_0_0_2 : (((-1 : ℤ) ^ (rightScaleBit 7 3 2).val * positiveScale (rightScaleExponent 7 3 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 2 3 : ℤ)) • HexagonAtoms732.outerLeftABC) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 7 3 2) • (rowColumnMul HexagonRowColumn732.rows_assocCAB HexagonRowColumn732.cols_right2)) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal7_case_3_2_row_0_0_3 : (((-1 : ℤ) ^ (rightScaleBit 7 3 2).val * positiveScale (rightScaleExponent 7 3 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 2 3 : ℤ)) • HexagonAtoms732.outerLeftABC) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 7 3 2) • (rowColumnMul HexagonRowColumn732.rows_assocCAB HexagonRowColumn732.cols_right2)) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal7_case_3_2_row_0_1_0 : (((-1 : ℤ) ^ (rightScaleBit 7 3 2).val * positiveScale (rightScaleExponent 7 3 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 2 3 : ℤ)) • HexagonAtoms732.outerLeftABC) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 7 3 2) • (rowColumnMul HexagonRowColumn732.rows_assocCAB HexagonRowColumn732.cols_right2)) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal7_case_3_2_row_0_1_1 : (((-1 : ℤ) ^ (rightScaleBit 7 3 2).val * positiveScale (rightScaleExponent 7 3 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 2 3 : ℤ)) • HexagonAtoms732.outerLeftABC) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 7 3 2) • (rowColumnMul HexagonRowColumn732.rows_assocCAB HexagonRowColumn732.cols_right2)) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal7_case_3_2_row_0_1_2 : (((-1 : ℤ) ^ (rightScaleBit 7 3 2).val * positiveScale (rightScaleExponent 7 3 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 2 3 : ℤ)) • HexagonAtoms732.outerLeftABC) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 7 3 2) • (rowColumnMul HexagonRowColumn732.rows_assocCAB HexagonRowColumn732.cols_right2)) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal7_case_3_2_row_0_1_3 : (((-1 : ℤ) ^ (rightScaleBit 7 3 2).val * positiveScale (rightScaleExponent 7 3 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 2 3 : ℤ)) • HexagonAtoms732.outerLeftABC) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 7 3 2) • (rowColumnMul HexagonRowColumn732.rows_assocCAB HexagonRowColumn732.cols_right2)) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal7_case_3_2_row_1_0_0 : (((-1 : ℤ) ^ (rightScaleBit 7 3 2).val * positiveScale (rightScaleExponent 7 3 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 2 3 : ℤ)) • HexagonAtoms732.outerLeftABC) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 7 3 2) • (rowColumnMul HexagonRowColumn732.rows_assocCAB HexagonRowColumn732.cols_right2)) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal7_case_3_2_row_1_0_1 : (((-1 : ℤ) ^ (rightScaleBit 7 3 2).val * positiveScale (rightScaleExponent 7 3 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 2 3 : ℤ)) • HexagonAtoms732.outerLeftABC) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 7 3 2) • (rowColumnMul HexagonRowColumn732.rows_assocCAB HexagonRowColumn732.cols_right2)) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal7_case_3_2_row_1_0_2 : (((-1 : ℤ) ^ (rightScaleBit 7 3 2).val * positiveScale (rightScaleExponent 7 3 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 2 3 : ℤ)) • HexagonAtoms732.outerLeftABC) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 7 3 2) • (rowColumnMul HexagonRowColumn732.rows_assocCAB HexagonRowColumn732.cols_right2)) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal7_case_3_2_row_1_0_3 : (((-1 : ℤ) ^ (rightScaleBit 7 3 2).val * positiveScale (rightScaleExponent 7 3 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 2 3 : ℤ)) • HexagonAtoms732.outerLeftABC) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 7 3 2) • (rowColumnMul HexagonRowColumn732.rows_assocCAB HexagonRowColumn732.cols_right2)) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal7_case_3_2_row_1_1_0 : (((-1 : ℤ) ^ (rightScaleBit 7 3 2).val * positiveScale (rightScaleExponent 7 3 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 2 3 : ℤ)) • HexagonAtoms732.outerLeftABC) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 7 3 2) • (rowColumnMul HexagonRowColumn732.rows_assocCAB HexagonRowColumn732.cols_right2)) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal7_case_3_2_row_1_1_1 : (((-1 : ℤ) ^ (rightScaleBit 7 3 2).val * positiveScale (rightScaleExponent 7 3 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 2 3 : ℤ)) • HexagonAtoms732.outerLeftABC) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 7 3 2) • (rowColumnMul HexagonRowColumn732.rows_assocCAB HexagonRowColumn732.cols_right2)) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal7_case_3_2_row_1_1_2 : (((-1 : ℤ) ^ (rightScaleBit 7 3 2).val * positiveScale (rightScaleExponent 7 3 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 2 3 : ℤ)) • HexagonAtoms732.outerLeftABC) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 7 3 2) • (rowColumnMul HexagonRowColumn732.rows_assocCAB HexagonRowColumn732.cols_right2)) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal7_case_3_2_row_1_1_3 : (((-1 : ℤ) ^ (rightScaleBit 7 3 2).val * positiveScale (rightScaleExponent 7 3 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 2 3 : ℤ)) • HexagonAtoms732.outerLeftABC) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 7 3 2) • (rowColumnMul HexagonRowColumn732.rows_assocCAB HexagonRowColumn732.cols_right2)) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal7_case_3_2_checked : ((-1 : ℤ) ^ (rightScaleBit 7 3 2).val * positiveScale (rightScaleExponent 7 3 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 2 3 : ℤ)) • HexagonAtoms732.outerLeftABC = negativeScale (rightScaleExponent 7 3 2) • (rowColumnMul HexagonRowColumn732.rows_assocCAB HexagonRowColumn732.cols_right2) := by
  funext r
  fin_cases r
  · exact rightFinal7_case_3_2_row_0_0_0
  · exact rightFinal7_case_3_2_row_0_0_1
  · exact rightFinal7_case_3_2_row_0_0_2
  · exact rightFinal7_case_3_2_row_0_0_3
  · exact rightFinal7_case_3_2_row_0_1_0
  · exact rightFinal7_case_3_2_row_0_1_1
  · exact rightFinal7_case_3_2_row_0_1_2
  · exact rightFinal7_case_3_2_row_0_1_3
  · exact rightFinal7_case_3_2_row_1_0_0
  · exact rightFinal7_case_3_2_row_1_0_1
  · exact rightFinal7_case_3_2_row_1_0_2
  · exact rightFinal7_case_3_2_row_1_0_3
  · exact rightFinal7_case_3_2_row_1_1_0
  · exact rightFinal7_case_3_2_row_1_1_1
  · exact rightFinal7_case_3_2_row_1_1_2
  · exact rightFinal7_case_3_2_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem rightFinal7_case_3_2 : ((-1 : ℤ) ^ (rightScaleBit 7 3 2).val * positiveScale (rightScaleExponent 7 3 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 2 3 : ℤ)) • outerLeftZ 7 3 2 = negativeScale (rightScaleExponent 7 3 2) • (associatorZ 2 7 3 * right2Middle7 3 2) := by
  simpa only [HexagonAtoms732.assocABC_eq,
    HexagonAtoms732.outerABC_eq,
    HexagonAtoms732.assocBAC_eq,
    HexagonAtoms732.innerABC_eq,
    HexagonAtoms732.innerRightABC_eq,
    HexagonAtoms732.inverseACB_eq,
    HexagonAtoms732.innerACB_eq,
    HexagonAtoms732.assocBCA_eq,
    HexagonAtoms732.innerRightBAC_eq,
    HexagonAtoms732.assocCAB_eq,
    HexagonAtoms732.outerLeftABC_eq,
    HexagonRowColumn732.product0_eq,
    HexagonRowColumn732.product1_eq,
    HexagonRowColumn732.product2_eq,
    HexagonRowColumn732.product3_eq,
    HexagonRowColumn732.product4_eq,
    HexagonRowColumn732.product5_eq,
    HexagonRowColumn732.product6_eq,
    HexagonRowColumn732.product7_eq] using rightFinal7_case_3_2_checked

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonCases7
