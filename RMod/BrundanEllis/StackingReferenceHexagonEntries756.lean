import RMod.BrundanEllis.StackingReferenceHexagonMiddle7
import RMod.BrundanEllis.StackingReferenceSparseMatrixCheck
import RMod.BrundanEllis.StackingReferenceHexagonAtoms756
import RMod.BrundanEllis.StackingReferenceHexagonRowColumn756

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

private theorem left0Middle7_eq_case_5_6_row_0_0_0 : (left0Middle7 5 6) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn756.rows_outerABC HexagonRowColumn756.cols_assocABC) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle7_eq_case_5_6_row_0_0_1 : (left0Middle7 5 6) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn756.rows_outerABC HexagonRowColumn756.cols_assocABC) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle7_eq_case_5_6_row_0_0_2 : (left0Middle7 5 6) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn756.rows_outerABC HexagonRowColumn756.cols_assocABC) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle7_eq_case_5_6_row_0_0_3 : (left0Middle7 5 6) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn756.rows_outerABC HexagonRowColumn756.cols_assocABC) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle7_eq_case_5_6_row_0_1_0 : (left0Middle7 5 6) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn756.rows_outerABC HexagonRowColumn756.cols_assocABC) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle7_eq_case_5_6_row_0_1_1 : (left0Middle7 5 6) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn756.rows_outerABC HexagonRowColumn756.cols_assocABC) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle7_eq_case_5_6_row_0_1_2 : (left0Middle7 5 6) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn756.rows_outerABC HexagonRowColumn756.cols_assocABC) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle7_eq_case_5_6_row_0_1_3 : (left0Middle7 5 6) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn756.rows_outerABC HexagonRowColumn756.cols_assocABC) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle7_eq_case_5_6_row_1_0_0 : (left0Middle7 5 6) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn756.rows_outerABC HexagonRowColumn756.cols_assocABC) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle7_eq_case_5_6_row_1_0_1 : (left0Middle7 5 6) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn756.rows_outerABC HexagonRowColumn756.cols_assocABC) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle7_eq_case_5_6_row_1_0_2 : (left0Middle7 5 6) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn756.rows_outerABC HexagonRowColumn756.cols_assocABC) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle7_eq_case_5_6_row_1_0_3 : (left0Middle7 5 6) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn756.rows_outerABC HexagonRowColumn756.cols_assocABC) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle7_eq_case_5_6_row_1_1_0 : (left0Middle7 5 6) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn756.rows_outerABC HexagonRowColumn756.cols_assocABC) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle7_eq_case_5_6_row_1_1_1 : (left0Middle7 5 6) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn756.rows_outerABC HexagonRowColumn756.cols_assocABC) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle7_eq_case_5_6_row_1_1_2 : (left0Middle7 5 6) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn756.rows_outerABC HexagonRowColumn756.cols_assocABC) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle7_eq_case_5_6_row_1_1_3 : (left0Middle7 5 6) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn756.rows_outerABC HexagonRowColumn756.cols_assocABC) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle7_eq_case_5_6_checked : left0Middle7 5 6 = rowColumnMul HexagonRowColumn756.rows_outerABC HexagonRowColumn756.cols_assocABC := by
  funext r
  fin_cases r
  · exact left0Middle7_eq_case_5_6_row_0_0_0
  · exact left0Middle7_eq_case_5_6_row_0_0_1
  · exact left0Middle7_eq_case_5_6_row_0_0_2
  · exact left0Middle7_eq_case_5_6_row_0_0_3
  · exact left0Middle7_eq_case_5_6_row_0_1_0
  · exact left0Middle7_eq_case_5_6_row_0_1_1
  · exact left0Middle7_eq_case_5_6_row_0_1_2
  · exact left0Middle7_eq_case_5_6_row_0_1_3
  · exact left0Middle7_eq_case_5_6_row_1_0_0
  · exact left0Middle7_eq_case_5_6_row_1_0_1
  · exact left0Middle7_eq_case_5_6_row_1_0_2
  · exact left0Middle7_eq_case_5_6_row_1_0_3
  · exact left0Middle7_eq_case_5_6_row_1_1_0
  · exact left0Middle7_eq_case_5_6_row_1_1_1
  · exact left0Middle7_eq_case_5_6_row_1_1_2
  · exact left0Middle7_eq_case_5_6_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem left0Middle7_eq_case_5_6 : left0Middle7 5 6 = outerRightZ 7 5 6 * associatorZ 7 5 6 := by
  simpa only [HexagonAtoms756.assocABC_eq,
    HexagonAtoms756.outerABC_eq,
    HexagonAtoms756.assocBAC_eq,
    HexagonAtoms756.innerABC_eq,
    HexagonAtoms756.innerRightABC_eq,
    HexagonAtoms756.inverseACB_eq,
    HexagonAtoms756.innerACB_eq,
    HexagonAtoms756.assocBCA_eq,
    HexagonAtoms756.innerRightBAC_eq,
    HexagonAtoms756.assocCAB_eq,
    HexagonAtoms756.outerLeftABC_eq,
    HexagonRowColumn756.product0_eq,
    HexagonRowColumn756.product1_eq,
    HexagonRowColumn756.product2_eq,
    HexagonRowColumn756.product3_eq,
    HexagonRowColumn756.product4_eq,
    HexagonRowColumn756.product5_eq,
    HexagonRowColumn756.product6_eq,
    HexagonRowColumn756.product7_eq] using left0Middle7_eq_case_5_6_checked

private theorem left1Middle7_eq_case_5_6_row_0_0_0 : (left1Middle7 5 6) ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4)) = (HexagonAtoms756.assocBAC) ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle7_eq_case_5_6_row_0_0_1 : (left1Middle7 5 6) ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4)) = (HexagonAtoms756.assocBAC) ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle7_eq_case_5_6_row_0_0_2 : (left1Middle7 5 6) ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4)) = (HexagonAtoms756.assocBAC) ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle7_eq_case_5_6_row_0_0_3 : (left1Middle7 5 6) ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4)) = (HexagonAtoms756.assocBAC) ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle7_eq_case_5_6_row_0_1_0 : (left1Middle7 5 6) ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4)) = (HexagonAtoms756.assocBAC) ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle7_eq_case_5_6_row_0_1_1 : (left1Middle7 5 6) ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4)) = (HexagonAtoms756.assocBAC) ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle7_eq_case_5_6_row_0_1_2 : (left1Middle7 5 6) ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4)) = (HexagonAtoms756.assocBAC) ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle7_eq_case_5_6_row_0_1_3 : (left1Middle7 5 6) ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4)) = (HexagonAtoms756.assocBAC) ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle7_eq_case_5_6_row_0_2_0 : (left1Middle7 5 6) ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4)) = (HexagonAtoms756.assocBAC) ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle7_eq_case_5_6_row_0_2_1 : (left1Middle7 5 6) ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4)) = (HexagonAtoms756.assocBAC) ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle7_eq_case_5_6_row_0_2_2 : (left1Middle7 5 6) ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4)) = (HexagonAtoms756.assocBAC) ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle7_eq_case_5_6_row_0_2_3 : (left1Middle7 5 6) ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4)) = (HexagonAtoms756.assocBAC) ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle7_eq_case_5_6_row_0_3_0 : (left1Middle7 5 6) ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4)) = (HexagonAtoms756.assocBAC) ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle7_eq_case_5_6_row_0_3_1 : (left1Middle7 5 6) ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4)) = (HexagonAtoms756.assocBAC) ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle7_eq_case_5_6_row_0_3_2 : (left1Middle7 5 6) ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4)) = (HexagonAtoms756.assocBAC) ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle7_eq_case_5_6_row_0_3_3 : (left1Middle7 5 6) ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4)) = (HexagonAtoms756.assocBAC) ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle7_eq_case_5_6_checked : left1Middle7 5 6 = HexagonAtoms756.assocBAC := by
  funext r
  fin_cases r
  · exact left1Middle7_eq_case_5_6_row_0_0_0
  · exact left1Middle7_eq_case_5_6_row_0_0_1
  · exact left1Middle7_eq_case_5_6_row_0_0_2
  · exact left1Middle7_eq_case_5_6_row_0_0_3
  · exact left1Middle7_eq_case_5_6_row_0_1_0
  · exact left1Middle7_eq_case_5_6_row_0_1_1
  · exact left1Middle7_eq_case_5_6_row_0_1_2
  · exact left1Middle7_eq_case_5_6_row_0_1_3
  · exact left1Middle7_eq_case_5_6_row_0_2_0
  · exact left1Middle7_eq_case_5_6_row_0_2_1
  · exact left1Middle7_eq_case_5_6_row_0_2_2
  · exact left1Middle7_eq_case_5_6_row_0_2_3
  · exact left1Middle7_eq_case_5_6_row_0_3_0
  · exact left1Middle7_eq_case_5_6_row_0_3_1
  · exact left1Middle7_eq_case_5_6_row_0_3_2
  · exact left1Middle7_eq_case_5_6_row_0_3_3

set_option backward.isDefEq.respectTransparency false in
theorem left1Middle7_eq_case_5_6 : left1Middle7 5 6 = associatorZ 5 7 6 * innerLeftZ 7 5 6 := by
  simpa only [HexagonAtoms756.assocABC_eq,
    HexagonAtoms756.outerABC_eq,
    HexagonAtoms756.assocBAC_eq,
    HexagonAtoms756.innerABC_eq,
    HexagonAtoms756.innerRightABC_eq,
    HexagonAtoms756.inverseACB_eq,
    HexagonAtoms756.innerACB_eq,
    HexagonAtoms756.assocBCA_eq,
    HexagonAtoms756.innerRightBAC_eq,
    HexagonAtoms756.assocCAB_eq,
    HexagonAtoms756.outerLeftABC_eq,
    HexagonRowColumn756.product0_eq,
    HexagonRowColumn756.product1_eq,
    HexagonRowColumn756.product2_eq,
    HexagonRowColumn756.product3_eq,
    HexagonRowColumn756.product4_eq,
    HexagonRowColumn756.product5_eq,
    HexagonRowColumn756.product6_eq,
    HexagonRowColumn756.product7_eq] using left1Middle7_eq_case_5_6_checked

private theorem right0Middle7_eq_case_5_6_row_0_0_0 : (right0Middle7 5 6) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms756.assocABC) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle7_eq_case_5_6_row_0_0_1 : (right0Middle7 5 6) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms756.assocABC) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle7_eq_case_5_6_row_0_0_2 : (right0Middle7 5 6) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms756.assocABC) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle7_eq_case_5_6_row_0_0_3 : (right0Middle7 5 6) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms756.assocABC) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle7_eq_case_5_6_row_0_1_0 : (right0Middle7 5 6) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms756.assocABC) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle7_eq_case_5_6_row_0_1_1 : (right0Middle7 5 6) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms756.assocABC) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle7_eq_case_5_6_row_0_1_2 : (right0Middle7 5 6) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms756.assocABC) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle7_eq_case_5_6_row_0_1_3 : (right0Middle7 5 6) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms756.assocABC) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle7_eq_case_5_6_row_1_0_0 : (right0Middle7 5 6) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms756.assocABC) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle7_eq_case_5_6_row_1_0_1 : (right0Middle7 5 6) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms756.assocABC) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle7_eq_case_5_6_row_1_0_2 : (right0Middle7 5 6) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms756.assocABC) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle7_eq_case_5_6_row_1_0_3 : (right0Middle7 5 6) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms756.assocABC) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle7_eq_case_5_6_row_1_1_0 : (right0Middle7 5 6) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms756.assocABC) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle7_eq_case_5_6_row_1_1_1 : (right0Middle7 5 6) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms756.assocABC) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle7_eq_case_5_6_row_1_1_2 : (right0Middle7 5 6) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms756.assocABC) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle7_eq_case_5_6_row_1_1_3 : (right0Middle7 5 6) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms756.assocABC) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle7_eq_case_5_6_checked : right0Middle7 5 6 = HexagonAtoms756.assocABC := by
  funext r
  fin_cases r
  · exact right0Middle7_eq_case_5_6_row_0_0_0
  · exact right0Middle7_eq_case_5_6_row_0_0_1
  · exact right0Middle7_eq_case_5_6_row_0_0_2
  · exact right0Middle7_eq_case_5_6_row_0_0_3
  · exact right0Middle7_eq_case_5_6_row_0_1_0
  · exact right0Middle7_eq_case_5_6_row_0_1_1
  · exact right0Middle7_eq_case_5_6_row_0_1_2
  · exact right0Middle7_eq_case_5_6_row_0_1_3
  · exact right0Middle7_eq_case_5_6_row_1_0_0
  · exact right0Middle7_eq_case_5_6_row_1_0_1
  · exact right0Middle7_eq_case_5_6_row_1_0_2
  · exact right0Middle7_eq_case_5_6_row_1_0_3
  · exact right0Middle7_eq_case_5_6_row_1_1_0
  · exact right0Middle7_eq_case_5_6_row_1_1_1
  · exact right0Middle7_eq_case_5_6_row_1_1_2
  · exact right0Middle7_eq_case_5_6_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem right0Middle7_eq_case_5_6 : right0Middle7 5 6 = innerRightZ 7 5 6 * associatorZ 7 5 6 := by
  simpa only [HexagonAtoms756.assocABC_eq,
    HexagonAtoms756.outerABC_eq,
    HexagonAtoms756.assocBAC_eq,
    HexagonAtoms756.innerABC_eq,
    HexagonAtoms756.innerRightABC_eq,
    HexagonAtoms756.inverseACB_eq,
    HexagonAtoms756.innerACB_eq,
    HexagonAtoms756.assocBCA_eq,
    HexagonAtoms756.innerRightBAC_eq,
    HexagonAtoms756.assocCAB_eq,
    HexagonAtoms756.outerLeftABC_eq,
    HexagonRowColumn756.product0_eq,
    HexagonRowColumn756.product1_eq,
    HexagonRowColumn756.product2_eq,
    HexagonRowColumn756.product3_eq,
    HexagonRowColumn756.product4_eq,
    HexagonRowColumn756.product5_eq,
    HexagonRowColumn756.product6_eq,
    HexagonRowColumn756.product7_eq] using right0Middle7_eq_case_5_6_checked

private theorem right1Middle7_eq_case_5_6_row_0_0_0 : (right1Middle7 5 6) ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn756.rows_inverseACB HexagonRowColumn756.cols_right0) ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle7_eq_case_5_6_row_0_0_1 : (right1Middle7 5 6) ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn756.rows_inverseACB HexagonRowColumn756.cols_right0) ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle7_eq_case_5_6_row_0_0_2 : (right1Middle7 5 6) ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn756.rows_inverseACB HexagonRowColumn756.cols_right0) ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle7_eq_case_5_6_row_0_0_3 : (right1Middle7 5 6) ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn756.rows_inverseACB HexagonRowColumn756.cols_right0) ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle7_eq_case_5_6_row_0_1_0 : (right1Middle7 5 6) ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn756.rows_inverseACB HexagonRowColumn756.cols_right0) ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle7_eq_case_5_6_row_0_1_1 : (right1Middle7 5 6) ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn756.rows_inverseACB HexagonRowColumn756.cols_right0) ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle7_eq_case_5_6_row_0_1_2 : (right1Middle7 5 6) ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn756.rows_inverseACB HexagonRowColumn756.cols_right0) ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle7_eq_case_5_6_row_0_1_3 : (right1Middle7 5 6) ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn756.rows_inverseACB HexagonRowColumn756.cols_right0) ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle7_eq_case_5_6_row_0_2_0 : (right1Middle7 5 6) ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn756.rows_inverseACB HexagonRowColumn756.cols_right0) ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle7_eq_case_5_6_row_0_2_1 : (right1Middle7 5 6) ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn756.rows_inverseACB HexagonRowColumn756.cols_right0) ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle7_eq_case_5_6_row_0_2_2 : (right1Middle7 5 6) ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn756.rows_inverseACB HexagonRowColumn756.cols_right0) ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle7_eq_case_5_6_row_0_2_3 : (right1Middle7 5 6) ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn756.rows_inverseACB HexagonRowColumn756.cols_right0) ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle7_eq_case_5_6_row_0_3_0 : (right1Middle7 5 6) ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn756.rows_inverseACB HexagonRowColumn756.cols_right0) ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle7_eq_case_5_6_row_0_3_1 : (right1Middle7 5 6) ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn756.rows_inverseACB HexagonRowColumn756.cols_right0) ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle7_eq_case_5_6_row_0_3_2 : (right1Middle7 5 6) ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn756.rows_inverseACB HexagonRowColumn756.cols_right0) ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle7_eq_case_5_6_row_0_3_3 : (right1Middle7 5 6) ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn756.rows_inverseACB HexagonRowColumn756.cols_right0) ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle7_eq_case_5_6_checked : right1Middle7 5 6 = rowColumnMul HexagonRowColumn756.rows_inverseACB HexagonRowColumn756.cols_right0 := by
  funext r
  fin_cases r
  · exact right1Middle7_eq_case_5_6_row_0_0_0
  · exact right1Middle7_eq_case_5_6_row_0_0_1
  · exact right1Middle7_eq_case_5_6_row_0_0_2
  · exact right1Middle7_eq_case_5_6_row_0_0_3
  · exact right1Middle7_eq_case_5_6_row_0_1_0
  · exact right1Middle7_eq_case_5_6_row_0_1_1
  · exact right1Middle7_eq_case_5_6_row_0_1_2
  · exact right1Middle7_eq_case_5_6_row_0_1_3
  · exact right1Middle7_eq_case_5_6_row_0_2_0
  · exact right1Middle7_eq_case_5_6_row_0_2_1
  · exact right1Middle7_eq_case_5_6_row_0_2_2
  · exact right1Middle7_eq_case_5_6_row_0_2_3
  · exact right1Middle7_eq_case_5_6_row_0_3_0
  · exact right1Middle7_eq_case_5_6_row_0_3_1
  · exact right1Middle7_eq_case_5_6_row_0_3_2
  · exact right1Middle7_eq_case_5_6_row_0_3_3

set_option backward.isDefEq.respectTransparency false in
theorem right1Middle7_eq_case_5_6 : right1Middle7 5 6 = associatorInverseZ 7 6 5 * right0Middle7 5 6 := by
  simpa only [HexagonAtoms756.assocABC_eq,
    HexagonAtoms756.outerABC_eq,
    HexagonAtoms756.assocBAC_eq,
    HexagonAtoms756.innerABC_eq,
    HexagonAtoms756.innerRightABC_eq,
    HexagonAtoms756.inverseACB_eq,
    HexagonAtoms756.innerACB_eq,
    HexagonAtoms756.assocBCA_eq,
    HexagonAtoms756.innerRightBAC_eq,
    HexagonAtoms756.assocCAB_eq,
    HexagonAtoms756.outerLeftABC_eq,
    HexagonRowColumn756.product0_eq,
    HexagonRowColumn756.product1_eq,
    HexagonRowColumn756.product2_eq,
    HexagonRowColumn756.product3_eq,
    HexagonRowColumn756.product4_eq,
    HexagonRowColumn756.product5_eq,
    HexagonRowColumn756.product6_eq,
    HexagonRowColumn756.product7_eq] using right1Middle7_eq_case_5_6_checked

private theorem right2Middle7_eq_case_5_6_row_0_0_0 : (right2Middle7 5 6) ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn756.rows_innerACB HexagonRowColumn756.cols_right1) ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle7_eq_case_5_6_row_0_0_1 : (right2Middle7 5 6) ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn756.rows_innerACB HexagonRowColumn756.cols_right1) ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle7_eq_case_5_6_row_0_0_2 : (right2Middle7 5 6) ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn756.rows_innerACB HexagonRowColumn756.cols_right1) ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle7_eq_case_5_6_row_0_0_3 : (right2Middle7 5 6) ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn756.rows_innerACB HexagonRowColumn756.cols_right1) ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle7_eq_case_5_6_row_0_1_0 : (right2Middle7 5 6) ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn756.rows_innerACB HexagonRowColumn756.cols_right1) ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle7_eq_case_5_6_row_0_1_1 : (right2Middle7 5 6) ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn756.rows_innerACB HexagonRowColumn756.cols_right1) ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle7_eq_case_5_6_row_0_1_2 : (right2Middle7 5 6) ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn756.rows_innerACB HexagonRowColumn756.cols_right1) ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle7_eq_case_5_6_row_0_1_3 : (right2Middle7 5 6) ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn756.rows_innerACB HexagonRowColumn756.cols_right1) ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle7_eq_case_5_6_row_0_2_0 : (right2Middle7 5 6) ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn756.rows_innerACB HexagonRowColumn756.cols_right1) ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle7_eq_case_5_6_row_0_2_1 : (right2Middle7 5 6) ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn756.rows_innerACB HexagonRowColumn756.cols_right1) ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle7_eq_case_5_6_row_0_2_2 : (right2Middle7 5 6) ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn756.rows_innerACB HexagonRowColumn756.cols_right1) ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle7_eq_case_5_6_row_0_2_3 : (right2Middle7 5 6) ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn756.rows_innerACB HexagonRowColumn756.cols_right1) ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle7_eq_case_5_6_row_0_3_0 : (right2Middle7 5 6) ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn756.rows_innerACB HexagonRowColumn756.cols_right1) ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle7_eq_case_5_6_row_0_3_1 : (right2Middle7 5 6) ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn756.rows_innerACB HexagonRowColumn756.cols_right1) ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle7_eq_case_5_6_row_0_3_2 : (right2Middle7 5 6) ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn756.rows_innerACB HexagonRowColumn756.cols_right1) ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle7_eq_case_5_6_row_0_3_3 : (right2Middle7 5 6) ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn756.rows_innerACB HexagonRowColumn756.cols_right1) ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle7_eq_case_5_6_checked : right2Middle7 5 6 = rowColumnMul HexagonRowColumn756.rows_innerACB HexagonRowColumn756.cols_right1 := by
  funext r
  fin_cases r
  · exact right2Middle7_eq_case_5_6_row_0_0_0
  · exact right2Middle7_eq_case_5_6_row_0_0_1
  · exact right2Middle7_eq_case_5_6_row_0_0_2
  · exact right2Middle7_eq_case_5_6_row_0_0_3
  · exact right2Middle7_eq_case_5_6_row_0_1_0
  · exact right2Middle7_eq_case_5_6_row_0_1_1
  · exact right2Middle7_eq_case_5_6_row_0_1_2
  · exact right2Middle7_eq_case_5_6_row_0_1_3
  · exact right2Middle7_eq_case_5_6_row_0_2_0
  · exact right2Middle7_eq_case_5_6_row_0_2_1
  · exact right2Middle7_eq_case_5_6_row_0_2_2
  · exact right2Middle7_eq_case_5_6_row_0_2_3
  · exact right2Middle7_eq_case_5_6_row_0_3_0
  · exact right2Middle7_eq_case_5_6_row_0_3_1
  · exact right2Middle7_eq_case_5_6_row_0_3_2
  · exact right2Middle7_eq_case_5_6_row_0_3_3

set_option backward.isDefEq.respectTransparency false in
theorem right2Middle7_eq_case_5_6 : right2Middle7 5 6 = innerLeftZ 7 6 5 * right1Middle7 5 6 := by
  simpa only [HexagonAtoms756.assocABC_eq,
    HexagonAtoms756.outerABC_eq,
    HexagonAtoms756.assocBAC_eq,
    HexagonAtoms756.innerABC_eq,
    HexagonAtoms756.innerRightABC_eq,
    HexagonAtoms756.inverseACB_eq,
    HexagonAtoms756.innerACB_eq,
    HexagonAtoms756.assocBCA_eq,
    HexagonAtoms756.innerRightBAC_eq,
    HexagonAtoms756.assocCAB_eq,
    HexagonAtoms756.outerLeftABC_eq,
    HexagonRowColumn756.product0_eq,
    HexagonRowColumn756.product1_eq,
    HexagonRowColumn756.product2_eq,
    HexagonRowColumn756.product3_eq,
    HexagonRowColumn756.product4_eq,
    HexagonRowColumn756.product5_eq,
    HexagonRowColumn756.product6_eq,
    HexagonRowColumn756.product7_eq] using right2Middle7_eq_case_5_6_checked

private theorem leftFinal7_case_5_6_row_0_0_0 : (((-1 : ℤ) ^ (leftScaleBit 7 5 6).val * positiveScale (leftScaleExponent 7 5 6)) •
      (rowColumnMul HexagonRowColumn756.rows_assocBCA HexagonRowColumn756.cols_left0)) ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4)) = (negativeScale (leftScaleExponent 7 5 6) • (rowColumnMul HexagonRowColumn756.rows_innerRightBAC HexagonRowColumn756.cols_left1)) ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal7_case_5_6_row_0_0_1 : (((-1 : ℤ) ^ (leftScaleBit 7 5 6).val * positiveScale (leftScaleExponent 7 5 6)) •
      (rowColumnMul HexagonRowColumn756.rows_assocBCA HexagonRowColumn756.cols_left0)) ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4)) = (negativeScale (leftScaleExponent 7 5 6) • (rowColumnMul HexagonRowColumn756.rows_innerRightBAC HexagonRowColumn756.cols_left1)) ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal7_case_5_6_row_0_0_2 : (((-1 : ℤ) ^ (leftScaleBit 7 5 6).val * positiveScale (leftScaleExponent 7 5 6)) •
      (rowColumnMul HexagonRowColumn756.rows_assocBCA HexagonRowColumn756.cols_left0)) ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4)) = (negativeScale (leftScaleExponent 7 5 6) • (rowColumnMul HexagonRowColumn756.rows_innerRightBAC HexagonRowColumn756.cols_left1)) ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal7_case_5_6_row_0_0_3 : (((-1 : ℤ) ^ (leftScaleBit 7 5 6).val * positiveScale (leftScaleExponent 7 5 6)) •
      (rowColumnMul HexagonRowColumn756.rows_assocBCA HexagonRowColumn756.cols_left0)) ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4)) = (negativeScale (leftScaleExponent 7 5 6) • (rowColumnMul HexagonRowColumn756.rows_innerRightBAC HexagonRowColumn756.cols_left1)) ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal7_case_5_6_row_0_1_0 : (((-1 : ℤ) ^ (leftScaleBit 7 5 6).val * positiveScale (leftScaleExponent 7 5 6)) •
      (rowColumnMul HexagonRowColumn756.rows_assocBCA HexagonRowColumn756.cols_left0)) ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4)) = (negativeScale (leftScaleExponent 7 5 6) • (rowColumnMul HexagonRowColumn756.rows_innerRightBAC HexagonRowColumn756.cols_left1)) ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal7_case_5_6_row_0_1_1 : (((-1 : ℤ) ^ (leftScaleBit 7 5 6).val * positiveScale (leftScaleExponent 7 5 6)) •
      (rowColumnMul HexagonRowColumn756.rows_assocBCA HexagonRowColumn756.cols_left0)) ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4)) = (negativeScale (leftScaleExponent 7 5 6) • (rowColumnMul HexagonRowColumn756.rows_innerRightBAC HexagonRowColumn756.cols_left1)) ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal7_case_5_6_row_0_1_2 : (((-1 : ℤ) ^ (leftScaleBit 7 5 6).val * positiveScale (leftScaleExponent 7 5 6)) •
      (rowColumnMul HexagonRowColumn756.rows_assocBCA HexagonRowColumn756.cols_left0)) ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4)) = (negativeScale (leftScaleExponent 7 5 6) • (rowColumnMul HexagonRowColumn756.rows_innerRightBAC HexagonRowColumn756.cols_left1)) ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal7_case_5_6_row_0_1_3 : (((-1 : ℤ) ^ (leftScaleBit 7 5 6).val * positiveScale (leftScaleExponent 7 5 6)) •
      (rowColumnMul HexagonRowColumn756.rows_assocBCA HexagonRowColumn756.cols_left0)) ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4)) = (negativeScale (leftScaleExponent 7 5 6) • (rowColumnMul HexagonRowColumn756.rows_innerRightBAC HexagonRowColumn756.cols_left1)) ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal7_case_5_6_row_0_2_0 : (((-1 : ℤ) ^ (leftScaleBit 7 5 6).val * positiveScale (leftScaleExponent 7 5 6)) •
      (rowColumnMul HexagonRowColumn756.rows_assocBCA HexagonRowColumn756.cols_left0)) ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4)) = (negativeScale (leftScaleExponent 7 5 6) • (rowColumnMul HexagonRowColumn756.rows_innerRightBAC HexagonRowColumn756.cols_left1)) ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal7_case_5_6_row_0_2_1 : (((-1 : ℤ) ^ (leftScaleBit 7 5 6).val * positiveScale (leftScaleExponent 7 5 6)) •
      (rowColumnMul HexagonRowColumn756.rows_assocBCA HexagonRowColumn756.cols_left0)) ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4)) = (negativeScale (leftScaleExponent 7 5 6) • (rowColumnMul HexagonRowColumn756.rows_innerRightBAC HexagonRowColumn756.cols_left1)) ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal7_case_5_6_row_0_2_2 : (((-1 : ℤ) ^ (leftScaleBit 7 5 6).val * positiveScale (leftScaleExponent 7 5 6)) •
      (rowColumnMul HexagonRowColumn756.rows_assocBCA HexagonRowColumn756.cols_left0)) ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4)) = (negativeScale (leftScaleExponent 7 5 6) • (rowColumnMul HexagonRowColumn756.rows_innerRightBAC HexagonRowColumn756.cols_left1)) ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal7_case_5_6_row_0_2_3 : (((-1 : ℤ) ^ (leftScaleBit 7 5 6).val * positiveScale (leftScaleExponent 7 5 6)) •
      (rowColumnMul HexagonRowColumn756.rows_assocBCA HexagonRowColumn756.cols_left0)) ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4)) = (negativeScale (leftScaleExponent 7 5 6) • (rowColumnMul HexagonRowColumn756.rows_innerRightBAC HexagonRowColumn756.cols_left1)) ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal7_case_5_6_row_0_3_0 : (((-1 : ℤ) ^ (leftScaleBit 7 5 6).val * positiveScale (leftScaleExponent 7 5 6)) •
      (rowColumnMul HexagonRowColumn756.rows_assocBCA HexagonRowColumn756.cols_left0)) ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4)) = (negativeScale (leftScaleExponent 7 5 6) • (rowColumnMul HexagonRowColumn756.rows_innerRightBAC HexagonRowColumn756.cols_left1)) ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal7_case_5_6_row_0_3_1 : (((-1 : ℤ) ^ (leftScaleBit 7 5 6).val * positiveScale (leftScaleExponent 7 5 6)) •
      (rowColumnMul HexagonRowColumn756.rows_assocBCA HexagonRowColumn756.cols_left0)) ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4)) = (negativeScale (leftScaleExponent 7 5 6) • (rowColumnMul HexagonRowColumn756.rows_innerRightBAC HexagonRowColumn756.cols_left1)) ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal7_case_5_6_row_0_3_2 : (((-1 : ℤ) ^ (leftScaleBit 7 5 6).val * positiveScale (leftScaleExponent 7 5 6)) •
      (rowColumnMul HexagonRowColumn756.rows_assocBCA HexagonRowColumn756.cols_left0)) ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4)) = (negativeScale (leftScaleExponent 7 5 6) • (rowColumnMul HexagonRowColumn756.rows_innerRightBAC HexagonRowColumn756.cols_left1)) ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal7_case_5_6_row_0_3_3 : (((-1 : ℤ) ^ (leftScaleBit 7 5 6).val * positiveScale (leftScaleExponent 7 5 6)) •
      (rowColumnMul HexagonRowColumn756.rows_assocBCA HexagonRowColumn756.cols_left0)) ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4)) = (negativeScale (leftScaleExponent 7 5 6) • (rowColumnMul HexagonRowColumn756.rows_innerRightBAC HexagonRowColumn756.cols_left1)) ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal7_case_5_6_checked : ((-1 : ℤ) ^ (leftScaleBit 7 5 6).val * positiveScale (leftScaleExponent 7 5 6)) •
      (rowColumnMul HexagonRowColumn756.rows_assocBCA HexagonRowColumn756.cols_left0) = negativeScale (leftScaleExponent 7 5 6) • (rowColumnMul HexagonRowColumn756.rows_innerRightBAC HexagonRowColumn756.cols_left1) := by
  funext r
  fin_cases r
  · exact leftFinal7_case_5_6_row_0_0_0
  · exact leftFinal7_case_5_6_row_0_0_1
  · exact leftFinal7_case_5_6_row_0_0_2
  · exact leftFinal7_case_5_6_row_0_0_3
  · exact leftFinal7_case_5_6_row_0_1_0
  · exact leftFinal7_case_5_6_row_0_1_1
  · exact leftFinal7_case_5_6_row_0_1_2
  · exact leftFinal7_case_5_6_row_0_1_3
  · exact leftFinal7_case_5_6_row_0_2_0
  · exact leftFinal7_case_5_6_row_0_2_1
  · exact leftFinal7_case_5_6_row_0_2_2
  · exact leftFinal7_case_5_6_row_0_2_3
  · exact leftFinal7_case_5_6_row_0_3_0
  · exact leftFinal7_case_5_6_row_0_3_1
  · exact leftFinal7_case_5_6_row_0_3_2
  · exact leftFinal7_case_5_6_row_0_3_3

set_option backward.isDefEq.respectTransparency false in
theorem leftFinal7_case_5_6 : ((-1 : ℤ) ^ (leftScaleBit 7 5 6).val * positiveScale (leftScaleExponent 7 5 6)) •
      (associatorZ 5 6 7 * left0Middle7 5 6) = negativeScale (leftScaleExponent 7 5 6) • (innerRightZ 5 7 6 * left1Middle7 5 6) := by
  simpa only [HexagonAtoms756.assocABC_eq,
    HexagonAtoms756.outerABC_eq,
    HexagonAtoms756.assocBAC_eq,
    HexagonAtoms756.innerABC_eq,
    HexagonAtoms756.innerRightABC_eq,
    HexagonAtoms756.inverseACB_eq,
    HexagonAtoms756.innerACB_eq,
    HexagonAtoms756.assocBCA_eq,
    HexagonAtoms756.innerRightBAC_eq,
    HexagonAtoms756.assocCAB_eq,
    HexagonAtoms756.outerLeftABC_eq,
    HexagonRowColumn756.product0_eq,
    HexagonRowColumn756.product1_eq,
    HexagonRowColumn756.product2_eq,
    HexagonRowColumn756.product3_eq,
    HexagonRowColumn756.product4_eq,
    HexagonRowColumn756.product5_eq,
    HexagonRowColumn756.product6_eq,
    HexagonRowColumn756.product7_eq] using leftFinal7_case_5_6_checked

private theorem rightFinal7_case_5_6_row_0_0_0 : (((-1 : ℤ) ^ (rightScaleBit 7 5 6).val * positiveScale (rightScaleExponent 7 5 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 6 5 : ℤ)) • HexagonAtoms756.outerLeftABC) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 7 5 6) • (rowColumnMul HexagonRowColumn756.rows_assocCAB HexagonRowColumn756.cols_right2)) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal7_case_5_6_row_0_0_1 : (((-1 : ℤ) ^ (rightScaleBit 7 5 6).val * positiveScale (rightScaleExponent 7 5 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 6 5 : ℤ)) • HexagonAtoms756.outerLeftABC) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 7 5 6) • (rowColumnMul HexagonRowColumn756.rows_assocCAB HexagonRowColumn756.cols_right2)) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal7_case_5_6_row_0_0_2 : (((-1 : ℤ) ^ (rightScaleBit 7 5 6).val * positiveScale (rightScaleExponent 7 5 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 6 5 : ℤ)) • HexagonAtoms756.outerLeftABC) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 7 5 6) • (rowColumnMul HexagonRowColumn756.rows_assocCAB HexagonRowColumn756.cols_right2)) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal7_case_5_6_row_0_0_3 : (((-1 : ℤ) ^ (rightScaleBit 7 5 6).val * positiveScale (rightScaleExponent 7 5 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 6 5 : ℤ)) • HexagonAtoms756.outerLeftABC) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 7 5 6) • (rowColumnMul HexagonRowColumn756.rows_assocCAB HexagonRowColumn756.cols_right2)) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal7_case_5_6_row_0_1_0 : (((-1 : ℤ) ^ (rightScaleBit 7 5 6).val * positiveScale (rightScaleExponent 7 5 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 6 5 : ℤ)) • HexagonAtoms756.outerLeftABC) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 7 5 6) • (rowColumnMul HexagonRowColumn756.rows_assocCAB HexagonRowColumn756.cols_right2)) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal7_case_5_6_row_0_1_1 : (((-1 : ℤ) ^ (rightScaleBit 7 5 6).val * positiveScale (rightScaleExponent 7 5 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 6 5 : ℤ)) • HexagonAtoms756.outerLeftABC) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 7 5 6) • (rowColumnMul HexagonRowColumn756.rows_assocCAB HexagonRowColumn756.cols_right2)) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal7_case_5_6_row_0_1_2 : (((-1 : ℤ) ^ (rightScaleBit 7 5 6).val * positiveScale (rightScaleExponent 7 5 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 6 5 : ℤ)) • HexagonAtoms756.outerLeftABC) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 7 5 6) • (rowColumnMul HexagonRowColumn756.rows_assocCAB HexagonRowColumn756.cols_right2)) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal7_case_5_6_row_0_1_3 : (((-1 : ℤ) ^ (rightScaleBit 7 5 6).val * positiveScale (rightScaleExponent 7 5 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 6 5 : ℤ)) • HexagonAtoms756.outerLeftABC) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 7 5 6) • (rowColumnMul HexagonRowColumn756.rows_assocCAB HexagonRowColumn756.cols_right2)) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal7_case_5_6_row_1_0_0 : (((-1 : ℤ) ^ (rightScaleBit 7 5 6).val * positiveScale (rightScaleExponent 7 5 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 6 5 : ℤ)) • HexagonAtoms756.outerLeftABC) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 7 5 6) • (rowColumnMul HexagonRowColumn756.rows_assocCAB HexagonRowColumn756.cols_right2)) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal7_case_5_6_row_1_0_1 : (((-1 : ℤ) ^ (rightScaleBit 7 5 6).val * positiveScale (rightScaleExponent 7 5 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 6 5 : ℤ)) • HexagonAtoms756.outerLeftABC) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 7 5 6) • (rowColumnMul HexagonRowColumn756.rows_assocCAB HexagonRowColumn756.cols_right2)) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal7_case_5_6_row_1_0_2 : (((-1 : ℤ) ^ (rightScaleBit 7 5 6).val * positiveScale (rightScaleExponent 7 5 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 6 5 : ℤ)) • HexagonAtoms756.outerLeftABC) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 7 5 6) • (rowColumnMul HexagonRowColumn756.rows_assocCAB HexagonRowColumn756.cols_right2)) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal7_case_5_6_row_1_0_3 : (((-1 : ℤ) ^ (rightScaleBit 7 5 6).val * positiveScale (rightScaleExponent 7 5 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 6 5 : ℤ)) • HexagonAtoms756.outerLeftABC) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 7 5 6) • (rowColumnMul HexagonRowColumn756.rows_assocCAB HexagonRowColumn756.cols_right2)) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal7_case_5_6_row_1_1_0 : (((-1 : ℤ) ^ (rightScaleBit 7 5 6).val * positiveScale (rightScaleExponent 7 5 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 6 5 : ℤ)) • HexagonAtoms756.outerLeftABC) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 7 5 6) • (rowColumnMul HexagonRowColumn756.rows_assocCAB HexagonRowColumn756.cols_right2)) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal7_case_5_6_row_1_1_1 : (((-1 : ℤ) ^ (rightScaleBit 7 5 6).val * positiveScale (rightScaleExponent 7 5 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 6 5 : ℤ)) • HexagonAtoms756.outerLeftABC) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 7 5 6) • (rowColumnMul HexagonRowColumn756.rows_assocCAB HexagonRowColumn756.cols_right2)) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal7_case_5_6_row_1_1_2 : (((-1 : ℤ) ^ (rightScaleBit 7 5 6).val * positiveScale (rightScaleExponent 7 5 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 6 5 : ℤ)) • HexagonAtoms756.outerLeftABC) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 7 5 6) • (rowColumnMul HexagonRowColumn756.rows_assocCAB HexagonRowColumn756.cols_right2)) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal7_case_5_6_row_1_1_3 : (((-1 : ℤ) ^ (rightScaleBit 7 5 6).val * positiveScale (rightScaleExponent 7 5 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 6 5 : ℤ)) • HexagonAtoms756.outerLeftABC) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 7 5 6) • (rowColumnMul HexagonRowColumn756.rows_assocCAB HexagonRowColumn756.cols_right2)) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal7_case_5_6_checked : ((-1 : ℤ) ^ (rightScaleBit 7 5 6).val * positiveScale (rightScaleExponent 7 5 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 6 5 : ℤ)) • HexagonAtoms756.outerLeftABC = negativeScale (rightScaleExponent 7 5 6) • (rowColumnMul HexagonRowColumn756.rows_assocCAB HexagonRowColumn756.cols_right2) := by
  funext r
  fin_cases r
  · exact rightFinal7_case_5_6_row_0_0_0
  · exact rightFinal7_case_5_6_row_0_0_1
  · exact rightFinal7_case_5_6_row_0_0_2
  · exact rightFinal7_case_5_6_row_0_0_3
  · exact rightFinal7_case_5_6_row_0_1_0
  · exact rightFinal7_case_5_6_row_0_1_1
  · exact rightFinal7_case_5_6_row_0_1_2
  · exact rightFinal7_case_5_6_row_0_1_3
  · exact rightFinal7_case_5_6_row_1_0_0
  · exact rightFinal7_case_5_6_row_1_0_1
  · exact rightFinal7_case_5_6_row_1_0_2
  · exact rightFinal7_case_5_6_row_1_0_3
  · exact rightFinal7_case_5_6_row_1_1_0
  · exact rightFinal7_case_5_6_row_1_1_1
  · exact rightFinal7_case_5_6_row_1_1_2
  · exact rightFinal7_case_5_6_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem rightFinal7_case_5_6 : ((-1 : ℤ) ^ (rightScaleBit 7 5 6).val * positiveScale (rightScaleExponent 7 5 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 6 5 : ℤ)) • outerLeftZ 7 5 6 = negativeScale (rightScaleExponent 7 5 6) • (associatorZ 6 7 5 * right2Middle7 5 6) := by
  simpa only [HexagonAtoms756.assocABC_eq,
    HexagonAtoms756.outerABC_eq,
    HexagonAtoms756.assocBAC_eq,
    HexagonAtoms756.innerABC_eq,
    HexagonAtoms756.innerRightABC_eq,
    HexagonAtoms756.inverseACB_eq,
    HexagonAtoms756.innerACB_eq,
    HexagonAtoms756.assocBCA_eq,
    HexagonAtoms756.innerRightBAC_eq,
    HexagonAtoms756.assocCAB_eq,
    HexagonAtoms756.outerLeftABC_eq,
    HexagonRowColumn756.product0_eq,
    HexagonRowColumn756.product1_eq,
    HexagonRowColumn756.product2_eq,
    HexagonRowColumn756.product3_eq,
    HexagonRowColumn756.product4_eq,
    HexagonRowColumn756.product5_eq,
    HexagonRowColumn756.product6_eq,
    HexagonRowColumn756.product7_eq] using rightFinal7_case_5_6_checked

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonCases7
