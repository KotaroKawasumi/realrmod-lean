import RMod.BrundanEllis.StackingReferenceHexagonMiddle3
import RMod.BrundanEllis.StackingReferenceSparseMatrixCheck
import RMod.BrundanEllis.StackingReferenceHexagonAtoms374
import RMod.BrundanEllis.StackingReferenceHexagonRowColumn374

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

private theorem left0Middle3_eq_case_7_4_row_0_0_0 : (left0Middle3 7 4) ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn374.rows_outerABC HexagonRowColumn374.cols_assocABC) ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_7_4_row_0_0_1 : (left0Middle3 7 4) ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn374.rows_outerABC HexagonRowColumn374.cols_assocABC) ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_7_4_row_0_0_2 : (left0Middle3 7 4) ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn374.rows_outerABC HexagonRowColumn374.cols_assocABC) ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_7_4_row_0_0_3 : (left0Middle3 7 4) ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn374.rows_outerABC HexagonRowColumn374.cols_assocABC) ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_7_4_row_0_1_0 : (left0Middle3 7 4) ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn374.rows_outerABC HexagonRowColumn374.cols_assocABC) ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_7_4_row_0_1_1 : (left0Middle3 7 4) ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn374.rows_outerABC HexagonRowColumn374.cols_assocABC) ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_7_4_row_0_1_2 : (left0Middle3 7 4) ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn374.rows_outerABC HexagonRowColumn374.cols_assocABC) ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_7_4_row_0_1_3 : (left0Middle3 7 4) ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn374.rows_outerABC HexagonRowColumn374.cols_assocABC) ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_7_4_row_0_2_0 : (left0Middle3 7 4) ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn374.rows_outerABC HexagonRowColumn374.cols_assocABC) ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_7_4_row_0_2_1 : (left0Middle3 7 4) ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn374.rows_outerABC HexagonRowColumn374.cols_assocABC) ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_7_4_row_0_2_2 : (left0Middle3 7 4) ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn374.rows_outerABC HexagonRowColumn374.cols_assocABC) ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_7_4_row_0_2_3 : (left0Middle3 7 4) ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn374.rows_outerABC HexagonRowColumn374.cols_assocABC) ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_7_4_row_0_3_0 : (left0Middle3 7 4) ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn374.rows_outerABC HexagonRowColumn374.cols_assocABC) ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_7_4_row_0_3_1 : (left0Middle3 7 4) ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn374.rows_outerABC HexagonRowColumn374.cols_assocABC) ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_7_4_row_0_3_2 : (left0Middle3 7 4) ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn374.rows_outerABC HexagonRowColumn374.cols_assocABC) ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_7_4_row_0_3_3 : (left0Middle3 7 4) ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn374.rows_outerABC HexagonRowColumn374.cols_assocABC) ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_7_4_checked : left0Middle3 7 4 = rowColumnMul HexagonRowColumn374.rows_outerABC HexagonRowColumn374.cols_assocABC := by
  funext r
  fin_cases r
  · exact left0Middle3_eq_case_7_4_row_0_0_0
  · exact left0Middle3_eq_case_7_4_row_0_0_1
  · exact left0Middle3_eq_case_7_4_row_0_0_2
  · exact left0Middle3_eq_case_7_4_row_0_0_3
  · exact left0Middle3_eq_case_7_4_row_0_1_0
  · exact left0Middle3_eq_case_7_4_row_0_1_1
  · exact left0Middle3_eq_case_7_4_row_0_1_2
  · exact left0Middle3_eq_case_7_4_row_0_1_3
  · exact left0Middle3_eq_case_7_4_row_0_2_0
  · exact left0Middle3_eq_case_7_4_row_0_2_1
  · exact left0Middle3_eq_case_7_4_row_0_2_2
  · exact left0Middle3_eq_case_7_4_row_0_2_3
  · exact left0Middle3_eq_case_7_4_row_0_3_0
  · exact left0Middle3_eq_case_7_4_row_0_3_1
  · exact left0Middle3_eq_case_7_4_row_0_3_2
  · exact left0Middle3_eq_case_7_4_row_0_3_3

set_option backward.isDefEq.respectTransparency false in
theorem left0Middle3_eq_case_7_4 : left0Middle3 7 4 = outerRightZ 3 7 4 * associatorZ 3 7 4 := by
  simpa only [HexagonAtoms374.assocABC_eq,
    HexagonAtoms374.outerABC_eq,
    HexagonAtoms374.assocBAC_eq,
    HexagonAtoms374.innerABC_eq,
    HexagonAtoms374.innerRightABC_eq,
    HexagonAtoms374.inverseACB_eq,
    HexagonAtoms374.innerACB_eq,
    HexagonAtoms374.assocBCA_eq,
    HexagonAtoms374.innerRightBAC_eq,
    HexagonAtoms374.assocCAB_eq,
    HexagonAtoms374.outerLeftABC_eq,
    HexagonRowColumn374.product0_eq,
    HexagonRowColumn374.product1_eq,
    HexagonRowColumn374.product2_eq,
    HexagonRowColumn374.product3_eq,
    HexagonRowColumn374.product4_eq,
    HexagonRowColumn374.product5_eq,
    HexagonRowColumn374.product6_eq,
    HexagonRowColumn374.product7_eq] using left0Middle3_eq_case_7_4_checked

private theorem left1Middle3_eq_case_7_4_row_0_0_0 : (left1Middle3 7 4) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms374.assocBAC) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_7_4_row_0_0_1 : (left1Middle3 7 4) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms374.assocBAC) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_7_4_row_0_0_2 : (left1Middle3 7 4) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms374.assocBAC) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_7_4_row_0_0_3 : (left1Middle3 7 4) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms374.assocBAC) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_7_4_row_1_0_0 : (left1Middle3 7 4) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms374.assocBAC) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_7_4_row_1_0_1 : (left1Middle3 7 4) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms374.assocBAC) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_7_4_row_1_0_2 : (left1Middle3 7 4) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms374.assocBAC) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_7_4_row_1_0_3 : (left1Middle3 7 4) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms374.assocBAC) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_7_4_row_2_0_0 : (left1Middle3 7 4) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms374.assocBAC) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_7_4_row_2_0_1 : (left1Middle3 7 4) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms374.assocBAC) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_7_4_row_2_0_2 : (left1Middle3 7 4) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms374.assocBAC) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_7_4_row_2_0_3 : (left1Middle3 7 4) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms374.assocBAC) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_7_4_row_3_0_0 : (left1Middle3 7 4) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms374.assocBAC) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_7_4_row_3_0_1 : (left1Middle3 7 4) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms374.assocBAC) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_7_4_row_3_0_2 : (left1Middle3 7 4) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms374.assocBAC) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_7_4_row_3_0_3 : (left1Middle3 7 4) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms374.assocBAC) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_7_4_checked : left1Middle3 7 4 = HexagonAtoms374.assocBAC := by
  funext r
  fin_cases r
  · exact left1Middle3_eq_case_7_4_row_0_0_0
  · exact left1Middle3_eq_case_7_4_row_0_0_1
  · exact left1Middle3_eq_case_7_4_row_0_0_2
  · exact left1Middle3_eq_case_7_4_row_0_0_3
  · exact left1Middle3_eq_case_7_4_row_1_0_0
  · exact left1Middle3_eq_case_7_4_row_1_0_1
  · exact left1Middle3_eq_case_7_4_row_1_0_2
  · exact left1Middle3_eq_case_7_4_row_1_0_3
  · exact left1Middle3_eq_case_7_4_row_2_0_0
  · exact left1Middle3_eq_case_7_4_row_2_0_1
  · exact left1Middle3_eq_case_7_4_row_2_0_2
  · exact left1Middle3_eq_case_7_4_row_2_0_3
  · exact left1Middle3_eq_case_7_4_row_3_0_0
  · exact left1Middle3_eq_case_7_4_row_3_0_1
  · exact left1Middle3_eq_case_7_4_row_3_0_2
  · exact left1Middle3_eq_case_7_4_row_3_0_3

set_option backward.isDefEq.respectTransparency false in
theorem left1Middle3_eq_case_7_4 : left1Middle3 7 4 = associatorZ 7 3 4 * innerLeftZ 3 7 4 := by
  simpa only [HexagonAtoms374.assocABC_eq,
    HexagonAtoms374.outerABC_eq,
    HexagonAtoms374.assocBAC_eq,
    HexagonAtoms374.innerABC_eq,
    HexagonAtoms374.innerRightABC_eq,
    HexagonAtoms374.inverseACB_eq,
    HexagonAtoms374.innerACB_eq,
    HexagonAtoms374.assocBCA_eq,
    HexagonAtoms374.innerRightBAC_eq,
    HexagonAtoms374.assocCAB_eq,
    HexagonAtoms374.outerLeftABC_eq,
    HexagonRowColumn374.product0_eq,
    HexagonRowColumn374.product1_eq,
    HexagonRowColumn374.product2_eq,
    HexagonRowColumn374.product3_eq,
    HexagonRowColumn374.product4_eq,
    HexagonRowColumn374.product5_eq,
    HexagonRowColumn374.product6_eq,
    HexagonRowColumn374.product7_eq] using left1Middle3_eq_case_7_4_checked

private theorem right0Middle3_eq_case_7_4_row_0_0_0 : (right0Middle3 7 4) ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4)) = (HexagonAtoms374.assocABC) ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_7_4_row_0_0_1 : (right0Middle3 7 4) ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4)) = (HexagonAtoms374.assocABC) ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_7_4_row_0_0_2 : (right0Middle3 7 4) ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4)) = (HexagonAtoms374.assocABC) ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_7_4_row_0_0_3 : (right0Middle3 7 4) ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4)) = (HexagonAtoms374.assocABC) ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_7_4_row_0_1_0 : (right0Middle3 7 4) ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4)) = (HexagonAtoms374.assocABC) ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_7_4_row_0_1_1 : (right0Middle3 7 4) ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4)) = (HexagonAtoms374.assocABC) ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_7_4_row_0_1_2 : (right0Middle3 7 4) ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4)) = (HexagonAtoms374.assocABC) ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_7_4_row_0_1_3 : (right0Middle3 7 4) ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4)) = (HexagonAtoms374.assocABC) ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_7_4_row_0_2_0 : (right0Middle3 7 4) ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4)) = (HexagonAtoms374.assocABC) ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_7_4_row_0_2_1 : (right0Middle3 7 4) ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4)) = (HexagonAtoms374.assocABC) ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_7_4_row_0_2_2 : (right0Middle3 7 4) ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4)) = (HexagonAtoms374.assocABC) ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_7_4_row_0_2_3 : (right0Middle3 7 4) ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4)) = (HexagonAtoms374.assocABC) ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_7_4_row_0_3_0 : (right0Middle3 7 4) ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4)) = (HexagonAtoms374.assocABC) ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_7_4_row_0_3_1 : (right0Middle3 7 4) ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4)) = (HexagonAtoms374.assocABC) ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_7_4_row_0_3_2 : (right0Middle3 7 4) ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4)) = (HexagonAtoms374.assocABC) ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_7_4_row_0_3_3 : (right0Middle3 7 4) ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4)) = (HexagonAtoms374.assocABC) ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_7_4_checked : right0Middle3 7 4 = HexagonAtoms374.assocABC := by
  funext r
  fin_cases r
  · exact right0Middle3_eq_case_7_4_row_0_0_0
  · exact right0Middle3_eq_case_7_4_row_0_0_1
  · exact right0Middle3_eq_case_7_4_row_0_0_2
  · exact right0Middle3_eq_case_7_4_row_0_0_3
  · exact right0Middle3_eq_case_7_4_row_0_1_0
  · exact right0Middle3_eq_case_7_4_row_0_1_1
  · exact right0Middle3_eq_case_7_4_row_0_1_2
  · exact right0Middle3_eq_case_7_4_row_0_1_3
  · exact right0Middle3_eq_case_7_4_row_0_2_0
  · exact right0Middle3_eq_case_7_4_row_0_2_1
  · exact right0Middle3_eq_case_7_4_row_0_2_2
  · exact right0Middle3_eq_case_7_4_row_0_2_3
  · exact right0Middle3_eq_case_7_4_row_0_3_0
  · exact right0Middle3_eq_case_7_4_row_0_3_1
  · exact right0Middle3_eq_case_7_4_row_0_3_2
  · exact right0Middle3_eq_case_7_4_row_0_3_3

set_option backward.isDefEq.respectTransparency false in
theorem right0Middle3_eq_case_7_4 : right0Middle3 7 4 = innerRightZ 3 7 4 * associatorZ 3 7 4 := by
  simpa only [HexagonAtoms374.assocABC_eq,
    HexagonAtoms374.outerABC_eq,
    HexagonAtoms374.assocBAC_eq,
    HexagonAtoms374.innerABC_eq,
    HexagonAtoms374.innerRightABC_eq,
    HexagonAtoms374.inverseACB_eq,
    HexagonAtoms374.innerACB_eq,
    HexagonAtoms374.assocBCA_eq,
    HexagonAtoms374.innerRightBAC_eq,
    HexagonAtoms374.assocCAB_eq,
    HexagonAtoms374.outerLeftABC_eq,
    HexagonRowColumn374.product0_eq,
    HexagonRowColumn374.product1_eq,
    HexagonRowColumn374.product2_eq,
    HexagonRowColumn374.product3_eq,
    HexagonRowColumn374.product4_eq,
    HexagonRowColumn374.product5_eq,
    HexagonRowColumn374.product6_eq,
    HexagonRowColumn374.product7_eq] using right0Middle3_eq_case_7_4_checked

private theorem right1Middle3_eq_case_7_4_row_0_0_0 : (right1Middle3 7 4) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn374.rows_inverseACB HexagonRowColumn374.cols_right0) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_7_4_row_0_0_1 : (right1Middle3 7 4) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn374.rows_inverseACB HexagonRowColumn374.cols_right0) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_7_4_row_0_0_2 : (right1Middle3 7 4) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn374.rows_inverseACB HexagonRowColumn374.cols_right0) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_7_4_row_0_0_3 : (right1Middle3 7 4) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn374.rows_inverseACB HexagonRowColumn374.cols_right0) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_7_4_row_1_0_0 : (right1Middle3 7 4) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn374.rows_inverseACB HexagonRowColumn374.cols_right0) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_7_4_row_1_0_1 : (right1Middle3 7 4) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn374.rows_inverseACB HexagonRowColumn374.cols_right0) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_7_4_row_1_0_2 : (right1Middle3 7 4) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn374.rows_inverseACB HexagonRowColumn374.cols_right0) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_7_4_row_1_0_3 : (right1Middle3 7 4) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn374.rows_inverseACB HexagonRowColumn374.cols_right0) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_7_4_row_2_0_0 : (right1Middle3 7 4) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn374.rows_inverseACB HexagonRowColumn374.cols_right0) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_7_4_row_2_0_1 : (right1Middle3 7 4) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn374.rows_inverseACB HexagonRowColumn374.cols_right0) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_7_4_row_2_0_2 : (right1Middle3 7 4) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn374.rows_inverseACB HexagonRowColumn374.cols_right0) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_7_4_row_2_0_3 : (right1Middle3 7 4) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn374.rows_inverseACB HexagonRowColumn374.cols_right0) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_7_4_row_3_0_0 : (right1Middle3 7 4) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn374.rows_inverseACB HexagonRowColumn374.cols_right0) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_7_4_row_3_0_1 : (right1Middle3 7 4) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn374.rows_inverseACB HexagonRowColumn374.cols_right0) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_7_4_row_3_0_2 : (right1Middle3 7 4) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn374.rows_inverseACB HexagonRowColumn374.cols_right0) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_7_4_row_3_0_3 : (right1Middle3 7 4) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn374.rows_inverseACB HexagonRowColumn374.cols_right0) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_7_4_checked : right1Middle3 7 4 = rowColumnMul HexagonRowColumn374.rows_inverseACB HexagonRowColumn374.cols_right0 := by
  funext r
  fin_cases r
  · exact right1Middle3_eq_case_7_4_row_0_0_0
  · exact right1Middle3_eq_case_7_4_row_0_0_1
  · exact right1Middle3_eq_case_7_4_row_0_0_2
  · exact right1Middle3_eq_case_7_4_row_0_0_3
  · exact right1Middle3_eq_case_7_4_row_1_0_0
  · exact right1Middle3_eq_case_7_4_row_1_0_1
  · exact right1Middle3_eq_case_7_4_row_1_0_2
  · exact right1Middle3_eq_case_7_4_row_1_0_3
  · exact right1Middle3_eq_case_7_4_row_2_0_0
  · exact right1Middle3_eq_case_7_4_row_2_0_1
  · exact right1Middle3_eq_case_7_4_row_2_0_2
  · exact right1Middle3_eq_case_7_4_row_2_0_3
  · exact right1Middle3_eq_case_7_4_row_3_0_0
  · exact right1Middle3_eq_case_7_4_row_3_0_1
  · exact right1Middle3_eq_case_7_4_row_3_0_2
  · exact right1Middle3_eq_case_7_4_row_3_0_3

set_option backward.isDefEq.respectTransparency false in
theorem right1Middle3_eq_case_7_4 : right1Middle3 7 4 = associatorInverseZ 3 4 7 * right0Middle3 7 4 := by
  simpa only [HexagonAtoms374.assocABC_eq,
    HexagonAtoms374.outerABC_eq,
    HexagonAtoms374.assocBAC_eq,
    HexagonAtoms374.innerABC_eq,
    HexagonAtoms374.innerRightABC_eq,
    HexagonAtoms374.inverseACB_eq,
    HexagonAtoms374.innerACB_eq,
    HexagonAtoms374.assocBCA_eq,
    HexagonAtoms374.innerRightBAC_eq,
    HexagonAtoms374.assocCAB_eq,
    HexagonAtoms374.outerLeftABC_eq,
    HexagonRowColumn374.product0_eq,
    HexagonRowColumn374.product1_eq,
    HexagonRowColumn374.product2_eq,
    HexagonRowColumn374.product3_eq,
    HexagonRowColumn374.product4_eq,
    HexagonRowColumn374.product5_eq,
    HexagonRowColumn374.product6_eq,
    HexagonRowColumn374.product7_eq] using right1Middle3_eq_case_7_4_checked

private theorem right2Middle3_eq_case_7_4_row_0_0_0 : (right2Middle3 7 4) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (right1Middle3 7 4) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_7_4_row_0_0_1 : (right2Middle3 7 4) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (right1Middle3 7 4) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_7_4_row_0_0_2 : (right2Middle3 7 4) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (right1Middle3 7 4) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_7_4_row_0_0_3 : (right2Middle3 7 4) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (right1Middle3 7 4) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_7_4_row_1_0_0 : (right2Middle3 7 4) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (right1Middle3 7 4) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_7_4_row_1_0_1 : (right2Middle3 7 4) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (right1Middle3 7 4) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_7_4_row_1_0_2 : (right2Middle3 7 4) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (right1Middle3 7 4) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_7_4_row_1_0_3 : (right2Middle3 7 4) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (right1Middle3 7 4) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_7_4_row_2_0_0 : (right2Middle3 7 4) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (right1Middle3 7 4) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_7_4_row_2_0_1 : (right2Middle3 7 4) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (right1Middle3 7 4) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_7_4_row_2_0_2 : (right2Middle3 7 4) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (right1Middle3 7 4) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_7_4_row_2_0_3 : (right2Middle3 7 4) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (right1Middle3 7 4) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_7_4_row_3_0_0 : (right2Middle3 7 4) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (right1Middle3 7 4) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_7_4_row_3_0_1 : (right2Middle3 7 4) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (right1Middle3 7 4) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_7_4_row_3_0_2 : (right2Middle3 7 4) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (right1Middle3 7 4) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_7_4_row_3_0_3 : (right2Middle3 7 4) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (right1Middle3 7 4) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_7_4_checked : right2Middle3 7 4 = right1Middle3 7 4 := by
  funext r
  fin_cases r
  · exact right2Middle3_eq_case_7_4_row_0_0_0
  · exact right2Middle3_eq_case_7_4_row_0_0_1
  · exact right2Middle3_eq_case_7_4_row_0_0_2
  · exact right2Middle3_eq_case_7_4_row_0_0_3
  · exact right2Middle3_eq_case_7_4_row_1_0_0
  · exact right2Middle3_eq_case_7_4_row_1_0_1
  · exact right2Middle3_eq_case_7_4_row_1_0_2
  · exact right2Middle3_eq_case_7_4_row_1_0_3
  · exact right2Middle3_eq_case_7_4_row_2_0_0
  · exact right2Middle3_eq_case_7_4_row_2_0_1
  · exact right2Middle3_eq_case_7_4_row_2_0_2
  · exact right2Middle3_eq_case_7_4_row_2_0_3
  · exact right2Middle3_eq_case_7_4_row_3_0_0
  · exact right2Middle3_eq_case_7_4_row_3_0_1
  · exact right2Middle3_eq_case_7_4_row_3_0_2
  · exact right2Middle3_eq_case_7_4_row_3_0_3

set_option backward.isDefEq.respectTransparency false in
theorem right2Middle3_eq_case_7_4 : right2Middle3 7 4 = innerLeftZ 3 4 7 * right1Middle3 7 4 := by
  simpa only [HexagonAtoms374.assocABC_eq,
    HexagonAtoms374.outerABC_eq,
    HexagonAtoms374.assocBAC_eq,
    HexagonAtoms374.innerABC_eq,
    HexagonAtoms374.innerRightABC_eq,
    HexagonAtoms374.inverseACB_eq,
    HexagonAtoms374.innerACB_eq,
    HexagonAtoms374.assocBCA_eq,
    HexagonAtoms374.innerRightBAC_eq,
    HexagonAtoms374.assocCAB_eq,
    HexagonAtoms374.outerLeftABC_eq,
    HexagonRowColumn374.product0_eq,
    HexagonRowColumn374.product1_eq,
    HexagonRowColumn374.product2_eq,
    HexagonRowColumn374.product3_eq,
    HexagonRowColumn374.product4_eq,
    HexagonRowColumn374.product5_eq,
    HexagonRowColumn374.product6_eq,
    HexagonRowColumn374.product7_eq] using right2Middle3_eq_case_7_4_checked

private theorem leftFinal3_case_7_4_row_0_0_0 : (((-1 : ℤ) ^ (leftScaleBit 3 7 4).val * positiveScale (leftScaleExponent 3 7 4)) •
      (rowColumnMul HexagonRowColumn374.rows_assocBCA HexagonRowColumn374.cols_left0)) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (negativeScale (leftScaleExponent 3 7 4) • (left1Middle3 7 4)) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal3_case_7_4_row_0_0_1 : (((-1 : ℤ) ^ (leftScaleBit 3 7 4).val * positiveScale (leftScaleExponent 3 7 4)) •
      (rowColumnMul HexagonRowColumn374.rows_assocBCA HexagonRowColumn374.cols_left0)) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (negativeScale (leftScaleExponent 3 7 4) • (left1Middle3 7 4)) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal3_case_7_4_row_0_0_2 : (((-1 : ℤ) ^ (leftScaleBit 3 7 4).val * positiveScale (leftScaleExponent 3 7 4)) •
      (rowColumnMul HexagonRowColumn374.rows_assocBCA HexagonRowColumn374.cols_left0)) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (negativeScale (leftScaleExponent 3 7 4) • (left1Middle3 7 4)) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal3_case_7_4_row_0_0_3 : (((-1 : ℤ) ^ (leftScaleBit 3 7 4).val * positiveScale (leftScaleExponent 3 7 4)) •
      (rowColumnMul HexagonRowColumn374.rows_assocBCA HexagonRowColumn374.cols_left0)) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (negativeScale (leftScaleExponent 3 7 4) • (left1Middle3 7 4)) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal3_case_7_4_row_1_0_0 : (((-1 : ℤ) ^ (leftScaleBit 3 7 4).val * positiveScale (leftScaleExponent 3 7 4)) •
      (rowColumnMul HexagonRowColumn374.rows_assocBCA HexagonRowColumn374.cols_left0)) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (negativeScale (leftScaleExponent 3 7 4) • (left1Middle3 7 4)) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal3_case_7_4_row_1_0_1 : (((-1 : ℤ) ^ (leftScaleBit 3 7 4).val * positiveScale (leftScaleExponent 3 7 4)) •
      (rowColumnMul HexagonRowColumn374.rows_assocBCA HexagonRowColumn374.cols_left0)) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (negativeScale (leftScaleExponent 3 7 4) • (left1Middle3 7 4)) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal3_case_7_4_row_1_0_2 : (((-1 : ℤ) ^ (leftScaleBit 3 7 4).val * positiveScale (leftScaleExponent 3 7 4)) •
      (rowColumnMul HexagonRowColumn374.rows_assocBCA HexagonRowColumn374.cols_left0)) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (negativeScale (leftScaleExponent 3 7 4) • (left1Middle3 7 4)) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal3_case_7_4_row_1_0_3 : (((-1 : ℤ) ^ (leftScaleBit 3 7 4).val * positiveScale (leftScaleExponent 3 7 4)) •
      (rowColumnMul HexagonRowColumn374.rows_assocBCA HexagonRowColumn374.cols_left0)) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (negativeScale (leftScaleExponent 3 7 4) • (left1Middle3 7 4)) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal3_case_7_4_row_2_0_0 : (((-1 : ℤ) ^ (leftScaleBit 3 7 4).val * positiveScale (leftScaleExponent 3 7 4)) •
      (rowColumnMul HexagonRowColumn374.rows_assocBCA HexagonRowColumn374.cols_left0)) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (negativeScale (leftScaleExponent 3 7 4) • (left1Middle3 7 4)) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal3_case_7_4_row_2_0_1 : (((-1 : ℤ) ^ (leftScaleBit 3 7 4).val * positiveScale (leftScaleExponent 3 7 4)) •
      (rowColumnMul HexagonRowColumn374.rows_assocBCA HexagonRowColumn374.cols_left0)) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (negativeScale (leftScaleExponent 3 7 4) • (left1Middle3 7 4)) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal3_case_7_4_row_2_0_2 : (((-1 : ℤ) ^ (leftScaleBit 3 7 4).val * positiveScale (leftScaleExponent 3 7 4)) •
      (rowColumnMul HexagonRowColumn374.rows_assocBCA HexagonRowColumn374.cols_left0)) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (negativeScale (leftScaleExponent 3 7 4) • (left1Middle3 7 4)) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal3_case_7_4_row_2_0_3 : (((-1 : ℤ) ^ (leftScaleBit 3 7 4).val * positiveScale (leftScaleExponent 3 7 4)) •
      (rowColumnMul HexagonRowColumn374.rows_assocBCA HexagonRowColumn374.cols_left0)) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (negativeScale (leftScaleExponent 3 7 4) • (left1Middle3 7 4)) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal3_case_7_4_row_3_0_0 : (((-1 : ℤ) ^ (leftScaleBit 3 7 4).val * positiveScale (leftScaleExponent 3 7 4)) •
      (rowColumnMul HexagonRowColumn374.rows_assocBCA HexagonRowColumn374.cols_left0)) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (negativeScale (leftScaleExponent 3 7 4) • (left1Middle3 7 4)) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal3_case_7_4_row_3_0_1 : (((-1 : ℤ) ^ (leftScaleBit 3 7 4).val * positiveScale (leftScaleExponent 3 7 4)) •
      (rowColumnMul HexagonRowColumn374.rows_assocBCA HexagonRowColumn374.cols_left0)) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (negativeScale (leftScaleExponent 3 7 4) • (left1Middle3 7 4)) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal3_case_7_4_row_3_0_2 : (((-1 : ℤ) ^ (leftScaleBit 3 7 4).val * positiveScale (leftScaleExponent 3 7 4)) •
      (rowColumnMul HexagonRowColumn374.rows_assocBCA HexagonRowColumn374.cols_left0)) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (negativeScale (leftScaleExponent 3 7 4) • (left1Middle3 7 4)) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal3_case_7_4_row_3_0_3 : (((-1 : ℤ) ^ (leftScaleBit 3 7 4).val * positiveScale (leftScaleExponent 3 7 4)) •
      (rowColumnMul HexagonRowColumn374.rows_assocBCA HexagonRowColumn374.cols_left0)) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (negativeScale (leftScaleExponent 3 7 4) • (left1Middle3 7 4)) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal3_case_7_4_checked : ((-1 : ℤ) ^ (leftScaleBit 3 7 4).val * positiveScale (leftScaleExponent 3 7 4)) •
      (rowColumnMul HexagonRowColumn374.rows_assocBCA HexagonRowColumn374.cols_left0) = negativeScale (leftScaleExponent 3 7 4) • (left1Middle3 7 4) := by
  funext r
  fin_cases r
  · exact leftFinal3_case_7_4_row_0_0_0
  · exact leftFinal3_case_7_4_row_0_0_1
  · exact leftFinal3_case_7_4_row_0_0_2
  · exact leftFinal3_case_7_4_row_0_0_3
  · exact leftFinal3_case_7_4_row_1_0_0
  · exact leftFinal3_case_7_4_row_1_0_1
  · exact leftFinal3_case_7_4_row_1_0_2
  · exact leftFinal3_case_7_4_row_1_0_3
  · exact leftFinal3_case_7_4_row_2_0_0
  · exact leftFinal3_case_7_4_row_2_0_1
  · exact leftFinal3_case_7_4_row_2_0_2
  · exact leftFinal3_case_7_4_row_2_0_3
  · exact leftFinal3_case_7_4_row_3_0_0
  · exact leftFinal3_case_7_4_row_3_0_1
  · exact leftFinal3_case_7_4_row_3_0_2
  · exact leftFinal3_case_7_4_row_3_0_3

set_option backward.isDefEq.respectTransparency false in
theorem leftFinal3_case_7_4 : ((-1 : ℤ) ^ (leftScaleBit 3 7 4).val * positiveScale (leftScaleExponent 3 7 4)) •
      (associatorZ 7 4 3 * left0Middle3 7 4) = negativeScale (leftScaleExponent 3 7 4) • (innerRightZ 7 3 4 * left1Middle3 7 4) := by
  simpa only [HexagonAtoms374.assocABC_eq,
    HexagonAtoms374.outerABC_eq,
    HexagonAtoms374.assocBAC_eq,
    HexagonAtoms374.innerABC_eq,
    HexagonAtoms374.innerRightABC_eq,
    HexagonAtoms374.inverseACB_eq,
    HexagonAtoms374.innerACB_eq,
    HexagonAtoms374.assocBCA_eq,
    HexagonAtoms374.innerRightBAC_eq,
    HexagonAtoms374.assocCAB_eq,
    HexagonAtoms374.outerLeftABC_eq,
    HexagonRowColumn374.product0_eq,
    HexagonRowColumn374.product1_eq,
    HexagonRowColumn374.product2_eq,
    HexagonRowColumn374.product3_eq,
    HexagonRowColumn374.product4_eq,
    HexagonRowColumn374.product5_eq,
    HexagonRowColumn374.product6_eq,
    HexagonRowColumn374.product7_eq] using leftFinal3_case_7_4_checked

private theorem rightFinal3_case_7_4_row_0_0_0 : (((-1 : ℤ) ^ (rightScaleBit 3 7 4).val * positiveScale (rightScaleExponent 3 7 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 4 7 : ℤ)) • HexagonAtoms374.outerLeftABC) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 3 7 4) • (rowColumnMul HexagonRowColumn374.rows_assocCAB HexagonRowColumn374.cols_right2)) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal3_case_7_4_row_0_0_1 : (((-1 : ℤ) ^ (rightScaleBit 3 7 4).val * positiveScale (rightScaleExponent 3 7 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 4 7 : ℤ)) • HexagonAtoms374.outerLeftABC) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 3 7 4) • (rowColumnMul HexagonRowColumn374.rows_assocCAB HexagonRowColumn374.cols_right2)) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal3_case_7_4_row_0_0_2 : (((-1 : ℤ) ^ (rightScaleBit 3 7 4).val * positiveScale (rightScaleExponent 3 7 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 4 7 : ℤ)) • HexagonAtoms374.outerLeftABC) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 3 7 4) • (rowColumnMul HexagonRowColumn374.rows_assocCAB HexagonRowColumn374.cols_right2)) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal3_case_7_4_row_0_0_3 : (((-1 : ℤ) ^ (rightScaleBit 3 7 4).val * positiveScale (rightScaleExponent 3 7 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 4 7 : ℤ)) • HexagonAtoms374.outerLeftABC) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 3 7 4) • (rowColumnMul HexagonRowColumn374.rows_assocCAB HexagonRowColumn374.cols_right2)) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal3_case_7_4_row_0_1_0 : (((-1 : ℤ) ^ (rightScaleBit 3 7 4).val * positiveScale (rightScaleExponent 3 7 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 4 7 : ℤ)) • HexagonAtoms374.outerLeftABC) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 3 7 4) • (rowColumnMul HexagonRowColumn374.rows_assocCAB HexagonRowColumn374.cols_right2)) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal3_case_7_4_row_0_1_1 : (((-1 : ℤ) ^ (rightScaleBit 3 7 4).val * positiveScale (rightScaleExponent 3 7 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 4 7 : ℤ)) • HexagonAtoms374.outerLeftABC) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 3 7 4) • (rowColumnMul HexagonRowColumn374.rows_assocCAB HexagonRowColumn374.cols_right2)) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal3_case_7_4_row_0_1_2 : (((-1 : ℤ) ^ (rightScaleBit 3 7 4).val * positiveScale (rightScaleExponent 3 7 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 4 7 : ℤ)) • HexagonAtoms374.outerLeftABC) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 3 7 4) • (rowColumnMul HexagonRowColumn374.rows_assocCAB HexagonRowColumn374.cols_right2)) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal3_case_7_4_row_0_1_3 : (((-1 : ℤ) ^ (rightScaleBit 3 7 4).val * positiveScale (rightScaleExponent 3 7 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 4 7 : ℤ)) • HexagonAtoms374.outerLeftABC) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 3 7 4) • (rowColumnMul HexagonRowColumn374.rows_assocCAB HexagonRowColumn374.cols_right2)) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal3_case_7_4_row_1_0_0 : (((-1 : ℤ) ^ (rightScaleBit 3 7 4).val * positiveScale (rightScaleExponent 3 7 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 4 7 : ℤ)) • HexagonAtoms374.outerLeftABC) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 3 7 4) • (rowColumnMul HexagonRowColumn374.rows_assocCAB HexagonRowColumn374.cols_right2)) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal3_case_7_4_row_1_0_1 : (((-1 : ℤ) ^ (rightScaleBit 3 7 4).val * positiveScale (rightScaleExponent 3 7 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 4 7 : ℤ)) • HexagonAtoms374.outerLeftABC) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 3 7 4) • (rowColumnMul HexagonRowColumn374.rows_assocCAB HexagonRowColumn374.cols_right2)) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal3_case_7_4_row_1_0_2 : (((-1 : ℤ) ^ (rightScaleBit 3 7 4).val * positiveScale (rightScaleExponent 3 7 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 4 7 : ℤ)) • HexagonAtoms374.outerLeftABC) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 3 7 4) • (rowColumnMul HexagonRowColumn374.rows_assocCAB HexagonRowColumn374.cols_right2)) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal3_case_7_4_row_1_0_3 : (((-1 : ℤ) ^ (rightScaleBit 3 7 4).val * positiveScale (rightScaleExponent 3 7 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 4 7 : ℤ)) • HexagonAtoms374.outerLeftABC) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 3 7 4) • (rowColumnMul HexagonRowColumn374.rows_assocCAB HexagonRowColumn374.cols_right2)) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal3_case_7_4_row_1_1_0 : (((-1 : ℤ) ^ (rightScaleBit 3 7 4).val * positiveScale (rightScaleExponent 3 7 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 4 7 : ℤ)) • HexagonAtoms374.outerLeftABC) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 3 7 4) • (rowColumnMul HexagonRowColumn374.rows_assocCAB HexagonRowColumn374.cols_right2)) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal3_case_7_4_row_1_1_1 : (((-1 : ℤ) ^ (rightScaleBit 3 7 4).val * positiveScale (rightScaleExponent 3 7 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 4 7 : ℤ)) • HexagonAtoms374.outerLeftABC) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 3 7 4) • (rowColumnMul HexagonRowColumn374.rows_assocCAB HexagonRowColumn374.cols_right2)) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal3_case_7_4_row_1_1_2 : (((-1 : ℤ) ^ (rightScaleBit 3 7 4).val * positiveScale (rightScaleExponent 3 7 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 4 7 : ℤ)) • HexagonAtoms374.outerLeftABC) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 3 7 4) • (rowColumnMul HexagonRowColumn374.rows_assocCAB HexagonRowColumn374.cols_right2)) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal3_case_7_4_row_1_1_3 : (((-1 : ℤ) ^ (rightScaleBit 3 7 4).val * positiveScale (rightScaleExponent 3 7 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 4 7 : ℤ)) • HexagonAtoms374.outerLeftABC) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 3 7 4) • (rowColumnMul HexagonRowColumn374.rows_assocCAB HexagonRowColumn374.cols_right2)) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal3_case_7_4_checked : ((-1 : ℤ) ^ (rightScaleBit 3 7 4).val * positiveScale (rightScaleExponent 3 7 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 4 7 : ℤ)) • HexagonAtoms374.outerLeftABC = negativeScale (rightScaleExponent 3 7 4) • (rowColumnMul HexagonRowColumn374.rows_assocCAB HexagonRowColumn374.cols_right2) := by
  funext r
  fin_cases r
  · exact rightFinal3_case_7_4_row_0_0_0
  · exact rightFinal3_case_7_4_row_0_0_1
  · exact rightFinal3_case_7_4_row_0_0_2
  · exact rightFinal3_case_7_4_row_0_0_3
  · exact rightFinal3_case_7_4_row_0_1_0
  · exact rightFinal3_case_7_4_row_0_1_1
  · exact rightFinal3_case_7_4_row_0_1_2
  · exact rightFinal3_case_7_4_row_0_1_3
  · exact rightFinal3_case_7_4_row_1_0_0
  · exact rightFinal3_case_7_4_row_1_0_1
  · exact rightFinal3_case_7_4_row_1_0_2
  · exact rightFinal3_case_7_4_row_1_0_3
  · exact rightFinal3_case_7_4_row_1_1_0
  · exact rightFinal3_case_7_4_row_1_1_1
  · exact rightFinal3_case_7_4_row_1_1_2
  · exact rightFinal3_case_7_4_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem rightFinal3_case_7_4 : ((-1 : ℤ) ^ (rightScaleBit 3 7 4).val * positiveScale (rightScaleExponent 3 7 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 4 7 : ℤ)) • outerLeftZ 3 7 4 = negativeScale (rightScaleExponent 3 7 4) • (associatorZ 4 3 7 * right2Middle3 7 4) := by
  simpa only [HexagonAtoms374.assocABC_eq,
    HexagonAtoms374.outerABC_eq,
    HexagonAtoms374.assocBAC_eq,
    HexagonAtoms374.innerABC_eq,
    HexagonAtoms374.innerRightABC_eq,
    HexagonAtoms374.inverseACB_eq,
    HexagonAtoms374.innerACB_eq,
    HexagonAtoms374.assocBCA_eq,
    HexagonAtoms374.innerRightBAC_eq,
    HexagonAtoms374.assocCAB_eq,
    HexagonAtoms374.outerLeftABC_eq,
    HexagonRowColumn374.product0_eq,
    HexagonRowColumn374.product1_eq,
    HexagonRowColumn374.product2_eq,
    HexagonRowColumn374.product3_eq,
    HexagonRowColumn374.product4_eq,
    HexagonRowColumn374.product5_eq,
    HexagonRowColumn374.product6_eq,
    HexagonRowColumn374.product7_eq] using rightFinal3_case_7_4_checked

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonCases3
