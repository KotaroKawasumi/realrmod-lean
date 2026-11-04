import RMod.BrundanEllis.StackingReferenceHexagonMiddle3
import RMod.BrundanEllis.StackingReferenceSparseMatrixCheck
import RMod.BrundanEllis.StackingReferenceHexagonAtoms323
import RMod.BrundanEllis.StackingReferenceHexagonRowColumn323

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

private theorem left0Middle3_eq_case_2_3_row_0_0_0 : (left0Middle3 2 3) ((0 : Fin 2), (0 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn323.rows_outerABC HexagonRowColumn323.cols_assocABC) ((0 : Fin 2), (0 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem left0Middle3_eq_case_2_3_row_0_1_0 : (left0Middle3 2 3) ((0 : Fin 2), (1 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn323.rows_outerABC HexagonRowColumn323.cols_assocABC) ((0 : Fin 2), (1 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem left0Middle3_eq_case_2_3_row_0_2_0 : (left0Middle3 2 3) ((0 : Fin 2), (2 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn323.rows_outerABC HexagonRowColumn323.cols_assocABC) ((0 : Fin 2), (2 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem left0Middle3_eq_case_2_3_row_0_3_0 : (left0Middle3 2 3) ((0 : Fin 2), (3 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn323.rows_outerABC HexagonRowColumn323.cols_assocABC) ((0 : Fin 2), (3 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem left0Middle3_eq_case_2_3_row_0_4_0 : (left0Middle3 2 3) ((0 : Fin 2), (4 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn323.rows_outerABC HexagonRowColumn323.cols_assocABC) ((0 : Fin 2), (4 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem left0Middle3_eq_case_2_3_row_0_5_0 : (left0Middle3 2 3) ((0 : Fin 2), (5 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn323.rows_outerABC HexagonRowColumn323.cols_assocABC) ((0 : Fin 2), (5 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem left0Middle3_eq_case_2_3_row_0_6_0 : (left0Middle3 2 3) ((0 : Fin 2), (6 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn323.rows_outerABC HexagonRowColumn323.cols_assocABC) ((0 : Fin 2), (6 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem left0Middle3_eq_case_2_3_row_0_7_0 : (left0Middle3 2 3) ((0 : Fin 2), (7 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn323.rows_outerABC HexagonRowColumn323.cols_assocABC) ((0 : Fin 2), (7 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem left0Middle3_eq_case_2_3_row_1_0_0 : (left0Middle3 2 3) ((1 : Fin 2), (0 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn323.rows_outerABC HexagonRowColumn323.cols_assocABC) ((1 : Fin 2), (0 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem left0Middle3_eq_case_2_3_row_1_1_0 : (left0Middle3 2 3) ((1 : Fin 2), (1 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn323.rows_outerABC HexagonRowColumn323.cols_assocABC) ((1 : Fin 2), (1 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem left0Middle3_eq_case_2_3_row_1_2_0 : (left0Middle3 2 3) ((1 : Fin 2), (2 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn323.rows_outerABC HexagonRowColumn323.cols_assocABC) ((1 : Fin 2), (2 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem left0Middle3_eq_case_2_3_row_1_3_0 : (left0Middle3 2 3) ((1 : Fin 2), (3 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn323.rows_outerABC HexagonRowColumn323.cols_assocABC) ((1 : Fin 2), (3 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem left0Middle3_eq_case_2_3_row_1_4_0 : (left0Middle3 2 3) ((1 : Fin 2), (4 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn323.rows_outerABC HexagonRowColumn323.cols_assocABC) ((1 : Fin 2), (4 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem left0Middle3_eq_case_2_3_row_1_5_0 : (left0Middle3 2 3) ((1 : Fin 2), (5 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn323.rows_outerABC HexagonRowColumn323.cols_assocABC) ((1 : Fin 2), (5 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem left0Middle3_eq_case_2_3_row_1_6_0 : (left0Middle3 2 3) ((1 : Fin 2), (6 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn323.rows_outerABC HexagonRowColumn323.cols_assocABC) ((1 : Fin 2), (6 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem left0Middle3_eq_case_2_3_row_1_7_0 : (left0Middle3 2 3) ((1 : Fin 2), (7 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn323.rows_outerABC HexagonRowColumn323.cols_assocABC) ((1 : Fin 2), (7 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem left0Middle3_eq_case_2_3_checked : left0Middle3 2 3 = rowColumnMul HexagonRowColumn323.rows_outerABC HexagonRowColumn323.cols_assocABC := by
  funext r
  fin_cases r
  · exact left0Middle3_eq_case_2_3_row_0_0_0
  · exact left0Middle3_eq_case_2_3_row_0_1_0
  · exact left0Middle3_eq_case_2_3_row_0_2_0
  · exact left0Middle3_eq_case_2_3_row_0_3_0
  · exact left0Middle3_eq_case_2_3_row_0_4_0
  · exact left0Middle3_eq_case_2_3_row_0_5_0
  · exact left0Middle3_eq_case_2_3_row_0_6_0
  · exact left0Middle3_eq_case_2_3_row_0_7_0
  · exact left0Middle3_eq_case_2_3_row_1_0_0
  · exact left0Middle3_eq_case_2_3_row_1_1_0
  · exact left0Middle3_eq_case_2_3_row_1_2_0
  · exact left0Middle3_eq_case_2_3_row_1_3_0
  · exact left0Middle3_eq_case_2_3_row_1_4_0
  · exact left0Middle3_eq_case_2_3_row_1_5_0
  · exact left0Middle3_eq_case_2_3_row_1_6_0
  · exact left0Middle3_eq_case_2_3_row_1_7_0

set_option backward.isDefEq.respectTransparency false in
theorem left0Middle3_eq_case_2_3 : left0Middle3 2 3 = outerRightZ 3 2 3 * associatorZ 3 2 3 := by
  simpa only [HexagonAtoms323.assocABC_eq,
    HexagonAtoms323.outerABC_eq,
    HexagonAtoms323.assocBAC_eq,
    HexagonAtoms323.innerABC_eq,
    HexagonAtoms323.innerRightABC_eq,
    HexagonAtoms323.inverseACB_eq,
    HexagonAtoms323.innerACB_eq,
    HexagonAtoms323.assocBCA_eq,
    HexagonAtoms323.innerRightBAC_eq,
    HexagonAtoms323.assocCAB_eq,
    HexagonAtoms323.outerLeftABC_eq,
    HexagonRowColumn323.assocBCA_alias,
    HexagonRowColumn323.product0_eq,
    HexagonRowColumn323.product1_eq,
    HexagonRowColumn323.product2_eq,
    HexagonRowColumn323.product3_eq,
    HexagonRowColumn323.product4_eq,
    HexagonRowColumn323.product5_eq,
    HexagonRowColumn323.product6_eq,
    HexagonRowColumn323.product7_eq] using left0Middle3_eq_case_2_3_checked

private theorem left1Middle3_eq_case_2_3_row_0_0_0 : (left1Middle3 2 3) ((0 : Fin 4), (0 : Fin 4), (0 : Fin 1)) = (HexagonAtoms323.assocBAC) ((0 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem left1Middle3_eq_case_2_3_row_0_1_0 : (left1Middle3 2 3) ((0 : Fin 4), (1 : Fin 4), (0 : Fin 1)) = (HexagonAtoms323.assocBAC) ((0 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem left1Middle3_eq_case_2_3_row_0_2_0 : (left1Middle3 2 3) ((0 : Fin 4), (2 : Fin 4), (0 : Fin 1)) = (HexagonAtoms323.assocBAC) ((0 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem left1Middle3_eq_case_2_3_row_0_3_0 : (left1Middle3 2 3) ((0 : Fin 4), (3 : Fin 4), (0 : Fin 1)) = (HexagonAtoms323.assocBAC) ((0 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem left1Middle3_eq_case_2_3_row_1_0_0 : (left1Middle3 2 3) ((1 : Fin 4), (0 : Fin 4), (0 : Fin 1)) = (HexagonAtoms323.assocBAC) ((1 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem left1Middle3_eq_case_2_3_row_1_1_0 : (left1Middle3 2 3) ((1 : Fin 4), (1 : Fin 4), (0 : Fin 1)) = (HexagonAtoms323.assocBAC) ((1 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem left1Middle3_eq_case_2_3_row_1_2_0 : (left1Middle3 2 3) ((1 : Fin 4), (2 : Fin 4), (0 : Fin 1)) = (HexagonAtoms323.assocBAC) ((1 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem left1Middle3_eq_case_2_3_row_1_3_0 : (left1Middle3 2 3) ((1 : Fin 4), (3 : Fin 4), (0 : Fin 1)) = (HexagonAtoms323.assocBAC) ((1 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem left1Middle3_eq_case_2_3_row_2_0_0 : (left1Middle3 2 3) ((2 : Fin 4), (0 : Fin 4), (0 : Fin 1)) = (HexagonAtoms323.assocBAC) ((2 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem left1Middle3_eq_case_2_3_row_2_1_0 : (left1Middle3 2 3) ((2 : Fin 4), (1 : Fin 4), (0 : Fin 1)) = (HexagonAtoms323.assocBAC) ((2 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem left1Middle3_eq_case_2_3_row_2_2_0 : (left1Middle3 2 3) ((2 : Fin 4), (2 : Fin 4), (0 : Fin 1)) = (HexagonAtoms323.assocBAC) ((2 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem left1Middle3_eq_case_2_3_row_2_3_0 : (left1Middle3 2 3) ((2 : Fin 4), (3 : Fin 4), (0 : Fin 1)) = (HexagonAtoms323.assocBAC) ((2 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem left1Middle3_eq_case_2_3_row_3_0_0 : (left1Middle3 2 3) ((3 : Fin 4), (0 : Fin 4), (0 : Fin 1)) = (HexagonAtoms323.assocBAC) ((3 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem left1Middle3_eq_case_2_3_row_3_1_0 : (left1Middle3 2 3) ((3 : Fin 4), (1 : Fin 4), (0 : Fin 1)) = (HexagonAtoms323.assocBAC) ((3 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem left1Middle3_eq_case_2_3_row_3_2_0 : (left1Middle3 2 3) ((3 : Fin 4), (2 : Fin 4), (0 : Fin 1)) = (HexagonAtoms323.assocBAC) ((3 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem left1Middle3_eq_case_2_3_row_3_3_0 : (left1Middle3 2 3) ((3 : Fin 4), (3 : Fin 4), (0 : Fin 1)) = (HexagonAtoms323.assocBAC) ((3 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem left1Middle3_eq_case_2_3_checked : left1Middle3 2 3 = HexagonAtoms323.assocBAC := by
  funext r
  fin_cases r
  · exact left1Middle3_eq_case_2_3_row_0_0_0
  · exact left1Middle3_eq_case_2_3_row_0_1_0
  · exact left1Middle3_eq_case_2_3_row_0_2_0
  · exact left1Middle3_eq_case_2_3_row_0_3_0
  · exact left1Middle3_eq_case_2_3_row_1_0_0
  · exact left1Middle3_eq_case_2_3_row_1_1_0
  · exact left1Middle3_eq_case_2_3_row_1_2_0
  · exact left1Middle3_eq_case_2_3_row_1_3_0
  · exact left1Middle3_eq_case_2_3_row_2_0_0
  · exact left1Middle3_eq_case_2_3_row_2_1_0
  · exact left1Middle3_eq_case_2_3_row_2_2_0
  · exact left1Middle3_eq_case_2_3_row_2_3_0
  · exact left1Middle3_eq_case_2_3_row_3_0_0
  · exact left1Middle3_eq_case_2_3_row_3_1_0
  · exact left1Middle3_eq_case_2_3_row_3_2_0
  · exact left1Middle3_eq_case_2_3_row_3_3_0

set_option backward.isDefEq.respectTransparency false in
theorem left1Middle3_eq_case_2_3 : left1Middle3 2 3 = associatorZ 2 3 3 * innerLeftZ 3 2 3 := by
  simpa only [HexagonAtoms323.assocABC_eq,
    HexagonAtoms323.outerABC_eq,
    HexagonAtoms323.assocBAC_eq,
    HexagonAtoms323.innerABC_eq,
    HexagonAtoms323.innerRightABC_eq,
    HexagonAtoms323.inverseACB_eq,
    HexagonAtoms323.innerACB_eq,
    HexagonAtoms323.assocBCA_eq,
    HexagonAtoms323.innerRightBAC_eq,
    HexagonAtoms323.assocCAB_eq,
    HexagonAtoms323.outerLeftABC_eq,
    HexagonRowColumn323.assocBCA_alias,
    HexagonRowColumn323.product0_eq,
    HexagonRowColumn323.product1_eq,
    HexagonRowColumn323.product2_eq,
    HexagonRowColumn323.product3_eq,
    HexagonRowColumn323.product4_eq,
    HexagonRowColumn323.product5_eq,
    HexagonRowColumn323.product6_eq,
    HexagonRowColumn323.product7_eq] using left1Middle3_eq_case_2_3_checked

private theorem right0Middle3_eq_case_2_3_row_0_0_0 : (right0Middle3 2 3) ((0 : Fin 2), (0 : Fin 8), (0 : Fin 1)) = (HexagonAtoms323.assocABC) ((0 : Fin 2), (0 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right0Middle3_eq_case_2_3_row_0_1_0 : (right0Middle3 2 3) ((0 : Fin 2), (1 : Fin 8), (0 : Fin 1)) = (HexagonAtoms323.assocABC) ((0 : Fin 2), (1 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right0Middle3_eq_case_2_3_row_0_2_0 : (right0Middle3 2 3) ((0 : Fin 2), (2 : Fin 8), (0 : Fin 1)) = (HexagonAtoms323.assocABC) ((0 : Fin 2), (2 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right0Middle3_eq_case_2_3_row_0_3_0 : (right0Middle3 2 3) ((0 : Fin 2), (3 : Fin 8), (0 : Fin 1)) = (HexagonAtoms323.assocABC) ((0 : Fin 2), (3 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right0Middle3_eq_case_2_3_row_0_4_0 : (right0Middle3 2 3) ((0 : Fin 2), (4 : Fin 8), (0 : Fin 1)) = (HexagonAtoms323.assocABC) ((0 : Fin 2), (4 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right0Middle3_eq_case_2_3_row_0_5_0 : (right0Middle3 2 3) ((0 : Fin 2), (5 : Fin 8), (0 : Fin 1)) = (HexagonAtoms323.assocABC) ((0 : Fin 2), (5 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right0Middle3_eq_case_2_3_row_0_6_0 : (right0Middle3 2 3) ((0 : Fin 2), (6 : Fin 8), (0 : Fin 1)) = (HexagonAtoms323.assocABC) ((0 : Fin 2), (6 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right0Middle3_eq_case_2_3_row_0_7_0 : (right0Middle3 2 3) ((0 : Fin 2), (7 : Fin 8), (0 : Fin 1)) = (HexagonAtoms323.assocABC) ((0 : Fin 2), (7 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right0Middle3_eq_case_2_3_row_1_0_0 : (right0Middle3 2 3) ((1 : Fin 2), (0 : Fin 8), (0 : Fin 1)) = (HexagonAtoms323.assocABC) ((1 : Fin 2), (0 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right0Middle3_eq_case_2_3_row_1_1_0 : (right0Middle3 2 3) ((1 : Fin 2), (1 : Fin 8), (0 : Fin 1)) = (HexagonAtoms323.assocABC) ((1 : Fin 2), (1 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right0Middle3_eq_case_2_3_row_1_2_0 : (right0Middle3 2 3) ((1 : Fin 2), (2 : Fin 8), (0 : Fin 1)) = (HexagonAtoms323.assocABC) ((1 : Fin 2), (2 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right0Middle3_eq_case_2_3_row_1_3_0 : (right0Middle3 2 3) ((1 : Fin 2), (3 : Fin 8), (0 : Fin 1)) = (HexagonAtoms323.assocABC) ((1 : Fin 2), (3 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right0Middle3_eq_case_2_3_row_1_4_0 : (right0Middle3 2 3) ((1 : Fin 2), (4 : Fin 8), (0 : Fin 1)) = (HexagonAtoms323.assocABC) ((1 : Fin 2), (4 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right0Middle3_eq_case_2_3_row_1_5_0 : (right0Middle3 2 3) ((1 : Fin 2), (5 : Fin 8), (0 : Fin 1)) = (HexagonAtoms323.assocABC) ((1 : Fin 2), (5 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right0Middle3_eq_case_2_3_row_1_6_0 : (right0Middle3 2 3) ((1 : Fin 2), (6 : Fin 8), (0 : Fin 1)) = (HexagonAtoms323.assocABC) ((1 : Fin 2), (6 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right0Middle3_eq_case_2_3_row_1_7_0 : (right0Middle3 2 3) ((1 : Fin 2), (7 : Fin 8), (0 : Fin 1)) = (HexagonAtoms323.assocABC) ((1 : Fin 2), (7 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right0Middle3_eq_case_2_3_checked : right0Middle3 2 3 = HexagonAtoms323.assocABC := by
  funext r
  fin_cases r
  · exact right0Middle3_eq_case_2_3_row_0_0_0
  · exact right0Middle3_eq_case_2_3_row_0_1_0
  · exact right0Middle3_eq_case_2_3_row_0_2_0
  · exact right0Middle3_eq_case_2_3_row_0_3_0
  · exact right0Middle3_eq_case_2_3_row_0_4_0
  · exact right0Middle3_eq_case_2_3_row_0_5_0
  · exact right0Middle3_eq_case_2_3_row_0_6_0
  · exact right0Middle3_eq_case_2_3_row_0_7_0
  · exact right0Middle3_eq_case_2_3_row_1_0_0
  · exact right0Middle3_eq_case_2_3_row_1_1_0
  · exact right0Middle3_eq_case_2_3_row_1_2_0
  · exact right0Middle3_eq_case_2_3_row_1_3_0
  · exact right0Middle3_eq_case_2_3_row_1_4_0
  · exact right0Middle3_eq_case_2_3_row_1_5_0
  · exact right0Middle3_eq_case_2_3_row_1_6_0
  · exact right0Middle3_eq_case_2_3_row_1_7_0

set_option backward.isDefEq.respectTransparency false in
theorem right0Middle3_eq_case_2_3 : right0Middle3 2 3 = innerRightZ 3 2 3 * associatorZ 3 2 3 := by
  simpa only [HexagonAtoms323.assocABC_eq,
    HexagonAtoms323.outerABC_eq,
    HexagonAtoms323.assocBAC_eq,
    HexagonAtoms323.innerABC_eq,
    HexagonAtoms323.innerRightABC_eq,
    HexagonAtoms323.inverseACB_eq,
    HexagonAtoms323.innerACB_eq,
    HexagonAtoms323.assocBCA_eq,
    HexagonAtoms323.innerRightBAC_eq,
    HexagonAtoms323.assocCAB_eq,
    HexagonAtoms323.outerLeftABC_eq,
    HexagonRowColumn323.assocBCA_alias,
    HexagonRowColumn323.product0_eq,
    HexagonRowColumn323.product1_eq,
    HexagonRowColumn323.product2_eq,
    HexagonRowColumn323.product3_eq,
    HexagonRowColumn323.product4_eq,
    HexagonRowColumn323.product5_eq,
    HexagonRowColumn323.product6_eq,
    HexagonRowColumn323.product7_eq] using right0Middle3_eq_case_2_3_checked

private theorem right1Middle3_eq_case_2_3_row_0_0_0 : (right1Middle3 2 3) ((0 : Fin 4), (0 : Fin 4), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn323.rows_inverseACB HexagonRowColumn323.cols_right0) ((0 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right1Middle3_eq_case_2_3_row_0_1_0 : (right1Middle3 2 3) ((0 : Fin 4), (1 : Fin 4), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn323.rows_inverseACB HexagonRowColumn323.cols_right0) ((0 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right1Middle3_eq_case_2_3_row_0_2_0 : (right1Middle3 2 3) ((0 : Fin 4), (2 : Fin 4), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn323.rows_inverseACB HexagonRowColumn323.cols_right0) ((0 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right1Middle3_eq_case_2_3_row_0_3_0 : (right1Middle3 2 3) ((0 : Fin 4), (3 : Fin 4), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn323.rows_inverseACB HexagonRowColumn323.cols_right0) ((0 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right1Middle3_eq_case_2_3_row_1_0_0 : (right1Middle3 2 3) ((1 : Fin 4), (0 : Fin 4), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn323.rows_inverseACB HexagonRowColumn323.cols_right0) ((1 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right1Middle3_eq_case_2_3_row_1_1_0 : (right1Middle3 2 3) ((1 : Fin 4), (1 : Fin 4), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn323.rows_inverseACB HexagonRowColumn323.cols_right0) ((1 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right1Middle3_eq_case_2_3_row_1_2_0 : (right1Middle3 2 3) ((1 : Fin 4), (2 : Fin 4), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn323.rows_inverseACB HexagonRowColumn323.cols_right0) ((1 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right1Middle3_eq_case_2_3_row_1_3_0 : (right1Middle3 2 3) ((1 : Fin 4), (3 : Fin 4), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn323.rows_inverseACB HexagonRowColumn323.cols_right0) ((1 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right1Middle3_eq_case_2_3_row_2_0_0 : (right1Middle3 2 3) ((2 : Fin 4), (0 : Fin 4), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn323.rows_inverseACB HexagonRowColumn323.cols_right0) ((2 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right1Middle3_eq_case_2_3_row_2_1_0 : (right1Middle3 2 3) ((2 : Fin 4), (1 : Fin 4), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn323.rows_inverseACB HexagonRowColumn323.cols_right0) ((2 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right1Middle3_eq_case_2_3_row_2_2_0 : (right1Middle3 2 3) ((2 : Fin 4), (2 : Fin 4), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn323.rows_inverseACB HexagonRowColumn323.cols_right0) ((2 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right1Middle3_eq_case_2_3_row_2_3_0 : (right1Middle3 2 3) ((2 : Fin 4), (3 : Fin 4), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn323.rows_inverseACB HexagonRowColumn323.cols_right0) ((2 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right1Middle3_eq_case_2_3_row_3_0_0 : (right1Middle3 2 3) ((3 : Fin 4), (0 : Fin 4), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn323.rows_inverseACB HexagonRowColumn323.cols_right0) ((3 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right1Middle3_eq_case_2_3_row_3_1_0 : (right1Middle3 2 3) ((3 : Fin 4), (1 : Fin 4), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn323.rows_inverseACB HexagonRowColumn323.cols_right0) ((3 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right1Middle3_eq_case_2_3_row_3_2_0 : (right1Middle3 2 3) ((3 : Fin 4), (2 : Fin 4), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn323.rows_inverseACB HexagonRowColumn323.cols_right0) ((3 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right1Middle3_eq_case_2_3_row_3_3_0 : (right1Middle3 2 3) ((3 : Fin 4), (3 : Fin 4), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn323.rows_inverseACB HexagonRowColumn323.cols_right0) ((3 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right1Middle3_eq_case_2_3_checked : right1Middle3 2 3 = rowColumnMul HexagonRowColumn323.rows_inverseACB HexagonRowColumn323.cols_right0 := by
  funext r
  fin_cases r
  · exact right1Middle3_eq_case_2_3_row_0_0_0
  · exact right1Middle3_eq_case_2_3_row_0_1_0
  · exact right1Middle3_eq_case_2_3_row_0_2_0
  · exact right1Middle3_eq_case_2_3_row_0_3_0
  · exact right1Middle3_eq_case_2_3_row_1_0_0
  · exact right1Middle3_eq_case_2_3_row_1_1_0
  · exact right1Middle3_eq_case_2_3_row_1_2_0
  · exact right1Middle3_eq_case_2_3_row_1_3_0
  · exact right1Middle3_eq_case_2_3_row_2_0_0
  · exact right1Middle3_eq_case_2_3_row_2_1_0
  · exact right1Middle3_eq_case_2_3_row_2_2_0
  · exact right1Middle3_eq_case_2_3_row_2_3_0
  · exact right1Middle3_eq_case_2_3_row_3_0_0
  · exact right1Middle3_eq_case_2_3_row_3_1_0
  · exact right1Middle3_eq_case_2_3_row_3_2_0
  · exact right1Middle3_eq_case_2_3_row_3_3_0

set_option backward.isDefEq.respectTransparency false in
theorem right1Middle3_eq_case_2_3 : right1Middle3 2 3 = associatorInverseZ 3 3 2 * right0Middle3 2 3 := by
  simpa only [HexagonAtoms323.assocABC_eq,
    HexagonAtoms323.outerABC_eq,
    HexagonAtoms323.assocBAC_eq,
    HexagonAtoms323.innerABC_eq,
    HexagonAtoms323.innerRightABC_eq,
    HexagonAtoms323.inverseACB_eq,
    HexagonAtoms323.innerACB_eq,
    HexagonAtoms323.assocBCA_eq,
    HexagonAtoms323.innerRightBAC_eq,
    HexagonAtoms323.assocCAB_eq,
    HexagonAtoms323.outerLeftABC_eq,
    HexagonRowColumn323.assocBCA_alias,
    HexagonRowColumn323.product0_eq,
    HexagonRowColumn323.product1_eq,
    HexagonRowColumn323.product2_eq,
    HexagonRowColumn323.product3_eq,
    HexagonRowColumn323.product4_eq,
    HexagonRowColumn323.product5_eq,
    HexagonRowColumn323.product6_eq,
    HexagonRowColumn323.product7_eq] using right1Middle3_eq_case_2_3_checked

private theorem right2Middle3_eq_case_2_3_row_0_0_0 : (right2Middle3 2 3) ((0 : Fin 4), (0 : Fin 4), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn323.rows_innerACB HexagonRowColumn323.cols_right1) ((0 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right2Middle3_eq_case_2_3_row_0_1_0 : (right2Middle3 2 3) ((0 : Fin 4), (1 : Fin 4), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn323.rows_innerACB HexagonRowColumn323.cols_right1) ((0 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right2Middle3_eq_case_2_3_row_0_2_0 : (right2Middle3 2 3) ((0 : Fin 4), (2 : Fin 4), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn323.rows_innerACB HexagonRowColumn323.cols_right1) ((0 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right2Middle3_eq_case_2_3_row_0_3_0 : (right2Middle3 2 3) ((0 : Fin 4), (3 : Fin 4), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn323.rows_innerACB HexagonRowColumn323.cols_right1) ((0 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right2Middle3_eq_case_2_3_row_1_0_0 : (right2Middle3 2 3) ((1 : Fin 4), (0 : Fin 4), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn323.rows_innerACB HexagonRowColumn323.cols_right1) ((1 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right2Middle3_eq_case_2_3_row_1_1_0 : (right2Middle3 2 3) ((1 : Fin 4), (1 : Fin 4), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn323.rows_innerACB HexagonRowColumn323.cols_right1) ((1 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right2Middle3_eq_case_2_3_row_1_2_0 : (right2Middle3 2 3) ((1 : Fin 4), (2 : Fin 4), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn323.rows_innerACB HexagonRowColumn323.cols_right1) ((1 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right2Middle3_eq_case_2_3_row_1_3_0 : (right2Middle3 2 3) ((1 : Fin 4), (3 : Fin 4), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn323.rows_innerACB HexagonRowColumn323.cols_right1) ((1 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right2Middle3_eq_case_2_3_row_2_0_0 : (right2Middle3 2 3) ((2 : Fin 4), (0 : Fin 4), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn323.rows_innerACB HexagonRowColumn323.cols_right1) ((2 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right2Middle3_eq_case_2_3_row_2_1_0 : (right2Middle3 2 3) ((2 : Fin 4), (1 : Fin 4), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn323.rows_innerACB HexagonRowColumn323.cols_right1) ((2 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right2Middle3_eq_case_2_3_row_2_2_0 : (right2Middle3 2 3) ((2 : Fin 4), (2 : Fin 4), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn323.rows_innerACB HexagonRowColumn323.cols_right1) ((2 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right2Middle3_eq_case_2_3_row_2_3_0 : (right2Middle3 2 3) ((2 : Fin 4), (3 : Fin 4), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn323.rows_innerACB HexagonRowColumn323.cols_right1) ((2 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right2Middle3_eq_case_2_3_row_3_0_0 : (right2Middle3 2 3) ((3 : Fin 4), (0 : Fin 4), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn323.rows_innerACB HexagonRowColumn323.cols_right1) ((3 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right2Middle3_eq_case_2_3_row_3_1_0 : (right2Middle3 2 3) ((3 : Fin 4), (1 : Fin 4), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn323.rows_innerACB HexagonRowColumn323.cols_right1) ((3 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right2Middle3_eq_case_2_3_row_3_2_0 : (right2Middle3 2 3) ((3 : Fin 4), (2 : Fin 4), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn323.rows_innerACB HexagonRowColumn323.cols_right1) ((3 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right2Middle3_eq_case_2_3_row_3_3_0 : (right2Middle3 2 3) ((3 : Fin 4), (3 : Fin 4), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn323.rows_innerACB HexagonRowColumn323.cols_right1) ((3 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right2Middle3_eq_case_2_3_checked : right2Middle3 2 3 = rowColumnMul HexagonRowColumn323.rows_innerACB HexagonRowColumn323.cols_right1 := by
  funext r
  fin_cases r
  · exact right2Middle3_eq_case_2_3_row_0_0_0
  · exact right2Middle3_eq_case_2_3_row_0_1_0
  · exact right2Middle3_eq_case_2_3_row_0_2_0
  · exact right2Middle3_eq_case_2_3_row_0_3_0
  · exact right2Middle3_eq_case_2_3_row_1_0_0
  · exact right2Middle3_eq_case_2_3_row_1_1_0
  · exact right2Middle3_eq_case_2_3_row_1_2_0
  · exact right2Middle3_eq_case_2_3_row_1_3_0
  · exact right2Middle3_eq_case_2_3_row_2_0_0
  · exact right2Middle3_eq_case_2_3_row_2_1_0
  · exact right2Middle3_eq_case_2_3_row_2_2_0
  · exact right2Middle3_eq_case_2_3_row_2_3_0
  · exact right2Middle3_eq_case_2_3_row_3_0_0
  · exact right2Middle3_eq_case_2_3_row_3_1_0
  · exact right2Middle3_eq_case_2_3_row_3_2_0
  · exact right2Middle3_eq_case_2_3_row_3_3_0

set_option backward.isDefEq.respectTransparency false in
theorem right2Middle3_eq_case_2_3 : right2Middle3 2 3 = innerLeftZ 3 3 2 * right1Middle3 2 3 := by
  simpa only [HexagonAtoms323.assocABC_eq,
    HexagonAtoms323.outerABC_eq,
    HexagonAtoms323.assocBAC_eq,
    HexagonAtoms323.innerABC_eq,
    HexagonAtoms323.innerRightABC_eq,
    HexagonAtoms323.inverseACB_eq,
    HexagonAtoms323.innerACB_eq,
    HexagonAtoms323.assocBCA_eq,
    HexagonAtoms323.innerRightBAC_eq,
    HexagonAtoms323.assocCAB_eq,
    HexagonAtoms323.outerLeftABC_eq,
    HexagonRowColumn323.assocBCA_alias,
    HexagonRowColumn323.product0_eq,
    HexagonRowColumn323.product1_eq,
    HexagonRowColumn323.product2_eq,
    HexagonRowColumn323.product3_eq,
    HexagonRowColumn323.product4_eq,
    HexagonRowColumn323.product5_eq,
    HexagonRowColumn323.product6_eq,
    HexagonRowColumn323.product7_eq] using right2Middle3_eq_case_2_3_checked

private theorem leftFinal3_case_2_3_row_0_0_0 : (((-1 : ℤ) ^ (leftScaleBit 3 2 3).val * positiveScale (leftScaleExponent 3 2 3)) •
      (rowColumnMul HexagonRowColumn323.rows_assocBAC HexagonRowColumn323.cols_left0)) ((0 : Fin 4), (0 : Fin 4), (0 : Fin 1)) = (negativeScale (leftScaleExponent 3 2 3) • (rowColumnMul HexagonRowColumn323.rows_innerRightBAC HexagonRowColumn323.cols_left1)) ((0 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem leftFinal3_case_2_3_row_0_1_0 : (((-1 : ℤ) ^ (leftScaleBit 3 2 3).val * positiveScale (leftScaleExponent 3 2 3)) •
      (rowColumnMul HexagonRowColumn323.rows_assocBAC HexagonRowColumn323.cols_left0)) ((0 : Fin 4), (1 : Fin 4), (0 : Fin 1)) = (negativeScale (leftScaleExponent 3 2 3) • (rowColumnMul HexagonRowColumn323.rows_innerRightBAC HexagonRowColumn323.cols_left1)) ((0 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem leftFinal3_case_2_3_row_0_2_0 : (((-1 : ℤ) ^ (leftScaleBit 3 2 3).val * positiveScale (leftScaleExponent 3 2 3)) •
      (rowColumnMul HexagonRowColumn323.rows_assocBAC HexagonRowColumn323.cols_left0)) ((0 : Fin 4), (2 : Fin 4), (0 : Fin 1)) = (negativeScale (leftScaleExponent 3 2 3) • (rowColumnMul HexagonRowColumn323.rows_innerRightBAC HexagonRowColumn323.cols_left1)) ((0 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem leftFinal3_case_2_3_row_0_3_0 : (((-1 : ℤ) ^ (leftScaleBit 3 2 3).val * positiveScale (leftScaleExponent 3 2 3)) •
      (rowColumnMul HexagonRowColumn323.rows_assocBAC HexagonRowColumn323.cols_left0)) ((0 : Fin 4), (3 : Fin 4), (0 : Fin 1)) = (negativeScale (leftScaleExponent 3 2 3) • (rowColumnMul HexagonRowColumn323.rows_innerRightBAC HexagonRowColumn323.cols_left1)) ((0 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem leftFinal3_case_2_3_row_1_0_0 : (((-1 : ℤ) ^ (leftScaleBit 3 2 3).val * positiveScale (leftScaleExponent 3 2 3)) •
      (rowColumnMul HexagonRowColumn323.rows_assocBAC HexagonRowColumn323.cols_left0)) ((1 : Fin 4), (0 : Fin 4), (0 : Fin 1)) = (negativeScale (leftScaleExponent 3 2 3) • (rowColumnMul HexagonRowColumn323.rows_innerRightBAC HexagonRowColumn323.cols_left1)) ((1 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem leftFinal3_case_2_3_row_1_1_0 : (((-1 : ℤ) ^ (leftScaleBit 3 2 3).val * positiveScale (leftScaleExponent 3 2 3)) •
      (rowColumnMul HexagonRowColumn323.rows_assocBAC HexagonRowColumn323.cols_left0)) ((1 : Fin 4), (1 : Fin 4), (0 : Fin 1)) = (negativeScale (leftScaleExponent 3 2 3) • (rowColumnMul HexagonRowColumn323.rows_innerRightBAC HexagonRowColumn323.cols_left1)) ((1 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem leftFinal3_case_2_3_row_1_2_0 : (((-1 : ℤ) ^ (leftScaleBit 3 2 3).val * positiveScale (leftScaleExponent 3 2 3)) •
      (rowColumnMul HexagonRowColumn323.rows_assocBAC HexagonRowColumn323.cols_left0)) ((1 : Fin 4), (2 : Fin 4), (0 : Fin 1)) = (negativeScale (leftScaleExponent 3 2 3) • (rowColumnMul HexagonRowColumn323.rows_innerRightBAC HexagonRowColumn323.cols_left1)) ((1 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem leftFinal3_case_2_3_row_1_3_0 : (((-1 : ℤ) ^ (leftScaleBit 3 2 3).val * positiveScale (leftScaleExponent 3 2 3)) •
      (rowColumnMul HexagonRowColumn323.rows_assocBAC HexagonRowColumn323.cols_left0)) ((1 : Fin 4), (3 : Fin 4), (0 : Fin 1)) = (negativeScale (leftScaleExponent 3 2 3) • (rowColumnMul HexagonRowColumn323.rows_innerRightBAC HexagonRowColumn323.cols_left1)) ((1 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem leftFinal3_case_2_3_row_2_0_0 : (((-1 : ℤ) ^ (leftScaleBit 3 2 3).val * positiveScale (leftScaleExponent 3 2 3)) •
      (rowColumnMul HexagonRowColumn323.rows_assocBAC HexagonRowColumn323.cols_left0)) ((2 : Fin 4), (0 : Fin 4), (0 : Fin 1)) = (negativeScale (leftScaleExponent 3 2 3) • (rowColumnMul HexagonRowColumn323.rows_innerRightBAC HexagonRowColumn323.cols_left1)) ((2 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem leftFinal3_case_2_3_row_2_1_0 : (((-1 : ℤ) ^ (leftScaleBit 3 2 3).val * positiveScale (leftScaleExponent 3 2 3)) •
      (rowColumnMul HexagonRowColumn323.rows_assocBAC HexagonRowColumn323.cols_left0)) ((2 : Fin 4), (1 : Fin 4), (0 : Fin 1)) = (negativeScale (leftScaleExponent 3 2 3) • (rowColumnMul HexagonRowColumn323.rows_innerRightBAC HexagonRowColumn323.cols_left1)) ((2 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem leftFinal3_case_2_3_row_2_2_0 : (((-1 : ℤ) ^ (leftScaleBit 3 2 3).val * positiveScale (leftScaleExponent 3 2 3)) •
      (rowColumnMul HexagonRowColumn323.rows_assocBAC HexagonRowColumn323.cols_left0)) ((2 : Fin 4), (2 : Fin 4), (0 : Fin 1)) = (negativeScale (leftScaleExponent 3 2 3) • (rowColumnMul HexagonRowColumn323.rows_innerRightBAC HexagonRowColumn323.cols_left1)) ((2 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem leftFinal3_case_2_3_row_2_3_0 : (((-1 : ℤ) ^ (leftScaleBit 3 2 3).val * positiveScale (leftScaleExponent 3 2 3)) •
      (rowColumnMul HexagonRowColumn323.rows_assocBAC HexagonRowColumn323.cols_left0)) ((2 : Fin 4), (3 : Fin 4), (0 : Fin 1)) = (negativeScale (leftScaleExponent 3 2 3) • (rowColumnMul HexagonRowColumn323.rows_innerRightBAC HexagonRowColumn323.cols_left1)) ((2 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem leftFinal3_case_2_3_row_3_0_0 : (((-1 : ℤ) ^ (leftScaleBit 3 2 3).val * positiveScale (leftScaleExponent 3 2 3)) •
      (rowColumnMul HexagonRowColumn323.rows_assocBAC HexagonRowColumn323.cols_left0)) ((3 : Fin 4), (0 : Fin 4), (0 : Fin 1)) = (negativeScale (leftScaleExponent 3 2 3) • (rowColumnMul HexagonRowColumn323.rows_innerRightBAC HexagonRowColumn323.cols_left1)) ((3 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem leftFinal3_case_2_3_row_3_1_0 : (((-1 : ℤ) ^ (leftScaleBit 3 2 3).val * positiveScale (leftScaleExponent 3 2 3)) •
      (rowColumnMul HexagonRowColumn323.rows_assocBAC HexagonRowColumn323.cols_left0)) ((3 : Fin 4), (1 : Fin 4), (0 : Fin 1)) = (negativeScale (leftScaleExponent 3 2 3) • (rowColumnMul HexagonRowColumn323.rows_innerRightBAC HexagonRowColumn323.cols_left1)) ((3 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem leftFinal3_case_2_3_row_3_2_0 : (((-1 : ℤ) ^ (leftScaleBit 3 2 3).val * positiveScale (leftScaleExponent 3 2 3)) •
      (rowColumnMul HexagonRowColumn323.rows_assocBAC HexagonRowColumn323.cols_left0)) ((3 : Fin 4), (2 : Fin 4), (0 : Fin 1)) = (negativeScale (leftScaleExponent 3 2 3) • (rowColumnMul HexagonRowColumn323.rows_innerRightBAC HexagonRowColumn323.cols_left1)) ((3 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem leftFinal3_case_2_3_row_3_3_0 : (((-1 : ℤ) ^ (leftScaleBit 3 2 3).val * positiveScale (leftScaleExponent 3 2 3)) •
      (rowColumnMul HexagonRowColumn323.rows_assocBAC HexagonRowColumn323.cols_left0)) ((3 : Fin 4), (3 : Fin 4), (0 : Fin 1)) = (negativeScale (leftScaleExponent 3 2 3) • (rowColumnMul HexagonRowColumn323.rows_innerRightBAC HexagonRowColumn323.cols_left1)) ((3 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem leftFinal3_case_2_3_checked : ((-1 : ℤ) ^ (leftScaleBit 3 2 3).val * positiveScale (leftScaleExponent 3 2 3)) •
      (rowColumnMul HexagonRowColumn323.rows_assocBAC HexagonRowColumn323.cols_left0) = negativeScale (leftScaleExponent 3 2 3) • (rowColumnMul HexagonRowColumn323.rows_innerRightBAC HexagonRowColumn323.cols_left1) := by
  funext r
  fin_cases r
  · exact leftFinal3_case_2_3_row_0_0_0
  · exact leftFinal3_case_2_3_row_0_1_0
  · exact leftFinal3_case_2_3_row_0_2_0
  · exact leftFinal3_case_2_3_row_0_3_0
  · exact leftFinal3_case_2_3_row_1_0_0
  · exact leftFinal3_case_2_3_row_1_1_0
  · exact leftFinal3_case_2_3_row_1_2_0
  · exact leftFinal3_case_2_3_row_1_3_0
  · exact leftFinal3_case_2_3_row_2_0_0
  · exact leftFinal3_case_2_3_row_2_1_0
  · exact leftFinal3_case_2_3_row_2_2_0
  · exact leftFinal3_case_2_3_row_2_3_0
  · exact leftFinal3_case_2_3_row_3_0_0
  · exact leftFinal3_case_2_3_row_3_1_0
  · exact leftFinal3_case_2_3_row_3_2_0
  · exact leftFinal3_case_2_3_row_3_3_0

set_option backward.isDefEq.respectTransparency false in
theorem leftFinal3_case_2_3 : ((-1 : ℤ) ^ (leftScaleBit 3 2 3).val * positiveScale (leftScaleExponent 3 2 3)) •
      (associatorZ 2 3 3 * left0Middle3 2 3) = negativeScale (leftScaleExponent 3 2 3) • (innerRightZ 2 3 3 * left1Middle3 2 3) := by
  simpa only [HexagonAtoms323.assocABC_eq,
    HexagonAtoms323.outerABC_eq,
    HexagonAtoms323.assocBAC_eq,
    HexagonAtoms323.innerABC_eq,
    HexagonAtoms323.innerRightABC_eq,
    HexagonAtoms323.inverseACB_eq,
    HexagonAtoms323.innerACB_eq,
    HexagonAtoms323.assocBCA_eq,
    HexagonAtoms323.innerRightBAC_eq,
    HexagonAtoms323.assocCAB_eq,
    HexagonAtoms323.outerLeftABC_eq,
    HexagonRowColumn323.assocBCA_alias,
    HexagonRowColumn323.product0_eq,
    HexagonRowColumn323.product1_eq,
    HexagonRowColumn323.product2_eq,
    HexagonRowColumn323.product3_eq,
    HexagonRowColumn323.product4_eq,
    HexagonRowColumn323.product5_eq,
    HexagonRowColumn323.product6_eq,
    HexagonRowColumn323.product7_eq] using leftFinal3_case_2_3_checked

private theorem rightFinal3_case_2_3_row_0_0_0 : (((-1 : ℤ) ^ (rightScaleBit 3 2 3).val * positiveScale (rightScaleExponent 3 2 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 3 2 : ℤ)) • HexagonAtoms323.outerLeftABC) ((0 : Fin 2), (0 : Fin 8), (0 : Fin 1)) = (negativeScale (rightScaleExponent 3 2 3) • (rowColumnMul HexagonRowColumn323.rows_assocCAB HexagonRowColumn323.cols_right2)) ((0 : Fin 2), (0 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem rightFinal3_case_2_3_row_0_1_0 : (((-1 : ℤ) ^ (rightScaleBit 3 2 3).val * positiveScale (rightScaleExponent 3 2 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 3 2 : ℤ)) • HexagonAtoms323.outerLeftABC) ((0 : Fin 2), (1 : Fin 8), (0 : Fin 1)) = (negativeScale (rightScaleExponent 3 2 3) • (rowColumnMul HexagonRowColumn323.rows_assocCAB HexagonRowColumn323.cols_right2)) ((0 : Fin 2), (1 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem rightFinal3_case_2_3_row_0_2_0 : (((-1 : ℤ) ^ (rightScaleBit 3 2 3).val * positiveScale (rightScaleExponent 3 2 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 3 2 : ℤ)) • HexagonAtoms323.outerLeftABC) ((0 : Fin 2), (2 : Fin 8), (0 : Fin 1)) = (negativeScale (rightScaleExponent 3 2 3) • (rowColumnMul HexagonRowColumn323.rows_assocCAB HexagonRowColumn323.cols_right2)) ((0 : Fin 2), (2 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem rightFinal3_case_2_3_row_0_3_0 : (((-1 : ℤ) ^ (rightScaleBit 3 2 3).val * positiveScale (rightScaleExponent 3 2 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 3 2 : ℤ)) • HexagonAtoms323.outerLeftABC) ((0 : Fin 2), (3 : Fin 8), (0 : Fin 1)) = (negativeScale (rightScaleExponent 3 2 3) • (rowColumnMul HexagonRowColumn323.rows_assocCAB HexagonRowColumn323.cols_right2)) ((0 : Fin 2), (3 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem rightFinal3_case_2_3_row_0_4_0 : (((-1 : ℤ) ^ (rightScaleBit 3 2 3).val * positiveScale (rightScaleExponent 3 2 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 3 2 : ℤ)) • HexagonAtoms323.outerLeftABC) ((0 : Fin 2), (4 : Fin 8), (0 : Fin 1)) = (negativeScale (rightScaleExponent 3 2 3) • (rowColumnMul HexagonRowColumn323.rows_assocCAB HexagonRowColumn323.cols_right2)) ((0 : Fin 2), (4 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem rightFinal3_case_2_3_row_0_5_0 : (((-1 : ℤ) ^ (rightScaleBit 3 2 3).val * positiveScale (rightScaleExponent 3 2 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 3 2 : ℤ)) • HexagonAtoms323.outerLeftABC) ((0 : Fin 2), (5 : Fin 8), (0 : Fin 1)) = (negativeScale (rightScaleExponent 3 2 3) • (rowColumnMul HexagonRowColumn323.rows_assocCAB HexagonRowColumn323.cols_right2)) ((0 : Fin 2), (5 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem rightFinal3_case_2_3_row_0_6_0 : (((-1 : ℤ) ^ (rightScaleBit 3 2 3).val * positiveScale (rightScaleExponent 3 2 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 3 2 : ℤ)) • HexagonAtoms323.outerLeftABC) ((0 : Fin 2), (6 : Fin 8), (0 : Fin 1)) = (negativeScale (rightScaleExponent 3 2 3) • (rowColumnMul HexagonRowColumn323.rows_assocCAB HexagonRowColumn323.cols_right2)) ((0 : Fin 2), (6 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem rightFinal3_case_2_3_row_0_7_0 : (((-1 : ℤ) ^ (rightScaleBit 3 2 3).val * positiveScale (rightScaleExponent 3 2 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 3 2 : ℤ)) • HexagonAtoms323.outerLeftABC) ((0 : Fin 2), (7 : Fin 8), (0 : Fin 1)) = (negativeScale (rightScaleExponent 3 2 3) • (rowColumnMul HexagonRowColumn323.rows_assocCAB HexagonRowColumn323.cols_right2)) ((0 : Fin 2), (7 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem rightFinal3_case_2_3_row_1_0_0 : (((-1 : ℤ) ^ (rightScaleBit 3 2 3).val * positiveScale (rightScaleExponent 3 2 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 3 2 : ℤ)) • HexagonAtoms323.outerLeftABC) ((1 : Fin 2), (0 : Fin 8), (0 : Fin 1)) = (negativeScale (rightScaleExponent 3 2 3) • (rowColumnMul HexagonRowColumn323.rows_assocCAB HexagonRowColumn323.cols_right2)) ((1 : Fin 2), (0 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem rightFinal3_case_2_3_row_1_1_0 : (((-1 : ℤ) ^ (rightScaleBit 3 2 3).val * positiveScale (rightScaleExponent 3 2 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 3 2 : ℤ)) • HexagonAtoms323.outerLeftABC) ((1 : Fin 2), (1 : Fin 8), (0 : Fin 1)) = (negativeScale (rightScaleExponent 3 2 3) • (rowColumnMul HexagonRowColumn323.rows_assocCAB HexagonRowColumn323.cols_right2)) ((1 : Fin 2), (1 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem rightFinal3_case_2_3_row_1_2_0 : (((-1 : ℤ) ^ (rightScaleBit 3 2 3).val * positiveScale (rightScaleExponent 3 2 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 3 2 : ℤ)) • HexagonAtoms323.outerLeftABC) ((1 : Fin 2), (2 : Fin 8), (0 : Fin 1)) = (negativeScale (rightScaleExponent 3 2 3) • (rowColumnMul HexagonRowColumn323.rows_assocCAB HexagonRowColumn323.cols_right2)) ((1 : Fin 2), (2 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem rightFinal3_case_2_3_row_1_3_0 : (((-1 : ℤ) ^ (rightScaleBit 3 2 3).val * positiveScale (rightScaleExponent 3 2 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 3 2 : ℤ)) • HexagonAtoms323.outerLeftABC) ((1 : Fin 2), (3 : Fin 8), (0 : Fin 1)) = (negativeScale (rightScaleExponent 3 2 3) • (rowColumnMul HexagonRowColumn323.rows_assocCAB HexagonRowColumn323.cols_right2)) ((1 : Fin 2), (3 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem rightFinal3_case_2_3_row_1_4_0 : (((-1 : ℤ) ^ (rightScaleBit 3 2 3).val * positiveScale (rightScaleExponent 3 2 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 3 2 : ℤ)) • HexagonAtoms323.outerLeftABC) ((1 : Fin 2), (4 : Fin 8), (0 : Fin 1)) = (negativeScale (rightScaleExponent 3 2 3) • (rowColumnMul HexagonRowColumn323.rows_assocCAB HexagonRowColumn323.cols_right2)) ((1 : Fin 2), (4 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem rightFinal3_case_2_3_row_1_5_0 : (((-1 : ℤ) ^ (rightScaleBit 3 2 3).val * positiveScale (rightScaleExponent 3 2 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 3 2 : ℤ)) • HexagonAtoms323.outerLeftABC) ((1 : Fin 2), (5 : Fin 8), (0 : Fin 1)) = (negativeScale (rightScaleExponent 3 2 3) • (rowColumnMul HexagonRowColumn323.rows_assocCAB HexagonRowColumn323.cols_right2)) ((1 : Fin 2), (5 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem rightFinal3_case_2_3_row_1_6_0 : (((-1 : ℤ) ^ (rightScaleBit 3 2 3).val * positiveScale (rightScaleExponent 3 2 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 3 2 : ℤ)) • HexagonAtoms323.outerLeftABC) ((1 : Fin 2), (6 : Fin 8), (0 : Fin 1)) = (negativeScale (rightScaleExponent 3 2 3) • (rowColumnMul HexagonRowColumn323.rows_assocCAB HexagonRowColumn323.cols_right2)) ((1 : Fin 2), (6 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem rightFinal3_case_2_3_row_1_7_0 : (((-1 : ℤ) ^ (rightScaleBit 3 2 3).val * positiveScale (rightScaleExponent 3 2 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 3 2 : ℤ)) • HexagonAtoms323.outerLeftABC) ((1 : Fin 2), (7 : Fin 8), (0 : Fin 1)) = (negativeScale (rightScaleExponent 3 2 3) • (rowColumnMul HexagonRowColumn323.rows_assocCAB HexagonRowColumn323.cols_right2)) ((1 : Fin 2), (7 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem rightFinal3_case_2_3_checked : ((-1 : ℤ) ^ (rightScaleBit 3 2 3).val * positiveScale (rightScaleExponent 3 2 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 3 2 : ℤ)) • HexagonAtoms323.outerLeftABC = negativeScale (rightScaleExponent 3 2 3) • (rowColumnMul HexagonRowColumn323.rows_assocCAB HexagonRowColumn323.cols_right2) := by
  funext r
  fin_cases r
  · exact rightFinal3_case_2_3_row_0_0_0
  · exact rightFinal3_case_2_3_row_0_1_0
  · exact rightFinal3_case_2_3_row_0_2_0
  · exact rightFinal3_case_2_3_row_0_3_0
  · exact rightFinal3_case_2_3_row_0_4_0
  · exact rightFinal3_case_2_3_row_0_5_0
  · exact rightFinal3_case_2_3_row_0_6_0
  · exact rightFinal3_case_2_3_row_0_7_0
  · exact rightFinal3_case_2_3_row_1_0_0
  · exact rightFinal3_case_2_3_row_1_1_0
  · exact rightFinal3_case_2_3_row_1_2_0
  · exact rightFinal3_case_2_3_row_1_3_0
  · exact rightFinal3_case_2_3_row_1_4_0
  · exact rightFinal3_case_2_3_row_1_5_0
  · exact rightFinal3_case_2_3_row_1_6_0
  · exact rightFinal3_case_2_3_row_1_7_0

set_option backward.isDefEq.respectTransparency false in
theorem rightFinal3_case_2_3 : ((-1 : ℤ) ^ (rightScaleBit 3 2 3).val * positiveScale (rightScaleExponent 3 2 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 3 2 : ℤ)) • outerLeftZ 3 2 3 = negativeScale (rightScaleExponent 3 2 3) • (associatorZ 3 3 2 * right2Middle3 2 3) := by
  simpa only [HexagonAtoms323.assocABC_eq,
    HexagonAtoms323.outerABC_eq,
    HexagonAtoms323.assocBAC_eq,
    HexagonAtoms323.innerABC_eq,
    HexagonAtoms323.innerRightABC_eq,
    HexagonAtoms323.inverseACB_eq,
    HexagonAtoms323.innerACB_eq,
    HexagonAtoms323.assocBCA_eq,
    HexagonAtoms323.innerRightBAC_eq,
    HexagonAtoms323.assocCAB_eq,
    HexagonAtoms323.outerLeftABC_eq,
    HexagonRowColumn323.assocBCA_alias,
    HexagonRowColumn323.product0_eq,
    HexagonRowColumn323.product1_eq,
    HexagonRowColumn323.product2_eq,
    HexagonRowColumn323.product3_eq,
    HexagonRowColumn323.product4_eq,
    HexagonRowColumn323.product5_eq,
    HexagonRowColumn323.product6_eq,
    HexagonRowColumn323.product7_eq] using rightFinal3_case_2_3_checked

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonCases3
