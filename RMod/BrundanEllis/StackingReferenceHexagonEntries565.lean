import RMod.BrundanEllis.StackingReferenceHexagonMiddle5
import RMod.BrundanEllis.StackingReferenceSparseMatrixCheck
import RMod.BrundanEllis.StackingReferenceHexagonAtoms565
import RMod.BrundanEllis.StackingReferenceHexagonRowColumn565

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

private theorem left0Middle5_eq_case_6_5_row_0_0_0 : (left0Middle5 6 5) ((0 : Fin 2), (0 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn565.rows_outerABC HexagonRowColumn565.cols_assocABC) ((0 : Fin 2), (0 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem left0Middle5_eq_case_6_5_row_0_1_0 : (left0Middle5 6 5) ((0 : Fin 2), (1 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn565.rows_outerABC HexagonRowColumn565.cols_assocABC) ((0 : Fin 2), (1 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem left0Middle5_eq_case_6_5_row_0_2_0 : (left0Middle5 6 5) ((0 : Fin 2), (2 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn565.rows_outerABC HexagonRowColumn565.cols_assocABC) ((0 : Fin 2), (2 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem left0Middle5_eq_case_6_5_row_0_3_0 : (left0Middle5 6 5) ((0 : Fin 2), (3 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn565.rows_outerABC HexagonRowColumn565.cols_assocABC) ((0 : Fin 2), (3 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem left0Middle5_eq_case_6_5_row_0_4_0 : (left0Middle5 6 5) ((0 : Fin 2), (4 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn565.rows_outerABC HexagonRowColumn565.cols_assocABC) ((0 : Fin 2), (4 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem left0Middle5_eq_case_6_5_row_0_5_0 : (left0Middle5 6 5) ((0 : Fin 2), (5 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn565.rows_outerABC HexagonRowColumn565.cols_assocABC) ((0 : Fin 2), (5 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem left0Middle5_eq_case_6_5_row_0_6_0 : (left0Middle5 6 5) ((0 : Fin 2), (6 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn565.rows_outerABC HexagonRowColumn565.cols_assocABC) ((0 : Fin 2), (6 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem left0Middle5_eq_case_6_5_row_0_7_0 : (left0Middle5 6 5) ((0 : Fin 2), (7 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn565.rows_outerABC HexagonRowColumn565.cols_assocABC) ((0 : Fin 2), (7 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem left0Middle5_eq_case_6_5_row_1_0_0 : (left0Middle5 6 5) ((1 : Fin 2), (0 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn565.rows_outerABC HexagonRowColumn565.cols_assocABC) ((1 : Fin 2), (0 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem left0Middle5_eq_case_6_5_row_1_1_0 : (left0Middle5 6 5) ((1 : Fin 2), (1 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn565.rows_outerABC HexagonRowColumn565.cols_assocABC) ((1 : Fin 2), (1 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem left0Middle5_eq_case_6_5_row_1_2_0 : (left0Middle5 6 5) ((1 : Fin 2), (2 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn565.rows_outerABC HexagonRowColumn565.cols_assocABC) ((1 : Fin 2), (2 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem left0Middle5_eq_case_6_5_row_1_3_0 : (left0Middle5 6 5) ((1 : Fin 2), (3 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn565.rows_outerABC HexagonRowColumn565.cols_assocABC) ((1 : Fin 2), (3 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem left0Middle5_eq_case_6_5_row_1_4_0 : (left0Middle5 6 5) ((1 : Fin 2), (4 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn565.rows_outerABC HexagonRowColumn565.cols_assocABC) ((1 : Fin 2), (4 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem left0Middle5_eq_case_6_5_row_1_5_0 : (left0Middle5 6 5) ((1 : Fin 2), (5 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn565.rows_outerABC HexagonRowColumn565.cols_assocABC) ((1 : Fin 2), (5 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem left0Middle5_eq_case_6_5_row_1_6_0 : (left0Middle5 6 5) ((1 : Fin 2), (6 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn565.rows_outerABC HexagonRowColumn565.cols_assocABC) ((1 : Fin 2), (6 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem left0Middle5_eq_case_6_5_row_1_7_0 : (left0Middle5 6 5) ((1 : Fin 2), (7 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn565.rows_outerABC HexagonRowColumn565.cols_assocABC) ((1 : Fin 2), (7 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem left0Middle5_eq_case_6_5_checked : left0Middle5 6 5 = rowColumnMul HexagonRowColumn565.rows_outerABC HexagonRowColumn565.cols_assocABC := by
  funext r
  fin_cases r
  · exact left0Middle5_eq_case_6_5_row_0_0_0
  · exact left0Middle5_eq_case_6_5_row_0_1_0
  · exact left0Middle5_eq_case_6_5_row_0_2_0
  · exact left0Middle5_eq_case_6_5_row_0_3_0
  · exact left0Middle5_eq_case_6_5_row_0_4_0
  · exact left0Middle5_eq_case_6_5_row_0_5_0
  · exact left0Middle5_eq_case_6_5_row_0_6_0
  · exact left0Middle5_eq_case_6_5_row_0_7_0
  · exact left0Middle5_eq_case_6_5_row_1_0_0
  · exact left0Middle5_eq_case_6_5_row_1_1_0
  · exact left0Middle5_eq_case_6_5_row_1_2_0
  · exact left0Middle5_eq_case_6_5_row_1_3_0
  · exact left0Middle5_eq_case_6_5_row_1_4_0
  · exact left0Middle5_eq_case_6_5_row_1_5_0
  · exact left0Middle5_eq_case_6_5_row_1_6_0
  · exact left0Middle5_eq_case_6_5_row_1_7_0

set_option backward.isDefEq.respectTransparency false in
theorem left0Middle5_eq_case_6_5 : left0Middle5 6 5 = outerRightZ 5 6 5 * associatorZ 5 6 5 := by
  simpa only [HexagonAtoms565.assocABC_eq,
    HexagonAtoms565.outerABC_eq,
    HexagonAtoms565.assocBAC_eq,
    HexagonAtoms565.innerABC_eq,
    HexagonAtoms565.innerRightABC_eq,
    HexagonAtoms565.inverseACB_eq,
    HexagonAtoms565.innerACB_eq,
    HexagonAtoms565.assocBCA_eq,
    HexagonAtoms565.innerRightBAC_eq,
    HexagonAtoms565.assocCAB_eq,
    HexagonAtoms565.outerLeftABC_eq,
    HexagonRowColumn565.assocBCA_alias,
    HexagonRowColumn565.product0_eq,
    HexagonRowColumn565.product1_eq,
    HexagonRowColumn565.product2_eq,
    HexagonRowColumn565.product3_eq,
    HexagonRowColumn565.product4_eq,
    HexagonRowColumn565.product5_eq,
    HexagonRowColumn565.product6_eq,
    HexagonRowColumn565.product7_eq] using left0Middle5_eq_case_6_5_checked

private theorem left1Middle5_eq_case_6_5_row_0_0_0 : (left1Middle5 6 5) ((0 : Fin 4), (0 : Fin 4), (0 : Fin 1)) = (HexagonAtoms565.assocBAC) ((0 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem left1Middle5_eq_case_6_5_row_0_1_0 : (left1Middle5 6 5) ((0 : Fin 4), (1 : Fin 4), (0 : Fin 1)) = (HexagonAtoms565.assocBAC) ((0 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem left1Middle5_eq_case_6_5_row_0_2_0 : (left1Middle5 6 5) ((0 : Fin 4), (2 : Fin 4), (0 : Fin 1)) = (HexagonAtoms565.assocBAC) ((0 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem left1Middle5_eq_case_6_5_row_0_3_0 : (left1Middle5 6 5) ((0 : Fin 4), (3 : Fin 4), (0 : Fin 1)) = (HexagonAtoms565.assocBAC) ((0 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem left1Middle5_eq_case_6_5_row_1_0_0 : (left1Middle5 6 5) ((1 : Fin 4), (0 : Fin 4), (0 : Fin 1)) = (HexagonAtoms565.assocBAC) ((1 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem left1Middle5_eq_case_6_5_row_1_1_0 : (left1Middle5 6 5) ((1 : Fin 4), (1 : Fin 4), (0 : Fin 1)) = (HexagonAtoms565.assocBAC) ((1 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem left1Middle5_eq_case_6_5_row_1_2_0 : (left1Middle5 6 5) ((1 : Fin 4), (2 : Fin 4), (0 : Fin 1)) = (HexagonAtoms565.assocBAC) ((1 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem left1Middle5_eq_case_6_5_row_1_3_0 : (left1Middle5 6 5) ((1 : Fin 4), (3 : Fin 4), (0 : Fin 1)) = (HexagonAtoms565.assocBAC) ((1 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem left1Middle5_eq_case_6_5_row_2_0_0 : (left1Middle5 6 5) ((2 : Fin 4), (0 : Fin 4), (0 : Fin 1)) = (HexagonAtoms565.assocBAC) ((2 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem left1Middle5_eq_case_6_5_row_2_1_0 : (left1Middle5 6 5) ((2 : Fin 4), (1 : Fin 4), (0 : Fin 1)) = (HexagonAtoms565.assocBAC) ((2 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem left1Middle5_eq_case_6_5_row_2_2_0 : (left1Middle5 6 5) ((2 : Fin 4), (2 : Fin 4), (0 : Fin 1)) = (HexagonAtoms565.assocBAC) ((2 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem left1Middle5_eq_case_6_5_row_2_3_0 : (left1Middle5 6 5) ((2 : Fin 4), (3 : Fin 4), (0 : Fin 1)) = (HexagonAtoms565.assocBAC) ((2 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem left1Middle5_eq_case_6_5_row_3_0_0 : (left1Middle5 6 5) ((3 : Fin 4), (0 : Fin 4), (0 : Fin 1)) = (HexagonAtoms565.assocBAC) ((3 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem left1Middle5_eq_case_6_5_row_3_1_0 : (left1Middle5 6 5) ((3 : Fin 4), (1 : Fin 4), (0 : Fin 1)) = (HexagonAtoms565.assocBAC) ((3 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem left1Middle5_eq_case_6_5_row_3_2_0 : (left1Middle5 6 5) ((3 : Fin 4), (2 : Fin 4), (0 : Fin 1)) = (HexagonAtoms565.assocBAC) ((3 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem left1Middle5_eq_case_6_5_row_3_3_0 : (left1Middle5 6 5) ((3 : Fin 4), (3 : Fin 4), (0 : Fin 1)) = (HexagonAtoms565.assocBAC) ((3 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem left1Middle5_eq_case_6_5_checked : left1Middle5 6 5 = HexagonAtoms565.assocBAC := by
  funext r
  fin_cases r
  · exact left1Middle5_eq_case_6_5_row_0_0_0
  · exact left1Middle5_eq_case_6_5_row_0_1_0
  · exact left1Middle5_eq_case_6_5_row_0_2_0
  · exact left1Middle5_eq_case_6_5_row_0_3_0
  · exact left1Middle5_eq_case_6_5_row_1_0_0
  · exact left1Middle5_eq_case_6_5_row_1_1_0
  · exact left1Middle5_eq_case_6_5_row_1_2_0
  · exact left1Middle5_eq_case_6_5_row_1_3_0
  · exact left1Middle5_eq_case_6_5_row_2_0_0
  · exact left1Middle5_eq_case_6_5_row_2_1_0
  · exact left1Middle5_eq_case_6_5_row_2_2_0
  · exact left1Middle5_eq_case_6_5_row_2_3_0
  · exact left1Middle5_eq_case_6_5_row_3_0_0
  · exact left1Middle5_eq_case_6_5_row_3_1_0
  · exact left1Middle5_eq_case_6_5_row_3_2_0
  · exact left1Middle5_eq_case_6_5_row_3_3_0

set_option backward.isDefEq.respectTransparency false in
theorem left1Middle5_eq_case_6_5 : left1Middle5 6 5 = associatorZ 6 5 5 * innerLeftZ 5 6 5 := by
  simpa only [HexagonAtoms565.assocABC_eq,
    HexagonAtoms565.outerABC_eq,
    HexagonAtoms565.assocBAC_eq,
    HexagonAtoms565.innerABC_eq,
    HexagonAtoms565.innerRightABC_eq,
    HexagonAtoms565.inverseACB_eq,
    HexagonAtoms565.innerACB_eq,
    HexagonAtoms565.assocBCA_eq,
    HexagonAtoms565.innerRightBAC_eq,
    HexagonAtoms565.assocCAB_eq,
    HexagonAtoms565.outerLeftABC_eq,
    HexagonRowColumn565.assocBCA_alias,
    HexagonRowColumn565.product0_eq,
    HexagonRowColumn565.product1_eq,
    HexagonRowColumn565.product2_eq,
    HexagonRowColumn565.product3_eq,
    HexagonRowColumn565.product4_eq,
    HexagonRowColumn565.product5_eq,
    HexagonRowColumn565.product6_eq,
    HexagonRowColumn565.product7_eq] using left1Middle5_eq_case_6_5_checked

private theorem right0Middle5_eq_case_6_5_row_0_0_0 : (right0Middle5 6 5) ((0 : Fin 2), (0 : Fin 8), (0 : Fin 1)) = (HexagonAtoms565.assocABC) ((0 : Fin 2), (0 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right0Middle5_eq_case_6_5_row_0_1_0 : (right0Middle5 6 5) ((0 : Fin 2), (1 : Fin 8), (0 : Fin 1)) = (HexagonAtoms565.assocABC) ((0 : Fin 2), (1 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right0Middle5_eq_case_6_5_row_0_2_0 : (right0Middle5 6 5) ((0 : Fin 2), (2 : Fin 8), (0 : Fin 1)) = (HexagonAtoms565.assocABC) ((0 : Fin 2), (2 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right0Middle5_eq_case_6_5_row_0_3_0 : (right0Middle5 6 5) ((0 : Fin 2), (3 : Fin 8), (0 : Fin 1)) = (HexagonAtoms565.assocABC) ((0 : Fin 2), (3 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right0Middle5_eq_case_6_5_row_0_4_0 : (right0Middle5 6 5) ((0 : Fin 2), (4 : Fin 8), (0 : Fin 1)) = (HexagonAtoms565.assocABC) ((0 : Fin 2), (4 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right0Middle5_eq_case_6_5_row_0_5_0 : (right0Middle5 6 5) ((0 : Fin 2), (5 : Fin 8), (0 : Fin 1)) = (HexagonAtoms565.assocABC) ((0 : Fin 2), (5 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right0Middle5_eq_case_6_5_row_0_6_0 : (right0Middle5 6 5) ((0 : Fin 2), (6 : Fin 8), (0 : Fin 1)) = (HexagonAtoms565.assocABC) ((0 : Fin 2), (6 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right0Middle5_eq_case_6_5_row_0_7_0 : (right0Middle5 6 5) ((0 : Fin 2), (7 : Fin 8), (0 : Fin 1)) = (HexagonAtoms565.assocABC) ((0 : Fin 2), (7 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right0Middle5_eq_case_6_5_row_1_0_0 : (right0Middle5 6 5) ((1 : Fin 2), (0 : Fin 8), (0 : Fin 1)) = (HexagonAtoms565.assocABC) ((1 : Fin 2), (0 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right0Middle5_eq_case_6_5_row_1_1_0 : (right0Middle5 6 5) ((1 : Fin 2), (1 : Fin 8), (0 : Fin 1)) = (HexagonAtoms565.assocABC) ((1 : Fin 2), (1 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right0Middle5_eq_case_6_5_row_1_2_0 : (right0Middle5 6 5) ((1 : Fin 2), (2 : Fin 8), (0 : Fin 1)) = (HexagonAtoms565.assocABC) ((1 : Fin 2), (2 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right0Middle5_eq_case_6_5_row_1_3_0 : (right0Middle5 6 5) ((1 : Fin 2), (3 : Fin 8), (0 : Fin 1)) = (HexagonAtoms565.assocABC) ((1 : Fin 2), (3 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right0Middle5_eq_case_6_5_row_1_4_0 : (right0Middle5 6 5) ((1 : Fin 2), (4 : Fin 8), (0 : Fin 1)) = (HexagonAtoms565.assocABC) ((1 : Fin 2), (4 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right0Middle5_eq_case_6_5_row_1_5_0 : (right0Middle5 6 5) ((1 : Fin 2), (5 : Fin 8), (0 : Fin 1)) = (HexagonAtoms565.assocABC) ((1 : Fin 2), (5 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right0Middle5_eq_case_6_5_row_1_6_0 : (right0Middle5 6 5) ((1 : Fin 2), (6 : Fin 8), (0 : Fin 1)) = (HexagonAtoms565.assocABC) ((1 : Fin 2), (6 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right0Middle5_eq_case_6_5_row_1_7_0 : (right0Middle5 6 5) ((1 : Fin 2), (7 : Fin 8), (0 : Fin 1)) = (HexagonAtoms565.assocABC) ((1 : Fin 2), (7 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right0Middle5_eq_case_6_5_checked : right0Middle5 6 5 = HexagonAtoms565.assocABC := by
  funext r
  fin_cases r
  · exact right0Middle5_eq_case_6_5_row_0_0_0
  · exact right0Middle5_eq_case_6_5_row_0_1_0
  · exact right0Middle5_eq_case_6_5_row_0_2_0
  · exact right0Middle5_eq_case_6_5_row_0_3_0
  · exact right0Middle5_eq_case_6_5_row_0_4_0
  · exact right0Middle5_eq_case_6_5_row_0_5_0
  · exact right0Middle5_eq_case_6_5_row_0_6_0
  · exact right0Middle5_eq_case_6_5_row_0_7_0
  · exact right0Middle5_eq_case_6_5_row_1_0_0
  · exact right0Middle5_eq_case_6_5_row_1_1_0
  · exact right0Middle5_eq_case_6_5_row_1_2_0
  · exact right0Middle5_eq_case_6_5_row_1_3_0
  · exact right0Middle5_eq_case_6_5_row_1_4_0
  · exact right0Middle5_eq_case_6_5_row_1_5_0
  · exact right0Middle5_eq_case_6_5_row_1_6_0
  · exact right0Middle5_eq_case_6_5_row_1_7_0

set_option backward.isDefEq.respectTransparency false in
theorem right0Middle5_eq_case_6_5 : right0Middle5 6 5 = innerRightZ 5 6 5 * associatorZ 5 6 5 := by
  simpa only [HexagonAtoms565.assocABC_eq,
    HexagonAtoms565.outerABC_eq,
    HexagonAtoms565.assocBAC_eq,
    HexagonAtoms565.innerABC_eq,
    HexagonAtoms565.innerRightABC_eq,
    HexagonAtoms565.inverseACB_eq,
    HexagonAtoms565.innerACB_eq,
    HexagonAtoms565.assocBCA_eq,
    HexagonAtoms565.innerRightBAC_eq,
    HexagonAtoms565.assocCAB_eq,
    HexagonAtoms565.outerLeftABC_eq,
    HexagonRowColumn565.assocBCA_alias,
    HexagonRowColumn565.product0_eq,
    HexagonRowColumn565.product1_eq,
    HexagonRowColumn565.product2_eq,
    HexagonRowColumn565.product3_eq,
    HexagonRowColumn565.product4_eq,
    HexagonRowColumn565.product5_eq,
    HexagonRowColumn565.product6_eq,
    HexagonRowColumn565.product7_eq] using right0Middle5_eq_case_6_5_checked

private theorem right1Middle5_eq_case_6_5_row_0_0_0 : (right1Middle5 6 5) ((0 : Fin 4), (0 : Fin 4), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn565.rows_inverseACB HexagonRowColumn565.cols_right0) ((0 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right1Middle5_eq_case_6_5_row_0_1_0 : (right1Middle5 6 5) ((0 : Fin 4), (1 : Fin 4), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn565.rows_inverseACB HexagonRowColumn565.cols_right0) ((0 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right1Middle5_eq_case_6_5_row_0_2_0 : (right1Middle5 6 5) ((0 : Fin 4), (2 : Fin 4), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn565.rows_inverseACB HexagonRowColumn565.cols_right0) ((0 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right1Middle5_eq_case_6_5_row_0_3_0 : (right1Middle5 6 5) ((0 : Fin 4), (3 : Fin 4), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn565.rows_inverseACB HexagonRowColumn565.cols_right0) ((0 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right1Middle5_eq_case_6_5_row_1_0_0 : (right1Middle5 6 5) ((1 : Fin 4), (0 : Fin 4), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn565.rows_inverseACB HexagonRowColumn565.cols_right0) ((1 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right1Middle5_eq_case_6_5_row_1_1_0 : (right1Middle5 6 5) ((1 : Fin 4), (1 : Fin 4), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn565.rows_inverseACB HexagonRowColumn565.cols_right0) ((1 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right1Middle5_eq_case_6_5_row_1_2_0 : (right1Middle5 6 5) ((1 : Fin 4), (2 : Fin 4), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn565.rows_inverseACB HexagonRowColumn565.cols_right0) ((1 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right1Middle5_eq_case_6_5_row_1_3_0 : (right1Middle5 6 5) ((1 : Fin 4), (3 : Fin 4), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn565.rows_inverseACB HexagonRowColumn565.cols_right0) ((1 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right1Middle5_eq_case_6_5_row_2_0_0 : (right1Middle5 6 5) ((2 : Fin 4), (0 : Fin 4), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn565.rows_inverseACB HexagonRowColumn565.cols_right0) ((2 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right1Middle5_eq_case_6_5_row_2_1_0 : (right1Middle5 6 5) ((2 : Fin 4), (1 : Fin 4), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn565.rows_inverseACB HexagonRowColumn565.cols_right0) ((2 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right1Middle5_eq_case_6_5_row_2_2_0 : (right1Middle5 6 5) ((2 : Fin 4), (2 : Fin 4), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn565.rows_inverseACB HexagonRowColumn565.cols_right0) ((2 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right1Middle5_eq_case_6_5_row_2_3_0 : (right1Middle5 6 5) ((2 : Fin 4), (3 : Fin 4), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn565.rows_inverseACB HexagonRowColumn565.cols_right0) ((2 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right1Middle5_eq_case_6_5_row_3_0_0 : (right1Middle5 6 5) ((3 : Fin 4), (0 : Fin 4), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn565.rows_inverseACB HexagonRowColumn565.cols_right0) ((3 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right1Middle5_eq_case_6_5_row_3_1_0 : (right1Middle5 6 5) ((3 : Fin 4), (1 : Fin 4), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn565.rows_inverseACB HexagonRowColumn565.cols_right0) ((3 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right1Middle5_eq_case_6_5_row_3_2_0 : (right1Middle5 6 5) ((3 : Fin 4), (2 : Fin 4), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn565.rows_inverseACB HexagonRowColumn565.cols_right0) ((3 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right1Middle5_eq_case_6_5_row_3_3_0 : (right1Middle5 6 5) ((3 : Fin 4), (3 : Fin 4), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn565.rows_inverseACB HexagonRowColumn565.cols_right0) ((3 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right1Middle5_eq_case_6_5_checked : right1Middle5 6 5 = rowColumnMul HexagonRowColumn565.rows_inverseACB HexagonRowColumn565.cols_right0 := by
  funext r
  fin_cases r
  · exact right1Middle5_eq_case_6_5_row_0_0_0
  · exact right1Middle5_eq_case_6_5_row_0_1_0
  · exact right1Middle5_eq_case_6_5_row_0_2_0
  · exact right1Middle5_eq_case_6_5_row_0_3_0
  · exact right1Middle5_eq_case_6_5_row_1_0_0
  · exact right1Middle5_eq_case_6_5_row_1_1_0
  · exact right1Middle5_eq_case_6_5_row_1_2_0
  · exact right1Middle5_eq_case_6_5_row_1_3_0
  · exact right1Middle5_eq_case_6_5_row_2_0_0
  · exact right1Middle5_eq_case_6_5_row_2_1_0
  · exact right1Middle5_eq_case_6_5_row_2_2_0
  · exact right1Middle5_eq_case_6_5_row_2_3_0
  · exact right1Middle5_eq_case_6_5_row_3_0_0
  · exact right1Middle5_eq_case_6_5_row_3_1_0
  · exact right1Middle5_eq_case_6_5_row_3_2_0
  · exact right1Middle5_eq_case_6_5_row_3_3_0

set_option backward.isDefEq.respectTransparency false in
theorem right1Middle5_eq_case_6_5 : right1Middle5 6 5 = associatorInverseZ 5 5 6 * right0Middle5 6 5 := by
  simpa only [HexagonAtoms565.assocABC_eq,
    HexagonAtoms565.outerABC_eq,
    HexagonAtoms565.assocBAC_eq,
    HexagonAtoms565.innerABC_eq,
    HexagonAtoms565.innerRightABC_eq,
    HexagonAtoms565.inverseACB_eq,
    HexagonAtoms565.innerACB_eq,
    HexagonAtoms565.assocBCA_eq,
    HexagonAtoms565.innerRightBAC_eq,
    HexagonAtoms565.assocCAB_eq,
    HexagonAtoms565.outerLeftABC_eq,
    HexagonRowColumn565.assocBCA_alias,
    HexagonRowColumn565.product0_eq,
    HexagonRowColumn565.product1_eq,
    HexagonRowColumn565.product2_eq,
    HexagonRowColumn565.product3_eq,
    HexagonRowColumn565.product4_eq,
    HexagonRowColumn565.product5_eq,
    HexagonRowColumn565.product6_eq,
    HexagonRowColumn565.product7_eq] using right1Middle5_eq_case_6_5_checked

private theorem right2Middle5_eq_case_6_5_row_0_0_0 : (right2Middle5 6 5) ((0 : Fin 4), (0 : Fin 4), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn565.rows_innerACB HexagonRowColumn565.cols_right1) ((0 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right2Middle5_eq_case_6_5_row_0_1_0 : (right2Middle5 6 5) ((0 : Fin 4), (1 : Fin 4), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn565.rows_innerACB HexagonRowColumn565.cols_right1) ((0 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right2Middle5_eq_case_6_5_row_0_2_0 : (right2Middle5 6 5) ((0 : Fin 4), (2 : Fin 4), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn565.rows_innerACB HexagonRowColumn565.cols_right1) ((0 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right2Middle5_eq_case_6_5_row_0_3_0 : (right2Middle5 6 5) ((0 : Fin 4), (3 : Fin 4), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn565.rows_innerACB HexagonRowColumn565.cols_right1) ((0 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right2Middle5_eq_case_6_5_row_1_0_0 : (right2Middle5 6 5) ((1 : Fin 4), (0 : Fin 4), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn565.rows_innerACB HexagonRowColumn565.cols_right1) ((1 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right2Middle5_eq_case_6_5_row_1_1_0 : (right2Middle5 6 5) ((1 : Fin 4), (1 : Fin 4), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn565.rows_innerACB HexagonRowColumn565.cols_right1) ((1 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right2Middle5_eq_case_6_5_row_1_2_0 : (right2Middle5 6 5) ((1 : Fin 4), (2 : Fin 4), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn565.rows_innerACB HexagonRowColumn565.cols_right1) ((1 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right2Middle5_eq_case_6_5_row_1_3_0 : (right2Middle5 6 5) ((1 : Fin 4), (3 : Fin 4), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn565.rows_innerACB HexagonRowColumn565.cols_right1) ((1 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right2Middle5_eq_case_6_5_row_2_0_0 : (right2Middle5 6 5) ((2 : Fin 4), (0 : Fin 4), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn565.rows_innerACB HexagonRowColumn565.cols_right1) ((2 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right2Middle5_eq_case_6_5_row_2_1_0 : (right2Middle5 6 5) ((2 : Fin 4), (1 : Fin 4), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn565.rows_innerACB HexagonRowColumn565.cols_right1) ((2 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right2Middle5_eq_case_6_5_row_2_2_0 : (right2Middle5 6 5) ((2 : Fin 4), (2 : Fin 4), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn565.rows_innerACB HexagonRowColumn565.cols_right1) ((2 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right2Middle5_eq_case_6_5_row_2_3_0 : (right2Middle5 6 5) ((2 : Fin 4), (3 : Fin 4), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn565.rows_innerACB HexagonRowColumn565.cols_right1) ((2 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right2Middle5_eq_case_6_5_row_3_0_0 : (right2Middle5 6 5) ((3 : Fin 4), (0 : Fin 4), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn565.rows_innerACB HexagonRowColumn565.cols_right1) ((3 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right2Middle5_eq_case_6_5_row_3_1_0 : (right2Middle5 6 5) ((3 : Fin 4), (1 : Fin 4), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn565.rows_innerACB HexagonRowColumn565.cols_right1) ((3 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right2Middle5_eq_case_6_5_row_3_2_0 : (right2Middle5 6 5) ((3 : Fin 4), (2 : Fin 4), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn565.rows_innerACB HexagonRowColumn565.cols_right1) ((3 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right2Middle5_eq_case_6_5_row_3_3_0 : (right2Middle5 6 5) ((3 : Fin 4), (3 : Fin 4), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn565.rows_innerACB HexagonRowColumn565.cols_right1) ((3 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right2Middle5_eq_case_6_5_checked : right2Middle5 6 5 = rowColumnMul HexagonRowColumn565.rows_innerACB HexagonRowColumn565.cols_right1 := by
  funext r
  fin_cases r
  · exact right2Middle5_eq_case_6_5_row_0_0_0
  · exact right2Middle5_eq_case_6_5_row_0_1_0
  · exact right2Middle5_eq_case_6_5_row_0_2_0
  · exact right2Middle5_eq_case_6_5_row_0_3_0
  · exact right2Middle5_eq_case_6_5_row_1_0_0
  · exact right2Middle5_eq_case_6_5_row_1_1_0
  · exact right2Middle5_eq_case_6_5_row_1_2_0
  · exact right2Middle5_eq_case_6_5_row_1_3_0
  · exact right2Middle5_eq_case_6_5_row_2_0_0
  · exact right2Middle5_eq_case_6_5_row_2_1_0
  · exact right2Middle5_eq_case_6_5_row_2_2_0
  · exact right2Middle5_eq_case_6_5_row_2_3_0
  · exact right2Middle5_eq_case_6_5_row_3_0_0
  · exact right2Middle5_eq_case_6_5_row_3_1_0
  · exact right2Middle5_eq_case_6_5_row_3_2_0
  · exact right2Middle5_eq_case_6_5_row_3_3_0

set_option backward.isDefEq.respectTransparency false in
theorem right2Middle5_eq_case_6_5 : right2Middle5 6 5 = innerLeftZ 5 5 6 * right1Middle5 6 5 := by
  simpa only [HexagonAtoms565.assocABC_eq,
    HexagonAtoms565.outerABC_eq,
    HexagonAtoms565.assocBAC_eq,
    HexagonAtoms565.innerABC_eq,
    HexagonAtoms565.innerRightABC_eq,
    HexagonAtoms565.inverseACB_eq,
    HexagonAtoms565.innerACB_eq,
    HexagonAtoms565.assocBCA_eq,
    HexagonAtoms565.innerRightBAC_eq,
    HexagonAtoms565.assocCAB_eq,
    HexagonAtoms565.outerLeftABC_eq,
    HexagonRowColumn565.assocBCA_alias,
    HexagonRowColumn565.product0_eq,
    HexagonRowColumn565.product1_eq,
    HexagonRowColumn565.product2_eq,
    HexagonRowColumn565.product3_eq,
    HexagonRowColumn565.product4_eq,
    HexagonRowColumn565.product5_eq,
    HexagonRowColumn565.product6_eq,
    HexagonRowColumn565.product7_eq] using right2Middle5_eq_case_6_5_checked

private theorem leftFinal5_case_6_5_row_0_0_0 : (((-1 : ℤ) ^ (leftScaleBit 5 6 5).val * positiveScale (leftScaleExponent 5 6 5)) •
      (rowColumnMul HexagonRowColumn565.rows_assocBAC HexagonRowColumn565.cols_left0)) ((0 : Fin 4), (0 : Fin 4), (0 : Fin 1)) = (negativeScale (leftScaleExponent 5 6 5) • (rowColumnMul HexagonRowColumn565.rows_innerRightBAC HexagonRowColumn565.cols_left1)) ((0 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem leftFinal5_case_6_5_row_0_1_0 : (((-1 : ℤ) ^ (leftScaleBit 5 6 5).val * positiveScale (leftScaleExponent 5 6 5)) •
      (rowColumnMul HexagonRowColumn565.rows_assocBAC HexagonRowColumn565.cols_left0)) ((0 : Fin 4), (1 : Fin 4), (0 : Fin 1)) = (negativeScale (leftScaleExponent 5 6 5) • (rowColumnMul HexagonRowColumn565.rows_innerRightBAC HexagonRowColumn565.cols_left1)) ((0 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem leftFinal5_case_6_5_row_0_2_0 : (((-1 : ℤ) ^ (leftScaleBit 5 6 5).val * positiveScale (leftScaleExponent 5 6 5)) •
      (rowColumnMul HexagonRowColumn565.rows_assocBAC HexagonRowColumn565.cols_left0)) ((0 : Fin 4), (2 : Fin 4), (0 : Fin 1)) = (negativeScale (leftScaleExponent 5 6 5) • (rowColumnMul HexagonRowColumn565.rows_innerRightBAC HexagonRowColumn565.cols_left1)) ((0 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem leftFinal5_case_6_5_row_0_3_0 : (((-1 : ℤ) ^ (leftScaleBit 5 6 5).val * positiveScale (leftScaleExponent 5 6 5)) •
      (rowColumnMul HexagonRowColumn565.rows_assocBAC HexagonRowColumn565.cols_left0)) ((0 : Fin 4), (3 : Fin 4), (0 : Fin 1)) = (negativeScale (leftScaleExponent 5 6 5) • (rowColumnMul HexagonRowColumn565.rows_innerRightBAC HexagonRowColumn565.cols_left1)) ((0 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem leftFinal5_case_6_5_row_1_0_0 : (((-1 : ℤ) ^ (leftScaleBit 5 6 5).val * positiveScale (leftScaleExponent 5 6 5)) •
      (rowColumnMul HexagonRowColumn565.rows_assocBAC HexagonRowColumn565.cols_left0)) ((1 : Fin 4), (0 : Fin 4), (0 : Fin 1)) = (negativeScale (leftScaleExponent 5 6 5) • (rowColumnMul HexagonRowColumn565.rows_innerRightBAC HexagonRowColumn565.cols_left1)) ((1 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem leftFinal5_case_6_5_row_1_1_0 : (((-1 : ℤ) ^ (leftScaleBit 5 6 5).val * positiveScale (leftScaleExponent 5 6 5)) •
      (rowColumnMul HexagonRowColumn565.rows_assocBAC HexagonRowColumn565.cols_left0)) ((1 : Fin 4), (1 : Fin 4), (0 : Fin 1)) = (negativeScale (leftScaleExponent 5 6 5) • (rowColumnMul HexagonRowColumn565.rows_innerRightBAC HexagonRowColumn565.cols_left1)) ((1 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem leftFinal5_case_6_5_row_1_2_0 : (((-1 : ℤ) ^ (leftScaleBit 5 6 5).val * positiveScale (leftScaleExponent 5 6 5)) •
      (rowColumnMul HexagonRowColumn565.rows_assocBAC HexagonRowColumn565.cols_left0)) ((1 : Fin 4), (2 : Fin 4), (0 : Fin 1)) = (negativeScale (leftScaleExponent 5 6 5) • (rowColumnMul HexagonRowColumn565.rows_innerRightBAC HexagonRowColumn565.cols_left1)) ((1 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem leftFinal5_case_6_5_row_1_3_0 : (((-1 : ℤ) ^ (leftScaleBit 5 6 5).val * positiveScale (leftScaleExponent 5 6 5)) •
      (rowColumnMul HexagonRowColumn565.rows_assocBAC HexagonRowColumn565.cols_left0)) ((1 : Fin 4), (3 : Fin 4), (0 : Fin 1)) = (negativeScale (leftScaleExponent 5 6 5) • (rowColumnMul HexagonRowColumn565.rows_innerRightBAC HexagonRowColumn565.cols_left1)) ((1 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem leftFinal5_case_6_5_row_2_0_0 : (((-1 : ℤ) ^ (leftScaleBit 5 6 5).val * positiveScale (leftScaleExponent 5 6 5)) •
      (rowColumnMul HexagonRowColumn565.rows_assocBAC HexagonRowColumn565.cols_left0)) ((2 : Fin 4), (0 : Fin 4), (0 : Fin 1)) = (negativeScale (leftScaleExponent 5 6 5) • (rowColumnMul HexagonRowColumn565.rows_innerRightBAC HexagonRowColumn565.cols_left1)) ((2 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem leftFinal5_case_6_5_row_2_1_0 : (((-1 : ℤ) ^ (leftScaleBit 5 6 5).val * positiveScale (leftScaleExponent 5 6 5)) •
      (rowColumnMul HexagonRowColumn565.rows_assocBAC HexagonRowColumn565.cols_left0)) ((2 : Fin 4), (1 : Fin 4), (0 : Fin 1)) = (negativeScale (leftScaleExponent 5 6 5) • (rowColumnMul HexagonRowColumn565.rows_innerRightBAC HexagonRowColumn565.cols_left1)) ((2 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem leftFinal5_case_6_5_row_2_2_0 : (((-1 : ℤ) ^ (leftScaleBit 5 6 5).val * positiveScale (leftScaleExponent 5 6 5)) •
      (rowColumnMul HexagonRowColumn565.rows_assocBAC HexagonRowColumn565.cols_left0)) ((2 : Fin 4), (2 : Fin 4), (0 : Fin 1)) = (negativeScale (leftScaleExponent 5 6 5) • (rowColumnMul HexagonRowColumn565.rows_innerRightBAC HexagonRowColumn565.cols_left1)) ((2 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem leftFinal5_case_6_5_row_2_3_0 : (((-1 : ℤ) ^ (leftScaleBit 5 6 5).val * positiveScale (leftScaleExponent 5 6 5)) •
      (rowColumnMul HexagonRowColumn565.rows_assocBAC HexagonRowColumn565.cols_left0)) ((2 : Fin 4), (3 : Fin 4), (0 : Fin 1)) = (negativeScale (leftScaleExponent 5 6 5) • (rowColumnMul HexagonRowColumn565.rows_innerRightBAC HexagonRowColumn565.cols_left1)) ((2 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem leftFinal5_case_6_5_row_3_0_0 : (((-1 : ℤ) ^ (leftScaleBit 5 6 5).val * positiveScale (leftScaleExponent 5 6 5)) •
      (rowColumnMul HexagonRowColumn565.rows_assocBAC HexagonRowColumn565.cols_left0)) ((3 : Fin 4), (0 : Fin 4), (0 : Fin 1)) = (negativeScale (leftScaleExponent 5 6 5) • (rowColumnMul HexagonRowColumn565.rows_innerRightBAC HexagonRowColumn565.cols_left1)) ((3 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem leftFinal5_case_6_5_row_3_1_0 : (((-1 : ℤ) ^ (leftScaleBit 5 6 5).val * positiveScale (leftScaleExponent 5 6 5)) •
      (rowColumnMul HexagonRowColumn565.rows_assocBAC HexagonRowColumn565.cols_left0)) ((3 : Fin 4), (1 : Fin 4), (0 : Fin 1)) = (negativeScale (leftScaleExponent 5 6 5) • (rowColumnMul HexagonRowColumn565.rows_innerRightBAC HexagonRowColumn565.cols_left1)) ((3 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem leftFinal5_case_6_5_row_3_2_0 : (((-1 : ℤ) ^ (leftScaleBit 5 6 5).val * positiveScale (leftScaleExponent 5 6 5)) •
      (rowColumnMul HexagonRowColumn565.rows_assocBAC HexagonRowColumn565.cols_left0)) ((3 : Fin 4), (2 : Fin 4), (0 : Fin 1)) = (negativeScale (leftScaleExponent 5 6 5) • (rowColumnMul HexagonRowColumn565.rows_innerRightBAC HexagonRowColumn565.cols_left1)) ((3 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem leftFinal5_case_6_5_row_3_3_0 : (((-1 : ℤ) ^ (leftScaleBit 5 6 5).val * positiveScale (leftScaleExponent 5 6 5)) •
      (rowColumnMul HexagonRowColumn565.rows_assocBAC HexagonRowColumn565.cols_left0)) ((3 : Fin 4), (3 : Fin 4), (0 : Fin 1)) = (negativeScale (leftScaleExponent 5 6 5) • (rowColumnMul HexagonRowColumn565.rows_innerRightBAC HexagonRowColumn565.cols_left1)) ((3 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem leftFinal5_case_6_5_checked : ((-1 : ℤ) ^ (leftScaleBit 5 6 5).val * positiveScale (leftScaleExponent 5 6 5)) •
      (rowColumnMul HexagonRowColumn565.rows_assocBAC HexagonRowColumn565.cols_left0) = negativeScale (leftScaleExponent 5 6 5) • (rowColumnMul HexagonRowColumn565.rows_innerRightBAC HexagonRowColumn565.cols_left1) := by
  funext r
  fin_cases r
  · exact leftFinal5_case_6_5_row_0_0_0
  · exact leftFinal5_case_6_5_row_0_1_0
  · exact leftFinal5_case_6_5_row_0_2_0
  · exact leftFinal5_case_6_5_row_0_3_0
  · exact leftFinal5_case_6_5_row_1_0_0
  · exact leftFinal5_case_6_5_row_1_1_0
  · exact leftFinal5_case_6_5_row_1_2_0
  · exact leftFinal5_case_6_5_row_1_3_0
  · exact leftFinal5_case_6_5_row_2_0_0
  · exact leftFinal5_case_6_5_row_2_1_0
  · exact leftFinal5_case_6_5_row_2_2_0
  · exact leftFinal5_case_6_5_row_2_3_0
  · exact leftFinal5_case_6_5_row_3_0_0
  · exact leftFinal5_case_6_5_row_3_1_0
  · exact leftFinal5_case_6_5_row_3_2_0
  · exact leftFinal5_case_6_5_row_3_3_0

set_option backward.isDefEq.respectTransparency false in
theorem leftFinal5_case_6_5 : ((-1 : ℤ) ^ (leftScaleBit 5 6 5).val * positiveScale (leftScaleExponent 5 6 5)) •
      (associatorZ 6 5 5 * left0Middle5 6 5) = negativeScale (leftScaleExponent 5 6 5) • (innerRightZ 6 5 5 * left1Middle5 6 5) := by
  simpa only [HexagonAtoms565.assocABC_eq,
    HexagonAtoms565.outerABC_eq,
    HexagonAtoms565.assocBAC_eq,
    HexagonAtoms565.innerABC_eq,
    HexagonAtoms565.innerRightABC_eq,
    HexagonAtoms565.inverseACB_eq,
    HexagonAtoms565.innerACB_eq,
    HexagonAtoms565.assocBCA_eq,
    HexagonAtoms565.innerRightBAC_eq,
    HexagonAtoms565.assocCAB_eq,
    HexagonAtoms565.outerLeftABC_eq,
    HexagonRowColumn565.assocBCA_alias,
    HexagonRowColumn565.product0_eq,
    HexagonRowColumn565.product1_eq,
    HexagonRowColumn565.product2_eq,
    HexagonRowColumn565.product3_eq,
    HexagonRowColumn565.product4_eq,
    HexagonRowColumn565.product5_eq,
    HexagonRowColumn565.product6_eq,
    HexagonRowColumn565.product7_eq] using leftFinal5_case_6_5_checked

private theorem rightFinal5_case_6_5_row_0_0_0 : (((-1 : ℤ) ^ (rightScaleBit 5 6 5).val * positiveScale (rightScaleExponent 5 6 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 5 6 : ℤ)) • HexagonAtoms565.outerLeftABC) ((0 : Fin 2), (0 : Fin 8), (0 : Fin 1)) = (negativeScale (rightScaleExponent 5 6 5) • (rowColumnMul HexagonRowColumn565.rows_assocCAB HexagonRowColumn565.cols_right2)) ((0 : Fin 2), (0 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem rightFinal5_case_6_5_row_0_1_0 : (((-1 : ℤ) ^ (rightScaleBit 5 6 5).val * positiveScale (rightScaleExponent 5 6 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 5 6 : ℤ)) • HexagonAtoms565.outerLeftABC) ((0 : Fin 2), (1 : Fin 8), (0 : Fin 1)) = (negativeScale (rightScaleExponent 5 6 5) • (rowColumnMul HexagonRowColumn565.rows_assocCAB HexagonRowColumn565.cols_right2)) ((0 : Fin 2), (1 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem rightFinal5_case_6_5_row_0_2_0 : (((-1 : ℤ) ^ (rightScaleBit 5 6 5).val * positiveScale (rightScaleExponent 5 6 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 5 6 : ℤ)) • HexagonAtoms565.outerLeftABC) ((0 : Fin 2), (2 : Fin 8), (0 : Fin 1)) = (negativeScale (rightScaleExponent 5 6 5) • (rowColumnMul HexagonRowColumn565.rows_assocCAB HexagonRowColumn565.cols_right2)) ((0 : Fin 2), (2 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem rightFinal5_case_6_5_row_0_3_0 : (((-1 : ℤ) ^ (rightScaleBit 5 6 5).val * positiveScale (rightScaleExponent 5 6 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 5 6 : ℤ)) • HexagonAtoms565.outerLeftABC) ((0 : Fin 2), (3 : Fin 8), (0 : Fin 1)) = (negativeScale (rightScaleExponent 5 6 5) • (rowColumnMul HexagonRowColumn565.rows_assocCAB HexagonRowColumn565.cols_right2)) ((0 : Fin 2), (3 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem rightFinal5_case_6_5_row_0_4_0 : (((-1 : ℤ) ^ (rightScaleBit 5 6 5).val * positiveScale (rightScaleExponent 5 6 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 5 6 : ℤ)) • HexagonAtoms565.outerLeftABC) ((0 : Fin 2), (4 : Fin 8), (0 : Fin 1)) = (negativeScale (rightScaleExponent 5 6 5) • (rowColumnMul HexagonRowColumn565.rows_assocCAB HexagonRowColumn565.cols_right2)) ((0 : Fin 2), (4 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem rightFinal5_case_6_5_row_0_5_0 : (((-1 : ℤ) ^ (rightScaleBit 5 6 5).val * positiveScale (rightScaleExponent 5 6 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 5 6 : ℤ)) • HexagonAtoms565.outerLeftABC) ((0 : Fin 2), (5 : Fin 8), (0 : Fin 1)) = (negativeScale (rightScaleExponent 5 6 5) • (rowColumnMul HexagonRowColumn565.rows_assocCAB HexagonRowColumn565.cols_right2)) ((0 : Fin 2), (5 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem rightFinal5_case_6_5_row_0_6_0 : (((-1 : ℤ) ^ (rightScaleBit 5 6 5).val * positiveScale (rightScaleExponent 5 6 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 5 6 : ℤ)) • HexagonAtoms565.outerLeftABC) ((0 : Fin 2), (6 : Fin 8), (0 : Fin 1)) = (negativeScale (rightScaleExponent 5 6 5) • (rowColumnMul HexagonRowColumn565.rows_assocCAB HexagonRowColumn565.cols_right2)) ((0 : Fin 2), (6 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem rightFinal5_case_6_5_row_0_7_0 : (((-1 : ℤ) ^ (rightScaleBit 5 6 5).val * positiveScale (rightScaleExponent 5 6 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 5 6 : ℤ)) • HexagonAtoms565.outerLeftABC) ((0 : Fin 2), (7 : Fin 8), (0 : Fin 1)) = (negativeScale (rightScaleExponent 5 6 5) • (rowColumnMul HexagonRowColumn565.rows_assocCAB HexagonRowColumn565.cols_right2)) ((0 : Fin 2), (7 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem rightFinal5_case_6_5_row_1_0_0 : (((-1 : ℤ) ^ (rightScaleBit 5 6 5).val * positiveScale (rightScaleExponent 5 6 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 5 6 : ℤ)) • HexagonAtoms565.outerLeftABC) ((1 : Fin 2), (0 : Fin 8), (0 : Fin 1)) = (negativeScale (rightScaleExponent 5 6 5) • (rowColumnMul HexagonRowColumn565.rows_assocCAB HexagonRowColumn565.cols_right2)) ((1 : Fin 2), (0 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem rightFinal5_case_6_5_row_1_1_0 : (((-1 : ℤ) ^ (rightScaleBit 5 6 5).val * positiveScale (rightScaleExponent 5 6 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 5 6 : ℤ)) • HexagonAtoms565.outerLeftABC) ((1 : Fin 2), (1 : Fin 8), (0 : Fin 1)) = (negativeScale (rightScaleExponent 5 6 5) • (rowColumnMul HexagonRowColumn565.rows_assocCAB HexagonRowColumn565.cols_right2)) ((1 : Fin 2), (1 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem rightFinal5_case_6_5_row_1_2_0 : (((-1 : ℤ) ^ (rightScaleBit 5 6 5).val * positiveScale (rightScaleExponent 5 6 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 5 6 : ℤ)) • HexagonAtoms565.outerLeftABC) ((1 : Fin 2), (2 : Fin 8), (0 : Fin 1)) = (negativeScale (rightScaleExponent 5 6 5) • (rowColumnMul HexagonRowColumn565.rows_assocCAB HexagonRowColumn565.cols_right2)) ((1 : Fin 2), (2 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem rightFinal5_case_6_5_row_1_3_0 : (((-1 : ℤ) ^ (rightScaleBit 5 6 5).val * positiveScale (rightScaleExponent 5 6 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 5 6 : ℤ)) • HexagonAtoms565.outerLeftABC) ((1 : Fin 2), (3 : Fin 8), (0 : Fin 1)) = (negativeScale (rightScaleExponent 5 6 5) • (rowColumnMul HexagonRowColumn565.rows_assocCAB HexagonRowColumn565.cols_right2)) ((1 : Fin 2), (3 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem rightFinal5_case_6_5_row_1_4_0 : (((-1 : ℤ) ^ (rightScaleBit 5 6 5).val * positiveScale (rightScaleExponent 5 6 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 5 6 : ℤ)) • HexagonAtoms565.outerLeftABC) ((1 : Fin 2), (4 : Fin 8), (0 : Fin 1)) = (negativeScale (rightScaleExponent 5 6 5) • (rowColumnMul HexagonRowColumn565.rows_assocCAB HexagonRowColumn565.cols_right2)) ((1 : Fin 2), (4 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem rightFinal5_case_6_5_row_1_5_0 : (((-1 : ℤ) ^ (rightScaleBit 5 6 5).val * positiveScale (rightScaleExponent 5 6 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 5 6 : ℤ)) • HexagonAtoms565.outerLeftABC) ((1 : Fin 2), (5 : Fin 8), (0 : Fin 1)) = (negativeScale (rightScaleExponent 5 6 5) • (rowColumnMul HexagonRowColumn565.rows_assocCAB HexagonRowColumn565.cols_right2)) ((1 : Fin 2), (5 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem rightFinal5_case_6_5_row_1_6_0 : (((-1 : ℤ) ^ (rightScaleBit 5 6 5).val * positiveScale (rightScaleExponent 5 6 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 5 6 : ℤ)) • HexagonAtoms565.outerLeftABC) ((1 : Fin 2), (6 : Fin 8), (0 : Fin 1)) = (negativeScale (rightScaleExponent 5 6 5) • (rowColumnMul HexagonRowColumn565.rows_assocCAB HexagonRowColumn565.cols_right2)) ((1 : Fin 2), (6 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem rightFinal5_case_6_5_row_1_7_0 : (((-1 : ℤ) ^ (rightScaleBit 5 6 5).val * positiveScale (rightScaleExponent 5 6 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 5 6 : ℤ)) • HexagonAtoms565.outerLeftABC) ((1 : Fin 2), (7 : Fin 8), (0 : Fin 1)) = (negativeScale (rightScaleExponent 5 6 5) • (rowColumnMul HexagonRowColumn565.rows_assocCAB HexagonRowColumn565.cols_right2)) ((1 : Fin 2), (7 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem rightFinal5_case_6_5_checked : ((-1 : ℤ) ^ (rightScaleBit 5 6 5).val * positiveScale (rightScaleExponent 5 6 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 5 6 : ℤ)) • HexagonAtoms565.outerLeftABC = negativeScale (rightScaleExponent 5 6 5) • (rowColumnMul HexagonRowColumn565.rows_assocCAB HexagonRowColumn565.cols_right2) := by
  funext r
  fin_cases r
  · exact rightFinal5_case_6_5_row_0_0_0
  · exact rightFinal5_case_6_5_row_0_1_0
  · exact rightFinal5_case_6_5_row_0_2_0
  · exact rightFinal5_case_6_5_row_0_3_0
  · exact rightFinal5_case_6_5_row_0_4_0
  · exact rightFinal5_case_6_5_row_0_5_0
  · exact rightFinal5_case_6_5_row_0_6_0
  · exact rightFinal5_case_6_5_row_0_7_0
  · exact rightFinal5_case_6_5_row_1_0_0
  · exact rightFinal5_case_6_5_row_1_1_0
  · exact rightFinal5_case_6_5_row_1_2_0
  · exact rightFinal5_case_6_5_row_1_3_0
  · exact rightFinal5_case_6_5_row_1_4_0
  · exact rightFinal5_case_6_5_row_1_5_0
  · exact rightFinal5_case_6_5_row_1_6_0
  · exact rightFinal5_case_6_5_row_1_7_0

set_option backward.isDefEq.respectTransparency false in
theorem rightFinal5_case_6_5 : ((-1 : ℤ) ^ (rightScaleBit 5 6 5).val * positiveScale (rightScaleExponent 5 6 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 5 6 : ℤ)) • outerLeftZ 5 6 5 = negativeScale (rightScaleExponent 5 6 5) • (associatorZ 5 5 6 * right2Middle5 6 5) := by
  simpa only [HexagonAtoms565.assocABC_eq,
    HexagonAtoms565.outerABC_eq,
    HexagonAtoms565.assocBAC_eq,
    HexagonAtoms565.innerABC_eq,
    HexagonAtoms565.innerRightABC_eq,
    HexagonAtoms565.inverseACB_eq,
    HexagonAtoms565.innerACB_eq,
    HexagonAtoms565.assocBCA_eq,
    HexagonAtoms565.innerRightBAC_eq,
    HexagonAtoms565.assocCAB_eq,
    HexagonAtoms565.outerLeftABC_eq,
    HexagonRowColumn565.assocBCA_alias,
    HexagonRowColumn565.product0_eq,
    HexagonRowColumn565.product1_eq,
    HexagonRowColumn565.product2_eq,
    HexagonRowColumn565.product3_eq,
    HexagonRowColumn565.product4_eq,
    HexagonRowColumn565.product5_eq,
    HexagonRowColumn565.product6_eq,
    HexagonRowColumn565.product7_eq] using rightFinal5_case_6_5_checked

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonCases5
