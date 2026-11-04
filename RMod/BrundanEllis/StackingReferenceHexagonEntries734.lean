import RMod.BrundanEllis.StackingReferenceHexagonMiddle7
import RMod.BrundanEllis.StackingReferenceSparseMatrixCheck
import RMod.BrundanEllis.StackingReferenceHexagonAtoms734
import RMod.BrundanEllis.StackingReferenceHexagonRowColumn734

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

private theorem left0Middle7_eq_case_3_4_row_0_0_0 : (left0Middle7 3 4) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn734.rows_outerABC HexagonRowColumn734.cols_assocABC) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle7_eq_case_3_4_row_0_0_1 : (left0Middle7 3 4) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn734.rows_outerABC HexagonRowColumn734.cols_assocABC) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle7_eq_case_3_4_row_0_0_2 : (left0Middle7 3 4) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn734.rows_outerABC HexagonRowColumn734.cols_assocABC) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle7_eq_case_3_4_row_0_0_3 : (left0Middle7 3 4) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn734.rows_outerABC HexagonRowColumn734.cols_assocABC) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle7_eq_case_3_4_row_1_0_0 : (left0Middle7 3 4) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn734.rows_outerABC HexagonRowColumn734.cols_assocABC) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle7_eq_case_3_4_row_1_0_1 : (left0Middle7 3 4) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn734.rows_outerABC HexagonRowColumn734.cols_assocABC) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle7_eq_case_3_4_row_1_0_2 : (left0Middle7 3 4) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn734.rows_outerABC HexagonRowColumn734.cols_assocABC) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle7_eq_case_3_4_row_1_0_3 : (left0Middle7 3 4) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn734.rows_outerABC HexagonRowColumn734.cols_assocABC) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle7_eq_case_3_4_row_2_0_0 : (left0Middle7 3 4) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn734.rows_outerABC HexagonRowColumn734.cols_assocABC) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle7_eq_case_3_4_row_2_0_1 : (left0Middle7 3 4) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn734.rows_outerABC HexagonRowColumn734.cols_assocABC) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle7_eq_case_3_4_row_2_0_2 : (left0Middle7 3 4) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn734.rows_outerABC HexagonRowColumn734.cols_assocABC) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle7_eq_case_3_4_row_2_0_3 : (left0Middle7 3 4) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn734.rows_outerABC HexagonRowColumn734.cols_assocABC) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle7_eq_case_3_4_row_3_0_0 : (left0Middle7 3 4) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn734.rows_outerABC HexagonRowColumn734.cols_assocABC) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle7_eq_case_3_4_row_3_0_1 : (left0Middle7 3 4) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn734.rows_outerABC HexagonRowColumn734.cols_assocABC) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle7_eq_case_3_4_row_3_0_2 : (left0Middle7 3 4) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn734.rows_outerABC HexagonRowColumn734.cols_assocABC) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle7_eq_case_3_4_row_3_0_3 : (left0Middle7 3 4) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn734.rows_outerABC HexagonRowColumn734.cols_assocABC) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle7_eq_case_3_4_checked : left0Middle7 3 4 = rowColumnMul HexagonRowColumn734.rows_outerABC HexagonRowColumn734.cols_assocABC := by
  funext r
  fin_cases r
  · exact left0Middle7_eq_case_3_4_row_0_0_0
  · exact left0Middle7_eq_case_3_4_row_0_0_1
  · exact left0Middle7_eq_case_3_4_row_0_0_2
  · exact left0Middle7_eq_case_3_4_row_0_0_3
  · exact left0Middle7_eq_case_3_4_row_1_0_0
  · exact left0Middle7_eq_case_3_4_row_1_0_1
  · exact left0Middle7_eq_case_3_4_row_1_0_2
  · exact left0Middle7_eq_case_3_4_row_1_0_3
  · exact left0Middle7_eq_case_3_4_row_2_0_0
  · exact left0Middle7_eq_case_3_4_row_2_0_1
  · exact left0Middle7_eq_case_3_4_row_2_0_2
  · exact left0Middle7_eq_case_3_4_row_2_0_3
  · exact left0Middle7_eq_case_3_4_row_3_0_0
  · exact left0Middle7_eq_case_3_4_row_3_0_1
  · exact left0Middle7_eq_case_3_4_row_3_0_2
  · exact left0Middle7_eq_case_3_4_row_3_0_3

set_option backward.isDefEq.respectTransparency false in
theorem left0Middle7_eq_case_3_4 : left0Middle7 3 4 = outerRightZ 7 3 4 * associatorZ 7 3 4 := by
  simpa only [HexagonAtoms734.assocABC_eq,
    HexagonAtoms734.outerABC_eq,
    HexagonAtoms734.assocBAC_eq,
    HexagonAtoms734.innerABC_eq,
    HexagonAtoms734.innerRightABC_eq,
    HexagonAtoms734.inverseACB_eq,
    HexagonAtoms734.innerACB_eq,
    HexagonAtoms734.assocBCA_eq,
    HexagonAtoms734.innerRightBAC_eq,
    HexagonAtoms734.assocCAB_eq,
    HexagonAtoms734.outerLeftABC_eq,
    HexagonRowColumn734.product0_eq,
    HexagonRowColumn734.product1_eq,
    HexagonRowColumn734.product2_eq,
    HexagonRowColumn734.product3_eq,
    HexagonRowColumn734.product4_eq,
    HexagonRowColumn734.product5_eq,
    HexagonRowColumn734.product6_eq,
    HexagonRowColumn734.product7_eq] using left0Middle7_eq_case_3_4_checked

private theorem left1Middle7_eq_case_3_4_row_0_0_0 : (left1Middle7 3 4) ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4)) = (HexagonAtoms734.assocBAC) ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle7_eq_case_3_4_row_0_0_1 : (left1Middle7 3 4) ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4)) = (HexagonAtoms734.assocBAC) ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle7_eq_case_3_4_row_0_0_2 : (left1Middle7 3 4) ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4)) = (HexagonAtoms734.assocBAC) ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle7_eq_case_3_4_row_0_0_3 : (left1Middle7 3 4) ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4)) = (HexagonAtoms734.assocBAC) ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle7_eq_case_3_4_row_0_1_0 : (left1Middle7 3 4) ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4)) = (HexagonAtoms734.assocBAC) ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle7_eq_case_3_4_row_0_1_1 : (left1Middle7 3 4) ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4)) = (HexagonAtoms734.assocBAC) ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle7_eq_case_3_4_row_0_1_2 : (left1Middle7 3 4) ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4)) = (HexagonAtoms734.assocBAC) ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle7_eq_case_3_4_row_0_1_3 : (left1Middle7 3 4) ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4)) = (HexagonAtoms734.assocBAC) ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle7_eq_case_3_4_row_0_2_0 : (left1Middle7 3 4) ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4)) = (HexagonAtoms734.assocBAC) ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle7_eq_case_3_4_row_0_2_1 : (left1Middle7 3 4) ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4)) = (HexagonAtoms734.assocBAC) ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle7_eq_case_3_4_row_0_2_2 : (left1Middle7 3 4) ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4)) = (HexagonAtoms734.assocBAC) ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle7_eq_case_3_4_row_0_2_3 : (left1Middle7 3 4) ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4)) = (HexagonAtoms734.assocBAC) ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle7_eq_case_3_4_row_0_3_0 : (left1Middle7 3 4) ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4)) = (HexagonAtoms734.assocBAC) ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle7_eq_case_3_4_row_0_3_1 : (left1Middle7 3 4) ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4)) = (HexagonAtoms734.assocBAC) ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle7_eq_case_3_4_row_0_3_2 : (left1Middle7 3 4) ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4)) = (HexagonAtoms734.assocBAC) ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle7_eq_case_3_4_row_0_3_3 : (left1Middle7 3 4) ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4)) = (HexagonAtoms734.assocBAC) ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle7_eq_case_3_4_checked : left1Middle7 3 4 = HexagonAtoms734.assocBAC := by
  funext r
  fin_cases r
  · exact left1Middle7_eq_case_3_4_row_0_0_0
  · exact left1Middle7_eq_case_3_4_row_0_0_1
  · exact left1Middle7_eq_case_3_4_row_0_0_2
  · exact left1Middle7_eq_case_3_4_row_0_0_3
  · exact left1Middle7_eq_case_3_4_row_0_1_0
  · exact left1Middle7_eq_case_3_4_row_0_1_1
  · exact left1Middle7_eq_case_3_4_row_0_1_2
  · exact left1Middle7_eq_case_3_4_row_0_1_3
  · exact left1Middle7_eq_case_3_4_row_0_2_0
  · exact left1Middle7_eq_case_3_4_row_0_2_1
  · exact left1Middle7_eq_case_3_4_row_0_2_2
  · exact left1Middle7_eq_case_3_4_row_0_2_3
  · exact left1Middle7_eq_case_3_4_row_0_3_0
  · exact left1Middle7_eq_case_3_4_row_0_3_1
  · exact left1Middle7_eq_case_3_4_row_0_3_2
  · exact left1Middle7_eq_case_3_4_row_0_3_3

set_option backward.isDefEq.respectTransparency false in
theorem left1Middle7_eq_case_3_4 : left1Middle7 3 4 = associatorZ 3 7 4 * innerLeftZ 7 3 4 := by
  simpa only [HexagonAtoms734.assocABC_eq,
    HexagonAtoms734.outerABC_eq,
    HexagonAtoms734.assocBAC_eq,
    HexagonAtoms734.innerABC_eq,
    HexagonAtoms734.innerRightABC_eq,
    HexagonAtoms734.inverseACB_eq,
    HexagonAtoms734.innerACB_eq,
    HexagonAtoms734.assocBCA_eq,
    HexagonAtoms734.innerRightBAC_eq,
    HexagonAtoms734.assocCAB_eq,
    HexagonAtoms734.outerLeftABC_eq,
    HexagonRowColumn734.product0_eq,
    HexagonRowColumn734.product1_eq,
    HexagonRowColumn734.product2_eq,
    HexagonRowColumn734.product3_eq,
    HexagonRowColumn734.product4_eq,
    HexagonRowColumn734.product5_eq,
    HexagonRowColumn734.product6_eq,
    HexagonRowColumn734.product7_eq] using left1Middle7_eq_case_3_4_checked

private theorem right0Middle7_eq_case_3_4_row_0_0_0 : (right0Middle7 3 4) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms734.assocABC) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle7_eq_case_3_4_row_0_0_1 : (right0Middle7 3 4) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms734.assocABC) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle7_eq_case_3_4_row_0_0_2 : (right0Middle7 3 4) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms734.assocABC) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle7_eq_case_3_4_row_0_0_3 : (right0Middle7 3 4) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms734.assocABC) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle7_eq_case_3_4_row_1_0_0 : (right0Middle7 3 4) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms734.assocABC) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle7_eq_case_3_4_row_1_0_1 : (right0Middle7 3 4) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms734.assocABC) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle7_eq_case_3_4_row_1_0_2 : (right0Middle7 3 4) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms734.assocABC) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle7_eq_case_3_4_row_1_0_3 : (right0Middle7 3 4) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms734.assocABC) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle7_eq_case_3_4_row_2_0_0 : (right0Middle7 3 4) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms734.assocABC) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle7_eq_case_3_4_row_2_0_1 : (right0Middle7 3 4) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms734.assocABC) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle7_eq_case_3_4_row_2_0_2 : (right0Middle7 3 4) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms734.assocABC) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle7_eq_case_3_4_row_2_0_3 : (right0Middle7 3 4) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms734.assocABC) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle7_eq_case_3_4_row_3_0_0 : (right0Middle7 3 4) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms734.assocABC) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle7_eq_case_3_4_row_3_0_1 : (right0Middle7 3 4) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms734.assocABC) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle7_eq_case_3_4_row_3_0_2 : (right0Middle7 3 4) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms734.assocABC) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle7_eq_case_3_4_row_3_0_3 : (right0Middle7 3 4) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms734.assocABC) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle7_eq_case_3_4_checked : right0Middle7 3 4 = HexagonAtoms734.assocABC := by
  funext r
  fin_cases r
  · exact right0Middle7_eq_case_3_4_row_0_0_0
  · exact right0Middle7_eq_case_3_4_row_0_0_1
  · exact right0Middle7_eq_case_3_4_row_0_0_2
  · exact right0Middle7_eq_case_3_4_row_0_0_3
  · exact right0Middle7_eq_case_3_4_row_1_0_0
  · exact right0Middle7_eq_case_3_4_row_1_0_1
  · exact right0Middle7_eq_case_3_4_row_1_0_2
  · exact right0Middle7_eq_case_3_4_row_1_0_3
  · exact right0Middle7_eq_case_3_4_row_2_0_0
  · exact right0Middle7_eq_case_3_4_row_2_0_1
  · exact right0Middle7_eq_case_3_4_row_2_0_2
  · exact right0Middle7_eq_case_3_4_row_2_0_3
  · exact right0Middle7_eq_case_3_4_row_3_0_0
  · exact right0Middle7_eq_case_3_4_row_3_0_1
  · exact right0Middle7_eq_case_3_4_row_3_0_2
  · exact right0Middle7_eq_case_3_4_row_3_0_3

set_option backward.isDefEq.respectTransparency false in
theorem right0Middle7_eq_case_3_4 : right0Middle7 3 4 = innerRightZ 7 3 4 * associatorZ 7 3 4 := by
  simpa only [HexagonAtoms734.assocABC_eq,
    HexagonAtoms734.outerABC_eq,
    HexagonAtoms734.assocBAC_eq,
    HexagonAtoms734.innerABC_eq,
    HexagonAtoms734.innerRightABC_eq,
    HexagonAtoms734.inverseACB_eq,
    HexagonAtoms734.innerACB_eq,
    HexagonAtoms734.assocBCA_eq,
    HexagonAtoms734.innerRightBAC_eq,
    HexagonAtoms734.assocCAB_eq,
    HexagonAtoms734.outerLeftABC_eq,
    HexagonRowColumn734.product0_eq,
    HexagonRowColumn734.product1_eq,
    HexagonRowColumn734.product2_eq,
    HexagonRowColumn734.product3_eq,
    HexagonRowColumn734.product4_eq,
    HexagonRowColumn734.product5_eq,
    HexagonRowColumn734.product6_eq,
    HexagonRowColumn734.product7_eq] using right0Middle7_eq_case_3_4_checked

private theorem right1Middle7_eq_case_3_4_row_0_0_0 : (right1Middle7 3 4) ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn734.rows_inverseACB HexagonRowColumn734.cols_right0) ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle7_eq_case_3_4_row_0_0_1 : (right1Middle7 3 4) ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn734.rows_inverseACB HexagonRowColumn734.cols_right0) ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle7_eq_case_3_4_row_0_0_2 : (right1Middle7 3 4) ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn734.rows_inverseACB HexagonRowColumn734.cols_right0) ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle7_eq_case_3_4_row_0_0_3 : (right1Middle7 3 4) ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn734.rows_inverseACB HexagonRowColumn734.cols_right0) ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle7_eq_case_3_4_row_0_1_0 : (right1Middle7 3 4) ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn734.rows_inverseACB HexagonRowColumn734.cols_right0) ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle7_eq_case_3_4_row_0_1_1 : (right1Middle7 3 4) ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn734.rows_inverseACB HexagonRowColumn734.cols_right0) ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle7_eq_case_3_4_row_0_1_2 : (right1Middle7 3 4) ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn734.rows_inverseACB HexagonRowColumn734.cols_right0) ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle7_eq_case_3_4_row_0_1_3 : (right1Middle7 3 4) ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn734.rows_inverseACB HexagonRowColumn734.cols_right0) ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle7_eq_case_3_4_row_0_2_0 : (right1Middle7 3 4) ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn734.rows_inverseACB HexagonRowColumn734.cols_right0) ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle7_eq_case_3_4_row_0_2_1 : (right1Middle7 3 4) ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn734.rows_inverseACB HexagonRowColumn734.cols_right0) ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle7_eq_case_3_4_row_0_2_2 : (right1Middle7 3 4) ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn734.rows_inverseACB HexagonRowColumn734.cols_right0) ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle7_eq_case_3_4_row_0_2_3 : (right1Middle7 3 4) ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn734.rows_inverseACB HexagonRowColumn734.cols_right0) ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle7_eq_case_3_4_row_0_3_0 : (right1Middle7 3 4) ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn734.rows_inverseACB HexagonRowColumn734.cols_right0) ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle7_eq_case_3_4_row_0_3_1 : (right1Middle7 3 4) ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn734.rows_inverseACB HexagonRowColumn734.cols_right0) ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle7_eq_case_3_4_row_0_3_2 : (right1Middle7 3 4) ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn734.rows_inverseACB HexagonRowColumn734.cols_right0) ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle7_eq_case_3_4_row_0_3_3 : (right1Middle7 3 4) ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn734.rows_inverseACB HexagonRowColumn734.cols_right0) ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle7_eq_case_3_4_checked : right1Middle7 3 4 = rowColumnMul HexagonRowColumn734.rows_inverseACB HexagonRowColumn734.cols_right0 := by
  funext r
  fin_cases r
  · exact right1Middle7_eq_case_3_4_row_0_0_0
  · exact right1Middle7_eq_case_3_4_row_0_0_1
  · exact right1Middle7_eq_case_3_4_row_0_0_2
  · exact right1Middle7_eq_case_3_4_row_0_0_3
  · exact right1Middle7_eq_case_3_4_row_0_1_0
  · exact right1Middle7_eq_case_3_4_row_0_1_1
  · exact right1Middle7_eq_case_3_4_row_0_1_2
  · exact right1Middle7_eq_case_3_4_row_0_1_3
  · exact right1Middle7_eq_case_3_4_row_0_2_0
  · exact right1Middle7_eq_case_3_4_row_0_2_1
  · exact right1Middle7_eq_case_3_4_row_0_2_2
  · exact right1Middle7_eq_case_3_4_row_0_2_3
  · exact right1Middle7_eq_case_3_4_row_0_3_0
  · exact right1Middle7_eq_case_3_4_row_0_3_1
  · exact right1Middle7_eq_case_3_4_row_0_3_2
  · exact right1Middle7_eq_case_3_4_row_0_3_3

set_option backward.isDefEq.respectTransparency false in
theorem right1Middle7_eq_case_3_4 : right1Middle7 3 4 = associatorInverseZ 7 4 3 * right0Middle7 3 4 := by
  simpa only [HexagonAtoms734.assocABC_eq,
    HexagonAtoms734.outerABC_eq,
    HexagonAtoms734.assocBAC_eq,
    HexagonAtoms734.innerABC_eq,
    HexagonAtoms734.innerRightABC_eq,
    HexagonAtoms734.inverseACB_eq,
    HexagonAtoms734.innerACB_eq,
    HexagonAtoms734.assocBCA_eq,
    HexagonAtoms734.innerRightBAC_eq,
    HexagonAtoms734.assocCAB_eq,
    HexagonAtoms734.outerLeftABC_eq,
    HexagonRowColumn734.product0_eq,
    HexagonRowColumn734.product1_eq,
    HexagonRowColumn734.product2_eq,
    HexagonRowColumn734.product3_eq,
    HexagonRowColumn734.product4_eq,
    HexagonRowColumn734.product5_eq,
    HexagonRowColumn734.product6_eq,
    HexagonRowColumn734.product7_eq] using right1Middle7_eq_case_3_4_checked

private theorem right2Middle7_eq_case_3_4_row_0_0_0 : (right2Middle7 3 4) ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4)) = (right1Middle7 3 4) ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle7_eq_case_3_4_row_0_0_1 : (right2Middle7 3 4) ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4)) = (right1Middle7 3 4) ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle7_eq_case_3_4_row_0_0_2 : (right2Middle7 3 4) ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4)) = (right1Middle7 3 4) ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle7_eq_case_3_4_row_0_0_3 : (right2Middle7 3 4) ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4)) = (right1Middle7 3 4) ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle7_eq_case_3_4_row_0_1_0 : (right2Middle7 3 4) ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4)) = (right1Middle7 3 4) ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle7_eq_case_3_4_row_0_1_1 : (right2Middle7 3 4) ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4)) = (right1Middle7 3 4) ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle7_eq_case_3_4_row_0_1_2 : (right2Middle7 3 4) ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4)) = (right1Middle7 3 4) ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle7_eq_case_3_4_row_0_1_3 : (right2Middle7 3 4) ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4)) = (right1Middle7 3 4) ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle7_eq_case_3_4_row_0_2_0 : (right2Middle7 3 4) ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4)) = (right1Middle7 3 4) ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle7_eq_case_3_4_row_0_2_1 : (right2Middle7 3 4) ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4)) = (right1Middle7 3 4) ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle7_eq_case_3_4_row_0_2_2 : (right2Middle7 3 4) ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4)) = (right1Middle7 3 4) ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle7_eq_case_3_4_row_0_2_3 : (right2Middle7 3 4) ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4)) = (right1Middle7 3 4) ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle7_eq_case_3_4_row_0_3_0 : (right2Middle7 3 4) ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4)) = (right1Middle7 3 4) ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle7_eq_case_3_4_row_0_3_1 : (right2Middle7 3 4) ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4)) = (right1Middle7 3 4) ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle7_eq_case_3_4_row_0_3_2 : (right2Middle7 3 4) ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4)) = (right1Middle7 3 4) ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle7_eq_case_3_4_row_0_3_3 : (right2Middle7 3 4) ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4)) = (right1Middle7 3 4) ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle7_eq_case_3_4_checked : right2Middle7 3 4 = right1Middle7 3 4 := by
  funext r
  fin_cases r
  · exact right2Middle7_eq_case_3_4_row_0_0_0
  · exact right2Middle7_eq_case_3_4_row_0_0_1
  · exact right2Middle7_eq_case_3_4_row_0_0_2
  · exact right2Middle7_eq_case_3_4_row_0_0_3
  · exact right2Middle7_eq_case_3_4_row_0_1_0
  · exact right2Middle7_eq_case_3_4_row_0_1_1
  · exact right2Middle7_eq_case_3_4_row_0_1_2
  · exact right2Middle7_eq_case_3_4_row_0_1_3
  · exact right2Middle7_eq_case_3_4_row_0_2_0
  · exact right2Middle7_eq_case_3_4_row_0_2_1
  · exact right2Middle7_eq_case_3_4_row_0_2_2
  · exact right2Middle7_eq_case_3_4_row_0_2_3
  · exact right2Middle7_eq_case_3_4_row_0_3_0
  · exact right2Middle7_eq_case_3_4_row_0_3_1
  · exact right2Middle7_eq_case_3_4_row_0_3_2
  · exact right2Middle7_eq_case_3_4_row_0_3_3

set_option backward.isDefEq.respectTransparency false in
theorem right2Middle7_eq_case_3_4 : right2Middle7 3 4 = innerLeftZ 7 4 3 * right1Middle7 3 4 := by
  simpa only [HexagonAtoms734.assocABC_eq,
    HexagonAtoms734.outerABC_eq,
    HexagonAtoms734.assocBAC_eq,
    HexagonAtoms734.innerABC_eq,
    HexagonAtoms734.innerRightABC_eq,
    HexagonAtoms734.inverseACB_eq,
    HexagonAtoms734.innerACB_eq,
    HexagonAtoms734.assocBCA_eq,
    HexagonAtoms734.innerRightBAC_eq,
    HexagonAtoms734.assocCAB_eq,
    HexagonAtoms734.outerLeftABC_eq,
    HexagonRowColumn734.product0_eq,
    HexagonRowColumn734.product1_eq,
    HexagonRowColumn734.product2_eq,
    HexagonRowColumn734.product3_eq,
    HexagonRowColumn734.product4_eq,
    HexagonRowColumn734.product5_eq,
    HexagonRowColumn734.product6_eq,
    HexagonRowColumn734.product7_eq] using right2Middle7_eq_case_3_4_checked

private theorem leftFinal7_case_3_4_row_0_0_0 : (((-1 : ℤ) ^ (leftScaleBit 7 3 4).val * positiveScale (leftScaleExponent 7 3 4)) •
      (rowColumnMul HexagonRowColumn734.rows_assocBCA HexagonRowColumn734.cols_left0)) ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4)) = (negativeScale (leftScaleExponent 7 3 4) • (left1Middle7 3 4)) ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal7_case_3_4_row_0_0_1 : (((-1 : ℤ) ^ (leftScaleBit 7 3 4).val * positiveScale (leftScaleExponent 7 3 4)) •
      (rowColumnMul HexagonRowColumn734.rows_assocBCA HexagonRowColumn734.cols_left0)) ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4)) = (negativeScale (leftScaleExponent 7 3 4) • (left1Middle7 3 4)) ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal7_case_3_4_row_0_0_2 : (((-1 : ℤ) ^ (leftScaleBit 7 3 4).val * positiveScale (leftScaleExponent 7 3 4)) •
      (rowColumnMul HexagonRowColumn734.rows_assocBCA HexagonRowColumn734.cols_left0)) ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4)) = (negativeScale (leftScaleExponent 7 3 4) • (left1Middle7 3 4)) ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal7_case_3_4_row_0_0_3 : (((-1 : ℤ) ^ (leftScaleBit 7 3 4).val * positiveScale (leftScaleExponent 7 3 4)) •
      (rowColumnMul HexagonRowColumn734.rows_assocBCA HexagonRowColumn734.cols_left0)) ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4)) = (negativeScale (leftScaleExponent 7 3 4) • (left1Middle7 3 4)) ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal7_case_3_4_row_0_1_0 : (((-1 : ℤ) ^ (leftScaleBit 7 3 4).val * positiveScale (leftScaleExponent 7 3 4)) •
      (rowColumnMul HexagonRowColumn734.rows_assocBCA HexagonRowColumn734.cols_left0)) ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4)) = (negativeScale (leftScaleExponent 7 3 4) • (left1Middle7 3 4)) ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal7_case_3_4_row_0_1_1 : (((-1 : ℤ) ^ (leftScaleBit 7 3 4).val * positiveScale (leftScaleExponent 7 3 4)) •
      (rowColumnMul HexagonRowColumn734.rows_assocBCA HexagonRowColumn734.cols_left0)) ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4)) = (negativeScale (leftScaleExponent 7 3 4) • (left1Middle7 3 4)) ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal7_case_3_4_row_0_1_2 : (((-1 : ℤ) ^ (leftScaleBit 7 3 4).val * positiveScale (leftScaleExponent 7 3 4)) •
      (rowColumnMul HexagonRowColumn734.rows_assocBCA HexagonRowColumn734.cols_left0)) ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4)) = (negativeScale (leftScaleExponent 7 3 4) • (left1Middle7 3 4)) ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal7_case_3_4_row_0_1_3 : (((-1 : ℤ) ^ (leftScaleBit 7 3 4).val * positiveScale (leftScaleExponent 7 3 4)) •
      (rowColumnMul HexagonRowColumn734.rows_assocBCA HexagonRowColumn734.cols_left0)) ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4)) = (negativeScale (leftScaleExponent 7 3 4) • (left1Middle7 3 4)) ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal7_case_3_4_row_0_2_0 : (((-1 : ℤ) ^ (leftScaleBit 7 3 4).val * positiveScale (leftScaleExponent 7 3 4)) •
      (rowColumnMul HexagonRowColumn734.rows_assocBCA HexagonRowColumn734.cols_left0)) ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4)) = (negativeScale (leftScaleExponent 7 3 4) • (left1Middle7 3 4)) ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal7_case_3_4_row_0_2_1 : (((-1 : ℤ) ^ (leftScaleBit 7 3 4).val * positiveScale (leftScaleExponent 7 3 4)) •
      (rowColumnMul HexagonRowColumn734.rows_assocBCA HexagonRowColumn734.cols_left0)) ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4)) = (negativeScale (leftScaleExponent 7 3 4) • (left1Middle7 3 4)) ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal7_case_3_4_row_0_2_2 : (((-1 : ℤ) ^ (leftScaleBit 7 3 4).val * positiveScale (leftScaleExponent 7 3 4)) •
      (rowColumnMul HexagonRowColumn734.rows_assocBCA HexagonRowColumn734.cols_left0)) ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4)) = (negativeScale (leftScaleExponent 7 3 4) • (left1Middle7 3 4)) ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal7_case_3_4_row_0_2_3 : (((-1 : ℤ) ^ (leftScaleBit 7 3 4).val * positiveScale (leftScaleExponent 7 3 4)) •
      (rowColumnMul HexagonRowColumn734.rows_assocBCA HexagonRowColumn734.cols_left0)) ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4)) = (negativeScale (leftScaleExponent 7 3 4) • (left1Middle7 3 4)) ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal7_case_3_4_row_0_3_0 : (((-1 : ℤ) ^ (leftScaleBit 7 3 4).val * positiveScale (leftScaleExponent 7 3 4)) •
      (rowColumnMul HexagonRowColumn734.rows_assocBCA HexagonRowColumn734.cols_left0)) ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4)) = (negativeScale (leftScaleExponent 7 3 4) • (left1Middle7 3 4)) ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal7_case_3_4_row_0_3_1 : (((-1 : ℤ) ^ (leftScaleBit 7 3 4).val * positiveScale (leftScaleExponent 7 3 4)) •
      (rowColumnMul HexagonRowColumn734.rows_assocBCA HexagonRowColumn734.cols_left0)) ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4)) = (negativeScale (leftScaleExponent 7 3 4) • (left1Middle7 3 4)) ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal7_case_3_4_row_0_3_2 : (((-1 : ℤ) ^ (leftScaleBit 7 3 4).val * positiveScale (leftScaleExponent 7 3 4)) •
      (rowColumnMul HexagonRowColumn734.rows_assocBCA HexagonRowColumn734.cols_left0)) ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4)) = (negativeScale (leftScaleExponent 7 3 4) • (left1Middle7 3 4)) ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal7_case_3_4_row_0_3_3 : (((-1 : ℤ) ^ (leftScaleBit 7 3 4).val * positiveScale (leftScaleExponent 7 3 4)) •
      (rowColumnMul HexagonRowColumn734.rows_assocBCA HexagonRowColumn734.cols_left0)) ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4)) = (negativeScale (leftScaleExponent 7 3 4) • (left1Middle7 3 4)) ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal7_case_3_4_checked : ((-1 : ℤ) ^ (leftScaleBit 7 3 4).val * positiveScale (leftScaleExponent 7 3 4)) •
      (rowColumnMul HexagonRowColumn734.rows_assocBCA HexagonRowColumn734.cols_left0) = negativeScale (leftScaleExponent 7 3 4) • (left1Middle7 3 4) := by
  funext r
  fin_cases r
  · exact leftFinal7_case_3_4_row_0_0_0
  · exact leftFinal7_case_3_4_row_0_0_1
  · exact leftFinal7_case_3_4_row_0_0_2
  · exact leftFinal7_case_3_4_row_0_0_3
  · exact leftFinal7_case_3_4_row_0_1_0
  · exact leftFinal7_case_3_4_row_0_1_1
  · exact leftFinal7_case_3_4_row_0_1_2
  · exact leftFinal7_case_3_4_row_0_1_3
  · exact leftFinal7_case_3_4_row_0_2_0
  · exact leftFinal7_case_3_4_row_0_2_1
  · exact leftFinal7_case_3_4_row_0_2_2
  · exact leftFinal7_case_3_4_row_0_2_3
  · exact leftFinal7_case_3_4_row_0_3_0
  · exact leftFinal7_case_3_4_row_0_3_1
  · exact leftFinal7_case_3_4_row_0_3_2
  · exact leftFinal7_case_3_4_row_0_3_3

set_option backward.isDefEq.respectTransparency false in
theorem leftFinal7_case_3_4 : ((-1 : ℤ) ^ (leftScaleBit 7 3 4).val * positiveScale (leftScaleExponent 7 3 4)) •
      (associatorZ 3 4 7 * left0Middle7 3 4) = negativeScale (leftScaleExponent 7 3 4) • (innerRightZ 3 7 4 * left1Middle7 3 4) := by
  simpa only [HexagonAtoms734.assocABC_eq,
    HexagonAtoms734.outerABC_eq,
    HexagonAtoms734.assocBAC_eq,
    HexagonAtoms734.innerABC_eq,
    HexagonAtoms734.innerRightABC_eq,
    HexagonAtoms734.inverseACB_eq,
    HexagonAtoms734.innerACB_eq,
    HexagonAtoms734.assocBCA_eq,
    HexagonAtoms734.innerRightBAC_eq,
    HexagonAtoms734.assocCAB_eq,
    HexagonAtoms734.outerLeftABC_eq,
    HexagonRowColumn734.product0_eq,
    HexagonRowColumn734.product1_eq,
    HexagonRowColumn734.product2_eq,
    HexagonRowColumn734.product3_eq,
    HexagonRowColumn734.product4_eq,
    HexagonRowColumn734.product5_eq,
    HexagonRowColumn734.product6_eq,
    HexagonRowColumn734.product7_eq] using leftFinal7_case_3_4_checked

private theorem rightFinal7_case_3_4_row_0_0_0 : (((-1 : ℤ) ^ (rightScaleBit 7 3 4).val * positiveScale (rightScaleExponent 7 3 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 4 3 : ℤ)) • HexagonAtoms734.outerLeftABC) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 7 3 4) • (rowColumnMul HexagonRowColumn734.rows_assocCAB HexagonRowColumn734.cols_right2)) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal7_case_3_4_row_0_0_1 : (((-1 : ℤ) ^ (rightScaleBit 7 3 4).val * positiveScale (rightScaleExponent 7 3 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 4 3 : ℤ)) • HexagonAtoms734.outerLeftABC) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 7 3 4) • (rowColumnMul HexagonRowColumn734.rows_assocCAB HexagonRowColumn734.cols_right2)) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal7_case_3_4_row_0_0_2 : (((-1 : ℤ) ^ (rightScaleBit 7 3 4).val * positiveScale (rightScaleExponent 7 3 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 4 3 : ℤ)) • HexagonAtoms734.outerLeftABC) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 7 3 4) • (rowColumnMul HexagonRowColumn734.rows_assocCAB HexagonRowColumn734.cols_right2)) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal7_case_3_4_row_0_0_3 : (((-1 : ℤ) ^ (rightScaleBit 7 3 4).val * positiveScale (rightScaleExponent 7 3 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 4 3 : ℤ)) • HexagonAtoms734.outerLeftABC) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 7 3 4) • (rowColumnMul HexagonRowColumn734.rows_assocCAB HexagonRowColumn734.cols_right2)) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal7_case_3_4_row_0_1_0 : (((-1 : ℤ) ^ (rightScaleBit 7 3 4).val * positiveScale (rightScaleExponent 7 3 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 4 3 : ℤ)) • HexagonAtoms734.outerLeftABC) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 7 3 4) • (rowColumnMul HexagonRowColumn734.rows_assocCAB HexagonRowColumn734.cols_right2)) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal7_case_3_4_row_0_1_1 : (((-1 : ℤ) ^ (rightScaleBit 7 3 4).val * positiveScale (rightScaleExponent 7 3 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 4 3 : ℤ)) • HexagonAtoms734.outerLeftABC) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 7 3 4) • (rowColumnMul HexagonRowColumn734.rows_assocCAB HexagonRowColumn734.cols_right2)) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal7_case_3_4_row_0_1_2 : (((-1 : ℤ) ^ (rightScaleBit 7 3 4).val * positiveScale (rightScaleExponent 7 3 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 4 3 : ℤ)) • HexagonAtoms734.outerLeftABC) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 7 3 4) • (rowColumnMul HexagonRowColumn734.rows_assocCAB HexagonRowColumn734.cols_right2)) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal7_case_3_4_row_0_1_3 : (((-1 : ℤ) ^ (rightScaleBit 7 3 4).val * positiveScale (rightScaleExponent 7 3 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 4 3 : ℤ)) • HexagonAtoms734.outerLeftABC) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 7 3 4) • (rowColumnMul HexagonRowColumn734.rows_assocCAB HexagonRowColumn734.cols_right2)) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal7_case_3_4_row_1_0_0 : (((-1 : ℤ) ^ (rightScaleBit 7 3 4).val * positiveScale (rightScaleExponent 7 3 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 4 3 : ℤ)) • HexagonAtoms734.outerLeftABC) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 7 3 4) • (rowColumnMul HexagonRowColumn734.rows_assocCAB HexagonRowColumn734.cols_right2)) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal7_case_3_4_row_1_0_1 : (((-1 : ℤ) ^ (rightScaleBit 7 3 4).val * positiveScale (rightScaleExponent 7 3 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 4 3 : ℤ)) • HexagonAtoms734.outerLeftABC) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 7 3 4) • (rowColumnMul HexagonRowColumn734.rows_assocCAB HexagonRowColumn734.cols_right2)) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal7_case_3_4_row_1_0_2 : (((-1 : ℤ) ^ (rightScaleBit 7 3 4).val * positiveScale (rightScaleExponent 7 3 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 4 3 : ℤ)) • HexagonAtoms734.outerLeftABC) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 7 3 4) • (rowColumnMul HexagonRowColumn734.rows_assocCAB HexagonRowColumn734.cols_right2)) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal7_case_3_4_row_1_0_3 : (((-1 : ℤ) ^ (rightScaleBit 7 3 4).val * positiveScale (rightScaleExponent 7 3 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 4 3 : ℤ)) • HexagonAtoms734.outerLeftABC) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 7 3 4) • (rowColumnMul HexagonRowColumn734.rows_assocCAB HexagonRowColumn734.cols_right2)) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal7_case_3_4_row_1_1_0 : (((-1 : ℤ) ^ (rightScaleBit 7 3 4).val * positiveScale (rightScaleExponent 7 3 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 4 3 : ℤ)) • HexagonAtoms734.outerLeftABC) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 7 3 4) • (rowColumnMul HexagonRowColumn734.rows_assocCAB HexagonRowColumn734.cols_right2)) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal7_case_3_4_row_1_1_1 : (((-1 : ℤ) ^ (rightScaleBit 7 3 4).val * positiveScale (rightScaleExponent 7 3 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 4 3 : ℤ)) • HexagonAtoms734.outerLeftABC) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 7 3 4) • (rowColumnMul HexagonRowColumn734.rows_assocCAB HexagonRowColumn734.cols_right2)) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal7_case_3_4_row_1_1_2 : (((-1 : ℤ) ^ (rightScaleBit 7 3 4).val * positiveScale (rightScaleExponent 7 3 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 4 3 : ℤ)) • HexagonAtoms734.outerLeftABC) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 7 3 4) • (rowColumnMul HexagonRowColumn734.rows_assocCAB HexagonRowColumn734.cols_right2)) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal7_case_3_4_row_1_1_3 : (((-1 : ℤ) ^ (rightScaleBit 7 3 4).val * positiveScale (rightScaleExponent 7 3 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 4 3 : ℤ)) • HexagonAtoms734.outerLeftABC) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 7 3 4) • (rowColumnMul HexagonRowColumn734.rows_assocCAB HexagonRowColumn734.cols_right2)) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal7_case_3_4_checked : ((-1 : ℤ) ^ (rightScaleBit 7 3 4).val * positiveScale (rightScaleExponent 7 3 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 4 3 : ℤ)) • HexagonAtoms734.outerLeftABC = negativeScale (rightScaleExponent 7 3 4) • (rowColumnMul HexagonRowColumn734.rows_assocCAB HexagonRowColumn734.cols_right2) := by
  funext r
  fin_cases r
  · exact rightFinal7_case_3_4_row_0_0_0
  · exact rightFinal7_case_3_4_row_0_0_1
  · exact rightFinal7_case_3_4_row_0_0_2
  · exact rightFinal7_case_3_4_row_0_0_3
  · exact rightFinal7_case_3_4_row_0_1_0
  · exact rightFinal7_case_3_4_row_0_1_1
  · exact rightFinal7_case_3_4_row_0_1_2
  · exact rightFinal7_case_3_4_row_0_1_3
  · exact rightFinal7_case_3_4_row_1_0_0
  · exact rightFinal7_case_3_4_row_1_0_1
  · exact rightFinal7_case_3_4_row_1_0_2
  · exact rightFinal7_case_3_4_row_1_0_3
  · exact rightFinal7_case_3_4_row_1_1_0
  · exact rightFinal7_case_3_4_row_1_1_1
  · exact rightFinal7_case_3_4_row_1_1_2
  · exact rightFinal7_case_3_4_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem rightFinal7_case_3_4 : ((-1 : ℤ) ^ (rightScaleBit 7 3 4).val * positiveScale (rightScaleExponent 7 3 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 4 3 : ℤ)) • outerLeftZ 7 3 4 = negativeScale (rightScaleExponent 7 3 4) • (associatorZ 4 7 3 * right2Middle7 3 4) := by
  simpa only [HexagonAtoms734.assocABC_eq,
    HexagonAtoms734.outerABC_eq,
    HexagonAtoms734.assocBAC_eq,
    HexagonAtoms734.innerABC_eq,
    HexagonAtoms734.innerRightABC_eq,
    HexagonAtoms734.inverseACB_eq,
    HexagonAtoms734.innerACB_eq,
    HexagonAtoms734.assocBCA_eq,
    HexagonAtoms734.innerRightBAC_eq,
    HexagonAtoms734.assocCAB_eq,
    HexagonAtoms734.outerLeftABC_eq,
    HexagonRowColumn734.product0_eq,
    HexagonRowColumn734.product1_eq,
    HexagonRowColumn734.product2_eq,
    HexagonRowColumn734.product3_eq,
    HexagonRowColumn734.product4_eq,
    HexagonRowColumn734.product5_eq,
    HexagonRowColumn734.product6_eq,
    HexagonRowColumn734.product7_eq] using rightFinal7_case_3_4_checked

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonCases7
