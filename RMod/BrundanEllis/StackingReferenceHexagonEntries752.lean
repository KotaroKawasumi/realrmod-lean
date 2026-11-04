import RMod.BrundanEllis.StackingReferenceHexagonMiddle7
import RMod.BrundanEllis.StackingReferenceSparseMatrixCheck
import RMod.BrundanEllis.StackingReferenceHexagonAtoms752
import RMod.BrundanEllis.StackingReferenceHexagonRowColumn752

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

private theorem left0Middle7_eq_case_5_2_row_0_0_0 : (left0Middle7 5 2) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn752.rows_outerABC HexagonRowColumn752.cols_assocABC) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle7_eq_case_5_2_row_0_0_1 : (left0Middle7 5 2) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn752.rows_outerABC HexagonRowColumn752.cols_assocABC) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle7_eq_case_5_2_row_0_0_2 : (left0Middle7 5 2) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn752.rows_outerABC HexagonRowColumn752.cols_assocABC) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle7_eq_case_5_2_row_0_0_3 : (left0Middle7 5 2) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn752.rows_outerABC HexagonRowColumn752.cols_assocABC) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle7_eq_case_5_2_row_1_0_0 : (left0Middle7 5 2) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn752.rows_outerABC HexagonRowColumn752.cols_assocABC) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle7_eq_case_5_2_row_1_0_1 : (left0Middle7 5 2) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn752.rows_outerABC HexagonRowColumn752.cols_assocABC) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle7_eq_case_5_2_row_1_0_2 : (left0Middle7 5 2) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn752.rows_outerABC HexagonRowColumn752.cols_assocABC) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle7_eq_case_5_2_row_1_0_3 : (left0Middle7 5 2) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn752.rows_outerABC HexagonRowColumn752.cols_assocABC) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle7_eq_case_5_2_row_2_0_0 : (left0Middle7 5 2) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn752.rows_outerABC HexagonRowColumn752.cols_assocABC) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle7_eq_case_5_2_row_2_0_1 : (left0Middle7 5 2) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn752.rows_outerABC HexagonRowColumn752.cols_assocABC) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle7_eq_case_5_2_row_2_0_2 : (left0Middle7 5 2) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn752.rows_outerABC HexagonRowColumn752.cols_assocABC) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle7_eq_case_5_2_row_2_0_3 : (left0Middle7 5 2) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn752.rows_outerABC HexagonRowColumn752.cols_assocABC) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle7_eq_case_5_2_row_3_0_0 : (left0Middle7 5 2) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn752.rows_outerABC HexagonRowColumn752.cols_assocABC) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle7_eq_case_5_2_row_3_0_1 : (left0Middle7 5 2) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn752.rows_outerABC HexagonRowColumn752.cols_assocABC) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle7_eq_case_5_2_row_3_0_2 : (left0Middle7 5 2) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn752.rows_outerABC HexagonRowColumn752.cols_assocABC) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle7_eq_case_5_2_row_3_0_3 : (left0Middle7 5 2) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn752.rows_outerABC HexagonRowColumn752.cols_assocABC) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle7_eq_case_5_2_checked : left0Middle7 5 2 = rowColumnMul HexagonRowColumn752.rows_outerABC HexagonRowColumn752.cols_assocABC := by
  funext r
  fin_cases r
  · exact left0Middle7_eq_case_5_2_row_0_0_0
  · exact left0Middle7_eq_case_5_2_row_0_0_1
  · exact left0Middle7_eq_case_5_2_row_0_0_2
  · exact left0Middle7_eq_case_5_2_row_0_0_3
  · exact left0Middle7_eq_case_5_2_row_1_0_0
  · exact left0Middle7_eq_case_5_2_row_1_0_1
  · exact left0Middle7_eq_case_5_2_row_1_0_2
  · exact left0Middle7_eq_case_5_2_row_1_0_3
  · exact left0Middle7_eq_case_5_2_row_2_0_0
  · exact left0Middle7_eq_case_5_2_row_2_0_1
  · exact left0Middle7_eq_case_5_2_row_2_0_2
  · exact left0Middle7_eq_case_5_2_row_2_0_3
  · exact left0Middle7_eq_case_5_2_row_3_0_0
  · exact left0Middle7_eq_case_5_2_row_3_0_1
  · exact left0Middle7_eq_case_5_2_row_3_0_2
  · exact left0Middle7_eq_case_5_2_row_3_0_3

set_option backward.isDefEq.respectTransparency false in
theorem left0Middle7_eq_case_5_2 : left0Middle7 5 2 = outerRightZ 7 5 2 * associatorZ 7 5 2 := by
  simpa only [HexagonAtoms752.assocABC_eq,
    HexagonAtoms752.outerABC_eq,
    HexagonAtoms752.assocBAC_eq,
    HexagonAtoms752.innerABC_eq,
    HexagonAtoms752.innerRightABC_eq,
    HexagonAtoms752.inverseACB_eq,
    HexagonAtoms752.innerACB_eq,
    HexagonAtoms752.assocBCA_eq,
    HexagonAtoms752.innerRightBAC_eq,
    HexagonAtoms752.assocCAB_eq,
    HexagonAtoms752.outerLeftABC_eq,
    HexagonRowColumn752.product0_eq,
    HexagonRowColumn752.product1_eq,
    HexagonRowColumn752.product2_eq,
    HexagonRowColumn752.product3_eq,
    HexagonRowColumn752.product4_eq,
    HexagonRowColumn752.product5_eq,
    HexagonRowColumn752.product6_eq,
    HexagonRowColumn752.product7_eq] using left0Middle7_eq_case_5_2_checked

private theorem left1Middle7_eq_case_5_2_row_0_0_0 : (left1Middle7 5 2) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms752.assocBAC) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle7_eq_case_5_2_row_0_0_1 : (left1Middle7 5 2) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms752.assocBAC) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle7_eq_case_5_2_row_0_0_2 : (left1Middle7 5 2) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms752.assocBAC) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle7_eq_case_5_2_row_0_0_3 : (left1Middle7 5 2) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms752.assocBAC) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle7_eq_case_5_2_row_0_1_0 : (left1Middle7 5 2) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms752.assocBAC) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle7_eq_case_5_2_row_0_1_1 : (left1Middle7 5 2) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms752.assocBAC) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle7_eq_case_5_2_row_0_1_2 : (left1Middle7 5 2) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms752.assocBAC) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle7_eq_case_5_2_row_0_1_3 : (left1Middle7 5 2) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms752.assocBAC) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle7_eq_case_5_2_row_1_0_0 : (left1Middle7 5 2) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms752.assocBAC) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle7_eq_case_5_2_row_1_0_1 : (left1Middle7 5 2) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms752.assocBAC) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle7_eq_case_5_2_row_1_0_2 : (left1Middle7 5 2) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms752.assocBAC) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle7_eq_case_5_2_row_1_0_3 : (left1Middle7 5 2) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms752.assocBAC) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle7_eq_case_5_2_row_1_1_0 : (left1Middle7 5 2) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms752.assocBAC) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle7_eq_case_5_2_row_1_1_1 : (left1Middle7 5 2) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms752.assocBAC) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle7_eq_case_5_2_row_1_1_2 : (left1Middle7 5 2) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms752.assocBAC) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle7_eq_case_5_2_row_1_1_3 : (left1Middle7 5 2) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms752.assocBAC) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle7_eq_case_5_2_checked : left1Middle7 5 2 = HexagonAtoms752.assocBAC := by
  funext r
  fin_cases r
  · exact left1Middle7_eq_case_5_2_row_0_0_0
  · exact left1Middle7_eq_case_5_2_row_0_0_1
  · exact left1Middle7_eq_case_5_2_row_0_0_2
  · exact left1Middle7_eq_case_5_2_row_0_0_3
  · exact left1Middle7_eq_case_5_2_row_0_1_0
  · exact left1Middle7_eq_case_5_2_row_0_1_1
  · exact left1Middle7_eq_case_5_2_row_0_1_2
  · exact left1Middle7_eq_case_5_2_row_0_1_3
  · exact left1Middle7_eq_case_5_2_row_1_0_0
  · exact left1Middle7_eq_case_5_2_row_1_0_1
  · exact left1Middle7_eq_case_5_2_row_1_0_2
  · exact left1Middle7_eq_case_5_2_row_1_0_3
  · exact left1Middle7_eq_case_5_2_row_1_1_0
  · exact left1Middle7_eq_case_5_2_row_1_1_1
  · exact left1Middle7_eq_case_5_2_row_1_1_2
  · exact left1Middle7_eq_case_5_2_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem left1Middle7_eq_case_5_2 : left1Middle7 5 2 = associatorZ 5 7 2 * innerLeftZ 7 5 2 := by
  simpa only [HexagonAtoms752.assocABC_eq,
    HexagonAtoms752.outerABC_eq,
    HexagonAtoms752.assocBAC_eq,
    HexagonAtoms752.innerABC_eq,
    HexagonAtoms752.innerRightABC_eq,
    HexagonAtoms752.inverseACB_eq,
    HexagonAtoms752.innerACB_eq,
    HexagonAtoms752.assocBCA_eq,
    HexagonAtoms752.innerRightBAC_eq,
    HexagonAtoms752.assocCAB_eq,
    HexagonAtoms752.outerLeftABC_eq,
    HexagonRowColumn752.product0_eq,
    HexagonRowColumn752.product1_eq,
    HexagonRowColumn752.product2_eq,
    HexagonRowColumn752.product3_eq,
    HexagonRowColumn752.product4_eq,
    HexagonRowColumn752.product5_eq,
    HexagonRowColumn752.product6_eq,
    HexagonRowColumn752.product7_eq] using left1Middle7_eq_case_5_2_checked

private theorem right0Middle7_eq_case_5_2_row_0_0_0 : (right0Middle7 5 2) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms752.assocABC) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle7_eq_case_5_2_row_0_0_1 : (right0Middle7 5 2) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms752.assocABC) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle7_eq_case_5_2_row_0_0_2 : (right0Middle7 5 2) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms752.assocABC) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle7_eq_case_5_2_row_0_0_3 : (right0Middle7 5 2) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms752.assocABC) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle7_eq_case_5_2_row_1_0_0 : (right0Middle7 5 2) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms752.assocABC) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle7_eq_case_5_2_row_1_0_1 : (right0Middle7 5 2) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms752.assocABC) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle7_eq_case_5_2_row_1_0_2 : (right0Middle7 5 2) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms752.assocABC) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle7_eq_case_5_2_row_1_0_3 : (right0Middle7 5 2) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms752.assocABC) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle7_eq_case_5_2_row_2_0_0 : (right0Middle7 5 2) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms752.assocABC) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle7_eq_case_5_2_row_2_0_1 : (right0Middle7 5 2) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms752.assocABC) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle7_eq_case_5_2_row_2_0_2 : (right0Middle7 5 2) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms752.assocABC) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle7_eq_case_5_2_row_2_0_3 : (right0Middle7 5 2) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms752.assocABC) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle7_eq_case_5_2_row_3_0_0 : (right0Middle7 5 2) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms752.assocABC) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle7_eq_case_5_2_row_3_0_1 : (right0Middle7 5 2) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms752.assocABC) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle7_eq_case_5_2_row_3_0_2 : (right0Middle7 5 2) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms752.assocABC) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle7_eq_case_5_2_row_3_0_3 : (right0Middle7 5 2) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms752.assocABC) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle7_eq_case_5_2_checked : right0Middle7 5 2 = HexagonAtoms752.assocABC := by
  funext r
  fin_cases r
  · exact right0Middle7_eq_case_5_2_row_0_0_0
  · exact right0Middle7_eq_case_5_2_row_0_0_1
  · exact right0Middle7_eq_case_5_2_row_0_0_2
  · exact right0Middle7_eq_case_5_2_row_0_0_3
  · exact right0Middle7_eq_case_5_2_row_1_0_0
  · exact right0Middle7_eq_case_5_2_row_1_0_1
  · exact right0Middle7_eq_case_5_2_row_1_0_2
  · exact right0Middle7_eq_case_5_2_row_1_0_3
  · exact right0Middle7_eq_case_5_2_row_2_0_0
  · exact right0Middle7_eq_case_5_2_row_2_0_1
  · exact right0Middle7_eq_case_5_2_row_2_0_2
  · exact right0Middle7_eq_case_5_2_row_2_0_3
  · exact right0Middle7_eq_case_5_2_row_3_0_0
  · exact right0Middle7_eq_case_5_2_row_3_0_1
  · exact right0Middle7_eq_case_5_2_row_3_0_2
  · exact right0Middle7_eq_case_5_2_row_3_0_3

set_option backward.isDefEq.respectTransparency false in
theorem right0Middle7_eq_case_5_2 : right0Middle7 5 2 = innerRightZ 7 5 2 * associatorZ 7 5 2 := by
  simpa only [HexagonAtoms752.assocABC_eq,
    HexagonAtoms752.outerABC_eq,
    HexagonAtoms752.assocBAC_eq,
    HexagonAtoms752.innerABC_eq,
    HexagonAtoms752.innerRightABC_eq,
    HexagonAtoms752.inverseACB_eq,
    HexagonAtoms752.innerACB_eq,
    HexagonAtoms752.assocBCA_eq,
    HexagonAtoms752.innerRightBAC_eq,
    HexagonAtoms752.assocCAB_eq,
    HexagonAtoms752.outerLeftABC_eq,
    HexagonRowColumn752.product0_eq,
    HexagonRowColumn752.product1_eq,
    HexagonRowColumn752.product2_eq,
    HexagonRowColumn752.product3_eq,
    HexagonRowColumn752.product4_eq,
    HexagonRowColumn752.product5_eq,
    HexagonRowColumn752.product6_eq,
    HexagonRowColumn752.product7_eq] using right0Middle7_eq_case_5_2_checked

private theorem right1Middle7_eq_case_5_2_row_0_0_0 : (right1Middle7 5 2) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn752.rows_inverseACB HexagonRowColumn752.cols_right0) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle7_eq_case_5_2_row_0_0_1 : (right1Middle7 5 2) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn752.rows_inverseACB HexagonRowColumn752.cols_right0) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle7_eq_case_5_2_row_0_0_2 : (right1Middle7 5 2) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn752.rows_inverseACB HexagonRowColumn752.cols_right0) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle7_eq_case_5_2_row_0_0_3 : (right1Middle7 5 2) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn752.rows_inverseACB HexagonRowColumn752.cols_right0) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle7_eq_case_5_2_row_0_1_0 : (right1Middle7 5 2) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn752.rows_inverseACB HexagonRowColumn752.cols_right0) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle7_eq_case_5_2_row_0_1_1 : (right1Middle7 5 2) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn752.rows_inverseACB HexagonRowColumn752.cols_right0) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle7_eq_case_5_2_row_0_1_2 : (right1Middle7 5 2) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn752.rows_inverseACB HexagonRowColumn752.cols_right0) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle7_eq_case_5_2_row_0_1_3 : (right1Middle7 5 2) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn752.rows_inverseACB HexagonRowColumn752.cols_right0) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle7_eq_case_5_2_row_1_0_0 : (right1Middle7 5 2) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn752.rows_inverseACB HexagonRowColumn752.cols_right0) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle7_eq_case_5_2_row_1_0_1 : (right1Middle7 5 2) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn752.rows_inverseACB HexagonRowColumn752.cols_right0) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle7_eq_case_5_2_row_1_0_2 : (right1Middle7 5 2) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn752.rows_inverseACB HexagonRowColumn752.cols_right0) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle7_eq_case_5_2_row_1_0_3 : (right1Middle7 5 2) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn752.rows_inverseACB HexagonRowColumn752.cols_right0) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle7_eq_case_5_2_row_1_1_0 : (right1Middle7 5 2) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn752.rows_inverseACB HexagonRowColumn752.cols_right0) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle7_eq_case_5_2_row_1_1_1 : (right1Middle7 5 2) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn752.rows_inverseACB HexagonRowColumn752.cols_right0) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle7_eq_case_5_2_row_1_1_2 : (right1Middle7 5 2) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn752.rows_inverseACB HexagonRowColumn752.cols_right0) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle7_eq_case_5_2_row_1_1_3 : (right1Middle7 5 2) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn752.rows_inverseACB HexagonRowColumn752.cols_right0) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle7_eq_case_5_2_checked : right1Middle7 5 2 = rowColumnMul HexagonRowColumn752.rows_inverseACB HexagonRowColumn752.cols_right0 := by
  funext r
  fin_cases r
  · exact right1Middle7_eq_case_5_2_row_0_0_0
  · exact right1Middle7_eq_case_5_2_row_0_0_1
  · exact right1Middle7_eq_case_5_2_row_0_0_2
  · exact right1Middle7_eq_case_5_2_row_0_0_3
  · exact right1Middle7_eq_case_5_2_row_0_1_0
  · exact right1Middle7_eq_case_5_2_row_0_1_1
  · exact right1Middle7_eq_case_5_2_row_0_1_2
  · exact right1Middle7_eq_case_5_2_row_0_1_3
  · exact right1Middle7_eq_case_5_2_row_1_0_0
  · exact right1Middle7_eq_case_5_2_row_1_0_1
  · exact right1Middle7_eq_case_5_2_row_1_0_2
  · exact right1Middle7_eq_case_5_2_row_1_0_3
  · exact right1Middle7_eq_case_5_2_row_1_1_0
  · exact right1Middle7_eq_case_5_2_row_1_1_1
  · exact right1Middle7_eq_case_5_2_row_1_1_2
  · exact right1Middle7_eq_case_5_2_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem right1Middle7_eq_case_5_2 : right1Middle7 5 2 = associatorInverseZ 7 2 5 * right0Middle7 5 2 := by
  simpa only [HexagonAtoms752.assocABC_eq,
    HexagonAtoms752.outerABC_eq,
    HexagonAtoms752.assocBAC_eq,
    HexagonAtoms752.innerABC_eq,
    HexagonAtoms752.innerRightABC_eq,
    HexagonAtoms752.inverseACB_eq,
    HexagonAtoms752.innerACB_eq,
    HexagonAtoms752.assocBCA_eq,
    HexagonAtoms752.innerRightBAC_eq,
    HexagonAtoms752.assocCAB_eq,
    HexagonAtoms752.outerLeftABC_eq,
    HexagonRowColumn752.product0_eq,
    HexagonRowColumn752.product1_eq,
    HexagonRowColumn752.product2_eq,
    HexagonRowColumn752.product3_eq,
    HexagonRowColumn752.product4_eq,
    HexagonRowColumn752.product5_eq,
    HexagonRowColumn752.product6_eq,
    HexagonRowColumn752.product7_eq] using right1Middle7_eq_case_5_2_checked

private theorem right2Middle7_eq_case_5_2_row_0_0_0 : (right2Middle7 5 2) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (right1Middle7 5 2) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle7_eq_case_5_2_row_0_0_1 : (right2Middle7 5 2) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (right1Middle7 5 2) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle7_eq_case_5_2_row_0_0_2 : (right2Middle7 5 2) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (right1Middle7 5 2) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle7_eq_case_5_2_row_0_0_3 : (right2Middle7 5 2) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (right1Middle7 5 2) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle7_eq_case_5_2_row_0_1_0 : (right2Middle7 5 2) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (right1Middle7 5 2) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle7_eq_case_5_2_row_0_1_1 : (right2Middle7 5 2) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (right1Middle7 5 2) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle7_eq_case_5_2_row_0_1_2 : (right2Middle7 5 2) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (right1Middle7 5 2) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle7_eq_case_5_2_row_0_1_3 : (right2Middle7 5 2) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (right1Middle7 5 2) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle7_eq_case_5_2_row_1_0_0 : (right2Middle7 5 2) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (right1Middle7 5 2) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle7_eq_case_5_2_row_1_0_1 : (right2Middle7 5 2) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (right1Middle7 5 2) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle7_eq_case_5_2_row_1_0_2 : (right2Middle7 5 2) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (right1Middle7 5 2) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle7_eq_case_5_2_row_1_0_3 : (right2Middle7 5 2) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (right1Middle7 5 2) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle7_eq_case_5_2_row_1_1_0 : (right2Middle7 5 2) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (right1Middle7 5 2) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle7_eq_case_5_2_row_1_1_1 : (right2Middle7 5 2) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (right1Middle7 5 2) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle7_eq_case_5_2_row_1_1_2 : (right2Middle7 5 2) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (right1Middle7 5 2) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle7_eq_case_5_2_row_1_1_3 : (right2Middle7 5 2) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (right1Middle7 5 2) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle7_eq_case_5_2_checked : right2Middle7 5 2 = right1Middle7 5 2 := by
  funext r
  fin_cases r
  · exact right2Middle7_eq_case_5_2_row_0_0_0
  · exact right2Middle7_eq_case_5_2_row_0_0_1
  · exact right2Middle7_eq_case_5_2_row_0_0_2
  · exact right2Middle7_eq_case_5_2_row_0_0_3
  · exact right2Middle7_eq_case_5_2_row_0_1_0
  · exact right2Middle7_eq_case_5_2_row_0_1_1
  · exact right2Middle7_eq_case_5_2_row_0_1_2
  · exact right2Middle7_eq_case_5_2_row_0_1_3
  · exact right2Middle7_eq_case_5_2_row_1_0_0
  · exact right2Middle7_eq_case_5_2_row_1_0_1
  · exact right2Middle7_eq_case_5_2_row_1_0_2
  · exact right2Middle7_eq_case_5_2_row_1_0_3
  · exact right2Middle7_eq_case_5_2_row_1_1_0
  · exact right2Middle7_eq_case_5_2_row_1_1_1
  · exact right2Middle7_eq_case_5_2_row_1_1_2
  · exact right2Middle7_eq_case_5_2_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem right2Middle7_eq_case_5_2 : right2Middle7 5 2 = innerLeftZ 7 2 5 * right1Middle7 5 2 := by
  simpa only [HexagonAtoms752.assocABC_eq,
    HexagonAtoms752.outerABC_eq,
    HexagonAtoms752.assocBAC_eq,
    HexagonAtoms752.innerABC_eq,
    HexagonAtoms752.innerRightABC_eq,
    HexagonAtoms752.inverseACB_eq,
    HexagonAtoms752.innerACB_eq,
    HexagonAtoms752.assocBCA_eq,
    HexagonAtoms752.innerRightBAC_eq,
    HexagonAtoms752.assocCAB_eq,
    HexagonAtoms752.outerLeftABC_eq,
    HexagonRowColumn752.product0_eq,
    HexagonRowColumn752.product1_eq,
    HexagonRowColumn752.product2_eq,
    HexagonRowColumn752.product3_eq,
    HexagonRowColumn752.product4_eq,
    HexagonRowColumn752.product5_eq,
    HexagonRowColumn752.product6_eq,
    HexagonRowColumn752.product7_eq] using right2Middle7_eq_case_5_2_checked

private theorem leftFinal7_case_5_2_row_0_0_0 : (((-1 : ℤ) ^ (leftScaleBit 7 5 2).val * positiveScale (leftScaleExponent 7 5 2)) •
      (rowColumnMul HexagonRowColumn752.rows_assocBCA HexagonRowColumn752.cols_left0)) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 7 5 2) • (left1Middle7 5 2)) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal7_case_5_2_row_0_0_1 : (((-1 : ℤ) ^ (leftScaleBit 7 5 2).val * positiveScale (leftScaleExponent 7 5 2)) •
      (rowColumnMul HexagonRowColumn752.rows_assocBCA HexagonRowColumn752.cols_left0)) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 7 5 2) • (left1Middle7 5 2)) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal7_case_5_2_row_0_0_2 : (((-1 : ℤ) ^ (leftScaleBit 7 5 2).val * positiveScale (leftScaleExponent 7 5 2)) •
      (rowColumnMul HexagonRowColumn752.rows_assocBCA HexagonRowColumn752.cols_left0)) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 7 5 2) • (left1Middle7 5 2)) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal7_case_5_2_row_0_0_3 : (((-1 : ℤ) ^ (leftScaleBit 7 5 2).val * positiveScale (leftScaleExponent 7 5 2)) •
      (rowColumnMul HexagonRowColumn752.rows_assocBCA HexagonRowColumn752.cols_left0)) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 7 5 2) • (left1Middle7 5 2)) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal7_case_5_2_row_0_1_0 : (((-1 : ℤ) ^ (leftScaleBit 7 5 2).val * positiveScale (leftScaleExponent 7 5 2)) •
      (rowColumnMul HexagonRowColumn752.rows_assocBCA HexagonRowColumn752.cols_left0)) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 7 5 2) • (left1Middle7 5 2)) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal7_case_5_2_row_0_1_1 : (((-1 : ℤ) ^ (leftScaleBit 7 5 2).val * positiveScale (leftScaleExponent 7 5 2)) •
      (rowColumnMul HexagonRowColumn752.rows_assocBCA HexagonRowColumn752.cols_left0)) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 7 5 2) • (left1Middle7 5 2)) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal7_case_5_2_row_0_1_2 : (((-1 : ℤ) ^ (leftScaleBit 7 5 2).val * positiveScale (leftScaleExponent 7 5 2)) •
      (rowColumnMul HexagonRowColumn752.rows_assocBCA HexagonRowColumn752.cols_left0)) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 7 5 2) • (left1Middle7 5 2)) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal7_case_5_2_row_0_1_3 : (((-1 : ℤ) ^ (leftScaleBit 7 5 2).val * positiveScale (leftScaleExponent 7 5 2)) •
      (rowColumnMul HexagonRowColumn752.rows_assocBCA HexagonRowColumn752.cols_left0)) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 7 5 2) • (left1Middle7 5 2)) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal7_case_5_2_row_1_0_0 : (((-1 : ℤ) ^ (leftScaleBit 7 5 2).val * positiveScale (leftScaleExponent 7 5 2)) •
      (rowColumnMul HexagonRowColumn752.rows_assocBCA HexagonRowColumn752.cols_left0)) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 7 5 2) • (left1Middle7 5 2)) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal7_case_5_2_row_1_0_1 : (((-1 : ℤ) ^ (leftScaleBit 7 5 2).val * positiveScale (leftScaleExponent 7 5 2)) •
      (rowColumnMul HexagonRowColumn752.rows_assocBCA HexagonRowColumn752.cols_left0)) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 7 5 2) • (left1Middle7 5 2)) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal7_case_5_2_row_1_0_2 : (((-1 : ℤ) ^ (leftScaleBit 7 5 2).val * positiveScale (leftScaleExponent 7 5 2)) •
      (rowColumnMul HexagonRowColumn752.rows_assocBCA HexagonRowColumn752.cols_left0)) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 7 5 2) • (left1Middle7 5 2)) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal7_case_5_2_row_1_0_3 : (((-1 : ℤ) ^ (leftScaleBit 7 5 2).val * positiveScale (leftScaleExponent 7 5 2)) •
      (rowColumnMul HexagonRowColumn752.rows_assocBCA HexagonRowColumn752.cols_left0)) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 7 5 2) • (left1Middle7 5 2)) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal7_case_5_2_row_1_1_0 : (((-1 : ℤ) ^ (leftScaleBit 7 5 2).val * positiveScale (leftScaleExponent 7 5 2)) •
      (rowColumnMul HexagonRowColumn752.rows_assocBCA HexagonRowColumn752.cols_left0)) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 7 5 2) • (left1Middle7 5 2)) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal7_case_5_2_row_1_1_1 : (((-1 : ℤ) ^ (leftScaleBit 7 5 2).val * positiveScale (leftScaleExponent 7 5 2)) •
      (rowColumnMul HexagonRowColumn752.rows_assocBCA HexagonRowColumn752.cols_left0)) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 7 5 2) • (left1Middle7 5 2)) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal7_case_5_2_row_1_1_2 : (((-1 : ℤ) ^ (leftScaleBit 7 5 2).val * positiveScale (leftScaleExponent 7 5 2)) •
      (rowColumnMul HexagonRowColumn752.rows_assocBCA HexagonRowColumn752.cols_left0)) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 7 5 2) • (left1Middle7 5 2)) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal7_case_5_2_row_1_1_3 : (((-1 : ℤ) ^ (leftScaleBit 7 5 2).val * positiveScale (leftScaleExponent 7 5 2)) •
      (rowColumnMul HexagonRowColumn752.rows_assocBCA HexagonRowColumn752.cols_left0)) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 7 5 2) • (left1Middle7 5 2)) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal7_case_5_2_checked : ((-1 : ℤ) ^ (leftScaleBit 7 5 2).val * positiveScale (leftScaleExponent 7 5 2)) •
      (rowColumnMul HexagonRowColumn752.rows_assocBCA HexagonRowColumn752.cols_left0) = negativeScale (leftScaleExponent 7 5 2) • (left1Middle7 5 2) := by
  funext r
  fin_cases r
  · exact leftFinal7_case_5_2_row_0_0_0
  · exact leftFinal7_case_5_2_row_0_0_1
  · exact leftFinal7_case_5_2_row_0_0_2
  · exact leftFinal7_case_5_2_row_0_0_3
  · exact leftFinal7_case_5_2_row_0_1_0
  · exact leftFinal7_case_5_2_row_0_1_1
  · exact leftFinal7_case_5_2_row_0_1_2
  · exact leftFinal7_case_5_2_row_0_1_3
  · exact leftFinal7_case_5_2_row_1_0_0
  · exact leftFinal7_case_5_2_row_1_0_1
  · exact leftFinal7_case_5_2_row_1_0_2
  · exact leftFinal7_case_5_2_row_1_0_3
  · exact leftFinal7_case_5_2_row_1_1_0
  · exact leftFinal7_case_5_2_row_1_1_1
  · exact leftFinal7_case_5_2_row_1_1_2
  · exact leftFinal7_case_5_2_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem leftFinal7_case_5_2 : ((-1 : ℤ) ^ (leftScaleBit 7 5 2).val * positiveScale (leftScaleExponent 7 5 2)) •
      (associatorZ 5 2 7 * left0Middle7 5 2) = negativeScale (leftScaleExponent 7 5 2) • (innerRightZ 5 7 2 * left1Middle7 5 2) := by
  simpa only [HexagonAtoms752.assocABC_eq,
    HexagonAtoms752.outerABC_eq,
    HexagonAtoms752.assocBAC_eq,
    HexagonAtoms752.innerABC_eq,
    HexagonAtoms752.innerRightABC_eq,
    HexagonAtoms752.inverseACB_eq,
    HexagonAtoms752.innerACB_eq,
    HexagonAtoms752.assocBCA_eq,
    HexagonAtoms752.innerRightBAC_eq,
    HexagonAtoms752.assocCAB_eq,
    HexagonAtoms752.outerLeftABC_eq,
    HexagonRowColumn752.product0_eq,
    HexagonRowColumn752.product1_eq,
    HexagonRowColumn752.product2_eq,
    HexagonRowColumn752.product3_eq,
    HexagonRowColumn752.product4_eq,
    HexagonRowColumn752.product5_eq,
    HexagonRowColumn752.product6_eq,
    HexagonRowColumn752.product7_eq] using leftFinal7_case_5_2_checked

private theorem rightFinal7_case_5_2_row_0_0_0 : (((-1 : ℤ) ^ (rightScaleBit 7 5 2).val * positiveScale (rightScaleExponent 7 5 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 2 5 : ℤ)) • HexagonAtoms752.outerLeftABC) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 7 5 2) • (rowColumnMul HexagonRowColumn752.rows_assocCAB HexagonRowColumn752.cols_right2)) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal7_case_5_2_row_0_0_1 : (((-1 : ℤ) ^ (rightScaleBit 7 5 2).val * positiveScale (rightScaleExponent 7 5 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 2 5 : ℤ)) • HexagonAtoms752.outerLeftABC) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 7 5 2) • (rowColumnMul HexagonRowColumn752.rows_assocCAB HexagonRowColumn752.cols_right2)) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal7_case_5_2_row_0_0_2 : (((-1 : ℤ) ^ (rightScaleBit 7 5 2).val * positiveScale (rightScaleExponent 7 5 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 2 5 : ℤ)) • HexagonAtoms752.outerLeftABC) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 7 5 2) • (rowColumnMul HexagonRowColumn752.rows_assocCAB HexagonRowColumn752.cols_right2)) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal7_case_5_2_row_0_0_3 : (((-1 : ℤ) ^ (rightScaleBit 7 5 2).val * positiveScale (rightScaleExponent 7 5 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 2 5 : ℤ)) • HexagonAtoms752.outerLeftABC) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 7 5 2) • (rowColumnMul HexagonRowColumn752.rows_assocCAB HexagonRowColumn752.cols_right2)) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal7_case_5_2_row_0_1_0 : (((-1 : ℤ) ^ (rightScaleBit 7 5 2).val * positiveScale (rightScaleExponent 7 5 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 2 5 : ℤ)) • HexagonAtoms752.outerLeftABC) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 7 5 2) • (rowColumnMul HexagonRowColumn752.rows_assocCAB HexagonRowColumn752.cols_right2)) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal7_case_5_2_row_0_1_1 : (((-1 : ℤ) ^ (rightScaleBit 7 5 2).val * positiveScale (rightScaleExponent 7 5 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 2 5 : ℤ)) • HexagonAtoms752.outerLeftABC) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 7 5 2) • (rowColumnMul HexagonRowColumn752.rows_assocCAB HexagonRowColumn752.cols_right2)) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal7_case_5_2_row_0_1_2 : (((-1 : ℤ) ^ (rightScaleBit 7 5 2).val * positiveScale (rightScaleExponent 7 5 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 2 5 : ℤ)) • HexagonAtoms752.outerLeftABC) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 7 5 2) • (rowColumnMul HexagonRowColumn752.rows_assocCAB HexagonRowColumn752.cols_right2)) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal7_case_5_2_row_0_1_3 : (((-1 : ℤ) ^ (rightScaleBit 7 5 2).val * positiveScale (rightScaleExponent 7 5 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 2 5 : ℤ)) • HexagonAtoms752.outerLeftABC) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 7 5 2) • (rowColumnMul HexagonRowColumn752.rows_assocCAB HexagonRowColumn752.cols_right2)) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal7_case_5_2_row_1_0_0 : (((-1 : ℤ) ^ (rightScaleBit 7 5 2).val * positiveScale (rightScaleExponent 7 5 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 2 5 : ℤ)) • HexagonAtoms752.outerLeftABC) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 7 5 2) • (rowColumnMul HexagonRowColumn752.rows_assocCAB HexagonRowColumn752.cols_right2)) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal7_case_5_2_row_1_0_1 : (((-1 : ℤ) ^ (rightScaleBit 7 5 2).val * positiveScale (rightScaleExponent 7 5 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 2 5 : ℤ)) • HexagonAtoms752.outerLeftABC) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 7 5 2) • (rowColumnMul HexagonRowColumn752.rows_assocCAB HexagonRowColumn752.cols_right2)) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal7_case_5_2_row_1_0_2 : (((-1 : ℤ) ^ (rightScaleBit 7 5 2).val * positiveScale (rightScaleExponent 7 5 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 2 5 : ℤ)) • HexagonAtoms752.outerLeftABC) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 7 5 2) • (rowColumnMul HexagonRowColumn752.rows_assocCAB HexagonRowColumn752.cols_right2)) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal7_case_5_2_row_1_0_3 : (((-1 : ℤ) ^ (rightScaleBit 7 5 2).val * positiveScale (rightScaleExponent 7 5 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 2 5 : ℤ)) • HexagonAtoms752.outerLeftABC) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 7 5 2) • (rowColumnMul HexagonRowColumn752.rows_assocCAB HexagonRowColumn752.cols_right2)) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal7_case_5_2_row_1_1_0 : (((-1 : ℤ) ^ (rightScaleBit 7 5 2).val * positiveScale (rightScaleExponent 7 5 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 2 5 : ℤ)) • HexagonAtoms752.outerLeftABC) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 7 5 2) • (rowColumnMul HexagonRowColumn752.rows_assocCAB HexagonRowColumn752.cols_right2)) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal7_case_5_2_row_1_1_1 : (((-1 : ℤ) ^ (rightScaleBit 7 5 2).val * positiveScale (rightScaleExponent 7 5 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 2 5 : ℤ)) • HexagonAtoms752.outerLeftABC) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 7 5 2) • (rowColumnMul HexagonRowColumn752.rows_assocCAB HexagonRowColumn752.cols_right2)) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal7_case_5_2_row_1_1_2 : (((-1 : ℤ) ^ (rightScaleBit 7 5 2).val * positiveScale (rightScaleExponent 7 5 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 2 5 : ℤ)) • HexagonAtoms752.outerLeftABC) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 7 5 2) • (rowColumnMul HexagonRowColumn752.rows_assocCAB HexagonRowColumn752.cols_right2)) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal7_case_5_2_row_1_1_3 : (((-1 : ℤ) ^ (rightScaleBit 7 5 2).val * positiveScale (rightScaleExponent 7 5 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 2 5 : ℤ)) • HexagonAtoms752.outerLeftABC) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 7 5 2) • (rowColumnMul HexagonRowColumn752.rows_assocCAB HexagonRowColumn752.cols_right2)) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal7_case_5_2_checked : ((-1 : ℤ) ^ (rightScaleBit 7 5 2).val * positiveScale (rightScaleExponent 7 5 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 2 5 : ℤ)) • HexagonAtoms752.outerLeftABC = negativeScale (rightScaleExponent 7 5 2) • (rowColumnMul HexagonRowColumn752.rows_assocCAB HexagonRowColumn752.cols_right2) := by
  funext r
  fin_cases r
  · exact rightFinal7_case_5_2_row_0_0_0
  · exact rightFinal7_case_5_2_row_0_0_1
  · exact rightFinal7_case_5_2_row_0_0_2
  · exact rightFinal7_case_5_2_row_0_0_3
  · exact rightFinal7_case_5_2_row_0_1_0
  · exact rightFinal7_case_5_2_row_0_1_1
  · exact rightFinal7_case_5_2_row_0_1_2
  · exact rightFinal7_case_5_2_row_0_1_3
  · exact rightFinal7_case_5_2_row_1_0_0
  · exact rightFinal7_case_5_2_row_1_0_1
  · exact rightFinal7_case_5_2_row_1_0_2
  · exact rightFinal7_case_5_2_row_1_0_3
  · exact rightFinal7_case_5_2_row_1_1_0
  · exact rightFinal7_case_5_2_row_1_1_1
  · exact rightFinal7_case_5_2_row_1_1_2
  · exact rightFinal7_case_5_2_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem rightFinal7_case_5_2 : ((-1 : ℤ) ^ (rightScaleBit 7 5 2).val * positiveScale (rightScaleExponent 7 5 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 2 5 : ℤ)) • outerLeftZ 7 5 2 = negativeScale (rightScaleExponent 7 5 2) • (associatorZ 2 7 5 * right2Middle7 5 2) := by
  simpa only [HexagonAtoms752.assocABC_eq,
    HexagonAtoms752.outerABC_eq,
    HexagonAtoms752.assocBAC_eq,
    HexagonAtoms752.innerABC_eq,
    HexagonAtoms752.innerRightABC_eq,
    HexagonAtoms752.inverseACB_eq,
    HexagonAtoms752.innerACB_eq,
    HexagonAtoms752.assocBCA_eq,
    HexagonAtoms752.innerRightBAC_eq,
    HexagonAtoms752.assocCAB_eq,
    HexagonAtoms752.outerLeftABC_eq,
    HexagonRowColumn752.product0_eq,
    HexagonRowColumn752.product1_eq,
    HexagonRowColumn752.product2_eq,
    HexagonRowColumn752.product3_eq,
    HexagonRowColumn752.product4_eq,
    HexagonRowColumn752.product5_eq,
    HexagonRowColumn752.product6_eq,
    HexagonRowColumn752.product7_eq] using rightFinal7_case_5_2_checked

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonCases7
