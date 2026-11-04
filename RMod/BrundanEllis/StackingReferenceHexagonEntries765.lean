import RMod.BrundanEllis.StackingReferenceHexagonMiddle7
import RMod.BrundanEllis.StackingReferenceSparseMatrixCheck
import RMod.BrundanEllis.StackingReferenceHexagonAtoms765
import RMod.BrundanEllis.StackingReferenceHexagonRowColumn765

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

private theorem left0Middle7_eq_case_6_5_row_0_0_0 : (left0Middle7 6 5) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn765.rows_outerABC HexagonRowColumn765.cols_assocABC) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem left0Middle7_eq_case_6_5_row_0_0_1 : (left0Middle7 6 5) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn765.rows_outerABC HexagonRowColumn765.cols_assocABC) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem left0Middle7_eq_case_6_5_row_0_0_2 : (left0Middle7 6 5) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn765.rows_outerABC HexagonRowColumn765.cols_assocABC) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem left0Middle7_eq_case_6_5_row_0_0_3 : (left0Middle7 6 5) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn765.rows_outerABC HexagonRowColumn765.cols_assocABC) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem left0Middle7_eq_case_6_5_row_0_1_0 : (left0Middle7 6 5) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn765.rows_outerABC HexagonRowColumn765.cols_assocABC) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem left0Middle7_eq_case_6_5_row_0_1_1 : (left0Middle7 6 5) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn765.rows_outerABC HexagonRowColumn765.cols_assocABC) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem left0Middle7_eq_case_6_5_row_0_1_2 : (left0Middle7 6 5) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn765.rows_outerABC HexagonRowColumn765.cols_assocABC) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem left0Middle7_eq_case_6_5_row_0_1_3 : (left0Middle7 6 5) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn765.rows_outerABC HexagonRowColumn765.cols_assocABC) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem left0Middle7_eq_case_6_5_row_1_0_0 : (left0Middle7 6 5) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn765.rows_outerABC HexagonRowColumn765.cols_assocABC) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem left0Middle7_eq_case_6_5_row_1_0_1 : (left0Middle7 6 5) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn765.rows_outerABC HexagonRowColumn765.cols_assocABC) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem left0Middle7_eq_case_6_5_row_1_0_2 : (left0Middle7 6 5) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn765.rows_outerABC HexagonRowColumn765.cols_assocABC) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem left0Middle7_eq_case_6_5_row_1_0_3 : (left0Middle7 6 5) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn765.rows_outerABC HexagonRowColumn765.cols_assocABC) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem left0Middle7_eq_case_6_5_row_1_1_0 : (left0Middle7 6 5) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn765.rows_outerABC HexagonRowColumn765.cols_assocABC) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem left0Middle7_eq_case_6_5_row_1_1_1 : (left0Middle7 6 5) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn765.rows_outerABC HexagonRowColumn765.cols_assocABC) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem left0Middle7_eq_case_6_5_row_1_1_2 : (left0Middle7 6 5) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn765.rows_outerABC HexagonRowColumn765.cols_assocABC) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem left0Middle7_eq_case_6_5_row_1_1_3 : (left0Middle7 6 5) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn765.rows_outerABC HexagonRowColumn765.cols_assocABC) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem left0Middle7_eq_case_6_5_checked : left0Middle7 6 5 = rowColumnMul HexagonRowColumn765.rows_outerABC HexagonRowColumn765.cols_assocABC := by
  funext r
  fin_cases r
  · exact left0Middle7_eq_case_6_5_row_0_0_0
  · exact left0Middle7_eq_case_6_5_row_0_0_1
  · exact left0Middle7_eq_case_6_5_row_0_0_2
  · exact left0Middle7_eq_case_6_5_row_0_0_3
  · exact left0Middle7_eq_case_6_5_row_0_1_0
  · exact left0Middle7_eq_case_6_5_row_0_1_1
  · exact left0Middle7_eq_case_6_5_row_0_1_2
  · exact left0Middle7_eq_case_6_5_row_0_1_3
  · exact left0Middle7_eq_case_6_5_row_1_0_0
  · exact left0Middle7_eq_case_6_5_row_1_0_1
  · exact left0Middle7_eq_case_6_5_row_1_0_2
  · exact left0Middle7_eq_case_6_5_row_1_0_3
  · exact left0Middle7_eq_case_6_5_row_1_1_0
  · exact left0Middle7_eq_case_6_5_row_1_1_1
  · exact left0Middle7_eq_case_6_5_row_1_1_2
  · exact left0Middle7_eq_case_6_5_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem left0Middle7_eq_case_6_5 : left0Middle7 6 5 = outerRightZ 7 6 5 * associatorZ 7 6 5 := by
  simpa only [HexagonAtoms765.assocABC_eq,
    HexagonAtoms765.outerABC_eq,
    HexagonAtoms765.assocBAC_eq,
    HexagonAtoms765.innerABC_eq,
    HexagonAtoms765.innerRightABC_eq,
    HexagonAtoms765.inverseACB_eq,
    HexagonAtoms765.innerACB_eq,
    HexagonAtoms765.assocBCA_eq,
    HexagonAtoms765.innerRightBAC_eq,
    HexagonAtoms765.assocCAB_eq,
    HexagonAtoms765.outerLeftABC_eq,
    HexagonRowColumn765.product0_eq,
    HexagonRowColumn765.product1_eq,
    HexagonRowColumn765.product2_eq,
    HexagonRowColumn765.product3_eq,
    HexagonRowColumn765.product4_eq,
    HexagonRowColumn765.product5_eq,
    HexagonRowColumn765.product6_eq,
    HexagonRowColumn765.product7_eq] using left0Middle7_eq_case_6_5_checked

private theorem left1Middle7_eq_case_6_5_row_0_0_0 : (left1Middle7 6 5) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn765.rows_assocBAC HexagonRowColumn765.cols_innerABC) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem left1Middle7_eq_case_6_5_row_0_0_1 : (left1Middle7 6 5) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn765.rows_assocBAC HexagonRowColumn765.cols_innerABC) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem left1Middle7_eq_case_6_5_row_0_0_2 : (left1Middle7 6 5) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn765.rows_assocBAC HexagonRowColumn765.cols_innerABC) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem left1Middle7_eq_case_6_5_row_0_0_3 : (left1Middle7 6 5) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn765.rows_assocBAC HexagonRowColumn765.cols_innerABC) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem left1Middle7_eq_case_6_5_row_0_1_0 : (left1Middle7 6 5) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn765.rows_assocBAC HexagonRowColumn765.cols_innerABC) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem left1Middle7_eq_case_6_5_row_0_1_1 : (left1Middle7 6 5) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn765.rows_assocBAC HexagonRowColumn765.cols_innerABC) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem left1Middle7_eq_case_6_5_row_0_1_2 : (left1Middle7 6 5) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn765.rows_assocBAC HexagonRowColumn765.cols_innerABC) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem left1Middle7_eq_case_6_5_row_0_1_3 : (left1Middle7 6 5) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn765.rows_assocBAC HexagonRowColumn765.cols_innerABC) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem left1Middle7_eq_case_6_5_row_1_0_0 : (left1Middle7 6 5) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn765.rows_assocBAC HexagonRowColumn765.cols_innerABC) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem left1Middle7_eq_case_6_5_row_1_0_1 : (left1Middle7 6 5) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn765.rows_assocBAC HexagonRowColumn765.cols_innerABC) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem left1Middle7_eq_case_6_5_row_1_0_2 : (left1Middle7 6 5) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn765.rows_assocBAC HexagonRowColumn765.cols_innerABC) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem left1Middle7_eq_case_6_5_row_1_0_3 : (left1Middle7 6 5) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn765.rows_assocBAC HexagonRowColumn765.cols_innerABC) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem left1Middle7_eq_case_6_5_row_1_1_0 : (left1Middle7 6 5) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn765.rows_assocBAC HexagonRowColumn765.cols_innerABC) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem left1Middle7_eq_case_6_5_row_1_1_1 : (left1Middle7 6 5) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn765.rows_assocBAC HexagonRowColumn765.cols_innerABC) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem left1Middle7_eq_case_6_5_row_1_1_2 : (left1Middle7 6 5) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn765.rows_assocBAC HexagonRowColumn765.cols_innerABC) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem left1Middle7_eq_case_6_5_row_1_1_3 : (left1Middle7 6 5) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn765.rows_assocBAC HexagonRowColumn765.cols_innerABC) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem left1Middle7_eq_case_6_5_checked : left1Middle7 6 5 = rowColumnMul HexagonRowColumn765.rows_assocBAC HexagonRowColumn765.cols_innerABC := by
  funext r
  fin_cases r
  · exact left1Middle7_eq_case_6_5_row_0_0_0
  · exact left1Middle7_eq_case_6_5_row_0_0_1
  · exact left1Middle7_eq_case_6_5_row_0_0_2
  · exact left1Middle7_eq_case_6_5_row_0_0_3
  · exact left1Middle7_eq_case_6_5_row_0_1_0
  · exact left1Middle7_eq_case_6_5_row_0_1_1
  · exact left1Middle7_eq_case_6_5_row_0_1_2
  · exact left1Middle7_eq_case_6_5_row_0_1_3
  · exact left1Middle7_eq_case_6_5_row_1_0_0
  · exact left1Middle7_eq_case_6_5_row_1_0_1
  · exact left1Middle7_eq_case_6_5_row_1_0_2
  · exact left1Middle7_eq_case_6_5_row_1_0_3
  · exact left1Middle7_eq_case_6_5_row_1_1_0
  · exact left1Middle7_eq_case_6_5_row_1_1_1
  · exact left1Middle7_eq_case_6_5_row_1_1_2
  · exact left1Middle7_eq_case_6_5_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem left1Middle7_eq_case_6_5 : left1Middle7 6 5 = associatorZ 6 7 5 * innerLeftZ 7 6 5 := by
  simpa only [HexagonAtoms765.assocABC_eq,
    HexagonAtoms765.outerABC_eq,
    HexagonAtoms765.assocBAC_eq,
    HexagonAtoms765.innerABC_eq,
    HexagonAtoms765.innerRightABC_eq,
    HexagonAtoms765.inverseACB_eq,
    HexagonAtoms765.innerACB_eq,
    HexagonAtoms765.assocBCA_eq,
    HexagonAtoms765.innerRightBAC_eq,
    HexagonAtoms765.assocCAB_eq,
    HexagonAtoms765.outerLeftABC_eq,
    HexagonRowColumn765.product0_eq,
    HexagonRowColumn765.product1_eq,
    HexagonRowColumn765.product2_eq,
    HexagonRowColumn765.product3_eq,
    HexagonRowColumn765.product4_eq,
    HexagonRowColumn765.product5_eq,
    HexagonRowColumn765.product6_eq,
    HexagonRowColumn765.product7_eq] using left1Middle7_eq_case_6_5_checked

private theorem right0Middle7_eq_case_6_5_row_0_0_0 : (right0Middle7 6 5) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms765.assocABC) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right0Middle7_eq_case_6_5_row_0_0_1 : (right0Middle7 6 5) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms765.assocABC) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right0Middle7_eq_case_6_5_row_0_0_2 : (right0Middle7 6 5) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms765.assocABC) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right0Middle7_eq_case_6_5_row_0_0_3 : (right0Middle7 6 5) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms765.assocABC) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right0Middle7_eq_case_6_5_row_0_1_0 : (right0Middle7 6 5) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms765.assocABC) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right0Middle7_eq_case_6_5_row_0_1_1 : (right0Middle7 6 5) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms765.assocABC) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right0Middle7_eq_case_6_5_row_0_1_2 : (right0Middle7 6 5) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms765.assocABC) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right0Middle7_eq_case_6_5_row_0_1_3 : (right0Middle7 6 5) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms765.assocABC) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right0Middle7_eq_case_6_5_row_1_0_0 : (right0Middle7 6 5) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms765.assocABC) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right0Middle7_eq_case_6_5_row_1_0_1 : (right0Middle7 6 5) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms765.assocABC) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right0Middle7_eq_case_6_5_row_1_0_2 : (right0Middle7 6 5) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms765.assocABC) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right0Middle7_eq_case_6_5_row_1_0_3 : (right0Middle7 6 5) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms765.assocABC) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right0Middle7_eq_case_6_5_row_1_1_0 : (right0Middle7 6 5) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms765.assocABC) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right0Middle7_eq_case_6_5_row_1_1_1 : (right0Middle7 6 5) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms765.assocABC) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right0Middle7_eq_case_6_5_row_1_1_2 : (right0Middle7 6 5) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms765.assocABC) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right0Middle7_eq_case_6_5_row_1_1_3 : (right0Middle7 6 5) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms765.assocABC) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right0Middle7_eq_case_6_5_checked : right0Middle7 6 5 = HexagonAtoms765.assocABC := by
  funext r
  fin_cases r
  · exact right0Middle7_eq_case_6_5_row_0_0_0
  · exact right0Middle7_eq_case_6_5_row_0_0_1
  · exact right0Middle7_eq_case_6_5_row_0_0_2
  · exact right0Middle7_eq_case_6_5_row_0_0_3
  · exact right0Middle7_eq_case_6_5_row_0_1_0
  · exact right0Middle7_eq_case_6_5_row_0_1_1
  · exact right0Middle7_eq_case_6_5_row_0_1_2
  · exact right0Middle7_eq_case_6_5_row_0_1_3
  · exact right0Middle7_eq_case_6_5_row_1_0_0
  · exact right0Middle7_eq_case_6_5_row_1_0_1
  · exact right0Middle7_eq_case_6_5_row_1_0_2
  · exact right0Middle7_eq_case_6_5_row_1_0_3
  · exact right0Middle7_eq_case_6_5_row_1_1_0
  · exact right0Middle7_eq_case_6_5_row_1_1_1
  · exact right0Middle7_eq_case_6_5_row_1_1_2
  · exact right0Middle7_eq_case_6_5_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem right0Middle7_eq_case_6_5 : right0Middle7 6 5 = innerRightZ 7 6 5 * associatorZ 7 6 5 := by
  simpa only [HexagonAtoms765.assocABC_eq,
    HexagonAtoms765.outerABC_eq,
    HexagonAtoms765.assocBAC_eq,
    HexagonAtoms765.innerABC_eq,
    HexagonAtoms765.innerRightABC_eq,
    HexagonAtoms765.inverseACB_eq,
    HexagonAtoms765.innerACB_eq,
    HexagonAtoms765.assocBCA_eq,
    HexagonAtoms765.innerRightBAC_eq,
    HexagonAtoms765.assocCAB_eq,
    HexagonAtoms765.outerLeftABC_eq,
    HexagonRowColumn765.product0_eq,
    HexagonRowColumn765.product1_eq,
    HexagonRowColumn765.product2_eq,
    HexagonRowColumn765.product3_eq,
    HexagonRowColumn765.product4_eq,
    HexagonRowColumn765.product5_eq,
    HexagonRowColumn765.product6_eq,
    HexagonRowColumn765.product7_eq] using right0Middle7_eq_case_6_5_checked

private theorem right1Middle7_eq_case_6_5_row_0_0_0 : (right1Middle7 6 5) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn765.rows_inverseACB HexagonRowColumn765.cols_right0) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right1Middle7_eq_case_6_5_row_0_0_1 : (right1Middle7 6 5) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn765.rows_inverseACB HexagonRowColumn765.cols_right0) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right1Middle7_eq_case_6_5_row_0_0_2 : (right1Middle7 6 5) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn765.rows_inverseACB HexagonRowColumn765.cols_right0) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right1Middle7_eq_case_6_5_row_0_0_3 : (right1Middle7 6 5) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn765.rows_inverseACB HexagonRowColumn765.cols_right0) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right1Middle7_eq_case_6_5_row_0_1_0 : (right1Middle7 6 5) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn765.rows_inverseACB HexagonRowColumn765.cols_right0) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right1Middle7_eq_case_6_5_row_0_1_1 : (right1Middle7 6 5) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn765.rows_inverseACB HexagonRowColumn765.cols_right0) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right1Middle7_eq_case_6_5_row_0_1_2 : (right1Middle7 6 5) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn765.rows_inverseACB HexagonRowColumn765.cols_right0) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right1Middle7_eq_case_6_5_row_0_1_3 : (right1Middle7 6 5) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn765.rows_inverseACB HexagonRowColumn765.cols_right0) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right1Middle7_eq_case_6_5_row_1_0_0 : (right1Middle7 6 5) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn765.rows_inverseACB HexagonRowColumn765.cols_right0) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right1Middle7_eq_case_6_5_row_1_0_1 : (right1Middle7 6 5) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn765.rows_inverseACB HexagonRowColumn765.cols_right0) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right1Middle7_eq_case_6_5_row_1_0_2 : (right1Middle7 6 5) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn765.rows_inverseACB HexagonRowColumn765.cols_right0) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right1Middle7_eq_case_6_5_row_1_0_3 : (right1Middle7 6 5) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn765.rows_inverseACB HexagonRowColumn765.cols_right0) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right1Middle7_eq_case_6_5_row_1_1_0 : (right1Middle7 6 5) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn765.rows_inverseACB HexagonRowColumn765.cols_right0) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right1Middle7_eq_case_6_5_row_1_1_1 : (right1Middle7 6 5) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn765.rows_inverseACB HexagonRowColumn765.cols_right0) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right1Middle7_eq_case_6_5_row_1_1_2 : (right1Middle7 6 5) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn765.rows_inverseACB HexagonRowColumn765.cols_right0) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right1Middle7_eq_case_6_5_row_1_1_3 : (right1Middle7 6 5) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn765.rows_inverseACB HexagonRowColumn765.cols_right0) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right1Middle7_eq_case_6_5_checked : right1Middle7 6 5 = rowColumnMul HexagonRowColumn765.rows_inverseACB HexagonRowColumn765.cols_right0 := by
  funext r
  fin_cases r
  · exact right1Middle7_eq_case_6_5_row_0_0_0
  · exact right1Middle7_eq_case_6_5_row_0_0_1
  · exact right1Middle7_eq_case_6_5_row_0_0_2
  · exact right1Middle7_eq_case_6_5_row_0_0_3
  · exact right1Middle7_eq_case_6_5_row_0_1_0
  · exact right1Middle7_eq_case_6_5_row_0_1_1
  · exact right1Middle7_eq_case_6_5_row_0_1_2
  · exact right1Middle7_eq_case_6_5_row_0_1_3
  · exact right1Middle7_eq_case_6_5_row_1_0_0
  · exact right1Middle7_eq_case_6_5_row_1_0_1
  · exact right1Middle7_eq_case_6_5_row_1_0_2
  · exact right1Middle7_eq_case_6_5_row_1_0_3
  · exact right1Middle7_eq_case_6_5_row_1_1_0
  · exact right1Middle7_eq_case_6_5_row_1_1_1
  · exact right1Middle7_eq_case_6_5_row_1_1_2
  · exact right1Middle7_eq_case_6_5_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem right1Middle7_eq_case_6_5 : right1Middle7 6 5 = associatorInverseZ 7 5 6 * right0Middle7 6 5 := by
  simpa only [HexagonAtoms765.assocABC_eq,
    HexagonAtoms765.outerABC_eq,
    HexagonAtoms765.assocBAC_eq,
    HexagonAtoms765.innerABC_eq,
    HexagonAtoms765.innerRightABC_eq,
    HexagonAtoms765.inverseACB_eq,
    HexagonAtoms765.innerACB_eq,
    HexagonAtoms765.assocBCA_eq,
    HexagonAtoms765.innerRightBAC_eq,
    HexagonAtoms765.assocCAB_eq,
    HexagonAtoms765.outerLeftABC_eq,
    HexagonRowColumn765.product0_eq,
    HexagonRowColumn765.product1_eq,
    HexagonRowColumn765.product2_eq,
    HexagonRowColumn765.product3_eq,
    HexagonRowColumn765.product4_eq,
    HexagonRowColumn765.product5_eq,
    HexagonRowColumn765.product6_eq,
    HexagonRowColumn765.product7_eq] using right1Middle7_eq_case_6_5_checked

private theorem right2Middle7_eq_case_6_5_row_0_0_0 : (right2Middle7 6 5) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (right1Middle7 6 5) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right2Middle7_eq_case_6_5_row_0_0_1 : (right2Middle7 6 5) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (right1Middle7 6 5) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right2Middle7_eq_case_6_5_row_0_0_2 : (right2Middle7 6 5) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (right1Middle7 6 5) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right2Middle7_eq_case_6_5_row_0_0_3 : (right2Middle7 6 5) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (right1Middle7 6 5) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right2Middle7_eq_case_6_5_row_0_1_0 : (right2Middle7 6 5) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (right1Middle7 6 5) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right2Middle7_eq_case_6_5_row_0_1_1 : (right2Middle7 6 5) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (right1Middle7 6 5) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right2Middle7_eq_case_6_5_row_0_1_2 : (right2Middle7 6 5) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (right1Middle7 6 5) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right2Middle7_eq_case_6_5_row_0_1_3 : (right2Middle7 6 5) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (right1Middle7 6 5) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right2Middle7_eq_case_6_5_row_1_0_0 : (right2Middle7 6 5) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (right1Middle7 6 5) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right2Middle7_eq_case_6_5_row_1_0_1 : (right2Middle7 6 5) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (right1Middle7 6 5) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right2Middle7_eq_case_6_5_row_1_0_2 : (right2Middle7 6 5) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (right1Middle7 6 5) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right2Middle7_eq_case_6_5_row_1_0_3 : (right2Middle7 6 5) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (right1Middle7 6 5) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right2Middle7_eq_case_6_5_row_1_1_0 : (right2Middle7 6 5) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (right1Middle7 6 5) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right2Middle7_eq_case_6_5_row_1_1_1 : (right2Middle7 6 5) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (right1Middle7 6 5) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right2Middle7_eq_case_6_5_row_1_1_2 : (right2Middle7 6 5) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (right1Middle7 6 5) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right2Middle7_eq_case_6_5_row_1_1_3 : (right2Middle7 6 5) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (right1Middle7 6 5) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right2Middle7_eq_case_6_5_checked : right2Middle7 6 5 = right1Middle7 6 5 := by
  funext r
  fin_cases r
  · exact right2Middle7_eq_case_6_5_row_0_0_0
  · exact right2Middle7_eq_case_6_5_row_0_0_1
  · exact right2Middle7_eq_case_6_5_row_0_0_2
  · exact right2Middle7_eq_case_6_5_row_0_0_3
  · exact right2Middle7_eq_case_6_5_row_0_1_0
  · exact right2Middle7_eq_case_6_5_row_0_1_1
  · exact right2Middle7_eq_case_6_5_row_0_1_2
  · exact right2Middle7_eq_case_6_5_row_0_1_3
  · exact right2Middle7_eq_case_6_5_row_1_0_0
  · exact right2Middle7_eq_case_6_5_row_1_0_1
  · exact right2Middle7_eq_case_6_5_row_1_0_2
  · exact right2Middle7_eq_case_6_5_row_1_0_3
  · exact right2Middle7_eq_case_6_5_row_1_1_0
  · exact right2Middle7_eq_case_6_5_row_1_1_1
  · exact right2Middle7_eq_case_6_5_row_1_1_2
  · exact right2Middle7_eq_case_6_5_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem right2Middle7_eq_case_6_5 : right2Middle7 6 5 = innerLeftZ 7 5 6 * right1Middle7 6 5 := by
  simpa only [HexagonAtoms765.assocABC_eq,
    HexagonAtoms765.outerABC_eq,
    HexagonAtoms765.assocBAC_eq,
    HexagonAtoms765.innerABC_eq,
    HexagonAtoms765.innerRightABC_eq,
    HexagonAtoms765.inverseACB_eq,
    HexagonAtoms765.innerACB_eq,
    HexagonAtoms765.assocBCA_eq,
    HexagonAtoms765.innerRightBAC_eq,
    HexagonAtoms765.assocCAB_eq,
    HexagonAtoms765.outerLeftABC_eq,
    HexagonRowColumn765.product0_eq,
    HexagonRowColumn765.product1_eq,
    HexagonRowColumn765.product2_eq,
    HexagonRowColumn765.product3_eq,
    HexagonRowColumn765.product4_eq,
    HexagonRowColumn765.product5_eq,
    HexagonRowColumn765.product6_eq,
    HexagonRowColumn765.product7_eq] using right2Middle7_eq_case_6_5_checked

private theorem leftFinal7_case_6_5_row_0_0_0 : (((-1 : ℤ) ^ (leftScaleBit 7 6 5).val * positiveScale (leftScaleExponent 7 6 5)) •
      (rowColumnMul HexagonRowColumn765.rows_assocBCA HexagonRowColumn765.cols_left0)) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 7 6 5) • (left1Middle7 6 5)) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem leftFinal7_case_6_5_row_0_0_1 : (((-1 : ℤ) ^ (leftScaleBit 7 6 5).val * positiveScale (leftScaleExponent 7 6 5)) •
      (rowColumnMul HexagonRowColumn765.rows_assocBCA HexagonRowColumn765.cols_left0)) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 7 6 5) • (left1Middle7 6 5)) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem leftFinal7_case_6_5_row_0_0_2 : (((-1 : ℤ) ^ (leftScaleBit 7 6 5).val * positiveScale (leftScaleExponent 7 6 5)) •
      (rowColumnMul HexagonRowColumn765.rows_assocBCA HexagonRowColumn765.cols_left0)) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 7 6 5) • (left1Middle7 6 5)) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem leftFinal7_case_6_5_row_0_0_3 : (((-1 : ℤ) ^ (leftScaleBit 7 6 5).val * positiveScale (leftScaleExponent 7 6 5)) •
      (rowColumnMul HexagonRowColumn765.rows_assocBCA HexagonRowColumn765.cols_left0)) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 7 6 5) • (left1Middle7 6 5)) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem leftFinal7_case_6_5_row_0_1_0 : (((-1 : ℤ) ^ (leftScaleBit 7 6 5).val * positiveScale (leftScaleExponent 7 6 5)) •
      (rowColumnMul HexagonRowColumn765.rows_assocBCA HexagonRowColumn765.cols_left0)) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 7 6 5) • (left1Middle7 6 5)) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem leftFinal7_case_6_5_row_0_1_1 : (((-1 : ℤ) ^ (leftScaleBit 7 6 5).val * positiveScale (leftScaleExponent 7 6 5)) •
      (rowColumnMul HexagonRowColumn765.rows_assocBCA HexagonRowColumn765.cols_left0)) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 7 6 5) • (left1Middle7 6 5)) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem leftFinal7_case_6_5_row_0_1_2 : (((-1 : ℤ) ^ (leftScaleBit 7 6 5).val * positiveScale (leftScaleExponent 7 6 5)) •
      (rowColumnMul HexagonRowColumn765.rows_assocBCA HexagonRowColumn765.cols_left0)) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 7 6 5) • (left1Middle7 6 5)) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem leftFinal7_case_6_5_row_0_1_3 : (((-1 : ℤ) ^ (leftScaleBit 7 6 5).val * positiveScale (leftScaleExponent 7 6 5)) •
      (rowColumnMul HexagonRowColumn765.rows_assocBCA HexagonRowColumn765.cols_left0)) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 7 6 5) • (left1Middle7 6 5)) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem leftFinal7_case_6_5_row_1_0_0 : (((-1 : ℤ) ^ (leftScaleBit 7 6 5).val * positiveScale (leftScaleExponent 7 6 5)) •
      (rowColumnMul HexagonRowColumn765.rows_assocBCA HexagonRowColumn765.cols_left0)) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 7 6 5) • (left1Middle7 6 5)) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem leftFinal7_case_6_5_row_1_0_1 : (((-1 : ℤ) ^ (leftScaleBit 7 6 5).val * positiveScale (leftScaleExponent 7 6 5)) •
      (rowColumnMul HexagonRowColumn765.rows_assocBCA HexagonRowColumn765.cols_left0)) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 7 6 5) • (left1Middle7 6 5)) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem leftFinal7_case_6_5_row_1_0_2 : (((-1 : ℤ) ^ (leftScaleBit 7 6 5).val * positiveScale (leftScaleExponent 7 6 5)) •
      (rowColumnMul HexagonRowColumn765.rows_assocBCA HexagonRowColumn765.cols_left0)) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 7 6 5) • (left1Middle7 6 5)) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem leftFinal7_case_6_5_row_1_0_3 : (((-1 : ℤ) ^ (leftScaleBit 7 6 5).val * positiveScale (leftScaleExponent 7 6 5)) •
      (rowColumnMul HexagonRowColumn765.rows_assocBCA HexagonRowColumn765.cols_left0)) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 7 6 5) • (left1Middle7 6 5)) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem leftFinal7_case_6_5_row_1_1_0 : (((-1 : ℤ) ^ (leftScaleBit 7 6 5).val * positiveScale (leftScaleExponent 7 6 5)) •
      (rowColumnMul HexagonRowColumn765.rows_assocBCA HexagonRowColumn765.cols_left0)) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 7 6 5) • (left1Middle7 6 5)) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem leftFinal7_case_6_5_row_1_1_1 : (((-1 : ℤ) ^ (leftScaleBit 7 6 5).val * positiveScale (leftScaleExponent 7 6 5)) •
      (rowColumnMul HexagonRowColumn765.rows_assocBCA HexagonRowColumn765.cols_left0)) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 7 6 5) • (left1Middle7 6 5)) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem leftFinal7_case_6_5_row_1_1_2 : (((-1 : ℤ) ^ (leftScaleBit 7 6 5).val * positiveScale (leftScaleExponent 7 6 5)) •
      (rowColumnMul HexagonRowColumn765.rows_assocBCA HexagonRowColumn765.cols_left0)) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 7 6 5) • (left1Middle7 6 5)) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem leftFinal7_case_6_5_row_1_1_3 : (((-1 : ℤ) ^ (leftScaleBit 7 6 5).val * positiveScale (leftScaleExponent 7 6 5)) •
      (rowColumnMul HexagonRowColumn765.rows_assocBCA HexagonRowColumn765.cols_left0)) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 7 6 5) • (left1Middle7 6 5)) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem leftFinal7_case_6_5_checked : ((-1 : ℤ) ^ (leftScaleBit 7 6 5).val * positiveScale (leftScaleExponent 7 6 5)) •
      (rowColumnMul HexagonRowColumn765.rows_assocBCA HexagonRowColumn765.cols_left0) = negativeScale (leftScaleExponent 7 6 5) • (left1Middle7 6 5) := by
  funext r
  fin_cases r
  · exact leftFinal7_case_6_5_row_0_0_0
  · exact leftFinal7_case_6_5_row_0_0_1
  · exact leftFinal7_case_6_5_row_0_0_2
  · exact leftFinal7_case_6_5_row_0_0_3
  · exact leftFinal7_case_6_5_row_0_1_0
  · exact leftFinal7_case_6_5_row_0_1_1
  · exact leftFinal7_case_6_5_row_0_1_2
  · exact leftFinal7_case_6_5_row_0_1_3
  · exact leftFinal7_case_6_5_row_1_0_0
  · exact leftFinal7_case_6_5_row_1_0_1
  · exact leftFinal7_case_6_5_row_1_0_2
  · exact leftFinal7_case_6_5_row_1_0_3
  · exact leftFinal7_case_6_5_row_1_1_0
  · exact leftFinal7_case_6_5_row_1_1_1
  · exact leftFinal7_case_6_5_row_1_1_2
  · exact leftFinal7_case_6_5_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem leftFinal7_case_6_5 : ((-1 : ℤ) ^ (leftScaleBit 7 6 5).val * positiveScale (leftScaleExponent 7 6 5)) •
      (associatorZ 6 5 7 * left0Middle7 6 5) = negativeScale (leftScaleExponent 7 6 5) • (innerRightZ 6 7 5 * left1Middle7 6 5) := by
  simpa only [HexagonAtoms765.assocABC_eq,
    HexagonAtoms765.outerABC_eq,
    HexagonAtoms765.assocBAC_eq,
    HexagonAtoms765.innerABC_eq,
    HexagonAtoms765.innerRightABC_eq,
    HexagonAtoms765.inverseACB_eq,
    HexagonAtoms765.innerACB_eq,
    HexagonAtoms765.assocBCA_eq,
    HexagonAtoms765.innerRightBAC_eq,
    HexagonAtoms765.assocCAB_eq,
    HexagonAtoms765.outerLeftABC_eq,
    HexagonRowColumn765.product0_eq,
    HexagonRowColumn765.product1_eq,
    HexagonRowColumn765.product2_eq,
    HexagonRowColumn765.product3_eq,
    HexagonRowColumn765.product4_eq,
    HexagonRowColumn765.product5_eq,
    HexagonRowColumn765.product6_eq,
    HexagonRowColumn765.product7_eq] using leftFinal7_case_6_5_checked

private theorem rightFinal7_case_6_5_row_0_0_0 : (((-1 : ℤ) ^ (rightScaleBit 7 6 5).val * positiveScale (rightScaleExponent 7 6 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 5 6 : ℤ)) • HexagonAtoms765.outerLeftABC) ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4)) = (negativeScale (rightScaleExponent 7 6 5) • (rowColumnMul HexagonRowColumn765.rows_assocCAB HexagonRowColumn765.cols_right2)) ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem rightFinal7_case_6_5_row_0_0_1 : (((-1 : ℤ) ^ (rightScaleBit 7 6 5).val * positiveScale (rightScaleExponent 7 6 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 5 6 : ℤ)) • HexagonAtoms765.outerLeftABC) ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4)) = (negativeScale (rightScaleExponent 7 6 5) • (rowColumnMul HexagonRowColumn765.rows_assocCAB HexagonRowColumn765.cols_right2)) ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem rightFinal7_case_6_5_row_0_0_2 : (((-1 : ℤ) ^ (rightScaleBit 7 6 5).val * positiveScale (rightScaleExponent 7 6 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 5 6 : ℤ)) • HexagonAtoms765.outerLeftABC) ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4)) = (negativeScale (rightScaleExponent 7 6 5) • (rowColumnMul HexagonRowColumn765.rows_assocCAB HexagonRowColumn765.cols_right2)) ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem rightFinal7_case_6_5_row_0_0_3 : (((-1 : ℤ) ^ (rightScaleBit 7 6 5).val * positiveScale (rightScaleExponent 7 6 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 5 6 : ℤ)) • HexagonAtoms765.outerLeftABC) ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4)) = (negativeScale (rightScaleExponent 7 6 5) • (rowColumnMul HexagonRowColumn765.rows_assocCAB HexagonRowColumn765.cols_right2)) ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem rightFinal7_case_6_5_row_0_1_0 : (((-1 : ℤ) ^ (rightScaleBit 7 6 5).val * positiveScale (rightScaleExponent 7 6 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 5 6 : ℤ)) • HexagonAtoms765.outerLeftABC) ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4)) = (negativeScale (rightScaleExponent 7 6 5) • (rowColumnMul HexagonRowColumn765.rows_assocCAB HexagonRowColumn765.cols_right2)) ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem rightFinal7_case_6_5_row_0_1_1 : (((-1 : ℤ) ^ (rightScaleBit 7 6 5).val * positiveScale (rightScaleExponent 7 6 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 5 6 : ℤ)) • HexagonAtoms765.outerLeftABC) ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4)) = (negativeScale (rightScaleExponent 7 6 5) • (rowColumnMul HexagonRowColumn765.rows_assocCAB HexagonRowColumn765.cols_right2)) ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem rightFinal7_case_6_5_row_0_1_2 : (((-1 : ℤ) ^ (rightScaleBit 7 6 5).val * positiveScale (rightScaleExponent 7 6 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 5 6 : ℤ)) • HexagonAtoms765.outerLeftABC) ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4)) = (negativeScale (rightScaleExponent 7 6 5) • (rowColumnMul HexagonRowColumn765.rows_assocCAB HexagonRowColumn765.cols_right2)) ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem rightFinal7_case_6_5_row_0_1_3 : (((-1 : ℤ) ^ (rightScaleBit 7 6 5).val * positiveScale (rightScaleExponent 7 6 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 5 6 : ℤ)) • HexagonAtoms765.outerLeftABC) ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4)) = (negativeScale (rightScaleExponent 7 6 5) • (rowColumnMul HexagonRowColumn765.rows_assocCAB HexagonRowColumn765.cols_right2)) ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem rightFinal7_case_6_5_row_0_2_0 : (((-1 : ℤ) ^ (rightScaleBit 7 6 5).val * positiveScale (rightScaleExponent 7 6 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 5 6 : ℤ)) • HexagonAtoms765.outerLeftABC) ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4)) = (negativeScale (rightScaleExponent 7 6 5) • (rowColumnMul HexagonRowColumn765.rows_assocCAB HexagonRowColumn765.cols_right2)) ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem rightFinal7_case_6_5_row_0_2_1 : (((-1 : ℤ) ^ (rightScaleBit 7 6 5).val * positiveScale (rightScaleExponent 7 6 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 5 6 : ℤ)) • HexagonAtoms765.outerLeftABC) ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4)) = (negativeScale (rightScaleExponent 7 6 5) • (rowColumnMul HexagonRowColumn765.rows_assocCAB HexagonRowColumn765.cols_right2)) ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem rightFinal7_case_6_5_row_0_2_2 : (((-1 : ℤ) ^ (rightScaleBit 7 6 5).val * positiveScale (rightScaleExponent 7 6 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 5 6 : ℤ)) • HexagonAtoms765.outerLeftABC) ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4)) = (negativeScale (rightScaleExponent 7 6 5) • (rowColumnMul HexagonRowColumn765.rows_assocCAB HexagonRowColumn765.cols_right2)) ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem rightFinal7_case_6_5_row_0_2_3 : (((-1 : ℤ) ^ (rightScaleBit 7 6 5).val * positiveScale (rightScaleExponent 7 6 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 5 6 : ℤ)) • HexagonAtoms765.outerLeftABC) ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4)) = (negativeScale (rightScaleExponent 7 6 5) • (rowColumnMul HexagonRowColumn765.rows_assocCAB HexagonRowColumn765.cols_right2)) ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem rightFinal7_case_6_5_row_0_3_0 : (((-1 : ℤ) ^ (rightScaleBit 7 6 5).val * positiveScale (rightScaleExponent 7 6 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 5 6 : ℤ)) • HexagonAtoms765.outerLeftABC) ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4)) = (negativeScale (rightScaleExponent 7 6 5) • (rowColumnMul HexagonRowColumn765.rows_assocCAB HexagonRowColumn765.cols_right2)) ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem rightFinal7_case_6_5_row_0_3_1 : (((-1 : ℤ) ^ (rightScaleBit 7 6 5).val * positiveScale (rightScaleExponent 7 6 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 5 6 : ℤ)) • HexagonAtoms765.outerLeftABC) ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4)) = (negativeScale (rightScaleExponent 7 6 5) • (rowColumnMul HexagonRowColumn765.rows_assocCAB HexagonRowColumn765.cols_right2)) ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem rightFinal7_case_6_5_row_0_3_2 : (((-1 : ℤ) ^ (rightScaleBit 7 6 5).val * positiveScale (rightScaleExponent 7 6 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 5 6 : ℤ)) • HexagonAtoms765.outerLeftABC) ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4)) = (negativeScale (rightScaleExponent 7 6 5) • (rowColumnMul HexagonRowColumn765.rows_assocCAB HexagonRowColumn765.cols_right2)) ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem rightFinal7_case_6_5_row_0_3_3 : (((-1 : ℤ) ^ (rightScaleBit 7 6 5).val * positiveScale (rightScaleExponent 7 6 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 5 6 : ℤ)) • HexagonAtoms765.outerLeftABC) ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4)) = (negativeScale (rightScaleExponent 7 6 5) • (rowColumnMul HexagonRowColumn765.rows_assocCAB HexagonRowColumn765.cols_right2)) ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem rightFinal7_case_6_5_checked : ((-1 : ℤ) ^ (rightScaleBit 7 6 5).val * positiveScale (rightScaleExponent 7 6 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 5 6 : ℤ)) • HexagonAtoms765.outerLeftABC = negativeScale (rightScaleExponent 7 6 5) • (rowColumnMul HexagonRowColumn765.rows_assocCAB HexagonRowColumn765.cols_right2) := by
  funext r
  fin_cases r
  · exact rightFinal7_case_6_5_row_0_0_0
  · exact rightFinal7_case_6_5_row_0_0_1
  · exact rightFinal7_case_6_5_row_0_0_2
  · exact rightFinal7_case_6_5_row_0_0_3
  · exact rightFinal7_case_6_5_row_0_1_0
  · exact rightFinal7_case_6_5_row_0_1_1
  · exact rightFinal7_case_6_5_row_0_1_2
  · exact rightFinal7_case_6_5_row_0_1_3
  · exact rightFinal7_case_6_5_row_0_2_0
  · exact rightFinal7_case_6_5_row_0_2_1
  · exact rightFinal7_case_6_5_row_0_2_2
  · exact rightFinal7_case_6_5_row_0_2_3
  · exact rightFinal7_case_6_5_row_0_3_0
  · exact rightFinal7_case_6_5_row_0_3_1
  · exact rightFinal7_case_6_5_row_0_3_2
  · exact rightFinal7_case_6_5_row_0_3_3

set_option backward.isDefEq.respectTransparency false in
theorem rightFinal7_case_6_5 : ((-1 : ℤ) ^ (rightScaleBit 7 6 5).val * positiveScale (rightScaleExponent 7 6 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 5 6 : ℤ)) • outerLeftZ 7 6 5 = negativeScale (rightScaleExponent 7 6 5) • (associatorZ 5 7 6 * right2Middle7 6 5) := by
  simpa only [HexagonAtoms765.assocABC_eq,
    HexagonAtoms765.outerABC_eq,
    HexagonAtoms765.assocBAC_eq,
    HexagonAtoms765.innerABC_eq,
    HexagonAtoms765.innerRightABC_eq,
    HexagonAtoms765.inverseACB_eq,
    HexagonAtoms765.innerACB_eq,
    HexagonAtoms765.assocBCA_eq,
    HexagonAtoms765.innerRightBAC_eq,
    HexagonAtoms765.assocCAB_eq,
    HexagonAtoms765.outerLeftABC_eq,
    HexagonRowColumn765.product0_eq,
    HexagonRowColumn765.product1_eq,
    HexagonRowColumn765.product2_eq,
    HexagonRowColumn765.product3_eq,
    HexagonRowColumn765.product4_eq,
    HexagonRowColumn765.product5_eq,
    HexagonRowColumn765.product6_eq,
    HexagonRowColumn765.product7_eq] using rightFinal7_case_6_5_checked

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonCases7
