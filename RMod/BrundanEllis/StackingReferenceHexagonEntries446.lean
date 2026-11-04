import RMod.BrundanEllis.StackingReferenceHexagonMiddle4
import RMod.BrundanEllis.StackingReferenceSparseMatrixCheck
import RMod.BrundanEllis.StackingReferenceHexagonAtoms446
import RMod.BrundanEllis.StackingReferenceHexagonRowColumn446

/-! Seven closed product identities for one reference triple.
The proof uses only verified atomic maps and ordinary kernel reduction. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
set_option linter.unusedSimpArgs false
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonCases4
open Superfusion

private theorem left0Middle4_eq_case_4_6_row_0_0_0 : (left0Middle4 4 6) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms446.assocABC) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_4_6_row_0_0_1 : (left0Middle4 4 6) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms446.assocABC) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_4_6_row_0_0_2 : (left0Middle4 4 6) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms446.assocABC) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_4_6_row_0_0_3 : (left0Middle4 4 6) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms446.assocABC) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_4_6_row_0_1_0 : (left0Middle4 4 6) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms446.assocABC) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_4_6_row_0_1_1 : (left0Middle4 4 6) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms446.assocABC) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_4_6_row_0_1_2 : (left0Middle4 4 6) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms446.assocABC) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_4_6_row_0_1_3 : (left0Middle4 4 6) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms446.assocABC) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_4_6_row_1_0_0 : (left0Middle4 4 6) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms446.assocABC) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_4_6_row_1_0_1 : (left0Middle4 4 6) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms446.assocABC) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_4_6_row_1_0_2 : (left0Middle4 4 6) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms446.assocABC) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_4_6_row_1_0_3 : (left0Middle4 4 6) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms446.assocABC) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_4_6_row_1_1_0 : (left0Middle4 4 6) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms446.assocABC) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_4_6_row_1_1_1 : (left0Middle4 4 6) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms446.assocABC) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_4_6_row_1_1_2 : (left0Middle4 4 6) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms446.assocABC) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_4_6_row_1_1_3 : (left0Middle4 4 6) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms446.assocABC) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_4_6_checked : left0Middle4 4 6 = HexagonAtoms446.assocABC := by
  funext r
  fin_cases r
  · exact left0Middle4_eq_case_4_6_row_0_0_0
  · exact left0Middle4_eq_case_4_6_row_0_0_1
  · exact left0Middle4_eq_case_4_6_row_0_0_2
  · exact left0Middle4_eq_case_4_6_row_0_0_3
  · exact left0Middle4_eq_case_4_6_row_0_1_0
  · exact left0Middle4_eq_case_4_6_row_0_1_1
  · exact left0Middle4_eq_case_4_6_row_0_1_2
  · exact left0Middle4_eq_case_4_6_row_0_1_3
  · exact left0Middle4_eq_case_4_6_row_1_0_0
  · exact left0Middle4_eq_case_4_6_row_1_0_1
  · exact left0Middle4_eq_case_4_6_row_1_0_2
  · exact left0Middle4_eq_case_4_6_row_1_0_3
  · exact left0Middle4_eq_case_4_6_row_1_1_0
  · exact left0Middle4_eq_case_4_6_row_1_1_1
  · exact left0Middle4_eq_case_4_6_row_1_1_2
  · exact left0Middle4_eq_case_4_6_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem left0Middle4_eq_case_4_6 : left0Middle4 4 6 = outerRightZ 4 4 6 * associatorZ 4 4 6 := by
  simpa only [HexagonAtoms446.assocABC_eq,
    HexagonAtoms446.outerABC_eq,
    HexagonAtoms446.assocBAC_eq,
    HexagonAtoms446.innerABC_eq,
    HexagonAtoms446.innerRightABC_eq,
    HexagonAtoms446.inverseACB_eq,
    HexagonAtoms446.innerACB_eq,
    HexagonAtoms446.assocBCA_eq,
    HexagonAtoms446.innerRightBAC_eq,
    HexagonAtoms446.assocCAB_eq,
    HexagonAtoms446.outerLeftABC_eq,
    HexagonRowColumn446.assocBAC_alias,
    HexagonRowColumn446.innerRightBAC_alias,
    HexagonRowColumn446.product0_eq,
    HexagonRowColumn446.product1_eq,
    HexagonRowColumn446.product2_eq,
    HexagonRowColumn446.product3_eq,
    HexagonRowColumn446.product4_eq,
    HexagonRowColumn446.product5_eq,
    HexagonRowColumn446.product6_eq,
    HexagonRowColumn446.product7_eq] using left0Middle4_eq_case_4_6_checked

private theorem left1Middle4_eq_case_4_6_row_0_0_0 : (left1Middle4 4 6) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn446.rows_assocABC HexagonRowColumn446.cols_innerABC) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_4_6_row_0_0_1 : (left1Middle4 4 6) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn446.rows_assocABC HexagonRowColumn446.cols_innerABC) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_4_6_row_0_0_2 : (left1Middle4 4 6) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn446.rows_assocABC HexagonRowColumn446.cols_innerABC) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_4_6_row_0_0_3 : (left1Middle4 4 6) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn446.rows_assocABC HexagonRowColumn446.cols_innerABC) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_4_6_row_0_1_0 : (left1Middle4 4 6) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn446.rows_assocABC HexagonRowColumn446.cols_innerABC) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_4_6_row_0_1_1 : (left1Middle4 4 6) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn446.rows_assocABC HexagonRowColumn446.cols_innerABC) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_4_6_row_0_1_2 : (left1Middle4 4 6) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn446.rows_assocABC HexagonRowColumn446.cols_innerABC) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_4_6_row_0_1_3 : (left1Middle4 4 6) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn446.rows_assocABC HexagonRowColumn446.cols_innerABC) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_4_6_row_1_0_0 : (left1Middle4 4 6) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn446.rows_assocABC HexagonRowColumn446.cols_innerABC) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_4_6_row_1_0_1 : (left1Middle4 4 6) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn446.rows_assocABC HexagonRowColumn446.cols_innerABC) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_4_6_row_1_0_2 : (left1Middle4 4 6) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn446.rows_assocABC HexagonRowColumn446.cols_innerABC) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_4_6_row_1_0_3 : (left1Middle4 4 6) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn446.rows_assocABC HexagonRowColumn446.cols_innerABC) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_4_6_row_1_1_0 : (left1Middle4 4 6) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn446.rows_assocABC HexagonRowColumn446.cols_innerABC) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_4_6_row_1_1_1 : (left1Middle4 4 6) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn446.rows_assocABC HexagonRowColumn446.cols_innerABC) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_4_6_row_1_1_2 : (left1Middle4 4 6) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn446.rows_assocABC HexagonRowColumn446.cols_innerABC) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_4_6_row_1_1_3 : (left1Middle4 4 6) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn446.rows_assocABC HexagonRowColumn446.cols_innerABC) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_4_6_checked : left1Middle4 4 6 = rowColumnMul HexagonRowColumn446.rows_assocABC HexagonRowColumn446.cols_innerABC := by
  funext r
  fin_cases r
  · exact left1Middle4_eq_case_4_6_row_0_0_0
  · exact left1Middle4_eq_case_4_6_row_0_0_1
  · exact left1Middle4_eq_case_4_6_row_0_0_2
  · exact left1Middle4_eq_case_4_6_row_0_0_3
  · exact left1Middle4_eq_case_4_6_row_0_1_0
  · exact left1Middle4_eq_case_4_6_row_0_1_1
  · exact left1Middle4_eq_case_4_6_row_0_1_2
  · exact left1Middle4_eq_case_4_6_row_0_1_3
  · exact left1Middle4_eq_case_4_6_row_1_0_0
  · exact left1Middle4_eq_case_4_6_row_1_0_1
  · exact left1Middle4_eq_case_4_6_row_1_0_2
  · exact left1Middle4_eq_case_4_6_row_1_0_3
  · exact left1Middle4_eq_case_4_6_row_1_1_0
  · exact left1Middle4_eq_case_4_6_row_1_1_1
  · exact left1Middle4_eq_case_4_6_row_1_1_2
  · exact left1Middle4_eq_case_4_6_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem left1Middle4_eq_case_4_6 : left1Middle4 4 6 = associatorZ 4 4 6 * innerLeftZ 4 4 6 := by
  simpa only [HexagonAtoms446.assocABC_eq,
    HexagonAtoms446.outerABC_eq,
    HexagonAtoms446.assocBAC_eq,
    HexagonAtoms446.innerABC_eq,
    HexagonAtoms446.innerRightABC_eq,
    HexagonAtoms446.inverseACB_eq,
    HexagonAtoms446.innerACB_eq,
    HexagonAtoms446.assocBCA_eq,
    HexagonAtoms446.innerRightBAC_eq,
    HexagonAtoms446.assocCAB_eq,
    HexagonAtoms446.outerLeftABC_eq,
    HexagonRowColumn446.assocBAC_alias,
    HexagonRowColumn446.innerRightBAC_alias,
    HexagonRowColumn446.product0_eq,
    HexagonRowColumn446.product1_eq,
    HexagonRowColumn446.product2_eq,
    HexagonRowColumn446.product3_eq,
    HexagonRowColumn446.product4_eq,
    HexagonRowColumn446.product5_eq,
    HexagonRowColumn446.product6_eq,
    HexagonRowColumn446.product7_eq] using left1Middle4_eq_case_4_6_checked

private theorem right0Middle4_eq_case_4_6_row_0_0_0 : (right0Middle4 4 6) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms446.assocABC) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_4_6_row_0_0_1 : (right0Middle4 4 6) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms446.assocABC) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_4_6_row_0_0_2 : (right0Middle4 4 6) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms446.assocABC) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_4_6_row_0_0_3 : (right0Middle4 4 6) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms446.assocABC) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_4_6_row_0_1_0 : (right0Middle4 4 6) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms446.assocABC) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_4_6_row_0_1_1 : (right0Middle4 4 6) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms446.assocABC) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_4_6_row_0_1_2 : (right0Middle4 4 6) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms446.assocABC) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_4_6_row_0_1_3 : (right0Middle4 4 6) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms446.assocABC) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_4_6_row_1_0_0 : (right0Middle4 4 6) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms446.assocABC) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_4_6_row_1_0_1 : (right0Middle4 4 6) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms446.assocABC) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_4_6_row_1_0_2 : (right0Middle4 4 6) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms446.assocABC) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_4_6_row_1_0_3 : (right0Middle4 4 6) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms446.assocABC) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_4_6_row_1_1_0 : (right0Middle4 4 6) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms446.assocABC) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_4_6_row_1_1_1 : (right0Middle4 4 6) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms446.assocABC) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_4_6_row_1_1_2 : (right0Middle4 4 6) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms446.assocABC) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_4_6_row_1_1_3 : (right0Middle4 4 6) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms446.assocABC) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_4_6_checked : right0Middle4 4 6 = HexagonAtoms446.assocABC := by
  funext r
  fin_cases r
  · exact right0Middle4_eq_case_4_6_row_0_0_0
  · exact right0Middle4_eq_case_4_6_row_0_0_1
  · exact right0Middle4_eq_case_4_6_row_0_0_2
  · exact right0Middle4_eq_case_4_6_row_0_0_3
  · exact right0Middle4_eq_case_4_6_row_0_1_0
  · exact right0Middle4_eq_case_4_6_row_0_1_1
  · exact right0Middle4_eq_case_4_6_row_0_1_2
  · exact right0Middle4_eq_case_4_6_row_0_1_3
  · exact right0Middle4_eq_case_4_6_row_1_0_0
  · exact right0Middle4_eq_case_4_6_row_1_0_1
  · exact right0Middle4_eq_case_4_6_row_1_0_2
  · exact right0Middle4_eq_case_4_6_row_1_0_3
  · exact right0Middle4_eq_case_4_6_row_1_1_0
  · exact right0Middle4_eq_case_4_6_row_1_1_1
  · exact right0Middle4_eq_case_4_6_row_1_1_2
  · exact right0Middle4_eq_case_4_6_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem right0Middle4_eq_case_4_6 : right0Middle4 4 6 = innerRightZ 4 4 6 * associatorZ 4 4 6 := by
  simpa only [HexagonAtoms446.assocABC_eq,
    HexagonAtoms446.outerABC_eq,
    HexagonAtoms446.assocBAC_eq,
    HexagonAtoms446.innerABC_eq,
    HexagonAtoms446.innerRightABC_eq,
    HexagonAtoms446.inverseACB_eq,
    HexagonAtoms446.innerACB_eq,
    HexagonAtoms446.assocBCA_eq,
    HexagonAtoms446.innerRightBAC_eq,
    HexagonAtoms446.assocCAB_eq,
    HexagonAtoms446.outerLeftABC_eq,
    HexagonRowColumn446.assocBAC_alias,
    HexagonRowColumn446.innerRightBAC_alias,
    HexagonRowColumn446.product0_eq,
    HexagonRowColumn446.product1_eq,
    HexagonRowColumn446.product2_eq,
    HexagonRowColumn446.product3_eq,
    HexagonRowColumn446.product4_eq,
    HexagonRowColumn446.product5_eq,
    HexagonRowColumn446.product6_eq,
    HexagonRowColumn446.product7_eq] using right0Middle4_eq_case_4_6_checked

private theorem right1Middle4_eq_case_4_6_row_0_0_0 : (right1Middle4 4 6) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn446.rows_inverseACB HexagonRowColumn446.cols_right0) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_4_6_row_0_0_1 : (right1Middle4 4 6) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn446.rows_inverseACB HexagonRowColumn446.cols_right0) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_4_6_row_0_0_2 : (right1Middle4 4 6) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn446.rows_inverseACB HexagonRowColumn446.cols_right0) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_4_6_row_0_0_3 : (right1Middle4 4 6) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn446.rows_inverseACB HexagonRowColumn446.cols_right0) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_4_6_row_0_1_0 : (right1Middle4 4 6) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn446.rows_inverseACB HexagonRowColumn446.cols_right0) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_4_6_row_0_1_1 : (right1Middle4 4 6) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn446.rows_inverseACB HexagonRowColumn446.cols_right0) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_4_6_row_0_1_2 : (right1Middle4 4 6) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn446.rows_inverseACB HexagonRowColumn446.cols_right0) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_4_6_row_0_1_3 : (right1Middle4 4 6) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn446.rows_inverseACB HexagonRowColumn446.cols_right0) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_4_6_row_1_0_0 : (right1Middle4 4 6) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn446.rows_inverseACB HexagonRowColumn446.cols_right0) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_4_6_row_1_0_1 : (right1Middle4 4 6) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn446.rows_inverseACB HexagonRowColumn446.cols_right0) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_4_6_row_1_0_2 : (right1Middle4 4 6) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn446.rows_inverseACB HexagonRowColumn446.cols_right0) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_4_6_row_1_0_3 : (right1Middle4 4 6) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn446.rows_inverseACB HexagonRowColumn446.cols_right0) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_4_6_row_1_1_0 : (right1Middle4 4 6) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn446.rows_inverseACB HexagonRowColumn446.cols_right0) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_4_6_row_1_1_1 : (right1Middle4 4 6) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn446.rows_inverseACB HexagonRowColumn446.cols_right0) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_4_6_row_1_1_2 : (right1Middle4 4 6) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn446.rows_inverseACB HexagonRowColumn446.cols_right0) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_4_6_row_1_1_3 : (right1Middle4 4 6) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn446.rows_inverseACB HexagonRowColumn446.cols_right0) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_4_6_checked : right1Middle4 4 6 = rowColumnMul HexagonRowColumn446.rows_inverseACB HexagonRowColumn446.cols_right0 := by
  funext r
  fin_cases r
  · exact right1Middle4_eq_case_4_6_row_0_0_0
  · exact right1Middle4_eq_case_4_6_row_0_0_1
  · exact right1Middle4_eq_case_4_6_row_0_0_2
  · exact right1Middle4_eq_case_4_6_row_0_0_3
  · exact right1Middle4_eq_case_4_6_row_0_1_0
  · exact right1Middle4_eq_case_4_6_row_0_1_1
  · exact right1Middle4_eq_case_4_6_row_0_1_2
  · exact right1Middle4_eq_case_4_6_row_0_1_3
  · exact right1Middle4_eq_case_4_6_row_1_0_0
  · exact right1Middle4_eq_case_4_6_row_1_0_1
  · exact right1Middle4_eq_case_4_6_row_1_0_2
  · exact right1Middle4_eq_case_4_6_row_1_0_3
  · exact right1Middle4_eq_case_4_6_row_1_1_0
  · exact right1Middle4_eq_case_4_6_row_1_1_1
  · exact right1Middle4_eq_case_4_6_row_1_1_2
  · exact right1Middle4_eq_case_4_6_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem right1Middle4_eq_case_4_6 : right1Middle4 4 6 = associatorInverseZ 4 6 4 * right0Middle4 4 6 := by
  simpa only [HexagonAtoms446.assocABC_eq,
    HexagonAtoms446.outerABC_eq,
    HexagonAtoms446.assocBAC_eq,
    HexagonAtoms446.innerABC_eq,
    HexagonAtoms446.innerRightABC_eq,
    HexagonAtoms446.inverseACB_eq,
    HexagonAtoms446.innerACB_eq,
    HexagonAtoms446.assocBCA_eq,
    HexagonAtoms446.innerRightBAC_eq,
    HexagonAtoms446.assocCAB_eq,
    HexagonAtoms446.outerLeftABC_eq,
    HexagonRowColumn446.assocBAC_alias,
    HexagonRowColumn446.innerRightBAC_alias,
    HexagonRowColumn446.product0_eq,
    HexagonRowColumn446.product1_eq,
    HexagonRowColumn446.product2_eq,
    HexagonRowColumn446.product3_eq,
    HexagonRowColumn446.product4_eq,
    HexagonRowColumn446.product5_eq,
    HexagonRowColumn446.product6_eq,
    HexagonRowColumn446.product7_eq] using right1Middle4_eq_case_4_6_checked

private theorem right2Middle4_eq_case_4_6_row_0_0_0 : (right2Middle4 4 6) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (right1Middle4 4 6) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_4_6_row_0_0_1 : (right2Middle4 4 6) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (right1Middle4 4 6) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_4_6_row_0_0_2 : (right2Middle4 4 6) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (right1Middle4 4 6) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_4_6_row_0_0_3 : (right2Middle4 4 6) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (right1Middle4 4 6) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_4_6_row_0_1_0 : (right2Middle4 4 6) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (right1Middle4 4 6) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_4_6_row_0_1_1 : (right2Middle4 4 6) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (right1Middle4 4 6) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_4_6_row_0_1_2 : (right2Middle4 4 6) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (right1Middle4 4 6) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_4_6_row_0_1_3 : (right2Middle4 4 6) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (right1Middle4 4 6) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_4_6_row_1_0_0 : (right2Middle4 4 6) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (right1Middle4 4 6) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_4_6_row_1_0_1 : (right2Middle4 4 6) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (right1Middle4 4 6) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_4_6_row_1_0_2 : (right2Middle4 4 6) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (right1Middle4 4 6) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_4_6_row_1_0_3 : (right2Middle4 4 6) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (right1Middle4 4 6) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_4_6_row_1_1_0 : (right2Middle4 4 6) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (right1Middle4 4 6) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_4_6_row_1_1_1 : (right2Middle4 4 6) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (right1Middle4 4 6) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_4_6_row_1_1_2 : (right2Middle4 4 6) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (right1Middle4 4 6) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_4_6_row_1_1_3 : (right2Middle4 4 6) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (right1Middle4 4 6) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_4_6_checked : right2Middle4 4 6 = right1Middle4 4 6 := by
  funext r
  fin_cases r
  · exact right2Middle4_eq_case_4_6_row_0_0_0
  · exact right2Middle4_eq_case_4_6_row_0_0_1
  · exact right2Middle4_eq_case_4_6_row_0_0_2
  · exact right2Middle4_eq_case_4_6_row_0_0_3
  · exact right2Middle4_eq_case_4_6_row_0_1_0
  · exact right2Middle4_eq_case_4_6_row_0_1_1
  · exact right2Middle4_eq_case_4_6_row_0_1_2
  · exact right2Middle4_eq_case_4_6_row_0_1_3
  · exact right2Middle4_eq_case_4_6_row_1_0_0
  · exact right2Middle4_eq_case_4_6_row_1_0_1
  · exact right2Middle4_eq_case_4_6_row_1_0_2
  · exact right2Middle4_eq_case_4_6_row_1_0_3
  · exact right2Middle4_eq_case_4_6_row_1_1_0
  · exact right2Middle4_eq_case_4_6_row_1_1_1
  · exact right2Middle4_eq_case_4_6_row_1_1_2
  · exact right2Middle4_eq_case_4_6_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem right2Middle4_eq_case_4_6 : right2Middle4 4 6 = innerLeftZ 4 6 4 * right1Middle4 4 6 := by
  simpa only [HexagonAtoms446.assocABC_eq,
    HexagonAtoms446.outerABC_eq,
    HexagonAtoms446.assocBAC_eq,
    HexagonAtoms446.innerABC_eq,
    HexagonAtoms446.innerRightABC_eq,
    HexagonAtoms446.inverseACB_eq,
    HexagonAtoms446.innerACB_eq,
    HexagonAtoms446.assocBCA_eq,
    HexagonAtoms446.innerRightBAC_eq,
    HexagonAtoms446.assocCAB_eq,
    HexagonAtoms446.outerLeftABC_eq,
    HexagonRowColumn446.assocBAC_alias,
    HexagonRowColumn446.innerRightBAC_alias,
    HexagonRowColumn446.product0_eq,
    HexagonRowColumn446.product1_eq,
    HexagonRowColumn446.product2_eq,
    HexagonRowColumn446.product3_eq,
    HexagonRowColumn446.product4_eq,
    HexagonRowColumn446.product5_eq,
    HexagonRowColumn446.product6_eq,
    HexagonRowColumn446.product7_eq] using right2Middle4_eq_case_4_6_checked

private theorem leftFinal4_case_4_6_row_0_0_0 : (((-1 : ℤ) ^ (leftScaleBit 4 4 6).val * positiveScale (leftScaleExponent 4 4 6)) •
      (rowColumnMul HexagonRowColumn446.rows_assocBCA HexagonRowColumn446.cols_left0)) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 4 4 6) • (left1Middle4 4 6)) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal4_case_4_6_row_0_0_1 : (((-1 : ℤ) ^ (leftScaleBit 4 4 6).val * positiveScale (leftScaleExponent 4 4 6)) •
      (rowColumnMul HexagonRowColumn446.rows_assocBCA HexagonRowColumn446.cols_left0)) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 4 4 6) • (left1Middle4 4 6)) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal4_case_4_6_row_0_0_2 : (((-1 : ℤ) ^ (leftScaleBit 4 4 6).val * positiveScale (leftScaleExponent 4 4 6)) •
      (rowColumnMul HexagonRowColumn446.rows_assocBCA HexagonRowColumn446.cols_left0)) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 4 4 6) • (left1Middle4 4 6)) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal4_case_4_6_row_0_0_3 : (((-1 : ℤ) ^ (leftScaleBit 4 4 6).val * positiveScale (leftScaleExponent 4 4 6)) •
      (rowColumnMul HexagonRowColumn446.rows_assocBCA HexagonRowColumn446.cols_left0)) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 4 4 6) • (left1Middle4 4 6)) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal4_case_4_6_row_0_1_0 : (((-1 : ℤ) ^ (leftScaleBit 4 4 6).val * positiveScale (leftScaleExponent 4 4 6)) •
      (rowColumnMul HexagonRowColumn446.rows_assocBCA HexagonRowColumn446.cols_left0)) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 4 4 6) • (left1Middle4 4 6)) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal4_case_4_6_row_0_1_1 : (((-1 : ℤ) ^ (leftScaleBit 4 4 6).val * positiveScale (leftScaleExponent 4 4 6)) •
      (rowColumnMul HexagonRowColumn446.rows_assocBCA HexagonRowColumn446.cols_left0)) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 4 4 6) • (left1Middle4 4 6)) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal4_case_4_6_row_0_1_2 : (((-1 : ℤ) ^ (leftScaleBit 4 4 6).val * positiveScale (leftScaleExponent 4 4 6)) •
      (rowColumnMul HexagonRowColumn446.rows_assocBCA HexagonRowColumn446.cols_left0)) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 4 4 6) • (left1Middle4 4 6)) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal4_case_4_6_row_0_1_3 : (((-1 : ℤ) ^ (leftScaleBit 4 4 6).val * positiveScale (leftScaleExponent 4 4 6)) •
      (rowColumnMul HexagonRowColumn446.rows_assocBCA HexagonRowColumn446.cols_left0)) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 4 4 6) • (left1Middle4 4 6)) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal4_case_4_6_row_1_0_0 : (((-1 : ℤ) ^ (leftScaleBit 4 4 6).val * positiveScale (leftScaleExponent 4 4 6)) •
      (rowColumnMul HexagonRowColumn446.rows_assocBCA HexagonRowColumn446.cols_left0)) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 4 4 6) • (left1Middle4 4 6)) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal4_case_4_6_row_1_0_1 : (((-1 : ℤ) ^ (leftScaleBit 4 4 6).val * positiveScale (leftScaleExponent 4 4 6)) •
      (rowColumnMul HexagonRowColumn446.rows_assocBCA HexagonRowColumn446.cols_left0)) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 4 4 6) • (left1Middle4 4 6)) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal4_case_4_6_row_1_0_2 : (((-1 : ℤ) ^ (leftScaleBit 4 4 6).val * positiveScale (leftScaleExponent 4 4 6)) •
      (rowColumnMul HexagonRowColumn446.rows_assocBCA HexagonRowColumn446.cols_left0)) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 4 4 6) • (left1Middle4 4 6)) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal4_case_4_6_row_1_0_3 : (((-1 : ℤ) ^ (leftScaleBit 4 4 6).val * positiveScale (leftScaleExponent 4 4 6)) •
      (rowColumnMul HexagonRowColumn446.rows_assocBCA HexagonRowColumn446.cols_left0)) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 4 4 6) • (left1Middle4 4 6)) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal4_case_4_6_row_1_1_0 : (((-1 : ℤ) ^ (leftScaleBit 4 4 6).val * positiveScale (leftScaleExponent 4 4 6)) •
      (rowColumnMul HexagonRowColumn446.rows_assocBCA HexagonRowColumn446.cols_left0)) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 4 4 6) • (left1Middle4 4 6)) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal4_case_4_6_row_1_1_1 : (((-1 : ℤ) ^ (leftScaleBit 4 4 6).val * positiveScale (leftScaleExponent 4 4 6)) •
      (rowColumnMul HexagonRowColumn446.rows_assocBCA HexagonRowColumn446.cols_left0)) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 4 4 6) • (left1Middle4 4 6)) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal4_case_4_6_row_1_1_2 : (((-1 : ℤ) ^ (leftScaleBit 4 4 6).val * positiveScale (leftScaleExponent 4 4 6)) •
      (rowColumnMul HexagonRowColumn446.rows_assocBCA HexagonRowColumn446.cols_left0)) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 4 4 6) • (left1Middle4 4 6)) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal4_case_4_6_row_1_1_3 : (((-1 : ℤ) ^ (leftScaleBit 4 4 6).val * positiveScale (leftScaleExponent 4 4 6)) •
      (rowColumnMul HexagonRowColumn446.rows_assocBCA HexagonRowColumn446.cols_left0)) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 4 4 6) • (left1Middle4 4 6)) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal4_case_4_6_checked : ((-1 : ℤ) ^ (leftScaleBit 4 4 6).val * positiveScale (leftScaleExponent 4 4 6)) •
      (rowColumnMul HexagonRowColumn446.rows_assocBCA HexagonRowColumn446.cols_left0) = negativeScale (leftScaleExponent 4 4 6) • (left1Middle4 4 6) := by
  funext r
  fin_cases r
  · exact leftFinal4_case_4_6_row_0_0_0
  · exact leftFinal4_case_4_6_row_0_0_1
  · exact leftFinal4_case_4_6_row_0_0_2
  · exact leftFinal4_case_4_6_row_0_0_3
  · exact leftFinal4_case_4_6_row_0_1_0
  · exact leftFinal4_case_4_6_row_0_1_1
  · exact leftFinal4_case_4_6_row_0_1_2
  · exact leftFinal4_case_4_6_row_0_1_3
  · exact leftFinal4_case_4_6_row_1_0_0
  · exact leftFinal4_case_4_6_row_1_0_1
  · exact leftFinal4_case_4_6_row_1_0_2
  · exact leftFinal4_case_4_6_row_1_0_3
  · exact leftFinal4_case_4_6_row_1_1_0
  · exact leftFinal4_case_4_6_row_1_1_1
  · exact leftFinal4_case_4_6_row_1_1_2
  · exact leftFinal4_case_4_6_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem leftFinal4_case_4_6 : ((-1 : ℤ) ^ (leftScaleBit 4 4 6).val * positiveScale (leftScaleExponent 4 4 6)) •
      (associatorZ 4 6 4 * left0Middle4 4 6) = negativeScale (leftScaleExponent 4 4 6) • (innerRightZ 4 4 6 * left1Middle4 4 6) := by
  simpa only [HexagonAtoms446.assocABC_eq,
    HexagonAtoms446.outerABC_eq,
    HexagonAtoms446.assocBAC_eq,
    HexagonAtoms446.innerABC_eq,
    HexagonAtoms446.innerRightABC_eq,
    HexagonAtoms446.inverseACB_eq,
    HexagonAtoms446.innerACB_eq,
    HexagonAtoms446.assocBCA_eq,
    HexagonAtoms446.innerRightBAC_eq,
    HexagonAtoms446.assocCAB_eq,
    HexagonAtoms446.outerLeftABC_eq,
    HexagonRowColumn446.assocBAC_alias,
    HexagonRowColumn446.innerRightBAC_alias,
    HexagonRowColumn446.product0_eq,
    HexagonRowColumn446.product1_eq,
    HexagonRowColumn446.product2_eq,
    HexagonRowColumn446.product3_eq,
    HexagonRowColumn446.product4_eq,
    HexagonRowColumn446.product5_eq,
    HexagonRowColumn446.product6_eq,
    HexagonRowColumn446.product7_eq] using leftFinal4_case_4_6_checked

private theorem rightFinal4_case_4_6_row_0_0_0 : (((-1 : ℤ) ^ (rightScaleBit 4 4 6).val * positiveScale (rightScaleExponent 4 4 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 6 4 : ℤ)) • HexagonAtoms446.outerLeftABC) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (negativeScale (rightScaleExponent 4 4 6) • (rowColumnMul HexagonRowColumn446.rows_assocCAB HexagonRowColumn446.cols_right2)) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal4_case_4_6_row_0_0_1 : (((-1 : ℤ) ^ (rightScaleBit 4 4 6).val * positiveScale (rightScaleExponent 4 4 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 6 4 : ℤ)) • HexagonAtoms446.outerLeftABC) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (negativeScale (rightScaleExponent 4 4 6) • (rowColumnMul HexagonRowColumn446.rows_assocCAB HexagonRowColumn446.cols_right2)) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal4_case_4_6_row_0_0_2 : (((-1 : ℤ) ^ (rightScaleBit 4 4 6).val * positiveScale (rightScaleExponent 4 4 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 6 4 : ℤ)) • HexagonAtoms446.outerLeftABC) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (negativeScale (rightScaleExponent 4 4 6) • (rowColumnMul HexagonRowColumn446.rows_assocCAB HexagonRowColumn446.cols_right2)) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal4_case_4_6_row_0_0_3 : (((-1 : ℤ) ^ (rightScaleBit 4 4 6).val * positiveScale (rightScaleExponent 4 4 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 6 4 : ℤ)) • HexagonAtoms446.outerLeftABC) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (negativeScale (rightScaleExponent 4 4 6) • (rowColumnMul HexagonRowColumn446.rows_assocCAB HexagonRowColumn446.cols_right2)) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal4_case_4_6_row_1_0_0 : (((-1 : ℤ) ^ (rightScaleBit 4 4 6).val * positiveScale (rightScaleExponent 4 4 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 6 4 : ℤ)) • HexagonAtoms446.outerLeftABC) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (negativeScale (rightScaleExponent 4 4 6) • (rowColumnMul HexagonRowColumn446.rows_assocCAB HexagonRowColumn446.cols_right2)) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal4_case_4_6_row_1_0_1 : (((-1 : ℤ) ^ (rightScaleBit 4 4 6).val * positiveScale (rightScaleExponent 4 4 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 6 4 : ℤ)) • HexagonAtoms446.outerLeftABC) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (negativeScale (rightScaleExponent 4 4 6) • (rowColumnMul HexagonRowColumn446.rows_assocCAB HexagonRowColumn446.cols_right2)) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal4_case_4_6_row_1_0_2 : (((-1 : ℤ) ^ (rightScaleBit 4 4 6).val * positiveScale (rightScaleExponent 4 4 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 6 4 : ℤ)) • HexagonAtoms446.outerLeftABC) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (negativeScale (rightScaleExponent 4 4 6) • (rowColumnMul HexagonRowColumn446.rows_assocCAB HexagonRowColumn446.cols_right2)) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal4_case_4_6_row_1_0_3 : (((-1 : ℤ) ^ (rightScaleBit 4 4 6).val * positiveScale (rightScaleExponent 4 4 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 6 4 : ℤ)) • HexagonAtoms446.outerLeftABC) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (negativeScale (rightScaleExponent 4 4 6) • (rowColumnMul HexagonRowColumn446.rows_assocCAB HexagonRowColumn446.cols_right2)) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal4_case_4_6_row_2_0_0 : (((-1 : ℤ) ^ (rightScaleBit 4 4 6).val * positiveScale (rightScaleExponent 4 4 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 6 4 : ℤ)) • HexagonAtoms446.outerLeftABC) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (negativeScale (rightScaleExponent 4 4 6) • (rowColumnMul HexagonRowColumn446.rows_assocCAB HexagonRowColumn446.cols_right2)) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal4_case_4_6_row_2_0_1 : (((-1 : ℤ) ^ (rightScaleBit 4 4 6).val * positiveScale (rightScaleExponent 4 4 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 6 4 : ℤ)) • HexagonAtoms446.outerLeftABC) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (negativeScale (rightScaleExponent 4 4 6) • (rowColumnMul HexagonRowColumn446.rows_assocCAB HexagonRowColumn446.cols_right2)) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal4_case_4_6_row_2_0_2 : (((-1 : ℤ) ^ (rightScaleBit 4 4 6).val * positiveScale (rightScaleExponent 4 4 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 6 4 : ℤ)) • HexagonAtoms446.outerLeftABC) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (negativeScale (rightScaleExponent 4 4 6) • (rowColumnMul HexagonRowColumn446.rows_assocCAB HexagonRowColumn446.cols_right2)) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal4_case_4_6_row_2_0_3 : (((-1 : ℤ) ^ (rightScaleBit 4 4 6).val * positiveScale (rightScaleExponent 4 4 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 6 4 : ℤ)) • HexagonAtoms446.outerLeftABC) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (negativeScale (rightScaleExponent 4 4 6) • (rowColumnMul HexagonRowColumn446.rows_assocCAB HexagonRowColumn446.cols_right2)) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal4_case_4_6_row_3_0_0 : (((-1 : ℤ) ^ (rightScaleBit 4 4 6).val * positiveScale (rightScaleExponent 4 4 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 6 4 : ℤ)) • HexagonAtoms446.outerLeftABC) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (negativeScale (rightScaleExponent 4 4 6) • (rowColumnMul HexagonRowColumn446.rows_assocCAB HexagonRowColumn446.cols_right2)) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal4_case_4_6_row_3_0_1 : (((-1 : ℤ) ^ (rightScaleBit 4 4 6).val * positiveScale (rightScaleExponent 4 4 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 6 4 : ℤ)) • HexagonAtoms446.outerLeftABC) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (negativeScale (rightScaleExponent 4 4 6) • (rowColumnMul HexagonRowColumn446.rows_assocCAB HexagonRowColumn446.cols_right2)) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal4_case_4_6_row_3_0_2 : (((-1 : ℤ) ^ (rightScaleBit 4 4 6).val * positiveScale (rightScaleExponent 4 4 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 6 4 : ℤ)) • HexagonAtoms446.outerLeftABC) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (negativeScale (rightScaleExponent 4 4 6) • (rowColumnMul HexagonRowColumn446.rows_assocCAB HexagonRowColumn446.cols_right2)) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal4_case_4_6_row_3_0_3 : (((-1 : ℤ) ^ (rightScaleBit 4 4 6).val * positiveScale (rightScaleExponent 4 4 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 6 4 : ℤ)) • HexagonAtoms446.outerLeftABC) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (negativeScale (rightScaleExponent 4 4 6) • (rowColumnMul HexagonRowColumn446.rows_assocCAB HexagonRowColumn446.cols_right2)) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal4_case_4_6_checked : ((-1 : ℤ) ^ (rightScaleBit 4 4 6).val * positiveScale (rightScaleExponent 4 4 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 6 4 : ℤ)) • HexagonAtoms446.outerLeftABC = negativeScale (rightScaleExponent 4 4 6) • (rowColumnMul HexagonRowColumn446.rows_assocCAB HexagonRowColumn446.cols_right2) := by
  funext r
  fin_cases r
  · exact rightFinal4_case_4_6_row_0_0_0
  · exact rightFinal4_case_4_6_row_0_0_1
  · exact rightFinal4_case_4_6_row_0_0_2
  · exact rightFinal4_case_4_6_row_0_0_3
  · exact rightFinal4_case_4_6_row_1_0_0
  · exact rightFinal4_case_4_6_row_1_0_1
  · exact rightFinal4_case_4_6_row_1_0_2
  · exact rightFinal4_case_4_6_row_1_0_3
  · exact rightFinal4_case_4_6_row_2_0_0
  · exact rightFinal4_case_4_6_row_2_0_1
  · exact rightFinal4_case_4_6_row_2_0_2
  · exact rightFinal4_case_4_6_row_2_0_3
  · exact rightFinal4_case_4_6_row_3_0_0
  · exact rightFinal4_case_4_6_row_3_0_1
  · exact rightFinal4_case_4_6_row_3_0_2
  · exact rightFinal4_case_4_6_row_3_0_3

set_option backward.isDefEq.respectTransparency false in
theorem rightFinal4_case_4_6 : ((-1 : ℤ) ^ (rightScaleBit 4 4 6).val * positiveScale (rightScaleExponent 4 4 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 6 4 : ℤ)) • outerLeftZ 4 4 6 = negativeScale (rightScaleExponent 4 4 6) • (associatorZ 6 4 4 * right2Middle4 4 6) := by
  simpa only [HexagonAtoms446.assocABC_eq,
    HexagonAtoms446.outerABC_eq,
    HexagonAtoms446.assocBAC_eq,
    HexagonAtoms446.innerABC_eq,
    HexagonAtoms446.innerRightABC_eq,
    HexagonAtoms446.inverseACB_eq,
    HexagonAtoms446.innerACB_eq,
    HexagonAtoms446.assocBCA_eq,
    HexagonAtoms446.innerRightBAC_eq,
    HexagonAtoms446.assocCAB_eq,
    HexagonAtoms446.outerLeftABC_eq,
    HexagonRowColumn446.assocBAC_alias,
    HexagonRowColumn446.innerRightBAC_alias,
    HexagonRowColumn446.product0_eq,
    HexagonRowColumn446.product1_eq,
    HexagonRowColumn446.product2_eq,
    HexagonRowColumn446.product3_eq,
    HexagonRowColumn446.product4_eq,
    HexagonRowColumn446.product5_eq,
    HexagonRowColumn446.product6_eq,
    HexagonRowColumn446.product7_eq] using rightFinal4_case_4_6_checked

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonCases4
