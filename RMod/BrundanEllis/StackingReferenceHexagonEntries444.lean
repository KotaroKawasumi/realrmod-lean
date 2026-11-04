import RMod.BrundanEllis.StackingReferenceHexagonMiddle4
import RMod.BrundanEllis.StackingReferenceSparseMatrixCheck
import RMod.BrundanEllis.StackingReferenceHexagonAtoms444
import RMod.BrundanEllis.StackingReferenceHexagonRowColumn444

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

private theorem left0Middle4_eq_case_4_4_row_0_0_0 : (left0Middle4 4 4) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms444.assocABC) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_4_4_row_0_0_1 : (left0Middle4 4 4) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms444.assocABC) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_4_4_row_0_0_2 : (left0Middle4 4 4) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms444.assocABC) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_4_4_row_0_0_3 : (left0Middle4 4 4) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms444.assocABC) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_4_4_row_1_0_0 : (left0Middle4 4 4) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms444.assocABC) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_4_4_row_1_0_1 : (left0Middle4 4 4) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms444.assocABC) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_4_4_row_1_0_2 : (left0Middle4 4 4) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms444.assocABC) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_4_4_row_1_0_3 : (left0Middle4 4 4) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms444.assocABC) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_4_4_row_2_0_0 : (left0Middle4 4 4) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms444.assocABC) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_4_4_row_2_0_1 : (left0Middle4 4 4) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms444.assocABC) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_4_4_row_2_0_2 : (left0Middle4 4 4) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms444.assocABC) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_4_4_row_2_0_3 : (left0Middle4 4 4) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms444.assocABC) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_4_4_row_3_0_0 : (left0Middle4 4 4) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms444.assocABC) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_4_4_row_3_0_1 : (left0Middle4 4 4) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms444.assocABC) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_4_4_row_3_0_2 : (left0Middle4 4 4) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms444.assocABC) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_4_4_row_3_0_3 : (left0Middle4 4 4) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms444.assocABC) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_4_4_checked : left0Middle4 4 4 = HexagonAtoms444.assocABC := by
  funext r
  fin_cases r
  · exact left0Middle4_eq_case_4_4_row_0_0_0
  · exact left0Middle4_eq_case_4_4_row_0_0_1
  · exact left0Middle4_eq_case_4_4_row_0_0_2
  · exact left0Middle4_eq_case_4_4_row_0_0_3
  · exact left0Middle4_eq_case_4_4_row_1_0_0
  · exact left0Middle4_eq_case_4_4_row_1_0_1
  · exact left0Middle4_eq_case_4_4_row_1_0_2
  · exact left0Middle4_eq_case_4_4_row_1_0_3
  · exact left0Middle4_eq_case_4_4_row_2_0_0
  · exact left0Middle4_eq_case_4_4_row_2_0_1
  · exact left0Middle4_eq_case_4_4_row_2_0_2
  · exact left0Middle4_eq_case_4_4_row_2_0_3
  · exact left0Middle4_eq_case_4_4_row_3_0_0
  · exact left0Middle4_eq_case_4_4_row_3_0_1
  · exact left0Middle4_eq_case_4_4_row_3_0_2
  · exact left0Middle4_eq_case_4_4_row_3_0_3

set_option backward.isDefEq.respectTransparency false in
theorem left0Middle4_eq_case_4_4 : left0Middle4 4 4 = outerRightZ 4 4 4 * associatorZ 4 4 4 := by
  simpa only [HexagonAtoms444.assocABC_eq,
    HexagonAtoms444.outerABC_eq,
    HexagonAtoms444.assocBAC_eq,
    HexagonAtoms444.innerABC_eq,
    HexagonAtoms444.innerRightABC_eq,
    HexagonAtoms444.inverseACB_eq,
    HexagonAtoms444.innerACB_eq,
    HexagonAtoms444.assocBCA_eq,
    HexagonAtoms444.innerRightBAC_eq,
    HexagonAtoms444.assocCAB_eq,
    HexagonAtoms444.outerLeftABC_eq,
    HexagonRowColumn444.assocBAC_alias,
    HexagonRowColumn444.innerACB_alias,
    HexagonRowColumn444.assocBCA_alias,
    HexagonRowColumn444.innerRightBAC_alias,
    HexagonRowColumn444.assocCAB_alias,
    HexagonRowColumn444.product0_eq,
    HexagonRowColumn444.product1_eq,
    HexagonRowColumn444.product2_eq,
    HexagonRowColumn444.product3_eq,
    HexagonRowColumn444.product4_eq,
    HexagonRowColumn444.product5_eq,
    HexagonRowColumn444.product6_eq,
    HexagonRowColumn444.product7_eq] using left0Middle4_eq_case_4_4_checked

private theorem left1Middle4_eq_case_4_4_row_0_0_0 : (left1Middle4 4 4) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn444.rows_assocABC HexagonRowColumn444.cols_innerABC) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_4_4_row_0_0_1 : (left1Middle4 4 4) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn444.rows_assocABC HexagonRowColumn444.cols_innerABC) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_4_4_row_0_0_2 : (left1Middle4 4 4) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn444.rows_assocABC HexagonRowColumn444.cols_innerABC) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_4_4_row_0_0_3 : (left1Middle4 4 4) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn444.rows_assocABC HexagonRowColumn444.cols_innerABC) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_4_4_row_1_0_0 : (left1Middle4 4 4) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn444.rows_assocABC HexagonRowColumn444.cols_innerABC) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_4_4_row_1_0_1 : (left1Middle4 4 4) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn444.rows_assocABC HexagonRowColumn444.cols_innerABC) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_4_4_row_1_0_2 : (left1Middle4 4 4) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn444.rows_assocABC HexagonRowColumn444.cols_innerABC) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_4_4_row_1_0_3 : (left1Middle4 4 4) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn444.rows_assocABC HexagonRowColumn444.cols_innerABC) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_4_4_row_2_0_0 : (left1Middle4 4 4) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn444.rows_assocABC HexagonRowColumn444.cols_innerABC) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_4_4_row_2_0_1 : (left1Middle4 4 4) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn444.rows_assocABC HexagonRowColumn444.cols_innerABC) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_4_4_row_2_0_2 : (left1Middle4 4 4) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn444.rows_assocABC HexagonRowColumn444.cols_innerABC) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_4_4_row_2_0_3 : (left1Middle4 4 4) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn444.rows_assocABC HexagonRowColumn444.cols_innerABC) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_4_4_row_3_0_0 : (left1Middle4 4 4) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn444.rows_assocABC HexagonRowColumn444.cols_innerABC) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_4_4_row_3_0_1 : (left1Middle4 4 4) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn444.rows_assocABC HexagonRowColumn444.cols_innerABC) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_4_4_row_3_0_2 : (left1Middle4 4 4) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn444.rows_assocABC HexagonRowColumn444.cols_innerABC) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_4_4_row_3_0_3 : (left1Middle4 4 4) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn444.rows_assocABC HexagonRowColumn444.cols_innerABC) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_4_4_checked : left1Middle4 4 4 = rowColumnMul HexagonRowColumn444.rows_assocABC HexagonRowColumn444.cols_innerABC := by
  funext r
  fin_cases r
  · exact left1Middle4_eq_case_4_4_row_0_0_0
  · exact left1Middle4_eq_case_4_4_row_0_0_1
  · exact left1Middle4_eq_case_4_4_row_0_0_2
  · exact left1Middle4_eq_case_4_4_row_0_0_3
  · exact left1Middle4_eq_case_4_4_row_1_0_0
  · exact left1Middle4_eq_case_4_4_row_1_0_1
  · exact left1Middle4_eq_case_4_4_row_1_0_2
  · exact left1Middle4_eq_case_4_4_row_1_0_3
  · exact left1Middle4_eq_case_4_4_row_2_0_0
  · exact left1Middle4_eq_case_4_4_row_2_0_1
  · exact left1Middle4_eq_case_4_4_row_2_0_2
  · exact left1Middle4_eq_case_4_4_row_2_0_3
  · exact left1Middle4_eq_case_4_4_row_3_0_0
  · exact left1Middle4_eq_case_4_4_row_3_0_1
  · exact left1Middle4_eq_case_4_4_row_3_0_2
  · exact left1Middle4_eq_case_4_4_row_3_0_3

set_option backward.isDefEq.respectTransparency false in
theorem left1Middle4_eq_case_4_4 : left1Middle4 4 4 = associatorZ 4 4 4 * innerLeftZ 4 4 4 := by
  simpa only [HexagonAtoms444.assocABC_eq,
    HexagonAtoms444.outerABC_eq,
    HexagonAtoms444.assocBAC_eq,
    HexagonAtoms444.innerABC_eq,
    HexagonAtoms444.innerRightABC_eq,
    HexagonAtoms444.inverseACB_eq,
    HexagonAtoms444.innerACB_eq,
    HexagonAtoms444.assocBCA_eq,
    HexagonAtoms444.innerRightBAC_eq,
    HexagonAtoms444.assocCAB_eq,
    HexagonAtoms444.outerLeftABC_eq,
    HexagonRowColumn444.assocBAC_alias,
    HexagonRowColumn444.innerACB_alias,
    HexagonRowColumn444.assocBCA_alias,
    HexagonRowColumn444.innerRightBAC_alias,
    HexagonRowColumn444.assocCAB_alias,
    HexagonRowColumn444.product0_eq,
    HexagonRowColumn444.product1_eq,
    HexagonRowColumn444.product2_eq,
    HexagonRowColumn444.product3_eq,
    HexagonRowColumn444.product4_eq,
    HexagonRowColumn444.product5_eq,
    HexagonRowColumn444.product6_eq,
    HexagonRowColumn444.product7_eq] using left1Middle4_eq_case_4_4_checked

private theorem right0Middle4_eq_case_4_4_row_0_0_0 : (right0Middle4 4 4) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn444.rows_innerRightABC HexagonRowColumn444.cols_assocABC) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_4_4_row_0_0_1 : (right0Middle4 4 4) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn444.rows_innerRightABC HexagonRowColumn444.cols_assocABC) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_4_4_row_0_0_2 : (right0Middle4 4 4) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn444.rows_innerRightABC HexagonRowColumn444.cols_assocABC) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_4_4_row_0_0_3 : (right0Middle4 4 4) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn444.rows_innerRightABC HexagonRowColumn444.cols_assocABC) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_4_4_row_1_0_0 : (right0Middle4 4 4) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn444.rows_innerRightABC HexagonRowColumn444.cols_assocABC) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_4_4_row_1_0_1 : (right0Middle4 4 4) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn444.rows_innerRightABC HexagonRowColumn444.cols_assocABC) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_4_4_row_1_0_2 : (right0Middle4 4 4) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn444.rows_innerRightABC HexagonRowColumn444.cols_assocABC) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_4_4_row_1_0_3 : (right0Middle4 4 4) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn444.rows_innerRightABC HexagonRowColumn444.cols_assocABC) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_4_4_row_2_0_0 : (right0Middle4 4 4) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn444.rows_innerRightABC HexagonRowColumn444.cols_assocABC) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_4_4_row_2_0_1 : (right0Middle4 4 4) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn444.rows_innerRightABC HexagonRowColumn444.cols_assocABC) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_4_4_row_2_0_2 : (right0Middle4 4 4) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn444.rows_innerRightABC HexagonRowColumn444.cols_assocABC) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_4_4_row_2_0_3 : (right0Middle4 4 4) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn444.rows_innerRightABC HexagonRowColumn444.cols_assocABC) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_4_4_row_3_0_0 : (right0Middle4 4 4) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn444.rows_innerRightABC HexagonRowColumn444.cols_assocABC) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_4_4_row_3_0_1 : (right0Middle4 4 4) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn444.rows_innerRightABC HexagonRowColumn444.cols_assocABC) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_4_4_row_3_0_2 : (right0Middle4 4 4) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn444.rows_innerRightABC HexagonRowColumn444.cols_assocABC) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_4_4_row_3_0_3 : (right0Middle4 4 4) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn444.rows_innerRightABC HexagonRowColumn444.cols_assocABC) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_4_4_checked : right0Middle4 4 4 = rowColumnMul HexagonRowColumn444.rows_innerRightABC HexagonRowColumn444.cols_assocABC := by
  funext r
  fin_cases r
  · exact right0Middle4_eq_case_4_4_row_0_0_0
  · exact right0Middle4_eq_case_4_4_row_0_0_1
  · exact right0Middle4_eq_case_4_4_row_0_0_2
  · exact right0Middle4_eq_case_4_4_row_0_0_3
  · exact right0Middle4_eq_case_4_4_row_1_0_0
  · exact right0Middle4_eq_case_4_4_row_1_0_1
  · exact right0Middle4_eq_case_4_4_row_1_0_2
  · exact right0Middle4_eq_case_4_4_row_1_0_3
  · exact right0Middle4_eq_case_4_4_row_2_0_0
  · exact right0Middle4_eq_case_4_4_row_2_0_1
  · exact right0Middle4_eq_case_4_4_row_2_0_2
  · exact right0Middle4_eq_case_4_4_row_2_0_3
  · exact right0Middle4_eq_case_4_4_row_3_0_0
  · exact right0Middle4_eq_case_4_4_row_3_0_1
  · exact right0Middle4_eq_case_4_4_row_3_0_2
  · exact right0Middle4_eq_case_4_4_row_3_0_3

set_option backward.isDefEq.respectTransparency false in
theorem right0Middle4_eq_case_4_4 : right0Middle4 4 4 = innerRightZ 4 4 4 * associatorZ 4 4 4 := by
  simpa only [HexagonAtoms444.assocABC_eq,
    HexagonAtoms444.outerABC_eq,
    HexagonAtoms444.assocBAC_eq,
    HexagonAtoms444.innerABC_eq,
    HexagonAtoms444.innerRightABC_eq,
    HexagonAtoms444.inverseACB_eq,
    HexagonAtoms444.innerACB_eq,
    HexagonAtoms444.assocBCA_eq,
    HexagonAtoms444.innerRightBAC_eq,
    HexagonAtoms444.assocCAB_eq,
    HexagonAtoms444.outerLeftABC_eq,
    HexagonRowColumn444.assocBAC_alias,
    HexagonRowColumn444.innerACB_alias,
    HexagonRowColumn444.assocBCA_alias,
    HexagonRowColumn444.innerRightBAC_alias,
    HexagonRowColumn444.assocCAB_alias,
    HexagonRowColumn444.product0_eq,
    HexagonRowColumn444.product1_eq,
    HexagonRowColumn444.product2_eq,
    HexagonRowColumn444.product3_eq,
    HexagonRowColumn444.product4_eq,
    HexagonRowColumn444.product5_eq,
    HexagonRowColumn444.product6_eq,
    HexagonRowColumn444.product7_eq] using right0Middle4_eq_case_4_4_checked

private theorem right1Middle4_eq_case_4_4_row_0_0_0 : (right1Middle4 4 4) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn444.rows_inverseACB HexagonRowColumn444.cols_right0) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_4_4_row_0_0_1 : (right1Middle4 4 4) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn444.rows_inverseACB HexagonRowColumn444.cols_right0) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_4_4_row_0_0_2 : (right1Middle4 4 4) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn444.rows_inverseACB HexagonRowColumn444.cols_right0) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_4_4_row_0_0_3 : (right1Middle4 4 4) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn444.rows_inverseACB HexagonRowColumn444.cols_right0) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_4_4_row_1_0_0 : (right1Middle4 4 4) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn444.rows_inverseACB HexagonRowColumn444.cols_right0) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_4_4_row_1_0_1 : (right1Middle4 4 4) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn444.rows_inverseACB HexagonRowColumn444.cols_right0) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_4_4_row_1_0_2 : (right1Middle4 4 4) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn444.rows_inverseACB HexagonRowColumn444.cols_right0) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_4_4_row_1_0_3 : (right1Middle4 4 4) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn444.rows_inverseACB HexagonRowColumn444.cols_right0) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_4_4_row_2_0_0 : (right1Middle4 4 4) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn444.rows_inverseACB HexagonRowColumn444.cols_right0) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_4_4_row_2_0_1 : (right1Middle4 4 4) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn444.rows_inverseACB HexagonRowColumn444.cols_right0) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_4_4_row_2_0_2 : (right1Middle4 4 4) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn444.rows_inverseACB HexagonRowColumn444.cols_right0) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_4_4_row_2_0_3 : (right1Middle4 4 4) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn444.rows_inverseACB HexagonRowColumn444.cols_right0) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_4_4_row_3_0_0 : (right1Middle4 4 4) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn444.rows_inverseACB HexagonRowColumn444.cols_right0) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_4_4_row_3_0_1 : (right1Middle4 4 4) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn444.rows_inverseACB HexagonRowColumn444.cols_right0) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_4_4_row_3_0_2 : (right1Middle4 4 4) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn444.rows_inverseACB HexagonRowColumn444.cols_right0) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_4_4_row_3_0_3 : (right1Middle4 4 4) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn444.rows_inverseACB HexagonRowColumn444.cols_right0) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_4_4_checked : right1Middle4 4 4 = rowColumnMul HexagonRowColumn444.rows_inverseACB HexagonRowColumn444.cols_right0 := by
  funext r
  fin_cases r
  · exact right1Middle4_eq_case_4_4_row_0_0_0
  · exact right1Middle4_eq_case_4_4_row_0_0_1
  · exact right1Middle4_eq_case_4_4_row_0_0_2
  · exact right1Middle4_eq_case_4_4_row_0_0_3
  · exact right1Middle4_eq_case_4_4_row_1_0_0
  · exact right1Middle4_eq_case_4_4_row_1_0_1
  · exact right1Middle4_eq_case_4_4_row_1_0_2
  · exact right1Middle4_eq_case_4_4_row_1_0_3
  · exact right1Middle4_eq_case_4_4_row_2_0_0
  · exact right1Middle4_eq_case_4_4_row_2_0_1
  · exact right1Middle4_eq_case_4_4_row_2_0_2
  · exact right1Middle4_eq_case_4_4_row_2_0_3
  · exact right1Middle4_eq_case_4_4_row_3_0_0
  · exact right1Middle4_eq_case_4_4_row_3_0_1
  · exact right1Middle4_eq_case_4_4_row_3_0_2
  · exact right1Middle4_eq_case_4_4_row_3_0_3

set_option backward.isDefEq.respectTransparency false in
theorem right1Middle4_eq_case_4_4 : right1Middle4 4 4 = associatorInverseZ 4 4 4 * right0Middle4 4 4 := by
  simpa only [HexagonAtoms444.assocABC_eq,
    HexagonAtoms444.outerABC_eq,
    HexagonAtoms444.assocBAC_eq,
    HexagonAtoms444.innerABC_eq,
    HexagonAtoms444.innerRightABC_eq,
    HexagonAtoms444.inverseACB_eq,
    HexagonAtoms444.innerACB_eq,
    HexagonAtoms444.assocBCA_eq,
    HexagonAtoms444.innerRightBAC_eq,
    HexagonAtoms444.assocCAB_eq,
    HexagonAtoms444.outerLeftABC_eq,
    HexagonRowColumn444.assocBAC_alias,
    HexagonRowColumn444.innerACB_alias,
    HexagonRowColumn444.assocBCA_alias,
    HexagonRowColumn444.innerRightBAC_alias,
    HexagonRowColumn444.assocCAB_alias,
    HexagonRowColumn444.product0_eq,
    HexagonRowColumn444.product1_eq,
    HexagonRowColumn444.product2_eq,
    HexagonRowColumn444.product3_eq,
    HexagonRowColumn444.product4_eq,
    HexagonRowColumn444.product5_eq,
    HexagonRowColumn444.product6_eq,
    HexagonRowColumn444.product7_eq] using right1Middle4_eq_case_4_4_checked

private theorem right2Middle4_eq_case_4_4_row_0_0_0 : (right2Middle4 4 4) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn444.rows_innerABC HexagonRowColumn444.cols_right1) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_4_4_row_0_0_1 : (right2Middle4 4 4) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn444.rows_innerABC HexagonRowColumn444.cols_right1) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_4_4_row_0_0_2 : (right2Middle4 4 4) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn444.rows_innerABC HexagonRowColumn444.cols_right1) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_4_4_row_0_0_3 : (right2Middle4 4 4) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn444.rows_innerABC HexagonRowColumn444.cols_right1) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_4_4_row_1_0_0 : (right2Middle4 4 4) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn444.rows_innerABC HexagonRowColumn444.cols_right1) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_4_4_row_1_0_1 : (right2Middle4 4 4) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn444.rows_innerABC HexagonRowColumn444.cols_right1) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_4_4_row_1_0_2 : (right2Middle4 4 4) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn444.rows_innerABC HexagonRowColumn444.cols_right1) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_4_4_row_1_0_3 : (right2Middle4 4 4) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn444.rows_innerABC HexagonRowColumn444.cols_right1) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_4_4_row_2_0_0 : (right2Middle4 4 4) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn444.rows_innerABC HexagonRowColumn444.cols_right1) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_4_4_row_2_0_1 : (right2Middle4 4 4) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn444.rows_innerABC HexagonRowColumn444.cols_right1) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_4_4_row_2_0_2 : (right2Middle4 4 4) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn444.rows_innerABC HexagonRowColumn444.cols_right1) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_4_4_row_2_0_3 : (right2Middle4 4 4) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn444.rows_innerABC HexagonRowColumn444.cols_right1) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_4_4_row_3_0_0 : (right2Middle4 4 4) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn444.rows_innerABC HexagonRowColumn444.cols_right1) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_4_4_row_3_0_1 : (right2Middle4 4 4) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn444.rows_innerABC HexagonRowColumn444.cols_right1) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_4_4_row_3_0_2 : (right2Middle4 4 4) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn444.rows_innerABC HexagonRowColumn444.cols_right1) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_4_4_row_3_0_3 : (right2Middle4 4 4) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn444.rows_innerABC HexagonRowColumn444.cols_right1) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_4_4_checked : right2Middle4 4 4 = rowColumnMul HexagonRowColumn444.rows_innerABC HexagonRowColumn444.cols_right1 := by
  funext r
  fin_cases r
  · exact right2Middle4_eq_case_4_4_row_0_0_0
  · exact right2Middle4_eq_case_4_4_row_0_0_1
  · exact right2Middle4_eq_case_4_4_row_0_0_2
  · exact right2Middle4_eq_case_4_4_row_0_0_3
  · exact right2Middle4_eq_case_4_4_row_1_0_0
  · exact right2Middle4_eq_case_4_4_row_1_0_1
  · exact right2Middle4_eq_case_4_4_row_1_0_2
  · exact right2Middle4_eq_case_4_4_row_1_0_3
  · exact right2Middle4_eq_case_4_4_row_2_0_0
  · exact right2Middle4_eq_case_4_4_row_2_0_1
  · exact right2Middle4_eq_case_4_4_row_2_0_2
  · exact right2Middle4_eq_case_4_4_row_2_0_3
  · exact right2Middle4_eq_case_4_4_row_3_0_0
  · exact right2Middle4_eq_case_4_4_row_3_0_1
  · exact right2Middle4_eq_case_4_4_row_3_0_2
  · exact right2Middle4_eq_case_4_4_row_3_0_3

set_option backward.isDefEq.respectTransparency false in
theorem right2Middle4_eq_case_4_4 : right2Middle4 4 4 = innerLeftZ 4 4 4 * right1Middle4 4 4 := by
  simpa only [HexagonAtoms444.assocABC_eq,
    HexagonAtoms444.outerABC_eq,
    HexagonAtoms444.assocBAC_eq,
    HexagonAtoms444.innerABC_eq,
    HexagonAtoms444.innerRightABC_eq,
    HexagonAtoms444.inverseACB_eq,
    HexagonAtoms444.innerACB_eq,
    HexagonAtoms444.assocBCA_eq,
    HexagonAtoms444.innerRightBAC_eq,
    HexagonAtoms444.assocCAB_eq,
    HexagonAtoms444.outerLeftABC_eq,
    HexagonRowColumn444.assocBAC_alias,
    HexagonRowColumn444.innerACB_alias,
    HexagonRowColumn444.assocBCA_alias,
    HexagonRowColumn444.innerRightBAC_alias,
    HexagonRowColumn444.assocCAB_alias,
    HexagonRowColumn444.product0_eq,
    HexagonRowColumn444.product1_eq,
    HexagonRowColumn444.product2_eq,
    HexagonRowColumn444.product3_eq,
    HexagonRowColumn444.product4_eq,
    HexagonRowColumn444.product5_eq,
    HexagonRowColumn444.product6_eq,
    HexagonRowColumn444.product7_eq] using right2Middle4_eq_case_4_4_checked

private theorem leftFinal4_case_4_4_row_0_0_0 : (((-1 : ℤ) ^ (leftScaleBit 4 4 4).val * positiveScale (leftScaleExponent 4 4 4)) •
      (rowColumnMul HexagonRowColumn444.rows_assocABC HexagonRowColumn444.cols_left0)) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (negativeScale (leftScaleExponent 4 4 4) • (rowColumnMul HexagonRowColumn444.rows_innerRightABC HexagonRowColumn444.cols_left1)) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal4_case_4_4_row_0_0_1 : (((-1 : ℤ) ^ (leftScaleBit 4 4 4).val * positiveScale (leftScaleExponent 4 4 4)) •
      (rowColumnMul HexagonRowColumn444.rows_assocABC HexagonRowColumn444.cols_left0)) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (negativeScale (leftScaleExponent 4 4 4) • (rowColumnMul HexagonRowColumn444.rows_innerRightABC HexagonRowColumn444.cols_left1)) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal4_case_4_4_row_0_0_2 : (((-1 : ℤ) ^ (leftScaleBit 4 4 4).val * positiveScale (leftScaleExponent 4 4 4)) •
      (rowColumnMul HexagonRowColumn444.rows_assocABC HexagonRowColumn444.cols_left0)) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (negativeScale (leftScaleExponent 4 4 4) • (rowColumnMul HexagonRowColumn444.rows_innerRightABC HexagonRowColumn444.cols_left1)) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal4_case_4_4_row_0_0_3 : (((-1 : ℤ) ^ (leftScaleBit 4 4 4).val * positiveScale (leftScaleExponent 4 4 4)) •
      (rowColumnMul HexagonRowColumn444.rows_assocABC HexagonRowColumn444.cols_left0)) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (negativeScale (leftScaleExponent 4 4 4) • (rowColumnMul HexagonRowColumn444.rows_innerRightABC HexagonRowColumn444.cols_left1)) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal4_case_4_4_row_1_0_0 : (((-1 : ℤ) ^ (leftScaleBit 4 4 4).val * positiveScale (leftScaleExponent 4 4 4)) •
      (rowColumnMul HexagonRowColumn444.rows_assocABC HexagonRowColumn444.cols_left0)) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (negativeScale (leftScaleExponent 4 4 4) • (rowColumnMul HexagonRowColumn444.rows_innerRightABC HexagonRowColumn444.cols_left1)) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal4_case_4_4_row_1_0_1 : (((-1 : ℤ) ^ (leftScaleBit 4 4 4).val * positiveScale (leftScaleExponent 4 4 4)) •
      (rowColumnMul HexagonRowColumn444.rows_assocABC HexagonRowColumn444.cols_left0)) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (negativeScale (leftScaleExponent 4 4 4) • (rowColumnMul HexagonRowColumn444.rows_innerRightABC HexagonRowColumn444.cols_left1)) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal4_case_4_4_row_1_0_2 : (((-1 : ℤ) ^ (leftScaleBit 4 4 4).val * positiveScale (leftScaleExponent 4 4 4)) •
      (rowColumnMul HexagonRowColumn444.rows_assocABC HexagonRowColumn444.cols_left0)) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (negativeScale (leftScaleExponent 4 4 4) • (rowColumnMul HexagonRowColumn444.rows_innerRightABC HexagonRowColumn444.cols_left1)) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal4_case_4_4_row_1_0_3 : (((-1 : ℤ) ^ (leftScaleBit 4 4 4).val * positiveScale (leftScaleExponent 4 4 4)) •
      (rowColumnMul HexagonRowColumn444.rows_assocABC HexagonRowColumn444.cols_left0)) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (negativeScale (leftScaleExponent 4 4 4) • (rowColumnMul HexagonRowColumn444.rows_innerRightABC HexagonRowColumn444.cols_left1)) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal4_case_4_4_row_2_0_0 : (((-1 : ℤ) ^ (leftScaleBit 4 4 4).val * positiveScale (leftScaleExponent 4 4 4)) •
      (rowColumnMul HexagonRowColumn444.rows_assocABC HexagonRowColumn444.cols_left0)) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (negativeScale (leftScaleExponent 4 4 4) • (rowColumnMul HexagonRowColumn444.rows_innerRightABC HexagonRowColumn444.cols_left1)) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal4_case_4_4_row_2_0_1 : (((-1 : ℤ) ^ (leftScaleBit 4 4 4).val * positiveScale (leftScaleExponent 4 4 4)) •
      (rowColumnMul HexagonRowColumn444.rows_assocABC HexagonRowColumn444.cols_left0)) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (negativeScale (leftScaleExponent 4 4 4) • (rowColumnMul HexagonRowColumn444.rows_innerRightABC HexagonRowColumn444.cols_left1)) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal4_case_4_4_row_2_0_2 : (((-1 : ℤ) ^ (leftScaleBit 4 4 4).val * positiveScale (leftScaleExponent 4 4 4)) •
      (rowColumnMul HexagonRowColumn444.rows_assocABC HexagonRowColumn444.cols_left0)) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (negativeScale (leftScaleExponent 4 4 4) • (rowColumnMul HexagonRowColumn444.rows_innerRightABC HexagonRowColumn444.cols_left1)) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal4_case_4_4_row_2_0_3 : (((-1 : ℤ) ^ (leftScaleBit 4 4 4).val * positiveScale (leftScaleExponent 4 4 4)) •
      (rowColumnMul HexagonRowColumn444.rows_assocABC HexagonRowColumn444.cols_left0)) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (negativeScale (leftScaleExponent 4 4 4) • (rowColumnMul HexagonRowColumn444.rows_innerRightABC HexagonRowColumn444.cols_left1)) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal4_case_4_4_row_3_0_0 : (((-1 : ℤ) ^ (leftScaleBit 4 4 4).val * positiveScale (leftScaleExponent 4 4 4)) •
      (rowColumnMul HexagonRowColumn444.rows_assocABC HexagonRowColumn444.cols_left0)) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (negativeScale (leftScaleExponent 4 4 4) • (rowColumnMul HexagonRowColumn444.rows_innerRightABC HexagonRowColumn444.cols_left1)) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal4_case_4_4_row_3_0_1 : (((-1 : ℤ) ^ (leftScaleBit 4 4 4).val * positiveScale (leftScaleExponent 4 4 4)) •
      (rowColumnMul HexagonRowColumn444.rows_assocABC HexagonRowColumn444.cols_left0)) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (negativeScale (leftScaleExponent 4 4 4) • (rowColumnMul HexagonRowColumn444.rows_innerRightABC HexagonRowColumn444.cols_left1)) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal4_case_4_4_row_3_0_2 : (((-1 : ℤ) ^ (leftScaleBit 4 4 4).val * positiveScale (leftScaleExponent 4 4 4)) •
      (rowColumnMul HexagonRowColumn444.rows_assocABC HexagonRowColumn444.cols_left0)) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (negativeScale (leftScaleExponent 4 4 4) • (rowColumnMul HexagonRowColumn444.rows_innerRightABC HexagonRowColumn444.cols_left1)) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal4_case_4_4_row_3_0_3 : (((-1 : ℤ) ^ (leftScaleBit 4 4 4).val * positiveScale (leftScaleExponent 4 4 4)) •
      (rowColumnMul HexagonRowColumn444.rows_assocABC HexagonRowColumn444.cols_left0)) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (negativeScale (leftScaleExponent 4 4 4) • (rowColumnMul HexagonRowColumn444.rows_innerRightABC HexagonRowColumn444.cols_left1)) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal4_case_4_4_checked : ((-1 : ℤ) ^ (leftScaleBit 4 4 4).val * positiveScale (leftScaleExponent 4 4 4)) •
      (rowColumnMul HexagonRowColumn444.rows_assocABC HexagonRowColumn444.cols_left0) = negativeScale (leftScaleExponent 4 4 4) • (rowColumnMul HexagonRowColumn444.rows_innerRightABC HexagonRowColumn444.cols_left1) := by
  funext r
  fin_cases r
  · exact leftFinal4_case_4_4_row_0_0_0
  · exact leftFinal4_case_4_4_row_0_0_1
  · exact leftFinal4_case_4_4_row_0_0_2
  · exact leftFinal4_case_4_4_row_0_0_3
  · exact leftFinal4_case_4_4_row_1_0_0
  · exact leftFinal4_case_4_4_row_1_0_1
  · exact leftFinal4_case_4_4_row_1_0_2
  · exact leftFinal4_case_4_4_row_1_0_3
  · exact leftFinal4_case_4_4_row_2_0_0
  · exact leftFinal4_case_4_4_row_2_0_1
  · exact leftFinal4_case_4_4_row_2_0_2
  · exact leftFinal4_case_4_4_row_2_0_3
  · exact leftFinal4_case_4_4_row_3_0_0
  · exact leftFinal4_case_4_4_row_3_0_1
  · exact leftFinal4_case_4_4_row_3_0_2
  · exact leftFinal4_case_4_4_row_3_0_3

set_option backward.isDefEq.respectTransparency false in
theorem leftFinal4_case_4_4 : ((-1 : ℤ) ^ (leftScaleBit 4 4 4).val * positiveScale (leftScaleExponent 4 4 4)) •
      (associatorZ 4 4 4 * left0Middle4 4 4) = negativeScale (leftScaleExponent 4 4 4) • (innerRightZ 4 4 4 * left1Middle4 4 4) := by
  simpa only [HexagonAtoms444.assocABC_eq,
    HexagonAtoms444.outerABC_eq,
    HexagonAtoms444.assocBAC_eq,
    HexagonAtoms444.innerABC_eq,
    HexagonAtoms444.innerRightABC_eq,
    HexagonAtoms444.inverseACB_eq,
    HexagonAtoms444.innerACB_eq,
    HexagonAtoms444.assocBCA_eq,
    HexagonAtoms444.innerRightBAC_eq,
    HexagonAtoms444.assocCAB_eq,
    HexagonAtoms444.outerLeftABC_eq,
    HexagonRowColumn444.assocBAC_alias,
    HexagonRowColumn444.innerACB_alias,
    HexagonRowColumn444.assocBCA_alias,
    HexagonRowColumn444.innerRightBAC_alias,
    HexagonRowColumn444.assocCAB_alias,
    HexagonRowColumn444.product0_eq,
    HexagonRowColumn444.product1_eq,
    HexagonRowColumn444.product2_eq,
    HexagonRowColumn444.product3_eq,
    HexagonRowColumn444.product4_eq,
    HexagonRowColumn444.product5_eq,
    HexagonRowColumn444.product6_eq,
    HexagonRowColumn444.product7_eq] using leftFinal4_case_4_4_checked

private theorem rightFinal4_case_4_4_row_0_0_0 : (((-1 : ℤ) ^ (rightScaleBit 4 4 4).val * positiveScale (rightScaleExponent 4 4 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 4 4 : ℤ)) • HexagonAtoms444.outerLeftABC) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (negativeScale (rightScaleExponent 4 4 4) • (rowColumnMul HexagonRowColumn444.rows_assocABC HexagonRowColumn444.cols_right2)) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal4_case_4_4_row_0_0_1 : (((-1 : ℤ) ^ (rightScaleBit 4 4 4).val * positiveScale (rightScaleExponent 4 4 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 4 4 : ℤ)) • HexagonAtoms444.outerLeftABC) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (negativeScale (rightScaleExponent 4 4 4) • (rowColumnMul HexagonRowColumn444.rows_assocABC HexagonRowColumn444.cols_right2)) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal4_case_4_4_row_0_0_2 : (((-1 : ℤ) ^ (rightScaleBit 4 4 4).val * positiveScale (rightScaleExponent 4 4 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 4 4 : ℤ)) • HexagonAtoms444.outerLeftABC) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (negativeScale (rightScaleExponent 4 4 4) • (rowColumnMul HexagonRowColumn444.rows_assocABC HexagonRowColumn444.cols_right2)) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal4_case_4_4_row_0_0_3 : (((-1 : ℤ) ^ (rightScaleBit 4 4 4).val * positiveScale (rightScaleExponent 4 4 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 4 4 : ℤ)) • HexagonAtoms444.outerLeftABC) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (negativeScale (rightScaleExponent 4 4 4) • (rowColumnMul HexagonRowColumn444.rows_assocABC HexagonRowColumn444.cols_right2)) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal4_case_4_4_row_1_0_0 : (((-1 : ℤ) ^ (rightScaleBit 4 4 4).val * positiveScale (rightScaleExponent 4 4 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 4 4 : ℤ)) • HexagonAtoms444.outerLeftABC) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (negativeScale (rightScaleExponent 4 4 4) • (rowColumnMul HexagonRowColumn444.rows_assocABC HexagonRowColumn444.cols_right2)) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal4_case_4_4_row_1_0_1 : (((-1 : ℤ) ^ (rightScaleBit 4 4 4).val * positiveScale (rightScaleExponent 4 4 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 4 4 : ℤ)) • HexagonAtoms444.outerLeftABC) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (negativeScale (rightScaleExponent 4 4 4) • (rowColumnMul HexagonRowColumn444.rows_assocABC HexagonRowColumn444.cols_right2)) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal4_case_4_4_row_1_0_2 : (((-1 : ℤ) ^ (rightScaleBit 4 4 4).val * positiveScale (rightScaleExponent 4 4 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 4 4 : ℤ)) • HexagonAtoms444.outerLeftABC) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (negativeScale (rightScaleExponent 4 4 4) • (rowColumnMul HexagonRowColumn444.rows_assocABC HexagonRowColumn444.cols_right2)) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal4_case_4_4_row_1_0_3 : (((-1 : ℤ) ^ (rightScaleBit 4 4 4).val * positiveScale (rightScaleExponent 4 4 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 4 4 : ℤ)) • HexagonAtoms444.outerLeftABC) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (negativeScale (rightScaleExponent 4 4 4) • (rowColumnMul HexagonRowColumn444.rows_assocABC HexagonRowColumn444.cols_right2)) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal4_case_4_4_row_2_0_0 : (((-1 : ℤ) ^ (rightScaleBit 4 4 4).val * positiveScale (rightScaleExponent 4 4 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 4 4 : ℤ)) • HexagonAtoms444.outerLeftABC) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (negativeScale (rightScaleExponent 4 4 4) • (rowColumnMul HexagonRowColumn444.rows_assocABC HexagonRowColumn444.cols_right2)) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal4_case_4_4_row_2_0_1 : (((-1 : ℤ) ^ (rightScaleBit 4 4 4).val * positiveScale (rightScaleExponent 4 4 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 4 4 : ℤ)) • HexagonAtoms444.outerLeftABC) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (negativeScale (rightScaleExponent 4 4 4) • (rowColumnMul HexagonRowColumn444.rows_assocABC HexagonRowColumn444.cols_right2)) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal4_case_4_4_row_2_0_2 : (((-1 : ℤ) ^ (rightScaleBit 4 4 4).val * positiveScale (rightScaleExponent 4 4 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 4 4 : ℤ)) • HexagonAtoms444.outerLeftABC) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (negativeScale (rightScaleExponent 4 4 4) • (rowColumnMul HexagonRowColumn444.rows_assocABC HexagonRowColumn444.cols_right2)) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal4_case_4_4_row_2_0_3 : (((-1 : ℤ) ^ (rightScaleBit 4 4 4).val * positiveScale (rightScaleExponent 4 4 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 4 4 : ℤ)) • HexagonAtoms444.outerLeftABC) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (negativeScale (rightScaleExponent 4 4 4) • (rowColumnMul HexagonRowColumn444.rows_assocABC HexagonRowColumn444.cols_right2)) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal4_case_4_4_row_3_0_0 : (((-1 : ℤ) ^ (rightScaleBit 4 4 4).val * positiveScale (rightScaleExponent 4 4 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 4 4 : ℤ)) • HexagonAtoms444.outerLeftABC) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (negativeScale (rightScaleExponent 4 4 4) • (rowColumnMul HexagonRowColumn444.rows_assocABC HexagonRowColumn444.cols_right2)) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal4_case_4_4_row_3_0_1 : (((-1 : ℤ) ^ (rightScaleBit 4 4 4).val * positiveScale (rightScaleExponent 4 4 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 4 4 : ℤ)) • HexagonAtoms444.outerLeftABC) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (negativeScale (rightScaleExponent 4 4 4) • (rowColumnMul HexagonRowColumn444.rows_assocABC HexagonRowColumn444.cols_right2)) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal4_case_4_4_row_3_0_2 : (((-1 : ℤ) ^ (rightScaleBit 4 4 4).val * positiveScale (rightScaleExponent 4 4 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 4 4 : ℤ)) • HexagonAtoms444.outerLeftABC) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (negativeScale (rightScaleExponent 4 4 4) • (rowColumnMul HexagonRowColumn444.rows_assocABC HexagonRowColumn444.cols_right2)) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal4_case_4_4_row_3_0_3 : (((-1 : ℤ) ^ (rightScaleBit 4 4 4).val * positiveScale (rightScaleExponent 4 4 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 4 4 : ℤ)) • HexagonAtoms444.outerLeftABC) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (negativeScale (rightScaleExponent 4 4 4) • (rowColumnMul HexagonRowColumn444.rows_assocABC HexagonRowColumn444.cols_right2)) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal4_case_4_4_checked : ((-1 : ℤ) ^ (rightScaleBit 4 4 4).val * positiveScale (rightScaleExponent 4 4 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 4 4 : ℤ)) • HexagonAtoms444.outerLeftABC = negativeScale (rightScaleExponent 4 4 4) • (rowColumnMul HexagonRowColumn444.rows_assocABC HexagonRowColumn444.cols_right2) := by
  funext r
  fin_cases r
  · exact rightFinal4_case_4_4_row_0_0_0
  · exact rightFinal4_case_4_4_row_0_0_1
  · exact rightFinal4_case_4_4_row_0_0_2
  · exact rightFinal4_case_4_4_row_0_0_3
  · exact rightFinal4_case_4_4_row_1_0_0
  · exact rightFinal4_case_4_4_row_1_0_1
  · exact rightFinal4_case_4_4_row_1_0_2
  · exact rightFinal4_case_4_4_row_1_0_3
  · exact rightFinal4_case_4_4_row_2_0_0
  · exact rightFinal4_case_4_4_row_2_0_1
  · exact rightFinal4_case_4_4_row_2_0_2
  · exact rightFinal4_case_4_4_row_2_0_3
  · exact rightFinal4_case_4_4_row_3_0_0
  · exact rightFinal4_case_4_4_row_3_0_1
  · exact rightFinal4_case_4_4_row_3_0_2
  · exact rightFinal4_case_4_4_row_3_0_3

set_option backward.isDefEq.respectTransparency false in
theorem rightFinal4_case_4_4 : ((-1 : ℤ) ^ (rightScaleBit 4 4 4).val * positiveScale (rightScaleExponent 4 4 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 4 4 : ℤ)) • outerLeftZ 4 4 4 = negativeScale (rightScaleExponent 4 4 4) • (associatorZ 4 4 4 * right2Middle4 4 4) := by
  simpa only [HexagonAtoms444.assocABC_eq,
    HexagonAtoms444.outerABC_eq,
    HexagonAtoms444.assocBAC_eq,
    HexagonAtoms444.innerABC_eq,
    HexagonAtoms444.innerRightABC_eq,
    HexagonAtoms444.inverseACB_eq,
    HexagonAtoms444.innerACB_eq,
    HexagonAtoms444.assocBCA_eq,
    HexagonAtoms444.innerRightBAC_eq,
    HexagonAtoms444.assocCAB_eq,
    HexagonAtoms444.outerLeftABC_eq,
    HexagonRowColumn444.assocBAC_alias,
    HexagonRowColumn444.innerACB_alias,
    HexagonRowColumn444.assocBCA_alias,
    HexagonRowColumn444.innerRightBAC_alias,
    HexagonRowColumn444.assocCAB_alias,
    HexagonRowColumn444.product0_eq,
    HexagonRowColumn444.product1_eq,
    HexagonRowColumn444.product2_eq,
    HexagonRowColumn444.product3_eq,
    HexagonRowColumn444.product4_eq,
    HexagonRowColumn444.product5_eq,
    HexagonRowColumn444.product6_eq,
    HexagonRowColumn444.product7_eq] using rightFinal4_case_4_4_checked

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonCases4
