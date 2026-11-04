import RMod.BrundanEllis.StackingReferenceHexagonMiddle4
import RMod.BrundanEllis.StackingReferenceSparseMatrixCheck
import RMod.BrundanEllis.StackingReferenceHexagonAtoms442
import RMod.BrundanEllis.StackingReferenceHexagonRowColumn442

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

private theorem left0Middle4_eq_case_4_2_row_0_0_0 : (left0Middle4 4 2) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms442.assocABC) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_4_2_row_0_0_1 : (left0Middle4 4 2) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms442.assocABC) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_4_2_row_0_0_2 : (left0Middle4 4 2) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms442.assocABC) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_4_2_row_0_0_3 : (left0Middle4 4 2) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms442.assocABC) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_4_2_row_0_1_0 : (left0Middle4 4 2) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms442.assocABC) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_4_2_row_0_1_1 : (left0Middle4 4 2) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms442.assocABC) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_4_2_row_0_1_2 : (left0Middle4 4 2) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms442.assocABC) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_4_2_row_0_1_3 : (left0Middle4 4 2) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms442.assocABC) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_4_2_row_1_0_0 : (left0Middle4 4 2) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms442.assocABC) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_4_2_row_1_0_1 : (left0Middle4 4 2) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms442.assocABC) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_4_2_row_1_0_2 : (left0Middle4 4 2) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms442.assocABC) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_4_2_row_1_0_3 : (left0Middle4 4 2) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms442.assocABC) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_4_2_row_1_1_0 : (left0Middle4 4 2) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms442.assocABC) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_4_2_row_1_1_1 : (left0Middle4 4 2) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms442.assocABC) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_4_2_row_1_1_2 : (left0Middle4 4 2) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms442.assocABC) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_4_2_row_1_1_3 : (left0Middle4 4 2) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms442.assocABC) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_4_2_checked : left0Middle4 4 2 = HexagonAtoms442.assocABC := by
  funext r
  fin_cases r
  · exact left0Middle4_eq_case_4_2_row_0_0_0
  · exact left0Middle4_eq_case_4_2_row_0_0_1
  · exact left0Middle4_eq_case_4_2_row_0_0_2
  · exact left0Middle4_eq_case_4_2_row_0_0_3
  · exact left0Middle4_eq_case_4_2_row_0_1_0
  · exact left0Middle4_eq_case_4_2_row_0_1_1
  · exact left0Middle4_eq_case_4_2_row_0_1_2
  · exact left0Middle4_eq_case_4_2_row_0_1_3
  · exact left0Middle4_eq_case_4_2_row_1_0_0
  · exact left0Middle4_eq_case_4_2_row_1_0_1
  · exact left0Middle4_eq_case_4_2_row_1_0_2
  · exact left0Middle4_eq_case_4_2_row_1_0_3
  · exact left0Middle4_eq_case_4_2_row_1_1_0
  · exact left0Middle4_eq_case_4_2_row_1_1_1
  · exact left0Middle4_eq_case_4_2_row_1_1_2
  · exact left0Middle4_eq_case_4_2_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem left0Middle4_eq_case_4_2 : left0Middle4 4 2 = outerRightZ 4 4 2 * associatorZ 4 4 2 := by
  simpa only [HexagonAtoms442.assocABC_eq,
    HexagonAtoms442.outerABC_eq,
    HexagonAtoms442.assocBAC_eq,
    HexagonAtoms442.innerABC_eq,
    HexagonAtoms442.innerRightABC_eq,
    HexagonAtoms442.inverseACB_eq,
    HexagonAtoms442.innerACB_eq,
    HexagonAtoms442.assocBCA_eq,
    HexagonAtoms442.innerRightBAC_eq,
    HexagonAtoms442.assocCAB_eq,
    HexagonAtoms442.outerLeftABC_eq,
    HexagonRowColumn442.assocBAC_alias,
    HexagonRowColumn442.innerRightBAC_alias,
    HexagonRowColumn442.product0_eq,
    HexagonRowColumn442.product1_eq,
    HexagonRowColumn442.product2_eq,
    HexagonRowColumn442.product3_eq,
    HexagonRowColumn442.product4_eq,
    HexagonRowColumn442.product5_eq,
    HexagonRowColumn442.product6_eq,
    HexagonRowColumn442.product7_eq] using left0Middle4_eq_case_4_2_checked

private theorem left1Middle4_eq_case_4_2_row_0_0_0 : (left1Middle4 4 2) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn442.rows_assocABC HexagonRowColumn442.cols_innerABC) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_4_2_row_0_0_1 : (left1Middle4 4 2) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn442.rows_assocABC HexagonRowColumn442.cols_innerABC) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_4_2_row_0_0_2 : (left1Middle4 4 2) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn442.rows_assocABC HexagonRowColumn442.cols_innerABC) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_4_2_row_0_0_3 : (left1Middle4 4 2) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn442.rows_assocABC HexagonRowColumn442.cols_innerABC) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_4_2_row_0_1_0 : (left1Middle4 4 2) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn442.rows_assocABC HexagonRowColumn442.cols_innerABC) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_4_2_row_0_1_1 : (left1Middle4 4 2) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn442.rows_assocABC HexagonRowColumn442.cols_innerABC) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_4_2_row_0_1_2 : (left1Middle4 4 2) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn442.rows_assocABC HexagonRowColumn442.cols_innerABC) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_4_2_row_0_1_3 : (left1Middle4 4 2) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn442.rows_assocABC HexagonRowColumn442.cols_innerABC) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_4_2_row_1_0_0 : (left1Middle4 4 2) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn442.rows_assocABC HexagonRowColumn442.cols_innerABC) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_4_2_row_1_0_1 : (left1Middle4 4 2) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn442.rows_assocABC HexagonRowColumn442.cols_innerABC) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_4_2_row_1_0_2 : (left1Middle4 4 2) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn442.rows_assocABC HexagonRowColumn442.cols_innerABC) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_4_2_row_1_0_3 : (left1Middle4 4 2) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn442.rows_assocABC HexagonRowColumn442.cols_innerABC) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_4_2_row_1_1_0 : (left1Middle4 4 2) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn442.rows_assocABC HexagonRowColumn442.cols_innerABC) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_4_2_row_1_1_1 : (left1Middle4 4 2) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn442.rows_assocABC HexagonRowColumn442.cols_innerABC) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_4_2_row_1_1_2 : (left1Middle4 4 2) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn442.rows_assocABC HexagonRowColumn442.cols_innerABC) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_4_2_row_1_1_3 : (left1Middle4 4 2) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn442.rows_assocABC HexagonRowColumn442.cols_innerABC) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_4_2_checked : left1Middle4 4 2 = rowColumnMul HexagonRowColumn442.rows_assocABC HexagonRowColumn442.cols_innerABC := by
  funext r
  fin_cases r
  · exact left1Middle4_eq_case_4_2_row_0_0_0
  · exact left1Middle4_eq_case_4_2_row_0_0_1
  · exact left1Middle4_eq_case_4_2_row_0_0_2
  · exact left1Middle4_eq_case_4_2_row_0_0_3
  · exact left1Middle4_eq_case_4_2_row_0_1_0
  · exact left1Middle4_eq_case_4_2_row_0_1_1
  · exact left1Middle4_eq_case_4_2_row_0_1_2
  · exact left1Middle4_eq_case_4_2_row_0_1_3
  · exact left1Middle4_eq_case_4_2_row_1_0_0
  · exact left1Middle4_eq_case_4_2_row_1_0_1
  · exact left1Middle4_eq_case_4_2_row_1_0_2
  · exact left1Middle4_eq_case_4_2_row_1_0_3
  · exact left1Middle4_eq_case_4_2_row_1_1_0
  · exact left1Middle4_eq_case_4_2_row_1_1_1
  · exact left1Middle4_eq_case_4_2_row_1_1_2
  · exact left1Middle4_eq_case_4_2_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem left1Middle4_eq_case_4_2 : left1Middle4 4 2 = associatorZ 4 4 2 * innerLeftZ 4 4 2 := by
  simpa only [HexagonAtoms442.assocABC_eq,
    HexagonAtoms442.outerABC_eq,
    HexagonAtoms442.assocBAC_eq,
    HexagonAtoms442.innerABC_eq,
    HexagonAtoms442.innerRightABC_eq,
    HexagonAtoms442.inverseACB_eq,
    HexagonAtoms442.innerACB_eq,
    HexagonAtoms442.assocBCA_eq,
    HexagonAtoms442.innerRightBAC_eq,
    HexagonAtoms442.assocCAB_eq,
    HexagonAtoms442.outerLeftABC_eq,
    HexagonRowColumn442.assocBAC_alias,
    HexagonRowColumn442.innerRightBAC_alias,
    HexagonRowColumn442.product0_eq,
    HexagonRowColumn442.product1_eq,
    HexagonRowColumn442.product2_eq,
    HexagonRowColumn442.product3_eq,
    HexagonRowColumn442.product4_eq,
    HexagonRowColumn442.product5_eq,
    HexagonRowColumn442.product6_eq,
    HexagonRowColumn442.product7_eq] using left1Middle4_eq_case_4_2_checked

private theorem right0Middle4_eq_case_4_2_row_0_0_0 : (right0Middle4 4 2) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms442.assocABC) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_4_2_row_0_0_1 : (right0Middle4 4 2) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms442.assocABC) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_4_2_row_0_0_2 : (right0Middle4 4 2) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms442.assocABC) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_4_2_row_0_0_3 : (right0Middle4 4 2) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms442.assocABC) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_4_2_row_0_1_0 : (right0Middle4 4 2) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms442.assocABC) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_4_2_row_0_1_1 : (right0Middle4 4 2) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms442.assocABC) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_4_2_row_0_1_2 : (right0Middle4 4 2) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms442.assocABC) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_4_2_row_0_1_3 : (right0Middle4 4 2) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms442.assocABC) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_4_2_row_1_0_0 : (right0Middle4 4 2) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms442.assocABC) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_4_2_row_1_0_1 : (right0Middle4 4 2) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms442.assocABC) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_4_2_row_1_0_2 : (right0Middle4 4 2) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms442.assocABC) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_4_2_row_1_0_3 : (right0Middle4 4 2) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms442.assocABC) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_4_2_row_1_1_0 : (right0Middle4 4 2) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms442.assocABC) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_4_2_row_1_1_1 : (right0Middle4 4 2) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms442.assocABC) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_4_2_row_1_1_2 : (right0Middle4 4 2) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms442.assocABC) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_4_2_row_1_1_3 : (right0Middle4 4 2) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms442.assocABC) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_4_2_checked : right0Middle4 4 2 = HexagonAtoms442.assocABC := by
  funext r
  fin_cases r
  · exact right0Middle4_eq_case_4_2_row_0_0_0
  · exact right0Middle4_eq_case_4_2_row_0_0_1
  · exact right0Middle4_eq_case_4_2_row_0_0_2
  · exact right0Middle4_eq_case_4_2_row_0_0_3
  · exact right0Middle4_eq_case_4_2_row_0_1_0
  · exact right0Middle4_eq_case_4_2_row_0_1_1
  · exact right0Middle4_eq_case_4_2_row_0_1_2
  · exact right0Middle4_eq_case_4_2_row_0_1_3
  · exact right0Middle4_eq_case_4_2_row_1_0_0
  · exact right0Middle4_eq_case_4_2_row_1_0_1
  · exact right0Middle4_eq_case_4_2_row_1_0_2
  · exact right0Middle4_eq_case_4_2_row_1_0_3
  · exact right0Middle4_eq_case_4_2_row_1_1_0
  · exact right0Middle4_eq_case_4_2_row_1_1_1
  · exact right0Middle4_eq_case_4_2_row_1_1_2
  · exact right0Middle4_eq_case_4_2_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem right0Middle4_eq_case_4_2 : right0Middle4 4 2 = innerRightZ 4 4 2 * associatorZ 4 4 2 := by
  simpa only [HexagonAtoms442.assocABC_eq,
    HexagonAtoms442.outerABC_eq,
    HexagonAtoms442.assocBAC_eq,
    HexagonAtoms442.innerABC_eq,
    HexagonAtoms442.innerRightABC_eq,
    HexagonAtoms442.inverseACB_eq,
    HexagonAtoms442.innerACB_eq,
    HexagonAtoms442.assocBCA_eq,
    HexagonAtoms442.innerRightBAC_eq,
    HexagonAtoms442.assocCAB_eq,
    HexagonAtoms442.outerLeftABC_eq,
    HexagonRowColumn442.assocBAC_alias,
    HexagonRowColumn442.innerRightBAC_alias,
    HexagonRowColumn442.product0_eq,
    HexagonRowColumn442.product1_eq,
    HexagonRowColumn442.product2_eq,
    HexagonRowColumn442.product3_eq,
    HexagonRowColumn442.product4_eq,
    HexagonRowColumn442.product5_eq,
    HexagonRowColumn442.product6_eq,
    HexagonRowColumn442.product7_eq] using right0Middle4_eq_case_4_2_checked

private theorem right1Middle4_eq_case_4_2_row_0_0_0 : (right1Middle4 4 2) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn442.rows_inverseACB HexagonRowColumn442.cols_right0) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_4_2_row_0_0_1 : (right1Middle4 4 2) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn442.rows_inverseACB HexagonRowColumn442.cols_right0) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_4_2_row_0_0_2 : (right1Middle4 4 2) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn442.rows_inverseACB HexagonRowColumn442.cols_right0) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_4_2_row_0_0_3 : (right1Middle4 4 2) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn442.rows_inverseACB HexagonRowColumn442.cols_right0) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_4_2_row_0_1_0 : (right1Middle4 4 2) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn442.rows_inverseACB HexagonRowColumn442.cols_right0) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_4_2_row_0_1_1 : (right1Middle4 4 2) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn442.rows_inverseACB HexagonRowColumn442.cols_right0) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_4_2_row_0_1_2 : (right1Middle4 4 2) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn442.rows_inverseACB HexagonRowColumn442.cols_right0) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_4_2_row_0_1_3 : (right1Middle4 4 2) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn442.rows_inverseACB HexagonRowColumn442.cols_right0) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_4_2_row_1_0_0 : (right1Middle4 4 2) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn442.rows_inverseACB HexagonRowColumn442.cols_right0) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_4_2_row_1_0_1 : (right1Middle4 4 2) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn442.rows_inverseACB HexagonRowColumn442.cols_right0) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_4_2_row_1_0_2 : (right1Middle4 4 2) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn442.rows_inverseACB HexagonRowColumn442.cols_right0) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_4_2_row_1_0_3 : (right1Middle4 4 2) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn442.rows_inverseACB HexagonRowColumn442.cols_right0) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_4_2_row_1_1_0 : (right1Middle4 4 2) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn442.rows_inverseACB HexagonRowColumn442.cols_right0) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_4_2_row_1_1_1 : (right1Middle4 4 2) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn442.rows_inverseACB HexagonRowColumn442.cols_right0) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_4_2_row_1_1_2 : (right1Middle4 4 2) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn442.rows_inverseACB HexagonRowColumn442.cols_right0) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_4_2_row_1_1_3 : (right1Middle4 4 2) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn442.rows_inverseACB HexagonRowColumn442.cols_right0) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_4_2_checked : right1Middle4 4 2 = rowColumnMul HexagonRowColumn442.rows_inverseACB HexagonRowColumn442.cols_right0 := by
  funext r
  fin_cases r
  · exact right1Middle4_eq_case_4_2_row_0_0_0
  · exact right1Middle4_eq_case_4_2_row_0_0_1
  · exact right1Middle4_eq_case_4_2_row_0_0_2
  · exact right1Middle4_eq_case_4_2_row_0_0_3
  · exact right1Middle4_eq_case_4_2_row_0_1_0
  · exact right1Middle4_eq_case_4_2_row_0_1_1
  · exact right1Middle4_eq_case_4_2_row_0_1_2
  · exact right1Middle4_eq_case_4_2_row_0_1_3
  · exact right1Middle4_eq_case_4_2_row_1_0_0
  · exact right1Middle4_eq_case_4_2_row_1_0_1
  · exact right1Middle4_eq_case_4_2_row_1_0_2
  · exact right1Middle4_eq_case_4_2_row_1_0_3
  · exact right1Middle4_eq_case_4_2_row_1_1_0
  · exact right1Middle4_eq_case_4_2_row_1_1_1
  · exact right1Middle4_eq_case_4_2_row_1_1_2
  · exact right1Middle4_eq_case_4_2_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem right1Middle4_eq_case_4_2 : right1Middle4 4 2 = associatorInverseZ 4 2 4 * right0Middle4 4 2 := by
  simpa only [HexagonAtoms442.assocABC_eq,
    HexagonAtoms442.outerABC_eq,
    HexagonAtoms442.assocBAC_eq,
    HexagonAtoms442.innerABC_eq,
    HexagonAtoms442.innerRightABC_eq,
    HexagonAtoms442.inverseACB_eq,
    HexagonAtoms442.innerACB_eq,
    HexagonAtoms442.assocBCA_eq,
    HexagonAtoms442.innerRightBAC_eq,
    HexagonAtoms442.assocCAB_eq,
    HexagonAtoms442.outerLeftABC_eq,
    HexagonRowColumn442.assocBAC_alias,
    HexagonRowColumn442.innerRightBAC_alias,
    HexagonRowColumn442.product0_eq,
    HexagonRowColumn442.product1_eq,
    HexagonRowColumn442.product2_eq,
    HexagonRowColumn442.product3_eq,
    HexagonRowColumn442.product4_eq,
    HexagonRowColumn442.product5_eq,
    HexagonRowColumn442.product6_eq,
    HexagonRowColumn442.product7_eq] using right1Middle4_eq_case_4_2_checked

private theorem right2Middle4_eq_case_4_2_row_0_0_0 : (right2Middle4 4 2) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (right1Middle4 4 2) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_4_2_row_0_0_1 : (right2Middle4 4 2) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (right1Middle4 4 2) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_4_2_row_0_0_2 : (right2Middle4 4 2) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (right1Middle4 4 2) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_4_2_row_0_0_3 : (right2Middle4 4 2) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (right1Middle4 4 2) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_4_2_row_0_1_0 : (right2Middle4 4 2) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (right1Middle4 4 2) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_4_2_row_0_1_1 : (right2Middle4 4 2) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (right1Middle4 4 2) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_4_2_row_0_1_2 : (right2Middle4 4 2) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (right1Middle4 4 2) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_4_2_row_0_1_3 : (right2Middle4 4 2) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (right1Middle4 4 2) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_4_2_row_1_0_0 : (right2Middle4 4 2) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (right1Middle4 4 2) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_4_2_row_1_0_1 : (right2Middle4 4 2) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (right1Middle4 4 2) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_4_2_row_1_0_2 : (right2Middle4 4 2) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (right1Middle4 4 2) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_4_2_row_1_0_3 : (right2Middle4 4 2) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (right1Middle4 4 2) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_4_2_row_1_1_0 : (right2Middle4 4 2) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (right1Middle4 4 2) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_4_2_row_1_1_1 : (right2Middle4 4 2) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (right1Middle4 4 2) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_4_2_row_1_1_2 : (right2Middle4 4 2) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (right1Middle4 4 2) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_4_2_row_1_1_3 : (right2Middle4 4 2) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (right1Middle4 4 2) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_4_2_checked : right2Middle4 4 2 = right1Middle4 4 2 := by
  funext r
  fin_cases r
  · exact right2Middle4_eq_case_4_2_row_0_0_0
  · exact right2Middle4_eq_case_4_2_row_0_0_1
  · exact right2Middle4_eq_case_4_2_row_0_0_2
  · exact right2Middle4_eq_case_4_2_row_0_0_3
  · exact right2Middle4_eq_case_4_2_row_0_1_0
  · exact right2Middle4_eq_case_4_2_row_0_1_1
  · exact right2Middle4_eq_case_4_2_row_0_1_2
  · exact right2Middle4_eq_case_4_2_row_0_1_3
  · exact right2Middle4_eq_case_4_2_row_1_0_0
  · exact right2Middle4_eq_case_4_2_row_1_0_1
  · exact right2Middle4_eq_case_4_2_row_1_0_2
  · exact right2Middle4_eq_case_4_2_row_1_0_3
  · exact right2Middle4_eq_case_4_2_row_1_1_0
  · exact right2Middle4_eq_case_4_2_row_1_1_1
  · exact right2Middle4_eq_case_4_2_row_1_1_2
  · exact right2Middle4_eq_case_4_2_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem right2Middle4_eq_case_4_2 : right2Middle4 4 2 = innerLeftZ 4 2 4 * right1Middle4 4 2 := by
  simpa only [HexagonAtoms442.assocABC_eq,
    HexagonAtoms442.outerABC_eq,
    HexagonAtoms442.assocBAC_eq,
    HexagonAtoms442.innerABC_eq,
    HexagonAtoms442.innerRightABC_eq,
    HexagonAtoms442.inverseACB_eq,
    HexagonAtoms442.innerACB_eq,
    HexagonAtoms442.assocBCA_eq,
    HexagonAtoms442.innerRightBAC_eq,
    HexagonAtoms442.assocCAB_eq,
    HexagonAtoms442.outerLeftABC_eq,
    HexagonRowColumn442.assocBAC_alias,
    HexagonRowColumn442.innerRightBAC_alias,
    HexagonRowColumn442.product0_eq,
    HexagonRowColumn442.product1_eq,
    HexagonRowColumn442.product2_eq,
    HexagonRowColumn442.product3_eq,
    HexagonRowColumn442.product4_eq,
    HexagonRowColumn442.product5_eq,
    HexagonRowColumn442.product6_eq,
    HexagonRowColumn442.product7_eq] using right2Middle4_eq_case_4_2_checked

private theorem leftFinal4_case_4_2_row_0_0_0 : (((-1 : ℤ) ^ (leftScaleBit 4 4 2).val * positiveScale (leftScaleExponent 4 4 2)) •
      (rowColumnMul HexagonRowColumn442.rows_assocBCA HexagonRowColumn442.cols_left0)) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 4 4 2) • (left1Middle4 4 2)) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal4_case_4_2_row_0_0_1 : (((-1 : ℤ) ^ (leftScaleBit 4 4 2).val * positiveScale (leftScaleExponent 4 4 2)) •
      (rowColumnMul HexagonRowColumn442.rows_assocBCA HexagonRowColumn442.cols_left0)) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 4 4 2) • (left1Middle4 4 2)) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal4_case_4_2_row_0_0_2 : (((-1 : ℤ) ^ (leftScaleBit 4 4 2).val * positiveScale (leftScaleExponent 4 4 2)) •
      (rowColumnMul HexagonRowColumn442.rows_assocBCA HexagonRowColumn442.cols_left0)) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 4 4 2) • (left1Middle4 4 2)) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal4_case_4_2_row_0_0_3 : (((-1 : ℤ) ^ (leftScaleBit 4 4 2).val * positiveScale (leftScaleExponent 4 4 2)) •
      (rowColumnMul HexagonRowColumn442.rows_assocBCA HexagonRowColumn442.cols_left0)) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 4 4 2) • (left1Middle4 4 2)) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal4_case_4_2_row_0_1_0 : (((-1 : ℤ) ^ (leftScaleBit 4 4 2).val * positiveScale (leftScaleExponent 4 4 2)) •
      (rowColumnMul HexagonRowColumn442.rows_assocBCA HexagonRowColumn442.cols_left0)) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 4 4 2) • (left1Middle4 4 2)) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal4_case_4_2_row_0_1_1 : (((-1 : ℤ) ^ (leftScaleBit 4 4 2).val * positiveScale (leftScaleExponent 4 4 2)) •
      (rowColumnMul HexagonRowColumn442.rows_assocBCA HexagonRowColumn442.cols_left0)) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 4 4 2) • (left1Middle4 4 2)) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal4_case_4_2_row_0_1_2 : (((-1 : ℤ) ^ (leftScaleBit 4 4 2).val * positiveScale (leftScaleExponent 4 4 2)) •
      (rowColumnMul HexagonRowColumn442.rows_assocBCA HexagonRowColumn442.cols_left0)) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 4 4 2) • (left1Middle4 4 2)) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal4_case_4_2_row_0_1_3 : (((-1 : ℤ) ^ (leftScaleBit 4 4 2).val * positiveScale (leftScaleExponent 4 4 2)) •
      (rowColumnMul HexagonRowColumn442.rows_assocBCA HexagonRowColumn442.cols_left0)) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 4 4 2) • (left1Middle4 4 2)) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal4_case_4_2_row_1_0_0 : (((-1 : ℤ) ^ (leftScaleBit 4 4 2).val * positiveScale (leftScaleExponent 4 4 2)) •
      (rowColumnMul HexagonRowColumn442.rows_assocBCA HexagonRowColumn442.cols_left0)) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 4 4 2) • (left1Middle4 4 2)) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal4_case_4_2_row_1_0_1 : (((-1 : ℤ) ^ (leftScaleBit 4 4 2).val * positiveScale (leftScaleExponent 4 4 2)) •
      (rowColumnMul HexagonRowColumn442.rows_assocBCA HexagonRowColumn442.cols_left0)) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 4 4 2) • (left1Middle4 4 2)) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal4_case_4_2_row_1_0_2 : (((-1 : ℤ) ^ (leftScaleBit 4 4 2).val * positiveScale (leftScaleExponent 4 4 2)) •
      (rowColumnMul HexagonRowColumn442.rows_assocBCA HexagonRowColumn442.cols_left0)) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 4 4 2) • (left1Middle4 4 2)) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal4_case_4_2_row_1_0_3 : (((-1 : ℤ) ^ (leftScaleBit 4 4 2).val * positiveScale (leftScaleExponent 4 4 2)) •
      (rowColumnMul HexagonRowColumn442.rows_assocBCA HexagonRowColumn442.cols_left0)) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 4 4 2) • (left1Middle4 4 2)) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal4_case_4_2_row_1_1_0 : (((-1 : ℤ) ^ (leftScaleBit 4 4 2).val * positiveScale (leftScaleExponent 4 4 2)) •
      (rowColumnMul HexagonRowColumn442.rows_assocBCA HexagonRowColumn442.cols_left0)) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 4 4 2) • (left1Middle4 4 2)) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal4_case_4_2_row_1_1_1 : (((-1 : ℤ) ^ (leftScaleBit 4 4 2).val * positiveScale (leftScaleExponent 4 4 2)) •
      (rowColumnMul HexagonRowColumn442.rows_assocBCA HexagonRowColumn442.cols_left0)) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 4 4 2) • (left1Middle4 4 2)) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal4_case_4_2_row_1_1_2 : (((-1 : ℤ) ^ (leftScaleBit 4 4 2).val * positiveScale (leftScaleExponent 4 4 2)) •
      (rowColumnMul HexagonRowColumn442.rows_assocBCA HexagonRowColumn442.cols_left0)) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 4 4 2) • (left1Middle4 4 2)) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal4_case_4_2_row_1_1_3 : (((-1 : ℤ) ^ (leftScaleBit 4 4 2).val * positiveScale (leftScaleExponent 4 4 2)) •
      (rowColumnMul HexagonRowColumn442.rows_assocBCA HexagonRowColumn442.cols_left0)) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 4 4 2) • (left1Middle4 4 2)) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal4_case_4_2_checked : ((-1 : ℤ) ^ (leftScaleBit 4 4 2).val * positiveScale (leftScaleExponent 4 4 2)) •
      (rowColumnMul HexagonRowColumn442.rows_assocBCA HexagonRowColumn442.cols_left0) = negativeScale (leftScaleExponent 4 4 2) • (left1Middle4 4 2) := by
  funext r
  fin_cases r
  · exact leftFinal4_case_4_2_row_0_0_0
  · exact leftFinal4_case_4_2_row_0_0_1
  · exact leftFinal4_case_4_2_row_0_0_2
  · exact leftFinal4_case_4_2_row_0_0_3
  · exact leftFinal4_case_4_2_row_0_1_0
  · exact leftFinal4_case_4_2_row_0_1_1
  · exact leftFinal4_case_4_2_row_0_1_2
  · exact leftFinal4_case_4_2_row_0_1_3
  · exact leftFinal4_case_4_2_row_1_0_0
  · exact leftFinal4_case_4_2_row_1_0_1
  · exact leftFinal4_case_4_2_row_1_0_2
  · exact leftFinal4_case_4_2_row_1_0_3
  · exact leftFinal4_case_4_2_row_1_1_0
  · exact leftFinal4_case_4_2_row_1_1_1
  · exact leftFinal4_case_4_2_row_1_1_2
  · exact leftFinal4_case_4_2_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem leftFinal4_case_4_2 : ((-1 : ℤ) ^ (leftScaleBit 4 4 2).val * positiveScale (leftScaleExponent 4 4 2)) •
      (associatorZ 4 2 4 * left0Middle4 4 2) = negativeScale (leftScaleExponent 4 4 2) • (innerRightZ 4 4 2 * left1Middle4 4 2) := by
  simpa only [HexagonAtoms442.assocABC_eq,
    HexagonAtoms442.outerABC_eq,
    HexagonAtoms442.assocBAC_eq,
    HexagonAtoms442.innerABC_eq,
    HexagonAtoms442.innerRightABC_eq,
    HexagonAtoms442.inverseACB_eq,
    HexagonAtoms442.innerACB_eq,
    HexagonAtoms442.assocBCA_eq,
    HexagonAtoms442.innerRightBAC_eq,
    HexagonAtoms442.assocCAB_eq,
    HexagonAtoms442.outerLeftABC_eq,
    HexagonRowColumn442.assocBAC_alias,
    HexagonRowColumn442.innerRightBAC_alias,
    HexagonRowColumn442.product0_eq,
    HexagonRowColumn442.product1_eq,
    HexagonRowColumn442.product2_eq,
    HexagonRowColumn442.product3_eq,
    HexagonRowColumn442.product4_eq,
    HexagonRowColumn442.product5_eq,
    HexagonRowColumn442.product6_eq,
    HexagonRowColumn442.product7_eq] using leftFinal4_case_4_2_checked

private theorem rightFinal4_case_4_2_row_0_0_0 : (((-1 : ℤ) ^ (rightScaleBit 4 4 2).val * positiveScale (rightScaleExponent 4 4 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 2 4 : ℤ)) • HexagonAtoms442.outerLeftABC) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (negativeScale (rightScaleExponent 4 4 2) • (rowColumnMul HexagonRowColumn442.rows_assocCAB HexagonRowColumn442.cols_right2)) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal4_case_4_2_row_0_0_1 : (((-1 : ℤ) ^ (rightScaleBit 4 4 2).val * positiveScale (rightScaleExponent 4 4 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 2 4 : ℤ)) • HexagonAtoms442.outerLeftABC) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (negativeScale (rightScaleExponent 4 4 2) • (rowColumnMul HexagonRowColumn442.rows_assocCAB HexagonRowColumn442.cols_right2)) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal4_case_4_2_row_0_0_2 : (((-1 : ℤ) ^ (rightScaleBit 4 4 2).val * positiveScale (rightScaleExponent 4 4 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 2 4 : ℤ)) • HexagonAtoms442.outerLeftABC) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (negativeScale (rightScaleExponent 4 4 2) • (rowColumnMul HexagonRowColumn442.rows_assocCAB HexagonRowColumn442.cols_right2)) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal4_case_4_2_row_0_0_3 : (((-1 : ℤ) ^ (rightScaleBit 4 4 2).val * positiveScale (rightScaleExponent 4 4 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 2 4 : ℤ)) • HexagonAtoms442.outerLeftABC) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (negativeScale (rightScaleExponent 4 4 2) • (rowColumnMul HexagonRowColumn442.rows_assocCAB HexagonRowColumn442.cols_right2)) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal4_case_4_2_row_1_0_0 : (((-1 : ℤ) ^ (rightScaleBit 4 4 2).val * positiveScale (rightScaleExponent 4 4 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 2 4 : ℤ)) • HexagonAtoms442.outerLeftABC) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (negativeScale (rightScaleExponent 4 4 2) • (rowColumnMul HexagonRowColumn442.rows_assocCAB HexagonRowColumn442.cols_right2)) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal4_case_4_2_row_1_0_1 : (((-1 : ℤ) ^ (rightScaleBit 4 4 2).val * positiveScale (rightScaleExponent 4 4 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 2 4 : ℤ)) • HexagonAtoms442.outerLeftABC) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (negativeScale (rightScaleExponent 4 4 2) • (rowColumnMul HexagonRowColumn442.rows_assocCAB HexagonRowColumn442.cols_right2)) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal4_case_4_2_row_1_0_2 : (((-1 : ℤ) ^ (rightScaleBit 4 4 2).val * positiveScale (rightScaleExponent 4 4 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 2 4 : ℤ)) • HexagonAtoms442.outerLeftABC) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (negativeScale (rightScaleExponent 4 4 2) • (rowColumnMul HexagonRowColumn442.rows_assocCAB HexagonRowColumn442.cols_right2)) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal4_case_4_2_row_1_0_3 : (((-1 : ℤ) ^ (rightScaleBit 4 4 2).val * positiveScale (rightScaleExponent 4 4 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 2 4 : ℤ)) • HexagonAtoms442.outerLeftABC) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (negativeScale (rightScaleExponent 4 4 2) • (rowColumnMul HexagonRowColumn442.rows_assocCAB HexagonRowColumn442.cols_right2)) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal4_case_4_2_row_2_0_0 : (((-1 : ℤ) ^ (rightScaleBit 4 4 2).val * positiveScale (rightScaleExponent 4 4 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 2 4 : ℤ)) • HexagonAtoms442.outerLeftABC) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (negativeScale (rightScaleExponent 4 4 2) • (rowColumnMul HexagonRowColumn442.rows_assocCAB HexagonRowColumn442.cols_right2)) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal4_case_4_2_row_2_0_1 : (((-1 : ℤ) ^ (rightScaleBit 4 4 2).val * positiveScale (rightScaleExponent 4 4 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 2 4 : ℤ)) • HexagonAtoms442.outerLeftABC) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (negativeScale (rightScaleExponent 4 4 2) • (rowColumnMul HexagonRowColumn442.rows_assocCAB HexagonRowColumn442.cols_right2)) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal4_case_4_2_row_2_0_2 : (((-1 : ℤ) ^ (rightScaleBit 4 4 2).val * positiveScale (rightScaleExponent 4 4 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 2 4 : ℤ)) • HexagonAtoms442.outerLeftABC) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (negativeScale (rightScaleExponent 4 4 2) • (rowColumnMul HexagonRowColumn442.rows_assocCAB HexagonRowColumn442.cols_right2)) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal4_case_4_2_row_2_0_3 : (((-1 : ℤ) ^ (rightScaleBit 4 4 2).val * positiveScale (rightScaleExponent 4 4 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 2 4 : ℤ)) • HexagonAtoms442.outerLeftABC) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (negativeScale (rightScaleExponent 4 4 2) • (rowColumnMul HexagonRowColumn442.rows_assocCAB HexagonRowColumn442.cols_right2)) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal4_case_4_2_row_3_0_0 : (((-1 : ℤ) ^ (rightScaleBit 4 4 2).val * positiveScale (rightScaleExponent 4 4 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 2 4 : ℤ)) • HexagonAtoms442.outerLeftABC) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (negativeScale (rightScaleExponent 4 4 2) • (rowColumnMul HexagonRowColumn442.rows_assocCAB HexagonRowColumn442.cols_right2)) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal4_case_4_2_row_3_0_1 : (((-1 : ℤ) ^ (rightScaleBit 4 4 2).val * positiveScale (rightScaleExponent 4 4 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 2 4 : ℤ)) • HexagonAtoms442.outerLeftABC) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (negativeScale (rightScaleExponent 4 4 2) • (rowColumnMul HexagonRowColumn442.rows_assocCAB HexagonRowColumn442.cols_right2)) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal4_case_4_2_row_3_0_2 : (((-1 : ℤ) ^ (rightScaleBit 4 4 2).val * positiveScale (rightScaleExponent 4 4 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 2 4 : ℤ)) • HexagonAtoms442.outerLeftABC) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (negativeScale (rightScaleExponent 4 4 2) • (rowColumnMul HexagonRowColumn442.rows_assocCAB HexagonRowColumn442.cols_right2)) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal4_case_4_2_row_3_0_3 : (((-1 : ℤ) ^ (rightScaleBit 4 4 2).val * positiveScale (rightScaleExponent 4 4 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 2 4 : ℤ)) • HexagonAtoms442.outerLeftABC) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (negativeScale (rightScaleExponent 4 4 2) • (rowColumnMul HexagonRowColumn442.rows_assocCAB HexagonRowColumn442.cols_right2)) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal4_case_4_2_checked : ((-1 : ℤ) ^ (rightScaleBit 4 4 2).val * positiveScale (rightScaleExponent 4 4 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 2 4 : ℤ)) • HexagonAtoms442.outerLeftABC = negativeScale (rightScaleExponent 4 4 2) • (rowColumnMul HexagonRowColumn442.rows_assocCAB HexagonRowColumn442.cols_right2) := by
  funext r
  fin_cases r
  · exact rightFinal4_case_4_2_row_0_0_0
  · exact rightFinal4_case_4_2_row_0_0_1
  · exact rightFinal4_case_4_2_row_0_0_2
  · exact rightFinal4_case_4_2_row_0_0_3
  · exact rightFinal4_case_4_2_row_1_0_0
  · exact rightFinal4_case_4_2_row_1_0_1
  · exact rightFinal4_case_4_2_row_1_0_2
  · exact rightFinal4_case_4_2_row_1_0_3
  · exact rightFinal4_case_4_2_row_2_0_0
  · exact rightFinal4_case_4_2_row_2_0_1
  · exact rightFinal4_case_4_2_row_2_0_2
  · exact rightFinal4_case_4_2_row_2_0_3
  · exact rightFinal4_case_4_2_row_3_0_0
  · exact rightFinal4_case_4_2_row_3_0_1
  · exact rightFinal4_case_4_2_row_3_0_2
  · exact rightFinal4_case_4_2_row_3_0_3

set_option backward.isDefEq.respectTransparency false in
theorem rightFinal4_case_4_2 : ((-1 : ℤ) ^ (rightScaleBit 4 4 2).val * positiveScale (rightScaleExponent 4 4 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 2 4 : ℤ)) • outerLeftZ 4 4 2 = negativeScale (rightScaleExponent 4 4 2) • (associatorZ 2 4 4 * right2Middle4 4 2) := by
  simpa only [HexagonAtoms442.assocABC_eq,
    HexagonAtoms442.outerABC_eq,
    HexagonAtoms442.assocBAC_eq,
    HexagonAtoms442.innerABC_eq,
    HexagonAtoms442.innerRightABC_eq,
    HexagonAtoms442.inverseACB_eq,
    HexagonAtoms442.innerACB_eq,
    HexagonAtoms442.assocBCA_eq,
    HexagonAtoms442.innerRightBAC_eq,
    HexagonAtoms442.assocCAB_eq,
    HexagonAtoms442.outerLeftABC_eq,
    HexagonRowColumn442.assocBAC_alias,
    HexagonRowColumn442.innerRightBAC_alias,
    HexagonRowColumn442.product0_eq,
    HexagonRowColumn442.product1_eq,
    HexagonRowColumn442.product2_eq,
    HexagonRowColumn442.product3_eq,
    HexagonRowColumn442.product4_eq,
    HexagonRowColumn442.product5_eq,
    HexagonRowColumn442.product6_eq,
    HexagonRowColumn442.product7_eq] using rightFinal4_case_4_2_checked

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonCases4
