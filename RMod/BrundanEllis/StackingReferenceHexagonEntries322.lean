import RMod.BrundanEllis.StackingReferenceHexagonMiddle3
import RMod.BrundanEllis.StackingReferenceSparseMatrixCheck
import RMod.BrundanEllis.StackingReferenceHexagonAtoms322
import RMod.BrundanEllis.StackingReferenceHexagonRowColumn322

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

private theorem left0Middle3_eq_case_2_2_row_0_0_0 : (left0Middle3 2 2) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (HexagonAtoms322.assocABC) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle3_eq_case_2_2_row_0_0_1 : (left0Middle3 2 2) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (HexagonAtoms322.assocABC) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle3_eq_case_2_2_row_0_1_0 : (left0Middle3 2 2) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (HexagonAtoms322.assocABC) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle3_eq_case_2_2_row_0_1_1 : (left0Middle3 2 2) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (HexagonAtoms322.assocABC) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle3_eq_case_2_2_row_0_2_0 : (left0Middle3 2 2) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (HexagonAtoms322.assocABC) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle3_eq_case_2_2_row_0_2_1 : (left0Middle3 2 2) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (HexagonAtoms322.assocABC) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle3_eq_case_2_2_row_0_3_0 : (left0Middle3 2 2) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (HexagonAtoms322.assocABC) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle3_eq_case_2_2_row_0_3_1 : (left0Middle3 2 2) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (HexagonAtoms322.assocABC) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle3_eq_case_2_2_row_1_0_0 : (left0Middle3 2 2) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (HexagonAtoms322.assocABC) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle3_eq_case_2_2_row_1_0_1 : (left0Middle3 2 2) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (HexagonAtoms322.assocABC) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle3_eq_case_2_2_row_1_1_0 : (left0Middle3 2 2) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (HexagonAtoms322.assocABC) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle3_eq_case_2_2_row_1_1_1 : (left0Middle3 2 2) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (HexagonAtoms322.assocABC) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle3_eq_case_2_2_row_1_2_0 : (left0Middle3 2 2) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (HexagonAtoms322.assocABC) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle3_eq_case_2_2_row_1_2_1 : (left0Middle3 2 2) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (HexagonAtoms322.assocABC) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle3_eq_case_2_2_row_1_3_0 : (left0Middle3 2 2) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (HexagonAtoms322.assocABC) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle3_eq_case_2_2_row_1_3_1 : (left0Middle3 2 2) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (HexagonAtoms322.assocABC) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle3_eq_case_2_2_checked : left0Middle3 2 2 = HexagonAtoms322.assocABC := by
  funext r
  fin_cases r
  · exact left0Middle3_eq_case_2_2_row_0_0_0
  · exact left0Middle3_eq_case_2_2_row_0_0_1
  · exact left0Middle3_eq_case_2_2_row_0_1_0
  · exact left0Middle3_eq_case_2_2_row_0_1_1
  · exact left0Middle3_eq_case_2_2_row_0_2_0
  · exact left0Middle3_eq_case_2_2_row_0_2_1
  · exact left0Middle3_eq_case_2_2_row_0_3_0
  · exact left0Middle3_eq_case_2_2_row_0_3_1
  · exact left0Middle3_eq_case_2_2_row_1_0_0
  · exact left0Middle3_eq_case_2_2_row_1_0_1
  · exact left0Middle3_eq_case_2_2_row_1_1_0
  · exact left0Middle3_eq_case_2_2_row_1_1_1
  · exact left0Middle3_eq_case_2_2_row_1_2_0
  · exact left0Middle3_eq_case_2_2_row_1_2_1
  · exact left0Middle3_eq_case_2_2_row_1_3_0
  · exact left0Middle3_eq_case_2_2_row_1_3_1

set_option backward.isDefEq.respectTransparency false in
theorem left0Middle3_eq_case_2_2 : left0Middle3 2 2 = outerRightZ 3 2 2 * associatorZ 3 2 2 := by
  simpa only [HexagonAtoms322.assocABC_eq,
    HexagonAtoms322.outerABC_eq,
    HexagonAtoms322.assocBAC_eq,
    HexagonAtoms322.innerABC_eq,
    HexagonAtoms322.innerRightABC_eq,
    HexagonAtoms322.inverseACB_eq,
    HexagonAtoms322.innerACB_eq,
    HexagonAtoms322.assocBCA_eq,
    HexagonAtoms322.innerRightBAC_eq,
    HexagonAtoms322.assocCAB_eq,
    HexagonAtoms322.outerLeftABC_eq,
    HexagonRowColumn322.innerACB_alias,
    HexagonRowColumn322.assocCAB_alias,
    HexagonRowColumn322.product0_eq,
    HexagonRowColumn322.product1_eq,
    HexagonRowColumn322.product2_eq,
    HexagonRowColumn322.product3_eq,
    HexagonRowColumn322.product4_eq,
    HexagonRowColumn322.product5_eq,
    HexagonRowColumn322.product6_eq,
    HexagonRowColumn322.product7_eq] using left0Middle3_eq_case_2_2_checked

private theorem left1Middle3_eq_case_2_2_row_0_0_0 : (left1Middle3 2 2) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (HexagonAtoms322.assocBAC) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle3_eq_case_2_2_row_0_0_1 : (left1Middle3 2 2) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (HexagonAtoms322.assocBAC) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle3_eq_case_2_2_row_0_1_0 : (left1Middle3 2 2) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (HexagonAtoms322.assocBAC) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle3_eq_case_2_2_row_0_1_1 : (left1Middle3 2 2) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (HexagonAtoms322.assocBAC) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle3_eq_case_2_2_row_0_2_0 : (left1Middle3 2 2) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (HexagonAtoms322.assocBAC) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle3_eq_case_2_2_row_0_2_1 : (left1Middle3 2 2) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (HexagonAtoms322.assocBAC) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle3_eq_case_2_2_row_0_3_0 : (left1Middle3 2 2) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (HexagonAtoms322.assocBAC) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle3_eq_case_2_2_row_0_3_1 : (left1Middle3 2 2) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (HexagonAtoms322.assocBAC) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle3_eq_case_2_2_row_1_0_0 : (left1Middle3 2 2) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (HexagonAtoms322.assocBAC) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle3_eq_case_2_2_row_1_0_1 : (left1Middle3 2 2) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (HexagonAtoms322.assocBAC) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle3_eq_case_2_2_row_1_1_0 : (left1Middle3 2 2) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (HexagonAtoms322.assocBAC) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle3_eq_case_2_2_row_1_1_1 : (left1Middle3 2 2) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (HexagonAtoms322.assocBAC) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle3_eq_case_2_2_row_1_2_0 : (left1Middle3 2 2) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (HexagonAtoms322.assocBAC) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle3_eq_case_2_2_row_1_2_1 : (left1Middle3 2 2) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (HexagonAtoms322.assocBAC) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle3_eq_case_2_2_row_1_3_0 : (left1Middle3 2 2) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (HexagonAtoms322.assocBAC) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle3_eq_case_2_2_row_1_3_1 : (left1Middle3 2 2) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (HexagonAtoms322.assocBAC) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle3_eq_case_2_2_checked : left1Middle3 2 2 = HexagonAtoms322.assocBAC := by
  funext r
  fin_cases r
  · exact left1Middle3_eq_case_2_2_row_0_0_0
  · exact left1Middle3_eq_case_2_2_row_0_0_1
  · exact left1Middle3_eq_case_2_2_row_0_1_0
  · exact left1Middle3_eq_case_2_2_row_0_1_1
  · exact left1Middle3_eq_case_2_2_row_0_2_0
  · exact left1Middle3_eq_case_2_2_row_0_2_1
  · exact left1Middle3_eq_case_2_2_row_0_3_0
  · exact left1Middle3_eq_case_2_2_row_0_3_1
  · exact left1Middle3_eq_case_2_2_row_1_0_0
  · exact left1Middle3_eq_case_2_2_row_1_0_1
  · exact left1Middle3_eq_case_2_2_row_1_1_0
  · exact left1Middle3_eq_case_2_2_row_1_1_1
  · exact left1Middle3_eq_case_2_2_row_1_2_0
  · exact left1Middle3_eq_case_2_2_row_1_2_1
  · exact left1Middle3_eq_case_2_2_row_1_3_0
  · exact left1Middle3_eq_case_2_2_row_1_3_1

set_option backward.isDefEq.respectTransparency false in
theorem left1Middle3_eq_case_2_2 : left1Middle3 2 2 = associatorZ 2 3 2 * innerLeftZ 3 2 2 := by
  simpa only [HexagonAtoms322.assocABC_eq,
    HexagonAtoms322.outerABC_eq,
    HexagonAtoms322.assocBAC_eq,
    HexagonAtoms322.innerABC_eq,
    HexagonAtoms322.innerRightABC_eq,
    HexagonAtoms322.inverseACB_eq,
    HexagonAtoms322.innerACB_eq,
    HexagonAtoms322.assocBCA_eq,
    HexagonAtoms322.innerRightBAC_eq,
    HexagonAtoms322.assocCAB_eq,
    HexagonAtoms322.outerLeftABC_eq,
    HexagonRowColumn322.innerACB_alias,
    HexagonRowColumn322.assocCAB_alias,
    HexagonRowColumn322.product0_eq,
    HexagonRowColumn322.product1_eq,
    HexagonRowColumn322.product2_eq,
    HexagonRowColumn322.product3_eq,
    HexagonRowColumn322.product4_eq,
    HexagonRowColumn322.product5_eq,
    HexagonRowColumn322.product6_eq,
    HexagonRowColumn322.product7_eq] using left1Middle3_eq_case_2_2_checked

private theorem right0Middle3_eq_case_2_2_row_0_0_0 : (right0Middle3 2 2) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn322.rows_innerRightABC HexagonRowColumn322.cols_assocABC) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle3_eq_case_2_2_row_0_0_1 : (right0Middle3 2 2) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn322.rows_innerRightABC HexagonRowColumn322.cols_assocABC) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle3_eq_case_2_2_row_0_1_0 : (right0Middle3 2 2) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn322.rows_innerRightABC HexagonRowColumn322.cols_assocABC) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle3_eq_case_2_2_row_0_1_1 : (right0Middle3 2 2) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn322.rows_innerRightABC HexagonRowColumn322.cols_assocABC) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle3_eq_case_2_2_row_0_2_0 : (right0Middle3 2 2) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn322.rows_innerRightABC HexagonRowColumn322.cols_assocABC) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle3_eq_case_2_2_row_0_2_1 : (right0Middle3 2 2) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn322.rows_innerRightABC HexagonRowColumn322.cols_assocABC) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle3_eq_case_2_2_row_0_3_0 : (right0Middle3 2 2) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn322.rows_innerRightABC HexagonRowColumn322.cols_assocABC) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle3_eq_case_2_2_row_0_3_1 : (right0Middle3 2 2) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn322.rows_innerRightABC HexagonRowColumn322.cols_assocABC) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle3_eq_case_2_2_row_1_0_0 : (right0Middle3 2 2) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn322.rows_innerRightABC HexagonRowColumn322.cols_assocABC) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle3_eq_case_2_2_row_1_0_1 : (right0Middle3 2 2) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn322.rows_innerRightABC HexagonRowColumn322.cols_assocABC) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle3_eq_case_2_2_row_1_1_0 : (right0Middle3 2 2) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn322.rows_innerRightABC HexagonRowColumn322.cols_assocABC) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle3_eq_case_2_2_row_1_1_1 : (right0Middle3 2 2) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn322.rows_innerRightABC HexagonRowColumn322.cols_assocABC) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle3_eq_case_2_2_row_1_2_0 : (right0Middle3 2 2) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn322.rows_innerRightABC HexagonRowColumn322.cols_assocABC) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle3_eq_case_2_2_row_1_2_1 : (right0Middle3 2 2) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn322.rows_innerRightABC HexagonRowColumn322.cols_assocABC) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle3_eq_case_2_2_row_1_3_0 : (right0Middle3 2 2) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn322.rows_innerRightABC HexagonRowColumn322.cols_assocABC) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle3_eq_case_2_2_row_1_3_1 : (right0Middle3 2 2) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn322.rows_innerRightABC HexagonRowColumn322.cols_assocABC) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle3_eq_case_2_2_checked : right0Middle3 2 2 = rowColumnMul HexagonRowColumn322.rows_innerRightABC HexagonRowColumn322.cols_assocABC := by
  funext r
  fin_cases r
  · exact right0Middle3_eq_case_2_2_row_0_0_0
  · exact right0Middle3_eq_case_2_2_row_0_0_1
  · exact right0Middle3_eq_case_2_2_row_0_1_0
  · exact right0Middle3_eq_case_2_2_row_0_1_1
  · exact right0Middle3_eq_case_2_2_row_0_2_0
  · exact right0Middle3_eq_case_2_2_row_0_2_1
  · exact right0Middle3_eq_case_2_2_row_0_3_0
  · exact right0Middle3_eq_case_2_2_row_0_3_1
  · exact right0Middle3_eq_case_2_2_row_1_0_0
  · exact right0Middle3_eq_case_2_2_row_1_0_1
  · exact right0Middle3_eq_case_2_2_row_1_1_0
  · exact right0Middle3_eq_case_2_2_row_1_1_1
  · exact right0Middle3_eq_case_2_2_row_1_2_0
  · exact right0Middle3_eq_case_2_2_row_1_2_1
  · exact right0Middle3_eq_case_2_2_row_1_3_0
  · exact right0Middle3_eq_case_2_2_row_1_3_1

set_option backward.isDefEq.respectTransparency false in
theorem right0Middle3_eq_case_2_2 : right0Middle3 2 2 = innerRightZ 3 2 2 * associatorZ 3 2 2 := by
  simpa only [HexagonAtoms322.assocABC_eq,
    HexagonAtoms322.outerABC_eq,
    HexagonAtoms322.assocBAC_eq,
    HexagonAtoms322.innerABC_eq,
    HexagonAtoms322.innerRightABC_eq,
    HexagonAtoms322.inverseACB_eq,
    HexagonAtoms322.innerACB_eq,
    HexagonAtoms322.assocBCA_eq,
    HexagonAtoms322.innerRightBAC_eq,
    HexagonAtoms322.assocCAB_eq,
    HexagonAtoms322.outerLeftABC_eq,
    HexagonRowColumn322.innerACB_alias,
    HexagonRowColumn322.assocCAB_alias,
    HexagonRowColumn322.product0_eq,
    HexagonRowColumn322.product1_eq,
    HexagonRowColumn322.product2_eq,
    HexagonRowColumn322.product3_eq,
    HexagonRowColumn322.product4_eq,
    HexagonRowColumn322.product5_eq,
    HexagonRowColumn322.product6_eq,
    HexagonRowColumn322.product7_eq] using right0Middle3_eq_case_2_2_checked

private theorem right1Middle3_eq_case_2_2_row_0_0_0 : (right1Middle3 2 2) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn322.rows_inverseACB HexagonRowColumn322.cols_right0) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle3_eq_case_2_2_row_0_0_1 : (right1Middle3 2 2) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn322.rows_inverseACB HexagonRowColumn322.cols_right0) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle3_eq_case_2_2_row_0_1_0 : (right1Middle3 2 2) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn322.rows_inverseACB HexagonRowColumn322.cols_right0) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle3_eq_case_2_2_row_0_1_1 : (right1Middle3 2 2) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn322.rows_inverseACB HexagonRowColumn322.cols_right0) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle3_eq_case_2_2_row_0_2_0 : (right1Middle3 2 2) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn322.rows_inverseACB HexagonRowColumn322.cols_right0) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle3_eq_case_2_2_row_0_2_1 : (right1Middle3 2 2) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn322.rows_inverseACB HexagonRowColumn322.cols_right0) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle3_eq_case_2_2_row_0_3_0 : (right1Middle3 2 2) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn322.rows_inverseACB HexagonRowColumn322.cols_right0) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle3_eq_case_2_2_row_0_3_1 : (right1Middle3 2 2) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn322.rows_inverseACB HexagonRowColumn322.cols_right0) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle3_eq_case_2_2_row_1_0_0 : (right1Middle3 2 2) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn322.rows_inverseACB HexagonRowColumn322.cols_right0) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle3_eq_case_2_2_row_1_0_1 : (right1Middle3 2 2) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn322.rows_inverseACB HexagonRowColumn322.cols_right0) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle3_eq_case_2_2_row_1_1_0 : (right1Middle3 2 2) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn322.rows_inverseACB HexagonRowColumn322.cols_right0) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle3_eq_case_2_2_row_1_1_1 : (right1Middle3 2 2) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn322.rows_inverseACB HexagonRowColumn322.cols_right0) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle3_eq_case_2_2_row_1_2_0 : (right1Middle3 2 2) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn322.rows_inverseACB HexagonRowColumn322.cols_right0) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle3_eq_case_2_2_row_1_2_1 : (right1Middle3 2 2) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn322.rows_inverseACB HexagonRowColumn322.cols_right0) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle3_eq_case_2_2_row_1_3_0 : (right1Middle3 2 2) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn322.rows_inverseACB HexagonRowColumn322.cols_right0) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle3_eq_case_2_2_row_1_3_1 : (right1Middle3 2 2) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn322.rows_inverseACB HexagonRowColumn322.cols_right0) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle3_eq_case_2_2_checked : right1Middle3 2 2 = rowColumnMul HexagonRowColumn322.rows_inverseACB HexagonRowColumn322.cols_right0 := by
  funext r
  fin_cases r
  · exact right1Middle3_eq_case_2_2_row_0_0_0
  · exact right1Middle3_eq_case_2_2_row_0_0_1
  · exact right1Middle3_eq_case_2_2_row_0_1_0
  · exact right1Middle3_eq_case_2_2_row_0_1_1
  · exact right1Middle3_eq_case_2_2_row_0_2_0
  · exact right1Middle3_eq_case_2_2_row_0_2_1
  · exact right1Middle3_eq_case_2_2_row_0_3_0
  · exact right1Middle3_eq_case_2_2_row_0_3_1
  · exact right1Middle3_eq_case_2_2_row_1_0_0
  · exact right1Middle3_eq_case_2_2_row_1_0_1
  · exact right1Middle3_eq_case_2_2_row_1_1_0
  · exact right1Middle3_eq_case_2_2_row_1_1_1
  · exact right1Middle3_eq_case_2_2_row_1_2_0
  · exact right1Middle3_eq_case_2_2_row_1_2_1
  · exact right1Middle3_eq_case_2_2_row_1_3_0
  · exact right1Middle3_eq_case_2_2_row_1_3_1

set_option backward.isDefEq.respectTransparency false in
theorem right1Middle3_eq_case_2_2 : right1Middle3 2 2 = associatorInverseZ 3 2 2 * right0Middle3 2 2 := by
  simpa only [HexagonAtoms322.assocABC_eq,
    HexagonAtoms322.outerABC_eq,
    HexagonAtoms322.assocBAC_eq,
    HexagonAtoms322.innerABC_eq,
    HexagonAtoms322.innerRightABC_eq,
    HexagonAtoms322.inverseACB_eq,
    HexagonAtoms322.innerACB_eq,
    HexagonAtoms322.assocBCA_eq,
    HexagonAtoms322.innerRightBAC_eq,
    HexagonAtoms322.assocCAB_eq,
    HexagonAtoms322.outerLeftABC_eq,
    HexagonRowColumn322.innerACB_alias,
    HexagonRowColumn322.assocCAB_alias,
    HexagonRowColumn322.product0_eq,
    HexagonRowColumn322.product1_eq,
    HexagonRowColumn322.product2_eq,
    HexagonRowColumn322.product3_eq,
    HexagonRowColumn322.product4_eq,
    HexagonRowColumn322.product5_eq,
    HexagonRowColumn322.product6_eq,
    HexagonRowColumn322.product7_eq] using right1Middle3_eq_case_2_2_checked

private theorem right2Middle3_eq_case_2_2_row_0_0_0 : (right2Middle3 2 2) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (right1Middle3 2 2) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle3_eq_case_2_2_row_0_0_1 : (right2Middle3 2 2) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (right1Middle3 2 2) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle3_eq_case_2_2_row_0_1_0 : (right2Middle3 2 2) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (right1Middle3 2 2) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle3_eq_case_2_2_row_0_1_1 : (right2Middle3 2 2) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (right1Middle3 2 2) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle3_eq_case_2_2_row_0_2_0 : (right2Middle3 2 2) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (right1Middle3 2 2) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle3_eq_case_2_2_row_0_2_1 : (right2Middle3 2 2) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (right1Middle3 2 2) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle3_eq_case_2_2_row_0_3_0 : (right2Middle3 2 2) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (right1Middle3 2 2) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle3_eq_case_2_2_row_0_3_1 : (right2Middle3 2 2) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (right1Middle3 2 2) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle3_eq_case_2_2_row_1_0_0 : (right2Middle3 2 2) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (right1Middle3 2 2) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle3_eq_case_2_2_row_1_0_1 : (right2Middle3 2 2) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (right1Middle3 2 2) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle3_eq_case_2_2_row_1_1_0 : (right2Middle3 2 2) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (right1Middle3 2 2) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle3_eq_case_2_2_row_1_1_1 : (right2Middle3 2 2) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (right1Middle3 2 2) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle3_eq_case_2_2_row_1_2_0 : (right2Middle3 2 2) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (right1Middle3 2 2) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle3_eq_case_2_2_row_1_2_1 : (right2Middle3 2 2) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (right1Middle3 2 2) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle3_eq_case_2_2_row_1_3_0 : (right2Middle3 2 2) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (right1Middle3 2 2) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle3_eq_case_2_2_row_1_3_1 : (right2Middle3 2 2) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (right1Middle3 2 2) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle3_eq_case_2_2_checked : right2Middle3 2 2 = right1Middle3 2 2 := by
  funext r
  fin_cases r
  · exact right2Middle3_eq_case_2_2_row_0_0_0
  · exact right2Middle3_eq_case_2_2_row_0_0_1
  · exact right2Middle3_eq_case_2_2_row_0_1_0
  · exact right2Middle3_eq_case_2_2_row_0_1_1
  · exact right2Middle3_eq_case_2_2_row_0_2_0
  · exact right2Middle3_eq_case_2_2_row_0_2_1
  · exact right2Middle3_eq_case_2_2_row_0_3_0
  · exact right2Middle3_eq_case_2_2_row_0_3_1
  · exact right2Middle3_eq_case_2_2_row_1_0_0
  · exact right2Middle3_eq_case_2_2_row_1_0_1
  · exact right2Middle3_eq_case_2_2_row_1_1_0
  · exact right2Middle3_eq_case_2_2_row_1_1_1
  · exact right2Middle3_eq_case_2_2_row_1_2_0
  · exact right2Middle3_eq_case_2_2_row_1_2_1
  · exact right2Middle3_eq_case_2_2_row_1_3_0
  · exact right2Middle3_eq_case_2_2_row_1_3_1

set_option backward.isDefEq.respectTransparency false in
theorem right2Middle3_eq_case_2_2 : right2Middle3 2 2 = innerLeftZ 3 2 2 * right1Middle3 2 2 := by
  simpa only [HexagonAtoms322.assocABC_eq,
    HexagonAtoms322.outerABC_eq,
    HexagonAtoms322.assocBAC_eq,
    HexagonAtoms322.innerABC_eq,
    HexagonAtoms322.innerRightABC_eq,
    HexagonAtoms322.inverseACB_eq,
    HexagonAtoms322.innerACB_eq,
    HexagonAtoms322.assocBCA_eq,
    HexagonAtoms322.innerRightBAC_eq,
    HexagonAtoms322.assocCAB_eq,
    HexagonAtoms322.outerLeftABC_eq,
    HexagonRowColumn322.innerACB_alias,
    HexagonRowColumn322.assocCAB_alias,
    HexagonRowColumn322.product0_eq,
    HexagonRowColumn322.product1_eq,
    HexagonRowColumn322.product2_eq,
    HexagonRowColumn322.product3_eq,
    HexagonRowColumn322.product4_eq,
    HexagonRowColumn322.product5_eq,
    HexagonRowColumn322.product6_eq,
    HexagonRowColumn322.product7_eq] using right2Middle3_eq_case_2_2_checked

private theorem leftFinal3_case_2_2_row_0_0_0 : (((-1 : ℤ) ^ (leftScaleBit 3 2 2).val * positiveScale (leftScaleExponent 3 2 2)) •
      (rowColumnMul HexagonRowColumn322.rows_assocBCA HexagonRowColumn322.cols_left0)) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 3 2 2) • (left1Middle3 2 2)) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal3_case_2_2_row_0_0_1 : (((-1 : ℤ) ^ (leftScaleBit 3 2 2).val * positiveScale (leftScaleExponent 3 2 2)) •
      (rowColumnMul HexagonRowColumn322.rows_assocBCA HexagonRowColumn322.cols_left0)) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 3 2 2) • (left1Middle3 2 2)) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal3_case_2_2_row_0_1_0 : (((-1 : ℤ) ^ (leftScaleBit 3 2 2).val * positiveScale (leftScaleExponent 3 2 2)) •
      (rowColumnMul HexagonRowColumn322.rows_assocBCA HexagonRowColumn322.cols_left0)) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 3 2 2) • (left1Middle3 2 2)) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal3_case_2_2_row_0_1_1 : (((-1 : ℤ) ^ (leftScaleBit 3 2 2).val * positiveScale (leftScaleExponent 3 2 2)) •
      (rowColumnMul HexagonRowColumn322.rows_assocBCA HexagonRowColumn322.cols_left0)) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 3 2 2) • (left1Middle3 2 2)) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal3_case_2_2_row_0_2_0 : (((-1 : ℤ) ^ (leftScaleBit 3 2 2).val * positiveScale (leftScaleExponent 3 2 2)) •
      (rowColumnMul HexagonRowColumn322.rows_assocBCA HexagonRowColumn322.cols_left0)) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 3 2 2) • (left1Middle3 2 2)) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal3_case_2_2_row_0_2_1 : (((-1 : ℤ) ^ (leftScaleBit 3 2 2).val * positiveScale (leftScaleExponent 3 2 2)) •
      (rowColumnMul HexagonRowColumn322.rows_assocBCA HexagonRowColumn322.cols_left0)) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 3 2 2) • (left1Middle3 2 2)) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal3_case_2_2_row_0_3_0 : (((-1 : ℤ) ^ (leftScaleBit 3 2 2).val * positiveScale (leftScaleExponent 3 2 2)) •
      (rowColumnMul HexagonRowColumn322.rows_assocBCA HexagonRowColumn322.cols_left0)) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 3 2 2) • (left1Middle3 2 2)) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal3_case_2_2_row_0_3_1 : (((-1 : ℤ) ^ (leftScaleBit 3 2 2).val * positiveScale (leftScaleExponent 3 2 2)) •
      (rowColumnMul HexagonRowColumn322.rows_assocBCA HexagonRowColumn322.cols_left0)) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 3 2 2) • (left1Middle3 2 2)) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal3_case_2_2_row_1_0_0 : (((-1 : ℤ) ^ (leftScaleBit 3 2 2).val * positiveScale (leftScaleExponent 3 2 2)) •
      (rowColumnMul HexagonRowColumn322.rows_assocBCA HexagonRowColumn322.cols_left0)) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 3 2 2) • (left1Middle3 2 2)) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal3_case_2_2_row_1_0_1 : (((-1 : ℤ) ^ (leftScaleBit 3 2 2).val * positiveScale (leftScaleExponent 3 2 2)) •
      (rowColumnMul HexagonRowColumn322.rows_assocBCA HexagonRowColumn322.cols_left0)) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 3 2 2) • (left1Middle3 2 2)) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal3_case_2_2_row_1_1_0 : (((-1 : ℤ) ^ (leftScaleBit 3 2 2).val * positiveScale (leftScaleExponent 3 2 2)) •
      (rowColumnMul HexagonRowColumn322.rows_assocBCA HexagonRowColumn322.cols_left0)) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 3 2 2) • (left1Middle3 2 2)) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal3_case_2_2_row_1_1_1 : (((-1 : ℤ) ^ (leftScaleBit 3 2 2).val * positiveScale (leftScaleExponent 3 2 2)) •
      (rowColumnMul HexagonRowColumn322.rows_assocBCA HexagonRowColumn322.cols_left0)) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 3 2 2) • (left1Middle3 2 2)) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal3_case_2_2_row_1_2_0 : (((-1 : ℤ) ^ (leftScaleBit 3 2 2).val * positiveScale (leftScaleExponent 3 2 2)) •
      (rowColumnMul HexagonRowColumn322.rows_assocBCA HexagonRowColumn322.cols_left0)) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 3 2 2) • (left1Middle3 2 2)) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal3_case_2_2_row_1_2_1 : (((-1 : ℤ) ^ (leftScaleBit 3 2 2).val * positiveScale (leftScaleExponent 3 2 2)) •
      (rowColumnMul HexagonRowColumn322.rows_assocBCA HexagonRowColumn322.cols_left0)) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 3 2 2) • (left1Middle3 2 2)) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal3_case_2_2_row_1_3_0 : (((-1 : ℤ) ^ (leftScaleBit 3 2 2).val * positiveScale (leftScaleExponent 3 2 2)) •
      (rowColumnMul HexagonRowColumn322.rows_assocBCA HexagonRowColumn322.cols_left0)) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 3 2 2) • (left1Middle3 2 2)) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal3_case_2_2_row_1_3_1 : (((-1 : ℤ) ^ (leftScaleBit 3 2 2).val * positiveScale (leftScaleExponent 3 2 2)) •
      (rowColumnMul HexagonRowColumn322.rows_assocBCA HexagonRowColumn322.cols_left0)) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 3 2 2) • (left1Middle3 2 2)) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal3_case_2_2_checked : ((-1 : ℤ) ^ (leftScaleBit 3 2 2).val * positiveScale (leftScaleExponent 3 2 2)) •
      (rowColumnMul HexagonRowColumn322.rows_assocBCA HexagonRowColumn322.cols_left0) = negativeScale (leftScaleExponent 3 2 2) • (left1Middle3 2 2) := by
  funext r
  fin_cases r
  · exact leftFinal3_case_2_2_row_0_0_0
  · exact leftFinal3_case_2_2_row_0_0_1
  · exact leftFinal3_case_2_2_row_0_1_0
  · exact leftFinal3_case_2_2_row_0_1_1
  · exact leftFinal3_case_2_2_row_0_2_0
  · exact leftFinal3_case_2_2_row_0_2_1
  · exact leftFinal3_case_2_2_row_0_3_0
  · exact leftFinal3_case_2_2_row_0_3_1
  · exact leftFinal3_case_2_2_row_1_0_0
  · exact leftFinal3_case_2_2_row_1_0_1
  · exact leftFinal3_case_2_2_row_1_1_0
  · exact leftFinal3_case_2_2_row_1_1_1
  · exact leftFinal3_case_2_2_row_1_2_0
  · exact leftFinal3_case_2_2_row_1_2_1
  · exact leftFinal3_case_2_2_row_1_3_0
  · exact leftFinal3_case_2_2_row_1_3_1

set_option backward.isDefEq.respectTransparency false in
theorem leftFinal3_case_2_2 : ((-1 : ℤ) ^ (leftScaleBit 3 2 2).val * positiveScale (leftScaleExponent 3 2 2)) •
      (associatorZ 2 2 3 * left0Middle3 2 2) = negativeScale (leftScaleExponent 3 2 2) • (innerRightZ 2 3 2 * left1Middle3 2 2) := by
  simpa only [HexagonAtoms322.assocABC_eq,
    HexagonAtoms322.outerABC_eq,
    HexagonAtoms322.assocBAC_eq,
    HexagonAtoms322.innerABC_eq,
    HexagonAtoms322.innerRightABC_eq,
    HexagonAtoms322.inverseACB_eq,
    HexagonAtoms322.innerACB_eq,
    HexagonAtoms322.assocBCA_eq,
    HexagonAtoms322.innerRightBAC_eq,
    HexagonAtoms322.assocCAB_eq,
    HexagonAtoms322.outerLeftABC_eq,
    HexagonRowColumn322.innerACB_alias,
    HexagonRowColumn322.assocCAB_alias,
    HexagonRowColumn322.product0_eq,
    HexagonRowColumn322.product1_eq,
    HexagonRowColumn322.product2_eq,
    HexagonRowColumn322.product3_eq,
    HexagonRowColumn322.product4_eq,
    HexagonRowColumn322.product5_eq,
    HexagonRowColumn322.product6_eq,
    HexagonRowColumn322.product7_eq] using leftFinal3_case_2_2_checked

private theorem rightFinal3_case_2_2_row_0_0_0 : (((-1 : ℤ) ^ (rightScaleBit 3 2 2).val * positiveScale (rightScaleExponent 3 2 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 2 : ℤ)) • HexagonAtoms322.outerLeftABC) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (negativeScale (rightScaleExponent 3 2 2) • (rowColumnMul HexagonRowColumn322.rows_assocBAC HexagonRowColumn322.cols_right2)) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal3_case_2_2_row_0_0_1 : (((-1 : ℤ) ^ (rightScaleBit 3 2 2).val * positiveScale (rightScaleExponent 3 2 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 2 : ℤ)) • HexagonAtoms322.outerLeftABC) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (negativeScale (rightScaleExponent 3 2 2) • (rowColumnMul HexagonRowColumn322.rows_assocBAC HexagonRowColumn322.cols_right2)) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal3_case_2_2_row_0_1_0 : (((-1 : ℤ) ^ (rightScaleBit 3 2 2).val * positiveScale (rightScaleExponent 3 2 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 2 : ℤ)) • HexagonAtoms322.outerLeftABC) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (negativeScale (rightScaleExponent 3 2 2) • (rowColumnMul HexagonRowColumn322.rows_assocBAC HexagonRowColumn322.cols_right2)) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal3_case_2_2_row_0_1_1 : (((-1 : ℤ) ^ (rightScaleBit 3 2 2).val * positiveScale (rightScaleExponent 3 2 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 2 : ℤ)) • HexagonAtoms322.outerLeftABC) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (negativeScale (rightScaleExponent 3 2 2) • (rowColumnMul HexagonRowColumn322.rows_assocBAC HexagonRowColumn322.cols_right2)) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal3_case_2_2_row_0_2_0 : (((-1 : ℤ) ^ (rightScaleBit 3 2 2).val * positiveScale (rightScaleExponent 3 2 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 2 : ℤ)) • HexagonAtoms322.outerLeftABC) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (negativeScale (rightScaleExponent 3 2 2) • (rowColumnMul HexagonRowColumn322.rows_assocBAC HexagonRowColumn322.cols_right2)) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal3_case_2_2_row_0_2_1 : (((-1 : ℤ) ^ (rightScaleBit 3 2 2).val * positiveScale (rightScaleExponent 3 2 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 2 : ℤ)) • HexagonAtoms322.outerLeftABC) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (negativeScale (rightScaleExponent 3 2 2) • (rowColumnMul HexagonRowColumn322.rows_assocBAC HexagonRowColumn322.cols_right2)) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal3_case_2_2_row_0_3_0 : (((-1 : ℤ) ^ (rightScaleBit 3 2 2).val * positiveScale (rightScaleExponent 3 2 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 2 : ℤ)) • HexagonAtoms322.outerLeftABC) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (negativeScale (rightScaleExponent 3 2 2) • (rowColumnMul HexagonRowColumn322.rows_assocBAC HexagonRowColumn322.cols_right2)) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal3_case_2_2_row_0_3_1 : (((-1 : ℤ) ^ (rightScaleBit 3 2 2).val * positiveScale (rightScaleExponent 3 2 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 2 : ℤ)) • HexagonAtoms322.outerLeftABC) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (negativeScale (rightScaleExponent 3 2 2) • (rowColumnMul HexagonRowColumn322.rows_assocBAC HexagonRowColumn322.cols_right2)) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal3_case_2_2_row_1_0_0 : (((-1 : ℤ) ^ (rightScaleBit 3 2 2).val * positiveScale (rightScaleExponent 3 2 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 2 : ℤ)) • HexagonAtoms322.outerLeftABC) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (negativeScale (rightScaleExponent 3 2 2) • (rowColumnMul HexagonRowColumn322.rows_assocBAC HexagonRowColumn322.cols_right2)) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal3_case_2_2_row_1_0_1 : (((-1 : ℤ) ^ (rightScaleBit 3 2 2).val * positiveScale (rightScaleExponent 3 2 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 2 : ℤ)) • HexagonAtoms322.outerLeftABC) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (negativeScale (rightScaleExponent 3 2 2) • (rowColumnMul HexagonRowColumn322.rows_assocBAC HexagonRowColumn322.cols_right2)) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal3_case_2_2_row_1_1_0 : (((-1 : ℤ) ^ (rightScaleBit 3 2 2).val * positiveScale (rightScaleExponent 3 2 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 2 : ℤ)) • HexagonAtoms322.outerLeftABC) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (negativeScale (rightScaleExponent 3 2 2) • (rowColumnMul HexagonRowColumn322.rows_assocBAC HexagonRowColumn322.cols_right2)) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal3_case_2_2_row_1_1_1 : (((-1 : ℤ) ^ (rightScaleBit 3 2 2).val * positiveScale (rightScaleExponent 3 2 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 2 : ℤ)) • HexagonAtoms322.outerLeftABC) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (negativeScale (rightScaleExponent 3 2 2) • (rowColumnMul HexagonRowColumn322.rows_assocBAC HexagonRowColumn322.cols_right2)) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal3_case_2_2_row_1_2_0 : (((-1 : ℤ) ^ (rightScaleBit 3 2 2).val * positiveScale (rightScaleExponent 3 2 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 2 : ℤ)) • HexagonAtoms322.outerLeftABC) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (negativeScale (rightScaleExponent 3 2 2) • (rowColumnMul HexagonRowColumn322.rows_assocBAC HexagonRowColumn322.cols_right2)) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal3_case_2_2_row_1_2_1 : (((-1 : ℤ) ^ (rightScaleBit 3 2 2).val * positiveScale (rightScaleExponent 3 2 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 2 : ℤ)) • HexagonAtoms322.outerLeftABC) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (negativeScale (rightScaleExponent 3 2 2) • (rowColumnMul HexagonRowColumn322.rows_assocBAC HexagonRowColumn322.cols_right2)) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal3_case_2_2_row_1_3_0 : (((-1 : ℤ) ^ (rightScaleBit 3 2 2).val * positiveScale (rightScaleExponent 3 2 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 2 : ℤ)) • HexagonAtoms322.outerLeftABC) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (negativeScale (rightScaleExponent 3 2 2) • (rowColumnMul HexagonRowColumn322.rows_assocBAC HexagonRowColumn322.cols_right2)) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal3_case_2_2_row_1_3_1 : (((-1 : ℤ) ^ (rightScaleBit 3 2 2).val * positiveScale (rightScaleExponent 3 2 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 2 : ℤ)) • HexagonAtoms322.outerLeftABC) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (negativeScale (rightScaleExponent 3 2 2) • (rowColumnMul HexagonRowColumn322.rows_assocBAC HexagonRowColumn322.cols_right2)) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal3_case_2_2_checked : ((-1 : ℤ) ^ (rightScaleBit 3 2 2).val * positiveScale (rightScaleExponent 3 2 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 2 : ℤ)) • HexagonAtoms322.outerLeftABC = negativeScale (rightScaleExponent 3 2 2) • (rowColumnMul HexagonRowColumn322.rows_assocBAC HexagonRowColumn322.cols_right2) := by
  funext r
  fin_cases r
  · exact rightFinal3_case_2_2_row_0_0_0
  · exact rightFinal3_case_2_2_row_0_0_1
  · exact rightFinal3_case_2_2_row_0_1_0
  · exact rightFinal3_case_2_2_row_0_1_1
  · exact rightFinal3_case_2_2_row_0_2_0
  · exact rightFinal3_case_2_2_row_0_2_1
  · exact rightFinal3_case_2_2_row_0_3_0
  · exact rightFinal3_case_2_2_row_0_3_1
  · exact rightFinal3_case_2_2_row_1_0_0
  · exact rightFinal3_case_2_2_row_1_0_1
  · exact rightFinal3_case_2_2_row_1_1_0
  · exact rightFinal3_case_2_2_row_1_1_1
  · exact rightFinal3_case_2_2_row_1_2_0
  · exact rightFinal3_case_2_2_row_1_2_1
  · exact rightFinal3_case_2_2_row_1_3_0
  · exact rightFinal3_case_2_2_row_1_3_1

set_option backward.isDefEq.respectTransparency false in
theorem rightFinal3_case_2_2 : ((-1 : ℤ) ^ (rightScaleBit 3 2 2).val * positiveScale (rightScaleExponent 3 2 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 2 : ℤ)) • outerLeftZ 3 2 2 = negativeScale (rightScaleExponent 3 2 2) • (associatorZ 2 3 2 * right2Middle3 2 2) := by
  simpa only [HexagonAtoms322.assocABC_eq,
    HexagonAtoms322.outerABC_eq,
    HexagonAtoms322.assocBAC_eq,
    HexagonAtoms322.innerABC_eq,
    HexagonAtoms322.innerRightABC_eq,
    HexagonAtoms322.inverseACB_eq,
    HexagonAtoms322.innerACB_eq,
    HexagonAtoms322.assocBCA_eq,
    HexagonAtoms322.innerRightBAC_eq,
    HexagonAtoms322.assocCAB_eq,
    HexagonAtoms322.outerLeftABC_eq,
    HexagonRowColumn322.innerACB_alias,
    HexagonRowColumn322.assocCAB_alias,
    HexagonRowColumn322.product0_eq,
    HexagonRowColumn322.product1_eq,
    HexagonRowColumn322.product2_eq,
    HexagonRowColumn322.product3_eq,
    HexagonRowColumn322.product4_eq,
    HexagonRowColumn322.product5_eq,
    HexagonRowColumn322.product6_eq,
    HexagonRowColumn322.product7_eq] using rightFinal3_case_2_2_checked

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonCases3
