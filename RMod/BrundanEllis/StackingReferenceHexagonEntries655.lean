import RMod.BrundanEllis.StackingReferenceHexagonMiddle6
import RMod.BrundanEllis.StackingReferenceSparseMatrixCheck
import RMod.BrundanEllis.StackingReferenceHexagonAtoms655
import RMod.BrundanEllis.StackingReferenceHexagonRowColumn655

/-! Seven closed product identities for one reference triple.
The proof uses only verified atomic maps and ordinary kernel reduction. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
set_option linter.unusedSimpArgs false
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonCases6
open Superfusion

private theorem left0Middle6_eq_case_5_5_row_0_0_0 : (left0Middle6 5 5) ((0 : Fin 4), (0 : Fin 4), (0 : Fin 1)) = (HexagonAtoms655.assocABC) ((0 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem left0Middle6_eq_case_5_5_row_0_1_0 : (left0Middle6 5 5) ((0 : Fin 4), (1 : Fin 4), (0 : Fin 1)) = (HexagonAtoms655.assocABC) ((0 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem left0Middle6_eq_case_5_5_row_0_2_0 : (left0Middle6 5 5) ((0 : Fin 4), (2 : Fin 4), (0 : Fin 1)) = (HexagonAtoms655.assocABC) ((0 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem left0Middle6_eq_case_5_5_row_0_3_0 : (left0Middle6 5 5) ((0 : Fin 4), (3 : Fin 4), (0 : Fin 1)) = (HexagonAtoms655.assocABC) ((0 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem left0Middle6_eq_case_5_5_row_1_0_0 : (left0Middle6 5 5) ((1 : Fin 4), (0 : Fin 4), (0 : Fin 1)) = (HexagonAtoms655.assocABC) ((1 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem left0Middle6_eq_case_5_5_row_1_1_0 : (left0Middle6 5 5) ((1 : Fin 4), (1 : Fin 4), (0 : Fin 1)) = (HexagonAtoms655.assocABC) ((1 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem left0Middle6_eq_case_5_5_row_1_2_0 : (left0Middle6 5 5) ((1 : Fin 4), (2 : Fin 4), (0 : Fin 1)) = (HexagonAtoms655.assocABC) ((1 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem left0Middle6_eq_case_5_5_row_1_3_0 : (left0Middle6 5 5) ((1 : Fin 4), (3 : Fin 4), (0 : Fin 1)) = (HexagonAtoms655.assocABC) ((1 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem left0Middle6_eq_case_5_5_row_2_0_0 : (left0Middle6 5 5) ((2 : Fin 4), (0 : Fin 4), (0 : Fin 1)) = (HexagonAtoms655.assocABC) ((2 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem left0Middle6_eq_case_5_5_row_2_1_0 : (left0Middle6 5 5) ((2 : Fin 4), (1 : Fin 4), (0 : Fin 1)) = (HexagonAtoms655.assocABC) ((2 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem left0Middle6_eq_case_5_5_row_2_2_0 : (left0Middle6 5 5) ((2 : Fin 4), (2 : Fin 4), (0 : Fin 1)) = (HexagonAtoms655.assocABC) ((2 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem left0Middle6_eq_case_5_5_row_2_3_0 : (left0Middle6 5 5) ((2 : Fin 4), (3 : Fin 4), (0 : Fin 1)) = (HexagonAtoms655.assocABC) ((2 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem left0Middle6_eq_case_5_5_row_3_0_0 : (left0Middle6 5 5) ((3 : Fin 4), (0 : Fin 4), (0 : Fin 1)) = (HexagonAtoms655.assocABC) ((3 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem left0Middle6_eq_case_5_5_row_3_1_0 : (left0Middle6 5 5) ((3 : Fin 4), (1 : Fin 4), (0 : Fin 1)) = (HexagonAtoms655.assocABC) ((3 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem left0Middle6_eq_case_5_5_row_3_2_0 : (left0Middle6 5 5) ((3 : Fin 4), (2 : Fin 4), (0 : Fin 1)) = (HexagonAtoms655.assocABC) ((3 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem left0Middle6_eq_case_5_5_row_3_3_0 : (left0Middle6 5 5) ((3 : Fin 4), (3 : Fin 4), (0 : Fin 1)) = (HexagonAtoms655.assocABC) ((3 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem left0Middle6_eq_case_5_5_checked : left0Middle6 5 5 = HexagonAtoms655.assocABC := by
  funext r
  fin_cases r
  · exact left0Middle6_eq_case_5_5_row_0_0_0
  · exact left0Middle6_eq_case_5_5_row_0_1_0
  · exact left0Middle6_eq_case_5_5_row_0_2_0
  · exact left0Middle6_eq_case_5_5_row_0_3_0
  · exact left0Middle6_eq_case_5_5_row_1_0_0
  · exact left0Middle6_eq_case_5_5_row_1_1_0
  · exact left0Middle6_eq_case_5_5_row_1_2_0
  · exact left0Middle6_eq_case_5_5_row_1_3_0
  · exact left0Middle6_eq_case_5_5_row_2_0_0
  · exact left0Middle6_eq_case_5_5_row_2_1_0
  · exact left0Middle6_eq_case_5_5_row_2_2_0
  · exact left0Middle6_eq_case_5_5_row_2_3_0
  · exact left0Middle6_eq_case_5_5_row_3_0_0
  · exact left0Middle6_eq_case_5_5_row_3_1_0
  · exact left0Middle6_eq_case_5_5_row_3_2_0
  · exact left0Middle6_eq_case_5_5_row_3_3_0

set_option backward.isDefEq.respectTransparency false in
theorem left0Middle6_eq_case_5_5 : left0Middle6 5 5 = outerRightZ 6 5 5 * associatorZ 6 5 5 := by
  simpa only [HexagonAtoms655.assocABC_eq,
    HexagonAtoms655.outerABC_eq,
    HexagonAtoms655.assocBAC_eq,
    HexagonAtoms655.innerABC_eq,
    HexagonAtoms655.innerRightABC_eq,
    HexagonAtoms655.inverseACB_eq,
    HexagonAtoms655.innerACB_eq,
    HexagonAtoms655.assocBCA_eq,
    HexagonAtoms655.innerRightBAC_eq,
    HexagonAtoms655.assocCAB_eq,
    HexagonAtoms655.outerLeftABC_eq,
    HexagonRowColumn655.innerACB_alias,
    HexagonRowColumn655.assocCAB_alias,
    HexagonRowColumn655.product0_eq,
    HexagonRowColumn655.product1_eq,
    HexagonRowColumn655.product2_eq,
    HexagonRowColumn655.product3_eq,
    HexagonRowColumn655.product4_eq,
    HexagonRowColumn655.product5_eq,
    HexagonRowColumn655.product6_eq,
    HexagonRowColumn655.product7_eq] using left0Middle6_eq_case_5_5_checked

private theorem left1Middle6_eq_case_5_5_row_0_0_0 : (left1Middle6 5 5) ((0 : Fin 2), (0 : Fin 8), (0 : Fin 1)) = (HexagonAtoms655.assocBAC) ((0 : Fin 2), (0 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem left1Middle6_eq_case_5_5_row_0_1_0 : (left1Middle6 5 5) ((0 : Fin 2), (1 : Fin 8), (0 : Fin 1)) = (HexagonAtoms655.assocBAC) ((0 : Fin 2), (1 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem left1Middle6_eq_case_5_5_row_0_2_0 : (left1Middle6 5 5) ((0 : Fin 2), (2 : Fin 8), (0 : Fin 1)) = (HexagonAtoms655.assocBAC) ((0 : Fin 2), (2 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem left1Middle6_eq_case_5_5_row_0_3_0 : (left1Middle6 5 5) ((0 : Fin 2), (3 : Fin 8), (0 : Fin 1)) = (HexagonAtoms655.assocBAC) ((0 : Fin 2), (3 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem left1Middle6_eq_case_5_5_row_0_4_0 : (left1Middle6 5 5) ((0 : Fin 2), (4 : Fin 8), (0 : Fin 1)) = (HexagonAtoms655.assocBAC) ((0 : Fin 2), (4 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem left1Middle6_eq_case_5_5_row_0_5_0 : (left1Middle6 5 5) ((0 : Fin 2), (5 : Fin 8), (0 : Fin 1)) = (HexagonAtoms655.assocBAC) ((0 : Fin 2), (5 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem left1Middle6_eq_case_5_5_row_0_6_0 : (left1Middle6 5 5) ((0 : Fin 2), (6 : Fin 8), (0 : Fin 1)) = (HexagonAtoms655.assocBAC) ((0 : Fin 2), (6 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem left1Middle6_eq_case_5_5_row_0_7_0 : (left1Middle6 5 5) ((0 : Fin 2), (7 : Fin 8), (0 : Fin 1)) = (HexagonAtoms655.assocBAC) ((0 : Fin 2), (7 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem left1Middle6_eq_case_5_5_row_1_0_0 : (left1Middle6 5 5) ((1 : Fin 2), (0 : Fin 8), (0 : Fin 1)) = (HexagonAtoms655.assocBAC) ((1 : Fin 2), (0 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem left1Middle6_eq_case_5_5_row_1_1_0 : (left1Middle6 5 5) ((1 : Fin 2), (1 : Fin 8), (0 : Fin 1)) = (HexagonAtoms655.assocBAC) ((1 : Fin 2), (1 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem left1Middle6_eq_case_5_5_row_1_2_0 : (left1Middle6 5 5) ((1 : Fin 2), (2 : Fin 8), (0 : Fin 1)) = (HexagonAtoms655.assocBAC) ((1 : Fin 2), (2 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem left1Middle6_eq_case_5_5_row_1_3_0 : (left1Middle6 5 5) ((1 : Fin 2), (3 : Fin 8), (0 : Fin 1)) = (HexagonAtoms655.assocBAC) ((1 : Fin 2), (3 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem left1Middle6_eq_case_5_5_row_1_4_0 : (left1Middle6 5 5) ((1 : Fin 2), (4 : Fin 8), (0 : Fin 1)) = (HexagonAtoms655.assocBAC) ((1 : Fin 2), (4 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem left1Middle6_eq_case_5_5_row_1_5_0 : (left1Middle6 5 5) ((1 : Fin 2), (5 : Fin 8), (0 : Fin 1)) = (HexagonAtoms655.assocBAC) ((1 : Fin 2), (5 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem left1Middle6_eq_case_5_5_row_1_6_0 : (left1Middle6 5 5) ((1 : Fin 2), (6 : Fin 8), (0 : Fin 1)) = (HexagonAtoms655.assocBAC) ((1 : Fin 2), (6 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem left1Middle6_eq_case_5_5_row_1_7_0 : (left1Middle6 5 5) ((1 : Fin 2), (7 : Fin 8), (0 : Fin 1)) = (HexagonAtoms655.assocBAC) ((1 : Fin 2), (7 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem left1Middle6_eq_case_5_5_checked : left1Middle6 5 5 = HexagonAtoms655.assocBAC := by
  funext r
  fin_cases r
  · exact left1Middle6_eq_case_5_5_row_0_0_0
  · exact left1Middle6_eq_case_5_5_row_0_1_0
  · exact left1Middle6_eq_case_5_5_row_0_2_0
  · exact left1Middle6_eq_case_5_5_row_0_3_0
  · exact left1Middle6_eq_case_5_5_row_0_4_0
  · exact left1Middle6_eq_case_5_5_row_0_5_0
  · exact left1Middle6_eq_case_5_5_row_0_6_0
  · exact left1Middle6_eq_case_5_5_row_0_7_0
  · exact left1Middle6_eq_case_5_5_row_1_0_0
  · exact left1Middle6_eq_case_5_5_row_1_1_0
  · exact left1Middle6_eq_case_5_5_row_1_2_0
  · exact left1Middle6_eq_case_5_5_row_1_3_0
  · exact left1Middle6_eq_case_5_5_row_1_4_0
  · exact left1Middle6_eq_case_5_5_row_1_5_0
  · exact left1Middle6_eq_case_5_5_row_1_6_0
  · exact left1Middle6_eq_case_5_5_row_1_7_0

set_option backward.isDefEq.respectTransparency false in
theorem left1Middle6_eq_case_5_5 : left1Middle6 5 5 = associatorZ 5 6 5 * innerLeftZ 6 5 5 := by
  simpa only [HexagonAtoms655.assocABC_eq,
    HexagonAtoms655.outerABC_eq,
    HexagonAtoms655.assocBAC_eq,
    HexagonAtoms655.innerABC_eq,
    HexagonAtoms655.innerRightABC_eq,
    HexagonAtoms655.inverseACB_eq,
    HexagonAtoms655.innerACB_eq,
    HexagonAtoms655.assocBCA_eq,
    HexagonAtoms655.innerRightBAC_eq,
    HexagonAtoms655.assocCAB_eq,
    HexagonAtoms655.outerLeftABC_eq,
    HexagonRowColumn655.innerACB_alias,
    HexagonRowColumn655.assocCAB_alias,
    HexagonRowColumn655.product0_eq,
    HexagonRowColumn655.product1_eq,
    HexagonRowColumn655.product2_eq,
    HexagonRowColumn655.product3_eq,
    HexagonRowColumn655.product4_eq,
    HexagonRowColumn655.product5_eq,
    HexagonRowColumn655.product6_eq,
    HexagonRowColumn655.product7_eq] using left1Middle6_eq_case_5_5_checked

private theorem right0Middle6_eq_case_5_5_row_0_0_0 : (right0Middle6 5 5) ((0 : Fin 4), (0 : Fin 4), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn655.rows_innerRightABC HexagonRowColumn655.cols_assocABC) ((0 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right0Middle6_eq_case_5_5_row_0_1_0 : (right0Middle6 5 5) ((0 : Fin 4), (1 : Fin 4), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn655.rows_innerRightABC HexagonRowColumn655.cols_assocABC) ((0 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right0Middle6_eq_case_5_5_row_0_2_0 : (right0Middle6 5 5) ((0 : Fin 4), (2 : Fin 4), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn655.rows_innerRightABC HexagonRowColumn655.cols_assocABC) ((0 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right0Middle6_eq_case_5_5_row_0_3_0 : (right0Middle6 5 5) ((0 : Fin 4), (3 : Fin 4), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn655.rows_innerRightABC HexagonRowColumn655.cols_assocABC) ((0 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right0Middle6_eq_case_5_5_row_1_0_0 : (right0Middle6 5 5) ((1 : Fin 4), (0 : Fin 4), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn655.rows_innerRightABC HexagonRowColumn655.cols_assocABC) ((1 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right0Middle6_eq_case_5_5_row_1_1_0 : (right0Middle6 5 5) ((1 : Fin 4), (1 : Fin 4), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn655.rows_innerRightABC HexagonRowColumn655.cols_assocABC) ((1 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right0Middle6_eq_case_5_5_row_1_2_0 : (right0Middle6 5 5) ((1 : Fin 4), (2 : Fin 4), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn655.rows_innerRightABC HexagonRowColumn655.cols_assocABC) ((1 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right0Middle6_eq_case_5_5_row_1_3_0 : (right0Middle6 5 5) ((1 : Fin 4), (3 : Fin 4), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn655.rows_innerRightABC HexagonRowColumn655.cols_assocABC) ((1 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right0Middle6_eq_case_5_5_row_2_0_0 : (right0Middle6 5 5) ((2 : Fin 4), (0 : Fin 4), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn655.rows_innerRightABC HexagonRowColumn655.cols_assocABC) ((2 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right0Middle6_eq_case_5_5_row_2_1_0 : (right0Middle6 5 5) ((2 : Fin 4), (1 : Fin 4), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn655.rows_innerRightABC HexagonRowColumn655.cols_assocABC) ((2 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right0Middle6_eq_case_5_5_row_2_2_0 : (right0Middle6 5 5) ((2 : Fin 4), (2 : Fin 4), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn655.rows_innerRightABC HexagonRowColumn655.cols_assocABC) ((2 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right0Middle6_eq_case_5_5_row_2_3_0 : (right0Middle6 5 5) ((2 : Fin 4), (3 : Fin 4), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn655.rows_innerRightABC HexagonRowColumn655.cols_assocABC) ((2 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right0Middle6_eq_case_5_5_row_3_0_0 : (right0Middle6 5 5) ((3 : Fin 4), (0 : Fin 4), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn655.rows_innerRightABC HexagonRowColumn655.cols_assocABC) ((3 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right0Middle6_eq_case_5_5_row_3_1_0 : (right0Middle6 5 5) ((3 : Fin 4), (1 : Fin 4), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn655.rows_innerRightABC HexagonRowColumn655.cols_assocABC) ((3 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right0Middle6_eq_case_5_5_row_3_2_0 : (right0Middle6 5 5) ((3 : Fin 4), (2 : Fin 4), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn655.rows_innerRightABC HexagonRowColumn655.cols_assocABC) ((3 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right0Middle6_eq_case_5_5_row_3_3_0 : (right0Middle6 5 5) ((3 : Fin 4), (3 : Fin 4), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn655.rows_innerRightABC HexagonRowColumn655.cols_assocABC) ((3 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right0Middle6_eq_case_5_5_checked : right0Middle6 5 5 = rowColumnMul HexagonRowColumn655.rows_innerRightABC HexagonRowColumn655.cols_assocABC := by
  funext r
  fin_cases r
  · exact right0Middle6_eq_case_5_5_row_0_0_0
  · exact right0Middle6_eq_case_5_5_row_0_1_0
  · exact right0Middle6_eq_case_5_5_row_0_2_0
  · exact right0Middle6_eq_case_5_5_row_0_3_0
  · exact right0Middle6_eq_case_5_5_row_1_0_0
  · exact right0Middle6_eq_case_5_5_row_1_1_0
  · exact right0Middle6_eq_case_5_5_row_1_2_0
  · exact right0Middle6_eq_case_5_5_row_1_3_0
  · exact right0Middle6_eq_case_5_5_row_2_0_0
  · exact right0Middle6_eq_case_5_5_row_2_1_0
  · exact right0Middle6_eq_case_5_5_row_2_2_0
  · exact right0Middle6_eq_case_5_5_row_2_3_0
  · exact right0Middle6_eq_case_5_5_row_3_0_0
  · exact right0Middle6_eq_case_5_5_row_3_1_0
  · exact right0Middle6_eq_case_5_5_row_3_2_0
  · exact right0Middle6_eq_case_5_5_row_3_3_0

set_option backward.isDefEq.respectTransparency false in
theorem right0Middle6_eq_case_5_5 : right0Middle6 5 5 = innerRightZ 6 5 5 * associatorZ 6 5 5 := by
  simpa only [HexagonAtoms655.assocABC_eq,
    HexagonAtoms655.outerABC_eq,
    HexagonAtoms655.assocBAC_eq,
    HexagonAtoms655.innerABC_eq,
    HexagonAtoms655.innerRightABC_eq,
    HexagonAtoms655.inverseACB_eq,
    HexagonAtoms655.innerACB_eq,
    HexagonAtoms655.assocBCA_eq,
    HexagonAtoms655.innerRightBAC_eq,
    HexagonAtoms655.assocCAB_eq,
    HexagonAtoms655.outerLeftABC_eq,
    HexagonRowColumn655.innerACB_alias,
    HexagonRowColumn655.assocCAB_alias,
    HexagonRowColumn655.product0_eq,
    HexagonRowColumn655.product1_eq,
    HexagonRowColumn655.product2_eq,
    HexagonRowColumn655.product3_eq,
    HexagonRowColumn655.product4_eq,
    HexagonRowColumn655.product5_eq,
    HexagonRowColumn655.product6_eq,
    HexagonRowColumn655.product7_eq] using right0Middle6_eq_case_5_5_checked

private theorem right1Middle6_eq_case_5_5_row_0_0_0 : (right1Middle6 5 5) ((0 : Fin 2), (0 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn655.rows_inverseACB HexagonRowColumn655.cols_right0) ((0 : Fin 2), (0 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right1Middle6_eq_case_5_5_row_0_1_0 : (right1Middle6 5 5) ((0 : Fin 2), (1 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn655.rows_inverseACB HexagonRowColumn655.cols_right0) ((0 : Fin 2), (1 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right1Middle6_eq_case_5_5_row_0_2_0 : (right1Middle6 5 5) ((0 : Fin 2), (2 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn655.rows_inverseACB HexagonRowColumn655.cols_right0) ((0 : Fin 2), (2 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right1Middle6_eq_case_5_5_row_0_3_0 : (right1Middle6 5 5) ((0 : Fin 2), (3 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn655.rows_inverseACB HexagonRowColumn655.cols_right0) ((0 : Fin 2), (3 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right1Middle6_eq_case_5_5_row_0_4_0 : (right1Middle6 5 5) ((0 : Fin 2), (4 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn655.rows_inverseACB HexagonRowColumn655.cols_right0) ((0 : Fin 2), (4 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right1Middle6_eq_case_5_5_row_0_5_0 : (right1Middle6 5 5) ((0 : Fin 2), (5 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn655.rows_inverseACB HexagonRowColumn655.cols_right0) ((0 : Fin 2), (5 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right1Middle6_eq_case_5_5_row_0_6_0 : (right1Middle6 5 5) ((0 : Fin 2), (6 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn655.rows_inverseACB HexagonRowColumn655.cols_right0) ((0 : Fin 2), (6 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right1Middle6_eq_case_5_5_row_0_7_0 : (right1Middle6 5 5) ((0 : Fin 2), (7 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn655.rows_inverseACB HexagonRowColumn655.cols_right0) ((0 : Fin 2), (7 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right1Middle6_eq_case_5_5_row_1_0_0 : (right1Middle6 5 5) ((1 : Fin 2), (0 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn655.rows_inverseACB HexagonRowColumn655.cols_right0) ((1 : Fin 2), (0 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right1Middle6_eq_case_5_5_row_1_1_0 : (right1Middle6 5 5) ((1 : Fin 2), (1 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn655.rows_inverseACB HexagonRowColumn655.cols_right0) ((1 : Fin 2), (1 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right1Middle6_eq_case_5_5_row_1_2_0 : (right1Middle6 5 5) ((1 : Fin 2), (2 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn655.rows_inverseACB HexagonRowColumn655.cols_right0) ((1 : Fin 2), (2 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right1Middle6_eq_case_5_5_row_1_3_0 : (right1Middle6 5 5) ((1 : Fin 2), (3 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn655.rows_inverseACB HexagonRowColumn655.cols_right0) ((1 : Fin 2), (3 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right1Middle6_eq_case_5_5_row_1_4_0 : (right1Middle6 5 5) ((1 : Fin 2), (4 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn655.rows_inverseACB HexagonRowColumn655.cols_right0) ((1 : Fin 2), (4 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right1Middle6_eq_case_5_5_row_1_5_0 : (right1Middle6 5 5) ((1 : Fin 2), (5 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn655.rows_inverseACB HexagonRowColumn655.cols_right0) ((1 : Fin 2), (5 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right1Middle6_eq_case_5_5_row_1_6_0 : (right1Middle6 5 5) ((1 : Fin 2), (6 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn655.rows_inverseACB HexagonRowColumn655.cols_right0) ((1 : Fin 2), (6 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right1Middle6_eq_case_5_5_row_1_7_0 : (right1Middle6 5 5) ((1 : Fin 2), (7 : Fin 8), (0 : Fin 1)) = (rowColumnMul HexagonRowColumn655.rows_inverseACB HexagonRowColumn655.cols_right0) ((1 : Fin 2), (7 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right1Middle6_eq_case_5_5_checked : right1Middle6 5 5 = rowColumnMul HexagonRowColumn655.rows_inverseACB HexagonRowColumn655.cols_right0 := by
  funext r
  fin_cases r
  · exact right1Middle6_eq_case_5_5_row_0_0_0
  · exact right1Middle6_eq_case_5_5_row_0_1_0
  · exact right1Middle6_eq_case_5_5_row_0_2_0
  · exact right1Middle6_eq_case_5_5_row_0_3_0
  · exact right1Middle6_eq_case_5_5_row_0_4_0
  · exact right1Middle6_eq_case_5_5_row_0_5_0
  · exact right1Middle6_eq_case_5_5_row_0_6_0
  · exact right1Middle6_eq_case_5_5_row_0_7_0
  · exact right1Middle6_eq_case_5_5_row_1_0_0
  · exact right1Middle6_eq_case_5_5_row_1_1_0
  · exact right1Middle6_eq_case_5_5_row_1_2_0
  · exact right1Middle6_eq_case_5_5_row_1_3_0
  · exact right1Middle6_eq_case_5_5_row_1_4_0
  · exact right1Middle6_eq_case_5_5_row_1_5_0
  · exact right1Middle6_eq_case_5_5_row_1_6_0
  · exact right1Middle6_eq_case_5_5_row_1_7_0

set_option backward.isDefEq.respectTransparency false in
theorem right1Middle6_eq_case_5_5 : right1Middle6 5 5 = associatorInverseZ 6 5 5 * right0Middle6 5 5 := by
  simpa only [HexagonAtoms655.assocABC_eq,
    HexagonAtoms655.outerABC_eq,
    HexagonAtoms655.assocBAC_eq,
    HexagonAtoms655.innerABC_eq,
    HexagonAtoms655.innerRightABC_eq,
    HexagonAtoms655.inverseACB_eq,
    HexagonAtoms655.innerACB_eq,
    HexagonAtoms655.assocBCA_eq,
    HexagonAtoms655.innerRightBAC_eq,
    HexagonAtoms655.assocCAB_eq,
    HexagonAtoms655.outerLeftABC_eq,
    HexagonRowColumn655.innerACB_alias,
    HexagonRowColumn655.assocCAB_alias,
    HexagonRowColumn655.product0_eq,
    HexagonRowColumn655.product1_eq,
    HexagonRowColumn655.product2_eq,
    HexagonRowColumn655.product3_eq,
    HexagonRowColumn655.product4_eq,
    HexagonRowColumn655.product5_eq,
    HexagonRowColumn655.product6_eq,
    HexagonRowColumn655.product7_eq] using right1Middle6_eq_case_5_5_checked

private theorem right2Middle6_eq_case_5_5_row_0_0_0 : (right2Middle6 5 5) ((0 : Fin 2), (0 : Fin 8), (0 : Fin 1)) = (right1Middle6 5 5) ((0 : Fin 2), (0 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right2Middle6_eq_case_5_5_row_0_1_0 : (right2Middle6 5 5) ((0 : Fin 2), (1 : Fin 8), (0 : Fin 1)) = (right1Middle6 5 5) ((0 : Fin 2), (1 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right2Middle6_eq_case_5_5_row_0_2_0 : (right2Middle6 5 5) ((0 : Fin 2), (2 : Fin 8), (0 : Fin 1)) = (right1Middle6 5 5) ((0 : Fin 2), (2 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right2Middle6_eq_case_5_5_row_0_3_0 : (right2Middle6 5 5) ((0 : Fin 2), (3 : Fin 8), (0 : Fin 1)) = (right1Middle6 5 5) ((0 : Fin 2), (3 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right2Middle6_eq_case_5_5_row_0_4_0 : (right2Middle6 5 5) ((0 : Fin 2), (4 : Fin 8), (0 : Fin 1)) = (right1Middle6 5 5) ((0 : Fin 2), (4 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right2Middle6_eq_case_5_5_row_0_5_0 : (right2Middle6 5 5) ((0 : Fin 2), (5 : Fin 8), (0 : Fin 1)) = (right1Middle6 5 5) ((0 : Fin 2), (5 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right2Middle6_eq_case_5_5_row_0_6_0 : (right2Middle6 5 5) ((0 : Fin 2), (6 : Fin 8), (0 : Fin 1)) = (right1Middle6 5 5) ((0 : Fin 2), (6 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right2Middle6_eq_case_5_5_row_0_7_0 : (right2Middle6 5 5) ((0 : Fin 2), (7 : Fin 8), (0 : Fin 1)) = (right1Middle6 5 5) ((0 : Fin 2), (7 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right2Middle6_eq_case_5_5_row_1_0_0 : (right2Middle6 5 5) ((1 : Fin 2), (0 : Fin 8), (0 : Fin 1)) = (right1Middle6 5 5) ((1 : Fin 2), (0 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right2Middle6_eq_case_5_5_row_1_1_0 : (right2Middle6 5 5) ((1 : Fin 2), (1 : Fin 8), (0 : Fin 1)) = (right1Middle6 5 5) ((1 : Fin 2), (1 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right2Middle6_eq_case_5_5_row_1_2_0 : (right2Middle6 5 5) ((1 : Fin 2), (2 : Fin 8), (0 : Fin 1)) = (right1Middle6 5 5) ((1 : Fin 2), (2 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right2Middle6_eq_case_5_5_row_1_3_0 : (right2Middle6 5 5) ((1 : Fin 2), (3 : Fin 8), (0 : Fin 1)) = (right1Middle6 5 5) ((1 : Fin 2), (3 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right2Middle6_eq_case_5_5_row_1_4_0 : (right2Middle6 5 5) ((1 : Fin 2), (4 : Fin 8), (0 : Fin 1)) = (right1Middle6 5 5) ((1 : Fin 2), (4 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right2Middle6_eq_case_5_5_row_1_5_0 : (right2Middle6 5 5) ((1 : Fin 2), (5 : Fin 8), (0 : Fin 1)) = (right1Middle6 5 5) ((1 : Fin 2), (5 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right2Middle6_eq_case_5_5_row_1_6_0 : (right2Middle6 5 5) ((1 : Fin 2), (6 : Fin 8), (0 : Fin 1)) = (right1Middle6 5 5) ((1 : Fin 2), (6 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right2Middle6_eq_case_5_5_row_1_7_0 : (right2Middle6 5 5) ((1 : Fin 2), (7 : Fin 8), (0 : Fin 1)) = (right1Middle6 5 5) ((1 : Fin 2), (7 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem right2Middle6_eq_case_5_5_checked : right2Middle6 5 5 = right1Middle6 5 5 := by
  funext r
  fin_cases r
  · exact right2Middle6_eq_case_5_5_row_0_0_0
  · exact right2Middle6_eq_case_5_5_row_0_1_0
  · exact right2Middle6_eq_case_5_5_row_0_2_0
  · exact right2Middle6_eq_case_5_5_row_0_3_0
  · exact right2Middle6_eq_case_5_5_row_0_4_0
  · exact right2Middle6_eq_case_5_5_row_0_5_0
  · exact right2Middle6_eq_case_5_5_row_0_6_0
  · exact right2Middle6_eq_case_5_5_row_0_7_0
  · exact right2Middle6_eq_case_5_5_row_1_0_0
  · exact right2Middle6_eq_case_5_5_row_1_1_0
  · exact right2Middle6_eq_case_5_5_row_1_2_0
  · exact right2Middle6_eq_case_5_5_row_1_3_0
  · exact right2Middle6_eq_case_5_5_row_1_4_0
  · exact right2Middle6_eq_case_5_5_row_1_5_0
  · exact right2Middle6_eq_case_5_5_row_1_6_0
  · exact right2Middle6_eq_case_5_5_row_1_7_0

set_option backward.isDefEq.respectTransparency false in
theorem right2Middle6_eq_case_5_5 : right2Middle6 5 5 = innerLeftZ 6 5 5 * right1Middle6 5 5 := by
  simpa only [HexagonAtoms655.assocABC_eq,
    HexagonAtoms655.outerABC_eq,
    HexagonAtoms655.assocBAC_eq,
    HexagonAtoms655.innerABC_eq,
    HexagonAtoms655.innerRightABC_eq,
    HexagonAtoms655.inverseACB_eq,
    HexagonAtoms655.innerACB_eq,
    HexagonAtoms655.assocBCA_eq,
    HexagonAtoms655.innerRightBAC_eq,
    HexagonAtoms655.assocCAB_eq,
    HexagonAtoms655.outerLeftABC_eq,
    HexagonRowColumn655.innerACB_alias,
    HexagonRowColumn655.assocCAB_alias,
    HexagonRowColumn655.product0_eq,
    HexagonRowColumn655.product1_eq,
    HexagonRowColumn655.product2_eq,
    HexagonRowColumn655.product3_eq,
    HexagonRowColumn655.product4_eq,
    HexagonRowColumn655.product5_eq,
    HexagonRowColumn655.product6_eq,
    HexagonRowColumn655.product7_eq] using right2Middle6_eq_case_5_5_checked

private theorem leftFinal6_case_5_5_row_0_0_0 : (((-1 : ℤ) ^ (leftScaleBit 6 5 5).val * positiveScale (leftScaleExponent 6 5 5)) •
      (rowColumnMul HexagonRowColumn655.rows_assocBCA HexagonRowColumn655.cols_left0)) ((0 : Fin 2), (0 : Fin 8), (0 : Fin 1)) = (negativeScale (leftScaleExponent 6 5 5) • (left1Middle6 5 5)) ((0 : Fin 2), (0 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem leftFinal6_case_5_5_row_0_1_0 : (((-1 : ℤ) ^ (leftScaleBit 6 5 5).val * positiveScale (leftScaleExponent 6 5 5)) •
      (rowColumnMul HexagonRowColumn655.rows_assocBCA HexagonRowColumn655.cols_left0)) ((0 : Fin 2), (1 : Fin 8), (0 : Fin 1)) = (negativeScale (leftScaleExponent 6 5 5) • (left1Middle6 5 5)) ((0 : Fin 2), (1 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem leftFinal6_case_5_5_row_0_2_0 : (((-1 : ℤ) ^ (leftScaleBit 6 5 5).val * positiveScale (leftScaleExponent 6 5 5)) •
      (rowColumnMul HexagonRowColumn655.rows_assocBCA HexagonRowColumn655.cols_left0)) ((0 : Fin 2), (2 : Fin 8), (0 : Fin 1)) = (negativeScale (leftScaleExponent 6 5 5) • (left1Middle6 5 5)) ((0 : Fin 2), (2 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem leftFinal6_case_5_5_row_0_3_0 : (((-1 : ℤ) ^ (leftScaleBit 6 5 5).val * positiveScale (leftScaleExponent 6 5 5)) •
      (rowColumnMul HexagonRowColumn655.rows_assocBCA HexagonRowColumn655.cols_left0)) ((0 : Fin 2), (3 : Fin 8), (0 : Fin 1)) = (negativeScale (leftScaleExponent 6 5 5) • (left1Middle6 5 5)) ((0 : Fin 2), (3 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem leftFinal6_case_5_5_row_0_4_0 : (((-1 : ℤ) ^ (leftScaleBit 6 5 5).val * positiveScale (leftScaleExponent 6 5 5)) •
      (rowColumnMul HexagonRowColumn655.rows_assocBCA HexagonRowColumn655.cols_left0)) ((0 : Fin 2), (4 : Fin 8), (0 : Fin 1)) = (negativeScale (leftScaleExponent 6 5 5) • (left1Middle6 5 5)) ((0 : Fin 2), (4 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem leftFinal6_case_5_5_row_0_5_0 : (((-1 : ℤ) ^ (leftScaleBit 6 5 5).val * positiveScale (leftScaleExponent 6 5 5)) •
      (rowColumnMul HexagonRowColumn655.rows_assocBCA HexagonRowColumn655.cols_left0)) ((0 : Fin 2), (5 : Fin 8), (0 : Fin 1)) = (negativeScale (leftScaleExponent 6 5 5) • (left1Middle6 5 5)) ((0 : Fin 2), (5 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem leftFinal6_case_5_5_row_0_6_0 : (((-1 : ℤ) ^ (leftScaleBit 6 5 5).val * positiveScale (leftScaleExponent 6 5 5)) •
      (rowColumnMul HexagonRowColumn655.rows_assocBCA HexagonRowColumn655.cols_left0)) ((0 : Fin 2), (6 : Fin 8), (0 : Fin 1)) = (negativeScale (leftScaleExponent 6 5 5) • (left1Middle6 5 5)) ((0 : Fin 2), (6 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem leftFinal6_case_5_5_row_0_7_0 : (((-1 : ℤ) ^ (leftScaleBit 6 5 5).val * positiveScale (leftScaleExponent 6 5 5)) •
      (rowColumnMul HexagonRowColumn655.rows_assocBCA HexagonRowColumn655.cols_left0)) ((0 : Fin 2), (7 : Fin 8), (0 : Fin 1)) = (negativeScale (leftScaleExponent 6 5 5) • (left1Middle6 5 5)) ((0 : Fin 2), (7 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem leftFinal6_case_5_5_row_1_0_0 : (((-1 : ℤ) ^ (leftScaleBit 6 5 5).val * positiveScale (leftScaleExponent 6 5 5)) •
      (rowColumnMul HexagonRowColumn655.rows_assocBCA HexagonRowColumn655.cols_left0)) ((1 : Fin 2), (0 : Fin 8), (0 : Fin 1)) = (negativeScale (leftScaleExponent 6 5 5) • (left1Middle6 5 5)) ((1 : Fin 2), (0 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem leftFinal6_case_5_5_row_1_1_0 : (((-1 : ℤ) ^ (leftScaleBit 6 5 5).val * positiveScale (leftScaleExponent 6 5 5)) •
      (rowColumnMul HexagonRowColumn655.rows_assocBCA HexagonRowColumn655.cols_left0)) ((1 : Fin 2), (1 : Fin 8), (0 : Fin 1)) = (negativeScale (leftScaleExponent 6 5 5) • (left1Middle6 5 5)) ((1 : Fin 2), (1 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem leftFinal6_case_5_5_row_1_2_0 : (((-1 : ℤ) ^ (leftScaleBit 6 5 5).val * positiveScale (leftScaleExponent 6 5 5)) •
      (rowColumnMul HexagonRowColumn655.rows_assocBCA HexagonRowColumn655.cols_left0)) ((1 : Fin 2), (2 : Fin 8), (0 : Fin 1)) = (negativeScale (leftScaleExponent 6 5 5) • (left1Middle6 5 5)) ((1 : Fin 2), (2 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem leftFinal6_case_5_5_row_1_3_0 : (((-1 : ℤ) ^ (leftScaleBit 6 5 5).val * positiveScale (leftScaleExponent 6 5 5)) •
      (rowColumnMul HexagonRowColumn655.rows_assocBCA HexagonRowColumn655.cols_left0)) ((1 : Fin 2), (3 : Fin 8), (0 : Fin 1)) = (negativeScale (leftScaleExponent 6 5 5) • (left1Middle6 5 5)) ((1 : Fin 2), (3 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem leftFinal6_case_5_5_row_1_4_0 : (((-1 : ℤ) ^ (leftScaleBit 6 5 5).val * positiveScale (leftScaleExponent 6 5 5)) •
      (rowColumnMul HexagonRowColumn655.rows_assocBCA HexagonRowColumn655.cols_left0)) ((1 : Fin 2), (4 : Fin 8), (0 : Fin 1)) = (negativeScale (leftScaleExponent 6 5 5) • (left1Middle6 5 5)) ((1 : Fin 2), (4 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem leftFinal6_case_5_5_row_1_5_0 : (((-1 : ℤ) ^ (leftScaleBit 6 5 5).val * positiveScale (leftScaleExponent 6 5 5)) •
      (rowColumnMul HexagonRowColumn655.rows_assocBCA HexagonRowColumn655.cols_left0)) ((1 : Fin 2), (5 : Fin 8), (0 : Fin 1)) = (negativeScale (leftScaleExponent 6 5 5) • (left1Middle6 5 5)) ((1 : Fin 2), (5 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem leftFinal6_case_5_5_row_1_6_0 : (((-1 : ℤ) ^ (leftScaleBit 6 5 5).val * positiveScale (leftScaleExponent 6 5 5)) •
      (rowColumnMul HexagonRowColumn655.rows_assocBCA HexagonRowColumn655.cols_left0)) ((1 : Fin 2), (6 : Fin 8), (0 : Fin 1)) = (negativeScale (leftScaleExponent 6 5 5) • (left1Middle6 5 5)) ((1 : Fin 2), (6 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem leftFinal6_case_5_5_row_1_7_0 : (((-1 : ℤ) ^ (leftScaleBit 6 5 5).val * positiveScale (leftScaleExponent 6 5 5)) •
      (rowColumnMul HexagonRowColumn655.rows_assocBCA HexagonRowColumn655.cols_left0)) ((1 : Fin 2), (7 : Fin 8), (0 : Fin 1)) = (negativeScale (leftScaleExponent 6 5 5) • (left1Middle6 5 5)) ((1 : Fin 2), (7 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem leftFinal6_case_5_5_checked : ((-1 : ℤ) ^ (leftScaleBit 6 5 5).val * positiveScale (leftScaleExponent 6 5 5)) •
      (rowColumnMul HexagonRowColumn655.rows_assocBCA HexagonRowColumn655.cols_left0) = negativeScale (leftScaleExponent 6 5 5) • (left1Middle6 5 5) := by
  funext r
  fin_cases r
  · exact leftFinal6_case_5_5_row_0_0_0
  · exact leftFinal6_case_5_5_row_0_1_0
  · exact leftFinal6_case_5_5_row_0_2_0
  · exact leftFinal6_case_5_5_row_0_3_0
  · exact leftFinal6_case_5_5_row_0_4_0
  · exact leftFinal6_case_5_5_row_0_5_0
  · exact leftFinal6_case_5_5_row_0_6_0
  · exact leftFinal6_case_5_5_row_0_7_0
  · exact leftFinal6_case_5_5_row_1_0_0
  · exact leftFinal6_case_5_5_row_1_1_0
  · exact leftFinal6_case_5_5_row_1_2_0
  · exact leftFinal6_case_5_5_row_1_3_0
  · exact leftFinal6_case_5_5_row_1_4_0
  · exact leftFinal6_case_5_5_row_1_5_0
  · exact leftFinal6_case_5_5_row_1_6_0
  · exact leftFinal6_case_5_5_row_1_7_0

set_option backward.isDefEq.respectTransparency false in
theorem leftFinal6_case_5_5 : ((-1 : ℤ) ^ (leftScaleBit 6 5 5).val * positiveScale (leftScaleExponent 6 5 5)) •
      (associatorZ 5 5 6 * left0Middle6 5 5) = negativeScale (leftScaleExponent 6 5 5) • (innerRightZ 5 6 5 * left1Middle6 5 5) := by
  simpa only [HexagonAtoms655.assocABC_eq,
    HexagonAtoms655.outerABC_eq,
    HexagonAtoms655.assocBAC_eq,
    HexagonAtoms655.innerABC_eq,
    HexagonAtoms655.innerRightABC_eq,
    HexagonAtoms655.inverseACB_eq,
    HexagonAtoms655.innerACB_eq,
    HexagonAtoms655.assocBCA_eq,
    HexagonAtoms655.innerRightBAC_eq,
    HexagonAtoms655.assocCAB_eq,
    HexagonAtoms655.outerLeftABC_eq,
    HexagonRowColumn655.innerACB_alias,
    HexagonRowColumn655.assocCAB_alias,
    HexagonRowColumn655.product0_eq,
    HexagonRowColumn655.product1_eq,
    HexagonRowColumn655.product2_eq,
    HexagonRowColumn655.product3_eq,
    HexagonRowColumn655.product4_eq,
    HexagonRowColumn655.product5_eq,
    HexagonRowColumn655.product6_eq,
    HexagonRowColumn655.product7_eq] using leftFinal6_case_5_5_checked

private theorem rightFinal6_case_5_5_row_0_0_0 : (((-1 : ℤ) ^ (rightScaleBit 6 5 5).val * positiveScale (rightScaleExponent 6 5 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 5 : ℤ)) • HexagonAtoms655.outerLeftABC) ((0 : Fin 2), (0 : Fin 8), (0 : Fin 1)) = (negativeScale (rightScaleExponent 6 5 5) • (rowColumnMul HexagonRowColumn655.rows_assocBAC HexagonRowColumn655.cols_right2)) ((0 : Fin 2), (0 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem rightFinal6_case_5_5_row_0_1_0 : (((-1 : ℤ) ^ (rightScaleBit 6 5 5).val * positiveScale (rightScaleExponent 6 5 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 5 : ℤ)) • HexagonAtoms655.outerLeftABC) ((0 : Fin 2), (1 : Fin 8), (0 : Fin 1)) = (negativeScale (rightScaleExponent 6 5 5) • (rowColumnMul HexagonRowColumn655.rows_assocBAC HexagonRowColumn655.cols_right2)) ((0 : Fin 2), (1 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem rightFinal6_case_5_5_row_0_2_0 : (((-1 : ℤ) ^ (rightScaleBit 6 5 5).val * positiveScale (rightScaleExponent 6 5 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 5 : ℤ)) • HexagonAtoms655.outerLeftABC) ((0 : Fin 2), (2 : Fin 8), (0 : Fin 1)) = (negativeScale (rightScaleExponent 6 5 5) • (rowColumnMul HexagonRowColumn655.rows_assocBAC HexagonRowColumn655.cols_right2)) ((0 : Fin 2), (2 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem rightFinal6_case_5_5_row_0_3_0 : (((-1 : ℤ) ^ (rightScaleBit 6 5 5).val * positiveScale (rightScaleExponent 6 5 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 5 : ℤ)) • HexagonAtoms655.outerLeftABC) ((0 : Fin 2), (3 : Fin 8), (0 : Fin 1)) = (negativeScale (rightScaleExponent 6 5 5) • (rowColumnMul HexagonRowColumn655.rows_assocBAC HexagonRowColumn655.cols_right2)) ((0 : Fin 2), (3 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem rightFinal6_case_5_5_row_0_4_0 : (((-1 : ℤ) ^ (rightScaleBit 6 5 5).val * positiveScale (rightScaleExponent 6 5 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 5 : ℤ)) • HexagonAtoms655.outerLeftABC) ((0 : Fin 2), (4 : Fin 8), (0 : Fin 1)) = (negativeScale (rightScaleExponent 6 5 5) • (rowColumnMul HexagonRowColumn655.rows_assocBAC HexagonRowColumn655.cols_right2)) ((0 : Fin 2), (4 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem rightFinal6_case_5_5_row_0_5_0 : (((-1 : ℤ) ^ (rightScaleBit 6 5 5).val * positiveScale (rightScaleExponent 6 5 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 5 : ℤ)) • HexagonAtoms655.outerLeftABC) ((0 : Fin 2), (5 : Fin 8), (0 : Fin 1)) = (negativeScale (rightScaleExponent 6 5 5) • (rowColumnMul HexagonRowColumn655.rows_assocBAC HexagonRowColumn655.cols_right2)) ((0 : Fin 2), (5 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem rightFinal6_case_5_5_row_0_6_0 : (((-1 : ℤ) ^ (rightScaleBit 6 5 5).val * positiveScale (rightScaleExponent 6 5 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 5 : ℤ)) • HexagonAtoms655.outerLeftABC) ((0 : Fin 2), (6 : Fin 8), (0 : Fin 1)) = (negativeScale (rightScaleExponent 6 5 5) • (rowColumnMul HexagonRowColumn655.rows_assocBAC HexagonRowColumn655.cols_right2)) ((0 : Fin 2), (6 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem rightFinal6_case_5_5_row_0_7_0 : (((-1 : ℤ) ^ (rightScaleBit 6 5 5).val * positiveScale (rightScaleExponent 6 5 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 5 : ℤ)) • HexagonAtoms655.outerLeftABC) ((0 : Fin 2), (7 : Fin 8), (0 : Fin 1)) = (negativeScale (rightScaleExponent 6 5 5) • (rowColumnMul HexagonRowColumn655.rows_assocBAC HexagonRowColumn655.cols_right2)) ((0 : Fin 2), (7 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem rightFinal6_case_5_5_row_1_0_0 : (((-1 : ℤ) ^ (rightScaleBit 6 5 5).val * positiveScale (rightScaleExponent 6 5 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 5 : ℤ)) • HexagonAtoms655.outerLeftABC) ((1 : Fin 2), (0 : Fin 8), (0 : Fin 1)) = (negativeScale (rightScaleExponent 6 5 5) • (rowColumnMul HexagonRowColumn655.rows_assocBAC HexagonRowColumn655.cols_right2)) ((1 : Fin 2), (0 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem rightFinal6_case_5_5_row_1_1_0 : (((-1 : ℤ) ^ (rightScaleBit 6 5 5).val * positiveScale (rightScaleExponent 6 5 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 5 : ℤ)) • HexagonAtoms655.outerLeftABC) ((1 : Fin 2), (1 : Fin 8), (0 : Fin 1)) = (negativeScale (rightScaleExponent 6 5 5) • (rowColumnMul HexagonRowColumn655.rows_assocBAC HexagonRowColumn655.cols_right2)) ((1 : Fin 2), (1 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem rightFinal6_case_5_5_row_1_2_0 : (((-1 : ℤ) ^ (rightScaleBit 6 5 5).val * positiveScale (rightScaleExponent 6 5 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 5 : ℤ)) • HexagonAtoms655.outerLeftABC) ((1 : Fin 2), (2 : Fin 8), (0 : Fin 1)) = (negativeScale (rightScaleExponent 6 5 5) • (rowColumnMul HexagonRowColumn655.rows_assocBAC HexagonRowColumn655.cols_right2)) ((1 : Fin 2), (2 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem rightFinal6_case_5_5_row_1_3_0 : (((-1 : ℤ) ^ (rightScaleBit 6 5 5).val * positiveScale (rightScaleExponent 6 5 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 5 : ℤ)) • HexagonAtoms655.outerLeftABC) ((1 : Fin 2), (3 : Fin 8), (0 : Fin 1)) = (negativeScale (rightScaleExponent 6 5 5) • (rowColumnMul HexagonRowColumn655.rows_assocBAC HexagonRowColumn655.cols_right2)) ((1 : Fin 2), (3 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem rightFinal6_case_5_5_row_1_4_0 : (((-1 : ℤ) ^ (rightScaleBit 6 5 5).val * positiveScale (rightScaleExponent 6 5 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 5 : ℤ)) • HexagonAtoms655.outerLeftABC) ((1 : Fin 2), (4 : Fin 8), (0 : Fin 1)) = (negativeScale (rightScaleExponent 6 5 5) • (rowColumnMul HexagonRowColumn655.rows_assocBAC HexagonRowColumn655.cols_right2)) ((1 : Fin 2), (4 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem rightFinal6_case_5_5_row_1_5_0 : (((-1 : ℤ) ^ (rightScaleBit 6 5 5).val * positiveScale (rightScaleExponent 6 5 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 5 : ℤ)) • HexagonAtoms655.outerLeftABC) ((1 : Fin 2), (5 : Fin 8), (0 : Fin 1)) = (negativeScale (rightScaleExponent 6 5 5) • (rowColumnMul HexagonRowColumn655.rows_assocBAC HexagonRowColumn655.cols_right2)) ((1 : Fin 2), (5 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem rightFinal6_case_5_5_row_1_6_0 : (((-1 : ℤ) ^ (rightScaleBit 6 5 5).val * positiveScale (rightScaleExponent 6 5 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 5 : ℤ)) • HexagonAtoms655.outerLeftABC) ((1 : Fin 2), (6 : Fin 8), (0 : Fin 1)) = (negativeScale (rightScaleExponent 6 5 5) • (rowColumnMul HexagonRowColumn655.rows_assocBAC HexagonRowColumn655.cols_right2)) ((1 : Fin 2), (6 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem rightFinal6_case_5_5_row_1_7_0 : (((-1 : ℤ) ^ (rightScaleBit 6 5 5).val * positiveScale (rightScaleExponent 6 5 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 5 : ℤ)) • HexagonAtoms655.outerLeftABC) ((1 : Fin 2), (7 : Fin 8), (0 : Fin 1)) = (negativeScale (rightScaleExponent 6 5 5) • (rowColumnMul HexagonRowColumn655.rows_assocBAC HexagonRowColumn655.cols_right2)) ((1 : Fin 2), (7 : Fin 8), (0 : Fin 1)) := by
  apply tripleRowCheck_sound (a := 2) (b := 8) (c := 1)
  decide +kernel

private theorem rightFinal6_case_5_5_checked : ((-1 : ℤ) ^ (rightScaleBit 6 5 5).val * positiveScale (rightScaleExponent 6 5 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 5 : ℤ)) • HexagonAtoms655.outerLeftABC = negativeScale (rightScaleExponent 6 5 5) • (rowColumnMul HexagonRowColumn655.rows_assocBAC HexagonRowColumn655.cols_right2) := by
  funext r
  fin_cases r
  · exact rightFinal6_case_5_5_row_0_0_0
  · exact rightFinal6_case_5_5_row_0_1_0
  · exact rightFinal6_case_5_5_row_0_2_0
  · exact rightFinal6_case_5_5_row_0_3_0
  · exact rightFinal6_case_5_5_row_0_4_0
  · exact rightFinal6_case_5_5_row_0_5_0
  · exact rightFinal6_case_5_5_row_0_6_0
  · exact rightFinal6_case_5_5_row_0_7_0
  · exact rightFinal6_case_5_5_row_1_0_0
  · exact rightFinal6_case_5_5_row_1_1_0
  · exact rightFinal6_case_5_5_row_1_2_0
  · exact rightFinal6_case_5_5_row_1_3_0
  · exact rightFinal6_case_5_5_row_1_4_0
  · exact rightFinal6_case_5_5_row_1_5_0
  · exact rightFinal6_case_5_5_row_1_6_0
  · exact rightFinal6_case_5_5_row_1_7_0

set_option backward.isDefEq.respectTransparency false in
theorem rightFinal6_case_5_5 : ((-1 : ℤ) ^ (rightScaleBit 6 5 5).val * positiveScale (rightScaleExponent 6 5 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 5 : ℤ)) • outerLeftZ 6 5 5 = negativeScale (rightScaleExponent 6 5 5) • (associatorZ 5 6 5 * right2Middle6 5 5) := by
  simpa only [HexagonAtoms655.assocABC_eq,
    HexagonAtoms655.outerABC_eq,
    HexagonAtoms655.assocBAC_eq,
    HexagonAtoms655.innerABC_eq,
    HexagonAtoms655.innerRightABC_eq,
    HexagonAtoms655.inverseACB_eq,
    HexagonAtoms655.innerACB_eq,
    HexagonAtoms655.assocBCA_eq,
    HexagonAtoms655.innerRightBAC_eq,
    HexagonAtoms655.assocCAB_eq,
    HexagonAtoms655.outerLeftABC_eq,
    HexagonRowColumn655.innerACB_alias,
    HexagonRowColumn655.assocCAB_alias,
    HexagonRowColumn655.product0_eq,
    HexagonRowColumn655.product1_eq,
    HexagonRowColumn655.product2_eq,
    HexagonRowColumn655.product3_eq,
    HexagonRowColumn655.product4_eq,
    HexagonRowColumn655.product5_eq,
    HexagonRowColumn655.product6_eq,
    HexagonRowColumn655.product7_eq] using rightFinal6_case_5_5_checked

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonCases6
