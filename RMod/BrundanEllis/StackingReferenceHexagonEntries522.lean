import RMod.BrundanEllis.StackingReferenceHexagonMiddle5
import RMod.BrundanEllis.StackingReferenceSparseMatrixCheck
import RMod.BrundanEllis.StackingReferenceHexagonAtoms522
import RMod.BrundanEllis.StackingReferenceHexagonRowColumn522

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

private theorem left0Middle5_eq_case_2_2_row_0_0_0 : (left0Middle5 2 2) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (HexagonAtoms522.assocABC) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_2_2_row_0_0_1 : (left0Middle5 2 2) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (HexagonAtoms522.assocABC) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_2_2_row_0_1_0 : (left0Middle5 2 2) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (HexagonAtoms522.assocABC) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_2_2_row_0_1_1 : (left0Middle5 2 2) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (HexagonAtoms522.assocABC) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_2_2_row_0_2_0 : (left0Middle5 2 2) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (HexagonAtoms522.assocABC) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_2_2_row_0_2_1 : (left0Middle5 2 2) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (HexagonAtoms522.assocABC) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_2_2_row_0_3_0 : (left0Middle5 2 2) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (HexagonAtoms522.assocABC) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_2_2_row_0_3_1 : (left0Middle5 2 2) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (HexagonAtoms522.assocABC) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_2_2_row_1_0_0 : (left0Middle5 2 2) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (HexagonAtoms522.assocABC) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_2_2_row_1_0_1 : (left0Middle5 2 2) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (HexagonAtoms522.assocABC) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_2_2_row_1_1_0 : (left0Middle5 2 2) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (HexagonAtoms522.assocABC) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_2_2_row_1_1_1 : (left0Middle5 2 2) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (HexagonAtoms522.assocABC) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_2_2_row_1_2_0 : (left0Middle5 2 2) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (HexagonAtoms522.assocABC) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_2_2_row_1_2_1 : (left0Middle5 2 2) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (HexagonAtoms522.assocABC) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_2_2_row_1_3_0 : (left0Middle5 2 2) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (HexagonAtoms522.assocABC) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_2_2_row_1_3_1 : (left0Middle5 2 2) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (HexagonAtoms522.assocABC) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_2_2_checked : left0Middle5 2 2 = HexagonAtoms522.assocABC := by
  funext r
  fin_cases r
  · exact left0Middle5_eq_case_2_2_row_0_0_0
  · exact left0Middle5_eq_case_2_2_row_0_0_1
  · exact left0Middle5_eq_case_2_2_row_0_1_0
  · exact left0Middle5_eq_case_2_2_row_0_1_1
  · exact left0Middle5_eq_case_2_2_row_0_2_0
  · exact left0Middle5_eq_case_2_2_row_0_2_1
  · exact left0Middle5_eq_case_2_2_row_0_3_0
  · exact left0Middle5_eq_case_2_2_row_0_3_1
  · exact left0Middle5_eq_case_2_2_row_1_0_0
  · exact left0Middle5_eq_case_2_2_row_1_0_1
  · exact left0Middle5_eq_case_2_2_row_1_1_0
  · exact left0Middle5_eq_case_2_2_row_1_1_1
  · exact left0Middle5_eq_case_2_2_row_1_2_0
  · exact left0Middle5_eq_case_2_2_row_1_2_1
  · exact left0Middle5_eq_case_2_2_row_1_3_0
  · exact left0Middle5_eq_case_2_2_row_1_3_1

set_option backward.isDefEq.respectTransparency false in
theorem left0Middle5_eq_case_2_2 : left0Middle5 2 2 = outerRightZ 5 2 2 * associatorZ 5 2 2 := by
  simpa only [HexagonAtoms522.assocABC_eq,
    HexagonAtoms522.outerABC_eq,
    HexagonAtoms522.assocBAC_eq,
    HexagonAtoms522.innerABC_eq,
    HexagonAtoms522.innerRightABC_eq,
    HexagonAtoms522.inverseACB_eq,
    HexagonAtoms522.innerACB_eq,
    HexagonAtoms522.assocBCA_eq,
    HexagonAtoms522.innerRightBAC_eq,
    HexagonAtoms522.assocCAB_eq,
    HexagonAtoms522.outerLeftABC_eq,
    HexagonRowColumn522.innerACB_alias,
    HexagonRowColumn522.assocCAB_alias,
    HexagonRowColumn522.product0_eq,
    HexagonRowColumn522.product1_eq,
    HexagonRowColumn522.product2_eq,
    HexagonRowColumn522.product3_eq,
    HexagonRowColumn522.product4_eq,
    HexagonRowColumn522.product5_eq,
    HexagonRowColumn522.product6_eq,
    HexagonRowColumn522.product7_eq] using left0Middle5_eq_case_2_2_checked

private theorem left1Middle5_eq_case_2_2_row_0_0_0 : (left1Middle5 2 2) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (HexagonAtoms522.assocBAC) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_2_2_row_0_0_1 : (left1Middle5 2 2) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (HexagonAtoms522.assocBAC) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_2_2_row_0_1_0 : (left1Middle5 2 2) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (HexagonAtoms522.assocBAC) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_2_2_row_0_1_1 : (left1Middle5 2 2) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (HexagonAtoms522.assocBAC) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_2_2_row_1_0_0 : (left1Middle5 2 2) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (HexagonAtoms522.assocBAC) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_2_2_row_1_0_1 : (left1Middle5 2 2) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (HexagonAtoms522.assocBAC) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_2_2_row_1_1_0 : (left1Middle5 2 2) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (HexagonAtoms522.assocBAC) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_2_2_row_1_1_1 : (left1Middle5 2 2) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (HexagonAtoms522.assocBAC) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_2_2_row_2_0_0 : (left1Middle5 2 2) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (HexagonAtoms522.assocBAC) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_2_2_row_2_0_1 : (left1Middle5 2 2) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (HexagonAtoms522.assocBAC) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_2_2_row_2_1_0 : (left1Middle5 2 2) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (HexagonAtoms522.assocBAC) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_2_2_row_2_1_1 : (left1Middle5 2 2) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (HexagonAtoms522.assocBAC) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_2_2_row_3_0_0 : (left1Middle5 2 2) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (HexagonAtoms522.assocBAC) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_2_2_row_3_0_1 : (left1Middle5 2 2) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (HexagonAtoms522.assocBAC) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_2_2_row_3_1_0 : (left1Middle5 2 2) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (HexagonAtoms522.assocBAC) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_2_2_row_3_1_1 : (left1Middle5 2 2) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (HexagonAtoms522.assocBAC) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_2_2_checked : left1Middle5 2 2 = HexagonAtoms522.assocBAC := by
  funext r
  fin_cases r
  · exact left1Middle5_eq_case_2_2_row_0_0_0
  · exact left1Middle5_eq_case_2_2_row_0_0_1
  · exact left1Middle5_eq_case_2_2_row_0_1_0
  · exact left1Middle5_eq_case_2_2_row_0_1_1
  · exact left1Middle5_eq_case_2_2_row_1_0_0
  · exact left1Middle5_eq_case_2_2_row_1_0_1
  · exact left1Middle5_eq_case_2_2_row_1_1_0
  · exact left1Middle5_eq_case_2_2_row_1_1_1
  · exact left1Middle5_eq_case_2_2_row_2_0_0
  · exact left1Middle5_eq_case_2_2_row_2_0_1
  · exact left1Middle5_eq_case_2_2_row_2_1_0
  · exact left1Middle5_eq_case_2_2_row_2_1_1
  · exact left1Middle5_eq_case_2_2_row_3_0_0
  · exact left1Middle5_eq_case_2_2_row_3_0_1
  · exact left1Middle5_eq_case_2_2_row_3_1_0
  · exact left1Middle5_eq_case_2_2_row_3_1_1

set_option backward.isDefEq.respectTransparency false in
theorem left1Middle5_eq_case_2_2 : left1Middle5 2 2 = associatorZ 2 5 2 * innerLeftZ 5 2 2 := by
  simpa only [HexagonAtoms522.assocABC_eq,
    HexagonAtoms522.outerABC_eq,
    HexagonAtoms522.assocBAC_eq,
    HexagonAtoms522.innerABC_eq,
    HexagonAtoms522.innerRightABC_eq,
    HexagonAtoms522.inverseACB_eq,
    HexagonAtoms522.innerACB_eq,
    HexagonAtoms522.assocBCA_eq,
    HexagonAtoms522.innerRightBAC_eq,
    HexagonAtoms522.assocCAB_eq,
    HexagonAtoms522.outerLeftABC_eq,
    HexagonRowColumn522.innerACB_alias,
    HexagonRowColumn522.assocCAB_alias,
    HexagonRowColumn522.product0_eq,
    HexagonRowColumn522.product1_eq,
    HexagonRowColumn522.product2_eq,
    HexagonRowColumn522.product3_eq,
    HexagonRowColumn522.product4_eq,
    HexagonRowColumn522.product5_eq,
    HexagonRowColumn522.product6_eq,
    HexagonRowColumn522.product7_eq] using left1Middle5_eq_case_2_2_checked

private theorem right0Middle5_eq_case_2_2_row_0_0_0 : (right0Middle5 2 2) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn522.rows_innerRightABC HexagonRowColumn522.cols_assocABC) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_2_2_row_0_0_1 : (right0Middle5 2 2) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn522.rows_innerRightABC HexagonRowColumn522.cols_assocABC) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_2_2_row_0_1_0 : (right0Middle5 2 2) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn522.rows_innerRightABC HexagonRowColumn522.cols_assocABC) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_2_2_row_0_1_1 : (right0Middle5 2 2) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn522.rows_innerRightABC HexagonRowColumn522.cols_assocABC) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_2_2_row_0_2_0 : (right0Middle5 2 2) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn522.rows_innerRightABC HexagonRowColumn522.cols_assocABC) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_2_2_row_0_2_1 : (right0Middle5 2 2) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn522.rows_innerRightABC HexagonRowColumn522.cols_assocABC) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_2_2_row_0_3_0 : (right0Middle5 2 2) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn522.rows_innerRightABC HexagonRowColumn522.cols_assocABC) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_2_2_row_0_3_1 : (right0Middle5 2 2) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn522.rows_innerRightABC HexagonRowColumn522.cols_assocABC) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_2_2_row_1_0_0 : (right0Middle5 2 2) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn522.rows_innerRightABC HexagonRowColumn522.cols_assocABC) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_2_2_row_1_0_1 : (right0Middle5 2 2) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn522.rows_innerRightABC HexagonRowColumn522.cols_assocABC) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_2_2_row_1_1_0 : (right0Middle5 2 2) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn522.rows_innerRightABC HexagonRowColumn522.cols_assocABC) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_2_2_row_1_1_1 : (right0Middle5 2 2) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn522.rows_innerRightABC HexagonRowColumn522.cols_assocABC) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_2_2_row_1_2_0 : (right0Middle5 2 2) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn522.rows_innerRightABC HexagonRowColumn522.cols_assocABC) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_2_2_row_1_2_1 : (right0Middle5 2 2) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn522.rows_innerRightABC HexagonRowColumn522.cols_assocABC) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_2_2_row_1_3_0 : (right0Middle5 2 2) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn522.rows_innerRightABC HexagonRowColumn522.cols_assocABC) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_2_2_row_1_3_1 : (right0Middle5 2 2) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn522.rows_innerRightABC HexagonRowColumn522.cols_assocABC) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_2_2_checked : right0Middle5 2 2 = rowColumnMul HexagonRowColumn522.rows_innerRightABC HexagonRowColumn522.cols_assocABC := by
  funext r
  fin_cases r
  · exact right0Middle5_eq_case_2_2_row_0_0_0
  · exact right0Middle5_eq_case_2_2_row_0_0_1
  · exact right0Middle5_eq_case_2_2_row_0_1_0
  · exact right0Middle5_eq_case_2_2_row_0_1_1
  · exact right0Middle5_eq_case_2_2_row_0_2_0
  · exact right0Middle5_eq_case_2_2_row_0_2_1
  · exact right0Middle5_eq_case_2_2_row_0_3_0
  · exact right0Middle5_eq_case_2_2_row_0_3_1
  · exact right0Middle5_eq_case_2_2_row_1_0_0
  · exact right0Middle5_eq_case_2_2_row_1_0_1
  · exact right0Middle5_eq_case_2_2_row_1_1_0
  · exact right0Middle5_eq_case_2_2_row_1_1_1
  · exact right0Middle5_eq_case_2_2_row_1_2_0
  · exact right0Middle5_eq_case_2_2_row_1_2_1
  · exact right0Middle5_eq_case_2_2_row_1_3_0
  · exact right0Middle5_eq_case_2_2_row_1_3_1

set_option backward.isDefEq.respectTransparency false in
theorem right0Middle5_eq_case_2_2 : right0Middle5 2 2 = innerRightZ 5 2 2 * associatorZ 5 2 2 := by
  simpa only [HexagonAtoms522.assocABC_eq,
    HexagonAtoms522.outerABC_eq,
    HexagonAtoms522.assocBAC_eq,
    HexagonAtoms522.innerABC_eq,
    HexagonAtoms522.innerRightABC_eq,
    HexagonAtoms522.inverseACB_eq,
    HexagonAtoms522.innerACB_eq,
    HexagonAtoms522.assocBCA_eq,
    HexagonAtoms522.innerRightBAC_eq,
    HexagonAtoms522.assocCAB_eq,
    HexagonAtoms522.outerLeftABC_eq,
    HexagonRowColumn522.innerACB_alias,
    HexagonRowColumn522.assocCAB_alias,
    HexagonRowColumn522.product0_eq,
    HexagonRowColumn522.product1_eq,
    HexagonRowColumn522.product2_eq,
    HexagonRowColumn522.product3_eq,
    HexagonRowColumn522.product4_eq,
    HexagonRowColumn522.product5_eq,
    HexagonRowColumn522.product6_eq,
    HexagonRowColumn522.product7_eq] using right0Middle5_eq_case_2_2_checked

private theorem right1Middle5_eq_case_2_2_row_0_0_0 : (right1Middle5 2 2) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn522.rows_inverseACB HexagonRowColumn522.cols_right0) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_2_2_row_0_0_1 : (right1Middle5 2 2) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn522.rows_inverseACB HexagonRowColumn522.cols_right0) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_2_2_row_0_1_0 : (right1Middle5 2 2) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn522.rows_inverseACB HexagonRowColumn522.cols_right0) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_2_2_row_0_1_1 : (right1Middle5 2 2) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn522.rows_inverseACB HexagonRowColumn522.cols_right0) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_2_2_row_1_0_0 : (right1Middle5 2 2) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn522.rows_inverseACB HexagonRowColumn522.cols_right0) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_2_2_row_1_0_1 : (right1Middle5 2 2) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn522.rows_inverseACB HexagonRowColumn522.cols_right0) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_2_2_row_1_1_0 : (right1Middle5 2 2) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn522.rows_inverseACB HexagonRowColumn522.cols_right0) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_2_2_row_1_1_1 : (right1Middle5 2 2) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn522.rows_inverseACB HexagonRowColumn522.cols_right0) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_2_2_row_2_0_0 : (right1Middle5 2 2) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn522.rows_inverseACB HexagonRowColumn522.cols_right0) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_2_2_row_2_0_1 : (right1Middle5 2 2) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn522.rows_inverseACB HexagonRowColumn522.cols_right0) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_2_2_row_2_1_0 : (right1Middle5 2 2) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn522.rows_inverseACB HexagonRowColumn522.cols_right0) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_2_2_row_2_1_1 : (right1Middle5 2 2) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn522.rows_inverseACB HexagonRowColumn522.cols_right0) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_2_2_row_3_0_0 : (right1Middle5 2 2) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn522.rows_inverseACB HexagonRowColumn522.cols_right0) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_2_2_row_3_0_1 : (right1Middle5 2 2) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn522.rows_inverseACB HexagonRowColumn522.cols_right0) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_2_2_row_3_1_0 : (right1Middle5 2 2) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn522.rows_inverseACB HexagonRowColumn522.cols_right0) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_2_2_row_3_1_1 : (right1Middle5 2 2) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn522.rows_inverseACB HexagonRowColumn522.cols_right0) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_2_2_checked : right1Middle5 2 2 = rowColumnMul HexagonRowColumn522.rows_inverseACB HexagonRowColumn522.cols_right0 := by
  funext r
  fin_cases r
  · exact right1Middle5_eq_case_2_2_row_0_0_0
  · exact right1Middle5_eq_case_2_2_row_0_0_1
  · exact right1Middle5_eq_case_2_2_row_0_1_0
  · exact right1Middle5_eq_case_2_2_row_0_1_1
  · exact right1Middle5_eq_case_2_2_row_1_0_0
  · exact right1Middle5_eq_case_2_2_row_1_0_1
  · exact right1Middle5_eq_case_2_2_row_1_1_0
  · exact right1Middle5_eq_case_2_2_row_1_1_1
  · exact right1Middle5_eq_case_2_2_row_2_0_0
  · exact right1Middle5_eq_case_2_2_row_2_0_1
  · exact right1Middle5_eq_case_2_2_row_2_1_0
  · exact right1Middle5_eq_case_2_2_row_2_1_1
  · exact right1Middle5_eq_case_2_2_row_3_0_0
  · exact right1Middle5_eq_case_2_2_row_3_0_1
  · exact right1Middle5_eq_case_2_2_row_3_1_0
  · exact right1Middle5_eq_case_2_2_row_3_1_1

set_option backward.isDefEq.respectTransparency false in
theorem right1Middle5_eq_case_2_2 : right1Middle5 2 2 = associatorInverseZ 5 2 2 * right0Middle5 2 2 := by
  simpa only [HexagonAtoms522.assocABC_eq,
    HexagonAtoms522.outerABC_eq,
    HexagonAtoms522.assocBAC_eq,
    HexagonAtoms522.innerABC_eq,
    HexagonAtoms522.innerRightABC_eq,
    HexagonAtoms522.inverseACB_eq,
    HexagonAtoms522.innerACB_eq,
    HexagonAtoms522.assocBCA_eq,
    HexagonAtoms522.innerRightBAC_eq,
    HexagonAtoms522.assocCAB_eq,
    HexagonAtoms522.outerLeftABC_eq,
    HexagonRowColumn522.innerACB_alias,
    HexagonRowColumn522.assocCAB_alias,
    HexagonRowColumn522.product0_eq,
    HexagonRowColumn522.product1_eq,
    HexagonRowColumn522.product2_eq,
    HexagonRowColumn522.product3_eq,
    HexagonRowColumn522.product4_eq,
    HexagonRowColumn522.product5_eq,
    HexagonRowColumn522.product6_eq,
    HexagonRowColumn522.product7_eq] using right1Middle5_eq_case_2_2_checked

private theorem right2Middle5_eq_case_2_2_row_0_0_0 : (right2Middle5 2 2) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (right1Middle5 2 2) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_2_2_row_0_0_1 : (right2Middle5 2 2) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (right1Middle5 2 2) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_2_2_row_0_1_0 : (right2Middle5 2 2) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (right1Middle5 2 2) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_2_2_row_0_1_1 : (right2Middle5 2 2) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (right1Middle5 2 2) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_2_2_row_1_0_0 : (right2Middle5 2 2) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (right1Middle5 2 2) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_2_2_row_1_0_1 : (right2Middle5 2 2) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (right1Middle5 2 2) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_2_2_row_1_1_0 : (right2Middle5 2 2) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (right1Middle5 2 2) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_2_2_row_1_1_1 : (right2Middle5 2 2) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (right1Middle5 2 2) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_2_2_row_2_0_0 : (right2Middle5 2 2) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (right1Middle5 2 2) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_2_2_row_2_0_1 : (right2Middle5 2 2) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (right1Middle5 2 2) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_2_2_row_2_1_0 : (right2Middle5 2 2) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (right1Middle5 2 2) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_2_2_row_2_1_1 : (right2Middle5 2 2) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (right1Middle5 2 2) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_2_2_row_3_0_0 : (right2Middle5 2 2) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (right1Middle5 2 2) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_2_2_row_3_0_1 : (right2Middle5 2 2) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (right1Middle5 2 2) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_2_2_row_3_1_0 : (right2Middle5 2 2) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (right1Middle5 2 2) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_2_2_row_3_1_1 : (right2Middle5 2 2) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (right1Middle5 2 2) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_2_2_checked : right2Middle5 2 2 = right1Middle5 2 2 := by
  funext r
  fin_cases r
  · exact right2Middle5_eq_case_2_2_row_0_0_0
  · exact right2Middle5_eq_case_2_2_row_0_0_1
  · exact right2Middle5_eq_case_2_2_row_0_1_0
  · exact right2Middle5_eq_case_2_2_row_0_1_1
  · exact right2Middle5_eq_case_2_2_row_1_0_0
  · exact right2Middle5_eq_case_2_2_row_1_0_1
  · exact right2Middle5_eq_case_2_2_row_1_1_0
  · exact right2Middle5_eq_case_2_2_row_1_1_1
  · exact right2Middle5_eq_case_2_2_row_2_0_0
  · exact right2Middle5_eq_case_2_2_row_2_0_1
  · exact right2Middle5_eq_case_2_2_row_2_1_0
  · exact right2Middle5_eq_case_2_2_row_2_1_1
  · exact right2Middle5_eq_case_2_2_row_3_0_0
  · exact right2Middle5_eq_case_2_2_row_3_0_1
  · exact right2Middle5_eq_case_2_2_row_3_1_0
  · exact right2Middle5_eq_case_2_2_row_3_1_1

set_option backward.isDefEq.respectTransparency false in
theorem right2Middle5_eq_case_2_2 : right2Middle5 2 2 = innerLeftZ 5 2 2 * right1Middle5 2 2 := by
  simpa only [HexagonAtoms522.assocABC_eq,
    HexagonAtoms522.outerABC_eq,
    HexagonAtoms522.assocBAC_eq,
    HexagonAtoms522.innerABC_eq,
    HexagonAtoms522.innerRightABC_eq,
    HexagonAtoms522.inverseACB_eq,
    HexagonAtoms522.innerACB_eq,
    HexagonAtoms522.assocBCA_eq,
    HexagonAtoms522.innerRightBAC_eq,
    HexagonAtoms522.assocCAB_eq,
    HexagonAtoms522.outerLeftABC_eq,
    HexagonRowColumn522.innerACB_alias,
    HexagonRowColumn522.assocCAB_alias,
    HexagonRowColumn522.product0_eq,
    HexagonRowColumn522.product1_eq,
    HexagonRowColumn522.product2_eq,
    HexagonRowColumn522.product3_eq,
    HexagonRowColumn522.product4_eq,
    HexagonRowColumn522.product5_eq,
    HexagonRowColumn522.product6_eq,
    HexagonRowColumn522.product7_eq] using right2Middle5_eq_case_2_2_checked

private theorem leftFinal5_case_2_2_row_0_0_0 : (((-1 : ℤ) ^ (leftScaleBit 5 2 2).val * positiveScale (leftScaleExponent 5 2 2)) •
      (rowColumnMul HexagonRowColumn522.rows_assocBCA HexagonRowColumn522.cols_left0)) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (negativeScale (leftScaleExponent 5 2 2) • (left1Middle5 2 2)) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem leftFinal5_case_2_2_row_0_0_1 : (((-1 : ℤ) ^ (leftScaleBit 5 2 2).val * positiveScale (leftScaleExponent 5 2 2)) •
      (rowColumnMul HexagonRowColumn522.rows_assocBCA HexagonRowColumn522.cols_left0)) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (negativeScale (leftScaleExponent 5 2 2) • (left1Middle5 2 2)) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem leftFinal5_case_2_2_row_0_1_0 : (((-1 : ℤ) ^ (leftScaleBit 5 2 2).val * positiveScale (leftScaleExponent 5 2 2)) •
      (rowColumnMul HexagonRowColumn522.rows_assocBCA HexagonRowColumn522.cols_left0)) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (negativeScale (leftScaleExponent 5 2 2) • (left1Middle5 2 2)) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem leftFinal5_case_2_2_row_0_1_1 : (((-1 : ℤ) ^ (leftScaleBit 5 2 2).val * positiveScale (leftScaleExponent 5 2 2)) •
      (rowColumnMul HexagonRowColumn522.rows_assocBCA HexagonRowColumn522.cols_left0)) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (negativeScale (leftScaleExponent 5 2 2) • (left1Middle5 2 2)) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem leftFinal5_case_2_2_row_1_0_0 : (((-1 : ℤ) ^ (leftScaleBit 5 2 2).val * positiveScale (leftScaleExponent 5 2 2)) •
      (rowColumnMul HexagonRowColumn522.rows_assocBCA HexagonRowColumn522.cols_left0)) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (negativeScale (leftScaleExponent 5 2 2) • (left1Middle5 2 2)) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem leftFinal5_case_2_2_row_1_0_1 : (((-1 : ℤ) ^ (leftScaleBit 5 2 2).val * positiveScale (leftScaleExponent 5 2 2)) •
      (rowColumnMul HexagonRowColumn522.rows_assocBCA HexagonRowColumn522.cols_left0)) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (negativeScale (leftScaleExponent 5 2 2) • (left1Middle5 2 2)) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem leftFinal5_case_2_2_row_1_1_0 : (((-1 : ℤ) ^ (leftScaleBit 5 2 2).val * positiveScale (leftScaleExponent 5 2 2)) •
      (rowColumnMul HexagonRowColumn522.rows_assocBCA HexagonRowColumn522.cols_left0)) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (negativeScale (leftScaleExponent 5 2 2) • (left1Middle5 2 2)) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem leftFinal5_case_2_2_row_1_1_1 : (((-1 : ℤ) ^ (leftScaleBit 5 2 2).val * positiveScale (leftScaleExponent 5 2 2)) •
      (rowColumnMul HexagonRowColumn522.rows_assocBCA HexagonRowColumn522.cols_left0)) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (negativeScale (leftScaleExponent 5 2 2) • (left1Middle5 2 2)) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem leftFinal5_case_2_2_row_2_0_0 : (((-1 : ℤ) ^ (leftScaleBit 5 2 2).val * positiveScale (leftScaleExponent 5 2 2)) •
      (rowColumnMul HexagonRowColumn522.rows_assocBCA HexagonRowColumn522.cols_left0)) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (negativeScale (leftScaleExponent 5 2 2) • (left1Middle5 2 2)) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem leftFinal5_case_2_2_row_2_0_1 : (((-1 : ℤ) ^ (leftScaleBit 5 2 2).val * positiveScale (leftScaleExponent 5 2 2)) •
      (rowColumnMul HexagonRowColumn522.rows_assocBCA HexagonRowColumn522.cols_left0)) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (negativeScale (leftScaleExponent 5 2 2) • (left1Middle5 2 2)) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem leftFinal5_case_2_2_row_2_1_0 : (((-1 : ℤ) ^ (leftScaleBit 5 2 2).val * positiveScale (leftScaleExponent 5 2 2)) •
      (rowColumnMul HexagonRowColumn522.rows_assocBCA HexagonRowColumn522.cols_left0)) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (negativeScale (leftScaleExponent 5 2 2) • (left1Middle5 2 2)) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem leftFinal5_case_2_2_row_2_1_1 : (((-1 : ℤ) ^ (leftScaleBit 5 2 2).val * positiveScale (leftScaleExponent 5 2 2)) •
      (rowColumnMul HexagonRowColumn522.rows_assocBCA HexagonRowColumn522.cols_left0)) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (negativeScale (leftScaleExponent 5 2 2) • (left1Middle5 2 2)) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem leftFinal5_case_2_2_row_3_0_0 : (((-1 : ℤ) ^ (leftScaleBit 5 2 2).val * positiveScale (leftScaleExponent 5 2 2)) •
      (rowColumnMul HexagonRowColumn522.rows_assocBCA HexagonRowColumn522.cols_left0)) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (negativeScale (leftScaleExponent 5 2 2) • (left1Middle5 2 2)) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem leftFinal5_case_2_2_row_3_0_1 : (((-1 : ℤ) ^ (leftScaleBit 5 2 2).val * positiveScale (leftScaleExponent 5 2 2)) •
      (rowColumnMul HexagonRowColumn522.rows_assocBCA HexagonRowColumn522.cols_left0)) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (negativeScale (leftScaleExponent 5 2 2) • (left1Middle5 2 2)) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem leftFinal5_case_2_2_row_3_1_0 : (((-1 : ℤ) ^ (leftScaleBit 5 2 2).val * positiveScale (leftScaleExponent 5 2 2)) •
      (rowColumnMul HexagonRowColumn522.rows_assocBCA HexagonRowColumn522.cols_left0)) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (negativeScale (leftScaleExponent 5 2 2) • (left1Middle5 2 2)) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem leftFinal5_case_2_2_row_3_1_1 : (((-1 : ℤ) ^ (leftScaleBit 5 2 2).val * positiveScale (leftScaleExponent 5 2 2)) •
      (rowColumnMul HexagonRowColumn522.rows_assocBCA HexagonRowColumn522.cols_left0)) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (negativeScale (leftScaleExponent 5 2 2) • (left1Middle5 2 2)) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem leftFinal5_case_2_2_checked : ((-1 : ℤ) ^ (leftScaleBit 5 2 2).val * positiveScale (leftScaleExponent 5 2 2)) •
      (rowColumnMul HexagonRowColumn522.rows_assocBCA HexagonRowColumn522.cols_left0) = negativeScale (leftScaleExponent 5 2 2) • (left1Middle5 2 2) := by
  funext r
  fin_cases r
  · exact leftFinal5_case_2_2_row_0_0_0
  · exact leftFinal5_case_2_2_row_0_0_1
  · exact leftFinal5_case_2_2_row_0_1_0
  · exact leftFinal5_case_2_2_row_0_1_1
  · exact leftFinal5_case_2_2_row_1_0_0
  · exact leftFinal5_case_2_2_row_1_0_1
  · exact leftFinal5_case_2_2_row_1_1_0
  · exact leftFinal5_case_2_2_row_1_1_1
  · exact leftFinal5_case_2_2_row_2_0_0
  · exact leftFinal5_case_2_2_row_2_0_1
  · exact leftFinal5_case_2_2_row_2_1_0
  · exact leftFinal5_case_2_2_row_2_1_1
  · exact leftFinal5_case_2_2_row_3_0_0
  · exact leftFinal5_case_2_2_row_3_0_1
  · exact leftFinal5_case_2_2_row_3_1_0
  · exact leftFinal5_case_2_2_row_3_1_1

set_option backward.isDefEq.respectTransparency false in
theorem leftFinal5_case_2_2 : ((-1 : ℤ) ^ (leftScaleBit 5 2 2).val * positiveScale (leftScaleExponent 5 2 2)) •
      (associatorZ 2 2 5 * left0Middle5 2 2) = negativeScale (leftScaleExponent 5 2 2) • (innerRightZ 2 5 2 * left1Middle5 2 2) := by
  simpa only [HexagonAtoms522.assocABC_eq,
    HexagonAtoms522.outerABC_eq,
    HexagonAtoms522.assocBAC_eq,
    HexagonAtoms522.innerABC_eq,
    HexagonAtoms522.innerRightABC_eq,
    HexagonAtoms522.inverseACB_eq,
    HexagonAtoms522.innerACB_eq,
    HexagonAtoms522.assocBCA_eq,
    HexagonAtoms522.innerRightBAC_eq,
    HexagonAtoms522.assocCAB_eq,
    HexagonAtoms522.outerLeftABC_eq,
    HexagonRowColumn522.innerACB_alias,
    HexagonRowColumn522.assocCAB_alias,
    HexagonRowColumn522.product0_eq,
    HexagonRowColumn522.product1_eq,
    HexagonRowColumn522.product2_eq,
    HexagonRowColumn522.product3_eq,
    HexagonRowColumn522.product4_eq,
    HexagonRowColumn522.product5_eq,
    HexagonRowColumn522.product6_eq,
    HexagonRowColumn522.product7_eq] using leftFinal5_case_2_2_checked

private theorem rightFinal5_case_2_2_row_0_0_0 : (((-1 : ℤ) ^ (rightScaleBit 5 2 2).val * positiveScale (rightScaleExponent 5 2 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 2 2 : ℤ)) • HexagonAtoms522.outerLeftABC) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (negativeScale (rightScaleExponent 5 2 2) • (rowColumnMul HexagonRowColumn522.rows_assocBAC HexagonRowColumn522.cols_right2)) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem rightFinal5_case_2_2_row_0_0_1 : (((-1 : ℤ) ^ (rightScaleBit 5 2 2).val * positiveScale (rightScaleExponent 5 2 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 2 2 : ℤ)) • HexagonAtoms522.outerLeftABC) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (negativeScale (rightScaleExponent 5 2 2) • (rowColumnMul HexagonRowColumn522.rows_assocBAC HexagonRowColumn522.cols_right2)) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem rightFinal5_case_2_2_row_0_1_0 : (((-1 : ℤ) ^ (rightScaleBit 5 2 2).val * positiveScale (rightScaleExponent 5 2 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 2 2 : ℤ)) • HexagonAtoms522.outerLeftABC) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (negativeScale (rightScaleExponent 5 2 2) • (rowColumnMul HexagonRowColumn522.rows_assocBAC HexagonRowColumn522.cols_right2)) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem rightFinal5_case_2_2_row_0_1_1 : (((-1 : ℤ) ^ (rightScaleBit 5 2 2).val * positiveScale (rightScaleExponent 5 2 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 2 2 : ℤ)) • HexagonAtoms522.outerLeftABC) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (negativeScale (rightScaleExponent 5 2 2) • (rowColumnMul HexagonRowColumn522.rows_assocBAC HexagonRowColumn522.cols_right2)) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem rightFinal5_case_2_2_row_1_0_0 : (((-1 : ℤ) ^ (rightScaleBit 5 2 2).val * positiveScale (rightScaleExponent 5 2 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 2 2 : ℤ)) • HexagonAtoms522.outerLeftABC) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (negativeScale (rightScaleExponent 5 2 2) • (rowColumnMul HexagonRowColumn522.rows_assocBAC HexagonRowColumn522.cols_right2)) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem rightFinal5_case_2_2_row_1_0_1 : (((-1 : ℤ) ^ (rightScaleBit 5 2 2).val * positiveScale (rightScaleExponent 5 2 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 2 2 : ℤ)) • HexagonAtoms522.outerLeftABC) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (negativeScale (rightScaleExponent 5 2 2) • (rowColumnMul HexagonRowColumn522.rows_assocBAC HexagonRowColumn522.cols_right2)) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem rightFinal5_case_2_2_row_1_1_0 : (((-1 : ℤ) ^ (rightScaleBit 5 2 2).val * positiveScale (rightScaleExponent 5 2 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 2 2 : ℤ)) • HexagonAtoms522.outerLeftABC) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (negativeScale (rightScaleExponent 5 2 2) • (rowColumnMul HexagonRowColumn522.rows_assocBAC HexagonRowColumn522.cols_right2)) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem rightFinal5_case_2_2_row_1_1_1 : (((-1 : ℤ) ^ (rightScaleBit 5 2 2).val * positiveScale (rightScaleExponent 5 2 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 2 2 : ℤ)) • HexagonAtoms522.outerLeftABC) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (negativeScale (rightScaleExponent 5 2 2) • (rowColumnMul HexagonRowColumn522.rows_assocBAC HexagonRowColumn522.cols_right2)) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem rightFinal5_case_2_2_row_2_0_0 : (((-1 : ℤ) ^ (rightScaleBit 5 2 2).val * positiveScale (rightScaleExponent 5 2 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 2 2 : ℤ)) • HexagonAtoms522.outerLeftABC) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (negativeScale (rightScaleExponent 5 2 2) • (rowColumnMul HexagonRowColumn522.rows_assocBAC HexagonRowColumn522.cols_right2)) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem rightFinal5_case_2_2_row_2_0_1 : (((-1 : ℤ) ^ (rightScaleBit 5 2 2).val * positiveScale (rightScaleExponent 5 2 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 2 2 : ℤ)) • HexagonAtoms522.outerLeftABC) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (negativeScale (rightScaleExponent 5 2 2) • (rowColumnMul HexagonRowColumn522.rows_assocBAC HexagonRowColumn522.cols_right2)) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem rightFinal5_case_2_2_row_2_1_0 : (((-1 : ℤ) ^ (rightScaleBit 5 2 2).val * positiveScale (rightScaleExponent 5 2 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 2 2 : ℤ)) • HexagonAtoms522.outerLeftABC) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (negativeScale (rightScaleExponent 5 2 2) • (rowColumnMul HexagonRowColumn522.rows_assocBAC HexagonRowColumn522.cols_right2)) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem rightFinal5_case_2_2_row_2_1_1 : (((-1 : ℤ) ^ (rightScaleBit 5 2 2).val * positiveScale (rightScaleExponent 5 2 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 2 2 : ℤ)) • HexagonAtoms522.outerLeftABC) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (negativeScale (rightScaleExponent 5 2 2) • (rowColumnMul HexagonRowColumn522.rows_assocBAC HexagonRowColumn522.cols_right2)) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem rightFinal5_case_2_2_row_3_0_0 : (((-1 : ℤ) ^ (rightScaleBit 5 2 2).val * positiveScale (rightScaleExponent 5 2 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 2 2 : ℤ)) • HexagonAtoms522.outerLeftABC) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (negativeScale (rightScaleExponent 5 2 2) • (rowColumnMul HexagonRowColumn522.rows_assocBAC HexagonRowColumn522.cols_right2)) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem rightFinal5_case_2_2_row_3_0_1 : (((-1 : ℤ) ^ (rightScaleBit 5 2 2).val * positiveScale (rightScaleExponent 5 2 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 2 2 : ℤ)) • HexagonAtoms522.outerLeftABC) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (negativeScale (rightScaleExponent 5 2 2) • (rowColumnMul HexagonRowColumn522.rows_assocBAC HexagonRowColumn522.cols_right2)) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem rightFinal5_case_2_2_row_3_1_0 : (((-1 : ℤ) ^ (rightScaleBit 5 2 2).val * positiveScale (rightScaleExponent 5 2 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 2 2 : ℤ)) • HexagonAtoms522.outerLeftABC) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (negativeScale (rightScaleExponent 5 2 2) • (rowColumnMul HexagonRowColumn522.rows_assocBAC HexagonRowColumn522.cols_right2)) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem rightFinal5_case_2_2_row_3_1_1 : (((-1 : ℤ) ^ (rightScaleBit 5 2 2).val * positiveScale (rightScaleExponent 5 2 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 2 2 : ℤ)) • HexagonAtoms522.outerLeftABC) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (negativeScale (rightScaleExponent 5 2 2) • (rowColumnMul HexagonRowColumn522.rows_assocBAC HexagonRowColumn522.cols_right2)) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem rightFinal5_case_2_2_checked : ((-1 : ℤ) ^ (rightScaleBit 5 2 2).val * positiveScale (rightScaleExponent 5 2 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 2 2 : ℤ)) • HexagonAtoms522.outerLeftABC = negativeScale (rightScaleExponent 5 2 2) • (rowColumnMul HexagonRowColumn522.rows_assocBAC HexagonRowColumn522.cols_right2) := by
  funext r
  fin_cases r
  · exact rightFinal5_case_2_2_row_0_0_0
  · exact rightFinal5_case_2_2_row_0_0_1
  · exact rightFinal5_case_2_2_row_0_1_0
  · exact rightFinal5_case_2_2_row_0_1_1
  · exact rightFinal5_case_2_2_row_1_0_0
  · exact rightFinal5_case_2_2_row_1_0_1
  · exact rightFinal5_case_2_2_row_1_1_0
  · exact rightFinal5_case_2_2_row_1_1_1
  · exact rightFinal5_case_2_2_row_2_0_0
  · exact rightFinal5_case_2_2_row_2_0_1
  · exact rightFinal5_case_2_2_row_2_1_0
  · exact rightFinal5_case_2_2_row_2_1_1
  · exact rightFinal5_case_2_2_row_3_0_0
  · exact rightFinal5_case_2_2_row_3_0_1
  · exact rightFinal5_case_2_2_row_3_1_0
  · exact rightFinal5_case_2_2_row_3_1_1

set_option backward.isDefEq.respectTransparency false in
theorem rightFinal5_case_2_2 : ((-1 : ℤ) ^ (rightScaleBit 5 2 2).val * positiveScale (rightScaleExponent 5 2 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 2 2 : ℤ)) • outerLeftZ 5 2 2 = negativeScale (rightScaleExponent 5 2 2) • (associatorZ 2 5 2 * right2Middle5 2 2) := by
  simpa only [HexagonAtoms522.assocABC_eq,
    HexagonAtoms522.outerABC_eq,
    HexagonAtoms522.assocBAC_eq,
    HexagonAtoms522.innerABC_eq,
    HexagonAtoms522.innerRightABC_eq,
    HexagonAtoms522.inverseACB_eq,
    HexagonAtoms522.innerACB_eq,
    HexagonAtoms522.assocBCA_eq,
    HexagonAtoms522.innerRightBAC_eq,
    HexagonAtoms522.assocCAB_eq,
    HexagonAtoms522.outerLeftABC_eq,
    HexagonRowColumn522.innerACB_alias,
    HexagonRowColumn522.assocCAB_alias,
    HexagonRowColumn522.product0_eq,
    HexagonRowColumn522.product1_eq,
    HexagonRowColumn522.product2_eq,
    HexagonRowColumn522.product3_eq,
    HexagonRowColumn522.product4_eq,
    HexagonRowColumn522.product5_eq,
    HexagonRowColumn522.product6_eq,
    HexagonRowColumn522.product7_eq] using rightFinal5_case_2_2_checked

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonCases5
