import RMod.BrundanEllis.StackingReferenceHexagonMiddle7
import RMod.BrundanEllis.StackingReferenceSparseMatrixCheck
import RMod.BrundanEllis.StackingReferenceHexagonAtoms755
import RMod.BrundanEllis.StackingReferenceHexagonRowColumn755

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

private theorem left0Middle7_eq_case_5_5_row_0_0_0 : (left0Middle7 5 5) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (HexagonAtoms755.assocABC) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle7_eq_case_5_5_row_0_0_1 : (left0Middle7 5 5) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (HexagonAtoms755.assocABC) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle7_eq_case_5_5_row_0_1_0 : (left0Middle7 5 5) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (HexagonAtoms755.assocABC) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle7_eq_case_5_5_row_0_1_1 : (left0Middle7 5 5) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (HexagonAtoms755.assocABC) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle7_eq_case_5_5_row_1_0_0 : (left0Middle7 5 5) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (HexagonAtoms755.assocABC) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle7_eq_case_5_5_row_1_0_1 : (left0Middle7 5 5) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (HexagonAtoms755.assocABC) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle7_eq_case_5_5_row_1_1_0 : (left0Middle7 5 5) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (HexagonAtoms755.assocABC) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle7_eq_case_5_5_row_1_1_1 : (left0Middle7 5 5) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (HexagonAtoms755.assocABC) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle7_eq_case_5_5_row_2_0_0 : (left0Middle7 5 5) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (HexagonAtoms755.assocABC) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle7_eq_case_5_5_row_2_0_1 : (left0Middle7 5 5) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (HexagonAtoms755.assocABC) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle7_eq_case_5_5_row_2_1_0 : (left0Middle7 5 5) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (HexagonAtoms755.assocABC) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle7_eq_case_5_5_row_2_1_1 : (left0Middle7 5 5) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (HexagonAtoms755.assocABC) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle7_eq_case_5_5_row_3_0_0 : (left0Middle7 5 5) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (HexagonAtoms755.assocABC) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle7_eq_case_5_5_row_3_0_1 : (left0Middle7 5 5) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (HexagonAtoms755.assocABC) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle7_eq_case_5_5_row_3_1_0 : (left0Middle7 5 5) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (HexagonAtoms755.assocABC) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle7_eq_case_5_5_row_3_1_1 : (left0Middle7 5 5) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (HexagonAtoms755.assocABC) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle7_eq_case_5_5_checked : left0Middle7 5 5 = HexagonAtoms755.assocABC := by
  funext r
  fin_cases r
  · exact left0Middle7_eq_case_5_5_row_0_0_0
  · exact left0Middle7_eq_case_5_5_row_0_0_1
  · exact left0Middle7_eq_case_5_5_row_0_1_0
  · exact left0Middle7_eq_case_5_5_row_0_1_1
  · exact left0Middle7_eq_case_5_5_row_1_0_0
  · exact left0Middle7_eq_case_5_5_row_1_0_1
  · exact left0Middle7_eq_case_5_5_row_1_1_0
  · exact left0Middle7_eq_case_5_5_row_1_1_1
  · exact left0Middle7_eq_case_5_5_row_2_0_0
  · exact left0Middle7_eq_case_5_5_row_2_0_1
  · exact left0Middle7_eq_case_5_5_row_2_1_0
  · exact left0Middle7_eq_case_5_5_row_2_1_1
  · exact left0Middle7_eq_case_5_5_row_3_0_0
  · exact left0Middle7_eq_case_5_5_row_3_0_1
  · exact left0Middle7_eq_case_5_5_row_3_1_0
  · exact left0Middle7_eq_case_5_5_row_3_1_1

set_option backward.isDefEq.respectTransparency false in
theorem left0Middle7_eq_case_5_5 : left0Middle7 5 5 = outerRightZ 7 5 5 * associatorZ 7 5 5 := by
  simpa only [HexagonAtoms755.assocABC_eq,
    HexagonAtoms755.outerABC_eq,
    HexagonAtoms755.assocBAC_eq,
    HexagonAtoms755.innerABC_eq,
    HexagonAtoms755.innerRightABC_eq,
    HexagonAtoms755.inverseACB_eq,
    HexagonAtoms755.innerACB_eq,
    HexagonAtoms755.assocBCA_eq,
    HexagonAtoms755.innerRightBAC_eq,
    HexagonAtoms755.assocCAB_eq,
    HexagonAtoms755.outerLeftABC_eq,
    HexagonRowColumn755.innerACB_alias,
    HexagonRowColumn755.assocCAB_alias,
    HexagonRowColumn755.product0_eq,
    HexagonRowColumn755.product1_eq,
    HexagonRowColumn755.product2_eq,
    HexagonRowColumn755.product3_eq,
    HexagonRowColumn755.product4_eq,
    HexagonRowColumn755.product5_eq,
    HexagonRowColumn755.product6_eq,
    HexagonRowColumn755.product7_eq] using left0Middle7_eq_case_5_5_checked

private theorem left1Middle7_eq_case_5_5_row_0_0_0 : (left1Middle7 5 5) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (HexagonAtoms755.assocBAC) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle7_eq_case_5_5_row_0_0_1 : (left1Middle7 5 5) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (HexagonAtoms755.assocBAC) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle7_eq_case_5_5_row_0_1_0 : (left1Middle7 5 5) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (HexagonAtoms755.assocBAC) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle7_eq_case_5_5_row_0_1_1 : (left1Middle7 5 5) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (HexagonAtoms755.assocBAC) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle7_eq_case_5_5_row_0_2_0 : (left1Middle7 5 5) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (HexagonAtoms755.assocBAC) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle7_eq_case_5_5_row_0_2_1 : (left1Middle7 5 5) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (HexagonAtoms755.assocBAC) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle7_eq_case_5_5_row_0_3_0 : (left1Middle7 5 5) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (HexagonAtoms755.assocBAC) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle7_eq_case_5_5_row_0_3_1 : (left1Middle7 5 5) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (HexagonAtoms755.assocBAC) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle7_eq_case_5_5_row_1_0_0 : (left1Middle7 5 5) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (HexagonAtoms755.assocBAC) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle7_eq_case_5_5_row_1_0_1 : (left1Middle7 5 5) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (HexagonAtoms755.assocBAC) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle7_eq_case_5_5_row_1_1_0 : (left1Middle7 5 5) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (HexagonAtoms755.assocBAC) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle7_eq_case_5_5_row_1_1_1 : (left1Middle7 5 5) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (HexagonAtoms755.assocBAC) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle7_eq_case_5_5_row_1_2_0 : (left1Middle7 5 5) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (HexagonAtoms755.assocBAC) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle7_eq_case_5_5_row_1_2_1 : (left1Middle7 5 5) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (HexagonAtoms755.assocBAC) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle7_eq_case_5_5_row_1_3_0 : (left1Middle7 5 5) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (HexagonAtoms755.assocBAC) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle7_eq_case_5_5_row_1_3_1 : (left1Middle7 5 5) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (HexagonAtoms755.assocBAC) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle7_eq_case_5_5_checked : left1Middle7 5 5 = HexagonAtoms755.assocBAC := by
  funext r
  fin_cases r
  · exact left1Middle7_eq_case_5_5_row_0_0_0
  · exact left1Middle7_eq_case_5_5_row_0_0_1
  · exact left1Middle7_eq_case_5_5_row_0_1_0
  · exact left1Middle7_eq_case_5_5_row_0_1_1
  · exact left1Middle7_eq_case_5_5_row_0_2_0
  · exact left1Middle7_eq_case_5_5_row_0_2_1
  · exact left1Middle7_eq_case_5_5_row_0_3_0
  · exact left1Middle7_eq_case_5_5_row_0_3_1
  · exact left1Middle7_eq_case_5_5_row_1_0_0
  · exact left1Middle7_eq_case_5_5_row_1_0_1
  · exact left1Middle7_eq_case_5_5_row_1_1_0
  · exact left1Middle7_eq_case_5_5_row_1_1_1
  · exact left1Middle7_eq_case_5_5_row_1_2_0
  · exact left1Middle7_eq_case_5_5_row_1_2_1
  · exact left1Middle7_eq_case_5_5_row_1_3_0
  · exact left1Middle7_eq_case_5_5_row_1_3_1

set_option backward.isDefEq.respectTransparency false in
theorem left1Middle7_eq_case_5_5 : left1Middle7 5 5 = associatorZ 5 7 5 * innerLeftZ 7 5 5 := by
  simpa only [HexagonAtoms755.assocABC_eq,
    HexagonAtoms755.outerABC_eq,
    HexagonAtoms755.assocBAC_eq,
    HexagonAtoms755.innerABC_eq,
    HexagonAtoms755.innerRightABC_eq,
    HexagonAtoms755.inverseACB_eq,
    HexagonAtoms755.innerACB_eq,
    HexagonAtoms755.assocBCA_eq,
    HexagonAtoms755.innerRightBAC_eq,
    HexagonAtoms755.assocCAB_eq,
    HexagonAtoms755.outerLeftABC_eq,
    HexagonRowColumn755.innerACB_alias,
    HexagonRowColumn755.assocCAB_alias,
    HexagonRowColumn755.product0_eq,
    HexagonRowColumn755.product1_eq,
    HexagonRowColumn755.product2_eq,
    HexagonRowColumn755.product3_eq,
    HexagonRowColumn755.product4_eq,
    HexagonRowColumn755.product5_eq,
    HexagonRowColumn755.product6_eq,
    HexagonRowColumn755.product7_eq] using left1Middle7_eq_case_5_5_checked

private theorem right0Middle7_eq_case_5_5_row_0_0_0 : (right0Middle7 5 5) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn755.rows_innerRightABC HexagonRowColumn755.cols_assocABC) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle7_eq_case_5_5_row_0_0_1 : (right0Middle7 5 5) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn755.rows_innerRightABC HexagonRowColumn755.cols_assocABC) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle7_eq_case_5_5_row_0_1_0 : (right0Middle7 5 5) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn755.rows_innerRightABC HexagonRowColumn755.cols_assocABC) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle7_eq_case_5_5_row_0_1_1 : (right0Middle7 5 5) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn755.rows_innerRightABC HexagonRowColumn755.cols_assocABC) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle7_eq_case_5_5_row_1_0_0 : (right0Middle7 5 5) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn755.rows_innerRightABC HexagonRowColumn755.cols_assocABC) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle7_eq_case_5_5_row_1_0_1 : (right0Middle7 5 5) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn755.rows_innerRightABC HexagonRowColumn755.cols_assocABC) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle7_eq_case_5_5_row_1_1_0 : (right0Middle7 5 5) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn755.rows_innerRightABC HexagonRowColumn755.cols_assocABC) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle7_eq_case_5_5_row_1_1_1 : (right0Middle7 5 5) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn755.rows_innerRightABC HexagonRowColumn755.cols_assocABC) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle7_eq_case_5_5_row_2_0_0 : (right0Middle7 5 5) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn755.rows_innerRightABC HexagonRowColumn755.cols_assocABC) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle7_eq_case_5_5_row_2_0_1 : (right0Middle7 5 5) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn755.rows_innerRightABC HexagonRowColumn755.cols_assocABC) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle7_eq_case_5_5_row_2_1_0 : (right0Middle7 5 5) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn755.rows_innerRightABC HexagonRowColumn755.cols_assocABC) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle7_eq_case_5_5_row_2_1_1 : (right0Middle7 5 5) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn755.rows_innerRightABC HexagonRowColumn755.cols_assocABC) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle7_eq_case_5_5_row_3_0_0 : (right0Middle7 5 5) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn755.rows_innerRightABC HexagonRowColumn755.cols_assocABC) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle7_eq_case_5_5_row_3_0_1 : (right0Middle7 5 5) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn755.rows_innerRightABC HexagonRowColumn755.cols_assocABC) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle7_eq_case_5_5_row_3_1_0 : (right0Middle7 5 5) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn755.rows_innerRightABC HexagonRowColumn755.cols_assocABC) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle7_eq_case_5_5_row_3_1_1 : (right0Middle7 5 5) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn755.rows_innerRightABC HexagonRowColumn755.cols_assocABC) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle7_eq_case_5_5_checked : right0Middle7 5 5 = rowColumnMul HexagonRowColumn755.rows_innerRightABC HexagonRowColumn755.cols_assocABC := by
  funext r
  fin_cases r
  · exact right0Middle7_eq_case_5_5_row_0_0_0
  · exact right0Middle7_eq_case_5_5_row_0_0_1
  · exact right0Middle7_eq_case_5_5_row_0_1_0
  · exact right0Middle7_eq_case_5_5_row_0_1_1
  · exact right0Middle7_eq_case_5_5_row_1_0_0
  · exact right0Middle7_eq_case_5_5_row_1_0_1
  · exact right0Middle7_eq_case_5_5_row_1_1_0
  · exact right0Middle7_eq_case_5_5_row_1_1_1
  · exact right0Middle7_eq_case_5_5_row_2_0_0
  · exact right0Middle7_eq_case_5_5_row_2_0_1
  · exact right0Middle7_eq_case_5_5_row_2_1_0
  · exact right0Middle7_eq_case_5_5_row_2_1_1
  · exact right0Middle7_eq_case_5_5_row_3_0_0
  · exact right0Middle7_eq_case_5_5_row_3_0_1
  · exact right0Middle7_eq_case_5_5_row_3_1_0
  · exact right0Middle7_eq_case_5_5_row_3_1_1

set_option backward.isDefEq.respectTransparency false in
theorem right0Middle7_eq_case_5_5 : right0Middle7 5 5 = innerRightZ 7 5 5 * associatorZ 7 5 5 := by
  simpa only [HexagonAtoms755.assocABC_eq,
    HexagonAtoms755.outerABC_eq,
    HexagonAtoms755.assocBAC_eq,
    HexagonAtoms755.innerABC_eq,
    HexagonAtoms755.innerRightABC_eq,
    HexagonAtoms755.inverseACB_eq,
    HexagonAtoms755.innerACB_eq,
    HexagonAtoms755.assocBCA_eq,
    HexagonAtoms755.innerRightBAC_eq,
    HexagonAtoms755.assocCAB_eq,
    HexagonAtoms755.outerLeftABC_eq,
    HexagonRowColumn755.innerACB_alias,
    HexagonRowColumn755.assocCAB_alias,
    HexagonRowColumn755.product0_eq,
    HexagonRowColumn755.product1_eq,
    HexagonRowColumn755.product2_eq,
    HexagonRowColumn755.product3_eq,
    HexagonRowColumn755.product4_eq,
    HexagonRowColumn755.product5_eq,
    HexagonRowColumn755.product6_eq,
    HexagonRowColumn755.product7_eq] using right0Middle7_eq_case_5_5_checked

private theorem right1Middle7_eq_case_5_5_row_0_0_0 : (right1Middle7 5 5) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn755.rows_inverseACB HexagonRowColumn755.cols_right0) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle7_eq_case_5_5_row_0_0_1 : (right1Middle7 5 5) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn755.rows_inverseACB HexagonRowColumn755.cols_right0) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle7_eq_case_5_5_row_0_1_0 : (right1Middle7 5 5) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn755.rows_inverseACB HexagonRowColumn755.cols_right0) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle7_eq_case_5_5_row_0_1_1 : (right1Middle7 5 5) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn755.rows_inverseACB HexagonRowColumn755.cols_right0) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle7_eq_case_5_5_row_0_2_0 : (right1Middle7 5 5) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn755.rows_inverseACB HexagonRowColumn755.cols_right0) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle7_eq_case_5_5_row_0_2_1 : (right1Middle7 5 5) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn755.rows_inverseACB HexagonRowColumn755.cols_right0) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle7_eq_case_5_5_row_0_3_0 : (right1Middle7 5 5) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn755.rows_inverseACB HexagonRowColumn755.cols_right0) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle7_eq_case_5_5_row_0_3_1 : (right1Middle7 5 5) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn755.rows_inverseACB HexagonRowColumn755.cols_right0) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle7_eq_case_5_5_row_1_0_0 : (right1Middle7 5 5) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn755.rows_inverseACB HexagonRowColumn755.cols_right0) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle7_eq_case_5_5_row_1_0_1 : (right1Middle7 5 5) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn755.rows_inverseACB HexagonRowColumn755.cols_right0) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle7_eq_case_5_5_row_1_1_0 : (right1Middle7 5 5) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn755.rows_inverseACB HexagonRowColumn755.cols_right0) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle7_eq_case_5_5_row_1_1_1 : (right1Middle7 5 5) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn755.rows_inverseACB HexagonRowColumn755.cols_right0) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle7_eq_case_5_5_row_1_2_0 : (right1Middle7 5 5) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn755.rows_inverseACB HexagonRowColumn755.cols_right0) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle7_eq_case_5_5_row_1_2_1 : (right1Middle7 5 5) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn755.rows_inverseACB HexagonRowColumn755.cols_right0) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle7_eq_case_5_5_row_1_3_0 : (right1Middle7 5 5) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn755.rows_inverseACB HexagonRowColumn755.cols_right0) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle7_eq_case_5_5_row_1_3_1 : (right1Middle7 5 5) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn755.rows_inverseACB HexagonRowColumn755.cols_right0) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle7_eq_case_5_5_checked : right1Middle7 5 5 = rowColumnMul HexagonRowColumn755.rows_inverseACB HexagonRowColumn755.cols_right0 := by
  funext r
  fin_cases r
  · exact right1Middle7_eq_case_5_5_row_0_0_0
  · exact right1Middle7_eq_case_5_5_row_0_0_1
  · exact right1Middle7_eq_case_5_5_row_0_1_0
  · exact right1Middle7_eq_case_5_5_row_0_1_1
  · exact right1Middle7_eq_case_5_5_row_0_2_0
  · exact right1Middle7_eq_case_5_5_row_0_2_1
  · exact right1Middle7_eq_case_5_5_row_0_3_0
  · exact right1Middle7_eq_case_5_5_row_0_3_1
  · exact right1Middle7_eq_case_5_5_row_1_0_0
  · exact right1Middle7_eq_case_5_5_row_1_0_1
  · exact right1Middle7_eq_case_5_5_row_1_1_0
  · exact right1Middle7_eq_case_5_5_row_1_1_1
  · exact right1Middle7_eq_case_5_5_row_1_2_0
  · exact right1Middle7_eq_case_5_5_row_1_2_1
  · exact right1Middle7_eq_case_5_5_row_1_3_0
  · exact right1Middle7_eq_case_5_5_row_1_3_1

set_option backward.isDefEq.respectTransparency false in
theorem right1Middle7_eq_case_5_5 : right1Middle7 5 5 = associatorInverseZ 7 5 5 * right0Middle7 5 5 := by
  simpa only [HexagonAtoms755.assocABC_eq,
    HexagonAtoms755.outerABC_eq,
    HexagonAtoms755.assocBAC_eq,
    HexagonAtoms755.innerABC_eq,
    HexagonAtoms755.innerRightABC_eq,
    HexagonAtoms755.inverseACB_eq,
    HexagonAtoms755.innerACB_eq,
    HexagonAtoms755.assocBCA_eq,
    HexagonAtoms755.innerRightBAC_eq,
    HexagonAtoms755.assocCAB_eq,
    HexagonAtoms755.outerLeftABC_eq,
    HexagonRowColumn755.innerACB_alias,
    HexagonRowColumn755.assocCAB_alias,
    HexagonRowColumn755.product0_eq,
    HexagonRowColumn755.product1_eq,
    HexagonRowColumn755.product2_eq,
    HexagonRowColumn755.product3_eq,
    HexagonRowColumn755.product4_eq,
    HexagonRowColumn755.product5_eq,
    HexagonRowColumn755.product6_eq,
    HexagonRowColumn755.product7_eq] using right1Middle7_eq_case_5_5_checked

private theorem right2Middle7_eq_case_5_5_row_0_0_0 : (right2Middle7 5 5) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (right1Middle7 5 5) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle7_eq_case_5_5_row_0_0_1 : (right2Middle7 5 5) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (right1Middle7 5 5) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle7_eq_case_5_5_row_0_1_0 : (right2Middle7 5 5) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (right1Middle7 5 5) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle7_eq_case_5_5_row_0_1_1 : (right2Middle7 5 5) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (right1Middle7 5 5) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle7_eq_case_5_5_row_0_2_0 : (right2Middle7 5 5) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (right1Middle7 5 5) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle7_eq_case_5_5_row_0_2_1 : (right2Middle7 5 5) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (right1Middle7 5 5) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle7_eq_case_5_5_row_0_3_0 : (right2Middle7 5 5) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (right1Middle7 5 5) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle7_eq_case_5_5_row_0_3_1 : (right2Middle7 5 5) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (right1Middle7 5 5) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle7_eq_case_5_5_row_1_0_0 : (right2Middle7 5 5) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (right1Middle7 5 5) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle7_eq_case_5_5_row_1_0_1 : (right2Middle7 5 5) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (right1Middle7 5 5) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle7_eq_case_5_5_row_1_1_0 : (right2Middle7 5 5) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (right1Middle7 5 5) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle7_eq_case_5_5_row_1_1_1 : (right2Middle7 5 5) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (right1Middle7 5 5) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle7_eq_case_5_5_row_1_2_0 : (right2Middle7 5 5) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (right1Middle7 5 5) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle7_eq_case_5_5_row_1_2_1 : (right2Middle7 5 5) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (right1Middle7 5 5) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle7_eq_case_5_5_row_1_3_0 : (right2Middle7 5 5) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (right1Middle7 5 5) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle7_eq_case_5_5_row_1_3_1 : (right2Middle7 5 5) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (right1Middle7 5 5) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle7_eq_case_5_5_checked : right2Middle7 5 5 = right1Middle7 5 5 := by
  funext r
  fin_cases r
  · exact right2Middle7_eq_case_5_5_row_0_0_0
  · exact right2Middle7_eq_case_5_5_row_0_0_1
  · exact right2Middle7_eq_case_5_5_row_0_1_0
  · exact right2Middle7_eq_case_5_5_row_0_1_1
  · exact right2Middle7_eq_case_5_5_row_0_2_0
  · exact right2Middle7_eq_case_5_5_row_0_2_1
  · exact right2Middle7_eq_case_5_5_row_0_3_0
  · exact right2Middle7_eq_case_5_5_row_0_3_1
  · exact right2Middle7_eq_case_5_5_row_1_0_0
  · exact right2Middle7_eq_case_5_5_row_1_0_1
  · exact right2Middle7_eq_case_5_5_row_1_1_0
  · exact right2Middle7_eq_case_5_5_row_1_1_1
  · exact right2Middle7_eq_case_5_5_row_1_2_0
  · exact right2Middle7_eq_case_5_5_row_1_2_1
  · exact right2Middle7_eq_case_5_5_row_1_3_0
  · exact right2Middle7_eq_case_5_5_row_1_3_1

set_option backward.isDefEq.respectTransparency false in
theorem right2Middle7_eq_case_5_5 : right2Middle7 5 5 = innerLeftZ 7 5 5 * right1Middle7 5 5 := by
  simpa only [HexagonAtoms755.assocABC_eq,
    HexagonAtoms755.outerABC_eq,
    HexagonAtoms755.assocBAC_eq,
    HexagonAtoms755.innerABC_eq,
    HexagonAtoms755.innerRightABC_eq,
    HexagonAtoms755.inverseACB_eq,
    HexagonAtoms755.innerACB_eq,
    HexagonAtoms755.assocBCA_eq,
    HexagonAtoms755.innerRightBAC_eq,
    HexagonAtoms755.assocCAB_eq,
    HexagonAtoms755.outerLeftABC_eq,
    HexagonRowColumn755.innerACB_alias,
    HexagonRowColumn755.assocCAB_alias,
    HexagonRowColumn755.product0_eq,
    HexagonRowColumn755.product1_eq,
    HexagonRowColumn755.product2_eq,
    HexagonRowColumn755.product3_eq,
    HexagonRowColumn755.product4_eq,
    HexagonRowColumn755.product5_eq,
    HexagonRowColumn755.product6_eq,
    HexagonRowColumn755.product7_eq] using right2Middle7_eq_case_5_5_checked

private theorem leftFinal7_case_5_5_row_0_0_0 : (((-1 : ℤ) ^ (leftScaleBit 7 5 5).val * positiveScale (leftScaleExponent 7 5 5)) •
      (rowColumnMul HexagonRowColumn755.rows_assocBCA HexagonRowColumn755.cols_left0)) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 7 5 5) • (left1Middle7 5 5)) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal7_case_5_5_row_0_0_1 : (((-1 : ℤ) ^ (leftScaleBit 7 5 5).val * positiveScale (leftScaleExponent 7 5 5)) •
      (rowColumnMul HexagonRowColumn755.rows_assocBCA HexagonRowColumn755.cols_left0)) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 7 5 5) • (left1Middle7 5 5)) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal7_case_5_5_row_0_1_0 : (((-1 : ℤ) ^ (leftScaleBit 7 5 5).val * positiveScale (leftScaleExponent 7 5 5)) •
      (rowColumnMul HexagonRowColumn755.rows_assocBCA HexagonRowColumn755.cols_left0)) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 7 5 5) • (left1Middle7 5 5)) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal7_case_5_5_row_0_1_1 : (((-1 : ℤ) ^ (leftScaleBit 7 5 5).val * positiveScale (leftScaleExponent 7 5 5)) •
      (rowColumnMul HexagonRowColumn755.rows_assocBCA HexagonRowColumn755.cols_left0)) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 7 5 5) • (left1Middle7 5 5)) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal7_case_5_5_row_0_2_0 : (((-1 : ℤ) ^ (leftScaleBit 7 5 5).val * positiveScale (leftScaleExponent 7 5 5)) •
      (rowColumnMul HexagonRowColumn755.rows_assocBCA HexagonRowColumn755.cols_left0)) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 7 5 5) • (left1Middle7 5 5)) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal7_case_5_5_row_0_2_1 : (((-1 : ℤ) ^ (leftScaleBit 7 5 5).val * positiveScale (leftScaleExponent 7 5 5)) •
      (rowColumnMul HexagonRowColumn755.rows_assocBCA HexagonRowColumn755.cols_left0)) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 7 5 5) • (left1Middle7 5 5)) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal7_case_5_5_row_0_3_0 : (((-1 : ℤ) ^ (leftScaleBit 7 5 5).val * positiveScale (leftScaleExponent 7 5 5)) •
      (rowColumnMul HexagonRowColumn755.rows_assocBCA HexagonRowColumn755.cols_left0)) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 7 5 5) • (left1Middle7 5 5)) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal7_case_5_5_row_0_3_1 : (((-1 : ℤ) ^ (leftScaleBit 7 5 5).val * positiveScale (leftScaleExponent 7 5 5)) •
      (rowColumnMul HexagonRowColumn755.rows_assocBCA HexagonRowColumn755.cols_left0)) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 7 5 5) • (left1Middle7 5 5)) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal7_case_5_5_row_1_0_0 : (((-1 : ℤ) ^ (leftScaleBit 7 5 5).val * positiveScale (leftScaleExponent 7 5 5)) •
      (rowColumnMul HexagonRowColumn755.rows_assocBCA HexagonRowColumn755.cols_left0)) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 7 5 5) • (left1Middle7 5 5)) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal7_case_5_5_row_1_0_1 : (((-1 : ℤ) ^ (leftScaleBit 7 5 5).val * positiveScale (leftScaleExponent 7 5 5)) •
      (rowColumnMul HexagonRowColumn755.rows_assocBCA HexagonRowColumn755.cols_left0)) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 7 5 5) • (left1Middle7 5 5)) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal7_case_5_5_row_1_1_0 : (((-1 : ℤ) ^ (leftScaleBit 7 5 5).val * positiveScale (leftScaleExponent 7 5 5)) •
      (rowColumnMul HexagonRowColumn755.rows_assocBCA HexagonRowColumn755.cols_left0)) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 7 5 5) • (left1Middle7 5 5)) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal7_case_5_5_row_1_1_1 : (((-1 : ℤ) ^ (leftScaleBit 7 5 5).val * positiveScale (leftScaleExponent 7 5 5)) •
      (rowColumnMul HexagonRowColumn755.rows_assocBCA HexagonRowColumn755.cols_left0)) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 7 5 5) • (left1Middle7 5 5)) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal7_case_5_5_row_1_2_0 : (((-1 : ℤ) ^ (leftScaleBit 7 5 5).val * positiveScale (leftScaleExponent 7 5 5)) •
      (rowColumnMul HexagonRowColumn755.rows_assocBCA HexagonRowColumn755.cols_left0)) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 7 5 5) • (left1Middle7 5 5)) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal7_case_5_5_row_1_2_1 : (((-1 : ℤ) ^ (leftScaleBit 7 5 5).val * positiveScale (leftScaleExponent 7 5 5)) •
      (rowColumnMul HexagonRowColumn755.rows_assocBCA HexagonRowColumn755.cols_left0)) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 7 5 5) • (left1Middle7 5 5)) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal7_case_5_5_row_1_3_0 : (((-1 : ℤ) ^ (leftScaleBit 7 5 5).val * positiveScale (leftScaleExponent 7 5 5)) •
      (rowColumnMul HexagonRowColumn755.rows_assocBCA HexagonRowColumn755.cols_left0)) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 7 5 5) • (left1Middle7 5 5)) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal7_case_5_5_row_1_3_1 : (((-1 : ℤ) ^ (leftScaleBit 7 5 5).val * positiveScale (leftScaleExponent 7 5 5)) •
      (rowColumnMul HexagonRowColumn755.rows_assocBCA HexagonRowColumn755.cols_left0)) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 7 5 5) • (left1Middle7 5 5)) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal7_case_5_5_checked : ((-1 : ℤ) ^ (leftScaleBit 7 5 5).val * positiveScale (leftScaleExponent 7 5 5)) •
      (rowColumnMul HexagonRowColumn755.rows_assocBCA HexagonRowColumn755.cols_left0) = negativeScale (leftScaleExponent 7 5 5) • (left1Middle7 5 5) := by
  funext r
  fin_cases r
  · exact leftFinal7_case_5_5_row_0_0_0
  · exact leftFinal7_case_5_5_row_0_0_1
  · exact leftFinal7_case_5_5_row_0_1_0
  · exact leftFinal7_case_5_5_row_0_1_1
  · exact leftFinal7_case_5_5_row_0_2_0
  · exact leftFinal7_case_5_5_row_0_2_1
  · exact leftFinal7_case_5_5_row_0_3_0
  · exact leftFinal7_case_5_5_row_0_3_1
  · exact leftFinal7_case_5_5_row_1_0_0
  · exact leftFinal7_case_5_5_row_1_0_1
  · exact leftFinal7_case_5_5_row_1_1_0
  · exact leftFinal7_case_5_5_row_1_1_1
  · exact leftFinal7_case_5_5_row_1_2_0
  · exact leftFinal7_case_5_5_row_1_2_1
  · exact leftFinal7_case_5_5_row_1_3_0
  · exact leftFinal7_case_5_5_row_1_3_1

set_option backward.isDefEq.respectTransparency false in
theorem leftFinal7_case_5_5 : ((-1 : ℤ) ^ (leftScaleBit 7 5 5).val * positiveScale (leftScaleExponent 7 5 5)) •
      (associatorZ 5 5 7 * left0Middle7 5 5) = negativeScale (leftScaleExponent 7 5 5) • (innerRightZ 5 7 5 * left1Middle7 5 5) := by
  simpa only [HexagonAtoms755.assocABC_eq,
    HexagonAtoms755.outerABC_eq,
    HexagonAtoms755.assocBAC_eq,
    HexagonAtoms755.innerABC_eq,
    HexagonAtoms755.innerRightABC_eq,
    HexagonAtoms755.inverseACB_eq,
    HexagonAtoms755.innerACB_eq,
    HexagonAtoms755.assocBCA_eq,
    HexagonAtoms755.innerRightBAC_eq,
    HexagonAtoms755.assocCAB_eq,
    HexagonAtoms755.outerLeftABC_eq,
    HexagonRowColumn755.innerACB_alias,
    HexagonRowColumn755.assocCAB_alias,
    HexagonRowColumn755.product0_eq,
    HexagonRowColumn755.product1_eq,
    HexagonRowColumn755.product2_eq,
    HexagonRowColumn755.product3_eq,
    HexagonRowColumn755.product4_eq,
    HexagonRowColumn755.product5_eq,
    HexagonRowColumn755.product6_eq,
    HexagonRowColumn755.product7_eq] using leftFinal7_case_5_5_checked

private theorem rightFinal7_case_5_5_row_0_0_0 : (((-1 : ℤ) ^ (rightScaleBit 7 5 5).val * positiveScale (rightScaleExponent 7 5 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 5 5 : ℤ)) • HexagonAtoms755.outerLeftABC) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (negativeScale (rightScaleExponent 7 5 5) • (rowColumnMul HexagonRowColumn755.rows_assocBAC HexagonRowColumn755.cols_right2)) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal7_case_5_5_row_0_0_1 : (((-1 : ℤ) ^ (rightScaleBit 7 5 5).val * positiveScale (rightScaleExponent 7 5 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 5 5 : ℤ)) • HexagonAtoms755.outerLeftABC) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (negativeScale (rightScaleExponent 7 5 5) • (rowColumnMul HexagonRowColumn755.rows_assocBAC HexagonRowColumn755.cols_right2)) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal7_case_5_5_row_0_1_0 : (((-1 : ℤ) ^ (rightScaleBit 7 5 5).val * positiveScale (rightScaleExponent 7 5 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 5 5 : ℤ)) • HexagonAtoms755.outerLeftABC) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (negativeScale (rightScaleExponent 7 5 5) • (rowColumnMul HexagonRowColumn755.rows_assocBAC HexagonRowColumn755.cols_right2)) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal7_case_5_5_row_0_1_1 : (((-1 : ℤ) ^ (rightScaleBit 7 5 5).val * positiveScale (rightScaleExponent 7 5 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 5 5 : ℤ)) • HexagonAtoms755.outerLeftABC) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (negativeScale (rightScaleExponent 7 5 5) • (rowColumnMul HexagonRowColumn755.rows_assocBAC HexagonRowColumn755.cols_right2)) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal7_case_5_5_row_0_2_0 : (((-1 : ℤ) ^ (rightScaleBit 7 5 5).val * positiveScale (rightScaleExponent 7 5 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 5 5 : ℤ)) • HexagonAtoms755.outerLeftABC) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (negativeScale (rightScaleExponent 7 5 5) • (rowColumnMul HexagonRowColumn755.rows_assocBAC HexagonRowColumn755.cols_right2)) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal7_case_5_5_row_0_2_1 : (((-1 : ℤ) ^ (rightScaleBit 7 5 5).val * positiveScale (rightScaleExponent 7 5 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 5 5 : ℤ)) • HexagonAtoms755.outerLeftABC) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (negativeScale (rightScaleExponent 7 5 5) • (rowColumnMul HexagonRowColumn755.rows_assocBAC HexagonRowColumn755.cols_right2)) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal7_case_5_5_row_0_3_0 : (((-1 : ℤ) ^ (rightScaleBit 7 5 5).val * positiveScale (rightScaleExponent 7 5 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 5 5 : ℤ)) • HexagonAtoms755.outerLeftABC) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (negativeScale (rightScaleExponent 7 5 5) • (rowColumnMul HexagonRowColumn755.rows_assocBAC HexagonRowColumn755.cols_right2)) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal7_case_5_5_row_0_3_1 : (((-1 : ℤ) ^ (rightScaleBit 7 5 5).val * positiveScale (rightScaleExponent 7 5 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 5 5 : ℤ)) • HexagonAtoms755.outerLeftABC) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (negativeScale (rightScaleExponent 7 5 5) • (rowColumnMul HexagonRowColumn755.rows_assocBAC HexagonRowColumn755.cols_right2)) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal7_case_5_5_row_1_0_0 : (((-1 : ℤ) ^ (rightScaleBit 7 5 5).val * positiveScale (rightScaleExponent 7 5 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 5 5 : ℤ)) • HexagonAtoms755.outerLeftABC) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (negativeScale (rightScaleExponent 7 5 5) • (rowColumnMul HexagonRowColumn755.rows_assocBAC HexagonRowColumn755.cols_right2)) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal7_case_5_5_row_1_0_1 : (((-1 : ℤ) ^ (rightScaleBit 7 5 5).val * positiveScale (rightScaleExponent 7 5 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 5 5 : ℤ)) • HexagonAtoms755.outerLeftABC) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (negativeScale (rightScaleExponent 7 5 5) • (rowColumnMul HexagonRowColumn755.rows_assocBAC HexagonRowColumn755.cols_right2)) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal7_case_5_5_row_1_1_0 : (((-1 : ℤ) ^ (rightScaleBit 7 5 5).val * positiveScale (rightScaleExponent 7 5 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 5 5 : ℤ)) • HexagonAtoms755.outerLeftABC) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (negativeScale (rightScaleExponent 7 5 5) • (rowColumnMul HexagonRowColumn755.rows_assocBAC HexagonRowColumn755.cols_right2)) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal7_case_5_5_row_1_1_1 : (((-1 : ℤ) ^ (rightScaleBit 7 5 5).val * positiveScale (rightScaleExponent 7 5 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 5 5 : ℤ)) • HexagonAtoms755.outerLeftABC) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (negativeScale (rightScaleExponent 7 5 5) • (rowColumnMul HexagonRowColumn755.rows_assocBAC HexagonRowColumn755.cols_right2)) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal7_case_5_5_row_1_2_0 : (((-1 : ℤ) ^ (rightScaleBit 7 5 5).val * positiveScale (rightScaleExponent 7 5 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 5 5 : ℤ)) • HexagonAtoms755.outerLeftABC) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (negativeScale (rightScaleExponent 7 5 5) • (rowColumnMul HexagonRowColumn755.rows_assocBAC HexagonRowColumn755.cols_right2)) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal7_case_5_5_row_1_2_1 : (((-1 : ℤ) ^ (rightScaleBit 7 5 5).val * positiveScale (rightScaleExponent 7 5 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 5 5 : ℤ)) • HexagonAtoms755.outerLeftABC) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (negativeScale (rightScaleExponent 7 5 5) • (rowColumnMul HexagonRowColumn755.rows_assocBAC HexagonRowColumn755.cols_right2)) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal7_case_5_5_row_1_3_0 : (((-1 : ℤ) ^ (rightScaleBit 7 5 5).val * positiveScale (rightScaleExponent 7 5 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 5 5 : ℤ)) • HexagonAtoms755.outerLeftABC) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (negativeScale (rightScaleExponent 7 5 5) • (rowColumnMul HexagonRowColumn755.rows_assocBAC HexagonRowColumn755.cols_right2)) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal7_case_5_5_row_1_3_1 : (((-1 : ℤ) ^ (rightScaleBit 7 5 5).val * positiveScale (rightScaleExponent 7 5 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 5 5 : ℤ)) • HexagonAtoms755.outerLeftABC) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (negativeScale (rightScaleExponent 7 5 5) • (rowColumnMul HexagonRowColumn755.rows_assocBAC HexagonRowColumn755.cols_right2)) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal7_case_5_5_checked : ((-1 : ℤ) ^ (rightScaleBit 7 5 5).val * positiveScale (rightScaleExponent 7 5 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 5 5 : ℤ)) • HexagonAtoms755.outerLeftABC = negativeScale (rightScaleExponent 7 5 5) • (rowColumnMul HexagonRowColumn755.rows_assocBAC HexagonRowColumn755.cols_right2) := by
  funext r
  fin_cases r
  · exact rightFinal7_case_5_5_row_0_0_0
  · exact rightFinal7_case_5_5_row_0_0_1
  · exact rightFinal7_case_5_5_row_0_1_0
  · exact rightFinal7_case_5_5_row_0_1_1
  · exact rightFinal7_case_5_5_row_0_2_0
  · exact rightFinal7_case_5_5_row_0_2_1
  · exact rightFinal7_case_5_5_row_0_3_0
  · exact rightFinal7_case_5_5_row_0_3_1
  · exact rightFinal7_case_5_5_row_1_0_0
  · exact rightFinal7_case_5_5_row_1_0_1
  · exact rightFinal7_case_5_5_row_1_1_0
  · exact rightFinal7_case_5_5_row_1_1_1
  · exact rightFinal7_case_5_5_row_1_2_0
  · exact rightFinal7_case_5_5_row_1_2_1
  · exact rightFinal7_case_5_5_row_1_3_0
  · exact rightFinal7_case_5_5_row_1_3_1

set_option backward.isDefEq.respectTransparency false in
theorem rightFinal7_case_5_5 : ((-1 : ℤ) ^ (rightScaleBit 7 5 5).val * positiveScale (rightScaleExponent 7 5 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 5 5 : ℤ)) • outerLeftZ 7 5 5 = negativeScale (rightScaleExponent 7 5 5) • (associatorZ 5 7 5 * right2Middle7 5 5) := by
  simpa only [HexagonAtoms755.assocABC_eq,
    HexagonAtoms755.outerABC_eq,
    HexagonAtoms755.assocBAC_eq,
    HexagonAtoms755.innerABC_eq,
    HexagonAtoms755.innerRightABC_eq,
    HexagonAtoms755.inverseACB_eq,
    HexagonAtoms755.innerACB_eq,
    HexagonAtoms755.assocBCA_eq,
    HexagonAtoms755.innerRightBAC_eq,
    HexagonAtoms755.assocCAB_eq,
    HexagonAtoms755.outerLeftABC_eq,
    HexagonRowColumn755.innerACB_alias,
    HexagonRowColumn755.assocCAB_alias,
    HexagonRowColumn755.product0_eq,
    HexagonRowColumn755.product1_eq,
    HexagonRowColumn755.product2_eq,
    HexagonRowColumn755.product3_eq,
    HexagonRowColumn755.product4_eq,
    HexagonRowColumn755.product5_eq,
    HexagonRowColumn755.product6_eq,
    HexagonRowColumn755.product7_eq] using rightFinal7_case_5_5_checked

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonCases7
