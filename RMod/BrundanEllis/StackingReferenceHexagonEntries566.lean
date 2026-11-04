import RMod.BrundanEllis.StackingReferenceHexagonMiddle5
import RMod.BrundanEllis.StackingReferenceSparseMatrixCheck
import RMod.BrundanEllis.StackingReferenceHexagonAtoms566
import RMod.BrundanEllis.StackingReferenceHexagonRowColumn566

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

private theorem left0Middle5_eq_case_6_6_row_0_0_0 : (left0Middle5 6 6) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (HexagonAtoms566.assocABC) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_6_6_row_0_0_1 : (left0Middle5 6 6) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (HexagonAtoms566.assocABC) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_6_6_row_0_1_0 : (left0Middle5 6 6) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (HexagonAtoms566.assocABC) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_6_6_row_0_1_1 : (left0Middle5 6 6) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (HexagonAtoms566.assocABC) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_6_6_row_0_2_0 : (left0Middle5 6 6) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (HexagonAtoms566.assocABC) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_6_6_row_0_2_1 : (left0Middle5 6 6) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (HexagonAtoms566.assocABC) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_6_6_row_0_3_0 : (left0Middle5 6 6) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (HexagonAtoms566.assocABC) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_6_6_row_0_3_1 : (left0Middle5 6 6) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (HexagonAtoms566.assocABC) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_6_6_row_1_0_0 : (left0Middle5 6 6) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (HexagonAtoms566.assocABC) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_6_6_row_1_0_1 : (left0Middle5 6 6) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (HexagonAtoms566.assocABC) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_6_6_row_1_1_0 : (left0Middle5 6 6) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (HexagonAtoms566.assocABC) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_6_6_row_1_1_1 : (left0Middle5 6 6) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (HexagonAtoms566.assocABC) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_6_6_row_1_2_0 : (left0Middle5 6 6) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (HexagonAtoms566.assocABC) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_6_6_row_1_2_1 : (left0Middle5 6 6) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (HexagonAtoms566.assocABC) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_6_6_row_1_3_0 : (left0Middle5 6 6) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (HexagonAtoms566.assocABC) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_6_6_row_1_3_1 : (left0Middle5 6 6) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (HexagonAtoms566.assocABC) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_6_6_checked : left0Middle5 6 6 = HexagonAtoms566.assocABC := by
  funext r
  fin_cases r
  · exact left0Middle5_eq_case_6_6_row_0_0_0
  · exact left0Middle5_eq_case_6_6_row_0_0_1
  · exact left0Middle5_eq_case_6_6_row_0_1_0
  · exact left0Middle5_eq_case_6_6_row_0_1_1
  · exact left0Middle5_eq_case_6_6_row_0_2_0
  · exact left0Middle5_eq_case_6_6_row_0_2_1
  · exact left0Middle5_eq_case_6_6_row_0_3_0
  · exact left0Middle5_eq_case_6_6_row_0_3_1
  · exact left0Middle5_eq_case_6_6_row_1_0_0
  · exact left0Middle5_eq_case_6_6_row_1_0_1
  · exact left0Middle5_eq_case_6_6_row_1_1_0
  · exact left0Middle5_eq_case_6_6_row_1_1_1
  · exact left0Middle5_eq_case_6_6_row_1_2_0
  · exact left0Middle5_eq_case_6_6_row_1_2_1
  · exact left0Middle5_eq_case_6_6_row_1_3_0
  · exact left0Middle5_eq_case_6_6_row_1_3_1

set_option backward.isDefEq.respectTransparency false in
theorem left0Middle5_eq_case_6_6 : left0Middle5 6 6 = outerRightZ 5 6 6 * associatorZ 5 6 6 := by
  simpa only [HexagonAtoms566.assocABC_eq,
    HexagonAtoms566.outerABC_eq,
    HexagonAtoms566.assocBAC_eq,
    HexagonAtoms566.innerABC_eq,
    HexagonAtoms566.innerRightABC_eq,
    HexagonAtoms566.inverseACB_eq,
    HexagonAtoms566.innerACB_eq,
    HexagonAtoms566.assocBCA_eq,
    HexagonAtoms566.innerRightBAC_eq,
    HexagonAtoms566.assocCAB_eq,
    HexagonAtoms566.outerLeftABC_eq,
    HexagonRowColumn566.innerACB_alias,
    HexagonRowColumn566.assocCAB_alias,
    HexagonRowColumn566.product0_eq,
    HexagonRowColumn566.product1_eq,
    HexagonRowColumn566.product2_eq,
    HexagonRowColumn566.product3_eq,
    HexagonRowColumn566.product4_eq,
    HexagonRowColumn566.product5_eq,
    HexagonRowColumn566.product6_eq,
    HexagonRowColumn566.product7_eq] using left0Middle5_eq_case_6_6_checked

private theorem left1Middle5_eq_case_6_6_row_0_0_0 : (left1Middle5 6 6) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (HexagonAtoms566.assocBAC) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_6_6_row_0_0_1 : (left1Middle5 6 6) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (HexagonAtoms566.assocBAC) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_6_6_row_0_1_0 : (left1Middle5 6 6) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (HexagonAtoms566.assocBAC) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_6_6_row_0_1_1 : (left1Middle5 6 6) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (HexagonAtoms566.assocBAC) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_6_6_row_0_2_0 : (left1Middle5 6 6) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (HexagonAtoms566.assocBAC) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_6_6_row_0_2_1 : (left1Middle5 6 6) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (HexagonAtoms566.assocBAC) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_6_6_row_0_3_0 : (left1Middle5 6 6) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (HexagonAtoms566.assocBAC) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_6_6_row_0_3_1 : (left1Middle5 6 6) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (HexagonAtoms566.assocBAC) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_6_6_row_1_0_0 : (left1Middle5 6 6) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (HexagonAtoms566.assocBAC) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_6_6_row_1_0_1 : (left1Middle5 6 6) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (HexagonAtoms566.assocBAC) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_6_6_row_1_1_0 : (left1Middle5 6 6) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (HexagonAtoms566.assocBAC) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_6_6_row_1_1_1 : (left1Middle5 6 6) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (HexagonAtoms566.assocBAC) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_6_6_row_1_2_0 : (left1Middle5 6 6) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (HexagonAtoms566.assocBAC) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_6_6_row_1_2_1 : (left1Middle5 6 6) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (HexagonAtoms566.assocBAC) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_6_6_row_1_3_0 : (left1Middle5 6 6) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (HexagonAtoms566.assocBAC) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_6_6_row_1_3_1 : (left1Middle5 6 6) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (HexagonAtoms566.assocBAC) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_6_6_checked : left1Middle5 6 6 = HexagonAtoms566.assocBAC := by
  funext r
  fin_cases r
  · exact left1Middle5_eq_case_6_6_row_0_0_0
  · exact left1Middle5_eq_case_6_6_row_0_0_1
  · exact left1Middle5_eq_case_6_6_row_0_1_0
  · exact left1Middle5_eq_case_6_6_row_0_1_1
  · exact left1Middle5_eq_case_6_6_row_0_2_0
  · exact left1Middle5_eq_case_6_6_row_0_2_1
  · exact left1Middle5_eq_case_6_6_row_0_3_0
  · exact left1Middle5_eq_case_6_6_row_0_3_1
  · exact left1Middle5_eq_case_6_6_row_1_0_0
  · exact left1Middle5_eq_case_6_6_row_1_0_1
  · exact left1Middle5_eq_case_6_6_row_1_1_0
  · exact left1Middle5_eq_case_6_6_row_1_1_1
  · exact left1Middle5_eq_case_6_6_row_1_2_0
  · exact left1Middle5_eq_case_6_6_row_1_2_1
  · exact left1Middle5_eq_case_6_6_row_1_3_0
  · exact left1Middle5_eq_case_6_6_row_1_3_1

set_option backward.isDefEq.respectTransparency false in
theorem left1Middle5_eq_case_6_6 : left1Middle5 6 6 = associatorZ 6 5 6 * innerLeftZ 5 6 6 := by
  simpa only [HexagonAtoms566.assocABC_eq,
    HexagonAtoms566.outerABC_eq,
    HexagonAtoms566.assocBAC_eq,
    HexagonAtoms566.innerABC_eq,
    HexagonAtoms566.innerRightABC_eq,
    HexagonAtoms566.inverseACB_eq,
    HexagonAtoms566.innerACB_eq,
    HexagonAtoms566.assocBCA_eq,
    HexagonAtoms566.innerRightBAC_eq,
    HexagonAtoms566.assocCAB_eq,
    HexagonAtoms566.outerLeftABC_eq,
    HexagonRowColumn566.innerACB_alias,
    HexagonRowColumn566.assocCAB_alias,
    HexagonRowColumn566.product0_eq,
    HexagonRowColumn566.product1_eq,
    HexagonRowColumn566.product2_eq,
    HexagonRowColumn566.product3_eq,
    HexagonRowColumn566.product4_eq,
    HexagonRowColumn566.product5_eq,
    HexagonRowColumn566.product6_eq,
    HexagonRowColumn566.product7_eq] using left1Middle5_eq_case_6_6_checked

private theorem right0Middle5_eq_case_6_6_row_0_0_0 : (right0Middle5 6 6) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn566.rows_innerRightABC HexagonRowColumn566.cols_assocABC) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_6_6_row_0_0_1 : (right0Middle5 6 6) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn566.rows_innerRightABC HexagonRowColumn566.cols_assocABC) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_6_6_row_0_1_0 : (right0Middle5 6 6) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn566.rows_innerRightABC HexagonRowColumn566.cols_assocABC) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_6_6_row_0_1_1 : (right0Middle5 6 6) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn566.rows_innerRightABC HexagonRowColumn566.cols_assocABC) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_6_6_row_0_2_0 : (right0Middle5 6 6) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn566.rows_innerRightABC HexagonRowColumn566.cols_assocABC) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_6_6_row_0_2_1 : (right0Middle5 6 6) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn566.rows_innerRightABC HexagonRowColumn566.cols_assocABC) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_6_6_row_0_3_0 : (right0Middle5 6 6) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn566.rows_innerRightABC HexagonRowColumn566.cols_assocABC) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_6_6_row_0_3_1 : (right0Middle5 6 6) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn566.rows_innerRightABC HexagonRowColumn566.cols_assocABC) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_6_6_row_1_0_0 : (right0Middle5 6 6) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn566.rows_innerRightABC HexagonRowColumn566.cols_assocABC) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_6_6_row_1_0_1 : (right0Middle5 6 6) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn566.rows_innerRightABC HexagonRowColumn566.cols_assocABC) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_6_6_row_1_1_0 : (right0Middle5 6 6) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn566.rows_innerRightABC HexagonRowColumn566.cols_assocABC) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_6_6_row_1_1_1 : (right0Middle5 6 6) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn566.rows_innerRightABC HexagonRowColumn566.cols_assocABC) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_6_6_row_1_2_0 : (right0Middle5 6 6) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn566.rows_innerRightABC HexagonRowColumn566.cols_assocABC) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_6_6_row_1_2_1 : (right0Middle5 6 6) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn566.rows_innerRightABC HexagonRowColumn566.cols_assocABC) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_6_6_row_1_3_0 : (right0Middle5 6 6) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn566.rows_innerRightABC HexagonRowColumn566.cols_assocABC) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_6_6_row_1_3_1 : (right0Middle5 6 6) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn566.rows_innerRightABC HexagonRowColumn566.cols_assocABC) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_6_6_checked : right0Middle5 6 6 = rowColumnMul HexagonRowColumn566.rows_innerRightABC HexagonRowColumn566.cols_assocABC := by
  funext r
  fin_cases r
  · exact right0Middle5_eq_case_6_6_row_0_0_0
  · exact right0Middle5_eq_case_6_6_row_0_0_1
  · exact right0Middle5_eq_case_6_6_row_0_1_0
  · exact right0Middle5_eq_case_6_6_row_0_1_1
  · exact right0Middle5_eq_case_6_6_row_0_2_0
  · exact right0Middle5_eq_case_6_6_row_0_2_1
  · exact right0Middle5_eq_case_6_6_row_0_3_0
  · exact right0Middle5_eq_case_6_6_row_0_3_1
  · exact right0Middle5_eq_case_6_6_row_1_0_0
  · exact right0Middle5_eq_case_6_6_row_1_0_1
  · exact right0Middle5_eq_case_6_6_row_1_1_0
  · exact right0Middle5_eq_case_6_6_row_1_1_1
  · exact right0Middle5_eq_case_6_6_row_1_2_0
  · exact right0Middle5_eq_case_6_6_row_1_2_1
  · exact right0Middle5_eq_case_6_6_row_1_3_0
  · exact right0Middle5_eq_case_6_6_row_1_3_1

set_option backward.isDefEq.respectTransparency false in
theorem right0Middle5_eq_case_6_6 : right0Middle5 6 6 = innerRightZ 5 6 6 * associatorZ 5 6 6 := by
  simpa only [HexagonAtoms566.assocABC_eq,
    HexagonAtoms566.outerABC_eq,
    HexagonAtoms566.assocBAC_eq,
    HexagonAtoms566.innerABC_eq,
    HexagonAtoms566.innerRightABC_eq,
    HexagonAtoms566.inverseACB_eq,
    HexagonAtoms566.innerACB_eq,
    HexagonAtoms566.assocBCA_eq,
    HexagonAtoms566.innerRightBAC_eq,
    HexagonAtoms566.assocCAB_eq,
    HexagonAtoms566.outerLeftABC_eq,
    HexagonRowColumn566.innerACB_alias,
    HexagonRowColumn566.assocCAB_alias,
    HexagonRowColumn566.product0_eq,
    HexagonRowColumn566.product1_eq,
    HexagonRowColumn566.product2_eq,
    HexagonRowColumn566.product3_eq,
    HexagonRowColumn566.product4_eq,
    HexagonRowColumn566.product5_eq,
    HexagonRowColumn566.product6_eq,
    HexagonRowColumn566.product7_eq] using right0Middle5_eq_case_6_6_checked

private theorem right1Middle5_eq_case_6_6_row_0_0_0 : (right1Middle5 6 6) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn566.rows_inverseACB HexagonRowColumn566.cols_right0) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_6_6_row_0_0_1 : (right1Middle5 6 6) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn566.rows_inverseACB HexagonRowColumn566.cols_right0) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_6_6_row_0_1_0 : (right1Middle5 6 6) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn566.rows_inverseACB HexagonRowColumn566.cols_right0) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_6_6_row_0_1_1 : (right1Middle5 6 6) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn566.rows_inverseACB HexagonRowColumn566.cols_right0) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_6_6_row_0_2_0 : (right1Middle5 6 6) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn566.rows_inverseACB HexagonRowColumn566.cols_right0) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_6_6_row_0_2_1 : (right1Middle5 6 6) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn566.rows_inverseACB HexagonRowColumn566.cols_right0) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_6_6_row_0_3_0 : (right1Middle5 6 6) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn566.rows_inverseACB HexagonRowColumn566.cols_right0) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_6_6_row_0_3_1 : (right1Middle5 6 6) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn566.rows_inverseACB HexagonRowColumn566.cols_right0) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_6_6_row_1_0_0 : (right1Middle5 6 6) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn566.rows_inverseACB HexagonRowColumn566.cols_right0) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_6_6_row_1_0_1 : (right1Middle5 6 6) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn566.rows_inverseACB HexagonRowColumn566.cols_right0) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_6_6_row_1_1_0 : (right1Middle5 6 6) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn566.rows_inverseACB HexagonRowColumn566.cols_right0) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_6_6_row_1_1_1 : (right1Middle5 6 6) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn566.rows_inverseACB HexagonRowColumn566.cols_right0) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_6_6_row_1_2_0 : (right1Middle5 6 6) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn566.rows_inverseACB HexagonRowColumn566.cols_right0) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_6_6_row_1_2_1 : (right1Middle5 6 6) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn566.rows_inverseACB HexagonRowColumn566.cols_right0) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_6_6_row_1_3_0 : (right1Middle5 6 6) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn566.rows_inverseACB HexagonRowColumn566.cols_right0) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_6_6_row_1_3_1 : (right1Middle5 6 6) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn566.rows_inverseACB HexagonRowColumn566.cols_right0) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_6_6_checked : right1Middle5 6 6 = rowColumnMul HexagonRowColumn566.rows_inverseACB HexagonRowColumn566.cols_right0 := by
  funext r
  fin_cases r
  · exact right1Middle5_eq_case_6_6_row_0_0_0
  · exact right1Middle5_eq_case_6_6_row_0_0_1
  · exact right1Middle5_eq_case_6_6_row_0_1_0
  · exact right1Middle5_eq_case_6_6_row_0_1_1
  · exact right1Middle5_eq_case_6_6_row_0_2_0
  · exact right1Middle5_eq_case_6_6_row_0_2_1
  · exact right1Middle5_eq_case_6_6_row_0_3_0
  · exact right1Middle5_eq_case_6_6_row_0_3_1
  · exact right1Middle5_eq_case_6_6_row_1_0_0
  · exact right1Middle5_eq_case_6_6_row_1_0_1
  · exact right1Middle5_eq_case_6_6_row_1_1_0
  · exact right1Middle5_eq_case_6_6_row_1_1_1
  · exact right1Middle5_eq_case_6_6_row_1_2_0
  · exact right1Middle5_eq_case_6_6_row_1_2_1
  · exact right1Middle5_eq_case_6_6_row_1_3_0
  · exact right1Middle5_eq_case_6_6_row_1_3_1

set_option backward.isDefEq.respectTransparency false in
theorem right1Middle5_eq_case_6_6 : right1Middle5 6 6 = associatorInverseZ 5 6 6 * right0Middle5 6 6 := by
  simpa only [HexagonAtoms566.assocABC_eq,
    HexagonAtoms566.outerABC_eq,
    HexagonAtoms566.assocBAC_eq,
    HexagonAtoms566.innerABC_eq,
    HexagonAtoms566.innerRightABC_eq,
    HexagonAtoms566.inverseACB_eq,
    HexagonAtoms566.innerACB_eq,
    HexagonAtoms566.assocBCA_eq,
    HexagonAtoms566.innerRightBAC_eq,
    HexagonAtoms566.assocCAB_eq,
    HexagonAtoms566.outerLeftABC_eq,
    HexagonRowColumn566.innerACB_alias,
    HexagonRowColumn566.assocCAB_alias,
    HexagonRowColumn566.product0_eq,
    HexagonRowColumn566.product1_eq,
    HexagonRowColumn566.product2_eq,
    HexagonRowColumn566.product3_eq,
    HexagonRowColumn566.product4_eq,
    HexagonRowColumn566.product5_eq,
    HexagonRowColumn566.product6_eq,
    HexagonRowColumn566.product7_eq] using right1Middle5_eq_case_6_6_checked

private theorem right2Middle5_eq_case_6_6_row_0_0_0 : (right2Middle5 6 6) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (right1Middle5 6 6) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_6_6_row_0_0_1 : (right2Middle5 6 6) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (right1Middle5 6 6) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_6_6_row_0_1_0 : (right2Middle5 6 6) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (right1Middle5 6 6) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_6_6_row_0_1_1 : (right2Middle5 6 6) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (right1Middle5 6 6) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_6_6_row_0_2_0 : (right2Middle5 6 6) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (right1Middle5 6 6) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_6_6_row_0_2_1 : (right2Middle5 6 6) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (right1Middle5 6 6) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_6_6_row_0_3_0 : (right2Middle5 6 6) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (right1Middle5 6 6) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_6_6_row_0_3_1 : (right2Middle5 6 6) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (right1Middle5 6 6) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_6_6_row_1_0_0 : (right2Middle5 6 6) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (right1Middle5 6 6) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_6_6_row_1_0_1 : (right2Middle5 6 6) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (right1Middle5 6 6) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_6_6_row_1_1_0 : (right2Middle5 6 6) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (right1Middle5 6 6) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_6_6_row_1_1_1 : (right2Middle5 6 6) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (right1Middle5 6 6) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_6_6_row_1_2_0 : (right2Middle5 6 6) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (right1Middle5 6 6) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_6_6_row_1_2_1 : (right2Middle5 6 6) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (right1Middle5 6 6) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_6_6_row_1_3_0 : (right2Middle5 6 6) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (right1Middle5 6 6) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_6_6_row_1_3_1 : (right2Middle5 6 6) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (right1Middle5 6 6) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_6_6_checked : right2Middle5 6 6 = right1Middle5 6 6 := by
  funext r
  fin_cases r
  · exact right2Middle5_eq_case_6_6_row_0_0_0
  · exact right2Middle5_eq_case_6_6_row_0_0_1
  · exact right2Middle5_eq_case_6_6_row_0_1_0
  · exact right2Middle5_eq_case_6_6_row_0_1_1
  · exact right2Middle5_eq_case_6_6_row_0_2_0
  · exact right2Middle5_eq_case_6_6_row_0_2_1
  · exact right2Middle5_eq_case_6_6_row_0_3_0
  · exact right2Middle5_eq_case_6_6_row_0_3_1
  · exact right2Middle5_eq_case_6_6_row_1_0_0
  · exact right2Middle5_eq_case_6_6_row_1_0_1
  · exact right2Middle5_eq_case_6_6_row_1_1_0
  · exact right2Middle5_eq_case_6_6_row_1_1_1
  · exact right2Middle5_eq_case_6_6_row_1_2_0
  · exact right2Middle5_eq_case_6_6_row_1_2_1
  · exact right2Middle5_eq_case_6_6_row_1_3_0
  · exact right2Middle5_eq_case_6_6_row_1_3_1

set_option backward.isDefEq.respectTransparency false in
theorem right2Middle5_eq_case_6_6 : right2Middle5 6 6 = innerLeftZ 5 6 6 * right1Middle5 6 6 := by
  simpa only [HexagonAtoms566.assocABC_eq,
    HexagonAtoms566.outerABC_eq,
    HexagonAtoms566.assocBAC_eq,
    HexagonAtoms566.innerABC_eq,
    HexagonAtoms566.innerRightABC_eq,
    HexagonAtoms566.inverseACB_eq,
    HexagonAtoms566.innerACB_eq,
    HexagonAtoms566.assocBCA_eq,
    HexagonAtoms566.innerRightBAC_eq,
    HexagonAtoms566.assocCAB_eq,
    HexagonAtoms566.outerLeftABC_eq,
    HexagonRowColumn566.innerACB_alias,
    HexagonRowColumn566.assocCAB_alias,
    HexagonRowColumn566.product0_eq,
    HexagonRowColumn566.product1_eq,
    HexagonRowColumn566.product2_eq,
    HexagonRowColumn566.product3_eq,
    HexagonRowColumn566.product4_eq,
    HexagonRowColumn566.product5_eq,
    HexagonRowColumn566.product6_eq,
    HexagonRowColumn566.product7_eq] using right2Middle5_eq_case_6_6_checked

private theorem leftFinal5_case_6_6_row_0_0_0 : (((-1 : ℤ) ^ (leftScaleBit 5 6 6).val * positiveScale (leftScaleExponent 5 6 6)) •
      (rowColumnMul HexagonRowColumn566.rows_assocBCA HexagonRowColumn566.cols_left0)) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 5 6 6) • (left1Middle5 6 6)) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal5_case_6_6_row_0_0_1 : (((-1 : ℤ) ^ (leftScaleBit 5 6 6).val * positiveScale (leftScaleExponent 5 6 6)) •
      (rowColumnMul HexagonRowColumn566.rows_assocBCA HexagonRowColumn566.cols_left0)) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 5 6 6) • (left1Middle5 6 6)) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal5_case_6_6_row_0_1_0 : (((-1 : ℤ) ^ (leftScaleBit 5 6 6).val * positiveScale (leftScaleExponent 5 6 6)) •
      (rowColumnMul HexagonRowColumn566.rows_assocBCA HexagonRowColumn566.cols_left0)) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 5 6 6) • (left1Middle5 6 6)) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal5_case_6_6_row_0_1_1 : (((-1 : ℤ) ^ (leftScaleBit 5 6 6).val * positiveScale (leftScaleExponent 5 6 6)) •
      (rowColumnMul HexagonRowColumn566.rows_assocBCA HexagonRowColumn566.cols_left0)) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 5 6 6) • (left1Middle5 6 6)) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal5_case_6_6_row_0_2_0 : (((-1 : ℤ) ^ (leftScaleBit 5 6 6).val * positiveScale (leftScaleExponent 5 6 6)) •
      (rowColumnMul HexagonRowColumn566.rows_assocBCA HexagonRowColumn566.cols_left0)) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 5 6 6) • (left1Middle5 6 6)) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal5_case_6_6_row_0_2_1 : (((-1 : ℤ) ^ (leftScaleBit 5 6 6).val * positiveScale (leftScaleExponent 5 6 6)) •
      (rowColumnMul HexagonRowColumn566.rows_assocBCA HexagonRowColumn566.cols_left0)) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 5 6 6) • (left1Middle5 6 6)) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal5_case_6_6_row_0_3_0 : (((-1 : ℤ) ^ (leftScaleBit 5 6 6).val * positiveScale (leftScaleExponent 5 6 6)) •
      (rowColumnMul HexagonRowColumn566.rows_assocBCA HexagonRowColumn566.cols_left0)) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 5 6 6) • (left1Middle5 6 6)) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal5_case_6_6_row_0_3_1 : (((-1 : ℤ) ^ (leftScaleBit 5 6 6).val * positiveScale (leftScaleExponent 5 6 6)) •
      (rowColumnMul HexagonRowColumn566.rows_assocBCA HexagonRowColumn566.cols_left0)) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 5 6 6) • (left1Middle5 6 6)) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal5_case_6_6_row_1_0_0 : (((-1 : ℤ) ^ (leftScaleBit 5 6 6).val * positiveScale (leftScaleExponent 5 6 6)) •
      (rowColumnMul HexagonRowColumn566.rows_assocBCA HexagonRowColumn566.cols_left0)) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 5 6 6) • (left1Middle5 6 6)) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal5_case_6_6_row_1_0_1 : (((-1 : ℤ) ^ (leftScaleBit 5 6 6).val * positiveScale (leftScaleExponent 5 6 6)) •
      (rowColumnMul HexagonRowColumn566.rows_assocBCA HexagonRowColumn566.cols_left0)) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 5 6 6) • (left1Middle5 6 6)) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal5_case_6_6_row_1_1_0 : (((-1 : ℤ) ^ (leftScaleBit 5 6 6).val * positiveScale (leftScaleExponent 5 6 6)) •
      (rowColumnMul HexagonRowColumn566.rows_assocBCA HexagonRowColumn566.cols_left0)) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 5 6 6) • (left1Middle5 6 6)) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal5_case_6_6_row_1_1_1 : (((-1 : ℤ) ^ (leftScaleBit 5 6 6).val * positiveScale (leftScaleExponent 5 6 6)) •
      (rowColumnMul HexagonRowColumn566.rows_assocBCA HexagonRowColumn566.cols_left0)) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 5 6 6) • (left1Middle5 6 6)) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal5_case_6_6_row_1_2_0 : (((-1 : ℤ) ^ (leftScaleBit 5 6 6).val * positiveScale (leftScaleExponent 5 6 6)) •
      (rowColumnMul HexagonRowColumn566.rows_assocBCA HexagonRowColumn566.cols_left0)) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 5 6 6) • (left1Middle5 6 6)) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal5_case_6_6_row_1_2_1 : (((-1 : ℤ) ^ (leftScaleBit 5 6 6).val * positiveScale (leftScaleExponent 5 6 6)) •
      (rowColumnMul HexagonRowColumn566.rows_assocBCA HexagonRowColumn566.cols_left0)) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 5 6 6) • (left1Middle5 6 6)) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal5_case_6_6_row_1_3_0 : (((-1 : ℤ) ^ (leftScaleBit 5 6 6).val * positiveScale (leftScaleExponent 5 6 6)) •
      (rowColumnMul HexagonRowColumn566.rows_assocBCA HexagonRowColumn566.cols_left0)) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 5 6 6) • (left1Middle5 6 6)) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal5_case_6_6_row_1_3_1 : (((-1 : ℤ) ^ (leftScaleBit 5 6 6).val * positiveScale (leftScaleExponent 5 6 6)) •
      (rowColumnMul HexagonRowColumn566.rows_assocBCA HexagonRowColumn566.cols_left0)) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 5 6 6) • (left1Middle5 6 6)) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal5_case_6_6_checked : ((-1 : ℤ) ^ (leftScaleBit 5 6 6).val * positiveScale (leftScaleExponent 5 6 6)) •
      (rowColumnMul HexagonRowColumn566.rows_assocBCA HexagonRowColumn566.cols_left0) = negativeScale (leftScaleExponent 5 6 6) • (left1Middle5 6 6) := by
  funext r
  fin_cases r
  · exact leftFinal5_case_6_6_row_0_0_0
  · exact leftFinal5_case_6_6_row_0_0_1
  · exact leftFinal5_case_6_6_row_0_1_0
  · exact leftFinal5_case_6_6_row_0_1_1
  · exact leftFinal5_case_6_6_row_0_2_0
  · exact leftFinal5_case_6_6_row_0_2_1
  · exact leftFinal5_case_6_6_row_0_3_0
  · exact leftFinal5_case_6_6_row_0_3_1
  · exact leftFinal5_case_6_6_row_1_0_0
  · exact leftFinal5_case_6_6_row_1_0_1
  · exact leftFinal5_case_6_6_row_1_1_0
  · exact leftFinal5_case_6_6_row_1_1_1
  · exact leftFinal5_case_6_6_row_1_2_0
  · exact leftFinal5_case_6_6_row_1_2_1
  · exact leftFinal5_case_6_6_row_1_3_0
  · exact leftFinal5_case_6_6_row_1_3_1

set_option backward.isDefEq.respectTransparency false in
theorem leftFinal5_case_6_6 : ((-1 : ℤ) ^ (leftScaleBit 5 6 6).val * positiveScale (leftScaleExponent 5 6 6)) •
      (associatorZ 6 6 5 * left0Middle5 6 6) = negativeScale (leftScaleExponent 5 6 6) • (innerRightZ 6 5 6 * left1Middle5 6 6) := by
  simpa only [HexagonAtoms566.assocABC_eq,
    HexagonAtoms566.outerABC_eq,
    HexagonAtoms566.assocBAC_eq,
    HexagonAtoms566.innerABC_eq,
    HexagonAtoms566.innerRightABC_eq,
    HexagonAtoms566.inverseACB_eq,
    HexagonAtoms566.innerACB_eq,
    HexagonAtoms566.assocBCA_eq,
    HexagonAtoms566.innerRightBAC_eq,
    HexagonAtoms566.assocCAB_eq,
    HexagonAtoms566.outerLeftABC_eq,
    HexagonRowColumn566.innerACB_alias,
    HexagonRowColumn566.assocCAB_alias,
    HexagonRowColumn566.product0_eq,
    HexagonRowColumn566.product1_eq,
    HexagonRowColumn566.product2_eq,
    HexagonRowColumn566.product3_eq,
    HexagonRowColumn566.product4_eq,
    HexagonRowColumn566.product5_eq,
    HexagonRowColumn566.product6_eq,
    HexagonRowColumn566.product7_eq] using leftFinal5_case_6_6_checked

private theorem rightFinal5_case_6_6_row_0_0_0 : (((-1 : ℤ) ^ (rightScaleBit 5 6 6).val * positiveScale (rightScaleExponent 5 6 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 6 6 : ℤ)) • HexagonAtoms566.outerLeftABC) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (negativeScale (rightScaleExponent 5 6 6) • (rowColumnMul HexagonRowColumn566.rows_assocBAC HexagonRowColumn566.cols_right2)) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal5_case_6_6_row_0_0_1 : (((-1 : ℤ) ^ (rightScaleBit 5 6 6).val * positiveScale (rightScaleExponent 5 6 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 6 6 : ℤ)) • HexagonAtoms566.outerLeftABC) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (negativeScale (rightScaleExponent 5 6 6) • (rowColumnMul HexagonRowColumn566.rows_assocBAC HexagonRowColumn566.cols_right2)) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal5_case_6_6_row_0_1_0 : (((-1 : ℤ) ^ (rightScaleBit 5 6 6).val * positiveScale (rightScaleExponent 5 6 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 6 6 : ℤ)) • HexagonAtoms566.outerLeftABC) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (negativeScale (rightScaleExponent 5 6 6) • (rowColumnMul HexagonRowColumn566.rows_assocBAC HexagonRowColumn566.cols_right2)) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal5_case_6_6_row_0_1_1 : (((-1 : ℤ) ^ (rightScaleBit 5 6 6).val * positiveScale (rightScaleExponent 5 6 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 6 6 : ℤ)) • HexagonAtoms566.outerLeftABC) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (negativeScale (rightScaleExponent 5 6 6) • (rowColumnMul HexagonRowColumn566.rows_assocBAC HexagonRowColumn566.cols_right2)) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal5_case_6_6_row_0_2_0 : (((-1 : ℤ) ^ (rightScaleBit 5 6 6).val * positiveScale (rightScaleExponent 5 6 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 6 6 : ℤ)) • HexagonAtoms566.outerLeftABC) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (negativeScale (rightScaleExponent 5 6 6) • (rowColumnMul HexagonRowColumn566.rows_assocBAC HexagonRowColumn566.cols_right2)) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal5_case_6_6_row_0_2_1 : (((-1 : ℤ) ^ (rightScaleBit 5 6 6).val * positiveScale (rightScaleExponent 5 6 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 6 6 : ℤ)) • HexagonAtoms566.outerLeftABC) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (negativeScale (rightScaleExponent 5 6 6) • (rowColumnMul HexagonRowColumn566.rows_assocBAC HexagonRowColumn566.cols_right2)) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal5_case_6_6_row_0_3_0 : (((-1 : ℤ) ^ (rightScaleBit 5 6 6).val * positiveScale (rightScaleExponent 5 6 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 6 6 : ℤ)) • HexagonAtoms566.outerLeftABC) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (negativeScale (rightScaleExponent 5 6 6) • (rowColumnMul HexagonRowColumn566.rows_assocBAC HexagonRowColumn566.cols_right2)) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal5_case_6_6_row_0_3_1 : (((-1 : ℤ) ^ (rightScaleBit 5 6 6).val * positiveScale (rightScaleExponent 5 6 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 6 6 : ℤ)) • HexagonAtoms566.outerLeftABC) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (negativeScale (rightScaleExponent 5 6 6) • (rowColumnMul HexagonRowColumn566.rows_assocBAC HexagonRowColumn566.cols_right2)) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal5_case_6_6_row_1_0_0 : (((-1 : ℤ) ^ (rightScaleBit 5 6 6).val * positiveScale (rightScaleExponent 5 6 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 6 6 : ℤ)) • HexagonAtoms566.outerLeftABC) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (negativeScale (rightScaleExponent 5 6 6) • (rowColumnMul HexagonRowColumn566.rows_assocBAC HexagonRowColumn566.cols_right2)) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal5_case_6_6_row_1_0_1 : (((-1 : ℤ) ^ (rightScaleBit 5 6 6).val * positiveScale (rightScaleExponent 5 6 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 6 6 : ℤ)) • HexagonAtoms566.outerLeftABC) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (negativeScale (rightScaleExponent 5 6 6) • (rowColumnMul HexagonRowColumn566.rows_assocBAC HexagonRowColumn566.cols_right2)) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal5_case_6_6_row_1_1_0 : (((-1 : ℤ) ^ (rightScaleBit 5 6 6).val * positiveScale (rightScaleExponent 5 6 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 6 6 : ℤ)) • HexagonAtoms566.outerLeftABC) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (negativeScale (rightScaleExponent 5 6 6) • (rowColumnMul HexagonRowColumn566.rows_assocBAC HexagonRowColumn566.cols_right2)) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal5_case_6_6_row_1_1_1 : (((-1 : ℤ) ^ (rightScaleBit 5 6 6).val * positiveScale (rightScaleExponent 5 6 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 6 6 : ℤ)) • HexagonAtoms566.outerLeftABC) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (negativeScale (rightScaleExponent 5 6 6) • (rowColumnMul HexagonRowColumn566.rows_assocBAC HexagonRowColumn566.cols_right2)) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal5_case_6_6_row_1_2_0 : (((-1 : ℤ) ^ (rightScaleBit 5 6 6).val * positiveScale (rightScaleExponent 5 6 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 6 6 : ℤ)) • HexagonAtoms566.outerLeftABC) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (negativeScale (rightScaleExponent 5 6 6) • (rowColumnMul HexagonRowColumn566.rows_assocBAC HexagonRowColumn566.cols_right2)) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal5_case_6_6_row_1_2_1 : (((-1 : ℤ) ^ (rightScaleBit 5 6 6).val * positiveScale (rightScaleExponent 5 6 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 6 6 : ℤ)) • HexagonAtoms566.outerLeftABC) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (negativeScale (rightScaleExponent 5 6 6) • (rowColumnMul HexagonRowColumn566.rows_assocBAC HexagonRowColumn566.cols_right2)) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal5_case_6_6_row_1_3_0 : (((-1 : ℤ) ^ (rightScaleBit 5 6 6).val * positiveScale (rightScaleExponent 5 6 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 6 6 : ℤ)) • HexagonAtoms566.outerLeftABC) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (negativeScale (rightScaleExponent 5 6 6) • (rowColumnMul HexagonRowColumn566.rows_assocBAC HexagonRowColumn566.cols_right2)) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal5_case_6_6_row_1_3_1 : (((-1 : ℤ) ^ (rightScaleBit 5 6 6).val * positiveScale (rightScaleExponent 5 6 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 6 6 : ℤ)) • HexagonAtoms566.outerLeftABC) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (negativeScale (rightScaleExponent 5 6 6) • (rowColumnMul HexagonRowColumn566.rows_assocBAC HexagonRowColumn566.cols_right2)) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal5_case_6_6_checked : ((-1 : ℤ) ^ (rightScaleBit 5 6 6).val * positiveScale (rightScaleExponent 5 6 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 6 6 : ℤ)) • HexagonAtoms566.outerLeftABC = negativeScale (rightScaleExponent 5 6 6) • (rowColumnMul HexagonRowColumn566.rows_assocBAC HexagonRowColumn566.cols_right2) := by
  funext r
  fin_cases r
  · exact rightFinal5_case_6_6_row_0_0_0
  · exact rightFinal5_case_6_6_row_0_0_1
  · exact rightFinal5_case_6_6_row_0_1_0
  · exact rightFinal5_case_6_6_row_0_1_1
  · exact rightFinal5_case_6_6_row_0_2_0
  · exact rightFinal5_case_6_6_row_0_2_1
  · exact rightFinal5_case_6_6_row_0_3_0
  · exact rightFinal5_case_6_6_row_0_3_1
  · exact rightFinal5_case_6_6_row_1_0_0
  · exact rightFinal5_case_6_6_row_1_0_1
  · exact rightFinal5_case_6_6_row_1_1_0
  · exact rightFinal5_case_6_6_row_1_1_1
  · exact rightFinal5_case_6_6_row_1_2_0
  · exact rightFinal5_case_6_6_row_1_2_1
  · exact rightFinal5_case_6_6_row_1_3_0
  · exact rightFinal5_case_6_6_row_1_3_1

set_option backward.isDefEq.respectTransparency false in
theorem rightFinal5_case_6_6 : ((-1 : ℤ) ^ (rightScaleBit 5 6 6).val * positiveScale (rightScaleExponent 5 6 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 6 6 : ℤ)) • outerLeftZ 5 6 6 = negativeScale (rightScaleExponent 5 6 6) • (associatorZ 6 5 6 * right2Middle5 6 6) := by
  simpa only [HexagonAtoms566.assocABC_eq,
    HexagonAtoms566.outerABC_eq,
    HexagonAtoms566.assocBAC_eq,
    HexagonAtoms566.innerABC_eq,
    HexagonAtoms566.innerRightABC_eq,
    HexagonAtoms566.inverseACB_eq,
    HexagonAtoms566.innerACB_eq,
    HexagonAtoms566.assocBCA_eq,
    HexagonAtoms566.innerRightBAC_eq,
    HexagonAtoms566.assocCAB_eq,
    HexagonAtoms566.outerLeftABC_eq,
    HexagonRowColumn566.innerACB_alias,
    HexagonRowColumn566.assocCAB_alias,
    HexagonRowColumn566.product0_eq,
    HexagonRowColumn566.product1_eq,
    HexagonRowColumn566.product2_eq,
    HexagonRowColumn566.product3_eq,
    HexagonRowColumn566.product4_eq,
    HexagonRowColumn566.product5_eq,
    HexagonRowColumn566.product6_eq,
    HexagonRowColumn566.product7_eq] using rightFinal5_case_6_6_checked

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonCases5
