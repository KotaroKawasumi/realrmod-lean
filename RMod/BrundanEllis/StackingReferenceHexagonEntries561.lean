import RMod.BrundanEllis.StackingReferenceHexagonMiddle5
import RMod.BrundanEllis.StackingReferenceSparseMatrixCheck
import RMod.BrundanEllis.StackingReferenceHexagonAtoms561
import RMod.BrundanEllis.StackingReferenceHexagonRowColumn561

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

private theorem left0Middle5_eq_case_6_1_row_0_0_0 : (left0Middle5 6 1) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn561.rows_outerABC HexagonRowColumn561.cols_assocABC) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_6_1_row_0_0_1 : (left0Middle5 6 1) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn561.rows_outerABC HexagonRowColumn561.cols_assocABC) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_6_1_row_0_0_2 : (left0Middle5 6 1) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn561.rows_outerABC HexagonRowColumn561.cols_assocABC) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_6_1_row_0_0_3 : (left0Middle5 6 1) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn561.rows_outerABC HexagonRowColumn561.cols_assocABC) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_6_1_row_0_1_0 : (left0Middle5 6 1) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn561.rows_outerABC HexagonRowColumn561.cols_assocABC) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_6_1_row_0_1_1 : (left0Middle5 6 1) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn561.rows_outerABC HexagonRowColumn561.cols_assocABC) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_6_1_row_0_1_2 : (left0Middle5 6 1) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn561.rows_outerABC HexagonRowColumn561.cols_assocABC) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_6_1_row_0_1_3 : (left0Middle5 6 1) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn561.rows_outerABC HexagonRowColumn561.cols_assocABC) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_6_1_row_1_0_0 : (left0Middle5 6 1) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn561.rows_outerABC HexagonRowColumn561.cols_assocABC) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_6_1_row_1_0_1 : (left0Middle5 6 1) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn561.rows_outerABC HexagonRowColumn561.cols_assocABC) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_6_1_row_1_0_2 : (left0Middle5 6 1) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn561.rows_outerABC HexagonRowColumn561.cols_assocABC) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_6_1_row_1_0_3 : (left0Middle5 6 1) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn561.rows_outerABC HexagonRowColumn561.cols_assocABC) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_6_1_row_1_1_0 : (left0Middle5 6 1) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn561.rows_outerABC HexagonRowColumn561.cols_assocABC) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_6_1_row_1_1_1 : (left0Middle5 6 1) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn561.rows_outerABC HexagonRowColumn561.cols_assocABC) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_6_1_row_1_1_2 : (left0Middle5 6 1) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn561.rows_outerABC HexagonRowColumn561.cols_assocABC) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_6_1_row_1_1_3 : (left0Middle5 6 1) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn561.rows_outerABC HexagonRowColumn561.cols_assocABC) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle5_eq_case_6_1_checked : left0Middle5 6 1 = rowColumnMul HexagonRowColumn561.rows_outerABC HexagonRowColumn561.cols_assocABC := by
  funext r
  fin_cases r
  · exact left0Middle5_eq_case_6_1_row_0_0_0
  · exact left0Middle5_eq_case_6_1_row_0_0_1
  · exact left0Middle5_eq_case_6_1_row_0_0_2
  · exact left0Middle5_eq_case_6_1_row_0_0_3
  · exact left0Middle5_eq_case_6_1_row_0_1_0
  · exact left0Middle5_eq_case_6_1_row_0_1_1
  · exact left0Middle5_eq_case_6_1_row_0_1_2
  · exact left0Middle5_eq_case_6_1_row_0_1_3
  · exact left0Middle5_eq_case_6_1_row_1_0_0
  · exact left0Middle5_eq_case_6_1_row_1_0_1
  · exact left0Middle5_eq_case_6_1_row_1_0_2
  · exact left0Middle5_eq_case_6_1_row_1_0_3
  · exact left0Middle5_eq_case_6_1_row_1_1_0
  · exact left0Middle5_eq_case_6_1_row_1_1_1
  · exact left0Middle5_eq_case_6_1_row_1_1_2
  · exact left0Middle5_eq_case_6_1_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem left0Middle5_eq_case_6_1 : left0Middle5 6 1 = outerRightZ 5 6 1 * associatorZ 5 6 1 := by
  simpa only [HexagonAtoms561.assocABC_eq,
    HexagonAtoms561.outerABC_eq,
    HexagonAtoms561.assocBAC_eq,
    HexagonAtoms561.innerABC_eq,
    HexagonAtoms561.innerRightABC_eq,
    HexagonAtoms561.inverseACB_eq,
    HexagonAtoms561.innerACB_eq,
    HexagonAtoms561.assocBCA_eq,
    HexagonAtoms561.innerRightBAC_eq,
    HexagonAtoms561.assocCAB_eq,
    HexagonAtoms561.outerLeftABC_eq,
    HexagonRowColumn561.product0_eq,
    HexagonRowColumn561.product1_eq,
    HexagonRowColumn561.product2_eq,
    HexagonRowColumn561.product3_eq,
    HexagonRowColumn561.product4_eq,
    HexagonRowColumn561.product5_eq,
    HexagonRowColumn561.product6_eq,
    HexagonRowColumn561.product7_eq] using left0Middle5_eq_case_6_1_checked

private theorem left1Middle5_eq_case_6_1_row_0_0_0 : (left1Middle5 6 1) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms561.assocBAC) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_6_1_row_0_0_1 : (left1Middle5 6 1) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms561.assocBAC) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_6_1_row_0_0_2 : (left1Middle5 6 1) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms561.assocBAC) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_6_1_row_0_0_3 : (left1Middle5 6 1) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms561.assocBAC) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_6_1_row_0_1_0 : (left1Middle5 6 1) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms561.assocBAC) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_6_1_row_0_1_1 : (left1Middle5 6 1) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms561.assocBAC) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_6_1_row_0_1_2 : (left1Middle5 6 1) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms561.assocBAC) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_6_1_row_0_1_3 : (left1Middle5 6 1) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms561.assocBAC) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_6_1_row_1_0_0 : (left1Middle5 6 1) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms561.assocBAC) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_6_1_row_1_0_1 : (left1Middle5 6 1) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms561.assocBAC) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_6_1_row_1_0_2 : (left1Middle5 6 1) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms561.assocBAC) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_6_1_row_1_0_3 : (left1Middle5 6 1) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms561.assocBAC) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_6_1_row_1_1_0 : (left1Middle5 6 1) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms561.assocBAC) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_6_1_row_1_1_1 : (left1Middle5 6 1) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms561.assocBAC) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_6_1_row_1_1_2 : (left1Middle5 6 1) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms561.assocBAC) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_6_1_row_1_1_3 : (left1Middle5 6 1) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms561.assocBAC) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle5_eq_case_6_1_checked : left1Middle5 6 1 = HexagonAtoms561.assocBAC := by
  funext r
  fin_cases r
  · exact left1Middle5_eq_case_6_1_row_0_0_0
  · exact left1Middle5_eq_case_6_1_row_0_0_1
  · exact left1Middle5_eq_case_6_1_row_0_0_2
  · exact left1Middle5_eq_case_6_1_row_0_0_3
  · exact left1Middle5_eq_case_6_1_row_0_1_0
  · exact left1Middle5_eq_case_6_1_row_0_1_1
  · exact left1Middle5_eq_case_6_1_row_0_1_2
  · exact left1Middle5_eq_case_6_1_row_0_1_3
  · exact left1Middle5_eq_case_6_1_row_1_0_0
  · exact left1Middle5_eq_case_6_1_row_1_0_1
  · exact left1Middle5_eq_case_6_1_row_1_0_2
  · exact left1Middle5_eq_case_6_1_row_1_0_3
  · exact left1Middle5_eq_case_6_1_row_1_1_0
  · exact left1Middle5_eq_case_6_1_row_1_1_1
  · exact left1Middle5_eq_case_6_1_row_1_1_2
  · exact left1Middle5_eq_case_6_1_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem left1Middle5_eq_case_6_1 : left1Middle5 6 1 = associatorZ 6 5 1 * innerLeftZ 5 6 1 := by
  simpa only [HexagonAtoms561.assocABC_eq,
    HexagonAtoms561.outerABC_eq,
    HexagonAtoms561.assocBAC_eq,
    HexagonAtoms561.innerABC_eq,
    HexagonAtoms561.innerRightABC_eq,
    HexagonAtoms561.inverseACB_eq,
    HexagonAtoms561.innerACB_eq,
    HexagonAtoms561.assocBCA_eq,
    HexagonAtoms561.innerRightBAC_eq,
    HexagonAtoms561.assocCAB_eq,
    HexagonAtoms561.outerLeftABC_eq,
    HexagonRowColumn561.product0_eq,
    HexagonRowColumn561.product1_eq,
    HexagonRowColumn561.product2_eq,
    HexagonRowColumn561.product3_eq,
    HexagonRowColumn561.product4_eq,
    HexagonRowColumn561.product5_eq,
    HexagonRowColumn561.product6_eq,
    HexagonRowColumn561.product7_eq] using left1Middle5_eq_case_6_1_checked

private theorem right0Middle5_eq_case_6_1_row_0_0_0 : (right0Middle5 6 1) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms561.assocABC) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_6_1_row_0_0_1 : (right0Middle5 6 1) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms561.assocABC) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_6_1_row_0_0_2 : (right0Middle5 6 1) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms561.assocABC) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_6_1_row_0_0_3 : (right0Middle5 6 1) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms561.assocABC) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_6_1_row_0_1_0 : (right0Middle5 6 1) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms561.assocABC) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_6_1_row_0_1_1 : (right0Middle5 6 1) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms561.assocABC) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_6_1_row_0_1_2 : (right0Middle5 6 1) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms561.assocABC) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_6_1_row_0_1_3 : (right0Middle5 6 1) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms561.assocABC) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_6_1_row_1_0_0 : (right0Middle5 6 1) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms561.assocABC) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_6_1_row_1_0_1 : (right0Middle5 6 1) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms561.assocABC) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_6_1_row_1_0_2 : (right0Middle5 6 1) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms561.assocABC) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_6_1_row_1_0_3 : (right0Middle5 6 1) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms561.assocABC) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_6_1_row_1_1_0 : (right0Middle5 6 1) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms561.assocABC) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_6_1_row_1_1_1 : (right0Middle5 6 1) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms561.assocABC) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_6_1_row_1_1_2 : (right0Middle5 6 1) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms561.assocABC) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_6_1_row_1_1_3 : (right0Middle5 6 1) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms561.assocABC) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle5_eq_case_6_1_checked : right0Middle5 6 1 = HexagonAtoms561.assocABC := by
  funext r
  fin_cases r
  · exact right0Middle5_eq_case_6_1_row_0_0_0
  · exact right0Middle5_eq_case_6_1_row_0_0_1
  · exact right0Middle5_eq_case_6_1_row_0_0_2
  · exact right0Middle5_eq_case_6_1_row_0_0_3
  · exact right0Middle5_eq_case_6_1_row_0_1_0
  · exact right0Middle5_eq_case_6_1_row_0_1_1
  · exact right0Middle5_eq_case_6_1_row_0_1_2
  · exact right0Middle5_eq_case_6_1_row_0_1_3
  · exact right0Middle5_eq_case_6_1_row_1_0_0
  · exact right0Middle5_eq_case_6_1_row_1_0_1
  · exact right0Middle5_eq_case_6_1_row_1_0_2
  · exact right0Middle5_eq_case_6_1_row_1_0_3
  · exact right0Middle5_eq_case_6_1_row_1_1_0
  · exact right0Middle5_eq_case_6_1_row_1_1_1
  · exact right0Middle5_eq_case_6_1_row_1_1_2
  · exact right0Middle5_eq_case_6_1_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem right0Middle5_eq_case_6_1 : right0Middle5 6 1 = innerRightZ 5 6 1 * associatorZ 5 6 1 := by
  simpa only [HexagonAtoms561.assocABC_eq,
    HexagonAtoms561.outerABC_eq,
    HexagonAtoms561.assocBAC_eq,
    HexagonAtoms561.innerABC_eq,
    HexagonAtoms561.innerRightABC_eq,
    HexagonAtoms561.inverseACB_eq,
    HexagonAtoms561.innerACB_eq,
    HexagonAtoms561.assocBCA_eq,
    HexagonAtoms561.innerRightBAC_eq,
    HexagonAtoms561.assocCAB_eq,
    HexagonAtoms561.outerLeftABC_eq,
    HexagonRowColumn561.product0_eq,
    HexagonRowColumn561.product1_eq,
    HexagonRowColumn561.product2_eq,
    HexagonRowColumn561.product3_eq,
    HexagonRowColumn561.product4_eq,
    HexagonRowColumn561.product5_eq,
    HexagonRowColumn561.product6_eq,
    HexagonRowColumn561.product7_eq] using right0Middle5_eq_case_6_1_checked

private theorem right1Middle5_eq_case_6_1_row_0_0_0 : (right1Middle5 6 1) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn561.rows_inverseACB HexagonRowColumn561.cols_right0) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_6_1_row_0_0_1 : (right1Middle5 6 1) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn561.rows_inverseACB HexagonRowColumn561.cols_right0) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_6_1_row_0_0_2 : (right1Middle5 6 1) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn561.rows_inverseACB HexagonRowColumn561.cols_right0) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_6_1_row_0_0_3 : (right1Middle5 6 1) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn561.rows_inverseACB HexagonRowColumn561.cols_right0) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_6_1_row_0_1_0 : (right1Middle5 6 1) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn561.rows_inverseACB HexagonRowColumn561.cols_right0) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_6_1_row_0_1_1 : (right1Middle5 6 1) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn561.rows_inverseACB HexagonRowColumn561.cols_right0) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_6_1_row_0_1_2 : (right1Middle5 6 1) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn561.rows_inverseACB HexagonRowColumn561.cols_right0) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_6_1_row_0_1_3 : (right1Middle5 6 1) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn561.rows_inverseACB HexagonRowColumn561.cols_right0) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_6_1_row_1_0_0 : (right1Middle5 6 1) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn561.rows_inverseACB HexagonRowColumn561.cols_right0) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_6_1_row_1_0_1 : (right1Middle5 6 1) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn561.rows_inverseACB HexagonRowColumn561.cols_right0) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_6_1_row_1_0_2 : (right1Middle5 6 1) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn561.rows_inverseACB HexagonRowColumn561.cols_right0) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_6_1_row_1_0_3 : (right1Middle5 6 1) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn561.rows_inverseACB HexagonRowColumn561.cols_right0) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_6_1_row_1_1_0 : (right1Middle5 6 1) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn561.rows_inverseACB HexagonRowColumn561.cols_right0) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_6_1_row_1_1_1 : (right1Middle5 6 1) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn561.rows_inverseACB HexagonRowColumn561.cols_right0) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_6_1_row_1_1_2 : (right1Middle5 6 1) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn561.rows_inverseACB HexagonRowColumn561.cols_right0) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_6_1_row_1_1_3 : (right1Middle5 6 1) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn561.rows_inverseACB HexagonRowColumn561.cols_right0) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle5_eq_case_6_1_checked : right1Middle5 6 1 = rowColumnMul HexagonRowColumn561.rows_inverseACB HexagonRowColumn561.cols_right0 := by
  funext r
  fin_cases r
  · exact right1Middle5_eq_case_6_1_row_0_0_0
  · exact right1Middle5_eq_case_6_1_row_0_0_1
  · exact right1Middle5_eq_case_6_1_row_0_0_2
  · exact right1Middle5_eq_case_6_1_row_0_0_3
  · exact right1Middle5_eq_case_6_1_row_0_1_0
  · exact right1Middle5_eq_case_6_1_row_0_1_1
  · exact right1Middle5_eq_case_6_1_row_0_1_2
  · exact right1Middle5_eq_case_6_1_row_0_1_3
  · exact right1Middle5_eq_case_6_1_row_1_0_0
  · exact right1Middle5_eq_case_6_1_row_1_0_1
  · exact right1Middle5_eq_case_6_1_row_1_0_2
  · exact right1Middle5_eq_case_6_1_row_1_0_3
  · exact right1Middle5_eq_case_6_1_row_1_1_0
  · exact right1Middle5_eq_case_6_1_row_1_1_1
  · exact right1Middle5_eq_case_6_1_row_1_1_2
  · exact right1Middle5_eq_case_6_1_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem right1Middle5_eq_case_6_1 : right1Middle5 6 1 = associatorInverseZ 5 1 6 * right0Middle5 6 1 := by
  simpa only [HexagonAtoms561.assocABC_eq,
    HexagonAtoms561.outerABC_eq,
    HexagonAtoms561.assocBAC_eq,
    HexagonAtoms561.innerABC_eq,
    HexagonAtoms561.innerRightABC_eq,
    HexagonAtoms561.inverseACB_eq,
    HexagonAtoms561.innerACB_eq,
    HexagonAtoms561.assocBCA_eq,
    HexagonAtoms561.innerRightBAC_eq,
    HexagonAtoms561.assocCAB_eq,
    HexagonAtoms561.outerLeftABC_eq,
    HexagonRowColumn561.product0_eq,
    HexagonRowColumn561.product1_eq,
    HexagonRowColumn561.product2_eq,
    HexagonRowColumn561.product3_eq,
    HexagonRowColumn561.product4_eq,
    HexagonRowColumn561.product5_eq,
    HexagonRowColumn561.product6_eq,
    HexagonRowColumn561.product7_eq] using right1Middle5_eq_case_6_1_checked

private theorem right2Middle5_eq_case_6_1_row_0_0_0 : (right2Middle5 6 1) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (right1Middle5 6 1) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_6_1_row_0_0_1 : (right2Middle5 6 1) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (right1Middle5 6 1) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_6_1_row_0_0_2 : (right2Middle5 6 1) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (right1Middle5 6 1) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_6_1_row_0_0_3 : (right2Middle5 6 1) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (right1Middle5 6 1) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_6_1_row_0_1_0 : (right2Middle5 6 1) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (right1Middle5 6 1) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_6_1_row_0_1_1 : (right2Middle5 6 1) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (right1Middle5 6 1) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_6_1_row_0_1_2 : (right2Middle5 6 1) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (right1Middle5 6 1) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_6_1_row_0_1_3 : (right2Middle5 6 1) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (right1Middle5 6 1) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_6_1_row_1_0_0 : (right2Middle5 6 1) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (right1Middle5 6 1) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_6_1_row_1_0_1 : (right2Middle5 6 1) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (right1Middle5 6 1) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_6_1_row_1_0_2 : (right2Middle5 6 1) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (right1Middle5 6 1) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_6_1_row_1_0_3 : (right2Middle5 6 1) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (right1Middle5 6 1) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_6_1_row_1_1_0 : (right2Middle5 6 1) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (right1Middle5 6 1) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_6_1_row_1_1_1 : (right2Middle5 6 1) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (right1Middle5 6 1) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_6_1_row_1_1_2 : (right2Middle5 6 1) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (right1Middle5 6 1) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_6_1_row_1_1_3 : (right2Middle5 6 1) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (right1Middle5 6 1) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle5_eq_case_6_1_checked : right2Middle5 6 1 = right1Middle5 6 1 := by
  funext r
  fin_cases r
  · exact right2Middle5_eq_case_6_1_row_0_0_0
  · exact right2Middle5_eq_case_6_1_row_0_0_1
  · exact right2Middle5_eq_case_6_1_row_0_0_2
  · exact right2Middle5_eq_case_6_1_row_0_0_3
  · exact right2Middle5_eq_case_6_1_row_0_1_0
  · exact right2Middle5_eq_case_6_1_row_0_1_1
  · exact right2Middle5_eq_case_6_1_row_0_1_2
  · exact right2Middle5_eq_case_6_1_row_0_1_3
  · exact right2Middle5_eq_case_6_1_row_1_0_0
  · exact right2Middle5_eq_case_6_1_row_1_0_1
  · exact right2Middle5_eq_case_6_1_row_1_0_2
  · exact right2Middle5_eq_case_6_1_row_1_0_3
  · exact right2Middle5_eq_case_6_1_row_1_1_0
  · exact right2Middle5_eq_case_6_1_row_1_1_1
  · exact right2Middle5_eq_case_6_1_row_1_1_2
  · exact right2Middle5_eq_case_6_1_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem right2Middle5_eq_case_6_1 : right2Middle5 6 1 = innerLeftZ 5 1 6 * right1Middle5 6 1 := by
  simpa only [HexagonAtoms561.assocABC_eq,
    HexagonAtoms561.outerABC_eq,
    HexagonAtoms561.assocBAC_eq,
    HexagonAtoms561.innerABC_eq,
    HexagonAtoms561.innerRightABC_eq,
    HexagonAtoms561.inverseACB_eq,
    HexagonAtoms561.innerACB_eq,
    HexagonAtoms561.assocBCA_eq,
    HexagonAtoms561.innerRightBAC_eq,
    HexagonAtoms561.assocCAB_eq,
    HexagonAtoms561.outerLeftABC_eq,
    HexagonRowColumn561.product0_eq,
    HexagonRowColumn561.product1_eq,
    HexagonRowColumn561.product2_eq,
    HexagonRowColumn561.product3_eq,
    HexagonRowColumn561.product4_eq,
    HexagonRowColumn561.product5_eq,
    HexagonRowColumn561.product6_eq,
    HexagonRowColumn561.product7_eq] using right2Middle5_eq_case_6_1_checked

private theorem leftFinal5_case_6_1_row_0_0_0 : (((-1 : ℤ) ^ (leftScaleBit 5 6 1).val * positiveScale (leftScaleExponent 5 6 1)) •
      (rowColumnMul HexagonRowColumn561.rows_assocBCA HexagonRowColumn561.cols_left0)) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 5 6 1) • (left1Middle5 6 1)) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_6_1_row_0_0_1 : (((-1 : ℤ) ^ (leftScaleBit 5 6 1).val * positiveScale (leftScaleExponent 5 6 1)) •
      (rowColumnMul HexagonRowColumn561.rows_assocBCA HexagonRowColumn561.cols_left0)) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 5 6 1) • (left1Middle5 6 1)) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_6_1_row_0_0_2 : (((-1 : ℤ) ^ (leftScaleBit 5 6 1).val * positiveScale (leftScaleExponent 5 6 1)) •
      (rowColumnMul HexagonRowColumn561.rows_assocBCA HexagonRowColumn561.cols_left0)) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 5 6 1) • (left1Middle5 6 1)) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_6_1_row_0_0_3 : (((-1 : ℤ) ^ (leftScaleBit 5 6 1).val * positiveScale (leftScaleExponent 5 6 1)) •
      (rowColumnMul HexagonRowColumn561.rows_assocBCA HexagonRowColumn561.cols_left0)) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 5 6 1) • (left1Middle5 6 1)) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_6_1_row_0_1_0 : (((-1 : ℤ) ^ (leftScaleBit 5 6 1).val * positiveScale (leftScaleExponent 5 6 1)) •
      (rowColumnMul HexagonRowColumn561.rows_assocBCA HexagonRowColumn561.cols_left0)) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 5 6 1) • (left1Middle5 6 1)) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_6_1_row_0_1_1 : (((-1 : ℤ) ^ (leftScaleBit 5 6 1).val * positiveScale (leftScaleExponent 5 6 1)) •
      (rowColumnMul HexagonRowColumn561.rows_assocBCA HexagonRowColumn561.cols_left0)) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 5 6 1) • (left1Middle5 6 1)) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_6_1_row_0_1_2 : (((-1 : ℤ) ^ (leftScaleBit 5 6 1).val * positiveScale (leftScaleExponent 5 6 1)) •
      (rowColumnMul HexagonRowColumn561.rows_assocBCA HexagonRowColumn561.cols_left0)) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 5 6 1) • (left1Middle5 6 1)) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_6_1_row_0_1_3 : (((-1 : ℤ) ^ (leftScaleBit 5 6 1).val * positiveScale (leftScaleExponent 5 6 1)) •
      (rowColumnMul HexagonRowColumn561.rows_assocBCA HexagonRowColumn561.cols_left0)) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 5 6 1) • (left1Middle5 6 1)) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_6_1_row_1_0_0 : (((-1 : ℤ) ^ (leftScaleBit 5 6 1).val * positiveScale (leftScaleExponent 5 6 1)) •
      (rowColumnMul HexagonRowColumn561.rows_assocBCA HexagonRowColumn561.cols_left0)) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 5 6 1) • (left1Middle5 6 1)) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_6_1_row_1_0_1 : (((-1 : ℤ) ^ (leftScaleBit 5 6 1).val * positiveScale (leftScaleExponent 5 6 1)) •
      (rowColumnMul HexagonRowColumn561.rows_assocBCA HexagonRowColumn561.cols_left0)) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 5 6 1) • (left1Middle5 6 1)) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_6_1_row_1_0_2 : (((-1 : ℤ) ^ (leftScaleBit 5 6 1).val * positiveScale (leftScaleExponent 5 6 1)) •
      (rowColumnMul HexagonRowColumn561.rows_assocBCA HexagonRowColumn561.cols_left0)) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 5 6 1) • (left1Middle5 6 1)) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_6_1_row_1_0_3 : (((-1 : ℤ) ^ (leftScaleBit 5 6 1).val * positiveScale (leftScaleExponent 5 6 1)) •
      (rowColumnMul HexagonRowColumn561.rows_assocBCA HexagonRowColumn561.cols_left0)) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 5 6 1) • (left1Middle5 6 1)) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_6_1_row_1_1_0 : (((-1 : ℤ) ^ (leftScaleBit 5 6 1).val * positiveScale (leftScaleExponent 5 6 1)) •
      (rowColumnMul HexagonRowColumn561.rows_assocBCA HexagonRowColumn561.cols_left0)) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 5 6 1) • (left1Middle5 6 1)) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_6_1_row_1_1_1 : (((-1 : ℤ) ^ (leftScaleBit 5 6 1).val * positiveScale (leftScaleExponent 5 6 1)) •
      (rowColumnMul HexagonRowColumn561.rows_assocBCA HexagonRowColumn561.cols_left0)) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 5 6 1) • (left1Middle5 6 1)) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_6_1_row_1_1_2 : (((-1 : ℤ) ^ (leftScaleBit 5 6 1).val * positiveScale (leftScaleExponent 5 6 1)) •
      (rowColumnMul HexagonRowColumn561.rows_assocBCA HexagonRowColumn561.cols_left0)) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 5 6 1) • (left1Middle5 6 1)) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_6_1_row_1_1_3 : (((-1 : ℤ) ^ (leftScaleBit 5 6 1).val * positiveScale (leftScaleExponent 5 6 1)) •
      (rowColumnMul HexagonRowColumn561.rows_assocBCA HexagonRowColumn561.cols_left0)) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 5 6 1) • (left1Middle5 6 1)) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal5_case_6_1_checked : ((-1 : ℤ) ^ (leftScaleBit 5 6 1).val * positiveScale (leftScaleExponent 5 6 1)) •
      (rowColumnMul HexagonRowColumn561.rows_assocBCA HexagonRowColumn561.cols_left0) = negativeScale (leftScaleExponent 5 6 1) • (left1Middle5 6 1) := by
  funext r
  fin_cases r
  · exact leftFinal5_case_6_1_row_0_0_0
  · exact leftFinal5_case_6_1_row_0_0_1
  · exact leftFinal5_case_6_1_row_0_0_2
  · exact leftFinal5_case_6_1_row_0_0_3
  · exact leftFinal5_case_6_1_row_0_1_0
  · exact leftFinal5_case_6_1_row_0_1_1
  · exact leftFinal5_case_6_1_row_0_1_2
  · exact leftFinal5_case_6_1_row_0_1_3
  · exact leftFinal5_case_6_1_row_1_0_0
  · exact leftFinal5_case_6_1_row_1_0_1
  · exact leftFinal5_case_6_1_row_1_0_2
  · exact leftFinal5_case_6_1_row_1_0_3
  · exact leftFinal5_case_6_1_row_1_1_0
  · exact leftFinal5_case_6_1_row_1_1_1
  · exact leftFinal5_case_6_1_row_1_1_2
  · exact leftFinal5_case_6_1_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem leftFinal5_case_6_1 : ((-1 : ℤ) ^ (leftScaleBit 5 6 1).val * positiveScale (leftScaleExponent 5 6 1)) •
      (associatorZ 6 1 5 * left0Middle5 6 1) = negativeScale (leftScaleExponent 5 6 1) • (innerRightZ 6 5 1 * left1Middle5 6 1) := by
  simpa only [HexagonAtoms561.assocABC_eq,
    HexagonAtoms561.outerABC_eq,
    HexagonAtoms561.assocBAC_eq,
    HexagonAtoms561.innerABC_eq,
    HexagonAtoms561.innerRightABC_eq,
    HexagonAtoms561.inverseACB_eq,
    HexagonAtoms561.innerACB_eq,
    HexagonAtoms561.assocBCA_eq,
    HexagonAtoms561.innerRightBAC_eq,
    HexagonAtoms561.assocCAB_eq,
    HexagonAtoms561.outerLeftABC_eq,
    HexagonRowColumn561.product0_eq,
    HexagonRowColumn561.product1_eq,
    HexagonRowColumn561.product2_eq,
    HexagonRowColumn561.product3_eq,
    HexagonRowColumn561.product4_eq,
    HexagonRowColumn561.product5_eq,
    HexagonRowColumn561.product6_eq,
    HexagonRowColumn561.product7_eq] using leftFinal5_case_6_1_checked

private theorem rightFinal5_case_6_1_row_0_0_0 : (((-1 : ℤ) ^ (rightScaleBit 5 6 1).val * positiveScale (rightScaleExponent 5 6 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 1 6 : ℤ)) • HexagonAtoms561.outerLeftABC) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 5 6 1) • (rowColumnMul HexagonRowColumn561.rows_assocCAB HexagonRowColumn561.cols_right2)) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_6_1_row_0_0_1 : (((-1 : ℤ) ^ (rightScaleBit 5 6 1).val * positiveScale (rightScaleExponent 5 6 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 1 6 : ℤ)) • HexagonAtoms561.outerLeftABC) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 5 6 1) • (rowColumnMul HexagonRowColumn561.rows_assocCAB HexagonRowColumn561.cols_right2)) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_6_1_row_0_0_2 : (((-1 : ℤ) ^ (rightScaleBit 5 6 1).val * positiveScale (rightScaleExponent 5 6 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 1 6 : ℤ)) • HexagonAtoms561.outerLeftABC) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 5 6 1) • (rowColumnMul HexagonRowColumn561.rows_assocCAB HexagonRowColumn561.cols_right2)) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_6_1_row_0_0_3 : (((-1 : ℤ) ^ (rightScaleBit 5 6 1).val * positiveScale (rightScaleExponent 5 6 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 1 6 : ℤ)) • HexagonAtoms561.outerLeftABC) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 5 6 1) • (rowColumnMul HexagonRowColumn561.rows_assocCAB HexagonRowColumn561.cols_right2)) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_6_1_row_0_1_0 : (((-1 : ℤ) ^ (rightScaleBit 5 6 1).val * positiveScale (rightScaleExponent 5 6 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 1 6 : ℤ)) • HexagonAtoms561.outerLeftABC) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 5 6 1) • (rowColumnMul HexagonRowColumn561.rows_assocCAB HexagonRowColumn561.cols_right2)) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_6_1_row_0_1_1 : (((-1 : ℤ) ^ (rightScaleBit 5 6 1).val * positiveScale (rightScaleExponent 5 6 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 1 6 : ℤ)) • HexagonAtoms561.outerLeftABC) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 5 6 1) • (rowColumnMul HexagonRowColumn561.rows_assocCAB HexagonRowColumn561.cols_right2)) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_6_1_row_0_1_2 : (((-1 : ℤ) ^ (rightScaleBit 5 6 1).val * positiveScale (rightScaleExponent 5 6 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 1 6 : ℤ)) • HexagonAtoms561.outerLeftABC) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 5 6 1) • (rowColumnMul HexagonRowColumn561.rows_assocCAB HexagonRowColumn561.cols_right2)) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_6_1_row_0_1_3 : (((-1 : ℤ) ^ (rightScaleBit 5 6 1).val * positiveScale (rightScaleExponent 5 6 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 1 6 : ℤ)) • HexagonAtoms561.outerLeftABC) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 5 6 1) • (rowColumnMul HexagonRowColumn561.rows_assocCAB HexagonRowColumn561.cols_right2)) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_6_1_row_1_0_0 : (((-1 : ℤ) ^ (rightScaleBit 5 6 1).val * positiveScale (rightScaleExponent 5 6 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 1 6 : ℤ)) • HexagonAtoms561.outerLeftABC) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 5 6 1) • (rowColumnMul HexagonRowColumn561.rows_assocCAB HexagonRowColumn561.cols_right2)) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_6_1_row_1_0_1 : (((-1 : ℤ) ^ (rightScaleBit 5 6 1).val * positiveScale (rightScaleExponent 5 6 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 1 6 : ℤ)) • HexagonAtoms561.outerLeftABC) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 5 6 1) • (rowColumnMul HexagonRowColumn561.rows_assocCAB HexagonRowColumn561.cols_right2)) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_6_1_row_1_0_2 : (((-1 : ℤ) ^ (rightScaleBit 5 6 1).val * positiveScale (rightScaleExponent 5 6 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 1 6 : ℤ)) • HexagonAtoms561.outerLeftABC) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 5 6 1) • (rowColumnMul HexagonRowColumn561.rows_assocCAB HexagonRowColumn561.cols_right2)) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_6_1_row_1_0_3 : (((-1 : ℤ) ^ (rightScaleBit 5 6 1).val * positiveScale (rightScaleExponent 5 6 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 1 6 : ℤ)) • HexagonAtoms561.outerLeftABC) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 5 6 1) • (rowColumnMul HexagonRowColumn561.rows_assocCAB HexagonRowColumn561.cols_right2)) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_6_1_row_1_1_0 : (((-1 : ℤ) ^ (rightScaleBit 5 6 1).val * positiveScale (rightScaleExponent 5 6 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 1 6 : ℤ)) • HexagonAtoms561.outerLeftABC) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 5 6 1) • (rowColumnMul HexagonRowColumn561.rows_assocCAB HexagonRowColumn561.cols_right2)) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_6_1_row_1_1_1 : (((-1 : ℤ) ^ (rightScaleBit 5 6 1).val * positiveScale (rightScaleExponent 5 6 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 1 6 : ℤ)) • HexagonAtoms561.outerLeftABC) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 5 6 1) • (rowColumnMul HexagonRowColumn561.rows_assocCAB HexagonRowColumn561.cols_right2)) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_6_1_row_1_1_2 : (((-1 : ℤ) ^ (rightScaleBit 5 6 1).val * positiveScale (rightScaleExponent 5 6 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 1 6 : ℤ)) • HexagonAtoms561.outerLeftABC) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 5 6 1) • (rowColumnMul HexagonRowColumn561.rows_assocCAB HexagonRowColumn561.cols_right2)) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_6_1_row_1_1_3 : (((-1 : ℤ) ^ (rightScaleBit 5 6 1).val * positiveScale (rightScaleExponent 5 6 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 1 6 : ℤ)) • HexagonAtoms561.outerLeftABC) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 5 6 1) • (rowColumnMul HexagonRowColumn561.rows_assocCAB HexagonRowColumn561.cols_right2)) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal5_case_6_1_checked : ((-1 : ℤ) ^ (rightScaleBit 5 6 1).val * positiveScale (rightScaleExponent 5 6 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 1 6 : ℤ)) • HexagonAtoms561.outerLeftABC = negativeScale (rightScaleExponent 5 6 1) • (rowColumnMul HexagonRowColumn561.rows_assocCAB HexagonRowColumn561.cols_right2) := by
  funext r
  fin_cases r
  · exact rightFinal5_case_6_1_row_0_0_0
  · exact rightFinal5_case_6_1_row_0_0_1
  · exact rightFinal5_case_6_1_row_0_0_2
  · exact rightFinal5_case_6_1_row_0_0_3
  · exact rightFinal5_case_6_1_row_0_1_0
  · exact rightFinal5_case_6_1_row_0_1_1
  · exact rightFinal5_case_6_1_row_0_1_2
  · exact rightFinal5_case_6_1_row_0_1_3
  · exact rightFinal5_case_6_1_row_1_0_0
  · exact rightFinal5_case_6_1_row_1_0_1
  · exact rightFinal5_case_6_1_row_1_0_2
  · exact rightFinal5_case_6_1_row_1_0_3
  · exact rightFinal5_case_6_1_row_1_1_0
  · exact rightFinal5_case_6_1_row_1_1_1
  · exact rightFinal5_case_6_1_row_1_1_2
  · exact rightFinal5_case_6_1_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem rightFinal5_case_6_1 : ((-1 : ℤ) ^ (rightScaleBit 5 6 1).val * positiveScale (rightScaleExponent 5 6 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 1 6 : ℤ)) • outerLeftZ 5 6 1 = negativeScale (rightScaleExponent 5 6 1) • (associatorZ 1 5 6 * right2Middle5 6 1) := by
  simpa only [HexagonAtoms561.assocABC_eq,
    HexagonAtoms561.outerABC_eq,
    HexagonAtoms561.assocBAC_eq,
    HexagonAtoms561.innerABC_eq,
    HexagonAtoms561.innerRightABC_eq,
    HexagonAtoms561.inverseACB_eq,
    HexagonAtoms561.innerACB_eq,
    HexagonAtoms561.assocBCA_eq,
    HexagonAtoms561.innerRightBAC_eq,
    HexagonAtoms561.assocCAB_eq,
    HexagonAtoms561.outerLeftABC_eq,
    HexagonRowColumn561.product0_eq,
    HexagonRowColumn561.product1_eq,
    HexagonRowColumn561.product2_eq,
    HexagonRowColumn561.product3_eq,
    HexagonRowColumn561.product4_eq,
    HexagonRowColumn561.product5_eq,
    HexagonRowColumn561.product6_eq,
    HexagonRowColumn561.product7_eq] using rightFinal5_case_6_1_checked

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonCases5
