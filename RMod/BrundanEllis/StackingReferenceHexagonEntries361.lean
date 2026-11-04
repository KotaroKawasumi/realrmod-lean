import RMod.BrundanEllis.StackingReferenceHexagonMiddle3
import RMod.BrundanEllis.StackingReferenceSparseMatrixCheck
import RMod.BrundanEllis.StackingReferenceHexagonAtoms361
import RMod.BrundanEllis.StackingReferenceHexagonRowColumn361

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

private theorem left0Middle3_eq_case_6_1_row_0_0_0 : (left0Middle3 6 1) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn361.rows_outerABC HexagonRowColumn361.cols_assocABC) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_6_1_row_0_0_1 : (left0Middle3 6 1) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn361.rows_outerABC HexagonRowColumn361.cols_assocABC) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_6_1_row_0_0_2 : (left0Middle3 6 1) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn361.rows_outerABC HexagonRowColumn361.cols_assocABC) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_6_1_row_0_0_3 : (left0Middle3 6 1) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn361.rows_outerABC HexagonRowColumn361.cols_assocABC) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_6_1_row_0_1_0 : (left0Middle3 6 1) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn361.rows_outerABC HexagonRowColumn361.cols_assocABC) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_6_1_row_0_1_1 : (left0Middle3 6 1) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn361.rows_outerABC HexagonRowColumn361.cols_assocABC) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_6_1_row_0_1_2 : (left0Middle3 6 1) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn361.rows_outerABC HexagonRowColumn361.cols_assocABC) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_6_1_row_0_1_3 : (left0Middle3 6 1) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn361.rows_outerABC HexagonRowColumn361.cols_assocABC) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_6_1_row_1_0_0 : (left0Middle3 6 1) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn361.rows_outerABC HexagonRowColumn361.cols_assocABC) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_6_1_row_1_0_1 : (left0Middle3 6 1) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn361.rows_outerABC HexagonRowColumn361.cols_assocABC) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_6_1_row_1_0_2 : (left0Middle3 6 1) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn361.rows_outerABC HexagonRowColumn361.cols_assocABC) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_6_1_row_1_0_3 : (left0Middle3 6 1) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn361.rows_outerABC HexagonRowColumn361.cols_assocABC) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_6_1_row_1_1_0 : (left0Middle3 6 1) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn361.rows_outerABC HexagonRowColumn361.cols_assocABC) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_6_1_row_1_1_1 : (left0Middle3 6 1) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn361.rows_outerABC HexagonRowColumn361.cols_assocABC) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_6_1_row_1_1_2 : (left0Middle3 6 1) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn361.rows_outerABC HexagonRowColumn361.cols_assocABC) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_6_1_row_1_1_3 : (left0Middle3 6 1) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn361.rows_outerABC HexagonRowColumn361.cols_assocABC) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_6_1_checked : left0Middle3 6 1 = rowColumnMul HexagonRowColumn361.rows_outerABC HexagonRowColumn361.cols_assocABC := by
  funext r
  fin_cases r
  · exact left0Middle3_eq_case_6_1_row_0_0_0
  · exact left0Middle3_eq_case_6_1_row_0_0_1
  · exact left0Middle3_eq_case_6_1_row_0_0_2
  · exact left0Middle3_eq_case_6_1_row_0_0_3
  · exact left0Middle3_eq_case_6_1_row_0_1_0
  · exact left0Middle3_eq_case_6_1_row_0_1_1
  · exact left0Middle3_eq_case_6_1_row_0_1_2
  · exact left0Middle3_eq_case_6_1_row_0_1_3
  · exact left0Middle3_eq_case_6_1_row_1_0_0
  · exact left0Middle3_eq_case_6_1_row_1_0_1
  · exact left0Middle3_eq_case_6_1_row_1_0_2
  · exact left0Middle3_eq_case_6_1_row_1_0_3
  · exact left0Middle3_eq_case_6_1_row_1_1_0
  · exact left0Middle3_eq_case_6_1_row_1_1_1
  · exact left0Middle3_eq_case_6_1_row_1_1_2
  · exact left0Middle3_eq_case_6_1_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem left0Middle3_eq_case_6_1 : left0Middle3 6 1 = outerRightZ 3 6 1 * associatorZ 3 6 1 := by
  simpa only [HexagonAtoms361.assocABC_eq,
    HexagonAtoms361.outerABC_eq,
    HexagonAtoms361.assocBAC_eq,
    HexagonAtoms361.innerABC_eq,
    HexagonAtoms361.innerRightABC_eq,
    HexagonAtoms361.inverseACB_eq,
    HexagonAtoms361.innerACB_eq,
    HexagonAtoms361.assocBCA_eq,
    HexagonAtoms361.innerRightBAC_eq,
    HexagonAtoms361.assocCAB_eq,
    HexagonAtoms361.outerLeftABC_eq,
    HexagonRowColumn361.product0_eq,
    HexagonRowColumn361.product1_eq,
    HexagonRowColumn361.product2_eq,
    HexagonRowColumn361.product3_eq,
    HexagonRowColumn361.product4_eq,
    HexagonRowColumn361.product5_eq,
    HexagonRowColumn361.product6_eq,
    HexagonRowColumn361.product7_eq] using left0Middle3_eq_case_6_1_checked

private theorem left1Middle3_eq_case_6_1_row_0_0_0 : (left1Middle3 6 1) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms361.assocBAC) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_6_1_row_0_0_1 : (left1Middle3 6 1) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms361.assocBAC) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_6_1_row_0_0_2 : (left1Middle3 6 1) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms361.assocBAC) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_6_1_row_0_0_3 : (left1Middle3 6 1) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms361.assocBAC) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_6_1_row_0_1_0 : (left1Middle3 6 1) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms361.assocBAC) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_6_1_row_0_1_1 : (left1Middle3 6 1) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms361.assocBAC) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_6_1_row_0_1_2 : (left1Middle3 6 1) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms361.assocBAC) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_6_1_row_0_1_3 : (left1Middle3 6 1) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms361.assocBAC) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_6_1_row_1_0_0 : (left1Middle3 6 1) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms361.assocBAC) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_6_1_row_1_0_1 : (left1Middle3 6 1) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms361.assocBAC) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_6_1_row_1_0_2 : (left1Middle3 6 1) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms361.assocBAC) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_6_1_row_1_0_3 : (left1Middle3 6 1) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms361.assocBAC) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_6_1_row_1_1_0 : (left1Middle3 6 1) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms361.assocBAC) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_6_1_row_1_1_1 : (left1Middle3 6 1) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms361.assocBAC) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_6_1_row_1_1_2 : (left1Middle3 6 1) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms361.assocBAC) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_6_1_row_1_1_3 : (left1Middle3 6 1) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms361.assocBAC) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_6_1_checked : left1Middle3 6 1 = HexagonAtoms361.assocBAC := by
  funext r
  fin_cases r
  · exact left1Middle3_eq_case_6_1_row_0_0_0
  · exact left1Middle3_eq_case_6_1_row_0_0_1
  · exact left1Middle3_eq_case_6_1_row_0_0_2
  · exact left1Middle3_eq_case_6_1_row_0_0_3
  · exact left1Middle3_eq_case_6_1_row_0_1_0
  · exact left1Middle3_eq_case_6_1_row_0_1_1
  · exact left1Middle3_eq_case_6_1_row_0_1_2
  · exact left1Middle3_eq_case_6_1_row_0_1_3
  · exact left1Middle3_eq_case_6_1_row_1_0_0
  · exact left1Middle3_eq_case_6_1_row_1_0_1
  · exact left1Middle3_eq_case_6_1_row_1_0_2
  · exact left1Middle3_eq_case_6_1_row_1_0_3
  · exact left1Middle3_eq_case_6_1_row_1_1_0
  · exact left1Middle3_eq_case_6_1_row_1_1_1
  · exact left1Middle3_eq_case_6_1_row_1_1_2
  · exact left1Middle3_eq_case_6_1_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem left1Middle3_eq_case_6_1 : left1Middle3 6 1 = associatorZ 6 3 1 * innerLeftZ 3 6 1 := by
  simpa only [HexagonAtoms361.assocABC_eq,
    HexagonAtoms361.outerABC_eq,
    HexagonAtoms361.assocBAC_eq,
    HexagonAtoms361.innerABC_eq,
    HexagonAtoms361.innerRightABC_eq,
    HexagonAtoms361.inverseACB_eq,
    HexagonAtoms361.innerACB_eq,
    HexagonAtoms361.assocBCA_eq,
    HexagonAtoms361.innerRightBAC_eq,
    HexagonAtoms361.assocCAB_eq,
    HexagonAtoms361.outerLeftABC_eq,
    HexagonRowColumn361.product0_eq,
    HexagonRowColumn361.product1_eq,
    HexagonRowColumn361.product2_eq,
    HexagonRowColumn361.product3_eq,
    HexagonRowColumn361.product4_eq,
    HexagonRowColumn361.product5_eq,
    HexagonRowColumn361.product6_eq,
    HexagonRowColumn361.product7_eq] using left1Middle3_eq_case_6_1_checked

private theorem right0Middle3_eq_case_6_1_row_0_0_0 : (right0Middle3 6 1) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms361.assocABC) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_6_1_row_0_0_1 : (right0Middle3 6 1) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms361.assocABC) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_6_1_row_0_0_2 : (right0Middle3 6 1) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms361.assocABC) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_6_1_row_0_0_3 : (right0Middle3 6 1) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms361.assocABC) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_6_1_row_0_1_0 : (right0Middle3 6 1) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms361.assocABC) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_6_1_row_0_1_1 : (right0Middle3 6 1) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms361.assocABC) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_6_1_row_0_1_2 : (right0Middle3 6 1) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms361.assocABC) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_6_1_row_0_1_3 : (right0Middle3 6 1) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms361.assocABC) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_6_1_row_1_0_0 : (right0Middle3 6 1) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms361.assocABC) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_6_1_row_1_0_1 : (right0Middle3 6 1) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms361.assocABC) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_6_1_row_1_0_2 : (right0Middle3 6 1) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms361.assocABC) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_6_1_row_1_0_3 : (right0Middle3 6 1) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms361.assocABC) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_6_1_row_1_1_0 : (right0Middle3 6 1) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms361.assocABC) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_6_1_row_1_1_1 : (right0Middle3 6 1) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms361.assocABC) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_6_1_row_1_1_2 : (right0Middle3 6 1) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms361.assocABC) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_6_1_row_1_1_3 : (right0Middle3 6 1) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms361.assocABC) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_6_1_checked : right0Middle3 6 1 = HexagonAtoms361.assocABC := by
  funext r
  fin_cases r
  · exact right0Middle3_eq_case_6_1_row_0_0_0
  · exact right0Middle3_eq_case_6_1_row_0_0_1
  · exact right0Middle3_eq_case_6_1_row_0_0_2
  · exact right0Middle3_eq_case_6_1_row_0_0_3
  · exact right0Middle3_eq_case_6_1_row_0_1_0
  · exact right0Middle3_eq_case_6_1_row_0_1_1
  · exact right0Middle3_eq_case_6_1_row_0_1_2
  · exact right0Middle3_eq_case_6_1_row_0_1_3
  · exact right0Middle3_eq_case_6_1_row_1_0_0
  · exact right0Middle3_eq_case_6_1_row_1_0_1
  · exact right0Middle3_eq_case_6_1_row_1_0_2
  · exact right0Middle3_eq_case_6_1_row_1_0_3
  · exact right0Middle3_eq_case_6_1_row_1_1_0
  · exact right0Middle3_eq_case_6_1_row_1_1_1
  · exact right0Middle3_eq_case_6_1_row_1_1_2
  · exact right0Middle3_eq_case_6_1_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem right0Middle3_eq_case_6_1 : right0Middle3 6 1 = innerRightZ 3 6 1 * associatorZ 3 6 1 := by
  simpa only [HexagonAtoms361.assocABC_eq,
    HexagonAtoms361.outerABC_eq,
    HexagonAtoms361.assocBAC_eq,
    HexagonAtoms361.innerABC_eq,
    HexagonAtoms361.innerRightABC_eq,
    HexagonAtoms361.inverseACB_eq,
    HexagonAtoms361.innerACB_eq,
    HexagonAtoms361.assocBCA_eq,
    HexagonAtoms361.innerRightBAC_eq,
    HexagonAtoms361.assocCAB_eq,
    HexagonAtoms361.outerLeftABC_eq,
    HexagonRowColumn361.product0_eq,
    HexagonRowColumn361.product1_eq,
    HexagonRowColumn361.product2_eq,
    HexagonRowColumn361.product3_eq,
    HexagonRowColumn361.product4_eq,
    HexagonRowColumn361.product5_eq,
    HexagonRowColumn361.product6_eq,
    HexagonRowColumn361.product7_eq] using right0Middle3_eq_case_6_1_checked

private theorem right1Middle3_eq_case_6_1_row_0_0_0 : (right1Middle3 6 1) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn361.rows_inverseACB HexagonRowColumn361.cols_right0) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_6_1_row_0_0_1 : (right1Middle3 6 1) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn361.rows_inverseACB HexagonRowColumn361.cols_right0) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_6_1_row_0_0_2 : (right1Middle3 6 1) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn361.rows_inverseACB HexagonRowColumn361.cols_right0) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_6_1_row_0_0_3 : (right1Middle3 6 1) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn361.rows_inverseACB HexagonRowColumn361.cols_right0) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_6_1_row_0_1_0 : (right1Middle3 6 1) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn361.rows_inverseACB HexagonRowColumn361.cols_right0) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_6_1_row_0_1_1 : (right1Middle3 6 1) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn361.rows_inverseACB HexagonRowColumn361.cols_right0) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_6_1_row_0_1_2 : (right1Middle3 6 1) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn361.rows_inverseACB HexagonRowColumn361.cols_right0) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_6_1_row_0_1_3 : (right1Middle3 6 1) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn361.rows_inverseACB HexagonRowColumn361.cols_right0) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_6_1_row_1_0_0 : (right1Middle3 6 1) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn361.rows_inverseACB HexagonRowColumn361.cols_right0) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_6_1_row_1_0_1 : (right1Middle3 6 1) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn361.rows_inverseACB HexagonRowColumn361.cols_right0) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_6_1_row_1_0_2 : (right1Middle3 6 1) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn361.rows_inverseACB HexagonRowColumn361.cols_right0) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_6_1_row_1_0_3 : (right1Middle3 6 1) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn361.rows_inverseACB HexagonRowColumn361.cols_right0) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_6_1_row_1_1_0 : (right1Middle3 6 1) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn361.rows_inverseACB HexagonRowColumn361.cols_right0) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_6_1_row_1_1_1 : (right1Middle3 6 1) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn361.rows_inverseACB HexagonRowColumn361.cols_right0) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_6_1_row_1_1_2 : (right1Middle3 6 1) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn361.rows_inverseACB HexagonRowColumn361.cols_right0) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_6_1_row_1_1_3 : (right1Middle3 6 1) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn361.rows_inverseACB HexagonRowColumn361.cols_right0) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_6_1_checked : right1Middle3 6 1 = rowColumnMul HexagonRowColumn361.rows_inverseACB HexagonRowColumn361.cols_right0 := by
  funext r
  fin_cases r
  · exact right1Middle3_eq_case_6_1_row_0_0_0
  · exact right1Middle3_eq_case_6_1_row_0_0_1
  · exact right1Middle3_eq_case_6_1_row_0_0_2
  · exact right1Middle3_eq_case_6_1_row_0_0_3
  · exact right1Middle3_eq_case_6_1_row_0_1_0
  · exact right1Middle3_eq_case_6_1_row_0_1_1
  · exact right1Middle3_eq_case_6_1_row_0_1_2
  · exact right1Middle3_eq_case_6_1_row_0_1_3
  · exact right1Middle3_eq_case_6_1_row_1_0_0
  · exact right1Middle3_eq_case_6_1_row_1_0_1
  · exact right1Middle3_eq_case_6_1_row_1_0_2
  · exact right1Middle3_eq_case_6_1_row_1_0_3
  · exact right1Middle3_eq_case_6_1_row_1_1_0
  · exact right1Middle3_eq_case_6_1_row_1_1_1
  · exact right1Middle3_eq_case_6_1_row_1_1_2
  · exact right1Middle3_eq_case_6_1_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem right1Middle3_eq_case_6_1 : right1Middle3 6 1 = associatorInverseZ 3 1 6 * right0Middle3 6 1 := by
  simpa only [HexagonAtoms361.assocABC_eq,
    HexagonAtoms361.outerABC_eq,
    HexagonAtoms361.assocBAC_eq,
    HexagonAtoms361.innerABC_eq,
    HexagonAtoms361.innerRightABC_eq,
    HexagonAtoms361.inverseACB_eq,
    HexagonAtoms361.innerACB_eq,
    HexagonAtoms361.assocBCA_eq,
    HexagonAtoms361.innerRightBAC_eq,
    HexagonAtoms361.assocCAB_eq,
    HexagonAtoms361.outerLeftABC_eq,
    HexagonRowColumn361.product0_eq,
    HexagonRowColumn361.product1_eq,
    HexagonRowColumn361.product2_eq,
    HexagonRowColumn361.product3_eq,
    HexagonRowColumn361.product4_eq,
    HexagonRowColumn361.product5_eq,
    HexagonRowColumn361.product6_eq,
    HexagonRowColumn361.product7_eq] using right1Middle3_eq_case_6_1_checked

private theorem right2Middle3_eq_case_6_1_row_0_0_0 : (right2Middle3 6 1) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (right1Middle3 6 1) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_6_1_row_0_0_1 : (right2Middle3 6 1) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (right1Middle3 6 1) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_6_1_row_0_0_2 : (right2Middle3 6 1) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (right1Middle3 6 1) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_6_1_row_0_0_3 : (right2Middle3 6 1) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (right1Middle3 6 1) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_6_1_row_0_1_0 : (right2Middle3 6 1) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (right1Middle3 6 1) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_6_1_row_0_1_1 : (right2Middle3 6 1) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (right1Middle3 6 1) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_6_1_row_0_1_2 : (right2Middle3 6 1) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (right1Middle3 6 1) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_6_1_row_0_1_3 : (right2Middle3 6 1) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (right1Middle3 6 1) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_6_1_row_1_0_0 : (right2Middle3 6 1) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (right1Middle3 6 1) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_6_1_row_1_0_1 : (right2Middle3 6 1) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (right1Middle3 6 1) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_6_1_row_1_0_2 : (right2Middle3 6 1) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (right1Middle3 6 1) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_6_1_row_1_0_3 : (right2Middle3 6 1) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (right1Middle3 6 1) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_6_1_row_1_1_0 : (right2Middle3 6 1) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (right1Middle3 6 1) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_6_1_row_1_1_1 : (right2Middle3 6 1) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (right1Middle3 6 1) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_6_1_row_1_1_2 : (right2Middle3 6 1) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (right1Middle3 6 1) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_6_1_row_1_1_3 : (right2Middle3 6 1) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (right1Middle3 6 1) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_6_1_checked : right2Middle3 6 1 = right1Middle3 6 1 := by
  funext r
  fin_cases r
  · exact right2Middle3_eq_case_6_1_row_0_0_0
  · exact right2Middle3_eq_case_6_1_row_0_0_1
  · exact right2Middle3_eq_case_6_1_row_0_0_2
  · exact right2Middle3_eq_case_6_1_row_0_0_3
  · exact right2Middle3_eq_case_6_1_row_0_1_0
  · exact right2Middle3_eq_case_6_1_row_0_1_1
  · exact right2Middle3_eq_case_6_1_row_0_1_2
  · exact right2Middle3_eq_case_6_1_row_0_1_3
  · exact right2Middle3_eq_case_6_1_row_1_0_0
  · exact right2Middle3_eq_case_6_1_row_1_0_1
  · exact right2Middle3_eq_case_6_1_row_1_0_2
  · exact right2Middle3_eq_case_6_1_row_1_0_3
  · exact right2Middle3_eq_case_6_1_row_1_1_0
  · exact right2Middle3_eq_case_6_1_row_1_1_1
  · exact right2Middle3_eq_case_6_1_row_1_1_2
  · exact right2Middle3_eq_case_6_1_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem right2Middle3_eq_case_6_1 : right2Middle3 6 1 = innerLeftZ 3 1 6 * right1Middle3 6 1 := by
  simpa only [HexagonAtoms361.assocABC_eq,
    HexagonAtoms361.outerABC_eq,
    HexagonAtoms361.assocBAC_eq,
    HexagonAtoms361.innerABC_eq,
    HexagonAtoms361.innerRightABC_eq,
    HexagonAtoms361.inverseACB_eq,
    HexagonAtoms361.innerACB_eq,
    HexagonAtoms361.assocBCA_eq,
    HexagonAtoms361.innerRightBAC_eq,
    HexagonAtoms361.assocCAB_eq,
    HexagonAtoms361.outerLeftABC_eq,
    HexagonRowColumn361.product0_eq,
    HexagonRowColumn361.product1_eq,
    HexagonRowColumn361.product2_eq,
    HexagonRowColumn361.product3_eq,
    HexagonRowColumn361.product4_eq,
    HexagonRowColumn361.product5_eq,
    HexagonRowColumn361.product6_eq,
    HexagonRowColumn361.product7_eq] using right2Middle3_eq_case_6_1_checked

private theorem leftFinal3_case_6_1_row_0_0_0 : (((-1 : ℤ) ^ (leftScaleBit 3 6 1).val * positiveScale (leftScaleExponent 3 6 1)) •
      (rowColumnMul HexagonRowColumn361.rows_assocBCA HexagonRowColumn361.cols_left0)) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 3 6 1) • (left1Middle3 6 1)) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal3_case_6_1_row_0_0_1 : (((-1 : ℤ) ^ (leftScaleBit 3 6 1).val * positiveScale (leftScaleExponent 3 6 1)) •
      (rowColumnMul HexagonRowColumn361.rows_assocBCA HexagonRowColumn361.cols_left0)) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 3 6 1) • (left1Middle3 6 1)) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal3_case_6_1_row_0_0_2 : (((-1 : ℤ) ^ (leftScaleBit 3 6 1).val * positiveScale (leftScaleExponent 3 6 1)) •
      (rowColumnMul HexagonRowColumn361.rows_assocBCA HexagonRowColumn361.cols_left0)) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 3 6 1) • (left1Middle3 6 1)) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal3_case_6_1_row_0_0_3 : (((-1 : ℤ) ^ (leftScaleBit 3 6 1).val * positiveScale (leftScaleExponent 3 6 1)) •
      (rowColumnMul HexagonRowColumn361.rows_assocBCA HexagonRowColumn361.cols_left0)) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 3 6 1) • (left1Middle3 6 1)) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal3_case_6_1_row_0_1_0 : (((-1 : ℤ) ^ (leftScaleBit 3 6 1).val * positiveScale (leftScaleExponent 3 6 1)) •
      (rowColumnMul HexagonRowColumn361.rows_assocBCA HexagonRowColumn361.cols_left0)) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 3 6 1) • (left1Middle3 6 1)) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal3_case_6_1_row_0_1_1 : (((-1 : ℤ) ^ (leftScaleBit 3 6 1).val * positiveScale (leftScaleExponent 3 6 1)) •
      (rowColumnMul HexagonRowColumn361.rows_assocBCA HexagonRowColumn361.cols_left0)) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 3 6 1) • (left1Middle3 6 1)) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal3_case_6_1_row_0_1_2 : (((-1 : ℤ) ^ (leftScaleBit 3 6 1).val * positiveScale (leftScaleExponent 3 6 1)) •
      (rowColumnMul HexagonRowColumn361.rows_assocBCA HexagonRowColumn361.cols_left0)) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 3 6 1) • (left1Middle3 6 1)) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal3_case_6_1_row_0_1_3 : (((-1 : ℤ) ^ (leftScaleBit 3 6 1).val * positiveScale (leftScaleExponent 3 6 1)) •
      (rowColumnMul HexagonRowColumn361.rows_assocBCA HexagonRowColumn361.cols_left0)) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 3 6 1) • (left1Middle3 6 1)) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal3_case_6_1_row_1_0_0 : (((-1 : ℤ) ^ (leftScaleBit 3 6 1).val * positiveScale (leftScaleExponent 3 6 1)) •
      (rowColumnMul HexagonRowColumn361.rows_assocBCA HexagonRowColumn361.cols_left0)) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 3 6 1) • (left1Middle3 6 1)) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal3_case_6_1_row_1_0_1 : (((-1 : ℤ) ^ (leftScaleBit 3 6 1).val * positiveScale (leftScaleExponent 3 6 1)) •
      (rowColumnMul HexagonRowColumn361.rows_assocBCA HexagonRowColumn361.cols_left0)) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 3 6 1) • (left1Middle3 6 1)) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal3_case_6_1_row_1_0_2 : (((-1 : ℤ) ^ (leftScaleBit 3 6 1).val * positiveScale (leftScaleExponent 3 6 1)) •
      (rowColumnMul HexagonRowColumn361.rows_assocBCA HexagonRowColumn361.cols_left0)) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 3 6 1) • (left1Middle3 6 1)) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal3_case_6_1_row_1_0_3 : (((-1 : ℤ) ^ (leftScaleBit 3 6 1).val * positiveScale (leftScaleExponent 3 6 1)) •
      (rowColumnMul HexagonRowColumn361.rows_assocBCA HexagonRowColumn361.cols_left0)) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 3 6 1) • (left1Middle3 6 1)) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal3_case_6_1_row_1_1_0 : (((-1 : ℤ) ^ (leftScaleBit 3 6 1).val * positiveScale (leftScaleExponent 3 6 1)) •
      (rowColumnMul HexagonRowColumn361.rows_assocBCA HexagonRowColumn361.cols_left0)) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 3 6 1) • (left1Middle3 6 1)) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal3_case_6_1_row_1_1_1 : (((-1 : ℤ) ^ (leftScaleBit 3 6 1).val * positiveScale (leftScaleExponent 3 6 1)) •
      (rowColumnMul HexagonRowColumn361.rows_assocBCA HexagonRowColumn361.cols_left0)) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 3 6 1) • (left1Middle3 6 1)) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal3_case_6_1_row_1_1_2 : (((-1 : ℤ) ^ (leftScaleBit 3 6 1).val * positiveScale (leftScaleExponent 3 6 1)) •
      (rowColumnMul HexagonRowColumn361.rows_assocBCA HexagonRowColumn361.cols_left0)) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 3 6 1) • (left1Middle3 6 1)) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal3_case_6_1_row_1_1_3 : (((-1 : ℤ) ^ (leftScaleBit 3 6 1).val * positiveScale (leftScaleExponent 3 6 1)) •
      (rowColumnMul HexagonRowColumn361.rows_assocBCA HexagonRowColumn361.cols_left0)) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 3 6 1) • (left1Middle3 6 1)) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal3_case_6_1_checked : ((-1 : ℤ) ^ (leftScaleBit 3 6 1).val * positiveScale (leftScaleExponent 3 6 1)) •
      (rowColumnMul HexagonRowColumn361.rows_assocBCA HexagonRowColumn361.cols_left0) = negativeScale (leftScaleExponent 3 6 1) • (left1Middle3 6 1) := by
  funext r
  fin_cases r
  · exact leftFinal3_case_6_1_row_0_0_0
  · exact leftFinal3_case_6_1_row_0_0_1
  · exact leftFinal3_case_6_1_row_0_0_2
  · exact leftFinal3_case_6_1_row_0_0_3
  · exact leftFinal3_case_6_1_row_0_1_0
  · exact leftFinal3_case_6_1_row_0_1_1
  · exact leftFinal3_case_6_1_row_0_1_2
  · exact leftFinal3_case_6_1_row_0_1_3
  · exact leftFinal3_case_6_1_row_1_0_0
  · exact leftFinal3_case_6_1_row_1_0_1
  · exact leftFinal3_case_6_1_row_1_0_2
  · exact leftFinal3_case_6_1_row_1_0_3
  · exact leftFinal3_case_6_1_row_1_1_0
  · exact leftFinal3_case_6_1_row_1_1_1
  · exact leftFinal3_case_6_1_row_1_1_2
  · exact leftFinal3_case_6_1_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem leftFinal3_case_6_1 : ((-1 : ℤ) ^ (leftScaleBit 3 6 1).val * positiveScale (leftScaleExponent 3 6 1)) •
      (associatorZ 6 1 3 * left0Middle3 6 1) = negativeScale (leftScaleExponent 3 6 1) • (innerRightZ 6 3 1 * left1Middle3 6 1) := by
  simpa only [HexagonAtoms361.assocABC_eq,
    HexagonAtoms361.outerABC_eq,
    HexagonAtoms361.assocBAC_eq,
    HexagonAtoms361.innerABC_eq,
    HexagonAtoms361.innerRightABC_eq,
    HexagonAtoms361.inverseACB_eq,
    HexagonAtoms361.innerACB_eq,
    HexagonAtoms361.assocBCA_eq,
    HexagonAtoms361.innerRightBAC_eq,
    HexagonAtoms361.assocCAB_eq,
    HexagonAtoms361.outerLeftABC_eq,
    HexagonRowColumn361.product0_eq,
    HexagonRowColumn361.product1_eq,
    HexagonRowColumn361.product2_eq,
    HexagonRowColumn361.product3_eq,
    HexagonRowColumn361.product4_eq,
    HexagonRowColumn361.product5_eq,
    HexagonRowColumn361.product6_eq,
    HexagonRowColumn361.product7_eq] using leftFinal3_case_6_1_checked

private theorem rightFinal3_case_6_1_row_0_0_0 : (((-1 : ℤ) ^ (rightScaleBit 3 6 1).val * positiveScale (rightScaleExponent 3 6 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 1 6 : ℤ)) • HexagonAtoms361.outerLeftABC) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (negativeScale (rightScaleExponent 3 6 1) • (rowColumnMul HexagonRowColumn361.rows_assocCAB HexagonRowColumn361.cols_right2)) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal3_case_6_1_row_0_0_1 : (((-1 : ℤ) ^ (rightScaleBit 3 6 1).val * positiveScale (rightScaleExponent 3 6 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 1 6 : ℤ)) • HexagonAtoms361.outerLeftABC) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (negativeScale (rightScaleExponent 3 6 1) • (rowColumnMul HexagonRowColumn361.rows_assocCAB HexagonRowColumn361.cols_right2)) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal3_case_6_1_row_0_0_2 : (((-1 : ℤ) ^ (rightScaleBit 3 6 1).val * positiveScale (rightScaleExponent 3 6 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 1 6 : ℤ)) • HexagonAtoms361.outerLeftABC) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (negativeScale (rightScaleExponent 3 6 1) • (rowColumnMul HexagonRowColumn361.rows_assocCAB HexagonRowColumn361.cols_right2)) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal3_case_6_1_row_0_0_3 : (((-1 : ℤ) ^ (rightScaleBit 3 6 1).val * positiveScale (rightScaleExponent 3 6 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 1 6 : ℤ)) • HexagonAtoms361.outerLeftABC) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (negativeScale (rightScaleExponent 3 6 1) • (rowColumnMul HexagonRowColumn361.rows_assocCAB HexagonRowColumn361.cols_right2)) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal3_case_6_1_row_1_0_0 : (((-1 : ℤ) ^ (rightScaleBit 3 6 1).val * positiveScale (rightScaleExponent 3 6 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 1 6 : ℤ)) • HexagonAtoms361.outerLeftABC) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (negativeScale (rightScaleExponent 3 6 1) • (rowColumnMul HexagonRowColumn361.rows_assocCAB HexagonRowColumn361.cols_right2)) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal3_case_6_1_row_1_0_1 : (((-1 : ℤ) ^ (rightScaleBit 3 6 1).val * positiveScale (rightScaleExponent 3 6 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 1 6 : ℤ)) • HexagonAtoms361.outerLeftABC) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (negativeScale (rightScaleExponent 3 6 1) • (rowColumnMul HexagonRowColumn361.rows_assocCAB HexagonRowColumn361.cols_right2)) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal3_case_6_1_row_1_0_2 : (((-1 : ℤ) ^ (rightScaleBit 3 6 1).val * positiveScale (rightScaleExponent 3 6 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 1 6 : ℤ)) • HexagonAtoms361.outerLeftABC) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (negativeScale (rightScaleExponent 3 6 1) • (rowColumnMul HexagonRowColumn361.rows_assocCAB HexagonRowColumn361.cols_right2)) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal3_case_6_1_row_1_0_3 : (((-1 : ℤ) ^ (rightScaleBit 3 6 1).val * positiveScale (rightScaleExponent 3 6 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 1 6 : ℤ)) • HexagonAtoms361.outerLeftABC) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (negativeScale (rightScaleExponent 3 6 1) • (rowColumnMul HexagonRowColumn361.rows_assocCAB HexagonRowColumn361.cols_right2)) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal3_case_6_1_row_2_0_0 : (((-1 : ℤ) ^ (rightScaleBit 3 6 1).val * positiveScale (rightScaleExponent 3 6 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 1 6 : ℤ)) • HexagonAtoms361.outerLeftABC) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (negativeScale (rightScaleExponent 3 6 1) • (rowColumnMul HexagonRowColumn361.rows_assocCAB HexagonRowColumn361.cols_right2)) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal3_case_6_1_row_2_0_1 : (((-1 : ℤ) ^ (rightScaleBit 3 6 1).val * positiveScale (rightScaleExponent 3 6 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 1 6 : ℤ)) • HexagonAtoms361.outerLeftABC) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (negativeScale (rightScaleExponent 3 6 1) • (rowColumnMul HexagonRowColumn361.rows_assocCAB HexagonRowColumn361.cols_right2)) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal3_case_6_1_row_2_0_2 : (((-1 : ℤ) ^ (rightScaleBit 3 6 1).val * positiveScale (rightScaleExponent 3 6 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 1 6 : ℤ)) • HexagonAtoms361.outerLeftABC) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (negativeScale (rightScaleExponent 3 6 1) • (rowColumnMul HexagonRowColumn361.rows_assocCAB HexagonRowColumn361.cols_right2)) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal3_case_6_1_row_2_0_3 : (((-1 : ℤ) ^ (rightScaleBit 3 6 1).val * positiveScale (rightScaleExponent 3 6 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 1 6 : ℤ)) • HexagonAtoms361.outerLeftABC) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (negativeScale (rightScaleExponent 3 6 1) • (rowColumnMul HexagonRowColumn361.rows_assocCAB HexagonRowColumn361.cols_right2)) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal3_case_6_1_row_3_0_0 : (((-1 : ℤ) ^ (rightScaleBit 3 6 1).val * positiveScale (rightScaleExponent 3 6 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 1 6 : ℤ)) • HexagonAtoms361.outerLeftABC) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (negativeScale (rightScaleExponent 3 6 1) • (rowColumnMul HexagonRowColumn361.rows_assocCAB HexagonRowColumn361.cols_right2)) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal3_case_6_1_row_3_0_1 : (((-1 : ℤ) ^ (rightScaleBit 3 6 1).val * positiveScale (rightScaleExponent 3 6 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 1 6 : ℤ)) • HexagonAtoms361.outerLeftABC) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (negativeScale (rightScaleExponent 3 6 1) • (rowColumnMul HexagonRowColumn361.rows_assocCAB HexagonRowColumn361.cols_right2)) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal3_case_6_1_row_3_0_2 : (((-1 : ℤ) ^ (rightScaleBit 3 6 1).val * positiveScale (rightScaleExponent 3 6 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 1 6 : ℤ)) • HexagonAtoms361.outerLeftABC) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (negativeScale (rightScaleExponent 3 6 1) • (rowColumnMul HexagonRowColumn361.rows_assocCAB HexagonRowColumn361.cols_right2)) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal3_case_6_1_row_3_0_3 : (((-1 : ℤ) ^ (rightScaleBit 3 6 1).val * positiveScale (rightScaleExponent 3 6 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 1 6 : ℤ)) • HexagonAtoms361.outerLeftABC) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (negativeScale (rightScaleExponent 3 6 1) • (rowColumnMul HexagonRowColumn361.rows_assocCAB HexagonRowColumn361.cols_right2)) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal3_case_6_1_checked : ((-1 : ℤ) ^ (rightScaleBit 3 6 1).val * positiveScale (rightScaleExponent 3 6 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 1 6 : ℤ)) • HexagonAtoms361.outerLeftABC = negativeScale (rightScaleExponent 3 6 1) • (rowColumnMul HexagonRowColumn361.rows_assocCAB HexagonRowColumn361.cols_right2) := by
  funext r
  fin_cases r
  · exact rightFinal3_case_6_1_row_0_0_0
  · exact rightFinal3_case_6_1_row_0_0_1
  · exact rightFinal3_case_6_1_row_0_0_2
  · exact rightFinal3_case_6_1_row_0_0_3
  · exact rightFinal3_case_6_1_row_1_0_0
  · exact rightFinal3_case_6_1_row_1_0_1
  · exact rightFinal3_case_6_1_row_1_0_2
  · exact rightFinal3_case_6_1_row_1_0_3
  · exact rightFinal3_case_6_1_row_2_0_0
  · exact rightFinal3_case_6_1_row_2_0_1
  · exact rightFinal3_case_6_1_row_2_0_2
  · exact rightFinal3_case_6_1_row_2_0_3
  · exact rightFinal3_case_6_1_row_3_0_0
  · exact rightFinal3_case_6_1_row_3_0_1
  · exact rightFinal3_case_6_1_row_3_0_2
  · exact rightFinal3_case_6_1_row_3_0_3

set_option backward.isDefEq.respectTransparency false in
theorem rightFinal3_case_6_1 : ((-1 : ℤ) ^ (rightScaleBit 3 6 1).val * positiveScale (rightScaleExponent 3 6 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 1 6 : ℤ)) • outerLeftZ 3 6 1 = negativeScale (rightScaleExponent 3 6 1) • (associatorZ 1 3 6 * right2Middle3 6 1) := by
  simpa only [HexagonAtoms361.assocABC_eq,
    HexagonAtoms361.outerABC_eq,
    HexagonAtoms361.assocBAC_eq,
    HexagonAtoms361.innerABC_eq,
    HexagonAtoms361.innerRightABC_eq,
    HexagonAtoms361.inverseACB_eq,
    HexagonAtoms361.innerACB_eq,
    HexagonAtoms361.assocBCA_eq,
    HexagonAtoms361.innerRightBAC_eq,
    HexagonAtoms361.assocCAB_eq,
    HexagonAtoms361.outerLeftABC_eq,
    HexagonRowColumn361.product0_eq,
    HexagonRowColumn361.product1_eq,
    HexagonRowColumn361.product2_eq,
    HexagonRowColumn361.product3_eq,
    HexagonRowColumn361.product4_eq,
    HexagonRowColumn361.product5_eq,
    HexagonRowColumn361.product6_eq,
    HexagonRowColumn361.product7_eq] using rightFinal3_case_6_1_checked

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonCases3
