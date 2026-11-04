import RMod.BrundanEllis.StackingReferenceHexagonMiddle3
import RMod.BrundanEllis.StackingReferenceSparseMatrixCheck
import RMod.BrundanEllis.StackingReferenceHexagonAtoms327
import RMod.BrundanEllis.StackingReferenceHexagonRowColumn327

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

private theorem left0Middle3_eq_case_2_7_row_0_0_0 : (left0Middle3 2 7) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn327.rows_outerABC HexagonRowColumn327.cols_assocABC) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_2_7_row_0_0_1 : (left0Middle3 2 7) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn327.rows_outerABC HexagonRowColumn327.cols_assocABC) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_2_7_row_0_0_2 : (left0Middle3 2 7) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn327.rows_outerABC HexagonRowColumn327.cols_assocABC) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_2_7_row_0_0_3 : (left0Middle3 2 7) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn327.rows_outerABC HexagonRowColumn327.cols_assocABC) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_2_7_row_0_1_0 : (left0Middle3 2 7) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn327.rows_outerABC HexagonRowColumn327.cols_assocABC) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_2_7_row_0_1_1 : (left0Middle3 2 7) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn327.rows_outerABC HexagonRowColumn327.cols_assocABC) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_2_7_row_0_1_2 : (left0Middle3 2 7) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn327.rows_outerABC HexagonRowColumn327.cols_assocABC) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_2_7_row_0_1_3 : (left0Middle3 2 7) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn327.rows_outerABC HexagonRowColumn327.cols_assocABC) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_2_7_row_1_0_0 : (left0Middle3 2 7) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn327.rows_outerABC HexagonRowColumn327.cols_assocABC) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_2_7_row_1_0_1 : (left0Middle3 2 7) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn327.rows_outerABC HexagonRowColumn327.cols_assocABC) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_2_7_row_1_0_2 : (left0Middle3 2 7) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn327.rows_outerABC HexagonRowColumn327.cols_assocABC) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_2_7_row_1_0_3 : (left0Middle3 2 7) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn327.rows_outerABC HexagonRowColumn327.cols_assocABC) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_2_7_row_1_1_0 : (left0Middle3 2 7) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn327.rows_outerABC HexagonRowColumn327.cols_assocABC) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_2_7_row_1_1_1 : (left0Middle3 2 7) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn327.rows_outerABC HexagonRowColumn327.cols_assocABC) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_2_7_row_1_1_2 : (left0Middle3 2 7) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn327.rows_outerABC HexagonRowColumn327.cols_assocABC) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_2_7_row_1_1_3 : (left0Middle3 2 7) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn327.rows_outerABC HexagonRowColumn327.cols_assocABC) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle3_eq_case_2_7_checked : left0Middle3 2 7 = rowColumnMul HexagonRowColumn327.rows_outerABC HexagonRowColumn327.cols_assocABC := by
  funext r
  fin_cases r
  · exact left0Middle3_eq_case_2_7_row_0_0_0
  · exact left0Middle3_eq_case_2_7_row_0_0_1
  · exact left0Middle3_eq_case_2_7_row_0_0_2
  · exact left0Middle3_eq_case_2_7_row_0_0_3
  · exact left0Middle3_eq_case_2_7_row_0_1_0
  · exact left0Middle3_eq_case_2_7_row_0_1_1
  · exact left0Middle3_eq_case_2_7_row_0_1_2
  · exact left0Middle3_eq_case_2_7_row_0_1_3
  · exact left0Middle3_eq_case_2_7_row_1_0_0
  · exact left0Middle3_eq_case_2_7_row_1_0_1
  · exact left0Middle3_eq_case_2_7_row_1_0_2
  · exact left0Middle3_eq_case_2_7_row_1_0_3
  · exact left0Middle3_eq_case_2_7_row_1_1_0
  · exact left0Middle3_eq_case_2_7_row_1_1_1
  · exact left0Middle3_eq_case_2_7_row_1_1_2
  · exact left0Middle3_eq_case_2_7_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem left0Middle3_eq_case_2_7 : left0Middle3 2 7 = outerRightZ 3 2 7 * associatorZ 3 2 7 := by
  simpa only [HexagonAtoms327.assocABC_eq,
    HexagonAtoms327.outerABC_eq,
    HexagonAtoms327.assocBAC_eq,
    HexagonAtoms327.innerABC_eq,
    HexagonAtoms327.innerRightABC_eq,
    HexagonAtoms327.inverseACB_eq,
    HexagonAtoms327.innerACB_eq,
    HexagonAtoms327.assocBCA_eq,
    HexagonAtoms327.innerRightBAC_eq,
    HexagonAtoms327.assocCAB_eq,
    HexagonAtoms327.outerLeftABC_eq,
    HexagonRowColumn327.product0_eq,
    HexagonRowColumn327.product1_eq,
    HexagonRowColumn327.product2_eq,
    HexagonRowColumn327.product3_eq,
    HexagonRowColumn327.product4_eq,
    HexagonRowColumn327.product5_eq,
    HexagonRowColumn327.product6_eq,
    HexagonRowColumn327.product7_eq] using left0Middle3_eq_case_2_7_checked

private theorem left1Middle3_eq_case_2_7_row_0_0_0 : (left1Middle3 2 7) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms327.assocBAC) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_2_7_row_0_0_1 : (left1Middle3 2 7) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms327.assocBAC) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_2_7_row_0_0_2 : (left1Middle3 2 7) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms327.assocBAC) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_2_7_row_0_0_3 : (left1Middle3 2 7) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms327.assocBAC) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_2_7_row_0_1_0 : (left1Middle3 2 7) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms327.assocBAC) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_2_7_row_0_1_1 : (left1Middle3 2 7) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms327.assocBAC) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_2_7_row_0_1_2 : (left1Middle3 2 7) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms327.assocBAC) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_2_7_row_0_1_3 : (left1Middle3 2 7) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms327.assocBAC) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_2_7_row_1_0_0 : (left1Middle3 2 7) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms327.assocBAC) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_2_7_row_1_0_1 : (left1Middle3 2 7) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms327.assocBAC) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_2_7_row_1_0_2 : (left1Middle3 2 7) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms327.assocBAC) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_2_7_row_1_0_3 : (left1Middle3 2 7) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms327.assocBAC) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_2_7_row_1_1_0 : (left1Middle3 2 7) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms327.assocBAC) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_2_7_row_1_1_1 : (left1Middle3 2 7) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms327.assocBAC) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_2_7_row_1_1_2 : (left1Middle3 2 7) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms327.assocBAC) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_2_7_row_1_1_3 : (left1Middle3 2 7) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms327.assocBAC) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle3_eq_case_2_7_checked : left1Middle3 2 7 = HexagonAtoms327.assocBAC := by
  funext r
  fin_cases r
  · exact left1Middle3_eq_case_2_7_row_0_0_0
  · exact left1Middle3_eq_case_2_7_row_0_0_1
  · exact left1Middle3_eq_case_2_7_row_0_0_2
  · exact left1Middle3_eq_case_2_7_row_0_0_3
  · exact left1Middle3_eq_case_2_7_row_0_1_0
  · exact left1Middle3_eq_case_2_7_row_0_1_1
  · exact left1Middle3_eq_case_2_7_row_0_1_2
  · exact left1Middle3_eq_case_2_7_row_0_1_3
  · exact left1Middle3_eq_case_2_7_row_1_0_0
  · exact left1Middle3_eq_case_2_7_row_1_0_1
  · exact left1Middle3_eq_case_2_7_row_1_0_2
  · exact left1Middle3_eq_case_2_7_row_1_0_3
  · exact left1Middle3_eq_case_2_7_row_1_1_0
  · exact left1Middle3_eq_case_2_7_row_1_1_1
  · exact left1Middle3_eq_case_2_7_row_1_1_2
  · exact left1Middle3_eq_case_2_7_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem left1Middle3_eq_case_2_7 : left1Middle3 2 7 = associatorZ 2 3 7 * innerLeftZ 3 2 7 := by
  simpa only [HexagonAtoms327.assocABC_eq,
    HexagonAtoms327.outerABC_eq,
    HexagonAtoms327.assocBAC_eq,
    HexagonAtoms327.innerABC_eq,
    HexagonAtoms327.innerRightABC_eq,
    HexagonAtoms327.inverseACB_eq,
    HexagonAtoms327.innerACB_eq,
    HexagonAtoms327.assocBCA_eq,
    HexagonAtoms327.innerRightBAC_eq,
    HexagonAtoms327.assocCAB_eq,
    HexagonAtoms327.outerLeftABC_eq,
    HexagonRowColumn327.product0_eq,
    HexagonRowColumn327.product1_eq,
    HexagonRowColumn327.product2_eq,
    HexagonRowColumn327.product3_eq,
    HexagonRowColumn327.product4_eq,
    HexagonRowColumn327.product5_eq,
    HexagonRowColumn327.product6_eq,
    HexagonRowColumn327.product7_eq] using left1Middle3_eq_case_2_7_checked

private theorem right0Middle3_eq_case_2_7_row_0_0_0 : (right0Middle3 2 7) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms327.assocABC) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_2_7_row_0_0_1 : (right0Middle3 2 7) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms327.assocABC) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_2_7_row_0_0_2 : (right0Middle3 2 7) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms327.assocABC) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_2_7_row_0_0_3 : (right0Middle3 2 7) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms327.assocABC) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_2_7_row_0_1_0 : (right0Middle3 2 7) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms327.assocABC) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_2_7_row_0_1_1 : (right0Middle3 2 7) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms327.assocABC) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_2_7_row_0_1_2 : (right0Middle3 2 7) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms327.assocABC) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_2_7_row_0_1_3 : (right0Middle3 2 7) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms327.assocABC) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_2_7_row_1_0_0 : (right0Middle3 2 7) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms327.assocABC) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_2_7_row_1_0_1 : (right0Middle3 2 7) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms327.assocABC) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_2_7_row_1_0_2 : (right0Middle3 2 7) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms327.assocABC) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_2_7_row_1_0_3 : (right0Middle3 2 7) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms327.assocABC) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_2_7_row_1_1_0 : (right0Middle3 2 7) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms327.assocABC) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_2_7_row_1_1_1 : (right0Middle3 2 7) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms327.assocABC) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_2_7_row_1_1_2 : (right0Middle3 2 7) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms327.assocABC) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_2_7_row_1_1_3 : (right0Middle3 2 7) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms327.assocABC) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle3_eq_case_2_7_checked : right0Middle3 2 7 = HexagonAtoms327.assocABC := by
  funext r
  fin_cases r
  · exact right0Middle3_eq_case_2_7_row_0_0_0
  · exact right0Middle3_eq_case_2_7_row_0_0_1
  · exact right0Middle3_eq_case_2_7_row_0_0_2
  · exact right0Middle3_eq_case_2_7_row_0_0_3
  · exact right0Middle3_eq_case_2_7_row_0_1_0
  · exact right0Middle3_eq_case_2_7_row_0_1_1
  · exact right0Middle3_eq_case_2_7_row_0_1_2
  · exact right0Middle3_eq_case_2_7_row_0_1_3
  · exact right0Middle3_eq_case_2_7_row_1_0_0
  · exact right0Middle3_eq_case_2_7_row_1_0_1
  · exact right0Middle3_eq_case_2_7_row_1_0_2
  · exact right0Middle3_eq_case_2_7_row_1_0_3
  · exact right0Middle3_eq_case_2_7_row_1_1_0
  · exact right0Middle3_eq_case_2_7_row_1_1_1
  · exact right0Middle3_eq_case_2_7_row_1_1_2
  · exact right0Middle3_eq_case_2_7_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem right0Middle3_eq_case_2_7 : right0Middle3 2 7 = innerRightZ 3 2 7 * associatorZ 3 2 7 := by
  simpa only [HexagonAtoms327.assocABC_eq,
    HexagonAtoms327.outerABC_eq,
    HexagonAtoms327.assocBAC_eq,
    HexagonAtoms327.innerABC_eq,
    HexagonAtoms327.innerRightABC_eq,
    HexagonAtoms327.inverseACB_eq,
    HexagonAtoms327.innerACB_eq,
    HexagonAtoms327.assocBCA_eq,
    HexagonAtoms327.innerRightBAC_eq,
    HexagonAtoms327.assocCAB_eq,
    HexagonAtoms327.outerLeftABC_eq,
    HexagonRowColumn327.product0_eq,
    HexagonRowColumn327.product1_eq,
    HexagonRowColumn327.product2_eq,
    HexagonRowColumn327.product3_eq,
    HexagonRowColumn327.product4_eq,
    HexagonRowColumn327.product5_eq,
    HexagonRowColumn327.product6_eq,
    HexagonRowColumn327.product7_eq] using right0Middle3_eq_case_2_7_checked

private theorem right1Middle3_eq_case_2_7_row_0_0_0 : (right1Middle3 2 7) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn327.rows_inverseACB HexagonRowColumn327.cols_right0) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_2_7_row_0_0_1 : (right1Middle3 2 7) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn327.rows_inverseACB HexagonRowColumn327.cols_right0) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_2_7_row_0_0_2 : (right1Middle3 2 7) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn327.rows_inverseACB HexagonRowColumn327.cols_right0) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_2_7_row_0_0_3 : (right1Middle3 2 7) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn327.rows_inverseACB HexagonRowColumn327.cols_right0) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_2_7_row_0_1_0 : (right1Middle3 2 7) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn327.rows_inverseACB HexagonRowColumn327.cols_right0) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_2_7_row_0_1_1 : (right1Middle3 2 7) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn327.rows_inverseACB HexagonRowColumn327.cols_right0) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_2_7_row_0_1_2 : (right1Middle3 2 7) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn327.rows_inverseACB HexagonRowColumn327.cols_right0) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_2_7_row_0_1_3 : (right1Middle3 2 7) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn327.rows_inverseACB HexagonRowColumn327.cols_right0) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_2_7_row_1_0_0 : (right1Middle3 2 7) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn327.rows_inverseACB HexagonRowColumn327.cols_right0) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_2_7_row_1_0_1 : (right1Middle3 2 7) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn327.rows_inverseACB HexagonRowColumn327.cols_right0) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_2_7_row_1_0_2 : (right1Middle3 2 7) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn327.rows_inverseACB HexagonRowColumn327.cols_right0) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_2_7_row_1_0_3 : (right1Middle3 2 7) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn327.rows_inverseACB HexagonRowColumn327.cols_right0) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_2_7_row_1_1_0 : (right1Middle3 2 7) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn327.rows_inverseACB HexagonRowColumn327.cols_right0) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_2_7_row_1_1_1 : (right1Middle3 2 7) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn327.rows_inverseACB HexagonRowColumn327.cols_right0) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_2_7_row_1_1_2 : (right1Middle3 2 7) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn327.rows_inverseACB HexagonRowColumn327.cols_right0) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_2_7_row_1_1_3 : (right1Middle3 2 7) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn327.rows_inverseACB HexagonRowColumn327.cols_right0) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle3_eq_case_2_7_checked : right1Middle3 2 7 = rowColumnMul HexagonRowColumn327.rows_inverseACB HexagonRowColumn327.cols_right0 := by
  funext r
  fin_cases r
  · exact right1Middle3_eq_case_2_7_row_0_0_0
  · exact right1Middle3_eq_case_2_7_row_0_0_1
  · exact right1Middle3_eq_case_2_7_row_0_0_2
  · exact right1Middle3_eq_case_2_7_row_0_0_3
  · exact right1Middle3_eq_case_2_7_row_0_1_0
  · exact right1Middle3_eq_case_2_7_row_0_1_1
  · exact right1Middle3_eq_case_2_7_row_0_1_2
  · exact right1Middle3_eq_case_2_7_row_0_1_3
  · exact right1Middle3_eq_case_2_7_row_1_0_0
  · exact right1Middle3_eq_case_2_7_row_1_0_1
  · exact right1Middle3_eq_case_2_7_row_1_0_2
  · exact right1Middle3_eq_case_2_7_row_1_0_3
  · exact right1Middle3_eq_case_2_7_row_1_1_0
  · exact right1Middle3_eq_case_2_7_row_1_1_1
  · exact right1Middle3_eq_case_2_7_row_1_1_2
  · exact right1Middle3_eq_case_2_7_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem right1Middle3_eq_case_2_7 : right1Middle3 2 7 = associatorInverseZ 3 7 2 * right0Middle3 2 7 := by
  simpa only [HexagonAtoms327.assocABC_eq,
    HexagonAtoms327.outerABC_eq,
    HexagonAtoms327.assocBAC_eq,
    HexagonAtoms327.innerABC_eq,
    HexagonAtoms327.innerRightABC_eq,
    HexagonAtoms327.inverseACB_eq,
    HexagonAtoms327.innerACB_eq,
    HexagonAtoms327.assocBCA_eq,
    HexagonAtoms327.innerRightBAC_eq,
    HexagonAtoms327.assocCAB_eq,
    HexagonAtoms327.outerLeftABC_eq,
    HexagonRowColumn327.product0_eq,
    HexagonRowColumn327.product1_eq,
    HexagonRowColumn327.product2_eq,
    HexagonRowColumn327.product3_eq,
    HexagonRowColumn327.product4_eq,
    HexagonRowColumn327.product5_eq,
    HexagonRowColumn327.product6_eq,
    HexagonRowColumn327.product7_eq] using right1Middle3_eq_case_2_7_checked

private theorem right2Middle3_eq_case_2_7_row_0_0_0 : (right2Middle3 2 7) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (right1Middle3 2 7) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_2_7_row_0_0_1 : (right2Middle3 2 7) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (right1Middle3 2 7) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_2_7_row_0_0_2 : (right2Middle3 2 7) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (right1Middle3 2 7) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_2_7_row_0_0_3 : (right2Middle3 2 7) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (right1Middle3 2 7) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_2_7_row_0_1_0 : (right2Middle3 2 7) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (right1Middle3 2 7) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_2_7_row_0_1_1 : (right2Middle3 2 7) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (right1Middle3 2 7) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_2_7_row_0_1_2 : (right2Middle3 2 7) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (right1Middle3 2 7) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_2_7_row_0_1_3 : (right2Middle3 2 7) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (right1Middle3 2 7) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_2_7_row_1_0_0 : (right2Middle3 2 7) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (right1Middle3 2 7) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_2_7_row_1_0_1 : (right2Middle3 2 7) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (right1Middle3 2 7) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_2_7_row_1_0_2 : (right2Middle3 2 7) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (right1Middle3 2 7) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_2_7_row_1_0_3 : (right2Middle3 2 7) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (right1Middle3 2 7) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_2_7_row_1_1_0 : (right2Middle3 2 7) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (right1Middle3 2 7) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_2_7_row_1_1_1 : (right2Middle3 2 7) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (right1Middle3 2 7) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_2_7_row_1_1_2 : (right2Middle3 2 7) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (right1Middle3 2 7) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_2_7_row_1_1_3 : (right2Middle3 2 7) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (right1Middle3 2 7) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle3_eq_case_2_7_checked : right2Middle3 2 7 = right1Middle3 2 7 := by
  funext r
  fin_cases r
  · exact right2Middle3_eq_case_2_7_row_0_0_0
  · exact right2Middle3_eq_case_2_7_row_0_0_1
  · exact right2Middle3_eq_case_2_7_row_0_0_2
  · exact right2Middle3_eq_case_2_7_row_0_0_3
  · exact right2Middle3_eq_case_2_7_row_0_1_0
  · exact right2Middle3_eq_case_2_7_row_0_1_1
  · exact right2Middle3_eq_case_2_7_row_0_1_2
  · exact right2Middle3_eq_case_2_7_row_0_1_3
  · exact right2Middle3_eq_case_2_7_row_1_0_0
  · exact right2Middle3_eq_case_2_7_row_1_0_1
  · exact right2Middle3_eq_case_2_7_row_1_0_2
  · exact right2Middle3_eq_case_2_7_row_1_0_3
  · exact right2Middle3_eq_case_2_7_row_1_1_0
  · exact right2Middle3_eq_case_2_7_row_1_1_1
  · exact right2Middle3_eq_case_2_7_row_1_1_2
  · exact right2Middle3_eq_case_2_7_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem right2Middle3_eq_case_2_7 : right2Middle3 2 7 = innerLeftZ 3 7 2 * right1Middle3 2 7 := by
  simpa only [HexagonAtoms327.assocABC_eq,
    HexagonAtoms327.outerABC_eq,
    HexagonAtoms327.assocBAC_eq,
    HexagonAtoms327.innerABC_eq,
    HexagonAtoms327.innerRightABC_eq,
    HexagonAtoms327.inverseACB_eq,
    HexagonAtoms327.innerACB_eq,
    HexagonAtoms327.assocBCA_eq,
    HexagonAtoms327.innerRightBAC_eq,
    HexagonAtoms327.assocCAB_eq,
    HexagonAtoms327.outerLeftABC_eq,
    HexagonRowColumn327.product0_eq,
    HexagonRowColumn327.product1_eq,
    HexagonRowColumn327.product2_eq,
    HexagonRowColumn327.product3_eq,
    HexagonRowColumn327.product4_eq,
    HexagonRowColumn327.product5_eq,
    HexagonRowColumn327.product6_eq,
    HexagonRowColumn327.product7_eq] using right2Middle3_eq_case_2_7_checked

private theorem leftFinal3_case_2_7_row_0_0_0 : (((-1 : ℤ) ^ (leftScaleBit 3 2 7).val * positiveScale (leftScaleExponent 3 2 7)) •
      (rowColumnMul HexagonRowColumn327.rows_assocBCA HexagonRowColumn327.cols_left0)) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 3 2 7) • (left1Middle3 2 7)) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal3_case_2_7_row_0_0_1 : (((-1 : ℤ) ^ (leftScaleBit 3 2 7).val * positiveScale (leftScaleExponent 3 2 7)) •
      (rowColumnMul HexagonRowColumn327.rows_assocBCA HexagonRowColumn327.cols_left0)) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 3 2 7) • (left1Middle3 2 7)) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal3_case_2_7_row_0_0_2 : (((-1 : ℤ) ^ (leftScaleBit 3 2 7).val * positiveScale (leftScaleExponent 3 2 7)) •
      (rowColumnMul HexagonRowColumn327.rows_assocBCA HexagonRowColumn327.cols_left0)) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 3 2 7) • (left1Middle3 2 7)) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal3_case_2_7_row_0_0_3 : (((-1 : ℤ) ^ (leftScaleBit 3 2 7).val * positiveScale (leftScaleExponent 3 2 7)) •
      (rowColumnMul HexagonRowColumn327.rows_assocBCA HexagonRowColumn327.cols_left0)) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 3 2 7) • (left1Middle3 2 7)) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal3_case_2_7_row_0_1_0 : (((-1 : ℤ) ^ (leftScaleBit 3 2 7).val * positiveScale (leftScaleExponent 3 2 7)) •
      (rowColumnMul HexagonRowColumn327.rows_assocBCA HexagonRowColumn327.cols_left0)) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 3 2 7) • (left1Middle3 2 7)) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal3_case_2_7_row_0_1_1 : (((-1 : ℤ) ^ (leftScaleBit 3 2 7).val * positiveScale (leftScaleExponent 3 2 7)) •
      (rowColumnMul HexagonRowColumn327.rows_assocBCA HexagonRowColumn327.cols_left0)) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 3 2 7) • (left1Middle3 2 7)) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal3_case_2_7_row_0_1_2 : (((-1 : ℤ) ^ (leftScaleBit 3 2 7).val * positiveScale (leftScaleExponent 3 2 7)) •
      (rowColumnMul HexagonRowColumn327.rows_assocBCA HexagonRowColumn327.cols_left0)) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 3 2 7) • (left1Middle3 2 7)) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal3_case_2_7_row_0_1_3 : (((-1 : ℤ) ^ (leftScaleBit 3 2 7).val * positiveScale (leftScaleExponent 3 2 7)) •
      (rowColumnMul HexagonRowColumn327.rows_assocBCA HexagonRowColumn327.cols_left0)) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 3 2 7) • (left1Middle3 2 7)) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal3_case_2_7_row_1_0_0 : (((-1 : ℤ) ^ (leftScaleBit 3 2 7).val * positiveScale (leftScaleExponent 3 2 7)) •
      (rowColumnMul HexagonRowColumn327.rows_assocBCA HexagonRowColumn327.cols_left0)) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 3 2 7) • (left1Middle3 2 7)) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal3_case_2_7_row_1_0_1 : (((-1 : ℤ) ^ (leftScaleBit 3 2 7).val * positiveScale (leftScaleExponent 3 2 7)) •
      (rowColumnMul HexagonRowColumn327.rows_assocBCA HexagonRowColumn327.cols_left0)) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 3 2 7) • (left1Middle3 2 7)) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal3_case_2_7_row_1_0_2 : (((-1 : ℤ) ^ (leftScaleBit 3 2 7).val * positiveScale (leftScaleExponent 3 2 7)) •
      (rowColumnMul HexagonRowColumn327.rows_assocBCA HexagonRowColumn327.cols_left0)) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 3 2 7) • (left1Middle3 2 7)) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal3_case_2_7_row_1_0_3 : (((-1 : ℤ) ^ (leftScaleBit 3 2 7).val * positiveScale (leftScaleExponent 3 2 7)) •
      (rowColumnMul HexagonRowColumn327.rows_assocBCA HexagonRowColumn327.cols_left0)) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 3 2 7) • (left1Middle3 2 7)) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal3_case_2_7_row_1_1_0 : (((-1 : ℤ) ^ (leftScaleBit 3 2 7).val * positiveScale (leftScaleExponent 3 2 7)) •
      (rowColumnMul HexagonRowColumn327.rows_assocBCA HexagonRowColumn327.cols_left0)) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 3 2 7) • (left1Middle3 2 7)) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal3_case_2_7_row_1_1_1 : (((-1 : ℤ) ^ (leftScaleBit 3 2 7).val * positiveScale (leftScaleExponent 3 2 7)) •
      (rowColumnMul HexagonRowColumn327.rows_assocBCA HexagonRowColumn327.cols_left0)) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 3 2 7) • (left1Middle3 2 7)) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal3_case_2_7_row_1_1_2 : (((-1 : ℤ) ^ (leftScaleBit 3 2 7).val * positiveScale (leftScaleExponent 3 2 7)) •
      (rowColumnMul HexagonRowColumn327.rows_assocBCA HexagonRowColumn327.cols_left0)) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 3 2 7) • (left1Middle3 2 7)) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal3_case_2_7_row_1_1_3 : (((-1 : ℤ) ^ (leftScaleBit 3 2 7).val * positiveScale (leftScaleExponent 3 2 7)) •
      (rowColumnMul HexagonRowColumn327.rows_assocBCA HexagonRowColumn327.cols_left0)) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 3 2 7) • (left1Middle3 2 7)) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal3_case_2_7_checked : ((-1 : ℤ) ^ (leftScaleBit 3 2 7).val * positiveScale (leftScaleExponent 3 2 7)) •
      (rowColumnMul HexagonRowColumn327.rows_assocBCA HexagonRowColumn327.cols_left0) = negativeScale (leftScaleExponent 3 2 7) • (left1Middle3 2 7) := by
  funext r
  fin_cases r
  · exact leftFinal3_case_2_7_row_0_0_0
  · exact leftFinal3_case_2_7_row_0_0_1
  · exact leftFinal3_case_2_7_row_0_0_2
  · exact leftFinal3_case_2_7_row_0_0_3
  · exact leftFinal3_case_2_7_row_0_1_0
  · exact leftFinal3_case_2_7_row_0_1_1
  · exact leftFinal3_case_2_7_row_0_1_2
  · exact leftFinal3_case_2_7_row_0_1_3
  · exact leftFinal3_case_2_7_row_1_0_0
  · exact leftFinal3_case_2_7_row_1_0_1
  · exact leftFinal3_case_2_7_row_1_0_2
  · exact leftFinal3_case_2_7_row_1_0_3
  · exact leftFinal3_case_2_7_row_1_1_0
  · exact leftFinal3_case_2_7_row_1_1_1
  · exact leftFinal3_case_2_7_row_1_1_2
  · exact leftFinal3_case_2_7_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem leftFinal3_case_2_7 : ((-1 : ℤ) ^ (leftScaleBit 3 2 7).val * positiveScale (leftScaleExponent 3 2 7)) •
      (associatorZ 2 7 3 * left0Middle3 2 7) = negativeScale (leftScaleExponent 3 2 7) • (innerRightZ 2 3 7 * left1Middle3 2 7) := by
  simpa only [HexagonAtoms327.assocABC_eq,
    HexagonAtoms327.outerABC_eq,
    HexagonAtoms327.assocBAC_eq,
    HexagonAtoms327.innerABC_eq,
    HexagonAtoms327.innerRightABC_eq,
    HexagonAtoms327.inverseACB_eq,
    HexagonAtoms327.innerACB_eq,
    HexagonAtoms327.assocBCA_eq,
    HexagonAtoms327.innerRightBAC_eq,
    HexagonAtoms327.assocCAB_eq,
    HexagonAtoms327.outerLeftABC_eq,
    HexagonRowColumn327.product0_eq,
    HexagonRowColumn327.product1_eq,
    HexagonRowColumn327.product2_eq,
    HexagonRowColumn327.product3_eq,
    HexagonRowColumn327.product4_eq,
    HexagonRowColumn327.product5_eq,
    HexagonRowColumn327.product6_eq,
    HexagonRowColumn327.product7_eq] using leftFinal3_case_2_7_checked

private theorem rightFinal3_case_2_7_row_0_0_0 : (((-1 : ℤ) ^ (rightScaleBit 3 2 7).val * positiveScale (rightScaleExponent 3 2 7) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 7 2 : ℤ)) • HexagonAtoms327.outerLeftABC) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 3 2 7) • (rowColumnMul HexagonRowColumn327.rows_assocCAB HexagonRowColumn327.cols_right2)) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal3_case_2_7_row_0_0_1 : (((-1 : ℤ) ^ (rightScaleBit 3 2 7).val * positiveScale (rightScaleExponent 3 2 7) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 7 2 : ℤ)) • HexagonAtoms327.outerLeftABC) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 3 2 7) • (rowColumnMul HexagonRowColumn327.rows_assocCAB HexagonRowColumn327.cols_right2)) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal3_case_2_7_row_0_0_2 : (((-1 : ℤ) ^ (rightScaleBit 3 2 7).val * positiveScale (rightScaleExponent 3 2 7) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 7 2 : ℤ)) • HexagonAtoms327.outerLeftABC) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 3 2 7) • (rowColumnMul HexagonRowColumn327.rows_assocCAB HexagonRowColumn327.cols_right2)) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal3_case_2_7_row_0_0_3 : (((-1 : ℤ) ^ (rightScaleBit 3 2 7).val * positiveScale (rightScaleExponent 3 2 7) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 7 2 : ℤ)) • HexagonAtoms327.outerLeftABC) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 3 2 7) • (rowColumnMul HexagonRowColumn327.rows_assocCAB HexagonRowColumn327.cols_right2)) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal3_case_2_7_row_0_1_0 : (((-1 : ℤ) ^ (rightScaleBit 3 2 7).val * positiveScale (rightScaleExponent 3 2 7) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 7 2 : ℤ)) • HexagonAtoms327.outerLeftABC) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 3 2 7) • (rowColumnMul HexagonRowColumn327.rows_assocCAB HexagonRowColumn327.cols_right2)) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal3_case_2_7_row_0_1_1 : (((-1 : ℤ) ^ (rightScaleBit 3 2 7).val * positiveScale (rightScaleExponent 3 2 7) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 7 2 : ℤ)) • HexagonAtoms327.outerLeftABC) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 3 2 7) • (rowColumnMul HexagonRowColumn327.rows_assocCAB HexagonRowColumn327.cols_right2)) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal3_case_2_7_row_0_1_2 : (((-1 : ℤ) ^ (rightScaleBit 3 2 7).val * positiveScale (rightScaleExponent 3 2 7) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 7 2 : ℤ)) • HexagonAtoms327.outerLeftABC) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 3 2 7) • (rowColumnMul HexagonRowColumn327.rows_assocCAB HexagonRowColumn327.cols_right2)) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal3_case_2_7_row_0_1_3 : (((-1 : ℤ) ^ (rightScaleBit 3 2 7).val * positiveScale (rightScaleExponent 3 2 7) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 7 2 : ℤ)) • HexagonAtoms327.outerLeftABC) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 3 2 7) • (rowColumnMul HexagonRowColumn327.rows_assocCAB HexagonRowColumn327.cols_right2)) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal3_case_2_7_row_1_0_0 : (((-1 : ℤ) ^ (rightScaleBit 3 2 7).val * positiveScale (rightScaleExponent 3 2 7) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 7 2 : ℤ)) • HexagonAtoms327.outerLeftABC) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 3 2 7) • (rowColumnMul HexagonRowColumn327.rows_assocCAB HexagonRowColumn327.cols_right2)) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal3_case_2_7_row_1_0_1 : (((-1 : ℤ) ^ (rightScaleBit 3 2 7).val * positiveScale (rightScaleExponent 3 2 7) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 7 2 : ℤ)) • HexagonAtoms327.outerLeftABC) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 3 2 7) • (rowColumnMul HexagonRowColumn327.rows_assocCAB HexagonRowColumn327.cols_right2)) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal3_case_2_7_row_1_0_2 : (((-1 : ℤ) ^ (rightScaleBit 3 2 7).val * positiveScale (rightScaleExponent 3 2 7) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 7 2 : ℤ)) • HexagonAtoms327.outerLeftABC) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 3 2 7) • (rowColumnMul HexagonRowColumn327.rows_assocCAB HexagonRowColumn327.cols_right2)) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal3_case_2_7_row_1_0_3 : (((-1 : ℤ) ^ (rightScaleBit 3 2 7).val * positiveScale (rightScaleExponent 3 2 7) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 7 2 : ℤ)) • HexagonAtoms327.outerLeftABC) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 3 2 7) • (rowColumnMul HexagonRowColumn327.rows_assocCAB HexagonRowColumn327.cols_right2)) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal3_case_2_7_row_1_1_0 : (((-1 : ℤ) ^ (rightScaleBit 3 2 7).val * positiveScale (rightScaleExponent 3 2 7) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 7 2 : ℤ)) • HexagonAtoms327.outerLeftABC) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 3 2 7) • (rowColumnMul HexagonRowColumn327.rows_assocCAB HexagonRowColumn327.cols_right2)) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal3_case_2_7_row_1_1_1 : (((-1 : ℤ) ^ (rightScaleBit 3 2 7).val * positiveScale (rightScaleExponent 3 2 7) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 7 2 : ℤ)) • HexagonAtoms327.outerLeftABC) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 3 2 7) • (rowColumnMul HexagonRowColumn327.rows_assocCAB HexagonRowColumn327.cols_right2)) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal3_case_2_7_row_1_1_2 : (((-1 : ℤ) ^ (rightScaleBit 3 2 7).val * positiveScale (rightScaleExponent 3 2 7) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 7 2 : ℤ)) • HexagonAtoms327.outerLeftABC) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 3 2 7) • (rowColumnMul HexagonRowColumn327.rows_assocCAB HexagonRowColumn327.cols_right2)) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal3_case_2_7_row_1_1_3 : (((-1 : ℤ) ^ (rightScaleBit 3 2 7).val * positiveScale (rightScaleExponent 3 2 7) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 7 2 : ℤ)) • HexagonAtoms327.outerLeftABC) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 3 2 7) • (rowColumnMul HexagonRowColumn327.rows_assocCAB HexagonRowColumn327.cols_right2)) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal3_case_2_7_checked : ((-1 : ℤ) ^ (rightScaleBit 3 2 7).val * positiveScale (rightScaleExponent 3 2 7) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 7 2 : ℤ)) • HexagonAtoms327.outerLeftABC = negativeScale (rightScaleExponent 3 2 7) • (rowColumnMul HexagonRowColumn327.rows_assocCAB HexagonRowColumn327.cols_right2) := by
  funext r
  fin_cases r
  · exact rightFinal3_case_2_7_row_0_0_0
  · exact rightFinal3_case_2_7_row_0_0_1
  · exact rightFinal3_case_2_7_row_0_0_2
  · exact rightFinal3_case_2_7_row_0_0_3
  · exact rightFinal3_case_2_7_row_0_1_0
  · exact rightFinal3_case_2_7_row_0_1_1
  · exact rightFinal3_case_2_7_row_0_1_2
  · exact rightFinal3_case_2_7_row_0_1_3
  · exact rightFinal3_case_2_7_row_1_0_0
  · exact rightFinal3_case_2_7_row_1_0_1
  · exact rightFinal3_case_2_7_row_1_0_2
  · exact rightFinal3_case_2_7_row_1_0_3
  · exact rightFinal3_case_2_7_row_1_1_0
  · exact rightFinal3_case_2_7_row_1_1_1
  · exact rightFinal3_case_2_7_row_1_1_2
  · exact rightFinal3_case_2_7_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem rightFinal3_case_2_7 : ((-1 : ℤ) ^ (rightScaleBit 3 2 7).val * positiveScale (rightScaleExponent 3 2 7) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 7 2 : ℤ)) • outerLeftZ 3 2 7 = negativeScale (rightScaleExponent 3 2 7) • (associatorZ 7 3 2 * right2Middle3 2 7) := by
  simpa only [HexagonAtoms327.assocABC_eq,
    HexagonAtoms327.outerABC_eq,
    HexagonAtoms327.assocBAC_eq,
    HexagonAtoms327.innerABC_eq,
    HexagonAtoms327.innerRightABC_eq,
    HexagonAtoms327.inverseACB_eq,
    HexagonAtoms327.innerACB_eq,
    HexagonAtoms327.assocBCA_eq,
    HexagonAtoms327.innerRightBAC_eq,
    HexagonAtoms327.assocCAB_eq,
    HexagonAtoms327.outerLeftABC_eq,
    HexagonRowColumn327.product0_eq,
    HexagonRowColumn327.product1_eq,
    HexagonRowColumn327.product2_eq,
    HexagonRowColumn327.product3_eq,
    HexagonRowColumn327.product4_eq,
    HexagonRowColumn327.product5_eq,
    HexagonRowColumn327.product6_eq,
    HexagonRowColumn327.product7_eq] using rightFinal3_case_2_7_checked

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonCases3
