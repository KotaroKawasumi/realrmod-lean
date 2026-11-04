import RMod.BrundanEllis.StackingReferenceHexagonMiddle6
import RMod.BrundanEllis.StackingReferenceSparseMatrixCheck
import RMod.BrundanEllis.StackingReferenceHexagonAtoms663
import RMod.BrundanEllis.StackingReferenceHexagonRowColumn663

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

private theorem left0Middle6_eq_case_6_3_row_0_0_0 : (left0Middle6 6 3) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (HexagonAtoms663.assocABC) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle6_eq_case_6_3_row_0_0_1 : (left0Middle6 6 3) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (HexagonAtoms663.assocABC) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle6_eq_case_6_3_row_0_1_0 : (left0Middle6 6 3) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (HexagonAtoms663.assocABC) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle6_eq_case_6_3_row_0_1_1 : (left0Middle6 6 3) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (HexagonAtoms663.assocABC) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle6_eq_case_6_3_row_1_0_0 : (left0Middle6 6 3) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (HexagonAtoms663.assocABC) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle6_eq_case_6_3_row_1_0_1 : (left0Middle6 6 3) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (HexagonAtoms663.assocABC) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle6_eq_case_6_3_row_1_1_0 : (left0Middle6 6 3) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (HexagonAtoms663.assocABC) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle6_eq_case_6_3_row_1_1_1 : (left0Middle6 6 3) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (HexagonAtoms663.assocABC) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle6_eq_case_6_3_row_2_0_0 : (left0Middle6 6 3) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (HexagonAtoms663.assocABC) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle6_eq_case_6_3_row_2_0_1 : (left0Middle6 6 3) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (HexagonAtoms663.assocABC) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle6_eq_case_6_3_row_2_1_0 : (left0Middle6 6 3) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (HexagonAtoms663.assocABC) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle6_eq_case_6_3_row_2_1_1 : (left0Middle6 6 3) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (HexagonAtoms663.assocABC) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle6_eq_case_6_3_row_3_0_0 : (left0Middle6 6 3) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (HexagonAtoms663.assocABC) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle6_eq_case_6_3_row_3_0_1 : (left0Middle6 6 3) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (HexagonAtoms663.assocABC) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle6_eq_case_6_3_row_3_1_0 : (left0Middle6 6 3) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (HexagonAtoms663.assocABC) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle6_eq_case_6_3_row_3_1_1 : (left0Middle6 6 3) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (HexagonAtoms663.assocABC) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle6_eq_case_6_3_checked : left0Middle6 6 3 = HexagonAtoms663.assocABC := by
  funext r
  fin_cases r
  · exact left0Middle6_eq_case_6_3_row_0_0_0
  · exact left0Middle6_eq_case_6_3_row_0_0_1
  · exact left0Middle6_eq_case_6_3_row_0_1_0
  · exact left0Middle6_eq_case_6_3_row_0_1_1
  · exact left0Middle6_eq_case_6_3_row_1_0_0
  · exact left0Middle6_eq_case_6_3_row_1_0_1
  · exact left0Middle6_eq_case_6_3_row_1_1_0
  · exact left0Middle6_eq_case_6_3_row_1_1_1
  · exact left0Middle6_eq_case_6_3_row_2_0_0
  · exact left0Middle6_eq_case_6_3_row_2_0_1
  · exact left0Middle6_eq_case_6_3_row_2_1_0
  · exact left0Middle6_eq_case_6_3_row_2_1_1
  · exact left0Middle6_eq_case_6_3_row_3_0_0
  · exact left0Middle6_eq_case_6_3_row_3_0_1
  · exact left0Middle6_eq_case_6_3_row_3_1_0
  · exact left0Middle6_eq_case_6_3_row_3_1_1

set_option backward.isDefEq.respectTransparency false in
theorem left0Middle6_eq_case_6_3 : left0Middle6 6 3 = outerRightZ 6 6 3 * associatorZ 6 6 3 := by
  simpa only [HexagonAtoms663.assocABC_eq,
    HexagonAtoms663.outerABC_eq,
    HexagonAtoms663.assocBAC_eq,
    HexagonAtoms663.innerABC_eq,
    HexagonAtoms663.innerRightABC_eq,
    HexagonAtoms663.inverseACB_eq,
    HexagonAtoms663.innerACB_eq,
    HexagonAtoms663.assocBCA_eq,
    HexagonAtoms663.innerRightBAC_eq,
    HexagonAtoms663.assocCAB_eq,
    HexagonAtoms663.outerLeftABC_eq,
    HexagonRowColumn663.assocBAC_alias,
    HexagonRowColumn663.innerRightBAC_alias,
    HexagonRowColumn663.product0_eq,
    HexagonRowColumn663.product1_eq,
    HexagonRowColumn663.product2_eq,
    HexagonRowColumn663.product3_eq,
    HexagonRowColumn663.product4_eq,
    HexagonRowColumn663.product5_eq,
    HexagonRowColumn663.product6_eq,
    HexagonRowColumn663.product7_eq] using left0Middle6_eq_case_6_3_checked

private theorem left1Middle6_eq_case_6_3_row_0_0_0 : (left1Middle6 6 3) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn663.rows_assocABC HexagonRowColumn663.cols_innerABC) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle6_eq_case_6_3_row_0_0_1 : (left1Middle6 6 3) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn663.rows_assocABC HexagonRowColumn663.cols_innerABC) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle6_eq_case_6_3_row_0_1_0 : (left1Middle6 6 3) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn663.rows_assocABC HexagonRowColumn663.cols_innerABC) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle6_eq_case_6_3_row_0_1_1 : (left1Middle6 6 3) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn663.rows_assocABC HexagonRowColumn663.cols_innerABC) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle6_eq_case_6_3_row_1_0_0 : (left1Middle6 6 3) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn663.rows_assocABC HexagonRowColumn663.cols_innerABC) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle6_eq_case_6_3_row_1_0_1 : (left1Middle6 6 3) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn663.rows_assocABC HexagonRowColumn663.cols_innerABC) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle6_eq_case_6_3_row_1_1_0 : (left1Middle6 6 3) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn663.rows_assocABC HexagonRowColumn663.cols_innerABC) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle6_eq_case_6_3_row_1_1_1 : (left1Middle6 6 3) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn663.rows_assocABC HexagonRowColumn663.cols_innerABC) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle6_eq_case_6_3_row_2_0_0 : (left1Middle6 6 3) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn663.rows_assocABC HexagonRowColumn663.cols_innerABC) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle6_eq_case_6_3_row_2_0_1 : (left1Middle6 6 3) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn663.rows_assocABC HexagonRowColumn663.cols_innerABC) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle6_eq_case_6_3_row_2_1_0 : (left1Middle6 6 3) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn663.rows_assocABC HexagonRowColumn663.cols_innerABC) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle6_eq_case_6_3_row_2_1_1 : (left1Middle6 6 3) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn663.rows_assocABC HexagonRowColumn663.cols_innerABC) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle6_eq_case_6_3_row_3_0_0 : (left1Middle6 6 3) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn663.rows_assocABC HexagonRowColumn663.cols_innerABC) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle6_eq_case_6_3_row_3_0_1 : (left1Middle6 6 3) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn663.rows_assocABC HexagonRowColumn663.cols_innerABC) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle6_eq_case_6_3_row_3_1_0 : (left1Middle6 6 3) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn663.rows_assocABC HexagonRowColumn663.cols_innerABC) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle6_eq_case_6_3_row_3_1_1 : (left1Middle6 6 3) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn663.rows_assocABC HexagonRowColumn663.cols_innerABC) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle6_eq_case_6_3_checked : left1Middle6 6 3 = rowColumnMul HexagonRowColumn663.rows_assocABC HexagonRowColumn663.cols_innerABC := by
  funext r
  fin_cases r
  · exact left1Middle6_eq_case_6_3_row_0_0_0
  · exact left1Middle6_eq_case_6_3_row_0_0_1
  · exact left1Middle6_eq_case_6_3_row_0_1_0
  · exact left1Middle6_eq_case_6_3_row_0_1_1
  · exact left1Middle6_eq_case_6_3_row_1_0_0
  · exact left1Middle6_eq_case_6_3_row_1_0_1
  · exact left1Middle6_eq_case_6_3_row_1_1_0
  · exact left1Middle6_eq_case_6_3_row_1_1_1
  · exact left1Middle6_eq_case_6_3_row_2_0_0
  · exact left1Middle6_eq_case_6_3_row_2_0_1
  · exact left1Middle6_eq_case_6_3_row_2_1_0
  · exact left1Middle6_eq_case_6_3_row_2_1_1
  · exact left1Middle6_eq_case_6_3_row_3_0_0
  · exact left1Middle6_eq_case_6_3_row_3_0_1
  · exact left1Middle6_eq_case_6_3_row_3_1_0
  · exact left1Middle6_eq_case_6_3_row_3_1_1

set_option backward.isDefEq.respectTransparency false in
theorem left1Middle6_eq_case_6_3 : left1Middle6 6 3 = associatorZ 6 6 3 * innerLeftZ 6 6 3 := by
  simpa only [HexagonAtoms663.assocABC_eq,
    HexagonAtoms663.outerABC_eq,
    HexagonAtoms663.assocBAC_eq,
    HexagonAtoms663.innerABC_eq,
    HexagonAtoms663.innerRightABC_eq,
    HexagonAtoms663.inverseACB_eq,
    HexagonAtoms663.innerACB_eq,
    HexagonAtoms663.assocBCA_eq,
    HexagonAtoms663.innerRightBAC_eq,
    HexagonAtoms663.assocCAB_eq,
    HexagonAtoms663.outerLeftABC_eq,
    HexagonRowColumn663.assocBAC_alias,
    HexagonRowColumn663.innerRightBAC_alias,
    HexagonRowColumn663.product0_eq,
    HexagonRowColumn663.product1_eq,
    HexagonRowColumn663.product2_eq,
    HexagonRowColumn663.product3_eq,
    HexagonRowColumn663.product4_eq,
    HexagonRowColumn663.product5_eq,
    HexagonRowColumn663.product6_eq,
    HexagonRowColumn663.product7_eq] using left1Middle6_eq_case_6_3_checked

private theorem right0Middle6_eq_case_6_3_row_0_0_0 : (right0Middle6 6 3) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (HexagonAtoms663.assocABC) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle6_eq_case_6_3_row_0_0_1 : (right0Middle6 6 3) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (HexagonAtoms663.assocABC) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle6_eq_case_6_3_row_0_1_0 : (right0Middle6 6 3) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (HexagonAtoms663.assocABC) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle6_eq_case_6_3_row_0_1_1 : (right0Middle6 6 3) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (HexagonAtoms663.assocABC) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle6_eq_case_6_3_row_1_0_0 : (right0Middle6 6 3) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (HexagonAtoms663.assocABC) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle6_eq_case_6_3_row_1_0_1 : (right0Middle6 6 3) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (HexagonAtoms663.assocABC) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle6_eq_case_6_3_row_1_1_0 : (right0Middle6 6 3) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (HexagonAtoms663.assocABC) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle6_eq_case_6_3_row_1_1_1 : (right0Middle6 6 3) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (HexagonAtoms663.assocABC) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle6_eq_case_6_3_row_2_0_0 : (right0Middle6 6 3) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (HexagonAtoms663.assocABC) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle6_eq_case_6_3_row_2_0_1 : (right0Middle6 6 3) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (HexagonAtoms663.assocABC) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle6_eq_case_6_3_row_2_1_0 : (right0Middle6 6 3) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (HexagonAtoms663.assocABC) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle6_eq_case_6_3_row_2_1_1 : (right0Middle6 6 3) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (HexagonAtoms663.assocABC) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle6_eq_case_6_3_row_3_0_0 : (right0Middle6 6 3) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (HexagonAtoms663.assocABC) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle6_eq_case_6_3_row_3_0_1 : (right0Middle6 6 3) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (HexagonAtoms663.assocABC) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle6_eq_case_6_3_row_3_1_0 : (right0Middle6 6 3) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (HexagonAtoms663.assocABC) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle6_eq_case_6_3_row_3_1_1 : (right0Middle6 6 3) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (HexagonAtoms663.assocABC) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle6_eq_case_6_3_checked : right0Middle6 6 3 = HexagonAtoms663.assocABC := by
  funext r
  fin_cases r
  · exact right0Middle6_eq_case_6_3_row_0_0_0
  · exact right0Middle6_eq_case_6_3_row_0_0_1
  · exact right0Middle6_eq_case_6_3_row_0_1_0
  · exact right0Middle6_eq_case_6_3_row_0_1_1
  · exact right0Middle6_eq_case_6_3_row_1_0_0
  · exact right0Middle6_eq_case_6_3_row_1_0_1
  · exact right0Middle6_eq_case_6_3_row_1_1_0
  · exact right0Middle6_eq_case_6_3_row_1_1_1
  · exact right0Middle6_eq_case_6_3_row_2_0_0
  · exact right0Middle6_eq_case_6_3_row_2_0_1
  · exact right0Middle6_eq_case_6_3_row_2_1_0
  · exact right0Middle6_eq_case_6_3_row_2_1_1
  · exact right0Middle6_eq_case_6_3_row_3_0_0
  · exact right0Middle6_eq_case_6_3_row_3_0_1
  · exact right0Middle6_eq_case_6_3_row_3_1_0
  · exact right0Middle6_eq_case_6_3_row_3_1_1

set_option backward.isDefEq.respectTransparency false in
theorem right0Middle6_eq_case_6_3 : right0Middle6 6 3 = innerRightZ 6 6 3 * associatorZ 6 6 3 := by
  simpa only [HexagonAtoms663.assocABC_eq,
    HexagonAtoms663.outerABC_eq,
    HexagonAtoms663.assocBAC_eq,
    HexagonAtoms663.innerABC_eq,
    HexagonAtoms663.innerRightABC_eq,
    HexagonAtoms663.inverseACB_eq,
    HexagonAtoms663.innerACB_eq,
    HexagonAtoms663.assocBCA_eq,
    HexagonAtoms663.innerRightBAC_eq,
    HexagonAtoms663.assocCAB_eq,
    HexagonAtoms663.outerLeftABC_eq,
    HexagonRowColumn663.assocBAC_alias,
    HexagonRowColumn663.innerRightBAC_alias,
    HexagonRowColumn663.product0_eq,
    HexagonRowColumn663.product1_eq,
    HexagonRowColumn663.product2_eq,
    HexagonRowColumn663.product3_eq,
    HexagonRowColumn663.product4_eq,
    HexagonRowColumn663.product5_eq,
    HexagonRowColumn663.product6_eq,
    HexagonRowColumn663.product7_eq] using right0Middle6_eq_case_6_3_checked

private theorem right1Middle6_eq_case_6_3_row_0_0_0 : (right1Middle6 6 3) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn663.rows_inverseACB HexagonRowColumn663.cols_right0) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle6_eq_case_6_3_row_0_0_1 : (right1Middle6 6 3) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn663.rows_inverseACB HexagonRowColumn663.cols_right0) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle6_eq_case_6_3_row_0_1_0 : (right1Middle6 6 3) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn663.rows_inverseACB HexagonRowColumn663.cols_right0) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle6_eq_case_6_3_row_0_1_1 : (right1Middle6 6 3) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn663.rows_inverseACB HexagonRowColumn663.cols_right0) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle6_eq_case_6_3_row_1_0_0 : (right1Middle6 6 3) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn663.rows_inverseACB HexagonRowColumn663.cols_right0) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle6_eq_case_6_3_row_1_0_1 : (right1Middle6 6 3) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn663.rows_inverseACB HexagonRowColumn663.cols_right0) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle6_eq_case_6_3_row_1_1_0 : (right1Middle6 6 3) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn663.rows_inverseACB HexagonRowColumn663.cols_right0) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle6_eq_case_6_3_row_1_1_1 : (right1Middle6 6 3) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn663.rows_inverseACB HexagonRowColumn663.cols_right0) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle6_eq_case_6_3_row_2_0_0 : (right1Middle6 6 3) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn663.rows_inverseACB HexagonRowColumn663.cols_right0) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle6_eq_case_6_3_row_2_0_1 : (right1Middle6 6 3) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn663.rows_inverseACB HexagonRowColumn663.cols_right0) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle6_eq_case_6_3_row_2_1_0 : (right1Middle6 6 3) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn663.rows_inverseACB HexagonRowColumn663.cols_right0) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle6_eq_case_6_3_row_2_1_1 : (right1Middle6 6 3) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn663.rows_inverseACB HexagonRowColumn663.cols_right0) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle6_eq_case_6_3_row_3_0_0 : (right1Middle6 6 3) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn663.rows_inverseACB HexagonRowColumn663.cols_right0) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle6_eq_case_6_3_row_3_0_1 : (right1Middle6 6 3) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn663.rows_inverseACB HexagonRowColumn663.cols_right0) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle6_eq_case_6_3_row_3_1_0 : (right1Middle6 6 3) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn663.rows_inverseACB HexagonRowColumn663.cols_right0) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle6_eq_case_6_3_row_3_1_1 : (right1Middle6 6 3) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn663.rows_inverseACB HexagonRowColumn663.cols_right0) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle6_eq_case_6_3_checked : right1Middle6 6 3 = rowColumnMul HexagonRowColumn663.rows_inverseACB HexagonRowColumn663.cols_right0 := by
  funext r
  fin_cases r
  · exact right1Middle6_eq_case_6_3_row_0_0_0
  · exact right1Middle6_eq_case_6_3_row_0_0_1
  · exact right1Middle6_eq_case_6_3_row_0_1_0
  · exact right1Middle6_eq_case_6_3_row_0_1_1
  · exact right1Middle6_eq_case_6_3_row_1_0_0
  · exact right1Middle6_eq_case_6_3_row_1_0_1
  · exact right1Middle6_eq_case_6_3_row_1_1_0
  · exact right1Middle6_eq_case_6_3_row_1_1_1
  · exact right1Middle6_eq_case_6_3_row_2_0_0
  · exact right1Middle6_eq_case_6_3_row_2_0_1
  · exact right1Middle6_eq_case_6_3_row_2_1_0
  · exact right1Middle6_eq_case_6_3_row_2_1_1
  · exact right1Middle6_eq_case_6_3_row_3_0_0
  · exact right1Middle6_eq_case_6_3_row_3_0_1
  · exact right1Middle6_eq_case_6_3_row_3_1_0
  · exact right1Middle6_eq_case_6_3_row_3_1_1

set_option backward.isDefEq.respectTransparency false in
theorem right1Middle6_eq_case_6_3 : right1Middle6 6 3 = associatorInverseZ 6 3 6 * right0Middle6 6 3 := by
  simpa only [HexagonAtoms663.assocABC_eq,
    HexagonAtoms663.outerABC_eq,
    HexagonAtoms663.assocBAC_eq,
    HexagonAtoms663.innerABC_eq,
    HexagonAtoms663.innerRightABC_eq,
    HexagonAtoms663.inverseACB_eq,
    HexagonAtoms663.innerACB_eq,
    HexagonAtoms663.assocBCA_eq,
    HexagonAtoms663.innerRightBAC_eq,
    HexagonAtoms663.assocCAB_eq,
    HexagonAtoms663.outerLeftABC_eq,
    HexagonRowColumn663.assocBAC_alias,
    HexagonRowColumn663.innerRightBAC_alias,
    HexagonRowColumn663.product0_eq,
    HexagonRowColumn663.product1_eq,
    HexagonRowColumn663.product2_eq,
    HexagonRowColumn663.product3_eq,
    HexagonRowColumn663.product4_eq,
    HexagonRowColumn663.product5_eq,
    HexagonRowColumn663.product6_eq,
    HexagonRowColumn663.product7_eq] using right1Middle6_eq_case_6_3_checked

private theorem right2Middle6_eq_case_6_3_row_0_0_0 : (right2Middle6 6 3) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (right1Middle6 6 3) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle6_eq_case_6_3_row_0_0_1 : (right2Middle6 6 3) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (right1Middle6 6 3) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle6_eq_case_6_3_row_0_1_0 : (right2Middle6 6 3) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (right1Middle6 6 3) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle6_eq_case_6_3_row_0_1_1 : (right2Middle6 6 3) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (right1Middle6 6 3) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle6_eq_case_6_3_row_1_0_0 : (right2Middle6 6 3) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (right1Middle6 6 3) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle6_eq_case_6_3_row_1_0_1 : (right2Middle6 6 3) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (right1Middle6 6 3) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle6_eq_case_6_3_row_1_1_0 : (right2Middle6 6 3) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (right1Middle6 6 3) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle6_eq_case_6_3_row_1_1_1 : (right2Middle6 6 3) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (right1Middle6 6 3) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle6_eq_case_6_3_row_2_0_0 : (right2Middle6 6 3) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (right1Middle6 6 3) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle6_eq_case_6_3_row_2_0_1 : (right2Middle6 6 3) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (right1Middle6 6 3) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle6_eq_case_6_3_row_2_1_0 : (right2Middle6 6 3) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (right1Middle6 6 3) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle6_eq_case_6_3_row_2_1_1 : (right2Middle6 6 3) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (right1Middle6 6 3) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle6_eq_case_6_3_row_3_0_0 : (right2Middle6 6 3) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (right1Middle6 6 3) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle6_eq_case_6_3_row_3_0_1 : (right2Middle6 6 3) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (right1Middle6 6 3) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle6_eq_case_6_3_row_3_1_0 : (right2Middle6 6 3) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (right1Middle6 6 3) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle6_eq_case_6_3_row_3_1_1 : (right2Middle6 6 3) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (right1Middle6 6 3) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle6_eq_case_6_3_checked : right2Middle6 6 3 = right1Middle6 6 3 := by
  funext r
  fin_cases r
  · exact right2Middle6_eq_case_6_3_row_0_0_0
  · exact right2Middle6_eq_case_6_3_row_0_0_1
  · exact right2Middle6_eq_case_6_3_row_0_1_0
  · exact right2Middle6_eq_case_6_3_row_0_1_1
  · exact right2Middle6_eq_case_6_3_row_1_0_0
  · exact right2Middle6_eq_case_6_3_row_1_0_1
  · exact right2Middle6_eq_case_6_3_row_1_1_0
  · exact right2Middle6_eq_case_6_3_row_1_1_1
  · exact right2Middle6_eq_case_6_3_row_2_0_0
  · exact right2Middle6_eq_case_6_3_row_2_0_1
  · exact right2Middle6_eq_case_6_3_row_2_1_0
  · exact right2Middle6_eq_case_6_3_row_2_1_1
  · exact right2Middle6_eq_case_6_3_row_3_0_0
  · exact right2Middle6_eq_case_6_3_row_3_0_1
  · exact right2Middle6_eq_case_6_3_row_3_1_0
  · exact right2Middle6_eq_case_6_3_row_3_1_1

set_option backward.isDefEq.respectTransparency false in
theorem right2Middle6_eq_case_6_3 : right2Middle6 6 3 = innerLeftZ 6 3 6 * right1Middle6 6 3 := by
  simpa only [HexagonAtoms663.assocABC_eq,
    HexagonAtoms663.outerABC_eq,
    HexagonAtoms663.assocBAC_eq,
    HexagonAtoms663.innerABC_eq,
    HexagonAtoms663.innerRightABC_eq,
    HexagonAtoms663.inverseACB_eq,
    HexagonAtoms663.innerACB_eq,
    HexagonAtoms663.assocBCA_eq,
    HexagonAtoms663.innerRightBAC_eq,
    HexagonAtoms663.assocCAB_eq,
    HexagonAtoms663.outerLeftABC_eq,
    HexagonRowColumn663.assocBAC_alias,
    HexagonRowColumn663.innerRightBAC_alias,
    HexagonRowColumn663.product0_eq,
    HexagonRowColumn663.product1_eq,
    HexagonRowColumn663.product2_eq,
    HexagonRowColumn663.product3_eq,
    HexagonRowColumn663.product4_eq,
    HexagonRowColumn663.product5_eq,
    HexagonRowColumn663.product6_eq,
    HexagonRowColumn663.product7_eq] using right2Middle6_eq_case_6_3_checked

private theorem leftFinal6_case_6_3_row_0_0_0 : (((-1 : ℤ) ^ (leftScaleBit 6 6 3).val * positiveScale (leftScaleExponent 6 6 3)) •
      (rowColumnMul HexagonRowColumn663.rows_assocBCA HexagonRowColumn663.cols_left0)) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (negativeScale (leftScaleExponent 6 6 3) • (left1Middle6 6 3)) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal6_case_6_3_row_0_0_1 : (((-1 : ℤ) ^ (leftScaleBit 6 6 3).val * positiveScale (leftScaleExponent 6 6 3)) •
      (rowColumnMul HexagonRowColumn663.rows_assocBCA HexagonRowColumn663.cols_left0)) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (negativeScale (leftScaleExponent 6 6 3) • (left1Middle6 6 3)) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal6_case_6_3_row_0_1_0 : (((-1 : ℤ) ^ (leftScaleBit 6 6 3).val * positiveScale (leftScaleExponent 6 6 3)) •
      (rowColumnMul HexagonRowColumn663.rows_assocBCA HexagonRowColumn663.cols_left0)) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (negativeScale (leftScaleExponent 6 6 3) • (left1Middle6 6 3)) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal6_case_6_3_row_0_1_1 : (((-1 : ℤ) ^ (leftScaleBit 6 6 3).val * positiveScale (leftScaleExponent 6 6 3)) •
      (rowColumnMul HexagonRowColumn663.rows_assocBCA HexagonRowColumn663.cols_left0)) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (negativeScale (leftScaleExponent 6 6 3) • (left1Middle6 6 3)) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal6_case_6_3_row_1_0_0 : (((-1 : ℤ) ^ (leftScaleBit 6 6 3).val * positiveScale (leftScaleExponent 6 6 3)) •
      (rowColumnMul HexagonRowColumn663.rows_assocBCA HexagonRowColumn663.cols_left0)) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (negativeScale (leftScaleExponent 6 6 3) • (left1Middle6 6 3)) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal6_case_6_3_row_1_0_1 : (((-1 : ℤ) ^ (leftScaleBit 6 6 3).val * positiveScale (leftScaleExponent 6 6 3)) •
      (rowColumnMul HexagonRowColumn663.rows_assocBCA HexagonRowColumn663.cols_left0)) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (negativeScale (leftScaleExponent 6 6 3) • (left1Middle6 6 3)) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal6_case_6_3_row_1_1_0 : (((-1 : ℤ) ^ (leftScaleBit 6 6 3).val * positiveScale (leftScaleExponent 6 6 3)) •
      (rowColumnMul HexagonRowColumn663.rows_assocBCA HexagonRowColumn663.cols_left0)) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (negativeScale (leftScaleExponent 6 6 3) • (left1Middle6 6 3)) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal6_case_6_3_row_1_1_1 : (((-1 : ℤ) ^ (leftScaleBit 6 6 3).val * positiveScale (leftScaleExponent 6 6 3)) •
      (rowColumnMul HexagonRowColumn663.rows_assocBCA HexagonRowColumn663.cols_left0)) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (negativeScale (leftScaleExponent 6 6 3) • (left1Middle6 6 3)) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal6_case_6_3_row_2_0_0 : (((-1 : ℤ) ^ (leftScaleBit 6 6 3).val * positiveScale (leftScaleExponent 6 6 3)) •
      (rowColumnMul HexagonRowColumn663.rows_assocBCA HexagonRowColumn663.cols_left0)) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (negativeScale (leftScaleExponent 6 6 3) • (left1Middle6 6 3)) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal6_case_6_3_row_2_0_1 : (((-1 : ℤ) ^ (leftScaleBit 6 6 3).val * positiveScale (leftScaleExponent 6 6 3)) •
      (rowColumnMul HexagonRowColumn663.rows_assocBCA HexagonRowColumn663.cols_left0)) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (negativeScale (leftScaleExponent 6 6 3) • (left1Middle6 6 3)) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal6_case_6_3_row_2_1_0 : (((-1 : ℤ) ^ (leftScaleBit 6 6 3).val * positiveScale (leftScaleExponent 6 6 3)) •
      (rowColumnMul HexagonRowColumn663.rows_assocBCA HexagonRowColumn663.cols_left0)) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (negativeScale (leftScaleExponent 6 6 3) • (left1Middle6 6 3)) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal6_case_6_3_row_2_1_1 : (((-1 : ℤ) ^ (leftScaleBit 6 6 3).val * positiveScale (leftScaleExponent 6 6 3)) •
      (rowColumnMul HexagonRowColumn663.rows_assocBCA HexagonRowColumn663.cols_left0)) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (negativeScale (leftScaleExponent 6 6 3) • (left1Middle6 6 3)) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal6_case_6_3_row_3_0_0 : (((-1 : ℤ) ^ (leftScaleBit 6 6 3).val * positiveScale (leftScaleExponent 6 6 3)) •
      (rowColumnMul HexagonRowColumn663.rows_assocBCA HexagonRowColumn663.cols_left0)) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (negativeScale (leftScaleExponent 6 6 3) • (left1Middle6 6 3)) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal6_case_6_3_row_3_0_1 : (((-1 : ℤ) ^ (leftScaleBit 6 6 3).val * positiveScale (leftScaleExponent 6 6 3)) •
      (rowColumnMul HexagonRowColumn663.rows_assocBCA HexagonRowColumn663.cols_left0)) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (negativeScale (leftScaleExponent 6 6 3) • (left1Middle6 6 3)) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal6_case_6_3_row_3_1_0 : (((-1 : ℤ) ^ (leftScaleBit 6 6 3).val * positiveScale (leftScaleExponent 6 6 3)) •
      (rowColumnMul HexagonRowColumn663.rows_assocBCA HexagonRowColumn663.cols_left0)) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (negativeScale (leftScaleExponent 6 6 3) • (left1Middle6 6 3)) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal6_case_6_3_row_3_1_1 : (((-1 : ℤ) ^ (leftScaleBit 6 6 3).val * positiveScale (leftScaleExponent 6 6 3)) •
      (rowColumnMul HexagonRowColumn663.rows_assocBCA HexagonRowColumn663.cols_left0)) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (negativeScale (leftScaleExponent 6 6 3) • (left1Middle6 6 3)) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal6_case_6_3_checked : ((-1 : ℤ) ^ (leftScaleBit 6 6 3).val * positiveScale (leftScaleExponent 6 6 3)) •
      (rowColumnMul HexagonRowColumn663.rows_assocBCA HexagonRowColumn663.cols_left0) = negativeScale (leftScaleExponent 6 6 3) • (left1Middle6 6 3) := by
  funext r
  fin_cases r
  · exact leftFinal6_case_6_3_row_0_0_0
  · exact leftFinal6_case_6_3_row_0_0_1
  · exact leftFinal6_case_6_3_row_0_1_0
  · exact leftFinal6_case_6_3_row_0_1_1
  · exact leftFinal6_case_6_3_row_1_0_0
  · exact leftFinal6_case_6_3_row_1_0_1
  · exact leftFinal6_case_6_3_row_1_1_0
  · exact leftFinal6_case_6_3_row_1_1_1
  · exact leftFinal6_case_6_3_row_2_0_0
  · exact leftFinal6_case_6_3_row_2_0_1
  · exact leftFinal6_case_6_3_row_2_1_0
  · exact leftFinal6_case_6_3_row_2_1_1
  · exact leftFinal6_case_6_3_row_3_0_0
  · exact leftFinal6_case_6_3_row_3_0_1
  · exact leftFinal6_case_6_3_row_3_1_0
  · exact leftFinal6_case_6_3_row_3_1_1

set_option backward.isDefEq.respectTransparency false in
theorem leftFinal6_case_6_3 : ((-1 : ℤ) ^ (leftScaleBit 6 6 3).val * positiveScale (leftScaleExponent 6 6 3)) •
      (associatorZ 6 3 6 * left0Middle6 6 3) = negativeScale (leftScaleExponent 6 6 3) • (innerRightZ 6 6 3 * left1Middle6 6 3) := by
  simpa only [HexagonAtoms663.assocABC_eq,
    HexagonAtoms663.outerABC_eq,
    HexagonAtoms663.assocBAC_eq,
    HexagonAtoms663.innerABC_eq,
    HexagonAtoms663.innerRightABC_eq,
    HexagonAtoms663.inverseACB_eq,
    HexagonAtoms663.innerACB_eq,
    HexagonAtoms663.assocBCA_eq,
    HexagonAtoms663.innerRightBAC_eq,
    HexagonAtoms663.assocCAB_eq,
    HexagonAtoms663.outerLeftABC_eq,
    HexagonRowColumn663.assocBAC_alias,
    HexagonRowColumn663.innerRightBAC_alias,
    HexagonRowColumn663.product0_eq,
    HexagonRowColumn663.product1_eq,
    HexagonRowColumn663.product2_eq,
    HexagonRowColumn663.product3_eq,
    HexagonRowColumn663.product4_eq,
    HexagonRowColumn663.product5_eq,
    HexagonRowColumn663.product6_eq,
    HexagonRowColumn663.product7_eq] using leftFinal6_case_6_3_checked

private theorem rightFinal6_case_6_3_row_0_0_0 : (((-1 : ℤ) ^ (rightScaleBit 6 6 3).val * positiveScale (rightScaleExponent 6 6 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 3 6 : ℤ)) • HexagonAtoms663.outerLeftABC) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (negativeScale (rightScaleExponent 6 6 3) • (rowColumnMul HexagonRowColumn663.rows_assocCAB HexagonRowColumn663.cols_right2)) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal6_case_6_3_row_0_0_1 : (((-1 : ℤ) ^ (rightScaleBit 6 6 3).val * positiveScale (rightScaleExponent 6 6 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 3 6 : ℤ)) • HexagonAtoms663.outerLeftABC) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (negativeScale (rightScaleExponent 6 6 3) • (rowColumnMul HexagonRowColumn663.rows_assocCAB HexagonRowColumn663.cols_right2)) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal6_case_6_3_row_0_1_0 : (((-1 : ℤ) ^ (rightScaleBit 6 6 3).val * positiveScale (rightScaleExponent 6 6 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 3 6 : ℤ)) • HexagonAtoms663.outerLeftABC) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (negativeScale (rightScaleExponent 6 6 3) • (rowColumnMul HexagonRowColumn663.rows_assocCAB HexagonRowColumn663.cols_right2)) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal6_case_6_3_row_0_1_1 : (((-1 : ℤ) ^ (rightScaleBit 6 6 3).val * positiveScale (rightScaleExponent 6 6 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 3 6 : ℤ)) • HexagonAtoms663.outerLeftABC) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (negativeScale (rightScaleExponent 6 6 3) • (rowColumnMul HexagonRowColumn663.rows_assocCAB HexagonRowColumn663.cols_right2)) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal6_case_6_3_row_0_2_0 : (((-1 : ℤ) ^ (rightScaleBit 6 6 3).val * positiveScale (rightScaleExponent 6 6 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 3 6 : ℤ)) • HexagonAtoms663.outerLeftABC) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (negativeScale (rightScaleExponent 6 6 3) • (rowColumnMul HexagonRowColumn663.rows_assocCAB HexagonRowColumn663.cols_right2)) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal6_case_6_3_row_0_2_1 : (((-1 : ℤ) ^ (rightScaleBit 6 6 3).val * positiveScale (rightScaleExponent 6 6 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 3 6 : ℤ)) • HexagonAtoms663.outerLeftABC) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (negativeScale (rightScaleExponent 6 6 3) • (rowColumnMul HexagonRowColumn663.rows_assocCAB HexagonRowColumn663.cols_right2)) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal6_case_6_3_row_0_3_0 : (((-1 : ℤ) ^ (rightScaleBit 6 6 3).val * positiveScale (rightScaleExponent 6 6 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 3 6 : ℤ)) • HexagonAtoms663.outerLeftABC) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (negativeScale (rightScaleExponent 6 6 3) • (rowColumnMul HexagonRowColumn663.rows_assocCAB HexagonRowColumn663.cols_right2)) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal6_case_6_3_row_0_3_1 : (((-1 : ℤ) ^ (rightScaleBit 6 6 3).val * positiveScale (rightScaleExponent 6 6 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 3 6 : ℤ)) • HexagonAtoms663.outerLeftABC) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (negativeScale (rightScaleExponent 6 6 3) • (rowColumnMul HexagonRowColumn663.rows_assocCAB HexagonRowColumn663.cols_right2)) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal6_case_6_3_row_1_0_0 : (((-1 : ℤ) ^ (rightScaleBit 6 6 3).val * positiveScale (rightScaleExponent 6 6 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 3 6 : ℤ)) • HexagonAtoms663.outerLeftABC) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (negativeScale (rightScaleExponent 6 6 3) • (rowColumnMul HexagonRowColumn663.rows_assocCAB HexagonRowColumn663.cols_right2)) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal6_case_6_3_row_1_0_1 : (((-1 : ℤ) ^ (rightScaleBit 6 6 3).val * positiveScale (rightScaleExponent 6 6 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 3 6 : ℤ)) • HexagonAtoms663.outerLeftABC) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (negativeScale (rightScaleExponent 6 6 3) • (rowColumnMul HexagonRowColumn663.rows_assocCAB HexagonRowColumn663.cols_right2)) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal6_case_6_3_row_1_1_0 : (((-1 : ℤ) ^ (rightScaleBit 6 6 3).val * positiveScale (rightScaleExponent 6 6 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 3 6 : ℤ)) • HexagonAtoms663.outerLeftABC) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (negativeScale (rightScaleExponent 6 6 3) • (rowColumnMul HexagonRowColumn663.rows_assocCAB HexagonRowColumn663.cols_right2)) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal6_case_6_3_row_1_1_1 : (((-1 : ℤ) ^ (rightScaleBit 6 6 3).val * positiveScale (rightScaleExponent 6 6 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 3 6 : ℤ)) • HexagonAtoms663.outerLeftABC) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (negativeScale (rightScaleExponent 6 6 3) • (rowColumnMul HexagonRowColumn663.rows_assocCAB HexagonRowColumn663.cols_right2)) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal6_case_6_3_row_1_2_0 : (((-1 : ℤ) ^ (rightScaleBit 6 6 3).val * positiveScale (rightScaleExponent 6 6 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 3 6 : ℤ)) • HexagonAtoms663.outerLeftABC) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (negativeScale (rightScaleExponent 6 6 3) • (rowColumnMul HexagonRowColumn663.rows_assocCAB HexagonRowColumn663.cols_right2)) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal6_case_6_3_row_1_2_1 : (((-1 : ℤ) ^ (rightScaleBit 6 6 3).val * positiveScale (rightScaleExponent 6 6 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 3 6 : ℤ)) • HexagonAtoms663.outerLeftABC) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (negativeScale (rightScaleExponent 6 6 3) • (rowColumnMul HexagonRowColumn663.rows_assocCAB HexagonRowColumn663.cols_right2)) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal6_case_6_3_row_1_3_0 : (((-1 : ℤ) ^ (rightScaleBit 6 6 3).val * positiveScale (rightScaleExponent 6 6 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 3 6 : ℤ)) • HexagonAtoms663.outerLeftABC) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (negativeScale (rightScaleExponent 6 6 3) • (rowColumnMul HexagonRowColumn663.rows_assocCAB HexagonRowColumn663.cols_right2)) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal6_case_6_3_row_1_3_1 : (((-1 : ℤ) ^ (rightScaleBit 6 6 3).val * positiveScale (rightScaleExponent 6 6 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 3 6 : ℤ)) • HexagonAtoms663.outerLeftABC) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (negativeScale (rightScaleExponent 6 6 3) • (rowColumnMul HexagonRowColumn663.rows_assocCAB HexagonRowColumn663.cols_right2)) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal6_case_6_3_checked : ((-1 : ℤ) ^ (rightScaleBit 6 6 3).val * positiveScale (rightScaleExponent 6 6 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 3 6 : ℤ)) • HexagonAtoms663.outerLeftABC = negativeScale (rightScaleExponent 6 6 3) • (rowColumnMul HexagonRowColumn663.rows_assocCAB HexagonRowColumn663.cols_right2) := by
  funext r
  fin_cases r
  · exact rightFinal6_case_6_3_row_0_0_0
  · exact rightFinal6_case_6_3_row_0_0_1
  · exact rightFinal6_case_6_3_row_0_1_0
  · exact rightFinal6_case_6_3_row_0_1_1
  · exact rightFinal6_case_6_3_row_0_2_0
  · exact rightFinal6_case_6_3_row_0_2_1
  · exact rightFinal6_case_6_3_row_0_3_0
  · exact rightFinal6_case_6_3_row_0_3_1
  · exact rightFinal6_case_6_3_row_1_0_0
  · exact rightFinal6_case_6_3_row_1_0_1
  · exact rightFinal6_case_6_3_row_1_1_0
  · exact rightFinal6_case_6_3_row_1_1_1
  · exact rightFinal6_case_6_3_row_1_2_0
  · exact rightFinal6_case_6_3_row_1_2_1
  · exact rightFinal6_case_6_3_row_1_3_0
  · exact rightFinal6_case_6_3_row_1_3_1

set_option backward.isDefEq.respectTransparency false in
theorem rightFinal6_case_6_3 : ((-1 : ℤ) ^ (rightScaleBit 6 6 3).val * positiveScale (rightScaleExponent 6 6 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 3 6 : ℤ)) • outerLeftZ 6 6 3 = negativeScale (rightScaleExponent 6 6 3) • (associatorZ 3 6 6 * right2Middle6 6 3) := by
  simpa only [HexagonAtoms663.assocABC_eq,
    HexagonAtoms663.outerABC_eq,
    HexagonAtoms663.assocBAC_eq,
    HexagonAtoms663.innerABC_eq,
    HexagonAtoms663.innerRightABC_eq,
    HexagonAtoms663.inverseACB_eq,
    HexagonAtoms663.innerACB_eq,
    HexagonAtoms663.assocBCA_eq,
    HexagonAtoms663.innerRightBAC_eq,
    HexagonAtoms663.assocCAB_eq,
    HexagonAtoms663.outerLeftABC_eq,
    HexagonRowColumn663.assocBAC_alias,
    HexagonRowColumn663.innerRightBAC_alias,
    HexagonRowColumn663.product0_eq,
    HexagonRowColumn663.product1_eq,
    HexagonRowColumn663.product2_eq,
    HexagonRowColumn663.product3_eq,
    HexagonRowColumn663.product4_eq,
    HexagonRowColumn663.product5_eq,
    HexagonRowColumn663.product6_eq,
    HexagonRowColumn663.product7_eq] using rightFinal6_case_6_3_checked

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonCases6
