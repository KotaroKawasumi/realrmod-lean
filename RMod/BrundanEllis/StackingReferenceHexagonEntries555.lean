import RMod.BrundanEllis.StackingReferenceHexagonMiddle5
import RMod.BrundanEllis.StackingReferenceSparseMatrixCheck
import RMod.BrundanEllis.StackingReferenceHexagonAtoms555
import RMod.BrundanEllis.StackingReferenceHexagonRowColumn555

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

private theorem left0Middle5_eq_case_5_5_row_0_0_0 : (left0Middle5 5 5) ((0 : Fin 4), (0 : Fin 4), (0 : Fin 2)) = (HexagonAtoms555.assocABC) ((0 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_5_5_row_0_0_1 : (left0Middle5 5 5) ((0 : Fin 4), (0 : Fin 4), (1 : Fin 2)) = (HexagonAtoms555.assocABC) ((0 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_5_5_row_0_1_0 : (left0Middle5 5 5) ((0 : Fin 4), (1 : Fin 4), (0 : Fin 2)) = (HexagonAtoms555.assocABC) ((0 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_5_5_row_0_1_1 : (left0Middle5 5 5) ((0 : Fin 4), (1 : Fin 4), (1 : Fin 2)) = (HexagonAtoms555.assocABC) ((0 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_5_5_row_0_2_0 : (left0Middle5 5 5) ((0 : Fin 4), (2 : Fin 4), (0 : Fin 2)) = (HexagonAtoms555.assocABC) ((0 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_5_5_row_0_2_1 : (left0Middle5 5 5) ((0 : Fin 4), (2 : Fin 4), (1 : Fin 2)) = (HexagonAtoms555.assocABC) ((0 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_5_5_row_0_3_0 : (left0Middle5 5 5) ((0 : Fin 4), (3 : Fin 4), (0 : Fin 2)) = (HexagonAtoms555.assocABC) ((0 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_5_5_row_0_3_1 : (left0Middle5 5 5) ((0 : Fin 4), (3 : Fin 4), (1 : Fin 2)) = (HexagonAtoms555.assocABC) ((0 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_5_5_row_1_0_0 : (left0Middle5 5 5) ((1 : Fin 4), (0 : Fin 4), (0 : Fin 2)) = (HexagonAtoms555.assocABC) ((1 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_5_5_row_1_0_1 : (left0Middle5 5 5) ((1 : Fin 4), (0 : Fin 4), (1 : Fin 2)) = (HexagonAtoms555.assocABC) ((1 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_5_5_row_1_1_0 : (left0Middle5 5 5) ((1 : Fin 4), (1 : Fin 4), (0 : Fin 2)) = (HexagonAtoms555.assocABC) ((1 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_5_5_row_1_1_1 : (left0Middle5 5 5) ((1 : Fin 4), (1 : Fin 4), (1 : Fin 2)) = (HexagonAtoms555.assocABC) ((1 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_5_5_row_1_2_0 : (left0Middle5 5 5) ((1 : Fin 4), (2 : Fin 4), (0 : Fin 2)) = (HexagonAtoms555.assocABC) ((1 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_5_5_row_1_2_1 : (left0Middle5 5 5) ((1 : Fin 4), (2 : Fin 4), (1 : Fin 2)) = (HexagonAtoms555.assocABC) ((1 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_5_5_row_1_3_0 : (left0Middle5 5 5) ((1 : Fin 4), (3 : Fin 4), (0 : Fin 2)) = (HexagonAtoms555.assocABC) ((1 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_5_5_row_1_3_1 : (left0Middle5 5 5) ((1 : Fin 4), (3 : Fin 4), (1 : Fin 2)) = (HexagonAtoms555.assocABC) ((1 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_5_5_row_2_0_0 : (left0Middle5 5 5) ((2 : Fin 4), (0 : Fin 4), (0 : Fin 2)) = (HexagonAtoms555.assocABC) ((2 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_5_5_row_2_0_1 : (left0Middle5 5 5) ((2 : Fin 4), (0 : Fin 4), (1 : Fin 2)) = (HexagonAtoms555.assocABC) ((2 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_5_5_row_2_1_0 : (left0Middle5 5 5) ((2 : Fin 4), (1 : Fin 4), (0 : Fin 2)) = (HexagonAtoms555.assocABC) ((2 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_5_5_row_2_1_1 : (left0Middle5 5 5) ((2 : Fin 4), (1 : Fin 4), (1 : Fin 2)) = (HexagonAtoms555.assocABC) ((2 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_5_5_row_2_2_0 : (left0Middle5 5 5) ((2 : Fin 4), (2 : Fin 4), (0 : Fin 2)) = (HexagonAtoms555.assocABC) ((2 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_5_5_row_2_2_1 : (left0Middle5 5 5) ((2 : Fin 4), (2 : Fin 4), (1 : Fin 2)) = (HexagonAtoms555.assocABC) ((2 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_5_5_row_2_3_0 : (left0Middle5 5 5) ((2 : Fin 4), (3 : Fin 4), (0 : Fin 2)) = (HexagonAtoms555.assocABC) ((2 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_5_5_row_2_3_1 : (left0Middle5 5 5) ((2 : Fin 4), (3 : Fin 4), (1 : Fin 2)) = (HexagonAtoms555.assocABC) ((2 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_5_5_row_3_0_0 : (left0Middle5 5 5) ((3 : Fin 4), (0 : Fin 4), (0 : Fin 2)) = (HexagonAtoms555.assocABC) ((3 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_5_5_row_3_0_1 : (left0Middle5 5 5) ((3 : Fin 4), (0 : Fin 4), (1 : Fin 2)) = (HexagonAtoms555.assocABC) ((3 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_5_5_row_3_1_0 : (left0Middle5 5 5) ((3 : Fin 4), (1 : Fin 4), (0 : Fin 2)) = (HexagonAtoms555.assocABC) ((3 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_5_5_row_3_1_1 : (left0Middle5 5 5) ((3 : Fin 4), (1 : Fin 4), (1 : Fin 2)) = (HexagonAtoms555.assocABC) ((3 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_5_5_row_3_2_0 : (left0Middle5 5 5) ((3 : Fin 4), (2 : Fin 4), (0 : Fin 2)) = (HexagonAtoms555.assocABC) ((3 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_5_5_row_3_2_1 : (left0Middle5 5 5) ((3 : Fin 4), (2 : Fin 4), (1 : Fin 2)) = (HexagonAtoms555.assocABC) ((3 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_5_5_row_3_3_0 : (left0Middle5 5 5) ((3 : Fin 4), (3 : Fin 4), (0 : Fin 2)) = (HexagonAtoms555.assocABC) ((3 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_5_5_row_3_3_1 : (left0Middle5 5 5) ((3 : Fin 4), (3 : Fin 4), (1 : Fin 2)) = (HexagonAtoms555.assocABC) ((3 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_5_5_checked : left0Middle5 5 5 = HexagonAtoms555.assocABC := by
  funext r
  fin_cases r
  · exact left0Middle5_eq_case_5_5_row_0_0_0
  · exact left0Middle5_eq_case_5_5_row_0_0_1
  · exact left0Middle5_eq_case_5_5_row_0_1_0
  · exact left0Middle5_eq_case_5_5_row_0_1_1
  · exact left0Middle5_eq_case_5_5_row_0_2_0
  · exact left0Middle5_eq_case_5_5_row_0_2_1
  · exact left0Middle5_eq_case_5_5_row_0_3_0
  · exact left0Middle5_eq_case_5_5_row_0_3_1
  · exact left0Middle5_eq_case_5_5_row_1_0_0
  · exact left0Middle5_eq_case_5_5_row_1_0_1
  · exact left0Middle5_eq_case_5_5_row_1_1_0
  · exact left0Middle5_eq_case_5_5_row_1_1_1
  · exact left0Middle5_eq_case_5_5_row_1_2_0
  · exact left0Middle5_eq_case_5_5_row_1_2_1
  · exact left0Middle5_eq_case_5_5_row_1_3_0
  · exact left0Middle5_eq_case_5_5_row_1_3_1
  · exact left0Middle5_eq_case_5_5_row_2_0_0
  · exact left0Middle5_eq_case_5_5_row_2_0_1
  · exact left0Middle5_eq_case_5_5_row_2_1_0
  · exact left0Middle5_eq_case_5_5_row_2_1_1
  · exact left0Middle5_eq_case_5_5_row_2_2_0
  · exact left0Middle5_eq_case_5_5_row_2_2_1
  · exact left0Middle5_eq_case_5_5_row_2_3_0
  · exact left0Middle5_eq_case_5_5_row_2_3_1
  · exact left0Middle5_eq_case_5_5_row_3_0_0
  · exact left0Middle5_eq_case_5_5_row_3_0_1
  · exact left0Middle5_eq_case_5_5_row_3_1_0
  · exact left0Middle5_eq_case_5_5_row_3_1_1
  · exact left0Middle5_eq_case_5_5_row_3_2_0
  · exact left0Middle5_eq_case_5_5_row_3_2_1
  · exact left0Middle5_eq_case_5_5_row_3_3_0
  · exact left0Middle5_eq_case_5_5_row_3_3_1

set_option backward.isDefEq.respectTransparency false in
theorem left0Middle5_eq_case_5_5 : left0Middle5 5 5 = outerRightZ 5 5 5 * associatorZ 5 5 5 := by
  simpa only [HexagonAtoms555.assocABC_eq,
    HexagonAtoms555.outerABC_eq,
    HexagonAtoms555.assocBAC_eq,
    HexagonAtoms555.innerABC_eq,
    HexagonAtoms555.innerRightABC_eq,
    HexagonAtoms555.inverseACB_eq,
    HexagonAtoms555.innerACB_eq,
    HexagonAtoms555.assocBCA_eq,
    HexagonAtoms555.innerRightBAC_eq,
    HexagonAtoms555.assocCAB_eq,
    HexagonAtoms555.outerLeftABC_eq,
    HexagonRowColumn555.assocBAC_alias,
    HexagonRowColumn555.innerACB_alias,
    HexagonRowColumn555.assocBCA_alias,
    HexagonRowColumn555.innerRightBAC_alias,
    HexagonRowColumn555.assocCAB_alias,
    HexagonRowColumn555.product0_eq,
    HexagonRowColumn555.product1_eq,
    HexagonRowColumn555.product2_eq,
    HexagonRowColumn555.product3_eq,
    HexagonRowColumn555.product4_eq,
    HexagonRowColumn555.product5_eq,
    HexagonRowColumn555.product6_eq,
    HexagonRowColumn555.product7_eq] using left0Middle5_eq_case_5_5_checked

private theorem left1Middle5_eq_case_5_5_row_0_0_0 : (left1Middle5 5 5) ((0 : Fin 4), (0 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_assocABC HexagonRowColumn555.cols_innerABC) ((0 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_5_5_row_0_0_1 : (left1Middle5 5 5) ((0 : Fin 4), (0 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_assocABC HexagonRowColumn555.cols_innerABC) ((0 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_5_5_row_0_1_0 : (left1Middle5 5 5) ((0 : Fin 4), (1 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_assocABC HexagonRowColumn555.cols_innerABC) ((0 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_5_5_row_0_1_1 : (left1Middle5 5 5) ((0 : Fin 4), (1 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_assocABC HexagonRowColumn555.cols_innerABC) ((0 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_5_5_row_0_2_0 : (left1Middle5 5 5) ((0 : Fin 4), (2 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_assocABC HexagonRowColumn555.cols_innerABC) ((0 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_5_5_row_0_2_1 : (left1Middle5 5 5) ((0 : Fin 4), (2 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_assocABC HexagonRowColumn555.cols_innerABC) ((0 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_5_5_row_0_3_0 : (left1Middle5 5 5) ((0 : Fin 4), (3 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_assocABC HexagonRowColumn555.cols_innerABC) ((0 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_5_5_row_0_3_1 : (left1Middle5 5 5) ((0 : Fin 4), (3 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_assocABC HexagonRowColumn555.cols_innerABC) ((0 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_5_5_row_1_0_0 : (left1Middle5 5 5) ((1 : Fin 4), (0 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_assocABC HexagonRowColumn555.cols_innerABC) ((1 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_5_5_row_1_0_1 : (left1Middle5 5 5) ((1 : Fin 4), (0 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_assocABC HexagonRowColumn555.cols_innerABC) ((1 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_5_5_row_1_1_0 : (left1Middle5 5 5) ((1 : Fin 4), (1 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_assocABC HexagonRowColumn555.cols_innerABC) ((1 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_5_5_row_1_1_1 : (left1Middle5 5 5) ((1 : Fin 4), (1 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_assocABC HexagonRowColumn555.cols_innerABC) ((1 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_5_5_row_1_2_0 : (left1Middle5 5 5) ((1 : Fin 4), (2 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_assocABC HexagonRowColumn555.cols_innerABC) ((1 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_5_5_row_1_2_1 : (left1Middle5 5 5) ((1 : Fin 4), (2 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_assocABC HexagonRowColumn555.cols_innerABC) ((1 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_5_5_row_1_3_0 : (left1Middle5 5 5) ((1 : Fin 4), (3 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_assocABC HexagonRowColumn555.cols_innerABC) ((1 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_5_5_row_1_3_1 : (left1Middle5 5 5) ((1 : Fin 4), (3 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_assocABC HexagonRowColumn555.cols_innerABC) ((1 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_5_5_row_2_0_0 : (left1Middle5 5 5) ((2 : Fin 4), (0 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_assocABC HexagonRowColumn555.cols_innerABC) ((2 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_5_5_row_2_0_1 : (left1Middle5 5 5) ((2 : Fin 4), (0 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_assocABC HexagonRowColumn555.cols_innerABC) ((2 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_5_5_row_2_1_0 : (left1Middle5 5 5) ((2 : Fin 4), (1 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_assocABC HexagonRowColumn555.cols_innerABC) ((2 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_5_5_row_2_1_1 : (left1Middle5 5 5) ((2 : Fin 4), (1 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_assocABC HexagonRowColumn555.cols_innerABC) ((2 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_5_5_row_2_2_0 : (left1Middle5 5 5) ((2 : Fin 4), (2 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_assocABC HexagonRowColumn555.cols_innerABC) ((2 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_5_5_row_2_2_1 : (left1Middle5 5 5) ((2 : Fin 4), (2 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_assocABC HexagonRowColumn555.cols_innerABC) ((2 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_5_5_row_2_3_0 : (left1Middle5 5 5) ((2 : Fin 4), (3 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_assocABC HexagonRowColumn555.cols_innerABC) ((2 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_5_5_row_2_3_1 : (left1Middle5 5 5) ((2 : Fin 4), (3 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_assocABC HexagonRowColumn555.cols_innerABC) ((2 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_5_5_row_3_0_0 : (left1Middle5 5 5) ((3 : Fin 4), (0 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_assocABC HexagonRowColumn555.cols_innerABC) ((3 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_5_5_row_3_0_1 : (left1Middle5 5 5) ((3 : Fin 4), (0 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_assocABC HexagonRowColumn555.cols_innerABC) ((3 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_5_5_row_3_1_0 : (left1Middle5 5 5) ((3 : Fin 4), (1 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_assocABC HexagonRowColumn555.cols_innerABC) ((3 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_5_5_row_3_1_1 : (left1Middle5 5 5) ((3 : Fin 4), (1 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_assocABC HexagonRowColumn555.cols_innerABC) ((3 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_5_5_row_3_2_0 : (left1Middle5 5 5) ((3 : Fin 4), (2 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_assocABC HexagonRowColumn555.cols_innerABC) ((3 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_5_5_row_3_2_1 : (left1Middle5 5 5) ((3 : Fin 4), (2 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_assocABC HexagonRowColumn555.cols_innerABC) ((3 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_5_5_row_3_3_0 : (left1Middle5 5 5) ((3 : Fin 4), (3 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_assocABC HexagonRowColumn555.cols_innerABC) ((3 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_5_5_row_3_3_1 : (left1Middle5 5 5) ((3 : Fin 4), (3 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_assocABC HexagonRowColumn555.cols_innerABC) ((3 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_5_5_checked : left1Middle5 5 5 = rowColumnMul HexagonRowColumn555.rows_assocABC HexagonRowColumn555.cols_innerABC := by
  funext r
  fin_cases r
  · exact left1Middle5_eq_case_5_5_row_0_0_0
  · exact left1Middle5_eq_case_5_5_row_0_0_1
  · exact left1Middle5_eq_case_5_5_row_0_1_0
  · exact left1Middle5_eq_case_5_5_row_0_1_1
  · exact left1Middle5_eq_case_5_5_row_0_2_0
  · exact left1Middle5_eq_case_5_5_row_0_2_1
  · exact left1Middle5_eq_case_5_5_row_0_3_0
  · exact left1Middle5_eq_case_5_5_row_0_3_1
  · exact left1Middle5_eq_case_5_5_row_1_0_0
  · exact left1Middle5_eq_case_5_5_row_1_0_1
  · exact left1Middle5_eq_case_5_5_row_1_1_0
  · exact left1Middle5_eq_case_5_5_row_1_1_1
  · exact left1Middle5_eq_case_5_5_row_1_2_0
  · exact left1Middle5_eq_case_5_5_row_1_2_1
  · exact left1Middle5_eq_case_5_5_row_1_3_0
  · exact left1Middle5_eq_case_5_5_row_1_3_1
  · exact left1Middle5_eq_case_5_5_row_2_0_0
  · exact left1Middle5_eq_case_5_5_row_2_0_1
  · exact left1Middle5_eq_case_5_5_row_2_1_0
  · exact left1Middle5_eq_case_5_5_row_2_1_1
  · exact left1Middle5_eq_case_5_5_row_2_2_0
  · exact left1Middle5_eq_case_5_5_row_2_2_1
  · exact left1Middle5_eq_case_5_5_row_2_3_0
  · exact left1Middle5_eq_case_5_5_row_2_3_1
  · exact left1Middle5_eq_case_5_5_row_3_0_0
  · exact left1Middle5_eq_case_5_5_row_3_0_1
  · exact left1Middle5_eq_case_5_5_row_3_1_0
  · exact left1Middle5_eq_case_5_5_row_3_1_1
  · exact left1Middle5_eq_case_5_5_row_3_2_0
  · exact left1Middle5_eq_case_5_5_row_3_2_1
  · exact left1Middle5_eq_case_5_5_row_3_3_0
  · exact left1Middle5_eq_case_5_5_row_3_3_1

set_option backward.isDefEq.respectTransparency false in
theorem left1Middle5_eq_case_5_5 : left1Middle5 5 5 = associatorZ 5 5 5 * innerLeftZ 5 5 5 := by
  simpa only [HexagonAtoms555.assocABC_eq,
    HexagonAtoms555.outerABC_eq,
    HexagonAtoms555.assocBAC_eq,
    HexagonAtoms555.innerABC_eq,
    HexagonAtoms555.innerRightABC_eq,
    HexagonAtoms555.inverseACB_eq,
    HexagonAtoms555.innerACB_eq,
    HexagonAtoms555.assocBCA_eq,
    HexagonAtoms555.innerRightBAC_eq,
    HexagonAtoms555.assocCAB_eq,
    HexagonAtoms555.outerLeftABC_eq,
    HexagonRowColumn555.assocBAC_alias,
    HexagonRowColumn555.innerACB_alias,
    HexagonRowColumn555.assocBCA_alias,
    HexagonRowColumn555.innerRightBAC_alias,
    HexagonRowColumn555.assocCAB_alias,
    HexagonRowColumn555.product0_eq,
    HexagonRowColumn555.product1_eq,
    HexagonRowColumn555.product2_eq,
    HexagonRowColumn555.product3_eq,
    HexagonRowColumn555.product4_eq,
    HexagonRowColumn555.product5_eq,
    HexagonRowColumn555.product6_eq,
    HexagonRowColumn555.product7_eq] using left1Middle5_eq_case_5_5_checked

private theorem right0Middle5_eq_case_5_5_row_0_0_0 : (right0Middle5 5 5) ((0 : Fin 4), (0 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_innerRightABC HexagonRowColumn555.cols_assocABC) ((0 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_5_5_row_0_0_1 : (right0Middle5 5 5) ((0 : Fin 4), (0 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_innerRightABC HexagonRowColumn555.cols_assocABC) ((0 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_5_5_row_0_1_0 : (right0Middle5 5 5) ((0 : Fin 4), (1 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_innerRightABC HexagonRowColumn555.cols_assocABC) ((0 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_5_5_row_0_1_1 : (right0Middle5 5 5) ((0 : Fin 4), (1 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_innerRightABC HexagonRowColumn555.cols_assocABC) ((0 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_5_5_row_0_2_0 : (right0Middle5 5 5) ((0 : Fin 4), (2 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_innerRightABC HexagonRowColumn555.cols_assocABC) ((0 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_5_5_row_0_2_1 : (right0Middle5 5 5) ((0 : Fin 4), (2 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_innerRightABC HexagonRowColumn555.cols_assocABC) ((0 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_5_5_row_0_3_0 : (right0Middle5 5 5) ((0 : Fin 4), (3 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_innerRightABC HexagonRowColumn555.cols_assocABC) ((0 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_5_5_row_0_3_1 : (right0Middle5 5 5) ((0 : Fin 4), (3 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_innerRightABC HexagonRowColumn555.cols_assocABC) ((0 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_5_5_row_1_0_0 : (right0Middle5 5 5) ((1 : Fin 4), (0 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_innerRightABC HexagonRowColumn555.cols_assocABC) ((1 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_5_5_row_1_0_1 : (right0Middle5 5 5) ((1 : Fin 4), (0 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_innerRightABC HexagonRowColumn555.cols_assocABC) ((1 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_5_5_row_1_1_0 : (right0Middle5 5 5) ((1 : Fin 4), (1 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_innerRightABC HexagonRowColumn555.cols_assocABC) ((1 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_5_5_row_1_1_1 : (right0Middle5 5 5) ((1 : Fin 4), (1 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_innerRightABC HexagonRowColumn555.cols_assocABC) ((1 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_5_5_row_1_2_0 : (right0Middle5 5 5) ((1 : Fin 4), (2 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_innerRightABC HexagonRowColumn555.cols_assocABC) ((1 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_5_5_row_1_2_1 : (right0Middle5 5 5) ((1 : Fin 4), (2 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_innerRightABC HexagonRowColumn555.cols_assocABC) ((1 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_5_5_row_1_3_0 : (right0Middle5 5 5) ((1 : Fin 4), (3 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_innerRightABC HexagonRowColumn555.cols_assocABC) ((1 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_5_5_row_1_3_1 : (right0Middle5 5 5) ((1 : Fin 4), (3 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_innerRightABC HexagonRowColumn555.cols_assocABC) ((1 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_5_5_row_2_0_0 : (right0Middle5 5 5) ((2 : Fin 4), (0 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_innerRightABC HexagonRowColumn555.cols_assocABC) ((2 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_5_5_row_2_0_1 : (right0Middle5 5 5) ((2 : Fin 4), (0 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_innerRightABC HexagonRowColumn555.cols_assocABC) ((2 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_5_5_row_2_1_0 : (right0Middle5 5 5) ((2 : Fin 4), (1 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_innerRightABC HexagonRowColumn555.cols_assocABC) ((2 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_5_5_row_2_1_1 : (right0Middle5 5 5) ((2 : Fin 4), (1 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_innerRightABC HexagonRowColumn555.cols_assocABC) ((2 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_5_5_row_2_2_0 : (right0Middle5 5 5) ((2 : Fin 4), (2 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_innerRightABC HexagonRowColumn555.cols_assocABC) ((2 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_5_5_row_2_2_1 : (right0Middle5 5 5) ((2 : Fin 4), (2 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_innerRightABC HexagonRowColumn555.cols_assocABC) ((2 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_5_5_row_2_3_0 : (right0Middle5 5 5) ((2 : Fin 4), (3 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_innerRightABC HexagonRowColumn555.cols_assocABC) ((2 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_5_5_row_2_3_1 : (right0Middle5 5 5) ((2 : Fin 4), (3 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_innerRightABC HexagonRowColumn555.cols_assocABC) ((2 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_5_5_row_3_0_0 : (right0Middle5 5 5) ((3 : Fin 4), (0 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_innerRightABC HexagonRowColumn555.cols_assocABC) ((3 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_5_5_row_3_0_1 : (right0Middle5 5 5) ((3 : Fin 4), (0 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_innerRightABC HexagonRowColumn555.cols_assocABC) ((3 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_5_5_row_3_1_0 : (right0Middle5 5 5) ((3 : Fin 4), (1 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_innerRightABC HexagonRowColumn555.cols_assocABC) ((3 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_5_5_row_3_1_1 : (right0Middle5 5 5) ((3 : Fin 4), (1 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_innerRightABC HexagonRowColumn555.cols_assocABC) ((3 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_5_5_row_3_2_0 : (right0Middle5 5 5) ((3 : Fin 4), (2 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_innerRightABC HexagonRowColumn555.cols_assocABC) ((3 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_5_5_row_3_2_1 : (right0Middle5 5 5) ((3 : Fin 4), (2 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_innerRightABC HexagonRowColumn555.cols_assocABC) ((3 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_5_5_row_3_3_0 : (right0Middle5 5 5) ((3 : Fin 4), (3 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_innerRightABC HexagonRowColumn555.cols_assocABC) ((3 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_5_5_row_3_3_1 : (right0Middle5 5 5) ((3 : Fin 4), (3 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_innerRightABC HexagonRowColumn555.cols_assocABC) ((3 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_5_5_checked : right0Middle5 5 5 = rowColumnMul HexagonRowColumn555.rows_innerRightABC HexagonRowColumn555.cols_assocABC := by
  funext r
  fin_cases r
  · exact right0Middle5_eq_case_5_5_row_0_0_0
  · exact right0Middle5_eq_case_5_5_row_0_0_1
  · exact right0Middle5_eq_case_5_5_row_0_1_0
  · exact right0Middle5_eq_case_5_5_row_0_1_1
  · exact right0Middle5_eq_case_5_5_row_0_2_0
  · exact right0Middle5_eq_case_5_5_row_0_2_1
  · exact right0Middle5_eq_case_5_5_row_0_3_0
  · exact right0Middle5_eq_case_5_5_row_0_3_1
  · exact right0Middle5_eq_case_5_5_row_1_0_0
  · exact right0Middle5_eq_case_5_5_row_1_0_1
  · exact right0Middle5_eq_case_5_5_row_1_1_0
  · exact right0Middle5_eq_case_5_5_row_1_1_1
  · exact right0Middle5_eq_case_5_5_row_1_2_0
  · exact right0Middle5_eq_case_5_5_row_1_2_1
  · exact right0Middle5_eq_case_5_5_row_1_3_0
  · exact right0Middle5_eq_case_5_5_row_1_3_1
  · exact right0Middle5_eq_case_5_5_row_2_0_0
  · exact right0Middle5_eq_case_5_5_row_2_0_1
  · exact right0Middle5_eq_case_5_5_row_2_1_0
  · exact right0Middle5_eq_case_5_5_row_2_1_1
  · exact right0Middle5_eq_case_5_5_row_2_2_0
  · exact right0Middle5_eq_case_5_5_row_2_2_1
  · exact right0Middle5_eq_case_5_5_row_2_3_0
  · exact right0Middle5_eq_case_5_5_row_2_3_1
  · exact right0Middle5_eq_case_5_5_row_3_0_0
  · exact right0Middle5_eq_case_5_5_row_3_0_1
  · exact right0Middle5_eq_case_5_5_row_3_1_0
  · exact right0Middle5_eq_case_5_5_row_3_1_1
  · exact right0Middle5_eq_case_5_5_row_3_2_0
  · exact right0Middle5_eq_case_5_5_row_3_2_1
  · exact right0Middle5_eq_case_5_5_row_3_3_0
  · exact right0Middle5_eq_case_5_5_row_3_3_1

set_option backward.isDefEq.respectTransparency false in
theorem right0Middle5_eq_case_5_5 : right0Middle5 5 5 = innerRightZ 5 5 5 * associatorZ 5 5 5 := by
  simpa only [HexagonAtoms555.assocABC_eq,
    HexagonAtoms555.outerABC_eq,
    HexagonAtoms555.assocBAC_eq,
    HexagonAtoms555.innerABC_eq,
    HexagonAtoms555.innerRightABC_eq,
    HexagonAtoms555.inverseACB_eq,
    HexagonAtoms555.innerACB_eq,
    HexagonAtoms555.assocBCA_eq,
    HexagonAtoms555.innerRightBAC_eq,
    HexagonAtoms555.assocCAB_eq,
    HexagonAtoms555.outerLeftABC_eq,
    HexagonRowColumn555.assocBAC_alias,
    HexagonRowColumn555.innerACB_alias,
    HexagonRowColumn555.assocBCA_alias,
    HexagonRowColumn555.innerRightBAC_alias,
    HexagonRowColumn555.assocCAB_alias,
    HexagonRowColumn555.product0_eq,
    HexagonRowColumn555.product1_eq,
    HexagonRowColumn555.product2_eq,
    HexagonRowColumn555.product3_eq,
    HexagonRowColumn555.product4_eq,
    HexagonRowColumn555.product5_eq,
    HexagonRowColumn555.product6_eq,
    HexagonRowColumn555.product7_eq] using right0Middle5_eq_case_5_5_checked

private theorem right1Middle5_eq_case_5_5_row_0_0_0 : (right1Middle5 5 5) ((0 : Fin 4), (0 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_inverseACB HexagonRowColumn555.cols_right0) ((0 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_5_5_row_0_0_1 : (right1Middle5 5 5) ((0 : Fin 4), (0 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_inverseACB HexagonRowColumn555.cols_right0) ((0 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_5_5_row_0_1_0 : (right1Middle5 5 5) ((0 : Fin 4), (1 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_inverseACB HexagonRowColumn555.cols_right0) ((0 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_5_5_row_0_1_1 : (right1Middle5 5 5) ((0 : Fin 4), (1 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_inverseACB HexagonRowColumn555.cols_right0) ((0 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_5_5_row_0_2_0 : (right1Middle5 5 5) ((0 : Fin 4), (2 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_inverseACB HexagonRowColumn555.cols_right0) ((0 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_5_5_row_0_2_1 : (right1Middle5 5 5) ((0 : Fin 4), (2 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_inverseACB HexagonRowColumn555.cols_right0) ((0 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_5_5_row_0_3_0 : (right1Middle5 5 5) ((0 : Fin 4), (3 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_inverseACB HexagonRowColumn555.cols_right0) ((0 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_5_5_row_0_3_1 : (right1Middle5 5 5) ((0 : Fin 4), (3 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_inverseACB HexagonRowColumn555.cols_right0) ((0 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_5_5_row_1_0_0 : (right1Middle5 5 5) ((1 : Fin 4), (0 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_inverseACB HexagonRowColumn555.cols_right0) ((1 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_5_5_row_1_0_1 : (right1Middle5 5 5) ((1 : Fin 4), (0 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_inverseACB HexagonRowColumn555.cols_right0) ((1 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_5_5_row_1_1_0 : (right1Middle5 5 5) ((1 : Fin 4), (1 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_inverseACB HexagonRowColumn555.cols_right0) ((1 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_5_5_row_1_1_1 : (right1Middle5 5 5) ((1 : Fin 4), (1 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_inverseACB HexagonRowColumn555.cols_right0) ((1 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_5_5_row_1_2_0 : (right1Middle5 5 5) ((1 : Fin 4), (2 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_inverseACB HexagonRowColumn555.cols_right0) ((1 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_5_5_row_1_2_1 : (right1Middle5 5 5) ((1 : Fin 4), (2 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_inverseACB HexagonRowColumn555.cols_right0) ((1 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_5_5_row_1_3_0 : (right1Middle5 5 5) ((1 : Fin 4), (3 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_inverseACB HexagonRowColumn555.cols_right0) ((1 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_5_5_row_1_3_1 : (right1Middle5 5 5) ((1 : Fin 4), (3 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_inverseACB HexagonRowColumn555.cols_right0) ((1 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_5_5_row_2_0_0 : (right1Middle5 5 5) ((2 : Fin 4), (0 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_inverseACB HexagonRowColumn555.cols_right0) ((2 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_5_5_row_2_0_1 : (right1Middle5 5 5) ((2 : Fin 4), (0 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_inverseACB HexagonRowColumn555.cols_right0) ((2 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_5_5_row_2_1_0 : (right1Middle5 5 5) ((2 : Fin 4), (1 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_inverseACB HexagonRowColumn555.cols_right0) ((2 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_5_5_row_2_1_1 : (right1Middle5 5 5) ((2 : Fin 4), (1 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_inverseACB HexagonRowColumn555.cols_right0) ((2 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_5_5_row_2_2_0 : (right1Middle5 5 5) ((2 : Fin 4), (2 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_inverseACB HexagonRowColumn555.cols_right0) ((2 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_5_5_row_2_2_1 : (right1Middle5 5 5) ((2 : Fin 4), (2 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_inverseACB HexagonRowColumn555.cols_right0) ((2 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_5_5_row_2_3_0 : (right1Middle5 5 5) ((2 : Fin 4), (3 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_inverseACB HexagonRowColumn555.cols_right0) ((2 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_5_5_row_2_3_1 : (right1Middle5 5 5) ((2 : Fin 4), (3 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_inverseACB HexagonRowColumn555.cols_right0) ((2 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_5_5_row_3_0_0 : (right1Middle5 5 5) ((3 : Fin 4), (0 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_inverseACB HexagonRowColumn555.cols_right0) ((3 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_5_5_row_3_0_1 : (right1Middle5 5 5) ((3 : Fin 4), (0 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_inverseACB HexagonRowColumn555.cols_right0) ((3 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_5_5_row_3_1_0 : (right1Middle5 5 5) ((3 : Fin 4), (1 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_inverseACB HexagonRowColumn555.cols_right0) ((3 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_5_5_row_3_1_1 : (right1Middle5 5 5) ((3 : Fin 4), (1 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_inverseACB HexagonRowColumn555.cols_right0) ((3 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_5_5_row_3_2_0 : (right1Middle5 5 5) ((3 : Fin 4), (2 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_inverseACB HexagonRowColumn555.cols_right0) ((3 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_5_5_row_3_2_1 : (right1Middle5 5 5) ((3 : Fin 4), (2 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_inverseACB HexagonRowColumn555.cols_right0) ((3 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_5_5_row_3_3_0 : (right1Middle5 5 5) ((3 : Fin 4), (3 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_inverseACB HexagonRowColumn555.cols_right0) ((3 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_5_5_row_3_3_1 : (right1Middle5 5 5) ((3 : Fin 4), (3 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_inverseACB HexagonRowColumn555.cols_right0) ((3 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_5_5_checked : right1Middle5 5 5 = rowColumnMul HexagonRowColumn555.rows_inverseACB HexagonRowColumn555.cols_right0 := by
  funext r
  fin_cases r
  · exact right1Middle5_eq_case_5_5_row_0_0_0
  · exact right1Middle5_eq_case_5_5_row_0_0_1
  · exact right1Middle5_eq_case_5_5_row_0_1_0
  · exact right1Middle5_eq_case_5_5_row_0_1_1
  · exact right1Middle5_eq_case_5_5_row_0_2_0
  · exact right1Middle5_eq_case_5_5_row_0_2_1
  · exact right1Middle5_eq_case_5_5_row_0_3_0
  · exact right1Middle5_eq_case_5_5_row_0_3_1
  · exact right1Middle5_eq_case_5_5_row_1_0_0
  · exact right1Middle5_eq_case_5_5_row_1_0_1
  · exact right1Middle5_eq_case_5_5_row_1_1_0
  · exact right1Middle5_eq_case_5_5_row_1_1_1
  · exact right1Middle5_eq_case_5_5_row_1_2_0
  · exact right1Middle5_eq_case_5_5_row_1_2_1
  · exact right1Middle5_eq_case_5_5_row_1_3_0
  · exact right1Middle5_eq_case_5_5_row_1_3_1
  · exact right1Middle5_eq_case_5_5_row_2_0_0
  · exact right1Middle5_eq_case_5_5_row_2_0_1
  · exact right1Middle5_eq_case_5_5_row_2_1_0
  · exact right1Middle5_eq_case_5_5_row_2_1_1
  · exact right1Middle5_eq_case_5_5_row_2_2_0
  · exact right1Middle5_eq_case_5_5_row_2_2_1
  · exact right1Middle5_eq_case_5_5_row_2_3_0
  · exact right1Middle5_eq_case_5_5_row_2_3_1
  · exact right1Middle5_eq_case_5_5_row_3_0_0
  · exact right1Middle5_eq_case_5_5_row_3_0_1
  · exact right1Middle5_eq_case_5_5_row_3_1_0
  · exact right1Middle5_eq_case_5_5_row_3_1_1
  · exact right1Middle5_eq_case_5_5_row_3_2_0
  · exact right1Middle5_eq_case_5_5_row_3_2_1
  · exact right1Middle5_eq_case_5_5_row_3_3_0
  · exact right1Middle5_eq_case_5_5_row_3_3_1

set_option backward.isDefEq.respectTransparency false in
theorem right1Middle5_eq_case_5_5 : right1Middle5 5 5 = associatorInverseZ 5 5 5 * right0Middle5 5 5 := by
  simpa only [HexagonAtoms555.assocABC_eq,
    HexagonAtoms555.outerABC_eq,
    HexagonAtoms555.assocBAC_eq,
    HexagonAtoms555.innerABC_eq,
    HexagonAtoms555.innerRightABC_eq,
    HexagonAtoms555.inverseACB_eq,
    HexagonAtoms555.innerACB_eq,
    HexagonAtoms555.assocBCA_eq,
    HexagonAtoms555.innerRightBAC_eq,
    HexagonAtoms555.assocCAB_eq,
    HexagonAtoms555.outerLeftABC_eq,
    HexagonRowColumn555.assocBAC_alias,
    HexagonRowColumn555.innerACB_alias,
    HexagonRowColumn555.assocBCA_alias,
    HexagonRowColumn555.innerRightBAC_alias,
    HexagonRowColumn555.assocCAB_alias,
    HexagonRowColumn555.product0_eq,
    HexagonRowColumn555.product1_eq,
    HexagonRowColumn555.product2_eq,
    HexagonRowColumn555.product3_eq,
    HexagonRowColumn555.product4_eq,
    HexagonRowColumn555.product5_eq,
    HexagonRowColumn555.product6_eq,
    HexagonRowColumn555.product7_eq] using right1Middle5_eq_case_5_5_checked

private theorem right2Middle5_eq_case_5_5_row_0_0_0 : (right2Middle5 5 5) ((0 : Fin 4), (0 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_innerABC HexagonRowColumn555.cols_right1) ((0 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_5_5_row_0_0_1 : (right2Middle5 5 5) ((0 : Fin 4), (0 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_innerABC HexagonRowColumn555.cols_right1) ((0 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_5_5_row_0_1_0 : (right2Middle5 5 5) ((0 : Fin 4), (1 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_innerABC HexagonRowColumn555.cols_right1) ((0 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_5_5_row_0_1_1 : (right2Middle5 5 5) ((0 : Fin 4), (1 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_innerABC HexagonRowColumn555.cols_right1) ((0 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_5_5_row_0_2_0 : (right2Middle5 5 5) ((0 : Fin 4), (2 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_innerABC HexagonRowColumn555.cols_right1) ((0 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_5_5_row_0_2_1 : (right2Middle5 5 5) ((0 : Fin 4), (2 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_innerABC HexagonRowColumn555.cols_right1) ((0 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_5_5_row_0_3_0 : (right2Middle5 5 5) ((0 : Fin 4), (3 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_innerABC HexagonRowColumn555.cols_right1) ((0 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_5_5_row_0_3_1 : (right2Middle5 5 5) ((0 : Fin 4), (3 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_innerABC HexagonRowColumn555.cols_right1) ((0 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_5_5_row_1_0_0 : (right2Middle5 5 5) ((1 : Fin 4), (0 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_innerABC HexagonRowColumn555.cols_right1) ((1 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_5_5_row_1_0_1 : (right2Middle5 5 5) ((1 : Fin 4), (0 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_innerABC HexagonRowColumn555.cols_right1) ((1 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_5_5_row_1_1_0 : (right2Middle5 5 5) ((1 : Fin 4), (1 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_innerABC HexagonRowColumn555.cols_right1) ((1 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_5_5_row_1_1_1 : (right2Middle5 5 5) ((1 : Fin 4), (1 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_innerABC HexagonRowColumn555.cols_right1) ((1 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_5_5_row_1_2_0 : (right2Middle5 5 5) ((1 : Fin 4), (2 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_innerABC HexagonRowColumn555.cols_right1) ((1 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_5_5_row_1_2_1 : (right2Middle5 5 5) ((1 : Fin 4), (2 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_innerABC HexagonRowColumn555.cols_right1) ((1 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_5_5_row_1_3_0 : (right2Middle5 5 5) ((1 : Fin 4), (3 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_innerABC HexagonRowColumn555.cols_right1) ((1 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_5_5_row_1_3_1 : (right2Middle5 5 5) ((1 : Fin 4), (3 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_innerABC HexagonRowColumn555.cols_right1) ((1 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_5_5_row_2_0_0 : (right2Middle5 5 5) ((2 : Fin 4), (0 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_innerABC HexagonRowColumn555.cols_right1) ((2 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_5_5_row_2_0_1 : (right2Middle5 5 5) ((2 : Fin 4), (0 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_innerABC HexagonRowColumn555.cols_right1) ((2 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_5_5_row_2_1_0 : (right2Middle5 5 5) ((2 : Fin 4), (1 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_innerABC HexagonRowColumn555.cols_right1) ((2 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_5_5_row_2_1_1 : (right2Middle5 5 5) ((2 : Fin 4), (1 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_innerABC HexagonRowColumn555.cols_right1) ((2 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_5_5_row_2_2_0 : (right2Middle5 5 5) ((2 : Fin 4), (2 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_innerABC HexagonRowColumn555.cols_right1) ((2 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_5_5_row_2_2_1 : (right2Middle5 5 5) ((2 : Fin 4), (2 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_innerABC HexagonRowColumn555.cols_right1) ((2 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_5_5_row_2_3_0 : (right2Middle5 5 5) ((2 : Fin 4), (3 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_innerABC HexagonRowColumn555.cols_right1) ((2 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_5_5_row_2_3_1 : (right2Middle5 5 5) ((2 : Fin 4), (3 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_innerABC HexagonRowColumn555.cols_right1) ((2 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_5_5_row_3_0_0 : (right2Middle5 5 5) ((3 : Fin 4), (0 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_innerABC HexagonRowColumn555.cols_right1) ((3 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_5_5_row_3_0_1 : (right2Middle5 5 5) ((3 : Fin 4), (0 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_innerABC HexagonRowColumn555.cols_right1) ((3 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_5_5_row_3_1_0 : (right2Middle5 5 5) ((3 : Fin 4), (1 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_innerABC HexagonRowColumn555.cols_right1) ((3 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_5_5_row_3_1_1 : (right2Middle5 5 5) ((3 : Fin 4), (1 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_innerABC HexagonRowColumn555.cols_right1) ((3 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_5_5_row_3_2_0 : (right2Middle5 5 5) ((3 : Fin 4), (2 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_innerABC HexagonRowColumn555.cols_right1) ((3 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_5_5_row_3_2_1 : (right2Middle5 5 5) ((3 : Fin 4), (2 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_innerABC HexagonRowColumn555.cols_right1) ((3 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_5_5_row_3_3_0 : (right2Middle5 5 5) ((3 : Fin 4), (3 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_innerABC HexagonRowColumn555.cols_right1) ((3 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_5_5_row_3_3_1 : (right2Middle5 5 5) ((3 : Fin 4), (3 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn555.rows_innerABC HexagonRowColumn555.cols_right1) ((3 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_5_5_checked : right2Middle5 5 5 = rowColumnMul HexagonRowColumn555.rows_innerABC HexagonRowColumn555.cols_right1 := by
  funext r
  fin_cases r
  · exact right2Middle5_eq_case_5_5_row_0_0_0
  · exact right2Middle5_eq_case_5_5_row_0_0_1
  · exact right2Middle5_eq_case_5_5_row_0_1_0
  · exact right2Middle5_eq_case_5_5_row_0_1_1
  · exact right2Middle5_eq_case_5_5_row_0_2_0
  · exact right2Middle5_eq_case_5_5_row_0_2_1
  · exact right2Middle5_eq_case_5_5_row_0_3_0
  · exact right2Middle5_eq_case_5_5_row_0_3_1
  · exact right2Middle5_eq_case_5_5_row_1_0_0
  · exact right2Middle5_eq_case_5_5_row_1_0_1
  · exact right2Middle5_eq_case_5_5_row_1_1_0
  · exact right2Middle5_eq_case_5_5_row_1_1_1
  · exact right2Middle5_eq_case_5_5_row_1_2_0
  · exact right2Middle5_eq_case_5_5_row_1_2_1
  · exact right2Middle5_eq_case_5_5_row_1_3_0
  · exact right2Middle5_eq_case_5_5_row_1_3_1
  · exact right2Middle5_eq_case_5_5_row_2_0_0
  · exact right2Middle5_eq_case_5_5_row_2_0_1
  · exact right2Middle5_eq_case_5_5_row_2_1_0
  · exact right2Middle5_eq_case_5_5_row_2_1_1
  · exact right2Middle5_eq_case_5_5_row_2_2_0
  · exact right2Middle5_eq_case_5_5_row_2_2_1
  · exact right2Middle5_eq_case_5_5_row_2_3_0
  · exact right2Middle5_eq_case_5_5_row_2_3_1
  · exact right2Middle5_eq_case_5_5_row_3_0_0
  · exact right2Middle5_eq_case_5_5_row_3_0_1
  · exact right2Middle5_eq_case_5_5_row_3_1_0
  · exact right2Middle5_eq_case_5_5_row_3_1_1
  · exact right2Middle5_eq_case_5_5_row_3_2_0
  · exact right2Middle5_eq_case_5_5_row_3_2_1
  · exact right2Middle5_eq_case_5_5_row_3_3_0
  · exact right2Middle5_eq_case_5_5_row_3_3_1

set_option backward.isDefEq.respectTransparency false in
theorem right2Middle5_eq_case_5_5 : right2Middle5 5 5 = innerLeftZ 5 5 5 * right1Middle5 5 5 := by
  simpa only [HexagonAtoms555.assocABC_eq,
    HexagonAtoms555.outerABC_eq,
    HexagonAtoms555.assocBAC_eq,
    HexagonAtoms555.innerABC_eq,
    HexagonAtoms555.innerRightABC_eq,
    HexagonAtoms555.inverseACB_eq,
    HexagonAtoms555.innerACB_eq,
    HexagonAtoms555.assocBCA_eq,
    HexagonAtoms555.innerRightBAC_eq,
    HexagonAtoms555.assocCAB_eq,
    HexagonAtoms555.outerLeftABC_eq,
    HexagonRowColumn555.assocBAC_alias,
    HexagonRowColumn555.innerACB_alias,
    HexagonRowColumn555.assocBCA_alias,
    HexagonRowColumn555.innerRightBAC_alias,
    HexagonRowColumn555.assocCAB_alias,
    HexagonRowColumn555.product0_eq,
    HexagonRowColumn555.product1_eq,
    HexagonRowColumn555.product2_eq,
    HexagonRowColumn555.product3_eq,
    HexagonRowColumn555.product4_eq,
    HexagonRowColumn555.product5_eq,
    HexagonRowColumn555.product6_eq,
    HexagonRowColumn555.product7_eq] using right2Middle5_eq_case_5_5_checked

private theorem leftFinal5_case_5_5_row_0_0_0 : (((-1 : ℤ) ^ (leftScaleBit 5 5 5).val * positiveScale (leftScaleExponent 5 5 5)) •
      (rowColumnMul HexagonRowColumn555.rows_assocABC HexagonRowColumn555.cols_left0)) ((0 : Fin 4), (0 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 5 5 5) • (rowColumnMul HexagonRowColumn555.rows_innerRightABC HexagonRowColumn555.cols_left1)) ((0 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal5_case_5_5_row_0_0_1 : (((-1 : ℤ) ^ (leftScaleBit 5 5 5).val * positiveScale (leftScaleExponent 5 5 5)) •
      (rowColumnMul HexagonRowColumn555.rows_assocABC HexagonRowColumn555.cols_left0)) ((0 : Fin 4), (0 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 5 5 5) • (rowColumnMul HexagonRowColumn555.rows_innerRightABC HexagonRowColumn555.cols_left1)) ((0 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal5_case_5_5_row_0_1_0 : (((-1 : ℤ) ^ (leftScaleBit 5 5 5).val * positiveScale (leftScaleExponent 5 5 5)) •
      (rowColumnMul HexagonRowColumn555.rows_assocABC HexagonRowColumn555.cols_left0)) ((0 : Fin 4), (1 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 5 5 5) • (rowColumnMul HexagonRowColumn555.rows_innerRightABC HexagonRowColumn555.cols_left1)) ((0 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal5_case_5_5_row_0_1_1 : (((-1 : ℤ) ^ (leftScaleBit 5 5 5).val * positiveScale (leftScaleExponent 5 5 5)) •
      (rowColumnMul HexagonRowColumn555.rows_assocABC HexagonRowColumn555.cols_left0)) ((0 : Fin 4), (1 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 5 5 5) • (rowColumnMul HexagonRowColumn555.rows_innerRightABC HexagonRowColumn555.cols_left1)) ((0 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal5_case_5_5_row_0_2_0 : (((-1 : ℤ) ^ (leftScaleBit 5 5 5).val * positiveScale (leftScaleExponent 5 5 5)) •
      (rowColumnMul HexagonRowColumn555.rows_assocABC HexagonRowColumn555.cols_left0)) ((0 : Fin 4), (2 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 5 5 5) • (rowColumnMul HexagonRowColumn555.rows_innerRightABC HexagonRowColumn555.cols_left1)) ((0 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal5_case_5_5_row_0_2_1 : (((-1 : ℤ) ^ (leftScaleBit 5 5 5).val * positiveScale (leftScaleExponent 5 5 5)) •
      (rowColumnMul HexagonRowColumn555.rows_assocABC HexagonRowColumn555.cols_left0)) ((0 : Fin 4), (2 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 5 5 5) • (rowColumnMul HexagonRowColumn555.rows_innerRightABC HexagonRowColumn555.cols_left1)) ((0 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal5_case_5_5_row_0_3_0 : (((-1 : ℤ) ^ (leftScaleBit 5 5 5).val * positiveScale (leftScaleExponent 5 5 5)) •
      (rowColumnMul HexagonRowColumn555.rows_assocABC HexagonRowColumn555.cols_left0)) ((0 : Fin 4), (3 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 5 5 5) • (rowColumnMul HexagonRowColumn555.rows_innerRightABC HexagonRowColumn555.cols_left1)) ((0 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal5_case_5_5_row_0_3_1 : (((-1 : ℤ) ^ (leftScaleBit 5 5 5).val * positiveScale (leftScaleExponent 5 5 5)) •
      (rowColumnMul HexagonRowColumn555.rows_assocABC HexagonRowColumn555.cols_left0)) ((0 : Fin 4), (3 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 5 5 5) • (rowColumnMul HexagonRowColumn555.rows_innerRightABC HexagonRowColumn555.cols_left1)) ((0 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal5_case_5_5_row_1_0_0 : (((-1 : ℤ) ^ (leftScaleBit 5 5 5).val * positiveScale (leftScaleExponent 5 5 5)) •
      (rowColumnMul HexagonRowColumn555.rows_assocABC HexagonRowColumn555.cols_left0)) ((1 : Fin 4), (0 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 5 5 5) • (rowColumnMul HexagonRowColumn555.rows_innerRightABC HexagonRowColumn555.cols_left1)) ((1 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal5_case_5_5_row_1_0_1 : (((-1 : ℤ) ^ (leftScaleBit 5 5 5).val * positiveScale (leftScaleExponent 5 5 5)) •
      (rowColumnMul HexagonRowColumn555.rows_assocABC HexagonRowColumn555.cols_left0)) ((1 : Fin 4), (0 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 5 5 5) • (rowColumnMul HexagonRowColumn555.rows_innerRightABC HexagonRowColumn555.cols_left1)) ((1 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal5_case_5_5_row_1_1_0 : (((-1 : ℤ) ^ (leftScaleBit 5 5 5).val * positiveScale (leftScaleExponent 5 5 5)) •
      (rowColumnMul HexagonRowColumn555.rows_assocABC HexagonRowColumn555.cols_left0)) ((1 : Fin 4), (1 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 5 5 5) • (rowColumnMul HexagonRowColumn555.rows_innerRightABC HexagonRowColumn555.cols_left1)) ((1 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal5_case_5_5_row_1_1_1 : (((-1 : ℤ) ^ (leftScaleBit 5 5 5).val * positiveScale (leftScaleExponent 5 5 5)) •
      (rowColumnMul HexagonRowColumn555.rows_assocABC HexagonRowColumn555.cols_left0)) ((1 : Fin 4), (1 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 5 5 5) • (rowColumnMul HexagonRowColumn555.rows_innerRightABC HexagonRowColumn555.cols_left1)) ((1 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal5_case_5_5_row_1_2_0 : (((-1 : ℤ) ^ (leftScaleBit 5 5 5).val * positiveScale (leftScaleExponent 5 5 5)) •
      (rowColumnMul HexagonRowColumn555.rows_assocABC HexagonRowColumn555.cols_left0)) ((1 : Fin 4), (2 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 5 5 5) • (rowColumnMul HexagonRowColumn555.rows_innerRightABC HexagonRowColumn555.cols_left1)) ((1 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal5_case_5_5_row_1_2_1 : (((-1 : ℤ) ^ (leftScaleBit 5 5 5).val * positiveScale (leftScaleExponent 5 5 5)) •
      (rowColumnMul HexagonRowColumn555.rows_assocABC HexagonRowColumn555.cols_left0)) ((1 : Fin 4), (2 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 5 5 5) • (rowColumnMul HexagonRowColumn555.rows_innerRightABC HexagonRowColumn555.cols_left1)) ((1 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal5_case_5_5_row_1_3_0 : (((-1 : ℤ) ^ (leftScaleBit 5 5 5).val * positiveScale (leftScaleExponent 5 5 5)) •
      (rowColumnMul HexagonRowColumn555.rows_assocABC HexagonRowColumn555.cols_left0)) ((1 : Fin 4), (3 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 5 5 5) • (rowColumnMul HexagonRowColumn555.rows_innerRightABC HexagonRowColumn555.cols_left1)) ((1 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal5_case_5_5_row_1_3_1 : (((-1 : ℤ) ^ (leftScaleBit 5 5 5).val * positiveScale (leftScaleExponent 5 5 5)) •
      (rowColumnMul HexagonRowColumn555.rows_assocABC HexagonRowColumn555.cols_left0)) ((1 : Fin 4), (3 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 5 5 5) • (rowColumnMul HexagonRowColumn555.rows_innerRightABC HexagonRowColumn555.cols_left1)) ((1 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal5_case_5_5_row_2_0_0 : (((-1 : ℤ) ^ (leftScaleBit 5 5 5).val * positiveScale (leftScaleExponent 5 5 5)) •
      (rowColumnMul HexagonRowColumn555.rows_assocABC HexagonRowColumn555.cols_left0)) ((2 : Fin 4), (0 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 5 5 5) • (rowColumnMul HexagonRowColumn555.rows_innerRightABC HexagonRowColumn555.cols_left1)) ((2 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal5_case_5_5_row_2_0_1 : (((-1 : ℤ) ^ (leftScaleBit 5 5 5).val * positiveScale (leftScaleExponent 5 5 5)) •
      (rowColumnMul HexagonRowColumn555.rows_assocABC HexagonRowColumn555.cols_left0)) ((2 : Fin 4), (0 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 5 5 5) • (rowColumnMul HexagonRowColumn555.rows_innerRightABC HexagonRowColumn555.cols_left1)) ((2 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal5_case_5_5_row_2_1_0 : (((-1 : ℤ) ^ (leftScaleBit 5 5 5).val * positiveScale (leftScaleExponent 5 5 5)) •
      (rowColumnMul HexagonRowColumn555.rows_assocABC HexagonRowColumn555.cols_left0)) ((2 : Fin 4), (1 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 5 5 5) • (rowColumnMul HexagonRowColumn555.rows_innerRightABC HexagonRowColumn555.cols_left1)) ((2 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal5_case_5_5_row_2_1_1 : (((-1 : ℤ) ^ (leftScaleBit 5 5 5).val * positiveScale (leftScaleExponent 5 5 5)) •
      (rowColumnMul HexagonRowColumn555.rows_assocABC HexagonRowColumn555.cols_left0)) ((2 : Fin 4), (1 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 5 5 5) • (rowColumnMul HexagonRowColumn555.rows_innerRightABC HexagonRowColumn555.cols_left1)) ((2 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal5_case_5_5_row_2_2_0 : (((-1 : ℤ) ^ (leftScaleBit 5 5 5).val * positiveScale (leftScaleExponent 5 5 5)) •
      (rowColumnMul HexagonRowColumn555.rows_assocABC HexagonRowColumn555.cols_left0)) ((2 : Fin 4), (2 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 5 5 5) • (rowColumnMul HexagonRowColumn555.rows_innerRightABC HexagonRowColumn555.cols_left1)) ((2 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal5_case_5_5_row_2_2_1 : (((-1 : ℤ) ^ (leftScaleBit 5 5 5).val * positiveScale (leftScaleExponent 5 5 5)) •
      (rowColumnMul HexagonRowColumn555.rows_assocABC HexagonRowColumn555.cols_left0)) ((2 : Fin 4), (2 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 5 5 5) • (rowColumnMul HexagonRowColumn555.rows_innerRightABC HexagonRowColumn555.cols_left1)) ((2 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal5_case_5_5_row_2_3_0 : (((-1 : ℤ) ^ (leftScaleBit 5 5 5).val * positiveScale (leftScaleExponent 5 5 5)) •
      (rowColumnMul HexagonRowColumn555.rows_assocABC HexagonRowColumn555.cols_left0)) ((2 : Fin 4), (3 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 5 5 5) • (rowColumnMul HexagonRowColumn555.rows_innerRightABC HexagonRowColumn555.cols_left1)) ((2 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal5_case_5_5_row_2_3_1 : (((-1 : ℤ) ^ (leftScaleBit 5 5 5).val * positiveScale (leftScaleExponent 5 5 5)) •
      (rowColumnMul HexagonRowColumn555.rows_assocABC HexagonRowColumn555.cols_left0)) ((2 : Fin 4), (3 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 5 5 5) • (rowColumnMul HexagonRowColumn555.rows_innerRightABC HexagonRowColumn555.cols_left1)) ((2 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal5_case_5_5_row_3_0_0 : (((-1 : ℤ) ^ (leftScaleBit 5 5 5).val * positiveScale (leftScaleExponent 5 5 5)) •
      (rowColumnMul HexagonRowColumn555.rows_assocABC HexagonRowColumn555.cols_left0)) ((3 : Fin 4), (0 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 5 5 5) • (rowColumnMul HexagonRowColumn555.rows_innerRightABC HexagonRowColumn555.cols_left1)) ((3 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal5_case_5_5_row_3_0_1 : (((-1 : ℤ) ^ (leftScaleBit 5 5 5).val * positiveScale (leftScaleExponent 5 5 5)) •
      (rowColumnMul HexagonRowColumn555.rows_assocABC HexagonRowColumn555.cols_left0)) ((3 : Fin 4), (0 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 5 5 5) • (rowColumnMul HexagonRowColumn555.rows_innerRightABC HexagonRowColumn555.cols_left1)) ((3 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal5_case_5_5_row_3_1_0 : (((-1 : ℤ) ^ (leftScaleBit 5 5 5).val * positiveScale (leftScaleExponent 5 5 5)) •
      (rowColumnMul HexagonRowColumn555.rows_assocABC HexagonRowColumn555.cols_left0)) ((3 : Fin 4), (1 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 5 5 5) • (rowColumnMul HexagonRowColumn555.rows_innerRightABC HexagonRowColumn555.cols_left1)) ((3 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal5_case_5_5_row_3_1_1 : (((-1 : ℤ) ^ (leftScaleBit 5 5 5).val * positiveScale (leftScaleExponent 5 5 5)) •
      (rowColumnMul HexagonRowColumn555.rows_assocABC HexagonRowColumn555.cols_left0)) ((3 : Fin 4), (1 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 5 5 5) • (rowColumnMul HexagonRowColumn555.rows_innerRightABC HexagonRowColumn555.cols_left1)) ((3 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal5_case_5_5_row_3_2_0 : (((-1 : ℤ) ^ (leftScaleBit 5 5 5).val * positiveScale (leftScaleExponent 5 5 5)) •
      (rowColumnMul HexagonRowColumn555.rows_assocABC HexagonRowColumn555.cols_left0)) ((3 : Fin 4), (2 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 5 5 5) • (rowColumnMul HexagonRowColumn555.rows_innerRightABC HexagonRowColumn555.cols_left1)) ((3 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal5_case_5_5_row_3_2_1 : (((-1 : ℤ) ^ (leftScaleBit 5 5 5).val * positiveScale (leftScaleExponent 5 5 5)) •
      (rowColumnMul HexagonRowColumn555.rows_assocABC HexagonRowColumn555.cols_left0)) ((3 : Fin 4), (2 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 5 5 5) • (rowColumnMul HexagonRowColumn555.rows_innerRightABC HexagonRowColumn555.cols_left1)) ((3 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal5_case_5_5_row_3_3_0 : (((-1 : ℤ) ^ (leftScaleBit 5 5 5).val * positiveScale (leftScaleExponent 5 5 5)) •
      (rowColumnMul HexagonRowColumn555.rows_assocABC HexagonRowColumn555.cols_left0)) ((3 : Fin 4), (3 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 5 5 5) • (rowColumnMul HexagonRowColumn555.rows_innerRightABC HexagonRowColumn555.cols_left1)) ((3 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal5_case_5_5_row_3_3_1 : (((-1 : ℤ) ^ (leftScaleBit 5 5 5).val * positiveScale (leftScaleExponent 5 5 5)) •
      (rowColumnMul HexagonRowColumn555.rows_assocABC HexagonRowColumn555.cols_left0)) ((3 : Fin 4), (3 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 5 5 5) • (rowColumnMul HexagonRowColumn555.rows_innerRightABC HexagonRowColumn555.cols_left1)) ((3 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal5_case_5_5_checked : ((-1 : ℤ) ^ (leftScaleBit 5 5 5).val * positiveScale (leftScaleExponent 5 5 5)) •
      (rowColumnMul HexagonRowColumn555.rows_assocABC HexagonRowColumn555.cols_left0) = negativeScale (leftScaleExponent 5 5 5) • (rowColumnMul HexagonRowColumn555.rows_innerRightABC HexagonRowColumn555.cols_left1) := by
  funext r
  fin_cases r
  · exact leftFinal5_case_5_5_row_0_0_0
  · exact leftFinal5_case_5_5_row_0_0_1
  · exact leftFinal5_case_5_5_row_0_1_0
  · exact leftFinal5_case_5_5_row_0_1_1
  · exact leftFinal5_case_5_5_row_0_2_0
  · exact leftFinal5_case_5_5_row_0_2_1
  · exact leftFinal5_case_5_5_row_0_3_0
  · exact leftFinal5_case_5_5_row_0_3_1
  · exact leftFinal5_case_5_5_row_1_0_0
  · exact leftFinal5_case_5_5_row_1_0_1
  · exact leftFinal5_case_5_5_row_1_1_0
  · exact leftFinal5_case_5_5_row_1_1_1
  · exact leftFinal5_case_5_5_row_1_2_0
  · exact leftFinal5_case_5_5_row_1_2_1
  · exact leftFinal5_case_5_5_row_1_3_0
  · exact leftFinal5_case_5_5_row_1_3_1
  · exact leftFinal5_case_5_5_row_2_0_0
  · exact leftFinal5_case_5_5_row_2_0_1
  · exact leftFinal5_case_5_5_row_2_1_0
  · exact leftFinal5_case_5_5_row_2_1_1
  · exact leftFinal5_case_5_5_row_2_2_0
  · exact leftFinal5_case_5_5_row_2_2_1
  · exact leftFinal5_case_5_5_row_2_3_0
  · exact leftFinal5_case_5_5_row_2_3_1
  · exact leftFinal5_case_5_5_row_3_0_0
  · exact leftFinal5_case_5_5_row_3_0_1
  · exact leftFinal5_case_5_5_row_3_1_0
  · exact leftFinal5_case_5_5_row_3_1_1
  · exact leftFinal5_case_5_5_row_3_2_0
  · exact leftFinal5_case_5_5_row_3_2_1
  · exact leftFinal5_case_5_5_row_3_3_0
  · exact leftFinal5_case_5_5_row_3_3_1

set_option backward.isDefEq.respectTransparency false in
theorem leftFinal5_case_5_5 : ((-1 : ℤ) ^ (leftScaleBit 5 5 5).val * positiveScale (leftScaleExponent 5 5 5)) •
      (associatorZ 5 5 5 * left0Middle5 5 5) = negativeScale (leftScaleExponent 5 5 5) • (innerRightZ 5 5 5 * left1Middle5 5 5) := by
  simpa only [HexagonAtoms555.assocABC_eq,
    HexagonAtoms555.outerABC_eq,
    HexagonAtoms555.assocBAC_eq,
    HexagonAtoms555.innerABC_eq,
    HexagonAtoms555.innerRightABC_eq,
    HexagonAtoms555.inverseACB_eq,
    HexagonAtoms555.innerACB_eq,
    HexagonAtoms555.assocBCA_eq,
    HexagonAtoms555.innerRightBAC_eq,
    HexagonAtoms555.assocCAB_eq,
    HexagonAtoms555.outerLeftABC_eq,
    HexagonRowColumn555.assocBAC_alias,
    HexagonRowColumn555.innerACB_alias,
    HexagonRowColumn555.assocBCA_alias,
    HexagonRowColumn555.innerRightBAC_alias,
    HexagonRowColumn555.assocCAB_alias,
    HexagonRowColumn555.product0_eq,
    HexagonRowColumn555.product1_eq,
    HexagonRowColumn555.product2_eq,
    HexagonRowColumn555.product3_eq,
    HexagonRowColumn555.product4_eq,
    HexagonRowColumn555.product5_eq,
    HexagonRowColumn555.product6_eq,
    HexagonRowColumn555.product7_eq] using leftFinal5_case_5_5_checked

private theorem rightFinal5_case_5_5_row_0_0_0 : (((-1 : ℤ) ^ (rightScaleBit 5 5 5).val * positiveScale (rightScaleExponent 5 5 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 5 5 : ℤ)) • HexagonAtoms555.outerLeftABC) ((0 : Fin 4), (0 : Fin 4), (0 : Fin 2)) = (negativeScale (rightScaleExponent 5 5 5) • (rowColumnMul HexagonRowColumn555.rows_assocABC HexagonRowColumn555.cols_right2)) ((0 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal5_case_5_5_row_0_0_1 : (((-1 : ℤ) ^ (rightScaleBit 5 5 5).val * positiveScale (rightScaleExponent 5 5 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 5 5 : ℤ)) • HexagonAtoms555.outerLeftABC) ((0 : Fin 4), (0 : Fin 4), (1 : Fin 2)) = (negativeScale (rightScaleExponent 5 5 5) • (rowColumnMul HexagonRowColumn555.rows_assocABC HexagonRowColumn555.cols_right2)) ((0 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal5_case_5_5_row_0_1_0 : (((-1 : ℤ) ^ (rightScaleBit 5 5 5).val * positiveScale (rightScaleExponent 5 5 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 5 5 : ℤ)) • HexagonAtoms555.outerLeftABC) ((0 : Fin 4), (1 : Fin 4), (0 : Fin 2)) = (negativeScale (rightScaleExponent 5 5 5) • (rowColumnMul HexagonRowColumn555.rows_assocABC HexagonRowColumn555.cols_right2)) ((0 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal5_case_5_5_row_0_1_1 : (((-1 : ℤ) ^ (rightScaleBit 5 5 5).val * positiveScale (rightScaleExponent 5 5 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 5 5 : ℤ)) • HexagonAtoms555.outerLeftABC) ((0 : Fin 4), (1 : Fin 4), (1 : Fin 2)) = (negativeScale (rightScaleExponent 5 5 5) • (rowColumnMul HexagonRowColumn555.rows_assocABC HexagonRowColumn555.cols_right2)) ((0 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal5_case_5_5_row_0_2_0 : (((-1 : ℤ) ^ (rightScaleBit 5 5 5).val * positiveScale (rightScaleExponent 5 5 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 5 5 : ℤ)) • HexagonAtoms555.outerLeftABC) ((0 : Fin 4), (2 : Fin 4), (0 : Fin 2)) = (negativeScale (rightScaleExponent 5 5 5) • (rowColumnMul HexagonRowColumn555.rows_assocABC HexagonRowColumn555.cols_right2)) ((0 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal5_case_5_5_row_0_2_1 : (((-1 : ℤ) ^ (rightScaleBit 5 5 5).val * positiveScale (rightScaleExponent 5 5 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 5 5 : ℤ)) • HexagonAtoms555.outerLeftABC) ((0 : Fin 4), (2 : Fin 4), (1 : Fin 2)) = (negativeScale (rightScaleExponent 5 5 5) • (rowColumnMul HexagonRowColumn555.rows_assocABC HexagonRowColumn555.cols_right2)) ((0 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal5_case_5_5_row_0_3_0 : (((-1 : ℤ) ^ (rightScaleBit 5 5 5).val * positiveScale (rightScaleExponent 5 5 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 5 5 : ℤ)) • HexagonAtoms555.outerLeftABC) ((0 : Fin 4), (3 : Fin 4), (0 : Fin 2)) = (negativeScale (rightScaleExponent 5 5 5) • (rowColumnMul HexagonRowColumn555.rows_assocABC HexagonRowColumn555.cols_right2)) ((0 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal5_case_5_5_row_0_3_1 : (((-1 : ℤ) ^ (rightScaleBit 5 5 5).val * positiveScale (rightScaleExponent 5 5 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 5 5 : ℤ)) • HexagonAtoms555.outerLeftABC) ((0 : Fin 4), (3 : Fin 4), (1 : Fin 2)) = (negativeScale (rightScaleExponent 5 5 5) • (rowColumnMul HexagonRowColumn555.rows_assocABC HexagonRowColumn555.cols_right2)) ((0 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal5_case_5_5_row_1_0_0 : (((-1 : ℤ) ^ (rightScaleBit 5 5 5).val * positiveScale (rightScaleExponent 5 5 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 5 5 : ℤ)) • HexagonAtoms555.outerLeftABC) ((1 : Fin 4), (0 : Fin 4), (0 : Fin 2)) = (negativeScale (rightScaleExponent 5 5 5) • (rowColumnMul HexagonRowColumn555.rows_assocABC HexagonRowColumn555.cols_right2)) ((1 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal5_case_5_5_row_1_0_1 : (((-1 : ℤ) ^ (rightScaleBit 5 5 5).val * positiveScale (rightScaleExponent 5 5 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 5 5 : ℤ)) • HexagonAtoms555.outerLeftABC) ((1 : Fin 4), (0 : Fin 4), (1 : Fin 2)) = (negativeScale (rightScaleExponent 5 5 5) • (rowColumnMul HexagonRowColumn555.rows_assocABC HexagonRowColumn555.cols_right2)) ((1 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal5_case_5_5_row_1_1_0 : (((-1 : ℤ) ^ (rightScaleBit 5 5 5).val * positiveScale (rightScaleExponent 5 5 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 5 5 : ℤ)) • HexagonAtoms555.outerLeftABC) ((1 : Fin 4), (1 : Fin 4), (0 : Fin 2)) = (negativeScale (rightScaleExponent 5 5 5) • (rowColumnMul HexagonRowColumn555.rows_assocABC HexagonRowColumn555.cols_right2)) ((1 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal5_case_5_5_row_1_1_1 : (((-1 : ℤ) ^ (rightScaleBit 5 5 5).val * positiveScale (rightScaleExponent 5 5 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 5 5 : ℤ)) • HexagonAtoms555.outerLeftABC) ((1 : Fin 4), (1 : Fin 4), (1 : Fin 2)) = (negativeScale (rightScaleExponent 5 5 5) • (rowColumnMul HexagonRowColumn555.rows_assocABC HexagonRowColumn555.cols_right2)) ((1 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal5_case_5_5_row_1_2_0 : (((-1 : ℤ) ^ (rightScaleBit 5 5 5).val * positiveScale (rightScaleExponent 5 5 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 5 5 : ℤ)) • HexagonAtoms555.outerLeftABC) ((1 : Fin 4), (2 : Fin 4), (0 : Fin 2)) = (negativeScale (rightScaleExponent 5 5 5) • (rowColumnMul HexagonRowColumn555.rows_assocABC HexagonRowColumn555.cols_right2)) ((1 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal5_case_5_5_row_1_2_1 : (((-1 : ℤ) ^ (rightScaleBit 5 5 5).val * positiveScale (rightScaleExponent 5 5 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 5 5 : ℤ)) • HexagonAtoms555.outerLeftABC) ((1 : Fin 4), (2 : Fin 4), (1 : Fin 2)) = (negativeScale (rightScaleExponent 5 5 5) • (rowColumnMul HexagonRowColumn555.rows_assocABC HexagonRowColumn555.cols_right2)) ((1 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal5_case_5_5_row_1_3_0 : (((-1 : ℤ) ^ (rightScaleBit 5 5 5).val * positiveScale (rightScaleExponent 5 5 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 5 5 : ℤ)) • HexagonAtoms555.outerLeftABC) ((1 : Fin 4), (3 : Fin 4), (0 : Fin 2)) = (negativeScale (rightScaleExponent 5 5 5) • (rowColumnMul HexagonRowColumn555.rows_assocABC HexagonRowColumn555.cols_right2)) ((1 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal5_case_5_5_row_1_3_1 : (((-1 : ℤ) ^ (rightScaleBit 5 5 5).val * positiveScale (rightScaleExponent 5 5 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 5 5 : ℤ)) • HexagonAtoms555.outerLeftABC) ((1 : Fin 4), (3 : Fin 4), (1 : Fin 2)) = (negativeScale (rightScaleExponent 5 5 5) • (rowColumnMul HexagonRowColumn555.rows_assocABC HexagonRowColumn555.cols_right2)) ((1 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal5_case_5_5_row_2_0_0 : (((-1 : ℤ) ^ (rightScaleBit 5 5 5).val * positiveScale (rightScaleExponent 5 5 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 5 5 : ℤ)) • HexagonAtoms555.outerLeftABC) ((2 : Fin 4), (0 : Fin 4), (0 : Fin 2)) = (negativeScale (rightScaleExponent 5 5 5) • (rowColumnMul HexagonRowColumn555.rows_assocABC HexagonRowColumn555.cols_right2)) ((2 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal5_case_5_5_row_2_0_1 : (((-1 : ℤ) ^ (rightScaleBit 5 5 5).val * positiveScale (rightScaleExponent 5 5 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 5 5 : ℤ)) • HexagonAtoms555.outerLeftABC) ((2 : Fin 4), (0 : Fin 4), (1 : Fin 2)) = (negativeScale (rightScaleExponent 5 5 5) • (rowColumnMul HexagonRowColumn555.rows_assocABC HexagonRowColumn555.cols_right2)) ((2 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal5_case_5_5_row_2_1_0 : (((-1 : ℤ) ^ (rightScaleBit 5 5 5).val * positiveScale (rightScaleExponent 5 5 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 5 5 : ℤ)) • HexagonAtoms555.outerLeftABC) ((2 : Fin 4), (1 : Fin 4), (0 : Fin 2)) = (negativeScale (rightScaleExponent 5 5 5) • (rowColumnMul HexagonRowColumn555.rows_assocABC HexagonRowColumn555.cols_right2)) ((2 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal5_case_5_5_row_2_1_1 : (((-1 : ℤ) ^ (rightScaleBit 5 5 5).val * positiveScale (rightScaleExponent 5 5 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 5 5 : ℤ)) • HexagonAtoms555.outerLeftABC) ((2 : Fin 4), (1 : Fin 4), (1 : Fin 2)) = (negativeScale (rightScaleExponent 5 5 5) • (rowColumnMul HexagonRowColumn555.rows_assocABC HexagonRowColumn555.cols_right2)) ((2 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal5_case_5_5_row_2_2_0 : (((-1 : ℤ) ^ (rightScaleBit 5 5 5).val * positiveScale (rightScaleExponent 5 5 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 5 5 : ℤ)) • HexagonAtoms555.outerLeftABC) ((2 : Fin 4), (2 : Fin 4), (0 : Fin 2)) = (negativeScale (rightScaleExponent 5 5 5) • (rowColumnMul HexagonRowColumn555.rows_assocABC HexagonRowColumn555.cols_right2)) ((2 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal5_case_5_5_row_2_2_1 : (((-1 : ℤ) ^ (rightScaleBit 5 5 5).val * positiveScale (rightScaleExponent 5 5 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 5 5 : ℤ)) • HexagonAtoms555.outerLeftABC) ((2 : Fin 4), (2 : Fin 4), (1 : Fin 2)) = (negativeScale (rightScaleExponent 5 5 5) • (rowColumnMul HexagonRowColumn555.rows_assocABC HexagonRowColumn555.cols_right2)) ((2 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal5_case_5_5_row_2_3_0 : (((-1 : ℤ) ^ (rightScaleBit 5 5 5).val * positiveScale (rightScaleExponent 5 5 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 5 5 : ℤ)) • HexagonAtoms555.outerLeftABC) ((2 : Fin 4), (3 : Fin 4), (0 : Fin 2)) = (negativeScale (rightScaleExponent 5 5 5) • (rowColumnMul HexagonRowColumn555.rows_assocABC HexagonRowColumn555.cols_right2)) ((2 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal5_case_5_5_row_2_3_1 : (((-1 : ℤ) ^ (rightScaleBit 5 5 5).val * positiveScale (rightScaleExponent 5 5 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 5 5 : ℤ)) • HexagonAtoms555.outerLeftABC) ((2 : Fin 4), (3 : Fin 4), (1 : Fin 2)) = (negativeScale (rightScaleExponent 5 5 5) • (rowColumnMul HexagonRowColumn555.rows_assocABC HexagonRowColumn555.cols_right2)) ((2 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal5_case_5_5_row_3_0_0 : (((-1 : ℤ) ^ (rightScaleBit 5 5 5).val * positiveScale (rightScaleExponent 5 5 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 5 5 : ℤ)) • HexagonAtoms555.outerLeftABC) ((3 : Fin 4), (0 : Fin 4), (0 : Fin 2)) = (negativeScale (rightScaleExponent 5 5 5) • (rowColumnMul HexagonRowColumn555.rows_assocABC HexagonRowColumn555.cols_right2)) ((3 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal5_case_5_5_row_3_0_1 : (((-1 : ℤ) ^ (rightScaleBit 5 5 5).val * positiveScale (rightScaleExponent 5 5 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 5 5 : ℤ)) • HexagonAtoms555.outerLeftABC) ((3 : Fin 4), (0 : Fin 4), (1 : Fin 2)) = (negativeScale (rightScaleExponent 5 5 5) • (rowColumnMul HexagonRowColumn555.rows_assocABC HexagonRowColumn555.cols_right2)) ((3 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal5_case_5_5_row_3_1_0 : (((-1 : ℤ) ^ (rightScaleBit 5 5 5).val * positiveScale (rightScaleExponent 5 5 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 5 5 : ℤ)) • HexagonAtoms555.outerLeftABC) ((3 : Fin 4), (1 : Fin 4), (0 : Fin 2)) = (negativeScale (rightScaleExponent 5 5 5) • (rowColumnMul HexagonRowColumn555.rows_assocABC HexagonRowColumn555.cols_right2)) ((3 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal5_case_5_5_row_3_1_1 : (((-1 : ℤ) ^ (rightScaleBit 5 5 5).val * positiveScale (rightScaleExponent 5 5 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 5 5 : ℤ)) • HexagonAtoms555.outerLeftABC) ((3 : Fin 4), (1 : Fin 4), (1 : Fin 2)) = (negativeScale (rightScaleExponent 5 5 5) • (rowColumnMul HexagonRowColumn555.rows_assocABC HexagonRowColumn555.cols_right2)) ((3 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal5_case_5_5_row_3_2_0 : (((-1 : ℤ) ^ (rightScaleBit 5 5 5).val * positiveScale (rightScaleExponent 5 5 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 5 5 : ℤ)) • HexagonAtoms555.outerLeftABC) ((3 : Fin 4), (2 : Fin 4), (0 : Fin 2)) = (negativeScale (rightScaleExponent 5 5 5) • (rowColumnMul HexagonRowColumn555.rows_assocABC HexagonRowColumn555.cols_right2)) ((3 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal5_case_5_5_row_3_2_1 : (((-1 : ℤ) ^ (rightScaleBit 5 5 5).val * positiveScale (rightScaleExponent 5 5 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 5 5 : ℤ)) • HexagonAtoms555.outerLeftABC) ((3 : Fin 4), (2 : Fin 4), (1 : Fin 2)) = (negativeScale (rightScaleExponent 5 5 5) • (rowColumnMul HexagonRowColumn555.rows_assocABC HexagonRowColumn555.cols_right2)) ((3 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal5_case_5_5_row_3_3_0 : (((-1 : ℤ) ^ (rightScaleBit 5 5 5).val * positiveScale (rightScaleExponent 5 5 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 5 5 : ℤ)) • HexagonAtoms555.outerLeftABC) ((3 : Fin 4), (3 : Fin 4), (0 : Fin 2)) = (negativeScale (rightScaleExponent 5 5 5) • (rowColumnMul HexagonRowColumn555.rows_assocABC HexagonRowColumn555.cols_right2)) ((3 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal5_case_5_5_row_3_3_1 : (((-1 : ℤ) ^ (rightScaleBit 5 5 5).val * positiveScale (rightScaleExponent 5 5 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 5 5 : ℤ)) • HexagonAtoms555.outerLeftABC) ((3 : Fin 4), (3 : Fin 4), (1 : Fin 2)) = (negativeScale (rightScaleExponent 5 5 5) • (rowColumnMul HexagonRowColumn555.rows_assocABC HexagonRowColumn555.cols_right2)) ((3 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal5_case_5_5_checked : ((-1 : ℤ) ^ (rightScaleBit 5 5 5).val * positiveScale (rightScaleExponent 5 5 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 5 5 : ℤ)) • HexagonAtoms555.outerLeftABC = negativeScale (rightScaleExponent 5 5 5) • (rowColumnMul HexagonRowColumn555.rows_assocABC HexagonRowColumn555.cols_right2) := by
  funext r
  fin_cases r
  · exact rightFinal5_case_5_5_row_0_0_0
  · exact rightFinal5_case_5_5_row_0_0_1
  · exact rightFinal5_case_5_5_row_0_1_0
  · exact rightFinal5_case_5_5_row_0_1_1
  · exact rightFinal5_case_5_5_row_0_2_0
  · exact rightFinal5_case_5_5_row_0_2_1
  · exact rightFinal5_case_5_5_row_0_3_0
  · exact rightFinal5_case_5_5_row_0_3_1
  · exact rightFinal5_case_5_5_row_1_0_0
  · exact rightFinal5_case_5_5_row_1_0_1
  · exact rightFinal5_case_5_5_row_1_1_0
  · exact rightFinal5_case_5_5_row_1_1_1
  · exact rightFinal5_case_5_5_row_1_2_0
  · exact rightFinal5_case_5_5_row_1_2_1
  · exact rightFinal5_case_5_5_row_1_3_0
  · exact rightFinal5_case_5_5_row_1_3_1
  · exact rightFinal5_case_5_5_row_2_0_0
  · exact rightFinal5_case_5_5_row_2_0_1
  · exact rightFinal5_case_5_5_row_2_1_0
  · exact rightFinal5_case_5_5_row_2_1_1
  · exact rightFinal5_case_5_5_row_2_2_0
  · exact rightFinal5_case_5_5_row_2_2_1
  · exact rightFinal5_case_5_5_row_2_3_0
  · exact rightFinal5_case_5_5_row_2_3_1
  · exact rightFinal5_case_5_5_row_3_0_0
  · exact rightFinal5_case_5_5_row_3_0_1
  · exact rightFinal5_case_5_5_row_3_1_0
  · exact rightFinal5_case_5_5_row_3_1_1
  · exact rightFinal5_case_5_5_row_3_2_0
  · exact rightFinal5_case_5_5_row_3_2_1
  · exact rightFinal5_case_5_5_row_3_3_0
  · exact rightFinal5_case_5_5_row_3_3_1

set_option backward.isDefEq.respectTransparency false in
theorem rightFinal5_case_5_5 : ((-1 : ℤ) ^ (rightScaleBit 5 5 5).val * positiveScale (rightScaleExponent 5 5 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 5 5 : ℤ)) • outerLeftZ 5 5 5 = negativeScale (rightScaleExponent 5 5 5) • (associatorZ 5 5 5 * right2Middle5 5 5) := by
  simpa only [HexagonAtoms555.assocABC_eq,
    HexagonAtoms555.outerABC_eq,
    HexagonAtoms555.assocBAC_eq,
    HexagonAtoms555.innerABC_eq,
    HexagonAtoms555.innerRightABC_eq,
    HexagonAtoms555.inverseACB_eq,
    HexagonAtoms555.innerACB_eq,
    HexagonAtoms555.assocBCA_eq,
    HexagonAtoms555.innerRightBAC_eq,
    HexagonAtoms555.assocCAB_eq,
    HexagonAtoms555.outerLeftABC_eq,
    HexagonRowColumn555.assocBAC_alias,
    HexagonRowColumn555.innerACB_alias,
    HexagonRowColumn555.assocBCA_alias,
    HexagonRowColumn555.innerRightBAC_alias,
    HexagonRowColumn555.assocCAB_alias,
    HexagonRowColumn555.product0_eq,
    HexagonRowColumn555.product1_eq,
    HexagonRowColumn555.product2_eq,
    HexagonRowColumn555.product3_eq,
    HexagonRowColumn555.product4_eq,
    HexagonRowColumn555.product5_eq,
    HexagonRowColumn555.product6_eq,
    HexagonRowColumn555.product7_eq] using rightFinal5_case_5_5_checked

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonCases5
