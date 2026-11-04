import RMod.BrundanEllis.StackingReferenceHexagonMiddle6
import RMod.BrundanEllis.StackingReferenceSparseMatrixCheck
import RMod.BrundanEllis.StackingReferenceHexagonAtoms675
import RMod.BrundanEllis.StackingReferenceHexagonRowColumn675

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

private theorem left0Middle6_eq_case_7_5_row_0_0_0 : (left0Middle6 7 5) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms675.assocABC) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_7_5_row_0_0_1 : (left0Middle6 7 5) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms675.assocABC) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_7_5_row_0_0_2 : (left0Middle6 7 5) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms675.assocABC) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_7_5_row_0_0_3 : (left0Middle6 7 5) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms675.assocABC) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_7_5_row_0_1_0 : (left0Middle6 7 5) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms675.assocABC) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_7_5_row_0_1_1 : (left0Middle6 7 5) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms675.assocABC) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_7_5_row_0_1_2 : (left0Middle6 7 5) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms675.assocABC) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_7_5_row_0_1_3 : (left0Middle6 7 5) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms675.assocABC) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_7_5_row_1_0_0 : (left0Middle6 7 5) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms675.assocABC) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_7_5_row_1_0_1 : (left0Middle6 7 5) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms675.assocABC) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_7_5_row_1_0_2 : (left0Middle6 7 5) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms675.assocABC) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_7_5_row_1_0_3 : (left0Middle6 7 5) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms675.assocABC) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_7_5_row_1_1_0 : (left0Middle6 7 5) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms675.assocABC) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_7_5_row_1_1_1 : (left0Middle6 7 5) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms675.assocABC) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_7_5_row_1_1_2 : (left0Middle6 7 5) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms675.assocABC) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_7_5_row_1_1_3 : (left0Middle6 7 5) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms675.assocABC) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_7_5_checked : left0Middle6 7 5 = HexagonAtoms675.assocABC := by
  funext r
  fin_cases r
  · exact left0Middle6_eq_case_7_5_row_0_0_0
  · exact left0Middle6_eq_case_7_5_row_0_0_1
  · exact left0Middle6_eq_case_7_5_row_0_0_2
  · exact left0Middle6_eq_case_7_5_row_0_0_3
  · exact left0Middle6_eq_case_7_5_row_0_1_0
  · exact left0Middle6_eq_case_7_5_row_0_1_1
  · exact left0Middle6_eq_case_7_5_row_0_1_2
  · exact left0Middle6_eq_case_7_5_row_0_1_3
  · exact left0Middle6_eq_case_7_5_row_1_0_0
  · exact left0Middle6_eq_case_7_5_row_1_0_1
  · exact left0Middle6_eq_case_7_5_row_1_0_2
  · exact left0Middle6_eq_case_7_5_row_1_0_3
  · exact left0Middle6_eq_case_7_5_row_1_1_0
  · exact left0Middle6_eq_case_7_5_row_1_1_1
  · exact left0Middle6_eq_case_7_5_row_1_1_2
  · exact left0Middle6_eq_case_7_5_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem left0Middle6_eq_case_7_5 : left0Middle6 7 5 = outerRightZ 6 7 5 * associatorZ 6 7 5 := by
  simpa only [HexagonAtoms675.assocABC_eq,
    HexagonAtoms675.outerABC_eq,
    HexagonAtoms675.assocBAC_eq,
    HexagonAtoms675.innerABC_eq,
    HexagonAtoms675.innerRightABC_eq,
    HexagonAtoms675.inverseACB_eq,
    HexagonAtoms675.innerACB_eq,
    HexagonAtoms675.assocBCA_eq,
    HexagonAtoms675.innerRightBAC_eq,
    HexagonAtoms675.assocCAB_eq,
    HexagonAtoms675.outerLeftABC_eq,
    HexagonRowColumn675.product0_eq,
    HexagonRowColumn675.product1_eq,
    HexagonRowColumn675.product2_eq,
    HexagonRowColumn675.product3_eq,
    HexagonRowColumn675.product4_eq,
    HexagonRowColumn675.product5_eq,
    HexagonRowColumn675.product6_eq,
    HexagonRowColumn675.product7_eq] using left0Middle6_eq_case_7_5_checked

private theorem left1Middle6_eq_case_7_5_row_0_0_0 : (left1Middle6 7 5) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn675.rows_assocBAC HexagonRowColumn675.cols_innerABC) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_7_5_row_0_0_1 : (left1Middle6 7 5) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn675.rows_assocBAC HexagonRowColumn675.cols_innerABC) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_7_5_row_0_0_2 : (left1Middle6 7 5) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn675.rows_assocBAC HexagonRowColumn675.cols_innerABC) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_7_5_row_0_0_3 : (left1Middle6 7 5) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn675.rows_assocBAC HexagonRowColumn675.cols_innerABC) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_7_5_row_0_1_0 : (left1Middle6 7 5) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn675.rows_assocBAC HexagonRowColumn675.cols_innerABC) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_7_5_row_0_1_1 : (left1Middle6 7 5) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn675.rows_assocBAC HexagonRowColumn675.cols_innerABC) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_7_5_row_0_1_2 : (left1Middle6 7 5) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn675.rows_assocBAC HexagonRowColumn675.cols_innerABC) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_7_5_row_0_1_3 : (left1Middle6 7 5) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn675.rows_assocBAC HexagonRowColumn675.cols_innerABC) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_7_5_row_1_0_0 : (left1Middle6 7 5) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn675.rows_assocBAC HexagonRowColumn675.cols_innerABC) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_7_5_row_1_0_1 : (left1Middle6 7 5) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn675.rows_assocBAC HexagonRowColumn675.cols_innerABC) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_7_5_row_1_0_2 : (left1Middle6 7 5) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn675.rows_assocBAC HexagonRowColumn675.cols_innerABC) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_7_5_row_1_0_3 : (left1Middle6 7 5) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn675.rows_assocBAC HexagonRowColumn675.cols_innerABC) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_7_5_row_1_1_0 : (left1Middle6 7 5) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn675.rows_assocBAC HexagonRowColumn675.cols_innerABC) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_7_5_row_1_1_1 : (left1Middle6 7 5) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn675.rows_assocBAC HexagonRowColumn675.cols_innerABC) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_7_5_row_1_1_2 : (left1Middle6 7 5) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn675.rows_assocBAC HexagonRowColumn675.cols_innerABC) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_7_5_row_1_1_3 : (left1Middle6 7 5) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn675.rows_assocBAC HexagonRowColumn675.cols_innerABC) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_7_5_checked : left1Middle6 7 5 = rowColumnMul HexagonRowColumn675.rows_assocBAC HexagonRowColumn675.cols_innerABC := by
  funext r
  fin_cases r
  · exact left1Middle6_eq_case_7_5_row_0_0_0
  · exact left1Middle6_eq_case_7_5_row_0_0_1
  · exact left1Middle6_eq_case_7_5_row_0_0_2
  · exact left1Middle6_eq_case_7_5_row_0_0_3
  · exact left1Middle6_eq_case_7_5_row_0_1_0
  · exact left1Middle6_eq_case_7_5_row_0_1_1
  · exact left1Middle6_eq_case_7_5_row_0_1_2
  · exact left1Middle6_eq_case_7_5_row_0_1_3
  · exact left1Middle6_eq_case_7_5_row_1_0_0
  · exact left1Middle6_eq_case_7_5_row_1_0_1
  · exact left1Middle6_eq_case_7_5_row_1_0_2
  · exact left1Middle6_eq_case_7_5_row_1_0_3
  · exact left1Middle6_eq_case_7_5_row_1_1_0
  · exact left1Middle6_eq_case_7_5_row_1_1_1
  · exact left1Middle6_eq_case_7_5_row_1_1_2
  · exact left1Middle6_eq_case_7_5_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem left1Middle6_eq_case_7_5 : left1Middle6 7 5 = associatorZ 7 6 5 * innerLeftZ 6 7 5 := by
  simpa only [HexagonAtoms675.assocABC_eq,
    HexagonAtoms675.outerABC_eq,
    HexagonAtoms675.assocBAC_eq,
    HexagonAtoms675.innerABC_eq,
    HexagonAtoms675.innerRightABC_eq,
    HexagonAtoms675.inverseACB_eq,
    HexagonAtoms675.innerACB_eq,
    HexagonAtoms675.assocBCA_eq,
    HexagonAtoms675.innerRightBAC_eq,
    HexagonAtoms675.assocCAB_eq,
    HexagonAtoms675.outerLeftABC_eq,
    HexagonRowColumn675.product0_eq,
    HexagonRowColumn675.product1_eq,
    HexagonRowColumn675.product2_eq,
    HexagonRowColumn675.product3_eq,
    HexagonRowColumn675.product4_eq,
    HexagonRowColumn675.product5_eq,
    HexagonRowColumn675.product6_eq,
    HexagonRowColumn675.product7_eq] using left1Middle6_eq_case_7_5_checked

private theorem right0Middle6_eq_case_7_5_row_0_0_0 : (right0Middle6 7 5) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms675.assocABC) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_7_5_row_0_0_1 : (right0Middle6 7 5) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms675.assocABC) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_7_5_row_0_0_2 : (right0Middle6 7 5) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms675.assocABC) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_7_5_row_0_0_3 : (right0Middle6 7 5) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms675.assocABC) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_7_5_row_0_1_0 : (right0Middle6 7 5) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms675.assocABC) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_7_5_row_0_1_1 : (right0Middle6 7 5) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms675.assocABC) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_7_5_row_0_1_2 : (right0Middle6 7 5) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms675.assocABC) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_7_5_row_0_1_3 : (right0Middle6 7 5) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms675.assocABC) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_7_5_row_1_0_0 : (right0Middle6 7 5) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms675.assocABC) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_7_5_row_1_0_1 : (right0Middle6 7 5) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms675.assocABC) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_7_5_row_1_0_2 : (right0Middle6 7 5) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms675.assocABC) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_7_5_row_1_0_3 : (right0Middle6 7 5) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms675.assocABC) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_7_5_row_1_1_0 : (right0Middle6 7 5) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms675.assocABC) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_7_5_row_1_1_1 : (right0Middle6 7 5) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms675.assocABC) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_7_5_row_1_1_2 : (right0Middle6 7 5) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms675.assocABC) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_7_5_row_1_1_3 : (right0Middle6 7 5) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms675.assocABC) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_7_5_checked : right0Middle6 7 5 = HexagonAtoms675.assocABC := by
  funext r
  fin_cases r
  · exact right0Middle6_eq_case_7_5_row_0_0_0
  · exact right0Middle6_eq_case_7_5_row_0_0_1
  · exact right0Middle6_eq_case_7_5_row_0_0_2
  · exact right0Middle6_eq_case_7_5_row_0_0_3
  · exact right0Middle6_eq_case_7_5_row_0_1_0
  · exact right0Middle6_eq_case_7_5_row_0_1_1
  · exact right0Middle6_eq_case_7_5_row_0_1_2
  · exact right0Middle6_eq_case_7_5_row_0_1_3
  · exact right0Middle6_eq_case_7_5_row_1_0_0
  · exact right0Middle6_eq_case_7_5_row_1_0_1
  · exact right0Middle6_eq_case_7_5_row_1_0_2
  · exact right0Middle6_eq_case_7_5_row_1_0_3
  · exact right0Middle6_eq_case_7_5_row_1_1_0
  · exact right0Middle6_eq_case_7_5_row_1_1_1
  · exact right0Middle6_eq_case_7_5_row_1_1_2
  · exact right0Middle6_eq_case_7_5_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem right0Middle6_eq_case_7_5 : right0Middle6 7 5 = innerRightZ 6 7 5 * associatorZ 6 7 5 := by
  simpa only [HexagonAtoms675.assocABC_eq,
    HexagonAtoms675.outerABC_eq,
    HexagonAtoms675.assocBAC_eq,
    HexagonAtoms675.innerABC_eq,
    HexagonAtoms675.innerRightABC_eq,
    HexagonAtoms675.inverseACB_eq,
    HexagonAtoms675.innerACB_eq,
    HexagonAtoms675.assocBCA_eq,
    HexagonAtoms675.innerRightBAC_eq,
    HexagonAtoms675.assocCAB_eq,
    HexagonAtoms675.outerLeftABC_eq,
    HexagonRowColumn675.product0_eq,
    HexagonRowColumn675.product1_eq,
    HexagonRowColumn675.product2_eq,
    HexagonRowColumn675.product3_eq,
    HexagonRowColumn675.product4_eq,
    HexagonRowColumn675.product5_eq,
    HexagonRowColumn675.product6_eq,
    HexagonRowColumn675.product7_eq] using right0Middle6_eq_case_7_5_checked

private theorem right1Middle6_eq_case_7_5_row_0_0_0 : (right1Middle6 7 5) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn675.rows_inverseACB HexagonRowColumn675.cols_right0) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_7_5_row_0_0_1 : (right1Middle6 7 5) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn675.rows_inverseACB HexagonRowColumn675.cols_right0) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_7_5_row_0_0_2 : (right1Middle6 7 5) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn675.rows_inverseACB HexagonRowColumn675.cols_right0) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_7_5_row_0_0_3 : (right1Middle6 7 5) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn675.rows_inverseACB HexagonRowColumn675.cols_right0) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_7_5_row_0_1_0 : (right1Middle6 7 5) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn675.rows_inverseACB HexagonRowColumn675.cols_right0) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_7_5_row_0_1_1 : (right1Middle6 7 5) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn675.rows_inverseACB HexagonRowColumn675.cols_right0) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_7_5_row_0_1_2 : (right1Middle6 7 5) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn675.rows_inverseACB HexagonRowColumn675.cols_right0) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_7_5_row_0_1_3 : (right1Middle6 7 5) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn675.rows_inverseACB HexagonRowColumn675.cols_right0) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_7_5_row_1_0_0 : (right1Middle6 7 5) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn675.rows_inverseACB HexagonRowColumn675.cols_right0) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_7_5_row_1_0_1 : (right1Middle6 7 5) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn675.rows_inverseACB HexagonRowColumn675.cols_right0) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_7_5_row_1_0_2 : (right1Middle6 7 5) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn675.rows_inverseACB HexagonRowColumn675.cols_right0) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_7_5_row_1_0_3 : (right1Middle6 7 5) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn675.rows_inverseACB HexagonRowColumn675.cols_right0) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_7_5_row_1_1_0 : (right1Middle6 7 5) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn675.rows_inverseACB HexagonRowColumn675.cols_right0) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_7_5_row_1_1_1 : (right1Middle6 7 5) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn675.rows_inverseACB HexagonRowColumn675.cols_right0) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_7_5_row_1_1_2 : (right1Middle6 7 5) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn675.rows_inverseACB HexagonRowColumn675.cols_right0) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_7_5_row_1_1_3 : (right1Middle6 7 5) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn675.rows_inverseACB HexagonRowColumn675.cols_right0) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_7_5_checked : right1Middle6 7 5 = rowColumnMul HexagonRowColumn675.rows_inverseACB HexagonRowColumn675.cols_right0 := by
  funext r
  fin_cases r
  · exact right1Middle6_eq_case_7_5_row_0_0_0
  · exact right1Middle6_eq_case_7_5_row_0_0_1
  · exact right1Middle6_eq_case_7_5_row_0_0_2
  · exact right1Middle6_eq_case_7_5_row_0_0_3
  · exact right1Middle6_eq_case_7_5_row_0_1_0
  · exact right1Middle6_eq_case_7_5_row_0_1_1
  · exact right1Middle6_eq_case_7_5_row_0_1_2
  · exact right1Middle6_eq_case_7_5_row_0_1_3
  · exact right1Middle6_eq_case_7_5_row_1_0_0
  · exact right1Middle6_eq_case_7_5_row_1_0_1
  · exact right1Middle6_eq_case_7_5_row_1_0_2
  · exact right1Middle6_eq_case_7_5_row_1_0_3
  · exact right1Middle6_eq_case_7_5_row_1_1_0
  · exact right1Middle6_eq_case_7_5_row_1_1_1
  · exact right1Middle6_eq_case_7_5_row_1_1_2
  · exact right1Middle6_eq_case_7_5_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem right1Middle6_eq_case_7_5 : right1Middle6 7 5 = associatorInverseZ 6 5 7 * right0Middle6 7 5 := by
  simpa only [HexagonAtoms675.assocABC_eq,
    HexagonAtoms675.outerABC_eq,
    HexagonAtoms675.assocBAC_eq,
    HexagonAtoms675.innerABC_eq,
    HexagonAtoms675.innerRightABC_eq,
    HexagonAtoms675.inverseACB_eq,
    HexagonAtoms675.innerACB_eq,
    HexagonAtoms675.assocBCA_eq,
    HexagonAtoms675.innerRightBAC_eq,
    HexagonAtoms675.assocCAB_eq,
    HexagonAtoms675.outerLeftABC_eq,
    HexagonRowColumn675.product0_eq,
    HexagonRowColumn675.product1_eq,
    HexagonRowColumn675.product2_eq,
    HexagonRowColumn675.product3_eq,
    HexagonRowColumn675.product4_eq,
    HexagonRowColumn675.product5_eq,
    HexagonRowColumn675.product6_eq,
    HexagonRowColumn675.product7_eq] using right1Middle6_eq_case_7_5_checked

private theorem right2Middle6_eq_case_7_5_row_0_0_0 : (right2Middle6 7 5) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (right1Middle6 7 5) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_7_5_row_0_0_1 : (right2Middle6 7 5) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (right1Middle6 7 5) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_7_5_row_0_0_2 : (right2Middle6 7 5) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (right1Middle6 7 5) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_7_5_row_0_0_3 : (right2Middle6 7 5) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (right1Middle6 7 5) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_7_5_row_0_1_0 : (right2Middle6 7 5) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (right1Middle6 7 5) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_7_5_row_0_1_1 : (right2Middle6 7 5) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (right1Middle6 7 5) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_7_5_row_0_1_2 : (right2Middle6 7 5) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (right1Middle6 7 5) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_7_5_row_0_1_3 : (right2Middle6 7 5) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (right1Middle6 7 5) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_7_5_row_1_0_0 : (right2Middle6 7 5) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (right1Middle6 7 5) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_7_5_row_1_0_1 : (right2Middle6 7 5) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (right1Middle6 7 5) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_7_5_row_1_0_2 : (right2Middle6 7 5) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (right1Middle6 7 5) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_7_5_row_1_0_3 : (right2Middle6 7 5) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (right1Middle6 7 5) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_7_5_row_1_1_0 : (right2Middle6 7 5) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (right1Middle6 7 5) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_7_5_row_1_1_1 : (right2Middle6 7 5) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (right1Middle6 7 5) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_7_5_row_1_1_2 : (right2Middle6 7 5) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (right1Middle6 7 5) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_7_5_row_1_1_3 : (right2Middle6 7 5) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (right1Middle6 7 5) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_7_5_checked : right2Middle6 7 5 = right1Middle6 7 5 := by
  funext r
  fin_cases r
  · exact right2Middle6_eq_case_7_5_row_0_0_0
  · exact right2Middle6_eq_case_7_5_row_0_0_1
  · exact right2Middle6_eq_case_7_5_row_0_0_2
  · exact right2Middle6_eq_case_7_5_row_0_0_3
  · exact right2Middle6_eq_case_7_5_row_0_1_0
  · exact right2Middle6_eq_case_7_5_row_0_1_1
  · exact right2Middle6_eq_case_7_5_row_0_1_2
  · exact right2Middle6_eq_case_7_5_row_0_1_3
  · exact right2Middle6_eq_case_7_5_row_1_0_0
  · exact right2Middle6_eq_case_7_5_row_1_0_1
  · exact right2Middle6_eq_case_7_5_row_1_0_2
  · exact right2Middle6_eq_case_7_5_row_1_0_3
  · exact right2Middle6_eq_case_7_5_row_1_1_0
  · exact right2Middle6_eq_case_7_5_row_1_1_1
  · exact right2Middle6_eq_case_7_5_row_1_1_2
  · exact right2Middle6_eq_case_7_5_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem right2Middle6_eq_case_7_5 : right2Middle6 7 5 = innerLeftZ 6 5 7 * right1Middle6 7 5 := by
  simpa only [HexagonAtoms675.assocABC_eq,
    HexagonAtoms675.outerABC_eq,
    HexagonAtoms675.assocBAC_eq,
    HexagonAtoms675.innerABC_eq,
    HexagonAtoms675.innerRightABC_eq,
    HexagonAtoms675.inverseACB_eq,
    HexagonAtoms675.innerACB_eq,
    HexagonAtoms675.assocBCA_eq,
    HexagonAtoms675.innerRightBAC_eq,
    HexagonAtoms675.assocCAB_eq,
    HexagonAtoms675.outerLeftABC_eq,
    HexagonRowColumn675.product0_eq,
    HexagonRowColumn675.product1_eq,
    HexagonRowColumn675.product2_eq,
    HexagonRowColumn675.product3_eq,
    HexagonRowColumn675.product4_eq,
    HexagonRowColumn675.product5_eq,
    HexagonRowColumn675.product6_eq,
    HexagonRowColumn675.product7_eq] using right2Middle6_eq_case_7_5_checked

private theorem leftFinal6_case_7_5_row_0_0_0 : (((-1 : ℤ) ^ (leftScaleBit 6 7 5).val * positiveScale (leftScaleExponent 6 7 5)) •
      (rowColumnMul HexagonRowColumn675.rows_assocBCA HexagonRowColumn675.cols_left0)) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 6 7 5) • (left1Middle6 7 5)) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem leftFinal6_case_7_5_row_0_0_1 : (((-1 : ℤ) ^ (leftScaleBit 6 7 5).val * positiveScale (leftScaleExponent 6 7 5)) •
      (rowColumnMul HexagonRowColumn675.rows_assocBCA HexagonRowColumn675.cols_left0)) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 6 7 5) • (left1Middle6 7 5)) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem leftFinal6_case_7_5_row_0_0_2 : (((-1 : ℤ) ^ (leftScaleBit 6 7 5).val * positiveScale (leftScaleExponent 6 7 5)) •
      (rowColumnMul HexagonRowColumn675.rows_assocBCA HexagonRowColumn675.cols_left0)) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 6 7 5) • (left1Middle6 7 5)) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem leftFinal6_case_7_5_row_0_0_3 : (((-1 : ℤ) ^ (leftScaleBit 6 7 5).val * positiveScale (leftScaleExponent 6 7 5)) •
      (rowColumnMul HexagonRowColumn675.rows_assocBCA HexagonRowColumn675.cols_left0)) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 6 7 5) • (left1Middle6 7 5)) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem leftFinal6_case_7_5_row_0_1_0 : (((-1 : ℤ) ^ (leftScaleBit 6 7 5).val * positiveScale (leftScaleExponent 6 7 5)) •
      (rowColumnMul HexagonRowColumn675.rows_assocBCA HexagonRowColumn675.cols_left0)) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 6 7 5) • (left1Middle6 7 5)) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem leftFinal6_case_7_5_row_0_1_1 : (((-1 : ℤ) ^ (leftScaleBit 6 7 5).val * positiveScale (leftScaleExponent 6 7 5)) •
      (rowColumnMul HexagonRowColumn675.rows_assocBCA HexagonRowColumn675.cols_left0)) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 6 7 5) • (left1Middle6 7 5)) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem leftFinal6_case_7_5_row_0_1_2 : (((-1 : ℤ) ^ (leftScaleBit 6 7 5).val * positiveScale (leftScaleExponent 6 7 5)) •
      (rowColumnMul HexagonRowColumn675.rows_assocBCA HexagonRowColumn675.cols_left0)) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 6 7 5) • (left1Middle6 7 5)) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem leftFinal6_case_7_5_row_0_1_3 : (((-1 : ℤ) ^ (leftScaleBit 6 7 5).val * positiveScale (leftScaleExponent 6 7 5)) •
      (rowColumnMul HexagonRowColumn675.rows_assocBCA HexagonRowColumn675.cols_left0)) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 6 7 5) • (left1Middle6 7 5)) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem leftFinal6_case_7_5_row_1_0_0 : (((-1 : ℤ) ^ (leftScaleBit 6 7 5).val * positiveScale (leftScaleExponent 6 7 5)) •
      (rowColumnMul HexagonRowColumn675.rows_assocBCA HexagonRowColumn675.cols_left0)) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 6 7 5) • (left1Middle6 7 5)) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem leftFinal6_case_7_5_row_1_0_1 : (((-1 : ℤ) ^ (leftScaleBit 6 7 5).val * positiveScale (leftScaleExponent 6 7 5)) •
      (rowColumnMul HexagonRowColumn675.rows_assocBCA HexagonRowColumn675.cols_left0)) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 6 7 5) • (left1Middle6 7 5)) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem leftFinal6_case_7_5_row_1_0_2 : (((-1 : ℤ) ^ (leftScaleBit 6 7 5).val * positiveScale (leftScaleExponent 6 7 5)) •
      (rowColumnMul HexagonRowColumn675.rows_assocBCA HexagonRowColumn675.cols_left0)) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 6 7 5) • (left1Middle6 7 5)) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem leftFinal6_case_7_5_row_1_0_3 : (((-1 : ℤ) ^ (leftScaleBit 6 7 5).val * positiveScale (leftScaleExponent 6 7 5)) •
      (rowColumnMul HexagonRowColumn675.rows_assocBCA HexagonRowColumn675.cols_left0)) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 6 7 5) • (left1Middle6 7 5)) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem leftFinal6_case_7_5_row_1_1_0 : (((-1 : ℤ) ^ (leftScaleBit 6 7 5).val * positiveScale (leftScaleExponent 6 7 5)) •
      (rowColumnMul HexagonRowColumn675.rows_assocBCA HexagonRowColumn675.cols_left0)) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 6 7 5) • (left1Middle6 7 5)) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem leftFinal6_case_7_5_row_1_1_1 : (((-1 : ℤ) ^ (leftScaleBit 6 7 5).val * positiveScale (leftScaleExponent 6 7 5)) •
      (rowColumnMul HexagonRowColumn675.rows_assocBCA HexagonRowColumn675.cols_left0)) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 6 7 5) • (left1Middle6 7 5)) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem leftFinal6_case_7_5_row_1_1_2 : (((-1 : ℤ) ^ (leftScaleBit 6 7 5).val * positiveScale (leftScaleExponent 6 7 5)) •
      (rowColumnMul HexagonRowColumn675.rows_assocBCA HexagonRowColumn675.cols_left0)) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 6 7 5) • (left1Middle6 7 5)) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem leftFinal6_case_7_5_row_1_1_3 : (((-1 : ℤ) ^ (leftScaleBit 6 7 5).val * positiveScale (leftScaleExponent 6 7 5)) •
      (rowColumnMul HexagonRowColumn675.rows_assocBCA HexagonRowColumn675.cols_left0)) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 6 7 5) • (left1Middle6 7 5)) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem leftFinal6_case_7_5_checked : ((-1 : ℤ) ^ (leftScaleBit 6 7 5).val * positiveScale (leftScaleExponent 6 7 5)) •
      (rowColumnMul HexagonRowColumn675.rows_assocBCA HexagonRowColumn675.cols_left0) = negativeScale (leftScaleExponent 6 7 5) • (left1Middle6 7 5) := by
  funext r
  fin_cases r
  · exact leftFinal6_case_7_5_row_0_0_0
  · exact leftFinal6_case_7_5_row_0_0_1
  · exact leftFinal6_case_7_5_row_0_0_2
  · exact leftFinal6_case_7_5_row_0_0_3
  · exact leftFinal6_case_7_5_row_0_1_0
  · exact leftFinal6_case_7_5_row_0_1_1
  · exact leftFinal6_case_7_5_row_0_1_2
  · exact leftFinal6_case_7_5_row_0_1_3
  · exact leftFinal6_case_7_5_row_1_0_0
  · exact leftFinal6_case_7_5_row_1_0_1
  · exact leftFinal6_case_7_5_row_1_0_2
  · exact leftFinal6_case_7_5_row_1_0_3
  · exact leftFinal6_case_7_5_row_1_1_0
  · exact leftFinal6_case_7_5_row_1_1_1
  · exact leftFinal6_case_7_5_row_1_1_2
  · exact leftFinal6_case_7_5_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem leftFinal6_case_7_5 : ((-1 : ℤ) ^ (leftScaleBit 6 7 5).val * positiveScale (leftScaleExponent 6 7 5)) •
      (associatorZ 7 5 6 * left0Middle6 7 5) = negativeScale (leftScaleExponent 6 7 5) • (innerRightZ 7 6 5 * left1Middle6 7 5) := by
  simpa only [HexagonAtoms675.assocABC_eq,
    HexagonAtoms675.outerABC_eq,
    HexagonAtoms675.assocBAC_eq,
    HexagonAtoms675.innerABC_eq,
    HexagonAtoms675.innerRightABC_eq,
    HexagonAtoms675.inverseACB_eq,
    HexagonAtoms675.innerACB_eq,
    HexagonAtoms675.assocBCA_eq,
    HexagonAtoms675.innerRightBAC_eq,
    HexagonAtoms675.assocCAB_eq,
    HexagonAtoms675.outerLeftABC_eq,
    HexagonRowColumn675.product0_eq,
    HexagonRowColumn675.product1_eq,
    HexagonRowColumn675.product2_eq,
    HexagonRowColumn675.product3_eq,
    HexagonRowColumn675.product4_eq,
    HexagonRowColumn675.product5_eq,
    HexagonRowColumn675.product6_eq,
    HexagonRowColumn675.product7_eq] using leftFinal6_case_7_5_checked

private theorem rightFinal6_case_7_5_row_0_0_0 : (((-1 : ℤ) ^ (rightScaleBit 6 7 5).val * positiveScale (rightScaleExponent 6 7 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 7 : ℤ)) • HexagonAtoms675.outerLeftABC) ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4)) = (negativeScale (rightScaleExponent 6 7 5) • (rowColumnMul HexagonRowColumn675.rows_assocCAB HexagonRowColumn675.cols_right2)) ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem rightFinal6_case_7_5_row_0_0_1 : (((-1 : ℤ) ^ (rightScaleBit 6 7 5).val * positiveScale (rightScaleExponent 6 7 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 7 : ℤ)) • HexagonAtoms675.outerLeftABC) ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4)) = (negativeScale (rightScaleExponent 6 7 5) • (rowColumnMul HexagonRowColumn675.rows_assocCAB HexagonRowColumn675.cols_right2)) ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem rightFinal6_case_7_5_row_0_0_2 : (((-1 : ℤ) ^ (rightScaleBit 6 7 5).val * positiveScale (rightScaleExponent 6 7 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 7 : ℤ)) • HexagonAtoms675.outerLeftABC) ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4)) = (negativeScale (rightScaleExponent 6 7 5) • (rowColumnMul HexagonRowColumn675.rows_assocCAB HexagonRowColumn675.cols_right2)) ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem rightFinal6_case_7_5_row_0_0_3 : (((-1 : ℤ) ^ (rightScaleBit 6 7 5).val * positiveScale (rightScaleExponent 6 7 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 7 : ℤ)) • HexagonAtoms675.outerLeftABC) ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4)) = (negativeScale (rightScaleExponent 6 7 5) • (rowColumnMul HexagonRowColumn675.rows_assocCAB HexagonRowColumn675.cols_right2)) ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem rightFinal6_case_7_5_row_0_1_0 : (((-1 : ℤ) ^ (rightScaleBit 6 7 5).val * positiveScale (rightScaleExponent 6 7 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 7 : ℤ)) • HexagonAtoms675.outerLeftABC) ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4)) = (negativeScale (rightScaleExponent 6 7 5) • (rowColumnMul HexagonRowColumn675.rows_assocCAB HexagonRowColumn675.cols_right2)) ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem rightFinal6_case_7_5_row_0_1_1 : (((-1 : ℤ) ^ (rightScaleBit 6 7 5).val * positiveScale (rightScaleExponent 6 7 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 7 : ℤ)) • HexagonAtoms675.outerLeftABC) ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4)) = (negativeScale (rightScaleExponent 6 7 5) • (rowColumnMul HexagonRowColumn675.rows_assocCAB HexagonRowColumn675.cols_right2)) ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem rightFinal6_case_7_5_row_0_1_2 : (((-1 : ℤ) ^ (rightScaleBit 6 7 5).val * positiveScale (rightScaleExponent 6 7 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 7 : ℤ)) • HexagonAtoms675.outerLeftABC) ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4)) = (negativeScale (rightScaleExponent 6 7 5) • (rowColumnMul HexagonRowColumn675.rows_assocCAB HexagonRowColumn675.cols_right2)) ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem rightFinal6_case_7_5_row_0_1_3 : (((-1 : ℤ) ^ (rightScaleBit 6 7 5).val * positiveScale (rightScaleExponent 6 7 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 7 : ℤ)) • HexagonAtoms675.outerLeftABC) ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4)) = (negativeScale (rightScaleExponent 6 7 5) • (rowColumnMul HexagonRowColumn675.rows_assocCAB HexagonRowColumn675.cols_right2)) ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem rightFinal6_case_7_5_row_0_2_0 : (((-1 : ℤ) ^ (rightScaleBit 6 7 5).val * positiveScale (rightScaleExponent 6 7 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 7 : ℤ)) • HexagonAtoms675.outerLeftABC) ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4)) = (negativeScale (rightScaleExponent 6 7 5) • (rowColumnMul HexagonRowColumn675.rows_assocCAB HexagonRowColumn675.cols_right2)) ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem rightFinal6_case_7_5_row_0_2_1 : (((-1 : ℤ) ^ (rightScaleBit 6 7 5).val * positiveScale (rightScaleExponent 6 7 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 7 : ℤ)) • HexagonAtoms675.outerLeftABC) ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4)) = (negativeScale (rightScaleExponent 6 7 5) • (rowColumnMul HexagonRowColumn675.rows_assocCAB HexagonRowColumn675.cols_right2)) ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem rightFinal6_case_7_5_row_0_2_2 : (((-1 : ℤ) ^ (rightScaleBit 6 7 5).val * positiveScale (rightScaleExponent 6 7 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 7 : ℤ)) • HexagonAtoms675.outerLeftABC) ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4)) = (negativeScale (rightScaleExponent 6 7 5) • (rowColumnMul HexagonRowColumn675.rows_assocCAB HexagonRowColumn675.cols_right2)) ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem rightFinal6_case_7_5_row_0_2_3 : (((-1 : ℤ) ^ (rightScaleBit 6 7 5).val * positiveScale (rightScaleExponent 6 7 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 7 : ℤ)) • HexagonAtoms675.outerLeftABC) ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4)) = (negativeScale (rightScaleExponent 6 7 5) • (rowColumnMul HexagonRowColumn675.rows_assocCAB HexagonRowColumn675.cols_right2)) ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem rightFinal6_case_7_5_row_0_3_0 : (((-1 : ℤ) ^ (rightScaleBit 6 7 5).val * positiveScale (rightScaleExponent 6 7 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 7 : ℤ)) • HexagonAtoms675.outerLeftABC) ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4)) = (negativeScale (rightScaleExponent 6 7 5) • (rowColumnMul HexagonRowColumn675.rows_assocCAB HexagonRowColumn675.cols_right2)) ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem rightFinal6_case_7_5_row_0_3_1 : (((-1 : ℤ) ^ (rightScaleBit 6 7 5).val * positiveScale (rightScaleExponent 6 7 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 7 : ℤ)) • HexagonAtoms675.outerLeftABC) ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4)) = (negativeScale (rightScaleExponent 6 7 5) • (rowColumnMul HexagonRowColumn675.rows_assocCAB HexagonRowColumn675.cols_right2)) ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem rightFinal6_case_7_5_row_0_3_2 : (((-1 : ℤ) ^ (rightScaleBit 6 7 5).val * positiveScale (rightScaleExponent 6 7 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 7 : ℤ)) • HexagonAtoms675.outerLeftABC) ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4)) = (negativeScale (rightScaleExponent 6 7 5) • (rowColumnMul HexagonRowColumn675.rows_assocCAB HexagonRowColumn675.cols_right2)) ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem rightFinal6_case_7_5_row_0_3_3 : (((-1 : ℤ) ^ (rightScaleBit 6 7 5).val * positiveScale (rightScaleExponent 6 7 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 7 : ℤ)) • HexagonAtoms675.outerLeftABC) ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4)) = (negativeScale (rightScaleExponent 6 7 5) • (rowColumnMul HexagonRowColumn675.rows_assocCAB HexagonRowColumn675.cols_right2)) ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem rightFinal6_case_7_5_checked : ((-1 : ℤ) ^ (rightScaleBit 6 7 5).val * positiveScale (rightScaleExponent 6 7 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 7 : ℤ)) • HexagonAtoms675.outerLeftABC = negativeScale (rightScaleExponent 6 7 5) • (rowColumnMul HexagonRowColumn675.rows_assocCAB HexagonRowColumn675.cols_right2) := by
  funext r
  fin_cases r
  · exact rightFinal6_case_7_5_row_0_0_0
  · exact rightFinal6_case_7_5_row_0_0_1
  · exact rightFinal6_case_7_5_row_0_0_2
  · exact rightFinal6_case_7_5_row_0_0_3
  · exact rightFinal6_case_7_5_row_0_1_0
  · exact rightFinal6_case_7_5_row_0_1_1
  · exact rightFinal6_case_7_5_row_0_1_2
  · exact rightFinal6_case_7_5_row_0_1_3
  · exact rightFinal6_case_7_5_row_0_2_0
  · exact rightFinal6_case_7_5_row_0_2_1
  · exact rightFinal6_case_7_5_row_0_2_2
  · exact rightFinal6_case_7_5_row_0_2_3
  · exact rightFinal6_case_7_5_row_0_3_0
  · exact rightFinal6_case_7_5_row_0_3_1
  · exact rightFinal6_case_7_5_row_0_3_2
  · exact rightFinal6_case_7_5_row_0_3_3

set_option backward.isDefEq.respectTransparency false in
theorem rightFinal6_case_7_5 : ((-1 : ℤ) ^ (rightScaleBit 6 7 5).val * positiveScale (rightScaleExponent 6 7 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 7 : ℤ)) • outerLeftZ 6 7 5 = negativeScale (rightScaleExponent 6 7 5) • (associatorZ 5 6 7 * right2Middle6 7 5) := by
  simpa only [HexagonAtoms675.assocABC_eq,
    HexagonAtoms675.outerABC_eq,
    HexagonAtoms675.assocBAC_eq,
    HexagonAtoms675.innerABC_eq,
    HexagonAtoms675.innerRightABC_eq,
    HexagonAtoms675.inverseACB_eq,
    HexagonAtoms675.innerACB_eq,
    HexagonAtoms675.assocBCA_eq,
    HexagonAtoms675.innerRightBAC_eq,
    HexagonAtoms675.assocCAB_eq,
    HexagonAtoms675.outerLeftABC_eq,
    HexagonRowColumn675.product0_eq,
    HexagonRowColumn675.product1_eq,
    HexagonRowColumn675.product2_eq,
    HexagonRowColumn675.product3_eq,
    HexagonRowColumn675.product4_eq,
    HexagonRowColumn675.product5_eq,
    HexagonRowColumn675.product6_eq,
    HexagonRowColumn675.product7_eq] using rightFinal6_case_7_5_checked

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonCases6
