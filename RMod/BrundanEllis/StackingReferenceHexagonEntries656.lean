import RMod.BrundanEllis.StackingReferenceHexagonMiddle6
import RMod.BrundanEllis.StackingReferenceSparseMatrixCheck
import RMod.BrundanEllis.StackingReferenceHexagonAtoms656
import RMod.BrundanEllis.StackingReferenceHexagonRowColumn656

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

private theorem left0Middle6_eq_case_5_6_row_0_0_0 : (left0Middle6 5 6) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (HexagonAtoms656.assocABC) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle6_eq_case_5_6_row_0_0_1 : (left0Middle6 5 6) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (HexagonAtoms656.assocABC) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle6_eq_case_5_6_row_0_1_0 : (left0Middle6 5 6) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (HexagonAtoms656.assocABC) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle6_eq_case_5_6_row_0_1_1 : (left0Middle6 5 6) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (HexagonAtoms656.assocABC) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle6_eq_case_5_6_row_0_2_0 : (left0Middle6 5 6) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (HexagonAtoms656.assocABC) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle6_eq_case_5_6_row_0_2_1 : (left0Middle6 5 6) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (HexagonAtoms656.assocABC) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle6_eq_case_5_6_row_0_3_0 : (left0Middle6 5 6) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (HexagonAtoms656.assocABC) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle6_eq_case_5_6_row_0_3_1 : (left0Middle6 5 6) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (HexagonAtoms656.assocABC) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle6_eq_case_5_6_row_1_0_0 : (left0Middle6 5 6) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (HexagonAtoms656.assocABC) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle6_eq_case_5_6_row_1_0_1 : (left0Middle6 5 6) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (HexagonAtoms656.assocABC) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle6_eq_case_5_6_row_1_1_0 : (left0Middle6 5 6) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (HexagonAtoms656.assocABC) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle6_eq_case_5_6_row_1_1_1 : (left0Middle6 5 6) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (HexagonAtoms656.assocABC) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle6_eq_case_5_6_row_1_2_0 : (left0Middle6 5 6) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (HexagonAtoms656.assocABC) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle6_eq_case_5_6_row_1_2_1 : (left0Middle6 5 6) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (HexagonAtoms656.assocABC) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle6_eq_case_5_6_row_1_3_0 : (left0Middle6 5 6) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (HexagonAtoms656.assocABC) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle6_eq_case_5_6_row_1_3_1 : (left0Middle6 5 6) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (HexagonAtoms656.assocABC) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle6_eq_case_5_6_checked : left0Middle6 5 6 = HexagonAtoms656.assocABC := by
  funext r
  fin_cases r
  · exact left0Middle6_eq_case_5_6_row_0_0_0
  · exact left0Middle6_eq_case_5_6_row_0_0_1
  · exact left0Middle6_eq_case_5_6_row_0_1_0
  · exact left0Middle6_eq_case_5_6_row_0_1_1
  · exact left0Middle6_eq_case_5_6_row_0_2_0
  · exact left0Middle6_eq_case_5_6_row_0_2_1
  · exact left0Middle6_eq_case_5_6_row_0_3_0
  · exact left0Middle6_eq_case_5_6_row_0_3_1
  · exact left0Middle6_eq_case_5_6_row_1_0_0
  · exact left0Middle6_eq_case_5_6_row_1_0_1
  · exact left0Middle6_eq_case_5_6_row_1_1_0
  · exact left0Middle6_eq_case_5_6_row_1_1_1
  · exact left0Middle6_eq_case_5_6_row_1_2_0
  · exact left0Middle6_eq_case_5_6_row_1_2_1
  · exact left0Middle6_eq_case_5_6_row_1_3_0
  · exact left0Middle6_eq_case_5_6_row_1_3_1

set_option backward.isDefEq.respectTransparency false in
theorem left0Middle6_eq_case_5_6 : left0Middle6 5 6 = outerRightZ 6 5 6 * associatorZ 6 5 6 := by
  simpa only [HexagonAtoms656.assocABC_eq,
    HexagonAtoms656.outerABC_eq,
    HexagonAtoms656.assocBAC_eq,
    HexagonAtoms656.innerABC_eq,
    HexagonAtoms656.innerRightABC_eq,
    HexagonAtoms656.inverseACB_eq,
    HexagonAtoms656.innerACB_eq,
    HexagonAtoms656.assocBCA_eq,
    HexagonAtoms656.innerRightBAC_eq,
    HexagonAtoms656.assocCAB_eq,
    HexagonAtoms656.outerLeftABC_eq,
    HexagonRowColumn656.assocBCA_alias,
    HexagonRowColumn656.product0_eq,
    HexagonRowColumn656.product1_eq,
    HexagonRowColumn656.product2_eq,
    HexagonRowColumn656.product3_eq,
    HexagonRowColumn656.product4_eq,
    HexagonRowColumn656.product5_eq,
    HexagonRowColumn656.product6_eq,
    HexagonRowColumn656.product7_eq] using left0Middle6_eq_case_5_6_checked

private theorem left1Middle6_eq_case_5_6_row_0_0_0 : (left1Middle6 5 6) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (HexagonAtoms656.assocBAC) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle6_eq_case_5_6_row_0_0_1 : (left1Middle6 5 6) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (HexagonAtoms656.assocBAC) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle6_eq_case_5_6_row_0_1_0 : (left1Middle6 5 6) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (HexagonAtoms656.assocBAC) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle6_eq_case_5_6_row_0_1_1 : (left1Middle6 5 6) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (HexagonAtoms656.assocBAC) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle6_eq_case_5_6_row_0_2_0 : (left1Middle6 5 6) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (HexagonAtoms656.assocBAC) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle6_eq_case_5_6_row_0_2_1 : (left1Middle6 5 6) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (HexagonAtoms656.assocBAC) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle6_eq_case_5_6_row_0_3_0 : (left1Middle6 5 6) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (HexagonAtoms656.assocBAC) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle6_eq_case_5_6_row_0_3_1 : (left1Middle6 5 6) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (HexagonAtoms656.assocBAC) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle6_eq_case_5_6_row_1_0_0 : (left1Middle6 5 6) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (HexagonAtoms656.assocBAC) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle6_eq_case_5_6_row_1_0_1 : (left1Middle6 5 6) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (HexagonAtoms656.assocBAC) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle6_eq_case_5_6_row_1_1_0 : (left1Middle6 5 6) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (HexagonAtoms656.assocBAC) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle6_eq_case_5_6_row_1_1_1 : (left1Middle6 5 6) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (HexagonAtoms656.assocBAC) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle6_eq_case_5_6_row_1_2_0 : (left1Middle6 5 6) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (HexagonAtoms656.assocBAC) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle6_eq_case_5_6_row_1_2_1 : (left1Middle6 5 6) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (HexagonAtoms656.assocBAC) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle6_eq_case_5_6_row_1_3_0 : (left1Middle6 5 6) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (HexagonAtoms656.assocBAC) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle6_eq_case_5_6_row_1_3_1 : (left1Middle6 5 6) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (HexagonAtoms656.assocBAC) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle6_eq_case_5_6_checked : left1Middle6 5 6 = HexagonAtoms656.assocBAC := by
  funext r
  fin_cases r
  · exact left1Middle6_eq_case_5_6_row_0_0_0
  · exact left1Middle6_eq_case_5_6_row_0_0_1
  · exact left1Middle6_eq_case_5_6_row_0_1_0
  · exact left1Middle6_eq_case_5_6_row_0_1_1
  · exact left1Middle6_eq_case_5_6_row_0_2_0
  · exact left1Middle6_eq_case_5_6_row_0_2_1
  · exact left1Middle6_eq_case_5_6_row_0_3_0
  · exact left1Middle6_eq_case_5_6_row_0_3_1
  · exact left1Middle6_eq_case_5_6_row_1_0_0
  · exact left1Middle6_eq_case_5_6_row_1_0_1
  · exact left1Middle6_eq_case_5_6_row_1_1_0
  · exact left1Middle6_eq_case_5_6_row_1_1_1
  · exact left1Middle6_eq_case_5_6_row_1_2_0
  · exact left1Middle6_eq_case_5_6_row_1_2_1
  · exact left1Middle6_eq_case_5_6_row_1_3_0
  · exact left1Middle6_eq_case_5_6_row_1_3_1

set_option backward.isDefEq.respectTransparency false in
theorem left1Middle6_eq_case_5_6 : left1Middle6 5 6 = associatorZ 5 6 6 * innerLeftZ 6 5 6 := by
  simpa only [HexagonAtoms656.assocABC_eq,
    HexagonAtoms656.outerABC_eq,
    HexagonAtoms656.assocBAC_eq,
    HexagonAtoms656.innerABC_eq,
    HexagonAtoms656.innerRightABC_eq,
    HexagonAtoms656.inverseACB_eq,
    HexagonAtoms656.innerACB_eq,
    HexagonAtoms656.assocBCA_eq,
    HexagonAtoms656.innerRightBAC_eq,
    HexagonAtoms656.assocCAB_eq,
    HexagonAtoms656.outerLeftABC_eq,
    HexagonRowColumn656.assocBCA_alias,
    HexagonRowColumn656.product0_eq,
    HexagonRowColumn656.product1_eq,
    HexagonRowColumn656.product2_eq,
    HexagonRowColumn656.product3_eq,
    HexagonRowColumn656.product4_eq,
    HexagonRowColumn656.product5_eq,
    HexagonRowColumn656.product6_eq,
    HexagonRowColumn656.product7_eq] using left1Middle6_eq_case_5_6_checked

private theorem right0Middle6_eq_case_5_6_row_0_0_0 : (right0Middle6 5 6) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (HexagonAtoms656.assocABC) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle6_eq_case_5_6_row_0_0_1 : (right0Middle6 5 6) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (HexagonAtoms656.assocABC) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle6_eq_case_5_6_row_0_1_0 : (right0Middle6 5 6) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (HexagonAtoms656.assocABC) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle6_eq_case_5_6_row_0_1_1 : (right0Middle6 5 6) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (HexagonAtoms656.assocABC) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle6_eq_case_5_6_row_0_2_0 : (right0Middle6 5 6) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (HexagonAtoms656.assocABC) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle6_eq_case_5_6_row_0_2_1 : (right0Middle6 5 6) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (HexagonAtoms656.assocABC) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle6_eq_case_5_6_row_0_3_0 : (right0Middle6 5 6) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (HexagonAtoms656.assocABC) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle6_eq_case_5_6_row_0_3_1 : (right0Middle6 5 6) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (HexagonAtoms656.assocABC) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle6_eq_case_5_6_row_1_0_0 : (right0Middle6 5 6) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (HexagonAtoms656.assocABC) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle6_eq_case_5_6_row_1_0_1 : (right0Middle6 5 6) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (HexagonAtoms656.assocABC) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle6_eq_case_5_6_row_1_1_0 : (right0Middle6 5 6) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (HexagonAtoms656.assocABC) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle6_eq_case_5_6_row_1_1_1 : (right0Middle6 5 6) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (HexagonAtoms656.assocABC) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle6_eq_case_5_6_row_1_2_0 : (right0Middle6 5 6) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (HexagonAtoms656.assocABC) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle6_eq_case_5_6_row_1_2_1 : (right0Middle6 5 6) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (HexagonAtoms656.assocABC) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle6_eq_case_5_6_row_1_3_0 : (right0Middle6 5 6) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (HexagonAtoms656.assocABC) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle6_eq_case_5_6_row_1_3_1 : (right0Middle6 5 6) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (HexagonAtoms656.assocABC) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle6_eq_case_5_6_checked : right0Middle6 5 6 = HexagonAtoms656.assocABC := by
  funext r
  fin_cases r
  · exact right0Middle6_eq_case_5_6_row_0_0_0
  · exact right0Middle6_eq_case_5_6_row_0_0_1
  · exact right0Middle6_eq_case_5_6_row_0_1_0
  · exact right0Middle6_eq_case_5_6_row_0_1_1
  · exact right0Middle6_eq_case_5_6_row_0_2_0
  · exact right0Middle6_eq_case_5_6_row_0_2_1
  · exact right0Middle6_eq_case_5_6_row_0_3_0
  · exact right0Middle6_eq_case_5_6_row_0_3_1
  · exact right0Middle6_eq_case_5_6_row_1_0_0
  · exact right0Middle6_eq_case_5_6_row_1_0_1
  · exact right0Middle6_eq_case_5_6_row_1_1_0
  · exact right0Middle6_eq_case_5_6_row_1_1_1
  · exact right0Middle6_eq_case_5_6_row_1_2_0
  · exact right0Middle6_eq_case_5_6_row_1_2_1
  · exact right0Middle6_eq_case_5_6_row_1_3_0
  · exact right0Middle6_eq_case_5_6_row_1_3_1

set_option backward.isDefEq.respectTransparency false in
theorem right0Middle6_eq_case_5_6 : right0Middle6 5 6 = innerRightZ 6 5 6 * associatorZ 6 5 6 := by
  simpa only [HexagonAtoms656.assocABC_eq,
    HexagonAtoms656.outerABC_eq,
    HexagonAtoms656.assocBAC_eq,
    HexagonAtoms656.innerABC_eq,
    HexagonAtoms656.innerRightABC_eq,
    HexagonAtoms656.inverseACB_eq,
    HexagonAtoms656.innerACB_eq,
    HexagonAtoms656.assocBCA_eq,
    HexagonAtoms656.innerRightBAC_eq,
    HexagonAtoms656.assocCAB_eq,
    HexagonAtoms656.outerLeftABC_eq,
    HexagonRowColumn656.assocBCA_alias,
    HexagonRowColumn656.product0_eq,
    HexagonRowColumn656.product1_eq,
    HexagonRowColumn656.product2_eq,
    HexagonRowColumn656.product3_eq,
    HexagonRowColumn656.product4_eq,
    HexagonRowColumn656.product5_eq,
    HexagonRowColumn656.product6_eq,
    HexagonRowColumn656.product7_eq] using right0Middle6_eq_case_5_6_checked

private theorem right1Middle6_eq_case_5_6_row_0_0_0 : (right1Middle6 5 6) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn656.rows_inverseACB HexagonRowColumn656.cols_right0) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle6_eq_case_5_6_row_0_0_1 : (right1Middle6 5 6) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn656.rows_inverseACB HexagonRowColumn656.cols_right0) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle6_eq_case_5_6_row_0_1_0 : (right1Middle6 5 6) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn656.rows_inverseACB HexagonRowColumn656.cols_right0) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle6_eq_case_5_6_row_0_1_1 : (right1Middle6 5 6) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn656.rows_inverseACB HexagonRowColumn656.cols_right0) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle6_eq_case_5_6_row_0_2_0 : (right1Middle6 5 6) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn656.rows_inverseACB HexagonRowColumn656.cols_right0) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle6_eq_case_5_6_row_0_2_1 : (right1Middle6 5 6) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn656.rows_inverseACB HexagonRowColumn656.cols_right0) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle6_eq_case_5_6_row_0_3_0 : (right1Middle6 5 6) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn656.rows_inverseACB HexagonRowColumn656.cols_right0) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle6_eq_case_5_6_row_0_3_1 : (right1Middle6 5 6) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn656.rows_inverseACB HexagonRowColumn656.cols_right0) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle6_eq_case_5_6_row_1_0_0 : (right1Middle6 5 6) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn656.rows_inverseACB HexagonRowColumn656.cols_right0) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle6_eq_case_5_6_row_1_0_1 : (right1Middle6 5 6) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn656.rows_inverseACB HexagonRowColumn656.cols_right0) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle6_eq_case_5_6_row_1_1_0 : (right1Middle6 5 6) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn656.rows_inverseACB HexagonRowColumn656.cols_right0) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle6_eq_case_5_6_row_1_1_1 : (right1Middle6 5 6) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn656.rows_inverseACB HexagonRowColumn656.cols_right0) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle6_eq_case_5_6_row_1_2_0 : (right1Middle6 5 6) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn656.rows_inverseACB HexagonRowColumn656.cols_right0) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle6_eq_case_5_6_row_1_2_1 : (right1Middle6 5 6) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn656.rows_inverseACB HexagonRowColumn656.cols_right0) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle6_eq_case_5_6_row_1_3_0 : (right1Middle6 5 6) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn656.rows_inverseACB HexagonRowColumn656.cols_right0) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle6_eq_case_5_6_row_1_3_1 : (right1Middle6 5 6) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn656.rows_inverseACB HexagonRowColumn656.cols_right0) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle6_eq_case_5_6_checked : right1Middle6 5 6 = rowColumnMul HexagonRowColumn656.rows_inverseACB HexagonRowColumn656.cols_right0 := by
  funext r
  fin_cases r
  · exact right1Middle6_eq_case_5_6_row_0_0_0
  · exact right1Middle6_eq_case_5_6_row_0_0_1
  · exact right1Middle6_eq_case_5_6_row_0_1_0
  · exact right1Middle6_eq_case_5_6_row_0_1_1
  · exact right1Middle6_eq_case_5_6_row_0_2_0
  · exact right1Middle6_eq_case_5_6_row_0_2_1
  · exact right1Middle6_eq_case_5_6_row_0_3_0
  · exact right1Middle6_eq_case_5_6_row_0_3_1
  · exact right1Middle6_eq_case_5_6_row_1_0_0
  · exact right1Middle6_eq_case_5_6_row_1_0_1
  · exact right1Middle6_eq_case_5_6_row_1_1_0
  · exact right1Middle6_eq_case_5_6_row_1_1_1
  · exact right1Middle6_eq_case_5_6_row_1_2_0
  · exact right1Middle6_eq_case_5_6_row_1_2_1
  · exact right1Middle6_eq_case_5_6_row_1_3_0
  · exact right1Middle6_eq_case_5_6_row_1_3_1

set_option backward.isDefEq.respectTransparency false in
theorem right1Middle6_eq_case_5_6 : right1Middle6 5 6 = associatorInverseZ 6 6 5 * right0Middle6 5 6 := by
  simpa only [HexagonAtoms656.assocABC_eq,
    HexagonAtoms656.outerABC_eq,
    HexagonAtoms656.assocBAC_eq,
    HexagonAtoms656.innerABC_eq,
    HexagonAtoms656.innerRightABC_eq,
    HexagonAtoms656.inverseACB_eq,
    HexagonAtoms656.innerACB_eq,
    HexagonAtoms656.assocBCA_eq,
    HexagonAtoms656.innerRightBAC_eq,
    HexagonAtoms656.assocCAB_eq,
    HexagonAtoms656.outerLeftABC_eq,
    HexagonRowColumn656.assocBCA_alias,
    HexagonRowColumn656.product0_eq,
    HexagonRowColumn656.product1_eq,
    HexagonRowColumn656.product2_eq,
    HexagonRowColumn656.product3_eq,
    HexagonRowColumn656.product4_eq,
    HexagonRowColumn656.product5_eq,
    HexagonRowColumn656.product6_eq,
    HexagonRowColumn656.product7_eq] using right1Middle6_eq_case_5_6_checked

private theorem right2Middle6_eq_case_5_6_row_0_0_0 : (right2Middle6 5 6) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn656.rows_innerACB HexagonRowColumn656.cols_right1) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle6_eq_case_5_6_row_0_0_1 : (right2Middle6 5 6) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn656.rows_innerACB HexagonRowColumn656.cols_right1) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle6_eq_case_5_6_row_0_1_0 : (right2Middle6 5 6) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn656.rows_innerACB HexagonRowColumn656.cols_right1) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle6_eq_case_5_6_row_0_1_1 : (right2Middle6 5 6) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn656.rows_innerACB HexagonRowColumn656.cols_right1) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle6_eq_case_5_6_row_0_2_0 : (right2Middle6 5 6) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn656.rows_innerACB HexagonRowColumn656.cols_right1) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle6_eq_case_5_6_row_0_2_1 : (right2Middle6 5 6) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn656.rows_innerACB HexagonRowColumn656.cols_right1) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle6_eq_case_5_6_row_0_3_0 : (right2Middle6 5 6) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn656.rows_innerACB HexagonRowColumn656.cols_right1) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle6_eq_case_5_6_row_0_3_1 : (right2Middle6 5 6) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn656.rows_innerACB HexagonRowColumn656.cols_right1) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle6_eq_case_5_6_row_1_0_0 : (right2Middle6 5 6) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn656.rows_innerACB HexagonRowColumn656.cols_right1) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle6_eq_case_5_6_row_1_0_1 : (right2Middle6 5 6) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn656.rows_innerACB HexagonRowColumn656.cols_right1) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle6_eq_case_5_6_row_1_1_0 : (right2Middle6 5 6) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn656.rows_innerACB HexagonRowColumn656.cols_right1) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle6_eq_case_5_6_row_1_1_1 : (right2Middle6 5 6) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn656.rows_innerACB HexagonRowColumn656.cols_right1) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle6_eq_case_5_6_row_1_2_0 : (right2Middle6 5 6) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn656.rows_innerACB HexagonRowColumn656.cols_right1) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle6_eq_case_5_6_row_1_2_1 : (right2Middle6 5 6) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn656.rows_innerACB HexagonRowColumn656.cols_right1) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle6_eq_case_5_6_row_1_3_0 : (right2Middle6 5 6) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn656.rows_innerACB HexagonRowColumn656.cols_right1) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle6_eq_case_5_6_row_1_3_1 : (right2Middle6 5 6) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn656.rows_innerACB HexagonRowColumn656.cols_right1) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle6_eq_case_5_6_checked : right2Middle6 5 6 = rowColumnMul HexagonRowColumn656.rows_innerACB HexagonRowColumn656.cols_right1 := by
  funext r
  fin_cases r
  · exact right2Middle6_eq_case_5_6_row_0_0_0
  · exact right2Middle6_eq_case_5_6_row_0_0_1
  · exact right2Middle6_eq_case_5_6_row_0_1_0
  · exact right2Middle6_eq_case_5_6_row_0_1_1
  · exact right2Middle6_eq_case_5_6_row_0_2_0
  · exact right2Middle6_eq_case_5_6_row_0_2_1
  · exact right2Middle6_eq_case_5_6_row_0_3_0
  · exact right2Middle6_eq_case_5_6_row_0_3_1
  · exact right2Middle6_eq_case_5_6_row_1_0_0
  · exact right2Middle6_eq_case_5_6_row_1_0_1
  · exact right2Middle6_eq_case_5_6_row_1_1_0
  · exact right2Middle6_eq_case_5_6_row_1_1_1
  · exact right2Middle6_eq_case_5_6_row_1_2_0
  · exact right2Middle6_eq_case_5_6_row_1_2_1
  · exact right2Middle6_eq_case_5_6_row_1_3_0
  · exact right2Middle6_eq_case_5_6_row_1_3_1

set_option backward.isDefEq.respectTransparency false in
theorem right2Middle6_eq_case_5_6 : right2Middle6 5 6 = innerLeftZ 6 6 5 * right1Middle6 5 6 := by
  simpa only [HexagonAtoms656.assocABC_eq,
    HexagonAtoms656.outerABC_eq,
    HexagonAtoms656.assocBAC_eq,
    HexagonAtoms656.innerABC_eq,
    HexagonAtoms656.innerRightABC_eq,
    HexagonAtoms656.inverseACB_eq,
    HexagonAtoms656.innerACB_eq,
    HexagonAtoms656.assocBCA_eq,
    HexagonAtoms656.innerRightBAC_eq,
    HexagonAtoms656.assocCAB_eq,
    HexagonAtoms656.outerLeftABC_eq,
    HexagonRowColumn656.assocBCA_alias,
    HexagonRowColumn656.product0_eq,
    HexagonRowColumn656.product1_eq,
    HexagonRowColumn656.product2_eq,
    HexagonRowColumn656.product3_eq,
    HexagonRowColumn656.product4_eq,
    HexagonRowColumn656.product5_eq,
    HexagonRowColumn656.product6_eq,
    HexagonRowColumn656.product7_eq] using right2Middle6_eq_case_5_6_checked

private theorem leftFinal6_case_5_6_row_0_0_0 : (((-1 : ℤ) ^ (leftScaleBit 6 5 6).val * positiveScale (leftScaleExponent 6 5 6)) •
      (rowColumnMul HexagonRowColumn656.rows_assocBAC HexagonRowColumn656.cols_left0)) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 6 5 6) • (rowColumnMul HexagonRowColumn656.rows_innerRightBAC HexagonRowColumn656.cols_left1)) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal6_case_5_6_row_0_0_1 : (((-1 : ℤ) ^ (leftScaleBit 6 5 6).val * positiveScale (leftScaleExponent 6 5 6)) •
      (rowColumnMul HexagonRowColumn656.rows_assocBAC HexagonRowColumn656.cols_left0)) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 6 5 6) • (rowColumnMul HexagonRowColumn656.rows_innerRightBAC HexagonRowColumn656.cols_left1)) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal6_case_5_6_row_0_1_0 : (((-1 : ℤ) ^ (leftScaleBit 6 5 6).val * positiveScale (leftScaleExponent 6 5 6)) •
      (rowColumnMul HexagonRowColumn656.rows_assocBAC HexagonRowColumn656.cols_left0)) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 6 5 6) • (rowColumnMul HexagonRowColumn656.rows_innerRightBAC HexagonRowColumn656.cols_left1)) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal6_case_5_6_row_0_1_1 : (((-1 : ℤ) ^ (leftScaleBit 6 5 6).val * positiveScale (leftScaleExponent 6 5 6)) •
      (rowColumnMul HexagonRowColumn656.rows_assocBAC HexagonRowColumn656.cols_left0)) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 6 5 6) • (rowColumnMul HexagonRowColumn656.rows_innerRightBAC HexagonRowColumn656.cols_left1)) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal6_case_5_6_row_0_2_0 : (((-1 : ℤ) ^ (leftScaleBit 6 5 6).val * positiveScale (leftScaleExponent 6 5 6)) •
      (rowColumnMul HexagonRowColumn656.rows_assocBAC HexagonRowColumn656.cols_left0)) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 6 5 6) • (rowColumnMul HexagonRowColumn656.rows_innerRightBAC HexagonRowColumn656.cols_left1)) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal6_case_5_6_row_0_2_1 : (((-1 : ℤ) ^ (leftScaleBit 6 5 6).val * positiveScale (leftScaleExponent 6 5 6)) •
      (rowColumnMul HexagonRowColumn656.rows_assocBAC HexagonRowColumn656.cols_left0)) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 6 5 6) • (rowColumnMul HexagonRowColumn656.rows_innerRightBAC HexagonRowColumn656.cols_left1)) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal6_case_5_6_row_0_3_0 : (((-1 : ℤ) ^ (leftScaleBit 6 5 6).val * positiveScale (leftScaleExponent 6 5 6)) •
      (rowColumnMul HexagonRowColumn656.rows_assocBAC HexagonRowColumn656.cols_left0)) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 6 5 6) • (rowColumnMul HexagonRowColumn656.rows_innerRightBAC HexagonRowColumn656.cols_left1)) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal6_case_5_6_row_0_3_1 : (((-1 : ℤ) ^ (leftScaleBit 6 5 6).val * positiveScale (leftScaleExponent 6 5 6)) •
      (rowColumnMul HexagonRowColumn656.rows_assocBAC HexagonRowColumn656.cols_left0)) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 6 5 6) • (rowColumnMul HexagonRowColumn656.rows_innerRightBAC HexagonRowColumn656.cols_left1)) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal6_case_5_6_row_1_0_0 : (((-1 : ℤ) ^ (leftScaleBit 6 5 6).val * positiveScale (leftScaleExponent 6 5 6)) •
      (rowColumnMul HexagonRowColumn656.rows_assocBAC HexagonRowColumn656.cols_left0)) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 6 5 6) • (rowColumnMul HexagonRowColumn656.rows_innerRightBAC HexagonRowColumn656.cols_left1)) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal6_case_5_6_row_1_0_1 : (((-1 : ℤ) ^ (leftScaleBit 6 5 6).val * positiveScale (leftScaleExponent 6 5 6)) •
      (rowColumnMul HexagonRowColumn656.rows_assocBAC HexagonRowColumn656.cols_left0)) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 6 5 6) • (rowColumnMul HexagonRowColumn656.rows_innerRightBAC HexagonRowColumn656.cols_left1)) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal6_case_5_6_row_1_1_0 : (((-1 : ℤ) ^ (leftScaleBit 6 5 6).val * positiveScale (leftScaleExponent 6 5 6)) •
      (rowColumnMul HexagonRowColumn656.rows_assocBAC HexagonRowColumn656.cols_left0)) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 6 5 6) • (rowColumnMul HexagonRowColumn656.rows_innerRightBAC HexagonRowColumn656.cols_left1)) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal6_case_5_6_row_1_1_1 : (((-1 : ℤ) ^ (leftScaleBit 6 5 6).val * positiveScale (leftScaleExponent 6 5 6)) •
      (rowColumnMul HexagonRowColumn656.rows_assocBAC HexagonRowColumn656.cols_left0)) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 6 5 6) • (rowColumnMul HexagonRowColumn656.rows_innerRightBAC HexagonRowColumn656.cols_left1)) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal6_case_5_6_row_1_2_0 : (((-1 : ℤ) ^ (leftScaleBit 6 5 6).val * positiveScale (leftScaleExponent 6 5 6)) •
      (rowColumnMul HexagonRowColumn656.rows_assocBAC HexagonRowColumn656.cols_left0)) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 6 5 6) • (rowColumnMul HexagonRowColumn656.rows_innerRightBAC HexagonRowColumn656.cols_left1)) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal6_case_5_6_row_1_2_1 : (((-1 : ℤ) ^ (leftScaleBit 6 5 6).val * positiveScale (leftScaleExponent 6 5 6)) •
      (rowColumnMul HexagonRowColumn656.rows_assocBAC HexagonRowColumn656.cols_left0)) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 6 5 6) • (rowColumnMul HexagonRowColumn656.rows_innerRightBAC HexagonRowColumn656.cols_left1)) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal6_case_5_6_row_1_3_0 : (((-1 : ℤ) ^ (leftScaleBit 6 5 6).val * positiveScale (leftScaleExponent 6 5 6)) •
      (rowColumnMul HexagonRowColumn656.rows_assocBAC HexagonRowColumn656.cols_left0)) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 6 5 6) • (rowColumnMul HexagonRowColumn656.rows_innerRightBAC HexagonRowColumn656.cols_left1)) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal6_case_5_6_row_1_3_1 : (((-1 : ℤ) ^ (leftScaleBit 6 5 6).val * positiveScale (leftScaleExponent 6 5 6)) •
      (rowColumnMul HexagonRowColumn656.rows_assocBAC HexagonRowColumn656.cols_left0)) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 6 5 6) • (rowColumnMul HexagonRowColumn656.rows_innerRightBAC HexagonRowColumn656.cols_left1)) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal6_case_5_6_checked : ((-1 : ℤ) ^ (leftScaleBit 6 5 6).val * positiveScale (leftScaleExponent 6 5 6)) •
      (rowColumnMul HexagonRowColumn656.rows_assocBAC HexagonRowColumn656.cols_left0) = negativeScale (leftScaleExponent 6 5 6) • (rowColumnMul HexagonRowColumn656.rows_innerRightBAC HexagonRowColumn656.cols_left1) := by
  funext r
  fin_cases r
  · exact leftFinal6_case_5_6_row_0_0_0
  · exact leftFinal6_case_5_6_row_0_0_1
  · exact leftFinal6_case_5_6_row_0_1_0
  · exact leftFinal6_case_5_6_row_0_1_1
  · exact leftFinal6_case_5_6_row_0_2_0
  · exact leftFinal6_case_5_6_row_0_2_1
  · exact leftFinal6_case_5_6_row_0_3_0
  · exact leftFinal6_case_5_6_row_0_3_1
  · exact leftFinal6_case_5_6_row_1_0_0
  · exact leftFinal6_case_5_6_row_1_0_1
  · exact leftFinal6_case_5_6_row_1_1_0
  · exact leftFinal6_case_5_6_row_1_1_1
  · exact leftFinal6_case_5_6_row_1_2_0
  · exact leftFinal6_case_5_6_row_1_2_1
  · exact leftFinal6_case_5_6_row_1_3_0
  · exact leftFinal6_case_5_6_row_1_3_1

set_option backward.isDefEq.respectTransparency false in
theorem leftFinal6_case_5_6 : ((-1 : ℤ) ^ (leftScaleBit 6 5 6).val * positiveScale (leftScaleExponent 6 5 6)) •
      (associatorZ 5 6 6 * left0Middle6 5 6) = negativeScale (leftScaleExponent 6 5 6) • (innerRightZ 5 6 6 * left1Middle6 5 6) := by
  simpa only [HexagonAtoms656.assocABC_eq,
    HexagonAtoms656.outerABC_eq,
    HexagonAtoms656.assocBAC_eq,
    HexagonAtoms656.innerABC_eq,
    HexagonAtoms656.innerRightABC_eq,
    HexagonAtoms656.inverseACB_eq,
    HexagonAtoms656.innerACB_eq,
    HexagonAtoms656.assocBCA_eq,
    HexagonAtoms656.innerRightBAC_eq,
    HexagonAtoms656.assocCAB_eq,
    HexagonAtoms656.outerLeftABC_eq,
    HexagonRowColumn656.assocBCA_alias,
    HexagonRowColumn656.product0_eq,
    HexagonRowColumn656.product1_eq,
    HexagonRowColumn656.product2_eq,
    HexagonRowColumn656.product3_eq,
    HexagonRowColumn656.product4_eq,
    HexagonRowColumn656.product5_eq,
    HexagonRowColumn656.product6_eq,
    HexagonRowColumn656.product7_eq] using leftFinal6_case_5_6_checked

private theorem rightFinal6_case_5_6_row_0_0_0 : (((-1 : ℤ) ^ (rightScaleBit 6 5 6).val * positiveScale (rightScaleExponent 6 5 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 6 5 : ℤ)) • HexagonAtoms656.outerLeftABC) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (negativeScale (rightScaleExponent 6 5 6) • (rowColumnMul HexagonRowColumn656.rows_assocCAB HexagonRowColumn656.cols_right2)) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal6_case_5_6_row_0_0_1 : (((-1 : ℤ) ^ (rightScaleBit 6 5 6).val * positiveScale (rightScaleExponent 6 5 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 6 5 : ℤ)) • HexagonAtoms656.outerLeftABC) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (negativeScale (rightScaleExponent 6 5 6) • (rowColumnMul HexagonRowColumn656.rows_assocCAB HexagonRowColumn656.cols_right2)) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal6_case_5_6_row_0_1_0 : (((-1 : ℤ) ^ (rightScaleBit 6 5 6).val * positiveScale (rightScaleExponent 6 5 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 6 5 : ℤ)) • HexagonAtoms656.outerLeftABC) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (negativeScale (rightScaleExponent 6 5 6) • (rowColumnMul HexagonRowColumn656.rows_assocCAB HexagonRowColumn656.cols_right2)) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal6_case_5_6_row_0_1_1 : (((-1 : ℤ) ^ (rightScaleBit 6 5 6).val * positiveScale (rightScaleExponent 6 5 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 6 5 : ℤ)) • HexagonAtoms656.outerLeftABC) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (negativeScale (rightScaleExponent 6 5 6) • (rowColumnMul HexagonRowColumn656.rows_assocCAB HexagonRowColumn656.cols_right2)) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal6_case_5_6_row_0_2_0 : (((-1 : ℤ) ^ (rightScaleBit 6 5 6).val * positiveScale (rightScaleExponent 6 5 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 6 5 : ℤ)) • HexagonAtoms656.outerLeftABC) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (negativeScale (rightScaleExponent 6 5 6) • (rowColumnMul HexagonRowColumn656.rows_assocCAB HexagonRowColumn656.cols_right2)) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal6_case_5_6_row_0_2_1 : (((-1 : ℤ) ^ (rightScaleBit 6 5 6).val * positiveScale (rightScaleExponent 6 5 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 6 5 : ℤ)) • HexagonAtoms656.outerLeftABC) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (negativeScale (rightScaleExponent 6 5 6) • (rowColumnMul HexagonRowColumn656.rows_assocCAB HexagonRowColumn656.cols_right2)) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal6_case_5_6_row_0_3_0 : (((-1 : ℤ) ^ (rightScaleBit 6 5 6).val * positiveScale (rightScaleExponent 6 5 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 6 5 : ℤ)) • HexagonAtoms656.outerLeftABC) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (negativeScale (rightScaleExponent 6 5 6) • (rowColumnMul HexagonRowColumn656.rows_assocCAB HexagonRowColumn656.cols_right2)) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal6_case_5_6_row_0_3_1 : (((-1 : ℤ) ^ (rightScaleBit 6 5 6).val * positiveScale (rightScaleExponent 6 5 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 6 5 : ℤ)) • HexagonAtoms656.outerLeftABC) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (negativeScale (rightScaleExponent 6 5 6) • (rowColumnMul HexagonRowColumn656.rows_assocCAB HexagonRowColumn656.cols_right2)) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal6_case_5_6_row_1_0_0 : (((-1 : ℤ) ^ (rightScaleBit 6 5 6).val * positiveScale (rightScaleExponent 6 5 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 6 5 : ℤ)) • HexagonAtoms656.outerLeftABC) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (negativeScale (rightScaleExponent 6 5 6) • (rowColumnMul HexagonRowColumn656.rows_assocCAB HexagonRowColumn656.cols_right2)) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal6_case_5_6_row_1_0_1 : (((-1 : ℤ) ^ (rightScaleBit 6 5 6).val * positiveScale (rightScaleExponent 6 5 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 6 5 : ℤ)) • HexagonAtoms656.outerLeftABC) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (negativeScale (rightScaleExponent 6 5 6) • (rowColumnMul HexagonRowColumn656.rows_assocCAB HexagonRowColumn656.cols_right2)) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal6_case_5_6_row_1_1_0 : (((-1 : ℤ) ^ (rightScaleBit 6 5 6).val * positiveScale (rightScaleExponent 6 5 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 6 5 : ℤ)) • HexagonAtoms656.outerLeftABC) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (negativeScale (rightScaleExponent 6 5 6) • (rowColumnMul HexagonRowColumn656.rows_assocCAB HexagonRowColumn656.cols_right2)) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal6_case_5_6_row_1_1_1 : (((-1 : ℤ) ^ (rightScaleBit 6 5 6).val * positiveScale (rightScaleExponent 6 5 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 6 5 : ℤ)) • HexagonAtoms656.outerLeftABC) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (negativeScale (rightScaleExponent 6 5 6) • (rowColumnMul HexagonRowColumn656.rows_assocCAB HexagonRowColumn656.cols_right2)) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal6_case_5_6_row_1_2_0 : (((-1 : ℤ) ^ (rightScaleBit 6 5 6).val * positiveScale (rightScaleExponent 6 5 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 6 5 : ℤ)) • HexagonAtoms656.outerLeftABC) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (negativeScale (rightScaleExponent 6 5 6) • (rowColumnMul HexagonRowColumn656.rows_assocCAB HexagonRowColumn656.cols_right2)) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal6_case_5_6_row_1_2_1 : (((-1 : ℤ) ^ (rightScaleBit 6 5 6).val * positiveScale (rightScaleExponent 6 5 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 6 5 : ℤ)) • HexagonAtoms656.outerLeftABC) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (negativeScale (rightScaleExponent 6 5 6) • (rowColumnMul HexagonRowColumn656.rows_assocCAB HexagonRowColumn656.cols_right2)) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal6_case_5_6_row_1_3_0 : (((-1 : ℤ) ^ (rightScaleBit 6 5 6).val * positiveScale (rightScaleExponent 6 5 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 6 5 : ℤ)) • HexagonAtoms656.outerLeftABC) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (negativeScale (rightScaleExponent 6 5 6) • (rowColumnMul HexagonRowColumn656.rows_assocCAB HexagonRowColumn656.cols_right2)) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal6_case_5_6_row_1_3_1 : (((-1 : ℤ) ^ (rightScaleBit 6 5 6).val * positiveScale (rightScaleExponent 6 5 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 6 5 : ℤ)) • HexagonAtoms656.outerLeftABC) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (negativeScale (rightScaleExponent 6 5 6) • (rowColumnMul HexagonRowColumn656.rows_assocCAB HexagonRowColumn656.cols_right2)) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal6_case_5_6_checked : ((-1 : ℤ) ^ (rightScaleBit 6 5 6).val * positiveScale (rightScaleExponent 6 5 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 6 5 : ℤ)) • HexagonAtoms656.outerLeftABC = negativeScale (rightScaleExponent 6 5 6) • (rowColumnMul HexagonRowColumn656.rows_assocCAB HexagonRowColumn656.cols_right2) := by
  funext r
  fin_cases r
  · exact rightFinal6_case_5_6_row_0_0_0
  · exact rightFinal6_case_5_6_row_0_0_1
  · exact rightFinal6_case_5_6_row_0_1_0
  · exact rightFinal6_case_5_6_row_0_1_1
  · exact rightFinal6_case_5_6_row_0_2_0
  · exact rightFinal6_case_5_6_row_0_2_1
  · exact rightFinal6_case_5_6_row_0_3_0
  · exact rightFinal6_case_5_6_row_0_3_1
  · exact rightFinal6_case_5_6_row_1_0_0
  · exact rightFinal6_case_5_6_row_1_0_1
  · exact rightFinal6_case_5_6_row_1_1_0
  · exact rightFinal6_case_5_6_row_1_1_1
  · exact rightFinal6_case_5_6_row_1_2_0
  · exact rightFinal6_case_5_6_row_1_2_1
  · exact rightFinal6_case_5_6_row_1_3_0
  · exact rightFinal6_case_5_6_row_1_3_1

set_option backward.isDefEq.respectTransparency false in
theorem rightFinal6_case_5_6 : ((-1 : ℤ) ^ (rightScaleBit 6 5 6).val * positiveScale (rightScaleExponent 6 5 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 6 5 : ℤ)) • outerLeftZ 6 5 6 = negativeScale (rightScaleExponent 6 5 6) • (associatorZ 6 6 5 * right2Middle6 5 6) := by
  simpa only [HexagonAtoms656.assocABC_eq,
    HexagonAtoms656.outerABC_eq,
    HexagonAtoms656.assocBAC_eq,
    HexagonAtoms656.innerABC_eq,
    HexagonAtoms656.innerRightABC_eq,
    HexagonAtoms656.inverseACB_eq,
    HexagonAtoms656.innerACB_eq,
    HexagonAtoms656.assocBCA_eq,
    HexagonAtoms656.innerRightBAC_eq,
    HexagonAtoms656.assocCAB_eq,
    HexagonAtoms656.outerLeftABC_eq,
    HexagonRowColumn656.assocBCA_alias,
    HexagonRowColumn656.product0_eq,
    HexagonRowColumn656.product1_eq,
    HexagonRowColumn656.product2_eq,
    HexagonRowColumn656.product3_eq,
    HexagonRowColumn656.product4_eq,
    HexagonRowColumn656.product5_eq,
    HexagonRowColumn656.product6_eq,
    HexagonRowColumn656.product7_eq] using rightFinal6_case_5_6_checked

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonCases6
