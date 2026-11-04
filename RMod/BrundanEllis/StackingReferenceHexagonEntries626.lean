import RMod.BrundanEllis.StackingReferenceHexagonMiddle6
import RMod.BrundanEllis.StackingReferenceSparseMatrixCheck
import RMod.BrundanEllis.StackingReferenceHexagonAtoms626
import RMod.BrundanEllis.StackingReferenceHexagonRowColumn626

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

private theorem left0Middle6_eq_case_2_6_row_0_0_0 : (left0Middle6 2 6) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms626.assocABC) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_2_6_row_0_0_1 : (left0Middle6 2 6) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms626.assocABC) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_2_6_row_0_0_2 : (left0Middle6 2 6) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms626.assocABC) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_2_6_row_0_0_3 : (left0Middle6 2 6) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms626.assocABC) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_2_6_row_1_0_0 : (left0Middle6 2 6) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms626.assocABC) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_2_6_row_1_0_1 : (left0Middle6 2 6) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms626.assocABC) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_2_6_row_1_0_2 : (left0Middle6 2 6) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms626.assocABC) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_2_6_row_1_0_3 : (left0Middle6 2 6) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms626.assocABC) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_2_6_row_2_0_0 : (left0Middle6 2 6) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms626.assocABC) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_2_6_row_2_0_1 : (left0Middle6 2 6) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms626.assocABC) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_2_6_row_2_0_2 : (left0Middle6 2 6) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms626.assocABC) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_2_6_row_2_0_3 : (left0Middle6 2 6) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms626.assocABC) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_2_6_row_3_0_0 : (left0Middle6 2 6) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms626.assocABC) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_2_6_row_3_0_1 : (left0Middle6 2 6) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms626.assocABC) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_2_6_row_3_0_2 : (left0Middle6 2 6) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms626.assocABC) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_2_6_row_3_0_3 : (left0Middle6 2 6) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms626.assocABC) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_2_6_checked : left0Middle6 2 6 = HexagonAtoms626.assocABC := by
  funext r
  fin_cases r
  · exact left0Middle6_eq_case_2_6_row_0_0_0
  · exact left0Middle6_eq_case_2_6_row_0_0_1
  · exact left0Middle6_eq_case_2_6_row_0_0_2
  · exact left0Middle6_eq_case_2_6_row_0_0_3
  · exact left0Middle6_eq_case_2_6_row_1_0_0
  · exact left0Middle6_eq_case_2_6_row_1_0_1
  · exact left0Middle6_eq_case_2_6_row_1_0_2
  · exact left0Middle6_eq_case_2_6_row_1_0_3
  · exact left0Middle6_eq_case_2_6_row_2_0_0
  · exact left0Middle6_eq_case_2_6_row_2_0_1
  · exact left0Middle6_eq_case_2_6_row_2_0_2
  · exact left0Middle6_eq_case_2_6_row_2_0_3
  · exact left0Middle6_eq_case_2_6_row_3_0_0
  · exact left0Middle6_eq_case_2_6_row_3_0_1
  · exact left0Middle6_eq_case_2_6_row_3_0_2
  · exact left0Middle6_eq_case_2_6_row_3_0_3

set_option backward.isDefEq.respectTransparency false in
theorem left0Middle6_eq_case_2_6 : left0Middle6 2 6 = outerRightZ 6 2 6 * associatorZ 6 2 6 := by
  simpa only [HexagonAtoms626.assocABC_eq,
    HexagonAtoms626.outerABC_eq,
    HexagonAtoms626.assocBAC_eq,
    HexagonAtoms626.innerABC_eq,
    HexagonAtoms626.innerRightABC_eq,
    HexagonAtoms626.inverseACB_eq,
    HexagonAtoms626.innerACB_eq,
    HexagonAtoms626.assocBCA_eq,
    HexagonAtoms626.innerRightBAC_eq,
    HexagonAtoms626.assocCAB_eq,
    HexagonAtoms626.outerLeftABC_eq,
    HexagonRowColumn626.assocBCA_alias,
    HexagonRowColumn626.product0_eq,
    HexagonRowColumn626.product1_eq,
    HexagonRowColumn626.product2_eq,
    HexagonRowColumn626.product3_eq,
    HexagonRowColumn626.product4_eq,
    HexagonRowColumn626.product5_eq,
    HexagonRowColumn626.product6_eq,
    HexagonRowColumn626.product7_eq] using left0Middle6_eq_case_2_6_checked

private theorem left1Middle6_eq_case_2_6_row_0_0_0 : (left1Middle6 2 6) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms626.assocBAC) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_2_6_row_0_0_1 : (left1Middle6 2 6) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms626.assocBAC) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_2_6_row_0_0_2 : (left1Middle6 2 6) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms626.assocBAC) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_2_6_row_0_0_3 : (left1Middle6 2 6) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms626.assocBAC) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_2_6_row_0_1_0 : (left1Middle6 2 6) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms626.assocBAC) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_2_6_row_0_1_1 : (left1Middle6 2 6) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms626.assocBAC) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_2_6_row_0_1_2 : (left1Middle6 2 6) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms626.assocBAC) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_2_6_row_0_1_3 : (left1Middle6 2 6) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms626.assocBAC) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_2_6_row_1_0_0 : (left1Middle6 2 6) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms626.assocBAC) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_2_6_row_1_0_1 : (left1Middle6 2 6) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms626.assocBAC) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_2_6_row_1_0_2 : (left1Middle6 2 6) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms626.assocBAC) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_2_6_row_1_0_3 : (left1Middle6 2 6) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms626.assocBAC) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_2_6_row_1_1_0 : (left1Middle6 2 6) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms626.assocBAC) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_2_6_row_1_1_1 : (left1Middle6 2 6) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms626.assocBAC) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_2_6_row_1_1_2 : (left1Middle6 2 6) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms626.assocBAC) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_2_6_row_1_1_3 : (left1Middle6 2 6) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms626.assocBAC) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_2_6_checked : left1Middle6 2 6 = HexagonAtoms626.assocBAC := by
  funext r
  fin_cases r
  · exact left1Middle6_eq_case_2_6_row_0_0_0
  · exact left1Middle6_eq_case_2_6_row_0_0_1
  · exact left1Middle6_eq_case_2_6_row_0_0_2
  · exact left1Middle6_eq_case_2_6_row_0_0_3
  · exact left1Middle6_eq_case_2_6_row_0_1_0
  · exact left1Middle6_eq_case_2_6_row_0_1_1
  · exact left1Middle6_eq_case_2_6_row_0_1_2
  · exact left1Middle6_eq_case_2_6_row_0_1_3
  · exact left1Middle6_eq_case_2_6_row_1_0_0
  · exact left1Middle6_eq_case_2_6_row_1_0_1
  · exact left1Middle6_eq_case_2_6_row_1_0_2
  · exact left1Middle6_eq_case_2_6_row_1_0_3
  · exact left1Middle6_eq_case_2_6_row_1_1_0
  · exact left1Middle6_eq_case_2_6_row_1_1_1
  · exact left1Middle6_eq_case_2_6_row_1_1_2
  · exact left1Middle6_eq_case_2_6_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem left1Middle6_eq_case_2_6 : left1Middle6 2 6 = associatorZ 2 6 6 * innerLeftZ 6 2 6 := by
  simpa only [HexagonAtoms626.assocABC_eq,
    HexagonAtoms626.outerABC_eq,
    HexagonAtoms626.assocBAC_eq,
    HexagonAtoms626.innerABC_eq,
    HexagonAtoms626.innerRightABC_eq,
    HexagonAtoms626.inverseACB_eq,
    HexagonAtoms626.innerACB_eq,
    HexagonAtoms626.assocBCA_eq,
    HexagonAtoms626.innerRightBAC_eq,
    HexagonAtoms626.assocCAB_eq,
    HexagonAtoms626.outerLeftABC_eq,
    HexagonRowColumn626.assocBCA_alias,
    HexagonRowColumn626.product0_eq,
    HexagonRowColumn626.product1_eq,
    HexagonRowColumn626.product2_eq,
    HexagonRowColumn626.product3_eq,
    HexagonRowColumn626.product4_eq,
    HexagonRowColumn626.product5_eq,
    HexagonRowColumn626.product6_eq,
    HexagonRowColumn626.product7_eq] using left1Middle6_eq_case_2_6_checked

private theorem right0Middle6_eq_case_2_6_row_0_0_0 : (right0Middle6 2 6) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms626.assocABC) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_2_6_row_0_0_1 : (right0Middle6 2 6) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms626.assocABC) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_2_6_row_0_0_2 : (right0Middle6 2 6) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms626.assocABC) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_2_6_row_0_0_3 : (right0Middle6 2 6) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms626.assocABC) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_2_6_row_1_0_0 : (right0Middle6 2 6) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms626.assocABC) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_2_6_row_1_0_1 : (right0Middle6 2 6) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms626.assocABC) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_2_6_row_1_0_2 : (right0Middle6 2 6) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms626.assocABC) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_2_6_row_1_0_3 : (right0Middle6 2 6) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms626.assocABC) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_2_6_row_2_0_0 : (right0Middle6 2 6) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms626.assocABC) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_2_6_row_2_0_1 : (right0Middle6 2 6) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms626.assocABC) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_2_6_row_2_0_2 : (right0Middle6 2 6) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms626.assocABC) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_2_6_row_2_0_3 : (right0Middle6 2 6) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms626.assocABC) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_2_6_row_3_0_0 : (right0Middle6 2 6) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms626.assocABC) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_2_6_row_3_0_1 : (right0Middle6 2 6) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms626.assocABC) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_2_6_row_3_0_2 : (right0Middle6 2 6) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms626.assocABC) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_2_6_row_3_0_3 : (right0Middle6 2 6) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms626.assocABC) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_2_6_checked : right0Middle6 2 6 = HexagonAtoms626.assocABC := by
  funext r
  fin_cases r
  · exact right0Middle6_eq_case_2_6_row_0_0_0
  · exact right0Middle6_eq_case_2_6_row_0_0_1
  · exact right0Middle6_eq_case_2_6_row_0_0_2
  · exact right0Middle6_eq_case_2_6_row_0_0_3
  · exact right0Middle6_eq_case_2_6_row_1_0_0
  · exact right0Middle6_eq_case_2_6_row_1_0_1
  · exact right0Middle6_eq_case_2_6_row_1_0_2
  · exact right0Middle6_eq_case_2_6_row_1_0_3
  · exact right0Middle6_eq_case_2_6_row_2_0_0
  · exact right0Middle6_eq_case_2_6_row_2_0_1
  · exact right0Middle6_eq_case_2_6_row_2_0_2
  · exact right0Middle6_eq_case_2_6_row_2_0_3
  · exact right0Middle6_eq_case_2_6_row_3_0_0
  · exact right0Middle6_eq_case_2_6_row_3_0_1
  · exact right0Middle6_eq_case_2_6_row_3_0_2
  · exact right0Middle6_eq_case_2_6_row_3_0_3

set_option backward.isDefEq.respectTransparency false in
theorem right0Middle6_eq_case_2_6 : right0Middle6 2 6 = innerRightZ 6 2 6 * associatorZ 6 2 6 := by
  simpa only [HexagonAtoms626.assocABC_eq,
    HexagonAtoms626.outerABC_eq,
    HexagonAtoms626.assocBAC_eq,
    HexagonAtoms626.innerABC_eq,
    HexagonAtoms626.innerRightABC_eq,
    HexagonAtoms626.inverseACB_eq,
    HexagonAtoms626.innerACB_eq,
    HexagonAtoms626.assocBCA_eq,
    HexagonAtoms626.innerRightBAC_eq,
    HexagonAtoms626.assocCAB_eq,
    HexagonAtoms626.outerLeftABC_eq,
    HexagonRowColumn626.assocBCA_alias,
    HexagonRowColumn626.product0_eq,
    HexagonRowColumn626.product1_eq,
    HexagonRowColumn626.product2_eq,
    HexagonRowColumn626.product3_eq,
    HexagonRowColumn626.product4_eq,
    HexagonRowColumn626.product5_eq,
    HexagonRowColumn626.product6_eq,
    HexagonRowColumn626.product7_eq] using right0Middle6_eq_case_2_6_checked

private theorem right1Middle6_eq_case_2_6_row_0_0_0 : (right1Middle6 2 6) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn626.rows_inverseACB HexagonRowColumn626.cols_right0) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_2_6_row_0_0_1 : (right1Middle6 2 6) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn626.rows_inverseACB HexagonRowColumn626.cols_right0) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_2_6_row_0_0_2 : (right1Middle6 2 6) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn626.rows_inverseACB HexagonRowColumn626.cols_right0) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_2_6_row_0_0_3 : (right1Middle6 2 6) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn626.rows_inverseACB HexagonRowColumn626.cols_right0) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_2_6_row_0_1_0 : (right1Middle6 2 6) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn626.rows_inverseACB HexagonRowColumn626.cols_right0) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_2_6_row_0_1_1 : (right1Middle6 2 6) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn626.rows_inverseACB HexagonRowColumn626.cols_right0) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_2_6_row_0_1_2 : (right1Middle6 2 6) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn626.rows_inverseACB HexagonRowColumn626.cols_right0) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_2_6_row_0_1_3 : (right1Middle6 2 6) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn626.rows_inverseACB HexagonRowColumn626.cols_right0) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_2_6_row_1_0_0 : (right1Middle6 2 6) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn626.rows_inverseACB HexagonRowColumn626.cols_right0) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_2_6_row_1_0_1 : (right1Middle6 2 6) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn626.rows_inverseACB HexagonRowColumn626.cols_right0) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_2_6_row_1_0_2 : (right1Middle6 2 6) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn626.rows_inverseACB HexagonRowColumn626.cols_right0) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_2_6_row_1_0_3 : (right1Middle6 2 6) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn626.rows_inverseACB HexagonRowColumn626.cols_right0) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_2_6_row_1_1_0 : (right1Middle6 2 6) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn626.rows_inverseACB HexagonRowColumn626.cols_right0) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_2_6_row_1_1_1 : (right1Middle6 2 6) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn626.rows_inverseACB HexagonRowColumn626.cols_right0) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_2_6_row_1_1_2 : (right1Middle6 2 6) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn626.rows_inverseACB HexagonRowColumn626.cols_right0) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_2_6_row_1_1_3 : (right1Middle6 2 6) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn626.rows_inverseACB HexagonRowColumn626.cols_right0) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_2_6_checked : right1Middle6 2 6 = rowColumnMul HexagonRowColumn626.rows_inverseACB HexagonRowColumn626.cols_right0 := by
  funext r
  fin_cases r
  · exact right1Middle6_eq_case_2_6_row_0_0_0
  · exact right1Middle6_eq_case_2_6_row_0_0_1
  · exact right1Middle6_eq_case_2_6_row_0_0_2
  · exact right1Middle6_eq_case_2_6_row_0_0_3
  · exact right1Middle6_eq_case_2_6_row_0_1_0
  · exact right1Middle6_eq_case_2_6_row_0_1_1
  · exact right1Middle6_eq_case_2_6_row_0_1_2
  · exact right1Middle6_eq_case_2_6_row_0_1_3
  · exact right1Middle6_eq_case_2_6_row_1_0_0
  · exact right1Middle6_eq_case_2_6_row_1_0_1
  · exact right1Middle6_eq_case_2_6_row_1_0_2
  · exact right1Middle6_eq_case_2_6_row_1_0_3
  · exact right1Middle6_eq_case_2_6_row_1_1_0
  · exact right1Middle6_eq_case_2_6_row_1_1_1
  · exact right1Middle6_eq_case_2_6_row_1_1_2
  · exact right1Middle6_eq_case_2_6_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem right1Middle6_eq_case_2_6 : right1Middle6 2 6 = associatorInverseZ 6 6 2 * right0Middle6 2 6 := by
  simpa only [HexagonAtoms626.assocABC_eq,
    HexagonAtoms626.outerABC_eq,
    HexagonAtoms626.assocBAC_eq,
    HexagonAtoms626.innerABC_eq,
    HexagonAtoms626.innerRightABC_eq,
    HexagonAtoms626.inverseACB_eq,
    HexagonAtoms626.innerACB_eq,
    HexagonAtoms626.assocBCA_eq,
    HexagonAtoms626.innerRightBAC_eq,
    HexagonAtoms626.assocCAB_eq,
    HexagonAtoms626.outerLeftABC_eq,
    HexagonRowColumn626.assocBCA_alias,
    HexagonRowColumn626.product0_eq,
    HexagonRowColumn626.product1_eq,
    HexagonRowColumn626.product2_eq,
    HexagonRowColumn626.product3_eq,
    HexagonRowColumn626.product4_eq,
    HexagonRowColumn626.product5_eq,
    HexagonRowColumn626.product6_eq,
    HexagonRowColumn626.product7_eq] using right1Middle6_eq_case_2_6_checked

private theorem right2Middle6_eq_case_2_6_row_0_0_0 : (right2Middle6 2 6) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn626.rows_innerACB HexagonRowColumn626.cols_right1) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_2_6_row_0_0_1 : (right2Middle6 2 6) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn626.rows_innerACB HexagonRowColumn626.cols_right1) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_2_6_row_0_0_2 : (right2Middle6 2 6) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn626.rows_innerACB HexagonRowColumn626.cols_right1) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_2_6_row_0_0_3 : (right2Middle6 2 6) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn626.rows_innerACB HexagonRowColumn626.cols_right1) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_2_6_row_0_1_0 : (right2Middle6 2 6) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn626.rows_innerACB HexagonRowColumn626.cols_right1) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_2_6_row_0_1_1 : (right2Middle6 2 6) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn626.rows_innerACB HexagonRowColumn626.cols_right1) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_2_6_row_0_1_2 : (right2Middle6 2 6) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn626.rows_innerACB HexagonRowColumn626.cols_right1) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_2_6_row_0_1_3 : (right2Middle6 2 6) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn626.rows_innerACB HexagonRowColumn626.cols_right1) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_2_6_row_1_0_0 : (right2Middle6 2 6) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn626.rows_innerACB HexagonRowColumn626.cols_right1) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_2_6_row_1_0_1 : (right2Middle6 2 6) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn626.rows_innerACB HexagonRowColumn626.cols_right1) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_2_6_row_1_0_2 : (right2Middle6 2 6) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn626.rows_innerACB HexagonRowColumn626.cols_right1) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_2_6_row_1_0_3 : (right2Middle6 2 6) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn626.rows_innerACB HexagonRowColumn626.cols_right1) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_2_6_row_1_1_0 : (right2Middle6 2 6) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn626.rows_innerACB HexagonRowColumn626.cols_right1) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_2_6_row_1_1_1 : (right2Middle6 2 6) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn626.rows_innerACB HexagonRowColumn626.cols_right1) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_2_6_row_1_1_2 : (right2Middle6 2 6) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn626.rows_innerACB HexagonRowColumn626.cols_right1) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_2_6_row_1_1_3 : (right2Middle6 2 6) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn626.rows_innerACB HexagonRowColumn626.cols_right1) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_2_6_checked : right2Middle6 2 6 = rowColumnMul HexagonRowColumn626.rows_innerACB HexagonRowColumn626.cols_right1 := by
  funext r
  fin_cases r
  · exact right2Middle6_eq_case_2_6_row_0_0_0
  · exact right2Middle6_eq_case_2_6_row_0_0_1
  · exact right2Middle6_eq_case_2_6_row_0_0_2
  · exact right2Middle6_eq_case_2_6_row_0_0_3
  · exact right2Middle6_eq_case_2_6_row_0_1_0
  · exact right2Middle6_eq_case_2_6_row_0_1_1
  · exact right2Middle6_eq_case_2_6_row_0_1_2
  · exact right2Middle6_eq_case_2_6_row_0_1_3
  · exact right2Middle6_eq_case_2_6_row_1_0_0
  · exact right2Middle6_eq_case_2_6_row_1_0_1
  · exact right2Middle6_eq_case_2_6_row_1_0_2
  · exact right2Middle6_eq_case_2_6_row_1_0_3
  · exact right2Middle6_eq_case_2_6_row_1_1_0
  · exact right2Middle6_eq_case_2_6_row_1_1_1
  · exact right2Middle6_eq_case_2_6_row_1_1_2
  · exact right2Middle6_eq_case_2_6_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem right2Middle6_eq_case_2_6 : right2Middle6 2 6 = innerLeftZ 6 6 2 * right1Middle6 2 6 := by
  simpa only [HexagonAtoms626.assocABC_eq,
    HexagonAtoms626.outerABC_eq,
    HexagonAtoms626.assocBAC_eq,
    HexagonAtoms626.innerABC_eq,
    HexagonAtoms626.innerRightABC_eq,
    HexagonAtoms626.inverseACB_eq,
    HexagonAtoms626.innerACB_eq,
    HexagonAtoms626.assocBCA_eq,
    HexagonAtoms626.innerRightBAC_eq,
    HexagonAtoms626.assocCAB_eq,
    HexagonAtoms626.outerLeftABC_eq,
    HexagonRowColumn626.assocBCA_alias,
    HexagonRowColumn626.product0_eq,
    HexagonRowColumn626.product1_eq,
    HexagonRowColumn626.product2_eq,
    HexagonRowColumn626.product3_eq,
    HexagonRowColumn626.product4_eq,
    HexagonRowColumn626.product5_eq,
    HexagonRowColumn626.product6_eq,
    HexagonRowColumn626.product7_eq] using right2Middle6_eq_case_2_6_checked

private theorem leftFinal6_case_2_6_row_0_0_0 : (((-1 : ℤ) ^ (leftScaleBit 6 2 6).val * positiveScale (leftScaleExponent 6 2 6)) •
      (rowColumnMul HexagonRowColumn626.rows_assocBAC HexagonRowColumn626.cols_left0)) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 6 2 6) • (rowColumnMul HexagonRowColumn626.rows_innerRightBAC HexagonRowColumn626.cols_left1)) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal6_case_2_6_row_0_0_1 : (((-1 : ℤ) ^ (leftScaleBit 6 2 6).val * positiveScale (leftScaleExponent 6 2 6)) •
      (rowColumnMul HexagonRowColumn626.rows_assocBAC HexagonRowColumn626.cols_left0)) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 6 2 6) • (rowColumnMul HexagonRowColumn626.rows_innerRightBAC HexagonRowColumn626.cols_left1)) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal6_case_2_6_row_0_0_2 : (((-1 : ℤ) ^ (leftScaleBit 6 2 6).val * positiveScale (leftScaleExponent 6 2 6)) •
      (rowColumnMul HexagonRowColumn626.rows_assocBAC HexagonRowColumn626.cols_left0)) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 6 2 6) • (rowColumnMul HexagonRowColumn626.rows_innerRightBAC HexagonRowColumn626.cols_left1)) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal6_case_2_6_row_0_0_3 : (((-1 : ℤ) ^ (leftScaleBit 6 2 6).val * positiveScale (leftScaleExponent 6 2 6)) •
      (rowColumnMul HexagonRowColumn626.rows_assocBAC HexagonRowColumn626.cols_left0)) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 6 2 6) • (rowColumnMul HexagonRowColumn626.rows_innerRightBAC HexagonRowColumn626.cols_left1)) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal6_case_2_6_row_0_1_0 : (((-1 : ℤ) ^ (leftScaleBit 6 2 6).val * positiveScale (leftScaleExponent 6 2 6)) •
      (rowColumnMul HexagonRowColumn626.rows_assocBAC HexagonRowColumn626.cols_left0)) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 6 2 6) • (rowColumnMul HexagonRowColumn626.rows_innerRightBAC HexagonRowColumn626.cols_left1)) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal6_case_2_6_row_0_1_1 : (((-1 : ℤ) ^ (leftScaleBit 6 2 6).val * positiveScale (leftScaleExponent 6 2 6)) •
      (rowColumnMul HexagonRowColumn626.rows_assocBAC HexagonRowColumn626.cols_left0)) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 6 2 6) • (rowColumnMul HexagonRowColumn626.rows_innerRightBAC HexagonRowColumn626.cols_left1)) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal6_case_2_6_row_0_1_2 : (((-1 : ℤ) ^ (leftScaleBit 6 2 6).val * positiveScale (leftScaleExponent 6 2 6)) •
      (rowColumnMul HexagonRowColumn626.rows_assocBAC HexagonRowColumn626.cols_left0)) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 6 2 6) • (rowColumnMul HexagonRowColumn626.rows_innerRightBAC HexagonRowColumn626.cols_left1)) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal6_case_2_6_row_0_1_3 : (((-1 : ℤ) ^ (leftScaleBit 6 2 6).val * positiveScale (leftScaleExponent 6 2 6)) •
      (rowColumnMul HexagonRowColumn626.rows_assocBAC HexagonRowColumn626.cols_left0)) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 6 2 6) • (rowColumnMul HexagonRowColumn626.rows_innerRightBAC HexagonRowColumn626.cols_left1)) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal6_case_2_6_row_1_0_0 : (((-1 : ℤ) ^ (leftScaleBit 6 2 6).val * positiveScale (leftScaleExponent 6 2 6)) •
      (rowColumnMul HexagonRowColumn626.rows_assocBAC HexagonRowColumn626.cols_left0)) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 6 2 6) • (rowColumnMul HexagonRowColumn626.rows_innerRightBAC HexagonRowColumn626.cols_left1)) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal6_case_2_6_row_1_0_1 : (((-1 : ℤ) ^ (leftScaleBit 6 2 6).val * positiveScale (leftScaleExponent 6 2 6)) •
      (rowColumnMul HexagonRowColumn626.rows_assocBAC HexagonRowColumn626.cols_left0)) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 6 2 6) • (rowColumnMul HexagonRowColumn626.rows_innerRightBAC HexagonRowColumn626.cols_left1)) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal6_case_2_6_row_1_0_2 : (((-1 : ℤ) ^ (leftScaleBit 6 2 6).val * positiveScale (leftScaleExponent 6 2 6)) •
      (rowColumnMul HexagonRowColumn626.rows_assocBAC HexagonRowColumn626.cols_left0)) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 6 2 6) • (rowColumnMul HexagonRowColumn626.rows_innerRightBAC HexagonRowColumn626.cols_left1)) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal6_case_2_6_row_1_0_3 : (((-1 : ℤ) ^ (leftScaleBit 6 2 6).val * positiveScale (leftScaleExponent 6 2 6)) •
      (rowColumnMul HexagonRowColumn626.rows_assocBAC HexagonRowColumn626.cols_left0)) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 6 2 6) • (rowColumnMul HexagonRowColumn626.rows_innerRightBAC HexagonRowColumn626.cols_left1)) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal6_case_2_6_row_1_1_0 : (((-1 : ℤ) ^ (leftScaleBit 6 2 6).val * positiveScale (leftScaleExponent 6 2 6)) •
      (rowColumnMul HexagonRowColumn626.rows_assocBAC HexagonRowColumn626.cols_left0)) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 6 2 6) • (rowColumnMul HexagonRowColumn626.rows_innerRightBAC HexagonRowColumn626.cols_left1)) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal6_case_2_6_row_1_1_1 : (((-1 : ℤ) ^ (leftScaleBit 6 2 6).val * positiveScale (leftScaleExponent 6 2 6)) •
      (rowColumnMul HexagonRowColumn626.rows_assocBAC HexagonRowColumn626.cols_left0)) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 6 2 6) • (rowColumnMul HexagonRowColumn626.rows_innerRightBAC HexagonRowColumn626.cols_left1)) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal6_case_2_6_row_1_1_2 : (((-1 : ℤ) ^ (leftScaleBit 6 2 6).val * positiveScale (leftScaleExponent 6 2 6)) •
      (rowColumnMul HexagonRowColumn626.rows_assocBAC HexagonRowColumn626.cols_left0)) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 6 2 6) • (rowColumnMul HexagonRowColumn626.rows_innerRightBAC HexagonRowColumn626.cols_left1)) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal6_case_2_6_row_1_1_3 : (((-1 : ℤ) ^ (leftScaleBit 6 2 6).val * positiveScale (leftScaleExponent 6 2 6)) •
      (rowColumnMul HexagonRowColumn626.rows_assocBAC HexagonRowColumn626.cols_left0)) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 6 2 6) • (rowColumnMul HexagonRowColumn626.rows_innerRightBAC HexagonRowColumn626.cols_left1)) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal6_case_2_6_checked : ((-1 : ℤ) ^ (leftScaleBit 6 2 6).val * positiveScale (leftScaleExponent 6 2 6)) •
      (rowColumnMul HexagonRowColumn626.rows_assocBAC HexagonRowColumn626.cols_left0) = negativeScale (leftScaleExponent 6 2 6) • (rowColumnMul HexagonRowColumn626.rows_innerRightBAC HexagonRowColumn626.cols_left1) := by
  funext r
  fin_cases r
  · exact leftFinal6_case_2_6_row_0_0_0
  · exact leftFinal6_case_2_6_row_0_0_1
  · exact leftFinal6_case_2_6_row_0_0_2
  · exact leftFinal6_case_2_6_row_0_0_3
  · exact leftFinal6_case_2_6_row_0_1_0
  · exact leftFinal6_case_2_6_row_0_1_1
  · exact leftFinal6_case_2_6_row_0_1_2
  · exact leftFinal6_case_2_6_row_0_1_3
  · exact leftFinal6_case_2_6_row_1_0_0
  · exact leftFinal6_case_2_6_row_1_0_1
  · exact leftFinal6_case_2_6_row_1_0_2
  · exact leftFinal6_case_2_6_row_1_0_3
  · exact leftFinal6_case_2_6_row_1_1_0
  · exact leftFinal6_case_2_6_row_1_1_1
  · exact leftFinal6_case_2_6_row_1_1_2
  · exact leftFinal6_case_2_6_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem leftFinal6_case_2_6 : ((-1 : ℤ) ^ (leftScaleBit 6 2 6).val * positiveScale (leftScaleExponent 6 2 6)) •
      (associatorZ 2 6 6 * left0Middle6 2 6) = negativeScale (leftScaleExponent 6 2 6) • (innerRightZ 2 6 6 * left1Middle6 2 6) := by
  simpa only [HexagonAtoms626.assocABC_eq,
    HexagonAtoms626.outerABC_eq,
    HexagonAtoms626.assocBAC_eq,
    HexagonAtoms626.innerABC_eq,
    HexagonAtoms626.innerRightABC_eq,
    HexagonAtoms626.inverseACB_eq,
    HexagonAtoms626.innerACB_eq,
    HexagonAtoms626.assocBCA_eq,
    HexagonAtoms626.innerRightBAC_eq,
    HexagonAtoms626.assocCAB_eq,
    HexagonAtoms626.outerLeftABC_eq,
    HexagonRowColumn626.assocBCA_alias,
    HexagonRowColumn626.product0_eq,
    HexagonRowColumn626.product1_eq,
    HexagonRowColumn626.product2_eq,
    HexagonRowColumn626.product3_eq,
    HexagonRowColumn626.product4_eq,
    HexagonRowColumn626.product5_eq,
    HexagonRowColumn626.product6_eq,
    HexagonRowColumn626.product7_eq] using leftFinal6_case_2_6_checked

private theorem rightFinal6_case_2_6_row_0_0_0 : (((-1 : ℤ) ^ (rightScaleBit 6 2 6).val * positiveScale (rightScaleExponent 6 2 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 6 2 : ℤ)) • HexagonAtoms626.outerLeftABC) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (negativeScale (rightScaleExponent 6 2 6) • (rowColumnMul HexagonRowColumn626.rows_assocCAB HexagonRowColumn626.cols_right2)) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal6_case_2_6_row_0_0_1 : (((-1 : ℤ) ^ (rightScaleBit 6 2 6).val * positiveScale (rightScaleExponent 6 2 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 6 2 : ℤ)) • HexagonAtoms626.outerLeftABC) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (negativeScale (rightScaleExponent 6 2 6) • (rowColumnMul HexagonRowColumn626.rows_assocCAB HexagonRowColumn626.cols_right2)) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal6_case_2_6_row_0_0_2 : (((-1 : ℤ) ^ (rightScaleBit 6 2 6).val * positiveScale (rightScaleExponent 6 2 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 6 2 : ℤ)) • HexagonAtoms626.outerLeftABC) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (negativeScale (rightScaleExponent 6 2 6) • (rowColumnMul HexagonRowColumn626.rows_assocCAB HexagonRowColumn626.cols_right2)) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal6_case_2_6_row_0_0_3 : (((-1 : ℤ) ^ (rightScaleBit 6 2 6).val * positiveScale (rightScaleExponent 6 2 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 6 2 : ℤ)) • HexagonAtoms626.outerLeftABC) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (negativeScale (rightScaleExponent 6 2 6) • (rowColumnMul HexagonRowColumn626.rows_assocCAB HexagonRowColumn626.cols_right2)) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal6_case_2_6_row_1_0_0 : (((-1 : ℤ) ^ (rightScaleBit 6 2 6).val * positiveScale (rightScaleExponent 6 2 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 6 2 : ℤ)) • HexagonAtoms626.outerLeftABC) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (negativeScale (rightScaleExponent 6 2 6) • (rowColumnMul HexagonRowColumn626.rows_assocCAB HexagonRowColumn626.cols_right2)) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal6_case_2_6_row_1_0_1 : (((-1 : ℤ) ^ (rightScaleBit 6 2 6).val * positiveScale (rightScaleExponent 6 2 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 6 2 : ℤ)) • HexagonAtoms626.outerLeftABC) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (negativeScale (rightScaleExponent 6 2 6) • (rowColumnMul HexagonRowColumn626.rows_assocCAB HexagonRowColumn626.cols_right2)) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal6_case_2_6_row_1_0_2 : (((-1 : ℤ) ^ (rightScaleBit 6 2 6).val * positiveScale (rightScaleExponent 6 2 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 6 2 : ℤ)) • HexagonAtoms626.outerLeftABC) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (negativeScale (rightScaleExponent 6 2 6) • (rowColumnMul HexagonRowColumn626.rows_assocCAB HexagonRowColumn626.cols_right2)) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal6_case_2_6_row_1_0_3 : (((-1 : ℤ) ^ (rightScaleBit 6 2 6).val * positiveScale (rightScaleExponent 6 2 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 6 2 : ℤ)) • HexagonAtoms626.outerLeftABC) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (negativeScale (rightScaleExponent 6 2 6) • (rowColumnMul HexagonRowColumn626.rows_assocCAB HexagonRowColumn626.cols_right2)) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal6_case_2_6_row_2_0_0 : (((-1 : ℤ) ^ (rightScaleBit 6 2 6).val * positiveScale (rightScaleExponent 6 2 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 6 2 : ℤ)) • HexagonAtoms626.outerLeftABC) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (negativeScale (rightScaleExponent 6 2 6) • (rowColumnMul HexagonRowColumn626.rows_assocCAB HexagonRowColumn626.cols_right2)) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal6_case_2_6_row_2_0_1 : (((-1 : ℤ) ^ (rightScaleBit 6 2 6).val * positiveScale (rightScaleExponent 6 2 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 6 2 : ℤ)) • HexagonAtoms626.outerLeftABC) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (negativeScale (rightScaleExponent 6 2 6) • (rowColumnMul HexagonRowColumn626.rows_assocCAB HexagonRowColumn626.cols_right2)) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal6_case_2_6_row_2_0_2 : (((-1 : ℤ) ^ (rightScaleBit 6 2 6).val * positiveScale (rightScaleExponent 6 2 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 6 2 : ℤ)) • HexagonAtoms626.outerLeftABC) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (negativeScale (rightScaleExponent 6 2 6) • (rowColumnMul HexagonRowColumn626.rows_assocCAB HexagonRowColumn626.cols_right2)) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal6_case_2_6_row_2_0_3 : (((-1 : ℤ) ^ (rightScaleBit 6 2 6).val * positiveScale (rightScaleExponent 6 2 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 6 2 : ℤ)) • HexagonAtoms626.outerLeftABC) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (negativeScale (rightScaleExponent 6 2 6) • (rowColumnMul HexagonRowColumn626.rows_assocCAB HexagonRowColumn626.cols_right2)) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal6_case_2_6_row_3_0_0 : (((-1 : ℤ) ^ (rightScaleBit 6 2 6).val * positiveScale (rightScaleExponent 6 2 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 6 2 : ℤ)) • HexagonAtoms626.outerLeftABC) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (negativeScale (rightScaleExponent 6 2 6) • (rowColumnMul HexagonRowColumn626.rows_assocCAB HexagonRowColumn626.cols_right2)) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal6_case_2_6_row_3_0_1 : (((-1 : ℤ) ^ (rightScaleBit 6 2 6).val * positiveScale (rightScaleExponent 6 2 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 6 2 : ℤ)) • HexagonAtoms626.outerLeftABC) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (negativeScale (rightScaleExponent 6 2 6) • (rowColumnMul HexagonRowColumn626.rows_assocCAB HexagonRowColumn626.cols_right2)) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal6_case_2_6_row_3_0_2 : (((-1 : ℤ) ^ (rightScaleBit 6 2 6).val * positiveScale (rightScaleExponent 6 2 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 6 2 : ℤ)) • HexagonAtoms626.outerLeftABC) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (negativeScale (rightScaleExponent 6 2 6) • (rowColumnMul HexagonRowColumn626.rows_assocCAB HexagonRowColumn626.cols_right2)) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal6_case_2_6_row_3_0_3 : (((-1 : ℤ) ^ (rightScaleBit 6 2 6).val * positiveScale (rightScaleExponent 6 2 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 6 2 : ℤ)) • HexagonAtoms626.outerLeftABC) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (negativeScale (rightScaleExponent 6 2 6) • (rowColumnMul HexagonRowColumn626.rows_assocCAB HexagonRowColumn626.cols_right2)) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal6_case_2_6_checked : ((-1 : ℤ) ^ (rightScaleBit 6 2 6).val * positiveScale (rightScaleExponent 6 2 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 6 2 : ℤ)) • HexagonAtoms626.outerLeftABC = negativeScale (rightScaleExponent 6 2 6) • (rowColumnMul HexagonRowColumn626.rows_assocCAB HexagonRowColumn626.cols_right2) := by
  funext r
  fin_cases r
  · exact rightFinal6_case_2_6_row_0_0_0
  · exact rightFinal6_case_2_6_row_0_0_1
  · exact rightFinal6_case_2_6_row_0_0_2
  · exact rightFinal6_case_2_6_row_0_0_3
  · exact rightFinal6_case_2_6_row_1_0_0
  · exact rightFinal6_case_2_6_row_1_0_1
  · exact rightFinal6_case_2_6_row_1_0_2
  · exact rightFinal6_case_2_6_row_1_0_3
  · exact rightFinal6_case_2_6_row_2_0_0
  · exact rightFinal6_case_2_6_row_2_0_1
  · exact rightFinal6_case_2_6_row_2_0_2
  · exact rightFinal6_case_2_6_row_2_0_3
  · exact rightFinal6_case_2_6_row_3_0_0
  · exact rightFinal6_case_2_6_row_3_0_1
  · exact rightFinal6_case_2_6_row_3_0_2
  · exact rightFinal6_case_2_6_row_3_0_3

set_option backward.isDefEq.respectTransparency false in
theorem rightFinal6_case_2_6 : ((-1 : ℤ) ^ (rightScaleBit 6 2 6).val * positiveScale (rightScaleExponent 6 2 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 6 2 : ℤ)) • outerLeftZ 6 2 6 = negativeScale (rightScaleExponent 6 2 6) • (associatorZ 6 6 2 * right2Middle6 2 6) := by
  simpa only [HexagonAtoms626.assocABC_eq,
    HexagonAtoms626.outerABC_eq,
    HexagonAtoms626.assocBAC_eq,
    HexagonAtoms626.innerABC_eq,
    HexagonAtoms626.innerRightABC_eq,
    HexagonAtoms626.inverseACB_eq,
    HexagonAtoms626.innerACB_eq,
    HexagonAtoms626.assocBCA_eq,
    HexagonAtoms626.innerRightBAC_eq,
    HexagonAtoms626.assocCAB_eq,
    HexagonAtoms626.outerLeftABC_eq,
    HexagonRowColumn626.assocBCA_alias,
    HexagonRowColumn626.product0_eq,
    HexagonRowColumn626.product1_eq,
    HexagonRowColumn626.product2_eq,
    HexagonRowColumn626.product3_eq,
    HexagonRowColumn626.product4_eq,
    HexagonRowColumn626.product5_eq,
    HexagonRowColumn626.product6_eq,
    HexagonRowColumn626.product7_eq] using rightFinal6_case_2_6_checked

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonCases6
