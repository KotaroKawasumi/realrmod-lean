import RMod.BrundanEllis.StackingReferenceHexagonMiddle6
import RMod.BrundanEllis.StackingReferenceSparseMatrixCheck
import RMod.BrundanEllis.StackingReferenceHexagonAtoms645
import RMod.BrundanEllis.StackingReferenceHexagonRowColumn645

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

private theorem left0Middle6_eq_case_4_5_row_0_0_0 : (left0Middle6 4 5) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (HexagonAtoms645.assocABC) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle6_eq_case_4_5_row_0_0_1 : (left0Middle6 4 5) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (HexagonAtoms645.assocABC) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle6_eq_case_4_5_row_0_1_0 : (left0Middle6 4 5) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (HexagonAtoms645.assocABC) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle6_eq_case_4_5_row_0_1_1 : (left0Middle6 4 5) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (HexagonAtoms645.assocABC) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle6_eq_case_4_5_row_1_0_0 : (left0Middle6 4 5) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (HexagonAtoms645.assocABC) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle6_eq_case_4_5_row_1_0_1 : (left0Middle6 4 5) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (HexagonAtoms645.assocABC) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle6_eq_case_4_5_row_1_1_0 : (left0Middle6 4 5) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (HexagonAtoms645.assocABC) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle6_eq_case_4_5_row_1_1_1 : (left0Middle6 4 5) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (HexagonAtoms645.assocABC) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle6_eq_case_4_5_row_2_0_0 : (left0Middle6 4 5) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (HexagonAtoms645.assocABC) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle6_eq_case_4_5_row_2_0_1 : (left0Middle6 4 5) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (HexagonAtoms645.assocABC) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle6_eq_case_4_5_row_2_1_0 : (left0Middle6 4 5) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (HexagonAtoms645.assocABC) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle6_eq_case_4_5_row_2_1_1 : (left0Middle6 4 5) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (HexagonAtoms645.assocABC) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle6_eq_case_4_5_row_3_0_0 : (left0Middle6 4 5) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (HexagonAtoms645.assocABC) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle6_eq_case_4_5_row_3_0_1 : (left0Middle6 4 5) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (HexagonAtoms645.assocABC) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle6_eq_case_4_5_row_3_1_0 : (left0Middle6 4 5) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (HexagonAtoms645.assocABC) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle6_eq_case_4_5_row_3_1_1 : (left0Middle6 4 5) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (HexagonAtoms645.assocABC) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle6_eq_case_4_5_checked : left0Middle6 4 5 = HexagonAtoms645.assocABC := by
  funext r
  fin_cases r
  · exact left0Middle6_eq_case_4_5_row_0_0_0
  · exact left0Middle6_eq_case_4_5_row_0_0_1
  · exact left0Middle6_eq_case_4_5_row_0_1_0
  · exact left0Middle6_eq_case_4_5_row_0_1_1
  · exact left0Middle6_eq_case_4_5_row_1_0_0
  · exact left0Middle6_eq_case_4_5_row_1_0_1
  · exact left0Middle6_eq_case_4_5_row_1_1_0
  · exact left0Middle6_eq_case_4_5_row_1_1_1
  · exact left0Middle6_eq_case_4_5_row_2_0_0
  · exact left0Middle6_eq_case_4_5_row_2_0_1
  · exact left0Middle6_eq_case_4_5_row_2_1_0
  · exact left0Middle6_eq_case_4_5_row_2_1_1
  · exact left0Middle6_eq_case_4_5_row_3_0_0
  · exact left0Middle6_eq_case_4_5_row_3_0_1
  · exact left0Middle6_eq_case_4_5_row_3_1_0
  · exact left0Middle6_eq_case_4_5_row_3_1_1

set_option backward.isDefEq.respectTransparency false in
theorem left0Middle6_eq_case_4_5 : left0Middle6 4 5 = outerRightZ 6 4 5 * associatorZ 6 4 5 := by
  simpa only [HexagonAtoms645.assocABC_eq,
    HexagonAtoms645.outerABC_eq,
    HexagonAtoms645.assocBAC_eq,
    HexagonAtoms645.innerABC_eq,
    HexagonAtoms645.innerRightABC_eq,
    HexagonAtoms645.inverseACB_eq,
    HexagonAtoms645.innerACB_eq,
    HexagonAtoms645.assocBCA_eq,
    HexagonAtoms645.innerRightBAC_eq,
    HexagonAtoms645.assocCAB_eq,
    HexagonAtoms645.outerLeftABC_eq,
    HexagonRowColumn645.product0_eq,
    HexagonRowColumn645.product1_eq,
    HexagonRowColumn645.product2_eq,
    HexagonRowColumn645.product3_eq,
    HexagonRowColumn645.product4_eq,
    HexagonRowColumn645.product5_eq,
    HexagonRowColumn645.product6_eq,
    HexagonRowColumn645.product7_eq] using left0Middle6_eq_case_4_5_checked

private theorem left1Middle6_eq_case_4_5_row_0_0_0 : (left1Middle6 4 5) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (HexagonAtoms645.assocBAC) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle6_eq_case_4_5_row_0_0_1 : (left1Middle6 4 5) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (HexagonAtoms645.assocBAC) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle6_eq_case_4_5_row_0_1_0 : (left1Middle6 4 5) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (HexagonAtoms645.assocBAC) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle6_eq_case_4_5_row_0_1_1 : (left1Middle6 4 5) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (HexagonAtoms645.assocBAC) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle6_eq_case_4_5_row_0_2_0 : (left1Middle6 4 5) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (HexagonAtoms645.assocBAC) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle6_eq_case_4_5_row_0_2_1 : (left1Middle6 4 5) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (HexagonAtoms645.assocBAC) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle6_eq_case_4_5_row_0_3_0 : (left1Middle6 4 5) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (HexagonAtoms645.assocBAC) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle6_eq_case_4_5_row_0_3_1 : (left1Middle6 4 5) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (HexagonAtoms645.assocBAC) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle6_eq_case_4_5_row_1_0_0 : (left1Middle6 4 5) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (HexagonAtoms645.assocBAC) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle6_eq_case_4_5_row_1_0_1 : (left1Middle6 4 5) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (HexagonAtoms645.assocBAC) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle6_eq_case_4_5_row_1_1_0 : (left1Middle6 4 5) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (HexagonAtoms645.assocBAC) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle6_eq_case_4_5_row_1_1_1 : (left1Middle6 4 5) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (HexagonAtoms645.assocBAC) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle6_eq_case_4_5_row_1_2_0 : (left1Middle6 4 5) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (HexagonAtoms645.assocBAC) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle6_eq_case_4_5_row_1_2_1 : (left1Middle6 4 5) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (HexagonAtoms645.assocBAC) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle6_eq_case_4_5_row_1_3_0 : (left1Middle6 4 5) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (HexagonAtoms645.assocBAC) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle6_eq_case_4_5_row_1_3_1 : (left1Middle6 4 5) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (HexagonAtoms645.assocBAC) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle6_eq_case_4_5_checked : left1Middle6 4 5 = HexagonAtoms645.assocBAC := by
  funext r
  fin_cases r
  · exact left1Middle6_eq_case_4_5_row_0_0_0
  · exact left1Middle6_eq_case_4_5_row_0_0_1
  · exact left1Middle6_eq_case_4_5_row_0_1_0
  · exact left1Middle6_eq_case_4_5_row_0_1_1
  · exact left1Middle6_eq_case_4_5_row_0_2_0
  · exact left1Middle6_eq_case_4_5_row_0_2_1
  · exact left1Middle6_eq_case_4_5_row_0_3_0
  · exact left1Middle6_eq_case_4_5_row_0_3_1
  · exact left1Middle6_eq_case_4_5_row_1_0_0
  · exact left1Middle6_eq_case_4_5_row_1_0_1
  · exact left1Middle6_eq_case_4_5_row_1_1_0
  · exact left1Middle6_eq_case_4_5_row_1_1_1
  · exact left1Middle6_eq_case_4_5_row_1_2_0
  · exact left1Middle6_eq_case_4_5_row_1_2_1
  · exact left1Middle6_eq_case_4_5_row_1_3_0
  · exact left1Middle6_eq_case_4_5_row_1_3_1

set_option backward.isDefEq.respectTransparency false in
theorem left1Middle6_eq_case_4_5 : left1Middle6 4 5 = associatorZ 4 6 5 * innerLeftZ 6 4 5 := by
  simpa only [HexagonAtoms645.assocABC_eq,
    HexagonAtoms645.outerABC_eq,
    HexagonAtoms645.assocBAC_eq,
    HexagonAtoms645.innerABC_eq,
    HexagonAtoms645.innerRightABC_eq,
    HexagonAtoms645.inverseACB_eq,
    HexagonAtoms645.innerACB_eq,
    HexagonAtoms645.assocBCA_eq,
    HexagonAtoms645.innerRightBAC_eq,
    HexagonAtoms645.assocCAB_eq,
    HexagonAtoms645.outerLeftABC_eq,
    HexagonRowColumn645.product0_eq,
    HexagonRowColumn645.product1_eq,
    HexagonRowColumn645.product2_eq,
    HexagonRowColumn645.product3_eq,
    HexagonRowColumn645.product4_eq,
    HexagonRowColumn645.product5_eq,
    HexagonRowColumn645.product6_eq,
    HexagonRowColumn645.product7_eq] using left1Middle6_eq_case_4_5_checked

private theorem right0Middle6_eq_case_4_5_row_0_0_0 : (right0Middle6 4 5) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (HexagonAtoms645.assocABC) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle6_eq_case_4_5_row_0_0_1 : (right0Middle6 4 5) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (HexagonAtoms645.assocABC) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle6_eq_case_4_5_row_0_1_0 : (right0Middle6 4 5) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (HexagonAtoms645.assocABC) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle6_eq_case_4_5_row_0_1_1 : (right0Middle6 4 5) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (HexagonAtoms645.assocABC) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle6_eq_case_4_5_row_1_0_0 : (right0Middle6 4 5) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (HexagonAtoms645.assocABC) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle6_eq_case_4_5_row_1_0_1 : (right0Middle6 4 5) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (HexagonAtoms645.assocABC) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle6_eq_case_4_5_row_1_1_0 : (right0Middle6 4 5) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (HexagonAtoms645.assocABC) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle6_eq_case_4_5_row_1_1_1 : (right0Middle6 4 5) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (HexagonAtoms645.assocABC) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle6_eq_case_4_5_row_2_0_0 : (right0Middle6 4 5) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (HexagonAtoms645.assocABC) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle6_eq_case_4_5_row_2_0_1 : (right0Middle6 4 5) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (HexagonAtoms645.assocABC) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle6_eq_case_4_5_row_2_1_0 : (right0Middle6 4 5) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (HexagonAtoms645.assocABC) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle6_eq_case_4_5_row_2_1_1 : (right0Middle6 4 5) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (HexagonAtoms645.assocABC) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle6_eq_case_4_5_row_3_0_0 : (right0Middle6 4 5) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (HexagonAtoms645.assocABC) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle6_eq_case_4_5_row_3_0_1 : (right0Middle6 4 5) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (HexagonAtoms645.assocABC) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle6_eq_case_4_5_row_3_1_0 : (right0Middle6 4 5) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (HexagonAtoms645.assocABC) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle6_eq_case_4_5_row_3_1_1 : (right0Middle6 4 5) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (HexagonAtoms645.assocABC) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle6_eq_case_4_5_checked : right0Middle6 4 5 = HexagonAtoms645.assocABC := by
  funext r
  fin_cases r
  · exact right0Middle6_eq_case_4_5_row_0_0_0
  · exact right0Middle6_eq_case_4_5_row_0_0_1
  · exact right0Middle6_eq_case_4_5_row_0_1_0
  · exact right0Middle6_eq_case_4_5_row_0_1_1
  · exact right0Middle6_eq_case_4_5_row_1_0_0
  · exact right0Middle6_eq_case_4_5_row_1_0_1
  · exact right0Middle6_eq_case_4_5_row_1_1_0
  · exact right0Middle6_eq_case_4_5_row_1_1_1
  · exact right0Middle6_eq_case_4_5_row_2_0_0
  · exact right0Middle6_eq_case_4_5_row_2_0_1
  · exact right0Middle6_eq_case_4_5_row_2_1_0
  · exact right0Middle6_eq_case_4_5_row_2_1_1
  · exact right0Middle6_eq_case_4_5_row_3_0_0
  · exact right0Middle6_eq_case_4_5_row_3_0_1
  · exact right0Middle6_eq_case_4_5_row_3_1_0
  · exact right0Middle6_eq_case_4_5_row_3_1_1

set_option backward.isDefEq.respectTransparency false in
theorem right0Middle6_eq_case_4_5 : right0Middle6 4 5 = innerRightZ 6 4 5 * associatorZ 6 4 5 := by
  simpa only [HexagonAtoms645.assocABC_eq,
    HexagonAtoms645.outerABC_eq,
    HexagonAtoms645.assocBAC_eq,
    HexagonAtoms645.innerABC_eq,
    HexagonAtoms645.innerRightABC_eq,
    HexagonAtoms645.inverseACB_eq,
    HexagonAtoms645.innerACB_eq,
    HexagonAtoms645.assocBCA_eq,
    HexagonAtoms645.innerRightBAC_eq,
    HexagonAtoms645.assocCAB_eq,
    HexagonAtoms645.outerLeftABC_eq,
    HexagonRowColumn645.product0_eq,
    HexagonRowColumn645.product1_eq,
    HexagonRowColumn645.product2_eq,
    HexagonRowColumn645.product3_eq,
    HexagonRowColumn645.product4_eq,
    HexagonRowColumn645.product5_eq,
    HexagonRowColumn645.product6_eq,
    HexagonRowColumn645.product7_eq] using right0Middle6_eq_case_4_5_checked

private theorem right1Middle6_eq_case_4_5_row_0_0_0 : (right1Middle6 4 5) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn645.rows_inverseACB HexagonRowColumn645.cols_right0) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle6_eq_case_4_5_row_0_0_1 : (right1Middle6 4 5) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn645.rows_inverseACB HexagonRowColumn645.cols_right0) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle6_eq_case_4_5_row_0_1_0 : (right1Middle6 4 5) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn645.rows_inverseACB HexagonRowColumn645.cols_right0) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle6_eq_case_4_5_row_0_1_1 : (right1Middle6 4 5) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn645.rows_inverseACB HexagonRowColumn645.cols_right0) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle6_eq_case_4_5_row_0_2_0 : (right1Middle6 4 5) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn645.rows_inverseACB HexagonRowColumn645.cols_right0) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle6_eq_case_4_5_row_0_2_1 : (right1Middle6 4 5) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn645.rows_inverseACB HexagonRowColumn645.cols_right0) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle6_eq_case_4_5_row_0_3_0 : (right1Middle6 4 5) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn645.rows_inverseACB HexagonRowColumn645.cols_right0) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle6_eq_case_4_5_row_0_3_1 : (right1Middle6 4 5) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn645.rows_inverseACB HexagonRowColumn645.cols_right0) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle6_eq_case_4_5_row_1_0_0 : (right1Middle6 4 5) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn645.rows_inverseACB HexagonRowColumn645.cols_right0) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle6_eq_case_4_5_row_1_0_1 : (right1Middle6 4 5) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn645.rows_inverseACB HexagonRowColumn645.cols_right0) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle6_eq_case_4_5_row_1_1_0 : (right1Middle6 4 5) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn645.rows_inverseACB HexagonRowColumn645.cols_right0) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle6_eq_case_4_5_row_1_1_1 : (right1Middle6 4 5) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn645.rows_inverseACB HexagonRowColumn645.cols_right0) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle6_eq_case_4_5_row_1_2_0 : (right1Middle6 4 5) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn645.rows_inverseACB HexagonRowColumn645.cols_right0) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle6_eq_case_4_5_row_1_2_1 : (right1Middle6 4 5) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn645.rows_inverseACB HexagonRowColumn645.cols_right0) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle6_eq_case_4_5_row_1_3_0 : (right1Middle6 4 5) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn645.rows_inverseACB HexagonRowColumn645.cols_right0) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle6_eq_case_4_5_row_1_3_1 : (right1Middle6 4 5) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn645.rows_inverseACB HexagonRowColumn645.cols_right0) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle6_eq_case_4_5_checked : right1Middle6 4 5 = rowColumnMul HexagonRowColumn645.rows_inverseACB HexagonRowColumn645.cols_right0 := by
  funext r
  fin_cases r
  · exact right1Middle6_eq_case_4_5_row_0_0_0
  · exact right1Middle6_eq_case_4_5_row_0_0_1
  · exact right1Middle6_eq_case_4_5_row_0_1_0
  · exact right1Middle6_eq_case_4_5_row_0_1_1
  · exact right1Middle6_eq_case_4_5_row_0_2_0
  · exact right1Middle6_eq_case_4_5_row_0_2_1
  · exact right1Middle6_eq_case_4_5_row_0_3_0
  · exact right1Middle6_eq_case_4_5_row_0_3_1
  · exact right1Middle6_eq_case_4_5_row_1_0_0
  · exact right1Middle6_eq_case_4_5_row_1_0_1
  · exact right1Middle6_eq_case_4_5_row_1_1_0
  · exact right1Middle6_eq_case_4_5_row_1_1_1
  · exact right1Middle6_eq_case_4_5_row_1_2_0
  · exact right1Middle6_eq_case_4_5_row_1_2_1
  · exact right1Middle6_eq_case_4_5_row_1_3_0
  · exact right1Middle6_eq_case_4_5_row_1_3_1

set_option backward.isDefEq.respectTransparency false in
theorem right1Middle6_eq_case_4_5 : right1Middle6 4 5 = associatorInverseZ 6 5 4 * right0Middle6 4 5 := by
  simpa only [HexagonAtoms645.assocABC_eq,
    HexagonAtoms645.outerABC_eq,
    HexagonAtoms645.assocBAC_eq,
    HexagonAtoms645.innerABC_eq,
    HexagonAtoms645.innerRightABC_eq,
    HexagonAtoms645.inverseACB_eq,
    HexagonAtoms645.innerACB_eq,
    HexagonAtoms645.assocBCA_eq,
    HexagonAtoms645.innerRightBAC_eq,
    HexagonAtoms645.assocCAB_eq,
    HexagonAtoms645.outerLeftABC_eq,
    HexagonRowColumn645.product0_eq,
    HexagonRowColumn645.product1_eq,
    HexagonRowColumn645.product2_eq,
    HexagonRowColumn645.product3_eq,
    HexagonRowColumn645.product4_eq,
    HexagonRowColumn645.product5_eq,
    HexagonRowColumn645.product6_eq,
    HexagonRowColumn645.product7_eq] using right1Middle6_eq_case_4_5_checked

private theorem right2Middle6_eq_case_4_5_row_0_0_0 : (right2Middle6 4 5) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (right1Middle6 4 5) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle6_eq_case_4_5_row_0_0_1 : (right2Middle6 4 5) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (right1Middle6 4 5) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle6_eq_case_4_5_row_0_1_0 : (right2Middle6 4 5) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (right1Middle6 4 5) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle6_eq_case_4_5_row_0_1_1 : (right2Middle6 4 5) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (right1Middle6 4 5) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle6_eq_case_4_5_row_0_2_0 : (right2Middle6 4 5) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (right1Middle6 4 5) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle6_eq_case_4_5_row_0_2_1 : (right2Middle6 4 5) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (right1Middle6 4 5) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle6_eq_case_4_5_row_0_3_0 : (right2Middle6 4 5) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (right1Middle6 4 5) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle6_eq_case_4_5_row_0_3_1 : (right2Middle6 4 5) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (right1Middle6 4 5) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle6_eq_case_4_5_row_1_0_0 : (right2Middle6 4 5) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (right1Middle6 4 5) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle6_eq_case_4_5_row_1_0_1 : (right2Middle6 4 5) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (right1Middle6 4 5) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle6_eq_case_4_5_row_1_1_0 : (right2Middle6 4 5) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (right1Middle6 4 5) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle6_eq_case_4_5_row_1_1_1 : (right2Middle6 4 5) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (right1Middle6 4 5) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle6_eq_case_4_5_row_1_2_0 : (right2Middle6 4 5) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (right1Middle6 4 5) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle6_eq_case_4_5_row_1_2_1 : (right2Middle6 4 5) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (right1Middle6 4 5) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle6_eq_case_4_5_row_1_3_0 : (right2Middle6 4 5) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (right1Middle6 4 5) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle6_eq_case_4_5_row_1_3_1 : (right2Middle6 4 5) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (right1Middle6 4 5) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle6_eq_case_4_5_checked : right2Middle6 4 5 = right1Middle6 4 5 := by
  funext r
  fin_cases r
  · exact right2Middle6_eq_case_4_5_row_0_0_0
  · exact right2Middle6_eq_case_4_5_row_0_0_1
  · exact right2Middle6_eq_case_4_5_row_0_1_0
  · exact right2Middle6_eq_case_4_5_row_0_1_1
  · exact right2Middle6_eq_case_4_5_row_0_2_0
  · exact right2Middle6_eq_case_4_5_row_0_2_1
  · exact right2Middle6_eq_case_4_5_row_0_3_0
  · exact right2Middle6_eq_case_4_5_row_0_3_1
  · exact right2Middle6_eq_case_4_5_row_1_0_0
  · exact right2Middle6_eq_case_4_5_row_1_0_1
  · exact right2Middle6_eq_case_4_5_row_1_1_0
  · exact right2Middle6_eq_case_4_5_row_1_1_1
  · exact right2Middle6_eq_case_4_5_row_1_2_0
  · exact right2Middle6_eq_case_4_5_row_1_2_1
  · exact right2Middle6_eq_case_4_5_row_1_3_0
  · exact right2Middle6_eq_case_4_5_row_1_3_1

set_option backward.isDefEq.respectTransparency false in
theorem right2Middle6_eq_case_4_5 : right2Middle6 4 5 = innerLeftZ 6 5 4 * right1Middle6 4 5 := by
  simpa only [HexagonAtoms645.assocABC_eq,
    HexagonAtoms645.outerABC_eq,
    HexagonAtoms645.assocBAC_eq,
    HexagonAtoms645.innerABC_eq,
    HexagonAtoms645.innerRightABC_eq,
    HexagonAtoms645.inverseACB_eq,
    HexagonAtoms645.innerACB_eq,
    HexagonAtoms645.assocBCA_eq,
    HexagonAtoms645.innerRightBAC_eq,
    HexagonAtoms645.assocCAB_eq,
    HexagonAtoms645.outerLeftABC_eq,
    HexagonRowColumn645.product0_eq,
    HexagonRowColumn645.product1_eq,
    HexagonRowColumn645.product2_eq,
    HexagonRowColumn645.product3_eq,
    HexagonRowColumn645.product4_eq,
    HexagonRowColumn645.product5_eq,
    HexagonRowColumn645.product6_eq,
    HexagonRowColumn645.product7_eq] using right2Middle6_eq_case_4_5_checked

private theorem leftFinal6_case_4_5_row_0_0_0 : (((-1 : ℤ) ^ (leftScaleBit 6 4 5).val * positiveScale (leftScaleExponent 6 4 5)) •
      (rowColumnMul HexagonRowColumn645.rows_assocBCA HexagonRowColumn645.cols_left0)) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 6 4 5) • (left1Middle6 4 5)) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal6_case_4_5_row_0_0_1 : (((-1 : ℤ) ^ (leftScaleBit 6 4 5).val * positiveScale (leftScaleExponent 6 4 5)) •
      (rowColumnMul HexagonRowColumn645.rows_assocBCA HexagonRowColumn645.cols_left0)) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 6 4 5) • (left1Middle6 4 5)) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal6_case_4_5_row_0_1_0 : (((-1 : ℤ) ^ (leftScaleBit 6 4 5).val * positiveScale (leftScaleExponent 6 4 5)) •
      (rowColumnMul HexagonRowColumn645.rows_assocBCA HexagonRowColumn645.cols_left0)) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 6 4 5) • (left1Middle6 4 5)) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal6_case_4_5_row_0_1_1 : (((-1 : ℤ) ^ (leftScaleBit 6 4 5).val * positiveScale (leftScaleExponent 6 4 5)) •
      (rowColumnMul HexagonRowColumn645.rows_assocBCA HexagonRowColumn645.cols_left0)) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 6 4 5) • (left1Middle6 4 5)) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal6_case_4_5_row_0_2_0 : (((-1 : ℤ) ^ (leftScaleBit 6 4 5).val * positiveScale (leftScaleExponent 6 4 5)) •
      (rowColumnMul HexagonRowColumn645.rows_assocBCA HexagonRowColumn645.cols_left0)) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 6 4 5) • (left1Middle6 4 5)) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal6_case_4_5_row_0_2_1 : (((-1 : ℤ) ^ (leftScaleBit 6 4 5).val * positiveScale (leftScaleExponent 6 4 5)) •
      (rowColumnMul HexagonRowColumn645.rows_assocBCA HexagonRowColumn645.cols_left0)) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 6 4 5) • (left1Middle6 4 5)) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal6_case_4_5_row_0_3_0 : (((-1 : ℤ) ^ (leftScaleBit 6 4 5).val * positiveScale (leftScaleExponent 6 4 5)) •
      (rowColumnMul HexagonRowColumn645.rows_assocBCA HexagonRowColumn645.cols_left0)) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 6 4 5) • (left1Middle6 4 5)) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal6_case_4_5_row_0_3_1 : (((-1 : ℤ) ^ (leftScaleBit 6 4 5).val * positiveScale (leftScaleExponent 6 4 5)) •
      (rowColumnMul HexagonRowColumn645.rows_assocBCA HexagonRowColumn645.cols_left0)) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 6 4 5) • (left1Middle6 4 5)) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal6_case_4_5_row_1_0_0 : (((-1 : ℤ) ^ (leftScaleBit 6 4 5).val * positiveScale (leftScaleExponent 6 4 5)) •
      (rowColumnMul HexagonRowColumn645.rows_assocBCA HexagonRowColumn645.cols_left0)) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 6 4 5) • (left1Middle6 4 5)) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal6_case_4_5_row_1_0_1 : (((-1 : ℤ) ^ (leftScaleBit 6 4 5).val * positiveScale (leftScaleExponent 6 4 5)) •
      (rowColumnMul HexagonRowColumn645.rows_assocBCA HexagonRowColumn645.cols_left0)) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 6 4 5) • (left1Middle6 4 5)) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal6_case_4_5_row_1_1_0 : (((-1 : ℤ) ^ (leftScaleBit 6 4 5).val * positiveScale (leftScaleExponent 6 4 5)) •
      (rowColumnMul HexagonRowColumn645.rows_assocBCA HexagonRowColumn645.cols_left0)) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 6 4 5) • (left1Middle6 4 5)) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal6_case_4_5_row_1_1_1 : (((-1 : ℤ) ^ (leftScaleBit 6 4 5).val * positiveScale (leftScaleExponent 6 4 5)) •
      (rowColumnMul HexagonRowColumn645.rows_assocBCA HexagonRowColumn645.cols_left0)) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 6 4 5) • (left1Middle6 4 5)) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal6_case_4_5_row_1_2_0 : (((-1 : ℤ) ^ (leftScaleBit 6 4 5).val * positiveScale (leftScaleExponent 6 4 5)) •
      (rowColumnMul HexagonRowColumn645.rows_assocBCA HexagonRowColumn645.cols_left0)) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 6 4 5) • (left1Middle6 4 5)) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal6_case_4_5_row_1_2_1 : (((-1 : ℤ) ^ (leftScaleBit 6 4 5).val * positiveScale (leftScaleExponent 6 4 5)) •
      (rowColumnMul HexagonRowColumn645.rows_assocBCA HexagonRowColumn645.cols_left0)) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 6 4 5) • (left1Middle6 4 5)) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal6_case_4_5_row_1_3_0 : (((-1 : ℤ) ^ (leftScaleBit 6 4 5).val * positiveScale (leftScaleExponent 6 4 5)) •
      (rowColumnMul HexagonRowColumn645.rows_assocBCA HexagonRowColumn645.cols_left0)) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 6 4 5) • (left1Middle6 4 5)) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal6_case_4_5_row_1_3_1 : (((-1 : ℤ) ^ (leftScaleBit 6 4 5).val * positiveScale (leftScaleExponent 6 4 5)) •
      (rowColumnMul HexagonRowColumn645.rows_assocBCA HexagonRowColumn645.cols_left0)) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 6 4 5) • (left1Middle6 4 5)) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal6_case_4_5_checked : ((-1 : ℤ) ^ (leftScaleBit 6 4 5).val * positiveScale (leftScaleExponent 6 4 5)) •
      (rowColumnMul HexagonRowColumn645.rows_assocBCA HexagonRowColumn645.cols_left0) = negativeScale (leftScaleExponent 6 4 5) • (left1Middle6 4 5) := by
  funext r
  fin_cases r
  · exact leftFinal6_case_4_5_row_0_0_0
  · exact leftFinal6_case_4_5_row_0_0_1
  · exact leftFinal6_case_4_5_row_0_1_0
  · exact leftFinal6_case_4_5_row_0_1_1
  · exact leftFinal6_case_4_5_row_0_2_0
  · exact leftFinal6_case_4_5_row_0_2_1
  · exact leftFinal6_case_4_5_row_0_3_0
  · exact leftFinal6_case_4_5_row_0_3_1
  · exact leftFinal6_case_4_5_row_1_0_0
  · exact leftFinal6_case_4_5_row_1_0_1
  · exact leftFinal6_case_4_5_row_1_1_0
  · exact leftFinal6_case_4_5_row_1_1_1
  · exact leftFinal6_case_4_5_row_1_2_0
  · exact leftFinal6_case_4_5_row_1_2_1
  · exact leftFinal6_case_4_5_row_1_3_0
  · exact leftFinal6_case_4_5_row_1_3_1

set_option backward.isDefEq.respectTransparency false in
theorem leftFinal6_case_4_5 : ((-1 : ℤ) ^ (leftScaleBit 6 4 5).val * positiveScale (leftScaleExponent 6 4 5)) •
      (associatorZ 4 5 6 * left0Middle6 4 5) = negativeScale (leftScaleExponent 6 4 5) • (innerRightZ 4 6 5 * left1Middle6 4 5) := by
  simpa only [HexagonAtoms645.assocABC_eq,
    HexagonAtoms645.outerABC_eq,
    HexagonAtoms645.assocBAC_eq,
    HexagonAtoms645.innerABC_eq,
    HexagonAtoms645.innerRightABC_eq,
    HexagonAtoms645.inverseACB_eq,
    HexagonAtoms645.innerACB_eq,
    HexagonAtoms645.assocBCA_eq,
    HexagonAtoms645.innerRightBAC_eq,
    HexagonAtoms645.assocCAB_eq,
    HexagonAtoms645.outerLeftABC_eq,
    HexagonRowColumn645.product0_eq,
    HexagonRowColumn645.product1_eq,
    HexagonRowColumn645.product2_eq,
    HexagonRowColumn645.product3_eq,
    HexagonRowColumn645.product4_eq,
    HexagonRowColumn645.product5_eq,
    HexagonRowColumn645.product6_eq,
    HexagonRowColumn645.product7_eq] using leftFinal6_case_4_5_checked

private theorem rightFinal6_case_4_5_row_0_0_0 : (((-1 : ℤ) ^ (rightScaleBit 6 4 5).val * positiveScale (rightScaleExponent 6 4 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 4 : ℤ)) • HexagonAtoms645.outerLeftABC) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (negativeScale (rightScaleExponent 6 4 5) • (rowColumnMul HexagonRowColumn645.rows_assocCAB HexagonRowColumn645.cols_right2)) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal6_case_4_5_row_0_0_1 : (((-1 : ℤ) ^ (rightScaleBit 6 4 5).val * positiveScale (rightScaleExponent 6 4 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 4 : ℤ)) • HexagonAtoms645.outerLeftABC) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (negativeScale (rightScaleExponent 6 4 5) • (rowColumnMul HexagonRowColumn645.rows_assocCAB HexagonRowColumn645.cols_right2)) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal6_case_4_5_row_0_1_0 : (((-1 : ℤ) ^ (rightScaleBit 6 4 5).val * positiveScale (rightScaleExponent 6 4 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 4 : ℤ)) • HexagonAtoms645.outerLeftABC) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (negativeScale (rightScaleExponent 6 4 5) • (rowColumnMul HexagonRowColumn645.rows_assocCAB HexagonRowColumn645.cols_right2)) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal6_case_4_5_row_0_1_1 : (((-1 : ℤ) ^ (rightScaleBit 6 4 5).val * positiveScale (rightScaleExponent 6 4 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 4 : ℤ)) • HexagonAtoms645.outerLeftABC) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (negativeScale (rightScaleExponent 6 4 5) • (rowColumnMul HexagonRowColumn645.rows_assocCAB HexagonRowColumn645.cols_right2)) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal6_case_4_5_row_0_2_0 : (((-1 : ℤ) ^ (rightScaleBit 6 4 5).val * positiveScale (rightScaleExponent 6 4 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 4 : ℤ)) • HexagonAtoms645.outerLeftABC) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (negativeScale (rightScaleExponent 6 4 5) • (rowColumnMul HexagonRowColumn645.rows_assocCAB HexagonRowColumn645.cols_right2)) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal6_case_4_5_row_0_2_1 : (((-1 : ℤ) ^ (rightScaleBit 6 4 5).val * positiveScale (rightScaleExponent 6 4 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 4 : ℤ)) • HexagonAtoms645.outerLeftABC) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (negativeScale (rightScaleExponent 6 4 5) • (rowColumnMul HexagonRowColumn645.rows_assocCAB HexagonRowColumn645.cols_right2)) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal6_case_4_5_row_0_3_0 : (((-1 : ℤ) ^ (rightScaleBit 6 4 5).val * positiveScale (rightScaleExponent 6 4 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 4 : ℤ)) • HexagonAtoms645.outerLeftABC) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (negativeScale (rightScaleExponent 6 4 5) • (rowColumnMul HexagonRowColumn645.rows_assocCAB HexagonRowColumn645.cols_right2)) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal6_case_4_5_row_0_3_1 : (((-1 : ℤ) ^ (rightScaleBit 6 4 5).val * positiveScale (rightScaleExponent 6 4 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 4 : ℤ)) • HexagonAtoms645.outerLeftABC) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (negativeScale (rightScaleExponent 6 4 5) • (rowColumnMul HexagonRowColumn645.rows_assocCAB HexagonRowColumn645.cols_right2)) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal6_case_4_5_row_1_0_0 : (((-1 : ℤ) ^ (rightScaleBit 6 4 5).val * positiveScale (rightScaleExponent 6 4 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 4 : ℤ)) • HexagonAtoms645.outerLeftABC) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (negativeScale (rightScaleExponent 6 4 5) • (rowColumnMul HexagonRowColumn645.rows_assocCAB HexagonRowColumn645.cols_right2)) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal6_case_4_5_row_1_0_1 : (((-1 : ℤ) ^ (rightScaleBit 6 4 5).val * positiveScale (rightScaleExponent 6 4 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 4 : ℤ)) • HexagonAtoms645.outerLeftABC) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (negativeScale (rightScaleExponent 6 4 5) • (rowColumnMul HexagonRowColumn645.rows_assocCAB HexagonRowColumn645.cols_right2)) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal6_case_4_5_row_1_1_0 : (((-1 : ℤ) ^ (rightScaleBit 6 4 5).val * positiveScale (rightScaleExponent 6 4 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 4 : ℤ)) • HexagonAtoms645.outerLeftABC) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (negativeScale (rightScaleExponent 6 4 5) • (rowColumnMul HexagonRowColumn645.rows_assocCAB HexagonRowColumn645.cols_right2)) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal6_case_4_5_row_1_1_1 : (((-1 : ℤ) ^ (rightScaleBit 6 4 5).val * positiveScale (rightScaleExponent 6 4 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 4 : ℤ)) • HexagonAtoms645.outerLeftABC) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (negativeScale (rightScaleExponent 6 4 5) • (rowColumnMul HexagonRowColumn645.rows_assocCAB HexagonRowColumn645.cols_right2)) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal6_case_4_5_row_1_2_0 : (((-1 : ℤ) ^ (rightScaleBit 6 4 5).val * positiveScale (rightScaleExponent 6 4 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 4 : ℤ)) • HexagonAtoms645.outerLeftABC) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (negativeScale (rightScaleExponent 6 4 5) • (rowColumnMul HexagonRowColumn645.rows_assocCAB HexagonRowColumn645.cols_right2)) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal6_case_4_5_row_1_2_1 : (((-1 : ℤ) ^ (rightScaleBit 6 4 5).val * positiveScale (rightScaleExponent 6 4 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 4 : ℤ)) • HexagonAtoms645.outerLeftABC) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (negativeScale (rightScaleExponent 6 4 5) • (rowColumnMul HexagonRowColumn645.rows_assocCAB HexagonRowColumn645.cols_right2)) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal6_case_4_5_row_1_3_0 : (((-1 : ℤ) ^ (rightScaleBit 6 4 5).val * positiveScale (rightScaleExponent 6 4 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 4 : ℤ)) • HexagonAtoms645.outerLeftABC) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (negativeScale (rightScaleExponent 6 4 5) • (rowColumnMul HexagonRowColumn645.rows_assocCAB HexagonRowColumn645.cols_right2)) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal6_case_4_5_row_1_3_1 : (((-1 : ℤ) ^ (rightScaleBit 6 4 5).val * positiveScale (rightScaleExponent 6 4 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 4 : ℤ)) • HexagonAtoms645.outerLeftABC) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (negativeScale (rightScaleExponent 6 4 5) • (rowColumnMul HexagonRowColumn645.rows_assocCAB HexagonRowColumn645.cols_right2)) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal6_case_4_5_checked : ((-1 : ℤ) ^ (rightScaleBit 6 4 5).val * positiveScale (rightScaleExponent 6 4 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 4 : ℤ)) • HexagonAtoms645.outerLeftABC = negativeScale (rightScaleExponent 6 4 5) • (rowColumnMul HexagonRowColumn645.rows_assocCAB HexagonRowColumn645.cols_right2) := by
  funext r
  fin_cases r
  · exact rightFinal6_case_4_5_row_0_0_0
  · exact rightFinal6_case_4_5_row_0_0_1
  · exact rightFinal6_case_4_5_row_0_1_0
  · exact rightFinal6_case_4_5_row_0_1_1
  · exact rightFinal6_case_4_5_row_0_2_0
  · exact rightFinal6_case_4_5_row_0_2_1
  · exact rightFinal6_case_4_5_row_0_3_0
  · exact rightFinal6_case_4_5_row_0_3_1
  · exact rightFinal6_case_4_5_row_1_0_0
  · exact rightFinal6_case_4_5_row_1_0_1
  · exact rightFinal6_case_4_5_row_1_1_0
  · exact rightFinal6_case_4_5_row_1_1_1
  · exact rightFinal6_case_4_5_row_1_2_0
  · exact rightFinal6_case_4_5_row_1_2_1
  · exact rightFinal6_case_4_5_row_1_3_0
  · exact rightFinal6_case_4_5_row_1_3_1

set_option backward.isDefEq.respectTransparency false in
theorem rightFinal6_case_4_5 : ((-1 : ℤ) ^ (rightScaleBit 6 4 5).val * positiveScale (rightScaleExponent 6 4 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 5 4 : ℤ)) • outerLeftZ 6 4 5 = negativeScale (rightScaleExponent 6 4 5) • (associatorZ 5 6 4 * right2Middle6 4 5) := by
  simpa only [HexagonAtoms645.assocABC_eq,
    HexagonAtoms645.outerABC_eq,
    HexagonAtoms645.assocBAC_eq,
    HexagonAtoms645.innerABC_eq,
    HexagonAtoms645.innerRightABC_eq,
    HexagonAtoms645.inverseACB_eq,
    HexagonAtoms645.innerACB_eq,
    HexagonAtoms645.assocBCA_eq,
    HexagonAtoms645.innerRightBAC_eq,
    HexagonAtoms645.assocCAB_eq,
    HexagonAtoms645.outerLeftABC_eq,
    HexagonRowColumn645.product0_eq,
    HexagonRowColumn645.product1_eq,
    HexagonRowColumn645.product2_eq,
    HexagonRowColumn645.product3_eq,
    HexagonRowColumn645.product4_eq,
    HexagonRowColumn645.product5_eq,
    HexagonRowColumn645.product6_eq,
    HexagonRowColumn645.product7_eq] using rightFinal6_case_4_5_checked

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonCases6
