import RMod.BrundanEllis.StackingReferenceHexagonMiddle3
import RMod.BrundanEllis.StackingReferenceSparseMatrixCheck
import RMod.BrundanEllis.StackingReferenceHexagonAtoms302
import RMod.BrundanEllis.StackingReferenceHexagonRowColumn302

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

private theorem left0Middle3_eq_case_0_2_row_0_0_0 : (left0Middle3 0 2) ((0 : Fin 1), (0 : Fin 2), (0 : Fin 8)) = (HexagonAtoms302.assocABC) ((0 : Fin 1), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 1) (b := 2) (c := 8)
  decide +kernel

private theorem left0Middle3_eq_case_0_2_row_0_0_1 : (left0Middle3 0 2) ((0 : Fin 1), (0 : Fin 2), (1 : Fin 8)) = (HexagonAtoms302.assocABC) ((0 : Fin 1), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 1) (b := 2) (c := 8)
  decide +kernel

private theorem left0Middle3_eq_case_0_2_row_0_0_2 : (left0Middle3 0 2) ((0 : Fin 1), (0 : Fin 2), (2 : Fin 8)) = (HexagonAtoms302.assocABC) ((0 : Fin 1), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 1) (b := 2) (c := 8)
  decide +kernel

private theorem left0Middle3_eq_case_0_2_row_0_0_3 : (left0Middle3 0 2) ((0 : Fin 1), (0 : Fin 2), (3 : Fin 8)) = (HexagonAtoms302.assocABC) ((0 : Fin 1), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 1) (b := 2) (c := 8)
  decide +kernel

private theorem left0Middle3_eq_case_0_2_row_0_0_4 : (left0Middle3 0 2) ((0 : Fin 1), (0 : Fin 2), (4 : Fin 8)) = (HexagonAtoms302.assocABC) ((0 : Fin 1), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 1) (b := 2) (c := 8)
  decide +kernel

private theorem left0Middle3_eq_case_0_2_row_0_0_5 : (left0Middle3 0 2) ((0 : Fin 1), (0 : Fin 2), (5 : Fin 8)) = (HexagonAtoms302.assocABC) ((0 : Fin 1), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 1) (b := 2) (c := 8)
  decide +kernel

private theorem left0Middle3_eq_case_0_2_row_0_0_6 : (left0Middle3 0 2) ((0 : Fin 1), (0 : Fin 2), (6 : Fin 8)) = (HexagonAtoms302.assocABC) ((0 : Fin 1), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 1) (b := 2) (c := 8)
  decide +kernel

private theorem left0Middle3_eq_case_0_2_row_0_0_7 : (left0Middle3 0 2) ((0 : Fin 1), (0 : Fin 2), (7 : Fin 8)) = (HexagonAtoms302.assocABC) ((0 : Fin 1), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 1) (b := 2) (c := 8)
  decide +kernel

private theorem left0Middle3_eq_case_0_2_row_0_1_0 : (left0Middle3 0 2) ((0 : Fin 1), (1 : Fin 2), (0 : Fin 8)) = (HexagonAtoms302.assocABC) ((0 : Fin 1), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 1) (b := 2) (c := 8)
  decide +kernel

private theorem left0Middle3_eq_case_0_2_row_0_1_1 : (left0Middle3 0 2) ((0 : Fin 1), (1 : Fin 2), (1 : Fin 8)) = (HexagonAtoms302.assocABC) ((0 : Fin 1), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 1) (b := 2) (c := 8)
  decide +kernel

private theorem left0Middle3_eq_case_0_2_row_0_1_2 : (left0Middle3 0 2) ((0 : Fin 1), (1 : Fin 2), (2 : Fin 8)) = (HexagonAtoms302.assocABC) ((0 : Fin 1), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 1) (b := 2) (c := 8)
  decide +kernel

private theorem left0Middle3_eq_case_0_2_row_0_1_3 : (left0Middle3 0 2) ((0 : Fin 1), (1 : Fin 2), (3 : Fin 8)) = (HexagonAtoms302.assocABC) ((0 : Fin 1), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 1) (b := 2) (c := 8)
  decide +kernel

private theorem left0Middle3_eq_case_0_2_row_0_1_4 : (left0Middle3 0 2) ((0 : Fin 1), (1 : Fin 2), (4 : Fin 8)) = (HexagonAtoms302.assocABC) ((0 : Fin 1), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 1) (b := 2) (c := 8)
  decide +kernel

private theorem left0Middle3_eq_case_0_2_row_0_1_5 : (left0Middle3 0 2) ((0 : Fin 1), (1 : Fin 2), (5 : Fin 8)) = (HexagonAtoms302.assocABC) ((0 : Fin 1), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 1) (b := 2) (c := 8)
  decide +kernel

private theorem left0Middle3_eq_case_0_2_row_0_1_6 : (left0Middle3 0 2) ((0 : Fin 1), (1 : Fin 2), (6 : Fin 8)) = (HexagonAtoms302.assocABC) ((0 : Fin 1), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 1) (b := 2) (c := 8)
  decide +kernel

private theorem left0Middle3_eq_case_0_2_row_0_1_7 : (left0Middle3 0 2) ((0 : Fin 1), (1 : Fin 2), (7 : Fin 8)) = (HexagonAtoms302.assocABC) ((0 : Fin 1), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 1) (b := 2) (c := 8)
  decide +kernel

private theorem left0Middle3_eq_case_0_2_checked : left0Middle3 0 2 = HexagonAtoms302.assocABC := by
  funext r
  fin_cases r
  · exact left0Middle3_eq_case_0_2_row_0_0_0
  · exact left0Middle3_eq_case_0_2_row_0_0_1
  · exact left0Middle3_eq_case_0_2_row_0_0_2
  · exact left0Middle3_eq_case_0_2_row_0_0_3
  · exact left0Middle3_eq_case_0_2_row_0_0_4
  · exact left0Middle3_eq_case_0_2_row_0_0_5
  · exact left0Middle3_eq_case_0_2_row_0_0_6
  · exact left0Middle3_eq_case_0_2_row_0_0_7
  · exact left0Middle3_eq_case_0_2_row_0_1_0
  · exact left0Middle3_eq_case_0_2_row_0_1_1
  · exact left0Middle3_eq_case_0_2_row_0_1_2
  · exact left0Middle3_eq_case_0_2_row_0_1_3
  · exact left0Middle3_eq_case_0_2_row_0_1_4
  · exact left0Middle3_eq_case_0_2_row_0_1_5
  · exact left0Middle3_eq_case_0_2_row_0_1_6
  · exact left0Middle3_eq_case_0_2_row_0_1_7

set_option backward.isDefEq.respectTransparency false in
theorem left0Middle3_eq_case_0_2 : left0Middle3 0 2 = outerRightZ 3 0 2 * associatorZ 3 0 2 := by
  simpa only [HexagonAtoms302.assocABC_eq,
    HexagonAtoms302.outerABC_eq,
    HexagonAtoms302.assocBAC_eq,
    HexagonAtoms302.innerABC_eq,
    HexagonAtoms302.innerRightABC_eq,
    HexagonAtoms302.inverseACB_eq,
    HexagonAtoms302.innerACB_eq,
    HexagonAtoms302.assocBCA_eq,
    HexagonAtoms302.innerRightBAC_eq,
    HexagonAtoms302.assocCAB_eq,
    HexagonAtoms302.outerLeftABC_eq,
    HexagonRowColumn302.product0_eq,
    HexagonRowColumn302.product1_eq,
    HexagonRowColumn302.product2_eq,
    HexagonRowColumn302.product3_eq,
    HexagonRowColumn302.product4_eq,
    HexagonRowColumn302.product5_eq,
    HexagonRowColumn302.product6_eq,
    HexagonRowColumn302.product7_eq] using left0Middle3_eq_case_0_2_checked

private theorem left1Middle3_eq_case_0_2_row_0_0_0 : (left1Middle3 0 2) ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8)) = (HexagonAtoms302.assocBAC) ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 1) (b := 2) (c := 8)
  decide +kernel

private theorem left1Middle3_eq_case_0_2_row_0_0_1 : (left1Middle3 0 2) ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8)) = (HexagonAtoms302.assocBAC) ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 1) (b := 2) (c := 8)
  decide +kernel

private theorem left1Middle3_eq_case_0_2_row_0_0_2 : (left1Middle3 0 2) ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8)) = (HexagonAtoms302.assocBAC) ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 1) (b := 2) (c := 8)
  decide +kernel

private theorem left1Middle3_eq_case_0_2_row_0_0_3 : (left1Middle3 0 2) ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8)) = (HexagonAtoms302.assocBAC) ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 1) (b := 2) (c := 8)
  decide +kernel

private theorem left1Middle3_eq_case_0_2_row_0_0_4 : (left1Middle3 0 2) ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8)) = (HexagonAtoms302.assocBAC) ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 1) (b := 2) (c := 8)
  decide +kernel

private theorem left1Middle3_eq_case_0_2_row_0_0_5 : (left1Middle3 0 2) ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8)) = (HexagonAtoms302.assocBAC) ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 1) (b := 2) (c := 8)
  decide +kernel

private theorem left1Middle3_eq_case_0_2_row_0_0_6 : (left1Middle3 0 2) ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8)) = (HexagonAtoms302.assocBAC) ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 1) (b := 2) (c := 8)
  decide +kernel

private theorem left1Middle3_eq_case_0_2_row_0_0_7 : (left1Middle3 0 2) ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8)) = (HexagonAtoms302.assocBAC) ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 1) (b := 2) (c := 8)
  decide +kernel

private theorem left1Middle3_eq_case_0_2_row_1_0_0 : (left1Middle3 0 2) ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8)) = (HexagonAtoms302.assocBAC) ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 1) (b := 2) (c := 8)
  decide +kernel

private theorem left1Middle3_eq_case_0_2_row_1_0_1 : (left1Middle3 0 2) ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8)) = (HexagonAtoms302.assocBAC) ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 1) (b := 2) (c := 8)
  decide +kernel

private theorem left1Middle3_eq_case_0_2_row_1_0_2 : (left1Middle3 0 2) ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8)) = (HexagonAtoms302.assocBAC) ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 1) (b := 2) (c := 8)
  decide +kernel

private theorem left1Middle3_eq_case_0_2_row_1_0_3 : (left1Middle3 0 2) ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8)) = (HexagonAtoms302.assocBAC) ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 1) (b := 2) (c := 8)
  decide +kernel

private theorem left1Middle3_eq_case_0_2_row_1_0_4 : (left1Middle3 0 2) ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8)) = (HexagonAtoms302.assocBAC) ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 1) (b := 2) (c := 8)
  decide +kernel

private theorem left1Middle3_eq_case_0_2_row_1_0_5 : (left1Middle3 0 2) ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8)) = (HexagonAtoms302.assocBAC) ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 1) (b := 2) (c := 8)
  decide +kernel

private theorem left1Middle3_eq_case_0_2_row_1_0_6 : (left1Middle3 0 2) ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8)) = (HexagonAtoms302.assocBAC) ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 1) (b := 2) (c := 8)
  decide +kernel

private theorem left1Middle3_eq_case_0_2_row_1_0_7 : (left1Middle3 0 2) ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8)) = (HexagonAtoms302.assocBAC) ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 1) (b := 2) (c := 8)
  decide +kernel

private theorem left1Middle3_eq_case_0_2_checked : left1Middle3 0 2 = HexagonAtoms302.assocBAC := by
  funext r
  fin_cases r
  · exact left1Middle3_eq_case_0_2_row_0_0_0
  · exact left1Middle3_eq_case_0_2_row_0_0_1
  · exact left1Middle3_eq_case_0_2_row_0_0_2
  · exact left1Middle3_eq_case_0_2_row_0_0_3
  · exact left1Middle3_eq_case_0_2_row_0_0_4
  · exact left1Middle3_eq_case_0_2_row_0_0_5
  · exact left1Middle3_eq_case_0_2_row_0_0_6
  · exact left1Middle3_eq_case_0_2_row_0_0_7
  · exact left1Middle3_eq_case_0_2_row_1_0_0
  · exact left1Middle3_eq_case_0_2_row_1_0_1
  · exact left1Middle3_eq_case_0_2_row_1_0_2
  · exact left1Middle3_eq_case_0_2_row_1_0_3
  · exact left1Middle3_eq_case_0_2_row_1_0_4
  · exact left1Middle3_eq_case_0_2_row_1_0_5
  · exact left1Middle3_eq_case_0_2_row_1_0_6
  · exact left1Middle3_eq_case_0_2_row_1_0_7

set_option backward.isDefEq.respectTransparency false in
theorem left1Middle3_eq_case_0_2 : left1Middle3 0 2 = associatorZ 0 3 2 * innerLeftZ 3 0 2 := by
  simpa only [HexagonAtoms302.assocABC_eq,
    HexagonAtoms302.outerABC_eq,
    HexagonAtoms302.assocBAC_eq,
    HexagonAtoms302.innerABC_eq,
    HexagonAtoms302.innerRightABC_eq,
    HexagonAtoms302.inverseACB_eq,
    HexagonAtoms302.innerACB_eq,
    HexagonAtoms302.assocBCA_eq,
    HexagonAtoms302.innerRightBAC_eq,
    HexagonAtoms302.assocCAB_eq,
    HexagonAtoms302.outerLeftABC_eq,
    HexagonRowColumn302.product0_eq,
    HexagonRowColumn302.product1_eq,
    HexagonRowColumn302.product2_eq,
    HexagonRowColumn302.product3_eq,
    HexagonRowColumn302.product4_eq,
    HexagonRowColumn302.product5_eq,
    HexagonRowColumn302.product6_eq,
    HexagonRowColumn302.product7_eq] using left1Middle3_eq_case_0_2_checked

private theorem right0Middle3_eq_case_0_2_row_0_0_0 : (right0Middle3 0 2) ((0 : Fin 1), (0 : Fin 2), (0 : Fin 8)) = (HexagonAtoms302.assocABC) ((0 : Fin 1), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 1) (b := 2) (c := 8)
  decide +kernel

private theorem right0Middle3_eq_case_0_2_row_0_0_1 : (right0Middle3 0 2) ((0 : Fin 1), (0 : Fin 2), (1 : Fin 8)) = (HexagonAtoms302.assocABC) ((0 : Fin 1), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 1) (b := 2) (c := 8)
  decide +kernel

private theorem right0Middle3_eq_case_0_2_row_0_0_2 : (right0Middle3 0 2) ((0 : Fin 1), (0 : Fin 2), (2 : Fin 8)) = (HexagonAtoms302.assocABC) ((0 : Fin 1), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 1) (b := 2) (c := 8)
  decide +kernel

private theorem right0Middle3_eq_case_0_2_row_0_0_3 : (right0Middle3 0 2) ((0 : Fin 1), (0 : Fin 2), (3 : Fin 8)) = (HexagonAtoms302.assocABC) ((0 : Fin 1), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 1) (b := 2) (c := 8)
  decide +kernel

private theorem right0Middle3_eq_case_0_2_row_0_0_4 : (right0Middle3 0 2) ((0 : Fin 1), (0 : Fin 2), (4 : Fin 8)) = (HexagonAtoms302.assocABC) ((0 : Fin 1), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 1) (b := 2) (c := 8)
  decide +kernel

private theorem right0Middle3_eq_case_0_2_row_0_0_5 : (right0Middle3 0 2) ((0 : Fin 1), (0 : Fin 2), (5 : Fin 8)) = (HexagonAtoms302.assocABC) ((0 : Fin 1), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 1) (b := 2) (c := 8)
  decide +kernel

private theorem right0Middle3_eq_case_0_2_row_0_0_6 : (right0Middle3 0 2) ((0 : Fin 1), (0 : Fin 2), (6 : Fin 8)) = (HexagonAtoms302.assocABC) ((0 : Fin 1), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 1) (b := 2) (c := 8)
  decide +kernel

private theorem right0Middle3_eq_case_0_2_row_0_0_7 : (right0Middle3 0 2) ((0 : Fin 1), (0 : Fin 2), (7 : Fin 8)) = (HexagonAtoms302.assocABC) ((0 : Fin 1), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 1) (b := 2) (c := 8)
  decide +kernel

private theorem right0Middle3_eq_case_0_2_row_0_1_0 : (right0Middle3 0 2) ((0 : Fin 1), (1 : Fin 2), (0 : Fin 8)) = (HexagonAtoms302.assocABC) ((0 : Fin 1), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 1) (b := 2) (c := 8)
  decide +kernel

private theorem right0Middle3_eq_case_0_2_row_0_1_1 : (right0Middle3 0 2) ((0 : Fin 1), (1 : Fin 2), (1 : Fin 8)) = (HexagonAtoms302.assocABC) ((0 : Fin 1), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 1) (b := 2) (c := 8)
  decide +kernel

private theorem right0Middle3_eq_case_0_2_row_0_1_2 : (right0Middle3 0 2) ((0 : Fin 1), (1 : Fin 2), (2 : Fin 8)) = (HexagonAtoms302.assocABC) ((0 : Fin 1), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 1) (b := 2) (c := 8)
  decide +kernel

private theorem right0Middle3_eq_case_0_2_row_0_1_3 : (right0Middle3 0 2) ((0 : Fin 1), (1 : Fin 2), (3 : Fin 8)) = (HexagonAtoms302.assocABC) ((0 : Fin 1), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 1) (b := 2) (c := 8)
  decide +kernel

private theorem right0Middle3_eq_case_0_2_row_0_1_4 : (right0Middle3 0 2) ((0 : Fin 1), (1 : Fin 2), (4 : Fin 8)) = (HexagonAtoms302.assocABC) ((0 : Fin 1), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 1) (b := 2) (c := 8)
  decide +kernel

private theorem right0Middle3_eq_case_0_2_row_0_1_5 : (right0Middle3 0 2) ((0 : Fin 1), (1 : Fin 2), (5 : Fin 8)) = (HexagonAtoms302.assocABC) ((0 : Fin 1), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 1) (b := 2) (c := 8)
  decide +kernel

private theorem right0Middle3_eq_case_0_2_row_0_1_6 : (right0Middle3 0 2) ((0 : Fin 1), (1 : Fin 2), (6 : Fin 8)) = (HexagonAtoms302.assocABC) ((0 : Fin 1), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 1) (b := 2) (c := 8)
  decide +kernel

private theorem right0Middle3_eq_case_0_2_row_0_1_7 : (right0Middle3 0 2) ((0 : Fin 1), (1 : Fin 2), (7 : Fin 8)) = (HexagonAtoms302.assocABC) ((0 : Fin 1), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 1) (b := 2) (c := 8)
  decide +kernel

private theorem right0Middle3_eq_case_0_2_checked : right0Middle3 0 2 = HexagonAtoms302.assocABC := by
  funext r
  fin_cases r
  · exact right0Middle3_eq_case_0_2_row_0_0_0
  · exact right0Middle3_eq_case_0_2_row_0_0_1
  · exact right0Middle3_eq_case_0_2_row_0_0_2
  · exact right0Middle3_eq_case_0_2_row_0_0_3
  · exact right0Middle3_eq_case_0_2_row_0_0_4
  · exact right0Middle3_eq_case_0_2_row_0_0_5
  · exact right0Middle3_eq_case_0_2_row_0_0_6
  · exact right0Middle3_eq_case_0_2_row_0_0_7
  · exact right0Middle3_eq_case_0_2_row_0_1_0
  · exact right0Middle3_eq_case_0_2_row_0_1_1
  · exact right0Middle3_eq_case_0_2_row_0_1_2
  · exact right0Middle3_eq_case_0_2_row_0_1_3
  · exact right0Middle3_eq_case_0_2_row_0_1_4
  · exact right0Middle3_eq_case_0_2_row_0_1_5
  · exact right0Middle3_eq_case_0_2_row_0_1_6
  · exact right0Middle3_eq_case_0_2_row_0_1_7

set_option backward.isDefEq.respectTransparency false in
theorem right0Middle3_eq_case_0_2 : right0Middle3 0 2 = innerRightZ 3 0 2 * associatorZ 3 0 2 := by
  simpa only [HexagonAtoms302.assocABC_eq,
    HexagonAtoms302.outerABC_eq,
    HexagonAtoms302.assocBAC_eq,
    HexagonAtoms302.innerABC_eq,
    HexagonAtoms302.innerRightABC_eq,
    HexagonAtoms302.inverseACB_eq,
    HexagonAtoms302.innerACB_eq,
    HexagonAtoms302.assocBCA_eq,
    HexagonAtoms302.innerRightBAC_eq,
    HexagonAtoms302.assocCAB_eq,
    HexagonAtoms302.outerLeftABC_eq,
    HexagonRowColumn302.product0_eq,
    HexagonRowColumn302.product1_eq,
    HexagonRowColumn302.product2_eq,
    HexagonRowColumn302.product3_eq,
    HexagonRowColumn302.product4_eq,
    HexagonRowColumn302.product5_eq,
    HexagonRowColumn302.product6_eq,
    HexagonRowColumn302.product7_eq] using right0Middle3_eq_case_0_2_checked

private theorem right1Middle3_eq_case_0_2_row_0_0_0 : (right1Middle3 0 2) ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8)) = (rowColumnMul HexagonRowColumn302.rows_inverseACB HexagonRowColumn302.cols_right0) ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 1) (b := 2) (c := 8)
  decide +kernel

private theorem right1Middle3_eq_case_0_2_row_0_0_1 : (right1Middle3 0 2) ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8)) = (rowColumnMul HexagonRowColumn302.rows_inverseACB HexagonRowColumn302.cols_right0) ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 1) (b := 2) (c := 8)
  decide +kernel

private theorem right1Middle3_eq_case_0_2_row_0_0_2 : (right1Middle3 0 2) ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8)) = (rowColumnMul HexagonRowColumn302.rows_inverseACB HexagonRowColumn302.cols_right0) ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 1) (b := 2) (c := 8)
  decide +kernel

private theorem right1Middle3_eq_case_0_2_row_0_0_3 : (right1Middle3 0 2) ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8)) = (rowColumnMul HexagonRowColumn302.rows_inverseACB HexagonRowColumn302.cols_right0) ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 1) (b := 2) (c := 8)
  decide +kernel

private theorem right1Middle3_eq_case_0_2_row_0_0_4 : (right1Middle3 0 2) ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8)) = (rowColumnMul HexagonRowColumn302.rows_inverseACB HexagonRowColumn302.cols_right0) ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 1) (b := 2) (c := 8)
  decide +kernel

private theorem right1Middle3_eq_case_0_2_row_0_0_5 : (right1Middle3 0 2) ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8)) = (rowColumnMul HexagonRowColumn302.rows_inverseACB HexagonRowColumn302.cols_right0) ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 1) (b := 2) (c := 8)
  decide +kernel

private theorem right1Middle3_eq_case_0_2_row_0_0_6 : (right1Middle3 0 2) ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8)) = (rowColumnMul HexagonRowColumn302.rows_inverseACB HexagonRowColumn302.cols_right0) ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 1) (b := 2) (c := 8)
  decide +kernel

private theorem right1Middle3_eq_case_0_2_row_0_0_7 : (right1Middle3 0 2) ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8)) = (rowColumnMul HexagonRowColumn302.rows_inverseACB HexagonRowColumn302.cols_right0) ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 1) (b := 2) (c := 8)
  decide +kernel

private theorem right1Middle3_eq_case_0_2_row_1_0_0 : (right1Middle3 0 2) ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8)) = (rowColumnMul HexagonRowColumn302.rows_inverseACB HexagonRowColumn302.cols_right0) ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 1) (b := 2) (c := 8)
  decide +kernel

private theorem right1Middle3_eq_case_0_2_row_1_0_1 : (right1Middle3 0 2) ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8)) = (rowColumnMul HexagonRowColumn302.rows_inverseACB HexagonRowColumn302.cols_right0) ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 1) (b := 2) (c := 8)
  decide +kernel

private theorem right1Middle3_eq_case_0_2_row_1_0_2 : (right1Middle3 0 2) ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8)) = (rowColumnMul HexagonRowColumn302.rows_inverseACB HexagonRowColumn302.cols_right0) ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 1) (b := 2) (c := 8)
  decide +kernel

private theorem right1Middle3_eq_case_0_2_row_1_0_3 : (right1Middle3 0 2) ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8)) = (rowColumnMul HexagonRowColumn302.rows_inverseACB HexagonRowColumn302.cols_right0) ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 1) (b := 2) (c := 8)
  decide +kernel

private theorem right1Middle3_eq_case_0_2_row_1_0_4 : (right1Middle3 0 2) ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8)) = (rowColumnMul HexagonRowColumn302.rows_inverseACB HexagonRowColumn302.cols_right0) ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 1) (b := 2) (c := 8)
  decide +kernel

private theorem right1Middle3_eq_case_0_2_row_1_0_5 : (right1Middle3 0 2) ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8)) = (rowColumnMul HexagonRowColumn302.rows_inverseACB HexagonRowColumn302.cols_right0) ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 1) (b := 2) (c := 8)
  decide +kernel

private theorem right1Middle3_eq_case_0_2_row_1_0_6 : (right1Middle3 0 2) ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8)) = (rowColumnMul HexagonRowColumn302.rows_inverseACB HexagonRowColumn302.cols_right0) ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 1) (b := 2) (c := 8)
  decide +kernel

private theorem right1Middle3_eq_case_0_2_row_1_0_7 : (right1Middle3 0 2) ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8)) = (rowColumnMul HexagonRowColumn302.rows_inverseACB HexagonRowColumn302.cols_right0) ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 1) (b := 2) (c := 8)
  decide +kernel

private theorem right1Middle3_eq_case_0_2_checked : right1Middle3 0 2 = rowColumnMul HexagonRowColumn302.rows_inverseACB HexagonRowColumn302.cols_right0 := by
  funext r
  fin_cases r
  · exact right1Middle3_eq_case_0_2_row_0_0_0
  · exact right1Middle3_eq_case_0_2_row_0_0_1
  · exact right1Middle3_eq_case_0_2_row_0_0_2
  · exact right1Middle3_eq_case_0_2_row_0_0_3
  · exact right1Middle3_eq_case_0_2_row_0_0_4
  · exact right1Middle3_eq_case_0_2_row_0_0_5
  · exact right1Middle3_eq_case_0_2_row_0_0_6
  · exact right1Middle3_eq_case_0_2_row_0_0_7
  · exact right1Middle3_eq_case_0_2_row_1_0_0
  · exact right1Middle3_eq_case_0_2_row_1_0_1
  · exact right1Middle3_eq_case_0_2_row_1_0_2
  · exact right1Middle3_eq_case_0_2_row_1_0_3
  · exact right1Middle3_eq_case_0_2_row_1_0_4
  · exact right1Middle3_eq_case_0_2_row_1_0_5
  · exact right1Middle3_eq_case_0_2_row_1_0_6
  · exact right1Middle3_eq_case_0_2_row_1_0_7

set_option backward.isDefEq.respectTransparency false in
theorem right1Middle3_eq_case_0_2 : right1Middle3 0 2 = associatorInverseZ 3 2 0 * right0Middle3 0 2 := by
  simpa only [HexagonAtoms302.assocABC_eq,
    HexagonAtoms302.outerABC_eq,
    HexagonAtoms302.assocBAC_eq,
    HexagonAtoms302.innerABC_eq,
    HexagonAtoms302.innerRightABC_eq,
    HexagonAtoms302.inverseACB_eq,
    HexagonAtoms302.innerACB_eq,
    HexagonAtoms302.assocBCA_eq,
    HexagonAtoms302.innerRightBAC_eq,
    HexagonAtoms302.assocCAB_eq,
    HexagonAtoms302.outerLeftABC_eq,
    HexagonRowColumn302.product0_eq,
    HexagonRowColumn302.product1_eq,
    HexagonRowColumn302.product2_eq,
    HexagonRowColumn302.product3_eq,
    HexagonRowColumn302.product4_eq,
    HexagonRowColumn302.product5_eq,
    HexagonRowColumn302.product6_eq,
    HexagonRowColumn302.product7_eq] using right1Middle3_eq_case_0_2_checked

private theorem right2Middle3_eq_case_0_2_row_0_0_0 : (right2Middle3 0 2) ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8)) = (right1Middle3 0 2) ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 1) (b := 2) (c := 8)
  decide +kernel

private theorem right2Middle3_eq_case_0_2_row_0_0_1 : (right2Middle3 0 2) ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8)) = (right1Middle3 0 2) ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 1) (b := 2) (c := 8)
  decide +kernel

private theorem right2Middle3_eq_case_0_2_row_0_0_2 : (right2Middle3 0 2) ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8)) = (right1Middle3 0 2) ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 1) (b := 2) (c := 8)
  decide +kernel

private theorem right2Middle3_eq_case_0_2_row_0_0_3 : (right2Middle3 0 2) ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8)) = (right1Middle3 0 2) ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 1) (b := 2) (c := 8)
  decide +kernel

private theorem right2Middle3_eq_case_0_2_row_0_0_4 : (right2Middle3 0 2) ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8)) = (right1Middle3 0 2) ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 1) (b := 2) (c := 8)
  decide +kernel

private theorem right2Middle3_eq_case_0_2_row_0_0_5 : (right2Middle3 0 2) ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8)) = (right1Middle3 0 2) ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 1) (b := 2) (c := 8)
  decide +kernel

private theorem right2Middle3_eq_case_0_2_row_0_0_6 : (right2Middle3 0 2) ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8)) = (right1Middle3 0 2) ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 1) (b := 2) (c := 8)
  decide +kernel

private theorem right2Middle3_eq_case_0_2_row_0_0_7 : (right2Middle3 0 2) ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8)) = (right1Middle3 0 2) ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 1) (b := 2) (c := 8)
  decide +kernel

private theorem right2Middle3_eq_case_0_2_row_1_0_0 : (right2Middle3 0 2) ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8)) = (right1Middle3 0 2) ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 1) (b := 2) (c := 8)
  decide +kernel

private theorem right2Middle3_eq_case_0_2_row_1_0_1 : (right2Middle3 0 2) ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8)) = (right1Middle3 0 2) ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 1) (b := 2) (c := 8)
  decide +kernel

private theorem right2Middle3_eq_case_0_2_row_1_0_2 : (right2Middle3 0 2) ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8)) = (right1Middle3 0 2) ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 1) (b := 2) (c := 8)
  decide +kernel

private theorem right2Middle3_eq_case_0_2_row_1_0_3 : (right2Middle3 0 2) ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8)) = (right1Middle3 0 2) ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 1) (b := 2) (c := 8)
  decide +kernel

private theorem right2Middle3_eq_case_0_2_row_1_0_4 : (right2Middle3 0 2) ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8)) = (right1Middle3 0 2) ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 1) (b := 2) (c := 8)
  decide +kernel

private theorem right2Middle3_eq_case_0_2_row_1_0_5 : (right2Middle3 0 2) ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8)) = (right1Middle3 0 2) ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 1) (b := 2) (c := 8)
  decide +kernel

private theorem right2Middle3_eq_case_0_2_row_1_0_6 : (right2Middle3 0 2) ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8)) = (right1Middle3 0 2) ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 1) (b := 2) (c := 8)
  decide +kernel

private theorem right2Middle3_eq_case_0_2_row_1_0_7 : (right2Middle3 0 2) ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8)) = (right1Middle3 0 2) ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 1) (b := 2) (c := 8)
  decide +kernel

private theorem right2Middle3_eq_case_0_2_checked : right2Middle3 0 2 = right1Middle3 0 2 := by
  funext r
  fin_cases r
  · exact right2Middle3_eq_case_0_2_row_0_0_0
  · exact right2Middle3_eq_case_0_2_row_0_0_1
  · exact right2Middle3_eq_case_0_2_row_0_0_2
  · exact right2Middle3_eq_case_0_2_row_0_0_3
  · exact right2Middle3_eq_case_0_2_row_0_0_4
  · exact right2Middle3_eq_case_0_2_row_0_0_5
  · exact right2Middle3_eq_case_0_2_row_0_0_6
  · exact right2Middle3_eq_case_0_2_row_0_0_7
  · exact right2Middle3_eq_case_0_2_row_1_0_0
  · exact right2Middle3_eq_case_0_2_row_1_0_1
  · exact right2Middle3_eq_case_0_2_row_1_0_2
  · exact right2Middle3_eq_case_0_2_row_1_0_3
  · exact right2Middle3_eq_case_0_2_row_1_0_4
  · exact right2Middle3_eq_case_0_2_row_1_0_5
  · exact right2Middle3_eq_case_0_2_row_1_0_6
  · exact right2Middle3_eq_case_0_2_row_1_0_7

set_option backward.isDefEq.respectTransparency false in
theorem right2Middle3_eq_case_0_2 : right2Middle3 0 2 = innerLeftZ 3 2 0 * right1Middle3 0 2 := by
  simpa only [HexagonAtoms302.assocABC_eq,
    HexagonAtoms302.outerABC_eq,
    HexagonAtoms302.assocBAC_eq,
    HexagonAtoms302.innerABC_eq,
    HexagonAtoms302.innerRightABC_eq,
    HexagonAtoms302.inverseACB_eq,
    HexagonAtoms302.innerACB_eq,
    HexagonAtoms302.assocBCA_eq,
    HexagonAtoms302.innerRightBAC_eq,
    HexagonAtoms302.assocCAB_eq,
    HexagonAtoms302.outerLeftABC_eq,
    HexagonRowColumn302.product0_eq,
    HexagonRowColumn302.product1_eq,
    HexagonRowColumn302.product2_eq,
    HexagonRowColumn302.product3_eq,
    HexagonRowColumn302.product4_eq,
    HexagonRowColumn302.product5_eq,
    HexagonRowColumn302.product6_eq,
    HexagonRowColumn302.product7_eq] using right2Middle3_eq_case_0_2_checked

private theorem leftFinal3_case_0_2_row_0_0_0 : (((-1 : ℤ) ^ (leftScaleBit 3 0 2).val * positiveScale (leftScaleExponent 3 0 2)) •
      (rowColumnMul HexagonRowColumn302.rows_assocBCA HexagonRowColumn302.cols_left0)) ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8)) = (negativeScale (leftScaleExponent 3 0 2) • (left1Middle3 0 2)) ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 1) (b := 2) (c := 8)
  decide +kernel

private theorem leftFinal3_case_0_2_row_0_0_1 : (((-1 : ℤ) ^ (leftScaleBit 3 0 2).val * positiveScale (leftScaleExponent 3 0 2)) •
      (rowColumnMul HexagonRowColumn302.rows_assocBCA HexagonRowColumn302.cols_left0)) ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8)) = (negativeScale (leftScaleExponent 3 0 2) • (left1Middle3 0 2)) ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 1) (b := 2) (c := 8)
  decide +kernel

private theorem leftFinal3_case_0_2_row_0_0_2 : (((-1 : ℤ) ^ (leftScaleBit 3 0 2).val * positiveScale (leftScaleExponent 3 0 2)) •
      (rowColumnMul HexagonRowColumn302.rows_assocBCA HexagonRowColumn302.cols_left0)) ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8)) = (negativeScale (leftScaleExponent 3 0 2) • (left1Middle3 0 2)) ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 1) (b := 2) (c := 8)
  decide +kernel

private theorem leftFinal3_case_0_2_row_0_0_3 : (((-1 : ℤ) ^ (leftScaleBit 3 0 2).val * positiveScale (leftScaleExponent 3 0 2)) •
      (rowColumnMul HexagonRowColumn302.rows_assocBCA HexagonRowColumn302.cols_left0)) ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8)) = (negativeScale (leftScaleExponent 3 0 2) • (left1Middle3 0 2)) ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 1) (b := 2) (c := 8)
  decide +kernel

private theorem leftFinal3_case_0_2_row_0_0_4 : (((-1 : ℤ) ^ (leftScaleBit 3 0 2).val * positiveScale (leftScaleExponent 3 0 2)) •
      (rowColumnMul HexagonRowColumn302.rows_assocBCA HexagonRowColumn302.cols_left0)) ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8)) = (negativeScale (leftScaleExponent 3 0 2) • (left1Middle3 0 2)) ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 1) (b := 2) (c := 8)
  decide +kernel

private theorem leftFinal3_case_0_2_row_0_0_5 : (((-1 : ℤ) ^ (leftScaleBit 3 0 2).val * positiveScale (leftScaleExponent 3 0 2)) •
      (rowColumnMul HexagonRowColumn302.rows_assocBCA HexagonRowColumn302.cols_left0)) ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8)) = (negativeScale (leftScaleExponent 3 0 2) • (left1Middle3 0 2)) ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 1) (b := 2) (c := 8)
  decide +kernel

private theorem leftFinal3_case_0_2_row_0_0_6 : (((-1 : ℤ) ^ (leftScaleBit 3 0 2).val * positiveScale (leftScaleExponent 3 0 2)) •
      (rowColumnMul HexagonRowColumn302.rows_assocBCA HexagonRowColumn302.cols_left0)) ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8)) = (negativeScale (leftScaleExponent 3 0 2) • (left1Middle3 0 2)) ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 1) (b := 2) (c := 8)
  decide +kernel

private theorem leftFinal3_case_0_2_row_0_0_7 : (((-1 : ℤ) ^ (leftScaleBit 3 0 2).val * positiveScale (leftScaleExponent 3 0 2)) •
      (rowColumnMul HexagonRowColumn302.rows_assocBCA HexagonRowColumn302.cols_left0)) ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8)) = (negativeScale (leftScaleExponent 3 0 2) • (left1Middle3 0 2)) ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 1) (b := 2) (c := 8)
  decide +kernel

private theorem leftFinal3_case_0_2_row_1_0_0 : (((-1 : ℤ) ^ (leftScaleBit 3 0 2).val * positiveScale (leftScaleExponent 3 0 2)) •
      (rowColumnMul HexagonRowColumn302.rows_assocBCA HexagonRowColumn302.cols_left0)) ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8)) = (negativeScale (leftScaleExponent 3 0 2) • (left1Middle3 0 2)) ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 1) (b := 2) (c := 8)
  decide +kernel

private theorem leftFinal3_case_0_2_row_1_0_1 : (((-1 : ℤ) ^ (leftScaleBit 3 0 2).val * positiveScale (leftScaleExponent 3 0 2)) •
      (rowColumnMul HexagonRowColumn302.rows_assocBCA HexagonRowColumn302.cols_left0)) ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8)) = (negativeScale (leftScaleExponent 3 0 2) • (left1Middle3 0 2)) ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 1) (b := 2) (c := 8)
  decide +kernel

private theorem leftFinal3_case_0_2_row_1_0_2 : (((-1 : ℤ) ^ (leftScaleBit 3 0 2).val * positiveScale (leftScaleExponent 3 0 2)) •
      (rowColumnMul HexagonRowColumn302.rows_assocBCA HexagonRowColumn302.cols_left0)) ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8)) = (negativeScale (leftScaleExponent 3 0 2) • (left1Middle3 0 2)) ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 1) (b := 2) (c := 8)
  decide +kernel

private theorem leftFinal3_case_0_2_row_1_0_3 : (((-1 : ℤ) ^ (leftScaleBit 3 0 2).val * positiveScale (leftScaleExponent 3 0 2)) •
      (rowColumnMul HexagonRowColumn302.rows_assocBCA HexagonRowColumn302.cols_left0)) ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8)) = (negativeScale (leftScaleExponent 3 0 2) • (left1Middle3 0 2)) ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 1) (b := 2) (c := 8)
  decide +kernel

private theorem leftFinal3_case_0_2_row_1_0_4 : (((-1 : ℤ) ^ (leftScaleBit 3 0 2).val * positiveScale (leftScaleExponent 3 0 2)) •
      (rowColumnMul HexagonRowColumn302.rows_assocBCA HexagonRowColumn302.cols_left0)) ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8)) = (negativeScale (leftScaleExponent 3 0 2) • (left1Middle3 0 2)) ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 1) (b := 2) (c := 8)
  decide +kernel

private theorem leftFinal3_case_0_2_row_1_0_5 : (((-1 : ℤ) ^ (leftScaleBit 3 0 2).val * positiveScale (leftScaleExponent 3 0 2)) •
      (rowColumnMul HexagonRowColumn302.rows_assocBCA HexagonRowColumn302.cols_left0)) ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8)) = (negativeScale (leftScaleExponent 3 0 2) • (left1Middle3 0 2)) ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 1) (b := 2) (c := 8)
  decide +kernel

private theorem leftFinal3_case_0_2_row_1_0_6 : (((-1 : ℤ) ^ (leftScaleBit 3 0 2).val * positiveScale (leftScaleExponent 3 0 2)) •
      (rowColumnMul HexagonRowColumn302.rows_assocBCA HexagonRowColumn302.cols_left0)) ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8)) = (negativeScale (leftScaleExponent 3 0 2) • (left1Middle3 0 2)) ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 1) (b := 2) (c := 8)
  decide +kernel

private theorem leftFinal3_case_0_2_row_1_0_7 : (((-1 : ℤ) ^ (leftScaleBit 3 0 2).val * positiveScale (leftScaleExponent 3 0 2)) •
      (rowColumnMul HexagonRowColumn302.rows_assocBCA HexagonRowColumn302.cols_left0)) ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8)) = (negativeScale (leftScaleExponent 3 0 2) • (left1Middle3 0 2)) ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 1) (b := 2) (c := 8)
  decide +kernel

private theorem leftFinal3_case_0_2_checked : ((-1 : ℤ) ^ (leftScaleBit 3 0 2).val * positiveScale (leftScaleExponent 3 0 2)) •
      (rowColumnMul HexagonRowColumn302.rows_assocBCA HexagonRowColumn302.cols_left0) = negativeScale (leftScaleExponent 3 0 2) • (left1Middle3 0 2) := by
  funext r
  fin_cases r
  · exact leftFinal3_case_0_2_row_0_0_0
  · exact leftFinal3_case_0_2_row_0_0_1
  · exact leftFinal3_case_0_2_row_0_0_2
  · exact leftFinal3_case_0_2_row_0_0_3
  · exact leftFinal3_case_0_2_row_0_0_4
  · exact leftFinal3_case_0_2_row_0_0_5
  · exact leftFinal3_case_0_2_row_0_0_6
  · exact leftFinal3_case_0_2_row_0_0_7
  · exact leftFinal3_case_0_2_row_1_0_0
  · exact leftFinal3_case_0_2_row_1_0_1
  · exact leftFinal3_case_0_2_row_1_0_2
  · exact leftFinal3_case_0_2_row_1_0_3
  · exact leftFinal3_case_0_2_row_1_0_4
  · exact leftFinal3_case_0_2_row_1_0_5
  · exact leftFinal3_case_0_2_row_1_0_6
  · exact leftFinal3_case_0_2_row_1_0_7

set_option backward.isDefEq.respectTransparency false in
theorem leftFinal3_case_0_2 : ((-1 : ℤ) ^ (leftScaleBit 3 0 2).val * positiveScale (leftScaleExponent 3 0 2)) •
      (associatorZ 0 2 3 * left0Middle3 0 2) = negativeScale (leftScaleExponent 3 0 2) • (innerRightZ 0 3 2 * left1Middle3 0 2) := by
  simpa only [HexagonAtoms302.assocABC_eq,
    HexagonAtoms302.outerABC_eq,
    HexagonAtoms302.assocBAC_eq,
    HexagonAtoms302.innerABC_eq,
    HexagonAtoms302.innerRightABC_eq,
    HexagonAtoms302.inverseACB_eq,
    HexagonAtoms302.innerACB_eq,
    HexagonAtoms302.assocBCA_eq,
    HexagonAtoms302.innerRightBAC_eq,
    HexagonAtoms302.assocCAB_eq,
    HexagonAtoms302.outerLeftABC_eq,
    HexagonRowColumn302.product0_eq,
    HexagonRowColumn302.product1_eq,
    HexagonRowColumn302.product2_eq,
    HexagonRowColumn302.product3_eq,
    HexagonRowColumn302.product4_eq,
    HexagonRowColumn302.product5_eq,
    HexagonRowColumn302.product6_eq,
    HexagonRowColumn302.product7_eq] using leftFinal3_case_0_2_checked

private theorem rightFinal3_case_0_2_row_0_0_0 : (((-1 : ℤ) ^ (rightScaleBit 3 0 2).val * positiveScale (rightScaleExponent 3 0 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 0 : ℤ)) • HexagonAtoms302.outerLeftABC) ((0 : Fin 1), (0 : Fin 2), (0 : Fin 8)) = (negativeScale (rightScaleExponent 3 0 2) • (rowColumnMul HexagonRowColumn302.rows_assocCAB HexagonRowColumn302.cols_right2)) ((0 : Fin 1), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 1) (b := 2) (c := 8)
  decide +kernel

private theorem rightFinal3_case_0_2_row_0_0_1 : (((-1 : ℤ) ^ (rightScaleBit 3 0 2).val * positiveScale (rightScaleExponent 3 0 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 0 : ℤ)) • HexagonAtoms302.outerLeftABC) ((0 : Fin 1), (0 : Fin 2), (1 : Fin 8)) = (negativeScale (rightScaleExponent 3 0 2) • (rowColumnMul HexagonRowColumn302.rows_assocCAB HexagonRowColumn302.cols_right2)) ((0 : Fin 1), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 1) (b := 2) (c := 8)
  decide +kernel

private theorem rightFinal3_case_0_2_row_0_0_2 : (((-1 : ℤ) ^ (rightScaleBit 3 0 2).val * positiveScale (rightScaleExponent 3 0 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 0 : ℤ)) • HexagonAtoms302.outerLeftABC) ((0 : Fin 1), (0 : Fin 2), (2 : Fin 8)) = (negativeScale (rightScaleExponent 3 0 2) • (rowColumnMul HexagonRowColumn302.rows_assocCAB HexagonRowColumn302.cols_right2)) ((0 : Fin 1), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 1) (b := 2) (c := 8)
  decide +kernel

private theorem rightFinal3_case_0_2_row_0_0_3 : (((-1 : ℤ) ^ (rightScaleBit 3 0 2).val * positiveScale (rightScaleExponent 3 0 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 0 : ℤ)) • HexagonAtoms302.outerLeftABC) ((0 : Fin 1), (0 : Fin 2), (3 : Fin 8)) = (negativeScale (rightScaleExponent 3 0 2) • (rowColumnMul HexagonRowColumn302.rows_assocCAB HexagonRowColumn302.cols_right2)) ((0 : Fin 1), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 1) (b := 2) (c := 8)
  decide +kernel

private theorem rightFinal3_case_0_2_row_0_0_4 : (((-1 : ℤ) ^ (rightScaleBit 3 0 2).val * positiveScale (rightScaleExponent 3 0 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 0 : ℤ)) • HexagonAtoms302.outerLeftABC) ((0 : Fin 1), (0 : Fin 2), (4 : Fin 8)) = (negativeScale (rightScaleExponent 3 0 2) • (rowColumnMul HexagonRowColumn302.rows_assocCAB HexagonRowColumn302.cols_right2)) ((0 : Fin 1), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 1) (b := 2) (c := 8)
  decide +kernel

private theorem rightFinal3_case_0_2_row_0_0_5 : (((-1 : ℤ) ^ (rightScaleBit 3 0 2).val * positiveScale (rightScaleExponent 3 0 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 0 : ℤ)) • HexagonAtoms302.outerLeftABC) ((0 : Fin 1), (0 : Fin 2), (5 : Fin 8)) = (negativeScale (rightScaleExponent 3 0 2) • (rowColumnMul HexagonRowColumn302.rows_assocCAB HexagonRowColumn302.cols_right2)) ((0 : Fin 1), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 1) (b := 2) (c := 8)
  decide +kernel

private theorem rightFinal3_case_0_2_row_0_0_6 : (((-1 : ℤ) ^ (rightScaleBit 3 0 2).val * positiveScale (rightScaleExponent 3 0 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 0 : ℤ)) • HexagonAtoms302.outerLeftABC) ((0 : Fin 1), (0 : Fin 2), (6 : Fin 8)) = (negativeScale (rightScaleExponent 3 0 2) • (rowColumnMul HexagonRowColumn302.rows_assocCAB HexagonRowColumn302.cols_right2)) ((0 : Fin 1), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 1) (b := 2) (c := 8)
  decide +kernel

private theorem rightFinal3_case_0_2_row_0_0_7 : (((-1 : ℤ) ^ (rightScaleBit 3 0 2).val * positiveScale (rightScaleExponent 3 0 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 0 : ℤ)) • HexagonAtoms302.outerLeftABC) ((0 : Fin 1), (0 : Fin 2), (7 : Fin 8)) = (negativeScale (rightScaleExponent 3 0 2) • (rowColumnMul HexagonRowColumn302.rows_assocCAB HexagonRowColumn302.cols_right2)) ((0 : Fin 1), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 1) (b := 2) (c := 8)
  decide +kernel

private theorem rightFinal3_case_0_2_row_0_1_0 : (((-1 : ℤ) ^ (rightScaleBit 3 0 2).val * positiveScale (rightScaleExponent 3 0 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 0 : ℤ)) • HexagonAtoms302.outerLeftABC) ((0 : Fin 1), (1 : Fin 2), (0 : Fin 8)) = (negativeScale (rightScaleExponent 3 0 2) • (rowColumnMul HexagonRowColumn302.rows_assocCAB HexagonRowColumn302.cols_right2)) ((0 : Fin 1), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 1) (b := 2) (c := 8)
  decide +kernel

private theorem rightFinal3_case_0_2_row_0_1_1 : (((-1 : ℤ) ^ (rightScaleBit 3 0 2).val * positiveScale (rightScaleExponent 3 0 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 0 : ℤ)) • HexagonAtoms302.outerLeftABC) ((0 : Fin 1), (1 : Fin 2), (1 : Fin 8)) = (negativeScale (rightScaleExponent 3 0 2) • (rowColumnMul HexagonRowColumn302.rows_assocCAB HexagonRowColumn302.cols_right2)) ((0 : Fin 1), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 1) (b := 2) (c := 8)
  decide +kernel

private theorem rightFinal3_case_0_2_row_0_1_2 : (((-1 : ℤ) ^ (rightScaleBit 3 0 2).val * positiveScale (rightScaleExponent 3 0 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 0 : ℤ)) • HexagonAtoms302.outerLeftABC) ((0 : Fin 1), (1 : Fin 2), (2 : Fin 8)) = (negativeScale (rightScaleExponent 3 0 2) • (rowColumnMul HexagonRowColumn302.rows_assocCAB HexagonRowColumn302.cols_right2)) ((0 : Fin 1), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 1) (b := 2) (c := 8)
  decide +kernel

private theorem rightFinal3_case_0_2_row_0_1_3 : (((-1 : ℤ) ^ (rightScaleBit 3 0 2).val * positiveScale (rightScaleExponent 3 0 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 0 : ℤ)) • HexagonAtoms302.outerLeftABC) ((0 : Fin 1), (1 : Fin 2), (3 : Fin 8)) = (negativeScale (rightScaleExponent 3 0 2) • (rowColumnMul HexagonRowColumn302.rows_assocCAB HexagonRowColumn302.cols_right2)) ((0 : Fin 1), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 1) (b := 2) (c := 8)
  decide +kernel

private theorem rightFinal3_case_0_2_row_0_1_4 : (((-1 : ℤ) ^ (rightScaleBit 3 0 2).val * positiveScale (rightScaleExponent 3 0 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 0 : ℤ)) • HexagonAtoms302.outerLeftABC) ((0 : Fin 1), (1 : Fin 2), (4 : Fin 8)) = (negativeScale (rightScaleExponent 3 0 2) • (rowColumnMul HexagonRowColumn302.rows_assocCAB HexagonRowColumn302.cols_right2)) ((0 : Fin 1), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 1) (b := 2) (c := 8)
  decide +kernel

private theorem rightFinal3_case_0_2_row_0_1_5 : (((-1 : ℤ) ^ (rightScaleBit 3 0 2).val * positiveScale (rightScaleExponent 3 0 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 0 : ℤ)) • HexagonAtoms302.outerLeftABC) ((0 : Fin 1), (1 : Fin 2), (5 : Fin 8)) = (negativeScale (rightScaleExponent 3 0 2) • (rowColumnMul HexagonRowColumn302.rows_assocCAB HexagonRowColumn302.cols_right2)) ((0 : Fin 1), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 1) (b := 2) (c := 8)
  decide +kernel

private theorem rightFinal3_case_0_2_row_0_1_6 : (((-1 : ℤ) ^ (rightScaleBit 3 0 2).val * positiveScale (rightScaleExponent 3 0 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 0 : ℤ)) • HexagonAtoms302.outerLeftABC) ((0 : Fin 1), (1 : Fin 2), (6 : Fin 8)) = (negativeScale (rightScaleExponent 3 0 2) • (rowColumnMul HexagonRowColumn302.rows_assocCAB HexagonRowColumn302.cols_right2)) ((0 : Fin 1), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 1) (b := 2) (c := 8)
  decide +kernel

private theorem rightFinal3_case_0_2_row_0_1_7 : (((-1 : ℤ) ^ (rightScaleBit 3 0 2).val * positiveScale (rightScaleExponent 3 0 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 0 : ℤ)) • HexagonAtoms302.outerLeftABC) ((0 : Fin 1), (1 : Fin 2), (7 : Fin 8)) = (negativeScale (rightScaleExponent 3 0 2) • (rowColumnMul HexagonRowColumn302.rows_assocCAB HexagonRowColumn302.cols_right2)) ((0 : Fin 1), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound (a := 1) (b := 2) (c := 8)
  decide +kernel

private theorem rightFinal3_case_0_2_checked : ((-1 : ℤ) ^ (rightScaleBit 3 0 2).val * positiveScale (rightScaleExponent 3 0 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 0 : ℤ)) • HexagonAtoms302.outerLeftABC = negativeScale (rightScaleExponent 3 0 2) • (rowColumnMul HexagonRowColumn302.rows_assocCAB HexagonRowColumn302.cols_right2) := by
  funext r
  fin_cases r
  · exact rightFinal3_case_0_2_row_0_0_0
  · exact rightFinal3_case_0_2_row_0_0_1
  · exact rightFinal3_case_0_2_row_0_0_2
  · exact rightFinal3_case_0_2_row_0_0_3
  · exact rightFinal3_case_0_2_row_0_0_4
  · exact rightFinal3_case_0_2_row_0_0_5
  · exact rightFinal3_case_0_2_row_0_0_6
  · exact rightFinal3_case_0_2_row_0_0_7
  · exact rightFinal3_case_0_2_row_0_1_0
  · exact rightFinal3_case_0_2_row_0_1_1
  · exact rightFinal3_case_0_2_row_0_1_2
  · exact rightFinal3_case_0_2_row_0_1_3
  · exact rightFinal3_case_0_2_row_0_1_4
  · exact rightFinal3_case_0_2_row_0_1_5
  · exact rightFinal3_case_0_2_row_0_1_6
  · exact rightFinal3_case_0_2_row_0_1_7

set_option backward.isDefEq.respectTransparency false in
theorem rightFinal3_case_0_2 : ((-1 : ℤ) ^ (rightScaleBit 3 0 2).val * positiveScale (rightScaleExponent 3 0 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 0 : ℤ)) • outerLeftZ 3 0 2 = negativeScale (rightScaleExponent 3 0 2) • (associatorZ 2 3 0 * right2Middle3 0 2) := by
  simpa only [HexagonAtoms302.assocABC_eq,
    HexagonAtoms302.outerABC_eq,
    HexagonAtoms302.assocBAC_eq,
    HexagonAtoms302.innerABC_eq,
    HexagonAtoms302.innerRightABC_eq,
    HexagonAtoms302.inverseACB_eq,
    HexagonAtoms302.innerACB_eq,
    HexagonAtoms302.assocBCA_eq,
    HexagonAtoms302.innerRightBAC_eq,
    HexagonAtoms302.assocCAB_eq,
    HexagonAtoms302.outerLeftABC_eq,
    HexagonRowColumn302.product0_eq,
    HexagonRowColumn302.product1_eq,
    HexagonRowColumn302.product2_eq,
    HexagonRowColumn302.product3_eq,
    HexagonRowColumn302.product4_eq,
    HexagonRowColumn302.product5_eq,
    HexagonRowColumn302.product6_eq,
    HexagonRowColumn302.product7_eq] using rightFinal3_case_0_2_checked

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonCases3
