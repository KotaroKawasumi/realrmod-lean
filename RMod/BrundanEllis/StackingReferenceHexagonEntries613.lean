import RMod.BrundanEllis.StackingReferenceHexagonMiddle6
import RMod.BrundanEllis.StackingReferenceSparseMatrixCheck
import RMod.BrundanEllis.StackingReferenceHexagonAtoms613
import RMod.BrundanEllis.StackingReferenceHexagonRowColumn613

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

private theorem left0Middle6_eq_case_1_3_row_0_0_0 : (left0Middle6 1 3) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms613.assocABC) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_1_3_row_0_0_1 : (left0Middle6 1 3) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms613.assocABC) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_1_3_row_0_0_2 : (left0Middle6 1 3) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms613.assocABC) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_1_3_row_0_0_3 : (left0Middle6 1 3) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms613.assocABC) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_1_3_row_0_1_0 : (left0Middle6 1 3) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms613.assocABC) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_1_3_row_0_1_1 : (left0Middle6 1 3) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms613.assocABC) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_1_3_row_0_1_2 : (left0Middle6 1 3) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms613.assocABC) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_1_3_row_0_1_3 : (left0Middle6 1 3) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms613.assocABC) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_1_3_row_1_0_0 : (left0Middle6 1 3) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms613.assocABC) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_1_3_row_1_0_1 : (left0Middle6 1 3) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms613.assocABC) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_1_3_row_1_0_2 : (left0Middle6 1 3) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms613.assocABC) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_1_3_row_1_0_3 : (left0Middle6 1 3) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms613.assocABC) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_1_3_row_1_1_0 : (left0Middle6 1 3) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms613.assocABC) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_1_3_row_1_1_1 : (left0Middle6 1 3) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms613.assocABC) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_1_3_row_1_1_2 : (left0Middle6 1 3) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms613.assocABC) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_1_3_row_1_1_3 : (left0Middle6 1 3) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms613.assocABC) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_1_3_checked : left0Middle6 1 3 = HexagonAtoms613.assocABC := by
  funext r
  fin_cases r
  · exact left0Middle6_eq_case_1_3_row_0_0_0
  · exact left0Middle6_eq_case_1_3_row_0_0_1
  · exact left0Middle6_eq_case_1_3_row_0_0_2
  · exact left0Middle6_eq_case_1_3_row_0_0_3
  · exact left0Middle6_eq_case_1_3_row_0_1_0
  · exact left0Middle6_eq_case_1_3_row_0_1_1
  · exact left0Middle6_eq_case_1_3_row_0_1_2
  · exact left0Middle6_eq_case_1_3_row_0_1_3
  · exact left0Middle6_eq_case_1_3_row_1_0_0
  · exact left0Middle6_eq_case_1_3_row_1_0_1
  · exact left0Middle6_eq_case_1_3_row_1_0_2
  · exact left0Middle6_eq_case_1_3_row_1_0_3
  · exact left0Middle6_eq_case_1_3_row_1_1_0
  · exact left0Middle6_eq_case_1_3_row_1_1_1
  · exact left0Middle6_eq_case_1_3_row_1_1_2
  · exact left0Middle6_eq_case_1_3_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem left0Middle6_eq_case_1_3 : left0Middle6 1 3 = outerRightZ 6 1 3 * associatorZ 6 1 3 := by
  simpa only [HexagonAtoms613.assocABC_eq,
    HexagonAtoms613.outerABC_eq,
    HexagonAtoms613.assocBAC_eq,
    HexagonAtoms613.innerABC_eq,
    HexagonAtoms613.innerRightABC_eq,
    HexagonAtoms613.inverseACB_eq,
    HexagonAtoms613.innerACB_eq,
    HexagonAtoms613.assocBCA_eq,
    HexagonAtoms613.innerRightBAC_eq,
    HexagonAtoms613.assocCAB_eq,
    HexagonAtoms613.outerLeftABC_eq,
    HexagonRowColumn613.product0_eq,
    HexagonRowColumn613.product1_eq,
    HexagonRowColumn613.product2_eq,
    HexagonRowColumn613.product3_eq,
    HexagonRowColumn613.product4_eq,
    HexagonRowColumn613.product5_eq,
    HexagonRowColumn613.product6_eq,
    HexagonRowColumn613.product7_eq] using left0Middle6_eq_case_1_3_checked

private theorem left1Middle6_eq_case_1_3_row_0_0_0 : (left1Middle6 1 3) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms613.assocBAC) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_1_3_row_0_0_1 : (left1Middle6 1 3) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms613.assocBAC) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_1_3_row_0_0_2 : (left1Middle6 1 3) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms613.assocBAC) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_1_3_row_0_0_3 : (left1Middle6 1 3) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms613.assocBAC) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_1_3_row_1_0_0 : (left1Middle6 1 3) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms613.assocBAC) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_1_3_row_1_0_1 : (left1Middle6 1 3) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms613.assocBAC) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_1_3_row_1_0_2 : (left1Middle6 1 3) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms613.assocBAC) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_1_3_row_1_0_3 : (left1Middle6 1 3) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms613.assocBAC) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_1_3_row_2_0_0 : (left1Middle6 1 3) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms613.assocBAC) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_1_3_row_2_0_1 : (left1Middle6 1 3) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms613.assocBAC) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_1_3_row_2_0_2 : (left1Middle6 1 3) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms613.assocBAC) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_1_3_row_2_0_3 : (left1Middle6 1 3) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms613.assocBAC) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_1_3_row_3_0_0 : (left1Middle6 1 3) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms613.assocBAC) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_1_3_row_3_0_1 : (left1Middle6 1 3) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms613.assocBAC) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_1_3_row_3_0_2 : (left1Middle6 1 3) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms613.assocBAC) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_1_3_row_3_0_3 : (left1Middle6 1 3) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms613.assocBAC) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_1_3_checked : left1Middle6 1 3 = HexagonAtoms613.assocBAC := by
  funext r
  fin_cases r
  · exact left1Middle6_eq_case_1_3_row_0_0_0
  · exact left1Middle6_eq_case_1_3_row_0_0_1
  · exact left1Middle6_eq_case_1_3_row_0_0_2
  · exact left1Middle6_eq_case_1_3_row_0_0_3
  · exact left1Middle6_eq_case_1_3_row_1_0_0
  · exact left1Middle6_eq_case_1_3_row_1_0_1
  · exact left1Middle6_eq_case_1_3_row_1_0_2
  · exact left1Middle6_eq_case_1_3_row_1_0_3
  · exact left1Middle6_eq_case_1_3_row_2_0_0
  · exact left1Middle6_eq_case_1_3_row_2_0_1
  · exact left1Middle6_eq_case_1_3_row_2_0_2
  · exact left1Middle6_eq_case_1_3_row_2_0_3
  · exact left1Middle6_eq_case_1_3_row_3_0_0
  · exact left1Middle6_eq_case_1_3_row_3_0_1
  · exact left1Middle6_eq_case_1_3_row_3_0_2
  · exact left1Middle6_eq_case_1_3_row_3_0_3

set_option backward.isDefEq.respectTransparency false in
theorem left1Middle6_eq_case_1_3 : left1Middle6 1 3 = associatorZ 1 6 3 * innerLeftZ 6 1 3 := by
  simpa only [HexagonAtoms613.assocABC_eq,
    HexagonAtoms613.outerABC_eq,
    HexagonAtoms613.assocBAC_eq,
    HexagonAtoms613.innerABC_eq,
    HexagonAtoms613.innerRightABC_eq,
    HexagonAtoms613.inverseACB_eq,
    HexagonAtoms613.innerACB_eq,
    HexagonAtoms613.assocBCA_eq,
    HexagonAtoms613.innerRightBAC_eq,
    HexagonAtoms613.assocCAB_eq,
    HexagonAtoms613.outerLeftABC_eq,
    HexagonRowColumn613.product0_eq,
    HexagonRowColumn613.product1_eq,
    HexagonRowColumn613.product2_eq,
    HexagonRowColumn613.product3_eq,
    HexagonRowColumn613.product4_eq,
    HexagonRowColumn613.product5_eq,
    HexagonRowColumn613.product6_eq,
    HexagonRowColumn613.product7_eq] using left1Middle6_eq_case_1_3_checked

private theorem right0Middle6_eq_case_1_3_row_0_0_0 : (right0Middle6 1 3) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms613.assocABC) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_1_3_row_0_0_1 : (right0Middle6 1 3) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms613.assocABC) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_1_3_row_0_0_2 : (right0Middle6 1 3) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms613.assocABC) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_1_3_row_0_0_3 : (right0Middle6 1 3) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms613.assocABC) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_1_3_row_0_1_0 : (right0Middle6 1 3) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms613.assocABC) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_1_3_row_0_1_1 : (right0Middle6 1 3) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms613.assocABC) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_1_3_row_0_1_2 : (right0Middle6 1 3) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms613.assocABC) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_1_3_row_0_1_3 : (right0Middle6 1 3) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms613.assocABC) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_1_3_row_1_0_0 : (right0Middle6 1 3) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms613.assocABC) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_1_3_row_1_0_1 : (right0Middle6 1 3) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms613.assocABC) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_1_3_row_1_0_2 : (right0Middle6 1 3) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms613.assocABC) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_1_3_row_1_0_3 : (right0Middle6 1 3) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms613.assocABC) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_1_3_row_1_1_0 : (right0Middle6 1 3) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms613.assocABC) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_1_3_row_1_1_1 : (right0Middle6 1 3) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms613.assocABC) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_1_3_row_1_1_2 : (right0Middle6 1 3) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms613.assocABC) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_1_3_row_1_1_3 : (right0Middle6 1 3) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms613.assocABC) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_1_3_checked : right0Middle6 1 3 = HexagonAtoms613.assocABC := by
  funext r
  fin_cases r
  · exact right0Middle6_eq_case_1_3_row_0_0_0
  · exact right0Middle6_eq_case_1_3_row_0_0_1
  · exact right0Middle6_eq_case_1_3_row_0_0_2
  · exact right0Middle6_eq_case_1_3_row_0_0_3
  · exact right0Middle6_eq_case_1_3_row_0_1_0
  · exact right0Middle6_eq_case_1_3_row_0_1_1
  · exact right0Middle6_eq_case_1_3_row_0_1_2
  · exact right0Middle6_eq_case_1_3_row_0_1_3
  · exact right0Middle6_eq_case_1_3_row_1_0_0
  · exact right0Middle6_eq_case_1_3_row_1_0_1
  · exact right0Middle6_eq_case_1_3_row_1_0_2
  · exact right0Middle6_eq_case_1_3_row_1_0_3
  · exact right0Middle6_eq_case_1_3_row_1_1_0
  · exact right0Middle6_eq_case_1_3_row_1_1_1
  · exact right0Middle6_eq_case_1_3_row_1_1_2
  · exact right0Middle6_eq_case_1_3_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem right0Middle6_eq_case_1_3 : right0Middle6 1 3 = innerRightZ 6 1 3 * associatorZ 6 1 3 := by
  simpa only [HexagonAtoms613.assocABC_eq,
    HexagonAtoms613.outerABC_eq,
    HexagonAtoms613.assocBAC_eq,
    HexagonAtoms613.innerABC_eq,
    HexagonAtoms613.innerRightABC_eq,
    HexagonAtoms613.inverseACB_eq,
    HexagonAtoms613.innerACB_eq,
    HexagonAtoms613.assocBCA_eq,
    HexagonAtoms613.innerRightBAC_eq,
    HexagonAtoms613.assocCAB_eq,
    HexagonAtoms613.outerLeftABC_eq,
    HexagonRowColumn613.product0_eq,
    HexagonRowColumn613.product1_eq,
    HexagonRowColumn613.product2_eq,
    HexagonRowColumn613.product3_eq,
    HexagonRowColumn613.product4_eq,
    HexagonRowColumn613.product5_eq,
    HexagonRowColumn613.product6_eq,
    HexagonRowColumn613.product7_eq] using right0Middle6_eq_case_1_3_checked

private theorem right1Middle6_eq_case_1_3_row_0_0_0 : (right1Middle6 1 3) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn613.rows_inverseACB HexagonRowColumn613.cols_right0) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_1_3_row_0_0_1 : (right1Middle6 1 3) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn613.rows_inverseACB HexagonRowColumn613.cols_right0) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_1_3_row_0_0_2 : (right1Middle6 1 3) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn613.rows_inverseACB HexagonRowColumn613.cols_right0) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_1_3_row_0_0_3 : (right1Middle6 1 3) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn613.rows_inverseACB HexagonRowColumn613.cols_right0) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_1_3_row_1_0_0 : (right1Middle6 1 3) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn613.rows_inverseACB HexagonRowColumn613.cols_right0) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_1_3_row_1_0_1 : (right1Middle6 1 3) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn613.rows_inverseACB HexagonRowColumn613.cols_right0) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_1_3_row_1_0_2 : (right1Middle6 1 3) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn613.rows_inverseACB HexagonRowColumn613.cols_right0) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_1_3_row_1_0_3 : (right1Middle6 1 3) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn613.rows_inverseACB HexagonRowColumn613.cols_right0) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_1_3_row_2_0_0 : (right1Middle6 1 3) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn613.rows_inverseACB HexagonRowColumn613.cols_right0) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_1_3_row_2_0_1 : (right1Middle6 1 3) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn613.rows_inverseACB HexagonRowColumn613.cols_right0) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_1_3_row_2_0_2 : (right1Middle6 1 3) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn613.rows_inverseACB HexagonRowColumn613.cols_right0) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_1_3_row_2_0_3 : (right1Middle6 1 3) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn613.rows_inverseACB HexagonRowColumn613.cols_right0) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_1_3_row_3_0_0 : (right1Middle6 1 3) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn613.rows_inverseACB HexagonRowColumn613.cols_right0) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_1_3_row_3_0_1 : (right1Middle6 1 3) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn613.rows_inverseACB HexagonRowColumn613.cols_right0) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_1_3_row_3_0_2 : (right1Middle6 1 3) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn613.rows_inverseACB HexagonRowColumn613.cols_right0) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_1_3_row_3_0_3 : (right1Middle6 1 3) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn613.rows_inverseACB HexagonRowColumn613.cols_right0) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_1_3_checked : right1Middle6 1 3 = rowColumnMul HexagonRowColumn613.rows_inverseACB HexagonRowColumn613.cols_right0 := by
  funext r
  fin_cases r
  · exact right1Middle6_eq_case_1_3_row_0_0_0
  · exact right1Middle6_eq_case_1_3_row_0_0_1
  · exact right1Middle6_eq_case_1_3_row_0_0_2
  · exact right1Middle6_eq_case_1_3_row_0_0_3
  · exact right1Middle6_eq_case_1_3_row_1_0_0
  · exact right1Middle6_eq_case_1_3_row_1_0_1
  · exact right1Middle6_eq_case_1_3_row_1_0_2
  · exact right1Middle6_eq_case_1_3_row_1_0_3
  · exact right1Middle6_eq_case_1_3_row_2_0_0
  · exact right1Middle6_eq_case_1_3_row_2_0_1
  · exact right1Middle6_eq_case_1_3_row_2_0_2
  · exact right1Middle6_eq_case_1_3_row_2_0_3
  · exact right1Middle6_eq_case_1_3_row_3_0_0
  · exact right1Middle6_eq_case_1_3_row_3_0_1
  · exact right1Middle6_eq_case_1_3_row_3_0_2
  · exact right1Middle6_eq_case_1_3_row_3_0_3

set_option backward.isDefEq.respectTransparency false in
theorem right1Middle6_eq_case_1_3 : right1Middle6 1 3 = associatorInverseZ 6 3 1 * right0Middle6 1 3 := by
  simpa only [HexagonAtoms613.assocABC_eq,
    HexagonAtoms613.outerABC_eq,
    HexagonAtoms613.assocBAC_eq,
    HexagonAtoms613.innerABC_eq,
    HexagonAtoms613.innerRightABC_eq,
    HexagonAtoms613.inverseACB_eq,
    HexagonAtoms613.innerACB_eq,
    HexagonAtoms613.assocBCA_eq,
    HexagonAtoms613.innerRightBAC_eq,
    HexagonAtoms613.assocCAB_eq,
    HexagonAtoms613.outerLeftABC_eq,
    HexagonRowColumn613.product0_eq,
    HexagonRowColumn613.product1_eq,
    HexagonRowColumn613.product2_eq,
    HexagonRowColumn613.product3_eq,
    HexagonRowColumn613.product4_eq,
    HexagonRowColumn613.product5_eq,
    HexagonRowColumn613.product6_eq,
    HexagonRowColumn613.product7_eq] using right1Middle6_eq_case_1_3_checked

private theorem right2Middle6_eq_case_1_3_row_0_0_0 : (right2Middle6 1 3) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (right1Middle6 1 3) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_1_3_row_0_0_1 : (right2Middle6 1 3) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (right1Middle6 1 3) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_1_3_row_0_0_2 : (right2Middle6 1 3) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (right1Middle6 1 3) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_1_3_row_0_0_3 : (right2Middle6 1 3) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (right1Middle6 1 3) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_1_3_row_1_0_0 : (right2Middle6 1 3) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (right1Middle6 1 3) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_1_3_row_1_0_1 : (right2Middle6 1 3) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (right1Middle6 1 3) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_1_3_row_1_0_2 : (right2Middle6 1 3) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (right1Middle6 1 3) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_1_3_row_1_0_3 : (right2Middle6 1 3) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (right1Middle6 1 3) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_1_3_row_2_0_0 : (right2Middle6 1 3) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (right1Middle6 1 3) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_1_3_row_2_0_1 : (right2Middle6 1 3) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (right1Middle6 1 3) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_1_3_row_2_0_2 : (right2Middle6 1 3) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (right1Middle6 1 3) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_1_3_row_2_0_3 : (right2Middle6 1 3) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (right1Middle6 1 3) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_1_3_row_3_0_0 : (right2Middle6 1 3) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (right1Middle6 1 3) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_1_3_row_3_0_1 : (right2Middle6 1 3) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (right1Middle6 1 3) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_1_3_row_3_0_2 : (right2Middle6 1 3) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (right1Middle6 1 3) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_1_3_row_3_0_3 : (right2Middle6 1 3) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (right1Middle6 1 3) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_1_3_checked : right2Middle6 1 3 = right1Middle6 1 3 := by
  funext r
  fin_cases r
  · exact right2Middle6_eq_case_1_3_row_0_0_0
  · exact right2Middle6_eq_case_1_3_row_0_0_1
  · exact right2Middle6_eq_case_1_3_row_0_0_2
  · exact right2Middle6_eq_case_1_3_row_0_0_3
  · exact right2Middle6_eq_case_1_3_row_1_0_0
  · exact right2Middle6_eq_case_1_3_row_1_0_1
  · exact right2Middle6_eq_case_1_3_row_1_0_2
  · exact right2Middle6_eq_case_1_3_row_1_0_3
  · exact right2Middle6_eq_case_1_3_row_2_0_0
  · exact right2Middle6_eq_case_1_3_row_2_0_1
  · exact right2Middle6_eq_case_1_3_row_2_0_2
  · exact right2Middle6_eq_case_1_3_row_2_0_3
  · exact right2Middle6_eq_case_1_3_row_3_0_0
  · exact right2Middle6_eq_case_1_3_row_3_0_1
  · exact right2Middle6_eq_case_1_3_row_3_0_2
  · exact right2Middle6_eq_case_1_3_row_3_0_3

set_option backward.isDefEq.respectTransparency false in
theorem right2Middle6_eq_case_1_3 : right2Middle6 1 3 = innerLeftZ 6 3 1 * right1Middle6 1 3 := by
  simpa only [HexagonAtoms613.assocABC_eq,
    HexagonAtoms613.outerABC_eq,
    HexagonAtoms613.assocBAC_eq,
    HexagonAtoms613.innerABC_eq,
    HexagonAtoms613.innerRightABC_eq,
    HexagonAtoms613.inverseACB_eq,
    HexagonAtoms613.innerACB_eq,
    HexagonAtoms613.assocBCA_eq,
    HexagonAtoms613.innerRightBAC_eq,
    HexagonAtoms613.assocCAB_eq,
    HexagonAtoms613.outerLeftABC_eq,
    HexagonRowColumn613.product0_eq,
    HexagonRowColumn613.product1_eq,
    HexagonRowColumn613.product2_eq,
    HexagonRowColumn613.product3_eq,
    HexagonRowColumn613.product4_eq,
    HexagonRowColumn613.product5_eq,
    HexagonRowColumn613.product6_eq,
    HexagonRowColumn613.product7_eq] using right2Middle6_eq_case_1_3_checked

private theorem leftFinal6_case_1_3_row_0_0_0 : (((-1 : ℤ) ^ (leftScaleBit 6 1 3).val * positiveScale (leftScaleExponent 6 1 3)) •
      (rowColumnMul HexagonRowColumn613.rows_assocBCA HexagonRowColumn613.cols_left0)) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (negativeScale (leftScaleExponent 6 1 3) • (left1Middle6 1 3)) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal6_case_1_3_row_0_0_1 : (((-1 : ℤ) ^ (leftScaleBit 6 1 3).val * positiveScale (leftScaleExponent 6 1 3)) •
      (rowColumnMul HexagonRowColumn613.rows_assocBCA HexagonRowColumn613.cols_left0)) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (negativeScale (leftScaleExponent 6 1 3) • (left1Middle6 1 3)) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal6_case_1_3_row_0_0_2 : (((-1 : ℤ) ^ (leftScaleBit 6 1 3).val * positiveScale (leftScaleExponent 6 1 3)) •
      (rowColumnMul HexagonRowColumn613.rows_assocBCA HexagonRowColumn613.cols_left0)) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (negativeScale (leftScaleExponent 6 1 3) • (left1Middle6 1 3)) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal6_case_1_3_row_0_0_3 : (((-1 : ℤ) ^ (leftScaleBit 6 1 3).val * positiveScale (leftScaleExponent 6 1 3)) •
      (rowColumnMul HexagonRowColumn613.rows_assocBCA HexagonRowColumn613.cols_left0)) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (negativeScale (leftScaleExponent 6 1 3) • (left1Middle6 1 3)) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal6_case_1_3_row_1_0_0 : (((-1 : ℤ) ^ (leftScaleBit 6 1 3).val * positiveScale (leftScaleExponent 6 1 3)) •
      (rowColumnMul HexagonRowColumn613.rows_assocBCA HexagonRowColumn613.cols_left0)) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (negativeScale (leftScaleExponent 6 1 3) • (left1Middle6 1 3)) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal6_case_1_3_row_1_0_1 : (((-1 : ℤ) ^ (leftScaleBit 6 1 3).val * positiveScale (leftScaleExponent 6 1 3)) •
      (rowColumnMul HexagonRowColumn613.rows_assocBCA HexagonRowColumn613.cols_left0)) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (negativeScale (leftScaleExponent 6 1 3) • (left1Middle6 1 3)) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal6_case_1_3_row_1_0_2 : (((-1 : ℤ) ^ (leftScaleBit 6 1 3).val * positiveScale (leftScaleExponent 6 1 3)) •
      (rowColumnMul HexagonRowColumn613.rows_assocBCA HexagonRowColumn613.cols_left0)) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (negativeScale (leftScaleExponent 6 1 3) • (left1Middle6 1 3)) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal6_case_1_3_row_1_0_3 : (((-1 : ℤ) ^ (leftScaleBit 6 1 3).val * positiveScale (leftScaleExponent 6 1 3)) •
      (rowColumnMul HexagonRowColumn613.rows_assocBCA HexagonRowColumn613.cols_left0)) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (negativeScale (leftScaleExponent 6 1 3) • (left1Middle6 1 3)) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal6_case_1_3_row_2_0_0 : (((-1 : ℤ) ^ (leftScaleBit 6 1 3).val * positiveScale (leftScaleExponent 6 1 3)) •
      (rowColumnMul HexagonRowColumn613.rows_assocBCA HexagonRowColumn613.cols_left0)) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (negativeScale (leftScaleExponent 6 1 3) • (left1Middle6 1 3)) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal6_case_1_3_row_2_0_1 : (((-1 : ℤ) ^ (leftScaleBit 6 1 3).val * positiveScale (leftScaleExponent 6 1 3)) •
      (rowColumnMul HexagonRowColumn613.rows_assocBCA HexagonRowColumn613.cols_left0)) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (negativeScale (leftScaleExponent 6 1 3) • (left1Middle6 1 3)) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal6_case_1_3_row_2_0_2 : (((-1 : ℤ) ^ (leftScaleBit 6 1 3).val * positiveScale (leftScaleExponent 6 1 3)) •
      (rowColumnMul HexagonRowColumn613.rows_assocBCA HexagonRowColumn613.cols_left0)) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (negativeScale (leftScaleExponent 6 1 3) • (left1Middle6 1 3)) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal6_case_1_3_row_2_0_3 : (((-1 : ℤ) ^ (leftScaleBit 6 1 3).val * positiveScale (leftScaleExponent 6 1 3)) •
      (rowColumnMul HexagonRowColumn613.rows_assocBCA HexagonRowColumn613.cols_left0)) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (negativeScale (leftScaleExponent 6 1 3) • (left1Middle6 1 3)) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal6_case_1_3_row_3_0_0 : (((-1 : ℤ) ^ (leftScaleBit 6 1 3).val * positiveScale (leftScaleExponent 6 1 3)) •
      (rowColumnMul HexagonRowColumn613.rows_assocBCA HexagonRowColumn613.cols_left0)) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (negativeScale (leftScaleExponent 6 1 3) • (left1Middle6 1 3)) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal6_case_1_3_row_3_0_1 : (((-1 : ℤ) ^ (leftScaleBit 6 1 3).val * positiveScale (leftScaleExponent 6 1 3)) •
      (rowColumnMul HexagonRowColumn613.rows_assocBCA HexagonRowColumn613.cols_left0)) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (negativeScale (leftScaleExponent 6 1 3) • (left1Middle6 1 3)) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal6_case_1_3_row_3_0_2 : (((-1 : ℤ) ^ (leftScaleBit 6 1 3).val * positiveScale (leftScaleExponent 6 1 3)) •
      (rowColumnMul HexagonRowColumn613.rows_assocBCA HexagonRowColumn613.cols_left0)) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (negativeScale (leftScaleExponent 6 1 3) • (left1Middle6 1 3)) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal6_case_1_3_row_3_0_3 : (((-1 : ℤ) ^ (leftScaleBit 6 1 3).val * positiveScale (leftScaleExponent 6 1 3)) •
      (rowColumnMul HexagonRowColumn613.rows_assocBCA HexagonRowColumn613.cols_left0)) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (negativeScale (leftScaleExponent 6 1 3) • (left1Middle6 1 3)) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal6_case_1_3_checked : ((-1 : ℤ) ^ (leftScaleBit 6 1 3).val * positiveScale (leftScaleExponent 6 1 3)) •
      (rowColumnMul HexagonRowColumn613.rows_assocBCA HexagonRowColumn613.cols_left0) = negativeScale (leftScaleExponent 6 1 3) • (left1Middle6 1 3) := by
  funext r
  fin_cases r
  · exact leftFinal6_case_1_3_row_0_0_0
  · exact leftFinal6_case_1_3_row_0_0_1
  · exact leftFinal6_case_1_3_row_0_0_2
  · exact leftFinal6_case_1_3_row_0_0_3
  · exact leftFinal6_case_1_3_row_1_0_0
  · exact leftFinal6_case_1_3_row_1_0_1
  · exact leftFinal6_case_1_3_row_1_0_2
  · exact leftFinal6_case_1_3_row_1_0_3
  · exact leftFinal6_case_1_3_row_2_0_0
  · exact leftFinal6_case_1_3_row_2_0_1
  · exact leftFinal6_case_1_3_row_2_0_2
  · exact leftFinal6_case_1_3_row_2_0_3
  · exact leftFinal6_case_1_3_row_3_0_0
  · exact leftFinal6_case_1_3_row_3_0_1
  · exact leftFinal6_case_1_3_row_3_0_2
  · exact leftFinal6_case_1_3_row_3_0_3

set_option backward.isDefEq.respectTransparency false in
theorem leftFinal6_case_1_3 : ((-1 : ℤ) ^ (leftScaleBit 6 1 3).val * positiveScale (leftScaleExponent 6 1 3)) •
      (associatorZ 1 3 6 * left0Middle6 1 3) = negativeScale (leftScaleExponent 6 1 3) • (innerRightZ 1 6 3 * left1Middle6 1 3) := by
  simpa only [HexagonAtoms613.assocABC_eq,
    HexagonAtoms613.outerABC_eq,
    HexagonAtoms613.assocBAC_eq,
    HexagonAtoms613.innerABC_eq,
    HexagonAtoms613.innerRightABC_eq,
    HexagonAtoms613.inverseACB_eq,
    HexagonAtoms613.innerACB_eq,
    HexagonAtoms613.assocBCA_eq,
    HexagonAtoms613.innerRightBAC_eq,
    HexagonAtoms613.assocCAB_eq,
    HexagonAtoms613.outerLeftABC_eq,
    HexagonRowColumn613.product0_eq,
    HexagonRowColumn613.product1_eq,
    HexagonRowColumn613.product2_eq,
    HexagonRowColumn613.product3_eq,
    HexagonRowColumn613.product4_eq,
    HexagonRowColumn613.product5_eq,
    HexagonRowColumn613.product6_eq,
    HexagonRowColumn613.product7_eq] using leftFinal6_case_1_3_checked

private theorem rightFinal6_case_1_3_row_0_0_0 : (((-1 : ℤ) ^ (rightScaleBit 6 1 3).val * positiveScale (rightScaleExponent 6 1 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 3 1 : ℤ)) • HexagonAtoms613.outerLeftABC) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 6 1 3) • (rowColumnMul HexagonRowColumn613.rows_assocCAB HexagonRowColumn613.cols_right2)) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal6_case_1_3_row_0_0_1 : (((-1 : ℤ) ^ (rightScaleBit 6 1 3).val * positiveScale (rightScaleExponent 6 1 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 3 1 : ℤ)) • HexagonAtoms613.outerLeftABC) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 6 1 3) • (rowColumnMul HexagonRowColumn613.rows_assocCAB HexagonRowColumn613.cols_right2)) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal6_case_1_3_row_0_0_2 : (((-1 : ℤ) ^ (rightScaleBit 6 1 3).val * positiveScale (rightScaleExponent 6 1 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 3 1 : ℤ)) • HexagonAtoms613.outerLeftABC) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 6 1 3) • (rowColumnMul HexagonRowColumn613.rows_assocCAB HexagonRowColumn613.cols_right2)) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal6_case_1_3_row_0_0_3 : (((-1 : ℤ) ^ (rightScaleBit 6 1 3).val * positiveScale (rightScaleExponent 6 1 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 3 1 : ℤ)) • HexagonAtoms613.outerLeftABC) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 6 1 3) • (rowColumnMul HexagonRowColumn613.rows_assocCAB HexagonRowColumn613.cols_right2)) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal6_case_1_3_row_0_1_0 : (((-1 : ℤ) ^ (rightScaleBit 6 1 3).val * positiveScale (rightScaleExponent 6 1 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 3 1 : ℤ)) • HexagonAtoms613.outerLeftABC) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 6 1 3) • (rowColumnMul HexagonRowColumn613.rows_assocCAB HexagonRowColumn613.cols_right2)) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal6_case_1_3_row_0_1_1 : (((-1 : ℤ) ^ (rightScaleBit 6 1 3).val * positiveScale (rightScaleExponent 6 1 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 3 1 : ℤ)) • HexagonAtoms613.outerLeftABC) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 6 1 3) • (rowColumnMul HexagonRowColumn613.rows_assocCAB HexagonRowColumn613.cols_right2)) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal6_case_1_3_row_0_1_2 : (((-1 : ℤ) ^ (rightScaleBit 6 1 3).val * positiveScale (rightScaleExponent 6 1 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 3 1 : ℤ)) • HexagonAtoms613.outerLeftABC) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 6 1 3) • (rowColumnMul HexagonRowColumn613.rows_assocCAB HexagonRowColumn613.cols_right2)) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal6_case_1_3_row_0_1_3 : (((-1 : ℤ) ^ (rightScaleBit 6 1 3).val * positiveScale (rightScaleExponent 6 1 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 3 1 : ℤ)) • HexagonAtoms613.outerLeftABC) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 6 1 3) • (rowColumnMul HexagonRowColumn613.rows_assocCAB HexagonRowColumn613.cols_right2)) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal6_case_1_3_row_1_0_0 : (((-1 : ℤ) ^ (rightScaleBit 6 1 3).val * positiveScale (rightScaleExponent 6 1 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 3 1 : ℤ)) • HexagonAtoms613.outerLeftABC) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 6 1 3) • (rowColumnMul HexagonRowColumn613.rows_assocCAB HexagonRowColumn613.cols_right2)) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal6_case_1_3_row_1_0_1 : (((-1 : ℤ) ^ (rightScaleBit 6 1 3).val * positiveScale (rightScaleExponent 6 1 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 3 1 : ℤ)) • HexagonAtoms613.outerLeftABC) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 6 1 3) • (rowColumnMul HexagonRowColumn613.rows_assocCAB HexagonRowColumn613.cols_right2)) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal6_case_1_3_row_1_0_2 : (((-1 : ℤ) ^ (rightScaleBit 6 1 3).val * positiveScale (rightScaleExponent 6 1 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 3 1 : ℤ)) • HexagonAtoms613.outerLeftABC) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 6 1 3) • (rowColumnMul HexagonRowColumn613.rows_assocCAB HexagonRowColumn613.cols_right2)) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal6_case_1_3_row_1_0_3 : (((-1 : ℤ) ^ (rightScaleBit 6 1 3).val * positiveScale (rightScaleExponent 6 1 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 3 1 : ℤ)) • HexagonAtoms613.outerLeftABC) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 6 1 3) • (rowColumnMul HexagonRowColumn613.rows_assocCAB HexagonRowColumn613.cols_right2)) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal6_case_1_3_row_1_1_0 : (((-1 : ℤ) ^ (rightScaleBit 6 1 3).val * positiveScale (rightScaleExponent 6 1 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 3 1 : ℤ)) • HexagonAtoms613.outerLeftABC) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 6 1 3) • (rowColumnMul HexagonRowColumn613.rows_assocCAB HexagonRowColumn613.cols_right2)) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal6_case_1_3_row_1_1_1 : (((-1 : ℤ) ^ (rightScaleBit 6 1 3).val * positiveScale (rightScaleExponent 6 1 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 3 1 : ℤ)) • HexagonAtoms613.outerLeftABC) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 6 1 3) • (rowColumnMul HexagonRowColumn613.rows_assocCAB HexagonRowColumn613.cols_right2)) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal6_case_1_3_row_1_1_2 : (((-1 : ℤ) ^ (rightScaleBit 6 1 3).val * positiveScale (rightScaleExponent 6 1 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 3 1 : ℤ)) • HexagonAtoms613.outerLeftABC) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 6 1 3) • (rowColumnMul HexagonRowColumn613.rows_assocCAB HexagonRowColumn613.cols_right2)) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal6_case_1_3_row_1_1_3 : (((-1 : ℤ) ^ (rightScaleBit 6 1 3).val * positiveScale (rightScaleExponent 6 1 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 3 1 : ℤ)) • HexagonAtoms613.outerLeftABC) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 6 1 3) • (rowColumnMul HexagonRowColumn613.rows_assocCAB HexagonRowColumn613.cols_right2)) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal6_case_1_3_checked : ((-1 : ℤ) ^ (rightScaleBit 6 1 3).val * positiveScale (rightScaleExponent 6 1 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 3 1 : ℤ)) • HexagonAtoms613.outerLeftABC = negativeScale (rightScaleExponent 6 1 3) • (rowColumnMul HexagonRowColumn613.rows_assocCAB HexagonRowColumn613.cols_right2) := by
  funext r
  fin_cases r
  · exact rightFinal6_case_1_3_row_0_0_0
  · exact rightFinal6_case_1_3_row_0_0_1
  · exact rightFinal6_case_1_3_row_0_0_2
  · exact rightFinal6_case_1_3_row_0_0_3
  · exact rightFinal6_case_1_3_row_0_1_0
  · exact rightFinal6_case_1_3_row_0_1_1
  · exact rightFinal6_case_1_3_row_0_1_2
  · exact rightFinal6_case_1_3_row_0_1_3
  · exact rightFinal6_case_1_3_row_1_0_0
  · exact rightFinal6_case_1_3_row_1_0_1
  · exact rightFinal6_case_1_3_row_1_0_2
  · exact rightFinal6_case_1_3_row_1_0_3
  · exact rightFinal6_case_1_3_row_1_1_0
  · exact rightFinal6_case_1_3_row_1_1_1
  · exact rightFinal6_case_1_3_row_1_1_2
  · exact rightFinal6_case_1_3_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem rightFinal6_case_1_3 : ((-1 : ℤ) ^ (rightScaleBit 6 1 3).val * positiveScale (rightScaleExponent 6 1 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 3 1 : ℤ)) • outerLeftZ 6 1 3 = negativeScale (rightScaleExponent 6 1 3) • (associatorZ 3 6 1 * right2Middle6 1 3) := by
  simpa only [HexagonAtoms613.assocABC_eq,
    HexagonAtoms613.outerABC_eq,
    HexagonAtoms613.assocBAC_eq,
    HexagonAtoms613.innerABC_eq,
    HexagonAtoms613.innerRightABC_eq,
    HexagonAtoms613.inverseACB_eq,
    HexagonAtoms613.innerACB_eq,
    HexagonAtoms613.assocBCA_eq,
    HexagonAtoms613.innerRightBAC_eq,
    HexagonAtoms613.assocCAB_eq,
    HexagonAtoms613.outerLeftABC_eq,
    HexagonRowColumn613.product0_eq,
    HexagonRowColumn613.product1_eq,
    HexagonRowColumn613.product2_eq,
    HexagonRowColumn613.product3_eq,
    HexagonRowColumn613.product4_eq,
    HexagonRowColumn613.product5_eq,
    HexagonRowColumn613.product6_eq,
    HexagonRowColumn613.product7_eq] using rightFinal6_case_1_3_checked

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonCases6
