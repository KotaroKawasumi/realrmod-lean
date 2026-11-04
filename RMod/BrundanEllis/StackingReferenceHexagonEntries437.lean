import RMod.BrundanEllis.StackingReferenceHexagonMiddle4
import RMod.BrundanEllis.StackingReferenceSparseMatrixCheck
import RMod.BrundanEllis.StackingReferenceHexagonAtoms437
import RMod.BrundanEllis.StackingReferenceHexagonRowColumn437

/-! Seven closed product identities for one reference triple.
The proof uses only verified atomic maps and ordinary kernel reduction. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
set_option linter.unusedSimpArgs false
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonCases4
open Superfusion

private theorem left0Middle4_eq_case_3_7_row_0_0_0 : (left0Middle4 3 7) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms437.assocABC) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_3_7_row_0_0_1 : (left0Middle4 3 7) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms437.assocABC) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_3_7_row_0_0_2 : (left0Middle4 3 7) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms437.assocABC) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_3_7_row_0_0_3 : (left0Middle4 3 7) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms437.assocABC) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_3_7_row_0_1_0 : (left0Middle4 3 7) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms437.assocABC) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_3_7_row_0_1_1 : (left0Middle4 3 7) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms437.assocABC) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_3_7_row_0_1_2 : (left0Middle4 3 7) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms437.assocABC) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_3_7_row_0_1_3 : (left0Middle4 3 7) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms437.assocABC) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_3_7_row_1_0_0 : (left0Middle4 3 7) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms437.assocABC) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_3_7_row_1_0_1 : (left0Middle4 3 7) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms437.assocABC) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_3_7_row_1_0_2 : (left0Middle4 3 7) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms437.assocABC) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_3_7_row_1_0_3 : (left0Middle4 3 7) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms437.assocABC) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_3_7_row_1_1_0 : (left0Middle4 3 7) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms437.assocABC) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_3_7_row_1_1_1 : (left0Middle4 3 7) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms437.assocABC) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_3_7_row_1_1_2 : (left0Middle4 3 7) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms437.assocABC) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_3_7_row_1_1_3 : (left0Middle4 3 7) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms437.assocABC) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_3_7_checked : left0Middle4 3 7 = HexagonAtoms437.assocABC := by
  funext r
  fin_cases r
  · exact left0Middle4_eq_case_3_7_row_0_0_0
  · exact left0Middle4_eq_case_3_7_row_0_0_1
  · exact left0Middle4_eq_case_3_7_row_0_0_2
  · exact left0Middle4_eq_case_3_7_row_0_0_3
  · exact left0Middle4_eq_case_3_7_row_0_1_0
  · exact left0Middle4_eq_case_3_7_row_0_1_1
  · exact left0Middle4_eq_case_3_7_row_0_1_2
  · exact left0Middle4_eq_case_3_7_row_0_1_3
  · exact left0Middle4_eq_case_3_7_row_1_0_0
  · exact left0Middle4_eq_case_3_7_row_1_0_1
  · exact left0Middle4_eq_case_3_7_row_1_0_2
  · exact left0Middle4_eq_case_3_7_row_1_0_3
  · exact left0Middle4_eq_case_3_7_row_1_1_0
  · exact left0Middle4_eq_case_3_7_row_1_1_1
  · exact left0Middle4_eq_case_3_7_row_1_1_2
  · exact left0Middle4_eq_case_3_7_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem left0Middle4_eq_case_3_7 : left0Middle4 3 7 = outerRightZ 4 3 7 * associatorZ 4 3 7 := by
  simpa only [HexagonAtoms437.assocABC_eq,
    HexagonAtoms437.outerABC_eq,
    HexagonAtoms437.assocBAC_eq,
    HexagonAtoms437.innerABC_eq,
    HexagonAtoms437.innerRightABC_eq,
    HexagonAtoms437.inverseACB_eq,
    HexagonAtoms437.innerACB_eq,
    HexagonAtoms437.assocBCA_eq,
    HexagonAtoms437.innerRightBAC_eq,
    HexagonAtoms437.assocCAB_eq,
    HexagonAtoms437.outerLeftABC_eq,
    HexagonRowColumn437.product0_eq,
    HexagonRowColumn437.product1_eq,
    HexagonRowColumn437.product2_eq,
    HexagonRowColumn437.product3_eq,
    HexagonRowColumn437.product4_eq,
    HexagonRowColumn437.product5_eq,
    HexagonRowColumn437.product6_eq,
    HexagonRowColumn437.product7_eq] using left0Middle4_eq_case_3_7_checked

private theorem left1Middle4_eq_case_3_7_row_0_0_0 : (left1Middle4 3 7) ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4)) = (HexagonAtoms437.assocBAC) ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_3_7_row_0_0_1 : (left1Middle4 3 7) ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4)) = (HexagonAtoms437.assocBAC) ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_3_7_row_0_0_2 : (left1Middle4 3 7) ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4)) = (HexagonAtoms437.assocBAC) ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_3_7_row_0_0_3 : (left1Middle4 3 7) ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4)) = (HexagonAtoms437.assocBAC) ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_3_7_row_0_1_0 : (left1Middle4 3 7) ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4)) = (HexagonAtoms437.assocBAC) ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_3_7_row_0_1_1 : (left1Middle4 3 7) ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4)) = (HexagonAtoms437.assocBAC) ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_3_7_row_0_1_2 : (left1Middle4 3 7) ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4)) = (HexagonAtoms437.assocBAC) ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_3_7_row_0_1_3 : (left1Middle4 3 7) ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4)) = (HexagonAtoms437.assocBAC) ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_3_7_row_0_2_0 : (left1Middle4 3 7) ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4)) = (HexagonAtoms437.assocBAC) ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_3_7_row_0_2_1 : (left1Middle4 3 7) ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4)) = (HexagonAtoms437.assocBAC) ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_3_7_row_0_2_2 : (left1Middle4 3 7) ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4)) = (HexagonAtoms437.assocBAC) ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_3_7_row_0_2_3 : (left1Middle4 3 7) ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4)) = (HexagonAtoms437.assocBAC) ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_3_7_row_0_3_0 : (left1Middle4 3 7) ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4)) = (HexagonAtoms437.assocBAC) ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_3_7_row_0_3_1 : (left1Middle4 3 7) ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4)) = (HexagonAtoms437.assocBAC) ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_3_7_row_0_3_2 : (left1Middle4 3 7) ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4)) = (HexagonAtoms437.assocBAC) ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_3_7_row_0_3_3 : (left1Middle4 3 7) ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4)) = (HexagonAtoms437.assocBAC) ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_3_7_checked : left1Middle4 3 7 = HexagonAtoms437.assocBAC := by
  funext r
  fin_cases r
  · exact left1Middle4_eq_case_3_7_row_0_0_0
  · exact left1Middle4_eq_case_3_7_row_0_0_1
  · exact left1Middle4_eq_case_3_7_row_0_0_2
  · exact left1Middle4_eq_case_3_7_row_0_0_3
  · exact left1Middle4_eq_case_3_7_row_0_1_0
  · exact left1Middle4_eq_case_3_7_row_0_1_1
  · exact left1Middle4_eq_case_3_7_row_0_1_2
  · exact left1Middle4_eq_case_3_7_row_0_1_3
  · exact left1Middle4_eq_case_3_7_row_0_2_0
  · exact left1Middle4_eq_case_3_7_row_0_2_1
  · exact left1Middle4_eq_case_3_7_row_0_2_2
  · exact left1Middle4_eq_case_3_7_row_0_2_3
  · exact left1Middle4_eq_case_3_7_row_0_3_0
  · exact left1Middle4_eq_case_3_7_row_0_3_1
  · exact left1Middle4_eq_case_3_7_row_0_3_2
  · exact left1Middle4_eq_case_3_7_row_0_3_3

set_option backward.isDefEq.respectTransparency false in
theorem left1Middle4_eq_case_3_7 : left1Middle4 3 7 = associatorZ 3 4 7 * innerLeftZ 4 3 7 := by
  simpa only [HexagonAtoms437.assocABC_eq,
    HexagonAtoms437.outerABC_eq,
    HexagonAtoms437.assocBAC_eq,
    HexagonAtoms437.innerABC_eq,
    HexagonAtoms437.innerRightABC_eq,
    HexagonAtoms437.inverseACB_eq,
    HexagonAtoms437.innerACB_eq,
    HexagonAtoms437.assocBCA_eq,
    HexagonAtoms437.innerRightBAC_eq,
    HexagonAtoms437.assocCAB_eq,
    HexagonAtoms437.outerLeftABC_eq,
    HexagonRowColumn437.product0_eq,
    HexagonRowColumn437.product1_eq,
    HexagonRowColumn437.product2_eq,
    HexagonRowColumn437.product3_eq,
    HexagonRowColumn437.product4_eq,
    HexagonRowColumn437.product5_eq,
    HexagonRowColumn437.product6_eq,
    HexagonRowColumn437.product7_eq] using left1Middle4_eq_case_3_7_checked

private theorem right0Middle4_eq_case_3_7_row_0_0_0 : (right0Middle4 3 7) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms437.assocABC) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_3_7_row_0_0_1 : (right0Middle4 3 7) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms437.assocABC) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_3_7_row_0_0_2 : (right0Middle4 3 7) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms437.assocABC) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_3_7_row_0_0_3 : (right0Middle4 3 7) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms437.assocABC) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_3_7_row_0_1_0 : (right0Middle4 3 7) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms437.assocABC) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_3_7_row_0_1_1 : (right0Middle4 3 7) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms437.assocABC) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_3_7_row_0_1_2 : (right0Middle4 3 7) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms437.assocABC) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_3_7_row_0_1_3 : (right0Middle4 3 7) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms437.assocABC) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_3_7_row_1_0_0 : (right0Middle4 3 7) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms437.assocABC) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_3_7_row_1_0_1 : (right0Middle4 3 7) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms437.assocABC) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_3_7_row_1_0_2 : (right0Middle4 3 7) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms437.assocABC) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_3_7_row_1_0_3 : (right0Middle4 3 7) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms437.assocABC) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_3_7_row_1_1_0 : (right0Middle4 3 7) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms437.assocABC) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_3_7_row_1_1_1 : (right0Middle4 3 7) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms437.assocABC) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_3_7_row_1_1_2 : (right0Middle4 3 7) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms437.assocABC) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_3_7_row_1_1_3 : (right0Middle4 3 7) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms437.assocABC) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_3_7_checked : right0Middle4 3 7 = HexagonAtoms437.assocABC := by
  funext r
  fin_cases r
  · exact right0Middle4_eq_case_3_7_row_0_0_0
  · exact right0Middle4_eq_case_3_7_row_0_0_1
  · exact right0Middle4_eq_case_3_7_row_0_0_2
  · exact right0Middle4_eq_case_3_7_row_0_0_3
  · exact right0Middle4_eq_case_3_7_row_0_1_0
  · exact right0Middle4_eq_case_3_7_row_0_1_1
  · exact right0Middle4_eq_case_3_7_row_0_1_2
  · exact right0Middle4_eq_case_3_7_row_0_1_3
  · exact right0Middle4_eq_case_3_7_row_1_0_0
  · exact right0Middle4_eq_case_3_7_row_1_0_1
  · exact right0Middle4_eq_case_3_7_row_1_0_2
  · exact right0Middle4_eq_case_3_7_row_1_0_3
  · exact right0Middle4_eq_case_3_7_row_1_1_0
  · exact right0Middle4_eq_case_3_7_row_1_1_1
  · exact right0Middle4_eq_case_3_7_row_1_1_2
  · exact right0Middle4_eq_case_3_7_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem right0Middle4_eq_case_3_7 : right0Middle4 3 7 = innerRightZ 4 3 7 * associatorZ 4 3 7 := by
  simpa only [HexagonAtoms437.assocABC_eq,
    HexagonAtoms437.outerABC_eq,
    HexagonAtoms437.assocBAC_eq,
    HexagonAtoms437.innerABC_eq,
    HexagonAtoms437.innerRightABC_eq,
    HexagonAtoms437.inverseACB_eq,
    HexagonAtoms437.innerACB_eq,
    HexagonAtoms437.assocBCA_eq,
    HexagonAtoms437.innerRightBAC_eq,
    HexagonAtoms437.assocCAB_eq,
    HexagonAtoms437.outerLeftABC_eq,
    HexagonRowColumn437.product0_eq,
    HexagonRowColumn437.product1_eq,
    HexagonRowColumn437.product2_eq,
    HexagonRowColumn437.product3_eq,
    HexagonRowColumn437.product4_eq,
    HexagonRowColumn437.product5_eq,
    HexagonRowColumn437.product6_eq,
    HexagonRowColumn437.product7_eq] using right0Middle4_eq_case_3_7_checked

private theorem right1Middle4_eq_case_3_7_row_0_0_0 : (right1Middle4 3 7) ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn437.rows_inverseACB HexagonRowColumn437.cols_right0) ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_3_7_row_0_0_1 : (right1Middle4 3 7) ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn437.rows_inverseACB HexagonRowColumn437.cols_right0) ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_3_7_row_0_0_2 : (right1Middle4 3 7) ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn437.rows_inverseACB HexagonRowColumn437.cols_right0) ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_3_7_row_0_0_3 : (right1Middle4 3 7) ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn437.rows_inverseACB HexagonRowColumn437.cols_right0) ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_3_7_row_0_1_0 : (right1Middle4 3 7) ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn437.rows_inverseACB HexagonRowColumn437.cols_right0) ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_3_7_row_0_1_1 : (right1Middle4 3 7) ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn437.rows_inverseACB HexagonRowColumn437.cols_right0) ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_3_7_row_0_1_2 : (right1Middle4 3 7) ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn437.rows_inverseACB HexagonRowColumn437.cols_right0) ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_3_7_row_0_1_3 : (right1Middle4 3 7) ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn437.rows_inverseACB HexagonRowColumn437.cols_right0) ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_3_7_row_0_2_0 : (right1Middle4 3 7) ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn437.rows_inverseACB HexagonRowColumn437.cols_right0) ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_3_7_row_0_2_1 : (right1Middle4 3 7) ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn437.rows_inverseACB HexagonRowColumn437.cols_right0) ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_3_7_row_0_2_2 : (right1Middle4 3 7) ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn437.rows_inverseACB HexagonRowColumn437.cols_right0) ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_3_7_row_0_2_3 : (right1Middle4 3 7) ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn437.rows_inverseACB HexagonRowColumn437.cols_right0) ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_3_7_row_0_3_0 : (right1Middle4 3 7) ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn437.rows_inverseACB HexagonRowColumn437.cols_right0) ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_3_7_row_0_3_1 : (right1Middle4 3 7) ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn437.rows_inverseACB HexagonRowColumn437.cols_right0) ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_3_7_row_0_3_2 : (right1Middle4 3 7) ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn437.rows_inverseACB HexagonRowColumn437.cols_right0) ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_3_7_row_0_3_3 : (right1Middle4 3 7) ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn437.rows_inverseACB HexagonRowColumn437.cols_right0) ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_3_7_checked : right1Middle4 3 7 = rowColumnMul HexagonRowColumn437.rows_inverseACB HexagonRowColumn437.cols_right0 := by
  funext r
  fin_cases r
  · exact right1Middle4_eq_case_3_7_row_0_0_0
  · exact right1Middle4_eq_case_3_7_row_0_0_1
  · exact right1Middle4_eq_case_3_7_row_0_0_2
  · exact right1Middle4_eq_case_3_7_row_0_0_3
  · exact right1Middle4_eq_case_3_7_row_0_1_0
  · exact right1Middle4_eq_case_3_7_row_0_1_1
  · exact right1Middle4_eq_case_3_7_row_0_1_2
  · exact right1Middle4_eq_case_3_7_row_0_1_3
  · exact right1Middle4_eq_case_3_7_row_0_2_0
  · exact right1Middle4_eq_case_3_7_row_0_2_1
  · exact right1Middle4_eq_case_3_7_row_0_2_2
  · exact right1Middle4_eq_case_3_7_row_0_2_3
  · exact right1Middle4_eq_case_3_7_row_0_3_0
  · exact right1Middle4_eq_case_3_7_row_0_3_1
  · exact right1Middle4_eq_case_3_7_row_0_3_2
  · exact right1Middle4_eq_case_3_7_row_0_3_3

set_option backward.isDefEq.respectTransparency false in
theorem right1Middle4_eq_case_3_7 : right1Middle4 3 7 = associatorInverseZ 4 7 3 * right0Middle4 3 7 := by
  simpa only [HexagonAtoms437.assocABC_eq,
    HexagonAtoms437.outerABC_eq,
    HexagonAtoms437.assocBAC_eq,
    HexagonAtoms437.innerABC_eq,
    HexagonAtoms437.innerRightABC_eq,
    HexagonAtoms437.inverseACB_eq,
    HexagonAtoms437.innerACB_eq,
    HexagonAtoms437.assocBCA_eq,
    HexagonAtoms437.innerRightBAC_eq,
    HexagonAtoms437.assocCAB_eq,
    HexagonAtoms437.outerLeftABC_eq,
    HexagonRowColumn437.product0_eq,
    HexagonRowColumn437.product1_eq,
    HexagonRowColumn437.product2_eq,
    HexagonRowColumn437.product3_eq,
    HexagonRowColumn437.product4_eq,
    HexagonRowColumn437.product5_eq,
    HexagonRowColumn437.product6_eq,
    HexagonRowColumn437.product7_eq] using right1Middle4_eq_case_3_7_checked

private theorem right2Middle4_eq_case_3_7_row_0_0_0 : (right2Middle4 3 7) ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4)) = (right1Middle4 3 7) ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_3_7_row_0_0_1 : (right2Middle4 3 7) ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4)) = (right1Middle4 3 7) ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_3_7_row_0_0_2 : (right2Middle4 3 7) ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4)) = (right1Middle4 3 7) ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_3_7_row_0_0_3 : (right2Middle4 3 7) ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4)) = (right1Middle4 3 7) ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_3_7_row_0_1_0 : (right2Middle4 3 7) ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4)) = (right1Middle4 3 7) ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_3_7_row_0_1_1 : (right2Middle4 3 7) ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4)) = (right1Middle4 3 7) ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_3_7_row_0_1_2 : (right2Middle4 3 7) ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4)) = (right1Middle4 3 7) ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_3_7_row_0_1_3 : (right2Middle4 3 7) ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4)) = (right1Middle4 3 7) ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_3_7_row_0_2_0 : (right2Middle4 3 7) ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4)) = (right1Middle4 3 7) ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_3_7_row_0_2_1 : (right2Middle4 3 7) ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4)) = (right1Middle4 3 7) ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_3_7_row_0_2_2 : (right2Middle4 3 7) ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4)) = (right1Middle4 3 7) ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_3_7_row_0_2_3 : (right2Middle4 3 7) ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4)) = (right1Middle4 3 7) ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_3_7_row_0_3_0 : (right2Middle4 3 7) ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4)) = (right1Middle4 3 7) ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_3_7_row_0_3_1 : (right2Middle4 3 7) ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4)) = (right1Middle4 3 7) ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_3_7_row_0_3_2 : (right2Middle4 3 7) ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4)) = (right1Middle4 3 7) ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_3_7_row_0_3_3 : (right2Middle4 3 7) ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4)) = (right1Middle4 3 7) ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_3_7_checked : right2Middle4 3 7 = right1Middle4 3 7 := by
  funext r
  fin_cases r
  · exact right2Middle4_eq_case_3_7_row_0_0_0
  · exact right2Middle4_eq_case_3_7_row_0_0_1
  · exact right2Middle4_eq_case_3_7_row_0_0_2
  · exact right2Middle4_eq_case_3_7_row_0_0_3
  · exact right2Middle4_eq_case_3_7_row_0_1_0
  · exact right2Middle4_eq_case_3_7_row_0_1_1
  · exact right2Middle4_eq_case_3_7_row_0_1_2
  · exact right2Middle4_eq_case_3_7_row_0_1_3
  · exact right2Middle4_eq_case_3_7_row_0_2_0
  · exact right2Middle4_eq_case_3_7_row_0_2_1
  · exact right2Middle4_eq_case_3_7_row_0_2_2
  · exact right2Middle4_eq_case_3_7_row_0_2_3
  · exact right2Middle4_eq_case_3_7_row_0_3_0
  · exact right2Middle4_eq_case_3_7_row_0_3_1
  · exact right2Middle4_eq_case_3_7_row_0_3_2
  · exact right2Middle4_eq_case_3_7_row_0_3_3

set_option backward.isDefEq.respectTransparency false in
theorem right2Middle4_eq_case_3_7 : right2Middle4 3 7 = innerLeftZ 4 7 3 * right1Middle4 3 7 := by
  simpa only [HexagonAtoms437.assocABC_eq,
    HexagonAtoms437.outerABC_eq,
    HexagonAtoms437.assocBAC_eq,
    HexagonAtoms437.innerABC_eq,
    HexagonAtoms437.innerRightABC_eq,
    HexagonAtoms437.inverseACB_eq,
    HexagonAtoms437.innerACB_eq,
    HexagonAtoms437.assocBCA_eq,
    HexagonAtoms437.innerRightBAC_eq,
    HexagonAtoms437.assocCAB_eq,
    HexagonAtoms437.outerLeftABC_eq,
    HexagonRowColumn437.product0_eq,
    HexagonRowColumn437.product1_eq,
    HexagonRowColumn437.product2_eq,
    HexagonRowColumn437.product3_eq,
    HexagonRowColumn437.product4_eq,
    HexagonRowColumn437.product5_eq,
    HexagonRowColumn437.product6_eq,
    HexagonRowColumn437.product7_eq] using right2Middle4_eq_case_3_7_checked

private theorem leftFinal4_case_3_7_row_0_0_0 : (((-1 : ℤ) ^ (leftScaleBit 4 3 7).val * positiveScale (leftScaleExponent 4 3 7)) •
      (rowColumnMul HexagonRowColumn437.rows_assocBCA HexagonRowColumn437.cols_left0)) ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4)) = (negativeScale (leftScaleExponent 4 3 7) • (left1Middle4 3 7)) ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal4_case_3_7_row_0_0_1 : (((-1 : ℤ) ^ (leftScaleBit 4 3 7).val * positiveScale (leftScaleExponent 4 3 7)) •
      (rowColumnMul HexagonRowColumn437.rows_assocBCA HexagonRowColumn437.cols_left0)) ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4)) = (negativeScale (leftScaleExponent 4 3 7) • (left1Middle4 3 7)) ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal4_case_3_7_row_0_0_2 : (((-1 : ℤ) ^ (leftScaleBit 4 3 7).val * positiveScale (leftScaleExponent 4 3 7)) •
      (rowColumnMul HexagonRowColumn437.rows_assocBCA HexagonRowColumn437.cols_left0)) ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4)) = (negativeScale (leftScaleExponent 4 3 7) • (left1Middle4 3 7)) ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal4_case_3_7_row_0_0_3 : (((-1 : ℤ) ^ (leftScaleBit 4 3 7).val * positiveScale (leftScaleExponent 4 3 7)) •
      (rowColumnMul HexagonRowColumn437.rows_assocBCA HexagonRowColumn437.cols_left0)) ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4)) = (negativeScale (leftScaleExponent 4 3 7) • (left1Middle4 3 7)) ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal4_case_3_7_row_0_1_0 : (((-1 : ℤ) ^ (leftScaleBit 4 3 7).val * positiveScale (leftScaleExponent 4 3 7)) •
      (rowColumnMul HexagonRowColumn437.rows_assocBCA HexagonRowColumn437.cols_left0)) ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4)) = (negativeScale (leftScaleExponent 4 3 7) • (left1Middle4 3 7)) ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal4_case_3_7_row_0_1_1 : (((-1 : ℤ) ^ (leftScaleBit 4 3 7).val * positiveScale (leftScaleExponent 4 3 7)) •
      (rowColumnMul HexagonRowColumn437.rows_assocBCA HexagonRowColumn437.cols_left0)) ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4)) = (negativeScale (leftScaleExponent 4 3 7) • (left1Middle4 3 7)) ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal4_case_3_7_row_0_1_2 : (((-1 : ℤ) ^ (leftScaleBit 4 3 7).val * positiveScale (leftScaleExponent 4 3 7)) •
      (rowColumnMul HexagonRowColumn437.rows_assocBCA HexagonRowColumn437.cols_left0)) ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4)) = (negativeScale (leftScaleExponent 4 3 7) • (left1Middle4 3 7)) ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal4_case_3_7_row_0_1_3 : (((-1 : ℤ) ^ (leftScaleBit 4 3 7).val * positiveScale (leftScaleExponent 4 3 7)) •
      (rowColumnMul HexagonRowColumn437.rows_assocBCA HexagonRowColumn437.cols_left0)) ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4)) = (negativeScale (leftScaleExponent 4 3 7) • (left1Middle4 3 7)) ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal4_case_3_7_row_0_2_0 : (((-1 : ℤ) ^ (leftScaleBit 4 3 7).val * positiveScale (leftScaleExponent 4 3 7)) •
      (rowColumnMul HexagonRowColumn437.rows_assocBCA HexagonRowColumn437.cols_left0)) ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4)) = (negativeScale (leftScaleExponent 4 3 7) • (left1Middle4 3 7)) ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal4_case_3_7_row_0_2_1 : (((-1 : ℤ) ^ (leftScaleBit 4 3 7).val * positiveScale (leftScaleExponent 4 3 7)) •
      (rowColumnMul HexagonRowColumn437.rows_assocBCA HexagonRowColumn437.cols_left0)) ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4)) = (negativeScale (leftScaleExponent 4 3 7) • (left1Middle4 3 7)) ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal4_case_3_7_row_0_2_2 : (((-1 : ℤ) ^ (leftScaleBit 4 3 7).val * positiveScale (leftScaleExponent 4 3 7)) •
      (rowColumnMul HexagonRowColumn437.rows_assocBCA HexagonRowColumn437.cols_left0)) ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4)) = (negativeScale (leftScaleExponent 4 3 7) • (left1Middle4 3 7)) ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal4_case_3_7_row_0_2_3 : (((-1 : ℤ) ^ (leftScaleBit 4 3 7).val * positiveScale (leftScaleExponent 4 3 7)) •
      (rowColumnMul HexagonRowColumn437.rows_assocBCA HexagonRowColumn437.cols_left0)) ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4)) = (negativeScale (leftScaleExponent 4 3 7) • (left1Middle4 3 7)) ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal4_case_3_7_row_0_3_0 : (((-1 : ℤ) ^ (leftScaleBit 4 3 7).val * positiveScale (leftScaleExponent 4 3 7)) •
      (rowColumnMul HexagonRowColumn437.rows_assocBCA HexagonRowColumn437.cols_left0)) ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4)) = (negativeScale (leftScaleExponent 4 3 7) • (left1Middle4 3 7)) ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal4_case_3_7_row_0_3_1 : (((-1 : ℤ) ^ (leftScaleBit 4 3 7).val * positiveScale (leftScaleExponent 4 3 7)) •
      (rowColumnMul HexagonRowColumn437.rows_assocBCA HexagonRowColumn437.cols_left0)) ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4)) = (negativeScale (leftScaleExponent 4 3 7) • (left1Middle4 3 7)) ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal4_case_3_7_row_0_3_2 : (((-1 : ℤ) ^ (leftScaleBit 4 3 7).val * positiveScale (leftScaleExponent 4 3 7)) •
      (rowColumnMul HexagonRowColumn437.rows_assocBCA HexagonRowColumn437.cols_left0)) ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4)) = (negativeScale (leftScaleExponent 4 3 7) • (left1Middle4 3 7)) ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal4_case_3_7_row_0_3_3 : (((-1 : ℤ) ^ (leftScaleBit 4 3 7).val * positiveScale (leftScaleExponent 4 3 7)) •
      (rowColumnMul HexagonRowColumn437.rows_assocBCA HexagonRowColumn437.cols_left0)) ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4)) = (negativeScale (leftScaleExponent 4 3 7) • (left1Middle4 3 7)) ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal4_case_3_7_checked : ((-1 : ℤ) ^ (leftScaleBit 4 3 7).val * positiveScale (leftScaleExponent 4 3 7)) •
      (rowColumnMul HexagonRowColumn437.rows_assocBCA HexagonRowColumn437.cols_left0) = negativeScale (leftScaleExponent 4 3 7) • (left1Middle4 3 7) := by
  funext r
  fin_cases r
  · exact leftFinal4_case_3_7_row_0_0_0
  · exact leftFinal4_case_3_7_row_0_0_1
  · exact leftFinal4_case_3_7_row_0_0_2
  · exact leftFinal4_case_3_7_row_0_0_3
  · exact leftFinal4_case_3_7_row_0_1_0
  · exact leftFinal4_case_3_7_row_0_1_1
  · exact leftFinal4_case_3_7_row_0_1_2
  · exact leftFinal4_case_3_7_row_0_1_3
  · exact leftFinal4_case_3_7_row_0_2_0
  · exact leftFinal4_case_3_7_row_0_2_1
  · exact leftFinal4_case_3_7_row_0_2_2
  · exact leftFinal4_case_3_7_row_0_2_3
  · exact leftFinal4_case_3_7_row_0_3_0
  · exact leftFinal4_case_3_7_row_0_3_1
  · exact leftFinal4_case_3_7_row_0_3_2
  · exact leftFinal4_case_3_7_row_0_3_3

set_option backward.isDefEq.respectTransparency false in
theorem leftFinal4_case_3_7 : ((-1 : ℤ) ^ (leftScaleBit 4 3 7).val * positiveScale (leftScaleExponent 4 3 7)) •
      (associatorZ 3 7 4 * left0Middle4 3 7) = negativeScale (leftScaleExponent 4 3 7) • (innerRightZ 3 4 7 * left1Middle4 3 7) := by
  simpa only [HexagonAtoms437.assocABC_eq,
    HexagonAtoms437.outerABC_eq,
    HexagonAtoms437.assocBAC_eq,
    HexagonAtoms437.innerABC_eq,
    HexagonAtoms437.innerRightABC_eq,
    HexagonAtoms437.inverseACB_eq,
    HexagonAtoms437.innerACB_eq,
    HexagonAtoms437.assocBCA_eq,
    HexagonAtoms437.innerRightBAC_eq,
    HexagonAtoms437.assocCAB_eq,
    HexagonAtoms437.outerLeftABC_eq,
    HexagonRowColumn437.product0_eq,
    HexagonRowColumn437.product1_eq,
    HexagonRowColumn437.product2_eq,
    HexagonRowColumn437.product3_eq,
    HexagonRowColumn437.product4_eq,
    HexagonRowColumn437.product5_eq,
    HexagonRowColumn437.product6_eq,
    HexagonRowColumn437.product7_eq] using leftFinal4_case_3_7_checked

private theorem rightFinal4_case_3_7_row_0_0_0 : (((-1 : ℤ) ^ (rightScaleBit 4 3 7).val * positiveScale (rightScaleExponent 4 3 7) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 7 3 : ℤ)) • HexagonAtoms437.outerLeftABC) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (negativeScale (rightScaleExponent 4 3 7) • (rowColumnMul HexagonRowColumn437.rows_assocCAB HexagonRowColumn437.cols_right2)) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal4_case_3_7_row_0_0_1 : (((-1 : ℤ) ^ (rightScaleBit 4 3 7).val * positiveScale (rightScaleExponent 4 3 7) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 7 3 : ℤ)) • HexagonAtoms437.outerLeftABC) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (negativeScale (rightScaleExponent 4 3 7) • (rowColumnMul HexagonRowColumn437.rows_assocCAB HexagonRowColumn437.cols_right2)) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal4_case_3_7_row_0_0_2 : (((-1 : ℤ) ^ (rightScaleBit 4 3 7).val * positiveScale (rightScaleExponent 4 3 7) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 7 3 : ℤ)) • HexagonAtoms437.outerLeftABC) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (negativeScale (rightScaleExponent 4 3 7) • (rowColumnMul HexagonRowColumn437.rows_assocCAB HexagonRowColumn437.cols_right2)) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal4_case_3_7_row_0_0_3 : (((-1 : ℤ) ^ (rightScaleBit 4 3 7).val * positiveScale (rightScaleExponent 4 3 7) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 7 3 : ℤ)) • HexagonAtoms437.outerLeftABC) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (negativeScale (rightScaleExponent 4 3 7) • (rowColumnMul HexagonRowColumn437.rows_assocCAB HexagonRowColumn437.cols_right2)) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal4_case_3_7_row_1_0_0 : (((-1 : ℤ) ^ (rightScaleBit 4 3 7).val * positiveScale (rightScaleExponent 4 3 7) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 7 3 : ℤ)) • HexagonAtoms437.outerLeftABC) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (negativeScale (rightScaleExponent 4 3 7) • (rowColumnMul HexagonRowColumn437.rows_assocCAB HexagonRowColumn437.cols_right2)) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal4_case_3_7_row_1_0_1 : (((-1 : ℤ) ^ (rightScaleBit 4 3 7).val * positiveScale (rightScaleExponent 4 3 7) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 7 3 : ℤ)) • HexagonAtoms437.outerLeftABC) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (negativeScale (rightScaleExponent 4 3 7) • (rowColumnMul HexagonRowColumn437.rows_assocCAB HexagonRowColumn437.cols_right2)) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal4_case_3_7_row_1_0_2 : (((-1 : ℤ) ^ (rightScaleBit 4 3 7).val * positiveScale (rightScaleExponent 4 3 7) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 7 3 : ℤ)) • HexagonAtoms437.outerLeftABC) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (negativeScale (rightScaleExponent 4 3 7) • (rowColumnMul HexagonRowColumn437.rows_assocCAB HexagonRowColumn437.cols_right2)) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal4_case_3_7_row_1_0_3 : (((-1 : ℤ) ^ (rightScaleBit 4 3 7).val * positiveScale (rightScaleExponent 4 3 7) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 7 3 : ℤ)) • HexagonAtoms437.outerLeftABC) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (negativeScale (rightScaleExponent 4 3 7) • (rowColumnMul HexagonRowColumn437.rows_assocCAB HexagonRowColumn437.cols_right2)) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal4_case_3_7_row_2_0_0 : (((-1 : ℤ) ^ (rightScaleBit 4 3 7).val * positiveScale (rightScaleExponent 4 3 7) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 7 3 : ℤ)) • HexagonAtoms437.outerLeftABC) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (negativeScale (rightScaleExponent 4 3 7) • (rowColumnMul HexagonRowColumn437.rows_assocCAB HexagonRowColumn437.cols_right2)) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal4_case_3_7_row_2_0_1 : (((-1 : ℤ) ^ (rightScaleBit 4 3 7).val * positiveScale (rightScaleExponent 4 3 7) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 7 3 : ℤ)) • HexagonAtoms437.outerLeftABC) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (negativeScale (rightScaleExponent 4 3 7) • (rowColumnMul HexagonRowColumn437.rows_assocCAB HexagonRowColumn437.cols_right2)) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal4_case_3_7_row_2_0_2 : (((-1 : ℤ) ^ (rightScaleBit 4 3 7).val * positiveScale (rightScaleExponent 4 3 7) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 7 3 : ℤ)) • HexagonAtoms437.outerLeftABC) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (negativeScale (rightScaleExponent 4 3 7) • (rowColumnMul HexagonRowColumn437.rows_assocCAB HexagonRowColumn437.cols_right2)) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal4_case_3_7_row_2_0_3 : (((-1 : ℤ) ^ (rightScaleBit 4 3 7).val * positiveScale (rightScaleExponent 4 3 7) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 7 3 : ℤ)) • HexagonAtoms437.outerLeftABC) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (negativeScale (rightScaleExponent 4 3 7) • (rowColumnMul HexagonRowColumn437.rows_assocCAB HexagonRowColumn437.cols_right2)) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal4_case_3_7_row_3_0_0 : (((-1 : ℤ) ^ (rightScaleBit 4 3 7).val * positiveScale (rightScaleExponent 4 3 7) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 7 3 : ℤ)) • HexagonAtoms437.outerLeftABC) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (negativeScale (rightScaleExponent 4 3 7) • (rowColumnMul HexagonRowColumn437.rows_assocCAB HexagonRowColumn437.cols_right2)) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal4_case_3_7_row_3_0_1 : (((-1 : ℤ) ^ (rightScaleBit 4 3 7).val * positiveScale (rightScaleExponent 4 3 7) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 7 3 : ℤ)) • HexagonAtoms437.outerLeftABC) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (negativeScale (rightScaleExponent 4 3 7) • (rowColumnMul HexagonRowColumn437.rows_assocCAB HexagonRowColumn437.cols_right2)) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal4_case_3_7_row_3_0_2 : (((-1 : ℤ) ^ (rightScaleBit 4 3 7).val * positiveScale (rightScaleExponent 4 3 7) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 7 3 : ℤ)) • HexagonAtoms437.outerLeftABC) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (negativeScale (rightScaleExponent 4 3 7) • (rowColumnMul HexagonRowColumn437.rows_assocCAB HexagonRowColumn437.cols_right2)) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal4_case_3_7_row_3_0_3 : (((-1 : ℤ) ^ (rightScaleBit 4 3 7).val * positiveScale (rightScaleExponent 4 3 7) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 7 3 : ℤ)) • HexagonAtoms437.outerLeftABC) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (negativeScale (rightScaleExponent 4 3 7) • (rowColumnMul HexagonRowColumn437.rows_assocCAB HexagonRowColumn437.cols_right2)) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal4_case_3_7_checked : ((-1 : ℤ) ^ (rightScaleBit 4 3 7).val * positiveScale (rightScaleExponent 4 3 7) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 7 3 : ℤ)) • HexagonAtoms437.outerLeftABC = negativeScale (rightScaleExponent 4 3 7) • (rowColumnMul HexagonRowColumn437.rows_assocCAB HexagonRowColumn437.cols_right2) := by
  funext r
  fin_cases r
  · exact rightFinal4_case_3_7_row_0_0_0
  · exact rightFinal4_case_3_7_row_0_0_1
  · exact rightFinal4_case_3_7_row_0_0_2
  · exact rightFinal4_case_3_7_row_0_0_3
  · exact rightFinal4_case_3_7_row_1_0_0
  · exact rightFinal4_case_3_7_row_1_0_1
  · exact rightFinal4_case_3_7_row_1_0_2
  · exact rightFinal4_case_3_7_row_1_0_3
  · exact rightFinal4_case_3_7_row_2_0_0
  · exact rightFinal4_case_3_7_row_2_0_1
  · exact rightFinal4_case_3_7_row_2_0_2
  · exact rightFinal4_case_3_7_row_2_0_3
  · exact rightFinal4_case_3_7_row_3_0_0
  · exact rightFinal4_case_3_7_row_3_0_1
  · exact rightFinal4_case_3_7_row_3_0_2
  · exact rightFinal4_case_3_7_row_3_0_3

set_option backward.isDefEq.respectTransparency false in
theorem rightFinal4_case_3_7 : ((-1 : ℤ) ^ (rightScaleBit 4 3 7).val * positiveScale (rightScaleExponent 4 3 7) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 7 3 : ℤ)) • outerLeftZ 4 3 7 = negativeScale (rightScaleExponent 4 3 7) • (associatorZ 7 4 3 * right2Middle4 3 7) := by
  simpa only [HexagonAtoms437.assocABC_eq,
    HexagonAtoms437.outerABC_eq,
    HexagonAtoms437.assocBAC_eq,
    HexagonAtoms437.innerABC_eq,
    HexagonAtoms437.innerRightABC_eq,
    HexagonAtoms437.inverseACB_eq,
    HexagonAtoms437.innerACB_eq,
    HexagonAtoms437.assocBCA_eq,
    HexagonAtoms437.innerRightBAC_eq,
    HexagonAtoms437.assocCAB_eq,
    HexagonAtoms437.outerLeftABC_eq,
    HexagonRowColumn437.product0_eq,
    HexagonRowColumn437.product1_eq,
    HexagonRowColumn437.product2_eq,
    HexagonRowColumn437.product3_eq,
    HexagonRowColumn437.product4_eq,
    HexagonRowColumn437.product5_eq,
    HexagonRowColumn437.product6_eq,
    HexagonRowColumn437.product7_eq] using rightFinal4_case_3_7_checked

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonCases4
