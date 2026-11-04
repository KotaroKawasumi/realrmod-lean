import RMod.BrundanEllis.StackingReferenceHexagonMiddle6
import RMod.BrundanEllis.StackingReferenceSparseMatrixCheck
import RMod.BrundanEllis.StackingReferenceHexagonAtoms631
import RMod.BrundanEllis.StackingReferenceHexagonRowColumn631

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

private theorem left0Middle6_eq_case_3_1_row_0_0_0 : (left0Middle6 3 1) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms631.assocABC) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_3_1_row_0_0_1 : (left0Middle6 3 1) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms631.assocABC) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_3_1_row_0_0_2 : (left0Middle6 3 1) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms631.assocABC) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_3_1_row_0_0_3 : (left0Middle6 3 1) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms631.assocABC) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_3_1_row_0_1_0 : (left0Middle6 3 1) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms631.assocABC) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_3_1_row_0_1_1 : (left0Middle6 3 1) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms631.assocABC) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_3_1_row_0_1_2 : (left0Middle6 3 1) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms631.assocABC) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_3_1_row_0_1_3 : (left0Middle6 3 1) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms631.assocABC) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_3_1_row_1_0_0 : (left0Middle6 3 1) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms631.assocABC) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_3_1_row_1_0_1 : (left0Middle6 3 1) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms631.assocABC) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_3_1_row_1_0_2 : (left0Middle6 3 1) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms631.assocABC) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_3_1_row_1_0_3 : (left0Middle6 3 1) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms631.assocABC) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_3_1_row_1_1_0 : (left0Middle6 3 1) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms631.assocABC) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_3_1_row_1_1_1 : (left0Middle6 3 1) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms631.assocABC) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_3_1_row_1_1_2 : (left0Middle6 3 1) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms631.assocABC) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_3_1_row_1_1_3 : (left0Middle6 3 1) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms631.assocABC) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left0Middle6_eq_case_3_1_checked : left0Middle6 3 1 = HexagonAtoms631.assocABC := by
  funext r
  fin_cases r
  · exact left0Middle6_eq_case_3_1_row_0_0_0
  · exact left0Middle6_eq_case_3_1_row_0_0_1
  · exact left0Middle6_eq_case_3_1_row_0_0_2
  · exact left0Middle6_eq_case_3_1_row_0_0_3
  · exact left0Middle6_eq_case_3_1_row_0_1_0
  · exact left0Middle6_eq_case_3_1_row_0_1_1
  · exact left0Middle6_eq_case_3_1_row_0_1_2
  · exact left0Middle6_eq_case_3_1_row_0_1_3
  · exact left0Middle6_eq_case_3_1_row_1_0_0
  · exact left0Middle6_eq_case_3_1_row_1_0_1
  · exact left0Middle6_eq_case_3_1_row_1_0_2
  · exact left0Middle6_eq_case_3_1_row_1_0_3
  · exact left0Middle6_eq_case_3_1_row_1_1_0
  · exact left0Middle6_eq_case_3_1_row_1_1_1
  · exact left0Middle6_eq_case_3_1_row_1_1_2
  · exact left0Middle6_eq_case_3_1_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem left0Middle6_eq_case_3_1 : left0Middle6 3 1 = outerRightZ 6 3 1 * associatorZ 6 3 1 := by
  simpa only [HexagonAtoms631.assocABC_eq,
    HexagonAtoms631.outerABC_eq,
    HexagonAtoms631.assocBAC_eq,
    HexagonAtoms631.innerABC_eq,
    HexagonAtoms631.innerRightABC_eq,
    HexagonAtoms631.inverseACB_eq,
    HexagonAtoms631.innerACB_eq,
    HexagonAtoms631.assocBCA_eq,
    HexagonAtoms631.innerRightBAC_eq,
    HexagonAtoms631.assocCAB_eq,
    HexagonAtoms631.outerLeftABC_eq,
    HexagonRowColumn631.product0_eq,
    HexagonRowColumn631.product1_eq,
    HexagonRowColumn631.product2_eq,
    HexagonRowColumn631.product3_eq,
    HexagonRowColumn631.product4_eq,
    HexagonRowColumn631.product5_eq,
    HexagonRowColumn631.product6_eq,
    HexagonRowColumn631.product7_eq] using left0Middle6_eq_case_3_1_checked

private theorem left1Middle6_eq_case_3_1_row_0_0_0 : (left1Middle6 3 1) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms631.assocBAC) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_3_1_row_0_0_1 : (left1Middle6 3 1) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms631.assocBAC) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_3_1_row_0_0_2 : (left1Middle6 3 1) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms631.assocBAC) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_3_1_row_0_0_3 : (left1Middle6 3 1) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms631.assocBAC) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_3_1_row_0_1_0 : (left1Middle6 3 1) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms631.assocBAC) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_3_1_row_0_1_1 : (left1Middle6 3 1) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms631.assocBAC) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_3_1_row_0_1_2 : (left1Middle6 3 1) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms631.assocBAC) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_3_1_row_0_1_3 : (left1Middle6 3 1) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms631.assocBAC) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_3_1_row_1_0_0 : (left1Middle6 3 1) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms631.assocBAC) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_3_1_row_1_0_1 : (left1Middle6 3 1) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms631.assocBAC) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_3_1_row_1_0_2 : (left1Middle6 3 1) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms631.assocBAC) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_3_1_row_1_0_3 : (left1Middle6 3 1) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms631.assocBAC) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_3_1_row_1_1_0 : (left1Middle6 3 1) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms631.assocBAC) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_3_1_row_1_1_1 : (left1Middle6 3 1) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms631.assocBAC) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_3_1_row_1_1_2 : (left1Middle6 3 1) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms631.assocBAC) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_3_1_row_1_1_3 : (left1Middle6 3 1) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms631.assocBAC) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem left1Middle6_eq_case_3_1_checked : left1Middle6 3 1 = HexagonAtoms631.assocBAC := by
  funext r
  fin_cases r
  · exact left1Middle6_eq_case_3_1_row_0_0_0
  · exact left1Middle6_eq_case_3_1_row_0_0_1
  · exact left1Middle6_eq_case_3_1_row_0_0_2
  · exact left1Middle6_eq_case_3_1_row_0_0_3
  · exact left1Middle6_eq_case_3_1_row_0_1_0
  · exact left1Middle6_eq_case_3_1_row_0_1_1
  · exact left1Middle6_eq_case_3_1_row_0_1_2
  · exact left1Middle6_eq_case_3_1_row_0_1_3
  · exact left1Middle6_eq_case_3_1_row_1_0_0
  · exact left1Middle6_eq_case_3_1_row_1_0_1
  · exact left1Middle6_eq_case_3_1_row_1_0_2
  · exact left1Middle6_eq_case_3_1_row_1_0_3
  · exact left1Middle6_eq_case_3_1_row_1_1_0
  · exact left1Middle6_eq_case_3_1_row_1_1_1
  · exact left1Middle6_eq_case_3_1_row_1_1_2
  · exact left1Middle6_eq_case_3_1_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem left1Middle6_eq_case_3_1 : left1Middle6 3 1 = associatorZ 3 6 1 * innerLeftZ 6 3 1 := by
  simpa only [HexagonAtoms631.assocABC_eq,
    HexagonAtoms631.outerABC_eq,
    HexagonAtoms631.assocBAC_eq,
    HexagonAtoms631.innerABC_eq,
    HexagonAtoms631.innerRightABC_eq,
    HexagonAtoms631.inverseACB_eq,
    HexagonAtoms631.innerACB_eq,
    HexagonAtoms631.assocBCA_eq,
    HexagonAtoms631.innerRightBAC_eq,
    HexagonAtoms631.assocCAB_eq,
    HexagonAtoms631.outerLeftABC_eq,
    HexagonRowColumn631.product0_eq,
    HexagonRowColumn631.product1_eq,
    HexagonRowColumn631.product2_eq,
    HexagonRowColumn631.product3_eq,
    HexagonRowColumn631.product4_eq,
    HexagonRowColumn631.product5_eq,
    HexagonRowColumn631.product6_eq,
    HexagonRowColumn631.product7_eq] using left1Middle6_eq_case_3_1_checked

private theorem right0Middle6_eq_case_3_1_row_0_0_0 : (right0Middle6 3 1) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms631.assocABC) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_3_1_row_0_0_1 : (right0Middle6 3 1) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms631.assocABC) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_3_1_row_0_0_2 : (right0Middle6 3 1) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms631.assocABC) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_3_1_row_0_0_3 : (right0Middle6 3 1) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms631.assocABC) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_3_1_row_0_1_0 : (right0Middle6 3 1) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms631.assocABC) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_3_1_row_0_1_1 : (right0Middle6 3 1) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms631.assocABC) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_3_1_row_0_1_2 : (right0Middle6 3 1) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms631.assocABC) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_3_1_row_0_1_3 : (right0Middle6 3 1) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms631.assocABC) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_3_1_row_1_0_0 : (right0Middle6 3 1) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms631.assocABC) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_3_1_row_1_0_1 : (right0Middle6 3 1) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms631.assocABC) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_3_1_row_1_0_2 : (right0Middle6 3 1) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms631.assocABC) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_3_1_row_1_0_3 : (right0Middle6 3 1) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms631.assocABC) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_3_1_row_1_1_0 : (right0Middle6 3 1) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms631.assocABC) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_3_1_row_1_1_1 : (right0Middle6 3 1) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms631.assocABC) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_3_1_row_1_1_2 : (right0Middle6 3 1) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms631.assocABC) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_3_1_row_1_1_3 : (right0Middle6 3 1) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms631.assocABC) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right0Middle6_eq_case_3_1_checked : right0Middle6 3 1 = HexagonAtoms631.assocABC := by
  funext r
  fin_cases r
  · exact right0Middle6_eq_case_3_1_row_0_0_0
  · exact right0Middle6_eq_case_3_1_row_0_0_1
  · exact right0Middle6_eq_case_3_1_row_0_0_2
  · exact right0Middle6_eq_case_3_1_row_0_0_3
  · exact right0Middle6_eq_case_3_1_row_0_1_0
  · exact right0Middle6_eq_case_3_1_row_0_1_1
  · exact right0Middle6_eq_case_3_1_row_0_1_2
  · exact right0Middle6_eq_case_3_1_row_0_1_3
  · exact right0Middle6_eq_case_3_1_row_1_0_0
  · exact right0Middle6_eq_case_3_1_row_1_0_1
  · exact right0Middle6_eq_case_3_1_row_1_0_2
  · exact right0Middle6_eq_case_3_1_row_1_0_3
  · exact right0Middle6_eq_case_3_1_row_1_1_0
  · exact right0Middle6_eq_case_3_1_row_1_1_1
  · exact right0Middle6_eq_case_3_1_row_1_1_2
  · exact right0Middle6_eq_case_3_1_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem right0Middle6_eq_case_3_1 : right0Middle6 3 1 = innerRightZ 6 3 1 * associatorZ 6 3 1 := by
  simpa only [HexagonAtoms631.assocABC_eq,
    HexagonAtoms631.outerABC_eq,
    HexagonAtoms631.assocBAC_eq,
    HexagonAtoms631.innerABC_eq,
    HexagonAtoms631.innerRightABC_eq,
    HexagonAtoms631.inverseACB_eq,
    HexagonAtoms631.innerACB_eq,
    HexagonAtoms631.assocBCA_eq,
    HexagonAtoms631.innerRightBAC_eq,
    HexagonAtoms631.assocCAB_eq,
    HexagonAtoms631.outerLeftABC_eq,
    HexagonRowColumn631.product0_eq,
    HexagonRowColumn631.product1_eq,
    HexagonRowColumn631.product2_eq,
    HexagonRowColumn631.product3_eq,
    HexagonRowColumn631.product4_eq,
    HexagonRowColumn631.product5_eq,
    HexagonRowColumn631.product6_eq,
    HexagonRowColumn631.product7_eq] using right0Middle6_eq_case_3_1_checked

private theorem right1Middle6_eq_case_3_1_row_0_0_0 : (right1Middle6 3 1) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn631.rows_inverseACB HexagonRowColumn631.cols_right0) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_3_1_row_0_0_1 : (right1Middle6 3 1) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn631.rows_inverseACB HexagonRowColumn631.cols_right0) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_3_1_row_0_0_2 : (right1Middle6 3 1) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn631.rows_inverseACB HexagonRowColumn631.cols_right0) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_3_1_row_0_0_3 : (right1Middle6 3 1) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn631.rows_inverseACB HexagonRowColumn631.cols_right0) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_3_1_row_0_1_0 : (right1Middle6 3 1) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn631.rows_inverseACB HexagonRowColumn631.cols_right0) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_3_1_row_0_1_1 : (right1Middle6 3 1) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn631.rows_inverseACB HexagonRowColumn631.cols_right0) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_3_1_row_0_1_2 : (right1Middle6 3 1) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn631.rows_inverseACB HexagonRowColumn631.cols_right0) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_3_1_row_0_1_3 : (right1Middle6 3 1) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn631.rows_inverseACB HexagonRowColumn631.cols_right0) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_3_1_row_1_0_0 : (right1Middle6 3 1) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn631.rows_inverseACB HexagonRowColumn631.cols_right0) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_3_1_row_1_0_1 : (right1Middle6 3 1) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn631.rows_inverseACB HexagonRowColumn631.cols_right0) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_3_1_row_1_0_2 : (right1Middle6 3 1) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn631.rows_inverseACB HexagonRowColumn631.cols_right0) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_3_1_row_1_0_3 : (right1Middle6 3 1) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn631.rows_inverseACB HexagonRowColumn631.cols_right0) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_3_1_row_1_1_0 : (right1Middle6 3 1) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn631.rows_inverseACB HexagonRowColumn631.cols_right0) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_3_1_row_1_1_1 : (right1Middle6 3 1) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn631.rows_inverseACB HexagonRowColumn631.cols_right0) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_3_1_row_1_1_2 : (right1Middle6 3 1) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn631.rows_inverseACB HexagonRowColumn631.cols_right0) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_3_1_row_1_1_3 : (right1Middle6 3 1) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn631.rows_inverseACB HexagonRowColumn631.cols_right0) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right1Middle6_eq_case_3_1_checked : right1Middle6 3 1 = rowColumnMul HexagonRowColumn631.rows_inverseACB HexagonRowColumn631.cols_right0 := by
  funext r
  fin_cases r
  · exact right1Middle6_eq_case_3_1_row_0_0_0
  · exact right1Middle6_eq_case_3_1_row_0_0_1
  · exact right1Middle6_eq_case_3_1_row_0_0_2
  · exact right1Middle6_eq_case_3_1_row_0_0_3
  · exact right1Middle6_eq_case_3_1_row_0_1_0
  · exact right1Middle6_eq_case_3_1_row_0_1_1
  · exact right1Middle6_eq_case_3_1_row_0_1_2
  · exact right1Middle6_eq_case_3_1_row_0_1_3
  · exact right1Middle6_eq_case_3_1_row_1_0_0
  · exact right1Middle6_eq_case_3_1_row_1_0_1
  · exact right1Middle6_eq_case_3_1_row_1_0_2
  · exact right1Middle6_eq_case_3_1_row_1_0_3
  · exact right1Middle6_eq_case_3_1_row_1_1_0
  · exact right1Middle6_eq_case_3_1_row_1_1_1
  · exact right1Middle6_eq_case_3_1_row_1_1_2
  · exact right1Middle6_eq_case_3_1_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem right1Middle6_eq_case_3_1 : right1Middle6 3 1 = associatorInverseZ 6 1 3 * right0Middle6 3 1 := by
  simpa only [HexagonAtoms631.assocABC_eq,
    HexagonAtoms631.outerABC_eq,
    HexagonAtoms631.assocBAC_eq,
    HexagonAtoms631.innerABC_eq,
    HexagonAtoms631.innerRightABC_eq,
    HexagonAtoms631.inverseACB_eq,
    HexagonAtoms631.innerACB_eq,
    HexagonAtoms631.assocBCA_eq,
    HexagonAtoms631.innerRightBAC_eq,
    HexagonAtoms631.assocCAB_eq,
    HexagonAtoms631.outerLeftABC_eq,
    HexagonRowColumn631.product0_eq,
    HexagonRowColumn631.product1_eq,
    HexagonRowColumn631.product2_eq,
    HexagonRowColumn631.product3_eq,
    HexagonRowColumn631.product4_eq,
    HexagonRowColumn631.product5_eq,
    HexagonRowColumn631.product6_eq,
    HexagonRowColumn631.product7_eq] using right1Middle6_eq_case_3_1_checked

private theorem right2Middle6_eq_case_3_1_row_0_0_0 : (right2Middle6 3 1) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (right1Middle6 3 1) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_3_1_row_0_0_1 : (right2Middle6 3 1) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (right1Middle6 3 1) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_3_1_row_0_0_2 : (right2Middle6 3 1) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (right1Middle6 3 1) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_3_1_row_0_0_3 : (right2Middle6 3 1) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (right1Middle6 3 1) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_3_1_row_0_1_0 : (right2Middle6 3 1) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (right1Middle6 3 1) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_3_1_row_0_1_1 : (right2Middle6 3 1) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (right1Middle6 3 1) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_3_1_row_0_1_2 : (right2Middle6 3 1) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (right1Middle6 3 1) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_3_1_row_0_1_3 : (right2Middle6 3 1) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (right1Middle6 3 1) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_3_1_row_1_0_0 : (right2Middle6 3 1) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (right1Middle6 3 1) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_3_1_row_1_0_1 : (right2Middle6 3 1) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (right1Middle6 3 1) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_3_1_row_1_0_2 : (right2Middle6 3 1) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (right1Middle6 3 1) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_3_1_row_1_0_3 : (right2Middle6 3 1) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (right1Middle6 3 1) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_3_1_row_1_1_0 : (right2Middle6 3 1) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (right1Middle6 3 1) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_3_1_row_1_1_1 : (right2Middle6 3 1) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (right1Middle6 3 1) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_3_1_row_1_1_2 : (right2Middle6 3 1) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (right1Middle6 3 1) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_3_1_row_1_1_3 : (right2Middle6 3 1) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (right1Middle6 3 1) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem right2Middle6_eq_case_3_1_checked : right2Middle6 3 1 = right1Middle6 3 1 := by
  funext r
  fin_cases r
  · exact right2Middle6_eq_case_3_1_row_0_0_0
  · exact right2Middle6_eq_case_3_1_row_0_0_1
  · exact right2Middle6_eq_case_3_1_row_0_0_2
  · exact right2Middle6_eq_case_3_1_row_0_0_3
  · exact right2Middle6_eq_case_3_1_row_0_1_0
  · exact right2Middle6_eq_case_3_1_row_0_1_1
  · exact right2Middle6_eq_case_3_1_row_0_1_2
  · exact right2Middle6_eq_case_3_1_row_0_1_3
  · exact right2Middle6_eq_case_3_1_row_1_0_0
  · exact right2Middle6_eq_case_3_1_row_1_0_1
  · exact right2Middle6_eq_case_3_1_row_1_0_2
  · exact right2Middle6_eq_case_3_1_row_1_0_3
  · exact right2Middle6_eq_case_3_1_row_1_1_0
  · exact right2Middle6_eq_case_3_1_row_1_1_1
  · exact right2Middle6_eq_case_3_1_row_1_1_2
  · exact right2Middle6_eq_case_3_1_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem right2Middle6_eq_case_3_1 : right2Middle6 3 1 = innerLeftZ 6 1 3 * right1Middle6 3 1 := by
  simpa only [HexagonAtoms631.assocABC_eq,
    HexagonAtoms631.outerABC_eq,
    HexagonAtoms631.assocBAC_eq,
    HexagonAtoms631.innerABC_eq,
    HexagonAtoms631.innerRightABC_eq,
    HexagonAtoms631.inverseACB_eq,
    HexagonAtoms631.innerACB_eq,
    HexagonAtoms631.assocBCA_eq,
    HexagonAtoms631.innerRightBAC_eq,
    HexagonAtoms631.assocCAB_eq,
    HexagonAtoms631.outerLeftABC_eq,
    HexagonRowColumn631.product0_eq,
    HexagonRowColumn631.product1_eq,
    HexagonRowColumn631.product2_eq,
    HexagonRowColumn631.product3_eq,
    HexagonRowColumn631.product4_eq,
    HexagonRowColumn631.product5_eq,
    HexagonRowColumn631.product6_eq,
    HexagonRowColumn631.product7_eq] using right2Middle6_eq_case_3_1_checked

private theorem leftFinal6_case_3_1_row_0_0_0 : (((-1 : ℤ) ^ (leftScaleBit 6 3 1).val * positiveScale (leftScaleExponent 6 3 1)) •
      (rowColumnMul HexagonRowColumn631.rows_assocBCA HexagonRowColumn631.cols_left0)) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 6 3 1) • (left1Middle6 3 1)) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal6_case_3_1_row_0_0_1 : (((-1 : ℤ) ^ (leftScaleBit 6 3 1).val * positiveScale (leftScaleExponent 6 3 1)) •
      (rowColumnMul HexagonRowColumn631.rows_assocBCA HexagonRowColumn631.cols_left0)) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 6 3 1) • (left1Middle6 3 1)) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal6_case_3_1_row_0_0_2 : (((-1 : ℤ) ^ (leftScaleBit 6 3 1).val * positiveScale (leftScaleExponent 6 3 1)) •
      (rowColumnMul HexagonRowColumn631.rows_assocBCA HexagonRowColumn631.cols_left0)) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 6 3 1) • (left1Middle6 3 1)) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal6_case_3_1_row_0_0_3 : (((-1 : ℤ) ^ (leftScaleBit 6 3 1).val * positiveScale (leftScaleExponent 6 3 1)) •
      (rowColumnMul HexagonRowColumn631.rows_assocBCA HexagonRowColumn631.cols_left0)) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 6 3 1) • (left1Middle6 3 1)) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal6_case_3_1_row_0_1_0 : (((-1 : ℤ) ^ (leftScaleBit 6 3 1).val * positiveScale (leftScaleExponent 6 3 1)) •
      (rowColumnMul HexagonRowColumn631.rows_assocBCA HexagonRowColumn631.cols_left0)) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 6 3 1) • (left1Middle6 3 1)) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal6_case_3_1_row_0_1_1 : (((-1 : ℤ) ^ (leftScaleBit 6 3 1).val * positiveScale (leftScaleExponent 6 3 1)) •
      (rowColumnMul HexagonRowColumn631.rows_assocBCA HexagonRowColumn631.cols_left0)) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 6 3 1) • (left1Middle6 3 1)) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal6_case_3_1_row_0_1_2 : (((-1 : ℤ) ^ (leftScaleBit 6 3 1).val * positiveScale (leftScaleExponent 6 3 1)) •
      (rowColumnMul HexagonRowColumn631.rows_assocBCA HexagonRowColumn631.cols_left0)) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 6 3 1) • (left1Middle6 3 1)) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal6_case_3_1_row_0_1_3 : (((-1 : ℤ) ^ (leftScaleBit 6 3 1).val * positiveScale (leftScaleExponent 6 3 1)) •
      (rowColumnMul HexagonRowColumn631.rows_assocBCA HexagonRowColumn631.cols_left0)) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 6 3 1) • (left1Middle6 3 1)) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal6_case_3_1_row_1_0_0 : (((-1 : ℤ) ^ (leftScaleBit 6 3 1).val * positiveScale (leftScaleExponent 6 3 1)) •
      (rowColumnMul HexagonRowColumn631.rows_assocBCA HexagonRowColumn631.cols_left0)) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 6 3 1) • (left1Middle6 3 1)) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal6_case_3_1_row_1_0_1 : (((-1 : ℤ) ^ (leftScaleBit 6 3 1).val * positiveScale (leftScaleExponent 6 3 1)) •
      (rowColumnMul HexagonRowColumn631.rows_assocBCA HexagonRowColumn631.cols_left0)) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 6 3 1) • (left1Middle6 3 1)) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal6_case_3_1_row_1_0_2 : (((-1 : ℤ) ^ (leftScaleBit 6 3 1).val * positiveScale (leftScaleExponent 6 3 1)) •
      (rowColumnMul HexagonRowColumn631.rows_assocBCA HexagonRowColumn631.cols_left0)) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 6 3 1) • (left1Middle6 3 1)) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal6_case_3_1_row_1_0_3 : (((-1 : ℤ) ^ (leftScaleBit 6 3 1).val * positiveScale (leftScaleExponent 6 3 1)) •
      (rowColumnMul HexagonRowColumn631.rows_assocBCA HexagonRowColumn631.cols_left0)) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 6 3 1) • (left1Middle6 3 1)) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal6_case_3_1_row_1_1_0 : (((-1 : ℤ) ^ (leftScaleBit 6 3 1).val * positiveScale (leftScaleExponent 6 3 1)) •
      (rowColumnMul HexagonRowColumn631.rows_assocBCA HexagonRowColumn631.cols_left0)) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 6 3 1) • (left1Middle6 3 1)) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal6_case_3_1_row_1_1_1 : (((-1 : ℤ) ^ (leftScaleBit 6 3 1).val * positiveScale (leftScaleExponent 6 3 1)) •
      (rowColumnMul HexagonRowColumn631.rows_assocBCA HexagonRowColumn631.cols_left0)) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 6 3 1) • (left1Middle6 3 1)) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal6_case_3_1_row_1_1_2 : (((-1 : ℤ) ^ (leftScaleBit 6 3 1).val * positiveScale (leftScaleExponent 6 3 1)) •
      (rowColumnMul HexagonRowColumn631.rows_assocBCA HexagonRowColumn631.cols_left0)) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 6 3 1) • (left1Middle6 3 1)) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal6_case_3_1_row_1_1_3 : (((-1 : ℤ) ^ (leftScaleBit 6 3 1).val * positiveScale (leftScaleExponent 6 3 1)) •
      (rowColumnMul HexagonRowColumn631.rows_assocBCA HexagonRowColumn631.cols_left0)) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 6 3 1) • (left1Middle6 3 1)) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem leftFinal6_case_3_1_checked : ((-1 : ℤ) ^ (leftScaleBit 6 3 1).val * positiveScale (leftScaleExponent 6 3 1)) •
      (rowColumnMul HexagonRowColumn631.rows_assocBCA HexagonRowColumn631.cols_left0) = negativeScale (leftScaleExponent 6 3 1) • (left1Middle6 3 1) := by
  funext r
  fin_cases r
  · exact leftFinal6_case_3_1_row_0_0_0
  · exact leftFinal6_case_3_1_row_0_0_1
  · exact leftFinal6_case_3_1_row_0_0_2
  · exact leftFinal6_case_3_1_row_0_0_3
  · exact leftFinal6_case_3_1_row_0_1_0
  · exact leftFinal6_case_3_1_row_0_1_1
  · exact leftFinal6_case_3_1_row_0_1_2
  · exact leftFinal6_case_3_1_row_0_1_3
  · exact leftFinal6_case_3_1_row_1_0_0
  · exact leftFinal6_case_3_1_row_1_0_1
  · exact leftFinal6_case_3_1_row_1_0_2
  · exact leftFinal6_case_3_1_row_1_0_3
  · exact leftFinal6_case_3_1_row_1_1_0
  · exact leftFinal6_case_3_1_row_1_1_1
  · exact leftFinal6_case_3_1_row_1_1_2
  · exact leftFinal6_case_3_1_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem leftFinal6_case_3_1 : ((-1 : ℤ) ^ (leftScaleBit 6 3 1).val * positiveScale (leftScaleExponent 6 3 1)) •
      (associatorZ 3 1 6 * left0Middle6 3 1) = negativeScale (leftScaleExponent 6 3 1) • (innerRightZ 3 6 1 * left1Middle6 3 1) := by
  simpa only [HexagonAtoms631.assocABC_eq,
    HexagonAtoms631.outerABC_eq,
    HexagonAtoms631.assocBAC_eq,
    HexagonAtoms631.innerABC_eq,
    HexagonAtoms631.innerRightABC_eq,
    HexagonAtoms631.inverseACB_eq,
    HexagonAtoms631.innerACB_eq,
    HexagonAtoms631.assocBCA_eq,
    HexagonAtoms631.innerRightBAC_eq,
    HexagonAtoms631.assocCAB_eq,
    HexagonAtoms631.outerLeftABC_eq,
    HexagonRowColumn631.product0_eq,
    HexagonRowColumn631.product1_eq,
    HexagonRowColumn631.product2_eq,
    HexagonRowColumn631.product3_eq,
    HexagonRowColumn631.product4_eq,
    HexagonRowColumn631.product5_eq,
    HexagonRowColumn631.product6_eq,
    HexagonRowColumn631.product7_eq] using leftFinal6_case_3_1_checked

private theorem rightFinal6_case_3_1_row_0_0_0 : (((-1 : ℤ) ^ (rightScaleBit 6 3 1).val * positiveScale (rightScaleExponent 6 3 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 1 3 : ℤ)) • HexagonAtoms631.outerLeftABC) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (negativeScale (rightScaleExponent 6 3 1) • (rowColumnMul HexagonRowColumn631.rows_assocCAB HexagonRowColumn631.cols_right2)) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal6_case_3_1_row_0_0_1 : (((-1 : ℤ) ^ (rightScaleBit 6 3 1).val * positiveScale (rightScaleExponent 6 3 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 1 3 : ℤ)) • HexagonAtoms631.outerLeftABC) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (negativeScale (rightScaleExponent 6 3 1) • (rowColumnMul HexagonRowColumn631.rows_assocCAB HexagonRowColumn631.cols_right2)) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal6_case_3_1_row_0_0_2 : (((-1 : ℤ) ^ (rightScaleBit 6 3 1).val * positiveScale (rightScaleExponent 6 3 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 1 3 : ℤ)) • HexagonAtoms631.outerLeftABC) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (negativeScale (rightScaleExponent 6 3 1) • (rowColumnMul HexagonRowColumn631.rows_assocCAB HexagonRowColumn631.cols_right2)) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal6_case_3_1_row_0_0_3 : (((-1 : ℤ) ^ (rightScaleBit 6 3 1).val * positiveScale (rightScaleExponent 6 3 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 1 3 : ℤ)) • HexagonAtoms631.outerLeftABC) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (negativeScale (rightScaleExponent 6 3 1) • (rowColumnMul HexagonRowColumn631.rows_assocCAB HexagonRowColumn631.cols_right2)) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal6_case_3_1_row_1_0_0 : (((-1 : ℤ) ^ (rightScaleBit 6 3 1).val * positiveScale (rightScaleExponent 6 3 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 1 3 : ℤ)) • HexagonAtoms631.outerLeftABC) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (negativeScale (rightScaleExponent 6 3 1) • (rowColumnMul HexagonRowColumn631.rows_assocCAB HexagonRowColumn631.cols_right2)) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal6_case_3_1_row_1_0_1 : (((-1 : ℤ) ^ (rightScaleBit 6 3 1).val * positiveScale (rightScaleExponent 6 3 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 1 3 : ℤ)) • HexagonAtoms631.outerLeftABC) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (negativeScale (rightScaleExponent 6 3 1) • (rowColumnMul HexagonRowColumn631.rows_assocCAB HexagonRowColumn631.cols_right2)) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal6_case_3_1_row_1_0_2 : (((-1 : ℤ) ^ (rightScaleBit 6 3 1).val * positiveScale (rightScaleExponent 6 3 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 1 3 : ℤ)) • HexagonAtoms631.outerLeftABC) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (negativeScale (rightScaleExponent 6 3 1) • (rowColumnMul HexagonRowColumn631.rows_assocCAB HexagonRowColumn631.cols_right2)) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal6_case_3_1_row_1_0_3 : (((-1 : ℤ) ^ (rightScaleBit 6 3 1).val * positiveScale (rightScaleExponent 6 3 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 1 3 : ℤ)) • HexagonAtoms631.outerLeftABC) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (negativeScale (rightScaleExponent 6 3 1) • (rowColumnMul HexagonRowColumn631.rows_assocCAB HexagonRowColumn631.cols_right2)) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal6_case_3_1_row_2_0_0 : (((-1 : ℤ) ^ (rightScaleBit 6 3 1).val * positiveScale (rightScaleExponent 6 3 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 1 3 : ℤ)) • HexagonAtoms631.outerLeftABC) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (negativeScale (rightScaleExponent 6 3 1) • (rowColumnMul HexagonRowColumn631.rows_assocCAB HexagonRowColumn631.cols_right2)) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal6_case_3_1_row_2_0_1 : (((-1 : ℤ) ^ (rightScaleBit 6 3 1).val * positiveScale (rightScaleExponent 6 3 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 1 3 : ℤ)) • HexagonAtoms631.outerLeftABC) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (negativeScale (rightScaleExponent 6 3 1) • (rowColumnMul HexagonRowColumn631.rows_assocCAB HexagonRowColumn631.cols_right2)) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal6_case_3_1_row_2_0_2 : (((-1 : ℤ) ^ (rightScaleBit 6 3 1).val * positiveScale (rightScaleExponent 6 3 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 1 3 : ℤ)) • HexagonAtoms631.outerLeftABC) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (negativeScale (rightScaleExponent 6 3 1) • (rowColumnMul HexagonRowColumn631.rows_assocCAB HexagonRowColumn631.cols_right2)) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal6_case_3_1_row_2_0_3 : (((-1 : ℤ) ^ (rightScaleBit 6 3 1).val * positiveScale (rightScaleExponent 6 3 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 1 3 : ℤ)) • HexagonAtoms631.outerLeftABC) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (negativeScale (rightScaleExponent 6 3 1) • (rowColumnMul HexagonRowColumn631.rows_assocCAB HexagonRowColumn631.cols_right2)) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal6_case_3_1_row_3_0_0 : (((-1 : ℤ) ^ (rightScaleBit 6 3 1).val * positiveScale (rightScaleExponent 6 3 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 1 3 : ℤ)) • HexagonAtoms631.outerLeftABC) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (negativeScale (rightScaleExponent 6 3 1) • (rowColumnMul HexagonRowColumn631.rows_assocCAB HexagonRowColumn631.cols_right2)) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal6_case_3_1_row_3_0_1 : (((-1 : ℤ) ^ (rightScaleBit 6 3 1).val * positiveScale (rightScaleExponent 6 3 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 1 3 : ℤ)) • HexagonAtoms631.outerLeftABC) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (negativeScale (rightScaleExponent 6 3 1) • (rowColumnMul HexagonRowColumn631.rows_assocCAB HexagonRowColumn631.cols_right2)) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal6_case_3_1_row_3_0_2 : (((-1 : ℤ) ^ (rightScaleBit 6 3 1).val * positiveScale (rightScaleExponent 6 3 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 1 3 : ℤ)) • HexagonAtoms631.outerLeftABC) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (negativeScale (rightScaleExponent 6 3 1) • (rowColumnMul HexagonRowColumn631.rows_assocCAB HexagonRowColumn631.cols_right2)) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal6_case_3_1_row_3_0_3 : (((-1 : ℤ) ^ (rightScaleBit 6 3 1).val * positiveScale (rightScaleExponent 6 3 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 1 3 : ℤ)) • HexagonAtoms631.outerLeftABC) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (negativeScale (rightScaleExponent 6 3 1) • (rowColumnMul HexagonRowColumn631.rows_assocCAB HexagonRowColumn631.cols_right2)) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 1) (c := 4)
  decide +kernel

private theorem rightFinal6_case_3_1_checked : ((-1 : ℤ) ^ (rightScaleBit 6 3 1).val * positiveScale (rightScaleExponent 6 3 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 1 3 : ℤ)) • HexagonAtoms631.outerLeftABC = negativeScale (rightScaleExponent 6 3 1) • (rowColumnMul HexagonRowColumn631.rows_assocCAB HexagonRowColumn631.cols_right2) := by
  funext r
  fin_cases r
  · exact rightFinal6_case_3_1_row_0_0_0
  · exact rightFinal6_case_3_1_row_0_0_1
  · exact rightFinal6_case_3_1_row_0_0_2
  · exact rightFinal6_case_3_1_row_0_0_3
  · exact rightFinal6_case_3_1_row_1_0_0
  · exact rightFinal6_case_3_1_row_1_0_1
  · exact rightFinal6_case_3_1_row_1_0_2
  · exact rightFinal6_case_3_1_row_1_0_3
  · exact rightFinal6_case_3_1_row_2_0_0
  · exact rightFinal6_case_3_1_row_2_0_1
  · exact rightFinal6_case_3_1_row_2_0_2
  · exact rightFinal6_case_3_1_row_2_0_3
  · exact rightFinal6_case_3_1_row_3_0_0
  · exact rightFinal6_case_3_1_row_3_0_1
  · exact rightFinal6_case_3_1_row_3_0_2
  · exact rightFinal6_case_3_1_row_3_0_3

set_option backward.isDefEq.respectTransparency false in
theorem rightFinal6_case_3_1 : ((-1 : ℤ) ^ (rightScaleBit 6 3 1).val * positiveScale (rightScaleExponent 6 3 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 1 3 : ℤ)) • outerLeftZ 6 3 1 = negativeScale (rightScaleExponent 6 3 1) • (associatorZ 1 6 3 * right2Middle6 3 1) := by
  simpa only [HexagonAtoms631.assocABC_eq,
    HexagonAtoms631.outerABC_eq,
    HexagonAtoms631.assocBAC_eq,
    HexagonAtoms631.innerABC_eq,
    HexagonAtoms631.innerRightABC_eq,
    HexagonAtoms631.inverseACB_eq,
    HexagonAtoms631.innerACB_eq,
    HexagonAtoms631.assocBCA_eq,
    HexagonAtoms631.innerRightBAC_eq,
    HexagonAtoms631.assocCAB_eq,
    HexagonAtoms631.outerLeftABC_eq,
    HexagonRowColumn631.product0_eq,
    HexagonRowColumn631.product1_eq,
    HexagonRowColumn631.product2_eq,
    HexagonRowColumn631.product3_eq,
    HexagonRowColumn631.product4_eq,
    HexagonRowColumn631.product5_eq,
    HexagonRowColumn631.product6_eq,
    HexagonRowColumn631.product7_eq] using rightFinal6_case_3_1_checked

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonCases6
