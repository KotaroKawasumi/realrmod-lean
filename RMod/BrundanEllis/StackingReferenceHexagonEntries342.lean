import RMod.BrundanEllis.StackingReferenceHexagonMiddle3
import RMod.BrundanEllis.StackingReferenceSparseMatrixCheck
import RMod.BrundanEllis.StackingReferenceHexagonAtoms342
import RMod.BrundanEllis.StackingReferenceHexagonRowColumn342

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

private theorem left0Middle3_eq_case_4_2_row_0_0_0 : (left0Middle3 4 2) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (HexagonAtoms342.assocABC) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left0Middle3_eq_case_4_2_row_0_0_1 : (left0Middle3 4 2) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (HexagonAtoms342.assocABC) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left0Middle3_eq_case_4_2_row_0_1_0 : (left0Middle3 4 2) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (HexagonAtoms342.assocABC) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left0Middle3_eq_case_4_2_row_0_1_1 : (left0Middle3 4 2) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (HexagonAtoms342.assocABC) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left0Middle3_eq_case_4_2_row_0_2_0 : (left0Middle3 4 2) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (HexagonAtoms342.assocABC) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left0Middle3_eq_case_4_2_row_0_2_1 : (left0Middle3 4 2) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (HexagonAtoms342.assocABC) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left0Middle3_eq_case_4_2_row_0_3_0 : (left0Middle3 4 2) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (HexagonAtoms342.assocABC) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left0Middle3_eq_case_4_2_row_0_3_1 : (left0Middle3 4 2) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (HexagonAtoms342.assocABC) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left0Middle3_eq_case_4_2_row_1_0_0 : (left0Middle3 4 2) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (HexagonAtoms342.assocABC) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left0Middle3_eq_case_4_2_row_1_0_1 : (left0Middle3 4 2) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (HexagonAtoms342.assocABC) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left0Middle3_eq_case_4_2_row_1_1_0 : (left0Middle3 4 2) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (HexagonAtoms342.assocABC) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left0Middle3_eq_case_4_2_row_1_1_1 : (left0Middle3 4 2) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (HexagonAtoms342.assocABC) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left0Middle3_eq_case_4_2_row_1_2_0 : (left0Middle3 4 2) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (HexagonAtoms342.assocABC) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left0Middle3_eq_case_4_2_row_1_2_1 : (left0Middle3 4 2) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (HexagonAtoms342.assocABC) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left0Middle3_eq_case_4_2_row_1_3_0 : (left0Middle3 4 2) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (HexagonAtoms342.assocABC) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left0Middle3_eq_case_4_2_row_1_3_1 : (left0Middle3 4 2) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (HexagonAtoms342.assocABC) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left0Middle3_eq_case_4_2_checked : left0Middle3 4 2 = HexagonAtoms342.assocABC := by
  funext r
  fin_cases r
  · exact left0Middle3_eq_case_4_2_row_0_0_0
  · exact left0Middle3_eq_case_4_2_row_0_0_1
  · exact left0Middle3_eq_case_4_2_row_0_1_0
  · exact left0Middle3_eq_case_4_2_row_0_1_1
  · exact left0Middle3_eq_case_4_2_row_0_2_0
  · exact left0Middle3_eq_case_4_2_row_0_2_1
  · exact left0Middle3_eq_case_4_2_row_0_3_0
  · exact left0Middle3_eq_case_4_2_row_0_3_1
  · exact left0Middle3_eq_case_4_2_row_1_0_0
  · exact left0Middle3_eq_case_4_2_row_1_0_1
  · exact left0Middle3_eq_case_4_2_row_1_1_0
  · exact left0Middle3_eq_case_4_2_row_1_1_1
  · exact left0Middle3_eq_case_4_2_row_1_2_0
  · exact left0Middle3_eq_case_4_2_row_1_2_1
  · exact left0Middle3_eq_case_4_2_row_1_3_0
  · exact left0Middle3_eq_case_4_2_row_1_3_1

set_option backward.isDefEq.respectTransparency false in
theorem left0Middle3_eq_case_4_2 : left0Middle3 4 2 = outerRightZ 3 4 2 * associatorZ 3 4 2 := by
  simpa only [HexagonAtoms342.assocABC_eq,
    HexagonAtoms342.outerABC_eq,
    HexagonAtoms342.assocBAC_eq,
    HexagonAtoms342.innerABC_eq,
    HexagonAtoms342.innerRightABC_eq,
    HexagonAtoms342.inverseACB_eq,
    HexagonAtoms342.innerACB_eq,
    HexagonAtoms342.assocBCA_eq,
    HexagonAtoms342.innerRightBAC_eq,
    HexagonAtoms342.assocCAB_eq,
    HexagonAtoms342.outerLeftABC_eq,
    HexagonRowColumn342.product0_eq,
    HexagonRowColumn342.product1_eq,
    HexagonRowColumn342.product2_eq,
    HexagonRowColumn342.product3_eq,
    HexagonRowColumn342.product4_eq,
    HexagonRowColumn342.product5_eq,
    HexagonRowColumn342.product6_eq,
    HexagonRowColumn342.product7_eq] using left0Middle3_eq_case_4_2_checked

private theorem left1Middle3_eq_case_4_2_row_0_0_0 : (left1Middle3 4 2) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (HexagonAtoms342.assocBAC) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left1Middle3_eq_case_4_2_row_0_0_1 : (left1Middle3 4 2) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (HexagonAtoms342.assocBAC) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left1Middle3_eq_case_4_2_row_0_1_0 : (left1Middle3 4 2) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (HexagonAtoms342.assocBAC) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left1Middle3_eq_case_4_2_row_0_1_1 : (left1Middle3 4 2) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (HexagonAtoms342.assocBAC) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left1Middle3_eq_case_4_2_row_0_2_0 : (left1Middle3 4 2) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (HexagonAtoms342.assocBAC) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left1Middle3_eq_case_4_2_row_0_2_1 : (left1Middle3 4 2) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (HexagonAtoms342.assocBAC) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left1Middle3_eq_case_4_2_row_0_3_0 : (left1Middle3 4 2) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (HexagonAtoms342.assocBAC) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left1Middle3_eq_case_4_2_row_0_3_1 : (left1Middle3 4 2) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (HexagonAtoms342.assocBAC) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left1Middle3_eq_case_4_2_row_1_0_0 : (left1Middle3 4 2) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (HexagonAtoms342.assocBAC) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left1Middle3_eq_case_4_2_row_1_0_1 : (left1Middle3 4 2) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (HexagonAtoms342.assocBAC) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left1Middle3_eq_case_4_2_row_1_1_0 : (left1Middle3 4 2) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (HexagonAtoms342.assocBAC) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left1Middle3_eq_case_4_2_row_1_1_1 : (left1Middle3 4 2) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (HexagonAtoms342.assocBAC) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left1Middle3_eq_case_4_2_row_1_2_0 : (left1Middle3 4 2) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (HexagonAtoms342.assocBAC) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left1Middle3_eq_case_4_2_row_1_2_1 : (left1Middle3 4 2) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (HexagonAtoms342.assocBAC) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left1Middle3_eq_case_4_2_row_1_3_0 : (left1Middle3 4 2) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (HexagonAtoms342.assocBAC) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left1Middle3_eq_case_4_2_row_1_3_1 : (left1Middle3 4 2) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (HexagonAtoms342.assocBAC) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left1Middle3_eq_case_4_2_checked : left1Middle3 4 2 = HexagonAtoms342.assocBAC := by
  funext r
  fin_cases r
  · exact left1Middle3_eq_case_4_2_row_0_0_0
  · exact left1Middle3_eq_case_4_2_row_0_0_1
  · exact left1Middle3_eq_case_4_2_row_0_1_0
  · exact left1Middle3_eq_case_4_2_row_0_1_1
  · exact left1Middle3_eq_case_4_2_row_0_2_0
  · exact left1Middle3_eq_case_4_2_row_0_2_1
  · exact left1Middle3_eq_case_4_2_row_0_3_0
  · exact left1Middle3_eq_case_4_2_row_0_3_1
  · exact left1Middle3_eq_case_4_2_row_1_0_0
  · exact left1Middle3_eq_case_4_2_row_1_0_1
  · exact left1Middle3_eq_case_4_2_row_1_1_0
  · exact left1Middle3_eq_case_4_2_row_1_1_1
  · exact left1Middle3_eq_case_4_2_row_1_2_0
  · exact left1Middle3_eq_case_4_2_row_1_2_1
  · exact left1Middle3_eq_case_4_2_row_1_3_0
  · exact left1Middle3_eq_case_4_2_row_1_3_1

set_option backward.isDefEq.respectTransparency false in
theorem left1Middle3_eq_case_4_2 : left1Middle3 4 2 = associatorZ 4 3 2 * innerLeftZ 3 4 2 := by
  simpa only [HexagonAtoms342.assocABC_eq,
    HexagonAtoms342.outerABC_eq,
    HexagonAtoms342.assocBAC_eq,
    HexagonAtoms342.innerABC_eq,
    HexagonAtoms342.innerRightABC_eq,
    HexagonAtoms342.inverseACB_eq,
    HexagonAtoms342.innerACB_eq,
    HexagonAtoms342.assocBCA_eq,
    HexagonAtoms342.innerRightBAC_eq,
    HexagonAtoms342.assocCAB_eq,
    HexagonAtoms342.outerLeftABC_eq,
    HexagonRowColumn342.product0_eq,
    HexagonRowColumn342.product1_eq,
    HexagonRowColumn342.product2_eq,
    HexagonRowColumn342.product3_eq,
    HexagonRowColumn342.product4_eq,
    HexagonRowColumn342.product5_eq,
    HexagonRowColumn342.product6_eq,
    HexagonRowColumn342.product7_eq] using left1Middle3_eq_case_4_2_checked

private theorem right0Middle3_eq_case_4_2_row_0_0_0 : (right0Middle3 4 2) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (HexagonAtoms342.assocABC) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right0Middle3_eq_case_4_2_row_0_0_1 : (right0Middle3 4 2) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (HexagonAtoms342.assocABC) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right0Middle3_eq_case_4_2_row_0_1_0 : (right0Middle3 4 2) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (HexagonAtoms342.assocABC) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right0Middle3_eq_case_4_2_row_0_1_1 : (right0Middle3 4 2) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (HexagonAtoms342.assocABC) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right0Middle3_eq_case_4_2_row_0_2_0 : (right0Middle3 4 2) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (HexagonAtoms342.assocABC) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right0Middle3_eq_case_4_2_row_0_2_1 : (right0Middle3 4 2) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (HexagonAtoms342.assocABC) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right0Middle3_eq_case_4_2_row_0_3_0 : (right0Middle3 4 2) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (HexagonAtoms342.assocABC) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right0Middle3_eq_case_4_2_row_0_3_1 : (right0Middle3 4 2) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (HexagonAtoms342.assocABC) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right0Middle3_eq_case_4_2_row_1_0_0 : (right0Middle3 4 2) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (HexagonAtoms342.assocABC) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right0Middle3_eq_case_4_2_row_1_0_1 : (right0Middle3 4 2) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (HexagonAtoms342.assocABC) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right0Middle3_eq_case_4_2_row_1_1_0 : (right0Middle3 4 2) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (HexagonAtoms342.assocABC) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right0Middle3_eq_case_4_2_row_1_1_1 : (right0Middle3 4 2) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (HexagonAtoms342.assocABC) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right0Middle3_eq_case_4_2_row_1_2_0 : (right0Middle3 4 2) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (HexagonAtoms342.assocABC) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right0Middle3_eq_case_4_2_row_1_2_1 : (right0Middle3 4 2) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (HexagonAtoms342.assocABC) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right0Middle3_eq_case_4_2_row_1_3_0 : (right0Middle3 4 2) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (HexagonAtoms342.assocABC) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right0Middle3_eq_case_4_2_row_1_3_1 : (right0Middle3 4 2) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (HexagonAtoms342.assocABC) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right0Middle3_eq_case_4_2_checked : right0Middle3 4 2 = HexagonAtoms342.assocABC := by
  funext r
  fin_cases r
  · exact right0Middle3_eq_case_4_2_row_0_0_0
  · exact right0Middle3_eq_case_4_2_row_0_0_1
  · exact right0Middle3_eq_case_4_2_row_0_1_0
  · exact right0Middle3_eq_case_4_2_row_0_1_1
  · exact right0Middle3_eq_case_4_2_row_0_2_0
  · exact right0Middle3_eq_case_4_2_row_0_2_1
  · exact right0Middle3_eq_case_4_2_row_0_3_0
  · exact right0Middle3_eq_case_4_2_row_0_3_1
  · exact right0Middle3_eq_case_4_2_row_1_0_0
  · exact right0Middle3_eq_case_4_2_row_1_0_1
  · exact right0Middle3_eq_case_4_2_row_1_1_0
  · exact right0Middle3_eq_case_4_2_row_1_1_1
  · exact right0Middle3_eq_case_4_2_row_1_2_0
  · exact right0Middle3_eq_case_4_2_row_1_2_1
  · exact right0Middle3_eq_case_4_2_row_1_3_0
  · exact right0Middle3_eq_case_4_2_row_1_3_1

set_option backward.isDefEq.respectTransparency false in
theorem right0Middle3_eq_case_4_2 : right0Middle3 4 2 = innerRightZ 3 4 2 * associatorZ 3 4 2 := by
  simpa only [HexagonAtoms342.assocABC_eq,
    HexagonAtoms342.outerABC_eq,
    HexagonAtoms342.assocBAC_eq,
    HexagonAtoms342.innerABC_eq,
    HexagonAtoms342.innerRightABC_eq,
    HexagonAtoms342.inverseACB_eq,
    HexagonAtoms342.innerACB_eq,
    HexagonAtoms342.assocBCA_eq,
    HexagonAtoms342.innerRightBAC_eq,
    HexagonAtoms342.assocCAB_eq,
    HexagonAtoms342.outerLeftABC_eq,
    HexagonRowColumn342.product0_eq,
    HexagonRowColumn342.product1_eq,
    HexagonRowColumn342.product2_eq,
    HexagonRowColumn342.product3_eq,
    HexagonRowColumn342.product4_eq,
    HexagonRowColumn342.product5_eq,
    HexagonRowColumn342.product6_eq,
    HexagonRowColumn342.product7_eq] using right0Middle3_eq_case_4_2_checked

private theorem right1Middle3_eq_case_4_2_row_0_0_0 : (right1Middle3 4 2) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn342.rows_inverseACB HexagonRowColumn342.cols_right0) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right1Middle3_eq_case_4_2_row_0_0_1 : (right1Middle3 4 2) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn342.rows_inverseACB HexagonRowColumn342.cols_right0) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right1Middle3_eq_case_4_2_row_0_1_0 : (right1Middle3 4 2) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn342.rows_inverseACB HexagonRowColumn342.cols_right0) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right1Middle3_eq_case_4_2_row_0_1_1 : (right1Middle3 4 2) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn342.rows_inverseACB HexagonRowColumn342.cols_right0) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right1Middle3_eq_case_4_2_row_0_2_0 : (right1Middle3 4 2) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn342.rows_inverseACB HexagonRowColumn342.cols_right0) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right1Middle3_eq_case_4_2_row_0_2_1 : (right1Middle3 4 2) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn342.rows_inverseACB HexagonRowColumn342.cols_right0) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right1Middle3_eq_case_4_2_row_0_3_0 : (right1Middle3 4 2) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn342.rows_inverseACB HexagonRowColumn342.cols_right0) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right1Middle3_eq_case_4_2_row_0_3_1 : (right1Middle3 4 2) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn342.rows_inverseACB HexagonRowColumn342.cols_right0) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right1Middle3_eq_case_4_2_row_1_0_0 : (right1Middle3 4 2) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn342.rows_inverseACB HexagonRowColumn342.cols_right0) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right1Middle3_eq_case_4_2_row_1_0_1 : (right1Middle3 4 2) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn342.rows_inverseACB HexagonRowColumn342.cols_right0) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right1Middle3_eq_case_4_2_row_1_1_0 : (right1Middle3 4 2) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn342.rows_inverseACB HexagonRowColumn342.cols_right0) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right1Middle3_eq_case_4_2_row_1_1_1 : (right1Middle3 4 2) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn342.rows_inverseACB HexagonRowColumn342.cols_right0) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right1Middle3_eq_case_4_2_row_1_2_0 : (right1Middle3 4 2) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn342.rows_inverseACB HexagonRowColumn342.cols_right0) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right1Middle3_eq_case_4_2_row_1_2_1 : (right1Middle3 4 2) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn342.rows_inverseACB HexagonRowColumn342.cols_right0) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right1Middle3_eq_case_4_2_row_1_3_0 : (right1Middle3 4 2) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn342.rows_inverseACB HexagonRowColumn342.cols_right0) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right1Middle3_eq_case_4_2_row_1_3_1 : (right1Middle3 4 2) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn342.rows_inverseACB HexagonRowColumn342.cols_right0) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right1Middle3_eq_case_4_2_checked : right1Middle3 4 2 = rowColumnMul HexagonRowColumn342.rows_inverseACB HexagonRowColumn342.cols_right0 := by
  funext r
  fin_cases r
  · exact right1Middle3_eq_case_4_2_row_0_0_0
  · exact right1Middle3_eq_case_4_2_row_0_0_1
  · exact right1Middle3_eq_case_4_2_row_0_1_0
  · exact right1Middle3_eq_case_4_2_row_0_1_1
  · exact right1Middle3_eq_case_4_2_row_0_2_0
  · exact right1Middle3_eq_case_4_2_row_0_2_1
  · exact right1Middle3_eq_case_4_2_row_0_3_0
  · exact right1Middle3_eq_case_4_2_row_0_3_1
  · exact right1Middle3_eq_case_4_2_row_1_0_0
  · exact right1Middle3_eq_case_4_2_row_1_0_1
  · exact right1Middle3_eq_case_4_2_row_1_1_0
  · exact right1Middle3_eq_case_4_2_row_1_1_1
  · exact right1Middle3_eq_case_4_2_row_1_2_0
  · exact right1Middle3_eq_case_4_2_row_1_2_1
  · exact right1Middle3_eq_case_4_2_row_1_3_0
  · exact right1Middle3_eq_case_4_2_row_1_3_1

set_option backward.isDefEq.respectTransparency false in
theorem right1Middle3_eq_case_4_2 : right1Middle3 4 2 = associatorInverseZ 3 2 4 * right0Middle3 4 2 := by
  simpa only [HexagonAtoms342.assocABC_eq,
    HexagonAtoms342.outerABC_eq,
    HexagonAtoms342.assocBAC_eq,
    HexagonAtoms342.innerABC_eq,
    HexagonAtoms342.innerRightABC_eq,
    HexagonAtoms342.inverseACB_eq,
    HexagonAtoms342.innerACB_eq,
    HexagonAtoms342.assocBCA_eq,
    HexagonAtoms342.innerRightBAC_eq,
    HexagonAtoms342.assocCAB_eq,
    HexagonAtoms342.outerLeftABC_eq,
    HexagonRowColumn342.product0_eq,
    HexagonRowColumn342.product1_eq,
    HexagonRowColumn342.product2_eq,
    HexagonRowColumn342.product3_eq,
    HexagonRowColumn342.product4_eq,
    HexagonRowColumn342.product5_eq,
    HexagonRowColumn342.product6_eq,
    HexagonRowColumn342.product7_eq] using right1Middle3_eq_case_4_2_checked

private theorem right2Middle3_eq_case_4_2_row_0_0_0 : (right2Middle3 4 2) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (right1Middle3 4 2) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right2Middle3_eq_case_4_2_row_0_0_1 : (right2Middle3 4 2) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (right1Middle3 4 2) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right2Middle3_eq_case_4_2_row_0_1_0 : (right2Middle3 4 2) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (right1Middle3 4 2) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right2Middle3_eq_case_4_2_row_0_1_1 : (right2Middle3 4 2) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (right1Middle3 4 2) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right2Middle3_eq_case_4_2_row_0_2_0 : (right2Middle3 4 2) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (right1Middle3 4 2) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right2Middle3_eq_case_4_2_row_0_2_1 : (right2Middle3 4 2) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (right1Middle3 4 2) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right2Middle3_eq_case_4_2_row_0_3_0 : (right2Middle3 4 2) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (right1Middle3 4 2) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right2Middle3_eq_case_4_2_row_0_3_1 : (right2Middle3 4 2) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (right1Middle3 4 2) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right2Middle3_eq_case_4_2_row_1_0_0 : (right2Middle3 4 2) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (right1Middle3 4 2) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right2Middle3_eq_case_4_2_row_1_0_1 : (right2Middle3 4 2) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (right1Middle3 4 2) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right2Middle3_eq_case_4_2_row_1_1_0 : (right2Middle3 4 2) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (right1Middle3 4 2) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right2Middle3_eq_case_4_2_row_1_1_1 : (right2Middle3 4 2) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (right1Middle3 4 2) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right2Middle3_eq_case_4_2_row_1_2_0 : (right2Middle3 4 2) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (right1Middle3 4 2) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right2Middle3_eq_case_4_2_row_1_2_1 : (right2Middle3 4 2) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (right1Middle3 4 2) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right2Middle3_eq_case_4_2_row_1_3_0 : (right2Middle3 4 2) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (right1Middle3 4 2) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right2Middle3_eq_case_4_2_row_1_3_1 : (right2Middle3 4 2) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (right1Middle3 4 2) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right2Middle3_eq_case_4_2_checked : right2Middle3 4 2 = right1Middle3 4 2 := by
  funext r
  fin_cases r
  · exact right2Middle3_eq_case_4_2_row_0_0_0
  · exact right2Middle3_eq_case_4_2_row_0_0_1
  · exact right2Middle3_eq_case_4_2_row_0_1_0
  · exact right2Middle3_eq_case_4_2_row_0_1_1
  · exact right2Middle3_eq_case_4_2_row_0_2_0
  · exact right2Middle3_eq_case_4_2_row_0_2_1
  · exact right2Middle3_eq_case_4_2_row_0_3_0
  · exact right2Middle3_eq_case_4_2_row_0_3_1
  · exact right2Middle3_eq_case_4_2_row_1_0_0
  · exact right2Middle3_eq_case_4_2_row_1_0_1
  · exact right2Middle3_eq_case_4_2_row_1_1_0
  · exact right2Middle3_eq_case_4_2_row_1_1_1
  · exact right2Middle3_eq_case_4_2_row_1_2_0
  · exact right2Middle3_eq_case_4_2_row_1_2_1
  · exact right2Middle3_eq_case_4_2_row_1_3_0
  · exact right2Middle3_eq_case_4_2_row_1_3_1

set_option backward.isDefEq.respectTransparency false in
theorem right2Middle3_eq_case_4_2 : right2Middle3 4 2 = innerLeftZ 3 2 4 * right1Middle3 4 2 := by
  simpa only [HexagonAtoms342.assocABC_eq,
    HexagonAtoms342.outerABC_eq,
    HexagonAtoms342.assocBAC_eq,
    HexagonAtoms342.innerABC_eq,
    HexagonAtoms342.innerRightABC_eq,
    HexagonAtoms342.inverseACB_eq,
    HexagonAtoms342.innerACB_eq,
    HexagonAtoms342.assocBCA_eq,
    HexagonAtoms342.innerRightBAC_eq,
    HexagonAtoms342.assocCAB_eq,
    HexagonAtoms342.outerLeftABC_eq,
    HexagonRowColumn342.product0_eq,
    HexagonRowColumn342.product1_eq,
    HexagonRowColumn342.product2_eq,
    HexagonRowColumn342.product3_eq,
    HexagonRowColumn342.product4_eq,
    HexagonRowColumn342.product5_eq,
    HexagonRowColumn342.product6_eq,
    HexagonRowColumn342.product7_eq] using right2Middle3_eq_case_4_2_checked

private theorem leftFinal3_case_4_2_row_0_0_0 : (((-1 : ℤ) ^ (leftScaleBit 3 4 2).val * positiveScale (leftScaleExponent 3 4 2)) •
      (rowColumnMul HexagonRowColumn342.rows_assocBCA HexagonRowColumn342.cols_left0)) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 3 4 2) • (left1Middle3 4 2)) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem leftFinal3_case_4_2_row_0_0_1 : (((-1 : ℤ) ^ (leftScaleBit 3 4 2).val * positiveScale (leftScaleExponent 3 4 2)) •
      (rowColumnMul HexagonRowColumn342.rows_assocBCA HexagonRowColumn342.cols_left0)) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 3 4 2) • (left1Middle3 4 2)) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem leftFinal3_case_4_2_row_0_1_0 : (((-1 : ℤ) ^ (leftScaleBit 3 4 2).val * positiveScale (leftScaleExponent 3 4 2)) •
      (rowColumnMul HexagonRowColumn342.rows_assocBCA HexagonRowColumn342.cols_left0)) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 3 4 2) • (left1Middle3 4 2)) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem leftFinal3_case_4_2_row_0_1_1 : (((-1 : ℤ) ^ (leftScaleBit 3 4 2).val * positiveScale (leftScaleExponent 3 4 2)) •
      (rowColumnMul HexagonRowColumn342.rows_assocBCA HexagonRowColumn342.cols_left0)) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 3 4 2) • (left1Middle3 4 2)) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem leftFinal3_case_4_2_row_0_2_0 : (((-1 : ℤ) ^ (leftScaleBit 3 4 2).val * positiveScale (leftScaleExponent 3 4 2)) •
      (rowColumnMul HexagonRowColumn342.rows_assocBCA HexagonRowColumn342.cols_left0)) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 3 4 2) • (left1Middle3 4 2)) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem leftFinal3_case_4_2_row_0_2_1 : (((-1 : ℤ) ^ (leftScaleBit 3 4 2).val * positiveScale (leftScaleExponent 3 4 2)) •
      (rowColumnMul HexagonRowColumn342.rows_assocBCA HexagonRowColumn342.cols_left0)) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 3 4 2) • (left1Middle3 4 2)) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem leftFinal3_case_4_2_row_0_3_0 : (((-1 : ℤ) ^ (leftScaleBit 3 4 2).val * positiveScale (leftScaleExponent 3 4 2)) •
      (rowColumnMul HexagonRowColumn342.rows_assocBCA HexagonRowColumn342.cols_left0)) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 3 4 2) • (left1Middle3 4 2)) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem leftFinal3_case_4_2_row_0_3_1 : (((-1 : ℤ) ^ (leftScaleBit 3 4 2).val * positiveScale (leftScaleExponent 3 4 2)) •
      (rowColumnMul HexagonRowColumn342.rows_assocBCA HexagonRowColumn342.cols_left0)) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 3 4 2) • (left1Middle3 4 2)) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem leftFinal3_case_4_2_row_1_0_0 : (((-1 : ℤ) ^ (leftScaleBit 3 4 2).val * positiveScale (leftScaleExponent 3 4 2)) •
      (rowColumnMul HexagonRowColumn342.rows_assocBCA HexagonRowColumn342.cols_left0)) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 3 4 2) • (left1Middle3 4 2)) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem leftFinal3_case_4_2_row_1_0_1 : (((-1 : ℤ) ^ (leftScaleBit 3 4 2).val * positiveScale (leftScaleExponent 3 4 2)) •
      (rowColumnMul HexagonRowColumn342.rows_assocBCA HexagonRowColumn342.cols_left0)) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 3 4 2) • (left1Middle3 4 2)) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem leftFinal3_case_4_2_row_1_1_0 : (((-1 : ℤ) ^ (leftScaleBit 3 4 2).val * positiveScale (leftScaleExponent 3 4 2)) •
      (rowColumnMul HexagonRowColumn342.rows_assocBCA HexagonRowColumn342.cols_left0)) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 3 4 2) • (left1Middle3 4 2)) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem leftFinal3_case_4_2_row_1_1_1 : (((-1 : ℤ) ^ (leftScaleBit 3 4 2).val * positiveScale (leftScaleExponent 3 4 2)) •
      (rowColumnMul HexagonRowColumn342.rows_assocBCA HexagonRowColumn342.cols_left0)) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 3 4 2) • (left1Middle3 4 2)) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem leftFinal3_case_4_2_row_1_2_0 : (((-1 : ℤ) ^ (leftScaleBit 3 4 2).val * positiveScale (leftScaleExponent 3 4 2)) •
      (rowColumnMul HexagonRowColumn342.rows_assocBCA HexagonRowColumn342.cols_left0)) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 3 4 2) • (left1Middle3 4 2)) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem leftFinal3_case_4_2_row_1_2_1 : (((-1 : ℤ) ^ (leftScaleBit 3 4 2).val * positiveScale (leftScaleExponent 3 4 2)) •
      (rowColumnMul HexagonRowColumn342.rows_assocBCA HexagonRowColumn342.cols_left0)) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 3 4 2) • (left1Middle3 4 2)) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem leftFinal3_case_4_2_row_1_3_0 : (((-1 : ℤ) ^ (leftScaleBit 3 4 2).val * positiveScale (leftScaleExponent 3 4 2)) •
      (rowColumnMul HexagonRowColumn342.rows_assocBCA HexagonRowColumn342.cols_left0)) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 3 4 2) • (left1Middle3 4 2)) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem leftFinal3_case_4_2_row_1_3_1 : (((-1 : ℤ) ^ (leftScaleBit 3 4 2).val * positiveScale (leftScaleExponent 3 4 2)) •
      (rowColumnMul HexagonRowColumn342.rows_assocBCA HexagonRowColumn342.cols_left0)) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 3 4 2) • (left1Middle3 4 2)) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem leftFinal3_case_4_2_checked : ((-1 : ℤ) ^ (leftScaleBit 3 4 2).val * positiveScale (leftScaleExponent 3 4 2)) •
      (rowColumnMul HexagonRowColumn342.rows_assocBCA HexagonRowColumn342.cols_left0) = negativeScale (leftScaleExponent 3 4 2) • (left1Middle3 4 2) := by
  funext r
  fin_cases r
  · exact leftFinal3_case_4_2_row_0_0_0
  · exact leftFinal3_case_4_2_row_0_0_1
  · exact leftFinal3_case_4_2_row_0_1_0
  · exact leftFinal3_case_4_2_row_0_1_1
  · exact leftFinal3_case_4_2_row_0_2_0
  · exact leftFinal3_case_4_2_row_0_2_1
  · exact leftFinal3_case_4_2_row_0_3_0
  · exact leftFinal3_case_4_2_row_0_3_1
  · exact leftFinal3_case_4_2_row_1_0_0
  · exact leftFinal3_case_4_2_row_1_0_1
  · exact leftFinal3_case_4_2_row_1_1_0
  · exact leftFinal3_case_4_2_row_1_1_1
  · exact leftFinal3_case_4_2_row_1_2_0
  · exact leftFinal3_case_4_2_row_1_2_1
  · exact leftFinal3_case_4_2_row_1_3_0
  · exact leftFinal3_case_4_2_row_1_3_1

set_option backward.isDefEq.respectTransparency false in
theorem leftFinal3_case_4_2 : ((-1 : ℤ) ^ (leftScaleBit 3 4 2).val * positiveScale (leftScaleExponent 3 4 2)) •
      (associatorZ 4 2 3 * left0Middle3 4 2) = negativeScale (leftScaleExponent 3 4 2) • (innerRightZ 4 3 2 * left1Middle3 4 2) := by
  simpa only [HexagonAtoms342.assocABC_eq,
    HexagonAtoms342.outerABC_eq,
    HexagonAtoms342.assocBAC_eq,
    HexagonAtoms342.innerABC_eq,
    HexagonAtoms342.innerRightABC_eq,
    HexagonAtoms342.inverseACB_eq,
    HexagonAtoms342.innerACB_eq,
    HexagonAtoms342.assocBCA_eq,
    HexagonAtoms342.innerRightBAC_eq,
    HexagonAtoms342.assocCAB_eq,
    HexagonAtoms342.outerLeftABC_eq,
    HexagonRowColumn342.product0_eq,
    HexagonRowColumn342.product1_eq,
    HexagonRowColumn342.product2_eq,
    HexagonRowColumn342.product3_eq,
    HexagonRowColumn342.product4_eq,
    HexagonRowColumn342.product5_eq,
    HexagonRowColumn342.product6_eq,
    HexagonRowColumn342.product7_eq] using leftFinal3_case_4_2_checked

private theorem rightFinal3_case_4_2_row_0_0_0 : (((-1 : ℤ) ^ (rightScaleBit 3 4 2).val * positiveScale (rightScaleExponent 3 4 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 4 : ℤ)) • HexagonAtoms342.outerLeftABC) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (negativeScale (rightScaleExponent 3 4 2) • (rowColumnMul HexagonRowColumn342.rows_assocCAB HexagonRowColumn342.cols_right2)) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem rightFinal3_case_4_2_row_0_0_1 : (((-1 : ℤ) ^ (rightScaleBit 3 4 2).val * positiveScale (rightScaleExponent 3 4 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 4 : ℤ)) • HexagonAtoms342.outerLeftABC) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (negativeScale (rightScaleExponent 3 4 2) • (rowColumnMul HexagonRowColumn342.rows_assocCAB HexagonRowColumn342.cols_right2)) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem rightFinal3_case_4_2_row_0_1_0 : (((-1 : ℤ) ^ (rightScaleBit 3 4 2).val * positiveScale (rightScaleExponent 3 4 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 4 : ℤ)) • HexagonAtoms342.outerLeftABC) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (negativeScale (rightScaleExponent 3 4 2) • (rowColumnMul HexagonRowColumn342.rows_assocCAB HexagonRowColumn342.cols_right2)) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem rightFinal3_case_4_2_row_0_1_1 : (((-1 : ℤ) ^ (rightScaleBit 3 4 2).val * positiveScale (rightScaleExponent 3 4 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 4 : ℤ)) • HexagonAtoms342.outerLeftABC) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (negativeScale (rightScaleExponent 3 4 2) • (rowColumnMul HexagonRowColumn342.rows_assocCAB HexagonRowColumn342.cols_right2)) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem rightFinal3_case_4_2_row_1_0_0 : (((-1 : ℤ) ^ (rightScaleBit 3 4 2).val * positiveScale (rightScaleExponent 3 4 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 4 : ℤ)) • HexagonAtoms342.outerLeftABC) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (negativeScale (rightScaleExponent 3 4 2) • (rowColumnMul HexagonRowColumn342.rows_assocCAB HexagonRowColumn342.cols_right2)) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem rightFinal3_case_4_2_row_1_0_1 : (((-1 : ℤ) ^ (rightScaleBit 3 4 2).val * positiveScale (rightScaleExponent 3 4 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 4 : ℤ)) • HexagonAtoms342.outerLeftABC) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (negativeScale (rightScaleExponent 3 4 2) • (rowColumnMul HexagonRowColumn342.rows_assocCAB HexagonRowColumn342.cols_right2)) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem rightFinal3_case_4_2_row_1_1_0 : (((-1 : ℤ) ^ (rightScaleBit 3 4 2).val * positiveScale (rightScaleExponent 3 4 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 4 : ℤ)) • HexagonAtoms342.outerLeftABC) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (negativeScale (rightScaleExponent 3 4 2) • (rowColumnMul HexagonRowColumn342.rows_assocCAB HexagonRowColumn342.cols_right2)) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem rightFinal3_case_4_2_row_1_1_1 : (((-1 : ℤ) ^ (rightScaleBit 3 4 2).val * positiveScale (rightScaleExponent 3 4 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 4 : ℤ)) • HexagonAtoms342.outerLeftABC) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (negativeScale (rightScaleExponent 3 4 2) • (rowColumnMul HexagonRowColumn342.rows_assocCAB HexagonRowColumn342.cols_right2)) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem rightFinal3_case_4_2_row_2_0_0 : (((-1 : ℤ) ^ (rightScaleBit 3 4 2).val * positiveScale (rightScaleExponent 3 4 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 4 : ℤ)) • HexagonAtoms342.outerLeftABC) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (negativeScale (rightScaleExponent 3 4 2) • (rowColumnMul HexagonRowColumn342.rows_assocCAB HexagonRowColumn342.cols_right2)) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem rightFinal3_case_4_2_row_2_0_1 : (((-1 : ℤ) ^ (rightScaleBit 3 4 2).val * positiveScale (rightScaleExponent 3 4 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 4 : ℤ)) • HexagonAtoms342.outerLeftABC) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (negativeScale (rightScaleExponent 3 4 2) • (rowColumnMul HexagonRowColumn342.rows_assocCAB HexagonRowColumn342.cols_right2)) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem rightFinal3_case_4_2_row_2_1_0 : (((-1 : ℤ) ^ (rightScaleBit 3 4 2).val * positiveScale (rightScaleExponent 3 4 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 4 : ℤ)) • HexagonAtoms342.outerLeftABC) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (negativeScale (rightScaleExponent 3 4 2) • (rowColumnMul HexagonRowColumn342.rows_assocCAB HexagonRowColumn342.cols_right2)) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem rightFinal3_case_4_2_row_2_1_1 : (((-1 : ℤ) ^ (rightScaleBit 3 4 2).val * positiveScale (rightScaleExponent 3 4 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 4 : ℤ)) • HexagonAtoms342.outerLeftABC) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (negativeScale (rightScaleExponent 3 4 2) • (rowColumnMul HexagonRowColumn342.rows_assocCAB HexagonRowColumn342.cols_right2)) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem rightFinal3_case_4_2_row_3_0_0 : (((-1 : ℤ) ^ (rightScaleBit 3 4 2).val * positiveScale (rightScaleExponent 3 4 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 4 : ℤ)) • HexagonAtoms342.outerLeftABC) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (negativeScale (rightScaleExponent 3 4 2) • (rowColumnMul HexagonRowColumn342.rows_assocCAB HexagonRowColumn342.cols_right2)) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem rightFinal3_case_4_2_row_3_0_1 : (((-1 : ℤ) ^ (rightScaleBit 3 4 2).val * positiveScale (rightScaleExponent 3 4 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 4 : ℤ)) • HexagonAtoms342.outerLeftABC) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (negativeScale (rightScaleExponent 3 4 2) • (rowColumnMul HexagonRowColumn342.rows_assocCAB HexagonRowColumn342.cols_right2)) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem rightFinal3_case_4_2_row_3_1_0 : (((-1 : ℤ) ^ (rightScaleBit 3 4 2).val * positiveScale (rightScaleExponent 3 4 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 4 : ℤ)) • HexagonAtoms342.outerLeftABC) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (negativeScale (rightScaleExponent 3 4 2) • (rowColumnMul HexagonRowColumn342.rows_assocCAB HexagonRowColumn342.cols_right2)) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem rightFinal3_case_4_2_row_3_1_1 : (((-1 : ℤ) ^ (rightScaleBit 3 4 2).val * positiveScale (rightScaleExponent 3 4 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 4 : ℤ)) • HexagonAtoms342.outerLeftABC) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (negativeScale (rightScaleExponent 3 4 2) • (rowColumnMul HexagonRowColumn342.rows_assocCAB HexagonRowColumn342.cols_right2)) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem rightFinal3_case_4_2_checked : ((-1 : ℤ) ^ (rightScaleBit 3 4 2).val * positiveScale (rightScaleExponent 3 4 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 4 : ℤ)) • HexagonAtoms342.outerLeftABC = negativeScale (rightScaleExponent 3 4 2) • (rowColumnMul HexagonRowColumn342.rows_assocCAB HexagonRowColumn342.cols_right2) := by
  funext r
  fin_cases r
  · exact rightFinal3_case_4_2_row_0_0_0
  · exact rightFinal3_case_4_2_row_0_0_1
  · exact rightFinal3_case_4_2_row_0_1_0
  · exact rightFinal3_case_4_2_row_0_1_1
  · exact rightFinal3_case_4_2_row_1_0_0
  · exact rightFinal3_case_4_2_row_1_0_1
  · exact rightFinal3_case_4_2_row_1_1_0
  · exact rightFinal3_case_4_2_row_1_1_1
  · exact rightFinal3_case_4_2_row_2_0_0
  · exact rightFinal3_case_4_2_row_2_0_1
  · exact rightFinal3_case_4_2_row_2_1_0
  · exact rightFinal3_case_4_2_row_2_1_1
  · exact rightFinal3_case_4_2_row_3_0_0
  · exact rightFinal3_case_4_2_row_3_0_1
  · exact rightFinal3_case_4_2_row_3_1_0
  · exact rightFinal3_case_4_2_row_3_1_1

set_option backward.isDefEq.respectTransparency false in
theorem rightFinal3_case_4_2 : ((-1 : ℤ) ^ (rightScaleBit 3 4 2).val * positiveScale (rightScaleExponent 3 4 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 2 4 : ℤ)) • outerLeftZ 3 4 2 = negativeScale (rightScaleExponent 3 4 2) • (associatorZ 2 3 4 * right2Middle3 4 2) := by
  simpa only [HexagonAtoms342.assocABC_eq,
    HexagonAtoms342.outerABC_eq,
    HexagonAtoms342.assocBAC_eq,
    HexagonAtoms342.innerABC_eq,
    HexagonAtoms342.innerRightABC_eq,
    HexagonAtoms342.inverseACB_eq,
    HexagonAtoms342.innerACB_eq,
    HexagonAtoms342.assocBCA_eq,
    HexagonAtoms342.innerRightBAC_eq,
    HexagonAtoms342.assocCAB_eq,
    HexagonAtoms342.outerLeftABC_eq,
    HexagonRowColumn342.product0_eq,
    HexagonRowColumn342.product1_eq,
    HexagonRowColumn342.product2_eq,
    HexagonRowColumn342.product3_eq,
    HexagonRowColumn342.product4_eq,
    HexagonRowColumn342.product5_eq,
    HexagonRowColumn342.product6_eq,
    HexagonRowColumn342.product7_eq] using rightFinal3_case_4_2_checked

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonCases3
