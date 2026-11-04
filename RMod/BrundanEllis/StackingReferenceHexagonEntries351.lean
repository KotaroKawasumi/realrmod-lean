import RMod.BrundanEllis.StackingReferenceHexagonMiddle3
import RMod.BrundanEllis.StackingReferenceSparseMatrixCheck
import RMod.BrundanEllis.StackingReferenceHexagonAtoms351
import RMod.BrundanEllis.StackingReferenceHexagonRowColumn351

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

private theorem left0Middle3_eq_case_5_1_row_0_0_0 : (left0Middle3 5 1) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (HexagonAtoms351.assocABC) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem left0Middle3_eq_case_5_1_row_0_0_1 : (left0Middle3 5 1) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (HexagonAtoms351.assocABC) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem left0Middle3_eq_case_5_1_row_0_1_0 : (left0Middle3 5 1) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (HexagonAtoms351.assocABC) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem left0Middle3_eq_case_5_1_row_0_1_1 : (left0Middle3 5 1) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (HexagonAtoms351.assocABC) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem left0Middle3_eq_case_5_1_row_0_2_0 : (left0Middle3 5 1) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (HexagonAtoms351.assocABC) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem left0Middle3_eq_case_5_1_row_0_2_1 : (left0Middle3 5 1) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (HexagonAtoms351.assocABC) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem left0Middle3_eq_case_5_1_row_0_3_0 : (left0Middle3 5 1) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (HexagonAtoms351.assocABC) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem left0Middle3_eq_case_5_1_row_0_3_1 : (left0Middle3 5 1) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (HexagonAtoms351.assocABC) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem left0Middle3_eq_case_5_1_row_1_0_0 : (left0Middle3 5 1) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (HexagonAtoms351.assocABC) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem left0Middle3_eq_case_5_1_row_1_0_1 : (left0Middle3 5 1) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (HexagonAtoms351.assocABC) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem left0Middle3_eq_case_5_1_row_1_1_0 : (left0Middle3 5 1) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (HexagonAtoms351.assocABC) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem left0Middle3_eq_case_5_1_row_1_1_1 : (left0Middle3 5 1) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (HexagonAtoms351.assocABC) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem left0Middle3_eq_case_5_1_row_1_2_0 : (left0Middle3 5 1) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (HexagonAtoms351.assocABC) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem left0Middle3_eq_case_5_1_row_1_2_1 : (left0Middle3 5 1) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (HexagonAtoms351.assocABC) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem left0Middle3_eq_case_5_1_row_1_3_0 : (left0Middle3 5 1) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (HexagonAtoms351.assocABC) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem left0Middle3_eq_case_5_1_row_1_3_1 : (left0Middle3 5 1) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (HexagonAtoms351.assocABC) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem left0Middle3_eq_case_5_1_checked : left0Middle3 5 1 = HexagonAtoms351.assocABC := by
  funext r
  fin_cases r
  · exact left0Middle3_eq_case_5_1_row_0_0_0
  · exact left0Middle3_eq_case_5_1_row_0_0_1
  · exact left0Middle3_eq_case_5_1_row_0_1_0
  · exact left0Middle3_eq_case_5_1_row_0_1_1
  · exact left0Middle3_eq_case_5_1_row_0_2_0
  · exact left0Middle3_eq_case_5_1_row_0_2_1
  · exact left0Middle3_eq_case_5_1_row_0_3_0
  · exact left0Middle3_eq_case_5_1_row_0_3_1
  · exact left0Middle3_eq_case_5_1_row_1_0_0
  · exact left0Middle3_eq_case_5_1_row_1_0_1
  · exact left0Middle3_eq_case_5_1_row_1_1_0
  · exact left0Middle3_eq_case_5_1_row_1_1_1
  · exact left0Middle3_eq_case_5_1_row_1_2_0
  · exact left0Middle3_eq_case_5_1_row_1_2_1
  · exact left0Middle3_eq_case_5_1_row_1_3_0
  · exact left0Middle3_eq_case_5_1_row_1_3_1

set_option backward.isDefEq.respectTransparency false in
theorem left0Middle3_eq_case_5_1 : left0Middle3 5 1 = outerRightZ 3 5 1 * associatorZ 3 5 1 := by
  simpa only [HexagonAtoms351.assocABC_eq,
    HexagonAtoms351.outerABC_eq,
    HexagonAtoms351.assocBAC_eq,
    HexagonAtoms351.innerABC_eq,
    HexagonAtoms351.innerRightABC_eq,
    HexagonAtoms351.inverseACB_eq,
    HexagonAtoms351.innerACB_eq,
    HexagonAtoms351.assocBCA_eq,
    HexagonAtoms351.innerRightBAC_eq,
    HexagonAtoms351.assocCAB_eq,
    HexagonAtoms351.outerLeftABC_eq,
    HexagonRowColumn351.product0_eq,
    HexagonRowColumn351.product1_eq,
    HexagonRowColumn351.product2_eq,
    HexagonRowColumn351.product3_eq,
    HexagonRowColumn351.product4_eq,
    HexagonRowColumn351.product5_eq,
    HexagonRowColumn351.product6_eq,
    HexagonRowColumn351.product7_eq] using left0Middle3_eq_case_5_1_checked

private theorem left1Middle3_eq_case_5_1_row_0_0_0 : (left1Middle3 5 1) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (HexagonAtoms351.assocBAC) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem left1Middle3_eq_case_5_1_row_0_0_1 : (left1Middle3 5 1) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (HexagonAtoms351.assocBAC) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem left1Middle3_eq_case_5_1_row_0_1_0 : (left1Middle3 5 1) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (HexagonAtoms351.assocBAC) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem left1Middle3_eq_case_5_1_row_0_1_1 : (left1Middle3 5 1) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (HexagonAtoms351.assocBAC) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem left1Middle3_eq_case_5_1_row_0_2_0 : (left1Middle3 5 1) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (HexagonAtoms351.assocBAC) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem left1Middle3_eq_case_5_1_row_0_2_1 : (left1Middle3 5 1) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (HexagonAtoms351.assocBAC) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem left1Middle3_eq_case_5_1_row_0_3_0 : (left1Middle3 5 1) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (HexagonAtoms351.assocBAC) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem left1Middle3_eq_case_5_1_row_0_3_1 : (left1Middle3 5 1) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (HexagonAtoms351.assocBAC) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem left1Middle3_eq_case_5_1_row_1_0_0 : (left1Middle3 5 1) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (HexagonAtoms351.assocBAC) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem left1Middle3_eq_case_5_1_row_1_0_1 : (left1Middle3 5 1) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (HexagonAtoms351.assocBAC) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem left1Middle3_eq_case_5_1_row_1_1_0 : (left1Middle3 5 1) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (HexagonAtoms351.assocBAC) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem left1Middle3_eq_case_5_1_row_1_1_1 : (left1Middle3 5 1) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (HexagonAtoms351.assocBAC) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem left1Middle3_eq_case_5_1_row_1_2_0 : (left1Middle3 5 1) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (HexagonAtoms351.assocBAC) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem left1Middle3_eq_case_5_1_row_1_2_1 : (left1Middle3 5 1) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (HexagonAtoms351.assocBAC) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem left1Middle3_eq_case_5_1_row_1_3_0 : (left1Middle3 5 1) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (HexagonAtoms351.assocBAC) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem left1Middle3_eq_case_5_1_row_1_3_1 : (left1Middle3 5 1) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (HexagonAtoms351.assocBAC) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem left1Middle3_eq_case_5_1_checked : left1Middle3 5 1 = HexagonAtoms351.assocBAC := by
  funext r
  fin_cases r
  · exact left1Middle3_eq_case_5_1_row_0_0_0
  · exact left1Middle3_eq_case_5_1_row_0_0_1
  · exact left1Middle3_eq_case_5_1_row_0_1_0
  · exact left1Middle3_eq_case_5_1_row_0_1_1
  · exact left1Middle3_eq_case_5_1_row_0_2_0
  · exact left1Middle3_eq_case_5_1_row_0_2_1
  · exact left1Middle3_eq_case_5_1_row_0_3_0
  · exact left1Middle3_eq_case_5_1_row_0_3_1
  · exact left1Middle3_eq_case_5_1_row_1_0_0
  · exact left1Middle3_eq_case_5_1_row_1_0_1
  · exact left1Middle3_eq_case_5_1_row_1_1_0
  · exact left1Middle3_eq_case_5_1_row_1_1_1
  · exact left1Middle3_eq_case_5_1_row_1_2_0
  · exact left1Middle3_eq_case_5_1_row_1_2_1
  · exact left1Middle3_eq_case_5_1_row_1_3_0
  · exact left1Middle3_eq_case_5_1_row_1_3_1

set_option backward.isDefEq.respectTransparency false in
theorem left1Middle3_eq_case_5_1 : left1Middle3 5 1 = associatorZ 5 3 1 * innerLeftZ 3 5 1 := by
  simpa only [HexagonAtoms351.assocABC_eq,
    HexagonAtoms351.outerABC_eq,
    HexagonAtoms351.assocBAC_eq,
    HexagonAtoms351.innerABC_eq,
    HexagonAtoms351.innerRightABC_eq,
    HexagonAtoms351.inverseACB_eq,
    HexagonAtoms351.innerACB_eq,
    HexagonAtoms351.assocBCA_eq,
    HexagonAtoms351.innerRightBAC_eq,
    HexagonAtoms351.assocCAB_eq,
    HexagonAtoms351.outerLeftABC_eq,
    HexagonRowColumn351.product0_eq,
    HexagonRowColumn351.product1_eq,
    HexagonRowColumn351.product2_eq,
    HexagonRowColumn351.product3_eq,
    HexagonRowColumn351.product4_eq,
    HexagonRowColumn351.product5_eq,
    HexagonRowColumn351.product6_eq,
    HexagonRowColumn351.product7_eq] using left1Middle3_eq_case_5_1_checked

private theorem right0Middle3_eq_case_5_1_row_0_0_0 : (right0Middle3 5 1) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (HexagonAtoms351.assocABC) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right0Middle3_eq_case_5_1_row_0_0_1 : (right0Middle3 5 1) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (HexagonAtoms351.assocABC) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right0Middle3_eq_case_5_1_row_0_1_0 : (right0Middle3 5 1) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (HexagonAtoms351.assocABC) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right0Middle3_eq_case_5_1_row_0_1_1 : (right0Middle3 5 1) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (HexagonAtoms351.assocABC) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right0Middle3_eq_case_5_1_row_0_2_0 : (right0Middle3 5 1) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (HexagonAtoms351.assocABC) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right0Middle3_eq_case_5_1_row_0_2_1 : (right0Middle3 5 1) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (HexagonAtoms351.assocABC) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right0Middle3_eq_case_5_1_row_0_3_0 : (right0Middle3 5 1) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (HexagonAtoms351.assocABC) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right0Middle3_eq_case_5_1_row_0_3_1 : (right0Middle3 5 1) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (HexagonAtoms351.assocABC) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right0Middle3_eq_case_5_1_row_1_0_0 : (right0Middle3 5 1) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (HexagonAtoms351.assocABC) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right0Middle3_eq_case_5_1_row_1_0_1 : (right0Middle3 5 1) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (HexagonAtoms351.assocABC) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right0Middle3_eq_case_5_1_row_1_1_0 : (right0Middle3 5 1) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (HexagonAtoms351.assocABC) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right0Middle3_eq_case_5_1_row_1_1_1 : (right0Middle3 5 1) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (HexagonAtoms351.assocABC) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right0Middle3_eq_case_5_1_row_1_2_0 : (right0Middle3 5 1) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (HexagonAtoms351.assocABC) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right0Middle3_eq_case_5_1_row_1_2_1 : (right0Middle3 5 1) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (HexagonAtoms351.assocABC) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right0Middle3_eq_case_5_1_row_1_3_0 : (right0Middle3 5 1) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (HexagonAtoms351.assocABC) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right0Middle3_eq_case_5_1_row_1_3_1 : (right0Middle3 5 1) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (HexagonAtoms351.assocABC) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right0Middle3_eq_case_5_1_checked : right0Middle3 5 1 = HexagonAtoms351.assocABC := by
  funext r
  fin_cases r
  · exact right0Middle3_eq_case_5_1_row_0_0_0
  · exact right0Middle3_eq_case_5_1_row_0_0_1
  · exact right0Middle3_eq_case_5_1_row_0_1_0
  · exact right0Middle3_eq_case_5_1_row_0_1_1
  · exact right0Middle3_eq_case_5_1_row_0_2_0
  · exact right0Middle3_eq_case_5_1_row_0_2_1
  · exact right0Middle3_eq_case_5_1_row_0_3_0
  · exact right0Middle3_eq_case_5_1_row_0_3_1
  · exact right0Middle3_eq_case_5_1_row_1_0_0
  · exact right0Middle3_eq_case_5_1_row_1_0_1
  · exact right0Middle3_eq_case_5_1_row_1_1_0
  · exact right0Middle3_eq_case_5_1_row_1_1_1
  · exact right0Middle3_eq_case_5_1_row_1_2_0
  · exact right0Middle3_eq_case_5_1_row_1_2_1
  · exact right0Middle3_eq_case_5_1_row_1_3_0
  · exact right0Middle3_eq_case_5_1_row_1_3_1

set_option backward.isDefEq.respectTransparency false in
theorem right0Middle3_eq_case_5_1 : right0Middle3 5 1 = innerRightZ 3 5 1 * associatorZ 3 5 1 := by
  simpa only [HexagonAtoms351.assocABC_eq,
    HexagonAtoms351.outerABC_eq,
    HexagonAtoms351.assocBAC_eq,
    HexagonAtoms351.innerABC_eq,
    HexagonAtoms351.innerRightABC_eq,
    HexagonAtoms351.inverseACB_eq,
    HexagonAtoms351.innerACB_eq,
    HexagonAtoms351.assocBCA_eq,
    HexagonAtoms351.innerRightBAC_eq,
    HexagonAtoms351.assocCAB_eq,
    HexagonAtoms351.outerLeftABC_eq,
    HexagonRowColumn351.product0_eq,
    HexagonRowColumn351.product1_eq,
    HexagonRowColumn351.product2_eq,
    HexagonRowColumn351.product3_eq,
    HexagonRowColumn351.product4_eq,
    HexagonRowColumn351.product5_eq,
    HexagonRowColumn351.product6_eq,
    HexagonRowColumn351.product7_eq] using right0Middle3_eq_case_5_1_checked

private theorem right1Middle3_eq_case_5_1_row_0_0_0 : (right1Middle3 5 1) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn351.rows_inverseACB HexagonRowColumn351.cols_right0) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right1Middle3_eq_case_5_1_row_0_0_1 : (right1Middle3 5 1) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn351.rows_inverseACB HexagonRowColumn351.cols_right0) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right1Middle3_eq_case_5_1_row_0_1_0 : (right1Middle3 5 1) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn351.rows_inverseACB HexagonRowColumn351.cols_right0) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right1Middle3_eq_case_5_1_row_0_1_1 : (right1Middle3 5 1) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn351.rows_inverseACB HexagonRowColumn351.cols_right0) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right1Middle3_eq_case_5_1_row_0_2_0 : (right1Middle3 5 1) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn351.rows_inverseACB HexagonRowColumn351.cols_right0) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right1Middle3_eq_case_5_1_row_0_2_1 : (right1Middle3 5 1) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn351.rows_inverseACB HexagonRowColumn351.cols_right0) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right1Middle3_eq_case_5_1_row_0_3_0 : (right1Middle3 5 1) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn351.rows_inverseACB HexagonRowColumn351.cols_right0) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right1Middle3_eq_case_5_1_row_0_3_1 : (right1Middle3 5 1) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn351.rows_inverseACB HexagonRowColumn351.cols_right0) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right1Middle3_eq_case_5_1_row_1_0_0 : (right1Middle3 5 1) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn351.rows_inverseACB HexagonRowColumn351.cols_right0) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right1Middle3_eq_case_5_1_row_1_0_1 : (right1Middle3 5 1) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn351.rows_inverseACB HexagonRowColumn351.cols_right0) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right1Middle3_eq_case_5_1_row_1_1_0 : (right1Middle3 5 1) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn351.rows_inverseACB HexagonRowColumn351.cols_right0) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right1Middle3_eq_case_5_1_row_1_1_1 : (right1Middle3 5 1) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn351.rows_inverseACB HexagonRowColumn351.cols_right0) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right1Middle3_eq_case_5_1_row_1_2_0 : (right1Middle3 5 1) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn351.rows_inverseACB HexagonRowColumn351.cols_right0) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right1Middle3_eq_case_5_1_row_1_2_1 : (right1Middle3 5 1) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn351.rows_inverseACB HexagonRowColumn351.cols_right0) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right1Middle3_eq_case_5_1_row_1_3_0 : (right1Middle3 5 1) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn351.rows_inverseACB HexagonRowColumn351.cols_right0) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right1Middle3_eq_case_5_1_row_1_3_1 : (right1Middle3 5 1) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn351.rows_inverseACB HexagonRowColumn351.cols_right0) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right1Middle3_eq_case_5_1_checked : right1Middle3 5 1 = rowColumnMul HexagonRowColumn351.rows_inverseACB HexagonRowColumn351.cols_right0 := by
  funext r
  fin_cases r
  · exact right1Middle3_eq_case_5_1_row_0_0_0
  · exact right1Middle3_eq_case_5_1_row_0_0_1
  · exact right1Middle3_eq_case_5_1_row_0_1_0
  · exact right1Middle3_eq_case_5_1_row_0_1_1
  · exact right1Middle3_eq_case_5_1_row_0_2_0
  · exact right1Middle3_eq_case_5_1_row_0_2_1
  · exact right1Middle3_eq_case_5_1_row_0_3_0
  · exact right1Middle3_eq_case_5_1_row_0_3_1
  · exact right1Middle3_eq_case_5_1_row_1_0_0
  · exact right1Middle3_eq_case_5_1_row_1_0_1
  · exact right1Middle3_eq_case_5_1_row_1_1_0
  · exact right1Middle3_eq_case_5_1_row_1_1_1
  · exact right1Middle3_eq_case_5_1_row_1_2_0
  · exact right1Middle3_eq_case_5_1_row_1_2_1
  · exact right1Middle3_eq_case_5_1_row_1_3_0
  · exact right1Middle3_eq_case_5_1_row_1_3_1

set_option backward.isDefEq.respectTransparency false in
theorem right1Middle3_eq_case_5_1 : right1Middle3 5 1 = associatorInverseZ 3 1 5 * right0Middle3 5 1 := by
  simpa only [HexagonAtoms351.assocABC_eq,
    HexagonAtoms351.outerABC_eq,
    HexagonAtoms351.assocBAC_eq,
    HexagonAtoms351.innerABC_eq,
    HexagonAtoms351.innerRightABC_eq,
    HexagonAtoms351.inverseACB_eq,
    HexagonAtoms351.innerACB_eq,
    HexagonAtoms351.assocBCA_eq,
    HexagonAtoms351.innerRightBAC_eq,
    HexagonAtoms351.assocCAB_eq,
    HexagonAtoms351.outerLeftABC_eq,
    HexagonRowColumn351.product0_eq,
    HexagonRowColumn351.product1_eq,
    HexagonRowColumn351.product2_eq,
    HexagonRowColumn351.product3_eq,
    HexagonRowColumn351.product4_eq,
    HexagonRowColumn351.product5_eq,
    HexagonRowColumn351.product6_eq,
    HexagonRowColumn351.product7_eq] using right1Middle3_eq_case_5_1_checked

private theorem right2Middle3_eq_case_5_1_row_0_0_0 : (right2Middle3 5 1) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (right1Middle3 5 1) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right2Middle3_eq_case_5_1_row_0_0_1 : (right2Middle3 5 1) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (right1Middle3 5 1) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right2Middle3_eq_case_5_1_row_0_1_0 : (right2Middle3 5 1) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (right1Middle3 5 1) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right2Middle3_eq_case_5_1_row_0_1_1 : (right2Middle3 5 1) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (right1Middle3 5 1) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right2Middle3_eq_case_5_1_row_0_2_0 : (right2Middle3 5 1) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (right1Middle3 5 1) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right2Middle3_eq_case_5_1_row_0_2_1 : (right2Middle3 5 1) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (right1Middle3 5 1) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right2Middle3_eq_case_5_1_row_0_3_0 : (right2Middle3 5 1) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (right1Middle3 5 1) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right2Middle3_eq_case_5_1_row_0_3_1 : (right2Middle3 5 1) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (right1Middle3 5 1) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right2Middle3_eq_case_5_1_row_1_0_0 : (right2Middle3 5 1) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (right1Middle3 5 1) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right2Middle3_eq_case_5_1_row_1_0_1 : (right2Middle3 5 1) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (right1Middle3 5 1) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right2Middle3_eq_case_5_1_row_1_1_0 : (right2Middle3 5 1) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (right1Middle3 5 1) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right2Middle3_eq_case_5_1_row_1_1_1 : (right2Middle3 5 1) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (right1Middle3 5 1) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right2Middle3_eq_case_5_1_row_1_2_0 : (right2Middle3 5 1) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (right1Middle3 5 1) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right2Middle3_eq_case_5_1_row_1_2_1 : (right2Middle3 5 1) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (right1Middle3 5 1) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right2Middle3_eq_case_5_1_row_1_3_0 : (right2Middle3 5 1) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (right1Middle3 5 1) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right2Middle3_eq_case_5_1_row_1_3_1 : (right2Middle3 5 1) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (right1Middle3 5 1) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right2Middle3_eq_case_5_1_checked : right2Middle3 5 1 = right1Middle3 5 1 := by
  funext r
  fin_cases r
  · exact right2Middle3_eq_case_5_1_row_0_0_0
  · exact right2Middle3_eq_case_5_1_row_0_0_1
  · exact right2Middle3_eq_case_5_1_row_0_1_0
  · exact right2Middle3_eq_case_5_1_row_0_1_1
  · exact right2Middle3_eq_case_5_1_row_0_2_0
  · exact right2Middle3_eq_case_5_1_row_0_2_1
  · exact right2Middle3_eq_case_5_1_row_0_3_0
  · exact right2Middle3_eq_case_5_1_row_0_3_1
  · exact right2Middle3_eq_case_5_1_row_1_0_0
  · exact right2Middle3_eq_case_5_1_row_1_0_1
  · exact right2Middle3_eq_case_5_1_row_1_1_0
  · exact right2Middle3_eq_case_5_1_row_1_1_1
  · exact right2Middle3_eq_case_5_1_row_1_2_0
  · exact right2Middle3_eq_case_5_1_row_1_2_1
  · exact right2Middle3_eq_case_5_1_row_1_3_0
  · exact right2Middle3_eq_case_5_1_row_1_3_1

set_option backward.isDefEq.respectTransparency false in
theorem right2Middle3_eq_case_5_1 : right2Middle3 5 1 = innerLeftZ 3 1 5 * right1Middle3 5 1 := by
  simpa only [HexagonAtoms351.assocABC_eq,
    HexagonAtoms351.outerABC_eq,
    HexagonAtoms351.assocBAC_eq,
    HexagonAtoms351.innerABC_eq,
    HexagonAtoms351.innerRightABC_eq,
    HexagonAtoms351.inverseACB_eq,
    HexagonAtoms351.innerACB_eq,
    HexagonAtoms351.assocBCA_eq,
    HexagonAtoms351.innerRightBAC_eq,
    HexagonAtoms351.assocCAB_eq,
    HexagonAtoms351.outerLeftABC_eq,
    HexagonRowColumn351.product0_eq,
    HexagonRowColumn351.product1_eq,
    HexagonRowColumn351.product2_eq,
    HexagonRowColumn351.product3_eq,
    HexagonRowColumn351.product4_eq,
    HexagonRowColumn351.product5_eq,
    HexagonRowColumn351.product6_eq,
    HexagonRowColumn351.product7_eq] using right2Middle3_eq_case_5_1_checked

private theorem leftFinal3_case_5_1_row_0_0_0 : (((-1 : ℤ) ^ (leftScaleBit 3 5 1).val * positiveScale (leftScaleExponent 3 5 1)) •
      (rowColumnMul HexagonRowColumn351.rows_assocBCA HexagonRowColumn351.cols_left0)) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 3 5 1) • (left1Middle3 5 1)) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem leftFinal3_case_5_1_row_0_0_1 : (((-1 : ℤ) ^ (leftScaleBit 3 5 1).val * positiveScale (leftScaleExponent 3 5 1)) •
      (rowColumnMul HexagonRowColumn351.rows_assocBCA HexagonRowColumn351.cols_left0)) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 3 5 1) • (left1Middle3 5 1)) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem leftFinal3_case_5_1_row_0_1_0 : (((-1 : ℤ) ^ (leftScaleBit 3 5 1).val * positiveScale (leftScaleExponent 3 5 1)) •
      (rowColumnMul HexagonRowColumn351.rows_assocBCA HexagonRowColumn351.cols_left0)) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 3 5 1) • (left1Middle3 5 1)) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem leftFinal3_case_5_1_row_0_1_1 : (((-1 : ℤ) ^ (leftScaleBit 3 5 1).val * positiveScale (leftScaleExponent 3 5 1)) •
      (rowColumnMul HexagonRowColumn351.rows_assocBCA HexagonRowColumn351.cols_left0)) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 3 5 1) • (left1Middle3 5 1)) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem leftFinal3_case_5_1_row_0_2_0 : (((-1 : ℤ) ^ (leftScaleBit 3 5 1).val * positiveScale (leftScaleExponent 3 5 1)) •
      (rowColumnMul HexagonRowColumn351.rows_assocBCA HexagonRowColumn351.cols_left0)) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 3 5 1) • (left1Middle3 5 1)) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem leftFinal3_case_5_1_row_0_2_1 : (((-1 : ℤ) ^ (leftScaleBit 3 5 1).val * positiveScale (leftScaleExponent 3 5 1)) •
      (rowColumnMul HexagonRowColumn351.rows_assocBCA HexagonRowColumn351.cols_left0)) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 3 5 1) • (left1Middle3 5 1)) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem leftFinal3_case_5_1_row_0_3_0 : (((-1 : ℤ) ^ (leftScaleBit 3 5 1).val * positiveScale (leftScaleExponent 3 5 1)) •
      (rowColumnMul HexagonRowColumn351.rows_assocBCA HexagonRowColumn351.cols_left0)) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 3 5 1) • (left1Middle3 5 1)) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem leftFinal3_case_5_1_row_0_3_1 : (((-1 : ℤ) ^ (leftScaleBit 3 5 1).val * positiveScale (leftScaleExponent 3 5 1)) •
      (rowColumnMul HexagonRowColumn351.rows_assocBCA HexagonRowColumn351.cols_left0)) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 3 5 1) • (left1Middle3 5 1)) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem leftFinal3_case_5_1_row_1_0_0 : (((-1 : ℤ) ^ (leftScaleBit 3 5 1).val * positiveScale (leftScaleExponent 3 5 1)) •
      (rowColumnMul HexagonRowColumn351.rows_assocBCA HexagonRowColumn351.cols_left0)) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 3 5 1) • (left1Middle3 5 1)) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem leftFinal3_case_5_1_row_1_0_1 : (((-1 : ℤ) ^ (leftScaleBit 3 5 1).val * positiveScale (leftScaleExponent 3 5 1)) •
      (rowColumnMul HexagonRowColumn351.rows_assocBCA HexagonRowColumn351.cols_left0)) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 3 5 1) • (left1Middle3 5 1)) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem leftFinal3_case_5_1_row_1_1_0 : (((-1 : ℤ) ^ (leftScaleBit 3 5 1).val * positiveScale (leftScaleExponent 3 5 1)) •
      (rowColumnMul HexagonRowColumn351.rows_assocBCA HexagonRowColumn351.cols_left0)) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 3 5 1) • (left1Middle3 5 1)) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem leftFinal3_case_5_1_row_1_1_1 : (((-1 : ℤ) ^ (leftScaleBit 3 5 1).val * positiveScale (leftScaleExponent 3 5 1)) •
      (rowColumnMul HexagonRowColumn351.rows_assocBCA HexagonRowColumn351.cols_left0)) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 3 5 1) • (left1Middle3 5 1)) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem leftFinal3_case_5_1_row_1_2_0 : (((-1 : ℤ) ^ (leftScaleBit 3 5 1).val * positiveScale (leftScaleExponent 3 5 1)) •
      (rowColumnMul HexagonRowColumn351.rows_assocBCA HexagonRowColumn351.cols_left0)) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 3 5 1) • (left1Middle3 5 1)) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem leftFinal3_case_5_1_row_1_2_1 : (((-1 : ℤ) ^ (leftScaleBit 3 5 1).val * positiveScale (leftScaleExponent 3 5 1)) •
      (rowColumnMul HexagonRowColumn351.rows_assocBCA HexagonRowColumn351.cols_left0)) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 3 5 1) • (left1Middle3 5 1)) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem leftFinal3_case_5_1_row_1_3_0 : (((-1 : ℤ) ^ (leftScaleBit 3 5 1).val * positiveScale (leftScaleExponent 3 5 1)) •
      (rowColumnMul HexagonRowColumn351.rows_assocBCA HexagonRowColumn351.cols_left0)) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 3 5 1) • (left1Middle3 5 1)) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem leftFinal3_case_5_1_row_1_3_1 : (((-1 : ℤ) ^ (leftScaleBit 3 5 1).val * positiveScale (leftScaleExponent 3 5 1)) •
      (rowColumnMul HexagonRowColumn351.rows_assocBCA HexagonRowColumn351.cols_left0)) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 3 5 1) • (left1Middle3 5 1)) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem leftFinal3_case_5_1_checked : ((-1 : ℤ) ^ (leftScaleBit 3 5 1).val * positiveScale (leftScaleExponent 3 5 1)) •
      (rowColumnMul HexagonRowColumn351.rows_assocBCA HexagonRowColumn351.cols_left0) = negativeScale (leftScaleExponent 3 5 1) • (left1Middle3 5 1) := by
  funext r
  fin_cases r
  · exact leftFinal3_case_5_1_row_0_0_0
  · exact leftFinal3_case_5_1_row_0_0_1
  · exact leftFinal3_case_5_1_row_0_1_0
  · exact leftFinal3_case_5_1_row_0_1_1
  · exact leftFinal3_case_5_1_row_0_2_0
  · exact leftFinal3_case_5_1_row_0_2_1
  · exact leftFinal3_case_5_1_row_0_3_0
  · exact leftFinal3_case_5_1_row_0_3_1
  · exact leftFinal3_case_5_1_row_1_0_0
  · exact leftFinal3_case_5_1_row_1_0_1
  · exact leftFinal3_case_5_1_row_1_1_0
  · exact leftFinal3_case_5_1_row_1_1_1
  · exact leftFinal3_case_5_1_row_1_2_0
  · exact leftFinal3_case_5_1_row_1_2_1
  · exact leftFinal3_case_5_1_row_1_3_0
  · exact leftFinal3_case_5_1_row_1_3_1

set_option backward.isDefEq.respectTransparency false in
theorem leftFinal3_case_5_1 : ((-1 : ℤ) ^ (leftScaleBit 3 5 1).val * positiveScale (leftScaleExponent 3 5 1)) •
      (associatorZ 5 1 3 * left0Middle3 5 1) = negativeScale (leftScaleExponent 3 5 1) • (innerRightZ 5 3 1 * left1Middle3 5 1) := by
  simpa only [HexagonAtoms351.assocABC_eq,
    HexagonAtoms351.outerABC_eq,
    HexagonAtoms351.assocBAC_eq,
    HexagonAtoms351.innerABC_eq,
    HexagonAtoms351.innerRightABC_eq,
    HexagonAtoms351.inverseACB_eq,
    HexagonAtoms351.innerACB_eq,
    HexagonAtoms351.assocBCA_eq,
    HexagonAtoms351.innerRightBAC_eq,
    HexagonAtoms351.assocCAB_eq,
    HexagonAtoms351.outerLeftABC_eq,
    HexagonRowColumn351.product0_eq,
    HexagonRowColumn351.product1_eq,
    HexagonRowColumn351.product2_eq,
    HexagonRowColumn351.product3_eq,
    HexagonRowColumn351.product4_eq,
    HexagonRowColumn351.product5_eq,
    HexagonRowColumn351.product6_eq,
    HexagonRowColumn351.product7_eq] using leftFinal3_case_5_1_checked

private theorem rightFinal3_case_5_1_row_0_0_0 : (((-1 : ℤ) ^ (rightScaleBit 3 5 1).val * positiveScale (rightScaleExponent 3 5 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 1 5 : ℤ)) • HexagonAtoms351.outerLeftABC) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 2)) = (negativeScale (rightScaleExponent 3 5 1) • (rowColumnMul HexagonRowColumn351.rows_assocCAB HexagonRowColumn351.cols_right2)) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem rightFinal3_case_5_1_row_0_0_1 : (((-1 : ℤ) ^ (rightScaleBit 3 5 1).val * positiveScale (rightScaleExponent 3 5 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 1 5 : ℤ)) • HexagonAtoms351.outerLeftABC) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 2)) = (negativeScale (rightScaleExponent 3 5 1) • (rowColumnMul HexagonRowColumn351.rows_assocCAB HexagonRowColumn351.cols_right2)) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem rightFinal3_case_5_1_row_1_0_0 : (((-1 : ℤ) ^ (rightScaleBit 3 5 1).val * positiveScale (rightScaleExponent 3 5 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 1 5 : ℤ)) • HexagonAtoms351.outerLeftABC) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 2)) = (negativeScale (rightScaleExponent 3 5 1) • (rowColumnMul HexagonRowColumn351.rows_assocCAB HexagonRowColumn351.cols_right2)) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem rightFinal3_case_5_1_row_1_0_1 : (((-1 : ℤ) ^ (rightScaleBit 3 5 1).val * positiveScale (rightScaleExponent 3 5 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 1 5 : ℤ)) • HexagonAtoms351.outerLeftABC) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 2)) = (negativeScale (rightScaleExponent 3 5 1) • (rowColumnMul HexagonRowColumn351.rows_assocCAB HexagonRowColumn351.cols_right2)) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem rightFinal3_case_5_1_row_2_0_0 : (((-1 : ℤ) ^ (rightScaleBit 3 5 1).val * positiveScale (rightScaleExponent 3 5 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 1 5 : ℤ)) • HexagonAtoms351.outerLeftABC) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 2)) = (negativeScale (rightScaleExponent 3 5 1) • (rowColumnMul HexagonRowColumn351.rows_assocCAB HexagonRowColumn351.cols_right2)) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem rightFinal3_case_5_1_row_2_0_1 : (((-1 : ℤ) ^ (rightScaleBit 3 5 1).val * positiveScale (rightScaleExponent 3 5 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 1 5 : ℤ)) • HexagonAtoms351.outerLeftABC) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 2)) = (negativeScale (rightScaleExponent 3 5 1) • (rowColumnMul HexagonRowColumn351.rows_assocCAB HexagonRowColumn351.cols_right2)) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem rightFinal3_case_5_1_row_3_0_0 : (((-1 : ℤ) ^ (rightScaleBit 3 5 1).val * positiveScale (rightScaleExponent 3 5 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 1 5 : ℤ)) • HexagonAtoms351.outerLeftABC) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 2)) = (negativeScale (rightScaleExponent 3 5 1) • (rowColumnMul HexagonRowColumn351.rows_assocCAB HexagonRowColumn351.cols_right2)) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem rightFinal3_case_5_1_row_3_0_1 : (((-1 : ℤ) ^ (rightScaleBit 3 5 1).val * positiveScale (rightScaleExponent 3 5 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 1 5 : ℤ)) • HexagonAtoms351.outerLeftABC) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 2)) = (negativeScale (rightScaleExponent 3 5 1) • (rowColumnMul HexagonRowColumn351.rows_assocCAB HexagonRowColumn351.cols_right2)) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem rightFinal3_case_5_1_row_4_0_0 : (((-1 : ℤ) ^ (rightScaleBit 3 5 1).val * positiveScale (rightScaleExponent 3 5 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 1 5 : ℤ)) • HexagonAtoms351.outerLeftABC) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 2)) = (negativeScale (rightScaleExponent 3 5 1) • (rowColumnMul HexagonRowColumn351.rows_assocCAB HexagonRowColumn351.cols_right2)) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem rightFinal3_case_5_1_row_4_0_1 : (((-1 : ℤ) ^ (rightScaleBit 3 5 1).val * positiveScale (rightScaleExponent 3 5 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 1 5 : ℤ)) • HexagonAtoms351.outerLeftABC) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 2)) = (negativeScale (rightScaleExponent 3 5 1) • (rowColumnMul HexagonRowColumn351.rows_assocCAB HexagonRowColumn351.cols_right2)) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem rightFinal3_case_5_1_row_5_0_0 : (((-1 : ℤ) ^ (rightScaleBit 3 5 1).val * positiveScale (rightScaleExponent 3 5 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 1 5 : ℤ)) • HexagonAtoms351.outerLeftABC) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 2)) = (negativeScale (rightScaleExponent 3 5 1) • (rowColumnMul HexagonRowColumn351.rows_assocCAB HexagonRowColumn351.cols_right2)) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem rightFinal3_case_5_1_row_5_0_1 : (((-1 : ℤ) ^ (rightScaleBit 3 5 1).val * positiveScale (rightScaleExponent 3 5 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 1 5 : ℤ)) • HexagonAtoms351.outerLeftABC) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 2)) = (negativeScale (rightScaleExponent 3 5 1) • (rowColumnMul HexagonRowColumn351.rows_assocCAB HexagonRowColumn351.cols_right2)) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem rightFinal3_case_5_1_row_6_0_0 : (((-1 : ℤ) ^ (rightScaleBit 3 5 1).val * positiveScale (rightScaleExponent 3 5 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 1 5 : ℤ)) • HexagonAtoms351.outerLeftABC) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 2)) = (negativeScale (rightScaleExponent 3 5 1) • (rowColumnMul HexagonRowColumn351.rows_assocCAB HexagonRowColumn351.cols_right2)) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem rightFinal3_case_5_1_row_6_0_1 : (((-1 : ℤ) ^ (rightScaleBit 3 5 1).val * positiveScale (rightScaleExponent 3 5 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 1 5 : ℤ)) • HexagonAtoms351.outerLeftABC) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 2)) = (negativeScale (rightScaleExponent 3 5 1) • (rowColumnMul HexagonRowColumn351.rows_assocCAB HexagonRowColumn351.cols_right2)) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem rightFinal3_case_5_1_row_7_0_0 : (((-1 : ℤ) ^ (rightScaleBit 3 5 1).val * positiveScale (rightScaleExponent 3 5 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 1 5 : ℤ)) • HexagonAtoms351.outerLeftABC) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 2)) = (negativeScale (rightScaleExponent 3 5 1) • (rowColumnMul HexagonRowColumn351.rows_assocCAB HexagonRowColumn351.cols_right2)) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem rightFinal3_case_5_1_row_7_0_1 : (((-1 : ℤ) ^ (rightScaleBit 3 5 1).val * positiveScale (rightScaleExponent 3 5 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 1 5 : ℤ)) • HexagonAtoms351.outerLeftABC) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 2)) = (negativeScale (rightScaleExponent 3 5 1) • (rowColumnMul HexagonRowColumn351.rows_assocCAB HexagonRowColumn351.cols_right2)) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem rightFinal3_case_5_1_checked : ((-1 : ℤ) ^ (rightScaleBit 3 5 1).val * positiveScale (rightScaleExponent 3 5 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 1 5 : ℤ)) • HexagonAtoms351.outerLeftABC = negativeScale (rightScaleExponent 3 5 1) • (rowColumnMul HexagonRowColumn351.rows_assocCAB HexagonRowColumn351.cols_right2) := by
  funext r
  fin_cases r
  · exact rightFinal3_case_5_1_row_0_0_0
  · exact rightFinal3_case_5_1_row_0_0_1
  · exact rightFinal3_case_5_1_row_1_0_0
  · exact rightFinal3_case_5_1_row_1_0_1
  · exact rightFinal3_case_5_1_row_2_0_0
  · exact rightFinal3_case_5_1_row_2_0_1
  · exact rightFinal3_case_5_1_row_3_0_0
  · exact rightFinal3_case_5_1_row_3_0_1
  · exact rightFinal3_case_5_1_row_4_0_0
  · exact rightFinal3_case_5_1_row_4_0_1
  · exact rightFinal3_case_5_1_row_5_0_0
  · exact rightFinal3_case_5_1_row_5_0_1
  · exact rightFinal3_case_5_1_row_6_0_0
  · exact rightFinal3_case_5_1_row_6_0_1
  · exact rightFinal3_case_5_1_row_7_0_0
  · exact rightFinal3_case_5_1_row_7_0_1

set_option backward.isDefEq.respectTransparency false in
theorem rightFinal3_case_5_1 : ((-1 : ℤ) ^ (rightScaleBit 3 5 1).val * positiveScale (rightScaleExponent 3 5 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 1 5 : ℤ)) • outerLeftZ 3 5 1 = negativeScale (rightScaleExponent 3 5 1) • (associatorZ 1 3 5 * right2Middle3 5 1) := by
  simpa only [HexagonAtoms351.assocABC_eq,
    HexagonAtoms351.outerABC_eq,
    HexagonAtoms351.assocBAC_eq,
    HexagonAtoms351.innerABC_eq,
    HexagonAtoms351.innerRightABC_eq,
    HexagonAtoms351.inverseACB_eq,
    HexagonAtoms351.innerACB_eq,
    HexagonAtoms351.assocBCA_eq,
    HexagonAtoms351.innerRightBAC_eq,
    HexagonAtoms351.assocCAB_eq,
    HexagonAtoms351.outerLeftABC_eq,
    HexagonRowColumn351.product0_eq,
    HexagonRowColumn351.product1_eq,
    HexagonRowColumn351.product2_eq,
    HexagonRowColumn351.product3_eq,
    HexagonRowColumn351.product4_eq,
    HexagonRowColumn351.product5_eq,
    HexagonRowColumn351.product6_eq,
    HexagonRowColumn351.product7_eq] using rightFinal3_case_5_1_checked

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonCases3
