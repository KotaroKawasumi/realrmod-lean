import RMod.BrundanEllis.StackingReferenceHexagonMiddle3
import RMod.BrundanEllis.StackingReferenceSparseMatrixCheck
import RMod.BrundanEllis.StackingReferenceHexagonAtoms313
import RMod.BrundanEllis.StackingReferenceHexagonRowColumn313

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

private theorem left0Middle3_eq_case_1_3_row_0_0_0 : (left0Middle3 1 3) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (HexagonAtoms313.assocABC) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle3_eq_case_1_3_row_0_0_1 : (left0Middle3 1 3) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (HexagonAtoms313.assocABC) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle3_eq_case_1_3_row_0_1_0 : (left0Middle3 1 3) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (HexagonAtoms313.assocABC) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle3_eq_case_1_3_row_0_1_1 : (left0Middle3 1 3) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (HexagonAtoms313.assocABC) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle3_eq_case_1_3_row_0_2_0 : (left0Middle3 1 3) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (HexagonAtoms313.assocABC) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle3_eq_case_1_3_row_0_2_1 : (left0Middle3 1 3) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (HexagonAtoms313.assocABC) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle3_eq_case_1_3_row_0_3_0 : (left0Middle3 1 3) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (HexagonAtoms313.assocABC) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle3_eq_case_1_3_row_0_3_1 : (left0Middle3 1 3) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (HexagonAtoms313.assocABC) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle3_eq_case_1_3_row_1_0_0 : (left0Middle3 1 3) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (HexagonAtoms313.assocABC) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle3_eq_case_1_3_row_1_0_1 : (left0Middle3 1 3) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (HexagonAtoms313.assocABC) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle3_eq_case_1_3_row_1_1_0 : (left0Middle3 1 3) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (HexagonAtoms313.assocABC) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle3_eq_case_1_3_row_1_1_1 : (left0Middle3 1 3) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (HexagonAtoms313.assocABC) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle3_eq_case_1_3_row_1_2_0 : (left0Middle3 1 3) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (HexagonAtoms313.assocABC) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle3_eq_case_1_3_row_1_2_1 : (left0Middle3 1 3) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (HexagonAtoms313.assocABC) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle3_eq_case_1_3_row_1_3_0 : (left0Middle3 1 3) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (HexagonAtoms313.assocABC) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle3_eq_case_1_3_row_1_3_1 : (left0Middle3 1 3) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (HexagonAtoms313.assocABC) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle3_eq_case_1_3_checked : left0Middle3 1 3 = HexagonAtoms313.assocABC := by
  funext r
  fin_cases r
  · exact left0Middle3_eq_case_1_3_row_0_0_0
  · exact left0Middle3_eq_case_1_3_row_0_0_1
  · exact left0Middle3_eq_case_1_3_row_0_1_0
  · exact left0Middle3_eq_case_1_3_row_0_1_1
  · exact left0Middle3_eq_case_1_3_row_0_2_0
  · exact left0Middle3_eq_case_1_3_row_0_2_1
  · exact left0Middle3_eq_case_1_3_row_0_3_0
  · exact left0Middle3_eq_case_1_3_row_0_3_1
  · exact left0Middle3_eq_case_1_3_row_1_0_0
  · exact left0Middle3_eq_case_1_3_row_1_0_1
  · exact left0Middle3_eq_case_1_3_row_1_1_0
  · exact left0Middle3_eq_case_1_3_row_1_1_1
  · exact left0Middle3_eq_case_1_3_row_1_2_0
  · exact left0Middle3_eq_case_1_3_row_1_2_1
  · exact left0Middle3_eq_case_1_3_row_1_3_0
  · exact left0Middle3_eq_case_1_3_row_1_3_1

set_option backward.isDefEq.respectTransparency false in
theorem left0Middle3_eq_case_1_3 : left0Middle3 1 3 = outerRightZ 3 1 3 * associatorZ 3 1 3 := by
  simpa only [HexagonAtoms313.assocABC_eq,
    HexagonAtoms313.outerABC_eq,
    HexagonAtoms313.assocBAC_eq,
    HexagonAtoms313.innerABC_eq,
    HexagonAtoms313.innerRightABC_eq,
    HexagonAtoms313.inverseACB_eq,
    HexagonAtoms313.innerACB_eq,
    HexagonAtoms313.assocBCA_eq,
    HexagonAtoms313.innerRightBAC_eq,
    HexagonAtoms313.assocCAB_eq,
    HexagonAtoms313.outerLeftABC_eq,
    HexagonRowColumn313.assocBCA_alias,
    HexagonRowColumn313.product0_eq,
    HexagonRowColumn313.product1_eq,
    HexagonRowColumn313.product2_eq,
    HexagonRowColumn313.product3_eq,
    HexagonRowColumn313.product4_eq,
    HexagonRowColumn313.product5_eq,
    HexagonRowColumn313.product6_eq,
    HexagonRowColumn313.product7_eq] using left0Middle3_eq_case_1_3_checked

private theorem left1Middle3_eq_case_1_3_row_0_0_0 : (left1Middle3 1 3) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (HexagonAtoms313.assocBAC) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle3_eq_case_1_3_row_0_0_1 : (left1Middle3 1 3) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (HexagonAtoms313.assocBAC) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle3_eq_case_1_3_row_0_1_0 : (left1Middle3 1 3) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (HexagonAtoms313.assocBAC) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle3_eq_case_1_3_row_0_1_1 : (left1Middle3 1 3) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (HexagonAtoms313.assocBAC) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle3_eq_case_1_3_row_1_0_0 : (left1Middle3 1 3) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (HexagonAtoms313.assocBAC) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle3_eq_case_1_3_row_1_0_1 : (left1Middle3 1 3) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (HexagonAtoms313.assocBAC) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle3_eq_case_1_3_row_1_1_0 : (left1Middle3 1 3) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (HexagonAtoms313.assocBAC) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle3_eq_case_1_3_row_1_1_1 : (left1Middle3 1 3) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (HexagonAtoms313.assocBAC) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle3_eq_case_1_3_row_2_0_0 : (left1Middle3 1 3) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (HexagonAtoms313.assocBAC) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle3_eq_case_1_3_row_2_0_1 : (left1Middle3 1 3) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (HexagonAtoms313.assocBAC) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle3_eq_case_1_3_row_2_1_0 : (left1Middle3 1 3) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (HexagonAtoms313.assocBAC) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle3_eq_case_1_3_row_2_1_1 : (left1Middle3 1 3) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (HexagonAtoms313.assocBAC) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle3_eq_case_1_3_row_3_0_0 : (left1Middle3 1 3) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (HexagonAtoms313.assocBAC) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle3_eq_case_1_3_row_3_0_1 : (left1Middle3 1 3) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (HexagonAtoms313.assocBAC) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle3_eq_case_1_3_row_3_1_0 : (left1Middle3 1 3) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (HexagonAtoms313.assocBAC) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle3_eq_case_1_3_row_3_1_1 : (left1Middle3 1 3) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (HexagonAtoms313.assocBAC) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle3_eq_case_1_3_checked : left1Middle3 1 3 = HexagonAtoms313.assocBAC := by
  funext r
  fin_cases r
  · exact left1Middle3_eq_case_1_3_row_0_0_0
  · exact left1Middle3_eq_case_1_3_row_0_0_1
  · exact left1Middle3_eq_case_1_3_row_0_1_0
  · exact left1Middle3_eq_case_1_3_row_0_1_1
  · exact left1Middle3_eq_case_1_3_row_1_0_0
  · exact left1Middle3_eq_case_1_3_row_1_0_1
  · exact left1Middle3_eq_case_1_3_row_1_1_0
  · exact left1Middle3_eq_case_1_3_row_1_1_1
  · exact left1Middle3_eq_case_1_3_row_2_0_0
  · exact left1Middle3_eq_case_1_3_row_2_0_1
  · exact left1Middle3_eq_case_1_3_row_2_1_0
  · exact left1Middle3_eq_case_1_3_row_2_1_1
  · exact left1Middle3_eq_case_1_3_row_3_0_0
  · exact left1Middle3_eq_case_1_3_row_3_0_1
  · exact left1Middle3_eq_case_1_3_row_3_1_0
  · exact left1Middle3_eq_case_1_3_row_3_1_1

set_option backward.isDefEq.respectTransparency false in
theorem left1Middle3_eq_case_1_3 : left1Middle3 1 3 = associatorZ 1 3 3 * innerLeftZ 3 1 3 := by
  simpa only [HexagonAtoms313.assocABC_eq,
    HexagonAtoms313.outerABC_eq,
    HexagonAtoms313.assocBAC_eq,
    HexagonAtoms313.innerABC_eq,
    HexagonAtoms313.innerRightABC_eq,
    HexagonAtoms313.inverseACB_eq,
    HexagonAtoms313.innerACB_eq,
    HexagonAtoms313.assocBCA_eq,
    HexagonAtoms313.innerRightBAC_eq,
    HexagonAtoms313.assocCAB_eq,
    HexagonAtoms313.outerLeftABC_eq,
    HexagonRowColumn313.assocBCA_alias,
    HexagonRowColumn313.product0_eq,
    HexagonRowColumn313.product1_eq,
    HexagonRowColumn313.product2_eq,
    HexagonRowColumn313.product3_eq,
    HexagonRowColumn313.product4_eq,
    HexagonRowColumn313.product5_eq,
    HexagonRowColumn313.product6_eq,
    HexagonRowColumn313.product7_eq] using left1Middle3_eq_case_1_3_checked

private theorem right0Middle3_eq_case_1_3_row_0_0_0 : (right0Middle3 1 3) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (HexagonAtoms313.assocABC) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle3_eq_case_1_3_row_0_0_1 : (right0Middle3 1 3) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (HexagonAtoms313.assocABC) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle3_eq_case_1_3_row_0_1_0 : (right0Middle3 1 3) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (HexagonAtoms313.assocABC) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle3_eq_case_1_3_row_0_1_1 : (right0Middle3 1 3) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (HexagonAtoms313.assocABC) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle3_eq_case_1_3_row_0_2_0 : (right0Middle3 1 3) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (HexagonAtoms313.assocABC) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle3_eq_case_1_3_row_0_2_1 : (right0Middle3 1 3) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (HexagonAtoms313.assocABC) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle3_eq_case_1_3_row_0_3_0 : (right0Middle3 1 3) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (HexagonAtoms313.assocABC) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle3_eq_case_1_3_row_0_3_1 : (right0Middle3 1 3) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (HexagonAtoms313.assocABC) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle3_eq_case_1_3_row_1_0_0 : (right0Middle3 1 3) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (HexagonAtoms313.assocABC) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle3_eq_case_1_3_row_1_0_1 : (right0Middle3 1 3) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (HexagonAtoms313.assocABC) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle3_eq_case_1_3_row_1_1_0 : (right0Middle3 1 3) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (HexagonAtoms313.assocABC) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle3_eq_case_1_3_row_1_1_1 : (right0Middle3 1 3) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (HexagonAtoms313.assocABC) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle3_eq_case_1_3_row_1_2_0 : (right0Middle3 1 3) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (HexagonAtoms313.assocABC) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle3_eq_case_1_3_row_1_2_1 : (right0Middle3 1 3) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (HexagonAtoms313.assocABC) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle3_eq_case_1_3_row_1_3_0 : (right0Middle3 1 3) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (HexagonAtoms313.assocABC) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle3_eq_case_1_3_row_1_3_1 : (right0Middle3 1 3) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (HexagonAtoms313.assocABC) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle3_eq_case_1_3_checked : right0Middle3 1 3 = HexagonAtoms313.assocABC := by
  funext r
  fin_cases r
  · exact right0Middle3_eq_case_1_3_row_0_0_0
  · exact right0Middle3_eq_case_1_3_row_0_0_1
  · exact right0Middle3_eq_case_1_3_row_0_1_0
  · exact right0Middle3_eq_case_1_3_row_0_1_1
  · exact right0Middle3_eq_case_1_3_row_0_2_0
  · exact right0Middle3_eq_case_1_3_row_0_2_1
  · exact right0Middle3_eq_case_1_3_row_0_3_0
  · exact right0Middle3_eq_case_1_3_row_0_3_1
  · exact right0Middle3_eq_case_1_3_row_1_0_0
  · exact right0Middle3_eq_case_1_3_row_1_0_1
  · exact right0Middle3_eq_case_1_3_row_1_1_0
  · exact right0Middle3_eq_case_1_3_row_1_1_1
  · exact right0Middle3_eq_case_1_3_row_1_2_0
  · exact right0Middle3_eq_case_1_3_row_1_2_1
  · exact right0Middle3_eq_case_1_3_row_1_3_0
  · exact right0Middle3_eq_case_1_3_row_1_3_1

set_option backward.isDefEq.respectTransparency false in
theorem right0Middle3_eq_case_1_3 : right0Middle3 1 3 = innerRightZ 3 1 3 * associatorZ 3 1 3 := by
  simpa only [HexagonAtoms313.assocABC_eq,
    HexagonAtoms313.outerABC_eq,
    HexagonAtoms313.assocBAC_eq,
    HexagonAtoms313.innerABC_eq,
    HexagonAtoms313.innerRightABC_eq,
    HexagonAtoms313.inverseACB_eq,
    HexagonAtoms313.innerACB_eq,
    HexagonAtoms313.assocBCA_eq,
    HexagonAtoms313.innerRightBAC_eq,
    HexagonAtoms313.assocCAB_eq,
    HexagonAtoms313.outerLeftABC_eq,
    HexagonRowColumn313.assocBCA_alias,
    HexagonRowColumn313.product0_eq,
    HexagonRowColumn313.product1_eq,
    HexagonRowColumn313.product2_eq,
    HexagonRowColumn313.product3_eq,
    HexagonRowColumn313.product4_eq,
    HexagonRowColumn313.product5_eq,
    HexagonRowColumn313.product6_eq,
    HexagonRowColumn313.product7_eq] using right0Middle3_eq_case_1_3_checked

private theorem right1Middle3_eq_case_1_3_row_0_0_0 : (right1Middle3 1 3) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn313.rows_inverseACB HexagonRowColumn313.cols_right0) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle3_eq_case_1_3_row_0_0_1 : (right1Middle3 1 3) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn313.rows_inverseACB HexagonRowColumn313.cols_right0) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle3_eq_case_1_3_row_0_1_0 : (right1Middle3 1 3) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn313.rows_inverseACB HexagonRowColumn313.cols_right0) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle3_eq_case_1_3_row_0_1_1 : (right1Middle3 1 3) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn313.rows_inverseACB HexagonRowColumn313.cols_right0) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle3_eq_case_1_3_row_1_0_0 : (right1Middle3 1 3) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn313.rows_inverseACB HexagonRowColumn313.cols_right0) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle3_eq_case_1_3_row_1_0_1 : (right1Middle3 1 3) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn313.rows_inverseACB HexagonRowColumn313.cols_right0) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle3_eq_case_1_3_row_1_1_0 : (right1Middle3 1 3) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn313.rows_inverseACB HexagonRowColumn313.cols_right0) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle3_eq_case_1_3_row_1_1_1 : (right1Middle3 1 3) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn313.rows_inverseACB HexagonRowColumn313.cols_right0) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle3_eq_case_1_3_row_2_0_0 : (right1Middle3 1 3) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn313.rows_inverseACB HexagonRowColumn313.cols_right0) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle3_eq_case_1_3_row_2_0_1 : (right1Middle3 1 3) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn313.rows_inverseACB HexagonRowColumn313.cols_right0) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle3_eq_case_1_3_row_2_1_0 : (right1Middle3 1 3) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn313.rows_inverseACB HexagonRowColumn313.cols_right0) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle3_eq_case_1_3_row_2_1_1 : (right1Middle3 1 3) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn313.rows_inverseACB HexagonRowColumn313.cols_right0) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle3_eq_case_1_3_row_3_0_0 : (right1Middle3 1 3) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn313.rows_inverseACB HexagonRowColumn313.cols_right0) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle3_eq_case_1_3_row_3_0_1 : (right1Middle3 1 3) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn313.rows_inverseACB HexagonRowColumn313.cols_right0) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle3_eq_case_1_3_row_3_1_0 : (right1Middle3 1 3) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn313.rows_inverseACB HexagonRowColumn313.cols_right0) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle3_eq_case_1_3_row_3_1_1 : (right1Middle3 1 3) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn313.rows_inverseACB HexagonRowColumn313.cols_right0) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle3_eq_case_1_3_checked : right1Middle3 1 3 = rowColumnMul HexagonRowColumn313.rows_inverseACB HexagonRowColumn313.cols_right0 := by
  funext r
  fin_cases r
  · exact right1Middle3_eq_case_1_3_row_0_0_0
  · exact right1Middle3_eq_case_1_3_row_0_0_1
  · exact right1Middle3_eq_case_1_3_row_0_1_0
  · exact right1Middle3_eq_case_1_3_row_0_1_1
  · exact right1Middle3_eq_case_1_3_row_1_0_0
  · exact right1Middle3_eq_case_1_3_row_1_0_1
  · exact right1Middle3_eq_case_1_3_row_1_1_0
  · exact right1Middle3_eq_case_1_3_row_1_1_1
  · exact right1Middle3_eq_case_1_3_row_2_0_0
  · exact right1Middle3_eq_case_1_3_row_2_0_1
  · exact right1Middle3_eq_case_1_3_row_2_1_0
  · exact right1Middle3_eq_case_1_3_row_2_1_1
  · exact right1Middle3_eq_case_1_3_row_3_0_0
  · exact right1Middle3_eq_case_1_3_row_3_0_1
  · exact right1Middle3_eq_case_1_3_row_3_1_0
  · exact right1Middle3_eq_case_1_3_row_3_1_1

set_option backward.isDefEq.respectTransparency false in
theorem right1Middle3_eq_case_1_3 : right1Middle3 1 3 = associatorInverseZ 3 3 1 * right0Middle3 1 3 := by
  simpa only [HexagonAtoms313.assocABC_eq,
    HexagonAtoms313.outerABC_eq,
    HexagonAtoms313.assocBAC_eq,
    HexagonAtoms313.innerABC_eq,
    HexagonAtoms313.innerRightABC_eq,
    HexagonAtoms313.inverseACB_eq,
    HexagonAtoms313.innerACB_eq,
    HexagonAtoms313.assocBCA_eq,
    HexagonAtoms313.innerRightBAC_eq,
    HexagonAtoms313.assocCAB_eq,
    HexagonAtoms313.outerLeftABC_eq,
    HexagonRowColumn313.assocBCA_alias,
    HexagonRowColumn313.product0_eq,
    HexagonRowColumn313.product1_eq,
    HexagonRowColumn313.product2_eq,
    HexagonRowColumn313.product3_eq,
    HexagonRowColumn313.product4_eq,
    HexagonRowColumn313.product5_eq,
    HexagonRowColumn313.product6_eq,
    HexagonRowColumn313.product7_eq] using right1Middle3_eq_case_1_3_checked

private theorem right2Middle3_eq_case_1_3_row_0_0_0 : (right2Middle3 1 3) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn313.rows_innerACB HexagonRowColumn313.cols_right1) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle3_eq_case_1_3_row_0_0_1 : (right2Middle3 1 3) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn313.rows_innerACB HexagonRowColumn313.cols_right1) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle3_eq_case_1_3_row_0_1_0 : (right2Middle3 1 3) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn313.rows_innerACB HexagonRowColumn313.cols_right1) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle3_eq_case_1_3_row_0_1_1 : (right2Middle3 1 3) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn313.rows_innerACB HexagonRowColumn313.cols_right1) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle3_eq_case_1_3_row_1_0_0 : (right2Middle3 1 3) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn313.rows_innerACB HexagonRowColumn313.cols_right1) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle3_eq_case_1_3_row_1_0_1 : (right2Middle3 1 3) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn313.rows_innerACB HexagonRowColumn313.cols_right1) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle3_eq_case_1_3_row_1_1_0 : (right2Middle3 1 3) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn313.rows_innerACB HexagonRowColumn313.cols_right1) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle3_eq_case_1_3_row_1_1_1 : (right2Middle3 1 3) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn313.rows_innerACB HexagonRowColumn313.cols_right1) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle3_eq_case_1_3_row_2_0_0 : (right2Middle3 1 3) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn313.rows_innerACB HexagonRowColumn313.cols_right1) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle3_eq_case_1_3_row_2_0_1 : (right2Middle3 1 3) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn313.rows_innerACB HexagonRowColumn313.cols_right1) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle3_eq_case_1_3_row_2_1_0 : (right2Middle3 1 3) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn313.rows_innerACB HexagonRowColumn313.cols_right1) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle3_eq_case_1_3_row_2_1_1 : (right2Middle3 1 3) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn313.rows_innerACB HexagonRowColumn313.cols_right1) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle3_eq_case_1_3_row_3_0_0 : (right2Middle3 1 3) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn313.rows_innerACB HexagonRowColumn313.cols_right1) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle3_eq_case_1_3_row_3_0_1 : (right2Middle3 1 3) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn313.rows_innerACB HexagonRowColumn313.cols_right1) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle3_eq_case_1_3_row_3_1_0 : (right2Middle3 1 3) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn313.rows_innerACB HexagonRowColumn313.cols_right1) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle3_eq_case_1_3_row_3_1_1 : (right2Middle3 1 3) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn313.rows_innerACB HexagonRowColumn313.cols_right1) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle3_eq_case_1_3_checked : right2Middle3 1 3 = rowColumnMul HexagonRowColumn313.rows_innerACB HexagonRowColumn313.cols_right1 := by
  funext r
  fin_cases r
  · exact right2Middle3_eq_case_1_3_row_0_0_0
  · exact right2Middle3_eq_case_1_3_row_0_0_1
  · exact right2Middle3_eq_case_1_3_row_0_1_0
  · exact right2Middle3_eq_case_1_3_row_0_1_1
  · exact right2Middle3_eq_case_1_3_row_1_0_0
  · exact right2Middle3_eq_case_1_3_row_1_0_1
  · exact right2Middle3_eq_case_1_3_row_1_1_0
  · exact right2Middle3_eq_case_1_3_row_1_1_1
  · exact right2Middle3_eq_case_1_3_row_2_0_0
  · exact right2Middle3_eq_case_1_3_row_2_0_1
  · exact right2Middle3_eq_case_1_3_row_2_1_0
  · exact right2Middle3_eq_case_1_3_row_2_1_1
  · exact right2Middle3_eq_case_1_3_row_3_0_0
  · exact right2Middle3_eq_case_1_3_row_3_0_1
  · exact right2Middle3_eq_case_1_3_row_3_1_0
  · exact right2Middle3_eq_case_1_3_row_3_1_1

set_option backward.isDefEq.respectTransparency false in
theorem right2Middle3_eq_case_1_3 : right2Middle3 1 3 = innerLeftZ 3 3 1 * right1Middle3 1 3 := by
  simpa only [HexagonAtoms313.assocABC_eq,
    HexagonAtoms313.outerABC_eq,
    HexagonAtoms313.assocBAC_eq,
    HexagonAtoms313.innerABC_eq,
    HexagonAtoms313.innerRightABC_eq,
    HexagonAtoms313.inverseACB_eq,
    HexagonAtoms313.innerACB_eq,
    HexagonAtoms313.assocBCA_eq,
    HexagonAtoms313.innerRightBAC_eq,
    HexagonAtoms313.assocCAB_eq,
    HexagonAtoms313.outerLeftABC_eq,
    HexagonRowColumn313.assocBCA_alias,
    HexagonRowColumn313.product0_eq,
    HexagonRowColumn313.product1_eq,
    HexagonRowColumn313.product2_eq,
    HexagonRowColumn313.product3_eq,
    HexagonRowColumn313.product4_eq,
    HexagonRowColumn313.product5_eq,
    HexagonRowColumn313.product6_eq,
    HexagonRowColumn313.product7_eq] using right2Middle3_eq_case_1_3_checked

private theorem leftFinal3_case_1_3_row_0_0_0 : (((-1 : ℤ) ^ (leftScaleBit 3 1 3).val * positiveScale (leftScaleExponent 3 1 3)) •
      (rowColumnMul HexagonRowColumn313.rows_assocBAC HexagonRowColumn313.cols_left0)) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (negativeScale (leftScaleExponent 3 1 3) • (rowColumnMul HexagonRowColumn313.rows_innerRightBAC HexagonRowColumn313.cols_left1)) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal3_case_1_3_row_0_0_1 : (((-1 : ℤ) ^ (leftScaleBit 3 1 3).val * positiveScale (leftScaleExponent 3 1 3)) •
      (rowColumnMul HexagonRowColumn313.rows_assocBAC HexagonRowColumn313.cols_left0)) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (negativeScale (leftScaleExponent 3 1 3) • (rowColumnMul HexagonRowColumn313.rows_innerRightBAC HexagonRowColumn313.cols_left1)) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal3_case_1_3_row_0_1_0 : (((-1 : ℤ) ^ (leftScaleBit 3 1 3).val * positiveScale (leftScaleExponent 3 1 3)) •
      (rowColumnMul HexagonRowColumn313.rows_assocBAC HexagonRowColumn313.cols_left0)) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (negativeScale (leftScaleExponent 3 1 3) • (rowColumnMul HexagonRowColumn313.rows_innerRightBAC HexagonRowColumn313.cols_left1)) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal3_case_1_3_row_0_1_1 : (((-1 : ℤ) ^ (leftScaleBit 3 1 3).val * positiveScale (leftScaleExponent 3 1 3)) •
      (rowColumnMul HexagonRowColumn313.rows_assocBAC HexagonRowColumn313.cols_left0)) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (negativeScale (leftScaleExponent 3 1 3) • (rowColumnMul HexagonRowColumn313.rows_innerRightBAC HexagonRowColumn313.cols_left1)) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal3_case_1_3_row_1_0_0 : (((-1 : ℤ) ^ (leftScaleBit 3 1 3).val * positiveScale (leftScaleExponent 3 1 3)) •
      (rowColumnMul HexagonRowColumn313.rows_assocBAC HexagonRowColumn313.cols_left0)) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (negativeScale (leftScaleExponent 3 1 3) • (rowColumnMul HexagonRowColumn313.rows_innerRightBAC HexagonRowColumn313.cols_left1)) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal3_case_1_3_row_1_0_1 : (((-1 : ℤ) ^ (leftScaleBit 3 1 3).val * positiveScale (leftScaleExponent 3 1 3)) •
      (rowColumnMul HexagonRowColumn313.rows_assocBAC HexagonRowColumn313.cols_left0)) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (negativeScale (leftScaleExponent 3 1 3) • (rowColumnMul HexagonRowColumn313.rows_innerRightBAC HexagonRowColumn313.cols_left1)) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal3_case_1_3_row_1_1_0 : (((-1 : ℤ) ^ (leftScaleBit 3 1 3).val * positiveScale (leftScaleExponent 3 1 3)) •
      (rowColumnMul HexagonRowColumn313.rows_assocBAC HexagonRowColumn313.cols_left0)) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (negativeScale (leftScaleExponent 3 1 3) • (rowColumnMul HexagonRowColumn313.rows_innerRightBAC HexagonRowColumn313.cols_left1)) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal3_case_1_3_row_1_1_1 : (((-1 : ℤ) ^ (leftScaleBit 3 1 3).val * positiveScale (leftScaleExponent 3 1 3)) •
      (rowColumnMul HexagonRowColumn313.rows_assocBAC HexagonRowColumn313.cols_left0)) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (negativeScale (leftScaleExponent 3 1 3) • (rowColumnMul HexagonRowColumn313.rows_innerRightBAC HexagonRowColumn313.cols_left1)) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal3_case_1_3_row_2_0_0 : (((-1 : ℤ) ^ (leftScaleBit 3 1 3).val * positiveScale (leftScaleExponent 3 1 3)) •
      (rowColumnMul HexagonRowColumn313.rows_assocBAC HexagonRowColumn313.cols_left0)) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (negativeScale (leftScaleExponent 3 1 3) • (rowColumnMul HexagonRowColumn313.rows_innerRightBAC HexagonRowColumn313.cols_left1)) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal3_case_1_3_row_2_0_1 : (((-1 : ℤ) ^ (leftScaleBit 3 1 3).val * positiveScale (leftScaleExponent 3 1 3)) •
      (rowColumnMul HexagonRowColumn313.rows_assocBAC HexagonRowColumn313.cols_left0)) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (negativeScale (leftScaleExponent 3 1 3) • (rowColumnMul HexagonRowColumn313.rows_innerRightBAC HexagonRowColumn313.cols_left1)) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal3_case_1_3_row_2_1_0 : (((-1 : ℤ) ^ (leftScaleBit 3 1 3).val * positiveScale (leftScaleExponent 3 1 3)) •
      (rowColumnMul HexagonRowColumn313.rows_assocBAC HexagonRowColumn313.cols_left0)) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (negativeScale (leftScaleExponent 3 1 3) • (rowColumnMul HexagonRowColumn313.rows_innerRightBAC HexagonRowColumn313.cols_left1)) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal3_case_1_3_row_2_1_1 : (((-1 : ℤ) ^ (leftScaleBit 3 1 3).val * positiveScale (leftScaleExponent 3 1 3)) •
      (rowColumnMul HexagonRowColumn313.rows_assocBAC HexagonRowColumn313.cols_left0)) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (negativeScale (leftScaleExponent 3 1 3) • (rowColumnMul HexagonRowColumn313.rows_innerRightBAC HexagonRowColumn313.cols_left1)) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal3_case_1_3_row_3_0_0 : (((-1 : ℤ) ^ (leftScaleBit 3 1 3).val * positiveScale (leftScaleExponent 3 1 3)) •
      (rowColumnMul HexagonRowColumn313.rows_assocBAC HexagonRowColumn313.cols_left0)) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (negativeScale (leftScaleExponent 3 1 3) • (rowColumnMul HexagonRowColumn313.rows_innerRightBAC HexagonRowColumn313.cols_left1)) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal3_case_1_3_row_3_0_1 : (((-1 : ℤ) ^ (leftScaleBit 3 1 3).val * positiveScale (leftScaleExponent 3 1 3)) •
      (rowColumnMul HexagonRowColumn313.rows_assocBAC HexagonRowColumn313.cols_left0)) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (negativeScale (leftScaleExponent 3 1 3) • (rowColumnMul HexagonRowColumn313.rows_innerRightBAC HexagonRowColumn313.cols_left1)) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal3_case_1_3_row_3_1_0 : (((-1 : ℤ) ^ (leftScaleBit 3 1 3).val * positiveScale (leftScaleExponent 3 1 3)) •
      (rowColumnMul HexagonRowColumn313.rows_assocBAC HexagonRowColumn313.cols_left0)) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (negativeScale (leftScaleExponent 3 1 3) • (rowColumnMul HexagonRowColumn313.rows_innerRightBAC HexagonRowColumn313.cols_left1)) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal3_case_1_3_row_3_1_1 : (((-1 : ℤ) ^ (leftScaleBit 3 1 3).val * positiveScale (leftScaleExponent 3 1 3)) •
      (rowColumnMul HexagonRowColumn313.rows_assocBAC HexagonRowColumn313.cols_left0)) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (negativeScale (leftScaleExponent 3 1 3) • (rowColumnMul HexagonRowColumn313.rows_innerRightBAC HexagonRowColumn313.cols_left1)) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal3_case_1_3_checked : ((-1 : ℤ) ^ (leftScaleBit 3 1 3).val * positiveScale (leftScaleExponent 3 1 3)) •
      (rowColumnMul HexagonRowColumn313.rows_assocBAC HexagonRowColumn313.cols_left0) = negativeScale (leftScaleExponent 3 1 3) • (rowColumnMul HexagonRowColumn313.rows_innerRightBAC HexagonRowColumn313.cols_left1) := by
  funext r
  fin_cases r
  · exact leftFinal3_case_1_3_row_0_0_0
  · exact leftFinal3_case_1_3_row_0_0_1
  · exact leftFinal3_case_1_3_row_0_1_0
  · exact leftFinal3_case_1_3_row_0_1_1
  · exact leftFinal3_case_1_3_row_1_0_0
  · exact leftFinal3_case_1_3_row_1_0_1
  · exact leftFinal3_case_1_3_row_1_1_0
  · exact leftFinal3_case_1_3_row_1_1_1
  · exact leftFinal3_case_1_3_row_2_0_0
  · exact leftFinal3_case_1_3_row_2_0_1
  · exact leftFinal3_case_1_3_row_2_1_0
  · exact leftFinal3_case_1_3_row_2_1_1
  · exact leftFinal3_case_1_3_row_3_0_0
  · exact leftFinal3_case_1_3_row_3_0_1
  · exact leftFinal3_case_1_3_row_3_1_0
  · exact leftFinal3_case_1_3_row_3_1_1

set_option backward.isDefEq.respectTransparency false in
theorem leftFinal3_case_1_3 : ((-1 : ℤ) ^ (leftScaleBit 3 1 3).val * positiveScale (leftScaleExponent 3 1 3)) •
      (associatorZ 1 3 3 * left0Middle3 1 3) = negativeScale (leftScaleExponent 3 1 3) • (innerRightZ 1 3 3 * left1Middle3 1 3) := by
  simpa only [HexagonAtoms313.assocABC_eq,
    HexagonAtoms313.outerABC_eq,
    HexagonAtoms313.assocBAC_eq,
    HexagonAtoms313.innerABC_eq,
    HexagonAtoms313.innerRightABC_eq,
    HexagonAtoms313.inverseACB_eq,
    HexagonAtoms313.innerACB_eq,
    HexagonAtoms313.assocBCA_eq,
    HexagonAtoms313.innerRightBAC_eq,
    HexagonAtoms313.assocCAB_eq,
    HexagonAtoms313.outerLeftABC_eq,
    HexagonRowColumn313.assocBCA_alias,
    HexagonRowColumn313.product0_eq,
    HexagonRowColumn313.product1_eq,
    HexagonRowColumn313.product2_eq,
    HexagonRowColumn313.product3_eq,
    HexagonRowColumn313.product4_eq,
    HexagonRowColumn313.product5_eq,
    HexagonRowColumn313.product6_eq,
    HexagonRowColumn313.product7_eq] using leftFinal3_case_1_3_checked

private theorem rightFinal3_case_1_3_row_0_0_0 : (((-1 : ℤ) ^ (rightScaleBit 3 1 3).val * positiveScale (rightScaleExponent 3 1 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 3 1 : ℤ)) • HexagonAtoms313.outerLeftABC) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (negativeScale (rightScaleExponent 3 1 3) • (rowColumnMul HexagonRowColumn313.rows_assocCAB HexagonRowColumn313.cols_right2)) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal3_case_1_3_row_0_0_1 : (((-1 : ℤ) ^ (rightScaleBit 3 1 3).val * positiveScale (rightScaleExponent 3 1 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 3 1 : ℤ)) • HexagonAtoms313.outerLeftABC) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (negativeScale (rightScaleExponent 3 1 3) • (rowColumnMul HexagonRowColumn313.rows_assocCAB HexagonRowColumn313.cols_right2)) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal3_case_1_3_row_0_1_0 : (((-1 : ℤ) ^ (rightScaleBit 3 1 3).val * positiveScale (rightScaleExponent 3 1 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 3 1 : ℤ)) • HexagonAtoms313.outerLeftABC) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (negativeScale (rightScaleExponent 3 1 3) • (rowColumnMul HexagonRowColumn313.rows_assocCAB HexagonRowColumn313.cols_right2)) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal3_case_1_3_row_0_1_1 : (((-1 : ℤ) ^ (rightScaleBit 3 1 3).val * positiveScale (rightScaleExponent 3 1 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 3 1 : ℤ)) • HexagonAtoms313.outerLeftABC) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (negativeScale (rightScaleExponent 3 1 3) • (rowColumnMul HexagonRowColumn313.rows_assocCAB HexagonRowColumn313.cols_right2)) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal3_case_1_3_row_0_2_0 : (((-1 : ℤ) ^ (rightScaleBit 3 1 3).val * positiveScale (rightScaleExponent 3 1 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 3 1 : ℤ)) • HexagonAtoms313.outerLeftABC) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (negativeScale (rightScaleExponent 3 1 3) • (rowColumnMul HexagonRowColumn313.rows_assocCAB HexagonRowColumn313.cols_right2)) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal3_case_1_3_row_0_2_1 : (((-1 : ℤ) ^ (rightScaleBit 3 1 3).val * positiveScale (rightScaleExponent 3 1 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 3 1 : ℤ)) • HexagonAtoms313.outerLeftABC) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (negativeScale (rightScaleExponent 3 1 3) • (rowColumnMul HexagonRowColumn313.rows_assocCAB HexagonRowColumn313.cols_right2)) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal3_case_1_3_row_0_3_0 : (((-1 : ℤ) ^ (rightScaleBit 3 1 3).val * positiveScale (rightScaleExponent 3 1 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 3 1 : ℤ)) • HexagonAtoms313.outerLeftABC) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (negativeScale (rightScaleExponent 3 1 3) • (rowColumnMul HexagonRowColumn313.rows_assocCAB HexagonRowColumn313.cols_right2)) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal3_case_1_3_row_0_3_1 : (((-1 : ℤ) ^ (rightScaleBit 3 1 3).val * positiveScale (rightScaleExponent 3 1 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 3 1 : ℤ)) • HexagonAtoms313.outerLeftABC) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (negativeScale (rightScaleExponent 3 1 3) • (rowColumnMul HexagonRowColumn313.rows_assocCAB HexagonRowColumn313.cols_right2)) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal3_case_1_3_row_1_0_0 : (((-1 : ℤ) ^ (rightScaleBit 3 1 3).val * positiveScale (rightScaleExponent 3 1 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 3 1 : ℤ)) • HexagonAtoms313.outerLeftABC) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (negativeScale (rightScaleExponent 3 1 3) • (rowColumnMul HexagonRowColumn313.rows_assocCAB HexagonRowColumn313.cols_right2)) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal3_case_1_3_row_1_0_1 : (((-1 : ℤ) ^ (rightScaleBit 3 1 3).val * positiveScale (rightScaleExponent 3 1 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 3 1 : ℤ)) • HexagonAtoms313.outerLeftABC) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (negativeScale (rightScaleExponent 3 1 3) • (rowColumnMul HexagonRowColumn313.rows_assocCAB HexagonRowColumn313.cols_right2)) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal3_case_1_3_row_1_1_0 : (((-1 : ℤ) ^ (rightScaleBit 3 1 3).val * positiveScale (rightScaleExponent 3 1 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 3 1 : ℤ)) • HexagonAtoms313.outerLeftABC) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (negativeScale (rightScaleExponent 3 1 3) • (rowColumnMul HexagonRowColumn313.rows_assocCAB HexagonRowColumn313.cols_right2)) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal3_case_1_3_row_1_1_1 : (((-1 : ℤ) ^ (rightScaleBit 3 1 3).val * positiveScale (rightScaleExponent 3 1 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 3 1 : ℤ)) • HexagonAtoms313.outerLeftABC) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (negativeScale (rightScaleExponent 3 1 3) • (rowColumnMul HexagonRowColumn313.rows_assocCAB HexagonRowColumn313.cols_right2)) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal3_case_1_3_row_1_2_0 : (((-1 : ℤ) ^ (rightScaleBit 3 1 3).val * positiveScale (rightScaleExponent 3 1 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 3 1 : ℤ)) • HexagonAtoms313.outerLeftABC) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (negativeScale (rightScaleExponent 3 1 3) • (rowColumnMul HexagonRowColumn313.rows_assocCAB HexagonRowColumn313.cols_right2)) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal3_case_1_3_row_1_2_1 : (((-1 : ℤ) ^ (rightScaleBit 3 1 3).val * positiveScale (rightScaleExponent 3 1 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 3 1 : ℤ)) • HexagonAtoms313.outerLeftABC) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (negativeScale (rightScaleExponent 3 1 3) • (rowColumnMul HexagonRowColumn313.rows_assocCAB HexagonRowColumn313.cols_right2)) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal3_case_1_3_row_1_3_0 : (((-1 : ℤ) ^ (rightScaleBit 3 1 3).val * positiveScale (rightScaleExponent 3 1 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 3 1 : ℤ)) • HexagonAtoms313.outerLeftABC) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (negativeScale (rightScaleExponent 3 1 3) • (rowColumnMul HexagonRowColumn313.rows_assocCAB HexagonRowColumn313.cols_right2)) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal3_case_1_3_row_1_3_1 : (((-1 : ℤ) ^ (rightScaleBit 3 1 3).val * positiveScale (rightScaleExponent 3 1 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 3 1 : ℤ)) • HexagonAtoms313.outerLeftABC) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (negativeScale (rightScaleExponent 3 1 3) • (rowColumnMul HexagonRowColumn313.rows_assocCAB HexagonRowColumn313.cols_right2)) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal3_case_1_3_checked : ((-1 : ℤ) ^ (rightScaleBit 3 1 3).val * positiveScale (rightScaleExponent 3 1 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 3 1 : ℤ)) • HexagonAtoms313.outerLeftABC = negativeScale (rightScaleExponent 3 1 3) • (rowColumnMul HexagonRowColumn313.rows_assocCAB HexagonRowColumn313.cols_right2) := by
  funext r
  fin_cases r
  · exact rightFinal3_case_1_3_row_0_0_0
  · exact rightFinal3_case_1_3_row_0_0_1
  · exact rightFinal3_case_1_3_row_0_1_0
  · exact rightFinal3_case_1_3_row_0_1_1
  · exact rightFinal3_case_1_3_row_0_2_0
  · exact rightFinal3_case_1_3_row_0_2_1
  · exact rightFinal3_case_1_3_row_0_3_0
  · exact rightFinal3_case_1_3_row_0_3_1
  · exact rightFinal3_case_1_3_row_1_0_0
  · exact rightFinal3_case_1_3_row_1_0_1
  · exact rightFinal3_case_1_3_row_1_1_0
  · exact rightFinal3_case_1_3_row_1_1_1
  · exact rightFinal3_case_1_3_row_1_2_0
  · exact rightFinal3_case_1_3_row_1_2_1
  · exact rightFinal3_case_1_3_row_1_3_0
  · exact rightFinal3_case_1_3_row_1_3_1

set_option backward.isDefEq.respectTransparency false in
theorem rightFinal3_case_1_3 : ((-1 : ℤ) ^ (rightScaleBit 3 1 3).val * positiveScale (rightScaleExponent 3 1 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 3 1 : ℤ)) • outerLeftZ 3 1 3 = negativeScale (rightScaleExponent 3 1 3) • (associatorZ 3 3 1 * right2Middle3 1 3) := by
  simpa only [HexagonAtoms313.assocABC_eq,
    HexagonAtoms313.outerABC_eq,
    HexagonAtoms313.assocBAC_eq,
    HexagonAtoms313.innerABC_eq,
    HexagonAtoms313.innerRightABC_eq,
    HexagonAtoms313.inverseACB_eq,
    HexagonAtoms313.innerACB_eq,
    HexagonAtoms313.assocBCA_eq,
    HexagonAtoms313.innerRightBAC_eq,
    HexagonAtoms313.assocCAB_eq,
    HexagonAtoms313.outerLeftABC_eq,
    HexagonRowColumn313.assocBCA_alias,
    HexagonRowColumn313.product0_eq,
    HexagonRowColumn313.product1_eq,
    HexagonRowColumn313.product2_eq,
    HexagonRowColumn313.product3_eq,
    HexagonRowColumn313.product4_eq,
    HexagonRowColumn313.product5_eq,
    HexagonRowColumn313.product6_eq,
    HexagonRowColumn313.product7_eq] using rightFinal3_case_1_3_checked

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonCases3
