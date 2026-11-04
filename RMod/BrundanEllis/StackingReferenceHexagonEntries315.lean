import RMod.BrundanEllis.StackingReferenceHexagonMiddle3
import RMod.BrundanEllis.StackingReferenceSparseMatrixCheck
import RMod.BrundanEllis.StackingReferenceHexagonAtoms315
import RMod.BrundanEllis.StackingReferenceHexagonRowColumn315

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

private theorem left0Middle3_eq_case_1_5_row_0_0_0 : (left0Middle3 1 5) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (HexagonAtoms315.assocABC) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle3_eq_case_1_5_row_0_0_1 : (left0Middle3 1 5) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (HexagonAtoms315.assocABC) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle3_eq_case_1_5_row_0_1_0 : (left0Middle3 1 5) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (HexagonAtoms315.assocABC) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle3_eq_case_1_5_row_0_1_1 : (left0Middle3 1 5) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (HexagonAtoms315.assocABC) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle3_eq_case_1_5_row_0_2_0 : (left0Middle3 1 5) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (HexagonAtoms315.assocABC) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle3_eq_case_1_5_row_0_2_1 : (left0Middle3 1 5) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (HexagonAtoms315.assocABC) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle3_eq_case_1_5_row_0_3_0 : (left0Middle3 1 5) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (HexagonAtoms315.assocABC) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle3_eq_case_1_5_row_0_3_1 : (left0Middle3 1 5) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (HexagonAtoms315.assocABC) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle3_eq_case_1_5_row_1_0_0 : (left0Middle3 1 5) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (HexagonAtoms315.assocABC) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle3_eq_case_1_5_row_1_0_1 : (left0Middle3 1 5) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (HexagonAtoms315.assocABC) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle3_eq_case_1_5_row_1_1_0 : (left0Middle3 1 5) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (HexagonAtoms315.assocABC) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle3_eq_case_1_5_row_1_1_1 : (left0Middle3 1 5) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (HexagonAtoms315.assocABC) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle3_eq_case_1_5_row_1_2_0 : (left0Middle3 1 5) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (HexagonAtoms315.assocABC) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle3_eq_case_1_5_row_1_2_1 : (left0Middle3 1 5) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (HexagonAtoms315.assocABC) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle3_eq_case_1_5_row_1_3_0 : (left0Middle3 1 5) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (HexagonAtoms315.assocABC) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle3_eq_case_1_5_row_1_3_1 : (left0Middle3 1 5) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (HexagonAtoms315.assocABC) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle3_eq_case_1_5_checked : left0Middle3 1 5 = HexagonAtoms315.assocABC := by
  funext r
  fin_cases r
  · exact left0Middle3_eq_case_1_5_row_0_0_0
  · exact left0Middle3_eq_case_1_5_row_0_0_1
  · exact left0Middle3_eq_case_1_5_row_0_1_0
  · exact left0Middle3_eq_case_1_5_row_0_1_1
  · exact left0Middle3_eq_case_1_5_row_0_2_0
  · exact left0Middle3_eq_case_1_5_row_0_2_1
  · exact left0Middle3_eq_case_1_5_row_0_3_0
  · exact left0Middle3_eq_case_1_5_row_0_3_1
  · exact left0Middle3_eq_case_1_5_row_1_0_0
  · exact left0Middle3_eq_case_1_5_row_1_0_1
  · exact left0Middle3_eq_case_1_5_row_1_1_0
  · exact left0Middle3_eq_case_1_5_row_1_1_1
  · exact left0Middle3_eq_case_1_5_row_1_2_0
  · exact left0Middle3_eq_case_1_5_row_1_2_1
  · exact left0Middle3_eq_case_1_5_row_1_3_0
  · exact left0Middle3_eq_case_1_5_row_1_3_1

set_option backward.isDefEq.respectTransparency false in
theorem left0Middle3_eq_case_1_5 : left0Middle3 1 5 = outerRightZ 3 1 5 * associatorZ 3 1 5 := by
  simpa only [HexagonAtoms315.assocABC_eq,
    HexagonAtoms315.outerABC_eq,
    HexagonAtoms315.assocBAC_eq,
    HexagonAtoms315.innerABC_eq,
    HexagonAtoms315.innerRightABC_eq,
    HexagonAtoms315.inverseACB_eq,
    HexagonAtoms315.innerACB_eq,
    HexagonAtoms315.assocBCA_eq,
    HexagonAtoms315.innerRightBAC_eq,
    HexagonAtoms315.assocCAB_eq,
    HexagonAtoms315.outerLeftABC_eq,
    HexagonRowColumn315.product0_eq,
    HexagonRowColumn315.product1_eq,
    HexagonRowColumn315.product2_eq,
    HexagonRowColumn315.product3_eq,
    HexagonRowColumn315.product4_eq,
    HexagonRowColumn315.product5_eq,
    HexagonRowColumn315.product6_eq,
    HexagonRowColumn315.product7_eq] using left0Middle3_eq_case_1_5_checked

private theorem left1Middle3_eq_case_1_5_row_0_0_0 : (left1Middle3 1 5) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 2)) = (HexagonAtoms315.assocBAC) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle3_eq_case_1_5_row_0_0_1 : (left1Middle3 1 5) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 2)) = (HexagonAtoms315.assocBAC) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle3_eq_case_1_5_row_1_0_0 : (left1Middle3 1 5) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 2)) = (HexagonAtoms315.assocBAC) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle3_eq_case_1_5_row_1_0_1 : (left1Middle3 1 5) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 2)) = (HexagonAtoms315.assocBAC) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle3_eq_case_1_5_row_2_0_0 : (left1Middle3 1 5) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 2)) = (HexagonAtoms315.assocBAC) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle3_eq_case_1_5_row_2_0_1 : (left1Middle3 1 5) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 2)) = (HexagonAtoms315.assocBAC) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle3_eq_case_1_5_row_3_0_0 : (left1Middle3 1 5) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 2)) = (HexagonAtoms315.assocBAC) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle3_eq_case_1_5_row_3_0_1 : (left1Middle3 1 5) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 2)) = (HexagonAtoms315.assocBAC) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle3_eq_case_1_5_row_4_0_0 : (left1Middle3 1 5) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 2)) = (HexagonAtoms315.assocBAC) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle3_eq_case_1_5_row_4_0_1 : (left1Middle3 1 5) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 2)) = (HexagonAtoms315.assocBAC) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle3_eq_case_1_5_row_5_0_0 : (left1Middle3 1 5) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 2)) = (HexagonAtoms315.assocBAC) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle3_eq_case_1_5_row_5_0_1 : (left1Middle3 1 5) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 2)) = (HexagonAtoms315.assocBAC) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle3_eq_case_1_5_row_6_0_0 : (left1Middle3 1 5) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 2)) = (HexagonAtoms315.assocBAC) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle3_eq_case_1_5_row_6_0_1 : (left1Middle3 1 5) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 2)) = (HexagonAtoms315.assocBAC) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle3_eq_case_1_5_row_7_0_0 : (left1Middle3 1 5) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 2)) = (HexagonAtoms315.assocBAC) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle3_eq_case_1_5_row_7_0_1 : (left1Middle3 1 5) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 2)) = (HexagonAtoms315.assocBAC) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle3_eq_case_1_5_checked : left1Middle3 1 5 = HexagonAtoms315.assocBAC := by
  funext r
  fin_cases r
  · exact left1Middle3_eq_case_1_5_row_0_0_0
  · exact left1Middle3_eq_case_1_5_row_0_0_1
  · exact left1Middle3_eq_case_1_5_row_1_0_0
  · exact left1Middle3_eq_case_1_5_row_1_0_1
  · exact left1Middle3_eq_case_1_5_row_2_0_0
  · exact left1Middle3_eq_case_1_5_row_2_0_1
  · exact left1Middle3_eq_case_1_5_row_3_0_0
  · exact left1Middle3_eq_case_1_5_row_3_0_1
  · exact left1Middle3_eq_case_1_5_row_4_0_0
  · exact left1Middle3_eq_case_1_5_row_4_0_1
  · exact left1Middle3_eq_case_1_5_row_5_0_0
  · exact left1Middle3_eq_case_1_5_row_5_0_1
  · exact left1Middle3_eq_case_1_5_row_6_0_0
  · exact left1Middle3_eq_case_1_5_row_6_0_1
  · exact left1Middle3_eq_case_1_5_row_7_0_0
  · exact left1Middle3_eq_case_1_5_row_7_0_1

set_option backward.isDefEq.respectTransparency false in
theorem left1Middle3_eq_case_1_5 : left1Middle3 1 5 = associatorZ 1 3 5 * innerLeftZ 3 1 5 := by
  simpa only [HexagonAtoms315.assocABC_eq,
    HexagonAtoms315.outerABC_eq,
    HexagonAtoms315.assocBAC_eq,
    HexagonAtoms315.innerABC_eq,
    HexagonAtoms315.innerRightABC_eq,
    HexagonAtoms315.inverseACB_eq,
    HexagonAtoms315.innerACB_eq,
    HexagonAtoms315.assocBCA_eq,
    HexagonAtoms315.innerRightBAC_eq,
    HexagonAtoms315.assocCAB_eq,
    HexagonAtoms315.outerLeftABC_eq,
    HexagonRowColumn315.product0_eq,
    HexagonRowColumn315.product1_eq,
    HexagonRowColumn315.product2_eq,
    HexagonRowColumn315.product3_eq,
    HexagonRowColumn315.product4_eq,
    HexagonRowColumn315.product5_eq,
    HexagonRowColumn315.product6_eq,
    HexagonRowColumn315.product7_eq] using left1Middle3_eq_case_1_5_checked

private theorem right0Middle3_eq_case_1_5_row_0_0_0 : (right0Middle3 1 5) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (HexagonAtoms315.assocABC) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle3_eq_case_1_5_row_0_0_1 : (right0Middle3 1 5) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (HexagonAtoms315.assocABC) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle3_eq_case_1_5_row_0_1_0 : (right0Middle3 1 5) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (HexagonAtoms315.assocABC) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle3_eq_case_1_5_row_0_1_1 : (right0Middle3 1 5) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (HexagonAtoms315.assocABC) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle3_eq_case_1_5_row_0_2_0 : (right0Middle3 1 5) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (HexagonAtoms315.assocABC) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle3_eq_case_1_5_row_0_2_1 : (right0Middle3 1 5) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (HexagonAtoms315.assocABC) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle3_eq_case_1_5_row_0_3_0 : (right0Middle3 1 5) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (HexagonAtoms315.assocABC) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle3_eq_case_1_5_row_0_3_1 : (right0Middle3 1 5) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (HexagonAtoms315.assocABC) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle3_eq_case_1_5_row_1_0_0 : (right0Middle3 1 5) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (HexagonAtoms315.assocABC) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle3_eq_case_1_5_row_1_0_1 : (right0Middle3 1 5) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (HexagonAtoms315.assocABC) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle3_eq_case_1_5_row_1_1_0 : (right0Middle3 1 5) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (HexagonAtoms315.assocABC) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle3_eq_case_1_5_row_1_1_1 : (right0Middle3 1 5) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (HexagonAtoms315.assocABC) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle3_eq_case_1_5_row_1_2_0 : (right0Middle3 1 5) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (HexagonAtoms315.assocABC) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle3_eq_case_1_5_row_1_2_1 : (right0Middle3 1 5) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (HexagonAtoms315.assocABC) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle3_eq_case_1_5_row_1_3_0 : (right0Middle3 1 5) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (HexagonAtoms315.assocABC) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle3_eq_case_1_5_row_1_3_1 : (right0Middle3 1 5) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (HexagonAtoms315.assocABC) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle3_eq_case_1_5_checked : right0Middle3 1 5 = HexagonAtoms315.assocABC := by
  funext r
  fin_cases r
  · exact right0Middle3_eq_case_1_5_row_0_0_0
  · exact right0Middle3_eq_case_1_5_row_0_0_1
  · exact right0Middle3_eq_case_1_5_row_0_1_0
  · exact right0Middle3_eq_case_1_5_row_0_1_1
  · exact right0Middle3_eq_case_1_5_row_0_2_0
  · exact right0Middle3_eq_case_1_5_row_0_2_1
  · exact right0Middle3_eq_case_1_5_row_0_3_0
  · exact right0Middle3_eq_case_1_5_row_0_3_1
  · exact right0Middle3_eq_case_1_5_row_1_0_0
  · exact right0Middle3_eq_case_1_5_row_1_0_1
  · exact right0Middle3_eq_case_1_5_row_1_1_0
  · exact right0Middle3_eq_case_1_5_row_1_1_1
  · exact right0Middle3_eq_case_1_5_row_1_2_0
  · exact right0Middle3_eq_case_1_5_row_1_2_1
  · exact right0Middle3_eq_case_1_5_row_1_3_0
  · exact right0Middle3_eq_case_1_5_row_1_3_1

set_option backward.isDefEq.respectTransparency false in
theorem right0Middle3_eq_case_1_5 : right0Middle3 1 5 = innerRightZ 3 1 5 * associatorZ 3 1 5 := by
  simpa only [HexagonAtoms315.assocABC_eq,
    HexagonAtoms315.outerABC_eq,
    HexagonAtoms315.assocBAC_eq,
    HexagonAtoms315.innerABC_eq,
    HexagonAtoms315.innerRightABC_eq,
    HexagonAtoms315.inverseACB_eq,
    HexagonAtoms315.innerACB_eq,
    HexagonAtoms315.assocBCA_eq,
    HexagonAtoms315.innerRightBAC_eq,
    HexagonAtoms315.assocCAB_eq,
    HexagonAtoms315.outerLeftABC_eq,
    HexagonRowColumn315.product0_eq,
    HexagonRowColumn315.product1_eq,
    HexagonRowColumn315.product2_eq,
    HexagonRowColumn315.product3_eq,
    HexagonRowColumn315.product4_eq,
    HexagonRowColumn315.product5_eq,
    HexagonRowColumn315.product6_eq,
    HexagonRowColumn315.product7_eq] using right0Middle3_eq_case_1_5_checked

private theorem right1Middle3_eq_case_1_5_row_0_0_0 : (right1Middle3 1 5) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn315.rows_inverseACB HexagonRowColumn315.cols_right0) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle3_eq_case_1_5_row_0_0_1 : (right1Middle3 1 5) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn315.rows_inverseACB HexagonRowColumn315.cols_right0) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle3_eq_case_1_5_row_1_0_0 : (right1Middle3 1 5) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn315.rows_inverseACB HexagonRowColumn315.cols_right0) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle3_eq_case_1_5_row_1_0_1 : (right1Middle3 1 5) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn315.rows_inverseACB HexagonRowColumn315.cols_right0) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle3_eq_case_1_5_row_2_0_0 : (right1Middle3 1 5) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn315.rows_inverseACB HexagonRowColumn315.cols_right0) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle3_eq_case_1_5_row_2_0_1 : (right1Middle3 1 5) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn315.rows_inverseACB HexagonRowColumn315.cols_right0) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle3_eq_case_1_5_row_3_0_0 : (right1Middle3 1 5) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn315.rows_inverseACB HexagonRowColumn315.cols_right0) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle3_eq_case_1_5_row_3_0_1 : (right1Middle3 1 5) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn315.rows_inverseACB HexagonRowColumn315.cols_right0) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle3_eq_case_1_5_row_4_0_0 : (right1Middle3 1 5) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn315.rows_inverseACB HexagonRowColumn315.cols_right0) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle3_eq_case_1_5_row_4_0_1 : (right1Middle3 1 5) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn315.rows_inverseACB HexagonRowColumn315.cols_right0) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle3_eq_case_1_5_row_5_0_0 : (right1Middle3 1 5) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn315.rows_inverseACB HexagonRowColumn315.cols_right0) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle3_eq_case_1_5_row_5_0_1 : (right1Middle3 1 5) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn315.rows_inverseACB HexagonRowColumn315.cols_right0) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle3_eq_case_1_5_row_6_0_0 : (right1Middle3 1 5) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn315.rows_inverseACB HexagonRowColumn315.cols_right0) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle3_eq_case_1_5_row_6_0_1 : (right1Middle3 1 5) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn315.rows_inverseACB HexagonRowColumn315.cols_right0) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle3_eq_case_1_5_row_7_0_0 : (right1Middle3 1 5) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn315.rows_inverseACB HexagonRowColumn315.cols_right0) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle3_eq_case_1_5_row_7_0_1 : (right1Middle3 1 5) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn315.rows_inverseACB HexagonRowColumn315.cols_right0) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle3_eq_case_1_5_checked : right1Middle3 1 5 = rowColumnMul HexagonRowColumn315.rows_inverseACB HexagonRowColumn315.cols_right0 := by
  funext r
  fin_cases r
  · exact right1Middle3_eq_case_1_5_row_0_0_0
  · exact right1Middle3_eq_case_1_5_row_0_0_1
  · exact right1Middle3_eq_case_1_5_row_1_0_0
  · exact right1Middle3_eq_case_1_5_row_1_0_1
  · exact right1Middle3_eq_case_1_5_row_2_0_0
  · exact right1Middle3_eq_case_1_5_row_2_0_1
  · exact right1Middle3_eq_case_1_5_row_3_0_0
  · exact right1Middle3_eq_case_1_5_row_3_0_1
  · exact right1Middle3_eq_case_1_5_row_4_0_0
  · exact right1Middle3_eq_case_1_5_row_4_0_1
  · exact right1Middle3_eq_case_1_5_row_5_0_0
  · exact right1Middle3_eq_case_1_5_row_5_0_1
  · exact right1Middle3_eq_case_1_5_row_6_0_0
  · exact right1Middle3_eq_case_1_5_row_6_0_1
  · exact right1Middle3_eq_case_1_5_row_7_0_0
  · exact right1Middle3_eq_case_1_5_row_7_0_1

set_option backward.isDefEq.respectTransparency false in
theorem right1Middle3_eq_case_1_5 : right1Middle3 1 5 = associatorInverseZ 3 5 1 * right0Middle3 1 5 := by
  simpa only [HexagonAtoms315.assocABC_eq,
    HexagonAtoms315.outerABC_eq,
    HexagonAtoms315.assocBAC_eq,
    HexagonAtoms315.innerABC_eq,
    HexagonAtoms315.innerRightABC_eq,
    HexagonAtoms315.inverseACB_eq,
    HexagonAtoms315.innerACB_eq,
    HexagonAtoms315.assocBCA_eq,
    HexagonAtoms315.innerRightBAC_eq,
    HexagonAtoms315.assocCAB_eq,
    HexagonAtoms315.outerLeftABC_eq,
    HexagonRowColumn315.product0_eq,
    HexagonRowColumn315.product1_eq,
    HexagonRowColumn315.product2_eq,
    HexagonRowColumn315.product3_eq,
    HexagonRowColumn315.product4_eq,
    HexagonRowColumn315.product5_eq,
    HexagonRowColumn315.product6_eq,
    HexagonRowColumn315.product7_eq] using right1Middle3_eq_case_1_5_checked

private theorem right2Middle3_eq_case_1_5_row_0_0_0 : (right2Middle3 1 5) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 2)) = (right1Middle3 1 5) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle3_eq_case_1_5_row_0_0_1 : (right2Middle3 1 5) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 2)) = (right1Middle3 1 5) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle3_eq_case_1_5_row_1_0_0 : (right2Middle3 1 5) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 2)) = (right1Middle3 1 5) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle3_eq_case_1_5_row_1_0_1 : (right2Middle3 1 5) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 2)) = (right1Middle3 1 5) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle3_eq_case_1_5_row_2_0_0 : (right2Middle3 1 5) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 2)) = (right1Middle3 1 5) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle3_eq_case_1_5_row_2_0_1 : (right2Middle3 1 5) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 2)) = (right1Middle3 1 5) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle3_eq_case_1_5_row_3_0_0 : (right2Middle3 1 5) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 2)) = (right1Middle3 1 5) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle3_eq_case_1_5_row_3_0_1 : (right2Middle3 1 5) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 2)) = (right1Middle3 1 5) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle3_eq_case_1_5_row_4_0_0 : (right2Middle3 1 5) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 2)) = (right1Middle3 1 5) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle3_eq_case_1_5_row_4_0_1 : (right2Middle3 1 5) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 2)) = (right1Middle3 1 5) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle3_eq_case_1_5_row_5_0_0 : (right2Middle3 1 5) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 2)) = (right1Middle3 1 5) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle3_eq_case_1_5_row_5_0_1 : (right2Middle3 1 5) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 2)) = (right1Middle3 1 5) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle3_eq_case_1_5_row_6_0_0 : (right2Middle3 1 5) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 2)) = (right1Middle3 1 5) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle3_eq_case_1_5_row_6_0_1 : (right2Middle3 1 5) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 2)) = (right1Middle3 1 5) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle3_eq_case_1_5_row_7_0_0 : (right2Middle3 1 5) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 2)) = (right1Middle3 1 5) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle3_eq_case_1_5_row_7_0_1 : (right2Middle3 1 5) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 2)) = (right1Middle3 1 5) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle3_eq_case_1_5_checked : right2Middle3 1 5 = right1Middle3 1 5 := by
  funext r
  fin_cases r
  · exact right2Middle3_eq_case_1_5_row_0_0_0
  · exact right2Middle3_eq_case_1_5_row_0_0_1
  · exact right2Middle3_eq_case_1_5_row_1_0_0
  · exact right2Middle3_eq_case_1_5_row_1_0_1
  · exact right2Middle3_eq_case_1_5_row_2_0_0
  · exact right2Middle3_eq_case_1_5_row_2_0_1
  · exact right2Middle3_eq_case_1_5_row_3_0_0
  · exact right2Middle3_eq_case_1_5_row_3_0_1
  · exact right2Middle3_eq_case_1_5_row_4_0_0
  · exact right2Middle3_eq_case_1_5_row_4_0_1
  · exact right2Middle3_eq_case_1_5_row_5_0_0
  · exact right2Middle3_eq_case_1_5_row_5_0_1
  · exact right2Middle3_eq_case_1_5_row_6_0_0
  · exact right2Middle3_eq_case_1_5_row_6_0_1
  · exact right2Middle3_eq_case_1_5_row_7_0_0
  · exact right2Middle3_eq_case_1_5_row_7_0_1

set_option backward.isDefEq.respectTransparency false in
theorem right2Middle3_eq_case_1_5 : right2Middle3 1 5 = innerLeftZ 3 5 1 * right1Middle3 1 5 := by
  simpa only [HexagonAtoms315.assocABC_eq,
    HexagonAtoms315.outerABC_eq,
    HexagonAtoms315.assocBAC_eq,
    HexagonAtoms315.innerABC_eq,
    HexagonAtoms315.innerRightABC_eq,
    HexagonAtoms315.inverseACB_eq,
    HexagonAtoms315.innerACB_eq,
    HexagonAtoms315.assocBCA_eq,
    HexagonAtoms315.innerRightBAC_eq,
    HexagonAtoms315.assocCAB_eq,
    HexagonAtoms315.outerLeftABC_eq,
    HexagonRowColumn315.product0_eq,
    HexagonRowColumn315.product1_eq,
    HexagonRowColumn315.product2_eq,
    HexagonRowColumn315.product3_eq,
    HexagonRowColumn315.product4_eq,
    HexagonRowColumn315.product5_eq,
    HexagonRowColumn315.product6_eq,
    HexagonRowColumn315.product7_eq] using right2Middle3_eq_case_1_5_checked

private theorem leftFinal3_case_1_5_row_0_0_0 : (((-1 : ℤ) ^ (leftScaleBit 3 1 5).val * positiveScale (leftScaleExponent 3 1 5)) •
      (rowColumnMul HexagonRowColumn315.rows_assocBCA HexagonRowColumn315.cols_left0)) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 2)) = (negativeScale (leftScaleExponent 3 1 5) • (left1Middle3 1 5)) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal3_case_1_5_row_0_0_1 : (((-1 : ℤ) ^ (leftScaleBit 3 1 5).val * positiveScale (leftScaleExponent 3 1 5)) •
      (rowColumnMul HexagonRowColumn315.rows_assocBCA HexagonRowColumn315.cols_left0)) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 2)) = (negativeScale (leftScaleExponent 3 1 5) • (left1Middle3 1 5)) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal3_case_1_5_row_1_0_0 : (((-1 : ℤ) ^ (leftScaleBit 3 1 5).val * positiveScale (leftScaleExponent 3 1 5)) •
      (rowColumnMul HexagonRowColumn315.rows_assocBCA HexagonRowColumn315.cols_left0)) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 2)) = (negativeScale (leftScaleExponent 3 1 5) • (left1Middle3 1 5)) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal3_case_1_5_row_1_0_1 : (((-1 : ℤ) ^ (leftScaleBit 3 1 5).val * positiveScale (leftScaleExponent 3 1 5)) •
      (rowColumnMul HexagonRowColumn315.rows_assocBCA HexagonRowColumn315.cols_left0)) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 2)) = (negativeScale (leftScaleExponent 3 1 5) • (left1Middle3 1 5)) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal3_case_1_5_row_2_0_0 : (((-1 : ℤ) ^ (leftScaleBit 3 1 5).val * positiveScale (leftScaleExponent 3 1 5)) •
      (rowColumnMul HexagonRowColumn315.rows_assocBCA HexagonRowColumn315.cols_left0)) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 2)) = (negativeScale (leftScaleExponent 3 1 5) • (left1Middle3 1 5)) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal3_case_1_5_row_2_0_1 : (((-1 : ℤ) ^ (leftScaleBit 3 1 5).val * positiveScale (leftScaleExponent 3 1 5)) •
      (rowColumnMul HexagonRowColumn315.rows_assocBCA HexagonRowColumn315.cols_left0)) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 2)) = (negativeScale (leftScaleExponent 3 1 5) • (left1Middle3 1 5)) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal3_case_1_5_row_3_0_0 : (((-1 : ℤ) ^ (leftScaleBit 3 1 5).val * positiveScale (leftScaleExponent 3 1 5)) •
      (rowColumnMul HexagonRowColumn315.rows_assocBCA HexagonRowColumn315.cols_left0)) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 2)) = (negativeScale (leftScaleExponent 3 1 5) • (left1Middle3 1 5)) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal3_case_1_5_row_3_0_1 : (((-1 : ℤ) ^ (leftScaleBit 3 1 5).val * positiveScale (leftScaleExponent 3 1 5)) •
      (rowColumnMul HexagonRowColumn315.rows_assocBCA HexagonRowColumn315.cols_left0)) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 2)) = (negativeScale (leftScaleExponent 3 1 5) • (left1Middle3 1 5)) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal3_case_1_5_row_4_0_0 : (((-1 : ℤ) ^ (leftScaleBit 3 1 5).val * positiveScale (leftScaleExponent 3 1 5)) •
      (rowColumnMul HexagonRowColumn315.rows_assocBCA HexagonRowColumn315.cols_left0)) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 2)) = (negativeScale (leftScaleExponent 3 1 5) • (left1Middle3 1 5)) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal3_case_1_5_row_4_0_1 : (((-1 : ℤ) ^ (leftScaleBit 3 1 5).val * positiveScale (leftScaleExponent 3 1 5)) •
      (rowColumnMul HexagonRowColumn315.rows_assocBCA HexagonRowColumn315.cols_left0)) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 2)) = (negativeScale (leftScaleExponent 3 1 5) • (left1Middle3 1 5)) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal3_case_1_5_row_5_0_0 : (((-1 : ℤ) ^ (leftScaleBit 3 1 5).val * positiveScale (leftScaleExponent 3 1 5)) •
      (rowColumnMul HexagonRowColumn315.rows_assocBCA HexagonRowColumn315.cols_left0)) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 2)) = (negativeScale (leftScaleExponent 3 1 5) • (left1Middle3 1 5)) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal3_case_1_5_row_5_0_1 : (((-1 : ℤ) ^ (leftScaleBit 3 1 5).val * positiveScale (leftScaleExponent 3 1 5)) •
      (rowColumnMul HexagonRowColumn315.rows_assocBCA HexagonRowColumn315.cols_left0)) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 2)) = (negativeScale (leftScaleExponent 3 1 5) • (left1Middle3 1 5)) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal3_case_1_5_row_6_0_0 : (((-1 : ℤ) ^ (leftScaleBit 3 1 5).val * positiveScale (leftScaleExponent 3 1 5)) •
      (rowColumnMul HexagonRowColumn315.rows_assocBCA HexagonRowColumn315.cols_left0)) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 2)) = (negativeScale (leftScaleExponent 3 1 5) • (left1Middle3 1 5)) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal3_case_1_5_row_6_0_1 : (((-1 : ℤ) ^ (leftScaleBit 3 1 5).val * positiveScale (leftScaleExponent 3 1 5)) •
      (rowColumnMul HexagonRowColumn315.rows_assocBCA HexagonRowColumn315.cols_left0)) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 2)) = (negativeScale (leftScaleExponent 3 1 5) • (left1Middle3 1 5)) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal3_case_1_5_row_7_0_0 : (((-1 : ℤ) ^ (leftScaleBit 3 1 5).val * positiveScale (leftScaleExponent 3 1 5)) •
      (rowColumnMul HexagonRowColumn315.rows_assocBCA HexagonRowColumn315.cols_left0)) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 2)) = (negativeScale (leftScaleExponent 3 1 5) • (left1Middle3 1 5)) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal3_case_1_5_row_7_0_1 : (((-1 : ℤ) ^ (leftScaleBit 3 1 5).val * positiveScale (leftScaleExponent 3 1 5)) •
      (rowColumnMul HexagonRowColumn315.rows_assocBCA HexagonRowColumn315.cols_left0)) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 2)) = (negativeScale (leftScaleExponent 3 1 5) • (left1Middle3 1 5)) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal3_case_1_5_checked : ((-1 : ℤ) ^ (leftScaleBit 3 1 5).val * positiveScale (leftScaleExponent 3 1 5)) •
      (rowColumnMul HexagonRowColumn315.rows_assocBCA HexagonRowColumn315.cols_left0) = negativeScale (leftScaleExponent 3 1 5) • (left1Middle3 1 5) := by
  funext r
  fin_cases r
  · exact leftFinal3_case_1_5_row_0_0_0
  · exact leftFinal3_case_1_5_row_0_0_1
  · exact leftFinal3_case_1_5_row_1_0_0
  · exact leftFinal3_case_1_5_row_1_0_1
  · exact leftFinal3_case_1_5_row_2_0_0
  · exact leftFinal3_case_1_5_row_2_0_1
  · exact leftFinal3_case_1_5_row_3_0_0
  · exact leftFinal3_case_1_5_row_3_0_1
  · exact leftFinal3_case_1_5_row_4_0_0
  · exact leftFinal3_case_1_5_row_4_0_1
  · exact leftFinal3_case_1_5_row_5_0_0
  · exact leftFinal3_case_1_5_row_5_0_1
  · exact leftFinal3_case_1_5_row_6_0_0
  · exact leftFinal3_case_1_5_row_6_0_1
  · exact leftFinal3_case_1_5_row_7_0_0
  · exact leftFinal3_case_1_5_row_7_0_1

set_option backward.isDefEq.respectTransparency false in
theorem leftFinal3_case_1_5 : ((-1 : ℤ) ^ (leftScaleBit 3 1 5).val * positiveScale (leftScaleExponent 3 1 5)) •
      (associatorZ 1 5 3 * left0Middle3 1 5) = negativeScale (leftScaleExponent 3 1 5) • (innerRightZ 1 3 5 * left1Middle3 1 5) := by
  simpa only [HexagonAtoms315.assocABC_eq,
    HexagonAtoms315.outerABC_eq,
    HexagonAtoms315.assocBAC_eq,
    HexagonAtoms315.innerABC_eq,
    HexagonAtoms315.innerRightABC_eq,
    HexagonAtoms315.inverseACB_eq,
    HexagonAtoms315.innerACB_eq,
    HexagonAtoms315.assocBCA_eq,
    HexagonAtoms315.innerRightBAC_eq,
    HexagonAtoms315.assocCAB_eq,
    HexagonAtoms315.outerLeftABC_eq,
    HexagonRowColumn315.product0_eq,
    HexagonRowColumn315.product1_eq,
    HexagonRowColumn315.product2_eq,
    HexagonRowColumn315.product3_eq,
    HexagonRowColumn315.product4_eq,
    HexagonRowColumn315.product5_eq,
    HexagonRowColumn315.product6_eq,
    HexagonRowColumn315.product7_eq] using leftFinal3_case_1_5_checked

private theorem rightFinal3_case_1_5_row_0_0_0 : (((-1 : ℤ) ^ (rightScaleBit 3 1 5).val * positiveScale (rightScaleExponent 3 1 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 5 1 : ℤ)) • HexagonAtoms315.outerLeftABC) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (negativeScale (rightScaleExponent 3 1 5) • (rowColumnMul HexagonRowColumn315.rows_assocCAB HexagonRowColumn315.cols_right2)) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal3_case_1_5_row_0_0_1 : (((-1 : ℤ) ^ (rightScaleBit 3 1 5).val * positiveScale (rightScaleExponent 3 1 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 5 1 : ℤ)) • HexagonAtoms315.outerLeftABC) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (negativeScale (rightScaleExponent 3 1 5) • (rowColumnMul HexagonRowColumn315.rows_assocCAB HexagonRowColumn315.cols_right2)) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal3_case_1_5_row_0_1_0 : (((-1 : ℤ) ^ (rightScaleBit 3 1 5).val * positiveScale (rightScaleExponent 3 1 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 5 1 : ℤ)) • HexagonAtoms315.outerLeftABC) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (negativeScale (rightScaleExponent 3 1 5) • (rowColumnMul HexagonRowColumn315.rows_assocCAB HexagonRowColumn315.cols_right2)) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal3_case_1_5_row_0_1_1 : (((-1 : ℤ) ^ (rightScaleBit 3 1 5).val * positiveScale (rightScaleExponent 3 1 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 5 1 : ℤ)) • HexagonAtoms315.outerLeftABC) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (negativeScale (rightScaleExponent 3 1 5) • (rowColumnMul HexagonRowColumn315.rows_assocCAB HexagonRowColumn315.cols_right2)) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal3_case_1_5_row_0_2_0 : (((-1 : ℤ) ^ (rightScaleBit 3 1 5).val * positiveScale (rightScaleExponent 3 1 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 5 1 : ℤ)) • HexagonAtoms315.outerLeftABC) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (negativeScale (rightScaleExponent 3 1 5) • (rowColumnMul HexagonRowColumn315.rows_assocCAB HexagonRowColumn315.cols_right2)) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal3_case_1_5_row_0_2_1 : (((-1 : ℤ) ^ (rightScaleBit 3 1 5).val * positiveScale (rightScaleExponent 3 1 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 5 1 : ℤ)) • HexagonAtoms315.outerLeftABC) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (negativeScale (rightScaleExponent 3 1 5) • (rowColumnMul HexagonRowColumn315.rows_assocCAB HexagonRowColumn315.cols_right2)) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal3_case_1_5_row_0_3_0 : (((-1 : ℤ) ^ (rightScaleBit 3 1 5).val * positiveScale (rightScaleExponent 3 1 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 5 1 : ℤ)) • HexagonAtoms315.outerLeftABC) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (negativeScale (rightScaleExponent 3 1 5) • (rowColumnMul HexagonRowColumn315.rows_assocCAB HexagonRowColumn315.cols_right2)) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal3_case_1_5_row_0_3_1 : (((-1 : ℤ) ^ (rightScaleBit 3 1 5).val * positiveScale (rightScaleExponent 3 1 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 5 1 : ℤ)) • HexagonAtoms315.outerLeftABC) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (negativeScale (rightScaleExponent 3 1 5) • (rowColumnMul HexagonRowColumn315.rows_assocCAB HexagonRowColumn315.cols_right2)) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal3_case_1_5_row_1_0_0 : (((-1 : ℤ) ^ (rightScaleBit 3 1 5).val * positiveScale (rightScaleExponent 3 1 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 5 1 : ℤ)) • HexagonAtoms315.outerLeftABC) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (negativeScale (rightScaleExponent 3 1 5) • (rowColumnMul HexagonRowColumn315.rows_assocCAB HexagonRowColumn315.cols_right2)) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal3_case_1_5_row_1_0_1 : (((-1 : ℤ) ^ (rightScaleBit 3 1 5).val * positiveScale (rightScaleExponent 3 1 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 5 1 : ℤ)) • HexagonAtoms315.outerLeftABC) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (negativeScale (rightScaleExponent 3 1 5) • (rowColumnMul HexagonRowColumn315.rows_assocCAB HexagonRowColumn315.cols_right2)) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal3_case_1_5_row_1_1_0 : (((-1 : ℤ) ^ (rightScaleBit 3 1 5).val * positiveScale (rightScaleExponent 3 1 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 5 1 : ℤ)) • HexagonAtoms315.outerLeftABC) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (negativeScale (rightScaleExponent 3 1 5) • (rowColumnMul HexagonRowColumn315.rows_assocCAB HexagonRowColumn315.cols_right2)) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal3_case_1_5_row_1_1_1 : (((-1 : ℤ) ^ (rightScaleBit 3 1 5).val * positiveScale (rightScaleExponent 3 1 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 5 1 : ℤ)) • HexagonAtoms315.outerLeftABC) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (negativeScale (rightScaleExponent 3 1 5) • (rowColumnMul HexagonRowColumn315.rows_assocCAB HexagonRowColumn315.cols_right2)) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal3_case_1_5_row_1_2_0 : (((-1 : ℤ) ^ (rightScaleBit 3 1 5).val * positiveScale (rightScaleExponent 3 1 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 5 1 : ℤ)) • HexagonAtoms315.outerLeftABC) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (negativeScale (rightScaleExponent 3 1 5) • (rowColumnMul HexagonRowColumn315.rows_assocCAB HexagonRowColumn315.cols_right2)) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal3_case_1_5_row_1_2_1 : (((-1 : ℤ) ^ (rightScaleBit 3 1 5).val * positiveScale (rightScaleExponent 3 1 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 5 1 : ℤ)) • HexagonAtoms315.outerLeftABC) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (negativeScale (rightScaleExponent 3 1 5) • (rowColumnMul HexagonRowColumn315.rows_assocCAB HexagonRowColumn315.cols_right2)) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal3_case_1_5_row_1_3_0 : (((-1 : ℤ) ^ (rightScaleBit 3 1 5).val * positiveScale (rightScaleExponent 3 1 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 5 1 : ℤ)) • HexagonAtoms315.outerLeftABC) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (negativeScale (rightScaleExponent 3 1 5) • (rowColumnMul HexagonRowColumn315.rows_assocCAB HexagonRowColumn315.cols_right2)) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal3_case_1_5_row_1_3_1 : (((-1 : ℤ) ^ (rightScaleBit 3 1 5).val * positiveScale (rightScaleExponent 3 1 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 5 1 : ℤ)) • HexagonAtoms315.outerLeftABC) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (negativeScale (rightScaleExponent 3 1 5) • (rowColumnMul HexagonRowColumn315.rows_assocCAB HexagonRowColumn315.cols_right2)) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal3_case_1_5_checked : ((-1 : ℤ) ^ (rightScaleBit 3 1 5).val * positiveScale (rightScaleExponent 3 1 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 5 1 : ℤ)) • HexagonAtoms315.outerLeftABC = negativeScale (rightScaleExponent 3 1 5) • (rowColumnMul HexagonRowColumn315.rows_assocCAB HexagonRowColumn315.cols_right2) := by
  funext r
  fin_cases r
  · exact rightFinal3_case_1_5_row_0_0_0
  · exact rightFinal3_case_1_5_row_0_0_1
  · exact rightFinal3_case_1_5_row_0_1_0
  · exact rightFinal3_case_1_5_row_0_1_1
  · exact rightFinal3_case_1_5_row_0_2_0
  · exact rightFinal3_case_1_5_row_0_2_1
  · exact rightFinal3_case_1_5_row_0_3_0
  · exact rightFinal3_case_1_5_row_0_3_1
  · exact rightFinal3_case_1_5_row_1_0_0
  · exact rightFinal3_case_1_5_row_1_0_1
  · exact rightFinal3_case_1_5_row_1_1_0
  · exact rightFinal3_case_1_5_row_1_1_1
  · exact rightFinal3_case_1_5_row_1_2_0
  · exact rightFinal3_case_1_5_row_1_2_1
  · exact rightFinal3_case_1_5_row_1_3_0
  · exact rightFinal3_case_1_5_row_1_3_1

set_option backward.isDefEq.respectTransparency false in
theorem rightFinal3_case_1_5 : ((-1 : ℤ) ^ (rightScaleBit 3 1 5).val * positiveScale (rightScaleExponent 3 1 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 5 1 : ℤ)) • outerLeftZ 3 1 5 = negativeScale (rightScaleExponent 3 1 5) • (associatorZ 5 3 1 * right2Middle3 1 5) := by
  simpa only [HexagonAtoms315.assocABC_eq,
    HexagonAtoms315.outerABC_eq,
    HexagonAtoms315.assocBAC_eq,
    HexagonAtoms315.innerABC_eq,
    HexagonAtoms315.innerRightABC_eq,
    HexagonAtoms315.inverseACB_eq,
    HexagonAtoms315.innerACB_eq,
    HexagonAtoms315.assocBCA_eq,
    HexagonAtoms315.innerRightBAC_eq,
    HexagonAtoms315.assocCAB_eq,
    HexagonAtoms315.outerLeftABC_eq,
    HexagonRowColumn315.product0_eq,
    HexagonRowColumn315.product1_eq,
    HexagonRowColumn315.product2_eq,
    HexagonRowColumn315.product3_eq,
    HexagonRowColumn315.product4_eq,
    HexagonRowColumn315.product5_eq,
    HexagonRowColumn315.product6_eq,
    HexagonRowColumn315.product7_eq] using rightFinal3_case_1_5_checked

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonCases3
