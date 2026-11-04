import RMod.BrundanEllis.StackingReferenceHexagonMiddle5
import RMod.BrundanEllis.StackingReferenceSparseMatrixCheck
import RMod.BrundanEllis.StackingReferenceHexagonAtoms573
import RMod.BrundanEllis.StackingReferenceHexagonRowColumn573

/-! Seven closed product identities for one reference triple.
The proof uses only verified atomic maps and ordinary kernel reduction. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
set_option linter.unusedSimpArgs false
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonCases5
open Superfusion

private theorem left0Middle5_eq_case_7_3_row_0_0_0 : (left0Middle5 7 3) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (HexagonAtoms573.assocABC) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_7_3_row_0_0_1 : (left0Middle5 7 3) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (HexagonAtoms573.assocABC) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_7_3_row_0_1_0 : (left0Middle5 7 3) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (HexagonAtoms573.assocABC) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_7_3_row_0_1_1 : (left0Middle5 7 3) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (HexagonAtoms573.assocABC) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_7_3_row_0_2_0 : (left0Middle5 7 3) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (HexagonAtoms573.assocABC) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_7_3_row_0_2_1 : (left0Middle5 7 3) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (HexagonAtoms573.assocABC) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_7_3_row_0_3_0 : (left0Middle5 7 3) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (HexagonAtoms573.assocABC) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_7_3_row_0_3_1 : (left0Middle5 7 3) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (HexagonAtoms573.assocABC) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_7_3_row_1_0_0 : (left0Middle5 7 3) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (HexagonAtoms573.assocABC) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_7_3_row_1_0_1 : (left0Middle5 7 3) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (HexagonAtoms573.assocABC) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_7_3_row_1_1_0 : (left0Middle5 7 3) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (HexagonAtoms573.assocABC) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_7_3_row_1_1_1 : (left0Middle5 7 3) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (HexagonAtoms573.assocABC) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_7_3_row_1_2_0 : (left0Middle5 7 3) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (HexagonAtoms573.assocABC) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_7_3_row_1_2_1 : (left0Middle5 7 3) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (HexagonAtoms573.assocABC) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_7_3_row_1_3_0 : (left0Middle5 7 3) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (HexagonAtoms573.assocABC) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_7_3_row_1_3_1 : (left0Middle5 7 3) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (HexagonAtoms573.assocABC) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_7_3_checked : left0Middle5 7 3 = HexagonAtoms573.assocABC := by
  funext r
  fin_cases r
  · exact left0Middle5_eq_case_7_3_row_0_0_0
  · exact left0Middle5_eq_case_7_3_row_0_0_1
  · exact left0Middle5_eq_case_7_3_row_0_1_0
  · exact left0Middle5_eq_case_7_3_row_0_1_1
  · exact left0Middle5_eq_case_7_3_row_0_2_0
  · exact left0Middle5_eq_case_7_3_row_0_2_1
  · exact left0Middle5_eq_case_7_3_row_0_3_0
  · exact left0Middle5_eq_case_7_3_row_0_3_1
  · exact left0Middle5_eq_case_7_3_row_1_0_0
  · exact left0Middle5_eq_case_7_3_row_1_0_1
  · exact left0Middle5_eq_case_7_3_row_1_1_0
  · exact left0Middle5_eq_case_7_3_row_1_1_1
  · exact left0Middle5_eq_case_7_3_row_1_2_0
  · exact left0Middle5_eq_case_7_3_row_1_2_1
  · exact left0Middle5_eq_case_7_3_row_1_3_0
  · exact left0Middle5_eq_case_7_3_row_1_3_1

set_option backward.isDefEq.respectTransparency false in
theorem left0Middle5_eq_case_7_3 : left0Middle5 7 3 = outerRightZ 5 7 3 * associatorZ 5 7 3 := by
  simpa only [HexagonAtoms573.assocABC_eq,
    HexagonAtoms573.outerABC_eq,
    HexagonAtoms573.assocBAC_eq,
    HexagonAtoms573.innerABC_eq,
    HexagonAtoms573.innerRightABC_eq,
    HexagonAtoms573.inverseACB_eq,
    HexagonAtoms573.innerACB_eq,
    HexagonAtoms573.assocBCA_eq,
    HexagonAtoms573.innerRightBAC_eq,
    HexagonAtoms573.assocCAB_eq,
    HexagonAtoms573.outerLeftABC_eq,
    HexagonRowColumn573.product0_eq,
    HexagonRowColumn573.product1_eq,
    HexagonRowColumn573.product2_eq,
    HexagonRowColumn573.product3_eq,
    HexagonRowColumn573.product4_eq,
    HexagonRowColumn573.product5_eq,
    HexagonRowColumn573.product6_eq,
    HexagonRowColumn573.product7_eq] using left0Middle5_eq_case_7_3_checked

private theorem left1Middle5_eq_case_7_3_row_0_0_0 : (left1Middle5 7 3) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 2)) = (HexagonAtoms573.assocBAC) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_7_3_row_0_0_1 : (left1Middle5 7 3) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 2)) = (HexagonAtoms573.assocBAC) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_7_3_row_1_0_0 : (left1Middle5 7 3) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 2)) = (HexagonAtoms573.assocBAC) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_7_3_row_1_0_1 : (left1Middle5 7 3) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 2)) = (HexagonAtoms573.assocBAC) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_7_3_row_2_0_0 : (left1Middle5 7 3) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 2)) = (HexagonAtoms573.assocBAC) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_7_3_row_2_0_1 : (left1Middle5 7 3) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 2)) = (HexagonAtoms573.assocBAC) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_7_3_row_3_0_0 : (left1Middle5 7 3) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 2)) = (HexagonAtoms573.assocBAC) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_7_3_row_3_0_1 : (left1Middle5 7 3) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 2)) = (HexagonAtoms573.assocBAC) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_7_3_row_4_0_0 : (left1Middle5 7 3) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 2)) = (HexagonAtoms573.assocBAC) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_7_3_row_4_0_1 : (left1Middle5 7 3) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 2)) = (HexagonAtoms573.assocBAC) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_7_3_row_5_0_0 : (left1Middle5 7 3) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 2)) = (HexagonAtoms573.assocBAC) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_7_3_row_5_0_1 : (left1Middle5 7 3) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 2)) = (HexagonAtoms573.assocBAC) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_7_3_row_6_0_0 : (left1Middle5 7 3) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 2)) = (HexagonAtoms573.assocBAC) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_7_3_row_6_0_1 : (left1Middle5 7 3) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 2)) = (HexagonAtoms573.assocBAC) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_7_3_row_7_0_0 : (left1Middle5 7 3) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 2)) = (HexagonAtoms573.assocBAC) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_7_3_row_7_0_1 : (left1Middle5 7 3) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 2)) = (HexagonAtoms573.assocBAC) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_7_3_checked : left1Middle5 7 3 = HexagonAtoms573.assocBAC := by
  funext r
  fin_cases r
  · exact left1Middle5_eq_case_7_3_row_0_0_0
  · exact left1Middle5_eq_case_7_3_row_0_0_1
  · exact left1Middle5_eq_case_7_3_row_1_0_0
  · exact left1Middle5_eq_case_7_3_row_1_0_1
  · exact left1Middle5_eq_case_7_3_row_2_0_0
  · exact left1Middle5_eq_case_7_3_row_2_0_1
  · exact left1Middle5_eq_case_7_3_row_3_0_0
  · exact left1Middle5_eq_case_7_3_row_3_0_1
  · exact left1Middle5_eq_case_7_3_row_4_0_0
  · exact left1Middle5_eq_case_7_3_row_4_0_1
  · exact left1Middle5_eq_case_7_3_row_5_0_0
  · exact left1Middle5_eq_case_7_3_row_5_0_1
  · exact left1Middle5_eq_case_7_3_row_6_0_0
  · exact left1Middle5_eq_case_7_3_row_6_0_1
  · exact left1Middle5_eq_case_7_3_row_7_0_0
  · exact left1Middle5_eq_case_7_3_row_7_0_1

set_option backward.isDefEq.respectTransparency false in
theorem left1Middle5_eq_case_7_3 : left1Middle5 7 3 = associatorZ 7 5 3 * innerLeftZ 5 7 3 := by
  simpa only [HexagonAtoms573.assocABC_eq,
    HexagonAtoms573.outerABC_eq,
    HexagonAtoms573.assocBAC_eq,
    HexagonAtoms573.innerABC_eq,
    HexagonAtoms573.innerRightABC_eq,
    HexagonAtoms573.inverseACB_eq,
    HexagonAtoms573.innerACB_eq,
    HexagonAtoms573.assocBCA_eq,
    HexagonAtoms573.innerRightBAC_eq,
    HexagonAtoms573.assocCAB_eq,
    HexagonAtoms573.outerLeftABC_eq,
    HexagonRowColumn573.product0_eq,
    HexagonRowColumn573.product1_eq,
    HexagonRowColumn573.product2_eq,
    HexagonRowColumn573.product3_eq,
    HexagonRowColumn573.product4_eq,
    HexagonRowColumn573.product5_eq,
    HexagonRowColumn573.product6_eq,
    HexagonRowColumn573.product7_eq] using left1Middle5_eq_case_7_3_checked

private theorem right0Middle5_eq_case_7_3_row_0_0_0 : (right0Middle5 7 3) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (HexagonAtoms573.assocABC) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_7_3_row_0_0_1 : (right0Middle5 7 3) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (HexagonAtoms573.assocABC) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_7_3_row_0_1_0 : (right0Middle5 7 3) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (HexagonAtoms573.assocABC) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_7_3_row_0_1_1 : (right0Middle5 7 3) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (HexagonAtoms573.assocABC) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_7_3_row_0_2_0 : (right0Middle5 7 3) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (HexagonAtoms573.assocABC) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_7_3_row_0_2_1 : (right0Middle5 7 3) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (HexagonAtoms573.assocABC) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_7_3_row_0_3_0 : (right0Middle5 7 3) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (HexagonAtoms573.assocABC) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_7_3_row_0_3_1 : (right0Middle5 7 3) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (HexagonAtoms573.assocABC) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_7_3_row_1_0_0 : (right0Middle5 7 3) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (HexagonAtoms573.assocABC) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_7_3_row_1_0_1 : (right0Middle5 7 3) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (HexagonAtoms573.assocABC) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_7_3_row_1_1_0 : (right0Middle5 7 3) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (HexagonAtoms573.assocABC) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_7_3_row_1_1_1 : (right0Middle5 7 3) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (HexagonAtoms573.assocABC) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_7_3_row_1_2_0 : (right0Middle5 7 3) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (HexagonAtoms573.assocABC) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_7_3_row_1_2_1 : (right0Middle5 7 3) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (HexagonAtoms573.assocABC) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_7_3_row_1_3_0 : (right0Middle5 7 3) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (HexagonAtoms573.assocABC) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_7_3_row_1_3_1 : (right0Middle5 7 3) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (HexagonAtoms573.assocABC) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_7_3_checked : right0Middle5 7 3 = HexagonAtoms573.assocABC := by
  funext r
  fin_cases r
  · exact right0Middle5_eq_case_7_3_row_0_0_0
  · exact right0Middle5_eq_case_7_3_row_0_0_1
  · exact right0Middle5_eq_case_7_3_row_0_1_0
  · exact right0Middle5_eq_case_7_3_row_0_1_1
  · exact right0Middle5_eq_case_7_3_row_0_2_0
  · exact right0Middle5_eq_case_7_3_row_0_2_1
  · exact right0Middle5_eq_case_7_3_row_0_3_0
  · exact right0Middle5_eq_case_7_3_row_0_3_1
  · exact right0Middle5_eq_case_7_3_row_1_0_0
  · exact right0Middle5_eq_case_7_3_row_1_0_1
  · exact right0Middle5_eq_case_7_3_row_1_1_0
  · exact right0Middle5_eq_case_7_3_row_1_1_1
  · exact right0Middle5_eq_case_7_3_row_1_2_0
  · exact right0Middle5_eq_case_7_3_row_1_2_1
  · exact right0Middle5_eq_case_7_3_row_1_3_0
  · exact right0Middle5_eq_case_7_3_row_1_3_1

set_option backward.isDefEq.respectTransparency false in
theorem right0Middle5_eq_case_7_3 : right0Middle5 7 3 = innerRightZ 5 7 3 * associatorZ 5 7 3 := by
  simpa only [HexagonAtoms573.assocABC_eq,
    HexagonAtoms573.outerABC_eq,
    HexagonAtoms573.assocBAC_eq,
    HexagonAtoms573.innerABC_eq,
    HexagonAtoms573.innerRightABC_eq,
    HexagonAtoms573.inverseACB_eq,
    HexagonAtoms573.innerACB_eq,
    HexagonAtoms573.assocBCA_eq,
    HexagonAtoms573.innerRightBAC_eq,
    HexagonAtoms573.assocCAB_eq,
    HexagonAtoms573.outerLeftABC_eq,
    HexagonRowColumn573.product0_eq,
    HexagonRowColumn573.product1_eq,
    HexagonRowColumn573.product2_eq,
    HexagonRowColumn573.product3_eq,
    HexagonRowColumn573.product4_eq,
    HexagonRowColumn573.product5_eq,
    HexagonRowColumn573.product6_eq,
    HexagonRowColumn573.product7_eq] using right0Middle5_eq_case_7_3_checked

private theorem right1Middle5_eq_case_7_3_row_0_0_0 : (right1Middle5 7 3) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn573.rows_inverseACB HexagonRowColumn573.cols_right0) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_7_3_row_0_0_1 : (right1Middle5 7 3) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn573.rows_inverseACB HexagonRowColumn573.cols_right0) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_7_3_row_1_0_0 : (right1Middle5 7 3) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn573.rows_inverseACB HexagonRowColumn573.cols_right0) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_7_3_row_1_0_1 : (right1Middle5 7 3) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn573.rows_inverseACB HexagonRowColumn573.cols_right0) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_7_3_row_2_0_0 : (right1Middle5 7 3) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn573.rows_inverseACB HexagonRowColumn573.cols_right0) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_7_3_row_2_0_1 : (right1Middle5 7 3) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn573.rows_inverseACB HexagonRowColumn573.cols_right0) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_7_3_row_3_0_0 : (right1Middle5 7 3) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn573.rows_inverseACB HexagonRowColumn573.cols_right0) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_7_3_row_3_0_1 : (right1Middle5 7 3) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn573.rows_inverseACB HexagonRowColumn573.cols_right0) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_7_3_row_4_0_0 : (right1Middle5 7 3) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn573.rows_inverseACB HexagonRowColumn573.cols_right0) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_7_3_row_4_0_1 : (right1Middle5 7 3) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn573.rows_inverseACB HexagonRowColumn573.cols_right0) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_7_3_row_5_0_0 : (right1Middle5 7 3) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn573.rows_inverseACB HexagonRowColumn573.cols_right0) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_7_3_row_5_0_1 : (right1Middle5 7 3) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn573.rows_inverseACB HexagonRowColumn573.cols_right0) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_7_3_row_6_0_0 : (right1Middle5 7 3) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn573.rows_inverseACB HexagonRowColumn573.cols_right0) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_7_3_row_6_0_1 : (right1Middle5 7 3) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn573.rows_inverseACB HexagonRowColumn573.cols_right0) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_7_3_row_7_0_0 : (right1Middle5 7 3) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn573.rows_inverseACB HexagonRowColumn573.cols_right0) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_7_3_row_7_0_1 : (right1Middle5 7 3) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn573.rows_inverseACB HexagonRowColumn573.cols_right0) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_7_3_checked : right1Middle5 7 3 = rowColumnMul HexagonRowColumn573.rows_inverseACB HexagonRowColumn573.cols_right0 := by
  funext r
  fin_cases r
  · exact right1Middle5_eq_case_7_3_row_0_0_0
  · exact right1Middle5_eq_case_7_3_row_0_0_1
  · exact right1Middle5_eq_case_7_3_row_1_0_0
  · exact right1Middle5_eq_case_7_3_row_1_0_1
  · exact right1Middle5_eq_case_7_3_row_2_0_0
  · exact right1Middle5_eq_case_7_3_row_2_0_1
  · exact right1Middle5_eq_case_7_3_row_3_0_0
  · exact right1Middle5_eq_case_7_3_row_3_0_1
  · exact right1Middle5_eq_case_7_3_row_4_0_0
  · exact right1Middle5_eq_case_7_3_row_4_0_1
  · exact right1Middle5_eq_case_7_3_row_5_0_0
  · exact right1Middle5_eq_case_7_3_row_5_0_1
  · exact right1Middle5_eq_case_7_3_row_6_0_0
  · exact right1Middle5_eq_case_7_3_row_6_0_1
  · exact right1Middle5_eq_case_7_3_row_7_0_0
  · exact right1Middle5_eq_case_7_3_row_7_0_1

set_option backward.isDefEq.respectTransparency false in
theorem right1Middle5_eq_case_7_3 : right1Middle5 7 3 = associatorInverseZ 5 3 7 * right0Middle5 7 3 := by
  simpa only [HexagonAtoms573.assocABC_eq,
    HexagonAtoms573.outerABC_eq,
    HexagonAtoms573.assocBAC_eq,
    HexagonAtoms573.innerABC_eq,
    HexagonAtoms573.innerRightABC_eq,
    HexagonAtoms573.inverseACB_eq,
    HexagonAtoms573.innerACB_eq,
    HexagonAtoms573.assocBCA_eq,
    HexagonAtoms573.innerRightBAC_eq,
    HexagonAtoms573.assocCAB_eq,
    HexagonAtoms573.outerLeftABC_eq,
    HexagonRowColumn573.product0_eq,
    HexagonRowColumn573.product1_eq,
    HexagonRowColumn573.product2_eq,
    HexagonRowColumn573.product3_eq,
    HexagonRowColumn573.product4_eq,
    HexagonRowColumn573.product5_eq,
    HexagonRowColumn573.product6_eq,
    HexagonRowColumn573.product7_eq] using right1Middle5_eq_case_7_3_checked

private theorem right2Middle5_eq_case_7_3_row_0_0_0 : (right2Middle5 7 3) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 2)) = (right1Middle5 7 3) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_7_3_row_0_0_1 : (right2Middle5 7 3) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 2)) = (right1Middle5 7 3) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_7_3_row_1_0_0 : (right2Middle5 7 3) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 2)) = (right1Middle5 7 3) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_7_3_row_1_0_1 : (right2Middle5 7 3) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 2)) = (right1Middle5 7 3) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_7_3_row_2_0_0 : (right2Middle5 7 3) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 2)) = (right1Middle5 7 3) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_7_3_row_2_0_1 : (right2Middle5 7 3) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 2)) = (right1Middle5 7 3) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_7_3_row_3_0_0 : (right2Middle5 7 3) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 2)) = (right1Middle5 7 3) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_7_3_row_3_0_1 : (right2Middle5 7 3) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 2)) = (right1Middle5 7 3) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_7_3_row_4_0_0 : (right2Middle5 7 3) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 2)) = (right1Middle5 7 3) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_7_3_row_4_0_1 : (right2Middle5 7 3) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 2)) = (right1Middle5 7 3) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_7_3_row_5_0_0 : (right2Middle5 7 3) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 2)) = (right1Middle5 7 3) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_7_3_row_5_0_1 : (right2Middle5 7 3) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 2)) = (right1Middle5 7 3) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_7_3_row_6_0_0 : (right2Middle5 7 3) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 2)) = (right1Middle5 7 3) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_7_3_row_6_0_1 : (right2Middle5 7 3) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 2)) = (right1Middle5 7 3) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_7_3_row_7_0_0 : (right2Middle5 7 3) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 2)) = (right1Middle5 7 3) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_7_3_row_7_0_1 : (right2Middle5 7 3) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 2)) = (right1Middle5 7 3) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_7_3_checked : right2Middle5 7 3 = right1Middle5 7 3 := by
  funext r
  fin_cases r
  · exact right2Middle5_eq_case_7_3_row_0_0_0
  · exact right2Middle5_eq_case_7_3_row_0_0_1
  · exact right2Middle5_eq_case_7_3_row_1_0_0
  · exact right2Middle5_eq_case_7_3_row_1_0_1
  · exact right2Middle5_eq_case_7_3_row_2_0_0
  · exact right2Middle5_eq_case_7_3_row_2_0_1
  · exact right2Middle5_eq_case_7_3_row_3_0_0
  · exact right2Middle5_eq_case_7_3_row_3_0_1
  · exact right2Middle5_eq_case_7_3_row_4_0_0
  · exact right2Middle5_eq_case_7_3_row_4_0_1
  · exact right2Middle5_eq_case_7_3_row_5_0_0
  · exact right2Middle5_eq_case_7_3_row_5_0_1
  · exact right2Middle5_eq_case_7_3_row_6_0_0
  · exact right2Middle5_eq_case_7_3_row_6_0_1
  · exact right2Middle5_eq_case_7_3_row_7_0_0
  · exact right2Middle5_eq_case_7_3_row_7_0_1

set_option backward.isDefEq.respectTransparency false in
theorem right2Middle5_eq_case_7_3 : right2Middle5 7 3 = innerLeftZ 5 3 7 * right1Middle5 7 3 := by
  simpa only [HexagonAtoms573.assocABC_eq,
    HexagonAtoms573.outerABC_eq,
    HexagonAtoms573.assocBAC_eq,
    HexagonAtoms573.innerABC_eq,
    HexagonAtoms573.innerRightABC_eq,
    HexagonAtoms573.inverseACB_eq,
    HexagonAtoms573.innerACB_eq,
    HexagonAtoms573.assocBCA_eq,
    HexagonAtoms573.innerRightBAC_eq,
    HexagonAtoms573.assocCAB_eq,
    HexagonAtoms573.outerLeftABC_eq,
    HexagonRowColumn573.product0_eq,
    HexagonRowColumn573.product1_eq,
    HexagonRowColumn573.product2_eq,
    HexagonRowColumn573.product3_eq,
    HexagonRowColumn573.product4_eq,
    HexagonRowColumn573.product5_eq,
    HexagonRowColumn573.product6_eq,
    HexagonRowColumn573.product7_eq] using right2Middle5_eq_case_7_3_checked

private theorem leftFinal5_case_7_3_row_0_0_0 : (((-1 : ℤ) ^ (leftScaleBit 5 7 3).val * positiveScale (leftScaleExponent 5 7 3)) •
      (rowColumnMul HexagonRowColumn573.rows_assocBCA HexagonRowColumn573.cols_left0)) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 2)) = (negativeScale (leftScaleExponent 5 7 3) • (left1Middle5 7 3)) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal5_case_7_3_row_0_0_1 : (((-1 : ℤ) ^ (leftScaleBit 5 7 3).val * positiveScale (leftScaleExponent 5 7 3)) •
      (rowColumnMul HexagonRowColumn573.rows_assocBCA HexagonRowColumn573.cols_left0)) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 2)) = (negativeScale (leftScaleExponent 5 7 3) • (left1Middle5 7 3)) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal5_case_7_3_row_1_0_0 : (((-1 : ℤ) ^ (leftScaleBit 5 7 3).val * positiveScale (leftScaleExponent 5 7 3)) •
      (rowColumnMul HexagonRowColumn573.rows_assocBCA HexagonRowColumn573.cols_left0)) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 2)) = (negativeScale (leftScaleExponent 5 7 3) • (left1Middle5 7 3)) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal5_case_7_3_row_1_0_1 : (((-1 : ℤ) ^ (leftScaleBit 5 7 3).val * positiveScale (leftScaleExponent 5 7 3)) •
      (rowColumnMul HexagonRowColumn573.rows_assocBCA HexagonRowColumn573.cols_left0)) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 2)) = (negativeScale (leftScaleExponent 5 7 3) • (left1Middle5 7 3)) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal5_case_7_3_row_2_0_0 : (((-1 : ℤ) ^ (leftScaleBit 5 7 3).val * positiveScale (leftScaleExponent 5 7 3)) •
      (rowColumnMul HexagonRowColumn573.rows_assocBCA HexagonRowColumn573.cols_left0)) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 2)) = (negativeScale (leftScaleExponent 5 7 3) • (left1Middle5 7 3)) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal5_case_7_3_row_2_0_1 : (((-1 : ℤ) ^ (leftScaleBit 5 7 3).val * positiveScale (leftScaleExponent 5 7 3)) •
      (rowColumnMul HexagonRowColumn573.rows_assocBCA HexagonRowColumn573.cols_left0)) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 2)) = (negativeScale (leftScaleExponent 5 7 3) • (left1Middle5 7 3)) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal5_case_7_3_row_3_0_0 : (((-1 : ℤ) ^ (leftScaleBit 5 7 3).val * positiveScale (leftScaleExponent 5 7 3)) •
      (rowColumnMul HexagonRowColumn573.rows_assocBCA HexagonRowColumn573.cols_left0)) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 2)) = (negativeScale (leftScaleExponent 5 7 3) • (left1Middle5 7 3)) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal5_case_7_3_row_3_0_1 : (((-1 : ℤ) ^ (leftScaleBit 5 7 3).val * positiveScale (leftScaleExponent 5 7 3)) •
      (rowColumnMul HexagonRowColumn573.rows_assocBCA HexagonRowColumn573.cols_left0)) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 2)) = (negativeScale (leftScaleExponent 5 7 3) • (left1Middle5 7 3)) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal5_case_7_3_row_4_0_0 : (((-1 : ℤ) ^ (leftScaleBit 5 7 3).val * positiveScale (leftScaleExponent 5 7 3)) •
      (rowColumnMul HexagonRowColumn573.rows_assocBCA HexagonRowColumn573.cols_left0)) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 2)) = (negativeScale (leftScaleExponent 5 7 3) • (left1Middle5 7 3)) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal5_case_7_3_row_4_0_1 : (((-1 : ℤ) ^ (leftScaleBit 5 7 3).val * positiveScale (leftScaleExponent 5 7 3)) •
      (rowColumnMul HexagonRowColumn573.rows_assocBCA HexagonRowColumn573.cols_left0)) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 2)) = (negativeScale (leftScaleExponent 5 7 3) • (left1Middle5 7 3)) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal5_case_7_3_row_5_0_0 : (((-1 : ℤ) ^ (leftScaleBit 5 7 3).val * positiveScale (leftScaleExponent 5 7 3)) •
      (rowColumnMul HexagonRowColumn573.rows_assocBCA HexagonRowColumn573.cols_left0)) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 2)) = (negativeScale (leftScaleExponent 5 7 3) • (left1Middle5 7 3)) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal5_case_7_3_row_5_0_1 : (((-1 : ℤ) ^ (leftScaleBit 5 7 3).val * positiveScale (leftScaleExponent 5 7 3)) •
      (rowColumnMul HexagonRowColumn573.rows_assocBCA HexagonRowColumn573.cols_left0)) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 2)) = (negativeScale (leftScaleExponent 5 7 3) • (left1Middle5 7 3)) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal5_case_7_3_row_6_0_0 : (((-1 : ℤ) ^ (leftScaleBit 5 7 3).val * positiveScale (leftScaleExponent 5 7 3)) •
      (rowColumnMul HexagonRowColumn573.rows_assocBCA HexagonRowColumn573.cols_left0)) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 2)) = (negativeScale (leftScaleExponent 5 7 3) • (left1Middle5 7 3)) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal5_case_7_3_row_6_0_1 : (((-1 : ℤ) ^ (leftScaleBit 5 7 3).val * positiveScale (leftScaleExponent 5 7 3)) •
      (rowColumnMul HexagonRowColumn573.rows_assocBCA HexagonRowColumn573.cols_left0)) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 2)) = (negativeScale (leftScaleExponent 5 7 3) • (left1Middle5 7 3)) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal5_case_7_3_row_7_0_0 : (((-1 : ℤ) ^ (leftScaleBit 5 7 3).val * positiveScale (leftScaleExponent 5 7 3)) •
      (rowColumnMul HexagonRowColumn573.rows_assocBCA HexagonRowColumn573.cols_left0)) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 2)) = (negativeScale (leftScaleExponent 5 7 3) • (left1Middle5 7 3)) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal5_case_7_3_row_7_0_1 : (((-1 : ℤ) ^ (leftScaleBit 5 7 3).val * positiveScale (leftScaleExponent 5 7 3)) •
      (rowColumnMul HexagonRowColumn573.rows_assocBCA HexagonRowColumn573.cols_left0)) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 2)) = (negativeScale (leftScaleExponent 5 7 3) • (left1Middle5 7 3)) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal5_case_7_3_checked : ((-1 : ℤ) ^ (leftScaleBit 5 7 3).val * positiveScale (leftScaleExponent 5 7 3)) •
      (rowColumnMul HexagonRowColumn573.rows_assocBCA HexagonRowColumn573.cols_left0) = negativeScale (leftScaleExponent 5 7 3) • (left1Middle5 7 3) := by
  funext r
  fin_cases r
  · exact leftFinal5_case_7_3_row_0_0_0
  · exact leftFinal5_case_7_3_row_0_0_1
  · exact leftFinal5_case_7_3_row_1_0_0
  · exact leftFinal5_case_7_3_row_1_0_1
  · exact leftFinal5_case_7_3_row_2_0_0
  · exact leftFinal5_case_7_3_row_2_0_1
  · exact leftFinal5_case_7_3_row_3_0_0
  · exact leftFinal5_case_7_3_row_3_0_1
  · exact leftFinal5_case_7_3_row_4_0_0
  · exact leftFinal5_case_7_3_row_4_0_1
  · exact leftFinal5_case_7_3_row_5_0_0
  · exact leftFinal5_case_7_3_row_5_0_1
  · exact leftFinal5_case_7_3_row_6_0_0
  · exact leftFinal5_case_7_3_row_6_0_1
  · exact leftFinal5_case_7_3_row_7_0_0
  · exact leftFinal5_case_7_3_row_7_0_1

set_option backward.isDefEq.respectTransparency false in
theorem leftFinal5_case_7_3 : ((-1 : ℤ) ^ (leftScaleBit 5 7 3).val * positiveScale (leftScaleExponent 5 7 3)) •
      (associatorZ 7 3 5 * left0Middle5 7 3) = negativeScale (leftScaleExponent 5 7 3) • (innerRightZ 7 5 3 * left1Middle5 7 3) := by
  simpa only [HexagonAtoms573.assocABC_eq,
    HexagonAtoms573.outerABC_eq,
    HexagonAtoms573.assocBAC_eq,
    HexagonAtoms573.innerABC_eq,
    HexagonAtoms573.innerRightABC_eq,
    HexagonAtoms573.inverseACB_eq,
    HexagonAtoms573.innerACB_eq,
    HexagonAtoms573.assocBCA_eq,
    HexagonAtoms573.innerRightBAC_eq,
    HexagonAtoms573.assocCAB_eq,
    HexagonAtoms573.outerLeftABC_eq,
    HexagonRowColumn573.product0_eq,
    HexagonRowColumn573.product1_eq,
    HexagonRowColumn573.product2_eq,
    HexagonRowColumn573.product3_eq,
    HexagonRowColumn573.product4_eq,
    HexagonRowColumn573.product5_eq,
    HexagonRowColumn573.product6_eq,
    HexagonRowColumn573.product7_eq] using leftFinal5_case_7_3_checked

private theorem rightFinal5_case_7_3_row_0_0_0 : (((-1 : ℤ) ^ (rightScaleBit 5 7 3).val * positiveScale (rightScaleExponent 5 7 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 3 7 : ℤ)) • HexagonAtoms573.outerLeftABC) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (negativeScale (rightScaleExponent 5 7 3) • (rowColumnMul HexagonRowColumn573.rows_assocCAB HexagonRowColumn573.cols_right2)) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal5_case_7_3_row_0_0_1 : (((-1 : ℤ) ^ (rightScaleBit 5 7 3).val * positiveScale (rightScaleExponent 5 7 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 3 7 : ℤ)) • HexagonAtoms573.outerLeftABC) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (negativeScale (rightScaleExponent 5 7 3) • (rowColumnMul HexagonRowColumn573.rows_assocCAB HexagonRowColumn573.cols_right2)) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal5_case_7_3_row_0_1_0 : (((-1 : ℤ) ^ (rightScaleBit 5 7 3).val * positiveScale (rightScaleExponent 5 7 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 3 7 : ℤ)) • HexagonAtoms573.outerLeftABC) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (negativeScale (rightScaleExponent 5 7 3) • (rowColumnMul HexagonRowColumn573.rows_assocCAB HexagonRowColumn573.cols_right2)) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal5_case_7_3_row_0_1_1 : (((-1 : ℤ) ^ (rightScaleBit 5 7 3).val * positiveScale (rightScaleExponent 5 7 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 3 7 : ℤ)) • HexagonAtoms573.outerLeftABC) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (negativeScale (rightScaleExponent 5 7 3) • (rowColumnMul HexagonRowColumn573.rows_assocCAB HexagonRowColumn573.cols_right2)) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal5_case_7_3_row_0_2_0 : (((-1 : ℤ) ^ (rightScaleBit 5 7 3).val * positiveScale (rightScaleExponent 5 7 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 3 7 : ℤ)) • HexagonAtoms573.outerLeftABC) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (negativeScale (rightScaleExponent 5 7 3) • (rowColumnMul HexagonRowColumn573.rows_assocCAB HexagonRowColumn573.cols_right2)) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal5_case_7_3_row_0_2_1 : (((-1 : ℤ) ^ (rightScaleBit 5 7 3).val * positiveScale (rightScaleExponent 5 7 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 3 7 : ℤ)) • HexagonAtoms573.outerLeftABC) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (negativeScale (rightScaleExponent 5 7 3) • (rowColumnMul HexagonRowColumn573.rows_assocCAB HexagonRowColumn573.cols_right2)) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal5_case_7_3_row_0_3_0 : (((-1 : ℤ) ^ (rightScaleBit 5 7 3).val * positiveScale (rightScaleExponent 5 7 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 3 7 : ℤ)) • HexagonAtoms573.outerLeftABC) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (negativeScale (rightScaleExponent 5 7 3) • (rowColumnMul HexagonRowColumn573.rows_assocCAB HexagonRowColumn573.cols_right2)) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal5_case_7_3_row_0_3_1 : (((-1 : ℤ) ^ (rightScaleBit 5 7 3).val * positiveScale (rightScaleExponent 5 7 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 3 7 : ℤ)) • HexagonAtoms573.outerLeftABC) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (negativeScale (rightScaleExponent 5 7 3) • (rowColumnMul HexagonRowColumn573.rows_assocCAB HexagonRowColumn573.cols_right2)) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal5_case_7_3_row_1_0_0 : (((-1 : ℤ) ^ (rightScaleBit 5 7 3).val * positiveScale (rightScaleExponent 5 7 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 3 7 : ℤ)) • HexagonAtoms573.outerLeftABC) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (negativeScale (rightScaleExponent 5 7 3) • (rowColumnMul HexagonRowColumn573.rows_assocCAB HexagonRowColumn573.cols_right2)) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal5_case_7_3_row_1_0_1 : (((-1 : ℤ) ^ (rightScaleBit 5 7 3).val * positiveScale (rightScaleExponent 5 7 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 3 7 : ℤ)) • HexagonAtoms573.outerLeftABC) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (negativeScale (rightScaleExponent 5 7 3) • (rowColumnMul HexagonRowColumn573.rows_assocCAB HexagonRowColumn573.cols_right2)) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal5_case_7_3_row_1_1_0 : (((-1 : ℤ) ^ (rightScaleBit 5 7 3).val * positiveScale (rightScaleExponent 5 7 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 3 7 : ℤ)) • HexagonAtoms573.outerLeftABC) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (negativeScale (rightScaleExponent 5 7 3) • (rowColumnMul HexagonRowColumn573.rows_assocCAB HexagonRowColumn573.cols_right2)) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal5_case_7_3_row_1_1_1 : (((-1 : ℤ) ^ (rightScaleBit 5 7 3).val * positiveScale (rightScaleExponent 5 7 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 3 7 : ℤ)) • HexagonAtoms573.outerLeftABC) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (negativeScale (rightScaleExponent 5 7 3) • (rowColumnMul HexagonRowColumn573.rows_assocCAB HexagonRowColumn573.cols_right2)) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal5_case_7_3_row_1_2_0 : (((-1 : ℤ) ^ (rightScaleBit 5 7 3).val * positiveScale (rightScaleExponent 5 7 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 3 7 : ℤ)) • HexagonAtoms573.outerLeftABC) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (negativeScale (rightScaleExponent 5 7 3) • (rowColumnMul HexagonRowColumn573.rows_assocCAB HexagonRowColumn573.cols_right2)) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal5_case_7_3_row_1_2_1 : (((-1 : ℤ) ^ (rightScaleBit 5 7 3).val * positiveScale (rightScaleExponent 5 7 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 3 7 : ℤ)) • HexagonAtoms573.outerLeftABC) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (negativeScale (rightScaleExponent 5 7 3) • (rowColumnMul HexagonRowColumn573.rows_assocCAB HexagonRowColumn573.cols_right2)) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal5_case_7_3_row_1_3_0 : (((-1 : ℤ) ^ (rightScaleBit 5 7 3).val * positiveScale (rightScaleExponent 5 7 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 3 7 : ℤ)) • HexagonAtoms573.outerLeftABC) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (negativeScale (rightScaleExponent 5 7 3) • (rowColumnMul HexagonRowColumn573.rows_assocCAB HexagonRowColumn573.cols_right2)) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal5_case_7_3_row_1_3_1 : (((-1 : ℤ) ^ (rightScaleBit 5 7 3).val * positiveScale (rightScaleExponent 5 7 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 3 7 : ℤ)) • HexagonAtoms573.outerLeftABC) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (negativeScale (rightScaleExponent 5 7 3) • (rowColumnMul HexagonRowColumn573.rows_assocCAB HexagonRowColumn573.cols_right2)) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal5_case_7_3_checked : ((-1 : ℤ) ^ (rightScaleBit 5 7 3).val * positiveScale (rightScaleExponent 5 7 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 3 7 : ℤ)) • HexagonAtoms573.outerLeftABC = negativeScale (rightScaleExponent 5 7 3) • (rowColumnMul HexagonRowColumn573.rows_assocCAB HexagonRowColumn573.cols_right2) := by
  funext r
  fin_cases r
  · exact rightFinal5_case_7_3_row_0_0_0
  · exact rightFinal5_case_7_3_row_0_0_1
  · exact rightFinal5_case_7_3_row_0_1_0
  · exact rightFinal5_case_7_3_row_0_1_1
  · exact rightFinal5_case_7_3_row_0_2_0
  · exact rightFinal5_case_7_3_row_0_2_1
  · exact rightFinal5_case_7_3_row_0_3_0
  · exact rightFinal5_case_7_3_row_0_3_1
  · exact rightFinal5_case_7_3_row_1_0_0
  · exact rightFinal5_case_7_3_row_1_0_1
  · exact rightFinal5_case_7_3_row_1_1_0
  · exact rightFinal5_case_7_3_row_1_1_1
  · exact rightFinal5_case_7_3_row_1_2_0
  · exact rightFinal5_case_7_3_row_1_2_1
  · exact rightFinal5_case_7_3_row_1_3_0
  · exact rightFinal5_case_7_3_row_1_3_1

set_option backward.isDefEq.respectTransparency false in
theorem rightFinal5_case_7_3 : ((-1 : ℤ) ^ (rightScaleBit 5 7 3).val * positiveScale (rightScaleExponent 5 7 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 3 7 : ℤ)) • outerLeftZ 5 7 3 = negativeScale (rightScaleExponent 5 7 3) • (associatorZ 3 5 7 * right2Middle5 7 3) := by
  simpa only [HexagonAtoms573.assocABC_eq,
    HexagonAtoms573.outerABC_eq,
    HexagonAtoms573.assocBAC_eq,
    HexagonAtoms573.innerABC_eq,
    HexagonAtoms573.innerRightABC_eq,
    HexagonAtoms573.inverseACB_eq,
    HexagonAtoms573.innerACB_eq,
    HexagonAtoms573.assocBCA_eq,
    HexagonAtoms573.innerRightBAC_eq,
    HexagonAtoms573.assocCAB_eq,
    HexagonAtoms573.outerLeftABC_eq,
    HexagonRowColumn573.product0_eq,
    HexagonRowColumn573.product1_eq,
    HexagonRowColumn573.product2_eq,
    HexagonRowColumn573.product3_eq,
    HexagonRowColumn573.product4_eq,
    HexagonRowColumn573.product5_eq,
    HexagonRowColumn573.product6_eq,
    HexagonRowColumn573.product7_eq] using rightFinal5_case_7_3_checked

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonCases5
