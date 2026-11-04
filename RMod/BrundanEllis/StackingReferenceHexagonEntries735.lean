import RMod.BrundanEllis.StackingReferenceHexagonMiddle7
import RMod.BrundanEllis.StackingReferenceSparseMatrixCheck
import RMod.BrundanEllis.StackingReferenceHexagonAtoms735
import RMod.BrundanEllis.StackingReferenceHexagonRowColumn735

/-! Seven closed product identities for one reference triple.
The proof uses only verified atomic maps and ordinary kernel reduction. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
set_option linter.unusedSimpArgs false
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonCases7
open Superfusion

private theorem left0Middle7_eq_case_3_5_row_0_0_0 : (left0Middle7 3 5) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 2)) = (HexagonAtoms735.assocABC) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle7_eq_case_3_5_row_0_0_1 : (left0Middle7 3 5) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 2)) = (HexagonAtoms735.assocABC) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle7_eq_case_3_5_row_1_0_0 : (left0Middle7 3 5) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 2)) = (HexagonAtoms735.assocABC) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle7_eq_case_3_5_row_1_0_1 : (left0Middle7 3 5) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 2)) = (HexagonAtoms735.assocABC) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle7_eq_case_3_5_row_2_0_0 : (left0Middle7 3 5) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 2)) = (HexagonAtoms735.assocABC) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle7_eq_case_3_5_row_2_0_1 : (left0Middle7 3 5) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 2)) = (HexagonAtoms735.assocABC) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle7_eq_case_3_5_row_3_0_0 : (left0Middle7 3 5) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 2)) = (HexagonAtoms735.assocABC) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle7_eq_case_3_5_row_3_0_1 : (left0Middle7 3 5) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 2)) = (HexagonAtoms735.assocABC) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle7_eq_case_3_5_row_4_0_0 : (left0Middle7 3 5) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 2)) = (HexagonAtoms735.assocABC) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle7_eq_case_3_5_row_4_0_1 : (left0Middle7 3 5) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 2)) = (HexagonAtoms735.assocABC) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle7_eq_case_3_5_row_5_0_0 : (left0Middle7 3 5) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 2)) = (HexagonAtoms735.assocABC) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle7_eq_case_3_5_row_5_0_1 : (left0Middle7 3 5) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 2)) = (HexagonAtoms735.assocABC) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle7_eq_case_3_5_row_6_0_0 : (left0Middle7 3 5) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 2)) = (HexagonAtoms735.assocABC) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle7_eq_case_3_5_row_6_0_1 : (left0Middle7 3 5) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 2)) = (HexagonAtoms735.assocABC) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle7_eq_case_3_5_row_7_0_0 : (left0Middle7 3 5) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 2)) = (HexagonAtoms735.assocABC) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle7_eq_case_3_5_row_7_0_1 : (left0Middle7 3 5) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 2)) = (HexagonAtoms735.assocABC) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle7_eq_case_3_5_checked : left0Middle7 3 5 = HexagonAtoms735.assocABC := by
  funext r
  fin_cases r
  · exact left0Middle7_eq_case_3_5_row_0_0_0
  · exact left0Middle7_eq_case_3_5_row_0_0_1
  · exact left0Middle7_eq_case_3_5_row_1_0_0
  · exact left0Middle7_eq_case_3_5_row_1_0_1
  · exact left0Middle7_eq_case_3_5_row_2_0_0
  · exact left0Middle7_eq_case_3_5_row_2_0_1
  · exact left0Middle7_eq_case_3_5_row_3_0_0
  · exact left0Middle7_eq_case_3_5_row_3_0_1
  · exact left0Middle7_eq_case_3_5_row_4_0_0
  · exact left0Middle7_eq_case_3_5_row_4_0_1
  · exact left0Middle7_eq_case_3_5_row_5_0_0
  · exact left0Middle7_eq_case_3_5_row_5_0_1
  · exact left0Middle7_eq_case_3_5_row_6_0_0
  · exact left0Middle7_eq_case_3_5_row_6_0_1
  · exact left0Middle7_eq_case_3_5_row_7_0_0
  · exact left0Middle7_eq_case_3_5_row_7_0_1

set_option backward.isDefEq.respectTransparency false in
theorem left0Middle7_eq_case_3_5 : left0Middle7 3 5 = outerRightZ 7 3 5 * associatorZ 7 3 5 := by
  simpa only [HexagonAtoms735.assocABC_eq,
    HexagonAtoms735.outerABC_eq,
    HexagonAtoms735.assocBAC_eq,
    HexagonAtoms735.innerABC_eq,
    HexagonAtoms735.innerRightABC_eq,
    HexagonAtoms735.inverseACB_eq,
    HexagonAtoms735.innerACB_eq,
    HexagonAtoms735.assocBCA_eq,
    HexagonAtoms735.innerRightBAC_eq,
    HexagonAtoms735.assocCAB_eq,
    HexagonAtoms735.outerLeftABC_eq,
    HexagonRowColumn735.product0_eq,
    HexagonRowColumn735.product1_eq,
    HexagonRowColumn735.product2_eq,
    HexagonRowColumn735.product3_eq,
    HexagonRowColumn735.product4_eq,
    HexagonRowColumn735.product5_eq,
    HexagonRowColumn735.product6_eq,
    HexagonRowColumn735.product7_eq] using left0Middle7_eq_case_3_5_checked

private theorem left1Middle7_eq_case_3_5_row_0_0_0 : (left1Middle7 3 5) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (HexagonAtoms735.assocBAC) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle7_eq_case_3_5_row_0_0_1 : (left1Middle7 3 5) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (HexagonAtoms735.assocBAC) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle7_eq_case_3_5_row_0_1_0 : (left1Middle7 3 5) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (HexagonAtoms735.assocBAC) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle7_eq_case_3_5_row_0_1_1 : (left1Middle7 3 5) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (HexagonAtoms735.assocBAC) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle7_eq_case_3_5_row_0_2_0 : (left1Middle7 3 5) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (HexagonAtoms735.assocBAC) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle7_eq_case_3_5_row_0_2_1 : (left1Middle7 3 5) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (HexagonAtoms735.assocBAC) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle7_eq_case_3_5_row_0_3_0 : (left1Middle7 3 5) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (HexagonAtoms735.assocBAC) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle7_eq_case_3_5_row_0_3_1 : (left1Middle7 3 5) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (HexagonAtoms735.assocBAC) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle7_eq_case_3_5_row_1_0_0 : (left1Middle7 3 5) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (HexagonAtoms735.assocBAC) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle7_eq_case_3_5_row_1_0_1 : (left1Middle7 3 5) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (HexagonAtoms735.assocBAC) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle7_eq_case_3_5_row_1_1_0 : (left1Middle7 3 5) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (HexagonAtoms735.assocBAC) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle7_eq_case_3_5_row_1_1_1 : (left1Middle7 3 5) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (HexagonAtoms735.assocBAC) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle7_eq_case_3_5_row_1_2_0 : (left1Middle7 3 5) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (HexagonAtoms735.assocBAC) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle7_eq_case_3_5_row_1_2_1 : (left1Middle7 3 5) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (HexagonAtoms735.assocBAC) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle7_eq_case_3_5_row_1_3_0 : (left1Middle7 3 5) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (HexagonAtoms735.assocBAC) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle7_eq_case_3_5_row_1_3_1 : (left1Middle7 3 5) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (HexagonAtoms735.assocBAC) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle7_eq_case_3_5_checked : left1Middle7 3 5 = HexagonAtoms735.assocBAC := by
  funext r
  fin_cases r
  · exact left1Middle7_eq_case_3_5_row_0_0_0
  · exact left1Middle7_eq_case_3_5_row_0_0_1
  · exact left1Middle7_eq_case_3_5_row_0_1_0
  · exact left1Middle7_eq_case_3_5_row_0_1_1
  · exact left1Middle7_eq_case_3_5_row_0_2_0
  · exact left1Middle7_eq_case_3_5_row_0_2_1
  · exact left1Middle7_eq_case_3_5_row_0_3_0
  · exact left1Middle7_eq_case_3_5_row_0_3_1
  · exact left1Middle7_eq_case_3_5_row_1_0_0
  · exact left1Middle7_eq_case_3_5_row_1_0_1
  · exact left1Middle7_eq_case_3_5_row_1_1_0
  · exact left1Middle7_eq_case_3_5_row_1_1_1
  · exact left1Middle7_eq_case_3_5_row_1_2_0
  · exact left1Middle7_eq_case_3_5_row_1_2_1
  · exact left1Middle7_eq_case_3_5_row_1_3_0
  · exact left1Middle7_eq_case_3_5_row_1_3_1

set_option backward.isDefEq.respectTransparency false in
theorem left1Middle7_eq_case_3_5 : left1Middle7 3 5 = associatorZ 3 7 5 * innerLeftZ 7 3 5 := by
  simpa only [HexagonAtoms735.assocABC_eq,
    HexagonAtoms735.outerABC_eq,
    HexagonAtoms735.assocBAC_eq,
    HexagonAtoms735.innerABC_eq,
    HexagonAtoms735.innerRightABC_eq,
    HexagonAtoms735.inverseACB_eq,
    HexagonAtoms735.innerACB_eq,
    HexagonAtoms735.assocBCA_eq,
    HexagonAtoms735.innerRightBAC_eq,
    HexagonAtoms735.assocCAB_eq,
    HexagonAtoms735.outerLeftABC_eq,
    HexagonRowColumn735.product0_eq,
    HexagonRowColumn735.product1_eq,
    HexagonRowColumn735.product2_eq,
    HexagonRowColumn735.product3_eq,
    HexagonRowColumn735.product4_eq,
    HexagonRowColumn735.product5_eq,
    HexagonRowColumn735.product6_eq,
    HexagonRowColumn735.product7_eq] using left1Middle7_eq_case_3_5_checked

private theorem right0Middle7_eq_case_3_5_row_0_0_0 : (right0Middle7 3 5) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 2)) = (HexagonAtoms735.assocABC) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle7_eq_case_3_5_row_0_0_1 : (right0Middle7 3 5) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 2)) = (HexagonAtoms735.assocABC) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle7_eq_case_3_5_row_1_0_0 : (right0Middle7 3 5) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 2)) = (HexagonAtoms735.assocABC) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle7_eq_case_3_5_row_1_0_1 : (right0Middle7 3 5) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 2)) = (HexagonAtoms735.assocABC) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle7_eq_case_3_5_row_2_0_0 : (right0Middle7 3 5) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 2)) = (HexagonAtoms735.assocABC) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle7_eq_case_3_5_row_2_0_1 : (right0Middle7 3 5) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 2)) = (HexagonAtoms735.assocABC) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle7_eq_case_3_5_row_3_0_0 : (right0Middle7 3 5) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 2)) = (HexagonAtoms735.assocABC) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle7_eq_case_3_5_row_3_0_1 : (right0Middle7 3 5) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 2)) = (HexagonAtoms735.assocABC) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle7_eq_case_3_5_row_4_0_0 : (right0Middle7 3 5) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 2)) = (HexagonAtoms735.assocABC) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle7_eq_case_3_5_row_4_0_1 : (right0Middle7 3 5) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 2)) = (HexagonAtoms735.assocABC) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle7_eq_case_3_5_row_5_0_0 : (right0Middle7 3 5) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 2)) = (HexagonAtoms735.assocABC) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle7_eq_case_3_5_row_5_0_1 : (right0Middle7 3 5) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 2)) = (HexagonAtoms735.assocABC) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle7_eq_case_3_5_row_6_0_0 : (right0Middle7 3 5) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 2)) = (HexagonAtoms735.assocABC) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle7_eq_case_3_5_row_6_0_1 : (right0Middle7 3 5) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 2)) = (HexagonAtoms735.assocABC) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle7_eq_case_3_5_row_7_0_0 : (right0Middle7 3 5) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 2)) = (HexagonAtoms735.assocABC) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle7_eq_case_3_5_row_7_0_1 : (right0Middle7 3 5) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 2)) = (HexagonAtoms735.assocABC) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle7_eq_case_3_5_checked : right0Middle7 3 5 = HexagonAtoms735.assocABC := by
  funext r
  fin_cases r
  · exact right0Middle7_eq_case_3_5_row_0_0_0
  · exact right0Middle7_eq_case_3_5_row_0_0_1
  · exact right0Middle7_eq_case_3_5_row_1_0_0
  · exact right0Middle7_eq_case_3_5_row_1_0_1
  · exact right0Middle7_eq_case_3_5_row_2_0_0
  · exact right0Middle7_eq_case_3_5_row_2_0_1
  · exact right0Middle7_eq_case_3_5_row_3_0_0
  · exact right0Middle7_eq_case_3_5_row_3_0_1
  · exact right0Middle7_eq_case_3_5_row_4_0_0
  · exact right0Middle7_eq_case_3_5_row_4_0_1
  · exact right0Middle7_eq_case_3_5_row_5_0_0
  · exact right0Middle7_eq_case_3_5_row_5_0_1
  · exact right0Middle7_eq_case_3_5_row_6_0_0
  · exact right0Middle7_eq_case_3_5_row_6_0_1
  · exact right0Middle7_eq_case_3_5_row_7_0_0
  · exact right0Middle7_eq_case_3_5_row_7_0_1

set_option backward.isDefEq.respectTransparency false in
theorem right0Middle7_eq_case_3_5 : right0Middle7 3 5 = innerRightZ 7 3 5 * associatorZ 7 3 5 := by
  simpa only [HexagonAtoms735.assocABC_eq,
    HexagonAtoms735.outerABC_eq,
    HexagonAtoms735.assocBAC_eq,
    HexagonAtoms735.innerABC_eq,
    HexagonAtoms735.innerRightABC_eq,
    HexagonAtoms735.inverseACB_eq,
    HexagonAtoms735.innerACB_eq,
    HexagonAtoms735.assocBCA_eq,
    HexagonAtoms735.innerRightBAC_eq,
    HexagonAtoms735.assocCAB_eq,
    HexagonAtoms735.outerLeftABC_eq,
    HexagonRowColumn735.product0_eq,
    HexagonRowColumn735.product1_eq,
    HexagonRowColumn735.product2_eq,
    HexagonRowColumn735.product3_eq,
    HexagonRowColumn735.product4_eq,
    HexagonRowColumn735.product5_eq,
    HexagonRowColumn735.product6_eq,
    HexagonRowColumn735.product7_eq] using right0Middle7_eq_case_3_5_checked

private theorem right1Middle7_eq_case_3_5_row_0_0_0 : (right1Middle7 3 5) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn735.rows_inverseACB HexagonRowColumn735.cols_right0) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle7_eq_case_3_5_row_0_0_1 : (right1Middle7 3 5) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn735.rows_inverseACB HexagonRowColumn735.cols_right0) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle7_eq_case_3_5_row_0_1_0 : (right1Middle7 3 5) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn735.rows_inverseACB HexagonRowColumn735.cols_right0) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle7_eq_case_3_5_row_0_1_1 : (right1Middle7 3 5) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn735.rows_inverseACB HexagonRowColumn735.cols_right0) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle7_eq_case_3_5_row_0_2_0 : (right1Middle7 3 5) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn735.rows_inverseACB HexagonRowColumn735.cols_right0) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle7_eq_case_3_5_row_0_2_1 : (right1Middle7 3 5) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn735.rows_inverseACB HexagonRowColumn735.cols_right0) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle7_eq_case_3_5_row_0_3_0 : (right1Middle7 3 5) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn735.rows_inverseACB HexagonRowColumn735.cols_right0) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle7_eq_case_3_5_row_0_3_1 : (right1Middle7 3 5) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn735.rows_inverseACB HexagonRowColumn735.cols_right0) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle7_eq_case_3_5_row_1_0_0 : (right1Middle7 3 5) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn735.rows_inverseACB HexagonRowColumn735.cols_right0) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle7_eq_case_3_5_row_1_0_1 : (right1Middle7 3 5) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn735.rows_inverseACB HexagonRowColumn735.cols_right0) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle7_eq_case_3_5_row_1_1_0 : (right1Middle7 3 5) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn735.rows_inverseACB HexagonRowColumn735.cols_right0) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle7_eq_case_3_5_row_1_1_1 : (right1Middle7 3 5) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn735.rows_inverseACB HexagonRowColumn735.cols_right0) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle7_eq_case_3_5_row_1_2_0 : (right1Middle7 3 5) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn735.rows_inverseACB HexagonRowColumn735.cols_right0) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle7_eq_case_3_5_row_1_2_1 : (right1Middle7 3 5) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn735.rows_inverseACB HexagonRowColumn735.cols_right0) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle7_eq_case_3_5_row_1_3_0 : (right1Middle7 3 5) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn735.rows_inverseACB HexagonRowColumn735.cols_right0) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle7_eq_case_3_5_row_1_3_1 : (right1Middle7 3 5) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn735.rows_inverseACB HexagonRowColumn735.cols_right0) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle7_eq_case_3_5_checked : right1Middle7 3 5 = rowColumnMul HexagonRowColumn735.rows_inverseACB HexagonRowColumn735.cols_right0 := by
  funext r
  fin_cases r
  · exact right1Middle7_eq_case_3_5_row_0_0_0
  · exact right1Middle7_eq_case_3_5_row_0_0_1
  · exact right1Middle7_eq_case_3_5_row_0_1_0
  · exact right1Middle7_eq_case_3_5_row_0_1_1
  · exact right1Middle7_eq_case_3_5_row_0_2_0
  · exact right1Middle7_eq_case_3_5_row_0_2_1
  · exact right1Middle7_eq_case_3_5_row_0_3_0
  · exact right1Middle7_eq_case_3_5_row_0_3_1
  · exact right1Middle7_eq_case_3_5_row_1_0_0
  · exact right1Middle7_eq_case_3_5_row_1_0_1
  · exact right1Middle7_eq_case_3_5_row_1_1_0
  · exact right1Middle7_eq_case_3_5_row_1_1_1
  · exact right1Middle7_eq_case_3_5_row_1_2_0
  · exact right1Middle7_eq_case_3_5_row_1_2_1
  · exact right1Middle7_eq_case_3_5_row_1_3_0
  · exact right1Middle7_eq_case_3_5_row_1_3_1

set_option backward.isDefEq.respectTransparency false in
theorem right1Middle7_eq_case_3_5 : right1Middle7 3 5 = associatorInverseZ 7 5 3 * right0Middle7 3 5 := by
  simpa only [HexagonAtoms735.assocABC_eq,
    HexagonAtoms735.outerABC_eq,
    HexagonAtoms735.assocBAC_eq,
    HexagonAtoms735.innerABC_eq,
    HexagonAtoms735.innerRightABC_eq,
    HexagonAtoms735.inverseACB_eq,
    HexagonAtoms735.innerACB_eq,
    HexagonAtoms735.assocBCA_eq,
    HexagonAtoms735.innerRightBAC_eq,
    HexagonAtoms735.assocCAB_eq,
    HexagonAtoms735.outerLeftABC_eq,
    HexagonRowColumn735.product0_eq,
    HexagonRowColumn735.product1_eq,
    HexagonRowColumn735.product2_eq,
    HexagonRowColumn735.product3_eq,
    HexagonRowColumn735.product4_eq,
    HexagonRowColumn735.product5_eq,
    HexagonRowColumn735.product6_eq,
    HexagonRowColumn735.product7_eq] using right1Middle7_eq_case_3_5_checked

private theorem right2Middle7_eq_case_3_5_row_0_0_0 : (right2Middle7 3 5) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (right1Middle7 3 5) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle7_eq_case_3_5_row_0_0_1 : (right2Middle7 3 5) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (right1Middle7 3 5) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle7_eq_case_3_5_row_0_1_0 : (right2Middle7 3 5) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (right1Middle7 3 5) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle7_eq_case_3_5_row_0_1_1 : (right2Middle7 3 5) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (right1Middle7 3 5) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle7_eq_case_3_5_row_0_2_0 : (right2Middle7 3 5) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (right1Middle7 3 5) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle7_eq_case_3_5_row_0_2_1 : (right2Middle7 3 5) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (right1Middle7 3 5) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle7_eq_case_3_5_row_0_3_0 : (right2Middle7 3 5) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (right1Middle7 3 5) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle7_eq_case_3_5_row_0_3_1 : (right2Middle7 3 5) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (right1Middle7 3 5) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle7_eq_case_3_5_row_1_0_0 : (right2Middle7 3 5) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (right1Middle7 3 5) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle7_eq_case_3_5_row_1_0_1 : (right2Middle7 3 5) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (right1Middle7 3 5) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle7_eq_case_3_5_row_1_1_0 : (right2Middle7 3 5) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (right1Middle7 3 5) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle7_eq_case_3_5_row_1_1_1 : (right2Middle7 3 5) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (right1Middle7 3 5) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle7_eq_case_3_5_row_1_2_0 : (right2Middle7 3 5) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (right1Middle7 3 5) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle7_eq_case_3_5_row_1_2_1 : (right2Middle7 3 5) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (right1Middle7 3 5) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle7_eq_case_3_5_row_1_3_0 : (right2Middle7 3 5) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (right1Middle7 3 5) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle7_eq_case_3_5_row_1_3_1 : (right2Middle7 3 5) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (right1Middle7 3 5) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle7_eq_case_3_5_checked : right2Middle7 3 5 = right1Middle7 3 5 := by
  funext r
  fin_cases r
  · exact right2Middle7_eq_case_3_5_row_0_0_0
  · exact right2Middle7_eq_case_3_5_row_0_0_1
  · exact right2Middle7_eq_case_3_5_row_0_1_0
  · exact right2Middle7_eq_case_3_5_row_0_1_1
  · exact right2Middle7_eq_case_3_5_row_0_2_0
  · exact right2Middle7_eq_case_3_5_row_0_2_1
  · exact right2Middle7_eq_case_3_5_row_0_3_0
  · exact right2Middle7_eq_case_3_5_row_0_3_1
  · exact right2Middle7_eq_case_3_5_row_1_0_0
  · exact right2Middle7_eq_case_3_5_row_1_0_1
  · exact right2Middle7_eq_case_3_5_row_1_1_0
  · exact right2Middle7_eq_case_3_5_row_1_1_1
  · exact right2Middle7_eq_case_3_5_row_1_2_0
  · exact right2Middle7_eq_case_3_5_row_1_2_1
  · exact right2Middle7_eq_case_3_5_row_1_3_0
  · exact right2Middle7_eq_case_3_5_row_1_3_1

set_option backward.isDefEq.respectTransparency false in
theorem right2Middle7_eq_case_3_5 : right2Middle7 3 5 = innerLeftZ 7 5 3 * right1Middle7 3 5 := by
  simpa only [HexagonAtoms735.assocABC_eq,
    HexagonAtoms735.outerABC_eq,
    HexagonAtoms735.assocBAC_eq,
    HexagonAtoms735.innerABC_eq,
    HexagonAtoms735.innerRightABC_eq,
    HexagonAtoms735.inverseACB_eq,
    HexagonAtoms735.innerACB_eq,
    HexagonAtoms735.assocBCA_eq,
    HexagonAtoms735.innerRightBAC_eq,
    HexagonAtoms735.assocCAB_eq,
    HexagonAtoms735.outerLeftABC_eq,
    HexagonRowColumn735.product0_eq,
    HexagonRowColumn735.product1_eq,
    HexagonRowColumn735.product2_eq,
    HexagonRowColumn735.product3_eq,
    HexagonRowColumn735.product4_eq,
    HexagonRowColumn735.product5_eq,
    HexagonRowColumn735.product6_eq,
    HexagonRowColumn735.product7_eq] using right2Middle7_eq_case_3_5_checked

private theorem leftFinal7_case_3_5_row_0_0_0 : (((-1 : ℤ) ^ (leftScaleBit 7 3 5).val * positiveScale (leftScaleExponent 7 3 5)) •
      (rowColumnMul HexagonRowColumn735.rows_assocBCA HexagonRowColumn735.cols_left0)) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 7 3 5) • (left1Middle7 3 5)) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal7_case_3_5_row_0_0_1 : (((-1 : ℤ) ^ (leftScaleBit 7 3 5).val * positiveScale (leftScaleExponent 7 3 5)) •
      (rowColumnMul HexagonRowColumn735.rows_assocBCA HexagonRowColumn735.cols_left0)) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 7 3 5) • (left1Middle7 3 5)) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal7_case_3_5_row_0_1_0 : (((-1 : ℤ) ^ (leftScaleBit 7 3 5).val * positiveScale (leftScaleExponent 7 3 5)) •
      (rowColumnMul HexagonRowColumn735.rows_assocBCA HexagonRowColumn735.cols_left0)) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 7 3 5) • (left1Middle7 3 5)) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal7_case_3_5_row_0_1_1 : (((-1 : ℤ) ^ (leftScaleBit 7 3 5).val * positiveScale (leftScaleExponent 7 3 5)) •
      (rowColumnMul HexagonRowColumn735.rows_assocBCA HexagonRowColumn735.cols_left0)) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 7 3 5) • (left1Middle7 3 5)) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal7_case_3_5_row_0_2_0 : (((-1 : ℤ) ^ (leftScaleBit 7 3 5).val * positiveScale (leftScaleExponent 7 3 5)) •
      (rowColumnMul HexagonRowColumn735.rows_assocBCA HexagonRowColumn735.cols_left0)) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 7 3 5) • (left1Middle7 3 5)) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal7_case_3_5_row_0_2_1 : (((-1 : ℤ) ^ (leftScaleBit 7 3 5).val * positiveScale (leftScaleExponent 7 3 5)) •
      (rowColumnMul HexagonRowColumn735.rows_assocBCA HexagonRowColumn735.cols_left0)) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 7 3 5) • (left1Middle7 3 5)) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal7_case_3_5_row_0_3_0 : (((-1 : ℤ) ^ (leftScaleBit 7 3 5).val * positiveScale (leftScaleExponent 7 3 5)) •
      (rowColumnMul HexagonRowColumn735.rows_assocBCA HexagonRowColumn735.cols_left0)) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 7 3 5) • (left1Middle7 3 5)) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal7_case_3_5_row_0_3_1 : (((-1 : ℤ) ^ (leftScaleBit 7 3 5).val * positiveScale (leftScaleExponent 7 3 5)) •
      (rowColumnMul HexagonRowColumn735.rows_assocBCA HexagonRowColumn735.cols_left0)) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 7 3 5) • (left1Middle7 3 5)) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal7_case_3_5_row_1_0_0 : (((-1 : ℤ) ^ (leftScaleBit 7 3 5).val * positiveScale (leftScaleExponent 7 3 5)) •
      (rowColumnMul HexagonRowColumn735.rows_assocBCA HexagonRowColumn735.cols_left0)) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 7 3 5) • (left1Middle7 3 5)) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal7_case_3_5_row_1_0_1 : (((-1 : ℤ) ^ (leftScaleBit 7 3 5).val * positiveScale (leftScaleExponent 7 3 5)) •
      (rowColumnMul HexagonRowColumn735.rows_assocBCA HexagonRowColumn735.cols_left0)) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 7 3 5) • (left1Middle7 3 5)) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal7_case_3_5_row_1_1_0 : (((-1 : ℤ) ^ (leftScaleBit 7 3 5).val * positiveScale (leftScaleExponent 7 3 5)) •
      (rowColumnMul HexagonRowColumn735.rows_assocBCA HexagonRowColumn735.cols_left0)) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 7 3 5) • (left1Middle7 3 5)) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal7_case_3_5_row_1_1_1 : (((-1 : ℤ) ^ (leftScaleBit 7 3 5).val * positiveScale (leftScaleExponent 7 3 5)) •
      (rowColumnMul HexagonRowColumn735.rows_assocBCA HexagonRowColumn735.cols_left0)) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 7 3 5) • (left1Middle7 3 5)) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal7_case_3_5_row_1_2_0 : (((-1 : ℤ) ^ (leftScaleBit 7 3 5).val * positiveScale (leftScaleExponent 7 3 5)) •
      (rowColumnMul HexagonRowColumn735.rows_assocBCA HexagonRowColumn735.cols_left0)) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 7 3 5) • (left1Middle7 3 5)) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal7_case_3_5_row_1_2_1 : (((-1 : ℤ) ^ (leftScaleBit 7 3 5).val * positiveScale (leftScaleExponent 7 3 5)) •
      (rowColumnMul HexagonRowColumn735.rows_assocBCA HexagonRowColumn735.cols_left0)) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 7 3 5) • (left1Middle7 3 5)) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal7_case_3_5_row_1_3_0 : (((-1 : ℤ) ^ (leftScaleBit 7 3 5).val * positiveScale (leftScaleExponent 7 3 5)) •
      (rowColumnMul HexagonRowColumn735.rows_assocBCA HexagonRowColumn735.cols_left0)) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 7 3 5) • (left1Middle7 3 5)) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal7_case_3_5_row_1_3_1 : (((-1 : ℤ) ^ (leftScaleBit 7 3 5).val * positiveScale (leftScaleExponent 7 3 5)) •
      (rowColumnMul HexagonRowColumn735.rows_assocBCA HexagonRowColumn735.cols_left0)) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 7 3 5) • (left1Middle7 3 5)) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal7_case_3_5_checked : ((-1 : ℤ) ^ (leftScaleBit 7 3 5).val * positiveScale (leftScaleExponent 7 3 5)) •
      (rowColumnMul HexagonRowColumn735.rows_assocBCA HexagonRowColumn735.cols_left0) = negativeScale (leftScaleExponent 7 3 5) • (left1Middle7 3 5) := by
  funext r
  fin_cases r
  · exact leftFinal7_case_3_5_row_0_0_0
  · exact leftFinal7_case_3_5_row_0_0_1
  · exact leftFinal7_case_3_5_row_0_1_0
  · exact leftFinal7_case_3_5_row_0_1_1
  · exact leftFinal7_case_3_5_row_0_2_0
  · exact leftFinal7_case_3_5_row_0_2_1
  · exact leftFinal7_case_3_5_row_0_3_0
  · exact leftFinal7_case_3_5_row_0_3_1
  · exact leftFinal7_case_3_5_row_1_0_0
  · exact leftFinal7_case_3_5_row_1_0_1
  · exact leftFinal7_case_3_5_row_1_1_0
  · exact leftFinal7_case_3_5_row_1_1_1
  · exact leftFinal7_case_3_5_row_1_2_0
  · exact leftFinal7_case_3_5_row_1_2_1
  · exact leftFinal7_case_3_5_row_1_3_0
  · exact leftFinal7_case_3_5_row_1_3_1

set_option backward.isDefEq.respectTransparency false in
theorem leftFinal7_case_3_5 : ((-1 : ℤ) ^ (leftScaleBit 7 3 5).val * positiveScale (leftScaleExponent 7 3 5)) •
      (associatorZ 3 5 7 * left0Middle7 3 5) = negativeScale (leftScaleExponent 7 3 5) • (innerRightZ 3 7 5 * left1Middle7 3 5) := by
  simpa only [HexagonAtoms735.assocABC_eq,
    HexagonAtoms735.outerABC_eq,
    HexagonAtoms735.assocBAC_eq,
    HexagonAtoms735.innerABC_eq,
    HexagonAtoms735.innerRightABC_eq,
    HexagonAtoms735.inverseACB_eq,
    HexagonAtoms735.innerACB_eq,
    HexagonAtoms735.assocBCA_eq,
    HexagonAtoms735.innerRightBAC_eq,
    HexagonAtoms735.assocCAB_eq,
    HexagonAtoms735.outerLeftABC_eq,
    HexagonRowColumn735.product0_eq,
    HexagonRowColumn735.product1_eq,
    HexagonRowColumn735.product2_eq,
    HexagonRowColumn735.product3_eq,
    HexagonRowColumn735.product4_eq,
    HexagonRowColumn735.product5_eq,
    HexagonRowColumn735.product6_eq,
    HexagonRowColumn735.product7_eq] using leftFinal7_case_3_5_checked

private theorem rightFinal7_case_3_5_row_0_0_0 : (((-1 : ℤ) ^ (rightScaleBit 7 3 5).val * positiveScale (rightScaleExponent 7 3 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 5 3 : ℤ)) • HexagonAtoms735.outerLeftABC) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (negativeScale (rightScaleExponent 7 3 5) • (rowColumnMul HexagonRowColumn735.rows_assocCAB HexagonRowColumn735.cols_right2)) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal7_case_3_5_row_0_0_1 : (((-1 : ℤ) ^ (rightScaleBit 7 3 5).val * positiveScale (rightScaleExponent 7 3 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 5 3 : ℤ)) • HexagonAtoms735.outerLeftABC) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (negativeScale (rightScaleExponent 7 3 5) • (rowColumnMul HexagonRowColumn735.rows_assocCAB HexagonRowColumn735.cols_right2)) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal7_case_3_5_row_0_1_0 : (((-1 : ℤ) ^ (rightScaleBit 7 3 5).val * positiveScale (rightScaleExponent 7 3 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 5 3 : ℤ)) • HexagonAtoms735.outerLeftABC) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (negativeScale (rightScaleExponent 7 3 5) • (rowColumnMul HexagonRowColumn735.rows_assocCAB HexagonRowColumn735.cols_right2)) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal7_case_3_5_row_0_1_1 : (((-1 : ℤ) ^ (rightScaleBit 7 3 5).val * positiveScale (rightScaleExponent 7 3 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 5 3 : ℤ)) • HexagonAtoms735.outerLeftABC) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (negativeScale (rightScaleExponent 7 3 5) • (rowColumnMul HexagonRowColumn735.rows_assocCAB HexagonRowColumn735.cols_right2)) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal7_case_3_5_row_0_2_0 : (((-1 : ℤ) ^ (rightScaleBit 7 3 5).val * positiveScale (rightScaleExponent 7 3 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 5 3 : ℤ)) • HexagonAtoms735.outerLeftABC) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (negativeScale (rightScaleExponent 7 3 5) • (rowColumnMul HexagonRowColumn735.rows_assocCAB HexagonRowColumn735.cols_right2)) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal7_case_3_5_row_0_2_1 : (((-1 : ℤ) ^ (rightScaleBit 7 3 5).val * positiveScale (rightScaleExponent 7 3 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 5 3 : ℤ)) • HexagonAtoms735.outerLeftABC) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (negativeScale (rightScaleExponent 7 3 5) • (rowColumnMul HexagonRowColumn735.rows_assocCAB HexagonRowColumn735.cols_right2)) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal7_case_3_5_row_0_3_0 : (((-1 : ℤ) ^ (rightScaleBit 7 3 5).val * positiveScale (rightScaleExponent 7 3 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 5 3 : ℤ)) • HexagonAtoms735.outerLeftABC) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (negativeScale (rightScaleExponent 7 3 5) • (rowColumnMul HexagonRowColumn735.rows_assocCAB HexagonRowColumn735.cols_right2)) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal7_case_3_5_row_0_3_1 : (((-1 : ℤ) ^ (rightScaleBit 7 3 5).val * positiveScale (rightScaleExponent 7 3 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 5 3 : ℤ)) • HexagonAtoms735.outerLeftABC) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (negativeScale (rightScaleExponent 7 3 5) • (rowColumnMul HexagonRowColumn735.rows_assocCAB HexagonRowColumn735.cols_right2)) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal7_case_3_5_row_1_0_0 : (((-1 : ℤ) ^ (rightScaleBit 7 3 5).val * positiveScale (rightScaleExponent 7 3 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 5 3 : ℤ)) • HexagonAtoms735.outerLeftABC) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (negativeScale (rightScaleExponent 7 3 5) • (rowColumnMul HexagonRowColumn735.rows_assocCAB HexagonRowColumn735.cols_right2)) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal7_case_3_5_row_1_0_1 : (((-1 : ℤ) ^ (rightScaleBit 7 3 5).val * positiveScale (rightScaleExponent 7 3 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 5 3 : ℤ)) • HexagonAtoms735.outerLeftABC) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (negativeScale (rightScaleExponent 7 3 5) • (rowColumnMul HexagonRowColumn735.rows_assocCAB HexagonRowColumn735.cols_right2)) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal7_case_3_5_row_1_1_0 : (((-1 : ℤ) ^ (rightScaleBit 7 3 5).val * positiveScale (rightScaleExponent 7 3 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 5 3 : ℤ)) • HexagonAtoms735.outerLeftABC) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (negativeScale (rightScaleExponent 7 3 5) • (rowColumnMul HexagonRowColumn735.rows_assocCAB HexagonRowColumn735.cols_right2)) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal7_case_3_5_row_1_1_1 : (((-1 : ℤ) ^ (rightScaleBit 7 3 5).val * positiveScale (rightScaleExponent 7 3 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 5 3 : ℤ)) • HexagonAtoms735.outerLeftABC) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (negativeScale (rightScaleExponent 7 3 5) • (rowColumnMul HexagonRowColumn735.rows_assocCAB HexagonRowColumn735.cols_right2)) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal7_case_3_5_row_1_2_0 : (((-1 : ℤ) ^ (rightScaleBit 7 3 5).val * positiveScale (rightScaleExponent 7 3 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 5 3 : ℤ)) • HexagonAtoms735.outerLeftABC) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (negativeScale (rightScaleExponent 7 3 5) • (rowColumnMul HexagonRowColumn735.rows_assocCAB HexagonRowColumn735.cols_right2)) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal7_case_3_5_row_1_2_1 : (((-1 : ℤ) ^ (rightScaleBit 7 3 5).val * positiveScale (rightScaleExponent 7 3 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 5 3 : ℤ)) • HexagonAtoms735.outerLeftABC) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (negativeScale (rightScaleExponent 7 3 5) • (rowColumnMul HexagonRowColumn735.rows_assocCAB HexagonRowColumn735.cols_right2)) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal7_case_3_5_row_1_3_0 : (((-1 : ℤ) ^ (rightScaleBit 7 3 5).val * positiveScale (rightScaleExponent 7 3 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 5 3 : ℤ)) • HexagonAtoms735.outerLeftABC) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (negativeScale (rightScaleExponent 7 3 5) • (rowColumnMul HexagonRowColumn735.rows_assocCAB HexagonRowColumn735.cols_right2)) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal7_case_3_5_row_1_3_1 : (((-1 : ℤ) ^ (rightScaleBit 7 3 5).val * positiveScale (rightScaleExponent 7 3 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 5 3 : ℤ)) • HexagonAtoms735.outerLeftABC) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (negativeScale (rightScaleExponent 7 3 5) • (rowColumnMul HexagonRowColumn735.rows_assocCAB HexagonRowColumn735.cols_right2)) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal7_case_3_5_checked : ((-1 : ℤ) ^ (rightScaleBit 7 3 5).val * positiveScale (rightScaleExponent 7 3 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 5 3 : ℤ)) • HexagonAtoms735.outerLeftABC = negativeScale (rightScaleExponent 7 3 5) • (rowColumnMul HexagonRowColumn735.rows_assocCAB HexagonRowColumn735.cols_right2) := by
  funext r
  fin_cases r
  · exact rightFinal7_case_3_5_row_0_0_0
  · exact rightFinal7_case_3_5_row_0_0_1
  · exact rightFinal7_case_3_5_row_0_1_0
  · exact rightFinal7_case_3_5_row_0_1_1
  · exact rightFinal7_case_3_5_row_0_2_0
  · exact rightFinal7_case_3_5_row_0_2_1
  · exact rightFinal7_case_3_5_row_0_3_0
  · exact rightFinal7_case_3_5_row_0_3_1
  · exact rightFinal7_case_3_5_row_1_0_0
  · exact rightFinal7_case_3_5_row_1_0_1
  · exact rightFinal7_case_3_5_row_1_1_0
  · exact rightFinal7_case_3_5_row_1_1_1
  · exact rightFinal7_case_3_5_row_1_2_0
  · exact rightFinal7_case_3_5_row_1_2_1
  · exact rightFinal7_case_3_5_row_1_3_0
  · exact rightFinal7_case_3_5_row_1_3_1

set_option backward.isDefEq.respectTransparency false in
theorem rightFinal7_case_3_5 : ((-1 : ℤ) ^ (rightScaleBit 7 3 5).val * positiveScale (rightScaleExponent 7 3 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 5 3 : ℤ)) • outerLeftZ 7 3 5 = negativeScale (rightScaleExponent 7 3 5) • (associatorZ 5 7 3 * right2Middle7 3 5) := by
  simpa only [HexagonAtoms735.assocABC_eq,
    HexagonAtoms735.outerABC_eq,
    HexagonAtoms735.assocBAC_eq,
    HexagonAtoms735.innerABC_eq,
    HexagonAtoms735.innerRightABC_eq,
    HexagonAtoms735.inverseACB_eq,
    HexagonAtoms735.innerACB_eq,
    HexagonAtoms735.assocBCA_eq,
    HexagonAtoms735.innerRightBAC_eq,
    HexagonAtoms735.assocCAB_eq,
    HexagonAtoms735.outerLeftABC_eq,
    HexagonRowColumn735.product0_eq,
    HexagonRowColumn735.product1_eq,
    HexagonRowColumn735.product2_eq,
    HexagonRowColumn735.product3_eq,
    HexagonRowColumn735.product4_eq,
    HexagonRowColumn735.product5_eq,
    HexagonRowColumn735.product6_eq,
    HexagonRowColumn735.product7_eq] using rightFinal7_case_3_5_checked

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonCases7
