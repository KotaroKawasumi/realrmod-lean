import RMod.BrundanEllis.StackingReferenceHexagonMiddle5
import RMod.BrundanEllis.StackingReferenceSparseMatrixCheck
import RMod.BrundanEllis.StackingReferenceHexagonAtoms537
import RMod.BrundanEllis.StackingReferenceHexagonRowColumn537

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

private theorem left0Middle5_eq_case_3_7_row_0_0_0 : (left0Middle5 3 7) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (HexagonAtoms537.assocABC) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_3_7_row_0_0_1 : (left0Middle5 3 7) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (HexagonAtoms537.assocABC) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_3_7_row_0_1_0 : (left0Middle5 3 7) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (HexagonAtoms537.assocABC) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_3_7_row_0_1_1 : (left0Middle5 3 7) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (HexagonAtoms537.assocABC) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_3_7_row_0_2_0 : (left0Middle5 3 7) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (HexagonAtoms537.assocABC) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_3_7_row_0_2_1 : (left0Middle5 3 7) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (HexagonAtoms537.assocABC) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_3_7_row_0_3_0 : (left0Middle5 3 7) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (HexagonAtoms537.assocABC) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_3_7_row_0_3_1 : (left0Middle5 3 7) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (HexagonAtoms537.assocABC) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_3_7_row_1_0_0 : (left0Middle5 3 7) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (HexagonAtoms537.assocABC) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_3_7_row_1_0_1 : (left0Middle5 3 7) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (HexagonAtoms537.assocABC) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_3_7_row_1_1_0 : (left0Middle5 3 7) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (HexagonAtoms537.assocABC) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_3_7_row_1_1_1 : (left0Middle5 3 7) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (HexagonAtoms537.assocABC) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_3_7_row_1_2_0 : (left0Middle5 3 7) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (HexagonAtoms537.assocABC) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_3_7_row_1_2_1 : (left0Middle5 3 7) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (HexagonAtoms537.assocABC) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_3_7_row_1_3_0 : (left0Middle5 3 7) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (HexagonAtoms537.assocABC) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_3_7_row_1_3_1 : (left0Middle5 3 7) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (HexagonAtoms537.assocABC) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_3_7_checked : left0Middle5 3 7 = HexagonAtoms537.assocABC := by
  funext r
  fin_cases r
  · exact left0Middle5_eq_case_3_7_row_0_0_0
  · exact left0Middle5_eq_case_3_7_row_0_0_1
  · exact left0Middle5_eq_case_3_7_row_0_1_0
  · exact left0Middle5_eq_case_3_7_row_0_1_1
  · exact left0Middle5_eq_case_3_7_row_0_2_0
  · exact left0Middle5_eq_case_3_7_row_0_2_1
  · exact left0Middle5_eq_case_3_7_row_0_3_0
  · exact left0Middle5_eq_case_3_7_row_0_3_1
  · exact left0Middle5_eq_case_3_7_row_1_0_0
  · exact left0Middle5_eq_case_3_7_row_1_0_1
  · exact left0Middle5_eq_case_3_7_row_1_1_0
  · exact left0Middle5_eq_case_3_7_row_1_1_1
  · exact left0Middle5_eq_case_3_7_row_1_2_0
  · exact left0Middle5_eq_case_3_7_row_1_2_1
  · exact left0Middle5_eq_case_3_7_row_1_3_0
  · exact left0Middle5_eq_case_3_7_row_1_3_1

set_option backward.isDefEq.respectTransparency false in
theorem left0Middle5_eq_case_3_7 : left0Middle5 3 7 = outerRightZ 5 3 7 * associatorZ 5 3 7 := by
  simpa only [HexagonAtoms537.assocABC_eq,
    HexagonAtoms537.outerABC_eq,
    HexagonAtoms537.assocBAC_eq,
    HexagonAtoms537.innerABC_eq,
    HexagonAtoms537.innerRightABC_eq,
    HexagonAtoms537.inverseACB_eq,
    HexagonAtoms537.innerACB_eq,
    HexagonAtoms537.assocBCA_eq,
    HexagonAtoms537.innerRightBAC_eq,
    HexagonAtoms537.assocCAB_eq,
    HexagonAtoms537.outerLeftABC_eq,
    HexagonRowColumn537.product0_eq,
    HexagonRowColumn537.product1_eq,
    HexagonRowColumn537.product2_eq,
    HexagonRowColumn537.product3_eq,
    HexagonRowColumn537.product4_eq,
    HexagonRowColumn537.product5_eq,
    HexagonRowColumn537.product6_eq,
    HexagonRowColumn537.product7_eq] using left0Middle5_eq_case_3_7_checked

private theorem left1Middle5_eq_case_3_7_row_0_0_0 : (left1Middle5 3 7) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (HexagonAtoms537.assocBAC) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_3_7_row_0_0_1 : (left1Middle5 3 7) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (HexagonAtoms537.assocBAC) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_3_7_row_0_1_0 : (left1Middle5 3 7) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (HexagonAtoms537.assocBAC) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_3_7_row_0_1_1 : (left1Middle5 3 7) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (HexagonAtoms537.assocBAC) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_3_7_row_0_2_0 : (left1Middle5 3 7) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (HexagonAtoms537.assocBAC) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_3_7_row_0_2_1 : (left1Middle5 3 7) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (HexagonAtoms537.assocBAC) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_3_7_row_0_3_0 : (left1Middle5 3 7) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (HexagonAtoms537.assocBAC) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_3_7_row_0_3_1 : (left1Middle5 3 7) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (HexagonAtoms537.assocBAC) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_3_7_row_1_0_0 : (left1Middle5 3 7) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (HexagonAtoms537.assocBAC) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_3_7_row_1_0_1 : (left1Middle5 3 7) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (HexagonAtoms537.assocBAC) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_3_7_row_1_1_0 : (left1Middle5 3 7) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (HexagonAtoms537.assocBAC) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_3_7_row_1_1_1 : (left1Middle5 3 7) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (HexagonAtoms537.assocBAC) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_3_7_row_1_2_0 : (left1Middle5 3 7) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (HexagonAtoms537.assocBAC) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_3_7_row_1_2_1 : (left1Middle5 3 7) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (HexagonAtoms537.assocBAC) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_3_7_row_1_3_0 : (left1Middle5 3 7) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (HexagonAtoms537.assocBAC) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_3_7_row_1_3_1 : (left1Middle5 3 7) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (HexagonAtoms537.assocBAC) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_3_7_checked : left1Middle5 3 7 = HexagonAtoms537.assocBAC := by
  funext r
  fin_cases r
  · exact left1Middle5_eq_case_3_7_row_0_0_0
  · exact left1Middle5_eq_case_3_7_row_0_0_1
  · exact left1Middle5_eq_case_3_7_row_0_1_0
  · exact left1Middle5_eq_case_3_7_row_0_1_1
  · exact left1Middle5_eq_case_3_7_row_0_2_0
  · exact left1Middle5_eq_case_3_7_row_0_2_1
  · exact left1Middle5_eq_case_3_7_row_0_3_0
  · exact left1Middle5_eq_case_3_7_row_0_3_1
  · exact left1Middle5_eq_case_3_7_row_1_0_0
  · exact left1Middle5_eq_case_3_7_row_1_0_1
  · exact left1Middle5_eq_case_3_7_row_1_1_0
  · exact left1Middle5_eq_case_3_7_row_1_1_1
  · exact left1Middle5_eq_case_3_7_row_1_2_0
  · exact left1Middle5_eq_case_3_7_row_1_2_1
  · exact left1Middle5_eq_case_3_7_row_1_3_0
  · exact left1Middle5_eq_case_3_7_row_1_3_1

set_option backward.isDefEq.respectTransparency false in
theorem left1Middle5_eq_case_3_7 : left1Middle5 3 7 = associatorZ 3 5 7 * innerLeftZ 5 3 7 := by
  simpa only [HexagonAtoms537.assocABC_eq,
    HexagonAtoms537.outerABC_eq,
    HexagonAtoms537.assocBAC_eq,
    HexagonAtoms537.innerABC_eq,
    HexagonAtoms537.innerRightABC_eq,
    HexagonAtoms537.inverseACB_eq,
    HexagonAtoms537.innerACB_eq,
    HexagonAtoms537.assocBCA_eq,
    HexagonAtoms537.innerRightBAC_eq,
    HexagonAtoms537.assocCAB_eq,
    HexagonAtoms537.outerLeftABC_eq,
    HexagonRowColumn537.product0_eq,
    HexagonRowColumn537.product1_eq,
    HexagonRowColumn537.product2_eq,
    HexagonRowColumn537.product3_eq,
    HexagonRowColumn537.product4_eq,
    HexagonRowColumn537.product5_eq,
    HexagonRowColumn537.product6_eq,
    HexagonRowColumn537.product7_eq] using left1Middle5_eq_case_3_7_checked

private theorem right0Middle5_eq_case_3_7_row_0_0_0 : (right0Middle5 3 7) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (HexagonAtoms537.assocABC) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_3_7_row_0_0_1 : (right0Middle5 3 7) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (HexagonAtoms537.assocABC) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_3_7_row_0_1_0 : (right0Middle5 3 7) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (HexagonAtoms537.assocABC) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_3_7_row_0_1_1 : (right0Middle5 3 7) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (HexagonAtoms537.assocABC) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_3_7_row_0_2_0 : (right0Middle5 3 7) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (HexagonAtoms537.assocABC) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_3_7_row_0_2_1 : (right0Middle5 3 7) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (HexagonAtoms537.assocABC) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_3_7_row_0_3_0 : (right0Middle5 3 7) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (HexagonAtoms537.assocABC) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_3_7_row_0_3_1 : (right0Middle5 3 7) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (HexagonAtoms537.assocABC) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_3_7_row_1_0_0 : (right0Middle5 3 7) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (HexagonAtoms537.assocABC) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_3_7_row_1_0_1 : (right0Middle5 3 7) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (HexagonAtoms537.assocABC) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_3_7_row_1_1_0 : (right0Middle5 3 7) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (HexagonAtoms537.assocABC) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_3_7_row_1_1_1 : (right0Middle5 3 7) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (HexagonAtoms537.assocABC) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_3_7_row_1_2_0 : (right0Middle5 3 7) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (HexagonAtoms537.assocABC) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_3_7_row_1_2_1 : (right0Middle5 3 7) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (HexagonAtoms537.assocABC) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_3_7_row_1_3_0 : (right0Middle5 3 7) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (HexagonAtoms537.assocABC) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_3_7_row_1_3_1 : (right0Middle5 3 7) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (HexagonAtoms537.assocABC) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_3_7_checked : right0Middle5 3 7 = HexagonAtoms537.assocABC := by
  funext r
  fin_cases r
  · exact right0Middle5_eq_case_3_7_row_0_0_0
  · exact right0Middle5_eq_case_3_7_row_0_0_1
  · exact right0Middle5_eq_case_3_7_row_0_1_0
  · exact right0Middle5_eq_case_3_7_row_0_1_1
  · exact right0Middle5_eq_case_3_7_row_0_2_0
  · exact right0Middle5_eq_case_3_7_row_0_2_1
  · exact right0Middle5_eq_case_3_7_row_0_3_0
  · exact right0Middle5_eq_case_3_7_row_0_3_1
  · exact right0Middle5_eq_case_3_7_row_1_0_0
  · exact right0Middle5_eq_case_3_7_row_1_0_1
  · exact right0Middle5_eq_case_3_7_row_1_1_0
  · exact right0Middle5_eq_case_3_7_row_1_1_1
  · exact right0Middle5_eq_case_3_7_row_1_2_0
  · exact right0Middle5_eq_case_3_7_row_1_2_1
  · exact right0Middle5_eq_case_3_7_row_1_3_0
  · exact right0Middle5_eq_case_3_7_row_1_3_1

set_option backward.isDefEq.respectTransparency false in
theorem right0Middle5_eq_case_3_7 : right0Middle5 3 7 = innerRightZ 5 3 7 * associatorZ 5 3 7 := by
  simpa only [HexagonAtoms537.assocABC_eq,
    HexagonAtoms537.outerABC_eq,
    HexagonAtoms537.assocBAC_eq,
    HexagonAtoms537.innerABC_eq,
    HexagonAtoms537.innerRightABC_eq,
    HexagonAtoms537.inverseACB_eq,
    HexagonAtoms537.innerACB_eq,
    HexagonAtoms537.assocBCA_eq,
    HexagonAtoms537.innerRightBAC_eq,
    HexagonAtoms537.assocCAB_eq,
    HexagonAtoms537.outerLeftABC_eq,
    HexagonRowColumn537.product0_eq,
    HexagonRowColumn537.product1_eq,
    HexagonRowColumn537.product2_eq,
    HexagonRowColumn537.product3_eq,
    HexagonRowColumn537.product4_eq,
    HexagonRowColumn537.product5_eq,
    HexagonRowColumn537.product6_eq,
    HexagonRowColumn537.product7_eq] using right0Middle5_eq_case_3_7_checked

private theorem right1Middle5_eq_case_3_7_row_0_0_0 : (right1Middle5 3 7) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn537.rows_inverseACB HexagonRowColumn537.cols_right0) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_3_7_row_0_0_1 : (right1Middle5 3 7) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn537.rows_inverseACB HexagonRowColumn537.cols_right0) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_3_7_row_0_1_0 : (right1Middle5 3 7) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn537.rows_inverseACB HexagonRowColumn537.cols_right0) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_3_7_row_0_1_1 : (right1Middle5 3 7) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn537.rows_inverseACB HexagonRowColumn537.cols_right0) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_3_7_row_0_2_0 : (right1Middle5 3 7) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn537.rows_inverseACB HexagonRowColumn537.cols_right0) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_3_7_row_0_2_1 : (right1Middle5 3 7) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn537.rows_inverseACB HexagonRowColumn537.cols_right0) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_3_7_row_0_3_0 : (right1Middle5 3 7) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn537.rows_inverseACB HexagonRowColumn537.cols_right0) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_3_7_row_0_3_1 : (right1Middle5 3 7) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn537.rows_inverseACB HexagonRowColumn537.cols_right0) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_3_7_row_1_0_0 : (right1Middle5 3 7) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn537.rows_inverseACB HexagonRowColumn537.cols_right0) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_3_7_row_1_0_1 : (right1Middle5 3 7) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn537.rows_inverseACB HexagonRowColumn537.cols_right0) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_3_7_row_1_1_0 : (right1Middle5 3 7) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn537.rows_inverseACB HexagonRowColumn537.cols_right0) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_3_7_row_1_1_1 : (right1Middle5 3 7) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn537.rows_inverseACB HexagonRowColumn537.cols_right0) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_3_7_row_1_2_0 : (right1Middle5 3 7) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn537.rows_inverseACB HexagonRowColumn537.cols_right0) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_3_7_row_1_2_1 : (right1Middle5 3 7) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn537.rows_inverseACB HexagonRowColumn537.cols_right0) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_3_7_row_1_3_0 : (right1Middle5 3 7) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn537.rows_inverseACB HexagonRowColumn537.cols_right0) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_3_7_row_1_3_1 : (right1Middle5 3 7) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn537.rows_inverseACB HexagonRowColumn537.cols_right0) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_3_7_checked : right1Middle5 3 7 = rowColumnMul HexagonRowColumn537.rows_inverseACB HexagonRowColumn537.cols_right0 := by
  funext r
  fin_cases r
  · exact right1Middle5_eq_case_3_7_row_0_0_0
  · exact right1Middle5_eq_case_3_7_row_0_0_1
  · exact right1Middle5_eq_case_3_7_row_0_1_0
  · exact right1Middle5_eq_case_3_7_row_0_1_1
  · exact right1Middle5_eq_case_3_7_row_0_2_0
  · exact right1Middle5_eq_case_3_7_row_0_2_1
  · exact right1Middle5_eq_case_3_7_row_0_3_0
  · exact right1Middle5_eq_case_3_7_row_0_3_1
  · exact right1Middle5_eq_case_3_7_row_1_0_0
  · exact right1Middle5_eq_case_3_7_row_1_0_1
  · exact right1Middle5_eq_case_3_7_row_1_1_0
  · exact right1Middle5_eq_case_3_7_row_1_1_1
  · exact right1Middle5_eq_case_3_7_row_1_2_0
  · exact right1Middle5_eq_case_3_7_row_1_2_1
  · exact right1Middle5_eq_case_3_7_row_1_3_0
  · exact right1Middle5_eq_case_3_7_row_1_3_1

set_option backward.isDefEq.respectTransparency false in
theorem right1Middle5_eq_case_3_7 : right1Middle5 3 7 = associatorInverseZ 5 7 3 * right0Middle5 3 7 := by
  simpa only [HexagonAtoms537.assocABC_eq,
    HexagonAtoms537.outerABC_eq,
    HexagonAtoms537.assocBAC_eq,
    HexagonAtoms537.innerABC_eq,
    HexagonAtoms537.innerRightABC_eq,
    HexagonAtoms537.inverseACB_eq,
    HexagonAtoms537.innerACB_eq,
    HexagonAtoms537.assocBCA_eq,
    HexagonAtoms537.innerRightBAC_eq,
    HexagonAtoms537.assocCAB_eq,
    HexagonAtoms537.outerLeftABC_eq,
    HexagonRowColumn537.product0_eq,
    HexagonRowColumn537.product1_eq,
    HexagonRowColumn537.product2_eq,
    HexagonRowColumn537.product3_eq,
    HexagonRowColumn537.product4_eq,
    HexagonRowColumn537.product5_eq,
    HexagonRowColumn537.product6_eq,
    HexagonRowColumn537.product7_eq] using right1Middle5_eq_case_3_7_checked

private theorem right2Middle5_eq_case_3_7_row_0_0_0 : (right2Middle5 3 7) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (right1Middle5 3 7) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_3_7_row_0_0_1 : (right2Middle5 3 7) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (right1Middle5 3 7) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_3_7_row_0_1_0 : (right2Middle5 3 7) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (right1Middle5 3 7) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_3_7_row_0_1_1 : (right2Middle5 3 7) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (right1Middle5 3 7) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_3_7_row_0_2_0 : (right2Middle5 3 7) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (right1Middle5 3 7) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_3_7_row_0_2_1 : (right2Middle5 3 7) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (right1Middle5 3 7) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_3_7_row_0_3_0 : (right2Middle5 3 7) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (right1Middle5 3 7) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_3_7_row_0_3_1 : (right2Middle5 3 7) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (right1Middle5 3 7) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_3_7_row_1_0_0 : (right2Middle5 3 7) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (right1Middle5 3 7) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_3_7_row_1_0_1 : (right2Middle5 3 7) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (right1Middle5 3 7) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_3_7_row_1_1_0 : (right2Middle5 3 7) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (right1Middle5 3 7) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_3_7_row_1_1_1 : (right2Middle5 3 7) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (right1Middle5 3 7) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_3_7_row_1_2_0 : (right2Middle5 3 7) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (right1Middle5 3 7) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_3_7_row_1_2_1 : (right2Middle5 3 7) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (right1Middle5 3 7) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_3_7_row_1_3_0 : (right2Middle5 3 7) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (right1Middle5 3 7) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_3_7_row_1_3_1 : (right2Middle5 3 7) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (right1Middle5 3 7) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_3_7_checked : right2Middle5 3 7 = right1Middle5 3 7 := by
  funext r
  fin_cases r
  · exact right2Middle5_eq_case_3_7_row_0_0_0
  · exact right2Middle5_eq_case_3_7_row_0_0_1
  · exact right2Middle5_eq_case_3_7_row_0_1_0
  · exact right2Middle5_eq_case_3_7_row_0_1_1
  · exact right2Middle5_eq_case_3_7_row_0_2_0
  · exact right2Middle5_eq_case_3_7_row_0_2_1
  · exact right2Middle5_eq_case_3_7_row_0_3_0
  · exact right2Middle5_eq_case_3_7_row_0_3_1
  · exact right2Middle5_eq_case_3_7_row_1_0_0
  · exact right2Middle5_eq_case_3_7_row_1_0_1
  · exact right2Middle5_eq_case_3_7_row_1_1_0
  · exact right2Middle5_eq_case_3_7_row_1_1_1
  · exact right2Middle5_eq_case_3_7_row_1_2_0
  · exact right2Middle5_eq_case_3_7_row_1_2_1
  · exact right2Middle5_eq_case_3_7_row_1_3_0
  · exact right2Middle5_eq_case_3_7_row_1_3_1

set_option backward.isDefEq.respectTransparency false in
theorem right2Middle5_eq_case_3_7 : right2Middle5 3 7 = innerLeftZ 5 7 3 * right1Middle5 3 7 := by
  simpa only [HexagonAtoms537.assocABC_eq,
    HexagonAtoms537.outerABC_eq,
    HexagonAtoms537.assocBAC_eq,
    HexagonAtoms537.innerABC_eq,
    HexagonAtoms537.innerRightABC_eq,
    HexagonAtoms537.inverseACB_eq,
    HexagonAtoms537.innerACB_eq,
    HexagonAtoms537.assocBCA_eq,
    HexagonAtoms537.innerRightBAC_eq,
    HexagonAtoms537.assocCAB_eq,
    HexagonAtoms537.outerLeftABC_eq,
    HexagonRowColumn537.product0_eq,
    HexagonRowColumn537.product1_eq,
    HexagonRowColumn537.product2_eq,
    HexagonRowColumn537.product3_eq,
    HexagonRowColumn537.product4_eq,
    HexagonRowColumn537.product5_eq,
    HexagonRowColumn537.product6_eq,
    HexagonRowColumn537.product7_eq] using right2Middle5_eq_case_3_7_checked

private theorem leftFinal5_case_3_7_row_0_0_0 : (((-1 : ℤ) ^ (leftScaleBit 5 3 7).val * positiveScale (leftScaleExponent 5 3 7)) •
      (rowColumnMul HexagonRowColumn537.rows_assocBCA HexagonRowColumn537.cols_left0)) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 5 3 7) • (left1Middle5 3 7)) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem leftFinal5_case_3_7_row_0_0_1 : (((-1 : ℤ) ^ (leftScaleBit 5 3 7).val * positiveScale (leftScaleExponent 5 3 7)) •
      (rowColumnMul HexagonRowColumn537.rows_assocBCA HexagonRowColumn537.cols_left0)) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 5 3 7) • (left1Middle5 3 7)) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem leftFinal5_case_3_7_row_0_1_0 : (((-1 : ℤ) ^ (leftScaleBit 5 3 7).val * positiveScale (leftScaleExponent 5 3 7)) •
      (rowColumnMul HexagonRowColumn537.rows_assocBCA HexagonRowColumn537.cols_left0)) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 5 3 7) • (left1Middle5 3 7)) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem leftFinal5_case_3_7_row_0_1_1 : (((-1 : ℤ) ^ (leftScaleBit 5 3 7).val * positiveScale (leftScaleExponent 5 3 7)) •
      (rowColumnMul HexagonRowColumn537.rows_assocBCA HexagonRowColumn537.cols_left0)) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 5 3 7) • (left1Middle5 3 7)) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem leftFinal5_case_3_7_row_0_2_0 : (((-1 : ℤ) ^ (leftScaleBit 5 3 7).val * positiveScale (leftScaleExponent 5 3 7)) •
      (rowColumnMul HexagonRowColumn537.rows_assocBCA HexagonRowColumn537.cols_left0)) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 5 3 7) • (left1Middle5 3 7)) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem leftFinal5_case_3_7_row_0_2_1 : (((-1 : ℤ) ^ (leftScaleBit 5 3 7).val * positiveScale (leftScaleExponent 5 3 7)) •
      (rowColumnMul HexagonRowColumn537.rows_assocBCA HexagonRowColumn537.cols_left0)) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 5 3 7) • (left1Middle5 3 7)) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem leftFinal5_case_3_7_row_0_3_0 : (((-1 : ℤ) ^ (leftScaleBit 5 3 7).val * positiveScale (leftScaleExponent 5 3 7)) •
      (rowColumnMul HexagonRowColumn537.rows_assocBCA HexagonRowColumn537.cols_left0)) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 5 3 7) • (left1Middle5 3 7)) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem leftFinal5_case_3_7_row_0_3_1 : (((-1 : ℤ) ^ (leftScaleBit 5 3 7).val * positiveScale (leftScaleExponent 5 3 7)) •
      (rowColumnMul HexagonRowColumn537.rows_assocBCA HexagonRowColumn537.cols_left0)) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 5 3 7) • (left1Middle5 3 7)) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem leftFinal5_case_3_7_row_1_0_0 : (((-1 : ℤ) ^ (leftScaleBit 5 3 7).val * positiveScale (leftScaleExponent 5 3 7)) •
      (rowColumnMul HexagonRowColumn537.rows_assocBCA HexagonRowColumn537.cols_left0)) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 5 3 7) • (left1Middle5 3 7)) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem leftFinal5_case_3_7_row_1_0_1 : (((-1 : ℤ) ^ (leftScaleBit 5 3 7).val * positiveScale (leftScaleExponent 5 3 7)) •
      (rowColumnMul HexagonRowColumn537.rows_assocBCA HexagonRowColumn537.cols_left0)) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 5 3 7) • (left1Middle5 3 7)) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem leftFinal5_case_3_7_row_1_1_0 : (((-1 : ℤ) ^ (leftScaleBit 5 3 7).val * positiveScale (leftScaleExponent 5 3 7)) •
      (rowColumnMul HexagonRowColumn537.rows_assocBCA HexagonRowColumn537.cols_left0)) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 5 3 7) • (left1Middle5 3 7)) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem leftFinal5_case_3_7_row_1_1_1 : (((-1 : ℤ) ^ (leftScaleBit 5 3 7).val * positiveScale (leftScaleExponent 5 3 7)) •
      (rowColumnMul HexagonRowColumn537.rows_assocBCA HexagonRowColumn537.cols_left0)) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 5 3 7) • (left1Middle5 3 7)) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem leftFinal5_case_3_7_row_1_2_0 : (((-1 : ℤ) ^ (leftScaleBit 5 3 7).val * positiveScale (leftScaleExponent 5 3 7)) •
      (rowColumnMul HexagonRowColumn537.rows_assocBCA HexagonRowColumn537.cols_left0)) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 5 3 7) • (left1Middle5 3 7)) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem leftFinal5_case_3_7_row_1_2_1 : (((-1 : ℤ) ^ (leftScaleBit 5 3 7).val * positiveScale (leftScaleExponent 5 3 7)) •
      (rowColumnMul HexagonRowColumn537.rows_assocBCA HexagonRowColumn537.cols_left0)) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 5 3 7) • (left1Middle5 3 7)) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem leftFinal5_case_3_7_row_1_3_0 : (((-1 : ℤ) ^ (leftScaleBit 5 3 7).val * positiveScale (leftScaleExponent 5 3 7)) •
      (rowColumnMul HexagonRowColumn537.rows_assocBCA HexagonRowColumn537.cols_left0)) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 5 3 7) • (left1Middle5 3 7)) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem leftFinal5_case_3_7_row_1_3_1 : (((-1 : ℤ) ^ (leftScaleBit 5 3 7).val * positiveScale (leftScaleExponent 5 3 7)) •
      (rowColumnMul HexagonRowColumn537.rows_assocBCA HexagonRowColumn537.cols_left0)) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 5 3 7) • (left1Middle5 3 7)) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem leftFinal5_case_3_7_checked : ((-1 : ℤ) ^ (leftScaleBit 5 3 7).val * positiveScale (leftScaleExponent 5 3 7)) •
      (rowColumnMul HexagonRowColumn537.rows_assocBCA HexagonRowColumn537.cols_left0) = negativeScale (leftScaleExponent 5 3 7) • (left1Middle5 3 7) := by
  funext r
  fin_cases r
  · exact leftFinal5_case_3_7_row_0_0_0
  · exact leftFinal5_case_3_7_row_0_0_1
  · exact leftFinal5_case_3_7_row_0_1_0
  · exact leftFinal5_case_3_7_row_0_1_1
  · exact leftFinal5_case_3_7_row_0_2_0
  · exact leftFinal5_case_3_7_row_0_2_1
  · exact leftFinal5_case_3_7_row_0_3_0
  · exact leftFinal5_case_3_7_row_0_3_1
  · exact leftFinal5_case_3_7_row_1_0_0
  · exact leftFinal5_case_3_7_row_1_0_1
  · exact leftFinal5_case_3_7_row_1_1_0
  · exact leftFinal5_case_3_7_row_1_1_1
  · exact leftFinal5_case_3_7_row_1_2_0
  · exact leftFinal5_case_3_7_row_1_2_1
  · exact leftFinal5_case_3_7_row_1_3_0
  · exact leftFinal5_case_3_7_row_1_3_1

set_option backward.isDefEq.respectTransparency false in
theorem leftFinal5_case_3_7 : ((-1 : ℤ) ^ (leftScaleBit 5 3 7).val * positiveScale (leftScaleExponent 5 3 7)) •
      (associatorZ 3 7 5 * left0Middle5 3 7) = negativeScale (leftScaleExponent 5 3 7) • (innerRightZ 3 5 7 * left1Middle5 3 7) := by
  simpa only [HexagonAtoms537.assocABC_eq,
    HexagonAtoms537.outerABC_eq,
    HexagonAtoms537.assocBAC_eq,
    HexagonAtoms537.innerABC_eq,
    HexagonAtoms537.innerRightABC_eq,
    HexagonAtoms537.inverseACB_eq,
    HexagonAtoms537.innerACB_eq,
    HexagonAtoms537.assocBCA_eq,
    HexagonAtoms537.innerRightBAC_eq,
    HexagonAtoms537.assocCAB_eq,
    HexagonAtoms537.outerLeftABC_eq,
    HexagonRowColumn537.product0_eq,
    HexagonRowColumn537.product1_eq,
    HexagonRowColumn537.product2_eq,
    HexagonRowColumn537.product3_eq,
    HexagonRowColumn537.product4_eq,
    HexagonRowColumn537.product5_eq,
    HexagonRowColumn537.product6_eq,
    HexagonRowColumn537.product7_eq] using leftFinal5_case_3_7_checked

private theorem rightFinal5_case_3_7_row_0_0_0 : (((-1 : ℤ) ^ (rightScaleBit 5 3 7).val * positiveScale (rightScaleExponent 5 3 7) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 7 3 : ℤ)) • HexagonAtoms537.outerLeftABC) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 2)) = (negativeScale (rightScaleExponent 5 3 7) • (rowColumnMul HexagonRowColumn537.rows_assocCAB HexagonRowColumn537.cols_right2)) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem rightFinal5_case_3_7_row_0_0_1 : (((-1 : ℤ) ^ (rightScaleBit 5 3 7).val * positiveScale (rightScaleExponent 5 3 7) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 7 3 : ℤ)) • HexagonAtoms537.outerLeftABC) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 2)) = (negativeScale (rightScaleExponent 5 3 7) • (rowColumnMul HexagonRowColumn537.rows_assocCAB HexagonRowColumn537.cols_right2)) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem rightFinal5_case_3_7_row_1_0_0 : (((-1 : ℤ) ^ (rightScaleBit 5 3 7).val * positiveScale (rightScaleExponent 5 3 7) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 7 3 : ℤ)) • HexagonAtoms537.outerLeftABC) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 2)) = (negativeScale (rightScaleExponent 5 3 7) • (rowColumnMul HexagonRowColumn537.rows_assocCAB HexagonRowColumn537.cols_right2)) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem rightFinal5_case_3_7_row_1_0_1 : (((-1 : ℤ) ^ (rightScaleBit 5 3 7).val * positiveScale (rightScaleExponent 5 3 7) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 7 3 : ℤ)) • HexagonAtoms537.outerLeftABC) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 2)) = (negativeScale (rightScaleExponent 5 3 7) • (rowColumnMul HexagonRowColumn537.rows_assocCAB HexagonRowColumn537.cols_right2)) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem rightFinal5_case_3_7_row_2_0_0 : (((-1 : ℤ) ^ (rightScaleBit 5 3 7).val * positiveScale (rightScaleExponent 5 3 7) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 7 3 : ℤ)) • HexagonAtoms537.outerLeftABC) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 2)) = (negativeScale (rightScaleExponent 5 3 7) • (rowColumnMul HexagonRowColumn537.rows_assocCAB HexagonRowColumn537.cols_right2)) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem rightFinal5_case_3_7_row_2_0_1 : (((-1 : ℤ) ^ (rightScaleBit 5 3 7).val * positiveScale (rightScaleExponent 5 3 7) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 7 3 : ℤ)) • HexagonAtoms537.outerLeftABC) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 2)) = (negativeScale (rightScaleExponent 5 3 7) • (rowColumnMul HexagonRowColumn537.rows_assocCAB HexagonRowColumn537.cols_right2)) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem rightFinal5_case_3_7_row_3_0_0 : (((-1 : ℤ) ^ (rightScaleBit 5 3 7).val * positiveScale (rightScaleExponent 5 3 7) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 7 3 : ℤ)) • HexagonAtoms537.outerLeftABC) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 2)) = (negativeScale (rightScaleExponent 5 3 7) • (rowColumnMul HexagonRowColumn537.rows_assocCAB HexagonRowColumn537.cols_right2)) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem rightFinal5_case_3_7_row_3_0_1 : (((-1 : ℤ) ^ (rightScaleBit 5 3 7).val * positiveScale (rightScaleExponent 5 3 7) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 7 3 : ℤ)) • HexagonAtoms537.outerLeftABC) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 2)) = (negativeScale (rightScaleExponent 5 3 7) • (rowColumnMul HexagonRowColumn537.rows_assocCAB HexagonRowColumn537.cols_right2)) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem rightFinal5_case_3_7_row_4_0_0 : (((-1 : ℤ) ^ (rightScaleBit 5 3 7).val * positiveScale (rightScaleExponent 5 3 7) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 7 3 : ℤ)) • HexagonAtoms537.outerLeftABC) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 2)) = (negativeScale (rightScaleExponent 5 3 7) • (rowColumnMul HexagonRowColumn537.rows_assocCAB HexagonRowColumn537.cols_right2)) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem rightFinal5_case_3_7_row_4_0_1 : (((-1 : ℤ) ^ (rightScaleBit 5 3 7).val * positiveScale (rightScaleExponent 5 3 7) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 7 3 : ℤ)) • HexagonAtoms537.outerLeftABC) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 2)) = (negativeScale (rightScaleExponent 5 3 7) • (rowColumnMul HexagonRowColumn537.rows_assocCAB HexagonRowColumn537.cols_right2)) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem rightFinal5_case_3_7_row_5_0_0 : (((-1 : ℤ) ^ (rightScaleBit 5 3 7).val * positiveScale (rightScaleExponent 5 3 7) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 7 3 : ℤ)) • HexagonAtoms537.outerLeftABC) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 2)) = (negativeScale (rightScaleExponent 5 3 7) • (rowColumnMul HexagonRowColumn537.rows_assocCAB HexagonRowColumn537.cols_right2)) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem rightFinal5_case_3_7_row_5_0_1 : (((-1 : ℤ) ^ (rightScaleBit 5 3 7).val * positiveScale (rightScaleExponent 5 3 7) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 7 3 : ℤ)) • HexagonAtoms537.outerLeftABC) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 2)) = (negativeScale (rightScaleExponent 5 3 7) • (rowColumnMul HexagonRowColumn537.rows_assocCAB HexagonRowColumn537.cols_right2)) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem rightFinal5_case_3_7_row_6_0_0 : (((-1 : ℤ) ^ (rightScaleBit 5 3 7).val * positiveScale (rightScaleExponent 5 3 7) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 7 3 : ℤ)) • HexagonAtoms537.outerLeftABC) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 2)) = (negativeScale (rightScaleExponent 5 3 7) • (rowColumnMul HexagonRowColumn537.rows_assocCAB HexagonRowColumn537.cols_right2)) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem rightFinal5_case_3_7_row_6_0_1 : (((-1 : ℤ) ^ (rightScaleBit 5 3 7).val * positiveScale (rightScaleExponent 5 3 7) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 7 3 : ℤ)) • HexagonAtoms537.outerLeftABC) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 2)) = (negativeScale (rightScaleExponent 5 3 7) • (rowColumnMul HexagonRowColumn537.rows_assocCAB HexagonRowColumn537.cols_right2)) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem rightFinal5_case_3_7_row_7_0_0 : (((-1 : ℤ) ^ (rightScaleBit 5 3 7).val * positiveScale (rightScaleExponent 5 3 7) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 7 3 : ℤ)) • HexagonAtoms537.outerLeftABC) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 2)) = (negativeScale (rightScaleExponent 5 3 7) • (rowColumnMul HexagonRowColumn537.rows_assocCAB HexagonRowColumn537.cols_right2)) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem rightFinal5_case_3_7_row_7_0_1 : (((-1 : ℤ) ^ (rightScaleBit 5 3 7).val * positiveScale (rightScaleExponent 5 3 7) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 7 3 : ℤ)) • HexagonAtoms537.outerLeftABC) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 2)) = (negativeScale (rightScaleExponent 5 3 7) • (rowColumnMul HexagonRowColumn537.rows_assocCAB HexagonRowColumn537.cols_right2)) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem rightFinal5_case_3_7_checked : ((-1 : ℤ) ^ (rightScaleBit 5 3 7).val * positiveScale (rightScaleExponent 5 3 7) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 7 3 : ℤ)) • HexagonAtoms537.outerLeftABC = negativeScale (rightScaleExponent 5 3 7) • (rowColumnMul HexagonRowColumn537.rows_assocCAB HexagonRowColumn537.cols_right2) := by
  funext r
  fin_cases r
  · exact rightFinal5_case_3_7_row_0_0_0
  · exact rightFinal5_case_3_7_row_0_0_1
  · exact rightFinal5_case_3_7_row_1_0_0
  · exact rightFinal5_case_3_7_row_1_0_1
  · exact rightFinal5_case_3_7_row_2_0_0
  · exact rightFinal5_case_3_7_row_2_0_1
  · exact rightFinal5_case_3_7_row_3_0_0
  · exact rightFinal5_case_3_7_row_3_0_1
  · exact rightFinal5_case_3_7_row_4_0_0
  · exact rightFinal5_case_3_7_row_4_0_1
  · exact rightFinal5_case_3_7_row_5_0_0
  · exact rightFinal5_case_3_7_row_5_0_1
  · exact rightFinal5_case_3_7_row_6_0_0
  · exact rightFinal5_case_3_7_row_6_0_1
  · exact rightFinal5_case_3_7_row_7_0_0
  · exact rightFinal5_case_3_7_row_7_0_1

set_option backward.isDefEq.respectTransparency false in
theorem rightFinal5_case_3_7 : ((-1 : ℤ) ^ (rightScaleBit 5 3 7).val * positiveScale (rightScaleExponent 5 3 7) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 7 3 : ℤ)) • outerLeftZ 5 3 7 = negativeScale (rightScaleExponent 5 3 7) • (associatorZ 7 5 3 * right2Middle5 3 7) := by
  simpa only [HexagonAtoms537.assocABC_eq,
    HexagonAtoms537.outerABC_eq,
    HexagonAtoms537.assocBAC_eq,
    HexagonAtoms537.innerABC_eq,
    HexagonAtoms537.innerRightABC_eq,
    HexagonAtoms537.inverseACB_eq,
    HexagonAtoms537.innerACB_eq,
    HexagonAtoms537.assocBCA_eq,
    HexagonAtoms537.innerRightBAC_eq,
    HexagonAtoms537.assocCAB_eq,
    HexagonAtoms537.outerLeftABC_eq,
    HexagonRowColumn537.product0_eq,
    HexagonRowColumn537.product1_eq,
    HexagonRowColumn537.product2_eq,
    HexagonRowColumn537.product3_eq,
    HexagonRowColumn537.product4_eq,
    HexagonRowColumn537.product5_eq,
    HexagonRowColumn537.product6_eq,
    HexagonRowColumn537.product7_eq] using rightFinal5_case_3_7_checked

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonCases5
