import RMod.BrundanEllis.StackingReferenceHexagonMiddle5
import RMod.BrundanEllis.StackingReferenceSparseMatrixCheck
import RMod.BrundanEllis.StackingReferenceHexagonAtoms546
import RMod.BrundanEllis.StackingReferenceHexagonRowColumn546

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

private theorem left0Middle5_eq_case_4_6_row_0_0_0 : (left0Middle5 4 6) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (HexagonAtoms546.assocABC) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_4_6_row_0_0_1 : (left0Middle5 4 6) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (HexagonAtoms546.assocABC) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_4_6_row_0_1_0 : (left0Middle5 4 6) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (HexagonAtoms546.assocABC) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_4_6_row_0_1_1 : (left0Middle5 4 6) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (HexagonAtoms546.assocABC) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_4_6_row_0_2_0 : (left0Middle5 4 6) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (HexagonAtoms546.assocABC) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_4_6_row_0_2_1 : (left0Middle5 4 6) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (HexagonAtoms546.assocABC) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_4_6_row_0_3_0 : (left0Middle5 4 6) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (HexagonAtoms546.assocABC) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_4_6_row_0_3_1 : (left0Middle5 4 6) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (HexagonAtoms546.assocABC) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_4_6_row_1_0_0 : (left0Middle5 4 6) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (HexagonAtoms546.assocABC) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_4_6_row_1_0_1 : (left0Middle5 4 6) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (HexagonAtoms546.assocABC) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_4_6_row_1_1_0 : (left0Middle5 4 6) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (HexagonAtoms546.assocABC) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_4_6_row_1_1_1 : (left0Middle5 4 6) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (HexagonAtoms546.assocABC) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_4_6_row_1_2_0 : (left0Middle5 4 6) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (HexagonAtoms546.assocABC) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_4_6_row_1_2_1 : (left0Middle5 4 6) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (HexagonAtoms546.assocABC) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_4_6_row_1_3_0 : (left0Middle5 4 6) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (HexagonAtoms546.assocABC) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_4_6_row_1_3_1 : (left0Middle5 4 6) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (HexagonAtoms546.assocABC) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_4_6_checked : left0Middle5 4 6 = HexagonAtoms546.assocABC := by
  funext r
  fin_cases r
  · exact left0Middle5_eq_case_4_6_row_0_0_0
  · exact left0Middle5_eq_case_4_6_row_0_0_1
  · exact left0Middle5_eq_case_4_6_row_0_1_0
  · exact left0Middle5_eq_case_4_6_row_0_1_1
  · exact left0Middle5_eq_case_4_6_row_0_2_0
  · exact left0Middle5_eq_case_4_6_row_0_2_1
  · exact left0Middle5_eq_case_4_6_row_0_3_0
  · exact left0Middle5_eq_case_4_6_row_0_3_1
  · exact left0Middle5_eq_case_4_6_row_1_0_0
  · exact left0Middle5_eq_case_4_6_row_1_0_1
  · exact left0Middle5_eq_case_4_6_row_1_1_0
  · exact left0Middle5_eq_case_4_6_row_1_1_1
  · exact left0Middle5_eq_case_4_6_row_1_2_0
  · exact left0Middle5_eq_case_4_6_row_1_2_1
  · exact left0Middle5_eq_case_4_6_row_1_3_0
  · exact left0Middle5_eq_case_4_6_row_1_3_1

set_option backward.isDefEq.respectTransparency false in
theorem left0Middle5_eq_case_4_6 : left0Middle5 4 6 = outerRightZ 5 4 6 * associatorZ 5 4 6 := by
  simpa only [HexagonAtoms546.assocABC_eq,
    HexagonAtoms546.outerABC_eq,
    HexagonAtoms546.assocBAC_eq,
    HexagonAtoms546.innerABC_eq,
    HexagonAtoms546.innerRightABC_eq,
    HexagonAtoms546.inverseACB_eq,
    HexagonAtoms546.innerACB_eq,
    HexagonAtoms546.assocBCA_eq,
    HexagonAtoms546.innerRightBAC_eq,
    HexagonAtoms546.assocCAB_eq,
    HexagonAtoms546.outerLeftABC_eq,
    HexagonRowColumn546.product0_eq,
    HexagonRowColumn546.product1_eq,
    HexagonRowColumn546.product2_eq,
    HexagonRowColumn546.product3_eq,
    HexagonRowColumn546.product4_eq,
    HexagonRowColumn546.product5_eq,
    HexagonRowColumn546.product6_eq,
    HexagonRowColumn546.product7_eq] using left0Middle5_eq_case_4_6_checked

private theorem left1Middle5_eq_case_4_6_row_0_0_0 : (left1Middle5 4 6) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (HexagonAtoms546.assocBAC) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_4_6_row_0_0_1 : (left1Middle5 4 6) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (HexagonAtoms546.assocBAC) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_4_6_row_0_1_0 : (left1Middle5 4 6) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (HexagonAtoms546.assocBAC) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_4_6_row_0_1_1 : (left1Middle5 4 6) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (HexagonAtoms546.assocBAC) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_4_6_row_0_2_0 : (left1Middle5 4 6) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (HexagonAtoms546.assocBAC) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_4_6_row_0_2_1 : (left1Middle5 4 6) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (HexagonAtoms546.assocBAC) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_4_6_row_0_3_0 : (left1Middle5 4 6) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (HexagonAtoms546.assocBAC) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_4_6_row_0_3_1 : (left1Middle5 4 6) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (HexagonAtoms546.assocBAC) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_4_6_row_1_0_0 : (left1Middle5 4 6) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (HexagonAtoms546.assocBAC) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_4_6_row_1_0_1 : (left1Middle5 4 6) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (HexagonAtoms546.assocBAC) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_4_6_row_1_1_0 : (left1Middle5 4 6) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (HexagonAtoms546.assocBAC) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_4_6_row_1_1_1 : (left1Middle5 4 6) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (HexagonAtoms546.assocBAC) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_4_6_row_1_2_0 : (left1Middle5 4 6) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (HexagonAtoms546.assocBAC) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_4_6_row_1_2_1 : (left1Middle5 4 6) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (HexagonAtoms546.assocBAC) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_4_6_row_1_3_0 : (left1Middle5 4 6) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (HexagonAtoms546.assocBAC) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_4_6_row_1_3_1 : (left1Middle5 4 6) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (HexagonAtoms546.assocBAC) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_4_6_checked : left1Middle5 4 6 = HexagonAtoms546.assocBAC := by
  funext r
  fin_cases r
  · exact left1Middle5_eq_case_4_6_row_0_0_0
  · exact left1Middle5_eq_case_4_6_row_0_0_1
  · exact left1Middle5_eq_case_4_6_row_0_1_0
  · exact left1Middle5_eq_case_4_6_row_0_1_1
  · exact left1Middle5_eq_case_4_6_row_0_2_0
  · exact left1Middle5_eq_case_4_6_row_0_2_1
  · exact left1Middle5_eq_case_4_6_row_0_3_0
  · exact left1Middle5_eq_case_4_6_row_0_3_1
  · exact left1Middle5_eq_case_4_6_row_1_0_0
  · exact left1Middle5_eq_case_4_6_row_1_0_1
  · exact left1Middle5_eq_case_4_6_row_1_1_0
  · exact left1Middle5_eq_case_4_6_row_1_1_1
  · exact left1Middle5_eq_case_4_6_row_1_2_0
  · exact left1Middle5_eq_case_4_6_row_1_2_1
  · exact left1Middle5_eq_case_4_6_row_1_3_0
  · exact left1Middle5_eq_case_4_6_row_1_3_1

set_option backward.isDefEq.respectTransparency false in
theorem left1Middle5_eq_case_4_6 : left1Middle5 4 6 = associatorZ 4 5 6 * innerLeftZ 5 4 6 := by
  simpa only [HexagonAtoms546.assocABC_eq,
    HexagonAtoms546.outerABC_eq,
    HexagonAtoms546.assocBAC_eq,
    HexagonAtoms546.innerABC_eq,
    HexagonAtoms546.innerRightABC_eq,
    HexagonAtoms546.inverseACB_eq,
    HexagonAtoms546.innerACB_eq,
    HexagonAtoms546.assocBCA_eq,
    HexagonAtoms546.innerRightBAC_eq,
    HexagonAtoms546.assocCAB_eq,
    HexagonAtoms546.outerLeftABC_eq,
    HexagonRowColumn546.product0_eq,
    HexagonRowColumn546.product1_eq,
    HexagonRowColumn546.product2_eq,
    HexagonRowColumn546.product3_eq,
    HexagonRowColumn546.product4_eq,
    HexagonRowColumn546.product5_eq,
    HexagonRowColumn546.product6_eq,
    HexagonRowColumn546.product7_eq] using left1Middle5_eq_case_4_6_checked

private theorem right0Middle5_eq_case_4_6_row_0_0_0 : (right0Middle5 4 6) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (HexagonAtoms546.assocABC) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_4_6_row_0_0_1 : (right0Middle5 4 6) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (HexagonAtoms546.assocABC) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_4_6_row_0_1_0 : (right0Middle5 4 6) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (HexagonAtoms546.assocABC) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_4_6_row_0_1_1 : (right0Middle5 4 6) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (HexagonAtoms546.assocABC) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_4_6_row_0_2_0 : (right0Middle5 4 6) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (HexagonAtoms546.assocABC) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_4_6_row_0_2_1 : (right0Middle5 4 6) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (HexagonAtoms546.assocABC) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_4_6_row_0_3_0 : (right0Middle5 4 6) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (HexagonAtoms546.assocABC) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_4_6_row_0_3_1 : (right0Middle5 4 6) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (HexagonAtoms546.assocABC) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_4_6_row_1_0_0 : (right0Middle5 4 6) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (HexagonAtoms546.assocABC) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_4_6_row_1_0_1 : (right0Middle5 4 6) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (HexagonAtoms546.assocABC) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_4_6_row_1_1_0 : (right0Middle5 4 6) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (HexagonAtoms546.assocABC) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_4_6_row_1_1_1 : (right0Middle5 4 6) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (HexagonAtoms546.assocABC) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_4_6_row_1_2_0 : (right0Middle5 4 6) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (HexagonAtoms546.assocABC) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_4_6_row_1_2_1 : (right0Middle5 4 6) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (HexagonAtoms546.assocABC) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_4_6_row_1_3_0 : (right0Middle5 4 6) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (HexagonAtoms546.assocABC) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_4_6_row_1_3_1 : (right0Middle5 4 6) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (HexagonAtoms546.assocABC) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_4_6_checked : right0Middle5 4 6 = HexagonAtoms546.assocABC := by
  funext r
  fin_cases r
  · exact right0Middle5_eq_case_4_6_row_0_0_0
  · exact right0Middle5_eq_case_4_6_row_0_0_1
  · exact right0Middle5_eq_case_4_6_row_0_1_0
  · exact right0Middle5_eq_case_4_6_row_0_1_1
  · exact right0Middle5_eq_case_4_6_row_0_2_0
  · exact right0Middle5_eq_case_4_6_row_0_2_1
  · exact right0Middle5_eq_case_4_6_row_0_3_0
  · exact right0Middle5_eq_case_4_6_row_0_3_1
  · exact right0Middle5_eq_case_4_6_row_1_0_0
  · exact right0Middle5_eq_case_4_6_row_1_0_1
  · exact right0Middle5_eq_case_4_6_row_1_1_0
  · exact right0Middle5_eq_case_4_6_row_1_1_1
  · exact right0Middle5_eq_case_4_6_row_1_2_0
  · exact right0Middle5_eq_case_4_6_row_1_2_1
  · exact right0Middle5_eq_case_4_6_row_1_3_0
  · exact right0Middle5_eq_case_4_6_row_1_3_1

set_option backward.isDefEq.respectTransparency false in
theorem right0Middle5_eq_case_4_6 : right0Middle5 4 6 = innerRightZ 5 4 6 * associatorZ 5 4 6 := by
  simpa only [HexagonAtoms546.assocABC_eq,
    HexagonAtoms546.outerABC_eq,
    HexagonAtoms546.assocBAC_eq,
    HexagonAtoms546.innerABC_eq,
    HexagonAtoms546.innerRightABC_eq,
    HexagonAtoms546.inverseACB_eq,
    HexagonAtoms546.innerACB_eq,
    HexagonAtoms546.assocBCA_eq,
    HexagonAtoms546.innerRightBAC_eq,
    HexagonAtoms546.assocCAB_eq,
    HexagonAtoms546.outerLeftABC_eq,
    HexagonRowColumn546.product0_eq,
    HexagonRowColumn546.product1_eq,
    HexagonRowColumn546.product2_eq,
    HexagonRowColumn546.product3_eq,
    HexagonRowColumn546.product4_eq,
    HexagonRowColumn546.product5_eq,
    HexagonRowColumn546.product6_eq,
    HexagonRowColumn546.product7_eq] using right0Middle5_eq_case_4_6_checked

private theorem right1Middle5_eq_case_4_6_row_0_0_0 : (right1Middle5 4 6) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn546.rows_inverseACB HexagonRowColumn546.cols_right0) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_4_6_row_0_0_1 : (right1Middle5 4 6) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn546.rows_inverseACB HexagonRowColumn546.cols_right0) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_4_6_row_0_1_0 : (right1Middle5 4 6) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn546.rows_inverseACB HexagonRowColumn546.cols_right0) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_4_6_row_0_1_1 : (right1Middle5 4 6) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn546.rows_inverseACB HexagonRowColumn546.cols_right0) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_4_6_row_0_2_0 : (right1Middle5 4 6) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn546.rows_inverseACB HexagonRowColumn546.cols_right0) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_4_6_row_0_2_1 : (right1Middle5 4 6) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn546.rows_inverseACB HexagonRowColumn546.cols_right0) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_4_6_row_0_3_0 : (right1Middle5 4 6) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn546.rows_inverseACB HexagonRowColumn546.cols_right0) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_4_6_row_0_3_1 : (right1Middle5 4 6) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn546.rows_inverseACB HexagonRowColumn546.cols_right0) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_4_6_row_1_0_0 : (right1Middle5 4 6) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn546.rows_inverseACB HexagonRowColumn546.cols_right0) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_4_6_row_1_0_1 : (right1Middle5 4 6) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn546.rows_inverseACB HexagonRowColumn546.cols_right0) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_4_6_row_1_1_0 : (right1Middle5 4 6) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn546.rows_inverseACB HexagonRowColumn546.cols_right0) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_4_6_row_1_1_1 : (right1Middle5 4 6) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn546.rows_inverseACB HexagonRowColumn546.cols_right0) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_4_6_row_1_2_0 : (right1Middle5 4 6) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn546.rows_inverseACB HexagonRowColumn546.cols_right0) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_4_6_row_1_2_1 : (right1Middle5 4 6) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn546.rows_inverseACB HexagonRowColumn546.cols_right0) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_4_6_row_1_3_0 : (right1Middle5 4 6) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn546.rows_inverseACB HexagonRowColumn546.cols_right0) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_4_6_row_1_3_1 : (right1Middle5 4 6) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn546.rows_inverseACB HexagonRowColumn546.cols_right0) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_4_6_checked : right1Middle5 4 6 = rowColumnMul HexagonRowColumn546.rows_inverseACB HexagonRowColumn546.cols_right0 := by
  funext r
  fin_cases r
  · exact right1Middle5_eq_case_4_6_row_0_0_0
  · exact right1Middle5_eq_case_4_6_row_0_0_1
  · exact right1Middle5_eq_case_4_6_row_0_1_0
  · exact right1Middle5_eq_case_4_6_row_0_1_1
  · exact right1Middle5_eq_case_4_6_row_0_2_0
  · exact right1Middle5_eq_case_4_6_row_0_2_1
  · exact right1Middle5_eq_case_4_6_row_0_3_0
  · exact right1Middle5_eq_case_4_6_row_0_3_1
  · exact right1Middle5_eq_case_4_6_row_1_0_0
  · exact right1Middle5_eq_case_4_6_row_1_0_1
  · exact right1Middle5_eq_case_4_6_row_1_1_0
  · exact right1Middle5_eq_case_4_6_row_1_1_1
  · exact right1Middle5_eq_case_4_6_row_1_2_0
  · exact right1Middle5_eq_case_4_6_row_1_2_1
  · exact right1Middle5_eq_case_4_6_row_1_3_0
  · exact right1Middle5_eq_case_4_6_row_1_3_1

set_option backward.isDefEq.respectTransparency false in
theorem right1Middle5_eq_case_4_6 : right1Middle5 4 6 = associatorInverseZ 5 6 4 * right0Middle5 4 6 := by
  simpa only [HexagonAtoms546.assocABC_eq,
    HexagonAtoms546.outerABC_eq,
    HexagonAtoms546.assocBAC_eq,
    HexagonAtoms546.innerABC_eq,
    HexagonAtoms546.innerRightABC_eq,
    HexagonAtoms546.inverseACB_eq,
    HexagonAtoms546.innerACB_eq,
    HexagonAtoms546.assocBCA_eq,
    HexagonAtoms546.innerRightBAC_eq,
    HexagonAtoms546.assocCAB_eq,
    HexagonAtoms546.outerLeftABC_eq,
    HexagonRowColumn546.product0_eq,
    HexagonRowColumn546.product1_eq,
    HexagonRowColumn546.product2_eq,
    HexagonRowColumn546.product3_eq,
    HexagonRowColumn546.product4_eq,
    HexagonRowColumn546.product5_eq,
    HexagonRowColumn546.product6_eq,
    HexagonRowColumn546.product7_eq] using right1Middle5_eq_case_4_6_checked

private theorem right2Middle5_eq_case_4_6_row_0_0_0 : (right2Middle5 4 6) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (right1Middle5 4 6) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_4_6_row_0_0_1 : (right2Middle5 4 6) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (right1Middle5 4 6) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_4_6_row_0_1_0 : (right2Middle5 4 6) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (right1Middle5 4 6) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_4_6_row_0_1_1 : (right2Middle5 4 6) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (right1Middle5 4 6) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_4_6_row_0_2_0 : (right2Middle5 4 6) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (right1Middle5 4 6) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_4_6_row_0_2_1 : (right2Middle5 4 6) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (right1Middle5 4 6) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_4_6_row_0_3_0 : (right2Middle5 4 6) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (right1Middle5 4 6) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_4_6_row_0_3_1 : (right2Middle5 4 6) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (right1Middle5 4 6) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_4_6_row_1_0_0 : (right2Middle5 4 6) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (right1Middle5 4 6) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_4_6_row_1_0_1 : (right2Middle5 4 6) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (right1Middle5 4 6) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_4_6_row_1_1_0 : (right2Middle5 4 6) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (right1Middle5 4 6) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_4_6_row_1_1_1 : (right2Middle5 4 6) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (right1Middle5 4 6) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_4_6_row_1_2_0 : (right2Middle5 4 6) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (right1Middle5 4 6) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_4_6_row_1_2_1 : (right2Middle5 4 6) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (right1Middle5 4 6) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_4_6_row_1_3_0 : (right2Middle5 4 6) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (right1Middle5 4 6) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_4_6_row_1_3_1 : (right2Middle5 4 6) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (right1Middle5 4 6) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_4_6_checked : right2Middle5 4 6 = right1Middle5 4 6 := by
  funext r
  fin_cases r
  · exact right2Middle5_eq_case_4_6_row_0_0_0
  · exact right2Middle5_eq_case_4_6_row_0_0_1
  · exact right2Middle5_eq_case_4_6_row_0_1_0
  · exact right2Middle5_eq_case_4_6_row_0_1_1
  · exact right2Middle5_eq_case_4_6_row_0_2_0
  · exact right2Middle5_eq_case_4_6_row_0_2_1
  · exact right2Middle5_eq_case_4_6_row_0_3_0
  · exact right2Middle5_eq_case_4_6_row_0_3_1
  · exact right2Middle5_eq_case_4_6_row_1_0_0
  · exact right2Middle5_eq_case_4_6_row_1_0_1
  · exact right2Middle5_eq_case_4_6_row_1_1_0
  · exact right2Middle5_eq_case_4_6_row_1_1_1
  · exact right2Middle5_eq_case_4_6_row_1_2_0
  · exact right2Middle5_eq_case_4_6_row_1_2_1
  · exact right2Middle5_eq_case_4_6_row_1_3_0
  · exact right2Middle5_eq_case_4_6_row_1_3_1

set_option backward.isDefEq.respectTransparency false in
theorem right2Middle5_eq_case_4_6 : right2Middle5 4 6 = innerLeftZ 5 6 4 * right1Middle5 4 6 := by
  simpa only [HexagonAtoms546.assocABC_eq,
    HexagonAtoms546.outerABC_eq,
    HexagonAtoms546.assocBAC_eq,
    HexagonAtoms546.innerABC_eq,
    HexagonAtoms546.innerRightABC_eq,
    HexagonAtoms546.inverseACB_eq,
    HexagonAtoms546.innerACB_eq,
    HexagonAtoms546.assocBCA_eq,
    HexagonAtoms546.innerRightBAC_eq,
    HexagonAtoms546.assocCAB_eq,
    HexagonAtoms546.outerLeftABC_eq,
    HexagonRowColumn546.product0_eq,
    HexagonRowColumn546.product1_eq,
    HexagonRowColumn546.product2_eq,
    HexagonRowColumn546.product3_eq,
    HexagonRowColumn546.product4_eq,
    HexagonRowColumn546.product5_eq,
    HexagonRowColumn546.product6_eq,
    HexagonRowColumn546.product7_eq] using right2Middle5_eq_case_4_6_checked

private theorem leftFinal5_case_4_6_row_0_0_0 : (((-1 : ℤ) ^ (leftScaleBit 5 4 6).val * positiveScale (leftScaleExponent 5 4 6)) •
      (rowColumnMul HexagonRowColumn546.rows_assocBCA HexagonRowColumn546.cols_left0)) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 5 4 6) • (left1Middle5 4 6)) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem leftFinal5_case_4_6_row_0_0_1 : (((-1 : ℤ) ^ (leftScaleBit 5 4 6).val * positiveScale (leftScaleExponent 5 4 6)) •
      (rowColumnMul HexagonRowColumn546.rows_assocBCA HexagonRowColumn546.cols_left0)) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 5 4 6) • (left1Middle5 4 6)) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem leftFinal5_case_4_6_row_0_1_0 : (((-1 : ℤ) ^ (leftScaleBit 5 4 6).val * positiveScale (leftScaleExponent 5 4 6)) •
      (rowColumnMul HexagonRowColumn546.rows_assocBCA HexagonRowColumn546.cols_left0)) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 5 4 6) • (left1Middle5 4 6)) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem leftFinal5_case_4_6_row_0_1_1 : (((-1 : ℤ) ^ (leftScaleBit 5 4 6).val * positiveScale (leftScaleExponent 5 4 6)) •
      (rowColumnMul HexagonRowColumn546.rows_assocBCA HexagonRowColumn546.cols_left0)) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 5 4 6) • (left1Middle5 4 6)) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem leftFinal5_case_4_6_row_0_2_0 : (((-1 : ℤ) ^ (leftScaleBit 5 4 6).val * positiveScale (leftScaleExponent 5 4 6)) •
      (rowColumnMul HexagonRowColumn546.rows_assocBCA HexagonRowColumn546.cols_left0)) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 5 4 6) • (left1Middle5 4 6)) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem leftFinal5_case_4_6_row_0_2_1 : (((-1 : ℤ) ^ (leftScaleBit 5 4 6).val * positiveScale (leftScaleExponent 5 4 6)) •
      (rowColumnMul HexagonRowColumn546.rows_assocBCA HexagonRowColumn546.cols_left0)) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 5 4 6) • (left1Middle5 4 6)) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem leftFinal5_case_4_6_row_0_3_0 : (((-1 : ℤ) ^ (leftScaleBit 5 4 6).val * positiveScale (leftScaleExponent 5 4 6)) •
      (rowColumnMul HexagonRowColumn546.rows_assocBCA HexagonRowColumn546.cols_left0)) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 5 4 6) • (left1Middle5 4 6)) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem leftFinal5_case_4_6_row_0_3_1 : (((-1 : ℤ) ^ (leftScaleBit 5 4 6).val * positiveScale (leftScaleExponent 5 4 6)) •
      (rowColumnMul HexagonRowColumn546.rows_assocBCA HexagonRowColumn546.cols_left0)) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 5 4 6) • (left1Middle5 4 6)) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem leftFinal5_case_4_6_row_1_0_0 : (((-1 : ℤ) ^ (leftScaleBit 5 4 6).val * positiveScale (leftScaleExponent 5 4 6)) •
      (rowColumnMul HexagonRowColumn546.rows_assocBCA HexagonRowColumn546.cols_left0)) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 5 4 6) • (left1Middle5 4 6)) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem leftFinal5_case_4_6_row_1_0_1 : (((-1 : ℤ) ^ (leftScaleBit 5 4 6).val * positiveScale (leftScaleExponent 5 4 6)) •
      (rowColumnMul HexagonRowColumn546.rows_assocBCA HexagonRowColumn546.cols_left0)) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 5 4 6) • (left1Middle5 4 6)) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem leftFinal5_case_4_6_row_1_1_0 : (((-1 : ℤ) ^ (leftScaleBit 5 4 6).val * positiveScale (leftScaleExponent 5 4 6)) •
      (rowColumnMul HexagonRowColumn546.rows_assocBCA HexagonRowColumn546.cols_left0)) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 5 4 6) • (left1Middle5 4 6)) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem leftFinal5_case_4_6_row_1_1_1 : (((-1 : ℤ) ^ (leftScaleBit 5 4 6).val * positiveScale (leftScaleExponent 5 4 6)) •
      (rowColumnMul HexagonRowColumn546.rows_assocBCA HexagonRowColumn546.cols_left0)) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 5 4 6) • (left1Middle5 4 6)) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem leftFinal5_case_4_6_row_1_2_0 : (((-1 : ℤ) ^ (leftScaleBit 5 4 6).val * positiveScale (leftScaleExponent 5 4 6)) •
      (rowColumnMul HexagonRowColumn546.rows_assocBCA HexagonRowColumn546.cols_left0)) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 5 4 6) • (left1Middle5 4 6)) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem leftFinal5_case_4_6_row_1_2_1 : (((-1 : ℤ) ^ (leftScaleBit 5 4 6).val * positiveScale (leftScaleExponent 5 4 6)) •
      (rowColumnMul HexagonRowColumn546.rows_assocBCA HexagonRowColumn546.cols_left0)) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 5 4 6) • (left1Middle5 4 6)) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem leftFinal5_case_4_6_row_1_3_0 : (((-1 : ℤ) ^ (leftScaleBit 5 4 6).val * positiveScale (leftScaleExponent 5 4 6)) •
      (rowColumnMul HexagonRowColumn546.rows_assocBCA HexagonRowColumn546.cols_left0)) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 5 4 6) • (left1Middle5 4 6)) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem leftFinal5_case_4_6_row_1_3_1 : (((-1 : ℤ) ^ (leftScaleBit 5 4 6).val * positiveScale (leftScaleExponent 5 4 6)) •
      (rowColumnMul HexagonRowColumn546.rows_assocBCA HexagonRowColumn546.cols_left0)) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 5 4 6) • (left1Middle5 4 6)) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem leftFinal5_case_4_6_checked : ((-1 : ℤ) ^ (leftScaleBit 5 4 6).val * positiveScale (leftScaleExponent 5 4 6)) •
      (rowColumnMul HexagonRowColumn546.rows_assocBCA HexagonRowColumn546.cols_left0) = negativeScale (leftScaleExponent 5 4 6) • (left1Middle5 4 6) := by
  funext r
  fin_cases r
  · exact leftFinal5_case_4_6_row_0_0_0
  · exact leftFinal5_case_4_6_row_0_0_1
  · exact leftFinal5_case_4_6_row_0_1_0
  · exact leftFinal5_case_4_6_row_0_1_1
  · exact leftFinal5_case_4_6_row_0_2_0
  · exact leftFinal5_case_4_6_row_0_2_1
  · exact leftFinal5_case_4_6_row_0_3_0
  · exact leftFinal5_case_4_6_row_0_3_1
  · exact leftFinal5_case_4_6_row_1_0_0
  · exact leftFinal5_case_4_6_row_1_0_1
  · exact leftFinal5_case_4_6_row_1_1_0
  · exact leftFinal5_case_4_6_row_1_1_1
  · exact leftFinal5_case_4_6_row_1_2_0
  · exact leftFinal5_case_4_6_row_1_2_1
  · exact leftFinal5_case_4_6_row_1_3_0
  · exact leftFinal5_case_4_6_row_1_3_1

set_option backward.isDefEq.respectTransparency false in
theorem leftFinal5_case_4_6 : ((-1 : ℤ) ^ (leftScaleBit 5 4 6).val * positiveScale (leftScaleExponent 5 4 6)) •
      (associatorZ 4 6 5 * left0Middle5 4 6) = negativeScale (leftScaleExponent 5 4 6) • (innerRightZ 4 5 6 * left1Middle5 4 6) := by
  simpa only [HexagonAtoms546.assocABC_eq,
    HexagonAtoms546.outerABC_eq,
    HexagonAtoms546.assocBAC_eq,
    HexagonAtoms546.innerABC_eq,
    HexagonAtoms546.innerRightABC_eq,
    HexagonAtoms546.inverseACB_eq,
    HexagonAtoms546.innerACB_eq,
    HexagonAtoms546.assocBCA_eq,
    HexagonAtoms546.innerRightBAC_eq,
    HexagonAtoms546.assocCAB_eq,
    HexagonAtoms546.outerLeftABC_eq,
    HexagonRowColumn546.product0_eq,
    HexagonRowColumn546.product1_eq,
    HexagonRowColumn546.product2_eq,
    HexagonRowColumn546.product3_eq,
    HexagonRowColumn546.product4_eq,
    HexagonRowColumn546.product5_eq,
    HexagonRowColumn546.product6_eq,
    HexagonRowColumn546.product7_eq] using leftFinal5_case_4_6_checked

private theorem rightFinal5_case_4_6_row_0_0_0 : (((-1 : ℤ) ^ (rightScaleBit 5 4 6).val * positiveScale (rightScaleExponent 5 4 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 6 4 : ℤ)) • HexagonAtoms546.outerLeftABC) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (negativeScale (rightScaleExponent 5 4 6) • (rowColumnMul HexagonRowColumn546.rows_assocCAB HexagonRowColumn546.cols_right2)) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem rightFinal5_case_4_6_row_0_0_1 : (((-1 : ℤ) ^ (rightScaleBit 5 4 6).val * positiveScale (rightScaleExponent 5 4 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 6 4 : ℤ)) • HexagonAtoms546.outerLeftABC) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (negativeScale (rightScaleExponent 5 4 6) • (rowColumnMul HexagonRowColumn546.rows_assocCAB HexagonRowColumn546.cols_right2)) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem rightFinal5_case_4_6_row_0_1_0 : (((-1 : ℤ) ^ (rightScaleBit 5 4 6).val * positiveScale (rightScaleExponent 5 4 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 6 4 : ℤ)) • HexagonAtoms546.outerLeftABC) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (negativeScale (rightScaleExponent 5 4 6) • (rowColumnMul HexagonRowColumn546.rows_assocCAB HexagonRowColumn546.cols_right2)) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem rightFinal5_case_4_6_row_0_1_1 : (((-1 : ℤ) ^ (rightScaleBit 5 4 6).val * positiveScale (rightScaleExponent 5 4 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 6 4 : ℤ)) • HexagonAtoms546.outerLeftABC) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (negativeScale (rightScaleExponent 5 4 6) • (rowColumnMul HexagonRowColumn546.rows_assocCAB HexagonRowColumn546.cols_right2)) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem rightFinal5_case_4_6_row_1_0_0 : (((-1 : ℤ) ^ (rightScaleBit 5 4 6).val * positiveScale (rightScaleExponent 5 4 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 6 4 : ℤ)) • HexagonAtoms546.outerLeftABC) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (negativeScale (rightScaleExponent 5 4 6) • (rowColumnMul HexagonRowColumn546.rows_assocCAB HexagonRowColumn546.cols_right2)) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem rightFinal5_case_4_6_row_1_0_1 : (((-1 : ℤ) ^ (rightScaleBit 5 4 6).val * positiveScale (rightScaleExponent 5 4 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 6 4 : ℤ)) • HexagonAtoms546.outerLeftABC) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (negativeScale (rightScaleExponent 5 4 6) • (rowColumnMul HexagonRowColumn546.rows_assocCAB HexagonRowColumn546.cols_right2)) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem rightFinal5_case_4_6_row_1_1_0 : (((-1 : ℤ) ^ (rightScaleBit 5 4 6).val * positiveScale (rightScaleExponent 5 4 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 6 4 : ℤ)) • HexagonAtoms546.outerLeftABC) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (negativeScale (rightScaleExponent 5 4 6) • (rowColumnMul HexagonRowColumn546.rows_assocCAB HexagonRowColumn546.cols_right2)) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem rightFinal5_case_4_6_row_1_1_1 : (((-1 : ℤ) ^ (rightScaleBit 5 4 6).val * positiveScale (rightScaleExponent 5 4 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 6 4 : ℤ)) • HexagonAtoms546.outerLeftABC) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (negativeScale (rightScaleExponent 5 4 6) • (rowColumnMul HexagonRowColumn546.rows_assocCAB HexagonRowColumn546.cols_right2)) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem rightFinal5_case_4_6_row_2_0_0 : (((-1 : ℤ) ^ (rightScaleBit 5 4 6).val * positiveScale (rightScaleExponent 5 4 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 6 4 : ℤ)) • HexagonAtoms546.outerLeftABC) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (negativeScale (rightScaleExponent 5 4 6) • (rowColumnMul HexagonRowColumn546.rows_assocCAB HexagonRowColumn546.cols_right2)) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem rightFinal5_case_4_6_row_2_0_1 : (((-1 : ℤ) ^ (rightScaleBit 5 4 6).val * positiveScale (rightScaleExponent 5 4 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 6 4 : ℤ)) • HexagonAtoms546.outerLeftABC) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (negativeScale (rightScaleExponent 5 4 6) • (rowColumnMul HexagonRowColumn546.rows_assocCAB HexagonRowColumn546.cols_right2)) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem rightFinal5_case_4_6_row_2_1_0 : (((-1 : ℤ) ^ (rightScaleBit 5 4 6).val * positiveScale (rightScaleExponent 5 4 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 6 4 : ℤ)) • HexagonAtoms546.outerLeftABC) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (negativeScale (rightScaleExponent 5 4 6) • (rowColumnMul HexagonRowColumn546.rows_assocCAB HexagonRowColumn546.cols_right2)) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem rightFinal5_case_4_6_row_2_1_1 : (((-1 : ℤ) ^ (rightScaleBit 5 4 6).val * positiveScale (rightScaleExponent 5 4 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 6 4 : ℤ)) • HexagonAtoms546.outerLeftABC) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (negativeScale (rightScaleExponent 5 4 6) • (rowColumnMul HexagonRowColumn546.rows_assocCAB HexagonRowColumn546.cols_right2)) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem rightFinal5_case_4_6_row_3_0_0 : (((-1 : ℤ) ^ (rightScaleBit 5 4 6).val * positiveScale (rightScaleExponent 5 4 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 6 4 : ℤ)) • HexagonAtoms546.outerLeftABC) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (negativeScale (rightScaleExponent 5 4 6) • (rowColumnMul HexagonRowColumn546.rows_assocCAB HexagonRowColumn546.cols_right2)) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem rightFinal5_case_4_6_row_3_0_1 : (((-1 : ℤ) ^ (rightScaleBit 5 4 6).val * positiveScale (rightScaleExponent 5 4 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 6 4 : ℤ)) • HexagonAtoms546.outerLeftABC) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (negativeScale (rightScaleExponent 5 4 6) • (rowColumnMul HexagonRowColumn546.rows_assocCAB HexagonRowColumn546.cols_right2)) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem rightFinal5_case_4_6_row_3_1_0 : (((-1 : ℤ) ^ (rightScaleBit 5 4 6).val * positiveScale (rightScaleExponent 5 4 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 6 4 : ℤ)) • HexagonAtoms546.outerLeftABC) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (negativeScale (rightScaleExponent 5 4 6) • (rowColumnMul HexagonRowColumn546.rows_assocCAB HexagonRowColumn546.cols_right2)) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem rightFinal5_case_4_6_row_3_1_1 : (((-1 : ℤ) ^ (rightScaleBit 5 4 6).val * positiveScale (rightScaleExponent 5 4 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 6 4 : ℤ)) • HexagonAtoms546.outerLeftABC) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (negativeScale (rightScaleExponent 5 4 6) • (rowColumnMul HexagonRowColumn546.rows_assocCAB HexagonRowColumn546.cols_right2)) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem rightFinal5_case_4_6_checked : ((-1 : ℤ) ^ (rightScaleBit 5 4 6).val * positiveScale (rightScaleExponent 5 4 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 6 4 : ℤ)) • HexagonAtoms546.outerLeftABC = negativeScale (rightScaleExponent 5 4 6) • (rowColumnMul HexagonRowColumn546.rows_assocCAB HexagonRowColumn546.cols_right2) := by
  funext r
  fin_cases r
  · exact rightFinal5_case_4_6_row_0_0_0
  · exact rightFinal5_case_4_6_row_0_0_1
  · exact rightFinal5_case_4_6_row_0_1_0
  · exact rightFinal5_case_4_6_row_0_1_1
  · exact rightFinal5_case_4_6_row_1_0_0
  · exact rightFinal5_case_4_6_row_1_0_1
  · exact rightFinal5_case_4_6_row_1_1_0
  · exact rightFinal5_case_4_6_row_1_1_1
  · exact rightFinal5_case_4_6_row_2_0_0
  · exact rightFinal5_case_4_6_row_2_0_1
  · exact rightFinal5_case_4_6_row_2_1_0
  · exact rightFinal5_case_4_6_row_2_1_1
  · exact rightFinal5_case_4_6_row_3_0_0
  · exact rightFinal5_case_4_6_row_3_0_1
  · exact rightFinal5_case_4_6_row_3_1_0
  · exact rightFinal5_case_4_6_row_3_1_1

set_option backward.isDefEq.respectTransparency false in
theorem rightFinal5_case_4_6 : ((-1 : ℤ) ^ (rightScaleBit 5 4 6).val * positiveScale (rightScaleExponent 5 4 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 6 4 : ℤ)) • outerLeftZ 5 4 6 = negativeScale (rightScaleExponent 5 4 6) • (associatorZ 6 5 4 * right2Middle5 4 6) := by
  simpa only [HexagonAtoms546.assocABC_eq,
    HexagonAtoms546.outerABC_eq,
    HexagonAtoms546.assocBAC_eq,
    HexagonAtoms546.innerABC_eq,
    HexagonAtoms546.innerRightABC_eq,
    HexagonAtoms546.inverseACB_eq,
    HexagonAtoms546.innerACB_eq,
    HexagonAtoms546.assocBCA_eq,
    HexagonAtoms546.innerRightBAC_eq,
    HexagonAtoms546.assocCAB_eq,
    HexagonAtoms546.outerLeftABC_eq,
    HexagonRowColumn546.product0_eq,
    HexagonRowColumn546.product1_eq,
    HexagonRowColumn546.product2_eq,
    HexagonRowColumn546.product3_eq,
    HexagonRowColumn546.product4_eq,
    HexagonRowColumn546.product5_eq,
    HexagonRowColumn546.product6_eq,
    HexagonRowColumn546.product7_eq] using rightFinal5_case_4_6_checked

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonCases5
