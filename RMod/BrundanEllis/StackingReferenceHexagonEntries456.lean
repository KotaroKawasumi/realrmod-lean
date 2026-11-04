import RMod.BrundanEllis.StackingReferenceHexagonMiddle4
import RMod.BrundanEllis.StackingReferenceSparseMatrixCheck
import RMod.BrundanEllis.StackingReferenceHexagonAtoms456
import RMod.BrundanEllis.StackingReferenceHexagonRowColumn456

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

private theorem left0Middle4_eq_case_5_6_row_0_0_0 : (left0Middle4 5 6) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (HexagonAtoms456.assocABC) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left0Middle4_eq_case_5_6_row_0_0_1 : (left0Middle4 5 6) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (HexagonAtoms456.assocABC) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left0Middle4_eq_case_5_6_row_0_1_0 : (left0Middle4 5 6) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (HexagonAtoms456.assocABC) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left0Middle4_eq_case_5_6_row_0_1_1 : (left0Middle4 5 6) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (HexagonAtoms456.assocABC) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left0Middle4_eq_case_5_6_row_0_2_0 : (left0Middle4 5 6) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (HexagonAtoms456.assocABC) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left0Middle4_eq_case_5_6_row_0_2_1 : (left0Middle4 5 6) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (HexagonAtoms456.assocABC) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left0Middle4_eq_case_5_6_row_0_3_0 : (left0Middle4 5 6) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (HexagonAtoms456.assocABC) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left0Middle4_eq_case_5_6_row_0_3_1 : (left0Middle4 5 6) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (HexagonAtoms456.assocABC) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left0Middle4_eq_case_5_6_row_1_0_0 : (left0Middle4 5 6) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (HexagonAtoms456.assocABC) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left0Middle4_eq_case_5_6_row_1_0_1 : (left0Middle4 5 6) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (HexagonAtoms456.assocABC) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left0Middle4_eq_case_5_6_row_1_1_0 : (left0Middle4 5 6) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (HexagonAtoms456.assocABC) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left0Middle4_eq_case_5_6_row_1_1_1 : (left0Middle4 5 6) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (HexagonAtoms456.assocABC) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left0Middle4_eq_case_5_6_row_1_2_0 : (left0Middle4 5 6) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (HexagonAtoms456.assocABC) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left0Middle4_eq_case_5_6_row_1_2_1 : (left0Middle4 5 6) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (HexagonAtoms456.assocABC) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left0Middle4_eq_case_5_6_row_1_3_0 : (left0Middle4 5 6) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (HexagonAtoms456.assocABC) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left0Middle4_eq_case_5_6_row_1_3_1 : (left0Middle4 5 6) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (HexagonAtoms456.assocABC) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left0Middle4_eq_case_5_6_checked : left0Middle4 5 6 = HexagonAtoms456.assocABC := by
  funext r
  fin_cases r
  · exact left0Middle4_eq_case_5_6_row_0_0_0
  · exact left0Middle4_eq_case_5_6_row_0_0_1
  · exact left0Middle4_eq_case_5_6_row_0_1_0
  · exact left0Middle4_eq_case_5_6_row_0_1_1
  · exact left0Middle4_eq_case_5_6_row_0_2_0
  · exact left0Middle4_eq_case_5_6_row_0_2_1
  · exact left0Middle4_eq_case_5_6_row_0_3_0
  · exact left0Middle4_eq_case_5_6_row_0_3_1
  · exact left0Middle4_eq_case_5_6_row_1_0_0
  · exact left0Middle4_eq_case_5_6_row_1_0_1
  · exact left0Middle4_eq_case_5_6_row_1_1_0
  · exact left0Middle4_eq_case_5_6_row_1_1_1
  · exact left0Middle4_eq_case_5_6_row_1_2_0
  · exact left0Middle4_eq_case_5_6_row_1_2_1
  · exact left0Middle4_eq_case_5_6_row_1_3_0
  · exact left0Middle4_eq_case_5_6_row_1_3_1

set_option backward.isDefEq.respectTransparency false in
theorem left0Middle4_eq_case_5_6 : left0Middle4 5 6 = outerRightZ 4 5 6 * associatorZ 4 5 6 := by
  simpa only [HexagonAtoms456.assocABC_eq,
    HexagonAtoms456.outerABC_eq,
    HexagonAtoms456.assocBAC_eq,
    HexagonAtoms456.innerABC_eq,
    HexagonAtoms456.innerRightABC_eq,
    HexagonAtoms456.inverseACB_eq,
    HexagonAtoms456.innerACB_eq,
    HexagonAtoms456.assocBCA_eq,
    HexagonAtoms456.innerRightBAC_eq,
    HexagonAtoms456.assocCAB_eq,
    HexagonAtoms456.outerLeftABC_eq,
    HexagonRowColumn456.product0_eq,
    HexagonRowColumn456.product1_eq,
    HexagonRowColumn456.product2_eq,
    HexagonRowColumn456.product3_eq,
    HexagonRowColumn456.product4_eq,
    HexagonRowColumn456.product5_eq,
    HexagonRowColumn456.product6_eq,
    HexagonRowColumn456.product7_eq] using left0Middle4_eq_case_5_6_checked

private theorem left1Middle4_eq_case_5_6_row_0_0_0 : (left1Middle4 5 6) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (HexagonAtoms456.assocBAC) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left1Middle4_eq_case_5_6_row_0_0_1 : (left1Middle4 5 6) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (HexagonAtoms456.assocBAC) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left1Middle4_eq_case_5_6_row_0_1_0 : (left1Middle4 5 6) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (HexagonAtoms456.assocBAC) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left1Middle4_eq_case_5_6_row_0_1_1 : (left1Middle4 5 6) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (HexagonAtoms456.assocBAC) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left1Middle4_eq_case_5_6_row_0_2_0 : (left1Middle4 5 6) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (HexagonAtoms456.assocBAC) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left1Middle4_eq_case_5_6_row_0_2_1 : (left1Middle4 5 6) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (HexagonAtoms456.assocBAC) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left1Middle4_eq_case_5_6_row_0_3_0 : (left1Middle4 5 6) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (HexagonAtoms456.assocBAC) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left1Middle4_eq_case_5_6_row_0_3_1 : (left1Middle4 5 6) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (HexagonAtoms456.assocBAC) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left1Middle4_eq_case_5_6_row_1_0_0 : (left1Middle4 5 6) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (HexagonAtoms456.assocBAC) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left1Middle4_eq_case_5_6_row_1_0_1 : (left1Middle4 5 6) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (HexagonAtoms456.assocBAC) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left1Middle4_eq_case_5_6_row_1_1_0 : (left1Middle4 5 6) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (HexagonAtoms456.assocBAC) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left1Middle4_eq_case_5_6_row_1_1_1 : (left1Middle4 5 6) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (HexagonAtoms456.assocBAC) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left1Middle4_eq_case_5_6_row_1_2_0 : (left1Middle4 5 6) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (HexagonAtoms456.assocBAC) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left1Middle4_eq_case_5_6_row_1_2_1 : (left1Middle4 5 6) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (HexagonAtoms456.assocBAC) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left1Middle4_eq_case_5_6_row_1_3_0 : (left1Middle4 5 6) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (HexagonAtoms456.assocBAC) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left1Middle4_eq_case_5_6_row_1_3_1 : (left1Middle4 5 6) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (HexagonAtoms456.assocBAC) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem left1Middle4_eq_case_5_6_checked : left1Middle4 5 6 = HexagonAtoms456.assocBAC := by
  funext r
  fin_cases r
  · exact left1Middle4_eq_case_5_6_row_0_0_0
  · exact left1Middle4_eq_case_5_6_row_0_0_1
  · exact left1Middle4_eq_case_5_6_row_0_1_0
  · exact left1Middle4_eq_case_5_6_row_0_1_1
  · exact left1Middle4_eq_case_5_6_row_0_2_0
  · exact left1Middle4_eq_case_5_6_row_0_2_1
  · exact left1Middle4_eq_case_5_6_row_0_3_0
  · exact left1Middle4_eq_case_5_6_row_0_3_1
  · exact left1Middle4_eq_case_5_6_row_1_0_0
  · exact left1Middle4_eq_case_5_6_row_1_0_1
  · exact left1Middle4_eq_case_5_6_row_1_1_0
  · exact left1Middle4_eq_case_5_6_row_1_1_1
  · exact left1Middle4_eq_case_5_6_row_1_2_0
  · exact left1Middle4_eq_case_5_6_row_1_2_1
  · exact left1Middle4_eq_case_5_6_row_1_3_0
  · exact left1Middle4_eq_case_5_6_row_1_3_1

set_option backward.isDefEq.respectTransparency false in
theorem left1Middle4_eq_case_5_6 : left1Middle4 5 6 = associatorZ 5 4 6 * innerLeftZ 4 5 6 := by
  simpa only [HexagonAtoms456.assocABC_eq,
    HexagonAtoms456.outerABC_eq,
    HexagonAtoms456.assocBAC_eq,
    HexagonAtoms456.innerABC_eq,
    HexagonAtoms456.innerRightABC_eq,
    HexagonAtoms456.inverseACB_eq,
    HexagonAtoms456.innerACB_eq,
    HexagonAtoms456.assocBCA_eq,
    HexagonAtoms456.innerRightBAC_eq,
    HexagonAtoms456.assocCAB_eq,
    HexagonAtoms456.outerLeftABC_eq,
    HexagonRowColumn456.product0_eq,
    HexagonRowColumn456.product1_eq,
    HexagonRowColumn456.product2_eq,
    HexagonRowColumn456.product3_eq,
    HexagonRowColumn456.product4_eq,
    HexagonRowColumn456.product5_eq,
    HexagonRowColumn456.product6_eq,
    HexagonRowColumn456.product7_eq] using left1Middle4_eq_case_5_6_checked

private theorem right0Middle4_eq_case_5_6_row_0_0_0 : (right0Middle4 5 6) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (HexagonAtoms456.assocABC) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right0Middle4_eq_case_5_6_row_0_0_1 : (right0Middle4 5 6) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (HexagonAtoms456.assocABC) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right0Middle4_eq_case_5_6_row_0_1_0 : (right0Middle4 5 6) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (HexagonAtoms456.assocABC) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right0Middle4_eq_case_5_6_row_0_1_1 : (right0Middle4 5 6) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (HexagonAtoms456.assocABC) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right0Middle4_eq_case_5_6_row_0_2_0 : (right0Middle4 5 6) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (HexagonAtoms456.assocABC) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right0Middle4_eq_case_5_6_row_0_2_1 : (right0Middle4 5 6) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (HexagonAtoms456.assocABC) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right0Middle4_eq_case_5_6_row_0_3_0 : (right0Middle4 5 6) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (HexagonAtoms456.assocABC) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right0Middle4_eq_case_5_6_row_0_3_1 : (right0Middle4 5 6) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (HexagonAtoms456.assocABC) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right0Middle4_eq_case_5_6_row_1_0_0 : (right0Middle4 5 6) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (HexagonAtoms456.assocABC) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right0Middle4_eq_case_5_6_row_1_0_1 : (right0Middle4 5 6) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (HexagonAtoms456.assocABC) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right0Middle4_eq_case_5_6_row_1_1_0 : (right0Middle4 5 6) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (HexagonAtoms456.assocABC) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right0Middle4_eq_case_5_6_row_1_1_1 : (right0Middle4 5 6) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (HexagonAtoms456.assocABC) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right0Middle4_eq_case_5_6_row_1_2_0 : (right0Middle4 5 6) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (HexagonAtoms456.assocABC) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right0Middle4_eq_case_5_6_row_1_2_1 : (right0Middle4 5 6) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (HexagonAtoms456.assocABC) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right0Middle4_eq_case_5_6_row_1_3_0 : (right0Middle4 5 6) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (HexagonAtoms456.assocABC) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right0Middle4_eq_case_5_6_row_1_3_1 : (right0Middle4 5 6) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (HexagonAtoms456.assocABC) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right0Middle4_eq_case_5_6_checked : right0Middle4 5 6 = HexagonAtoms456.assocABC := by
  funext r
  fin_cases r
  · exact right0Middle4_eq_case_5_6_row_0_0_0
  · exact right0Middle4_eq_case_5_6_row_0_0_1
  · exact right0Middle4_eq_case_5_6_row_0_1_0
  · exact right0Middle4_eq_case_5_6_row_0_1_1
  · exact right0Middle4_eq_case_5_6_row_0_2_0
  · exact right0Middle4_eq_case_5_6_row_0_2_1
  · exact right0Middle4_eq_case_5_6_row_0_3_0
  · exact right0Middle4_eq_case_5_6_row_0_3_1
  · exact right0Middle4_eq_case_5_6_row_1_0_0
  · exact right0Middle4_eq_case_5_6_row_1_0_1
  · exact right0Middle4_eq_case_5_6_row_1_1_0
  · exact right0Middle4_eq_case_5_6_row_1_1_1
  · exact right0Middle4_eq_case_5_6_row_1_2_0
  · exact right0Middle4_eq_case_5_6_row_1_2_1
  · exact right0Middle4_eq_case_5_6_row_1_3_0
  · exact right0Middle4_eq_case_5_6_row_1_3_1

set_option backward.isDefEq.respectTransparency false in
theorem right0Middle4_eq_case_5_6 : right0Middle4 5 6 = innerRightZ 4 5 6 * associatorZ 4 5 6 := by
  simpa only [HexagonAtoms456.assocABC_eq,
    HexagonAtoms456.outerABC_eq,
    HexagonAtoms456.assocBAC_eq,
    HexagonAtoms456.innerABC_eq,
    HexagonAtoms456.innerRightABC_eq,
    HexagonAtoms456.inverseACB_eq,
    HexagonAtoms456.innerACB_eq,
    HexagonAtoms456.assocBCA_eq,
    HexagonAtoms456.innerRightBAC_eq,
    HexagonAtoms456.assocCAB_eq,
    HexagonAtoms456.outerLeftABC_eq,
    HexagonRowColumn456.product0_eq,
    HexagonRowColumn456.product1_eq,
    HexagonRowColumn456.product2_eq,
    HexagonRowColumn456.product3_eq,
    HexagonRowColumn456.product4_eq,
    HexagonRowColumn456.product5_eq,
    HexagonRowColumn456.product6_eq,
    HexagonRowColumn456.product7_eq] using right0Middle4_eq_case_5_6_checked

private theorem right1Middle4_eq_case_5_6_row_0_0_0 : (right1Middle4 5 6) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn456.rows_inverseACB HexagonRowColumn456.cols_right0) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right1Middle4_eq_case_5_6_row_0_0_1 : (right1Middle4 5 6) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn456.rows_inverseACB HexagonRowColumn456.cols_right0) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right1Middle4_eq_case_5_6_row_0_1_0 : (right1Middle4 5 6) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn456.rows_inverseACB HexagonRowColumn456.cols_right0) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right1Middle4_eq_case_5_6_row_0_1_1 : (right1Middle4 5 6) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn456.rows_inverseACB HexagonRowColumn456.cols_right0) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right1Middle4_eq_case_5_6_row_0_2_0 : (right1Middle4 5 6) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn456.rows_inverseACB HexagonRowColumn456.cols_right0) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right1Middle4_eq_case_5_6_row_0_2_1 : (right1Middle4 5 6) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn456.rows_inverseACB HexagonRowColumn456.cols_right0) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right1Middle4_eq_case_5_6_row_0_3_0 : (right1Middle4 5 6) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn456.rows_inverseACB HexagonRowColumn456.cols_right0) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right1Middle4_eq_case_5_6_row_0_3_1 : (right1Middle4 5 6) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn456.rows_inverseACB HexagonRowColumn456.cols_right0) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right1Middle4_eq_case_5_6_row_1_0_0 : (right1Middle4 5 6) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn456.rows_inverseACB HexagonRowColumn456.cols_right0) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right1Middle4_eq_case_5_6_row_1_0_1 : (right1Middle4 5 6) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn456.rows_inverseACB HexagonRowColumn456.cols_right0) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right1Middle4_eq_case_5_6_row_1_1_0 : (right1Middle4 5 6) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn456.rows_inverseACB HexagonRowColumn456.cols_right0) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right1Middle4_eq_case_5_6_row_1_1_1 : (right1Middle4 5 6) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn456.rows_inverseACB HexagonRowColumn456.cols_right0) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right1Middle4_eq_case_5_6_row_1_2_0 : (right1Middle4 5 6) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn456.rows_inverseACB HexagonRowColumn456.cols_right0) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right1Middle4_eq_case_5_6_row_1_2_1 : (right1Middle4 5 6) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn456.rows_inverseACB HexagonRowColumn456.cols_right0) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right1Middle4_eq_case_5_6_row_1_3_0 : (right1Middle4 5 6) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn456.rows_inverseACB HexagonRowColumn456.cols_right0) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right1Middle4_eq_case_5_6_row_1_3_1 : (right1Middle4 5 6) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn456.rows_inverseACB HexagonRowColumn456.cols_right0) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right1Middle4_eq_case_5_6_checked : right1Middle4 5 6 = rowColumnMul HexagonRowColumn456.rows_inverseACB HexagonRowColumn456.cols_right0 := by
  funext r
  fin_cases r
  · exact right1Middle4_eq_case_5_6_row_0_0_0
  · exact right1Middle4_eq_case_5_6_row_0_0_1
  · exact right1Middle4_eq_case_5_6_row_0_1_0
  · exact right1Middle4_eq_case_5_6_row_0_1_1
  · exact right1Middle4_eq_case_5_6_row_0_2_0
  · exact right1Middle4_eq_case_5_6_row_0_2_1
  · exact right1Middle4_eq_case_5_6_row_0_3_0
  · exact right1Middle4_eq_case_5_6_row_0_3_1
  · exact right1Middle4_eq_case_5_6_row_1_0_0
  · exact right1Middle4_eq_case_5_6_row_1_0_1
  · exact right1Middle4_eq_case_5_6_row_1_1_0
  · exact right1Middle4_eq_case_5_6_row_1_1_1
  · exact right1Middle4_eq_case_5_6_row_1_2_0
  · exact right1Middle4_eq_case_5_6_row_1_2_1
  · exact right1Middle4_eq_case_5_6_row_1_3_0
  · exact right1Middle4_eq_case_5_6_row_1_3_1

set_option backward.isDefEq.respectTransparency false in
theorem right1Middle4_eq_case_5_6 : right1Middle4 5 6 = associatorInverseZ 4 6 5 * right0Middle4 5 6 := by
  simpa only [HexagonAtoms456.assocABC_eq,
    HexagonAtoms456.outerABC_eq,
    HexagonAtoms456.assocBAC_eq,
    HexagonAtoms456.innerABC_eq,
    HexagonAtoms456.innerRightABC_eq,
    HexagonAtoms456.inverseACB_eq,
    HexagonAtoms456.innerACB_eq,
    HexagonAtoms456.assocBCA_eq,
    HexagonAtoms456.innerRightBAC_eq,
    HexagonAtoms456.assocCAB_eq,
    HexagonAtoms456.outerLeftABC_eq,
    HexagonRowColumn456.product0_eq,
    HexagonRowColumn456.product1_eq,
    HexagonRowColumn456.product2_eq,
    HexagonRowColumn456.product3_eq,
    HexagonRowColumn456.product4_eq,
    HexagonRowColumn456.product5_eq,
    HexagonRowColumn456.product6_eq,
    HexagonRowColumn456.product7_eq] using right1Middle4_eq_case_5_6_checked

private theorem right2Middle4_eq_case_5_6_row_0_0_0 : (right2Middle4 5 6) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (right1Middle4 5 6) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right2Middle4_eq_case_5_6_row_0_0_1 : (right2Middle4 5 6) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (right1Middle4 5 6) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right2Middle4_eq_case_5_6_row_0_1_0 : (right2Middle4 5 6) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (right1Middle4 5 6) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right2Middle4_eq_case_5_6_row_0_1_1 : (right2Middle4 5 6) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (right1Middle4 5 6) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right2Middle4_eq_case_5_6_row_0_2_0 : (right2Middle4 5 6) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (right1Middle4 5 6) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right2Middle4_eq_case_5_6_row_0_2_1 : (right2Middle4 5 6) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (right1Middle4 5 6) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right2Middle4_eq_case_5_6_row_0_3_0 : (right2Middle4 5 6) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (right1Middle4 5 6) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right2Middle4_eq_case_5_6_row_0_3_1 : (right2Middle4 5 6) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (right1Middle4 5 6) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right2Middle4_eq_case_5_6_row_1_0_0 : (right2Middle4 5 6) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (right1Middle4 5 6) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right2Middle4_eq_case_5_6_row_1_0_1 : (right2Middle4 5 6) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (right1Middle4 5 6) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right2Middle4_eq_case_5_6_row_1_1_0 : (right2Middle4 5 6) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (right1Middle4 5 6) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right2Middle4_eq_case_5_6_row_1_1_1 : (right2Middle4 5 6) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (right1Middle4 5 6) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right2Middle4_eq_case_5_6_row_1_2_0 : (right2Middle4 5 6) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (right1Middle4 5 6) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right2Middle4_eq_case_5_6_row_1_2_1 : (right2Middle4 5 6) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (right1Middle4 5 6) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right2Middle4_eq_case_5_6_row_1_3_0 : (right2Middle4 5 6) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (right1Middle4 5 6) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right2Middle4_eq_case_5_6_row_1_3_1 : (right2Middle4 5 6) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (right1Middle4 5 6) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem right2Middle4_eq_case_5_6_checked : right2Middle4 5 6 = right1Middle4 5 6 := by
  funext r
  fin_cases r
  · exact right2Middle4_eq_case_5_6_row_0_0_0
  · exact right2Middle4_eq_case_5_6_row_0_0_1
  · exact right2Middle4_eq_case_5_6_row_0_1_0
  · exact right2Middle4_eq_case_5_6_row_0_1_1
  · exact right2Middle4_eq_case_5_6_row_0_2_0
  · exact right2Middle4_eq_case_5_6_row_0_2_1
  · exact right2Middle4_eq_case_5_6_row_0_3_0
  · exact right2Middle4_eq_case_5_6_row_0_3_1
  · exact right2Middle4_eq_case_5_6_row_1_0_0
  · exact right2Middle4_eq_case_5_6_row_1_0_1
  · exact right2Middle4_eq_case_5_6_row_1_1_0
  · exact right2Middle4_eq_case_5_6_row_1_1_1
  · exact right2Middle4_eq_case_5_6_row_1_2_0
  · exact right2Middle4_eq_case_5_6_row_1_2_1
  · exact right2Middle4_eq_case_5_6_row_1_3_0
  · exact right2Middle4_eq_case_5_6_row_1_3_1

set_option backward.isDefEq.respectTransparency false in
theorem right2Middle4_eq_case_5_6 : right2Middle4 5 6 = innerLeftZ 4 6 5 * right1Middle4 5 6 := by
  simpa only [HexagonAtoms456.assocABC_eq,
    HexagonAtoms456.outerABC_eq,
    HexagonAtoms456.assocBAC_eq,
    HexagonAtoms456.innerABC_eq,
    HexagonAtoms456.innerRightABC_eq,
    HexagonAtoms456.inverseACB_eq,
    HexagonAtoms456.innerACB_eq,
    HexagonAtoms456.assocBCA_eq,
    HexagonAtoms456.innerRightBAC_eq,
    HexagonAtoms456.assocCAB_eq,
    HexagonAtoms456.outerLeftABC_eq,
    HexagonRowColumn456.product0_eq,
    HexagonRowColumn456.product1_eq,
    HexagonRowColumn456.product2_eq,
    HexagonRowColumn456.product3_eq,
    HexagonRowColumn456.product4_eq,
    HexagonRowColumn456.product5_eq,
    HexagonRowColumn456.product6_eq,
    HexagonRowColumn456.product7_eq] using right2Middle4_eq_case_5_6_checked

private theorem leftFinal4_case_5_6_row_0_0_0 : (((-1 : ℤ) ^ (leftScaleBit 4 5 6).val * positiveScale (leftScaleExponent 4 5 6)) •
      (rowColumnMul HexagonRowColumn456.rows_assocBCA HexagonRowColumn456.cols_left0)) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 4 5 6) • (left1Middle4 5 6)) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem leftFinal4_case_5_6_row_0_0_1 : (((-1 : ℤ) ^ (leftScaleBit 4 5 6).val * positiveScale (leftScaleExponent 4 5 6)) •
      (rowColumnMul HexagonRowColumn456.rows_assocBCA HexagonRowColumn456.cols_left0)) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 4 5 6) • (left1Middle4 5 6)) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem leftFinal4_case_5_6_row_0_1_0 : (((-1 : ℤ) ^ (leftScaleBit 4 5 6).val * positiveScale (leftScaleExponent 4 5 6)) •
      (rowColumnMul HexagonRowColumn456.rows_assocBCA HexagonRowColumn456.cols_left0)) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 4 5 6) • (left1Middle4 5 6)) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem leftFinal4_case_5_6_row_0_1_1 : (((-1 : ℤ) ^ (leftScaleBit 4 5 6).val * positiveScale (leftScaleExponent 4 5 6)) •
      (rowColumnMul HexagonRowColumn456.rows_assocBCA HexagonRowColumn456.cols_left0)) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 4 5 6) • (left1Middle4 5 6)) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem leftFinal4_case_5_6_row_0_2_0 : (((-1 : ℤ) ^ (leftScaleBit 4 5 6).val * positiveScale (leftScaleExponent 4 5 6)) •
      (rowColumnMul HexagonRowColumn456.rows_assocBCA HexagonRowColumn456.cols_left0)) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 4 5 6) • (left1Middle4 5 6)) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem leftFinal4_case_5_6_row_0_2_1 : (((-1 : ℤ) ^ (leftScaleBit 4 5 6).val * positiveScale (leftScaleExponent 4 5 6)) •
      (rowColumnMul HexagonRowColumn456.rows_assocBCA HexagonRowColumn456.cols_left0)) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 4 5 6) • (left1Middle4 5 6)) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem leftFinal4_case_5_6_row_0_3_0 : (((-1 : ℤ) ^ (leftScaleBit 4 5 6).val * positiveScale (leftScaleExponent 4 5 6)) •
      (rowColumnMul HexagonRowColumn456.rows_assocBCA HexagonRowColumn456.cols_left0)) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 4 5 6) • (left1Middle4 5 6)) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem leftFinal4_case_5_6_row_0_3_1 : (((-1 : ℤ) ^ (leftScaleBit 4 5 6).val * positiveScale (leftScaleExponent 4 5 6)) •
      (rowColumnMul HexagonRowColumn456.rows_assocBCA HexagonRowColumn456.cols_left0)) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 4 5 6) • (left1Middle4 5 6)) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem leftFinal4_case_5_6_row_1_0_0 : (((-1 : ℤ) ^ (leftScaleBit 4 5 6).val * positiveScale (leftScaleExponent 4 5 6)) •
      (rowColumnMul HexagonRowColumn456.rows_assocBCA HexagonRowColumn456.cols_left0)) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 4 5 6) • (left1Middle4 5 6)) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem leftFinal4_case_5_6_row_1_0_1 : (((-1 : ℤ) ^ (leftScaleBit 4 5 6).val * positiveScale (leftScaleExponent 4 5 6)) •
      (rowColumnMul HexagonRowColumn456.rows_assocBCA HexagonRowColumn456.cols_left0)) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 4 5 6) • (left1Middle4 5 6)) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem leftFinal4_case_5_6_row_1_1_0 : (((-1 : ℤ) ^ (leftScaleBit 4 5 6).val * positiveScale (leftScaleExponent 4 5 6)) •
      (rowColumnMul HexagonRowColumn456.rows_assocBCA HexagonRowColumn456.cols_left0)) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 4 5 6) • (left1Middle4 5 6)) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem leftFinal4_case_5_6_row_1_1_1 : (((-1 : ℤ) ^ (leftScaleBit 4 5 6).val * positiveScale (leftScaleExponent 4 5 6)) •
      (rowColumnMul HexagonRowColumn456.rows_assocBCA HexagonRowColumn456.cols_left0)) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 4 5 6) • (left1Middle4 5 6)) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem leftFinal4_case_5_6_row_1_2_0 : (((-1 : ℤ) ^ (leftScaleBit 4 5 6).val * positiveScale (leftScaleExponent 4 5 6)) •
      (rowColumnMul HexagonRowColumn456.rows_assocBCA HexagonRowColumn456.cols_left0)) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 4 5 6) • (left1Middle4 5 6)) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem leftFinal4_case_5_6_row_1_2_1 : (((-1 : ℤ) ^ (leftScaleBit 4 5 6).val * positiveScale (leftScaleExponent 4 5 6)) •
      (rowColumnMul HexagonRowColumn456.rows_assocBCA HexagonRowColumn456.cols_left0)) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 4 5 6) • (left1Middle4 5 6)) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem leftFinal4_case_5_6_row_1_3_0 : (((-1 : ℤ) ^ (leftScaleBit 4 5 6).val * positiveScale (leftScaleExponent 4 5 6)) •
      (rowColumnMul HexagonRowColumn456.rows_assocBCA HexagonRowColumn456.cols_left0)) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 4 5 6) • (left1Middle4 5 6)) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem leftFinal4_case_5_6_row_1_3_1 : (((-1 : ℤ) ^ (leftScaleBit 4 5 6).val * positiveScale (leftScaleExponent 4 5 6)) •
      (rowColumnMul HexagonRowColumn456.rows_assocBCA HexagonRowColumn456.cols_left0)) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 4 5 6) • (left1Middle4 5 6)) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem leftFinal4_case_5_6_checked : ((-1 : ℤ) ^ (leftScaleBit 4 5 6).val * positiveScale (leftScaleExponent 4 5 6)) •
      (rowColumnMul HexagonRowColumn456.rows_assocBCA HexagonRowColumn456.cols_left0) = negativeScale (leftScaleExponent 4 5 6) • (left1Middle4 5 6) := by
  funext r
  fin_cases r
  · exact leftFinal4_case_5_6_row_0_0_0
  · exact leftFinal4_case_5_6_row_0_0_1
  · exact leftFinal4_case_5_6_row_0_1_0
  · exact leftFinal4_case_5_6_row_0_1_1
  · exact leftFinal4_case_5_6_row_0_2_0
  · exact leftFinal4_case_5_6_row_0_2_1
  · exact leftFinal4_case_5_6_row_0_3_0
  · exact leftFinal4_case_5_6_row_0_3_1
  · exact leftFinal4_case_5_6_row_1_0_0
  · exact leftFinal4_case_5_6_row_1_0_1
  · exact leftFinal4_case_5_6_row_1_1_0
  · exact leftFinal4_case_5_6_row_1_1_1
  · exact leftFinal4_case_5_6_row_1_2_0
  · exact leftFinal4_case_5_6_row_1_2_1
  · exact leftFinal4_case_5_6_row_1_3_0
  · exact leftFinal4_case_5_6_row_1_3_1

set_option backward.isDefEq.respectTransparency false in
theorem leftFinal4_case_5_6 : ((-1 : ℤ) ^ (leftScaleBit 4 5 6).val * positiveScale (leftScaleExponent 4 5 6)) •
      (associatorZ 5 6 4 * left0Middle4 5 6) = negativeScale (leftScaleExponent 4 5 6) • (innerRightZ 5 4 6 * left1Middle4 5 6) := by
  simpa only [HexagonAtoms456.assocABC_eq,
    HexagonAtoms456.outerABC_eq,
    HexagonAtoms456.assocBAC_eq,
    HexagonAtoms456.innerABC_eq,
    HexagonAtoms456.innerRightABC_eq,
    HexagonAtoms456.inverseACB_eq,
    HexagonAtoms456.innerACB_eq,
    HexagonAtoms456.assocBCA_eq,
    HexagonAtoms456.innerRightBAC_eq,
    HexagonAtoms456.assocCAB_eq,
    HexagonAtoms456.outerLeftABC_eq,
    HexagonRowColumn456.product0_eq,
    HexagonRowColumn456.product1_eq,
    HexagonRowColumn456.product2_eq,
    HexagonRowColumn456.product3_eq,
    HexagonRowColumn456.product4_eq,
    HexagonRowColumn456.product5_eq,
    HexagonRowColumn456.product6_eq,
    HexagonRowColumn456.product7_eq] using leftFinal4_case_5_6_checked

private theorem rightFinal4_case_5_6_row_0_0_0 : (((-1 : ℤ) ^ (rightScaleBit 4 5 6).val * positiveScale (rightScaleExponent 4 5 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 6 5 : ℤ)) • HexagonAtoms456.outerLeftABC) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (negativeScale (rightScaleExponent 4 5 6) • (rowColumnMul HexagonRowColumn456.rows_assocCAB HexagonRowColumn456.cols_right2)) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem rightFinal4_case_5_6_row_0_0_1 : (((-1 : ℤ) ^ (rightScaleBit 4 5 6).val * positiveScale (rightScaleExponent 4 5 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 6 5 : ℤ)) • HexagonAtoms456.outerLeftABC) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (negativeScale (rightScaleExponent 4 5 6) • (rowColumnMul HexagonRowColumn456.rows_assocCAB HexagonRowColumn456.cols_right2)) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem rightFinal4_case_5_6_row_0_1_0 : (((-1 : ℤ) ^ (rightScaleBit 4 5 6).val * positiveScale (rightScaleExponent 4 5 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 6 5 : ℤ)) • HexagonAtoms456.outerLeftABC) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (negativeScale (rightScaleExponent 4 5 6) • (rowColumnMul HexagonRowColumn456.rows_assocCAB HexagonRowColumn456.cols_right2)) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem rightFinal4_case_5_6_row_0_1_1 : (((-1 : ℤ) ^ (rightScaleBit 4 5 6).val * positiveScale (rightScaleExponent 4 5 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 6 5 : ℤ)) • HexagonAtoms456.outerLeftABC) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (negativeScale (rightScaleExponent 4 5 6) • (rowColumnMul HexagonRowColumn456.rows_assocCAB HexagonRowColumn456.cols_right2)) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem rightFinal4_case_5_6_row_1_0_0 : (((-1 : ℤ) ^ (rightScaleBit 4 5 6).val * positiveScale (rightScaleExponent 4 5 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 6 5 : ℤ)) • HexagonAtoms456.outerLeftABC) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (negativeScale (rightScaleExponent 4 5 6) • (rowColumnMul HexagonRowColumn456.rows_assocCAB HexagonRowColumn456.cols_right2)) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem rightFinal4_case_5_6_row_1_0_1 : (((-1 : ℤ) ^ (rightScaleBit 4 5 6).val * positiveScale (rightScaleExponent 4 5 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 6 5 : ℤ)) • HexagonAtoms456.outerLeftABC) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (negativeScale (rightScaleExponent 4 5 6) • (rowColumnMul HexagonRowColumn456.rows_assocCAB HexagonRowColumn456.cols_right2)) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem rightFinal4_case_5_6_row_1_1_0 : (((-1 : ℤ) ^ (rightScaleBit 4 5 6).val * positiveScale (rightScaleExponent 4 5 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 6 5 : ℤ)) • HexagonAtoms456.outerLeftABC) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (negativeScale (rightScaleExponent 4 5 6) • (rowColumnMul HexagonRowColumn456.rows_assocCAB HexagonRowColumn456.cols_right2)) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem rightFinal4_case_5_6_row_1_1_1 : (((-1 : ℤ) ^ (rightScaleBit 4 5 6).val * positiveScale (rightScaleExponent 4 5 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 6 5 : ℤ)) • HexagonAtoms456.outerLeftABC) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (negativeScale (rightScaleExponent 4 5 6) • (rowColumnMul HexagonRowColumn456.rows_assocCAB HexagonRowColumn456.cols_right2)) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem rightFinal4_case_5_6_row_2_0_0 : (((-1 : ℤ) ^ (rightScaleBit 4 5 6).val * positiveScale (rightScaleExponent 4 5 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 6 5 : ℤ)) • HexagonAtoms456.outerLeftABC) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (negativeScale (rightScaleExponent 4 5 6) • (rowColumnMul HexagonRowColumn456.rows_assocCAB HexagonRowColumn456.cols_right2)) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem rightFinal4_case_5_6_row_2_0_1 : (((-1 : ℤ) ^ (rightScaleBit 4 5 6).val * positiveScale (rightScaleExponent 4 5 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 6 5 : ℤ)) • HexagonAtoms456.outerLeftABC) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (negativeScale (rightScaleExponent 4 5 6) • (rowColumnMul HexagonRowColumn456.rows_assocCAB HexagonRowColumn456.cols_right2)) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem rightFinal4_case_5_6_row_2_1_0 : (((-1 : ℤ) ^ (rightScaleBit 4 5 6).val * positiveScale (rightScaleExponent 4 5 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 6 5 : ℤ)) • HexagonAtoms456.outerLeftABC) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (negativeScale (rightScaleExponent 4 5 6) • (rowColumnMul HexagonRowColumn456.rows_assocCAB HexagonRowColumn456.cols_right2)) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem rightFinal4_case_5_6_row_2_1_1 : (((-1 : ℤ) ^ (rightScaleBit 4 5 6).val * positiveScale (rightScaleExponent 4 5 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 6 5 : ℤ)) • HexagonAtoms456.outerLeftABC) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (negativeScale (rightScaleExponent 4 5 6) • (rowColumnMul HexagonRowColumn456.rows_assocCAB HexagonRowColumn456.cols_right2)) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem rightFinal4_case_5_6_row_3_0_0 : (((-1 : ℤ) ^ (rightScaleBit 4 5 6).val * positiveScale (rightScaleExponent 4 5 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 6 5 : ℤ)) • HexagonAtoms456.outerLeftABC) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (negativeScale (rightScaleExponent 4 5 6) • (rowColumnMul HexagonRowColumn456.rows_assocCAB HexagonRowColumn456.cols_right2)) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem rightFinal4_case_5_6_row_3_0_1 : (((-1 : ℤ) ^ (rightScaleBit 4 5 6).val * positiveScale (rightScaleExponent 4 5 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 6 5 : ℤ)) • HexagonAtoms456.outerLeftABC) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (negativeScale (rightScaleExponent 4 5 6) • (rowColumnMul HexagonRowColumn456.rows_assocCAB HexagonRowColumn456.cols_right2)) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem rightFinal4_case_5_6_row_3_1_0 : (((-1 : ℤ) ^ (rightScaleBit 4 5 6).val * positiveScale (rightScaleExponent 4 5 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 6 5 : ℤ)) • HexagonAtoms456.outerLeftABC) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (negativeScale (rightScaleExponent 4 5 6) • (rowColumnMul HexagonRowColumn456.rows_assocCAB HexagonRowColumn456.cols_right2)) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem rightFinal4_case_5_6_row_3_1_1 : (((-1 : ℤ) ^ (rightScaleBit 4 5 6).val * positiveScale (rightScaleExponent 4 5 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 6 5 : ℤ)) • HexagonAtoms456.outerLeftABC) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (negativeScale (rightScaleExponent 4 5 6) • (rowColumnMul HexagonRowColumn456.rows_assocCAB HexagonRowColumn456.cols_right2)) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 2)
  decide +kernel

private theorem rightFinal4_case_5_6_checked : ((-1 : ℤ) ^ (rightScaleBit 4 5 6).val * positiveScale (rightScaleExponent 4 5 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 6 5 : ℤ)) • HexagonAtoms456.outerLeftABC = negativeScale (rightScaleExponent 4 5 6) • (rowColumnMul HexagonRowColumn456.rows_assocCAB HexagonRowColumn456.cols_right2) := by
  funext r
  fin_cases r
  · exact rightFinal4_case_5_6_row_0_0_0
  · exact rightFinal4_case_5_6_row_0_0_1
  · exact rightFinal4_case_5_6_row_0_1_0
  · exact rightFinal4_case_5_6_row_0_1_1
  · exact rightFinal4_case_5_6_row_1_0_0
  · exact rightFinal4_case_5_6_row_1_0_1
  · exact rightFinal4_case_5_6_row_1_1_0
  · exact rightFinal4_case_5_6_row_1_1_1
  · exact rightFinal4_case_5_6_row_2_0_0
  · exact rightFinal4_case_5_6_row_2_0_1
  · exact rightFinal4_case_5_6_row_2_1_0
  · exact rightFinal4_case_5_6_row_2_1_1
  · exact rightFinal4_case_5_6_row_3_0_0
  · exact rightFinal4_case_5_6_row_3_0_1
  · exact rightFinal4_case_5_6_row_3_1_0
  · exact rightFinal4_case_5_6_row_3_1_1

set_option backward.isDefEq.respectTransparency false in
theorem rightFinal4_case_5_6 : ((-1 : ℤ) ^ (rightScaleBit 4 5 6).val * positiveScale (rightScaleExponent 4 5 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 6 5 : ℤ)) • outerLeftZ 4 5 6 = negativeScale (rightScaleExponent 4 5 6) • (associatorZ 6 4 5 * right2Middle4 5 6) := by
  simpa only [HexagonAtoms456.assocABC_eq,
    HexagonAtoms456.outerABC_eq,
    HexagonAtoms456.assocBAC_eq,
    HexagonAtoms456.innerABC_eq,
    HexagonAtoms456.innerRightABC_eq,
    HexagonAtoms456.inverseACB_eq,
    HexagonAtoms456.innerACB_eq,
    HexagonAtoms456.assocBCA_eq,
    HexagonAtoms456.innerRightBAC_eq,
    HexagonAtoms456.assocCAB_eq,
    HexagonAtoms456.outerLeftABC_eq,
    HexagonRowColumn456.product0_eq,
    HexagonRowColumn456.product1_eq,
    HexagonRowColumn456.product2_eq,
    HexagonRowColumn456.product3_eq,
    HexagonRowColumn456.product4_eq,
    HexagonRowColumn456.product5_eq,
    HexagonRowColumn456.product6_eq,
    HexagonRowColumn456.product7_eq] using rightFinal4_case_5_6_checked

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonCases4
