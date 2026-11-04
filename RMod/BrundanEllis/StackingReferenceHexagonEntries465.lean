import RMod.BrundanEllis.StackingReferenceHexagonMiddle4
import RMod.BrundanEllis.StackingReferenceSparseMatrixCheck
import RMod.BrundanEllis.StackingReferenceHexagonAtoms465
import RMod.BrundanEllis.StackingReferenceHexagonRowColumn465

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

private theorem left0Middle4_eq_case_6_5_row_0_0_0 : (left0Middle4 6 5) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (HexagonAtoms465.assocABC) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle4_eq_case_6_5_row_0_0_1 : (left0Middle4 6 5) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (HexagonAtoms465.assocABC) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle4_eq_case_6_5_row_0_1_0 : (left0Middle4 6 5) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (HexagonAtoms465.assocABC) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle4_eq_case_6_5_row_0_1_1 : (left0Middle4 6 5) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (HexagonAtoms465.assocABC) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle4_eq_case_6_5_row_0_2_0 : (left0Middle4 6 5) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (HexagonAtoms465.assocABC) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle4_eq_case_6_5_row_0_2_1 : (left0Middle4 6 5) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (HexagonAtoms465.assocABC) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle4_eq_case_6_5_row_0_3_0 : (left0Middle4 6 5) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (HexagonAtoms465.assocABC) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle4_eq_case_6_5_row_0_3_1 : (left0Middle4 6 5) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (HexagonAtoms465.assocABC) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle4_eq_case_6_5_row_1_0_0 : (left0Middle4 6 5) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (HexagonAtoms465.assocABC) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle4_eq_case_6_5_row_1_0_1 : (left0Middle4 6 5) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (HexagonAtoms465.assocABC) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle4_eq_case_6_5_row_1_1_0 : (left0Middle4 6 5) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (HexagonAtoms465.assocABC) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle4_eq_case_6_5_row_1_1_1 : (left0Middle4 6 5) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (HexagonAtoms465.assocABC) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle4_eq_case_6_5_row_1_2_0 : (left0Middle4 6 5) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (HexagonAtoms465.assocABC) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle4_eq_case_6_5_row_1_2_1 : (left0Middle4 6 5) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (HexagonAtoms465.assocABC) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle4_eq_case_6_5_row_1_3_0 : (left0Middle4 6 5) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (HexagonAtoms465.assocABC) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle4_eq_case_6_5_row_1_3_1 : (left0Middle4 6 5) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (HexagonAtoms465.assocABC) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left0Middle4_eq_case_6_5_checked : left0Middle4 6 5 = HexagonAtoms465.assocABC := by
  funext r
  fin_cases r
  · exact left0Middle4_eq_case_6_5_row_0_0_0
  · exact left0Middle4_eq_case_6_5_row_0_0_1
  · exact left0Middle4_eq_case_6_5_row_0_1_0
  · exact left0Middle4_eq_case_6_5_row_0_1_1
  · exact left0Middle4_eq_case_6_5_row_0_2_0
  · exact left0Middle4_eq_case_6_5_row_0_2_1
  · exact left0Middle4_eq_case_6_5_row_0_3_0
  · exact left0Middle4_eq_case_6_5_row_0_3_1
  · exact left0Middle4_eq_case_6_5_row_1_0_0
  · exact left0Middle4_eq_case_6_5_row_1_0_1
  · exact left0Middle4_eq_case_6_5_row_1_1_0
  · exact left0Middle4_eq_case_6_5_row_1_1_1
  · exact left0Middle4_eq_case_6_5_row_1_2_0
  · exact left0Middle4_eq_case_6_5_row_1_2_1
  · exact left0Middle4_eq_case_6_5_row_1_3_0
  · exact left0Middle4_eq_case_6_5_row_1_3_1

set_option backward.isDefEq.respectTransparency false in
theorem left0Middle4_eq_case_6_5 : left0Middle4 6 5 = outerRightZ 4 6 5 * associatorZ 4 6 5 := by
  simpa only [HexagonAtoms465.assocABC_eq,
    HexagonAtoms465.outerABC_eq,
    HexagonAtoms465.assocBAC_eq,
    HexagonAtoms465.innerABC_eq,
    HexagonAtoms465.innerRightABC_eq,
    HexagonAtoms465.inverseACB_eq,
    HexagonAtoms465.innerACB_eq,
    HexagonAtoms465.assocBCA_eq,
    HexagonAtoms465.innerRightBAC_eq,
    HexagonAtoms465.assocCAB_eq,
    HexagonAtoms465.outerLeftABC_eq,
    HexagonRowColumn465.product0_eq,
    HexagonRowColumn465.product1_eq,
    HexagonRowColumn465.product2_eq,
    HexagonRowColumn465.product3_eq,
    HexagonRowColumn465.product4_eq,
    HexagonRowColumn465.product5_eq,
    HexagonRowColumn465.product6_eq,
    HexagonRowColumn465.product7_eq] using left0Middle4_eq_case_6_5_checked

private theorem left1Middle4_eq_case_6_5_row_0_0_0 : (left1Middle4 6 5) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (HexagonAtoms465.assocBAC) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle4_eq_case_6_5_row_0_0_1 : (left1Middle4 6 5) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (HexagonAtoms465.assocBAC) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle4_eq_case_6_5_row_0_1_0 : (left1Middle4 6 5) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (HexagonAtoms465.assocBAC) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle4_eq_case_6_5_row_0_1_1 : (left1Middle4 6 5) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (HexagonAtoms465.assocBAC) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle4_eq_case_6_5_row_1_0_0 : (left1Middle4 6 5) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (HexagonAtoms465.assocBAC) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle4_eq_case_6_5_row_1_0_1 : (left1Middle4 6 5) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (HexagonAtoms465.assocBAC) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle4_eq_case_6_5_row_1_1_0 : (left1Middle4 6 5) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (HexagonAtoms465.assocBAC) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle4_eq_case_6_5_row_1_1_1 : (left1Middle4 6 5) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (HexagonAtoms465.assocBAC) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle4_eq_case_6_5_row_2_0_0 : (left1Middle4 6 5) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (HexagonAtoms465.assocBAC) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle4_eq_case_6_5_row_2_0_1 : (left1Middle4 6 5) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (HexagonAtoms465.assocBAC) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle4_eq_case_6_5_row_2_1_0 : (left1Middle4 6 5) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (HexagonAtoms465.assocBAC) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle4_eq_case_6_5_row_2_1_1 : (left1Middle4 6 5) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (HexagonAtoms465.assocBAC) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle4_eq_case_6_5_row_3_0_0 : (left1Middle4 6 5) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (HexagonAtoms465.assocBAC) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle4_eq_case_6_5_row_3_0_1 : (left1Middle4 6 5) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (HexagonAtoms465.assocBAC) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle4_eq_case_6_5_row_3_1_0 : (left1Middle4 6 5) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (HexagonAtoms465.assocBAC) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle4_eq_case_6_5_row_3_1_1 : (left1Middle4 6 5) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (HexagonAtoms465.assocBAC) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem left1Middle4_eq_case_6_5_checked : left1Middle4 6 5 = HexagonAtoms465.assocBAC := by
  funext r
  fin_cases r
  · exact left1Middle4_eq_case_6_5_row_0_0_0
  · exact left1Middle4_eq_case_6_5_row_0_0_1
  · exact left1Middle4_eq_case_6_5_row_0_1_0
  · exact left1Middle4_eq_case_6_5_row_0_1_1
  · exact left1Middle4_eq_case_6_5_row_1_0_0
  · exact left1Middle4_eq_case_6_5_row_1_0_1
  · exact left1Middle4_eq_case_6_5_row_1_1_0
  · exact left1Middle4_eq_case_6_5_row_1_1_1
  · exact left1Middle4_eq_case_6_5_row_2_0_0
  · exact left1Middle4_eq_case_6_5_row_2_0_1
  · exact left1Middle4_eq_case_6_5_row_2_1_0
  · exact left1Middle4_eq_case_6_5_row_2_1_1
  · exact left1Middle4_eq_case_6_5_row_3_0_0
  · exact left1Middle4_eq_case_6_5_row_3_0_1
  · exact left1Middle4_eq_case_6_5_row_3_1_0
  · exact left1Middle4_eq_case_6_5_row_3_1_1

set_option backward.isDefEq.respectTransparency false in
theorem left1Middle4_eq_case_6_5 : left1Middle4 6 5 = associatorZ 6 4 5 * innerLeftZ 4 6 5 := by
  simpa only [HexagonAtoms465.assocABC_eq,
    HexagonAtoms465.outerABC_eq,
    HexagonAtoms465.assocBAC_eq,
    HexagonAtoms465.innerABC_eq,
    HexagonAtoms465.innerRightABC_eq,
    HexagonAtoms465.inverseACB_eq,
    HexagonAtoms465.innerACB_eq,
    HexagonAtoms465.assocBCA_eq,
    HexagonAtoms465.innerRightBAC_eq,
    HexagonAtoms465.assocCAB_eq,
    HexagonAtoms465.outerLeftABC_eq,
    HexagonRowColumn465.product0_eq,
    HexagonRowColumn465.product1_eq,
    HexagonRowColumn465.product2_eq,
    HexagonRowColumn465.product3_eq,
    HexagonRowColumn465.product4_eq,
    HexagonRowColumn465.product5_eq,
    HexagonRowColumn465.product6_eq,
    HexagonRowColumn465.product7_eq] using left1Middle4_eq_case_6_5_checked

private theorem right0Middle4_eq_case_6_5_row_0_0_0 : (right0Middle4 6 5) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (HexagonAtoms465.assocABC) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle4_eq_case_6_5_row_0_0_1 : (right0Middle4 6 5) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (HexagonAtoms465.assocABC) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle4_eq_case_6_5_row_0_1_0 : (right0Middle4 6 5) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (HexagonAtoms465.assocABC) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle4_eq_case_6_5_row_0_1_1 : (right0Middle4 6 5) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (HexagonAtoms465.assocABC) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle4_eq_case_6_5_row_0_2_0 : (right0Middle4 6 5) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (HexagonAtoms465.assocABC) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle4_eq_case_6_5_row_0_2_1 : (right0Middle4 6 5) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (HexagonAtoms465.assocABC) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle4_eq_case_6_5_row_0_3_0 : (right0Middle4 6 5) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (HexagonAtoms465.assocABC) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle4_eq_case_6_5_row_0_3_1 : (right0Middle4 6 5) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (HexagonAtoms465.assocABC) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle4_eq_case_6_5_row_1_0_0 : (right0Middle4 6 5) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (HexagonAtoms465.assocABC) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle4_eq_case_6_5_row_1_0_1 : (right0Middle4 6 5) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (HexagonAtoms465.assocABC) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle4_eq_case_6_5_row_1_1_0 : (right0Middle4 6 5) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (HexagonAtoms465.assocABC) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle4_eq_case_6_5_row_1_1_1 : (right0Middle4 6 5) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (HexagonAtoms465.assocABC) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle4_eq_case_6_5_row_1_2_0 : (right0Middle4 6 5) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (HexagonAtoms465.assocABC) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle4_eq_case_6_5_row_1_2_1 : (right0Middle4 6 5) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (HexagonAtoms465.assocABC) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle4_eq_case_6_5_row_1_3_0 : (right0Middle4 6 5) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (HexagonAtoms465.assocABC) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle4_eq_case_6_5_row_1_3_1 : (right0Middle4 6 5) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (HexagonAtoms465.assocABC) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right0Middle4_eq_case_6_5_checked : right0Middle4 6 5 = HexagonAtoms465.assocABC := by
  funext r
  fin_cases r
  · exact right0Middle4_eq_case_6_5_row_0_0_0
  · exact right0Middle4_eq_case_6_5_row_0_0_1
  · exact right0Middle4_eq_case_6_5_row_0_1_0
  · exact right0Middle4_eq_case_6_5_row_0_1_1
  · exact right0Middle4_eq_case_6_5_row_0_2_0
  · exact right0Middle4_eq_case_6_5_row_0_2_1
  · exact right0Middle4_eq_case_6_5_row_0_3_0
  · exact right0Middle4_eq_case_6_5_row_0_3_1
  · exact right0Middle4_eq_case_6_5_row_1_0_0
  · exact right0Middle4_eq_case_6_5_row_1_0_1
  · exact right0Middle4_eq_case_6_5_row_1_1_0
  · exact right0Middle4_eq_case_6_5_row_1_1_1
  · exact right0Middle4_eq_case_6_5_row_1_2_0
  · exact right0Middle4_eq_case_6_5_row_1_2_1
  · exact right0Middle4_eq_case_6_5_row_1_3_0
  · exact right0Middle4_eq_case_6_5_row_1_3_1

set_option backward.isDefEq.respectTransparency false in
theorem right0Middle4_eq_case_6_5 : right0Middle4 6 5 = innerRightZ 4 6 5 * associatorZ 4 6 5 := by
  simpa only [HexagonAtoms465.assocABC_eq,
    HexagonAtoms465.outerABC_eq,
    HexagonAtoms465.assocBAC_eq,
    HexagonAtoms465.innerABC_eq,
    HexagonAtoms465.innerRightABC_eq,
    HexagonAtoms465.inverseACB_eq,
    HexagonAtoms465.innerACB_eq,
    HexagonAtoms465.assocBCA_eq,
    HexagonAtoms465.innerRightBAC_eq,
    HexagonAtoms465.assocCAB_eq,
    HexagonAtoms465.outerLeftABC_eq,
    HexagonRowColumn465.product0_eq,
    HexagonRowColumn465.product1_eq,
    HexagonRowColumn465.product2_eq,
    HexagonRowColumn465.product3_eq,
    HexagonRowColumn465.product4_eq,
    HexagonRowColumn465.product5_eq,
    HexagonRowColumn465.product6_eq,
    HexagonRowColumn465.product7_eq] using right0Middle4_eq_case_6_5_checked

private theorem right1Middle4_eq_case_6_5_row_0_0_0 : (right1Middle4 6 5) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn465.rows_inverseACB HexagonRowColumn465.cols_right0) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle4_eq_case_6_5_row_0_0_1 : (right1Middle4 6 5) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn465.rows_inverseACB HexagonRowColumn465.cols_right0) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle4_eq_case_6_5_row_0_1_0 : (right1Middle4 6 5) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn465.rows_inverseACB HexagonRowColumn465.cols_right0) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle4_eq_case_6_5_row_0_1_1 : (right1Middle4 6 5) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn465.rows_inverseACB HexagonRowColumn465.cols_right0) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle4_eq_case_6_5_row_1_0_0 : (right1Middle4 6 5) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn465.rows_inverseACB HexagonRowColumn465.cols_right0) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle4_eq_case_6_5_row_1_0_1 : (right1Middle4 6 5) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn465.rows_inverseACB HexagonRowColumn465.cols_right0) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle4_eq_case_6_5_row_1_1_0 : (right1Middle4 6 5) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn465.rows_inverseACB HexagonRowColumn465.cols_right0) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle4_eq_case_6_5_row_1_1_1 : (right1Middle4 6 5) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn465.rows_inverseACB HexagonRowColumn465.cols_right0) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle4_eq_case_6_5_row_2_0_0 : (right1Middle4 6 5) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn465.rows_inverseACB HexagonRowColumn465.cols_right0) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle4_eq_case_6_5_row_2_0_1 : (right1Middle4 6 5) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn465.rows_inverseACB HexagonRowColumn465.cols_right0) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle4_eq_case_6_5_row_2_1_0 : (right1Middle4 6 5) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn465.rows_inverseACB HexagonRowColumn465.cols_right0) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle4_eq_case_6_5_row_2_1_1 : (right1Middle4 6 5) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn465.rows_inverseACB HexagonRowColumn465.cols_right0) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle4_eq_case_6_5_row_3_0_0 : (right1Middle4 6 5) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn465.rows_inverseACB HexagonRowColumn465.cols_right0) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle4_eq_case_6_5_row_3_0_1 : (right1Middle4 6 5) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn465.rows_inverseACB HexagonRowColumn465.cols_right0) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle4_eq_case_6_5_row_3_1_0 : (right1Middle4 6 5) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn465.rows_inverseACB HexagonRowColumn465.cols_right0) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle4_eq_case_6_5_row_3_1_1 : (right1Middle4 6 5) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn465.rows_inverseACB HexagonRowColumn465.cols_right0) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right1Middle4_eq_case_6_5_checked : right1Middle4 6 5 = rowColumnMul HexagonRowColumn465.rows_inverseACB HexagonRowColumn465.cols_right0 := by
  funext r
  fin_cases r
  · exact right1Middle4_eq_case_6_5_row_0_0_0
  · exact right1Middle4_eq_case_6_5_row_0_0_1
  · exact right1Middle4_eq_case_6_5_row_0_1_0
  · exact right1Middle4_eq_case_6_5_row_0_1_1
  · exact right1Middle4_eq_case_6_5_row_1_0_0
  · exact right1Middle4_eq_case_6_5_row_1_0_1
  · exact right1Middle4_eq_case_6_5_row_1_1_0
  · exact right1Middle4_eq_case_6_5_row_1_1_1
  · exact right1Middle4_eq_case_6_5_row_2_0_0
  · exact right1Middle4_eq_case_6_5_row_2_0_1
  · exact right1Middle4_eq_case_6_5_row_2_1_0
  · exact right1Middle4_eq_case_6_5_row_2_1_1
  · exact right1Middle4_eq_case_6_5_row_3_0_0
  · exact right1Middle4_eq_case_6_5_row_3_0_1
  · exact right1Middle4_eq_case_6_5_row_3_1_0
  · exact right1Middle4_eq_case_6_5_row_3_1_1

set_option backward.isDefEq.respectTransparency false in
theorem right1Middle4_eq_case_6_5 : right1Middle4 6 5 = associatorInverseZ 4 5 6 * right0Middle4 6 5 := by
  simpa only [HexagonAtoms465.assocABC_eq,
    HexagonAtoms465.outerABC_eq,
    HexagonAtoms465.assocBAC_eq,
    HexagonAtoms465.innerABC_eq,
    HexagonAtoms465.innerRightABC_eq,
    HexagonAtoms465.inverseACB_eq,
    HexagonAtoms465.innerACB_eq,
    HexagonAtoms465.assocBCA_eq,
    HexagonAtoms465.innerRightBAC_eq,
    HexagonAtoms465.assocCAB_eq,
    HexagonAtoms465.outerLeftABC_eq,
    HexagonRowColumn465.product0_eq,
    HexagonRowColumn465.product1_eq,
    HexagonRowColumn465.product2_eq,
    HexagonRowColumn465.product3_eq,
    HexagonRowColumn465.product4_eq,
    HexagonRowColumn465.product5_eq,
    HexagonRowColumn465.product6_eq,
    HexagonRowColumn465.product7_eq] using right1Middle4_eq_case_6_5_checked

private theorem right2Middle4_eq_case_6_5_row_0_0_0 : (right2Middle4 6 5) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (right1Middle4 6 5) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle4_eq_case_6_5_row_0_0_1 : (right2Middle4 6 5) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (right1Middle4 6 5) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle4_eq_case_6_5_row_0_1_0 : (right2Middle4 6 5) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (right1Middle4 6 5) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle4_eq_case_6_5_row_0_1_1 : (right2Middle4 6 5) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (right1Middle4 6 5) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle4_eq_case_6_5_row_1_0_0 : (right2Middle4 6 5) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (right1Middle4 6 5) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle4_eq_case_6_5_row_1_0_1 : (right2Middle4 6 5) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (right1Middle4 6 5) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle4_eq_case_6_5_row_1_1_0 : (right2Middle4 6 5) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (right1Middle4 6 5) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle4_eq_case_6_5_row_1_1_1 : (right2Middle4 6 5) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (right1Middle4 6 5) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle4_eq_case_6_5_row_2_0_0 : (right2Middle4 6 5) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (right1Middle4 6 5) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle4_eq_case_6_5_row_2_0_1 : (right2Middle4 6 5) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (right1Middle4 6 5) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle4_eq_case_6_5_row_2_1_0 : (right2Middle4 6 5) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (right1Middle4 6 5) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle4_eq_case_6_5_row_2_1_1 : (right2Middle4 6 5) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (right1Middle4 6 5) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle4_eq_case_6_5_row_3_0_0 : (right2Middle4 6 5) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (right1Middle4 6 5) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle4_eq_case_6_5_row_3_0_1 : (right2Middle4 6 5) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (right1Middle4 6 5) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle4_eq_case_6_5_row_3_1_0 : (right2Middle4 6 5) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (right1Middle4 6 5) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle4_eq_case_6_5_row_3_1_1 : (right2Middle4 6 5) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (right1Middle4 6 5) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem right2Middle4_eq_case_6_5_checked : right2Middle4 6 5 = right1Middle4 6 5 := by
  funext r
  fin_cases r
  · exact right2Middle4_eq_case_6_5_row_0_0_0
  · exact right2Middle4_eq_case_6_5_row_0_0_1
  · exact right2Middle4_eq_case_6_5_row_0_1_0
  · exact right2Middle4_eq_case_6_5_row_0_1_1
  · exact right2Middle4_eq_case_6_5_row_1_0_0
  · exact right2Middle4_eq_case_6_5_row_1_0_1
  · exact right2Middle4_eq_case_6_5_row_1_1_0
  · exact right2Middle4_eq_case_6_5_row_1_1_1
  · exact right2Middle4_eq_case_6_5_row_2_0_0
  · exact right2Middle4_eq_case_6_5_row_2_0_1
  · exact right2Middle4_eq_case_6_5_row_2_1_0
  · exact right2Middle4_eq_case_6_5_row_2_1_1
  · exact right2Middle4_eq_case_6_5_row_3_0_0
  · exact right2Middle4_eq_case_6_5_row_3_0_1
  · exact right2Middle4_eq_case_6_5_row_3_1_0
  · exact right2Middle4_eq_case_6_5_row_3_1_1

set_option backward.isDefEq.respectTransparency false in
theorem right2Middle4_eq_case_6_5 : right2Middle4 6 5 = innerLeftZ 4 5 6 * right1Middle4 6 5 := by
  simpa only [HexagonAtoms465.assocABC_eq,
    HexagonAtoms465.outerABC_eq,
    HexagonAtoms465.assocBAC_eq,
    HexagonAtoms465.innerABC_eq,
    HexagonAtoms465.innerRightABC_eq,
    HexagonAtoms465.inverseACB_eq,
    HexagonAtoms465.innerACB_eq,
    HexagonAtoms465.assocBCA_eq,
    HexagonAtoms465.innerRightBAC_eq,
    HexagonAtoms465.assocCAB_eq,
    HexagonAtoms465.outerLeftABC_eq,
    HexagonRowColumn465.product0_eq,
    HexagonRowColumn465.product1_eq,
    HexagonRowColumn465.product2_eq,
    HexagonRowColumn465.product3_eq,
    HexagonRowColumn465.product4_eq,
    HexagonRowColumn465.product5_eq,
    HexagonRowColumn465.product6_eq,
    HexagonRowColumn465.product7_eq] using right2Middle4_eq_case_6_5_checked

private theorem leftFinal4_case_6_5_row_0_0_0 : (((-1 : ℤ) ^ (leftScaleBit 4 6 5).val * positiveScale (leftScaleExponent 4 6 5)) •
      (rowColumnMul HexagonRowColumn465.rows_assocBCA HexagonRowColumn465.cols_left0)) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (negativeScale (leftScaleExponent 4 6 5) • (left1Middle4 6 5)) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal4_case_6_5_row_0_0_1 : (((-1 : ℤ) ^ (leftScaleBit 4 6 5).val * positiveScale (leftScaleExponent 4 6 5)) •
      (rowColumnMul HexagonRowColumn465.rows_assocBCA HexagonRowColumn465.cols_left0)) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (negativeScale (leftScaleExponent 4 6 5) • (left1Middle4 6 5)) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal4_case_6_5_row_0_1_0 : (((-1 : ℤ) ^ (leftScaleBit 4 6 5).val * positiveScale (leftScaleExponent 4 6 5)) •
      (rowColumnMul HexagonRowColumn465.rows_assocBCA HexagonRowColumn465.cols_left0)) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (negativeScale (leftScaleExponent 4 6 5) • (left1Middle4 6 5)) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal4_case_6_5_row_0_1_1 : (((-1 : ℤ) ^ (leftScaleBit 4 6 5).val * positiveScale (leftScaleExponent 4 6 5)) •
      (rowColumnMul HexagonRowColumn465.rows_assocBCA HexagonRowColumn465.cols_left0)) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (negativeScale (leftScaleExponent 4 6 5) • (left1Middle4 6 5)) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal4_case_6_5_row_1_0_0 : (((-1 : ℤ) ^ (leftScaleBit 4 6 5).val * positiveScale (leftScaleExponent 4 6 5)) •
      (rowColumnMul HexagonRowColumn465.rows_assocBCA HexagonRowColumn465.cols_left0)) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (negativeScale (leftScaleExponent 4 6 5) • (left1Middle4 6 5)) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal4_case_6_5_row_1_0_1 : (((-1 : ℤ) ^ (leftScaleBit 4 6 5).val * positiveScale (leftScaleExponent 4 6 5)) •
      (rowColumnMul HexagonRowColumn465.rows_assocBCA HexagonRowColumn465.cols_left0)) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (negativeScale (leftScaleExponent 4 6 5) • (left1Middle4 6 5)) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal4_case_6_5_row_1_1_0 : (((-1 : ℤ) ^ (leftScaleBit 4 6 5).val * positiveScale (leftScaleExponent 4 6 5)) •
      (rowColumnMul HexagonRowColumn465.rows_assocBCA HexagonRowColumn465.cols_left0)) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (negativeScale (leftScaleExponent 4 6 5) • (left1Middle4 6 5)) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal4_case_6_5_row_1_1_1 : (((-1 : ℤ) ^ (leftScaleBit 4 6 5).val * positiveScale (leftScaleExponent 4 6 5)) •
      (rowColumnMul HexagonRowColumn465.rows_assocBCA HexagonRowColumn465.cols_left0)) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (negativeScale (leftScaleExponent 4 6 5) • (left1Middle4 6 5)) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal4_case_6_5_row_2_0_0 : (((-1 : ℤ) ^ (leftScaleBit 4 6 5).val * positiveScale (leftScaleExponent 4 6 5)) •
      (rowColumnMul HexagonRowColumn465.rows_assocBCA HexagonRowColumn465.cols_left0)) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (negativeScale (leftScaleExponent 4 6 5) • (left1Middle4 6 5)) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal4_case_6_5_row_2_0_1 : (((-1 : ℤ) ^ (leftScaleBit 4 6 5).val * positiveScale (leftScaleExponent 4 6 5)) •
      (rowColumnMul HexagonRowColumn465.rows_assocBCA HexagonRowColumn465.cols_left0)) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (negativeScale (leftScaleExponent 4 6 5) • (left1Middle4 6 5)) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal4_case_6_5_row_2_1_0 : (((-1 : ℤ) ^ (leftScaleBit 4 6 5).val * positiveScale (leftScaleExponent 4 6 5)) •
      (rowColumnMul HexagonRowColumn465.rows_assocBCA HexagonRowColumn465.cols_left0)) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (negativeScale (leftScaleExponent 4 6 5) • (left1Middle4 6 5)) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal4_case_6_5_row_2_1_1 : (((-1 : ℤ) ^ (leftScaleBit 4 6 5).val * positiveScale (leftScaleExponent 4 6 5)) •
      (rowColumnMul HexagonRowColumn465.rows_assocBCA HexagonRowColumn465.cols_left0)) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (negativeScale (leftScaleExponent 4 6 5) • (left1Middle4 6 5)) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal4_case_6_5_row_3_0_0 : (((-1 : ℤ) ^ (leftScaleBit 4 6 5).val * positiveScale (leftScaleExponent 4 6 5)) •
      (rowColumnMul HexagonRowColumn465.rows_assocBCA HexagonRowColumn465.cols_left0)) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2)) = (negativeScale (leftScaleExponent 4 6 5) • (left1Middle4 6 5)) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal4_case_6_5_row_3_0_1 : (((-1 : ℤ) ^ (leftScaleBit 4 6 5).val * positiveScale (leftScaleExponent 4 6 5)) •
      (rowColumnMul HexagonRowColumn465.rows_assocBCA HexagonRowColumn465.cols_left0)) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2)) = (negativeScale (leftScaleExponent 4 6 5) • (left1Middle4 6 5)) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal4_case_6_5_row_3_1_0 : (((-1 : ℤ) ^ (leftScaleBit 4 6 5).val * positiveScale (leftScaleExponent 4 6 5)) •
      (rowColumnMul HexagonRowColumn465.rows_assocBCA HexagonRowColumn465.cols_left0)) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2)) = (negativeScale (leftScaleExponent 4 6 5) • (left1Middle4 6 5)) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal4_case_6_5_row_3_1_1 : (((-1 : ℤ) ^ (leftScaleBit 4 6 5).val * positiveScale (leftScaleExponent 4 6 5)) •
      (rowColumnMul HexagonRowColumn465.rows_assocBCA HexagonRowColumn465.cols_left0)) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2)) = (negativeScale (leftScaleExponent 4 6 5) • (left1Middle4 6 5)) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem leftFinal4_case_6_5_checked : ((-1 : ℤ) ^ (leftScaleBit 4 6 5).val * positiveScale (leftScaleExponent 4 6 5)) •
      (rowColumnMul HexagonRowColumn465.rows_assocBCA HexagonRowColumn465.cols_left0) = negativeScale (leftScaleExponent 4 6 5) • (left1Middle4 6 5) := by
  funext r
  fin_cases r
  · exact leftFinal4_case_6_5_row_0_0_0
  · exact leftFinal4_case_6_5_row_0_0_1
  · exact leftFinal4_case_6_5_row_0_1_0
  · exact leftFinal4_case_6_5_row_0_1_1
  · exact leftFinal4_case_6_5_row_1_0_0
  · exact leftFinal4_case_6_5_row_1_0_1
  · exact leftFinal4_case_6_5_row_1_1_0
  · exact leftFinal4_case_6_5_row_1_1_1
  · exact leftFinal4_case_6_5_row_2_0_0
  · exact leftFinal4_case_6_5_row_2_0_1
  · exact leftFinal4_case_6_5_row_2_1_0
  · exact leftFinal4_case_6_5_row_2_1_1
  · exact leftFinal4_case_6_5_row_3_0_0
  · exact leftFinal4_case_6_5_row_3_0_1
  · exact leftFinal4_case_6_5_row_3_1_0
  · exact leftFinal4_case_6_5_row_3_1_1

set_option backward.isDefEq.respectTransparency false in
theorem leftFinal4_case_6_5 : ((-1 : ℤ) ^ (leftScaleBit 4 6 5).val * positiveScale (leftScaleExponent 4 6 5)) •
      (associatorZ 6 5 4 * left0Middle4 6 5) = negativeScale (leftScaleExponent 4 6 5) • (innerRightZ 6 4 5 * left1Middle4 6 5) := by
  simpa only [HexagonAtoms465.assocABC_eq,
    HexagonAtoms465.outerABC_eq,
    HexagonAtoms465.assocBAC_eq,
    HexagonAtoms465.innerABC_eq,
    HexagonAtoms465.innerRightABC_eq,
    HexagonAtoms465.inverseACB_eq,
    HexagonAtoms465.innerACB_eq,
    HexagonAtoms465.assocBCA_eq,
    HexagonAtoms465.innerRightBAC_eq,
    HexagonAtoms465.assocCAB_eq,
    HexagonAtoms465.outerLeftABC_eq,
    HexagonRowColumn465.product0_eq,
    HexagonRowColumn465.product1_eq,
    HexagonRowColumn465.product2_eq,
    HexagonRowColumn465.product3_eq,
    HexagonRowColumn465.product4_eq,
    HexagonRowColumn465.product5_eq,
    HexagonRowColumn465.product6_eq,
    HexagonRowColumn465.product7_eq] using leftFinal4_case_6_5_checked

private theorem rightFinal4_case_6_5_row_0_0_0 : (((-1 : ℤ) ^ (rightScaleBit 4 6 5).val * positiveScale (rightScaleExponent 4 6 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 5 6 : ℤ)) • HexagonAtoms465.outerLeftABC) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (negativeScale (rightScaleExponent 4 6 5) • (rowColumnMul HexagonRowColumn465.rows_assocCAB HexagonRowColumn465.cols_right2)) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal4_case_6_5_row_0_0_1 : (((-1 : ℤ) ^ (rightScaleBit 4 6 5).val * positiveScale (rightScaleExponent 4 6 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 5 6 : ℤ)) • HexagonAtoms465.outerLeftABC) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (negativeScale (rightScaleExponent 4 6 5) • (rowColumnMul HexagonRowColumn465.rows_assocCAB HexagonRowColumn465.cols_right2)) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal4_case_6_5_row_0_1_0 : (((-1 : ℤ) ^ (rightScaleBit 4 6 5).val * positiveScale (rightScaleExponent 4 6 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 5 6 : ℤ)) • HexagonAtoms465.outerLeftABC) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (negativeScale (rightScaleExponent 4 6 5) • (rowColumnMul HexagonRowColumn465.rows_assocCAB HexagonRowColumn465.cols_right2)) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal4_case_6_5_row_0_1_1 : (((-1 : ℤ) ^ (rightScaleBit 4 6 5).val * positiveScale (rightScaleExponent 4 6 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 5 6 : ℤ)) • HexagonAtoms465.outerLeftABC) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (negativeScale (rightScaleExponent 4 6 5) • (rowColumnMul HexagonRowColumn465.rows_assocCAB HexagonRowColumn465.cols_right2)) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal4_case_6_5_row_0_2_0 : (((-1 : ℤ) ^ (rightScaleBit 4 6 5).val * positiveScale (rightScaleExponent 4 6 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 5 6 : ℤ)) • HexagonAtoms465.outerLeftABC) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (negativeScale (rightScaleExponent 4 6 5) • (rowColumnMul HexagonRowColumn465.rows_assocCAB HexagonRowColumn465.cols_right2)) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal4_case_6_5_row_0_2_1 : (((-1 : ℤ) ^ (rightScaleBit 4 6 5).val * positiveScale (rightScaleExponent 4 6 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 5 6 : ℤ)) • HexagonAtoms465.outerLeftABC) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (negativeScale (rightScaleExponent 4 6 5) • (rowColumnMul HexagonRowColumn465.rows_assocCAB HexagonRowColumn465.cols_right2)) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal4_case_6_5_row_0_3_0 : (((-1 : ℤ) ^ (rightScaleBit 4 6 5).val * positiveScale (rightScaleExponent 4 6 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 5 6 : ℤ)) • HexagonAtoms465.outerLeftABC) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (negativeScale (rightScaleExponent 4 6 5) • (rowColumnMul HexagonRowColumn465.rows_assocCAB HexagonRowColumn465.cols_right2)) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal4_case_6_5_row_0_3_1 : (((-1 : ℤ) ^ (rightScaleBit 4 6 5).val * positiveScale (rightScaleExponent 4 6 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 5 6 : ℤ)) • HexagonAtoms465.outerLeftABC) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (negativeScale (rightScaleExponent 4 6 5) • (rowColumnMul HexagonRowColumn465.rows_assocCAB HexagonRowColumn465.cols_right2)) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal4_case_6_5_row_1_0_0 : (((-1 : ℤ) ^ (rightScaleBit 4 6 5).val * positiveScale (rightScaleExponent 4 6 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 5 6 : ℤ)) • HexagonAtoms465.outerLeftABC) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (negativeScale (rightScaleExponent 4 6 5) • (rowColumnMul HexagonRowColumn465.rows_assocCAB HexagonRowColumn465.cols_right2)) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal4_case_6_5_row_1_0_1 : (((-1 : ℤ) ^ (rightScaleBit 4 6 5).val * positiveScale (rightScaleExponent 4 6 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 5 6 : ℤ)) • HexagonAtoms465.outerLeftABC) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (negativeScale (rightScaleExponent 4 6 5) • (rowColumnMul HexagonRowColumn465.rows_assocCAB HexagonRowColumn465.cols_right2)) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal4_case_6_5_row_1_1_0 : (((-1 : ℤ) ^ (rightScaleBit 4 6 5).val * positiveScale (rightScaleExponent 4 6 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 5 6 : ℤ)) • HexagonAtoms465.outerLeftABC) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (negativeScale (rightScaleExponent 4 6 5) • (rowColumnMul HexagonRowColumn465.rows_assocCAB HexagonRowColumn465.cols_right2)) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal4_case_6_5_row_1_1_1 : (((-1 : ℤ) ^ (rightScaleBit 4 6 5).val * positiveScale (rightScaleExponent 4 6 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 5 6 : ℤ)) • HexagonAtoms465.outerLeftABC) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (negativeScale (rightScaleExponent 4 6 5) • (rowColumnMul HexagonRowColumn465.rows_assocCAB HexagonRowColumn465.cols_right2)) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal4_case_6_5_row_1_2_0 : (((-1 : ℤ) ^ (rightScaleBit 4 6 5).val * positiveScale (rightScaleExponent 4 6 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 5 6 : ℤ)) • HexagonAtoms465.outerLeftABC) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (negativeScale (rightScaleExponent 4 6 5) • (rowColumnMul HexagonRowColumn465.rows_assocCAB HexagonRowColumn465.cols_right2)) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal4_case_6_5_row_1_2_1 : (((-1 : ℤ) ^ (rightScaleBit 4 6 5).val * positiveScale (rightScaleExponent 4 6 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 5 6 : ℤ)) • HexagonAtoms465.outerLeftABC) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (negativeScale (rightScaleExponent 4 6 5) • (rowColumnMul HexagonRowColumn465.rows_assocCAB HexagonRowColumn465.cols_right2)) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal4_case_6_5_row_1_3_0 : (((-1 : ℤ) ^ (rightScaleBit 4 6 5).val * positiveScale (rightScaleExponent 4 6 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 5 6 : ℤ)) • HexagonAtoms465.outerLeftABC) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (negativeScale (rightScaleExponent 4 6 5) • (rowColumnMul HexagonRowColumn465.rows_assocCAB HexagonRowColumn465.cols_right2)) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal4_case_6_5_row_1_3_1 : (((-1 : ℤ) ^ (rightScaleBit 4 6 5).val * positiveScale (rightScaleExponent 4 6 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 5 6 : ℤ)) • HexagonAtoms465.outerLeftABC) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (negativeScale (rightScaleExponent 4 6 5) • (rowColumnMul HexagonRowColumn465.rows_assocCAB HexagonRowColumn465.cols_right2)) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 2) (b := 4) (c := 2)
  decide +kernel

private theorem rightFinal4_case_6_5_checked : ((-1 : ℤ) ^ (rightScaleBit 4 6 5).val * positiveScale (rightScaleExponent 4 6 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 5 6 : ℤ)) • HexagonAtoms465.outerLeftABC = negativeScale (rightScaleExponent 4 6 5) • (rowColumnMul HexagonRowColumn465.rows_assocCAB HexagonRowColumn465.cols_right2) := by
  funext r
  fin_cases r
  · exact rightFinal4_case_6_5_row_0_0_0
  · exact rightFinal4_case_6_5_row_0_0_1
  · exact rightFinal4_case_6_5_row_0_1_0
  · exact rightFinal4_case_6_5_row_0_1_1
  · exact rightFinal4_case_6_5_row_0_2_0
  · exact rightFinal4_case_6_5_row_0_2_1
  · exact rightFinal4_case_6_5_row_0_3_0
  · exact rightFinal4_case_6_5_row_0_3_1
  · exact rightFinal4_case_6_5_row_1_0_0
  · exact rightFinal4_case_6_5_row_1_0_1
  · exact rightFinal4_case_6_5_row_1_1_0
  · exact rightFinal4_case_6_5_row_1_1_1
  · exact rightFinal4_case_6_5_row_1_2_0
  · exact rightFinal4_case_6_5_row_1_2_1
  · exact rightFinal4_case_6_5_row_1_3_0
  · exact rightFinal4_case_6_5_row_1_3_1

set_option backward.isDefEq.respectTransparency false in
theorem rightFinal4_case_6_5 : ((-1 : ℤ) ^ (rightScaleBit 4 6 5).val * positiveScale (rightScaleExponent 4 6 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 5 6 : ℤ)) • outerLeftZ 4 6 5 = negativeScale (rightScaleExponent 4 6 5) • (associatorZ 5 4 6 * right2Middle4 6 5) := by
  simpa only [HexagonAtoms465.assocABC_eq,
    HexagonAtoms465.outerABC_eq,
    HexagonAtoms465.assocBAC_eq,
    HexagonAtoms465.innerABC_eq,
    HexagonAtoms465.innerRightABC_eq,
    HexagonAtoms465.inverseACB_eq,
    HexagonAtoms465.innerACB_eq,
    HexagonAtoms465.assocBCA_eq,
    HexagonAtoms465.innerRightBAC_eq,
    HexagonAtoms465.assocCAB_eq,
    HexagonAtoms465.outerLeftABC_eq,
    HexagonRowColumn465.product0_eq,
    HexagonRowColumn465.product1_eq,
    HexagonRowColumn465.product2_eq,
    HexagonRowColumn465.product3_eq,
    HexagonRowColumn465.product4_eq,
    HexagonRowColumn465.product5_eq,
    HexagonRowColumn465.product6_eq,
    HexagonRowColumn465.product7_eq] using rightFinal4_case_6_5_checked

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonCases4
