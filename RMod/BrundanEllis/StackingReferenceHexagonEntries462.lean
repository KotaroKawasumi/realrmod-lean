import RMod.BrundanEllis.StackingReferenceHexagonMiddle4
import RMod.BrundanEllis.StackingReferenceSparseMatrixCheck
import RMod.BrundanEllis.StackingReferenceHexagonAtoms462
import RMod.BrundanEllis.StackingReferenceHexagonRowColumn462

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

private theorem left0Middle4_eq_case_6_2_row_0_0_0 : (left0Middle4 6 2) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms462.assocABC) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_6_2_row_0_0_1 : (left0Middle4 6 2) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms462.assocABC) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_6_2_row_0_0_2 : (left0Middle4 6 2) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms462.assocABC) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_6_2_row_0_0_3 : (left0Middle4 6 2) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms462.assocABC) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_6_2_row_1_0_0 : (left0Middle4 6 2) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms462.assocABC) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_6_2_row_1_0_1 : (left0Middle4 6 2) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms462.assocABC) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_6_2_row_1_0_2 : (left0Middle4 6 2) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms462.assocABC) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_6_2_row_1_0_3 : (left0Middle4 6 2) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms462.assocABC) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_6_2_row_2_0_0 : (left0Middle4 6 2) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms462.assocABC) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_6_2_row_2_0_1 : (left0Middle4 6 2) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms462.assocABC) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_6_2_row_2_0_2 : (left0Middle4 6 2) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms462.assocABC) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_6_2_row_2_0_3 : (left0Middle4 6 2) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms462.assocABC) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_6_2_row_3_0_0 : (left0Middle4 6 2) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms462.assocABC) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_6_2_row_3_0_1 : (left0Middle4 6 2) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms462.assocABC) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_6_2_row_3_0_2 : (left0Middle4 6 2) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms462.assocABC) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_6_2_row_3_0_3 : (left0Middle4 6 2) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms462.assocABC) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_6_2_checked : left0Middle4 6 2 = HexagonAtoms462.assocABC := by
  funext r
  fin_cases r
  · exact left0Middle4_eq_case_6_2_row_0_0_0
  · exact left0Middle4_eq_case_6_2_row_0_0_1
  · exact left0Middle4_eq_case_6_2_row_0_0_2
  · exact left0Middle4_eq_case_6_2_row_0_0_3
  · exact left0Middle4_eq_case_6_2_row_1_0_0
  · exact left0Middle4_eq_case_6_2_row_1_0_1
  · exact left0Middle4_eq_case_6_2_row_1_0_2
  · exact left0Middle4_eq_case_6_2_row_1_0_3
  · exact left0Middle4_eq_case_6_2_row_2_0_0
  · exact left0Middle4_eq_case_6_2_row_2_0_1
  · exact left0Middle4_eq_case_6_2_row_2_0_2
  · exact left0Middle4_eq_case_6_2_row_2_0_3
  · exact left0Middle4_eq_case_6_2_row_3_0_0
  · exact left0Middle4_eq_case_6_2_row_3_0_1
  · exact left0Middle4_eq_case_6_2_row_3_0_2
  · exact left0Middle4_eq_case_6_2_row_3_0_3

set_option backward.isDefEq.respectTransparency false in
theorem left0Middle4_eq_case_6_2 : left0Middle4 6 2 = outerRightZ 4 6 2 * associatorZ 4 6 2 := by
  simpa only [HexagonAtoms462.assocABC_eq,
    HexagonAtoms462.outerABC_eq,
    HexagonAtoms462.assocBAC_eq,
    HexagonAtoms462.innerABC_eq,
    HexagonAtoms462.innerRightABC_eq,
    HexagonAtoms462.inverseACB_eq,
    HexagonAtoms462.innerACB_eq,
    HexagonAtoms462.assocBCA_eq,
    HexagonAtoms462.innerRightBAC_eq,
    HexagonAtoms462.assocCAB_eq,
    HexagonAtoms462.outerLeftABC_eq,
    HexagonRowColumn462.product0_eq,
    HexagonRowColumn462.product1_eq,
    HexagonRowColumn462.product2_eq,
    HexagonRowColumn462.product3_eq,
    HexagonRowColumn462.product4_eq,
    HexagonRowColumn462.product5_eq,
    HexagonRowColumn462.product6_eq,
    HexagonRowColumn462.product7_eq] using left0Middle4_eq_case_6_2_checked

private theorem left1Middle4_eq_case_6_2_row_0_0_0 : (left1Middle4 6 2) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms462.assocBAC) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_6_2_row_0_0_1 : (left1Middle4 6 2) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms462.assocBAC) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_6_2_row_0_0_2 : (left1Middle4 6 2) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms462.assocBAC) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_6_2_row_0_0_3 : (left1Middle4 6 2) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms462.assocBAC) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_6_2_row_0_1_0 : (left1Middle4 6 2) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms462.assocBAC) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_6_2_row_0_1_1 : (left1Middle4 6 2) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms462.assocBAC) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_6_2_row_0_1_2 : (left1Middle4 6 2) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms462.assocBAC) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_6_2_row_0_1_3 : (left1Middle4 6 2) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms462.assocBAC) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_6_2_row_1_0_0 : (left1Middle4 6 2) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms462.assocBAC) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_6_2_row_1_0_1 : (left1Middle4 6 2) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms462.assocBAC) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_6_2_row_1_0_2 : (left1Middle4 6 2) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms462.assocBAC) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_6_2_row_1_0_3 : (left1Middle4 6 2) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms462.assocBAC) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_6_2_row_1_1_0 : (left1Middle4 6 2) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms462.assocBAC) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_6_2_row_1_1_1 : (left1Middle4 6 2) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms462.assocBAC) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_6_2_row_1_1_2 : (left1Middle4 6 2) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms462.assocBAC) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_6_2_row_1_1_3 : (left1Middle4 6 2) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms462.assocBAC) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_6_2_checked : left1Middle4 6 2 = HexagonAtoms462.assocBAC := by
  funext r
  fin_cases r
  · exact left1Middle4_eq_case_6_2_row_0_0_0
  · exact left1Middle4_eq_case_6_2_row_0_0_1
  · exact left1Middle4_eq_case_6_2_row_0_0_2
  · exact left1Middle4_eq_case_6_2_row_0_0_3
  · exact left1Middle4_eq_case_6_2_row_0_1_0
  · exact left1Middle4_eq_case_6_2_row_0_1_1
  · exact left1Middle4_eq_case_6_2_row_0_1_2
  · exact left1Middle4_eq_case_6_2_row_0_1_3
  · exact left1Middle4_eq_case_6_2_row_1_0_0
  · exact left1Middle4_eq_case_6_2_row_1_0_1
  · exact left1Middle4_eq_case_6_2_row_1_0_2
  · exact left1Middle4_eq_case_6_2_row_1_0_3
  · exact left1Middle4_eq_case_6_2_row_1_1_0
  · exact left1Middle4_eq_case_6_2_row_1_1_1
  · exact left1Middle4_eq_case_6_2_row_1_1_2
  · exact left1Middle4_eq_case_6_2_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem left1Middle4_eq_case_6_2 : left1Middle4 6 2 = associatorZ 6 4 2 * innerLeftZ 4 6 2 := by
  simpa only [HexagonAtoms462.assocABC_eq,
    HexagonAtoms462.outerABC_eq,
    HexagonAtoms462.assocBAC_eq,
    HexagonAtoms462.innerABC_eq,
    HexagonAtoms462.innerRightABC_eq,
    HexagonAtoms462.inverseACB_eq,
    HexagonAtoms462.innerACB_eq,
    HexagonAtoms462.assocBCA_eq,
    HexagonAtoms462.innerRightBAC_eq,
    HexagonAtoms462.assocCAB_eq,
    HexagonAtoms462.outerLeftABC_eq,
    HexagonRowColumn462.product0_eq,
    HexagonRowColumn462.product1_eq,
    HexagonRowColumn462.product2_eq,
    HexagonRowColumn462.product3_eq,
    HexagonRowColumn462.product4_eq,
    HexagonRowColumn462.product5_eq,
    HexagonRowColumn462.product6_eq,
    HexagonRowColumn462.product7_eq] using left1Middle4_eq_case_6_2_checked

private theorem right0Middle4_eq_case_6_2_row_0_0_0 : (right0Middle4 6 2) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms462.assocABC) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_6_2_row_0_0_1 : (right0Middle4 6 2) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms462.assocABC) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_6_2_row_0_0_2 : (right0Middle4 6 2) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms462.assocABC) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_6_2_row_0_0_3 : (right0Middle4 6 2) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms462.assocABC) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_6_2_row_1_0_0 : (right0Middle4 6 2) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms462.assocABC) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_6_2_row_1_0_1 : (right0Middle4 6 2) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms462.assocABC) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_6_2_row_1_0_2 : (right0Middle4 6 2) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms462.assocABC) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_6_2_row_1_0_3 : (right0Middle4 6 2) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms462.assocABC) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_6_2_row_2_0_0 : (right0Middle4 6 2) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms462.assocABC) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_6_2_row_2_0_1 : (right0Middle4 6 2) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms462.assocABC) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_6_2_row_2_0_2 : (right0Middle4 6 2) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms462.assocABC) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_6_2_row_2_0_3 : (right0Middle4 6 2) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms462.assocABC) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_6_2_row_3_0_0 : (right0Middle4 6 2) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms462.assocABC) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_6_2_row_3_0_1 : (right0Middle4 6 2) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms462.assocABC) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_6_2_row_3_0_2 : (right0Middle4 6 2) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms462.assocABC) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_6_2_row_3_0_3 : (right0Middle4 6 2) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms462.assocABC) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_6_2_checked : right0Middle4 6 2 = HexagonAtoms462.assocABC := by
  funext r
  fin_cases r
  · exact right0Middle4_eq_case_6_2_row_0_0_0
  · exact right0Middle4_eq_case_6_2_row_0_0_1
  · exact right0Middle4_eq_case_6_2_row_0_0_2
  · exact right0Middle4_eq_case_6_2_row_0_0_3
  · exact right0Middle4_eq_case_6_2_row_1_0_0
  · exact right0Middle4_eq_case_6_2_row_1_0_1
  · exact right0Middle4_eq_case_6_2_row_1_0_2
  · exact right0Middle4_eq_case_6_2_row_1_0_3
  · exact right0Middle4_eq_case_6_2_row_2_0_0
  · exact right0Middle4_eq_case_6_2_row_2_0_1
  · exact right0Middle4_eq_case_6_2_row_2_0_2
  · exact right0Middle4_eq_case_6_2_row_2_0_3
  · exact right0Middle4_eq_case_6_2_row_3_0_0
  · exact right0Middle4_eq_case_6_2_row_3_0_1
  · exact right0Middle4_eq_case_6_2_row_3_0_2
  · exact right0Middle4_eq_case_6_2_row_3_0_3

set_option backward.isDefEq.respectTransparency false in
theorem right0Middle4_eq_case_6_2 : right0Middle4 6 2 = innerRightZ 4 6 2 * associatorZ 4 6 2 := by
  simpa only [HexagonAtoms462.assocABC_eq,
    HexagonAtoms462.outerABC_eq,
    HexagonAtoms462.assocBAC_eq,
    HexagonAtoms462.innerABC_eq,
    HexagonAtoms462.innerRightABC_eq,
    HexagonAtoms462.inverseACB_eq,
    HexagonAtoms462.innerACB_eq,
    HexagonAtoms462.assocBCA_eq,
    HexagonAtoms462.innerRightBAC_eq,
    HexagonAtoms462.assocCAB_eq,
    HexagonAtoms462.outerLeftABC_eq,
    HexagonRowColumn462.product0_eq,
    HexagonRowColumn462.product1_eq,
    HexagonRowColumn462.product2_eq,
    HexagonRowColumn462.product3_eq,
    HexagonRowColumn462.product4_eq,
    HexagonRowColumn462.product5_eq,
    HexagonRowColumn462.product6_eq,
    HexagonRowColumn462.product7_eq] using right0Middle4_eq_case_6_2_checked

private theorem right1Middle4_eq_case_6_2_row_0_0_0 : (right1Middle4 6 2) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn462.rows_inverseACB HexagonRowColumn462.cols_right0) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_6_2_row_0_0_1 : (right1Middle4 6 2) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn462.rows_inverseACB HexagonRowColumn462.cols_right0) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_6_2_row_0_0_2 : (right1Middle4 6 2) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn462.rows_inverseACB HexagonRowColumn462.cols_right0) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_6_2_row_0_0_3 : (right1Middle4 6 2) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn462.rows_inverseACB HexagonRowColumn462.cols_right0) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_6_2_row_0_1_0 : (right1Middle4 6 2) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn462.rows_inverseACB HexagonRowColumn462.cols_right0) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_6_2_row_0_1_1 : (right1Middle4 6 2) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn462.rows_inverseACB HexagonRowColumn462.cols_right0) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_6_2_row_0_1_2 : (right1Middle4 6 2) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn462.rows_inverseACB HexagonRowColumn462.cols_right0) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_6_2_row_0_1_3 : (right1Middle4 6 2) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn462.rows_inverseACB HexagonRowColumn462.cols_right0) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_6_2_row_1_0_0 : (right1Middle4 6 2) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn462.rows_inverseACB HexagonRowColumn462.cols_right0) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_6_2_row_1_0_1 : (right1Middle4 6 2) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn462.rows_inverseACB HexagonRowColumn462.cols_right0) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_6_2_row_1_0_2 : (right1Middle4 6 2) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn462.rows_inverseACB HexagonRowColumn462.cols_right0) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_6_2_row_1_0_3 : (right1Middle4 6 2) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn462.rows_inverseACB HexagonRowColumn462.cols_right0) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_6_2_row_1_1_0 : (right1Middle4 6 2) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn462.rows_inverseACB HexagonRowColumn462.cols_right0) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_6_2_row_1_1_1 : (right1Middle4 6 2) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn462.rows_inverseACB HexagonRowColumn462.cols_right0) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_6_2_row_1_1_2 : (right1Middle4 6 2) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn462.rows_inverseACB HexagonRowColumn462.cols_right0) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_6_2_row_1_1_3 : (right1Middle4 6 2) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn462.rows_inverseACB HexagonRowColumn462.cols_right0) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_6_2_checked : right1Middle4 6 2 = rowColumnMul HexagonRowColumn462.rows_inverseACB HexagonRowColumn462.cols_right0 := by
  funext r
  fin_cases r
  · exact right1Middle4_eq_case_6_2_row_0_0_0
  · exact right1Middle4_eq_case_6_2_row_0_0_1
  · exact right1Middle4_eq_case_6_2_row_0_0_2
  · exact right1Middle4_eq_case_6_2_row_0_0_3
  · exact right1Middle4_eq_case_6_2_row_0_1_0
  · exact right1Middle4_eq_case_6_2_row_0_1_1
  · exact right1Middle4_eq_case_6_2_row_0_1_2
  · exact right1Middle4_eq_case_6_2_row_0_1_3
  · exact right1Middle4_eq_case_6_2_row_1_0_0
  · exact right1Middle4_eq_case_6_2_row_1_0_1
  · exact right1Middle4_eq_case_6_2_row_1_0_2
  · exact right1Middle4_eq_case_6_2_row_1_0_3
  · exact right1Middle4_eq_case_6_2_row_1_1_0
  · exact right1Middle4_eq_case_6_2_row_1_1_1
  · exact right1Middle4_eq_case_6_2_row_1_1_2
  · exact right1Middle4_eq_case_6_2_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem right1Middle4_eq_case_6_2 : right1Middle4 6 2 = associatorInverseZ 4 2 6 * right0Middle4 6 2 := by
  simpa only [HexagonAtoms462.assocABC_eq,
    HexagonAtoms462.outerABC_eq,
    HexagonAtoms462.assocBAC_eq,
    HexagonAtoms462.innerABC_eq,
    HexagonAtoms462.innerRightABC_eq,
    HexagonAtoms462.inverseACB_eq,
    HexagonAtoms462.innerACB_eq,
    HexagonAtoms462.assocBCA_eq,
    HexagonAtoms462.innerRightBAC_eq,
    HexagonAtoms462.assocCAB_eq,
    HexagonAtoms462.outerLeftABC_eq,
    HexagonRowColumn462.product0_eq,
    HexagonRowColumn462.product1_eq,
    HexagonRowColumn462.product2_eq,
    HexagonRowColumn462.product3_eq,
    HexagonRowColumn462.product4_eq,
    HexagonRowColumn462.product5_eq,
    HexagonRowColumn462.product6_eq,
    HexagonRowColumn462.product7_eq] using right1Middle4_eq_case_6_2_checked

private theorem right2Middle4_eq_case_6_2_row_0_0_0 : (right2Middle4 6 2) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (right1Middle4 6 2) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_6_2_row_0_0_1 : (right2Middle4 6 2) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (right1Middle4 6 2) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_6_2_row_0_0_2 : (right2Middle4 6 2) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (right1Middle4 6 2) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_6_2_row_0_0_3 : (right2Middle4 6 2) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (right1Middle4 6 2) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_6_2_row_0_1_0 : (right2Middle4 6 2) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (right1Middle4 6 2) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_6_2_row_0_1_1 : (right2Middle4 6 2) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (right1Middle4 6 2) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_6_2_row_0_1_2 : (right2Middle4 6 2) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (right1Middle4 6 2) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_6_2_row_0_1_3 : (right2Middle4 6 2) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (right1Middle4 6 2) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_6_2_row_1_0_0 : (right2Middle4 6 2) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (right1Middle4 6 2) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_6_2_row_1_0_1 : (right2Middle4 6 2) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (right1Middle4 6 2) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_6_2_row_1_0_2 : (right2Middle4 6 2) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (right1Middle4 6 2) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_6_2_row_1_0_3 : (right2Middle4 6 2) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (right1Middle4 6 2) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_6_2_row_1_1_0 : (right2Middle4 6 2) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (right1Middle4 6 2) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_6_2_row_1_1_1 : (right2Middle4 6 2) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (right1Middle4 6 2) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_6_2_row_1_1_2 : (right2Middle4 6 2) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (right1Middle4 6 2) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_6_2_row_1_1_3 : (right2Middle4 6 2) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (right1Middle4 6 2) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_6_2_checked : right2Middle4 6 2 = right1Middle4 6 2 := by
  funext r
  fin_cases r
  · exact right2Middle4_eq_case_6_2_row_0_0_0
  · exact right2Middle4_eq_case_6_2_row_0_0_1
  · exact right2Middle4_eq_case_6_2_row_0_0_2
  · exact right2Middle4_eq_case_6_2_row_0_0_3
  · exact right2Middle4_eq_case_6_2_row_0_1_0
  · exact right2Middle4_eq_case_6_2_row_0_1_1
  · exact right2Middle4_eq_case_6_2_row_0_1_2
  · exact right2Middle4_eq_case_6_2_row_0_1_3
  · exact right2Middle4_eq_case_6_2_row_1_0_0
  · exact right2Middle4_eq_case_6_2_row_1_0_1
  · exact right2Middle4_eq_case_6_2_row_1_0_2
  · exact right2Middle4_eq_case_6_2_row_1_0_3
  · exact right2Middle4_eq_case_6_2_row_1_1_0
  · exact right2Middle4_eq_case_6_2_row_1_1_1
  · exact right2Middle4_eq_case_6_2_row_1_1_2
  · exact right2Middle4_eq_case_6_2_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem right2Middle4_eq_case_6_2 : right2Middle4 6 2 = innerLeftZ 4 2 6 * right1Middle4 6 2 := by
  simpa only [HexagonAtoms462.assocABC_eq,
    HexagonAtoms462.outerABC_eq,
    HexagonAtoms462.assocBAC_eq,
    HexagonAtoms462.innerABC_eq,
    HexagonAtoms462.innerRightABC_eq,
    HexagonAtoms462.inverseACB_eq,
    HexagonAtoms462.innerACB_eq,
    HexagonAtoms462.assocBCA_eq,
    HexagonAtoms462.innerRightBAC_eq,
    HexagonAtoms462.assocCAB_eq,
    HexagonAtoms462.outerLeftABC_eq,
    HexagonRowColumn462.product0_eq,
    HexagonRowColumn462.product1_eq,
    HexagonRowColumn462.product2_eq,
    HexagonRowColumn462.product3_eq,
    HexagonRowColumn462.product4_eq,
    HexagonRowColumn462.product5_eq,
    HexagonRowColumn462.product6_eq,
    HexagonRowColumn462.product7_eq] using right2Middle4_eq_case_6_2_checked

private theorem leftFinal4_case_6_2_row_0_0_0 : (((-1 : ℤ) ^ (leftScaleBit 4 6 2).val * positiveScale (leftScaleExponent 4 6 2)) •
      (rowColumnMul HexagonRowColumn462.rows_assocBCA HexagonRowColumn462.cols_left0)) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 4 6 2) • (left1Middle4 6 2)) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal4_case_6_2_row_0_0_1 : (((-1 : ℤ) ^ (leftScaleBit 4 6 2).val * positiveScale (leftScaleExponent 4 6 2)) •
      (rowColumnMul HexagonRowColumn462.rows_assocBCA HexagonRowColumn462.cols_left0)) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 4 6 2) • (left1Middle4 6 2)) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal4_case_6_2_row_0_0_2 : (((-1 : ℤ) ^ (leftScaleBit 4 6 2).val * positiveScale (leftScaleExponent 4 6 2)) •
      (rowColumnMul HexagonRowColumn462.rows_assocBCA HexagonRowColumn462.cols_left0)) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 4 6 2) • (left1Middle4 6 2)) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal4_case_6_2_row_0_0_3 : (((-1 : ℤ) ^ (leftScaleBit 4 6 2).val * positiveScale (leftScaleExponent 4 6 2)) •
      (rowColumnMul HexagonRowColumn462.rows_assocBCA HexagonRowColumn462.cols_left0)) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 4 6 2) • (left1Middle4 6 2)) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal4_case_6_2_row_0_1_0 : (((-1 : ℤ) ^ (leftScaleBit 4 6 2).val * positiveScale (leftScaleExponent 4 6 2)) •
      (rowColumnMul HexagonRowColumn462.rows_assocBCA HexagonRowColumn462.cols_left0)) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 4 6 2) • (left1Middle4 6 2)) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal4_case_6_2_row_0_1_1 : (((-1 : ℤ) ^ (leftScaleBit 4 6 2).val * positiveScale (leftScaleExponent 4 6 2)) •
      (rowColumnMul HexagonRowColumn462.rows_assocBCA HexagonRowColumn462.cols_left0)) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 4 6 2) • (left1Middle4 6 2)) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal4_case_6_2_row_0_1_2 : (((-1 : ℤ) ^ (leftScaleBit 4 6 2).val * positiveScale (leftScaleExponent 4 6 2)) •
      (rowColumnMul HexagonRowColumn462.rows_assocBCA HexagonRowColumn462.cols_left0)) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 4 6 2) • (left1Middle4 6 2)) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal4_case_6_2_row_0_1_3 : (((-1 : ℤ) ^ (leftScaleBit 4 6 2).val * positiveScale (leftScaleExponent 4 6 2)) •
      (rowColumnMul HexagonRowColumn462.rows_assocBCA HexagonRowColumn462.cols_left0)) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 4 6 2) • (left1Middle4 6 2)) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal4_case_6_2_row_1_0_0 : (((-1 : ℤ) ^ (leftScaleBit 4 6 2).val * positiveScale (leftScaleExponent 4 6 2)) •
      (rowColumnMul HexagonRowColumn462.rows_assocBCA HexagonRowColumn462.cols_left0)) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 4 6 2) • (left1Middle4 6 2)) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal4_case_6_2_row_1_0_1 : (((-1 : ℤ) ^ (leftScaleBit 4 6 2).val * positiveScale (leftScaleExponent 4 6 2)) •
      (rowColumnMul HexagonRowColumn462.rows_assocBCA HexagonRowColumn462.cols_left0)) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 4 6 2) • (left1Middle4 6 2)) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal4_case_6_2_row_1_0_2 : (((-1 : ℤ) ^ (leftScaleBit 4 6 2).val * positiveScale (leftScaleExponent 4 6 2)) •
      (rowColumnMul HexagonRowColumn462.rows_assocBCA HexagonRowColumn462.cols_left0)) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 4 6 2) • (left1Middle4 6 2)) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal4_case_6_2_row_1_0_3 : (((-1 : ℤ) ^ (leftScaleBit 4 6 2).val * positiveScale (leftScaleExponent 4 6 2)) •
      (rowColumnMul HexagonRowColumn462.rows_assocBCA HexagonRowColumn462.cols_left0)) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 4 6 2) • (left1Middle4 6 2)) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal4_case_6_2_row_1_1_0 : (((-1 : ℤ) ^ (leftScaleBit 4 6 2).val * positiveScale (leftScaleExponent 4 6 2)) •
      (rowColumnMul HexagonRowColumn462.rows_assocBCA HexagonRowColumn462.cols_left0)) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 4 6 2) • (left1Middle4 6 2)) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal4_case_6_2_row_1_1_1 : (((-1 : ℤ) ^ (leftScaleBit 4 6 2).val * positiveScale (leftScaleExponent 4 6 2)) •
      (rowColumnMul HexagonRowColumn462.rows_assocBCA HexagonRowColumn462.cols_left0)) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 4 6 2) • (left1Middle4 6 2)) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal4_case_6_2_row_1_1_2 : (((-1 : ℤ) ^ (leftScaleBit 4 6 2).val * positiveScale (leftScaleExponent 4 6 2)) •
      (rowColumnMul HexagonRowColumn462.rows_assocBCA HexagonRowColumn462.cols_left0)) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 4 6 2) • (left1Middle4 6 2)) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal4_case_6_2_row_1_1_3 : (((-1 : ℤ) ^ (leftScaleBit 4 6 2).val * positiveScale (leftScaleExponent 4 6 2)) •
      (rowColumnMul HexagonRowColumn462.rows_assocBCA HexagonRowColumn462.cols_left0)) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 4 6 2) • (left1Middle4 6 2)) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal4_case_6_2_checked : ((-1 : ℤ) ^ (leftScaleBit 4 6 2).val * positiveScale (leftScaleExponent 4 6 2)) •
      (rowColumnMul HexagonRowColumn462.rows_assocBCA HexagonRowColumn462.cols_left0) = negativeScale (leftScaleExponent 4 6 2) • (left1Middle4 6 2) := by
  funext r
  fin_cases r
  · exact leftFinal4_case_6_2_row_0_0_0
  · exact leftFinal4_case_6_2_row_0_0_1
  · exact leftFinal4_case_6_2_row_0_0_2
  · exact leftFinal4_case_6_2_row_0_0_3
  · exact leftFinal4_case_6_2_row_0_1_0
  · exact leftFinal4_case_6_2_row_0_1_1
  · exact leftFinal4_case_6_2_row_0_1_2
  · exact leftFinal4_case_6_2_row_0_1_3
  · exact leftFinal4_case_6_2_row_1_0_0
  · exact leftFinal4_case_6_2_row_1_0_1
  · exact leftFinal4_case_6_2_row_1_0_2
  · exact leftFinal4_case_6_2_row_1_0_3
  · exact leftFinal4_case_6_2_row_1_1_0
  · exact leftFinal4_case_6_2_row_1_1_1
  · exact leftFinal4_case_6_2_row_1_1_2
  · exact leftFinal4_case_6_2_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem leftFinal4_case_6_2 : ((-1 : ℤ) ^ (leftScaleBit 4 6 2).val * positiveScale (leftScaleExponent 4 6 2)) •
      (associatorZ 6 2 4 * left0Middle4 6 2) = negativeScale (leftScaleExponent 4 6 2) • (innerRightZ 6 4 2 * left1Middle4 6 2) := by
  simpa only [HexagonAtoms462.assocABC_eq,
    HexagonAtoms462.outerABC_eq,
    HexagonAtoms462.assocBAC_eq,
    HexagonAtoms462.innerABC_eq,
    HexagonAtoms462.innerRightABC_eq,
    HexagonAtoms462.inverseACB_eq,
    HexagonAtoms462.innerACB_eq,
    HexagonAtoms462.assocBCA_eq,
    HexagonAtoms462.innerRightBAC_eq,
    HexagonAtoms462.assocCAB_eq,
    HexagonAtoms462.outerLeftABC_eq,
    HexagonRowColumn462.product0_eq,
    HexagonRowColumn462.product1_eq,
    HexagonRowColumn462.product2_eq,
    HexagonRowColumn462.product3_eq,
    HexagonRowColumn462.product4_eq,
    HexagonRowColumn462.product5_eq,
    HexagonRowColumn462.product6_eq,
    HexagonRowColumn462.product7_eq] using leftFinal4_case_6_2_checked

private theorem rightFinal4_case_6_2_row_0_0_0 : (((-1 : ℤ) ^ (rightScaleBit 4 6 2).val * positiveScale (rightScaleExponent 4 6 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 2 6 : ℤ)) • HexagonAtoms462.outerLeftABC) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 4 6 2) • (rowColumnMul HexagonRowColumn462.rows_assocCAB HexagonRowColumn462.cols_right2)) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal4_case_6_2_row_0_0_1 : (((-1 : ℤ) ^ (rightScaleBit 4 6 2).val * positiveScale (rightScaleExponent 4 6 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 2 6 : ℤ)) • HexagonAtoms462.outerLeftABC) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 4 6 2) • (rowColumnMul HexagonRowColumn462.rows_assocCAB HexagonRowColumn462.cols_right2)) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal4_case_6_2_row_0_0_2 : (((-1 : ℤ) ^ (rightScaleBit 4 6 2).val * positiveScale (rightScaleExponent 4 6 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 2 6 : ℤ)) • HexagonAtoms462.outerLeftABC) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 4 6 2) • (rowColumnMul HexagonRowColumn462.rows_assocCAB HexagonRowColumn462.cols_right2)) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal4_case_6_2_row_0_0_3 : (((-1 : ℤ) ^ (rightScaleBit 4 6 2).val * positiveScale (rightScaleExponent 4 6 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 2 6 : ℤ)) • HexagonAtoms462.outerLeftABC) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 4 6 2) • (rowColumnMul HexagonRowColumn462.rows_assocCAB HexagonRowColumn462.cols_right2)) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal4_case_6_2_row_0_1_0 : (((-1 : ℤ) ^ (rightScaleBit 4 6 2).val * positiveScale (rightScaleExponent 4 6 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 2 6 : ℤ)) • HexagonAtoms462.outerLeftABC) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 4 6 2) • (rowColumnMul HexagonRowColumn462.rows_assocCAB HexagonRowColumn462.cols_right2)) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal4_case_6_2_row_0_1_1 : (((-1 : ℤ) ^ (rightScaleBit 4 6 2).val * positiveScale (rightScaleExponent 4 6 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 2 6 : ℤ)) • HexagonAtoms462.outerLeftABC) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 4 6 2) • (rowColumnMul HexagonRowColumn462.rows_assocCAB HexagonRowColumn462.cols_right2)) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal4_case_6_2_row_0_1_2 : (((-1 : ℤ) ^ (rightScaleBit 4 6 2).val * positiveScale (rightScaleExponent 4 6 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 2 6 : ℤ)) • HexagonAtoms462.outerLeftABC) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 4 6 2) • (rowColumnMul HexagonRowColumn462.rows_assocCAB HexagonRowColumn462.cols_right2)) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal4_case_6_2_row_0_1_3 : (((-1 : ℤ) ^ (rightScaleBit 4 6 2).val * positiveScale (rightScaleExponent 4 6 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 2 6 : ℤ)) • HexagonAtoms462.outerLeftABC) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 4 6 2) • (rowColumnMul HexagonRowColumn462.rows_assocCAB HexagonRowColumn462.cols_right2)) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal4_case_6_2_row_1_0_0 : (((-1 : ℤ) ^ (rightScaleBit 4 6 2).val * positiveScale (rightScaleExponent 4 6 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 2 6 : ℤ)) • HexagonAtoms462.outerLeftABC) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 4 6 2) • (rowColumnMul HexagonRowColumn462.rows_assocCAB HexagonRowColumn462.cols_right2)) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal4_case_6_2_row_1_0_1 : (((-1 : ℤ) ^ (rightScaleBit 4 6 2).val * positiveScale (rightScaleExponent 4 6 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 2 6 : ℤ)) • HexagonAtoms462.outerLeftABC) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 4 6 2) • (rowColumnMul HexagonRowColumn462.rows_assocCAB HexagonRowColumn462.cols_right2)) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal4_case_6_2_row_1_0_2 : (((-1 : ℤ) ^ (rightScaleBit 4 6 2).val * positiveScale (rightScaleExponent 4 6 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 2 6 : ℤ)) • HexagonAtoms462.outerLeftABC) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 4 6 2) • (rowColumnMul HexagonRowColumn462.rows_assocCAB HexagonRowColumn462.cols_right2)) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal4_case_6_2_row_1_0_3 : (((-1 : ℤ) ^ (rightScaleBit 4 6 2).val * positiveScale (rightScaleExponent 4 6 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 2 6 : ℤ)) • HexagonAtoms462.outerLeftABC) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 4 6 2) • (rowColumnMul HexagonRowColumn462.rows_assocCAB HexagonRowColumn462.cols_right2)) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal4_case_6_2_row_1_1_0 : (((-1 : ℤ) ^ (rightScaleBit 4 6 2).val * positiveScale (rightScaleExponent 4 6 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 2 6 : ℤ)) • HexagonAtoms462.outerLeftABC) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 4 6 2) • (rowColumnMul HexagonRowColumn462.rows_assocCAB HexagonRowColumn462.cols_right2)) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal4_case_6_2_row_1_1_1 : (((-1 : ℤ) ^ (rightScaleBit 4 6 2).val * positiveScale (rightScaleExponent 4 6 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 2 6 : ℤ)) • HexagonAtoms462.outerLeftABC) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 4 6 2) • (rowColumnMul HexagonRowColumn462.rows_assocCAB HexagonRowColumn462.cols_right2)) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal4_case_6_2_row_1_1_2 : (((-1 : ℤ) ^ (rightScaleBit 4 6 2).val * positiveScale (rightScaleExponent 4 6 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 2 6 : ℤ)) • HexagonAtoms462.outerLeftABC) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 4 6 2) • (rowColumnMul HexagonRowColumn462.rows_assocCAB HexagonRowColumn462.cols_right2)) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal4_case_6_2_row_1_1_3 : (((-1 : ℤ) ^ (rightScaleBit 4 6 2).val * positiveScale (rightScaleExponent 4 6 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 2 6 : ℤ)) • HexagonAtoms462.outerLeftABC) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 4 6 2) • (rowColumnMul HexagonRowColumn462.rows_assocCAB HexagonRowColumn462.cols_right2)) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal4_case_6_2_checked : ((-1 : ℤ) ^ (rightScaleBit 4 6 2).val * positiveScale (rightScaleExponent 4 6 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 2 6 : ℤ)) • HexagonAtoms462.outerLeftABC = negativeScale (rightScaleExponent 4 6 2) • (rowColumnMul HexagonRowColumn462.rows_assocCAB HexagonRowColumn462.cols_right2) := by
  funext r
  fin_cases r
  · exact rightFinal4_case_6_2_row_0_0_0
  · exact rightFinal4_case_6_2_row_0_0_1
  · exact rightFinal4_case_6_2_row_0_0_2
  · exact rightFinal4_case_6_2_row_0_0_3
  · exact rightFinal4_case_6_2_row_0_1_0
  · exact rightFinal4_case_6_2_row_0_1_1
  · exact rightFinal4_case_6_2_row_0_1_2
  · exact rightFinal4_case_6_2_row_0_1_3
  · exact rightFinal4_case_6_2_row_1_0_0
  · exact rightFinal4_case_6_2_row_1_0_1
  · exact rightFinal4_case_6_2_row_1_0_2
  · exact rightFinal4_case_6_2_row_1_0_3
  · exact rightFinal4_case_6_2_row_1_1_0
  · exact rightFinal4_case_6_2_row_1_1_1
  · exact rightFinal4_case_6_2_row_1_1_2
  · exact rightFinal4_case_6_2_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem rightFinal4_case_6_2 : ((-1 : ℤ) ^ (rightScaleBit 4 6 2).val * positiveScale (rightScaleExponent 4 6 2) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 2 6 : ℤ)) • outerLeftZ 4 6 2 = negativeScale (rightScaleExponent 4 6 2) • (associatorZ 2 4 6 * right2Middle4 6 2) := by
  simpa only [HexagonAtoms462.assocABC_eq,
    HexagonAtoms462.outerABC_eq,
    HexagonAtoms462.assocBAC_eq,
    HexagonAtoms462.innerABC_eq,
    HexagonAtoms462.innerRightABC_eq,
    HexagonAtoms462.inverseACB_eq,
    HexagonAtoms462.innerACB_eq,
    HexagonAtoms462.assocBCA_eq,
    HexagonAtoms462.innerRightBAC_eq,
    HexagonAtoms462.assocCAB_eq,
    HexagonAtoms462.outerLeftABC_eq,
    HexagonRowColumn462.product0_eq,
    HexagonRowColumn462.product1_eq,
    HexagonRowColumn462.product2_eq,
    HexagonRowColumn462.product3_eq,
    HexagonRowColumn462.product4_eq,
    HexagonRowColumn462.product5_eq,
    HexagonRowColumn462.product6_eq,
    HexagonRowColumn462.product7_eq] using rightFinal4_case_6_2_checked

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonCases4
