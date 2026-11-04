import RMod.BrundanEllis.StackingReferenceHexagonMiddle4
import RMod.BrundanEllis.StackingReferenceSparseMatrixCheck
import RMod.BrundanEllis.StackingReferenceHexagonAtoms424
import RMod.BrundanEllis.StackingReferenceHexagonRowColumn424

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

private theorem left0Middle4_eq_case_2_4_row_0_0_0 : (left0Middle4 2 4) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms424.assocABC) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_2_4_row_0_0_1 : (left0Middle4 2 4) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms424.assocABC) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_2_4_row_0_0_2 : (left0Middle4 2 4) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms424.assocABC) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_2_4_row_0_0_3 : (left0Middle4 2 4) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms424.assocABC) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_2_4_row_0_1_0 : (left0Middle4 2 4) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms424.assocABC) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_2_4_row_0_1_1 : (left0Middle4 2 4) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms424.assocABC) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_2_4_row_0_1_2 : (left0Middle4 2 4) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms424.assocABC) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_2_4_row_0_1_3 : (left0Middle4 2 4) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms424.assocABC) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_2_4_row_1_0_0 : (left0Middle4 2 4) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms424.assocABC) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_2_4_row_1_0_1 : (left0Middle4 2 4) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms424.assocABC) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_2_4_row_1_0_2 : (left0Middle4 2 4) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms424.assocABC) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_2_4_row_1_0_3 : (left0Middle4 2 4) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms424.assocABC) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_2_4_row_1_1_0 : (left0Middle4 2 4) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms424.assocABC) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_2_4_row_1_1_1 : (left0Middle4 2 4) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms424.assocABC) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_2_4_row_1_1_2 : (left0Middle4 2 4) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms424.assocABC) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_2_4_row_1_1_3 : (left0Middle4 2 4) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms424.assocABC) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_2_4_checked : left0Middle4 2 4 = HexagonAtoms424.assocABC := by
  funext r
  fin_cases r
  · exact left0Middle4_eq_case_2_4_row_0_0_0
  · exact left0Middle4_eq_case_2_4_row_0_0_1
  · exact left0Middle4_eq_case_2_4_row_0_0_2
  · exact left0Middle4_eq_case_2_4_row_0_0_3
  · exact left0Middle4_eq_case_2_4_row_0_1_0
  · exact left0Middle4_eq_case_2_4_row_0_1_1
  · exact left0Middle4_eq_case_2_4_row_0_1_2
  · exact left0Middle4_eq_case_2_4_row_0_1_3
  · exact left0Middle4_eq_case_2_4_row_1_0_0
  · exact left0Middle4_eq_case_2_4_row_1_0_1
  · exact left0Middle4_eq_case_2_4_row_1_0_2
  · exact left0Middle4_eq_case_2_4_row_1_0_3
  · exact left0Middle4_eq_case_2_4_row_1_1_0
  · exact left0Middle4_eq_case_2_4_row_1_1_1
  · exact left0Middle4_eq_case_2_4_row_1_1_2
  · exact left0Middle4_eq_case_2_4_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem left0Middle4_eq_case_2_4 : left0Middle4 2 4 = outerRightZ 4 2 4 * associatorZ 4 2 4 := by
  simpa only [HexagonAtoms424.assocABC_eq,
    HexagonAtoms424.outerABC_eq,
    HexagonAtoms424.assocBAC_eq,
    HexagonAtoms424.innerABC_eq,
    HexagonAtoms424.innerRightABC_eq,
    HexagonAtoms424.inverseACB_eq,
    HexagonAtoms424.innerACB_eq,
    HexagonAtoms424.assocBCA_eq,
    HexagonAtoms424.innerRightBAC_eq,
    HexagonAtoms424.assocCAB_eq,
    HexagonAtoms424.outerLeftABC_eq,
    HexagonRowColumn424.assocBCA_alias,
    HexagonRowColumn424.product0_eq,
    HexagonRowColumn424.product1_eq,
    HexagonRowColumn424.product2_eq,
    HexagonRowColumn424.product3_eq,
    HexagonRowColumn424.product4_eq,
    HexagonRowColumn424.product5_eq,
    HexagonRowColumn424.product6_eq,
    HexagonRowColumn424.product7_eq] using left0Middle4_eq_case_2_4_checked

private theorem left1Middle4_eq_case_2_4_row_0_0_0 : (left1Middle4 2 4) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms424.assocBAC) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_2_4_row_0_0_1 : (left1Middle4 2 4) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms424.assocBAC) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_2_4_row_0_0_2 : (left1Middle4 2 4) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms424.assocBAC) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_2_4_row_0_0_3 : (left1Middle4 2 4) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms424.assocBAC) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_2_4_row_1_0_0 : (left1Middle4 2 4) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms424.assocBAC) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_2_4_row_1_0_1 : (left1Middle4 2 4) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms424.assocBAC) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_2_4_row_1_0_2 : (left1Middle4 2 4) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms424.assocBAC) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_2_4_row_1_0_3 : (left1Middle4 2 4) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms424.assocBAC) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_2_4_row_2_0_0 : (left1Middle4 2 4) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms424.assocBAC) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_2_4_row_2_0_1 : (left1Middle4 2 4) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms424.assocBAC) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_2_4_row_2_0_2 : (left1Middle4 2 4) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms424.assocBAC) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_2_4_row_2_0_3 : (left1Middle4 2 4) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms424.assocBAC) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_2_4_row_3_0_0 : (left1Middle4 2 4) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms424.assocBAC) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_2_4_row_3_0_1 : (left1Middle4 2 4) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms424.assocBAC) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_2_4_row_3_0_2 : (left1Middle4 2 4) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms424.assocBAC) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_2_4_row_3_0_3 : (left1Middle4 2 4) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms424.assocBAC) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_2_4_checked : left1Middle4 2 4 = HexagonAtoms424.assocBAC := by
  funext r
  fin_cases r
  · exact left1Middle4_eq_case_2_4_row_0_0_0
  · exact left1Middle4_eq_case_2_4_row_0_0_1
  · exact left1Middle4_eq_case_2_4_row_0_0_2
  · exact left1Middle4_eq_case_2_4_row_0_0_3
  · exact left1Middle4_eq_case_2_4_row_1_0_0
  · exact left1Middle4_eq_case_2_4_row_1_0_1
  · exact left1Middle4_eq_case_2_4_row_1_0_2
  · exact left1Middle4_eq_case_2_4_row_1_0_3
  · exact left1Middle4_eq_case_2_4_row_2_0_0
  · exact left1Middle4_eq_case_2_4_row_2_0_1
  · exact left1Middle4_eq_case_2_4_row_2_0_2
  · exact left1Middle4_eq_case_2_4_row_2_0_3
  · exact left1Middle4_eq_case_2_4_row_3_0_0
  · exact left1Middle4_eq_case_2_4_row_3_0_1
  · exact left1Middle4_eq_case_2_4_row_3_0_2
  · exact left1Middle4_eq_case_2_4_row_3_0_3

set_option backward.isDefEq.respectTransparency false in
theorem left1Middle4_eq_case_2_4 : left1Middle4 2 4 = associatorZ 2 4 4 * innerLeftZ 4 2 4 := by
  simpa only [HexagonAtoms424.assocABC_eq,
    HexagonAtoms424.outerABC_eq,
    HexagonAtoms424.assocBAC_eq,
    HexagonAtoms424.innerABC_eq,
    HexagonAtoms424.innerRightABC_eq,
    HexagonAtoms424.inverseACB_eq,
    HexagonAtoms424.innerACB_eq,
    HexagonAtoms424.assocBCA_eq,
    HexagonAtoms424.innerRightBAC_eq,
    HexagonAtoms424.assocCAB_eq,
    HexagonAtoms424.outerLeftABC_eq,
    HexagonRowColumn424.assocBCA_alias,
    HexagonRowColumn424.product0_eq,
    HexagonRowColumn424.product1_eq,
    HexagonRowColumn424.product2_eq,
    HexagonRowColumn424.product3_eq,
    HexagonRowColumn424.product4_eq,
    HexagonRowColumn424.product5_eq,
    HexagonRowColumn424.product6_eq,
    HexagonRowColumn424.product7_eq] using left1Middle4_eq_case_2_4_checked

private theorem right0Middle4_eq_case_2_4_row_0_0_0 : (right0Middle4 2 4) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms424.assocABC) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_2_4_row_0_0_1 : (right0Middle4 2 4) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms424.assocABC) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_2_4_row_0_0_2 : (right0Middle4 2 4) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms424.assocABC) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_2_4_row_0_0_3 : (right0Middle4 2 4) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms424.assocABC) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_2_4_row_0_1_0 : (right0Middle4 2 4) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms424.assocABC) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_2_4_row_0_1_1 : (right0Middle4 2 4) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms424.assocABC) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_2_4_row_0_1_2 : (right0Middle4 2 4) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms424.assocABC) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_2_4_row_0_1_3 : (right0Middle4 2 4) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms424.assocABC) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_2_4_row_1_0_0 : (right0Middle4 2 4) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms424.assocABC) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_2_4_row_1_0_1 : (right0Middle4 2 4) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms424.assocABC) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_2_4_row_1_0_2 : (right0Middle4 2 4) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms424.assocABC) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_2_4_row_1_0_3 : (right0Middle4 2 4) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms424.assocABC) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_2_4_row_1_1_0 : (right0Middle4 2 4) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms424.assocABC) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_2_4_row_1_1_1 : (right0Middle4 2 4) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms424.assocABC) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_2_4_row_1_1_2 : (right0Middle4 2 4) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms424.assocABC) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_2_4_row_1_1_3 : (right0Middle4 2 4) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms424.assocABC) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_2_4_checked : right0Middle4 2 4 = HexagonAtoms424.assocABC := by
  funext r
  fin_cases r
  · exact right0Middle4_eq_case_2_4_row_0_0_0
  · exact right0Middle4_eq_case_2_4_row_0_0_1
  · exact right0Middle4_eq_case_2_4_row_0_0_2
  · exact right0Middle4_eq_case_2_4_row_0_0_3
  · exact right0Middle4_eq_case_2_4_row_0_1_0
  · exact right0Middle4_eq_case_2_4_row_0_1_1
  · exact right0Middle4_eq_case_2_4_row_0_1_2
  · exact right0Middle4_eq_case_2_4_row_0_1_3
  · exact right0Middle4_eq_case_2_4_row_1_0_0
  · exact right0Middle4_eq_case_2_4_row_1_0_1
  · exact right0Middle4_eq_case_2_4_row_1_0_2
  · exact right0Middle4_eq_case_2_4_row_1_0_3
  · exact right0Middle4_eq_case_2_4_row_1_1_0
  · exact right0Middle4_eq_case_2_4_row_1_1_1
  · exact right0Middle4_eq_case_2_4_row_1_1_2
  · exact right0Middle4_eq_case_2_4_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem right0Middle4_eq_case_2_4 : right0Middle4 2 4 = innerRightZ 4 2 4 * associatorZ 4 2 4 := by
  simpa only [HexagonAtoms424.assocABC_eq,
    HexagonAtoms424.outerABC_eq,
    HexagonAtoms424.assocBAC_eq,
    HexagonAtoms424.innerABC_eq,
    HexagonAtoms424.innerRightABC_eq,
    HexagonAtoms424.inverseACB_eq,
    HexagonAtoms424.innerACB_eq,
    HexagonAtoms424.assocBCA_eq,
    HexagonAtoms424.innerRightBAC_eq,
    HexagonAtoms424.assocCAB_eq,
    HexagonAtoms424.outerLeftABC_eq,
    HexagonRowColumn424.assocBCA_alias,
    HexagonRowColumn424.product0_eq,
    HexagonRowColumn424.product1_eq,
    HexagonRowColumn424.product2_eq,
    HexagonRowColumn424.product3_eq,
    HexagonRowColumn424.product4_eq,
    HexagonRowColumn424.product5_eq,
    HexagonRowColumn424.product6_eq,
    HexagonRowColumn424.product7_eq] using right0Middle4_eq_case_2_4_checked

private theorem right1Middle4_eq_case_2_4_row_0_0_0 : (right1Middle4 2 4) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn424.rows_inverseACB HexagonRowColumn424.cols_right0) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_2_4_row_0_0_1 : (right1Middle4 2 4) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn424.rows_inverseACB HexagonRowColumn424.cols_right0) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_2_4_row_0_0_2 : (right1Middle4 2 4) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn424.rows_inverseACB HexagonRowColumn424.cols_right0) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_2_4_row_0_0_3 : (right1Middle4 2 4) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn424.rows_inverseACB HexagonRowColumn424.cols_right0) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_2_4_row_1_0_0 : (right1Middle4 2 4) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn424.rows_inverseACB HexagonRowColumn424.cols_right0) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_2_4_row_1_0_1 : (right1Middle4 2 4) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn424.rows_inverseACB HexagonRowColumn424.cols_right0) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_2_4_row_1_0_2 : (right1Middle4 2 4) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn424.rows_inverseACB HexagonRowColumn424.cols_right0) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_2_4_row_1_0_3 : (right1Middle4 2 4) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn424.rows_inverseACB HexagonRowColumn424.cols_right0) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_2_4_row_2_0_0 : (right1Middle4 2 4) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn424.rows_inverseACB HexagonRowColumn424.cols_right0) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_2_4_row_2_0_1 : (right1Middle4 2 4) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn424.rows_inverseACB HexagonRowColumn424.cols_right0) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_2_4_row_2_0_2 : (right1Middle4 2 4) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn424.rows_inverseACB HexagonRowColumn424.cols_right0) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_2_4_row_2_0_3 : (right1Middle4 2 4) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn424.rows_inverseACB HexagonRowColumn424.cols_right0) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_2_4_row_3_0_0 : (right1Middle4 2 4) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn424.rows_inverseACB HexagonRowColumn424.cols_right0) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_2_4_row_3_0_1 : (right1Middle4 2 4) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn424.rows_inverseACB HexagonRowColumn424.cols_right0) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_2_4_row_3_0_2 : (right1Middle4 2 4) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn424.rows_inverseACB HexagonRowColumn424.cols_right0) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_2_4_row_3_0_3 : (right1Middle4 2 4) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn424.rows_inverseACB HexagonRowColumn424.cols_right0) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_2_4_checked : right1Middle4 2 4 = rowColumnMul HexagonRowColumn424.rows_inverseACB HexagonRowColumn424.cols_right0 := by
  funext r
  fin_cases r
  · exact right1Middle4_eq_case_2_4_row_0_0_0
  · exact right1Middle4_eq_case_2_4_row_0_0_1
  · exact right1Middle4_eq_case_2_4_row_0_0_2
  · exact right1Middle4_eq_case_2_4_row_0_0_3
  · exact right1Middle4_eq_case_2_4_row_1_0_0
  · exact right1Middle4_eq_case_2_4_row_1_0_1
  · exact right1Middle4_eq_case_2_4_row_1_0_2
  · exact right1Middle4_eq_case_2_4_row_1_0_3
  · exact right1Middle4_eq_case_2_4_row_2_0_0
  · exact right1Middle4_eq_case_2_4_row_2_0_1
  · exact right1Middle4_eq_case_2_4_row_2_0_2
  · exact right1Middle4_eq_case_2_4_row_2_0_3
  · exact right1Middle4_eq_case_2_4_row_3_0_0
  · exact right1Middle4_eq_case_2_4_row_3_0_1
  · exact right1Middle4_eq_case_2_4_row_3_0_2
  · exact right1Middle4_eq_case_2_4_row_3_0_3

set_option backward.isDefEq.respectTransparency false in
theorem right1Middle4_eq_case_2_4 : right1Middle4 2 4 = associatorInverseZ 4 4 2 * right0Middle4 2 4 := by
  simpa only [HexagonAtoms424.assocABC_eq,
    HexagonAtoms424.outerABC_eq,
    HexagonAtoms424.assocBAC_eq,
    HexagonAtoms424.innerABC_eq,
    HexagonAtoms424.innerRightABC_eq,
    HexagonAtoms424.inverseACB_eq,
    HexagonAtoms424.innerACB_eq,
    HexagonAtoms424.assocBCA_eq,
    HexagonAtoms424.innerRightBAC_eq,
    HexagonAtoms424.assocCAB_eq,
    HexagonAtoms424.outerLeftABC_eq,
    HexagonRowColumn424.assocBCA_alias,
    HexagonRowColumn424.product0_eq,
    HexagonRowColumn424.product1_eq,
    HexagonRowColumn424.product2_eq,
    HexagonRowColumn424.product3_eq,
    HexagonRowColumn424.product4_eq,
    HexagonRowColumn424.product5_eq,
    HexagonRowColumn424.product6_eq,
    HexagonRowColumn424.product7_eq] using right1Middle4_eq_case_2_4_checked

private theorem right2Middle4_eq_case_2_4_row_0_0_0 : (right2Middle4 2 4) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn424.rows_innerACB HexagonRowColumn424.cols_right1) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_2_4_row_0_0_1 : (right2Middle4 2 4) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn424.rows_innerACB HexagonRowColumn424.cols_right1) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_2_4_row_0_0_2 : (right2Middle4 2 4) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn424.rows_innerACB HexagonRowColumn424.cols_right1) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_2_4_row_0_0_3 : (right2Middle4 2 4) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn424.rows_innerACB HexagonRowColumn424.cols_right1) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_2_4_row_1_0_0 : (right2Middle4 2 4) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn424.rows_innerACB HexagonRowColumn424.cols_right1) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_2_4_row_1_0_1 : (right2Middle4 2 4) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn424.rows_innerACB HexagonRowColumn424.cols_right1) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_2_4_row_1_0_2 : (right2Middle4 2 4) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn424.rows_innerACB HexagonRowColumn424.cols_right1) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_2_4_row_1_0_3 : (right2Middle4 2 4) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn424.rows_innerACB HexagonRowColumn424.cols_right1) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_2_4_row_2_0_0 : (right2Middle4 2 4) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn424.rows_innerACB HexagonRowColumn424.cols_right1) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_2_4_row_2_0_1 : (right2Middle4 2 4) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn424.rows_innerACB HexagonRowColumn424.cols_right1) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_2_4_row_2_0_2 : (right2Middle4 2 4) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn424.rows_innerACB HexagonRowColumn424.cols_right1) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_2_4_row_2_0_3 : (right2Middle4 2 4) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn424.rows_innerACB HexagonRowColumn424.cols_right1) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_2_4_row_3_0_0 : (right2Middle4 2 4) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn424.rows_innerACB HexagonRowColumn424.cols_right1) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_2_4_row_3_0_1 : (right2Middle4 2 4) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn424.rows_innerACB HexagonRowColumn424.cols_right1) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_2_4_row_3_0_2 : (right2Middle4 2 4) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn424.rows_innerACB HexagonRowColumn424.cols_right1) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_2_4_row_3_0_3 : (right2Middle4 2 4) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn424.rows_innerACB HexagonRowColumn424.cols_right1) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_2_4_checked : right2Middle4 2 4 = rowColumnMul HexagonRowColumn424.rows_innerACB HexagonRowColumn424.cols_right1 := by
  funext r
  fin_cases r
  · exact right2Middle4_eq_case_2_4_row_0_0_0
  · exact right2Middle4_eq_case_2_4_row_0_0_1
  · exact right2Middle4_eq_case_2_4_row_0_0_2
  · exact right2Middle4_eq_case_2_4_row_0_0_3
  · exact right2Middle4_eq_case_2_4_row_1_0_0
  · exact right2Middle4_eq_case_2_4_row_1_0_1
  · exact right2Middle4_eq_case_2_4_row_1_0_2
  · exact right2Middle4_eq_case_2_4_row_1_0_3
  · exact right2Middle4_eq_case_2_4_row_2_0_0
  · exact right2Middle4_eq_case_2_4_row_2_0_1
  · exact right2Middle4_eq_case_2_4_row_2_0_2
  · exact right2Middle4_eq_case_2_4_row_2_0_3
  · exact right2Middle4_eq_case_2_4_row_3_0_0
  · exact right2Middle4_eq_case_2_4_row_3_0_1
  · exact right2Middle4_eq_case_2_4_row_3_0_2
  · exact right2Middle4_eq_case_2_4_row_3_0_3

set_option backward.isDefEq.respectTransparency false in
theorem right2Middle4_eq_case_2_4 : right2Middle4 2 4 = innerLeftZ 4 4 2 * right1Middle4 2 4 := by
  simpa only [HexagonAtoms424.assocABC_eq,
    HexagonAtoms424.outerABC_eq,
    HexagonAtoms424.assocBAC_eq,
    HexagonAtoms424.innerABC_eq,
    HexagonAtoms424.innerRightABC_eq,
    HexagonAtoms424.inverseACB_eq,
    HexagonAtoms424.innerACB_eq,
    HexagonAtoms424.assocBCA_eq,
    HexagonAtoms424.innerRightBAC_eq,
    HexagonAtoms424.assocCAB_eq,
    HexagonAtoms424.outerLeftABC_eq,
    HexagonRowColumn424.assocBCA_alias,
    HexagonRowColumn424.product0_eq,
    HexagonRowColumn424.product1_eq,
    HexagonRowColumn424.product2_eq,
    HexagonRowColumn424.product3_eq,
    HexagonRowColumn424.product4_eq,
    HexagonRowColumn424.product5_eq,
    HexagonRowColumn424.product6_eq,
    HexagonRowColumn424.product7_eq] using right2Middle4_eq_case_2_4_checked

private theorem leftFinal4_case_2_4_row_0_0_0 : (((-1 : ℤ) ^ (leftScaleBit 4 2 4).val * positiveScale (leftScaleExponent 4 2 4)) •
      (rowColumnMul HexagonRowColumn424.rows_assocBAC HexagonRowColumn424.cols_left0)) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (negativeScale (leftScaleExponent 4 2 4) • (rowColumnMul HexagonRowColumn424.rows_innerRightBAC HexagonRowColumn424.cols_left1)) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal4_case_2_4_row_0_0_1 : (((-1 : ℤ) ^ (leftScaleBit 4 2 4).val * positiveScale (leftScaleExponent 4 2 4)) •
      (rowColumnMul HexagonRowColumn424.rows_assocBAC HexagonRowColumn424.cols_left0)) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (negativeScale (leftScaleExponent 4 2 4) • (rowColumnMul HexagonRowColumn424.rows_innerRightBAC HexagonRowColumn424.cols_left1)) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal4_case_2_4_row_0_0_2 : (((-1 : ℤ) ^ (leftScaleBit 4 2 4).val * positiveScale (leftScaleExponent 4 2 4)) •
      (rowColumnMul HexagonRowColumn424.rows_assocBAC HexagonRowColumn424.cols_left0)) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (negativeScale (leftScaleExponent 4 2 4) • (rowColumnMul HexagonRowColumn424.rows_innerRightBAC HexagonRowColumn424.cols_left1)) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal4_case_2_4_row_0_0_3 : (((-1 : ℤ) ^ (leftScaleBit 4 2 4).val * positiveScale (leftScaleExponent 4 2 4)) •
      (rowColumnMul HexagonRowColumn424.rows_assocBAC HexagonRowColumn424.cols_left0)) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (negativeScale (leftScaleExponent 4 2 4) • (rowColumnMul HexagonRowColumn424.rows_innerRightBAC HexagonRowColumn424.cols_left1)) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal4_case_2_4_row_1_0_0 : (((-1 : ℤ) ^ (leftScaleBit 4 2 4).val * positiveScale (leftScaleExponent 4 2 4)) •
      (rowColumnMul HexagonRowColumn424.rows_assocBAC HexagonRowColumn424.cols_left0)) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (negativeScale (leftScaleExponent 4 2 4) • (rowColumnMul HexagonRowColumn424.rows_innerRightBAC HexagonRowColumn424.cols_left1)) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal4_case_2_4_row_1_0_1 : (((-1 : ℤ) ^ (leftScaleBit 4 2 4).val * positiveScale (leftScaleExponent 4 2 4)) •
      (rowColumnMul HexagonRowColumn424.rows_assocBAC HexagonRowColumn424.cols_left0)) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (negativeScale (leftScaleExponent 4 2 4) • (rowColumnMul HexagonRowColumn424.rows_innerRightBAC HexagonRowColumn424.cols_left1)) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal4_case_2_4_row_1_0_2 : (((-1 : ℤ) ^ (leftScaleBit 4 2 4).val * positiveScale (leftScaleExponent 4 2 4)) •
      (rowColumnMul HexagonRowColumn424.rows_assocBAC HexagonRowColumn424.cols_left0)) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (negativeScale (leftScaleExponent 4 2 4) • (rowColumnMul HexagonRowColumn424.rows_innerRightBAC HexagonRowColumn424.cols_left1)) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal4_case_2_4_row_1_0_3 : (((-1 : ℤ) ^ (leftScaleBit 4 2 4).val * positiveScale (leftScaleExponent 4 2 4)) •
      (rowColumnMul HexagonRowColumn424.rows_assocBAC HexagonRowColumn424.cols_left0)) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (negativeScale (leftScaleExponent 4 2 4) • (rowColumnMul HexagonRowColumn424.rows_innerRightBAC HexagonRowColumn424.cols_left1)) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal4_case_2_4_row_2_0_0 : (((-1 : ℤ) ^ (leftScaleBit 4 2 4).val * positiveScale (leftScaleExponent 4 2 4)) •
      (rowColumnMul HexagonRowColumn424.rows_assocBAC HexagonRowColumn424.cols_left0)) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (negativeScale (leftScaleExponent 4 2 4) • (rowColumnMul HexagonRowColumn424.rows_innerRightBAC HexagonRowColumn424.cols_left1)) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal4_case_2_4_row_2_0_1 : (((-1 : ℤ) ^ (leftScaleBit 4 2 4).val * positiveScale (leftScaleExponent 4 2 4)) •
      (rowColumnMul HexagonRowColumn424.rows_assocBAC HexagonRowColumn424.cols_left0)) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (negativeScale (leftScaleExponent 4 2 4) • (rowColumnMul HexagonRowColumn424.rows_innerRightBAC HexagonRowColumn424.cols_left1)) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal4_case_2_4_row_2_0_2 : (((-1 : ℤ) ^ (leftScaleBit 4 2 4).val * positiveScale (leftScaleExponent 4 2 4)) •
      (rowColumnMul HexagonRowColumn424.rows_assocBAC HexagonRowColumn424.cols_left0)) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (negativeScale (leftScaleExponent 4 2 4) • (rowColumnMul HexagonRowColumn424.rows_innerRightBAC HexagonRowColumn424.cols_left1)) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal4_case_2_4_row_2_0_3 : (((-1 : ℤ) ^ (leftScaleBit 4 2 4).val * positiveScale (leftScaleExponent 4 2 4)) •
      (rowColumnMul HexagonRowColumn424.rows_assocBAC HexagonRowColumn424.cols_left0)) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (negativeScale (leftScaleExponent 4 2 4) • (rowColumnMul HexagonRowColumn424.rows_innerRightBAC HexagonRowColumn424.cols_left1)) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal4_case_2_4_row_3_0_0 : (((-1 : ℤ) ^ (leftScaleBit 4 2 4).val * positiveScale (leftScaleExponent 4 2 4)) •
      (rowColumnMul HexagonRowColumn424.rows_assocBAC HexagonRowColumn424.cols_left0)) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (negativeScale (leftScaleExponent 4 2 4) • (rowColumnMul HexagonRowColumn424.rows_innerRightBAC HexagonRowColumn424.cols_left1)) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal4_case_2_4_row_3_0_1 : (((-1 : ℤ) ^ (leftScaleBit 4 2 4).val * positiveScale (leftScaleExponent 4 2 4)) •
      (rowColumnMul HexagonRowColumn424.rows_assocBAC HexagonRowColumn424.cols_left0)) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (negativeScale (leftScaleExponent 4 2 4) • (rowColumnMul HexagonRowColumn424.rows_innerRightBAC HexagonRowColumn424.cols_left1)) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal4_case_2_4_row_3_0_2 : (((-1 : ℤ) ^ (leftScaleBit 4 2 4).val * positiveScale (leftScaleExponent 4 2 4)) •
      (rowColumnMul HexagonRowColumn424.rows_assocBAC HexagonRowColumn424.cols_left0)) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (negativeScale (leftScaleExponent 4 2 4) • (rowColumnMul HexagonRowColumn424.rows_innerRightBAC HexagonRowColumn424.cols_left1)) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal4_case_2_4_row_3_0_3 : (((-1 : ℤ) ^ (leftScaleBit 4 2 4).val * positiveScale (leftScaleExponent 4 2 4)) •
      (rowColumnMul HexagonRowColumn424.rows_assocBAC HexagonRowColumn424.cols_left0)) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (negativeScale (leftScaleExponent 4 2 4) • (rowColumnMul HexagonRowColumn424.rows_innerRightBAC HexagonRowColumn424.cols_left1)) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal4_case_2_4_checked : ((-1 : ℤ) ^ (leftScaleBit 4 2 4).val * positiveScale (leftScaleExponent 4 2 4)) •
      (rowColumnMul HexagonRowColumn424.rows_assocBAC HexagonRowColumn424.cols_left0) = negativeScale (leftScaleExponent 4 2 4) • (rowColumnMul HexagonRowColumn424.rows_innerRightBAC HexagonRowColumn424.cols_left1) := by
  funext r
  fin_cases r
  · exact leftFinal4_case_2_4_row_0_0_0
  · exact leftFinal4_case_2_4_row_0_0_1
  · exact leftFinal4_case_2_4_row_0_0_2
  · exact leftFinal4_case_2_4_row_0_0_3
  · exact leftFinal4_case_2_4_row_1_0_0
  · exact leftFinal4_case_2_4_row_1_0_1
  · exact leftFinal4_case_2_4_row_1_0_2
  · exact leftFinal4_case_2_4_row_1_0_3
  · exact leftFinal4_case_2_4_row_2_0_0
  · exact leftFinal4_case_2_4_row_2_0_1
  · exact leftFinal4_case_2_4_row_2_0_2
  · exact leftFinal4_case_2_4_row_2_0_3
  · exact leftFinal4_case_2_4_row_3_0_0
  · exact leftFinal4_case_2_4_row_3_0_1
  · exact leftFinal4_case_2_4_row_3_0_2
  · exact leftFinal4_case_2_4_row_3_0_3

set_option backward.isDefEq.respectTransparency false in
theorem leftFinal4_case_2_4 : ((-1 : ℤ) ^ (leftScaleBit 4 2 4).val * positiveScale (leftScaleExponent 4 2 4)) •
      (associatorZ 2 4 4 * left0Middle4 2 4) = negativeScale (leftScaleExponent 4 2 4) • (innerRightZ 2 4 4 * left1Middle4 2 4) := by
  simpa only [HexagonAtoms424.assocABC_eq,
    HexagonAtoms424.outerABC_eq,
    HexagonAtoms424.assocBAC_eq,
    HexagonAtoms424.innerABC_eq,
    HexagonAtoms424.innerRightABC_eq,
    HexagonAtoms424.inverseACB_eq,
    HexagonAtoms424.innerACB_eq,
    HexagonAtoms424.assocBCA_eq,
    HexagonAtoms424.innerRightBAC_eq,
    HexagonAtoms424.assocCAB_eq,
    HexagonAtoms424.outerLeftABC_eq,
    HexagonRowColumn424.assocBCA_alias,
    HexagonRowColumn424.product0_eq,
    HexagonRowColumn424.product1_eq,
    HexagonRowColumn424.product2_eq,
    HexagonRowColumn424.product3_eq,
    HexagonRowColumn424.product4_eq,
    HexagonRowColumn424.product5_eq,
    HexagonRowColumn424.product6_eq,
    HexagonRowColumn424.product7_eq] using leftFinal4_case_2_4_checked

private theorem rightFinal4_case_2_4_row_0_0_0 : (((-1 : ℤ) ^ (rightScaleBit 4 2 4).val * positiveScale (rightScaleExponent 4 2 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 4 2 : ℤ)) • HexagonAtoms424.outerLeftABC) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 4 2 4) • (rowColumnMul HexagonRowColumn424.rows_assocCAB HexagonRowColumn424.cols_right2)) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal4_case_2_4_row_0_0_1 : (((-1 : ℤ) ^ (rightScaleBit 4 2 4).val * positiveScale (rightScaleExponent 4 2 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 4 2 : ℤ)) • HexagonAtoms424.outerLeftABC) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 4 2 4) • (rowColumnMul HexagonRowColumn424.rows_assocCAB HexagonRowColumn424.cols_right2)) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal4_case_2_4_row_0_0_2 : (((-1 : ℤ) ^ (rightScaleBit 4 2 4).val * positiveScale (rightScaleExponent 4 2 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 4 2 : ℤ)) • HexagonAtoms424.outerLeftABC) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 4 2 4) • (rowColumnMul HexagonRowColumn424.rows_assocCAB HexagonRowColumn424.cols_right2)) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal4_case_2_4_row_0_0_3 : (((-1 : ℤ) ^ (rightScaleBit 4 2 4).val * positiveScale (rightScaleExponent 4 2 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 4 2 : ℤ)) • HexagonAtoms424.outerLeftABC) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 4 2 4) • (rowColumnMul HexagonRowColumn424.rows_assocCAB HexagonRowColumn424.cols_right2)) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal4_case_2_4_row_0_1_0 : (((-1 : ℤ) ^ (rightScaleBit 4 2 4).val * positiveScale (rightScaleExponent 4 2 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 4 2 : ℤ)) • HexagonAtoms424.outerLeftABC) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 4 2 4) • (rowColumnMul HexagonRowColumn424.rows_assocCAB HexagonRowColumn424.cols_right2)) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal4_case_2_4_row_0_1_1 : (((-1 : ℤ) ^ (rightScaleBit 4 2 4).val * positiveScale (rightScaleExponent 4 2 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 4 2 : ℤ)) • HexagonAtoms424.outerLeftABC) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 4 2 4) • (rowColumnMul HexagonRowColumn424.rows_assocCAB HexagonRowColumn424.cols_right2)) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal4_case_2_4_row_0_1_2 : (((-1 : ℤ) ^ (rightScaleBit 4 2 4).val * positiveScale (rightScaleExponent 4 2 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 4 2 : ℤ)) • HexagonAtoms424.outerLeftABC) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 4 2 4) • (rowColumnMul HexagonRowColumn424.rows_assocCAB HexagonRowColumn424.cols_right2)) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal4_case_2_4_row_0_1_3 : (((-1 : ℤ) ^ (rightScaleBit 4 2 4).val * positiveScale (rightScaleExponent 4 2 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 4 2 : ℤ)) • HexagonAtoms424.outerLeftABC) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 4 2 4) • (rowColumnMul HexagonRowColumn424.rows_assocCAB HexagonRowColumn424.cols_right2)) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal4_case_2_4_row_1_0_0 : (((-1 : ℤ) ^ (rightScaleBit 4 2 4).val * positiveScale (rightScaleExponent 4 2 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 4 2 : ℤ)) • HexagonAtoms424.outerLeftABC) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 4 2 4) • (rowColumnMul HexagonRowColumn424.rows_assocCAB HexagonRowColumn424.cols_right2)) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal4_case_2_4_row_1_0_1 : (((-1 : ℤ) ^ (rightScaleBit 4 2 4).val * positiveScale (rightScaleExponent 4 2 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 4 2 : ℤ)) • HexagonAtoms424.outerLeftABC) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 4 2 4) • (rowColumnMul HexagonRowColumn424.rows_assocCAB HexagonRowColumn424.cols_right2)) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal4_case_2_4_row_1_0_2 : (((-1 : ℤ) ^ (rightScaleBit 4 2 4).val * positiveScale (rightScaleExponent 4 2 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 4 2 : ℤ)) • HexagonAtoms424.outerLeftABC) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 4 2 4) • (rowColumnMul HexagonRowColumn424.rows_assocCAB HexagonRowColumn424.cols_right2)) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal4_case_2_4_row_1_0_3 : (((-1 : ℤ) ^ (rightScaleBit 4 2 4).val * positiveScale (rightScaleExponent 4 2 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 4 2 : ℤ)) • HexagonAtoms424.outerLeftABC) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 4 2 4) • (rowColumnMul HexagonRowColumn424.rows_assocCAB HexagonRowColumn424.cols_right2)) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal4_case_2_4_row_1_1_0 : (((-1 : ℤ) ^ (rightScaleBit 4 2 4).val * positiveScale (rightScaleExponent 4 2 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 4 2 : ℤ)) • HexagonAtoms424.outerLeftABC) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 4 2 4) • (rowColumnMul HexagonRowColumn424.rows_assocCAB HexagonRowColumn424.cols_right2)) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal4_case_2_4_row_1_1_1 : (((-1 : ℤ) ^ (rightScaleBit 4 2 4).val * positiveScale (rightScaleExponent 4 2 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 4 2 : ℤ)) • HexagonAtoms424.outerLeftABC) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 4 2 4) • (rowColumnMul HexagonRowColumn424.rows_assocCAB HexagonRowColumn424.cols_right2)) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal4_case_2_4_row_1_1_2 : (((-1 : ℤ) ^ (rightScaleBit 4 2 4).val * positiveScale (rightScaleExponent 4 2 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 4 2 : ℤ)) • HexagonAtoms424.outerLeftABC) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 4 2 4) • (rowColumnMul HexagonRowColumn424.rows_assocCAB HexagonRowColumn424.cols_right2)) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal4_case_2_4_row_1_1_3 : (((-1 : ℤ) ^ (rightScaleBit 4 2 4).val * positiveScale (rightScaleExponent 4 2 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 4 2 : ℤ)) • HexagonAtoms424.outerLeftABC) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 4 2 4) • (rowColumnMul HexagonRowColumn424.rows_assocCAB HexagonRowColumn424.cols_right2)) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 2) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal4_case_2_4_checked : ((-1 : ℤ) ^ (rightScaleBit 4 2 4).val * positiveScale (rightScaleExponent 4 2 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 4 2 : ℤ)) • HexagonAtoms424.outerLeftABC = negativeScale (rightScaleExponent 4 2 4) • (rowColumnMul HexagonRowColumn424.rows_assocCAB HexagonRowColumn424.cols_right2) := by
  funext r
  fin_cases r
  · exact rightFinal4_case_2_4_row_0_0_0
  · exact rightFinal4_case_2_4_row_0_0_1
  · exact rightFinal4_case_2_4_row_0_0_2
  · exact rightFinal4_case_2_4_row_0_0_3
  · exact rightFinal4_case_2_4_row_0_1_0
  · exact rightFinal4_case_2_4_row_0_1_1
  · exact rightFinal4_case_2_4_row_0_1_2
  · exact rightFinal4_case_2_4_row_0_1_3
  · exact rightFinal4_case_2_4_row_1_0_0
  · exact rightFinal4_case_2_4_row_1_0_1
  · exact rightFinal4_case_2_4_row_1_0_2
  · exact rightFinal4_case_2_4_row_1_0_3
  · exact rightFinal4_case_2_4_row_1_1_0
  · exact rightFinal4_case_2_4_row_1_1_1
  · exact rightFinal4_case_2_4_row_1_1_2
  · exact rightFinal4_case_2_4_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem rightFinal4_case_2_4 : ((-1 : ℤ) ^ (rightScaleBit 4 2 4).val * positiveScale (rightScaleExponent 4 2 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 4 2 : ℤ)) • outerLeftZ 4 2 4 = negativeScale (rightScaleExponent 4 2 4) • (associatorZ 4 4 2 * right2Middle4 2 4) := by
  simpa only [HexagonAtoms424.assocABC_eq,
    HexagonAtoms424.outerABC_eq,
    HexagonAtoms424.assocBAC_eq,
    HexagonAtoms424.innerABC_eq,
    HexagonAtoms424.innerRightABC_eq,
    HexagonAtoms424.inverseACB_eq,
    HexagonAtoms424.innerACB_eq,
    HexagonAtoms424.assocBCA_eq,
    HexagonAtoms424.innerRightBAC_eq,
    HexagonAtoms424.assocCAB_eq,
    HexagonAtoms424.outerLeftABC_eq,
    HexagonRowColumn424.assocBCA_alias,
    HexagonRowColumn424.product0_eq,
    HexagonRowColumn424.product1_eq,
    HexagonRowColumn424.product2_eq,
    HexagonRowColumn424.product3_eq,
    HexagonRowColumn424.product4_eq,
    HexagonRowColumn424.product5_eq,
    HexagonRowColumn424.product6_eq,
    HexagonRowColumn424.product7_eq] using rightFinal4_case_2_4_checked

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonCases4
