import RMod.BrundanEllis.StackingReferenceHexagonMiddle4
import RMod.BrundanEllis.StackingReferenceSparseMatrixCheck
import RMod.BrundanEllis.StackingReferenceHexagonAtoms473
import RMod.BrundanEllis.StackingReferenceHexagonRowColumn473

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

private theorem left0Middle4_eq_case_7_3_row_0_0_0 : (left0Middle4 7 3) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms473.assocABC) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_7_3_row_0_0_1 : (left0Middle4 7 3) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms473.assocABC) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_7_3_row_0_0_2 : (left0Middle4 7 3) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms473.assocABC) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_7_3_row_0_0_3 : (left0Middle4 7 3) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms473.assocABC) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_7_3_row_0_1_0 : (left0Middle4 7 3) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms473.assocABC) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_7_3_row_0_1_1 : (left0Middle4 7 3) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms473.assocABC) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_7_3_row_0_1_2 : (left0Middle4 7 3) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms473.assocABC) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_7_3_row_0_1_3 : (left0Middle4 7 3) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms473.assocABC) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_7_3_row_1_0_0 : (left0Middle4 7 3) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms473.assocABC) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_7_3_row_1_0_1 : (left0Middle4 7 3) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms473.assocABC) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_7_3_row_1_0_2 : (left0Middle4 7 3) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms473.assocABC) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_7_3_row_1_0_3 : (left0Middle4 7 3) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms473.assocABC) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_7_3_row_1_1_0 : (left0Middle4 7 3) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms473.assocABC) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_7_3_row_1_1_1 : (left0Middle4 7 3) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms473.assocABC) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_7_3_row_1_1_2 : (left0Middle4 7 3) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms473.assocABC) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_7_3_row_1_1_3 : (left0Middle4 7 3) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms473.assocABC) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_7_3_checked : left0Middle4 7 3 = HexagonAtoms473.assocABC := by
  funext r
  fin_cases r
  · exact left0Middle4_eq_case_7_3_row_0_0_0
  · exact left0Middle4_eq_case_7_3_row_0_0_1
  · exact left0Middle4_eq_case_7_3_row_0_0_2
  · exact left0Middle4_eq_case_7_3_row_0_0_3
  · exact left0Middle4_eq_case_7_3_row_0_1_0
  · exact left0Middle4_eq_case_7_3_row_0_1_1
  · exact left0Middle4_eq_case_7_3_row_0_1_2
  · exact left0Middle4_eq_case_7_3_row_0_1_3
  · exact left0Middle4_eq_case_7_3_row_1_0_0
  · exact left0Middle4_eq_case_7_3_row_1_0_1
  · exact left0Middle4_eq_case_7_3_row_1_0_2
  · exact left0Middle4_eq_case_7_3_row_1_0_3
  · exact left0Middle4_eq_case_7_3_row_1_1_0
  · exact left0Middle4_eq_case_7_3_row_1_1_1
  · exact left0Middle4_eq_case_7_3_row_1_1_2
  · exact left0Middle4_eq_case_7_3_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem left0Middle4_eq_case_7_3 : left0Middle4 7 3 = outerRightZ 4 7 3 * associatorZ 4 7 3 := by
  simpa only [HexagonAtoms473.assocABC_eq,
    HexagonAtoms473.outerABC_eq,
    HexagonAtoms473.assocBAC_eq,
    HexagonAtoms473.innerABC_eq,
    HexagonAtoms473.innerRightABC_eq,
    HexagonAtoms473.inverseACB_eq,
    HexagonAtoms473.innerACB_eq,
    HexagonAtoms473.assocBCA_eq,
    HexagonAtoms473.innerRightBAC_eq,
    HexagonAtoms473.assocCAB_eq,
    HexagonAtoms473.outerLeftABC_eq,
    HexagonRowColumn473.product0_eq,
    HexagonRowColumn473.product1_eq,
    HexagonRowColumn473.product2_eq,
    HexagonRowColumn473.product3_eq,
    HexagonRowColumn473.product4_eq,
    HexagonRowColumn473.product5_eq,
    HexagonRowColumn473.product6_eq,
    HexagonRowColumn473.product7_eq] using left0Middle4_eq_case_7_3_checked

private theorem left1Middle4_eq_case_7_3_row_0_0_0 : (left1Middle4 7 3) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms473.assocBAC) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_7_3_row_0_0_1 : (left1Middle4 7 3) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms473.assocBAC) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_7_3_row_0_0_2 : (left1Middle4 7 3) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms473.assocBAC) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_7_3_row_0_0_3 : (left1Middle4 7 3) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms473.assocBAC) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_7_3_row_1_0_0 : (left1Middle4 7 3) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms473.assocBAC) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_7_3_row_1_0_1 : (left1Middle4 7 3) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms473.assocBAC) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_7_3_row_1_0_2 : (left1Middle4 7 3) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms473.assocBAC) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_7_3_row_1_0_3 : (left1Middle4 7 3) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms473.assocBAC) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_7_3_row_2_0_0 : (left1Middle4 7 3) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms473.assocBAC) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_7_3_row_2_0_1 : (left1Middle4 7 3) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms473.assocBAC) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_7_3_row_2_0_2 : (left1Middle4 7 3) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms473.assocBAC) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_7_3_row_2_0_3 : (left1Middle4 7 3) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms473.assocBAC) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_7_3_row_3_0_0 : (left1Middle4 7 3) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms473.assocBAC) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_7_3_row_3_0_1 : (left1Middle4 7 3) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms473.assocBAC) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_7_3_row_3_0_2 : (left1Middle4 7 3) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms473.assocBAC) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_7_3_row_3_0_3 : (left1Middle4 7 3) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms473.assocBAC) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_7_3_checked : left1Middle4 7 3 = HexagonAtoms473.assocBAC := by
  funext r
  fin_cases r
  · exact left1Middle4_eq_case_7_3_row_0_0_0
  · exact left1Middle4_eq_case_7_3_row_0_0_1
  · exact left1Middle4_eq_case_7_3_row_0_0_2
  · exact left1Middle4_eq_case_7_3_row_0_0_3
  · exact left1Middle4_eq_case_7_3_row_1_0_0
  · exact left1Middle4_eq_case_7_3_row_1_0_1
  · exact left1Middle4_eq_case_7_3_row_1_0_2
  · exact left1Middle4_eq_case_7_3_row_1_0_3
  · exact left1Middle4_eq_case_7_3_row_2_0_0
  · exact left1Middle4_eq_case_7_3_row_2_0_1
  · exact left1Middle4_eq_case_7_3_row_2_0_2
  · exact left1Middle4_eq_case_7_3_row_2_0_3
  · exact left1Middle4_eq_case_7_3_row_3_0_0
  · exact left1Middle4_eq_case_7_3_row_3_0_1
  · exact left1Middle4_eq_case_7_3_row_3_0_2
  · exact left1Middle4_eq_case_7_3_row_3_0_3

set_option backward.isDefEq.respectTransparency false in
theorem left1Middle4_eq_case_7_3 : left1Middle4 7 3 = associatorZ 7 4 3 * innerLeftZ 4 7 3 := by
  simpa only [HexagonAtoms473.assocABC_eq,
    HexagonAtoms473.outerABC_eq,
    HexagonAtoms473.assocBAC_eq,
    HexagonAtoms473.innerABC_eq,
    HexagonAtoms473.innerRightABC_eq,
    HexagonAtoms473.inverseACB_eq,
    HexagonAtoms473.innerACB_eq,
    HexagonAtoms473.assocBCA_eq,
    HexagonAtoms473.innerRightBAC_eq,
    HexagonAtoms473.assocCAB_eq,
    HexagonAtoms473.outerLeftABC_eq,
    HexagonRowColumn473.product0_eq,
    HexagonRowColumn473.product1_eq,
    HexagonRowColumn473.product2_eq,
    HexagonRowColumn473.product3_eq,
    HexagonRowColumn473.product4_eq,
    HexagonRowColumn473.product5_eq,
    HexagonRowColumn473.product6_eq,
    HexagonRowColumn473.product7_eq] using left1Middle4_eq_case_7_3_checked

private theorem right0Middle4_eq_case_7_3_row_0_0_0 : (right0Middle4 7 3) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms473.assocABC) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_7_3_row_0_0_1 : (right0Middle4 7 3) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms473.assocABC) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_7_3_row_0_0_2 : (right0Middle4 7 3) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms473.assocABC) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_7_3_row_0_0_3 : (right0Middle4 7 3) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms473.assocABC) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_7_3_row_0_1_0 : (right0Middle4 7 3) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms473.assocABC) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_7_3_row_0_1_1 : (right0Middle4 7 3) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms473.assocABC) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_7_3_row_0_1_2 : (right0Middle4 7 3) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms473.assocABC) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_7_3_row_0_1_3 : (right0Middle4 7 3) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms473.assocABC) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_7_3_row_1_0_0 : (right0Middle4 7 3) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms473.assocABC) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_7_3_row_1_0_1 : (right0Middle4 7 3) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms473.assocABC) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_7_3_row_1_0_2 : (right0Middle4 7 3) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms473.assocABC) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_7_3_row_1_0_3 : (right0Middle4 7 3) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms473.assocABC) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_7_3_row_1_1_0 : (right0Middle4 7 3) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms473.assocABC) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_7_3_row_1_1_1 : (right0Middle4 7 3) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms473.assocABC) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_7_3_row_1_1_2 : (right0Middle4 7 3) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms473.assocABC) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_7_3_row_1_1_3 : (right0Middle4 7 3) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms473.assocABC) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_7_3_checked : right0Middle4 7 3 = HexagonAtoms473.assocABC := by
  funext r
  fin_cases r
  · exact right0Middle4_eq_case_7_3_row_0_0_0
  · exact right0Middle4_eq_case_7_3_row_0_0_1
  · exact right0Middle4_eq_case_7_3_row_0_0_2
  · exact right0Middle4_eq_case_7_3_row_0_0_3
  · exact right0Middle4_eq_case_7_3_row_0_1_0
  · exact right0Middle4_eq_case_7_3_row_0_1_1
  · exact right0Middle4_eq_case_7_3_row_0_1_2
  · exact right0Middle4_eq_case_7_3_row_0_1_3
  · exact right0Middle4_eq_case_7_3_row_1_0_0
  · exact right0Middle4_eq_case_7_3_row_1_0_1
  · exact right0Middle4_eq_case_7_3_row_1_0_2
  · exact right0Middle4_eq_case_7_3_row_1_0_3
  · exact right0Middle4_eq_case_7_3_row_1_1_0
  · exact right0Middle4_eq_case_7_3_row_1_1_1
  · exact right0Middle4_eq_case_7_3_row_1_1_2
  · exact right0Middle4_eq_case_7_3_row_1_1_3

set_option backward.isDefEq.respectTransparency false in
theorem right0Middle4_eq_case_7_3 : right0Middle4 7 3 = innerRightZ 4 7 3 * associatorZ 4 7 3 := by
  simpa only [HexagonAtoms473.assocABC_eq,
    HexagonAtoms473.outerABC_eq,
    HexagonAtoms473.assocBAC_eq,
    HexagonAtoms473.innerABC_eq,
    HexagonAtoms473.innerRightABC_eq,
    HexagonAtoms473.inverseACB_eq,
    HexagonAtoms473.innerACB_eq,
    HexagonAtoms473.assocBCA_eq,
    HexagonAtoms473.innerRightBAC_eq,
    HexagonAtoms473.assocCAB_eq,
    HexagonAtoms473.outerLeftABC_eq,
    HexagonRowColumn473.product0_eq,
    HexagonRowColumn473.product1_eq,
    HexagonRowColumn473.product2_eq,
    HexagonRowColumn473.product3_eq,
    HexagonRowColumn473.product4_eq,
    HexagonRowColumn473.product5_eq,
    HexagonRowColumn473.product6_eq,
    HexagonRowColumn473.product7_eq] using right0Middle4_eq_case_7_3_checked

private theorem right1Middle4_eq_case_7_3_row_0_0_0 : (right1Middle4 7 3) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn473.rows_inverseACB HexagonRowColumn473.cols_right0) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_7_3_row_0_0_1 : (right1Middle4 7 3) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn473.rows_inverseACB HexagonRowColumn473.cols_right0) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_7_3_row_0_0_2 : (right1Middle4 7 3) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn473.rows_inverseACB HexagonRowColumn473.cols_right0) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_7_3_row_0_0_3 : (right1Middle4 7 3) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn473.rows_inverseACB HexagonRowColumn473.cols_right0) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_7_3_row_1_0_0 : (right1Middle4 7 3) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn473.rows_inverseACB HexagonRowColumn473.cols_right0) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_7_3_row_1_0_1 : (right1Middle4 7 3) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn473.rows_inverseACB HexagonRowColumn473.cols_right0) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_7_3_row_1_0_2 : (right1Middle4 7 3) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn473.rows_inverseACB HexagonRowColumn473.cols_right0) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_7_3_row_1_0_3 : (right1Middle4 7 3) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn473.rows_inverseACB HexagonRowColumn473.cols_right0) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_7_3_row_2_0_0 : (right1Middle4 7 3) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn473.rows_inverseACB HexagonRowColumn473.cols_right0) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_7_3_row_2_0_1 : (right1Middle4 7 3) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn473.rows_inverseACB HexagonRowColumn473.cols_right0) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_7_3_row_2_0_2 : (right1Middle4 7 3) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn473.rows_inverseACB HexagonRowColumn473.cols_right0) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_7_3_row_2_0_3 : (right1Middle4 7 3) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn473.rows_inverseACB HexagonRowColumn473.cols_right0) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_7_3_row_3_0_0 : (right1Middle4 7 3) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn473.rows_inverseACB HexagonRowColumn473.cols_right0) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_7_3_row_3_0_1 : (right1Middle4 7 3) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn473.rows_inverseACB HexagonRowColumn473.cols_right0) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_7_3_row_3_0_2 : (right1Middle4 7 3) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn473.rows_inverseACB HexagonRowColumn473.cols_right0) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_7_3_row_3_0_3 : (right1Middle4 7 3) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn473.rows_inverseACB HexagonRowColumn473.cols_right0) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_7_3_checked : right1Middle4 7 3 = rowColumnMul HexagonRowColumn473.rows_inverseACB HexagonRowColumn473.cols_right0 := by
  funext r
  fin_cases r
  · exact right1Middle4_eq_case_7_3_row_0_0_0
  · exact right1Middle4_eq_case_7_3_row_0_0_1
  · exact right1Middle4_eq_case_7_3_row_0_0_2
  · exact right1Middle4_eq_case_7_3_row_0_0_3
  · exact right1Middle4_eq_case_7_3_row_1_0_0
  · exact right1Middle4_eq_case_7_3_row_1_0_1
  · exact right1Middle4_eq_case_7_3_row_1_0_2
  · exact right1Middle4_eq_case_7_3_row_1_0_3
  · exact right1Middle4_eq_case_7_3_row_2_0_0
  · exact right1Middle4_eq_case_7_3_row_2_0_1
  · exact right1Middle4_eq_case_7_3_row_2_0_2
  · exact right1Middle4_eq_case_7_3_row_2_0_3
  · exact right1Middle4_eq_case_7_3_row_3_0_0
  · exact right1Middle4_eq_case_7_3_row_3_0_1
  · exact right1Middle4_eq_case_7_3_row_3_0_2
  · exact right1Middle4_eq_case_7_3_row_3_0_3

set_option backward.isDefEq.respectTransparency false in
theorem right1Middle4_eq_case_7_3 : right1Middle4 7 3 = associatorInverseZ 4 3 7 * right0Middle4 7 3 := by
  simpa only [HexagonAtoms473.assocABC_eq,
    HexagonAtoms473.outerABC_eq,
    HexagonAtoms473.assocBAC_eq,
    HexagonAtoms473.innerABC_eq,
    HexagonAtoms473.innerRightABC_eq,
    HexagonAtoms473.inverseACB_eq,
    HexagonAtoms473.innerACB_eq,
    HexagonAtoms473.assocBCA_eq,
    HexagonAtoms473.innerRightBAC_eq,
    HexagonAtoms473.assocCAB_eq,
    HexagonAtoms473.outerLeftABC_eq,
    HexagonRowColumn473.product0_eq,
    HexagonRowColumn473.product1_eq,
    HexagonRowColumn473.product2_eq,
    HexagonRowColumn473.product3_eq,
    HexagonRowColumn473.product4_eq,
    HexagonRowColumn473.product5_eq,
    HexagonRowColumn473.product6_eq,
    HexagonRowColumn473.product7_eq] using right1Middle4_eq_case_7_3_checked

private theorem right2Middle4_eq_case_7_3_row_0_0_0 : (right2Middle4 7 3) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (right1Middle4 7 3) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_7_3_row_0_0_1 : (right2Middle4 7 3) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (right1Middle4 7 3) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_7_3_row_0_0_2 : (right2Middle4 7 3) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (right1Middle4 7 3) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_7_3_row_0_0_3 : (right2Middle4 7 3) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (right1Middle4 7 3) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_7_3_row_1_0_0 : (right2Middle4 7 3) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (right1Middle4 7 3) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_7_3_row_1_0_1 : (right2Middle4 7 3) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (right1Middle4 7 3) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_7_3_row_1_0_2 : (right2Middle4 7 3) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (right1Middle4 7 3) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_7_3_row_1_0_3 : (right2Middle4 7 3) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (right1Middle4 7 3) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_7_3_row_2_0_0 : (right2Middle4 7 3) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (right1Middle4 7 3) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_7_3_row_2_0_1 : (right2Middle4 7 3) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (right1Middle4 7 3) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_7_3_row_2_0_2 : (right2Middle4 7 3) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (right1Middle4 7 3) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_7_3_row_2_0_3 : (right2Middle4 7 3) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (right1Middle4 7 3) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_7_3_row_3_0_0 : (right2Middle4 7 3) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (right1Middle4 7 3) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_7_3_row_3_0_1 : (right2Middle4 7 3) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (right1Middle4 7 3) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_7_3_row_3_0_2 : (right2Middle4 7 3) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (right1Middle4 7 3) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_7_3_row_3_0_3 : (right2Middle4 7 3) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (right1Middle4 7 3) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_7_3_checked : right2Middle4 7 3 = right1Middle4 7 3 := by
  funext r
  fin_cases r
  · exact right2Middle4_eq_case_7_3_row_0_0_0
  · exact right2Middle4_eq_case_7_3_row_0_0_1
  · exact right2Middle4_eq_case_7_3_row_0_0_2
  · exact right2Middle4_eq_case_7_3_row_0_0_3
  · exact right2Middle4_eq_case_7_3_row_1_0_0
  · exact right2Middle4_eq_case_7_3_row_1_0_1
  · exact right2Middle4_eq_case_7_3_row_1_0_2
  · exact right2Middle4_eq_case_7_3_row_1_0_3
  · exact right2Middle4_eq_case_7_3_row_2_0_0
  · exact right2Middle4_eq_case_7_3_row_2_0_1
  · exact right2Middle4_eq_case_7_3_row_2_0_2
  · exact right2Middle4_eq_case_7_3_row_2_0_3
  · exact right2Middle4_eq_case_7_3_row_3_0_0
  · exact right2Middle4_eq_case_7_3_row_3_0_1
  · exact right2Middle4_eq_case_7_3_row_3_0_2
  · exact right2Middle4_eq_case_7_3_row_3_0_3

set_option backward.isDefEq.respectTransparency false in
theorem right2Middle4_eq_case_7_3 : right2Middle4 7 3 = innerLeftZ 4 3 7 * right1Middle4 7 3 := by
  simpa only [HexagonAtoms473.assocABC_eq,
    HexagonAtoms473.outerABC_eq,
    HexagonAtoms473.assocBAC_eq,
    HexagonAtoms473.innerABC_eq,
    HexagonAtoms473.innerRightABC_eq,
    HexagonAtoms473.inverseACB_eq,
    HexagonAtoms473.innerACB_eq,
    HexagonAtoms473.assocBCA_eq,
    HexagonAtoms473.innerRightBAC_eq,
    HexagonAtoms473.assocCAB_eq,
    HexagonAtoms473.outerLeftABC_eq,
    HexagonRowColumn473.product0_eq,
    HexagonRowColumn473.product1_eq,
    HexagonRowColumn473.product2_eq,
    HexagonRowColumn473.product3_eq,
    HexagonRowColumn473.product4_eq,
    HexagonRowColumn473.product5_eq,
    HexagonRowColumn473.product6_eq,
    HexagonRowColumn473.product7_eq] using right2Middle4_eq_case_7_3_checked

private theorem leftFinal4_case_7_3_row_0_0_0 : (((-1 : ℤ) ^ (leftScaleBit 4 7 3).val * positiveScale (leftScaleExponent 4 7 3)) •
      (rowColumnMul HexagonRowColumn473.rows_assocBCA HexagonRowColumn473.cols_left0)) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (negativeScale (leftScaleExponent 4 7 3) • (left1Middle4 7 3)) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem leftFinal4_case_7_3_row_0_0_1 : (((-1 : ℤ) ^ (leftScaleBit 4 7 3).val * positiveScale (leftScaleExponent 4 7 3)) •
      (rowColumnMul HexagonRowColumn473.rows_assocBCA HexagonRowColumn473.cols_left0)) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (negativeScale (leftScaleExponent 4 7 3) • (left1Middle4 7 3)) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem leftFinal4_case_7_3_row_0_0_2 : (((-1 : ℤ) ^ (leftScaleBit 4 7 3).val * positiveScale (leftScaleExponent 4 7 3)) •
      (rowColumnMul HexagonRowColumn473.rows_assocBCA HexagonRowColumn473.cols_left0)) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (negativeScale (leftScaleExponent 4 7 3) • (left1Middle4 7 3)) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem leftFinal4_case_7_3_row_0_0_3 : (((-1 : ℤ) ^ (leftScaleBit 4 7 3).val * positiveScale (leftScaleExponent 4 7 3)) •
      (rowColumnMul HexagonRowColumn473.rows_assocBCA HexagonRowColumn473.cols_left0)) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (negativeScale (leftScaleExponent 4 7 3) • (left1Middle4 7 3)) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem leftFinal4_case_7_3_row_1_0_0 : (((-1 : ℤ) ^ (leftScaleBit 4 7 3).val * positiveScale (leftScaleExponent 4 7 3)) •
      (rowColumnMul HexagonRowColumn473.rows_assocBCA HexagonRowColumn473.cols_left0)) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (negativeScale (leftScaleExponent 4 7 3) • (left1Middle4 7 3)) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem leftFinal4_case_7_3_row_1_0_1 : (((-1 : ℤ) ^ (leftScaleBit 4 7 3).val * positiveScale (leftScaleExponent 4 7 3)) •
      (rowColumnMul HexagonRowColumn473.rows_assocBCA HexagonRowColumn473.cols_left0)) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (negativeScale (leftScaleExponent 4 7 3) • (left1Middle4 7 3)) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem leftFinal4_case_7_3_row_1_0_2 : (((-1 : ℤ) ^ (leftScaleBit 4 7 3).val * positiveScale (leftScaleExponent 4 7 3)) •
      (rowColumnMul HexagonRowColumn473.rows_assocBCA HexagonRowColumn473.cols_left0)) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (negativeScale (leftScaleExponent 4 7 3) • (left1Middle4 7 3)) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem leftFinal4_case_7_3_row_1_0_3 : (((-1 : ℤ) ^ (leftScaleBit 4 7 3).val * positiveScale (leftScaleExponent 4 7 3)) •
      (rowColumnMul HexagonRowColumn473.rows_assocBCA HexagonRowColumn473.cols_left0)) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (negativeScale (leftScaleExponent 4 7 3) • (left1Middle4 7 3)) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem leftFinal4_case_7_3_row_2_0_0 : (((-1 : ℤ) ^ (leftScaleBit 4 7 3).val * positiveScale (leftScaleExponent 4 7 3)) •
      (rowColumnMul HexagonRowColumn473.rows_assocBCA HexagonRowColumn473.cols_left0)) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (negativeScale (leftScaleExponent 4 7 3) • (left1Middle4 7 3)) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem leftFinal4_case_7_3_row_2_0_1 : (((-1 : ℤ) ^ (leftScaleBit 4 7 3).val * positiveScale (leftScaleExponent 4 7 3)) •
      (rowColumnMul HexagonRowColumn473.rows_assocBCA HexagonRowColumn473.cols_left0)) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (negativeScale (leftScaleExponent 4 7 3) • (left1Middle4 7 3)) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem leftFinal4_case_7_3_row_2_0_2 : (((-1 : ℤ) ^ (leftScaleBit 4 7 3).val * positiveScale (leftScaleExponent 4 7 3)) •
      (rowColumnMul HexagonRowColumn473.rows_assocBCA HexagonRowColumn473.cols_left0)) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (negativeScale (leftScaleExponent 4 7 3) • (left1Middle4 7 3)) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem leftFinal4_case_7_3_row_2_0_3 : (((-1 : ℤ) ^ (leftScaleBit 4 7 3).val * positiveScale (leftScaleExponent 4 7 3)) •
      (rowColumnMul HexagonRowColumn473.rows_assocBCA HexagonRowColumn473.cols_left0)) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (negativeScale (leftScaleExponent 4 7 3) • (left1Middle4 7 3)) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem leftFinal4_case_7_3_row_3_0_0 : (((-1 : ℤ) ^ (leftScaleBit 4 7 3).val * positiveScale (leftScaleExponent 4 7 3)) •
      (rowColumnMul HexagonRowColumn473.rows_assocBCA HexagonRowColumn473.cols_left0)) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) = (negativeScale (leftScaleExponent 4 7 3) • (left1Middle4 7 3)) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem leftFinal4_case_7_3_row_3_0_1 : (((-1 : ℤ) ^ (leftScaleBit 4 7 3).val * positiveScale (leftScaleExponent 4 7 3)) •
      (rowColumnMul HexagonRowColumn473.rows_assocBCA HexagonRowColumn473.cols_left0)) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) = (negativeScale (leftScaleExponent 4 7 3) • (left1Middle4 7 3)) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem leftFinal4_case_7_3_row_3_0_2 : (((-1 : ℤ) ^ (leftScaleBit 4 7 3).val * positiveScale (leftScaleExponent 4 7 3)) •
      (rowColumnMul HexagonRowColumn473.rows_assocBCA HexagonRowColumn473.cols_left0)) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) = (negativeScale (leftScaleExponent 4 7 3) • (left1Middle4 7 3)) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem leftFinal4_case_7_3_row_3_0_3 : (((-1 : ℤ) ^ (leftScaleBit 4 7 3).val * positiveScale (leftScaleExponent 4 7 3)) •
      (rowColumnMul HexagonRowColumn473.rows_assocBCA HexagonRowColumn473.cols_left0)) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) = (negativeScale (leftScaleExponent 4 7 3) • (left1Middle4 7 3)) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem leftFinal4_case_7_3_checked : ((-1 : ℤ) ^ (leftScaleBit 4 7 3).val * positiveScale (leftScaleExponent 4 7 3)) •
      (rowColumnMul HexagonRowColumn473.rows_assocBCA HexagonRowColumn473.cols_left0) = negativeScale (leftScaleExponent 4 7 3) • (left1Middle4 7 3) := by
  funext r
  fin_cases r
  · exact leftFinal4_case_7_3_row_0_0_0
  · exact leftFinal4_case_7_3_row_0_0_1
  · exact leftFinal4_case_7_3_row_0_0_2
  · exact leftFinal4_case_7_3_row_0_0_3
  · exact leftFinal4_case_7_3_row_1_0_0
  · exact leftFinal4_case_7_3_row_1_0_1
  · exact leftFinal4_case_7_3_row_1_0_2
  · exact leftFinal4_case_7_3_row_1_0_3
  · exact leftFinal4_case_7_3_row_2_0_0
  · exact leftFinal4_case_7_3_row_2_0_1
  · exact leftFinal4_case_7_3_row_2_0_2
  · exact leftFinal4_case_7_3_row_2_0_3
  · exact leftFinal4_case_7_3_row_3_0_0
  · exact leftFinal4_case_7_3_row_3_0_1
  · exact leftFinal4_case_7_3_row_3_0_2
  · exact leftFinal4_case_7_3_row_3_0_3

set_option backward.isDefEq.respectTransparency false in
theorem leftFinal4_case_7_3 : ((-1 : ℤ) ^ (leftScaleBit 4 7 3).val * positiveScale (leftScaleExponent 4 7 3)) •
      (associatorZ 7 3 4 * left0Middle4 7 3) = negativeScale (leftScaleExponent 4 7 3) • (innerRightZ 7 4 3 * left1Middle4 7 3) := by
  simpa only [HexagonAtoms473.assocABC_eq,
    HexagonAtoms473.outerABC_eq,
    HexagonAtoms473.assocBAC_eq,
    HexagonAtoms473.innerABC_eq,
    HexagonAtoms473.innerRightABC_eq,
    HexagonAtoms473.inverseACB_eq,
    HexagonAtoms473.innerACB_eq,
    HexagonAtoms473.assocBCA_eq,
    HexagonAtoms473.innerRightBAC_eq,
    HexagonAtoms473.assocCAB_eq,
    HexagonAtoms473.outerLeftABC_eq,
    HexagonRowColumn473.product0_eq,
    HexagonRowColumn473.product1_eq,
    HexagonRowColumn473.product2_eq,
    HexagonRowColumn473.product3_eq,
    HexagonRowColumn473.product4_eq,
    HexagonRowColumn473.product5_eq,
    HexagonRowColumn473.product6_eq,
    HexagonRowColumn473.product7_eq] using leftFinal4_case_7_3_checked

private theorem rightFinal4_case_7_3_row_0_0_0 : (((-1 : ℤ) ^ (rightScaleBit 4 7 3).val * positiveScale (rightScaleExponent 4 7 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 3 7 : ℤ)) • HexagonAtoms473.outerLeftABC) ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4)) = (negativeScale (rightScaleExponent 4 7 3) • (rowColumnMul HexagonRowColumn473.rows_assocCAB HexagonRowColumn473.cols_right2)) ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem rightFinal4_case_7_3_row_0_0_1 : (((-1 : ℤ) ^ (rightScaleBit 4 7 3).val * positiveScale (rightScaleExponent 4 7 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 3 7 : ℤ)) • HexagonAtoms473.outerLeftABC) ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4)) = (negativeScale (rightScaleExponent 4 7 3) • (rowColumnMul HexagonRowColumn473.rows_assocCAB HexagonRowColumn473.cols_right2)) ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem rightFinal4_case_7_3_row_0_0_2 : (((-1 : ℤ) ^ (rightScaleBit 4 7 3).val * positiveScale (rightScaleExponent 4 7 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 3 7 : ℤ)) • HexagonAtoms473.outerLeftABC) ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4)) = (negativeScale (rightScaleExponent 4 7 3) • (rowColumnMul HexagonRowColumn473.rows_assocCAB HexagonRowColumn473.cols_right2)) ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem rightFinal4_case_7_3_row_0_0_3 : (((-1 : ℤ) ^ (rightScaleBit 4 7 3).val * positiveScale (rightScaleExponent 4 7 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 3 7 : ℤ)) • HexagonAtoms473.outerLeftABC) ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4)) = (negativeScale (rightScaleExponent 4 7 3) • (rowColumnMul HexagonRowColumn473.rows_assocCAB HexagonRowColumn473.cols_right2)) ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem rightFinal4_case_7_3_row_0_1_0 : (((-1 : ℤ) ^ (rightScaleBit 4 7 3).val * positiveScale (rightScaleExponent 4 7 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 3 7 : ℤ)) • HexagonAtoms473.outerLeftABC) ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4)) = (negativeScale (rightScaleExponent 4 7 3) • (rowColumnMul HexagonRowColumn473.rows_assocCAB HexagonRowColumn473.cols_right2)) ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem rightFinal4_case_7_3_row_0_1_1 : (((-1 : ℤ) ^ (rightScaleBit 4 7 3).val * positiveScale (rightScaleExponent 4 7 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 3 7 : ℤ)) • HexagonAtoms473.outerLeftABC) ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4)) = (negativeScale (rightScaleExponent 4 7 3) • (rowColumnMul HexagonRowColumn473.rows_assocCAB HexagonRowColumn473.cols_right2)) ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem rightFinal4_case_7_3_row_0_1_2 : (((-1 : ℤ) ^ (rightScaleBit 4 7 3).val * positiveScale (rightScaleExponent 4 7 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 3 7 : ℤ)) • HexagonAtoms473.outerLeftABC) ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4)) = (negativeScale (rightScaleExponent 4 7 3) • (rowColumnMul HexagonRowColumn473.rows_assocCAB HexagonRowColumn473.cols_right2)) ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem rightFinal4_case_7_3_row_0_1_3 : (((-1 : ℤ) ^ (rightScaleBit 4 7 3).val * positiveScale (rightScaleExponent 4 7 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 3 7 : ℤ)) • HexagonAtoms473.outerLeftABC) ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4)) = (negativeScale (rightScaleExponent 4 7 3) • (rowColumnMul HexagonRowColumn473.rows_assocCAB HexagonRowColumn473.cols_right2)) ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem rightFinal4_case_7_3_row_0_2_0 : (((-1 : ℤ) ^ (rightScaleBit 4 7 3).val * positiveScale (rightScaleExponent 4 7 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 3 7 : ℤ)) • HexagonAtoms473.outerLeftABC) ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4)) = (negativeScale (rightScaleExponent 4 7 3) • (rowColumnMul HexagonRowColumn473.rows_assocCAB HexagonRowColumn473.cols_right2)) ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem rightFinal4_case_7_3_row_0_2_1 : (((-1 : ℤ) ^ (rightScaleBit 4 7 3).val * positiveScale (rightScaleExponent 4 7 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 3 7 : ℤ)) • HexagonAtoms473.outerLeftABC) ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4)) = (negativeScale (rightScaleExponent 4 7 3) • (rowColumnMul HexagonRowColumn473.rows_assocCAB HexagonRowColumn473.cols_right2)) ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem rightFinal4_case_7_3_row_0_2_2 : (((-1 : ℤ) ^ (rightScaleBit 4 7 3).val * positiveScale (rightScaleExponent 4 7 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 3 7 : ℤ)) • HexagonAtoms473.outerLeftABC) ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4)) = (negativeScale (rightScaleExponent 4 7 3) • (rowColumnMul HexagonRowColumn473.rows_assocCAB HexagonRowColumn473.cols_right2)) ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem rightFinal4_case_7_3_row_0_2_3 : (((-1 : ℤ) ^ (rightScaleBit 4 7 3).val * positiveScale (rightScaleExponent 4 7 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 3 7 : ℤ)) • HexagonAtoms473.outerLeftABC) ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4)) = (negativeScale (rightScaleExponent 4 7 3) • (rowColumnMul HexagonRowColumn473.rows_assocCAB HexagonRowColumn473.cols_right2)) ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem rightFinal4_case_7_3_row_0_3_0 : (((-1 : ℤ) ^ (rightScaleBit 4 7 3).val * positiveScale (rightScaleExponent 4 7 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 3 7 : ℤ)) • HexagonAtoms473.outerLeftABC) ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4)) = (negativeScale (rightScaleExponent 4 7 3) • (rowColumnMul HexagonRowColumn473.rows_assocCAB HexagonRowColumn473.cols_right2)) ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem rightFinal4_case_7_3_row_0_3_1 : (((-1 : ℤ) ^ (rightScaleBit 4 7 3).val * positiveScale (rightScaleExponent 4 7 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 3 7 : ℤ)) • HexagonAtoms473.outerLeftABC) ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4)) = (negativeScale (rightScaleExponent 4 7 3) • (rowColumnMul HexagonRowColumn473.rows_assocCAB HexagonRowColumn473.cols_right2)) ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem rightFinal4_case_7_3_row_0_3_2 : (((-1 : ℤ) ^ (rightScaleBit 4 7 3).val * positiveScale (rightScaleExponent 4 7 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 3 7 : ℤ)) • HexagonAtoms473.outerLeftABC) ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4)) = (negativeScale (rightScaleExponent 4 7 3) • (rowColumnMul HexagonRowColumn473.rows_assocCAB HexagonRowColumn473.cols_right2)) ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem rightFinal4_case_7_3_row_0_3_3 : (((-1 : ℤ) ^ (rightScaleBit 4 7 3).val * positiveScale (rightScaleExponent 4 7 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 3 7 : ℤ)) • HexagonAtoms473.outerLeftABC) ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4)) = (negativeScale (rightScaleExponent 4 7 3) • (rowColumnMul HexagonRowColumn473.rows_assocCAB HexagonRowColumn473.cols_right2)) ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 1) (b := 4) (c := 4)
  decide +kernel

private theorem rightFinal4_case_7_3_checked : ((-1 : ℤ) ^ (rightScaleBit 4 7 3).val * positiveScale (rightScaleExponent 4 7 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 3 7 : ℤ)) • HexagonAtoms473.outerLeftABC = negativeScale (rightScaleExponent 4 7 3) • (rowColumnMul HexagonRowColumn473.rows_assocCAB HexagonRowColumn473.cols_right2) := by
  funext r
  fin_cases r
  · exact rightFinal4_case_7_3_row_0_0_0
  · exact rightFinal4_case_7_3_row_0_0_1
  · exact rightFinal4_case_7_3_row_0_0_2
  · exact rightFinal4_case_7_3_row_0_0_3
  · exact rightFinal4_case_7_3_row_0_1_0
  · exact rightFinal4_case_7_3_row_0_1_1
  · exact rightFinal4_case_7_3_row_0_1_2
  · exact rightFinal4_case_7_3_row_0_1_3
  · exact rightFinal4_case_7_3_row_0_2_0
  · exact rightFinal4_case_7_3_row_0_2_1
  · exact rightFinal4_case_7_3_row_0_2_2
  · exact rightFinal4_case_7_3_row_0_2_3
  · exact rightFinal4_case_7_3_row_0_3_0
  · exact rightFinal4_case_7_3_row_0_3_1
  · exact rightFinal4_case_7_3_row_0_3_2
  · exact rightFinal4_case_7_3_row_0_3_3

set_option backward.isDefEq.respectTransparency false in
theorem rightFinal4_case_7_3 : ((-1 : ℤ) ^ (rightScaleBit 4 7 3).val * positiveScale (rightScaleExponent 4 7 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 3 7 : ℤ)) • outerLeftZ 4 7 3 = negativeScale (rightScaleExponent 4 7 3) • (associatorZ 3 4 7 * right2Middle4 7 3) := by
  simpa only [HexagonAtoms473.assocABC_eq,
    HexagonAtoms473.outerABC_eq,
    HexagonAtoms473.assocBAC_eq,
    HexagonAtoms473.innerABC_eq,
    HexagonAtoms473.innerRightABC_eq,
    HexagonAtoms473.inverseACB_eq,
    HexagonAtoms473.innerACB_eq,
    HexagonAtoms473.assocBCA_eq,
    HexagonAtoms473.innerRightBAC_eq,
    HexagonAtoms473.assocCAB_eq,
    HexagonAtoms473.outerLeftABC_eq,
    HexagonRowColumn473.product0_eq,
    HexagonRowColumn473.product1_eq,
    HexagonRowColumn473.product2_eq,
    HexagonRowColumn473.product3_eq,
    HexagonRowColumn473.product4_eq,
    HexagonRowColumn473.product5_eq,
    HexagonRowColumn473.product6_eq,
    HexagonRowColumn473.product7_eq] using rightFinal4_case_7_3_checked

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonCases4
