import RMod.BrundanEllis.StackingReferenceHexagonMiddle5
import RMod.BrundanEllis.StackingReferenceSparseMatrixCheck
import RMod.BrundanEllis.StackingReferenceHexagonAtoms531
import RMod.BrundanEllis.StackingReferenceHexagonRowColumn531

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

private theorem left0Middle5_eq_case_3_1_row_0_0_0 : (left0Middle5 3 1) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (HexagonAtoms531.assocABC) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_3_1_row_0_0_1 : (left0Middle5 3 1) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (HexagonAtoms531.assocABC) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_3_1_row_0_1_0 : (left0Middle5 3 1) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (HexagonAtoms531.assocABC) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_3_1_row_0_1_1 : (left0Middle5 3 1) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (HexagonAtoms531.assocABC) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_3_1_row_0_2_0 : (left0Middle5 3 1) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (HexagonAtoms531.assocABC) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_3_1_row_0_2_1 : (left0Middle5 3 1) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (HexagonAtoms531.assocABC) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_3_1_row_0_3_0 : (left0Middle5 3 1) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (HexagonAtoms531.assocABC) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_3_1_row_0_3_1 : (left0Middle5 3 1) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (HexagonAtoms531.assocABC) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_3_1_row_1_0_0 : (left0Middle5 3 1) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (HexagonAtoms531.assocABC) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_3_1_row_1_0_1 : (left0Middle5 3 1) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (HexagonAtoms531.assocABC) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_3_1_row_1_1_0 : (left0Middle5 3 1) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (HexagonAtoms531.assocABC) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_3_1_row_1_1_1 : (left0Middle5 3 1) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (HexagonAtoms531.assocABC) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_3_1_row_1_2_0 : (left0Middle5 3 1) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (HexagonAtoms531.assocABC) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_3_1_row_1_2_1 : (left0Middle5 3 1) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (HexagonAtoms531.assocABC) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_3_1_row_1_3_0 : (left0Middle5 3 1) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (HexagonAtoms531.assocABC) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_3_1_row_1_3_1 : (left0Middle5 3 1) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (HexagonAtoms531.assocABC) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem left0Middle5_eq_case_3_1_checked : left0Middle5 3 1 = HexagonAtoms531.assocABC := by
  funext r
  fin_cases r
  · exact left0Middle5_eq_case_3_1_row_0_0_0
  · exact left0Middle5_eq_case_3_1_row_0_0_1
  · exact left0Middle5_eq_case_3_1_row_0_1_0
  · exact left0Middle5_eq_case_3_1_row_0_1_1
  · exact left0Middle5_eq_case_3_1_row_0_2_0
  · exact left0Middle5_eq_case_3_1_row_0_2_1
  · exact left0Middle5_eq_case_3_1_row_0_3_0
  · exact left0Middle5_eq_case_3_1_row_0_3_1
  · exact left0Middle5_eq_case_3_1_row_1_0_0
  · exact left0Middle5_eq_case_3_1_row_1_0_1
  · exact left0Middle5_eq_case_3_1_row_1_1_0
  · exact left0Middle5_eq_case_3_1_row_1_1_1
  · exact left0Middle5_eq_case_3_1_row_1_2_0
  · exact left0Middle5_eq_case_3_1_row_1_2_1
  · exact left0Middle5_eq_case_3_1_row_1_3_0
  · exact left0Middle5_eq_case_3_1_row_1_3_1

set_option backward.isDefEq.respectTransparency false in
theorem left0Middle5_eq_case_3_1 : left0Middle5 3 1 = outerRightZ 5 3 1 * associatorZ 5 3 1 := by
  simpa only [HexagonAtoms531.assocABC_eq,
    HexagonAtoms531.outerABC_eq,
    HexagonAtoms531.assocBAC_eq,
    HexagonAtoms531.innerABC_eq,
    HexagonAtoms531.innerRightABC_eq,
    HexagonAtoms531.inverseACB_eq,
    HexagonAtoms531.innerACB_eq,
    HexagonAtoms531.assocBCA_eq,
    HexagonAtoms531.innerRightBAC_eq,
    HexagonAtoms531.assocCAB_eq,
    HexagonAtoms531.outerLeftABC_eq,
    HexagonRowColumn531.product0_eq,
    HexagonRowColumn531.product1_eq,
    HexagonRowColumn531.product2_eq,
    HexagonRowColumn531.product3_eq,
    HexagonRowColumn531.product4_eq,
    HexagonRowColumn531.product5_eq,
    HexagonRowColumn531.product6_eq,
    HexagonRowColumn531.product7_eq] using left0Middle5_eq_case_3_1_checked

private theorem left1Middle5_eq_case_3_1_row_0_0_0 : (left1Middle5 3 1) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (HexagonAtoms531.assocBAC) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_3_1_row_0_0_1 : (left1Middle5 3 1) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (HexagonAtoms531.assocBAC) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_3_1_row_0_1_0 : (left1Middle5 3 1) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (HexagonAtoms531.assocBAC) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_3_1_row_0_1_1 : (left1Middle5 3 1) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (HexagonAtoms531.assocBAC) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_3_1_row_0_2_0 : (left1Middle5 3 1) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (HexagonAtoms531.assocBAC) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_3_1_row_0_2_1 : (left1Middle5 3 1) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (HexagonAtoms531.assocBAC) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_3_1_row_0_3_0 : (left1Middle5 3 1) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (HexagonAtoms531.assocBAC) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_3_1_row_0_3_1 : (left1Middle5 3 1) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (HexagonAtoms531.assocBAC) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_3_1_row_1_0_0 : (left1Middle5 3 1) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (HexagonAtoms531.assocBAC) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_3_1_row_1_0_1 : (left1Middle5 3 1) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (HexagonAtoms531.assocBAC) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_3_1_row_1_1_0 : (left1Middle5 3 1) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (HexagonAtoms531.assocBAC) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_3_1_row_1_1_1 : (left1Middle5 3 1) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (HexagonAtoms531.assocBAC) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_3_1_row_1_2_0 : (left1Middle5 3 1) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (HexagonAtoms531.assocBAC) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_3_1_row_1_2_1 : (left1Middle5 3 1) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (HexagonAtoms531.assocBAC) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_3_1_row_1_3_0 : (left1Middle5 3 1) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (HexagonAtoms531.assocBAC) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_3_1_row_1_3_1 : (left1Middle5 3 1) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (HexagonAtoms531.assocBAC) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem left1Middle5_eq_case_3_1_checked : left1Middle5 3 1 = HexagonAtoms531.assocBAC := by
  funext r
  fin_cases r
  · exact left1Middle5_eq_case_3_1_row_0_0_0
  · exact left1Middle5_eq_case_3_1_row_0_0_1
  · exact left1Middle5_eq_case_3_1_row_0_1_0
  · exact left1Middle5_eq_case_3_1_row_0_1_1
  · exact left1Middle5_eq_case_3_1_row_0_2_0
  · exact left1Middle5_eq_case_3_1_row_0_2_1
  · exact left1Middle5_eq_case_3_1_row_0_3_0
  · exact left1Middle5_eq_case_3_1_row_0_3_1
  · exact left1Middle5_eq_case_3_1_row_1_0_0
  · exact left1Middle5_eq_case_3_1_row_1_0_1
  · exact left1Middle5_eq_case_3_1_row_1_1_0
  · exact left1Middle5_eq_case_3_1_row_1_1_1
  · exact left1Middle5_eq_case_3_1_row_1_2_0
  · exact left1Middle5_eq_case_3_1_row_1_2_1
  · exact left1Middle5_eq_case_3_1_row_1_3_0
  · exact left1Middle5_eq_case_3_1_row_1_3_1

set_option backward.isDefEq.respectTransparency false in
theorem left1Middle5_eq_case_3_1 : left1Middle5 3 1 = associatorZ 3 5 1 * innerLeftZ 5 3 1 := by
  simpa only [HexagonAtoms531.assocABC_eq,
    HexagonAtoms531.outerABC_eq,
    HexagonAtoms531.assocBAC_eq,
    HexagonAtoms531.innerABC_eq,
    HexagonAtoms531.innerRightABC_eq,
    HexagonAtoms531.inverseACB_eq,
    HexagonAtoms531.innerACB_eq,
    HexagonAtoms531.assocBCA_eq,
    HexagonAtoms531.innerRightBAC_eq,
    HexagonAtoms531.assocCAB_eq,
    HexagonAtoms531.outerLeftABC_eq,
    HexagonRowColumn531.product0_eq,
    HexagonRowColumn531.product1_eq,
    HexagonRowColumn531.product2_eq,
    HexagonRowColumn531.product3_eq,
    HexagonRowColumn531.product4_eq,
    HexagonRowColumn531.product5_eq,
    HexagonRowColumn531.product6_eq,
    HexagonRowColumn531.product7_eq] using left1Middle5_eq_case_3_1_checked

private theorem right0Middle5_eq_case_3_1_row_0_0_0 : (right0Middle5 3 1) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (HexagonAtoms531.assocABC) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_3_1_row_0_0_1 : (right0Middle5 3 1) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (HexagonAtoms531.assocABC) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_3_1_row_0_1_0 : (right0Middle5 3 1) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (HexagonAtoms531.assocABC) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_3_1_row_0_1_1 : (right0Middle5 3 1) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (HexagonAtoms531.assocABC) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_3_1_row_0_2_0 : (right0Middle5 3 1) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (HexagonAtoms531.assocABC) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_3_1_row_0_2_1 : (right0Middle5 3 1) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (HexagonAtoms531.assocABC) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_3_1_row_0_3_0 : (right0Middle5 3 1) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (HexagonAtoms531.assocABC) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_3_1_row_0_3_1 : (right0Middle5 3 1) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (HexagonAtoms531.assocABC) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_3_1_row_1_0_0 : (right0Middle5 3 1) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (HexagonAtoms531.assocABC) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_3_1_row_1_0_1 : (right0Middle5 3 1) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (HexagonAtoms531.assocABC) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_3_1_row_1_1_0 : (right0Middle5 3 1) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (HexagonAtoms531.assocABC) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_3_1_row_1_1_1 : (right0Middle5 3 1) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (HexagonAtoms531.assocABC) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_3_1_row_1_2_0 : (right0Middle5 3 1) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (HexagonAtoms531.assocABC) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_3_1_row_1_2_1 : (right0Middle5 3 1) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (HexagonAtoms531.assocABC) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_3_1_row_1_3_0 : (right0Middle5 3 1) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (HexagonAtoms531.assocABC) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_3_1_row_1_3_1 : (right0Middle5 3 1) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (HexagonAtoms531.assocABC) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right0Middle5_eq_case_3_1_checked : right0Middle5 3 1 = HexagonAtoms531.assocABC := by
  funext r
  fin_cases r
  · exact right0Middle5_eq_case_3_1_row_0_0_0
  · exact right0Middle5_eq_case_3_1_row_0_0_1
  · exact right0Middle5_eq_case_3_1_row_0_1_0
  · exact right0Middle5_eq_case_3_1_row_0_1_1
  · exact right0Middle5_eq_case_3_1_row_0_2_0
  · exact right0Middle5_eq_case_3_1_row_0_2_1
  · exact right0Middle5_eq_case_3_1_row_0_3_0
  · exact right0Middle5_eq_case_3_1_row_0_3_1
  · exact right0Middle5_eq_case_3_1_row_1_0_0
  · exact right0Middle5_eq_case_3_1_row_1_0_1
  · exact right0Middle5_eq_case_3_1_row_1_1_0
  · exact right0Middle5_eq_case_3_1_row_1_1_1
  · exact right0Middle5_eq_case_3_1_row_1_2_0
  · exact right0Middle5_eq_case_3_1_row_1_2_1
  · exact right0Middle5_eq_case_3_1_row_1_3_0
  · exact right0Middle5_eq_case_3_1_row_1_3_1

set_option backward.isDefEq.respectTransparency false in
theorem right0Middle5_eq_case_3_1 : right0Middle5 3 1 = innerRightZ 5 3 1 * associatorZ 5 3 1 := by
  simpa only [HexagonAtoms531.assocABC_eq,
    HexagonAtoms531.outerABC_eq,
    HexagonAtoms531.assocBAC_eq,
    HexagonAtoms531.innerABC_eq,
    HexagonAtoms531.innerRightABC_eq,
    HexagonAtoms531.inverseACB_eq,
    HexagonAtoms531.innerACB_eq,
    HexagonAtoms531.assocBCA_eq,
    HexagonAtoms531.innerRightBAC_eq,
    HexagonAtoms531.assocCAB_eq,
    HexagonAtoms531.outerLeftABC_eq,
    HexagonRowColumn531.product0_eq,
    HexagonRowColumn531.product1_eq,
    HexagonRowColumn531.product2_eq,
    HexagonRowColumn531.product3_eq,
    HexagonRowColumn531.product4_eq,
    HexagonRowColumn531.product5_eq,
    HexagonRowColumn531.product6_eq,
    HexagonRowColumn531.product7_eq] using right0Middle5_eq_case_3_1_checked

private theorem right1Middle5_eq_case_3_1_row_0_0_0 : (right1Middle5 3 1) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn531.rows_inverseACB HexagonRowColumn531.cols_right0) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_3_1_row_0_0_1 : (right1Middle5 3 1) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn531.rows_inverseACB HexagonRowColumn531.cols_right0) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_3_1_row_0_1_0 : (right1Middle5 3 1) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn531.rows_inverseACB HexagonRowColumn531.cols_right0) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_3_1_row_0_1_1 : (right1Middle5 3 1) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn531.rows_inverseACB HexagonRowColumn531.cols_right0) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_3_1_row_0_2_0 : (right1Middle5 3 1) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn531.rows_inverseACB HexagonRowColumn531.cols_right0) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_3_1_row_0_2_1 : (right1Middle5 3 1) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn531.rows_inverseACB HexagonRowColumn531.cols_right0) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_3_1_row_0_3_0 : (right1Middle5 3 1) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn531.rows_inverseACB HexagonRowColumn531.cols_right0) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_3_1_row_0_3_1 : (right1Middle5 3 1) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn531.rows_inverseACB HexagonRowColumn531.cols_right0) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_3_1_row_1_0_0 : (right1Middle5 3 1) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn531.rows_inverseACB HexagonRowColumn531.cols_right0) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_3_1_row_1_0_1 : (right1Middle5 3 1) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn531.rows_inverseACB HexagonRowColumn531.cols_right0) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_3_1_row_1_1_0 : (right1Middle5 3 1) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn531.rows_inverseACB HexagonRowColumn531.cols_right0) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_3_1_row_1_1_1 : (right1Middle5 3 1) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn531.rows_inverseACB HexagonRowColumn531.cols_right0) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_3_1_row_1_2_0 : (right1Middle5 3 1) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn531.rows_inverseACB HexagonRowColumn531.cols_right0) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_3_1_row_1_2_1 : (right1Middle5 3 1) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn531.rows_inverseACB HexagonRowColumn531.cols_right0) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_3_1_row_1_3_0 : (right1Middle5 3 1) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (rowColumnMul HexagonRowColumn531.rows_inverseACB HexagonRowColumn531.cols_right0) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_3_1_row_1_3_1 : (right1Middle5 3 1) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (rowColumnMul HexagonRowColumn531.rows_inverseACB HexagonRowColumn531.cols_right0) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right1Middle5_eq_case_3_1_checked : right1Middle5 3 1 = rowColumnMul HexagonRowColumn531.rows_inverseACB HexagonRowColumn531.cols_right0 := by
  funext r
  fin_cases r
  · exact right1Middle5_eq_case_3_1_row_0_0_0
  · exact right1Middle5_eq_case_3_1_row_0_0_1
  · exact right1Middle5_eq_case_3_1_row_0_1_0
  · exact right1Middle5_eq_case_3_1_row_0_1_1
  · exact right1Middle5_eq_case_3_1_row_0_2_0
  · exact right1Middle5_eq_case_3_1_row_0_2_1
  · exact right1Middle5_eq_case_3_1_row_0_3_0
  · exact right1Middle5_eq_case_3_1_row_0_3_1
  · exact right1Middle5_eq_case_3_1_row_1_0_0
  · exact right1Middle5_eq_case_3_1_row_1_0_1
  · exact right1Middle5_eq_case_3_1_row_1_1_0
  · exact right1Middle5_eq_case_3_1_row_1_1_1
  · exact right1Middle5_eq_case_3_1_row_1_2_0
  · exact right1Middle5_eq_case_3_1_row_1_2_1
  · exact right1Middle5_eq_case_3_1_row_1_3_0
  · exact right1Middle5_eq_case_3_1_row_1_3_1

set_option backward.isDefEq.respectTransparency false in
theorem right1Middle5_eq_case_3_1 : right1Middle5 3 1 = associatorInverseZ 5 1 3 * right0Middle5 3 1 := by
  simpa only [HexagonAtoms531.assocABC_eq,
    HexagonAtoms531.outerABC_eq,
    HexagonAtoms531.assocBAC_eq,
    HexagonAtoms531.innerABC_eq,
    HexagonAtoms531.innerRightABC_eq,
    HexagonAtoms531.inverseACB_eq,
    HexagonAtoms531.innerACB_eq,
    HexagonAtoms531.assocBCA_eq,
    HexagonAtoms531.innerRightBAC_eq,
    HexagonAtoms531.assocCAB_eq,
    HexagonAtoms531.outerLeftABC_eq,
    HexagonRowColumn531.product0_eq,
    HexagonRowColumn531.product1_eq,
    HexagonRowColumn531.product2_eq,
    HexagonRowColumn531.product3_eq,
    HexagonRowColumn531.product4_eq,
    HexagonRowColumn531.product5_eq,
    HexagonRowColumn531.product6_eq,
    HexagonRowColumn531.product7_eq] using right1Middle5_eq_case_3_1_checked

private theorem right2Middle5_eq_case_3_1_row_0_0_0 : (right2Middle5 3 1) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (right1Middle5 3 1) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_3_1_row_0_0_1 : (right2Middle5 3 1) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (right1Middle5 3 1) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_3_1_row_0_1_0 : (right2Middle5 3 1) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (right1Middle5 3 1) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_3_1_row_0_1_1 : (right2Middle5 3 1) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (right1Middle5 3 1) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_3_1_row_0_2_0 : (right2Middle5 3 1) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (right1Middle5 3 1) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_3_1_row_0_2_1 : (right2Middle5 3 1) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (right1Middle5 3 1) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_3_1_row_0_3_0 : (right2Middle5 3 1) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (right1Middle5 3 1) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_3_1_row_0_3_1 : (right2Middle5 3 1) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (right1Middle5 3 1) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_3_1_row_1_0_0 : (right2Middle5 3 1) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (right1Middle5 3 1) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_3_1_row_1_0_1 : (right2Middle5 3 1) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (right1Middle5 3 1) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_3_1_row_1_1_0 : (right2Middle5 3 1) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (right1Middle5 3 1) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_3_1_row_1_1_1 : (right2Middle5 3 1) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (right1Middle5 3 1) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_3_1_row_1_2_0 : (right2Middle5 3 1) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (right1Middle5 3 1) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_3_1_row_1_2_1 : (right2Middle5 3 1) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (right1Middle5 3 1) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_3_1_row_1_3_0 : (right2Middle5 3 1) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (right1Middle5 3 1) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_3_1_row_1_3_1 : (right2Middle5 3 1) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (right1Middle5 3 1) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem right2Middle5_eq_case_3_1_checked : right2Middle5 3 1 = right1Middle5 3 1 := by
  funext r
  fin_cases r
  · exact right2Middle5_eq_case_3_1_row_0_0_0
  · exact right2Middle5_eq_case_3_1_row_0_0_1
  · exact right2Middle5_eq_case_3_1_row_0_1_0
  · exact right2Middle5_eq_case_3_1_row_0_1_1
  · exact right2Middle5_eq_case_3_1_row_0_2_0
  · exact right2Middle5_eq_case_3_1_row_0_2_1
  · exact right2Middle5_eq_case_3_1_row_0_3_0
  · exact right2Middle5_eq_case_3_1_row_0_3_1
  · exact right2Middle5_eq_case_3_1_row_1_0_0
  · exact right2Middle5_eq_case_3_1_row_1_0_1
  · exact right2Middle5_eq_case_3_1_row_1_1_0
  · exact right2Middle5_eq_case_3_1_row_1_1_1
  · exact right2Middle5_eq_case_3_1_row_1_2_0
  · exact right2Middle5_eq_case_3_1_row_1_2_1
  · exact right2Middle5_eq_case_3_1_row_1_3_0
  · exact right2Middle5_eq_case_3_1_row_1_3_1

set_option backward.isDefEq.respectTransparency false in
theorem right2Middle5_eq_case_3_1 : right2Middle5 3 1 = innerLeftZ 5 1 3 * right1Middle5 3 1 := by
  simpa only [HexagonAtoms531.assocABC_eq,
    HexagonAtoms531.outerABC_eq,
    HexagonAtoms531.assocBAC_eq,
    HexagonAtoms531.innerABC_eq,
    HexagonAtoms531.innerRightABC_eq,
    HexagonAtoms531.inverseACB_eq,
    HexagonAtoms531.innerACB_eq,
    HexagonAtoms531.assocBCA_eq,
    HexagonAtoms531.innerRightBAC_eq,
    HexagonAtoms531.assocCAB_eq,
    HexagonAtoms531.outerLeftABC_eq,
    HexagonRowColumn531.product0_eq,
    HexagonRowColumn531.product1_eq,
    HexagonRowColumn531.product2_eq,
    HexagonRowColumn531.product3_eq,
    HexagonRowColumn531.product4_eq,
    HexagonRowColumn531.product5_eq,
    HexagonRowColumn531.product6_eq,
    HexagonRowColumn531.product7_eq] using right2Middle5_eq_case_3_1_checked

private theorem leftFinal5_case_3_1_row_0_0_0 : (((-1 : ℤ) ^ (leftScaleBit 5 3 1).val * positiveScale (leftScaleExponent 5 3 1)) •
      (rowColumnMul HexagonRowColumn531.rows_assocBCA HexagonRowColumn531.cols_left0)) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 5 3 1) • (left1Middle5 3 1)) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem leftFinal5_case_3_1_row_0_0_1 : (((-1 : ℤ) ^ (leftScaleBit 5 3 1).val * positiveScale (leftScaleExponent 5 3 1)) •
      (rowColumnMul HexagonRowColumn531.rows_assocBCA HexagonRowColumn531.cols_left0)) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 5 3 1) • (left1Middle5 3 1)) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem leftFinal5_case_3_1_row_0_1_0 : (((-1 : ℤ) ^ (leftScaleBit 5 3 1).val * positiveScale (leftScaleExponent 5 3 1)) •
      (rowColumnMul HexagonRowColumn531.rows_assocBCA HexagonRowColumn531.cols_left0)) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 5 3 1) • (left1Middle5 3 1)) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem leftFinal5_case_3_1_row_0_1_1 : (((-1 : ℤ) ^ (leftScaleBit 5 3 1).val * positiveScale (leftScaleExponent 5 3 1)) •
      (rowColumnMul HexagonRowColumn531.rows_assocBCA HexagonRowColumn531.cols_left0)) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 5 3 1) • (left1Middle5 3 1)) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem leftFinal5_case_3_1_row_0_2_0 : (((-1 : ℤ) ^ (leftScaleBit 5 3 1).val * positiveScale (leftScaleExponent 5 3 1)) •
      (rowColumnMul HexagonRowColumn531.rows_assocBCA HexagonRowColumn531.cols_left0)) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 5 3 1) • (left1Middle5 3 1)) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem leftFinal5_case_3_1_row_0_2_1 : (((-1 : ℤ) ^ (leftScaleBit 5 3 1).val * positiveScale (leftScaleExponent 5 3 1)) •
      (rowColumnMul HexagonRowColumn531.rows_assocBCA HexagonRowColumn531.cols_left0)) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 5 3 1) • (left1Middle5 3 1)) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem leftFinal5_case_3_1_row_0_3_0 : (((-1 : ℤ) ^ (leftScaleBit 5 3 1).val * positiveScale (leftScaleExponent 5 3 1)) •
      (rowColumnMul HexagonRowColumn531.rows_assocBCA HexagonRowColumn531.cols_left0)) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 5 3 1) • (left1Middle5 3 1)) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem leftFinal5_case_3_1_row_0_3_1 : (((-1 : ℤ) ^ (leftScaleBit 5 3 1).val * positiveScale (leftScaleExponent 5 3 1)) •
      (rowColumnMul HexagonRowColumn531.rows_assocBCA HexagonRowColumn531.cols_left0)) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 5 3 1) • (left1Middle5 3 1)) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem leftFinal5_case_3_1_row_1_0_0 : (((-1 : ℤ) ^ (leftScaleBit 5 3 1).val * positiveScale (leftScaleExponent 5 3 1)) •
      (rowColumnMul HexagonRowColumn531.rows_assocBCA HexagonRowColumn531.cols_left0)) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 5 3 1) • (left1Middle5 3 1)) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem leftFinal5_case_3_1_row_1_0_1 : (((-1 : ℤ) ^ (leftScaleBit 5 3 1).val * positiveScale (leftScaleExponent 5 3 1)) •
      (rowColumnMul HexagonRowColumn531.rows_assocBCA HexagonRowColumn531.cols_left0)) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 5 3 1) • (left1Middle5 3 1)) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem leftFinal5_case_3_1_row_1_1_0 : (((-1 : ℤ) ^ (leftScaleBit 5 3 1).val * positiveScale (leftScaleExponent 5 3 1)) •
      (rowColumnMul HexagonRowColumn531.rows_assocBCA HexagonRowColumn531.cols_left0)) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 5 3 1) • (left1Middle5 3 1)) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem leftFinal5_case_3_1_row_1_1_1 : (((-1 : ℤ) ^ (leftScaleBit 5 3 1).val * positiveScale (leftScaleExponent 5 3 1)) •
      (rowColumnMul HexagonRowColumn531.rows_assocBCA HexagonRowColumn531.cols_left0)) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 5 3 1) • (left1Middle5 3 1)) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem leftFinal5_case_3_1_row_1_2_0 : (((-1 : ℤ) ^ (leftScaleBit 5 3 1).val * positiveScale (leftScaleExponent 5 3 1)) •
      (rowColumnMul HexagonRowColumn531.rows_assocBCA HexagonRowColumn531.cols_left0)) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 5 3 1) • (left1Middle5 3 1)) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem leftFinal5_case_3_1_row_1_2_1 : (((-1 : ℤ) ^ (leftScaleBit 5 3 1).val * positiveScale (leftScaleExponent 5 3 1)) •
      (rowColumnMul HexagonRowColumn531.rows_assocBCA HexagonRowColumn531.cols_left0)) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 5 3 1) • (left1Middle5 3 1)) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem leftFinal5_case_3_1_row_1_3_0 : (((-1 : ℤ) ^ (leftScaleBit 5 3 1).val * positiveScale (leftScaleExponent 5 3 1)) •
      (rowColumnMul HexagonRowColumn531.rows_assocBCA HexagonRowColumn531.cols_left0)) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) = (negativeScale (leftScaleExponent 5 3 1) • (left1Middle5 3 1)) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem leftFinal5_case_3_1_row_1_3_1 : (((-1 : ℤ) ^ (leftScaleBit 5 3 1).val * positiveScale (leftScaleExponent 5 3 1)) •
      (rowColumnMul HexagonRowColumn531.rows_assocBCA HexagonRowColumn531.cols_left0)) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) = (negativeScale (leftScaleExponent 5 3 1) • (left1Middle5 3 1)) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem leftFinal5_case_3_1_checked : ((-1 : ℤ) ^ (leftScaleBit 5 3 1).val * positiveScale (leftScaleExponent 5 3 1)) •
      (rowColumnMul HexagonRowColumn531.rows_assocBCA HexagonRowColumn531.cols_left0) = negativeScale (leftScaleExponent 5 3 1) • (left1Middle5 3 1) := by
  funext r
  fin_cases r
  · exact leftFinal5_case_3_1_row_0_0_0
  · exact leftFinal5_case_3_1_row_0_0_1
  · exact leftFinal5_case_3_1_row_0_1_0
  · exact leftFinal5_case_3_1_row_0_1_1
  · exact leftFinal5_case_3_1_row_0_2_0
  · exact leftFinal5_case_3_1_row_0_2_1
  · exact leftFinal5_case_3_1_row_0_3_0
  · exact leftFinal5_case_3_1_row_0_3_1
  · exact leftFinal5_case_3_1_row_1_0_0
  · exact leftFinal5_case_3_1_row_1_0_1
  · exact leftFinal5_case_3_1_row_1_1_0
  · exact leftFinal5_case_3_1_row_1_1_1
  · exact leftFinal5_case_3_1_row_1_2_0
  · exact leftFinal5_case_3_1_row_1_2_1
  · exact leftFinal5_case_3_1_row_1_3_0
  · exact leftFinal5_case_3_1_row_1_3_1

set_option backward.isDefEq.respectTransparency false in
theorem leftFinal5_case_3_1 : ((-1 : ℤ) ^ (leftScaleBit 5 3 1).val * positiveScale (leftScaleExponent 5 3 1)) •
      (associatorZ 3 1 5 * left0Middle5 3 1) = negativeScale (leftScaleExponent 5 3 1) • (innerRightZ 3 5 1 * left1Middle5 3 1) := by
  simpa only [HexagonAtoms531.assocABC_eq,
    HexagonAtoms531.outerABC_eq,
    HexagonAtoms531.assocBAC_eq,
    HexagonAtoms531.innerABC_eq,
    HexagonAtoms531.innerRightABC_eq,
    HexagonAtoms531.inverseACB_eq,
    HexagonAtoms531.innerACB_eq,
    HexagonAtoms531.assocBCA_eq,
    HexagonAtoms531.innerRightBAC_eq,
    HexagonAtoms531.assocCAB_eq,
    HexagonAtoms531.outerLeftABC_eq,
    HexagonRowColumn531.product0_eq,
    HexagonRowColumn531.product1_eq,
    HexagonRowColumn531.product2_eq,
    HexagonRowColumn531.product3_eq,
    HexagonRowColumn531.product4_eq,
    HexagonRowColumn531.product5_eq,
    HexagonRowColumn531.product6_eq,
    HexagonRowColumn531.product7_eq] using leftFinal5_case_3_1_checked

private theorem rightFinal5_case_3_1_row_0_0_0 : (((-1 : ℤ) ^ (rightScaleBit 5 3 1).val * positiveScale (rightScaleExponent 5 3 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 1 3 : ℤ)) • HexagonAtoms531.outerLeftABC) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 2)) = (negativeScale (rightScaleExponent 5 3 1) • (rowColumnMul HexagonRowColumn531.rows_assocCAB HexagonRowColumn531.cols_right2)) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem rightFinal5_case_3_1_row_0_0_1 : (((-1 : ℤ) ^ (rightScaleBit 5 3 1).val * positiveScale (rightScaleExponent 5 3 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 1 3 : ℤ)) • HexagonAtoms531.outerLeftABC) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 2)) = (negativeScale (rightScaleExponent 5 3 1) • (rowColumnMul HexagonRowColumn531.rows_assocCAB HexagonRowColumn531.cols_right2)) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem rightFinal5_case_3_1_row_1_0_0 : (((-1 : ℤ) ^ (rightScaleBit 5 3 1).val * positiveScale (rightScaleExponent 5 3 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 1 3 : ℤ)) • HexagonAtoms531.outerLeftABC) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 2)) = (negativeScale (rightScaleExponent 5 3 1) • (rowColumnMul HexagonRowColumn531.rows_assocCAB HexagonRowColumn531.cols_right2)) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem rightFinal5_case_3_1_row_1_0_1 : (((-1 : ℤ) ^ (rightScaleBit 5 3 1).val * positiveScale (rightScaleExponent 5 3 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 1 3 : ℤ)) • HexagonAtoms531.outerLeftABC) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 2)) = (negativeScale (rightScaleExponent 5 3 1) • (rowColumnMul HexagonRowColumn531.rows_assocCAB HexagonRowColumn531.cols_right2)) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem rightFinal5_case_3_1_row_2_0_0 : (((-1 : ℤ) ^ (rightScaleBit 5 3 1).val * positiveScale (rightScaleExponent 5 3 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 1 3 : ℤ)) • HexagonAtoms531.outerLeftABC) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 2)) = (negativeScale (rightScaleExponent 5 3 1) • (rowColumnMul HexagonRowColumn531.rows_assocCAB HexagonRowColumn531.cols_right2)) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem rightFinal5_case_3_1_row_2_0_1 : (((-1 : ℤ) ^ (rightScaleBit 5 3 1).val * positiveScale (rightScaleExponent 5 3 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 1 3 : ℤ)) • HexagonAtoms531.outerLeftABC) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 2)) = (negativeScale (rightScaleExponent 5 3 1) • (rowColumnMul HexagonRowColumn531.rows_assocCAB HexagonRowColumn531.cols_right2)) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem rightFinal5_case_3_1_row_3_0_0 : (((-1 : ℤ) ^ (rightScaleBit 5 3 1).val * positiveScale (rightScaleExponent 5 3 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 1 3 : ℤ)) • HexagonAtoms531.outerLeftABC) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 2)) = (negativeScale (rightScaleExponent 5 3 1) • (rowColumnMul HexagonRowColumn531.rows_assocCAB HexagonRowColumn531.cols_right2)) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem rightFinal5_case_3_1_row_3_0_1 : (((-1 : ℤ) ^ (rightScaleBit 5 3 1).val * positiveScale (rightScaleExponent 5 3 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 1 3 : ℤ)) • HexagonAtoms531.outerLeftABC) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 2)) = (negativeScale (rightScaleExponent 5 3 1) • (rowColumnMul HexagonRowColumn531.rows_assocCAB HexagonRowColumn531.cols_right2)) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem rightFinal5_case_3_1_row_4_0_0 : (((-1 : ℤ) ^ (rightScaleBit 5 3 1).val * positiveScale (rightScaleExponent 5 3 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 1 3 : ℤ)) • HexagonAtoms531.outerLeftABC) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 2)) = (negativeScale (rightScaleExponent 5 3 1) • (rowColumnMul HexagonRowColumn531.rows_assocCAB HexagonRowColumn531.cols_right2)) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem rightFinal5_case_3_1_row_4_0_1 : (((-1 : ℤ) ^ (rightScaleBit 5 3 1).val * positiveScale (rightScaleExponent 5 3 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 1 3 : ℤ)) • HexagonAtoms531.outerLeftABC) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 2)) = (negativeScale (rightScaleExponent 5 3 1) • (rowColumnMul HexagonRowColumn531.rows_assocCAB HexagonRowColumn531.cols_right2)) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem rightFinal5_case_3_1_row_5_0_0 : (((-1 : ℤ) ^ (rightScaleBit 5 3 1).val * positiveScale (rightScaleExponent 5 3 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 1 3 : ℤ)) • HexagonAtoms531.outerLeftABC) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 2)) = (negativeScale (rightScaleExponent 5 3 1) • (rowColumnMul HexagonRowColumn531.rows_assocCAB HexagonRowColumn531.cols_right2)) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem rightFinal5_case_3_1_row_5_0_1 : (((-1 : ℤ) ^ (rightScaleBit 5 3 1).val * positiveScale (rightScaleExponent 5 3 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 1 3 : ℤ)) • HexagonAtoms531.outerLeftABC) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 2)) = (negativeScale (rightScaleExponent 5 3 1) • (rowColumnMul HexagonRowColumn531.rows_assocCAB HexagonRowColumn531.cols_right2)) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem rightFinal5_case_3_1_row_6_0_0 : (((-1 : ℤ) ^ (rightScaleBit 5 3 1).val * positiveScale (rightScaleExponent 5 3 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 1 3 : ℤ)) • HexagonAtoms531.outerLeftABC) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 2)) = (negativeScale (rightScaleExponent 5 3 1) • (rowColumnMul HexagonRowColumn531.rows_assocCAB HexagonRowColumn531.cols_right2)) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem rightFinal5_case_3_1_row_6_0_1 : (((-1 : ℤ) ^ (rightScaleBit 5 3 1).val * positiveScale (rightScaleExponent 5 3 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 1 3 : ℤ)) • HexagonAtoms531.outerLeftABC) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 2)) = (negativeScale (rightScaleExponent 5 3 1) • (rowColumnMul HexagonRowColumn531.rows_assocCAB HexagonRowColumn531.cols_right2)) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem rightFinal5_case_3_1_row_7_0_0 : (((-1 : ℤ) ^ (rightScaleBit 5 3 1).val * positiveScale (rightScaleExponent 5 3 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 1 3 : ℤ)) • HexagonAtoms531.outerLeftABC) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 2)) = (negativeScale (rightScaleExponent 5 3 1) • (rowColumnMul HexagonRowColumn531.rows_assocCAB HexagonRowColumn531.cols_right2)) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem rightFinal5_case_3_1_row_7_0_1 : (((-1 : ℤ) ^ (rightScaleBit 5 3 1).val * positiveScale (rightScaleExponent 5 3 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 1 3 : ℤ)) • HexagonAtoms531.outerLeftABC) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 2)) = (negativeScale (rightScaleExponent 5 3 1) • (rowColumnMul HexagonRowColumn531.rows_assocCAB HexagonRowColumn531.cols_right2)) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleRowCheck_sound (a := 8) (b := 1) (c := 2)
  decide +kernel

private theorem rightFinal5_case_3_1_checked : ((-1 : ℤ) ^ (rightScaleBit 5 3 1).val * positiveScale (rightScaleExponent 5 3 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 1 3 : ℤ)) • HexagonAtoms531.outerLeftABC = negativeScale (rightScaleExponent 5 3 1) • (rowColumnMul HexagonRowColumn531.rows_assocCAB HexagonRowColumn531.cols_right2) := by
  funext r
  fin_cases r
  · exact rightFinal5_case_3_1_row_0_0_0
  · exact rightFinal5_case_3_1_row_0_0_1
  · exact rightFinal5_case_3_1_row_1_0_0
  · exact rightFinal5_case_3_1_row_1_0_1
  · exact rightFinal5_case_3_1_row_2_0_0
  · exact rightFinal5_case_3_1_row_2_0_1
  · exact rightFinal5_case_3_1_row_3_0_0
  · exact rightFinal5_case_3_1_row_3_0_1
  · exact rightFinal5_case_3_1_row_4_0_0
  · exact rightFinal5_case_3_1_row_4_0_1
  · exact rightFinal5_case_3_1_row_5_0_0
  · exact rightFinal5_case_3_1_row_5_0_1
  · exact rightFinal5_case_3_1_row_6_0_0
  · exact rightFinal5_case_3_1_row_6_0_1
  · exact rightFinal5_case_3_1_row_7_0_0
  · exact rightFinal5_case_3_1_row_7_0_1

set_option backward.isDefEq.respectTransparency false in
theorem rightFinal5_case_3_1 : ((-1 : ℤ) ^ (rightScaleBit 5 3 1).val * positiveScale (rightScaleExponent 5 3 1) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 1 3 : ℤ)) • outerLeftZ 5 3 1 = negativeScale (rightScaleExponent 5 3 1) • (associatorZ 1 5 3 * right2Middle5 3 1) := by
  simpa only [HexagonAtoms531.assocABC_eq,
    HexagonAtoms531.outerABC_eq,
    HexagonAtoms531.assocBAC_eq,
    HexagonAtoms531.innerABC_eq,
    HexagonAtoms531.innerRightABC_eq,
    HexagonAtoms531.inverseACB_eq,
    HexagonAtoms531.innerACB_eq,
    HexagonAtoms531.assocBCA_eq,
    HexagonAtoms531.innerRightBAC_eq,
    HexagonAtoms531.assocCAB_eq,
    HexagonAtoms531.outerLeftABC_eq,
    HexagonRowColumn531.product0_eq,
    HexagonRowColumn531.product1_eq,
    HexagonRowColumn531.product2_eq,
    HexagonRowColumn531.product3_eq,
    HexagonRowColumn531.product4_eq,
    HexagonRowColumn531.product5_eq,
    HexagonRowColumn531.product6_eq,
    HexagonRowColumn531.product7_eq] using rightFinal5_case_3_1_checked

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonCases5
