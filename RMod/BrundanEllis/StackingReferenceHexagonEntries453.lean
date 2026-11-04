import RMod.BrundanEllis.StackingReferenceHexagonMiddle4
import RMod.BrundanEllis.StackingReferenceSparseMatrixCheck
import RMod.BrundanEllis.StackingReferenceHexagonAtoms453
import RMod.BrundanEllis.StackingReferenceHexagonRowColumn453

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

private theorem left0Middle4_eq_case_5_3_row_0_0_0 : (left0Middle4 5 3) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms453.assocABC) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_5_3_row_0_0_1 : (left0Middle4 5 3) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms453.assocABC) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_5_3_row_0_0_2 : (left0Middle4 5 3) ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms453.assocABC) ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_5_3_row_0_0_3 : (left0Middle4 5 3) ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms453.assocABC) ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_5_3_row_1_0_0 : (left0Middle4 5 3) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms453.assocABC) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_5_3_row_1_0_1 : (left0Middle4 5 3) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms453.assocABC) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_5_3_row_1_0_2 : (left0Middle4 5 3) ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms453.assocABC) ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_5_3_row_1_0_3 : (left0Middle4 5 3) ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms453.assocABC) ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_5_3_row_2_0_0 : (left0Middle4 5 3) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms453.assocABC) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_5_3_row_2_0_1 : (left0Middle4 5 3) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms453.assocABC) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_5_3_row_2_0_2 : (left0Middle4 5 3) ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms453.assocABC) ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_5_3_row_2_0_3 : (left0Middle4 5 3) ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms453.assocABC) ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_5_3_row_3_0_0 : (left0Middle4 5 3) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms453.assocABC) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_5_3_row_3_0_1 : (left0Middle4 5 3) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms453.assocABC) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_5_3_row_3_0_2 : (left0Middle4 5 3) ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms453.assocABC) ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_5_3_row_3_0_3 : (left0Middle4 5 3) ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms453.assocABC) ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_5_3_row_4_0_0 : (left0Middle4 5 3) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms453.assocABC) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_5_3_row_4_0_1 : (left0Middle4 5 3) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms453.assocABC) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_5_3_row_4_0_2 : (left0Middle4 5 3) ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms453.assocABC) ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_5_3_row_4_0_3 : (left0Middle4 5 3) ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms453.assocABC) ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_5_3_row_5_0_0 : (left0Middle4 5 3) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms453.assocABC) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_5_3_row_5_0_1 : (left0Middle4 5 3) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms453.assocABC) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_5_3_row_5_0_2 : (left0Middle4 5 3) ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms453.assocABC) ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_5_3_row_5_0_3 : (left0Middle4 5 3) ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms453.assocABC) ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_5_3_row_6_0_0 : (left0Middle4 5 3) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms453.assocABC) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_5_3_row_6_0_1 : (left0Middle4 5 3) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms453.assocABC) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_5_3_row_6_0_2 : (left0Middle4 5 3) ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms453.assocABC) ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_5_3_row_6_0_3 : (left0Middle4 5 3) ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms453.assocABC) ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_5_3_row_7_0_0 : (left0Middle4 5 3) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms453.assocABC) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_5_3_row_7_0_1 : (left0Middle4 5 3) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms453.assocABC) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_5_3_row_7_0_2 : (left0Middle4 5 3) ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms453.assocABC) ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_5_3_row_7_0_3 : (left0Middle4 5 3) ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms453.assocABC) ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left0Middle4_eq_case_5_3_checked : left0Middle4 5 3 = HexagonAtoms453.assocABC := by
  funext r
  fin_cases r
  · exact left0Middle4_eq_case_5_3_row_0_0_0
  · exact left0Middle4_eq_case_5_3_row_0_0_1
  · exact left0Middle4_eq_case_5_3_row_0_0_2
  · exact left0Middle4_eq_case_5_3_row_0_0_3
  · exact left0Middle4_eq_case_5_3_row_1_0_0
  · exact left0Middle4_eq_case_5_3_row_1_0_1
  · exact left0Middle4_eq_case_5_3_row_1_0_2
  · exact left0Middle4_eq_case_5_3_row_1_0_3
  · exact left0Middle4_eq_case_5_3_row_2_0_0
  · exact left0Middle4_eq_case_5_3_row_2_0_1
  · exact left0Middle4_eq_case_5_3_row_2_0_2
  · exact left0Middle4_eq_case_5_3_row_2_0_3
  · exact left0Middle4_eq_case_5_3_row_3_0_0
  · exact left0Middle4_eq_case_5_3_row_3_0_1
  · exact left0Middle4_eq_case_5_3_row_3_0_2
  · exact left0Middle4_eq_case_5_3_row_3_0_3
  · exact left0Middle4_eq_case_5_3_row_4_0_0
  · exact left0Middle4_eq_case_5_3_row_4_0_1
  · exact left0Middle4_eq_case_5_3_row_4_0_2
  · exact left0Middle4_eq_case_5_3_row_4_0_3
  · exact left0Middle4_eq_case_5_3_row_5_0_0
  · exact left0Middle4_eq_case_5_3_row_5_0_1
  · exact left0Middle4_eq_case_5_3_row_5_0_2
  · exact left0Middle4_eq_case_5_3_row_5_0_3
  · exact left0Middle4_eq_case_5_3_row_6_0_0
  · exact left0Middle4_eq_case_5_3_row_6_0_1
  · exact left0Middle4_eq_case_5_3_row_6_0_2
  · exact left0Middle4_eq_case_5_3_row_6_0_3
  · exact left0Middle4_eq_case_5_3_row_7_0_0
  · exact left0Middle4_eq_case_5_3_row_7_0_1
  · exact left0Middle4_eq_case_5_3_row_7_0_2
  · exact left0Middle4_eq_case_5_3_row_7_0_3

set_option backward.isDefEq.respectTransparency false in
theorem left0Middle4_eq_case_5_3 : left0Middle4 5 3 = outerRightZ 4 5 3 * associatorZ 4 5 3 := by
  simpa only [HexagonAtoms453.assocABC_eq,
    HexagonAtoms453.outerABC_eq,
    HexagonAtoms453.assocBAC_eq,
    HexagonAtoms453.innerABC_eq,
    HexagonAtoms453.innerRightABC_eq,
    HexagonAtoms453.inverseACB_eq,
    HexagonAtoms453.innerACB_eq,
    HexagonAtoms453.assocBCA_eq,
    HexagonAtoms453.innerRightBAC_eq,
    HexagonAtoms453.assocCAB_eq,
    HexagonAtoms453.outerLeftABC_eq,
    HexagonRowColumn453.product0_eq,
    HexagonRowColumn453.product1_eq,
    HexagonRowColumn453.product2_eq,
    HexagonRowColumn453.product3_eq,
    HexagonRowColumn453.product4_eq,
    HexagonRowColumn453.product5_eq,
    HexagonRowColumn453.product6_eq,
    HexagonRowColumn453.product7_eq] using left0Middle4_eq_case_5_3_checked

private theorem left1Middle4_eq_case_5_3_row_0_0_0 : (left1Middle4 5 3) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms453.assocBAC) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_5_3_row_0_0_1 : (left1Middle4 5 3) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms453.assocBAC) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_5_3_row_0_0_2 : (left1Middle4 5 3) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms453.assocBAC) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_5_3_row_0_0_3 : (left1Middle4 5 3) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms453.assocBAC) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_5_3_row_0_1_0 : (left1Middle4 5 3) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms453.assocBAC) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_5_3_row_0_1_1 : (left1Middle4 5 3) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms453.assocBAC) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_5_3_row_0_1_2 : (left1Middle4 5 3) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms453.assocBAC) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_5_3_row_0_1_3 : (left1Middle4 5 3) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms453.assocBAC) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_5_3_row_1_0_0 : (left1Middle4 5 3) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms453.assocBAC) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_5_3_row_1_0_1 : (left1Middle4 5 3) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms453.assocBAC) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_5_3_row_1_0_2 : (left1Middle4 5 3) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms453.assocBAC) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_5_3_row_1_0_3 : (left1Middle4 5 3) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms453.assocBAC) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_5_3_row_1_1_0 : (left1Middle4 5 3) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms453.assocBAC) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_5_3_row_1_1_1 : (left1Middle4 5 3) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms453.assocBAC) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_5_3_row_1_1_2 : (left1Middle4 5 3) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms453.assocBAC) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_5_3_row_1_1_3 : (left1Middle4 5 3) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms453.assocBAC) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_5_3_row_2_0_0 : (left1Middle4 5 3) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms453.assocBAC) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_5_3_row_2_0_1 : (left1Middle4 5 3) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms453.assocBAC) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_5_3_row_2_0_2 : (left1Middle4 5 3) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms453.assocBAC) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_5_3_row_2_0_3 : (left1Middle4 5 3) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms453.assocBAC) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_5_3_row_2_1_0 : (left1Middle4 5 3) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms453.assocBAC) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_5_3_row_2_1_1 : (left1Middle4 5 3) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms453.assocBAC) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_5_3_row_2_1_2 : (left1Middle4 5 3) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms453.assocBAC) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_5_3_row_2_1_3 : (left1Middle4 5 3) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms453.assocBAC) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_5_3_row_3_0_0 : (left1Middle4 5 3) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (HexagonAtoms453.assocBAC) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_5_3_row_3_0_1 : (left1Middle4 5 3) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (HexagonAtoms453.assocBAC) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_5_3_row_3_0_2 : (left1Middle4 5 3) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (HexagonAtoms453.assocBAC) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_5_3_row_3_0_3 : (left1Middle4 5 3) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (HexagonAtoms453.assocBAC) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_5_3_row_3_1_0 : (left1Middle4 5 3) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (HexagonAtoms453.assocBAC) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_5_3_row_3_1_1 : (left1Middle4 5 3) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (HexagonAtoms453.assocBAC) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_5_3_row_3_1_2 : (left1Middle4 5 3) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (HexagonAtoms453.assocBAC) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_5_3_row_3_1_3 : (left1Middle4 5 3) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (HexagonAtoms453.assocBAC) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem left1Middle4_eq_case_5_3_checked : left1Middle4 5 3 = HexagonAtoms453.assocBAC := by
  funext r
  fin_cases r
  · exact left1Middle4_eq_case_5_3_row_0_0_0
  · exact left1Middle4_eq_case_5_3_row_0_0_1
  · exact left1Middle4_eq_case_5_3_row_0_0_2
  · exact left1Middle4_eq_case_5_3_row_0_0_3
  · exact left1Middle4_eq_case_5_3_row_0_1_0
  · exact left1Middle4_eq_case_5_3_row_0_1_1
  · exact left1Middle4_eq_case_5_3_row_0_1_2
  · exact left1Middle4_eq_case_5_3_row_0_1_3
  · exact left1Middle4_eq_case_5_3_row_1_0_0
  · exact left1Middle4_eq_case_5_3_row_1_0_1
  · exact left1Middle4_eq_case_5_3_row_1_0_2
  · exact left1Middle4_eq_case_5_3_row_1_0_3
  · exact left1Middle4_eq_case_5_3_row_1_1_0
  · exact left1Middle4_eq_case_5_3_row_1_1_1
  · exact left1Middle4_eq_case_5_3_row_1_1_2
  · exact left1Middle4_eq_case_5_3_row_1_1_3
  · exact left1Middle4_eq_case_5_3_row_2_0_0
  · exact left1Middle4_eq_case_5_3_row_2_0_1
  · exact left1Middle4_eq_case_5_3_row_2_0_2
  · exact left1Middle4_eq_case_5_3_row_2_0_3
  · exact left1Middle4_eq_case_5_3_row_2_1_0
  · exact left1Middle4_eq_case_5_3_row_2_1_1
  · exact left1Middle4_eq_case_5_3_row_2_1_2
  · exact left1Middle4_eq_case_5_3_row_2_1_3
  · exact left1Middle4_eq_case_5_3_row_3_0_0
  · exact left1Middle4_eq_case_5_3_row_3_0_1
  · exact left1Middle4_eq_case_5_3_row_3_0_2
  · exact left1Middle4_eq_case_5_3_row_3_0_3
  · exact left1Middle4_eq_case_5_3_row_3_1_0
  · exact left1Middle4_eq_case_5_3_row_3_1_1
  · exact left1Middle4_eq_case_5_3_row_3_1_2
  · exact left1Middle4_eq_case_5_3_row_3_1_3

set_option backward.isDefEq.respectTransparency false in
theorem left1Middle4_eq_case_5_3 : left1Middle4 5 3 = associatorZ 5 4 3 * innerLeftZ 4 5 3 := by
  simpa only [HexagonAtoms453.assocABC_eq,
    HexagonAtoms453.outerABC_eq,
    HexagonAtoms453.assocBAC_eq,
    HexagonAtoms453.innerABC_eq,
    HexagonAtoms453.innerRightABC_eq,
    HexagonAtoms453.inverseACB_eq,
    HexagonAtoms453.innerACB_eq,
    HexagonAtoms453.assocBCA_eq,
    HexagonAtoms453.innerRightBAC_eq,
    HexagonAtoms453.assocCAB_eq,
    HexagonAtoms453.outerLeftABC_eq,
    HexagonRowColumn453.product0_eq,
    HexagonRowColumn453.product1_eq,
    HexagonRowColumn453.product2_eq,
    HexagonRowColumn453.product3_eq,
    HexagonRowColumn453.product4_eq,
    HexagonRowColumn453.product5_eq,
    HexagonRowColumn453.product6_eq,
    HexagonRowColumn453.product7_eq] using left1Middle4_eq_case_5_3_checked

private theorem right0Middle4_eq_case_5_3_row_0_0_0 : (right0Middle4 5 3) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms453.assocABC) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_5_3_row_0_0_1 : (right0Middle4 5 3) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms453.assocABC) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_5_3_row_0_0_2 : (right0Middle4 5 3) ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms453.assocABC) ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_5_3_row_0_0_3 : (right0Middle4 5 3) ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms453.assocABC) ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_5_3_row_1_0_0 : (right0Middle4 5 3) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms453.assocABC) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_5_3_row_1_0_1 : (right0Middle4 5 3) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms453.assocABC) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_5_3_row_1_0_2 : (right0Middle4 5 3) ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms453.assocABC) ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_5_3_row_1_0_3 : (right0Middle4 5 3) ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms453.assocABC) ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_5_3_row_2_0_0 : (right0Middle4 5 3) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms453.assocABC) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_5_3_row_2_0_1 : (right0Middle4 5 3) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms453.assocABC) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_5_3_row_2_0_2 : (right0Middle4 5 3) ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms453.assocABC) ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_5_3_row_2_0_3 : (right0Middle4 5 3) ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms453.assocABC) ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_5_3_row_3_0_0 : (right0Middle4 5 3) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms453.assocABC) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_5_3_row_3_0_1 : (right0Middle4 5 3) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms453.assocABC) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_5_3_row_3_0_2 : (right0Middle4 5 3) ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms453.assocABC) ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_5_3_row_3_0_3 : (right0Middle4 5 3) ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms453.assocABC) ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_5_3_row_4_0_0 : (right0Middle4 5 3) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms453.assocABC) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_5_3_row_4_0_1 : (right0Middle4 5 3) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms453.assocABC) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_5_3_row_4_0_2 : (right0Middle4 5 3) ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms453.assocABC) ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_5_3_row_4_0_3 : (right0Middle4 5 3) ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms453.assocABC) ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_5_3_row_5_0_0 : (right0Middle4 5 3) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms453.assocABC) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_5_3_row_5_0_1 : (right0Middle4 5 3) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms453.assocABC) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_5_3_row_5_0_2 : (right0Middle4 5 3) ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms453.assocABC) ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_5_3_row_5_0_3 : (right0Middle4 5 3) ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms453.assocABC) ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_5_3_row_6_0_0 : (right0Middle4 5 3) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms453.assocABC) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_5_3_row_6_0_1 : (right0Middle4 5 3) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms453.assocABC) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_5_3_row_6_0_2 : (right0Middle4 5 3) ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms453.assocABC) ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_5_3_row_6_0_3 : (right0Middle4 5 3) ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms453.assocABC) ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_5_3_row_7_0_0 : (right0Middle4 5 3) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = (HexagonAtoms453.assocABC) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_5_3_row_7_0_1 : (right0Middle4 5 3) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = (HexagonAtoms453.assocABC) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_5_3_row_7_0_2 : (right0Middle4 5 3) ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = (HexagonAtoms453.assocABC) ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_5_3_row_7_0_3 : (right0Middle4 5 3) ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = (HexagonAtoms453.assocABC) ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right0Middle4_eq_case_5_3_checked : right0Middle4 5 3 = HexagonAtoms453.assocABC := by
  funext r
  fin_cases r
  · exact right0Middle4_eq_case_5_3_row_0_0_0
  · exact right0Middle4_eq_case_5_3_row_0_0_1
  · exact right0Middle4_eq_case_5_3_row_0_0_2
  · exact right0Middle4_eq_case_5_3_row_0_0_3
  · exact right0Middle4_eq_case_5_3_row_1_0_0
  · exact right0Middle4_eq_case_5_3_row_1_0_1
  · exact right0Middle4_eq_case_5_3_row_1_0_2
  · exact right0Middle4_eq_case_5_3_row_1_0_3
  · exact right0Middle4_eq_case_5_3_row_2_0_0
  · exact right0Middle4_eq_case_5_3_row_2_0_1
  · exact right0Middle4_eq_case_5_3_row_2_0_2
  · exact right0Middle4_eq_case_5_3_row_2_0_3
  · exact right0Middle4_eq_case_5_3_row_3_0_0
  · exact right0Middle4_eq_case_5_3_row_3_0_1
  · exact right0Middle4_eq_case_5_3_row_3_0_2
  · exact right0Middle4_eq_case_5_3_row_3_0_3
  · exact right0Middle4_eq_case_5_3_row_4_0_0
  · exact right0Middle4_eq_case_5_3_row_4_0_1
  · exact right0Middle4_eq_case_5_3_row_4_0_2
  · exact right0Middle4_eq_case_5_3_row_4_0_3
  · exact right0Middle4_eq_case_5_3_row_5_0_0
  · exact right0Middle4_eq_case_5_3_row_5_0_1
  · exact right0Middle4_eq_case_5_3_row_5_0_2
  · exact right0Middle4_eq_case_5_3_row_5_0_3
  · exact right0Middle4_eq_case_5_3_row_6_0_0
  · exact right0Middle4_eq_case_5_3_row_6_0_1
  · exact right0Middle4_eq_case_5_3_row_6_0_2
  · exact right0Middle4_eq_case_5_3_row_6_0_3
  · exact right0Middle4_eq_case_5_3_row_7_0_0
  · exact right0Middle4_eq_case_5_3_row_7_0_1
  · exact right0Middle4_eq_case_5_3_row_7_0_2
  · exact right0Middle4_eq_case_5_3_row_7_0_3

set_option backward.isDefEq.respectTransparency false in
theorem right0Middle4_eq_case_5_3 : right0Middle4 5 3 = innerRightZ 4 5 3 * associatorZ 4 5 3 := by
  simpa only [HexagonAtoms453.assocABC_eq,
    HexagonAtoms453.outerABC_eq,
    HexagonAtoms453.assocBAC_eq,
    HexagonAtoms453.innerABC_eq,
    HexagonAtoms453.innerRightABC_eq,
    HexagonAtoms453.inverseACB_eq,
    HexagonAtoms453.innerACB_eq,
    HexagonAtoms453.assocBCA_eq,
    HexagonAtoms453.innerRightBAC_eq,
    HexagonAtoms453.assocCAB_eq,
    HexagonAtoms453.outerLeftABC_eq,
    HexagonRowColumn453.product0_eq,
    HexagonRowColumn453.product1_eq,
    HexagonRowColumn453.product2_eq,
    HexagonRowColumn453.product3_eq,
    HexagonRowColumn453.product4_eq,
    HexagonRowColumn453.product5_eq,
    HexagonRowColumn453.product6_eq,
    HexagonRowColumn453.product7_eq] using right0Middle4_eq_case_5_3_checked

private theorem right1Middle4_eq_case_5_3_row_0_0_0 : (right1Middle4 5 3) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn453.rows_inverseACB HexagonRowColumn453.cols_right0) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_5_3_row_0_0_1 : (right1Middle4 5 3) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn453.rows_inverseACB HexagonRowColumn453.cols_right0) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_5_3_row_0_0_2 : (right1Middle4 5 3) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn453.rows_inverseACB HexagonRowColumn453.cols_right0) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_5_3_row_0_0_3 : (right1Middle4 5 3) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn453.rows_inverseACB HexagonRowColumn453.cols_right0) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_5_3_row_0_1_0 : (right1Middle4 5 3) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn453.rows_inverseACB HexagonRowColumn453.cols_right0) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_5_3_row_0_1_1 : (right1Middle4 5 3) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn453.rows_inverseACB HexagonRowColumn453.cols_right0) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_5_3_row_0_1_2 : (right1Middle4 5 3) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn453.rows_inverseACB HexagonRowColumn453.cols_right0) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_5_3_row_0_1_3 : (right1Middle4 5 3) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn453.rows_inverseACB HexagonRowColumn453.cols_right0) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_5_3_row_1_0_0 : (right1Middle4 5 3) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn453.rows_inverseACB HexagonRowColumn453.cols_right0) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_5_3_row_1_0_1 : (right1Middle4 5 3) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn453.rows_inverseACB HexagonRowColumn453.cols_right0) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_5_3_row_1_0_2 : (right1Middle4 5 3) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn453.rows_inverseACB HexagonRowColumn453.cols_right0) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_5_3_row_1_0_3 : (right1Middle4 5 3) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn453.rows_inverseACB HexagonRowColumn453.cols_right0) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_5_3_row_1_1_0 : (right1Middle4 5 3) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn453.rows_inverseACB HexagonRowColumn453.cols_right0) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_5_3_row_1_1_1 : (right1Middle4 5 3) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn453.rows_inverseACB HexagonRowColumn453.cols_right0) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_5_3_row_1_1_2 : (right1Middle4 5 3) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn453.rows_inverseACB HexagonRowColumn453.cols_right0) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_5_3_row_1_1_3 : (right1Middle4 5 3) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn453.rows_inverseACB HexagonRowColumn453.cols_right0) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_5_3_row_2_0_0 : (right1Middle4 5 3) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn453.rows_inverseACB HexagonRowColumn453.cols_right0) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_5_3_row_2_0_1 : (right1Middle4 5 3) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn453.rows_inverseACB HexagonRowColumn453.cols_right0) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_5_3_row_2_0_2 : (right1Middle4 5 3) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn453.rows_inverseACB HexagonRowColumn453.cols_right0) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_5_3_row_2_0_3 : (right1Middle4 5 3) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn453.rows_inverseACB HexagonRowColumn453.cols_right0) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_5_3_row_2_1_0 : (right1Middle4 5 3) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn453.rows_inverseACB HexagonRowColumn453.cols_right0) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_5_3_row_2_1_1 : (right1Middle4 5 3) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn453.rows_inverseACB HexagonRowColumn453.cols_right0) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_5_3_row_2_1_2 : (right1Middle4 5 3) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn453.rows_inverseACB HexagonRowColumn453.cols_right0) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_5_3_row_2_1_3 : (right1Middle4 5 3) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn453.rows_inverseACB HexagonRowColumn453.cols_right0) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_5_3_row_3_0_0 : (right1Middle4 5 3) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn453.rows_inverseACB HexagonRowColumn453.cols_right0) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_5_3_row_3_0_1 : (right1Middle4 5 3) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn453.rows_inverseACB HexagonRowColumn453.cols_right0) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_5_3_row_3_0_2 : (right1Middle4 5 3) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn453.rows_inverseACB HexagonRowColumn453.cols_right0) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_5_3_row_3_0_3 : (right1Middle4 5 3) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn453.rows_inverseACB HexagonRowColumn453.cols_right0) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_5_3_row_3_1_0 : (right1Middle4 5 3) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (rowColumnMul HexagonRowColumn453.rows_inverseACB HexagonRowColumn453.cols_right0) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_5_3_row_3_1_1 : (right1Middle4 5 3) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (rowColumnMul HexagonRowColumn453.rows_inverseACB HexagonRowColumn453.cols_right0) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_5_3_row_3_1_2 : (right1Middle4 5 3) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (rowColumnMul HexagonRowColumn453.rows_inverseACB HexagonRowColumn453.cols_right0) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_5_3_row_3_1_3 : (right1Middle4 5 3) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (rowColumnMul HexagonRowColumn453.rows_inverseACB HexagonRowColumn453.cols_right0) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right1Middle4_eq_case_5_3_checked : right1Middle4 5 3 = rowColumnMul HexagonRowColumn453.rows_inverseACB HexagonRowColumn453.cols_right0 := by
  funext r
  fin_cases r
  · exact right1Middle4_eq_case_5_3_row_0_0_0
  · exact right1Middle4_eq_case_5_3_row_0_0_1
  · exact right1Middle4_eq_case_5_3_row_0_0_2
  · exact right1Middle4_eq_case_5_3_row_0_0_3
  · exact right1Middle4_eq_case_5_3_row_0_1_0
  · exact right1Middle4_eq_case_5_3_row_0_1_1
  · exact right1Middle4_eq_case_5_3_row_0_1_2
  · exact right1Middle4_eq_case_5_3_row_0_1_3
  · exact right1Middle4_eq_case_5_3_row_1_0_0
  · exact right1Middle4_eq_case_5_3_row_1_0_1
  · exact right1Middle4_eq_case_5_3_row_1_0_2
  · exact right1Middle4_eq_case_5_3_row_1_0_3
  · exact right1Middle4_eq_case_5_3_row_1_1_0
  · exact right1Middle4_eq_case_5_3_row_1_1_1
  · exact right1Middle4_eq_case_5_3_row_1_1_2
  · exact right1Middle4_eq_case_5_3_row_1_1_3
  · exact right1Middle4_eq_case_5_3_row_2_0_0
  · exact right1Middle4_eq_case_5_3_row_2_0_1
  · exact right1Middle4_eq_case_5_3_row_2_0_2
  · exact right1Middle4_eq_case_5_3_row_2_0_3
  · exact right1Middle4_eq_case_5_3_row_2_1_0
  · exact right1Middle4_eq_case_5_3_row_2_1_1
  · exact right1Middle4_eq_case_5_3_row_2_1_2
  · exact right1Middle4_eq_case_5_3_row_2_1_3
  · exact right1Middle4_eq_case_5_3_row_3_0_0
  · exact right1Middle4_eq_case_5_3_row_3_0_1
  · exact right1Middle4_eq_case_5_3_row_3_0_2
  · exact right1Middle4_eq_case_5_3_row_3_0_3
  · exact right1Middle4_eq_case_5_3_row_3_1_0
  · exact right1Middle4_eq_case_5_3_row_3_1_1
  · exact right1Middle4_eq_case_5_3_row_3_1_2
  · exact right1Middle4_eq_case_5_3_row_3_1_3

set_option backward.isDefEq.respectTransparency false in
theorem right1Middle4_eq_case_5_3 : right1Middle4 5 3 = associatorInverseZ 4 3 5 * right0Middle4 5 3 := by
  simpa only [HexagonAtoms453.assocABC_eq,
    HexagonAtoms453.outerABC_eq,
    HexagonAtoms453.assocBAC_eq,
    HexagonAtoms453.innerABC_eq,
    HexagonAtoms453.innerRightABC_eq,
    HexagonAtoms453.inverseACB_eq,
    HexagonAtoms453.innerACB_eq,
    HexagonAtoms453.assocBCA_eq,
    HexagonAtoms453.innerRightBAC_eq,
    HexagonAtoms453.assocCAB_eq,
    HexagonAtoms453.outerLeftABC_eq,
    HexagonRowColumn453.product0_eq,
    HexagonRowColumn453.product1_eq,
    HexagonRowColumn453.product2_eq,
    HexagonRowColumn453.product3_eq,
    HexagonRowColumn453.product4_eq,
    HexagonRowColumn453.product5_eq,
    HexagonRowColumn453.product6_eq,
    HexagonRowColumn453.product7_eq] using right1Middle4_eq_case_5_3_checked

private theorem right2Middle4_eq_case_5_3_row_0_0_0 : (right2Middle4 5 3) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (right1Middle4 5 3) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_5_3_row_0_0_1 : (right2Middle4 5 3) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (right1Middle4 5 3) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_5_3_row_0_0_2 : (right2Middle4 5 3) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (right1Middle4 5 3) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_5_3_row_0_0_3 : (right2Middle4 5 3) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (right1Middle4 5 3) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_5_3_row_0_1_0 : (right2Middle4 5 3) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (right1Middle4 5 3) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_5_3_row_0_1_1 : (right2Middle4 5 3) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (right1Middle4 5 3) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_5_3_row_0_1_2 : (right2Middle4 5 3) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (right1Middle4 5 3) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_5_3_row_0_1_3 : (right2Middle4 5 3) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (right1Middle4 5 3) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_5_3_row_1_0_0 : (right2Middle4 5 3) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (right1Middle4 5 3) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_5_3_row_1_0_1 : (right2Middle4 5 3) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (right1Middle4 5 3) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_5_3_row_1_0_2 : (right2Middle4 5 3) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (right1Middle4 5 3) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_5_3_row_1_0_3 : (right2Middle4 5 3) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (right1Middle4 5 3) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_5_3_row_1_1_0 : (right2Middle4 5 3) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (right1Middle4 5 3) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_5_3_row_1_1_1 : (right2Middle4 5 3) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (right1Middle4 5 3) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_5_3_row_1_1_2 : (right2Middle4 5 3) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (right1Middle4 5 3) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_5_3_row_1_1_3 : (right2Middle4 5 3) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (right1Middle4 5 3) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_5_3_row_2_0_0 : (right2Middle4 5 3) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (right1Middle4 5 3) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_5_3_row_2_0_1 : (right2Middle4 5 3) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (right1Middle4 5 3) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_5_3_row_2_0_2 : (right2Middle4 5 3) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (right1Middle4 5 3) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_5_3_row_2_0_3 : (right2Middle4 5 3) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (right1Middle4 5 3) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_5_3_row_2_1_0 : (right2Middle4 5 3) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (right1Middle4 5 3) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_5_3_row_2_1_1 : (right2Middle4 5 3) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (right1Middle4 5 3) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_5_3_row_2_1_2 : (right2Middle4 5 3) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (right1Middle4 5 3) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_5_3_row_2_1_3 : (right2Middle4 5 3) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (right1Middle4 5 3) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_5_3_row_3_0_0 : (right2Middle4 5 3) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (right1Middle4 5 3) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_5_3_row_3_0_1 : (right2Middle4 5 3) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (right1Middle4 5 3) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_5_3_row_3_0_2 : (right2Middle4 5 3) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (right1Middle4 5 3) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_5_3_row_3_0_3 : (right2Middle4 5 3) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (right1Middle4 5 3) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_5_3_row_3_1_0 : (right2Middle4 5 3) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (right1Middle4 5 3) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_5_3_row_3_1_1 : (right2Middle4 5 3) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (right1Middle4 5 3) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_5_3_row_3_1_2 : (right2Middle4 5 3) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (right1Middle4 5 3) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_5_3_row_3_1_3 : (right2Middle4 5 3) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (right1Middle4 5 3) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem right2Middle4_eq_case_5_3_checked : right2Middle4 5 3 = right1Middle4 5 3 := by
  funext r
  fin_cases r
  · exact right2Middle4_eq_case_5_3_row_0_0_0
  · exact right2Middle4_eq_case_5_3_row_0_0_1
  · exact right2Middle4_eq_case_5_3_row_0_0_2
  · exact right2Middle4_eq_case_5_3_row_0_0_3
  · exact right2Middle4_eq_case_5_3_row_0_1_0
  · exact right2Middle4_eq_case_5_3_row_0_1_1
  · exact right2Middle4_eq_case_5_3_row_0_1_2
  · exact right2Middle4_eq_case_5_3_row_0_1_3
  · exact right2Middle4_eq_case_5_3_row_1_0_0
  · exact right2Middle4_eq_case_5_3_row_1_0_1
  · exact right2Middle4_eq_case_5_3_row_1_0_2
  · exact right2Middle4_eq_case_5_3_row_1_0_3
  · exact right2Middle4_eq_case_5_3_row_1_1_0
  · exact right2Middle4_eq_case_5_3_row_1_1_1
  · exact right2Middle4_eq_case_5_3_row_1_1_2
  · exact right2Middle4_eq_case_5_3_row_1_1_3
  · exact right2Middle4_eq_case_5_3_row_2_0_0
  · exact right2Middle4_eq_case_5_3_row_2_0_1
  · exact right2Middle4_eq_case_5_3_row_2_0_2
  · exact right2Middle4_eq_case_5_3_row_2_0_3
  · exact right2Middle4_eq_case_5_3_row_2_1_0
  · exact right2Middle4_eq_case_5_3_row_2_1_1
  · exact right2Middle4_eq_case_5_3_row_2_1_2
  · exact right2Middle4_eq_case_5_3_row_2_1_3
  · exact right2Middle4_eq_case_5_3_row_3_0_0
  · exact right2Middle4_eq_case_5_3_row_3_0_1
  · exact right2Middle4_eq_case_5_3_row_3_0_2
  · exact right2Middle4_eq_case_5_3_row_3_0_3
  · exact right2Middle4_eq_case_5_3_row_3_1_0
  · exact right2Middle4_eq_case_5_3_row_3_1_1
  · exact right2Middle4_eq_case_5_3_row_3_1_2
  · exact right2Middle4_eq_case_5_3_row_3_1_3

set_option backward.isDefEq.respectTransparency false in
theorem right2Middle4_eq_case_5_3 : right2Middle4 5 3 = innerLeftZ 4 3 5 * right1Middle4 5 3 := by
  simpa only [HexagonAtoms453.assocABC_eq,
    HexagonAtoms453.outerABC_eq,
    HexagonAtoms453.assocBAC_eq,
    HexagonAtoms453.innerABC_eq,
    HexagonAtoms453.innerRightABC_eq,
    HexagonAtoms453.inverseACB_eq,
    HexagonAtoms453.innerACB_eq,
    HexagonAtoms453.assocBCA_eq,
    HexagonAtoms453.innerRightBAC_eq,
    HexagonAtoms453.assocCAB_eq,
    HexagonAtoms453.outerLeftABC_eq,
    HexagonRowColumn453.product0_eq,
    HexagonRowColumn453.product1_eq,
    HexagonRowColumn453.product2_eq,
    HexagonRowColumn453.product3_eq,
    HexagonRowColumn453.product4_eq,
    HexagonRowColumn453.product5_eq,
    HexagonRowColumn453.product6_eq,
    HexagonRowColumn453.product7_eq] using right2Middle4_eq_case_5_3_checked

private theorem leftFinal4_case_5_3_row_0_0_0 : (((-1 : ℤ) ^ (leftScaleBit 4 5 3).val * positiveScale (leftScaleExponent 4 5 3)) •
      (rowColumnMul HexagonRowColumn453.rows_assocBCA HexagonRowColumn453.cols_left0)) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 4 5 3) • (left1Middle4 5 3)) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal4_case_5_3_row_0_0_1 : (((-1 : ℤ) ^ (leftScaleBit 4 5 3).val * positiveScale (leftScaleExponent 4 5 3)) •
      (rowColumnMul HexagonRowColumn453.rows_assocBCA HexagonRowColumn453.cols_left0)) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 4 5 3) • (left1Middle4 5 3)) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal4_case_5_3_row_0_0_2 : (((-1 : ℤ) ^ (leftScaleBit 4 5 3).val * positiveScale (leftScaleExponent 4 5 3)) •
      (rowColumnMul HexagonRowColumn453.rows_assocBCA HexagonRowColumn453.cols_left0)) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 4 5 3) • (left1Middle4 5 3)) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal4_case_5_3_row_0_0_3 : (((-1 : ℤ) ^ (leftScaleBit 4 5 3).val * positiveScale (leftScaleExponent 4 5 3)) •
      (rowColumnMul HexagonRowColumn453.rows_assocBCA HexagonRowColumn453.cols_left0)) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 4 5 3) • (left1Middle4 5 3)) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal4_case_5_3_row_0_1_0 : (((-1 : ℤ) ^ (leftScaleBit 4 5 3).val * positiveScale (leftScaleExponent 4 5 3)) •
      (rowColumnMul HexagonRowColumn453.rows_assocBCA HexagonRowColumn453.cols_left0)) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 4 5 3) • (left1Middle4 5 3)) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal4_case_5_3_row_0_1_1 : (((-1 : ℤ) ^ (leftScaleBit 4 5 3).val * positiveScale (leftScaleExponent 4 5 3)) •
      (rowColumnMul HexagonRowColumn453.rows_assocBCA HexagonRowColumn453.cols_left0)) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 4 5 3) • (left1Middle4 5 3)) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal4_case_5_3_row_0_1_2 : (((-1 : ℤ) ^ (leftScaleBit 4 5 3).val * positiveScale (leftScaleExponent 4 5 3)) •
      (rowColumnMul HexagonRowColumn453.rows_assocBCA HexagonRowColumn453.cols_left0)) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 4 5 3) • (left1Middle4 5 3)) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal4_case_5_3_row_0_1_3 : (((-1 : ℤ) ^ (leftScaleBit 4 5 3).val * positiveScale (leftScaleExponent 4 5 3)) •
      (rowColumnMul HexagonRowColumn453.rows_assocBCA HexagonRowColumn453.cols_left0)) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 4 5 3) • (left1Middle4 5 3)) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal4_case_5_3_row_1_0_0 : (((-1 : ℤ) ^ (leftScaleBit 4 5 3).val * positiveScale (leftScaleExponent 4 5 3)) •
      (rowColumnMul HexagonRowColumn453.rows_assocBCA HexagonRowColumn453.cols_left0)) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 4 5 3) • (left1Middle4 5 3)) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal4_case_5_3_row_1_0_1 : (((-1 : ℤ) ^ (leftScaleBit 4 5 3).val * positiveScale (leftScaleExponent 4 5 3)) •
      (rowColumnMul HexagonRowColumn453.rows_assocBCA HexagonRowColumn453.cols_left0)) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 4 5 3) • (left1Middle4 5 3)) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal4_case_5_3_row_1_0_2 : (((-1 : ℤ) ^ (leftScaleBit 4 5 3).val * positiveScale (leftScaleExponent 4 5 3)) •
      (rowColumnMul HexagonRowColumn453.rows_assocBCA HexagonRowColumn453.cols_left0)) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 4 5 3) • (left1Middle4 5 3)) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal4_case_5_3_row_1_0_3 : (((-1 : ℤ) ^ (leftScaleBit 4 5 3).val * positiveScale (leftScaleExponent 4 5 3)) •
      (rowColumnMul HexagonRowColumn453.rows_assocBCA HexagonRowColumn453.cols_left0)) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 4 5 3) • (left1Middle4 5 3)) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal4_case_5_3_row_1_1_0 : (((-1 : ℤ) ^ (leftScaleBit 4 5 3).val * positiveScale (leftScaleExponent 4 5 3)) •
      (rowColumnMul HexagonRowColumn453.rows_assocBCA HexagonRowColumn453.cols_left0)) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 4 5 3) • (left1Middle4 5 3)) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal4_case_5_3_row_1_1_1 : (((-1 : ℤ) ^ (leftScaleBit 4 5 3).val * positiveScale (leftScaleExponent 4 5 3)) •
      (rowColumnMul HexagonRowColumn453.rows_assocBCA HexagonRowColumn453.cols_left0)) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 4 5 3) • (left1Middle4 5 3)) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal4_case_5_3_row_1_1_2 : (((-1 : ℤ) ^ (leftScaleBit 4 5 3).val * positiveScale (leftScaleExponent 4 5 3)) •
      (rowColumnMul HexagonRowColumn453.rows_assocBCA HexagonRowColumn453.cols_left0)) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 4 5 3) • (left1Middle4 5 3)) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal4_case_5_3_row_1_1_3 : (((-1 : ℤ) ^ (leftScaleBit 4 5 3).val * positiveScale (leftScaleExponent 4 5 3)) •
      (rowColumnMul HexagonRowColumn453.rows_assocBCA HexagonRowColumn453.cols_left0)) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 4 5 3) • (left1Middle4 5 3)) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal4_case_5_3_row_2_0_0 : (((-1 : ℤ) ^ (leftScaleBit 4 5 3).val * positiveScale (leftScaleExponent 4 5 3)) •
      (rowColumnMul HexagonRowColumn453.rows_assocBCA HexagonRowColumn453.cols_left0)) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 4 5 3) • (left1Middle4 5 3)) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal4_case_5_3_row_2_0_1 : (((-1 : ℤ) ^ (leftScaleBit 4 5 3).val * positiveScale (leftScaleExponent 4 5 3)) •
      (rowColumnMul HexagonRowColumn453.rows_assocBCA HexagonRowColumn453.cols_left0)) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 4 5 3) • (left1Middle4 5 3)) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal4_case_5_3_row_2_0_2 : (((-1 : ℤ) ^ (leftScaleBit 4 5 3).val * positiveScale (leftScaleExponent 4 5 3)) •
      (rowColumnMul HexagonRowColumn453.rows_assocBCA HexagonRowColumn453.cols_left0)) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 4 5 3) • (left1Middle4 5 3)) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal4_case_5_3_row_2_0_3 : (((-1 : ℤ) ^ (leftScaleBit 4 5 3).val * positiveScale (leftScaleExponent 4 5 3)) •
      (rowColumnMul HexagonRowColumn453.rows_assocBCA HexagonRowColumn453.cols_left0)) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 4 5 3) • (left1Middle4 5 3)) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal4_case_5_3_row_2_1_0 : (((-1 : ℤ) ^ (leftScaleBit 4 5 3).val * positiveScale (leftScaleExponent 4 5 3)) •
      (rowColumnMul HexagonRowColumn453.rows_assocBCA HexagonRowColumn453.cols_left0)) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 4 5 3) • (left1Middle4 5 3)) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal4_case_5_3_row_2_1_1 : (((-1 : ℤ) ^ (leftScaleBit 4 5 3).val * positiveScale (leftScaleExponent 4 5 3)) •
      (rowColumnMul HexagonRowColumn453.rows_assocBCA HexagonRowColumn453.cols_left0)) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 4 5 3) • (left1Middle4 5 3)) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal4_case_5_3_row_2_1_2 : (((-1 : ℤ) ^ (leftScaleBit 4 5 3).val * positiveScale (leftScaleExponent 4 5 3)) •
      (rowColumnMul HexagonRowColumn453.rows_assocBCA HexagonRowColumn453.cols_left0)) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 4 5 3) • (left1Middle4 5 3)) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal4_case_5_3_row_2_1_3 : (((-1 : ℤ) ^ (leftScaleBit 4 5 3).val * positiveScale (leftScaleExponent 4 5 3)) •
      (rowColumnMul HexagonRowColumn453.rows_assocBCA HexagonRowColumn453.cols_left0)) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 4 5 3) • (left1Middle4 5 3)) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal4_case_5_3_row_3_0_0 : (((-1 : ℤ) ^ (leftScaleBit 4 5 3).val * positiveScale (leftScaleExponent 4 5 3)) •
      (rowColumnMul HexagonRowColumn453.rows_assocBCA HexagonRowColumn453.cols_left0)) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 4 5 3) • (left1Middle4 5 3)) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal4_case_5_3_row_3_0_1 : (((-1 : ℤ) ^ (leftScaleBit 4 5 3).val * positiveScale (leftScaleExponent 4 5 3)) •
      (rowColumnMul HexagonRowColumn453.rows_assocBCA HexagonRowColumn453.cols_left0)) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 4 5 3) • (left1Middle4 5 3)) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal4_case_5_3_row_3_0_2 : (((-1 : ℤ) ^ (leftScaleBit 4 5 3).val * positiveScale (leftScaleExponent 4 5 3)) •
      (rowColumnMul HexagonRowColumn453.rows_assocBCA HexagonRowColumn453.cols_left0)) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 4 5 3) • (left1Middle4 5 3)) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal4_case_5_3_row_3_0_3 : (((-1 : ℤ) ^ (leftScaleBit 4 5 3).val * positiveScale (leftScaleExponent 4 5 3)) •
      (rowColumnMul HexagonRowColumn453.rows_assocBCA HexagonRowColumn453.cols_left0)) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 4 5 3) • (left1Middle4 5 3)) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal4_case_5_3_row_3_1_0 : (((-1 : ℤ) ^ (leftScaleBit 4 5 3).val * positiveScale (leftScaleExponent 4 5 3)) •
      (rowColumnMul HexagonRowColumn453.rows_assocBCA HexagonRowColumn453.cols_left0)) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (leftScaleExponent 4 5 3) • (left1Middle4 5 3)) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal4_case_5_3_row_3_1_1 : (((-1 : ℤ) ^ (leftScaleBit 4 5 3).val * positiveScale (leftScaleExponent 4 5 3)) •
      (rowColumnMul HexagonRowColumn453.rows_assocBCA HexagonRowColumn453.cols_left0)) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (leftScaleExponent 4 5 3) • (left1Middle4 5 3)) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal4_case_5_3_row_3_1_2 : (((-1 : ℤ) ^ (leftScaleBit 4 5 3).val * positiveScale (leftScaleExponent 4 5 3)) •
      (rowColumnMul HexagonRowColumn453.rows_assocBCA HexagonRowColumn453.cols_left0)) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (leftScaleExponent 4 5 3) • (left1Middle4 5 3)) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal4_case_5_3_row_3_1_3 : (((-1 : ℤ) ^ (leftScaleBit 4 5 3).val * positiveScale (leftScaleExponent 4 5 3)) •
      (rowColumnMul HexagonRowColumn453.rows_assocBCA HexagonRowColumn453.cols_left0)) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (leftScaleExponent 4 5 3) • (left1Middle4 5 3)) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem leftFinal4_case_5_3_checked : ((-1 : ℤ) ^ (leftScaleBit 4 5 3).val * positiveScale (leftScaleExponent 4 5 3)) •
      (rowColumnMul HexagonRowColumn453.rows_assocBCA HexagonRowColumn453.cols_left0) = negativeScale (leftScaleExponent 4 5 3) • (left1Middle4 5 3) := by
  funext r
  fin_cases r
  · exact leftFinal4_case_5_3_row_0_0_0
  · exact leftFinal4_case_5_3_row_0_0_1
  · exact leftFinal4_case_5_3_row_0_0_2
  · exact leftFinal4_case_5_3_row_0_0_3
  · exact leftFinal4_case_5_3_row_0_1_0
  · exact leftFinal4_case_5_3_row_0_1_1
  · exact leftFinal4_case_5_3_row_0_1_2
  · exact leftFinal4_case_5_3_row_0_1_3
  · exact leftFinal4_case_5_3_row_1_0_0
  · exact leftFinal4_case_5_3_row_1_0_1
  · exact leftFinal4_case_5_3_row_1_0_2
  · exact leftFinal4_case_5_3_row_1_0_3
  · exact leftFinal4_case_5_3_row_1_1_0
  · exact leftFinal4_case_5_3_row_1_1_1
  · exact leftFinal4_case_5_3_row_1_1_2
  · exact leftFinal4_case_5_3_row_1_1_3
  · exact leftFinal4_case_5_3_row_2_0_0
  · exact leftFinal4_case_5_3_row_2_0_1
  · exact leftFinal4_case_5_3_row_2_0_2
  · exact leftFinal4_case_5_3_row_2_0_3
  · exact leftFinal4_case_5_3_row_2_1_0
  · exact leftFinal4_case_5_3_row_2_1_1
  · exact leftFinal4_case_5_3_row_2_1_2
  · exact leftFinal4_case_5_3_row_2_1_3
  · exact leftFinal4_case_5_3_row_3_0_0
  · exact leftFinal4_case_5_3_row_3_0_1
  · exact leftFinal4_case_5_3_row_3_0_2
  · exact leftFinal4_case_5_3_row_3_0_3
  · exact leftFinal4_case_5_3_row_3_1_0
  · exact leftFinal4_case_5_3_row_3_1_1
  · exact leftFinal4_case_5_3_row_3_1_2
  · exact leftFinal4_case_5_3_row_3_1_3

set_option backward.isDefEq.respectTransparency false in
theorem leftFinal4_case_5_3 : ((-1 : ℤ) ^ (leftScaleBit 4 5 3).val * positiveScale (leftScaleExponent 4 5 3)) •
      (associatorZ 5 3 4 * left0Middle4 5 3) = negativeScale (leftScaleExponent 4 5 3) • (innerRightZ 5 4 3 * left1Middle4 5 3) := by
  simpa only [HexagonAtoms453.assocABC_eq,
    HexagonAtoms453.outerABC_eq,
    HexagonAtoms453.assocBAC_eq,
    HexagonAtoms453.innerABC_eq,
    HexagonAtoms453.innerRightABC_eq,
    HexagonAtoms453.inverseACB_eq,
    HexagonAtoms453.innerACB_eq,
    HexagonAtoms453.assocBCA_eq,
    HexagonAtoms453.innerRightBAC_eq,
    HexagonAtoms453.assocCAB_eq,
    HexagonAtoms453.outerLeftABC_eq,
    HexagonRowColumn453.product0_eq,
    HexagonRowColumn453.product1_eq,
    HexagonRowColumn453.product2_eq,
    HexagonRowColumn453.product3_eq,
    HexagonRowColumn453.product4_eq,
    HexagonRowColumn453.product5_eq,
    HexagonRowColumn453.product6_eq,
    HexagonRowColumn453.product7_eq] using leftFinal4_case_5_3_checked

private theorem rightFinal4_case_5_3_row_0_0_0 : (((-1 : ℤ) ^ (rightScaleBit 4 5 3).val * positiveScale (rightScaleExponent 4 5 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 3 5 : ℤ)) • HexagonAtoms453.outerLeftABC) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 4 5 3) • (rowColumnMul HexagonRowColumn453.rows_assocCAB HexagonRowColumn453.cols_right2)) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal4_case_5_3_row_0_0_1 : (((-1 : ℤ) ^ (rightScaleBit 4 5 3).val * positiveScale (rightScaleExponent 4 5 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 3 5 : ℤ)) • HexagonAtoms453.outerLeftABC) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 4 5 3) • (rowColumnMul HexagonRowColumn453.rows_assocCAB HexagonRowColumn453.cols_right2)) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal4_case_5_3_row_0_0_2 : (((-1 : ℤ) ^ (rightScaleBit 4 5 3).val * positiveScale (rightScaleExponent 4 5 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 3 5 : ℤ)) • HexagonAtoms453.outerLeftABC) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 4 5 3) • (rowColumnMul HexagonRowColumn453.rows_assocCAB HexagonRowColumn453.cols_right2)) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal4_case_5_3_row_0_0_3 : (((-1 : ℤ) ^ (rightScaleBit 4 5 3).val * positiveScale (rightScaleExponent 4 5 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 3 5 : ℤ)) • HexagonAtoms453.outerLeftABC) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 4 5 3) • (rowColumnMul HexagonRowColumn453.rows_assocCAB HexagonRowColumn453.cols_right2)) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal4_case_5_3_row_0_1_0 : (((-1 : ℤ) ^ (rightScaleBit 4 5 3).val * positiveScale (rightScaleExponent 4 5 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 3 5 : ℤ)) • HexagonAtoms453.outerLeftABC) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 4 5 3) • (rowColumnMul HexagonRowColumn453.rows_assocCAB HexagonRowColumn453.cols_right2)) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal4_case_5_3_row_0_1_1 : (((-1 : ℤ) ^ (rightScaleBit 4 5 3).val * positiveScale (rightScaleExponent 4 5 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 3 5 : ℤ)) • HexagonAtoms453.outerLeftABC) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 4 5 3) • (rowColumnMul HexagonRowColumn453.rows_assocCAB HexagonRowColumn453.cols_right2)) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal4_case_5_3_row_0_1_2 : (((-1 : ℤ) ^ (rightScaleBit 4 5 3).val * positiveScale (rightScaleExponent 4 5 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 3 5 : ℤ)) • HexagonAtoms453.outerLeftABC) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 4 5 3) • (rowColumnMul HexagonRowColumn453.rows_assocCAB HexagonRowColumn453.cols_right2)) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal4_case_5_3_row_0_1_3 : (((-1 : ℤ) ^ (rightScaleBit 4 5 3).val * positiveScale (rightScaleExponent 4 5 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 3 5 : ℤ)) • HexagonAtoms453.outerLeftABC) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 4 5 3) • (rowColumnMul HexagonRowColumn453.rows_assocCAB HexagonRowColumn453.cols_right2)) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal4_case_5_3_row_1_0_0 : (((-1 : ℤ) ^ (rightScaleBit 4 5 3).val * positiveScale (rightScaleExponent 4 5 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 3 5 : ℤ)) • HexagonAtoms453.outerLeftABC) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 4 5 3) • (rowColumnMul HexagonRowColumn453.rows_assocCAB HexagonRowColumn453.cols_right2)) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal4_case_5_3_row_1_0_1 : (((-1 : ℤ) ^ (rightScaleBit 4 5 3).val * positiveScale (rightScaleExponent 4 5 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 3 5 : ℤ)) • HexagonAtoms453.outerLeftABC) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 4 5 3) • (rowColumnMul HexagonRowColumn453.rows_assocCAB HexagonRowColumn453.cols_right2)) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal4_case_5_3_row_1_0_2 : (((-1 : ℤ) ^ (rightScaleBit 4 5 3).val * positiveScale (rightScaleExponent 4 5 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 3 5 : ℤ)) • HexagonAtoms453.outerLeftABC) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 4 5 3) • (rowColumnMul HexagonRowColumn453.rows_assocCAB HexagonRowColumn453.cols_right2)) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal4_case_5_3_row_1_0_3 : (((-1 : ℤ) ^ (rightScaleBit 4 5 3).val * positiveScale (rightScaleExponent 4 5 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 3 5 : ℤ)) • HexagonAtoms453.outerLeftABC) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 4 5 3) • (rowColumnMul HexagonRowColumn453.rows_assocCAB HexagonRowColumn453.cols_right2)) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal4_case_5_3_row_1_1_0 : (((-1 : ℤ) ^ (rightScaleBit 4 5 3).val * positiveScale (rightScaleExponent 4 5 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 3 5 : ℤ)) • HexagonAtoms453.outerLeftABC) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 4 5 3) • (rowColumnMul HexagonRowColumn453.rows_assocCAB HexagonRowColumn453.cols_right2)) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal4_case_5_3_row_1_1_1 : (((-1 : ℤ) ^ (rightScaleBit 4 5 3).val * positiveScale (rightScaleExponent 4 5 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 3 5 : ℤ)) • HexagonAtoms453.outerLeftABC) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 4 5 3) • (rowColumnMul HexagonRowColumn453.rows_assocCAB HexagonRowColumn453.cols_right2)) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal4_case_5_3_row_1_1_2 : (((-1 : ℤ) ^ (rightScaleBit 4 5 3).val * positiveScale (rightScaleExponent 4 5 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 3 5 : ℤ)) • HexagonAtoms453.outerLeftABC) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 4 5 3) • (rowColumnMul HexagonRowColumn453.rows_assocCAB HexagonRowColumn453.cols_right2)) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal4_case_5_3_row_1_1_3 : (((-1 : ℤ) ^ (rightScaleBit 4 5 3).val * positiveScale (rightScaleExponent 4 5 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 3 5 : ℤ)) • HexagonAtoms453.outerLeftABC) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 4 5 3) • (rowColumnMul HexagonRowColumn453.rows_assocCAB HexagonRowColumn453.cols_right2)) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal4_case_5_3_row_2_0_0 : (((-1 : ℤ) ^ (rightScaleBit 4 5 3).val * positiveScale (rightScaleExponent 4 5 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 3 5 : ℤ)) • HexagonAtoms453.outerLeftABC) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 4 5 3) • (rowColumnMul HexagonRowColumn453.rows_assocCAB HexagonRowColumn453.cols_right2)) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal4_case_5_3_row_2_0_1 : (((-1 : ℤ) ^ (rightScaleBit 4 5 3).val * positiveScale (rightScaleExponent 4 5 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 3 5 : ℤ)) • HexagonAtoms453.outerLeftABC) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 4 5 3) • (rowColumnMul HexagonRowColumn453.rows_assocCAB HexagonRowColumn453.cols_right2)) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal4_case_5_3_row_2_0_2 : (((-1 : ℤ) ^ (rightScaleBit 4 5 3).val * positiveScale (rightScaleExponent 4 5 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 3 5 : ℤ)) • HexagonAtoms453.outerLeftABC) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 4 5 3) • (rowColumnMul HexagonRowColumn453.rows_assocCAB HexagonRowColumn453.cols_right2)) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal4_case_5_3_row_2_0_3 : (((-1 : ℤ) ^ (rightScaleBit 4 5 3).val * positiveScale (rightScaleExponent 4 5 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 3 5 : ℤ)) • HexagonAtoms453.outerLeftABC) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 4 5 3) • (rowColumnMul HexagonRowColumn453.rows_assocCAB HexagonRowColumn453.cols_right2)) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal4_case_5_3_row_2_1_0 : (((-1 : ℤ) ^ (rightScaleBit 4 5 3).val * positiveScale (rightScaleExponent 4 5 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 3 5 : ℤ)) • HexagonAtoms453.outerLeftABC) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 4 5 3) • (rowColumnMul HexagonRowColumn453.rows_assocCAB HexagonRowColumn453.cols_right2)) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal4_case_5_3_row_2_1_1 : (((-1 : ℤ) ^ (rightScaleBit 4 5 3).val * positiveScale (rightScaleExponent 4 5 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 3 5 : ℤ)) • HexagonAtoms453.outerLeftABC) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 4 5 3) • (rowColumnMul HexagonRowColumn453.rows_assocCAB HexagonRowColumn453.cols_right2)) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal4_case_5_3_row_2_1_2 : (((-1 : ℤ) ^ (rightScaleBit 4 5 3).val * positiveScale (rightScaleExponent 4 5 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 3 5 : ℤ)) • HexagonAtoms453.outerLeftABC) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 4 5 3) • (rowColumnMul HexagonRowColumn453.rows_assocCAB HexagonRowColumn453.cols_right2)) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal4_case_5_3_row_2_1_3 : (((-1 : ℤ) ^ (rightScaleBit 4 5 3).val * positiveScale (rightScaleExponent 4 5 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 3 5 : ℤ)) • HexagonAtoms453.outerLeftABC) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 4 5 3) • (rowColumnMul HexagonRowColumn453.rows_assocCAB HexagonRowColumn453.cols_right2)) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal4_case_5_3_row_3_0_0 : (((-1 : ℤ) ^ (rightScaleBit 4 5 3).val * positiveScale (rightScaleExponent 4 5 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 3 5 : ℤ)) • HexagonAtoms453.outerLeftABC) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 4 5 3) • (rowColumnMul HexagonRowColumn453.rows_assocCAB HexagonRowColumn453.cols_right2)) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal4_case_5_3_row_3_0_1 : (((-1 : ℤ) ^ (rightScaleBit 4 5 3).val * positiveScale (rightScaleExponent 4 5 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 3 5 : ℤ)) • HexagonAtoms453.outerLeftABC) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 4 5 3) • (rowColumnMul HexagonRowColumn453.rows_assocCAB HexagonRowColumn453.cols_right2)) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal4_case_5_3_row_3_0_2 : (((-1 : ℤ) ^ (rightScaleBit 4 5 3).val * positiveScale (rightScaleExponent 4 5 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 3 5 : ℤ)) • HexagonAtoms453.outerLeftABC) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 4 5 3) • (rowColumnMul HexagonRowColumn453.rows_assocCAB HexagonRowColumn453.cols_right2)) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal4_case_5_3_row_3_0_3 : (((-1 : ℤ) ^ (rightScaleBit 4 5 3).val * positiveScale (rightScaleExponent 4 5 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 3 5 : ℤ)) • HexagonAtoms453.outerLeftABC) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 4 5 3) • (rowColumnMul HexagonRowColumn453.rows_assocCAB HexagonRowColumn453.cols_right2)) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal4_case_5_3_row_3_1_0 : (((-1 : ℤ) ^ (rightScaleBit 4 5 3).val * positiveScale (rightScaleExponent 4 5 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 3 5 : ℤ)) • HexagonAtoms453.outerLeftABC) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = (negativeScale (rightScaleExponent 4 5 3) • (rowColumnMul HexagonRowColumn453.rows_assocCAB HexagonRowColumn453.cols_right2)) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal4_case_5_3_row_3_1_1 : (((-1 : ℤ) ^ (rightScaleBit 4 5 3).val * positiveScale (rightScaleExponent 4 5 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 3 5 : ℤ)) • HexagonAtoms453.outerLeftABC) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = (negativeScale (rightScaleExponent 4 5 3) • (rowColumnMul HexagonRowColumn453.rows_assocCAB HexagonRowColumn453.cols_right2)) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal4_case_5_3_row_3_1_2 : (((-1 : ℤ) ^ (rightScaleBit 4 5 3).val * positiveScale (rightScaleExponent 4 5 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 3 5 : ℤ)) • HexagonAtoms453.outerLeftABC) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = (negativeScale (rightScaleExponent 4 5 3) • (rowColumnMul HexagonRowColumn453.rows_assocCAB HexagonRowColumn453.cols_right2)) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal4_case_5_3_row_3_1_3 : (((-1 : ℤ) ^ (rightScaleBit 4 5 3).val * positiveScale (rightScaleExponent 4 5 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 3 5 : ℤ)) • HexagonAtoms453.outerLeftABC) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = (negativeScale (rightScaleExponent 4 5 3) • (rowColumnMul HexagonRowColumn453.rows_assocCAB HexagonRowColumn453.cols_right2)) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound (a := 4) (b := 2) (c := 4)
  decide +kernel

private theorem rightFinal4_case_5_3_checked : ((-1 : ℤ) ^ (rightScaleBit 4 5 3).val * positiveScale (rightScaleExponent 4 5 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 3 5 : ℤ)) • HexagonAtoms453.outerLeftABC = negativeScale (rightScaleExponent 4 5 3) • (rowColumnMul HexagonRowColumn453.rows_assocCAB HexagonRowColumn453.cols_right2) := by
  funext r
  fin_cases r
  · exact rightFinal4_case_5_3_row_0_0_0
  · exact rightFinal4_case_5_3_row_0_0_1
  · exact rightFinal4_case_5_3_row_0_0_2
  · exact rightFinal4_case_5_3_row_0_0_3
  · exact rightFinal4_case_5_3_row_0_1_0
  · exact rightFinal4_case_5_3_row_0_1_1
  · exact rightFinal4_case_5_3_row_0_1_2
  · exact rightFinal4_case_5_3_row_0_1_3
  · exact rightFinal4_case_5_3_row_1_0_0
  · exact rightFinal4_case_5_3_row_1_0_1
  · exact rightFinal4_case_5_3_row_1_0_2
  · exact rightFinal4_case_5_3_row_1_0_3
  · exact rightFinal4_case_5_3_row_1_1_0
  · exact rightFinal4_case_5_3_row_1_1_1
  · exact rightFinal4_case_5_3_row_1_1_2
  · exact rightFinal4_case_5_3_row_1_1_3
  · exact rightFinal4_case_5_3_row_2_0_0
  · exact rightFinal4_case_5_3_row_2_0_1
  · exact rightFinal4_case_5_3_row_2_0_2
  · exact rightFinal4_case_5_3_row_2_0_3
  · exact rightFinal4_case_5_3_row_2_1_0
  · exact rightFinal4_case_5_3_row_2_1_1
  · exact rightFinal4_case_5_3_row_2_1_2
  · exact rightFinal4_case_5_3_row_2_1_3
  · exact rightFinal4_case_5_3_row_3_0_0
  · exact rightFinal4_case_5_3_row_3_0_1
  · exact rightFinal4_case_5_3_row_3_0_2
  · exact rightFinal4_case_5_3_row_3_0_3
  · exact rightFinal4_case_5_3_row_3_1_0
  · exact rightFinal4_case_5_3_row_3_1_1
  · exact rightFinal4_case_5_3_row_3_1_2
  · exact rightFinal4_case_5_3_row_3_1_3

set_option backward.isDefEq.respectTransparency false in
theorem rightFinal4_case_5_3 : ((-1 : ℤ) ^ (rightScaleBit 4 5 3).val * positiveScale (rightScaleExponent 4 5 3) *
      (RMod.ConstructiveConnectorTable.inverseScale 4 3 5 : ℤ)) • outerLeftZ 4 5 3 = negativeScale (rightScaleExponent 4 5 3) • (associatorZ 3 4 5 * right2Middle4 5 3) := by
  simpa only [HexagonAtoms453.assocABC_eq,
    HexagonAtoms453.outerABC_eq,
    HexagonAtoms453.assocBAC_eq,
    HexagonAtoms453.innerABC_eq,
    HexagonAtoms453.innerRightABC_eq,
    HexagonAtoms453.inverseACB_eq,
    HexagonAtoms453.innerACB_eq,
    HexagonAtoms453.assocBCA_eq,
    HexagonAtoms453.innerRightBAC_eq,
    HexagonAtoms453.assocCAB_eq,
    HexagonAtoms453.outerLeftABC_eq,
    HexagonRowColumn453.product0_eq,
    HexagonRowColumn453.product1_eq,
    HexagonRowColumn453.product2_eq,
    HexagonRowColumn453.product3_eq,
    HexagonRowColumn453.product4_eq,
    HexagonRowColumn453.product5_eq,
    HexagonRowColumn453.product6_eq,
    HexagonRowColumn453.product7_eq] using rightFinal4_case_5_3_checked

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonCases4
