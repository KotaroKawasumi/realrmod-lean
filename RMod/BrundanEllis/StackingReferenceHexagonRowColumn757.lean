import RMod.BrundanEllis.StackingReferenceHexagonAtoms757
import RMod.BrundanEllis.StackingReferenceHexagonMiddle7
import RMod.BrundanEllis.StackingReferenceRowColumnCheck

/-! Verified row and column lists. Each subsequent scalar product traverses
these lists directly, without repeated lookup into the original matrices. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn757
open Superfusion

theorem assocBCA_alias : HexagonAtoms757.assocBCA = HexagonAtoms757.assocBAC :=
  HexagonAtoms757.assocBCA_eq.symm.trans HexagonAtoms757.assocBAC_eq

private def rows_inverseACBData : List (List ℤ) := [decodeIntegerRow 16 3 1 19931224,
    decodeIntegerRow 16 3 1 20991190,
    decodeIntegerRow 16 3 1 35872510,
    decodeIntegerRow 16 3 1 26306248,
    decodeIntegerRow 16 3 1 21543016,
    decodeIntegerRow 16 3 1 21529930,
    decodeIntegerRow 16 3 1 21346210,
    decodeIntegerRow 16 3 1 21464312,
    decodeIntegerRow 16 3 1 7174696,
    decodeIntegerRow 16 3 1 26306410,
    decodeIntegerRow 16 3 1 19926850,
    decodeIntegerRow 16 3 1 22054072,
    decodeIntegerRow 16 3 1 21700504,
    decodeIntegerRow 16 3 1 21464310,
    decodeIntegerRow 16 3 1 21543070,
    decodeIntegerRow 16 3 1 21516808]

def rows_inverseACB (r : LeftIndex 7 7 5) : List ℤ := rows_inverseACBData.getD (leftPosition 7 7 5 r) []

private theorem rows_inverseACB_eq_0_0_0 : (tripleIndices 2 1 8).map ((HexagonAtoms757.inverseACB) ((0 : Fin 1), (0 : Fin 2), (0 : Fin 8))) = rows_inverseACB ((0 : Fin 1), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_1 : (tripleIndices 2 1 8).map ((HexagonAtoms757.inverseACB) ((0 : Fin 1), (0 : Fin 2), (1 : Fin 8))) = rows_inverseACB ((0 : Fin 1), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_2 : (tripleIndices 2 1 8).map ((HexagonAtoms757.inverseACB) ((0 : Fin 1), (0 : Fin 2), (2 : Fin 8))) = rows_inverseACB ((0 : Fin 1), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_3 : (tripleIndices 2 1 8).map ((HexagonAtoms757.inverseACB) ((0 : Fin 1), (0 : Fin 2), (3 : Fin 8))) = rows_inverseACB ((0 : Fin 1), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_4 : (tripleIndices 2 1 8).map ((HexagonAtoms757.inverseACB) ((0 : Fin 1), (0 : Fin 2), (4 : Fin 8))) = rows_inverseACB ((0 : Fin 1), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_5 : (tripleIndices 2 1 8).map ((HexagonAtoms757.inverseACB) ((0 : Fin 1), (0 : Fin 2), (5 : Fin 8))) = rows_inverseACB ((0 : Fin 1), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_6 : (tripleIndices 2 1 8).map ((HexagonAtoms757.inverseACB) ((0 : Fin 1), (0 : Fin 2), (6 : Fin 8))) = rows_inverseACB ((0 : Fin 1), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_7 : (tripleIndices 2 1 8).map ((HexagonAtoms757.inverseACB) ((0 : Fin 1), (0 : Fin 2), (7 : Fin 8))) = rows_inverseACB ((0 : Fin 1), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_0 : (tripleIndices 2 1 8).map ((HexagonAtoms757.inverseACB) ((0 : Fin 1), (1 : Fin 2), (0 : Fin 8))) = rows_inverseACB ((0 : Fin 1), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_1 : (tripleIndices 2 1 8).map ((HexagonAtoms757.inverseACB) ((0 : Fin 1), (1 : Fin 2), (1 : Fin 8))) = rows_inverseACB ((0 : Fin 1), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_2 : (tripleIndices 2 1 8).map ((HexagonAtoms757.inverseACB) ((0 : Fin 1), (1 : Fin 2), (2 : Fin 8))) = rows_inverseACB ((0 : Fin 1), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_3 : (tripleIndices 2 1 8).map ((HexagonAtoms757.inverseACB) ((0 : Fin 1), (1 : Fin 2), (3 : Fin 8))) = rows_inverseACB ((0 : Fin 1), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_4 : (tripleIndices 2 1 8).map ((HexagonAtoms757.inverseACB) ((0 : Fin 1), (1 : Fin 2), (4 : Fin 8))) = rows_inverseACB ((0 : Fin 1), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_5 : (tripleIndices 2 1 8).map ((HexagonAtoms757.inverseACB) ((0 : Fin 1), (1 : Fin 2), (5 : Fin 8))) = rows_inverseACB ((0 : Fin 1), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_6 : (tripleIndices 2 1 8).map ((HexagonAtoms757.inverseACB) ((0 : Fin 1), (1 : Fin 2), (6 : Fin 8))) = rows_inverseACB ((0 : Fin 1), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_7 : (tripleIndices 2 1 8).map ((HexagonAtoms757.inverseACB) ((0 : Fin 1), (1 : Fin 2), (7 : Fin 8))) = rows_inverseACB ((0 : Fin 1), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_inverseACB_data (r : LeftIndex 7 7 5) : (tripleIndices 2 1 8).map ((HexagonAtoms757.inverseACB) r) = rows_inverseACB r := by
  fin_cases r
  · exact rows_inverseACB_eq_0_0_0
  · exact rows_inverseACB_eq_0_0_1
  · exact rows_inverseACB_eq_0_0_2
  · exact rows_inverseACB_eq_0_0_3
  · exact rows_inverseACB_eq_0_0_4
  · exact rows_inverseACB_eq_0_0_5
  · exact rows_inverseACB_eq_0_0_6
  · exact rows_inverseACB_eq_0_0_7
  · exact rows_inverseACB_eq_0_1_0
  · exact rows_inverseACB_eq_0_1_1
  · exact rows_inverseACB_eq_0_1_2
  · exact rows_inverseACB_eq_0_1_3
  · exact rows_inverseACB_eq_0_1_4
  · exact rows_inverseACB_eq_0_1_5
  · exact rows_inverseACB_eq_0_1_6
  · exact rows_inverseACB_eq_0_1_7

private def rows_innerACBData : List (List ℤ) := [decodeIntegerRow 16 3 1 23115496,
    decodeIntegerRow 16 3 1 22055530,
    decodeIntegerRow 16 3 1 7174210,
    decodeIntegerRow 16 3 1 16740472,
    decodeIntegerRow 16 3 1 21503704,
    decodeIntegerRow 16 3 1 21516790,
    decodeIntegerRow 16 3 1 21700510,
    decodeIntegerRow 16 3 1 21582408,
    decodeIntegerRow 16 3 1 35872024,
    decodeIntegerRow 16 3 1 16740310,
    decodeIntegerRow 16 3 1 23119870,
    decodeIntegerRow 16 3 1 20992648,
    decodeIntegerRow 16 3 1 21346216,
    decodeIntegerRow 16 3 1 21582410,
    decodeIntegerRow 16 3 1 21503650,
    decodeIntegerRow 16 3 1 21529912]

def rows_innerACB (r : LeftIndex 7 7 5) : List ℤ := rows_innerACBData.getD (leftPosition 7 7 5 r) []

private theorem rows_innerACB_eq_0_0_0 : (tripleIndices 1 2 8).map ((HexagonAtoms757.innerACB) ((0 : Fin 1), (0 : Fin 2), (0 : Fin 8))) = rows_innerACB ((0 : Fin 1), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_0_1 : (tripleIndices 1 2 8).map ((HexagonAtoms757.innerACB) ((0 : Fin 1), (0 : Fin 2), (1 : Fin 8))) = rows_innerACB ((0 : Fin 1), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_0_2 : (tripleIndices 1 2 8).map ((HexagonAtoms757.innerACB) ((0 : Fin 1), (0 : Fin 2), (2 : Fin 8))) = rows_innerACB ((0 : Fin 1), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_0_3 : (tripleIndices 1 2 8).map ((HexagonAtoms757.innerACB) ((0 : Fin 1), (0 : Fin 2), (3 : Fin 8))) = rows_innerACB ((0 : Fin 1), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_0_4 : (tripleIndices 1 2 8).map ((HexagonAtoms757.innerACB) ((0 : Fin 1), (0 : Fin 2), (4 : Fin 8))) = rows_innerACB ((0 : Fin 1), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_0_5 : (tripleIndices 1 2 8).map ((HexagonAtoms757.innerACB) ((0 : Fin 1), (0 : Fin 2), (5 : Fin 8))) = rows_innerACB ((0 : Fin 1), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_0_6 : (tripleIndices 1 2 8).map ((HexagonAtoms757.innerACB) ((0 : Fin 1), (0 : Fin 2), (6 : Fin 8))) = rows_innerACB ((0 : Fin 1), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_0_7 : (tripleIndices 1 2 8).map ((HexagonAtoms757.innerACB) ((0 : Fin 1), (0 : Fin 2), (7 : Fin 8))) = rows_innerACB ((0 : Fin 1), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_1_0 : (tripleIndices 1 2 8).map ((HexagonAtoms757.innerACB) ((0 : Fin 1), (1 : Fin 2), (0 : Fin 8))) = rows_innerACB ((0 : Fin 1), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_1_1 : (tripleIndices 1 2 8).map ((HexagonAtoms757.innerACB) ((0 : Fin 1), (1 : Fin 2), (1 : Fin 8))) = rows_innerACB ((0 : Fin 1), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_1_2 : (tripleIndices 1 2 8).map ((HexagonAtoms757.innerACB) ((0 : Fin 1), (1 : Fin 2), (2 : Fin 8))) = rows_innerACB ((0 : Fin 1), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_1_3 : (tripleIndices 1 2 8).map ((HexagonAtoms757.innerACB) ((0 : Fin 1), (1 : Fin 2), (3 : Fin 8))) = rows_innerACB ((0 : Fin 1), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_1_4 : (tripleIndices 1 2 8).map ((HexagonAtoms757.innerACB) ((0 : Fin 1), (1 : Fin 2), (4 : Fin 8))) = rows_innerACB ((0 : Fin 1), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_1_5 : (tripleIndices 1 2 8).map ((HexagonAtoms757.innerACB) ((0 : Fin 1), (1 : Fin 2), (5 : Fin 8))) = rows_innerACB ((0 : Fin 1), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_1_6 : (tripleIndices 1 2 8).map ((HexagonAtoms757.innerACB) ((0 : Fin 1), (1 : Fin 2), (6 : Fin 8))) = rows_innerACB ((0 : Fin 1), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_1_7 : (tripleIndices 1 2 8).map ((HexagonAtoms757.innerACB) ((0 : Fin 1), (1 : Fin 2), (7 : Fin 8))) = rows_innerACB ((0 : Fin 1), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_innerACB_data (r : LeftIndex 7 7 5) : (tripleIndices 1 2 8).map ((HexagonAtoms757.innerACB) r) = rows_innerACB r := by
  fin_cases r
  · exact rows_innerACB_eq_0_0_0
  · exact rows_innerACB_eq_0_0_1
  · exact rows_innerACB_eq_0_0_2
  · exact rows_innerACB_eq_0_0_3
  · exact rows_innerACB_eq_0_0_4
  · exact rows_innerACB_eq_0_0_5
  · exact rows_innerACB_eq_0_0_6
  · exact rows_innerACB_eq_0_0_7
  · exact rows_innerACB_eq_0_1_0
  · exact rows_innerACB_eq_0_1_1
  · exact rows_innerACB_eq_0_1_2
  · exact rows_innerACB_eq_0_1_3
  · exact rows_innerACB_eq_0_1_4
  · exact rows_innerACB_eq_0_1_5
  · exact rows_innerACB_eq_0_1_6
  · exact rows_innerACB_eq_0_1_7

private def rows_assocBACData : List (List ℤ) := [decodeIntegerRow 16 3 1 21523361,
    decodeIntegerRow 16 3 1 21523363,
    decodeIntegerRow 16 3 1 21523369,
    decodeIntegerRow 16 3 1 21523387,
    decodeIntegerRow 16 3 1 21523441,
    decodeIntegerRow 16 3 1 21523603,
    decodeIntegerRow 16 3 1 21524089,
    decodeIntegerRow 16 3 1 21525547,
    decodeIntegerRow 16 3 1 21529921,
    decodeIntegerRow 16 3 1 21543043,
    decodeIntegerRow 16 3 1 21582409,
    decodeIntegerRow 16 3 1 21700507,
    decodeIntegerRow 16 3 1 22054801,
    decodeIntegerRow 16 3 1 23117683,
    decodeIntegerRow 16 3 1 26306329,
    decodeIntegerRow 16 3 1 35872267]

def rows_assocBAC (r : RightIndex 5 7 7) : List ℤ := rows_assocBACData.getD (rightPosition 5 7 7 r) []

private theorem rows_assocBAC_eq_0_0_0 : (tripleIndices 2 1 8).map ((HexagonAtoms757.assocBAC) ((0 : Fin 1), (0 : Fin 2), (0 : Fin 8))) = rows_assocBAC ((0 : Fin 1), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_1 : (tripleIndices 2 1 8).map ((HexagonAtoms757.assocBAC) ((0 : Fin 1), (0 : Fin 2), (1 : Fin 8))) = rows_assocBAC ((0 : Fin 1), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_2 : (tripleIndices 2 1 8).map ((HexagonAtoms757.assocBAC) ((0 : Fin 1), (0 : Fin 2), (2 : Fin 8))) = rows_assocBAC ((0 : Fin 1), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_3 : (tripleIndices 2 1 8).map ((HexagonAtoms757.assocBAC) ((0 : Fin 1), (0 : Fin 2), (3 : Fin 8))) = rows_assocBAC ((0 : Fin 1), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_4 : (tripleIndices 2 1 8).map ((HexagonAtoms757.assocBAC) ((0 : Fin 1), (0 : Fin 2), (4 : Fin 8))) = rows_assocBAC ((0 : Fin 1), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_5 : (tripleIndices 2 1 8).map ((HexagonAtoms757.assocBAC) ((0 : Fin 1), (0 : Fin 2), (5 : Fin 8))) = rows_assocBAC ((0 : Fin 1), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_6 : (tripleIndices 2 1 8).map ((HexagonAtoms757.assocBAC) ((0 : Fin 1), (0 : Fin 2), (6 : Fin 8))) = rows_assocBAC ((0 : Fin 1), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_7 : (tripleIndices 2 1 8).map ((HexagonAtoms757.assocBAC) ((0 : Fin 1), (0 : Fin 2), (7 : Fin 8))) = rows_assocBAC ((0 : Fin 1), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_1_0 : (tripleIndices 2 1 8).map ((HexagonAtoms757.assocBAC) ((0 : Fin 1), (1 : Fin 2), (0 : Fin 8))) = rows_assocBAC ((0 : Fin 1), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_1_1 : (tripleIndices 2 1 8).map ((HexagonAtoms757.assocBAC) ((0 : Fin 1), (1 : Fin 2), (1 : Fin 8))) = rows_assocBAC ((0 : Fin 1), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_1_2 : (tripleIndices 2 1 8).map ((HexagonAtoms757.assocBAC) ((0 : Fin 1), (1 : Fin 2), (2 : Fin 8))) = rows_assocBAC ((0 : Fin 1), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_1_3 : (tripleIndices 2 1 8).map ((HexagonAtoms757.assocBAC) ((0 : Fin 1), (1 : Fin 2), (3 : Fin 8))) = rows_assocBAC ((0 : Fin 1), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_1_4 : (tripleIndices 2 1 8).map ((HexagonAtoms757.assocBAC) ((0 : Fin 1), (1 : Fin 2), (4 : Fin 8))) = rows_assocBAC ((0 : Fin 1), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_1_5 : (tripleIndices 2 1 8).map ((HexagonAtoms757.assocBAC) ((0 : Fin 1), (1 : Fin 2), (5 : Fin 8))) = rows_assocBAC ((0 : Fin 1), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_1_6 : (tripleIndices 2 1 8).map ((HexagonAtoms757.assocBAC) ((0 : Fin 1), (1 : Fin 2), (6 : Fin 8))) = rows_assocBAC ((0 : Fin 1), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_1_7 : (tripleIndices 2 1 8).map ((HexagonAtoms757.assocBAC) ((0 : Fin 1), (1 : Fin 2), (7 : Fin 8))) = rows_assocBAC ((0 : Fin 1), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocBAC_data (r : RightIndex 5 7 7) : (tripleIndices 2 1 8).map ((HexagonAtoms757.assocBAC) r) = rows_assocBAC r := by
  fin_cases r
  · exact rows_assocBAC_eq_0_0_0
  · exact rows_assocBAC_eq_0_0_1
  · exact rows_assocBAC_eq_0_0_2
  · exact rows_assocBAC_eq_0_0_3
  · exact rows_assocBAC_eq_0_0_4
  · exact rows_assocBAC_eq_0_0_5
  · exact rows_assocBAC_eq_0_0_6
  · exact rows_assocBAC_eq_0_0_7
  · exact rows_assocBAC_eq_0_1_0
  · exact rows_assocBAC_eq_0_1_1
  · exact rows_assocBAC_eq_0_1_2
  · exact rows_assocBAC_eq_0_1_3
  · exact rows_assocBAC_eq_0_1_4
  · exact rows_assocBAC_eq_0_1_5
  · exact rows_assocBAC_eq_0_1_6
  · exact rows_assocBAC_eq_0_1_7

private def rows_innerRightBACData : List (List ℤ) := [decodeIntegerRow 16 3 1 23115496,
    decodeIntegerRow 16 3 1 22055530,
    decodeIntegerRow 16 3 1 7174210,
    decodeIntegerRow 16 3 1 16740472,
    decodeIntegerRow 16 3 1 21503704,
    decodeIntegerRow 16 3 1 21516790,
    decodeIntegerRow 16 3 1 21700510,
    decodeIntegerRow 16 3 1 21582408,
    decodeIntegerRow 16 3 1 35872024,
    decodeIntegerRow 16 3 1 16740310,
    decodeIntegerRow 16 3 1 23119870,
    decodeIntegerRow 16 3 1 20992648,
    decodeIntegerRow 16 3 1 21346216,
    decodeIntegerRow 16 3 1 21582410,
    decodeIntegerRow 16 3 1 21503650,
    decodeIntegerRow 16 3 1 21529912]

def rows_innerRightBAC (r : RightIndex 5 7 7) : List ℤ := rows_innerRightBACData.getD (rightPosition 5 7 7 r) []

private theorem rows_innerRightBAC_eq_0_0_0 : (tripleIndices 1 2 8).map ((HexagonAtoms757.innerRightBAC) ((0 : Fin 1), (0 : Fin 2), (0 : Fin 8))) = rows_innerRightBAC ((0 : Fin 1), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_0_1 : (tripleIndices 1 2 8).map ((HexagonAtoms757.innerRightBAC) ((0 : Fin 1), (0 : Fin 2), (1 : Fin 8))) = rows_innerRightBAC ((0 : Fin 1), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_0_2 : (tripleIndices 1 2 8).map ((HexagonAtoms757.innerRightBAC) ((0 : Fin 1), (0 : Fin 2), (2 : Fin 8))) = rows_innerRightBAC ((0 : Fin 1), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_0_3 : (tripleIndices 1 2 8).map ((HexagonAtoms757.innerRightBAC) ((0 : Fin 1), (0 : Fin 2), (3 : Fin 8))) = rows_innerRightBAC ((0 : Fin 1), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_0_4 : (tripleIndices 1 2 8).map ((HexagonAtoms757.innerRightBAC) ((0 : Fin 1), (0 : Fin 2), (4 : Fin 8))) = rows_innerRightBAC ((0 : Fin 1), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_0_5 : (tripleIndices 1 2 8).map ((HexagonAtoms757.innerRightBAC) ((0 : Fin 1), (0 : Fin 2), (5 : Fin 8))) = rows_innerRightBAC ((0 : Fin 1), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_0_6 : (tripleIndices 1 2 8).map ((HexagonAtoms757.innerRightBAC) ((0 : Fin 1), (0 : Fin 2), (6 : Fin 8))) = rows_innerRightBAC ((0 : Fin 1), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_0_7 : (tripleIndices 1 2 8).map ((HexagonAtoms757.innerRightBAC) ((0 : Fin 1), (0 : Fin 2), (7 : Fin 8))) = rows_innerRightBAC ((0 : Fin 1), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_1_0 : (tripleIndices 1 2 8).map ((HexagonAtoms757.innerRightBAC) ((0 : Fin 1), (1 : Fin 2), (0 : Fin 8))) = rows_innerRightBAC ((0 : Fin 1), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_1_1 : (tripleIndices 1 2 8).map ((HexagonAtoms757.innerRightBAC) ((0 : Fin 1), (1 : Fin 2), (1 : Fin 8))) = rows_innerRightBAC ((0 : Fin 1), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_1_2 : (tripleIndices 1 2 8).map ((HexagonAtoms757.innerRightBAC) ((0 : Fin 1), (1 : Fin 2), (2 : Fin 8))) = rows_innerRightBAC ((0 : Fin 1), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_1_3 : (tripleIndices 1 2 8).map ((HexagonAtoms757.innerRightBAC) ((0 : Fin 1), (1 : Fin 2), (3 : Fin 8))) = rows_innerRightBAC ((0 : Fin 1), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_1_4 : (tripleIndices 1 2 8).map ((HexagonAtoms757.innerRightBAC) ((0 : Fin 1), (1 : Fin 2), (4 : Fin 8))) = rows_innerRightBAC ((0 : Fin 1), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_1_5 : (tripleIndices 1 2 8).map ((HexagonAtoms757.innerRightBAC) ((0 : Fin 1), (1 : Fin 2), (5 : Fin 8))) = rows_innerRightBAC ((0 : Fin 1), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_1_6 : (tripleIndices 1 2 8).map ((HexagonAtoms757.innerRightBAC) ((0 : Fin 1), (1 : Fin 2), (6 : Fin 8))) = rows_innerRightBAC ((0 : Fin 1), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_1_7 : (tripleIndices 1 2 8).map ((HexagonAtoms757.innerRightBAC) ((0 : Fin 1), (1 : Fin 2), (7 : Fin 8))) = rows_innerRightBAC ((0 : Fin 1), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_innerRightBAC_data (r : RightIndex 5 7 7) : (tripleIndices 1 2 8).map ((HexagonAtoms757.innerRightBAC) r) = rows_innerRightBAC r := by
  fin_cases r
  · exact rows_innerRightBAC_eq_0_0_0
  · exact rows_innerRightBAC_eq_0_0_1
  · exact rows_innerRightBAC_eq_0_0_2
  · exact rows_innerRightBAC_eq_0_0_3
  · exact rows_innerRightBAC_eq_0_0_4
  · exact rows_innerRightBAC_eq_0_0_5
  · exact rows_innerRightBAC_eq_0_0_6
  · exact rows_innerRightBAC_eq_0_0_7
  · exact rows_innerRightBAC_eq_0_1_0
  · exact rows_innerRightBAC_eq_0_1_1
  · exact rows_innerRightBAC_eq_0_1_2
  · exact rows_innerRightBAC_eq_0_1_3
  · exact rows_innerRightBAC_eq_0_1_4
  · exact rows_innerRightBAC_eq_0_1_5
  · exact rows_innerRightBAC_eq_0_1_6
  · exact rows_innerRightBAC_eq_0_1_7

private def rows_assocCABData : List (List ℤ) := [decodeIntegerRow 16 3 1 19931224,
    decodeIntegerRow 16 3 1 20991190,
    decodeIntegerRow 16 3 1 35872510,
    decodeIntegerRow 16 3 1 26306248,
    decodeIntegerRow 16 3 1 21543016,
    decodeIntegerRow 16 3 1 21529930,
    decodeIntegerRow 16 3 1 21346210,
    decodeIntegerRow 16 3 1 21464312,
    decodeIntegerRow 16 3 1 7174696,
    decodeIntegerRow 16 3 1 26306410,
    decodeIntegerRow 16 3 1 19926850,
    decodeIntegerRow 16 3 1 22054072,
    decodeIntegerRow 16 3 1 21700504,
    decodeIntegerRow 16 3 1 21464310,
    decodeIntegerRow 16 3 1 21543070,
    decodeIntegerRow 16 3 1 21516808]

def rows_assocCAB (r : RightIndex 7 7 5) : List ℤ := rows_assocCABData.getD (rightPosition 7 7 5 r) []

private theorem rows_assocCAB_eq_0_0_0 : (tripleIndices 1 2 8).map ((HexagonAtoms757.assocCAB) ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_1 : (tripleIndices 1 2 8).map ((HexagonAtoms757.assocCAB) ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_2 : (tripleIndices 1 2 8).map ((HexagonAtoms757.assocCAB) ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_3 : (tripleIndices 1 2 8).map ((HexagonAtoms757.assocCAB) ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_4 : (tripleIndices 1 2 8).map ((HexagonAtoms757.assocCAB) ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_5 : (tripleIndices 1 2 8).map ((HexagonAtoms757.assocCAB) ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_6 : (tripleIndices 1 2 8).map ((HexagonAtoms757.assocCAB) ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_7 : (tripleIndices 1 2 8).map ((HexagonAtoms757.assocCAB) ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_0 : (tripleIndices 1 2 8).map ((HexagonAtoms757.assocCAB) ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_1 : (tripleIndices 1 2 8).map ((HexagonAtoms757.assocCAB) ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_2 : (tripleIndices 1 2 8).map ((HexagonAtoms757.assocCAB) ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_3 : (tripleIndices 1 2 8).map ((HexagonAtoms757.assocCAB) ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_4 : (tripleIndices 1 2 8).map ((HexagonAtoms757.assocCAB) ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_5 : (tripleIndices 1 2 8).map ((HexagonAtoms757.assocCAB) ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_6 : (tripleIndices 1 2 8).map ((HexagonAtoms757.assocCAB) ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_7 : (tripleIndices 1 2 8).map ((HexagonAtoms757.assocCAB) ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocCAB_data (r : RightIndex 7 7 5) : (tripleIndices 1 2 8).map ((HexagonAtoms757.assocCAB) r) = rows_assocCAB r := by
  fin_cases r
  · exact rows_assocCAB_eq_0_0_0
  · exact rows_assocCAB_eq_0_0_1
  · exact rows_assocCAB_eq_0_0_2
  · exact rows_assocCAB_eq_0_0_3
  · exact rows_assocCAB_eq_0_0_4
  · exact rows_assocCAB_eq_0_0_5
  · exact rows_assocCAB_eq_0_0_6
  · exact rows_assocCAB_eq_0_0_7
  · exact rows_assocCAB_eq_1_0_0
  · exact rows_assocCAB_eq_1_0_1
  · exact rows_assocCAB_eq_1_0_2
  · exact rows_assocCAB_eq_1_0_3
  · exact rows_assocCAB_eq_1_0_4
  · exact rows_assocCAB_eq_1_0_5
  · exact rows_assocCAB_eq_1_0_6
  · exact rows_assocCAB_eq_1_0_7

private def cols_right0Data : List (List ℤ) := [decodeIntegerRow 16 3 1 19931224,
    decodeIntegerRow 16 3 1 20991190,
    decodeIntegerRow 16 3 1 35872510,
    decodeIntegerRow 16 3 1 26306248,
    decodeIntegerRow 16 3 1 21543016,
    decodeIntegerRow 16 3 1 21529930,
    decodeIntegerRow 16 3 1 21346210,
    decodeIntegerRow 16 3 1 21464312,
    decodeIntegerRow 16 3 1 7174696,
    decodeIntegerRow 16 3 1 26306410,
    decodeIntegerRow 16 3 1 19926850,
    decodeIntegerRow 16 3 1 22054072,
    decodeIntegerRow 16 3 1 21700504,
    decodeIntegerRow 16 3 1 21464310,
    decodeIntegerRow 16 3 1 21543070,
    decodeIntegerRow 16 3 1 21516808]

def cols_right0 (r : LeftIndex 7 5 7) : List ℤ := cols_right0Data.getD (leftPosition 7 5 7 r) []

private theorem cols_right0_eq_0_0_0 : (tripleIndices 2 1 8).map (fun j => (right0Middle7 5 7) j ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8))) = cols_right0 ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_1 : (tripleIndices 2 1 8).map (fun j => (right0Middle7 5 7) j ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8))) = cols_right0 ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_2 : (tripleIndices 2 1 8).map (fun j => (right0Middle7 5 7) j ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8))) = cols_right0 ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_3 : (tripleIndices 2 1 8).map (fun j => (right0Middle7 5 7) j ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8))) = cols_right0 ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_4 : (tripleIndices 2 1 8).map (fun j => (right0Middle7 5 7) j ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8))) = cols_right0 ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_5 : (tripleIndices 2 1 8).map (fun j => (right0Middle7 5 7) j ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8))) = cols_right0 ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_6 : (tripleIndices 2 1 8).map (fun j => (right0Middle7 5 7) j ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8))) = cols_right0 ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_7 : (tripleIndices 2 1 8).map (fun j => (right0Middle7 5 7) j ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8))) = cols_right0 ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_0 : (tripleIndices 2 1 8).map (fun j => (right0Middle7 5 7) j ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8))) = cols_right0 ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_1 : (tripleIndices 2 1 8).map (fun j => (right0Middle7 5 7) j ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8))) = cols_right0 ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_2 : (tripleIndices 2 1 8).map (fun j => (right0Middle7 5 7) j ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8))) = cols_right0 ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_3 : (tripleIndices 2 1 8).map (fun j => (right0Middle7 5 7) j ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8))) = cols_right0 ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_4 : (tripleIndices 2 1 8).map (fun j => (right0Middle7 5 7) j ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8))) = cols_right0 ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_5 : (tripleIndices 2 1 8).map (fun j => (right0Middle7 5 7) j ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8))) = cols_right0 ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_6 : (tripleIndices 2 1 8).map (fun j => (right0Middle7 5 7) j ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8))) = cols_right0 ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_7 : (tripleIndices 2 1 8).map (fun j => (right0Middle7 5 7) j ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8))) = cols_right0 ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right0_data (r : LeftIndex 7 5 7) : (tripleIndices 2 1 8).map (fun j => (right0Middle7 5 7) j r) = cols_right0 r := by
  fin_cases r
  · exact cols_right0_eq_0_0_0
  · exact cols_right0_eq_0_0_1
  · exact cols_right0_eq_0_0_2
  · exact cols_right0_eq_0_0_3
  · exact cols_right0_eq_0_0_4
  · exact cols_right0_eq_0_0_5
  · exact cols_right0_eq_0_0_6
  · exact cols_right0_eq_0_0_7
  · exact cols_right0_eq_1_0_0
  · exact cols_right0_eq_1_0_1
  · exact cols_right0_eq_1_0_2
  · exact cols_right0_eq_1_0_3
  · exact cols_right0_eq_1_0_4
  · exact cols_right0_eq_1_0_5
  · exact cols_right0_eq_1_0_6
  · exact cols_right0_eq_1_0_7

private def cols_right1Data : List (List ℤ) := [decodeIntegerRow 16 5 2 76293945314,
    decodeIntegerRow 16 5 2 76293945322,
    decodeIntegerRow 16 5 2 76293945362,
    decodeIntegerRow 16 5 2 76293945562,
    decodeIntegerRow 16 5 2 76293946562,
    decodeIntegerRow 16 5 2 76293951562,
    decodeIntegerRow 16 5 2 76293976562,
    decodeIntegerRow 16 5 2 76294101562,
    decodeIntegerRow 16 5 2 76294726562,
    decodeIntegerRow 16 5 2 76297851562,
    decodeIntegerRow 16 5 2 76313476562,
    decodeIntegerRow 16 5 2 76391601562,
    decodeIntegerRow 16 5 2 76782226562,
    decodeIntegerRow 16 5 2 78735351562,
    decodeIntegerRow 16 5 2 88500976562,
    decodeIntegerRow 16 5 2 137329101562]

def cols_right1 (r : LeftIndex 7 5 7) : List ℤ := cols_right1Data.getD (leftPosition 7 5 7 r) []

private theorem cols_right1_eq_0_0_0 : (tripleIndices 1 2 8).map (fun j => (right1Middle7 5 7) j ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8))) = cols_right1 ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_0_1 : (tripleIndices 1 2 8).map (fun j => (right1Middle7 5 7) j ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8))) = cols_right1 ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_0_2 : (tripleIndices 1 2 8).map (fun j => (right1Middle7 5 7) j ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8))) = cols_right1 ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_0_3 : (tripleIndices 1 2 8).map (fun j => (right1Middle7 5 7) j ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8))) = cols_right1 ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_0_4 : (tripleIndices 1 2 8).map (fun j => (right1Middle7 5 7) j ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8))) = cols_right1 ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_0_5 : (tripleIndices 1 2 8).map (fun j => (right1Middle7 5 7) j ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8))) = cols_right1 ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_0_6 : (tripleIndices 1 2 8).map (fun j => (right1Middle7 5 7) j ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8))) = cols_right1 ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_0_7 : (tripleIndices 1 2 8).map (fun j => (right1Middle7 5 7) j ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8))) = cols_right1 ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_0_0 : (tripleIndices 1 2 8).map (fun j => (right1Middle7 5 7) j ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8))) = cols_right1 ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_0_1 : (tripleIndices 1 2 8).map (fun j => (right1Middle7 5 7) j ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8))) = cols_right1 ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_0_2 : (tripleIndices 1 2 8).map (fun j => (right1Middle7 5 7) j ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8))) = cols_right1 ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_0_3 : (tripleIndices 1 2 8).map (fun j => (right1Middle7 5 7) j ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8))) = cols_right1 ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_0_4 : (tripleIndices 1 2 8).map (fun j => (right1Middle7 5 7) j ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8))) = cols_right1 ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_0_5 : (tripleIndices 1 2 8).map (fun j => (right1Middle7 5 7) j ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8))) = cols_right1 ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_0_6 : (tripleIndices 1 2 8).map (fun j => (right1Middle7 5 7) j ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8))) = cols_right1 ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_0_7 : (tripleIndices 1 2 8).map (fun j => (right1Middle7 5 7) j ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8))) = cols_right1 ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right1_data (r : LeftIndex 7 5 7) : (tripleIndices 1 2 8).map (fun j => (right1Middle7 5 7) j r) = cols_right1 r := by
  fin_cases r
  · exact cols_right1_eq_0_0_0
  · exact cols_right1_eq_0_0_1
  · exact cols_right1_eq_0_0_2
  · exact cols_right1_eq_0_0_3
  · exact cols_right1_eq_0_0_4
  · exact cols_right1_eq_0_0_5
  · exact cols_right1_eq_0_0_6
  · exact cols_right1_eq_0_0_7
  · exact cols_right1_eq_1_0_0
  · exact cols_right1_eq_1_0_1
  · exact cols_right1_eq_1_0_2
  · exact cols_right1_eq_1_0_3
  · exact cols_right1_eq_1_0_4
  · exact cols_right1_eq_1_0_5
  · exact cols_right1_eq_1_0_6
  · exact cols_right1_eq_1_0_7

private def cols_left0Data : List (List ℤ) := [decodeIntegerRow 16 3 1 19931224,
    decodeIntegerRow 16 3 1 20991190,
    decodeIntegerRow 16 3 1 35872510,
    decodeIntegerRow 16 3 1 26306248,
    decodeIntegerRow 16 3 1 21543016,
    decodeIntegerRow 16 3 1 21529930,
    decodeIntegerRow 16 3 1 21346210,
    decodeIntegerRow 16 3 1 21464312,
    decodeIntegerRow 16 3 1 7174696,
    decodeIntegerRow 16 3 1 26306410,
    decodeIntegerRow 16 3 1 19926850,
    decodeIntegerRow 16 3 1 22054072,
    decodeIntegerRow 16 3 1 21700504,
    decodeIntegerRow 16 3 1 21464310,
    decodeIntegerRow 16 3 1 21543070,
    decodeIntegerRow 16 3 1 21516808]

def cols_left0 (r : LeftIndex 7 5 7) : List ℤ := cols_left0Data.getD (leftPosition 7 5 7 r) []

private theorem cols_left0_eq_0_0_0 : (tripleIndices 2 1 8).map (fun j => (left0Middle7 5 7) j ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8))) = cols_left0 ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_1 : (tripleIndices 2 1 8).map (fun j => (left0Middle7 5 7) j ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8))) = cols_left0 ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_2 : (tripleIndices 2 1 8).map (fun j => (left0Middle7 5 7) j ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8))) = cols_left0 ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_3 : (tripleIndices 2 1 8).map (fun j => (left0Middle7 5 7) j ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8))) = cols_left0 ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_4 : (tripleIndices 2 1 8).map (fun j => (left0Middle7 5 7) j ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8))) = cols_left0 ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_5 : (tripleIndices 2 1 8).map (fun j => (left0Middle7 5 7) j ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8))) = cols_left0 ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_6 : (tripleIndices 2 1 8).map (fun j => (left0Middle7 5 7) j ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8))) = cols_left0 ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_7 : (tripleIndices 2 1 8).map (fun j => (left0Middle7 5 7) j ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8))) = cols_left0 ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_0 : (tripleIndices 2 1 8).map (fun j => (left0Middle7 5 7) j ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8))) = cols_left0 ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_1 : (tripleIndices 2 1 8).map (fun j => (left0Middle7 5 7) j ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8))) = cols_left0 ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_2 : (tripleIndices 2 1 8).map (fun j => (left0Middle7 5 7) j ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8))) = cols_left0 ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_3 : (tripleIndices 2 1 8).map (fun j => (left0Middle7 5 7) j ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8))) = cols_left0 ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_4 : (tripleIndices 2 1 8).map (fun j => (left0Middle7 5 7) j ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8))) = cols_left0 ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_5 : (tripleIndices 2 1 8).map (fun j => (left0Middle7 5 7) j ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8))) = cols_left0 ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_6 : (tripleIndices 2 1 8).map (fun j => (left0Middle7 5 7) j ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8))) = cols_left0 ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_7 : (tripleIndices 2 1 8).map (fun j => (left0Middle7 5 7) j ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8))) = cols_left0 ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_left0_data (r : LeftIndex 7 5 7) : (tripleIndices 2 1 8).map (fun j => (left0Middle7 5 7) j r) = cols_left0 r := by
  fin_cases r
  · exact cols_left0_eq_0_0_0
  · exact cols_left0_eq_0_0_1
  · exact cols_left0_eq_0_0_2
  · exact cols_left0_eq_0_0_3
  · exact cols_left0_eq_0_0_4
  · exact cols_left0_eq_0_0_5
  · exact cols_left0_eq_0_0_6
  · exact cols_left0_eq_0_0_7
  · exact cols_left0_eq_1_0_0
  · exact cols_left0_eq_1_0_1
  · exact cols_left0_eq_1_0_2
  · exact cols_left0_eq_1_0_3
  · exact cols_left0_eq_1_0_4
  · exact cols_left0_eq_1_0_5
  · exact cols_left0_eq_1_0_6
  · exact cols_left0_eq_1_0_7

private def cols_left1Data : List (List ℤ) := [decodeIntegerRow 16 3 1 21523361,
    decodeIntegerRow 16 3 1 21523363,
    decodeIntegerRow 16 3 1 21523369,
    decodeIntegerRow 16 3 1 21523387,
    decodeIntegerRow 16 3 1 21523441,
    decodeIntegerRow 16 3 1 21523603,
    decodeIntegerRow 16 3 1 21524089,
    decodeIntegerRow 16 3 1 21525547,
    decodeIntegerRow 16 3 1 21529921,
    decodeIntegerRow 16 3 1 21543043,
    decodeIntegerRow 16 3 1 21582409,
    decodeIntegerRow 16 3 1 21700507,
    decodeIntegerRow 16 3 1 22054801,
    decodeIntegerRow 16 3 1 23117683,
    decodeIntegerRow 16 3 1 26306329,
    decodeIntegerRow 16 3 1 35872267]

def cols_left1 (r : LeftIndex 7 5 7) : List ℤ := cols_left1Data.getD (leftPosition 7 5 7 r) []

private theorem cols_left1_eq_0_0_0 : (tripleIndices 1 2 8).map (fun j => (left1Middle7 5 7) j ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8))) = cols_left1 ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_0_1 : (tripleIndices 1 2 8).map (fun j => (left1Middle7 5 7) j ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8))) = cols_left1 ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_0_2 : (tripleIndices 1 2 8).map (fun j => (left1Middle7 5 7) j ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8))) = cols_left1 ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_0_3 : (tripleIndices 1 2 8).map (fun j => (left1Middle7 5 7) j ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8))) = cols_left1 ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_0_4 : (tripleIndices 1 2 8).map (fun j => (left1Middle7 5 7) j ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8))) = cols_left1 ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_0_5 : (tripleIndices 1 2 8).map (fun j => (left1Middle7 5 7) j ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8))) = cols_left1 ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_0_6 : (tripleIndices 1 2 8).map (fun j => (left1Middle7 5 7) j ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8))) = cols_left1 ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_0_7 : (tripleIndices 1 2 8).map (fun j => (left1Middle7 5 7) j ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8))) = cols_left1 ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_0_0 : (tripleIndices 1 2 8).map (fun j => (left1Middle7 5 7) j ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8))) = cols_left1 ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_0_1 : (tripleIndices 1 2 8).map (fun j => (left1Middle7 5 7) j ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8))) = cols_left1 ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_0_2 : (tripleIndices 1 2 8).map (fun j => (left1Middle7 5 7) j ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8))) = cols_left1 ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_0_3 : (tripleIndices 1 2 8).map (fun j => (left1Middle7 5 7) j ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8))) = cols_left1 ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_0_4 : (tripleIndices 1 2 8).map (fun j => (left1Middle7 5 7) j ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8))) = cols_left1 ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_0_5 : (tripleIndices 1 2 8).map (fun j => (left1Middle7 5 7) j ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8))) = cols_left1 ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_0_6 : (tripleIndices 1 2 8).map (fun j => (left1Middle7 5 7) j ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8))) = cols_left1 ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_0_7 : (tripleIndices 1 2 8).map (fun j => (left1Middle7 5 7) j ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8))) = cols_left1 ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_left1_data (r : LeftIndex 7 5 7) : (tripleIndices 1 2 8).map (fun j => (left1Middle7 5 7) j r) = cols_left1 r := by
  fin_cases r
  · exact cols_left1_eq_0_0_0
  · exact cols_left1_eq_0_0_1
  · exact cols_left1_eq_0_0_2
  · exact cols_left1_eq_0_0_3
  · exact cols_left1_eq_0_0_4
  · exact cols_left1_eq_0_0_5
  · exact cols_left1_eq_0_0_6
  · exact cols_left1_eq_0_0_7
  · exact cols_left1_eq_1_0_0
  · exact cols_left1_eq_1_0_1
  · exact cols_left1_eq_1_0_2
  · exact cols_left1_eq_1_0_3
  · exact cols_left1_eq_1_0_4
  · exact cols_left1_eq_1_0_5
  · exact cols_left1_eq_1_0_6
  · exact cols_left1_eq_1_0_7

private def cols_right2Data : List (List ℤ) := [decodeIntegerRow 16 5 2 78735195312,
    decodeIntegerRow 16 5 2 76782257812,
    decodeIntegerRow 16 5 2 15258782812,
    decodeIntegerRow 16 5 2 64086915312,
    decodeIntegerRow 16 5 2 76290039312,
    decodeIntegerRow 16 5 2 76293164012,
    decodeIntegerRow 16 5 2 76391601572,
    decodeIntegerRow 16 5 2 76313476560,
    decodeIntegerRow 16 5 2 137329095312,
    decodeIntegerRow 16 5 2 64086912812,
    decodeIntegerRow 16 5 2 78735507812,
    decodeIntegerRow 16 5 2 75805695312,
    decodeIntegerRow 16 5 2 76196289072,
    decodeIntegerRow 16 5 2 76313476564,
    decodeIntegerRow 16 5 2 76290038812,
    decodeIntegerRow 16 5 2 76294726512]

def cols_right2 (r : LeftIndex 7 5 7) : List ℤ := cols_right2Data.getD (leftPosition 7 5 7 r) []

private theorem cols_right2_eq_0_0_0 : (tripleIndices 1 2 8).map (fun j => (right2Middle7 5 7) j ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8))) = cols_right2 ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_1 : (tripleIndices 1 2 8).map (fun j => (right2Middle7 5 7) j ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8))) = cols_right2 ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_2 : (tripleIndices 1 2 8).map (fun j => (right2Middle7 5 7) j ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8))) = cols_right2 ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_3 : (tripleIndices 1 2 8).map (fun j => (right2Middle7 5 7) j ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8))) = cols_right2 ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_4 : (tripleIndices 1 2 8).map (fun j => (right2Middle7 5 7) j ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8))) = cols_right2 ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_5 : (tripleIndices 1 2 8).map (fun j => (right2Middle7 5 7) j ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8))) = cols_right2 ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_6 : (tripleIndices 1 2 8).map (fun j => (right2Middle7 5 7) j ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8))) = cols_right2 ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_7 : (tripleIndices 1 2 8).map (fun j => (right2Middle7 5 7) j ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8))) = cols_right2 ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_0 : (tripleIndices 1 2 8).map (fun j => (right2Middle7 5 7) j ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8))) = cols_right2 ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_1 : (tripleIndices 1 2 8).map (fun j => (right2Middle7 5 7) j ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8))) = cols_right2 ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_2 : (tripleIndices 1 2 8).map (fun j => (right2Middle7 5 7) j ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8))) = cols_right2 ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_3 : (tripleIndices 1 2 8).map (fun j => (right2Middle7 5 7) j ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8))) = cols_right2 ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_4 : (tripleIndices 1 2 8).map (fun j => (right2Middle7 5 7) j ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8))) = cols_right2 ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_5 : (tripleIndices 1 2 8).map (fun j => (right2Middle7 5 7) j ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8))) = cols_right2 ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_6 : (tripleIndices 1 2 8).map (fun j => (right2Middle7 5 7) j ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8))) = cols_right2 ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_7 : (tripleIndices 1 2 8).map (fun j => (right2Middle7 5 7) j ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8))) = cols_right2 ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right2_data (r : LeftIndex 7 5 7) : (tripleIndices 1 2 8).map (fun j => (right2Middle7 5 7) j r) = cols_right2 r := by
  fin_cases r
  · exact cols_right2_eq_0_0_0
  · exact cols_right2_eq_0_0_1
  · exact cols_right2_eq_0_0_2
  · exact cols_right2_eq_0_0_3
  · exact cols_right2_eq_0_0_4
  · exact cols_right2_eq_0_0_5
  · exact cols_right2_eq_0_0_6
  · exact cols_right2_eq_0_0_7
  · exact cols_right2_eq_1_0_0
  · exact cols_right2_eq_1_0_1
  · exact cols_right2_eq_1_0_2
  · exact cols_right2_eq_1_0_3
  · exact cols_right2_eq_1_0_4
  · exact cols_right2_eq_1_0_5
  · exact cols_right2_eq_1_0_6
  · exact cols_right2_eq_1_0_7

theorem product0_eq : HexagonAtoms757.outerABC * HexagonAtoms757.assocABC = HexagonAtoms757.assocABC :=
  Matrix.one_mul (m := Fin 2 × Fin 1 × Fin 8) (n := Fin 2 × Fin 1 × Fin 8) _

theorem product1_eq : HexagonAtoms757.assocBAC * HexagonAtoms757.innerABC = HexagonAtoms757.assocBAC :=
  Matrix.mul_one (m := Fin 1 × Fin 2 × Fin 8) (n := Fin 2 × Fin 1 × Fin 8) _

theorem product2_eq : HexagonAtoms757.innerRightABC * HexagonAtoms757.assocABC = HexagonAtoms757.assocABC :=
  Matrix.one_mul (m := Fin 2 × Fin 1 × Fin 8) (n := Fin 2 × Fin 1 × Fin 8) _

theorem product3_eq : HexagonAtoms757.inverseACB * right0Middle7 5 7 = rowColumnMul rows_inverseACB cols_right0 :=
  (rowColumnMul_eq _ _ _ _ rows_inverseACB_data cols_right0_data).symm

theorem product4_eq : HexagonAtoms757.innerACB * right1Middle7 5 7 = rowColumnMul rows_innerACB cols_right1 :=
  (rowColumnMul_eq _ _ _ _ rows_innerACB_data cols_right1_data).symm

theorem product5_eq : HexagonAtoms757.assocBAC * left0Middle7 5 7 = rowColumnMul rows_assocBAC cols_left0 :=
  (rowColumnMul_eq _ _ _ _ rows_assocBAC_data cols_left0_data).symm

theorem product6_eq : HexagonAtoms757.innerRightBAC * left1Middle7 5 7 = rowColumnMul rows_innerRightBAC cols_left1 :=
  (rowColumnMul_eq _ _ _ _ rows_innerRightBAC_data cols_left1_data).symm

theorem product7_eq : HexagonAtoms757.assocCAB * right2Middle7 5 7 = rowColumnMul rows_assocCAB cols_right2 :=
  (rowColumnMul_eq _ _ _ _ rows_assocCAB_data cols_right2_data).symm

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn757
