import RMod.BrundanEllis.StackingReferenceHexagonAtoms577
import RMod.BrundanEllis.StackingReferenceHexagonMiddle5
import RMod.BrundanEllis.StackingReferenceRowColumnCheck

/-! Verified row and column lists. Each subsequent scalar product traverses
these lists directly, without repeated lookup into the original matrices. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn577
open Superfusion

theorem innerACB_alias : HexagonAtoms577.innerACB = HexagonAtoms577.innerABC :=
  HexagonAtoms577.innerACB_eq.symm.trans HexagonAtoms577.innerABC_eq

theorem assocCAB_alias : HexagonAtoms577.assocCAB = HexagonAtoms577.assocBAC :=
  HexagonAtoms577.assocCAB_eq.symm.trans HexagonAtoms577.assocBAC_eq

private def rows_innerRightABCData : List (List ℤ) := [decodeIntegerRow 16 3 1 23115496,
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

def rows_innerRightABC (r : RightIndex 5 7 7) : List ℤ := rows_innerRightABCData.getD (rightPosition 5 7 7 r) []

private theorem rows_innerRightABC_eq_0_0_0 : (tripleIndices 1 2 8).map ((HexagonAtoms577.innerRightABC) ((0 : Fin 1), (0 : Fin 2), (0 : Fin 8))) = rows_innerRightABC ((0 : Fin 1), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_0_1 : (tripleIndices 1 2 8).map ((HexagonAtoms577.innerRightABC) ((0 : Fin 1), (0 : Fin 2), (1 : Fin 8))) = rows_innerRightABC ((0 : Fin 1), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_0_2 : (tripleIndices 1 2 8).map ((HexagonAtoms577.innerRightABC) ((0 : Fin 1), (0 : Fin 2), (2 : Fin 8))) = rows_innerRightABC ((0 : Fin 1), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_0_3 : (tripleIndices 1 2 8).map ((HexagonAtoms577.innerRightABC) ((0 : Fin 1), (0 : Fin 2), (3 : Fin 8))) = rows_innerRightABC ((0 : Fin 1), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_0_4 : (tripleIndices 1 2 8).map ((HexagonAtoms577.innerRightABC) ((0 : Fin 1), (0 : Fin 2), (4 : Fin 8))) = rows_innerRightABC ((0 : Fin 1), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_0_5 : (tripleIndices 1 2 8).map ((HexagonAtoms577.innerRightABC) ((0 : Fin 1), (0 : Fin 2), (5 : Fin 8))) = rows_innerRightABC ((0 : Fin 1), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_0_6 : (tripleIndices 1 2 8).map ((HexagonAtoms577.innerRightABC) ((0 : Fin 1), (0 : Fin 2), (6 : Fin 8))) = rows_innerRightABC ((0 : Fin 1), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_0_7 : (tripleIndices 1 2 8).map ((HexagonAtoms577.innerRightABC) ((0 : Fin 1), (0 : Fin 2), (7 : Fin 8))) = rows_innerRightABC ((0 : Fin 1), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_1_0 : (tripleIndices 1 2 8).map ((HexagonAtoms577.innerRightABC) ((0 : Fin 1), (1 : Fin 2), (0 : Fin 8))) = rows_innerRightABC ((0 : Fin 1), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_1_1 : (tripleIndices 1 2 8).map ((HexagonAtoms577.innerRightABC) ((0 : Fin 1), (1 : Fin 2), (1 : Fin 8))) = rows_innerRightABC ((0 : Fin 1), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_1_2 : (tripleIndices 1 2 8).map ((HexagonAtoms577.innerRightABC) ((0 : Fin 1), (1 : Fin 2), (2 : Fin 8))) = rows_innerRightABC ((0 : Fin 1), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_1_3 : (tripleIndices 1 2 8).map ((HexagonAtoms577.innerRightABC) ((0 : Fin 1), (1 : Fin 2), (3 : Fin 8))) = rows_innerRightABC ((0 : Fin 1), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_1_4 : (tripleIndices 1 2 8).map ((HexagonAtoms577.innerRightABC) ((0 : Fin 1), (1 : Fin 2), (4 : Fin 8))) = rows_innerRightABC ((0 : Fin 1), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_1_5 : (tripleIndices 1 2 8).map ((HexagonAtoms577.innerRightABC) ((0 : Fin 1), (1 : Fin 2), (5 : Fin 8))) = rows_innerRightABC ((0 : Fin 1), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_1_6 : (tripleIndices 1 2 8).map ((HexagonAtoms577.innerRightABC) ((0 : Fin 1), (1 : Fin 2), (6 : Fin 8))) = rows_innerRightABC ((0 : Fin 1), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_1_7 : (tripleIndices 1 2 8).map ((HexagonAtoms577.innerRightABC) ((0 : Fin 1), (1 : Fin 2), (7 : Fin 8))) = rows_innerRightABC ((0 : Fin 1), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_innerRightABC_data (r : RightIndex 5 7 7) : (tripleIndices 1 2 8).map ((HexagonAtoms577.innerRightABC) r) = rows_innerRightABC r := by
  fin_cases r
  · exact rows_innerRightABC_eq_0_0_0
  · exact rows_innerRightABC_eq_0_0_1
  · exact rows_innerRightABC_eq_0_0_2
  · exact rows_innerRightABC_eq_0_0_3
  · exact rows_innerRightABC_eq_0_0_4
  · exact rows_innerRightABC_eq_0_0_5
  · exact rows_innerRightABC_eq_0_0_6
  · exact rows_innerRightABC_eq_0_0_7
  · exact rows_innerRightABC_eq_0_1_0
  · exact rows_innerRightABC_eq_0_1_1
  · exact rows_innerRightABC_eq_0_1_2
  · exact rows_innerRightABC_eq_0_1_3
  · exact rows_innerRightABC_eq_0_1_4
  · exact rows_innerRightABC_eq_0_1_5
  · exact rows_innerRightABC_eq_0_1_6
  · exact rows_innerRightABC_eq_0_1_7

private def rows_inverseACBData : List (List ℤ) := [decodeIntegerRow 16 3 1 21523361,
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

def rows_inverseACB (r : LeftIndex 5 7 7) : List ℤ := rows_inverseACBData.getD (leftPosition 5 7 7 r) []

private theorem rows_inverseACB_eq_0_0_0 : (tripleIndices 1 2 8).map ((HexagonAtoms577.inverseACB) ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_1 : (tripleIndices 1 2 8).map ((HexagonAtoms577.inverseACB) ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_2 : (tripleIndices 1 2 8).map ((HexagonAtoms577.inverseACB) ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_3 : (tripleIndices 1 2 8).map ((HexagonAtoms577.inverseACB) ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_4 : (tripleIndices 1 2 8).map ((HexagonAtoms577.inverseACB) ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_5 : (tripleIndices 1 2 8).map ((HexagonAtoms577.inverseACB) ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_6 : (tripleIndices 1 2 8).map ((HexagonAtoms577.inverseACB) ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_7 : (tripleIndices 1 2 8).map ((HexagonAtoms577.inverseACB) ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_0 : (tripleIndices 1 2 8).map ((HexagonAtoms577.inverseACB) ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_1 : (tripleIndices 1 2 8).map ((HexagonAtoms577.inverseACB) ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_2 : (tripleIndices 1 2 8).map ((HexagonAtoms577.inverseACB) ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_3 : (tripleIndices 1 2 8).map ((HexagonAtoms577.inverseACB) ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_4 : (tripleIndices 1 2 8).map ((HexagonAtoms577.inverseACB) ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_5 : (tripleIndices 1 2 8).map ((HexagonAtoms577.inverseACB) ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_6 : (tripleIndices 1 2 8).map ((HexagonAtoms577.inverseACB) ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_7 : (tripleIndices 1 2 8).map ((HexagonAtoms577.inverseACB) ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_inverseACB_data (r : LeftIndex 5 7 7) : (tripleIndices 1 2 8).map ((HexagonAtoms577.inverseACB) r) = rows_inverseACB r := by
  fin_cases r
  · exact rows_inverseACB_eq_0_0_0
  · exact rows_inverseACB_eq_0_0_1
  · exact rows_inverseACB_eq_0_0_2
  · exact rows_inverseACB_eq_0_0_3
  · exact rows_inverseACB_eq_0_0_4
  · exact rows_inverseACB_eq_0_0_5
  · exact rows_inverseACB_eq_0_0_6
  · exact rows_inverseACB_eq_0_0_7
  · exact rows_inverseACB_eq_1_0_0
  · exact rows_inverseACB_eq_1_0_1
  · exact rows_inverseACB_eq_1_0_2
  · exact rows_inverseACB_eq_1_0_3
  · exact rows_inverseACB_eq_1_0_4
  · exact rows_inverseACB_eq_1_0_5
  · exact rows_inverseACB_eq_1_0_6
  · exact rows_inverseACB_eq_1_0_7

private def rows_assocBCAData : List (List ℤ) := [decodeIntegerRow 16 3 1 19931224,
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

def rows_assocBCA (r : RightIndex 7 7 5) : List ℤ := rows_assocBCAData.getD (rightPosition 7 7 5 r) []

private theorem rows_assocBCA_eq_0_0_0 : (tripleIndices 1 2 8).map ((HexagonAtoms577.assocBCA) ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8))) = rows_assocBCA ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_1 : (tripleIndices 1 2 8).map ((HexagonAtoms577.assocBCA) ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8))) = rows_assocBCA ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_2 : (tripleIndices 1 2 8).map ((HexagonAtoms577.assocBCA) ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8))) = rows_assocBCA ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_3 : (tripleIndices 1 2 8).map ((HexagonAtoms577.assocBCA) ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8))) = rows_assocBCA ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_4 : (tripleIndices 1 2 8).map ((HexagonAtoms577.assocBCA) ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8))) = rows_assocBCA ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_5 : (tripleIndices 1 2 8).map ((HexagonAtoms577.assocBCA) ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8))) = rows_assocBCA ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_6 : (tripleIndices 1 2 8).map ((HexagonAtoms577.assocBCA) ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8))) = rows_assocBCA ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_7 : (tripleIndices 1 2 8).map ((HexagonAtoms577.assocBCA) ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8))) = rows_assocBCA ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_0 : (tripleIndices 1 2 8).map ((HexagonAtoms577.assocBCA) ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8))) = rows_assocBCA ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_1 : (tripleIndices 1 2 8).map ((HexagonAtoms577.assocBCA) ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8))) = rows_assocBCA ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_2 : (tripleIndices 1 2 8).map ((HexagonAtoms577.assocBCA) ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8))) = rows_assocBCA ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_3 : (tripleIndices 1 2 8).map ((HexagonAtoms577.assocBCA) ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8))) = rows_assocBCA ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_4 : (tripleIndices 1 2 8).map ((HexagonAtoms577.assocBCA) ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8))) = rows_assocBCA ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_5 : (tripleIndices 1 2 8).map ((HexagonAtoms577.assocBCA) ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8))) = rows_assocBCA ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_6 : (tripleIndices 1 2 8).map ((HexagonAtoms577.assocBCA) ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8))) = rows_assocBCA ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_7 : (tripleIndices 1 2 8).map ((HexagonAtoms577.assocBCA) ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8))) = rows_assocBCA ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocBCA_data (r : RightIndex 7 7 5) : (tripleIndices 1 2 8).map ((HexagonAtoms577.assocBCA) r) = rows_assocBCA r := by
  fin_cases r
  · exact rows_assocBCA_eq_0_0_0
  · exact rows_assocBCA_eq_0_0_1
  · exact rows_assocBCA_eq_0_0_2
  · exact rows_assocBCA_eq_0_0_3
  · exact rows_assocBCA_eq_0_0_4
  · exact rows_assocBCA_eq_0_0_5
  · exact rows_assocBCA_eq_0_0_6
  · exact rows_assocBCA_eq_0_0_7
  · exact rows_assocBCA_eq_1_0_0
  · exact rows_assocBCA_eq_1_0_1
  · exact rows_assocBCA_eq_1_0_2
  · exact rows_assocBCA_eq_1_0_3
  · exact rows_assocBCA_eq_1_0_4
  · exact rows_assocBCA_eq_1_0_5
  · exact rows_assocBCA_eq_1_0_6
  · exact rows_assocBCA_eq_1_0_7

private def rows_assocBACData : List (List ℤ) := [decodeIntegerRow 16 3 1 19931224,
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

def rows_assocBAC (r : RightIndex 7 5 7) : List ℤ := rows_assocBACData.getD (rightPosition 7 5 7 r) []

private theorem rows_assocBAC_eq_0_0_0 : (tripleIndices 2 1 8).map ((HexagonAtoms577.assocBAC) ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8))) = rows_assocBAC ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_1 : (tripleIndices 2 1 8).map ((HexagonAtoms577.assocBAC) ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8))) = rows_assocBAC ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_2 : (tripleIndices 2 1 8).map ((HexagonAtoms577.assocBAC) ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8))) = rows_assocBAC ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_3 : (tripleIndices 2 1 8).map ((HexagonAtoms577.assocBAC) ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8))) = rows_assocBAC ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_4 : (tripleIndices 2 1 8).map ((HexagonAtoms577.assocBAC) ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8))) = rows_assocBAC ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_5 : (tripleIndices 2 1 8).map ((HexagonAtoms577.assocBAC) ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8))) = rows_assocBAC ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_6 : (tripleIndices 2 1 8).map ((HexagonAtoms577.assocBAC) ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8))) = rows_assocBAC ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_7 : (tripleIndices 2 1 8).map ((HexagonAtoms577.assocBAC) ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8))) = rows_assocBAC ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_0 : (tripleIndices 2 1 8).map ((HexagonAtoms577.assocBAC) ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8))) = rows_assocBAC ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_1 : (tripleIndices 2 1 8).map ((HexagonAtoms577.assocBAC) ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8))) = rows_assocBAC ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_2 : (tripleIndices 2 1 8).map ((HexagonAtoms577.assocBAC) ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8))) = rows_assocBAC ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_3 : (tripleIndices 2 1 8).map ((HexagonAtoms577.assocBAC) ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8))) = rows_assocBAC ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_4 : (tripleIndices 2 1 8).map ((HexagonAtoms577.assocBAC) ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8))) = rows_assocBAC ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_5 : (tripleIndices 2 1 8).map ((HexagonAtoms577.assocBAC) ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8))) = rows_assocBAC ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_6 : (tripleIndices 2 1 8).map ((HexagonAtoms577.assocBAC) ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8))) = rows_assocBAC ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_7 : (tripleIndices 2 1 8).map ((HexagonAtoms577.assocBAC) ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8))) = rows_assocBAC ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocBAC_data (r : RightIndex 7 5 7) : (tripleIndices 2 1 8).map ((HexagonAtoms577.assocBAC) r) = rows_assocBAC r := by
  fin_cases r
  · exact rows_assocBAC_eq_0_0_0
  · exact rows_assocBAC_eq_0_0_1
  · exact rows_assocBAC_eq_0_0_2
  · exact rows_assocBAC_eq_0_0_3
  · exact rows_assocBAC_eq_0_0_4
  · exact rows_assocBAC_eq_0_0_5
  · exact rows_assocBAC_eq_0_0_6
  · exact rows_assocBAC_eq_0_0_7
  · exact rows_assocBAC_eq_1_0_0
  · exact rows_assocBAC_eq_1_0_1
  · exact rows_assocBAC_eq_1_0_2
  · exact rows_assocBAC_eq_1_0_3
  · exact rows_assocBAC_eq_1_0_4
  · exact rows_assocBAC_eq_1_0_5
  · exact rows_assocBAC_eq_1_0_6
  · exact rows_assocBAC_eq_1_0_7

private def cols_assocABCData : List (List ℤ) := [decodeIntegerRow 16 3 1 21523361,
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

def cols_assocABC (r : LeftIndex 5 7 7) : List ℤ := cols_assocABCData.getD (leftPosition 5 7 7 r) []

private theorem cols_assocABC_eq_0_0_0 : (tripleIndices 1 2 8).map (fun j => (HexagonAtoms577.assocABC) j ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8))) = cols_assocABC ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_1 : (tripleIndices 1 2 8).map (fun j => (HexagonAtoms577.assocABC) j ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8))) = cols_assocABC ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_2 : (tripleIndices 1 2 8).map (fun j => (HexagonAtoms577.assocABC) j ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8))) = cols_assocABC ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_3 : (tripleIndices 1 2 8).map (fun j => (HexagonAtoms577.assocABC) j ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8))) = cols_assocABC ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_4 : (tripleIndices 1 2 8).map (fun j => (HexagonAtoms577.assocABC) j ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8))) = cols_assocABC ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_5 : (tripleIndices 1 2 8).map (fun j => (HexagonAtoms577.assocABC) j ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8))) = cols_assocABC ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_6 : (tripleIndices 1 2 8).map (fun j => (HexagonAtoms577.assocABC) j ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8))) = cols_assocABC ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_7 : (tripleIndices 1 2 8).map (fun j => (HexagonAtoms577.assocABC) j ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8))) = cols_assocABC ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_0 : (tripleIndices 1 2 8).map (fun j => (HexagonAtoms577.assocABC) j ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8))) = cols_assocABC ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_1 : (tripleIndices 1 2 8).map (fun j => (HexagonAtoms577.assocABC) j ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8))) = cols_assocABC ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_2 : (tripleIndices 1 2 8).map (fun j => (HexagonAtoms577.assocABC) j ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8))) = cols_assocABC ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_3 : (tripleIndices 1 2 8).map (fun j => (HexagonAtoms577.assocABC) j ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8))) = cols_assocABC ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_4 : (tripleIndices 1 2 8).map (fun j => (HexagonAtoms577.assocABC) j ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8))) = cols_assocABC ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_5 : (tripleIndices 1 2 8).map (fun j => (HexagonAtoms577.assocABC) j ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8))) = cols_assocABC ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_6 : (tripleIndices 1 2 8).map (fun j => (HexagonAtoms577.assocABC) j ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8))) = cols_assocABC ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_7 : (tripleIndices 1 2 8).map (fun j => (HexagonAtoms577.assocABC) j ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8))) = cols_assocABC ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_assocABC_data (r : LeftIndex 5 7 7) : (tripleIndices 1 2 8).map (fun j => (HexagonAtoms577.assocABC) j r) = cols_assocABC r := by
  fin_cases r
  · exact cols_assocABC_eq_0_0_0
  · exact cols_assocABC_eq_0_0_1
  · exact cols_assocABC_eq_0_0_2
  · exact cols_assocABC_eq_0_0_3
  · exact cols_assocABC_eq_0_0_4
  · exact cols_assocABC_eq_0_0_5
  · exact cols_assocABC_eq_0_0_6
  · exact cols_assocABC_eq_0_0_7
  · exact cols_assocABC_eq_1_0_0
  · exact cols_assocABC_eq_1_0_1
  · exact cols_assocABC_eq_1_0_2
  · exact cols_assocABC_eq_1_0_3
  · exact cols_assocABC_eq_1_0_4
  · exact cols_assocABC_eq_1_0_5
  · exact cols_assocABC_eq_1_0_6
  · exact cols_assocABC_eq_1_0_7

private def cols_right0Data : List (List ℤ) := [decodeIntegerRow 16 3 1 23115496,
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

def cols_right0 (r : LeftIndex 5 7 7) : List ℤ := cols_right0Data.getD (leftPosition 5 7 7 r) []

private theorem cols_right0_eq_0_0_0 : (tripleIndices 1 2 8).map (fun j => (right0Middle5 7 7) j ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8))) = cols_right0 ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_1 : (tripleIndices 1 2 8).map (fun j => (right0Middle5 7 7) j ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8))) = cols_right0 ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_2 : (tripleIndices 1 2 8).map (fun j => (right0Middle5 7 7) j ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8))) = cols_right0 ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_3 : (tripleIndices 1 2 8).map (fun j => (right0Middle5 7 7) j ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8))) = cols_right0 ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_4 : (tripleIndices 1 2 8).map (fun j => (right0Middle5 7 7) j ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8))) = cols_right0 ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_5 : (tripleIndices 1 2 8).map (fun j => (right0Middle5 7 7) j ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8))) = cols_right0 ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_6 : (tripleIndices 1 2 8).map (fun j => (right0Middle5 7 7) j ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8))) = cols_right0 ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_7 : (tripleIndices 1 2 8).map (fun j => (right0Middle5 7 7) j ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8))) = cols_right0 ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_0 : (tripleIndices 1 2 8).map (fun j => (right0Middle5 7 7) j ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8))) = cols_right0 ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_1 : (tripleIndices 1 2 8).map (fun j => (right0Middle5 7 7) j ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8))) = cols_right0 ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_2 : (tripleIndices 1 2 8).map (fun j => (right0Middle5 7 7) j ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8))) = cols_right0 ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_3 : (tripleIndices 1 2 8).map (fun j => (right0Middle5 7 7) j ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8))) = cols_right0 ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_4 : (tripleIndices 1 2 8).map (fun j => (right0Middle5 7 7) j ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8))) = cols_right0 ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_5 : (tripleIndices 1 2 8).map (fun j => (right0Middle5 7 7) j ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8))) = cols_right0 ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_6 : (tripleIndices 1 2 8).map (fun j => (right0Middle5 7 7) j ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8))) = cols_right0 ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_7 : (tripleIndices 1 2 8).map (fun j => (right0Middle5 7 7) j ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8))) = cols_right0 ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right0_data (r : LeftIndex 5 7 7) : (tripleIndices 1 2 8).map (fun j => (right0Middle5 7 7) j r) = cols_right0 r := by
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

private def cols_left0Data : List (List ℤ) := [decodeIntegerRow 16 3 1 21523361,
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

def cols_left0 (r : LeftIndex 5 7 7) : List ℤ := cols_left0Data.getD (leftPosition 5 7 7 r) []

private theorem cols_left0_eq_0_0_0 : (tripleIndices 1 2 8).map (fun j => (left0Middle5 7 7) j ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8))) = cols_left0 ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_1 : (tripleIndices 1 2 8).map (fun j => (left0Middle5 7 7) j ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8))) = cols_left0 ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_2 : (tripleIndices 1 2 8).map (fun j => (left0Middle5 7 7) j ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8))) = cols_left0 ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_3 : (tripleIndices 1 2 8).map (fun j => (left0Middle5 7 7) j ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8))) = cols_left0 ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_4 : (tripleIndices 1 2 8).map (fun j => (left0Middle5 7 7) j ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8))) = cols_left0 ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_5 : (tripleIndices 1 2 8).map (fun j => (left0Middle5 7 7) j ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8))) = cols_left0 ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_6 : (tripleIndices 1 2 8).map (fun j => (left0Middle5 7 7) j ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8))) = cols_left0 ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_7 : (tripleIndices 1 2 8).map (fun j => (left0Middle5 7 7) j ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8))) = cols_left0 ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_0 : (tripleIndices 1 2 8).map (fun j => (left0Middle5 7 7) j ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8))) = cols_left0 ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_1 : (tripleIndices 1 2 8).map (fun j => (left0Middle5 7 7) j ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8))) = cols_left0 ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_2 : (tripleIndices 1 2 8).map (fun j => (left0Middle5 7 7) j ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8))) = cols_left0 ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_3 : (tripleIndices 1 2 8).map (fun j => (left0Middle5 7 7) j ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8))) = cols_left0 ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_4 : (tripleIndices 1 2 8).map (fun j => (left0Middle5 7 7) j ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8))) = cols_left0 ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_5 : (tripleIndices 1 2 8).map (fun j => (left0Middle5 7 7) j ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8))) = cols_left0 ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_6 : (tripleIndices 1 2 8).map (fun j => (left0Middle5 7 7) j ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8))) = cols_left0 ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_7 : (tripleIndices 1 2 8).map (fun j => (left0Middle5 7 7) j ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8))) = cols_left0 ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_left0_data (r : LeftIndex 5 7 7) : (tripleIndices 1 2 8).map (fun j => (left0Middle5 7 7) j r) = cols_left0 r := by
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

private def cols_right2Data : List (List ℤ) := [decodeIntegerRow 16 3 1 23115496,
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

def cols_right2 (r : LeftIndex 5 7 7) : List ℤ := cols_right2Data.getD (leftPosition 5 7 7 r) []

private theorem cols_right2_eq_0_0_0 : (tripleIndices 2 1 8).map (fun j => (right2Middle5 7 7) j ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8))) = cols_right2 ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_1 : (tripleIndices 2 1 8).map (fun j => (right2Middle5 7 7) j ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8))) = cols_right2 ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_2 : (tripleIndices 2 1 8).map (fun j => (right2Middle5 7 7) j ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8))) = cols_right2 ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_3 : (tripleIndices 2 1 8).map (fun j => (right2Middle5 7 7) j ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8))) = cols_right2 ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_4 : (tripleIndices 2 1 8).map (fun j => (right2Middle5 7 7) j ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8))) = cols_right2 ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_5 : (tripleIndices 2 1 8).map (fun j => (right2Middle5 7 7) j ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8))) = cols_right2 ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_6 : (tripleIndices 2 1 8).map (fun j => (right2Middle5 7 7) j ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8))) = cols_right2 ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_7 : (tripleIndices 2 1 8).map (fun j => (right2Middle5 7 7) j ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8))) = cols_right2 ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_0 : (tripleIndices 2 1 8).map (fun j => (right2Middle5 7 7) j ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8))) = cols_right2 ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_1 : (tripleIndices 2 1 8).map (fun j => (right2Middle5 7 7) j ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8))) = cols_right2 ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_2 : (tripleIndices 2 1 8).map (fun j => (right2Middle5 7 7) j ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8))) = cols_right2 ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_3 : (tripleIndices 2 1 8).map (fun j => (right2Middle5 7 7) j ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8))) = cols_right2 ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_4 : (tripleIndices 2 1 8).map (fun j => (right2Middle5 7 7) j ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8))) = cols_right2 ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_5 : (tripleIndices 2 1 8).map (fun j => (right2Middle5 7 7) j ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8))) = cols_right2 ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_6 : (tripleIndices 2 1 8).map (fun j => (right2Middle5 7 7) j ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8))) = cols_right2 ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_7 : (tripleIndices 2 1 8).map (fun j => (right2Middle5 7 7) j ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8))) = cols_right2 ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right2_data (r : LeftIndex 5 7 7) : (tripleIndices 2 1 8).map (fun j => (right2Middle5 7 7) j r) = cols_right2 r := by
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

theorem product0_eq : HexagonAtoms577.outerABC * HexagonAtoms577.assocABC = HexagonAtoms577.assocABC :=
  Matrix.one_mul (m := Fin 1 × Fin 2 × Fin 8) (n := Fin 2 × Fin 1 × Fin 8) _

theorem product1_eq : HexagonAtoms577.assocBAC * HexagonAtoms577.innerABC = HexagonAtoms577.assocBAC :=
  Matrix.mul_one (m := Fin 2 × Fin 1 × Fin 8) (n := Fin 2 × Fin 1 × Fin 8) _

theorem product2_eq : HexagonAtoms577.innerRightABC * HexagonAtoms577.assocABC = rowColumnMul rows_innerRightABC cols_assocABC :=
  (rowColumnMul_eq _ _ _ _ rows_innerRightABC_data cols_assocABC_data).symm

theorem product3_eq : HexagonAtoms577.inverseACB * right0Middle5 7 7 = rowColumnMul rows_inverseACB cols_right0 :=
  (rowColumnMul_eq _ _ _ _ rows_inverseACB_data cols_right0_data).symm

theorem product4_eq : HexagonAtoms577.innerABC * right1Middle5 7 7 = right1Middle5 7 7 :=
  Matrix.one_mul (m := Fin 2 × Fin 1 × Fin 8) (n := Fin 2 × Fin 1 × Fin 8) _

theorem product5_eq : HexagonAtoms577.assocBCA * left0Middle5 7 7 = rowColumnMul rows_assocBCA cols_left0 :=
  (rowColumnMul_eq _ _ _ _ rows_assocBCA_data cols_left0_data).symm

theorem product6_eq : HexagonAtoms577.innerRightBAC * left1Middle5 7 7 = left1Middle5 7 7 :=
  Matrix.one_mul (m := Fin 2 × Fin 1 × Fin 8) (n := Fin 2 × Fin 1 × Fin 8) _

theorem product7_eq : HexagonAtoms577.assocBAC * right2Middle5 7 7 = rowColumnMul rows_assocBAC cols_right2 :=
  (rowColumnMul_eq _ _ _ _ rows_assocBAC_data cols_right2_data).symm

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn577
