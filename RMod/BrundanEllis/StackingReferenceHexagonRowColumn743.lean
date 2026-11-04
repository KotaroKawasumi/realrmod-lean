import RMod.BrundanEllis.StackingReferenceHexagonAtoms743
import RMod.BrundanEllis.StackingReferenceHexagonMiddle7
import RMod.BrundanEllis.StackingReferenceRowColumnCheck

/-! Verified row and column lists. Each subsequent scalar product traverses
these lists directly, without repeated lookup into the original matrices. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn743
open Superfusion

private def rows_outerABCData : List (List ℤ) := [decodeIntegerRow 16 3 1 21523354,
    decodeIntegerRow 16 3 1 21523388,
    decodeIntegerRow 16 3 1 21523386,
    decodeIntegerRow 16 3 1 21523372,
    decodeIntegerRow 16 3 1 21522874,
    decodeIntegerRow 16 3 1 21525628,
    decodeIntegerRow 16 3 1 21525466,
    decodeIntegerRow 16 3 1 21524332,
    decodeIntegerRow 16 3 1 21562726,
    decodeIntegerRow 16 3 1 21339652,
    decodeIntegerRow 16 3 1 21352774,
    decodeIntegerRow 16 3 1 21444628,
    decodeIntegerRow 16 3 1 24712006,
    decodeIntegerRow 16 3 1 6643012,
    decodeIntegerRow 16 3 1 7705894,
    decodeIntegerRow 16 3 1 15146068]

def rows_outerABC (r : LeftIndex 4 3 7) : List ℤ := rows_outerABCData.getD (leftPosition 4 3 7 r) []

private theorem rows_outerABC_eq_0_0_0 : (tripleIndices 4 1 4).map ((HexagonAtoms743.outerABC) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_outerABC ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_0_1 : (tripleIndices 4 1 4).map ((HexagonAtoms743.outerABC) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_outerABC ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_0_2 : (tripleIndices 4 1 4).map ((HexagonAtoms743.outerABC) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_outerABC ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_0_3 : (tripleIndices 4 1 4).map ((HexagonAtoms743.outerABC) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_outerABC ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_0 : (tripleIndices 4 1 4).map ((HexagonAtoms743.outerABC) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_outerABC ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_1 : (tripleIndices 4 1 4).map ((HexagonAtoms743.outerABC) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_outerABC ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_2 : (tripleIndices 4 1 4).map ((HexagonAtoms743.outerABC) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_outerABC ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_3 : (tripleIndices 4 1 4).map ((HexagonAtoms743.outerABC) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_outerABC ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_2_0_0 : (tripleIndices 4 1 4).map ((HexagonAtoms743.outerABC) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_outerABC ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_2_0_1 : (tripleIndices 4 1 4).map ((HexagonAtoms743.outerABC) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_outerABC ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_2_0_2 : (tripleIndices 4 1 4).map ((HexagonAtoms743.outerABC) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_outerABC ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_2_0_3 : (tripleIndices 4 1 4).map ((HexagonAtoms743.outerABC) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_outerABC ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_3_0_0 : (tripleIndices 4 1 4).map ((HexagonAtoms743.outerABC) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_outerABC ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_3_0_1 : (tripleIndices 4 1 4).map ((HexagonAtoms743.outerABC) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_outerABC ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_3_0_2 : (tripleIndices 4 1 4).map ((HexagonAtoms743.outerABC) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_outerABC ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_3_0_3 : (tripleIndices 4 1 4).map ((HexagonAtoms743.outerABC) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_outerABC ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_outerABC_data (r : LeftIndex 4 3 7) : (tripleIndices 4 1 4).map ((HexagonAtoms743.outerABC) r) = rows_outerABC r := by
  fin_cases r
  · exact rows_outerABC_eq_0_0_0
  · exact rows_outerABC_eq_0_0_1
  · exact rows_outerABC_eq_0_0_2
  · exact rows_outerABC_eq_0_0_3
  · exact rows_outerABC_eq_1_0_0
  · exact rows_outerABC_eq_1_0_1
  · exact rows_outerABC_eq_1_0_2
  · exact rows_outerABC_eq_1_0_3
  · exact rows_outerABC_eq_2_0_0
  · exact rows_outerABC_eq_2_0_1
  · exact rows_outerABC_eq_2_0_2
  · exact rows_outerABC_eq_2_0_3
  · exact rows_outerABC_eq_3_0_0
  · exact rows_outerABC_eq_3_0_1
  · exact rows_outerABC_eq_3_0_2
  · exact rows_outerABC_eq_3_0_3

private def rows_inverseACBData : List (List ℤ) := [decodeIntegerRow 16 3 1 21562700,
    decodeIntegerRow 16 3 1 21339664,
    decodeIntegerRow 16 3 1 21352780,
    decodeIntegerRow 16 3 1 21444656,
    decodeIntegerRow 16 3 1 7706380,
    decodeIntegerRow 16 3 1 27898384,
    decodeIntegerRow 16 3 1 24709900,
    decodeIntegerRow 16 3 1 36402736,
    decodeIntegerRow 16 3 1 21693952,
    decodeIntegerRow 16 3 1 21444600,
    decodeIntegerRow 16 3 1 21483968,
    decodeIntegerRow 16 3 1 21339640,
    decodeIntegerRow 16 3 1 18332608,
    decodeIntegerRow 16 3 1 36404680,
    decodeIntegerRow 16 3 1 35341312,
    decodeIntegerRow 16 3 1 27902920]

def rows_inverseACB (r : LeftIndex 7 3 4) : List ℤ := rows_inverseACBData.getD (leftPosition 7 3 4 r) []

private theorem rows_inverseACB_eq_0_0_0 : (tripleIndices 4 1 4).map ((HexagonAtoms743.inverseACB) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_1 : (tripleIndices 4 1 4).map ((HexagonAtoms743.inverseACB) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_2 : (tripleIndices 4 1 4).map ((HexagonAtoms743.inverseACB) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_3 : (tripleIndices 4 1 4).map ((HexagonAtoms743.inverseACB) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_0 : (tripleIndices 4 1 4).map ((HexagonAtoms743.inverseACB) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = rows_inverseACB ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_1 : (tripleIndices 4 1 4).map ((HexagonAtoms743.inverseACB) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = rows_inverseACB ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_2 : (tripleIndices 4 1 4).map ((HexagonAtoms743.inverseACB) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = rows_inverseACB ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_3 : (tripleIndices 4 1 4).map ((HexagonAtoms743.inverseACB) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = rows_inverseACB ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_0 : (tripleIndices 4 1 4).map ((HexagonAtoms743.inverseACB) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_1 : (tripleIndices 4 1 4).map ((HexagonAtoms743.inverseACB) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_2 : (tripleIndices 4 1 4).map ((HexagonAtoms743.inverseACB) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_3 : (tripleIndices 4 1 4).map ((HexagonAtoms743.inverseACB) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_0 : (tripleIndices 4 1 4).map ((HexagonAtoms743.inverseACB) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = rows_inverseACB ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_1 : (tripleIndices 4 1 4).map ((HexagonAtoms743.inverseACB) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = rows_inverseACB ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_2 : (tripleIndices 4 1 4).map ((HexagonAtoms743.inverseACB) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = rows_inverseACB ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_3 : (tripleIndices 4 1 4).map ((HexagonAtoms743.inverseACB) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = rows_inverseACB ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_inverseACB_data (r : LeftIndex 7 3 4) : (tripleIndices 4 1 4).map ((HexagonAtoms743.inverseACB) r) = rows_inverseACB r := by
  fin_cases r
  · exact rows_inverseACB_eq_0_0_0
  · exact rows_inverseACB_eq_0_0_1
  · exact rows_inverseACB_eq_0_0_2
  · exact rows_inverseACB_eq_0_0_3
  · exact rows_inverseACB_eq_0_1_0
  · exact rows_inverseACB_eq_0_1_1
  · exact rows_inverseACB_eq_0_1_2
  · exact rows_inverseACB_eq_0_1_3
  · exact rows_inverseACB_eq_1_0_0
  · exact rows_inverseACB_eq_1_0_1
  · exact rows_inverseACB_eq_1_0_2
  · exact rows_inverseACB_eq_1_0_3
  · exact rows_inverseACB_eq_1_1_0
  · exact rows_inverseACB_eq_1_1_1
  · exact rows_inverseACB_eq_1_1_2
  · exact rows_inverseACB_eq_1_1_3

private def rows_assocBCAData : List (List ℤ) := [decodeIntegerRow 16 3 1 21516808,
    decodeIntegerRow 16 3 1 21503650,
    decodeIntegerRow 16 3 1 21464312,
    decodeIntegerRow 16 3 1 21346210,
    decodeIntegerRow 16 3 1 16740472,
    decodeIntegerRow 16 3 1 35872510,
    decodeIntegerRow 16 3 1 20992648,
    decodeIntegerRow 16 3 1 23119870,
    decodeIntegerRow 16 3 1 21582410,
    decodeIntegerRow 16 3 1 21346216,
    decodeIntegerRow 16 3 1 21529930,
    decodeIntegerRow 16 3 1 21503704,
    decodeIntegerRow 16 3 1 22055530,
    decodeIntegerRow 16 3 1 23115496,
    decodeIntegerRow 16 3 1 26306410,
    decodeIntegerRow 16 3 1 35872024]

def rows_assocBCA (r : RightIndex 4 3 7) : List ℤ := rows_assocBCAData.getD (rightPosition 4 3 7 r) []

private theorem rows_assocBCA_eq_0_0_0 : (tripleIndices 4 1 4).map ((HexagonAtoms743.assocBCA) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = rows_assocBCA ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_1 : (tripleIndices 4 1 4).map ((HexagonAtoms743.assocBCA) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = rows_assocBCA ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_2 : (tripleIndices 4 1 4).map ((HexagonAtoms743.assocBCA) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = rows_assocBCA ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_3 : (tripleIndices 4 1 4).map ((HexagonAtoms743.assocBCA) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = rows_assocBCA ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_0 : (tripleIndices 4 1 4).map ((HexagonAtoms743.assocBCA) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = rows_assocBCA ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_1 : (tripleIndices 4 1 4).map ((HexagonAtoms743.assocBCA) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = rows_assocBCA ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_2 : (tripleIndices 4 1 4).map ((HexagonAtoms743.assocBCA) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = rows_assocBCA ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_3 : (tripleIndices 4 1 4).map ((HexagonAtoms743.assocBCA) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = rows_assocBCA ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_0 : (tripleIndices 4 1 4).map ((HexagonAtoms743.assocBCA) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = rows_assocBCA ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_1 : (tripleIndices 4 1 4).map ((HexagonAtoms743.assocBCA) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = rows_assocBCA ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_2 : (tripleIndices 4 1 4).map ((HexagonAtoms743.assocBCA) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = rows_assocBCA ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_3 : (tripleIndices 4 1 4).map ((HexagonAtoms743.assocBCA) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = rows_assocBCA ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_0 : (tripleIndices 4 1 4).map ((HexagonAtoms743.assocBCA) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = rows_assocBCA ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_1 : (tripleIndices 4 1 4).map ((HexagonAtoms743.assocBCA) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = rows_assocBCA ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_2 : (tripleIndices 4 1 4).map ((HexagonAtoms743.assocBCA) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = rows_assocBCA ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_3 : (tripleIndices 4 1 4).map ((HexagonAtoms743.assocBCA) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = rows_assocBCA ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocBCA_data (r : RightIndex 4 3 7) : (tripleIndices 4 1 4).map ((HexagonAtoms743.assocBCA) r) = rows_assocBCA r := by
  fin_cases r
  · exact rows_assocBCA_eq_0_0_0
  · exact rows_assocBCA_eq_0_0_1
  · exact rows_assocBCA_eq_0_0_2
  · exact rows_assocBCA_eq_0_0_3
  · exact rows_assocBCA_eq_0_1_0
  · exact rows_assocBCA_eq_0_1_1
  · exact rows_assocBCA_eq_0_1_2
  · exact rows_assocBCA_eq_0_1_3
  · exact rows_assocBCA_eq_1_0_0
  · exact rows_assocBCA_eq_1_0_1
  · exact rows_assocBCA_eq_1_0_2
  · exact rows_assocBCA_eq_1_0_3
  · exact rows_assocBCA_eq_1_1_0
  · exact rows_assocBCA_eq_1_1_1
  · exact rows_assocBCA_eq_1_1_2
  · exact rows_assocBCA_eq_1_1_3

private def rows_assocCABData : List (List ℤ) := [decodeIntegerRow 16 3 1 21523282,
    decodeIntegerRow 16 3 1 21523118,
    decodeIntegerRow 16 3 1 21522658,
    decodeIntegerRow 16 3 1 21521182,
    decodeIntegerRow 16 3 1 21523444,
    decodeIntegerRow 16 3 1 21523604,
    decodeIntegerRow 16 3 1 21524116,
    decodeIntegerRow 16 3 1 21525556,
    decodeIntegerRow 16 3 1 7115404,
    decodeIntegerRow 16 3 1 26483476,
    decodeIntegerRow 16 3 1 19922476,
    decodeIntegerRow 16 3 1 22074484,
    decodeIntegerRow 16 3 1 35813218,
    decodeIntegerRow 16 3 1 16917538,
    decodeIntegerRow 16 3 1 23111122,
    decodeIntegerRow 16 3 1 21011602]

def rows_assocCAB (r : RightIndex 3 7 4) : List ℤ := rows_assocCABData.getD (rightPosition 3 7 4 r) []

private theorem rows_assocCAB_eq_0_0_0 : (tripleIndices 2 2 4).map ((HexagonAtoms743.assocCAB) ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4))) = rows_assocCAB ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_1 : (tripleIndices 2 2 4).map ((HexagonAtoms743.assocCAB) ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4))) = rows_assocCAB ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_2 : (tripleIndices 2 2 4).map ((HexagonAtoms743.assocCAB) ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4))) = rows_assocCAB ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_3 : (tripleIndices 2 2 4).map ((HexagonAtoms743.assocCAB) ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4))) = rows_assocCAB ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_0 : (tripleIndices 2 2 4).map ((HexagonAtoms743.assocCAB) ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4))) = rows_assocCAB ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_1 : (tripleIndices 2 2 4).map ((HexagonAtoms743.assocCAB) ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4))) = rows_assocCAB ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_2 : (tripleIndices 2 2 4).map ((HexagonAtoms743.assocCAB) ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4))) = rows_assocCAB ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_3 : (tripleIndices 2 2 4).map ((HexagonAtoms743.assocCAB) ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4))) = rows_assocCAB ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_2_0 : (tripleIndices 2 2 4).map ((HexagonAtoms743.assocCAB) ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4))) = rows_assocCAB ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_2_1 : (tripleIndices 2 2 4).map ((HexagonAtoms743.assocCAB) ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4))) = rows_assocCAB ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_2_2 : (tripleIndices 2 2 4).map ((HexagonAtoms743.assocCAB) ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4))) = rows_assocCAB ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_2_3 : (tripleIndices 2 2 4).map ((HexagonAtoms743.assocCAB) ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4))) = rows_assocCAB ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_3_0 : (tripleIndices 2 2 4).map ((HexagonAtoms743.assocCAB) ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4))) = rows_assocCAB ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_3_1 : (tripleIndices 2 2 4).map ((HexagonAtoms743.assocCAB) ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4))) = rows_assocCAB ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_3_2 : (tripleIndices 2 2 4).map ((HexagonAtoms743.assocCAB) ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4))) = rows_assocCAB ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_3_3 : (tripleIndices 2 2 4).map ((HexagonAtoms743.assocCAB) ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4))) = rows_assocCAB ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocCAB_data (r : RightIndex 3 7 4) : (tripleIndices 2 2 4).map ((HexagonAtoms743.assocCAB) r) = rows_assocCAB r := by
  fin_cases r
  · exact rows_assocCAB_eq_0_0_0
  · exact rows_assocCAB_eq_0_0_1
  · exact rows_assocCAB_eq_0_0_2
  · exact rows_assocCAB_eq_0_0_3
  · exact rows_assocCAB_eq_0_1_0
  · exact rows_assocCAB_eq_0_1_1
  · exact rows_assocCAB_eq_0_1_2
  · exact rows_assocCAB_eq_0_1_3
  · exact rows_assocCAB_eq_0_2_0
  · exact rows_assocCAB_eq_0_2_1
  · exact rows_assocCAB_eq_0_2_2
  · exact rows_assocCAB_eq_0_2_3
  · exact rows_assocCAB_eq_0_3_0
  · exact rows_assocCAB_eq_0_3_1
  · exact rows_assocCAB_eq_0_3_2
  · exact rows_assocCAB_eq_0_3_3

private def cols_assocABCData : List (List ℤ) := [decodeIntegerRow 16 3 1 23176786,
    decodeIntegerRow 16 3 1 21877906,
    decodeIntegerRow 16 3 1 35879554,
    decodeIntegerRow 16 3 1 26288834,
    decodeIntegerRow 16 3 1 19987978,
    decodeIntegerRow 16 3 1 20814538,
    decodeIntegerRow 16 3 1 7180282,
    decodeIntegerRow 16 3 1 16718522,
    decodeIntegerRow 16 3 1 21877402,
    decodeIntegerRow 16 3 1 23176678,
    decodeIntegerRow 16 3 1 26284458,
    decodeIntegerRow 16 3 1 35878102,
    decodeIntegerRow 16 3 1 20815006,
    decodeIntegerRow 16 3 1 19988194,
    decodeIntegerRow 16 3 1 16722894,
    decodeIntegerRow 16 3 1 7181746]

def cols_assocABC (r : LeftIndex 7 4 3) : List ℤ := cols_assocABCData.getD (leftPosition 7 4 3 r) []

private theorem cols_assocABC_eq_0_0_0 : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms743.assocABC) j ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4))) = cols_assocABC ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_1 : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms743.assocABC) j ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4))) = cols_assocABC ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_2 : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms743.assocABC) j ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4))) = cols_assocABC ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_3 : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms743.assocABC) j ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4))) = cols_assocABC ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_0 : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms743.assocABC) j ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4))) = cols_assocABC ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_1 : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms743.assocABC) j ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4))) = cols_assocABC ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_2 : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms743.assocABC) j ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4))) = cols_assocABC ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_3 : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms743.assocABC) j ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4))) = cols_assocABC ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_2_0 : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms743.assocABC) j ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4))) = cols_assocABC ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_2_1 : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms743.assocABC) j ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4))) = cols_assocABC ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_2_2 : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms743.assocABC) j ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4))) = cols_assocABC ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_2_3 : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms743.assocABC) j ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4))) = cols_assocABC ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_3_0 : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms743.assocABC) j ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4))) = cols_assocABC ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_3_1 : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms743.assocABC) j ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4))) = cols_assocABC ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_3_2 : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms743.assocABC) j ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4))) = cols_assocABC ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_3_3 : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms743.assocABC) j ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4))) = cols_assocABC ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_assocABC_data (r : LeftIndex 7 4 3) : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms743.assocABC) j r) = cols_assocABC r := by
  fin_cases r
  · exact cols_assocABC_eq_0_0_0
  · exact cols_assocABC_eq_0_0_1
  · exact cols_assocABC_eq_0_0_2
  · exact cols_assocABC_eq_0_0_3
  · exact cols_assocABC_eq_0_1_0
  · exact cols_assocABC_eq_0_1_1
  · exact cols_assocABC_eq_0_1_2
  · exact cols_assocABC_eq_0_1_3
  · exact cols_assocABC_eq_0_2_0
  · exact cols_assocABC_eq_0_2_1
  · exact cols_assocABC_eq_0_2_2
  · exact cols_assocABC_eq_0_2_3
  · exact cols_assocABC_eq_0_3_0
  · exact cols_assocABC_eq_0_3_1
  · exact cols_assocABC_eq_0_3_2
  · exact cols_assocABC_eq_0_3_3

private def cols_right0Data : List (List ℤ) := [decodeIntegerRow 16 3 1 23176786,
    decodeIntegerRow 16 3 1 21877906,
    decodeIntegerRow 16 3 1 35879554,
    decodeIntegerRow 16 3 1 26288834,
    decodeIntegerRow 16 3 1 19987978,
    decodeIntegerRow 16 3 1 20814538,
    decodeIntegerRow 16 3 1 7180282,
    decodeIntegerRow 16 3 1 16718522,
    decodeIntegerRow 16 3 1 21877402,
    decodeIntegerRow 16 3 1 23176678,
    decodeIntegerRow 16 3 1 26284458,
    decodeIntegerRow 16 3 1 35878102,
    decodeIntegerRow 16 3 1 20815006,
    decodeIntegerRow 16 3 1 19988194,
    decodeIntegerRow 16 3 1 16722894,
    decodeIntegerRow 16 3 1 7181746]

def cols_right0 (r : LeftIndex 7 4 3) : List ℤ := cols_right0Data.getD (leftPosition 7 4 3 r) []

private theorem cols_right0_eq_0_0_0 : (tripleIndices 4 1 4).map (fun j => (right0Middle7 4 3) j ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4))) = cols_right0 ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_1 : (tripleIndices 4 1 4).map (fun j => (right0Middle7 4 3) j ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4))) = cols_right0 ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_2 : (tripleIndices 4 1 4).map (fun j => (right0Middle7 4 3) j ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4))) = cols_right0 ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_3 : (tripleIndices 4 1 4).map (fun j => (right0Middle7 4 3) j ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4))) = cols_right0 ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_0 : (tripleIndices 4 1 4).map (fun j => (right0Middle7 4 3) j ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4))) = cols_right0 ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_1 : (tripleIndices 4 1 4).map (fun j => (right0Middle7 4 3) j ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4))) = cols_right0 ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_2 : (tripleIndices 4 1 4).map (fun j => (right0Middle7 4 3) j ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4))) = cols_right0 ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_3 : (tripleIndices 4 1 4).map (fun j => (right0Middle7 4 3) j ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4))) = cols_right0 ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_2_0 : (tripleIndices 4 1 4).map (fun j => (right0Middle7 4 3) j ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4))) = cols_right0 ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_2_1 : (tripleIndices 4 1 4).map (fun j => (right0Middle7 4 3) j ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4))) = cols_right0 ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_2_2 : (tripleIndices 4 1 4).map (fun j => (right0Middle7 4 3) j ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4))) = cols_right0 ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_2_3 : (tripleIndices 4 1 4).map (fun j => (right0Middle7 4 3) j ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4))) = cols_right0 ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_3_0 : (tripleIndices 4 1 4).map (fun j => (right0Middle7 4 3) j ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4))) = cols_right0 ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_3_1 : (tripleIndices 4 1 4).map (fun j => (right0Middle7 4 3) j ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4))) = cols_right0 ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_3_2 : (tripleIndices 4 1 4).map (fun j => (right0Middle7 4 3) j ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4))) = cols_right0 ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_3_3 : (tripleIndices 4 1 4).map (fun j => (right0Middle7 4 3) j ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4))) = cols_right0 ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right0_data (r : LeftIndex 7 4 3) : (tripleIndices 4 1 4).map (fun j => (right0Middle7 4 3) j r) = cols_right0 r := by
  fin_cases r
  · exact cols_right0_eq_0_0_0
  · exact cols_right0_eq_0_0_1
  · exact cols_right0_eq_0_0_2
  · exact cols_right0_eq_0_0_3
  · exact cols_right0_eq_0_1_0
  · exact cols_right0_eq_0_1_1
  · exact cols_right0_eq_0_1_2
  · exact cols_right0_eq_0_1_3
  · exact cols_right0_eq_0_2_0
  · exact cols_right0_eq_0_2_1
  · exact cols_right0_eq_0_2_2
  · exact cols_right0_eq_0_2_3
  · exact cols_right0_eq_0_3_0
  · exact cols_right0_eq_0_3_1
  · exact cols_right0_eq_0_3_2
  · exact cols_right0_eq_0_3_3

private def cols_left0Data : List (List ℤ) := [decodeIntegerRow 16 3 1 6471928,
    decodeIntegerRow 16 3 1 24793032,
    decodeIntegerRow 16 3 1 15187512,
    decodeIntegerRow 16 3 1 7890568,
    decodeIntegerRow 16 3 1 36233596,
    decodeIntegerRow 16 3 1 18411204,
    decodeIntegerRow 16 3 1 27937884,
    decodeIntegerRow 16 3 1 35523556,
    decodeIntegerRow 16 3 1 24788444,
    decodeIntegerRow 16 3 1 6472924,
    decodeIntegerRow 16 3 1 7888636,
    decodeIntegerRow 16 3 1 15183356,
    decodeIntegerRow 16 3 1 18415688,
    decodeIntegerRow 16 3 1 36232648,
    decodeIntegerRow 16 3 1 35525512,
    decodeIntegerRow 16 3 1 27942152]

def cols_left0 (r : LeftIndex 7 4 3) : List ℤ := cols_left0Data.getD (leftPosition 7 4 3 r) []

private theorem cols_left0_eq_0_0_0 : (tripleIndices 4 1 4).map (fun j => (left0Middle7 4 3) j ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4))) = cols_left0 ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_1 : (tripleIndices 4 1 4).map (fun j => (left0Middle7 4 3) j ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4))) = cols_left0 ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_2 : (tripleIndices 4 1 4).map (fun j => (left0Middle7 4 3) j ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4))) = cols_left0 ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_3 : (tripleIndices 4 1 4).map (fun j => (left0Middle7 4 3) j ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4))) = cols_left0 ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_0 : (tripleIndices 4 1 4).map (fun j => (left0Middle7 4 3) j ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4))) = cols_left0 ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_1 : (tripleIndices 4 1 4).map (fun j => (left0Middle7 4 3) j ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4))) = cols_left0 ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_2 : (tripleIndices 4 1 4).map (fun j => (left0Middle7 4 3) j ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4))) = cols_left0 ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_3 : (tripleIndices 4 1 4).map (fun j => (left0Middle7 4 3) j ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4))) = cols_left0 ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_2_0 : (tripleIndices 4 1 4).map (fun j => (left0Middle7 4 3) j ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4))) = cols_left0 ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_2_1 : (tripleIndices 4 1 4).map (fun j => (left0Middle7 4 3) j ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4))) = cols_left0 ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_2_2 : (tripleIndices 4 1 4).map (fun j => (left0Middle7 4 3) j ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4))) = cols_left0 ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_2_3 : (tripleIndices 4 1 4).map (fun j => (left0Middle7 4 3) j ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4))) = cols_left0 ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_3_0 : (tripleIndices 4 1 4).map (fun j => (left0Middle7 4 3) j ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4))) = cols_left0 ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_3_1 : (tripleIndices 4 1 4).map (fun j => (left0Middle7 4 3) j ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4))) = cols_left0 ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_3_2 : (tripleIndices 4 1 4).map (fun j => (left0Middle7 4 3) j ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4))) = cols_left0 ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_3_3 : (tripleIndices 4 1 4).map (fun j => (left0Middle7 4 3) j ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4))) = cols_left0 ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_left0_data (r : LeftIndex 7 4 3) : (tripleIndices 4 1 4).map (fun j => (left0Middle7 4 3) j r) = cols_left0 r := by
  fin_cases r
  · exact cols_left0_eq_0_0_0
  · exact cols_left0_eq_0_0_1
  · exact cols_left0_eq_0_0_2
  · exact cols_left0_eq_0_0_3
  · exact cols_left0_eq_0_1_0
  · exact cols_left0_eq_0_1_1
  · exact cols_left0_eq_0_1_2
  · exact cols_left0_eq_0_1_3
  · exact cols_left0_eq_0_2_0
  · exact cols_left0_eq_0_2_1
  · exact cols_left0_eq_0_2_2
  · exact cols_left0_eq_0_2_3
  · exact cols_left0_eq_0_3_0
  · exact cols_left0_eq_0_3_1
  · exact cols_left0_eq_0_3_2
  · exact cols_left0_eq_0_3_3

private def cols_right2Data : List (List ℤ) := [decodeIntegerRow 16 5 2 137817382564,
    decodeIntegerRow 16 5 2 66528320372,
    decodeIntegerRow 16 5 2 90942382852,
    decodeIntegerRow 16 5 2 136840820564,
    decodeIntegerRow 16 5 2 14770507564,
    decodeIntegerRow 16 5 2 86059570372,
    decodeIntegerRow 16 5 2 61645507852,
    decodeIntegerRow 16 5 2 15747070564,
    decodeIntegerRow 16 5 2 76390977812,
    decodeIntegerRow 16 5 2 76270482812,
    decodeIntegerRow 16 5 2 76278357812,
    decodeIntegerRow 16 5 2 76195662812,
    decodeIntegerRow 16 5 2 76390662812,
    decodeIntegerRow 16 5 2 76270532812,
    decodeIntegerRow 16 5 2 76278282812,
    decodeIntegerRow 16 5 2 76195352812]

def cols_right2 (r : LeftIndex 7 4 3) : List ℤ := cols_right2Data.getD (leftPosition 7 4 3 r) []

private theorem cols_right2_eq_0_0_0 : (tripleIndices 2 2 4).map (fun j => (right2Middle7 4 3) j ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4))) = cols_right2 ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_1 : (tripleIndices 2 2 4).map (fun j => (right2Middle7 4 3) j ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4))) = cols_right2 ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_2 : (tripleIndices 2 2 4).map (fun j => (right2Middle7 4 3) j ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4))) = cols_right2 ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_3 : (tripleIndices 2 2 4).map (fun j => (right2Middle7 4 3) j ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4))) = cols_right2 ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_0 : (tripleIndices 2 2 4).map (fun j => (right2Middle7 4 3) j ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4))) = cols_right2 ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_1 : (tripleIndices 2 2 4).map (fun j => (right2Middle7 4 3) j ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4))) = cols_right2 ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_2 : (tripleIndices 2 2 4).map (fun j => (right2Middle7 4 3) j ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4))) = cols_right2 ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_3 : (tripleIndices 2 2 4).map (fun j => (right2Middle7 4 3) j ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4))) = cols_right2 ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_2_0 : (tripleIndices 2 2 4).map (fun j => (right2Middle7 4 3) j ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4))) = cols_right2 ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_2_1 : (tripleIndices 2 2 4).map (fun j => (right2Middle7 4 3) j ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4))) = cols_right2 ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_2_2 : (tripleIndices 2 2 4).map (fun j => (right2Middle7 4 3) j ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4))) = cols_right2 ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_2_3 : (tripleIndices 2 2 4).map (fun j => (right2Middle7 4 3) j ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4))) = cols_right2 ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_3_0 : (tripleIndices 2 2 4).map (fun j => (right2Middle7 4 3) j ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4))) = cols_right2 ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_3_1 : (tripleIndices 2 2 4).map (fun j => (right2Middle7 4 3) j ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4))) = cols_right2 ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_3_2 : (tripleIndices 2 2 4).map (fun j => (right2Middle7 4 3) j ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4))) = cols_right2 ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_3_3 : (tripleIndices 2 2 4).map (fun j => (right2Middle7 4 3) j ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4))) = cols_right2 ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right2_data (r : LeftIndex 7 4 3) : (tripleIndices 2 2 4).map (fun j => (right2Middle7 4 3) j r) = cols_right2 r := by
  fin_cases r
  · exact cols_right2_eq_0_0_0
  · exact cols_right2_eq_0_0_1
  · exact cols_right2_eq_0_0_2
  · exact cols_right2_eq_0_0_3
  · exact cols_right2_eq_0_1_0
  · exact cols_right2_eq_0_1_1
  · exact cols_right2_eq_0_1_2
  · exact cols_right2_eq_0_1_3
  · exact cols_right2_eq_0_2_0
  · exact cols_right2_eq_0_2_1
  · exact cols_right2_eq_0_2_2
  · exact cols_right2_eq_0_2_3
  · exact cols_right2_eq_0_3_0
  · exact cols_right2_eq_0_3_1
  · exact cols_right2_eq_0_3_2
  · exact cols_right2_eq_0_3_3

theorem product0_eq : HexagonAtoms743.outerABC * HexagonAtoms743.assocABC = rowColumnMul rows_outerABC cols_assocABC :=
  (rowColumnMul_eq _ _ _ _ rows_outerABC_data cols_assocABC_data).symm

theorem product1_eq : HexagonAtoms743.assocBAC * HexagonAtoms743.innerABC = HexagonAtoms743.assocBAC :=
  Matrix.mul_one (m := Fin 2 × Fin 2 × Fin 4) (n := Fin 1 × Fin 4 × Fin 4) _

theorem product2_eq : HexagonAtoms743.innerRightABC * HexagonAtoms743.assocABC = HexagonAtoms743.assocABC :=
  Matrix.one_mul (m := Fin 4 × Fin 1 × Fin 4) (n := Fin 1 × Fin 4 × Fin 4) _

theorem product3_eq : HexagonAtoms743.inverseACB * right0Middle7 4 3 = rowColumnMul rows_inverseACB cols_right0 :=
  (rowColumnMul_eq _ _ _ _ rows_inverseACB_data cols_right0_data).symm

theorem product4_eq : HexagonAtoms743.innerACB * right1Middle7 4 3 = right1Middle7 4 3 :=
  Matrix.one_mul (m := Fin 2 × Fin 2 × Fin 4) (n := Fin 1 × Fin 4 × Fin 4) _

theorem product5_eq : HexagonAtoms743.assocBCA * left0Middle7 4 3 = rowColumnMul rows_assocBCA cols_left0 :=
  (rowColumnMul_eq _ _ _ _ rows_assocBCA_data cols_left0_data).symm

theorem product6_eq : HexagonAtoms743.innerRightBAC * left1Middle7 4 3 = left1Middle7 4 3 :=
  Matrix.one_mul (m := Fin 2 × Fin 2 × Fin 4) (n := Fin 1 × Fin 4 × Fin 4) _

theorem product7_eq : HexagonAtoms743.assocCAB * right2Middle7 4 3 = rowColumnMul rows_assocCAB cols_right2 :=
  (rowColumnMul_eq _ _ _ _ rows_assocCAB_data cols_right2_data).symm

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn743
