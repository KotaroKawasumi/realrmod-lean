import RMod.BrundanEllis.StackingReferenceHexagonAtoms756
import RMod.BrundanEllis.StackingReferenceHexagonMiddle7
import RMod.BrundanEllis.StackingReferenceRowColumnCheck

/-! Verified row and column lists. Each subsequent scalar product traverses
these lists directly, without repeated lookup into the original matrices. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn756
open Superfusion

private def rows_outerABCData : List (List ℤ) := [decodeIntegerRow 16 3 1 21523361,
    decodeIntegerRow 16 3 1 21523363,
    decodeIntegerRow 16 3 1 21523369,
    decodeIntegerRow 16 3 1 21523387,
    decodeIntegerRow 16 3 1 21523441,
    decodeIntegerRow 16 3 1 21523603,
    decodeIntegerRow 16 3 1 21524089,
    decodeIntegerRow 16 3 1 21525547,
    decodeIntegerRow 16 3 1 21516799,
    decodeIntegerRow 16 3 1 21503677,
    decodeIntegerRow 16 3 1 21464311,
    decodeIntegerRow 16 3 1 21346213,
    decodeIntegerRow 16 3 1 20991919,
    decodeIntegerRow 16 3 1 19929037,
    decodeIntegerRow 16 3 1 16740391,
    decodeIntegerRow 16 3 1 7174453]

def rows_outerABC (r : LeftIndex 5 6 7) : List ℤ := rows_outerABCData.getD (leftPosition 5 6 7 r) []

private theorem rows_outerABC_eq_0_0_0 : (tripleIndices 2 2 4).map ((HexagonAtoms756.outerABC) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = rows_outerABC ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_0_1 : (tripleIndices 2 2 4).map ((HexagonAtoms756.outerABC) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = rows_outerABC ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_0_2 : (tripleIndices 2 2 4).map ((HexagonAtoms756.outerABC) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = rows_outerABC ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_0_3 : (tripleIndices 2 2 4).map ((HexagonAtoms756.outerABC) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = rows_outerABC ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_1_0 : (tripleIndices 2 2 4).map ((HexagonAtoms756.outerABC) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = rows_outerABC ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_1_1 : (tripleIndices 2 2 4).map ((HexagonAtoms756.outerABC) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = rows_outerABC ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_1_2 : (tripleIndices 2 2 4).map ((HexagonAtoms756.outerABC) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = rows_outerABC ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_1_3 : (tripleIndices 2 2 4).map ((HexagonAtoms756.outerABC) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = rows_outerABC ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_0 : (tripleIndices 2 2 4).map ((HexagonAtoms756.outerABC) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = rows_outerABC ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_1 : (tripleIndices 2 2 4).map ((HexagonAtoms756.outerABC) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = rows_outerABC ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_2 : (tripleIndices 2 2 4).map ((HexagonAtoms756.outerABC) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = rows_outerABC ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_3 : (tripleIndices 2 2 4).map ((HexagonAtoms756.outerABC) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = rows_outerABC ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_1_0 : (tripleIndices 2 2 4).map ((HexagonAtoms756.outerABC) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = rows_outerABC ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_1_1 : (tripleIndices 2 2 4).map ((HexagonAtoms756.outerABC) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = rows_outerABC ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_1_2 : (tripleIndices 2 2 4).map ((HexagonAtoms756.outerABC) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = rows_outerABC ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_1_3 : (tripleIndices 2 2 4).map ((HexagonAtoms756.outerABC) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = rows_outerABC ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_outerABC_data (r : LeftIndex 5 6 7) : (tripleIndices 2 2 4).map ((HexagonAtoms756.outerABC) r) = rows_outerABC r := by
  fin_cases r
  · exact rows_outerABC_eq_0_0_0
  · exact rows_outerABC_eq_0_0_1
  · exact rows_outerABC_eq_0_0_2
  · exact rows_outerABC_eq_0_0_3
  · exact rows_outerABC_eq_0_1_0
  · exact rows_outerABC_eq_0_1_1
  · exact rows_outerABC_eq_0_1_2
  · exact rows_outerABC_eq_0_1_3
  · exact rows_outerABC_eq_1_0_0
  · exact rows_outerABC_eq_1_0_1
  · exact rows_outerABC_eq_1_0_2
  · exact rows_outerABC_eq_1_0_3
  · exact rows_outerABC_eq_1_1_0
  · exact rows_outerABC_eq_1_1_1
  · exact rows_outerABC_eq_1_1_2
  · exact rows_outerABC_eq_1_1_3

private def rows_inverseACBData : List (List ℤ) := [decodeIntegerRow 16 3 1 28082080,
    decodeIntegerRow 16 3 1 6720800,
    decodeIntegerRow 16 3 1 35379680,
    decodeIntegerRow 16 3 1 18503200,
    decodeIntegerRow 16 3 1 27719200,
    decodeIntegerRow 16 3 1 6565280,
    decodeIntegerRow 16 3 1 35301920,
    decodeIntegerRow 16 3 1 18166240,
    decodeIntegerRow 16 3 1 6722688,
    decodeIntegerRow 16 3 1 14960080,
    decodeIntegerRow 16 3 1 18507400,
    decodeIntegerRow 16 3 1 7666016,
    decodeIntegerRow 16 3 1 36483440,
    decodeIntegerRow 16 3 1 27714688,
    decodeIntegerRow 16 3 1 24884704,
    decodeIntegerRow 16 3 1 35301000]

def rows_inverseACB (r : LeftIndex 7 6 5) : List ℤ := rows_inverseACBData.getD (leftPosition 7 6 5 r) []

private theorem rows_inverseACB_eq_0_0_0 : (tripleIndices 2 2 4).map ((HexagonAtoms756.inverseACB) ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4))) = rows_inverseACB ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_1 : (tripleIndices 2 2 4).map ((HexagonAtoms756.inverseACB) ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4))) = rows_inverseACB ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_2 : (tripleIndices 2 2 4).map ((HexagonAtoms756.inverseACB) ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4))) = rows_inverseACB ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_3 : (tripleIndices 2 2 4).map ((HexagonAtoms756.inverseACB) ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4))) = rows_inverseACB ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_0 : (tripleIndices 2 2 4).map ((HexagonAtoms756.inverseACB) ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4))) = rows_inverseACB ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_1 : (tripleIndices 2 2 4).map ((HexagonAtoms756.inverseACB) ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4))) = rows_inverseACB ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_2 : (tripleIndices 2 2 4).map ((HexagonAtoms756.inverseACB) ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4))) = rows_inverseACB ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_3 : (tripleIndices 2 2 4).map ((HexagonAtoms756.inverseACB) ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4))) = rows_inverseACB ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_2_0 : (tripleIndices 2 2 4).map ((HexagonAtoms756.inverseACB) ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4))) = rows_inverseACB ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_2_1 : (tripleIndices 2 2 4).map ((HexagonAtoms756.inverseACB) ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4))) = rows_inverseACB ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_2_2 : (tripleIndices 2 2 4).map ((HexagonAtoms756.inverseACB) ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4))) = rows_inverseACB ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_2_3 : (tripleIndices 2 2 4).map ((HexagonAtoms756.inverseACB) ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4))) = rows_inverseACB ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_3_0 : (tripleIndices 2 2 4).map ((HexagonAtoms756.inverseACB) ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4))) = rows_inverseACB ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_3_1 : (tripleIndices 2 2 4).map ((HexagonAtoms756.inverseACB) ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4))) = rows_inverseACB ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_3_2 : (tripleIndices 2 2 4).map ((HexagonAtoms756.inverseACB) ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4))) = rows_inverseACB ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_3_3 : (tripleIndices 2 2 4).map ((HexagonAtoms756.inverseACB) ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4))) = rows_inverseACB ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_inverseACB_data (r : LeftIndex 7 6 5) : (tripleIndices 2 2 4).map ((HexagonAtoms756.inverseACB) r) = rows_inverseACB r := by
  fin_cases r
  · exact rows_inverseACB_eq_0_0_0
  · exact rows_inverseACB_eq_0_0_1
  · exact rows_inverseACB_eq_0_0_2
  · exact rows_inverseACB_eq_0_0_3
  · exact rows_inverseACB_eq_0_1_0
  · exact rows_inverseACB_eq_0_1_1
  · exact rows_inverseACB_eq_0_1_2
  · exact rows_inverseACB_eq_0_1_3
  · exact rows_inverseACB_eq_0_2_0
  · exact rows_inverseACB_eq_0_2_1
  · exact rows_inverseACB_eq_0_2_2
  · exact rows_inverseACB_eq_0_2_3
  · exact rows_inverseACB_eq_0_3_0
  · exact rows_inverseACB_eq_0_3_1
  · exact rows_inverseACB_eq_0_3_2
  · exact rows_inverseACB_eq_0_3_3

private def rows_innerACBData : List (List ℤ) := [decodeIntegerRow 16 3 1 21444656,
    decodeIntegerRow 16 3 1 21707080,
    decodeIntegerRow 16 3 1 21352780,
    decodeIntegerRow 16 3 1 21562752,
    decodeIntegerRow 16 3 1 24709900,
    decodeIntegerRow 16 3 1 7705408,
    decodeIntegerRow 16 3 1 6643984,
    decodeIntegerRow 16 3 1 27902920,
    decodeIntegerRow 16 3 1 21707056,
    decodeIntegerRow 16 3 1 21602120,
    decodeIntegerRow 16 3 1 21562700,
    decodeIntegerRow 16 3 1 21693952,
    decodeIntegerRow 16 3 1 7706380,
    decodeIntegerRow 16 3 1 18332608,
    decodeIntegerRow 16 3 1 27898384,
    decodeIntegerRow 16 3 1 36404680]

def rows_innerACB (r : LeftIndex 6 7 5) : List ℤ := rows_innerACBData.getD (leftPosition 6 7 5 r) []

private theorem rows_innerACB_eq_0_0_0 : (tripleIndices 1 4 4).map ((HexagonAtoms756.innerACB) ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4))) = rows_innerACB ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_0_1 : (tripleIndices 1 4 4).map ((HexagonAtoms756.innerACB) ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4))) = rows_innerACB ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_0_2 : (tripleIndices 1 4 4).map ((HexagonAtoms756.innerACB) ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4))) = rows_innerACB ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_0_3 : (tripleIndices 1 4 4).map ((HexagonAtoms756.innerACB) ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4))) = rows_innerACB ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_1_0 : (tripleIndices 1 4 4).map ((HexagonAtoms756.innerACB) ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4))) = rows_innerACB ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_1_1 : (tripleIndices 1 4 4).map ((HexagonAtoms756.innerACB) ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4))) = rows_innerACB ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_1_2 : (tripleIndices 1 4 4).map ((HexagonAtoms756.innerACB) ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4))) = rows_innerACB ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_1_3 : (tripleIndices 1 4 4).map ((HexagonAtoms756.innerACB) ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4))) = rows_innerACB ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_2_0 : (tripleIndices 1 4 4).map ((HexagonAtoms756.innerACB) ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4))) = rows_innerACB ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_2_1 : (tripleIndices 1 4 4).map ((HexagonAtoms756.innerACB) ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4))) = rows_innerACB ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_2_2 : (tripleIndices 1 4 4).map ((HexagonAtoms756.innerACB) ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4))) = rows_innerACB ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_2_3 : (tripleIndices 1 4 4).map ((HexagonAtoms756.innerACB) ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4))) = rows_innerACB ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_3_0 : (tripleIndices 1 4 4).map ((HexagonAtoms756.innerACB) ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4))) = rows_innerACB ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_3_1 : (tripleIndices 1 4 4).map ((HexagonAtoms756.innerACB) ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4))) = rows_innerACB ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_3_2 : (tripleIndices 1 4 4).map ((HexagonAtoms756.innerACB) ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4))) = rows_innerACB ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_3_3 : (tripleIndices 1 4 4).map ((HexagonAtoms756.innerACB) ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4))) = rows_innerACB ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_innerACB_data (r : LeftIndex 6 7 5) : (tripleIndices 1 4 4).map ((HexagonAtoms756.innerACB) r) = rows_innerACB r := by
  fin_cases r
  · exact rows_innerACB_eq_0_0_0
  · exact rows_innerACB_eq_0_0_1
  · exact rows_innerACB_eq_0_0_2
  · exact rows_innerACB_eq_0_0_3
  · exact rows_innerACB_eq_0_1_0
  · exact rows_innerACB_eq_0_1_1
  · exact rows_innerACB_eq_0_1_2
  · exact rows_innerACB_eq_0_1_3
  · exact rows_innerACB_eq_0_2_0
  · exact rows_innerACB_eq_0_2_1
  · exact rows_innerACB_eq_0_2_2
  · exact rows_innerACB_eq_0_2_3
  · exact rows_innerACB_eq_0_3_0
  · exact rows_innerACB_eq_0_3_1
  · exact rows_innerACB_eq_0_3_2
  · exact rows_innerACB_eq_0_3_3

private def rows_assocBCAData : List (List ℤ) := [decodeIntegerRow 16 3 1 21523361,
    decodeIntegerRow 16 3 1 21523363,
    decodeIntegerRow 16 3 1 21523369,
    decodeIntegerRow 16 3 1 21523387,
    decodeIntegerRow 16 3 1 22054801,
    decodeIntegerRow 16 3 1 23117683,
    decodeIntegerRow 16 3 1 26306329,
    decodeIntegerRow 16 3 1 35872267,
    decodeIntegerRow 16 3 1 21523441,
    decodeIntegerRow 16 3 1 21523603,
    decodeIntegerRow 16 3 1 21524089,
    decodeIntegerRow 16 3 1 21525547,
    decodeIntegerRow 16 3 1 21529921,
    decodeIntegerRow 16 3 1 21543043,
    decodeIntegerRow 16 3 1 21582409,
    decodeIntegerRow 16 3 1 21700507]

def rows_assocBCA (r : RightIndex 5 6 7) : List ℤ := rows_assocBCAData.getD (rightPosition 5 6 7 r) []

private theorem rows_assocBCA_eq_0_0_0 : (tripleIndices 2 2 4).map ((HexagonAtoms756.assocBCA) ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4))) = rows_assocBCA ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_1 : (tripleIndices 2 2 4).map ((HexagonAtoms756.assocBCA) ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4))) = rows_assocBCA ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_2 : (tripleIndices 2 2 4).map ((HexagonAtoms756.assocBCA) ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4))) = rows_assocBCA ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_3 : (tripleIndices 2 2 4).map ((HexagonAtoms756.assocBCA) ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4))) = rows_assocBCA ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_0 : (tripleIndices 2 2 4).map ((HexagonAtoms756.assocBCA) ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4))) = rows_assocBCA ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_1 : (tripleIndices 2 2 4).map ((HexagonAtoms756.assocBCA) ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4))) = rows_assocBCA ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_2 : (tripleIndices 2 2 4).map ((HexagonAtoms756.assocBCA) ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4))) = rows_assocBCA ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_3 : (tripleIndices 2 2 4).map ((HexagonAtoms756.assocBCA) ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4))) = rows_assocBCA ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_2_0 : (tripleIndices 2 2 4).map ((HexagonAtoms756.assocBCA) ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4))) = rows_assocBCA ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_2_1 : (tripleIndices 2 2 4).map ((HexagonAtoms756.assocBCA) ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4))) = rows_assocBCA ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_2_2 : (tripleIndices 2 2 4).map ((HexagonAtoms756.assocBCA) ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4))) = rows_assocBCA ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_2_3 : (tripleIndices 2 2 4).map ((HexagonAtoms756.assocBCA) ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4))) = rows_assocBCA ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_3_0 : (tripleIndices 2 2 4).map ((HexagonAtoms756.assocBCA) ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4))) = rows_assocBCA ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_3_1 : (tripleIndices 2 2 4).map ((HexagonAtoms756.assocBCA) ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4))) = rows_assocBCA ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_3_2 : (tripleIndices 2 2 4).map ((HexagonAtoms756.assocBCA) ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4))) = rows_assocBCA ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_3_3 : (tripleIndices 2 2 4).map ((HexagonAtoms756.assocBCA) ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4))) = rows_assocBCA ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocBCA_data (r : RightIndex 5 6 7) : (tripleIndices 2 2 4).map ((HexagonAtoms756.assocBCA) r) = rows_assocBCA r := by
  fin_cases r
  · exact rows_assocBCA_eq_0_0_0
  · exact rows_assocBCA_eq_0_0_1
  · exact rows_assocBCA_eq_0_0_2
  · exact rows_assocBCA_eq_0_0_3
  · exact rows_assocBCA_eq_0_1_0
  · exact rows_assocBCA_eq_0_1_1
  · exact rows_assocBCA_eq_0_1_2
  · exact rows_assocBCA_eq_0_1_3
  · exact rows_assocBCA_eq_0_2_0
  · exact rows_assocBCA_eq_0_2_1
  · exact rows_assocBCA_eq_0_2_2
  · exact rows_assocBCA_eq_0_2_3
  · exact rows_assocBCA_eq_0_3_0
  · exact rows_assocBCA_eq_0_3_1
  · exact rows_assocBCA_eq_0_3_2
  · exact rows_assocBCA_eq_0_3_3

private def rows_innerRightBACData : List (List ℤ) := [decodeIntegerRow 16 3 1 18334688,
    decodeIntegerRow 16 3 1 35340820,
    decodeIntegerRow 16 3 1 36403720,
    decodeIntegerRow 16 3 1 15146096,
    decodeIntegerRow 16 3 1 21604360,
    decodeIntegerRow 16 3 1 21340624,
    decodeIntegerRow 16 3 1 21694432,
    decodeIntegerRow 16 3 1 21486100,
    decodeIntegerRow 16 3 1 21708040,
    decodeIntegerRow 16 3 1 21599824,
    decodeIntegerRow 16 3 1 21564832,
    decodeIntegerRow 16 3 1 21693460,
    decodeIntegerRow 16 3 1 7705888,
    decodeIntegerRow 16 3 1 18334740,
    decodeIntegerRow 16 3 1 27900680,
    decodeIntegerRow 16 3 1 36403696]

def rows_innerRightBAC (r : RightIndex 5 6 7) : List ℤ := rows_innerRightBACData.getD (rightPosition 5 6 7 r) []

private theorem rows_innerRightBAC_eq_0_0_0 : (tripleIndices 1 4 4).map ((HexagonAtoms756.innerRightBAC) ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4))) = rows_innerRightBAC ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_0_1 : (tripleIndices 1 4 4).map ((HexagonAtoms756.innerRightBAC) ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4))) = rows_innerRightBAC ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_0_2 : (tripleIndices 1 4 4).map ((HexagonAtoms756.innerRightBAC) ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4))) = rows_innerRightBAC ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_0_3 : (tripleIndices 1 4 4).map ((HexagonAtoms756.innerRightBAC) ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4))) = rows_innerRightBAC ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_1_0 : (tripleIndices 1 4 4).map ((HexagonAtoms756.innerRightBAC) ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4))) = rows_innerRightBAC ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_1_1 : (tripleIndices 1 4 4).map ((HexagonAtoms756.innerRightBAC) ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4))) = rows_innerRightBAC ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_1_2 : (tripleIndices 1 4 4).map ((HexagonAtoms756.innerRightBAC) ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4))) = rows_innerRightBAC ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_1_3 : (tripleIndices 1 4 4).map ((HexagonAtoms756.innerRightBAC) ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4))) = rows_innerRightBAC ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_2_0 : (tripleIndices 1 4 4).map ((HexagonAtoms756.innerRightBAC) ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4))) = rows_innerRightBAC ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_2_1 : (tripleIndices 1 4 4).map ((HexagonAtoms756.innerRightBAC) ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4))) = rows_innerRightBAC ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_2_2 : (tripleIndices 1 4 4).map ((HexagonAtoms756.innerRightBAC) ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4))) = rows_innerRightBAC ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_2_3 : (tripleIndices 1 4 4).map ((HexagonAtoms756.innerRightBAC) ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4))) = rows_innerRightBAC ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_3_0 : (tripleIndices 1 4 4).map ((HexagonAtoms756.innerRightBAC) ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4))) = rows_innerRightBAC ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_3_1 : (tripleIndices 1 4 4).map ((HexagonAtoms756.innerRightBAC) ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4))) = rows_innerRightBAC ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_3_2 : (tripleIndices 1 4 4).map ((HexagonAtoms756.innerRightBAC) ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4))) = rows_innerRightBAC ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_3_3 : (tripleIndices 1 4 4).map ((HexagonAtoms756.innerRightBAC) ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4))) = rows_innerRightBAC ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_innerRightBAC_data (r : RightIndex 5 6 7) : (tripleIndices 1 4 4).map ((HexagonAtoms756.innerRightBAC) r) = rows_innerRightBAC r := by
  fin_cases r
  · exact rows_innerRightBAC_eq_0_0_0
  · exact rows_innerRightBAC_eq_0_0_1
  · exact rows_innerRightBAC_eq_0_0_2
  · exact rows_innerRightBAC_eq_0_0_3
  · exact rows_innerRightBAC_eq_0_1_0
  · exact rows_innerRightBAC_eq_0_1_1
  · exact rows_innerRightBAC_eq_0_1_2
  · exact rows_innerRightBAC_eq_0_1_3
  · exact rows_innerRightBAC_eq_0_2_0
  · exact rows_innerRightBAC_eq_0_2_1
  · exact rows_innerRightBAC_eq_0_2_2
  · exact rows_innerRightBAC_eq_0_2_3
  · exact rows_innerRightBAC_eq_0_3_0
  · exact rows_innerRightBAC_eq_0_3_1
  · exact rows_innerRightBAC_eq_0_3_2
  · exact rows_innerRightBAC_eq_0_3_3

private def rows_assocCABData : List (List ℤ) := [decodeIntegerRow 16 3 1 7174462,
    decodeIntegerRow 16 3 1 16740364,
    decodeIntegerRow 16 3 1 23117682,
    decodeIntegerRow 16 3 1 22054804,
    decodeIntegerRow 16 3 1 19929036,
    decodeIntegerRow 16 3 1 22054798,
    decodeIntegerRow 16 3 1 7174444,
    decodeIntegerRow 16 3 1 26306302,
    decodeIntegerRow 16 3 1 21580222,
    decodeIntegerRow 16 3 1 21345484,
    decodeIntegerRow 16 3 1 21517042,
    decodeIntegerRow 16 3 1 21543124,
    decodeIntegerRow 16 3 1 21530164,
    decodeIntegerRow 16 3 1 21542962,
    decodeIntegerRow 16 3 1 21584596,
    decodeIntegerRow 16 3 1 21699778]

def rows_assocCAB (r : RightIndex 6 7 5) : List ℤ := rows_assocCABData.getD (rightPosition 6 7 5 r) []

private theorem rows_assocCAB_eq_0_0_0 : (tripleIndices 1 4 4).map ((HexagonAtoms756.assocCAB) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_1 : (tripleIndices 1 4 4).map ((HexagonAtoms756.assocCAB) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_2 : (tripleIndices 1 4 4).map ((HexagonAtoms756.assocCAB) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_3 : (tripleIndices 1 4 4).map ((HexagonAtoms756.assocCAB) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_0 : (tripleIndices 1 4 4).map ((HexagonAtoms756.assocCAB) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = rows_assocCAB ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_1 : (tripleIndices 1 4 4).map ((HexagonAtoms756.assocCAB) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = rows_assocCAB ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_2 : (tripleIndices 1 4 4).map ((HexagonAtoms756.assocCAB) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = rows_assocCAB ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_3 : (tripleIndices 1 4 4).map ((HexagonAtoms756.assocCAB) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = rows_assocCAB ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_0 : (tripleIndices 1 4 4).map ((HexagonAtoms756.assocCAB) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_1 : (tripleIndices 1 4 4).map ((HexagonAtoms756.assocCAB) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_2 : (tripleIndices 1 4 4).map ((HexagonAtoms756.assocCAB) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_3 : (tripleIndices 1 4 4).map ((HexagonAtoms756.assocCAB) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_0 : (tripleIndices 1 4 4).map ((HexagonAtoms756.assocCAB) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = rows_assocCAB ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_1 : (tripleIndices 1 4 4).map ((HexagonAtoms756.assocCAB) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = rows_assocCAB ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_2 : (tripleIndices 1 4 4).map ((HexagonAtoms756.assocCAB) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = rows_assocCAB ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_3 : (tripleIndices 1 4 4).map ((HexagonAtoms756.assocCAB) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = rows_assocCAB ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocCAB_data (r : RightIndex 6 7 5) : (tripleIndices 1 4 4).map ((HexagonAtoms756.assocCAB) r) = rows_assocCAB r := by
  fin_cases r
  · exact rows_assocCAB_eq_0_0_0
  · exact rows_assocCAB_eq_0_0_1
  · exact rows_assocCAB_eq_0_0_2
  · exact rows_assocCAB_eq_0_0_3
  · exact rows_assocCAB_eq_0_1_0
  · exact rows_assocCAB_eq_0_1_1
  · exact rows_assocCAB_eq_0_1_2
  · exact rows_assocCAB_eq_0_1_3
  · exact rows_assocCAB_eq_1_0_0
  · exact rows_assocCAB_eq_1_0_1
  · exact rows_assocCAB_eq_1_0_2
  · exact rows_assocCAB_eq_1_0_3
  · exact rows_assocCAB_eq_1_1_0
  · exact rows_assocCAB_eq_1_1_1
  · exact rows_assocCAB_eq_1_1_2
  · exact rows_assocCAB_eq_1_1_3

private def cols_assocABCData : List (List ℤ) := [decodeIntegerRow 16 3 1 21484022,
    decodeIntegerRow 16 3 1 21693958,
    decodeIntegerRow 16 3 1 21707074,
    decodeIntegerRow 16 3 1 21444654,
    decodeIntegerRow 16 3 1 27898546,
    decodeIntegerRow 16 3 1 6642526,
    decodeIntegerRow 16 3 1 35341798,
    decodeIntegerRow 16 3 1 18336982,
    decodeIntegerRow 16 3 1 21339658,
    decodeIntegerRow 16 3 1 21444602,
    decodeIntegerRow 16 3 1 21483966,
    decodeIntegerRow 16 3 1 21352786,
    decodeIntegerRow 16 3 1 35339854,
    decodeIntegerRow 16 3 1 24714274,
    decodeIntegerRow 16 3 1 15143962,
    decodeIntegerRow 16 3 1 6643498]

def cols_assocABC (r : LeftIndex 7 5 6) : List ℤ := cols_assocABCData.getD (leftPosition 7 5 6 r) []

private theorem cols_assocABC_eq_0_0_0 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms756.assocABC) j ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = cols_assocABC ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_1 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms756.assocABC) j ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = cols_assocABC ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_2 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms756.assocABC) j ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = cols_assocABC ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_3 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms756.assocABC) j ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = cols_assocABC ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_0 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms756.assocABC) j ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = cols_assocABC ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_1 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms756.assocABC) j ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = cols_assocABC ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_2 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms756.assocABC) j ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = cols_assocABC ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_3 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms756.assocABC) j ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = cols_assocABC ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_0 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms756.assocABC) j ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = cols_assocABC ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_1 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms756.assocABC) j ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = cols_assocABC ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_2 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms756.assocABC) j ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = cols_assocABC ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_3 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms756.assocABC) j ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = cols_assocABC ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_1_0 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms756.assocABC) j ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = cols_assocABC ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_1_1 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms756.assocABC) j ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = cols_assocABC ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_1_2 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms756.assocABC) j ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = cols_assocABC ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_1_3 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms756.assocABC) j ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = cols_assocABC ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_assocABC_data (r : LeftIndex 7 5 6) : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms756.assocABC) j r) = cols_assocABC r := by
  fin_cases r
  · exact cols_assocABC_eq_0_0_0
  · exact cols_assocABC_eq_0_0_1
  · exact cols_assocABC_eq_0_0_2
  · exact cols_assocABC_eq_0_0_3
  · exact cols_assocABC_eq_0_1_0
  · exact cols_assocABC_eq_0_1_1
  · exact cols_assocABC_eq_0_1_2
  · exact cols_assocABC_eq_0_1_3
  · exact cols_assocABC_eq_1_0_0
  · exact cols_assocABC_eq_1_0_1
  · exact cols_assocABC_eq_1_0_2
  · exact cols_assocABC_eq_1_0_3
  · exact cols_assocABC_eq_1_1_0
  · exact cols_assocABC_eq_1_1_1
  · exact cols_assocABC_eq_1_1_2
  · exact cols_assocABC_eq_1_1_3

private def cols_right0Data : List (List ℤ) := [decodeIntegerRow 16 3 1 21484022,
    decodeIntegerRow 16 3 1 21693958,
    decodeIntegerRow 16 3 1 21707074,
    decodeIntegerRow 16 3 1 21444654,
    decodeIntegerRow 16 3 1 27898546,
    decodeIntegerRow 16 3 1 6642526,
    decodeIntegerRow 16 3 1 35341798,
    decodeIntegerRow 16 3 1 18336982,
    decodeIntegerRow 16 3 1 21339658,
    decodeIntegerRow 16 3 1 21444602,
    decodeIntegerRow 16 3 1 21483966,
    decodeIntegerRow 16 3 1 21352786,
    decodeIntegerRow 16 3 1 35339854,
    decodeIntegerRow 16 3 1 24714274,
    decodeIntegerRow 16 3 1 15143962,
    decodeIntegerRow 16 3 1 6643498]

def cols_right0 (r : LeftIndex 7 5 6) : List ℤ := cols_right0Data.getD (leftPosition 7 5 6 r) []

private theorem cols_right0_eq_0_0_0 : (tripleIndices 2 2 4).map (fun j => (right0Middle7 5 6) j ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = cols_right0 ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_1 : (tripleIndices 2 2 4).map (fun j => (right0Middle7 5 6) j ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = cols_right0 ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_2 : (tripleIndices 2 2 4).map (fun j => (right0Middle7 5 6) j ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = cols_right0 ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_3 : (tripleIndices 2 2 4).map (fun j => (right0Middle7 5 6) j ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = cols_right0 ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_0 : (tripleIndices 2 2 4).map (fun j => (right0Middle7 5 6) j ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = cols_right0 ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_1 : (tripleIndices 2 2 4).map (fun j => (right0Middle7 5 6) j ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = cols_right0 ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_2 : (tripleIndices 2 2 4).map (fun j => (right0Middle7 5 6) j ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = cols_right0 ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_3 : (tripleIndices 2 2 4).map (fun j => (right0Middle7 5 6) j ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = cols_right0 ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_0 : (tripleIndices 2 2 4).map (fun j => (right0Middle7 5 6) j ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = cols_right0 ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_1 : (tripleIndices 2 2 4).map (fun j => (right0Middle7 5 6) j ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = cols_right0 ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_2 : (tripleIndices 2 2 4).map (fun j => (right0Middle7 5 6) j ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = cols_right0 ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_3 : (tripleIndices 2 2 4).map (fun j => (right0Middle7 5 6) j ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = cols_right0 ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_0 : (tripleIndices 2 2 4).map (fun j => (right0Middle7 5 6) j ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = cols_right0 ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_1 : (tripleIndices 2 2 4).map (fun j => (right0Middle7 5 6) j ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = cols_right0 ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_2 : (tripleIndices 2 2 4).map (fun j => (right0Middle7 5 6) j ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = cols_right0 ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_3 : (tripleIndices 2 2 4).map (fun j => (right0Middle7 5 6) j ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = cols_right0 ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right0_data (r : LeftIndex 7 5 6) : (tripleIndices 2 2 4).map (fun j => (right0Middle7 5 6) j r) = cols_right0 r := by
  fin_cases r
  · exact cols_right0_eq_0_0_0
  · exact cols_right0_eq_0_0_1
  · exact cols_right0_eq_0_0_2
  · exact cols_right0_eq_0_0_3
  · exact cols_right0_eq_0_1_0
  · exact cols_right0_eq_0_1_1
  · exact cols_right0_eq_0_1_2
  · exact cols_right0_eq_0_1_3
  · exact cols_right0_eq_1_0_0
  · exact cols_right0_eq_1_0_1
  · exact cols_right0_eq_1_0_2
  · exact cols_right0_eq_1_0_3
  · exact cols_right0_eq_1_1_0
  · exact cols_right0_eq_1_1_1
  · exact cols_right0_eq_1_1_2
  · exact cols_right0_eq_1_1_3

private def cols_right1Data : List (List ℤ) := [decodeIntegerRow 16 5 2 137914295272,
    decodeIntegerRow 16 5 2 90957850560,
    decodeIntegerRow 16 5 2 86036288064,
    decodeIntegerRow 16 5 2 136742357752,
    decodeIntegerRow 16 5 2 66504728064,
    decodeIntegerRow 16 5 2 136939232872,
    decodeIntegerRow 16 5 2 137720545352,
    decodeIntegerRow 16 5 2 61661290560,
    decodeIntegerRow 16 5 2 90926915560,
    decodeIntegerRow 16 5 2 14867420352,
    decodeIntegerRow 16 5 2 136939282752,
    decodeIntegerRow 16 5 2 66505037560,
    decodeIntegerRow 16 5 2 136742407872,
    decodeIntegerRow 16 5 2 86035977560,
    decodeIntegerRow 16 5 2 61629725560,
    decodeIntegerRow 16 5 2 14673670272]

def cols_right1 (r : LeftIndex 7 5 6) : List ℤ := cols_right1Data.getD (leftPosition 7 5 6 r) []

private theorem cols_right1_eq_0_0_0 : (tripleIndices 1 4 4).map (fun j => (right1Middle7 5 6) j ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = cols_right1 ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_0_1 : (tripleIndices 1 4 4).map (fun j => (right1Middle7 5 6) j ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = cols_right1 ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_0_2 : (tripleIndices 1 4 4).map (fun j => (right1Middle7 5 6) j ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = cols_right1 ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_0_3 : (tripleIndices 1 4 4).map (fun j => (right1Middle7 5 6) j ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = cols_right1 ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_1_0 : (tripleIndices 1 4 4).map (fun j => (right1Middle7 5 6) j ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = cols_right1 ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_1_1 : (tripleIndices 1 4 4).map (fun j => (right1Middle7 5 6) j ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = cols_right1 ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_1_2 : (tripleIndices 1 4 4).map (fun j => (right1Middle7 5 6) j ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = cols_right1 ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_1_3 : (tripleIndices 1 4 4).map (fun j => (right1Middle7 5 6) j ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = cols_right1 ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_0_0 : (tripleIndices 1 4 4).map (fun j => (right1Middle7 5 6) j ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = cols_right1 ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_0_1 : (tripleIndices 1 4 4).map (fun j => (right1Middle7 5 6) j ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = cols_right1 ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_0_2 : (tripleIndices 1 4 4).map (fun j => (right1Middle7 5 6) j ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = cols_right1 ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_0_3 : (tripleIndices 1 4 4).map (fun j => (right1Middle7 5 6) j ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = cols_right1 ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_1_0 : (tripleIndices 1 4 4).map (fun j => (right1Middle7 5 6) j ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = cols_right1 ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_1_1 : (tripleIndices 1 4 4).map (fun j => (right1Middle7 5 6) j ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = cols_right1 ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_1_2 : (tripleIndices 1 4 4).map (fun j => (right1Middle7 5 6) j ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = cols_right1 ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_1_3 : (tripleIndices 1 4 4).map (fun j => (right1Middle7 5 6) j ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = cols_right1 ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right1_data (r : LeftIndex 7 5 6) : (tripleIndices 1 4 4).map (fun j => (right1Middle7 5 6) j r) = cols_right1 r := by
  fin_cases r
  · exact cols_right1_eq_0_0_0
  · exact cols_right1_eq_0_0_1
  · exact cols_right1_eq_0_0_2
  · exact cols_right1_eq_0_0_3
  · exact cols_right1_eq_0_1_0
  · exact cols_right1_eq_0_1_1
  · exact cols_right1_eq_0_1_2
  · exact cols_right1_eq_0_1_3
  · exact cols_right1_eq_1_0_0
  · exact cols_right1_eq_1_0_1
  · exact cols_right1_eq_1_0_2
  · exact cols_right1_eq_1_0_3
  · exact cols_right1_eq_1_1_0
  · exact cols_right1_eq_1_1_1
  · exact cols_right1_eq_1_1_2
  · exact cols_right1_eq_1_1_3

private def cols_left0Data : List (List ℤ) := [decodeIntegerRow 16 3 1 21562754,
    decodeIntegerRow 16 3 1 21352786,
    decodeIntegerRow 16 3 1 21339658,
    decodeIntegerRow 16 3 1 21602118,
    decodeIntegerRow 16 3 1 15143962,
    decodeIntegerRow 16 3 1 36403222,
    decodeIntegerRow 16 3 1 7706866,
    decodeIntegerRow 16 3 1 24714274,
    decodeIntegerRow 16 3 1 21707074,
    decodeIntegerRow 16 3 1 21602066,
    decodeIntegerRow 16 3 1 21562698,
    decodeIntegerRow 16 3 1 21693958,
    decodeIntegerRow 16 3 1 7704922,
    decodeIntegerRow 16 3 1 18336982,
    decodeIntegerRow 16 3 1 27898546,
    decodeIntegerRow 16 3 1 36404194]

def cols_left0 (r : LeftIndex 7 5 6) : List ℤ := cols_left0Data.getD (leftPosition 7 5 6 r) []

private theorem cols_left0_eq_0_0_0 : (tripleIndices 2 2 4).map (fun j => (left0Middle7 5 6) j ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = cols_left0 ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_1 : (tripleIndices 2 2 4).map (fun j => (left0Middle7 5 6) j ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = cols_left0 ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_2 : (tripleIndices 2 2 4).map (fun j => (left0Middle7 5 6) j ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = cols_left0 ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_3 : (tripleIndices 2 2 4).map (fun j => (left0Middle7 5 6) j ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = cols_left0 ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_0 : (tripleIndices 2 2 4).map (fun j => (left0Middle7 5 6) j ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = cols_left0 ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_1 : (tripleIndices 2 2 4).map (fun j => (left0Middle7 5 6) j ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = cols_left0 ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_2 : (tripleIndices 2 2 4).map (fun j => (left0Middle7 5 6) j ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = cols_left0 ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_3 : (tripleIndices 2 2 4).map (fun j => (left0Middle7 5 6) j ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = cols_left0 ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_0 : (tripleIndices 2 2 4).map (fun j => (left0Middle7 5 6) j ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = cols_left0 ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_1 : (tripleIndices 2 2 4).map (fun j => (left0Middle7 5 6) j ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = cols_left0 ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_2 : (tripleIndices 2 2 4).map (fun j => (left0Middle7 5 6) j ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = cols_left0 ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_3 : (tripleIndices 2 2 4).map (fun j => (left0Middle7 5 6) j ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = cols_left0 ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_0 : (tripleIndices 2 2 4).map (fun j => (left0Middle7 5 6) j ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = cols_left0 ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_1 : (tripleIndices 2 2 4).map (fun j => (left0Middle7 5 6) j ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = cols_left0 ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_2 : (tripleIndices 2 2 4).map (fun j => (left0Middle7 5 6) j ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = cols_left0 ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_3 : (tripleIndices 2 2 4).map (fun j => (left0Middle7 5 6) j ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = cols_left0 ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_left0_data (r : LeftIndex 7 5 6) : (tripleIndices 2 2 4).map (fun j => (left0Middle7 5 6) j r) = cols_left0 r := by
  fin_cases r
  · exact cols_left0_eq_0_0_0
  · exact cols_left0_eq_0_0_1
  · exact cols_left0_eq_0_0_2
  · exact cols_left0_eq_0_0_3
  · exact cols_left0_eq_0_1_0
  · exact cols_left0_eq_0_1_1
  · exact cols_left0_eq_0_1_2
  · exact cols_left0_eq_0_1_3
  · exact cols_left0_eq_1_0_0
  · exact cols_left0_eq_1_0_1
  · exact cols_left0_eq_1_0_2
  · exact cols_left0_eq_1_0_3
  · exact cols_left0_eq_1_1_0
  · exact cols_left0_eq_1_1_1
  · exact cols_left0_eq_1_1_2
  · exact cols_left0_eq_1_1_3

private def cols_left1Data : List (List ℤ) := [decodeIntegerRow 16 3 1 21523361,
    decodeIntegerRow 16 3 1 21523363,
    decodeIntegerRow 16 3 1 21523369,
    decodeIntegerRow 16 3 1 21523387,
    decodeIntegerRow 16 3 1 21529921,
    decodeIntegerRow 16 3 1 21543043,
    decodeIntegerRow 16 3 1 21582409,
    decodeIntegerRow 16 3 1 21700507,
    decodeIntegerRow 16 3 1 22054801,
    decodeIntegerRow 16 3 1 23117683,
    decodeIntegerRow 16 3 1 26306329,
    decodeIntegerRow 16 3 1 35872267,
    decodeIntegerRow 16 3 1 21523441,
    decodeIntegerRow 16 3 1 21523603,
    decodeIntegerRow 16 3 1 21524089,
    decodeIntegerRow 16 3 1 21525547]

def cols_left1 (r : LeftIndex 7 5 6) : List ℤ := cols_left1Data.getD (leftPosition 7 5 6 r) []

private theorem cols_left1_eq_0_0_0 : (tripleIndices 1 4 4).map (fun j => (left1Middle7 5 6) j ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = cols_left1 ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_0_1 : (tripleIndices 1 4 4).map (fun j => (left1Middle7 5 6) j ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = cols_left1 ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_0_2 : (tripleIndices 1 4 4).map (fun j => (left1Middle7 5 6) j ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = cols_left1 ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_0_3 : (tripleIndices 1 4 4).map (fun j => (left1Middle7 5 6) j ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = cols_left1 ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_1_0 : (tripleIndices 1 4 4).map (fun j => (left1Middle7 5 6) j ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = cols_left1 ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_1_1 : (tripleIndices 1 4 4).map (fun j => (left1Middle7 5 6) j ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = cols_left1 ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_1_2 : (tripleIndices 1 4 4).map (fun j => (left1Middle7 5 6) j ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = cols_left1 ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_1_3 : (tripleIndices 1 4 4).map (fun j => (left1Middle7 5 6) j ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = cols_left1 ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_0_0 : (tripleIndices 1 4 4).map (fun j => (left1Middle7 5 6) j ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = cols_left1 ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_0_1 : (tripleIndices 1 4 4).map (fun j => (left1Middle7 5 6) j ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = cols_left1 ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_0_2 : (tripleIndices 1 4 4).map (fun j => (left1Middle7 5 6) j ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = cols_left1 ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_0_3 : (tripleIndices 1 4 4).map (fun j => (left1Middle7 5 6) j ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = cols_left1 ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_1_0 : (tripleIndices 1 4 4).map (fun j => (left1Middle7 5 6) j ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = cols_left1 ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_1_1 : (tripleIndices 1 4 4).map (fun j => (left1Middle7 5 6) j ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = cols_left1 ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_1_2 : (tripleIndices 1 4 4).map (fun j => (left1Middle7 5 6) j ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = cols_left1 ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_1_3 : (tripleIndices 1 4 4).map (fun j => (left1Middle7 5 6) j ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = cols_left1 ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_left1_data (r : LeftIndex 7 5 6) : (tripleIndices 1 4 4).map (fun j => (left1Middle7 5 6) j r) = cols_left1 r := by
  fin_cases r
  · exact cols_left1_eq_0_0_0
  · exact cols_left1_eq_0_0_1
  · exact cols_left1_eq_0_0_2
  · exact cols_left1_eq_0_0_3
  · exact cols_left1_eq_0_1_0
  · exact cols_left1_eq_0_1_1
  · exact cols_left1_eq_0_1_2
  · exact cols_left1_eq_0_1_3
  · exact cols_left1_eq_1_0_0
  · exact cols_left1_eq_1_0_1
  · exact cols_left1_eq_1_0_2
  · exact cols_left1_eq_1_0_3
  · exact cols_left1_eq_1_1_0
  · exact cols_left1_eq_1_1_1
  · exact cols_left1_eq_1_1_2
  · exact cols_left1_eq_1_1_3

private def cols_right2Data : List (List ℤ) := [decodeIntegerRow 16 17 8 47229980349911958272,
    decodeIntegerRow 16 17 8 25677618550308680976,
    decodeIntegerRow 16 17 8 24251359313570186752,
    decodeIntegerRow 16 17 8 24325934959935596016,
    decodeIntegerRow 16 17 8 24409832562096681744,
    decodeIntegerRow 16 17 8 24325934959935596288,
    decodeIntegerRow 16 17 8 47229980349911962896,
    decodeIntegerRow 16 17 8 22983573325358266112,
    decodeIntegerRow 16 17 8 24330579813164940032,
    decodeIntegerRow 16 17 8 24330870113196995856,
    decodeIntegerRow 16 17 8 24330595993628134912,
    decodeIntegerRow 16 17 8 24330594989129754096,
    decodeIntegerRow 16 17 8 24330595882016015856,
    decodeIntegerRow 16 17 8 24330594989131090432,
    decodeIntegerRow 16 17 8 24330579806599521264,
    decodeIntegerRow 16 17 8 24330321762856073728]

def cols_right2 (r : LeftIndex 7 5 6) : List ℤ := cols_right2Data.getD (leftPosition 7 5 6 r) []

private theorem cols_right2_eq_0_0_0 : (tripleIndices 1 4 4).map (fun j => (right2Middle7 5 6) j ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = cols_right2 ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_1 : (tripleIndices 1 4 4).map (fun j => (right2Middle7 5 6) j ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = cols_right2 ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_2 : (tripleIndices 1 4 4).map (fun j => (right2Middle7 5 6) j ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = cols_right2 ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_3 : (tripleIndices 1 4 4).map (fun j => (right2Middle7 5 6) j ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = cols_right2 ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_0 : (tripleIndices 1 4 4).map (fun j => (right2Middle7 5 6) j ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = cols_right2 ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_1 : (tripleIndices 1 4 4).map (fun j => (right2Middle7 5 6) j ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = cols_right2 ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_2 : (tripleIndices 1 4 4).map (fun j => (right2Middle7 5 6) j ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = cols_right2 ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_3 : (tripleIndices 1 4 4).map (fun j => (right2Middle7 5 6) j ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = cols_right2 ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_0 : (tripleIndices 1 4 4).map (fun j => (right2Middle7 5 6) j ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = cols_right2 ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_1 : (tripleIndices 1 4 4).map (fun j => (right2Middle7 5 6) j ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = cols_right2 ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_2 : (tripleIndices 1 4 4).map (fun j => (right2Middle7 5 6) j ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = cols_right2 ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_3 : (tripleIndices 1 4 4).map (fun j => (right2Middle7 5 6) j ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = cols_right2 ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_0 : (tripleIndices 1 4 4).map (fun j => (right2Middle7 5 6) j ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = cols_right2 ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_1 : (tripleIndices 1 4 4).map (fun j => (right2Middle7 5 6) j ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = cols_right2 ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_2 : (tripleIndices 1 4 4).map (fun j => (right2Middle7 5 6) j ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = cols_right2 ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_3 : (tripleIndices 1 4 4).map (fun j => (right2Middle7 5 6) j ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = cols_right2 ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right2_data (r : LeftIndex 7 5 6) : (tripleIndices 1 4 4).map (fun j => (right2Middle7 5 6) j r) = cols_right2 r := by
  fin_cases r
  · exact cols_right2_eq_0_0_0
  · exact cols_right2_eq_0_0_1
  · exact cols_right2_eq_0_0_2
  · exact cols_right2_eq_0_0_3
  · exact cols_right2_eq_0_1_0
  · exact cols_right2_eq_0_1_1
  · exact cols_right2_eq_0_1_2
  · exact cols_right2_eq_0_1_3
  · exact cols_right2_eq_1_0_0
  · exact cols_right2_eq_1_0_1
  · exact cols_right2_eq_1_0_2
  · exact cols_right2_eq_1_0_3
  · exact cols_right2_eq_1_1_0
  · exact cols_right2_eq_1_1_1
  · exact cols_right2_eq_1_1_2
  · exact cols_right2_eq_1_1_3

theorem product0_eq : HexagonAtoms756.outerABC * HexagonAtoms756.assocABC = rowColumnMul rows_outerABC cols_assocABC :=
  (rowColumnMul_eq _ _ _ _ rows_outerABC_data cols_assocABC_data).symm

theorem product1_eq : HexagonAtoms756.assocBAC * HexagonAtoms756.innerABC = HexagonAtoms756.assocBAC :=
  Matrix.mul_one (m := Fin 1 × Fin 4 × Fin 4) (n := Fin 2 × Fin 2 × Fin 4) _

theorem product2_eq : HexagonAtoms756.innerRightABC * HexagonAtoms756.assocABC = HexagonAtoms756.assocABC :=
  Matrix.one_mul (m := Fin 2 × Fin 2 × Fin 4) (n := Fin 2 × Fin 2 × Fin 4) _

theorem product3_eq : HexagonAtoms756.inverseACB * right0Middle7 5 6 = rowColumnMul rows_inverseACB cols_right0 :=
  (rowColumnMul_eq _ _ _ _ rows_inverseACB_data cols_right0_data).symm

theorem product4_eq : HexagonAtoms756.innerACB * right1Middle7 5 6 = rowColumnMul rows_innerACB cols_right1 :=
  (rowColumnMul_eq _ _ _ _ rows_innerACB_data cols_right1_data).symm

theorem product5_eq : HexagonAtoms756.assocBCA * left0Middle7 5 6 = rowColumnMul rows_assocBCA cols_left0 :=
  (rowColumnMul_eq _ _ _ _ rows_assocBCA_data cols_left0_data).symm

theorem product6_eq : HexagonAtoms756.innerRightBAC * left1Middle7 5 6 = rowColumnMul rows_innerRightBAC cols_left1 :=
  (rowColumnMul_eq _ _ _ _ rows_innerRightBAC_data cols_left1_data).symm

theorem product7_eq : HexagonAtoms756.assocCAB * right2Middle7 5 6 = rowColumnMul rows_assocCAB cols_right2 :=
  (rowColumnMul_eq _ _ _ _ rows_assocCAB_data cols_right2_data).symm

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn756
