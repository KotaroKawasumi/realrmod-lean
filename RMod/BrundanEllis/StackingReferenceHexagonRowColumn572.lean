import RMod.BrundanEllis.StackingReferenceHexagonAtoms572
import RMod.BrundanEllis.StackingReferenceHexagonMiddle5
import RMod.BrundanEllis.StackingReferenceRowColumnCheck

/-! Verified row and column lists. Each subsequent scalar product traverses
these lists directly, without repeated lookup into the original matrices. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn572
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

def rows_outerABC (r : LeftIndex 7 2 5) : List ℤ := rows_outerABCData.getD (leftPosition 7 2 5 r) []

private theorem rows_outerABC_eq_0_0_0 : (tripleIndices 2 2 4).map ((HexagonAtoms572.outerABC) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = rows_outerABC ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_0_1 : (tripleIndices 2 2 4).map ((HexagonAtoms572.outerABC) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = rows_outerABC ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_0_2 : (tripleIndices 2 2 4).map ((HexagonAtoms572.outerABC) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = rows_outerABC ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_0_3 : (tripleIndices 2 2 4).map ((HexagonAtoms572.outerABC) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = rows_outerABC ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_1_0 : (tripleIndices 2 2 4).map ((HexagonAtoms572.outerABC) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = rows_outerABC ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_1_1 : (tripleIndices 2 2 4).map ((HexagonAtoms572.outerABC) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = rows_outerABC ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_1_2 : (tripleIndices 2 2 4).map ((HexagonAtoms572.outerABC) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = rows_outerABC ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_1_3 : (tripleIndices 2 2 4).map ((HexagonAtoms572.outerABC) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = rows_outerABC ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_0 : (tripleIndices 2 2 4).map ((HexagonAtoms572.outerABC) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = rows_outerABC ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_1 : (tripleIndices 2 2 4).map ((HexagonAtoms572.outerABC) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = rows_outerABC ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_2 : (tripleIndices 2 2 4).map ((HexagonAtoms572.outerABC) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = rows_outerABC ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_3 : (tripleIndices 2 2 4).map ((HexagonAtoms572.outerABC) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = rows_outerABC ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_1_0 : (tripleIndices 2 2 4).map ((HexagonAtoms572.outerABC) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = rows_outerABC ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_1_1 : (tripleIndices 2 2 4).map ((HexagonAtoms572.outerABC) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = rows_outerABC ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_1_2 : (tripleIndices 2 2 4).map ((HexagonAtoms572.outerABC) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = rows_outerABC ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_1_3 : (tripleIndices 2 2 4).map ((HexagonAtoms572.outerABC) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = rows_outerABC ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_outerABC_data (r : LeftIndex 7 2 5) : (tripleIndices 2 2 4).map ((HexagonAtoms572.outerABC) r) = rows_outerABC r := by
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

private def rows_inverseACBData : List (List ℤ) := [decodeIntegerRow 16 3 1 21050240,
    decodeIntegerRow 16 3 1 19754080,
    decodeIntegerRow 16 3 1 16746880,
    decodeIntegerRow 16 3 1 7155040,
    decodeIntegerRow 16 3 1 22114580,
    decodeIntegerRow 16 3 1 22938352,
    decodeIntegerRow 16 3 1 26312980,
    decodeIntegerRow 16 3 1 35852368,
    decodeIntegerRow 16 3 1 16733920,
    decodeIntegerRow 16 3 1 35852800,
    decodeIntegerRow 16 3 1 20933600,
    decodeIntegerRow 16 3 1 22942720,
    decodeIntegerRow 16 3 1 16747024,
    decodeIntegerRow 16 3 1 35892220,
    decodeIntegerRow 16 3 1 21051696,
    decodeIntegerRow 16 3 1 23297020]

def rows_inverseACB (r : LeftIndex 5 2 7) : List ℤ := rows_inverseACBData.getD (leftPosition 5 2 7 r) []

private theorem rows_inverseACB_eq_0_0_0 : (tripleIndices 2 2 4).map ((HexagonAtoms572.inverseACB) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_1 : (tripleIndices 2 2 4).map ((HexagonAtoms572.inverseACB) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_2 : (tripleIndices 2 2 4).map ((HexagonAtoms572.inverseACB) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_3 : (tripleIndices 2 2 4).map ((HexagonAtoms572.inverseACB) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_0 : (tripleIndices 2 2 4).map ((HexagonAtoms572.inverseACB) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_1 : (tripleIndices 2 2 4).map ((HexagonAtoms572.inverseACB) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_2 : (tripleIndices 2 2 4).map ((HexagonAtoms572.inverseACB) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_3 : (tripleIndices 2 2 4).map ((HexagonAtoms572.inverseACB) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_0 : (tripleIndices 2 2 4).map ((HexagonAtoms572.inverseACB) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_1 : (tripleIndices 2 2 4).map ((HexagonAtoms572.inverseACB) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_2 : (tripleIndices 2 2 4).map ((HexagonAtoms572.inverseACB) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_3 : (tripleIndices 2 2 4).map ((HexagonAtoms572.inverseACB) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_0 : (tripleIndices 2 2 4).map ((HexagonAtoms572.inverseACB) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_1 : (tripleIndices 2 2 4).map ((HexagonAtoms572.inverseACB) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_2 : (tripleIndices 2 2 4).map ((HexagonAtoms572.inverseACB) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_3 : (tripleIndices 2 2 4).map ((HexagonAtoms572.inverseACB) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_inverseACB_data (r : LeftIndex 5 2 7) : (tripleIndices 2 2 4).map ((HexagonAtoms572.inverseACB) r) = rows_inverseACB r := by
  fin_cases r
  · exact rows_inverseACB_eq_0_0_0
  · exact rows_inverseACB_eq_0_0_1
  · exact rows_inverseACB_eq_0_0_2
  · exact rows_inverseACB_eq_0_0_3
  · exact rows_inverseACB_eq_1_0_0
  · exact rows_inverseACB_eq_1_0_1
  · exact rows_inverseACB_eq_1_0_2
  · exact rows_inverseACB_eq_1_0_3
  · exact rows_inverseACB_eq_2_0_0
  · exact rows_inverseACB_eq_2_0_1
  · exact rows_inverseACB_eq_2_0_2
  · exact rows_inverseACB_eq_2_0_3
  · exact rows_inverseACB_eq_3_0_0
  · exact rows_inverseACB_eq_3_0_1
  · exact rows_inverseACB_eq_3_0_2
  · exact rows_inverseACB_eq_3_0_3

private def rows_assocBCAData : List (List ℤ) := [decodeIntegerRow 16 3 1 18520684,
    decodeIntegerRow 16 3 1 36363884,
    decodeIntegerRow 16 3 1 35420556,
    decodeIntegerRow 16 3 1 28073356,
    decodeIntegerRow 16 3 1 24893440,
    decodeIntegerRow 16 3 1 6604160,
    decodeIntegerRow 16 3 1 7783680,
    decodeIntegerRow 16 3 1 15314560,
    decodeIntegerRow 16 3 1 36443588,
    decodeIntegerRow 16 3 1 18148732,
    decodeIntegerRow 16 3 1 27727972,
    decodeIntegerRow 16 3 1 35261148,
    decodeIntegerRow 16 3 1 36364800,
    decodeIntegerRow 16 3 1 18516160,
    decodeIntegerRow 16 3 1 28069120,
    decodeIntegerRow 16 3 1 35418560]

def rows_assocBCA (r : RightIndex 7 2 5) : List ℤ := rows_assocBCAData.getD (rightPosition 7 2 5 r) []

private theorem rows_assocBCA_eq_0_0_0 : (tripleIndices 2 2 4).map ((HexagonAtoms572.assocBCA) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_assocBCA ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_1 : (tripleIndices 2 2 4).map ((HexagonAtoms572.assocBCA) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_assocBCA ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_2 : (tripleIndices 2 2 4).map ((HexagonAtoms572.assocBCA) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_assocBCA ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_3 : (tripleIndices 2 2 4).map ((HexagonAtoms572.assocBCA) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_assocBCA ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_0 : (tripleIndices 2 2 4).map ((HexagonAtoms572.assocBCA) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_assocBCA ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_1 : (tripleIndices 2 2 4).map ((HexagonAtoms572.assocBCA) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_assocBCA ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_2 : (tripleIndices 2 2 4).map ((HexagonAtoms572.assocBCA) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_assocBCA ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_3 : (tripleIndices 2 2 4).map ((HexagonAtoms572.assocBCA) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_assocBCA ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_0 : (tripleIndices 2 2 4).map ((HexagonAtoms572.assocBCA) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_assocBCA ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_1 : (tripleIndices 2 2 4).map ((HexagonAtoms572.assocBCA) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_assocBCA ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_2 : (tripleIndices 2 2 4).map ((HexagonAtoms572.assocBCA) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_assocBCA ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_3 : (tripleIndices 2 2 4).map ((HexagonAtoms572.assocBCA) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_assocBCA ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_0 : (tripleIndices 2 2 4).map ((HexagonAtoms572.assocBCA) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_assocBCA ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_1 : (tripleIndices 2 2 4).map ((HexagonAtoms572.assocBCA) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_assocBCA ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_2 : (tripleIndices 2 2 4).map ((HexagonAtoms572.assocBCA) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_assocBCA ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_3 : (tripleIndices 2 2 4).map ((HexagonAtoms572.assocBCA) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_assocBCA ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocBCA_data (r : RightIndex 7 2 5) : (tripleIndices 2 2 4).map ((HexagonAtoms572.assocBCA) r) = rows_assocBCA r := by
  fin_cases r
  · exact rows_assocBCA_eq_0_0_0
  · exact rows_assocBCA_eq_0_0_1
  · exact rows_assocBCA_eq_0_0_2
  · exact rows_assocBCA_eq_0_0_3
  · exact rows_assocBCA_eq_1_0_0
  · exact rows_assocBCA_eq_1_0_1
  · exact rows_assocBCA_eq_1_0_2
  · exact rows_assocBCA_eq_1_0_3
  · exact rows_assocBCA_eq_2_0_0
  · exact rows_assocBCA_eq_2_0_1
  · exact rows_assocBCA_eq_2_0_2
  · exact rows_assocBCA_eq_2_0_3
  · exact rows_assocBCA_eq_3_0_0
  · exact rows_assocBCA_eq_3_0_1
  · exact rows_assocBCA_eq_3_0_2
  · exact rows_assocBCA_eq_3_0_3

private def rows_assocCABData : List (List ℤ) := [decodeIntegerRow 16 3 1 36232648,
    decodeIntegerRow 16 3 1 18415688,
    decodeIntegerRow 16 3 1 27942152,
    decodeIntegerRow 16 3 1 35525512,
    decodeIntegerRow 16 3 1 15108836,
    decodeIntegerRow 16 3 1 35523556,
    decodeIntegerRow 16 3 1 6813124,
    decodeIntegerRow 16 3 1 18411204,
    decodeIntegerRow 16 3 1 15183356,
    decodeIntegerRow 16 3 1 35158084,
    decodeIntegerRow 16 3 1 6472924,
    decodeIntegerRow 16 3 1 18258276,
    decodeIntegerRow 16 3 1 36574792,
    decodeIntegerRow 16 3 1 18253688,
    decodeIntegerRow 16 3 1 27859208,
    decodeIntegerRow 16 3 1 35156152]

def rows_assocCAB (r : RightIndex 2 5 7) : List ℤ := rows_assocCABData.getD (rightPosition 2 5 7 r) []

private theorem rows_assocCAB_eq_0_0_0 : (tripleIndices 4 1 4).map ((HexagonAtoms572.assocCAB) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_1 : (tripleIndices 4 1 4).map ((HexagonAtoms572.assocCAB) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_2 : (tripleIndices 4 1 4).map ((HexagonAtoms572.assocCAB) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_3 : (tripleIndices 4 1 4).map ((HexagonAtoms572.assocCAB) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_0 : (tripleIndices 4 1 4).map ((HexagonAtoms572.assocCAB) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = rows_assocCAB ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_1 : (tripleIndices 4 1 4).map ((HexagonAtoms572.assocCAB) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = rows_assocCAB ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_2 : (tripleIndices 4 1 4).map ((HexagonAtoms572.assocCAB) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = rows_assocCAB ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_3 : (tripleIndices 4 1 4).map ((HexagonAtoms572.assocCAB) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = rows_assocCAB ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_0 : (tripleIndices 4 1 4).map ((HexagonAtoms572.assocCAB) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_1 : (tripleIndices 4 1 4).map ((HexagonAtoms572.assocCAB) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_2 : (tripleIndices 4 1 4).map ((HexagonAtoms572.assocCAB) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_3 : (tripleIndices 4 1 4).map ((HexagonAtoms572.assocCAB) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_0 : (tripleIndices 4 1 4).map ((HexagonAtoms572.assocCAB) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = rows_assocCAB ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_1 : (tripleIndices 4 1 4).map ((HexagonAtoms572.assocCAB) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = rows_assocCAB ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_2 : (tripleIndices 4 1 4).map ((HexagonAtoms572.assocCAB) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = rows_assocCAB ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_3 : (tripleIndices 4 1 4).map ((HexagonAtoms572.assocCAB) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = rows_assocCAB ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocCAB_data (r : RightIndex 2 5 7) : (tripleIndices 4 1 4).map ((HexagonAtoms572.assocCAB) r) = rows_assocCAB r := by
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

private def cols_assocABCData : List (List ℤ) := [decodeIntegerRow 16 3 1 16740394,
    decodeIntegerRow 16 3 1 35872268,
    decodeIntegerRow 16 3 1 20991946,
    decodeIntegerRow 16 3 1 23117692,
    decodeIntegerRow 16 3 1 21502948,
    decodeIntegerRow 16 3 1 21518986,
    decodeIntegerRow 16 3 1 21346132,
    decodeIntegerRow 16 3 1 21464554,
    decodeIntegerRow 16 3 1 7174454,
    decodeIntegerRow 16 3 1 26306332,
    decodeIntegerRow 16 3 1 19929046,
    decodeIntegerRow 16 3 1 22054828,
    decodeIntegerRow 16 3 1 21532108,
    decodeIntegerRow 16 3 1 21542314,
    decodeIntegerRow 16 3 1 21582652,
    decodeIntegerRow 16 3 1 21700426]

def cols_assocABC (r : LeftIndex 5 7 2) : List ℤ := cols_assocABCData.getD (leftPosition 5 7 2 r) []

private theorem cols_assocABC_eq_0_0_0 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms572.assocABC) j ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = cols_assocABC ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_1 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms572.assocABC) j ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = cols_assocABC ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_2 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms572.assocABC) j ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = cols_assocABC ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_3 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms572.assocABC) j ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = cols_assocABC ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_0 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms572.assocABC) j ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = cols_assocABC ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_1 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms572.assocABC) j ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = cols_assocABC ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_2 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms572.assocABC) j ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = cols_assocABC ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_3 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms572.assocABC) j ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = cols_assocABC ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_0 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms572.assocABC) j ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = cols_assocABC ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_1 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms572.assocABC) j ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = cols_assocABC ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_2 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms572.assocABC) j ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = cols_assocABC ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_3 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms572.assocABC) j ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = cols_assocABC ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_1_0 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms572.assocABC) j ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = cols_assocABC ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_1_1 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms572.assocABC) j ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = cols_assocABC ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_1_2 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms572.assocABC) j ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = cols_assocABC ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_1_3 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms572.assocABC) j ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = cols_assocABC ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_assocABC_data (r : LeftIndex 5 7 2) : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms572.assocABC) j r) = cols_assocABC r := by
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

private def cols_right0Data : List (List ℤ) := [decodeIntegerRow 16 3 1 16740394,
    decodeIntegerRow 16 3 1 35872268,
    decodeIntegerRow 16 3 1 20991946,
    decodeIntegerRow 16 3 1 23117692,
    decodeIntegerRow 16 3 1 21502948,
    decodeIntegerRow 16 3 1 21518986,
    decodeIntegerRow 16 3 1 21346132,
    decodeIntegerRow 16 3 1 21464554,
    decodeIntegerRow 16 3 1 7174454,
    decodeIntegerRow 16 3 1 26306332,
    decodeIntegerRow 16 3 1 19929046,
    decodeIntegerRow 16 3 1 22054828,
    decodeIntegerRow 16 3 1 21532108,
    decodeIntegerRow 16 3 1 21542314,
    decodeIntegerRow 16 3 1 21582652,
    decodeIntegerRow 16 3 1 21700426]

def cols_right0 (r : LeftIndex 5 7 2) : List ℤ := cols_right0Data.getD (leftPosition 5 7 2 r) []

private theorem cols_right0_eq_0_0_0 : (tripleIndices 2 2 4).map (fun j => (right0Middle5 7 2) j ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = cols_right0 ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_1 : (tripleIndices 2 2 4).map (fun j => (right0Middle5 7 2) j ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = cols_right0 ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_2 : (tripleIndices 2 2 4).map (fun j => (right0Middle5 7 2) j ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = cols_right0 ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_3 : (tripleIndices 2 2 4).map (fun j => (right0Middle5 7 2) j ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = cols_right0 ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_0 : (tripleIndices 2 2 4).map (fun j => (right0Middle5 7 2) j ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = cols_right0 ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_1 : (tripleIndices 2 2 4).map (fun j => (right0Middle5 7 2) j ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = cols_right0 ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_2 : (tripleIndices 2 2 4).map (fun j => (right0Middle5 7 2) j ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = cols_right0 ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_3 : (tripleIndices 2 2 4).map (fun j => (right0Middle5 7 2) j ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = cols_right0 ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_0 : (tripleIndices 2 2 4).map (fun j => (right0Middle5 7 2) j ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = cols_right0 ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_1 : (tripleIndices 2 2 4).map (fun j => (right0Middle5 7 2) j ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = cols_right0 ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_2 : (tripleIndices 2 2 4).map (fun j => (right0Middle5 7 2) j ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = cols_right0 ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_3 : (tripleIndices 2 2 4).map (fun j => (right0Middle5 7 2) j ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = cols_right0 ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_0 : (tripleIndices 2 2 4).map (fun j => (right0Middle5 7 2) j ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = cols_right0 ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_1 : (tripleIndices 2 2 4).map (fun j => (right0Middle5 7 2) j ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = cols_right0 ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_2 : (tripleIndices 2 2 4).map (fun j => (right0Middle5 7 2) j ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = cols_right0 ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_3 : (tripleIndices 2 2 4).map (fun j => (right0Middle5 7 2) j ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = cols_right0 ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right0_data (r : LeftIndex 5 7 2) : (tripleIndices 2 2 4).map (fun j => (right0Middle5 7 2) j r) = cols_right0 r := by
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

private def cols_left0Data : List (List ℤ) := [decodeIntegerRow 16 3 1 26306332,
    decodeIntegerRow 16 3 1 7174454,
    decodeIntegerRow 16 3 1 22054828,
    decodeIntegerRow 16 3 1 19929046,
    decodeIntegerRow 16 3 1 21542314,
    decodeIntegerRow 16 3 1 21532108,
    decodeIntegerRow 16 3 1 21700426,
    decodeIntegerRow 16 3 1 21582652,
    decodeIntegerRow 16 3 1 35872268,
    decodeIntegerRow 16 3 1 16740394,
    decodeIntegerRow 16 3 1 23117692,
    decodeIntegerRow 16 3 1 20991946,
    decodeIntegerRow 16 3 1 21518986,
    decodeIntegerRow 16 3 1 21502948,
    decodeIntegerRow 16 3 1 21464554,
    decodeIntegerRow 16 3 1 21346132]

def cols_left0 (r : LeftIndex 5 7 2) : List ℤ := cols_left0Data.getD (leftPosition 5 7 2 r) []

private theorem cols_left0_eq_0_0_0 : (tripleIndices 2 2 4).map (fun j => (left0Middle5 7 2) j ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = cols_left0 ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_1 : (tripleIndices 2 2 4).map (fun j => (left0Middle5 7 2) j ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = cols_left0 ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_2 : (tripleIndices 2 2 4).map (fun j => (left0Middle5 7 2) j ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = cols_left0 ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_3 : (tripleIndices 2 2 4).map (fun j => (left0Middle5 7 2) j ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = cols_left0 ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_0 : (tripleIndices 2 2 4).map (fun j => (left0Middle5 7 2) j ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = cols_left0 ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_1 : (tripleIndices 2 2 4).map (fun j => (left0Middle5 7 2) j ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = cols_left0 ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_2 : (tripleIndices 2 2 4).map (fun j => (left0Middle5 7 2) j ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = cols_left0 ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_3 : (tripleIndices 2 2 4).map (fun j => (left0Middle5 7 2) j ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = cols_left0 ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_0 : (tripleIndices 2 2 4).map (fun j => (left0Middle5 7 2) j ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = cols_left0 ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_1 : (tripleIndices 2 2 4).map (fun j => (left0Middle5 7 2) j ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = cols_left0 ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_2 : (tripleIndices 2 2 4).map (fun j => (left0Middle5 7 2) j ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = cols_left0 ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_3 : (tripleIndices 2 2 4).map (fun j => (left0Middle5 7 2) j ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = cols_left0 ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_0 : (tripleIndices 2 2 4).map (fun j => (left0Middle5 7 2) j ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = cols_left0 ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_1 : (tripleIndices 2 2 4).map (fun j => (left0Middle5 7 2) j ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = cols_left0 ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_2 : (tripleIndices 2 2 4).map (fun j => (left0Middle5 7 2) j ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = cols_left0 ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_3 : (tripleIndices 2 2 4).map (fun j => (left0Middle5 7 2) j ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = cols_left0 ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_left0_data (r : LeftIndex 5 7 2) : (tripleIndices 2 2 4).map (fun j => (left0Middle5 7 2) j r) = cols_left0 r := by
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

private def cols_right2Data : List (List ℤ) := [decodeIntegerRow 16 3 1 36232648,
    decodeIntegerRow 16 3 1 18415688,
    decodeIntegerRow 16 3 1 27942152,
    decodeIntegerRow 16 3 1 35525512,
    decodeIntegerRow 16 3 1 15108836,
    decodeIntegerRow 16 3 1 35523556,
    decodeIntegerRow 16 3 1 6813124,
    decodeIntegerRow 16 3 1 18411204,
    decodeIntegerRow 16 3 1 15183356,
    decodeIntegerRow 16 3 1 35158084,
    decodeIntegerRow 16 3 1 6472924,
    decodeIntegerRow 16 3 1 18258276,
    decodeIntegerRow 16 3 1 36574792,
    decodeIntegerRow 16 3 1 18253688,
    decodeIntegerRow 16 3 1 27859208,
    decodeIntegerRow 16 3 1 35156152]

def cols_right2 (r : LeftIndex 5 7 2) : List ℤ := cols_right2Data.getD (leftPosition 5 7 2 r) []

private theorem cols_right2_eq_0_0_0 : (tripleIndices 4 1 4).map (fun j => (right2Middle5 7 2) j ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = cols_right2 ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_1 : (tripleIndices 4 1 4).map (fun j => (right2Middle5 7 2) j ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = cols_right2 ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_2 : (tripleIndices 4 1 4).map (fun j => (right2Middle5 7 2) j ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = cols_right2 ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_3 : (tripleIndices 4 1 4).map (fun j => (right2Middle5 7 2) j ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = cols_right2 ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_0 : (tripleIndices 4 1 4).map (fun j => (right2Middle5 7 2) j ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = cols_right2 ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_1 : (tripleIndices 4 1 4).map (fun j => (right2Middle5 7 2) j ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = cols_right2 ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_2 : (tripleIndices 4 1 4).map (fun j => (right2Middle5 7 2) j ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = cols_right2 ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_3 : (tripleIndices 4 1 4).map (fun j => (right2Middle5 7 2) j ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = cols_right2 ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_0 : (tripleIndices 4 1 4).map (fun j => (right2Middle5 7 2) j ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = cols_right2 ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_1 : (tripleIndices 4 1 4).map (fun j => (right2Middle5 7 2) j ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = cols_right2 ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_2 : (tripleIndices 4 1 4).map (fun j => (right2Middle5 7 2) j ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = cols_right2 ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_3 : (tripleIndices 4 1 4).map (fun j => (right2Middle5 7 2) j ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = cols_right2 ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_0 : (tripleIndices 4 1 4).map (fun j => (right2Middle5 7 2) j ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = cols_right2 ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_1 : (tripleIndices 4 1 4).map (fun j => (right2Middle5 7 2) j ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = cols_right2 ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_2 : (tripleIndices 4 1 4).map (fun j => (right2Middle5 7 2) j ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = cols_right2 ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_3 : (tripleIndices 4 1 4).map (fun j => (right2Middle5 7 2) j ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = cols_right2 ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right2_data (r : LeftIndex 5 7 2) : (tripleIndices 4 1 4).map (fun j => (right2Middle5 7 2) j r) = cols_right2 r := by
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

theorem product0_eq : HexagonAtoms572.outerABC * HexagonAtoms572.assocABC = rowColumnMul rows_outerABC cols_assocABC :=
  (rowColumnMul_eq _ _ _ _ rows_outerABC_data cols_assocABC_data).symm

theorem product1_eq : HexagonAtoms572.assocBAC * HexagonAtoms572.innerABC = HexagonAtoms572.assocBAC :=
  Matrix.mul_one (m := Fin 4 × Fin 1 × Fin 4) (n := Fin 2 × Fin 2 × Fin 4) _

theorem product2_eq : HexagonAtoms572.innerRightABC * HexagonAtoms572.assocABC = HexagonAtoms572.assocABC :=
  Matrix.one_mul (m := Fin 2 × Fin 2 × Fin 4) (n := Fin 2 × Fin 2 × Fin 4) _

theorem product3_eq : HexagonAtoms572.inverseACB * right0Middle5 7 2 = rowColumnMul rows_inverseACB cols_right0 :=
  (rowColumnMul_eq _ _ _ _ rows_inverseACB_data cols_right0_data).symm

theorem product4_eq : HexagonAtoms572.innerACB * right1Middle5 7 2 = right1Middle5 7 2 :=
  Matrix.one_mul (m := Fin 4 × Fin 1 × Fin 4) (n := Fin 2 × Fin 2 × Fin 4) _

theorem product5_eq : HexagonAtoms572.assocBCA * left0Middle5 7 2 = rowColumnMul rows_assocBCA cols_left0 :=
  (rowColumnMul_eq _ _ _ _ rows_assocBCA_data cols_left0_data).symm

theorem product6_eq : HexagonAtoms572.innerRightBAC * left1Middle5 7 2 = left1Middle5 7 2 :=
  Matrix.one_mul (m := Fin 4 × Fin 1 × Fin 4) (n := Fin 2 × Fin 2 × Fin 4) _

theorem product7_eq : HexagonAtoms572.assocCAB * right2Middle5 7 2 = rowColumnMul rows_assocCAB cols_right2 :=
  (rowColumnMul_eq _ _ _ _ rows_assocCAB_data cols_right2_data).symm

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn572
