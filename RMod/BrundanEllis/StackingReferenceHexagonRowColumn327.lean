import RMod.BrundanEllis.StackingReferenceHexagonAtoms327
import RMod.BrundanEllis.StackingReferenceHexagonMiddle3
import RMod.BrundanEllis.StackingReferenceRowColumnCheck

/-! Verified row and column lists. Each subsequent scalar product traverses
these lists directly, without repeated lookup into the original matrices. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn327
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

def rows_outerABC (r : LeftIndex 2 7 3) : List ℤ := rows_outerABCData.getD (leftPosition 2 7 3 r) []

private theorem rows_outerABC_eq_0_0_0 : (tripleIndices 2 2 4).map ((HexagonAtoms327.outerABC) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = rows_outerABC ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_0_1 : (tripleIndices 2 2 4).map ((HexagonAtoms327.outerABC) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = rows_outerABC ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_0_2 : (tripleIndices 2 2 4).map ((HexagonAtoms327.outerABC) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = rows_outerABC ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_0_3 : (tripleIndices 2 2 4).map ((HexagonAtoms327.outerABC) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = rows_outerABC ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_1_0 : (tripleIndices 2 2 4).map ((HexagonAtoms327.outerABC) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = rows_outerABC ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_1_1 : (tripleIndices 2 2 4).map ((HexagonAtoms327.outerABC) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = rows_outerABC ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_1_2 : (tripleIndices 2 2 4).map ((HexagonAtoms327.outerABC) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = rows_outerABC ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_1_3 : (tripleIndices 2 2 4).map ((HexagonAtoms327.outerABC) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = rows_outerABC ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_0 : (tripleIndices 2 2 4).map ((HexagonAtoms327.outerABC) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = rows_outerABC ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_1 : (tripleIndices 2 2 4).map ((HexagonAtoms327.outerABC) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = rows_outerABC ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_2 : (tripleIndices 2 2 4).map ((HexagonAtoms327.outerABC) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = rows_outerABC ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_3 : (tripleIndices 2 2 4).map ((HexagonAtoms327.outerABC) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = rows_outerABC ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_1_0 : (tripleIndices 2 2 4).map ((HexagonAtoms327.outerABC) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = rows_outerABC ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_1_1 : (tripleIndices 2 2 4).map ((HexagonAtoms327.outerABC) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = rows_outerABC ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_1_2 : (tripleIndices 2 2 4).map ((HexagonAtoms327.outerABC) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = rows_outerABC ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_1_3 : (tripleIndices 2 2 4).map ((HexagonAtoms327.outerABC) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = rows_outerABC ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_outerABC_data (r : LeftIndex 2 7 3) : (tripleIndices 2 2 4).map ((HexagonAtoms327.outerABC) r) = rows_outerABC r := by
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

private def rows_inverseACBData : List (List ℤ) := [decodeIntegerRow 16 3 1 21257680,
    decodeIntegerRow 16 3 1 21629632,
    decodeIntegerRow 16 3 1 21310816,
    decodeIntegerRow 16 3 1 21390520,
    decodeIntegerRow 16 3 1 265760,
    decodeIntegerRow 16 3 1 30026400,
    decodeIntegerRow 16 3 1 4517280,
    decodeIntegerRow 16 3 1 10894560,
    decodeIntegerRow 16 3 1 265680,
    decodeIntegerRow 16 3 1 30026432,
    decodeIntegerRow 16 3 1 4517216,
    decodeIntegerRow 16 3 1 10894520,
    decodeIntegerRow 16 3 1 21782560,
    decodeIntegerRow 16 3 1 21419680,
    decodeIntegerRow 16 3 1 21730720,
    decodeIntegerRow 16 3 1 21652960]

def rows_inverseACB (r : LeftIndex 3 7 2) : List ℤ := rows_inverseACBData.getD (leftPosition 3 7 2 r) []

private theorem rows_inverseACB_eq_0_0_0 : (tripleIndices 2 2 4).map ((HexagonAtoms327.inverseACB) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_1 : (tripleIndices 2 2 4).map ((HexagonAtoms327.inverseACB) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_2 : (tripleIndices 2 2 4).map ((HexagonAtoms327.inverseACB) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_3 : (tripleIndices 2 2 4).map ((HexagonAtoms327.inverseACB) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_0 : (tripleIndices 2 2 4).map ((HexagonAtoms327.inverseACB) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = rows_inverseACB ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_1 : (tripleIndices 2 2 4).map ((HexagonAtoms327.inverseACB) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = rows_inverseACB ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_2 : (tripleIndices 2 2 4).map ((HexagonAtoms327.inverseACB) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = rows_inverseACB ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_3 : (tripleIndices 2 2 4).map ((HexagonAtoms327.inverseACB) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = rows_inverseACB ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_0 : (tripleIndices 2 2 4).map ((HexagonAtoms327.inverseACB) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_1 : (tripleIndices 2 2 4).map ((HexagonAtoms327.inverseACB) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_2 : (tripleIndices 2 2 4).map ((HexagonAtoms327.inverseACB) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_3 : (tripleIndices 2 2 4).map ((HexagonAtoms327.inverseACB) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_0 : (tripleIndices 2 2 4).map ((HexagonAtoms327.inverseACB) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = rows_inverseACB ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_1 : (tripleIndices 2 2 4).map ((HexagonAtoms327.inverseACB) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = rows_inverseACB ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_2 : (tripleIndices 2 2 4).map ((HexagonAtoms327.inverseACB) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = rows_inverseACB ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_3 : (tripleIndices 2 2 4).map ((HexagonAtoms327.inverseACB) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = rows_inverseACB ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_inverseACB_data (r : LeftIndex 3 7 2) : (tripleIndices 2 2 4).map ((HexagonAtoms327.inverseACB) r) = rows_inverseACB r := by
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

private def rows_assocBCAData : List (List ℤ) := [decodeIntegerRow 16 3 1 21419680,
    decodeIntegerRow 16 3 1 21264160,
    decodeIntegerRow 16 3 1 21652960,
    decodeIntegerRow 16 3 1 21316000,
    decodeIntegerRow 16 3 1 38529504,
    decodeIntegerRow 16 3 1 10894520,
    decodeIntegerRow 16 3 1 265680,
    decodeIntegerRow 16 3 1 13020288,
    decodeIntegerRow 16 3 1 13020320,
    decodeIntegerRow 16 3 1 265760,
    decodeIntegerRow 16 3 1 32152160,
    decodeIntegerRow 16 3 1 4517280,
    decodeIntegerRow 16 3 1 21310816,
    decodeIntegerRow 16 3 1 21656200,
    decodeIntegerRow 16 3 1 21789040,
    decodeIntegerRow 16 3 1 21629632]

def rows_assocBCA (r : RightIndex 2 7 3) : List ℤ := rows_assocBCAData.getD (rightPosition 2 7 3 r) []

private theorem rows_assocBCA_eq_0_0_0 : (tripleIndices 2 2 4).map ((HexagonAtoms327.assocBCA) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = rows_assocBCA ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_1 : (tripleIndices 2 2 4).map ((HexagonAtoms327.assocBCA) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = rows_assocBCA ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_2 : (tripleIndices 2 2 4).map ((HexagonAtoms327.assocBCA) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = rows_assocBCA ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_3 : (tripleIndices 2 2 4).map ((HexagonAtoms327.assocBCA) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = rows_assocBCA ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_0 : (tripleIndices 2 2 4).map ((HexagonAtoms327.assocBCA) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = rows_assocBCA ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_1 : (tripleIndices 2 2 4).map ((HexagonAtoms327.assocBCA) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = rows_assocBCA ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_2 : (tripleIndices 2 2 4).map ((HexagonAtoms327.assocBCA) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = rows_assocBCA ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_3 : (tripleIndices 2 2 4).map ((HexagonAtoms327.assocBCA) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = rows_assocBCA ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_0 : (tripleIndices 2 2 4).map ((HexagonAtoms327.assocBCA) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = rows_assocBCA ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_1 : (tripleIndices 2 2 4).map ((HexagonAtoms327.assocBCA) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = rows_assocBCA ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_2 : (tripleIndices 2 2 4).map ((HexagonAtoms327.assocBCA) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = rows_assocBCA ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_3 : (tripleIndices 2 2 4).map ((HexagonAtoms327.assocBCA) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = rows_assocBCA ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_0 : (tripleIndices 2 2 4).map ((HexagonAtoms327.assocBCA) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = rows_assocBCA ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_1 : (tripleIndices 2 2 4).map ((HexagonAtoms327.assocBCA) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = rows_assocBCA ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_2 : (tripleIndices 2 2 4).map ((HexagonAtoms327.assocBCA) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = rows_assocBCA ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_3 : (tripleIndices 2 2 4).map ((HexagonAtoms327.assocBCA) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = rows_assocBCA ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocBCA_data (r : RightIndex 2 7 3) : (tripleIndices 2 2 4).map ((HexagonAtoms327.assocBCA) r) = rows_assocBCA r := by
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

private def rows_assocCABData : List (List ℤ) := [decodeIntegerRow 16 3 1 21759556,
    decodeIntegerRow 16 3 1 21405262,
    decodeIntegerRow 16 3 1 21497116,
    decodeIntegerRow 16 3 1 21536482,
    decodeIntegerRow 16 3 1 21523358,
    decodeIntegerRow 16 3 1 21523364,
    decodeIntegerRow 16 3 1 21523342,
    decodeIntegerRow 16 3 1 21523396,
    decodeIntegerRow 16 3 1 23649124,
    decodeIntegerRow 16 3 1 22586242,
    decodeIntegerRow 16 3 1 40655236,
    decodeIntegerRow 16 3 1 31089298,
    decodeIntegerRow 16 3 1 21524818,
    decodeIntegerRow 16 3 1 21526276,
    decodeIntegerRow 16 3 1 21523198,
    decodeIntegerRow 16 3 1 21523036]

def rows_assocCAB (r : RightIndex 7 3 2) : List ℤ := rows_assocCABData.getD (rightPosition 7 3 2 r) []

private theorem rows_assocCAB_eq_0_0_0 : (tripleIndices 2 2 4).map ((HexagonAtoms327.assocCAB) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_1 : (tripleIndices 2 2 4).map ((HexagonAtoms327.assocCAB) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_2 : (tripleIndices 2 2 4).map ((HexagonAtoms327.assocCAB) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_3 : (tripleIndices 2 2 4).map ((HexagonAtoms327.assocCAB) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_0 : (tripleIndices 2 2 4).map ((HexagonAtoms327.assocCAB) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = rows_assocCAB ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_1 : (tripleIndices 2 2 4).map ((HexagonAtoms327.assocCAB) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = rows_assocCAB ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_2 : (tripleIndices 2 2 4).map ((HexagonAtoms327.assocCAB) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = rows_assocCAB ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_3 : (tripleIndices 2 2 4).map ((HexagonAtoms327.assocCAB) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = rows_assocCAB ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_0 : (tripleIndices 2 2 4).map ((HexagonAtoms327.assocCAB) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_1 : (tripleIndices 2 2 4).map ((HexagonAtoms327.assocCAB) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_2 : (tripleIndices 2 2 4).map ((HexagonAtoms327.assocCAB) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_3 : (tripleIndices 2 2 4).map ((HexagonAtoms327.assocCAB) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_0 : (tripleIndices 2 2 4).map ((HexagonAtoms327.assocCAB) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = rows_assocCAB ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_1 : (tripleIndices 2 2 4).map ((HexagonAtoms327.assocCAB) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = rows_assocCAB ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_2 : (tripleIndices 2 2 4).map ((HexagonAtoms327.assocCAB) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = rows_assocCAB ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_3 : (tripleIndices 2 2 4).map ((HexagonAtoms327.assocCAB) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = rows_assocCAB ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocCAB_data (r : RightIndex 7 3 2) : (tripleIndices 2 2 4).map ((HexagonAtoms327.assocCAB) r) = rows_assocCAB r := by
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

private def cols_assocABCData : List (List ℤ) := [decodeIntegerRow 16 3 1 7705868,
    decodeIntegerRow 16 3 1 18334708,
    decodeIntegerRow 16 3 1 27900664,
    decodeIntegerRow 16 3 1 36403736,
    decodeIntegerRow 16 3 1 21337384,
    decodeIntegerRow 16 3 1 21443656,
    decodeIntegerRow 16 3 1 21483508,
    decodeIntegerRow 16 3 1 21350668,
    decodeIntegerRow 16 3 1 21445600,
    decodeIntegerRow 16 3 1 21704800,
    decodeIntegerRow 16 3 1 21354880,
    decodeIntegerRow 16 3 1 21562240,
    decodeIntegerRow 16 3 1 18334720,
    decodeIntegerRow 16 3 1 35340800,
    decodeIntegerRow 16 3 1 36403680,
    decodeIntegerRow 16 3 1 15146080]

def cols_assocABC (r : LeftIndex 3 2 7) : List ℤ := cols_assocABCData.getD (leftPosition 3 2 7 r) []

private theorem cols_assocABC_eq_0_0_0 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms327.assocABC) j ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = cols_assocABC ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_1 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms327.assocABC) j ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = cols_assocABC ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_2 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms327.assocABC) j ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = cols_assocABC ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_3 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms327.assocABC) j ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = cols_assocABC ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_0 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms327.assocABC) j ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = cols_assocABC ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_1 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms327.assocABC) j ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = cols_assocABC ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_2 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms327.assocABC) j ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = cols_assocABC ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_3 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms327.assocABC) j ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = cols_assocABC ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_0 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms327.assocABC) j ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = cols_assocABC ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_1 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms327.assocABC) j ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = cols_assocABC ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_2 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms327.assocABC) j ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = cols_assocABC ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_3 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms327.assocABC) j ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = cols_assocABC ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_1_0 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms327.assocABC) j ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = cols_assocABC ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_1_1 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms327.assocABC) j ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = cols_assocABC ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_1_2 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms327.assocABC) j ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = cols_assocABC ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_1_3 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms327.assocABC) j ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = cols_assocABC ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_assocABC_data (r : LeftIndex 3 2 7) : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms327.assocABC) j r) = cols_assocABC r := by
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

private def cols_right0Data : List (List ℤ) := [decodeIntegerRow 16 3 1 7705868,
    decodeIntegerRow 16 3 1 18334708,
    decodeIntegerRow 16 3 1 27900664,
    decodeIntegerRow 16 3 1 36403736,
    decodeIntegerRow 16 3 1 21337384,
    decodeIntegerRow 16 3 1 21443656,
    decodeIntegerRow 16 3 1 21483508,
    decodeIntegerRow 16 3 1 21350668,
    decodeIntegerRow 16 3 1 21445600,
    decodeIntegerRow 16 3 1 21704800,
    decodeIntegerRow 16 3 1 21354880,
    decodeIntegerRow 16 3 1 21562240,
    decodeIntegerRow 16 3 1 18334720,
    decodeIntegerRow 16 3 1 35340800,
    decodeIntegerRow 16 3 1 36403680,
    decodeIntegerRow 16 3 1 15146080]

def cols_right0 (r : LeftIndex 3 2 7) : List ℤ := cols_right0Data.getD (leftPosition 3 2 7 r) []

private theorem cols_right0_eq_0_0_0 : (tripleIndices 2 2 4).map (fun j => (right0Middle3 2 7) j ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = cols_right0 ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_1 : (tripleIndices 2 2 4).map (fun j => (right0Middle3 2 7) j ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = cols_right0 ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_2 : (tripleIndices 2 2 4).map (fun j => (right0Middle3 2 7) j ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = cols_right0 ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_3 : (tripleIndices 2 2 4).map (fun j => (right0Middle3 2 7) j ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = cols_right0 ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_0 : (tripleIndices 2 2 4).map (fun j => (right0Middle3 2 7) j ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = cols_right0 ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_1 : (tripleIndices 2 2 4).map (fun j => (right0Middle3 2 7) j ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = cols_right0 ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_2 : (tripleIndices 2 2 4).map (fun j => (right0Middle3 2 7) j ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = cols_right0 ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_3 : (tripleIndices 2 2 4).map (fun j => (right0Middle3 2 7) j ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = cols_right0 ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_0 : (tripleIndices 2 2 4).map (fun j => (right0Middle3 2 7) j ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = cols_right0 ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_1 : (tripleIndices 2 2 4).map (fun j => (right0Middle3 2 7) j ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = cols_right0 ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_2 : (tripleIndices 2 2 4).map (fun j => (right0Middle3 2 7) j ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = cols_right0 ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_3 : (tripleIndices 2 2 4).map (fun j => (right0Middle3 2 7) j ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = cols_right0 ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_0 : (tripleIndices 2 2 4).map (fun j => (right0Middle3 2 7) j ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = cols_right0 ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_1 : (tripleIndices 2 2 4).map (fun j => (right0Middle3 2 7) j ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = cols_right0 ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_2 : (tripleIndices 2 2 4).map (fun j => (right0Middle3 2 7) j ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = cols_right0 ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_3 : (tripleIndices 2 2 4).map (fun j => (right0Middle3 2 7) j ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = cols_right0 ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right0_data (r : LeftIndex 3 2 7) : (tripleIndices 2 2 4).map (fun j => (right0Middle3 2 7) j r) = cols_right0 r := by
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

private def cols_left0Data : List (List ℤ) := [decodeIntegerRow 16 3 1 35340800,
    decodeIntegerRow 16 3 1 24712000,
    decodeIntegerRow 16 3 1 15146080,
    decodeIntegerRow 16 3 1 6643040,
    decodeIntegerRow 16 3 1 21704800,
    decodeIntegerRow 16 3 1 21601120,
    decodeIntegerRow 16 3 1 21562240,
    decodeIntegerRow 16 3 1 21691840,
    decodeIntegerRow 16 3 1 21603064,
    decodeIntegerRow 16 3 1 21337384,
    decodeIntegerRow 16 3 1 21696052,
    decodeIntegerRow 16 3 1 21483508,
    decodeIntegerRow 16 3 1 24712012,
    decodeIntegerRow 16 3 1 7705868,
    decodeIntegerRow 16 3 1 6642984,
    decodeIntegerRow 16 3 1 27900664]

def cols_left0 (r : LeftIndex 3 2 7) : List ℤ := cols_left0Data.getD (leftPosition 3 2 7 r) []

private theorem cols_left0_eq_0_0_0 : (tripleIndices 2 2 4).map (fun j => (left0Middle3 2 7) j ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = cols_left0 ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_1 : (tripleIndices 2 2 4).map (fun j => (left0Middle3 2 7) j ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = cols_left0 ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_2 : (tripleIndices 2 2 4).map (fun j => (left0Middle3 2 7) j ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = cols_left0 ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_3 : (tripleIndices 2 2 4).map (fun j => (left0Middle3 2 7) j ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = cols_left0 ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_0 : (tripleIndices 2 2 4).map (fun j => (left0Middle3 2 7) j ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = cols_left0 ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_1 : (tripleIndices 2 2 4).map (fun j => (left0Middle3 2 7) j ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = cols_left0 ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_2 : (tripleIndices 2 2 4).map (fun j => (left0Middle3 2 7) j ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = cols_left0 ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_3 : (tripleIndices 2 2 4).map (fun j => (left0Middle3 2 7) j ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = cols_left0 ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_0 : (tripleIndices 2 2 4).map (fun j => (left0Middle3 2 7) j ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = cols_left0 ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_1 : (tripleIndices 2 2 4).map (fun j => (left0Middle3 2 7) j ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = cols_left0 ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_2 : (tripleIndices 2 2 4).map (fun j => (left0Middle3 2 7) j ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = cols_left0 ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_3 : (tripleIndices 2 2 4).map (fun j => (left0Middle3 2 7) j ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = cols_left0 ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_0 : (tripleIndices 2 2 4).map (fun j => (left0Middle3 2 7) j ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = cols_left0 ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_1 : (tripleIndices 2 2 4).map (fun j => (left0Middle3 2 7) j ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = cols_left0 ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_2 : (tripleIndices 2 2 4).map (fun j => (left0Middle3 2 7) j ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = cols_left0 ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_3 : (tripleIndices 2 2 4).map (fun j => (left0Middle3 2 7) j ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = cols_left0 ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_left0_data (r : LeftIndex 3 2 7) : (tripleIndices 2 2 4).map (fun j => (left0Middle3 2 7) j r) = cols_left0 r := by
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

private def cols_right2Data : List (List ℤ) := [decodeIntegerRow 16 9 4 926649565801960,
    decodeIntegerRow 16 9 4 926398517325088,
    decodeIntegerRow 16 9 4 926508372557080,
    decodeIntegerRow 16 9 4 926511471920992,
    decodeIntegerRow 16 9 4 926510094425888,
    decodeIntegerRow 16 9 4 926510094425960,
    decodeIntegerRow 16 9 4 926510094423328,
    decodeIntegerRow 16 9 4 926510094429160,
    decodeIntegerRow 16 9 4 915212912966680,
    decodeIntegerRow 16 9 4 917472349258528,
    decodeIntegerRow 16 9 4 11438396227480,
    decodeIntegerRow 16 9 4 194452735867168,
    decodeIntegerRow 16 9 4 926510077419808,
    decodeIntegerRow 16 9 4 926510073168280,
    decodeIntegerRow 16 9 4 926510094635872,
    decodeIntegerRow 16 9 4 926510094688360]

def cols_right2 (r : LeftIndex 3 2 7) : List ℤ := cols_right2Data.getD (leftPosition 3 2 7 r) []

private theorem cols_right2_eq_0_0_0 : (tripleIndices 2 2 4).map (fun j => (right2Middle3 2 7) j ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = cols_right2 ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_1 : (tripleIndices 2 2 4).map (fun j => (right2Middle3 2 7) j ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = cols_right2 ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_2 : (tripleIndices 2 2 4).map (fun j => (right2Middle3 2 7) j ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = cols_right2 ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_3 : (tripleIndices 2 2 4).map (fun j => (right2Middle3 2 7) j ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = cols_right2 ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_0 : (tripleIndices 2 2 4).map (fun j => (right2Middle3 2 7) j ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = cols_right2 ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_1 : (tripleIndices 2 2 4).map (fun j => (right2Middle3 2 7) j ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = cols_right2 ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_2 : (tripleIndices 2 2 4).map (fun j => (right2Middle3 2 7) j ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = cols_right2 ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_3 : (tripleIndices 2 2 4).map (fun j => (right2Middle3 2 7) j ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = cols_right2 ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_0 : (tripleIndices 2 2 4).map (fun j => (right2Middle3 2 7) j ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = cols_right2 ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_1 : (tripleIndices 2 2 4).map (fun j => (right2Middle3 2 7) j ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = cols_right2 ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_2 : (tripleIndices 2 2 4).map (fun j => (right2Middle3 2 7) j ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = cols_right2 ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_3 : (tripleIndices 2 2 4).map (fun j => (right2Middle3 2 7) j ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = cols_right2 ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_0 : (tripleIndices 2 2 4).map (fun j => (right2Middle3 2 7) j ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = cols_right2 ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_1 : (tripleIndices 2 2 4).map (fun j => (right2Middle3 2 7) j ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = cols_right2 ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_2 : (tripleIndices 2 2 4).map (fun j => (right2Middle3 2 7) j ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = cols_right2 ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_3 : (tripleIndices 2 2 4).map (fun j => (right2Middle3 2 7) j ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = cols_right2 ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right2_data (r : LeftIndex 3 2 7) : (tripleIndices 2 2 4).map (fun j => (right2Middle3 2 7) j r) = cols_right2 r := by
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

theorem product0_eq : HexagonAtoms327.outerABC * HexagonAtoms327.assocABC = rowColumnMul rows_outerABC cols_assocABC :=
  (rowColumnMul_eq _ _ _ _ rows_outerABC_data cols_assocABC_data).symm

theorem product1_eq : HexagonAtoms327.assocBAC * HexagonAtoms327.innerABC = HexagonAtoms327.assocBAC :=
  Matrix.mul_one (m := Fin 2 × Fin 2 × Fin 4) (n := Fin 2 × Fin 2 × Fin 4) _

theorem product2_eq : HexagonAtoms327.innerRightABC * HexagonAtoms327.assocABC = HexagonAtoms327.assocABC :=
  Matrix.one_mul (m := Fin 2 × Fin 2 × Fin 4) (n := Fin 2 × Fin 2 × Fin 4) _

theorem product3_eq : HexagonAtoms327.inverseACB * right0Middle3 2 7 = rowColumnMul rows_inverseACB cols_right0 :=
  (rowColumnMul_eq _ _ _ _ rows_inverseACB_data cols_right0_data).symm

theorem product4_eq : HexagonAtoms327.innerACB * right1Middle3 2 7 = right1Middle3 2 7 :=
  Matrix.one_mul (m := Fin 2 × Fin 2 × Fin 4) (n := Fin 2 × Fin 2 × Fin 4) _

theorem product5_eq : HexagonAtoms327.assocBCA * left0Middle3 2 7 = rowColumnMul rows_assocBCA cols_left0 :=
  (rowColumnMul_eq _ _ _ _ rows_assocBCA_data cols_left0_data).symm

theorem product6_eq : HexagonAtoms327.innerRightBAC * left1Middle3 2 7 = left1Middle3 2 7 :=
  Matrix.one_mul (m := Fin 2 × Fin 2 × Fin 4) (n := Fin 2 × Fin 2 × Fin 4) _

theorem product7_eq : HexagonAtoms327.assocCAB * right2Middle3 2 7 = rowColumnMul rows_assocCAB cols_right2 :=
  (rowColumnMul_eq _ _ _ _ rows_assocCAB_data cols_right2_data).symm

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn327
