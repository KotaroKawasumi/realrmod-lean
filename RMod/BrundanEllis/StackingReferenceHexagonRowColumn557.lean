import RMod.BrundanEllis.StackingReferenceHexagonAtoms557
import RMod.BrundanEllis.StackingReferenceHexagonMiddle5
import RMod.BrundanEllis.StackingReferenceRowColumnCheck

/-! Verified row and column lists. Each subsequent scalar product traverses
these lists directly, without repeated lookup into the original matrices. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn557
open Superfusion

theorem assocBAC_alias : HexagonAtoms557.assocBAC = HexagonAtoms557.assocABC :=
  HexagonAtoms557.assocBAC_eq.symm.trans HexagonAtoms557.assocABC_eq

theorem innerRightBAC_alias : HexagonAtoms557.innerRightBAC = HexagonAtoms557.innerRightABC :=
  HexagonAtoms557.innerRightBAC_eq.symm.trans HexagonAtoms557.innerRightABC_eq

private def rows_assocABCData : List (List ℤ) := [decodeIntegerRow 16 3 1 19909436,
    decodeIntegerRow 16 3 1 22061608,
    decodeIntegerRow 16 3 1 23137448,
    decodeIntegerRow 16 3 1 20985604,
    decodeIntegerRow 16 3 1 7352320,
    decodeIntegerRow 16 3 1 26249440,
    decodeIntegerRow 16 3 1 7350880,
    decodeIntegerRow 16 3 1 26245120,
    decodeIntegerRow 16 3 1 22048480,
    decodeIntegerRow 16 3 1 23097920,
    decodeIntegerRow 16 3 1 20998720,
    decodeIntegerRow 16 3 1 19948640,
    decodeIntegerRow 16 3 1 26367592,
    decodeIntegerRow 16 3 1 36048676,
    decodeIntegerRow 16 3 1 26363164,
    decodeIntegerRow 16 3 1 36050152]

def rows_assocABC (r : RightIndex 5 5 7) : List ℤ := rows_assocABCData.getD (rightPosition 5 5 7 r) []

private theorem rows_assocABC_eq_0_0_0 : (tripleIndices 4 2 2).map ((HexagonAtoms557.assocABC) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = rows_assocABC ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_0_1 : (tripleIndices 4 2 2).map ((HexagonAtoms557.assocABC) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = rows_assocABC ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_1_0 : (tripleIndices 4 2 2).map ((HexagonAtoms557.assocABC) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = rows_assocABC ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_1_1 : (tripleIndices 4 2 2).map ((HexagonAtoms557.assocABC) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = rows_assocABC ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_2_0 : (tripleIndices 4 2 2).map ((HexagonAtoms557.assocABC) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = rows_assocABC ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_2_1 : (tripleIndices 4 2 2).map ((HexagonAtoms557.assocABC) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = rows_assocABC ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_3_0 : (tripleIndices 4 2 2).map ((HexagonAtoms557.assocABC) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = rows_assocABC ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_3_1 : (tripleIndices 4 2 2).map ((HexagonAtoms557.assocABC) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = rows_assocABC ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_0_0 : (tripleIndices 4 2 2).map ((HexagonAtoms557.assocABC) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = rows_assocABC ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_0_1 : (tripleIndices 4 2 2).map ((HexagonAtoms557.assocABC) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = rows_assocABC ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_1_0 : (tripleIndices 4 2 2).map ((HexagonAtoms557.assocABC) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = rows_assocABC ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_1_1 : (tripleIndices 4 2 2).map ((HexagonAtoms557.assocABC) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = rows_assocABC ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_2_0 : (tripleIndices 4 2 2).map ((HexagonAtoms557.assocABC) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = rows_assocABC ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_2_1 : (tripleIndices 4 2 2).map ((HexagonAtoms557.assocABC) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = rows_assocABC ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_3_0 : (tripleIndices 4 2 2).map ((HexagonAtoms557.assocABC) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = rows_assocABC ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_3_1 : (tripleIndices 4 2 2).map ((HexagonAtoms557.assocABC) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = rows_assocABC ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocABC_data (r : RightIndex 5 5 7) : (tripleIndices 4 2 2).map ((HexagonAtoms557.assocABC) r) = rows_assocABC r := by
  fin_cases r
  · exact rows_assocABC_eq_0_0_0
  · exact rows_assocABC_eq_0_0_1
  · exact rows_assocABC_eq_0_1_0
  · exact rows_assocABC_eq_0_1_1
  · exact rows_assocABC_eq_0_2_0
  · exact rows_assocABC_eq_0_2_1
  · exact rows_assocABC_eq_0_3_0
  · exact rows_assocABC_eq_0_3_1
  · exact rows_assocABC_eq_1_0_0
  · exact rows_assocABC_eq_1_0_1
  · exact rows_assocABC_eq_1_1_0
  · exact rows_assocABC_eq_1_1_1
  · exact rows_assocABC_eq_1_2_0
  · exact rows_assocABC_eq_1_2_1
  · exact rows_assocABC_eq_1_3_0
  · exact rows_assocABC_eq_1_3_1

private def rows_inverseACBData : List (List ℤ) := [decodeIntegerRow 16 3 1 21464230,
    decodeIntegerRow 16 3 1 21345970,
    decodeIntegerRow 16 3 1 23117710,
    decodeIntegerRow 16 3 1 20991910,
    decodeIntegerRow 16 3 1 16740392,
    decodeIntegerRow 16 3 1 7174456,
    decodeIntegerRow 16 3 1 21505864,
    decodeIntegerRow 16 3 1 21529192,
    decodeIntegerRow 16 3 1 21501490,
    decodeIntegerRow 16 3 1 21530650,
    decodeIntegerRow 16 3 1 26306330,
    decodeIntegerRow 16 3 1 35872270,
    decodeIntegerRow 16 3 1 19929064,
    decodeIntegerRow 16 3 1 22054792,
    decodeIntegerRow 16 3 1 21464392,
    decodeIntegerRow 16 3 1 21346456]

def rows_inverseACB (r : LeftIndex 5 7 5) : List ℤ := rows_inverseACBData.getD (leftPosition 5 7 5 r) []

private theorem rows_inverseACB_eq_0_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms557.inverseACB) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms557.inverseACB) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_0 : (tripleIndices 2 4 2).map ((HexagonAtoms557.inverseACB) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = rows_inverseACB ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_1 : (tripleIndices 2 4 2).map ((HexagonAtoms557.inverseACB) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = rows_inverseACB ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_2_0 : (tripleIndices 2 4 2).map ((HexagonAtoms557.inverseACB) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = rows_inverseACB ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_2_1 : (tripleIndices 2 4 2).map ((HexagonAtoms557.inverseACB) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = rows_inverseACB ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_3_0 : (tripleIndices 2 4 2).map ((HexagonAtoms557.inverseACB) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = rows_inverseACB ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_3_1 : (tripleIndices 2 4 2).map ((HexagonAtoms557.inverseACB) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = rows_inverseACB ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms557.inverseACB) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms557.inverseACB) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_0 : (tripleIndices 2 4 2).map ((HexagonAtoms557.inverseACB) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = rows_inverseACB ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_1 : (tripleIndices 2 4 2).map ((HexagonAtoms557.inverseACB) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = rows_inverseACB ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_2_0 : (tripleIndices 2 4 2).map ((HexagonAtoms557.inverseACB) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = rows_inverseACB ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_2_1 : (tripleIndices 2 4 2).map ((HexagonAtoms557.inverseACB) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = rows_inverseACB ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_3_0 : (tripleIndices 2 4 2).map ((HexagonAtoms557.inverseACB) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = rows_inverseACB ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_3_1 : (tripleIndices 2 4 2).map ((HexagonAtoms557.inverseACB) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = rows_inverseACB ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_inverseACB_data (r : LeftIndex 5 7 5) : (tripleIndices 2 4 2).map ((HexagonAtoms557.inverseACB) r) = rows_inverseACB r := by
  fin_cases r
  · exact rows_inverseACB_eq_0_0_0
  · exact rows_inverseACB_eq_0_0_1
  · exact rows_inverseACB_eq_0_1_0
  · exact rows_inverseACB_eq_0_1_1
  · exact rows_inverseACB_eq_0_2_0
  · exact rows_inverseACB_eq_0_2_1
  · exact rows_inverseACB_eq_0_3_0
  · exact rows_inverseACB_eq_0_3_1
  · exact rows_inverseACB_eq_1_0_0
  · exact rows_inverseACB_eq_1_0_1
  · exact rows_inverseACB_eq_1_1_0
  · exact rows_inverseACB_eq_1_1_1
  · exact rows_inverseACB_eq_1_2_0
  · exact rows_inverseACB_eq_1_2_1
  · exact rows_inverseACB_eq_1_3_0
  · exact rows_inverseACB_eq_1_3_1

private def rows_assocBCAData : List (List ℤ) := [decodeIntegerRow 16 3 1 21582490,
    decodeIntegerRow 16 3 1 21700750,
    decodeIntegerRow 16 3 1 19929010,
    decodeIntegerRow 16 3 1 22054810,
    decodeIntegerRow 16 3 1 26306328,
    decodeIntegerRow 16 3 1 35872264,
    decodeIntegerRow 16 3 1 21540856,
    decodeIntegerRow 16 3 1 21517528,
    decodeIntegerRow 16 3 1 21545230,
    decodeIntegerRow 16 3 1 21516070,
    decodeIntegerRow 16 3 1 16740390,
    decodeIntegerRow 16 3 1 7174450,
    decodeIntegerRow 16 3 1 23117656,
    decodeIntegerRow 16 3 1 20991928,
    decodeIntegerRow 16 3 1 21582328,
    decodeIntegerRow 16 3 1 21700264]

def rows_assocBCA (r : RightIndex 5 7 5) : List ℤ := rows_assocBCAData.getD (rightPosition 5 7 5 r) []

private theorem rows_assocBCA_eq_0_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms557.assocBCA) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = rows_assocBCA ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms557.assocBCA) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = rows_assocBCA ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_0 : (tripleIndices 2 4 2).map ((HexagonAtoms557.assocBCA) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = rows_assocBCA ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_1 : (tripleIndices 2 4 2).map ((HexagonAtoms557.assocBCA) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = rows_assocBCA ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_2_0 : (tripleIndices 2 4 2).map ((HexagonAtoms557.assocBCA) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = rows_assocBCA ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_2_1 : (tripleIndices 2 4 2).map ((HexagonAtoms557.assocBCA) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = rows_assocBCA ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_3_0 : (tripleIndices 2 4 2).map ((HexagonAtoms557.assocBCA) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = rows_assocBCA ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_3_1 : (tripleIndices 2 4 2).map ((HexagonAtoms557.assocBCA) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = rows_assocBCA ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms557.assocBCA) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = rows_assocBCA ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms557.assocBCA) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = rows_assocBCA ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_0 : (tripleIndices 2 4 2).map ((HexagonAtoms557.assocBCA) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = rows_assocBCA ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_1 : (tripleIndices 2 4 2).map ((HexagonAtoms557.assocBCA) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = rows_assocBCA ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_2_0 : (tripleIndices 2 4 2).map ((HexagonAtoms557.assocBCA) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = rows_assocBCA ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_2_1 : (tripleIndices 2 4 2).map ((HexagonAtoms557.assocBCA) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = rows_assocBCA ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_3_0 : (tripleIndices 2 4 2).map ((HexagonAtoms557.assocBCA) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = rows_assocBCA ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_3_1 : (tripleIndices 2 4 2).map ((HexagonAtoms557.assocBCA) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = rows_assocBCA ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocBCA_data (r : RightIndex 5 7 5) : (tripleIndices 2 4 2).map ((HexagonAtoms557.assocBCA) r) = rows_assocBCA r := by
  fin_cases r
  · exact rows_assocBCA_eq_0_0_0
  · exact rows_assocBCA_eq_0_0_1
  · exact rows_assocBCA_eq_0_1_0
  · exact rows_assocBCA_eq_0_1_1
  · exact rows_assocBCA_eq_0_2_0
  · exact rows_assocBCA_eq_0_2_1
  · exact rows_assocBCA_eq_0_3_0
  · exact rows_assocBCA_eq_0_3_1
  · exact rows_assocBCA_eq_1_0_0
  · exact rows_assocBCA_eq_1_0_1
  · exact rows_assocBCA_eq_1_1_0
  · exact rows_assocBCA_eq_1_1_1
  · exact rows_assocBCA_eq_1_2_0
  · exact rows_assocBCA_eq_1_2_1
  · exact rows_assocBCA_eq_1_3_0
  · exact rows_assocBCA_eq_1_3_1

private def rows_assocCABData : List (List ℤ) := [decodeIntegerRow 16 3 1 37414780,
    decodeIntegerRow 16 3 1 16053420,
    decodeIntegerRow 16 3 1 25580496,
    decodeIntegerRow 16 3 1 34342768,
    decodeIntegerRow 16 3 1 8702380,
    decodeIntegerRow 16 3 1 25575620,
    decodeIntegerRow 16 3 1 16049552,
    decodeIntegerRow 16 3 1 5633296,
    decodeIntegerRow 16 3 1 26682260,
    decodeIntegerRow 16 3 1 37518460,
    decodeIntegerRow 16 3 1 34213168,
    decodeIntegerRow 16 3 1 17077424,
    decodeIntegerRow 16 3 1 17072580,
    decodeIntegerRow 16 3 1 8835220,
    decodeIntegerRow 16 3 1 5527024,
    decodeIntegerRow 16 3 1 26678352]

def rows_assocCAB (r : RightIndex 7 5 5) : List ℤ := rows_assocCABData.getD (rightPosition 7 5 5 r) []

private theorem rows_assocCAB_eq_0_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms557.assocCAB) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = rows_assocCAB ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms557.assocCAB) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = rows_assocCAB ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_0 : (tripleIndices 2 4 2).map ((HexagonAtoms557.assocCAB) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = rows_assocCAB ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_1 : (tripleIndices 2 4 2).map ((HexagonAtoms557.assocCAB) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = rows_assocCAB ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms557.assocCAB) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = rows_assocCAB ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms557.assocCAB) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = rows_assocCAB ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_0 : (tripleIndices 2 4 2).map ((HexagonAtoms557.assocCAB) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = rows_assocCAB ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_1 : (tripleIndices 2 4 2).map ((HexagonAtoms557.assocCAB) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = rows_assocCAB ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms557.assocCAB) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = rows_assocCAB ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms557.assocCAB) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = rows_assocCAB ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_1_0 : (tripleIndices 2 4 2).map ((HexagonAtoms557.assocCAB) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = rows_assocCAB ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_1_1 : (tripleIndices 2 4 2).map ((HexagonAtoms557.assocCAB) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = rows_assocCAB ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms557.assocCAB) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = rows_assocCAB ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms557.assocCAB) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = rows_assocCAB ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_1_0 : (tripleIndices 2 4 2).map ((HexagonAtoms557.assocCAB) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = rows_assocCAB ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_1_1 : (tripleIndices 2 4 2).map ((HexagonAtoms557.assocCAB) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = rows_assocCAB ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocCAB_data (r : RightIndex 7 5 5) : (tripleIndices 2 4 2).map ((HexagonAtoms557.assocCAB) r) = rows_assocCAB r := by
  fin_cases r
  · exact rows_assocCAB_eq_0_0_0
  · exact rows_assocCAB_eq_0_0_1
  · exact rows_assocCAB_eq_0_1_0
  · exact rows_assocCAB_eq_0_1_1
  · exact rows_assocCAB_eq_1_0_0
  · exact rows_assocCAB_eq_1_0_1
  · exact rows_assocCAB_eq_1_1_0
  · exact rows_assocCAB_eq_1_1_1
  · exact rows_assocCAB_eq_2_0_0
  · exact rows_assocCAB_eq_2_0_1
  · exact rows_assocCAB_eq_2_1_0
  · exact rows_assocCAB_eq_2_1_1
  · exact rows_assocCAB_eq_3_0_0
  · exact rows_assocCAB_eq_3_0_1
  · exact rows_assocCAB_eq_3_1_0
  · exact rows_assocCAB_eq_3_1_1

private def cols_innerABCData : List (List ℤ) := [decodeIntegerRow 16 3 1 6472900,
    decodeIntegerRow 16 3 1 24792980,
    decodeIntegerRow 16 3 1 15187568,
    decodeIntegerRow 16 3 1 7888624,
    decodeIntegerRow 16 3 1 7890580,
    decodeIntegerRow 16 3 1 27863420,
    decodeIntegerRow 16 3 1 24788496,
    decodeIntegerRow 16 3 1 36574768,
    decodeIntegerRow 16 3 1 15108780,
    decodeIntegerRow 16 3 1 7521220,
    decodeIntegerRow 16 3 1 36232624,
    decodeIntegerRow 16 3 1 18411152,
    decodeIntegerRow 16 3 1 24630980,
    decodeIntegerRow 16 3 1 36233620,
    decodeIntegerRow 16 3 1 35523568,
    decodeIntegerRow 16 3 1 15104624]

def cols_innerABC (r : LeftIndex 5 5 7) : List ℤ := cols_innerABCData.getD (leftPosition 5 5 7 r) []

private theorem cols_innerABC_eq_0_0_0 : (tripleIndices 4 2 2).map (fun j => (HexagonAtoms557.innerABC) j ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = cols_innerABC ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_0_1 : (tripleIndices 4 2 2).map (fun j => (HexagonAtoms557.innerABC) j ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = cols_innerABC ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_1_0 : (tripleIndices 4 2 2).map (fun j => (HexagonAtoms557.innerABC) j ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = cols_innerABC ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_1_1 : (tripleIndices 4 2 2).map (fun j => (HexagonAtoms557.innerABC) j ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = cols_innerABC ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_0_0 : (tripleIndices 4 2 2).map (fun j => (HexagonAtoms557.innerABC) j ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = cols_innerABC ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_0_1 : (tripleIndices 4 2 2).map (fun j => (HexagonAtoms557.innerABC) j ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = cols_innerABC ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_1_0 : (tripleIndices 4 2 2).map (fun j => (HexagonAtoms557.innerABC) j ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = cols_innerABC ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_1_1 : (tripleIndices 4 2 2).map (fun j => (HexagonAtoms557.innerABC) j ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = cols_innerABC ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_2_0_0 : (tripleIndices 4 2 2).map (fun j => (HexagonAtoms557.innerABC) j ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = cols_innerABC ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_2_0_1 : (tripleIndices 4 2 2).map (fun j => (HexagonAtoms557.innerABC) j ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = cols_innerABC ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_2_1_0 : (tripleIndices 4 2 2).map (fun j => (HexagonAtoms557.innerABC) j ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = cols_innerABC ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_2_1_1 : (tripleIndices 4 2 2).map (fun j => (HexagonAtoms557.innerABC) j ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = cols_innerABC ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_3_0_0 : (tripleIndices 4 2 2).map (fun j => (HexagonAtoms557.innerABC) j ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = cols_innerABC ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_3_0_1 : (tripleIndices 4 2 2).map (fun j => (HexagonAtoms557.innerABC) j ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = cols_innerABC ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_3_1_0 : (tripleIndices 4 2 2).map (fun j => (HexagonAtoms557.innerABC) j ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = cols_innerABC ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_3_1_1 : (tripleIndices 4 2 2).map (fun j => (HexagonAtoms557.innerABC) j ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = cols_innerABC ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_innerABC_data (r : LeftIndex 5 5 7) : (tripleIndices 4 2 2).map (fun j => (HexagonAtoms557.innerABC) j r) = cols_innerABC r := by
  fin_cases r
  · exact cols_innerABC_eq_0_0_0
  · exact cols_innerABC_eq_0_0_1
  · exact cols_innerABC_eq_0_1_0
  · exact cols_innerABC_eq_0_1_1
  · exact cols_innerABC_eq_1_0_0
  · exact cols_innerABC_eq_1_0_1
  · exact cols_innerABC_eq_1_1_0
  · exact cols_innerABC_eq_1_1_1
  · exact cols_innerABC_eq_2_0_0
  · exact cols_innerABC_eq_2_0_1
  · exact cols_innerABC_eq_2_1_0
  · exact cols_innerABC_eq_2_1_1
  · exact cols_innerABC_eq_3_0_0
  · exact cols_innerABC_eq_3_0_1
  · exact cols_innerABC_eq_3_1_0
  · exact cols_innerABC_eq_3_1_1

private def cols_right0Data : List (List ℤ) := [decodeIntegerRow 16 3 1 21720200,
    decodeIntegerRow 16 3 1 21457780,
    decodeIntegerRow 16 3 1 34278592,
    decodeIntegerRow 16 3 1 17273776,
    decodeIntegerRow 16 3 1 21326540,
    decodeIntegerRow 16 3 1 21589000,
    decodeIntegerRow 16 3 1 34277296,
    decodeIntegerRow 16 3 1 17269888,
    decodeIntegerRow 16 3 1 21575824,
    decodeIntegerRow 16 3 1 21680832,
    decodeIntegerRow 16 3 1 26835340,
    decodeIntegerRow 16 3 1 37467400,
    decodeIntegerRow 16 3 1 21470848,
    decodeIntegerRow 16 3 1 21365904,
    decodeIntegerRow 16 3 1 26840200,
    decodeIntegerRow 16 3 1 37465780]

def cols_right0 (r : LeftIndex 5 5 7) : List ℤ := cols_right0Data.getD (leftPosition 5 5 7 r) []

private theorem cols_right0_eq_0_0_0 : (tripleIndices 2 4 2).map (fun j => (right0Middle5 5 7) j ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = cols_right0 ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_1 : (tripleIndices 2 4 2).map (fun j => (right0Middle5 5 7) j ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = cols_right0 ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_0 : (tripleIndices 2 4 2).map (fun j => (right0Middle5 5 7) j ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = cols_right0 ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_1 : (tripleIndices 2 4 2).map (fun j => (right0Middle5 5 7) j ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = cols_right0 ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_0 : (tripleIndices 2 4 2).map (fun j => (right0Middle5 5 7) j ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = cols_right0 ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_1 : (tripleIndices 2 4 2).map (fun j => (right0Middle5 5 7) j ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = cols_right0 ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_0 : (tripleIndices 2 4 2).map (fun j => (right0Middle5 5 7) j ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = cols_right0 ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_1 : (tripleIndices 2 4 2).map (fun j => (right0Middle5 5 7) j ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = cols_right0 ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_0 : (tripleIndices 2 4 2).map (fun j => (right0Middle5 5 7) j ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = cols_right0 ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_1 : (tripleIndices 2 4 2).map (fun j => (right0Middle5 5 7) j ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = cols_right0 ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_1_0 : (tripleIndices 2 4 2).map (fun j => (right0Middle5 5 7) j ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = cols_right0 ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_1_1 : (tripleIndices 2 4 2).map (fun j => (right0Middle5 5 7) j ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = cols_right0 ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_0 : (tripleIndices 2 4 2).map (fun j => (right0Middle5 5 7) j ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = cols_right0 ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_1 : (tripleIndices 2 4 2).map (fun j => (right0Middle5 5 7) j ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = cols_right0 ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_1_0 : (tripleIndices 2 4 2).map (fun j => (right0Middle5 5 7) j ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = cols_right0 ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_1_1 : (tripleIndices 2 4 2).map (fun j => (right0Middle5 5 7) j ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = cols_right0 ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right0_data (r : LeftIndex 5 5 7) : (tripleIndices 2 4 2).map (fun j => (right0Middle5 5 7) j r) = cols_right0 r := by
  fin_cases r
  · exact cols_right0_eq_0_0_0
  · exact cols_right0_eq_0_0_1
  · exact cols_right0_eq_0_1_0
  · exact cols_right0_eq_0_1_1
  · exact cols_right0_eq_1_0_0
  · exact cols_right0_eq_1_0_1
  · exact cols_right0_eq_1_1_0
  · exact cols_right0_eq_1_1_1
  · exact cols_right0_eq_2_0_0
  · exact cols_right0_eq_2_0_1
  · exact cols_right0_eq_2_1_0
  · exact cols_right0_eq_2_1_1
  · exact cols_right0_eq_3_0_0
  · exact cols_right0_eq_3_0_1
  · exact cols_right0_eq_3_1_0
  · exact cols_right0_eq_3_1_1

private def cols_left0Data : List (List ℤ) := [decodeIntegerRow 16 3 1 21720200,
    decodeIntegerRow 16 3 1 21457780,
    decodeIntegerRow 16 3 1 34278592,
    decodeIntegerRow 16 3 1 17273776,
    decodeIntegerRow 16 3 1 21326540,
    decodeIntegerRow 16 3 1 21589000,
    decodeIntegerRow 16 3 1 34277296,
    decodeIntegerRow 16 3 1 17269888,
    decodeIntegerRow 16 3 1 21575824,
    decodeIntegerRow 16 3 1 21680832,
    decodeIntegerRow 16 3 1 26835340,
    decodeIntegerRow 16 3 1 37467400,
    decodeIntegerRow 16 3 1 21470848,
    decodeIntegerRow 16 3 1 21365904,
    decodeIntegerRow 16 3 1 26840200,
    decodeIntegerRow 16 3 1 37465780]

def cols_left0 (r : LeftIndex 5 5 7) : List ℤ := cols_left0Data.getD (leftPosition 5 5 7 r) []

private theorem cols_left0_eq_0_0_0 : (tripleIndices 2 4 2).map (fun j => (left0Middle5 5 7) j ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = cols_left0 ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_1 : (tripleIndices 2 4 2).map (fun j => (left0Middle5 5 7) j ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = cols_left0 ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_0 : (tripleIndices 2 4 2).map (fun j => (left0Middle5 5 7) j ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = cols_left0 ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_1 : (tripleIndices 2 4 2).map (fun j => (left0Middle5 5 7) j ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = cols_left0 ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_0 : (tripleIndices 2 4 2).map (fun j => (left0Middle5 5 7) j ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = cols_left0 ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_1 : (tripleIndices 2 4 2).map (fun j => (left0Middle5 5 7) j ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = cols_left0 ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_0 : (tripleIndices 2 4 2).map (fun j => (left0Middle5 5 7) j ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = cols_left0 ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_1 : (tripleIndices 2 4 2).map (fun j => (left0Middle5 5 7) j ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = cols_left0 ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_0 : (tripleIndices 2 4 2).map (fun j => (left0Middle5 5 7) j ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = cols_left0 ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_1 : (tripleIndices 2 4 2).map (fun j => (left0Middle5 5 7) j ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = cols_left0 ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_1_0 : (tripleIndices 2 4 2).map (fun j => (left0Middle5 5 7) j ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = cols_left0 ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_1_1 : (tripleIndices 2 4 2).map (fun j => (left0Middle5 5 7) j ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = cols_left0 ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_0 : (tripleIndices 2 4 2).map (fun j => (left0Middle5 5 7) j ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = cols_left0 ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_1 : (tripleIndices 2 4 2).map (fun j => (left0Middle5 5 7) j ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = cols_left0 ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_1_0 : (tripleIndices 2 4 2).map (fun j => (left0Middle5 5 7) j ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = cols_left0 ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_1_1 : (tripleIndices 2 4 2).map (fun j => (left0Middle5 5 7) j ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = cols_left0 ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_left0_data (r : LeftIndex 5 5 7) : (tripleIndices 2 4 2).map (fun j => (left0Middle5 5 7) j r) = cols_left0 r := by
  fin_cases r
  · exact cols_left0_eq_0_0_0
  · exact cols_left0_eq_0_0_1
  · exact cols_left0_eq_0_1_0
  · exact cols_left0_eq_0_1_1
  · exact cols_left0_eq_1_0_0
  · exact cols_left0_eq_1_0_1
  · exact cols_left0_eq_1_1_0
  · exact cols_left0_eq_1_1_1
  · exact cols_left0_eq_2_0_0
  · exact cols_left0_eq_2_0_1
  · exact cols_left0_eq_2_1_0
  · exact cols_left0_eq_2_1_1
  · exact cols_left0_eq_3_0_0
  · exact cols_left0_eq_3_0_1
  · exact cols_left0_eq_3_1_0
  · exact cols_left0_eq_3_1_1

private def cols_right2Data : List (List ℤ) := [decodeIntegerRow 16 3 1 5631940,
    decodeIntegerRow 16 3 1 26993300,
    decodeIntegerRow 16 3 1 17466224,
    decodeIntegerRow 16 3 1 8703952,
    decodeIntegerRow 16 3 1 34344340,
    decodeIntegerRow 16 3 1 17471100,
    decodeIntegerRow 16 3 1 26997168,
    decodeIntegerRow 16 3 1 37413424,
    decodeIntegerRow 16 3 1 16364460,
    decodeIntegerRow 16 3 1 5528260,
    decodeIntegerRow 16 3 1 8833552,
    decodeIntegerRow 16 3 1 25969296,
    decodeIntegerRow 16 3 1 25974140,
    decodeIntegerRow 16 3 1 34211500,
    decodeIntegerRow 16 3 1 37519696,
    decodeIntegerRow 16 3 1 16368368]

def cols_right2 (r : LeftIndex 5 5 7) : List ℤ := cols_right2Data.getD (leftPosition 5 5 7 r) []

private theorem cols_right2_eq_0_0_0 : (tripleIndices 2 4 2).map (fun j => (right2Middle5 5 7) j ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = cols_right2 ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_1 : (tripleIndices 2 4 2).map (fun j => (right2Middle5 5 7) j ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = cols_right2 ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_0 : (tripleIndices 2 4 2).map (fun j => (right2Middle5 5 7) j ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = cols_right2 ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_1 : (tripleIndices 2 4 2).map (fun j => (right2Middle5 5 7) j ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = cols_right2 ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_0 : (tripleIndices 2 4 2).map (fun j => (right2Middle5 5 7) j ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = cols_right2 ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_1 : (tripleIndices 2 4 2).map (fun j => (right2Middle5 5 7) j ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = cols_right2 ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_0 : (tripleIndices 2 4 2).map (fun j => (right2Middle5 5 7) j ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = cols_right2 ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_1 : (tripleIndices 2 4 2).map (fun j => (right2Middle5 5 7) j ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = cols_right2 ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_0 : (tripleIndices 2 4 2).map (fun j => (right2Middle5 5 7) j ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = cols_right2 ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_1 : (tripleIndices 2 4 2).map (fun j => (right2Middle5 5 7) j ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = cols_right2 ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_1_0 : (tripleIndices 2 4 2).map (fun j => (right2Middle5 5 7) j ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = cols_right2 ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_1_1 : (tripleIndices 2 4 2).map (fun j => (right2Middle5 5 7) j ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = cols_right2 ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_0 : (tripleIndices 2 4 2).map (fun j => (right2Middle5 5 7) j ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = cols_right2 ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_1 : (tripleIndices 2 4 2).map (fun j => (right2Middle5 5 7) j ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = cols_right2 ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_1_0 : (tripleIndices 2 4 2).map (fun j => (right2Middle5 5 7) j ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = cols_right2 ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_1_1 : (tripleIndices 2 4 2).map (fun j => (right2Middle5 5 7) j ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = cols_right2 ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right2_data (r : LeftIndex 5 5 7) : (tripleIndices 2 4 2).map (fun j => (right2Middle5 5 7) j r) = cols_right2 r := by
  fin_cases r
  · exact cols_right2_eq_0_0_0
  · exact cols_right2_eq_0_0_1
  · exact cols_right2_eq_0_1_0
  · exact cols_right2_eq_0_1_1
  · exact cols_right2_eq_1_0_0
  · exact cols_right2_eq_1_0_1
  · exact cols_right2_eq_1_1_0
  · exact cols_right2_eq_1_1_1
  · exact cols_right2_eq_2_0_0
  · exact cols_right2_eq_2_0_1
  · exact cols_right2_eq_2_1_0
  · exact cols_right2_eq_2_1_1
  · exact cols_right2_eq_3_0_0
  · exact cols_right2_eq_3_0_1
  · exact cols_right2_eq_3_1_0
  · exact cols_right2_eq_3_1_1

theorem product0_eq : HexagonAtoms557.outerABC * HexagonAtoms557.assocABC = HexagonAtoms557.assocABC :=
  Matrix.one_mul (m := Fin 2 × Fin 4 × Fin 2) (n := Fin 4 × Fin 2 × Fin 2) _

theorem product1_eq : HexagonAtoms557.assocABC * HexagonAtoms557.innerABC = rowColumnMul rows_assocABC cols_innerABC :=
  (rowColumnMul_eq _ _ _ _ rows_assocABC_data cols_innerABC_data).symm

theorem product2_eq : HexagonAtoms557.innerRightABC * HexagonAtoms557.assocABC = HexagonAtoms557.assocABC :=
  Matrix.one_mul (m := Fin 2 × Fin 4 × Fin 2) (n := Fin 4 × Fin 2 × Fin 2) _

theorem product3_eq : HexagonAtoms557.inverseACB * right0Middle5 5 7 = rowColumnMul rows_inverseACB cols_right0 :=
  (rowColumnMul_eq _ _ _ _ rows_inverseACB_data cols_right0_data).symm

theorem product4_eq : HexagonAtoms557.innerACB * right1Middle5 5 7 = right1Middle5 5 7 :=
  Matrix.one_mul (m := Fin 2 × Fin 4 × Fin 2) (n := Fin 4 × Fin 2 × Fin 2) _

theorem product5_eq : HexagonAtoms557.assocBCA * left0Middle5 5 7 = rowColumnMul rows_assocBCA cols_left0 :=
  (rowColumnMul_eq _ _ _ _ rows_assocBCA_data cols_left0_data).symm

theorem product6_eq : HexagonAtoms557.innerRightABC * left1Middle5 5 7 = left1Middle5 5 7 :=
  Matrix.one_mul (m := Fin 2 × Fin 4 × Fin 2) (n := Fin 4 × Fin 2 × Fin 2) _

theorem product7_eq : HexagonAtoms557.assocCAB * right2Middle5 5 7 = rowColumnMul rows_assocCAB cols_right2 :=
  (rowColumnMul_eq _ _ _ _ rows_assocCAB_data cols_right2_data).symm

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn557
