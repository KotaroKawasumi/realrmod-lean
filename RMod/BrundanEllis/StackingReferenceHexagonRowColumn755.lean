import RMod.BrundanEllis.StackingReferenceHexagonAtoms755
import RMod.BrundanEllis.StackingReferenceHexagonMiddle7
import RMod.BrundanEllis.StackingReferenceRowColumnCheck

/-! Verified row and column lists. Each subsequent scalar product traverses
these lists directly, without repeated lookup into the original matrices. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn755
open Superfusion

theorem innerACB_alias : HexagonAtoms755.innerACB = HexagonAtoms755.innerABC :=
  HexagonAtoms755.innerACB_eq.symm.trans HexagonAtoms755.innerABC_eq

theorem assocCAB_alias : HexagonAtoms755.assocCAB = HexagonAtoms755.assocBAC :=
  HexagonAtoms755.assocCAB_eq.symm.trans HexagonAtoms755.assocBAC_eq

private def rows_innerRightABCData : List (List ℤ) := [decodeIntegerRow 16 3 1 36573820,
    decodeIntegerRow 16 3 1 18253740,
    decodeIntegerRow 16 3 1 27859152,
    decodeIntegerRow 16 3 1 35158096,
    decodeIntegerRow 16 3 1 35156140,
    decodeIntegerRow 16 3 1 15183300,
    decodeIntegerRow 16 3 1 18258224,
    decodeIntegerRow 16 3 1 6471952,
    decodeIntegerRow 16 3 1 27937940,
    decodeIntegerRow 16 3 1 35525500,
    decodeIntegerRow 16 3 1 6814096,
    decodeIntegerRow 16 3 1 24635568,
    decodeIntegerRow 16 3 1 18415740,
    decodeIntegerRow 16 3 1 6813100,
    decodeIntegerRow 16 3 1 7523152,
    decodeIntegerRow 16 3 1 27942096]

def rows_innerRightABC (r : RightIndex 7 5 5) : List ℤ := rows_innerRightABCData.getD (rightPosition 7 5 5 r) []

private theorem rows_innerRightABC_eq_0_0_0 : (tripleIndices 4 2 2).map ((HexagonAtoms755.innerRightABC) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = rows_innerRightABC ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_0_1 : (tripleIndices 4 2 2).map ((HexagonAtoms755.innerRightABC) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = rows_innerRightABC ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_1_0 : (tripleIndices 4 2 2).map ((HexagonAtoms755.innerRightABC) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = rows_innerRightABC ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_1_1 : (tripleIndices 4 2 2).map ((HexagonAtoms755.innerRightABC) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = rows_innerRightABC ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_0_0 : (tripleIndices 4 2 2).map ((HexagonAtoms755.innerRightABC) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = rows_innerRightABC ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_0_1 : (tripleIndices 4 2 2).map ((HexagonAtoms755.innerRightABC) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = rows_innerRightABC ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_1_0 : (tripleIndices 4 2 2).map ((HexagonAtoms755.innerRightABC) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = rows_innerRightABC ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_1_1 : (tripleIndices 4 2 2).map ((HexagonAtoms755.innerRightABC) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = rows_innerRightABC ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_2_0_0 : (tripleIndices 4 2 2).map ((HexagonAtoms755.innerRightABC) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = rows_innerRightABC ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_2_0_1 : (tripleIndices 4 2 2).map ((HexagonAtoms755.innerRightABC) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = rows_innerRightABC ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_2_1_0 : (tripleIndices 4 2 2).map ((HexagonAtoms755.innerRightABC) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = rows_innerRightABC ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_2_1_1 : (tripleIndices 4 2 2).map ((HexagonAtoms755.innerRightABC) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = rows_innerRightABC ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_3_0_0 : (tripleIndices 4 2 2).map ((HexagonAtoms755.innerRightABC) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = rows_innerRightABC ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_3_0_1 : (tripleIndices 4 2 2).map ((HexagonAtoms755.innerRightABC) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = rows_innerRightABC ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_3_1_0 : (tripleIndices 4 2 2).map ((HexagonAtoms755.innerRightABC) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = rows_innerRightABC ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_3_1_1 : (tripleIndices 4 2 2).map ((HexagonAtoms755.innerRightABC) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = rows_innerRightABC ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_innerRightABC_data (r : RightIndex 7 5 5) : (tripleIndices 4 2 2).map ((HexagonAtoms755.innerRightABC) r) = rows_innerRightABC r := by
  fin_cases r
  · exact rows_innerRightABC_eq_0_0_0
  · exact rows_innerRightABC_eq_0_0_1
  · exact rows_innerRightABC_eq_0_1_0
  · exact rows_innerRightABC_eq_0_1_1
  · exact rows_innerRightABC_eq_1_0_0
  · exact rows_innerRightABC_eq_1_0_1
  · exact rows_innerRightABC_eq_1_1_0
  · exact rows_innerRightABC_eq_1_1_1
  · exact rows_innerRightABC_eq_2_0_0
  · exact rows_innerRightABC_eq_2_0_1
  · exact rows_innerRightABC_eq_2_1_0
  · exact rows_innerRightABC_eq_2_1_1
  · exact rows_innerRightABC_eq_3_0_0
  · exact rows_innerRightABC_eq_3_0_1
  · exact rows_innerRightABC_eq_3_1_0
  · exact rows_innerRightABC_eq_3_1_1

private def rows_inverseACBData : List (List ℤ) := [decodeIntegerRow 16 3 1 6827680,
    decodeIntegerRow 16 3 1 24674720,
    decodeIntegerRow 16 3 1 7535800,
    decodeIntegerRow 16 3 1 27981680,
    decodeIntegerRow 16 3 1 27977088,
    decodeIntegerRow 16 3 1 35511904,
    decodeIntegerRow 16 3 1 18376160,
    decodeIntegerRow 16 3 1 6825760,
    decodeIntegerRow 16 3 1 27819680,
    decodeIntegerRow 16 3 1 35170720,
    decodeIntegerRow 16 3 1 18297480,
    decodeIntegerRow 16 3 1 6458320,
    decodeIntegerRow 16 3 1 36586432,
    decodeIntegerRow 16 3 1 18293216,
    decodeIntegerRow 16 3 1 35169760,
    decodeIntegerRow 16 3 1 15222560]

def rows_inverseACB (r : LeftIndex 7 5 5) : List ℤ := rows_inverseACBData.getD (leftPosition 7 5 5 r) []

private theorem rows_inverseACB_eq_0_0_0 : (tripleIndices 4 2 2).map ((HexagonAtoms755.inverseACB) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_1 : (tripleIndices 4 2 2).map ((HexagonAtoms755.inverseACB) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_0 : (tripleIndices 4 2 2).map ((HexagonAtoms755.inverseACB) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = rows_inverseACB ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_1 : (tripleIndices 4 2 2).map ((HexagonAtoms755.inverseACB) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = rows_inverseACB ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_2_0 : (tripleIndices 4 2 2).map ((HexagonAtoms755.inverseACB) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = rows_inverseACB ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_2_1 : (tripleIndices 4 2 2).map ((HexagonAtoms755.inverseACB) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = rows_inverseACB ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_3_0 : (tripleIndices 4 2 2).map ((HexagonAtoms755.inverseACB) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = rows_inverseACB ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_3_1 : (tripleIndices 4 2 2).map ((HexagonAtoms755.inverseACB) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = rows_inverseACB ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_0 : (tripleIndices 4 2 2).map ((HexagonAtoms755.inverseACB) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_1 : (tripleIndices 4 2 2).map ((HexagonAtoms755.inverseACB) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_0 : (tripleIndices 4 2 2).map ((HexagonAtoms755.inverseACB) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = rows_inverseACB ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_1 : (tripleIndices 4 2 2).map ((HexagonAtoms755.inverseACB) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = rows_inverseACB ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_2_0 : (tripleIndices 4 2 2).map ((HexagonAtoms755.inverseACB) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = rows_inverseACB ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_2_1 : (tripleIndices 4 2 2).map ((HexagonAtoms755.inverseACB) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = rows_inverseACB ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_3_0 : (tripleIndices 4 2 2).map ((HexagonAtoms755.inverseACB) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = rows_inverseACB ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_3_1 : (tripleIndices 4 2 2).map ((HexagonAtoms755.inverseACB) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = rows_inverseACB ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_inverseACB_data (r : LeftIndex 7 5 5) : (tripleIndices 4 2 2).map ((HexagonAtoms755.inverseACB) r) = rows_inverseACB r := by
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

private def rows_assocBCAData : List (List ℤ) := [decodeIntegerRow 16 3 1 19909436,
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

def rows_assocBCA (r : RightIndex 5 5 7) : List ℤ := rows_assocBCAData.getD (rightPosition 5 5 7 r) []

private theorem rows_assocBCA_eq_0_0_0 : (tripleIndices 4 2 2).map ((HexagonAtoms755.assocBCA) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = rows_assocBCA ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_1 : (tripleIndices 4 2 2).map ((HexagonAtoms755.assocBCA) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = rows_assocBCA ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_0 : (tripleIndices 4 2 2).map ((HexagonAtoms755.assocBCA) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = rows_assocBCA ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_1 : (tripleIndices 4 2 2).map ((HexagonAtoms755.assocBCA) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = rows_assocBCA ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_2_0 : (tripleIndices 4 2 2).map ((HexagonAtoms755.assocBCA) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = rows_assocBCA ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_2_1 : (tripleIndices 4 2 2).map ((HexagonAtoms755.assocBCA) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = rows_assocBCA ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_3_0 : (tripleIndices 4 2 2).map ((HexagonAtoms755.assocBCA) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = rows_assocBCA ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_3_1 : (tripleIndices 4 2 2).map ((HexagonAtoms755.assocBCA) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = rows_assocBCA ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_0 : (tripleIndices 4 2 2).map ((HexagonAtoms755.assocBCA) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = rows_assocBCA ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_1 : (tripleIndices 4 2 2).map ((HexagonAtoms755.assocBCA) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = rows_assocBCA ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_0 : (tripleIndices 4 2 2).map ((HexagonAtoms755.assocBCA) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = rows_assocBCA ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_1 : (tripleIndices 4 2 2).map ((HexagonAtoms755.assocBCA) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = rows_assocBCA ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_2_0 : (tripleIndices 4 2 2).map ((HexagonAtoms755.assocBCA) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = rows_assocBCA ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_2_1 : (tripleIndices 4 2 2).map ((HexagonAtoms755.assocBCA) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = rows_assocBCA ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_3_0 : (tripleIndices 4 2 2).map ((HexagonAtoms755.assocBCA) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = rows_assocBCA ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_3_1 : (tripleIndices 4 2 2).map ((HexagonAtoms755.assocBCA) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = rows_assocBCA ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocBCA_data (r : RightIndex 5 5 7) : (tripleIndices 4 2 2).map ((HexagonAtoms755.assocBCA) r) = rows_assocBCA r := by
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

private def rows_assocBACData : List (List ℤ) := [decodeIntegerRow 16 3 1 21582490,
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

def rows_assocBAC (r : RightIndex 5 7 5) : List ℤ := rows_assocBACData.getD (rightPosition 5 7 5 r) []

private theorem rows_assocBAC_eq_0_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms755.assocBAC) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = rows_assocBAC ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms755.assocBAC) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = rows_assocBAC ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_1_0 : (tripleIndices 2 4 2).map ((HexagonAtoms755.assocBAC) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = rows_assocBAC ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_1_1 : (tripleIndices 2 4 2).map ((HexagonAtoms755.assocBAC) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = rows_assocBAC ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_2_0 : (tripleIndices 2 4 2).map ((HexagonAtoms755.assocBAC) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = rows_assocBAC ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_2_1 : (tripleIndices 2 4 2).map ((HexagonAtoms755.assocBAC) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = rows_assocBAC ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_3_0 : (tripleIndices 2 4 2).map ((HexagonAtoms755.assocBAC) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = rows_assocBAC ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_3_1 : (tripleIndices 2 4 2).map ((HexagonAtoms755.assocBAC) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = rows_assocBAC ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms755.assocBAC) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = rows_assocBAC ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms755.assocBAC) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = rows_assocBAC ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_1_0 : (tripleIndices 2 4 2).map ((HexagonAtoms755.assocBAC) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = rows_assocBAC ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_1_1 : (tripleIndices 2 4 2).map ((HexagonAtoms755.assocBAC) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = rows_assocBAC ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_2_0 : (tripleIndices 2 4 2).map ((HexagonAtoms755.assocBAC) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = rows_assocBAC ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_2_1 : (tripleIndices 2 4 2).map ((HexagonAtoms755.assocBAC) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = rows_assocBAC ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_3_0 : (tripleIndices 2 4 2).map ((HexagonAtoms755.assocBAC) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = rows_assocBAC ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_3_1 : (tripleIndices 2 4 2).map ((HexagonAtoms755.assocBAC) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = rows_assocBAC ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocBAC_data (r : RightIndex 5 7 5) : (tripleIndices 2 4 2).map ((HexagonAtoms755.assocBAC) r) = rows_assocBAC r := by
  fin_cases r
  · exact rows_assocBAC_eq_0_0_0
  · exact rows_assocBAC_eq_0_0_1
  · exact rows_assocBAC_eq_0_1_0
  · exact rows_assocBAC_eq_0_1_1
  · exact rows_assocBAC_eq_0_2_0
  · exact rows_assocBAC_eq_0_2_1
  · exact rows_assocBAC_eq_0_3_0
  · exact rows_assocBAC_eq_0_3_1
  · exact rows_assocBAC_eq_1_0_0
  · exact rows_assocBAC_eq_1_0_1
  · exact rows_assocBAC_eq_1_1_0
  · exact rows_assocBAC_eq_1_1_1
  · exact rows_assocBAC_eq_1_2_0
  · exact rows_assocBAC_eq_1_2_1
  · exact rows_assocBAC_eq_1_3_0
  · exact rows_assocBAC_eq_1_3_1

private def cols_assocABCData : List (List ℤ) := [decodeIntegerRow 16 3 1 6827680,
    decodeIntegerRow 16 3 1 24674720,
    decodeIntegerRow 16 3 1 7535800,
    decodeIntegerRow 16 3 1 27981680,
    decodeIntegerRow 16 3 1 27977088,
    decodeIntegerRow 16 3 1 35511904,
    decodeIntegerRow 16 3 1 18376160,
    decodeIntegerRow 16 3 1 6825760,
    decodeIntegerRow 16 3 1 27819680,
    decodeIntegerRow 16 3 1 35170720,
    decodeIntegerRow 16 3 1 18297480,
    decodeIntegerRow 16 3 1 6458320,
    decodeIntegerRow 16 3 1 36586432,
    decodeIntegerRow 16 3 1 18293216,
    decodeIntegerRow 16 3 1 35169760,
    decodeIntegerRow 16 3 1 15222560]

def cols_assocABC (r : LeftIndex 7 5 5) : List ℤ := cols_assocABCData.getD (leftPosition 7 5 5 r) []

private theorem cols_assocABC_eq_0_0_0 : (tripleIndices 4 2 2).map (fun j => (HexagonAtoms755.assocABC) j ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = cols_assocABC ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_1 : (tripleIndices 4 2 2).map (fun j => (HexagonAtoms755.assocABC) j ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = cols_assocABC ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_0 : (tripleIndices 4 2 2).map (fun j => (HexagonAtoms755.assocABC) j ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = cols_assocABC ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_1 : (tripleIndices 4 2 2).map (fun j => (HexagonAtoms755.assocABC) j ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = cols_assocABC ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_2_0 : (tripleIndices 4 2 2).map (fun j => (HexagonAtoms755.assocABC) j ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = cols_assocABC ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_2_1 : (tripleIndices 4 2 2).map (fun j => (HexagonAtoms755.assocABC) j ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = cols_assocABC ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_3_0 : (tripleIndices 4 2 2).map (fun j => (HexagonAtoms755.assocABC) j ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = cols_assocABC ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_3_1 : (tripleIndices 4 2 2).map (fun j => (HexagonAtoms755.assocABC) j ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = cols_assocABC ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_0 : (tripleIndices 4 2 2).map (fun j => (HexagonAtoms755.assocABC) j ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = cols_assocABC ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_1 : (tripleIndices 4 2 2).map (fun j => (HexagonAtoms755.assocABC) j ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = cols_assocABC ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_1_0 : (tripleIndices 4 2 2).map (fun j => (HexagonAtoms755.assocABC) j ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = cols_assocABC ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_1_1 : (tripleIndices 4 2 2).map (fun j => (HexagonAtoms755.assocABC) j ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = cols_assocABC ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_2_0 : (tripleIndices 4 2 2).map (fun j => (HexagonAtoms755.assocABC) j ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = cols_assocABC ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_2_1 : (tripleIndices 4 2 2).map (fun j => (HexagonAtoms755.assocABC) j ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = cols_assocABC ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_3_0 : (tripleIndices 4 2 2).map (fun j => (HexagonAtoms755.assocABC) j ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = cols_assocABC ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_3_1 : (tripleIndices 4 2 2).map (fun j => (HexagonAtoms755.assocABC) j ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = cols_assocABC ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_assocABC_data (r : LeftIndex 7 5 5) : (tripleIndices 4 2 2).map (fun j => (HexagonAtoms755.assocABC) j r) = cols_assocABC r := by
  fin_cases r
  · exact cols_assocABC_eq_0_0_0
  · exact cols_assocABC_eq_0_0_1
  · exact cols_assocABC_eq_0_1_0
  · exact cols_assocABC_eq_0_1_1
  · exact cols_assocABC_eq_0_2_0
  · exact cols_assocABC_eq_0_2_1
  · exact cols_assocABC_eq_0_3_0
  · exact cols_assocABC_eq_0_3_1
  · exact cols_assocABC_eq_1_0_0
  · exact cols_assocABC_eq_1_0_1
  · exact cols_assocABC_eq_1_1_0
  · exact cols_assocABC_eq_1_1_1
  · exact cols_assocABC_eq_1_2_0
  · exact cols_assocABC_eq_1_2_1
  · exact cols_assocABC_eq_1_3_0
  · exact cols_assocABC_eq_1_3_1

private def cols_right0Data : List (List ℤ) := [decodeIntegerRow 16 9 4 936679107394944,
    decodeIntegerRow 16 9 4 925380203856880,
    decodeIntegerRow 16 9 4 916341081404400,
    decodeIntegerRow 16 9 4 927639984522496,
    decodeIntegerRow 16 9 4 1749949096440640,
    decodeIntegerRow 16 9 4 835016852614720,
    decodeIntegerRow 16 9 4 1749949100691520,
    decodeIntegerRow 16 9 4 835016890872640,
    decodeIntegerRow 16 9 4 925380548230720,
    decodeIntegerRow 16 9 4 916344180820800,
    decodeIntegerRow 16 9 4 927639640148800,
    decodeIntegerRow 16 9 4 936676008083520,
    decodeIntegerRow 16 9 4 834988958333680,
    decodeIntegerRow 16 9 4 102820043934976,
    decodeIntegerRow 16 9 4 834988996603264,
    decodeIntegerRow 16 9 4 102820039682800]

def cols_right0 (r : LeftIndex 7 5 5) : List ℤ := cols_right0Data.getD (leftPosition 7 5 5 r) []

private theorem cols_right0_eq_0_0_0 : (tripleIndices 4 2 2).map (fun j => (right0Middle7 5 5) j ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = cols_right0 ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_1 : (tripleIndices 4 2 2).map (fun j => (right0Middle7 5 5) j ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = cols_right0 ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_0 : (tripleIndices 4 2 2).map (fun j => (right0Middle7 5 5) j ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = cols_right0 ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_1 : (tripleIndices 4 2 2).map (fun j => (right0Middle7 5 5) j ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = cols_right0 ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_2_0 : (tripleIndices 4 2 2).map (fun j => (right0Middle7 5 5) j ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = cols_right0 ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_2_1 : (tripleIndices 4 2 2).map (fun j => (right0Middle7 5 5) j ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = cols_right0 ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_3_0 : (tripleIndices 4 2 2).map (fun j => (right0Middle7 5 5) j ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = cols_right0 ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_3_1 : (tripleIndices 4 2 2).map (fun j => (right0Middle7 5 5) j ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = cols_right0 ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_0 : (tripleIndices 4 2 2).map (fun j => (right0Middle7 5 5) j ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = cols_right0 ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_1 : (tripleIndices 4 2 2).map (fun j => (right0Middle7 5 5) j ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = cols_right0 ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_0 : (tripleIndices 4 2 2).map (fun j => (right0Middle7 5 5) j ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = cols_right0 ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_1 : (tripleIndices 4 2 2).map (fun j => (right0Middle7 5 5) j ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = cols_right0 ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_2_0 : (tripleIndices 4 2 2).map (fun j => (right0Middle7 5 5) j ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = cols_right0 ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_2_1 : (tripleIndices 4 2 2).map (fun j => (right0Middle7 5 5) j ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = cols_right0 ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_3_0 : (tripleIndices 4 2 2).map (fun j => (right0Middle7 5 5) j ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = cols_right0 ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_3_1 : (tripleIndices 4 2 2).map (fun j => (right0Middle7 5 5) j ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = cols_right0 ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right0_data (r : LeftIndex 7 5 5) : (tripleIndices 4 2 2).map (fun j => (right0Middle7 5 5) j r) = cols_right0 r := by
  fin_cases r
  · exact cols_right0_eq_0_0_0
  · exact cols_right0_eq_0_0_1
  · exact cols_right0_eq_0_1_0
  · exact cols_right0_eq_0_1_1
  · exact cols_right0_eq_0_2_0
  · exact cols_right0_eq_0_2_1
  · exact cols_right0_eq_0_3_0
  · exact cols_right0_eq_0_3_1
  · exact cols_right0_eq_1_0_0
  · exact cols_right0_eq_1_0_1
  · exact cols_right0_eq_1_1_0
  · exact cols_right0_eq_1_1_1
  · exact cols_right0_eq_1_2_0
  · exact cols_right0_eq_1_2_1
  · exact cols_right0_eq_1_3_0
  · exact cols_right0_eq_1_3_1

private def cols_left0Data : List (List ℤ) := [decodeIntegerRow 16 3 1 6827680,
    decodeIntegerRow 16 3 1 24674720,
    decodeIntegerRow 16 3 1 7535800,
    decodeIntegerRow 16 3 1 27981680,
    decodeIntegerRow 16 3 1 27977088,
    decodeIntegerRow 16 3 1 35511904,
    decodeIntegerRow 16 3 1 18376160,
    decodeIntegerRow 16 3 1 6825760,
    decodeIntegerRow 16 3 1 27819680,
    decodeIntegerRow 16 3 1 35170720,
    decodeIntegerRow 16 3 1 18297480,
    decodeIntegerRow 16 3 1 6458320,
    decodeIntegerRow 16 3 1 36586432,
    decodeIntegerRow 16 3 1 18293216,
    decodeIntegerRow 16 3 1 35169760,
    decodeIntegerRow 16 3 1 15222560]

def cols_left0 (r : LeftIndex 7 5 5) : List ℤ := cols_left0Data.getD (leftPosition 7 5 5 r) []

private theorem cols_left0_eq_0_0_0 : (tripleIndices 4 2 2).map (fun j => (left0Middle7 5 5) j ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = cols_left0 ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_1 : (tripleIndices 4 2 2).map (fun j => (left0Middle7 5 5) j ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = cols_left0 ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_0 : (tripleIndices 4 2 2).map (fun j => (left0Middle7 5 5) j ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = cols_left0 ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_1 : (tripleIndices 4 2 2).map (fun j => (left0Middle7 5 5) j ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = cols_left0 ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_2_0 : (tripleIndices 4 2 2).map (fun j => (left0Middle7 5 5) j ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = cols_left0 ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_2_1 : (tripleIndices 4 2 2).map (fun j => (left0Middle7 5 5) j ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = cols_left0 ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_3_0 : (tripleIndices 4 2 2).map (fun j => (left0Middle7 5 5) j ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = cols_left0 ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_3_1 : (tripleIndices 4 2 2).map (fun j => (left0Middle7 5 5) j ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = cols_left0 ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_0 : (tripleIndices 4 2 2).map (fun j => (left0Middle7 5 5) j ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = cols_left0 ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_1 : (tripleIndices 4 2 2).map (fun j => (left0Middle7 5 5) j ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = cols_left0 ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_0 : (tripleIndices 4 2 2).map (fun j => (left0Middle7 5 5) j ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = cols_left0 ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_1 : (tripleIndices 4 2 2).map (fun j => (left0Middle7 5 5) j ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = cols_left0 ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_2_0 : (tripleIndices 4 2 2).map (fun j => (left0Middle7 5 5) j ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = cols_left0 ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_2_1 : (tripleIndices 4 2 2).map (fun j => (left0Middle7 5 5) j ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = cols_left0 ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_3_0 : (tripleIndices 4 2 2).map (fun j => (left0Middle7 5 5) j ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = cols_left0 ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_3_1 : (tripleIndices 4 2 2).map (fun j => (left0Middle7 5 5) j ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = cols_left0 ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_left0_data (r : LeftIndex 7 5 5) : (tripleIndices 4 2 2).map (fun j => (left0Middle7 5 5) j r) = cols_left0 r := by
  fin_cases r
  · exact cols_left0_eq_0_0_0
  · exact cols_left0_eq_0_0_1
  · exact cols_left0_eq_0_1_0
  · exact cols_left0_eq_0_1_1
  · exact cols_left0_eq_0_2_0
  · exact cols_left0_eq_0_2_1
  · exact cols_left0_eq_0_3_0
  · exact cols_left0_eq_0_3_1
  · exact cols_left0_eq_1_0_0
  · exact cols_left0_eq_1_0_1
  · exact cols_left0_eq_1_1_0
  · exact cols_left0_eq_1_1_1
  · exact cols_left0_eq_1_2_0
  · exact cols_left0_eq_1_2_1
  · exact cols_left0_eq_1_3_0
  · exact cols_left0_eq_1_3_1

private def cols_right2Data : List (List ℤ) := [decodeIntegerRow 16 33 16 988992625236543222172960,
    decodeIntegerRow 16 33 16 988993409404984284762400,
    decodeIntegerRow 16 33 16 988111955067384262332640,
    decodeIntegerRow 16 33 16 989019286963518686743840,
    decodeIntegerRow 16 33 16 1018053907639820248927488,
    decodeIntegerRow 16 33 16 1948015728713126167661824,
    decodeIntegerRow 16 33 16 988992601473181294310656,
    decodeIntegerRow 16 33 16 988992600708797564562688,
    decodeIntegerRow 16 33 16 988992601474545084485920,
    decodeIntegerRow 16 33 16 988992600708756237587680,
    decodeIntegerRow 16 33 16 959931293822738629006560,
    decodeIntegerRow 16 33 16 29969472749432710271200,
    decodeIntegerRow 16 33 16 989873246395174614451456,
    decodeIntegerRow 16 33 16 988965914499040191225088,
    decodeIntegerRow 16 33 16 988992625236543184223488,
    decodeIntegerRow 16 33 16 988993409404983032429824]

def cols_right2 (r : LeftIndex 7 5 5) : List ℤ := cols_right2Data.getD (leftPosition 7 5 5 r) []

private theorem cols_right2_eq_0_0_0 : (tripleIndices 2 4 2).map (fun j => (right2Middle7 5 5) j ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = cols_right2 ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_1 : (tripleIndices 2 4 2).map (fun j => (right2Middle7 5 5) j ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = cols_right2 ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_0 : (tripleIndices 2 4 2).map (fun j => (right2Middle7 5 5) j ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = cols_right2 ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_1 : (tripleIndices 2 4 2).map (fun j => (right2Middle7 5 5) j ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = cols_right2 ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_2_0 : (tripleIndices 2 4 2).map (fun j => (right2Middle7 5 5) j ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = cols_right2 ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_2_1 : (tripleIndices 2 4 2).map (fun j => (right2Middle7 5 5) j ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = cols_right2 ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_3_0 : (tripleIndices 2 4 2).map (fun j => (right2Middle7 5 5) j ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = cols_right2 ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_3_1 : (tripleIndices 2 4 2).map (fun j => (right2Middle7 5 5) j ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = cols_right2 ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_0 : (tripleIndices 2 4 2).map (fun j => (right2Middle7 5 5) j ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = cols_right2 ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_1 : (tripleIndices 2 4 2).map (fun j => (right2Middle7 5 5) j ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = cols_right2 ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_0 : (tripleIndices 2 4 2).map (fun j => (right2Middle7 5 5) j ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = cols_right2 ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_1 : (tripleIndices 2 4 2).map (fun j => (right2Middle7 5 5) j ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = cols_right2 ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_2_0 : (tripleIndices 2 4 2).map (fun j => (right2Middle7 5 5) j ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = cols_right2 ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_2_1 : (tripleIndices 2 4 2).map (fun j => (right2Middle7 5 5) j ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = cols_right2 ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_3_0 : (tripleIndices 2 4 2).map (fun j => (right2Middle7 5 5) j ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = cols_right2 ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_3_1 : (tripleIndices 2 4 2).map (fun j => (right2Middle7 5 5) j ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = cols_right2 ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right2_data (r : LeftIndex 7 5 5) : (tripleIndices 2 4 2).map (fun j => (right2Middle7 5 5) j r) = cols_right2 r := by
  fin_cases r
  · exact cols_right2_eq_0_0_0
  · exact cols_right2_eq_0_0_1
  · exact cols_right2_eq_0_1_0
  · exact cols_right2_eq_0_1_1
  · exact cols_right2_eq_0_2_0
  · exact cols_right2_eq_0_2_1
  · exact cols_right2_eq_0_3_0
  · exact cols_right2_eq_0_3_1
  · exact cols_right2_eq_1_0_0
  · exact cols_right2_eq_1_0_1
  · exact cols_right2_eq_1_1_0
  · exact cols_right2_eq_1_1_1
  · exact cols_right2_eq_1_2_0
  · exact cols_right2_eq_1_2_1
  · exact cols_right2_eq_1_3_0
  · exact cols_right2_eq_1_3_1

theorem product0_eq : HexagonAtoms755.outerABC * HexagonAtoms755.assocABC = HexagonAtoms755.assocABC :=
  Matrix.one_mul (m := Fin 4 × Fin 2 × Fin 2) (n := Fin 2 × Fin 4 × Fin 2) _

theorem product1_eq : HexagonAtoms755.assocBAC * HexagonAtoms755.innerABC = HexagonAtoms755.assocBAC :=
  Matrix.mul_one (m := Fin 2 × Fin 4 × Fin 2) (n := Fin 2 × Fin 4 × Fin 2) _

theorem product2_eq : HexagonAtoms755.innerRightABC * HexagonAtoms755.assocABC = rowColumnMul rows_innerRightABC cols_assocABC :=
  (rowColumnMul_eq _ _ _ _ rows_innerRightABC_data cols_assocABC_data).symm

theorem product3_eq : HexagonAtoms755.inverseACB * right0Middle7 5 5 = rowColumnMul rows_inverseACB cols_right0 :=
  (rowColumnMul_eq _ _ _ _ rows_inverseACB_data cols_right0_data).symm

theorem product4_eq : HexagonAtoms755.innerABC * right1Middle7 5 5 = right1Middle7 5 5 :=
  Matrix.one_mul (m := Fin 2 × Fin 4 × Fin 2) (n := Fin 2 × Fin 4 × Fin 2) _

theorem product5_eq : HexagonAtoms755.assocBCA * left0Middle7 5 5 = rowColumnMul rows_assocBCA cols_left0 :=
  (rowColumnMul_eq _ _ _ _ rows_assocBCA_data cols_left0_data).symm

theorem product6_eq : HexagonAtoms755.innerRightBAC * left1Middle7 5 5 = left1Middle7 5 5 :=
  Matrix.one_mul (m := Fin 2 × Fin 4 × Fin 2) (n := Fin 2 × Fin 4 × Fin 2) _

theorem product7_eq : HexagonAtoms755.assocBAC * right2Middle7 5 5 = rowColumnMul rows_assocBAC cols_right2 :=
  (rowColumnMul_eq _ _ _ _ rows_assocBAC_data cols_right2_data).symm

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn755
