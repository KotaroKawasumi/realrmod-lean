import RMod.BrundanEllis.StackingReferenceHexagonAtoms622
import RMod.BrundanEllis.StackingReferenceHexagonMiddle6
import RMod.BrundanEllis.StackingReferenceRowColumnCheck

/-! Verified row and column lists. Each subsequent scalar product traverses
these lists directly, without repeated lookup into the original matrices. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn622
open Superfusion

theorem innerACB_alias : HexagonAtoms622.innerACB = HexagonAtoms622.innerABC :=
  HexagonAtoms622.innerACB_eq.symm.trans HexagonAtoms622.innerABC_eq

theorem assocCAB_alias : HexagonAtoms622.assocCAB = HexagonAtoms622.assocBAC :=
  HexagonAtoms622.assocCAB_eq.symm.trans HexagonAtoms622.assocBAC_eq

private def rows_innerRightABCData : List (List ℤ) := [decodeIntegerRow 16 3 1 21523387,
    decodeIntegerRow 16 3 1 21523369,
    decodeIntegerRow 16 3 1 21523357,
    decodeIntegerRow 16 3 1 21523359,
    decodeIntegerRow 16 3 1 21525547,
    decodeIntegerRow 16 3 1 21524089,
    decodeIntegerRow 16 3 1 21523117,
    decodeIntegerRow 16 3 1 21523279,
    decodeIntegerRow 16 3 1 26306329,
    decodeIntegerRow 16 3 1 7174453,
    decodeIntegerRow 16 3 1 20991919,
    decodeIntegerRow 16 3 1 23117683,
    decodeIntegerRow 16 3 1 21582409,
    decodeIntegerRow 16 3 1 21346213,
    decodeIntegerRow 16 3 1 21516799,
    decodeIntegerRow 16 3 1 21543043]

def rows_innerRightABC (r : RightIndex 6 2 2) : List ℤ := rows_innerRightABCData.getD (rightPosition 6 2 2 r) []

private theorem rows_innerRightABC_eq_0_0_0 : (tripleIndices 2 2 4).map ((HexagonAtoms622.innerRightABC) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = rows_innerRightABC ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_0_1 : (tripleIndices 2 2 4).map ((HexagonAtoms622.innerRightABC) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = rows_innerRightABC ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_0_2 : (tripleIndices 2 2 4).map ((HexagonAtoms622.innerRightABC) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = rows_innerRightABC ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_0_3 : (tripleIndices 2 2 4).map ((HexagonAtoms622.innerRightABC) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = rows_innerRightABC ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_1_0 : (tripleIndices 2 2 4).map ((HexagonAtoms622.innerRightABC) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = rows_innerRightABC ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_1_1 : (tripleIndices 2 2 4).map ((HexagonAtoms622.innerRightABC) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = rows_innerRightABC ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_1_2 : (tripleIndices 2 2 4).map ((HexagonAtoms622.innerRightABC) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = rows_innerRightABC ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_1_3 : (tripleIndices 2 2 4).map ((HexagonAtoms622.innerRightABC) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = rows_innerRightABC ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_0_0 : (tripleIndices 2 2 4).map ((HexagonAtoms622.innerRightABC) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = rows_innerRightABC ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_0_1 : (tripleIndices 2 2 4).map ((HexagonAtoms622.innerRightABC) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = rows_innerRightABC ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_0_2 : (tripleIndices 2 2 4).map ((HexagonAtoms622.innerRightABC) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = rows_innerRightABC ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_0_3 : (tripleIndices 2 2 4).map ((HexagonAtoms622.innerRightABC) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = rows_innerRightABC ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_1_0 : (tripleIndices 2 2 4).map ((HexagonAtoms622.innerRightABC) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = rows_innerRightABC ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_1_1 : (tripleIndices 2 2 4).map ((HexagonAtoms622.innerRightABC) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = rows_innerRightABC ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_1_2 : (tripleIndices 2 2 4).map ((HexagonAtoms622.innerRightABC) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = rows_innerRightABC ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_1_3 : (tripleIndices 2 2 4).map ((HexagonAtoms622.innerRightABC) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = rows_innerRightABC ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_innerRightABC_data (r : RightIndex 6 2 2) : (tripleIndices 2 2 4).map ((HexagonAtoms622.innerRightABC) r) = rows_innerRightABC r := by
  fin_cases r
  · exact rows_innerRightABC_eq_0_0_0
  · exact rows_innerRightABC_eq_0_0_1
  · exact rows_innerRightABC_eq_0_0_2
  · exact rows_innerRightABC_eq_0_0_3
  · exact rows_innerRightABC_eq_0_1_0
  · exact rows_innerRightABC_eq_0_1_1
  · exact rows_innerRightABC_eq_0_1_2
  · exact rows_innerRightABC_eq_0_1_3
  · exact rows_innerRightABC_eq_1_0_0
  · exact rows_innerRightABC_eq_1_0_1
  · exact rows_innerRightABC_eq_1_0_2
  · exact rows_innerRightABC_eq_1_0_3
  · exact rows_innerRightABC_eq_1_1_0
  · exact rows_innerRightABC_eq_1_1_1
  · exact rows_innerRightABC_eq_1_1_2
  · exact rows_innerRightABC_eq_1_1_3

private def rows_inverseACBData : List (List ℤ) := [decodeIntegerRow 16 3 1 21602066,
    decodeIntegerRow 16 3 1 21339646,
    decodeIntegerRow 16 3 1 21693958,
    decodeIntegerRow 16 3 1 21484022,
    decodeIntegerRow 16 3 1 21483966,
    decodeIntegerRow 16 3 1 21693934,
    decodeIntegerRow 16 3 1 21707062,
    decodeIntegerRow 16 3 1 21444602,
    decodeIntegerRow 16 3 1 24709738,
    decodeIntegerRow 16 3 1 7704922,
    decodeIntegerRow 16 3 1 6642526,
    decodeIntegerRow 16 3 1 27898546,
    decodeIntegerRow 16 3 1 15143962,
    decodeIntegerRow 16 3 1 36403222,
    decodeIntegerRow 16 3 1 7706866,
    decodeIntegerRow 16 3 1 24714274]

def rows_inverseACB (r : LeftIndex 6 2 2) : List ℤ := rows_inverseACBData.getD (leftPosition 6 2 2 r) []

private theorem rows_inverseACB_eq_0_0_0 : (tripleIndices 2 2 4).map ((HexagonAtoms622.inverseACB) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_1 : (tripleIndices 2 2 4).map ((HexagonAtoms622.inverseACB) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_2 : (tripleIndices 2 2 4).map ((HexagonAtoms622.inverseACB) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_3 : (tripleIndices 2 2 4).map ((HexagonAtoms622.inverseACB) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_0 : (tripleIndices 2 2 4).map ((HexagonAtoms622.inverseACB) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_1 : (tripleIndices 2 2 4).map ((HexagonAtoms622.inverseACB) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_2 : (tripleIndices 2 2 4).map ((HexagonAtoms622.inverseACB) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_3 : (tripleIndices 2 2 4).map ((HexagonAtoms622.inverseACB) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_0 : (tripleIndices 2 2 4).map ((HexagonAtoms622.inverseACB) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_1 : (tripleIndices 2 2 4).map ((HexagonAtoms622.inverseACB) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_2 : (tripleIndices 2 2 4).map ((HexagonAtoms622.inverseACB) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_3 : (tripleIndices 2 2 4).map ((HexagonAtoms622.inverseACB) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_0 : (tripleIndices 2 2 4).map ((HexagonAtoms622.inverseACB) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_1 : (tripleIndices 2 2 4).map ((HexagonAtoms622.inverseACB) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_2 : (tripleIndices 2 2 4).map ((HexagonAtoms622.inverseACB) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_3 : (tripleIndices 2 2 4).map ((HexagonAtoms622.inverseACB) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_inverseACB_data (r : LeftIndex 6 2 2) : (tripleIndices 2 2 4).map ((HexagonAtoms622.inverseACB) r) = rows_inverseACB r := by
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

private def rows_assocBCAData : List (List ℤ) := [decodeIntegerRow 16 3 1 6643040,
    decodeIntegerRow 16 3 1 15146080,
    decodeIntegerRow 16 3 1 18334720,
    decodeIntegerRow 16 3 1 7705920,
    decodeIntegerRow 16 3 1 7705868,
    decodeIntegerRow 16 3 1 18334708,
    decodeIntegerRow 16 3 1 27900664,
    decodeIntegerRow 16 3 1 36403736,
    decodeIntegerRow 16 3 1 21691840,
    decodeIntegerRow 16 3 1 21562240,
    decodeIntegerRow 16 3 1 21445600,
    decodeIntegerRow 16 3 1 21341920,
    decodeIntegerRow 16 3 1 21709336,
    decodeIntegerRow 16 3 1 21603064,
    decodeIntegerRow 16 3 1 21563212,
    decodeIntegerRow 16 3 1 21696052]

def rows_assocBCA (r : RightIndex 2 2 6) : List ℤ := rows_assocBCAData.getD (rightPosition 2 2 6 r) []

private theorem rows_assocBCA_eq_0_0_0 : (tripleIndices 2 2 4).map ((HexagonAtoms622.assocBCA) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_assocBCA ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_1 : (tripleIndices 2 2 4).map ((HexagonAtoms622.assocBCA) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_assocBCA ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_2 : (tripleIndices 2 2 4).map ((HexagonAtoms622.assocBCA) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_assocBCA ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_3 : (tripleIndices 2 2 4).map ((HexagonAtoms622.assocBCA) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_assocBCA ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_0 : (tripleIndices 2 2 4).map ((HexagonAtoms622.assocBCA) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_assocBCA ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_1 : (tripleIndices 2 2 4).map ((HexagonAtoms622.assocBCA) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_assocBCA ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_2 : (tripleIndices 2 2 4).map ((HexagonAtoms622.assocBCA) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_assocBCA ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_3 : (tripleIndices 2 2 4).map ((HexagonAtoms622.assocBCA) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_assocBCA ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_0 : (tripleIndices 2 2 4).map ((HexagonAtoms622.assocBCA) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_assocBCA ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_1 : (tripleIndices 2 2 4).map ((HexagonAtoms622.assocBCA) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_assocBCA ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_2 : (tripleIndices 2 2 4).map ((HexagonAtoms622.assocBCA) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_assocBCA ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_3 : (tripleIndices 2 2 4).map ((HexagonAtoms622.assocBCA) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_assocBCA ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_0 : (tripleIndices 2 2 4).map ((HexagonAtoms622.assocBCA) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_assocBCA ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_1 : (tripleIndices 2 2 4).map ((HexagonAtoms622.assocBCA) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_assocBCA ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_2 : (tripleIndices 2 2 4).map ((HexagonAtoms622.assocBCA) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_assocBCA ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_3 : (tripleIndices 2 2 4).map ((HexagonAtoms622.assocBCA) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_assocBCA ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocBCA_data (r : RightIndex 2 2 6) : (tripleIndices 2 2 4).map ((HexagonAtoms622.assocBCA) r) = rows_assocBCA r := by
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

private def rows_assocBACData : List (List ℤ) := [decodeIntegerRow 16 3 1 19988032,
    decodeIntegerRow 16 3 1 21877420,
    decodeIntegerRow 16 3 1 7167160,
    decodeIntegerRow 16 3 1 26323824,
    decodeIntegerRow 16 3 1 26328200,
    decodeIntegerRow 16 3 1 7168624,
    decodeIntegerRow 16 3 1 21168832,
    decodeIntegerRow 16 3 1 23058580,
    decodeIntegerRow 16 3 1 22232200,
    decodeIntegerRow 16 3 1 23176624,
    decodeIntegerRow 16 3 1 26288832,
    decodeIntegerRow 16 3 1 35864980,
    decodeIntegerRow 16 3 1 35866432,
    decodeIntegerRow 16 3 1 26284460,
    decodeIntegerRow 16 3 1 19869880,
    decodeIntegerRow 16 3 1 20815024]

def rows_assocBAC (r : RightIndex 2 6 2) : List ℤ := rows_assocBACData.getD (rightPosition 2 6 2 r) []

private theorem rows_assocBAC_eq_0_0_0 : (tripleIndices 4 1 4).map ((HexagonAtoms622.assocBAC) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_assocBAC ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_1 : (tripleIndices 4 1 4).map ((HexagonAtoms622.assocBAC) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_assocBAC ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_2 : (tripleIndices 4 1 4).map ((HexagonAtoms622.assocBAC) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_assocBAC ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_3 : (tripleIndices 4 1 4).map ((HexagonAtoms622.assocBAC) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_assocBAC ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_0 : (tripleIndices 4 1 4).map ((HexagonAtoms622.assocBAC) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_assocBAC ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_1 : (tripleIndices 4 1 4).map ((HexagonAtoms622.assocBAC) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_assocBAC ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_2 : (tripleIndices 4 1 4).map ((HexagonAtoms622.assocBAC) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_assocBAC ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_3 : (tripleIndices 4 1 4).map ((HexagonAtoms622.assocBAC) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_assocBAC ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_0_0 : (tripleIndices 4 1 4).map ((HexagonAtoms622.assocBAC) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_assocBAC ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_0_1 : (tripleIndices 4 1 4).map ((HexagonAtoms622.assocBAC) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_assocBAC ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_0_2 : (tripleIndices 4 1 4).map ((HexagonAtoms622.assocBAC) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_assocBAC ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_0_3 : (tripleIndices 4 1 4).map ((HexagonAtoms622.assocBAC) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_assocBAC ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_0_0 : (tripleIndices 4 1 4).map ((HexagonAtoms622.assocBAC) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_assocBAC ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_0_1 : (tripleIndices 4 1 4).map ((HexagonAtoms622.assocBAC) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_assocBAC ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_0_2 : (tripleIndices 4 1 4).map ((HexagonAtoms622.assocBAC) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_assocBAC ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_0_3 : (tripleIndices 4 1 4).map ((HexagonAtoms622.assocBAC) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_assocBAC ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocBAC_data (r : RightIndex 2 6 2) : (tripleIndices 4 1 4).map ((HexagonAtoms622.assocBAC) r) = rows_assocBAC r := by
  fin_cases r
  · exact rows_assocBAC_eq_0_0_0
  · exact rows_assocBAC_eq_0_0_1
  · exact rows_assocBAC_eq_0_0_2
  · exact rows_assocBAC_eq_0_0_3
  · exact rows_assocBAC_eq_1_0_0
  · exact rows_assocBAC_eq_1_0_1
  · exact rows_assocBAC_eq_1_0_2
  · exact rows_assocBAC_eq_1_0_3
  · exact rows_assocBAC_eq_2_0_0
  · exact rows_assocBAC_eq_2_0_1
  · exact rows_assocBAC_eq_2_0_2
  · exact rows_assocBAC_eq_2_0_3
  · exact rows_assocBAC_eq_3_0_0
  · exact rows_assocBAC_eq_3_0_1
  · exact rows_assocBAC_eq_3_0_2
  · exact rows_assocBAC_eq_3_0_3

private def cols_assocABCData : List (List ℤ) := [decodeIntegerRow 16 3 1 21602066,
    decodeIntegerRow 16 3 1 21339646,
    decodeIntegerRow 16 3 1 21693958,
    decodeIntegerRow 16 3 1 21484022,
    decodeIntegerRow 16 3 1 21483966,
    decodeIntegerRow 16 3 1 21693934,
    decodeIntegerRow 16 3 1 21707062,
    decodeIntegerRow 16 3 1 21444602,
    decodeIntegerRow 16 3 1 24709738,
    decodeIntegerRow 16 3 1 7704922,
    decodeIntegerRow 16 3 1 6642526,
    decodeIntegerRow 16 3 1 27898546,
    decodeIntegerRow 16 3 1 15143962,
    decodeIntegerRow 16 3 1 36403222,
    decodeIntegerRow 16 3 1 7706866,
    decodeIntegerRow 16 3 1 24714274]

def cols_assocABC (r : LeftIndex 6 2 2) : List ℤ := cols_assocABCData.getD (leftPosition 6 2 2 r) []

private theorem cols_assocABC_eq_0_0_0 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms622.assocABC) j ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_assocABC ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_1 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms622.assocABC) j ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_assocABC ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_2 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms622.assocABC) j ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_assocABC ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_3 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms622.assocABC) j ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_assocABC ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_0 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms622.assocABC) j ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_assocABC ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_1 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms622.assocABC) j ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_assocABC ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_2 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms622.assocABC) j ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_assocABC ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_3 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms622.assocABC) j ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_assocABC ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_0_0 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms622.assocABC) j ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_assocABC ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_0_1 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms622.assocABC) j ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_assocABC ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_0_2 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms622.assocABC) j ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_assocABC ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_0_3 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms622.assocABC) j ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_assocABC ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_0_0 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms622.assocABC) j ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_assocABC ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_0_1 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms622.assocABC) j ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_assocABC ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_0_2 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms622.assocABC) j ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_assocABC ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_0_3 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms622.assocABC) j ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_assocABC ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_assocABC_data (r : LeftIndex 6 2 2) : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms622.assocABC) j r) = cols_assocABC r := by
  fin_cases r
  · exact cols_assocABC_eq_0_0_0
  · exact cols_assocABC_eq_0_0_1
  · exact cols_assocABC_eq_0_0_2
  · exact cols_assocABC_eq_0_0_3
  · exact cols_assocABC_eq_1_0_0
  · exact cols_assocABC_eq_1_0_1
  · exact cols_assocABC_eq_1_0_2
  · exact cols_assocABC_eq_1_0_3
  · exact cols_assocABC_eq_2_0_0
  · exact cols_assocABC_eq_2_0_1
  · exact cols_assocABC_eq_2_0_2
  · exact cols_assocABC_eq_2_0_3
  · exact cols_assocABC_eq_3_0_0
  · exact cols_assocABC_eq_3_0_1
  · exact cols_assocABC_eq_3_0_2
  · exact cols_assocABC_eq_3_0_3

private def cols_right0Data : List (List ℤ) := [decodeIntegerRow 16 3 1 36403680,
    decodeIntegerRow 16 3 1 27900640,
    decodeIntegerRow 16 3 1 24712000,
    decodeIntegerRow 16 3 1 35340800,
    decodeIntegerRow 16 3 1 35340852,
    decodeIntegerRow 16 3 1 24712012,
    decodeIntegerRow 16 3 1 15146056,
    decodeIntegerRow 16 3 1 6642984,
    decodeIntegerRow 16 3 1 21354880,
    decodeIntegerRow 16 3 1 21484480,
    decodeIntegerRow 16 3 1 21601120,
    decodeIntegerRow 16 3 1 21704800,
    decodeIntegerRow 16 3 1 21337384,
    decodeIntegerRow 16 3 1 21443656,
    decodeIntegerRow 16 3 1 21483508,
    decodeIntegerRow 16 3 1 21350668]

def cols_right0 (r : LeftIndex 6 2 2) : List ℤ := cols_right0Data.getD (leftPosition 6 2 2 r) []

private theorem cols_right0_eq_0_0_0 : (tripleIndices 2 2 4).map (fun j => (right0Middle6 2 2) j ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_right0 ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_1 : (tripleIndices 2 2 4).map (fun j => (right0Middle6 2 2) j ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_right0 ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_2 : (tripleIndices 2 2 4).map (fun j => (right0Middle6 2 2) j ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_right0 ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_3 : (tripleIndices 2 2 4).map (fun j => (right0Middle6 2 2) j ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_right0 ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_0 : (tripleIndices 2 2 4).map (fun j => (right0Middle6 2 2) j ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_right0 ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_1 : (tripleIndices 2 2 4).map (fun j => (right0Middle6 2 2) j ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_right0 ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_2 : (tripleIndices 2 2 4).map (fun j => (right0Middle6 2 2) j ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_right0 ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_3 : (tripleIndices 2 2 4).map (fun j => (right0Middle6 2 2) j ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_right0 ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_0 : (tripleIndices 2 2 4).map (fun j => (right0Middle6 2 2) j ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_right0 ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_1 : (tripleIndices 2 2 4).map (fun j => (right0Middle6 2 2) j ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_right0 ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_2 : (tripleIndices 2 2 4).map (fun j => (right0Middle6 2 2) j ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_right0 ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_3 : (tripleIndices 2 2 4).map (fun j => (right0Middle6 2 2) j ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_right0 ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_0 : (tripleIndices 2 2 4).map (fun j => (right0Middle6 2 2) j ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_right0 ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_1 : (tripleIndices 2 2 4).map (fun j => (right0Middle6 2 2) j ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_right0 ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_2 : (tripleIndices 2 2 4).map (fun j => (right0Middle6 2 2) j ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_right0 ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_3 : (tripleIndices 2 2 4).map (fun j => (right0Middle6 2 2) j ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_right0 ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right0_data (r : LeftIndex 6 2 2) : (tripleIndices 2 2 4).map (fun j => (right0Middle6 2 2) j r) = cols_right0 r := by
  fin_cases r
  · exact cols_right0_eq_0_0_0
  · exact cols_right0_eq_0_0_1
  · exact cols_right0_eq_0_0_2
  · exact cols_right0_eq_0_0_3
  · exact cols_right0_eq_1_0_0
  · exact cols_right0_eq_1_0_1
  · exact cols_right0_eq_1_0_2
  · exact cols_right0_eq_1_0_3
  · exact cols_right0_eq_2_0_0
  · exact cols_right0_eq_2_0_1
  · exact cols_right0_eq_2_0_2
  · exact cols_right0_eq_2_0_3
  · exact cols_right0_eq_3_0_0
  · exact cols_right0_eq_3_0_1
  · exact cols_right0_eq_3_0_2
  · exact cols_right0_eq_3_0_3

private def cols_left0Data : List (List ℤ) := [decodeIntegerRow 16 3 1 21602066,
    decodeIntegerRow 16 3 1 21339646,
    decodeIntegerRow 16 3 1 21693958,
    decodeIntegerRow 16 3 1 21484022,
    decodeIntegerRow 16 3 1 21483966,
    decodeIntegerRow 16 3 1 21693934,
    decodeIntegerRow 16 3 1 21707062,
    decodeIntegerRow 16 3 1 21444602,
    decodeIntegerRow 16 3 1 24709738,
    decodeIntegerRow 16 3 1 7704922,
    decodeIntegerRow 16 3 1 6642526,
    decodeIntegerRow 16 3 1 27898546,
    decodeIntegerRow 16 3 1 15143962,
    decodeIntegerRow 16 3 1 36403222,
    decodeIntegerRow 16 3 1 7706866,
    decodeIntegerRow 16 3 1 24714274]

def cols_left0 (r : LeftIndex 6 2 2) : List ℤ := cols_left0Data.getD (leftPosition 6 2 2 r) []

private theorem cols_left0_eq_0_0_0 : (tripleIndices 2 2 4).map (fun j => (left0Middle6 2 2) j ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_left0 ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_1 : (tripleIndices 2 2 4).map (fun j => (left0Middle6 2 2) j ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_left0 ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_2 : (tripleIndices 2 2 4).map (fun j => (left0Middle6 2 2) j ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_left0 ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_3 : (tripleIndices 2 2 4).map (fun j => (left0Middle6 2 2) j ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_left0 ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_0 : (tripleIndices 2 2 4).map (fun j => (left0Middle6 2 2) j ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_left0 ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_1 : (tripleIndices 2 2 4).map (fun j => (left0Middle6 2 2) j ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_left0 ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_2 : (tripleIndices 2 2 4).map (fun j => (left0Middle6 2 2) j ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_left0 ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_3 : (tripleIndices 2 2 4).map (fun j => (left0Middle6 2 2) j ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_left0 ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_0 : (tripleIndices 2 2 4).map (fun j => (left0Middle6 2 2) j ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_left0 ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_1 : (tripleIndices 2 2 4).map (fun j => (left0Middle6 2 2) j ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_left0 ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_2 : (tripleIndices 2 2 4).map (fun j => (left0Middle6 2 2) j ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_left0 ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_3 : (tripleIndices 2 2 4).map (fun j => (left0Middle6 2 2) j ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_left0 ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_0 : (tripleIndices 2 2 4).map (fun j => (left0Middle6 2 2) j ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_left0 ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_1 : (tripleIndices 2 2 4).map (fun j => (left0Middle6 2 2) j ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_left0 ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_2 : (tripleIndices 2 2 4).map (fun j => (left0Middle6 2 2) j ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_left0 ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_3 : (tripleIndices 2 2 4).map (fun j => (left0Middle6 2 2) j ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_left0 ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_left0_data (r : LeftIndex 6 2 2) : (tripleIndices 2 2 4).map (fun j => (left0Middle6 2 2) j r) = cols_left0 r := by
  fin_cases r
  · exact cols_left0_eq_0_0_0
  · exact cols_left0_eq_0_0_1
  · exact cols_left0_eq_0_0_2
  · exact cols_left0_eq_0_0_3
  · exact cols_left0_eq_1_0_0
  · exact cols_left0_eq_1_0_1
  · exact cols_left0_eq_1_0_2
  · exact cols_left0_eq_1_0_3
  · exact cols_left0_eq_2_0_0
  · exact cols_left0_eq_2_0_1
  · exact cols_left0_eq_2_0_2
  · exact cols_left0_eq_2_0_3
  · exact cols_left0_eq_3_0_0
  · exact cols_left0_eq_3_0_1
  · exact cols_left0_eq_3_0_2
  · exact cols_left0_eq_3_0_3

private def cols_right2Data : List (List ℤ) := [decodeIntegerRow 16 5 2 78715821312,
    decodeIntegerRow 16 5 2 75903326512,
    decodeIntegerRow 16 5 2 137329914072,
    decodeIntegerRow 16 5 2 64083164064,
    decodeIntegerRow 16 5 2 64082851560,
    decodeIntegerRow 16 5 2 137329851552,
    decodeIntegerRow 16 5 2 76684576512,
    decodeIntegerRow 16 5 2 73872071312,
    decodeIntegerRow 16 5 2 75708001512,
    decodeIntegerRow 16 5 2 73833009312,
    decodeIntegerRow 16 5 2 64090664064,
    decodeIntegerRow 16 5 2 15259601552,
    decodeIntegerRow 16 5 2 15259539072,
    decodeIntegerRow 16 5 2 64090976560,
    decodeIntegerRow 16 5 2 78754884312,
    decodeIntegerRow 16 5 2 76879876512]

def cols_right2 (r : LeftIndex 6 2 2) : List ℤ := cols_right2Data.getD (leftPosition 6 2 2 r) []

private theorem cols_right2_eq_0_0_0 : (tripleIndices 4 1 4).map (fun j => (right2Middle6 2 2) j ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_right2 ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_1 : (tripleIndices 4 1 4).map (fun j => (right2Middle6 2 2) j ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_right2 ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_2 : (tripleIndices 4 1 4).map (fun j => (right2Middle6 2 2) j ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_right2 ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_3 : (tripleIndices 4 1 4).map (fun j => (right2Middle6 2 2) j ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_right2 ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_0 : (tripleIndices 4 1 4).map (fun j => (right2Middle6 2 2) j ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_right2 ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_1 : (tripleIndices 4 1 4).map (fun j => (right2Middle6 2 2) j ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_right2 ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_2 : (tripleIndices 4 1 4).map (fun j => (right2Middle6 2 2) j ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_right2 ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_3 : (tripleIndices 4 1 4).map (fun j => (right2Middle6 2 2) j ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_right2 ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_0 : (tripleIndices 4 1 4).map (fun j => (right2Middle6 2 2) j ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_right2 ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_1 : (tripleIndices 4 1 4).map (fun j => (right2Middle6 2 2) j ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_right2 ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_2 : (tripleIndices 4 1 4).map (fun j => (right2Middle6 2 2) j ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_right2 ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_3 : (tripleIndices 4 1 4).map (fun j => (right2Middle6 2 2) j ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_right2 ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_0 : (tripleIndices 4 1 4).map (fun j => (right2Middle6 2 2) j ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_right2 ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_1 : (tripleIndices 4 1 4).map (fun j => (right2Middle6 2 2) j ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_right2 ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_2 : (tripleIndices 4 1 4).map (fun j => (right2Middle6 2 2) j ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_right2 ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_3 : (tripleIndices 4 1 4).map (fun j => (right2Middle6 2 2) j ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_right2 ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right2_data (r : LeftIndex 6 2 2) : (tripleIndices 4 1 4).map (fun j => (right2Middle6 2 2) j r) = cols_right2 r := by
  fin_cases r
  · exact cols_right2_eq_0_0_0
  · exact cols_right2_eq_0_0_1
  · exact cols_right2_eq_0_0_2
  · exact cols_right2_eq_0_0_3
  · exact cols_right2_eq_1_0_0
  · exact cols_right2_eq_1_0_1
  · exact cols_right2_eq_1_0_2
  · exact cols_right2_eq_1_0_3
  · exact cols_right2_eq_2_0_0
  · exact cols_right2_eq_2_0_1
  · exact cols_right2_eq_2_0_2
  · exact cols_right2_eq_2_0_3
  · exact cols_right2_eq_3_0_0
  · exact cols_right2_eq_3_0_1
  · exact cols_right2_eq_3_0_2
  · exact cols_right2_eq_3_0_3

theorem product0_eq : HexagonAtoms622.outerABC * HexagonAtoms622.assocABC = HexagonAtoms622.assocABC :=
  Matrix.one_mul (m := Fin 2 × Fin 2 × Fin 4) (n := Fin 4 × Fin 1 × Fin 4) _

theorem product1_eq : HexagonAtoms622.assocBAC * HexagonAtoms622.innerABC = HexagonAtoms622.assocBAC :=
  Matrix.mul_one (m := Fin 4 × Fin 1 × Fin 4) (n := Fin 4 × Fin 1 × Fin 4) _

theorem product2_eq : HexagonAtoms622.innerRightABC * HexagonAtoms622.assocABC = rowColumnMul rows_innerRightABC cols_assocABC :=
  (rowColumnMul_eq _ _ _ _ rows_innerRightABC_data cols_assocABC_data).symm

theorem product3_eq : HexagonAtoms622.inverseACB * right0Middle6 2 2 = rowColumnMul rows_inverseACB cols_right0 :=
  (rowColumnMul_eq _ _ _ _ rows_inverseACB_data cols_right0_data).symm

theorem product4_eq : HexagonAtoms622.innerABC * right1Middle6 2 2 = right1Middle6 2 2 :=
  Matrix.one_mul (m := Fin 4 × Fin 1 × Fin 4) (n := Fin 4 × Fin 1 × Fin 4) _

theorem product5_eq : HexagonAtoms622.assocBCA * left0Middle6 2 2 = rowColumnMul rows_assocBCA cols_left0 :=
  (rowColumnMul_eq _ _ _ _ rows_assocBCA_data cols_left0_data).symm

theorem product6_eq : HexagonAtoms622.innerRightBAC * left1Middle6 2 2 = left1Middle6 2 2 :=
  Matrix.one_mul (m := Fin 4 × Fin 1 × Fin 4) (n := Fin 4 × Fin 1 × Fin 4) _

theorem product7_eq : HexagonAtoms622.assocBAC * right2Middle6 2 2 = rowColumnMul rows_assocBAC cols_right2 :=
  (rowColumnMul_eq _ _ _ _ rows_assocBAC_data cols_right2_data).symm

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn622
