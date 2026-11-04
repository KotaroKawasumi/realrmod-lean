import RMod.BrundanEllis.StackingReferenceHexagonAtoms667
import RMod.BrundanEllis.StackingReferenceHexagonMiddle6
import RMod.BrundanEllis.StackingReferenceRowColumnCheck

/-! Verified row and column lists. Each subsequent scalar product traverses
these lists directly, without repeated lookup into the original matrices. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn667
open Superfusion

theorem assocBAC_alias : HexagonAtoms667.assocBAC = HexagonAtoms667.assocABC :=
  HexagonAtoms667.assocBAC_eq.symm.trans HexagonAtoms667.assocABC_eq

theorem innerRightBAC_alias : HexagonAtoms667.innerRightBAC = HexagonAtoms667.innerRightABC :=
  HexagonAtoms667.innerRightBAC_eq.symm.trans HexagonAtoms667.innerRightABC_eq

private def rows_assocABCData : List (List ℤ) := [decodeIntegerRow 16 3 1 36403736,
    decodeIntegerRow 16 3 1 15146080,
    decodeIntegerRow 16 3 1 18334720,
    decodeIntegerRow 16 3 1 35340852,
    decodeIntegerRow 16 3 1 21341920,
    decodeIntegerRow 16 3 1 21603064,
    decodeIntegerRow 16 3 1 21563212,
    decodeIntegerRow 16 3 1 21354880,
    decodeIntegerRow 16 3 1 15146056,
    decodeIntegerRow 16 3 1 6643040,
    decodeIntegerRow 16 3 1 35340800,
    decodeIntegerRow 16 3 1 24712012,
    decodeIntegerRow 16 3 1 21601120,
    decodeIntegerRow 16 3 1 21709336,
    decodeIntegerRow 16 3 1 21350668,
    decodeIntegerRow 16 3 1 21484480]

def rows_assocABC (r : RightIndex 6 6 7) : List ℤ := rows_assocABCData.getD (rightPosition 6 6 7 r) []

private theorem rows_assocABC_eq_0_0_0 : (tripleIndices 2 1 8).map ((HexagonAtoms667.assocABC) ((0 : Fin 1), (0 : Fin 2), (0 : Fin 8))) = rows_assocABC ((0 : Fin 1), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_0_1 : (tripleIndices 2 1 8).map ((HexagonAtoms667.assocABC) ((0 : Fin 1), (0 : Fin 2), (1 : Fin 8))) = rows_assocABC ((0 : Fin 1), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_0_2 : (tripleIndices 2 1 8).map ((HexagonAtoms667.assocABC) ((0 : Fin 1), (0 : Fin 2), (2 : Fin 8))) = rows_assocABC ((0 : Fin 1), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_0_3 : (tripleIndices 2 1 8).map ((HexagonAtoms667.assocABC) ((0 : Fin 1), (0 : Fin 2), (3 : Fin 8))) = rows_assocABC ((0 : Fin 1), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_0_4 : (tripleIndices 2 1 8).map ((HexagonAtoms667.assocABC) ((0 : Fin 1), (0 : Fin 2), (4 : Fin 8))) = rows_assocABC ((0 : Fin 1), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_0_5 : (tripleIndices 2 1 8).map ((HexagonAtoms667.assocABC) ((0 : Fin 1), (0 : Fin 2), (5 : Fin 8))) = rows_assocABC ((0 : Fin 1), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_0_6 : (tripleIndices 2 1 8).map ((HexagonAtoms667.assocABC) ((0 : Fin 1), (0 : Fin 2), (6 : Fin 8))) = rows_assocABC ((0 : Fin 1), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_0_7 : (tripleIndices 2 1 8).map ((HexagonAtoms667.assocABC) ((0 : Fin 1), (0 : Fin 2), (7 : Fin 8))) = rows_assocABC ((0 : Fin 1), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_1_0 : (tripleIndices 2 1 8).map ((HexagonAtoms667.assocABC) ((0 : Fin 1), (1 : Fin 2), (0 : Fin 8))) = rows_assocABC ((0 : Fin 1), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_1_1 : (tripleIndices 2 1 8).map ((HexagonAtoms667.assocABC) ((0 : Fin 1), (1 : Fin 2), (1 : Fin 8))) = rows_assocABC ((0 : Fin 1), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_1_2 : (tripleIndices 2 1 8).map ((HexagonAtoms667.assocABC) ((0 : Fin 1), (1 : Fin 2), (2 : Fin 8))) = rows_assocABC ((0 : Fin 1), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_1_3 : (tripleIndices 2 1 8).map ((HexagonAtoms667.assocABC) ((0 : Fin 1), (1 : Fin 2), (3 : Fin 8))) = rows_assocABC ((0 : Fin 1), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_1_4 : (tripleIndices 2 1 8).map ((HexagonAtoms667.assocABC) ((0 : Fin 1), (1 : Fin 2), (4 : Fin 8))) = rows_assocABC ((0 : Fin 1), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_1_5 : (tripleIndices 2 1 8).map ((HexagonAtoms667.assocABC) ((0 : Fin 1), (1 : Fin 2), (5 : Fin 8))) = rows_assocABC ((0 : Fin 1), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_1_6 : (tripleIndices 2 1 8).map ((HexagonAtoms667.assocABC) ((0 : Fin 1), (1 : Fin 2), (6 : Fin 8))) = rows_assocABC ((0 : Fin 1), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_1_7 : (tripleIndices 2 1 8).map ((HexagonAtoms667.assocABC) ((0 : Fin 1), (1 : Fin 2), (7 : Fin 8))) = rows_assocABC ((0 : Fin 1), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocABC_data (r : RightIndex 6 6 7) : (tripleIndices 2 1 8).map ((HexagonAtoms667.assocABC) r) = rows_assocABC r := by
  fin_cases r
  · exact rows_assocABC_eq_0_0_0
  · exact rows_assocABC_eq_0_0_1
  · exact rows_assocABC_eq_0_0_2
  · exact rows_assocABC_eq_0_0_3
  · exact rows_assocABC_eq_0_0_4
  · exact rows_assocABC_eq_0_0_5
  · exact rows_assocABC_eq_0_0_6
  · exact rows_assocABC_eq_0_0_7
  · exact rows_assocABC_eq_0_1_0
  · exact rows_assocABC_eq_0_1_1
  · exact rows_assocABC_eq_0_1_2
  · exact rows_assocABC_eq_0_1_3
  · exact rows_assocABC_eq_0_1_4
  · exact rows_assocABC_eq_0_1_5
  · exact rows_assocABC_eq_0_1_6
  · exact rows_assocABC_eq_0_1_7

private def rows_innerRightABCData : List (List ℤ) := [decodeIntegerRow 16 3 1 21524306,
    decodeIntegerRow 16 3 1 21525622,
    decodeIntegerRow 16 3 1 21521266,
    decodeIntegerRow 16 3 1 21522902,
    decodeIntegerRow 16 3 1 21521242,
    decodeIntegerRow 16 3 1 21522846,
    decodeIntegerRow 16 3 1 21524358,
    decodeIntegerRow 16 3 1 21525634,
    decodeIntegerRow 16 3 1 18518422,
    decodeIntegerRow 16 3 1 7784626,
    decodeIntegerRow 16 3 1 6682378,
    decodeIntegerRow 16 3 1 15316654,
    decodeIntegerRow 16 3 1 36443074,
    decodeIntegerRow 16 3 1 28071238,
    decodeIntegerRow 16 3 1 24895714,
    decodeIntegerRow 16 3 1 35419558]

def rows_innerRightABC (r : RightIndex 6 7 6) : List ℤ := rows_innerRightABCData.getD (rightPosition 6 7 6 r) []

private theorem rows_innerRightABC_eq_0_0_0 : (tripleIndices 1 2 8).map ((HexagonAtoms667.innerRightABC) ((0 : Fin 1), (0 : Fin 2), (0 : Fin 8))) = rows_innerRightABC ((0 : Fin 1), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_0_1 : (tripleIndices 1 2 8).map ((HexagonAtoms667.innerRightABC) ((0 : Fin 1), (0 : Fin 2), (1 : Fin 8))) = rows_innerRightABC ((0 : Fin 1), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_0_2 : (tripleIndices 1 2 8).map ((HexagonAtoms667.innerRightABC) ((0 : Fin 1), (0 : Fin 2), (2 : Fin 8))) = rows_innerRightABC ((0 : Fin 1), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_0_3 : (tripleIndices 1 2 8).map ((HexagonAtoms667.innerRightABC) ((0 : Fin 1), (0 : Fin 2), (3 : Fin 8))) = rows_innerRightABC ((0 : Fin 1), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_0_4 : (tripleIndices 1 2 8).map ((HexagonAtoms667.innerRightABC) ((0 : Fin 1), (0 : Fin 2), (4 : Fin 8))) = rows_innerRightABC ((0 : Fin 1), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_0_5 : (tripleIndices 1 2 8).map ((HexagonAtoms667.innerRightABC) ((0 : Fin 1), (0 : Fin 2), (5 : Fin 8))) = rows_innerRightABC ((0 : Fin 1), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_0_6 : (tripleIndices 1 2 8).map ((HexagonAtoms667.innerRightABC) ((0 : Fin 1), (0 : Fin 2), (6 : Fin 8))) = rows_innerRightABC ((0 : Fin 1), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_0_7 : (tripleIndices 1 2 8).map ((HexagonAtoms667.innerRightABC) ((0 : Fin 1), (0 : Fin 2), (7 : Fin 8))) = rows_innerRightABC ((0 : Fin 1), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_1_0 : (tripleIndices 1 2 8).map ((HexagonAtoms667.innerRightABC) ((0 : Fin 1), (1 : Fin 2), (0 : Fin 8))) = rows_innerRightABC ((0 : Fin 1), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_1_1 : (tripleIndices 1 2 8).map ((HexagonAtoms667.innerRightABC) ((0 : Fin 1), (1 : Fin 2), (1 : Fin 8))) = rows_innerRightABC ((0 : Fin 1), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_1_2 : (tripleIndices 1 2 8).map ((HexagonAtoms667.innerRightABC) ((0 : Fin 1), (1 : Fin 2), (2 : Fin 8))) = rows_innerRightABC ((0 : Fin 1), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_1_3 : (tripleIndices 1 2 8).map ((HexagonAtoms667.innerRightABC) ((0 : Fin 1), (1 : Fin 2), (3 : Fin 8))) = rows_innerRightABC ((0 : Fin 1), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_1_4 : (tripleIndices 1 2 8).map ((HexagonAtoms667.innerRightABC) ((0 : Fin 1), (1 : Fin 2), (4 : Fin 8))) = rows_innerRightABC ((0 : Fin 1), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_1_5 : (tripleIndices 1 2 8).map ((HexagonAtoms667.innerRightABC) ((0 : Fin 1), (1 : Fin 2), (5 : Fin 8))) = rows_innerRightABC ((0 : Fin 1), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_1_6 : (tripleIndices 1 2 8).map ((HexagonAtoms667.innerRightABC) ((0 : Fin 1), (1 : Fin 2), (6 : Fin 8))) = rows_innerRightABC ((0 : Fin 1), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_1_7 : (tripleIndices 1 2 8).map ((HexagonAtoms667.innerRightABC) ((0 : Fin 1), (1 : Fin 2), (7 : Fin 8))) = rows_innerRightABC ((0 : Fin 1), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_innerRightABC_data (r : RightIndex 6 7 6) : (tripleIndices 1 2 8).map ((HexagonAtoms667.innerRightABC) r) = rows_innerRightABC r := by
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

private def rows_inverseACBData : List (List ℤ) := [decodeIntegerRow 16 3 1 21602066,
    decodeIntegerRow 16 3 1 21339646,
    decodeIntegerRow 16 3 1 21693958,
    decodeIntegerRow 16 3 1 21484022,
    decodeIntegerRow 16 3 1 27898546,
    decodeIntegerRow 16 3 1 6642526,
    decodeIntegerRow 16 3 1 35341798,
    decodeIntegerRow 16 3 1 18336982,
    decodeIntegerRow 16 3 1 27902758,
    decodeIntegerRow 16 3 1 36403222,
    decodeIntegerRow 16 3 1 7706866,
    decodeIntegerRow 16 3 1 18332446,
    decodeIntegerRow 16 3 1 21444602,
    decodeIntegerRow 16 3 1 21339658,
    decodeIntegerRow 16 3 1 21693934,
    decodeIntegerRow 16 3 1 21562754]

def rows_inverseACB (r : LeftIndex 6 7 6) : List ℤ := rows_inverseACBData.getD (leftPosition 6 7 6 r) []

private theorem rows_inverseACB_eq_0_0_0 : (tripleIndices 1 2 8).map ((HexagonAtoms667.inverseACB) ((0 : Fin 1), (0 : Fin 2), (0 : Fin 8))) = rows_inverseACB ((0 : Fin 1), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_1 : (tripleIndices 1 2 8).map ((HexagonAtoms667.inverseACB) ((0 : Fin 1), (0 : Fin 2), (1 : Fin 8))) = rows_inverseACB ((0 : Fin 1), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_2 : (tripleIndices 1 2 8).map ((HexagonAtoms667.inverseACB) ((0 : Fin 1), (0 : Fin 2), (2 : Fin 8))) = rows_inverseACB ((0 : Fin 1), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_3 : (tripleIndices 1 2 8).map ((HexagonAtoms667.inverseACB) ((0 : Fin 1), (0 : Fin 2), (3 : Fin 8))) = rows_inverseACB ((0 : Fin 1), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_4 : (tripleIndices 1 2 8).map ((HexagonAtoms667.inverseACB) ((0 : Fin 1), (0 : Fin 2), (4 : Fin 8))) = rows_inverseACB ((0 : Fin 1), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_5 : (tripleIndices 1 2 8).map ((HexagonAtoms667.inverseACB) ((0 : Fin 1), (0 : Fin 2), (5 : Fin 8))) = rows_inverseACB ((0 : Fin 1), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_6 : (tripleIndices 1 2 8).map ((HexagonAtoms667.inverseACB) ((0 : Fin 1), (0 : Fin 2), (6 : Fin 8))) = rows_inverseACB ((0 : Fin 1), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_7 : (tripleIndices 1 2 8).map ((HexagonAtoms667.inverseACB) ((0 : Fin 1), (0 : Fin 2), (7 : Fin 8))) = rows_inverseACB ((0 : Fin 1), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_0 : (tripleIndices 1 2 8).map ((HexagonAtoms667.inverseACB) ((0 : Fin 1), (1 : Fin 2), (0 : Fin 8))) = rows_inverseACB ((0 : Fin 1), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_1 : (tripleIndices 1 2 8).map ((HexagonAtoms667.inverseACB) ((0 : Fin 1), (1 : Fin 2), (1 : Fin 8))) = rows_inverseACB ((0 : Fin 1), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_2 : (tripleIndices 1 2 8).map ((HexagonAtoms667.inverseACB) ((0 : Fin 1), (1 : Fin 2), (2 : Fin 8))) = rows_inverseACB ((0 : Fin 1), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_3 : (tripleIndices 1 2 8).map ((HexagonAtoms667.inverseACB) ((0 : Fin 1), (1 : Fin 2), (3 : Fin 8))) = rows_inverseACB ((0 : Fin 1), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_4 : (tripleIndices 1 2 8).map ((HexagonAtoms667.inverseACB) ((0 : Fin 1), (1 : Fin 2), (4 : Fin 8))) = rows_inverseACB ((0 : Fin 1), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_5 : (tripleIndices 1 2 8).map ((HexagonAtoms667.inverseACB) ((0 : Fin 1), (1 : Fin 2), (5 : Fin 8))) = rows_inverseACB ((0 : Fin 1), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_6 : (tripleIndices 1 2 8).map ((HexagonAtoms667.inverseACB) ((0 : Fin 1), (1 : Fin 2), (6 : Fin 8))) = rows_inverseACB ((0 : Fin 1), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_7 : (tripleIndices 1 2 8).map ((HexagonAtoms667.inverseACB) ((0 : Fin 1), (1 : Fin 2), (7 : Fin 8))) = rows_inverseACB ((0 : Fin 1), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_inverseACB_data (r : LeftIndex 6 7 6) : (tripleIndices 1 2 8).map ((HexagonAtoms667.inverseACB) r) = rows_inverseACB r := by
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

private def rows_innerACBData : List (List ℤ) := [decodeIntegerRow 16 3 1 21524306,
    decodeIntegerRow 16 3 1 21525622,
    decodeIntegerRow 16 3 1 21521266,
    decodeIntegerRow 16 3 1 21522902,
    decodeIntegerRow 16 3 1 21521242,
    decodeIntegerRow 16 3 1 21522846,
    decodeIntegerRow 16 3 1 21524358,
    decodeIntegerRow 16 3 1 21525634,
    decodeIntegerRow 16 3 1 18518422,
    decodeIntegerRow 16 3 1 7784626,
    decodeIntegerRow 16 3 1 6682378,
    decodeIntegerRow 16 3 1 15316654,
    decodeIntegerRow 16 3 1 36443074,
    decodeIntegerRow 16 3 1 28071238,
    decodeIntegerRow 16 3 1 24895714,
    decodeIntegerRow 16 3 1 35419558]

def rows_innerACB (r : LeftIndex 7 6 6) : List ℤ := rows_innerACBData.getD (leftPosition 7 6 6 r) []

private theorem rows_innerACB_eq_0_0_0 : (tripleIndices 1 2 8).map ((HexagonAtoms667.innerACB) ((0 : Fin 1), (0 : Fin 2), (0 : Fin 8))) = rows_innerACB ((0 : Fin 1), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_0_1 : (tripleIndices 1 2 8).map ((HexagonAtoms667.innerACB) ((0 : Fin 1), (0 : Fin 2), (1 : Fin 8))) = rows_innerACB ((0 : Fin 1), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_0_2 : (tripleIndices 1 2 8).map ((HexagonAtoms667.innerACB) ((0 : Fin 1), (0 : Fin 2), (2 : Fin 8))) = rows_innerACB ((0 : Fin 1), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_0_3 : (tripleIndices 1 2 8).map ((HexagonAtoms667.innerACB) ((0 : Fin 1), (0 : Fin 2), (3 : Fin 8))) = rows_innerACB ((0 : Fin 1), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_0_4 : (tripleIndices 1 2 8).map ((HexagonAtoms667.innerACB) ((0 : Fin 1), (0 : Fin 2), (4 : Fin 8))) = rows_innerACB ((0 : Fin 1), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_0_5 : (tripleIndices 1 2 8).map ((HexagonAtoms667.innerACB) ((0 : Fin 1), (0 : Fin 2), (5 : Fin 8))) = rows_innerACB ((0 : Fin 1), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_0_6 : (tripleIndices 1 2 8).map ((HexagonAtoms667.innerACB) ((0 : Fin 1), (0 : Fin 2), (6 : Fin 8))) = rows_innerACB ((0 : Fin 1), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_0_7 : (tripleIndices 1 2 8).map ((HexagonAtoms667.innerACB) ((0 : Fin 1), (0 : Fin 2), (7 : Fin 8))) = rows_innerACB ((0 : Fin 1), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_1_0 : (tripleIndices 1 2 8).map ((HexagonAtoms667.innerACB) ((0 : Fin 1), (1 : Fin 2), (0 : Fin 8))) = rows_innerACB ((0 : Fin 1), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_1_1 : (tripleIndices 1 2 8).map ((HexagonAtoms667.innerACB) ((0 : Fin 1), (1 : Fin 2), (1 : Fin 8))) = rows_innerACB ((0 : Fin 1), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_1_2 : (tripleIndices 1 2 8).map ((HexagonAtoms667.innerACB) ((0 : Fin 1), (1 : Fin 2), (2 : Fin 8))) = rows_innerACB ((0 : Fin 1), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_1_3 : (tripleIndices 1 2 8).map ((HexagonAtoms667.innerACB) ((0 : Fin 1), (1 : Fin 2), (3 : Fin 8))) = rows_innerACB ((0 : Fin 1), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_1_4 : (tripleIndices 1 2 8).map ((HexagonAtoms667.innerACB) ((0 : Fin 1), (1 : Fin 2), (4 : Fin 8))) = rows_innerACB ((0 : Fin 1), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_1_5 : (tripleIndices 1 2 8).map ((HexagonAtoms667.innerACB) ((0 : Fin 1), (1 : Fin 2), (5 : Fin 8))) = rows_innerACB ((0 : Fin 1), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_1_6 : (tripleIndices 1 2 8).map ((HexagonAtoms667.innerACB) ((0 : Fin 1), (1 : Fin 2), (6 : Fin 8))) = rows_innerACB ((0 : Fin 1), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_1_7 : (tripleIndices 1 2 8).map ((HexagonAtoms667.innerACB) ((0 : Fin 1), (1 : Fin 2), (7 : Fin 8))) = rows_innerACB ((0 : Fin 1), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_innerACB_data (r : LeftIndex 7 6 6) : (tripleIndices 1 2 8).map ((HexagonAtoms667.innerACB) r) = rows_innerACB r := by
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

private def rows_assocBCAData : List (List ℤ) := [decodeIntegerRow 16 3 1 36403736,
    decodeIntegerRow 16 3 1 15146080,
    decodeIntegerRow 16 3 1 18334720,
    decodeIntegerRow 16 3 1 35340852,
    decodeIntegerRow 16 3 1 21341920,
    decodeIntegerRow 16 3 1 21603064,
    decodeIntegerRow 16 3 1 21563212,
    decodeIntegerRow 16 3 1 21354880,
    decodeIntegerRow 16 3 1 15146056,
    decodeIntegerRow 16 3 1 6643040,
    decodeIntegerRow 16 3 1 35340800,
    decodeIntegerRow 16 3 1 24712012,
    decodeIntegerRow 16 3 1 21601120,
    decodeIntegerRow 16 3 1 21709336,
    decodeIntegerRow 16 3 1 21350668,
    decodeIntegerRow 16 3 1 21484480]

def rows_assocBCA (r : RightIndex 6 7 6) : List ℤ := rows_assocBCAData.getD (rightPosition 6 7 6 r) []

private theorem rows_assocBCA_eq_0_0_0 : (tripleIndices 1 2 8).map ((HexagonAtoms667.assocBCA) ((0 : Fin 1), (0 : Fin 2), (0 : Fin 8))) = rows_assocBCA ((0 : Fin 1), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_1 : (tripleIndices 1 2 8).map ((HexagonAtoms667.assocBCA) ((0 : Fin 1), (0 : Fin 2), (1 : Fin 8))) = rows_assocBCA ((0 : Fin 1), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_2 : (tripleIndices 1 2 8).map ((HexagonAtoms667.assocBCA) ((0 : Fin 1), (0 : Fin 2), (2 : Fin 8))) = rows_assocBCA ((0 : Fin 1), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_3 : (tripleIndices 1 2 8).map ((HexagonAtoms667.assocBCA) ((0 : Fin 1), (0 : Fin 2), (3 : Fin 8))) = rows_assocBCA ((0 : Fin 1), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_4 : (tripleIndices 1 2 8).map ((HexagonAtoms667.assocBCA) ((0 : Fin 1), (0 : Fin 2), (4 : Fin 8))) = rows_assocBCA ((0 : Fin 1), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_5 : (tripleIndices 1 2 8).map ((HexagonAtoms667.assocBCA) ((0 : Fin 1), (0 : Fin 2), (5 : Fin 8))) = rows_assocBCA ((0 : Fin 1), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_6 : (tripleIndices 1 2 8).map ((HexagonAtoms667.assocBCA) ((0 : Fin 1), (0 : Fin 2), (6 : Fin 8))) = rows_assocBCA ((0 : Fin 1), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_7 : (tripleIndices 1 2 8).map ((HexagonAtoms667.assocBCA) ((0 : Fin 1), (0 : Fin 2), (7 : Fin 8))) = rows_assocBCA ((0 : Fin 1), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_0 : (tripleIndices 1 2 8).map ((HexagonAtoms667.assocBCA) ((0 : Fin 1), (1 : Fin 2), (0 : Fin 8))) = rows_assocBCA ((0 : Fin 1), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_1 : (tripleIndices 1 2 8).map ((HexagonAtoms667.assocBCA) ((0 : Fin 1), (1 : Fin 2), (1 : Fin 8))) = rows_assocBCA ((0 : Fin 1), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_2 : (tripleIndices 1 2 8).map ((HexagonAtoms667.assocBCA) ((0 : Fin 1), (1 : Fin 2), (2 : Fin 8))) = rows_assocBCA ((0 : Fin 1), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_3 : (tripleIndices 1 2 8).map ((HexagonAtoms667.assocBCA) ((0 : Fin 1), (1 : Fin 2), (3 : Fin 8))) = rows_assocBCA ((0 : Fin 1), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_4 : (tripleIndices 1 2 8).map ((HexagonAtoms667.assocBCA) ((0 : Fin 1), (1 : Fin 2), (4 : Fin 8))) = rows_assocBCA ((0 : Fin 1), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_5 : (tripleIndices 1 2 8).map ((HexagonAtoms667.assocBCA) ((0 : Fin 1), (1 : Fin 2), (5 : Fin 8))) = rows_assocBCA ((0 : Fin 1), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_6 : (tripleIndices 1 2 8).map ((HexagonAtoms667.assocBCA) ((0 : Fin 1), (1 : Fin 2), (6 : Fin 8))) = rows_assocBCA ((0 : Fin 1), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_7 : (tripleIndices 1 2 8).map ((HexagonAtoms667.assocBCA) ((0 : Fin 1), (1 : Fin 2), (7 : Fin 8))) = rows_assocBCA ((0 : Fin 1), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocBCA_data (r : RightIndex 6 7 6) : (tripleIndices 1 2 8).map ((HexagonAtoms667.assocBCA) r) = rows_assocBCA r := by
  fin_cases r
  · exact rows_assocBCA_eq_0_0_0
  · exact rows_assocBCA_eq_0_0_1
  · exact rows_assocBCA_eq_0_0_2
  · exact rows_assocBCA_eq_0_0_3
  · exact rows_assocBCA_eq_0_0_4
  · exact rows_assocBCA_eq_0_0_5
  · exact rows_assocBCA_eq_0_0_6
  · exact rows_assocBCA_eq_0_0_7
  · exact rows_assocBCA_eq_0_1_0
  · exact rows_assocBCA_eq_0_1_1
  · exact rows_assocBCA_eq_0_1_2
  · exact rows_assocBCA_eq_0_1_3
  · exact rows_assocBCA_eq_0_1_4
  · exact rows_assocBCA_eq_0_1_5
  · exact rows_assocBCA_eq_0_1_6
  · exact rows_assocBCA_eq_0_1_7

private def rows_assocCABData : List (List ℤ) := [decodeIntegerRow 16 3 1 20932654,
    decodeIntegerRow 16 3 1 23294758,
    decodeIntegerRow 16 3 1 26315074,
    decodeIntegerRow 16 3 1 7155498,
    decodeIntegerRow 16 3 1 16749142,
    decodeIntegerRow 16 3 1 35853314,
    decodeIntegerRow 16 3 1 21995482,
    decodeIntegerRow 16 3 1 20106094,
    decodeIntegerRow 16 3 1 26310706,
    decodeIntegerRow 16 3 1 35892678,
    decodeIntegerRow 16 3 1 22113634,
    decodeIntegerRow 16 3 1 23294902,
    decodeIntegerRow 16 3 1 21996022,
    decodeIntegerRow 16 3 1 22940446,
    decodeIntegerRow 16 3 1 26301958,
    decodeIntegerRow 16 3 1 35851854]

def rows_assocCAB (r : RightIndex 7 6 6) : List ℤ := rows_assocCABData.getD (rightPosition 7 6 6 r) []

private theorem rows_assocCAB_eq_0_0_0 : (tripleIndices 1 2 8).map ((HexagonAtoms667.assocCAB) ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_1 : (tripleIndices 1 2 8).map ((HexagonAtoms667.assocCAB) ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_2 : (tripleIndices 1 2 8).map ((HexagonAtoms667.assocCAB) ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_3 : (tripleIndices 1 2 8).map ((HexagonAtoms667.assocCAB) ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_4 : (tripleIndices 1 2 8).map ((HexagonAtoms667.assocCAB) ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_5 : (tripleIndices 1 2 8).map ((HexagonAtoms667.assocCAB) ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_6 : (tripleIndices 1 2 8).map ((HexagonAtoms667.assocCAB) ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_7 : (tripleIndices 1 2 8).map ((HexagonAtoms667.assocCAB) ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_0 : (tripleIndices 1 2 8).map ((HexagonAtoms667.assocCAB) ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_1 : (tripleIndices 1 2 8).map ((HexagonAtoms667.assocCAB) ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_2 : (tripleIndices 1 2 8).map ((HexagonAtoms667.assocCAB) ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_3 : (tripleIndices 1 2 8).map ((HexagonAtoms667.assocCAB) ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_4 : (tripleIndices 1 2 8).map ((HexagonAtoms667.assocCAB) ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_5 : (tripleIndices 1 2 8).map ((HexagonAtoms667.assocCAB) ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_6 : (tripleIndices 1 2 8).map ((HexagonAtoms667.assocCAB) ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_7 : (tripleIndices 1 2 8).map ((HexagonAtoms667.assocCAB) ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocCAB_data (r : RightIndex 7 6 6) : (tripleIndices 1 2 8).map ((HexagonAtoms667.assocCAB) r) = rows_assocCAB r := by
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

private def cols_innerABCData : List (List ℤ) := [decodeIntegerRow 16 3 1 21523333,
    decodeIntegerRow 16 3 1 21523351,
    decodeIntegerRow 16 3 1 21523363,
    decodeIntegerRow 16 3 1 21523361,
    decodeIntegerRow 16 3 1 21521173,
    decodeIntegerRow 16 3 1 21522631,
    decodeIntegerRow 16 3 1 21523603,
    decodeIntegerRow 16 3 1 21523441,
    decodeIntegerRow 16 3 1 23117683,
    decodeIntegerRow 16 3 1 22054801,
    decodeIntegerRow 16 3 1 7174453,
    decodeIntegerRow 16 3 1 16740391,
    decodeIntegerRow 16 3 1 21503677,
    decodeIntegerRow 16 3 1 21516799,
    decodeIntegerRow 16 3 1 21700507,
    decodeIntegerRow 16 3 1 21582409]

def cols_innerABC (r : LeftIndex 6 6 7) : List ℤ := cols_innerABCData.getD (leftPosition 6 6 7 r) []

private theorem cols_innerABC_eq_0_0_0 : (tripleIndices 2 1 8).map (fun j => (HexagonAtoms667.innerABC) j ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8))) = cols_innerABC ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_0_1 : (tripleIndices 2 1 8).map (fun j => (HexagonAtoms667.innerABC) j ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8))) = cols_innerABC ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_0_2 : (tripleIndices 2 1 8).map (fun j => (HexagonAtoms667.innerABC) j ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8))) = cols_innerABC ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_0_3 : (tripleIndices 2 1 8).map (fun j => (HexagonAtoms667.innerABC) j ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8))) = cols_innerABC ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_0_4 : (tripleIndices 2 1 8).map (fun j => (HexagonAtoms667.innerABC) j ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8))) = cols_innerABC ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_0_5 : (tripleIndices 2 1 8).map (fun j => (HexagonAtoms667.innerABC) j ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8))) = cols_innerABC ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_0_6 : (tripleIndices 2 1 8).map (fun j => (HexagonAtoms667.innerABC) j ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8))) = cols_innerABC ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_0_7 : (tripleIndices 2 1 8).map (fun j => (HexagonAtoms667.innerABC) j ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8))) = cols_innerABC ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_0_0 : (tripleIndices 2 1 8).map (fun j => (HexagonAtoms667.innerABC) j ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8))) = cols_innerABC ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_0_1 : (tripleIndices 2 1 8).map (fun j => (HexagonAtoms667.innerABC) j ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8))) = cols_innerABC ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_0_2 : (tripleIndices 2 1 8).map (fun j => (HexagonAtoms667.innerABC) j ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8))) = cols_innerABC ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_0_3 : (tripleIndices 2 1 8).map (fun j => (HexagonAtoms667.innerABC) j ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8))) = cols_innerABC ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_0_4 : (tripleIndices 2 1 8).map (fun j => (HexagonAtoms667.innerABC) j ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8))) = cols_innerABC ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_0_5 : (tripleIndices 2 1 8).map (fun j => (HexagonAtoms667.innerABC) j ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8))) = cols_innerABC ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_0_6 : (tripleIndices 2 1 8).map (fun j => (HexagonAtoms667.innerABC) j ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8))) = cols_innerABC ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_0_7 : (tripleIndices 2 1 8).map (fun j => (HexagonAtoms667.innerABC) j ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8))) = cols_innerABC ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_innerABC_data (r : LeftIndex 6 6 7) : (tripleIndices 2 1 8).map (fun j => (HexagonAtoms667.innerABC) j r) = cols_innerABC r := by
  fin_cases r
  · exact cols_innerABC_eq_0_0_0
  · exact cols_innerABC_eq_0_0_1
  · exact cols_innerABC_eq_0_0_2
  · exact cols_innerABC_eq_0_0_3
  · exact cols_innerABC_eq_0_0_4
  · exact cols_innerABC_eq_0_0_5
  · exact cols_innerABC_eq_0_0_6
  · exact cols_innerABC_eq_0_0_7
  · exact cols_innerABC_eq_1_0_0
  · exact cols_innerABC_eq_1_0_1
  · exact cols_innerABC_eq_1_0_2
  · exact cols_innerABC_eq_1_0_3
  · exact cols_innerABC_eq_1_0_4
  · exact cols_innerABC_eq_1_0_5
  · exact cols_innerABC_eq_1_0_6
  · exact cols_innerABC_eq_1_0_7

private def cols_assocABCData : List (List ℤ) := [decodeIntegerRow 16 3 1 21602066,
    decodeIntegerRow 16 3 1 21339646,
    decodeIntegerRow 16 3 1 21693958,
    decodeIntegerRow 16 3 1 21484022,
    decodeIntegerRow 16 3 1 27898546,
    decodeIntegerRow 16 3 1 6642526,
    decodeIntegerRow 16 3 1 35341798,
    decodeIntegerRow 16 3 1 18336982,
    decodeIntegerRow 16 3 1 27902758,
    decodeIntegerRow 16 3 1 36403222,
    decodeIntegerRow 16 3 1 7706866,
    decodeIntegerRow 16 3 1 18332446,
    decodeIntegerRow 16 3 1 21444602,
    decodeIntegerRow 16 3 1 21339658,
    decodeIntegerRow 16 3 1 21693934,
    decodeIntegerRow 16 3 1 21562754]

def cols_assocABC (r : LeftIndex 6 6 7) : List ℤ := cols_assocABCData.getD (leftPosition 6 6 7 r) []

private theorem cols_assocABC_eq_0_0_0 : (tripleIndices 1 2 8).map (fun j => (HexagonAtoms667.assocABC) j ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8))) = cols_assocABC ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_1 : (tripleIndices 1 2 8).map (fun j => (HexagonAtoms667.assocABC) j ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8))) = cols_assocABC ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_2 : (tripleIndices 1 2 8).map (fun j => (HexagonAtoms667.assocABC) j ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8))) = cols_assocABC ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_3 : (tripleIndices 1 2 8).map (fun j => (HexagonAtoms667.assocABC) j ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8))) = cols_assocABC ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_4 : (tripleIndices 1 2 8).map (fun j => (HexagonAtoms667.assocABC) j ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8))) = cols_assocABC ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_5 : (tripleIndices 1 2 8).map (fun j => (HexagonAtoms667.assocABC) j ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8))) = cols_assocABC ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_6 : (tripleIndices 1 2 8).map (fun j => (HexagonAtoms667.assocABC) j ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8))) = cols_assocABC ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_7 : (tripleIndices 1 2 8).map (fun j => (HexagonAtoms667.assocABC) j ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8))) = cols_assocABC ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_0 : (tripleIndices 1 2 8).map (fun j => (HexagonAtoms667.assocABC) j ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8))) = cols_assocABC ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_1 : (tripleIndices 1 2 8).map (fun j => (HexagonAtoms667.assocABC) j ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8))) = cols_assocABC ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_2 : (tripleIndices 1 2 8).map (fun j => (HexagonAtoms667.assocABC) j ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8))) = cols_assocABC ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_3 : (tripleIndices 1 2 8).map (fun j => (HexagonAtoms667.assocABC) j ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8))) = cols_assocABC ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_4 : (tripleIndices 1 2 8).map (fun j => (HexagonAtoms667.assocABC) j ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8))) = cols_assocABC ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_5 : (tripleIndices 1 2 8).map (fun j => (HexagonAtoms667.assocABC) j ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8))) = cols_assocABC ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_6 : (tripleIndices 1 2 8).map (fun j => (HexagonAtoms667.assocABC) j ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8))) = cols_assocABC ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_7 : (tripleIndices 1 2 8).map (fun j => (HexagonAtoms667.assocABC) j ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8))) = cols_assocABC ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_assocABC_data (r : LeftIndex 6 6 7) : (tripleIndices 1 2 8).map (fun j => (HexagonAtoms667.assocABC) j r) = cols_assocABC r := by
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

private def cols_right0Data : List (List ℤ) := [decodeIntegerRow 16 5 2 137332976564,
    decodeIntegerRow 16 5 2 64085976572,
    decodeIntegerRow 16 5 2 78833006612,
    decodeIntegerRow 16 5 2 75786126812,
    decodeIntegerRow 16 5 2 78637696612,
    decodeIntegerRow 16 5 2 75825201812,
    decodeIntegerRow 16 5 2 137325226564,
    decodeIntegerRow 16 5 2 64087851572,
    decodeIntegerRow 16 5 2 78637694012,
    decodeIntegerRow 16 5 2 76762701812,
    decodeIntegerRow 16 5 2 15262726564,
    decodeIntegerRow 16 5 2 64087539052,
    decodeIntegerRow 16 5 2 15254851564,
    decodeIntegerRow 16 5 2 64086289052,
    decodeIntegerRow 16 5 2 78833009012,
    decodeIntegerRow 16 5 2 76801751812]

def cols_right0 (r : LeftIndex 6 6 7) : List ℤ := cols_right0Data.getD (leftPosition 6 6 7 r) []

private theorem cols_right0_eq_0_0_0 : (tripleIndices 1 2 8).map (fun j => (right0Middle6 6 7) j ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8))) = cols_right0 ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_1 : (tripleIndices 1 2 8).map (fun j => (right0Middle6 6 7) j ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8))) = cols_right0 ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_2 : (tripleIndices 1 2 8).map (fun j => (right0Middle6 6 7) j ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8))) = cols_right0 ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_3 : (tripleIndices 1 2 8).map (fun j => (right0Middle6 6 7) j ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8))) = cols_right0 ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_4 : (tripleIndices 1 2 8).map (fun j => (right0Middle6 6 7) j ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8))) = cols_right0 ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_5 : (tripleIndices 1 2 8).map (fun j => (right0Middle6 6 7) j ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8))) = cols_right0 ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_6 : (tripleIndices 1 2 8).map (fun j => (right0Middle6 6 7) j ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8))) = cols_right0 ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_7 : (tripleIndices 1 2 8).map (fun j => (right0Middle6 6 7) j ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8))) = cols_right0 ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_0 : (tripleIndices 1 2 8).map (fun j => (right0Middle6 6 7) j ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8))) = cols_right0 ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_1 : (tripleIndices 1 2 8).map (fun j => (right0Middle6 6 7) j ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8))) = cols_right0 ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_2 : (tripleIndices 1 2 8).map (fun j => (right0Middle6 6 7) j ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8))) = cols_right0 ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_3 : (tripleIndices 1 2 8).map (fun j => (right0Middle6 6 7) j ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8))) = cols_right0 ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_4 : (tripleIndices 1 2 8).map (fun j => (right0Middle6 6 7) j ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8))) = cols_right0 ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_5 : (tripleIndices 1 2 8).map (fun j => (right0Middle6 6 7) j ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8))) = cols_right0 ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_6 : (tripleIndices 1 2 8).map (fun j => (right0Middle6 6 7) j ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8))) = cols_right0 ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_7 : (tripleIndices 1 2 8).map (fun j => (right0Middle6 6 7) j ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8))) = cols_right0 ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right0_data (r : LeftIndex 6 6 7) : (tripleIndices 1 2 8).map (fun j => (right0Middle6 6 7) j r) = cols_right0 r := by
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

private def cols_right1Data : List (List ℤ) := [decodeIntegerRow 16 9 4 926497696973192,
    decodeIntegerRow 16 9 4 926635446477832,
    decodeIntegerRow 16 9 4 926635790851528,
    decodeIntegerRow 16 9 4 926494597609272,
    decodeIntegerRow 16 9 4 845170407077512,
    decodeIntegerRow 16 9 4 1748944907020552,
    decodeIntegerRow 16 9 4 1751204342840008,
    decodeIntegerRow 16 9 4 824835480398392,
    decodeIntegerRow 16 9 4 926635790850952,
    decodeIntegerRow 16 9 4 926525591248392,
    decodeIntegerRow 16 9 4 926522491884488,
    decodeIntegerRow 16 9 4 926635446477112,
    decodeIntegerRow 16 9 4 1751204339060872,
    decodeIntegerRow 16 9 4 1028184746664712,
    decodeIntegerRow 16 9 4 1007849820090568,
    decodeIntegerRow 16 9 4 1748944902296632]

def cols_right1 (r : LeftIndex 6 6 7) : List ℤ := cols_right1Data.getD (leftPosition 6 6 7 r) []

private theorem cols_right1_eq_0_0_0 : (tripleIndices 1 2 8).map (fun j => (right1Middle6 6 7) j ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8))) = cols_right1 ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_0_1 : (tripleIndices 1 2 8).map (fun j => (right1Middle6 6 7) j ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8))) = cols_right1 ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_0_2 : (tripleIndices 1 2 8).map (fun j => (right1Middle6 6 7) j ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8))) = cols_right1 ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_0_3 : (tripleIndices 1 2 8).map (fun j => (right1Middle6 6 7) j ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8))) = cols_right1 ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_0_4 : (tripleIndices 1 2 8).map (fun j => (right1Middle6 6 7) j ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8))) = cols_right1 ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_0_5 : (tripleIndices 1 2 8).map (fun j => (right1Middle6 6 7) j ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8))) = cols_right1 ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_0_6 : (tripleIndices 1 2 8).map (fun j => (right1Middle6 6 7) j ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8))) = cols_right1 ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_0_7 : (tripleIndices 1 2 8).map (fun j => (right1Middle6 6 7) j ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8))) = cols_right1 ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_0_0 : (tripleIndices 1 2 8).map (fun j => (right1Middle6 6 7) j ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8))) = cols_right1 ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_0_1 : (tripleIndices 1 2 8).map (fun j => (right1Middle6 6 7) j ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8))) = cols_right1 ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_0_2 : (tripleIndices 1 2 8).map (fun j => (right1Middle6 6 7) j ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8))) = cols_right1 ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_0_3 : (tripleIndices 1 2 8).map (fun j => (right1Middle6 6 7) j ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8))) = cols_right1 ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_0_4 : (tripleIndices 1 2 8).map (fun j => (right1Middle6 6 7) j ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8))) = cols_right1 ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_0_5 : (tripleIndices 1 2 8).map (fun j => (right1Middle6 6 7) j ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8))) = cols_right1 ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_0_6 : (tripleIndices 1 2 8).map (fun j => (right1Middle6 6 7) j ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8))) = cols_right1 ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_0_7 : (tripleIndices 1 2 8).map (fun j => (right1Middle6 6 7) j ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8))) = cols_right1 ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right1_data (r : LeftIndex 6 6 7) : (tripleIndices 1 2 8).map (fun j => (right1Middle6 6 7) j r) = cols_right1 r := by
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

private def cols_left0Data : List (List ℤ) := [decodeIntegerRow 16 3 1 21602066,
    decodeIntegerRow 16 3 1 21339646,
    decodeIntegerRow 16 3 1 21693958,
    decodeIntegerRow 16 3 1 21484022,
    decodeIntegerRow 16 3 1 27898546,
    decodeIntegerRow 16 3 1 6642526,
    decodeIntegerRow 16 3 1 35341798,
    decodeIntegerRow 16 3 1 18336982,
    decodeIntegerRow 16 3 1 27902758,
    decodeIntegerRow 16 3 1 36403222,
    decodeIntegerRow 16 3 1 7706866,
    decodeIntegerRow 16 3 1 18332446,
    decodeIntegerRow 16 3 1 21444602,
    decodeIntegerRow 16 3 1 21339658,
    decodeIntegerRow 16 3 1 21693934,
    decodeIntegerRow 16 3 1 21562754]

def cols_left0 (r : LeftIndex 6 6 7) : List ℤ := cols_left0Data.getD (leftPosition 6 6 7 r) []

private theorem cols_left0_eq_0_0_0 : (tripleIndices 1 2 8).map (fun j => (left0Middle6 6 7) j ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8))) = cols_left0 ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_1 : (tripleIndices 1 2 8).map (fun j => (left0Middle6 6 7) j ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8))) = cols_left0 ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_2 : (tripleIndices 1 2 8).map (fun j => (left0Middle6 6 7) j ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8))) = cols_left0 ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_3 : (tripleIndices 1 2 8).map (fun j => (left0Middle6 6 7) j ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8))) = cols_left0 ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_4 : (tripleIndices 1 2 8).map (fun j => (left0Middle6 6 7) j ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8))) = cols_left0 ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_5 : (tripleIndices 1 2 8).map (fun j => (left0Middle6 6 7) j ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8))) = cols_left0 ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_6 : (tripleIndices 1 2 8).map (fun j => (left0Middle6 6 7) j ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8))) = cols_left0 ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_7 : (tripleIndices 1 2 8).map (fun j => (left0Middle6 6 7) j ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8))) = cols_left0 ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_0 : (tripleIndices 1 2 8).map (fun j => (left0Middle6 6 7) j ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8))) = cols_left0 ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_1 : (tripleIndices 1 2 8).map (fun j => (left0Middle6 6 7) j ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8))) = cols_left0 ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_2 : (tripleIndices 1 2 8).map (fun j => (left0Middle6 6 7) j ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8))) = cols_left0 ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_3 : (tripleIndices 1 2 8).map (fun j => (left0Middle6 6 7) j ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8))) = cols_left0 ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_4 : (tripleIndices 1 2 8).map (fun j => (left0Middle6 6 7) j ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8))) = cols_left0 ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_5 : (tripleIndices 1 2 8).map (fun j => (left0Middle6 6 7) j ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8))) = cols_left0 ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_6 : (tripleIndices 1 2 8).map (fun j => (left0Middle6 6 7) j ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8))) = cols_left0 ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_7 : (tripleIndices 1 2 8).map (fun j => (left0Middle6 6 7) j ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8))) = cols_left0 ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_left0_data (r : LeftIndex 6 6 7) : (tripleIndices 1 2 8).map (fun j => (left0Middle6 6 7) j r) = cols_left0 r := by
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

private def cols_left1Data : List (List ℤ) := [decodeIntegerRow 16 3 1 21562698,
    decodeIntegerRow 16 3 1 21352762,
    decodeIntegerRow 16 3 1 21339646,
    decodeIntegerRow 16 3 1 21602066,
    decodeIntegerRow 16 3 1 24709738,
    decodeIntegerRow 16 3 1 7704922,
    decodeIntegerRow 16 3 1 6642526,
    decodeIntegerRow 16 3 1 27898546,
    decodeIntegerRow 16 3 1 21339658,
    decodeIntegerRow 16 3 1 21444602,
    decodeIntegerRow 16 3 1 21483966,
    decodeIntegerRow 16 3 1 21352786,
    decodeIntegerRow 16 3 1 6643498,
    decodeIntegerRow 16 3 1 15143962,
    decodeIntegerRow 16 3 1 18332446,
    decodeIntegerRow 16 3 1 7706866]

def cols_left1 (r : LeftIndex 6 6 7) : List ℤ := cols_left1Data.getD (leftPosition 6 6 7 r) []

private theorem cols_left1_eq_0_0_0 : (tripleIndices 1 2 8).map (fun j => (left1Middle6 6 7) j ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8))) = cols_left1 ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_0_1 : (tripleIndices 1 2 8).map (fun j => (left1Middle6 6 7) j ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8))) = cols_left1 ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_0_2 : (tripleIndices 1 2 8).map (fun j => (left1Middle6 6 7) j ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8))) = cols_left1 ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_0_3 : (tripleIndices 1 2 8).map (fun j => (left1Middle6 6 7) j ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8))) = cols_left1 ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_0_4 : (tripleIndices 1 2 8).map (fun j => (left1Middle6 6 7) j ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8))) = cols_left1 ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_0_5 : (tripleIndices 1 2 8).map (fun j => (left1Middle6 6 7) j ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8))) = cols_left1 ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_0_6 : (tripleIndices 1 2 8).map (fun j => (left1Middle6 6 7) j ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8))) = cols_left1 ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_0_7 : (tripleIndices 1 2 8).map (fun j => (left1Middle6 6 7) j ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8))) = cols_left1 ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_0_0 : (tripleIndices 1 2 8).map (fun j => (left1Middle6 6 7) j ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8))) = cols_left1 ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_0_1 : (tripleIndices 1 2 8).map (fun j => (left1Middle6 6 7) j ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8))) = cols_left1 ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_0_2 : (tripleIndices 1 2 8).map (fun j => (left1Middle6 6 7) j ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8))) = cols_left1 ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_0_3 : (tripleIndices 1 2 8).map (fun j => (left1Middle6 6 7) j ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8))) = cols_left1 ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_0_4 : (tripleIndices 1 2 8).map (fun j => (left1Middle6 6 7) j ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8))) = cols_left1 ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_0_5 : (tripleIndices 1 2 8).map (fun j => (left1Middle6 6 7) j ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8))) = cols_left1 ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_0_6 : (tripleIndices 1 2 8).map (fun j => (left1Middle6 6 7) j ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8))) = cols_left1 ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_0_7 : (tripleIndices 1 2 8).map (fun j => (left1Middle6 6 7) j ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8))) = cols_left1 ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_left1_data (r : LeftIndex 6 6 7) : (tripleIndices 1 2 8).map (fun j => (left1Middle6 6 7) j r) = cols_left1 r := by
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

private def cols_right2Data : List (List ℤ) := [decodeIntegerRow 16 17 8 24325918831973073008,
    decodeIntegerRow 16 17 8 24410106737266476944,
    decodeIntegerRow 16 17 8 25677618609397410448,
    decodeIntegerRow 16 17 8 1431210577244996464,
    decodeIntegerRow 16 17 8 22983573384446995856,
    decodeIntegerRow 16 17 8 47229979401402049168,
    decodeIntegerRow 16 17 8 24335240787768670576,
    decodeIntegerRow 16 17 8 24251633488739977328,
    decodeIntegerRow 16 17 8 25677618602831991952,
    decodeIntegerRow 16 17 8 47229981298808073104,
    decodeIntegerRow 16 17 8 24335273043671156368,
    decodeIntegerRow 16 17 8 24410106737267808656,
    decodeIntegerRow 16 17 8 24335240787791466896,
    decodeIntegerRow 16 17 8 24409558386925550192,
    decodeIntegerRow 16 17 8 25677618497785291664,
    decodeIntegerRow 16 17 8 47229979401015848048]

def cols_right2 (r : LeftIndex 6 6 7) : List ℤ := cols_right2Data.getD (leftPosition 6 6 7 r) []

private theorem cols_right2_eq_0_0_0 : (tripleIndices 1 2 8).map (fun j => (right2Middle6 6 7) j ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8))) = cols_right2 ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_1 : (tripleIndices 1 2 8).map (fun j => (right2Middle6 6 7) j ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8))) = cols_right2 ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_2 : (tripleIndices 1 2 8).map (fun j => (right2Middle6 6 7) j ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8))) = cols_right2 ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_3 : (tripleIndices 1 2 8).map (fun j => (right2Middle6 6 7) j ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8))) = cols_right2 ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_4 : (tripleIndices 1 2 8).map (fun j => (right2Middle6 6 7) j ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8))) = cols_right2 ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_5 : (tripleIndices 1 2 8).map (fun j => (right2Middle6 6 7) j ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8))) = cols_right2 ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_6 : (tripleIndices 1 2 8).map (fun j => (right2Middle6 6 7) j ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8))) = cols_right2 ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_7 : (tripleIndices 1 2 8).map (fun j => (right2Middle6 6 7) j ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8))) = cols_right2 ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_0 : (tripleIndices 1 2 8).map (fun j => (right2Middle6 6 7) j ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8))) = cols_right2 ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_1 : (tripleIndices 1 2 8).map (fun j => (right2Middle6 6 7) j ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8))) = cols_right2 ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_2 : (tripleIndices 1 2 8).map (fun j => (right2Middle6 6 7) j ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8))) = cols_right2 ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_3 : (tripleIndices 1 2 8).map (fun j => (right2Middle6 6 7) j ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8))) = cols_right2 ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_4 : (tripleIndices 1 2 8).map (fun j => (right2Middle6 6 7) j ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8))) = cols_right2 ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_5 : (tripleIndices 1 2 8).map (fun j => (right2Middle6 6 7) j ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8))) = cols_right2 ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_6 : (tripleIndices 1 2 8).map (fun j => (right2Middle6 6 7) j ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8))) = cols_right2 ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_7 : (tripleIndices 1 2 8).map (fun j => (right2Middle6 6 7) j ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8))) = cols_right2 ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right2_data (r : LeftIndex 6 6 7) : (tripleIndices 1 2 8).map (fun j => (right2Middle6 6 7) j r) = cols_right2 r := by
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

theorem product0_eq : HexagonAtoms667.outerABC * HexagonAtoms667.assocABC = HexagonAtoms667.assocABC :=
  Matrix.one_mul (m := Fin 1 × Fin 2 × Fin 8) (n := Fin 2 × Fin 1 × Fin 8) _

theorem product1_eq : HexagonAtoms667.assocABC * HexagonAtoms667.innerABC = rowColumnMul rows_assocABC cols_innerABC :=
  (rowColumnMul_eq _ _ _ _ rows_assocABC_data cols_innerABC_data).symm

theorem product2_eq : HexagonAtoms667.innerRightABC * HexagonAtoms667.assocABC = rowColumnMul rows_innerRightABC cols_assocABC :=
  (rowColumnMul_eq _ _ _ _ rows_innerRightABC_data cols_assocABC_data).symm

theorem product3_eq : HexagonAtoms667.inverseACB * right0Middle6 6 7 = rowColumnMul rows_inverseACB cols_right0 :=
  (rowColumnMul_eq _ _ _ _ rows_inverseACB_data cols_right0_data).symm

theorem product4_eq : HexagonAtoms667.innerACB * right1Middle6 6 7 = rowColumnMul rows_innerACB cols_right1 :=
  (rowColumnMul_eq _ _ _ _ rows_innerACB_data cols_right1_data).symm

theorem product5_eq : HexagonAtoms667.assocBCA * left0Middle6 6 7 = rowColumnMul rows_assocBCA cols_left0 :=
  (rowColumnMul_eq _ _ _ _ rows_assocBCA_data cols_left0_data).symm

theorem product6_eq : HexagonAtoms667.innerRightABC * left1Middle6 6 7 = rowColumnMul rows_innerRightABC cols_left1 :=
  (rowColumnMul_eq _ _ _ _ rows_innerRightABC_data cols_left1_data).symm

theorem product7_eq : HexagonAtoms667.assocCAB * right2Middle6 6 7 = rowColumnMul rows_assocCAB cols_right2 :=
  (rowColumnMul_eq _ _ _ _ rows_assocCAB_data cols_right2_data).symm

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn667
