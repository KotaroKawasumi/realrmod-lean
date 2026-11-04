import RMod.BrundanEllis.StackingReferenceHexagonAtoms331
import RMod.BrundanEllis.StackingReferenceHexagonMiddle3
import RMod.BrundanEllis.StackingReferenceRowColumnCheck

/-! Verified row and column lists. Each subsequent scalar product traverses
these lists directly, without repeated lookup into the original matrices. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn331
open Superfusion

theorem assocBAC_alias : HexagonAtoms331.assocBAC = HexagonAtoms331.assocABC :=
  HexagonAtoms331.assocBAC_eq.symm.trans HexagonAtoms331.assocABC_eq

theorem innerRightBAC_alias : HexagonAtoms331.innerRightBAC = HexagonAtoms331.innerRightABC :=
  HexagonAtoms331.innerRightBAC_eq.symm.trans HexagonAtoms331.innerRightABC_eq

private def rows_assocABCData : List (List ℤ) := [decodeIntegerRow 16 3 1 7174462,
    decodeIntegerRow 16 3 1 16740418,
    decodeIntegerRow 16 3 1 21517042,
    decodeIntegerRow 16 3 1 21503758,
    decodeIntegerRow 16 3 1 19929038,
    decodeIntegerRow 16 3 1 20991922,
    decodeIntegerRow 16 3 1 21580222,
    decodeIntegerRow 16 3 1 21699778,
    decodeIntegerRow 16 3 1 21462124,
    decodeIntegerRow 16 3 1 21345484,
    decodeIntegerRow 16 3 1 19929036,
    decodeIntegerRow 16 3 1 20991916,
    decodeIntegerRow 16 3 1 21516556,
    decodeIntegerRow 16 3 1 21503596,
    decodeIntegerRow 16 3 1 35872276,
    decodeIntegerRow 16 3 1 26306356]

def rows_assocABC (r : RightIndex 3 3 1) : List ℤ := rows_assocABCData.getD (rightPosition 3 3 1 r) []

private theorem rows_assocABC_eq_0_0_0 : (tripleIndices 4 2 2).map ((HexagonAtoms331.assocABC) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = rows_assocABC ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_0_1 : (tripleIndices 4 2 2).map ((HexagonAtoms331.assocABC) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = rows_assocABC ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_1_0 : (tripleIndices 4 2 2).map ((HexagonAtoms331.assocABC) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = rows_assocABC ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_1_1 : (tripleIndices 4 2 2).map ((HexagonAtoms331.assocABC) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = rows_assocABC ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_2_0 : (tripleIndices 4 2 2).map ((HexagonAtoms331.assocABC) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = rows_assocABC ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_2_1 : (tripleIndices 4 2 2).map ((HexagonAtoms331.assocABC) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = rows_assocABC ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_3_0 : (tripleIndices 4 2 2).map ((HexagonAtoms331.assocABC) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = rows_assocABC ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_3_1 : (tripleIndices 4 2 2).map ((HexagonAtoms331.assocABC) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = rows_assocABC ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_0_0 : (tripleIndices 4 2 2).map ((HexagonAtoms331.assocABC) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = rows_assocABC ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_0_1 : (tripleIndices 4 2 2).map ((HexagonAtoms331.assocABC) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = rows_assocABC ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_1_0 : (tripleIndices 4 2 2).map ((HexagonAtoms331.assocABC) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = rows_assocABC ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_1_1 : (tripleIndices 4 2 2).map ((HexagonAtoms331.assocABC) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = rows_assocABC ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_2_0 : (tripleIndices 4 2 2).map ((HexagonAtoms331.assocABC) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = rows_assocABC ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_2_1 : (tripleIndices 4 2 2).map ((HexagonAtoms331.assocABC) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = rows_assocABC ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_3_0 : (tripleIndices 4 2 2).map ((HexagonAtoms331.assocABC) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = rows_assocABC ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_3_1 : (tripleIndices 4 2 2).map ((HexagonAtoms331.assocABC) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = rows_assocABC ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocABC_data (r : RightIndex 3 3 1) : (tripleIndices 4 2 2).map ((HexagonAtoms331.assocABC) r) = rows_assocABC r := by
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

private def rows_inverseACBData : List (List ℤ) := [decodeIntegerRow 16 3 1 21464314,
    decodeIntegerRow 16 3 1 21346214,
    decodeIntegerRow 16 3 1 35872186,
    decodeIntegerRow 16 3 1 26306086,
    decodeIntegerRow 16 3 1 21503668,
    decodeIntegerRow 16 3 1 21516772,
    decodeIntegerRow 16 3 1 22056988,
    decodeIntegerRow 16 3 1 23118412,
    decodeIntegerRow 16 3 1 16740148,
    decodeIntegerRow 16 3 1 7174372,
    decodeIntegerRow 16 3 1 21346212,
    decodeIntegerRow 16 3 1 21464308,
    decodeIntegerRow 16 3 1 19929766,
    decodeIntegerRow 16 3 1 20994106,
    decodeIntegerRow 16 3 1 21516826,
    decodeIntegerRow 16 3 1 21503686]

def rows_inverseACB (r : LeftIndex 3 1 3) : List ℤ := rows_inverseACBData.getD (leftPosition 3 1 3 r) []

private theorem rows_inverseACB_eq_0_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms331.inverseACB) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms331.inverseACB) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_0 : (tripleIndices 2 4 2).map ((HexagonAtoms331.inverseACB) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = rows_inverseACB ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_1 : (tripleIndices 2 4 2).map ((HexagonAtoms331.inverseACB) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = rows_inverseACB ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_2_0 : (tripleIndices 2 4 2).map ((HexagonAtoms331.inverseACB) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = rows_inverseACB ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_2_1 : (tripleIndices 2 4 2).map ((HexagonAtoms331.inverseACB) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = rows_inverseACB ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_3_0 : (tripleIndices 2 4 2).map ((HexagonAtoms331.inverseACB) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = rows_inverseACB ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_3_1 : (tripleIndices 2 4 2).map ((HexagonAtoms331.inverseACB) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = rows_inverseACB ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms331.inverseACB) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms331.inverseACB) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_0 : (tripleIndices 2 4 2).map ((HexagonAtoms331.inverseACB) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = rows_inverseACB ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_1 : (tripleIndices 2 4 2).map ((HexagonAtoms331.inverseACB) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = rows_inverseACB ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_2_0 : (tripleIndices 2 4 2).map ((HexagonAtoms331.inverseACB) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = rows_inverseACB ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_2_1 : (tripleIndices 2 4 2).map ((HexagonAtoms331.inverseACB) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = rows_inverseACB ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_3_0 : (tripleIndices 2 4 2).map ((HexagonAtoms331.inverseACB) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = rows_inverseACB ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_3_1 : (tripleIndices 2 4 2).map ((HexagonAtoms331.inverseACB) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = rows_inverseACB ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_inverseACB_data (r : LeftIndex 3 1 3) : (tripleIndices 2 4 2).map ((HexagonAtoms331.inverseACB) r) = rows_inverseACB r := by
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

private def rows_assocBCAData : List (List ℤ) := [decodeIntegerRow 16 3 1 21464314,
    decodeIntegerRow 16 3 1 21346214,
    decodeIntegerRow 16 3 1 35872186,
    decodeIntegerRow 16 3 1 26306086,
    decodeIntegerRow 16 3 1 21503668,
    decodeIntegerRow 16 3 1 21516772,
    decodeIntegerRow 16 3 1 22056988,
    decodeIntegerRow 16 3 1 23118412,
    decodeIntegerRow 16 3 1 16740148,
    decodeIntegerRow 16 3 1 7174372,
    decodeIntegerRow 16 3 1 21346212,
    decodeIntegerRow 16 3 1 21464308,
    decodeIntegerRow 16 3 1 19929766,
    decodeIntegerRow 16 3 1 20994106,
    decodeIntegerRow 16 3 1 21516826,
    decodeIntegerRow 16 3 1 21503686]

def rows_assocBCA (r : RightIndex 3 1 3) : List ℤ := rows_assocBCAData.getD (rightPosition 3 1 3 r) []

private theorem rows_assocBCA_eq_0_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms331.assocBCA) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = rows_assocBCA ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms331.assocBCA) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = rows_assocBCA ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_0 : (tripleIndices 2 4 2).map ((HexagonAtoms331.assocBCA) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = rows_assocBCA ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_1 : (tripleIndices 2 4 2).map ((HexagonAtoms331.assocBCA) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = rows_assocBCA ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_2_0 : (tripleIndices 2 4 2).map ((HexagonAtoms331.assocBCA) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = rows_assocBCA ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_2_1 : (tripleIndices 2 4 2).map ((HexagonAtoms331.assocBCA) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = rows_assocBCA ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_3_0 : (tripleIndices 2 4 2).map ((HexagonAtoms331.assocBCA) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = rows_assocBCA ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_3_1 : (tripleIndices 2 4 2).map ((HexagonAtoms331.assocBCA) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = rows_assocBCA ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms331.assocBCA) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = rows_assocBCA ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms331.assocBCA) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = rows_assocBCA ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_0 : (tripleIndices 2 4 2).map ((HexagonAtoms331.assocBCA) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = rows_assocBCA ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_1 : (tripleIndices 2 4 2).map ((HexagonAtoms331.assocBCA) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = rows_assocBCA ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_2_0 : (tripleIndices 2 4 2).map ((HexagonAtoms331.assocBCA) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = rows_assocBCA ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_2_1 : (tripleIndices 2 4 2).map ((HexagonAtoms331.assocBCA) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = rows_assocBCA ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_3_0 : (tripleIndices 2 4 2).map ((HexagonAtoms331.assocBCA) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = rows_assocBCA ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_3_1 : (tripleIndices 2 4 2).map ((HexagonAtoms331.assocBCA) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = rows_assocBCA ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocBCA_data (r : RightIndex 3 1 3) : (tripleIndices 2 4 2).map ((HexagonAtoms331.assocBCA) r) = rows_assocBCA r := by
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

private def rows_assocCABData : List (List ℤ) := [decodeIntegerRow 16 3 1 21680816,
    decodeIntegerRow 16 3 1 21575824,
    decodeIntegerRow 16 3 1 21457780,
    decodeIntegerRow 16 3 1 21326540,
    decodeIntegerRow 16 3 1 26835340,
    decodeIntegerRow 16 3 1 37465780,
    decodeIntegerRow 16 3 1 34277296,
    decodeIntegerRow 16 3 1 25772944,
    decodeIntegerRow 16 3 1 8768128,
    decodeIntegerRow 16 3 1 17269888,
    decodeIntegerRow 16 3 1 26840200,
    decodeIntegerRow 16 3 1 37467400,
    decodeIntegerRow 16 3 1 21589000,
    decodeIntegerRow 16 3 1 21720200,
    decodeIntegerRow 16 3 1 21680832,
    decodeIntegerRow 16 3 1 21575872]

def rows_assocCAB (r : RightIndex 1 3 3) : List ℤ := rows_assocCABData.getD (rightPosition 1 3 3 r) []

private theorem rows_assocCAB_eq_0_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms331.assocCAB) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = rows_assocCAB ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms331.assocCAB) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = rows_assocCAB ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_0 : (tripleIndices 2 4 2).map ((HexagonAtoms331.assocCAB) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = rows_assocCAB ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_1 : (tripleIndices 2 4 2).map ((HexagonAtoms331.assocCAB) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = rows_assocCAB ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms331.assocCAB) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = rows_assocCAB ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms331.assocCAB) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = rows_assocCAB ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_0 : (tripleIndices 2 4 2).map ((HexagonAtoms331.assocCAB) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = rows_assocCAB ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_1 : (tripleIndices 2 4 2).map ((HexagonAtoms331.assocCAB) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = rows_assocCAB ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms331.assocCAB) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = rows_assocCAB ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms331.assocCAB) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = rows_assocCAB ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_1_0 : (tripleIndices 2 4 2).map ((HexagonAtoms331.assocCAB) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = rows_assocCAB ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_1_1 : (tripleIndices 2 4 2).map ((HexagonAtoms331.assocCAB) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = rows_assocCAB ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms331.assocCAB) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = rows_assocCAB ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms331.assocCAB) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = rows_assocCAB ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_1_0 : (tripleIndices 2 4 2).map ((HexagonAtoms331.assocCAB) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = rows_assocCAB ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_1_1 : (tripleIndices 2 4 2).map ((HexagonAtoms331.assocCAB) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = rows_assocCAB ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocCAB_data (r : RightIndex 1 3 3) : (tripleIndices 2 4 2).map ((HexagonAtoms331.assocCAB) r) = rows_assocCAB r := by
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

private def cols_innerABCData : List (List ℤ) := [decodeIntegerRow 16 3 1 36219508,
    decodeIntegerRow 16 3 1 27819788,
    decodeIntegerRow 16 3 1 24670344,
    decodeIntegerRow 16 3 1 35169256,
    decodeIntegerRow 16 3 1 6826228,
    decodeIntegerRow 16 3 1 15222668,
    decodeIntegerRow 16 3 1 18371784,
    decodeIntegerRow 16 3 1 7875496,
    decodeIntegerRow 16 3 1 27977304,
    decodeIntegerRow 16 3 1 36586936,
    decodeIntegerRow 16 3 1 7536268,
    decodeIntegerRow 16 3 1 18297588,
    decodeIntegerRow 16 3 1 27981464,
    decodeIntegerRow 16 3 1 36587896,
    decodeIntegerRow 16 3 1 7534348,
    decodeIntegerRow 16 3 1 18293108]

def cols_innerABC (r : LeftIndex 3 3 1) : List ℤ := cols_innerABCData.getD (leftPosition 3 3 1 r) []

private theorem cols_innerABC_eq_0_0_0 : (tripleIndices 4 2 2).map (fun j => (HexagonAtoms331.innerABC) j ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = cols_innerABC ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_0_1 : (tripleIndices 4 2 2).map (fun j => (HexagonAtoms331.innerABC) j ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = cols_innerABC ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_1_0 : (tripleIndices 4 2 2).map (fun j => (HexagonAtoms331.innerABC) j ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = cols_innerABC ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_1_1 : (tripleIndices 4 2 2).map (fun j => (HexagonAtoms331.innerABC) j ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = cols_innerABC ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_0_0 : (tripleIndices 4 2 2).map (fun j => (HexagonAtoms331.innerABC) j ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = cols_innerABC ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_0_1 : (tripleIndices 4 2 2).map (fun j => (HexagonAtoms331.innerABC) j ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = cols_innerABC ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_1_0 : (tripleIndices 4 2 2).map (fun j => (HexagonAtoms331.innerABC) j ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = cols_innerABC ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_1_1 : (tripleIndices 4 2 2).map (fun j => (HexagonAtoms331.innerABC) j ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = cols_innerABC ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_2_0_0 : (tripleIndices 4 2 2).map (fun j => (HexagonAtoms331.innerABC) j ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = cols_innerABC ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_2_0_1 : (tripleIndices 4 2 2).map (fun j => (HexagonAtoms331.innerABC) j ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = cols_innerABC ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_2_1_0 : (tripleIndices 4 2 2).map (fun j => (HexagonAtoms331.innerABC) j ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = cols_innerABC ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_2_1_1 : (tripleIndices 4 2 2).map (fun j => (HexagonAtoms331.innerABC) j ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = cols_innerABC ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_3_0_0 : (tripleIndices 4 2 2).map (fun j => (HexagonAtoms331.innerABC) j ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = cols_innerABC ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_3_0_1 : (tripleIndices 4 2 2).map (fun j => (HexagonAtoms331.innerABC) j ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = cols_innerABC ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_3_1_0 : (tripleIndices 4 2 2).map (fun j => (HexagonAtoms331.innerABC) j ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = cols_innerABC ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_3_1_1 : (tripleIndices 4 2 2).map (fun j => (HexagonAtoms331.innerABC) j ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = cols_innerABC ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_innerABC_data (r : LeftIndex 3 3 1) : (tripleIndices 4 2 2).map (fun j => (HexagonAtoms331.innerABC) j r) = cols_innerABC r := by
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

private def cols_right0Data : List (List ℤ) := [decodeIntegerRow 16 3 1 21464392,
    decodeIntegerRow 16 3 1 21346456,
    decodeIntegerRow 16 3 1 26306330,
    decodeIntegerRow 16 3 1 35872270,
    decodeIntegerRow 16 3 1 19929064,
    decodeIntegerRow 16 3 1 20991928,
    decodeIntegerRow 16 3 1 21501490,
    decodeIntegerRow 16 3 1 21516070,
    decodeIntegerRow 16 3 1 20991910,
    decodeIntegerRow 16 3 1 19929010,
    decodeIntegerRow 16 3 1 21517528,
    decodeIntegerRow 16 3 1 21505864,
    decodeIntegerRow 16 3 1 21345970,
    decodeIntegerRow 16 3 1 21464230,
    decodeIntegerRow 16 3 1 35872264,
    decodeIntegerRow 16 3 1 26306328]

def cols_right0 (r : LeftIndex 3 3 1) : List ℤ := cols_right0Data.getD (leftPosition 3 3 1 r) []

private theorem cols_right0_eq_0_0_0 : (tripleIndices 2 4 2).map (fun j => (right0Middle3 3 1) j ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = cols_right0 ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_1 : (tripleIndices 2 4 2).map (fun j => (right0Middle3 3 1) j ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = cols_right0 ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_0 : (tripleIndices 2 4 2).map (fun j => (right0Middle3 3 1) j ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = cols_right0 ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_1 : (tripleIndices 2 4 2).map (fun j => (right0Middle3 3 1) j ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = cols_right0 ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_0 : (tripleIndices 2 4 2).map (fun j => (right0Middle3 3 1) j ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = cols_right0 ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_1 : (tripleIndices 2 4 2).map (fun j => (right0Middle3 3 1) j ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = cols_right0 ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_0 : (tripleIndices 2 4 2).map (fun j => (right0Middle3 3 1) j ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = cols_right0 ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_1 : (tripleIndices 2 4 2).map (fun j => (right0Middle3 3 1) j ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = cols_right0 ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_0 : (tripleIndices 2 4 2).map (fun j => (right0Middle3 3 1) j ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = cols_right0 ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_1 : (tripleIndices 2 4 2).map (fun j => (right0Middle3 3 1) j ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = cols_right0 ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_1_0 : (tripleIndices 2 4 2).map (fun j => (right0Middle3 3 1) j ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = cols_right0 ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_1_1 : (tripleIndices 2 4 2).map (fun j => (right0Middle3 3 1) j ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = cols_right0 ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_0 : (tripleIndices 2 4 2).map (fun j => (right0Middle3 3 1) j ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = cols_right0 ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_1 : (tripleIndices 2 4 2).map (fun j => (right0Middle3 3 1) j ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = cols_right0 ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_1_0 : (tripleIndices 2 4 2).map (fun j => (right0Middle3 3 1) j ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = cols_right0 ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_1_1 : (tripleIndices 2 4 2).map (fun j => (right0Middle3 3 1) j ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = cols_right0 ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right0_data (r : LeftIndex 3 3 1) : (tripleIndices 2 4 2).map (fun j => (right0Middle3 3 1) j r) = cols_right0 r := by
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

private def cols_left0Data : List (List ℤ) := [decodeIntegerRow 16 3 1 21464392,
    decodeIntegerRow 16 3 1 21346456,
    decodeIntegerRow 16 3 1 26306330,
    decodeIntegerRow 16 3 1 35872270,
    decodeIntegerRow 16 3 1 19929064,
    decodeIntegerRow 16 3 1 20991928,
    decodeIntegerRow 16 3 1 21501490,
    decodeIntegerRow 16 3 1 21516070,
    decodeIntegerRow 16 3 1 20991910,
    decodeIntegerRow 16 3 1 19929010,
    decodeIntegerRow 16 3 1 21517528,
    decodeIntegerRow 16 3 1 21505864,
    decodeIntegerRow 16 3 1 21345970,
    decodeIntegerRow 16 3 1 21464230,
    decodeIntegerRow 16 3 1 35872264,
    decodeIntegerRow 16 3 1 26306328]

def cols_left0 (r : LeftIndex 3 3 1) : List ℤ := cols_left0Data.getD (leftPosition 3 3 1 r) []

private theorem cols_left0_eq_0_0_0 : (tripleIndices 2 4 2).map (fun j => (left0Middle3 3 1) j ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = cols_left0 ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_1 : (tripleIndices 2 4 2).map (fun j => (left0Middle3 3 1) j ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = cols_left0 ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_0 : (tripleIndices 2 4 2).map (fun j => (left0Middle3 3 1) j ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = cols_left0 ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_1 : (tripleIndices 2 4 2).map (fun j => (left0Middle3 3 1) j ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = cols_left0 ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_0 : (tripleIndices 2 4 2).map (fun j => (left0Middle3 3 1) j ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = cols_left0 ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_1 : (tripleIndices 2 4 2).map (fun j => (left0Middle3 3 1) j ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = cols_left0 ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_0 : (tripleIndices 2 4 2).map (fun j => (left0Middle3 3 1) j ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = cols_left0 ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_1 : (tripleIndices 2 4 2).map (fun j => (left0Middle3 3 1) j ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = cols_left0 ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_0 : (tripleIndices 2 4 2).map (fun j => (left0Middle3 3 1) j ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = cols_left0 ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_1 : (tripleIndices 2 4 2).map (fun j => (left0Middle3 3 1) j ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = cols_left0 ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_1_0 : (tripleIndices 2 4 2).map (fun j => (left0Middle3 3 1) j ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = cols_left0 ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_1_1 : (tripleIndices 2 4 2).map (fun j => (left0Middle3 3 1) j ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = cols_left0 ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_0 : (tripleIndices 2 4 2).map (fun j => (left0Middle3 3 1) j ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = cols_left0 ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_1 : (tripleIndices 2 4 2).map (fun j => (left0Middle3 3 1) j ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = cols_left0 ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_1_0 : (tripleIndices 2 4 2).map (fun j => (left0Middle3 3 1) j ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = cols_left0 ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_1_1 : (tripleIndices 2 4 2).map (fun j => (left0Middle3 3 1) j ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = cols_left0 ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_left0_data (r : LeftIndex 3 3 1) : (tripleIndices 2 4 2).map (fun j => (left0Middle3 3 1) j r) = cols_left0 r := by
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

private def cols_right2Data : List (List ℤ) := [decodeIntegerRow 16 3 1 21680816,
    decodeIntegerRow 16 3 1 21575824,
    decodeIntegerRow 16 3 1 21457780,
    decodeIntegerRow 16 3 1 21326540,
    decodeIntegerRow 16 3 1 26835340,
    decodeIntegerRow 16 3 1 37465780,
    decodeIntegerRow 16 3 1 34277296,
    decodeIntegerRow 16 3 1 25772944,
    decodeIntegerRow 16 3 1 8768128,
    decodeIntegerRow 16 3 1 17269888,
    decodeIntegerRow 16 3 1 26840200,
    decodeIntegerRow 16 3 1 37467400,
    decodeIntegerRow 16 3 1 21589000,
    decodeIntegerRow 16 3 1 21720200,
    decodeIntegerRow 16 3 1 21680832,
    decodeIntegerRow 16 3 1 21575872]

def cols_right2 (r : LeftIndex 3 3 1) : List ℤ := cols_right2Data.getD (leftPosition 3 3 1 r) []

private theorem cols_right2_eq_0_0_0 : (tripleIndices 2 4 2).map (fun j => (right2Middle3 3 1) j ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = cols_right2 ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_1 : (tripleIndices 2 4 2).map (fun j => (right2Middle3 3 1) j ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = cols_right2 ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_0 : (tripleIndices 2 4 2).map (fun j => (right2Middle3 3 1) j ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = cols_right2 ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_1 : (tripleIndices 2 4 2).map (fun j => (right2Middle3 3 1) j ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = cols_right2 ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_0 : (tripleIndices 2 4 2).map (fun j => (right2Middle3 3 1) j ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = cols_right2 ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_1 : (tripleIndices 2 4 2).map (fun j => (right2Middle3 3 1) j ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = cols_right2 ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_0 : (tripleIndices 2 4 2).map (fun j => (right2Middle3 3 1) j ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = cols_right2 ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_1 : (tripleIndices 2 4 2).map (fun j => (right2Middle3 3 1) j ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = cols_right2 ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_0 : (tripleIndices 2 4 2).map (fun j => (right2Middle3 3 1) j ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = cols_right2 ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_1 : (tripleIndices 2 4 2).map (fun j => (right2Middle3 3 1) j ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = cols_right2 ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_1_0 : (tripleIndices 2 4 2).map (fun j => (right2Middle3 3 1) j ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = cols_right2 ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_1_1 : (tripleIndices 2 4 2).map (fun j => (right2Middle3 3 1) j ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = cols_right2 ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_0 : (tripleIndices 2 4 2).map (fun j => (right2Middle3 3 1) j ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = cols_right2 ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_1 : (tripleIndices 2 4 2).map (fun j => (right2Middle3 3 1) j ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = cols_right2 ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_1_0 : (tripleIndices 2 4 2).map (fun j => (right2Middle3 3 1) j ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = cols_right2 ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_1_1 : (tripleIndices 2 4 2).map (fun j => (right2Middle3 3 1) j ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = cols_right2 ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right2_data (r : LeftIndex 3 3 1) : (tripleIndices 2 4 2).map (fun j => (right2Middle3 3 1) j r) = cols_right2 r := by
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

theorem product0_eq : HexagonAtoms331.outerABC * HexagonAtoms331.assocABC = HexagonAtoms331.assocABC :=
  Matrix.one_mul (m := Fin 2 × Fin 4 × Fin 2) (n := Fin 4 × Fin 2 × Fin 2) _

theorem product1_eq : HexagonAtoms331.assocABC * HexagonAtoms331.innerABC = rowColumnMul rows_assocABC cols_innerABC :=
  (rowColumnMul_eq _ _ _ _ rows_assocABC_data cols_innerABC_data).symm

theorem product2_eq : HexagonAtoms331.innerRightABC * HexagonAtoms331.assocABC = HexagonAtoms331.assocABC :=
  Matrix.one_mul (m := Fin 2 × Fin 4 × Fin 2) (n := Fin 4 × Fin 2 × Fin 2) _

theorem product3_eq : HexagonAtoms331.inverseACB * right0Middle3 3 1 = rowColumnMul rows_inverseACB cols_right0 :=
  (rowColumnMul_eq _ _ _ _ rows_inverseACB_data cols_right0_data).symm

theorem product4_eq : HexagonAtoms331.innerACB * right1Middle3 3 1 = right1Middle3 3 1 :=
  Matrix.one_mul (m := Fin 2 × Fin 4 × Fin 2) (n := Fin 4 × Fin 2 × Fin 2) _

theorem product5_eq : HexagonAtoms331.assocBCA * left0Middle3 3 1 = rowColumnMul rows_assocBCA cols_left0 :=
  (rowColumnMul_eq _ _ _ _ rows_assocBCA_data cols_left0_data).symm

theorem product6_eq : HexagonAtoms331.innerRightABC * left1Middle3 3 1 = left1Middle3 3 1 :=
  Matrix.one_mul (m := Fin 2 × Fin 4 × Fin 2) (n := Fin 4 × Fin 2 × Fin 2) _

theorem product7_eq : HexagonAtoms331.assocCAB * right2Middle3 3 1 = rowColumnMul rows_assocCAB cols_right2 :=
  (rowColumnMul_eq _ _ _ _ rows_assocCAB_data cols_right2_data).symm

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn331
