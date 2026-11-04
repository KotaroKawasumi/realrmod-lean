import RMod.BrundanEllis.StackingReferenceHexagonAtoms616
import RMod.BrundanEllis.StackingReferenceHexagonMiddle6
import RMod.BrundanEllis.StackingReferenceRowColumnCheck

/-! Verified row and column lists. Each subsequent scalar product traverses
these lists directly, without repeated lookup into the original matrices. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn616
open Superfusion

theorem assocBCA_alias : HexagonAtoms616.assocBCA = HexagonAtoms616.assocBAC :=
  HexagonAtoms616.assocBCA_eq.symm.trans HexagonAtoms616.assocBAC_eq

private def rows_outerABCData : List (List ℤ) := [decodeIntegerRow 16 3 1 21523874,
    decodeIntegerRow 16 3 1 21525622,
    decodeIntegerRow 16 3 1 21525478,
    decodeIntegerRow 16 3 1 21522414,
    decodeIntegerRow 16 3 1 21525634,
    decodeIntegerRow 16 3 1 21522902,
    decodeIntegerRow 16 3 1 21524358,
    decodeIntegerRow 16 3 1 21525454,
    decodeIntegerRow 16 3 1 24895714,
    decodeIntegerRow 16 3 1 36364342,
    decodeIntegerRow 16 3 1 35419558,
    decodeIntegerRow 16 3 1 15316654,
    decodeIntegerRow 16 3 1 36443074,
    decodeIntegerRow 16 3 1 18518422,
    decodeIntegerRow 16 3 1 28071238,
    decodeIntegerRow 16 3 1 35262094]

def rows_outerABC (r : LeftIndex 1 6 6) : List ℤ := rows_outerABCData.getD (leftPosition 1 6 6 r) []

private theorem rows_outerABC_eq_0_0_0 : (tripleIndices 2 1 8).map ((HexagonAtoms616.outerABC) ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8))) = rows_outerABC ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_0_1 : (tripleIndices 2 1 8).map ((HexagonAtoms616.outerABC) ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8))) = rows_outerABC ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_0_2 : (tripleIndices 2 1 8).map ((HexagonAtoms616.outerABC) ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8))) = rows_outerABC ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_0_3 : (tripleIndices 2 1 8).map ((HexagonAtoms616.outerABC) ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8))) = rows_outerABC ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_0_4 : (tripleIndices 2 1 8).map ((HexagonAtoms616.outerABC) ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8))) = rows_outerABC ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_0_5 : (tripleIndices 2 1 8).map ((HexagonAtoms616.outerABC) ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8))) = rows_outerABC ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_0_6 : (tripleIndices 2 1 8).map ((HexagonAtoms616.outerABC) ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8))) = rows_outerABC ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_0_7 : (tripleIndices 2 1 8).map ((HexagonAtoms616.outerABC) ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8))) = rows_outerABC ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_0 : (tripleIndices 2 1 8).map ((HexagonAtoms616.outerABC) ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8))) = rows_outerABC ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_1 : (tripleIndices 2 1 8).map ((HexagonAtoms616.outerABC) ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8))) = rows_outerABC ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_2 : (tripleIndices 2 1 8).map ((HexagonAtoms616.outerABC) ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8))) = rows_outerABC ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_3 : (tripleIndices 2 1 8).map ((HexagonAtoms616.outerABC) ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8))) = rows_outerABC ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_4 : (tripleIndices 2 1 8).map ((HexagonAtoms616.outerABC) ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8))) = rows_outerABC ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_5 : (tripleIndices 2 1 8).map ((HexagonAtoms616.outerABC) ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8))) = rows_outerABC ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_6 : (tripleIndices 2 1 8).map ((HexagonAtoms616.outerABC) ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8))) = rows_outerABC ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_7 : (tripleIndices 2 1 8).map ((HexagonAtoms616.outerABC) ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8))) = rows_outerABC ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_outerABC_data (r : LeftIndex 1 6 6) : (tripleIndices 2 1 8).map ((HexagonAtoms616.outerABC) r) = rows_outerABC r := by
  fin_cases r
  · exact rows_outerABC_eq_0_0_0
  · exact rows_outerABC_eq_0_0_1
  · exact rows_outerABC_eq_0_0_2
  · exact rows_outerABC_eq_0_0_3
  · exact rows_outerABC_eq_0_0_4
  · exact rows_outerABC_eq_0_0_5
  · exact rows_outerABC_eq_0_0_6
  · exact rows_outerABC_eq_0_0_7
  · exact rows_outerABC_eq_1_0_0
  · exact rows_outerABC_eq_1_0_1
  · exact rows_outerABC_eq_1_0_2
  · exact rows_outerABC_eq_1_0_3
  · exact rows_outerABC_eq_1_0_4
  · exact rows_outerABC_eq_1_0_5
  · exact rows_outerABC_eq_1_0_6
  · exact rows_outerABC_eq_1_0_7

private def rows_inverseACBData : List (List ℤ) := [decodeIntegerRow 16 3 1 21445114,
    decodeIntegerRow 16 3 1 21696214,
    decodeIntegerRow 16 3 1 21341758,
    decodeIntegerRow 16 3 1 21483022,
    decodeIntegerRow 16 3 1 15146074,
    decodeIntegerRow 16 3 1 35340854,
    decodeIntegerRow 16 3 1 6643038,
    decodeIntegerRow 16 3 1 18334702,
    decodeIntegerRow 16 3 1 21709174,
    decodeIntegerRow 16 3 1 21484966,
    decodeIntegerRow 16 3 1 21602578,
    decodeIntegerRow 16 3 1 21691678,
    decodeIntegerRow 16 3 1 36403734,
    decodeIntegerRow 16 3 1 18334726,
    decodeIntegerRow 16 3 1 27900658,
    decodeIntegerRow 16 3 1 35340798]

def rows_inverseACB (r : LeftIndex 6 6 1) : List ℤ := rows_inverseACBData.getD (leftPosition 6 6 1 r) []

private theorem rows_inverseACB_eq_0_0_0 : (tripleIndices 2 1 8).map ((HexagonAtoms616.inverseACB) ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_1 : (tripleIndices 2 1 8).map ((HexagonAtoms616.inverseACB) ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_2 : (tripleIndices 2 1 8).map ((HexagonAtoms616.inverseACB) ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_3 : (tripleIndices 2 1 8).map ((HexagonAtoms616.inverseACB) ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_4 : (tripleIndices 2 1 8).map ((HexagonAtoms616.inverseACB) ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_5 : (tripleIndices 2 1 8).map ((HexagonAtoms616.inverseACB) ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_6 : (tripleIndices 2 1 8).map ((HexagonAtoms616.inverseACB) ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_7 : (tripleIndices 2 1 8).map ((HexagonAtoms616.inverseACB) ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_0 : (tripleIndices 2 1 8).map ((HexagonAtoms616.inverseACB) ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_1 : (tripleIndices 2 1 8).map ((HexagonAtoms616.inverseACB) ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_2 : (tripleIndices 2 1 8).map ((HexagonAtoms616.inverseACB) ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_3 : (tripleIndices 2 1 8).map ((HexagonAtoms616.inverseACB) ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_4 : (tripleIndices 2 1 8).map ((HexagonAtoms616.inverseACB) ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_5 : (tripleIndices 2 1 8).map ((HexagonAtoms616.inverseACB) ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_6 : (tripleIndices 2 1 8).map ((HexagonAtoms616.inverseACB) ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_7 : (tripleIndices 2 1 8).map ((HexagonAtoms616.inverseACB) ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_inverseACB_data (r : LeftIndex 6 6 1) : (tripleIndices 2 1 8).map ((HexagonAtoms616.inverseACB) r) = rows_inverseACB r := by
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

private def rows_innerACBData : List (List ℤ) := [decodeIntegerRow 16 3 1 21523387,
    decodeIntegerRow 16 3 1 21523351,
    decodeIntegerRow 16 3 1 21523363,
    decodeIntegerRow 16 3 1 21523359,
    decodeIntegerRow 16 3 1 21525547,
    decodeIntegerRow 16 3 1 21522631,
    decodeIntegerRow 16 3 1 21523603,
    decodeIntegerRow 16 3 1 21523279,
    decodeIntegerRow 16 3 1 23117683,
    decodeIntegerRow 16 3 1 20991919,
    decodeIntegerRow 16 3 1 7174453,
    decodeIntegerRow 16 3 1 26306329,
    decodeIntegerRow 16 3 1 21543043,
    decodeIntegerRow 16 3 1 21516799,
    decodeIntegerRow 16 3 1 21346213,
    decodeIntegerRow 16 3 1 21582409]

def rows_innerACB (r : LeftIndex 6 6 1) : List ℤ := rows_innerACBData.getD (leftPosition 6 6 1 r) []

private theorem rows_innerACB_eq_0_0_0 : (tripleIndices 2 1 8).map ((HexagonAtoms616.innerACB) ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8))) = rows_innerACB ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_0_1 : (tripleIndices 2 1 8).map ((HexagonAtoms616.innerACB) ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8))) = rows_innerACB ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_0_2 : (tripleIndices 2 1 8).map ((HexagonAtoms616.innerACB) ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8))) = rows_innerACB ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_0_3 : (tripleIndices 2 1 8).map ((HexagonAtoms616.innerACB) ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8))) = rows_innerACB ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_0_4 : (tripleIndices 2 1 8).map ((HexagonAtoms616.innerACB) ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8))) = rows_innerACB ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_0_5 : (tripleIndices 2 1 8).map ((HexagonAtoms616.innerACB) ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8))) = rows_innerACB ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_0_6 : (tripleIndices 2 1 8).map ((HexagonAtoms616.innerACB) ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8))) = rows_innerACB ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_0_7 : (tripleIndices 2 1 8).map ((HexagonAtoms616.innerACB) ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8))) = rows_innerACB ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_0_0 : (tripleIndices 2 1 8).map ((HexagonAtoms616.innerACB) ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8))) = rows_innerACB ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_0_1 : (tripleIndices 2 1 8).map ((HexagonAtoms616.innerACB) ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8))) = rows_innerACB ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_0_2 : (tripleIndices 2 1 8).map ((HexagonAtoms616.innerACB) ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8))) = rows_innerACB ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_0_3 : (tripleIndices 2 1 8).map ((HexagonAtoms616.innerACB) ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8))) = rows_innerACB ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_0_4 : (tripleIndices 2 1 8).map ((HexagonAtoms616.innerACB) ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8))) = rows_innerACB ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_0_5 : (tripleIndices 2 1 8).map ((HexagonAtoms616.innerACB) ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8))) = rows_innerACB ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_0_6 : (tripleIndices 2 1 8).map ((HexagonAtoms616.innerACB) ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8))) = rows_innerACB ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_0_7 : (tripleIndices 2 1 8).map ((HexagonAtoms616.innerACB) ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8))) = rows_innerACB ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_innerACB_data (r : LeftIndex 6 6 1) : (tripleIndices 2 1 8).map ((HexagonAtoms616.innerACB) r) = rows_innerACB r := by
  fin_cases r
  · exact rows_innerACB_eq_0_0_0
  · exact rows_innerACB_eq_0_0_1
  · exact rows_innerACB_eq_0_0_2
  · exact rows_innerACB_eq_0_0_3
  · exact rows_innerACB_eq_0_0_4
  · exact rows_innerACB_eq_0_0_5
  · exact rows_innerACB_eq_0_0_6
  · exact rows_innerACB_eq_0_0_7
  · exact rows_innerACB_eq_1_0_0
  · exact rows_innerACB_eq_1_0_1
  · exact rows_innerACB_eq_1_0_2
  · exact rows_innerACB_eq_1_0_3
  · exact rows_innerACB_eq_1_0_4
  · exact rows_innerACB_eq_1_0_5
  · exact rows_innerACB_eq_1_0_6
  · exact rows_innerACB_eq_1_0_7

private def rows_assocBACData : List (List ℤ) := [decodeIntegerRow 16 3 1 21010900,
    decodeIntegerRow 16 3 1 23122048,
    decodeIntegerRow 16 3 1 26483560,
    decodeIntegerRow 16 3 1 7233744,
    decodeIntegerRow 16 3 1 23113300,
    decodeIntegerRow 16 3 1 22073728,
    decodeIntegerRow 16 3 1 35931560,
    decodeIntegerRow 16 3 1 26129104,
    decodeIntegerRow 16 3 1 23108944,
    decodeIntegerRow 16 3 1 20971480,
    decodeIntegerRow 16 3 1 7115648,
    decodeIntegerRow 16 3 1 26129260,
    decodeIntegerRow 16 3 1 21012304,
    decodeIntegerRow 16 3 1 19920280,
    decodeIntegerRow 16 3 1 16563328,
    decodeIntegerRow 16 3 1 7233260]

def rows_assocBAC (r : RightIndex 1 6 6) : List ℤ := rows_assocBACData.getD (rightPosition 1 6 6 r) []

private theorem rows_assocBAC_eq_0_0_0 : (tripleIndices 2 1 8).map ((HexagonAtoms616.assocBAC) ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8))) = rows_assocBAC ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_1 : (tripleIndices 2 1 8).map ((HexagonAtoms616.assocBAC) ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8))) = rows_assocBAC ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_2 : (tripleIndices 2 1 8).map ((HexagonAtoms616.assocBAC) ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8))) = rows_assocBAC ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_3 : (tripleIndices 2 1 8).map ((HexagonAtoms616.assocBAC) ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8))) = rows_assocBAC ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_4 : (tripleIndices 2 1 8).map ((HexagonAtoms616.assocBAC) ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8))) = rows_assocBAC ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_5 : (tripleIndices 2 1 8).map ((HexagonAtoms616.assocBAC) ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8))) = rows_assocBAC ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_6 : (tripleIndices 2 1 8).map ((HexagonAtoms616.assocBAC) ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8))) = rows_assocBAC ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_7 : (tripleIndices 2 1 8).map ((HexagonAtoms616.assocBAC) ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8))) = rows_assocBAC ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_0 : (tripleIndices 2 1 8).map ((HexagonAtoms616.assocBAC) ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8))) = rows_assocBAC ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_1 : (tripleIndices 2 1 8).map ((HexagonAtoms616.assocBAC) ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8))) = rows_assocBAC ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_2 : (tripleIndices 2 1 8).map ((HexagonAtoms616.assocBAC) ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8))) = rows_assocBAC ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_3 : (tripleIndices 2 1 8).map ((HexagonAtoms616.assocBAC) ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8))) = rows_assocBAC ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_4 : (tripleIndices 2 1 8).map ((HexagonAtoms616.assocBAC) ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8))) = rows_assocBAC ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_5 : (tripleIndices 2 1 8).map ((HexagonAtoms616.assocBAC) ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8))) = rows_assocBAC ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_6 : (tripleIndices 2 1 8).map ((HexagonAtoms616.assocBAC) ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8))) = rows_assocBAC ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_7 : (tripleIndices 2 1 8).map ((HexagonAtoms616.assocBAC) ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8))) = rows_assocBAC ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocBAC_data (r : RightIndex 1 6 6) : (tripleIndices 2 1 8).map ((HexagonAtoms616.assocBAC) r) = rows_assocBAC r := by
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

private def rows_innerRightBACData : List (List ℤ) := [decodeIntegerRow 16 3 1 21523387,
    decodeIntegerRow 16 3 1 21523351,
    decodeIntegerRow 16 3 1 21523363,
    decodeIntegerRow 16 3 1 21523359,
    decodeIntegerRow 16 3 1 21525547,
    decodeIntegerRow 16 3 1 21522631,
    decodeIntegerRow 16 3 1 21523603,
    decodeIntegerRow 16 3 1 21523279,
    decodeIntegerRow 16 3 1 23117683,
    decodeIntegerRow 16 3 1 20991919,
    decodeIntegerRow 16 3 1 7174453,
    decodeIntegerRow 16 3 1 26306329,
    decodeIntegerRow 16 3 1 21543043,
    decodeIntegerRow 16 3 1 21516799,
    decodeIntegerRow 16 3 1 21346213,
    decodeIntegerRow 16 3 1 21582409]

def rows_innerRightBAC (r : RightIndex 1 6 6) : List ℤ := rows_innerRightBACData.getD (rightPosition 1 6 6 r) []

private theorem rows_innerRightBAC_eq_0_0_0 : (tripleIndices 2 1 8).map ((HexagonAtoms616.innerRightBAC) ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8))) = rows_innerRightBAC ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_0_1 : (tripleIndices 2 1 8).map ((HexagonAtoms616.innerRightBAC) ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8))) = rows_innerRightBAC ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_0_2 : (tripleIndices 2 1 8).map ((HexagonAtoms616.innerRightBAC) ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8))) = rows_innerRightBAC ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_0_3 : (tripleIndices 2 1 8).map ((HexagonAtoms616.innerRightBAC) ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8))) = rows_innerRightBAC ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_0_4 : (tripleIndices 2 1 8).map ((HexagonAtoms616.innerRightBAC) ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8))) = rows_innerRightBAC ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_0_5 : (tripleIndices 2 1 8).map ((HexagonAtoms616.innerRightBAC) ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8))) = rows_innerRightBAC ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_0_6 : (tripleIndices 2 1 8).map ((HexagonAtoms616.innerRightBAC) ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8))) = rows_innerRightBAC ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_0_7 : (tripleIndices 2 1 8).map ((HexagonAtoms616.innerRightBAC) ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8))) = rows_innerRightBAC ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_0_0 : (tripleIndices 2 1 8).map ((HexagonAtoms616.innerRightBAC) ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8))) = rows_innerRightBAC ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_0_1 : (tripleIndices 2 1 8).map ((HexagonAtoms616.innerRightBAC) ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8))) = rows_innerRightBAC ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_0_2 : (tripleIndices 2 1 8).map ((HexagonAtoms616.innerRightBAC) ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8))) = rows_innerRightBAC ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_0_3 : (tripleIndices 2 1 8).map ((HexagonAtoms616.innerRightBAC) ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8))) = rows_innerRightBAC ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_0_4 : (tripleIndices 2 1 8).map ((HexagonAtoms616.innerRightBAC) ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8))) = rows_innerRightBAC ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_0_5 : (tripleIndices 2 1 8).map ((HexagonAtoms616.innerRightBAC) ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8))) = rows_innerRightBAC ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_0_6 : (tripleIndices 2 1 8).map ((HexagonAtoms616.innerRightBAC) ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8))) = rows_innerRightBAC ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_0_7 : (tripleIndices 2 1 8).map ((HexagonAtoms616.innerRightBAC) ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8))) = rows_innerRightBAC ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_innerRightBAC_data (r : RightIndex 1 6 6) : (tripleIndices 2 1 8).map ((HexagonAtoms616.innerRightBAC) r) = rows_innerRightBAC r := by
  fin_cases r
  · exact rows_innerRightBAC_eq_0_0_0
  · exact rows_innerRightBAC_eq_0_0_1
  · exact rows_innerRightBAC_eq_0_0_2
  · exact rows_innerRightBAC_eq_0_0_3
  · exact rows_innerRightBAC_eq_0_0_4
  · exact rows_innerRightBAC_eq_0_0_5
  · exact rows_innerRightBAC_eq_0_0_6
  · exact rows_innerRightBAC_eq_0_0_7
  · exact rows_innerRightBAC_eq_1_0_0
  · exact rows_innerRightBAC_eq_1_0_1
  · exact rows_innerRightBAC_eq_1_0_2
  · exact rows_innerRightBAC_eq_1_0_3
  · exact rows_innerRightBAC_eq_1_0_4
  · exact rows_innerRightBAC_eq_1_0_5
  · exact rows_innerRightBAC_eq_1_0_6
  · exact rows_innerRightBAC_eq_1_0_7

private def rows_assocCABData : List (List ℤ) := [decodeIntegerRow 16 3 1 6642526,
    decodeIntegerRow 16 3 1 18332446,
    decodeIntegerRow 16 3 1 27898546,
    decodeIntegerRow 16 3 1 7706866,
    decodeIntegerRow 16 3 1 21339646,
    decodeIntegerRow 16 3 1 21483966,
    decodeIntegerRow 16 3 1 21602066,
    decodeIntegerRow 16 3 1 21352786,
    decodeIntegerRow 16 3 1 21352762,
    decodeIntegerRow 16 3 1 21602118,
    decodeIntegerRow 16 3 1 21562698,
    decodeIntegerRow 16 3 1 21707062,
    decodeIntegerRow 16 3 1 7704922,
    decodeIntegerRow 16 3 1 27902758,
    decodeIntegerRow 16 3 1 24709738,
    decodeIntegerRow 16 3 1 36403222]

def rows_assocCAB (r : RightIndex 6 6 1) : List ℤ := rows_assocCABData.getD (rightPosition 6 6 1 r) []

private theorem rows_assocCAB_eq_0_0_0 : (tripleIndices 2 1 8).map ((HexagonAtoms616.assocCAB) ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_1 : (tripleIndices 2 1 8).map ((HexagonAtoms616.assocCAB) ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_2 : (tripleIndices 2 1 8).map ((HexagonAtoms616.assocCAB) ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_3 : (tripleIndices 2 1 8).map ((HexagonAtoms616.assocCAB) ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_4 : (tripleIndices 2 1 8).map ((HexagonAtoms616.assocCAB) ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_5 : (tripleIndices 2 1 8).map ((HexagonAtoms616.assocCAB) ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_6 : (tripleIndices 2 1 8).map ((HexagonAtoms616.assocCAB) ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_7 : (tripleIndices 2 1 8).map ((HexagonAtoms616.assocCAB) ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_0 : (tripleIndices 2 1 8).map ((HexagonAtoms616.assocCAB) ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_1 : (tripleIndices 2 1 8).map ((HexagonAtoms616.assocCAB) ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_2 : (tripleIndices 2 1 8).map ((HexagonAtoms616.assocCAB) ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_3 : (tripleIndices 2 1 8).map ((HexagonAtoms616.assocCAB) ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_4 : (tripleIndices 2 1 8).map ((HexagonAtoms616.assocCAB) ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_5 : (tripleIndices 2 1 8).map ((HexagonAtoms616.assocCAB) ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_6 : (tripleIndices 2 1 8).map ((HexagonAtoms616.assocCAB) ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_7 : (tripleIndices 2 1 8).map ((HexagonAtoms616.assocCAB) ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocCAB_data (r : RightIndex 6 6 1) : (tripleIndices 2 1 8).map ((HexagonAtoms616.assocCAB) r) = rows_assocCAB r := by
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

private def cols_assocABCData : List (List ℤ) := [decodeIntegerRow 16 3 1 21995024,
    decodeIntegerRow 16 3 1 20104000,
    decodeIntegerRow 16 3 1 16733920,
    decodeIntegerRow 16 3 1 35892220,
    decodeIntegerRow 16 3 1 16747024,
    decodeIntegerRow 16 3 1 35852800,
    decodeIntegerRow 16 3 1 20933600,
    decodeIntegerRow 16 3 1 23297020,
    decodeIntegerRow 16 3 1 16746880,
    decodeIntegerRow 16 3 1 7194352,
    decodeIntegerRow 16 3 1 22114580,
    decodeIntegerRow 16 3 1 23292640,
    decodeIntegerRow 16 3 1 21996480,
    decodeIntegerRow 16 3 1 22938352,
    decodeIntegerRow 16 3 1 26312980,
    decodeIntegerRow 16 3 1 35891680]

def cols_assocABC (r : LeftIndex 6 1 6) : List ℤ := cols_assocABCData.getD (leftPosition 6 1 6 r) []

private theorem cols_assocABC_eq_0_0_0 : (tripleIndices 2 1 8).map (fun j => (HexagonAtoms616.assocABC) j ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8))) = cols_assocABC ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_1 : (tripleIndices 2 1 8).map (fun j => (HexagonAtoms616.assocABC) j ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8))) = cols_assocABC ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_2 : (tripleIndices 2 1 8).map (fun j => (HexagonAtoms616.assocABC) j ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8))) = cols_assocABC ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_3 : (tripleIndices 2 1 8).map (fun j => (HexagonAtoms616.assocABC) j ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8))) = cols_assocABC ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_4 : (tripleIndices 2 1 8).map (fun j => (HexagonAtoms616.assocABC) j ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8))) = cols_assocABC ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_5 : (tripleIndices 2 1 8).map (fun j => (HexagonAtoms616.assocABC) j ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8))) = cols_assocABC ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_6 : (tripleIndices 2 1 8).map (fun j => (HexagonAtoms616.assocABC) j ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8))) = cols_assocABC ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_7 : (tripleIndices 2 1 8).map (fun j => (HexagonAtoms616.assocABC) j ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8))) = cols_assocABC ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_0 : (tripleIndices 2 1 8).map (fun j => (HexagonAtoms616.assocABC) j ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8))) = cols_assocABC ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_1 : (tripleIndices 2 1 8).map (fun j => (HexagonAtoms616.assocABC) j ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8))) = cols_assocABC ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_2 : (tripleIndices 2 1 8).map (fun j => (HexagonAtoms616.assocABC) j ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8))) = cols_assocABC ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_3 : (tripleIndices 2 1 8).map (fun j => (HexagonAtoms616.assocABC) j ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8))) = cols_assocABC ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_4 : (tripleIndices 2 1 8).map (fun j => (HexagonAtoms616.assocABC) j ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8))) = cols_assocABC ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_5 : (tripleIndices 2 1 8).map (fun j => (HexagonAtoms616.assocABC) j ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8))) = cols_assocABC ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_6 : (tripleIndices 2 1 8).map (fun j => (HexagonAtoms616.assocABC) j ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8))) = cols_assocABC ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_7 : (tripleIndices 2 1 8).map (fun j => (HexagonAtoms616.assocABC) j ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8))) = cols_assocABC ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_assocABC_data (r : LeftIndex 6 1 6) : (tripleIndices 2 1 8).map (fun j => (HexagonAtoms616.assocABC) j r) = cols_assocABC r := by
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

private def cols_right0Data : List (List ℤ) := [decodeIntegerRow 16 3 1 21995024,
    decodeIntegerRow 16 3 1 20104000,
    decodeIntegerRow 16 3 1 16733920,
    decodeIntegerRow 16 3 1 35892220,
    decodeIntegerRow 16 3 1 16747024,
    decodeIntegerRow 16 3 1 35852800,
    decodeIntegerRow 16 3 1 20933600,
    decodeIntegerRow 16 3 1 23297020,
    decodeIntegerRow 16 3 1 16746880,
    decodeIntegerRow 16 3 1 7194352,
    decodeIntegerRow 16 3 1 22114580,
    decodeIntegerRow 16 3 1 23292640,
    decodeIntegerRow 16 3 1 21996480,
    decodeIntegerRow 16 3 1 22938352,
    decodeIntegerRow 16 3 1 26312980,
    decodeIntegerRow 16 3 1 35891680]

def cols_right0 (r : LeftIndex 6 1 6) : List ℤ := cols_right0Data.getD (leftPosition 6 1 6 r) []

private theorem cols_right0_eq_0_0_0 : (tripleIndices 2 1 8).map (fun j => (right0Middle6 1 6) j ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8))) = cols_right0 ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_1 : (tripleIndices 2 1 8).map (fun j => (right0Middle6 1 6) j ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8))) = cols_right0 ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_2 : (tripleIndices 2 1 8).map (fun j => (right0Middle6 1 6) j ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8))) = cols_right0 ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_3 : (tripleIndices 2 1 8).map (fun j => (right0Middle6 1 6) j ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8))) = cols_right0 ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_4 : (tripleIndices 2 1 8).map (fun j => (right0Middle6 1 6) j ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8))) = cols_right0 ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_5 : (tripleIndices 2 1 8).map (fun j => (right0Middle6 1 6) j ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8))) = cols_right0 ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_6 : (tripleIndices 2 1 8).map (fun j => (right0Middle6 1 6) j ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8))) = cols_right0 ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_7 : (tripleIndices 2 1 8).map (fun j => (right0Middle6 1 6) j ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8))) = cols_right0 ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_0 : (tripleIndices 2 1 8).map (fun j => (right0Middle6 1 6) j ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8))) = cols_right0 ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_1 : (tripleIndices 2 1 8).map (fun j => (right0Middle6 1 6) j ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8))) = cols_right0 ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_2 : (tripleIndices 2 1 8).map (fun j => (right0Middle6 1 6) j ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8))) = cols_right0 ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_3 : (tripleIndices 2 1 8).map (fun j => (right0Middle6 1 6) j ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8))) = cols_right0 ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_4 : (tripleIndices 2 1 8).map (fun j => (right0Middle6 1 6) j ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8))) = cols_right0 ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_5 : (tripleIndices 2 1 8).map (fun j => (right0Middle6 1 6) j ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8))) = cols_right0 ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_6 : (tripleIndices 2 1 8).map (fun j => (right0Middle6 1 6) j ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8))) = cols_right0 ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_7 : (tripleIndices 2 1 8).map (fun j => (right0Middle6 1 6) j ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8))) = cols_right0 ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right0_data (r : LeftIndex 6 1 6) : (tripleIndices 2 1 8).map (fun j => (right0Middle6 1 6) j r) = cols_right0 r := by
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

private def cols_right1Data : List (List ℤ) := [decodeIntegerRow 16 5 2 15239226812,
    decodeIntegerRow 16 5 2 64184414012,
    decodeIntegerRow 16 5 2 78734571572,
    decodeIntegerRow 16 5 2 76786139060,
    decodeIntegerRow 16 5 2 63989414012,
    decodeIntegerRow 16 5 2 137309538812,
    decodeIntegerRow 16 5 2 75809576564,
    decodeIntegerRow 16 5 2 78736131572,
    decodeIntegerRow 16 5 2 78736134052,
    decodeIntegerRow 16 5 2 75809564060,
    decodeIntegerRow 16 5 2 15278288812,
    decodeIntegerRow 16 5 2 88598789012,
    decodeIntegerRow 16 5 2 76786126564,
    decodeIntegerRow 16 5 2 78734569052,
    decodeIntegerRow 16 5 2 88403164012,
    decodeIntegerRow 16 5 2 137348601812]

def cols_right1 (r : LeftIndex 6 1 6) : List ℤ := cols_right1Data.getD (leftPosition 6 1 6 r) []

private theorem cols_right1_eq_0_0_0 : (tripleIndices 2 1 8).map (fun j => (right1Middle6 1 6) j ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8))) = cols_right1 ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_0_1 : (tripleIndices 2 1 8).map (fun j => (right1Middle6 1 6) j ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8))) = cols_right1 ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_0_2 : (tripleIndices 2 1 8).map (fun j => (right1Middle6 1 6) j ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8))) = cols_right1 ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_0_3 : (tripleIndices 2 1 8).map (fun j => (right1Middle6 1 6) j ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8))) = cols_right1 ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_0_4 : (tripleIndices 2 1 8).map (fun j => (right1Middle6 1 6) j ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8))) = cols_right1 ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_0_5 : (tripleIndices 2 1 8).map (fun j => (right1Middle6 1 6) j ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8))) = cols_right1 ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_0_6 : (tripleIndices 2 1 8).map (fun j => (right1Middle6 1 6) j ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8))) = cols_right1 ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_0_7 : (tripleIndices 2 1 8).map (fun j => (right1Middle6 1 6) j ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8))) = cols_right1 ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_0_0 : (tripleIndices 2 1 8).map (fun j => (right1Middle6 1 6) j ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8))) = cols_right1 ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_0_1 : (tripleIndices 2 1 8).map (fun j => (right1Middle6 1 6) j ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8))) = cols_right1 ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_0_2 : (tripleIndices 2 1 8).map (fun j => (right1Middle6 1 6) j ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8))) = cols_right1 ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_0_3 : (tripleIndices 2 1 8).map (fun j => (right1Middle6 1 6) j ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8))) = cols_right1 ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_0_4 : (tripleIndices 2 1 8).map (fun j => (right1Middle6 1 6) j ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8))) = cols_right1 ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_0_5 : (tripleIndices 2 1 8).map (fun j => (right1Middle6 1 6) j ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8))) = cols_right1 ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_0_6 : (tripleIndices 2 1 8).map (fun j => (right1Middle6 1 6) j ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8))) = cols_right1 ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_0_7 : (tripleIndices 2 1 8).map (fun j => (right1Middle6 1 6) j ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8))) = cols_right1 ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right1_data (r : LeftIndex 6 1 6) : (tripleIndices 2 1 8).map (fun j => (right1Middle6 1 6) j r) = cols_right1 r := by
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

private def cols_left0Data : List (List ℤ) := [decodeIntegerRow 16 5 2 76278295312,
    decodeIntegerRow 16 5 2 76392225312,
    decodeIntegerRow 16 5 2 76390665312,
    decodeIntegerRow 16 5 2 76317420312,
    decodeIntegerRow 16 5 2 66528320272,
    decodeIntegerRow 16 5 2 137817382560,
    decodeIntegerRow 16 5 2 136840820064,
    decodeIntegerRow 16 5 2 90942382872,
    decodeIntegerRow 16 5 2 66528320352,
    decodeIntegerRow 16 5 2 14770507560,
    decodeIntegerRow 16 5 2 15747070064,
    decodeIntegerRow 16 5 2 90942382752,
    decodeIntegerRow 16 5 2 76278345312,
    decodeIntegerRow 16 5 2 76195350312,
    decodeIntegerRow 16 5 2 76196915312,
    decodeIntegerRow 16 5 2 76317345312]

def cols_left0 (r : LeftIndex 6 1 6) : List ℤ := cols_left0Data.getD (leftPosition 6 1 6 r) []

private theorem cols_left0_eq_0_0_0 : (tripleIndices 2 1 8).map (fun j => (left0Middle6 1 6) j ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8))) = cols_left0 ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_1 : (tripleIndices 2 1 8).map (fun j => (left0Middle6 1 6) j ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8))) = cols_left0 ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_2 : (tripleIndices 2 1 8).map (fun j => (left0Middle6 1 6) j ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8))) = cols_left0 ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_3 : (tripleIndices 2 1 8).map (fun j => (left0Middle6 1 6) j ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8))) = cols_left0 ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_4 : (tripleIndices 2 1 8).map (fun j => (left0Middle6 1 6) j ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8))) = cols_left0 ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_5 : (tripleIndices 2 1 8).map (fun j => (left0Middle6 1 6) j ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8))) = cols_left0 ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_6 : (tripleIndices 2 1 8).map (fun j => (left0Middle6 1 6) j ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8))) = cols_left0 ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_7 : (tripleIndices 2 1 8).map (fun j => (left0Middle6 1 6) j ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8))) = cols_left0 ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_0 : (tripleIndices 2 1 8).map (fun j => (left0Middle6 1 6) j ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8))) = cols_left0 ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_1 : (tripleIndices 2 1 8).map (fun j => (left0Middle6 1 6) j ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8))) = cols_left0 ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_2 : (tripleIndices 2 1 8).map (fun j => (left0Middle6 1 6) j ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8))) = cols_left0 ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_3 : (tripleIndices 2 1 8).map (fun j => (left0Middle6 1 6) j ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8))) = cols_left0 ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_4 : (tripleIndices 2 1 8).map (fun j => (left0Middle6 1 6) j ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8))) = cols_left0 ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_5 : (tripleIndices 2 1 8).map (fun j => (left0Middle6 1 6) j ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8))) = cols_left0 ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_6 : (tripleIndices 2 1 8).map (fun j => (left0Middle6 1 6) j ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8))) = cols_left0 ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_7 : (tripleIndices 2 1 8).map (fun j => (left0Middle6 1 6) j ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8))) = cols_left0 ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_left0_data (r : LeftIndex 6 1 6) : (tripleIndices 2 1 8).map (fun j => (left0Middle6 1 6) j r) = cols_left0 r := by
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

private def cols_left1Data : List (List ℤ) := [decodeIntegerRow 16 3 1 35932018,
    decodeIntegerRow 16 3 1 26131378,
    decodeIntegerRow 16 3 1 19935514,
    decodeIntegerRow 16 3 1 20971994,
    decodeIntegerRow 16 3 1 26481298,
    decodeIntegerRow 16 3 1 7234258,
    decodeIntegerRow 16 3 1 22034874,
    decodeIntegerRow 16 3 1 19922554,
    decodeIntegerRow 16 3 1 19922398,
    decodeIntegerRow 16 3 1 22035362,
    decodeIntegerRow 16 3 1 35813974,
    decodeIntegerRow 16 3 1 16561066,
    decodeIntegerRow 16 3 1 20972478,
    decodeIntegerRow 16 3 1 19935682,
    decodeIntegerRow 16 3 1 16919734,
    decodeIntegerRow 16 3 1 7116106]

def cols_left1 (r : LeftIndex 6 1 6) : List ℤ := cols_left1Data.getD (leftPosition 6 1 6 r) []

private theorem cols_left1_eq_0_0_0 : (tripleIndices 2 1 8).map (fun j => (left1Middle6 1 6) j ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8))) = cols_left1 ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_0_1 : (tripleIndices 2 1 8).map (fun j => (left1Middle6 1 6) j ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8))) = cols_left1 ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_0_2 : (tripleIndices 2 1 8).map (fun j => (left1Middle6 1 6) j ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8))) = cols_left1 ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_0_3 : (tripleIndices 2 1 8).map (fun j => (left1Middle6 1 6) j ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8))) = cols_left1 ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_0_4 : (tripleIndices 2 1 8).map (fun j => (left1Middle6 1 6) j ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8))) = cols_left1 ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_0_5 : (tripleIndices 2 1 8).map (fun j => (left1Middle6 1 6) j ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8))) = cols_left1 ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_0_6 : (tripleIndices 2 1 8).map (fun j => (left1Middle6 1 6) j ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8))) = cols_left1 ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_0_7 : (tripleIndices 2 1 8).map (fun j => (left1Middle6 1 6) j ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8))) = cols_left1 ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_0_0 : (tripleIndices 2 1 8).map (fun j => (left1Middle6 1 6) j ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8))) = cols_left1 ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_0_1 : (tripleIndices 2 1 8).map (fun j => (left1Middle6 1 6) j ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8))) = cols_left1 ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_0_2 : (tripleIndices 2 1 8).map (fun j => (left1Middle6 1 6) j ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8))) = cols_left1 ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_0_3 : (tripleIndices 2 1 8).map (fun j => (left1Middle6 1 6) j ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8))) = cols_left1 ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_0_4 : (tripleIndices 2 1 8).map (fun j => (left1Middle6 1 6) j ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8))) = cols_left1 ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_0_5 : (tripleIndices 2 1 8).map (fun j => (left1Middle6 1 6) j ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8))) = cols_left1 ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_0_6 : (tripleIndices 2 1 8).map (fun j => (left1Middle6 1 6) j ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8))) = cols_left1 ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_0_7 : (tripleIndices 2 1 8).map (fun j => (left1Middle6 1 6) j ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8))) = cols_left1 ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_left1_data (r : LeftIndex 6 1 6) : (tripleIndices 2 1 8).map (fun j => (left1Middle6 1 6) j r) = cols_left1 r := by
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

private def cols_right2Data : List (List ℤ) := [decodeIntegerRow 16 5 2 15278326564,
    decodeIntegerRow 16 5 2 63989256572,
    decodeIntegerRow 16 5 2 78735976612,
    decodeIntegerRow 16 5 2 76778351812,
    decodeIntegerRow 16 5 2 88403321572,
    decodeIntegerRow 16 5 2 15239264060,
    decodeIntegerRow 16 5 2 76786163812,
    decodeIntegerRow 16 5 2 73853476612,
    decodeIntegerRow 16 5 2 73853164012,
    decodeIntegerRow 16 5 2 76786101812,
    decodeIntegerRow 16 5 2 137348639060,
    decodeIntegerRow 16 5 2 64184571572,
    decodeIntegerRow 16 5 2 76778288812,
    decodeIntegerRow 16 5 2 78736289012,
    decodeIntegerRow 16 5 2 88598631572,
    decodeIntegerRow 16 5 2 137309576564]

def cols_right2 (r : LeftIndex 6 1 6) : List ℤ := cols_right2Data.getD (leftPosition 6 1 6 r) []

private theorem cols_right2_eq_0_0_0 : (tripleIndices 2 1 8).map (fun j => (right2Middle6 1 6) j ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8))) = cols_right2 ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_1 : (tripleIndices 2 1 8).map (fun j => (right2Middle6 1 6) j ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8))) = cols_right2 ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_2 : (tripleIndices 2 1 8).map (fun j => (right2Middle6 1 6) j ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8))) = cols_right2 ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_3 : (tripleIndices 2 1 8).map (fun j => (right2Middle6 1 6) j ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8))) = cols_right2 ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_4 : (tripleIndices 2 1 8).map (fun j => (right2Middle6 1 6) j ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8))) = cols_right2 ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_5 : (tripleIndices 2 1 8).map (fun j => (right2Middle6 1 6) j ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8))) = cols_right2 ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_6 : (tripleIndices 2 1 8).map (fun j => (right2Middle6 1 6) j ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8))) = cols_right2 ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_7 : (tripleIndices 2 1 8).map (fun j => (right2Middle6 1 6) j ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8))) = cols_right2 ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_0 : (tripleIndices 2 1 8).map (fun j => (right2Middle6 1 6) j ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8))) = cols_right2 ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_1 : (tripleIndices 2 1 8).map (fun j => (right2Middle6 1 6) j ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8))) = cols_right2 ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_2 : (tripleIndices 2 1 8).map (fun j => (right2Middle6 1 6) j ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8))) = cols_right2 ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_3 : (tripleIndices 2 1 8).map (fun j => (right2Middle6 1 6) j ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8))) = cols_right2 ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_4 : (tripleIndices 2 1 8).map (fun j => (right2Middle6 1 6) j ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8))) = cols_right2 ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_5 : (tripleIndices 2 1 8).map (fun j => (right2Middle6 1 6) j ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8))) = cols_right2 ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_6 : (tripleIndices 2 1 8).map (fun j => (right2Middle6 1 6) j ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8))) = cols_right2 ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_7 : (tripleIndices 2 1 8).map (fun j => (right2Middle6 1 6) j ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8))) = cols_right2 ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right2_data (r : LeftIndex 6 1 6) : (tripleIndices 2 1 8).map (fun j => (right2Middle6 1 6) j r) = cols_right2 r := by
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

theorem product0_eq : HexagonAtoms616.outerABC * HexagonAtoms616.assocABC = rowColumnMul rows_outerABC cols_assocABC :=
  (rowColumnMul_eq _ _ _ _ rows_outerABC_data cols_assocABC_data).symm

theorem product1_eq : HexagonAtoms616.assocBAC * HexagonAtoms616.innerABC = HexagonAtoms616.assocBAC :=
  Matrix.mul_one (m := Fin 2 × Fin 1 × Fin 8) (n := Fin 2 × Fin 1 × Fin 8) _

theorem product2_eq : HexagonAtoms616.innerRightABC * HexagonAtoms616.assocABC = HexagonAtoms616.assocABC :=
  Matrix.one_mul (m := Fin 2 × Fin 1 × Fin 8) (n := Fin 2 × Fin 1 × Fin 8) _

theorem product3_eq : HexagonAtoms616.inverseACB * right0Middle6 1 6 = rowColumnMul rows_inverseACB cols_right0 :=
  (rowColumnMul_eq _ _ _ _ rows_inverseACB_data cols_right0_data).symm

theorem product4_eq : HexagonAtoms616.innerACB * right1Middle6 1 6 = rowColumnMul rows_innerACB cols_right1 :=
  (rowColumnMul_eq _ _ _ _ rows_innerACB_data cols_right1_data).symm

theorem product5_eq : HexagonAtoms616.assocBAC * left0Middle6 1 6 = rowColumnMul rows_assocBAC cols_left0 :=
  (rowColumnMul_eq _ _ _ _ rows_assocBAC_data cols_left0_data).symm

theorem product6_eq : HexagonAtoms616.innerRightBAC * left1Middle6 1 6 = rowColumnMul rows_innerRightBAC cols_left1 :=
  (rowColumnMul_eq _ _ _ _ rows_innerRightBAC_data cols_left1_data).symm

theorem product7_eq : HexagonAtoms616.assocCAB * right2Middle6 1 6 = rowColumnMul rows_assocCAB cols_right2 :=
  (rowColumnMul_eq _ _ _ _ rows_assocCAB_data cols_right2_data).symm

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn616
