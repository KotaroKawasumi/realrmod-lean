import RMod.BrundanEllis.StackingReferenceHexagonAtoms663
import RMod.BrundanEllis.StackingReferenceHexagonMiddle6
import RMod.BrundanEllis.StackingReferenceRowColumnCheck

/-! Verified row and column lists. Each subsequent scalar product traverses
these lists directly, without repeated lookup into the original matrices. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn663
open Superfusion

theorem assocBAC_alias : HexagonAtoms663.assocBAC = HexagonAtoms663.assocABC :=
  HexagonAtoms663.assocBAC_eq.symm.trans HexagonAtoms663.assocABC_eq

theorem innerRightBAC_alias : HexagonAtoms663.innerRightBAC = HexagonAtoms663.innerRightABC :=
  HexagonAtoms663.innerRightBAC_eq.symm.trans HexagonAtoms663.innerRightABC_eq

private def rows_assocABCData : List (List ℤ) := [decodeIntegerRow 16 3 1 5515360,
    decodeIntegerRow 16 3 1 16014560,
    decodeIntegerRow 16 3 1 25619360,
    decodeIntegerRow 16 3 1 34226080,
    decodeIntegerRow 16 3 1 8821888,
    decodeIntegerRow 16 3 1 17431232,
    decodeIntegerRow 16 3 1 16009680,
    decodeIntegerRow 16 3 1 5513680,
    decodeIntegerRow 16 3 1 17112416,
    decodeIntegerRow 16 3 1 8715616,
    decodeIntegerRow 16 3 1 37400200,
    decodeIntegerRow 16 3 1 26638520,
    decodeIntegerRow 16 3 1 16403360,
    decodeIntegerRow 16 3 1 5644960,
    decodeIntegerRow 16 3 1 8716960,
    decodeIntegerRow 16 3 1 17116320]

def rows_assocABC (r : RightIndex 6 6 3) : List ℤ := rows_assocABCData.getD (rightPosition 6 6 3 r) []

private theorem rows_assocABC_eq_0_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms663.assocABC) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = rows_assocABC ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms663.assocABC) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = rows_assocABC ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_1_0 : (tripleIndices 2 4 2).map ((HexagonAtoms663.assocABC) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = rows_assocABC ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_1_1 : (tripleIndices 2 4 2).map ((HexagonAtoms663.assocABC) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = rows_assocABC ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms663.assocABC) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = rows_assocABC ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms663.assocABC) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = rows_assocABC ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_1_0 : (tripleIndices 2 4 2).map ((HexagonAtoms663.assocABC) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = rows_assocABC ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_1_1 : (tripleIndices 2 4 2).map ((HexagonAtoms663.assocABC) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = rows_assocABC ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_2_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms663.assocABC) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = rows_assocABC ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_2_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms663.assocABC) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = rows_assocABC ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_2_1_0 : (tripleIndices 2 4 2).map ((HexagonAtoms663.assocABC) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = rows_assocABC ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_2_1_1 : (tripleIndices 2 4 2).map ((HexagonAtoms663.assocABC) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = rows_assocABC ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_3_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms663.assocABC) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = rows_assocABC ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_3_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms663.assocABC) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = rows_assocABC ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_3_1_0 : (tripleIndices 2 4 2).map ((HexagonAtoms663.assocABC) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = rows_assocABC ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_3_1_1 : (tripleIndices 2 4 2).map ((HexagonAtoms663.assocABC) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = rows_assocABC ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocABC_data (r : RightIndex 6 6 3) : (tripleIndices 2 4 2).map ((HexagonAtoms663.assocABC) r) = rows_assocABC r := by
  fin_cases r
  · exact rows_assocABC_eq_0_0_0
  · exact rows_assocABC_eq_0_0_1
  · exact rows_assocABC_eq_0_1_0
  · exact rows_assocABC_eq_0_1_1
  · exact rows_assocABC_eq_1_0_0
  · exact rows_assocABC_eq_1_0_1
  · exact rows_assocABC_eq_1_1_0
  · exact rows_assocABC_eq_1_1_1
  · exact rows_assocABC_eq_2_0_0
  · exact rows_assocABC_eq_2_0_1
  · exact rows_assocABC_eq_2_1_0
  · exact rows_assocABC_eq_2_1_1
  · exact rows_assocABC_eq_3_0_0
  · exact rows_assocABC_eq_3_0_1
  · exact rows_assocABC_eq_3_1_0
  · exact rows_assocABC_eq_3_1_1

private def rows_inverseACBData : List (List ℤ) := [decodeIntegerRow 16 3 1 23058526,
    decodeIntegerRow 16 3 1 21877402,
    decodeIntegerRow 16 3 1 7167166,
    decodeIntegerRow 16 3 1 16718522,
    decodeIntegerRow 16 3 1 26323826,
    decodeIntegerRow 16 3 1 35878102,
    decodeIntegerRow 16 3 1 21877906,
    decodeIntegerRow 16 3 1 23058742,
    decodeIntegerRow 16 3 1 20814538,
    decodeIntegerRow 16 3 1 19869934,
    decodeIntegerRow 16 3 1 16762262,
    decodeIntegerRow 16 3 1 7181746,
    decodeIntegerRow 16 3 1 7180282,
    decodeIntegerRow 16 3 1 16757886,
    decodeIntegerRow 16 3 1 23176678,
    decodeIntegerRow 16 3 1 22231714]

def rows_inverseACB (r : LeftIndex 6 3 6) : List ℤ := rows_inverseACBData.getD (leftPosition 6 3 6 r) []

private theorem rows_inverseACB_eq_0_0_0 : (tripleIndices 4 2 2).map ((HexagonAtoms663.inverseACB) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_1 : (tripleIndices 4 2 2).map ((HexagonAtoms663.inverseACB) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_0 : (tripleIndices 4 2 2).map ((HexagonAtoms663.inverseACB) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = rows_inverseACB ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_1 : (tripleIndices 4 2 2).map ((HexagonAtoms663.inverseACB) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = rows_inverseACB ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_0 : (tripleIndices 4 2 2).map ((HexagonAtoms663.inverseACB) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_1 : (tripleIndices 4 2 2).map ((HexagonAtoms663.inverseACB) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_0 : (tripleIndices 4 2 2).map ((HexagonAtoms663.inverseACB) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = rows_inverseACB ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_1 : (tripleIndices 4 2 2).map ((HexagonAtoms663.inverseACB) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = rows_inverseACB ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_0 : (tripleIndices 4 2 2).map ((HexagonAtoms663.inverseACB) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_1 : (tripleIndices 4 2 2).map ((HexagonAtoms663.inverseACB) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_1_0 : (tripleIndices 4 2 2).map ((HexagonAtoms663.inverseACB) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = rows_inverseACB ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_1_1 : (tripleIndices 4 2 2).map ((HexagonAtoms663.inverseACB) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = rows_inverseACB ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_0 : (tripleIndices 4 2 2).map ((HexagonAtoms663.inverseACB) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_1 : (tripleIndices 4 2 2).map ((HexagonAtoms663.inverseACB) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_1_0 : (tripleIndices 4 2 2).map ((HexagonAtoms663.inverseACB) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = rows_inverseACB ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_1_1 : (tripleIndices 4 2 2).map ((HexagonAtoms663.inverseACB) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = rows_inverseACB ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_inverseACB_data (r : LeftIndex 6 3 6) : (tripleIndices 4 2 2).map ((HexagonAtoms663.inverseACB) r) = rows_inverseACB r := by
  fin_cases r
  · exact rows_inverseACB_eq_0_0_0
  · exact rows_inverseACB_eq_0_0_1
  · exact rows_inverseACB_eq_0_1_0
  · exact rows_inverseACB_eq_0_1_1
  · exact rows_inverseACB_eq_1_0_0
  · exact rows_inverseACB_eq_1_0_1
  · exact rows_inverseACB_eq_1_1_0
  · exact rows_inverseACB_eq_1_1_1
  · exact rows_inverseACB_eq_2_0_0
  · exact rows_inverseACB_eq_2_0_1
  · exact rows_inverseACB_eq_2_1_0
  · exact rows_inverseACB_eq_2_1_1
  · exact rows_inverseACB_eq_3_0_0
  · exact rows_inverseACB_eq_3_0_1
  · exact rows_inverseACB_eq_3_1_0
  · exact rows_inverseACB_eq_3_1_1

private def rows_assocBCAData : List (List ℤ) := [decodeIntegerRow 16 3 1 19988194,
    decodeIntegerRow 16 3 1 21169318,
    decodeIntegerRow 16 3 1 35879554,
    decodeIntegerRow 16 3 1 26328198,
    decodeIntegerRow 16 3 1 16722894,
    decodeIntegerRow 16 3 1 7168618,
    decodeIntegerRow 16 3 1 21168814,
    decodeIntegerRow 16 3 1 19987978,
    decodeIntegerRow 16 3 1 22232182,
    decodeIntegerRow 16 3 1 23176786,
    decodeIntegerRow 16 3 1 26284458,
    decodeIntegerRow 16 3 1 35864974,
    decodeIntegerRow 16 3 1 35866438,
    decodeIntegerRow 16 3 1 26288834,
    decodeIntegerRow 16 3 1 19870042,
    decodeIntegerRow 16 3 1 20815006]

def rows_assocBCA (r : RightIndex 6 3 6) : List ℤ := rows_assocBCAData.getD (rightPosition 6 3 6 r) []

private theorem rows_assocBCA_eq_0_0_0 : (tripleIndices 4 2 2).map ((HexagonAtoms663.assocBCA) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = rows_assocBCA ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_1 : (tripleIndices 4 2 2).map ((HexagonAtoms663.assocBCA) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = rows_assocBCA ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_0 : (tripleIndices 4 2 2).map ((HexagonAtoms663.assocBCA) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = rows_assocBCA ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_1 : (tripleIndices 4 2 2).map ((HexagonAtoms663.assocBCA) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = rows_assocBCA ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_0 : (tripleIndices 4 2 2).map ((HexagonAtoms663.assocBCA) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = rows_assocBCA ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_1 : (tripleIndices 4 2 2).map ((HexagonAtoms663.assocBCA) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = rows_assocBCA ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_0 : (tripleIndices 4 2 2).map ((HexagonAtoms663.assocBCA) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = rows_assocBCA ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_1 : (tripleIndices 4 2 2).map ((HexagonAtoms663.assocBCA) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = rows_assocBCA ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_0 : (tripleIndices 4 2 2).map ((HexagonAtoms663.assocBCA) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = rows_assocBCA ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_1 : (tripleIndices 4 2 2).map ((HexagonAtoms663.assocBCA) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = rows_assocBCA ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_1_0 : (tripleIndices 4 2 2).map ((HexagonAtoms663.assocBCA) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = rows_assocBCA ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_1_1 : (tripleIndices 4 2 2).map ((HexagonAtoms663.assocBCA) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = rows_assocBCA ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_0 : (tripleIndices 4 2 2).map ((HexagonAtoms663.assocBCA) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = rows_assocBCA ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_1 : (tripleIndices 4 2 2).map ((HexagonAtoms663.assocBCA) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = rows_assocBCA ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_1_0 : (tripleIndices 4 2 2).map ((HexagonAtoms663.assocBCA) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = rows_assocBCA ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_1_1 : (tripleIndices 4 2 2).map ((HexagonAtoms663.assocBCA) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = rows_assocBCA ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocBCA_data (r : RightIndex 6 3 6) : (tripleIndices 4 2 2).map ((HexagonAtoms663.assocBCA) r) = rows_assocBCA r := by
  fin_cases r
  · exact rows_assocBCA_eq_0_0_0
  · exact rows_assocBCA_eq_0_0_1
  · exact rows_assocBCA_eq_0_1_0
  · exact rows_assocBCA_eq_0_1_1
  · exact rows_assocBCA_eq_1_0_0
  · exact rows_assocBCA_eq_1_0_1
  · exact rows_assocBCA_eq_1_1_0
  · exact rows_assocBCA_eq_1_1_1
  · exact rows_assocBCA_eq_2_0_0
  · exact rows_assocBCA_eq_2_0_1
  · exact rows_assocBCA_eq_2_1_0
  · exact rows_assocBCA_eq_2_1_1
  · exact rows_assocBCA_eq_3_0_0
  · exact rows_assocBCA_eq_3_0_1
  · exact rows_assocBCA_eq_3_1_0
  · exact rows_assocBCA_eq_3_1_1

private def rows_assocCABData : List (List ℤ) := [decodeIntegerRow 16 3 1 6471448,
    decodeIntegerRow 16 3 1 15104408,
    decodeIntegerRow 16 3 1 7890076,
    decodeIntegerRow 16 3 1 18415524,
    decodeIntegerRow 16 3 1 24635352,
    decodeIntegerRow 16 3 1 35157592,
    decodeIntegerRow 16 3 1 27937724,
    decodeIntegerRow 16 3 1 36573316,
    decodeIntegerRow 16 3 1 15183192,
    decodeIntegerRow 16 3 1 6812632,
    decodeIntegerRow 16 3 1 24788604,
    decodeIntegerRow 16 3 1 35524036,
    decodeIntegerRow 16 3 1 35525032,
    decodeIntegerRow 16 3 1 24792872,
    decodeIntegerRow 16 3 1 6814564,
    decodeIntegerRow 16 3 1 15187676]

def rows_assocCAB (r : RightIndex 3 6 6) : List ℤ := rows_assocCABData.getD (rightPosition 3 6 6 r) []

private theorem rows_assocCAB_eq_0_0_0 : (tripleIndices 4 2 2).map ((HexagonAtoms663.assocCAB) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_1 : (tripleIndices 4 2 2).map ((HexagonAtoms663.assocCAB) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_0 : (tripleIndices 4 2 2).map ((HexagonAtoms663.assocCAB) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = rows_assocCAB ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_1 : (tripleIndices 4 2 2).map ((HexagonAtoms663.assocCAB) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = rows_assocCAB ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_2_0 : (tripleIndices 4 2 2).map ((HexagonAtoms663.assocCAB) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = rows_assocCAB ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_2_1 : (tripleIndices 4 2 2).map ((HexagonAtoms663.assocCAB) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = rows_assocCAB ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_3_0 : (tripleIndices 4 2 2).map ((HexagonAtoms663.assocCAB) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = rows_assocCAB ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_3_1 : (tripleIndices 4 2 2).map ((HexagonAtoms663.assocCAB) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = rows_assocCAB ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_0 : (tripleIndices 4 2 2).map ((HexagonAtoms663.assocCAB) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_1 : (tripleIndices 4 2 2).map ((HexagonAtoms663.assocCAB) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_0 : (tripleIndices 4 2 2).map ((HexagonAtoms663.assocCAB) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = rows_assocCAB ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_1 : (tripleIndices 4 2 2).map ((HexagonAtoms663.assocCAB) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = rows_assocCAB ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_2_0 : (tripleIndices 4 2 2).map ((HexagonAtoms663.assocCAB) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = rows_assocCAB ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_2_1 : (tripleIndices 4 2 2).map ((HexagonAtoms663.assocCAB) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = rows_assocCAB ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_3_0 : (tripleIndices 4 2 2).map ((HexagonAtoms663.assocCAB) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = rows_assocCAB ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_3_1 : (tripleIndices 4 2 2).map ((HexagonAtoms663.assocCAB) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = rows_assocCAB ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocCAB_data (r : RightIndex 3 6 6) : (tripleIndices 4 2 2).map ((HexagonAtoms663.assocCAB) r) = rows_assocCAB r := by
  fin_cases r
  · exact rows_assocCAB_eq_0_0_0
  · exact rows_assocCAB_eq_0_0_1
  · exact rows_assocCAB_eq_0_1_0
  · exact rows_assocCAB_eq_0_1_1
  · exact rows_assocCAB_eq_0_2_0
  · exact rows_assocCAB_eq_0_2_1
  · exact rows_assocCAB_eq_0_3_0
  · exact rows_assocCAB_eq_0_3_1
  · exact rows_assocCAB_eq_1_0_0
  · exact rows_assocCAB_eq_1_0_1
  · exact rows_assocCAB_eq_1_1_0
  · exact rows_assocCAB_eq_1_1_1
  · exact rows_assocCAB_eq_1_2_0
  · exact rows_assocCAB_eq_1_2_1
  · exact rows_assocCAB_eq_1_3_0
  · exact rows_assocCAB_eq_1_3_1

private def cols_innerABCData : List (List ℤ) := [decodeIntegerRow 16 3 1 21523603,
    decodeIntegerRow 16 3 1 21523441,
    decodeIntegerRow 16 3 1 21521173,
    decodeIntegerRow 16 3 1 21522631,
    decodeIntegerRow 16 3 1 21523357,
    decodeIntegerRow 16 3 1 21523359,
    decodeIntegerRow 16 3 1 21523387,
    decodeIntegerRow 16 3 1 21523369,
    decodeIntegerRow 16 3 1 35872267,
    decodeIntegerRow 16 3 1 26306329,
    decodeIntegerRow 16 3 1 23117683,
    decodeIntegerRow 16 3 1 22054801,
    decodeIntegerRow 16 3 1 21346213,
    decodeIntegerRow 16 3 1 21464311,
    decodeIntegerRow 16 3 1 21503677,
    decodeIntegerRow 16 3 1 21516799]

def cols_innerABC (r : LeftIndex 6 6 3) : List ℤ := cols_innerABCData.getD (leftPosition 6 6 3 r) []

private theorem cols_innerABC_eq_0_0_0 : (tripleIndices 2 4 2).map (fun j => (HexagonAtoms663.innerABC) j ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = cols_innerABC ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_0_1 : (tripleIndices 2 4 2).map (fun j => (HexagonAtoms663.innerABC) j ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = cols_innerABC ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_1_0 : (tripleIndices 2 4 2).map (fun j => (HexagonAtoms663.innerABC) j ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = cols_innerABC ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_1_1 : (tripleIndices 2 4 2).map (fun j => (HexagonAtoms663.innerABC) j ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = cols_innerABC ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_2_0 : (tripleIndices 2 4 2).map (fun j => (HexagonAtoms663.innerABC) j ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = cols_innerABC ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_2_1 : (tripleIndices 2 4 2).map (fun j => (HexagonAtoms663.innerABC) j ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = cols_innerABC ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_3_0 : (tripleIndices 2 4 2).map (fun j => (HexagonAtoms663.innerABC) j ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = cols_innerABC ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_3_1 : (tripleIndices 2 4 2).map (fun j => (HexagonAtoms663.innerABC) j ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = cols_innerABC ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_0_0 : (tripleIndices 2 4 2).map (fun j => (HexagonAtoms663.innerABC) j ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = cols_innerABC ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_0_1 : (tripleIndices 2 4 2).map (fun j => (HexagonAtoms663.innerABC) j ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = cols_innerABC ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_1_0 : (tripleIndices 2 4 2).map (fun j => (HexagonAtoms663.innerABC) j ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = cols_innerABC ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_1_1 : (tripleIndices 2 4 2).map (fun j => (HexagonAtoms663.innerABC) j ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = cols_innerABC ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_2_0 : (tripleIndices 2 4 2).map (fun j => (HexagonAtoms663.innerABC) j ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = cols_innerABC ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_2_1 : (tripleIndices 2 4 2).map (fun j => (HexagonAtoms663.innerABC) j ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = cols_innerABC ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_3_0 : (tripleIndices 2 4 2).map (fun j => (HexagonAtoms663.innerABC) j ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = cols_innerABC ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_3_1 : (tripleIndices 2 4 2).map (fun j => (HexagonAtoms663.innerABC) j ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = cols_innerABC ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_innerABC_data (r : LeftIndex 6 6 3) : (tripleIndices 2 4 2).map (fun j => (HexagonAtoms663.innerABC) j r) = cols_innerABC r := by
  fin_cases r
  · exact cols_innerABC_eq_0_0_0
  · exact cols_innerABC_eq_0_0_1
  · exact cols_innerABC_eq_0_1_0
  · exact cols_innerABC_eq_0_1_1
  · exact cols_innerABC_eq_0_2_0
  · exact cols_innerABC_eq_0_2_1
  · exact cols_innerABC_eq_0_3_0
  · exact cols_innerABC_eq_0_3_1
  · exact cols_innerABC_eq_1_0_0
  · exact cols_innerABC_eq_1_0_1
  · exact cols_innerABC_eq_1_1_0
  · exact cols_innerABC_eq_1_1_1
  · exact cols_innerABC_eq_1_2_0
  · exact cols_innerABC_eq_1_2_1
  · exact cols_innerABC_eq_1_3_0
  · exact cols_innerABC_eq_1_3_1

private def cols_right0Data : List (List ℤ) := [decodeIntegerRow 16 3 1 7889128,
    decodeIntegerRow 16 3 1 18411368,
    decodeIntegerRow 16 3 1 36573316,
    decodeIntegerRow 16 3 1 27937724,
    decodeIntegerRow 16 3 1 15104408,
    decodeIntegerRow 16 3 1 6471448,
    decodeIntegerRow 16 3 1 24631196,
    decodeIntegerRow 16 3 1 35156644,
    decodeIntegerRow 16 3 1 27859044,
    decodeIntegerRow 16 3 1 36232156,
    decodeIntegerRow 16 3 1 18253848,
    decodeIntegerRow 16 3 1 7521688,
    decodeIntegerRow 16 3 1 35524036,
    decodeIntegerRow 16 3 1 24788604,
    decodeIntegerRow 16 3 1 6812632,
    decodeIntegerRow 16 3 1 15183192]

def cols_right0 (r : LeftIndex 6 6 3) : List ℤ := cols_right0Data.getD (leftPosition 6 6 3 r) []

private theorem cols_right0_eq_0_0_0 : (tripleIndices 4 2 2).map (fun j => (right0Middle6 6 3) j ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = cols_right0 ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_1 : (tripleIndices 4 2 2).map (fun j => (right0Middle6 6 3) j ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = cols_right0 ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_0 : (tripleIndices 4 2 2).map (fun j => (right0Middle6 6 3) j ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = cols_right0 ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_1 : (tripleIndices 4 2 2).map (fun j => (right0Middle6 6 3) j ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = cols_right0 ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_2_0 : (tripleIndices 4 2 2).map (fun j => (right0Middle6 6 3) j ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = cols_right0 ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_2_1 : (tripleIndices 4 2 2).map (fun j => (right0Middle6 6 3) j ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = cols_right0 ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_3_0 : (tripleIndices 4 2 2).map (fun j => (right0Middle6 6 3) j ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = cols_right0 ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_3_1 : (tripleIndices 4 2 2).map (fun j => (right0Middle6 6 3) j ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = cols_right0 ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_0 : (tripleIndices 4 2 2).map (fun j => (right0Middle6 6 3) j ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = cols_right0 ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_1 : (tripleIndices 4 2 2).map (fun j => (right0Middle6 6 3) j ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = cols_right0 ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_0 : (tripleIndices 4 2 2).map (fun j => (right0Middle6 6 3) j ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = cols_right0 ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_1 : (tripleIndices 4 2 2).map (fun j => (right0Middle6 6 3) j ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = cols_right0 ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_2_0 : (tripleIndices 4 2 2).map (fun j => (right0Middle6 6 3) j ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = cols_right0 ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_2_1 : (tripleIndices 4 2 2).map (fun j => (right0Middle6 6 3) j ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = cols_right0 ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_3_0 : (tripleIndices 4 2 2).map (fun j => (right0Middle6 6 3) j ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = cols_right0 ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_3_1 : (tripleIndices 4 2 2).map (fun j => (right0Middle6 6 3) j ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = cols_right0 ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right0_data (r : LeftIndex 6 6 3) : (tripleIndices 4 2 2).map (fun j => (right0Middle6 6 3) j r) = cols_right0 r := by
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

private def cols_left0Data : List (List ℤ) := [decodeIntegerRow 16 3 1 7889128,
    decodeIntegerRow 16 3 1 18411368,
    decodeIntegerRow 16 3 1 36573316,
    decodeIntegerRow 16 3 1 27937724,
    decodeIntegerRow 16 3 1 15104408,
    decodeIntegerRow 16 3 1 6471448,
    decodeIntegerRow 16 3 1 24631196,
    decodeIntegerRow 16 3 1 35156644,
    decodeIntegerRow 16 3 1 27859044,
    decodeIntegerRow 16 3 1 36232156,
    decodeIntegerRow 16 3 1 18253848,
    decodeIntegerRow 16 3 1 7521688,
    decodeIntegerRow 16 3 1 35524036,
    decodeIntegerRow 16 3 1 24788604,
    decodeIntegerRow 16 3 1 6812632,
    decodeIntegerRow 16 3 1 15183192]

def cols_left0 (r : LeftIndex 6 6 3) : List ℤ := cols_left0Data.getD (leftPosition 6 6 3 r) []

private theorem cols_left0_eq_0_0_0 : (tripleIndices 4 2 2).map (fun j => (left0Middle6 6 3) j ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = cols_left0 ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_1 : (tripleIndices 4 2 2).map (fun j => (left0Middle6 6 3) j ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = cols_left0 ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_0 : (tripleIndices 4 2 2).map (fun j => (left0Middle6 6 3) j ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = cols_left0 ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_1 : (tripleIndices 4 2 2).map (fun j => (left0Middle6 6 3) j ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = cols_left0 ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_2_0 : (tripleIndices 4 2 2).map (fun j => (left0Middle6 6 3) j ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = cols_left0 ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_2_1 : (tripleIndices 4 2 2).map (fun j => (left0Middle6 6 3) j ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = cols_left0 ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_3_0 : (tripleIndices 4 2 2).map (fun j => (left0Middle6 6 3) j ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = cols_left0 ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_3_1 : (tripleIndices 4 2 2).map (fun j => (left0Middle6 6 3) j ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = cols_left0 ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_0 : (tripleIndices 4 2 2).map (fun j => (left0Middle6 6 3) j ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = cols_left0 ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_1 : (tripleIndices 4 2 2).map (fun j => (left0Middle6 6 3) j ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = cols_left0 ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_0 : (tripleIndices 4 2 2).map (fun j => (left0Middle6 6 3) j ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = cols_left0 ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_1 : (tripleIndices 4 2 2).map (fun j => (left0Middle6 6 3) j ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = cols_left0 ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_2_0 : (tripleIndices 4 2 2).map (fun j => (left0Middle6 6 3) j ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = cols_left0 ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_2_1 : (tripleIndices 4 2 2).map (fun j => (left0Middle6 6 3) j ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = cols_left0 ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_3_0 : (tripleIndices 4 2 2).map (fun j => (left0Middle6 6 3) j ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = cols_left0 ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_3_1 : (tripleIndices 4 2 2).map (fun j => (left0Middle6 6 3) j ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = cols_left0 ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_left0_data (r : LeftIndex 6 6 3) : (tripleIndices 4 2 2).map (fun j => (left0Middle6 6 3) j r) = cols_left0 r := by
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

private def cols_right2Data : List (List ℤ) := [decodeIntegerRow 16 5 2 137914295352,
    decodeIntegerRow 16 5 2 90958165560,
    decodeIntegerRow 16 5 2 136742357872,
    decodeIntegerRow 16 5 2 86035978064,
    decodeIntegerRow 16 5 2 66551603064,
    decodeIntegerRow 16 5 2 15845482872,
    decodeIntegerRow 16 5 2 61630040560,
    decodeIntegerRow 16 5 2 14673670352,
    decodeIntegerRow 16 5 2 90926915064,
    decodeIntegerRow 16 5 2 137720545272,
    decodeIntegerRow 16 5 2 66505038064,
    decodeIntegerRow 16 5 2 15648657872,
    decodeIntegerRow 16 5 2 15648607752,
    decodeIntegerRow 16 5 2 66504727560,
    decodeIntegerRow 16 5 2 137720470352,
    decodeIntegerRow 16 5 2 90926600560]

def cols_right2 (r : LeftIndex 6 6 3) : List ℤ := cols_right2Data.getD (leftPosition 6 6 3 r) []

private theorem cols_right2_eq_0_0_0 : (tripleIndices 4 2 2).map (fun j => (right2Middle6 6 3) j ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = cols_right2 ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_1 : (tripleIndices 4 2 2).map (fun j => (right2Middle6 6 3) j ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = cols_right2 ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_0 : (tripleIndices 4 2 2).map (fun j => (right2Middle6 6 3) j ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = cols_right2 ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_1 : (tripleIndices 4 2 2).map (fun j => (right2Middle6 6 3) j ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = cols_right2 ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_2_0 : (tripleIndices 4 2 2).map (fun j => (right2Middle6 6 3) j ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = cols_right2 ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_2_1 : (tripleIndices 4 2 2).map (fun j => (right2Middle6 6 3) j ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = cols_right2 ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_3_0 : (tripleIndices 4 2 2).map (fun j => (right2Middle6 6 3) j ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = cols_right2 ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_3_1 : (tripleIndices 4 2 2).map (fun j => (right2Middle6 6 3) j ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = cols_right2 ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_0 : (tripleIndices 4 2 2).map (fun j => (right2Middle6 6 3) j ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = cols_right2 ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_1 : (tripleIndices 4 2 2).map (fun j => (right2Middle6 6 3) j ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = cols_right2 ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_0 : (tripleIndices 4 2 2).map (fun j => (right2Middle6 6 3) j ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = cols_right2 ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_1 : (tripleIndices 4 2 2).map (fun j => (right2Middle6 6 3) j ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = cols_right2 ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_2_0 : (tripleIndices 4 2 2).map (fun j => (right2Middle6 6 3) j ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = cols_right2 ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_2_1 : (tripleIndices 4 2 2).map (fun j => (right2Middle6 6 3) j ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = cols_right2 ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_3_0 : (tripleIndices 4 2 2).map (fun j => (right2Middle6 6 3) j ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = cols_right2 ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_3_1 : (tripleIndices 4 2 2).map (fun j => (right2Middle6 6 3) j ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = cols_right2 ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right2_data (r : LeftIndex 6 6 3) : (tripleIndices 4 2 2).map (fun j => (right2Middle6 6 3) j r) = cols_right2 r := by
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

theorem product0_eq : HexagonAtoms663.outerABC * HexagonAtoms663.assocABC = HexagonAtoms663.assocABC :=
  Matrix.one_mul (m := Fin 4 × Fin 2 × Fin 2) (n := Fin 2 × Fin 4 × Fin 2) _

theorem product1_eq : HexagonAtoms663.assocABC * HexagonAtoms663.innerABC = rowColumnMul rows_assocABC cols_innerABC :=
  (rowColumnMul_eq _ _ _ _ rows_assocABC_data cols_innerABC_data).symm

theorem product2_eq : HexagonAtoms663.innerRightABC * HexagonAtoms663.assocABC = HexagonAtoms663.assocABC :=
  Matrix.one_mul (m := Fin 4 × Fin 2 × Fin 2) (n := Fin 2 × Fin 4 × Fin 2) _

theorem product3_eq : HexagonAtoms663.inverseACB * right0Middle6 6 3 = rowColumnMul rows_inverseACB cols_right0 :=
  (rowColumnMul_eq _ _ _ _ rows_inverseACB_data cols_right0_data).symm

theorem product4_eq : HexagonAtoms663.innerACB * right1Middle6 6 3 = right1Middle6 6 3 :=
  Matrix.one_mul (m := Fin 4 × Fin 2 × Fin 2) (n := Fin 2 × Fin 4 × Fin 2) _

theorem product5_eq : HexagonAtoms663.assocBCA * left0Middle6 6 3 = rowColumnMul rows_assocBCA cols_left0 :=
  (rowColumnMul_eq _ _ _ _ rows_assocBCA_data cols_left0_data).symm

theorem product6_eq : HexagonAtoms663.innerRightABC * left1Middle6 6 3 = left1Middle6 6 3 :=
  Matrix.one_mul (m := Fin 4 × Fin 2 × Fin 2) (n := Fin 2 × Fin 4 × Fin 2) _

theorem product7_eq : HexagonAtoms663.assocCAB * right2Middle6 6 3 = rowColumnMul rows_assocCAB cols_right2 :=
  (rowColumnMul_eq _ _ _ _ rows_assocCAB_data cols_right2_data).symm

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn663
