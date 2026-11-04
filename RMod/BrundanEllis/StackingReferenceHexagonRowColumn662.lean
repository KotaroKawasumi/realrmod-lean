import RMod.BrundanEllis.StackingReferenceHexagonAtoms662
import RMod.BrundanEllis.StackingReferenceHexagonMiddle6
import RMod.BrundanEllis.StackingReferenceRowColumnCheck

/-! Verified row and column lists. Each subsequent scalar product traverses
these lists directly, without repeated lookup into the original matrices. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn662
open Superfusion

theorem assocBAC_alias : HexagonAtoms662.assocBAC = HexagonAtoms662.assocABC :=
  HexagonAtoms662.assocBAC_eq.symm.trans HexagonAtoms662.assocABC_eq

theorem innerRightBAC_alias : HexagonAtoms662.innerRightBAC = HexagonAtoms662.innerRightABC :=
  HexagonAtoms662.innerRightBAC_eq.symm.trans HexagonAtoms662.innerRightABC_eq

private def rows_assocABCData : List (List ℤ) := [decodeIntegerRow 16 3 1 21529924,
    decodeIntegerRow 16 3 1 21543044,
    decodeIntegerRow 16 3 1 21582436,
    decodeIntegerRow 16 3 1 21700516,
    decodeIntegerRow 16 3 1 21700498,
    decodeIntegerRow 16 3 1 21464338,
    decodeIntegerRow 16 3 1 21543042,
    decodeIntegerRow 16 3 1 21516802,
    decodeIntegerRow 16 3 1 7173724,
    decodeIntegerRow 16 3 1 26308516,
    decodeIntegerRow 16 3 1 19928956,
    decodeIntegerRow 16 3 1 22055044,
    decodeIntegerRow 16 3 1 22054558,
    decodeIntegerRow 16 3 1 23117602,
    decodeIntegerRow 16 3 1 26304142,
    decodeIntegerRow 16 3 1 35871538]

def rows_assocABC (r : RightIndex 6 6 2) : List ℤ := rows_assocABCData.getD (rightPosition 6 6 2 r) []

private theorem rows_assocABC_eq_0_0_0 : (tripleIndices 2 2 4).map ((HexagonAtoms662.assocABC) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_assocABC ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_0_1 : (tripleIndices 2 2 4).map ((HexagonAtoms662.assocABC) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_assocABC ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_0_2 : (tripleIndices 2 2 4).map ((HexagonAtoms662.assocABC) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_assocABC ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_0_3 : (tripleIndices 2 2 4).map ((HexagonAtoms662.assocABC) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_assocABC ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_0_0 : (tripleIndices 2 2 4).map ((HexagonAtoms662.assocABC) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_assocABC ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_0_1 : (tripleIndices 2 2 4).map ((HexagonAtoms662.assocABC) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_assocABC ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_0_2 : (tripleIndices 2 2 4).map ((HexagonAtoms662.assocABC) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_assocABC ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_0_3 : (tripleIndices 2 2 4).map ((HexagonAtoms662.assocABC) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_assocABC ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_2_0_0 : (tripleIndices 2 2 4).map ((HexagonAtoms662.assocABC) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_assocABC ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_2_0_1 : (tripleIndices 2 2 4).map ((HexagonAtoms662.assocABC) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_assocABC ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_2_0_2 : (tripleIndices 2 2 4).map ((HexagonAtoms662.assocABC) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_assocABC ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_2_0_3 : (tripleIndices 2 2 4).map ((HexagonAtoms662.assocABC) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_assocABC ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_3_0_0 : (tripleIndices 2 2 4).map ((HexagonAtoms662.assocABC) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_assocABC ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_3_0_1 : (tripleIndices 2 2 4).map ((HexagonAtoms662.assocABC) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_assocABC ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_3_0_2 : (tripleIndices 2 2 4).map ((HexagonAtoms662.assocABC) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_assocABC ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_3_0_3 : (tripleIndices 2 2 4).map ((HexagonAtoms662.assocABC) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_assocABC ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocABC_data (r : RightIndex 6 6 2) : (tripleIndices 2 2 4).map ((HexagonAtoms662.assocABC) r) = rows_assocABC r := by
  fin_cases r
  · exact rows_assocABC_eq_0_0_0
  · exact rows_assocABC_eq_0_0_1
  · exact rows_assocABC_eq_0_0_2
  · exact rows_assocABC_eq_0_0_3
  · exact rows_assocABC_eq_1_0_0
  · exact rows_assocABC_eq_1_0_1
  · exact rows_assocABC_eq_1_0_2
  · exact rows_assocABC_eq_1_0_3
  · exact rows_assocABC_eq_2_0_0
  · exact rows_assocABC_eq_2_0_1
  · exact rows_assocABC_eq_2_0_2
  · exact rows_assocABC_eq_2_0_3
  · exact rows_assocABC_eq_3_0_0
  · exact rows_assocABC_eq_3_0_1
  · exact rows_assocABC_eq_3_0_2
  · exact rows_assocABC_eq_3_0_3

private def rows_inverseACBData : List (List ℤ) := [decodeIntegerRow 16 3 1 19988140,
    decodeIntegerRow 16 3 1 20815024,
    decodeIntegerRow 16 3 1 7181740,
    decodeIntegerRow 16 3 1 16722896,
    decodeIntegerRow 16 3 1 16718520,
    decodeIntegerRow 16 3 1 35866432,
    decodeIntegerRow 16 3 1 20814520,
    decodeIntegerRow 16 3 1 23058688,
    decodeIntegerRow 16 3 1 21877888,
    decodeIntegerRow 16 3 1 23176840,
    decodeIntegerRow 16 3 1 26288832,
    decodeIntegerRow 16 3 1 35879560,
    decodeIntegerRow 16 3 1 7168624,
    decodeIntegerRow 16 3 1 26284460,
    decodeIntegerRow 16 3 1 19870096,
    decodeIntegerRow 16 3 1 21877420]

def rows_inverseACB (r : LeftIndex 6 2 6) : List ℤ := rows_inverseACBData.getD (leftPosition 6 2 6 r) []

private theorem rows_inverseACB_eq_0_0_0 : (tripleIndices 4 1 4).map ((HexagonAtoms662.inverseACB) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_1 : (tripleIndices 4 1 4).map ((HexagonAtoms662.inverseACB) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_2 : (tripleIndices 4 1 4).map ((HexagonAtoms662.inverseACB) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_3 : (tripleIndices 4 1 4).map ((HexagonAtoms662.inverseACB) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_0 : (tripleIndices 4 1 4).map ((HexagonAtoms662.inverseACB) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_1 : (tripleIndices 4 1 4).map ((HexagonAtoms662.inverseACB) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_2 : (tripleIndices 4 1 4).map ((HexagonAtoms662.inverseACB) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_3 : (tripleIndices 4 1 4).map ((HexagonAtoms662.inverseACB) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_0 : (tripleIndices 4 1 4).map ((HexagonAtoms662.inverseACB) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_1 : (tripleIndices 4 1 4).map ((HexagonAtoms662.inverseACB) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_2 : (tripleIndices 4 1 4).map ((HexagonAtoms662.inverseACB) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_3 : (tripleIndices 4 1 4).map ((HexagonAtoms662.inverseACB) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_0 : (tripleIndices 4 1 4).map ((HexagonAtoms662.inverseACB) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_1 : (tripleIndices 4 1 4).map ((HexagonAtoms662.inverseACB) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_2 : (tripleIndices 4 1 4).map ((HexagonAtoms662.inverseACB) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_3 : (tripleIndices 4 1 4).map ((HexagonAtoms662.inverseACB) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_inverseACB_data (r : LeftIndex 6 2 6) : (tripleIndices 4 1 4).map ((HexagonAtoms662.inverseACB) r) = rows_inverseACB r := by
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

private def rows_assocBCAData : List (List ℤ) := [decodeIntegerRow 16 3 1 23058580,
    decodeIntegerRow 16 3 1 22231696,
    decodeIntegerRow 16 3 1 35864980,
    decodeIntegerRow 16 3 1 26323824,
    decodeIntegerRow 16 3 1 26328200,
    decodeIntegerRow 16 3 1 7180288,
    decodeIntegerRow 16 3 1 22232200,
    decodeIntegerRow 16 3 1 19988032,
    decodeIntegerRow 16 3 1 21168832,
    decodeIntegerRow 16 3 1 19869880,
    decodeIntegerRow 16 3 1 16757888,
    decodeIntegerRow 16 3 1 7167160,
    decodeIntegerRow 16 3 1 35878096,
    decodeIntegerRow 16 3 1 16762260,
    decodeIntegerRow 16 3 1 23176624,
    decodeIntegerRow 16 3 1 21169300]

def rows_assocBCA (r : RightIndex 6 2 6) : List ℤ := rows_assocBCAData.getD (rightPosition 6 2 6 r) []

private theorem rows_assocBCA_eq_0_0_0 : (tripleIndices 4 1 4).map ((HexagonAtoms662.assocBCA) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_assocBCA ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_1 : (tripleIndices 4 1 4).map ((HexagonAtoms662.assocBCA) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_assocBCA ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_2 : (tripleIndices 4 1 4).map ((HexagonAtoms662.assocBCA) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_assocBCA ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_3 : (tripleIndices 4 1 4).map ((HexagonAtoms662.assocBCA) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_assocBCA ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_0 : (tripleIndices 4 1 4).map ((HexagonAtoms662.assocBCA) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_assocBCA ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_1 : (tripleIndices 4 1 4).map ((HexagonAtoms662.assocBCA) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_assocBCA ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_2 : (tripleIndices 4 1 4).map ((HexagonAtoms662.assocBCA) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_assocBCA ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_3 : (tripleIndices 4 1 4).map ((HexagonAtoms662.assocBCA) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_assocBCA ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_0 : (tripleIndices 4 1 4).map ((HexagonAtoms662.assocBCA) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_assocBCA ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_1 : (tripleIndices 4 1 4).map ((HexagonAtoms662.assocBCA) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_assocBCA ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_2 : (tripleIndices 4 1 4).map ((HexagonAtoms662.assocBCA) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_assocBCA ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_3 : (tripleIndices 4 1 4).map ((HexagonAtoms662.assocBCA) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_assocBCA ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_0 : (tripleIndices 4 1 4).map ((HexagonAtoms662.assocBCA) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_assocBCA ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_1 : (tripleIndices 4 1 4).map ((HexagonAtoms662.assocBCA) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_assocBCA ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_2 : (tripleIndices 4 1 4).map ((HexagonAtoms662.assocBCA) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_assocBCA ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_3 : (tripleIndices 4 1 4).map ((HexagonAtoms662.assocBCA) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_assocBCA ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocBCA_data (r : RightIndex 6 2 6) : (tripleIndices 4 1 4).map ((HexagonAtoms662.assocBCA) r) = rows_assocBCA r := by
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

private def rows_assocCABData : List (List ℤ) := [decodeIntegerRow 16 3 1 21523612,
    decodeIntegerRow 16 3 1 21523414,
    decodeIntegerRow 16 3 1 21525548,
    decodeIntegerRow 16 3 1 21524086,
    decodeIntegerRow 16 3 1 16760074,
    decodeIntegerRow 16 3 1 35878828,
    decodeIntegerRow 16 3 1 21169066,
    decodeIntegerRow 16 3 1 23176732,
    decodeIntegerRow 16 3 1 19988086,
    decodeIntegerRow 16 3 1 20814772,
    decodeIntegerRow 16 3 1 7181014,
    decodeIntegerRow 16 3 1 16720708,
    decodeIntegerRow 16 3 1 21524092,
    decodeIntegerRow 16 3 1 21521174,
    decodeIntegerRow 16 3 1 21523468,
    decodeIntegerRow 16 3 1 21523126]

def rows_assocCAB (r : RightIndex 2 6 6) : List ℤ := rows_assocCABData.getD (rightPosition 2 6 6 r) []

private theorem rows_assocCAB_eq_0_0_0 : (tripleIndices 4 1 4).map ((HexagonAtoms662.assocCAB) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_1 : (tripleIndices 4 1 4).map ((HexagonAtoms662.assocCAB) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_2 : (tripleIndices 4 1 4).map ((HexagonAtoms662.assocCAB) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_3 : (tripleIndices 4 1 4).map ((HexagonAtoms662.assocCAB) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_0 : (tripleIndices 4 1 4).map ((HexagonAtoms662.assocCAB) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = rows_assocCAB ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_1 : (tripleIndices 4 1 4).map ((HexagonAtoms662.assocCAB) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = rows_assocCAB ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_2 : (tripleIndices 4 1 4).map ((HexagonAtoms662.assocCAB) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = rows_assocCAB ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_3 : (tripleIndices 4 1 4).map ((HexagonAtoms662.assocCAB) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = rows_assocCAB ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_0 : (tripleIndices 4 1 4).map ((HexagonAtoms662.assocCAB) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_1 : (tripleIndices 4 1 4).map ((HexagonAtoms662.assocCAB) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_2 : (tripleIndices 4 1 4).map ((HexagonAtoms662.assocCAB) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_3 : (tripleIndices 4 1 4).map ((HexagonAtoms662.assocCAB) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_0 : (tripleIndices 4 1 4).map ((HexagonAtoms662.assocCAB) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = rows_assocCAB ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_1 : (tripleIndices 4 1 4).map ((HexagonAtoms662.assocCAB) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = rows_assocCAB ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_2 : (tripleIndices 4 1 4).map ((HexagonAtoms662.assocCAB) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = rows_assocCAB ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_3 : (tripleIndices 4 1 4).map ((HexagonAtoms662.assocCAB) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = rows_assocCAB ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocCAB_data (r : RightIndex 2 6 6) : (tripleIndices 4 1 4).map ((HexagonAtoms662.assocCAB) r) = rows_assocCAB r := by
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

private def cols_innerABCData : List (List ℤ) := [decodeIntegerRow 16 3 1 21523333,
    decodeIntegerRow 16 3 1 21523369,
    decodeIntegerRow 16 3 1 21523357,
    decodeIntegerRow 16 3 1 21523361,
    decodeIntegerRow 16 3 1 21521173,
    decodeIntegerRow 16 3 1 21524089,
    decodeIntegerRow 16 3 1 21523117,
    decodeIntegerRow 16 3 1 21523441,
    decodeIntegerRow 16 3 1 23117683,
    decodeIntegerRow 16 3 1 22054801,
    decodeIntegerRow 16 3 1 35872267,
    decodeIntegerRow 16 3 1 26306329,
    decodeIntegerRow 16 3 1 21503677,
    decodeIntegerRow 16 3 1 21516799,
    decodeIntegerRow 16 3 1 21346213,
    decodeIntegerRow 16 3 1 21464311]

def cols_innerABC (r : LeftIndex 6 6 2) : List ℤ := cols_innerABCData.getD (leftPosition 6 6 2 r) []

private theorem cols_innerABC_eq_0_0_0 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms662.innerABC) j ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = cols_innerABC ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_0_1 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms662.innerABC) j ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = cols_innerABC ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_0_2 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms662.innerABC) j ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = cols_innerABC ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_0_3 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms662.innerABC) j ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = cols_innerABC ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_1_0 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms662.innerABC) j ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = cols_innerABC ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_1_1 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms662.innerABC) j ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = cols_innerABC ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_1_2 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms662.innerABC) j ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = cols_innerABC ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_1_3 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms662.innerABC) j ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = cols_innerABC ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_0_0 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms662.innerABC) j ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = cols_innerABC ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_0_1 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms662.innerABC) j ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = cols_innerABC ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_0_2 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms662.innerABC) j ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = cols_innerABC ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_0_3 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms662.innerABC) j ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = cols_innerABC ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_1_0 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms662.innerABC) j ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = cols_innerABC ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_1_1 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms662.innerABC) j ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = cols_innerABC ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_1_2 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms662.innerABC) j ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = cols_innerABC ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_1_3 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms662.innerABC) j ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = cols_innerABC ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_innerABC_data (r : LeftIndex 6 6 2) : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms662.innerABC) j r) = cols_innerABC r := by
  fin_cases r
  · exact cols_innerABC_eq_0_0_0
  · exact cols_innerABC_eq_0_0_1
  · exact cols_innerABC_eq_0_0_2
  · exact cols_innerABC_eq_0_0_3
  · exact cols_innerABC_eq_0_1_0
  · exact cols_innerABC_eq_0_1_1
  · exact cols_innerABC_eq_0_1_2
  · exact cols_innerABC_eq_0_1_3
  · exact cols_innerABC_eq_1_0_0
  · exact cols_innerABC_eq_1_0_1
  · exact cols_innerABC_eq_1_0_2
  · exact cols_innerABC_eq_1_0_3
  · exact cols_innerABC_eq_1_1_0
  · exact cols_innerABC_eq_1_1_1
  · exact cols_innerABC_eq_1_1_2
  · exact cols_innerABC_eq_1_1_3

private def cols_right0Data : List (List ℤ) := [decodeIntegerRow 16 3 1 21522634,
    decodeIntegerRow 16 3 1 21525548,
    decodeIntegerRow 16 3 1 21523306,
    decodeIntegerRow 16 3 1 21523612,
    decodeIntegerRow 16 3 1 19869988,
    decodeIntegerRow 16 3 1 21169066,
    decodeIntegerRow 16 3 1 7167892,
    decodeIntegerRow 16 3 1 16760074,
    decodeIntegerRow 16 3 1 21521174,
    decodeIntegerRow 16 3 1 21524092,
    decodeIntegerRow 16 3 1 21523126,
    decodeIntegerRow 16 3 1 21523468,
    decodeIntegerRow 16 3 1 22231948,
    decodeIntegerRow 16 3 1 23058634,
    decodeIntegerRow 16 3 1 26326012,
    decodeIntegerRow 16 3 1 35865706]

def cols_right0 (r : LeftIndex 6 6 2) : List ℤ := cols_right0Data.getD (leftPosition 6 6 2 r) []

private theorem cols_right0_eq_0_0_0 : (tripleIndices 4 1 4).map (fun j => (right0Middle6 6 2) j ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = cols_right0 ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_1 : (tripleIndices 4 1 4).map (fun j => (right0Middle6 6 2) j ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = cols_right0 ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_2 : (tripleIndices 4 1 4).map (fun j => (right0Middle6 6 2) j ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = cols_right0 ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_3 : (tripleIndices 4 1 4).map (fun j => (right0Middle6 6 2) j ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = cols_right0 ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_0 : (tripleIndices 4 1 4).map (fun j => (right0Middle6 6 2) j ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = cols_right0 ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_1 : (tripleIndices 4 1 4).map (fun j => (right0Middle6 6 2) j ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = cols_right0 ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_2 : (tripleIndices 4 1 4).map (fun j => (right0Middle6 6 2) j ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = cols_right0 ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_3 : (tripleIndices 4 1 4).map (fun j => (right0Middle6 6 2) j ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = cols_right0 ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_0 : (tripleIndices 4 1 4).map (fun j => (right0Middle6 6 2) j ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = cols_right0 ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_1 : (tripleIndices 4 1 4).map (fun j => (right0Middle6 6 2) j ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = cols_right0 ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_2 : (tripleIndices 4 1 4).map (fun j => (right0Middle6 6 2) j ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = cols_right0 ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_3 : (tripleIndices 4 1 4).map (fun j => (right0Middle6 6 2) j ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = cols_right0 ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_0 : (tripleIndices 4 1 4).map (fun j => (right0Middle6 6 2) j ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = cols_right0 ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_1 : (tripleIndices 4 1 4).map (fun j => (right0Middle6 6 2) j ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = cols_right0 ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_2 : (tripleIndices 4 1 4).map (fun j => (right0Middle6 6 2) j ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = cols_right0 ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_3 : (tripleIndices 4 1 4).map (fun j => (right0Middle6 6 2) j ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = cols_right0 ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right0_data (r : LeftIndex 6 6 2) : (tripleIndices 4 1 4).map (fun j => (right0Middle6 6 2) j r) = cols_right0 r := by
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

private def cols_left0Data : List (List ℤ) := [decodeIntegerRow 16 3 1 21522634,
    decodeIntegerRow 16 3 1 21525548,
    decodeIntegerRow 16 3 1 21523306,
    decodeIntegerRow 16 3 1 21523612,
    decodeIntegerRow 16 3 1 19869988,
    decodeIntegerRow 16 3 1 21169066,
    decodeIntegerRow 16 3 1 7167892,
    decodeIntegerRow 16 3 1 16760074,
    decodeIntegerRow 16 3 1 21521174,
    decodeIntegerRow 16 3 1 21524092,
    decodeIntegerRow 16 3 1 21523126,
    decodeIntegerRow 16 3 1 21523468,
    decodeIntegerRow 16 3 1 22231948,
    decodeIntegerRow 16 3 1 23058634,
    decodeIntegerRow 16 3 1 26326012,
    decodeIntegerRow 16 3 1 35865706]

def cols_left0 (r : LeftIndex 6 6 2) : List ℤ := cols_left0Data.getD (leftPosition 6 6 2 r) []

private theorem cols_left0_eq_0_0_0 : (tripleIndices 4 1 4).map (fun j => (left0Middle6 6 2) j ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = cols_left0 ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_1 : (tripleIndices 4 1 4).map (fun j => (left0Middle6 6 2) j ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = cols_left0 ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_2 : (tripleIndices 4 1 4).map (fun j => (left0Middle6 6 2) j ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = cols_left0 ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_3 : (tripleIndices 4 1 4).map (fun j => (left0Middle6 6 2) j ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = cols_left0 ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_0 : (tripleIndices 4 1 4).map (fun j => (left0Middle6 6 2) j ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = cols_left0 ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_1 : (tripleIndices 4 1 4).map (fun j => (left0Middle6 6 2) j ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = cols_left0 ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_2 : (tripleIndices 4 1 4).map (fun j => (left0Middle6 6 2) j ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = cols_left0 ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_3 : (tripleIndices 4 1 4).map (fun j => (left0Middle6 6 2) j ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = cols_left0 ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_0 : (tripleIndices 4 1 4).map (fun j => (left0Middle6 6 2) j ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = cols_left0 ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_1 : (tripleIndices 4 1 4).map (fun j => (left0Middle6 6 2) j ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = cols_left0 ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_2 : (tripleIndices 4 1 4).map (fun j => (left0Middle6 6 2) j ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = cols_left0 ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_3 : (tripleIndices 4 1 4).map (fun j => (left0Middle6 6 2) j ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = cols_left0 ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_0 : (tripleIndices 4 1 4).map (fun j => (left0Middle6 6 2) j ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = cols_left0 ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_1 : (tripleIndices 4 1 4).map (fun j => (left0Middle6 6 2) j ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = cols_left0 ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_2 : (tripleIndices 4 1 4).map (fun j => (left0Middle6 6 2) j ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = cols_left0 ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_3 : (tripleIndices 4 1 4).map (fun j => (left0Middle6 6 2) j ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = cols_left0 ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_left0_data (r : LeftIndex 6 6 2) : (tripleIndices 4 1 4).map (fun j => (left0Middle6 6 2) j r) = cols_left0 r := by
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

private def cols_right2Data : List (List ℤ) := [decodeIntegerRow 16 5 2 76293939012,
    decodeIntegerRow 16 5 2 76293944312,
    decodeIntegerRow 16 5 2 76293789060,
    decodeIntegerRow 16 5 2 76293914072,
    decodeIntegerRow 16 5 2 88497070312,
    decodeIntegerRow 16 5 2 15258007812,
    decodeIntegerRow 16 5 2 76684570312,
    decodeIntegerRow 16 5 2 73833007812,
    decodeIntegerRow 16 5 2 78715820312,
    decodeIntegerRow 16 5 2 76879882812,
    decodeIntegerRow 16 5 2 137328320312,
    decodeIntegerRow 16 5 2 88504882812,
    decodeIntegerRow 16 5 2 76293914052,
    decodeIntegerRow 16 5 2 76294101560,
    decodeIntegerRow 16 5 2 76293943812,
    decodeIntegerRow 16 5 2 76293951512]

def cols_right2 (r : LeftIndex 6 6 2) : List ℤ := cols_right2Data.getD (leftPosition 6 6 2 r) []

private theorem cols_right2_eq_0_0_0 : (tripleIndices 4 1 4).map (fun j => (right2Middle6 6 2) j ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = cols_right2 ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_1 : (tripleIndices 4 1 4).map (fun j => (right2Middle6 6 2) j ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = cols_right2 ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_2 : (tripleIndices 4 1 4).map (fun j => (right2Middle6 6 2) j ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = cols_right2 ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_3 : (tripleIndices 4 1 4).map (fun j => (right2Middle6 6 2) j ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = cols_right2 ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_0 : (tripleIndices 4 1 4).map (fun j => (right2Middle6 6 2) j ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = cols_right2 ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_1 : (tripleIndices 4 1 4).map (fun j => (right2Middle6 6 2) j ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = cols_right2 ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_2 : (tripleIndices 4 1 4).map (fun j => (right2Middle6 6 2) j ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = cols_right2 ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_3 : (tripleIndices 4 1 4).map (fun j => (right2Middle6 6 2) j ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = cols_right2 ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_0 : (tripleIndices 4 1 4).map (fun j => (right2Middle6 6 2) j ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = cols_right2 ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_1 : (tripleIndices 4 1 4).map (fun j => (right2Middle6 6 2) j ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = cols_right2 ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_2 : (tripleIndices 4 1 4).map (fun j => (right2Middle6 6 2) j ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = cols_right2 ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_3 : (tripleIndices 4 1 4).map (fun j => (right2Middle6 6 2) j ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = cols_right2 ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_0 : (tripleIndices 4 1 4).map (fun j => (right2Middle6 6 2) j ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = cols_right2 ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_1 : (tripleIndices 4 1 4).map (fun j => (right2Middle6 6 2) j ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = cols_right2 ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_2 : (tripleIndices 4 1 4).map (fun j => (right2Middle6 6 2) j ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = cols_right2 ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_3 : (tripleIndices 4 1 4).map (fun j => (right2Middle6 6 2) j ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = cols_right2 ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right2_data (r : LeftIndex 6 6 2) : (tripleIndices 4 1 4).map (fun j => (right2Middle6 6 2) j r) = cols_right2 r := by
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

theorem product0_eq : HexagonAtoms662.outerABC * HexagonAtoms662.assocABC = HexagonAtoms662.assocABC :=
  Matrix.one_mul (m := Fin 4 × Fin 1 × Fin 4) (n := Fin 2 × Fin 2 × Fin 4) _

theorem product1_eq : HexagonAtoms662.assocABC * HexagonAtoms662.innerABC = rowColumnMul rows_assocABC cols_innerABC :=
  (rowColumnMul_eq _ _ _ _ rows_assocABC_data cols_innerABC_data).symm

theorem product2_eq : HexagonAtoms662.innerRightABC * HexagonAtoms662.assocABC = HexagonAtoms662.assocABC :=
  Matrix.one_mul (m := Fin 4 × Fin 1 × Fin 4) (n := Fin 2 × Fin 2 × Fin 4) _

theorem product3_eq : HexagonAtoms662.inverseACB * right0Middle6 6 2 = rowColumnMul rows_inverseACB cols_right0 :=
  (rowColumnMul_eq _ _ _ _ rows_inverseACB_data cols_right0_data).symm

theorem product4_eq : HexagonAtoms662.innerACB * right1Middle6 6 2 = right1Middle6 6 2 :=
  Matrix.one_mul (m := Fin 4 × Fin 1 × Fin 4) (n := Fin 2 × Fin 2 × Fin 4) _

theorem product5_eq : HexagonAtoms662.assocBCA * left0Middle6 6 2 = rowColumnMul rows_assocBCA cols_left0 :=
  (rowColumnMul_eq _ _ _ _ rows_assocBCA_data cols_left0_data).symm

theorem product6_eq : HexagonAtoms662.innerRightABC * left1Middle6 6 2 = left1Middle6 6 2 :=
  Matrix.one_mul (m := Fin 4 × Fin 1 × Fin 4) (n := Fin 2 × Fin 2 × Fin 4) _

theorem product7_eq : HexagonAtoms662.assocCAB * right2Middle6 6 2 = rowColumnMul rows_assocCAB cols_right2 :=
  (rowColumnMul_eq _ _ _ _ rows_assocCAB_data cols_right2_data).symm

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn662
