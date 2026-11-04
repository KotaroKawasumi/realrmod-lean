import RMod.BrundanEllis.StackingReferenceHexagonAtoms734
import RMod.BrundanEllis.StackingReferenceHexagonMiddle7
import RMod.BrundanEllis.StackingReferenceRowColumnCheck

/-! Verified row and column lists. Each subsequent scalar product traverses
these lists directly, without repeated lookup into the original matrices. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn734
open Superfusion

private def rows_outerABCData : List (List ℤ) := [decodeIntegerRow 16 3 1 21523354,
    decodeIntegerRow 16 3 1 21523388,
    decodeIntegerRow 16 3 1 21523386,
    decodeIntegerRow 16 3 1 21523372,
    decodeIntegerRow 16 3 1 21522874,
    decodeIntegerRow 16 3 1 21525628,
    decodeIntegerRow 16 3 1 21525466,
    decodeIntegerRow 16 3 1 21524332,
    decodeIntegerRow 16 3 1 21562726,
    decodeIntegerRow 16 3 1 21339652,
    decodeIntegerRow 16 3 1 21352774,
    decodeIntegerRow 16 3 1 21444628,
    decodeIntegerRow 16 3 1 24712006,
    decodeIntegerRow 16 3 1 6643012,
    decodeIntegerRow 16 3 1 7705894,
    decodeIntegerRow 16 3 1 15146068]

def rows_outerABC (r : LeftIndex 3 4 7) : List ℤ := rows_outerABCData.getD (leftPosition 3 4 7 r) []

private theorem rows_outerABC_eq_0_0_0 : (tripleIndices 4 1 4).map ((HexagonAtoms734.outerABC) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_outerABC ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_0_1 : (tripleIndices 4 1 4).map ((HexagonAtoms734.outerABC) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_outerABC ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_0_2 : (tripleIndices 4 1 4).map ((HexagonAtoms734.outerABC) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_outerABC ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_0_3 : (tripleIndices 4 1 4).map ((HexagonAtoms734.outerABC) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_outerABC ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_0 : (tripleIndices 4 1 4).map ((HexagonAtoms734.outerABC) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_outerABC ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_1 : (tripleIndices 4 1 4).map ((HexagonAtoms734.outerABC) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_outerABC ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_2 : (tripleIndices 4 1 4).map ((HexagonAtoms734.outerABC) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_outerABC ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_3 : (tripleIndices 4 1 4).map ((HexagonAtoms734.outerABC) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_outerABC ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_2_0_0 : (tripleIndices 4 1 4).map ((HexagonAtoms734.outerABC) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_outerABC ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_2_0_1 : (tripleIndices 4 1 4).map ((HexagonAtoms734.outerABC) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_outerABC ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_2_0_2 : (tripleIndices 4 1 4).map ((HexagonAtoms734.outerABC) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_outerABC ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_2_0_3 : (tripleIndices 4 1 4).map ((HexagonAtoms734.outerABC) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_outerABC ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_3_0_0 : (tripleIndices 4 1 4).map ((HexagonAtoms734.outerABC) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_outerABC ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_3_0_1 : (tripleIndices 4 1 4).map ((HexagonAtoms734.outerABC) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_outerABC ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_3_0_2 : (tripleIndices 4 1 4).map ((HexagonAtoms734.outerABC) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_outerABC ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_3_0_3 : (tripleIndices 4 1 4).map ((HexagonAtoms734.outerABC) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_outerABC ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_outerABC_data (r : LeftIndex 3 4 7) : (tripleIndices 4 1 4).map ((HexagonAtoms734.outerABC) r) = rows_outerABC r := by
  fin_cases r
  · exact rows_outerABC_eq_0_0_0
  · exact rows_outerABC_eq_0_0_1
  · exact rows_outerABC_eq_0_0_2
  · exact rows_outerABC_eq_0_0_3
  · exact rows_outerABC_eq_1_0_0
  · exact rows_outerABC_eq_1_0_1
  · exact rows_outerABC_eq_1_0_2
  · exact rows_outerABC_eq_1_0_3
  · exact rows_outerABC_eq_2_0_0
  · exact rows_outerABC_eq_2_0_1
  · exact rows_outerABC_eq_2_0_2
  · exact rows_outerABC_eq_2_0_3
  · exact rows_outerABC_eq_3_0_0
  · exact rows_outerABC_eq_3_0_1
  · exact rows_outerABC_eq_3_0_2
  · exact rows_outerABC_eq_3_0_3

private def rows_inverseACBData : List (List ℤ) := [decodeIntegerRow 16 3 1 23176786,
    decodeIntegerRow 16 3 1 21877906,
    decodeIntegerRow 16 3 1 35879554,
    decodeIntegerRow 16 3 1 26288834,
    decodeIntegerRow 16 3 1 19987978,
    decodeIntegerRow 16 3 1 20814538,
    decodeIntegerRow 16 3 1 7180282,
    decodeIntegerRow 16 3 1 16718522,
    decodeIntegerRow 16 3 1 21877402,
    decodeIntegerRow 16 3 1 23176678,
    decodeIntegerRow 16 3 1 26284458,
    decodeIntegerRow 16 3 1 35878102,
    decodeIntegerRow 16 3 1 20815006,
    decodeIntegerRow 16 3 1 19988194,
    decodeIntegerRow 16 3 1 16722894,
    decodeIntegerRow 16 3 1 7181746]

def rows_inverseACB (r : LeftIndex 7 4 3) : List ℤ := rows_inverseACBData.getD (leftPosition 7 4 3 r) []

private theorem rows_inverseACB_eq_0_0_0 : (tripleIndices 4 1 4).map ((HexagonAtoms734.inverseACB) ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4))) = rows_inverseACB ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_1 : (tripleIndices 4 1 4).map ((HexagonAtoms734.inverseACB) ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4))) = rows_inverseACB ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_2 : (tripleIndices 4 1 4).map ((HexagonAtoms734.inverseACB) ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4))) = rows_inverseACB ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_3 : (tripleIndices 4 1 4).map ((HexagonAtoms734.inverseACB) ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4))) = rows_inverseACB ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_0 : (tripleIndices 4 1 4).map ((HexagonAtoms734.inverseACB) ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4))) = rows_inverseACB ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_1 : (tripleIndices 4 1 4).map ((HexagonAtoms734.inverseACB) ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4))) = rows_inverseACB ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_2 : (tripleIndices 4 1 4).map ((HexagonAtoms734.inverseACB) ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4))) = rows_inverseACB ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_3 : (tripleIndices 4 1 4).map ((HexagonAtoms734.inverseACB) ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4))) = rows_inverseACB ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_2_0 : (tripleIndices 4 1 4).map ((HexagonAtoms734.inverseACB) ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4))) = rows_inverseACB ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_2_1 : (tripleIndices 4 1 4).map ((HexagonAtoms734.inverseACB) ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4))) = rows_inverseACB ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_2_2 : (tripleIndices 4 1 4).map ((HexagonAtoms734.inverseACB) ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4))) = rows_inverseACB ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_2_3 : (tripleIndices 4 1 4).map ((HexagonAtoms734.inverseACB) ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4))) = rows_inverseACB ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_3_0 : (tripleIndices 4 1 4).map ((HexagonAtoms734.inverseACB) ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4))) = rows_inverseACB ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_3_1 : (tripleIndices 4 1 4).map ((HexagonAtoms734.inverseACB) ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4))) = rows_inverseACB ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_3_2 : (tripleIndices 4 1 4).map ((HexagonAtoms734.inverseACB) ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4))) = rows_inverseACB ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_3_3 : (tripleIndices 4 1 4).map ((HexagonAtoms734.inverseACB) ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4))) = rows_inverseACB ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_inverseACB_data (r : LeftIndex 7 4 3) : (tripleIndices 4 1 4).map ((HexagonAtoms734.inverseACB) r) = rows_inverseACB r := by
  fin_cases r
  · exact rows_inverseACB_eq_0_0_0
  · exact rows_inverseACB_eq_0_0_1
  · exact rows_inverseACB_eq_0_0_2
  · exact rows_inverseACB_eq_0_0_3
  · exact rows_inverseACB_eq_0_1_0
  · exact rows_inverseACB_eq_0_1_1
  · exact rows_inverseACB_eq_0_1_2
  · exact rows_inverseACB_eq_0_1_3
  · exact rows_inverseACB_eq_0_2_0
  · exact rows_inverseACB_eq_0_2_1
  · exact rows_inverseACB_eq_0_2_2
  · exact rows_inverseACB_eq_0_2_3
  · exact rows_inverseACB_eq_0_3_0
  · exact rows_inverseACB_eq_0_3_1
  · exact rows_inverseACB_eq_0_3_2
  · exact rows_inverseACB_eq_0_3_3

private def rows_assocBCAData : List (List ℤ) := [decodeIntegerRow 16 3 1 16760182,
    decodeIntegerRow 16 3 1 35879062,
    decodeIntegerRow 16 3 1 21169798,
    decodeIntegerRow 16 3 1 23178918,
    decodeIntegerRow 16 3 1 26325958,
    decodeIntegerRow 16 3 1 7180762,
    decodeIntegerRow 16 3 1 22231222,
    decodeIntegerRow 16 3 1 19985898,
    decodeIntegerRow 16 3 1 35878594,
    decodeIntegerRow 16 3 1 16759966,
    decodeIntegerRow 16 3 1 23174546,
    decodeIntegerRow 16 3 1 21168334,
    decodeIntegerRow 16 3 1 7181266,
    decodeIntegerRow 16 3 1 26326066,
    decodeIntegerRow 16 3 1 19990274,
    decodeIntegerRow 16 3 1 22232674]

def rows_assocBCA (r : RightIndex 3 4 7) : List ℤ := rows_assocBCAData.getD (rightPosition 3 4 7 r) []

private theorem rows_assocBCA_eq_0_0_0 : (tripleIndices 4 1 4).map ((HexagonAtoms734.assocBCA) ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4))) = rows_assocBCA ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_1 : (tripleIndices 4 1 4).map ((HexagonAtoms734.assocBCA) ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4))) = rows_assocBCA ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_2 : (tripleIndices 4 1 4).map ((HexagonAtoms734.assocBCA) ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4))) = rows_assocBCA ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_3 : (tripleIndices 4 1 4).map ((HexagonAtoms734.assocBCA) ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4))) = rows_assocBCA ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_0 : (tripleIndices 4 1 4).map ((HexagonAtoms734.assocBCA) ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4))) = rows_assocBCA ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_1 : (tripleIndices 4 1 4).map ((HexagonAtoms734.assocBCA) ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4))) = rows_assocBCA ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_2 : (tripleIndices 4 1 4).map ((HexagonAtoms734.assocBCA) ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4))) = rows_assocBCA ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_3 : (tripleIndices 4 1 4).map ((HexagonAtoms734.assocBCA) ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4))) = rows_assocBCA ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_2_0 : (tripleIndices 4 1 4).map ((HexagonAtoms734.assocBCA) ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4))) = rows_assocBCA ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_2_1 : (tripleIndices 4 1 4).map ((HexagonAtoms734.assocBCA) ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4))) = rows_assocBCA ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_2_2 : (tripleIndices 4 1 4).map ((HexagonAtoms734.assocBCA) ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4))) = rows_assocBCA ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_2_3 : (tripleIndices 4 1 4).map ((HexagonAtoms734.assocBCA) ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4))) = rows_assocBCA ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_3_0 : (tripleIndices 4 1 4).map ((HexagonAtoms734.assocBCA) ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4))) = rows_assocBCA ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_3_1 : (tripleIndices 4 1 4).map ((HexagonAtoms734.assocBCA) ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4))) = rows_assocBCA ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_3_2 : (tripleIndices 4 1 4).map ((HexagonAtoms734.assocBCA) ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4))) = rows_assocBCA ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_3_3 : (tripleIndices 4 1 4).map ((HexagonAtoms734.assocBCA) ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4))) = rows_assocBCA ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocBCA_data (r : RightIndex 3 4 7) : (tripleIndices 4 1 4).map ((HexagonAtoms734.assocBCA) r) = rows_assocBCA r := by
  fin_cases r
  · exact rows_assocBCA_eq_0_0_0
  · exact rows_assocBCA_eq_0_0_1
  · exact rows_assocBCA_eq_0_0_2
  · exact rows_assocBCA_eq_0_0_3
  · exact rows_assocBCA_eq_0_1_0
  · exact rows_assocBCA_eq_0_1_1
  · exact rows_assocBCA_eq_0_1_2
  · exact rows_assocBCA_eq_0_1_3
  · exact rows_assocBCA_eq_0_2_0
  · exact rows_assocBCA_eq_0_2_1
  · exact rows_assocBCA_eq_0_2_2
  · exact rows_assocBCA_eq_0_2_3
  · exact rows_assocBCA_eq_0_3_0
  · exact rows_assocBCA_eq_0_3_1
  · exact rows_assocBCA_eq_0_3_2
  · exact rows_assocBCA_eq_0_3_3

private def rows_assocCABData : List (List ℤ) := [decodeIntegerRow 16 3 1 21525656,
    decodeIntegerRow 16 3 1 21522868,
    decodeIntegerRow 16 3 1 21524344,
    decodeIntegerRow 16 3 1 21525492,
    decodeIntegerRow 16 3 1 35170240,
    decodeIntegerRow 16 3 1 15224800,
    decodeIntegerRow 16 3 1 18374080,
    decodeIntegerRow 16 3 1 6826720,
    decodeIntegerRow 16 3 1 6459304,
    decodeIntegerRow 16 3 1 24751372,
    decodeIntegerRow 16 3 1 15067336,
    decodeIntegerRow 16 3 1 7535308,
    decodeIntegerRow 16 3 1 21525440,
    decodeIntegerRow 16 3 1 21522400,
    decodeIntegerRow 16 3 1 21522880,
    decodeIntegerRow 16 3 1 21521120]

def rows_assocCAB (r : RightIndex 4 7 3) : List ℤ := rows_assocCABData.getD (rightPosition 4 7 3 r) []

private theorem rows_assocCAB_eq_0_0_0 : (tripleIndices 1 4 4).map ((HexagonAtoms734.assocCAB) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_1 : (tripleIndices 1 4 4).map ((HexagonAtoms734.assocCAB) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_2 : (tripleIndices 1 4 4).map ((HexagonAtoms734.assocCAB) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_3 : (tripleIndices 1 4 4).map ((HexagonAtoms734.assocCAB) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_0 : (tripleIndices 1 4 4).map ((HexagonAtoms734.assocCAB) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = rows_assocCAB ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_1 : (tripleIndices 1 4 4).map ((HexagonAtoms734.assocCAB) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = rows_assocCAB ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_2 : (tripleIndices 1 4 4).map ((HexagonAtoms734.assocCAB) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = rows_assocCAB ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_3 : (tripleIndices 1 4 4).map ((HexagonAtoms734.assocCAB) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = rows_assocCAB ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_0 : (tripleIndices 1 4 4).map ((HexagonAtoms734.assocCAB) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_1 : (tripleIndices 1 4 4).map ((HexagonAtoms734.assocCAB) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_2 : (tripleIndices 1 4 4).map ((HexagonAtoms734.assocCAB) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_3 : (tripleIndices 1 4 4).map ((HexagonAtoms734.assocCAB) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_0 : (tripleIndices 1 4 4).map ((HexagonAtoms734.assocCAB) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = rows_assocCAB ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_1 : (tripleIndices 1 4 4).map ((HexagonAtoms734.assocCAB) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = rows_assocCAB ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_2 : (tripleIndices 1 4 4).map ((HexagonAtoms734.assocCAB) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = rows_assocCAB ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_3 : (tripleIndices 1 4 4).map ((HexagonAtoms734.assocCAB) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = rows_assocCAB ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocCAB_data (r : RightIndex 4 7 3) : (tripleIndices 1 4 4).map ((HexagonAtoms734.assocCAB) r) = rows_assocCAB r := by
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

private def cols_assocABCData : List (List ℤ) := [decodeIntegerRow 16 3 1 21562700,
    decodeIntegerRow 16 3 1 21339664,
    decodeIntegerRow 16 3 1 21352780,
    decodeIntegerRow 16 3 1 21444656,
    decodeIntegerRow 16 3 1 7706380,
    decodeIntegerRow 16 3 1 27898384,
    decodeIntegerRow 16 3 1 24709900,
    decodeIntegerRow 16 3 1 36402736,
    decodeIntegerRow 16 3 1 21693952,
    decodeIntegerRow 16 3 1 21444600,
    decodeIntegerRow 16 3 1 21483968,
    decodeIntegerRow 16 3 1 21339640,
    decodeIntegerRow 16 3 1 18332608,
    decodeIntegerRow 16 3 1 36404680,
    decodeIntegerRow 16 3 1 35341312,
    decodeIntegerRow 16 3 1 27902920]

def cols_assocABC (r : LeftIndex 7 3 4) : List ℤ := cols_assocABCData.getD (leftPosition 7 3 4 r) []

private theorem cols_assocABC_eq_0_0_0 : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms734.assocABC) j ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = cols_assocABC ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_1 : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms734.assocABC) j ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = cols_assocABC ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_2 : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms734.assocABC) j ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = cols_assocABC ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_3 : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms734.assocABC) j ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = cols_assocABC ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_0 : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms734.assocABC) j ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = cols_assocABC ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_1 : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms734.assocABC) j ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = cols_assocABC ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_2 : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms734.assocABC) j ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = cols_assocABC ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_3 : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms734.assocABC) j ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = cols_assocABC ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_0 : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms734.assocABC) j ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = cols_assocABC ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_1 : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms734.assocABC) j ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = cols_assocABC ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_2 : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms734.assocABC) j ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = cols_assocABC ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_3 : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms734.assocABC) j ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = cols_assocABC ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_1_0 : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms734.assocABC) j ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = cols_assocABC ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_1_1 : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms734.assocABC) j ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = cols_assocABC ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_1_2 : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms734.assocABC) j ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = cols_assocABC ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_1_3 : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms734.assocABC) j ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = cols_assocABC ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_assocABC_data (r : LeftIndex 7 3 4) : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms734.assocABC) j r) = cols_assocABC r := by
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

private def cols_right0Data : List (List ℤ) := [decodeIntegerRow 16 3 1 21562700,
    decodeIntegerRow 16 3 1 21339664,
    decodeIntegerRow 16 3 1 21352780,
    decodeIntegerRow 16 3 1 21444656,
    decodeIntegerRow 16 3 1 7706380,
    decodeIntegerRow 16 3 1 27898384,
    decodeIntegerRow 16 3 1 24709900,
    decodeIntegerRow 16 3 1 36402736,
    decodeIntegerRow 16 3 1 21693952,
    decodeIntegerRow 16 3 1 21444600,
    decodeIntegerRow 16 3 1 21483968,
    decodeIntegerRow 16 3 1 21339640,
    decodeIntegerRow 16 3 1 18332608,
    decodeIntegerRow 16 3 1 36404680,
    decodeIntegerRow 16 3 1 35341312,
    decodeIntegerRow 16 3 1 27902920]

def cols_right0 (r : LeftIndex 7 3 4) : List ℤ := cols_right0Data.getD (leftPosition 7 3 4 r) []

private theorem cols_right0_eq_0_0_0 : (tripleIndices 4 1 4).map (fun j => (right0Middle7 3 4) j ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = cols_right0 ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_1 : (tripleIndices 4 1 4).map (fun j => (right0Middle7 3 4) j ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = cols_right0 ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_2 : (tripleIndices 4 1 4).map (fun j => (right0Middle7 3 4) j ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = cols_right0 ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_3 : (tripleIndices 4 1 4).map (fun j => (right0Middle7 3 4) j ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = cols_right0 ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_0 : (tripleIndices 4 1 4).map (fun j => (right0Middle7 3 4) j ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = cols_right0 ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_1 : (tripleIndices 4 1 4).map (fun j => (right0Middle7 3 4) j ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = cols_right0 ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_2 : (tripleIndices 4 1 4).map (fun j => (right0Middle7 3 4) j ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = cols_right0 ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_3 : (tripleIndices 4 1 4).map (fun j => (right0Middle7 3 4) j ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = cols_right0 ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_0 : (tripleIndices 4 1 4).map (fun j => (right0Middle7 3 4) j ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = cols_right0 ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_1 : (tripleIndices 4 1 4).map (fun j => (right0Middle7 3 4) j ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = cols_right0 ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_2 : (tripleIndices 4 1 4).map (fun j => (right0Middle7 3 4) j ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = cols_right0 ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_3 : (tripleIndices 4 1 4).map (fun j => (right0Middle7 3 4) j ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = cols_right0 ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_0 : (tripleIndices 4 1 4).map (fun j => (right0Middle7 3 4) j ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = cols_right0 ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_1 : (tripleIndices 4 1 4).map (fun j => (right0Middle7 3 4) j ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = cols_right0 ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_2 : (tripleIndices 4 1 4).map (fun j => (right0Middle7 3 4) j ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = cols_right0 ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_3 : (tripleIndices 4 1 4).map (fun j => (right0Middle7 3 4) j ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = cols_right0 ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right0_data (r : LeftIndex 7 3 4) : (tripleIndices 4 1 4).map (fun j => (right0Middle7 3 4) j r) = cols_right0 r := by
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

private def cols_left0Data : List (List ℤ) := [decodeIntegerRow 16 5 2 76294726512,
    decodeIntegerRow 16 5 2 76297851812,
    decodeIntegerRow 16 5 2 76313476560,
    decodeIntegerRow 16 5 2 76391601572,
    decodeIntegerRow 16 5 2 88500975312,
    decodeIntegerRow 16 5 2 15258782812,
    decodeIntegerRow 16 5 2 76782195312,
    decodeIntegerRow 16 5 2 73852382812,
    decodeIntegerRow 16 5 2 76274414060,
    decodeIntegerRow 16 5 2 76391601552,
    decodeIntegerRow 16 5 2 76293164012,
    decodeIntegerRow 16 5 2 76297851312,
    decodeIntegerRow 16 5 2 75805632812,
    decodeIntegerRow 16 5 2 73852695312,
    decodeIntegerRow 16 5 2 64086912812,
    decodeIntegerRow 16 5 2 15258795312]

def cols_left0 (r : LeftIndex 7 3 4) : List ℤ := cols_left0Data.getD (leftPosition 7 3 4 r) []

private theorem cols_left0_eq_0_0_0 : (tripleIndices 4 1 4).map (fun j => (left0Middle7 3 4) j ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = cols_left0 ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_1 : (tripleIndices 4 1 4).map (fun j => (left0Middle7 3 4) j ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = cols_left0 ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_2 : (tripleIndices 4 1 4).map (fun j => (left0Middle7 3 4) j ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = cols_left0 ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_3 : (tripleIndices 4 1 4).map (fun j => (left0Middle7 3 4) j ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = cols_left0 ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_0 : (tripleIndices 4 1 4).map (fun j => (left0Middle7 3 4) j ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = cols_left0 ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_1 : (tripleIndices 4 1 4).map (fun j => (left0Middle7 3 4) j ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = cols_left0 ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_2 : (tripleIndices 4 1 4).map (fun j => (left0Middle7 3 4) j ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = cols_left0 ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_3 : (tripleIndices 4 1 4).map (fun j => (left0Middle7 3 4) j ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = cols_left0 ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_0 : (tripleIndices 4 1 4).map (fun j => (left0Middle7 3 4) j ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = cols_left0 ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_1 : (tripleIndices 4 1 4).map (fun j => (left0Middle7 3 4) j ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = cols_left0 ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_2 : (tripleIndices 4 1 4).map (fun j => (left0Middle7 3 4) j ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = cols_left0 ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_3 : (tripleIndices 4 1 4).map (fun j => (left0Middle7 3 4) j ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = cols_left0 ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_0 : (tripleIndices 4 1 4).map (fun j => (left0Middle7 3 4) j ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = cols_left0 ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_1 : (tripleIndices 4 1 4).map (fun j => (left0Middle7 3 4) j ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = cols_left0 ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_2 : (tripleIndices 4 1 4).map (fun j => (left0Middle7 3 4) j ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = cols_left0 ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_3 : (tripleIndices 4 1 4).map (fun j => (left0Middle7 3 4) j ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = cols_left0 ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_left0_data (r : LeftIndex 7 3 4) : (tripleIndices 4 1 4).map (fun j => (left0Middle7 3 4) j r) = cols_left0 r := by
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

private def cols_right2Data : List (List ℤ) := [decodeIntegerRow 16 5 2 76294103064,
    decodeIntegerRow 16 5 2 76293920272,
    decodeIntegerRow 16 5 2 76293982872,
    decodeIntegerRow 16 5 2 76294100560,
    decodeIntegerRow 16 5 2 136743945312,
    decodeIntegerRow 16 5 2 61668945312,
    decodeIntegerRow 16 5 2 66543945312,
    decodeIntegerRow 16 5 2 14868945312,
    decodeIntegerRow 16 5 2 14672070312,
    decodeIntegerRow 16 5 2 86075195312,
    decodeIntegerRow 16 5 2 61622070312,
    decodeIntegerRow 16 5 2 15650195312,
    decodeIntegerRow 16 5 2 76294100064,
    decodeIntegerRow 16 5 2 76293907872,
    decodeIntegerRow 16 5 2 76293920352,
    decodeIntegerRow 16 5 2 76293788064]

def cols_right2 (r : LeftIndex 7 3 4) : List ℤ := cols_right2Data.getD (leftPosition 7 3 4 r) []

private theorem cols_right2_eq_0_0_0 : (tripleIndices 1 4 4).map (fun j => (right2Middle7 3 4) j ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = cols_right2 ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_1 : (tripleIndices 1 4 4).map (fun j => (right2Middle7 3 4) j ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = cols_right2 ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_2 : (tripleIndices 1 4 4).map (fun j => (right2Middle7 3 4) j ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = cols_right2 ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_3 : (tripleIndices 1 4 4).map (fun j => (right2Middle7 3 4) j ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = cols_right2 ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_0 : (tripleIndices 1 4 4).map (fun j => (right2Middle7 3 4) j ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = cols_right2 ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_1 : (tripleIndices 1 4 4).map (fun j => (right2Middle7 3 4) j ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = cols_right2 ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_2 : (tripleIndices 1 4 4).map (fun j => (right2Middle7 3 4) j ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = cols_right2 ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_3 : (tripleIndices 1 4 4).map (fun j => (right2Middle7 3 4) j ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = cols_right2 ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_0 : (tripleIndices 1 4 4).map (fun j => (right2Middle7 3 4) j ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = cols_right2 ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_1 : (tripleIndices 1 4 4).map (fun j => (right2Middle7 3 4) j ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = cols_right2 ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_2 : (tripleIndices 1 4 4).map (fun j => (right2Middle7 3 4) j ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = cols_right2 ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_3 : (tripleIndices 1 4 4).map (fun j => (right2Middle7 3 4) j ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = cols_right2 ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_0 : (tripleIndices 1 4 4).map (fun j => (right2Middle7 3 4) j ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = cols_right2 ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_1 : (tripleIndices 1 4 4).map (fun j => (right2Middle7 3 4) j ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = cols_right2 ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_2 : (tripleIndices 1 4 4).map (fun j => (right2Middle7 3 4) j ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = cols_right2 ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_3 : (tripleIndices 1 4 4).map (fun j => (right2Middle7 3 4) j ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = cols_right2 ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right2_data (r : LeftIndex 7 3 4) : (tripleIndices 1 4 4).map (fun j => (right2Middle7 3 4) j r) = cols_right2 r := by
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

theorem product0_eq : HexagonAtoms734.outerABC * HexagonAtoms734.assocABC = rowColumnMul rows_outerABC cols_assocABC :=
  (rowColumnMul_eq _ _ _ _ rows_outerABC_data cols_assocABC_data).symm

theorem product1_eq : HexagonAtoms734.assocBAC * HexagonAtoms734.innerABC = HexagonAtoms734.assocBAC :=
  Matrix.mul_one (m := Fin 1 × Fin 4 × Fin 4) (n := Fin 2 × Fin 2 × Fin 4) _

theorem product2_eq : HexagonAtoms734.innerRightABC * HexagonAtoms734.assocABC = HexagonAtoms734.assocABC :=
  Matrix.one_mul (m := Fin 4 × Fin 1 × Fin 4) (n := Fin 2 × Fin 2 × Fin 4) _

theorem product3_eq : HexagonAtoms734.inverseACB * right0Middle7 3 4 = rowColumnMul rows_inverseACB cols_right0 :=
  (rowColumnMul_eq _ _ _ _ rows_inverseACB_data cols_right0_data).symm

theorem product4_eq : HexagonAtoms734.innerACB * right1Middle7 3 4 = right1Middle7 3 4 :=
  Matrix.one_mul (m := Fin 1 × Fin 4 × Fin 4) (n := Fin 2 × Fin 2 × Fin 4) _

theorem product5_eq : HexagonAtoms734.assocBCA * left0Middle7 3 4 = rowColumnMul rows_assocBCA cols_left0 :=
  (rowColumnMul_eq _ _ _ _ rows_assocBCA_data cols_left0_data).symm

theorem product6_eq : HexagonAtoms734.innerRightBAC * left1Middle7 3 4 = left1Middle7 3 4 :=
  Matrix.one_mul (m := Fin 1 × Fin 4 × Fin 4) (n := Fin 2 × Fin 2 × Fin 4) _

theorem product7_eq : HexagonAtoms734.assocCAB * right2Middle7 3 4 = rowColumnMul rows_assocCAB cols_right2 :=
  (rowColumnMul_eq _ _ _ _ rows_assocCAB_data cols_right2_data).symm

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn734
