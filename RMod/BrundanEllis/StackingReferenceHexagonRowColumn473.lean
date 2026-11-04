import RMod.BrundanEllis.StackingReferenceHexagonAtoms473
import RMod.BrundanEllis.StackingReferenceHexagonMiddle4
import RMod.BrundanEllis.StackingReferenceRowColumnCheck

/-! Verified row and column lists. Each subsequent scalar product traverses
these lists directly, without repeated lookup into the original matrices. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn473
open Superfusion

private def rows_inverseACBData : List (List ℤ) := [decodeIntegerRow 16 3 1 21529930,
    decodeIntegerRow 16 3 1 21543016,
    decodeIntegerRow 16 3 1 21582410,
    decodeIntegerRow 16 3 1 21700504,
    decodeIntegerRow 16 3 1 26306410,
    decodeIntegerRow 16 3 1 7174696,
    decodeIntegerRow 16 3 1 22055530,
    decodeIntegerRow 16 3 1 19931224,
    decodeIntegerRow 16 3 1 21582408,
    decodeIntegerRow 16 3 1 21346210,
    decodeIntegerRow 16 3 1 21529912,
    decodeIntegerRow 16 3 1 21503650,
    decodeIntegerRow 16 3 1 22054072,
    decodeIntegerRow 16 3 1 23119870,
    decodeIntegerRow 16 3 1 26306248,
    decodeIntegerRow 16 3 1 35872510]

def rows_inverseACB (r : LeftIndex 4 3 7) : List ℤ := rows_inverseACBData.getD (leftPosition 4 3 7 r) []

private theorem rows_inverseACB_eq_0_0_0 : (tripleIndices 2 2 4).map ((HexagonAtoms473.inverseACB) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_1 : (tripleIndices 2 2 4).map ((HexagonAtoms473.inverseACB) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_2 : (tripleIndices 2 2 4).map ((HexagonAtoms473.inverseACB) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_3 : (tripleIndices 2 2 4).map ((HexagonAtoms473.inverseACB) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_0 : (tripleIndices 2 2 4).map ((HexagonAtoms473.inverseACB) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_1 : (tripleIndices 2 2 4).map ((HexagonAtoms473.inverseACB) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_2 : (tripleIndices 2 2 4).map ((HexagonAtoms473.inverseACB) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_3 : (tripleIndices 2 2 4).map ((HexagonAtoms473.inverseACB) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_0 : (tripleIndices 2 2 4).map ((HexagonAtoms473.inverseACB) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_1 : (tripleIndices 2 2 4).map ((HexagonAtoms473.inverseACB) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_2 : (tripleIndices 2 2 4).map ((HexagonAtoms473.inverseACB) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_3 : (tripleIndices 2 2 4).map ((HexagonAtoms473.inverseACB) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_0 : (tripleIndices 2 2 4).map ((HexagonAtoms473.inverseACB) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_1 : (tripleIndices 2 2 4).map ((HexagonAtoms473.inverseACB) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_2 : (tripleIndices 2 2 4).map ((HexagonAtoms473.inverseACB) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_3 : (tripleIndices 2 2 4).map ((HexagonAtoms473.inverseACB) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_inverseACB_data (r : LeftIndex 4 3 7) : (tripleIndices 2 2 4).map ((HexagonAtoms473.inverseACB) r) = rows_inverseACB r := by
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

private def rows_assocBCAData : List (List ℤ) := [decodeIntegerRow 16 3 1 21562754,
    decodeIntegerRow 16 3 1 21339646,
    decodeIntegerRow 16 3 1 21352786,
    decodeIntegerRow 16 3 1 21444654,
    decodeIntegerRow 16 3 1 36404194,
    decodeIntegerRow 16 3 1 18332446,
    decodeIntegerRow 16 3 1 27898546,
    decodeIntegerRow 16 3 1 35339854,
    decodeIntegerRow 16 3 1 21339658,
    decodeIntegerRow 16 3 1 21562698,
    decodeIntegerRow 16 3 1 21444602,
    decodeIntegerRow 16 3 1 21352762,
    decodeIntegerRow 16 3 1 18336982,
    decodeIntegerRow 16 3 1 36403222,
    decodeIntegerRow 16 3 1 35341798,
    decodeIntegerRow 16 3 1 27902758]

def rows_assocBCA (r : RightIndex 7 3 4) : List ℤ := rows_assocBCAData.getD (rightPosition 7 3 4 r) []

private theorem rows_assocBCA_eq_0_0_0 : (tripleIndices 2 2 4).map ((HexagonAtoms473.assocBCA) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_assocBCA ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_1 : (tripleIndices 2 2 4).map ((HexagonAtoms473.assocBCA) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_assocBCA ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_2 : (tripleIndices 2 2 4).map ((HexagonAtoms473.assocBCA) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_assocBCA ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_3 : (tripleIndices 2 2 4).map ((HexagonAtoms473.assocBCA) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_assocBCA ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_0 : (tripleIndices 2 2 4).map ((HexagonAtoms473.assocBCA) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_assocBCA ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_1 : (tripleIndices 2 2 4).map ((HexagonAtoms473.assocBCA) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_assocBCA ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_2 : (tripleIndices 2 2 4).map ((HexagonAtoms473.assocBCA) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_assocBCA ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_3 : (tripleIndices 2 2 4).map ((HexagonAtoms473.assocBCA) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_assocBCA ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_0 : (tripleIndices 2 2 4).map ((HexagonAtoms473.assocBCA) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_assocBCA ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_1 : (tripleIndices 2 2 4).map ((HexagonAtoms473.assocBCA) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_assocBCA ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_2 : (tripleIndices 2 2 4).map ((HexagonAtoms473.assocBCA) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_assocBCA ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_3 : (tripleIndices 2 2 4).map ((HexagonAtoms473.assocBCA) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_assocBCA ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_0 : (tripleIndices 2 2 4).map ((HexagonAtoms473.assocBCA) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_assocBCA ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_1 : (tripleIndices 2 2 4).map ((HexagonAtoms473.assocBCA) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_assocBCA ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_2 : (tripleIndices 2 2 4).map ((HexagonAtoms473.assocBCA) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_assocBCA ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_3 : (tripleIndices 2 2 4).map ((HexagonAtoms473.assocBCA) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_assocBCA ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocBCA_data (r : RightIndex 7 3 4) : (tripleIndices 2 2 4).map ((HexagonAtoms473.assocBCA) r) = rows_assocBCA r := by
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

private def rows_assocCABData : List (List ℤ) := [decodeIntegerRow 16 3 1 16760182,
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

def rows_assocCAB (r : RightIndex 3 4 7) : List ℤ := rows_assocCABData.getD (rightPosition 3 4 7 r) []

private theorem rows_assocCAB_eq_0_0_0 : (tripleIndices 4 1 4).map ((HexagonAtoms473.assocCAB) ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4))) = rows_assocCAB ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_1 : (tripleIndices 4 1 4).map ((HexagonAtoms473.assocCAB) ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4))) = rows_assocCAB ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_2 : (tripleIndices 4 1 4).map ((HexagonAtoms473.assocCAB) ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4))) = rows_assocCAB ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_3 : (tripleIndices 4 1 4).map ((HexagonAtoms473.assocCAB) ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4))) = rows_assocCAB ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_0 : (tripleIndices 4 1 4).map ((HexagonAtoms473.assocCAB) ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4))) = rows_assocCAB ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_1 : (tripleIndices 4 1 4).map ((HexagonAtoms473.assocCAB) ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4))) = rows_assocCAB ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_2 : (tripleIndices 4 1 4).map ((HexagonAtoms473.assocCAB) ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4))) = rows_assocCAB ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_3 : (tripleIndices 4 1 4).map ((HexagonAtoms473.assocCAB) ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4))) = rows_assocCAB ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_2_0 : (tripleIndices 4 1 4).map ((HexagonAtoms473.assocCAB) ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4))) = rows_assocCAB ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_2_1 : (tripleIndices 4 1 4).map ((HexagonAtoms473.assocCAB) ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4))) = rows_assocCAB ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_2_2 : (tripleIndices 4 1 4).map ((HexagonAtoms473.assocCAB) ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4))) = rows_assocCAB ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_2_3 : (tripleIndices 4 1 4).map ((HexagonAtoms473.assocCAB) ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4))) = rows_assocCAB ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_3_0 : (tripleIndices 4 1 4).map ((HexagonAtoms473.assocCAB) ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4))) = rows_assocCAB ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_3_1 : (tripleIndices 4 1 4).map ((HexagonAtoms473.assocCAB) ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4))) = rows_assocCAB ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_3_2 : (tripleIndices 4 1 4).map ((HexagonAtoms473.assocCAB) ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4))) = rows_assocCAB ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_3_3 : (tripleIndices 4 1 4).map ((HexagonAtoms473.assocCAB) ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4))) = rows_assocCAB ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocCAB_data (r : RightIndex 3 4 7) : (tripleIndices 4 1 4).map ((HexagonAtoms473.assocCAB) r) = rows_assocCAB r := by
  fin_cases r
  · exact rows_assocCAB_eq_0_0_0
  · exact rows_assocCAB_eq_0_0_1
  · exact rows_assocCAB_eq_0_0_2
  · exact rows_assocCAB_eq_0_0_3
  · exact rows_assocCAB_eq_0_1_0
  · exact rows_assocCAB_eq_0_1_1
  · exact rows_assocCAB_eq_0_1_2
  · exact rows_assocCAB_eq_0_1_3
  · exact rows_assocCAB_eq_0_2_0
  · exact rows_assocCAB_eq_0_2_1
  · exact rows_assocCAB_eq_0_2_2
  · exact rows_assocCAB_eq_0_2_3
  · exact rows_assocCAB_eq_0_3_0
  · exact rows_assocCAB_eq_0_3_1
  · exact rows_assocCAB_eq_0_3_2
  · exact rows_assocCAB_eq_0_3_3

private def cols_right0Data : List (List ℤ) := [decodeIntegerRow 16 3 1 36403682,
    decodeIntegerRow 16 3 1 18334726,
    decodeIntegerRow 16 3 1 27900658,
    decodeIntegerRow 16 3 1 35340854,
    decodeIntegerRow 16 3 1 6642986,
    decodeIntegerRow 16 3 1 24712018,
    decodeIntegerRow 16 3 1 15146074,
    decodeIntegerRow 16 3 1 7705922,
    decodeIntegerRow 16 3 1 21696214,
    decodeIntegerRow 16 3 1 21444142,
    decodeIntegerRow 16 3 1 21484966,
    decodeIntegerRow 16 3 1 21341758,
    decodeIntegerRow 16 3 1 21691678,
    decodeIntegerRow 16 3 1 21445114,
    decodeIntegerRow 16 3 1 21483022,
    decodeIntegerRow 16 3 1 21337546]

def cols_right0 (r : LeftIndex 4 7 3) : List ℤ := cols_right0Data.getD (leftPosition 4 7 3 r) []

private theorem cols_right0_eq_0_0_0 : (tripleIndices 2 2 4).map (fun j => (right0Middle4 7 3) j ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4))) = cols_right0 ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_1 : (tripleIndices 2 2 4).map (fun j => (right0Middle4 7 3) j ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4))) = cols_right0 ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_2 : (tripleIndices 2 2 4).map (fun j => (right0Middle4 7 3) j ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4))) = cols_right0 ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_3 : (tripleIndices 2 2 4).map (fun j => (right0Middle4 7 3) j ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4))) = cols_right0 ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_0 : (tripleIndices 2 2 4).map (fun j => (right0Middle4 7 3) j ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4))) = cols_right0 ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_1 : (tripleIndices 2 2 4).map (fun j => (right0Middle4 7 3) j ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4))) = cols_right0 ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_2 : (tripleIndices 2 2 4).map (fun j => (right0Middle4 7 3) j ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4))) = cols_right0 ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_3 : (tripleIndices 2 2 4).map (fun j => (right0Middle4 7 3) j ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4))) = cols_right0 ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_2_0 : (tripleIndices 2 2 4).map (fun j => (right0Middle4 7 3) j ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4))) = cols_right0 ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_2_1 : (tripleIndices 2 2 4).map (fun j => (right0Middle4 7 3) j ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4))) = cols_right0 ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_2_2 : (tripleIndices 2 2 4).map (fun j => (right0Middle4 7 3) j ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4))) = cols_right0 ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_2_3 : (tripleIndices 2 2 4).map (fun j => (right0Middle4 7 3) j ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4))) = cols_right0 ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_3_0 : (tripleIndices 2 2 4).map (fun j => (right0Middle4 7 3) j ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4))) = cols_right0 ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_3_1 : (tripleIndices 2 2 4).map (fun j => (right0Middle4 7 3) j ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4))) = cols_right0 ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_3_2 : (tripleIndices 2 2 4).map (fun j => (right0Middle4 7 3) j ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4))) = cols_right0 ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_3_3 : (tripleIndices 2 2 4).map (fun j => (right0Middle4 7 3) j ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4))) = cols_right0 ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right0_data (r : LeftIndex 4 7 3) : (tripleIndices 2 2 4).map (fun j => (right0Middle4 7 3) j r) = cols_right0 r := by
  fin_cases r
  · exact cols_right0_eq_0_0_0
  · exact cols_right0_eq_0_0_1
  · exact cols_right0_eq_0_0_2
  · exact cols_right0_eq_0_0_3
  · exact cols_right0_eq_0_1_0
  · exact cols_right0_eq_0_1_1
  · exact cols_right0_eq_0_1_2
  · exact cols_right0_eq_0_1_3
  · exact cols_right0_eq_0_2_0
  · exact cols_right0_eq_0_2_1
  · exact cols_right0_eq_0_2_2
  · exact cols_right0_eq_0_2_3
  · exact cols_right0_eq_0_3_0
  · exact cols_right0_eq_0_3_1
  · exact cols_right0_eq_0_3_2
  · exact cols_right0_eq_0_3_3

private def cols_left0Data : List (List ℤ) := [decodeIntegerRow 16 3 1 36403682,
    decodeIntegerRow 16 3 1 18334726,
    decodeIntegerRow 16 3 1 27900658,
    decodeIntegerRow 16 3 1 35340854,
    decodeIntegerRow 16 3 1 6642986,
    decodeIntegerRow 16 3 1 24712018,
    decodeIntegerRow 16 3 1 15146074,
    decodeIntegerRow 16 3 1 7705922,
    decodeIntegerRow 16 3 1 21696214,
    decodeIntegerRow 16 3 1 21444142,
    decodeIntegerRow 16 3 1 21484966,
    decodeIntegerRow 16 3 1 21341758,
    decodeIntegerRow 16 3 1 21691678,
    decodeIntegerRow 16 3 1 21445114,
    decodeIntegerRow 16 3 1 21483022,
    decodeIntegerRow 16 3 1 21337546]

def cols_left0 (r : LeftIndex 4 7 3) : List ℤ := cols_left0Data.getD (leftPosition 4 7 3 r) []

private theorem cols_left0_eq_0_0_0 : (tripleIndices 2 2 4).map (fun j => (left0Middle4 7 3) j ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4))) = cols_left0 ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_1 : (tripleIndices 2 2 4).map (fun j => (left0Middle4 7 3) j ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4))) = cols_left0 ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_2 : (tripleIndices 2 2 4).map (fun j => (left0Middle4 7 3) j ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4))) = cols_left0 ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_3 : (tripleIndices 2 2 4).map (fun j => (left0Middle4 7 3) j ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4))) = cols_left0 ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_0 : (tripleIndices 2 2 4).map (fun j => (left0Middle4 7 3) j ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4))) = cols_left0 ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_1 : (tripleIndices 2 2 4).map (fun j => (left0Middle4 7 3) j ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4))) = cols_left0 ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_2 : (tripleIndices 2 2 4).map (fun j => (left0Middle4 7 3) j ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4))) = cols_left0 ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_3 : (tripleIndices 2 2 4).map (fun j => (left0Middle4 7 3) j ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4))) = cols_left0 ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_2_0 : (tripleIndices 2 2 4).map (fun j => (left0Middle4 7 3) j ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4))) = cols_left0 ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_2_1 : (tripleIndices 2 2 4).map (fun j => (left0Middle4 7 3) j ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4))) = cols_left0 ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_2_2 : (tripleIndices 2 2 4).map (fun j => (left0Middle4 7 3) j ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4))) = cols_left0 ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_2_3 : (tripleIndices 2 2 4).map (fun j => (left0Middle4 7 3) j ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4))) = cols_left0 ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_3_0 : (tripleIndices 2 2 4).map (fun j => (left0Middle4 7 3) j ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4))) = cols_left0 ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_3_1 : (tripleIndices 2 2 4).map (fun j => (left0Middle4 7 3) j ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4))) = cols_left0 ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_3_2 : (tripleIndices 2 2 4).map (fun j => (left0Middle4 7 3) j ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4))) = cols_left0 ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_3_3 : (tripleIndices 2 2 4).map (fun j => (left0Middle4 7 3) j ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4))) = cols_left0 ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_left0_data (r : LeftIndex 4 7 3) : (tripleIndices 2 2 4).map (fun j => (left0Middle4 7 3) j r) = cols_left0 r := by
  fin_cases r
  · exact cols_left0_eq_0_0_0
  · exact cols_left0_eq_0_0_1
  · exact cols_left0_eq_0_0_2
  · exact cols_left0_eq_0_0_3
  · exact cols_left0_eq_0_1_0
  · exact cols_left0_eq_0_1_1
  · exact cols_left0_eq_0_1_2
  · exact cols_left0_eq_0_1_3
  · exact cols_left0_eq_0_2_0
  · exact cols_left0_eq_0_2_1
  · exact cols_left0_eq_0_2_2
  · exact cols_left0_eq_0_2_3
  · exact cols_left0_eq_0_3_0
  · exact cols_left0_eq_0_3_1
  · exact cols_left0_eq_0_3_2
  · exact cols_left0_eq_0_3_3

private def cols_right2Data : List (List ℤ) := [decodeIntegerRow 16 3 1 36574792,
    decodeIntegerRow 16 3 1 18253688,
    decodeIntegerRow 16 3 1 27859208,
    decodeIntegerRow 16 3 1 35156152,
    decodeIntegerRow 16 3 1 6813124,
    decodeIntegerRow 16 3 1 24635516,
    decodeIntegerRow 16 3 1 15108836,
    decodeIntegerRow 16 3 1 7523164,
    decodeIntegerRow 16 3 1 18258276,
    decodeIntegerRow 16 3 1 36573796,
    decodeIntegerRow 16 3 1 35158084,
    decodeIntegerRow 16 3 1 27863364,
    decodeIntegerRow 16 3 1 24631032,
    decodeIntegerRow 16 3 1 6814072,
    decodeIntegerRow 16 3 1 7521208,
    decodeIntegerRow 16 3 1 15104568]

def cols_right2 (r : LeftIndex 4 7 3) : List ℤ := cols_right2Data.getD (leftPosition 4 7 3 r) []

private theorem cols_right2_eq_0_0_0 : (tripleIndices 4 1 4).map (fun j => (right2Middle4 7 3) j ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4))) = cols_right2 ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_1 : (tripleIndices 4 1 4).map (fun j => (right2Middle4 7 3) j ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4))) = cols_right2 ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_2 : (tripleIndices 4 1 4).map (fun j => (right2Middle4 7 3) j ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4))) = cols_right2 ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_3 : (tripleIndices 4 1 4).map (fun j => (right2Middle4 7 3) j ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4))) = cols_right2 ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_0 : (tripleIndices 4 1 4).map (fun j => (right2Middle4 7 3) j ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4))) = cols_right2 ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_1 : (tripleIndices 4 1 4).map (fun j => (right2Middle4 7 3) j ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4))) = cols_right2 ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_2 : (tripleIndices 4 1 4).map (fun j => (right2Middle4 7 3) j ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4))) = cols_right2 ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_3 : (tripleIndices 4 1 4).map (fun j => (right2Middle4 7 3) j ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4))) = cols_right2 ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_2_0 : (tripleIndices 4 1 4).map (fun j => (right2Middle4 7 3) j ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4))) = cols_right2 ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_2_1 : (tripleIndices 4 1 4).map (fun j => (right2Middle4 7 3) j ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4))) = cols_right2 ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_2_2 : (tripleIndices 4 1 4).map (fun j => (right2Middle4 7 3) j ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4))) = cols_right2 ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_2_3 : (tripleIndices 4 1 4).map (fun j => (right2Middle4 7 3) j ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4))) = cols_right2 ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_3_0 : (tripleIndices 4 1 4).map (fun j => (right2Middle4 7 3) j ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4))) = cols_right2 ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_3_1 : (tripleIndices 4 1 4).map (fun j => (right2Middle4 7 3) j ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4))) = cols_right2 ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_3_2 : (tripleIndices 4 1 4).map (fun j => (right2Middle4 7 3) j ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4))) = cols_right2 ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_3_3 : (tripleIndices 4 1 4).map (fun j => (right2Middle4 7 3) j ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4))) = cols_right2 ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right2_data (r : LeftIndex 4 7 3) : (tripleIndices 4 1 4).map (fun j => (right2Middle4 7 3) j r) = cols_right2 r := by
  fin_cases r
  · exact cols_right2_eq_0_0_0
  · exact cols_right2_eq_0_0_1
  · exact cols_right2_eq_0_0_2
  · exact cols_right2_eq_0_0_3
  · exact cols_right2_eq_0_1_0
  · exact cols_right2_eq_0_1_1
  · exact cols_right2_eq_0_1_2
  · exact cols_right2_eq_0_1_3
  · exact cols_right2_eq_0_2_0
  · exact cols_right2_eq_0_2_1
  · exact cols_right2_eq_0_2_2
  · exact cols_right2_eq_0_2_3
  · exact cols_right2_eq_0_3_0
  · exact cols_right2_eq_0_3_1
  · exact cols_right2_eq_0_3_2
  · exact cols_right2_eq_0_3_3

theorem product0_eq : HexagonAtoms473.outerABC * HexagonAtoms473.assocABC = HexagonAtoms473.assocABC :=
  Matrix.one_mul (m := Fin 2 × Fin 2 × Fin 4) (n := Fin 1 × Fin 4 × Fin 4) _

theorem product1_eq : HexagonAtoms473.assocBAC * HexagonAtoms473.innerABC = HexagonAtoms473.assocBAC :=
  Matrix.mul_one (m := Fin 4 × Fin 1 × Fin 4) (n := Fin 1 × Fin 4 × Fin 4) _

theorem product2_eq : HexagonAtoms473.innerRightABC * HexagonAtoms473.assocABC = HexagonAtoms473.assocABC :=
  Matrix.one_mul (m := Fin 2 × Fin 2 × Fin 4) (n := Fin 1 × Fin 4 × Fin 4) _

theorem product3_eq : HexagonAtoms473.inverseACB * right0Middle4 7 3 = rowColumnMul rows_inverseACB cols_right0 :=
  (rowColumnMul_eq _ _ _ _ rows_inverseACB_data cols_right0_data).symm

theorem product4_eq : HexagonAtoms473.innerACB * right1Middle4 7 3 = right1Middle4 7 3 :=
  Matrix.one_mul (m := Fin 4 × Fin 1 × Fin 4) (n := Fin 1 × Fin 4 × Fin 4) _

theorem product5_eq : HexagonAtoms473.assocBCA * left0Middle4 7 3 = rowColumnMul rows_assocBCA cols_left0 :=
  (rowColumnMul_eq _ _ _ _ rows_assocBCA_data cols_left0_data).symm

theorem product6_eq : HexagonAtoms473.innerRightBAC * left1Middle4 7 3 = left1Middle4 7 3 :=
  Matrix.one_mul (m := Fin 4 × Fin 1 × Fin 4) (n := Fin 1 × Fin 4 × Fin 4) _

theorem product7_eq : HexagonAtoms473.assocCAB * right2Middle4 7 3 = rowColumnMul rows_assocCAB cols_right2 :=
  (rowColumnMul_eq _ _ _ _ rows_assocCAB_data cols_right2_data).symm

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn473
