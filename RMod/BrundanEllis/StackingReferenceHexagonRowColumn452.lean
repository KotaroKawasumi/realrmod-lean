import RMod.BrundanEllis.StackingReferenceHexagonAtoms452
import RMod.BrundanEllis.StackingReferenceHexagonMiddle4
import RMod.BrundanEllis.StackingReferenceRowColumnCheck

/-! Verified row and column lists. Each subsequent scalar product traverses
these lists directly, without repeated lookup into the original matrices. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn452
open Superfusion

private def rows_inverseACBData : List (List ℤ) := [decodeIntegerRow 32 3 1 720889769845756,
    decodeIntegerRow 32 3 1 309680110774328,
    decodeIntegerRow 32 3 1 906269435328964,
    decodeIntegerRow 32 3 1 865536753020872,
    decodeIntegerRow 32 3 1 951834743446684,
    decodeIntegerRow 32 3 1 1002734716933768,
    decodeIntegerRow 32 3 1 1132692953674204,
    decodeIntegerRow 32 3 1 1545033880101128,
    decodeIntegerRow 32 3 1 1545033877265316,
    decodeIntegerRow 32 3 1 720327234228472,
    decodeIntegerRow 32 3 1 1002734745592036,
    decodeIntegerRow 32 3 1 901185454957432,
    decodeIntegerRow 32 3 1 987483464568004,
    decodeIntegerRow 32 3 1 906269444907592,
    decodeIntegerRow 32 3 1 1543340074533116,
    decodeIntegerRow 32 3 1 720889768660408,
    decodeIntegerRow 32 3 1 309687862727048,
    decodeIntegerRow 32 3 1 1132107174957724,
    decodeIntegerRow 32 3 1 865473876071032,
    decodeIntegerRow 32 3 1 946939288581796,
    decodeIntegerRow 32 3 1 1002797421617992,
    decodeIntegerRow 32 3 1 900997426880644,
    decodeIntegerRow 32 3 1 1545027678538952,
    decodeIntegerRow 32 3 1 720345830416324,
    decodeIntegerRow 32 3 1 1132674357495112,
    decodeIntegerRow 32 3 1 1545027681371844,
    decodeIntegerRow 32 3 1 952022771524552,
    decodeIntegerRow 32 3 1 1002797392959364,
    decodeIntegerRow 32 3 1 946939298161288,
    decodeIntegerRow 32 3 1 987546284043484,
    decodeIntegerRow 32 3 1 1132107173781112,
    decodeIntegerRow 32 3 1 1543332329666276]

def rows_inverseACB (r : LeftIndex 4 2 5) : List ℤ := rows_inverseACBData.getD (leftPosition 4 2 5 r) []

private theorem rows_inverseACB_eq_0_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms452.inverseACB) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms452.inverseACB) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms452.inverseACB) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms452.inverseACB) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms452.inverseACB) ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms452.inverseACB) ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms452.inverseACB) ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms452.inverseACB) ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_0 : (tripleIndices 4 1 8).map ((HexagonAtoms452.inverseACB) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8))) = rows_inverseACB ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_1 : (tripleIndices 4 1 8).map ((HexagonAtoms452.inverseACB) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8))) = rows_inverseACB ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_2 : (tripleIndices 4 1 8).map ((HexagonAtoms452.inverseACB) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8))) = rows_inverseACB ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_3 : (tripleIndices 4 1 8).map ((HexagonAtoms452.inverseACB) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8))) = rows_inverseACB ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_4 : (tripleIndices 4 1 8).map ((HexagonAtoms452.inverseACB) ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8))) = rows_inverseACB ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_5 : (tripleIndices 4 1 8).map ((HexagonAtoms452.inverseACB) ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8))) = rows_inverseACB ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_6 : (tripleIndices 4 1 8).map ((HexagonAtoms452.inverseACB) ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8))) = rows_inverseACB ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_7 : (tripleIndices 4 1 8).map ((HexagonAtoms452.inverseACB) ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8))) = rows_inverseACB ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms452.inverseACB) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms452.inverseACB) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms452.inverseACB) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms452.inverseACB) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms452.inverseACB) ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms452.inverseACB) ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms452.inverseACB) ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms452.inverseACB) ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_0 : (tripleIndices 4 1 8).map ((HexagonAtoms452.inverseACB) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8))) = rows_inverseACB ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_1 : (tripleIndices 4 1 8).map ((HexagonAtoms452.inverseACB) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8))) = rows_inverseACB ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_2 : (tripleIndices 4 1 8).map ((HexagonAtoms452.inverseACB) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8))) = rows_inverseACB ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_3 : (tripleIndices 4 1 8).map ((HexagonAtoms452.inverseACB) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8))) = rows_inverseACB ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_4 : (tripleIndices 4 1 8).map ((HexagonAtoms452.inverseACB) ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8))) = rows_inverseACB ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_5 : (tripleIndices 4 1 8).map ((HexagonAtoms452.inverseACB) ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8))) = rows_inverseACB ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_6 : (tripleIndices 4 1 8).map ((HexagonAtoms452.inverseACB) ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8))) = rows_inverseACB ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_7 : (tripleIndices 4 1 8).map ((HexagonAtoms452.inverseACB) ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8))) = rows_inverseACB ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_inverseACB_data (r : LeftIndex 4 2 5) : (tripleIndices 4 1 8).map ((HexagonAtoms452.inverseACB) r) = rows_inverseACB r := by
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
  · exact rows_inverseACB_eq_1_0_0
  · exact rows_inverseACB_eq_1_0_1
  · exact rows_inverseACB_eq_1_0_2
  · exact rows_inverseACB_eq_1_0_3
  · exact rows_inverseACB_eq_1_0_4
  · exact rows_inverseACB_eq_1_0_5
  · exact rows_inverseACB_eq_1_0_6
  · exact rows_inverseACB_eq_1_0_7
  · exact rows_inverseACB_eq_1_1_0
  · exact rows_inverseACB_eq_1_1_1
  · exact rows_inverseACB_eq_1_1_2
  · exact rows_inverseACB_eq_1_1_3
  · exact rows_inverseACB_eq_1_1_4
  · exact rows_inverseACB_eq_1_1_5
  · exact rows_inverseACB_eq_1_1_6
  · exact rows_inverseACB_eq_1_1_7

private def rows_assocBCAData : List (List ℤ) := [decodeIntegerRow 32 3 1 1132130419006084,
    decodeIntegerRow 32 3 1 1543340078077512,
    decodeIntegerRow 32 3 1 946750753522876,
    decodeIntegerRow 32 3 1 987483435830968,
    decodeIntegerRow 32 3 1 901185445405156,
    decodeIntegerRow 32 3 1 850285471918072,
    decodeIntegerRow 32 3 1 720327235177636,
    decodeIntegerRow 32 3 1 307986308750712,
    decodeIntegerRow 32 3 1 307986311586524,
    decodeIntegerRow 32 3 1 1132692954623368,
    decodeIntegerRow 32 3 1 850285443259804,
    decodeIntegerRow 32 3 1 951834733894408,
    decodeIntegerRow 32 3 1 865536724283836,
    decodeIntegerRow 32 3 1 946750743944248,
    decodeIntegerRow 32 3 1 309680114318724,
    decodeIntegerRow 32 3 1 1132130420191432,
    decodeIntegerRow 32 3 1 1543332326124792,
    decodeIntegerRow 32 3 1 720913013894116,
    decodeIntegerRow 32 3 1 987546312780808,
    decodeIntegerRow 32 3 1 906080900270044,
    decodeIntegerRow 32 3 1 850222767233848,
    decodeIntegerRow 32 3 1 952022761971196,
    decodeIntegerRow 32 3 1 307992510312888,
    decodeIntegerRow 32 3 1 1132674358435516,
    decodeIntegerRow 32 3 1 720345831356728,
    decodeIntegerRow 32 3 1 307992507479996,
    decodeIntegerRow 32 3 1 900997417327288,
    decodeIntegerRow 32 3 1 850222795892476,
    decodeIntegerRow 32 3 1 906080890690552,
    decodeIntegerRow 32 3 1 865473904808356,
    decodeIntegerRow 32 3 1 720913015070728,
    decodeIntegerRow 32 3 1 309687859185564]

def rows_assocBCA (r : RightIndex 5 2 4) : List ℤ := rows_assocBCAData.getD (rightPosition 5 2 4 r) []

private theorem rows_assocBCA_eq_0_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms452.assocBCA) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8))) = rows_assocBCA ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms452.assocBCA) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8))) = rows_assocBCA ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms452.assocBCA) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8))) = rows_assocBCA ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms452.assocBCA) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8))) = rows_assocBCA ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms452.assocBCA) ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8))) = rows_assocBCA ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms452.assocBCA) ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8))) = rows_assocBCA ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms452.assocBCA) ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8))) = rows_assocBCA ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms452.assocBCA) ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8))) = rows_assocBCA ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_0 : (tripleIndices 4 1 8).map ((HexagonAtoms452.assocBCA) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8))) = rows_assocBCA ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_1 : (tripleIndices 4 1 8).map ((HexagonAtoms452.assocBCA) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8))) = rows_assocBCA ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_2 : (tripleIndices 4 1 8).map ((HexagonAtoms452.assocBCA) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8))) = rows_assocBCA ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_3 : (tripleIndices 4 1 8).map ((HexagonAtoms452.assocBCA) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8))) = rows_assocBCA ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_4 : (tripleIndices 4 1 8).map ((HexagonAtoms452.assocBCA) ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8))) = rows_assocBCA ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_5 : (tripleIndices 4 1 8).map ((HexagonAtoms452.assocBCA) ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8))) = rows_assocBCA ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_6 : (tripleIndices 4 1 8).map ((HexagonAtoms452.assocBCA) ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8))) = rows_assocBCA ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_7 : (tripleIndices 4 1 8).map ((HexagonAtoms452.assocBCA) ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8))) = rows_assocBCA ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_0 : (tripleIndices 4 1 8).map ((HexagonAtoms452.assocBCA) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8))) = rows_assocBCA ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_1 : (tripleIndices 4 1 8).map ((HexagonAtoms452.assocBCA) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8))) = rows_assocBCA ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_2 : (tripleIndices 4 1 8).map ((HexagonAtoms452.assocBCA) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8))) = rows_assocBCA ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_3 : (tripleIndices 4 1 8).map ((HexagonAtoms452.assocBCA) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8))) = rows_assocBCA ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_4 : (tripleIndices 4 1 8).map ((HexagonAtoms452.assocBCA) ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8))) = rows_assocBCA ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_5 : (tripleIndices 4 1 8).map ((HexagonAtoms452.assocBCA) ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8))) = rows_assocBCA ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_6 : (tripleIndices 4 1 8).map ((HexagonAtoms452.assocBCA) ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8))) = rows_assocBCA ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_7 : (tripleIndices 4 1 8).map ((HexagonAtoms452.assocBCA) ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8))) = rows_assocBCA ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_0 : (tripleIndices 4 1 8).map ((HexagonAtoms452.assocBCA) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8))) = rows_assocBCA ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_1 : (tripleIndices 4 1 8).map ((HexagonAtoms452.assocBCA) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8))) = rows_assocBCA ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_2 : (tripleIndices 4 1 8).map ((HexagonAtoms452.assocBCA) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8))) = rows_assocBCA ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_3 : (tripleIndices 4 1 8).map ((HexagonAtoms452.assocBCA) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8))) = rows_assocBCA ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_4 : (tripleIndices 4 1 8).map ((HexagonAtoms452.assocBCA) ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8))) = rows_assocBCA ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_5 : (tripleIndices 4 1 8).map ((HexagonAtoms452.assocBCA) ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8))) = rows_assocBCA ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_6 : (tripleIndices 4 1 8).map ((HexagonAtoms452.assocBCA) ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8))) = rows_assocBCA ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_7 : (tripleIndices 4 1 8).map ((HexagonAtoms452.assocBCA) ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8))) = rows_assocBCA ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocBCA_data (r : RightIndex 5 2 4) : (tripleIndices 4 1 8).map ((HexagonAtoms452.assocBCA) r) = rows_assocBCA r := by
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
  · exact rows_assocBCA_eq_1_0_0
  · exact rows_assocBCA_eq_1_0_1
  · exact rows_assocBCA_eq_1_0_2
  · exact rows_assocBCA_eq_1_0_3
  · exact rows_assocBCA_eq_1_0_4
  · exact rows_assocBCA_eq_1_0_5
  · exact rows_assocBCA_eq_1_0_6
  · exact rows_assocBCA_eq_1_0_7
  · exact rows_assocBCA_eq_1_1_0
  · exact rows_assocBCA_eq_1_1_1
  · exact rows_assocBCA_eq_1_1_2
  · exact rows_assocBCA_eq_1_1_3
  · exact rows_assocBCA_eq_1_1_4
  · exact rows_assocBCA_eq_1_1_5
  · exact rows_assocBCA_eq_1_1_6
  · exact rows_assocBCA_eq_1_1_7

private def rows_assocCABData : List (List ℤ) := [decodeIntegerRow 32 3 1 926792394763216,
    decodeIntegerRow 32 3 1 927357426259240,
    decodeIntegerRow 32 3 1 929050797999340,
    decodeIntegerRow 32 3 1 934136079311712,
    decodeIntegerRow 32 3 1 949376421746896,
    decodeIntegerRow 32 3 1 995143972924840,
    decodeIntegerRow 32 3 1 1132307083872940,
    decodeIntegerRow 32 3 1 1544214870175072,
    decodeIntegerRow 32 3 1 995136999354580,
    decodeIntegerRow 32 3 1 949397342448928,
    decodeIntegerRow 32 3 1 308868080795824,
    decodeIntegerRow 32 3 1 720524818620760,
    decodeIntegerRow 32 3 1 925662848686060,
    decodeIntegerRow 32 3 1 926227535808352,
    decodeIntegerRow 32 3 1 934135304470736,
    decodeIntegerRow 32 3 1 929053122522280,
    decodeIntegerRow 32 3 1 1544214873363880,
    decodeIntegerRow 32 3 1 720713106041296,
    decodeIntegerRow 32 3 1 995143944225568,
    decodeIntegerRow 32 3 1 903643757543380,
    decodeIntegerRow 32 3 1 918884109500760,
    decodeIntegerRow 32 3 1 929050797986224,
    decodeIntegerRow 32 3 1 925662762946912,
    decodeIntegerRow 32 3 1 926792394881260,
    decodeIntegerRow 32 3 1 929053122509152,
    decodeIntegerRow 32 3 1 918884884341740,
    decodeIntegerRow 32 3 1 926227535690200,
    decodeIntegerRow 32 3 1 927357339811504,
    decodeIntegerRow 32 3 1 1132495369167712,
    decodeIntegerRow 32 3 1 308868077607340,
    decodeIntegerRow 32 3 1 903622836832600,
    decodeIntegerRow 32 3 1 995136970658224]

def rows_assocCAB (r : RightIndex 2 4 5) : List ℤ := rows_assocCABData.getD (rightPosition 2 4 5 r) []

private theorem rows_assocCAB_eq_0_0_0 : (tripleIndices 2 2 8).map ((HexagonAtoms452.assocCAB) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_assocCAB ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_1 : (tripleIndices 2 2 8).map ((HexagonAtoms452.assocCAB) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_assocCAB ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_2 : (tripleIndices 2 2 8).map ((HexagonAtoms452.assocCAB) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_assocCAB ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_3 : (tripleIndices 2 2 8).map ((HexagonAtoms452.assocCAB) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_assocCAB ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_4 : (tripleIndices 2 2 8).map ((HexagonAtoms452.assocCAB) ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_assocCAB ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_5 : (tripleIndices 2 2 8).map ((HexagonAtoms452.assocCAB) ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_assocCAB ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_6 : (tripleIndices 2 2 8).map ((HexagonAtoms452.assocCAB) ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_assocCAB ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_7 : (tripleIndices 2 2 8).map ((HexagonAtoms452.assocCAB) ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_assocCAB ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_0 : (tripleIndices 2 2 8).map ((HexagonAtoms452.assocCAB) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_assocCAB ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_1 : (tripleIndices 2 2 8).map ((HexagonAtoms452.assocCAB) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_assocCAB ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_2 : (tripleIndices 2 2 8).map ((HexagonAtoms452.assocCAB) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_assocCAB ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_3 : (tripleIndices 2 2 8).map ((HexagonAtoms452.assocCAB) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_assocCAB ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_4 : (tripleIndices 2 2 8).map ((HexagonAtoms452.assocCAB) ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_assocCAB ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_5 : (tripleIndices 2 2 8).map ((HexagonAtoms452.assocCAB) ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_assocCAB ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_6 : (tripleIndices 2 2 8).map ((HexagonAtoms452.assocCAB) ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_assocCAB ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_7 : (tripleIndices 2 2 8).map ((HexagonAtoms452.assocCAB) ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_assocCAB ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_0 : (tripleIndices 2 2 8).map ((HexagonAtoms452.assocCAB) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_assocCAB ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_1 : (tripleIndices 2 2 8).map ((HexagonAtoms452.assocCAB) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_assocCAB ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_2 : (tripleIndices 2 2 8).map ((HexagonAtoms452.assocCAB) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_assocCAB ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_3 : (tripleIndices 2 2 8).map ((HexagonAtoms452.assocCAB) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_assocCAB ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_4 : (tripleIndices 2 2 8).map ((HexagonAtoms452.assocCAB) ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_assocCAB ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_5 : (tripleIndices 2 2 8).map ((HexagonAtoms452.assocCAB) ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_assocCAB ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_6 : (tripleIndices 2 2 8).map ((HexagonAtoms452.assocCAB) ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_assocCAB ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_7 : (tripleIndices 2 2 8).map ((HexagonAtoms452.assocCAB) ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_assocCAB ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_0 : (tripleIndices 2 2 8).map ((HexagonAtoms452.assocCAB) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = rows_assocCAB ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_1 : (tripleIndices 2 2 8).map ((HexagonAtoms452.assocCAB) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = rows_assocCAB ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_2 : (tripleIndices 2 2 8).map ((HexagonAtoms452.assocCAB) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = rows_assocCAB ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_3 : (tripleIndices 2 2 8).map ((HexagonAtoms452.assocCAB) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = rows_assocCAB ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_4 : (tripleIndices 2 2 8).map ((HexagonAtoms452.assocCAB) ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = rows_assocCAB ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_5 : (tripleIndices 2 2 8).map ((HexagonAtoms452.assocCAB) ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = rows_assocCAB ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_6 : (tripleIndices 2 2 8).map ((HexagonAtoms452.assocCAB) ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = rows_assocCAB ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_7 : (tripleIndices 2 2 8).map ((HexagonAtoms452.assocCAB) ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = rows_assocCAB ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocCAB_data (r : RightIndex 2 4 5) : (tripleIndices 2 2 8).map ((HexagonAtoms452.assocCAB) r) = rows_assocCAB r := by
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
  · exact rows_assocCAB_eq_2_0_0
  · exact rows_assocCAB_eq_2_0_1
  · exact rows_assocCAB_eq_2_0_2
  · exact rows_assocCAB_eq_2_0_3
  · exact rows_assocCAB_eq_2_0_4
  · exact rows_assocCAB_eq_2_0_5
  · exact rows_assocCAB_eq_2_0_6
  · exact rows_assocCAB_eq_2_0_7
  · exact rows_assocCAB_eq_3_0_0
  · exact rows_assocCAB_eq_3_0_1
  · exact rows_assocCAB_eq_3_0_2
  · exact rows_assocCAB_eq_3_0_3
  · exact rows_assocCAB_eq_3_0_4
  · exact rows_assocCAB_eq_3_0_5
  · exact rows_assocCAB_eq_3_0_6
  · exact rows_assocCAB_eq_3_0_7

private def cols_right0Data : List (List ℤ) := [decodeIntegerRow 32 3 1 1132087373350060,
    decodeIntegerRow 32 3 1 1543241928364528,
    decodeIntegerRow 32 3 1 946841142071984,
    decodeIntegerRow 32 3 1 987503266018180,
    decodeIntegerRow 32 3 1 901088331988460,
    decodeIntegerRow 32 3 1 850244835855088,
    decodeIntegerRow 32 3 1 720305195372464,
    decodeIntegerRow 32 3 1 307895393722180,
    decodeIntegerRow 32 3 1 1132714994660500,
    decodeIntegerRow 32 3 1 1545124791586288,
    decodeIntegerRow 32 3 1 951931847282864,
    decodeIntegerRow 32 3 1 1002775381738300,
    decodeIntegerRow 32 3 1 946841151623340,
    decodeIntegerRow 32 3 1 987503237364112,
    decodeIntegerRow 32 3 1 1132087372405456,
    decodeIntegerRow 32 3 1 1543241931198340,
    decodeIntegerRow 32 3 1 901094530717740,
    decodeIntegerRow 32 3 1 1002756756817648,
    decodeIntegerRow 32 3 1 1132652317453744,
    decodeIntegerRow 32 3 1 308083421799940,
    decodeIntegerRow 32 3 1 720869967288940,
    decodeIntegerRow 32 3 1 1543430473001968,
    decodeIntegerRow 32 3 1 946848890480304,
    decodeIntegerRow 32 3 1 865493677599940,
    decodeIntegerRow 32 3 1 906171288817260,
    decodeIntegerRow 32 3 1 987526482589072,
    decodeIntegerRow 32 3 1 1132150220617936,
    decodeIntegerRow 32 3 1 309589713014980,
    decodeIntegerRow 32 3 1 1132652318634580,
    decodeIntegerRow 32 3 1 308083425342448,
    decodeIntegerRow 32 3 1 901094540295344,
    decodeIntegerRow 32 3 1 1002756785550460]

def cols_right0 (r : LeftIndex 4 5 2) : List ℤ := cols_right0Data.getD (leftPosition 4 5 2 r) []

private theorem cols_right0_eq_0_0_0 : (tripleIndices 4 1 8).map (fun j => (right0Middle4 5 2) j ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = cols_right0 ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_1 : (tripleIndices 4 1 8).map (fun j => (right0Middle4 5 2) j ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = cols_right0 ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_2 : (tripleIndices 4 1 8).map (fun j => (right0Middle4 5 2) j ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = cols_right0 ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_3 : (tripleIndices 4 1 8).map (fun j => (right0Middle4 5 2) j ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = cols_right0 ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_4 : (tripleIndices 4 1 8).map (fun j => (right0Middle4 5 2) j ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = cols_right0 ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_5 : (tripleIndices 4 1 8).map (fun j => (right0Middle4 5 2) j ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = cols_right0 ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_6 : (tripleIndices 4 1 8).map (fun j => (right0Middle4 5 2) j ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = cols_right0 ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_7 : (tripleIndices 4 1 8).map (fun j => (right0Middle4 5 2) j ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = cols_right0 ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_0 : (tripleIndices 4 1 8).map (fun j => (right0Middle4 5 2) j ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = cols_right0 ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_1 : (tripleIndices 4 1 8).map (fun j => (right0Middle4 5 2) j ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = cols_right0 ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_2 : (tripleIndices 4 1 8).map (fun j => (right0Middle4 5 2) j ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = cols_right0 ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_3 : (tripleIndices 4 1 8).map (fun j => (right0Middle4 5 2) j ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = cols_right0 ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_4 : (tripleIndices 4 1 8).map (fun j => (right0Middle4 5 2) j ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = cols_right0 ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_5 : (tripleIndices 4 1 8).map (fun j => (right0Middle4 5 2) j ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = cols_right0 ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_6 : (tripleIndices 4 1 8).map (fun j => (right0Middle4 5 2) j ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = cols_right0 ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_7 : (tripleIndices 4 1 8).map (fun j => (right0Middle4 5 2) j ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = cols_right0 ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_0 : (tripleIndices 4 1 8).map (fun j => (right0Middle4 5 2) j ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = cols_right0 ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_1 : (tripleIndices 4 1 8).map (fun j => (right0Middle4 5 2) j ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = cols_right0 ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_2 : (tripleIndices 4 1 8).map (fun j => (right0Middle4 5 2) j ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = cols_right0 ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_3 : (tripleIndices 4 1 8).map (fun j => (right0Middle4 5 2) j ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = cols_right0 ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_4 : (tripleIndices 4 1 8).map (fun j => (right0Middle4 5 2) j ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = cols_right0 ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_5 : (tripleIndices 4 1 8).map (fun j => (right0Middle4 5 2) j ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = cols_right0 ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_6 : (tripleIndices 4 1 8).map (fun j => (right0Middle4 5 2) j ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = cols_right0 ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_7 : (tripleIndices 4 1 8).map (fun j => (right0Middle4 5 2) j ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = cols_right0 ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_0 : (tripleIndices 4 1 8).map (fun j => (right0Middle4 5 2) j ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = cols_right0 ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_1 : (tripleIndices 4 1 8).map (fun j => (right0Middle4 5 2) j ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = cols_right0 ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_2 : (tripleIndices 4 1 8).map (fun j => (right0Middle4 5 2) j ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = cols_right0 ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_3 : (tripleIndices 4 1 8).map (fun j => (right0Middle4 5 2) j ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = cols_right0 ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_4 : (tripleIndices 4 1 8).map (fun j => (right0Middle4 5 2) j ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = cols_right0 ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_5 : (tripleIndices 4 1 8).map (fun j => (right0Middle4 5 2) j ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = cols_right0 ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_6 : (tripleIndices 4 1 8).map (fun j => (right0Middle4 5 2) j ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = cols_right0 ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_7 : (tripleIndices 4 1 8).map (fun j => (right0Middle4 5 2) j ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = cols_right0 ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right0_data (r : LeftIndex 4 5 2) : (tripleIndices 4 1 8).map (fun j => (right0Middle4 5 2) j r) = cols_right0 r := by
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
  · exact cols_right0_eq_2_0_0
  · exact cols_right0_eq_2_0_1
  · exact cols_right0_eq_2_0_2
  · exact cols_right0_eq_2_0_3
  · exact cols_right0_eq_2_0_4
  · exact cols_right0_eq_2_0_5
  · exact cols_right0_eq_2_0_6
  · exact cols_right0_eq_2_0_7
  · exact cols_right0_eq_3_0_0
  · exact cols_right0_eq_3_0_1
  · exact cols_right0_eq_3_0_2
  · exact cols_right0_eq_3_0_3
  · exact cols_right0_eq_3_0_4
  · exact cols_right0_eq_3_0_5
  · exact cols_right0_eq_3_0_6
  · exact cols_right0_eq_3_0_7

private def cols_left0Data : List (List ℤ) := [decodeIntegerRow 32 3 1 1132087373350060,
    decodeIntegerRow 32 3 1 1543241928364528,
    decodeIntegerRow 32 3 1 946841142071984,
    decodeIntegerRow 32 3 1 987503266018180,
    decodeIntegerRow 32 3 1 901088331988460,
    decodeIntegerRow 32 3 1 850244835855088,
    decodeIntegerRow 32 3 1 720305195372464,
    decodeIntegerRow 32 3 1 307895393722180,
    decodeIntegerRow 32 3 1 1132714994660500,
    decodeIntegerRow 32 3 1 1545124791586288,
    decodeIntegerRow 32 3 1 951931847282864,
    decodeIntegerRow 32 3 1 1002775381738300,
    decodeIntegerRow 32 3 1 946841151623340,
    decodeIntegerRow 32 3 1 987503237364112,
    decodeIntegerRow 32 3 1 1132087372405456,
    decodeIntegerRow 32 3 1 1543241931198340,
    decodeIntegerRow 32 3 1 901094530717740,
    decodeIntegerRow 32 3 1 1002756756817648,
    decodeIntegerRow 32 3 1 1132652317453744,
    decodeIntegerRow 32 3 1 308083421799940,
    decodeIntegerRow 32 3 1 720869967288940,
    decodeIntegerRow 32 3 1 1543430473001968,
    decodeIntegerRow 32 3 1 946848890480304,
    decodeIntegerRow 32 3 1 865493677599940,
    decodeIntegerRow 32 3 1 906171288817260,
    decodeIntegerRow 32 3 1 987526482589072,
    decodeIntegerRow 32 3 1 1132150220617936,
    decodeIntegerRow 32 3 1 309589713014980,
    decodeIntegerRow 32 3 1 1132652318634580,
    decodeIntegerRow 32 3 1 308083425342448,
    decodeIntegerRow 32 3 1 901094540295344,
    decodeIntegerRow 32 3 1 1002756785550460]

def cols_left0 (r : LeftIndex 4 5 2) : List ℤ := cols_left0Data.getD (leftPosition 4 5 2 r) []

private theorem cols_left0_eq_0_0_0 : (tripleIndices 4 1 8).map (fun j => (left0Middle4 5 2) j ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = cols_left0 ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_1 : (tripleIndices 4 1 8).map (fun j => (left0Middle4 5 2) j ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = cols_left0 ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_2 : (tripleIndices 4 1 8).map (fun j => (left0Middle4 5 2) j ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = cols_left0 ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_3 : (tripleIndices 4 1 8).map (fun j => (left0Middle4 5 2) j ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = cols_left0 ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_4 : (tripleIndices 4 1 8).map (fun j => (left0Middle4 5 2) j ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = cols_left0 ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_5 : (tripleIndices 4 1 8).map (fun j => (left0Middle4 5 2) j ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = cols_left0 ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_6 : (tripleIndices 4 1 8).map (fun j => (left0Middle4 5 2) j ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = cols_left0 ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_7 : (tripleIndices 4 1 8).map (fun j => (left0Middle4 5 2) j ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = cols_left0 ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_0 : (tripleIndices 4 1 8).map (fun j => (left0Middle4 5 2) j ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = cols_left0 ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_1 : (tripleIndices 4 1 8).map (fun j => (left0Middle4 5 2) j ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = cols_left0 ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_2 : (tripleIndices 4 1 8).map (fun j => (left0Middle4 5 2) j ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = cols_left0 ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_3 : (tripleIndices 4 1 8).map (fun j => (left0Middle4 5 2) j ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = cols_left0 ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_4 : (tripleIndices 4 1 8).map (fun j => (left0Middle4 5 2) j ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = cols_left0 ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_5 : (tripleIndices 4 1 8).map (fun j => (left0Middle4 5 2) j ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = cols_left0 ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_6 : (tripleIndices 4 1 8).map (fun j => (left0Middle4 5 2) j ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = cols_left0 ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_7 : (tripleIndices 4 1 8).map (fun j => (left0Middle4 5 2) j ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = cols_left0 ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_0 : (tripleIndices 4 1 8).map (fun j => (left0Middle4 5 2) j ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = cols_left0 ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_1 : (tripleIndices 4 1 8).map (fun j => (left0Middle4 5 2) j ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = cols_left0 ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_2 : (tripleIndices 4 1 8).map (fun j => (left0Middle4 5 2) j ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = cols_left0 ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_3 : (tripleIndices 4 1 8).map (fun j => (left0Middle4 5 2) j ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = cols_left0 ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_4 : (tripleIndices 4 1 8).map (fun j => (left0Middle4 5 2) j ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = cols_left0 ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_5 : (tripleIndices 4 1 8).map (fun j => (left0Middle4 5 2) j ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = cols_left0 ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_6 : (tripleIndices 4 1 8).map (fun j => (left0Middle4 5 2) j ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = cols_left0 ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_7 : (tripleIndices 4 1 8).map (fun j => (left0Middle4 5 2) j ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = cols_left0 ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_0 : (tripleIndices 4 1 8).map (fun j => (left0Middle4 5 2) j ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = cols_left0 ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_1 : (tripleIndices 4 1 8).map (fun j => (left0Middle4 5 2) j ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = cols_left0 ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_2 : (tripleIndices 4 1 8).map (fun j => (left0Middle4 5 2) j ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = cols_left0 ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_3 : (tripleIndices 4 1 8).map (fun j => (left0Middle4 5 2) j ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = cols_left0 ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_4 : (tripleIndices 4 1 8).map (fun j => (left0Middle4 5 2) j ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = cols_left0 ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_5 : (tripleIndices 4 1 8).map (fun j => (left0Middle4 5 2) j ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = cols_left0 ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_6 : (tripleIndices 4 1 8).map (fun j => (left0Middle4 5 2) j ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = cols_left0 ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_7 : (tripleIndices 4 1 8).map (fun j => (left0Middle4 5 2) j ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = cols_left0 ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_left0_data (r : LeftIndex 4 5 2) : (tripleIndices 4 1 8).map (fun j => (left0Middle4 5 2) j r) = cols_left0 r := by
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
  · exact cols_left0_eq_2_0_0
  · exact cols_left0_eq_2_0_1
  · exact cols_left0_eq_2_0_2
  · exact cols_left0_eq_2_0_3
  · exact cols_left0_eq_2_0_4
  · exact cols_left0_eq_2_0_5
  · exact cols_left0_eq_2_0_6
  · exact cols_left0_eq_2_0_7
  · exact cols_left0_eq_3_0_0
  · exact cols_left0_eq_3_0_1
  · exact cols_left0_eq_3_0_2
  · exact cols_left0_eq_3_0_3
  · exact cols_left0_eq_3_0_4
  · exact cols_left0_eq_3_0_5
  · exact cols_left0_eq_3_0_6
  · exact cols_left0_eq_3_0_7

private def cols_right2Data : List (List ℤ) := [decodeIntegerRow 32 5 2 13146406230484512657560,
    decodeIntegerRow 32 5 2 20882641992273462537752,
    decodeIntegerRow 32 5 2 21025691308655297225272,
    decodeIntegerRow 32 5 2 13861662334122215845064,
    decodeIntegerRow 32 5 2 20877873697595921912872,
    decodeIntegerRow 32 5 2 13116842308365340783064,
    decodeIntegerRow 32 5 2 9391361278090965795064,
    decodeIntegerRow 32 5 2 2250220575042015665272,
    decodeIntegerRow 32 5 2 9421354716811622095064,
    decodeIntegerRow 32 5 2 2257380761809790975272,
    decodeIntegerRow 32 5 2 20882630625085962852872,
    decodeIntegerRow 32 5 2 13146454277359512733064,
    decodeIntegerRow 32 5 2 21032836236634009415272,
    decodeIntegerRow 32 5 2 13891750377335059545064,
    decodeIntegerRow 32 5 2 13116890391861434607560,
    decodeIntegerRow 32 5 2 20877862176599828477752,
    decodeIntegerRow 32 5 2 2250220575012915975352,
    decodeIntegerRow 32 5 2 13891703087172997045064,
    decodeIntegerRow 32 5 2 13116842308486465857560,
    decodeIntegerRow 32 5 2 2405190667810765662872,
    decodeIntegerRow 32 5 2 9421402031387840845064,
    decodeIntegerRow 32 5 2 21025691308684790665352,
    decodeIntegerRow 32 5 2 2400422373132837537752,
    decodeIntegerRow 32 5 2 13146406230605575233064,
    decodeIntegerRow 32 5 2 20877862176580103162872,
    decodeIntegerRow 32 5 2 10166173973404403357560,
    decodeIntegerRow 32 5 2 13891750377212059595560,
    decodeIntegerRow 32 5 2 2250228128723853165272,
    decodeIntegerRow 32 5 2 10136610087906387733064,
    decodeIntegerRow 32 5 2 20882630625066625037752,
    decodeIntegerRow 32 5 2 21025683603606665975272,
    decodeIntegerRow 32 5 2 9421354716934715795560]

def cols_right2 (r : LeftIndex 4 5 2) : List ℤ := cols_right2Data.getD (leftPosition 4 5 2 r) []

private theorem cols_right2_eq_0_0_0 : (tripleIndices 2 2 8).map (fun j => (right2Middle4 5 2) j ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = cols_right2 ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_1 : (tripleIndices 2 2 8).map (fun j => (right2Middle4 5 2) j ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = cols_right2 ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_2 : (tripleIndices 2 2 8).map (fun j => (right2Middle4 5 2) j ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = cols_right2 ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_3 : (tripleIndices 2 2 8).map (fun j => (right2Middle4 5 2) j ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = cols_right2 ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_4 : (tripleIndices 2 2 8).map (fun j => (right2Middle4 5 2) j ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = cols_right2 ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_5 : (tripleIndices 2 2 8).map (fun j => (right2Middle4 5 2) j ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = cols_right2 ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_6 : (tripleIndices 2 2 8).map (fun j => (right2Middle4 5 2) j ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = cols_right2 ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_7 : (tripleIndices 2 2 8).map (fun j => (right2Middle4 5 2) j ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = cols_right2 ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_0 : (tripleIndices 2 2 8).map (fun j => (right2Middle4 5 2) j ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = cols_right2 ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_1 : (tripleIndices 2 2 8).map (fun j => (right2Middle4 5 2) j ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = cols_right2 ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_2 : (tripleIndices 2 2 8).map (fun j => (right2Middle4 5 2) j ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = cols_right2 ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_3 : (tripleIndices 2 2 8).map (fun j => (right2Middle4 5 2) j ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = cols_right2 ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_4 : (tripleIndices 2 2 8).map (fun j => (right2Middle4 5 2) j ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = cols_right2 ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_5 : (tripleIndices 2 2 8).map (fun j => (right2Middle4 5 2) j ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = cols_right2 ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_6 : (tripleIndices 2 2 8).map (fun j => (right2Middle4 5 2) j ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = cols_right2 ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_7 : (tripleIndices 2 2 8).map (fun j => (right2Middle4 5 2) j ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = cols_right2 ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_0 : (tripleIndices 2 2 8).map (fun j => (right2Middle4 5 2) j ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = cols_right2 ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_1 : (tripleIndices 2 2 8).map (fun j => (right2Middle4 5 2) j ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = cols_right2 ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_2 : (tripleIndices 2 2 8).map (fun j => (right2Middle4 5 2) j ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = cols_right2 ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_3 : (tripleIndices 2 2 8).map (fun j => (right2Middle4 5 2) j ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = cols_right2 ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_4 : (tripleIndices 2 2 8).map (fun j => (right2Middle4 5 2) j ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = cols_right2 ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_5 : (tripleIndices 2 2 8).map (fun j => (right2Middle4 5 2) j ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = cols_right2 ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_6 : (tripleIndices 2 2 8).map (fun j => (right2Middle4 5 2) j ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = cols_right2 ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_7 : (tripleIndices 2 2 8).map (fun j => (right2Middle4 5 2) j ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = cols_right2 ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_0 : (tripleIndices 2 2 8).map (fun j => (right2Middle4 5 2) j ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8))) = cols_right2 ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_1 : (tripleIndices 2 2 8).map (fun j => (right2Middle4 5 2) j ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8))) = cols_right2 ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_2 : (tripleIndices 2 2 8).map (fun j => (right2Middle4 5 2) j ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8))) = cols_right2 ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_3 : (tripleIndices 2 2 8).map (fun j => (right2Middle4 5 2) j ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8))) = cols_right2 ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_4 : (tripleIndices 2 2 8).map (fun j => (right2Middle4 5 2) j ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8))) = cols_right2 ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_5 : (tripleIndices 2 2 8).map (fun j => (right2Middle4 5 2) j ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8))) = cols_right2 ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_6 : (tripleIndices 2 2 8).map (fun j => (right2Middle4 5 2) j ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8))) = cols_right2 ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_7 : (tripleIndices 2 2 8).map (fun j => (right2Middle4 5 2) j ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8))) = cols_right2 ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right2_data (r : LeftIndex 4 5 2) : (tripleIndices 2 2 8).map (fun j => (right2Middle4 5 2) j r) = cols_right2 r := by
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
  · exact cols_right2_eq_2_0_0
  · exact cols_right2_eq_2_0_1
  · exact cols_right2_eq_2_0_2
  · exact cols_right2_eq_2_0_3
  · exact cols_right2_eq_2_0_4
  · exact cols_right2_eq_2_0_5
  · exact cols_right2_eq_2_0_6
  · exact cols_right2_eq_2_0_7
  · exact cols_right2_eq_3_0_0
  · exact cols_right2_eq_3_0_1
  · exact cols_right2_eq_3_0_2
  · exact cols_right2_eq_3_0_3
  · exact cols_right2_eq_3_0_4
  · exact cols_right2_eq_3_0_5
  · exact cols_right2_eq_3_0_6
  · exact cols_right2_eq_3_0_7

theorem product0_eq : HexagonAtoms452.outerABC * HexagonAtoms452.assocABC = HexagonAtoms452.assocABC :=
  Matrix.one_mul (m := Fin 4 × Fin 1 × Fin 8) (n := Fin 4 × Fin 1 × Fin 8) _

theorem product1_eq : HexagonAtoms452.assocBAC * HexagonAtoms452.innerABC = HexagonAtoms452.assocBAC :=
  Matrix.mul_one (m := Fin 2 × Fin 2 × Fin 8) (n := Fin 4 × Fin 1 × Fin 8) _

theorem product2_eq : HexagonAtoms452.innerRightABC * HexagonAtoms452.assocABC = HexagonAtoms452.assocABC :=
  Matrix.one_mul (m := Fin 4 × Fin 1 × Fin 8) (n := Fin 4 × Fin 1 × Fin 8) _

theorem product3_eq : HexagonAtoms452.inverseACB * right0Middle4 5 2 = rowColumnMul rows_inverseACB cols_right0 :=
  (rowColumnMul_eq _ _ _ _ rows_inverseACB_data cols_right0_data).symm

theorem product4_eq : HexagonAtoms452.innerACB * right1Middle4 5 2 = right1Middle4 5 2 :=
  Matrix.one_mul (m := Fin 2 × Fin 2 × Fin 8) (n := Fin 4 × Fin 1 × Fin 8) _

theorem product5_eq : HexagonAtoms452.assocBCA * left0Middle4 5 2 = rowColumnMul rows_assocBCA cols_left0 :=
  (rowColumnMul_eq _ _ _ _ rows_assocBCA_data cols_left0_data).symm

theorem product6_eq : HexagonAtoms452.innerRightBAC * left1Middle4 5 2 = left1Middle4 5 2 :=
  Matrix.one_mul (m := Fin 2 × Fin 2 × Fin 8) (n := Fin 4 × Fin 1 × Fin 8) _

theorem product7_eq : HexagonAtoms452.assocCAB * right2Middle4 5 2 = rowColumnMul rows_assocCAB cols_right2 :=
  (rowColumnMul_eq _ _ _ _ rows_assocCAB_data cols_right2_data).symm

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn452
