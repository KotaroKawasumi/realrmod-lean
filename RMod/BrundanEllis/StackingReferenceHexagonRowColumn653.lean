import RMod.BrundanEllis.StackingReferenceHexagonAtoms653
import RMod.BrundanEllis.StackingReferenceHexagonMiddle6
import RMod.BrundanEllis.StackingReferenceRowColumnCheck

/-! Verified row and column lists. Each subsequent scalar product traverses
these lists directly, without repeated lookup into the original matrices. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn653
open Superfusion

private def rows_inverseACBData : List (List ℤ) := [decodeIntegerRow 32 3 1 785881637237444,
    decodeIntegerRow 32 3 1 1574304698824972,
    decodeIntegerRow 32 3 1 1513309226564836,
    decodeIntegerRow 32 3 1 1199295457537388,
    decodeIntegerRow 32 3 1 1559813629231684,
    decodeIntegerRow 32 3 1 792618074939532,
    decodeIntegerRow 32 3 1 1202768267165796,
    decodeIntegerRow 32 3 1 1529306580642028,
    decodeIntegerRow 32 3 1 1199295429530772,
    decodeIntegerRow 32 3 1 339710975122276,
    decodeIntegerRow 32 3 1 1574304705045748,
    decodeIntegerRow 32 3 1 1067138581038404,
    decodeIntegerRow 32 3 1 323713595535892,
    decodeIntegerRow 32 3 1 1202768294429156,
    decodeIntegerRow 32 3 1 1060402083815028,
    decodeIntegerRow 32 3 1 1559813622697924,
    decodeIntegerRow 32 3 1 323897318939188,
    decodeIntegerRow 32 3 1 1202684095047036,
    decodeIntegerRow 32 3 1 1060361275518932,
    decodeIntegerRow 32 3 1 1559620601199964,
    decodeIntegerRow 32 3 1 1199378595800012,
    decodeIntegerRow 32 3 1 339532072947844,
    decodeIntegerRow 32 3 1 1574502203400748,
    decodeIntegerRow 32 3 1 1067181455568036,
    decodeIntegerRow 32 3 1 293399581116124,
    decodeIntegerRow 32 3 1 1060361305625388,
    decodeIntegerRow 32 3 1 650336121076476,
    decodeIntegerRow 32 3 1 323897331616972,
    decodeIntegerRow 32 3 1 1067181426152996,
    decodeIntegerRow 32 3 1 278517991669972,
    decodeIntegerRow 32 3 1 339532060116484,
    decodeIntegerRow 32 3 1 653641565053748]

def rows_inverseACB (r : LeftIndex 6 3 5) : List ℤ := rows_inverseACBData.getD (leftPosition 6 3 5 r) []

private theorem rows_inverseACB_eq_0_0_0 : (tripleIndices 8 1 4).map ((HexagonAtoms653.inverseACB) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_1 : (tripleIndices 8 1 4).map ((HexagonAtoms653.inverseACB) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_2 : (tripleIndices 8 1 4).map ((HexagonAtoms653.inverseACB) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_3 : (tripleIndices 8 1 4).map ((HexagonAtoms653.inverseACB) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_0 : (tripleIndices 8 1 4).map ((HexagonAtoms653.inverseACB) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_inverseACB ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_1 : (tripleIndices 8 1 4).map ((HexagonAtoms653.inverseACB) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_inverseACB ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_2 : (tripleIndices 8 1 4).map ((HexagonAtoms653.inverseACB) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_inverseACB ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_3 : (tripleIndices 8 1 4).map ((HexagonAtoms653.inverseACB) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_inverseACB ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_0 : (tripleIndices 8 1 4).map ((HexagonAtoms653.inverseACB) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_1 : (tripleIndices 8 1 4).map ((HexagonAtoms653.inverseACB) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_2 : (tripleIndices 8 1 4).map ((HexagonAtoms653.inverseACB) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_3 : (tripleIndices 8 1 4).map ((HexagonAtoms653.inverseACB) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_0 : (tripleIndices 8 1 4).map ((HexagonAtoms653.inverseACB) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_inverseACB ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_1 : (tripleIndices 8 1 4).map ((HexagonAtoms653.inverseACB) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_inverseACB ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_2 : (tripleIndices 8 1 4).map ((HexagonAtoms653.inverseACB) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_inverseACB ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_3 : (tripleIndices 8 1 4).map ((HexagonAtoms653.inverseACB) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_inverseACB ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_0 : (tripleIndices 8 1 4).map ((HexagonAtoms653.inverseACB) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_1 : (tripleIndices 8 1 4).map ((HexagonAtoms653.inverseACB) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_2 : (tripleIndices 8 1 4).map ((HexagonAtoms653.inverseACB) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_3 : (tripleIndices 8 1 4).map ((HexagonAtoms653.inverseACB) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_1_0 : (tripleIndices 8 1 4).map ((HexagonAtoms653.inverseACB) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_inverseACB ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_1_1 : (tripleIndices 8 1 4).map ((HexagonAtoms653.inverseACB) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_inverseACB ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_1_2 : (tripleIndices 8 1 4).map ((HexagonAtoms653.inverseACB) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_inverseACB ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_1_3 : (tripleIndices 8 1 4).map ((HexagonAtoms653.inverseACB) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_inverseACB ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_0 : (tripleIndices 8 1 4).map ((HexagonAtoms653.inverseACB) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_1 : (tripleIndices 8 1 4).map ((HexagonAtoms653.inverseACB) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_2 : (tripleIndices 8 1 4).map ((HexagonAtoms653.inverseACB) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_3 : (tripleIndices 8 1 4).map ((HexagonAtoms653.inverseACB) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_1_0 : (tripleIndices 8 1 4).map ((HexagonAtoms653.inverseACB) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_inverseACB ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_1_1 : (tripleIndices 8 1 4).map ((HexagonAtoms653.inverseACB) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_inverseACB ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_1_2 : (tripleIndices 8 1 4).map ((HexagonAtoms653.inverseACB) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_inverseACB ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_1_3 : (tripleIndices 8 1 4).map ((HexagonAtoms653.inverseACB) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_inverseACB ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_inverseACB_data (r : LeftIndex 6 3 5) : (tripleIndices 8 1 4).map ((HexagonAtoms653.inverseACB) r) = rows_inverseACB r := by
  fin_cases r
  · exact rows_inverseACB_eq_0_0_0
  · exact rows_inverseACB_eq_0_0_1
  · exact rows_inverseACB_eq_0_0_2
  · exact rows_inverseACB_eq_0_0_3
  · exact rows_inverseACB_eq_0_1_0
  · exact rows_inverseACB_eq_0_1_1
  · exact rows_inverseACB_eq_0_1_2
  · exact rows_inverseACB_eq_0_1_3
  · exact rows_inverseACB_eq_1_0_0
  · exact rows_inverseACB_eq_1_0_1
  · exact rows_inverseACB_eq_1_0_2
  · exact rows_inverseACB_eq_1_0_3
  · exact rows_inverseACB_eq_1_1_0
  · exact rows_inverseACB_eq_1_1_1
  · exact rows_inverseACB_eq_1_1_2
  · exact rows_inverseACB_eq_1_1_3
  · exact rows_inverseACB_eq_2_0_0
  · exact rows_inverseACB_eq_2_0_1
  · exact rows_inverseACB_eq_2_0_2
  · exact rows_inverseACB_eq_2_0_3
  · exact rows_inverseACB_eq_2_1_0
  · exact rows_inverseACB_eq_2_1_1
  · exact rows_inverseACB_eq_2_1_2
  · exact rows_inverseACB_eq_2_1_3
  · exact rows_inverseACB_eq_3_0_0
  · exact rows_inverseACB_eq_3_0_1
  · exact rows_inverseACB_eq_3_0_2
  · exact rows_inverseACB_eq_3_0_3
  · exact rows_inverseACB_eq_3_1_0
  · exact rows_inverseACB_eq_3_1_1
  · exact rows_inverseACB_eq_3_1_2
  · exact rows_inverseACB_eq_3_1_3

private def rows_assocBCAData : List (List ℤ) := [decodeIntegerRow 32 3 1 785881637237444,
    decodeIntegerRow 32 3 1 1574304698824972,
    decodeIntegerRow 32 3 1 1513309226564836,
    decodeIntegerRow 32 3 1 1199295457537388,
    decodeIntegerRow 32 3 1 1559813629231684,
    decodeIntegerRow 32 3 1 792618074939532,
    decodeIntegerRow 32 3 1 1202768267165796,
    decodeIntegerRow 32 3 1 1529306580642028,
    decodeIntegerRow 32 3 1 1199295429530772,
    decodeIntegerRow 32 3 1 339710975122276,
    decodeIntegerRow 32 3 1 1574304705045748,
    decodeIntegerRow 32 3 1 1067138581038404,
    decodeIntegerRow 32 3 1 323713595535892,
    decodeIntegerRow 32 3 1 1202768294429156,
    decodeIntegerRow 32 3 1 1060402083815028,
    decodeIntegerRow 32 3 1 1559813622697924,
    decodeIntegerRow 32 3 1 1529122869912652,
    decodeIntegerRow 32 3 1 650336093804804,
    decodeIntegerRow 32 3 1 792658913332908,
    decodeIntegerRow 32 3 1 293399587651876,
    decodeIntegerRow 32 3 1 653641593051828,
    decodeIntegerRow 32 3 1 1513488115903996,
    decodeIntegerRow 32 3 1 278517985451092,
    decodeIntegerRow 32 3 1 785838733283804,
    decodeIntegerRow 32 3 1 1559620607735716,
    decodeIntegerRow 32 3 1 792658883226452,
    decodeIntegerRow 32 3 1 1202684067775364,
    decodeIntegerRow 32 3 1 1529122857234868,
    decodeIntegerRow 32 3 1 785838762698844,
    decodeIntegerRow 32 3 1 1574502197181868,
    decodeIntegerRow 32 3 1 1513488128735356,
    decodeIntegerRow 32 3 1 1199378623798092]

def rows_assocBCA (r : RightIndex 5 3 6) : List ℤ := rows_assocBCAData.getD (rightPosition 5 3 6 r) []

private theorem rows_assocBCA_eq_0_0_0 : (tripleIndices 8 1 4).map ((HexagonAtoms653.assocBCA) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_assocBCA ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_1 : (tripleIndices 8 1 4).map ((HexagonAtoms653.assocBCA) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_assocBCA ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_2 : (tripleIndices 8 1 4).map ((HexagonAtoms653.assocBCA) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_assocBCA ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_3 : (tripleIndices 8 1 4).map ((HexagonAtoms653.assocBCA) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_assocBCA ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_0 : (tripleIndices 8 1 4).map ((HexagonAtoms653.assocBCA) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_assocBCA ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_1 : (tripleIndices 8 1 4).map ((HexagonAtoms653.assocBCA) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_assocBCA ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_2 : (tripleIndices 8 1 4).map ((HexagonAtoms653.assocBCA) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_assocBCA ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_3 : (tripleIndices 8 1 4).map ((HexagonAtoms653.assocBCA) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_assocBCA ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_0 : (tripleIndices 8 1 4).map ((HexagonAtoms653.assocBCA) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_assocBCA ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_1 : (tripleIndices 8 1 4).map ((HexagonAtoms653.assocBCA) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_assocBCA ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_2 : (tripleIndices 8 1 4).map ((HexagonAtoms653.assocBCA) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_assocBCA ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_3 : (tripleIndices 8 1 4).map ((HexagonAtoms653.assocBCA) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_assocBCA ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_0 : (tripleIndices 8 1 4).map ((HexagonAtoms653.assocBCA) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_assocBCA ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_1 : (tripleIndices 8 1 4).map ((HexagonAtoms653.assocBCA) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_assocBCA ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_2 : (tripleIndices 8 1 4).map ((HexagonAtoms653.assocBCA) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_assocBCA ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_3 : (tripleIndices 8 1 4).map ((HexagonAtoms653.assocBCA) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_assocBCA ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_0 : (tripleIndices 8 1 4).map ((HexagonAtoms653.assocBCA) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_assocBCA ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_1 : (tripleIndices 8 1 4).map ((HexagonAtoms653.assocBCA) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_assocBCA ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_2 : (tripleIndices 8 1 4).map ((HexagonAtoms653.assocBCA) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_assocBCA ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_3 : (tripleIndices 8 1 4).map ((HexagonAtoms653.assocBCA) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_assocBCA ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_1_0 : (tripleIndices 8 1 4).map ((HexagonAtoms653.assocBCA) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_assocBCA ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_1_1 : (tripleIndices 8 1 4).map ((HexagonAtoms653.assocBCA) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_assocBCA ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_1_2 : (tripleIndices 8 1 4).map ((HexagonAtoms653.assocBCA) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_assocBCA ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_1_3 : (tripleIndices 8 1 4).map ((HexagonAtoms653.assocBCA) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_assocBCA ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_0 : (tripleIndices 8 1 4).map ((HexagonAtoms653.assocBCA) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_assocBCA ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_1 : (tripleIndices 8 1 4).map ((HexagonAtoms653.assocBCA) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_assocBCA ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_2 : (tripleIndices 8 1 4).map ((HexagonAtoms653.assocBCA) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_assocBCA ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_3 : (tripleIndices 8 1 4).map ((HexagonAtoms653.assocBCA) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_assocBCA ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_1_0 : (tripleIndices 8 1 4).map ((HexagonAtoms653.assocBCA) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_assocBCA ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_1_1 : (tripleIndices 8 1 4).map ((HexagonAtoms653.assocBCA) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_assocBCA ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_1_2 : (tripleIndices 8 1 4).map ((HexagonAtoms653.assocBCA) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_assocBCA ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_1_3 : (tripleIndices 8 1 4).map ((HexagonAtoms653.assocBCA) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_assocBCA ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocBCA_data (r : RightIndex 5 3 6) : (tripleIndices 8 1 4).map ((HexagonAtoms653.assocBCA) r) = rows_assocBCA r := by
  fin_cases r
  · exact rows_assocBCA_eq_0_0_0
  · exact rows_assocBCA_eq_0_0_1
  · exact rows_assocBCA_eq_0_0_2
  · exact rows_assocBCA_eq_0_0_3
  · exact rows_assocBCA_eq_0_1_0
  · exact rows_assocBCA_eq_0_1_1
  · exact rows_assocBCA_eq_0_1_2
  · exact rows_assocBCA_eq_0_1_3
  · exact rows_assocBCA_eq_1_0_0
  · exact rows_assocBCA_eq_1_0_1
  · exact rows_assocBCA_eq_1_0_2
  · exact rows_assocBCA_eq_1_0_3
  · exact rows_assocBCA_eq_1_1_0
  · exact rows_assocBCA_eq_1_1_1
  · exact rows_assocBCA_eq_1_1_2
  · exact rows_assocBCA_eq_1_1_3
  · exact rows_assocBCA_eq_2_0_0
  · exact rows_assocBCA_eq_2_0_1
  · exact rows_assocBCA_eq_2_0_2
  · exact rows_assocBCA_eq_2_0_3
  · exact rows_assocBCA_eq_2_1_0
  · exact rows_assocBCA_eq_2_1_1
  · exact rows_assocBCA_eq_2_1_2
  · exact rows_assocBCA_eq_2_1_3
  · exact rows_assocBCA_eq_3_0_0
  · exact rows_assocBCA_eq_3_0_1
  · exact rows_assocBCA_eq_3_0_2
  · exact rows_assocBCA_eq_3_0_3
  · exact rows_assocBCA_eq_3_1_0
  · exact rows_assocBCA_eq_3_1_1
  · exact rows_assocBCA_eq_3_1_2
  · exact rows_assocBCA_eq_3_1_3

private def rows_assocCABData : List (List ℤ) := [decodeIntegerRow 32 3 1 926415822107660,
    decodeIntegerRow 32 3 1 926541432436624,
    decodeIntegerRow 32 3 1 926498471811340,
    decodeIntegerRow 32 3 1 926513193789616,
    decodeIntegerRow 32 3 1 926416080386528,
    decodeIntegerRow 32 3 1 926541518534440,
    decodeIntegerRow 32 3 1 926500796334112,
    decodeIntegerRow 32 3 1 926513968631080,
    decodeIntegerRow 32 3 1 1002766069866280,
    decodeIntegerRow 32 3 1 946845022469728,
    decodeIntegerRow 32 3 1 1545030784108840,
    decodeIntegerRow 32 3 1 1132118811313312,
    decodeIntegerRow 32 3 1 865505315018416,
    decodeIntegerRow 32 3 1 901091437914100,
    decodeIntegerRow 32 3 1 309683991527824,
    decodeIntegerRow 32 3 1 720336547163380,
    decodeIntegerRow 32 3 1 926478756410848,
    decodeIntegerRow 32 3 1 926604366745640,
    decodeIntegerRow 32 3 1 926506995061792,
    decodeIntegerRow 32 3 1 926521717040680,
    decodeIntegerRow 32 3 1 926478670321780,
    decodeIntegerRow 32 3 1 926604108463856,
    decodeIntegerRow 32 3 1 926506220221300,
    decodeIntegerRow 32 3 1 926519392517584,
    decodeIntegerRow 32 3 1 946845019635376,
    decodeIntegerRow 32 3 1 1002766068685300,
    decodeIntegerRow 32 3 1 1132118782654864,
    decodeIntegerRow 32 3 1 1545030774529780,
    decodeIntegerRow 32 3 1 901091434371160,
    decodeIntegerRow 32 3 1 865505314073632,
    decodeIntegerRow 32 3 1 720336518426200,
    decodeIntegerRow 32 3 1 309683981975008]

def rows_assocCAB (r : RightIndex 3 6 5) : List ℤ := rows_assocCABData.getD (rightPosition 3 6 5 r) []

private theorem rows_assocCAB_eq_0_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms653.assocCAB) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 4))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms653.assocCAB) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 4))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms653.assocCAB) ((0 : Fin 2), (0 : Fin 4), (2 : Fin 4))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms653.assocCAB) ((0 : Fin 2), (0 : Fin 4), (3 : Fin 4))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms653.assocCAB) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 4))) = rows_assocCAB ((0 : Fin 2), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms653.assocCAB) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 4))) = rows_assocCAB ((0 : Fin 2), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms653.assocCAB) ((0 : Fin 2), (1 : Fin 4), (2 : Fin 4))) = rows_assocCAB ((0 : Fin 2), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms653.assocCAB) ((0 : Fin 2), (1 : Fin 4), (3 : Fin 4))) = rows_assocCAB ((0 : Fin 2), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_2_0 : (tripleIndices 4 2 4).map ((HexagonAtoms653.assocCAB) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 4))) = rows_assocCAB ((0 : Fin 2), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_2_1 : (tripleIndices 4 2 4).map ((HexagonAtoms653.assocCAB) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 4))) = rows_assocCAB ((0 : Fin 2), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_2_2 : (tripleIndices 4 2 4).map ((HexagonAtoms653.assocCAB) ((0 : Fin 2), (2 : Fin 4), (2 : Fin 4))) = rows_assocCAB ((0 : Fin 2), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_2_3 : (tripleIndices 4 2 4).map ((HexagonAtoms653.assocCAB) ((0 : Fin 2), (2 : Fin 4), (3 : Fin 4))) = rows_assocCAB ((0 : Fin 2), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_3_0 : (tripleIndices 4 2 4).map ((HexagonAtoms653.assocCAB) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 4))) = rows_assocCAB ((0 : Fin 2), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_3_1 : (tripleIndices 4 2 4).map ((HexagonAtoms653.assocCAB) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 4))) = rows_assocCAB ((0 : Fin 2), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_3_2 : (tripleIndices 4 2 4).map ((HexagonAtoms653.assocCAB) ((0 : Fin 2), (3 : Fin 4), (2 : Fin 4))) = rows_assocCAB ((0 : Fin 2), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_3_3 : (tripleIndices 4 2 4).map ((HexagonAtoms653.assocCAB) ((0 : Fin 2), (3 : Fin 4), (3 : Fin 4))) = rows_assocCAB ((0 : Fin 2), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms653.assocCAB) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 4))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms653.assocCAB) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 4))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms653.assocCAB) ((1 : Fin 2), (0 : Fin 4), (2 : Fin 4))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms653.assocCAB) ((1 : Fin 2), (0 : Fin 4), (3 : Fin 4))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms653.assocCAB) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 4))) = rows_assocCAB ((1 : Fin 2), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms653.assocCAB) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 4))) = rows_assocCAB ((1 : Fin 2), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms653.assocCAB) ((1 : Fin 2), (1 : Fin 4), (2 : Fin 4))) = rows_assocCAB ((1 : Fin 2), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms653.assocCAB) ((1 : Fin 2), (1 : Fin 4), (3 : Fin 4))) = rows_assocCAB ((1 : Fin 2), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_2_0 : (tripleIndices 4 2 4).map ((HexagonAtoms653.assocCAB) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 4))) = rows_assocCAB ((1 : Fin 2), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_2_1 : (tripleIndices 4 2 4).map ((HexagonAtoms653.assocCAB) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 4))) = rows_assocCAB ((1 : Fin 2), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_2_2 : (tripleIndices 4 2 4).map ((HexagonAtoms653.assocCAB) ((1 : Fin 2), (2 : Fin 4), (2 : Fin 4))) = rows_assocCAB ((1 : Fin 2), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_2_3 : (tripleIndices 4 2 4).map ((HexagonAtoms653.assocCAB) ((1 : Fin 2), (2 : Fin 4), (3 : Fin 4))) = rows_assocCAB ((1 : Fin 2), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_3_0 : (tripleIndices 4 2 4).map ((HexagonAtoms653.assocCAB) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 4))) = rows_assocCAB ((1 : Fin 2), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_3_1 : (tripleIndices 4 2 4).map ((HexagonAtoms653.assocCAB) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 4))) = rows_assocCAB ((1 : Fin 2), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_3_2 : (tripleIndices 4 2 4).map ((HexagonAtoms653.assocCAB) ((1 : Fin 2), (3 : Fin 4), (2 : Fin 4))) = rows_assocCAB ((1 : Fin 2), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_3_3 : (tripleIndices 4 2 4).map ((HexagonAtoms653.assocCAB) ((1 : Fin 2), (3 : Fin 4), (3 : Fin 4))) = rows_assocCAB ((1 : Fin 2), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocCAB_data (r : RightIndex 3 6 5) : (tripleIndices 4 2 4).map ((HexagonAtoms653.assocCAB) r) = rows_assocCAB r := by
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
  · exact rows_assocCAB_eq_1_0_0
  · exact rows_assocCAB_eq_1_0_1
  · exact rows_assocCAB_eq_1_0_2
  · exact rows_assocCAB_eq_1_0_3
  · exact rows_assocCAB_eq_1_1_0
  · exact rows_assocCAB_eq_1_1_1
  · exact rows_assocCAB_eq_1_1_2
  · exact rows_assocCAB_eq_1_1_3
  · exact rows_assocCAB_eq_1_2_0
  · exact rows_assocCAB_eq_1_2_1
  · exact rows_assocCAB_eq_1_2_2
  · exact rows_assocCAB_eq_1_2_3
  · exact rows_assocCAB_eq_1_3_0
  · exact rows_assocCAB_eq_1_3_1
  · exact rows_assocCAB_eq_1_3_2
  · exact rows_assocCAB_eq_1_3_3

private def cols_right0Data : List (List ℤ) := [decodeIntegerRow 32 3 1 957017128647724,
    decodeIntegerRow 32 3 1 992608693252844,
    decodeIntegerRow 32 3 1 1133280024975436,
    decodeIntegerRow 32 3 1 1543995162959116,
    decodeIntegerRow 32 3 1 957007840082560,
    decodeIntegerRow 32 3 1 992588518676480,
    decodeIntegerRow 32 3 1 1133217005284480,
    decodeIntegerRow 32 3 1 1543806959388160,
    decodeIntegerRow 32 3 1 1131522685283200,
    decodeIntegerRow 32 3 1 308648453296000,
    decodeIntegerRow 32 3 1 941758960071040,
    decodeIntegerRow 32 3 1 855348684666240,
    decodeIntegerRow 32 3 1 1131585190539268,
    decodeIntegerRow 32 3 1 308460083915452,
    decodeIntegerRow 32 3 1 941763618722212,
    decodeIntegerRow 32 3 1 855327017803548,
    decodeIntegerRow 32 3 1 1133217004576000,
    decodeIntegerRow 32 3 1 309213226157440,
    decodeIntegerRow 32 3 1 957007830557440,
    decodeIntegerRow 32 3 1 860431641468800,
    decodeIntegerRow 32 3 1 719740163167708,
    decodeIntegerRow 32 3 1 1543995159651868,
    decodeIntegerRow 32 3 1 896003050676092,
    decodeIntegerRow 32 3 1 992608664537532,
    decodeIntegerRow 32 3 1 941763609115444,
    decodeIntegerRow 32 3 1 997693199737356,
    decodeIntegerRow 32 3 1 1131585189121876,
    decodeIntegerRow 32 3 1 1544560108007404,
    decodeIntegerRow 32 3 1 911261219176960,
    decodeIntegerRow 32 3 1 855348713346560,
    decodeIntegerRow 32 3 1 721497502151680,
    decodeIntegerRow 32 3 1 308648456366080]

def cols_right0 (r : LeftIndex 6 5 3) : List ℤ := cols_right0Data.getD (leftPosition 6 5 3 r) []

private theorem cols_right0_eq_0_0_0 : (tripleIndices 8 1 4).map (fun j => (right0Middle6 5 3) j ((0 : Fin 2), (0 : Fin 4), (0 : Fin 4))) = cols_right0 ((0 : Fin 2), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_1 : (tripleIndices 8 1 4).map (fun j => (right0Middle6 5 3) j ((0 : Fin 2), (0 : Fin 4), (1 : Fin 4))) = cols_right0 ((0 : Fin 2), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_2 : (tripleIndices 8 1 4).map (fun j => (right0Middle6 5 3) j ((0 : Fin 2), (0 : Fin 4), (2 : Fin 4))) = cols_right0 ((0 : Fin 2), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_3 : (tripleIndices 8 1 4).map (fun j => (right0Middle6 5 3) j ((0 : Fin 2), (0 : Fin 4), (3 : Fin 4))) = cols_right0 ((0 : Fin 2), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_0 : (tripleIndices 8 1 4).map (fun j => (right0Middle6 5 3) j ((0 : Fin 2), (1 : Fin 4), (0 : Fin 4))) = cols_right0 ((0 : Fin 2), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_1 : (tripleIndices 8 1 4).map (fun j => (right0Middle6 5 3) j ((0 : Fin 2), (1 : Fin 4), (1 : Fin 4))) = cols_right0 ((0 : Fin 2), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_2 : (tripleIndices 8 1 4).map (fun j => (right0Middle6 5 3) j ((0 : Fin 2), (1 : Fin 4), (2 : Fin 4))) = cols_right0 ((0 : Fin 2), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_3 : (tripleIndices 8 1 4).map (fun j => (right0Middle6 5 3) j ((0 : Fin 2), (1 : Fin 4), (3 : Fin 4))) = cols_right0 ((0 : Fin 2), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_2_0 : (tripleIndices 8 1 4).map (fun j => (right0Middle6 5 3) j ((0 : Fin 2), (2 : Fin 4), (0 : Fin 4))) = cols_right0 ((0 : Fin 2), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_2_1 : (tripleIndices 8 1 4).map (fun j => (right0Middle6 5 3) j ((0 : Fin 2), (2 : Fin 4), (1 : Fin 4))) = cols_right0 ((0 : Fin 2), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_2_2 : (tripleIndices 8 1 4).map (fun j => (right0Middle6 5 3) j ((0 : Fin 2), (2 : Fin 4), (2 : Fin 4))) = cols_right0 ((0 : Fin 2), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_2_3 : (tripleIndices 8 1 4).map (fun j => (right0Middle6 5 3) j ((0 : Fin 2), (2 : Fin 4), (3 : Fin 4))) = cols_right0 ((0 : Fin 2), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_3_0 : (tripleIndices 8 1 4).map (fun j => (right0Middle6 5 3) j ((0 : Fin 2), (3 : Fin 4), (0 : Fin 4))) = cols_right0 ((0 : Fin 2), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_3_1 : (tripleIndices 8 1 4).map (fun j => (right0Middle6 5 3) j ((0 : Fin 2), (3 : Fin 4), (1 : Fin 4))) = cols_right0 ((0 : Fin 2), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_3_2 : (tripleIndices 8 1 4).map (fun j => (right0Middle6 5 3) j ((0 : Fin 2), (3 : Fin 4), (2 : Fin 4))) = cols_right0 ((0 : Fin 2), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_3_3 : (tripleIndices 8 1 4).map (fun j => (right0Middle6 5 3) j ((0 : Fin 2), (3 : Fin 4), (3 : Fin 4))) = cols_right0 ((0 : Fin 2), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_0 : (tripleIndices 8 1 4).map (fun j => (right0Middle6 5 3) j ((1 : Fin 2), (0 : Fin 4), (0 : Fin 4))) = cols_right0 ((1 : Fin 2), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_1 : (tripleIndices 8 1 4).map (fun j => (right0Middle6 5 3) j ((1 : Fin 2), (0 : Fin 4), (1 : Fin 4))) = cols_right0 ((1 : Fin 2), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_2 : (tripleIndices 8 1 4).map (fun j => (right0Middle6 5 3) j ((1 : Fin 2), (0 : Fin 4), (2 : Fin 4))) = cols_right0 ((1 : Fin 2), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_3 : (tripleIndices 8 1 4).map (fun j => (right0Middle6 5 3) j ((1 : Fin 2), (0 : Fin 4), (3 : Fin 4))) = cols_right0 ((1 : Fin 2), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_0 : (tripleIndices 8 1 4).map (fun j => (right0Middle6 5 3) j ((1 : Fin 2), (1 : Fin 4), (0 : Fin 4))) = cols_right0 ((1 : Fin 2), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_1 : (tripleIndices 8 1 4).map (fun j => (right0Middle6 5 3) j ((1 : Fin 2), (1 : Fin 4), (1 : Fin 4))) = cols_right0 ((1 : Fin 2), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_2 : (tripleIndices 8 1 4).map (fun j => (right0Middle6 5 3) j ((1 : Fin 2), (1 : Fin 4), (2 : Fin 4))) = cols_right0 ((1 : Fin 2), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_3 : (tripleIndices 8 1 4).map (fun j => (right0Middle6 5 3) j ((1 : Fin 2), (1 : Fin 4), (3 : Fin 4))) = cols_right0 ((1 : Fin 2), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_2_0 : (tripleIndices 8 1 4).map (fun j => (right0Middle6 5 3) j ((1 : Fin 2), (2 : Fin 4), (0 : Fin 4))) = cols_right0 ((1 : Fin 2), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_2_1 : (tripleIndices 8 1 4).map (fun j => (right0Middle6 5 3) j ((1 : Fin 2), (2 : Fin 4), (1 : Fin 4))) = cols_right0 ((1 : Fin 2), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_2_2 : (tripleIndices 8 1 4).map (fun j => (right0Middle6 5 3) j ((1 : Fin 2), (2 : Fin 4), (2 : Fin 4))) = cols_right0 ((1 : Fin 2), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_2_3 : (tripleIndices 8 1 4).map (fun j => (right0Middle6 5 3) j ((1 : Fin 2), (2 : Fin 4), (3 : Fin 4))) = cols_right0 ((1 : Fin 2), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_3_0 : (tripleIndices 8 1 4).map (fun j => (right0Middle6 5 3) j ((1 : Fin 2), (3 : Fin 4), (0 : Fin 4))) = cols_right0 ((1 : Fin 2), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_3_1 : (tripleIndices 8 1 4).map (fun j => (right0Middle6 5 3) j ((1 : Fin 2), (3 : Fin 4), (1 : Fin 4))) = cols_right0 ((1 : Fin 2), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_3_2 : (tripleIndices 8 1 4).map (fun j => (right0Middle6 5 3) j ((1 : Fin 2), (3 : Fin 4), (2 : Fin 4))) = cols_right0 ((1 : Fin 2), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_3_3 : (tripleIndices 8 1 4).map (fun j => (right0Middle6 5 3) j ((1 : Fin 2), (3 : Fin 4), (3 : Fin 4))) = cols_right0 ((1 : Fin 2), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right0_data (r : LeftIndex 6 5 3) : (tripleIndices 8 1 4).map (fun j => (right0Middle6 5 3) j r) = cols_right0 r := by
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
  · exact cols_right0_eq_1_0_0
  · exact cols_right0_eq_1_0_1
  · exact cols_right0_eq_1_0_2
  · exact cols_right0_eq_1_0_3
  · exact cols_right0_eq_1_1_0
  · exact cols_right0_eq_1_1_1
  · exact cols_right0_eq_1_1_2
  · exact cols_right0_eq_1_1_3
  · exact cols_right0_eq_1_2_0
  · exact cols_right0_eq_1_2_1
  · exact cols_right0_eq_1_2_2
  · exact cols_right0_eq_1_2_3
  · exact cols_right0_eq_1_3_0
  · exact cols_right0_eq_1_3_1
  · exact cols_right0_eq_1_3_2
  · exact cols_right0_eq_1_3_3

private def cols_left0Data : List (List ℤ) := [decodeIntegerRow 32 3 1 957017128647724,
    decodeIntegerRow 32 3 1 992608693252844,
    decodeIntegerRow 32 3 1 1133280024975436,
    decodeIntegerRow 32 3 1 1543995162959116,
    decodeIntegerRow 32 3 1 957007840082560,
    decodeIntegerRow 32 3 1 992588518676480,
    decodeIntegerRow 32 3 1 1133217005284480,
    decodeIntegerRow 32 3 1 1543806959388160,
    decodeIntegerRow 32 3 1 1131522685283200,
    decodeIntegerRow 32 3 1 308648453296000,
    decodeIntegerRow 32 3 1 941758960071040,
    decodeIntegerRow 32 3 1 855348684666240,
    decodeIntegerRow 32 3 1 1131585190539268,
    decodeIntegerRow 32 3 1 308460083915452,
    decodeIntegerRow 32 3 1 941763618722212,
    decodeIntegerRow 32 3 1 855327017803548,
    decodeIntegerRow 32 3 1 1133217004576000,
    decodeIntegerRow 32 3 1 309213226157440,
    decodeIntegerRow 32 3 1 957007830557440,
    decodeIntegerRow 32 3 1 860431641468800,
    decodeIntegerRow 32 3 1 719740163167708,
    decodeIntegerRow 32 3 1 1543995159651868,
    decodeIntegerRow 32 3 1 896003050676092,
    decodeIntegerRow 32 3 1 992608664537532,
    decodeIntegerRow 32 3 1 941763609115444,
    decodeIntegerRow 32 3 1 997693199737356,
    decodeIntegerRow 32 3 1 1131585189121876,
    decodeIntegerRow 32 3 1 1544560108007404,
    decodeIntegerRow 32 3 1 911261219176960,
    decodeIntegerRow 32 3 1 855348713346560,
    decodeIntegerRow 32 3 1 721497502151680,
    decodeIntegerRow 32 3 1 308648456366080]

def cols_left0 (r : LeftIndex 6 5 3) : List ℤ := cols_left0Data.getD (leftPosition 6 5 3 r) []

private theorem cols_left0_eq_0_0_0 : (tripleIndices 8 1 4).map (fun j => (left0Middle6 5 3) j ((0 : Fin 2), (0 : Fin 4), (0 : Fin 4))) = cols_left0 ((0 : Fin 2), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_1 : (tripleIndices 8 1 4).map (fun j => (left0Middle6 5 3) j ((0 : Fin 2), (0 : Fin 4), (1 : Fin 4))) = cols_left0 ((0 : Fin 2), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_2 : (tripleIndices 8 1 4).map (fun j => (left0Middle6 5 3) j ((0 : Fin 2), (0 : Fin 4), (2 : Fin 4))) = cols_left0 ((0 : Fin 2), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_3 : (tripleIndices 8 1 4).map (fun j => (left0Middle6 5 3) j ((0 : Fin 2), (0 : Fin 4), (3 : Fin 4))) = cols_left0 ((0 : Fin 2), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_0 : (tripleIndices 8 1 4).map (fun j => (left0Middle6 5 3) j ((0 : Fin 2), (1 : Fin 4), (0 : Fin 4))) = cols_left0 ((0 : Fin 2), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_1 : (tripleIndices 8 1 4).map (fun j => (left0Middle6 5 3) j ((0 : Fin 2), (1 : Fin 4), (1 : Fin 4))) = cols_left0 ((0 : Fin 2), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_2 : (tripleIndices 8 1 4).map (fun j => (left0Middle6 5 3) j ((0 : Fin 2), (1 : Fin 4), (2 : Fin 4))) = cols_left0 ((0 : Fin 2), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_3 : (tripleIndices 8 1 4).map (fun j => (left0Middle6 5 3) j ((0 : Fin 2), (1 : Fin 4), (3 : Fin 4))) = cols_left0 ((0 : Fin 2), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_2_0 : (tripleIndices 8 1 4).map (fun j => (left0Middle6 5 3) j ((0 : Fin 2), (2 : Fin 4), (0 : Fin 4))) = cols_left0 ((0 : Fin 2), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_2_1 : (tripleIndices 8 1 4).map (fun j => (left0Middle6 5 3) j ((0 : Fin 2), (2 : Fin 4), (1 : Fin 4))) = cols_left0 ((0 : Fin 2), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_2_2 : (tripleIndices 8 1 4).map (fun j => (left0Middle6 5 3) j ((0 : Fin 2), (2 : Fin 4), (2 : Fin 4))) = cols_left0 ((0 : Fin 2), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_2_3 : (tripleIndices 8 1 4).map (fun j => (left0Middle6 5 3) j ((0 : Fin 2), (2 : Fin 4), (3 : Fin 4))) = cols_left0 ((0 : Fin 2), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_3_0 : (tripleIndices 8 1 4).map (fun j => (left0Middle6 5 3) j ((0 : Fin 2), (3 : Fin 4), (0 : Fin 4))) = cols_left0 ((0 : Fin 2), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_3_1 : (tripleIndices 8 1 4).map (fun j => (left0Middle6 5 3) j ((0 : Fin 2), (3 : Fin 4), (1 : Fin 4))) = cols_left0 ((0 : Fin 2), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_3_2 : (tripleIndices 8 1 4).map (fun j => (left0Middle6 5 3) j ((0 : Fin 2), (3 : Fin 4), (2 : Fin 4))) = cols_left0 ((0 : Fin 2), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_3_3 : (tripleIndices 8 1 4).map (fun j => (left0Middle6 5 3) j ((0 : Fin 2), (3 : Fin 4), (3 : Fin 4))) = cols_left0 ((0 : Fin 2), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_0 : (tripleIndices 8 1 4).map (fun j => (left0Middle6 5 3) j ((1 : Fin 2), (0 : Fin 4), (0 : Fin 4))) = cols_left0 ((1 : Fin 2), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_1 : (tripleIndices 8 1 4).map (fun j => (left0Middle6 5 3) j ((1 : Fin 2), (0 : Fin 4), (1 : Fin 4))) = cols_left0 ((1 : Fin 2), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_2 : (tripleIndices 8 1 4).map (fun j => (left0Middle6 5 3) j ((1 : Fin 2), (0 : Fin 4), (2 : Fin 4))) = cols_left0 ((1 : Fin 2), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_3 : (tripleIndices 8 1 4).map (fun j => (left0Middle6 5 3) j ((1 : Fin 2), (0 : Fin 4), (3 : Fin 4))) = cols_left0 ((1 : Fin 2), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_0 : (tripleIndices 8 1 4).map (fun j => (left0Middle6 5 3) j ((1 : Fin 2), (1 : Fin 4), (0 : Fin 4))) = cols_left0 ((1 : Fin 2), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_1 : (tripleIndices 8 1 4).map (fun j => (left0Middle6 5 3) j ((1 : Fin 2), (1 : Fin 4), (1 : Fin 4))) = cols_left0 ((1 : Fin 2), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_2 : (tripleIndices 8 1 4).map (fun j => (left0Middle6 5 3) j ((1 : Fin 2), (1 : Fin 4), (2 : Fin 4))) = cols_left0 ((1 : Fin 2), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_3 : (tripleIndices 8 1 4).map (fun j => (left0Middle6 5 3) j ((1 : Fin 2), (1 : Fin 4), (3 : Fin 4))) = cols_left0 ((1 : Fin 2), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_2_0 : (tripleIndices 8 1 4).map (fun j => (left0Middle6 5 3) j ((1 : Fin 2), (2 : Fin 4), (0 : Fin 4))) = cols_left0 ((1 : Fin 2), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_2_1 : (tripleIndices 8 1 4).map (fun j => (left0Middle6 5 3) j ((1 : Fin 2), (2 : Fin 4), (1 : Fin 4))) = cols_left0 ((1 : Fin 2), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_2_2 : (tripleIndices 8 1 4).map (fun j => (left0Middle6 5 3) j ((1 : Fin 2), (2 : Fin 4), (2 : Fin 4))) = cols_left0 ((1 : Fin 2), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_2_3 : (tripleIndices 8 1 4).map (fun j => (left0Middle6 5 3) j ((1 : Fin 2), (2 : Fin 4), (3 : Fin 4))) = cols_left0 ((1 : Fin 2), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_3_0 : (tripleIndices 8 1 4).map (fun j => (left0Middle6 5 3) j ((1 : Fin 2), (3 : Fin 4), (0 : Fin 4))) = cols_left0 ((1 : Fin 2), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_3_1 : (tripleIndices 8 1 4).map (fun j => (left0Middle6 5 3) j ((1 : Fin 2), (3 : Fin 4), (1 : Fin 4))) = cols_left0 ((1 : Fin 2), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_3_2 : (tripleIndices 8 1 4).map (fun j => (left0Middle6 5 3) j ((1 : Fin 2), (3 : Fin 4), (2 : Fin 4))) = cols_left0 ((1 : Fin 2), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_3_3 : (tripleIndices 8 1 4).map (fun j => (left0Middle6 5 3) j ((1 : Fin 2), (3 : Fin 4), (3 : Fin 4))) = cols_left0 ((1 : Fin 2), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_left0_data (r : LeftIndex 6 5 3) : (tripleIndices 8 1 4).map (fun j => (left0Middle6 5 3) j r) = cols_left0 r := by
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
  · exact cols_left0_eq_1_0_0
  · exact cols_left0_eq_1_0_1
  · exact cols_left0_eq_1_0_2
  · exact cols_left0_eq_1_0_3
  · exact cols_left0_eq_1_1_0
  · exact cols_left0_eq_1_1_1
  · exact cols_left0_eq_1_1_2
  · exact cols_left0_eq_1_1_3
  · exact cols_left0_eq_1_2_0
  · exact cols_left0_eq_1_2_1
  · exact cols_left0_eq_1_2_2
  · exact cols_left0_eq_1_2_3
  · exact cols_left0_eq_1_3_0
  · exact cols_left0_eq_1_3_1
  · exact cols_left0_eq_1_3_2
  · exact cols_left0_eq_1_3_3

private def cols_right2Data : List (List ℤ) := [decodeIntegerRow 32 9 4 1867566032834895642291413411200,
    decodeIntegerRow 32 9 4 188666786303241657017046289280,
    decodeIntegerRow 32 9 4 192853638270965498283714672000,
    decodeIntegerRow 32 9 4 1528436765757814101128058436480,
    decodeIntegerRow 32 9 4 1566117796211135972887424414224,
    decodeIntegerRow 32 9 4 3245016963183027194093249468816,
    decodeIntegerRow 32 9 4 3240830253022313267266598620944,
    decodeIntegerRow 32 9 4 1905247061537513687946581642896,
    decodeIntegerRow 32 9 4 1716818937411317291988701803024,
    decodeIntegerRow 32 9 4 1717074828154643892832997923216,
    decodeIntegerRow 32 9 4 1717074190033907738723359657744,
    decodeIntegerRow 32 9 4 1716870626066297667586573553296,
    decodeIntegerRow 32 9 4 1716818937409983117452732256640,
    decodeIntegerRow 32 9 4 1717074828165435882412832728960,
    decodeIntegerRow 32 9 4 1717074190023086100820426695040,
    decodeIntegerRow 32 9 4 1716870626065230327957790168960,
    decodeIntegerRow 32 9 4 192853567270199217642643324800,
    decodeIntegerRow 32 9 4 1905247061537513687921786730880,
    decodeIntegerRow 32 9 4 1867566024081376511801418313600,
    decodeIntegerRow 32 9 4 3245016963183027194343953566080,
    decodeIntegerRow 32 9 4 3240830182021546986122741572464,
    decodeIntegerRow 32 9 4 1528436765757814101152853347056,
    decodeIntegerRow 32 9 4 1566117787457616842335442038384,
    decodeIntegerRow 32 9 4 188666786303241656766342180336,
    decodeIntegerRow 32 9 4 1716609630269428033225877232016,
    decodeIntegerRow 32 9 4 1716870626065230165278381879824,
    decodeIntegerRow 32 9 4 1716864882882529570554386878096,
    decodeIntegerRow 32 9 4 1717074828165437527282491510544,
    decodeIntegerRow 32 9 4 1716609630258606395323020691840,
    decodeIntegerRow 32 9 4 1716870626066297504907155816320,
    decodeIntegerRow 32 9 4 1716864882881195396018409773440,
    decodeIntegerRow 32 9 4 1717074828154645537702580072320]

def cols_right2 (r : LeftIndex 6 5 3) : List ℤ := cols_right2Data.getD (leftPosition 6 5 3 r) []

private theorem cols_right2_eq_0_0_0 : (tripleIndices 4 2 4).map (fun j => (right2Middle6 5 3) j ((0 : Fin 2), (0 : Fin 4), (0 : Fin 4))) = cols_right2 ((0 : Fin 2), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_1 : (tripleIndices 4 2 4).map (fun j => (right2Middle6 5 3) j ((0 : Fin 2), (0 : Fin 4), (1 : Fin 4))) = cols_right2 ((0 : Fin 2), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_2 : (tripleIndices 4 2 4).map (fun j => (right2Middle6 5 3) j ((0 : Fin 2), (0 : Fin 4), (2 : Fin 4))) = cols_right2 ((0 : Fin 2), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_3 : (tripleIndices 4 2 4).map (fun j => (right2Middle6 5 3) j ((0 : Fin 2), (0 : Fin 4), (3 : Fin 4))) = cols_right2 ((0 : Fin 2), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_0 : (tripleIndices 4 2 4).map (fun j => (right2Middle6 5 3) j ((0 : Fin 2), (1 : Fin 4), (0 : Fin 4))) = cols_right2 ((0 : Fin 2), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_1 : (tripleIndices 4 2 4).map (fun j => (right2Middle6 5 3) j ((0 : Fin 2), (1 : Fin 4), (1 : Fin 4))) = cols_right2 ((0 : Fin 2), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_2 : (tripleIndices 4 2 4).map (fun j => (right2Middle6 5 3) j ((0 : Fin 2), (1 : Fin 4), (2 : Fin 4))) = cols_right2 ((0 : Fin 2), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_3 : (tripleIndices 4 2 4).map (fun j => (right2Middle6 5 3) j ((0 : Fin 2), (1 : Fin 4), (3 : Fin 4))) = cols_right2 ((0 : Fin 2), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_2_0 : (tripleIndices 4 2 4).map (fun j => (right2Middle6 5 3) j ((0 : Fin 2), (2 : Fin 4), (0 : Fin 4))) = cols_right2 ((0 : Fin 2), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_2_1 : (tripleIndices 4 2 4).map (fun j => (right2Middle6 5 3) j ((0 : Fin 2), (2 : Fin 4), (1 : Fin 4))) = cols_right2 ((0 : Fin 2), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_2_2 : (tripleIndices 4 2 4).map (fun j => (right2Middle6 5 3) j ((0 : Fin 2), (2 : Fin 4), (2 : Fin 4))) = cols_right2 ((0 : Fin 2), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_2_3 : (tripleIndices 4 2 4).map (fun j => (right2Middle6 5 3) j ((0 : Fin 2), (2 : Fin 4), (3 : Fin 4))) = cols_right2 ((0 : Fin 2), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_3_0 : (tripleIndices 4 2 4).map (fun j => (right2Middle6 5 3) j ((0 : Fin 2), (3 : Fin 4), (0 : Fin 4))) = cols_right2 ((0 : Fin 2), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_3_1 : (tripleIndices 4 2 4).map (fun j => (right2Middle6 5 3) j ((0 : Fin 2), (3 : Fin 4), (1 : Fin 4))) = cols_right2 ((0 : Fin 2), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_3_2 : (tripleIndices 4 2 4).map (fun j => (right2Middle6 5 3) j ((0 : Fin 2), (3 : Fin 4), (2 : Fin 4))) = cols_right2 ((0 : Fin 2), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_3_3 : (tripleIndices 4 2 4).map (fun j => (right2Middle6 5 3) j ((0 : Fin 2), (3 : Fin 4), (3 : Fin 4))) = cols_right2 ((0 : Fin 2), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_0 : (tripleIndices 4 2 4).map (fun j => (right2Middle6 5 3) j ((1 : Fin 2), (0 : Fin 4), (0 : Fin 4))) = cols_right2 ((1 : Fin 2), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_1 : (tripleIndices 4 2 4).map (fun j => (right2Middle6 5 3) j ((1 : Fin 2), (0 : Fin 4), (1 : Fin 4))) = cols_right2 ((1 : Fin 2), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_2 : (tripleIndices 4 2 4).map (fun j => (right2Middle6 5 3) j ((1 : Fin 2), (0 : Fin 4), (2 : Fin 4))) = cols_right2 ((1 : Fin 2), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_3 : (tripleIndices 4 2 4).map (fun j => (right2Middle6 5 3) j ((1 : Fin 2), (0 : Fin 4), (3 : Fin 4))) = cols_right2 ((1 : Fin 2), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_0 : (tripleIndices 4 2 4).map (fun j => (right2Middle6 5 3) j ((1 : Fin 2), (1 : Fin 4), (0 : Fin 4))) = cols_right2 ((1 : Fin 2), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_1 : (tripleIndices 4 2 4).map (fun j => (right2Middle6 5 3) j ((1 : Fin 2), (1 : Fin 4), (1 : Fin 4))) = cols_right2 ((1 : Fin 2), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_2 : (tripleIndices 4 2 4).map (fun j => (right2Middle6 5 3) j ((1 : Fin 2), (1 : Fin 4), (2 : Fin 4))) = cols_right2 ((1 : Fin 2), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_3 : (tripleIndices 4 2 4).map (fun j => (right2Middle6 5 3) j ((1 : Fin 2), (1 : Fin 4), (3 : Fin 4))) = cols_right2 ((1 : Fin 2), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_2_0 : (tripleIndices 4 2 4).map (fun j => (right2Middle6 5 3) j ((1 : Fin 2), (2 : Fin 4), (0 : Fin 4))) = cols_right2 ((1 : Fin 2), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_2_1 : (tripleIndices 4 2 4).map (fun j => (right2Middle6 5 3) j ((1 : Fin 2), (2 : Fin 4), (1 : Fin 4))) = cols_right2 ((1 : Fin 2), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_2_2 : (tripleIndices 4 2 4).map (fun j => (right2Middle6 5 3) j ((1 : Fin 2), (2 : Fin 4), (2 : Fin 4))) = cols_right2 ((1 : Fin 2), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_2_3 : (tripleIndices 4 2 4).map (fun j => (right2Middle6 5 3) j ((1 : Fin 2), (2 : Fin 4), (3 : Fin 4))) = cols_right2 ((1 : Fin 2), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_3_0 : (tripleIndices 4 2 4).map (fun j => (right2Middle6 5 3) j ((1 : Fin 2), (3 : Fin 4), (0 : Fin 4))) = cols_right2 ((1 : Fin 2), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_3_1 : (tripleIndices 4 2 4).map (fun j => (right2Middle6 5 3) j ((1 : Fin 2), (3 : Fin 4), (1 : Fin 4))) = cols_right2 ((1 : Fin 2), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_3_2 : (tripleIndices 4 2 4).map (fun j => (right2Middle6 5 3) j ((1 : Fin 2), (3 : Fin 4), (2 : Fin 4))) = cols_right2 ((1 : Fin 2), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_3_3 : (tripleIndices 4 2 4).map (fun j => (right2Middle6 5 3) j ((1 : Fin 2), (3 : Fin 4), (3 : Fin 4))) = cols_right2 ((1 : Fin 2), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right2_data (r : LeftIndex 6 5 3) : (tripleIndices 4 2 4).map (fun j => (right2Middle6 5 3) j r) = cols_right2 r := by
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
  · exact cols_right2_eq_1_0_0
  · exact cols_right2_eq_1_0_1
  · exact cols_right2_eq_1_0_2
  · exact cols_right2_eq_1_0_3
  · exact cols_right2_eq_1_1_0
  · exact cols_right2_eq_1_1_1
  · exact cols_right2_eq_1_1_2
  · exact cols_right2_eq_1_1_3
  · exact cols_right2_eq_1_2_0
  · exact cols_right2_eq_1_2_1
  · exact cols_right2_eq_1_2_2
  · exact cols_right2_eq_1_2_3
  · exact cols_right2_eq_1_3_0
  · exact cols_right2_eq_1_3_1
  · exact cols_right2_eq_1_3_2
  · exact cols_right2_eq_1_3_3

theorem product0_eq : HexagonAtoms653.outerABC * HexagonAtoms653.assocABC = HexagonAtoms653.assocABC :=
  Matrix.one_mul (m := Fin 8 × Fin 1 × Fin 4) (n := Fin 2 × Fin 4 × Fin 4) _

theorem product1_eq : HexagonAtoms653.assocBAC * HexagonAtoms653.innerABC = HexagonAtoms653.assocBAC :=
  Matrix.mul_one (m := Fin 4 × Fin 2 × Fin 4) (n := Fin 2 × Fin 4 × Fin 4) _

theorem product2_eq : HexagonAtoms653.innerRightABC * HexagonAtoms653.assocABC = HexagonAtoms653.assocABC :=
  Matrix.one_mul (m := Fin 8 × Fin 1 × Fin 4) (n := Fin 2 × Fin 4 × Fin 4) _

theorem product3_eq : HexagonAtoms653.inverseACB * right0Middle6 5 3 = rowColumnMul rows_inverseACB cols_right0 :=
  (rowColumnMul_eq _ _ _ _ rows_inverseACB_data cols_right0_data).symm

theorem product4_eq : HexagonAtoms653.innerACB * right1Middle6 5 3 = right1Middle6 5 3 :=
  Matrix.one_mul (m := Fin 4 × Fin 2 × Fin 4) (n := Fin 2 × Fin 4 × Fin 4) _

theorem product5_eq : HexagonAtoms653.assocBCA * left0Middle6 5 3 = rowColumnMul rows_assocBCA cols_left0 :=
  (rowColumnMul_eq _ _ _ _ rows_assocBCA_data cols_left0_data).symm

theorem product6_eq : HexagonAtoms653.innerRightBAC * left1Middle6 5 3 = left1Middle6 5 3 :=
  Matrix.one_mul (m := Fin 4 × Fin 2 × Fin 4) (n := Fin 2 × Fin 4 × Fin 4) _

theorem product7_eq : HexagonAtoms653.assocCAB * right2Middle6 5 3 = rowColumnMul rows_assocCAB cols_right2 :=
  (rowColumnMul_eq _ _ _ _ rows_assocCAB_data cols_right2_data).symm

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn653
