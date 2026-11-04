import RMod.BrundanEllis.StackingReferenceHexagonAtoms437
import RMod.BrundanEllis.StackingReferenceHexagonMiddle4
import RMod.BrundanEllis.StackingReferenceRowColumnCheck

/-! Verified row and column lists. Each subsequent scalar product traverses
these lists directly, without repeated lookup into the original matrices. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn437
open Superfusion

private def rows_inverseACBData : List (List ℤ) := [decodeIntegerRow 16 3 1 36403682,
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

def rows_inverseACB (r : LeftIndex 4 7 3) : List ℤ := rows_inverseACBData.getD (leftPosition 4 7 3 r) []

private theorem rows_inverseACB_eq_0_0_0 : (tripleIndices 2 2 4).map ((HexagonAtoms437.inverseACB) ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4))) = rows_inverseACB ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_1 : (tripleIndices 2 2 4).map ((HexagonAtoms437.inverseACB) ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4))) = rows_inverseACB ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_2 : (tripleIndices 2 2 4).map ((HexagonAtoms437.inverseACB) ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4))) = rows_inverseACB ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_3 : (tripleIndices 2 2 4).map ((HexagonAtoms437.inverseACB) ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4))) = rows_inverseACB ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_0 : (tripleIndices 2 2 4).map ((HexagonAtoms437.inverseACB) ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4))) = rows_inverseACB ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_1 : (tripleIndices 2 2 4).map ((HexagonAtoms437.inverseACB) ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4))) = rows_inverseACB ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_2 : (tripleIndices 2 2 4).map ((HexagonAtoms437.inverseACB) ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4))) = rows_inverseACB ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_3 : (tripleIndices 2 2 4).map ((HexagonAtoms437.inverseACB) ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4))) = rows_inverseACB ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_2_0 : (tripleIndices 2 2 4).map ((HexagonAtoms437.inverseACB) ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4))) = rows_inverseACB ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_2_1 : (tripleIndices 2 2 4).map ((HexagonAtoms437.inverseACB) ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4))) = rows_inverseACB ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_2_2 : (tripleIndices 2 2 4).map ((HexagonAtoms437.inverseACB) ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4))) = rows_inverseACB ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_2_3 : (tripleIndices 2 2 4).map ((HexagonAtoms437.inverseACB) ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4))) = rows_inverseACB ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_3_0 : (tripleIndices 2 2 4).map ((HexagonAtoms437.inverseACB) ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4))) = rows_inverseACB ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_3_1 : (tripleIndices 2 2 4).map ((HexagonAtoms437.inverseACB) ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4))) = rows_inverseACB ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_3_2 : (tripleIndices 2 2 4).map ((HexagonAtoms437.inverseACB) ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4))) = rows_inverseACB ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_3_3 : (tripleIndices 2 2 4).map ((HexagonAtoms437.inverseACB) ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4))) = rows_inverseACB ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_inverseACB_data (r : LeftIndex 4 7 3) : (tripleIndices 2 2 4).map ((HexagonAtoms437.inverseACB) r) = rows_inverseACB r := by
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

private def rows_assocBCAData : List (List ℤ) := [decodeIntegerRow 16 3 1 21523282,
    decodeIntegerRow 16 3 1 21523118,
    decodeIntegerRow 16 3 1 21522658,
    decodeIntegerRow 16 3 1 21521182,
    decodeIntegerRow 16 3 1 21523444,
    decodeIntegerRow 16 3 1 21523604,
    decodeIntegerRow 16 3 1 21524116,
    decodeIntegerRow 16 3 1 21525556,
    decodeIntegerRow 16 3 1 7115404,
    decodeIntegerRow 16 3 1 26483476,
    decodeIntegerRow 16 3 1 19922476,
    decodeIntegerRow 16 3 1 22074484,
    decodeIntegerRow 16 3 1 35813218,
    decodeIntegerRow 16 3 1 16917538,
    decodeIntegerRow 16 3 1 23111122,
    decodeIntegerRow 16 3 1 21011602]

def rows_assocBCA (r : RightIndex 3 7 4) : List ℤ := rows_assocBCAData.getD (rightPosition 3 7 4 r) []

private theorem rows_assocBCA_eq_0_0_0 : (tripleIndices 2 2 4).map ((HexagonAtoms437.assocBCA) ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4))) = rows_assocBCA ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_1 : (tripleIndices 2 2 4).map ((HexagonAtoms437.assocBCA) ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4))) = rows_assocBCA ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_2 : (tripleIndices 2 2 4).map ((HexagonAtoms437.assocBCA) ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4))) = rows_assocBCA ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_3 : (tripleIndices 2 2 4).map ((HexagonAtoms437.assocBCA) ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4))) = rows_assocBCA ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_0 : (tripleIndices 2 2 4).map ((HexagonAtoms437.assocBCA) ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4))) = rows_assocBCA ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_1 : (tripleIndices 2 2 4).map ((HexagonAtoms437.assocBCA) ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4))) = rows_assocBCA ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_2 : (tripleIndices 2 2 4).map ((HexagonAtoms437.assocBCA) ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4))) = rows_assocBCA ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_3 : (tripleIndices 2 2 4).map ((HexagonAtoms437.assocBCA) ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4))) = rows_assocBCA ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_2_0 : (tripleIndices 2 2 4).map ((HexagonAtoms437.assocBCA) ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4))) = rows_assocBCA ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_2_1 : (tripleIndices 2 2 4).map ((HexagonAtoms437.assocBCA) ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4))) = rows_assocBCA ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_2_2 : (tripleIndices 2 2 4).map ((HexagonAtoms437.assocBCA) ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4))) = rows_assocBCA ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_2_3 : (tripleIndices 2 2 4).map ((HexagonAtoms437.assocBCA) ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4))) = rows_assocBCA ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_3_0 : (tripleIndices 2 2 4).map ((HexagonAtoms437.assocBCA) ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4))) = rows_assocBCA ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_3_1 : (tripleIndices 2 2 4).map ((HexagonAtoms437.assocBCA) ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4))) = rows_assocBCA ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_3_2 : (tripleIndices 2 2 4).map ((HexagonAtoms437.assocBCA) ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4))) = rows_assocBCA ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_3_3 : (tripleIndices 2 2 4).map ((HexagonAtoms437.assocBCA) ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4))) = rows_assocBCA ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocBCA_data (r : RightIndex 3 7 4) : (tripleIndices 2 2 4).map ((HexagonAtoms437.assocBCA) r) = rows_assocBCA r := by
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

private def rows_assocCABData : List (List ℤ) := [decodeIntegerRow 16 3 1 16683556,
    decodeIntegerRow 16 3 1 36048676,
    decodeIntegerRow 16 3 1 20985604,
    decodeIntegerRow 16 3 1 23137284,
    decodeIntegerRow 16 3 1 23097920,
    decodeIntegerRow 16 3 1 22048000,
    decodeIntegerRow 16 3 1 35694400,
    decodeIntegerRow 16 3 1 26245120,
    decodeIntegerRow 16 3 1 36050152,
    decodeIntegerRow 16 3 1 16679128,
    decodeIntegerRow 16 3 1 23137448,
    decodeIntegerRow 16 3 1 20985112,
    decodeIntegerRow 16 3 1 20998240,
    decodeIntegerRow 16 3 1 19948640,
    decodeIntegerRow 16 3 1 16797280,
    decodeIntegerRow 16 3 1 7350880]

def rows_assocCAB (r : RightIndex 7 4 3) : List ℤ := rows_assocCABData.getD (rightPosition 7 4 3 r) []

private theorem rows_assocCAB_eq_0_0_0 : (tripleIndices 1 4 4).map ((HexagonAtoms437.assocCAB) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_assocCAB ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_1 : (tripleIndices 1 4 4).map ((HexagonAtoms437.assocCAB) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_assocCAB ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_2 : (tripleIndices 1 4 4).map ((HexagonAtoms437.assocCAB) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_assocCAB ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_3 : (tripleIndices 1 4 4).map ((HexagonAtoms437.assocCAB) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_assocCAB ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_0 : (tripleIndices 1 4 4).map ((HexagonAtoms437.assocCAB) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_assocCAB ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_1 : (tripleIndices 1 4 4).map ((HexagonAtoms437.assocCAB) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_assocCAB ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_2 : (tripleIndices 1 4 4).map ((HexagonAtoms437.assocCAB) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_assocCAB ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_3 : (tripleIndices 1 4 4).map ((HexagonAtoms437.assocCAB) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_assocCAB ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_0 : (tripleIndices 1 4 4).map ((HexagonAtoms437.assocCAB) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_assocCAB ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_1 : (tripleIndices 1 4 4).map ((HexagonAtoms437.assocCAB) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_assocCAB ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_2 : (tripleIndices 1 4 4).map ((HexagonAtoms437.assocCAB) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_assocCAB ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_3 : (tripleIndices 1 4 4).map ((HexagonAtoms437.assocCAB) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_assocCAB ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_0 : (tripleIndices 1 4 4).map ((HexagonAtoms437.assocCAB) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_assocCAB ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_1 : (tripleIndices 1 4 4).map ((HexagonAtoms437.assocCAB) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_assocCAB ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_2 : (tripleIndices 1 4 4).map ((HexagonAtoms437.assocCAB) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_assocCAB ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_3 : (tripleIndices 1 4 4).map ((HexagonAtoms437.assocCAB) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_assocCAB ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocCAB_data (r : RightIndex 7 4 3) : (tripleIndices 1 4 4).map ((HexagonAtoms437.assocCAB) r) = rows_assocCAB r := by
  fin_cases r
  · exact rows_assocCAB_eq_0_0_0
  · exact rows_assocCAB_eq_0_0_1
  · exact rows_assocCAB_eq_0_0_2
  · exact rows_assocCAB_eq_0_0_3
  · exact rows_assocCAB_eq_1_0_0
  · exact rows_assocCAB_eq_1_0_1
  · exact rows_assocCAB_eq_1_0_2
  · exact rows_assocCAB_eq_1_0_3
  · exact rows_assocCAB_eq_2_0_0
  · exact rows_assocCAB_eq_2_0_1
  · exact rows_assocCAB_eq_2_0_2
  · exact rows_assocCAB_eq_2_0_3
  · exact rows_assocCAB_eq_3_0_0
  · exact rows_assocCAB_eq_3_0_1
  · exact rows_assocCAB_eq_3_0_2
  · exact rows_assocCAB_eq_3_0_3

private def cols_right0Data : List (List ℤ) := [decodeIntegerRow 16 3 1 21529930,
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

def cols_right0 (r : LeftIndex 4 3 7) : List ℤ := cols_right0Data.getD (leftPosition 4 3 7 r) []

private theorem cols_right0_eq_0_0_0 : (tripleIndices 2 2 4).map (fun j => (right0Middle4 3 7) j ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_right0 ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_1 : (tripleIndices 2 2 4).map (fun j => (right0Middle4 3 7) j ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_right0 ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_2 : (tripleIndices 2 2 4).map (fun j => (right0Middle4 3 7) j ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_right0 ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_3 : (tripleIndices 2 2 4).map (fun j => (right0Middle4 3 7) j ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_right0 ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_0 : (tripleIndices 2 2 4).map (fun j => (right0Middle4 3 7) j ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_right0 ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_1 : (tripleIndices 2 2 4).map (fun j => (right0Middle4 3 7) j ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_right0 ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_2 : (tripleIndices 2 2 4).map (fun j => (right0Middle4 3 7) j ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_right0 ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_3 : (tripleIndices 2 2 4).map (fun j => (right0Middle4 3 7) j ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_right0 ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_0 : (tripleIndices 2 2 4).map (fun j => (right0Middle4 3 7) j ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_right0 ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_1 : (tripleIndices 2 2 4).map (fun j => (right0Middle4 3 7) j ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_right0 ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_2 : (tripleIndices 2 2 4).map (fun j => (right0Middle4 3 7) j ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_right0 ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_3 : (tripleIndices 2 2 4).map (fun j => (right0Middle4 3 7) j ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_right0 ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_0 : (tripleIndices 2 2 4).map (fun j => (right0Middle4 3 7) j ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_right0 ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_1 : (tripleIndices 2 2 4).map (fun j => (right0Middle4 3 7) j ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_right0 ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_2 : (tripleIndices 2 2 4).map (fun j => (right0Middle4 3 7) j ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_right0 ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_3 : (tripleIndices 2 2 4).map (fun j => (right0Middle4 3 7) j ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_right0 ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right0_data (r : LeftIndex 4 3 7) : (tripleIndices 2 2 4).map (fun j => (right0Middle4 3 7) j r) = cols_right0 r := by
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

private def cols_left0Data : List (List ℤ) := [decodeIntegerRow 16 3 1 21529930,
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

def cols_left0 (r : LeftIndex 4 3 7) : List ℤ := cols_left0Data.getD (leftPosition 4 3 7 r) []

private theorem cols_left0_eq_0_0_0 : (tripleIndices 2 2 4).map (fun j => (left0Middle4 3 7) j ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_left0 ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_1 : (tripleIndices 2 2 4).map (fun j => (left0Middle4 3 7) j ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_left0 ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_2 : (tripleIndices 2 2 4).map (fun j => (left0Middle4 3 7) j ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_left0 ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_3 : (tripleIndices 2 2 4).map (fun j => (left0Middle4 3 7) j ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_left0 ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_0 : (tripleIndices 2 2 4).map (fun j => (left0Middle4 3 7) j ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_left0 ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_1 : (tripleIndices 2 2 4).map (fun j => (left0Middle4 3 7) j ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_left0 ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_2 : (tripleIndices 2 2 4).map (fun j => (left0Middle4 3 7) j ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_left0 ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_3 : (tripleIndices 2 2 4).map (fun j => (left0Middle4 3 7) j ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_left0 ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_0 : (tripleIndices 2 2 4).map (fun j => (left0Middle4 3 7) j ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_left0 ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_1 : (tripleIndices 2 2 4).map (fun j => (left0Middle4 3 7) j ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_left0 ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_2 : (tripleIndices 2 2 4).map (fun j => (left0Middle4 3 7) j ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_left0 ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_3 : (tripleIndices 2 2 4).map (fun j => (left0Middle4 3 7) j ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_left0 ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_0 : (tripleIndices 2 2 4).map (fun j => (left0Middle4 3 7) j ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_left0 ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_1 : (tripleIndices 2 2 4).map (fun j => (left0Middle4 3 7) j ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_left0 ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_2 : (tripleIndices 2 2 4).map (fun j => (left0Middle4 3 7) j ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_left0 ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_3 : (tripleIndices 2 2 4).map (fun j => (left0Middle4 3 7) j ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_left0 ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_left0_data (r : LeftIndex 4 3 7) : (tripleIndices 2 2 4).map (fun j => (left0Middle4 3 7) j r) = cols_left0 r := by
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

private def cols_right2Data : List (List ℤ) := [decodeIntegerRow 16 3 1 6460288,
    decodeIntegerRow 16 3 1 24749240,
    decodeIntegerRow 16 3 1 15069632,
    decodeIntegerRow 16 3 1 7535800,
    decodeIntegerRow 16 3 1 35169760,
    decodeIntegerRow 16 3 1 15227040,
    decodeIntegerRow 16 3 1 18376160,
    decodeIntegerRow 16 3 1 6827680,
    decodeIntegerRow 16 3 1 15065040,
    decodeIntegerRow 16 3 1 35511904,
    decodeIntegerRow 16 3 1 6458320,
    decodeIntegerRow 16 3 1 18293216,
    decodeIntegerRow 16 3 1 24674720,
    decodeIntegerRow 16 3 1 6825760,
    decodeIntegerRow 16 3 1 7876000,
    decodeIntegerRow 16 3 1 15222560]

def cols_right2 (r : LeftIndex 4 3 7) : List ℤ := cols_right2Data.getD (leftPosition 4 3 7 r) []

private theorem cols_right2_eq_0_0_0 : (tripleIndices 1 4 4).map (fun j => (right2Middle4 3 7) j ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_right2 ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_1 : (tripleIndices 1 4 4).map (fun j => (right2Middle4 3 7) j ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_right2 ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_2 : (tripleIndices 1 4 4).map (fun j => (right2Middle4 3 7) j ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_right2 ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_3 : (tripleIndices 1 4 4).map (fun j => (right2Middle4 3 7) j ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_right2 ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_0 : (tripleIndices 1 4 4).map (fun j => (right2Middle4 3 7) j ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_right2 ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_1 : (tripleIndices 1 4 4).map (fun j => (right2Middle4 3 7) j ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_right2 ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_2 : (tripleIndices 1 4 4).map (fun j => (right2Middle4 3 7) j ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_right2 ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_3 : (tripleIndices 1 4 4).map (fun j => (right2Middle4 3 7) j ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_right2 ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_0 : (tripleIndices 1 4 4).map (fun j => (right2Middle4 3 7) j ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_right2 ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_1 : (tripleIndices 1 4 4).map (fun j => (right2Middle4 3 7) j ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_right2 ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_2 : (tripleIndices 1 4 4).map (fun j => (right2Middle4 3 7) j ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_right2 ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_3 : (tripleIndices 1 4 4).map (fun j => (right2Middle4 3 7) j ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_right2 ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_0 : (tripleIndices 1 4 4).map (fun j => (right2Middle4 3 7) j ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_right2 ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_1 : (tripleIndices 1 4 4).map (fun j => (right2Middle4 3 7) j ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_right2 ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_2 : (tripleIndices 1 4 4).map (fun j => (right2Middle4 3 7) j ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_right2 ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_3 : (tripleIndices 1 4 4).map (fun j => (right2Middle4 3 7) j ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_right2 ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right2_data (r : LeftIndex 4 3 7) : (tripleIndices 1 4 4).map (fun j => (right2Middle4 3 7) j r) = cols_right2 r := by
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

theorem product0_eq : HexagonAtoms437.outerABC * HexagonAtoms437.assocABC = HexagonAtoms437.assocABC :=
  Matrix.one_mul (m := Fin 2 × Fin 2 × Fin 4) (n := Fin 4 × Fin 1 × Fin 4) _

theorem product1_eq : HexagonAtoms437.assocBAC * HexagonAtoms437.innerABC = HexagonAtoms437.assocBAC :=
  Matrix.mul_one (m := Fin 1 × Fin 4 × Fin 4) (n := Fin 4 × Fin 1 × Fin 4) _

theorem product2_eq : HexagonAtoms437.innerRightABC * HexagonAtoms437.assocABC = HexagonAtoms437.assocABC :=
  Matrix.one_mul (m := Fin 2 × Fin 2 × Fin 4) (n := Fin 4 × Fin 1 × Fin 4) _

theorem product3_eq : HexagonAtoms437.inverseACB * right0Middle4 3 7 = rowColumnMul rows_inverseACB cols_right0 :=
  (rowColumnMul_eq _ _ _ _ rows_inverseACB_data cols_right0_data).symm

theorem product4_eq : HexagonAtoms437.innerACB * right1Middle4 3 7 = right1Middle4 3 7 :=
  Matrix.one_mul (m := Fin 1 × Fin 4 × Fin 4) (n := Fin 4 × Fin 1 × Fin 4) _

theorem product5_eq : HexagonAtoms437.assocBCA * left0Middle4 3 7 = rowColumnMul rows_assocBCA cols_left0 :=
  (rowColumnMul_eq _ _ _ _ rows_assocBCA_data cols_left0_data).symm

theorem product6_eq : HexagonAtoms437.innerRightBAC * left1Middle4 3 7 = left1Middle4 3 7 :=
  Matrix.one_mul (m := Fin 1 × Fin 4 × Fin 4) (n := Fin 4 × Fin 1 × Fin 4) _

theorem product7_eq : HexagonAtoms437.assocCAB * right2Middle4 3 7 = rowColumnMul rows_assocCAB cols_right2 :=
  (rowColumnMul_eq _ _ _ _ rows_assocCAB_data cols_right2_data).symm

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn437
