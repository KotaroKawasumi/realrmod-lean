import RMod.BrundanEllis.StackingReferenceHexagonAtoms357
import RMod.BrundanEllis.StackingReferenceHexagonMiddle3
import RMod.BrundanEllis.StackingReferenceRowColumnCheck

/-! Verified row and column lists. Each subsequent scalar product traverses
these lists directly, without repeated lookup into the original matrices. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn357
open Superfusion

private def rows_inverseACBData : List (List ℤ) := [decodeIntegerRow 16 3 1 5515360,
    decodeIntegerRow 16 3 1 16014560,
    decodeIntegerRow 16 3 1 37400200,
    decodeIntegerRow 16 3 1 26638520,
    decodeIntegerRow 16 3 1 25619360,
    decodeIntegerRow 16 3 1 34226080,
    decodeIntegerRow 16 3 1 17112416,
    decodeIntegerRow 16 3 1 8715616,
    decodeIntegerRow 16 3 1 16403360,
    decodeIntegerRow 16 3 1 5644960,
    decodeIntegerRow 16 3 1 16009680,
    decodeIntegerRow 16 3 1 5513680,
    decodeIntegerRow 16 3 1 8716960,
    decodeIntegerRow 16 3 1 17116320,
    decodeIntegerRow 16 3 1 8821888,
    decodeIntegerRow 16 3 1 17431232]

def rows_inverseACB (r : LeftIndex 3 7 5) : List ℤ := rows_inverseACBData.getD (leftPosition 3 7 5 r) []

private theorem rows_inverseACB_eq_0_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms357.inverseACB) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms357.inverseACB) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_0 : (tripleIndices 2 4 2).map ((HexagonAtoms357.inverseACB) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = rows_inverseACB ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_1 : (tripleIndices 2 4 2).map ((HexagonAtoms357.inverseACB) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = rows_inverseACB ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_2_0 : (tripleIndices 2 4 2).map ((HexagonAtoms357.inverseACB) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = rows_inverseACB ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_2_1 : (tripleIndices 2 4 2).map ((HexagonAtoms357.inverseACB) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = rows_inverseACB ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_3_0 : (tripleIndices 2 4 2).map ((HexagonAtoms357.inverseACB) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = rows_inverseACB ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_3_1 : (tripleIndices 2 4 2).map ((HexagonAtoms357.inverseACB) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = rows_inverseACB ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms357.inverseACB) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms357.inverseACB) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_0 : (tripleIndices 2 4 2).map ((HexagonAtoms357.inverseACB) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = rows_inverseACB ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_1 : (tripleIndices 2 4 2).map ((HexagonAtoms357.inverseACB) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = rows_inverseACB ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_2_0 : (tripleIndices 2 4 2).map ((HexagonAtoms357.inverseACB) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = rows_inverseACB ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_2_1 : (tripleIndices 2 4 2).map ((HexagonAtoms357.inverseACB) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = rows_inverseACB ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_3_0 : (tripleIndices 2 4 2).map ((HexagonAtoms357.inverseACB) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = rows_inverseACB ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_3_1 : (tripleIndices 2 4 2).map ((HexagonAtoms357.inverseACB) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = rows_inverseACB ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_inverseACB_data (r : LeftIndex 3 7 5) : (tripleIndices 2 4 2).map ((HexagonAtoms357.inverseACB) r) = rows_inverseACB r := by
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

private def rows_assocBCAData : List (List ℤ) := [decodeIntegerRow 16 3 1 5515360,
    decodeIntegerRow 16 3 1 16014560,
    decodeIntegerRow 16 3 1 37400200,
    decodeIntegerRow 16 3 1 26638520,
    decodeIntegerRow 16 3 1 25619360,
    decodeIntegerRow 16 3 1 34226080,
    decodeIntegerRow 16 3 1 17112416,
    decodeIntegerRow 16 3 1 8715616,
    decodeIntegerRow 16 3 1 16403360,
    decodeIntegerRow 16 3 1 5644960,
    decodeIntegerRow 16 3 1 16009680,
    decodeIntegerRow 16 3 1 5513680,
    decodeIntegerRow 16 3 1 8716960,
    decodeIntegerRow 16 3 1 17116320,
    decodeIntegerRow 16 3 1 8821888,
    decodeIntegerRow 16 3 1 17431232]

def rows_assocBCA (r : RightIndex 5 7 3) : List ℤ := rows_assocBCAData.getD (rightPosition 5 7 3 r) []

private theorem rows_assocBCA_eq_0_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms357.assocBCA) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = rows_assocBCA ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms357.assocBCA) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = rows_assocBCA ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_0 : (tripleIndices 2 4 2).map ((HexagonAtoms357.assocBCA) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = rows_assocBCA ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_1 : (tripleIndices 2 4 2).map ((HexagonAtoms357.assocBCA) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = rows_assocBCA ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_2_0 : (tripleIndices 2 4 2).map ((HexagonAtoms357.assocBCA) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = rows_assocBCA ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_2_1 : (tripleIndices 2 4 2).map ((HexagonAtoms357.assocBCA) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = rows_assocBCA ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_3_0 : (tripleIndices 2 4 2).map ((HexagonAtoms357.assocBCA) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = rows_assocBCA ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_3_1 : (tripleIndices 2 4 2).map ((HexagonAtoms357.assocBCA) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = rows_assocBCA ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms357.assocBCA) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = rows_assocBCA ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms357.assocBCA) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = rows_assocBCA ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_0 : (tripleIndices 2 4 2).map ((HexagonAtoms357.assocBCA) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = rows_assocBCA ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_1 : (tripleIndices 2 4 2).map ((HexagonAtoms357.assocBCA) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = rows_assocBCA ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_2_0 : (tripleIndices 2 4 2).map ((HexagonAtoms357.assocBCA) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = rows_assocBCA ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_2_1 : (tripleIndices 2 4 2).map ((HexagonAtoms357.assocBCA) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = rows_assocBCA ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_3_0 : (tripleIndices 2 4 2).map ((HexagonAtoms357.assocBCA) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = rows_assocBCA ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_3_1 : (tripleIndices 2 4 2).map ((HexagonAtoms357.assocBCA) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = rows_assocBCA ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocBCA_data (r : RightIndex 5 7 3) : (tripleIndices 2 4 2).map ((HexagonAtoms357.assocBCA) r) = rows_assocBCA r := by
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

private def rows_assocCABData : List (List ℤ) := [decodeIntegerRow 16 3 1 8821888,
    decodeIntegerRow 16 3 1 17431232,
    decodeIntegerRow 16 3 1 5515360,
    decodeIntegerRow 16 3 1 16014560,
    decodeIntegerRow 16 3 1 8716960,
    decodeIntegerRow 16 3 1 17116320,
    decodeIntegerRow 16 3 1 37400200,
    decodeIntegerRow 16 3 1 26638520,
    decodeIntegerRow 16 3 1 25934304,
    decodeIntegerRow 16 3 1 34331104,
    decodeIntegerRow 16 3 1 16403360,
    decodeIntegerRow 16 3 1 5644960,
    decodeIntegerRow 16 3 1 17427360,
    decodeIntegerRow 16 3 1 8820640,
    decodeIntegerRow 16 3 1 16009680,
    decodeIntegerRow 16 3 1 5513680]

def rows_assocCAB (r : RightIndex 7 3 5) : List ℤ := rows_assocCABData.getD (rightPosition 7 3 5 r) []

private theorem rows_assocCAB_eq_0_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms357.assocCAB) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 2))) = rows_assocCAB ((0 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms357.assocCAB) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 2))) = rows_assocCAB ((0 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms357.assocCAB) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 2))) = rows_assocCAB ((1 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms357.assocCAB) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 2))) = rows_assocCAB ((1 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms357.assocCAB) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 2))) = rows_assocCAB ((2 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms357.assocCAB) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 2))) = rows_assocCAB ((2 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms357.assocCAB) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 2))) = rows_assocCAB ((3 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms357.assocCAB) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 2))) = rows_assocCAB ((3 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_4_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms357.assocCAB) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 2))) = rows_assocCAB ((4 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_4_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms357.assocCAB) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 2))) = rows_assocCAB ((4 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_5_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms357.assocCAB) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 2))) = rows_assocCAB ((5 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_5_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms357.assocCAB) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 2))) = rows_assocCAB ((5 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_6_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms357.assocCAB) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 2))) = rows_assocCAB ((6 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_6_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms357.assocCAB) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 2))) = rows_assocCAB ((6 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_7_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms357.assocCAB) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 2))) = rows_assocCAB ((7 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_7_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms357.assocCAB) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 2))) = rows_assocCAB ((7 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocCAB_data (r : RightIndex 7 3 5) : (tripleIndices 2 4 2).map ((HexagonAtoms357.assocCAB) r) = rows_assocCAB r := by
  fin_cases r
  · exact rows_assocCAB_eq_0_0_0
  · exact rows_assocCAB_eq_0_0_1
  · exact rows_assocCAB_eq_1_0_0
  · exact rows_assocCAB_eq_1_0_1
  · exact rows_assocCAB_eq_2_0_0
  · exact rows_assocCAB_eq_2_0_1
  · exact rows_assocCAB_eq_3_0_0
  · exact rows_assocCAB_eq_3_0_1
  · exact rows_assocCAB_eq_4_0_0
  · exact rows_assocCAB_eq_4_0_1
  · exact rows_assocCAB_eq_5_0_0
  · exact rows_assocCAB_eq_5_0_1
  · exact rows_assocCAB_eq_6_0_0
  · exact rows_assocCAB_eq_6_0_1
  · exact rows_assocCAB_eq_7_0_0
  · exact rows_assocCAB_eq_7_0_1

private def cols_right0Data : List (List ℤ) := [decodeIntegerRow 16 3 1 26483234,
    decodeIntegerRow 16 3 1 35931238,
    decodeIntegerRow 16 3 1 16917294,
    decodeIntegerRow 16 3 1 7233418,
    decodeIntegerRow 16 3 1 20974414,
    decodeIntegerRow 16 3 1 19923178,
    decodeIntegerRow 16 3 1 21009406,
    decodeIntegerRow 16 3 1 19934842,
    decodeIntegerRow 16 3 1 19936354,
    decodeIntegerRow 16 3 1 21013798,
    decodeIntegerRow 16 3 1 23124946,
    decodeIntegerRow 16 3 1 22076662,
    decodeIntegerRow 16 3 1 7233586,
    decodeIntegerRow 16 3 1 16917782,
    decodeIntegerRow 16 3 1 7115326,
    decodeIntegerRow 16 3 1 16563002]

def cols_right0 (r : LeftIndex 3 5 7) : List ℤ := cols_right0Data.getD (leftPosition 3 5 7 r) []

private theorem cols_right0_eq_0_0_0 : (tripleIndices 2 4 2).map (fun j => (right0Middle3 5 7) j ((0 : Fin 8), (0 : Fin 1), (0 : Fin 2))) = cols_right0 ((0 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_1 : (tripleIndices 2 4 2).map (fun j => (right0Middle3 5 7) j ((0 : Fin 8), (0 : Fin 1), (1 : Fin 2))) = cols_right0 ((0 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_0 : (tripleIndices 2 4 2).map (fun j => (right0Middle3 5 7) j ((1 : Fin 8), (0 : Fin 1), (0 : Fin 2))) = cols_right0 ((1 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_1 : (tripleIndices 2 4 2).map (fun j => (right0Middle3 5 7) j ((1 : Fin 8), (0 : Fin 1), (1 : Fin 2))) = cols_right0 ((1 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_0 : (tripleIndices 2 4 2).map (fun j => (right0Middle3 5 7) j ((2 : Fin 8), (0 : Fin 1), (0 : Fin 2))) = cols_right0 ((2 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_1 : (tripleIndices 2 4 2).map (fun j => (right0Middle3 5 7) j ((2 : Fin 8), (0 : Fin 1), (1 : Fin 2))) = cols_right0 ((2 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_0 : (tripleIndices 2 4 2).map (fun j => (right0Middle3 5 7) j ((3 : Fin 8), (0 : Fin 1), (0 : Fin 2))) = cols_right0 ((3 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_1 : (tripleIndices 2 4 2).map (fun j => (right0Middle3 5 7) j ((3 : Fin 8), (0 : Fin 1), (1 : Fin 2))) = cols_right0 ((3 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_4_0_0 : (tripleIndices 2 4 2).map (fun j => (right0Middle3 5 7) j ((4 : Fin 8), (0 : Fin 1), (0 : Fin 2))) = cols_right0 ((4 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_4_0_1 : (tripleIndices 2 4 2).map (fun j => (right0Middle3 5 7) j ((4 : Fin 8), (0 : Fin 1), (1 : Fin 2))) = cols_right0 ((4 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_5_0_0 : (tripleIndices 2 4 2).map (fun j => (right0Middle3 5 7) j ((5 : Fin 8), (0 : Fin 1), (0 : Fin 2))) = cols_right0 ((5 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_5_0_1 : (tripleIndices 2 4 2).map (fun j => (right0Middle3 5 7) j ((5 : Fin 8), (0 : Fin 1), (1 : Fin 2))) = cols_right0 ((5 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_6_0_0 : (tripleIndices 2 4 2).map (fun j => (right0Middle3 5 7) j ((6 : Fin 8), (0 : Fin 1), (0 : Fin 2))) = cols_right0 ((6 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_6_0_1 : (tripleIndices 2 4 2).map (fun j => (right0Middle3 5 7) j ((6 : Fin 8), (0 : Fin 1), (1 : Fin 2))) = cols_right0 ((6 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_7_0_0 : (tripleIndices 2 4 2).map (fun j => (right0Middle3 5 7) j ((7 : Fin 8), (0 : Fin 1), (0 : Fin 2))) = cols_right0 ((7 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_7_0_1 : (tripleIndices 2 4 2).map (fun j => (right0Middle3 5 7) j ((7 : Fin 8), (0 : Fin 1), (1 : Fin 2))) = cols_right0 ((7 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right0_data (r : LeftIndex 3 5 7) : (tripleIndices 2 4 2).map (fun j => (right0Middle3 5 7) j r) = cols_right0 r := by
  fin_cases r
  · exact cols_right0_eq_0_0_0
  · exact cols_right0_eq_0_0_1
  · exact cols_right0_eq_1_0_0
  · exact cols_right0_eq_1_0_1
  · exact cols_right0_eq_2_0_0
  · exact cols_right0_eq_2_0_1
  · exact cols_right0_eq_3_0_0
  · exact cols_right0_eq_3_0_1
  · exact cols_right0_eq_4_0_0
  · exact cols_right0_eq_4_0_1
  · exact cols_right0_eq_5_0_0
  · exact cols_right0_eq_5_0_1
  · exact cols_right0_eq_6_0_0
  · exact cols_right0_eq_6_0_1
  · exact cols_right0_eq_7_0_0
  · exact cols_right0_eq_7_0_1

private def cols_left0Data : List (List ℤ) := [decodeIntegerRow 16 3 1 26483234,
    decodeIntegerRow 16 3 1 35931238,
    decodeIntegerRow 16 3 1 16917294,
    decodeIntegerRow 16 3 1 7233418,
    decodeIntegerRow 16 3 1 20974414,
    decodeIntegerRow 16 3 1 19923178,
    decodeIntegerRow 16 3 1 21009406,
    decodeIntegerRow 16 3 1 19934842,
    decodeIntegerRow 16 3 1 19936354,
    decodeIntegerRow 16 3 1 21013798,
    decodeIntegerRow 16 3 1 23124946,
    decodeIntegerRow 16 3 1 22076662,
    decodeIntegerRow 16 3 1 7233586,
    decodeIntegerRow 16 3 1 16917782,
    decodeIntegerRow 16 3 1 7115326,
    decodeIntegerRow 16 3 1 16563002]

def cols_left0 (r : LeftIndex 3 5 7) : List ℤ := cols_left0Data.getD (leftPosition 3 5 7 r) []

private theorem cols_left0_eq_0_0_0 : (tripleIndices 2 4 2).map (fun j => (left0Middle3 5 7) j ((0 : Fin 8), (0 : Fin 1), (0 : Fin 2))) = cols_left0 ((0 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_1 : (tripleIndices 2 4 2).map (fun j => (left0Middle3 5 7) j ((0 : Fin 8), (0 : Fin 1), (1 : Fin 2))) = cols_left0 ((0 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_0 : (tripleIndices 2 4 2).map (fun j => (left0Middle3 5 7) j ((1 : Fin 8), (0 : Fin 1), (0 : Fin 2))) = cols_left0 ((1 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_1 : (tripleIndices 2 4 2).map (fun j => (left0Middle3 5 7) j ((1 : Fin 8), (0 : Fin 1), (1 : Fin 2))) = cols_left0 ((1 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_0 : (tripleIndices 2 4 2).map (fun j => (left0Middle3 5 7) j ((2 : Fin 8), (0 : Fin 1), (0 : Fin 2))) = cols_left0 ((2 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_1 : (tripleIndices 2 4 2).map (fun j => (left0Middle3 5 7) j ((2 : Fin 8), (0 : Fin 1), (1 : Fin 2))) = cols_left0 ((2 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_0 : (tripleIndices 2 4 2).map (fun j => (left0Middle3 5 7) j ((3 : Fin 8), (0 : Fin 1), (0 : Fin 2))) = cols_left0 ((3 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_1 : (tripleIndices 2 4 2).map (fun j => (left0Middle3 5 7) j ((3 : Fin 8), (0 : Fin 1), (1 : Fin 2))) = cols_left0 ((3 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_4_0_0 : (tripleIndices 2 4 2).map (fun j => (left0Middle3 5 7) j ((4 : Fin 8), (0 : Fin 1), (0 : Fin 2))) = cols_left0 ((4 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_4_0_1 : (tripleIndices 2 4 2).map (fun j => (left0Middle3 5 7) j ((4 : Fin 8), (0 : Fin 1), (1 : Fin 2))) = cols_left0 ((4 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_5_0_0 : (tripleIndices 2 4 2).map (fun j => (left0Middle3 5 7) j ((5 : Fin 8), (0 : Fin 1), (0 : Fin 2))) = cols_left0 ((5 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_5_0_1 : (tripleIndices 2 4 2).map (fun j => (left0Middle3 5 7) j ((5 : Fin 8), (0 : Fin 1), (1 : Fin 2))) = cols_left0 ((5 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_6_0_0 : (tripleIndices 2 4 2).map (fun j => (left0Middle3 5 7) j ((6 : Fin 8), (0 : Fin 1), (0 : Fin 2))) = cols_left0 ((6 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_6_0_1 : (tripleIndices 2 4 2).map (fun j => (left0Middle3 5 7) j ((6 : Fin 8), (0 : Fin 1), (1 : Fin 2))) = cols_left0 ((6 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_7_0_0 : (tripleIndices 2 4 2).map (fun j => (left0Middle3 5 7) j ((7 : Fin 8), (0 : Fin 1), (0 : Fin 2))) = cols_left0 ((7 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_7_0_1 : (tripleIndices 2 4 2).map (fun j => (left0Middle3 5 7) j ((7 : Fin 8), (0 : Fin 1), (1 : Fin 2))) = cols_left0 ((7 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_left0_data (r : LeftIndex 3 5 7) : (tripleIndices 2 4 2).map (fun j => (left0Middle3 5 7) j r) = cols_left0 r := by
  fin_cases r
  · exact cols_left0_eq_0_0_0
  · exact cols_left0_eq_0_0_1
  · exact cols_left0_eq_1_0_0
  · exact cols_left0_eq_1_0_1
  · exact cols_left0_eq_2_0_0
  · exact cols_left0_eq_2_0_1
  · exact cols_left0_eq_3_0_0
  · exact cols_left0_eq_3_0_1
  · exact cols_left0_eq_4_0_0
  · exact cols_left0_eq_4_0_1
  · exact cols_left0_eq_5_0_0
  · exact cols_left0_eq_5_0_1
  · exact cols_left0_eq_6_0_0
  · exact cols_left0_eq_6_0_1
  · exact cols_left0_eq_7_0_0
  · exact cols_left0_eq_7_0_1

private def cols_right2Data : List (List ℤ) := [decodeIntegerRow 16 5 2 134868915552,
    decodeIntegerRow 16 5 2 87918795360,
    decodeIntegerRow 16 5 2 139790787552,
    decodeIntegerRow 16 5 2 89090657760,
    decodeIntegerRow 16 5 2 134906415072,
    decodeIntegerRow 16 5 2 88106295264,
    decodeIntegerRow 16 5 2 12837727552,
    decodeIntegerRow 16 5 2 63700357760,
    decodeIntegerRow 16 5 2 64481295264,
    decodeIntegerRow 16 5 2 17681415072,
    decodeIntegerRow 16 5 2 88887857760,
    decodeIntegerRow 16 5 2 139750227552,
    decodeIntegerRow 16 5 2 87919095264,
    decodeIntegerRow 16 5 2 134868975072,
    decodeIntegerRow 16 5 2 89090982864,
    decodeIntegerRow 16 5 2 139790853072]

def cols_right2 (r : LeftIndex 3 5 7) : List ℤ := cols_right2Data.getD (leftPosition 3 5 7 r) []

private theorem cols_right2_eq_0_0_0 : (tripleIndices 2 4 2).map (fun j => (right2Middle3 5 7) j ((0 : Fin 8), (0 : Fin 1), (0 : Fin 2))) = cols_right2 ((0 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_1 : (tripleIndices 2 4 2).map (fun j => (right2Middle3 5 7) j ((0 : Fin 8), (0 : Fin 1), (1 : Fin 2))) = cols_right2 ((0 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_0 : (tripleIndices 2 4 2).map (fun j => (right2Middle3 5 7) j ((1 : Fin 8), (0 : Fin 1), (0 : Fin 2))) = cols_right2 ((1 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_1 : (tripleIndices 2 4 2).map (fun j => (right2Middle3 5 7) j ((1 : Fin 8), (0 : Fin 1), (1 : Fin 2))) = cols_right2 ((1 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_0 : (tripleIndices 2 4 2).map (fun j => (right2Middle3 5 7) j ((2 : Fin 8), (0 : Fin 1), (0 : Fin 2))) = cols_right2 ((2 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_1 : (tripleIndices 2 4 2).map (fun j => (right2Middle3 5 7) j ((2 : Fin 8), (0 : Fin 1), (1 : Fin 2))) = cols_right2 ((2 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_0 : (tripleIndices 2 4 2).map (fun j => (right2Middle3 5 7) j ((3 : Fin 8), (0 : Fin 1), (0 : Fin 2))) = cols_right2 ((3 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_1 : (tripleIndices 2 4 2).map (fun j => (right2Middle3 5 7) j ((3 : Fin 8), (0 : Fin 1), (1 : Fin 2))) = cols_right2 ((3 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_4_0_0 : (tripleIndices 2 4 2).map (fun j => (right2Middle3 5 7) j ((4 : Fin 8), (0 : Fin 1), (0 : Fin 2))) = cols_right2 ((4 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_4_0_1 : (tripleIndices 2 4 2).map (fun j => (right2Middle3 5 7) j ((4 : Fin 8), (0 : Fin 1), (1 : Fin 2))) = cols_right2 ((4 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_5_0_0 : (tripleIndices 2 4 2).map (fun j => (right2Middle3 5 7) j ((5 : Fin 8), (0 : Fin 1), (0 : Fin 2))) = cols_right2 ((5 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_5_0_1 : (tripleIndices 2 4 2).map (fun j => (right2Middle3 5 7) j ((5 : Fin 8), (0 : Fin 1), (1 : Fin 2))) = cols_right2 ((5 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_6_0_0 : (tripleIndices 2 4 2).map (fun j => (right2Middle3 5 7) j ((6 : Fin 8), (0 : Fin 1), (0 : Fin 2))) = cols_right2 ((6 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_6_0_1 : (tripleIndices 2 4 2).map (fun j => (right2Middle3 5 7) j ((6 : Fin 8), (0 : Fin 1), (1 : Fin 2))) = cols_right2 ((6 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_7_0_0 : (tripleIndices 2 4 2).map (fun j => (right2Middle3 5 7) j ((7 : Fin 8), (0 : Fin 1), (0 : Fin 2))) = cols_right2 ((7 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_7_0_1 : (tripleIndices 2 4 2).map (fun j => (right2Middle3 5 7) j ((7 : Fin 8), (0 : Fin 1), (1 : Fin 2))) = cols_right2 ((7 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right2_data (r : LeftIndex 3 5 7) : (tripleIndices 2 4 2).map (fun j => (right2Middle3 5 7) j r) = cols_right2 r := by
  fin_cases r
  · exact cols_right2_eq_0_0_0
  · exact cols_right2_eq_0_0_1
  · exact cols_right2_eq_1_0_0
  · exact cols_right2_eq_1_0_1
  · exact cols_right2_eq_2_0_0
  · exact cols_right2_eq_2_0_1
  · exact cols_right2_eq_3_0_0
  · exact cols_right2_eq_3_0_1
  · exact cols_right2_eq_4_0_0
  · exact cols_right2_eq_4_0_1
  · exact cols_right2_eq_5_0_0
  · exact cols_right2_eq_5_0_1
  · exact cols_right2_eq_6_0_0
  · exact cols_right2_eq_6_0_1
  · exact cols_right2_eq_7_0_0
  · exact cols_right2_eq_7_0_1

theorem product0_eq : HexagonAtoms357.outerABC * HexagonAtoms357.assocABC = HexagonAtoms357.assocABC :=
  Matrix.one_mul (m := Fin 2 × Fin 4 × Fin 2) (n := Fin 8 × Fin 1 × Fin 2) _

theorem product1_eq : HexagonAtoms357.assocBAC * HexagonAtoms357.innerABC = HexagonAtoms357.assocBAC :=
  Matrix.mul_one (m := Fin 2 × Fin 4 × Fin 2) (n := Fin 8 × Fin 1 × Fin 2) _

theorem product2_eq : HexagonAtoms357.innerRightABC * HexagonAtoms357.assocABC = HexagonAtoms357.assocABC :=
  Matrix.one_mul (m := Fin 2 × Fin 4 × Fin 2) (n := Fin 8 × Fin 1 × Fin 2) _

theorem product3_eq : HexagonAtoms357.inverseACB * right0Middle3 5 7 = rowColumnMul rows_inverseACB cols_right0 :=
  (rowColumnMul_eq _ _ _ _ rows_inverseACB_data cols_right0_data).symm

theorem product4_eq : HexagonAtoms357.innerACB * right1Middle3 5 7 = right1Middle3 5 7 :=
  Matrix.one_mul (m := Fin 2 × Fin 4 × Fin 2) (n := Fin 8 × Fin 1 × Fin 2) _

theorem product5_eq : HexagonAtoms357.assocBCA * left0Middle3 5 7 = rowColumnMul rows_assocBCA cols_left0 :=
  (rowColumnMul_eq _ _ _ _ rows_assocBCA_data cols_left0_data).symm

theorem product6_eq : HexagonAtoms357.innerRightBAC * left1Middle3 5 7 = left1Middle3 5 7 :=
  Matrix.one_mul (m := Fin 2 × Fin 4 × Fin 2) (n := Fin 8 × Fin 1 × Fin 2) _

theorem product7_eq : HexagonAtoms357.assocCAB * right2Middle3 5 7 = rowColumnMul rows_assocCAB cols_right2 :=
  (rowColumnMul_eq _ _ _ _ rows_assocCAB_data cols_right2_data).symm

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn357
