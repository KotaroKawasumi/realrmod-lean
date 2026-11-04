import RMod.BrundanEllis.StackingReferenceHexagonAtoms375
import RMod.BrundanEllis.StackingReferenceHexagonMiddle3
import RMod.BrundanEllis.StackingReferenceRowColumnCheck

/-! Verified row and column lists. Each subsequent scalar product traverses
these lists directly, without repeated lookup into the original matrices. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn375
open Superfusion

private def rows_inverseACBData : List (List ℤ) := [decodeIntegerRow 16 3 1 26483234,
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

def rows_inverseACB (r : LeftIndex 3 5 7) : List ℤ := rows_inverseACBData.getD (leftPosition 3 5 7 r) []

private theorem rows_inverseACB_eq_0_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms375.inverseACB) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 2))) = rows_inverseACB ((0 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms375.inverseACB) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 2))) = rows_inverseACB ((0 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms375.inverseACB) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 2))) = rows_inverseACB ((1 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms375.inverseACB) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 2))) = rows_inverseACB ((1 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms375.inverseACB) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 2))) = rows_inverseACB ((2 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms375.inverseACB) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 2))) = rows_inverseACB ((2 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms375.inverseACB) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 2))) = rows_inverseACB ((3 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms375.inverseACB) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 2))) = rows_inverseACB ((3 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_4_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms375.inverseACB) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 2))) = rows_inverseACB ((4 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_4_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms375.inverseACB) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 2))) = rows_inverseACB ((4 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_5_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms375.inverseACB) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 2))) = rows_inverseACB ((5 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_5_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms375.inverseACB) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 2))) = rows_inverseACB ((5 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_6_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms375.inverseACB) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 2))) = rows_inverseACB ((6 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_6_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms375.inverseACB) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 2))) = rows_inverseACB ((6 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_7_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms375.inverseACB) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 2))) = rows_inverseACB ((7 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_7_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms375.inverseACB) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 2))) = rows_inverseACB ((7 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_inverseACB_data (r : LeftIndex 3 5 7) : (tripleIndices 2 4 2).map ((HexagonAtoms375.inverseACB) r) = rows_inverseACB r := by
  fin_cases r
  · exact rows_inverseACB_eq_0_0_0
  · exact rows_inverseACB_eq_0_0_1
  · exact rows_inverseACB_eq_1_0_0
  · exact rows_inverseACB_eq_1_0_1
  · exact rows_inverseACB_eq_2_0_0
  · exact rows_inverseACB_eq_2_0_1
  · exact rows_inverseACB_eq_3_0_0
  · exact rows_inverseACB_eq_3_0_1
  · exact rows_inverseACB_eq_4_0_0
  · exact rows_inverseACB_eq_4_0_1
  · exact rows_inverseACB_eq_5_0_0
  · exact rows_inverseACB_eq_5_0_1
  · exact rows_inverseACB_eq_6_0_0
  · exact rows_inverseACB_eq_6_0_1
  · exact rows_inverseACB_eq_7_0_0
  · exact rows_inverseACB_eq_7_0_1

private def rows_assocBCAData : List (List ℤ) := [decodeIntegerRow 16 3 1 26483234,
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

def rows_assocBCA (r : RightIndex 7 5 3) : List ℤ := rows_assocBCAData.getD (rightPosition 7 5 3 r) []

private theorem rows_assocBCA_eq_0_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms375.assocBCA) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 2))) = rows_assocBCA ((0 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms375.assocBCA) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 2))) = rows_assocBCA ((0 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms375.assocBCA) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 2))) = rows_assocBCA ((1 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms375.assocBCA) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 2))) = rows_assocBCA ((1 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms375.assocBCA) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 2))) = rows_assocBCA ((2 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms375.assocBCA) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 2))) = rows_assocBCA ((2 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms375.assocBCA) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 2))) = rows_assocBCA ((3 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms375.assocBCA) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 2))) = rows_assocBCA ((3 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_4_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms375.assocBCA) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 2))) = rows_assocBCA ((4 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_4_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms375.assocBCA) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 2))) = rows_assocBCA ((4 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_5_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms375.assocBCA) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 2))) = rows_assocBCA ((5 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_5_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms375.assocBCA) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 2))) = rows_assocBCA ((5 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_6_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms375.assocBCA) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 2))) = rows_assocBCA ((6 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_6_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms375.assocBCA) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 2))) = rows_assocBCA ((6 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_7_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms375.assocBCA) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 2))) = rows_assocBCA ((7 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_7_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms375.assocBCA) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 2))) = rows_assocBCA ((7 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocBCA_data (r : RightIndex 7 5 3) : (tripleIndices 2 4 2).map ((HexagonAtoms375.assocBCA) r) = rows_assocBCA r := by
  fin_cases r
  · exact rows_assocBCA_eq_0_0_0
  · exact rows_assocBCA_eq_0_0_1
  · exact rows_assocBCA_eq_1_0_0
  · exact rows_assocBCA_eq_1_0_1
  · exact rows_assocBCA_eq_2_0_0
  · exact rows_assocBCA_eq_2_0_1
  · exact rows_assocBCA_eq_3_0_0
  · exact rows_assocBCA_eq_3_0_1
  · exact rows_assocBCA_eq_4_0_0
  · exact rows_assocBCA_eq_4_0_1
  · exact rows_assocBCA_eq_5_0_0
  · exact rows_assocBCA_eq_5_0_1
  · exact rows_assocBCA_eq_6_0_0
  · exact rows_assocBCA_eq_6_0_1
  · exact rows_assocBCA_eq_7_0_0
  · exact rows_assocBCA_eq_7_0_1

private def rows_assocCABData : List (List ℤ) := [decodeIntegerRow 16 3 1 16263412,
    decodeIntegerRow 16 3 1 5738252,
    decodeIntegerRow 16 3 1 17339896,
    decodeIntegerRow 16 3 1 8966424,
    decodeIntegerRow 16 3 1 8571144,
    decodeIntegerRow 16 3 1 17203816,
    decodeIntegerRow 16 3 1 5422028,
    decodeIntegerRow 16 3 1 16154548,
    decodeIntegerRow 16 3 1 5736936,
    decodeIntegerRow 16 3 1 16259464,
    decodeIntegerRow 16 3 1 8964788,
    decodeIntegerRow 16 3 1 17334988,
    decodeIntegerRow 16 3 1 17208628,
    decodeIntegerRow 16 3 1 8572748,
    decodeIntegerRow 16 3 1 16158376,
    decodeIntegerRow 16 3 1 5423304]

def rows_assocCAB (r : RightIndex 5 3 7) : List ℤ := rows_assocCABData.getD (rightPosition 5 3 7 r) []

private theorem rows_assocCAB_eq_0_0_0 : (tripleIndices 8 1 2).map ((HexagonAtoms375.assocCAB) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_1 : (tripleIndices 8 1 2).map ((HexagonAtoms375.assocCAB) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_0 : (tripleIndices 8 1 2).map ((HexagonAtoms375.assocCAB) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = rows_assocCAB ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_1 : (tripleIndices 8 1 2).map ((HexagonAtoms375.assocCAB) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = rows_assocCAB ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_2_0 : (tripleIndices 8 1 2).map ((HexagonAtoms375.assocCAB) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = rows_assocCAB ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_2_1 : (tripleIndices 8 1 2).map ((HexagonAtoms375.assocCAB) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = rows_assocCAB ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_3_0 : (tripleIndices 8 1 2).map ((HexagonAtoms375.assocCAB) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = rows_assocCAB ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_3_1 : (tripleIndices 8 1 2).map ((HexagonAtoms375.assocCAB) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = rows_assocCAB ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_0 : (tripleIndices 8 1 2).map ((HexagonAtoms375.assocCAB) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_1 : (tripleIndices 8 1 2).map ((HexagonAtoms375.assocCAB) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_0 : (tripleIndices 8 1 2).map ((HexagonAtoms375.assocCAB) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = rows_assocCAB ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_1 : (tripleIndices 8 1 2).map ((HexagonAtoms375.assocCAB) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = rows_assocCAB ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_2_0 : (tripleIndices 8 1 2).map ((HexagonAtoms375.assocCAB) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = rows_assocCAB ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_2_1 : (tripleIndices 8 1 2).map ((HexagonAtoms375.assocCAB) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = rows_assocCAB ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_3_0 : (tripleIndices 8 1 2).map ((HexagonAtoms375.assocCAB) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = rows_assocCAB ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_3_1 : (tripleIndices 8 1 2).map ((HexagonAtoms375.assocCAB) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = rows_assocCAB ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocCAB_data (r : RightIndex 5 3 7) : (tripleIndices 8 1 2).map ((HexagonAtoms375.assocCAB) r) = rows_assocCAB r := by
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

private def cols_right0Data : List (List ℤ) := [decodeIntegerRow 16 3 1 5515360,
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

def cols_right0 (r : LeftIndex 3 7 5) : List ℤ := cols_right0Data.getD (leftPosition 3 7 5 r) []

private theorem cols_right0_eq_0_0_0 : (tripleIndices 2 4 2).map (fun j => (right0Middle3 7 5) j ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = cols_right0 ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_1 : (tripleIndices 2 4 2).map (fun j => (right0Middle3 7 5) j ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = cols_right0 ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_0 : (tripleIndices 2 4 2).map (fun j => (right0Middle3 7 5) j ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = cols_right0 ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_1 : (tripleIndices 2 4 2).map (fun j => (right0Middle3 7 5) j ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = cols_right0 ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_2_0 : (tripleIndices 2 4 2).map (fun j => (right0Middle3 7 5) j ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = cols_right0 ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_2_1 : (tripleIndices 2 4 2).map (fun j => (right0Middle3 7 5) j ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = cols_right0 ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_3_0 : (tripleIndices 2 4 2).map (fun j => (right0Middle3 7 5) j ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = cols_right0 ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_3_1 : (tripleIndices 2 4 2).map (fun j => (right0Middle3 7 5) j ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = cols_right0 ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_0 : (tripleIndices 2 4 2).map (fun j => (right0Middle3 7 5) j ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = cols_right0 ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_1 : (tripleIndices 2 4 2).map (fun j => (right0Middle3 7 5) j ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = cols_right0 ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_0 : (tripleIndices 2 4 2).map (fun j => (right0Middle3 7 5) j ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = cols_right0 ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_1 : (tripleIndices 2 4 2).map (fun j => (right0Middle3 7 5) j ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = cols_right0 ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_2_0 : (tripleIndices 2 4 2).map (fun j => (right0Middle3 7 5) j ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = cols_right0 ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_2_1 : (tripleIndices 2 4 2).map (fun j => (right0Middle3 7 5) j ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = cols_right0 ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_3_0 : (tripleIndices 2 4 2).map (fun j => (right0Middle3 7 5) j ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = cols_right0 ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_3_1 : (tripleIndices 2 4 2).map (fun j => (right0Middle3 7 5) j ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = cols_right0 ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right0_data (r : LeftIndex 3 7 5) : (tripleIndices 2 4 2).map (fun j => (right0Middle3 7 5) j r) = cols_right0 r := by
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

private def cols_left0Data : List (List ℤ) := [decodeIntegerRow 16 3 1 5515360,
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

def cols_left0 (r : LeftIndex 3 7 5) : List ℤ := cols_left0Data.getD (leftPosition 3 7 5 r) []

private theorem cols_left0_eq_0_0_0 : (tripleIndices 2 4 2).map (fun j => (left0Middle3 7 5) j ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = cols_left0 ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_1 : (tripleIndices 2 4 2).map (fun j => (left0Middle3 7 5) j ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = cols_left0 ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_0 : (tripleIndices 2 4 2).map (fun j => (left0Middle3 7 5) j ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = cols_left0 ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_1 : (tripleIndices 2 4 2).map (fun j => (left0Middle3 7 5) j ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = cols_left0 ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_2_0 : (tripleIndices 2 4 2).map (fun j => (left0Middle3 7 5) j ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = cols_left0 ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_2_1 : (tripleIndices 2 4 2).map (fun j => (left0Middle3 7 5) j ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = cols_left0 ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_3_0 : (tripleIndices 2 4 2).map (fun j => (left0Middle3 7 5) j ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = cols_left0 ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_3_1 : (tripleIndices 2 4 2).map (fun j => (left0Middle3 7 5) j ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = cols_left0 ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_0 : (tripleIndices 2 4 2).map (fun j => (left0Middle3 7 5) j ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = cols_left0 ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_1 : (tripleIndices 2 4 2).map (fun j => (left0Middle3 7 5) j ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = cols_left0 ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_0 : (tripleIndices 2 4 2).map (fun j => (left0Middle3 7 5) j ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = cols_left0 ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_1 : (tripleIndices 2 4 2).map (fun j => (left0Middle3 7 5) j ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = cols_left0 ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_2_0 : (tripleIndices 2 4 2).map (fun j => (left0Middle3 7 5) j ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = cols_left0 ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_2_1 : (tripleIndices 2 4 2).map (fun j => (left0Middle3 7 5) j ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = cols_left0 ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_3_0 : (tripleIndices 2 4 2).map (fun j => (left0Middle3 7 5) j ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = cols_left0 ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_3_1 : (tripleIndices 2 4 2).map (fun j => (left0Middle3 7 5) j ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = cols_left0 ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_left0_data (r : LeftIndex 3 7 5) : (tripleIndices 2 4 2).map (fun j => (left0Middle3 7 5) j r) = cols_left0 r := by
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

private def cols_right2Data : List (List ℤ) := [decodeIntegerRow 16 5 2 88970357552,
    decodeIntegerRow 16 5 2 139676727760,
    decodeIntegerRow 16 5 2 87992220072,
    decodeIntegerRow 16 5 2 134786100264,
    decodeIntegerRow 16 5 2 134989290264,
    decodeIntegerRow 16 5 2 88033170072,
    decodeIntegerRow 16 5 2 139864287760,
    decodeIntegerRow 16 5 2 89008157552,
    decodeIntegerRow 16 5 2 139676787864,
    decodeIntegerRow 16 5 2 88970658072,
    decodeIntegerRow 16 5 2 134786165360,
    decodeIntegerRow 16 5 2 87992545552,
    decodeIntegerRow 16 5 2 88032845552,
    decodeIntegerRow 16 5 2 134989225360,
    decodeIntegerRow 16 5 2 89007858072,
    decodeIntegerRow 16 5 2 139864227864]

def cols_right2 (r : LeftIndex 3 7 5) : List ℤ := cols_right2Data.getD (leftPosition 3 7 5 r) []

private theorem cols_right2_eq_0_0_0 : (tripleIndices 8 1 2).map (fun j => (right2Middle3 7 5) j ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = cols_right2 ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_1 : (tripleIndices 8 1 2).map (fun j => (right2Middle3 7 5) j ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = cols_right2 ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_0 : (tripleIndices 8 1 2).map (fun j => (right2Middle3 7 5) j ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = cols_right2 ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_1 : (tripleIndices 8 1 2).map (fun j => (right2Middle3 7 5) j ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = cols_right2 ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_2_0 : (tripleIndices 8 1 2).map (fun j => (right2Middle3 7 5) j ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = cols_right2 ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_2_1 : (tripleIndices 8 1 2).map (fun j => (right2Middle3 7 5) j ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = cols_right2 ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_3_0 : (tripleIndices 8 1 2).map (fun j => (right2Middle3 7 5) j ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = cols_right2 ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_3_1 : (tripleIndices 8 1 2).map (fun j => (right2Middle3 7 5) j ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = cols_right2 ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_0 : (tripleIndices 8 1 2).map (fun j => (right2Middle3 7 5) j ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = cols_right2 ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_1 : (tripleIndices 8 1 2).map (fun j => (right2Middle3 7 5) j ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = cols_right2 ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_0 : (tripleIndices 8 1 2).map (fun j => (right2Middle3 7 5) j ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = cols_right2 ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_1 : (tripleIndices 8 1 2).map (fun j => (right2Middle3 7 5) j ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = cols_right2 ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_2_0 : (tripleIndices 8 1 2).map (fun j => (right2Middle3 7 5) j ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = cols_right2 ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_2_1 : (tripleIndices 8 1 2).map (fun j => (right2Middle3 7 5) j ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = cols_right2 ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_3_0 : (tripleIndices 8 1 2).map (fun j => (right2Middle3 7 5) j ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = cols_right2 ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_3_1 : (tripleIndices 8 1 2).map (fun j => (right2Middle3 7 5) j ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = cols_right2 ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right2_data (r : LeftIndex 3 7 5) : (tripleIndices 8 1 2).map (fun j => (right2Middle3 7 5) j r) = cols_right2 r := by
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

theorem product0_eq : HexagonAtoms375.outerABC * HexagonAtoms375.assocABC = HexagonAtoms375.assocABC :=
  Matrix.one_mul (m := Fin 2 × Fin 4 × Fin 2) (n := Fin 2 × Fin 4 × Fin 2) _

theorem product1_eq : HexagonAtoms375.assocBAC * HexagonAtoms375.innerABC = HexagonAtoms375.assocBAC :=
  Matrix.mul_one (m := Fin 8 × Fin 1 × Fin 2) (n := Fin 2 × Fin 4 × Fin 2) _

theorem product2_eq : HexagonAtoms375.innerRightABC * HexagonAtoms375.assocABC = HexagonAtoms375.assocABC :=
  Matrix.one_mul (m := Fin 2 × Fin 4 × Fin 2) (n := Fin 2 × Fin 4 × Fin 2) _

theorem product3_eq : HexagonAtoms375.inverseACB * right0Middle3 7 5 = rowColumnMul rows_inverseACB cols_right0 :=
  (rowColumnMul_eq _ _ _ _ rows_inverseACB_data cols_right0_data).symm

theorem product4_eq : HexagonAtoms375.innerACB * right1Middle3 7 5 = right1Middle3 7 5 :=
  Matrix.one_mul (m := Fin 8 × Fin 1 × Fin 2) (n := Fin 2 × Fin 4 × Fin 2) _

theorem product5_eq : HexagonAtoms375.assocBCA * left0Middle3 7 5 = rowColumnMul rows_assocBCA cols_left0 :=
  (rowColumnMul_eq _ _ _ _ rows_assocBCA_data cols_left0_data).symm

theorem product6_eq : HexagonAtoms375.innerRightBAC * left1Middle3 7 5 = left1Middle3 7 5 :=
  Matrix.one_mul (m := Fin 8 × Fin 1 × Fin 2) (n := Fin 2 × Fin 4 × Fin 2) _

theorem product7_eq : HexagonAtoms375.assocCAB * right2Middle3 7 5 = rowColumnMul rows_assocCAB cols_right2 :=
  (rowColumnMul_eq _ _ _ _ rows_assocCAB_data cols_right2_data).symm

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn375
