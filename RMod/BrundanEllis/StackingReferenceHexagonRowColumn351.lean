import RMod.BrundanEllis.StackingReferenceHexagonAtoms351
import RMod.BrundanEllis.StackingReferenceHexagonMiddle3
import RMod.BrundanEllis.StackingReferenceRowColumnCheck

/-! Verified row and column lists. Each subsequent scalar product traverses
these lists directly, without repeated lookup into the original matrices. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn351
open Superfusion

private def rows_inverseACBData : List (List ℤ) := [decodeIntegerRow 16 3 1 21582406,
    decodeIntegerRow 16 3 1 21700508,
    decodeIntegerRow 16 3 1 7174372,
    decodeIntegerRow 16 3 1 26306086,
    decodeIntegerRow 16 3 1 21503686,
    decodeIntegerRow 16 3 1 21529948,
    decodeIntegerRow 16 3 1 22056988,
    decodeIntegerRow 16 3 1 23116954,
    decodeIntegerRow 16 3 1 20994106,
    decodeIntegerRow 16 3 1 19928308,
    decodeIntegerRow 16 3 1 21543052,
    decodeIntegerRow 16 3 1 21516826,
    decodeIntegerRow 16 3 1 7174534,
    decodeIntegerRow 16 3 1 26306572,
    decodeIntegerRow 16 3 1 21582412,
    decodeIntegerRow 16 3 1 21700506]

def rows_inverseACB (r : LeftIndex 3 1 5) : List ℤ := rows_inverseACBData.getD (leftPosition 3 1 5 r) []

private theorem rows_inverseACB_eq_0_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms351.inverseACB) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms351.inverseACB) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_0 : (tripleIndices 2 4 2).map ((HexagonAtoms351.inverseACB) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = rows_inverseACB ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_1 : (tripleIndices 2 4 2).map ((HexagonAtoms351.inverseACB) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = rows_inverseACB ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_2_0 : (tripleIndices 2 4 2).map ((HexagonAtoms351.inverseACB) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = rows_inverseACB ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_2_1 : (tripleIndices 2 4 2).map ((HexagonAtoms351.inverseACB) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = rows_inverseACB ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_3_0 : (tripleIndices 2 4 2).map ((HexagonAtoms351.inverseACB) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = rows_inverseACB ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_3_1 : (tripleIndices 2 4 2).map ((HexagonAtoms351.inverseACB) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = rows_inverseACB ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms351.inverseACB) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms351.inverseACB) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_0 : (tripleIndices 2 4 2).map ((HexagonAtoms351.inverseACB) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = rows_inverseACB ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_1 : (tripleIndices 2 4 2).map ((HexagonAtoms351.inverseACB) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = rows_inverseACB ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_2_0 : (tripleIndices 2 4 2).map ((HexagonAtoms351.inverseACB) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = rows_inverseACB ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_2_1 : (tripleIndices 2 4 2).map ((HexagonAtoms351.inverseACB) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = rows_inverseACB ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_3_0 : (tripleIndices 2 4 2).map ((HexagonAtoms351.inverseACB) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = rows_inverseACB ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_3_1 : (tripleIndices 2 4 2).map ((HexagonAtoms351.inverseACB) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = rows_inverseACB ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_inverseACB_data (r : LeftIndex 3 1 5) : (tripleIndices 2 4 2).map ((HexagonAtoms351.inverseACB) r) = rows_inverseACB r := by
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

private def rows_assocBCAData : List (List ℤ) := [decodeIntegerRow 16 3 1 21464314,
    decodeIntegerRow 16 3 1 21346212,
    decodeIntegerRow 16 3 1 35872348,
    decodeIntegerRow 16 3 1 16740634,
    decodeIntegerRow 16 3 1 21543034,
    decodeIntegerRow 16 3 1 21516772,
    decodeIntegerRow 16 3 1 20989732,
    decodeIntegerRow 16 3 1 19929766,
    decodeIntegerRow 16 3 1 22052614,
    decodeIntegerRow 16 3 1 23118412,
    decodeIntegerRow 16 3 1 21503668,
    decodeIntegerRow 16 3 1 21529894,
    decodeIntegerRow 16 3 1 35872186,
    decodeIntegerRow 16 3 1 16740148,
    decodeIntegerRow 16 3 1 21464308,
    decodeIntegerRow 16 3 1 21346214]

def rows_assocBCA (r : RightIndex 5 1 3) : List ℤ := rows_assocBCAData.getD (rightPosition 5 1 3 r) []

private theorem rows_assocBCA_eq_0_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms351.assocBCA) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = rows_assocBCA ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms351.assocBCA) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = rows_assocBCA ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_0 : (tripleIndices 2 4 2).map ((HexagonAtoms351.assocBCA) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = rows_assocBCA ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_1 : (tripleIndices 2 4 2).map ((HexagonAtoms351.assocBCA) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = rows_assocBCA ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_2_0 : (tripleIndices 2 4 2).map ((HexagonAtoms351.assocBCA) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = rows_assocBCA ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_2_1 : (tripleIndices 2 4 2).map ((HexagonAtoms351.assocBCA) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = rows_assocBCA ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_3_0 : (tripleIndices 2 4 2).map ((HexagonAtoms351.assocBCA) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = rows_assocBCA ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_3_1 : (tripleIndices 2 4 2).map ((HexagonAtoms351.assocBCA) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = rows_assocBCA ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms351.assocBCA) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = rows_assocBCA ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms351.assocBCA) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = rows_assocBCA ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_0 : (tripleIndices 2 4 2).map ((HexagonAtoms351.assocBCA) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = rows_assocBCA ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_1 : (tripleIndices 2 4 2).map ((HexagonAtoms351.assocBCA) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = rows_assocBCA ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_2_0 : (tripleIndices 2 4 2).map ((HexagonAtoms351.assocBCA) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = rows_assocBCA ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_2_1 : (tripleIndices 2 4 2).map ((HexagonAtoms351.assocBCA) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = rows_assocBCA ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_3_0 : (tripleIndices 2 4 2).map ((HexagonAtoms351.assocBCA) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = rows_assocBCA ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_3_1 : (tripleIndices 2 4 2).map ((HexagonAtoms351.assocBCA) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = rows_assocBCA ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocBCA_data (r : RightIndex 5 1 3) : (tripleIndices 2 4 2).map ((HexagonAtoms351.assocBCA) r) = rows_assocBCA r := by
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

private def rows_assocCABData : List (List ℤ) := [decodeIntegerRow 16 3 1 20812586,
    decodeIntegerRow 16 3 1 19988818,
    decodeIntegerRow 16 3 1 26325778,
    decodeIntegerRow 16 3 1 35865814,
    decodeIntegerRow 16 3 1 21879842,
    decodeIntegerRow 16 3 1 23176006,
    decodeIntegerRow 16 3 1 26286394,
    decodeIntegerRow 16 3 1 35878882,
    decodeIntegerRow 16 3 1 7167946,
    decodeIntegerRow 16 3 1 26286898,
    decodeIntegerRow 16 3 1 23177458,
    decodeIntegerRow 16 3 1 21171254,
    decodeIntegerRow 16 3 1 7181122,
    decodeIntegerRow 16 3 1 26326246,
    decodeIntegerRow 16 3 1 19987354,
    decodeIntegerRow 16 3 1 22229762]

def rows_assocCAB (r : RightIndex 1 3 5) : List ℤ := rows_assocCABData.getD (rightPosition 1 3 5 r) []

private theorem rows_assocCAB_eq_0_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms351.assocCAB) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 2))) = rows_assocCAB ((0 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms351.assocCAB) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 2))) = rows_assocCAB ((0 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms351.assocCAB) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 2))) = rows_assocCAB ((1 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms351.assocCAB) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 2))) = rows_assocCAB ((1 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms351.assocCAB) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 2))) = rows_assocCAB ((2 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms351.assocCAB) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 2))) = rows_assocCAB ((2 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms351.assocCAB) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 2))) = rows_assocCAB ((3 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms351.assocCAB) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 2))) = rows_assocCAB ((3 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_4_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms351.assocCAB) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 2))) = rows_assocCAB ((4 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_4_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms351.assocCAB) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 2))) = rows_assocCAB ((4 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_5_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms351.assocCAB) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 2))) = rows_assocCAB ((5 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_5_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms351.assocCAB) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 2))) = rows_assocCAB ((5 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_6_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms351.assocCAB) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 2))) = rows_assocCAB ((6 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_6_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms351.assocCAB) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 2))) = rows_assocCAB ((6 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_7_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms351.assocCAB) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 2))) = rows_assocCAB ((7 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_7_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms351.assocCAB) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 2))) = rows_assocCAB ((7 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocCAB_data (r : RightIndex 1 3 5) : (tripleIndices 2 4 2).map ((HexagonAtoms351.assocCAB) r) = rows_assocCAB r := by
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

private def cols_right0Data : List (List ℤ) := [decodeIntegerRow 16 3 1 34344172,
    decodeIntegerRow 16 3 1 17470616,
    decodeIntegerRow 16 3 1 5631784,
    decodeIntegerRow 16 3 1 26992812,
    decodeIntegerRow 16 3 1 8833708,
    decodeIntegerRow 16 3 1 25969784,
    decodeIntegerRow 16 3 1 37519864,
    decodeIntegerRow 16 3 1 16368852,
    decodeIntegerRow 16 3 1 17073068,
    decodeIntegerRow 16 3 1 8835064,
    decodeIntegerRow 16 3 1 26682744,
    decodeIntegerRow 16 3 1 37518292,
    decodeIntegerRow 16 3 1 25580012,
    decodeIntegerRow 16 3 1 34342936,
    decodeIntegerRow 16 3 1 16049064,
    decodeIntegerRow 16 3 1 5633452]

def cols_right0 (r : LeftIndex 3 5 1) : List ℤ := cols_right0Data.getD (leftPosition 3 5 1 r) []

private theorem cols_right0_eq_0_0_0 : (tripleIndices 2 4 2).map (fun j => (right0Middle3 5 1) j ((0 : Fin 8), (0 : Fin 1), (0 : Fin 2))) = cols_right0 ((0 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_1 : (tripleIndices 2 4 2).map (fun j => (right0Middle3 5 1) j ((0 : Fin 8), (0 : Fin 1), (1 : Fin 2))) = cols_right0 ((0 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_0 : (tripleIndices 2 4 2).map (fun j => (right0Middle3 5 1) j ((1 : Fin 8), (0 : Fin 1), (0 : Fin 2))) = cols_right0 ((1 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_1 : (tripleIndices 2 4 2).map (fun j => (right0Middle3 5 1) j ((1 : Fin 8), (0 : Fin 1), (1 : Fin 2))) = cols_right0 ((1 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_0 : (tripleIndices 2 4 2).map (fun j => (right0Middle3 5 1) j ((2 : Fin 8), (0 : Fin 1), (0 : Fin 2))) = cols_right0 ((2 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_1 : (tripleIndices 2 4 2).map (fun j => (right0Middle3 5 1) j ((2 : Fin 8), (0 : Fin 1), (1 : Fin 2))) = cols_right0 ((2 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_0 : (tripleIndices 2 4 2).map (fun j => (right0Middle3 5 1) j ((3 : Fin 8), (0 : Fin 1), (0 : Fin 2))) = cols_right0 ((3 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_1 : (tripleIndices 2 4 2).map (fun j => (right0Middle3 5 1) j ((3 : Fin 8), (0 : Fin 1), (1 : Fin 2))) = cols_right0 ((3 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_4_0_0 : (tripleIndices 2 4 2).map (fun j => (right0Middle3 5 1) j ((4 : Fin 8), (0 : Fin 1), (0 : Fin 2))) = cols_right0 ((4 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_4_0_1 : (tripleIndices 2 4 2).map (fun j => (right0Middle3 5 1) j ((4 : Fin 8), (0 : Fin 1), (1 : Fin 2))) = cols_right0 ((4 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_5_0_0 : (tripleIndices 2 4 2).map (fun j => (right0Middle3 5 1) j ((5 : Fin 8), (0 : Fin 1), (0 : Fin 2))) = cols_right0 ((5 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_5_0_1 : (tripleIndices 2 4 2).map (fun j => (right0Middle3 5 1) j ((5 : Fin 8), (0 : Fin 1), (1 : Fin 2))) = cols_right0 ((5 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_6_0_0 : (tripleIndices 2 4 2).map (fun j => (right0Middle3 5 1) j ((6 : Fin 8), (0 : Fin 1), (0 : Fin 2))) = cols_right0 ((6 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_6_0_1 : (tripleIndices 2 4 2).map (fun j => (right0Middle3 5 1) j ((6 : Fin 8), (0 : Fin 1), (1 : Fin 2))) = cols_right0 ((6 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_7_0_0 : (tripleIndices 2 4 2).map (fun j => (right0Middle3 5 1) j ((7 : Fin 8), (0 : Fin 1), (0 : Fin 2))) = cols_right0 ((7 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_7_0_1 : (tripleIndices 2 4 2).map (fun j => (right0Middle3 5 1) j ((7 : Fin 8), (0 : Fin 1), (1 : Fin 2))) = cols_right0 ((7 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right0_data (r : LeftIndex 3 5 1) : (tripleIndices 2 4 2).map (fun j => (right0Middle3 5 1) j r) = cols_right0 r := by
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

private def cols_left0Data : List (List ℤ) := [decodeIntegerRow 16 3 1 34344172,
    decodeIntegerRow 16 3 1 17470616,
    decodeIntegerRow 16 3 1 5631784,
    decodeIntegerRow 16 3 1 26992812,
    decodeIntegerRow 16 3 1 8833708,
    decodeIntegerRow 16 3 1 25969784,
    decodeIntegerRow 16 3 1 37519864,
    decodeIntegerRow 16 3 1 16368852,
    decodeIntegerRow 16 3 1 17073068,
    decodeIntegerRow 16 3 1 8835064,
    decodeIntegerRow 16 3 1 26682744,
    decodeIntegerRow 16 3 1 37518292,
    decodeIntegerRow 16 3 1 25580012,
    decodeIntegerRow 16 3 1 34342936,
    decodeIntegerRow 16 3 1 16049064,
    decodeIntegerRow 16 3 1 5633452]

def cols_left0 (r : LeftIndex 3 5 1) : List ℤ := cols_left0Data.getD (leftPosition 3 5 1 r) []

private theorem cols_left0_eq_0_0_0 : (tripleIndices 2 4 2).map (fun j => (left0Middle3 5 1) j ((0 : Fin 8), (0 : Fin 1), (0 : Fin 2))) = cols_left0 ((0 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_1 : (tripleIndices 2 4 2).map (fun j => (left0Middle3 5 1) j ((0 : Fin 8), (0 : Fin 1), (1 : Fin 2))) = cols_left0 ((0 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_0 : (tripleIndices 2 4 2).map (fun j => (left0Middle3 5 1) j ((1 : Fin 8), (0 : Fin 1), (0 : Fin 2))) = cols_left0 ((1 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_1 : (tripleIndices 2 4 2).map (fun j => (left0Middle3 5 1) j ((1 : Fin 8), (0 : Fin 1), (1 : Fin 2))) = cols_left0 ((1 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_0 : (tripleIndices 2 4 2).map (fun j => (left0Middle3 5 1) j ((2 : Fin 8), (0 : Fin 1), (0 : Fin 2))) = cols_left0 ((2 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_1 : (tripleIndices 2 4 2).map (fun j => (left0Middle3 5 1) j ((2 : Fin 8), (0 : Fin 1), (1 : Fin 2))) = cols_left0 ((2 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_0 : (tripleIndices 2 4 2).map (fun j => (left0Middle3 5 1) j ((3 : Fin 8), (0 : Fin 1), (0 : Fin 2))) = cols_left0 ((3 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_1 : (tripleIndices 2 4 2).map (fun j => (left0Middle3 5 1) j ((3 : Fin 8), (0 : Fin 1), (1 : Fin 2))) = cols_left0 ((3 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_4_0_0 : (tripleIndices 2 4 2).map (fun j => (left0Middle3 5 1) j ((4 : Fin 8), (0 : Fin 1), (0 : Fin 2))) = cols_left0 ((4 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_4_0_1 : (tripleIndices 2 4 2).map (fun j => (left0Middle3 5 1) j ((4 : Fin 8), (0 : Fin 1), (1 : Fin 2))) = cols_left0 ((4 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_5_0_0 : (tripleIndices 2 4 2).map (fun j => (left0Middle3 5 1) j ((5 : Fin 8), (0 : Fin 1), (0 : Fin 2))) = cols_left0 ((5 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_5_0_1 : (tripleIndices 2 4 2).map (fun j => (left0Middle3 5 1) j ((5 : Fin 8), (0 : Fin 1), (1 : Fin 2))) = cols_left0 ((5 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_6_0_0 : (tripleIndices 2 4 2).map (fun j => (left0Middle3 5 1) j ((6 : Fin 8), (0 : Fin 1), (0 : Fin 2))) = cols_left0 ((6 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_6_0_1 : (tripleIndices 2 4 2).map (fun j => (left0Middle3 5 1) j ((6 : Fin 8), (0 : Fin 1), (1 : Fin 2))) = cols_left0 ((6 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_7_0_0 : (tripleIndices 2 4 2).map (fun j => (left0Middle3 5 1) j ((7 : Fin 8), (0 : Fin 1), (0 : Fin 2))) = cols_left0 ((7 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_7_0_1 : (tripleIndices 2 4 2).map (fun j => (left0Middle3 5 1) j ((7 : Fin 8), (0 : Fin 1), (1 : Fin 2))) = cols_left0 ((7 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_left0_data (r : LeftIndex 3 5 1) : (tripleIndices 2 4 2).map (fun j => (left0Middle3 5 1) j r) = cols_left0 r := by
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

private def cols_right2Data : List (List ℤ) := [decodeIntegerRow 16 5 2 75707851564,
    decodeIntegerRow 16 5 2 73872101572,
    decodeIntegerRow 16 5 2 88504876612,
    decodeIntegerRow 16 5 2 137328321812,
    decodeIntegerRow 16 5 2 76684726564,
    decodeIntegerRow 16 5 2 78754851572,
    decodeIntegerRow 16 5 2 88497064012,
    decodeIntegerRow 16 5 2 137329883812,
    decodeIntegerRow 16 5 2 15258008812,
    decodeIntegerRow 16 5 2 88497076612,
    decodeIntegerRow 16 5 2 78754914052,
    decodeIntegerRow 16 5 2 75903476564,
    decodeIntegerRow 16 5 2 15259571812,
    decodeIntegerRow 16 5 2 88504889012,
    decodeIntegerRow 16 5 2 73872039052,
    decodeIntegerRow 16 5 2 76879726564]

def cols_right2 (r : LeftIndex 3 5 1) : List ℤ := cols_right2Data.getD (leftPosition 3 5 1 r) []

private theorem cols_right2_eq_0_0_0 : (tripleIndices 2 4 2).map (fun j => (right2Middle3 5 1) j ((0 : Fin 8), (0 : Fin 1), (0 : Fin 2))) = cols_right2 ((0 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_1 : (tripleIndices 2 4 2).map (fun j => (right2Middle3 5 1) j ((0 : Fin 8), (0 : Fin 1), (1 : Fin 2))) = cols_right2 ((0 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_0 : (tripleIndices 2 4 2).map (fun j => (right2Middle3 5 1) j ((1 : Fin 8), (0 : Fin 1), (0 : Fin 2))) = cols_right2 ((1 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_1 : (tripleIndices 2 4 2).map (fun j => (right2Middle3 5 1) j ((1 : Fin 8), (0 : Fin 1), (1 : Fin 2))) = cols_right2 ((1 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_0 : (tripleIndices 2 4 2).map (fun j => (right2Middle3 5 1) j ((2 : Fin 8), (0 : Fin 1), (0 : Fin 2))) = cols_right2 ((2 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_1 : (tripleIndices 2 4 2).map (fun j => (right2Middle3 5 1) j ((2 : Fin 8), (0 : Fin 1), (1 : Fin 2))) = cols_right2 ((2 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_0 : (tripleIndices 2 4 2).map (fun j => (right2Middle3 5 1) j ((3 : Fin 8), (0 : Fin 1), (0 : Fin 2))) = cols_right2 ((3 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_1 : (tripleIndices 2 4 2).map (fun j => (right2Middle3 5 1) j ((3 : Fin 8), (0 : Fin 1), (1 : Fin 2))) = cols_right2 ((3 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_4_0_0 : (tripleIndices 2 4 2).map (fun j => (right2Middle3 5 1) j ((4 : Fin 8), (0 : Fin 1), (0 : Fin 2))) = cols_right2 ((4 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_4_0_1 : (tripleIndices 2 4 2).map (fun j => (right2Middle3 5 1) j ((4 : Fin 8), (0 : Fin 1), (1 : Fin 2))) = cols_right2 ((4 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_5_0_0 : (tripleIndices 2 4 2).map (fun j => (right2Middle3 5 1) j ((5 : Fin 8), (0 : Fin 1), (0 : Fin 2))) = cols_right2 ((5 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_5_0_1 : (tripleIndices 2 4 2).map (fun j => (right2Middle3 5 1) j ((5 : Fin 8), (0 : Fin 1), (1 : Fin 2))) = cols_right2 ((5 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_6_0_0 : (tripleIndices 2 4 2).map (fun j => (right2Middle3 5 1) j ((6 : Fin 8), (0 : Fin 1), (0 : Fin 2))) = cols_right2 ((6 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_6_0_1 : (tripleIndices 2 4 2).map (fun j => (right2Middle3 5 1) j ((6 : Fin 8), (0 : Fin 1), (1 : Fin 2))) = cols_right2 ((6 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_7_0_0 : (tripleIndices 2 4 2).map (fun j => (right2Middle3 5 1) j ((7 : Fin 8), (0 : Fin 1), (0 : Fin 2))) = cols_right2 ((7 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_7_0_1 : (tripleIndices 2 4 2).map (fun j => (right2Middle3 5 1) j ((7 : Fin 8), (0 : Fin 1), (1 : Fin 2))) = cols_right2 ((7 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right2_data (r : LeftIndex 3 5 1) : (tripleIndices 2 4 2).map (fun j => (right2Middle3 5 1) j r) = cols_right2 r := by
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

theorem product0_eq : HexagonAtoms351.outerABC * HexagonAtoms351.assocABC = HexagonAtoms351.assocABC :=
  Matrix.one_mul (m := Fin 2 × Fin 4 × Fin 2) (n := Fin 8 × Fin 1 × Fin 2) _

theorem product1_eq : HexagonAtoms351.assocBAC * HexagonAtoms351.innerABC = HexagonAtoms351.assocBAC :=
  Matrix.mul_one (m := Fin 2 × Fin 4 × Fin 2) (n := Fin 8 × Fin 1 × Fin 2) _

theorem product2_eq : HexagonAtoms351.innerRightABC * HexagonAtoms351.assocABC = HexagonAtoms351.assocABC :=
  Matrix.one_mul (m := Fin 2 × Fin 4 × Fin 2) (n := Fin 8 × Fin 1 × Fin 2) _

theorem product3_eq : HexagonAtoms351.inverseACB * right0Middle3 5 1 = rowColumnMul rows_inverseACB cols_right0 :=
  (rowColumnMul_eq _ _ _ _ rows_inverseACB_data cols_right0_data).symm

theorem product4_eq : HexagonAtoms351.innerACB * right1Middle3 5 1 = right1Middle3 5 1 :=
  Matrix.one_mul (m := Fin 2 × Fin 4 × Fin 2) (n := Fin 8 × Fin 1 × Fin 2) _

theorem product5_eq : HexagonAtoms351.assocBCA * left0Middle3 5 1 = rowColumnMul rows_assocBCA cols_left0 :=
  (rowColumnMul_eq _ _ _ _ rows_assocBCA_data cols_left0_data).symm

theorem product6_eq : HexagonAtoms351.innerRightBAC * left1Middle3 5 1 = left1Middle3 5 1 :=
  Matrix.one_mul (m := Fin 2 × Fin 4 × Fin 2) (n := Fin 8 × Fin 1 × Fin 2) _

theorem product7_eq : HexagonAtoms351.assocCAB * right2Middle3 5 1 = rowColumnMul rows_assocCAB cols_right2 :=
  (rowColumnMul_eq _ _ _ _ rows_assocCAB_data cols_right2_data).symm

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn351
