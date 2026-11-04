import RMod.BrundanEllis.StackingReferenceHexagonAtoms513
import RMod.BrundanEllis.StackingReferenceHexagonMiddle5
import RMod.BrundanEllis.StackingReferenceRowColumnCheck

/-! Verified row and column lists. Each subsequent scalar product traverses
these lists directly, without repeated lookup into the original matrices. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn513
open Superfusion

private def rows_inverseACBData : List (List ℤ) := [decodeIntegerRow 16 3 1 20812586,
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

def rows_inverseACB (r : LeftIndex 5 3 1) : List ℤ := rows_inverseACBData.getD (leftPosition 5 3 1 r) []

private theorem rows_inverseACB_eq_0_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms513.inverseACB) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 2))) = rows_inverseACB ((0 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms513.inverseACB) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 2))) = rows_inverseACB ((0 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms513.inverseACB) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 2))) = rows_inverseACB ((1 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms513.inverseACB) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 2))) = rows_inverseACB ((1 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms513.inverseACB) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 2))) = rows_inverseACB ((2 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms513.inverseACB) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 2))) = rows_inverseACB ((2 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms513.inverseACB) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 2))) = rows_inverseACB ((3 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms513.inverseACB) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 2))) = rows_inverseACB ((3 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_4_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms513.inverseACB) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 2))) = rows_inverseACB ((4 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_4_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms513.inverseACB) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 2))) = rows_inverseACB ((4 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_5_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms513.inverseACB) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 2))) = rows_inverseACB ((5 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_5_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms513.inverseACB) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 2))) = rows_inverseACB ((5 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_6_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms513.inverseACB) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 2))) = rows_inverseACB ((6 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_6_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms513.inverseACB) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 2))) = rows_inverseACB ((6 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_7_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms513.inverseACB) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 2))) = rows_inverseACB ((7 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_7_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms513.inverseACB) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 2))) = rows_inverseACB ((7 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_inverseACB_data (r : LeftIndex 5 3 1) : (tripleIndices 2 4 2).map ((HexagonAtoms513.inverseACB) r) = rows_inverseACB r := by
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

private def rows_assocBCAData : List (List ℤ) := [decodeIntegerRow 16 3 1 20812586,
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

def rows_assocBCA (r : RightIndex 1 3 5) : List ℤ := rows_assocBCAData.getD (rightPosition 1 3 5 r) []

private theorem rows_assocBCA_eq_0_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms513.assocBCA) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 2))) = rows_assocBCA ((0 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms513.assocBCA) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 2))) = rows_assocBCA ((0 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms513.assocBCA) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 2))) = rows_assocBCA ((1 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms513.assocBCA) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 2))) = rows_assocBCA ((1 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms513.assocBCA) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 2))) = rows_assocBCA ((2 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms513.assocBCA) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 2))) = rows_assocBCA ((2 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms513.assocBCA) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 2))) = rows_assocBCA ((3 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms513.assocBCA) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 2))) = rows_assocBCA ((3 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_4_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms513.assocBCA) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 2))) = rows_assocBCA ((4 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_4_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms513.assocBCA) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 2))) = rows_assocBCA ((4 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_5_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms513.assocBCA) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 2))) = rows_assocBCA ((5 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_5_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms513.assocBCA) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 2))) = rows_assocBCA ((5 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_6_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms513.assocBCA) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 2))) = rows_assocBCA ((6 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_6_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms513.assocBCA) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 2))) = rows_assocBCA ((6 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_7_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms513.assocBCA) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 2))) = rows_assocBCA ((7 : Fin 8), (0 : Fin 1), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_7_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms513.assocBCA) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 2))) = rows_assocBCA ((7 : Fin 8), (0 : Fin 1), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocBCA_data (r : RightIndex 1 3 5) : (tripleIndices 2 4 2).map ((HexagonAtoms513.assocBCA) r) = rows_assocBCA r := by
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

private def rows_assocCABData : List (List ℤ) := [decodeIntegerRow 16 3 1 17217376,
    decodeIntegerRow 16 3 1 8611968,
    decodeIntegerRow 16 3 1 26905840,
    decodeIntegerRow 16 3 1 37662600,
    decodeIntegerRow 16 3 1 37270560,
    decodeIntegerRow 16 3 1 16276960,
    decodeIntegerRow 16 3 1 34121120,
    decodeIntegerRow 16 3 1 17326240,
    decodeIntegerRow 16 3 1 8610656,
    decodeIntegerRow 16 3 1 25825408,
    decodeIntegerRow 16 3 1 37664240,
    decodeIntegerRow 16 3 1 16145800,
    decodeIntegerRow 16 3 1 16272160,
    decodeIntegerRow 16 3 1 5777760,
    decodeIntegerRow 16 3 1 17322400,
    decodeIntegerRow 16 3 1 8926880]

def rows_assocCAB (r : RightIndex 3 5 1) : List ℤ := rows_assocCABData.getD (rightPosition 3 5 1 r) []

private theorem rows_assocCAB_eq_0_0_0 : (tripleIndices 8 1 2).map ((HexagonAtoms513.assocCAB) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_1 : (tripleIndices 8 1 2).map ((HexagonAtoms513.assocCAB) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_0 : (tripleIndices 8 1 2).map ((HexagonAtoms513.assocCAB) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = rows_assocCAB ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_1 : (tripleIndices 8 1 2).map ((HexagonAtoms513.assocCAB) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = rows_assocCAB ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_2_0 : (tripleIndices 8 1 2).map ((HexagonAtoms513.assocCAB) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = rows_assocCAB ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_2_1 : (tripleIndices 8 1 2).map ((HexagonAtoms513.assocCAB) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = rows_assocCAB ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_3_0 : (tripleIndices 8 1 2).map ((HexagonAtoms513.assocCAB) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = rows_assocCAB ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_3_1 : (tripleIndices 8 1 2).map ((HexagonAtoms513.assocCAB) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = rows_assocCAB ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_0 : (tripleIndices 8 1 2).map ((HexagonAtoms513.assocCAB) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_1 : (tripleIndices 8 1 2).map ((HexagonAtoms513.assocCAB) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_0 : (tripleIndices 8 1 2).map ((HexagonAtoms513.assocCAB) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = rows_assocCAB ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_1 : (tripleIndices 8 1 2).map ((HexagonAtoms513.assocCAB) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = rows_assocCAB ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_2_0 : (tripleIndices 8 1 2).map ((HexagonAtoms513.assocCAB) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = rows_assocCAB ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_2_1 : (tripleIndices 8 1 2).map ((HexagonAtoms513.assocCAB) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = rows_assocCAB ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_3_0 : (tripleIndices 8 1 2).map ((HexagonAtoms513.assocCAB) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = rows_assocCAB ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_3_1 : (tripleIndices 8 1 2).map ((HexagonAtoms513.assocCAB) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = rows_assocCAB ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocCAB_data (r : RightIndex 3 5 1) : (tripleIndices 8 1 2).map ((HexagonAtoms513.assocCAB) r) = rows_assocCAB r := by
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

private def cols_right0Data : List (List ℤ) := [decodeIntegerRow 16 3 1 35872264,
    decodeIntegerRow 16 3 1 16740392,
    decodeIntegerRow 16 3 1 21464230,
    decodeIntegerRow 16 3 1 21345970,
    decodeIntegerRow 16 3 1 20991928,
    decodeIntegerRow 16 3 1 19929064,
    decodeIntegerRow 16 3 1 21545230,
    decodeIntegerRow 16 3 1 21516070,
    decodeIntegerRow 16 3 1 21700264,
    decodeIntegerRow 16 3 1 21464392,
    decodeIntegerRow 16 3 1 16740390,
    decodeIntegerRow 16 3 1 7174450,
    decodeIntegerRow 16 3 1 21529192,
    decodeIntegerRow 16 3 1 21540856,
    decodeIntegerRow 16 3 1 19929010,
    decodeIntegerRow 16 3 1 22054810]

def cols_right0 (r : LeftIndex 5 1 3) : List ℤ := cols_right0Data.getD (leftPosition 5 1 3 r) []

private theorem cols_right0_eq_0_0_0 : (tripleIndices 2 4 2).map (fun j => (right0Middle5 1 3) j ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = cols_right0 ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_1 : (tripleIndices 2 4 2).map (fun j => (right0Middle5 1 3) j ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = cols_right0 ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_0 : (tripleIndices 2 4 2).map (fun j => (right0Middle5 1 3) j ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = cols_right0 ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_1 : (tripleIndices 2 4 2).map (fun j => (right0Middle5 1 3) j ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = cols_right0 ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_2_0 : (tripleIndices 2 4 2).map (fun j => (right0Middle5 1 3) j ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = cols_right0 ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_2_1 : (tripleIndices 2 4 2).map (fun j => (right0Middle5 1 3) j ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = cols_right0 ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_3_0 : (tripleIndices 2 4 2).map (fun j => (right0Middle5 1 3) j ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = cols_right0 ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_3_1 : (tripleIndices 2 4 2).map (fun j => (right0Middle5 1 3) j ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = cols_right0 ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_0 : (tripleIndices 2 4 2).map (fun j => (right0Middle5 1 3) j ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = cols_right0 ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_1 : (tripleIndices 2 4 2).map (fun j => (right0Middle5 1 3) j ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = cols_right0 ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_0 : (tripleIndices 2 4 2).map (fun j => (right0Middle5 1 3) j ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = cols_right0 ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_1 : (tripleIndices 2 4 2).map (fun j => (right0Middle5 1 3) j ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = cols_right0 ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_2_0 : (tripleIndices 2 4 2).map (fun j => (right0Middle5 1 3) j ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = cols_right0 ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_2_1 : (tripleIndices 2 4 2).map (fun j => (right0Middle5 1 3) j ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = cols_right0 ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_3_0 : (tripleIndices 2 4 2).map (fun j => (right0Middle5 1 3) j ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = cols_right0 ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_3_1 : (tripleIndices 2 4 2).map (fun j => (right0Middle5 1 3) j ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = cols_right0 ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right0_data (r : LeftIndex 5 1 3) : (tripleIndices 2 4 2).map (fun j => (right0Middle5 1 3) j r) = cols_right0 r := by
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

private def cols_left0Data : List (List ℤ) := [decodeIntegerRow 16 3 1 35872264,
    decodeIntegerRow 16 3 1 16740392,
    decodeIntegerRow 16 3 1 21464230,
    decodeIntegerRow 16 3 1 21345970,
    decodeIntegerRow 16 3 1 20991928,
    decodeIntegerRow 16 3 1 19929064,
    decodeIntegerRow 16 3 1 21545230,
    decodeIntegerRow 16 3 1 21516070,
    decodeIntegerRow 16 3 1 21700264,
    decodeIntegerRow 16 3 1 21464392,
    decodeIntegerRow 16 3 1 16740390,
    decodeIntegerRow 16 3 1 7174450,
    decodeIntegerRow 16 3 1 21529192,
    decodeIntegerRow 16 3 1 21540856,
    decodeIntegerRow 16 3 1 19929010,
    decodeIntegerRow 16 3 1 22054810]

def cols_left0 (r : LeftIndex 5 1 3) : List ℤ := cols_left0Data.getD (leftPosition 5 1 3 r) []

private theorem cols_left0_eq_0_0_0 : (tripleIndices 2 4 2).map (fun j => (left0Middle5 1 3) j ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = cols_left0 ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_1 : (tripleIndices 2 4 2).map (fun j => (left0Middle5 1 3) j ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = cols_left0 ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_0 : (tripleIndices 2 4 2).map (fun j => (left0Middle5 1 3) j ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = cols_left0 ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_1 : (tripleIndices 2 4 2).map (fun j => (left0Middle5 1 3) j ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = cols_left0 ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_2_0 : (tripleIndices 2 4 2).map (fun j => (left0Middle5 1 3) j ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = cols_left0 ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_2_1 : (tripleIndices 2 4 2).map (fun j => (left0Middle5 1 3) j ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = cols_left0 ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_3_0 : (tripleIndices 2 4 2).map (fun j => (left0Middle5 1 3) j ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = cols_left0 ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_3_1 : (tripleIndices 2 4 2).map (fun j => (left0Middle5 1 3) j ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = cols_left0 ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_0 : (tripleIndices 2 4 2).map (fun j => (left0Middle5 1 3) j ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = cols_left0 ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_1 : (tripleIndices 2 4 2).map (fun j => (left0Middle5 1 3) j ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = cols_left0 ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_0 : (tripleIndices 2 4 2).map (fun j => (left0Middle5 1 3) j ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = cols_left0 ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_1 : (tripleIndices 2 4 2).map (fun j => (left0Middle5 1 3) j ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = cols_left0 ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_2_0 : (tripleIndices 2 4 2).map (fun j => (left0Middle5 1 3) j ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = cols_left0 ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_2_1 : (tripleIndices 2 4 2).map (fun j => (left0Middle5 1 3) j ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = cols_left0 ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_3_0 : (tripleIndices 2 4 2).map (fun j => (left0Middle5 1 3) j ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = cols_left0 ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_3_1 : (tripleIndices 2 4 2).map (fun j => (left0Middle5 1 3) j ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = cols_left0 ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_left0_data (r : LeftIndex 5 1 3) : (tripleIndices 2 4 2).map (fun j => (left0Middle5 1 3) j r) = cols_left0 r := by
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

private def cols_right2Data : List (List ℤ) := [decodeIntegerRow 16 3 1 25829344,
    decodeIntegerRow 16 3 1 34434752,
    decodeIntegerRow 16 3 1 16140880,
    decodeIntegerRow 16 3 1 5384120,
    decodeIntegerRow 16 3 1 5776160,
    decodeIntegerRow 16 3 1 26769760,
    decodeIntegerRow 16 3 1 8925600,
    decodeIntegerRow 16 3 1 25720480,
    decodeIntegerRow 16 3 1 34436064,
    decodeIntegerRow 16 3 1 17221312,
    decodeIntegerRow 16 3 1 5382480,
    decodeIntegerRow 16 3 1 26900920,
    decodeIntegerRow 16 3 1 26774560,
    decodeIntegerRow 16 3 1 37268960,
    decodeIntegerRow 16 3 1 25724320,
    decodeIntegerRow 16 3 1 34119840]

def cols_right2 (r : LeftIndex 5 1 3) : List ℤ := cols_right2Data.getD (leftPosition 5 1 3 r) []

private theorem cols_right2_eq_0_0_0 : (tripleIndices 8 1 2).map (fun j => (right2Middle5 1 3) j ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = cols_right2 ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_1 : (tripleIndices 8 1 2).map (fun j => (right2Middle5 1 3) j ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = cols_right2 ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_0 : (tripleIndices 8 1 2).map (fun j => (right2Middle5 1 3) j ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = cols_right2 ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_1 : (tripleIndices 8 1 2).map (fun j => (right2Middle5 1 3) j ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = cols_right2 ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_2_0 : (tripleIndices 8 1 2).map (fun j => (right2Middle5 1 3) j ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = cols_right2 ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_2_1 : (tripleIndices 8 1 2).map (fun j => (right2Middle5 1 3) j ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = cols_right2 ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_3_0 : (tripleIndices 8 1 2).map (fun j => (right2Middle5 1 3) j ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = cols_right2 ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_3_1 : (tripleIndices 8 1 2).map (fun j => (right2Middle5 1 3) j ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = cols_right2 ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_0 : (tripleIndices 8 1 2).map (fun j => (right2Middle5 1 3) j ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = cols_right2 ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_1 : (tripleIndices 8 1 2).map (fun j => (right2Middle5 1 3) j ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = cols_right2 ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_0 : (tripleIndices 8 1 2).map (fun j => (right2Middle5 1 3) j ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = cols_right2 ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_1 : (tripleIndices 8 1 2).map (fun j => (right2Middle5 1 3) j ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = cols_right2 ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_2_0 : (tripleIndices 8 1 2).map (fun j => (right2Middle5 1 3) j ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = cols_right2 ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_2_1 : (tripleIndices 8 1 2).map (fun j => (right2Middle5 1 3) j ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = cols_right2 ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_3_0 : (tripleIndices 8 1 2).map (fun j => (right2Middle5 1 3) j ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = cols_right2 ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_3_1 : (tripleIndices 8 1 2).map (fun j => (right2Middle5 1 3) j ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = cols_right2 ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right2_data (r : LeftIndex 5 1 3) : (tripleIndices 8 1 2).map (fun j => (right2Middle5 1 3) j r) = cols_right2 r := by
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

theorem product0_eq : HexagonAtoms513.outerABC * HexagonAtoms513.assocABC = HexagonAtoms513.assocABC :=
  Matrix.one_mul (m := Fin 2 × Fin 4 × Fin 2) (n := Fin 2 × Fin 4 × Fin 2) _

theorem product1_eq : HexagonAtoms513.assocBAC * HexagonAtoms513.innerABC = HexagonAtoms513.assocBAC :=
  Matrix.mul_one (m := Fin 8 × Fin 1 × Fin 2) (n := Fin 2 × Fin 4 × Fin 2) _

theorem product2_eq : HexagonAtoms513.innerRightABC * HexagonAtoms513.assocABC = HexagonAtoms513.assocABC :=
  Matrix.one_mul (m := Fin 2 × Fin 4 × Fin 2) (n := Fin 2 × Fin 4 × Fin 2) _

theorem product3_eq : HexagonAtoms513.inverseACB * right0Middle5 1 3 = rowColumnMul rows_inverseACB cols_right0 :=
  (rowColumnMul_eq _ _ _ _ rows_inverseACB_data cols_right0_data).symm

theorem product4_eq : HexagonAtoms513.innerACB * right1Middle5 1 3 = right1Middle5 1 3 :=
  Matrix.one_mul (m := Fin 8 × Fin 1 × Fin 2) (n := Fin 2 × Fin 4 × Fin 2) _

theorem product5_eq : HexagonAtoms513.assocBCA * left0Middle5 1 3 = rowColumnMul rows_assocBCA cols_left0 :=
  (rowColumnMul_eq _ _ _ _ rows_assocBCA_data cols_left0_data).symm

theorem product6_eq : HexagonAtoms513.innerRightBAC * left1Middle5 1 3 = left1Middle5 1 3 :=
  Matrix.one_mul (m := Fin 8 × Fin 1 × Fin 2) (n := Fin 2 × Fin 4 × Fin 2) _

theorem product7_eq : HexagonAtoms513.assocCAB * right2Middle5 1 3 = rowColumnMul rows_assocCAB cols_right2 :=
  (rowColumnMul_eq _ _ _ _ rows_assocCAB_data cols_right2_data).symm

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn513
