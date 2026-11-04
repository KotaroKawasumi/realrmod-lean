import RMod.BrundanEllis.StackingReferenceHexagonAtoms416
import RMod.BrundanEllis.StackingReferenceHexagonMiddle4
import RMod.BrundanEllis.StackingReferenceRowColumnCheck

/-! Verified row and column lists. Each subsequent scalar product traverses
these lists directly, without repeated lookup into the original matrices. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn416
open Superfusion

private def rows_inverseACBData : List (List ℤ) := [decodeIntegerRow 16 3 1 21516718,
    decodeIntegerRow 16 3 1 21503920,
    decodeIntegerRow 16 3 1 21465040,
    decodeIntegerRow 16 3 1 21344026,
    decodeIntegerRow 16 3 1 20991920,
    decodeIntegerRow 16 3 1 19929034,
    decodeIntegerRow 16 3 1 16740382,
    decodeIntegerRow 16 3 1 7174480,
    decodeIntegerRow 16 3 1 20991918,
    decodeIntegerRow 16 3 1 23117680,
    decodeIntegerRow 16 3 1 26306320,
    decodeIntegerRow 16 3 1 7174426,
    decodeIntegerRow 16 3 1 21529840,
    decodeIntegerRow 16 3 1 21503434,
    decodeIntegerRow 16 3 1 21463582,
    decodeIntegerRow 16 3 1 21698320]

def rows_inverseACB (r : LeftIndex 4 6 1) : List ℤ := rows_inverseACBData.getD (leftPosition 4 6 1 r) []

private theorem rows_inverseACB_eq_0_0_0 : (tripleIndices 2 1 8).map ((HexagonAtoms416.inverseACB) ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_1 : (tripleIndices 2 1 8).map ((HexagonAtoms416.inverseACB) ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_2 : (tripleIndices 2 1 8).map ((HexagonAtoms416.inverseACB) ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_3 : (tripleIndices 2 1 8).map ((HexagonAtoms416.inverseACB) ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_4 : (tripleIndices 2 1 8).map ((HexagonAtoms416.inverseACB) ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_5 : (tripleIndices 2 1 8).map ((HexagonAtoms416.inverseACB) ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_6 : (tripleIndices 2 1 8).map ((HexagonAtoms416.inverseACB) ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_7 : (tripleIndices 2 1 8).map ((HexagonAtoms416.inverseACB) ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_0 : (tripleIndices 2 1 8).map ((HexagonAtoms416.inverseACB) ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_1 : (tripleIndices 2 1 8).map ((HexagonAtoms416.inverseACB) ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_2 : (tripleIndices 2 1 8).map ((HexagonAtoms416.inverseACB) ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_3 : (tripleIndices 2 1 8).map ((HexagonAtoms416.inverseACB) ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_4 : (tripleIndices 2 1 8).map ((HexagonAtoms416.inverseACB) ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_5 : (tripleIndices 2 1 8).map ((HexagonAtoms416.inverseACB) ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_6 : (tripleIndices 2 1 8).map ((HexagonAtoms416.inverseACB) ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_7 : (tripleIndices 2 1 8).map ((HexagonAtoms416.inverseACB) ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_inverseACB_data (r : LeftIndex 4 6 1) : (tripleIndices 2 1 8).map ((HexagonAtoms416.inverseACB) r) = rows_inverseACB r := by
  fin_cases r
  · exact rows_inverseACB_eq_0_0_0
  · exact rows_inverseACB_eq_0_0_1
  · exact rows_inverseACB_eq_0_0_2
  · exact rows_inverseACB_eq_0_0_3
  · exact rows_inverseACB_eq_0_0_4
  · exact rows_inverseACB_eq_0_0_5
  · exact rows_inverseACB_eq_0_0_6
  · exact rows_inverseACB_eq_0_0_7
  · exact rows_inverseACB_eq_1_0_0
  · exact rows_inverseACB_eq_1_0_1
  · exact rows_inverseACB_eq_1_0_2
  · exact rows_inverseACB_eq_1_0_3
  · exact rows_inverseACB_eq_1_0_4
  · exact rows_inverseACB_eq_1_0_5
  · exact rows_inverseACB_eq_1_0_6
  · exact rows_inverseACB_eq_1_0_7

private def rows_assocBCAData : List (List ℤ) := [decodeIntegerRow 16 3 1 18162016,
    decodeIntegerRow 16 3 1 7667040,
    decodeIntegerRow 16 3 1 6720800,
    decodeIntegerRow 16 3 1 15332032,
    decodeIntegerRow 16 3 1 7744800,
    decodeIntegerRow 16 3 1 18507400,
    decodeIntegerRow 16 3 1 28086640,
    decodeIntegerRow 16 3 1 36481440,
    decodeIntegerRow 16 3 1 7666016,
    decodeIntegerRow 16 3 1 24880480,
    decodeIntegerRow 16 3 1 15327520,
    decodeIntegerRow 16 3 1 36324032,
    decodeIntegerRow 16 3 1 18503200,
    decodeIntegerRow 16 3 1 35301000,
    decodeIntegerRow 16 3 1 36483440,
    decodeIntegerRow 16 3 1 14964640]

def rows_assocBCA (r : RightIndex 1 6 4) : List ℤ := rows_assocBCAData.getD (rightPosition 1 6 4 r) []

private theorem rows_assocBCA_eq_0_0_0 : (tripleIndices 2 1 8).map ((HexagonAtoms416.assocBCA) ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8))) = rows_assocBCA ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_1 : (tripleIndices 2 1 8).map ((HexagonAtoms416.assocBCA) ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8))) = rows_assocBCA ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_2 : (tripleIndices 2 1 8).map ((HexagonAtoms416.assocBCA) ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8))) = rows_assocBCA ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_3 : (tripleIndices 2 1 8).map ((HexagonAtoms416.assocBCA) ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8))) = rows_assocBCA ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_4 : (tripleIndices 2 1 8).map ((HexagonAtoms416.assocBCA) ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8))) = rows_assocBCA ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_5 : (tripleIndices 2 1 8).map ((HexagonAtoms416.assocBCA) ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8))) = rows_assocBCA ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_6 : (tripleIndices 2 1 8).map ((HexagonAtoms416.assocBCA) ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8))) = rows_assocBCA ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_7 : (tripleIndices 2 1 8).map ((HexagonAtoms416.assocBCA) ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8))) = rows_assocBCA ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_0 : (tripleIndices 2 1 8).map ((HexagonAtoms416.assocBCA) ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8))) = rows_assocBCA ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_1 : (tripleIndices 2 1 8).map ((HexagonAtoms416.assocBCA) ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8))) = rows_assocBCA ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_2 : (tripleIndices 2 1 8).map ((HexagonAtoms416.assocBCA) ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8))) = rows_assocBCA ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_3 : (tripleIndices 2 1 8).map ((HexagonAtoms416.assocBCA) ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8))) = rows_assocBCA ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_4 : (tripleIndices 2 1 8).map ((HexagonAtoms416.assocBCA) ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8))) = rows_assocBCA ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_5 : (tripleIndices 2 1 8).map ((HexagonAtoms416.assocBCA) ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8))) = rows_assocBCA ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_6 : (tripleIndices 2 1 8).map ((HexagonAtoms416.assocBCA) ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8))) = rows_assocBCA ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_7 : (tripleIndices 2 1 8).map ((HexagonAtoms416.assocBCA) ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8))) = rows_assocBCA ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocBCA_data (r : RightIndex 1 6 4) : (tripleIndices 2 1 8).map ((HexagonAtoms416.assocBCA) r) = rows_assocBCA r := by
  fin_cases r
  · exact rows_assocBCA_eq_0_0_0
  · exact rows_assocBCA_eq_0_0_1
  · exact rows_assocBCA_eq_0_0_2
  · exact rows_assocBCA_eq_0_0_3
  · exact rows_assocBCA_eq_0_0_4
  · exact rows_assocBCA_eq_0_0_5
  · exact rows_assocBCA_eq_0_0_6
  · exact rows_assocBCA_eq_0_0_7
  · exact rows_assocBCA_eq_1_0_0
  · exact rows_assocBCA_eq_1_0_1
  · exact rows_assocBCA_eq_1_0_2
  · exact rows_assocBCA_eq_1_0_3
  · exact rows_assocBCA_eq_1_0_4
  · exact rows_assocBCA_eq_1_0_5
  · exact rows_assocBCA_eq_1_0_6
  · exact rows_assocBCA_eq_1_0_7

private def rows_assocCABData : List (List ℤ) := [decodeIntegerRow 16 3 1 16740394,
    decodeIntegerRow 16 3 1 7174452,
    decodeIntegerRow 16 3 1 20991946,
    decodeIntegerRow 16 3 1 19929028,
    decodeIntegerRow 16 3 1 21582652,
    decodeIntegerRow 16 3 1 21700426,
    decodeIntegerRow 16 3 1 21532108,
    decodeIntegerRow 16 3 1 21542314,
    decodeIntegerRow 16 3 1 7174454,
    decodeIntegerRow 16 3 1 26306332,
    decodeIntegerRow 16 3 1 19929046,
    decodeIntegerRow 16 3 1 22054828,
    decodeIntegerRow 16 3 1 21700588,
    decodeIntegerRow 16 3 1 21464554,
    decodeIntegerRow 16 3 1 21543772,
    decodeIntegerRow 16 3 1 21518986]

def rows_assocCAB (r : RightIndex 6 4 1) : List ℤ := rows_assocCABData.getD (rightPosition 6 4 1 r) []

private theorem rows_assocCAB_eq_0_0_0 : (tripleIndices 2 1 8).map ((HexagonAtoms416.assocCAB) ((0 : Fin 1), (0 : Fin 2), (0 : Fin 8))) = rows_assocCAB ((0 : Fin 1), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_1 : (tripleIndices 2 1 8).map ((HexagonAtoms416.assocCAB) ((0 : Fin 1), (0 : Fin 2), (1 : Fin 8))) = rows_assocCAB ((0 : Fin 1), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_2 : (tripleIndices 2 1 8).map ((HexagonAtoms416.assocCAB) ((0 : Fin 1), (0 : Fin 2), (2 : Fin 8))) = rows_assocCAB ((0 : Fin 1), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_3 : (tripleIndices 2 1 8).map ((HexagonAtoms416.assocCAB) ((0 : Fin 1), (0 : Fin 2), (3 : Fin 8))) = rows_assocCAB ((0 : Fin 1), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_4 : (tripleIndices 2 1 8).map ((HexagonAtoms416.assocCAB) ((0 : Fin 1), (0 : Fin 2), (4 : Fin 8))) = rows_assocCAB ((0 : Fin 1), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_5 : (tripleIndices 2 1 8).map ((HexagonAtoms416.assocCAB) ((0 : Fin 1), (0 : Fin 2), (5 : Fin 8))) = rows_assocCAB ((0 : Fin 1), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_6 : (tripleIndices 2 1 8).map ((HexagonAtoms416.assocCAB) ((0 : Fin 1), (0 : Fin 2), (6 : Fin 8))) = rows_assocCAB ((0 : Fin 1), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_7 : (tripleIndices 2 1 8).map ((HexagonAtoms416.assocCAB) ((0 : Fin 1), (0 : Fin 2), (7 : Fin 8))) = rows_assocCAB ((0 : Fin 1), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_0 : (tripleIndices 2 1 8).map ((HexagonAtoms416.assocCAB) ((0 : Fin 1), (1 : Fin 2), (0 : Fin 8))) = rows_assocCAB ((0 : Fin 1), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_1 : (tripleIndices 2 1 8).map ((HexagonAtoms416.assocCAB) ((0 : Fin 1), (1 : Fin 2), (1 : Fin 8))) = rows_assocCAB ((0 : Fin 1), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_2 : (tripleIndices 2 1 8).map ((HexagonAtoms416.assocCAB) ((0 : Fin 1), (1 : Fin 2), (2 : Fin 8))) = rows_assocCAB ((0 : Fin 1), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_3 : (tripleIndices 2 1 8).map ((HexagonAtoms416.assocCAB) ((0 : Fin 1), (1 : Fin 2), (3 : Fin 8))) = rows_assocCAB ((0 : Fin 1), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_4 : (tripleIndices 2 1 8).map ((HexagonAtoms416.assocCAB) ((0 : Fin 1), (1 : Fin 2), (4 : Fin 8))) = rows_assocCAB ((0 : Fin 1), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_5 : (tripleIndices 2 1 8).map ((HexagonAtoms416.assocCAB) ((0 : Fin 1), (1 : Fin 2), (5 : Fin 8))) = rows_assocCAB ((0 : Fin 1), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_6 : (tripleIndices 2 1 8).map ((HexagonAtoms416.assocCAB) ((0 : Fin 1), (1 : Fin 2), (6 : Fin 8))) = rows_assocCAB ((0 : Fin 1), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_7 : (tripleIndices 2 1 8).map ((HexagonAtoms416.assocCAB) ((0 : Fin 1), (1 : Fin 2), (7 : Fin 8))) = rows_assocCAB ((0 : Fin 1), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocCAB_data (r : RightIndex 6 4 1) : (tripleIndices 2 1 8).map ((HexagonAtoms416.assocCAB) r) = rows_assocCAB r := by
  fin_cases r
  · exact rows_assocCAB_eq_0_0_0
  · exact rows_assocCAB_eq_0_0_1
  · exact rows_assocCAB_eq_0_0_2
  · exact rows_assocCAB_eq_0_0_3
  · exact rows_assocCAB_eq_0_0_4
  · exact rows_assocCAB_eq_0_0_5
  · exact rows_assocCAB_eq_0_0_6
  · exact rows_assocCAB_eq_0_0_7
  · exact rows_assocCAB_eq_0_1_0
  · exact rows_assocCAB_eq_0_1_1
  · exact rows_assocCAB_eq_0_1_2
  · exact rows_assocCAB_eq_0_1_3
  · exact rows_assocCAB_eq_0_1_4
  · exact rows_assocCAB_eq_0_1_5
  · exact rows_assocCAB_eq_0_1_6
  · exact rows_assocCAB_eq_0_1_7

private def cols_right0Data : List (List ℤ) := [decodeIntegerRow 16 3 1 21483022,
    decodeIntegerRow 16 3 1 21691678,
    decodeIntegerRow 16 3 1 21709174,
    decodeIntegerRow 16 3 1 21445114,
    decodeIntegerRow 16 3 1 18334726,
    decodeIntegerRow 16 3 1 35340854,
    decodeIntegerRow 16 3 1 36403682,
    decodeIntegerRow 16 3 1 15146062,
    decodeIntegerRow 16 3 1 21704962,
    decodeIntegerRow 16 3 1 21602578,
    decodeIntegerRow 16 3 1 21561754,
    decodeIntegerRow 16 3 1 21696214,
    decodeIntegerRow 16 3 1 36403734,
    decodeIntegerRow 16 3 1 27900646,
    decodeIntegerRow 16 3 1 24712018,
    decodeIntegerRow 16 3 1 35340798]

def cols_right0 (r : LeftIndex 4 1 6) : List ℤ := cols_right0Data.getD (leftPosition 4 1 6 r) []

private theorem cols_right0_eq_0_0_0 : (tripleIndices 2 1 8).map (fun j => (right0Middle4 1 6) j ((0 : Fin 1), (0 : Fin 2), (0 : Fin 8))) = cols_right0 ((0 : Fin 1), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_1 : (tripleIndices 2 1 8).map (fun j => (right0Middle4 1 6) j ((0 : Fin 1), (0 : Fin 2), (1 : Fin 8))) = cols_right0 ((0 : Fin 1), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_2 : (tripleIndices 2 1 8).map (fun j => (right0Middle4 1 6) j ((0 : Fin 1), (0 : Fin 2), (2 : Fin 8))) = cols_right0 ((0 : Fin 1), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_3 : (tripleIndices 2 1 8).map (fun j => (right0Middle4 1 6) j ((0 : Fin 1), (0 : Fin 2), (3 : Fin 8))) = cols_right0 ((0 : Fin 1), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_4 : (tripleIndices 2 1 8).map (fun j => (right0Middle4 1 6) j ((0 : Fin 1), (0 : Fin 2), (4 : Fin 8))) = cols_right0 ((0 : Fin 1), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_5 : (tripleIndices 2 1 8).map (fun j => (right0Middle4 1 6) j ((0 : Fin 1), (0 : Fin 2), (5 : Fin 8))) = cols_right0 ((0 : Fin 1), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_6 : (tripleIndices 2 1 8).map (fun j => (right0Middle4 1 6) j ((0 : Fin 1), (0 : Fin 2), (6 : Fin 8))) = cols_right0 ((0 : Fin 1), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_7 : (tripleIndices 2 1 8).map (fun j => (right0Middle4 1 6) j ((0 : Fin 1), (0 : Fin 2), (7 : Fin 8))) = cols_right0 ((0 : Fin 1), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_0 : (tripleIndices 2 1 8).map (fun j => (right0Middle4 1 6) j ((0 : Fin 1), (1 : Fin 2), (0 : Fin 8))) = cols_right0 ((0 : Fin 1), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_1 : (tripleIndices 2 1 8).map (fun j => (right0Middle4 1 6) j ((0 : Fin 1), (1 : Fin 2), (1 : Fin 8))) = cols_right0 ((0 : Fin 1), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_2 : (tripleIndices 2 1 8).map (fun j => (right0Middle4 1 6) j ((0 : Fin 1), (1 : Fin 2), (2 : Fin 8))) = cols_right0 ((0 : Fin 1), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_3 : (tripleIndices 2 1 8).map (fun j => (right0Middle4 1 6) j ((0 : Fin 1), (1 : Fin 2), (3 : Fin 8))) = cols_right0 ((0 : Fin 1), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_4 : (tripleIndices 2 1 8).map (fun j => (right0Middle4 1 6) j ((0 : Fin 1), (1 : Fin 2), (4 : Fin 8))) = cols_right0 ((0 : Fin 1), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_5 : (tripleIndices 2 1 8).map (fun j => (right0Middle4 1 6) j ((0 : Fin 1), (1 : Fin 2), (5 : Fin 8))) = cols_right0 ((0 : Fin 1), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_6 : (tripleIndices 2 1 8).map (fun j => (right0Middle4 1 6) j ((0 : Fin 1), (1 : Fin 2), (6 : Fin 8))) = cols_right0 ((0 : Fin 1), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_7 : (tripleIndices 2 1 8).map (fun j => (right0Middle4 1 6) j ((0 : Fin 1), (1 : Fin 2), (7 : Fin 8))) = cols_right0 ((0 : Fin 1), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right0_data (r : LeftIndex 4 1 6) : (tripleIndices 2 1 8).map (fun j => (right0Middle4 1 6) j r) = cols_right0 r := by
  fin_cases r
  · exact cols_right0_eq_0_0_0
  · exact cols_right0_eq_0_0_1
  · exact cols_right0_eq_0_0_2
  · exact cols_right0_eq_0_0_3
  · exact cols_right0_eq_0_0_4
  · exact cols_right0_eq_0_0_5
  · exact cols_right0_eq_0_0_6
  · exact cols_right0_eq_0_0_7
  · exact cols_right0_eq_0_1_0
  · exact cols_right0_eq_0_1_1
  · exact cols_right0_eq_0_1_2
  · exact cols_right0_eq_0_1_3
  · exact cols_right0_eq_0_1_4
  · exact cols_right0_eq_0_1_5
  · exact cols_right0_eq_0_1_6
  · exact cols_right0_eq_0_1_7

private def cols_left0Data : List (List ℤ) := [decodeIntegerRow 16 3 1 21483022,
    decodeIntegerRow 16 3 1 21691678,
    decodeIntegerRow 16 3 1 21709174,
    decodeIntegerRow 16 3 1 21445114,
    decodeIntegerRow 16 3 1 18334726,
    decodeIntegerRow 16 3 1 35340854,
    decodeIntegerRow 16 3 1 36403682,
    decodeIntegerRow 16 3 1 15146062,
    decodeIntegerRow 16 3 1 21704962,
    decodeIntegerRow 16 3 1 21602578,
    decodeIntegerRow 16 3 1 21561754,
    decodeIntegerRow 16 3 1 21696214,
    decodeIntegerRow 16 3 1 36403734,
    decodeIntegerRow 16 3 1 27900646,
    decodeIntegerRow 16 3 1 24712018,
    decodeIntegerRow 16 3 1 35340798]

def cols_left0 (r : LeftIndex 4 1 6) : List ℤ := cols_left0Data.getD (leftPosition 4 1 6 r) []

private theorem cols_left0_eq_0_0_0 : (tripleIndices 2 1 8).map (fun j => (left0Middle4 1 6) j ((0 : Fin 1), (0 : Fin 2), (0 : Fin 8))) = cols_left0 ((0 : Fin 1), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_1 : (tripleIndices 2 1 8).map (fun j => (left0Middle4 1 6) j ((0 : Fin 1), (0 : Fin 2), (1 : Fin 8))) = cols_left0 ((0 : Fin 1), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_2 : (tripleIndices 2 1 8).map (fun j => (left0Middle4 1 6) j ((0 : Fin 1), (0 : Fin 2), (2 : Fin 8))) = cols_left0 ((0 : Fin 1), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_3 : (tripleIndices 2 1 8).map (fun j => (left0Middle4 1 6) j ((0 : Fin 1), (0 : Fin 2), (3 : Fin 8))) = cols_left0 ((0 : Fin 1), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_4 : (tripleIndices 2 1 8).map (fun j => (left0Middle4 1 6) j ((0 : Fin 1), (0 : Fin 2), (4 : Fin 8))) = cols_left0 ((0 : Fin 1), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_5 : (tripleIndices 2 1 8).map (fun j => (left0Middle4 1 6) j ((0 : Fin 1), (0 : Fin 2), (5 : Fin 8))) = cols_left0 ((0 : Fin 1), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_6 : (tripleIndices 2 1 8).map (fun j => (left0Middle4 1 6) j ((0 : Fin 1), (0 : Fin 2), (6 : Fin 8))) = cols_left0 ((0 : Fin 1), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_7 : (tripleIndices 2 1 8).map (fun j => (left0Middle4 1 6) j ((0 : Fin 1), (0 : Fin 2), (7 : Fin 8))) = cols_left0 ((0 : Fin 1), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_0 : (tripleIndices 2 1 8).map (fun j => (left0Middle4 1 6) j ((0 : Fin 1), (1 : Fin 2), (0 : Fin 8))) = cols_left0 ((0 : Fin 1), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_1 : (tripleIndices 2 1 8).map (fun j => (left0Middle4 1 6) j ((0 : Fin 1), (1 : Fin 2), (1 : Fin 8))) = cols_left0 ((0 : Fin 1), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_2 : (tripleIndices 2 1 8).map (fun j => (left0Middle4 1 6) j ((0 : Fin 1), (1 : Fin 2), (2 : Fin 8))) = cols_left0 ((0 : Fin 1), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_3 : (tripleIndices 2 1 8).map (fun j => (left0Middle4 1 6) j ((0 : Fin 1), (1 : Fin 2), (3 : Fin 8))) = cols_left0 ((0 : Fin 1), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_4 : (tripleIndices 2 1 8).map (fun j => (left0Middle4 1 6) j ((0 : Fin 1), (1 : Fin 2), (4 : Fin 8))) = cols_left0 ((0 : Fin 1), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_5 : (tripleIndices 2 1 8).map (fun j => (left0Middle4 1 6) j ((0 : Fin 1), (1 : Fin 2), (5 : Fin 8))) = cols_left0 ((0 : Fin 1), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_6 : (tripleIndices 2 1 8).map (fun j => (left0Middle4 1 6) j ((0 : Fin 1), (1 : Fin 2), (6 : Fin 8))) = cols_left0 ((0 : Fin 1), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_7 : (tripleIndices 2 1 8).map (fun j => (left0Middle4 1 6) j ((0 : Fin 1), (1 : Fin 2), (7 : Fin 8))) = cols_left0 ((0 : Fin 1), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_left0_data (r : LeftIndex 4 1 6) : (tripleIndices 2 1 8).map (fun j => (left0Middle4 1 6) j r) = cols_left0 r := by
  fin_cases r
  · exact cols_left0_eq_0_0_0
  · exact cols_left0_eq_0_0_1
  · exact cols_left0_eq_0_0_2
  · exact cols_left0_eq_0_0_3
  · exact cols_left0_eq_0_0_4
  · exact cols_left0_eq_0_0_5
  · exact cols_left0_eq_0_0_6
  · exact cols_left0_eq_0_0_7
  · exact cols_left0_eq_0_1_0
  · exact cols_left0_eq_0_1_1
  · exact cols_left0_eq_0_1_2
  · exact cols_left0_eq_0_1_3
  · exact cols_left0_eq_0_1_4
  · exact cols_left0_eq_0_1_5
  · exact cols_left0_eq_0_1_6
  · exact cols_left0_eq_0_1_7

private def cols_right2Data : List (List ℤ) := [decodeIntegerRow 16 5 2 88500976552,
    decodeIntegerRow 16 5 2 137329101564,
    decodeIntegerRow 16 5 2 76782226312,
    decodeIntegerRow 16 5 2 78735351612,
    decodeIntegerRow 16 5 2 76274407812,
    decodeIntegerRow 16 5 2 76196290312,
    decodeIntegerRow 16 5 2 76293007812,
    decodeIntegerRow 16 5 2 76290070312,
    decodeIntegerRow 16 5 2 137329101560,
    decodeIntegerRow 16 5 2 64086914052,
    decodeIntegerRow 16 5 2 78735351512,
    decodeIntegerRow 16 5 2 75805663812,
    decodeIntegerRow 16 5 2 76196287812,
    decodeIntegerRow 16 5 2 76313470312,
    decodeIntegerRow 16 5 2 76290007812,
    decodeIntegerRow 16 5 2 76294570312]

def cols_right2 (r : LeftIndex 4 1 6) : List ℤ := cols_right2Data.getD (leftPosition 4 1 6 r) []

private theorem cols_right2_eq_0_0_0 : (tripleIndices 2 1 8).map (fun j => (right2Middle4 1 6) j ((0 : Fin 1), (0 : Fin 2), (0 : Fin 8))) = cols_right2 ((0 : Fin 1), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_1 : (tripleIndices 2 1 8).map (fun j => (right2Middle4 1 6) j ((0 : Fin 1), (0 : Fin 2), (1 : Fin 8))) = cols_right2 ((0 : Fin 1), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_2 : (tripleIndices 2 1 8).map (fun j => (right2Middle4 1 6) j ((0 : Fin 1), (0 : Fin 2), (2 : Fin 8))) = cols_right2 ((0 : Fin 1), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_3 : (tripleIndices 2 1 8).map (fun j => (right2Middle4 1 6) j ((0 : Fin 1), (0 : Fin 2), (3 : Fin 8))) = cols_right2 ((0 : Fin 1), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_4 : (tripleIndices 2 1 8).map (fun j => (right2Middle4 1 6) j ((0 : Fin 1), (0 : Fin 2), (4 : Fin 8))) = cols_right2 ((0 : Fin 1), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_5 : (tripleIndices 2 1 8).map (fun j => (right2Middle4 1 6) j ((0 : Fin 1), (0 : Fin 2), (5 : Fin 8))) = cols_right2 ((0 : Fin 1), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_6 : (tripleIndices 2 1 8).map (fun j => (right2Middle4 1 6) j ((0 : Fin 1), (0 : Fin 2), (6 : Fin 8))) = cols_right2 ((0 : Fin 1), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_7 : (tripleIndices 2 1 8).map (fun j => (right2Middle4 1 6) j ((0 : Fin 1), (0 : Fin 2), (7 : Fin 8))) = cols_right2 ((0 : Fin 1), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_0 : (tripleIndices 2 1 8).map (fun j => (right2Middle4 1 6) j ((0 : Fin 1), (1 : Fin 2), (0 : Fin 8))) = cols_right2 ((0 : Fin 1), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_1 : (tripleIndices 2 1 8).map (fun j => (right2Middle4 1 6) j ((0 : Fin 1), (1 : Fin 2), (1 : Fin 8))) = cols_right2 ((0 : Fin 1), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_2 : (tripleIndices 2 1 8).map (fun j => (right2Middle4 1 6) j ((0 : Fin 1), (1 : Fin 2), (2 : Fin 8))) = cols_right2 ((0 : Fin 1), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_3 : (tripleIndices 2 1 8).map (fun j => (right2Middle4 1 6) j ((0 : Fin 1), (1 : Fin 2), (3 : Fin 8))) = cols_right2 ((0 : Fin 1), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_4 : (tripleIndices 2 1 8).map (fun j => (right2Middle4 1 6) j ((0 : Fin 1), (1 : Fin 2), (4 : Fin 8))) = cols_right2 ((0 : Fin 1), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_5 : (tripleIndices 2 1 8).map (fun j => (right2Middle4 1 6) j ((0 : Fin 1), (1 : Fin 2), (5 : Fin 8))) = cols_right2 ((0 : Fin 1), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_6 : (tripleIndices 2 1 8).map (fun j => (right2Middle4 1 6) j ((0 : Fin 1), (1 : Fin 2), (6 : Fin 8))) = cols_right2 ((0 : Fin 1), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_7 : (tripleIndices 2 1 8).map (fun j => (right2Middle4 1 6) j ((0 : Fin 1), (1 : Fin 2), (7 : Fin 8))) = cols_right2 ((0 : Fin 1), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right2_data (r : LeftIndex 4 1 6) : (tripleIndices 2 1 8).map (fun j => (right2Middle4 1 6) j r) = cols_right2 r := by
  fin_cases r
  · exact cols_right2_eq_0_0_0
  · exact cols_right2_eq_0_0_1
  · exact cols_right2_eq_0_0_2
  · exact cols_right2_eq_0_0_3
  · exact cols_right2_eq_0_0_4
  · exact cols_right2_eq_0_0_5
  · exact cols_right2_eq_0_0_6
  · exact cols_right2_eq_0_0_7
  · exact cols_right2_eq_0_1_0
  · exact cols_right2_eq_0_1_1
  · exact cols_right2_eq_0_1_2
  · exact cols_right2_eq_0_1_3
  · exact cols_right2_eq_0_1_4
  · exact cols_right2_eq_0_1_5
  · exact cols_right2_eq_0_1_6
  · exact cols_right2_eq_0_1_7

theorem product0_eq : HexagonAtoms416.outerABC * HexagonAtoms416.assocABC = HexagonAtoms416.assocABC :=
  Matrix.one_mul (m := Fin 2 × Fin 1 × Fin 8) (n := Fin 1 × Fin 2 × Fin 8) _

theorem product1_eq : HexagonAtoms416.assocBAC * HexagonAtoms416.innerABC = HexagonAtoms416.assocBAC :=
  Matrix.mul_one (m := Fin 2 × Fin 1 × Fin 8) (n := Fin 1 × Fin 2 × Fin 8) _

theorem product2_eq : HexagonAtoms416.innerRightABC * HexagonAtoms416.assocABC = HexagonAtoms416.assocABC :=
  Matrix.one_mul (m := Fin 2 × Fin 1 × Fin 8) (n := Fin 1 × Fin 2 × Fin 8) _

theorem product3_eq : HexagonAtoms416.inverseACB * right0Middle4 1 6 = rowColumnMul rows_inverseACB cols_right0 :=
  (rowColumnMul_eq _ _ _ _ rows_inverseACB_data cols_right0_data).symm

theorem product4_eq : HexagonAtoms416.innerACB * right1Middle4 1 6 = right1Middle4 1 6 :=
  Matrix.one_mul (m := Fin 2 × Fin 1 × Fin 8) (n := Fin 1 × Fin 2 × Fin 8) _

theorem product5_eq : HexagonAtoms416.assocBCA * left0Middle4 1 6 = rowColumnMul rows_assocBCA cols_left0 :=
  (rowColumnMul_eq _ _ _ _ rows_assocBCA_data cols_left0_data).symm

theorem product6_eq : HexagonAtoms416.innerRightBAC * left1Middle4 1 6 = left1Middle4 1 6 :=
  Matrix.one_mul (m := Fin 2 × Fin 1 × Fin 8) (n := Fin 1 × Fin 2 × Fin 8) _

theorem product7_eq : HexagonAtoms416.assocCAB * right2Middle4 1 6 = rowColumnMul rows_assocCAB cols_right2 :=
  (rowColumnMul_eq _ _ _ _ rows_assocCAB_data cols_right2_data).symm

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn416
