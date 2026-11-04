import RMod.BrundanEllis.StackingReferenceHexagonAtoms713
import RMod.BrundanEllis.StackingReferenceHexagonMiddle7
import RMod.BrundanEllis.StackingReferenceRowColumnCheck

/-! Verified row and column lists. Each subsequent scalar product traverses
these lists directly, without repeated lookup into the original matrices. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn713
open Superfusion

private def rows_inverseACBData : List (List ℤ) := [decodeIntegerRow 16 3 1 18153100,
    decodeIntegerRow 16 3 1 7626704,
    decodeIntegerRow 16 3 1 6604592,
    decodeIntegerRow 16 3 1 14973220,
    decodeIntegerRow 16 3 1 6681380,
    decodeIntegerRow 16 3 1 15318928,
    decodeIntegerRow 16 3 1 18516304,
    decodeIntegerRow 16 3 1 7785140,
    decodeIntegerRow 16 3 1 35262608,
    decodeIntegerRow 16 3 1 18520540,
    decodeIntegerRow 16 3 1 27732340,
    decodeIntegerRow 16 3 1 6683376,
    decodeIntegerRow 16 3 1 14977744,
    decodeIntegerRow 16 3 1 36444020,
    decodeIntegerRow 16 3 1 7627620,
    decodeIntegerRow 16 3 1 24897808]

def rows_inverseACB (r : LeftIndex 7 3 1) : List ℤ := rows_inverseACBData.getD (leftPosition 7 3 1 r) []

private theorem rows_inverseACB_eq_0_0_0 : (tripleIndices 2 1 8).map ((HexagonAtoms713.inverseACB) ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_1 : (tripleIndices 2 1 8).map ((HexagonAtoms713.inverseACB) ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_2 : (tripleIndices 2 1 8).map ((HexagonAtoms713.inverseACB) ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_3 : (tripleIndices 2 1 8).map ((HexagonAtoms713.inverseACB) ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_4 : (tripleIndices 2 1 8).map ((HexagonAtoms713.inverseACB) ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_5 : (tripleIndices 2 1 8).map ((HexagonAtoms713.inverseACB) ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_6 : (tripleIndices 2 1 8).map ((HexagonAtoms713.inverseACB) ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_7 : (tripleIndices 2 1 8).map ((HexagonAtoms713.inverseACB) ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_0 : (tripleIndices 2 1 8).map ((HexagonAtoms713.inverseACB) ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_1 : (tripleIndices 2 1 8).map ((HexagonAtoms713.inverseACB) ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_2 : (tripleIndices 2 1 8).map ((HexagonAtoms713.inverseACB) ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_3 : (tripleIndices 2 1 8).map ((HexagonAtoms713.inverseACB) ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_4 : (tripleIndices 2 1 8).map ((HexagonAtoms713.inverseACB) ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_5 : (tripleIndices 2 1 8).map ((HexagonAtoms713.inverseACB) ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_6 : (tripleIndices 2 1 8).map ((HexagonAtoms713.inverseACB) ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_7 : (tripleIndices 2 1 8).map ((HexagonAtoms713.inverseACB) ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_inverseACB_data (r : LeftIndex 7 3 1) : (tripleIndices 2 1 8).map ((HexagonAtoms713.inverseACB) r) = rows_inverseACB r := by
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

private def rows_assocBCAData : List (List ℤ) := [decodeIntegerRow 16 3 1 21518986,
    decodeIntegerRow 16 3 1 21502948,
    decodeIntegerRow 16 3 1 21464554,
    decodeIntegerRow 16 3 1 21346132,
    decodeIntegerRow 16 3 1 20991892,
    decodeIntegerRow 16 3 1 19929046,
    decodeIntegerRow 16 3 1 16740388,
    decodeIntegerRow 16 3 1 7174454,
    decodeIntegerRow 16 3 1 35872268,
    decodeIntegerRow 16 3 1 16740394,
    decodeIntegerRow 16 3 1 23117692,
    decodeIntegerRow 16 3 1 20991946,
    decodeIntegerRow 16 3 1 21346294,
    decodeIntegerRow 16 3 1 21582652,
    decodeIntegerRow 16 3 1 21504406,
    decodeIntegerRow 16 3 1 21532108]

def rows_assocBCA (r : RightIndex 1 3 7) : List ℤ := rows_assocBCAData.getD (rightPosition 1 3 7 r) []

private theorem rows_assocBCA_eq_0_0_0 : (tripleIndices 2 1 8).map ((HexagonAtoms713.assocBCA) ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8))) = rows_assocBCA ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_1 : (tripleIndices 2 1 8).map ((HexagonAtoms713.assocBCA) ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8))) = rows_assocBCA ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_2 : (tripleIndices 2 1 8).map ((HexagonAtoms713.assocBCA) ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8))) = rows_assocBCA ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_3 : (tripleIndices 2 1 8).map ((HexagonAtoms713.assocBCA) ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8))) = rows_assocBCA ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_4 : (tripleIndices 2 1 8).map ((HexagonAtoms713.assocBCA) ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8))) = rows_assocBCA ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_5 : (tripleIndices 2 1 8).map ((HexagonAtoms713.assocBCA) ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8))) = rows_assocBCA ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_6 : (tripleIndices 2 1 8).map ((HexagonAtoms713.assocBCA) ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8))) = rows_assocBCA ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_7 : (tripleIndices 2 1 8).map ((HexagonAtoms713.assocBCA) ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8))) = rows_assocBCA ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_0 : (tripleIndices 2 1 8).map ((HexagonAtoms713.assocBCA) ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8))) = rows_assocBCA ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_1 : (tripleIndices 2 1 8).map ((HexagonAtoms713.assocBCA) ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8))) = rows_assocBCA ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_2 : (tripleIndices 2 1 8).map ((HexagonAtoms713.assocBCA) ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8))) = rows_assocBCA ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_3 : (tripleIndices 2 1 8).map ((HexagonAtoms713.assocBCA) ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8))) = rows_assocBCA ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_4 : (tripleIndices 2 1 8).map ((HexagonAtoms713.assocBCA) ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8))) = rows_assocBCA ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_5 : (tripleIndices 2 1 8).map ((HexagonAtoms713.assocBCA) ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8))) = rows_assocBCA ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_6 : (tripleIndices 2 1 8).map ((HexagonAtoms713.assocBCA) ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8))) = rows_assocBCA ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_7 : (tripleIndices 2 1 8).map ((HexagonAtoms713.assocBCA) ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8))) = rows_assocBCA ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocBCA_data (r : RightIndex 1 3 7) : (tripleIndices 2 1 8).map ((HexagonAtoms713.assocBCA) r) = rows_assocBCA r := by
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

private def rows_assocCABData : List (List ℤ) := [decodeIntegerRow 16 3 1 21516880,
    decodeIntegerRow 16 3 1 21503434,
    decodeIntegerRow 16 3 1 21463582,
    decodeIntegerRow 16 3 1 21348400,
    decodeIntegerRow 16 3 1 20991918,
    decodeIntegerRow 16 3 1 19929040,
    decodeIntegerRow 16 3 1 16740400,
    decodeIntegerRow 16 3 1 7174426,
    decodeIntegerRow 16 3 1 22054800,
    decodeIntegerRow 16 3 1 19929034,
    decodeIntegerRow 16 3 1 16740382,
    decodeIntegerRow 16 3 1 35872240,
    decodeIntegerRow 16 3 1 21516718,
    decodeIntegerRow 16 3 1 21542800,
    decodeIntegerRow 16 3 1 21581680,
    decodeIntegerRow 16 3 1 21344026]

def rows_assocCAB (r : RightIndex 3 7 1) : List ℤ := rows_assocCABData.getD (rightPosition 3 7 1 r) []

private theorem rows_assocCAB_eq_0_0_0 : (tripleIndices 2 1 8).map ((HexagonAtoms713.assocCAB) ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_1 : (tripleIndices 2 1 8).map ((HexagonAtoms713.assocCAB) ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_2 : (tripleIndices 2 1 8).map ((HexagonAtoms713.assocCAB) ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_3 : (tripleIndices 2 1 8).map ((HexagonAtoms713.assocCAB) ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_4 : (tripleIndices 2 1 8).map ((HexagonAtoms713.assocCAB) ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_5 : (tripleIndices 2 1 8).map ((HexagonAtoms713.assocCAB) ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_6 : (tripleIndices 2 1 8).map ((HexagonAtoms713.assocCAB) ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_7 : (tripleIndices 2 1 8).map ((HexagonAtoms713.assocCAB) ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_0 : (tripleIndices 2 1 8).map ((HexagonAtoms713.assocCAB) ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_1 : (tripleIndices 2 1 8).map ((HexagonAtoms713.assocCAB) ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_2 : (tripleIndices 2 1 8).map ((HexagonAtoms713.assocCAB) ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_3 : (tripleIndices 2 1 8).map ((HexagonAtoms713.assocCAB) ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_4 : (tripleIndices 2 1 8).map ((HexagonAtoms713.assocCAB) ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_5 : (tripleIndices 2 1 8).map ((HexagonAtoms713.assocCAB) ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_6 : (tripleIndices 2 1 8).map ((HexagonAtoms713.assocCAB) ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_7 : (tripleIndices 2 1 8).map ((HexagonAtoms713.assocCAB) ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocCAB_data (r : RightIndex 3 7 1) : (tripleIndices 2 1 8).map ((HexagonAtoms713.assocCAB) r) = rows_assocCAB r := by
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

private def cols_right0Data : List (List ℤ) := [decodeIntegerRow 16 3 1 7232746,
    decodeIntegerRow 16 3 1 26126986,
    decodeIntegerRow 16 3 1 19922398,
    decodeIntegerRow 16 3 1 22074242,
    decodeIntegerRow 16 3 1 26481298,
    decodeIntegerRow 16 3 1 7114702,
    decodeIntegerRow 16 3 1 21011846,
    decodeIntegerRow 16 3 1 23111206,
    decodeIntegerRow 16 3 1 19935682,
    decodeIntegerRow 16 3 1 21011358,
    decodeIntegerRow 16 3 1 35930614,
    decodeIntegerRow 16 3 1 26485654,
    decodeIntegerRow 16 3 1 22074726,
    decodeIntegerRow 16 3 1 23124166,
    decodeIntegerRow 16 3 1 26131378,
    decodeIntegerRow 16 3 1 35812462]

def cols_right0 (r : LeftIndex 7 1 3) : List ℤ := cols_right0Data.getD (leftPosition 7 1 3 r) []

private theorem cols_right0_eq_0_0_0 : (tripleIndices 2 1 8).map (fun j => (right0Middle7 1 3) j ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8))) = cols_right0 ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_1 : (tripleIndices 2 1 8).map (fun j => (right0Middle7 1 3) j ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8))) = cols_right0 ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_2 : (tripleIndices 2 1 8).map (fun j => (right0Middle7 1 3) j ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8))) = cols_right0 ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_3 : (tripleIndices 2 1 8).map (fun j => (right0Middle7 1 3) j ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8))) = cols_right0 ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_4 : (tripleIndices 2 1 8).map (fun j => (right0Middle7 1 3) j ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8))) = cols_right0 ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_5 : (tripleIndices 2 1 8).map (fun j => (right0Middle7 1 3) j ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8))) = cols_right0 ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_6 : (tripleIndices 2 1 8).map (fun j => (right0Middle7 1 3) j ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8))) = cols_right0 ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_7 : (tripleIndices 2 1 8).map (fun j => (right0Middle7 1 3) j ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8))) = cols_right0 ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_0 : (tripleIndices 2 1 8).map (fun j => (right0Middle7 1 3) j ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8))) = cols_right0 ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_1 : (tripleIndices 2 1 8).map (fun j => (right0Middle7 1 3) j ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8))) = cols_right0 ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_2 : (tripleIndices 2 1 8).map (fun j => (right0Middle7 1 3) j ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8))) = cols_right0 ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_3 : (tripleIndices 2 1 8).map (fun j => (right0Middle7 1 3) j ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8))) = cols_right0 ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_4 : (tripleIndices 2 1 8).map (fun j => (right0Middle7 1 3) j ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8))) = cols_right0 ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_5 : (tripleIndices 2 1 8).map (fun j => (right0Middle7 1 3) j ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8))) = cols_right0 ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_6 : (tripleIndices 2 1 8).map (fun j => (right0Middle7 1 3) j ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8))) = cols_right0 ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_7 : (tripleIndices 2 1 8).map (fun j => (right0Middle7 1 3) j ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8))) = cols_right0 ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right0_data (r : LeftIndex 7 1 3) : (tripleIndices 2 1 8).map (fun j => (right0Middle7 1 3) j r) = cols_right0 r := by
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

private def cols_left0Data : List (List ℤ) := [decodeIntegerRow 16 3 1 7232746,
    decodeIntegerRow 16 3 1 26126986,
    decodeIntegerRow 16 3 1 19922398,
    decodeIntegerRow 16 3 1 22074242,
    decodeIntegerRow 16 3 1 26481298,
    decodeIntegerRow 16 3 1 7114702,
    decodeIntegerRow 16 3 1 21011846,
    decodeIntegerRow 16 3 1 23111206,
    decodeIntegerRow 16 3 1 19935682,
    decodeIntegerRow 16 3 1 21011358,
    decodeIntegerRow 16 3 1 35930614,
    decodeIntegerRow 16 3 1 26485654,
    decodeIntegerRow 16 3 1 22074726,
    decodeIntegerRow 16 3 1 23124166,
    decodeIntegerRow 16 3 1 26131378,
    decodeIntegerRow 16 3 1 35812462]

def cols_left0 (r : LeftIndex 7 1 3) : List ℤ := cols_left0Data.getD (leftPosition 7 1 3 r) []

private theorem cols_left0_eq_0_0_0 : (tripleIndices 2 1 8).map (fun j => (left0Middle7 1 3) j ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8))) = cols_left0 ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_1 : (tripleIndices 2 1 8).map (fun j => (left0Middle7 1 3) j ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8))) = cols_left0 ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_2 : (tripleIndices 2 1 8).map (fun j => (left0Middle7 1 3) j ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8))) = cols_left0 ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_3 : (tripleIndices 2 1 8).map (fun j => (left0Middle7 1 3) j ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8))) = cols_left0 ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_4 : (tripleIndices 2 1 8).map (fun j => (left0Middle7 1 3) j ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8))) = cols_left0 ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_5 : (tripleIndices 2 1 8).map (fun j => (left0Middle7 1 3) j ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8))) = cols_left0 ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_6 : (tripleIndices 2 1 8).map (fun j => (left0Middle7 1 3) j ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8))) = cols_left0 ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_7 : (tripleIndices 2 1 8).map (fun j => (left0Middle7 1 3) j ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8))) = cols_left0 ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_0 : (tripleIndices 2 1 8).map (fun j => (left0Middle7 1 3) j ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8))) = cols_left0 ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_1 : (tripleIndices 2 1 8).map (fun j => (left0Middle7 1 3) j ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8))) = cols_left0 ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_2 : (tripleIndices 2 1 8).map (fun j => (left0Middle7 1 3) j ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8))) = cols_left0 ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_3 : (tripleIndices 2 1 8).map (fun j => (left0Middle7 1 3) j ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8))) = cols_left0 ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_4 : (tripleIndices 2 1 8).map (fun j => (left0Middle7 1 3) j ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8))) = cols_left0 ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_5 : (tripleIndices 2 1 8).map (fun j => (left0Middle7 1 3) j ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8))) = cols_left0 ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_6 : (tripleIndices 2 1 8).map (fun j => (left0Middle7 1 3) j ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8))) = cols_left0 ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_7 : (tripleIndices 2 1 8).map (fun j => (left0Middle7 1 3) j ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8))) = cols_left0 ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_left0_data (r : LeftIndex 7 1 3) : (tripleIndices 2 1 8).map (fun j => (left0Middle7 1 3) j r) = cols_left0 r := by
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

private def cols_right2Data : List (List ℤ) := [decodeIntegerRow 16 9 4 926509922265280,
    decodeIntegerRow 16 9 4 926508544507768,
    decodeIntegerRow 16 9 4 926496145162552,
    decodeIntegerRow 16 9 4 926384589319360,
    decodeIntegerRow 16 9 4 925380376279992,
    decodeIntegerRow 16 9 4 916342631112640,
    decodeIntegerRow 16 9 4 835002924606400,
    decodeIntegerRow 16 9 4 102945566044408,
    decodeIntegerRow 16 9 4 927639812571840,
    decodeIntegerRow 16 9 4 916342631112568,
    decodeIntegerRow 16 9 4 835002924605752,
    decodeIntegerRow 16 9 4 1750074622801600,
    decodeIntegerRow 16 9 4 926509922212792,
    decodeIntegerRow 16 9 4 926511643871680,
    decodeIntegerRow 16 9 4 926524039437760,
    decodeIntegerRow 16 9 4 926384551055608]

def cols_right2 (r : LeftIndex 7 1 3) : List ℤ := cols_right2Data.getD (leftPosition 7 1 3 r) []

private theorem cols_right2_eq_0_0_0 : (tripleIndices 2 1 8).map (fun j => (right2Middle7 1 3) j ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8))) = cols_right2 ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_1 : (tripleIndices 2 1 8).map (fun j => (right2Middle7 1 3) j ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8))) = cols_right2 ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_2 : (tripleIndices 2 1 8).map (fun j => (right2Middle7 1 3) j ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8))) = cols_right2 ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_3 : (tripleIndices 2 1 8).map (fun j => (right2Middle7 1 3) j ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8))) = cols_right2 ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_4 : (tripleIndices 2 1 8).map (fun j => (right2Middle7 1 3) j ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8))) = cols_right2 ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_5 : (tripleIndices 2 1 8).map (fun j => (right2Middle7 1 3) j ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8))) = cols_right2 ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_6 : (tripleIndices 2 1 8).map (fun j => (right2Middle7 1 3) j ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8))) = cols_right2 ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_7 : (tripleIndices 2 1 8).map (fun j => (right2Middle7 1 3) j ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8))) = cols_right2 ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_0 : (tripleIndices 2 1 8).map (fun j => (right2Middle7 1 3) j ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8))) = cols_right2 ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_1 : (tripleIndices 2 1 8).map (fun j => (right2Middle7 1 3) j ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8))) = cols_right2 ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_2 : (tripleIndices 2 1 8).map (fun j => (right2Middle7 1 3) j ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8))) = cols_right2 ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_3 : (tripleIndices 2 1 8).map (fun j => (right2Middle7 1 3) j ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8))) = cols_right2 ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_4 : (tripleIndices 2 1 8).map (fun j => (right2Middle7 1 3) j ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8))) = cols_right2 ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_5 : (tripleIndices 2 1 8).map (fun j => (right2Middle7 1 3) j ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8))) = cols_right2 ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_6 : (tripleIndices 2 1 8).map (fun j => (right2Middle7 1 3) j ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8))) = cols_right2 ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_7 : (tripleIndices 2 1 8).map (fun j => (right2Middle7 1 3) j ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8))) = cols_right2 ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right2_data (r : LeftIndex 7 1 3) : (tripleIndices 2 1 8).map (fun j => (right2Middle7 1 3) j r) = cols_right2 r := by
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

theorem product0_eq : HexagonAtoms713.outerABC * HexagonAtoms713.assocABC = HexagonAtoms713.assocABC :=
  Matrix.one_mul (m := Fin 2 × Fin 1 × Fin 8) (n := Fin 2 × Fin 1 × Fin 8) _

theorem product1_eq : HexagonAtoms713.assocBAC * HexagonAtoms713.innerABC = HexagonAtoms713.assocBAC :=
  Matrix.mul_one (m := Fin 2 × Fin 1 × Fin 8) (n := Fin 2 × Fin 1 × Fin 8) _

theorem product2_eq : HexagonAtoms713.innerRightABC * HexagonAtoms713.assocABC = HexagonAtoms713.assocABC :=
  Matrix.one_mul (m := Fin 2 × Fin 1 × Fin 8) (n := Fin 2 × Fin 1 × Fin 8) _

theorem product3_eq : HexagonAtoms713.inverseACB * right0Middle7 1 3 = rowColumnMul rows_inverseACB cols_right0 :=
  (rowColumnMul_eq _ _ _ _ rows_inverseACB_data cols_right0_data).symm

theorem product4_eq : HexagonAtoms713.innerACB * right1Middle7 1 3 = right1Middle7 1 3 :=
  Matrix.one_mul (m := Fin 2 × Fin 1 × Fin 8) (n := Fin 2 × Fin 1 × Fin 8) _

theorem product5_eq : HexagonAtoms713.assocBCA * left0Middle7 1 3 = rowColumnMul rows_assocBCA cols_left0 :=
  (rowColumnMul_eq _ _ _ _ rows_assocBCA_data cols_left0_data).symm

theorem product6_eq : HexagonAtoms713.innerRightBAC * left1Middle7 1 3 = left1Middle7 1 3 :=
  Matrix.one_mul (m := Fin 2 × Fin 1 × Fin 8) (n := Fin 2 × Fin 1 × Fin 8) _

theorem product7_eq : HexagonAtoms713.assocCAB * right2Middle7 1 3 = rowColumnMul rows_assocCAB cols_right2 :=
  (rowColumnMul_eq _ _ _ _ rows_assocCAB_data cols_right2_data).symm

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn713
