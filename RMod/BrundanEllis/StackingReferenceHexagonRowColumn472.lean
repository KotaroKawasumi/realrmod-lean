import RMod.BrundanEllis.StackingReferenceHexagonAtoms472
import RMod.BrundanEllis.StackingReferenceHexagonMiddle4
import RMod.BrundanEllis.StackingReferenceRowColumnCheck

/-! Verified row and column lists. Each subsequent scalar product traverses
these lists directly, without repeated lookup into the original matrices. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn472
open Superfusion

private def rows_inverseACBData : List (List ℤ) := [decodeIntegerRow 16 3 1 21516880,
    decodeIntegerRow 16 3 1 21503434,
    decodeIntegerRow 16 3 1 21463582,
    decodeIntegerRow 16 3 1 21348400,
    decodeIntegerRow 16 3 1 20991920,
    decodeIntegerRow 16 3 1 19929034,
    decodeIntegerRow 16 3 1 16740382,
    decodeIntegerRow 16 3 1 7174480,
    decodeIntegerRow 16 3 1 20991918,
    decodeIntegerRow 16 3 1 23117680,
    decodeIntegerRow 16 3 1 26306320,
    decodeIntegerRow 16 3 1 7174426,
    decodeIntegerRow 16 3 1 21516718,
    decodeIntegerRow 16 3 1 21542800,
    decodeIntegerRow 16 3 1 21581680,
    decodeIntegerRow 16 3 1 21344026]

def rows_inverseACB (r : LeftIndex 4 2 7) : List ℤ := rows_inverseACBData.getD (leftPosition 4 2 7 r) []

private theorem rows_inverseACB_eq_0_0_0 : (tripleIndices 2 1 8).map ((HexagonAtoms472.inverseACB) ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_1 : (tripleIndices 2 1 8).map ((HexagonAtoms472.inverseACB) ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_2 : (tripleIndices 2 1 8).map ((HexagonAtoms472.inverseACB) ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_3 : (tripleIndices 2 1 8).map ((HexagonAtoms472.inverseACB) ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_4 : (tripleIndices 2 1 8).map ((HexagonAtoms472.inverseACB) ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_5 : (tripleIndices 2 1 8).map ((HexagonAtoms472.inverseACB) ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_6 : (tripleIndices 2 1 8).map ((HexagonAtoms472.inverseACB) ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_7 : (tripleIndices 2 1 8).map ((HexagonAtoms472.inverseACB) ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_0 : (tripleIndices 2 1 8).map ((HexagonAtoms472.inverseACB) ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_1 : (tripleIndices 2 1 8).map ((HexagonAtoms472.inverseACB) ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_2 : (tripleIndices 2 1 8).map ((HexagonAtoms472.inverseACB) ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_3 : (tripleIndices 2 1 8).map ((HexagonAtoms472.inverseACB) ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_4 : (tripleIndices 2 1 8).map ((HexagonAtoms472.inverseACB) ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_5 : (tripleIndices 2 1 8).map ((HexagonAtoms472.inverseACB) ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_6 : (tripleIndices 2 1 8).map ((HexagonAtoms472.inverseACB) ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_7 : (tripleIndices 2 1 8).map ((HexagonAtoms472.inverseACB) ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_inverseACB_data (r : LeftIndex 4 2 7) : (tripleIndices 2 1 8).map ((HexagonAtoms472.inverseACB) r) = rows_inverseACB r := by
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

private def rows_assocBCAData : List (List ℤ) := [decodeIntegerRow 16 3 1 18153268,
    decodeIntegerRow 16 3 1 6682892,
    decodeIntegerRow 16 3 1 7626216,
    decodeIntegerRow 16 3 1 27732184,
    decodeIntegerRow 16 3 1 6603188,
    decodeIntegerRow 16 3 1 24530572,
    decodeIntegerRow 16 3 1 14977576,
    decodeIntegerRow 16 3 1 7785624,
    decodeIntegerRow 16 3 1 6681864,
    decodeIntegerRow 16 3 1 18148744,
    decodeIntegerRow 16 3 1 27727948,
    decodeIntegerRow 16 3 1 7628108,
    decodeIntegerRow 16 3 1 24526024,
    decodeIntegerRow 16 3 1 6604104,
    decodeIntegerRow 16 3 1 7783628,
    decodeIntegerRow 16 3 1 14973388]

def rows_assocBCA (r : RightIndex 7 2 4) : List ℤ := rows_assocBCAData.getD (rightPosition 7 2 4 r) []

private theorem rows_assocBCA_eq_0_0_0 : (tripleIndices 2 1 8).map ((HexagonAtoms472.assocBCA) ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8))) = rows_assocBCA ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_1 : (tripleIndices 2 1 8).map ((HexagonAtoms472.assocBCA) ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8))) = rows_assocBCA ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_2 : (tripleIndices 2 1 8).map ((HexagonAtoms472.assocBCA) ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8))) = rows_assocBCA ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_3 : (tripleIndices 2 1 8).map ((HexagonAtoms472.assocBCA) ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8))) = rows_assocBCA ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_4 : (tripleIndices 2 1 8).map ((HexagonAtoms472.assocBCA) ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8))) = rows_assocBCA ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_5 : (tripleIndices 2 1 8).map ((HexagonAtoms472.assocBCA) ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8))) = rows_assocBCA ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_6 : (tripleIndices 2 1 8).map ((HexagonAtoms472.assocBCA) ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8))) = rows_assocBCA ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_7 : (tripleIndices 2 1 8).map ((HexagonAtoms472.assocBCA) ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8))) = rows_assocBCA ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_0 : (tripleIndices 2 1 8).map ((HexagonAtoms472.assocBCA) ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8))) = rows_assocBCA ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_1 : (tripleIndices 2 1 8).map ((HexagonAtoms472.assocBCA) ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8))) = rows_assocBCA ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_2 : (tripleIndices 2 1 8).map ((HexagonAtoms472.assocBCA) ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8))) = rows_assocBCA ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_3 : (tripleIndices 2 1 8).map ((HexagonAtoms472.assocBCA) ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8))) = rows_assocBCA ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_4 : (tripleIndices 2 1 8).map ((HexagonAtoms472.assocBCA) ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8))) = rows_assocBCA ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_5 : (tripleIndices 2 1 8).map ((HexagonAtoms472.assocBCA) ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8))) = rows_assocBCA ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_6 : (tripleIndices 2 1 8).map ((HexagonAtoms472.assocBCA) ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8))) = rows_assocBCA ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_7 : (tripleIndices 2 1 8).map ((HexagonAtoms472.assocBCA) ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8))) = rows_assocBCA ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocBCA_data (r : RightIndex 7 2 4) : (tripleIndices 2 1 8).map ((HexagonAtoms472.assocBCA) r) = rows_assocBCA r := by
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

private def rows_assocCABData : List (List ℤ) := [decodeIntegerRow 16 3 1 22054801,
    decodeIntegerRow 16 3 1 19929037,
    decodeIntegerRow 16 3 1 16740391,
    decodeIntegerRow 16 3 1 35872267,
    decodeIntegerRow 16 3 1 21529921,
    decodeIntegerRow 16 3 1 21503677,
    decodeIntegerRow 16 3 1 21464311,
    decodeIntegerRow 16 3 1 21700507,
    decodeIntegerRow 16 3 1 21523357,
    decodeIntegerRow 16 3 1 21523359,
    decodeIntegerRow 16 3 1 21523333,
    decodeIntegerRow 16 3 1 21523351,
    decodeIntegerRow 16 3 1 21523117,
    decodeIntegerRow 16 3 1 21523279,
    decodeIntegerRow 16 3 1 21521173,
    decodeIntegerRow 16 3 1 21522631]

def rows_assocCAB (r : RightIndex 2 4 7) : List ℤ := rows_assocCABData.getD (rightPosition 2 4 7 r) []

private theorem rows_assocCAB_eq_0_0_0 : (tripleIndices 2 1 8).map ((HexagonAtoms472.assocCAB) ((0 : Fin 1), (0 : Fin 2), (0 : Fin 8))) = rows_assocCAB ((0 : Fin 1), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_1 : (tripleIndices 2 1 8).map ((HexagonAtoms472.assocCAB) ((0 : Fin 1), (0 : Fin 2), (1 : Fin 8))) = rows_assocCAB ((0 : Fin 1), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_2 : (tripleIndices 2 1 8).map ((HexagonAtoms472.assocCAB) ((0 : Fin 1), (0 : Fin 2), (2 : Fin 8))) = rows_assocCAB ((0 : Fin 1), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_3 : (tripleIndices 2 1 8).map ((HexagonAtoms472.assocCAB) ((0 : Fin 1), (0 : Fin 2), (3 : Fin 8))) = rows_assocCAB ((0 : Fin 1), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_4 : (tripleIndices 2 1 8).map ((HexagonAtoms472.assocCAB) ((0 : Fin 1), (0 : Fin 2), (4 : Fin 8))) = rows_assocCAB ((0 : Fin 1), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_5 : (tripleIndices 2 1 8).map ((HexagonAtoms472.assocCAB) ((0 : Fin 1), (0 : Fin 2), (5 : Fin 8))) = rows_assocCAB ((0 : Fin 1), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_6 : (tripleIndices 2 1 8).map ((HexagonAtoms472.assocCAB) ((0 : Fin 1), (0 : Fin 2), (6 : Fin 8))) = rows_assocCAB ((0 : Fin 1), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_7 : (tripleIndices 2 1 8).map ((HexagonAtoms472.assocCAB) ((0 : Fin 1), (0 : Fin 2), (7 : Fin 8))) = rows_assocCAB ((0 : Fin 1), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_0 : (tripleIndices 2 1 8).map ((HexagonAtoms472.assocCAB) ((0 : Fin 1), (1 : Fin 2), (0 : Fin 8))) = rows_assocCAB ((0 : Fin 1), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_1 : (tripleIndices 2 1 8).map ((HexagonAtoms472.assocCAB) ((0 : Fin 1), (1 : Fin 2), (1 : Fin 8))) = rows_assocCAB ((0 : Fin 1), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_2 : (tripleIndices 2 1 8).map ((HexagonAtoms472.assocCAB) ((0 : Fin 1), (1 : Fin 2), (2 : Fin 8))) = rows_assocCAB ((0 : Fin 1), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_3 : (tripleIndices 2 1 8).map ((HexagonAtoms472.assocCAB) ((0 : Fin 1), (1 : Fin 2), (3 : Fin 8))) = rows_assocCAB ((0 : Fin 1), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_4 : (tripleIndices 2 1 8).map ((HexagonAtoms472.assocCAB) ((0 : Fin 1), (1 : Fin 2), (4 : Fin 8))) = rows_assocCAB ((0 : Fin 1), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_5 : (tripleIndices 2 1 8).map ((HexagonAtoms472.assocCAB) ((0 : Fin 1), (1 : Fin 2), (5 : Fin 8))) = rows_assocCAB ((0 : Fin 1), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_6 : (tripleIndices 2 1 8).map ((HexagonAtoms472.assocCAB) ((0 : Fin 1), (1 : Fin 2), (6 : Fin 8))) = rows_assocCAB ((0 : Fin 1), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_7 : (tripleIndices 2 1 8).map ((HexagonAtoms472.assocCAB) ((0 : Fin 1), (1 : Fin 2), (7 : Fin 8))) = rows_assocCAB ((0 : Fin 1), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocCAB_data (r : RightIndex 2 4 7) : (tripleIndices 2 1 8).map ((HexagonAtoms472.assocCAB) r) = rows_assocCAB r := by
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

private def cols_right0Data : List (List ℤ) := [decodeIntegerRow 16 3 1 21530002,
    decodeIntegerRow 16 3 1 21542800,
    decodeIntegerRow 16 3 1 21581680,
    decodeIntegerRow 16 3 1 21702694,
    decodeIntegerRow 16 3 1 22054802,
    decodeIntegerRow 16 3 1 23117680,
    decodeIntegerRow 16 3 1 26306320,
    decodeIntegerRow 16 3 1 35872294,
    decodeIntegerRow 16 3 1 21503434,
    decodeIntegerRow 16 3 1 21516880,
    decodeIntegerRow 16 3 1 21348400,
    decodeIntegerRow 16 3 1 21463582,
    decodeIntegerRow 16 3 1 19929034,
    decodeIntegerRow 16 3 1 20991920,
    decodeIntegerRow 16 3 1 7174480,
    decodeIntegerRow 16 3 1 16740382]

def cols_right0 (r : LeftIndex 4 7 2) : List ℤ := cols_right0Data.getD (leftPosition 4 7 2 r) []

private theorem cols_right0_eq_0_0_0 : (tripleIndices 2 1 8).map (fun j => (right0Middle4 7 2) j ((0 : Fin 1), (0 : Fin 2), (0 : Fin 8))) = cols_right0 ((0 : Fin 1), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_1 : (tripleIndices 2 1 8).map (fun j => (right0Middle4 7 2) j ((0 : Fin 1), (0 : Fin 2), (1 : Fin 8))) = cols_right0 ((0 : Fin 1), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_2 : (tripleIndices 2 1 8).map (fun j => (right0Middle4 7 2) j ((0 : Fin 1), (0 : Fin 2), (2 : Fin 8))) = cols_right0 ((0 : Fin 1), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_3 : (tripleIndices 2 1 8).map (fun j => (right0Middle4 7 2) j ((0 : Fin 1), (0 : Fin 2), (3 : Fin 8))) = cols_right0 ((0 : Fin 1), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_4 : (tripleIndices 2 1 8).map (fun j => (right0Middle4 7 2) j ((0 : Fin 1), (0 : Fin 2), (4 : Fin 8))) = cols_right0 ((0 : Fin 1), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_5 : (tripleIndices 2 1 8).map (fun j => (right0Middle4 7 2) j ((0 : Fin 1), (0 : Fin 2), (5 : Fin 8))) = cols_right0 ((0 : Fin 1), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_6 : (tripleIndices 2 1 8).map (fun j => (right0Middle4 7 2) j ((0 : Fin 1), (0 : Fin 2), (6 : Fin 8))) = cols_right0 ((0 : Fin 1), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_7 : (tripleIndices 2 1 8).map (fun j => (right0Middle4 7 2) j ((0 : Fin 1), (0 : Fin 2), (7 : Fin 8))) = cols_right0 ((0 : Fin 1), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_0 : (tripleIndices 2 1 8).map (fun j => (right0Middle4 7 2) j ((0 : Fin 1), (1 : Fin 2), (0 : Fin 8))) = cols_right0 ((0 : Fin 1), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_1 : (tripleIndices 2 1 8).map (fun j => (right0Middle4 7 2) j ((0 : Fin 1), (1 : Fin 2), (1 : Fin 8))) = cols_right0 ((0 : Fin 1), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_2 : (tripleIndices 2 1 8).map (fun j => (right0Middle4 7 2) j ((0 : Fin 1), (1 : Fin 2), (2 : Fin 8))) = cols_right0 ((0 : Fin 1), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_3 : (tripleIndices 2 1 8).map (fun j => (right0Middle4 7 2) j ((0 : Fin 1), (1 : Fin 2), (3 : Fin 8))) = cols_right0 ((0 : Fin 1), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_4 : (tripleIndices 2 1 8).map (fun j => (right0Middle4 7 2) j ((0 : Fin 1), (1 : Fin 2), (4 : Fin 8))) = cols_right0 ((0 : Fin 1), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_5 : (tripleIndices 2 1 8).map (fun j => (right0Middle4 7 2) j ((0 : Fin 1), (1 : Fin 2), (5 : Fin 8))) = cols_right0 ((0 : Fin 1), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_6 : (tripleIndices 2 1 8).map (fun j => (right0Middle4 7 2) j ((0 : Fin 1), (1 : Fin 2), (6 : Fin 8))) = cols_right0 ((0 : Fin 1), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_7 : (tripleIndices 2 1 8).map (fun j => (right0Middle4 7 2) j ((0 : Fin 1), (1 : Fin 2), (7 : Fin 8))) = cols_right0 ((0 : Fin 1), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right0_data (r : LeftIndex 4 7 2) : (tripleIndices 2 1 8).map (fun j => (right0Middle4 7 2) j r) = cols_right0 r := by
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

private def cols_left0Data : List (List ℤ) := [decodeIntegerRow 16 3 1 21530002,
    decodeIntegerRow 16 3 1 21542800,
    decodeIntegerRow 16 3 1 21581680,
    decodeIntegerRow 16 3 1 21702694,
    decodeIntegerRow 16 3 1 22054802,
    decodeIntegerRow 16 3 1 23117680,
    decodeIntegerRow 16 3 1 26306320,
    decodeIntegerRow 16 3 1 35872294,
    decodeIntegerRow 16 3 1 21503434,
    decodeIntegerRow 16 3 1 21516880,
    decodeIntegerRow 16 3 1 21348400,
    decodeIntegerRow 16 3 1 21463582,
    decodeIntegerRow 16 3 1 19929034,
    decodeIntegerRow 16 3 1 20991920,
    decodeIntegerRow 16 3 1 7174480,
    decodeIntegerRow 16 3 1 16740382]

def cols_left0 (r : LeftIndex 4 7 2) : List ℤ := cols_left0Data.getD (leftPosition 4 7 2 r) []

private theorem cols_left0_eq_0_0_0 : (tripleIndices 2 1 8).map (fun j => (left0Middle4 7 2) j ((0 : Fin 1), (0 : Fin 2), (0 : Fin 8))) = cols_left0 ((0 : Fin 1), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_1 : (tripleIndices 2 1 8).map (fun j => (left0Middle4 7 2) j ((0 : Fin 1), (0 : Fin 2), (1 : Fin 8))) = cols_left0 ((0 : Fin 1), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_2 : (tripleIndices 2 1 8).map (fun j => (left0Middle4 7 2) j ((0 : Fin 1), (0 : Fin 2), (2 : Fin 8))) = cols_left0 ((0 : Fin 1), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_3 : (tripleIndices 2 1 8).map (fun j => (left0Middle4 7 2) j ((0 : Fin 1), (0 : Fin 2), (3 : Fin 8))) = cols_left0 ((0 : Fin 1), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_4 : (tripleIndices 2 1 8).map (fun j => (left0Middle4 7 2) j ((0 : Fin 1), (0 : Fin 2), (4 : Fin 8))) = cols_left0 ((0 : Fin 1), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_5 : (tripleIndices 2 1 8).map (fun j => (left0Middle4 7 2) j ((0 : Fin 1), (0 : Fin 2), (5 : Fin 8))) = cols_left0 ((0 : Fin 1), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_6 : (tripleIndices 2 1 8).map (fun j => (left0Middle4 7 2) j ((0 : Fin 1), (0 : Fin 2), (6 : Fin 8))) = cols_left0 ((0 : Fin 1), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_7 : (tripleIndices 2 1 8).map (fun j => (left0Middle4 7 2) j ((0 : Fin 1), (0 : Fin 2), (7 : Fin 8))) = cols_left0 ((0 : Fin 1), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_0 : (tripleIndices 2 1 8).map (fun j => (left0Middle4 7 2) j ((0 : Fin 1), (1 : Fin 2), (0 : Fin 8))) = cols_left0 ((0 : Fin 1), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_1 : (tripleIndices 2 1 8).map (fun j => (left0Middle4 7 2) j ((0 : Fin 1), (1 : Fin 2), (1 : Fin 8))) = cols_left0 ((0 : Fin 1), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_2 : (tripleIndices 2 1 8).map (fun j => (left0Middle4 7 2) j ((0 : Fin 1), (1 : Fin 2), (2 : Fin 8))) = cols_left0 ((0 : Fin 1), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_3 : (tripleIndices 2 1 8).map (fun j => (left0Middle4 7 2) j ((0 : Fin 1), (1 : Fin 2), (3 : Fin 8))) = cols_left0 ((0 : Fin 1), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_4 : (tripleIndices 2 1 8).map (fun j => (left0Middle4 7 2) j ((0 : Fin 1), (1 : Fin 2), (4 : Fin 8))) = cols_left0 ((0 : Fin 1), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_5 : (tripleIndices 2 1 8).map (fun j => (left0Middle4 7 2) j ((0 : Fin 1), (1 : Fin 2), (5 : Fin 8))) = cols_left0 ((0 : Fin 1), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_6 : (tripleIndices 2 1 8).map (fun j => (left0Middle4 7 2) j ((0 : Fin 1), (1 : Fin 2), (6 : Fin 8))) = cols_left0 ((0 : Fin 1), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_7 : (tripleIndices 2 1 8).map (fun j => (left0Middle4 7 2) j ((0 : Fin 1), (1 : Fin 2), (7 : Fin 8))) = cols_left0 ((0 : Fin 1), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_left0_data (r : LeftIndex 4 7 2) : (tripleIndices 2 1 8).map (fun j => (left0Middle4 7 2) j r) = cols_left0 r := by
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

private def cols_right2Data : List (List ℤ) := [decodeIntegerRow 16 5 2 75805664062,
    decodeIntegerRow 16 5 2 78735351562,
    decodeIntegerRow 16 5 2 88500976562,
    decodeIntegerRow 16 5 2 15258789062,
    decodeIntegerRow 16 5 2 76293164062,
    decodeIntegerRow 16 5 2 76297851562,
    decodeIntegerRow 16 5 2 76313476562,
    decodeIntegerRow 16 5 2 76196289062,
    decodeIntegerRow 16 5 2 76293945322,
    decodeIntegerRow 16 5 2 76293945314,
    decodeIntegerRow 16 5 2 76293945562,
    decodeIntegerRow 16 5 2 76293945362,
    decodeIntegerRow 16 5 2 76293951562,
    decodeIntegerRow 16 5 2 76293946562,
    decodeIntegerRow 16 5 2 76294101562,
    decodeIntegerRow 16 5 2 76293976562]

def cols_right2 (r : LeftIndex 4 7 2) : List ℤ := cols_right2Data.getD (leftPosition 4 7 2 r) []

private theorem cols_right2_eq_0_0_0 : (tripleIndices 2 1 8).map (fun j => (right2Middle4 7 2) j ((0 : Fin 1), (0 : Fin 2), (0 : Fin 8))) = cols_right2 ((0 : Fin 1), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_1 : (tripleIndices 2 1 8).map (fun j => (right2Middle4 7 2) j ((0 : Fin 1), (0 : Fin 2), (1 : Fin 8))) = cols_right2 ((0 : Fin 1), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_2 : (tripleIndices 2 1 8).map (fun j => (right2Middle4 7 2) j ((0 : Fin 1), (0 : Fin 2), (2 : Fin 8))) = cols_right2 ((0 : Fin 1), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_3 : (tripleIndices 2 1 8).map (fun j => (right2Middle4 7 2) j ((0 : Fin 1), (0 : Fin 2), (3 : Fin 8))) = cols_right2 ((0 : Fin 1), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_4 : (tripleIndices 2 1 8).map (fun j => (right2Middle4 7 2) j ((0 : Fin 1), (0 : Fin 2), (4 : Fin 8))) = cols_right2 ((0 : Fin 1), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_5 : (tripleIndices 2 1 8).map (fun j => (right2Middle4 7 2) j ((0 : Fin 1), (0 : Fin 2), (5 : Fin 8))) = cols_right2 ((0 : Fin 1), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_6 : (tripleIndices 2 1 8).map (fun j => (right2Middle4 7 2) j ((0 : Fin 1), (0 : Fin 2), (6 : Fin 8))) = cols_right2 ((0 : Fin 1), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_7 : (tripleIndices 2 1 8).map (fun j => (right2Middle4 7 2) j ((0 : Fin 1), (0 : Fin 2), (7 : Fin 8))) = cols_right2 ((0 : Fin 1), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_0 : (tripleIndices 2 1 8).map (fun j => (right2Middle4 7 2) j ((0 : Fin 1), (1 : Fin 2), (0 : Fin 8))) = cols_right2 ((0 : Fin 1), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_1 : (tripleIndices 2 1 8).map (fun j => (right2Middle4 7 2) j ((0 : Fin 1), (1 : Fin 2), (1 : Fin 8))) = cols_right2 ((0 : Fin 1), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_2 : (tripleIndices 2 1 8).map (fun j => (right2Middle4 7 2) j ((0 : Fin 1), (1 : Fin 2), (2 : Fin 8))) = cols_right2 ((0 : Fin 1), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_3 : (tripleIndices 2 1 8).map (fun j => (right2Middle4 7 2) j ((0 : Fin 1), (1 : Fin 2), (3 : Fin 8))) = cols_right2 ((0 : Fin 1), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_4 : (tripleIndices 2 1 8).map (fun j => (right2Middle4 7 2) j ((0 : Fin 1), (1 : Fin 2), (4 : Fin 8))) = cols_right2 ((0 : Fin 1), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_5 : (tripleIndices 2 1 8).map (fun j => (right2Middle4 7 2) j ((0 : Fin 1), (1 : Fin 2), (5 : Fin 8))) = cols_right2 ((0 : Fin 1), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_6 : (tripleIndices 2 1 8).map (fun j => (right2Middle4 7 2) j ((0 : Fin 1), (1 : Fin 2), (6 : Fin 8))) = cols_right2 ((0 : Fin 1), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_7 : (tripleIndices 2 1 8).map (fun j => (right2Middle4 7 2) j ((0 : Fin 1), (1 : Fin 2), (7 : Fin 8))) = cols_right2 ((0 : Fin 1), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right2_data (r : LeftIndex 4 7 2) : (tripleIndices 2 1 8).map (fun j => (right2Middle4 7 2) j r) = cols_right2 r := by
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

theorem product0_eq : HexagonAtoms472.outerABC * HexagonAtoms472.assocABC = HexagonAtoms472.assocABC :=
  Matrix.one_mul (m := Fin 2 × Fin 1 × Fin 8) (n := Fin 1 × Fin 2 × Fin 8) _

theorem product1_eq : HexagonAtoms472.assocBAC * HexagonAtoms472.innerABC = HexagonAtoms472.assocBAC :=
  Matrix.mul_one (m := Fin 2 × Fin 1 × Fin 8) (n := Fin 1 × Fin 2 × Fin 8) _

theorem product2_eq : HexagonAtoms472.innerRightABC * HexagonAtoms472.assocABC = HexagonAtoms472.assocABC :=
  Matrix.one_mul (m := Fin 2 × Fin 1 × Fin 8) (n := Fin 1 × Fin 2 × Fin 8) _

theorem product3_eq : HexagonAtoms472.inverseACB * right0Middle4 7 2 = rowColumnMul rows_inverseACB cols_right0 :=
  (rowColumnMul_eq _ _ _ _ rows_inverseACB_data cols_right0_data).symm

theorem product4_eq : HexagonAtoms472.innerACB * right1Middle4 7 2 = right1Middle4 7 2 :=
  Matrix.one_mul (m := Fin 2 × Fin 1 × Fin 8) (n := Fin 1 × Fin 2 × Fin 8) _

theorem product5_eq : HexagonAtoms472.assocBCA * left0Middle4 7 2 = rowColumnMul rows_assocBCA cols_left0 :=
  (rowColumnMul_eq _ _ _ _ rows_assocBCA_data cols_left0_data).symm

theorem product6_eq : HexagonAtoms472.innerRightBAC * left1Middle4 7 2 = left1Middle4 7 2 :=
  Matrix.one_mul (m := Fin 2 × Fin 1 × Fin 8) (n := Fin 1 × Fin 2 × Fin 8) _

theorem product7_eq : HexagonAtoms472.assocCAB * right2Middle4 7 2 = rowColumnMul rows_assocCAB cols_right2 :=
  (rowColumnMul_eq _ _ _ _ rows_assocCAB_data cols_right2_data).symm

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn472
