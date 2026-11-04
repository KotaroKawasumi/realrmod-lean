import RMod.BrundanEllis.StackingReferenceHexagonAtoms765
import RMod.BrundanEllis.StackingReferenceHexagonMiddle7
import RMod.BrundanEllis.StackingReferenceRowColumnCheck

/-! Verified row and column lists. Each subsequent scalar product traverses
these lists directly, without repeated lookup into the original matrices. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn765
open Superfusion

private def rows_outerABCData : List (List ℤ) := [decodeIntegerRow 16 3 1 21523361,
    decodeIntegerRow 16 3 1 21523363,
    decodeIntegerRow 16 3 1 21523369,
    decodeIntegerRow 16 3 1 21523387,
    decodeIntegerRow 16 3 1 21523441,
    decodeIntegerRow 16 3 1 21523603,
    decodeIntegerRow 16 3 1 21524089,
    decodeIntegerRow 16 3 1 21525547,
    decodeIntegerRow 16 3 1 21516799,
    decodeIntegerRow 16 3 1 21503677,
    decodeIntegerRow 16 3 1 21464311,
    decodeIntegerRow 16 3 1 21346213,
    decodeIntegerRow 16 3 1 20991919,
    decodeIntegerRow 16 3 1 19929037,
    decodeIntegerRow 16 3 1 16740391,
    decodeIntegerRow 16 3 1 7174453]

def rows_outerABC (r : LeftIndex 6 5 7) : List ℤ := rows_outerABCData.getD (leftPosition 6 5 7 r) []

private theorem rows_outerABC_eq_0_0_0 : (tripleIndices 2 2 4).map ((HexagonAtoms765.outerABC) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = rows_outerABC ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_0_1 : (tripleIndices 2 2 4).map ((HexagonAtoms765.outerABC) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = rows_outerABC ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_0_2 : (tripleIndices 2 2 4).map ((HexagonAtoms765.outerABC) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = rows_outerABC ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_0_3 : (tripleIndices 2 2 4).map ((HexagonAtoms765.outerABC) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = rows_outerABC ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_1_0 : (tripleIndices 2 2 4).map ((HexagonAtoms765.outerABC) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = rows_outerABC ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_1_1 : (tripleIndices 2 2 4).map ((HexagonAtoms765.outerABC) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = rows_outerABC ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_1_2 : (tripleIndices 2 2 4).map ((HexagonAtoms765.outerABC) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = rows_outerABC ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_1_3 : (tripleIndices 2 2 4).map ((HexagonAtoms765.outerABC) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = rows_outerABC ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_0 : (tripleIndices 2 2 4).map ((HexagonAtoms765.outerABC) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = rows_outerABC ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_1 : (tripleIndices 2 2 4).map ((HexagonAtoms765.outerABC) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = rows_outerABC ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_2 : (tripleIndices 2 2 4).map ((HexagonAtoms765.outerABC) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = rows_outerABC ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_3 : (tripleIndices 2 2 4).map ((HexagonAtoms765.outerABC) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = rows_outerABC ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_1_0 : (tripleIndices 2 2 4).map ((HexagonAtoms765.outerABC) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = rows_outerABC ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_1_1 : (tripleIndices 2 2 4).map ((HexagonAtoms765.outerABC) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = rows_outerABC ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_1_2 : (tripleIndices 2 2 4).map ((HexagonAtoms765.outerABC) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = rows_outerABC ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_1_3 : (tripleIndices 2 2 4).map ((HexagonAtoms765.outerABC) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = rows_outerABC ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_outerABC_data (r : LeftIndex 6 5 7) : (tripleIndices 2 2 4).map ((HexagonAtoms765.outerABC) r) = rows_outerABC r := by
  fin_cases r
  · exact rows_outerABC_eq_0_0_0
  · exact rows_outerABC_eq_0_0_1
  · exact rows_outerABC_eq_0_0_2
  · exact rows_outerABC_eq_0_0_3
  · exact rows_outerABC_eq_0_1_0
  · exact rows_outerABC_eq_0_1_1
  · exact rows_outerABC_eq_0_1_2
  · exact rows_outerABC_eq_0_1_3
  · exact rows_outerABC_eq_1_0_0
  · exact rows_outerABC_eq_1_0_1
  · exact rows_outerABC_eq_1_0_2
  · exact rows_outerABC_eq_1_0_3
  · exact rows_outerABC_eq_1_1_0
  · exact rows_outerABC_eq_1_1_1
  · exact rows_outerABC_eq_1_1_2
  · exact rows_outerABC_eq_1_1_3

private def rows_assocBACData : List (List ℤ) := [decodeIntegerRow 16 3 1 7174462,
    decodeIntegerRow 16 3 1 16740364,
    decodeIntegerRow 16 3 1 23117682,
    decodeIntegerRow 16 3 1 22054804,
    decodeIntegerRow 16 3 1 19929036,
    decodeIntegerRow 16 3 1 22054798,
    decodeIntegerRow 16 3 1 7174444,
    decodeIntegerRow 16 3 1 26306302,
    decodeIntegerRow 16 3 1 21580222,
    decodeIntegerRow 16 3 1 21345484,
    decodeIntegerRow 16 3 1 21517042,
    decodeIntegerRow 16 3 1 21543124,
    decodeIntegerRow 16 3 1 21530164,
    decodeIntegerRow 16 3 1 21542962,
    decodeIntegerRow 16 3 1 21584596,
    decodeIntegerRow 16 3 1 21699778]

def rows_assocBAC (r : RightIndex 6 7 5) : List ℤ := rows_assocBACData.getD (rightPosition 6 7 5 r) []

private theorem rows_assocBAC_eq_0_0_0 : (tripleIndices 1 4 4).map ((HexagonAtoms765.assocBAC) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = rows_assocBAC ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_1 : (tripleIndices 1 4 4).map ((HexagonAtoms765.assocBAC) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = rows_assocBAC ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_2 : (tripleIndices 1 4 4).map ((HexagonAtoms765.assocBAC) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = rows_assocBAC ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_3 : (tripleIndices 1 4 4).map ((HexagonAtoms765.assocBAC) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = rows_assocBAC ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_1_0 : (tripleIndices 1 4 4).map ((HexagonAtoms765.assocBAC) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = rows_assocBAC ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_1_1 : (tripleIndices 1 4 4).map ((HexagonAtoms765.assocBAC) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = rows_assocBAC ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_1_2 : (tripleIndices 1 4 4).map ((HexagonAtoms765.assocBAC) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = rows_assocBAC ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_1_3 : (tripleIndices 1 4 4).map ((HexagonAtoms765.assocBAC) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = rows_assocBAC ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_0 : (tripleIndices 1 4 4).map ((HexagonAtoms765.assocBAC) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = rows_assocBAC ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_1 : (tripleIndices 1 4 4).map ((HexagonAtoms765.assocBAC) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = rows_assocBAC ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_2 : (tripleIndices 1 4 4).map ((HexagonAtoms765.assocBAC) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = rows_assocBAC ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_3 : (tripleIndices 1 4 4).map ((HexagonAtoms765.assocBAC) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = rows_assocBAC ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_1_0 : (tripleIndices 1 4 4).map ((HexagonAtoms765.assocBAC) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = rows_assocBAC ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_1_1 : (tripleIndices 1 4 4).map ((HexagonAtoms765.assocBAC) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = rows_assocBAC ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_1_2 : (tripleIndices 1 4 4).map ((HexagonAtoms765.assocBAC) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = rows_assocBAC ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_1_3 : (tripleIndices 1 4 4).map ((HexagonAtoms765.assocBAC) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = rows_assocBAC ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocBAC_data (r : RightIndex 6 7 5) : (tripleIndices 1 4 4).map ((HexagonAtoms765.assocBAC) r) = rows_assocBAC r := by
  fin_cases r
  · exact rows_assocBAC_eq_0_0_0
  · exact rows_assocBAC_eq_0_0_1
  · exact rows_assocBAC_eq_0_0_2
  · exact rows_assocBAC_eq_0_0_3
  · exact rows_assocBAC_eq_0_1_0
  · exact rows_assocBAC_eq_0_1_1
  · exact rows_assocBAC_eq_0_1_2
  · exact rows_assocBAC_eq_0_1_3
  · exact rows_assocBAC_eq_1_0_0
  · exact rows_assocBAC_eq_1_0_1
  · exact rows_assocBAC_eq_1_0_2
  · exact rows_assocBAC_eq_1_0_3
  · exact rows_assocBAC_eq_1_1_0
  · exact rows_assocBAC_eq_1_1_1
  · exact rows_assocBAC_eq_1_1_2
  · exact rows_assocBAC_eq_1_1_3

private def rows_inverseACBData : List (List ℤ) := [decodeIntegerRow 16 3 1 21484022,
    decodeIntegerRow 16 3 1 21693958,
    decodeIntegerRow 16 3 1 21707074,
    decodeIntegerRow 16 3 1 21444654,
    decodeIntegerRow 16 3 1 27898546,
    decodeIntegerRow 16 3 1 6642526,
    decodeIntegerRow 16 3 1 35341798,
    decodeIntegerRow 16 3 1 18336982,
    decodeIntegerRow 16 3 1 21339658,
    decodeIntegerRow 16 3 1 21444602,
    decodeIntegerRow 16 3 1 21483966,
    decodeIntegerRow 16 3 1 21352786,
    decodeIntegerRow 16 3 1 35339854,
    decodeIntegerRow 16 3 1 24714274,
    decodeIntegerRow 16 3 1 15143962,
    decodeIntegerRow 16 3 1 6643498]

def rows_inverseACB (r : LeftIndex 7 5 6) : List ℤ := rows_inverseACBData.getD (leftPosition 7 5 6 r) []

private theorem rows_inverseACB_eq_0_0_0 : (tripleIndices 2 2 4).map ((HexagonAtoms765.inverseACB) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_1 : (tripleIndices 2 2 4).map ((HexagonAtoms765.inverseACB) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_2 : (tripleIndices 2 2 4).map ((HexagonAtoms765.inverseACB) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_3 : (tripleIndices 2 2 4).map ((HexagonAtoms765.inverseACB) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_0 : (tripleIndices 2 2 4).map ((HexagonAtoms765.inverseACB) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = rows_inverseACB ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_1 : (tripleIndices 2 2 4).map ((HexagonAtoms765.inverseACB) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = rows_inverseACB ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_2 : (tripleIndices 2 2 4).map ((HexagonAtoms765.inverseACB) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = rows_inverseACB ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_3 : (tripleIndices 2 2 4).map ((HexagonAtoms765.inverseACB) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = rows_inverseACB ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_0 : (tripleIndices 2 2 4).map ((HexagonAtoms765.inverseACB) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_1 : (tripleIndices 2 2 4).map ((HexagonAtoms765.inverseACB) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_2 : (tripleIndices 2 2 4).map ((HexagonAtoms765.inverseACB) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_3 : (tripleIndices 2 2 4).map ((HexagonAtoms765.inverseACB) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_0 : (tripleIndices 2 2 4).map ((HexagonAtoms765.inverseACB) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = rows_inverseACB ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_1 : (tripleIndices 2 2 4).map ((HexagonAtoms765.inverseACB) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = rows_inverseACB ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_2 : (tripleIndices 2 2 4).map ((HexagonAtoms765.inverseACB) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = rows_inverseACB ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_3 : (tripleIndices 2 2 4).map ((HexagonAtoms765.inverseACB) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = rows_inverseACB ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_inverseACB_data (r : LeftIndex 7 5 6) : (tripleIndices 2 2 4).map ((HexagonAtoms765.inverseACB) r) = rows_inverseACB r := by
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

private def rows_assocBCAData : List (List ℤ) := [decodeIntegerRow 16 3 1 21562754,
    decodeIntegerRow 16 3 1 21352786,
    decodeIntegerRow 16 3 1 21339658,
    decodeIntegerRow 16 3 1 21602118,
    decodeIntegerRow 16 3 1 15143962,
    decodeIntegerRow 16 3 1 36403222,
    decodeIntegerRow 16 3 1 7706866,
    decodeIntegerRow 16 3 1 24714274,
    decodeIntegerRow 16 3 1 21707074,
    decodeIntegerRow 16 3 1 21602066,
    decodeIntegerRow 16 3 1 21562698,
    decodeIntegerRow 16 3 1 21693958,
    decodeIntegerRow 16 3 1 7704922,
    decodeIntegerRow 16 3 1 18336982,
    decodeIntegerRow 16 3 1 27898546,
    decodeIntegerRow 16 3 1 36404194]

def rows_assocBCA (r : RightIndex 6 5 7) : List ℤ := rows_assocBCAData.getD (rightPosition 6 5 7 r) []

private theorem rows_assocBCA_eq_0_0_0 : (tripleIndices 2 2 4).map ((HexagonAtoms765.assocBCA) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = rows_assocBCA ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_1 : (tripleIndices 2 2 4).map ((HexagonAtoms765.assocBCA) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = rows_assocBCA ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_2 : (tripleIndices 2 2 4).map ((HexagonAtoms765.assocBCA) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = rows_assocBCA ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_3 : (tripleIndices 2 2 4).map ((HexagonAtoms765.assocBCA) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = rows_assocBCA ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_0 : (tripleIndices 2 2 4).map ((HexagonAtoms765.assocBCA) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = rows_assocBCA ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_1 : (tripleIndices 2 2 4).map ((HexagonAtoms765.assocBCA) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = rows_assocBCA ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_2 : (tripleIndices 2 2 4).map ((HexagonAtoms765.assocBCA) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = rows_assocBCA ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_3 : (tripleIndices 2 2 4).map ((HexagonAtoms765.assocBCA) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = rows_assocBCA ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_0 : (tripleIndices 2 2 4).map ((HexagonAtoms765.assocBCA) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = rows_assocBCA ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_1 : (tripleIndices 2 2 4).map ((HexagonAtoms765.assocBCA) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = rows_assocBCA ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_2 : (tripleIndices 2 2 4).map ((HexagonAtoms765.assocBCA) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = rows_assocBCA ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_3 : (tripleIndices 2 2 4).map ((HexagonAtoms765.assocBCA) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = rows_assocBCA ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_0 : (tripleIndices 2 2 4).map ((HexagonAtoms765.assocBCA) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = rows_assocBCA ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_1 : (tripleIndices 2 2 4).map ((HexagonAtoms765.assocBCA) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = rows_assocBCA ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_2 : (tripleIndices 2 2 4).map ((HexagonAtoms765.assocBCA) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = rows_assocBCA ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_3 : (tripleIndices 2 2 4).map ((HexagonAtoms765.assocBCA) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = rows_assocBCA ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocBCA_data (r : RightIndex 6 5 7) : (tripleIndices 2 2 4).map ((HexagonAtoms765.assocBCA) r) = rows_assocBCA r := by
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

private def rows_assocCABData : List (List ℤ) := [decodeIntegerRow 16 3 1 21523361,
    decodeIntegerRow 16 3 1 21523363,
    decodeIntegerRow 16 3 1 21523369,
    decodeIntegerRow 16 3 1 21523387,
    decodeIntegerRow 16 3 1 22054801,
    decodeIntegerRow 16 3 1 23117683,
    decodeIntegerRow 16 3 1 26306329,
    decodeIntegerRow 16 3 1 35872267,
    decodeIntegerRow 16 3 1 21523441,
    decodeIntegerRow 16 3 1 21523603,
    decodeIntegerRow 16 3 1 21524089,
    decodeIntegerRow 16 3 1 21525547,
    decodeIntegerRow 16 3 1 21529921,
    decodeIntegerRow 16 3 1 21543043,
    decodeIntegerRow 16 3 1 21582409,
    decodeIntegerRow 16 3 1 21700507]

def rows_assocCAB (r : RightIndex 5 7 6) : List ℤ := rows_assocCABData.getD (rightPosition 5 7 6 r) []

private theorem rows_assocCAB_eq_0_0_0 : (tripleIndices 2 2 4).map ((HexagonAtoms765.assocCAB) ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4))) = rows_assocCAB ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_1 : (tripleIndices 2 2 4).map ((HexagonAtoms765.assocCAB) ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4))) = rows_assocCAB ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_2 : (tripleIndices 2 2 4).map ((HexagonAtoms765.assocCAB) ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4))) = rows_assocCAB ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_3 : (tripleIndices 2 2 4).map ((HexagonAtoms765.assocCAB) ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4))) = rows_assocCAB ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_0 : (tripleIndices 2 2 4).map ((HexagonAtoms765.assocCAB) ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4))) = rows_assocCAB ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_1 : (tripleIndices 2 2 4).map ((HexagonAtoms765.assocCAB) ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4))) = rows_assocCAB ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_2 : (tripleIndices 2 2 4).map ((HexagonAtoms765.assocCAB) ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4))) = rows_assocCAB ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_3 : (tripleIndices 2 2 4).map ((HexagonAtoms765.assocCAB) ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4))) = rows_assocCAB ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_2_0 : (tripleIndices 2 2 4).map ((HexagonAtoms765.assocCAB) ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4))) = rows_assocCAB ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_2_1 : (tripleIndices 2 2 4).map ((HexagonAtoms765.assocCAB) ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4))) = rows_assocCAB ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_2_2 : (tripleIndices 2 2 4).map ((HexagonAtoms765.assocCAB) ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4))) = rows_assocCAB ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_2_3 : (tripleIndices 2 2 4).map ((HexagonAtoms765.assocCAB) ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4))) = rows_assocCAB ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_3_0 : (tripleIndices 2 2 4).map ((HexagonAtoms765.assocCAB) ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4))) = rows_assocCAB ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_3_1 : (tripleIndices 2 2 4).map ((HexagonAtoms765.assocCAB) ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4))) = rows_assocCAB ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_3_2 : (tripleIndices 2 2 4).map ((HexagonAtoms765.assocCAB) ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4))) = rows_assocCAB ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_3_3 : (tripleIndices 2 2 4).map ((HexagonAtoms765.assocCAB) ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4))) = rows_assocCAB ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocCAB_data (r : RightIndex 5 7 6) : (tripleIndices 2 2 4).map ((HexagonAtoms765.assocCAB) r) = rows_assocCAB r := by
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

private def cols_assocABCData : List (List ℤ) := [decodeIntegerRow 16 3 1 28082080,
    decodeIntegerRow 16 3 1 6720800,
    decodeIntegerRow 16 3 1 35379680,
    decodeIntegerRow 16 3 1 18503200,
    decodeIntegerRow 16 3 1 27719200,
    decodeIntegerRow 16 3 1 6565280,
    decodeIntegerRow 16 3 1 35301920,
    decodeIntegerRow 16 3 1 18166240,
    decodeIntegerRow 16 3 1 6722688,
    decodeIntegerRow 16 3 1 14960080,
    decodeIntegerRow 16 3 1 18507400,
    decodeIntegerRow 16 3 1 7666016,
    decodeIntegerRow 16 3 1 36483440,
    decodeIntegerRow 16 3 1 27714688,
    decodeIntegerRow 16 3 1 24884704,
    decodeIntegerRow 16 3 1 35301000]

def cols_assocABC (r : LeftIndex 7 6 5) : List ℤ := cols_assocABCData.getD (leftPosition 7 6 5 r) []

private theorem cols_assocABC_eq_0_0_0 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms765.assocABC) j ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4))) = cols_assocABC ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_1 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms765.assocABC) j ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4))) = cols_assocABC ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_2 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms765.assocABC) j ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4))) = cols_assocABC ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_3 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms765.assocABC) j ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4))) = cols_assocABC ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_0 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms765.assocABC) j ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4))) = cols_assocABC ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_1 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms765.assocABC) j ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4))) = cols_assocABC ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_2 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms765.assocABC) j ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4))) = cols_assocABC ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_3 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms765.assocABC) j ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4))) = cols_assocABC ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_2_0 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms765.assocABC) j ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4))) = cols_assocABC ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_2_1 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms765.assocABC) j ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4))) = cols_assocABC ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_2_2 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms765.assocABC) j ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4))) = cols_assocABC ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_2_3 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms765.assocABC) j ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4))) = cols_assocABC ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_3_0 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms765.assocABC) j ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4))) = cols_assocABC ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_3_1 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms765.assocABC) j ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4))) = cols_assocABC ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_3_2 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms765.assocABC) j ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4))) = cols_assocABC ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_3_3 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms765.assocABC) j ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4))) = cols_assocABC ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_assocABC_data (r : LeftIndex 7 6 5) : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms765.assocABC) j r) = cols_assocABC r := by
  fin_cases r
  · exact cols_assocABC_eq_0_0_0
  · exact cols_assocABC_eq_0_0_1
  · exact cols_assocABC_eq_0_0_2
  · exact cols_assocABC_eq_0_0_3
  · exact cols_assocABC_eq_0_1_0
  · exact cols_assocABC_eq_0_1_1
  · exact cols_assocABC_eq_0_1_2
  · exact cols_assocABC_eq_0_1_3
  · exact cols_assocABC_eq_0_2_0
  · exact cols_assocABC_eq_0_2_1
  · exact cols_assocABC_eq_0_2_2
  · exact cols_assocABC_eq_0_2_3
  · exact cols_assocABC_eq_0_3_0
  · exact cols_assocABC_eq_0_3_1
  · exact cols_assocABC_eq_0_3_2
  · exact cols_assocABC_eq_0_3_3

private def cols_innerABCData : List (List ℤ) := [decodeIntegerRow 16 3 1 21602066,
    decodeIntegerRow 16 3 1 21339646,
    decodeIntegerRow 16 3 1 21693958,
    decodeIntegerRow 16 3 1 21484022,
    decodeIntegerRow 16 3 1 18336982,
    decodeIntegerRow 16 3 1 35341798,
    decodeIntegerRow 16 3 1 36404194,
    decodeIntegerRow 16 3 1 15148174,
    decodeIntegerRow 16 3 1 21352786,
    decodeIntegerRow 16 3 1 21483966,
    decodeIntegerRow 16 3 1 21602118,
    decodeIntegerRow 16 3 1 21707062,
    decodeIntegerRow 16 3 1 36403222,
    decodeIntegerRow 16 3 1 27902758,
    decodeIntegerRow 16 3 1 24714274,
    decodeIntegerRow 16 3 1 35339854]

def cols_innerABC (r : LeftIndex 7 6 5) : List ℤ := cols_innerABCData.getD (leftPosition 7 6 5 r) []

private theorem cols_innerABC_eq_0_0_0 : (tripleIndices 1 4 4).map (fun j => (HexagonAtoms765.innerABC) j ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4))) = cols_innerABC ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_0_1 : (tripleIndices 1 4 4).map (fun j => (HexagonAtoms765.innerABC) j ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4))) = cols_innerABC ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_0_2 : (tripleIndices 1 4 4).map (fun j => (HexagonAtoms765.innerABC) j ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4))) = cols_innerABC ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_0_3 : (tripleIndices 1 4 4).map (fun j => (HexagonAtoms765.innerABC) j ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4))) = cols_innerABC ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_1_0 : (tripleIndices 1 4 4).map (fun j => (HexagonAtoms765.innerABC) j ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4))) = cols_innerABC ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_1_1 : (tripleIndices 1 4 4).map (fun j => (HexagonAtoms765.innerABC) j ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4))) = cols_innerABC ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_1_2 : (tripleIndices 1 4 4).map (fun j => (HexagonAtoms765.innerABC) j ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4))) = cols_innerABC ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_1_3 : (tripleIndices 1 4 4).map (fun j => (HexagonAtoms765.innerABC) j ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4))) = cols_innerABC ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_2_0 : (tripleIndices 1 4 4).map (fun j => (HexagonAtoms765.innerABC) j ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4))) = cols_innerABC ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_2_1 : (tripleIndices 1 4 4).map (fun j => (HexagonAtoms765.innerABC) j ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4))) = cols_innerABC ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_2_2 : (tripleIndices 1 4 4).map (fun j => (HexagonAtoms765.innerABC) j ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4))) = cols_innerABC ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_2_3 : (tripleIndices 1 4 4).map (fun j => (HexagonAtoms765.innerABC) j ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4))) = cols_innerABC ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_3_0 : (tripleIndices 1 4 4).map (fun j => (HexagonAtoms765.innerABC) j ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4))) = cols_innerABC ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_3_1 : (tripleIndices 1 4 4).map (fun j => (HexagonAtoms765.innerABC) j ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4))) = cols_innerABC ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_3_2 : (tripleIndices 1 4 4).map (fun j => (HexagonAtoms765.innerABC) j ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4))) = cols_innerABC ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_3_3 : (tripleIndices 1 4 4).map (fun j => (HexagonAtoms765.innerABC) j ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4))) = cols_innerABC ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_innerABC_data (r : LeftIndex 7 6 5) : (tripleIndices 1 4 4).map (fun j => (HexagonAtoms765.innerABC) j r) = cols_innerABC r := by
  fin_cases r
  · exact cols_innerABC_eq_0_0_0
  · exact cols_innerABC_eq_0_0_1
  · exact cols_innerABC_eq_0_0_2
  · exact cols_innerABC_eq_0_0_3
  · exact cols_innerABC_eq_0_1_0
  · exact cols_innerABC_eq_0_1_1
  · exact cols_innerABC_eq_0_1_2
  · exact cols_innerABC_eq_0_1_3
  · exact cols_innerABC_eq_0_2_0
  · exact cols_innerABC_eq_0_2_1
  · exact cols_innerABC_eq_0_2_2
  · exact cols_innerABC_eq_0_2_3
  · exact cols_innerABC_eq_0_3_0
  · exact cols_innerABC_eq_0_3_1
  · exact cols_innerABC_eq_0_3_2
  · exact cols_innerABC_eq_0_3_3

private def cols_right0Data : List (List ℤ) := [decodeIntegerRow 16 3 1 28082080,
    decodeIntegerRow 16 3 1 6720800,
    decodeIntegerRow 16 3 1 35379680,
    decodeIntegerRow 16 3 1 18503200,
    decodeIntegerRow 16 3 1 27719200,
    decodeIntegerRow 16 3 1 6565280,
    decodeIntegerRow 16 3 1 35301920,
    decodeIntegerRow 16 3 1 18166240,
    decodeIntegerRow 16 3 1 6722688,
    decodeIntegerRow 16 3 1 14960080,
    decodeIntegerRow 16 3 1 18507400,
    decodeIntegerRow 16 3 1 7666016,
    decodeIntegerRow 16 3 1 36483440,
    decodeIntegerRow 16 3 1 27714688,
    decodeIntegerRow 16 3 1 24884704,
    decodeIntegerRow 16 3 1 35301000]

def cols_right0 (r : LeftIndex 7 6 5) : List ℤ := cols_right0Data.getD (leftPosition 7 6 5 r) []

private theorem cols_right0_eq_0_0_0 : (tripleIndices 2 2 4).map (fun j => (right0Middle7 6 5) j ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4))) = cols_right0 ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_1 : (tripleIndices 2 2 4).map (fun j => (right0Middle7 6 5) j ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4))) = cols_right0 ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_2 : (tripleIndices 2 2 4).map (fun j => (right0Middle7 6 5) j ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4))) = cols_right0 ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_3 : (tripleIndices 2 2 4).map (fun j => (right0Middle7 6 5) j ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4))) = cols_right0 ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_0 : (tripleIndices 2 2 4).map (fun j => (right0Middle7 6 5) j ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4))) = cols_right0 ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_1 : (tripleIndices 2 2 4).map (fun j => (right0Middle7 6 5) j ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4))) = cols_right0 ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_2 : (tripleIndices 2 2 4).map (fun j => (right0Middle7 6 5) j ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4))) = cols_right0 ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_3 : (tripleIndices 2 2 4).map (fun j => (right0Middle7 6 5) j ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4))) = cols_right0 ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_2_0 : (tripleIndices 2 2 4).map (fun j => (right0Middle7 6 5) j ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4))) = cols_right0 ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_2_1 : (tripleIndices 2 2 4).map (fun j => (right0Middle7 6 5) j ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4))) = cols_right0 ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_2_2 : (tripleIndices 2 2 4).map (fun j => (right0Middle7 6 5) j ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4))) = cols_right0 ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_2_3 : (tripleIndices 2 2 4).map (fun j => (right0Middle7 6 5) j ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4))) = cols_right0 ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_3_0 : (tripleIndices 2 2 4).map (fun j => (right0Middle7 6 5) j ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4))) = cols_right0 ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_3_1 : (tripleIndices 2 2 4).map (fun j => (right0Middle7 6 5) j ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4))) = cols_right0 ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_3_2 : (tripleIndices 2 2 4).map (fun j => (right0Middle7 6 5) j ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4))) = cols_right0 ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_3_3 : (tripleIndices 2 2 4).map (fun j => (right0Middle7 6 5) j ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4))) = cols_right0 ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right0_data (r : LeftIndex 7 6 5) : (tripleIndices 2 2 4).map (fun j => (right0Middle7 6 5) j r) = cols_right0 r := by
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

private def cols_left0Data : List (List ℤ) := [decodeIntegerRow 16 3 1 14960080,
    decodeIntegerRow 16 3 1 36324032,
    decodeIntegerRow 16 3 1 7666016,
    decodeIntegerRow 16 3 1 24539320,
    decodeIntegerRow 16 3 1 15332032,
    decodeIntegerRow 16 3 1 36483440,
    decodeIntegerRow 16 3 1 7745720,
    decodeIntegerRow 16 3 1 24884704,
    decodeIntegerRow 16 3 1 36325920,
    decodeIntegerRow 16 3 1 28082080,
    decodeIntegerRow 16 3 1 24543520,
    decodeIntegerRow 16 3 1 35379680,
    decodeIntegerRow 16 3 1 6565280,
    decodeIntegerRow 16 3 1 15327520,
    decodeIntegerRow 16 3 1 18166240,
    decodeIntegerRow 16 3 1 7744800]

def cols_left0 (r : LeftIndex 7 6 5) : List ℤ := cols_left0Data.getD (leftPosition 7 6 5 r) []

private theorem cols_left0_eq_0_0_0 : (tripleIndices 2 2 4).map (fun j => (left0Middle7 6 5) j ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4))) = cols_left0 ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_1 : (tripleIndices 2 2 4).map (fun j => (left0Middle7 6 5) j ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4))) = cols_left0 ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_2 : (tripleIndices 2 2 4).map (fun j => (left0Middle7 6 5) j ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4))) = cols_left0 ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_3 : (tripleIndices 2 2 4).map (fun j => (left0Middle7 6 5) j ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4))) = cols_left0 ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_0 : (tripleIndices 2 2 4).map (fun j => (left0Middle7 6 5) j ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4))) = cols_left0 ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_1 : (tripleIndices 2 2 4).map (fun j => (left0Middle7 6 5) j ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4))) = cols_left0 ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_2 : (tripleIndices 2 2 4).map (fun j => (left0Middle7 6 5) j ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4))) = cols_left0 ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_3 : (tripleIndices 2 2 4).map (fun j => (left0Middle7 6 5) j ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4))) = cols_left0 ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_2_0 : (tripleIndices 2 2 4).map (fun j => (left0Middle7 6 5) j ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4))) = cols_left0 ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_2_1 : (tripleIndices 2 2 4).map (fun j => (left0Middle7 6 5) j ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4))) = cols_left0 ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_2_2 : (tripleIndices 2 2 4).map (fun j => (left0Middle7 6 5) j ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4))) = cols_left0 ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_2_3 : (tripleIndices 2 2 4).map (fun j => (left0Middle7 6 5) j ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4))) = cols_left0 ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_3_0 : (tripleIndices 2 2 4).map (fun j => (left0Middle7 6 5) j ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4))) = cols_left0 ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_3_1 : (tripleIndices 2 2 4).map (fun j => (left0Middle7 6 5) j ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4))) = cols_left0 ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_3_2 : (tripleIndices 2 2 4).map (fun j => (left0Middle7 6 5) j ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4))) = cols_left0 ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_3_3 : (tripleIndices 2 2 4).map (fun j => (left0Middle7 6 5) j ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4))) = cols_left0 ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_left0_data (r : LeftIndex 7 6 5) : (tripleIndices 2 2 4).map (fun j => (left0Middle7 6 5) j r) = cols_left0 r := by
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

private def cols_right2Data : List (List ℤ) := [decodeIntegerRow 16 5 2 61546915352,
    decodeIntegerRow 16 5 2 137793920064,
    decodeIntegerRow 16 5 2 15731482560,
    decodeIntegerRow 16 5 2 85962852872,
    decodeIntegerRow 16 5 2 66431602752,
    decodeIntegerRow 16 5 2 136825233064,
    decodeIntegerRow 16 5 2 137840845064,
    decodeIntegerRow 16 5 2 61744100352,
    decodeIntegerRow 16 5 2 136856482560,
    decodeIntegerRow 16 5 2 85962537752,
    decodeIntegerRow 16 5 2 61547225272,
    decodeIntegerRow 16 5 2 14793920064,
    decodeIntegerRow 16 5 2 14747095064,
    decodeIntegerRow 16 5 2 61743790272,
    decodeIntegerRow 16 5 2 66431287872,
    decodeIntegerRow 16 5 2 15762733064]

def cols_right2 (r : LeftIndex 7 6 5) : List ℤ := cols_right2Data.getD (leftPosition 7 6 5 r) []

private theorem cols_right2_eq_0_0_0 : (tripleIndices 2 2 4).map (fun j => (right2Middle7 6 5) j ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4))) = cols_right2 ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_1 : (tripleIndices 2 2 4).map (fun j => (right2Middle7 6 5) j ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4))) = cols_right2 ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_2 : (tripleIndices 2 2 4).map (fun j => (right2Middle7 6 5) j ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4))) = cols_right2 ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_3 : (tripleIndices 2 2 4).map (fun j => (right2Middle7 6 5) j ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4))) = cols_right2 ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_0 : (tripleIndices 2 2 4).map (fun j => (right2Middle7 6 5) j ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4))) = cols_right2 ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_1 : (tripleIndices 2 2 4).map (fun j => (right2Middle7 6 5) j ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4))) = cols_right2 ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_2 : (tripleIndices 2 2 4).map (fun j => (right2Middle7 6 5) j ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4))) = cols_right2 ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_3 : (tripleIndices 2 2 4).map (fun j => (right2Middle7 6 5) j ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4))) = cols_right2 ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_2_0 : (tripleIndices 2 2 4).map (fun j => (right2Middle7 6 5) j ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4))) = cols_right2 ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_2_1 : (tripleIndices 2 2 4).map (fun j => (right2Middle7 6 5) j ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4))) = cols_right2 ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_2_2 : (tripleIndices 2 2 4).map (fun j => (right2Middle7 6 5) j ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4))) = cols_right2 ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_2_3 : (tripleIndices 2 2 4).map (fun j => (right2Middle7 6 5) j ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4))) = cols_right2 ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_3_0 : (tripleIndices 2 2 4).map (fun j => (right2Middle7 6 5) j ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4))) = cols_right2 ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_3_1 : (tripleIndices 2 2 4).map (fun j => (right2Middle7 6 5) j ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4))) = cols_right2 ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_3_2 : (tripleIndices 2 2 4).map (fun j => (right2Middle7 6 5) j ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4))) = cols_right2 ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_3_3 : (tripleIndices 2 2 4).map (fun j => (right2Middle7 6 5) j ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4))) = cols_right2 ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right2_data (r : LeftIndex 7 6 5) : (tripleIndices 2 2 4).map (fun j => (right2Middle7 6 5) j r) = cols_right2 r := by
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

theorem product0_eq : HexagonAtoms765.outerABC * HexagonAtoms765.assocABC = rowColumnMul rows_outerABC cols_assocABC :=
  (rowColumnMul_eq _ _ _ _ rows_outerABC_data cols_assocABC_data).symm

theorem product1_eq : HexagonAtoms765.assocBAC * HexagonAtoms765.innerABC = rowColumnMul rows_assocBAC cols_innerABC :=
  (rowColumnMul_eq _ _ _ _ rows_assocBAC_data cols_innerABC_data).symm

theorem product2_eq : HexagonAtoms765.innerRightABC * HexagonAtoms765.assocABC = HexagonAtoms765.assocABC :=
  Matrix.one_mul (m := Fin 2 × Fin 2 × Fin 4) (n := Fin 1 × Fin 4 × Fin 4) _

theorem product3_eq : HexagonAtoms765.inverseACB * right0Middle7 6 5 = rowColumnMul rows_inverseACB cols_right0 :=
  (rowColumnMul_eq _ _ _ _ rows_inverseACB_data cols_right0_data).symm

theorem product4_eq : HexagonAtoms765.innerACB * right1Middle7 6 5 = right1Middle7 6 5 :=
  Matrix.one_mul (m := Fin 2 × Fin 2 × Fin 4) (n := Fin 1 × Fin 4 × Fin 4) _

theorem product5_eq : HexagonAtoms765.assocBCA * left0Middle7 6 5 = rowColumnMul rows_assocBCA cols_left0 :=
  (rowColumnMul_eq _ _ _ _ rows_assocBCA_data cols_left0_data).symm

theorem product6_eq : HexagonAtoms765.innerRightBAC * left1Middle7 6 5 = left1Middle7 6 5 :=
  Matrix.one_mul (m := Fin 2 × Fin 2 × Fin 4) (n := Fin 1 × Fin 4 × Fin 4) _

theorem product7_eq : HexagonAtoms765.assocCAB * right2Middle7 6 5 = rowColumnMul rows_assocCAB cols_right2 :=
  (rowColumnMul_eq _ _ _ _ rows_assocCAB_data cols_right2_data).symm

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn765
